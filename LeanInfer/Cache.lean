import Lean
import LeanInfer.Config

open Lean System

namespace LeanInfer.Cache

private def getHomeDir : IO FilePath := do
  let some dir ← IO.getEnv "HOME" | throw $ IO.userError "Cannot find the $HOME environment variable."
  return dir

private def ensureExists (dir : FilePath) : IO Unit := do
  if !(← dir.pathExists)  then
      IO.FS.createDirAll dir

def getDefaultCacheDir : IO FilePath := do
  return (← getHomeDir) / ".cache" / "lean_infer"

def getCacheDir : IO FilePath := do
  let defaultCacheDir ← getDefaultCacheDir
  let dir := match ← IO.getEnv "LEAN_INFER_CACHE_DIR" with
  | some dir => (dir : FilePath)
  | none => defaultCacheDir
  ensureExists dir
  return dir.normalize

private def getModelDir (url : HuggingFaceURL) : IO FilePath := do
  let cacheDir ← getCacheDir
  let dir := match url.user with
  | none => cacheDir / url.modelName
  | some user => cacheDir / user / url.modelName
  return dir.normalize

/--
Return the cache directory for storing the current model.
-/
def getGeneratorDir : IO (Option FilePath) := do
  let some url ← getGeneratorUrl | return none
  getModelDir url

def getEncoderDir : IO (Option FilePath) := do
  let some url ← getEncoderUrl | return none
  getModelDir url

/--
Check if a command is available.
-/
private def checkAvailable (cmd : String) : IO Unit := do
  let proc ← IO.Process.output {
    cmd := "which",
    args := #[cmd]
  }
  if proc.exitCode != 0 then
    throw $ IO.userError s!"Cannot find `{cmd}`."

private def initGitLFS : IO Unit := do
  checkAvailable "git"
  let proc ← IO.Process.output {
    cmd := "git"
    args := #["lfs", "install"]
  }
  if proc.exitCode != 0 then
    throw $ IO.userError "Failed to initialize Git LFS. Please install it from https://git-lfs.com."

private def download (url : HuggingFaceURL) : IO Unit := do
  initGitLFS
  let some dir := (← getModelDir url) |>.parent | unreachable!
  ensureExists dir
  let proc ← IO.Process.output {
    cmd := "git"
    args := #["clone", toString url]
    cwd := dir
  }
  if proc.exitCode != 0 then
    throw $ IO.userError s!"Failed to download the model. You download it manually from {url} and store it in `{dir}/`. See https://huggingface.co/docs/hub/models-downloading for details."

private def downloadGenerator : IO Unit := do
  let some url ← getGeneratorUrl | return ()
  download url

private def downloadEncoder : IO Unit := do
  let some url ← getEncoderUrl | return ()
  download url

private def hasLocalChange (root : FilePath) : IO Bool := do
  checkAvailable "git"
  let proc ← IO.Process.output {
    cmd := "git"
    args := #["diff", "--shortstat"]
    cwd := root
  }
  return proc.exitCode == 0 ∧ proc.stdout != ""

def checkGenerator : IO Unit := do
  let some modelDir ← getGeneratorDir | return ()
  if ← hasLocalChange modelDir then
    IO.FS.removeDirAll modelDir
  if ¬(← modelDir.pathExists) then
    downloadGenerator

def checkEncoder : IO Unit := do
  let some modelDir ← getEncoderDir | return ()
  if ← hasLocalChange modelDir then
    IO.FS.removeDirAll modelDir
  if ¬(← modelDir.pathExists) then
    downloadEncoder

end LeanInfer.Cache