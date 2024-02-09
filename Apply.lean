import Lean
import LeanCopilot

open Lean Elab Tactic Parser System
open LeanCopilot


deriving instance ToJson, FromJson for String.Pos

structure LocatedDeclDetails where
  declName : Name
  pos : String.Pos
  hasSorry : Bool
  sorryPos : Array String.Pos
deriving ToJson, FromJson, Repr


-- The following codes for pretty printing goals are adapted from [LeanDojo](https://github.com/lean-dojo/LeanDojo).
private def addLine (s : String) : String :=
  if s.isEmpty then s else s ++ "\n"

-- Similar to `Meta.ppGoal` but uses String instead of Format to make sure local declarations are separated by "\n".
private def ppGoal (mvarId : MVarId) : MetaM String := do
  match (← getMCtx).findDecl? mvarId with
  | none          => return "unknown goal"
  | some mvarDecl =>
    let indent         := 2
    let lctx           := mvarDecl.lctx
    let lctx           := lctx.sanitizeNames.run' { options := (← getOptions) }
    Meta.withLCtx lctx mvarDecl.localInstances do
      -- The followint two `let rec`s are being used to control the generated code size.
      -- Then should be remove after we rewrite the compiler in Lean
      let rec pushPending (ids : List Name) (type? : Option Expr) (s : String) : MetaM String := do
        if ids.isEmpty then
          return s
        else
          let s := addLine s
          match type? with
          | none      => return s
          | some type =>
            let typeFmt ← Meta.ppExpr type
            return (s ++ (Format.joinSep ids.reverse (format " ") ++ " :" ++ Format.nest indent (Format.line ++ typeFmt)).group).pretty
      let rec ppVars (varNames : List Name) (prevType? : Option Expr) (s : String) (localDecl : LocalDecl) : MetaM (List Name × Option Expr × String) := do
        match localDecl with
        | .cdecl _ _ varName type _ _ =>
          let varName := varName.simpMacroScopes
          let type ← instantiateMVars type
          if prevType? == none || prevType? == some type then
            return (varName :: varNames, some type, s)
          else do
            let s ← pushPending varNames prevType? s
            return ([varName], some type, s)
        | .ldecl _ _ varName type val _ _ => do
          let varName := varName.simpMacroScopes
          let s ← pushPending varNames prevType? s
          let s  := addLine s
          let type ← instantiateMVars type
          let typeFmt ← Meta.ppExpr type
          let mut fmtElem  := format varName ++ " : " ++ typeFmt
          let val ← instantiateMVars val
          let valFmt ← Meta.ppExpr val
          fmtElem := fmtElem ++ " :=" ++ Format.nest indent (Format.line ++ valFmt)
          let s := s ++ fmtElem.group.pretty
          return ([], none, s)
      let (varNames, type?, s) ← lctx.foldlM (init := ([], none, "")) fun (varNames, prevType?, s) (localDecl : LocalDecl) =>
         if localDecl.isAuxDecl || localDecl.isImplementationDetail then
           -- Ignore auxiliary declarations and implementation details.
           return (varNames, prevType?, s)
         else
           ppVars varNames prevType? s localDecl
      let s ← pushPending varNames type? s
      let goalTypeFmt ← Meta.ppExpr (← instantiateMVars mvarDecl.type)
      let goalFmt := Meta.getGoalPrefix mvarDecl ++ Format.nest indent goalTypeFmt
      let s := s ++ "\n" ++ goalFmt.pretty
      match mvarDecl.userName with
      | Name.anonymous => return s
      | name           => return "case " ++ name.eraseMacroScopes.toString ++ "\n" ++ s

def ppGoals (ctx : ContextInfo) (goals : List MVarId) : IO String :=
  if goals.isEmpty then
    return "no goals"
  else
    let fmt := ctx.runMetaM {} (return Std.Format.prefixJoin "\n\n" (← goals.mapM (ppGoal ·)))
    return (← fmt).pretty.trim


-- Note that instead of the standard `hasSorry`, what we really want is the exact `isSorry` assertion & position.
partial def IsSorry : InfoTree → IO Bool :=
  go none
where go ci?
  | .context ci t => go (ci.mergeIntoOuter? ci?) t
  | .node i cs =>
    match ci?, i with
    | some ci, .ofTermInfo ti
    | some ci, .ofOmissionInfo { toTermInfo := ti } => do
      let expr ← ti.runMetaM ci (instantiateMVars ti.expr)
      return expr.hasSorry
    | _, _ =>
      cs.anyM (go ci?)
  | _ => return false

partial def extractSorryPos : InfoTree → IO (Array String.Pos) :=
  go none
where go ci?
  | .context ci t => go (ci.mergeIntoOuter? ci?) t
  | .node i cs =>
    match ci?, i with
    | some ci, .ofTermInfo ti
    | some ci, .ofOmissionInfo { toTermInfo := ti } => do
      let expr ← ti.runMetaM ci (instantiateMVars ti.expr)
      if expr.isSorry then
        let pos := match (ti.stx.getPos?) with
          | some pos => pos
          | none => panic! "extractSorryPos: missing position information"
        return #[pos]
      else
        return #[]
    | _, _ =>
      cs.foldlM (init := #[]) (fun acc t => do
        let pos ← go ci? t
        return acc ++ pos)
  | _ => return #[]


def extractDeclName (stx : Syntax) : Option Name := do
  let declId ← stx.find? (·.getKind == `Lean.Parser.Command.declId)
  let id ← declId.getHead?
  return id.getId

partial def extractDeclInfo (fileMap : FileMap) (acc : Array LocatedDeclDetails := #[]) (t : InfoTree) : IO (Array LocatedDeclDetails) := do
  match t with
  | .context _ctx tree => extractDeclInfo fileMap acc tree
  | .node info children => do
    let childLeaves ← children.toArray.foldlM (extractDeclInfo fileMap ·) acc
    let hasSorry ← IsSorry t
    let sorryPos ← extractSorryPos t
    let locatedDeclDetails? : Option LocatedDeclDetails := do
      let .ofCommandInfo cmdInfo := info | none
      guard <| cmdInfo.elaborator == `Lean.Elab.Command.elabDeclaration
      let decl := cmdInfo.stx
      let id ← extractDeclName decl
      let pos ← decl.getPos? true
      return ⟨id, pos, hasSorry, sorryPos⟩
    match locatedDeclDetails? with
    | some locatedDeclDetails => return childLeaves.push locatedDeclDetails
    | none => return childLeaves
  | _ => return acc

def extractSorryInfo (decl : LocatedDeclDetails) (fileMap : FileMap) (tree : InfoTree) : List (String.Pos × List String) :=
  let sorryPos := decl.sorryPos
  let goalresults := (sorryPos.map (tree.goalsAt? fileMap ·)).toList
  let goals := goalresults.mapM (fun goals => goals.mapM fun goal => do
    let ti := goal.tacticInfo
    ppGoals goal.ctxInfo ti.goalsBefore
  )
  let goalStrs := match goals.run' () with
    | some v => v
    | none => panic! "extractSorryInfo: failed to extract local goals"
  sorryPos.toList.zip goalStrs

def resolveDeclsAux (fileMap : FileMap) (acc : Array LocatedDeclDetails := #[]) (t : InfoTree) : IO ((Array LocatedDeclDetails) × (List (String.Pos × List String))) := do
  let declDetails ← extractDeclInfo fileMap acc t
  let sorryInfo := (declDetails.filter (fun decl => decl.hasSorry)).map (fun decl => extractSorryInfo decl fileMap t)
  let flatSorryInfo := sorryInfo.toList.join
  return (declDetails, flatSorryInfo)

def resolveDecls (fileMap : FileMap) (trees : Array InfoTree) : IO ((Array LocatedDeclDetails) × (Array (String.Pos × List String))):= do
  let result ← trees.mapM (resolveDeclsAux fileMap)
  let decls := (result.map (fun (decls, _) => decls.toList)).toList.join
  let sorries := (result.map (fun (_, sorries) => sorries)).toList.join
  return (decls.toArray, sorries.toArray)

def extractDecls (file : System.FilePath) : IO <| ((Array LocatedDeclDetails) × (Array (String.Pos × List String))) := do
  let fileContents ← IO.FS.readFile file
  let fileMap := FileMap.ofString fileContents
  let context := Parser.mkInputContext fileContents file.toString
  let (header, state, messages) ← Parser.parseHeader context
  let (environment, messages) ← processHeader header {} messages context 0
  if messages.hasErrors then
    for msg in messages.toList do
      if msg.severity == .error then
        IO.throwServerError =<< msg.toString
  let commandState := { Command.mkState environment messages with infoState := { enabled := true } }
  let s ← IO.processCommands context state commandState
  resolveDecls fileMap s.commandState.infoState.trees.toArray

def sorryCount (file : System.FilePath) : IO Nat := do
  let decls ← extractDecls file
  return decls.1.foldl (init := 0) (fun acc decl => if decl.hasSorry then acc + 1 else acc)

def extractSorryDecls (file : System.FilePath) : IO (Array LocatedDeclDetails) := do
  let decls ← extractDecls file
  return decls.1.filter (fun decl => decl.hasSorry)

def extractSorry (file : System.FilePath) : IO (Array (String.Pos × List String)) := do
  let decls ← extractDecls file
  return decls.2


-- Quick test.
def exampleFilePath : System.FilePath := "../test/Example.lean"

#eval extractDecls exampleFilePath
#eval sorryCount exampleFilePath
#eval extractSorryDecls exampleFilePath
#eval extractSorry exampleFilePath
