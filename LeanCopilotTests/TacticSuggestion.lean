import LeanCopilot


/-
## Basic Usage
-/

example (a b c : Nat) : a + b + c = a + c + b := by
  suggest_tactics
  sorry

-- You may provide a prefix to constrain the generated tactics.
example (a b c : Nat) : a + b + c = a + c + b := by
  suggest_tactics "rw"
  sorry

/-
## Advanced Usage
-/

open Lean Meta LeanCopilot


set_option LeanCopilot.verbose true in
example (a b c : Nat) : a + b + c = a + c + b := by
  suggest_tactics
  sorry


set_option LeanCopilot.suggest_tactics.check false in
example (a b c : Nat) : a + b + c = a + c + b := by
  suggest_tactics
  sorry


/-
### Configure Generation Parameters
-/

def params := {Builtin.generator.params with
  numReturnSequences := 4
  minLength := 100
  lengthPenalty := 1.0
  temperature := 0.5
}

def updatedModel := {Builtin.generator with params := params}

#eval getModelRegistry
#eval registerGenerator "updatedModel" (.native updatedModel)
#eval getModelRegistry

set_option LeanCopilot.suggest_tactics.model "updatedModel" in
example (a b c : Nat) : a + b + c = a + c + b := by
  suggest_tactics
  sorry


/-
### Bring Your Own Model
-/

def myModel : ExternalGenerator := {
  name := "wellecks/llmstep-mathlib4-pythia2.8b"
  host := "localhost"
  port := 23337
}

#eval registerGenerator "wellecks/llmstep-mathlib4-pythia2.8b" (.external myModel)

set_option LeanCopilot.suggest_tactics.check false in
set_option LeanCopilot.suggest_tactics.model "wellecks/llmstep-mathlib4-pythia2.8b" in
example (a b c : Nat) : a + b + c = a + c + b := by
  suggest_tactics
  sorry
