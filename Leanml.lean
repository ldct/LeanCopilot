import Lean

open Lean Elab Parser Term Meta Tactic

def hello := "world"

elab "trace_goal_state" : tactic => do
  let goals ← getUnsolvedGoals
  let msg ← MessageData.toString <| ← addMessageContext <| goalsToMessageData goals
  logInfo <| s!"[GOAL STATE] {msg}"
