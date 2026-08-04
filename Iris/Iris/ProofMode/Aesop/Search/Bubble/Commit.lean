module

public meta import Iris.ProofMode.Aesop.Rule.Commit.Builtin
public meta import Iris.ProofMode.Aesop.Rule.Commit.Basic
public meta import Iris.ProofMode.Aesop.Rule.Types.Runner
public meta import Iris.ProofMode.Aesop.Search.Bubble.BubbleM
public meta import Iris.ProofMode.Aesop.Search.Bubble.Group

public meta section

namespace Iris.ProofMode.Aesop.Search.Bubble

open Lean Meta
open Iris.ProofMode.Aesop

variable {Q : Type} [Queue Q]

/- Result of one Bubble rule expansion.  This is deliberately separate from
the Copy engine's `RuleResult`: closing one Bubble alternative does not settle
the parent goal or discard its remaining rule matches. -/
inductive BubbleRuleResult
  | closed (closedRapps : Array RappRef)
  | expanded (expandedRapps : Array RappRef)
  | failed
  deriving Inhabited

/- Commit a rule expansion into the shared Goal/Rapp/Obun arena without using
the baseline's context-refill or settlement procedures. -/
def commitRuleOutput (gref : GoalRef) (usedRule : Rule RuleInfo)
    (output : RuleOutput) : BubbleM Q BubbleRuleResult := do
  if output.rappSepcs.isEmpty then return .failed
  let mut rappRefs := #[]

  -- no subgoals => closed, several subgoals => expanded
  let mut closedRapps := #[]
  let mut expandedRapps := #[]
  for spec in output.rappSepcs do
    let (rappRef, goalRefs) ← liftM (m := CoreM Q) <|
      Rule.Commit.Builtin.mkRappSpec gref usedRule spec
    rappRefs := rappRefs.push rappRef
    if goalRefs.isEmpty then
      closedRapps := closedRapps.push rappRef
    else
      expandedRapps := expandedRapps.push rappRef
    registerInitialGroups rappRef goalRefs

  gref.modify fun goal => goal.setChildren (goal.children ++ rappRefs)
  if closedRapps.isEmpty then
    return .expanded expandedRapps
  else
    return .closed closedRapps

end Iris.ProofMode.Aesop.Search.Bubble
