module

public meta import Iris.ProofMode.Aesop.Frontend.Attribute
public meta import Iris.ProofMode.Aesop.Index.Query
public meta import Iris.ProofMode.Aesop.Rule.Backward.Shape
public meta import Iris.ProofMode.Aesop.Rule.Types.Info

public meta section

namespace Iris.ProofMode.Aesop

open Lean Meta

namespace Rule.Backward

def mkBackwardRule (decl : Name) (successProbability : Percent)
    (scope : RuleScope) : MetaM (Rule RuleInfo) := do
  let indexingMode ← Rule.Backward.mkBackwardIndexingMode decl
  return {
    id := {
      name := decl
      kind := .backward
      phase := .unsafe
      scope
    }
    indexingMode
    info := RuleInfo.ofBuilder .backward successProbability
  }

end Rule.Backward

/- Build the discrimination-tree index for all registered backward rules. -/
def backwardRuleIndex : MetaM (Index RuleInfo) := do
  let entries ← getIaesopBackwardLemmas
  let mut idx : Index RuleInfo := {}
  let mut traceEntries : Array String := #[]
  for entry in entries do
    let { decl, successProbability } := entry
    let rule ← Rule.Backward.mkBackwardRule decl successProbability .global
    traceEntries := traceEntries.push
      s!"{decl} ({successProbability}): {toString (format rule.indexingMode)}"
    idx := idx.add rule rule.indexingMode
  trace[iaesop.ruleIndex] s!"iaesop.backward: generated backward index with {entries.size} rules"
  traceEntries.forM λ entry => do
    trace[iaesop.ruleIndex] s!"  {entry}"
  return idx

end Iris.ProofMode.Aesop
