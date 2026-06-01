module

public meta import Iris.ProofMode.Aesop.Frontend.Attribute
public meta import Iris.ProofMode.Aesop.Index.Query
public meta import Iris.ProofMode.Aesop.Rule.Backward.Shape
public meta import Iris.ProofMode.Aesop.Rule.Types.Info

public meta section

namespace Iris.ProofMode.Aesop

open Lean Meta

/- Build the discrimination-tree index for all registered backward rules. -/
def backwardRuleIndex : MetaM (Index RuleInfo) := do
  let decls ← getIaesopBackwardLemmas
  let mut idx : Index RuleInfo := {}
  let mut entries : Array String := #[]
  for decl in decls do
    let indexingMode ← Rule.Backward.mkBackwardIndexingMode decl
    let rule : Rule RuleInfo := {
      id := {
        name := decl
        kind := .backward
        phase := .unsafe
        scope := .global
      }
      indexingMode
      info := RuleInfo.ofBuilder .backward
    }
    entries := entries.push s!"{decl}: {toString (format indexingMode)}"
    idx := idx.add rule rule.indexingMode
  trace[iaesop.ruleIndex] s!"iaesop.backward: generated backward index with {entries.size} rules"
  entries.forM λ entry => do
    trace[iaesop.ruleIndex] s!"  {entry}"
  return idx

end Iris.ProofMode.Aesop
