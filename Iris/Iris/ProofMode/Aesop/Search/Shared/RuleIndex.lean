module

public meta import Iris.ProofMode.Aesop.Rule.Backward.Index
public meta import Iris.ProofMode.Aesop.Search.Shared.Configure

public meta section

namespace Iris.ProofMode.Aesop.Search.Shared

open Lean Meta
open Iris.ProofMode.Aesop

def localTheoremRuleIndex (rules : Array LocalTheoremRule) :
    MetaM (Index RuleInfo) := do
  let mut index : Index RuleInfo := {}
  let mut traceEntries : Array String := #[]
  for localRule in rules do
    match localRule.kind with
    | .backward =>
        let rule ← Rule.Backward.mkBackwardRule
          localRule.decl localRule.successProbability .local
        traceEntries := traceEntries.push
          s!"backward {localRule.decl} ({localRule.successProbability}): \
            {toString (format rule.indexingMode)}"
        index := index.add rule rule.indexingMode
    | .forward =>
        throwError "iaesop: local forward theorem rules are not implemented"
    | kind =>
        throwError "iaesop: unsupported local theorem rule kind '{kind}'"
  unless rules.isEmpty do
    trace[iaesop.ruleIndex]
      "iaesop: generated local theorem index with {rules.size} rules"
    traceEntries.forM fun entry => do
      trace[iaesop.ruleIndex] "  {entry}"
  return index

end Iris.ProofMode.Aesop.Search.Shared
