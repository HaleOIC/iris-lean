module

public meta import Lean
public meta import Iris.ProofMode.Aesop.Util.Percent

public meta section

namespace Iris.ProofMode.Aesop

open Lean Elab

structure RuleAttrEntry where
  decl : Name
  successProbability : Percent
  deriving Inhabited

/-- Theorems registered with `@[iaesop backward <p>%]`. -/
initialize iaesopBackwardExt :
    SimpleScopedEnvExtension RuleAttrEntry (Array RuleAttrEntry) ←
  registerSimpleScopedEnvExtension {
    addEntry := λ s entry =>
      if s.any λ old => old.decl == entry.decl then s else s.push entry
    initial := #[]
  }

/-- Theorems registered with `@[iaesop forward <p>%]`. -/
initialize iaesopForwardExt :
    SimpleScopedEnvExtension RuleAttrEntry (Array RuleAttrEntry) ←
  registerSimpleScopedEnvExtension {
    addEntry := λ s entry =>
      if s.any λ old => old.decl == entry.decl then s else s.push entry
    initial := #[]
  }

namespace Parser

declare_syntax_cat iaesopAttrRule
syntax "forward" num "%" : iaesopAttrRule
syntax "backward" num "%" : iaesopAttrRule

syntax (name := iaesop) "iaesop" (ppSpace iaesopAttrRule)+ : attr

end Parser

inductive AttrRule where
  | backward (successProbability : Percent)
  | forward (successProbability : Percent)

namespace AttrRule

private def elabSuccessProbability (kind : String) (p : Syntax) : CoreM Percent := do
  let some p := p.isNatLit?
    | throwError "iaesop: expected a numeral success probability for {kind} rule"
  match Percent.ofNat p with
  | some p => return p
  | none => throwError
      "iaesop: {kind} rule success probability '{p}%' is not between 0 and 100"

def «elab» (stx : Syntax) : CoreM AttrRule :=
  withRef stx do
    match stx with
    | `(iaesopAttrRule| forward $p:num %) =>
      return .forward (← elabSuccessProbability "forward" p)
    | `(iaesopAttrRule| backward $p:num %) =>
      return .backward (← elabSuccessProbability "backward" p)
    | _ => throwUnsupportedSyntax

end AttrRule

structure AttrConfig where
  rules : Array AttrRule

namespace AttrConfig

def «elab» (stx : Syntax) : CoreM AttrConfig :=
  withRef stx do
    match stx with
    | `(attr| iaesop $[$rules:iaesopAttrRule]*) =>
        return { rules := ← rules.mapM AttrRule.elab }
    | _ => throwUnsupportedSyntax

end AttrConfig

private def addBackwardRule (decl : Name) (successProbability : Percent)
    (kind : AttributeKind) : CoreM Unit := do
  if (iaesopBackwardExt.getState (← getEnv)).any λ entry => entry.decl == decl then
    throwError "iaesop: backward rule '{decl}' is already registered"
  iaesopBackwardExt.add { decl, successProbability } kind

private def addForwardRule (decl : Name) (successProbability : Percent)
    (kind : AttributeKind) : CoreM Unit := do
  if (iaesopForwardExt.getState (← getEnv)).any λ entry => entry.decl == decl then
    throwError "iaesop: forward rule '{decl}' is already registered"
  iaesopForwardExt.add { decl, successProbability } kind

initialize registerBuiltinAttribute {
  name := `iaesop
  descr := "Register a declaration as an iaesop rule."
  applicationTime := .afterCompilation
  add := fun decl stx kind => withRef stx do
    let config ← AttrConfig.elab stx
    for rule in config.rules do
      match rule with
      | .backward successProbability => addBackwardRule decl successProbability kind
      | .forward successProbability => addForwardRule decl successProbability kind
}

/-- All lemmas currently registered with `@[iaesop backward <p>%]`. -/
def getIaesopBackwardLemmas [Monad m] [MonadEnv m] : m (Array RuleAttrEntry) := do
  return iaesopBackwardExt.getState (← getEnv)

/-- All lemmas currently registered with `@[iaesop forward <p>%]`. -/
def getIaesopForwardLemmas [Monad m] [MonadEnv m] : m (Array RuleAttrEntry) := do
  return iaesopForwardExt.getState (← getEnv)

end Iris.ProofMode.Aesop
