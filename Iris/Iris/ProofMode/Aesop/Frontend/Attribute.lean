module

public meta import Lean

public meta section

namespace Iris.ProofMode.Aesop

open Lean Elab

/-- Names of theorems registered with `@[iaesop backward]`. -/
initialize iaesopBackwardExt : SimpleScopedEnvExtension Name (Array Name) ←
  registerSimpleScopedEnvExtension {
    addEntry := λ s n => if s.contains n then s else s.push n
    initial := #[]
  }

/-- Names of theorems registered with `@[iaesop forward]`. -/
initialize iaesopForwardExt : SimpleScopedEnvExtension Name (Array Name) ←
  registerSimpleScopedEnvExtension {
    addEntry := λ s n => if s.contains n then s else s.push n
    initial := #[]
  }

namespace Parser

declare_syntax_cat iaesopAttrRule
syntax "forward" : iaesopAttrRule
syntax "backward" : iaesopAttrRule

syntax (name := iaesop) "iaesop" (ppSpace iaesopAttrRule)+ : attr

end Parser

inductive AttrRule where
  | backward
  | forward

namespace AttrRule

def «elab» (stx : Syntax) : CoreM AttrRule :=
  withRef stx do
    match stx with
    | `(iaesopAttrRule| forward) => return .forward
    | `(iaesopAttrRule| backward) => return .backward
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

private def addBackwardRule (decl : Name) (kind : AttributeKind) : CoreM Unit := do
  if (iaesopBackwardExt.getState (← getEnv)).contains decl then
    throwError "iaesop: backward rule '{decl}' is already registered"
  iaesopBackwardExt.add decl kind

private def addForwardRule (decl : Name) (kind : AttributeKind) : CoreM Unit := do
  if (iaesopForwardExt.getState (← getEnv)).contains decl then
    throwError "iaesop: forward rule '{decl}' is already registered"
  iaesopForwardExt.add decl kind

initialize registerBuiltinAttribute {
  name := `iaesop
  descr := "Register a declaration as an iaesop rule."
  applicationTime := .afterCompilation
  add := fun decl stx kind => withRef stx do
    let config ← AttrConfig.elab stx
    for rule in config.rules do
      match rule with
      | .backward => addBackwardRule decl kind
      | .forward => addForwardRule decl kind
}

/-- All lemmas currently registered with `@[iaesop backward]`. -/
def getIaesopBackwardLemmas [Monad m] [MonadEnv m] : m (Array Name) := do
  return iaesopBackwardExt.getState (← getEnv)

/-- All lemmas currently registered with `@[iaesop forward]`. -/
def getIaesopForwardLemmas [Monad m] [MonadEnv m] : m (Array Name) := do
  return iaesopForwardExt.getState (← getEnv)

end Iris.ProofMode.Aesop
