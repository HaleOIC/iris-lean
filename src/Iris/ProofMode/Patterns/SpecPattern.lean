/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser, Zongyuan Liu, Yunsong Yang
-/
module

@[expose] public section

namespace Iris.ProofMode
open Lean

declare_syntax_cat specPat

-- TODO: support `[$]`, `[> $]`, and `[# $]` syntax once `iframe` tactic finished
-- TODO: support `//` suffix syntax once `done` tactic finished
syntax ident : specPat
syntax "%" term:max : specPat
syntax "[" ident* "]" optional(" as " ident) : specPat
syntax "[-" ident* "]" optional(" as " ident) : specPat
syntax "[>" ident* "]" optional(" as " ident) : specPat
syntax "[>-" ident* "]" optional(" as " ident) : specPat
-- TODO: replace this placeholder syntax by `[# $H1 .. $Hn]` once framing syntax is supported.
syntax "[#]" optional(" as " ident) : specPat

inductive SpecGoalKind
  | spatial
  | modal
  | intuitionistic
  deriving Repr, Inhabited

-- see https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris/proofmode/spec_patterns.v?ref_type=heads#L15
inductive SpecPat
  | ident (name : Ident)
  | pure (t : Term)
  | goal (kind : SpecGoalKind) (negate : Bool) (names : List Ident) (goalName : Name)
  deriving Repr, Inhabited

def SpecPat.isModal : SpecPat → Bool
  | .goal .modal .. => true
  | _ => false

partial def SpecPat.parse (pat : Syntax) : MacroM SpecPat := do
  match go ⟨← expandMacros pat⟩ with
  | none => Macro.throwUnsupported
  | some pat => return pat
where
  go : TSyntax `specPat → Option SpecPat
  | `(specPat| $name:ident) => some <| .ident name
  | `(specPat| % $term:term) => some <| .pure term
  | `(specPat| [$[$names:ident]*]) => some <| .goal .spatial false names.toList .anonymous
  | `(specPat| [$[$names:ident]*] as $goal:ident) => match goal.raw with
    | .ident _ _ val _ => some <| .goal .spatial false names.toList val
    | _ => none
  | `(specPat| [-$[$names:ident]*]) => some <| .goal .spatial true names.toList .anonymous
  | `(specPat| [-$[$names:ident]*] as $goal:ident) => match goal.raw with
    | .ident _ _ val _ => some <| .goal .spatial true names.toList val
    | _ => none
  | `(specPat| [>$[$names:ident]*]) => some <| .goal .modal false names.toList .anonymous
  | `(specPat| [>$[$names:ident]*] as $goal:ident) => match goal.raw with
    | .ident _ _ val _ => some <| .goal .modal false names.toList val
    | _ => none
  | `(specPat| [>-$[$names:ident]*]) => some <| .goal .modal true names.toList .anonymous
  | `(specPat| [>-$[$names:ident]*] as $goal:ident) => match goal.raw with
    | .ident _ _ val _ => some <| .goal .modal true names.toList val
    | _ => none
  | `(specPat| [#]) => some <| .goal .intuitionistic false [] .anonymous
  | `(specPat| [#] as $goal:ident) => match goal.raw with
    | .ident _ _ val _ => some <| .goal .intuitionistic false [] val
    | _ => none
  | _ => none
