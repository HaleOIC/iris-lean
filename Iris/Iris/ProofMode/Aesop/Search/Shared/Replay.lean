module

public meta import Iris.ProofMode.Aesop.Rule.Dispatch
public meta import Iris.ProofMode.Aesop.Search.Shared.Configure
public meta import Iris.ProofMode.Tactics.Cases
public meta import Iris.ProofMode.Tactics.Exact
public meta import Iris.ProofMode.Tactics.Exists
public meta import Iris.ProofMode.Tactics.Have

public meta section

namespace Iris.ProofMode.Aesop.Search.Shared

open Lean Meta
open Iris.ProofMode.Aesop

private def appliedHypTacticIdent? : AppliedHyp → Option (TSyntax `ident)
  | .spatial hyp | .intuitionistic hyp => some (mkIdent hyp.name)
  | .lean userName _ => some (mkIdent userName)

private def irisHypFrameIdent (hyp : IrisHyp) : TSyntax `frameIdent :=
  ⟨mkIdent hyp.name⟩

private def mkSpatialSpecPat (hyps : Array IrisHyp) : MetaM (TSyntax `specPat) := do
  let names := hyps.map irisHypFrameIdent
  `(specPat| [$[$names:frameIdent]*])

private def mkIApplyTactic (fn : TSyntax `term) (obun : Obun) :
    MetaM (TSyntax `tactic) := do
  if obun.finalizedSpatialSplits.isEmpty then
    `(tactic| iapply $fn:term)
  else
    let spats ← obun.finalizedSpatialSplits.mapM mkSpatialSpecPat
    `(tactic| iapply $fn:term $$ $spats:specPat*)

/-- Reconstruct the surface tactic for a replayed rule.  Both search engines
use this renderer; only their proof-path selection and replay traversal differ. -/
def mkReplayTactic (rapp : Rapp) (obun : Obun) (config : SearchConfig) :
    MetaM (TSyntax `tactic) := do
  let fallback ← `(tactic| skip)
  match rapp.appliedRule.info.builder with
  | .backward =>
      mkIApplyTactic (mkIdent rapp.appliedRule.id.name) obun
  | .tactic .ipureIntro =>
      if config.pureStop? then
        `(tactic| ipureintro)
      else
        let solver : TSyntax `tactic := ⟨config.pureSolver⟩
        `(tactic| (ipureintro; $solver:tactic))
  | .tactic .iexist => `(tactic| iexists _)
  | .tactic .icases =>
      match rapp.usedHyp? >>= appliedHypTacticIdent? with
      | some ident =>
          let binder ← `(binderIdent| $ident:ident)
          let pat ← `(icasesPat| ($binder:binderIdent | $binder:binderIdent))
          `(tactic| icases $ident:term with $pat:icasesPat)
      | none => pure fallback
  | .tactic .icasesFalse =>
      match rapp.usedHyp? >>= appliedHypTacticIdent? with
      | some ident =>
          let pat ← `(icasesPat| ⟨⟩)
          `(tactic| icases $ident:term with $pat:icasesPat)
      | none => pure fallback
  | .tactic .isplit => `(tactic| isplit)
  | .tactic .ileft => `(tactic| ileft)
  | .tactic .iright => `(tactic| iright)
  | .tactic .imodIntro => `(tactic| imodintro)
  | .tactic .imod =>
      match rapp.usedHyp? >>= appliedHypTacticIdent? with
      | some ident =>
          match rapp.generatedSpatialHyps[0]? with
          | some generated =>
              let generatedName := mkIdent generated.name
              let generatedBinder ← `(binderIdent| $generatedName:ident)
              let generatedPat ← `(icasesPat| $generatedBinder:binderIdent)
              `(tactic| imod $ident:term with $generatedPat:icasesPat)
          | none => `(tactic| imod $ident:term)
      | none => pure fallback
  | .tactic .identity =>
      match obun.finalizedSpatialSplits[0]? with
      | some leftContext =>
          let leftIdents := leftContext.map (fun hyp => mkIdent hyp.name)
          `(tactic| isplitl [$leftIdents*])
      | none => pure fallback
  | .tactic .applyHyps =>
      match rapp.usedHyp? >>= appliedHypTacticIdent? with
      | some ident =>
          if obun.goals.isEmpty || obun.kind.isInherited then
            `(tactic| iexact $ident:ident)
          else
            mkIApplyTactic ident obun
      | none => pure fallback
  | .tactic .haveHyps =>
      match rapp.usedHyp? >>= appliedHypTacticIdent?, rapp.generatedSpatialHyps[0]? with
      | some usedIdent, some generatedHyp =>
          let generatedIdent := mkIdent generatedHyp.name
          let generatedBinder ← `(binderIdent| $generatedIdent:ident)
          let generatedPat ← `(icasesPat| $generatedBinder:binderIdent)
          let premiseContexts :=
            obun.finalizedSpatialSplits.extract 0 (obun.goals.size - 1)
          if premiseContexts.isEmpty then
            pure fallback
          else
            let spats ← premiseContexts.mapM mkSpatialSpecPat
            `(tactic| ihave $generatedPat:icasesPat := $usedIdent:term $$ $spats:specPat*)
      | _, _ => pure fallback
  | _ => pure fallback

end Iris.ProofMode.Aesop.Search.Shared
