module

public import Iris.BI
public import Iris.ProofMode

@[expose] public section

namespace IAesopTest.Basic

open Iris Iris.BI

/- Independent singleton groups should be solved by the linear platform
without generating metavariable-refinement groups. -/
set_option linter.unusedVariables false in
#time
example [BI PROP]
    (P0 P1 P2 P3 P4 P5 P6 P7 : PROP)
    (P8 P9 P10 P11 P12 P13 P14 : PROP)
    (hCanon0Step0 : P0 ⊢ P14)
    (hCanon0Step1 : P14 ⊢ P7)
    (hConflict0 : P2 ⊢ P7)
    (hConflict6 : P6 ⊢ P7)
    (hCanon1 : P1 ⊢ P8)
    (hConflict5 : P5 ⊢ P8)
    (hCanon2 : P2 ⊢ P9)
    (hConflict1 : P5 ⊢ P9)
    (hConflict7 : P3 ⊢ P9)
    (hCanon3 : P3 ⊢ P10)
    (hConflict3 : P4 ⊢ P10)
    (hCanon4 : P4 ⊢ P11)
    (hConflict2 : P6 ⊢ P11)
    (hConflict8 : P5 ⊢ P11)
    (hCanon5 : P5 ⊢ P12)
    (hConflict4 : P6 ⊢ P12)
    (hCanon6 : P6 ⊢ P13) :
    P0 ∗ (P1 ∗ (P2 ∗ (P3 ∗ (P4 ∗ (P5 ∗ P6))))) ⊢
      P7 ∗ (P8 ∗ (P9 ∗ (P10 ∗ (P11 ∗ (P12 ∗ P13))))) := by
  iaesop bubble bestFirst

end IAesopTest.Basic
