import YangMills.Construction.RunningCouplingSlope.PlainCovariantMaps
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower Matrices
variable {L n k : ℕ}
def tangentForms (U : Edge L n k 0 → ComplexMatrix2) (ξ : LevelForms L n k) :
    (j : ℕ) → Edge L n k j → ComplexMatrix2
  | 0 => ξ.1
  | j + 1 =>
    meanCovariantStep (meanIterate U j) (tangentForms U ξ j) +
      if h : j < k then (ξ.2 ⟨j, h⟩ : Edge L n k (j + 1) → ComplexMatrix2) else 0
end YangMills.Construction.RunningCouplingSlope
end
