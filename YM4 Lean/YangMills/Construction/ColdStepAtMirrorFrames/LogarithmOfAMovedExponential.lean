import YangMills.Construction.ColdChainAtEveryLevel.LevelsAndFields
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
def diagonalTriple (r : imaginaryQuaternions) :
    imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions := (r, 0, r)
def ConjugatedExpLogSmooth : Prop :=
  ∃ (Θ : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions → imaginaryQuaternions)
    (U : Set (imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions)) (C : ℝ), IsOpen U ∧ 0 ≤ C ∧
    (∀ r, diagonalTriple r ∈ U) ∧ ContDiffOn ℝ 3 Θ U ∧
    (∀ z ∈ U, expUnit (Θ z) = expUnit z.1 * expUnit z.2.1 * (expUnit z.2.2)⁻¹) ∧
    (∀ r, Θ (diagonalTriple r) = 0) ∧
    (∀ (r : imaginaryQuaternions) (j : ℕ), ‖r‖ ≤ 1 → j ≤ 3 → ‖iteratedFDeriv ℝ j Θ (diagonalTriple r)‖ ≤ C) ∧
    (∀ z : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions,
      fderiv ℝ Θ 0 z = z.1 + z.2.1 - z.2.2) ∧
    ∀ (r : imaginaryQuaternions) (z : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions),
      ‖r‖ ≤ 1 → ‖fderiv ℝ Θ (diagonalTriple r) z - fderiv ℝ Θ 0 z‖ ≤ C * ‖r‖ * ‖z‖
end ColdStepAtMirrorFrames
end YangMills.Construction
end
