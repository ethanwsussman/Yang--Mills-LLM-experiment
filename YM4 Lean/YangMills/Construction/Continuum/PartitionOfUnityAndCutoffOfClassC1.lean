import YangMills.Construction.Continuum.FlatSchwartzAndTuples
import Mathlib
set_option autoImplicit false
open YangMills.Construction.EuclideanBalls
namespace YangMills.Construction.PartitionOfUnity
def C1PartitionAndCutoffExist : Prop :=
  (∀ d : ℕ, (d = 2 ∨ d = 4) → ∀ ε : ℝ, 0 < ε →
    ∃ χ : (Fin d → ℤ) → (Fin d → ℝ) → ℝ,
      (∀ m, χ m ∈ compactC1 d ℝ) ∧
      (∀ m z, χ m z ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ m, ∀ x ∈ tsupport (χ m), ∀ y ∈ tsupport (χ m),
        EuclideanCoords.sqrtSumSq (x - y) ≤ 4 * ε) ∧
      (∀ B : Set (Fin d → ℝ), Bornology.IsBounded B →
        {m | (tsupport (χ m) ∩ B).Nonempty}.Finite) ∧
      (∀ z, HasSum (fun m => χ m z) 1)) ∧
  (∀ ρ : ℝ, 0 < ρ →
    ∃ χ : (Fin 2 → ℝ) → ℝ,
      χ ∈ compactC1 2 ℝ ∧
      (∀ y, χ y ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ y, EuclideanCoords.sqrtSumSq y ≤ ρ → χ y = 1) ∧
      (∀ y, Real.sqrt 2 * ρ ≤ EuclideanCoords.sqrtSumSq y → χ y = 0))
end YangMills.Construction.PartitionOfUnity
