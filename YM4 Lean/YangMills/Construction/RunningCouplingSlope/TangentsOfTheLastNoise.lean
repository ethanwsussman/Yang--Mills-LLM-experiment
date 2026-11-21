import YangMills.Construction.RunningCouplingSlope.GaussianNumbersOfTheSoftChain
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower
def finalNoiseTangents (L n k : ℕ) : Submodule ℝ (LevelForms L n k) where
  carrier := {ξ | ξ.1 = 0 ∧ ∀ i : Fin k, (i : ℕ) + 1 ≠ k → ξ.2 i = 0}
  add_mem' := by
    rintro ξ ξ' ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨by simp [h1, h1'], fun i hi => ?_⟩
    simp [h2 i hi, h2' i hi]
  zero_mem' := ⟨rfl, fun _ _ => rfl⟩
  smul_mem' := by
    rintro c ξ ⟨h1, h2⟩
    refine ⟨by simp [h1], fun i hi => ?_⟩
    simp [h2 i hi]
def FinalNoiseComplement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 1 ≤ k → 0 < n →
    (∀ (X : ChainPoint L n k) (ξ τ : LevelForms L n k), τ ∈ finalNoiseTangents L n k →
      fibreMove X (ξ + τ) = fibreMove X ξ) ∧
    ∀ X : ChainPoint L n k, IsCompactValued X →
      (∀ τ ∈ finalNoiseTangents L n k, topDeriv X τ = 0 → τ = 0) ∧
      ∀ ξ : LevelForms L n k, ∃ τ ∈ finalNoiseTangents L n k, topDeriv X (ξ + τ) = 0
end YangMills.Construction.RunningCouplingSlope
end
