import YangMills.Construction.SeparatedSequences.SettingsOfOneSequence
import YangMills.Construction.SeparatedSequences.HoelderBoundOfTheExtensionKernelAtATopAndAnExpansionProof
import YangMills.Construction.SeparatedSequences.ClassSequenceHasASettingOfRegions
import YangMills.Construction.SeparatedSequences.PropagatorInASettingOfRegionsOfAClass
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set PeriodicLattice.DirichletOperators
noncomputable section
namespace SeparatedClasses.ApexOneGreenHolderBounds
open SingleSequence SingleSequence.SequenceData
section Seminorms
variable {C : ClassData}
end Seminorms
theorem sum_le_of_termwise {ι : Type} (S : Finset ι) (N : ℕ) (hN : S.card ≤ N) (X E U : ι → ℝ)
    (A Y D W e c : ℝ) (hY : 0 ≤ Y) (he : 0 ≤ e) (hD : 0 ≤ D) (hW : 0 ≤ W)
    (hX : ∀ z ∈ S, X z ≤ A * Y * E z * U z) (hE0 : ∀ z ∈ S, 0 ≤ E z) (hE : ∀ z ∈ S, E z ≤ e * D)
    (hU0 : ∀ z ∈ S, 0 ≤ U z) (hU : ∀ z ∈ S, U z ≤ W) (hc : (N : ℝ) * e * A ≤ c) (hc0 : 0 ≤ c) :
    ∑ z ∈ S, X z ≤ c * Y * D * W := by
  set A' := max A 0 with hA'
  have hA0 : 0 ≤ A' := le_max_right _ _
  have hterm : ∀ z ∈ S, X z ≤ A' * Y * (e * D) * W := by
    intro z hz
    refine (hX z hz).trans ?_
    have h1 : A * Y ≤ A' * Y := mul_le_mul_of_nonneg_right (le_max_left _ _) hY
    have h2 : A * Y * E z ≤ A' * Y * (e * D) :=
      (mul_le_mul_of_nonneg_right h1 (hE0 z hz)).trans
        (mul_le_mul_of_nonneg_left (hE z hz) (mul_nonneg hA0 hY))
    exact (mul_le_mul_of_nonneg_right h2 (hU0 z hz)).trans
      (mul_le_mul_of_nonneg_left (hU z hz) (mul_nonneg (mul_nonneg hA0 hY) (mul_nonneg he hD)))
  have hc' : (N : ℝ) * e * A' ≤ c := by
    rcases le_total A 0 with h | h
    · rw [hA', max_eq_right h]
      simpa using hc0
    · rwa [hA', max_eq_left h]
  have hT : 0 ≤ A' * Y * (e * D) * W :=
    mul_nonneg (mul_nonneg (mul_nonneg hA0 hY) (mul_nonneg he hD)) hW
  calc ∑ z ∈ S, X z ≤ ∑ _z ∈ S, A' * Y * (e * D) * W := Finset.sum_le_sum hterm
    _ = (S.card : ℝ) * (A' * Y * (e * D) * W) := by simp
    _ ≤ (N : ℝ) * (A' * Y * (e * D) * W) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hN) hT
    _ = ((N : ℝ) * e * A') * Y * D * W := by ring
    _ ≤ c * Y * D * W :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hc' hY) hD) hW
section Pieces
variable {C : ClassData} {Ω : ℕ → Set C.Point}
end Pieces
section EvaluationMaps
variable {s : SequenceData} {𝒮 : RegionSequence.NestedRegions} {σ : s.data.BareSite ≃ 𝒮.FineSite}
  {β : s.data.BareBond ≃ 𝒮.FineBond}
open Propagator RegionSequence.NestedRegions
end EvaluationMaps
section Numbers
variable (L : ℕ)
end Numbers
end SeparatedClasses.ApexOneGreenHolderBounds
end
end YangMills.Construction
