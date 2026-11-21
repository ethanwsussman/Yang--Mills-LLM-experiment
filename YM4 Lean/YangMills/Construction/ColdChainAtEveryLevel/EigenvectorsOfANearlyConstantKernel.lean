import YangMills.Construction.ColdChainAtEveryLevel.LineOfANearlyConstantKernel
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace NearlyConstantKernel
def symmetrizedApplyCore {ι : Type} (s : Finset ι) (u : ι → ℝ) (e : ι → ι → ι → ℍ[ℝ]) (v : ι → ℍ[ℝ])
    (i : ι) : ℍ[ℝ] :=
  ∑ i' ∈ s, ∑ i'' ∈ s, (u i' : ℍ[ℝ]) * ((Real.sqrt (u i'') : ℍ[ℝ]) * ((1 + e i i' i'') * v i''))
def UnitEigenvectorsNearOne : Prop :=
  ∀ (ι : Type) (s : Finset ι) (u : ι → ℝ) (e : ι → ι → ι → ℍ[ℝ]) (η : ℝ),
    (∀ i ∈ s, 0 ≤ u i) → ∑ i ∈ s, u i = 1 → 0 ≤ η → η ≤ 1 / 64 →
    (∀ i ∈ s, ∀ i' ∈ s, ∀ i'' ∈ s, ‖e i i' i''‖ ≤ η) →
    (∀ (v : ι → ℍ[ℝ]) (l : ℝ), 1 / 2 ≤ l → ∑ i ∈ s, ‖v i‖ ^ 2 = 1 →
      (∀ i ∈ s, (Real.sqrt (u i) : ℍ[ℝ]) * symmetrizedApplyCore s u e v i = (l : ℍ[ℝ]) * v i) →
      ∃ (h' : ι → ℍ[ℝ]) (c : ℍ[ℝ]), c ≠ 0 ∧ (∀ i ∈ s, ‖h' i - 1‖ ≤ 1) ∧
        ∑ i ∈ s, (u i : ℍ[ℝ]) * h' i = 1 ∧
        (∀ i ∈ s, 1 + perturbationApply s u e h' i = h' i * (l : ℍ[ℝ])) ∧
        ∀ i ∈ s, v i = (Real.sqrt (u i) : ℍ[ℝ]) * (h' i * c)) ∧
    ∀ h : ι → ℍ[ℝ], (∀ i ∈ s, ‖h i - 1‖ ≤ 1 / 2) → ∑ i ∈ s, (u i : ℍ[ℝ]) * h i = 1 →
      (∀ i ∈ s, 1 + perturbationApply s u e h i = h i * (1 + perturbationMean s u e h)) →
      (∀ i ∈ s, ∀ i' ∈ s, ∀ i'' ∈ s, star (e i i' i'') = e i'' i' i) →
      ∃ (l w : ℝ), 1 / 2 ≤ l ∧ 0 < w ∧
        ∑ i ∈ s, ‖(Real.sqrt (u i) : ℍ[ℝ]) * ((w : ℍ[ℝ]) * h i)‖ ^ 2 = 1 ∧
        ∀ i ∈ s, (Real.sqrt (u i) : ℍ[ℝ]) *
            symmetrizedApplyCore s u e (fun j => (Real.sqrt (u j) : ℍ[ℝ]) * ((w : ℍ[ℝ]) * h j)) i =
          (l : ℍ[ℝ]) * ((Real.sqrt (u i) : ℍ[ℝ]) * ((w : ℍ[ℝ]) * h i))
end NearlyConstantKernel
end YangMills.Construction
end
