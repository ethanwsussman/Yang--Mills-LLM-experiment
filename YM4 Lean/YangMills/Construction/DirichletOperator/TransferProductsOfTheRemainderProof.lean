import YangMills.Construction.DirichletOperator.PropagatorBoundsForDivergenceSourcesProof
import YangMills.Construction.RegionSequence.WeightedDistTriangleProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Torus
open RegionSequence RegionSequence.NestedRegions PartitionCubes Propagator PropagatorThresholds
  RemainderEstimates
namespace KernelChains
theorem chainWeight_nonneg (𝒯 : NestedRegions) (Γ : List (TorusSegment 4)) :
    0 ≤ 𝒯.chainWeight Γ := by apply _root_.YangMills.Construction.RegionSequence.WeightedDist.chainWeight_nonneg <;> assumption
variable {𝒮 : NestedRegions} {M : ℕ}
theorem weighted_row_sum_le {Y : Type} [Fintype Y] (n w e : Y → Y → ℝ) (c : Y → ℝ)
    (hn : ∀ y y'', 0 ≤ n y y'') (hc : ∀ y, 0 ≤ c y)
    (he : ∀ y y'' y', e y'' y' ≤ w y y'' * e y y') (he₀ : ∀ y y', 0 ≤ e y y')
    (hrow : ∀ y, ∑ y'', w y y'' * n y y'' ≤ 1 / 2) (y : Y) :
    ∑ y'', n y y'' * ∑ y', e y'' y' * c y' ≤ 2⁻¹ * ∑ y', e y y' * c y' := by
  calc ∑ y'', n y y'' * ∑ y', e y'' y' * c y'
      = ∑ y', ∑ y'', n y y'' * (e y'' y' * c y') := by
        simp only [Finset.mul_sum]
        exact Finset.sum_comm
    _ ≤ ∑ y', ∑ y'', (w y y'' * n y y'') * (e y y' * c y') := by
        refine Finset.sum_le_sum fun y' _ => Finset.sum_le_sum fun y'' _ => ?_
        have h₁ : e y'' y' * c y' ≤ (w y y'' * e y y') * c y' :=
          mul_le_mul_of_nonneg_right (he y y'' y') (hc y')
        calc n y y'' * (e y'' y' * c y') ≤ n y y'' * ((w y y'' * e y y') * c y') :=
              mul_le_mul_of_nonneg_left h₁ (hn y y'')
          _ = (w y y'' * n y y'') * (e y y' * c y') := by ring
    _ = ∑ y', (∑ y'', w y y'' * n y y'') * (e y y' * c y') := by
        simp only [Finset.sum_mul]
    _ ≤ ∑ y', 2⁻¹ * (e y y' * c y') := by
        refine Finset.sum_le_sum fun y' _ => ?_
        have h₂ : ∑ y'', w y y'' * n y y'' ≤ 2⁻¹ := by
          simpa [one_div] using hrow y
        exact mul_le_mul_of_nonneg_right h₂ (mul_nonneg (he₀ y y') (hc y'))
    _ = 2⁻¹ * ∑ y', e y y' * c y' := by
        rw [Finset.mul_sum]
end KernelChains
end YangMills.Construction
