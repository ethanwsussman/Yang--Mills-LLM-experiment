import YangMills.Construction.LimitsOfLatticeFamilies.AdmittedRadii
import YangMills.Construction.LimitsOfLatticeFamilies.SpacesOfFunctionsAndSeparatedTuples
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.LatticeLimits.ModelSpace
structure IsTorusPartitionDatum (s : Conventions.StandingParameters) (M : ℕ) (r : ℝ) {I : Type*}
    [Fintype I] (χ : I → torus.Carrier s → ℝ) (Θ : ℝ) : Prop where
  isBlockScale : IsBlockScale s M
  radius_mem : r ∈ admissibleRadii s torus
  mem_Icc : ∀ ι x, χ ι x ∈ Icc (0 : ℝ) 1
  isC1 : ∀ ι, IsC1 s torus (χ ι)
  sum_eq_one : ∀ x, ∑ ι, χ ι x = 1
  supportIn_subset_closedBall : ∀ ι, ∃ x, supportIn s torus (χ ι) ⊆ ModelSpace.closedBall s torus x r
  one_le : 1 ≤ Θ
  sum_le : ∑ ι, (1 + 40 * (M : ℝ) * TestFunctions.lipConstTorus (ℓ := s.side) (χ ι)) ≤ Θ
end YangMills.Construction.LatticeLimits.ModelSpace
end
