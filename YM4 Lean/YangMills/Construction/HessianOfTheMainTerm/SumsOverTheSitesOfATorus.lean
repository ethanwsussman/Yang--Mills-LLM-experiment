import YangMills.Construction.HessianOfTheMainTerm.LengthOfASiteOfATorus
import Mathlib
set_option autoImplicit false
open YangMills.Construction.PeriodicLattice
noncomputable section
namespace YangMills.Construction.HessianOfTheMainTerm.SiteSums
def BallDoublingAndWeightBound : Prop :=
  (∀ (L m : ℕ) (j : ℤ) (_ : Fintype (Site L m j)) (ℓ : ℕ), 1 < L → 0 ≤ (m : ℤ) + j → 1 ≤ ℓ →
    ℓ < sitesPerSide L m j →
    ∀ (_ : DecidablePred fun u : Site L m j => supLengthInMesh u < (ℓ : ℝ))
      (_ : DecidablePred fun u : Site L m j => supLengthInMesh u ≤ (ℓ : ℝ) / 2),
      ((Finset.univ.filter fun u : Site L m j => supLengthInMesh u < (ℓ : ℝ)).card : ℝ) ≤
        16 * ((Finset.univ.filter fun u : Site L m j => supLengthInMesh u ≤ (ℓ : ℝ) / 2).card : ℝ)) ∧
  ∀ μ : ℝ, 0 < μ → ∃ T : ℝ, 0 < T ∧ ∀ (L m : ℕ) (j : ℤ) (_ : Fintype (Site L m j)), 1 < L →
    0 ≤ (m : ℤ) + j → ∀ x : Site L m j,
      ∑ x' : Site L m j, (1 + supLengthInMesh (x' - x)) ^ 2 * Real.exp (-μ * supLengthInMesh (x' - x)) ≤ T
end YangMills.Construction.HessianOfTheMainTerm.SiteSums
