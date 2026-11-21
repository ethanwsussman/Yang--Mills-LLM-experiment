import YangMills.Construction.Dirichlet.CentresAndCells
import YangMills.Construction.WeightedGreen.DecayRateDefs
import YangMills.Construction.Dirichlet.BilinearForms
import YangMills.Construction.Dirichlet.RegionEnergyEstimate
import YangMills.Construction.LatticeCalculus.Identities
import YangMills.Construction.WeightedGreen.DecayRateBounds
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YangMills.Construction.Dirichlet.RegionEnergy
variable {d L : ℕ} {S aMinus aPlus ξ : ℝ}
section InnerSum
variable [Fintype (LatticeSite d S ξ)]
theorem innerSum_eq_sum (f g : LatticeSite d S ξ → ℝ) :
    innerSum f g = ξ ^ d * ∑ x, f x * g x := by
  rw [innerSum, finsum_eq_sum_of_fintype]
theorem innerSum_comm (f g : LatticeSite d S ξ → ℝ) : innerSum f g = innerSum g f := by
  simp only [innerSum_eq_sum, mul_comm (f _)]
theorem restrictTo_add (X : Set (Torus.PeriodicTorus d S)) (f g : LatticeSite d S ξ → ℝ) :
    restrictTo X (f + g) = restrictTo X f + restrictTo X g := Set.indicator_add _ _ _
theorem dirichletLaplacian_add (W : Set (Torus.PeriodicTorus d S)) (E : Set (LatticeBond d S ξ))
    (f g : LatticeSite d S ξ → ℝ) :
    dirichletLaplacian W E (f + g) = dirichletLaplacian W E f + dirichletLaplacian W E g := by
  simp only [dirichletLaplacian]
  rw [← restrictTo_add]
  congr 1
  funext x
  have hs : {y : LatticeSite d S ξ | IsNeighbor x y ∧ (y : Torus.PeriodicTorus d S) ∈ W}.Finite :=
    Set.toFinite _
  have h : ∑ᶠ y ∈ {y : LatticeSite d S ξ | IsNeighbor x y ∧ (y : Torus.PeriodicTorus d S) ∈ W},
      ((f + g) x - (f + g) y) =
      (∑ᶠ y ∈ {y : LatticeSite d S ξ | IsNeighbor x y ∧ (y : Torus.PeriodicTorus d S) ∈ W},
        (f x - f y)) +
      ∑ᶠ y ∈ {y : LatticeSite d S ξ | IsNeighbor x y ∧ (y : Torus.PeriodicTorus d S) ∈ W},
        (g x - g y) := by
    rw [← finsum_mem_add_distrib hs]
    refine finsum_mem_congr rfl fun y _ => ?_
    simp only [Pi.add_apply]
    ring
  simp only [Pi.add_apply] at h ⊢
  rw [h]
  ring
end InnerSum
section Setting
variable (𝒮 : BlockSetting d L aMinus aPlus S) [Fintype (LatticeSite d S 𝒮.ξ)]
theorem cellAverage_add (f g : LatticeSite d S 𝒮.ξ → ℝ) (y : Torus.PeriodicTorus d S) :
    𝒮.cellAverage (f + g) y = 𝒮.cellAverage f y + 𝒮.cellAverage g y := by
  simp only [BlockSetting.cellAverage, Pi.add_apply]
  rw [finsum_mem_add_distrib (Set.toFinite _)]
  ring
theorem averagingOp_add (f g : LatticeSite d S 𝒮.ξ → ℝ) :
    𝒮.averagingOp (f + g) = 𝒮.averagingOp f + 𝒮.averagingOp g := by
  simp only [BlockSetting.averagingOp]
  rw [← restrictTo_add]
  congr 1
  funext x
  simp only [cellAverage_add, Pi.add_apply]
  ring
end Setting
section Forms
variable (𝒮 : BlockSetting d L aMinus aPlus S) [Fintype (LatticeSite d S 𝒮.ξ)]
theorem localWeight_pos (hρ : ∀ x, 0 < 𝒮.localScale x) (x : LatticeSite d S 𝒮.ξ) :
    0 < 𝒮.localWeight x := by
  have := hρ x
  simp only [BlockSetting.localWeight]
  positivity
end Forms
section Energy
variable (𝒮 : BlockSetting d L aMinus aPlus S) [Fintype (LatticeSite d S 𝒮.ξ)]
end Energy
end YangMills.Construction.Dirichlet.RegionEnergy
