import YangMills.Construction.DirichletOperator.ChainOfRemaindersProof
import YangMills.Construction.Dirichlet.BlockGreenLinear
import YangMills.Construction.Dirichlet.CentresAndCells
import YangMills.Construction.Dirichlet.RegionEnergyEstimate
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus YangMills.Construction.Dirichlet
noncomputable section
namespace YangMills.Construction.Dirichlet.GreenLinearityProof
variable {d L : ℕ} {S aMinus aPlus : ℝ}
theorem restrictTo_add {ξ : ℝ} (X : Set (PeriodicTorus d S)) (f g : LatticeSite d S ξ → ℝ) :
    restrictTo X (f + g) = restrictTo X f + restrictTo X g := by
  funext x
  by_cases h : (x : PeriodicTorus d S) ∈ X <;> simp [restrictTo, indicator, h]
theorem dirichletLaplacian_add {ξ : ℝ} [Finite (LatticeSite d S ξ)]
    (W : Set (PeriodicTorus d S)) (E : Set (LatticeBond d S ξ)) (f g : LatticeSite d S ξ → ℝ) :
    dirichletLaplacian W E (f + g) = dirichletLaplacian W E f + dirichletLaplacian W E g := by
  unfold dirichletLaplacian
  rw [← restrictTo_add]
  congr 1
  funext x
  have hsum : (∑ᶠ x' ∈ {x' : LatticeSite d S ξ | IsNeighbor x x' ∧ (x' : PeriodicTorus d S) ∈ W},
        (f x + g x - (f x' + g x'))) =
      (∑ᶠ x' ∈ {x' : LatticeSite d S ξ | IsNeighbor x x' ∧ (x' : PeriodicTorus d S) ∈ W},
        (f x - f x')) +
      ∑ᶠ x' ∈ {x' : LatticeSite d S ξ | IsNeighbor x x' ∧ (x' : PeriodicTorus d S) ∈ W},
        (g x - g x') := by
    rw [← finsum_mem_add_distrib (Set.toFinite _)]
    refine finsum_mem_congr rfl fun x' _ => ?_
    ring
  simp only [Pi.add_apply]
  rw [hsum]
  ring
namespace BlockOps
variable (𝒮 : BlockSetting d L aMinus aPlus S)
theorem cellAverage_add [Finite (LatticeSite d S 𝒮.ξ)]
    (f g : LatticeSite d S 𝒮.ξ → ℝ) (y : PeriodicTorus d S) :
    𝒮.cellAverage (f + g) y = 𝒮.cellAverage f y + 𝒮.cellAverage g y := by
  unfold BlockSetting.cellAverage
  simp only [Pi.add_apply]
  rw [finsum_mem_add_distrib (Set.toFinite _), mul_add]
theorem averagingOp_add [Finite (LatticeSite d S 𝒮.ξ)]
    (f g : LatticeSite d S 𝒮.ξ → ℝ) :
    𝒮.averagingOp (f + g) = 𝒮.averagingOp f + 𝒮.averagingOp g := by
  unfold BlockSetting.averagingOp
  rw [← restrictTo_add]
  congr 1
  funext x
  simp only [Pi.add_apply, cellAverage_add]
  ring
end BlockOps
end YangMills.Construction.Dirichlet.GreenLinearityProof
