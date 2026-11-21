import YangMills.Construction.DirichletOperator.NormOfTheRemainderProof
import YangMills.Construction.DirichletOperator.WalkBoundsOnFunctions
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Dirichlet.WalkSeries
open Torus Dirichlet WeightedGreen Dirichlet.WalkExpansion
variable {d L : ℕ} {S aMinus aPlus : ℝ}
theorem hasSum_finsum_of_finite {α : Type*} {s : Set α} (hs : s.Finite) (v : α → ℝ) :
    HasSum (fun c : s => v c) (∑ᶠ a ∈ s, v a) := by
  have := hs.to_subtype
  let := Fintype.ofFinite s
  rw [← finsum_set_coe_eq_finsum_mem, finsum_eq_sum_of_fintype]
  exact hasSum_fintype _
section Functions
variable {ξ : ℝ}
theorem pointwiseMul_add (h f g : LatticeSite d S ξ → ℝ) :
    pointwiseMul h (f + g) = pointwiseMul h f + pointwiseMul h g := by apply _root_.YangMills.Construction.Dirichlet.RemainderNeumann.pointwiseMul_add <;> assumption
end Functions
variable (𝒮 : BlockSetting d L aMinus aPlus S)
variable (E : CentredCube d S → Set (LatticeBond d S 𝒮.ξ))
theorem sandwichedGreen_add (Q : CentredCube d S)
    (hlin : GreenLinearity.BlockGreenFacts 𝒮 (𝒮.innerRegion Q) (E Q))
    (f g : LatticeSite d S 𝒮.ξ → ℝ) :
    𝒮.sandwichedGreen E Q (f + g) = 𝒮.sandwichedGreen E Q f + 𝒮.sandwichedGreen E Q g := by
  simp only [BlockSetting.sandwichedGreen, BlockSetting.cubeGreen, pointwiseMul_add, hlin.map_add]
end YangMills.Construction.Dirichlet.WalkSeries
