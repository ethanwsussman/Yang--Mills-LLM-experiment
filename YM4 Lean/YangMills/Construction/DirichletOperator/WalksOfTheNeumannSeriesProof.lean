import YangMills.Construction.Dirichlet.CutoffDifferenceBoundsProof
import YangMills.Construction.DirichletOperator.ChainOfRemaindersProof
import YangMills.Construction.DirichletOperator.NeumannSeriesOfTheRemainderProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Torus Dirichlet
namespace Dirichlet.NeumannWalks
section Lists
variable {α X : Type*}
end Lists
section Cubes
variable {d L : ℕ} {S aMinus aPlus : ℝ} (𝒮 : BlockSetting d L aMinus aPlus S)
theorem pointwiseMul_add {ξ : ℝ} (h f g : LatticeSite d S ξ → ℝ) :
    pointwiseMul h (f + g) = pointwiseMul h f + pointwiseMul h g := by apply _root_.YangMills.Construction.Dirichlet.RemainderNeumann.pointwiseMul_add <;> assumption
variable (E : CentredCube d S → Set (LatticeBond d S 𝒮.ξ))
theorem sandwichedGreen_add (Q : CentredCube d S)
    (hG : ∀ f g, 𝒮.cubeGreen E Q (f + g) = 𝒮.cubeGreen E Q f + 𝒮.cubeGreen E Q g)
    (f g : LatticeSite d S 𝒮.ξ → ℝ) :
    𝒮.sandwichedGreen E Q (f + g) = 𝒮.sandwichedGreen E Q f + 𝒮.sandwichedGreen E Q g := by
  simp only [BlockSetting.sandwichedGreen]
  rw [pointwiseMul_add, hG, pointwiseMul_add]
end Cubes
end Dirichlet.NeumannWalks
end YangMills.Construction
