import YangMills.Construction.Dirichlet.BlockGreenLinearProof
import YangMills.Construction.Dirichlet.CommutatorBoundsProof
import YangMills.Construction.DirichletOperator.ChainOfRemaindersProof
import YangMills.Construction.DirichletOperator.NeumannSeriesOfTheRemainderProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Torus WeightedGreen
namespace Dirichlet.RemainderNormProof
open WalkExpansion
variable {d L : ℕ} {S aMinus aPlus : ℝ}
section Functions
variable {ξ : ℝ}
theorem restrictTo_add (X : Set (PeriodicTorus d S)) (f g : LatticeSite d S ξ → ℝ) :
    restrictTo X (f + g) = restrictTo X f + restrictTo X g := by apply _root_.YangMills.Construction.Dirichlet.GreenLinearityProof.restrictTo_add <;> assumption
theorem pointwiseMul_add (h f g : LatticeSite d S ξ → ℝ) :
    pointwiseMul h (f + g) = pointwiseMul h f + pointwiseMul h g := by apply _root_.YangMills.Construction.Dirichlet.RemainderNeumann.pointwiseMul_add <;> assumption
theorem pointwiseMul_smul (h : LatticeSite d S ξ → ℝ) (r : ℝ)
    (f : LatticeSite d S ξ → ℝ) : pointwiseMul h (r • f) = r • pointwiseMul h f := by apply _root_.YangMills.Construction.Dirichlet.RemainderNeumann.pointwiseMul_smul <;> assumption
theorem supNormAll_nonneg (f : LatticeSite d S ξ → ℝ) : 0 ≤ supNormAll f := by apply _root_.YangMills.Construction.Dirichlet.CubeEstimates.zero_le_supNormAll <;> assumption
theorem abs_le_supNormAll [Finite (LatticeSite d S ξ)]
    (f : LatticeSite d S ξ → ℝ) (x : LatticeSite d S ξ) :
    |f x| ≤ supNormAll f := by apply _root_.YangMills.Construction.Dirichlet.CubeEstimates.abs_le_supNormAll <;> assumption
end Functions
variable (𝒮 : BlockSetting d L aMinus aPlus S)
variable (E : CentredCube d S → Set (LatticeBond d S 𝒮.ξ))
variable {𝒮 E}
end Dirichlet.RemainderNormProof
end YangMills.Construction
