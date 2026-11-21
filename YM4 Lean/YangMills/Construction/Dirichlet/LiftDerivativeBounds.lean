import YangMills.Construction.Dirichlet.CoverCubeCount
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped ContDiff Topology
open YangMills.Construction.Torus YangMills.Construction.Dirichlet
open YangMills.Construction.Dirichlet.CoverCount
noncomputable section
namespace YangMills.Construction.Dirichlet.LiftDerivatives
variable {d L : ℕ} {S aMinus aPlus : ℝ} (𝒮 : BlockSetting d L aMinus aPlus S)
def liftedPartition (Q : CentredCube d S) : (Fin d → ℝ) → ℝ :=
  fun v => 𝒮.partitionOfUnity Q (torusProj d S v)
structure LiftDerivBounds (c : ℝ) (n : ℕ) (Q : CentredCube d S) (v : Fin d → ℝ) : Prop where
  contDiffAt : ContDiffAt ℝ ∞ (liftedPartition 𝒮 Q) v
  norm_fderiv_le :
    ‖fderiv ℝ (liftedPartition 𝒮 Q) v‖ ≤ c * (L : ℝ) / 𝒮.blockWidth n
  norm_fderiv_fderiv_le :
    ‖fderiv ℝ (fderiv ℝ (liftedPartition 𝒮 Q)) v‖ ≤
      c * (L : ℝ) ^ 2 / 𝒮.blockWidth n ^ 2
end YangMills.Construction.Dirichlet.LiftDerivatives
