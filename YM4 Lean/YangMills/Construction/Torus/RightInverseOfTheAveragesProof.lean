import YangMills.Construction.Torus.BoundsOnTheCompressedOperatorsProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.GeneralTorus.MeanOpRightInverse
open Finset
theorem finite_coarseBond (W : GaugeSetting) : Finite W.CoarseBond := by apply _root_.YangMills.Construction.GeneralTorus.InnerProductsAdjointsProjections.finite_coarseBond <;> assumption
theorem coarseSpacing_pos {W : GaugeSetting} (c : W.CoarseBond) :
    0 < GaugeSetting.coarseSpacing c := by apply _root_.YangMills.Construction.GeneralTorus.CompressedBoundsProof.coarseSpacing_pos <;> assumption
section Main
variable {W : GaugeSetting} [Fintype W.CoarseBond]
def kernelAction (M : W.CoarseBond → W.CoarseBond → ℝ) : Module.End ℝ W.CoarseField where
  toFun B c' := ∑ c, M c' c * B c
  map_add' B B' := by
    funext c'
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' r B := by
    funext c'
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
end Main
end YangMills.Construction.GeneralTorus.MeanOpRightInverse
