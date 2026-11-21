import YangMills.Construction.Torus.DistanceAveragesWholePairMatricesAndNormsProof
import YangMills.Construction.Torus.KernelThroughScaledMatrices
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Weighted.ScaledKernel
variable {D : TorusData} (B : SeparatedChain D)
theorem siteScale_pos (y : D.Space) : 0 < B.siteScale y := by apply _root_.YangMills.Construction.Weighted.AvgMatrix.siteScale_pos <;> assumption
theorem scaleSqOnLayer_eq_mulOp :
    B.scaleSqOnLayer = B.mulOp fun y => B.siteScale y ^ 2 := by
  refine LinearMap.ext fun w => funext fun y => ?_
  change B.siteScale y * (B.siteScale y * w y) = B.siteScale y ^ 2 * w y
  ring
theorem inverse_scaleOnLayer_eq_mulOp :
    Ring.inverse (B.scaleOnLayer : Module.End ℝ B.LayerFn) =
      B.mulOp fun y => (B.siteScale y)⁻¹ := by apply _root_.YangMills.Construction.Weighted.DistanceAvgPairMatrixNormProof.inverse_scaleOnLayer <;> assumption
theorem inverseScaleSqOnLayer_eq_mulOp :
    B.inverseScaleSqOnLayer = B.mulOp fun y => (B.siteScale y ^ 2)⁻¹ := by
  unfold SeparatedChain.inverseScaleSqOnLayer
  rw [inverse_scaleOnLayer_eq_mulOp]
  refine LinearMap.ext fun w => funext fun y => ?_
  change (B.siteScale y)⁻¹ * ((B.siteScale y)⁻¹ * w y) = (B.siteScale y ^ 2)⁻¹ * w y
  rw [sq, mul_inv, mul_assoc]
theorem kernelViaScaledMatricesClaim_of (h : DistanceAvgPairMatrixNormFacts) :
    KernelViaScaledMatricesClaim := by
  intro G K y y'
  obtain ⟨-, -, -, -, -, -, -, hM, -⟩ := h G.data G.chain G.stage_zero_nonempty
  obtain ⟨-, -, -, hk, -, hm, -⟩ := hM
  have ha := (siteScale_pos G.chain y).ne'
  have hb := (siteScale_pos G.chain y').ne'
  have e₁ := hm K (fun y => (G.chain.siteScale y ^ 2)⁻¹)
    (fun y => (G.chain.siteScale y ^ 2)⁻¹) y y'
  have e₂ := hm K (fun y => G.chain.siteScale y ^ 2)
    (fun y => G.chain.siteScale y ^ 2) y y'
  have e₃ := hm K (fun y => (G.chain.siteScale y ^ 2)⁻¹)
    (fun y => G.chain.siteScale y ^ 2) y y'
  rw [← inverseScaleSqOnLayer_eq_mulOp, hk K y y'] at e₁
  rw [← scaleSqOnLayer_eq_mulOp, hk K y y'] at e₂
  rw [← inverseScaleSqOnLayer_eq_mulOp, ← scaleSqOnLayer_eq_mulOp, hk K y y'] at e₃
  unfold SeparatedChain.KernelViaScaledMatrices
  rw [e₁, e₂, e₃]
  simp only [zpow_neg, zpow_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> field_simp
end YangMills.Construction.Weighted.ScaledKernel
