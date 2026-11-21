import YangMills.Construction.ColdStepAtMirrorFrames.LeastActionIsGaugeInvariant
import YangMills.Construction.HoleBesideASecondHole.EnergyInTheChart
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
private theorem re_conj_mul_inv (g : UnitQuaternion) (q : Quaternion ℝ) :
    ((g : Quaternion ℝ) * q * ((g⁻¹ : UnitQuaternion) : Quaternion ℝ)).re = q.re := by apply _root_.YangMills.Construction.GaugedCriticality.re_conj_unit <;> assumption
private theorem gaugeTransform_gaugeTransform_inv {j : ℕ} (γ : F.Site j → UnitQuaternion)
    (U : F.GaugeField j) :
    gaugeTransform γ (gaugeTransform (fun x => (γ x)⁻¹) U) = U := by apply _root_.YangMills.Construction.GaugeFixing.gaugeTransform_gaugeTransform_inv <;> assumption
theorem minimalActionGaugeInvariant (hcov : gaugeCovarianceStatement) :
    MinimalActionGaugeInvariant := by
  intro F a S k
  induction k with
  | zero =>
    intro _ hL γ U
    show wilsonAction S (gaugeTransform γ U) = wilsonAction S U
    unfold wilsonAction
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨_, _, hplaq, _⟩ := hcov F 0 (by simp [BlockFrame.top]) hL
    rw [hplaq γ U p]
    congr 1
    exact re_conj_mul_inv (γ p.1) _
  | succ k ih =>
    intro hk hL γ V
    obtain ⟨hinj, _, _, hfit⟩ := hcov F k (by omega) hL
    let γ' : F.Site k → UnitQuaternion := Function.extend (refineSite (F := F) (j := k)) γ 1
    have hγ' : ∀ y, γ' (refineSite y) = γ y := fun y => hinj.extend_apply _ _ _
    show (⨅ U : F.GaugeField k, (minimalAction a S k U + a * ∑ c ∈ innerBonds S (k + 1), blockFit U (gaugeTransform γ V) c)) =
      ⨅ U : F.GaugeField k, (minimalAction a S k U + a * ∑ c ∈ innerBonds S (k + 1), blockFit U V c)
    have hsurj : Function.Surjective (gaugeTransform (F := F) γ') :=
      fun U => ⟨_, gaugeTransform_gaugeTransform_inv γ' U⟩
    rw [← hsurj.iInf_comp]
    refine iInf_congr fun U => ?_
    rw [ih (by omega) hL γ' U]
    congr 2
    refine Finset.sum_congr rfl fun c _ => ?_
    exact hfit γ' γ U V c (hγ' _) (hγ' _)
end YangMills.Construction.ColdStepAtMirrorFrames
end
