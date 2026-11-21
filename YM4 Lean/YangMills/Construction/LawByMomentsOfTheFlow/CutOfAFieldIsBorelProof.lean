import YangMills.Construction.LawByMomentsOfTheFlow.CutOfAFieldIsBorel
import YangMills.Construction.ResponseInTheExpansion.TheCurvatureIsAGaussianChainProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Quaternion
namespace YangMills.Construction.MomentLaw
open TorusFields TorusLumps ResponseInTheExpansion BlockAverages ColdStepAtMirrorFrames
private theorem measurable_pathHolonomy {Ξ : Type} [MeasurableSpace Ξ] {F : BlockFrame} {j : ℕ}
    (X : Ξ → F.GaugeField j) (hX : ∀ x i, Measurable fun a => X a x i) (x : F.Site j) (l : List PathStep) :
    Measurable fun a => BlockAverages.pathHolonomy (X a) x l := by apply _root_.YangMills.SharedProofs.p6492 <;> assumption
private theorem measurable_axialGaugeAt (ℓ : TorusLumps.StepParameters) {n : ℕ} (o z : TorusSite n) :
    Measurable fun W : TorusField n => axialGaugeAt ℓ W o z := by
  unfold axialGaugeAt axialGaugeHolonomy
  refine measurable_pathHolonomy _ (fun x i => ?_) _ _
  exact (measurable_pi_apply i).comp (measurable_pi_apply _)
theorem cutoffMeasurable_holds (hChain : chainMeasurabilityStatement) : cutoffMeasurableStatement := by
  intro ℓ n _ o
  refine ⟨fun m b e => ?_, fun r => ?_⟩
  · obtain ⟨-, hI, hJ, hK⟩ := hChain.2.1
    have hgauge : Measurable fun W : TorusField n => gaugeTransform (axialGaugeAt ℓ W o) W b := by
      unfold ResponseInTheExpansion.gaugeTransform
      exact ((measurable_axialGaugeAt ℓ o _).mul ((measurable_pi_apply _).comp (measurable_pi_apply _))).mul
        (measurable_axialGaugeAt ℓ o _).inv
    have haxial : Measurable fun W : TorusField n => imaginaryComponent e (axialCoords ℓ W o b) := by
      unfold axialCoords
      fin_cases e
      · exact hI.comp hgauge
      · exact hJ.comp hgauge
      · exact hK.comp hgauge
    have hcut : (fun W : TorusField n => imaginaryComponent e (cutoffCoords ℓ W o m b)) =
        fun W => cutoffProfile o m b.1 * imaginaryComponent e (axialCoords ℓ W o b) := by
      funext W
      unfold cutoffCoords
      fin_cases e <;> simp [imaginaryComponent]
    rw [hcut]
    exact haxial.const_mul _
  · unfold MomentLaw.boxCurvature
    refine Measurable.iSup fun p => ?_
    have hplaq : Measurable fun W : TorusField n => TorusFields.holonomy W p.1.1 p.1.2.1 p.1.2.2 := by
      unfold TorusFields.holonomy
      have hev : ∀ (z : TorusSite n) (j : Fin 4), Measurable fun W : TorusField n => W z j := fun z j =>
        (measurable_pi_apply j).comp (measurable_pi_apply z)
      exact (((hev _ _).mul (hev _ _)).mul (hev _ _).inv).mul (hev _ _).inv
    have hcont : Continuous fun g : UnitQuaternion => ‖(g : ℍ[ℝ]) - 1‖ :=
      (continuous_subtype_val.sub continuous_const).norm
    exact hcont.measurable.comp hplaq
end YangMills.Construction.MomentLaw
end
