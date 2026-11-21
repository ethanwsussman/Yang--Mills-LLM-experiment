import YangMills.Construction.LawByMomentsOfTheFlow.ColoursOfForms
import YangMills.Construction.ResponseInTheExpansion.TheCurvatureIsAGaussianChainProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.MomentLaw
open BlockAverages WeightedResponses ResponseInTheExpansion
private theorem imaginaryComponent_add (e : Fin 3) (u w : imaginaryQuaternions) :
    imaginaryComponent e (u + w) = imaginaryComponent e u + imaginaryComponent e w := by
  fin_cases e <;> simp [imaginaryComponent]
private theorem imaginaryComponent_sub (e : Fin 3) (u w : imaginaryQuaternions) :
    imaginaryComponent e (u - w) = imaginaryComponent e u - imaginaryComponent e w := by
  fin_cases e <;> simp [imaginaryComponent]
private theorem imaginaryComponent_smul (e : Fin 3) (r : ℝ) (w : imaginaryQuaternions) :
    imaginaryComponent e (r • w) = r * imaginaryComponent e w := by
  fin_cases e <;> simp [imaginaryComponent]
private theorem imaginaryComponent_sum {ι : Type} (e : Fin 3) (s : Finset ι) (f : ι → imaginaryQuaternions) :
    imaginaryComponent e (∑ i ∈ s, f i) = ∑ i ∈ s, imaginaryComponent e (f i) := by apply _root_.YangMills.SharedProofs.p4562 <;> assumption
private theorem sum_imaginaryComponent_sq (w : imaginaryQuaternions) :
    ∑ e : Fin 3, imaginaryComponent e w ^ 2 = ‖w‖ ^ 2 := by
  have hre : (w : ℍ[ℝ]).re = 0 := w.2
  have hnorm : ‖w‖ ^ 2 = (w : ℍ[ℝ]).re ^ 2 + (w : ℍ[ℝ]).imI ^ 2 + (w : ℍ[ℝ]).imJ ^ 2 + (w : ℍ[ℝ]).imK ^ 2 := by
    have hcoe : ‖w‖ = ‖(w : ℍ[ℝ])‖ := rfl
    rw [hcoe, sq, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
  rw [hnorm, hre, Fin.sum_univ_three]
  simp [imaginaryComponent]
theorem colourFormIdentities_holds : colourFormIdentitiesStatement := by
  refine ⟨fun m F p => ?_, fun L _ n _ a ρA u A => ?_, fun m F G => ?_, fun m F G => ?_⟩
  · have hcomp : ∀ e : Fin 3, WeightedResponses.curl (toColourForm F e) p = imaginaryComponent e (lieFormCurl F p) := by
      intro e
      simp only [WeightedResponses.curl, toColourForm, lieFormCurl, imaginaryComponent_add, imaginaryComponent_sub]
    unfold curlNorm
    simp only [hcomp]
    rw [sum_imaginaryComponent_sq, Real.sqrt_sq (norm_nonneg _)]
  · funext e b
    simp only [pushColours, WeightedResponses.responseMap, toColourForm, responseOfLieForm, imaginaryComponent_sum,
      imaginaryComponent_smul]
  · funext e b
    simp only [toColourForm, imaginaryComponent_add]
  · funext e b
    simp only [toColourForm, imaginaryComponent_sub]
end YangMills.Construction.MomentLaw
end
