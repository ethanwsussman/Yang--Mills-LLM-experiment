import YangMills.Construction.ColdStepAtMirrorFrames.GaugeOfTheLeastChartProof
import YangMills.Construction.ColdStepAtMirrorFrames.LogarithmOfAMovedExponentialProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
namespace ReflectedTop
theorem expUnit_adjointMap (g : UnitQuaternion) (v : imaginaryQuaternions) :
    expUnit (adjointMap g v) = g * expUnit v * g⁻¹ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.MinimalChart.expUnit_adjointMap <;> assumption
theorem expUnit_neg (v : imaginaryQuaternions) : expUnit (-v) = (expUnit v)⁻¹ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.expUnit_neg <;> assumption
end ReflectedTop
open ReflectedTop in
theorem reflectedFieldOfTranslatedTop_proof : ReflectedFieldOfTranslatedTop := by
  classical
  intro F m y V k c X τ _
  funext z i
  by_cases hf : IsForwardOriented m z i
  · have hf' : reflectCoord m ((z i).valMinAbs + (Pi.single i 1 : Fin 4 → ℤ) i) =
        reflectCoord m (z i).valMinAbs + 1 := by simpa [IsForwardOriented] using hf
    have hsrc : sourceBond m y z i = (y + siteOfCoords F.top fun l => reflectCoord m (z l).valMinAbs, i) := by
      simp only [sourceBond, if_pos hf]
    simp only [reflectedField, leftTranslate]
    rw [if_pos hf', if_pos hf']
    congr 2
    simp only [bondSpread, reflectedDirection, hsrc, if_pos hf]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hc : c l = (y + siteOfCoords F.top fun l => reflectCoord m (z l).valMinAbs, i)
    · rw [if_pos hc, if_pos hc.symm]
    · rw [if_neg hc, if_neg (Ne.symm hc), smul_zero]
  · have hf' : ¬ reflectCoord m ((z i).valMinAbs + (Pi.single i 1 : Fin 4 → ℤ) i) =
        reflectCoord m (z i).valMinAbs + 1 := by simpa [IsForwardOriented] using hf
    set p : F.Cell := y + siteOfCoords F.top fun l =>
      reflectCoord m ((z l).valMinAbs + (Pi.single i 1 : Fin 4 → ℤ) l) with hp
    have hsrc : sourceBond m y z i = (p, i) := by
      simp only [sourceBond, if_neg hf, hp]
    simp only [reflectedField, leftTranslate]
    rw [if_neg hf', if_neg hf']
    rw [← hp]
    have hsum : (∑ l, τ l • reflectedDirection m y V (c l) (X l) z i) =
        - adjointMap (V p i)⁻¹ (bondSpread c X τ p i) := by
      simp only [bondSpread, map_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [reflectedDirection, hsrc, if_neg hf]
      by_cases hc : c l = (p, i)
      · rw [if_pos hc, if_pos hc.symm, hc]
        simp
      · rw [if_neg hc, if_neg (Ne.symm hc)]
        simp
    rw [hsum, expUnit_neg, expUnit_adjointMap]
    group
end ColdStepAtMirrorFrames
end YangMills.Construction
end
