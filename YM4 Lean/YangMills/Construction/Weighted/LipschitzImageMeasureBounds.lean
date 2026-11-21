import YangMills.Construction.Torus.BoundsOnTheWeightedDistanceProof
import Mathlib
set_option autoImplicit false
open Set MeasureTheory YangMills.Construction.TorusMetric
open scoped ENNReal NNReal
noncomputable section
namespace YangMills.Construction.Weighted.ImageMeasure
variable {S : ℝ}
theorem measurableEmbedding_ofLp_torus :
    MeasurableEmbedding (WithLp.ofLp : TorusL1 S → Torus4 S) :=
  (PiLp.homeomorph 1 fun _ : Fin 4 => AddCircle S).toMeasurableEquiv.measurableEmbedding
theorem l1LengthMeasure_apply [Fact (0 < S)] (A : Set (Torus4 S)) :
    l1LengthMeasure S A = (μH[1] : Measure (TorusL1 S)) (WithLp.ofLp ⁻¹' A) :=
  measurableEmbedding_ofLp_torus.map_apply _ _
theorem l1NormVec_nonneg (a : Fin 4 → ℝ) : 0 ≤ l1NormVec a :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _
theorem l1NormVec_smul (u : ℝ) (a : Fin 4 → ℝ) : l1NormVec (u • a) = |u| * l1NormVec a := by
  simp [l1NormVec, abs_mul, Finset.mul_sum]
theorem torusL1Norm_torusProj_le (a : Fin 4 → ℝ) : torusL1Norm (torusProj S a) ≤ l1NormVec a := by apply _root_.YangMills.Construction.Weighted.DistBounds.torusL1Norm_torusProj_le <;> assumption
theorem pointAt_sub_pointAt (s : LiftedSegment) (u u' : ℝ) :
    s.pointAt S u - s.pointAt S u' = torusProj S ((u - u') • s.displacement) := by apply _root_.YangMills.Construction.Weighted.DistBounds.pointAt_sub_pointAt <;> assumption
theorem segmentsSupport_cons (s : LiftedSegment) (Γ : List LiftedSegment) :
    segmentsSupport S (s :: Γ) = s.support S ∪ segmentsSupport S Γ := by
  simp [segmentsSupport]
theorem pathLengthIn_nonneg (Γ : List LiftedSegment) (A : Set (Torus4 S)) :
    0 ≤ pathLengthIn S Γ A := by apply _root_.YangMills.Construction.Weighted.DistBounds.pathLengthIn_nonneg <;> assumption
theorem ofReal_pathLengthIn_cons (s : LiftedSegment) (Γ : List LiftedSegment)
    (A : Set (Torus4 S)) :
    ENNReal.ofReal (l1NormVec s.displacement) * volume (Icc (0 : ℝ) 1 ∩ s.pointAt S ⁻¹' A) +
        ENNReal.ofReal (pathLengthIn S Γ A) =
      ENNReal.ofReal (pathLengthIn S (s :: Γ) A) := by
  have hfin : volume (Icc (0 : ℝ) 1 ∩ s.pointAt S ⁻¹' A) ≠ ⊤ :=
    ((measure_mono inter_subset_left).trans_lt (by simp)).ne
  have hcons : pathLengthIn S (s :: Γ) A =
      l1NormVec s.displacement * (volume (Icc (0 : ℝ) 1 ∩ s.pointAt S ⁻¹' A)).toReal +
        pathLengthIn S Γ A := by
    simp [pathLengthIn]
  rw [hcons, ENNReal.ofReal_add
    (mul_nonneg (l1NormVec_nonneg _) ENNReal.toReal_nonneg) (pathLengthIn_nonneg _ _),
    ENNReal.ofReal_mul (l1NormVec_nonneg _), ENNReal.ofReal_toReal hfin]
end YangMills.Construction.Weighted.ImageMeasure
end
