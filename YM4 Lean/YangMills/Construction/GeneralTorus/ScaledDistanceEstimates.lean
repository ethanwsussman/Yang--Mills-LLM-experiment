import YangMills.Construction.Geometry.ToriGeneralSide
import YangMills.Construction.SeparatedSequences.PointsOfACubeAreNearItsTopProof
import YangMills.Construction.Torus.AveragesOfTheExpansionTestFormsProof
import YangMills.Construction.Torus.WeightedLengthsAndLocalLipschitzNumbersProof
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction
open TorusMetric
namespace GeneralTorus.ScaledDistanceUpper
theorem levelSpacing_pos (D : ScaleData) (n : ℕ) : 0 < D.levelSpacing n := by apply _root_.YangMills.Construction.GeneralTorus.ChainStructureProof.levelSpacing_pos <;> assumption
variable {D : ScaleData}
theorem norm_apply_le_torusSupNorm {S : ℝ} (x : Torus4 S) (μ : Fin 4) :
    ‖x μ‖ ≤ torusSupNorm x := by apply _root_.YangMills.Construction.SequenceGeometryProof.norm_apply_le_torusSupNorm <;> assumption
theorem torusSupNorm_le {S c : ℝ} (x : Torus4 S) (h : ∀ μ, ‖x μ‖ ≤ c) : torusSupNorm x ≤ c := by
  choose b hb hb' using fun ν => exists_coe_eq_abs_eq_norm (x ν)
  have hbdd : BddBelow (supNormVec '' (torusProj S ⁻¹' {x})) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨v, -, rfl⟩
    exact (abs_nonneg (v 0)).trans (Finset.le_sup' (fun ν => |v ν|) (Finset.mem_univ 0))
  refine (csInf_le hbdd ⟨b, funext hb, rfl⟩).trans ?_
  refine Finset.sup'_le _ _ fun μ _ => ?_
  rw [hb' μ]
  exact h μ
theorem continuous_pointAt (S : ℝ) (s : LiftedSegment) : Continuous (s.pointAt S) := by apply _root_.YangMills.Construction.Weighted.WeightedLengthProof.continuous_pointAt <;> assumption
end GeneralTorus.ScaledDistanceUpper
end YangMills.Construction
end
