import YangMills.Construction.LatticeFields.BlockAveragingProof
import YangMills.Construction.LatticeFields.PointwiseBoundsOfDecay
import YangMills.Construction.LatticeFields.TransverseDecompositionProof
import YangMills.Construction.LatticeFields.WeightConjugationEstimates
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.LatticeFields.MetricAdjointCubes
variable {d : ℕ}
theorem latticeSpacing_pos (N : ℕ) [NeZero N] : 0 < latticeSpacing N := by apply _root_.YangMills.Construction.LatticeFields.PointwiseOfDecay.latticeSpacing_pos <;> assumption
theorem latticeSpacing_mul_cast (N : ℕ) [NeZero N] : latticeSpacing N * (N : ℝ) = 1 := by apply _root_.YangMills.Construction.LatticeFields.BlockAveraging.latticeSpacing_mul_cast <;> assumption
section Metric
variable {N : ℕ} {κ : LatticeShape d}
theorem siteDist_le_sum_abs (x x' : LatticeSite N κ) (v : scaledIntLattice d N)
    (hv : toSite N κ v = x - x') :
    siteDist x x' ≤ ∑ μ, |(v : Fin d → ℝ) μ| := by
  refine csInf_le ⟨0, ?_⟩ ⟨v, hv, rfl⟩
  rintro t ⟨u, -, rfl⟩
  exact Finset.sum_nonneg fun μ _ => abs_nonneg _
end Metric
section Operators
variable {N : ℕ} {κ : LatticeShape d} {I : Type}
theorem summable_mul_of_summable_sq {ι : Type} {u v : ι → ℝ} (hu : Summable fun i => u i ^ 2)
    (hv : Summable fun i => v i ^ 2) : Summable fun i => u i * v i := by apply _root_.YangMills.SharedProofs.p5943 <;> assumption
theorem summable_const_mul_field_mul (c : ℝ) {F G : LatticeField N κ I}
    (hF : FieldSquareSummable F) (hG : FieldSquareSummable G) :
    Summable fun p : LatticeSite N κ × I => c * F p.1 p.2 * G p.1 p.2 := by
  refine ((summable_mul_of_summable_sq hF hG).mul_left c).congr fun p => ?_
  ring
theorem fieldInner_comm (F G : LatticeField N κ I) : fieldInner F G = fieldInner G F :=
  tsum_congr fun p => by ring
theorem fieldInner_sub_left {F F' G : LatticeField N κ I} (hF : FieldSquareSummable F)
    (hF' : FieldSquareSummable F') (hG : FieldSquareSummable G) :
    fieldInner (F - F') G = fieldInner F G - fieldInner F' G := by
  unfold fieldInner
  rw [← (summable_const_mul_field_mul _ hF hG).tsum_sub (summable_const_mul_field_mul _ hF' hG)]
  refine tsum_congr fun p => ?_
  show latticeSpacing N ^ d * (F p.1 p.2 - F' p.1 p.2) * G p.1 p.2 = _
  ring
theorem fieldInner_smul_left (e : ℝ) (F G : LatticeField N κ I) :
    fieldInner (e • F) G = e * fieldInner F G := by apply _root_.YangMills.Construction.LatticeFields.Transverse.fieldInner_smul_left <;> assumption
theorem latticeGrad_eq_tensorGrad :
    (latticeGrad : ScalarField N κ → LatticeOneForm N κ) =
      (tensorGrad : LatticeTensor N κ 0 → LatticeTensor N κ 1) := by apply _root_.YangMills.Construction.LatticeFields.WeightConjugation.latticeGrad_eq_tensorGrad <;> assumption
theorem latticeDiv_eq_tensorGradAdjoint :
    (latticeDiv : LatticeOneForm N κ → ScalarField N κ) =
      (tensorGradAdjoint : LatticeTensor N κ 1 → LatticeTensor N κ 0) := by apply _root_.YangMills.Construction.LatticeFields.WeightConjugation.latticeDiv_eq_tensorGradAdjoint <;> assumption
end Operators
section Cubes
variable {N : ℕ} [NeZero N] {κ : LatticeShape d}
end Cubes
end YangMills.Construction.LatticeFields.MetricAdjointCubes
