import YangMills.Construction.Lattice.CovarianceOfComplexPlaquetteVariablesProof
import YangMills.Construction.Towers.DerivativesOfAPlaquetteTermProof
import YangMills.Construction.Towers.GaugeConditionsOfTheAlgebraOfTheLeftChartOnASideProof
import YangMills.Construction.Towers.MatrixFactsOfTheAlgebraOfTheLeftChart
import Mathlib
set_option autoImplicit false
open Matrix
noncomputable section
namespace YangMills.Construction.Tower.LeftChartAlgebra.MatrixIdentities
open Matrices (ComplexMatrix2)
theorem inv_eq_of_det_eq_one (g : ComplexMatrix2) (h : g.det = 1) :
    g⁻¹ = ComplexMatrix2.fullTrace g • (1 : ComplexMatrix2) - g := by apply _root_.YangMills.Construction.Tower.FaceTermDerivatives.inv_eq_trace_smul_one_sub <;> assumption
theorem fullTrace_inv_of_det_eq_one (g : ComplexMatrix2) (h : g.det = 1) :
    ComplexMatrix2.fullTrace g⁻¹ = ComplexMatrix2.fullTrace g := by apply _root_.YangMills.Construction.PeriodicLattice.PlaquetteCovariance.fullTrace_inv <;> assumption
theorem inv_eq_star_of_mem {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    g⁻¹ = star g := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.inv_eq_star_of_mem <;> assumption
theorem invTraceIdentity_holds : InvTraceIdentity := by
  refine ⟨fun g hg => ⟨inv_eq_of_det_eq_one g hg, fullTrace_inv_of_det_eq_one g hg⟩,
    fun g hg => ?_⟩
  have htr := fullTrace_inv_of_det_eq_one g (Matrix.mem_specialUnitaryGroup_iff.mp hg).2
  rw [inv_eq_star_of_mem hg, Matrix.star_eq_conjTranspose, ComplexMatrix2.fullTrace,
    ComplexMatrix2.fullTrace, Matrix.trace_conjTranspose] at htr
  exact Complex.conj_eq_iff_im.mp htr
theorem halfTraceInPauliCoords_holds : HalfTraceInPauliCoords := by
  intro X Y x y hX hY
  rw [halfTraceProduct, hX, hY, ComplexMatrix2.sum_smul_pauliFamily,
    ComplexMatrix2.sum_smul_pauliFamily]
  simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three, ComplexMatrix2.adjointMatrix,
    Matrix.conjTranspose_apply]
  simp [star_add, star_sub, star_mul']
  linear_combination (-((starRingEnd ℂ) (x 1) * y 1)) * Complex.I_sq
theorem norm_halfTraceProduct_le (X Y : ComplexMatrix2) :
    ‖halfTraceProduct X Y‖ ≤ (halfTraceProduct X X).re + (halfTraceProduct Y Y).re := by apply _root_.YangMills.Construction.Tower.LeftChartAlgebra.GaugeRequirements.norm_halfTraceProduct_le <;> assumption
theorem hermitianSeriesAbsConv_holds (ι : Type) : HermitianSeriesAbsConv ι := fun f g hf hg =>
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => norm_halfTraceProduct_le (f i) (g i))
    (hf.2.add hg.2)
theorem halfTraceProduct_conjugateBy {g : ComplexMatrix2}
    (hg : g ∈ PeriodicLattice.compactGaugeGroup) (X Y : ComplexMatrix2) :
    halfTraceProduct (ComplexMatrix2.conjugateBy g X) (ComplexMatrix2.conjugateBy g Y) =
      halfTraceProduct X Y := by
  have hu : star g * g = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (Matrix.mem_specialUnitaryGroup_iff.mp hg).1
  have hprod : (g * X * star g)ᴴ * (g * Y * star g) = g * (Xᴴ * Y) * star g := by
    rw [Matrix.star_eq_conjTranspose] at hu ⊢
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc gᴴ g, hu, Matrix.one_mul]
  simp only [halfTraceProduct, ComplexMatrix2.conjugateBy, inv_eq_star_of_mem hg,
    ComplexMatrix2.adjointMatrix, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace]
  rw [hprod, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hu, Matrix.one_mul]
theorem matrixIdentities_holds : MatrixIdentities.Statement :=
  ⟨invTraceIdentity_holds, halfTraceInPauliCoords_holds, hermitianSeriesAbsConv_holds,
    fun _ hg X _ Y _ => halfTraceProduct_conjugateBy hg X Y⟩
end YangMills.Construction.Tower.LeftChartAlgebra.MatrixIdentities
end
