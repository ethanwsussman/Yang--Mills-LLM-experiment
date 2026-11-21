import YangMills.Construction.Matrices.ComplexifiedAlgebraExp
import YangMills.Construction.Matrices.RepresentationsFieldsAndSmoothFunctionsOnG
import Mathlib
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace YangMills.Construction.Matrices.ComplexifiedAlgebra
private def entryCLM (i j : Fin 2) : ComplexMatrix2 →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)
private theorem det_matExp_of_fullTrace_zero (Z : ComplexMatrix2)
    (hZ : ComplexMatrix2.fullTrace Z = 0) : (ComplexMatrix2.matExp Z).det = 1 := by apply _root_.YangMills.Construction.SpinHarmonics.det_matExp_of_trace_eq_zero <;> assumption
private theorem exists_hermitian_split (A : ComplexMatrix2)
    (hA : ComplexMatrix2.fullTrace A = 0) :
    ∃ X ∈ ComplexMatrix2.hermitianTraceless, ∃ Y ∈ ComplexMatrix2.hermitianTraceless,
      A = X + Complex.I • Y := by
  have hs : ComplexMatrix2.fullTrace A.conjTranspose = 0 := by
    rw [ComplexMatrix2.fullTrace, Matrix.trace_conjTranspose]
    simp only [ComplexMatrix2.fullTrace] at hA
    simp [hA]
  have hA' : Matrix.trace A = 0 := hA
  have hs' : Matrix.trace A.conjTranspose = 0 := hs
  refine ⟨(1 / 2 : ℂ) • (A + A.conjTranspose), ⟨?_, ?_⟩,
    (-Complex.I / 2 : ℂ) • (A - A.conjTranspose), ⟨?_, ?_⟩, ?_⟩
  · ext i j
    simp [Matrix.conjTranspose_apply, add_comm]
    ring
  · simp [ComplexMatrix2.fullTrace, Matrix.trace_smul, Matrix.trace_add, hA', hs']
  · ext i j
    have h₂ : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ 2
    simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul,
      star_mul', star_sub, Complex.star_def, map_div₀, map_neg, Complex.conj_I]
    simp [h₂]
    ring
  · simp [ComplexMatrix2.fullTrace, Matrix.trace_smul, Matrix.trace_sub, hA', hs']
  · ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination ((A i j - A.conjTranspose i j) / 2) * hI
private theorem fullTrace_add_I_smul (X Y : ComplexMatrix2)
    (hX : X ∈ ComplexMatrix2.hermitianTraceless) (hY : Y ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.fullTrace (X + Complex.I • Y) = 0 := by
  have h₁ : Matrix.trace X = 0 := hX.2
  have h₂ : Matrix.trace Y = 0 := hY.2
  simp [ComplexMatrix2.fullTrace, Matrix.trace_add, Matrix.trace_smul, h₁, h₂]
theorem complexifiedAlgebra_exp_properties : ComplexifiedAlgebraExponential := by
  refine ⟨⟨?_, rfl⟩, ?_, ?_⟩
  · ext A
    constructor
    · exact fun hA => exists_hermitian_split A hA
    · rintro ⟨X, hX, Y, hY, rfl⟩
      exact fullTrace_add_I_smul X Y hX hY
  · intro Y hY
    exact det_matExp_of_fullTrace_zero _ (ComplexMatrix2.traceless.smul_mem Complex.I hY)
  · intro i j Y _
    refine ⟨fun Z => ComplexMatrix2.matExp (Complex.I • Z) i j, ?_,
      Filter.Eventually.of_forall fun _ => rfl⟩
    have h₁ : AnalyticAt ℂ (fun Z : ComplexMatrix2 => Complex.I • Z) Y :=
      (Complex.I • ContinuousLinearMap.id ℂ ComplexMatrix2).analyticAt Y
    exact (entryCLM i j).analyticAt _ |>.comp (NormedSpace.exp_analytic (𝕂 := ℂ) _ |>.comp h₁)
end YangMills.Construction.Matrices.ComplexifiedAlgebra
