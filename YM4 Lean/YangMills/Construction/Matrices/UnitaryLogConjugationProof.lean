import YangMills.Construction.Matrices.SpecialUnitaryAngleBoundsProof
import YangMills.Construction.Matrices.UnitaryLogarithmClosedFormProof
import Mathlib
open scoped Matrix.Norms.L2Operator
namespace YangMills.Construction.Matrices.ComplexMatrix2
namespace UnitaryLogFacts
private theorem sq_eq_neg_det_smul_of_trace_zero (A : ComplexMatrix2) (h : fullTrace A = 0) :
    A * A = (-A.det) • (1 : ComplexMatrix2) := by apply _root_.YangMills.SharedProofs.p51248 <;> assumption
private theorem neg_det_eq_norm_sq (Y : ComplexMatrix2) (hY : Y ∈ hermitianTraceless) :
    -Y.det = (‖Y‖ : ℂ) ^ 2 := by apply _root_.YangMills.SharedProofs.p28491 <;> assumption
private theorem self_mul_self_eq_norm_sq_smul (Y : ComplexMatrix2) (hY : Y ∈ hermitianTraceless) :
    Y * Y = ((‖Y‖ : ℂ) ^ 2) • (1 : ComplexMatrix2) := by
  have hY' : Y = Y.conjTranspose ∧ fullTrace Y = 0 := hY
  rw [sq_eq_neg_det_smul_of_trace_zero Y hY'.2, neg_det_eq_norm_sq Y hY]
private theorem sinc_mul_eq_sin (θ : ℝ) : Real.sinc θ * θ = Real.sin θ := by apply _root_.YangMills.Construction.PeriodicLattice.ElementaryStepFacts.sinc_mul_self_eq_sin <;> assumption
private theorem sinc_pos_of_lt_pi {θ : ℝ} (h₀ : 0 ≤ θ) (h₁ : θ < Real.pi) : 0 < Real.sinc θ := by apply _root_.YangMills.SharedProofs.p1819 <;> assumption
private theorem matExp_I_smul (Y : ComplexMatrix2) (hY : Y ∈ hermitianTraceless) :
    matExp (Complex.I • Y) =
      (Real.cos ‖Y‖ : ℂ) • (1 : ComplexMatrix2) + (Complex.I * (Real.sinc ‖Y‖ : ℂ)) • Y := by apply _root_.YangMills.SharedProofs.p44010 <;> assumption
private theorem matExp_I_smul_mem (Y : ComplexMatrix2) (hY : Y ∈ hermitianTraceless) :
    matExp (Complex.I • Y) ∈ specialUnitary := by apply _root_.YangMills.Construction.Matrices.ComplexMatrix2.ExpSurjective.matExp_I_smul_mem_specialUnitary <;> assumption
private theorem exists_real_add_I_smul (U : ComplexMatrix2) (hU : U ∈ specialUnitary) :
    ∃ (t : ℝ) (H : ComplexMatrix2), H ∈ hermitianTraceless ∧ halfTrace U = t ∧
      U = (t : ℂ) • (1 : ComplexMatrix2) + Complex.I • H ∧
      U⁻¹ = (t : ℂ) • (1 : ComplexMatrix2) - Complex.I • H ∧
      t ^ 2 + ‖H‖ ^ 2 = 1 := by apply _root_.YangMills.SharedProofs.p99018 <;> assumption
private theorem halfTrace_smul_one_add_smul (c d : ℂ) (A : ComplexMatrix2) (h : fullTrace A = 0) :
    halfTrace (c • (1 : ComplexMatrix2) + d • A) = c := by apply _root_.YangMills.SharedProofs.p42130 <;> assumption
private theorem sincAngle_eq_sinc (a : ℝ) : sincAngle a = Real.sinc a := by apply _root_.YangMills.SharedProofs.p10222 <;> assumption
private theorem existsUnique_unitaryLieLog (W : ComplexMatrix2) (hW : W ∈ unitaryLogDomain) :
    ∃! Y : ComplexMatrix2, Y ∈ hermitianTraceless ∧ ‖Y‖ < Real.pi ∧ matExp (Complex.I • Y) = W := by
  have hne : W ≠ -1 := fun h => hW.2 h
  obtain ⟨t, H, hH, ht, hWe, -, hs⟩ := exists_real_add_I_smul W hW.1
  have hb : |t| ≤ 1 := sq_le_one_iff_abs_le_one t |>.mp (by nlinarith [sq_nonneg ‖H‖])
  obtain ⟨hb₁, hb₂⟩ := abs_le.mp hb
  have htn : ¬ t ≤ -1 := by
    intro h
    have e : t = -1 := le_antisymm h hb₁
    have hH₀ : H = 0 := by
      have e₂ : ‖H‖ ^ 2 = 0 := by
        rw [e] at hs
        linarith
      exact norm_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp e₂)
    apply hne
    rw [hWe, hH₀, e]
    simp
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = Real.arccos t := ⟨_, rfl⟩
  have hcos : Real.cos θ = t := by rw [hθ]; exact Real.cos_arccos hb₁ hb₂
  have h₀ : 0 ≤ θ := by rw [hθ]; exact Real.arccos_nonneg t
  have hπ : θ < Real.pi := by
    rw [hθ]
    exact lt_of_le_of_ne (Real.arccos_le_pi t) fun h => htn (Real.arccos_eq_pi.mp h)
  have hsin : ‖H‖ = Real.sin θ := by
    have h₁ := Real.sin_nonneg_of_nonneg_of_le_pi h₀ hπ.le
    refine (sq_eq_sq₀ (norm_nonneg _) h₁).mp ?_
    have h₂ := Real.sin_sq_add_cos_sq θ
    rw [hcos] at h₂
    linarith
  have hp : 0 < Real.sinc θ := sinc_pos_of_lt_pi h₀ hπ
  have hsc : (Real.sinc θ : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hm : (1 / (Real.sinc θ : ℂ)) • H ∈ hermitianTraceless := by
    have h₁ := hermitianTraceless.smul_mem (1 / Real.sinc θ) hH
    convert h₁ using 1
    ext i j
    simp
  have hn : ‖(1 / (Real.sinc θ : ℂ)) • H‖ = θ := by
    rw [norm_smul, norm_div, norm_one, Complex.norm_real, Real.norm_of_nonneg hp.le, hsin,
      ← sinc_mul_eq_sin θ]
    field_simp
  refine ⟨(1 / (Real.sinc θ : ℂ)) • H, ⟨hm, by rw [hn]; exact hπ, ?_⟩, ?_⟩
  · rw [matExp_I_smul _ hm, hn, hcos, smul_smul, mul_assoc, mul_one_div_cancel hsc, mul_one, ← hWe]
  · rintro Y ⟨hY, hn', he⟩
    have hY' : Y = Y.conjTranspose ∧ fullTrace Y = 0 := hY
    have hf := matExp_I_smul Y hY
    rw [he] at hf
    have h₁ : (t : ℂ) = (Real.cos ‖Y‖ : ℂ) := by
      rw [← ht, hf]
      exact halfTrace_smul_one_add_smul _ _ _ hY'.2
    have h₂ : t = Real.cos ‖Y‖ := Complex.ofReal_injective h₁
    have h₃ : θ = ‖Y‖ := by
      rw [hθ, h₂]
      exact Real.arccos_cos (norm_nonneg _) hn'.le
    rw [← h₃, hcos] at hf
    have h₄ : Complex.I • H = (Complex.I * (Real.sinc θ : ℂ)) • Y :=
      add_left_cancel (hWe.symm.trans hf)
    have h₅ : H = (Real.sinc θ : ℂ) • Y := by
      calc H = ((-Complex.I) * Complex.I) • H := by
            rw [neg_mul, Complex.I_mul_I, neg_neg, one_smul]
        _ = (-Complex.I) • (Complex.I • H) := mul_smul _ _ _
        _ = (-Complex.I) • ((Complex.I * (Real.sinc θ : ℂ)) • Y) := by rw [h₄]
        _ = ((-Complex.I * Complex.I) * (Real.sinc θ : ℂ)) • Y := by
            rw [smul_smul, mul_assoc]
        _ = (Real.sinc θ : ℂ) • Y := by rw [neg_mul, Complex.I_mul_I, neg_neg, one_mul]
    rw [h₅, smul_smul, one_div_mul_cancel hsc, one_smul]
private theorem unitaryLieLog_spec (W : ComplexMatrix2) (hW : W ∈ unitaryLogDomain) :
    unitaryLieLog W ∈ hermitianTraceless ∧ ‖unitaryLieLog W‖ < Real.pi ∧
      matExp (Complex.I • unitaryLieLog W) = W :=
  Classical.epsilon_spec (p := fun Y : ComplexMatrix2 => Y ∈ hermitianTraceless ∧
    operatorNorm Y < Real.pi ∧ matExp (Complex.I • Y) = W) (existsUnique_unitaryLieLog W hW).exists
private theorem inv_properties (T : ComplexMatrix2) (hT : T ∈ specialUnitary) :
    T⁻¹ = T.conjTranspose ∧ T⁻¹ ∈ specialUnitary ∧ T * T⁻¹ = 1 ∧ T⁻¹ * T = 1 ∧ IsUnit T := by
  obtain ⟨hu, hd⟩ := Matrix.mem_specialUnitaryGroup_iff.mp hT
  have h₁ : T * T.conjTranspose = 1 := Matrix.mem_unitaryGroup_iff.mp hu
  have hinv : T⁻¹ = T.conjTranspose := Matrix.inv_eq_right_inv h₁
  have hunit : IsUnit T := (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [hd]; exact isUnit_one)
  have hdet : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det _).mp hunit
  have h₂ : T.conjTranspose * T = 1 := by
    rw [← hinv]
    exact Matrix.nonsing_inv_mul _ hdet
  refine ⟨hinv, ?_, by rw [hinv]; exact h₁, by rw [hinv]; exact h₂, hunit⟩
  rw [hinv]
  refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨Matrix.mem_unitaryGroup_iff.mpr ?_, ?_⟩
  · rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
    exact h₂
  · rw [Matrix.det_conjTranspose, hd]
    simp
private theorem conj_mem_hermitianTraceless (T Y : ComplexMatrix2) (hT : T ∈ specialUnitary)
    (hY : Y ∈ hermitianTraceless) : T * Y * T⁻¹ ∈ hermitianTraceless := by
  obtain ⟨hinv, -, -, hl, -⟩ := inv_properties T hT
  have hY' : Y = Y.conjTranspose ∧ fullTrace Y = 0 := hY
  refine ⟨?_, ?_⟩
  · rw [hinv, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, ← hY'.1, mul_assoc]
  · have e : fullTrace (T * Y * T⁻¹) = fullTrace (T⁻¹ * T * Y) := by
      rw [mul_assoc T⁻¹ T Y]
      exact Matrix.trace_mul_comm (T * Y) T⁻¹
    rw [e, hl, one_mul]
    exact hY'.2
abbrev _root_.YangMills.DeltaSharedProofs.p501638 := @conj_mem_hermitianTraceless
end UnitaryLogFacts
open UnitaryLogFacts in
theorem unitaryLogConjugationProperties_of_operatorNorm (hNorm : OperatorNormUnderConjugation) :
    UnitaryLogConjugationProperties := by
  obtain ⟨-, hconj, -, -, hexp, -, -⟩ := hNorm
  refine ⟨fun A hA => ⟨?_, ?_, matExp_I_smul_mem A hA⟩, existsUnique_unitaryLieLog,
    fun W hW T hT => ?_⟩
  · rw [pow_two]
    exact self_mul_self_eq_norm_sq_smul A hA
  · rw [sincAngle_eq_sinc]
    exact matExp_I_smul A hA
  · obtain ⟨-, hTi, hr, hl, hunit⟩ := inv_properties T hT
    have hdom : T * W * T⁻¹ ∈ unitaryLogDomain := by
      refine ⟨specialUnitary.mul_mem (specialUnitary.mul_mem hT hW.1) hTi, fun h => hW.2 ?_⟩
      have h₁ : T * W * T⁻¹ = -1 := h
      exact show W = -1 from by
        calc W = (T⁻¹ * T) * W * (T⁻¹ * T) := by rw [hl, one_mul, mul_one]
          _ = T⁻¹ * (T * W * T⁻¹) * T := by simp only [mul_assoc]
          _ = -1 := by rw [h₁, mul_neg, mul_one, neg_mul, hl]
    obtain ⟨hY, hn, he⟩ := unitaryLieLog_spec W hW
    have hsmul : T * (Complex.I • unitaryLieLog W) * T⁻¹ =
        Complex.I • (T * unitaryLieLog W * T⁻¹) := by
      rw [mul_smul_comm, smul_mul_assoc]
    have hlog : unitaryLieLog (T * W * T⁻¹) = T * unitaryLieLog W * T⁻¹ := by
      refine (existsUnique_unitaryLieLog _ hdom).unique (unitaryLieLog_spec _ hdom)
        ⟨conj_mem_hermitianTraceless T _ hT hY, ?_, ?_⟩
      · have h₁ : ‖T * unitaryLieLog W * T⁻¹‖ = ‖unitaryLieLog W‖ :=
          hconj _ _ (Matrix.specialUnitaryGroup_le_unitaryGroup hT)
        rw [h₁]
        exact hn
      · rw [← hsmul, ← hexp T _ hunit, he]
    refine ⟨hdom, ?_⟩
    rw [unitaryLog, unitaryLog, hlog, mul_smul_comm, smul_mul_assoc]
end YangMills.Construction.Matrices.ComplexMatrix2
