import YangMills.Construction.Lattice.MatricesBlocksAndGaugeTransformationsProof
import YangMills.Construction.Matrices.SpecialUnitaryExpSurjective
import Mathlib
open scoped Matrix.Norms.L2Operator
namespace YangMills.Construction.Matrices.ComplexMatrix2
private theorem mul_self_of_fullTrace_eq_zero (A : ComplexMatrix2) (h : fullTrace A = 0) :
    A * A = (-A.det) • (1 : ComplexMatrix2) := by
  have h₁ : A 1 1 = -A 0 0 := by
    have h₂ : A 0 0 + A 1 1 = 0 := by simpa [fullTrace, Matrix.trace_fin_two] using h
    linear_combination h₂
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, h₁] <;> ring
abbrev _root_.YangMills.SharedProofs.p51248 := @mul_self_of_fullTrace_eq_zero
private theorem mul_star_self_eq_norm_sq (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [← Complex.normSq_eq_norm_sq]
  exact Complex.mul_conj _
private theorem neg_det_eq_norm_sq (Y : ComplexMatrix2) (hY : Y ∈ hermitianTraceless) :
    -Y.det = (‖Y‖ : ℂ) ^ 2 := by
  have hY' : Y = Y.conjTranspose ∧ fullTrace Y = 0 := hY
  obtain ⟨hh, ht⟩ := hY'
  have hm := mul_self_of_fullTrace_eq_zero Y ht
  have e₀₁ : Y 0 1 = star (Y 1 0) := congrFun (congrFun hh 0) 1
  have e₀₀ : Y 0 0 = star (Y 0 0) := congrFun (congrFun hh 0) 0
  have hr : -Y.det = ((‖Y 0 0‖ ^ 2 + ‖Y 1 0‖ ^ 2 : ℝ) : ℂ) := by
    have e := congrFun (congrFun hm 0) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, Matrix.one_apply_eq,
      smul_eq_mul, mul_one] at e
    have a := mul_star_self_eq_norm_sq (Y 0 0)
    rw [← e₀₀] at a
    have b := mul_star_self_eq_norm_sq (Y 1 0)
    rw [← e₀₁] at b
    rw [← e, Complex.ofReal_add, ← a, ← b]
    ring
  have hn : ‖Y‖ * ‖Y‖ = ‖Y 0 0‖ ^ 2 + ‖Y 1 0‖ ^ 2 := by
    have c := CStarRing.norm_star_mul_self (x := Y)
    have s : star Y = Y := hh.symm
    rw [s, hm, hr, norm_smul, CStarRing.norm_one, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)] at c
    exact c.symm
  rw [hr, ← hn]
  push_cast
  ring
abbrev _root_.YangMills.SharedProofs.p28491 := @neg_det_eq_norm_sq
private theorem mul_self_eq_norm_sq_smul (Y : ComplexMatrix2) (hY : Y ∈ hermitianTraceless) :
    Y * Y = ((‖Y‖ : ℂ) ^ 2) • (1 : ComplexMatrix2) := by
  have hY' : Y = Y.conjTranspose ∧ fullTrace Y = 0 := hY
  rw [mul_self_of_fullTrace_eq_zero Y hY'.2, neg_det_eq_norm_sq Y hY]
private theorem sinc_mul_self_eq_sin (θ : ℝ) : Real.sinc θ * θ = Real.sin θ := by apply _root_.YangMills.Construction.PeriodicLattice.ElementaryStepFacts.sinc_mul_self_eq_sin <;> assumption
private theorem sinc_pos_of_lt_pi {θ : ℝ} (h₀ : 0 ≤ θ) (h₁ : θ < Real.pi) :
    0 < Real.sinc θ := by
  rcases eq_or_lt_of_le h₀ with h | h
  · simp [← h]
  · rw [Real.sinc_of_ne_zero h.ne']
    exact div_pos (Real.sin_pos_of_pos_of_lt_pi h h₁) h
abbrev _root_.YangMills.SharedProofs.p1819 := @sinc_pos_of_lt_pi
private theorem pow_eq_of_mul_self_eq (W : ComplexMatrix2) (w : ℂ) (hw : w ≠ 0)
    (h : W * W = (w * w) • (1 : ComplexMatrix2)) (n : ℕ) :
    W ^ n = ((w ^ n + (-w) ^ n) / 2) • (1 : ComplexMatrix2) +
      ((w ^ n - (-w) ^ n) / (2 * w)) • W := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have e₁ : (w ^ n - (-w) ^ n) / (2 * w) * (w * w) = (w ^ (n + 1) + (-w) ^ (n + 1)) / 2 := by
      rw [pow_succ w n, pow_succ (-w) n]
      field_simp
      ring
    have e₂ : (w ^ n + (-w) ^ n) / 2 = (w ^ (n + 1) - (-w) ^ (n + 1)) / (2 * w) := by
      rw [pow_succ w n, pow_succ (-w) n]
      field_simp
      ring
    rw [pow_succ W n, ih, add_mul, smul_mul_assoc, smul_mul_assoc, one_mul, h, smul_smul, e₁, e₂,
      add_comm]
private theorem matExp_eq_of_mul_self_eq (W : ComplexMatrix2) (w : ℂ) (hw : w ≠ 0)
    (h : W * W = (w * w) • (1 : ComplexMatrix2)) :
    matExp W = ((Complex.exp w + Complex.exp (-w)) / 2) • (1 : ComplexMatrix2) +
      ((Complex.exp w - Complex.exp (-w)) / (2 * w)) • W := by
  have hW := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) W
  have h₁ := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) w
  have h₂ := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (-w)
  rw [← Complex.exp_eq_exp_ℂ] at h₁ h₂
  have hS := (((h₁.add h₂).div_const 2).smul_const (1 : ComplexMatrix2)).add
    (((h₁.sub h₂).div_const (2 * w)).smul_const W)
  have e : (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • W ^ n) = fun b : ℕ =>
      ((((b.factorial : ℂ)⁻¹) • w ^ b + ((b.factorial : ℂ)⁻¹) • (-w) ^ b) / 2) •
          (1 : ComplexMatrix2) +
        ((((b.factorial : ℂ)⁻¹) • w ^ b - ((b.factorial : ℂ)⁻¹) • (-w) ^ b) / (2 * w)) • W := by
    funext n
    rw [pow_eq_of_mul_self_eq W w hw h n, smul_add, smul_smul, smul_smul]
    congr 2 <;> simp only [smul_eq_mul] <;> ring
  rw [e] at hW
  exact hW.unique hS
private theorem matExp_I_smul (Y : ComplexMatrix2) (hY : Y ∈ hermitianTraceless) :
    matExp (Complex.I • Y) =
      (Real.cos ‖Y‖ : ℂ) • (1 : ComplexMatrix2) + (Complex.I * (Real.sinc ‖Y‖ : ℂ)) • Y := by
  by_cases h0 : ‖Y‖ = 0
  · have hz : Y = 0 := norm_eq_zero.mp h0
    subst hz
    simp [matExp]
  have hθ : (‖Y‖ : ℂ) ≠ 0 := by exact_mod_cast h0
  have hw : (‖Y‖ : ℂ) * Complex.I ≠ 0 := mul_ne_zero hθ Complex.I_ne_zero
  have hsq : (Complex.I • Y) * (Complex.I • Y) =
      (((‖Y‖ : ℂ) * Complex.I) * ((‖Y‖ : ℂ) * Complex.I)) • (1 : ComplexMatrix2) := by
    rw [smul_mul_smul_comm, mul_self_eq_norm_sq_smul Y hY, smul_smul]
    congr 1
    ring
  have h := matExp_eq_of_mul_self_eq (Complex.I • Y) ((‖Y‖ : ℂ) * Complex.I) hw hsq
  have ep := Complex.exp_mul_I (‖Y‖ : ℂ)
  have em : Complex.exp (-((‖Y‖ : ℂ) * Complex.I)) =
      Complex.cos (‖Y‖ : ℂ) - Complex.sin (‖Y‖ : ℂ) * Complex.I := by
    rw [← neg_mul, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    ring
  rw [h, ep, em, Real.sinc_of_ne_zero h0, smul_smul]
  push_cast
  congr 2
  · ring
  · have hI := Complex.I_ne_zero
    field_simp
    ring
abbrev _root_.YangMills.SharedProofs.p44010 := @matExp_I_smul
private theorem matExp_neg_I_smul (Y : ComplexMatrix2) (hY : Y ∈ hermitianTraceless) :
    matExp (-(Complex.I • Y)) =
      (Real.cos ‖Y‖ : ℂ) • (1 : ComplexMatrix2) - (Complex.I * (Real.sinc ‖Y‖ : ℂ)) • Y := by
  have h := matExp_I_smul (-Y) (hermitianTraceless.neg_mem hY)
  rw [smul_neg, norm_neg, smul_neg, ← sub_eq_add_neg] at h
  exact h
private theorem matExp_I_smul_mem (Y : ComplexMatrix2) (hY : Y ∈ hermitianTraceless) :
    matExp (Complex.I • Y) ∈ specialUnitary := by apply _root_.YangMills.Construction.Matrices.ComplexMatrix2.ExpSurjective.matExp_I_smul_mem_specialUnitary <;> assumption
private theorem exists_halfTrace_decomposition (U : ComplexMatrix2) (hU : U ∈ specialUnitary) :
    ∃ (t : ℝ) (H : ComplexMatrix2), H ∈ hermitianTraceless ∧ halfTrace U = t ∧
      U = (t : ℂ) • (1 : ComplexMatrix2) + Complex.I • H ∧
      U⁻¹ = (t : ℂ) • (1 : ComplexMatrix2) - Complex.I • H ∧
      t ^ 2 + ‖H‖ ^ 2 = 1 := by
  obtain ⟨hu, hd⟩ := Matrix.mem_specialUnitaryGroup_iff.mp hU
  have h₁ : U * U.conjTranspose = 1 := Matrix.mem_unitaryGroup_iff.mp hu
  have hinv : U⁻¹ = U.conjTranspose := Matrix.inv_eq_right_inv h₁
  have hadj : U.adjugate = U.conjTranspose := by
    have h₂ := Matrix.adjugate_mul U
    rw [hd, one_smul] at h₂
    calc U.adjugate = U.adjugate * (U * U.conjTranspose) := by rw [h₁, mul_one]
      _ = U.conjTranspose := by rw [← mul_assoc, h₂, one_mul]
  have hsum : U + U.conjTranspose = fullTrace U • (1 : ComplexMatrix2) := by
    rw [← hadj, Matrix.adjugate_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [fullTrace, Matrix.trace_fin_two, add_comm]
  have e₂ : fullTrace U.conjTranspose = star (fullTrace U) := Matrix.trace_conjTranspose U
  have hstar : star (fullTrace U) = fullTrace U := by
    have e : fullTrace (U + U.conjTranspose) = 2 * fullTrace U := by
      rw [hsum]
      simp only [fullTrace, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
      push_cast
      ring
    have e₃ : fullTrace (U + U.conjTranspose) = fullTrace U + fullTrace U.conjTranspose :=
      Matrix.trace_add _ _
    rw [e₂] at e₃
    linear_combination e - e₃
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.mp hstar
  obtain ⟨H, hHdef⟩ : ∃ H : ComplexMatrix2, H = (-(Complex.I / 2)) • (U - U.conjTranspose) :=
    ⟨_, rfl⟩
  have hI : Complex.I * (-(Complex.I / 2)) = 1 / 2 := by
    linear_combination (-1 / 2 : ℂ) * Complex.I_sq
  have ht : (((r / 2 : ℝ)) : ℂ) = (1 / 2) * fullTrace U := by
    rw [hr]
    push_cast
    ring
  have hIH : Complex.I • H = (1 / 2 : ℂ) • (U - U.conjTranspose) := by
    rw [hHdef, smul_smul, hI]
  have htone : (((r / 2 : ℝ)) : ℂ) • (1 : ComplexMatrix2) =
      (1 / 2 : ℂ) • (U + U.conjTranspose) := by
    rw [ht, mul_smul, hsum]
  have hUe : U = (((r / 2 : ℝ)) : ℂ) • (1 : ComplexMatrix2) + Complex.I • H := by
    rw [htone, hIH]
    module
  have hVe : U.conjTranspose = (((r / 2 : ℝ)) : ℂ) • (1 : ComplexMatrix2) - Complex.I • H := by
    rw [htone, hIH]
    module
  have hH : H ∈ hermitianTraceless := by
    have hc : star (-(Complex.I / 2)) = Complex.I / 2 := by
      apply Complex.ext <;> simp
      norm_num
    have hH₁ : H = H.conjTranspose := by
      rw [hHdef, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
        Matrix.conjTranspose_conjTranspose, hc]
      module
    have hH₂ : fullTrace H = 0 := by
      have e₃ : fullTrace (U - U.conjTranspose) = fullTrace U - fullTrace U.conjTranspose :=
        Matrix.trace_sub _ _
      have e₄ : fullTrace H = (-(Complex.I / 2)) * fullTrace (U - U.conjTranspose) := by
        rw [hHdef]
        exact Matrix.trace_smul _ _
      rw [e₄, e₃, e₂, hstar]
      ring
    exact ⟨hH₁, hH₂⟩
  refine ⟨r / 2, H, hH, ?_, hUe, by rw [hinv]; exact hVe, ?_⟩
  · rw [ht]
  · obtain ⟨a, ha⟩ : ∃ a : ℂ, a = (((r / 2 : ℝ)) : ℂ) := ⟨_, rfl⟩
    rw [← ha] at hUe hVe
    have e : (a • (1 : ComplexMatrix2) + Complex.I • H) *
        (a • (1 : ComplexMatrix2) - Complex.I • H) = 1 := by
      rw [← hUe, ← hVe]
      exact h₁
    have e₅ : (a • (1 : ComplexMatrix2) + Complex.I • H) *
        (a • (1 : ComplexMatrix2) - Complex.I • H) =
        (a * a + (‖H‖ : ℂ) ^ 2) • (1 : ComplexMatrix2) := by
      rw [add_mul, mul_sub, mul_sub, smul_mul_smul_comm, smul_mul_smul_comm, smul_mul_smul_comm,
        smul_mul_smul_comm, one_mul, mul_one, one_mul, mul_self_eq_norm_sq_smul H hH,
        Complex.I_mul_I, mul_comm a Complex.I]
      module
    rw [e₅] at e
    have e₆ := congrFun (congrFun e 0) 0
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at e₆
    rw [ha] at e₆
    exact show (r / 2) ^ 2 + ‖H‖ ^ 2 = 1 from by
      have e₈ : ((((r / 2) ^ 2 + ‖H‖ ^ 2 : ℝ)) : ℂ) = ((1 : ℝ) : ℂ) := by
        push_cast
        push_cast at e₆
        linear_combination e₆
      exact Complex.ofReal_injective e₈
abbrev _root_.YangMills.SharedProofs.p99018 := @exists_halfTrace_decomposition
private theorem halfTrace_mem_Icc_and_eq_neg_one (U : ComplexMatrix2) (hU : U ∈ specialUnitary) :
    (∃ t ∈ Set.Icc (-1 : ℝ) 1, halfTrace U = t) ∧ (halfTrace U = -1 → U = -1) := by
  obtain ⟨t, H, -, ht, hUe, -, hs⟩ := exists_halfTrace_decomposition U hU
  have hb : |t| ≤ 1 := sq_le_one_iff_abs_le_one t |>.mp (by nlinarith [sq_nonneg ‖H‖])
  refine ⟨⟨t, abs_le.mp hb, ht⟩, fun h => ?_⟩
  have ht₁ : t = -1 := by
    have e : (t : ℂ) = ((-1 : ℝ) : ℂ) := by
      rw [← ht, h]
      simp
    exact Complex.ofReal_injective e
  have hH : H = 0 := by
    have e : ‖H‖ ^ 2 = 0 := by
      rw [ht₁] at hs
      linarith
    exact norm_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp e)
  rw [hUe, hH, ht₁]
  simp
private theorem exists_closedForm_data (U : ComplexMatrix2) (hU : U ∈ unitaryLogDomain) :
    ∃ (t θ : ℝ) (H : ComplexMatrix2), H ∈ hermitianTraceless ∧ halfTrace U = t ∧
      U = (t : ℂ) • (1 : ComplexMatrix2) + Complex.I • H ∧ θ = Real.arccos t ∧
      Real.cos θ = t ∧ 0 ≤ θ ∧ θ < Real.pi ∧ ‖H‖ = Real.sin θ ∧
      unitaryLieLogClosedForm U = (1 / (Real.sinc θ : ℂ)) • H := by
  have hG : U ∈ specialUnitary := hU.1
  have hne : U ≠ -1 := fun h => hU.2 h
  obtain ⟨t, H, hH, ht, hUe, hVe, hs⟩ := exists_halfTrace_decomposition U hG
  obtain ⟨⟨_, hI, ht'⟩, hm⟩ := halfTrace_mem_Icc_and_eq_neg_one U hG
  have hb : |t| ≤ 1 := sq_le_one_iff_abs_le_one t |>.mp (by nlinarith [sq_nonneg ‖H‖])
  obtain ⟨hb₁, hb₂⟩ := abs_le.mp hb
  have htn : ¬ t ≤ -1 := by
    intro h
    have e : t = -1 := le_antisymm h hb₁
    exact hne (hm (by rw [ht, e]; simp))
  have hcos : Real.cos (Real.arccos t) = t := Real.cos_arccos hb₁ hb₂
  have hpos : 0 ≤ Real.arccos t := Real.arccos_nonneg t
  have hpi : Real.arccos t < Real.pi :=
    lt_of_le_of_ne (Real.arccos_le_pi t) fun h => htn (Real.arccos_eq_pi.mp h)
  have hsin : ‖H‖ = Real.sin (Real.arccos t) := by
    have h₀ := Real.sin_nonneg_of_nonneg_of_le_pi hpos hpi.le
    refine (sq_eq_sq₀ (norm_nonneg _) h₀).mp ?_
    have h₁ := Real.sin_sq_add_cos_sq (Real.arccos t)
    rw [hcos] at h₁
    linarith
  refine ⟨t, Real.arccos t, H, hH, ht, hUe, rfl, hcos, hpos, hpi, hsin, ?_⟩
  have hd : U - U⁻¹ = (2 * Complex.I) • H := by
    calc U - U⁻¹ = ((t : ℂ) • (1 : ComplexMatrix2) + Complex.I • H) -
          ((t : ℂ) • (1 : ComplexMatrix2) - Complex.I • H) := by
          rw [hVe, ← hUe]
      _ = (2 * Complex.I) • H := by module
  have h2 : (2 * Complex.I) ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
  rw [unitaryLieLogClosedForm, ht, Complex.ofReal_re, hd, smul_smul (1 / (2 * Complex.I)),
    one_div_mul_cancel h2, one_smul]
private theorem halfTrace_smul_one_add_smul (c d : ℂ) (A : ComplexMatrix2)
    (h : fullTrace A = 0) : halfTrace (c • (1 : ComplexMatrix2) + d • A) = c := by
  have h₀ : Matrix.trace A = 0 := h
  simp only [halfTrace, fullTrace, Matrix.trace_add, Matrix.trace_smul, h₀, Matrix.trace_one,
    Fintype.card_fin, smul_eq_mul]
  push_cast
  ring
abbrev _root_.YangMills.SharedProofs.p42130 := @halfTrace_smul_one_add_smul
private theorem isLogarithm_iff_eq_closedForm (U : ComplexMatrix2) (hU : U ∈ unitaryLogDomain)
    (Y : ComplexMatrix2) :
    (Y ∈ hermitianTraceless ∧ ‖Y‖ < Real.pi ∧ matExp (Complex.I • Y) = U) ↔
      Y = unitaryLieLogClosedForm U := by
  obtain ⟨t, θ, H, hH, ht, hUe, hθ, hcos, h₀, hπ, hsin, hF⟩ := exists_closedForm_data U hU
  have hs : 0 < Real.sinc θ := sinc_pos_of_lt_pi h₀ hπ
  have hsc : (Real.sinc θ : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  rw [hF]
  constructor
  · rintro ⟨hY, hn, he⟩
    have hY' : Y = Y.conjTranspose ∧ fullTrace Y = 0 := hY
    have hf := matExp_I_smul Y hY
    rw [he] at hf
    have h₁ : (t : ℂ) = (Real.cos ‖Y‖ : ℂ) := by
      rw [← ht, hf]
      exact halfTrace_smul_one_add_smul _ _ _ hY'.2
    have h₂ : t = Real.cos ‖Y‖ := Complex.ofReal_injective h₁
    have h₃ : θ = ‖Y‖ := by
      rw [hθ, h₂]
      exact Real.arccos_cos (norm_nonneg _) hn.le
    rw [← h₃, hcos] at hf
    have h₄ : Complex.I • H = (Complex.I * (Real.sinc θ : ℂ)) • Y :=
      add_left_cancel (hUe.symm.trans hf)
    have h₅ : H = (Real.sinc θ : ℂ) • Y := by
      calc H = ((-Complex.I) * Complex.I) • H := by
            rw [neg_mul, Complex.I_mul_I, neg_neg, one_smul]
        _ = (-Complex.I) • (Complex.I • H) := mul_smul _ _ _
        _ = (-Complex.I) • ((Complex.I * (Real.sinc θ : ℂ)) • Y) := by rw [h₄]
        _ = ((-Complex.I * Complex.I) * (Real.sinc θ : ℂ)) • Y := by
            rw [smul_smul, mul_assoc]
        _ = (Real.sinc θ : ℂ) • Y := by rw [neg_mul, Complex.I_mul_I, neg_neg, one_mul]
    rw [h₅, smul_smul, one_div_mul_cancel hsc, one_smul]
  · rintro rfl
    have hm : (1 / (Real.sinc θ : ℂ)) • H ∈ hermitianTraceless := by
      have h₁ := hermitianTraceless.smul_mem (1 / Real.sinc θ) hH
      convert h₁ using 1
      ext i j
      simp
    have hn : ‖(1 / (Real.sinc θ : ℂ)) • H‖ = θ := by
      rw [norm_smul, norm_div, norm_one, Complex.norm_real, Real.norm_of_nonneg hs.le, hsin,
        ← sinc_mul_self_eq_sin θ]
      field_simp
    refine ⟨hm, by rw [hn]; exact hπ, ?_⟩
    rw [matExp_I_smul _ hm, hn, hcos, smul_smul, mul_assoc, mul_one_div_cancel hsc, mul_one,
      ← hUe]
private theorem continuousOn_closedForm :
    ContinuousOn unitaryLieLogClosedForm unitaryLogDomain := by
  have hg : Continuous fun U : ComplexMatrix2 =>
      Real.sinc (Real.arccos (halfTrace U).re) := by
    have c₁ : Continuous fun U : ComplexMatrix2 => (halfTrace U).re :=
      Complex.continuous_re.comp (continuous_const.mul continuous_id.matrix_trace)
    exact Real.continuous_sinc.comp (Real.continuous_arccos.comp c₁)
  have hne : ∀ U ∈ unitaryLogDomain,
      ((Real.sinc (Real.arccos (halfTrace U).re) : ℝ) : ℂ) ≠ 0 := by
    intro U hU
    obtain ⟨t, θ, H, -, ht, -, hθ, -, h₀, hπ, -, -⟩ := exists_closedForm_data U hU
    rw [ht, Complex.ofReal_re, ← hθ]
    exact_mod_cast (sinc_pos_of_lt_pi h₀ hπ).ne'
  have hc : ContinuousOn (fun U : ComplexMatrix2 =>
      (1 / ((Real.sinc (Real.arccos (halfTrace U).re) : ℝ) : ℂ)) •
        (1 / (2 * Complex.I)) • (U - U.conjTranspose)) unitaryLogDomain := by
    refine ContinuousOn.smul
      (continuousOn_const.div (Complex.continuous_ofReal.comp hg).continuousOn hne) ?_
    have c₂ : Continuous fun U : ComplexMatrix2 => U - U.conjTranspose :=
      continuous_id.sub (Continuous.matrix_conjTranspose continuous_id)
    exact (c₂.const_smul (1 / (2 * Complex.I))).continuousOn
  refine hc.congr fun U hU => ?_
  have hinv : U⁻¹ = U.conjTranspose := Matrix.inv_eq_right_inv
    (Matrix.mem_unitaryGroup_iff.mp (Matrix.specialUnitaryGroup_le_unitaryGroup hU.1))
  simp only [unitaryLieLogClosedForm, hinv]
private theorem unitaryLieLog_spec (U : ComplexMatrix2) (hU : U ∈ unitaryLogDomain) :
    unitaryLieLog U ∈ hermitianTraceless ∧ ‖unitaryLieLog U‖ < Real.pi ∧
      matExp (Complex.I • unitaryLieLog U) = U :=
  Classical.epsilon_spec (p := fun Y : ComplexMatrix2 => Y ∈ hermitianTraceless ∧
    operatorNorm Y < Real.pi ∧ matExp (Complex.I • Y) = U)
    ⟨unitaryLieLogClosedForm U, (isLogarithm_iff_eq_closedForm U hU _).mpr rfl⟩
theorem unitaryLogarithmProperties_holds : UnitaryLogarithmProperties := by
  have hlog : ContinuousOn unitaryLieLog unitaryLogDomain :=
    continuousOn_closedForm.congr fun U hU =>
      (isLogarithm_iff_eq_closedForm U hU _).mp (unitaryLieLog_spec U hU)
  refine ⟨fun Y hY => ⟨?_, matExp_I_smul Y hY, matExp_neg_I_smul Y hY, matExp_I_smul_mem Y hY⟩,
    halfTrace_mem_Icc_and_eq_neg_one, isLogarithm_iff_eq_closedForm, continuousOn_closedForm,
    fun U hU => ?_, ?_⟩
  · rw [pow_two]
    exact mul_self_eq_norm_sq_smul Y hY
  · obtain ⟨h₁, h₂, h₃⟩ := unitaryLieLog_spec U hU
    exact ⟨h₁, h₂, h₃, unitaryLieLog U, h₁, rfl⟩
  · show ContinuousOn (fun U => Complex.I • unitaryLieLog U) unitaryLogDomain
    exact hlog.const_smul Complex.I
end YangMills.Construction.Matrices.ComplexMatrix2
