import YangMills.Construction.FormsOnATorus.OrdersOfTheInverseSymbolProof
import YangMills.Construction.Lattice.MatricesBlocksAndGaugeTransformationsProof
import YangMills.Construction.Matrices.LinearMapsCompositesAndCoordinatesOfRealAnalyticMapsProof
import YangMills.Construction.Matrices.SpecialUnitaryAngles
import YangMills.Construction.Matrices.UnitaryLogConjugation
import Mathlib
open scoped Matrix.Norms.L2Operator
namespace YangMills.Construction.Matrices.ComplexMatrix2.RotationAngle
private theorem mem_unitaryGroup_of_mem {W : ComplexMatrix2} (hW : W ∈ specialUnitary) :
    W ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  (Matrix.mem_specialUnitaryGroup_iff.mp hW).1
private theorem det_eq_one_of_mem {W : ComplexMatrix2} (hW : W ∈ specialUnitary) : W.det = 1 :=
  (Matrix.mem_specialUnitaryGroup_iff.mp hW).2
private theorem star_mul_self_of_mem {W : ComplexMatrix2} (hW : W ∈ specialUnitary) :
    star W * W = 1 :=
  Matrix.mem_unitaryGroup_iff'.mp (mem_unitaryGroup_of_mem hW)
private theorem inv_eq_star_of_mem {W : ComplexMatrix2} (hW : W ∈ specialUnitary) :
    W⁻¹ = star W := by apply _root_.YangMills.Construction.Matrices.ComplexMatrix2.inv_eq_star_of_mem_specialUnitary <;> assumption
private theorem inv_mul_self_of_mem {W : ComplexMatrix2} (hW : W ∈ specialUnitary) :
    W⁻¹ * W = 1 := by apply _root_.YangMills.SharedProofs.p1227 <;> assumption
private theorem inv_mem_specialUnitary {W : ComplexMatrix2} (hW : W ∈ specialUnitary) :
    W⁻¹ ∈ specialUnitary := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.inv_mem_specialUnitary <;> assumption
private theorem add_inv_eq_trace_smul {W : ComplexMatrix2} (hW : W ∈ specialUnitary) :
    W + W⁻¹ = fullTrace W • (1 : ComplexMatrix2) := by
  have h : W⁻¹ = W.adjugate := by
    rw [Matrix.inv_def, det_eq_one_of_mem hW]
    simp
  rw [h, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fullTrace, Matrix.trace_fin_two]
  ring
private theorem fullTrace_inv {W : ComplexMatrix2} (hW : W ∈ specialUnitary) :
    fullTrace W⁻¹ = fullTrace W := by
  have h : Matrix.trace W + Matrix.trace W⁻¹ = Matrix.trace W * 2 := by
    have e := congrArg Matrix.trace (add_inv_eq_trace_smul hW)
    simpa [fullTrace, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one] using e
  simp only [fullTrace]
  linear_combination h
private theorem ofReal_re_halfTrace {W : ComplexMatrix2} (hW : W ∈ specialUnitary) :
    (((halfTrace W).re : ℝ) : ℂ) = halfTrace W := by
  have h₁ : star (fullTrace W) = fullTrace W := by
    have e : fullTrace (star W) = star (fullTrace W) := Matrix.trace_conjTranspose W
    rw [← e, ← inv_eq_star_of_mem hW, fullTrace_inv hW]
  apply Complex.conj_eq_iff_re.mp
  simp only [halfTrace, map_mul]
  have h₂ : (starRingEnd ℂ) (fullTrace W) = fullTrace W := h₁
  rw [h₂]
  simp only [map_div₀, map_one, map_ofNat]
private theorem abs_re_halfTrace_le {W : ComplexMatrix2} (hW : W ∈ specialUnitary) :
    |(halfTrace W).re| ≤ 1 := by
  have h₀ := entry_norm_bound_of_unitary (mem_unitaryGroup_of_mem hW) 0 0
  have h₁ := entry_norm_bound_of_unitary (mem_unitaryGroup_of_mem hW) 1 1
  have h₂ : ‖halfTrace W‖ ≤ 1 := by
    simp only [halfTrace, fullTrace, Matrix.trace_fin_two, norm_mul]
    have h₃ := norm_add_le (W 0 0) (W 1 1)
    norm_num
    linarith
  exact (Complex.abs_re_le_norm _).trans h₂
private theorem operatorNorm_sq_of_star_mul {X : ComplexMatrix2} {r : ℝ} (hr : 0 ≤ r)
    (h : star X * X = (r : ℂ) • (1 : ComplexMatrix2)) : operatorNorm X ^ 2 = r := by
  have c := CStarRing.norm_star_mul_self (x := X)
  rw [h, norm_smul, CStarRing.norm_one, mul_one, Complex.norm_real,
    Real.norm_of_nonneg hr] at c
  rw [sq]
  exact c.symm
private theorem ofReal_smul_one_injective {r s : ℝ}
    (h : (r : ℂ) • (1 : ComplexMatrix2) = (s : ℂ) • (1 : ComplexMatrix2)) : r = s := by
  have e := congrFun (congrFun h 0) 0
  simpa using e
private theorem isRotationAngle_iff {W : ComplexMatrix2} (hW : W ∈ specialUnitary) {θ : ℝ}
    (hθ : θ ∈ Set.Icc 0 Real.pi) :
    IsRotationAngle W θ ↔ (Real.cos θ : ℂ) = halfTrace W := by
  have e₁ : Complex.exp (θ * Complex.I) = Complex.cos θ + Complex.sin θ * Complex.I :=
    Complex.exp_mul_I θ
  have e₂ : Complex.exp (-(θ * Complex.I)) = Complex.cos θ - Complex.sin θ * Complex.I := by
    rw [← neg_mul, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    ring
  constructor
  · rintro ⟨-, h⟩
    have hs : Matrix.trace W = W.charpoly.roots.sum := Matrix.trace_eq_sum_roots_charpoly W
    rw [h] at hs
    simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton] at hs
    rw [e₁, e₂] at hs
    simp only [halfTrace, fullTrace, hs]
    push_cast
    ring
  · intro h
    refine ⟨hθ, ?_⟩
    have hp : W.charpoly = (Multiset.map (fun a => Polynomial.X - Polynomial.C a)
        ({Complex.exp (θ * Complex.I), Complex.exp (-(θ * Complex.I))} : Multiset ℂ)).prod := by
      have ht : Matrix.trace W =
          Complex.exp (θ * Complex.I) + Complex.exp (-(θ * Complex.I)) := by
        rw [e₁, e₂]
        simp only [halfTrace, fullTrace] at h
        push_cast at h
        linear_combination -2 * h
      have hd : Complex.exp (θ * Complex.I) * Complex.exp (-(θ * Complex.I)) = 1 := by
        rw [← Complex.exp_add]
        simp
      rw [Matrix.charpoly_fin_two, ht, det_eq_one_of_mem hW]
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
        Multiset.prod_cons, Multiset.prod_singleton]
      rw [← hd]
      simp only [map_add, map_mul]
      ring
    rw [hp, Polynomial.roots_multiset_prod_X_sub_C]
private theorem exists_isRotationAngle {W : ComplexMatrix2} (hW : W ∈ specialUnitary) :
    ∃ θ, IsRotationAngle W θ := by
  have hb := abs_le.mp (abs_re_halfTrace_le hW)
  refine ⟨Real.arccos (halfTrace W).re, ?_⟩
  rw [isRotationAngle_iff hW ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩,
    Real.cos_arccos hb.1 hb.2]
  exact ofReal_re_halfTrace hW
private theorem isRotationAngle_rotationAngle {W : ComplexMatrix2} (hW : W ∈ specialUnitary) :
    IsRotationAngle W (rotationAngle W) :=
  Classical.epsilon_spec (exists_isRotationAngle hW)
private theorem rotationAngle_mem_Icc {W : ComplexMatrix2} (hW : W ∈ specialUnitary) :
    rotationAngle W ∈ Set.Icc 0 Real.pi :=
  (isRotationAngle_rotationAngle hW).1
private theorem cos_rotationAngle {W : ComplexMatrix2} (hW : W ∈ specialUnitary) :
    (Real.cos (rotationAngle W) : ℂ) = halfTrace W :=
  (isRotationAngle_iff hW (rotationAngle_mem_Icc hW)).mp (isRotationAngle_rotationAngle hW)
private theorem eq_rotationAngle {W : ComplexMatrix2} (hW : W ∈ specialUnitary) {θ : ℝ}
    (hθ : θ ∈ Set.Icc 0 Real.pi) (h : (Real.cos θ : ℂ) = halfTrace W) :
    θ = rotationAngle W := by
  refine Real.injOn_cos hθ (rotationAngle_mem_Icc hW) ?_
  exact_mod_cast h.trans (cos_rotationAngle hW).symm
private theorem rotationAngle_one : rotationAngle (1 : ComplexMatrix2) = 0 := by
  have h := eq_rotationAngle (W := 1) (one_mem _) (θ := 0) ⟨le_rfl, Real.pi_pos.le⟩ (by
    simp [halfTrace, fullTrace, Matrix.trace_one])
  exact h.symm
private theorem star_mul_sub_one_eq {W : ComplexMatrix2} (hW : W ∈ specialUnitary) :
    star (W - 1) * (W - 1) =
      ((2 - 2 * Real.cos (rotationAngle W) : ℝ) : ℂ) • (1 : ComplexMatrix2) := by
  have ht : ((2 - 2 * Real.cos (rotationAngle W) : ℝ) : ℂ) = 2 - fullTrace W := by
    have hc := cos_rotationAngle hW
    rw [Complex.ofReal_cos] at hc
    push_cast
    rw [hc]
    simp only [halfTrace]
    ring
  have hs := add_inv_eq_trace_smul hW
  rw [inv_eq_star_of_mem hW] at hs
  rw [ht, sub_smul, ← hs, two_smul, star_sub, star_one, sub_mul, mul_sub, mul_sub,
    star_mul_self_of_mem hW]
  simp only [mul_one, one_mul]
  abel
private theorem star_mul_add_one_eq {W : ComplexMatrix2} (hW : W ∈ specialUnitary) :
    star (W + 1) * (W + 1) =
      ((2 + 2 * Real.cos (rotationAngle W) : ℝ) : ℂ) • (1 : ComplexMatrix2) := by
  have ht : ((2 + 2 * Real.cos (rotationAngle W) : ℝ) : ℂ) = 2 + fullTrace W := by
    have hc := cos_rotationAngle hW
    rw [Complex.ofReal_cos] at hc
    push_cast
    rw [hc]
    simp only [halfTrace]
    ring
  have hs := add_inv_eq_trace_smul hW
  rw [inv_eq_star_of_mem hW] at hs
  rw [ht, add_smul, ← hs, two_smul, star_add, star_one, add_mul, mul_add, mul_add,
    star_mul_self_of_mem hW]
  simp only [mul_one, one_mul]
  abel
private theorem two_mul_sin_half_sq (θ : ℝ) :
    (2 * Real.sin (θ / 2)) ^ 2 = 2 - 2 * Real.cos θ := by apply _root_.YangMills.SharedProofs.p90038 <;> assumption
private theorem two_mul_cos_half_sq (θ : ℝ) :
    (2 * Real.cos (θ / 2)) ^ 2 = 2 + 2 * Real.cos θ := by
  have e := Real.cos_two_mul (θ / 2)
  rw [show 2 * (θ / 2) = θ by ring] at e
  rw [e]
  ring
private theorem half_mem_Icc {θ : ℝ} (h : θ ∈ Set.Icc 0 Real.pi) :
    θ / 2 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
  have := Real.pi_pos
  exact ⟨by linarith [h.1], by linarith [h.2]⟩
private theorem operatorNorm_sub_one {W : ComplexMatrix2} (hW : W ∈ specialUnitary) :
    operatorNorm (W - 1) = 2 * Real.sin (rotationAngle W / 2) := by
  have hm := rotationAngle_mem_Icc hW
  have hs : 0 ≤ Real.sin (rotationAngle W / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hm.1]) (by linarith [hm.2, Real.pi_pos])
  have hr : 0 ≤ 2 - 2 * Real.cos (rotationAngle W) := by
    rw [← two_mul_sin_half_sq]
    positivity
  have h := operatorNorm_sq_of_star_mul hr (star_mul_sub_one_eq hW)
  rw [← two_mul_sin_half_sq] at h
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h
private theorem operatorNorm_add_one {W : ComplexMatrix2} (hW : W ∈ specialUnitary) :
    operatorNorm (W + 1) = 2 * Real.cos (rotationAngle W / 2) := by
  have hc : 0 ≤ Real.cos (rotationAngle W / 2) :=
    Real.cos_nonneg_of_mem_Icc (half_mem_Icc (rotationAngle_mem_Icc hW))
  have hr : 0 ≤ 2 + 2 * Real.cos (rotationAngle W) := by
    rw [← two_mul_cos_half_sq]
    positivity
  have h := operatorNorm_sq_of_star_mul hr (star_mul_add_one_eq hW)
  rw [← two_mul_cos_half_sq] at h
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h
private theorem rotationAngle_inv {W : ComplexMatrix2} (hW : W ∈ specialUnitary) :
    rotationAngle W⁻¹ = rotationAngle W := by
  refine (eq_rotationAngle (inv_mem_specialUnitary hW) (rotationAngle_mem_Icc hW) ?_).symm
  rw [cos_rotationAngle hW]
  simp only [halfTrace]
  rw [fullTrace_inv hW]
private theorem rotationAngle_conj {W T : ComplexMatrix2} (hW : W ∈ specialUnitary)
    (hT : T ∈ specialUnitary) : rotationAngle W = rotationAngle (T * W * T⁻¹) := by
  refine eq_rotationAngle (mul_mem (mul_mem hT hW) (inv_mem_specialUnitary hT))
    (rotationAngle_mem_Icc hW) ?_
  rw [cos_rotationAngle hW]
  simp only [halfTrace, fullTrace]
  rw [Matrix.trace_mul_comm (T * W), ← mul_assoc, inv_mul_self_of_mem hT, one_mul]
private theorem two_div_pi_mul_rotationAngle_le {W : ComplexMatrix2} (hW : W ∈ specialUnitary) :
    2 / Real.pi * rotationAngle W ≤ operatorNorm (W - 1) := by
  have hm := rotationAngle_mem_Icc hW
  have h := Real.mul_le_sin (x := rotationAngle W / 2) (by linarith [hm.1]) (by linarith [hm.2])
  rw [operatorNorm_sub_one hW]
  have e : 2 / Real.pi * rotationAngle W = 2 * (2 / Real.pi * (rotationAngle W / 2)) := by ring
  rw [e]
  linarith
private theorem operatorNorm_sub_one_le_rotationAngle {W : ComplexMatrix2}
    (hW : W ∈ specialUnitary) : operatorNorm (W - 1) ≤ rotationAngle W := by
  have hm := rotationAngle_mem_Icc hW
  have h := Real.sin_le (x := rotationAngle W / 2) (by linarith [hm.1])
  rw [operatorNorm_sub_one hW]
  linarith
private theorem sincAngle_eq_sinc (a : ℝ) : sincAngle a = Real.sinc a := by
  unfold sincAngle
  by_cases h : a = 0
  · simp [h]
  · rw [if_neg h, Real.sinc_of_ne_zero h, inv_mul_eq_div]
abbrev _root_.YangMills.SharedProofs.p10222 := @sincAngle_eq_sinc
private theorem sinc_mul_self_eq_sin (a : ℝ) : Real.sinc a * a = Real.sin a := by apply _root_.YangMills.Construction.PeriodicLattice.ElementaryStepFacts.sinc_mul_self_eq_sin <;> assumption
private theorem matExp_I_smul_eq (h₁ : UnitaryLogConjugationProperties) {A : ComplexMatrix2}
    (hA : A ∈ hermitianTraceless) : matExp (Complex.I • A) =
      (Real.cos (operatorNorm A) : ℂ) • (1 : ComplexMatrix2) +
        (Complex.I * (Real.sinc (operatorNorm A) : ℂ)) • A := by
  rw [(h₁.1 A hA).2.1, sincAngle_eq_sinc]
private theorem matExp_I_smul_mem (h₁ : UnitaryLogConjugationProperties) {A : ComplexMatrix2}
    (hA : A ∈ hermitianTraceless) : matExp (Complex.I • A) ∈ specialUnitary :=
  (h₁.1 A hA).2.2
private theorem cos_operatorNorm_eq_halfTrace (h₁ : UnitaryLogConjugationProperties)
    {A : ComplexMatrix2} (hA : A ∈ hermitianTraceless) :
    (Real.cos (operatorNorm A) : ℂ) = halfTrace (matExp (Complex.I • A)) := by
  have ht : fullTrace A = 0 := hA.2
  rw [matExp_I_smul_eq h₁ hA]
  simp only [halfTrace, fullTrace] at ht ⊢
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, ht, Matrix.trace_one]
  simp
  ring
private theorem rotationAngle_matExp_eq (h₁ : UnitaryLogConjugationProperties)
    {A : ComplexMatrix2} (hA : A ∈ hermitianTraceless) (h : operatorNorm A ≤ Real.pi) :
    rotationAngle (matExp (Complex.I • A)) = operatorNorm A :=
  (eq_rotationAngle (matExp_I_smul_mem h₁ hA) ⟨norm_nonneg _, h⟩
    (cos_operatorNorm_eq_halfTrace h₁ hA)).symm
private theorem rotationAngle_matExp_le (h₁ : UnitaryLogConjugationProperties)
    {A : ComplexMatrix2} (hA : A ∈ hermitianTraceless) :
    rotationAngle (matExp (Complex.I • A)) ≤ operatorNorm A := by
  by_cases h : operatorNorm A ≤ Real.pi
  · exact (rotationAngle_matExp_eq h₁ hA h).le
  · exact (rotationAngle_mem_Icc (matExp_I_smul_mem h₁ hA)).2.trans (not_le.mp h).le
private theorem unitaryLieLog_spec (h₁ : UnitaryLogConjugationProperties) {W : ComplexMatrix2}
    (hW : W ∈ unitaryLogDomain) :
    unitaryLieLog W ∈ hermitianTraceless ∧ operatorNorm (unitaryLieLog W) < Real.pi ∧
      matExp (Complex.I • unitaryLieLog W) = W :=
  Classical.epsilon_spec (h₁.2.1 W hW).exists
private theorem operatorNorm_unitaryLieLog (h₁ : UnitaryLogConjugationProperties)
    {W : ComplexMatrix2} (hW : W ∈ unitaryLogDomain) :
    operatorNorm (unitaryLieLog W) = rotationAngle W := by
  obtain ⟨hs, hn, he⟩ := unitaryLieLog_spec h₁ hW
  have h := rotationAngle_matExp_eq h₁ hs hn.le
  rw [he] at h
  exact h.symm
private theorem operatorNorm_sub_one_lt_one_iff {W : ComplexMatrix2} (hW : W ∈ specialUnitary) :
    operatorNorm (W - 1) < 1 ↔ rotationAngle W < Real.pi / 3 := by
  have hp := Real.pi_pos
  have h₁ : Real.pi / 6 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith, by linarith⟩
  have h := Real.strictMonoOn_sin.lt_iff_lt (half_mem_Icc (rotationAngle_mem_Icc hW)) h₁
  rw [Real.sin_pi_div_six] at h
  rw [operatorNorm_sub_one hW]
  constructor
  · intro e
    have := h.mp (by linarith)
    linarith
  · intro e
    have := h.mpr (by linarith)
    linarith
private theorem unitaryLog_eq_logSeries (h₃ : ExpLogEstimates) {W : ComplexMatrix2}
    (hW : W ∈ specialUnitary) (h : operatorNorm (W - 1) < 1) : unitaryLog W = logSeries W := by
  obtain ⟨-, -, -, -, -, -, -, h₈, -, -⟩ := h₃
  obtain ⟨H, -, hl, -, -, -, hd⟩ := h₈ W (mem_unitaryGroup_of_mem hW) h
  rw [hl, (hd (det_eq_one_of_mem hW)).2.2.2]
  rfl
private theorem rotationAngle_mul_le {W₁ W₂ : ComplexMatrix2} (hW₁ : W₁ ∈ specialUnitary)
    (hW₂ : W₂ ∈ specialUnitary) :
    rotationAngle (W₁ * W₂) ≤ rotationAngle W₁ + rotationAngle W₂ := by
  have m₁ := rotationAngle_mem_Icc hW₁
  have m₂ := rotationAngle_mem_Icc hW₂
  have hW := mul_mem hW₁ hW₂
  have m := rotationAngle_mem_Icc hW
  by_cases h : Real.pi ≤ rotationAngle W₁ + rotationAngle W₂
  · exact m.2.trans h
  have h' := not_le.mp h
  have hid : W₁ * W₂ - 1 =
      (1 / 2 : ℂ) • ((W₁ - 1) * (W₂ + 1) + (W₁ + 1) * (W₂ - 1)) := by
    have e : (W₁ - 1) * (W₂ + 1) + (W₁ + 1) * (W₂ - 1) = (2 : ℂ) • (W₁ * W₂ - 1) := by
      rw [two_smul]
      noncomm_ring
    rw [e, smul_smul]
    norm_num
  have hb : operatorNorm (W₁ * W₂ - 1) ≤
      2 * Real.sin ((rotationAngle W₁ + rotationAngle W₂) / 2) := by
    have e₁ : operatorNorm ((W₁ - 1) * (W₂ + 1)) ≤
        operatorNorm (W₁ - 1) * operatorNorm (W₂ + 1) := norm_mul_le _ _
    have e₂ : operatorNorm ((W₁ + 1) * (W₂ - 1)) ≤
        operatorNorm (W₁ + 1) * operatorNorm (W₂ - 1) := norm_mul_le _ _
    have e₃ := norm_add_le ((W₁ - 1) * (W₂ + 1)) ((W₁ + 1) * (W₂ - 1))
    have e₄ : operatorNorm (W₁ * W₂ - 1) =
        1 / 2 * ‖(W₁ - 1) * (W₂ + 1) + (W₁ + 1) * (W₂ - 1)‖ := by
      rw [hid, operatorNorm, norm_smul]
      norm_num
    rw [operatorNorm_sub_one hW₁, operatorNorm_add_one hW₂] at e₁
    rw [operatorNorm_add_one hW₁, operatorNorm_sub_one hW₂] at e₂
    rw [add_div, Real.sin_add, e₄]
    simp only [operatorNorm] at e₁ e₂
    nlinarith
  rw [operatorNorm_sub_one hW] at hb
  have hin : (rotationAngle W₁ + rotationAngle W₂) ∈ Set.Icc 0 Real.pi :=
    ⟨add_nonneg m₁.1 m₂.1, h'.le⟩
  have hle : Real.sin (rotationAngle (W₁ * W₂) / 2) ≤
      Real.sin ((rotationAngle W₁ + rotationAngle W₂) / 2) := by linarith
  have := (Real.strictMonoOn_sin.le_iff_le (half_mem_Icc m) (half_mem_Icc hin)).mp hle
  linarith
private theorem list_prod_mem_specialUnitary {n : ℕ} {W : Fin n → ComplexMatrix2}
    (h : ∀ i, W i ∈ specialUnitary) : (List.ofFn W).prod ∈ specialUnitary := by
  refine Submonoid.list_prod_mem _ ?_
  intro x hx
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).mp hx
  exact h i
private theorem prod_rotationAngle_and_operatorNorm_le (h₂ : OperatorNormUnderConjugation)
    (n : ℕ) :
    ∀ (W W' : Fin n → ComplexMatrix2), (∀ i, W i ∈ specialUnitary) →
      (∀ i, W' i ∈ specialUnitary) →
      rotationAngle ((List.ofFn W).prod * ((List.ofFn W').prod)⁻¹) ≤
          ∑ i, rotationAngle (W i * (W' i)⁻¹) ∧
        operatorNorm ((List.ofFn W).prod - (List.ofFn W').prod) ≤
          ∑ i, operatorNorm (W i * (W' i)⁻¹ - 1) := by
  induction n with
  | zero =>
    intro W W' _ _
    simp [rotationAngle_one]
  | succ n ih =>
    intro W W' hW hW'
    obtain ⟨i₁, i₂⟩ :=
      ih (fun i => W i.succ) (fun i => W' i.succ) (fun i => hW _) (fun i => hW' _)
    have hR : (List.ofFn fun i : Fin n => W i.succ).prod ∈ specialUnitary :=
      list_prod_mem_specialUnitary fun i => hW _
    have hR' : (List.ofFn fun i : Fin n => W' i.succ).prod ∈ specialUnitary :=
      list_prod_mem_specialUnitary fun i => hW' _
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Fin.sum_univ_succ,
      Fin.sum_univ_succ]
    generalize (List.ofFn fun i : Fin n => W i.succ).prod = R at *
    generalize (List.ofFn fun i : Fin n => W' i.succ).prod = R' at *
    have a₀ := hW 0
    have b₀ := hW' 0
    generalize W 0 = A at *
    generalize W' 0 = B at *
    constructor
    · have e : A * R * (B * R')⁻¹ = A * B⁻¹ * (B * (R * R'⁻¹) * B⁻¹) := by
        rw [Matrix.mul_inv_rev]
        simp only [mul_assoc]
        rw [← mul_assoc B⁻¹ B, inv_mul_self_of_mem b₀, one_mul]
      have hm : R * R'⁻¹ ∈ specialUnitary := mul_mem hR (inv_mem_specialUnitary hR')
      rw [e]
      have c := rotationAngle_mul_le (mul_mem a₀ (inv_mem_specialUnitary b₀))
        (mul_mem (mul_mem b₀ hm) (inv_mem_specialUnitary b₀))
      rw [← rotationAngle_conj hm b₀] at c
      linarith
    · have e : A * R - B * R' = A * (R - R') + (A - B) * R' := by noncomm_ring
      have c₁ : operatorNorm (A * (R - R')) = operatorNorm (R - R') :=
        CStarRing.norm_mem_unitary_mul _ (mem_unitaryGroup_of_mem a₀)
      have c₂ : operatorNorm ((A - B) * R') = operatorNorm (A - B) :=
        CStarRing.norm_mul_mem_unitary _ (mem_unitaryGroup_of_mem hR')
      have c₃ := h₂.2.2.2.1 A B (mem_unitaryGroup_of_mem a₀) (mem_unitaryGroup_of_mem b₀)
      have c₄ := norm_add_le (A * (R - R')) ((A - B) * R')
      rw [e]
      simp only [operatorNorm] at c₁ c₂ c₃ i₂ ⊢
      rw [c₁, c₂, ← c₃] at c₄
      linarith
private theorem mul_self_eq_of_mem (h₁ : UnitaryLogConjugationProperties) {A : ComplexMatrix2}
    (hA : A ∈ hermitianTraceless) :
    A * A = ((operatorNorm A ^ 2 : ℝ) : ℂ) • (1 : ComplexMatrix2) := by
  have h := (h₁.1 A hA).1
  rw [sq A] at h
  rw [h]
  push_cast
  rfl
private theorem star_eq_self_of_mem {A : ComplexMatrix2} (hA : A ∈ hermitianTraceless) :
    star A = A := hA.1.symm
private theorem ofReal_smul_mem {A : ComplexMatrix2} (hA : A ∈ hermitianTraceless) (x : ℝ) :
    (x : ℂ) • A ∈ hermitianTraceless := by
  have hh : A = A.conjTranspose := hA.1
  have ht : fullTrace A = 0 := hA.2
  refine ⟨?_, ?_⟩
  · rw [Matrix.conjTranspose_smul, ← hh]
    simp
  · simp only [fullTrace] at ht ⊢
    rw [Matrix.trace_smul, ht, smul_zero]
abbrev _root_.YangMills.SharedProofs.p60538 := @ofReal_smul_mem
private theorem exists_anticommutator (h₁ : UnitaryLogConjugationProperties)
    {Y Y' : ComplexMatrix2} (hY : Y ∈ hermitianTraceless) (hY' : Y' ∈ hermitianTraceless) :
    ∃ p : ℝ, |p| ≤ operatorNorm Y * operatorNorm Y' ∧
      Y * Y' + Y' * Y = ((2 * p : ℝ) : ℂ) • (1 : ComplexMatrix2) ∧
      operatorNorm (Y - Y') ^ 2 = operatorNorm Y ^ 2 + operatorNorm Y' ^ 2 - 2 * p := by
  have sY := mul_self_eq_of_mem h₁ hY
  have sY' := mul_self_eq_of_mem h₁ hY'
  have sP := mul_self_eq_of_mem h₁ (hermitianTraceless.add_mem hY hY')
  have sM := mul_self_eq_of_mem h₁ (hermitianTraceless.sub_mem hY hY')
  set p : ℝ := (operatorNorm (Y + Y') ^ 2 - operatorNorm Y ^ 2 - operatorNorm Y' ^ 2) / 2
    with hp
  have hanti : Y * Y' + Y' * Y = ((2 * p : ℝ) : ℂ) • (1 : ComplexMatrix2) := by
    have e : Y * Y' + Y' * Y = (Y + Y') * (Y + Y') - Y * Y - Y' * Y' := by noncomm_ring
    have c : ((2 * p : ℝ) : ℂ) =
        ((operatorNorm (Y + Y') ^ 2 : ℝ) : ℂ) - ((operatorNorm Y ^ 2 : ℝ) : ℂ) -
          ((operatorNorm Y' ^ 2 : ℝ) : ℂ) := by
      rw [hp]
      push_cast
      ring
    rw [e, sP, sY, sY', c, sub_smul, sub_smul]
  have hminus : operatorNorm (Y - Y') ^ 2 =
      operatorNorm Y ^ 2 + operatorNorm Y' ^ 2 - 2 * p := by
    apply ofReal_smul_one_injective (r := operatorNorm (Y - Y') ^ 2)
    have e : (Y - Y') * (Y - Y') = Y * Y + Y' * Y' - (Y * Y' + Y' * Y) := by noncomm_ring
    rw [← sM, e, sY, sY', hanti, ← add_smul, ← sub_smul]
    push_cast
    rfl
  refine ⟨p, ?_, hanti, hminus⟩
  have t₁ : operatorNorm (Y + Y') ≤ operatorNorm Y + operatorNorm Y' := norm_add_le _ _
  have t₂ : operatorNorm (Y - Y') ≤ operatorNorm Y + operatorNorm Y' := norm_sub_le _ _
  have n₁ : 0 ≤ operatorNorm (Y + Y') := norm_nonneg _
  have n₂ : 0 ≤ operatorNorm (Y - Y') := norm_nonneg _
  have q₁ : operatorNorm (Y + Y') ^ 2 ≤ (operatorNorm Y + operatorNorm Y') ^ 2 := pow_le_pow_left₀ n₁ t₁ 2
  have q₂ : operatorNorm (Y - Y') ^ 2 ≤ (operatorNorm Y + operatorNorm Y') ^ 2 := pow_le_pow_left₀ n₂ t₂ 2
  rw [abs_le]
  constructor
  · rw [hminus] at q₂
    nlinarith
  · rw [hp]
    nlinarith
private theorem operatorNorm_scalar_add_I_smul_sq (h₁ : UnitaryLogConjugationProperties) (α : ℝ)
    {Z : ComplexMatrix2} (hZ : Z ∈ hermitianTraceless) :
    operatorNorm ((α : ℂ) • (1 : ComplexMatrix2) + Complex.I • Z) ^ 2 =
      α ^ 2 + operatorNorm Z ^ 2 := by
  refine operatorNorm_sq_of_star_mul (by positivity) ?_
  have hs : star ((α : ℂ) • (1 : ComplexMatrix2) + Complex.I • Z) =
      (α : ℂ) • (1 : ComplexMatrix2) - Complex.I • Z := by
    rw [star_add, star_smul, star_smul, star_one, star_eq_self_of_mem hZ, sub_eq_add_neg,
      ← neg_smul]
    simp
  have sZ := mul_self_eq_of_mem h₁ hZ
  rw [hs]
  have e : ((α : ℂ) • (1 : ComplexMatrix2) - Complex.I • Z) *
      ((α : ℂ) • (1 : ComplexMatrix2) + Complex.I • Z) =
      ((α : ℂ) * α) • (1 : ComplexMatrix2) + Z * Z := by
    have e₁ : ((α : ℂ) • (1 : ComplexMatrix2) - Complex.I • Z) *
        ((α : ℂ) • (1 : ComplexMatrix2) + Complex.I • Z) =
        ((α : ℂ) * α) • (1 : ComplexMatrix2) - (Complex.I * Complex.I) • (Z * Z) := by
      simp only [sub_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
      module
    rw [e₁, Complex.I_mul_I, neg_smul, one_smul, sub_neg_eq_add]
  rw [e, sZ, ← add_smul]
  push_cast
  congr 1
  ring
private theorem exists_cos_parametrisation (h₁ : UnitaryLogConjugationProperties)
    {Y Y' : ComplexMatrix2} (hY : Y ∈ hermitianTraceless) (hY' : Y' ∈ hermitianTraceless) :
    ∃ q : ℝ, -1 ≤ q ∧ q ≤ 1 ∧
      operatorNorm (matExp (Complex.I • Y) - matExp (Complex.I • Y')) ^ 2 =
        2 - 2 * Real.cos (operatorNorm Y) * Real.cos (operatorNorm Y') -
          2 * q * Real.sin (operatorNorm Y) * Real.sin (operatorNorm Y') ∧
      operatorNorm (Y - Y') ^ 2 =
        operatorNorm Y ^ 2 + operatorNorm Y' ^ 2 - 2 * q * operatorNorm Y * operatorNorm Y' := by
  obtain ⟨p, hp, hanti, hminus⟩ := exists_anticommutator h₁ hY hY'
  set a := operatorNorm Y with ha
  set b := operatorNorm Y' with hb
  have na : 0 ≤ a := norm_nonneg _
  have nb : 0 ≤ b := norm_nonneg _
  obtain ⟨q, q₁, q₂, hq⟩ : ∃ q : ℝ, -1 ≤ q ∧ q ≤ 1 ∧ p = q * (a * b) := by
    by_cases h : a * b = 0
    · refine ⟨0, by norm_num, by norm_num, ?_⟩
      rw [h] at hp
      rw [zero_mul]
      exact abs_nonpos_iff.mp hp
    · have hpos : 0 < a * b := lt_of_le_of_ne (mul_nonneg na nb) (Ne.symm h)
      have hab := abs_le.mp hp
      refine ⟨p / (a * b), ?_, ?_, (div_mul_cancel₀ p h).symm⟩
      · rw [le_div_iff₀ hpos]
        linarith [hab.1]
      · rw [div_le_iff₀ hpos]
        linarith [hab.2]
  set s := Real.sinc a with hs
  set t := Real.sinc b with ht
  have sa : s * a = Real.sin a := sinc_mul_self_eq_sin a
  have tb : t * b = Real.sin b := sinc_mul_self_eq_sin b
  have hZ : (s : ℂ) • Y - (t : ℂ) • Y' ∈ hermitianTraceless :=
    hermitianTraceless.sub_mem (ofReal_smul_mem hY s) (ofReal_smul_mem hY' t)
  have hZZ : operatorNorm ((s : ℂ) • Y - (t : ℂ) • Y') ^ 2 =
      Real.sin a ^ 2 + Real.sin b ^ 2 - 2 * q * Real.sin a * Real.sin b := by
    apply ofReal_smul_one_injective
      (r := operatorNorm ((s : ℂ) • Y - (t : ℂ) • Y') ^ 2)
    rw [← mul_self_eq_of_mem h₁ hZ]
    have e : ((s : ℂ) • Y - (t : ℂ) • Y') * ((s : ℂ) • Y - (t : ℂ) • Y') =
        ((s : ℂ) * s) • (Y * Y) + ((t : ℂ) * t) • (Y' * Y') -
          ((s : ℂ) * t) • (Y * Y' + Y' * Y) := by
      simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm]
      module
    rw [e, mul_self_eq_of_mem h₁ hY, mul_self_eq_of_mem h₁ hY', hanti, smul_smul, smul_smul,
      smul_smul, ← add_smul, ← sub_smul]
    congr 1
    rw [← sa, ← tb, hq, ← ha, ← hb]
    push_cast
    ring
  have hdiff : matExp (Complex.I • Y) - matExp (Complex.I • Y') =
      ((Real.cos a - Real.cos b : ℝ) : ℂ) • (1 : ComplexMatrix2) +
        Complex.I • ((s : ℂ) • Y - (t : ℂ) • Y') := by
    rw [matExp_I_smul_eq h₁ hY, matExp_I_smul_eq h₁ hY', smul_sub, smul_smul, smul_smul,
      Complex.ofReal_sub, sub_smul]
    abel
  refine ⟨q, q₁, q₂, ?_, ?_⟩
  · rw [hdiff, operatorNorm_scalar_add_I_smul_sq h₁ _ hZ, hZZ]
    have c₁ := Real.sin_sq_add_cos_sq a
    have c₂ := Real.sin_sq_add_cos_sq b
    linear_combination c₁ + c₂
  · rw [hminus, hq]
    ring
private theorem matExp_lipschitz (h₁ : UnitaryLogConjugationProperties) {A B : ComplexMatrix2}
    (hA : A ∈ hermitianTraceless) (hB : B ∈ hermitianTraceless) :
    operatorNorm (matExp (Complex.I • A) - matExp (Complex.I • B)) ≤ operatorNorm (A - B) := by
  obtain ⟨q, q₁, q₂, hf, hg⟩ := exists_cos_parametrisation h₁ hA hB
  set a := operatorNorm A
  set b := operatorNorm B
  have e₁ := Real.one_sub_sq_div_two_le_cos (x := a - b)
  have e₂ := Real.one_sub_sq_div_two_le_cos (x := a + b)
  rw [Real.cos_sub] at e₁
  rw [Real.cos_add] at e₂
  have f₁ := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + q) (sub_nonneg.mpr e₁)
  have f₂ := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - q) (sub_nonneg.mpr e₂)
  refine le_of_sq_le_sq ?_ (norm_nonneg _)
  rw [hf, hg]
  nlinarith
private theorem mul_le_sin_of_chord {m u : ℝ} (hm : 0 < m) (hmπ : m ≤ Real.pi) (hu : 0 ≤ u)
    (hum : u ≤ m) : Real.sin m / m * u ≤ Real.sin u := by
  have hc : (1 - u / m) • Real.sin 0 + (u / m) • Real.sin m ≤
      Real.sin ((1 - u / m) • (0 : ℝ) + (u / m) • m) :=
    strictConcaveOn_sin_Icc.concaveOn.2 ⟨le_rfl, Real.pi_pos.le⟩ ⟨hm.le, hmπ⟩
      (sub_nonneg.mpr ((div_le_one hm).mpr hum)) (div_nonneg hu hm.le) (by ring)
  simp only [smul_eq_mul, Real.sin_zero, mul_zero, zero_add] at hc
  rw [div_mul_cancel₀ u hm.ne'] at hc
  calc Real.sin m / m * u = u / m * Real.sin m := by ring
    _ ≤ Real.sin u := hc
private theorem sq_mul_le_two_sub_two_cos {m x : ℝ} (hm : 0 < m) (hmπ : m < Real.pi)
    (hx : |x| / 2 ≤ m) : (Real.sin m / m) ^ 2 * x ^ 2 ≤ 2 - 2 * Real.cos x := by
  have hs : 0 ≤ Real.sin m / m := (div_pos (Real.sin_pos_of_pos_of_lt_pi hm hmπ) hm).le
  have h := mul_le_sin_of_chord hm hmπ.le (by positivity) hx
  have c := pow_le_pow_left₀ (mul_nonneg hs (by positivity : 0 ≤ |x| / 2)) h 2
  have t := two_mul_sin_half_sq |x|
  rw [Real.cos_abs] at t
  rw [← t, ← sq_abs x]
  calc (Real.sin m / m) ^ 2 * |x| ^ 2 = 4 * (Real.sin m / m * (|x| / 2)) ^ 2 := by ring
    _ ≤ 4 * Real.sin (|x| / 2) ^ 2 := by linarith
    _ = (2 * Real.sin (|x| / 2)) ^ 2 := by ring
private theorem matExp_inverse_lipschitz (h₁ : UnitaryLogConjugationProperties) {m : ℝ}
    (hm : 0 < m) (hmπ : m < Real.pi) {Y Y' : ComplexMatrix2} (hY : Y ∈ hermitianTraceless)
    (hY' : Y' ∈ hermitianTraceless) (ha : operatorNorm Y ≤ m) (hb : operatorNorm Y' ≤ m) :
    operatorNorm (Y - Y') ≤
      m / Real.sin m * operatorNorm (matExp (Complex.I • Y) - matExp (Complex.I • Y')) := by
  obtain ⟨q, q₁, q₂, hf, hg⟩ := exists_cos_parametrisation h₁ hY hY'
  have na : 0 ≤ operatorNorm Y := norm_nonneg _
  have nb : 0 ≤ operatorNorm Y' := norm_nonneg _
  set a := operatorNorm Y
  set b := operatorNorm Y'
  have d₁ : |a - b| ≤ 2 * m := abs_le.mpr ⟨by linarith, by linarith⟩
  have d₂ : |a + b| ≤ 2 * m := abs_le.mpr ⟨by linarith, by linarith⟩
  have e₁ := sq_mul_le_two_sub_two_cos hm hmπ (x := a - b) (by linarith)
  have e₂ := sq_mul_le_two_sub_two_cos hm hmπ (x := a + b) (by linarith)
  rw [Real.cos_sub] at e₁
  rw [Real.cos_add] at e₂
  have cpos : 0 < Real.sin m / m := div_pos (Real.sin_pos_of_pos_of_lt_pi hm hmπ) hm
  set c := Real.sin m / m with hc
  have f₁ := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + q) (sub_nonneg.mpr e₁)
  have f₂ := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - q) (sub_nonneg.mpr e₂)
  have hfin : (c * operatorNorm (Y - Y')) ^ 2 ≤
      operatorNorm (matExp (Complex.I • Y) - matExp (Complex.I • Y')) ^ 2 := by
    rw [mul_pow, hf, hg]
    nlinarith
  have hle := le_of_sq_le_sq hfin (norm_nonneg _)
  have hms : m / Real.sin m = c⁻¹ := by rw [hc, inv_div]
  rw [hms, ← div_eq_inv_mul, le_div_iff₀ cpos]
  linarith
private theorem mem_unitaryLogDomain_of {W : ComplexMatrix2} (hW : W ∈ specialUnitary) {m : ℝ}
    (hmπ : m < Real.pi) (h : rotationAngle W ≤ m) : W ∈ unitaryLogDomain := by
  refine ⟨hW, ?_⟩
  intro e
  have e' : W = -1 := e
  have hc : ((Real.cos Real.pi : ℝ) : ℂ) = halfTrace W := by
    rw [e']
    simp [halfTrace, fullTrace, Matrix.trace_neg, Matrix.trace_one]
  have := eq_rotationAngle hW ⟨Real.pi_pos.le, le_rfl⟩ hc
  linarith
private theorem div_sin_lt_of_lt_pi_div_three {m : ℝ} (h₀ : 0 < m) (h₁ : m < Real.pi / 3) :
    m / Real.sin m < 2 * Real.pi / (3 * Real.sqrt 3) := by
  have hp := Real.pi_pos
  have hsin : 0 < Real.sin m := Real.sin_pos_of_pos_of_lt_pi h₀ (by linarith)
  have hb : 0 < 3 * m / Real.pi := by positivity
  have hb₁ : 3 * m / Real.pi < 1 := by
    rw [div_lt_one hp]
    linarith
  have hc : (1 - 3 * m / Real.pi) • Real.sin 0 + (3 * m / Real.pi) • Real.sin (Real.pi / 3) <
      Real.sin ((1 - 3 * m / Real.pi) • (0 : ℝ) + (3 * m / Real.pi) • (Real.pi / 3)) :=
    strictConcaveOn_sin_Icc.2 ⟨le_rfl, hp.le⟩ ⟨by linarith, by linarith⟩ (by
      intro e
      linarith) (by linarith) hb (by ring)
  simp only [smul_eq_mul, Real.sin_zero, mul_zero, zero_add, Real.sin_pi_div_three] at hc
  have e : 3 * m / Real.pi * (Real.pi / 3) = m := by field_simp
  rw [e] at hc
  rw [div_lt_iff₀ hsin]
  have k : 0 < 2 * Real.pi / (3 * Real.sqrt 3) := by positivity
  have e₂ : 2 * Real.pi / (3 * Real.sqrt 3) * (3 * m / Real.pi * (Real.sqrt 3 / 2)) = m := by
    field_simp
  calc m = 2 * Real.pi / (3 * Real.sqrt 3) * (3 * m / Real.pi * (Real.sqrt 3 / 2)) := e₂.symm
    _ < 2 * Real.pi / (3 * Real.sqrt 3) * Real.sin m := mul_lt_mul_of_pos_left hc k
private theorem div_sin_le_one_add_sq {m : ℝ} (h₀ : 0 < m) (h₁ : m ≤ 1) :
    m / Real.sin m ≤ 1 + m ^ 2 / 5 := by
  have hsin : 0 < Real.sin m :=
    Real.sin_pos_of_pos_of_lt_pi h₀ (by linarith [Real.pi_gt_three])
  have h := Real.sin_ge_sub_cube h₀.le
  rw [div_le_iff₀ hsin]
  have k : 0 ≤ m ^ 3 * (1 - m ^ 2) := mul_nonneg (by positivity) (by nlinarith)
  calc m ≤ (1 + m ^ 2 / 5) * (m - m ^ 3 / 6) := by nlinarith
    _ ≤ (1 + m ^ 2 / 5) * Real.sin m := mul_le_mul_of_nonneg_left h (by positivity)
theorem specialUnitaryAngleBounds_holds (h₁ : UnitaryLogConjugationProperties)
    (h₂ : OperatorNormUnderConjugation) (h₃ : ExpLogEstimates) :
    SpecialUnitaryAngleBounds := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro W hW
    refine ⟨fun θ => ⟨fun h => ?_, ?_⟩, fun θ hθ => isRotationAngle_iff hW hθ⟩
    · exact eq_rotationAngle hW h.1 ((isRotationAngle_iff hW h.1).mp h)
    · rintro rfl
      exact isRotationAngle_rotationAngle hW
  · intro W hW
    exact ⟨operatorNorm_sub_one hW, operatorNorm_add_one hW, rotationAngle_inv hW,
      fun T hT => rotationAngle_conj hW hT, two_div_pi_mul_rotationAngle_le hW,
      operatorNorm_sub_one_le_rotationAngle hW⟩
  · intro A hA
    exact ⟨(h₁.1 A hA).1, matExp_I_smul_eq h₁ hA, rotationAngle_matExp_le h₁ hA,
      rotationAngle_matExp_eq h₁ hA⟩
  · intro W hW
    exact ⟨operatorNorm_unitaryLieLog h₁ hW, operatorNorm_sub_one_lt_one_iff hW.1,
      fun h => unitaryLog_eq_logSeries h₃ hW.1 ((operatorNorm_sub_one_lt_one_iff hW.1).mpr h)⟩
  · intro W₁ hW₁ W₂ hW₂
    exact rotationAngle_mul_le hW₁ hW₂
  · intro n W W' hW hW'
    exact prod_rotationAngle_and_operatorNorm_le h₂ n W W' hW hW'
  · intro A hA B hB
    exact matExp_lipschitz h₁ hA hB
  · intro m hm hmπ
    refine ⟨fun Y hY Y' hY' a b => matExp_inverse_lipschitz h₁ hm hmπ hY hY' a b,
      fun W hW W' hW' a b => ?_⟩
    have d := mem_unitaryLogDomain_of hW hmπ a
    have d' := mem_unitaryLogDomain_of hW' hmπ b
    obtain ⟨s, -, e⟩ := unitaryLieLog_spec h₁ d
    obtain ⟨s', -, e'⟩ := unitaryLieLog_spec h₁ d'
    have c := matExp_inverse_lipschitz h₁ hm hmπ s s'
      (by rw [operatorNorm_unitaryLieLog h₁ d]; exact a)
      (by rw [operatorNorm_unitaryLieLog h₁ d']; exact b)
    rwa [e, e'] at c
  · exact fun m a b => div_sin_lt_of_lt_pi_div_three a b
  · exact fun m a b => div_sin_le_one_add_sq a b
end YangMills.Construction.Matrices.ComplexMatrix2.RotationAngle
