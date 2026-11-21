import YangMills.Construction.LawInAState.MomentsOfWickPolynomials
import Mathlib
set_option autoImplicit false
set_option linter.all false
noncomputable section
open MeasureTheory ProbabilityTheory MvPolynomial Equiv
open scoped NNReal ENNReal
namespace YangMills.Construction.WickMoments
variable {q : ℕ}
private lemma integrable_pow_stdGaussian (n : ℕ) : Integrable (fun x : ℝ => x ^ n) (gaussianReal 0 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h := (memLp_id_gaussianReal' (μ := 0) (v := 1) (n : ℝ≥0∞)
      (ENNReal.natCast_ne_top n)).integrable_norm_pow hn.ne'
    refine h.mono' (by fun_prop) (ae_of_all _ fun x => ?_)
    simp
abbrev _root_.YangMills.SharedProofs.p8958 := @integrable_pow_stdGaussian
private lemma integrable_gaussianPDFReal_mul {f : ℝ → ℝ} (hf : Integrable f (gaussianReal 0 1)) :
    Integrable (fun x => gaussianPDFReal 0 1 x * f x) := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)] at hf
  simpa [toReal_gaussianPDF] using hf
private lemma hasDerivAt_gaussianPDFReal_std (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have h1 : HasDerivAt (fun y : ℝ => -(y - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))) (-x) x := by
    have h0 : HasDerivAt (fun y : ℝ => y * y) (1 * x + x * 1) x :=
      (hasDerivAt_id' x).mul (hasDerivAt_id' x)
    have h1' : HasDerivAt (fun y : ℝ => -(y * y) / 2) (-(1 * x + x * 1) / 2) x := h0.neg.div_const 2
    have fe : (fun y : ℝ => -(y - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))) = fun y => -(y * y) / 2 := by
      funext y
      simp only [NNReal.coe_one, sub_zero, mul_one]
      ring
    rw [fe]
    exact h1'.congr_deriv (by ring)
  have h2 := (h1.exp).const_mul (Real.sqrt (2 * Real.pi * ((1 : ℝ≥0) : ℝ)))⁻¹
  have e : gaussianPDFReal 0 1 = fun y : ℝ => (Real.sqrt (2 * Real.pi * ((1 : ℝ≥0) : ℝ)))⁻¹ *
      Real.exp (-(y - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))) := by
    funext y
    simp [gaussianPDFReal]
  rw [e]
  refine h2.congr_deriv ?_
  beta_reduce
  ring
abbrev _root_.YangMills.SharedProofs.p43829 := @hasDerivAt_gaussianPDFReal_std
private lemma integral_pow_add_two_stdGaussian (n : ℕ) :
    ∫ x, x ^ (n + 2) ∂(gaussianReal 0 1) = (n + 1) * ∫ x, x ^ n ∂(gaussianReal 0 1) := by
  have hint := fun k => integrable_gaussianPDFReal_mul (integrable_pow_stdGaussian k)
  have hd : ∀ x : ℝ, HasDerivAt (fun y => y ^ (n + 1) * gaussianPDFReal 0 1 y)
      (((n : ℝ) + 1) * (gaussianPDFReal 0 1 x * x ^ n) - gaussianPDFReal 0 1 x * x ^ (n + 2)) x := by
    intro x
    have h3 : HasDerivAt (fun y => y ^ (n + 1) * gaussianPDFReal 0 1 y) _ x :=
      (hasDerivAt_pow (n + 1) x).mul (hasDerivAt_gaussianPDFReal_std x)
    refine h3.congr_deriv ?_
    simp only [add_tsub_cancel_right, Nat.cast_add, Nat.cast_one]
    ring
  have hi1 : Integrable (fun x : ℝ => ((n : ℝ) + 1) * (gaussianPDFReal 0 1 x * x ^ n) -
      gaussianPDFReal 0 1 x * x ^ (n + 2)) := ((hint n).const_mul _).sub (hint (n + 2))
  have hi2 : Integrable (fun y : ℝ => y ^ (n + 1) * gaussianPDFReal 0 1 y) := by
    simpa [mul_comm] using hint (n + 1)
  have h0 := integral_eq_zero_of_hasDerivAt_of_integrable hd hi1 hi2
  rw [integral_sub ((hint n).const_mul _) (hint (n + 2)), integral_const_mul] at h0
  simp only [integral_gaussianReal_eq_integral_smul one_ne_zero, smul_eq_mul]
  linarith
abbrev _root_.YangMills.DeltaSharedProofs.p500965 := @integral_pow_add_two_stdGaussian
private lemma integral_pow_succ_stdGaussian (k : ℕ) :
    ∫ x, x ^ (k + 1) ∂(gaussianReal 0 1) = k * ∫ x, x ^ (k - 1) ∂(gaussianReal 0 1) := by
  cases k with
  | zero => simp
  | succ k =>
    have := integral_pow_add_two_stdGaussian k
    simpa using this
variable {ι : Type} [Fintype ι] [DecidableEq ι]
private abbrev stdGaussianPi (ι : Type) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1
private lemma eval_monomial_eq_prod (z : ι → ℝ) (n : ι →₀ ℕ) (c : ℝ) :
    eval z (monomial n c) = c * ∏ b, z b ^ n b := by
  rw [eval_monomial, Finsupp.prod_fintype _ _ (by simp)]
private lemma integrable_eval_stdGaussianPi (P : MvPolynomial ι ℝ) :
    Integrable (fun z => eval z P) (stdGaussianPi ι) := by
  induction P using MvPolynomial.induction_on' with
  | monomial n c =>
    simp only [eval_monomial_eq_prod]
    exact (Integrable.fintype_prod (f := fun b x => x ^ n b)
      (fun b => integrable_pow_stdGaussian _)).const_mul c
  | add p q hp hq => exact (hp.add hq).congr (ae_of_all _ fun z => by simp)
private lemma integral_eval_X_mul_stdGaussianPi (a : ι) (P : MvPolynomial ι ℝ) :
    ∫ z, eval z (X a * P) ∂(stdGaussianPi ι) = ∫ z, eval z (pderiv a P) ∂(stdGaussianPi ι) := by
  induction P using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [mul_add, map_add]
    rw [integral_add (integrable_eval_stdGaussianPi _) (integrable_eval_stdGaussianPi _),
      integral_add (integrable_eval_stdGaussianPi _) (integrable_eval_stdGaussianPi _), hp, hq]
  | monomial n c =>
    have e1 : ∀ z : ι → ℝ, eval z (X a * monomial n c) =
        c * ∏ b, z b ^ (n b + if a = b then 1 else 0) := by
      intro z
      rw [map_mul, eval_X, eval_monomial_eq_prod]
      simp only [pow_add, Finset.prod_mul_distrib]
      simp only [pow_ite, pow_one, pow_zero, Finset.prod_ite_eq, Finset.mem_univ, if_true]
      ring
    have e2 : ∀ z : ι → ℝ, eval z (pderiv a (monomial n c)) =
        (c * n a) * ∏ b, z b ^ (n b - if a = b then 1 else 0) := by
      intro z
      rw [pderiv_monomial, eval_monomial_eq_prod]
      simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply]
    simp only [e1, e2]
    rw [integral_const_mul, integral_const_mul,
      integral_fintype_prod_eq_prod (𝕜 := ℝ) (fun b x => x ^ (n b + if a = b then 1 else 0)),
      integral_fintype_prod_eq_prod (𝕜 := ℝ) (fun b x => x ^ (n b - if a = b then 1 else 0)),
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ a), ← Finset.mul_prod_erase _ _ (Finset.mem_univ a)]
    simp only [if_true]
    rw [integral_pow_succ_stdGaussian (n a)]
    have : ∏ b ∈ Finset.univ.erase a, ∫ x, x ^ (n b + if a = b then 1 else 0) ∂(gaussianReal 0 1) =
        ∏ b ∈ Finset.univ.erase a, ∫ x, x ^ (n b - if a = b then 1 else 0) ∂(gaussianReal 0 1) := by
      refine Finset.prod_congr rfl fun b hb => ?_
      have : a ≠ b := fun h => by simp [h] at hb
      simp [this]
    rw [this]
    ring
private lemma pderiv_bind₁_eq_sum (l : ι → MvPolynomial ι ℝ) (a : ι) (P : MvPolynomial ι ℝ) :
    pderiv a (bind₁ l P) = ∑ k, pderiv a (l k) * bind₁ l (pderiv k P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p j hp =>
    simp only [map_mul, bind₁_X_right, Derivation.leibniz, smul_eq_mul, hp, map_add, pderiv_X,
      mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    · simp [Pi.single_apply, mul_comm]
    · refine Finset.sum_congr rfl fun k _ => ?_
      ring
private def mixCoords (B : ι → ι → ℝ) (z : ι → ℝ) : ι → ℝ := fun i => ∑ a, B i a * z a
private def linearForms (B : ι → ι → ℝ) : ι → MvPolynomial ι ℝ := fun i => ∑ a, MvPolynomial.C (B i a) * X a
private lemma eval_bind₁_linearForms (B : ι → ι → ℝ) (z : ι → ℝ) (P : MvPolynomial ι ℝ) :
    eval z (bind₁ (linearForms B) P) = eval (mixCoords B z) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp => simp [hp, linearForms, mixCoords]
private lemma pderiv_linearForms (B : ι → ι → ℝ) (a k : ι) :
    pderiv a (linearForms B k) = MvPolynomial.C (B k a) := by
  simp [linearForms, map_sum, Derivation.leibniz, pderiv_X, Pi.single_apply]
private lemma continuous_mixCoords (B : ι → ι → ℝ) : Continuous (mixCoords B) := by
  unfold mixCoords
  fun_prop
private lemma integrable_and_stein_map_mixCoords (B : ι → ι → ℝ) :
    (∀ P : MvPolynomial ι ℝ, Integrable (fun ξ => eval ξ P) ((stdGaussianPi ι).map (mixCoords B))) ∧
    ∀ (j : ι) (P : MvPolynomial ι ℝ), ∫ ξ, eval ξ (X j * P) ∂((stdGaussianPi ι).map (mixCoords B)) =
      ∑ k, (∑ a, B j a * B k a) * ∫ ξ, eval ξ (pderiv k P) ∂((stdGaussianPi ι).map (mixCoords B)) := by
  have hm : Measurable (mixCoords B) := (continuous_mixCoords B).measurable
  have hc : ∀ P : MvPolynomial ι ℝ, Continuous fun ξ : ι → ℝ => eval ξ P := fun P =>
    MvPolynomial.continuous_eval P
  have hI : ∀ P : MvPolynomial ι ℝ, ∫ ξ, eval ξ P ∂((stdGaussianPi ι).map (mixCoords B)) =
      ∫ z, eval z (bind₁ (linearForms B) P) ∂(stdGaussianPi ι) := by
    intro P
    rw [integral_map hm.aemeasurable (hc P).aestronglyMeasurable]
    simp only [eval_bind₁_linearForms]
  refine ⟨fun P => ?_, fun j P => ?_⟩
  · rw [integrable_map_measure (hc P).aestronglyMeasurable hm.aemeasurable]
    have := integrable_eval_stdGaussianPi (bind₁ (linearForms B) P)
    simpa [Function.comp_def, eval_bind₁_linearForms] using this
  · rw [hI]
    have h1 : ∀ z : ι → ℝ, eval z (bind₁ (linearForms B) (X j * P)) =
        ∑ a, B j a * eval z (X a * bind₁ (linearForms B) P) := by
      intro z
      simp only [map_mul, bind₁_X_right, eval_X]
      simp [linearForms, Finset.sum_mul, mul_assoc]
    simp only [h1]
    rw [integral_finset_sum _ fun a _ => (integrable_eval_stdGaussianPi _).const_mul _]
    simp only [integral_const_mul, integral_eval_X_mul_stdGaussianPi, pderiv_bind₁_eq_sum, pderiv_linearForms]
    have h2 : ∀ a : ι, ∫ z, eval z (∑ k, MvPolynomial.C (B k a) * bind₁ (linearForms B) (pderiv k P)) ∂(stdGaussianPi ι) =
        ∑ k, B k a * ∫ ξ, eval ξ (pderiv k P) ∂((stdGaussianPi ι).map (mixCoords B)) := by
      intro a
      simp only [map_sum, map_mul, eval_C]
      rw [integral_finset_sum _ fun k _ => (integrable_eval_stdGaussianPi _).const_mul _]
      simp only [integral_const_mul, hI]
    simp only [h2, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => ?_
    ring
private lemma eq_map_mixCoords_of_isCenteredGaussian {C : ι → ι → ℝ} (B : ι → ι → ℝ)
    (hC : ∀ i j, C i j = ∑ a, B i a * B j a)
    {μ : Measure (ι → ℝ)} (h : IsCenteredGaussian C μ) : μ = (stdGaussianPi ι).map (mixCoords B) := by
  have hm : Measurable (mixCoords B) := (continuous_mixCoords B).measurable
  haveI := h.1
  haveI : IsProbabilityMeasure ((stdGaussianPi ι).map (mixCoords B)) :=
    Measure.isProbabilityMeasure_map hm.aemeasurable
  refine Measure.ext_of_charFunDual ?_
  funext L
  have hL : ∀ v : ι → ℝ, L v = ∑ i, L (Pi.single i 1) * v i := by
    intro v
    have : v = ∑ i, v i • (Pi.single i (1 : ℝ) : ι → ℝ) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [this]
    simp [map_sum, mul_comm]
  set t : ι → ℝ := fun i => L (Pi.single i 1) with ht
  rw [charFunDual_apply, charFunDual_apply,
    integral_map hm.aemeasurable (by fun_prop)]
  have e1 : ∀ v : ι → ℝ, Complex.exp (((L v : ℝ) : ℂ) * Complex.I) =
      Complex.exp (Complex.I * ((∑ i, t i * v i : ℝ) : ℂ)) := by
    intro v
    rw [hL v, mul_comm]
  simp only [e1]
  rw [h.2 t]
  have e2 : ∀ z : ι → ℝ, Complex.exp (Complex.I * ((∑ i, t i * mixCoords B z i : ℝ) : ℂ)) =
      ∏ a, Complex.exp (((∑ i, t i * B i a : ℝ) : ℂ) * (z a : ℂ) * Complex.I) := by
    intro z
    rw [← Complex.exp_sum]
    congr 1
    have hr : ∑ i, t i * mixCoords B z i = ∑ a, (∑ i, t i * B i a) * z a := by
      simp only [mixCoords, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hr, Complex.ofReal_sum, mul_comm, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.ofReal_mul]
  simp only [e2]
  rw [integral_fintype_prod_eq_prod (𝕜 := ℂ) (E := fun _ : ι => ℝ) (μ := fun _ => gaussianReal 0 1)
    (fun a x => Complex.exp (((∑ i, t i * B i a : ℝ) : ℂ) * (x : ℂ) * Complex.I))]
  have e3 : ∀ s : ℝ, ∫ x : ℝ, Complex.exp ((s : ℂ) * (x : ℂ) * Complex.I) ∂(gaussianReal 0 1) =
      Complex.exp (-((s : ℂ) ^ 2) / 2) := by
    intro s
    have := charFun_gaussianReal (μ := 0) (v := 1) s
    rw [charFun_apply_real] at this
    rw [this]
    congr 1
    simp
    ring
  simp only [e3]
  rw [← Complex.exp_sum]
  congr 1
  have e4 : ∑ i, ∑ j, t i * C i j * t j = ∑ a, (∑ i, t i * B i a) ^ 2 := by
    simp only [hC, sq, Finset.sum_mul_sum, Finset.mul_sum, Finset.sum_mul]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [e4]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring
private def involutionsOn (S : Finset (Fin q)) : Finset (Perm (Fin q)) :=
  Finset.univ.filter fun σ => σ * σ = 1 ∧ ∀ a, a ∉ S → σ a = a
private def pairStarts (σ : Perm (Fin q)) : Finset (Fin q) := Finset.univ.filter fun a => a < σ a
private def involutionTerm (K : ι → ι → ℝ) (i : Fin q → ι) (S : Finset (Fin q)) (σ : Perm (Fin q)) :
    MvPolynomial ι ℝ :=
  MvPolynomial.C ((-1 : ℝ) ^ (pairStarts σ).card * ∏ a ∈ pairStarts σ, K (i a) (i (σ a))) *
    ∏ a ∈ S.filter (fun a => σ a = a), X (i a)
private def wickWord (K : ι → ι → ℝ) (i : Fin q → ι) (S : Finset (Fin q)) : MvPolynomial ι ℝ :=
  ∑ σ ∈ involutionsOn S, involutionTerm K i S σ
private lemma swap_mul_apply_of_fixed {τ : Perm (Fin q)} {a b c : Fin q} (ha : τ a = a) (hb : τ b = b)
    (hca : c ≠ a) (hcb : c ≠ b) : (swap a b * τ) c = τ c := by
  have h1 : τ c ≠ a := fun h => hca (τ.injective (h.trans ha.symm))
  have h2 : τ c ≠ b := fun h => hcb (τ.injective (h.trans hb.symm))
  rw [Perm.mul_apply, swap_apply_of_ne_of_ne h1 h2]
private lemma pairStarts_swap_mul {τ : Perm (Fin q)} {a b : Fin q} (hab : a ≠ b) (ha : τ a = a)
    (hb : τ b = b) : pairStarts (swap a b * τ) = insert (min a b) (pairStarts τ) := by
  have ea : (swap a b * τ) a = b := by simp [Perm.mul_apply, ha]
  have eb : (swap a b * τ) b = a := by simp [Perm.mul_apply, hb]
  ext c
  simp only [pairStarts, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  by_cases hca : c = a
  · subst hca
    rw [ea, ha]
    constructor
    · intro h
      exact Or.inl (min_eq_left h.le).symm
    · rintro (h | h)
      · exact lt_of_le_of_ne (min_eq_left_iff.1 h.symm) hab
      · exact absurd h (lt_irrefl _)
  by_cases hcb : c = b
  · subst hcb
    rw [eb, hb]
    constructor
    · intro h
      exact Or.inl (min_eq_right h.le).symm
    · rintro (h | h)
      · exact lt_of_le_of_ne (min_eq_right_iff.1 h.symm) hab.symm
      · exact absurd h (lt_irrefl _)
  rw [swap_mul_apply_of_fixed ha hb hca hcb]
  constructor
  · exact Or.inr
  · rintro (h | h)
    · rcases min_choice a b with h' | h' <;> rw [h'] at h
      · exact absurd h hca
      · exact absurd h hcb
    · exact h
private lemma involutionTerm_swap_mul {K : ι → ι → ℝ} (hK : ∀ x y, K x y = K y x) (i : Fin q → ι)
    {S : Finset (Fin q)} {a b : Fin q} {τ : Perm (Fin q)} (hab : a ≠ b) (hbS : b ∉ S)
    (ha : τ a = a) (hb : τ b = b) :
    involutionTerm K i (insert b S) (swap a b * τ) =
      -(MvPolynomial.C (K (i b) (i a)) * involutionTerm K i (S.erase a) τ) := by
  have ea : (swap a b * τ) a = b := by simp [Perm.mul_apply, ha]
  have eb : (swap a b * τ) b = a := by simp [Perm.mul_apply, hb]
  have hmin : min a b ∉ pairStarts τ := by
    simp only [pairStarts, Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
    rcases min_choice a b with h' | h' <;> rw [h']
    · exact ha.le
    · exact hb.le
  have hcard : (pairStarts (swap a b * τ)).card = (pairStarts τ).card + 1 := by
    rw [pairStarts_swap_mul hab ha hb, Finset.card_insert_of_notMem hmin]
  have hprod : ∏ c ∈ pairStarts (swap a b * τ), K (i c) (i ((swap a b * τ) c)) =
      K (i b) (i a) * ∏ c ∈ pairStarts τ, K (i c) (i (τ c)) := by
    rw [pairStarts_swap_mul hab ha hb, Finset.prod_insert hmin]
    congr 1
    · rcases min_choice a b with h' | h' <;> rw [h']
      · rw [ea, hK]
      · rw [eb]
    · refine Finset.prod_congr rfl fun c hc => ?_
      simp only [pairStarts, Finset.mem_filter, Finset.mem_univ, true_and] at hc
      have h1 : c ≠ a := fun h => by subst h; exact absurd hc (by rw [ha]; exact lt_irrefl _)
      have h2 : c ≠ b := fun h => by subst h; exact absurd hc (by rw [hb]; exact lt_irrefl _)
      rw [swap_mul_apply_of_fixed ha hb h1 h2]
  have hfil : (insert b S).filter (fun c => (swap a b * τ) c = c) =
      (S.erase a).filter (fun c => τ c = c) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
    by_cases h1 : c = a
    · subst h1
      simp [ea, hab.symm]
    by_cases h2 : c = b
    · subst h2
      simp [eb, hbS, hab]
    · rw [swap_mul_apply_of_fixed ha hb h1 h2]
      simp [h1, h2]
  unfold involutionTerm
  rw [hprod, hcard, hfil, pow_succ]
  have : MvPolynomial.C ((-1 : ℝ) ^ (pairStarts τ).card * -1 *
      (K (i b) (i a) * ∏ c ∈ pairStarts τ, K (i c) (i (τ c)))) =
      -(MvPolynomial.C (K (i b) (i a)) * MvPolynomial.C ((-1 : ℝ) ^ (pairStarts τ).card *
        ∏ c ∈ pairStarts τ, K (i c) (i (τ c))) : MvPolynomial ι ℝ) := by
    rw [← map_mul, ← map_neg]
    congr 1
    ring
  rw [this]
  ring
private lemma swap_mul_involutive {ρ : Perm (Fin q)} {a b : Fin q}
    (hc : ρ * swap a b = swap a b * ρ) (h : ρ * ρ = 1) : (swap a b * ρ) * (swap a b * ρ) = 1 := by
  calc (swap a b * ρ) * (swap a b * ρ) = swap a b * (ρ * swap a b) * ρ := by simp only [mul_assoc]
    _ = swap a b * (swap a b * ρ) * ρ := by rw [hc]
    _ = ρ * ρ := by rw [swap_mul_self_mul]
    _ = 1 := h
private lemma mem_involutionsOn {S : Finset (Fin q)} {σ : Perm (Fin q)} :
    σ ∈ involutionsOn S ↔ σ * σ = 1 ∧ ∀ a, a ∉ S → σ a = a := by
  simp [involutionsOn]
private lemma apply_apply_of_mul_self {σ : Perm (Fin q)} (h : σ * σ = 1) (a : Fin q) : σ (σ a) = a := by
  have := congrArg (fun ρ : Perm (Fin q) => ρ a) h
  simpa [Perm.mul_apply] using this
private lemma wickWord_insert {K : ι → ι → ℝ} (hK : ∀ x y, K x y = K y x) (i : Fin q → ι)
    {S : Finset (Fin q)} {b : Fin q} (hb : b ∉ S) :
    wickWord K i (insert b S) = X (i b) * wickWord K i S -
      ∑ a ∈ S, MvPolynomial.C (K (i b) (i a)) * wickWord K i (S.erase a) := by
  have hmaps : ∀ σ ∈ involutionsOn (insert b S), σ b ∈ insert b S := by
    intro σ hσ
    by_contra hn
    obtain ⟨h1, h2⟩ := mem_involutionsOn.1 hσ
    have h3 := h2 _ hn
    rw [apply_apply_of_mul_self h1] at h3
    rw [← h3] at hn
    exact hn (Finset.mem_insert_self _ _)
  unfold wickWord
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.sum_insert hb]
  have h1 : ∑ σ ∈ (involutionsOn (insert b S)).filter (fun σ => σ b = b), involutionTerm K i (insert b S) σ =
      X (i b) * ∑ σ ∈ involutionsOn S, involutionTerm K i S σ := by
    have e : (involutionsOn (insert b S)).filter (fun σ => σ b = b) = involutionsOn S := by
      ext σ
      simp only [Finset.mem_filter, mem_involutionsOn, Finset.mem_insert, not_or]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨h1, fun a ha => ?_⟩
        by_cases hab : a = b
        · rw [hab, h3]
        · exact h2 a ⟨hab, ha⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, fun a ha => h2 a ha.2⟩, h2 b hb⟩
    rw [e, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ hσ => ?_
    have hσb : σ b = b := (mem_involutionsOn.1 hσ).2 b hb
    unfold involutionTerm
    rw [Finset.filter_insert, if_pos hσb, Finset.prod_insert (by simp [hb])]
    ring
  have h2 : ∀ a ∈ S, ∑ σ ∈ (involutionsOn (insert b S)).filter (fun σ => σ b = a),
      involutionTerm K i (insert b S) σ =
      -(MvPolynomial.C (K (i b) (i a)) * ∑ τ ∈ involutionsOn (S.erase a), involutionTerm K i (S.erase a) τ) := by
    intro a haS
    have hab : a ≠ b := fun h => hb (h ▸ haS)
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_nbij' (fun σ => swap a b * σ) (fun τ => swap a b * τ) ?_ ?_ ?_ ?_ ?_
    · intro σ hσ
      obtain ⟨hσ1, hσ3⟩ := Finset.mem_filter.1 hσ
      obtain ⟨h1, h2⟩ := mem_involutionsOn.1 hσ1
      have hσa : σ a = b := by rw [← hσ3, apply_apply_of_mul_self h1]
      have ea : (swap a b * σ) a = a := by simp [Perm.mul_apply, hσa]
      have eb : (swap a b * σ) b = b := by simp [Perm.mul_apply, hσ3]
      refine mem_involutionsOn.2 ⟨swap_mul_involutive ?_ h1, fun c hc => ?_⟩
      · rw [mul_swap_eq_swap_mul, hσa, hσ3, swap_comm]
      · by_cases h3 : c = a
        · rw [h3, ea]
        by_cases h4 : c = b
        · rw [h4, eb]
        · have h5 : c ∉ S := fun h => hc (Finset.mem_erase.2 ⟨h3, h⟩)
          have h6 : σ c = c := h2 c (by simp [h4, h5])
          rw [Perm.mul_apply, h6, swap_apply_of_ne_of_ne h3 h4]
    · intro τ hτ
      obtain ⟨h1, h2⟩ := mem_involutionsOn.1 hτ
      have ha : τ a = a := h2 a (by simp)
      have hb' : τ b = b := h2 b (by simp [hb])
      refine Finset.mem_filter.2 ⟨mem_involutionsOn.2 ⟨swap_mul_involutive ?_ h1, fun c hc => ?_⟩, ?_⟩
      · rw [mul_swap_eq_swap_mul, ha, hb']
      · simp only [Finset.mem_insert, not_or] at hc
        have h3 : c ≠ a := fun h => hc.2 (h ▸ haS)
        rw [swap_mul_apply_of_fixed ha hb' h3 hc.1]
        exact h2 c fun h => hc.2 (Finset.mem_of_mem_erase h)
      · simp [Perm.mul_apply, hb']
    · intro σ _
      exact swap_mul_self_mul _ _ _
    · intro τ _
      exact swap_mul_self_mul _ _ _
    · intro σ hσ
      obtain ⟨hσ1, hσ3⟩ := Finset.mem_filter.1 hσ
      obtain ⟨h1, h2⟩ := mem_involutionsOn.1 hσ1
      have hσa : σ a = b := by rw [← hσ3, apply_apply_of_mul_self h1]
      have ea : (swap a b * σ) a = a := by simp [Perm.mul_apply, hσa]
      have eb : (swap a b * σ) b = b := by simp [Perm.mul_apply, hσ3]
      have := involutionTerm_swap_mul hK i (S := S) hab hb ea eb
      rwa [swap_mul_self_mul] at this
  rw [h1, Finset.sum_congr rfl h2, Finset.sum_neg_distrib]
  ring
private lemma pderiv_prod_X (i : Fin q → ι) (k : ι) (F : Finset (Fin q)) :
    pderiv k (∏ a ∈ F, (X (i a) : MvPolynomial ι ℝ)) =
      ∑ a ∈ F, if i a = k then ∏ c ∈ F.erase a, (X (i c) : MvPolynomial ι ℝ) else 0 := by
  induction F using Finset.induction_on with
  | empty => simp
  | insert x F hx ih =>
    rw [Finset.prod_insert hx, Derivation.leibniz, ih, Finset.sum_insert hx, smul_eq_mul, smul_eq_mul,
      pderiv_X, Finset.erase_insert hx, add_comm, Finset.mul_sum]
    congr 1
    · by_cases h : i x = k
      · simp [h, Pi.single_apply]
      · simp [h, Pi.single_apply, Ne.symm h]
    · refine Finset.sum_congr rfl fun a ha => ?_
      have hax : a ≠ x := fun h => hx (h ▸ ha)
      rw [Finset.erase_insert_of_ne hax.symm, Finset.prod_insert (by simp [hx])]
      split_ifs <;> simp
private lemma pderiv_wickWord (K : ι → ι → ℝ) (i : Fin q → ι) (k : ι) (S : Finset (Fin q)) :
    pderiv k (wickWord K i S) = ∑ a ∈ S, if i a = k then wickWord K i (S.erase a) else 0 := by
  have h1 : ∀ σ : Perm (Fin q), pderiv k (involutionTerm K i S σ) =
      ∑ a ∈ S.filter (fun a => σ a = a), if i a = k then involutionTerm K i (S.erase a) σ else 0 := by
    intro σ
    unfold involutionTerm
    rw [pderiv_C_mul, pderiv_prod_X, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have : (S.filter fun c => σ c = c).erase a = (S.erase a).filter fun c => σ c = c := by
      ext c
      simp only [Finset.mem_erase, Finset.mem_filter]
      tauto
    rw [this]
    split_ifs <;> simp
  unfold wickWord
  rw [map_sum]
  simp only [h1]
  rw [Finset.sum_comm' (s' := fun a => (involutionsOn S).filter fun σ => σ a = a) (t' := S)
    (by intro σ a; simp only [Finset.mem_filter]; tauto)]
  refine Finset.sum_congr rfl fun a ha => ?_
  have e : (involutionsOn S).filter (fun σ => σ a = a) = involutionsOn (S.erase a) := by
    ext σ
    simp only [Finset.mem_filter, mem_involutionsOn, Finset.mem_erase, not_and]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, fun c hc => ?_⟩
      by_cases h : c = a
      · rw [h, h3]
      · exact h2 c (hc h)
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, fun c hc => h2 c fun _ => hc⟩, h2 a fun h => absurd rfl h⟩
  rw [e]
  split_ifs <;> simp
private lemma stein_wickWord_mul {K : ι → ι → ℝ} (hK : ∀ x y, K x y = K y x)
    (L : MvPolynomial ι ℝ →ₗ[ℝ] ℝ)
    (hS : ∀ j P, L (X j * P) = ∑ k, K j k * L (pderiv k P)) (i : Fin q → ι)
    {S : Finset (Fin q)} {b : Fin q} (hb : b ∉ S) (G : MvPolynomial ι ℝ) :
    L (wickWord K i (insert b S) * G) = ∑ k, K (i b) k * L (wickWord K i S * pderiv k G) := by
  rw [wickWord_insert hK i hb, sub_mul, map_sub, mul_assoc, hS]
  have h1 : ∀ k, L (pderiv k (wickWord K i S * G)) =
      L (wickWord K i S * pderiv k G) +
        ∑ a ∈ S, if i a = k then L (G * wickWord K i (S.erase a)) else 0 := by
    intro k
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, pderiv_wickWord, Finset.mul_sum, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs <;> simp
  simp only [h1, mul_add, Finset.sum_add_distrib]
  have h2 : ∑ k, K (i b) k * ∑ a ∈ S, (if i a = k then L (G * wickWord K i (S.erase a)) else 0) =
      L ((∑ a ∈ S, MvPolynomial.C (K (i b) (i a)) * wickWord K i (S.erase a)) * G) := by
    rw [Finset.sum_mul, map_sum]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [mul_assoc, MvPolynomial.C_mul', map_smul, smul_eq_mul, mul_comm G]
  rw [h2]
  ring
private def agreeOff (S : Finset (Fin q)) (u : Fin q → ι) : Finset (Fin q → ι) :=
  Finset.univ.filter fun i => ∀ a, a ∉ S → i a = u a
private def slotWick (K : ι → ι → ℝ) (A : (Fin q → ι) → ℝ) (S : Finset (Fin q)) (u : Fin q → ι) :
    MvPolynomial ι ℝ :=
  ∑ i ∈ agreeOff S u, MvPolynomial.C (A i) * wickWord K i S
private def slotSquareSum (K : ι → ι → ℝ) (A : (Fin q → ι) → ℝ) (S : Finset (Fin q)) : MvPolynomial ι ℝ :=
  ∑ u, slotWick K A S u ^ 2
private lemma sum_agreeOff_insert {M : Type} [AddCommMonoid M] (f : (Fin q → ι) → M) {S : Finset (Fin q)}
    {b : Fin q} (hb : b ∉ S) (u : Fin q → ι) :
    ∑ i ∈ agreeOff (insert b S) u, f i = ∑ m, ∑ i ∈ agreeOff S (Function.update u b m), f i := by
  rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.univ) (g := fun i : Fin q → ι => i b)
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr ?_ fun _ _ => rfl
  ext i
  simp only [agreeOff, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, not_or]
  constructor
  · rintro ⟨h1, h2⟩ a ha
    by_cases hab : a = b
    · subst hab
      simp [h2]
    · rw [Function.update_of_ne hab]
      exact h1 a ⟨hab, ha⟩
  · intro h
    refine ⟨fun a ha => ?_, ?_⟩
    · rw [h a ha.2, Function.update_of_ne ha.1]
    · rw [h b hb, Function.update_self]
private lemma apply_of_mem_agreeOff_update {S : Finset (Fin q)} {b : Fin q} (hb : b ∉ S) {u : Fin q → ι}
    {m : ι} {i : Fin q → ι} (hi : i ∈ agreeOff S (Function.update u b m)) : i b = m := by
  simp only [agreeOff, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rw [hi b hb, Function.update_self]
private lemma stein_slotWick_mul {K : ι → ι → ℝ} (hK : ∀ x y, K x y = K y x)
    (L : MvPolynomial ι ℝ →ₗ[ℝ] ℝ)
    (hS : ∀ j P, L (X j * P) = ∑ k, K j k * L (pderiv k P)) (A : (Fin q → ι) → ℝ)
    {S : Finset (Fin q)} {b : Fin q} (hb : b ∉ S) (u : Fin q → ι) (G : MvPolynomial ι ℝ) :
    L (slotWick K A (insert b S) u * G) =
      ∑ m, ∑ k, K m k * L (slotWick K A S (Function.update u b m) * pderiv k G) := by
  unfold slotWick
  rw [sum_agreeOff_insert _ hb, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_mul, map_sum]
  simp only [Finset.sum_mul, map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [mul_assoc, MvPolynomial.C_mul', map_smul, smul_eq_mul, stein_wickWord_mul hK L hS i hb,
    apply_of_mem_agreeOff_update hb hi, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_assoc, MvPolynomial.C_mul', map_smul, smul_eq_mul]
  ring
private lemma pderiv_slotWick (K : ι → ι → ℝ) (A : (Fin q → ι) → ℝ) (S : Finset (Fin q))
    (u : Fin q → ι) (k : ι) :
    pderiv k (slotWick K A S u) = ∑ a ∈ S, slotWick K A (S.erase a) (Function.update u a k) := by
  unfold slotWick
  rw [map_sum]
  simp only [pderiv_C_mul, pderiv_wickWord, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a ha => ?_
  simp only [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext i
  simp only [agreeOff, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, not_and]
  constructor
  · rintro ⟨h1, h2⟩ c hc
    by_cases hca : c = a
    · subst hca
      simp [h2]
    · rw [Function.update_of_ne hca]
      exact h1 c (hc hca)
  · intro h
    refine ⟨fun c hc => ?_, ?_⟩
    · have hca : c ≠ a := fun h' => hc (h' ▸ ha)
      rw [h c fun _ => hc, Function.update_of_ne hca]
    · rw [h a fun h' => absurd rfl h', Function.update_self]
private lemma young_pow_mul (n : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ((n : ℝ) + 1) * (x ^ n * y) ≤ n * x ^ (n + 1) + y ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : 0 ≤ (x ^ (n + 1) - y ^ (n + 1)) * (x - y) := by
      rcases le_total x y with h | h
      · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 (pow_le_pow_left₀ hx h _)) (sub_nonpos.2 h)
      · exact mul_nonneg (sub_nonneg.2 (pow_le_pow_left₀ hy h _)) (sub_nonneg.2 h)
    have h2 := mul_le_mul_of_nonneg_left ih hx
    push_cast
    linear_combination h2 + h1
private lemma bilinear_le_of_le_form {K : ι → ι → ℝ} {lam : ℝ} (hK : ∀ x y, K x y = K y x)
    (hpsd : ∀ t : ι → ℝ, 0 ≤ ∑ i, ∑ j, t i * K i j * t j)
    (hle : ∀ t : ι → ℝ, ∑ i, ∑ j, t i * K i j * t j ≤ lam * ∑ i, t i ^ 2) (x y : ι → ℝ) :
    ∑ m, ∑ k, K m k * (x m * y k) ≤ lam / 2 * (∑ m, x m ^ 2 + ∑ k, y k ^ 2) := by
  have h0 := hpsd (x - y)
  have hx := hle x
  have hy := hle y
  have e2 : ∑ i, ∑ j, y i * K i j * x j = ∑ m, ∑ k, K m k * (x m * y k) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => ?_
    rw [hK k m]
    ring
  have e3 : ∑ i, ∑ j, x i * K i j * y j = ∑ m, ∑ k, K m k * (x m * y k) :=
    Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => by ring
  have expand : ∀ i j, (x - y) i * K i j * (x - y) j =
      x i * K i j * x j + y i * K i j * y j - x i * K i j * y j - y i * K i j * x j := by
    intro i j
    simp only [Pi.sub_apply]
    ring
  simp only [expand, Finset.sum_sub_distrib, Finset.sum_add_distrib] at h0
  rw [e2, e3] at h0
  linarith
private lemma paired_sum_le {K : ι → ι → ℝ} {lam : ℝ} (hlam : 0 ≤ lam)
    (hform : ∀ x y : ι → ℝ, ∑ m, ∑ k, K m k * (x m * y k) ≤ lam / 2 * (∑ m, x m ^ 2 + ∑ k, y k ^ 2))
    {U : Type} [Fintype U] (f : U → ℝ) (t d : U → ι → ℝ) (n : ℕ) :
    ∑ u, ∑ m, ∑ k, K m k * (t u m * (f u * ((n : ℝ) * (∑ v, f v ^ 2) ^ (n - 1) * ∑ v, 2 * f v * d v k) +
        (∑ v, f v ^ 2) ^ n * d u k)) ≤
      (2 * n + 1) * lam * (∑ v, f v ^ 2) ^ n * ((∑ u, ∑ m, t u m ^ 2 + ∑ u, ∑ k, d u k ^ 2) / 2) := by
  set Q := ∑ v, f v ^ 2 with hQ
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun _ _ => sq_nonneg _
  set a := ∑ u, ∑ m, t u m ^ 2 with ha
  set b := ∑ u, ∑ k, d u k ^ 2 with hb
  let x : ι → ℝ := fun m => ∑ u, f u * t u m
  let y : ι → ℝ := fun k => ∑ u, f u * d u k
  have hE : ∀ k, ∑ v, 2 * f v * d v k = 2 * y k := by
    intro k
    simp only [y, Finset.mul_sum, mul_assoc]
  have hsplit : ∑ u, ∑ m, ∑ k, K m k * (t u m * (f u * ((n : ℝ) * Q ^ (n - 1) * ∑ v, 2 * f v * d v k) +
      Q ^ n * d u k)) = (2 * n * Q ^ (n - 1)) * ∑ m, ∑ k, K m k * (x m * y k) +
        Q ^ n * ∑ u, ∑ m, ∑ k, K m k * (t u m * d u k) := by
    simp only [hE]
    have term : ∀ u m k, K m k * (t u m * (f u * ((n : ℝ) * Q ^ (n - 1) * (2 * y k)) + Q ^ n * d u k)) =
        (2 * n * Q ^ (n - 1)) * (K m k * ((f u * t u m) * y k)) + Q ^ n * (K m k * (t u m * d u k)) := by
      intro u m k
      ring
    simp only [term, Finset.sum_add_distrib, ← Finset.mul_sum]
    congr 2
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [x, Finset.sum_mul, Finset.mul_sum]
  rw [hsplit]
  have hxs : ∑ m, x m ^ 2 ≤ Q * a := by
    have : ∀ m, x m ^ 2 ≤ Q * ∑ u, t u m ^ 2 := fun m => Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    calc ∑ m, x m ^ 2 ≤ ∑ m, Q * ∑ u, t u m ^ 2 := Finset.sum_le_sum fun m _ => this m
      _ = Q * a := by rw [← Finset.mul_sum, Finset.sum_comm]
  have hys : ∑ k, y k ^ 2 ≤ Q * b := by
    have : ∀ k, y k ^ 2 ≤ Q * ∑ u, d u k ^ 2 := fun k => Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    calc ∑ k, y k ^ 2 ≤ ∑ k, Q * ∑ u, d u k ^ 2 := Finset.sum_le_sum fun k _ => this k
      _ = Q * b := by rw [← Finset.mul_sum, Finset.sum_comm]
  have h1 : ∑ m, ∑ k, K m k * (x m * y k) ≤ lam / 2 * (Q * a + Q * b) :=
    (hform x y).trans (mul_le_mul_of_nonneg_left (add_le_add hxs hys) (by positivity))
  have h2 : ∑ u, ∑ m, ∑ k, K m k * (t u m * d u k) ≤ lam / 2 * (a + b) := by
    calc ∑ u, ∑ m, ∑ k, K m k * (t u m * d u k)
        ≤ ∑ u, lam / 2 * (∑ m, t u m ^ 2 + ∑ k, d u k ^ 2) :=
          Finset.sum_le_sum fun u _ => hform (t u) (d u)
      _ = lam / 2 * (a + b) := by rw [← Finset.mul_sum, Finset.sum_add_distrib]
  have h3 : (2 * n * Q ^ (n - 1)) * ∑ m, ∑ k, K m k * (x m * y k) ≤ n * lam * Q ^ n * (a + b) := by
    cases n with
    | zero => simp
    | succ n =>
      have := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2 * ((n + 1 : ℕ) : ℝ) * Q ^ n by positivity)
      simp only [add_tsub_cancel_right]
      refine this.trans (le_of_eq ?_)
      ring
  have h4 := mul_le_mul_of_nonneg_left h2 (pow_nonneg hQ0 n)
  calc _ ≤ n * lam * Q ^ n * (a + b) + Q ^ n * (lam / 2 * (a + b)) := add_le_add h3 h4
    _ = _ := by ring
private lemma sum_sum_update (b : Fin q) (f : (Fin q → ι) → ℝ) :
    ∑ u, ∑ m, f (Function.update u b m) = (Fintype.card ι : ℝ) * ∑ u, f u := by
  let e : (Fin q → ι) × ι ≃ (Fin q → ι) × ι :=
    { toFun := fun p => (Function.update p.1 b p.2, p.1 b)
      invFun := fun p => (Function.update p.1 b p.2, p.1 b)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  calc ∑ u, ∑ m, f (Function.update u b m) = ∑ p : (Fin q → ι) × ι, f (e p).1 := by
        rw [Fintype.sum_prod_type]
        rfl
    _ = ∑ p : (Fin q → ι) × ι, f p.1 := Equiv.sum_comp e (fun p => f p.1)
    _ = _ := by
        rw [Fintype.sum_prod_type]
        simp [Finset.mul_sum]
private structure IsSteinFunctional (K : ι → ι → ℝ) (lam : ℝ) (L : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) : Prop where
  symm : ∀ x y, K x y = K y x
  psd : ∀ t : ι → ℝ, 0 ≤ ∑ i, ∑ j, t i * K i j * t j
  le : ∀ t : ι → ℝ, ∑ i, ∑ j, t i * K i j * t j ≤ lam * ∑ i, t i ^ 2
  lam0 : 0 ≤ lam
  stein : ∀ j P, L (X j * P) = ∑ k, K j k * L (pderiv k P)
  pos : ∀ P, (∀ ξ, 0 ≤ eval ξ P) → 0 ≤ L P
  one : L 1 = 1
private lemma apply_C_mul (L : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) (c : ℝ) (P : MvPolynomial ι ℝ) :
    L (MvPolynomial.C c * P) = c * L P := by
  rw [MvPolynomial.C_mul', map_smul, smul_eq_mul]
private def removedGradSum (K : ι → ι → ℝ) (A : (Fin q → ι) → ℝ) (S : Finset (Fin q)) (b : Fin q) :
    MvPolynomial ι ℝ :=
  MvPolynomial.C (1 / 2) * (∑ u, ∑ m, slotWick K A S (Function.update u b m) ^ 2 +
    ∑ u, ∑ k : ι, pderiv k (slotWick K A (insert b S) u) ^ 2)
private lemma eval_slotSquareSum (K : ι → ι → ℝ) (A : (Fin q → ι) → ℝ) (S : Finset (Fin q)) (ξ : ι → ℝ) :
    eval ξ (slotSquareSum K A S) = ∑ u, eval ξ (slotWick K A S u) ^ 2 := by
  simp [slotSquareSum, map_sum, map_pow]
private lemma eval_pderiv_slotSquareSum (K : ι → ι → ℝ) (A : (Fin q → ι) → ℝ) (S : Finset (Fin q)) (k : ι)
    (ξ : ι → ℝ) :
    eval ξ (pderiv k (slotSquareSum K A S)) =
      ∑ v, 2 * eval ξ (slotWick K A S v) * eval ξ (pderiv k (slotWick K A S v)) := by
  unfold slotSquareSum
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [pderiv_pow]
  simp
private def pairedGradient (K : ι → ι → ℝ) (A : (Fin q → ι) → ℝ) (S : Finset (Fin q)) (b : Fin q) (n : ℕ) :
    MvPolynomial ι ℝ :=
  ∑ u, ∑ m, ∑ k, MvPolynomial.C (K m k) * (slotWick K A S (Function.update u b m) *
    pderiv k (slotWick K A (insert b S) u * slotSquareSum K A (insert b S) ^ n))
private lemma apply_slotSquareSum_pow_eq_pairedGradient {K : ι → ι → ℝ} {lam : ℝ}
    {L : MvPolynomial ι ℝ →ₗ[ℝ] ℝ} (h : IsSteinFunctional K lam L) (A : (Fin q → ι) → ℝ)
    {S : Finset (Fin q)} {b : Fin q} (hb : b ∉ S) (n : ℕ) :
    L (slotSquareSum K A (insert b S) ^ (n + 1)) = L (pairedGradient K A S b n) := by
  have e : slotSquareSum K A (insert b S) ^ (n + 1) =
      ∑ u, slotWick K A (insert b S) u * (slotWick K A (insert b S) u * slotSquareSum K A (insert b S) ^ n) := by
    calc slotSquareSum K A (insert b S) ^ (n + 1) =
          slotSquareSum K A (insert b S) * slotSquareSum K A (insert b S) ^ n := pow_succ' _ _
      _ = (∑ u, slotWick K A (insert b S) u ^ 2) * slotSquareSum K A (insert b S) ^ n := rfl
      _ = _ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun u _ => ?_
        ring
  rw [e, map_sum]
  simp only [stein_slotWick_mul h.symm L h.stein A hb]
  simp only [pairedGradient, map_sum, apply_C_mul]
private lemma eval_pairedGradient_le {K : ι → ι → ℝ} {lam : ℝ} {L : MvPolynomial ι ℝ →ₗ[ℝ] ℝ}
    (h : IsSteinFunctional K lam L) (A : (Fin q → ι) → ℝ) (S : Finset (Fin q)) (b : Fin q)
    (n : ℕ) (ξ : ι → ℝ) :
    eval ξ (pairedGradient K A S b n) ≤
      (2 * n + 1) * lam * eval ξ (slotSquareSum K A (insert b S)) ^ n * eval ξ (removedGradSum K A S b) := by
  have hform := bilinear_le_of_le_form (K := K) (lam := lam) h.symm h.psd h.le
  have hd : ∀ u k, eval ξ (pderiv k (slotWick K A (insert b S) u * slotSquareSum K A (insert b S) ^ n)) =
      eval ξ (slotWick K A (insert b S) u) * ((n : ℝ) * eval ξ (slotSquareSum K A (insert b S)) ^ (n - 1) *
        ∑ v, 2 * eval ξ (slotWick K A (insert b S) v) * eval ξ (pderiv k (slotWick K A (insert b S) v))) +
      eval ξ (slotSquareSum K A (insert b S)) ^ n * eval ξ (pderiv k (slotWick K A (insert b S) u)) := by
    intro u k
    rw [Derivation.leibniz, pderiv_pow]
    simp only [smul_eq_mul, map_add, map_mul, map_pow, map_natCast, eval_pderiv_slotSquareSum]
  have hb' := paired_sum_le h.lam0 hform (fun u => eval ξ (slotWick K A (insert b S) u))
    (fun u m => eval ξ (slotWick K A S (Function.update u b m)))
    (fun u k => eval ξ (pderiv k (slotWick K A (insert b S) u))) n
  have eR : eval ξ (pairedGradient K A S b n) =
      ∑ u, ∑ m, ∑ k, K m k * (eval ξ (slotWick K A S (Function.update u b m)) *
        eval ξ (pderiv k (slotWick K A (insert b S) u * slotSquareSum K A (insert b S) ^ n))) := by
    simp only [pairedGradient, map_sum, map_mul, eval_C]
  have eY : eval ξ (removedGradSum K A S b) =
      (∑ u, ∑ m, eval ξ (slotWick K A S (Function.update u b m)) ^ 2 +
        ∑ u, ∑ k, eval ξ (pderiv k (slotWick K A (insert b S) u)) ^ 2) / 2 := by
    simp only [removedGradSum, map_sum, map_mul, map_add, map_pow, eval_C]
    ring
  rw [eR, eY]
  simp only [hd]
  rw [eval_slotSquareSum]
  exact hb'
private lemma removedGradSum_nonneg (K : ι → ι → ℝ) (A : (Fin q → ι) → ℝ) (S : Finset (Fin q)) (b : Fin q)
    (ξ : ι → ℝ) : 0 ≤ eval ξ (removedGradSum K A S b) := by
  simp only [removedGradSum, map_sum, map_mul, map_add, map_pow, eval_C]
  have h1 : 0 ≤ ∑ u, ∑ m, eval ξ (slotWick K A S (Function.update u b m)) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h2 : 0 ≤ ∑ u, ∑ k, eval ξ (pderiv k (slotWick K A (insert b S) u)) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  exact mul_nonneg (by norm_num) (add_nonneg h1 h2)
private lemma slotSquareSum_nonneg (K : ι → ι → ℝ) (A : (Fin q → ι) → ℝ) (S : Finset (Fin q)) (ξ : ι → ℝ) :
    0 ≤ eval ξ (slotSquareSum K A S) := by
  rw [eval_slotSquareSum]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _
private lemma apply_slotSquareSum_insert_pow_le {K : ι → ι → ℝ} {lam : ℝ} {L : MvPolynomial ι ℝ →ₗ[ℝ] ℝ}
    (h : IsSteinFunctional K lam L) (A : (Fin q → ι) → ℝ) {S : Finset (Fin q)} {b : Fin q} (hb : b ∉ S)
    (n : ℕ) :
    L (slotSquareSum K A (insert b S) ^ (n + 1)) ≤
      ((2 * n + 1) * lam) ^ (n + 1) * L (removedGradSum K A S b ^ (n + 1)) := by
  have hc0 : 0 ≤ (2 * (n : ℝ) + 1) * lam := mul_nonneg (by positivity) h.lam0
  have hP := h.pos (MvPolynomial.C (n : ℝ) * slotSquareSum K A (insert b S) ^ (n + 1) +
      MvPolynomial.C (((2 * (n : ℝ) + 1) * lam) ^ (n + 1)) * removedGradSum K A S b ^ (n + 1) -
      MvPolynomial.C ((n : ℝ) + 1) * pairedGradient K A S b n) (by
    intro ξ
    simp only [map_sub, map_add, map_mul, map_pow, eval_C]
    have h1 := young_pow_mul n (slotSquareSum_nonneg K A (insert b S) ξ)
      (mul_nonneg hc0 (removedGradSum_nonneg K A S b ξ))
    have h2 := mul_le_mul_of_nonneg_left (eval_pairedGradient_le h A S b n ξ)
      (show 0 ≤ (n : ℝ) + 1 by positivity)
    have h3 : ((n : ℝ) + 1) * ((2 * n + 1) * lam * eval ξ (slotSquareSum K A (insert b S)) ^ n *
        eval ξ (removedGradSum K A S b)) =
        ((n : ℝ) + 1) * (eval ξ (slotSquareSum K A (insert b S)) ^ n *
          ((2 * n + 1) * lam * eval ξ (removedGradSum K A S b))) := by
      ring
    rw [mul_pow] at h1
    linarith)
  rw [map_sub, map_add, apply_C_mul, apply_C_mul, apply_C_mul,
    ← apply_slotSquareSum_pow_eq_pairedGradient h A hb n] at hP
  linarith
private lemma half_add_pow_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (n : ℕ) :
    ((x + y) / 2) ^ (n + 1) ≤ (x ^ (n + 1) + y ^ (n + 1)) / 2 := by
  have h := add_pow_le hx hy (n + 1)
  simp only [add_tsub_cancel_right] at h
  rw [div_pow, pow_succ (2 : ℝ) n]
  calc (x + y) ^ (n + 1) / (2 ^ n * 2) ≤ 2 ^ n * (x ^ (n + 1) + y ^ (n + 1)) / (2 ^ n * 2) := by gcongr
    _ = _ := by field_simp
private lemma removedGradSum_pow_le (K : ι → ι → ℝ) (A : (Fin q → ι) → ℝ) {S : Finset (Fin q)} {b : Fin q}
    (hb : b ∉ S) (n : ℕ) (ξ : ι → ℝ) :
    eval ξ (removedGradSum K A S b) ^ (n + 1) ≤
      1 / 2 * (Fintype.card ι : ℝ) ^ (n + 1) * eval ξ (slotSquareSum K A S) ^ (n + 1) +
      1 / 2 * (((S.card : ℝ) + 1) * Fintype.card ι) ^ (n + 1) * ((S.card : ℝ) + 1) ^ n *
        ∑ a ∈ insert b S, eval ξ (slotSquareSum K A ((insert b S).erase a)) ^ (n + 1) := by
  set s1 : ℝ := (S.card : ℝ) + 1 with hs1
  set N : ℝ := ((Fintype.card ι : ℕ) : ℝ) with hN
  have hs0 : 0 ≤ s1 := by positivity
  have hN0 : 0 ≤ N := by positivity
  have hcard : ((insert b S).card : ℝ) = s1 := by
    rw [Finset.card_insert_of_notMem hb]
    push_cast
    rfl
  have ea : ∑ u, ∑ m, eval ξ (slotWick K A S (Function.update u b m)) ^ 2 = N * eval ξ (slotSquareSum K A S) := by
    rw [eval_slotSquareSum]
    exact sum_sum_update b fun u => eval ξ (slotWick K A S u) ^ 2
  set W : ℝ := ∑ a ∈ insert b S, eval ξ (slotSquareSum K A ((insert b S).erase a)) with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun _ _ => slotSquareSum_nonneg _ _ _ _
  have eb : ∑ u, ∑ k, eval ξ (pderiv k (slotWick K A (insert b S) u)) ^ 2 ≤ s1 * N * W := by
    have h1 : ∀ u k, eval ξ (pderiv k (slotWick K A (insert b S) u)) ^ 2 ≤
        s1 * ∑ a ∈ insert b S, eval ξ (slotWick K A ((insert b S).erase a) (Function.update u a k)) ^ 2 := by
      intro u k
      rw [pderiv_slotWick, map_sum, ← hcard]
      exact sq_sum_le_card_mul_sum_sq
    calc ∑ u, ∑ k, eval ξ (pderiv k (slotWick K A (insert b S) u)) ^ 2
        ≤ ∑ u, ∑ k, s1 * ∑ a ∈ insert b S,
            eval ξ (slotWick K A ((insert b S).erase a) (Function.update u a k)) ^ 2 :=
          Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun k _ => h1 u k
      _ = s1 * ∑ a ∈ insert b S, ∑ u, ∑ k,
            eval ξ (slotWick K A ((insert b S).erase a) (Function.update u a k)) ^ 2 := by
          simp only [← Finset.mul_sum]
          congr 1
          have hsw : ∀ u : Fin q → ι, ∑ k : ι, ∑ a ∈ insert b S,
              eval ξ (slotWick K A ((insert b S).erase a) (Function.update u a k)) ^ 2 =
              ∑ a ∈ insert b S, ∑ k : ι,
                eval ξ (slotWick K A ((insert b S).erase a) (Function.update u a k)) ^ 2 :=
            fun u => Finset.sum_comm
          simp only [hsw]
          exact Finset.sum_comm
      _ = s1 * N * W := by
          rw [hW, mul_assoc, Finset.mul_sum (a := N)]
          congr 1
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [eval_slotSquareSum]
          exact sum_sum_update a fun u => eval ξ (slotWick K A ((insert b S).erase a) u) ^ 2
  have eY : eval ξ (removedGradSum K A S b) = (N * eval ξ (slotSquareSum K A S) +
      ∑ u, ∑ k, eval ξ (pderiv k (slotWick K A (insert b S) u)) ^ 2) / 2 := by
    rw [← ea]
    simp only [removedGradSum, map_sum, map_mul, map_add, map_pow, eval_C]
    ring
  have hQ0 := slotSquareSum_nonneg K A S ξ
  have hy : eval ξ (removedGradSum K A S b) ≤ (N * eval ξ (slotSquareSum K A S) + s1 * N * W) / 2 := by
    rw [eY]
    linarith
  have h2 := pow_le_pow_left₀ (removedGradSum_nonneg K A S b ξ) hy (n + 1)
  have h3 := half_add_pow_le (mul_nonneg hN0 hQ0) (mul_nonneg (mul_nonneg hs0 hN0) hW0) n
  have h4 : W ^ (n + 1) ≤
      s1 ^ n * ∑ a ∈ insert b S, eval ξ (slotSquareSum K A ((insert b S).erase a)) ^ (n + 1) := by
    rw [← hcard]
    exact pow_sum_le_card_mul_sum_pow (fun _ _ => slotSquareSum_nonneg _ _ _ _) n
  have h5 := mul_le_mul_of_nonneg_left h4 (show 0 ≤ 1 / 2 * (s1 * N) ^ (n + 1) by positivity)
  rw [mul_pow N, mul_pow (s1 * N)] at h3
  calc _ ≤ _ := h2.trans h3
    _ ≤ _ := by linarith
private lemma apply_removedGradSum_pow_le {K : ι → ι → ℝ} {lam : ℝ} {L : MvPolynomial ι ℝ →ₗ[ℝ] ℝ}
    (h : IsSteinFunctional K lam L) (A : (Fin q → ι) → ℝ) {S : Finset (Fin q)} {b : Fin q} (hb : b ∉ S)
    (n : ℕ) {β : ℝ} (hβ : 0 ≤ β)
    (hQ : ∀ T : Finset (Fin q), T.card = S.card → L (slotSquareSum K A T ^ (n + 1)) ≤ β ^ (n + 1)) :
    L (removedGradSum K A S b ^ (n + 1)) ≤ (((S.card : ℝ) + 1) ^ 2 * Fintype.card ι * β) ^ (n + 1) := by
  set s1 : ℝ := (S.card : ℝ) + 1 with hs1
  set N : ℝ := ((Fintype.card ι : ℕ) : ℝ) with hN
  have hs1' : 1 ≤ s1 := by
    rw [hs1]
    have : (0 : ℝ) ≤ S.card := by positivity
    linarith
  have hP := h.pos (MvPolynomial.C (1 / 2 * N ^ (n + 1)) * slotSquareSum K A S ^ (n + 1) +
      MvPolynomial.C (1 / 2 * (s1 * N) ^ (n + 1) * s1 ^ n) *
        ∑ a ∈ insert b S, slotSquareSum K A ((insert b S).erase a) ^ (n + 1) -
        removedGradSum K A S b ^ (n + 1)) (by
    intro ξ
    have := removedGradSum_pow_le K A hb n ξ
    simp only [map_sub, map_add, map_mul, map_pow, map_sum, eval_C]
    linarith)
  rw [map_sub, map_add, apply_C_mul, apply_C_mul, map_sum] at hP
  have h1 := hQ S rfl
  have h2 : ∑ a ∈ insert b S, L (slotSquareSum K A ((insert b S).erase a) ^ (n + 1)) ≤ s1 * β ^ (n + 1) := by
    calc _ ≤ ∑ a ∈ insert b S, β ^ (n + 1) := Finset.sum_le_sum fun a ha => hQ _ (by
          rw [Finset.card_erase_of_mem ha, Finset.card_insert_of_notMem hb]
          rfl)
      _ = s1 * β ^ (n + 1) := by
          rw [Finset.sum_const, Finset.card_insert_of_notMem hb, nsmul_eq_mul]
          push_cast
          rfl
  have h3 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 1 / 2 * N ^ (n + 1) by positivity)
  have h4 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 1 / 2 * (s1 * N) ^ (n + 1) * s1 ^ n by positivity)
  have hPP : 1 ≤ s1 ^ (n + 1) * s1 ^ (n + 1) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hs1') (one_le_pow₀ hs1')
  have hW : 0 ≤ (N * β) ^ (n + 1) := by positivity
  have e1 : (s1 ^ 2 * N * β) ^ (n + 1) = s1 ^ (n + 1) * s1 ^ (n + 1) * (N * β) ^ (n + 1) := by
    ring
  have e2 : 1 / 2 * (s1 * N) ^ (n + 1) * s1 ^ n * (s1 * β ^ (n + 1)) =
      1 / 2 * (s1 ^ (n + 1) * s1 ^ (n + 1) * (N * β) ^ (n + 1)) := by
    ring
  have e3 : 1 / 2 * N ^ (n + 1) * β ^ (n + 1) = 1 / 2 * (N * β) ^ (n + 1) := by ring
  rw [e1]
  rw [e2] at h4
  rw [e3] at h3
  nlinarith [mul_le_mul_of_nonneg_right hPP hW]
private lemma involutionsOn_empty : involutionsOn (∅ : Finset (Fin q)) = {1} := by
  ext σ
  simp only [mem_involutionsOn, Finset.notMem_empty, not_false_eq_true, forall_const, Finset.mem_singleton]
  constructor
  · rintro ⟨_, h⟩
    exact Equiv.ext h
  · rintro rfl
    simp
private lemma wickWord_empty (K : ι → ι → ℝ) (i : Fin q → ι) : wickWord K i ∅ = 1 := by
  simp [wickWord, involutionsOn_empty, involutionTerm, pairStarts]
private lemma slotSquareSum_empty (K : ι → ι → ℝ) (A : (Fin q → ι) → ℝ) :
    slotSquareSum K A ∅ = MvPolynomial.C (∑ i, A i ^ 2) := by
  have h : ∀ u, slotWick K A ∅ u = MvPolynomial.C (A u) := by
    intro u
    have : agreeOff (∅ : Finset (Fin q)) u = {u} := by
      ext i
      simp [agreeOff, funext_iff]
    simp [slotWick, this, wickWord_empty]
  simp [slotSquareSum, h, map_sum, map_pow]
private lemma apply_slotSquareSum_pow_le {K : ι → ι → ℝ} {lam : ℝ} {L : MvPolynomial ι ℝ →ₗ[ℝ] ℝ}
    (h : IsSteinFunctional K lam L) (A : (Fin q → ι) → ℝ) (n s : ℕ) :
    ∀ T : Finset (Fin q), T.card = s → L (slotSquareSum K A T ^ (n + 1)) ≤
      (((2 * (n : ℝ) + 1) * lam * Fintype.card ι) ^ s * (s.factorial : ℝ) ^ 2 * ∑ i, A i ^ 2) ^ (n + 1) := by
  have hl := h.lam0
  induction s with
  | zero =>
    intro T hT
    rw [Finset.card_eq_zero.1 hT, slotSquareSum_empty, ← map_pow]
    have := apply_C_mul L ((∑ i, A i ^ 2) ^ (n + 1)) 1
    rw [mul_one, h.one, mul_one] at this
    rw [this]
    simp
  | succ s ih =>
    intro T hT
    obtain ⟨b, hbT⟩ : T.Nonempty := Finset.card_pos.1 (by omega)
    have hS : (T.erase b).card = s := by
      rw [Finset.card_erase_of_mem hbT, hT]
      rfl
    have hb : b ∉ T.erase b := Finset.notMem_erase _ _
    have hins : insert b (T.erase b) = T := Finset.insert_erase hbT
    have h1 := apply_slotSquareSum_insert_pow_le h A hb n
    have h2 := apply_removedGradSum_pow_le h A hb n
      (β := ((2 * (n : ℝ) + 1) * lam * Fintype.card ι) ^ s * (s.factorial : ℝ) ^ 2 * ∑ i, A i ^ 2)
      (by positivity) (fun T' hT' => ih T' (hT'.trans hS))
    rw [hins] at h1
    refine h1.trans ((mul_le_mul_of_nonneg_left h2 (by positivity)).trans (le_of_eq ?_))
    rw [hS, ← mul_pow]
    congr 1
    rw [Nat.factorial_succ]
    push_cast
    ring
private lemma eval_slotWick_univ (K : ι → ι → ℝ) (A : (Fin q → ι) → ℝ) (u : Fin q → ι) (ξ : ι → ℝ) :
    eval ξ (slotWick K A Finset.univ u) = wickPolynomial K A ξ := by
  have hc : agreeOff (Finset.univ : Finset (Fin q)) u = Finset.univ := by
    ext i
    simp [agreeOff]
  have hi : involutionsOn (Finset.univ : Finset (Fin q)) = Finset.univ.filter fun σ => σ * σ = 1 := by
    ext σ
    simp [mem_involutionsOn]
  unfold slotWick wickPolynomial wickWord involutionTerm
  rw [hc, hi]
  simp only [map_sum, map_mul, eval_C, map_prod, eval_X, Finset.mul_sum, pairStarts]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun i _ => ?_
  ring
private def polyIntegral (μ : Measure (ι → ℝ))
    (hint : ∀ P : MvPolynomial ι ℝ, Integrable (fun ξ => eval ξ P) μ) : MvPolynomial ι ℝ →ₗ[ℝ] ℝ where
  toFun P := ∫ ξ, eval ξ P ∂μ
  map_add' p r := by
    simp only [map_add]
    exact integral_add (hint p) (hint r)
  map_smul' c p := by
    simp [smul_eval, integral_const_mul]
open scoped MatrixOrder Matrix.Norms.L2Operator in
private lemma exists_gram_factor {K : ι → ι → ℝ} (hs : ∀ i j, K i j = K j i)
    (hp : ∀ t : ι → ℝ, 0 ≤ ∑ i, ∑ j, t i * K i j * t j) :
    ∃ B : ι → ι → ℝ, ∀ i j, K i j = ∑ a, B i a * B j a := by
  have hA : (Matrix.of K).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
    · ext i j
      simp [hs i j]
    · have := hp x
      simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
      refine this.trans (le_of_eq (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_))
      ring
  obtain ⟨Y, hY⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  refine ⟨fun i a => Y a i, fun i j => ?_⟩
  have := congrFun (congrFun hY i) j
  simpa [Matrix.mul_apply, Matrix.star_eq_conjTranspose] using this
theorem wickMomentBound_holds : WickMomentBound := by
  intro q r
  cases r with
  | zero =>
    refine ⟨1, zero_le_one, ?_⟩
    intro ι _ _ C lam μ _ _ _ _ hG A
    haveI := hG.1
    simp
  | succ n =>
    refine ⟨((2 * (n : ℝ) + 1) ^ q * (q.factorial : ℝ) ^ 2) ^ (n + 1), by positivity, ?_⟩
    intro ι _ _ K lam μ h0 hs hp hl hG A
    obtain ⟨B, hB⟩ := exists_gram_factor hs hp
    have hμ := eq_map_mixCoords_of_isCenteredGaussian B hB hG
    haveI := hG.1
    obtain ⟨hint, hst⟩ : (∀ P : MvPolynomial ι ℝ, Integrable (fun ξ => eval ξ P) μ) ∧
        ∀ (j : ι) (P : MvPolynomial ι ℝ), ∫ ξ, eval ξ (X j * P) ∂μ =
          ∑ k, K j k * ∫ ξ, eval ξ (pderiv k P) ∂μ := by
      rw [hμ]
      simpa only [hB] using integrable_and_stein_map_mixCoords B
    have hL : IsSteinFunctional K lam (polyIntegral μ hint) :=
      { symm := hs
        psd := hp
        le := hl
        lam0 := h0
        stein := hst
        pos := fun P hP => integral_nonneg hP
        one := by simp [polyIntegral] }
    have hH : 0 ≤ ∑ i, A i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    rcases isEmpty_or_nonempty (Fin q → ι) with he | ⟨⟨u₀⟩⟩
    · have hw : ∀ ξ, wickPolynomial K A ξ = 0 := by
        intro ξ
        simp [wickPolynomial]
      simp only [hw]
      simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or, Nat.add_eq_zero_iff, one_ne_zero,
        and_false, not_false_eq_true, zero_pow, integral_zero]
      positivity
    · have main := apply_slotSquareSum_pow_le hL A n q Finset.univ (by simp)
      have hNq : (0 : ℝ) < (Fintype.card ι : ℝ) ^ q := by
        have : (0 : ℝ) < Fintype.card (Fin q → ι) := by
          exact_mod_cast Fintype.card_pos_iff.2 ⟨u₀⟩
        simpa using this
      have hQ : ∀ ξ : ι → ℝ, eval ξ (slotSquareSum K A Finset.univ ^ (n + 1)) =
          ((Fintype.card ι : ℝ) ^ q) ^ (n + 1) * wickPolynomial K A ξ ^ (2 * (n + 1)) := by
        intro ξ
        rw [map_pow, eval_slotSquareSum]
        simp only [eval_slotWick_univ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp only [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.cast_pow]
        rw [mul_pow, pow_mul]
      have hLQ : polyIntegral μ hint (slotSquareSum K A Finset.univ ^ (n + 1)) =
          ((Fintype.card ι : ℝ) ^ q) ^ (n + 1) * ∫ ξ, wickPolynomial K A ξ ^ (2 * (n + 1)) ∂μ := by
        show ∫ ξ, eval ξ (slotSquareSum K A Finset.univ ^ (n + 1)) ∂μ = _
        simp only [hQ]
        rw [integral_const_mul]
      rw [hLQ] at main
      have e : (((2 * (n : ℝ) + 1) * lam * Fintype.card ι) ^ q * (q.factorial : ℝ) ^ 2 * ∑ i, A i ^ 2) ^ (n + 1) =
          ((Fintype.card ι : ℝ) ^ q) ^ (n + 1) * (((2 * (n : ℝ) + 1) ^ q * (q.factorial : ℝ) ^ 2) ^ (n + 1) *
            (lam ^ q * ∑ i, A i ^ 2) ^ (n + 1)) := by
        simp only [mul_pow]
        ring
      rw [e] at main
      exact le_of_mul_le_mul_left main (by positivity)
end YangMills.Construction.WickMoments
end
