import YangMills.Construction.HilbertSpace.IteratedCauchySchwarz
import YangMills.Construction.SpectralCalculus.FormCompletionAndBoundedExtension
import Mathlib
set_option autoImplicit false
open YangMills.Construction.SpectralCalculus Filter Topology
open scoped ComplexOrder
namespace YangMills.Construction.HilbertSpace.IteratedCauchySchwarz
theorem two_rpow_neg_natCast_eq (k : ℕ) : (2 : ℝ) ^ (-(k : ℝ)) = (1 / 2 : ℝ) ^ k := by
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div, inv_pow]
theorem two_rpow_neg_natCast_pos (k : ℕ) : 0 < (2 : ℝ) ^ (-(k : ℝ)) := by
  rw [two_rpow_neg_natCast_eq]; positivity
theorem two_rpow_neg_natCast_le_one (k : ℕ) : (2 : ℝ) ^ (-(k : ℝ)) ≤ 1 := by
  rw [two_rpow_neg_natCast_eq]; exact pow_le_one₀ (by norm_num) (by norm_num)
theorem two_rpow_neg_natCast_succ (k : ℕ) :
    (2 : ℝ) ^ (-((k + 1 : ℕ) : ℝ)) = (2 : ℝ) ^ (-(k : ℝ)) * (1 / 2) := by
  rw [two_rpow_neg_natCast_eq, two_rpow_neg_natCast_eq, pow_succ]
theorem tendsto_two_rpow_neg_natCast :
    Tendsto (fun k : ℕ => (2 : ℝ) ^ (-(k : ℝ))) atTop (𝓝 0) := by
  simp only [two_rpow_neg_natCast_eq]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
theorem le_rpow_of_sq_le_mul_succ (N : ℝ) (x : ℕ → ℝ) (hN : 0 ≤ N) (hx : ∀ k, 0 ≤ x k)
    (h : ∀ k, x k ^ 2 ≤ N * x (k + 1)) (k : ℕ) :
    x 0 ≤ N ^ (1 - (2 : ℝ) ^ (-(k : ℝ))) * x k ^ ((2 : ℝ) ^ (-(k : ℝ))) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he := two_rpow_neg_natCast_pos k
    have he1 := two_rpow_neg_natCast_le_one k
    rw [two_rpow_neg_natCast_succ]
    set e : ℝ := (2 : ℝ) ^ (-(k : ℝ)) with hedef
    have hhalf : x k ≤ N ^ (1 / 2 : ℝ) * x (k + 1) ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, ← Real.sqrt_mul hN]
      exact Real.le_sqrt_of_sq_le (h k)
    have hpow : x k ^ e ≤ N ^ (e * (1 / 2)) * x (k + 1) ^ (e * (1 / 2)) := by
      calc x k ^ e ≤ (N ^ (1 / 2 : ℝ) * x (k + 1) ^ (1 / 2 : ℝ)) ^ e :=
            Real.rpow_le_rpow (hx k) hhalf he.le
        _ = N ^ (e * (1 / 2)) * x (k + 1) ^ (e * (1 / 2)) := by
            rw [Real.mul_rpow (Real.rpow_nonneg hN _) (Real.rpow_nonneg (hx _) _),
              ← Real.rpow_mul hN, ← Real.rpow_mul (hx _), mul_comm (1 / 2 : ℝ) e]
    calc x 0 ≤ N ^ (1 - e) * x k ^ e := ih
      _ ≤ N ^ (1 - e) * (N ^ (e * (1 / 2)) * x (k + 1) ^ (e * (1 / 2))) :=
          mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hN _)
      _ = N ^ (1 - e * (1 / 2)) * x (k + 1) ^ (e * (1 / 2)) := by
          rw [← mul_assoc, ← Real.rpow_add_of_nonneg hN (by linarith) (by linarith)]
          congr 2
          ring
theorem tendsto_mul_two_pow_rpow {c : ℝ} (hc : 0 < c) :
    Tendsto (fun k : ℕ => (c * 2 ^ k) ^ ((2 : ℝ) ^ (-(k : ℝ)))) atTop (𝓝 1) := by
  have hlog : ∀ k : ℕ, (c * 2 ^ k) ^ ((2 : ℝ) ^ (-(k : ℝ))) =
      Real.exp (Real.log c * (2 : ℝ) ^ (-(k : ℝ)) +
        Real.log 2 * ((k : ℝ) * (1 / 2 : ℝ) ^ k)) := by
    intro k
    rw [Real.rpow_def_of_pos (by positivity), Real.log_mul hc.ne' (by positivity), Real.log_pow,
      two_rpow_neg_natCast_eq]
    congr 1
    ring
  simp only [hlog]
  have t1 : Tendsto (fun k : ℕ => (k : ℝ) * (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
    tendsto_self_mul_const_pow_of_lt_one (by norm_num) (by norm_num)
  have t2 : Tendsto (fun k : ℕ => Real.log c * (2 : ℝ) ^ (-(k : ℝ)) +
      Real.log 2 * ((k : ℝ) * (1 / 2 : ℝ) ^ k)) atTop (𝓝 0) := by
    simpa using (tendsto_two_rpow_neg_natCast.const_mul (Real.log c)).add
      (t1.const_mul (Real.log 2))
  have t3 := (Real.continuous_exp.tendsto 0).comp t2
  rw [Real.exp_zero] at t3
  exact t3
theorem le_mul_of_forall_rpow_bound (a N b c : ℝ) (hN : 0 ≤ N) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : ∀ k : ℕ, 1 ≤ k →
      a ≤ N ^ (1 - (2 : ℝ) ^ (-(k : ℝ))) *
        (c * ((2 ^ k : ℕ) : ℝ) * b ^ (2 ^ k - 1)) ^ ((2 : ℝ) ^ (-(k : ℝ)))) :
    a ≤ b * N := by
  have hsplit : ∀ k : ℕ, (c * ((2 ^ k : ℕ) : ℝ) * b ^ (2 ^ k - 1)) ^ ((2 : ℝ) ^ (-(k : ℝ))) =
      (c * 2 ^ k) ^ ((2 : ℝ) ^ (-(k : ℝ))) * b ^ (1 - (2 : ℝ) ^ (-(k : ℝ))) := by
    intro k
    have hm : (((2 ^ k - 1 : ℕ)) : ℝ) = 2 ^ k - 1 := by
      rw [Nat.cast_sub Nat.one_le_two_pow]; push_cast; ring
    have hone : (2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k = 1 := by
      rw [← mul_pow]; norm_num
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast b (2 ^ k - 1),
      ← Real.rpow_mul hb, hm]
    push_cast
    congr 2
    rw [two_rpow_neg_natCast_eq]
    linarith
  have h1 : ∀ k : ℕ, 1 ≤ k → a ≤ N ^ (1 - (2 : ℝ) ^ (-(k : ℝ))) *
      ((c * 2 ^ k) ^ ((2 : ℝ) ^ (-(k : ℝ))) * b ^ (1 - (2 : ℝ) ^ (-(k : ℝ)))) := by
    intro k hk
    rw [← hsplit]
    exact h k hk
  have hhalf : (0 : ℝ) < 1 - (2 : ℝ) ^ (-((1 : ℕ) : ℝ)) := by
    rw [two_rpow_neg_natCast_eq]; norm_num
  rcases hN.eq_or_lt with rfl | hN'
  · have := h1 1 le_rfl
    rw [Real.zero_rpow hhalf.ne', zero_mul] at this
    simpa using this
  rcases hb.eq_or_lt with rfl | hb'
  · have := h1 1 le_rfl
    rw [Real.zero_rpow hhalf.ne', mul_zero, mul_zero] at this
    simpa using this
  rcases hc.eq_or_lt with rfl | hc'
  · have := h1 1 le_rfl
    rw [zero_mul, Real.zero_rpow (two_rpow_neg_natCast_pos 1).ne', zero_mul, mul_zero] at this
    exact this.trans (by positivity)
  have hsub : Tendsto (fun k : ℕ => 1 - (2 : ℝ) ^ (-(k : ℝ))) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub tendsto_two_rpow_neg_natCast
  have hNlim : Tendsto (fun k : ℕ => N ^ (1 - (2 : ℝ) ^ (-(k : ℝ)))) atTop (𝓝 N) := by
    simpa using (tendsto_const_nhds (x := N)).rpow hsub (Or.inl hN'.ne')
  have hblim : Tendsto (fun k : ℕ => b ^ (1 - (2 : ℝ) ^ (-(k : ℝ)))) atTop (𝓝 b) := by
    simpa using (tendsto_const_nhds (x := b)).rpow hsub (Or.inl hb'.ne')
  have hlim := hNlim.mul ((tendsto_mul_two_pow_rpow hc').mul hblim)
  have hfin : a ≤ N * (1 * b) :=
    ge_of_tendsto hlim ((eventually_ge_atTop 1).mono fun k hk => h1 k hk)
  linarith
theorem form_iterate_left_eq_right {V : Type} (form : V → V → ℂ) (A : V → V)
    (hA : ∀ f g : V, form (A f) g = form f (A g)) (n : ℕ) (f g : V) :
    form (A^[n] f) g = form f (A^[n] g) := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih, hA, Function.iterate_succ_apply']
theorem sq_formSeminorm_iterate_le {V : Type} [AddCommGroup V] [Module ℂ V]
    (hbasic : FormCompletionAndBoundedExtension)
    (form : V → V → ℂ) (A : V → V) (hform : IsPosHermitianForm form)
    (hA : ∀ f g : V, form (A f) g = form f (A g)) (n : ℕ) (f : V) :
    formSeminorm form (A^[n] f) ^ 2 ≤ formSeminorm form f * formSeminorm form (A^[n + n] f) := by
  have hre : 0 ≤ (form (A^[n] f) (A^[n] f)).re := (Complex.le_def.mp (hform.nonneg _)).1
  have hcs := (hbasic.1 V form hform).1.norm_le_mul f (A^[n + n] f)
  rw [formSeminorm, Real.sq_sqrt hre, form_iterate_left_eq_right form A hA,
    ← Function.iterate_add_apply]
  exact (Complex.re_le_norm _).trans hcs
theorem claim_holds (hbasic : FormCompletionAndBoundedExtension) : Claim := by
  intro V _ _ form A hform hA
  have hnn : ∀ v : V, 0 ≤ formSeminorm form v := fun v => Real.sqrt_nonneg _
  have hsq : ∀ (f : V) (k : ℕ), formSeminorm form (A^[2 ^ k] f) ^ 2 ≤
      formSeminorm form f * formSeminorm form (A^[2 ^ (k + 1)] f) := by
    intro f k
    have := sq_formSeminorm_iterate_le hbasic form A hform hA (2 ^ k) f
    rwa [← two_mul, ← pow_succ'] at this
  have hpart : ∀ (f : V) (k : ℕ), formSeminorm form (A f) ≤
      formSeminorm form f ^ (1 - (2 : ℝ) ^ (-(k : ℝ))) *
        formSeminorm form (A^[2 ^ k] f) ^ ((2 : ℝ) ^ (-(k : ℝ))) := by
    intro f k
    have := le_rpow_of_sq_le_mul_succ (formSeminorm form f)
      (fun j => formSeminorm form (A^[2 ^ j] f)) (hnn f) (fun j => hnn _) (hsq f) k
    simpa using this
  refine ⟨fun f k _ => hpart f k, fun f b c hb hc hbound => ?_⟩
  refine le_mul_of_forall_rpow_bound _ _ b c (hnn _) hb hc fun k hk => ?_
  refine (hpart f k).trans (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (hnn f) _))
  exact Real.rpow_le_rpow (hnn _) (hbound k (2 ^ k) hk rfl) (two_rpow_neg_natCast_pos k).le
end YangMills.Construction.HilbertSpace.IteratedCauchySchwarz
