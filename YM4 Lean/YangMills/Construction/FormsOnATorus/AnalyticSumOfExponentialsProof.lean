import YangMills.Construction.FormsOnATorus.AnalyticSumOfExponentials
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ExponentialSums
open scoped Nat
private abbrev Space : Type := Fin 4 → ℝ
private lemma summable_mul_pow_div_factorial (b e : (Fin 4 → ℤ) → ℝ) (hb : ∀ z, 0 ≤ b z) (he : ∀ z, 0 ≤ e z)
    (hS : Summable fun z => b z * Real.exp (e z)) :
    Summable fun x : (Fin 4 → ℤ) × ℕ => b x.1 * (e x.1 ^ x.2 / x.2 !) := by
  have h0 : ∀ x : (Fin 4 → ℤ) × ℕ, 0 ≤ b x.1 * (e x.1 ^ x.2 / x.2 !) := fun x =>
    mul_nonneg (hb _) (div_nonneg (pow_nonneg (he _) _) (Nat.cast_nonneg _))
  refine (summable_prod_of_nonneg h0).2 ⟨fun z => ?_, ?_⟩
  · exact (Real.summable_pow_div_factorial (e z)).mul_left (b z)
  · refine hS.congr fun z => ?_
    show b z * Real.exp (e z) = ∑' n : ℕ, b z * (e z ^ n / n !)
    rw [tsum_mul_left, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
theorem analyticAt_sum_exponentials : AnalyticAtSumOfExponentials := by
  intro a Λ L r hr hL hS
  have hΛ : ∀ z, 0 ≤ Λ z := fun z => (norm_nonneg _).trans (hL z)
  let term : (n : ℕ) → (Fin 4 → ℤ) → ContinuousMultilinearMap ℝ (fun _ : Fin n => Space) ℂ := fun n z =>
    (a z * ((n ! : ℕ) : ℂ)⁻¹) •
      (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℂ).compContinuousLinearMap fun _ => L z
  have hterm : ∀ n z, ‖term n z‖ ≤ ‖a z‖ * (Λ z ^ n / n !) := by
    intro n z
    simp only [term]
    rw [norm_smul, norm_mul, norm_inv, Complex.norm_natCast]
    have h1 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℂ) (fun _ => L z)
    rw [ContinuousMultilinearMap.norm_mkPiAlgebra, one_mul, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at h1
    have h2 : ‖L z‖ ^ n ≤ Λ z ^ n := pow_le_pow_left₀ (norm_nonneg _) (hL z) n
    calc _ ≤ ‖a z‖ * ((n ! : ℝ))⁻¹ * Λ z ^ n :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
      _ = _ := by rw [div_eq_mul_inv]; ring
  have hpow : ∀ (n : ℕ) (z : Fin 4 → ℤ), Λ z ^ n / n ! * r ^ n ≤ Real.exp (Λ z * r) := by
    intro n z
    have := Real.pow_div_factorial_le_exp (Λ z * r) (mul_nonneg (hΛ z) hr.le) n
    refine le_trans (le_of_eq ?_) this
    rw [mul_pow]; ring
  have hsum_term : ∀ n, Summable fun z => ‖term n z‖ := by
    intro n
    refine Summable.of_nonneg_of_le (fun z => norm_nonneg _) (fun z => ?_) (hS.mul_right ((r ^ n)⁻¹))
    have h1 := hterm n z
    have h2 := hpow n z
    have hrn : 0 < r ^ n := by positivity
    refine h1.trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [le_mul_inv_iff₀ hrn]
    exact h2
  let q : FormalMultilinearSeries ℝ Space ℂ := fun n => ∑' z, term n z
  have hq : ∀ n, ‖q n‖ * r ^ n ≤ ∑' z, ‖a z‖ * Real.exp (Λ z * r) := by
    intro n
    have h1 : ‖q n‖ ≤ ∑' z, ‖term n z‖ := norm_tsum_le_tsum_norm (hsum_term n)
    have hrn : 0 ≤ r ^ n := by positivity
    calc ‖q n‖ * r ^ n ≤ (∑' z, ‖term n z‖) * r ^ n := mul_le_mul_of_nonneg_right h1 hrn
      _ = ∑' z, ‖term n z‖ * r ^ n := by rw [tsum_mul_right]
      _ ≤ _ := by
        refine Summable.tsum_le_tsum (fun z => ?_) ((hsum_term n).mul_right _) hS
        calc ‖term n z‖ * r ^ n ≤ (‖a z‖ * (Λ z ^ n / n !)) * r ^ n :=
              mul_le_mul_of_nonneg_right (hterm n z) hrn
          _ = ‖a z‖ * (Λ z ^ n / n ! * r ^ n) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (hpow n z) (norm_nonneg _)
  have hle : (ENNReal.ofReal r) ≤ q.radius := by
    have h := q.le_radius_of_bound (∑' z, ‖a z‖ * Real.exp (Λ z * r)) (r := r.toNNReal) (fun n => by
      rw [Real.coe_toNNReal _ hr.le]; exact hq n)
    simpa [ENNReal.ofReal] using h
  refine HasFPowerSeriesOnBall.analyticAt (p := q) (r := ENNReal.ofReal r) ⟨hle, by simpa using hr, ?_⟩
  intro y hy
  rw [zero_add]
  have hy' : ‖y‖ < r := by
    have : y ∈ Metric.ball (0 : Space) r := by
      rw [← Metric.eball_ofReal]
      exact hy
    simpa using this
  set T : (Fin 4 → ℤ) × ℕ → ℂ := fun x => a x.1 * ((x.2 ! : ℕ) : ℂ)⁻¹ * (L x.1 y) ^ x.2 with hT
  have hTb : ∀ x, ‖T x‖ ≤ ‖a x.1‖ * ((Λ x.1 * r) ^ x.2 / x.2 !) := by
    intro x
    simp only [hT]
    rw [norm_mul, norm_mul, norm_inv, Complex.norm_natCast, norm_pow]
    have h1 : ‖L x.1 y‖ ≤ Λ x.1 * r :=
      ((L x.1).le_opNorm y).trans (mul_le_mul (hL x.1) hy'.le (norm_nonneg _) (hΛ x.1))
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 x.2
    have h3 : ‖a x.1‖ * ((x.2 ! : ℝ))⁻¹ * ‖L x.1 y‖ ^ x.2 ≤ ‖a x.1‖ * ((x.2 ! : ℝ))⁻¹ * (Λ x.1 * r) ^ x.2 :=
      mul_le_mul_of_nonneg_left h2 (mul_nonneg (norm_nonneg _) (inv_nonneg.2 (Nat.cast_nonneg _)))
    refine h3.trans (le_of_eq ?_)
    rw [div_eq_mul_inv]; ring
  have hU : Summable fun x : (Fin 4 → ℤ) × ℕ => ‖a x.1‖ * ((Λ x.1 * r) ^ x.2 / x.2 !) :=
    summable_mul_pow_div_factorial (fun z => ‖a z‖) (fun z => Λ z * r) (fun z => norm_nonneg _)
      (fun z => mul_nonneg (hΛ z) hr.le) hS
  have hTs : Summable T := Summable.of_norm_bounded hU hTb
  have hTS := hTs.hasSum
  have hfib1 : ∀ z, HasSum (fun n => T (z, n)) (a z * Complex.exp (L z y)) := by
    intro z
    have h := (NormedSpace.expSeries_div_hasSum_exp (L z y)).mul_left (a z)
    rw [← Complex.exp_eq_exp_ℂ] at h
    refine (congrArg (fun f : ℕ → ℂ => HasSum f _) ?_).mpr h
    funext n
    simp only [hT]
    rw [div_eq_mul_inv]; ring
  have hA := hTS.prod_fiberwise hfib1
  have hsw : HasSum (fun x : ℕ × (Fin 4 → ℤ) => T (x.2, x.1)) (∑' x, T x) := (Equiv.prodComm ℕ (Fin 4 → ℤ)).hasSum_iff.2 hTS
  have hfib2 : ∀ n, HasSum (fun z => T (z, n)) (q n fun _ => y) := by
    intro n
    have hs : Summable fun z => term n z := Summable.of_norm (hsum_term n)
    have h := hs.hasSum
    have h2 := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Space) ℂ (fun _ => y)).hasSum h
    refine (congrArg (fun f : (Fin 4 → ℤ) → ℂ => HasSum f _) ?_).mpr h2
    funext z
    simp [term, hT, mul_assoc, ContinuousMultilinearMap.mkPiAlgebra_apply]
  have hB := hsw.prod_fiberwise hfib2
  rw [hA.tsum_eq]
  exact hB
end YangMills.Construction.ExponentialSums
end
