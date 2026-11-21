import YangMills.Construction.ColdChainAtEveryLevel.ChartOverAnotherTopProof
import YangMills.Construction.ColdChainAtEveryLevel.FloorOfTheChartFormProof
import YangMills.Construction.ColdChainAtEveryLevel.RatesOfTheTerms
import YangMills.Construction.ColdChainAtEveryLevel.SecondVariationOfAFitInTheChart
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Quaternion Topology Nat
namespace YangMills.Construction.BlockAverages
namespace ChartFit
section ExpLine
def affineLine (A U : ℍ[ℝ]) (τ : ℝ) : ℍ[ℝ] := A + τ • U
def powDeriv (A U : ℍ[ℝ]) : ℕ → ℝ → ℍ[ℝ]
  | 0, _ => 0
  | n + 1, τ => U * affineLine A U τ ^ n + affineLine A U τ * powDeriv A U n τ
def powDeriv2 (A U : ℍ[ℝ]) : ℕ → ℝ → ℍ[ℝ]
  | 0, _ => 0
  | n + 1, τ => U * powDeriv A U n τ + (U * powDeriv A U n τ + affineLine A U τ * powDeriv2 A U n τ)
variable (A U : ℍ[ℝ])
theorem affineLine_hasDerivAt (τ : ℝ) : HasDerivAt (affineLine A U) U τ := by
  have h : HasDerivAt (fun s : ℝ => A + s • U) ((1 : ℝ) • U) τ :=
    ((hasDerivAt_id τ).smul_const U).const_add A
  rw [one_smul] at h
  exact h
theorem affineLine_pow_hasDerivAt (n : ℕ) (τ : ℝ) :
    HasDerivAt (fun s => affineLine A U s ^ n) (powDeriv A U n τ) τ := by
  induction n with
  | zero => simpa [powDeriv] using hasDerivAt_const τ (1 : ℍ[ℝ])
  | succ n ih =>
    have h := (affineLine_hasDerivAt A U τ).mul ih
    have e : (fun s => affineLine A U s ^ (n + 1)) = affineLine A U * fun s => affineLine A U s ^ n := by
      funext s; exact pow_succ' _ _
    rw [e]
    exact h
theorem powDeriv_hasDerivAt (n : ℕ) (τ : ℝ) : HasDerivAt (powDeriv A U n) (powDeriv2 A U n τ) τ := by
  induction n with
  | zero =>
    have : powDeriv A U 0 = fun _ => 0 := by funext s; rfl
    rw [this]
    simpa [powDeriv2] using hasDerivAt_const τ (0 : ℍ[ℝ])
  | succ n ih =>
    have h1 := (affineLine_pow_hasDerivAt A U n τ).const_mul U
    have h2 := (affineLine_hasDerivAt A U τ).mul ih
    have h := h1.add h2
    have e : powDeriv A U (n + 1) = (fun s => U * affineLine A U s ^ n) + (affineLine A U * powDeriv A U n) := by
      funext s; rfl
    rw [e]
    exact h
variable {A U}
theorem norm_powDeriv_le {T τ : ℝ} (hT : ‖affineLine A U τ‖ ≤ T) (n : ℕ) :
    ‖powDeriv A U (n + 1) τ‖ ≤ (n + 1) * ‖U‖ * T ^ n := by
  have hT0 : 0 ≤ T := (norm_nonneg _).trans hT
  induction n with
  | zero => simp [powDeriv]
  | succ n ih =>
    have h1 : ‖U * affineLine A U τ ^ (n + 1)‖ ≤ ‖U‖ * T ^ (n + 1) := by
      refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      exact (norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg _) hT _)
    have h2 : ‖affineLine A U τ * powDeriv A U (n + 1) τ‖ ≤ T * (((n : ℝ) + 1) * ‖U‖ * T ^ n) := by
      refine (norm_mul_le _ _).trans ?_
      exact mul_le_mul hT ih (norm_nonneg _) hT0
    have e : powDeriv A U (n + 1 + 1) τ = U * affineLine A U τ ^ (n + 1) + affineLine A U τ * powDeriv A U (n + 1) τ := rfl
    rw [e]
    refine (norm_add_le _ _).trans ((add_le_add h1 h2).trans (le_of_eq ?_))
    push_cast
    ring
theorem norm_powDeriv2_le {T τ : ℝ} (hT : ‖affineLine A U τ‖ ≤ T) (n : ℕ) :
    ‖powDeriv2 A U (n + 2) τ‖ ≤ (n + 2) * (n + 1) * ‖U‖ ^ 2 * T ^ n := by
  have hT0 : 0 ≤ T := (norm_nonneg _).trans hT
  induction n with
  | zero =>
    have e : powDeriv2 A U 2 τ = U * powDeriv A U 1 τ + (U * powDeriv A U 1 τ + affineLine A U τ * powDeriv2 A U 1 τ) := rfl
    have e1 : powDeriv2 A U 1 τ = 0 := by simp [powDeriv2, powDeriv]
    have e2 : powDeriv A U 1 τ = U := by simp [powDeriv]
    rw [e, e1, e2]
    simp only [mul_zero, add_zero]
    refine (norm_add_le _ _).trans ?_
    have := norm_mul_le U U
    norm_num
    nlinarith
  | succ n ih =>
    have h1 : ‖U * powDeriv A U (n + 2) τ‖ ≤ ‖U‖ * (((n + 1 : ℕ) + 1) * ‖U‖ * T ^ (n + 1)) := by
      refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      exact norm_powDeriv_le hT (n + 1)
    have h2 : ‖affineLine A U τ * powDeriv2 A U (n + 2) τ‖ ≤ T * (((n : ℝ) + 2) * (n + 1) * ‖U‖ ^ 2 * T ^ n) := by
      refine (norm_mul_le _ _).trans ?_
      exact mul_le_mul hT ih (norm_nonneg _) hT0
    have e : powDeriv2 A U (n + 1 + 2) τ =
        U * powDeriv A U (n + 2) τ + (U * powDeriv A U (n + 2) τ + affineLine A U τ * powDeriv2 A U (n + 2) τ) := rfl
    rw [e]
    refine (norm_add_le _ _).trans ((add_le_add h1 ((norm_add_le _ _).trans (add_le_add h1 h2))).trans
      (le_of_eq ?_))
    push_cast
    ring
theorem summable_of_shift_eq {b : ℕ → ℝ} (k : ℕ) (c T : ℝ)
    (hb : ∀ n, b (n + k) = c * (T ^ n / n !)) : Summable b := by
  refine (summable_nat_add_iff k).1 ?_
  simp only [hb]
  exact (Real.summable_pow_div_factorial T).mul_left c
def derivMajorant (c T : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => c * (T ^ n / n !)
def derivMajorant2 (c T : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 0
  | n + 2 => c * (T ^ n / n !)
theorem norm_powDeriv_term_le {T τ : ℝ} (hT : ‖affineLine A U τ‖ ≤ T) (n : ℕ) :
    ‖((n ! : ℝ)⁻¹) • powDeriv A U n τ‖ ≤ derivMajorant ‖U‖ T n := by
  cases n with
  | zero => simp [powDeriv, derivMajorant]
  | succ n =>
    have h := norm_powDeriv_le hT n
    rw [norm_smul, norm_inv, Real.norm_natCast]
    have hf : ((n + 1)! : ℝ) = (n + 1) * (n ! : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    calc (((n + 1)! : ℝ))⁻¹ * ‖powDeriv A U (n + 1) τ‖
        ≤ (((n + 1)! : ℝ))⁻¹ * ((n + 1) * ‖U‖ * T ^ n) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = derivMajorant ‖U‖ T (n + 1) := by
          simp only [derivMajorant]
          rw [hf]
          field_simp
theorem norm_powDeriv2_term_le {T τ : ℝ} (hT : ‖affineLine A U τ‖ ≤ T) (n : ℕ) :
    ‖((n ! : ℝ)⁻¹) • powDeriv2 A U n τ‖ ≤ derivMajorant2 (‖U‖ ^ 2) T n := by
  match n with
  | 0 => simp [powDeriv2, derivMajorant2]
  | 1 => simp [powDeriv2, powDeriv, derivMajorant2]
  | n + 2 =>
    have h := norm_powDeriv2_le hT n
    rw [norm_smul, norm_inv, Real.norm_natCast]
    have hf : ((n + 2)! : ℝ) = (n + 2) * ((n + 1) * (n ! : ℝ)) := by
      rw [Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
    calc (((n + 2)! : ℝ))⁻¹ * ‖powDeriv2 A U (n + 2) τ‖
        ≤ (((n + 2)! : ℝ))⁻¹ * ((n + 2) * (n + 1) * ‖U‖ ^ 2 * T ^ n) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = derivMajorant2 (‖U‖ ^ 2) T (n + 2) := by
          simp only [derivMajorant2]
          rw [hf]
          field_simp
theorem summable_derivMajorant (c T : ℝ) : Summable (derivMajorant c T) :=
  summable_of_shift_eq 1 c T fun _ => rfl
theorem summable_derivMajorant2 (c T : ℝ) : Summable (derivMajorant2 c T) :=
  summable_of_shift_eq 2 c T fun _ => rfl
def expDeriv (A U : ℍ[ℝ]) (τ : ℝ) : ℍ[ℝ] := ∑' n : ℕ, ((n ! : ℝ)⁻¹) • powDeriv A U n τ
def expDeriv2 (A U : ℍ[ℝ]) (τ : ℝ) : ℍ[ℝ] := ∑' n : ℕ, ((n ! : ℝ)⁻¹) • powDeriv2 A U n τ
theorem norm_affineLine_le {τ : ℝ} (hτ : τ ∈ Metric.ball (0 : ℝ) 1) : ‖affineLine A U τ‖ ≤ ‖A‖ + ‖U‖ := by
  have h : |τ| < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hτ
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) h.le
theorem exp_affineLine_eq (τ : ℝ) :
    NormedSpace.exp (A + τ • U) = ∑' n : ℕ, ((n ! : ℝ)⁻¹) • affineLine A U τ ^ n :=
  (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (A + τ • U)).tsum_eq.symm
theorem exp_affineLine_hasDerivAt {τ : ℝ} (hτ : τ ∈ Metric.ball (0 : ℝ) 1) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (A + s • U)) (expDeriv A U τ) τ := by
  have e : (fun s : ℝ => NormedSpace.exp (A + s • U)) =
      fun s : ℝ => ∑' n : ℕ, ((n ! : ℝ)⁻¹) • affineLine A U s ^ n := by
    funext s; exact exp_affineLine_eq s
  rw [e]
  refine hasDerivAt_tsum_of_isPreconnected (y₀ := (0 : ℝ)) (t := Metric.ball (0 : ℝ) 1)
    (u := derivMajorant ‖U‖ (‖A‖ + ‖U‖)) (g' := fun n s => ((n ! : ℝ)⁻¹) • powDeriv A U n s)
    (summable_derivMajorant _ _) Metric.isOpen_ball (convex_ball _ _).isPreconnected ?_ ?_
    (Metric.mem_ball_self one_pos) ?_ hτ
  · intro n y _
    exact (affineLine_pow_hasDerivAt A U n y).const_smul ((n ! : ℝ)⁻¹)
  · intro n y hy
    exact norm_powDeriv_term_le (norm_affineLine_le hy) n
  · exact (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (affineLine A U 0)).summable
theorem expDeriv_hasDerivAt {τ : ℝ} (hτ : τ ∈ Metric.ball (0 : ℝ) 1) :
    HasDerivAt (expDeriv A U) (expDeriv2 A U τ) τ := by
  refine hasDerivAt_tsum_of_isPreconnected (y₀ := (0 : ℝ)) (t := Metric.ball (0 : ℝ) 1)
    (u := derivMajorant2 (‖U‖ ^ 2) (‖A‖ + ‖U‖)) (g' := fun n s => ((n ! : ℝ)⁻¹) • powDeriv2 A U n s)
    (summable_derivMajorant2 _ _) Metric.isOpen_ball (convex_ball _ _).isPreconnected ?_ ?_
    (Metric.mem_ball_self one_pos) ?_ hτ
  · intro n y _
    exact (powDeriv_hasDerivAt A U n y).const_smul ((n ! : ℝ)⁻¹)
  · intro n y hy
    exact norm_powDeriv2_term_le (norm_affineLine_le hy) n
  · exact Summable.of_norm_bounded (summable_derivMajorant ‖U‖ ‖affineLine A U 0‖)
      fun n => norm_powDeriv_term_le le_rfl n
theorem hasSum_pow_div_factorial (T : ℝ) : HasSum (fun n : ℕ => T ^ n / n !) (Real.exp T) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp T
theorem norm_hasSum_sub_head_le {a : ℕ → ℍ[ℝ]} {s : ℍ[ℝ]} {c T : ℝ} (ha : HasSum a s)
    (hb : ∀ n, ‖a (n + 1)‖ ≤ c * (T ^ n / n !)) : ‖s - a 0‖ ≤ c * Real.exp T := by
  have h1 : HasSum (fun n => a (n + 1)) (s - a 0) := by
    have := (hasSum_nat_add_iff' (f := a) 1).2 ha
    simpa using this
  have h2 : HasSum (fun n : ℕ => c * (T ^ n / n !)) (c * Real.exp T) := (hasSum_pow_div_factorial T).mul_left c
  have h4 := tsum_of_norm_bounded h2 hb
  rwa [h1.tsum_eq] at h4
theorem pow_succ_div_factorial_le {T : ℝ} (hT : 0 ≤ T) (n : ℕ) : T ^ (n + 1) / (n + 1)! ≤ T * (T ^ n / n !) := by
  have hf : ((n + 1)! : ℝ) = (n + 1) * (n ! : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [hf, pow_succ, div_le_iff₀ (by positivity)]
  have : T * (T ^ n / (n ! : ℝ)) * (((n : ℝ) + 1) * (n ! : ℝ)) = T ^ n * T * (n + 1) := by
    field_simp
  rw [this]
  have h1 : (0 : ℝ) ≤ T ^ n * T := by positivity
  nlinarith [show (0 : ℝ) ≤ n by positivity]
theorem exp_le_three {T : ℝ} (hT : T ≤ 1) : Real.exp T ≤ 3 := by
  have h1 : Real.exp T ≤ Real.exp 1 := Real.exp_le_exp.2 hT
  have h2 := Real.exp_one_lt_d9
  linarith
theorem norm_exp_sub_one_le (hA : ‖A‖ ≤ 1) : ‖NormedSpace.exp A - 1‖ ≤ 3 * ‖A‖ := by
  have hs := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A
  have h := norm_hasSum_sub_head_le (c := ‖A‖) (T := ‖A‖) hs ?_
  · simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul] at h
    refine h.trans ?_
    have := exp_le_three hA
    nlinarith [norm_nonneg A]
  · intro n
    rw [norm_smul, norm_inv, Real.norm_natCast]
    have h1 : ‖A ^ (n + 1)‖ ≤ ‖A‖ ^ (n + 1) := norm_pow_le _ _
    calc (((n + 1)! : ℝ))⁻¹ * ‖A ^ (n + 1)‖ ≤ (((n + 1)! : ℝ))⁻¹ * ‖A‖ ^ (n + 1) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ‖A‖ ^ (n + 1) / (n + 1)! := by rw [div_eq_inv_mul]
      _ ≤ _ := pow_succ_div_factorial_le (norm_nonneg _) n
theorem norm_expDeriv_zero_sub_le (hA : ‖A‖ ≤ 1) : ‖expDeriv A U 0 - U‖ ≤ 3 * ‖A‖ * ‖U‖ := by
  have hl : affineLine A U 0 = A := by simp [affineLine]
  have hT : ‖affineLine A U 0‖ ≤ ‖A‖ := by rw [hl]
  have hsum : Summable fun n : ℕ => ((n ! : ℝ)⁻¹) • powDeriv A U n 0 :=
    Summable.of_norm_bounded (summable_derivMajorant ‖U‖ ‖A‖) fun n => norm_powDeriv_term_le hT n
  have h0 : HasSum (fun n : ℕ => ((n + 1 : ℕ)! : ℝ)⁻¹ • powDeriv A U (n + 1) 0) (expDeriv A U 0) := by
    have := (hasSum_nat_add_iff' (f := fun n : ℕ => ((n ! : ℝ)⁻¹) • powDeriv A U n 0) 1).2 hsum.hasSum
    simpa [powDeriv, expDeriv] using this
  have h := norm_hasSum_sub_head_le (c := ‖A‖ * ‖U‖) (T := ‖A‖) h0 ?_
  · have e : ((0 + 1 : ℕ)! : ℝ)⁻¹ • powDeriv A U (0 + 1) 0 = U := by simp [powDeriv]
    rw [e] at h
    refine h.trans ?_
    have := exp_le_three hA
    have h1 : 0 ≤ ‖A‖ * ‖U‖ := by positivity
    nlinarith
  · intro n
    have hb := norm_powDeriv_le hT (n + 1)
    rw [norm_smul, norm_inv, Real.norm_natCast]
    have hf : ((n + 1 + 1)! : ℝ) = (n + 2) * ((n + 1)! : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hn : (0 : ℝ) < (n + 1)! := by exact_mod_cast Nat.factorial_pos _
    calc (((n + 1 + 1)! : ℝ))⁻¹ * ‖powDeriv A U (n + 1 + 1) 0‖
        ≤ (((n + 1 + 1)! : ℝ))⁻¹ * ((((n + 1 : ℕ) : ℝ) + 1) * ‖U‖ * ‖A‖ ^ (n + 1)) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = ‖U‖ * (‖A‖ ^ (n + 1) / (n + 1)!) := by
          rw [hf]; push_cast; field_simp; ring
      _ ≤ ‖U‖ * (‖A‖ * (‖A‖ ^ n / n !)) :=
          mul_le_mul_of_nonneg_left (pow_succ_div_factorial_le (norm_nonneg _) n) (norm_nonneg _)
      _ = _ := by ring
theorem norm_expDeriv2_zero_le (hA : ‖A‖ ≤ 1) : ‖expDeriv2 A U 0‖ ≤ 3 * ‖U‖ ^ 2 := by
  have hl : affineLine A U 0 = A := by simp [affineLine]
  have hT : ‖affineLine A U 0‖ ≤ ‖A‖ := by rw [hl]
  have h2 : HasSum (derivMajorant2 (‖U‖ ^ 2) ‖A‖) (‖U‖ ^ 2 * Real.exp ‖A‖) := by
    have h3 := (hasSum_pow_div_factorial ‖A‖).mul_left (‖U‖ ^ 2)
    have := (hasSum_nat_add_iff' (f := derivMajorant2 (‖U‖ ^ 2) ‖A‖) 2).1 (by simpa [derivMajorant2, Finset.sum_range_succ] using h3)
    simpa [derivMajorant2, Finset.sum_range_succ] using this
  have h4 := tsum_of_norm_bounded h2 (fun n => norm_powDeriv2_term_le hT n)
  refine h4.trans ?_
  have := exp_le_three hA
  nlinarith [sq_nonneg ‖U‖]
theorem exp_affineLine_jet (A U : ℍ[ℝ]) (hA : ‖A‖ ≤ 1) :
    AnalyticAt ℝ (fun τ : ℝ => NormedSpace.exp (A + τ • U)) 0 ∧
      ‖deriv (fun τ : ℝ => NormedSpace.exp (A + τ • U)) 0 - U‖ ≤ 3 * ‖A‖ * ‖U‖ ∧
      ‖deriv (deriv fun τ : ℝ => NormedSpace.exp (A + τ • U)) 0‖ ≤ 3 * ‖U‖ ^ 2 := by
  have h0 : (0 : ℝ) ∈ Metric.ball (0 : ℝ) 1 := Metric.mem_ball_self one_pos
  have hd : deriv (fun τ : ℝ => NormedSpace.exp (A + τ • U)) =ᶠ[𝓝 0] expDeriv A U := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with τ hτ
    exact (exp_affineLine_hasDerivAt hτ).deriv
  refine ⟨?_, ?_, ?_⟩
  · have h1 : AnalyticAt ℝ (fun τ : ℝ => A + τ • U) 0 := by fun_prop
    exact AnalyticAt.fun_comp (NormedSpace.exp_analytic (𝕂 := ℝ) _) h1
  · rw [(exp_affineLine_hasDerivAt h0).deriv]
    exact norm_expDeriv_zero_sub_le hA
  · rw [hd.deriv_eq, (expDeriv_hasDerivAt h0).deriv]
    exact norm_expDeriv2_zero_le hA
end ExpLine
section Jets
def TwoJet {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E) (a b c : E) : Prop :=
  AnalyticAt ℝ f 0 ∧ f 0 = a ∧ deriv f 0 = b ∧ deriv (deriv f) 0 = c
variable {E G A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
theorem TwoJet.const (a : E) : TwoJet (fun _ : ℝ => a) a 0 0 := by
  refine ⟨analyticAt_const, rfl, by simp, by simp⟩
theorem TwoJet.map_clm {f : ℝ → E} {a b c : E} (hf : TwoJet f a b c) (L : E →L[ℝ] G) :
    TwoJet (fun τ => L (f τ)) (L a) (L b) (L c) := by
  obtain ⟨fa, rfl, rfl, rfl⟩ := hf
  have h1 : deriv (fun τ => L (f τ)) =ᶠ[𝓝 0] fun τ => L (deriv f τ) := by
    filter_upwards [fa.eventually_analyticAt] with τ hτ
    exact (L.hasFDerivAt.comp_hasDerivAt τ hτ.differentiableAt.hasDerivAt).deriv
  refine ⟨L.analyticAt _ |>.comp fa, rfl, h1.self_of_nhds, ?_⟩
  rw [h1.deriv_eq]
  exact (L.hasFDerivAt.comp_hasDerivAt 0 fa.deriv.differentiableAt.hasDerivAt).deriv
theorem TwoJet.add {f g : ℝ → E} {a b c a' b' c' : E} (hf : TwoJet f a b c) (hg : TwoJet g a' b' c') :
    TwoJet (fun τ => f τ + g τ) (a + a') (b + b') (c + c') := by
  obtain ⟨fa, rfl, rfl, rfl⟩ := hf
  obtain ⟨ga, rfl, rfl, rfl⟩ := hg
  have h1 : deriv (fun τ => f τ + g τ) =ᶠ[𝓝 0] fun τ => deriv f τ + deriv g τ := by
    filter_upwards [fa.eventually_analyticAt, ga.eventually_analyticAt] with τ h h'
    exact (h.differentiableAt.hasDerivAt.add h'.differentiableAt.hasDerivAt).deriv
  refine ⟨fa.add ga, rfl, h1.self_of_nhds, ?_⟩
  rw [h1.deriv_eq]
  exact (fa.deriv.differentiableAt.hasDerivAt.add ga.deriv.differentiableAt.hasDerivAt).deriv
theorem TwoJet.smul {f : ℝ → E} {a b c : E} (hf : TwoJet f a b c) (r : ℝ) :
    TwoJet (fun τ => r • f τ) (r • a) (r • b) (r • c) :=
  hf.map_clm (r • ContinuousLinearMap.id ℝ E)
theorem TwoJet.sum {ι : Type} (s : Finset ι) {f : ι → ℝ → E} {a b c : ι → E}
    (h : ∀ i ∈ s, TwoJet (f i) (a i) (b i) (c i)) :
    TwoJet (fun τ => ∑ i ∈ s, f i τ) (∑ i ∈ s, a i) (∑ i ∈ s, b i) (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using TwoJet.const (0 : E)
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
theorem TwoJet.mul {f g : ℝ → A} {a b c a' b' c' : A} (hf : TwoJet f a b c) (hg : TwoJet g a' b' c') :
    TwoJet (fun τ => f τ * g τ) (a * a') (b * a' + a * b') (c * a' + b * b' + (b * b' + a * c')) := by
  obtain ⟨fa, rfl, rfl, rfl⟩ := hf
  obtain ⟨ga, rfl, rfl, rfl⟩ := hg
  have h1 : deriv (fun τ => f τ * g τ) =ᶠ[𝓝 0] fun τ => deriv f τ * g τ + f τ * deriv g τ := by
    filter_upwards [fa.eventually_analyticAt, ga.eventually_analyticAt] with τ h h'
    exact (h.differentiableAt.hasDerivAt.mul h'.differentiableAt.hasDerivAt).deriv
  refine ⟨fa.mul ga, rfl, h1.self_of_nhds, ?_⟩
  rw [h1.deriv_eq]
  have d1 := fa.deriv.differentiableAt.hasDerivAt
  have d2 := ga.deriv.differentiableAt.hasDerivAt
  have e1 := fa.differentiableAt.hasDerivAt
  have e2 := ga.differentiableAt.hasDerivAt
  exact ((d1.mul e2).add (e1.mul d2)).deriv
theorem TwoJet.unique {f : ℝ → E} {a b c a' b' c' : E} (hf : TwoJet f a b c) (hg : TwoJet f a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  obtain ⟨-, rfl, rfl, rfl⟩ := hf
  obtain ⟨-, rfl, rfl, rfl⟩ := hg
  exact ⟨rfl, rfl, rfl⟩
def reCLM : ℍ[ℝ] →L[ℝ] ℝ := ⟨QuaternionAlgebra.reₗ _ _ _, Quaternion.continuous_re⟩
theorem reCLM_apply (q : ℍ[ℝ]) : reCLM q = q.re := rfl
def starCLM : ℍ[ℝ] →L[ℝ] ℍ[ℝ] :=
  ⟨{ toFun := star, map_add' := star_add, map_smul' := fun r q => quaternion_star_real_smul r q }, continuous_star⟩
theorem starCLM_apply (q : ℍ[ℝ]) : starCLM q = star q := rfl
theorem abs_re_le_norm (q : ℍ[ℝ]) : |q.re| ≤ ‖q‖ := by apply _root_.YangMills.Construction.BlockAverages.VariationRates.quaternion_abs_re_le_norm <;> assumption
theorem re_mul_star_self_eq_sq (q : ℍ[ℝ]) : (q * star q).re = ‖q‖ ^ 2 := by
  rw [Quaternion.self_mul_star, Quaternion.re_coe, Quaternion.normSq_eq_norm_mul_self]
  ring
theorem fit_second_deriv_ineq {N0 N1 N2 r2 X Y a δ e B c z : ℝ} (hlo : 1 / 2 ≤ N0) (hhi : N0 ≤ 1 + δ) (hδ0 : 0 ≤ δ)
    (hδ2 : δ ≤ 1 / 2) (he0 : 0 ≤ e) (hB0 : 0 ≤ B) (ha0 : 0 ≤ a) (hz0 : 0 ≤ z) (hzc : z ≤ c)
    (F1 : N0 * N1 = Y) (F2 : N0 * N2 + N1 * N1 = X + a ^ 2) (hale : a ≤ c + e) (halo : z ≤ e + a)
    (hb : |Y| ≤ e + a * δ) (hc2 : |X - N0 * r2| ≤ 2 * δ * B) :
    z ^ 2 - (2 * c * e + δ * (c + e) ^ 2 + 8 * (δ * (c + e) + e) ^ 2 + 4 * δ * B) ≤ N2 - r2 := by
  have hNpos : 0 < N0 := by linarith
  have hA : z ^ 2 - 2 * c * e ≤ a ^ 2 := by
    have h4 : z * e ≤ c * e := mul_le_mul_of_nonneg_right hzc he0
    rcases le_total z e with h | h
    · have h5 : z * (z - 2 * e) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hz0 (by linarith)
      nlinarith [sq_nonneg a]
    · have h5 : (z - e) ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
      nlinarith [sq_nonneg e]
  have hN1b : N1 * N1 ≤ 4 * (e + a * δ) ^ 2 := by
    have h1 : |N0 * N1| ≤ e + a * δ := by rw [F1]; exact hb
    rw [abs_mul, abs_of_nonneg hNpos.le] at h1
    have h3 : 0 ≤ |N1| := abs_nonneg _
    have h2 : |N1| ≤ 2 * (e + a * δ) := by
      have : 1 / 2 * |N1| ≤ N0 * |N1| := mul_le_mul_of_nonneg_right hlo h3
      linarith
    have h4 : |N1| ^ 2 ≤ (2 * (e + a * δ)) ^ 2 := pow_le_pow_left₀ h3 h2 2
    rw [sq_abs] at h4
    nlinarith
  set W : ℝ := 4 * (e + a * δ) ^ 2 + 2 * δ * B with hW
  have hW0 : 0 ≤ W := by positivity
  have hNd : a ^ 2 - W ≤ N0 * (N2 - r2) := by
    have h1 := (abs_le.1 hc2).1
    have : N0 * (N2 - r2) = X + a ^ 2 - N1 * N1 - N0 * r2 := by linarith
    rw [this, hW]
    linarith
  have hd1 : (a ^ 2 - W) / N0 ≤ N2 - r2 := by
    rw [div_le_iff₀ hNpos]
    linarith
  have h1 : a ^ 2 * (1 - δ) ≤ a ^ 2 / N0 := by
    rw [le_div_iff₀ hNpos]
    have h2 : (1 - δ) * N0 ≤ 1 := by nlinarith
    have h3 : 0 ≤ a ^ 2 := by positivity
    have h4 := mul_le_mul_of_nonneg_left h2 h3
    linarith
  have h2 : W / N0 ≤ 2 * W := by
    rw [div_le_iff₀ hNpos]
    nlinarith
  have h3 : a ^ 2 * (1 - δ) - 2 * W ≤ N2 - r2 := by
    rw [sub_div] at hd1
    linarith
  have h4 : a ^ 2 * δ ≤ δ * (c + e) ^ 2 := by
    have h5 : a ^ 2 ≤ (c + e) ^ 2 := pow_le_pow_left₀ ha0 hale 2
    have := mul_le_mul_of_nonneg_left h5 hδ0
    linarith
  have h5 : (e + a * δ) ^ 2 ≤ (δ * (c + e) + e) ^ 2 := by
    have h6 : a * δ ≤ (c + e) * δ := mul_le_mul_of_nonneg_right hale hδ0
    have h7 : 0 ≤ e + a * δ := by positivity
    exact pow_le_pow_left₀ h7 (by linarith) 2
  have h6 : W ≤ 4 * (δ * (c + e) + e) ^ 2 + 2 * δ * B := by rw [hW]; linarith
  nlinarith
theorem fit_second_deriv_lower {m : ℝ → ℍ[ℝ]} {m0 m1 m2 cv : ℍ[ℝ]} {δ e B c : ℝ} (hm : TwoJet m m0 m1 m2)
    (hδ : ‖m0 - 1‖ ≤ δ) (hδ2 : δ ≤ 1 / 2) (hre : cv.re = 0) (hc : ‖cv‖ ≤ c) (he : ‖m1 - cv‖ ≤ e)
    (hB : ‖m2‖ ≤ B) :
    AnalyticAt ℝ (fun τ => ‖m τ‖ - (m τ).re) 0 ∧
      ‖cv‖ ^ 2 - (2 * c * e + δ * (c + e) ^ 2 + 8 * (δ * (c + e) + e) ^ 2 + 4 * δ * B) ≤
        deriv (deriv fun τ => ‖m τ‖ - (m τ).re) 0 := by
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hδ
  have he0 : 0 ≤ e := (norm_nonneg _).trans he
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hB
  have hN1 : |‖m0‖ - 1| ≤ δ := by
    have := abs_norm_sub_norm_le m0 1
    rw [norm_one] at this
    exact this.trans hδ
  have hNlo : 1 / 2 ≤ ‖m0‖ := by
    have := (abs_le.1 hN1).1
    linarith
  have hNhi : ‖m0‖ ≤ 1 + δ := by
    have := (abs_le.1 hN1).2
    linarith
  have hm00 : m0 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hNlo
    norm_num at hNlo
  have hmA : AnalyticAt ℝ m 0 := hm.1
  have hval : m 0 = m0 := hm.2.1
  have hstar : TwoJet (fun τ => starCLM (m τ)) (starCLM m0) (starCLM m1) (starCLM m2) := hm.map_clm starCLM
  have hJ := hm.mul hstar
  have hu := hJ.map_clm reCLM
  have hne : ∀ᶠ τ in 𝓝 (0 : ℝ), m τ ≠ 0 := hmA.continuousAt.eventually_ne (by rw [hval]; exact hm00)
  have huA : AnalyticAt ℝ (fun τ => reCLM (m τ * starCLM (m τ))) 0 := hu.1
  have hupos : 0 < reCLM (m 0 * starCLM (m 0)) := by
    rw [reCLM_apply, starCLM_apply, re_mul_star_self_eq_sq, hval]
    positivity
  have hNA : AnalyticAt ℝ (fun τ => ‖m τ‖) 0 := by
    have h1 : AnalyticAt ℝ (fun τ => Real.exp (Real.log (reCLM (m τ * starCLM (m τ))) / 2)) 0 :=
      ((huA.log hupos).div_const).rexp'
    refine h1.congr ?_
    filter_upwards [hne] with τ hτ
    rw [reCLM_apply, starCLM_apply, re_mul_star_self_eq_sq, Real.log_pow]
    have hp : 0 < ‖m τ‖ := norm_pos_iff.2 hτ
    have : ((2 : ℕ) : ℝ) * Real.log ‖m τ‖ / 2 = Real.log ‖m τ‖ := by push_cast; ring
    rw [this, Real.exp_log hp]
  set N1 : ℝ := deriv (fun τ => ‖m τ‖) 0 with hN1def
  set N2 : ℝ := deriv (deriv fun τ => ‖m τ‖) 0 with hN2def
  have hNJ : TwoJet (fun τ => ‖m τ‖) ‖m0‖ N1 N2 := ⟨hNA, by simp [hval], rfl, rfl⟩
  have hNN := hNJ.mul hNJ
  have hsame : (fun τ => ‖m τ‖ * ‖m τ‖) = fun τ => reCLM (m τ * starCLM (m τ)) := by
    funext τ
    rw [reCLM_apply, starCLM_apply, re_mul_star_self_eq_sq]
    ring
  rw [hsame] at hNN
  obtain ⟨-, E1, E2⟩ := hNN.unique hu
  simp only [map_add, reCLM_apply, starCLM_apply, Quaternion.re_add] at E1 E2
  have hr := hm.map_clm reCLM
  have hfit : TwoJet (fun τ => ‖m τ‖ - (m τ).re) (‖m0‖ - m0.re) (N1 - m1.re) (N2 - m2.re) := by
    have h := hNJ.add (hr.smul (-1))
    simp only [reCLM_apply, neg_smul, one_smul, ← sub_eq_add_neg] at h
    exact h
  refine ⟨hfit.1, ?_⟩
  rw [hfit.2.2.2]
  have s1 : (m0 * star m1).re = (m1 * star m0).re := by
    rw [← Quaternion.re_star, star_mul, star_star]
  have s2 : (m0 * star m2).re = (m2 * star m0).re := by
    rw [← Quaternion.re_star, star_mul, star_star]
  have s3 : (m1 * star m1).re = ‖m1‖ ^ 2 := re_mul_star_self_eq_sq m1
  have F1 : ‖m0‖ * N1 = (m1 * star m0).re := by linarith
  have F2 : ‖m0‖ * N2 + N1 * N1 = (m2 * star m0).re + ‖m1‖ ^ 2 := by linarith
  have hale : ‖m1‖ ≤ c + e := by
    have h := norm_add_le (m1 - cv) cv
    rw [sub_add_cancel] at h
    linarith
  have halo : ‖cv‖ ≤ e + ‖m1‖ := by
    have h := norm_add_le (cv - m1) m1
    rw [sub_add_cancel, norm_sub_rev cv m1] at h
    linarith
  have hre1 : |m1.re| ≤ e := by
    have : (m1 - cv).re = m1.re := by simp [hre]
    rw [← this]
    exact (abs_re_le_norm _).trans he
  have hb : |(m1 * star m0).re| ≤ e + ‖m1‖ * δ := by
    have e1 : (m1 * star m0).re = m1.re + (m1 * star (m0 - 1)).re := by
      simp only [star_sub, star_one, mul_sub, mul_one, Quaternion.re_sub]
      ring
    rw [e1]
    refine (abs_add_le _ _).trans (add_le_add hre1 ?_)
    refine (abs_re_le_norm _).trans ?_
    rw [norm_mul, norm_star]
    exact mul_le_mul_of_nonneg_left hδ (norm_nonneg _)
  have hc2 : |(m2 * star m0).re - ‖m0‖ * m2.re| ≤ 2 * δ * B := by
    have e1 : (m2 * star m0).re - ‖m0‖ * m2.re = (m2 * star (m0 - (‖m0‖ : ℍ[ℝ]))).re := by
      simp only [star_sub, mul_sub, Quaternion.re_sub, Quaternion.star_coe, Quaternion.re_mul,
        Quaternion.re_coe, Quaternion.imI_coe, Quaternion.imJ_coe, Quaternion.imK_coe]
      ring
    rw [e1]
    refine (abs_re_le_norm _).trans ?_
    rw [norm_mul, norm_star]
    have h1 : ‖m0 - (‖m0‖ : ℍ[ℝ])‖ ≤ 2 * δ := by
      have h2 : m0 - (‖m0‖ : ℍ[ℝ]) = (m0 - 1) + (((1 - ‖m0‖ : ℝ)) : ℍ[ℝ]) := by
        rw [Quaternion.coe_sub, Quaternion.coe_one]
        abel
      rw [h2]
      refine (norm_add_le _ _).trans ?_
      rw [Quaternion.norm_coe, Real.norm_eq_abs, abs_sub_comm]
      linarith
    calc ‖m2‖ * ‖m0 - (‖m0‖ : ℍ[ℝ])‖ ≤ B * (2 * δ) :=
          mul_le_mul hB h1 (norm_nonneg _) hB0
      _ = 2 * δ * B := by ring
  exact fit_second_deriv_ineq hNlo hNhi hδ0 hδ2 he0 hB0 (norm_nonneg _) (norm_nonneg _) hc F1 F2 hale halo hb hc2
end Jets
section Steps
variable {F : BlockFrame} {j : ℕ}
def bondOfStep (x : F.Site j) (st : PathStep) : F.Site j × Fin 4 :=
  if st.2 then (x, st.1) else (x - unitStep j st.1, st.1)
def AllSteps (R : F.Site j → PathStep → Prop) : F.Site j → List PathStep → Prop
  | _, [] => True
  | x, st :: r => R x st ∧ AllSteps R (x + stepDisplacement j st) r
theorem adjointAction_mul_coe (g : UnitQuaternion) (w : ℍ[ℝ]) : adjointAction g w * (g : ℍ[ℝ]) = (g : ℍ[ℝ]) * w := by
  have h : ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (g : ℍ[ℝ]) = 1 := by
    rw [← Submonoid.coe_mul, inv_mul_cancel]
    rfl
  simp only [adjointAction]
  rw [mul_assoc, h, mul_one]
theorem norm_adjointAction (g : UnitQuaternion) (w : ℍ[ℝ]) : ‖adjointAction g w‖ = ‖w‖ := by apply _root_.YangMills.Construction.BlockLines.norm_adjointAction <;> assumption
theorem re_adjointAction (g : UnitQuaternion) (w : ℍ[ℝ]) : (adjointAction g w).re = w.re := by apply _root_.YangMills.Construction.PlaquetteLinearization.adjointAction_re <;> assumption
theorem re_imaginary (a : imaginaryQuaternions) : (a : ℍ[ℝ]).re = 0 := a.2
theorem star_imaginary (a : imaginaryQuaternions) : star (a : ℍ[ℝ]) = - (a : ℍ[ℝ]) := by apply _root_.YangMills.Construction.GaugeMotions.star_coe_imaginary <;> assumption
theorem norm_linkValueVariation (X : F.GaugeField j) (v : F.Site j → Fin 4 → imaginaryQuaternions) (x : F.Site j)
    (st : PathStep) :
    ‖linkValueVariation X v x st‖ = ‖v (bondOfStep x st).1 (bondOfStep x st).2‖ := by
  rcases st with ⟨i, b⟩
  cases b
  · simp [linkValueVariation, bondOfStep, norm_adjointAction]
  · simp [linkValueVariation, bondOfStep]
theorem re_linkValueVariation (X : F.GaugeField j) (v : F.Site j → Fin 4 → imaginaryQuaternions) (x : F.Site j)
    (st : PathStep) :
    (linkValueVariation X v x st).re = 0 := by
  rcases st with ⟨i, b⟩
  cases b
  · simp [linkValueVariation, re_adjointAction, re_imaginary]
  · simp [linkValueVariation, re_imaginary]
theorem pathHolonomyVariation_bound {X : F.GaugeField j} {v : F.Site j → Fin 4 → imaginaryQuaternions} {q : ℝ}
    {x : F.Site j} {l : List PathStep}
    (h : AllSteps (fun x st => ‖v (bondOfStep x st).1 (bondOfStep x st).2‖ ≤ q) x l) :
    ‖pathHolonomyVariation X v x l‖ ≤ l.length * q ∧ (pathHolonomyVariation X v x l).re = 0 := by
  induction l generalizing x with
  | nil => simp [pathHolonomyVariation]
  | cons st r ih =>
    obtain ⟨h1, h2⟩ := ih h.2
    constructor
    · simp only [pathHolonomyVariation, List.length_cons]
      refine (norm_add_le _ _).trans ?_
      rw [norm_adjointAction, norm_linkValueVariation]
      push_cast
      have := h.1
      linarith
    · simp only [pathHolonomyVariation, Quaternion.re_add, re_adjointAction, re_linkValueVariation, h2, add_zero]
def JetStep (X : ℝ → F.GaugeField j) (v : F.Site j → Fin 4 → imaginaryQuaternions) (ρ q : ℝ) (x : F.Site j)
    (st : PathStep) : Prop :=
  ∃ f1 f2 : ℍ[ℝ], TwoJet (fun τ => ((linkValue (X τ) x st : UnitQuaternion) : ℍ[ℝ]))
      ((linkValue (X 0) x st : UnitQuaternion) : ℍ[ℝ]) f1 f2 ∧
    ‖f1‖ ≤ 4 * q ∧ ‖f2‖ ≤ (4 * q) ^ 2 ∧
    ‖f1 - linkValueVariation (X 0) v x st * ((linkValue (X 0) x st : UnitQuaternion) : ℍ[ℝ])‖ ≤ 6 * ρ * q
theorem pathHolonomy_jet {X : ℝ → F.GaugeField j} {v : F.Site j → Fin 4 → imaginaryQuaternions} {ρ q : ℝ}
    (hq : 0 ≤ q) {x : F.Site j} {l : List PathStep} (h : AllSteps (JetStep X v ρ q) x l) :
    ∃ H1 H2 : ℍ[ℝ], TwoJet (fun τ => ((pathHolonomy (X τ) x l : UnitQuaternion) : ℍ[ℝ]))
        ((pathHolonomy (X 0) x l : UnitQuaternion) : ℍ[ℝ]) H1 H2 ∧
      ‖H1‖ ≤ l.length * (4 * q) ∧ ‖H2‖ ≤ (l.length * (4 * q)) ^ 2 ∧
      ‖H1 - pathHolonomyVariation (X 0) v x l * ((pathHolonomy (X 0) x l : UnitQuaternion) : ℍ[ℝ])‖ ≤
        l.length * (6 * ρ * q) := by
  induction l generalizing x with
  | nil =>
    refine ⟨0, 0, TwoJet.const _, by simp, by simp, by simp [pathHolonomyVariation]⟩
  | cons st r ih =>
    obtain ⟨f1, f2, jf, b1, b2, b3⟩ := h.1
    obtain ⟨R1, R2, jr, c1, c2, c3⟩ := ih h.2
    have hj := jf.mul jr
    set f0 : UnitQuaternion := linkValue (X 0) x st with hf0
    set R0 : UnitQuaternion := pathHolonomy (X 0) (x + stepDisplacement j st) r with hR0
    have nf : ‖(f0 : ℍ[ℝ])‖ = 1 := _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion _
    have nr : ‖(R0 : ℍ[ℝ])‖ = 1 := _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion _
    refine ⟨f1 * R0 + f0 * R1, f2 * R0 + f1 * R1 + (f1 * R1 + f0 * R2), hj, ?_, ?_, ?_⟩
    · simp only [List.length_cons]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, nf, nr]
      push_cast
      linarith
    · simp only [List.length_cons]
      have e1 : ‖f2 * R0‖ ≤ (4 * q) ^ 2 := by rw [norm_mul, nr, mul_one]; exact b2
      have e2 : ‖f1 * R1‖ ≤ 4 * q * (r.length * (4 * q)) := by
        rw [norm_mul]
        exact mul_le_mul b1 c1 (norm_nonneg _) (by positivity)
      have e3 : ‖(f0 : ℍ[ℝ]) * R2‖ ≤ (r.length * (4 * q)) ^ 2 := by rw [norm_mul, nf, one_mul]; exact c2
      refine (norm_add_le _ _).trans ?_
      have e4 := norm_add_le (f2 * (R0 : ℍ[ℝ])) (f1 * R1)
      have e5 := norm_add_le (f1 * R1) ((f0 : ℍ[ℝ]) * R2)
      have e6 : (((r.length + 1 : ℕ) : ℝ) * (4 * q)) ^ 2 =
          (4 * q) ^ 2 + 4 * q * (r.length * (4 * q)) + (4 * q * (r.length * (4 * q)) + (r.length * (4 * q)) ^ 2) := by
        push_cast
        ring
      rw [e6]
      linarith
    · have e : f1 * R0 + f0 * R1 - pathHolonomyVariation (X 0) v x (st :: r) *
            ((pathHolonomy (X 0) x (st :: r) : UnitQuaternion) : ℍ[ℝ]) =
          (f1 - linkValueVariation (X 0) v x st * f0) * R0 +
            f0 * (R1 - pathHolonomyVariation (X 0) v (x + stepDisplacement j st) r * R0) := by
        have e1 : ((pathHolonomy (X 0) x (st :: r) : UnitQuaternion) : ℍ[ℝ]) = f0 * R0 := rfl
        have e2 := adjointAction_mul_coe f0 (pathHolonomyVariation (X 0) v (x + stepDisplacement j st) r)
        have e3 : pathHolonomyVariation (X 0) v x (st :: r) =
            linkValueVariation (X 0) v x st +
              adjointAction f0 (pathHolonomyVariation (X 0) v (x + stepDisplacement j st) r) := rfl
        have e4 : adjointAction f0 (pathHolonomyVariation (X 0) v (x + stepDisplacement j st) r) * ((f0 : ℍ[ℝ]) * R0) =
            f0 * (pathHolonomyVariation (X 0) v (x + stepDisplacement j st) r * R0) := by
          rw [← mul_assoc, e2, mul_assoc]
        rw [e1, e3, add_mul, mul_sub, sub_mul, e4, mul_assoc (linkValueVariation (X 0) v x st)]
        abel
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, nf, nr, mul_one, one_mul]
      simp only [List.length_cons]
      push_cast
      linarith
theorem expUnit_zero : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
end Steps
section Chart
variable {F : BlockFrame}
def baseChart (V : F.GaugeField F.top) : F.GaugeField F.depth := chartedField (fun _ _ => 0) V
theorem chartedField_eq {S : Finset F.Cell} {w : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (hw : SupportedOnChords S w) (V : F.GaugeField F.top)
    (x : F.Site F.depth) (i : Fin 4) : chartedField w V x i = expUnit (w x i) * baseChart V x i := by
  classical
  simp only [baseChart, chartedField]
  by_cases h1 : IsCrossingBond (x, i)
  · simp [h1, expUnit_zero]
  · by_cases h2 : IsAxialTreeBond (x, i)
    · have h3 : (x, i) ∉ chordBonds S := by simp [chordBonds, h2]
      have h4 : w x i = 0 := hw _ h3
      simp [h1, h2, h4, expUnit_zero]
    · simp [h1, h2, expUnit_zero]
theorem supportedOnChords_chartLineShift {S : Finset F.Cell} {w dw : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (hw : SupportedOnChords S w) (hd : SupportedOnChords S dw) (τ : ℝ) :
    SupportedOnChords S (chartLineShift w dw τ) := by
  intro b hb
  simp [chartLineShift, hw b hb, hd b hb]
theorem chartLineShift_zero (w dw : F.Site F.depth → Fin 4 → imaginaryQuaternions) : chartLineShift w dw 0 = w := by
  funext x i
  simp [chartLineShift]
theorem coe_chartedField_shift {S : Finset F.Cell} {w dw : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (hw : SupportedOnChords S w) (hd : SupportedOnChords S dw)
    (V : F.GaugeField F.top) (τ : ℝ) (x : F.Site F.depth) (i : Fin 4) :
    ((chartedField (chartLineShift w dw τ) V x i : UnitQuaternion) : ℍ[ℝ]) =
      NormedSpace.exp ((w x i : ℍ[ℝ]) + τ • (dw x i : ℍ[ℝ])) * (baseChart V x i : ℍ[ℝ]) := by
  rw [chartedField_eq (supportedOnChords_chartLineShift hw hd τ)]
  rfl
theorem coe_chartedField_shift_inv {S : Finset F.Cell} {w dw : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (hw : SupportedOnChords S w) (hd : SupportedOnChords S dw) (V : F.GaugeField F.top) (τ : ℝ)
    (x : F.Site F.depth) (i : Fin 4) :
    (((chartedField (chartLineShift w dw τ) V x i)⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
      star (baseChart V x i : ℍ[ℝ]) *
        NormedSpace.exp (-(w x i : ℍ[ℝ]) + τ • (-(dw x i : ℍ[ℝ]))) := by
  rw [coe_unitQuaternion_inv, coe_chartedField_shift hw hd, star_mul, NormedSpace.star_exp, star_add, star_imaginary,
    quaternion_star_real_smul, star_imaginary]
theorem jetStep_chart {S : Finset F.Cell} {w dw : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (hw : SupportedOnChords S w) (hd : SupportedOnChords S dw)
    (V : F.GaugeField F.top) {ρ q : ℝ} (hρ1 : ρ ≤ 1) (hq : 0 ≤ q) (x : F.Site F.depth) (st : PathStep)
    (h1 : ‖w (bondOfStep x st).1 (bondOfStep x st).2‖ ≤ ρ) (h2 : ‖dw (bondOfStep x st).1 (bondOfStep x st).2‖ ≤ q) :
    JetStep (fun τ => chartedField (chartLineShift w dw τ) V) dw ρ q x st := by
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans h1
  rcases st with ⟨i, b⟩
  cases b
  · simp only [bondOfStep, Bool.false_eq_true, if_false] at h1 h2
    set x' := x - unitStep F.depth i with hx'
    have hA : ‖-(w x' i : ℍ[ℝ])‖ ≤ ρ := by rw [norm_neg]; exact h1
    have hU : ‖-(dw x' i : ℍ[ℝ])‖ ≤ q := by rw [norm_neg]; exact h2
    obtain ⟨g1, g2, g3⟩ := exp_affineLine_jet (-(w x' i : ℍ[ℝ])) (-(dw x' i : ℍ[ℝ])) (hA.trans hρ1)
    set E1 := deriv (fun τ : ℝ => NormedSpace.exp (-(w x' i : ℍ[ℝ]) + τ • (-(dw x' i : ℍ[ℝ])))) 0 with hE1
    set E2 := deriv (deriv fun τ : ℝ => NormedSpace.exp (-(w x' i : ℍ[ℝ]) + τ • (-(dw x' i : ℍ[ℝ])))) 0 with hE2
    set B : ℍ[ℝ] := star (baseChart V x' i : ℍ[ℝ]) with hB
    have nB : ‖B‖ = 1 := by rw [hB, norm_star]; exact _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion _
    have j0 : TwoJet (fun τ : ℝ => NormedSpace.exp (-(w x' i : ℍ[ℝ]) + τ • (-(dw x' i : ℍ[ℝ]))))
        (NormedSpace.exp (-(w x' i : ℍ[ℝ]))) E1 E2 := ⟨g1, by simp, rfl, rfl⟩
    have j1 := (TwoJet.const B).mul j0
    simp only [zero_mul, mul_zero, add_zero, zero_add] at j1
    have e0 : ∀ τ : ℝ, ((linkValue (chartedField (chartLineShift w dw τ) V) x (i, false) : UnitQuaternion) : ℍ[ℝ]) =
        B * NormedSpace.exp (-(w x' i : ℍ[ℝ]) + τ • (-(dw x' i : ℍ[ℝ]))) :=
      fun τ => coe_chartedField_shift_inv hw hd V τ x' i
    have e00 : ((linkValue (chartedField (chartLineShift w dw 0) V) x (i, false) : UnitQuaternion) : ℍ[ℝ]) =
        B * NormedSpace.exp (-(w x' i : ℍ[ℝ])) := by rw [e0]; simp
    have hE1b : ‖E1 + (dw x' i : ℍ[ℝ])‖ ≤ 3 * ρ * q := by
      have : E1 + (dw x' i : ℍ[ℝ]) = E1 - (-(dw x' i : ℍ[ℝ])) := by abel
      rw [this]
      refine g2.trans ?_
      exact mul_le_mul (by linarith) hU (norm_nonneg _) (by positivity)
    refine ⟨B * E1, B * E2, ?_, ?_, ?_, ?_⟩
    · have hf : (fun τ : ℝ => ((linkValue (chartedField (chartLineShift w dw τ) V) x (i, false) : UnitQuaternion) : ℍ[ℝ])) =
          fun τ => B * NormedSpace.exp (-(w x' i : ℍ[ℝ]) + τ • (-(dw x' i : ℍ[ℝ]))) := funext e0
      simp only []
      rw [hf, e00]
      exact j1
    · rw [norm_mul, nB, one_mul]
      have h3 : ‖E1‖ ≤ ‖E1 + (dw x' i : ℍ[ℝ])‖ + ‖(dw x' i : ℍ[ℝ])‖ := by
        have := norm_add_le (E1 + (dw x' i : ℍ[ℝ])) (-(dw x' i : ℍ[ℝ]))
        simpa using this
      have h4 : ρ * q ≤ q := mul_le_of_le_one_left hq hρ1
      have h5 : ‖(dw x' i : ℍ[ℝ])‖ ≤ q := h2
      nlinarith
    · rw [norm_mul, nB, one_mul]
      refine g3.trans ?_
      have h5 : ‖(-(dw x' i : ℍ[ℝ]))‖ ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hU 2
      nlinarith [sq_nonneg q]
    · set g : UnitQuaternion := (chartedField (chartLineShift w dw 0) V x' i)⁻¹ with hg
      have e1 : ((linkValue (chartedField (chartLineShift w dw 0) V) x (i, false) : UnitQuaternion) : ℍ[ℝ]) =
          (g : ℍ[ℝ]) := rfl
      have e2 : linkValueVariation (chartedField (chartLineShift w dw 0) V) dw x (i, false) =
          - adjointAction g (dw x' i : ℍ[ℝ]) := rfl
      have e3 : (g : ℍ[ℝ]) = B * NormedSpace.exp (-(w x' i : ℍ[ℝ])) := by rw [← e1, e00]
      simp only []
      rw [e1, e2, neg_mul, adjointAction_mul_coe, sub_neg_eq_add, e3, mul_assoc, ← mul_add, norm_mul, nB, one_mul]
      have h6 : E1 + NormedSpace.exp (-(w x' i : ℍ[ℝ])) * (dw x' i : ℍ[ℝ]) =
          (E1 + (dw x' i : ℍ[ℝ])) + (NormedSpace.exp (-(w x' i : ℍ[ℝ])) - 1) * (dw x' i : ℍ[ℝ]) := by
        noncomm_ring
      rw [h6]
      refine (norm_add_le _ _).trans ?_
      have h7 : ‖(NormedSpace.exp (-(w x' i : ℍ[ℝ])) - 1) * (dw x' i : ℍ[ℝ])‖ ≤ 3 * ρ * q := by
        rw [norm_mul]
        have h8 := norm_exp_sub_one_le (hA.trans hρ1)
        exact mul_le_mul (h8.trans (by linarith)) h2 (norm_nonneg _) (by positivity)
      linarith
  · simp only [bondOfStep, if_true] at h1 h2
    have hA : ‖(w x i : ℍ[ℝ])‖ ≤ ρ := h1
    have hU : ‖(dw x i : ℍ[ℝ])‖ ≤ q := h2
    obtain ⟨g1, g2, g3⟩ := exp_affineLine_jet (w x i : ℍ[ℝ]) (dw x i : ℍ[ℝ]) (hA.trans hρ1)
    set E1 := deriv (fun τ : ℝ => NormedSpace.exp ((w x i : ℍ[ℝ]) + τ • (dw x i : ℍ[ℝ]))) 0 with hE1
    set E2 := deriv (deriv fun τ : ℝ => NormedSpace.exp ((w x i : ℍ[ℝ]) + τ • (dw x i : ℍ[ℝ]))) 0 with hE2
    set B : ℍ[ℝ] := (baseChart V x i : ℍ[ℝ]) with hB
    have nB : ‖B‖ = 1 := _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion _
    have j0 : TwoJet (fun τ : ℝ => NormedSpace.exp ((w x i : ℍ[ℝ]) + τ • (dw x i : ℍ[ℝ])))
        (NormedSpace.exp (w x i : ℍ[ℝ])) E1 E2 := ⟨g1, by simp, rfl, rfl⟩
    have j1 := j0.mul (TwoJet.const B)
    simp only [zero_mul, mul_zero, add_zero, zero_add] at j1
    have e0 : ∀ τ : ℝ, ((linkValue (chartedField (chartLineShift w dw τ) V) x (i, true) : UnitQuaternion) : ℍ[ℝ]) =
        NormedSpace.exp ((w x i : ℍ[ℝ]) + τ • (dw x i : ℍ[ℝ])) * B :=
      fun τ => coe_chartedField_shift hw hd V τ x i
    have e00 : ((linkValue (chartedField (chartLineShift w dw 0) V) x (i, true) : UnitQuaternion) : ℍ[ℝ]) =
        NormedSpace.exp (w x i : ℍ[ℝ]) * B := by rw [e0]; simp
    have hE1b : ‖E1 - (dw x i : ℍ[ℝ])‖ ≤ 3 * ρ * q :=
      g2.trans (mul_le_mul (by linarith) hU (norm_nonneg _) (by positivity))
    refine ⟨E1 * B, E2 * B, ?_, ?_, ?_, ?_⟩
    · have hf : (fun τ : ℝ => ((linkValue (chartedField (chartLineShift w dw τ) V) x (i, true) : UnitQuaternion) : ℍ[ℝ])) =
          fun τ => NormedSpace.exp ((w x i : ℍ[ℝ]) + τ • (dw x i : ℍ[ℝ])) * B := funext e0
      simp only []
      rw [hf, e00]
      exact j1
    · rw [norm_mul, nB, mul_one]
      have h3 : ‖E1‖ ≤ ‖E1 - (dw x i : ℍ[ℝ])‖ + ‖(dw x i : ℍ[ℝ])‖ := by
        have := norm_add_le (E1 - (dw x i : ℍ[ℝ])) (dw x i : ℍ[ℝ])
        simpa using this
      have h4 : ρ * q ≤ q := mul_le_of_le_one_left hq hρ1
      nlinarith
    · rw [norm_mul, nB, mul_one]
      refine g3.trans ?_
      have h5 : ‖(dw x i : ℍ[ℝ])‖ ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hU 2
      nlinarith [sq_nonneg q]
    · have e2 : linkValueVariation (chartedField (chartLineShift w dw 0) V) dw x (i, true) = (dw x i : ℍ[ℝ]) := rfl
      simp only []
      rw [e00, e2, ← mul_assoc, ← sub_mul, norm_mul, nB, mul_one]
      have h6 : E1 - (dw x i : ℍ[ℝ]) * NormedSpace.exp (w x i : ℍ[ℝ]) =
          (E1 - (dw x i : ℍ[ℝ])) - (dw x i : ℍ[ℝ]) * (NormedSpace.exp (w x i : ℍ[ℝ]) - 1) := by
        noncomm_ring
      rw [h6]
      refine (norm_sub_le _ _).trans ?_
      have h7 : ‖(dw x i : ℍ[ℝ]) * (NormedSpace.exp (w x i : ℍ[ℝ]) - 1)‖ ≤ 3 * ρ * q := by
        rw [norm_mul]
        have h8 := norm_exp_sub_one_le (hA.trans hρ1)
        have h9 : ‖(dw x i : ℍ[ℝ])‖ * ‖NormedSpace.exp (w x i : ℍ[ℝ]) - 1‖ ≤ q * (3 * ρ) :=
          mul_le_mul hU (h8.trans (by linarith)) (norm_nonneg _) hq
        linarith
      linarith
theorem norm_linkValue_sub_base_le {S : Finset F.Cell} {w : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (hw : SupportedOnChords S w)
    (V : F.GaugeField F.top) {ρ : ℝ} (hρ1 : ρ ≤ 1) (x : F.Site F.depth) (st : PathStep)
    (h1 : ‖w (bondOfStep x st).1 (bondOfStep x st).2‖ ≤ ρ) :
    ‖((linkValue (chartedField w V) x st : UnitQuaternion) : ℍ[ℝ]) -
        ((linkValue (baseChart V) x st : UnitQuaternion) : ℍ[ℝ])‖ ≤ 3 * ρ := by
  have key : ∀ y k, ‖w y k‖ ≤ ρ →
      ‖((chartedField w V y k : UnitQuaternion) : ℍ[ℝ]) - (baseChart V y k : ℍ[ℝ])‖ ≤ 3 * ρ := by
    intro y k h
    have hA : ‖(w y k : ℍ[ℝ])‖ ≤ ρ := h
    rw [chartedField_eq hw]
    have e : ((expUnit (w y k) * baseChart V y k : UnitQuaternion) : ℍ[ℝ]) - (baseChart V y k : ℍ[ℝ]) =
        (NormedSpace.exp (w y k : ℍ[ℝ]) - 1) * (baseChart V y k : ℍ[ℝ]) := by
      rw [sub_mul, one_mul]
      rfl
    rw [e, norm_mul, _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion, mul_one]
    have := norm_exp_sub_one_le (hA.trans hρ1)
    linarith
  rcases st with ⟨i, b⟩
  cases b
  · simp only [bondOfStep, Bool.false_eq_true, if_false] at h1
    have e : ((linkValue (chartedField w V) x (i, false) : UnitQuaternion) : ℍ[ℝ]) -
          ((linkValue (baseChart V) x (i, false) : UnitQuaternion) : ℍ[ℝ]) =
        star (((chartedField w V (x - unitStep F.depth i) i : UnitQuaternion) : ℍ[ℝ]) -
          (baseChart V (x - unitStep F.depth i) i : ℍ[ℝ])) := by
      rw [star_sub]
      rfl
    rw [e, norm_star]
    exact key _ _ h1
  · simp only [bondOfStep, if_true] at h1
    exact key _ _ h1
theorem norm_pathHolonomy_sub_base_le {S : Finset F.Cell} {w : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (hw : SupportedOnChords S w)
    (V : F.GaugeField F.top) {ρ : ℝ} (hρ1 : ρ ≤ 1) {x : F.Site F.depth} {l : List PathStep}
    (h : AllSteps (fun x st => ‖w (bondOfStep x st).1 (bondOfStep x st).2‖ ≤ ρ) x l) :
    ‖((pathHolonomy (chartedField w V) x l : UnitQuaternion) : ℍ[ℝ]) -
        ((pathHolonomy (baseChart V) x l : UnitQuaternion) : ℍ[ℝ])‖ ≤
      l.length * (3 * ρ) := by
  induction l generalizing x with
  | nil => simp [pathHolonomy]
  | cons st r ih =>
    have h1 := norm_linkValue_sub_base_le hw V hρ1 x st h.1
    have h2 := ih h.2
    set a : UnitQuaternion := linkValue (chartedField w V) x st
    set a' : UnitQuaternion := linkValue (baseChart V) x st
    set b : UnitQuaternion := pathHolonomy (chartedField w V) (x + stepDisplacement F.depth st) r
    set b' : UnitQuaternion := pathHolonomy (baseChart V) (x + stepDisplacement F.depth st) r
    have e : ((pathHolonomy (chartedField w V) x (st :: r) : UnitQuaternion) : ℍ[ℝ]) -
          ((pathHolonomy (baseChart V) x (st :: r) : UnitQuaternion) : ℍ[ℝ]) =
        ((a : ℍ[ℝ]) - a') * b + a' * ((b : ℍ[ℝ]) - b') := by
      have e1 : ((pathHolonomy (chartedField w V) x (st :: r) : UnitQuaternion) : ℍ[ℝ]) = (a : ℍ[ℝ]) * b := rfl
      have e2 : ((pathHolonomy (baseChart V) x (st :: r) : UnitQuaternion) : ℍ[ℝ]) = (a' : ℍ[ℝ]) * b' := rfl
      rw [e1, e2]
      noncomm_ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion, _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion, mul_one, one_mul]
    simp only [List.length_cons]
    push_cast
    linarith
end Chart
section Contours
open LatticePaths LatticeFractionalIntegration
variable {F : BlockFrame}
theorem stepDisplacement_eq_siteOfCoords (j : ℕ) (st : PathStep) :
    stepDisplacement (F := F) j st = siteOfCoords j (FlatPairing.stepDisplacement st) := by apply _root_.YangMills.Construction.BlockAverages.ChartCoordinates.stepDisplacement_eq_siteOfCoords <;> assumption
theorem add_siteOfCoords_add_step (x0 : F.Site F.depth) (u : Lattice4) (st : PathStep) :
    x0 + siteOfCoords F.depth u + stepDisplacement F.depth st =
      x0 + siteOfCoords F.depth (u + FlatPairing.stepDisplacement st) := by
  rw [stepDisplacement_eq_siteOfCoords, siteOfCoords_add, add_assoc]
theorem pathHolonomy_append_at (X : F.GaugeField F.depth) (x0 : F.Site F.depth) (u : Lattice4)
    (l l' : List PathStep) :
    pathHolonomy X (x0 + siteOfCoords F.depth u) (l ++ l') =
      pathHolonomy X (x0 + siteOfCoords F.depth u) l * pathHolonomy X (x0 + siteOfCoords F.depth (endpoint u l)) l' := by
  induction l generalizing u with
  | nil => simp [pathHolonomy, endpoint]
  | cons st r ih =>
    show linkValue X _ st * pathHolonomy X (x0 + siteOfCoords F.depth u + stepDisplacement F.depth st) (r ++ l') =
      (linkValue X _ st * pathHolonomy X (x0 + siteOfCoords F.depth u + stepDisplacement F.depth st) r) *
        pathHolonomy X (x0 + siteOfCoords F.depth (endpoint (u + FlatPairing.stepDisplacement st) r)) l'
    rw [add_siteOfCoords_add_step, ih, mul_assoc]
theorem blockSide_pow_gap_int : (F.blockSide : ℤ) ^ (F.top - F.depth) = F.blockSide := by
  simp [BlockFrame.top]
theorem enclosingCell_near_centre (hodd : Odd F.blockSide) (y : F.Cell) {h : Lattice4}
    (hh : h ∈ centredCube F.blockSide) :
    enclosingCell (cellCentre F.depth y + siteOfCoords F.depth h) = y := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.enclosingCell_blockPoint <;> assumption
theorem cellCentre_add_unitStep (y : F.Cell) (i : Fin 4) :
    cellCentre F.depth (y + unitStep F.top i) =
      cellCentre F.depth y + siteOfCoords F.depth ((F.blockSide : ℤ) • basisVector i) := by
  rw [unitStep_eq, cellCentre_add F.depth (by simp [BlockFrame.top]) y (basisVector i), blockSide_pow_gap_int]
  congr 2
theorem refineSite_eq (y : F.Cell) : refineSite y = cellCentre F.depth y + siteOfCoords F.depth 0 := by
  rw [_root_.YangMills.Construction.BlockAverages.siteOfCoords_zero, add_zero]
  simp only [refineSite, cellCentre, blockSide_pow_gap_int]
theorem add_unitStep_ne (hamb : IsAdmissibleAmbient F) (y : F.Cell) (i : Fin 4) : y + unitStep F.top i ≠ y := by apply _root_.YangMills.Construction.BlockAverages.ChartFloor.add_unitStep_ne <;> assumption
theorem baseChart_inner_bond (hodd : Odd F.blockSide) (y : F.Cell) (V : F.GaugeField F.top) {v : Lattice4} {k : Fin 4}
    (hv : v ∈ centredCube F.blockSide) (hv' : v + basisVector k ∈ centredCube F.blockSide) :
    baseChart V (cellCentre F.depth y + siteOfCoords F.depth v) k = 1 := by
  classical
  have hx : ¬ IsCrossingBond ((cellCentre F.depth y + siteOfCoords F.depth v, k) : F.Site F.depth × Fin 4) := by
    intro hc
    apply hc
    show enclosingCell (cellCentre F.depth y + siteOfCoords F.depth v + unitStep F.depth k) =
      enclosingCell (cellCentre F.depth y + siteOfCoords F.depth v)
    rw [unitStep_eq, add_assoc, ← siteOfCoords_add, enclosingCell_near_centre hodd y hv',
      enclosingCell_near_centre hodd y hv]
  simp only [baseChart, chartedField, if_neg hx, expUnit_zero]
  split_ifs <;> rfl
theorem pathHolonomy_baseChart_block (hodd : Odd F.blockSide) (y : F.Cell) (V : F.GaugeField F.top) {u : Lattice4}
    {l : List PathStep} (h : AllAlong (fun v => v ∈ centredCube F.blockSide) u l) :
    pathHolonomy (baseChart V) (cellCentre F.depth y + siteOfCoords F.depth u) l = 1 := by
  induction l generalizing u with
  | nil => rfl
  | cons st r ih =>
    have h1 : u ∈ centredCube F.blockSide := h.1
    have h2 : u + FlatPairing.stepDisplacement st ∈ centredCube F.blockSide := allAlong_head h.2
    have hs : linkValue (baseChart V) (cellCentre F.depth y + siteOfCoords F.depth u) st = 1 := by
      rcases st with ⟨k, b⟩
      cases b
      · have e1 : u + FlatPairing.stepDisplacement (k, false) + basisVector k = u := by
          simp [FlatPairing.stepDisplacement]
        have e2 : cellCentre F.depth y + siteOfCoords F.depth u - unitStep F.depth k =
            cellCentre F.depth y + siteOfCoords F.depth (u + FlatPairing.stepDisplacement (k, false)) := by
          rw [← add_siteOfCoords_add_step]
          simp [stepDisplacement, sub_eq_add_neg]
        have h3 := baseChart_inner_bond hodd y V (k := k) h2 (by rw [e1]; exact h1)
        simp only [linkValue, Bool.false_eq_true, if_false]
        rw [e2, h3, inv_one]
      · have h3 := baseChart_inner_bond hodd y V (k := k) h1 (by simpa [FlatPairing.stepDisplacement] using h2)
        simp only [linkValue, if_true]
        exact h3
    show linkValue (baseChart V) _ st *
      pathHolonomy (baseChart V) (cellCentre F.depth y + siteOfCoords F.depth u + stepDisplacement F.depth st) r = 1
    rw [hs, one_mul, add_siteOfCoords_add_step]
    exact ih h.2
theorem mem_centredCube_of_between {L : ℕ} {h v : Lattice4} (hL : 1 ≤ L) (hh : h ∈ centredCube L)
    (hv : BetweenOrigin h v) : v ∈ centredCube L := by
  rw [_root_.YangMills.Construction.LatticePaths.mem_centredCube_iff]
  intro μ
  have h1 := ((_root_.YangMills.Construction.LatticePaths.mem_centredCube_iff L h).1 hh) μ
  have h2 := hv μ
  have hk : (0 : ℤ) ≤ ((L : ℤ) - 1) / 2 := by omega
  have a1 : min 0 (h μ) ≥ -(((L : ℤ) - 1) / 2) := le_min (by omega) h1.1
  have a2 : max 0 (h μ) ≤ ((L : ℤ) - 1) / 2 := max_le hk h1.2
  constructor <;> omega
theorem pathHolonomy_baseChart_straight (hodd : Odd F.blockSide) (hamb : IsAdmissibleAmbient F) (y : F.Cell)
    (V : F.GaugeField F.top) (i : Fin 4) {h : Lattice4} (hh : h ∈ centredCube F.blockSide) :
    pathHolonomy (baseChart V) (cellCentre F.depth y + siteOfCoords F.depth h)
      (List.replicate F.blockSide (i, true)) = V y i := by
  classical
  obtain ⟨M, hM⟩ := hodd
  have hLz : (F.blockSide : ℤ) = 2 * (M : ℤ) + 1 := by rw [hM]; push_cast; ring
  have hodd' : Odd F.blockSide := ⟨M, hM⟩
  have eM : ((F.blockSide : ℤ) - 1) / 2 = M := by rw [hLz]; omega
  have hcube : ∀ v : Lattice4, v ∈ centredCube F.blockSide ↔ ∀ μ, -(M : ℤ) ≤ v μ ∧ v μ ≤ M := by
    intro v
    rw [_root_.YangMills.Construction.LatticePaths.mem_centredCube_iff, eM]
  have hh' := (hcube h).1 hh
  obtain ⟨r1, hr1⟩ : ∃ r1 : ℕ, (r1 : ℤ) = (M : ℤ) - h i := ⟨((M : ℤ) - h i).toNat, by
    have := (hh' i).2
    omega⟩
  obtain ⟨r2, hr2⟩ : ∃ r2 : ℕ, (r2 : ℤ) = (M : ℤ) + h i := ⟨((M : ℤ) + h i).toNat, by
    have := (hh' i).1
    omega⟩
  have hsum : F.blockSide = r1 + (1 + r2) := by
    have : (F.blockSide : ℤ) = (r1 : ℤ) + (1 + (r2 : ℤ)) := by rw [hr1, hr2, hLz]; ring
    exact_mod_cast this
  have estep : FlatPairing.stepDisplacement (i, true) = basisVector i := by simp [FlatPairing.stepDisplacement]
  have p1 : AllAlong (fun v => v ∈ centredCube F.blockSide) h (List.replicate r1 (i, true)) := by
    refine allAlong_replicate fun k hk => (hcube _).2 fun μ => ?_
    have hμ := hh' μ
    rw [estep]
    by_cases e : μ = i
    · subst e
      simp only [Pi.add_apply, Pi.smul_apply, basisVector, Pi.single_eq_same, smul_eq_mul, mul_one]
      have : (k : ℤ) ≤ r1 := by exact_mod_cast hk
      constructor <;> omega
    · simpa [basisVector, Pi.single_apply, e] using hμ
  set v : Lattice4 := h + (r1 : ℤ) • basisVector i with hv
  have ev : endpoint h (List.replicate r1 (i, true)) = v := by rw [endpoint_replicate, estep]
  have vi : v i = M := by
    simp only [hv, Pi.add_apply, Pi.smul_apply, basisVector, Pi.single_eq_same, smul_eq_mul, mul_one]
    omega
  have vcube : v ∈ centredCube F.blockSide := by
    have := allAlong_endpoint p1
    rwa [ev] at this
  set y' : F.Cell := y + unitStep F.top i with hy'
  set v' : Lattice4 := v + basisVector i - (F.blockSide : ℤ) • basisVector i with hv'
  have e1 : cellCentre F.depth y + siteOfCoords F.depth (v + basisVector i) =
      cellCentre F.depth y' + siteOfCoords F.depth v' := by
    rw [hy', cellCentre_add_unitStep, add_assoc (cellCentre F.depth y), ← siteOfCoords_add]
    congr 2
    rw [hv']
    abel
  have v'i : v' i = -(M : ℤ) := by
    simp only [hv', Pi.sub_apply, Pi.add_apply, Pi.smul_apply, basisVector, Pi.single_eq_same, smul_eq_mul, mul_one]
    omega
  have vcube' := (hcube v).1 vcube
  have p3 : AllAlong (fun v => v ∈ centredCube F.blockSide) v' (List.replicate r2 (i, true)) := by
    refine allAlong_replicate fun k hk => (hcube _).2 fun μ => ?_
    rw [estep]
    by_cases e : μ = i
    · subst e
      simp only [Pi.add_apply, Pi.smul_apply, basisVector, Pi.single_eq_same, smul_eq_mul, mul_one]
      have : (k : ℤ) ≤ r2 := by exact_mod_cast hk
      have h3 := hh' μ
      constructor
      · have : 0 ≤ (k : ℤ) := by positivity
        show -(M : ℤ) ≤ v' μ + k
        omega
      · show v' μ + k ≤ M
        omega
    · have h3 := vcube' μ
      have : v' μ = v μ := by simp [hv', basisVector, Pi.single_apply, e]
      simpa [basisVector, Pi.single_apply, e, this] using h3
  have v'cube : v' ∈ centredCube F.blockSide := allAlong_head p3
  have hcross : IsCrossingBond ((cellCentre F.depth y + siteOfCoords F.depth v, i) : F.Site F.depth × Fin 4) := by
    show enclosingCell (cellCentre F.depth y + siteOfCoords F.depth v + unitStep F.depth i) ≠
      enclosingCell (cellCentre F.depth y + siteOfCoords F.depth v)
    rw [unitStep_eq, add_assoc, ← siteOfCoords_add, e1, enclosingCell_near_centre hodd' y' v'cube,
      enclosingCell_near_centre hodd' y vcube]
    exact add_unitStep_ne hamb y i
  have hbase : baseChart V (cellCentre F.depth y + siteOfCoords F.depth v) i = V y i := by
    simp only [baseChart, chartedField, if_pos hcross, expUnit_zero, one_mul]
    rw [enclosingCell_near_centre hodd' y vcube]
  rw [hsum, List.replicate_add, List.replicate_add, pathHolonomy_append_at, ev,
    pathHolonomy_baseChart_block hodd' y V p1, one_mul, pathHolonomy_append_at]
  have e2 : endpoint v (List.replicate 1 (i, true)) = v + basisVector i := by
    rw [endpoint_replicate, estep]
    simp
  rw [e2, e1, pathHolonomy_baseChart_block hodd' y' V p3, mul_one]
  show linkValue (baseChart V) _ (i, true) * 1 = V y i
  simp only [linkValue, if_true, mul_one]
  exact hbase
theorem pathHolonomy_baseChart_contour (hodd : Odd F.blockSide) (hL : 1 ≤ F.blockSide) (hamb : IsAdmissibleAmbient F)
    (y : F.Cell) (V : F.GaugeField F.top)
    (i : Fin 4) {h : Lattice4} (π : Equiv.Perm (Fin 4)) (hh : h ∈ centredCube F.blockSide) :
    pathHolonomy (baseChart V) (refineSite y) (bondContour F.blockSide h π i) = V y i := by
  obtain ⟨l1, l2⟩ := axisPath_spec h π
  have q1 : AllAlong (fun v => v ∈ centredCube F.blockSide) 0 (axisPath h π) :=
    allAlong_mono (fun v hv => mem_centredCube_of_between hL hh hv) l1
  have q3 : AllAlong (fun v => v ∈ centredCube F.blockSide) h (reversePath (axisPath h π)) := by
    have := allAlong_reversePath q1
    rwa [l2] at this
  have e1 : endpoint 0 (axisPath h π ++ List.replicate F.blockSide (i, true)) =
      h + (F.blockSide : ℤ) • basisVector i := by
    rw [endpoint_append, l2, endpoint_replicate]
    simp [FlatPairing.stepDisplacement]
  have e2 : cellCentre F.depth y + siteOfCoords F.depth (h + (F.blockSide : ℤ) • basisVector i) =
      cellCentre F.depth (y + unitStep F.top i) + siteOfCoords F.depth h := by
    rw [cellCentre_add_unitStep, siteOfCoords_add]
    abel
  unfold bondContour
  rw [refineSite_eq, pathHolonomy_append_at, pathHolonomy_append_at, l2, e1, e2,
    pathHolonomy_baseChart_block hodd y V q1, one_mul,
    pathHolonomy_baseChart_block hodd _ V q3, mul_one]
  exact pathHolonomy_baseChart_straight hodd hamb y V i hh
theorem allSteps_of_allAlong {R : F.Site F.depth × Fin 4 → Prop} {p : Lattice4 → Prop} {x0 : F.Site F.depth}
    (hR : ∀ v k, p v → R (x0 + siteOfCoords F.depth v, k)) {u : Lattice4} {l : List PathStep}
    (h : AllAlong p u l) :
    AllSteps (fun x st => R (bondOfStep x st)) (x0 + siteOfCoords F.depth u) l := by
  induction l generalizing u with
  | nil => trivial
  | cons st r ih =>
    refine ⟨?_, ?_⟩
    · rcases st with ⟨k, b⟩
      cases b
      · have e2 : x0 + siteOfCoords F.depth u - unitStep F.depth k =
            x0 + siteOfCoords F.depth (u + FlatPairing.stepDisplacement (k, false)) := by
          rw [← add_siteOfCoords_add_step]
          simp [stepDisplacement, sub_eq_add_neg]
        simp only [bondOfStep, Bool.false_eq_true, if_false]
        rw [e2]
        exact hR _ _ (allAlong_head h.2)
      · simp only [bondOfStep, if_true]
        exact hR _ _ h.1
    · rw [add_siteOfCoords_add_step]
      exact ih h.2
theorem allSteps_bondContour (hodd : Odd F.blockSide) (hL : 1 ≤ F.blockSide) {R : F.Site F.depth × Fin 4 → Prop}
    (y : F.Cell) (i : Fin 4)
    (hR : ∀ b : F.Site F.depth × Fin 4, (enclosingCell b.1 = y ∨ enclosingCell b.1 = y + unitStep F.top i) → R b)
    {h : Lattice4} (π : Equiv.Perm (Fin 4)) (hh : h ∈ centredCube F.blockSide) :
    AllSteps (fun x st => R (bondOfStep x st)) (refineSite y) (bondContour F.blockSide h π i) := by
  rw [refineSite_eq]
  refine allSteps_of_allAlong (p := fun v => v ∈ FlatPairing.twoBlockHull F.blockSide i) ?_
    (bondContour_spec π i hL hh).1
  intro v k hv
  apply hR
  obtain ⟨M, hM⟩ := hodd
  have hLz : (F.blockSide : ℤ) = 2 * (M : ℤ) + 1 := by rw [hM]; push_cast; ring
  have hodd' : Odd F.blockSide := ⟨M, hM⟩
  have eM : ((F.blockSide : ℤ) - 1) / 2 = M := by rw [hLz]; omega
  by_cases hi : v i ≤ M
  · left
    refine enclosingCell_near_centre hodd' y ((_root_.YangMills.Construction.LatticePaths.mem_centredCube_iff _ _).2 fun μ => ?_)
    have := hv μ
    rw [eM] at this ⊢
    by_cases e : μ = i
    · subst e
      simp only [if_true] at this
      exact ⟨this.1, hi⟩
    · simpa [e] using this
  · right
    have e2 : cellCentre F.depth y + siteOfCoords F.depth v =
        cellCentre F.depth (y + unitStep F.top i) +
          siteOfCoords F.depth (v - (F.blockSide : ℤ) • basisVector i) := by
      rw [cellCentre_add_unitStep, add_assoc, ← siteOfCoords_add]
      congr 2
      abel
    show enclosingCell (cellCentre F.depth y + siteOfCoords F.depth v) = _
    rw [e2]
    refine enclosingCell_near_centre hodd' _ ((_root_.YangMills.Construction.LatticePaths.mem_centredCube_iff _ _).2 fun μ => ?_)
    have := hv μ
    rw [eM] at this ⊢
    by_cases e : μ = i
    · subst e
      simp only [if_true] at this
      simp only [Pi.sub_apply, Pi.smul_apply, basisVector, Pi.single_eq_same, smul_eq_mul, mul_one]
      omega
    · simpa [e, basisVector, Pi.single_apply] using this
end Contours
section Bond
open LatticePaths LatticeFractionalIntegration
variable {F : BlockFrame}
theorem AllSteps.mono {j : ℕ} {R R' : F.Site j → PathStep → Prop} (hR : ∀ x st, R x st → R' x st)
    {x : F.Site j} {l : List PathStep} (h : AllSteps R x l) : AllSteps R' x l := by
  induction l generalizing x with
  | nil => trivial
  | cons st r ih => exact ⟨hR _ _ h.1, ih h.2⟩
theorem bondContour_jet (hodd : Odd F.blockSide) (hL : 1 ≤ F.blockSide) (hamb : IsAdmissibleAmbient F)
    {S : Finset F.Cell} {V : F.GaugeField F.top} {w dw : F.Site F.depth → Fin 4 → imaginaryQuaternions} {ρ q : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hq : 0 ≤ q)
    (hw : SupportedOnChords S w) (hdw : SupportedOnChords S dw) (y : F.Cell) (i : Fin 4)
    (hb : ∀ b : F.Site F.depth × Fin 4, (enclosingCell b.1 = y ∨ enclosingCell b.1 = y + unitStep F.top i) →
      ‖w b.1 b.2‖ ≤ ρ ∧ ‖dw b.1 b.2‖ ≤ q)
    {h : Lattice4} (π : Equiv.Perm (Fin 4)) (hh : h ∈ centredCube F.blockSide) :
    AnalyticAt ℝ (fun τ => ((pathHolonomy (chartedField (chartLineShift w dw τ) V) (refineSite y)
        (bondContour F.blockSide h π i) : UnitQuaternion) : ℍ[ℝ]) *
        (((V y i)⁻¹ : UnitQuaternion) : ℍ[ℝ])) 0 ∧
      ‖((pathHolonomy (chartedField w V) (refineSite y) (bondContour F.blockSide h π i) : UnitQuaternion) : ℍ[ℝ]) *
          (((V y i)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
        15 * F.blockSide * ρ ∧
      ‖deriv (fun τ => ((pathHolonomy (chartedField (chartLineShift w dw τ) V) (refineSite y)
          (bondContour F.blockSide h π i) : UnitQuaternion) : ℍ[ℝ]) *
          (((V y i)⁻¹ : UnitQuaternion) : ℍ[ℝ])) 0 -
          pathHolonomyVariation (chartedField w V) dw (refineSite y) (bondContour F.blockSide h π i)‖ ≤
        105 * (F.blockSide : ℝ) ^ 2 * ρ * q ∧
      ‖deriv (deriv fun τ => ((pathHolonomy (chartedField (chartLineShift w dw τ) V) (refineSite y)
          (bondContour F.blockSide h π i) : UnitQuaternion) : ℍ[ℝ]) *
          (((V y i)⁻¹ : UnitQuaternion) : ℍ[ℝ])) 0‖ ≤ 400 * (F.blockSide : ℝ) ^ 2 * q ^ 2 ∧
      ‖pathHolonomyVariation (chartedField w V) dw (refineSite y) (bondContour F.blockSide h π i)‖ ≤
        5 * F.blockSide * q ∧
      (pathHolonomyVariation (chartedField w V) dw (refineSite y) (bondContour F.blockSide h π i)).re = 0 := by
  set l := bondContour F.blockSide h π i with hl
  have hlen : (l.length : ℝ) ≤ 5 * F.blockSide := by exact_mod_cast length_bondContour_le π i hL hh
  have hLr : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hL
  have hsteps := allSteps_bondContour hodd hL (R := fun b => ‖w b.1 b.2‖ ≤ ρ ∧ ‖dw b.1 b.2‖ ≤ q) y i hb π hh
  have sw : AllSteps (fun x st => ‖w (bondOfStep x st).1 (bondOfStep x st).2‖ ≤ ρ) (refineSite y) l :=
    AllSteps.mono (fun _ _ a => a.1) hsteps
  have sd : AllSteps (fun x st => ‖dw (bondOfStep x st).1 (bondOfStep x st).2‖ ≤ q) (refineSite y) l :=
    AllSteps.mono (fun _ _ a => a.2) hsteps
  have sg : AllSteps (JetStep (fun τ => chartedField (chartLineShift w dw τ) V) dw ρ q) (refineSite y) l :=
    AllSteps.mono (fun x st a => jetStep_chart hw hdw V hρ1 hq x st a.1 a.2) hsteps
  obtain ⟨H1, H2, J, b1, b2, b3⟩ := pathHolonomy_jet hq sg
  simp only [chartLineShift_zero] at J b3
  obtain ⟨hv1, hv2⟩ := pathHolonomyVariation_bound (X := chartedField w V) sd
  have hbase := norm_pathHolonomy_sub_base_le hw V hρ1 sw
  rw [hl, pathHolonomy_baseChart_contour hodd hL hamb y V i π hh, ← hl] at hbase
  set g : ℍ[ℝ] := (((V y i)⁻¹ : UnitQuaternion) : ℍ[ℝ]) with hg
  set H0 : ℍ[ℝ] := ((pathHolonomy (chartedField w V) (refineSite y) l : UnitQuaternion) : ℍ[ℝ]) with hH0
  set hv : ℍ[ℝ] := pathHolonomyVariation (chartedField w V) dw (refineSite y) l with hhv
  have ng : ‖g‖ = 1 := norm_coe_unitQuaternion _
  have Vg : ((V y i : UnitQuaternion) : ℍ[ℝ]) * g = 1 := by
    rw [hg, ← Submonoid.coe_mul, mul_inv_cancel]
    rfl
  have J' := J.mul (TwoJet.const g)
  simp only [zero_mul, mul_zero, add_zero, zero_add] at J'
  have hd1 := J'.2.2.1
  have hd2 := J'.2.2.2
  have hnear : ‖H0 * g - 1‖ ≤ 15 * F.blockSide * ρ := by
    have e : H0 * g - 1 = (H0 - (V y i : ℍ[ℝ])) * g := by rw [sub_mul, Vg]
    rw [e, norm_mul, ng, mul_one]
    refine hbase.trans ?_
    have := mul_le_mul_of_nonneg_right hlen (show 0 ≤ 3 * ρ by positivity)
    linarith
  have hq5 : ‖hv‖ ≤ 5 * F.blockSide * q := hv1.trans (mul_le_mul_of_nonneg_right hlen hq)
  refine ⟨J'.1, hnear, ?_, ?_, hq5, hv2⟩
  · rw [hd1]
    have e : H1 * g - hv = (H1 - hv * H0) * g + hv * (H0 * g - 1) := by noncomm_ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, ng, mul_one]
    have t1 : (l.length : ℝ) * (6 * ρ * q) ≤ 5 * F.blockSide * (6 * ρ * q) :=
      mul_le_mul_of_nonneg_right hlen (by positivity)
    have t2 : ‖hv‖ * ‖H0 * g - 1‖ ≤ 5 * F.blockSide * q * (15 * F.blockSide * ρ) :=
      mul_le_mul hq5 hnear (norm_nonneg _) (by positivity)
    have t3 : 30 * (F.blockSide : ℝ) * (ρ * q) ≤ 30 * (F.blockSide : ℝ) ^ 2 * (ρ * q) := by
      have h0 : 0 ≤ ρ * q := by positivity
      have h1 : (F.blockSide : ℝ) ≤ (F.blockSide : ℝ) ^ 2 := by nlinarith
      have := mul_le_mul_of_nonneg_right h1 h0
      linarith
    nlinarith
  · rw [hd2, norm_mul, ng, mul_one]
    refine b2.trans ?_
    have t1 : (l.length : ℝ) * (4 * q) ≤ 5 * F.blockSide * (4 * q) := mul_le_mul_of_nonneg_right hlen (by positivity)
    have t2 : ((l.length : ℝ) * (4 * q)) ^ 2 ≤ (5 * F.blockSide * (4 * q)) ^ 2 := pow_le_pow_left₀ (by positivity) t1 2
    refine t2.trans (le_of_eq ?_)
    ring
theorem norm_contour_mean_le {L : ℕ} (hodd : Odd L) (hL : 1 ≤ L) {f : Lattice4 → Equiv.Perm (Fin 4) → ℍ[ℝ]} {b : ℝ}
    (hf : ∀ h ∈ centredCube L, ∀ π, ‖f h π‖ ≤ b) :
    ‖(1 / (24 * (L : ℝ) ^ 4)) • ∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4), f h π‖ ≤ b := by
  have h1 : ‖∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4), f h π‖ ≤ (L : ℝ) ^ 4 * (24 * b) := by
    refine (norm_sum_le _ _).trans ?_
    have h2 : ∀ h ∈ centredCube L, ‖∑ π : Equiv.Perm (Fin 4), f h π‖ ≤ 24 * b := by
      intro h hh
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun π _ => hf h hh π).trans (le_of_eq ?_)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm]
      simp [Nat.factorial]
    refine (Finset.sum_le_sum h2).trans (le_of_eq ?_)
    rw [Finset.sum_const, card_centredCube hodd]
    simp
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc 1 / (24 * (L : ℝ) ^ 4) * ‖∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4), f h π‖
      ≤ 1 / (24 * (L : ℝ) ^ 4) * ((L : ℝ) ^ 4 * (24 * b)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = b := by field_simp
theorem contour_mean_one {L : ℕ} (hodd : Odd L) (hL : 1 ≤ L) :
    (1 / (24 * (L : ℝ) ^ 4)) • ∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4), (1 : ℍ[ℝ]) = 1 := by
  have e : ∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4), (1 : ℍ[ℝ]) = ((24 * (L : ℝ) ^ 4 : ℝ)) • (1 : ℍ[ℝ]) := by
    rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_perm, card_centredCube hodd,
      ← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    congr 1
    simp [Nat.factorial]
    ring
  rw [e, smul_smul]
  have : 1 / (24 * (L : ℝ) ^ 4) * (24 * (L : ℝ) ^ 4) = 1 := by field_simp
  rw [this, one_smul]
theorem fit_constant_ineq {Lr ρ q : ℝ} (hL : 1 ≤ Lr) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / (30 * Lr)) (hq : 0 ≤ q) :
    2 * (5 * Lr * q) * (105 * Lr ^ 2 * ρ * q) +
        15 * Lr * ρ * (5 * Lr * q + 105 * Lr ^ 2 * ρ * q) ^ 2 +
        8 * (15 * Lr * ρ * (5 * Lr * q + 105 * Lr ^ 2 * ρ * q) + 105 * Lr ^ 2 * ρ * q) ^ 2 +
        4 * (15 * Lr * ρ) * (400 * Lr ^ 2 * q ^ 2) ≤ 50000 * Lr ^ 3 * ρ * q ^ 2 := by
  have hLpos : 0 < Lr := by linarith
  have ht : Lr * ρ ≤ 1 / 30 := by
    rw [le_div_iff₀ (by positivity)] at hρ
    linarith
  set P : ℝ := Lr ^ 3 * ρ * q ^ 2 with hP
  have hP0 : 0 ≤ P := by positivity
  have hce : 5 * Lr * q + 105 * Lr ^ 2 * ρ * q ≤ 9 * Lr * q := by
    have h1 : 105 * Lr ^ 2 * ρ * q = 105 * (Lr * ρ) * (Lr * q) := by ring
    have h2 : (Lr * ρ) * (Lr * q) ≤ 1 / 30 * (Lr * q) := mul_le_mul_of_nonneg_right ht (by positivity)
    rw [h1]
    nlinarith [mul_nonneg hLpos.le hq]
  have hce0 : 0 ≤ 5 * Lr * q + 105 * Lr ^ 2 * ρ * q := by positivity
  have a1 : 2 * (5 * Lr * q) * (105 * Lr ^ 2 * ρ * q) = 1050 * P := by rw [hP]; ring
  have a2 : 15 * Lr * ρ * (5 * Lr * q + 105 * Lr ^ 2 * ρ * q) ^ 2 ≤ 1215 * P := by
    have h1 : (5 * Lr * q + 105 * Lr ^ 2 * ρ * q) ^ 2 ≤ (9 * Lr * q) ^ 2 := pow_le_pow_left₀ hce0 hce 2
    have h2 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 15 * Lr * ρ by positivity)
    refine h2.trans (le_of_eq ?_)
    rw [hP]
    ring
  have a3 : 8 * (15 * Lr * ρ * (5 * Lr * q + 105 * Lr ^ 2 * ρ * q) + 105 * Lr ^ 2 * ρ * q) ^ 2 ≤ 15360 * P := by
    have h1 : 15 * Lr * ρ * (5 * Lr * q + 105 * Lr ^ 2 * ρ * q) + 105 * Lr ^ 2 * ρ * q ≤ 240 * Lr ^ 2 * ρ * q := by
      have h2 := mul_le_mul_of_nonneg_left hce (show 0 ≤ 15 * Lr * ρ by positivity)
      linarith
    have h4 : (15 * Lr * ρ * (5 * Lr * q + 105 * Lr ^ 2 * ρ * q) + 105 * Lr ^ 2 * ρ * q) ^ 2 ≤
        (240 * Lr ^ 2 * ρ * q) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    have h5 : (240 * Lr ^ 2 * ρ * q) ^ 2 = 57600 * (Lr * ρ) * P := by rw [hP]; ring
    have h6 : (Lr * ρ) * P ≤ 1 / 30 * P := mul_le_mul_of_nonneg_right ht hP0
    nlinarith
  have a4 : 4 * (15 * Lr * ρ) * (400 * Lr ^ 2 * q ^ 2) = 24000 * P := by rw [hP]; ring
  have : 50000 * Lr ^ 3 * ρ * q ^ 2 = 50000 * P := by rw [hP]; ring
  rw [this, a1, a4]
  linarith
theorem blockFit_second_deriv (hodd : Odd F.blockSide) (hL : 1 ≤ F.blockSide) (hamb : IsAdmissibleAmbient F)
    {S : Finset F.Cell} {V : F.GaugeField F.top} {w dw : F.Site F.depth → Fin 4 → imaginaryQuaternions} {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / (30 * (F.blockSide : ℝ)))
    (hw : SupportedOnChords S w) (hdw : SupportedOnChords S dw) (hwb : ∀ b ∈ chordBonds S, ‖w b.1 b.2‖ ≤ ρ)
    (c : F.Cell × Fin 4) :
    AnalyticAt ℝ (fun τ : ℝ => blockFit (chartedField (chartLineShift w dw τ) V) V c) 0 ∧
      ‖bondContourVariation (chartedField w V) dw c‖ ^ 2 -
          50000 * (F.blockSide : ℝ) ^ 3 * ρ * chordSqNormOnPair S c.1 (c.1 + unitStep F.top c.2) dw ≤
        deriv (deriv fun τ : ℝ => blockFit (chartedField (chartLineShift w dw τ) V) V c) 0 := by
  classical
  obtain ⟨y, i⟩ := c
  simp only []
  have hLr : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hL
  have hρ1 : ρ ≤ 1 := by
    refine hρ.trans ?_
    rw [div_le_one (by positivity)]
    linarith
  set Q : ℝ := chordSqNormOnPair S y (y + unitStep F.top i) dw with hQ
  have hQ0 : 0 ≤ Q := by
    rw [hQ]
    unfold chordSqNormOnPair
    exact Finset.sum_nonneg fun _ _ => by positivity
  set q : ℝ := Real.sqrt Q with hqdef
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hqQ : q ^ 2 = Q := Real.sq_sqrt hQ0
  have hb : ∀ b : F.Site F.depth × Fin 4, (enclosingCell b.1 = y ∨ enclosingCell b.1 = y + unitStep F.top i) →
      ‖w b.1 b.2‖ ≤ ρ ∧ ‖dw b.1 b.2‖ ≤ q := by
    intro b hcell
    by_cases hbc : b ∈ chordBonds S
    · refine ⟨hwb b hbc, ?_⟩
      have h1 : ‖dw b.1 b.2‖ ^ 2 ≤ Q := by
        rw [hQ]
        unfold chordSqNormOnPair
        exact Finset.single_le_sum (f := fun b : F.Site F.depth × Fin 4 => ‖dw b.1 b.2‖ ^ 2)
          (fun _ _ => by positivity) (Finset.mem_filter.2 ⟨hbc, hcell⟩)
      exact (le_abs_self _).trans (Real.abs_le_sqrt h1)
    · rw [hw b hbc, hdw b hbc]
      simpa using ⟨hρ0, hq⟩
  have key := fun (h : Lattice4) (hh : h ∈ centredCube F.blockSide) (π : Equiv.Perm (Fin 4)) =>
    bondContour_jet hodd hL hamb (V := V) hρ0 hρ1 hq hw hdw y i hb π hh
  set g : ℍ[ℝ] := (((V y i)⁻¹ : UnitQuaternion) : ℍ[ℝ]) with hg
  have ng : ‖g‖ = 1 := norm_coe_unitQuaternion _
  set a : Lattice4 → Equiv.Perm (Fin 4) → ℝ → ℍ[ℝ] := fun h π τ =>
    ((pathHolonomy (chartedField (chartLineShift w dw τ) V) (refineSite y) (bondContour F.blockSide h π i) :
      UnitQuaternion) : ℍ[ℝ]) * g with ha
  set hv : Lattice4 → Equiv.Perm (Fin 4) → ℍ[ℝ] := fun h π =>
    pathHolonomyVariation (chartedField w V) dw (refineSite y) (bondContour F.blockSide h π i) with hhv
  set κ : ℝ := 1 / (24 * (F.blockSide : ℝ) ^ 4) with hκ
  set m : ℝ → ℍ[ℝ] := fun τ => κ • ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), a h π τ with hm
  have ja : ∀ h ∈ centredCube F.blockSide, ∀ π,
      TwoJet (a h π) (a h π 0) (deriv (a h π) 0) (deriv (deriv (a h π)) 0) :=
    fun h hh π => ⟨(key h hh π).1, rfl, rfl, rfl⟩
  have jm : TwoJet m (κ • ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), a h π 0)
      (κ • ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), deriv (a h π) 0)
      (κ • ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), deriv (deriv (a h π)) 0) :=
    (TwoJet.sum (centredCube F.blockSide) fun h hh => TwoJet.sum Finset.univ fun π _ => ja h hh π).smul κ
  have a0 : ∀ h π, a h π 0 =
      ((pathHolonomy (chartedField w V) (refineSite y) (bondContour F.blockSide h π i) : UnitQuaternion) : ℍ[ℝ]) * g := by
    intro h π
    simp only [ha, chartLineShift_zero]
  have hδ : ‖(κ • ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), a h π 0) - 1‖ ≤
      15 * F.blockSide * ρ := by
    have e : (κ • ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), a h π 0) - 1 =
        κ • ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), (a h π 0 - 1) := by
      simp only [Finset.sum_sub_distrib, smul_sub]
      rw [contour_mean_one hodd hL]
    rw [e]
    refine norm_contour_mean_le hodd hL fun h hh π => ?_
    rw [a0]
    exact (key h hh π).2.1
  have hcv : bondContourVariation (chartedField w V) dw (y, i) =
      κ • ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), hv h π := rfl
  have hc : ‖bondContourVariation (chartedField w V) dw (y, i)‖ ≤ 5 * F.blockSide * q := by
    rw [hcv]
    exact norm_contour_mean_le hodd hL fun h hh π => (key h hh π).2.2.2.2.1
  have hre : (bondContourVariation (chartedField w V) dw (y, i)).re = 0 := by
    rw [hcv]
    have e : ∀ t : Finset Lattice4, (∑ h ∈ t, ∑ π : Equiv.Perm (Fin 4), hv h π).re =
        ∑ h ∈ t, ∑ π : Equiv.Perm (Fin 4), (hv h π).re := by
      intro t
      show reCLM _ = _
      rw [map_sum]
      exact Finset.sum_congr rfl fun h _ => by rw [map_sum]; rfl
    rw [Quaternion.re_smul, e, Finset.sum_congr rfl fun h hh =>
      Finset.sum_eq_zero fun π _ => (key h hh π).2.2.2.2.2]
    simp
  have he : ‖(κ • ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), deriv (a h π) 0) -
      bondContourVariation (chartedField w V) dw (y, i)‖ ≤ 105 * (F.blockSide : ℝ) ^ 2 * ρ * q := by
    rw [hcv, ← smul_sub]
    have e : (∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), deriv (a h π) 0) -
        ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), hv h π =
        ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), (deriv (a h π) 0 - hv h π) := by
      simp only [Finset.sum_sub_distrib]
    rw [e]
    exact norm_contour_mean_le hodd hL fun h hh π => (key h hh π).2.2.1
  have hB : ‖κ • ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), deriv (deriv (a h π)) 0‖ ≤
      400 * (F.blockSide : ℝ) ^ 2 * q ^ 2 :=
    norm_contour_mean_le hodd hL fun h hh π => (key h hh π).2.2.2.1
  have hδ2 : 15 * (F.blockSide : ℝ) * ρ ≤ 1 / 2 := by
    rw [le_div_iff₀ (by positivity)] at hρ
    linarith
  obtain ⟨r1, r2⟩ := fit_second_deriv_lower jm hδ hδ2 hre hc he hB
  have hfit : (fun τ : ℝ => blockFit (chartedField (chartLineShift w dw τ) V) V (y, i)) =
      fun τ => ‖m τ‖ - (m τ).re := by
    funext τ
    have e : _root_.YangMills.Construction.BlockAverages.contourAverage (chartedField (chartLineShift w dw τ) V) (y, i) * g = m τ := by
      simp only [_root_.YangMills.Construction.BlockAverages.contourAverage, hm, ha, smul_mul_assoc, Finset.sum_mul]
      rfl
    have e2 : ‖_root_.YangMills.Construction.BlockAverages.contourAverage (chartedField (chartLineShift w dw τ) V) (y, i)‖ = ‖m τ‖ := by
      rw [← e, norm_mul, ng, mul_one]
    simp only [blockFit]
    rw [e2, ← e]
  rw [hfit]
  refine ⟨r1, ?_⟩
  refine le_trans ?_ r2
  have hn := fit_constant_ineq hLr hρ0 hρ hq
  rw [← hqQ]
  linarith
end Bond
end ChartFit
theorem chartFitSecondVariation : chartFitSecondVariationStatement := by
  intro L hodd hL5
  have hLr : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  refine ⟨50000 * (L : ℝ) ^ 3, 1 / (30 * (L : ℝ)), 1, by positivity, by positivity, one_pos, ?_⟩
  intro F m S hFL hamb hm hreg ρ σ V w dw hρ0 hρ hσ0 hσ hV hw hdw hwb hcold c hc
  obtain rfl := hFL
  obtain ⟨r1, r2⟩ := ChartFit.blockFit_second_deriv hodd (by omega) hamb (S := S) (V := V)
    hρ0.le hρ hw hdw hwb c
  refine ⟨r1, le_trans ?_ r2⟩
  have hQ0 : 0 ≤ chordSqNormOnPair S c.1 (c.1 + unitStep F.top c.2) dw := by
    unfold chordSqNormOnPair
    exact Finset.sum_nonneg fun _ _ => by positivity
  have h1 : 50000 * (F.blockSide : ℝ) ^ 3 * ρ * chordSqNormOnPair S c.1 (c.1 + unitStep F.top c.2) dw ≤
      50000 * (F.blockSide : ℝ) ^ 3 * (ρ + σ) * chordSqNormOnPair S c.1 (c.1 + unitStep F.top c.2) dw := by
    refine mul_le_mul_of_nonneg_right ?_ hQ0
    refine mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith
end YangMills.Construction.BlockAverages
end
