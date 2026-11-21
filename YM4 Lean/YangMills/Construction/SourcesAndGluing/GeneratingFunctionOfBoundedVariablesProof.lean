import YangMills.Construction.SourcesAndGluing.GeneratingFunctionOfBoundedVariables
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Filter MeasureTheory Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.SourcesAndGluing.BoundedMGF
section Weighted
variable {𝒳 P : Type*} [MeasurableSpace 𝒳] [Fintype P]
def pairing (Y : P → 𝒳 → ℝ) (x : 𝒳) (s : P → ℂ) : ℂ := ∑ p, s p * (Y p x : ℂ)
def weightedExpectation (ν : Measure 𝒳) (Y : P → 𝒳 → ℝ) (f : 𝒳 → ℂ) (φ : ℂ → ℂ) (s : P → ℂ) : ℂ :=
  ∫ x, f x * φ (pairing Y x s) ∂ν
def IsBoundedMeasurable (f : 𝒳 → ℂ) : Prop := Measurable f ∧ ∃ K : ℝ, ∀ x, ‖f x‖ ≤ K
def expTerm (k : ℕ) (w : ℂ) : ℂ := 1 / (k.factorial : ℂ) * w ^ k
theorem hasDerivAt_expTerm (k : ℕ) (w : ℂ) :
    HasDerivAt (expTerm (k + 1)) (expTerm k w) w := by
  have h := (hasDerivAt_pow (k + 1) w).const_mul (1 / ((k + 1).factorial : ℂ))
  have hk : ((k.factorial : ℂ)) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hk1 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast k.succ_ne_zero
  have e : expTerm k w =
      1 / ((k + 1).factorial : ℂ) * (((k + 1 : ℕ) : ℂ) * w ^ (k + 1 - 1)) := by
    simp only [expTerm, Nat.factorial_succ, Nat.add_sub_cancel]
    push_cast
    field_simp
  rw [e]
  exact h
theorem continuous_expTerm (k : ℕ) : Continuous (expTerm k) := by
  unfold expTerm
  fun_prop
theorem hasSum_expTerm (w : ℂ) : HasSum (fun k => expTerm k w) (Complex.exp w) := by
  have h := NormedSpace.expSeries_div_hasSum_exp w
  rw [← Complex.exp_eq_exp_ℂ] at h
  have e : (fun k => expTerm k w) = fun n : ℕ => w ^ n / (n.factorial : ℂ) := by
    funext k
    rw [expTerm]
    ring
  rw [e]
  exact h
theorem norm_expTerm_le (k : ℕ) {w : ℂ} {B : ℝ} (hw : ‖w‖ ≤ B) :
    ‖expTerm k w‖ ≤ B ^ k / (k.factorial : ℝ) := by
  have h : ‖expTerm k w‖ = ‖w‖ ^ k / (k.factorial : ℝ) := by
    simp [expTerm, div_eq_inv_mul]
  rw [h]
  gcongr
theorem continuous_l1Norm : Continuous (l1Norm : (P → ℂ) → ℝ) := by
  unfold l1Norm
  fun_prop
theorem l1Norm_nonneg (s : P → ℂ) : 0 ≤ l1Norm s :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _
theorem l1Norm_zero : l1Norm (0 : P → ℂ) = 0 := by
  simp [l1Norm]
theorem isOpen_l1Ball (ρ : ℝ) : IsOpen (l1Ball ρ : Set (P → ℂ)) :=
  isOpen_lt continuous_l1Norm continuous_const
theorem continuous_pairing (Y : P → 𝒳 → ℝ) (x : 𝒳) : Continuous (pairing Y x) := by
  unfold pairing
  fun_prop
theorem norm_pairing_le {Y : P → 𝒳 → ℝ} {C : ℝ} (hC : ∀ p x, |Y p x| ≤ C) (x : 𝒳) (s : P → ℂ) :
    ‖pairing Y x s‖ ≤ C * l1Norm s := by
  unfold pairing l1Norm
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
  exact mul_le_mul_of_nonneg_right (hC p x) (norm_nonneg _)
theorem measurable_pairing {Y : P → 𝒳 → ℝ} (hY : ∀ p, Measurable (Y p)) (s : P → ℂ) :
    Measurable fun x => pairing Y x s := by
  unfold pairing
  refine Finset.measurable_fun_sum _ fun p _ => ?_
  exact ((Complex.measurable_ofReal.comp (hY p)).const_mul (s p))
theorem pairing_add_smul [DecidableEq P] (Y : P → 𝒳 → ℝ) (x : 𝒳) (s : P → ℂ) (ζ : ℂ) (a : P) :
    pairing Y x (s + ζ • coordVector a) = pairing Y x s + ζ * (Y a x : ℂ) := by
  simp [pairing, coordVector, add_mul, Finset.sum_add_distrib, Pi.single_apply]
theorem isBoundedMeasurable_pairing {Y : P → 𝒳 → ℝ} {C : ℝ} (hY : ∀ p, Measurable (Y p))
    (hC : ∀ p x, |Y p x| ≤ C) (s : P → ℂ) : IsBoundedMeasurable fun x => pairing Y x s :=
  ⟨measurable_pairing hY s, _, fun x => norm_pairing_le hC x s⟩
theorem isBoundedMeasurable_coord {Y : P → 𝒳 → ℝ} {C : ℝ} (hY : ∀ p, Measurable (Y p))
    (hC : ∀ p x, |Y p x| ≤ C) (a : P) : IsBoundedMeasurable fun x => (Y a x : ℂ) :=
  ⟨Complex.measurable_ofReal.comp (hY a), C, fun x => by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hC a x⟩
theorem IsBoundedMeasurable.mul {f g : 𝒳 → ℂ} (hf : IsBoundedMeasurable f)
    (hg : IsBoundedMeasurable g) : IsBoundedMeasurable fun x => f x * g x := by
  obtain ⟨hfm, K, hK⟩ := hf
  obtain ⟨hgm, L, hL⟩ := hg
  refine ⟨hfm.mul hgm, |K| * |L|, fun x => ?_⟩
  rw [norm_mul]
  exact mul_le_mul ((hK x).trans (le_abs_self K)) ((hL x).trans (le_abs_self L)) (norm_nonneg _)
    (abs_nonneg K)
theorem isBoundedMeasurable_one : IsBoundedMeasurable (fun _ => 1 : 𝒳 → ℂ) :=
  ⟨measurable_const, 1, fun _ => by simp⟩
theorem IsBoundedMeasurable.integrable {f : 𝒳 → ℂ} (hf : IsBoundedMeasurable f) (ν : Measure 𝒳)
    [IsFiniteMeasure ν] : Integrable f ν := by
  obtain ⟨hfm, K, hK⟩ := hf
  exact Integrable.of_bound hfm.aestronglyMeasurable K (ae_of_all _ hK)
theorem hasDerivAt_integral_line {φ ψ : ℂ → ℂ} (hφ : ∀ w, HasDerivAt φ (ψ w) w)
    (hψ : Continuous ψ) (ν : Measure 𝒳) [IsProbabilityMeasure ν] {f A B : 𝒳 → ℂ}
    (hf : IsBoundedMeasurable f) (hA : IsBoundedMeasurable A) (hB : IsBoundedMeasurable B)
    (ζ₀ : ℂ) :
    HasDerivAt (fun ζ => ∫ x, f x * φ (A x + ζ * B x) ∂ν)
      (∫ x, f x * B x * ψ (A x + ζ₀ * B x) ∂ν) ζ₀ := by
  have hφc : Continuous φ := continuous_iff_continuousAt.2 fun w => (hφ w).continuousAt
  have hfB := hf.mul hB
  obtain ⟨hfm, K, hK⟩ := hf
  obtain ⟨hAm, a, ha⟩ := hA
  obtain ⟨hBm, b, hb⟩ := hB
  obtain ⟨hfBm, D, hD⟩ := hfB
  have hmeas : ∀ ζ : ℂ, Measurable fun x => A x + ζ * B x := fun ζ => hAm.add (hBm.const_mul ζ)
  have hmem : ∀ ζ x, ‖ζ‖ ≤ ‖ζ₀‖ + 1 →
      A x + ζ * B x ∈ Metric.closedBall (0 : ℂ) (|a| + (‖ζ₀‖ + 1) * |b|) := by
    intro ζ x hζ
    rw [mem_closedBall_zero_iff]
    refine (norm_add_le _ _).trans (add_le_add ((ha x).trans (le_abs_self a)) ?_)
    rw [norm_mul]
    exact mul_le_mul hζ ((hb x).trans (le_abs_self b)) (norm_nonneg _) (by positivity)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) (|a| + (‖ζ₀‖ + 1) * |b|)).exists_bound_of_continuousOn
    hψ.continuousOn
  obtain ⟨M', hM'⟩ := (isCompact_closedBall (0 : ℂ) (|a| + (‖ζ₀‖ + 1) * |b|)).exists_bound_of_continuousOn
    hφc.continuousOn
  have hball : ∀ ζ ∈ Metric.ball ζ₀ 1, ‖ζ‖ ≤ ‖ζ₀‖ + 1 := by
    intro ζ hζ
    have h1 : ‖ζ - ζ₀‖ < 1 := by simpa [dist_eq_norm] using hζ
    have h2 : ‖ζ‖ ≤ ‖ζ - ζ₀‖ + ‖ζ₀‖ := by simpa using norm_add_le (ζ - ζ₀) ζ₀
    linarith
  have hint : Integrable (fun x => f x * φ (A x + ζ₀ * B x)) ν := by
    refine Integrable.of_bound (hfm.mul (hφc.measurable.comp (hmeas ζ₀))).aestronglyMeasurable
      (|K| * |M'|) (ae_of_all _ fun x => ?_)
    rw [norm_mul]
    exact mul_le_mul ((hK x).trans (le_abs_self K))
      ((hM' _ (hmem ζ₀ x (by linarith))).trans (le_abs_self M')) (norm_nonneg _) (abs_nonneg K)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
    (F := fun ζ x => f x * φ (A x + ζ * B x))
    (F' := fun ζ x => f x * B x * ψ (A x + ζ * B x))
    (bound := fun _ => |D| * |M|) (Metric.ball_mem_nhds ζ₀ one_pos)
    (Eventually.of_forall fun ζ => (hfm.mul (hφc.measurable.comp (hmeas ζ))).aestronglyMeasurable)
    hint (hfBm.mul (hψ.measurable.comp (hmeas ζ₀))).aestronglyMeasurable
    (ae_of_all _ fun x ζ hζ => ?_) (integrable_const _) (ae_of_all _ fun x ζ _ => ?_)).2
  · rw [norm_mul]
    exact mul_le_mul ((hD x).trans (le_abs_self D))
      ((hM _ (hmem ζ x (hball ζ hζ))).trans (le_abs_self M)) (norm_nonneg _) (abs_nonneg D)
  · have h1 : HasDerivAt (fun ζ : ℂ => A x + ζ * B x) (B x) ζ := by
      simpa using ((hasDerivAt_id ζ).mul_const (B x)).const_add (A x)
    have h2 := (hφ (A x + ζ * B x)).comp ζ h1
    have h3 : HasDerivAt (fun ζ : ℂ => f x * φ (A x + ζ * B x))
        (f x * (ψ (A x + ζ * B x) * B x)) ζ := h2.const_mul (f x)
    rw [show f x * B x * ψ (A x + ζ * B x) = f x * (ψ (A x + ζ * B x) * B x) by ring]
    exact h3
variable {ν : Measure 𝒳} [IsProbabilityMeasure ν] {Y : P → 𝒳 → ℝ} {C : ℝ}
theorem hasDerivAt_weightedExpectation [DecidableEq P] {φ ψ : ℂ → ℂ}
    (hφ : ∀ w, HasDerivAt φ (ψ w) w) (hψ : Continuous ψ) (hY : ∀ p, Measurable (Y p))
    (hC : ∀ p x, |Y p x| ≤ C) {f : 𝒳 → ℂ} (hf : IsBoundedMeasurable f) (s : P → ℂ) (a : P)
    (ζ₀ : ℂ) :
    HasDerivAt (fun ζ : ℂ => weightedExpectation ν Y f φ (s + ζ • coordVector a))
      (weightedExpectation ν Y (fun x => f x * (Y a x : ℂ)) ψ (s + ζ₀ • coordVector a)) ζ₀ := by
  have h := hasDerivAt_integral_line hφ hψ ν hf (isBoundedMeasurable_pairing hY hC s)
    (isBoundedMeasurable_coord hY hC a) ζ₀
  simpa only [weightedExpectation, pairing_add_smul] using h
theorem partialDeriv_weightedExpectation [DecidableEq P] {φ ψ : ℂ → ℂ}
    (hφ : ∀ w, HasDerivAt φ (ψ w) w) (hψ : Continuous ψ) (hY : ∀ p, Measurable (Y p))
    (hC : ∀ p x, |Y p x| ≤ C) {f : 𝒳 → ℂ} (hf : IsBoundedMeasurable f) (a : P) :
    partialDeriv a (weightedExpectation ν Y f φ) =
      weightedExpectation ν Y (fun x => f x * (Y a x : ℂ)) ψ := by
  funext s
  have h := (hasDerivAt_weightedExpectation (ν := ν) hφ hψ hY hC hf s a 0).deriv
  simpa [partialDeriv] using h
def listWeight (Y : P → 𝒳 → ℝ) (f : 𝒳 → ℂ) (l : List P) : 𝒳 → ℂ :=
  l.foldr (fun p g x => g x * (Y p x : ℂ)) f
theorem isBoundedMeasurable_listWeight (hY : ∀ p, Measurable (Y p)) (hC : ∀ p x, |Y p x| ≤ C)
    {f : 𝒳 → ℂ} (hf : IsBoundedMeasurable f) (l : List P) :
    IsBoundedMeasurable (listWeight Y f l) := by
  induction l with
  | nil => exact hf
  | cons a l ih => exact ih.mul (isBoundedMeasurable_coord hY hC a)
theorem listWeight_one (Y : P → 𝒳 → ℝ) (l : List P) (x : 𝒳) :
    listWeight Y (fun _ => 1) l x = (((l.map fun p => Y p x).prod : ℝ) : ℂ) := by
  induction l with
  | nil => simp [listWeight]
  | cons a l ih =>
    change listWeight Y (fun _ => 1) l x * (Y a x : ℂ) = _
    rw [ih]
    simp [mul_comm]
theorem iteratedPartials_exp [DecidableEq P] (hY : ∀ p, Measurable (Y p))
    (hC : ∀ p x, |Y p x| ≤ C) {f : 𝒳 → ℂ} (hf : IsBoundedMeasurable f) (l : List P) :
    iteratedPartials l (weightedExpectation ν Y f Complex.exp) =
      weightedExpectation ν Y (listWeight Y f l) Complex.exp := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change partialDeriv a (iteratedPartials l (weightedExpectation ν Y f Complex.exp)) = _
    rw [ih]
    exact partialDeriv_weightedExpectation Complex.hasDerivAt_exp Complex.continuous_exp hY hC
      (isBoundedMeasurable_listWeight hY hC hf l) a
theorem iteratedPartials_expTerm [DecidableEq P] (hY : ∀ p, Measurable (Y p))
    (hC : ∀ p x, |Y p x| ≤ C) {f : 𝒳 → ℂ} (hf : IsBoundedMeasurable f) (k : ℕ) (l : List P) :
    iteratedPartials l (weightedExpectation ν Y f (expTerm k)) =
      if l.length ≤ k then
        weightedExpectation ν Y (listWeight Y f l) (expTerm (k - l.length))
      else 0 := by
  induction l with
  | nil => simp [iteratedPartials, listWeight]
  | cons a l ih =>
    change partialDeriv a (iteratedPartials l (weightedExpectation ν Y f (expTerm k))) = _
    rw [ih]
    have hw := isBoundedMeasurable_listWeight hY hC hf l
    by_cases h : l.length ≤ k
    · rw [if_pos h]
      by_cases h' : l.length + 1 ≤ k
      · obtain ⟨j, hj⟩ : ∃ j, k - l.length = j + 1 := ⟨k - l.length - 1, by omega⟩
        have hj' : k - (a :: l).length = j := by simp only [List.length_cons]; omega
        rw [if_pos (by simpa using h'), hj, hj']
        exact partialDeriv_weightedExpectation (fun w => hasDerivAt_expTerm j w)
          (continuous_expTerm j) hY hC hw a
      · have hk : k - l.length = 0 := by omega
        rw [if_neg (by simpa using h'), hk]
        have hc : weightedExpectation ν Y (listWeight Y f l) (expTerm 0) =
            fun _ => ∫ x, listWeight Y f l x ∂ν := by
          funext s
          simp [weightedExpectation, expTerm]
        rw [hc]
        funext s
        simp [partialDeriv]
    · rw [if_neg h, if_neg (by simp only [List.length_cons]; omega)]
      funext s
      simp [partialDeriv]
theorem hasSum_weightedExpectation (hY : ∀ p, Measurable (Y p)) (hC : ∀ p x, |Y p x| ≤ C)
    {f : 𝒳 → ℂ} (hf : IsBoundedMeasurable f) (s : P → ℂ) :
    HasSum (fun k => weightedExpectation ν Y f (expTerm k) s)
      (weightedExpectation ν Y f Complex.exp s) := by
  obtain ⟨hfm, K, hK⟩ := hf
  have hterm : ∀ (k : ℕ) (x : 𝒳), ‖f x * expTerm k (pairing Y x s)‖ ≤
      |K| * ((C * l1Norm s) ^ k / (k.factorial : ℝ)) := by
    intro k x
    rw [norm_mul]
    exact mul_le_mul ((hK x).trans (le_abs_self K))
      (norm_expTerm_le k (norm_pairing_le hC x s)) (norm_nonneg _) (abs_nonneg K)
  have hmeas : ∀ k : ℕ, Measurable fun x => f x * expTerm k (pairing Y x s) := fun k =>
    hfm.mul ((continuous_expTerm k).measurable.comp (measurable_pairing hY s))
  have hint : ∀ k : ℕ, Integrable (fun x => f x * expTerm k (pairing Y x s)) ν := fun k =>
    Integrable.of_bound (hmeas k).aestronglyMeasurable _ (ae_of_all _ (hterm k))
  have hsum : Summable fun k : ℕ => ∫ x, ‖f x * expTerm k (pairing Y x s)‖ ∂ν := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun _ => norm_nonneg _) (fun k => ?_)
      ((Real.summable_pow_div_factorial (C * l1Norm s)).mul_left |K|)
    have h := norm_integral_le_of_norm_le_const (μ := ν)
      (f := fun x => ‖f x * expTerm k (pairing Y x s)‖)
      (C := |K| * ((C * l1Norm s) ^ k / (k.factorial : ℝ)))
      (ae_of_all _ fun x => by
        rw [norm_norm]
        exact hterm k x)
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _), probReal_univ, mul_one] at h
    exact h
  have h := hasSum_integral_of_summable_integral_norm hint hsum
  have hs : ∀ x, ∑' k, f x * expTerm k (pairing Y x s) =
      f x * Complex.exp (pairing Y x s) := fun x =>
    ((hasSum_expTerm (pairing Y x s)).mul_left (f x)).tsum_eq
  simp only [hs] at h
  exact h
theorem sum_range_ite_sub {M : Type*} [AddCommMonoid M] (g : ℕ → M) (m N : ℕ) :
    ∑ k ∈ Finset.range N, (if m ≤ k then g (k - m) else 0) = ∑ j ∈ Finset.range (N - m), g j := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : m ≤ N
    · rw [if_pos h, show N + 1 - m = (N - m) + 1 by omega, Finset.sum_range_succ]
    · rw [if_neg h, show N + 1 - m = N - m by omega, add_zero]
theorem famMGF_eq (ν : Measure 𝒳) (Y : P → 𝒳 → ℝ) :
    famMGF ν Y = weightedExpectation ν Y (fun _ => 1) Complex.exp := by
  funext s
  simp [famMGF, weightedExpectation, pairing]
theorem famSeriesTerm_eq (ν : Measure 𝒳) (Y : P → 𝒳 → ℝ) (k : ℕ) :
    famSeriesTerm ν Y k = weightedExpectation ν Y (fun _ => 1) (expTerm k) := by
  funext s
  simp only [famSeriesTerm, weightedExpectation, expTerm, pairing, one_mul]
  rw [integral_const_mul]
theorem continuous_famMGF (hY : ∀ p, Measurable (Y p))
    (hC : ∀ p x, |Y p x| ≤ C) : Continuous (famMGF ν Y) := by
  rw [continuous_iff_continuousAt]
  intro s₀
  have hnb : {s : P → ℂ | l1Norm s < l1Norm s₀ + 1} ∈ 𝓝 s₀ :=
    (isOpen_l1Ball _).mem_nhds (by
      change l1Norm s₀ < l1Norm s₀ + 1
      linarith)
  refine continuousAt_of_dominated (bound := fun _ => Real.exp (|C| * (l1Norm s₀ + 1)))
    (Eventually.of_forall fun s => ?_) ?_ (integrable_const _) (ae_of_all _ fun x => ?_)
  · exact (Complex.measurable_exp.comp (measurable_pairing hY s)).aestronglyMeasurable
  · filter_upwards [hnb] with s hs
    refine ae_of_all _ fun x => ?_
    have h1 : ‖pairing Y x s‖ ≤ |C| * (l1Norm s₀ + 1) := by
      refine (norm_pairing_le hC x s).trans ?_
      exact mul_le_mul (le_abs_self C) (le_of_lt hs) (l1Norm_nonneg s) (abs_nonneg C)
    have h2 : ‖Complex.exp (∑ p, s p * (Y p x : ℂ))‖ ≤ Real.exp ‖pairing Y x s‖ :=
      Complex.norm_exp_le_exp_norm _
    exact h2.trans (Real.exp_le_exp.2 h1)
  · exact (Complex.continuous_exp.comp (continuous_pairing Y x)).continuousAt
end Weighted
section Holomorphy
variable {P : Type*} [Fintype P] [DecidableEq P]
theorem holomorphicOnSet_of_separately {U : Set (P → ℂ)} {F : (P → ℂ) → ℂ} (hU : IsOpen U)
    (hc : ContinuousOn F U)
    (hd : ∀ a ∈ U, ∀ i : P, ∀ᶠ ζ in 𝓝 (0 : ℂ),
      DifferentiableAt ℂ (fun ζ : ℂ => F (a + ζ • coordVector i)) ζ) :
    HolomorphicOnSet U F := by
  intro N e
  have hΦ : Continuous (relabelCoordinates e) := by
    refine continuous_pi fun i => ?_
    simpa [relabelCoordinates, Equiv.arrowCongr] using continuous_apply (e.symm i)
  have key : ∀ (a : Coordinates.ComplexCoordinates N) (j : Fin N) (ζ : ℂ),
      relabelCoordinates e (a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j) =
        relabelCoordinates e a + ζ • coordVector (e j) := by
    intro a j ζ
    funext i
    by_cases hi : i = e j
    · subst hi
      simp [relabelCoordinates, Equiv.arrowCongr, Coordinates.ComplexCoordinates.stdBasisVector,
        coordVector]
    · have : e.symm i ≠ j := fun h => hi (by rw [← h]; simp)
      simp [relabelCoordinates, Equiv.arrowCongr, Coordinates.ComplexCoordinates.stdBasisVector,
        coordVector, hi, this]
  have hu : Continuous (Equiv.funUnique (Fin 1) ℂ).symm := continuous_pi fun _ => by
    simpa [Equiv.funUnique] using (continuous_id' : Continuous fun a : ℂ => a)
  refine ⟨hU.preimage hΦ, hu.comp_continuousOn (hc.comp hΦ.continuousOn fun _ h => h),
    fun a ha j => ?_⟩
  filter_upwards [hd (relabelCoordinates e a) ha (e j)] with ζ hζ
  refine differentiableAt_pi.2 fun i => ?_
  have : (fun ζ : ℂ => ((Equiv.funUnique (Fin 1) ℂ).symm ∘ F ∘ relabelCoordinates e)
        (a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j) i) =
      fun ζ : ℂ => F (relabelCoordinates e a + ζ • coordVector (e j)) := by
    funext ζ'
    simp [key, Equiv.funUnique]
  rw [this]
  exact hζ
end Holomorphy
section Main
variable {𝒳 P : Type*} [MeasurableSpace 𝒳] [Fintype P] {ν : Measure 𝒳} [IsProbabilityMeasure ν]
  {Y : P → 𝒳 → ℝ} {C : ℝ}
theorem differentiableAt_famMGF_line [DecidableEq P] (hY : ∀ p, Measurable (Y p))
    (hC : ∀ p x, |Y p x| ≤ C) (a : P → ℂ) (i : P) (ζ : ℂ) :
    DifferentiableAt ℂ (fun ζ : ℂ => famMGF ν Y (a + ζ • coordVector i)) ζ := by
  rw [famMGF_eq]
  exact (hasDerivAt_weightedExpectation Complex.hasDerivAt_exp Complex.continuous_exp hY hC
    isBoundedMeasurable_one a i ζ).differentiableAt
theorem norm_famSeriesTerm_le (hC : ∀ p x, |Y p x| ≤ C) (k : ℕ) (s : P → ℂ) :
    ‖famSeriesTerm ν Y k s‖ ≤ (C * l1Norm s) ^ k / (k.factorial : ℝ) := by
  rw [famSeriesTerm_eq]
  have h := norm_integral_le_of_norm_le_const (μ := ν)
    (f := fun x => (1 : ℂ) * expTerm k (pairing Y x s))
    (C := (C * l1Norm s) ^ k / (k.factorial : ℝ)) (ae_of_all _ fun x => by
      rw [one_mul]
      exact norm_expTerm_le k (norm_pairing_le hC x s))
  rw [probReal_univ, mul_one] at h
  exact h
theorem famSeriesTerm_eq_sum (hY : ∀ p, Measurable (Y p)) (hC : ∀ p x, |Y p x| ≤ C) (k : ℕ)
    (s : P → ℂ) : famSeriesTerm ν Y k s =
      1 / (k.factorial : ℂ) *
        ∑ q : Fin k → P, (∏ i, s (q i)) * ((∫ x, ∏ i, Y (q i) x ∂ν : ℝ) : ℂ) := by
  unfold famSeriesTerm
  congr 1
  simp_rw [Fintype.sum_pow, Finset.prod_mul_distrib]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun q _ => ?_
    rw [integral_const_mul]
    congr 1
    rw [← integral_complex_ofReal]
    simp
  · intro q _
    have hw : IsBoundedMeasurable fun x => ∏ i, (Y (q i) x : ℂ) := by
      induction k with
      | zero => simpa using isBoundedMeasurable_one
      | succ k ih =>
        simp_rw [Fin.prod_univ_succ]
        exact (isBoundedMeasurable_coord hY hC (q 0)).mul
          (ih (fun i => q i.succ) (Finset.mem_univ _))
    exact (hw.integrable ν).const_mul _
theorem exists_homogeneous_famSeriesTerm (hY : ∀ p, Measurable (Y p)) (hC : ∀ p x, |Y p x| ≤ C)
    (k : ℕ) :
    ∃ f : MvPolynomial P ℂ,
      f.IsHomogeneous k ∧ ∀ s, MvPolynomial.eval s f = famSeriesTerm ν Y k s := by
  refine ⟨MvPolynomial.C (1 / (k.factorial : ℂ)) * ∑ q : Fin k → P,
    MvPolynomial.C ((∫ x, ∏ i, Y (q i) x ∂ν : ℝ) : ℂ) * ∏ i, MvPolynomial.X (q i), ?_, fun s => ?_⟩
  · refine MvPolynomial.IsHomogeneous.C_mul ?_ _
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun q _ => ?_
    refine MvPolynomial.IsHomogeneous.C_mul ?_ _
    have h := MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset (Fin k))
      (fun i => (MvPolynomial.X (q i) : MvPolynomial P ℂ)) (fun _ => 1)
      (fun i _ => MvPolynomial.isHomogeneous_X ℂ (q i))
    simpa using h
  · rw [famSeriesTerm_eq_sum hY hC]
    simp [map_sum, map_prod, mul_comm]
theorem seriesExpansion [LinearOrder P] (hY : ∀ p, Measurable (Y p)) (hC0 : 0 ≤ C)
    (hC : ∀ p x, |Y p x| ≤ C) : SeriesExpansion ν Y C := by
  have h1 : IsBoundedMeasurable (fun _ => 1 : 𝒳 → ℂ) := isBoundedMeasurable_one
  have hsum : ∀ s, HasSum (fun k => famSeriesTerm ν Y k s) (famMGF ν Y s) := fun s => by
    simpa only [famSeriesTerm_eq, famMGF_eq] using
      hasSum_weightedExpectation hY hC h1 s
  refine ⟨fun s => ?_, famSeriesTerm_eq_sum hY hC, exists_homogeneous_famSeriesTerm hY hC,
    norm_famSeriesTerm_le hC, fun B hB => ?_, ?_, fun l s => ?_, ?_⟩
  · exact (hsum s).tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  · obtain ⟨R, hR⟩ := hB.exists_norm_le
    have hs : ∀ s ∈ B, l1Norm s ≤ (Fintype.card P : ℝ) * |R| := by
      intro s hs
      have h := Finset.sum_le_card_nsmul (Finset.univ : Finset P) (fun p => ‖s p‖) |R|
        (fun p _ => (norm_le_pi_norm s p).trans ((hR s hs).trans (le_abs_self R)))
      simpa [l1Norm, nsmul_eq_mul] using h
    have h := tendstoUniformlyOn_tsum_nat
      (Real.summable_pow_div_factorial (C * ((Fintype.card P : ℝ) * |R|)))
      (f := fun k s => famSeriesTerm ν Y k s) (s := B) (fun k s hsB => by
        refine (norm_famSeriesTerm_le hC k s).trans ?_
        have := hs s hsB
        have h0 := l1Norm_nonneg s
        gcongr)
    have heq : (fun s => ∑' k, famSeriesTerm ν Y k s) = famMGF ν Y :=
      funext fun s => (hsum s).tsum_eq
    rw [heq] at h
    rw [Metric.tendstoUniformlyOn_iff] at h ⊢
    intro ε hε
    exact (tendsto_add_atTop_nat 1).eventually (h ε hε)
  · exact holomorphicOnSet_of_separately isOpen_univ
      (continuous_famMGF hY hC).continuousOn
      fun a _ i => Eventually.of_forall fun ζ =>
        differentiableAt_famMGF_line hY hC a i ζ
  · have hk : ∀ k₀ : ℕ, ∑ k ∈ Finset.range (k₀ + 1),
        iteratedPartials l (famSeriesTerm ν Y k) s =
        ∑ j ∈ Finset.range (k₀ + 1 - l.length),
          weightedExpectation ν Y (listWeight Y (fun _ => 1) l) (expTerm j) s := by
      intro k₀
      rw [← sum_range_ite_sub]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [famSeriesTerm_eq, iteratedPartials_expTerm hY hC h1]
      split_ifs <;> rfl
    simp only [hk]
    rw [famMGF_eq, iteratedPartials_exp hY hC h1]
    exact (hasSum_weightedExpectation hY hC (isBoundedMeasurable_listWeight hY hC h1 l)
      s).tendsto_sum_nat.comp
      ((tendsto_sub_atTop_nat l.length).comp (tendsto_add_atTop_nat 1))
  · simp [famMGF]
theorem setPartial_famMGF_zero [LinearOrder P] (hY : ∀ p, Measurable (Y p))
    (hC : ∀ p x, |Y p x| ≤ C) (J : Finset P) :
    setPartial J (famMGF ν Y) 0 = ((∫ x, ∏ p ∈ J, Y p x ∂ν : ℝ) : ℂ) := by
  rw [famMGF_eq, setPartial, iteratedPartials_exp hY hC isBoundedMeasurable_one]
  have h : ∀ x, listWeight Y (fun _ => 1) J.sort x * Complex.exp (pairing Y x 0) =
      ((∏ p ∈ J, Y p x : ℝ) : ℂ) := by
    intro x
    have h0 : pairing Y x 0 = 0 := by simp [pairing]
    rw [listWeight_one, h0, Complex.exp_zero, mul_one]
    congr 1
    rw [← List.prod_toFinset _ (Finset.sort_nodup _ _), Finset.sort_toFinset]
  simp only [weightedExpectation, h]
  exact integral_complex_ofReal
theorem boundRadius_pos {C : ℝ} : 0 < boundRadius C := by
  unfold boundRadius
  split_ifs with h
  · exact div_pos (Real.log_pos one_lt_two) h
  · exact one_pos
theorem isLogRadius_boundRadius (hY : ∀ p, Measurable (Y p)) (hC0 : 0 ≤ C)
    (hC : ∀ p x, |Y p x| ≤ C) : IsLogRadius ν Y (boundRadius C) := by
  refine ⟨boundRadius_pos, fun s hs => ?_⟩
  have hB : C * l1Norm s < Real.log 2 := by
    rcases hC0.lt_or_eq with h | h
    · have hs' : l1Norm s < Real.log 2 / C := by
        have : l1Norm s < boundRadius C := hs
        simpa [boundRadius, h] using this
      rw [lt_div_iff₀ h] at hs'
      linarith
    · rw [← h, zero_mul]
      exact Real.log_pos one_lt_two
  have hexp : Real.exp (C * l1Norm s) < 2 := (Real.lt_log_iff_exp_lt two_pos).1 hB
  have hm : Measurable fun x => Complex.exp (pairing Y x s) :=
    Complex.measurable_exp.comp (measurable_pairing hY s)
  have hb : ∀ x, ‖Complex.exp (pairing Y x s)‖ ≤ Real.exp (C * l1Norm s) := fun x =>
    (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.2 (norm_pairing_le hC x s))
  have hint : Integrable (fun x => Complex.exp (pairing Y x s)) ν :=
    Integrable.of_bound hm.aestronglyMeasurable _ (ae_of_all _ hb)
  have hΓ : famMGF ν Y s - 1 = ∫ x, (Complex.exp (pairing Y x s) - 1) ∂ν := by
    rw [integral_sub hint (integrable_const _)]
    simp [famMGF, pairing]
  have hpt : ∀ x, ‖Complex.exp (pairing Y x s) - 1‖ ≤ Real.exp (C * l1Norm s) - 1 := by
    intro x
    have h := Complex.norm_exp_sub_sum_le_exp_norm_sub_sum (pairing Y x s) 1
    simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at h
    have h2 := Real.exp_le_exp.2 (norm_pairing_le hC x s)
    linarith
  have h := norm_integral_le_of_norm_le_const (μ := ν) (ae_of_all _ hpt)
  rw [probReal_univ, mul_one, ← hΓ] at h
  linarith
theorem logExpansion (hY : ∀ p, Measurable (Y p)) (hC0 : 0 ≤ C)
    (hC : ∀ p x, |Y p x| ≤ C) [DecidableEq P] : LogExpansion ν Y C := by
  have hcont := continuous_famMGF (ν := ν) hY hC
  refine ⟨⟨_, isLogRadius_boundRadius hY hC0 hC⟩, fun ρ hρ => ?_, ?_, fun ρ hρ s hs => ?_,
    isLogRadius_boundRadius hY hC0 hC⟩
  · have hmaps : ∀ s ∈ l1Ball (ι := P) ρ, famMGF ν Y s ∈ unitDiscAtOne := hρ.2
    refine holomorphicOnSet_of_separately (isOpen_l1Ball ρ)
      (differentiableOn_principalLog.continuousOn.comp hcont.continuousOn hmaps) fun a ha i => ?_
    have hline : Continuous fun ζ : ℂ => a + ζ • (coordVector i : P → ℂ) := by fun_prop
    have hnb : ∀ᶠ ζ in 𝓝 (0 : ℂ), a + ζ • (coordVector i : P → ℂ) ∈ l1Ball (ι := P) ρ :=
      hline.continuousAt.eventually_mem ((isOpen_l1Ball ρ).mem_nhds (by simpa using ha))
    filter_upwards [hnb] with ζ hζ
    exact (hasDerivAt_principalLog (hmaps _ hζ)).differentiableAt.comp ζ
      (differentiableAt_famMGF_line hY hC a i ζ)
  · have h0 : famMGF ν Y 0 = 1 := by simp [famMGF]
    simp [famLogMGF, h0, principalLog_one]
  · exact exp_principalLog (hρ.2 s hs)
end Main
theorem statement_holds : Statement := by
  classical
  intro 𝒳 _ ν _
  refine ⟨fun P _ _ _ Y C hY hC0 hC =>
    ⟨seriesExpansion hY hC0 hC, setPartial_famMGF_zero hY hC, logExpansion hY hC0 hC⟩,
    fun n X hX => ?_⟩
  choose c hc using fun i => (hX.isBounded i).bounded
  have hC0 : 0 ≤ ∑ i, |c i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hC : ∀ i x, |X i x| ≤ ∑ i, |c i| := fun i x =>
    ((hc i x).trans (le_abs_self _)).trans
      (Finset.single_le_sum (f := fun i => |c i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i))
  have hY : ∀ i, Measurable (X i) := fun i => (hX.isBounded i).measurable
  have hL := logExpansion (ν := ν) hY hC0 hC
  refine ⟨l1Ball (boundRadius (∑ i, |c i|)), ?_, hL.holomorphic _ hL.radius_of_bound⟩
  change l1Norm (0 : Fin n → ℂ) < _
  rw [l1Norm_zero]
  exact boundRadius_pos
end YangMills.Construction.SourcesAndGluing.BoundedMGF
end
