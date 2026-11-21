import YangMills.Construction.SummableBoundsOfTheFlow.PowersOfACut
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.ColdStepAtMirrorFrames
open scoped ContDiff
namespace YangMills.Construction
namespace Estimates
variable {ρ : ℝ} {p : ℝ → ℝ}
private theorem contDiffOn_iteratedDeriv_cutoff (hp : IsCutoff ρ p) (j : ℕ) :
    ContDiffOn ℝ ∞ (iteratedDeriv j p) (Set.Ioo 0 ρ) := by
  induction j with
  | zero =>
    simp only [iteratedDeriv_zero]
    exact (hp.smooth.mono Set.Ioo_subset_Ico_self).of_le (by exact_mod_cast le_rfl)
  | succ j ih =>
    rw [iteratedDeriv_succ]
    exact ((contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioo).1 ih).2
abbrev _root_.YangMills.SharedProofs.p62039 := @contDiffOn_iteratedDeriv_cutoff
private theorem differentiableOn_iteratedDeriv_cutoff (hp : IsCutoff ρ p) (j : ℕ) :
    DifferentiableOn ℝ (iteratedDeriv j p) (Set.Ioo 0 ρ) :=
  ((contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioo).1 (contDiffOn_iteratedDeriv_cutoff hp j)).1
private theorem iteratedDeriv_cutoff_eq_zero_of_lt (hp : IsCutoff ρ p) {u : ℝ} (hu0 : 0 < u)
    (hu1 : u < 5 * ρ / 8) (j : ℕ) (hj : 1 ≤ j) :
    iteratedDeriv j p u = 0 := by
  have hev : p =ᶠ[nhds u] fun _ => 0 := by
    filter_upwards [Ioo_mem_nhds hu0 hu1] with v hv
    exact hp.vanish_small v hv.1.le hv.2.le
  rw [hev.iteratedDeriv_eq]
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  simp
private theorem differentiableOn_cutoff (hp : IsCutoff ρ p) : DifferentiableOn ℝ p (Set.Ioo 0 ρ) := by
  have := differentiableOn_iteratedDeriv_cutoff hp 0
  simpa using this
private theorem deriv_cutoff_nonneg (hp : IsCutoff ρ p) (hρ : 0 < ρ) {u : ℝ} (hu0 : 0 < u)
    (hu1 : u < ρ) : 0 ≤ deriv p u := by
  have hconv : ConvexOn ℝ (Set.Ioo 0 ρ) p :=
    hp.convex.subset (fun x hx => ⟨hx.1.le, hx.2⟩) (convex_Ioo 0 ρ)
  have hd : ∀ x ∈ Set.Ioo 0 ρ, DifferentiableAt ℝ p x := fun x hx =>
    (differentiableOn_cutoff hp x hx).differentiableAt (Ioo_mem_nhds hx.1 hx.2)
  have hmono := hconv.monotoneOn_deriv hd
  have hv : ρ / 4 ∈ Set.Ioo 0 ρ := ⟨by positivity, by linarith⟩
  have hz : deriv p (ρ / 4) = 0 := by
    have := iteratedDeriv_cutoff_eq_zero_of_lt hp (u := ρ / 4) (by positivity) (by linarith) 1 le_rfl
    rwa [iteratedDeriv_one] at this
  by_cases hu : ρ / 4 ≤ u
  · have := hmono hv ⟨hu0, hu1⟩ hu
    rwa [hz] at this
  · push Not at hu
    have := iteratedDeriv_cutoff_eq_zero_of_lt hp hu0 (by linarith) 1 le_rfl
    rw [iteratedDeriv_one] at this
    exact this.ge
private theorem cutoff_nonneg (hp : IsCutoff ρ p) (hρ : 0 < ρ) {u : ℝ} (hu0 : 0 < u)
    (hu1 : u < ρ) : 0 ≤ p u := by
  by_cases hu : u ≤ ρ / 4
  · rw [hp.vanish_small u hu0.le (by linarith)]
  · push Not at hu
    have hmono : MonotoneOn p (Set.Ioo 0 ρ) :=
      monotoneOn_of_deriv_nonneg (convex_Ioo 0 ρ) (differentiableOn_cutoff hp).continuousOn
        (by rw [interior_Ioo]; exact differentiableOn_cutoff hp)
        (by rw [interior_Ioo]; exact fun x hx => deriv_cutoff_nonneg hp hρ hx.1 hx.2)
    have h2 := hmono (a := ρ / 4) (b := u) ⟨by positivity, by linarith⟩ ⟨hu0, hu1⟩ hu.le
    rwa [hp.vanish_small (ρ / 4) (by positivity) (by linarith)] at h2
private theorem exists_bound_iteratedDeriv_cutoff_le (hp : IsCutoff ρ p) {u₁ : ℝ} (h1 : u₁ < ρ)
    (j : ℕ) (hj : 1 ≤ j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u, 0 < u → u ≤ u₁ → |iteratedDeriv j p u| ≤ C := by
  by_cases hu : ρ / 4 ≤ u₁
  · have hcomp : IsCompact (Set.Icc (ρ / 4) u₁) := isCompact_Icc
    have hsub : Set.Icc (ρ / 4) u₁ ⊆ Set.Ioo 0 ρ := fun v hv => ⟨by linarith [hv.1], by linarith [hv.2]⟩
    obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn
      ((contDiffOn_iteratedDeriv_cutoff hp j).continuousOn.mono hsub)
    refine ⟨max C 0, le_max_right _ _, fun u h0 hu1 => ?_⟩
    by_cases hv : ρ / 4 ≤ u
    · exact (hC u ⟨hv, hu1⟩).trans (le_max_left _ _)
    · push Not at hv
      rw [iteratedDeriv_cutoff_eq_zero_of_lt hp h0 (by linarith) j hj, abs_zero]
      exact le_max_right _ _
  · push Not at hu
    refine ⟨0, le_rfl, fun u h0 hu1 => ?_⟩
    rw [iteratedDeriv_cutoff_eq_zero_of_lt hp h0 (by linarith) j hj, abs_zero]
private theorem cutoff_closed_form_near_edge (hp : IsCutoff ρ p) (hρ : 0 < ρ) :
    ∃ (u₁ A B : ℝ), 0 < u₁ ∧ u₁ < ρ ∧ ρ - 1 ≤ u₁ ∧
      (∀ u, u₁ < u → u < ρ → deriv p u = A + 1 / 3 * ((ρ - u) ^ 3)⁻¹) ∧
      (∀ u, u₁ < u → u < ρ → p u = B + A * u + 1 / 6 * ((ρ - u) ^ 2)⁻¹) ∧
      (∀ u, u₁ < u → u < ρ → deriv (deriv p) u = ((ρ - u) ^ 4)⁻¹) ∧
      ∀ n : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ u, u₁ < u → u < ρ →
        iteratedDeriv (n + 2) p u = c * ((ρ - u) ^ (n + 4))⁻¹ := by
  obtain ⟨u₀, hu₀, hedge⟩ := hp.rim_second_deriv
  set u₁ : ℝ := max (max u₀ (ρ / 2)) (ρ - 1) with hu₁
  have h1 : u₁ < ρ := max_lt (max_lt hu₀ (by linarith)) (by linarith)
  have h0 : 0 < u₁ :=
    lt_of_lt_of_le (by positivity : 0 < ρ / 2) ((le_max_right _ _).trans (le_max_left _ _))
  have hI : Set.Ioo u₁ ρ ⊆ Set.Ioo 0 ρ := fun v hv => ⟨h0.trans hv.1, hv.2⟩
  have hpos : ∀ u ∈ Set.Ioo u₁ ρ, (ρ - u) ≠ 0 := fun u hu => by have := hu.2; intro h; linarith
  have hu0 : ∀ u, u₁ < u → u₀ < u := fun u hu =>
    lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hu
  have hder : ∀ (k : ℕ) (u : ℝ), u ∈ Set.Ioo u₁ ρ →
      HasDerivAt (fun v : ℝ => ((ρ - v) ^ k)⁻¹) ((k : ℝ) * ((ρ - u) ^ (k + 1))⁻¹) u := by
    intro k u hu
    have hne := hpos u hu
    have h2 : HasDerivAt (fun v : ℝ => (ρ - v) ^ k) ((k : ℝ) * (ρ - u) ^ (k - 1) * (-1)) u :=
      ((hasDerivAt_id u).const_sub ρ).fun_pow k
    have h3 := h2.fun_inv (pow_ne_zero k hne)
    refine h3.congr_deriv ?_
    by_cases hk : k = 0
    · subst hk; simp
    · obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      field_simp
      ring
  have hP1 : ∃ A, Set.EqOn (deriv p) (fun v => 1 / 3 * ((ρ - v) ^ 3)⁻¹ + A) (Set.Ioo u₁ ρ) := by
    have hd1 : DifferentiableOn ℝ (deriv p) (Set.Ioo u₁ ρ) := by
      have := (differentiableOn_iteratedDeriv_cutoff hp 1).mono hI
      simpa [iteratedDeriv_one] using this
    have hd2 : DifferentiableOn ℝ (fun v : ℝ => 1 / 3 * ((ρ - v) ^ 3)⁻¹) (Set.Ioo u₁ ρ) := fun u hu =>
      ((hder 3 u hu).const_mul (1 / 3 : ℝ)).differentiableAt.differentiableWithinAt
    refine isOpen_Ioo.exists_eq_add_of_deriv_eq isPreconnected_Ioo hd1 hd2 fun u hu => ?_
    rw [hedge u (hu0 u hu.1) hu.2, ((hder 3 u hu).const_mul (1 / 3 : ℝ)).deriv]
    push_cast
    ring
  obtain ⟨A, hA⟩ := hP1
  have hP2 : ∃ B, Set.EqOn p (fun v => (A * v + 1 / 6 * ((ρ - v) ^ 2)⁻¹) + B) (Set.Ioo u₁ ρ) := by
    have hd1 : DifferentiableOn ℝ p (Set.Ioo u₁ ρ) := (differentiableOn_cutoff hp).mono hI
    have hd3 : ∀ u ∈ Set.Ioo u₁ ρ, HasDerivAt (fun v : ℝ => A * v + 1 / 6 * ((ρ - v) ^ 2)⁻¹)
        (A * 1 + 1 / 6 * (((2 : ℕ) : ℝ) * ((ρ - u) ^ (2 + 1))⁻¹)) u := fun u hu =>
      ((hasDerivAt_id u).const_mul A).add ((hder 2 u hu).const_mul (1 / 6 : ℝ))
    have hd2 : DifferentiableOn ℝ (fun v : ℝ => A * v + 1 / 6 * ((ρ - v) ^ 2)⁻¹) (Set.Ioo u₁ ρ) :=
      fun u hu => (hd3 u hu).differentiableAt.differentiableWithinAt
    refine isOpen_Ioo.exists_eq_add_of_deriv_eq isPreconnected_Ioo hd1 hd2 fun u hu => ?_
    rw [(hd3 u hu).deriv, hA hu]
    push_cast
    ring
  obtain ⟨B, hB⟩ := hP2
  refine ⟨u₁, A, B, h0, h1, le_max_right _ _, fun u h2 h3 => ?_, fun u h2 h3 => ?_,
    fun u h2 h3 => hedge u (hu0 u h2) h3, fun n => ?_⟩
  · rw [hA ⟨h2, h3⟩]; ring
  · rw [hB ⟨h2, h3⟩]; ring
  · induction n with
    | zero =>
      refine ⟨1, zero_le_one, fun u h2 h3 => ?_⟩
      have : iteratedDeriv 2 p = deriv (deriv p) := by
        rw [iteratedDeriv_succ, iteratedDeriv_one]
      simp only [zero_add, one_mul]
      rw [this, hedge u (hu0 u h2) h3]
    | succ n ih =>
      obtain ⟨c, hc, hcu⟩ := ih
      refine ⟨c * ((n + 4 : ℕ) : ℝ), by positivity, fun u h2 h3 => ?_⟩
      have hu : u ∈ Set.Ioo u₁ ρ := ⟨h2, h3⟩
      have e1 : iteratedDeriv (n + 1 + 2) p = deriv (iteratedDeriv (n + 2) p) := by
        rw [show n + 1 + 2 = (n + 2) + 1 by ring, iteratedDeriv_succ]
      have hev : iteratedDeriv (n + 2) p =ᶠ[nhds u] fun v => c * ((ρ - v) ^ (n + 4))⁻¹ := by
        filter_upwards [Ioo_mem_nhds h2 h3] with v hv
        exact hcu v hv.1 hv.2
      rw [e1, hev.deriv_eq, ((hder (n + 4) u hu).const_mul c).deriv]
      ring_nf
private theorem pow_mul_exp_neg_sq_le (y : ℝ) (hy : 1 ≤ y) (k : ℕ) :
    y ^ (3 * k) * Real.exp (-(y ^ 2 / 6)) ≤ 6 ^ (3 * k) * ((3 * k).factorial : ℝ) := by
  have h1 := Real.pow_div_factorial_le_exp (y ^ 2 / 6) (by positivity) (3 * k)
  have hf : (0 : ℝ) < ((3 * k).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  rw [div_le_iff₀ hf] at h1
  have h2 : y ^ (3 * k) ≤ (y ^ 2) ^ (3 * k) := by
    apply pow_le_pow_left₀ (by linarith)
    nlinarith
  have h3 : (y ^ 2 / 6) ^ (3 * k) * 6 ^ (3 * k) = (y ^ 2) ^ (3 * k) := by
    rw [← mul_pow]; congr 1; ring
  have hEE : Real.exp (y ^ 2 / 6) * Real.exp (-(y ^ 2 / 6)) = 1 := by
    rw [← Real.exp_add]; simp
  calc y ^ (3 * k) * Real.exp (-(y ^ 2 / 6)) ≤ (y ^ 2) ^ (3 * k) * Real.exp (-(y ^ 2 / 6)) := by gcongr
    _ = (y ^ 2 / 6) ^ (3 * k) * Real.exp (-(y ^ 2 / 6)) * 6 ^ (3 * k) := by rw [← h3]; ring
    _ ≤ (Real.exp (y ^ 2 / 6) * ((3 * k).factorial : ℝ)) * Real.exp (-(y ^ 2 / 6)) * 6 ^ (3 * k) := by
        gcongr
    _ = (Real.exp (y ^ 2 / 6) * Real.exp (-(y ^ 2 / 6))) * ((3 * k).factorial : ℝ) * 6 ^ (3 * k) := by
        ring
    _ = _ := by rw [hEE]; ring
theorem cutoffDerivBoundsStatement_holds : cutoffDerivBoundsStatement := by
  intro ρ p hρ hp
  obtain ⟨u₁, A, B, h0, h1, hu1, hP, hp', hP2, hit⟩ := cutoff_closed_form_near_edge hp hρ
  have hy1 : ∀ u, u₁ < u → u < ρ → 1 ≤ (ρ - u)⁻¹ := by
    intro u h2 h3
    have : 0 < ρ - u := by linarith
    exact (one_le_inv₀ this).2 (by linarith)
  have hform : ∀ u, u₁ < u → u < ρ → deriv p u = A + 1 / 3 * (ρ - u)⁻¹ ^ 3 := by
    intro u h2 h3
    rw [hP u h2 h3, inv_pow]
  have hval : ∀ u, u₁ < u → u < ρ → p u = B + A * u + 1 / 6 * (ρ - u)⁻¹ ^ 2 := by
    intro u h2 h3
    rw [hp' u h2 h3, inv_pow]
  have hcube : ∀ y : ℝ, 1 ≤ y → y ≤ y ^ 3 ∧ 1 ≤ y ^ 3 := by
    intro y hy
    have h2 : y ≤ y ^ 2 := by nlinarith
    have h3 : y ^ 2 ≤ y ^ 3 := by nlinarith [sq_nonneg y]
    exact ⟨h2.trans h3, hy.trans (h2.trans h3)⟩
  have hy3 : ∀ u, u₁ < u → u < ρ → (ρ - u)⁻¹ ≤ 3 * (1 + |A|) * (1 + deriv p u) := by
    intro u h2 h3
    have hy := hy1 u h2 h3
    have hn := deriv_cutoff_nonneg hp hρ (h0.trans h2) h3
    have hf := hform u h2 h3
    set y := (ρ - u)⁻¹ with hyd
    have h4 := (hcube y hy).1
    have h5 := neg_abs_le A
    have h6 := abs_nonneg A
    have h7 : y ^ 3 = 3 * (deriv p u - A) := by rw [hf]; ring
    have h8 : 0 ≤ |A| * deriv p u := mul_nonneg h6 hn
    nlinarith
  refine ⟨fun u h h' => deriv_cutoff_nonneg hp hρ h h',
    fun u h h' j hj => iteratedDeriv_cutoff_eq_zero_of_lt hp h h' j hj, ?_, ?_, ?_, ?_⟩
  · intro k
    obtain ⟨C1, hC1, hmid⟩ := exists_bound_iteratedDeriv_cutoff_le hp h1 1 le_rfl
    set Cedge : ℝ := (2 + |A|) ^ k * (6 ^ (3 * k) * ((3 * k).factorial : ℝ)) *
      Real.exp (|B| + |A| * ρ) with hCedge
    have hCe0 : 0 ≤ Cedge := by positivity
    refine ⟨max ((1 + C1) ^ k) Cedge, le_trans hCe0 (le_max_right _ _), fun u hu0 huρ => ?_⟩
    have hn := deriv_cutoff_nonneg hp hρ hu0 huρ
    by_cases hu : u ≤ u₁
    · have h2 := hmid u hu0 hu
      rw [iteratedDeriv_one, abs_of_nonneg hn] at h2
      have h3 : Real.exp (-p u) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have := cutoff_nonneg hp hρ hu0 huρ
        linarith
      refine le_trans ?_ (le_max_left _ _)
      calc (1 + deriv p u) ^ k * Real.exp (-p u) ≤ (1 + C1) ^ k * 1 := by gcongr
        _ = _ := mul_one _
    · push Not at hu
      refine le_trans ?_ (le_max_right _ _)
      have hy := hy1 u hu huρ
      have hf := hform u hu huρ
      have hv := hval u hu huρ
      set y := (ρ - u)⁻¹ with hyd
      obtain ⟨-, hc1⟩ := hcube y hy
      have h6 := abs_nonneg A
      have h2 : 1 + deriv p u ≤ (2 + |A|) * y ^ 3 := by
        rw [hf]
        have := le_abs_self A
        nlinarith
      have h3 : -p u ≤ (|B| + |A| * ρ) + -(y ^ 2 / 6) := by
        rw [hv]
        have e1 := neg_abs_le B
        have e2 : -(A * u) ≤ |A| * ρ := by
          have e3 := neg_le_abs (A * u)
          rw [abs_mul, abs_of_pos hu0] at e3
          have e4 := mul_le_mul_of_nonneg_left huρ.le h6
          linarith
        linarith
      have h4 : (1 + deriv p u) ^ k ≤ ((2 + |A|) * y ^ 3) ^ k := pow_le_pow_left₀ (by linarith) h2 k
      have h5 : Real.exp (-p u) ≤ Real.exp (|B| + |A| * ρ) * Real.exp (-(y ^ 2 / 6)) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.2 h3
      have h7 := pow_mul_exp_neg_sq_le y hy k
      calc (1 + deriv p u) ^ k * Real.exp (-p u)
          ≤ ((2 + |A|) * y ^ 3) ^ k * (Real.exp (|B| + |A| * ρ) * Real.exp (-(y ^ 2 / 6))) := by gcongr
        _ = (2 + |A|) ^ k * (y ^ (3 * k) * Real.exp (-(y ^ 2 / 6))) * Real.exp (|B| + |A| * ρ) := by
            rw [mul_pow, ← pow_mul]; ring
        _ ≤ (2 + |A|) ^ k * (6 ^ (3 * k) * ((3 * k).factorial : ℝ)) * Real.exp (|B| + |A| * ρ) := by
            gcongr
        _ = Cedge := rfl
  · intro ε hε
    obtain ⟨C2, hC2, hmid⟩ := exists_bound_iteratedDeriv_cutoff_le hp h1 2 (by norm_num)
    refine ⟨C2 + (18 / ε) ^ 2 + ε * A ^ 2, by positivity, fun u hu0 huρ => ?_⟩
    by_cases hu : u ≤ u₁
    · have h2 := hmid u hu0 hu
      have e : iteratedDeriv 2 p = deriv (deriv p) := by
        rw [iteratedDeriv_succ, iteratedDeriv_one]
      rw [e] at h2
      have h3 := (abs_le.1 h2).2
      have h4 : 0 ≤ ε * deriv p u ^ 2 := by positivity
      have h5 : 0 ≤ (18 / ε) ^ 2 := by positivity
      have h6 : 0 ≤ ε * A ^ 2 := by positivity
      linarith
    · push Not at hu
      have hy := hy1 u hu huρ
      have hf := hform u hu huρ
      have hedge : deriv (deriv p) u = (ρ - u)⁻¹ ^ 4 := by rw [hP2 u hu huρ, inv_pow]
      rw [hedge, hf]
      set y := (ρ - u)⁻¹ with hyd
      have hz : y ^ 4 ≤ ε / 18 * y ^ 6 + (18 / ε) ^ 2 := by
        have hD : 0 < 18 / ε := by positivity
        by_cases hc : y ^ 2 ≤ 18 / ε
        · have h2 : (y ^ 2) ^ 2 ≤ (18 / ε) ^ 2 := pow_le_pow_left₀ (by positivity) hc 2
          have h3 : 0 ≤ ε / 18 * y ^ 6 := by positivity
          have h4 : y ^ 4 = (y ^ 2) ^ 2 := by ring
          linarith
        · push Not at hc
          have h2 : 1 ≤ ε / 18 * y ^ 2 := by
            rw [div_lt_iff₀ hε] at hc
            have : ε / 18 * y ^ 2 = y ^ 2 * ε / 18 := by ring
            rw [this, le_div_iff₀ (by norm_num)]
            linarith
          have h3 : y ^ 4 * 1 ≤ y ^ 4 * (ε / 18 * y ^ 2) := by gcongr
          have h4 : 0 ≤ (18 / ε) ^ 2 := by positivity
          have h5 : y ^ 4 * (ε / 18 * y ^ 2) = ε / 18 * y ^ 6 := by ring
          linarith
      have hq : y ^ 6 / 18 - A ^ 2 ≤ (A + 1 / 3 * y ^ 3) ^ 2 := by
        nlinarith [sq_nonneg (2 * A + 1 / 3 * y ^ 3)]
      have hq2 : ε * (y ^ 6 / 18 - A ^ 2) ≤ ε * (A + 1 / 3 * y ^ 3) ^ 2 :=
        mul_le_mul_of_nonneg_left hq hε.le
      have e1 : ε * (y ^ 6 / 18 - A ^ 2) = ε / 18 * y ^ 6 - ε * A ^ 2 := by ring
      linarith
  · intro j hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    cases i with
    | zero =>
      refine ⟨1, 1, zero_le_one, fun u hu0 huρ => ?_⟩
      have hn := deriv_cutoff_nonneg hp hρ hu0 huρ
      simp only [zero_add, iteratedDeriv_one, pow_one, one_mul]
      rw [abs_of_nonneg hn]
      linarith
    | succ n =>
      obtain ⟨c, hc, hcu⟩ := hit n
      obtain ⟨C2, hC2, hmid⟩ := exists_bound_iteratedDeriv_cutoff_le hp h1 (n + 2) (by omega)
      refine ⟨max C2 (c * (3 * (1 + |A|)) ^ (n + 4)), n + 4, le_max_of_le_left hC2,
        fun u hu0 huρ => ?_⟩
      have hn := deriv_cutoff_nonneg hp hρ hu0 huρ
      have hone : 1 ≤ (1 + deriv p u) ^ (n + 4) := one_le_pow₀ (by linarith)
      by_cases hu : u ≤ u₁
      · have h2 := hmid u hu0 hu
        calc _ ≤ C2 := h2
          _ ≤ max C2 (c * (3 * (1 + |A|)) ^ (n + 4)) := le_max_left _ _
          _ = max C2 (c * (3 * (1 + |A|)) ^ (n + 4)) * 1 := (mul_one _).symm
          _ ≤ _ := by gcongr
      · push Not at hu
        have hy := hy1 u hu huρ
        have hb := hy3 u hu huρ
        have e : iteratedDeriv (n + 1 + 1) p u = c * (ρ - u)⁻¹ ^ (n + 4) := by
          rw [show n + 1 + 1 = n + 2 by ring, hcu u hu huρ, inv_pow]
        rw [e, abs_of_nonneg (by positivity)]
        have h2 : (ρ - u)⁻¹ ^ (n + 4) ≤ (3 * (1 + |A|) * (1 + deriv p u)) ^ (n + 4) :=
          pow_le_pow_left₀ (by linarith) hb _
        calc c * (ρ - u)⁻¹ ^ (n + 4) ≤ c * (3 * (1 + |A|) * (1 + deriv p u)) ^ (n + 4) := by gcongr
          _ = c * (3 * (1 + |A|)) ^ (n + 4) * (1 + deriv p u) ^ (n + 4) := by rw [mul_pow]; ring
          _ ≤ _ := by gcongr; exact le_max_right _ _
  · refine ⟨max (3 * (1 + |A|)) (ρ - u₁)⁻¹, le_max_of_le_left (by positivity), fun u hu0 huρ => ?_⟩
    have hn := deriv_cutoff_nonneg hp hρ hu0 huρ
    have hone : (1 : ℝ) ≤ 1 + deriv p u := by linarith
    by_cases hu : u ≤ u₁
    · have h2 : (ρ - u)⁻¹ ≤ (ρ - u₁)⁻¹ := by
        apply inv_anti₀ (by linarith) (by linarith)
      have h3 : (ρ - u₁)⁻¹ ≤ max (3 * (1 + |A|)) (ρ - u₁)⁻¹ := le_max_right _ _
      have h4 : 0 ≤ max (3 * (1 + |A|)) (ρ - u₁)⁻¹ := le_max_of_le_left (by positivity)
      nlinarith
    · push Not at hu
      refine (hy3 u hu huρ).trans ?_
      have h3 : 3 * (1 + |A|) ≤ max (3 * (1 + |A|)) (ρ - u₁)⁻¹ := le_max_left _ _
      gcongr
end Estimates
end YangMills.Construction
end
