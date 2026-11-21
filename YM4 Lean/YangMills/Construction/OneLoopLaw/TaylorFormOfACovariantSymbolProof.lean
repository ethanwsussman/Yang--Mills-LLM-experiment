import YangMills.Construction.Coordinates.PowerSeriesHolomorphy
import YangMills.Construction.OneLoopLaw.TaylorFormOfACovariantSymbol
import Mathlib
set_option autoImplicit false
open Filter Asymptotics
open scoped Topology ContDiff
noncomputable section
namespace YangMills.Construction.OneLoopLaw.CovariantSymbolTaylor
open YangMills.Construction.PeriodicOperators YangMills.Construction.PeriodicOperators.RiemannSums
open YangMills.Construction.PeriodicOperators.Tempered YangMills.Construction.OneLoopLaw.TemperedStiffness
open YangMills.Construction.Coordinates
open YangMills.Construction.InfiniteLattice (AmbientSpace)
theorem limit_eq_zero_of_isBigO_pow {f : ℝ → ℂ} {a : ℂ} {n : ℕ} (hf : Tendsto f (𝓝[≠] 0) (𝓝 a))
    (h : f =O[𝓝[≠] (0 : ℝ)] fun t => t ^ (n + 1)) : a = 0 := by
  have h0 : Tendsto (fun t : ℝ => t ^ (n + 1)) (𝓝[≠] 0) (𝓝 0) := by
    have : Continuous fun t : ℝ => t ^ (n + 1) := by fun_prop
    have h1 := this.tendsto 0
    simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, zero_pow] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique hf (h.trans_tendsto h0)
theorem isBigO_pow_of_mul_left {g : ℝ → ℂ} {n : ℕ}
    (h : (fun t : ℝ => (t : ℂ) * g t) =O[𝓝[≠] (0 : ℝ)] fun t => t ^ (n + 1)) :
    g =O[𝓝[≠] (0 : ℝ)] fun t => t ^ n := by
  obtain ⟨C, hC⟩ := h.bound
  refine IsBigO.of_bound C ?_
  filter_upwards [hC, self_mem_nhdsWithin] with t ht ht0
  have hpos : 0 < ‖t‖ := norm_pos_iff.2 ht0
  rw [norm_mul, Complex.norm_real, norm_pow, pow_succ] at ht
  rw [norm_pow]
  refine le_of_mul_le_mul_left ?_ hpos
  calc ‖t‖ * ‖g t‖ ≤ C * (‖t‖ ^ n * ‖t‖) := ht
    _ = ‖t‖ * (C * ‖t‖ ^ n) := by ring
theorem isLittleO_pow_of_mul_left {g : ℝ → ℂ} {n : ℕ}
    (h : (fun t : ℝ => (t : ℂ) * g t) =o[𝓝[≠] (0 : ℝ)] fun t => t ^ (n + 1)) :
    g =o[𝓝[≠] (0 : ℝ)] fun t => t ^ n := by
  rw [isLittleO_iff] at h ⊢
  intro C hC0
  filter_upwards [h hC0, self_mem_nhdsWithin] with t ht ht0
  have hpos : 0 < ‖t‖ := norm_pos_iff.2 ht0
  rw [norm_mul, Complex.norm_real, norm_pow, pow_succ] at ht
  rw [norm_pow]
  refine le_of_mul_le_mul_left ?_ hpos
  calc ‖t‖ * ‖g t‖ ≤ C * (‖t‖ ^ n * ‖t‖) := ht
    _ = ‖t‖ * (C * ‖t‖ ^ n) := by ring
theorem cubic_coeffs_eq_zero_of_isBigO {a₀ a₁ a₂ a₃ : ℂ}
    (h : (fun t : ℝ => a₀ + (t : ℂ) * a₁ + (t : ℂ) ^ 2 * a₂ + (t : ℂ) ^ 3 * a₃) =O[𝓝 0]
      fun t => t ^ 4) : a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0 ∧ a₃ = 0 := by
  have h' := h.mono (nhdsWithin_le_nhds (s := {0}ᶜ))
  have lim : ∀ (b₀ b₁ b₂ b₃ : ℂ), Tendsto
      (fun t : ℝ => b₀ + (t : ℂ) * b₁ + (t : ℂ) ^ 2 * b₂ + (t : ℂ) ^ 3 * b₃) (𝓝[≠] 0) (𝓝 b₀) := by
    intro b₀ b₁ b₂ b₃
    have : Continuous fun t : ℝ => b₀ + (t : ℂ) * b₁ + (t : ℂ) ^ 2 * b₂ + (t : ℂ) ^ 3 * b₃ := by
      fun_prop
    have h1 := this.tendsto 0
    simp only [Complex.ofReal_zero, zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  have e₀ : a₀ = 0 := limit_eq_zero_of_isBigO_pow (lim a₀ a₁ a₂ a₃) h'
  subst e₀
  have h₁ : (fun t : ℝ => a₁ + (t : ℂ) * a₂ + (t : ℂ) ^ 2 * a₃ + (t : ℂ) ^ 3 * 0) =O[𝓝[≠] (0 : ℝ)]
      fun t => t ^ 3 := by
    refine isBigO_pow_of_mul_left (h'.congr_left fun t => ?_)
    ring
  have e₁ : a₁ = 0 := limit_eq_zero_of_isBigO_pow (lim a₁ a₂ a₃ 0) h₁
  subst e₁
  have h₂ : (fun t : ℝ => a₂ + (t : ℂ) * a₃ + (t : ℂ) ^ 2 * 0 + (t : ℂ) ^ 3 * 0) =O[𝓝[≠] (0 : ℝ)]
      fun t => t ^ 2 := by
    refine isBigO_pow_of_mul_left (h₁.congr_left fun t => ?_)
    ring
  have e₂ : a₂ = 0 := limit_eq_zero_of_isBigO_pow (lim a₂ a₃ 0 0) h₂
  subst e₂
  have h₃ : (fun t : ℝ => a₃ + (t : ℂ) * 0 + (t : ℂ) ^ 2 * 0 + (t : ℂ) ^ 3 * 0) =O[𝓝[≠] (0 : ℝ)]
      fun t => t ^ 1 := by
    refine isBigO_pow_of_mul_left (h₂.congr_left fun t => ?_)
    ring
  exact ⟨rfl, rfl, rfl, limit_eq_zero_of_isBigO_pow (n := 0) (lim a₃ 0 0 0) h₃⟩
theorem deriv_deriv_zero_of_quadratic_approx {h : ℝ → ℂ} {a : ℂ} (hh : ContDiffAt ℝ 2 h 0)
    (ho : (fun t : ℝ => h t - (t : ℂ) ^ 2 * a) =o[𝓝 0] fun t => t ^ 2) :
    deriv (deriv h) 0 = 2 * a := by
  obtain ⟨u, hu, hc⟩ := hh.contDiffOn (m := 2) le_rfl (by simp)
  obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.1 hu
  have hc' : ContDiffOn ℝ ((2 : ℕ) : WithTop ℕ∞) h (Metric.ball 0 ε) := by
    simpa using hc.mono hb
  have ht := taylor_isLittleO (convex_ball (0 : ℝ) ε) (Metric.mem_ball_self hε) hc'
  rw [Metric.isOpen_ball.nhdsWithin_eq (Metric.mem_ball_self hε)] at ht
  have hd : ∀ k, iteratedDerivWithin k h (Metric.ball 0 ε) 0 = iteratedDeriv k h 0 := fun k =>
    iteratedDerivWithin_of_isOpen Metric.isOpen_ball (Metric.mem_ball_self hε)
  set c₁ : ℂ := deriv h 0
  set c₂ : ℂ := deriv (deriv h) 0
  have h2 : iteratedDeriv 2 h 0 = c₂ := by simp [iteratedDeriv_succ, c₂]
  have h1 : iteratedDeriv 1 h 0 = c₁ := by simp [c₁]
  have key : (fun t : ℝ => h 0 + (t : ℂ) * c₁ + (t : ℂ) ^ 2 * (c₂ / 2 - a)) =o[𝓝 0]
      fun t => t ^ 2 := by
    refine (ho.sub (by simpa using ht)).congr_left fun t => ?_
    have hw : derivWithin h (Metric.ball 0 ε) 0 = c₁ :=
      derivWithin_of_isOpen Metric.isOpen_ball (Metric.mem_ball_self hε)
    simp [taylor_within_apply, Finset.sum_range_succ, hd, h2, h1, hw, Nat.factorial]
    ring
  have hcancelled' := key.mono (nhdsWithin_le_nhds (s := {0}ᶜ))
  have lim : ∀ (b₀ b₁ b₂ : ℂ), Tendsto
      (fun t : ℝ => b₀ + (t : ℂ) * b₁ + (t : ℂ) ^ 2 * b₂) (𝓝[≠] 0) (𝓝 b₀) := by
    intro b₀ b₁ b₂
    have : Continuous fun t : ℝ => b₀ + (t : ℂ) * b₁ + (t : ℂ) ^ 2 * b₂ := by fun_prop
    have h1 := this.tendsto 0
    simp only [Complex.ofReal_zero, zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  have e₀ : h 0 = 0 := limit_eq_zero_of_isBigO_pow (n := 1) (lim _ _ _) hcancelled'.isBigO
  rw [e₀] at hcancelled'
  have k₁ : (fun t : ℝ => c₁ + (t : ℂ) * (c₂ / 2 - a) + (t : ℂ) ^ 2 * 0) =o[𝓝[≠] (0 : ℝ)]
      fun t => t ^ 1 := by
    refine isLittleO_pow_of_mul_left (hcancelled'.congr_left fun t => ?_)
    ring
  have e₁ : c₁ = 0 := limit_eq_zero_of_isBigO_pow (n := 0) (lim _ _ _) k₁.isBigO
  rw [e₁] at k₁
  have k₂ : (fun t : ℝ => c₂ / 2 - a) =o[𝓝[≠] (0 : ℝ)] fun t => t ^ 0 := by
    refine isLittleO_pow_of_mul_left (k₁.congr_left fun t => ?_)
    ring
  have k₃ : Tendsto (fun _ : ℝ => c₂ / 2 - a) (𝓝[≠] 0) (𝓝 0) :=
     (isLittleO_one_iff ℝ).1 (by simpa only [pow_zero] using k₂)
  have e₂ : c₂ / 2 - a = 0 := tendsto_nhds_unique tendsto_const_nhds k₃
  linear_combination 2 * e₂
abbrev IsBigOPowAtZero (f : AmbientSpace → ℂ) (k : ℕ) : Prop :=
  f =O[𝓝 (0 : AmbientSpace)] fun p : AmbientSpace => ‖p‖ ^ k
def IsQuadraticForm (Q : AmbientSpace → ℂ) : Prop :=
  ∃ a : Fin 4 → Fin 4 → ℂ, ∀ v : AmbientSpace, Q v = ∑ ρ, ∑ τ, a ρ τ * (v ρ : ℂ) * (v τ : ℂ)
structure CubicJet (f : AmbientSpace → ℂ) (c : ℂ) (L Q R : AmbientSpace → ℂ) : Prop where
  smul_lin : ∀ (t : ℝ) (v : AmbientSpace), L (t • v) = (t : ℂ) * L v
  smul_quad : ∀ (t : ℝ) (v : AmbientSpace), Q (t • v) = (t : ℂ) ^ 2 * Q v
  smul_cubic : ∀ (t : ℝ) (v : AmbientSpace), R (t • v) = (t : ℂ) ^ 3 * R v
  lin_bound : IsBigOPowAtZero L 1
  quad_bound : IsBigOPowAtZero Q 2
  cubic_bound : IsBigOPowAtZero R 3
  quad_form : IsQuadraticForm Q
  remainder : IsBigOPowAtZero (fun v => f v - (c + L v + Q v + R v)) 4
theorem isBigOPowAtZero_mono {f : AmbientSpace → ℂ} {k n : ℕ} (h : IsBigOPowAtZero f n)
    (hk : k ≤ n) : IsBigOPowAtZero f k := by
  refine h.trans (IsBigO.of_bound 1 ?_)
  have : ∀ᶠ p : AmbientSpace in 𝓝 0, ‖p‖ ≤ 1 := by
    filter_upwards [Metric.closedBall_mem_nhds (0 : AmbientSpace) one_pos] with p hp
    simpa using hp
  filter_upwards [this] with p hp
  simp only [norm_pow, norm_norm, one_mul]
  exact pow_le_pow_of_le_one (norm_nonneg p) hp hk
theorem isBigOPowAtZero_mul {f g : AmbientSpace → ℂ} {k n : ℕ} (hf : IsBigOPowAtZero f k)
    (hg : IsBigOPowAtZero g n) : IsBigOPowAtZero (fun p => f p * g p) (k + n) := by
  have := hf.mul hg
  simpa only [IsBigOPowAtZero, pow_add] using this
theorem homogeneous_parts_eq_zero {c : ℂ} {L Q R : AmbientSpace → ℂ}
    (hL : ∀ (t : ℝ) (v : AmbientSpace), L (t • v) = (t : ℂ) * L v)
    (hQ : ∀ (t : ℝ) (v : AmbientSpace), Q (t • v) = (t : ℂ) ^ 2 * Q v)
    (hR : ∀ (t : ℝ) (v : AmbientSpace), R (t • v) = (t : ℂ) ^ 3 * R v)
    (h : IsBigOPowAtZero (fun v => c + L v + Q v + R v) 4) :
    c = 0 ∧ (∀ v, L v = 0) ∧ (∀ v, Q v = 0) ∧ ∀ v, R v = 0 := by
  have key : ∀ v : AmbientSpace, c = 0 ∧ L v = 0 ∧ Q v = 0 ∧ R v = 0 := by
    intro v
    have ht : Tendsto (fun t : ℝ => t • v) (𝓝 0) (𝓝 (0 : AmbientSpace)) := by
      have : Continuous fun t : ℝ => t • v := by fun_prop
      simpa using this.tendsto 0
    have h1 := h.comp_tendsto ht
    have h2 : (fun t : ℝ => c + (t : ℂ) * L v + (t : ℂ) ^ 2 * Q v + (t : ℂ) ^ 3 * R v) =O[𝓝 0]
        fun t => t ^ 4 := by
      refine IsBigO.trans (f := fun t : ℝ => c + (t : ℂ) * L v + (t : ℂ) ^ 2 * Q v + (t : ℂ) ^ 3 * R v)
        (h1.congr_left fun t => ?_) (IsBigO.of_bound (‖v‖ ^ 4) (Eventually.of_forall fun t => ?_))
      · simp only [Function.comp, hL, hQ, hR]
      · simp only [Function.comp]
        rw [norm_pow, norm_norm, norm_smul, mul_pow, norm_pow]
        exact le_of_eq (by ring)
    exact cubic_coeffs_eq_zero_of_isBigO h2
  exact ⟨(key 0).1, fun v => (key v).2.1, fun v => (key v).2.2.1, fun v => (key v).2.2.2⟩
theorem norm_monomial_le (p : AmbientSpace) (m : Fin 4 → ℕ) :
    ‖∏ j, (p j : ℂ) ^ m j‖ ≤ ‖p‖ ^ (∑ j, m j) := by
  rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun j _ => ?_
  rw [norm_pow, Complex.norm_real]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm p j) _
def homogeneousPart (c : (Fin 4 → ℕ) → ℂ) (k : ℕ) (p : AmbientSpace) : ℂ :=
  ∑ m ∈ Finset.piAntidiag Finset.univ k, (∏ j, (p j : ℂ) ^ m j) * c m
theorem homogeneousPart_smul (c : (Fin 4 → ℕ) → ℂ) (k : ℕ) (t : ℝ) (p : AmbientSpace) :
    homogeneousPart c k (t • p) = (t : ℂ) ^ k * homogeneousPart c k p := by
  rw [homogeneousPart, homogeneousPart, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hs : ∑ j, m j = k := (Finset.mem_piAntidiag.1 hm).1
  have : ∏ j, (((t • p) j : ℝ) : ℂ) ^ m j = (t : ℂ) ^ k * ∏ j, (p j : ℂ) ^ m j := by
    simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, mul_pow, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, hs]
  rw [this]
  ring
theorem homogeneousPart_isBigOPowAtZero (c : (Fin 4 → ℕ) → ℂ) (k : ℕ) :
    IsBigOPowAtZero (homogeneousPart c k) k := by
  show (fun p : AmbientSpace => ∑ m ∈ Finset.piAntidiag Finset.univ k, (∏ j, (p j : ℂ) ^ m j) * c m)
    =O[𝓝 (0 : AmbientSpace)] fun p : AmbientSpace => ‖p‖ ^ k
  refine ?_
  have hsum := IsBigO.sum (s := Finset.piAntidiag Finset.univ k)
    (A := fun (m : Fin 4 → ℕ) (p : AmbientSpace) => (∏ j, (p j : ℂ) ^ m j) * c m)
    (g := fun p : AmbientSpace => ‖p‖ ^ k) (l := 𝓝 (0 : AmbientSpace)) ?_
  · simpa only [Finset.sum_fn] using hsum
  intro m hm
  have hs : ∑ j, m j = k := (Finset.mem_piAntidiag.1 hm).1
  refine IsBigO.of_bound ‖c m‖ (Eventually.of_forall fun p => ?_)
  rw [norm_mul, norm_pow, norm_norm, mul_comm]
  have := norm_monomial_le p m
  rw [hs] at this
  exact mul_le_mul_of_nonneg_left this (norm_nonneg _)
theorem eq_single_add_single_of_sum_eq_two (m : Fin 4 → ℕ) (hm : ∑ j, m j = 2) :
    ∃ ρ τ : Fin 4, m = Pi.single ρ 1 + Pi.single τ 1 := by
  have pick : ∀ (n : Fin 4 → ℕ) (k : ℕ), ∑ j, n j = k + 1 →
      ∃ ρ : Fin 4, ∑ j, (n - Pi.single ρ 1 : Fin 4 → ℕ) j = k ∧
        n = (n - Pi.single ρ 1 : Fin 4 → ℕ) + Pi.single ρ 1 := by
    intro n k hn
    obtain ⟨ρ, hρ⟩ : ∃ ρ, n ρ ≠ 0 := by
      by_contra hc
      push_neg at hc
      simp [hc] at hn
    refine ⟨ρ, ?_, ?_⟩
    · have : ∑ j, ((n - Pi.single ρ 1 : Fin 4 → ℕ) j + (Pi.single ρ 1 : Fin 4 → ℕ) j) = k + 1 := by
        rw [← hn]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : j = ρ
        · subst hj
          simp only [Pi.sub_apply, Pi.single_eq_same]
          omega
        · simp [Pi.single_eq_of_ne hj]
      rw [Finset.sum_add_distrib, Finset.sum_pi_single'] at this
      simpa using this
    · ext j
      by_cases hj : j = ρ
      · subst hj
        simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same]
        omega
      · simp [Pi.single_eq_of_ne hj]
  obtain ⟨ρ, h1, e1⟩ := pick m 1 hm
  obtain ⟨τ, h2, e2⟩ := pick _ 0 h1
  have z : (m - Pi.single ρ 1 - Pi.single τ 1 : Fin 4 → ℕ) = 0 := by
    ext j
    have := (Finset.sum_eq_zero_iff.1 h2) j (Finset.mem_univ j)
    simpa using this
  refine ⟨τ, ρ, ?_⟩
  rw [z, zero_add] at e2
  rw [e2] at e1
  exact e1
theorem isQuadraticForm_sum {ι : Type*} (s : Finset ι) (g : ι → AmbientSpace → ℂ)
    (h : ∀ i ∈ s, IsQuadraticForm (g i)) : IsQuadraticForm fun v => ∑ i ∈ s, g i v := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun v => by simp⟩
  | insert i s hi ih =>
    obtain ⟨a, ha⟩ := h i (Finset.mem_insert_self i s)
    obtain ⟨b, hb⟩ := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    refine ⟨a + b, fun v => ?_⟩
    have hb' : ∑ i ∈ s, g i v = ∑ ρ, ∑ τ, b ρ τ * (v ρ : ℂ) * (v τ : ℂ) := hb v
    beta_reduce
    rw [Finset.sum_insert hi, ha, hb', ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [Pi.add_apply]
    ring
theorem homogeneousPart_two_isQuadraticForm (c : (Fin 4 → ℕ) → ℂ) :
    IsQuadraticForm (homogeneousPart c 2) := by
  classical
  refine isQuadraticForm_sum _ _ fun m hm => ?_
  obtain ⟨ρ, τ, rfl⟩ := eq_single_add_single_of_sum_eq_two m (Finset.mem_piAntidiag.1 hm).1
  refine ⟨fun x y => if x = ρ ∧ y = τ then c (Pi.single ρ 1 + Pi.single τ 1) else 0, fun v => ?_⟩
  have : ∏ j, (v j : ℂ) ^ ((Pi.single ρ 1 + Pi.single τ 1 : Fin 4 → ℕ) j) =
      (v ρ : ℂ) * (v τ : ℂ) := by
    simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    congr 1
    · rw [Finset.prod_eq_single ρ] <;> simp +contextual [Pi.single_apply]
    · rw [Finset.prod_eq_single τ] <;> simp +contextual [Pi.single_apply]
  beta_reduce
  rw [this]
  rw [Finset.sum_eq_single ρ (fun x _ hx => by simp [hx]) (by simp),
    Finset.sum_eq_single τ (fun y _ hy => by simp [hy]) (by simp)]
  simp only [and_self, if_true]
  ring
theorem exists_cubicJet_of_hasSum {f : AmbientSpace → ℂ} {c : (Fin 4 → ℕ) → ℂ} {r : ℝ} (hr : 0 < r)
    (hs : ∀ p : AmbientSpace, ‖p‖ ≤ r →
      HasSum (fun m : Fin 4 → ℕ => (∏ j, (p j : ℂ) ^ m j) * c m) (f p))
    (hb : Summable fun m : Fin 4 → ℕ => r ^ (∑ j, m j) * ‖c m‖) :
    ∃ c₀ L Q R, CubicJet f c₀ L Q R := by
  classical
  have h0 : ∀ p, homogeneousPart c 0 p = homogeneousPart c 0 0 := by
    intro p
    have := homogeneousPart_smul c 0 0 p
    simpa using this.symm
  refine ⟨homogeneousPart c 0 0, homogeneousPart c 1, homogeneousPart c 2, homogeneousPart c 3,
    ?_⟩
  refine ⟨fun t v => by simpa using homogeneousPart_smul c 1 t v, homogeneousPart_smul c 2,
    homogeneousPart_smul c 3, homogeneousPart_isBigOPowAtZero c 1,
    homogeneousPart_isBigOPowAtZero c 2, homogeneousPart_isBigOPowAtZero c 3,
    homogeneousPart_two_isQuadraticForm c, ?_⟩
  set A : Finset (Fin 4 → ℕ) := (Finset.range 4).biUnion fun k => Finset.piAntidiag Finset.univ k
    with hA
  have hsum : ∀ p : AmbientSpace, ∑ m ∈ A, (∏ j, (p j : ℂ) ^ m j) * c m =
      homogeneousPart c 0 0 + homogeneousPart c 1 p + homogeneousPart c 2 p +
        homogeneousPart c 3 p := by
    intro p
    rw [← h0 p, hA, Finset.sum_biUnion]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, homogeneousPart]
    · intro k _ l _ hkl
      refine Finset.disjoint_left.2 fun m hk hl => hkl ?_
      rw [← (Finset.mem_piAntidiag.1 hk).1, (Finset.mem_piAntidiag.1 hl).1]
  have hnot : ∀ m, m ∉ A → 4 ≤ ∑ j, m j := by
    intro m hm
    by_contra hc
    refine hm (Finset.mem_biUnion.2 ⟨∑ j, m j, Finset.mem_range.2 (by omega), ?_⟩)
    simp
  refine IsBigO.of_bound ((∑' m : Fin 4 → ℕ, r ^ (∑ j, m j) * ‖c m‖) / r ^ 4) ?_
  have hball : ∀ᶠ p : AmbientSpace in 𝓝 0, ‖p‖ ≤ r := by
    filter_upwards [Metric.closedBall_mem_nhds (0 : AmbientSpace) hr] with p hp
    simpa using hp
  filter_upwards [hball] with p hp
  have h1 : HasSum (fun m : Fin 4 → ℕ => if m ∈ A then 0 else (∏ j, (p j : ℂ) ^ m j) * c m)
      (f p - ∑ m ∈ A, (∏ j, (p j : ℂ) ^ m j) * c m) := by
    have h2 : HasSum (fun m : Fin 4 → ℕ => if m ∈ A then (∏ j, (p j : ℂ) ^ m j) * c m else 0)
        (∑ m ∈ A, (∏ j, (p j : ℂ) ^ m j) * c m) := by
      have := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional _) (s := A)
        (f := fun m : Fin 4 → ℕ => if m ∈ A then (∏ j, (p j : ℂ) ^ m j) * c m else 0)
        (fun m hm => if_neg hm)
      rwa [Finset.sum_congr rfl (fun m hm => if_pos hm)] at this
    have e : (fun m : Fin 4 → ℕ => if m ∈ A then 0 else (∏ j, (p j : ℂ) ^ m j) * c m) =
        fun m => (∏ j, (p j : ℂ) ^ m j) * c m -
          if m ∈ A then (∏ j, (p j : ℂ) ^ m j) * c m else 0 := by
      funext m
      by_cases hm : m ∈ A <;> simp [hm]
    rw [e]
    exact (hs p hp).sub h2
  have h3 := hb.hasSum.mul_left ((‖p‖ / r) ^ 4)
  have h4 := h1.norm_le_of_bounded h3 ?_
  · rw [hsum p] at h4
    simp only [norm_pow, norm_norm]
    calc _ ≤ _ := h4
      _ = _ := by field_simp
  · intro m
    by_cases hm : m ∈ A
    · simp only [hm, if_true, norm_zero]
      positivity
    · simp only [hm, if_false]
      have h5 := hnot m hm
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h5
      have h6 := norm_monomial_le p m
      rw [norm_mul]
      have h7 : ‖p‖ ^ (∑ j, m j) ≤ (‖p‖ / r) ^ 4 * r ^ (∑ j, m j) := by
        rw [hd, pow_add, pow_add, div_pow]
        have : ‖p‖ ^ d ≤ r ^ d := pow_le_pow_left₀ (norm_nonneg _) hp d
        have hr4 : r ^ 4 ≠ 0 := by positivity
        calc ‖p‖ ^ 4 * ‖p‖ ^ d ≤ ‖p‖ ^ 4 * r ^ d := by gcongr
          _ = _ := by field_simp
      calc _ ≤ ‖p‖ ^ (∑ j, m j) * ‖c m‖ := by gcongr
        _ ≤ ((‖p‖ / r) ^ 4 * r ^ (∑ j, m j)) * ‖c m‖ := by gcongr
        _ = _ := by ring
theorem CubicJet.comp_of_eq_smul {f f' : AmbientSpace → ℂ} {c c' : ℂ}
    {L Q R L' Q' R' : AmbientSpace → ℂ}
    (J : CubicJet f c L Q R) (J' : CubicJet f' c' L' Q' R') (A : AmbientSpace → AmbientSpace)
    (hA : ∀ v, ‖A v‖ ≤ ‖v‖) (hh : ∀ (t : ℝ) (v : AmbientSpace), A (t • v) = t • A v) (ε : ℂ)
    (hf : ∀ v, f' (A v) = ε * f v) :
    c' = ε * c ∧ (∀ v, L' (A v) = ε * L v) ∧ (∀ v, Q' (A v) = ε * Q v) ∧
      ∀ v, R' (A v) = ε * R v := by
  have hAt : Tendsto A (𝓝 0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) hA ?_
    exact tendsto_zero_iff_norm_tendsto_zero.1 tendsto_id
  have e₁ : IsBigOPowAtZero (fun v => f' (A v) - (c' + L' (A v) + Q' (A v) + R' (A v))) 4 := by
    refine (J'.remainder.comp_tendsto hAt).trans
      (IsBigO.of_bound 1 (Eventually.of_forall fun v => ?_))
    simp only [Function.comp, norm_pow, norm_norm, one_mul]
    exact pow_le_pow_left₀ (norm_nonneg _) (hA v) 4
  have e₂ : IsBigOPowAtZero (fun v => ε * (f v - (c + L v + Q v + R v))) 4 :=
    J.remainder.const_mul_left ε
  have e₃ := homogeneous_parts_eq_zero (c := c' - ε * c) (L := fun v => L' (A v) - ε * L v)
    (Q := fun v => Q' (A v) - ε * Q v) (R := fun v => R' (A v) - ε * R v)
    (fun t v => by simp only [hh, J.smul_lin, J'.smul_lin]; ring)
    (fun t v => by simp only [hh, J.smul_quad, J'.smul_quad]; ring)
    (fun t v => by simp only [hh, J.smul_cubic, J'.smul_cubic]; ring)
    ((e₂.sub e₁).congr_left fun v => by rw [hf]; ring)
  refine ⟨sub_eq_zero.1 e₃.1, fun v => sub_eq_zero.1 (e₃.2.1 v),
    fun v => sub_eq_zero.1 (e₃.2.2.1 v), fun v => sub_eq_zero.1 (e₃.2.2.2 v)⟩
def basisVec (ρ : Fin 4) : AmbientSpace := Pi.single ρ 1
def quadCoeff (Q : AmbientSpace → ℂ) (ρ τ : Fin 4) : ℂ :=
  (Q (basisVec ρ + basisVec τ) - Q (basisVec ρ - basisVec τ)) / 2
theorem sum_sum_basisVec (b : Fin 4 → Fin 4 → ℂ) (ρ τ : Fin 4) :
    ∑ x, ∑ y, b x y * (basisVec ρ x : ℂ) * (basisVec τ y : ℂ) = b ρ τ := by
  rw [Finset.sum_eq_single ρ (fun x _ hx => by simp [basisVec, Pi.single_eq_of_ne hx]) (by simp),
    Finset.sum_eq_single τ (fun y _ hy => by simp [basisVec, Pi.single_eq_of_ne hy]) (by simp)]
  simp [basisVec]
theorem eq_half_sum_quadCoeff {Q : AmbientSpace → ℂ} (hQ : IsQuadraticForm Q) (v : AmbientSpace) :
    Q v = (1 / 2) * ∑ ρ, ∑ τ, quadCoeff Q ρ τ * (v ρ : ℂ) * (v τ : ℂ) := by
  obtain ⟨a, ha⟩ := hQ
  have hc : ∀ ρ τ, quadCoeff Q ρ τ = a ρ τ + a τ ρ := by
    intro ρ τ
    have e : ∀ (u w : AmbientSpace) (x y : Fin 4),
        a x y * ((u + w) x : ℂ) * ((u + w) y : ℂ) - a x y * ((u - w) x : ℂ) * ((u - w) y : ℂ) =
          2 * (a x y * (u x : ℂ) * (w y : ℂ)) + 2 * (a x y * (w x : ℂ) * (u y : ℂ)) := by
      intro u w x y
      simp only [Pi.add_apply, Pi.sub_apply]
      push_cast
      ring
    have h1 : Q (basisVec ρ + basisVec τ) - Q (basisVec ρ - basisVec τ) =
        2 * (a ρ τ + a τ ρ) := by
      rw [ha, ha, ← Finset.sum_sub_distrib]
      simp only [← Finset.sum_sub_distrib, e, Finset.sum_add_distrib, ← Finset.mul_sum,
        sum_sum_basisVec]
      ring
    rw [quadCoeff, h1]
    ring
  have s2 : ∑ ρ, ∑ τ, a τ ρ * (v ρ : ℂ) * (v τ : ℂ) =
      ∑ ρ, ∑ τ, a ρ τ * (v ρ : ℂ) * (v τ : ℂ) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  simp only [hc, add_mul, Finset.sum_add_distrib]
  rw [s2, ha]
  ring
def reflectAxis (σ : Fin 4) (v : AmbientSpace) : AmbientSpace :=
  fun x => (if x = σ then -1 else 1) * v x
theorem norm_reflectAxis_le (σ : Fin 4) (v : AmbientSpace) : ‖reflectAxis σ v‖ ≤ ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2 fun x => ?_
  have := norm_le_pi_norm v x
  by_cases hx : x = σ <;> simpa [reflectAxis, hx] using this
theorem reflectAxis_smul (σ : Fin 4) (t : ℝ) (v : AmbientSpace) :
    reflectAxis σ (t • v) = t • reflectAxis σ v := by
  ext x
  simp only [reflectAxis, Pi.smul_apply, smul_eq_mul]
  ring
theorem reflectAxis_add (σ : Fin 4) (u w : AmbientSpace) :
    reflectAxis σ (u + w) = reflectAxis σ u + reflectAxis σ w := by
  ext x
  simp only [reflectAxis, Pi.add_apply]
  ring
theorem reflectAxis_sub (σ : Fin 4) (u w : AmbientSpace) :
    reflectAxis σ (u - w) = reflectAxis σ u - reflectAxis σ w := by
  ext x
  simp only [reflectAxis, Pi.sub_apply]
  ring
theorem reflectAxis_basisVec_self (σ : Fin 4) : reflectAxis σ (basisVec σ) = -basisVec σ := by
  ext x
  by_cases hx : x = σ
  · subst hx
    simp [reflectAxis, basisVec]
  · simp [reflectAxis, basisVec, hx, Pi.single_eq_of_ne hx]
theorem reflectAxis_basisVec_of_ne {σ ρ : Fin 4} (h : ρ ≠ σ) :
    reflectAxis σ (basisVec ρ) = basisVec ρ := by
  ext x
  by_cases hx : x = σ
  · have : x ≠ ρ := fun e => h (e ▸ hx)
    simp [reflectAxis, basisVec, Pi.single_eq_of_ne this]
  · simp [reflectAxis, hx]
def axisSign (ρ μ : Fin 4) : ℤ := if μ = ρ then -1 else 1
theorem reflectSign_eq_axisSign (ρ μ : Fin 4) : reflectSign ρ μ = (axisSign ρ μ : ℂ) := by
  unfold reflectSign axisSign
  split_ifs <;> simp
theorem axisSign_mul_quadCoeff {Q : AmbientSpace → ℂ} (heven : ∀ v, Q (-v) = Q v) (σ : Fin 4)
    (s : ℂ) (h : ∀ v, Q (reflectAxis σ v) = s * Q v) (ρ τ : Fin 4) :
    (axisSign σ ρ : ℂ) * (axisSign σ τ : ℂ) * quadCoeff Q ρ τ = s * quadCoeff Q ρ τ := by
  have e : s * quadCoeff Q ρ τ =
      (Q (reflectAxis σ (basisVec ρ + basisVec τ)) -
        Q (reflectAxis σ (basisVec ρ - basisVec τ))) / 2 := by
    rw [h, h, quadCoeff]
    ring
  rw [e, reflectAxis_add, reflectAxis_sub]
  by_cases hρ : ρ = σ <;> by_cases hτ : τ = σ
  · subst hρ
    subst hτ
    have a1 : -basisVec τ + -basisVec τ = -(basisVec τ + basisVec τ) := by abel
    have a2 : -basisVec τ - -basisVec τ = basisVec τ - basisVec τ := by abel
    rw [reflectAxis_basisVec_self, quadCoeff, a1, a2, heven]
    simp only [axisSign, if_true]
    push_cast
    ring
  · subst hρ
    rw [reflectAxis_basisVec_self, reflectAxis_basisVec_of_ne hτ, quadCoeff]
    have a1 : -basisVec ρ + basisVec τ = -(basisVec ρ - basisVec τ) := by abel
    have a2 : -basisVec ρ - basisVec τ = -(basisVec ρ + basisVec τ) := by abel
    rw [a1, a2, heven, heven]
    simp only [axisSign, if_true, if_neg hτ]
    push_cast
    ring
  · subst hτ
    rw [reflectAxis_basisVec_self, reflectAxis_basisVec_of_ne hρ, quadCoeff]
    simp only [sub_neg_eq_add, ← sub_eq_add_neg]
    simp only [axisSign, if_true, if_neg hρ]
    push_cast
    ring
  · rw [reflectAxis_basisVec_of_ne hρ, reflectAxis_basisVec_of_ne hτ, quadCoeff]
    simp only [axisSign, if_neg hρ, if_neg hτ]
    push_cast
    ring
theorem index_pairs_of_axisSign_eq : ∀ μ ν ρ τ : Fin 4,
    (∀ σ, axisSign σ ρ * axisSign σ τ = axisSign σ μ * axisSign σ ν) →
      (ρ = μ ∧ τ = ν) ∨ (ρ = ν ∧ τ = μ) ∨ (ρ = τ ∧ μ = ν) := by
  unfold axisSign
  decide
theorem basisVec_comp_symm (σ : Equiv.Perm (Fin 4)) (ρ : Fin 4) :
    basisVec ρ ∘ σ.symm = basisVec (σ ρ) := by
  ext x
  simp only [basisVec, Function.comp, Pi.single_apply, Equiv.symm_apply_eq]
theorem exists_perm_to_zero_one {μ ν : Fin 4} (h : μ ≠ ν) :
    ∃ σ : Equiv.Perm (Fin 4), σ μ = 0 ∧ σ ν = 1 := by
  revert μ ν
  decide
def kron (x y : Fin 4) : ℂ := if x = y then 1 else 0
theorem tensor_eq_transverse (T : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ)
    (hsym : ∀ μ ν ρ τ, T μ ν ρ τ = T μ ν τ ρ)
    (hvan : ∀ μ ν ρ τ, T μ ν ρ τ ≠ 0 → (ρ = μ ∧ τ = ν) ∨ (ρ = ν ∧ τ = μ) ∨ (ρ = τ ∧ μ = ν))
    (hperm : ∀ (σ : Equiv.Perm (Fin 4)) μ ν ρ τ, T (σ μ) (σ ν) (σ ρ) (σ τ) = T μ ν ρ τ)
    (hG : ∀ (ν : Fin 4) (p : AmbientSpace),
      ∑ μ, (p μ : ℂ) * ∑ ρ, ∑ τ, T μ ν ρ τ * (p ρ : ℂ) * (p τ : ℂ) = 0) :
    ∃ b : ℂ, ∀ μ ν ρ τ, T μ ν ρ τ =
      2 * b * kron ρ τ * kron μ ν - b * (kron ρ μ * kron τ ν + kron ρ ν * kron τ μ) := by
  have zero : ∀ μ ν ρ τ, ¬((ρ = μ ∧ τ = ν) ∨ (ρ = ν ∧ τ = μ) ∨ (ρ = τ ∧ μ = ν)) →
      T μ ν ρ τ = 0 :=
    fun μ ν ρ τ h => by
      by_contra hc
      exact h (hvan μ ν ρ τ hc)
  have hD : T 0 0 0 0 = 0 := by
    have := hG 0 ![1, 0, 0, 0]
    simpa [Fin.sum_univ_four] using this
  have hAB : T 0 0 1 1 + 2 * T 1 0 1 0 = 0 := by
    have := hG 0 ![1, 1, 0, 0]
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, add_zero, zero_mul, one_mul]
      at this
    have z1 : T 0 0 0 1 = 0 := zero _ _ _ _ (by decide)
    have z2 : T 0 0 1 0 = 0 := zero _ _ _ _ (by decide)
    have z3 : T 1 0 0 0 = 0 := zero _ _ _ _ (by decide)
    have z4 : T 1 0 1 1 = 0 := zero _ _ _ _ (by decide)
    rw [hsym 1 0 0 1, hD, z1, z2, z3, z4] at this
    linear_combination this
  have hDm : ∀ μ, T μ μ μ μ = 0 := by
    intro μ
    rw [← hperm (Equiv.swap μ 0) μ μ μ μ]
    simpa using hD
  have hA : ∀ μ ρ, μ ≠ ρ → T μ μ ρ ρ = T 0 0 1 1 := by
    intro μ ρ h
    obtain ⟨σ, h0, h1⟩ := exists_perm_to_zero_one h
    rw [← hperm σ, h0, h1]
  have hB : ∀ μ ν, μ ≠ ν → T μ ν μ ν = T 1 0 1 0 := by
    intro μ ν h
    obtain ⟨σ, h0, h1⟩ := exists_perm_to_zero_one h
    obtain ⟨σ', h0', h1'⟩ := exists_perm_to_zero_one (show (1 : Fin 4) ≠ 0 by decide)
    rw [← hperm σ, h0, h1, ← hperm σ' 1 0 1 0, h0', h1']
  refine ⟨T 0 0 1 1 / 2, fun μ ν ρ τ => ?_⟩
  have hBb : T 1 0 1 0 = -(T 0 0 1 1 / 2) := by linear_combination (1 / 2 : ℂ) * hAB
  by_cases hμν : μ = ν
  · subst hμν
    by_cases hρτ : ρ = τ
    · subst hρτ
      by_cases hρμ : ρ = μ
      · subst hρμ
        rw [hDm]
        simp only [kron, if_true]
        ring
      · rw [hA μ ρ (Ne.symm hρμ)]
        simp only [kron, if_true, if_neg hρμ]
        ring
    · have hz := zero μ μ ρ τ (by
        rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨h, _⟩)
        · exact hρτ rfl
        · exact hρτ rfl
        · exact hρτ h)
      have h1 : ¬(ρ = μ ∧ τ = μ) := fun h => hρτ (h.1.trans h.2.symm)
      rw [hz]
      simp only [kron, if_neg hρτ]
      by_cases h2 : ρ = μ
      · have h3 : τ ≠ μ := fun h => h1 ⟨h2, h⟩
        simp [h2, h3]
      · simp [h2]
  · by_cases h1 : ρ = μ ∧ τ = ν
    · obtain ⟨rfl, rfl⟩ := h1
      rw [hB ρ τ hμν, hBb]
      simp only [kron, if_true, if_neg hμν, if_neg (Ne.symm hμν)]
      ring
    · by_cases h2 : ρ = ν ∧ τ = μ
      · obtain ⟨rfl, rfl⟩ := h2
        rw [hsym, hB τ ρ hμν, hBb]
        simp only [kron, if_true, if_neg hμν, if_neg (Ne.symm hμν)]
        ring
      · rw [zero μ ν ρ τ (by
          rintro (h | h | h)
          · exact h1 h
          · exact h2 h
          · exact hμν h.2)]
        have e1 : kron ρ μ * kron τ ν = 0 := by
          by_cases h : ρ = μ
          · have : τ ≠ ν := fun e => h1 ⟨h, e⟩
            simp [kron, this]
          · simp [kron, h]
        have e2 : kron ρ ν * kron τ μ = 0 := by
          by_cases h : ρ = ν
          · have : τ ≠ μ := fun e => h2 ⟨h, e⟩
            simp [kron, this]
          · simp [kron, h]
        rw [e1, e2]
        simp [kron, hμν]
theorem half_sum_transverse (b : ℂ) (μ ν : Fin 4) (x : Fin 4 → ℂ) :
    (1 / 2) * ∑ ρ, ∑ τ, (2 * b * kron ρ τ * kron μ ν -
        b * (kron ρ μ * kron τ ν + kron ρ ν * kron τ μ)) * x ρ * x τ =
      b * ((∑ ρ, x ρ ^ 2) * kron μ ν - x μ * x ν) := by
  have e1 : ∑ ρ, ∑ τ, kron ρ τ * x ρ * x τ = ∑ ρ, x ρ ^ 2 := by
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [Finset.sum_eq_single ρ (fun τ _ h => by simp [kron, Ne.symm h]) (by simp)]
    simp only [kron, if_true]
    ring
  have e2 : ∀ a c, ∑ ρ, ∑ τ, kron ρ a * kron τ c * x ρ * x τ = x a * x c := by
    intro a c
    rw [Finset.sum_eq_single a (fun ρ _ h => by simp [kron, h]) (by simp),
      Finset.sum_eq_single c (fun τ _ h => by simp [kron, h]) (by simp)]
    simp [kron]
  have e3 : ∑ ρ, ∑ τ, (2 * b * kron ρ τ * kron μ ν -
        b * (kron ρ μ * kron τ ν + kron ρ ν * kron τ μ)) * x ρ * x τ =
      2 * b * kron μ ν * (∑ ρ, ∑ τ, kron ρ τ * x ρ * x τ) -
        b * (∑ ρ, ∑ τ, kron ρ μ * kron τ ν * x ρ * x τ) -
        b * (∑ ρ, ∑ τ, kron ρ ν * kron τ μ * x ρ * x τ) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [e3, e1, e2, e2]
  ring
theorem gauge_relation_low_orders {f : Fin 4 → AmbientSpace → ℂ} {c : Fin 4 → ℂ}
    {L Q R : Fin 4 → AmbientSpace → ℂ}
    (J : ∀ μ, CubicJet (f μ) (c μ) (L μ) (Q μ) (R μ))
    (hg : ∀ p : AmbientSpace, ∑ μ, (Real.sin (p μ / 2) : ℂ) * f μ p = 0) :
    (∀ μ, c μ = 0) ∧ ∀ p : AmbientSpace, ∑ μ, (p μ : ℂ) * Q μ p = 0 := by
  have hone : ∀ μ : Fin 4, IsBigOPowAtZero (fun p : AmbientSpace => ((p μ : ℝ) : ℂ)) 1 := fun μ =>
    IsBigO.of_bound 1 (Eventually.of_forall fun p => by
      simpa using norm_le_pi_norm p μ)
  have hhalf : ∀ μ : Fin 4, IsBigOPowAtZero (fun p : AmbientSpace => (p μ : ℂ) / 2) 1 := fun μ =>
    ((hone μ).const_mul_left (1 / 2 : ℂ)).congr_left fun p => by ring
  have hcube : ∀ μ : Fin 4, IsBigOPowAtZero (fun p : AmbientSpace => -(p μ : ℂ) ^ 3 / 48) 3 :=
    fun μ => by
    have := isBigOPowAtZero_mul (isBigOPowAtZero_mul (hone μ) (hone μ)) (hone μ)
    have h2 := this.const_mul_left (-1 / 48 : ℂ)
    refine h2.congr_left fun p => ?_
    ring
  have hsin : ∀ μ : Fin 4, IsBigOPowAtZero
      (fun p : AmbientSpace => (Real.sin (p μ / 2) : ℂ) - ((p μ : ℂ) / 2 + -(p μ : ℂ) ^ 3 / 48))
      4 := by
    intro μ
    refine IsBigO.of_bound (5 / 96) ?_
    have hball : ∀ᶠ p : AmbientSpace in 𝓝 0, ‖p‖ ≤ 1 := by
      filter_upwards [Metric.closedBall_mem_nhds (0 : AmbientSpace) one_pos] with p hp
      simpa using hp
    filter_upwards [hball] with p hp
    have hx : |p μ / 2| ≤ 1 := by
      have h1 := norm_le_pi_norm p μ
      rw [Real.norm_eq_abs] at h1
      rw [abs_div, abs_two]
      linarith
    have hb := Real.sin_bound hx
    have e : (Real.sin (p μ / 2) : ℂ) - ((p μ : ℂ) / 2 + -(p μ : ℂ) ^ 3 / 48) =
        ((Real.sin (p μ / 2) - (p μ / 2 - (p μ / 2) ^ 3 / 6) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [e, Complex.norm_real, Real.norm_eq_abs]
    refine hb.trans ?_
    simp only [norm_pow, norm_norm]
    have h1 : |p μ / 2| ≤ ‖p‖ := by
      have h2 := norm_le_pi_norm p μ
      rw [Real.norm_eq_abs] at h2
      rw [abs_div, abs_two]
      have := abs_nonneg (p μ)
      linarith
    have h3 : |p μ / 2| ^ 4 ≤ ‖p‖ ^ 4 := pow_le_pow_left₀ (abs_nonneg _) h1 4
    have h4 : |p μ / 2| ^ 5 ≤ |p μ / 2| ^ 4 :=
      pow_le_pow_of_le_one (abs_nonneg _) hx (by norm_num)
    have h5 : 0 ≤ |p μ / 2| ^ 4 := by positivity
    linarith
  have hterm : ∀ μ, IsBigOPowAtZero (fun p : AmbientSpace => (Real.sin (p μ / 2) : ℂ) * f μ p -
      (((p μ : ℂ) / 2) * c μ + ((p μ : ℂ) / 2) * L μ p +
        (((p μ : ℂ) / 2) * Q μ p + (-(p μ : ℂ) ^ 3 / 48) * c μ))) 4 := by
    intro μ
    have hrest := (J μ).remainder
    have hg1 : IsBigOPowAtZero (fun p => L μ p + Q μ p + R μ p +
        (f μ p - (c μ + L μ p + Q μ p + R μ p))) 1 :=
      (((J μ).lin_bound.add (isBigOPowAtZero_mono (J μ).quad_bound (by norm_num))).add
        (isBigOPowAtZero_mono (J μ).cubic_bound (by norm_num))).add
        (isBigOPowAtZero_mono hrest (by norm_num))
    have hf0 : IsBigOPowAtZero (fun p => c μ + (L μ p + Q μ p + R μ p +
        (f μ p - (c μ + L μ p + Q μ p + R μ p)))) 0 := by
      refine IsBigO.add ?_ (isBigOPowAtZero_mono hg1 (by norm_num))
      exact IsBigO.of_bound ‖c μ‖ (Eventually.of_forall fun _ => by simp)
    have t1 := isBigOPowAtZero_mul (hsin μ) hf0
    have t2 := isBigOPowAtZero_mul (hhalf μ) (J μ).cubic_bound
    have t3 := isBigOPowAtZero_mul (hhalf μ) hrest
    have t4 := isBigOPowAtZero_mul (hcube μ) hg1
    have t5 := isBigOPowAtZero_mono t3 (k := 4) (by norm_num)
    refine (((t1.add t2).add t5).add t4).congr_left fun p => ?_
    ring
  have hsum : IsBigOPowAtZero (fun p : AmbientSpace => ∑ μ, (Real.sin (p μ / 2) : ℂ) * f μ p -
      ∑ μ, (((p μ : ℂ) / 2) * c μ + ((p μ : ℂ) / 2) * L μ p +
        (((p μ : ℂ) / 2) * Q μ p + (-(p μ : ℂ) ^ 3 / 48) * c μ))) 4 := by
    have := IsBigO.fun_sum (s := Finset.univ) (l := 𝓝 (0 : AmbientSpace))
      (g := fun p : AmbientSpace => ‖p‖ ^ 4) fun μ _ => hterm μ
    refine this.congr_left fun p => ?_
    rw [Finset.sum_sub_distrib]
  have hv := homogeneous_parts_eq_zero (c := 0) (L := fun p => ∑ μ, ((p μ : ℂ) / 2) * c μ)
    (Q := fun p => ∑ μ, ((p μ : ℂ) / 2) * L μ p)
    (R := fun p => ∑ μ, (((p μ : ℂ) / 2) * Q μ p + (-(p μ : ℂ) ^ 3 / 48) * c μ))
    (fun t v => by
      simp only [Finset.mul_sum, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
      exact Finset.sum_congr rfl fun _ _ => by ring)
    (fun t v => by
      simp only [Finset.mul_sum, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, (J _).smul_lin]
      exact Finset.sum_congr rfl fun _ _ => by ring)
    (fun t v => by
      simp only [Finset.mul_sum, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, (J _).smul_quad]
      exact Finset.sum_congr rfl fun _ _ => by ring)
    (by
      refine hsum.neg_left.congr_left fun p => ?_
      rw [hg p, Finset.sum_add_distrib, Finset.sum_add_distrib]
      ring_nf)
  have hc : ∀ μ, c μ = 0 := by
    intro μ
    have := hv.2.1 (basisVec μ)
    rw [Finset.sum_eq_single μ (fun x _ hx => by simp [basisVec, Pi.single_eq_of_ne hx])
      (by simp)] at this
    simpa [basisVec] using this
  refine ⟨hc, fun p => ?_⟩
  have := hv.2.2.2 p
  simp only [hc, mul_zero, add_zero] at this
  have e : ∑ μ, (p μ : ℂ) * Q μ p = 2 * ∑ μ, ((p μ : ℂ) / 2) * Q μ p := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [e, this, mul_zero]
theorem deriv_deriv_line_eq_fderiv_fderiv {G : AmbientSpace → ℂ} (hG : ContDiffAt ℝ 2 G 0)
    (u w : AmbientSpace) :
    deriv (fun s : ℝ => deriv (fun t : ℝ => G (s • u + t • w)) 0) 0 =
      fderiv ℝ (fderiv ℝ G) 0 u w := by
  have hd : ∀ᶠ x in 𝓝 (0 : AmbientSpace), DifferentiableAt ℝ G x := by
    filter_upwards [hG.eventually (by simp)] with x hx
    exact hx.differentiableAt (by simp)
  have ht : Tendsto (fun s : ℝ => s • u) (𝓝 0) (𝓝 (0 : AmbientSpace)) := by
    have : Continuous fun s : ℝ => s • u := by fun_prop
    simpa using this.tendsto 0
  have h1 : (fun s : ℝ => deriv (fun t : ℝ => G (s • u + t • w)) 0) =ᶠ[𝓝 0]
      fun s => fderiv ℝ G (s • u) w := by
    filter_upwards [ht.eventually hd] with s hs
    have hp : HasDerivAt (fun t : ℝ => s • u + t • w) w 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add (s • u)
    exact (hs.hasFDerivAt.comp_hasDerivAt_of_eq 0 hp (by simp)).deriv
  rw [h1.deriv_eq]
  have hD : DifferentiableAt ℝ (fderiv ℝ G) 0 :=
    (hG.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have hp : HasDerivAt (fun s : ℝ => s • u) u 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const u
  have h2 : HasDerivAt (fun s : ℝ => fderiv ℝ G (s • u)) (fderiv ℝ (fderiv ℝ G) 0 u) 0 :=
    hD.hasFDerivAt.comp_hasDerivAt_of_eq 0 hp (by simp)
  simpa using (h2.clm_apply (hasDerivAt_const (0 : ℝ) w)).deriv
theorem fderiv_fderiv_diag_eq {G : AmbientSpace → ℂ} (hG : ContDiffAt ℝ 2 G 0)
    (v : AmbientSpace) {a : ℂ}
    (ho : (fun t : ℝ => G (t • v) - (t : ℂ) ^ 2 * a) =o[𝓝 0] fun t => t ^ 2) :
    fderiv ℝ (fderiv ℝ G) 0 v v = 2 * a := by
  have hh : ContDiffAt ℝ 2 (fun t : ℝ => G (t • v)) 0 := by
    have hp : ContDiffAt ℝ 2 (fun t : ℝ => t • v) 0 := by fun_prop
    exact ContDiffAt.comp (g := G) (0 : ℝ) (by simpa using hG) hp
  rw [← deriv_deriv_zero_of_quadratic_approx hh ho, ← deriv_deriv_line_eq_fderiv_fderiv hG v v]
  congr 1
  funext s
  have e : (fun t : ℝ => G (s • v + t • v)) = fun t => (fun x : ℝ => G (x • v)) (s + t) := by
    funext t
    simp only [add_smul]
  rw [e]
  refine (deriv_comp_const_add (fun x : ℝ => G (x • v)) s 0).trans ?_
  simp
theorem isLittleO_along_line {G F Q w : AmbientSpace → ℂ} (hw : Continuous w) (hw0 : w 0 = 0)
    (hGF : ∀ p, G p = Complex.exp (w p) * F p) (hFQ : IsBigOPowAtZero (fun p => F p - Q p) 4)
    (hQ : ∀ (t : ℝ) (v : AmbientSpace), Q (t • v) = (t : ℂ) ^ 2 * Q v) (v : AmbientSpace) :
    (fun t : ℝ => G (t • v) - (t : ℂ) ^ 2 * Q v) =o[𝓝 0] fun t => t ^ 2 := by
  have ht : Tendsto (fun t : ℝ => t • v) (𝓝 0) (𝓝 (0 : AmbientSpace)) := by
    have : Continuous fun t : ℝ => t • v := by fun_prop
    simpa using this.tendsto 0
  have he : Tendsto (fun t : ℝ => Complex.exp (w (t • v))) (𝓝 0) (𝓝 1) := by
    have h1 : Tendsto (fun p => Complex.exp (w p)) (𝓝 0) (𝓝 (Complex.exp (w 0))) :=
      (Complex.continuous_exp.comp hw).tendsto 0
    rw [hw0, Complex.exp_zero] at h1
    exact h1.comp ht
  have h1 : (fun t : ℝ => Complex.exp (w (t • v)) - 1) =o[𝓝 0] fun _ => (1 : ℝ) :=
    (isLittleO_one_iff ℝ).2 (by simpa using he.sub_const 1)
  have h2 : (fun t : ℝ => (t : ℂ) ^ 2 * Q v) =O[𝓝 0] fun t : ℝ => t ^ 2 :=
    IsBigO.of_bound ‖Q v‖ (Eventually.of_forall fun t => by
      rw [norm_mul, norm_pow, norm_pow, Complex.norm_real, mul_comm])
  have h3 := h1.mul_isBigO h2
  have h4 : (fun t : ℝ => F (t • v) - Q (t • v)) =O[𝓝 0] fun t : ℝ => t ^ 4 := by
    refine (hFQ.comp_tendsto ht).trans
      (IsBigO.of_bound (‖v‖ ^ 4) (Eventually.of_forall fun t => ?_))
    simp only [Function.comp]
    rw [norm_pow, norm_norm, norm_smul, mul_pow, norm_pow]
    exact le_of_eq (by ring)
  have h5 := (he.isBigO_one ℝ).mul h4
  have h6 : (fun t : ℝ => (1 : ℝ) * t ^ 4) =o[𝓝 0] fun t : ℝ => t ^ 2 := by
    simpa using isLittleO_pow_pow (𝕜 := ℝ) (m := 2) (n := 4) (by norm_num)
  have h7 := h5.trans_isLittleO h6
  have h8 : (fun t : ℝ => (1 : ℝ) * t ^ 2) = fun t : ℝ => t ^ 2 := by
    funext t
    ring
  rw [h8] at h3
  refine (h3.add h7).congr_left fun t => ?_
  rw [hGF, hQ]
  ring
theorem secondPartialAtZero_eq_fderiv {g : (Fin 4 → ℂ) → ℂ}
    (hG : ContDiffAt ℝ 2 (fun p : AmbientSpace => g (toComplexVec p)) 0) (μ ν : Fin 4) :
    secondPartialAtZero g μ ν =
      fderiv ℝ (fderiv ℝ fun p : AmbientSpace => g (toComplexVec p)) 0 (basisVec μ)
        (basisVec ν) := by
  rw [← deriv_deriv_line_eq_fderiv_fderiv hG]
  have e : ∀ (ρ : Fin 4) (s : ℝ), (Pi.single ρ s : AmbientSpace) = s • basisVec ρ := by
    intro ρ s
    ext x
    by_cases hx : x = ρ
    · subst hx
      simp [basisVec]
    · simp [basisVec, Pi.single_eq_of_ne hx]
  unfold secondPartialAtZero
  simp only [e]
theorem twistedSymbol_isHolomorphicIn {O : Set (ComplexCoordinates 4)} {g : (Fin 4 → ℂ) → ℂ}
    (hg : ComplexCoordinates.IsHolomorphicIn O fun (z : ComplexCoordinates 4) (_ : Fin 1) => g z)
    (μ ν : Fin 4) :
    ComplexCoordinates.IsHolomorphicIn O fun (z : ComplexCoordinates 4) (_ : Fin 1) =>
      Complex.exp (Complex.I * ((z μ - z ν) / 2)) * g z := by
  obtain ⟨h1, h2, h3⟩ := hg
  refine ⟨h1, ?_, ?_⟩
  · refine continuousOn_pi.2 fun _ => ?_
    have hc : Continuous fun z : ComplexCoordinates 4 =>
        Complex.exp (Complex.I * ((z μ - z ν) / 2)) := by
      fun_prop
    exact hc.continuousOn.mul (continuousOn_pi.1 h2 0)
  · intro a ha j
    filter_upwards [h3 a ha j] with ζ hζ
    have h0 := (differentiableAt_pi.1 hζ) 0
    refine differentiableAt_pi.2 fun _ => DifferentiableAt.mul ?_ h0
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    fun_prop
theorem exists_cubicJet_of_isHolomorphicIn
    (H : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {O : Set (ComplexCoordinates 4)} (hO : (0 : ComplexCoordinates 4) ∈ O) {g : (Fin 4 → ℂ) → ℂ}
    (hg : ComplexCoordinates.IsHolomorphicIn O fun (z : ComplexCoordinates 4) (_ : Fin 1) => g z) :
    ∃ c₀ L Q R, CubicJet (fun p : AmbientSpace => g (toComplexVec p)) c₀ L Q R := by
  have hopen := hg.1
  have H1 := H.1 4 O hopen |>.1 1 (fun z _ => g z) hg
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen 0 hO
  have hsub : ComplexCoordinates.PowerSeriesHolomorphy.closedPolydisk
      (0 : ComplexCoordinates 4) (ε / 2) ⊆ O := by
    intro z hz
    refine hball (mem_ball_zero_iff.2 ?_)
    have : ‖z‖ ≤ ε / 2 := (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => by
      simpa using hz j
    linarith
  obtain ⟨c, hsum, hunif⟩ := H1.1 0 hO (ε / 2) (by positivity) hsub
  have hr : 0 < ε / 4 := by positivity
  refine exists_cubicJet_of_hasSum (c := fun m => c m 0) hr ?_ ?_
  · intro p hp
    have hm : toComplexVec p ∈ ComplexCoordinates.PowerSeriesHolomorphy.openPolydisk
        (0 : ComplexCoordinates 4) (ε / 2) := by
      intro j
      have h1 := norm_le_pi_norm p j
      simp only [toComplexVec, Pi.zero_apply, sub_zero, Complex.norm_real]
      linarith
    have h2 := Pi.hasSum.1 (hsum _ hm) 0
    simpa [ComplexCoordinates.PowerSeriesHolomorphy.monomialTerm, toComplexVec] using h2
  · have hz : (fun _ : Fin 4 => ((ε / 4 : ℝ) : ℂ)) ∈
        ComplexCoordinates.PowerSeriesHolomorphy.closedPolydisk
          (0 : ComplexCoordinates 4) (ε / 4) := by
      intro j
      simp only [Pi.zero_apply, sub_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      exact le_rfl
    have h2 := ((hunif (ε / 4) (by linarith)).1) _ hz
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) h2
    simp only [ComplexCoordinates.PowerSeriesHolomorphy.monomialTerm, Pi.zero_apply,
      sub_zero, norm_smul, norm_prod, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      Finset.prod_pow_eq_pow_sum]
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm (c m) 0) (by positivity)
theorem contDiffAt_two_of_isHolomorphicIn
    (H : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {O : Set (ComplexCoordinates 4)} (hO : (0 : ComplexCoordinates 4) ∈ O) {g : (Fin 4 → ℂ) → ℂ}
    (hg : ComplexCoordinates.IsHolomorphicIn O fun (z : ComplexCoordinates 4) (_ : Fin 1) => g z) :
    ContDiffAt ℝ 2 (fun p : AmbientSpace => g (toComplexVec p)) 0 := by
  have hopen := hg.1
  have H1 := (H.1 4 O hopen |>.1 1 (fun z _ => g z) hg).2.1
  have h2 : ContDiffAt ℝ ∞ (fun (z : ComplexCoordinates 4) (_ : Fin 1) => g z) 0 :=
    H1.contDiffAt (hopen.mem_nhds hO)
  have h3 : ContDiffAt ℝ 2 g 0 := (contDiffAt_pi.1 (h2.of_le (by norm_cast)) 0)
  have h4 : ContDiff ℝ 2 (fun p : AmbientSpace => toComplexVec p) := by
    refine contDiff_pi.2 fun μ => ?_
    exact Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ μ)
  have h5 : toComplexVec (0 : AmbientSpace) = 0 := by
    ext x
    simp [toComplexVec]
  exact ContDiffAt.comp (g := g) (0 : AmbientSpace) (by simpa [h5] using h3) h4.contDiffAt
theorem exp_sub_one_mul_eq_sin_mul (x y : ℝ) (w : ℂ) :
    (Complex.exp (Complex.I * (x : ℂ)) - 1) * w =
      2 * Complex.I * Complex.exp (Complex.I * (y : ℂ) / 2) *
        ((Real.sin (x / 2) : ℂ) * (Complex.exp (Complex.I * (((x : ℂ) - y) / 2)) * w)) := by
  set A := Complex.exp (Complex.I * (x : ℂ) / 2) with hA
  set B := Complex.exp (Complex.I * (y : ℂ) / 2) with hB
  have hA0 : A ≠ 0 := Complex.exp_ne_zero _
  have hB0 : B ≠ 0 := Complex.exp_ne_zero _
  have e1 : Complex.exp (Complex.I * (x : ℂ)) = A * A := by
    rw [hA, ← Complex.exp_add]
    congr 1
    ring
  have e2 : Complex.exp (Complex.I * (((x : ℂ) - y) / 2)) = A * B⁻¹ := by
    rw [hA, hB, ← Complex.exp_neg, ← Complex.exp_add]
    congr 1
    ring
  have e3 : (Real.sin (x / 2) : ℂ) = (A⁻¹ - A) * Complex.I / 2 := by
    rw [Complex.ofReal_sin, Complex.sin, hA, ← Complex.exp_neg]
    push_cast
    congr 3 <;> ring_nf
  rw [e1, e2, e3]
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring
theorem two_mul_eq_polarization {E : Type*} [AddCommGroup E] [Module ℝ E] {B : E → E → ℂ}
    (hadd : ∀ a b c, B (a + b) c = B a c + B b c) (hadd' : ∀ a b c, B a (b + c) = B a b + B a c)
    (hsym : ∀ a b, B a b = B b a) (u w : E) :
    2 * B u w = B (u + w) (u + w) - B u u - B w w := by
  rw [hadd, hadd', hadd', hsym w u]
  ring
theorem taylorExpansionClaim_holds (H : ComplexCoordinates.PowerSeriesHolomorphy.Properties) :
    TaylorExpansionClaim := by
  intro δ π hδ hhol hgauge hperm hrefl hconj
  have hmem : ∀ p : AmbientSpace, toComplexVec p ∈ imStrip δ := fun p μ => by
    simp [toComplexVec, hδ.le]
  have hzero : (0 : ComplexCoordinates 4) ∈ imStrip δ := fun μ => by simp [hδ.le]
  have hO : ∀ μ ν : Fin 4, ∃ O : Set (ComplexCoordinates 4), (0 : ComplexCoordinates 4) ∈ O ∧
      ComplexCoordinates.IsHolomorphicIn O
        fun (z : ComplexCoordinates 4) (_ : Fin 1) => π μ ν z := by
    intro μ ν
    obtain ⟨O, hs, hh⟩ := hhol μ ν
    exact ⟨O, hs hzero, hh⟩
  choose O hO0 hOh using hO
  let F : Fin 4 → Fin 4 → AmbientSpace → ℂ := fun μ ν p => twistedSymbol π μ ν (toComplexVec p)
  have hJ : ∀ μ ν, ∃ c L Q R, CubicJet (F μ ν) c L Q R := fun μ ν =>
    exists_cubicJet_of_isHolomorphicIn H (hO0 μ ν) (g := twistedSymbol π μ ν)
      (twistedSymbol_isHolomorphicIn (hOh μ ν) μ ν)
  choose c L Q R J using hJ
  have hP : ∀ (σ : Equiv.Perm (Fin 4)) (μ ν : Fin 4) (p : AmbientSpace),
      F (σ μ) (σ ν) (p ∘ σ.symm) = F μ ν p := fun σ μ ν p => hperm σ _ (hmem p) μ ν
  have hR : ∀ (ρ μ ν : Fin 4) (p : AmbientSpace),
      F μ ν (reflectAxis ρ p) = reflectSign ρ μ * reflectSign ρ ν * F μ ν p := by
    intro ρ μ ν p
    have e : toComplexVec (reflectAxis ρ p) = reflectCoord ρ (toComplexVec p) := by
      ext x
      by_cases hx : x = ρ
      · subst hx
        simp [toComplexVec, reflectAxis, reflectCoord]
      · simp [toComplexVec, reflectAxis, reflectCoord, hx, Function.update_of_ne hx]
    show twistedSymbol π μ ν (toComplexVec (reflectAxis ρ p)) = _
    rw [e]
    exact hrefl ρ _ (hmem p) μ ν
  have hs : ∀ μ : Fin 4, reflectSign 0 μ * reflectSign 1 μ * reflectSign 2 μ *
      reflectSign 3 μ = -1 := by
    intro μ
    fin_cases μ <;> simp [reflectSign]
  have hE : ∀ (μ ν : Fin 4) (p : AmbientSpace), F μ ν (-p) = F μ ν p := by
    intro μ ν p
    have e : -p = reflectAxis 0 (reflectAxis 1 (reflectAxis 2 (reflectAxis 3 p))) := by
      ext x
      fin_cases x <;> simp [reflectAxis]
    rw [e, hR, hR, hR, hR]
    calc _ = (reflectSign 0 μ * reflectSign 1 μ * reflectSign 2 μ * reflectSign 3 μ) *
          (reflectSign 0 ν * reflectSign 1 ν * reflectSign 2 ν * reflectSign 3 ν) *
            F μ ν p := by ring
      _ = _ := by
        rw [hs, hs]
        ring
  have hC : ∀ (μ ν : Fin 4) (p : AmbientSpace), (starRingEnd ℂ) (F μ ν p) = F μ ν p := by
    intro μ ν p
    refine Eq.trans ?_ (hE μ ν p)
    show (starRingEnd ℂ) (twistedSymbol π μ ν (toComplexVec p)) =
      twistedSymbol π μ ν (toComplexVec (-p))
    unfold twistedSymbol
    rw [map_mul, hconj, ← Complex.exp_conj]
    congr 2
    have hc2 : (starRingEnd ℂ) (2 : ℂ) = 2 := by simpa using Complex.conj_ofReal 2
    simp [toComplexVec, Complex.conj_ofReal, hc2]
    ring
  have hG : ∀ (ν : Fin 4) (p : AmbientSpace), ∑ μ, (Real.sin (p μ / 2) : ℂ) * F μ ν p = 0 := by
    intro ν p
    have h := hgauge _ (hmem p) ν
    have e : ∀ μ, (Complex.exp (Complex.I * toComplexVec p μ) - 1) * π μ ν (toComplexVec p) =
        2 * Complex.I * Complex.exp (Complex.I * (p ν : ℂ) / 2) *
          ((Real.sin (p μ / 2) : ℂ) * F μ ν p) := fun μ =>
      exp_sub_one_mul_eq_sin_mul (p μ) (p ν) _
    simp only [e] at h
    rw [← Finset.mul_sum] at h
    refine (mul_eq_zero.1 h).resolve_left ?_
    exact mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) (Complex.exp_ne_zero _)
  have hLR : ∀ μ ν, (∀ v, L μ ν v = 0) ∧ ∀ v, R μ ν v = 0 := by
    intro μ ν
    obtain ⟨-, h1, -, h3⟩ := (J μ ν).comp_of_eq_smul (J μ ν) (fun v => -v) (fun v => by simp)
      (fun t v => by simp) 1 (fun v => by simp [hE])
    refine ⟨fun v => ?_, fun v => ?_⟩
    · have e := (J μ ν).smul_lin (-1) v
      have e' := h1 v
      simp only [neg_smul, one_smul] at e
      rw [e'] at e
      push_cast at e
      linear_combination (1 / 2 : ℂ) * e
    · have e := (J μ ν).smul_cubic (-1) v
      have e' := h3 v
      simp only [neg_smul, one_smul] at e
      rw [e'] at e
      push_cast at e
      linear_combination (1 / 2 : ℂ) * e
  have hgo : ∀ ν, (∀ μ, c μ ν = 0) ∧ ∀ p : AmbientSpace, ∑ μ, (p μ : ℂ) * Q μ ν p = 0 :=
    fun ν => gauge_relation_low_orders (fun μ => J μ ν) (hG ν)
  have hQe : ∀ μ ν v, Q μ ν (-v) = Q μ ν v := by
    intro μ ν v
    have e := (J μ ν).smul_quad (-1) v
    simpa using e
  have hvan : ∀ μ ν ρ τ, quadCoeff (Q μ ν) ρ τ ≠ 0 →
      (ρ = μ ∧ τ = ν) ∨ (ρ = ν ∧ τ = μ) ∨ (ρ = τ ∧ μ = ν) := by
    intro μ ν ρ τ h
    refine index_pairs_of_axisSign_eq μ ν ρ τ fun σ => ?_
    obtain ⟨-, -, h2, -⟩ := (J μ ν).comp_of_eq_smul (J μ ν) (reflectAxis σ)
      (norm_reflectAxis_le σ) (reflectAxis_smul σ) (reflectSign σ μ * reflectSign σ ν) (hR σ μ ν)
    have h3 := axisSign_mul_quadCoeff (hQe μ ν) σ _ h2 ρ τ
    have h4 := mul_right_cancel₀ h h3
    rw [reflectSign_eq_axisSign, reflectSign_eq_axisSign] at h4
    exact_mod_cast h4
  have hTsym : ∀ μ ν ρ τ, quadCoeff (Q μ ν) ρ τ = quadCoeff (Q μ ν) τ ρ := by
    intro μ ν ρ τ
    have e : basisVec τ - basisVec ρ = -(basisVec ρ - basisVec τ) := by abel
    rw [quadCoeff, quadCoeff, e, hQe, add_comm]
  have hTperm : ∀ (σ : Equiv.Perm (Fin 4)) μ ν ρ τ,
      quadCoeff (Q (σ μ) (σ ν)) (σ ρ) (σ τ) = quadCoeff (Q μ ν) ρ τ := by
    intro σ μ ν ρ τ
    obtain ⟨-, -, h2, -⟩ := (J μ ν).comp_of_eq_smul (J (σ μ) (σ ν)) (fun v => v ∘ σ.symm)
      (fun v => (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2 fun x => norm_le_pi_norm v _)
      (fun t v => rfl) 1 (fun v => by simpa using hP σ μ ν v)
    have e1 : basisVec (σ ρ) + basisVec (σ τ) = (basisVec ρ + basisVec τ) ∘ σ.symm := by
      rw [← basisVec_comp_symm, ← basisVec_comp_symm]
      rfl
    have e2 : basisVec (σ ρ) - basisVec (σ τ) = (basisVec ρ - basisVec τ) ∘ σ.symm := by
      rw [← basisVec_comp_symm, ← basisVec_comp_symm]
      rfl
    rw [quadCoeff, quadCoeff, e1, e2, h2, h2, one_mul, one_mul]
  have hTG : ∀ (ν : Fin 4) (p : AmbientSpace),
      ∑ μ, (p μ : ℂ) * ∑ ρ, ∑ τ, quadCoeff (Q μ ν) ρ τ * (p ρ : ℂ) * (p τ : ℂ) = 0 := by
    intro ν p
    have h := (hgo ν).2 p
    have e : ∀ μ, (p μ : ℂ) * ∑ ρ, ∑ τ, quadCoeff (Q μ ν) ρ τ * (p ρ : ℂ) * (p τ : ℂ) =
        2 * ((p μ : ℂ) * Q μ ν p) := by
      intro μ
      rw [eq_half_sum_quadCoeff (J μ ν).quad_form p]
      ring
    simp only [e, ← Finset.mul_sum, h, mul_zero]
  obtain ⟨b, hb⟩ :=
    tensor_eq_transverse (fun μ ν ρ τ => quadCoeff (Q μ ν) ρ τ) hTsym hvan hTperm hTG
  have hQ : ∀ (μ ν : Fin 4) (p : AmbientSpace), Q μ ν p =
      b * ((∑ ρ, (p ρ : ℂ) ^ 2) * kron μ ν - (p μ : ℂ) * (p ν : ℂ)) := by
    intro μ ν p
    rw [eq_half_sum_quadCoeff (J μ ν).quad_form p]
    simp only [hb]
    exact half_sum_transverse b μ ν fun ρ => (p ρ : ℂ)
  have hFQ : ∀ μ ν, IsBigOPowAtZero (fun p => F μ ν p - Q μ ν p) 4 := by
    intro μ ν
    refine (J μ ν).remainder.congr_left fun p => ?_
    rw [(hgo ν).1 μ, (hLR μ ν).1, (hLR μ ν).2]
    ring
  have hconjQ : ∀ v, (starRingEnd ℂ) (Q 0 0 v) - Q 0 0 v = 0 := by
    have hv := homogeneous_parts_eq_zero (c := 0) (L := fun _ => 0)
      (Q := fun v => (starRingEnd ℂ) (Q 0 0 v) - Q 0 0 v) (R := fun _ => 0)
      (fun t v => by simp)
      (fun t v => by
        simp only [(J 0 0).smul_quad, map_mul, map_pow, Complex.conj_ofReal]
        ring)
      (fun t v => by simp)
      (by
        have h1 := hFQ 0 0
        have h2 : IsBigOPowAtZero (fun p => (starRingEnd ℂ) (F 0 0 p - Q 0 0 p)) 4 :=
          IsBigO.of_norm_left (by
            simpa only [Complex.norm_conj] using h1.norm_left)
        refine (h1.sub h2).congr_left fun p => ?_
        simp only [map_sub, hC]
        ring)
    exact hv.2.2.1
  have hbr : (starRingEnd ℂ) b = b := by
    have h1 := hconjQ (basisVec 1)
    have h2 : Q 0 0 (basisVec 1) = b := by
      rw [hQ]
      simp [Fin.sum_univ_four, kron, basisVec]
    rw [h2] at h1
    exact sub_eq_zero.1 h1
  obtain ⟨r, rfl⟩ := Complex.conj_eq_iff_real.1 hbr
  have hsq : ∀ p : AmbientSpace,
      YangMills.Construction.TorusMetric.euclidNormVec p ^ 2 = ∑ ρ, p ρ ^ 2 := fun p =>
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hQr : ∀ (μ ν : Fin 4) (p : AmbientSpace), Q μ ν p = (transverseTensor r μ ν p : ℂ) := by
    intro μ ν p
    rw [hQ, transverseTensor, hsq]
    by_cases h : μ = ν
    · simp [h, kron]
    · simp [h, kron]
  have hdiff : ∀ (μ ν : Fin 4) (v : AmbientSpace),
      fderiv ℝ (fderiv ℝ fun p : AmbientSpace => π μ ν (toComplexVec p)) 0 v v =
        2 * Q μ ν v := by
    intro μ ν v
    refine fderiv_fderiv_diag_eq
      (contDiffAt_two_of_isHolomorphicIn H (hO0 μ ν) (hOh μ ν)) v ?_
    refine isLittleO_along_line (G := fun p => π μ ν (toComplexVec p)) (F := F μ ν)
      (w := fun p => -(Complex.I * (((p μ : ℂ) - (p ν : ℂ)) / 2))) (by fun_prop) (by simp)
      (fun p => ?_) (hFQ μ ν) (J μ ν).smul_quad v
    show π μ ν (toComplexVec p) = _ * twistedSymbol π μ ν (toComplexVec p)
    unfold twistedSymbol
    simp only [toComplexVec]
    rw [← mul_assoc, ← Complex.exp_add]
    simp
  refine ⟨r, ?_, ?_⟩
  · intro μ ν
    have hle : ∀ p : AmbientSpace,
        ‖p‖ ≤ YangMills.Construction.TorusMetric.euclidNormVec p := fun p => by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun x => ?_
      rw [Real.norm_eq_abs]
      exact Real.abs_le_sqrt (Finset.single_le_sum (f := fun ρ => p ρ ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ x))
    have h0 : (fun p : AmbientSpace => ‖p‖ ^ 4) =O[𝓝 0]
        fun p => YangMills.Construction.TorusMetric.euclidNormVec p ^ 4 :=
      IsBigO.of_bound 1 (Eventually.of_forall fun p => by
        have hnn : 0 ≤ YangMills.Construction.TorusMetric.euclidNormVec p := Real.sqrt_nonneg _
        rw [one_mul, norm_pow, norm_pow, norm_norm, Real.norm_of_nonneg hnn]
        exact pow_le_pow_left₀ (norm_nonneg _) (hle p) 4)
    refine ((hFQ μ ν).trans h0).congr_left fun p => ?_
    rw [hQr]
    show twistedSymbol π μ ν (toComplexVec p) - _ = _
    unfold twistedSymbol
    simp only [toComplexVec]
    push_cast
    rfl
  · intro μ ν hμν
    have hc₁ := contDiffAt_two_of_isHolomorphicIn H (hO0 μ ν) (hOh μ ν)
    have hc₂ := contDiffAt_two_of_isHolomorphicIn H (hO0 ν ν) (hOh ν ν)
    have hu : ∀ x : Fin 4, basisVec x x = 1 := fun x => by simp [basisVec]
    have hu' : ∀ x y : Fin 4, x ≠ y → basisVec y x = 0 := fun x y h => by
      simp [basisVec, Pi.single_eq_of_ne h]
    have hsum : ∑ ρ, ((basisVec μ ρ : ℝ) : ℂ) ^ 2 = 1 := by
      rw [Finset.sum_eq_single μ (fun x _ hx => by simp [hu' x μ hx]) (by simp)]
      simp [hu]
    constructor
    · rw [secondPartialAtZero_eq_fderiv hc₁]
      have hS := hc₁.isSymmSndFDerivAt (by simp)
      have h2 := two_mul_eq_polarization
        (B := fun a b => fderiv ℝ (fderiv ℝ fun p : AmbientSpace => π μ ν (toComplexVec p)) 0 a b)
        (fun a b c => by simp) (fun a b c => by simp) (fun a b => hS a b)
        (basisVec μ) (basisVec ν)
      simp only [hdiff, hQ, Pi.add_apply, hu, hu' μ ν hμν, hu' ν μ (Ne.symm hμν), kron,
        if_neg hμν] at h2
      push_cast at h2
      linear_combination (1 / 2 : ℂ) * h2
    · rw [secondPartialAtZero_eq_fderiv hc₂, hdiff, hQ, hsum]
      simp only [kron, if_true, hu' ν μ (Ne.symm hμν)]
      push_cast
      ring
end YangMills.Construction.OneLoopLaw.CovariantSymbolTaylor
end
