import YangMills.Construction.ClusterExpansionOfAStep.CutOnTheQuaternions
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion ContDiff Topology
namespace YangMills.Construction.QuaternionCutoff
open YangMills.Construction.ColdStepAtMirrorFrames
def extendByZero (g : ℝ → ℝ) (t : ℝ) : ℝ := if 0 < t then g t else 0
theorem extendByZero_hasDerivAt (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hg0 : g 0 = 0) (hg1 : deriv g 0 = 0) (t : ℝ) :
    HasDerivAt (_root_.YangMills.Construction.QuaternionCutoff.extendByZero g) (_root_.YangMills.Construction.QuaternionCutoff.extendByZero (deriv g) t) t := by
  have hd : Differentiable ℝ g := hg.differentiable (by simp)
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have hev : _root_.YangMills.Construction.QuaternionCutoff.extendByZero g =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds ht] with z hz
      have hz' : z < 0 := hz
      simp [_root_.YangMills.Construction.QuaternionCutoff.extendByZero, not_lt.mpr hz'.le]
    have : _root_.YangMills.Construction.QuaternionCutoff.extendByZero (deriv g) t = 0 := by simp [_root_.YangMills.Construction.QuaternionCutoff.extendByZero, not_lt.mpr ht.le]
    rw [this]
    exact (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hev
  · have hz : _root_.YangMills.Construction.QuaternionCutoff.extendByZero (deriv g) 0 = 0 := by simp [_root_.YangMills.Construction.QuaternionCutoff.extendByZero]
    rw [hz]
    have hgd : HasDerivAt g 0 0 := by
      have := (hd 0).hasDerivAt
      rwa [hg1] at this
    rw [hasDerivAt_iff_isLittleO_nhds_zero] at hgd ⊢
    simp only [zero_add, hg0, sub_zero] at hgd ⊢
    have e0 : _root_.YangMills.Construction.QuaternionCutoff.extendByZero g 0 = 0 := by simp [_root_.YangMills.Construction.QuaternionCutoff.extendByZero]
    rw [e0]
    simp only [sub_zero]
    refine Asymptotics.IsBigO.trans_isLittleO ?_ hgd
    refine Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun z => ?_)
    unfold _root_.YangMills.Construction.QuaternionCutoff.extendByZero
    split_ifs
    · simp
    · simp
  · have hev : _root_.YangMills.Construction.QuaternionCutoff.extendByZero g =ᶠ[𝓝 t] g := by
      filter_upwards [Ioi_mem_nhds ht] with z hz
      simp [_root_.YangMills.Construction.QuaternionCutoff.extendByZero, show 0 < z from hz]
    have : _root_.YangMills.Construction.QuaternionCutoff.extendByZero (deriv g) t = deriv g t := by simp [_root_.YangMills.Construction.QuaternionCutoff.extendByZero, ht]
    rw [this]
    exact (hd t).hasDerivAt.congr_of_eventuallyEq hev
theorem extendByZero_contDiff (m : ℕ) : ∀ (g : ℝ → ℝ), ContDiff ℝ ∞ g → (∀ k : ℕ, iteratedDeriv k g 0 = 0) →
    ContDiff ℝ m (_root_.YangMills.Construction.QuaternionCutoff.extendByZero g) := by
  induction m with
  | zero =>
    intro g hg hk
    have hg0 : g 0 = 0 := by simpa using hk 0
    have hg1 : deriv g 0 = 0 := by simpa using hk 1
    simp only [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.mpr fun t => (extendByZero_hasDerivAt g hg hg0 hg1 t).continuousAt
  | succ m ih =>
    intro g hg hk
    have hg0 : g 0 = 0 := by simpa using hk 0
    have hg1 : deriv g 0 = 0 := by simpa using hk 1
    have hdg : ContDiff ℝ ∞ (deriv g) := by
      have := (contDiff_infty_iff_deriv (𝕜 := ℝ) (f := g)).mp hg
      exact this.2
    have hkd : ∀ k : ℕ, iteratedDeriv k (deriv g) 0 = 0 := by
      intro k
      rw [← iteratedDeriv_succ']
      exact hk (k + 1)
    have hderiv : deriv (_root_.YangMills.Construction.QuaternionCutoff.extendByZero g) = _root_.YangMills.Construction.QuaternionCutoff.extendByZero (deriv g) :=
      funext fun t => (extendByZero_hasDerivAt g hg hg0 hg1 t).deriv
    have : ContDiff ℝ ((m : WithTop ℕ∞) + 1) (_root_.YangMills.Construction.QuaternionCutoff.extendByZero g) := by
      refine contDiff_succ_iff_deriv.mpr ⟨fun t => (extendByZero_hasDerivAt g hg hg0 hg1 t).differentiableAt, ?_, ?_⟩
      · simp
      · rw [hderiv]
        exact ih (deriv g) hdg hkd
    exact_mod_cast this
theorem extendByZero_contDiff_top (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hk : ∀ k : ℕ, iteratedDeriv k g 0 = 0) :
    ContDiff ℝ ∞ (_root_.YangMills.Construction.QuaternionCutoff.extendByZero g) :=
  contDiff_infty.mpr fun m => extendByZero_contDiff m g hg hk
def flatAtZero (t : ℝ) : ℝ := expNegInvGlue (6 * t ^ 2)
theorem flatAtZero_contDiff : ContDiff ℝ ∞ flatAtZero :=
  (expNegInvGlue.contDiff (n := ⊤)).comp (by fun_prop)
theorem iteratedFDeriv_expNegInvGlue_zero (i : ℕ) : iteratedFDeriv ℝ i expNegInvGlue 0 = 0 := by
  have hc : Continuous (iteratedFDeriv ℝ i expNegInvGlue) :=
    (expNegInvGlue.contDiff (n := ⊤)).continuous_iteratedFDeriv (m := i) (by exact_mod_cast le_top)
  have hz : ∀ z : ℝ, z < 0 → iteratedFDeriv ℝ i expNegInvGlue z = 0 := by
    intro z hz
    have hev : expNegInvGlue =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hz] with w hw
      exact expNegInvGlue.zero_of_nonpos (le_of_lt hw)
    rw [(hev.iteratedFDeriv (𝕜 := ℝ) i).self_of_nhds]
    exact congrFun iteratedFDeriv_fun_zero z
  have hclosed : IsClosed {z : ℝ | iteratedFDeriv ℝ i expNegInvGlue z = 0} :=
    isClosed_eq hc continuous_const
  have hsub : Set.Iio (0 : ℝ) ⊆ {z : ℝ | iteratedFDeriv ℝ i expNegInvGlue z = 0} := fun z hz' => hz z hz'
  have hcl := closure_minimal hsub hclosed
  have h0 : (0 : ℝ) ∈ closure (Set.Iio (0 : ℝ)) := by
    rw [closure_Iio]
    exact Set.mem_Iic.mpr le_rfl
  exact hcl h0
theorem iteratedDeriv_flatAtZero_zero (k : ℕ) : iteratedDeriv k flatAtZero 0 = 0 := by
  have hq : ContDiff ℝ ∞ (fun t : ℝ => 6 * t ^ 2) := by fun_prop
  obtain ⟨D, hD1, hD⟩ : ∃ D : ℝ, 1 ≤ D ∧ ∀ i, i ≤ k →
      ‖iteratedFDeriv ℝ i (fun t : ℝ => 6 * t ^ 2) 0‖ ≤ D := by
    refine ⟨1 + ∑ i ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ i (fun t : ℝ => 6 * t ^ 2) 0‖, ?_, ?_⟩
    · have : 0 ≤ ∑ i ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ i (fun t : ℝ => 6 * t ^ 2) 0‖ :=
        Finset.sum_nonneg fun _ _ => norm_nonneg _
      linarith
    · intro i hi
      have := Finset.single_le_sum (f := fun i => ‖iteratedFDeriv ℝ i (fun t : ℝ => 6 * t ^ 2) 0‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
      linarith
  have hb := norm_iteratedFDeriv_comp_le (𝕜 := ℝ) (g := expNegInvGlue) (f := fun t : ℝ => 6 * t ^ 2)
    (n := k) (N := ∞) (expNegInvGlue.contDiff (n := ⊤)) hq (by exact_mod_cast le_top) 0 (C := 0) (D := D)
    (fun i _ => by
      have e : (6 * (0 : ℝ) ^ 2) = 0 := by norm_num
      simp only [e, iteratedFDeriv_expNegInvGlue_zero]
      simp)
    (fun i h1 hi => (hD i hi).trans (le_self_pow₀ hD1 (by omega)))
  have hz : ‖iteratedFDeriv ℝ k flatAtZero 0‖ ≤ 0 := by
    have e : flatAtZero = expNegInvGlue ∘ fun t : ℝ => 6 * t ^ 2 := rfl
    rw [e]
    simpa using hb
  rw [← norm_eq_zero, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact le_antisymm hz (norm_nonneg _)
def edgeBump : ℝ → ℝ := _root_.YangMills.Construction.QuaternionCutoff.extendByZero flatAtZero
theorem edgeBump_contDiff : ContDiff ℝ ∞ edgeBump :=
  extendByZero_contDiff_top _ flatAtZero_contDiff iteratedDeriv_flatAtZero_zero
theorem edgeBump_of_pos (t : ℝ) (ht : 0 < t) : edgeBump t = Real.exp (-((t ^ 2)⁻¹ / 6)) := by
  have h : 0 < 6 * t ^ 2 := by positivity
  simp only [edgeBump, _root_.YangMills.Construction.QuaternionCutoff.extendByZero, ht, if_true, flatAtZero, expNegInvGlue, not_le.mpr h, if_false]
  congr 1
  field_simp
theorem edgeBump_of_nonpos (t : ℝ) (ht : t ≤ 0) : edgeBump t = 0 := by
  simp [edgeBump, _root_.YangMills.Construction.QuaternionCutoff.extendByZero, not_lt.mpr ht]
theorem cutoff_eq_near_edge (ρ : ℝ) (p : ℝ → ℝ) (hρ : 0 < ρ) (hp : IsCutoff ρ p) :
    ∃ u₁ α β : ℝ, 0 < u₁ ∧ u₁ < ρ ∧ ∀ u, u₁ < u → u < ρ → p u = ((ρ - u) ^ 2)⁻¹ / 6 + α * u + β := by
  obtain ⟨u₀, hu₀, hrim⟩ := hp.rim_second_deriv
  set u₁ := max u₀ (ρ / 2) with hu₁
  have h1 : 0 < u₁ := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have h2 : u₁ < ρ := max_lt hu₀ (by linarith)
  have hI : IsOpen (Set.Ioo u₁ ρ) := isOpen_Ioo
  have hIc : IsPreconnected (Set.Ioo u₁ ρ) := isPreconnected_Ioo
  have hsub : Set.Ioo u₁ ρ ⊆ Set.Ico 0 ρ := fun u hu => ⟨(h1.trans hu.1).le, hu.2⟩
  have hpOn : ContDiffOn ℝ ∞ p (Set.Ioo u₁ ρ) := hp.smooth.mono hsub
  have hdOn : ContDiffOn ℝ 1 (deriv p) (Set.Ioo u₁ ρ) :=
    hpOn.deriv_of_isOpen hI (by
      have h : ∀ i : ℕ, (i : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := fun i => by exact_mod_cast le_top
      norm_num
      exact_mod_cast h 2)
  have hpd : ∀ u ∈ Set.Ioo u₁ ρ, HasDerivAt p (deriv p u) u := fun u hu =>
    ((hpOn.contDiffAt (hI.mem_nhds hu)).differentiableAt (by simp)).hasDerivAt
  have hpdd : ∀ u ∈ Set.Ioo u₁ ρ, HasDerivAt (deriv p) (((ρ - u) ^ 4)⁻¹) u := by
    intro u hu
    have hdd : DifferentiableAt ℝ (deriv p) u :=
      (hdOn.contDiffAt (hI.mem_nhds hu)).differentiableAt (by simp)
    have := hdd.hasDerivAt
    have e : deriv (deriv p) u = ((ρ - u) ^ 4)⁻¹ :=
      hrim u (lt_of_le_of_lt (le_max_left _ _) hu.1) hu.2
    rwa [e] at this
  have hw : ∀ u, HasDerivAt (fun u : ℝ => ρ - u) (-1) u := fun u => (hasDerivAt_id u).const_sub ρ
  have hw3 : ∀ u ∈ Set.Ioo u₁ ρ, HasDerivAt (fun u : ℝ => ((ρ - u) ^ 3)⁻¹ / 3) (((ρ - u) ^ 4)⁻¹) u := by
    intro u hu
    have ht : ρ - u ≠ 0 := sub_ne_zero.mpr (ne_of_gt hu.2)
    have h2 := (((hw u).pow 3).fun_inv (pow_ne_zero 3 ht)).div_const 3
    refine h2.congr_deriv ?_
    simp only [Pi.pow_apply]
    push_cast
    field_simp
    try ring
  have hw2 : ∀ u ∈ Set.Ioo u₁ ρ, HasDerivAt (fun u : ℝ => ((ρ - u) ^ 2)⁻¹ / 6) (((ρ - u) ^ 3)⁻¹ / 3) u := by
    intro u hu
    have ht : ρ - u ≠ 0 := sub_ne_zero.mpr (ne_of_gt hu.2)
    have h2 := (((hw u).pow 2).fun_inv (pow_ne_zero 2 ht)).div_const 6
    refine h2.congr_deriv ?_
    simp only [Pi.pow_apply]
    push_cast
    field_simp
    try ring
  have hc : (u₁ + ρ) / 2 ∈ Set.Ioo u₁ ρ := ⟨by linarith, by linarith⟩
  set c := (u₁ + ρ) / 2 with hc_def
  let r : ℝ → ℝ := fun u => deriv p u - ((ρ - u) ^ 3)⁻¹ / 3
  have hr : ∀ u ∈ Set.Ioo u₁ ρ, HasDerivAt r 0 u := by
    intro u hu
    have h3 := (hpdd u hu).fun_sub (hw3 u hu)
    rw [sub_self] at h3
    exact h3
  have hrconst : ∀ u ∈ Set.Ioo u₁ ρ, r u = r c := fun u hu =>
    hI.is_const_of_deriv_eq_zero hIc (fun z hz => (hr z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hr z hz).deriv) hu hc
  let q : ℝ → ℝ := fun u => p u - ((ρ - u) ^ 2)⁻¹ / 6 - r c * u
  have hq : ∀ u ∈ Set.Ioo u₁ ρ, HasDerivAt q 0 u := by
    intro u hu
    have h3 := ((hpd u hu).fun_sub (hw2 u hu)).fun_sub ((hasDerivAt_id u).const_mul (r c))
    have e : deriv p u - ((ρ - u) ^ 3)⁻¹ / 3 - r c * 1 = 0 := by
      have := hrconst u hu
      simp only [r] at this ⊢
      rw [← this]
      ring
    rw [e] at h3
    exact h3
  have hqconst : ∀ u ∈ Set.Ioo u₁ ρ, q u = q c := fun u hu =>
    hI.is_const_of_deriv_eq_zero hIc (fun z hz => (hq z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hq z hz).deriv) hu hc
  refine ⟨u₁, r c, q c, h1, h2, fun u h3 h4 => ?_⟩
  have := hqconst u ⟨h3, h4⟩
  simp only [q] at this ⊢
  linarith
theorem cutoffFactor_contDiffAt (ρ : ℝ) (p : ℝ → ℝ) (hρ : 0 < ρ) (hp : IsCutoff ρ p) (u : ℝ) (hu : 0 < u) :
    ContDiffAt ℝ ∞ (cutoffFactor ρ p) u := by
  obtain ⟨u₁, α, β, h1, h2, hform⟩ := cutoff_eq_near_edge ρ p hρ hp
  by_cases hc : u₁ < u
  · have hev : cutoffFactor ρ p =ᶠ[𝓝 u] fun z => edgeBump (ρ - z) * Real.exp (-(α * z + β)) := by
      filter_upwards [Ioi_mem_nhds hc] with z hz
      by_cases hzρ : z < ρ
      · have e := hform z hz hzρ
        have ht : 0 < ρ - z := by linarith
        simp only [cutoffFactor, hzρ, if_true, edgeBump_of_pos _ ht, ← Real.exp_add]
        congr 1
        rw [e]
        ring
      · have ht : ρ - z ≤ 0 := by linarith
        simp [cutoffFactor, hzρ, edgeBump_of_nonpos _ ht]
    have hs : ContDiffAt ℝ ∞ (fun z => edgeBump (ρ - z) * Real.exp (-(α * z + β))) u := by
      refine ContDiffAt.mul ?_ ?_
      · exact (edgeBump_contDiff.comp (by fun_prop)).contDiffAt
      · exact (Real.contDiff_exp.comp (by fun_prop)).contDiffAt
    exact hs.congr_of_eventuallyEq hev
  · have huρ : u < ρ := lt_of_le_of_lt (not_lt.mp hc) h2
    have hev : cutoffFactor ρ p =ᶠ[𝓝 u] fun z => Real.exp (- p z) := by
      filter_upwards [Iio_mem_nhds huρ] with z hz
      have hz' : z < ρ := hz
      simp [cutoffFactor, hz']
    have hpa : ContDiffAt ℝ ∞ p u := hp.smooth.contDiffAt (Ico_mem_nhds hu huρ)
    exact (Real.contDiff_exp.contDiffAt.comp u hpa.neg).congr_of_eventuallyEq hev
theorem _root_.YangMills.Construction.ColdStepAtMirrorFrames.quaternionCutoffSmoothBounded_holds :
    QuaternionCutoffSmoothBounded := by
  intro ρ p hρ hp
  have hs : ContDiff ℝ ∞ (fun v : ℍ[ℝ] => cutoffFactor ρ p ‖v‖) := by
    rw [contDiff_iff_contDiffAt]
    intro v
    by_cases hv : v = 0
    · subst hv
      have hev : (fun v : ℍ[ℝ] => cutoffFactor ρ p ‖v‖) =ᶠ[𝓝 0] fun _ => 1 := by
        have : Metric.ball (0 : ℍ[ℝ]) (5 * ρ / 8) ∈ 𝓝 (0 : ℍ[ℝ]) := Metric.ball_mem_nhds _ (by positivity)
        filter_upwards [this] with z hz
        have h1 : ‖z‖ < 5 * ρ / 8 := by simpa using hz
        have h2 : ‖z‖ < ρ := by linarith
        simp [cutoffFactor, h2, hp.vanish_small _ (norm_nonneg z) h1.le]
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · exact (cutoffFactor_contDiffAt ρ p hρ hp ‖v‖ (norm_pos_iff.mpr hv)).comp v (contDiffAt_norm ℝ hv)
  refine ⟨hs, fun j => ?_⟩
  have hcs : HasCompactSupport (fun v : ℍ[ℝ] => cutoffFactor ρ p ‖v‖) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℍ[ℝ]) ρ) fun v hv => ?_
    have h1 : ¬ ‖v‖ < ρ := by
      intro h
      exact hv (by simpa using h.le)
    simp [cutoffFactor, h1]
  have hcont : Continuous (iteratedFDeriv ℝ j (fun v : ℍ[ℝ] => cutoffFactor ρ p ‖v‖)) :=
    hs.continuous_iteratedFDeriv (m := j) (by exact_mod_cast le_top)
  exact hcont.bounded_above_of_compact_support (hcs.iteratedFDeriv j)
end YangMills.Construction.QuaternionCutoff
end
