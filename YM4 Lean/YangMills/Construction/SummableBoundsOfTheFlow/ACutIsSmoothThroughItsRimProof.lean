import YangMills.Construction.ClusterExpansionOfAStep.CutOnTheQuaternionsProof
import YangMills.Construction.ColdStepAtMirrorFrames.RimOfACutProof
import YangMills.Construction.SummableBoundsOfTheFlow.ACutIsSmoothThroughItsRim
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set Filter ColdStepAtMirrorFrames
open scoped Topology
namespace Estimates
namespace CutoffSmooth
def rightRestrict (E : ℝ → ℝ) (v : ℝ) : ℝ := if 0 < v then E v else 0
theorem contDiff_rightRestrict (n : ℕ) : ∀ E : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) E →
    (∀ j : ℕ, iteratedDeriv j E 0 = 0) → ContDiff ℝ n (rightRestrict E) := by apply _root_.YangMills.Construction.QuaternionCutoff.extendByZero_contDiff <;> assumption
theorem iteratedDeriv_mul_comp_sq_eq_zero (j : ℕ) : ∀ a G : ℝ → ℝ,
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G → (∀ m : ℕ, iteratedDeriv m G 0 = 0) →
    iteratedDeriv j (fun v => a v * G (6 * v ^ 2)) 0 = 0 := by
  induction j with
  | zero =>
    intro a G _ _ hf
    have h0 : G 0 = 0 := by simpa using hf 0
    simp [h0]
  | succ j ih =>
    intro a G ha hG hf
    have hq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun v : ℝ => 6 * v ^ 2 := by fun_prop
    have ha' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv a) := ((contDiff_infty_iff_deriv).1 ha).2
    have hG' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv G) := ((contDiff_infty_iff_deriv).1 hG).2
    have hb : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun v : ℝ => a v * (12 * v) :=
      ha.mul (by fun_prop)
    have hder : deriv (fun v => a v * G (6 * v ^ 2)) =
        fun v => deriv a v * G (6 * v ^ 2) + (a v * (12 * v)) * deriv G (6 * v ^ 2) := by
      funext v
      have d1 : HasDerivAt a (deriv a v) v := ((ha.differentiable (by simp)) v).hasDerivAt
      have d2 : HasDerivAt G (deriv G (6 * v ^ 2)) (6 * v ^ 2) :=
        ((hG.differentiable (by simp)) _).hasDerivAt
      have d3 : HasDerivAt (fun v : ℝ => 6 * v ^ 2) (12 * v) v := by
        have := (hasDerivAt_pow 2 v).const_mul (6 : ℝ)
        exact this.congr_deriv (by norm_num; ring)
      have d4 := d1.mul (d2.comp v d3)
      rw [show (fun v => a v * G (6 * v ^ 2)) = a * (G ∘ fun v : ℝ => 6 * v ^ 2) from rfl, d4.deriv]
      simp only [Function.comp]
      ring
    rw [iteratedDeriv_succ', hder]
    have c1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun v => deriv a v * G (6 * v ^ 2) :=
      ha'.mul (hG.comp hq)
    have c2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun v => (a v * (12 * v)) * deriv G (6 * v ^ 2) :=
      hb.mul (hG'.comp hq)
    have e := iteratedDeriv_add (n := j) (x := (0 : ℝ))
      (f := fun v => deriv a v * G (6 * v ^ 2))
      (g := fun v => (a v * (12 * v)) * deriv G (6 * v ^ 2))
      (c1.contDiffAt.of_le (by exact_mod_cast le_top)) (c2.contDiffAt.of_le (by exact_mod_cast le_top))
    have e' : iteratedDeriv j (fun v => deriv a v * G (6 * v ^ 2) +
        (a v * (12 * v)) * deriv G (6 * v ^ 2)) 0 = _ := e
    rw [e', ih _ _ ha' hG hf, ih _ _ hb hG' (fun m => by
      rw [← iteratedDeriv_succ']
      exact hf (m + 1)), add_zero]
theorem iteratedDeriv_expNegInvGlue_zero (m : ℕ) : iteratedDeriv m expNegInvGlue 0 = 0 := by
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) expNegInvGlue := expNegInvGlue.contDiff
  have hcont : Continuous (iteratedDeriv m expNegInvGlue) :=
    hc.continuous_iteratedDeriv m (by exact_mod_cast le_top)
  have hz : ∀ x : ℝ, x < 0 → iteratedDeriv m expNegInvGlue x = 0 := by
    intro x hx
    have ev : expNegInvGlue =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact expNegInvGlue.zero_of_nonpos (le_of_lt hy)
    rw [(Filter.EventuallyEq.iteratedDeriv ev m).self_of_nhds]
    simp
  have ht : Tendsto (iteratedDeriv m expNegInvGlue) (𝓝[<] 0) (𝓝 (iteratedDeriv m expNegInvGlue 0)) :=
    hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hz' : iteratedDeriv m expNegInvGlue =ᶠ[𝓝[<] 0] fun _ => (0 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with x hx using hz x hx
  exact tendsto_nhds_unique (ht.congr' hz') tendsto_const_nhds
def flatBump (v : ℝ) : ℝ := rightRestrict (fun v => 1 * expNegInvGlue (6 * v ^ 2)) v
theorem contDiff_flatBump : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) flatBump := by
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) expNegInvGlue := expNegInvGlue.contDiff
  have hq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun v : ℝ => 6 * v ^ 2 := by fun_prop
  refine contDiff_infty.2 fun n => ?_
  exact contDiff_rightRestrict n _ (contDiff_const.mul (hc.comp hq))
    fun j => iteratedDeriv_mul_comp_sq_eq_zero j _ _ contDiff_const hc
      iteratedDeriv_expNegInvGlue_zero
theorem flatBump_of_pos {v : ℝ} (hv : 0 < v) : flatBump v = Real.exp (-(((v ^ 2)⁻¹) / 6)) := by
  have h : 0 < 6 * v ^ 2 := by positivity
  simp only [flatBump, rightRestrict, hv, if_true, one_mul]
  rw [expNegInvGlue, if_neg (not_le.2 h)]
  congr 1
  field_simp
theorem flatBump_of_nonpos {v : ℝ} (hv : v ≤ 0) : flatBump v = 0 := by
  simp [flatBump, rightRestrict, not_lt.2 hv]
theorem eq_of_hasDerivAt_zero_Ioo {g : ℝ → ℝ} {c d : ℝ} (hd : ∀ u ∈ Ioo c d, HasDerivAt g 0 u)
    {u v : ℝ} (hu : u ∈ Ioo c d) (hv : v ∈ Ioo c d) : g u = g v := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CutoffFactor.eq_of_hasDerivAt_zero_on_Ioo <;> assumption
variable {ρ : ℝ} {p : ℝ → ℝ}
theorem contDiffAt_of_mem (hp : IsCutoff ρ p) {u : ℝ} (h0 : 0 < u) (h1 : u < ρ) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p u :=
  hp.smooth.contDiffAt (Ico_mem_nhds h0 h1)
theorem hasDerivAt_of_mem (hp : IsCutoff ρ p) {u : ℝ} (h0 : 0 < u) (h1 : u < ρ) :
    HasDerivAt p (deriv p u) u := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CutoffFactor.cutoff_hasDerivAt <;> assumption
theorem hasDerivAt_deriv_of_mem (hp : IsCutoff ρ p) {u : ℝ} (h0 : 0 < u) (h1 : u < ρ) :
    HasDerivAt (deriv p) (deriv (deriv p) u) u := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CutoffFactor.cutoff_hasDerivAt_deriv <;> assumption
theorem exists_form_near_rim (hρ : 0 < ρ) (hp : IsCutoff ρ p) : ∃ c A B : ℝ, 0 < c ∧ c < ρ ∧
    ∀ u ∈ Ioo c ρ, p u = ((ρ - u) ^ 2)⁻¹ / 6 + A * u + B := by
  obtain ⟨u₀, hu₀, hrim⟩ := hp.rim_second_deriv
  set c := max u₀ (ρ / 2) with hc
  have hc0 : 0 < c := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have hcρ : c < ρ := max_lt hu₀ (by linarith)
  set um := (c + ρ) / 2 with hum
  have humI : um ∈ Ioo c ρ := ⟨by simp only [hum]; linarith, by simp only [hum]; linarith⟩
  have hi : ∀ u ∈ Ioo c ρ, 0 < ρ - u := fun u hu => by linarith [hu.2]
  have hd3 : ∀ u ∈ Ioo c ρ, HasDerivAt (fun v => ((ρ - v) ^ 3)⁻¹ / 3) (((ρ - u) ^ 4)⁻¹) u := by
    intro u hu
    have h1 : HasDerivAt (fun v : ℝ => (ρ - v) ^ 3) (3 * (ρ - u) ^ 2 * (-1)) u := by
      have := ((hasDerivAt_id u).const_sub ρ).fun_pow 3
      exact HasDerivAt.congr_deriv this (by simp)
    have hne : (ρ - u) ^ 3 ≠ 0 := (pow_pos (hi u hu) 3).ne'
    refine HasDerivAt.congr_deriv ((h1.fun_inv hne).div_const 3) ?_
    have := hi u hu
    field_simp
    try ring
  have hd2 : ∀ u ∈ Ioo c ρ, HasDerivAt (fun v => ((ρ - v) ^ 2)⁻¹ / 6) (((ρ - u) ^ 3)⁻¹ / 3) u := by
    intro u hu
    have h1 : HasDerivAt (fun v : ℝ => (ρ - v) ^ 2) (2 * (ρ - u) * (-1)) u := by
      have := ((hasDerivAt_id u).const_sub ρ).fun_pow 2
      exact HasDerivAt.congr_deriv this (by simp)
    have hne : (ρ - u) ^ 2 ≠ 0 := (pow_pos (hi u hu) 2).ne'
    refine HasDerivAt.congr_deriv ((h1.fun_inv hne).div_const 6) ?_
    have := hi u hu
    field_simp
    try ring
  set A := deriv p um - ((ρ - um) ^ 3)⁻¹ / 3 with hA
  have hfirst : ∀ u ∈ Ioo c ρ, deriv p u = ((ρ - u) ^ 3)⁻¹ / 3 + A := by
    intro u hu
    have hz : ∀ v ∈ Ioo c ρ, HasDerivAt (fun w => deriv p w - ((ρ - w) ^ 3)⁻¹ / 3) 0 v := by
      intro v hv
      have h1 := hasDerivAt_deriv_of_mem hp (hc0.trans hv.1) hv.2
      have e : deriv (deriv p) v = ((ρ - v) ^ 4)⁻¹ :=
        hrim v (lt_of_le_of_lt (le_max_left _ _) hv.1) hv.2
      rw [e] at h1
      exact HasDerivAt.congr_deriv (h1.sub (hd3 v hv)) (by ring)
    have := eq_of_hasDerivAt_zero_Ioo hz hu humI
    simp only [hA]
    linarith
  set B := p um - ((ρ - um) ^ 2)⁻¹ / 6 - A * um with hB
  refine ⟨c, A, B, hc0, hcρ, fun u hu => ?_⟩
  have hz : ∀ v ∈ Ioo c ρ, HasDerivAt (fun w => p w - ((ρ - w) ^ 2)⁻¹ / 6 - A * w) 0 v := by
    intro v hv
    have h1 := hasDerivAt_of_mem hp (hc0.trans hv.1) hv.2
    rw [hfirst v hv] at h1
    have h2 : HasDerivAt (fun w : ℝ => A * w) A v := by
      simpa using (hasDerivAt_id v).const_mul A
    exact HasDerivAt.congr_deriv ((h1.sub (hd2 v hv)).sub h2) (by ring)
  have := eq_of_hasDerivAt_zero_Ioo hz hu humI
  simp only [hB]
  linarith
end CutoffSmooth
open CutoffSmooth in
theorem cutoffWeight_contDiff : CutoffWeightContDiff := by
  intro ρ p hρ hp
  obtain ⟨c, A, B, hc0, hcρ, hform⟩ := exists_form_near_rim hρ hp
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases h1 : x < 5 * ρ / 8
  · refine (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds h1] with u hu
    have hu' : u < 5 * ρ / 8 := hu
    have hm : max u 0 ≤ 5 * ρ / 8 := max_le hu'.le (by positivity)
    have hlt : max u 0 < ρ := by linarith
    simp [cutoffFactor, hlt, hp.vanish_small _ (le_max_right _ _) hm]
  · rw [not_lt] at h1
    by_cases h2 : x < ρ
    · have hx0 : 0 < x := by linarith
      have hsm : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => Real.exp (- p u)) x :=
        (contDiffAt_of_mem hp hx0 h2).neg.exp
      refine hsm.congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds hx0 h2] with u hu
      simp [cutoffFactor, max_eq_left hu.1.le, hu.2]
    · rw [not_lt] at h2
      have hcx : c < x := lt_of_lt_of_le hcρ h2
      have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun u => Real.exp (-(A * u + B)) * flatBump (ρ - u)) :=
        (by fun_prop : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun u => Real.exp (-(A * u + B))).mul
          (contDiff_flatBump.comp (by fun_prop))
      refine hsm.contDiffAt.congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hcx] with u hu
      have hu0 : 0 < u := hc0.trans hu
      by_cases h3 : u < ρ
      · have hm : max u 0 = u := max_eq_left hu0.le
        rw [show cutoffFactor ρ p (max u 0) = Real.exp (- p u) by simp [cutoffFactor, hm, h3],
          flatBump_of_pos (by linarith), hform u ⟨hu, h3⟩, ← Real.exp_add]
        congr 1
        ring
      · have hm : max u 0 = u := max_eq_left hu0.le
        rw [show cutoffFactor ρ p (max u 0) = 0 by simp [cutoffFactor, hm, h3],
          flatBump_of_nonpos (by linarith), mul_zero]
end Estimates
end YangMills.Construction
end
