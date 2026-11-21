import YangMills.Construction.TwoPoints.EntireContinuationInTheRotationAngle
import YangMills.Construction.TwoPoints.GrowthBoundsTheNumberOfHarmonics
import Mathlib
set_option autoImplicit false
open Filter Set MeasureTheory
open scoped Topology
noncomputable section
namespace YangMills.Construction.TwoPoints.HarmonicCountFromGrowth
theorem differentiable_of_isHolomorphicVia {F : ℂ → ℂ}
    (hF : Coordinates.ComplexCoordinates.IsHolomorphicVia (Equiv.funUnique (Fin 1) ℂ).symm
      (Equiv.funUnique (Fin 1) ℂ).symm univ F) : Differentiable ℂ F := by
  intro z
  have hsymm : ∀ w : ℂ, (Equiv.funUnique (Fin 1) ℂ).symm w = fun _ => w := by
    intro w
    funext i
    rw [Subsingleton.elim i default]
    simp
  obtain ⟨-, -, hdiff⟩ := hF
  have hmem : (fun _ : Fin 1 => z) ∈ (Equiv.funUnique (Fin 1) ℂ).symm '' univ :=
    ⟨z, mem_univ _, hsymm z⟩
  have hat := (hdiff _ hmem 0).self_of_nhds
  have hcomp := differentiableAt_pi.mp hat 0
  have hshift : DifferentiableAt ℂ (fun ζ : ℂ => F (z + ζ)) 0 := by
    refine hcomp.congr_of_eventuallyEq (Eventually.of_forall fun ζ => ?_)
    simp [Coordinates.ComplexCoordinates.stdBasisVector]
  have hshift' : DifferentiableAt ℂ (fun ζ : ℂ => F (z + ζ)) (z - z) := by
    rw [sub_self]
    exact hshift
  have hback : DifferentiableAt ℂ ((fun ζ : ℂ => F (z + ζ)) ∘ fun w : ℂ => w - z) z :=
    DifferentiableAt.comp (g := fun ζ : ℂ => F (z + ζ)) z hshift' (differentiableAt_id.sub_const z)
  have hfun : ((fun ζ : ℂ => F (z + ζ)) ∘ fun w : ℂ => w - z) = F := by
    funext w
    simp
  rwa [hfun] at hback
def expMode (n : ℤ) (w : ℂ) : ℂ := Complex.exp (-(4 * (n : ℂ) * Complex.I * w))
theorem differentiable_expMode (n : ℤ) : Differentiable ℂ (expMode n) := by
  unfold expMode
  fun_prop
theorem expMode_add_half_pi (n : ℤ) (w : ℂ) :
    expMode n (w + (Real.pi : ℂ) / 2) = expMode n w := by
  unfold expMode
  have harg : -(4 * (n : ℂ) * Complex.I * (w + (Real.pi : ℂ) / 2)) =
      -(4 * (n : ℂ) * Complex.I * w) + ((-n : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
theorem norm_expMode (n : ℤ) (x y : ℝ) :
    ‖expMode n ((x : ℂ) + (y : ℂ) * Complex.I)‖ = Real.exp (4 * (n : ℝ) * y) := by
  unfold expMode
  rw [Complex.norm_exp]
  congr 1
  simp
theorem intervalIntegral_horizontal_line_eq {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    (hper : ∀ w, G (w + (Real.pi : ℂ) / 2) = G w) (y : ℝ) :
    ∫ x in (0 : ℝ)..(Real.pi / 2), G ((x : ℂ) + (y : ℂ) * Complex.I) =
      ∫ x in (0 : ℝ)..(Real.pi / 2), G (x : ℂ) := by
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn G 0
    (((Real.pi / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) hG.differentiableOn
  have hre : (((Real.pi / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I).re = Real.pi / 2 := by simp
  have him : (((Real.pi / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I).im = y := by simp
  rw [hre, him, Complex.zero_re, Complex.zero_im] at hrect
  have hside : ∫ t in (0 : ℝ)..y, G (((Real.pi / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) =
      ∫ t in (0 : ℝ)..y, G (((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    have hpt := hper (((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I)
    rw [← hpt]
    congr 1
    push_cast
    ring
  rw [hside] at hrect
  have hbase : ∫ x in (0 : ℝ)..(Real.pi / 2), G ((x : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) =
      ∫ x in (0 : ℝ)..(Real.pi / 2), G (x : ℂ) := by
    simp
  rw [hbase] at hrect
  have hdiff := sub_eq_zero.mp (by simpa using hrect :
    (∫ x in (0 : ℝ)..(Real.pi / 2), G (x : ℂ)) -
      ∫ x in (0 : ℝ)..(Real.pi / 2), G ((x : ℂ) + (y : ℂ) * Complex.I) = 0)
  exact hdiff.symm
theorem fourierIntegral_eq_zero_of_growth {F : ℂ → ℂ} {Γ : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hF : Differentiable ℂ F) (hper : ∀ w, F (w + (Real.pi : ℂ) / 2) = F w)
    (hb : ∀ x y : ℝ, ‖F ((x : ℂ) + Complex.I * (y : ℂ))‖ ≤ Γ (a * Real.exp (-|y|)))
    (k₀ : ℕ) (hg : Tendsto (fun t : ℝ => t ^ (4 * (k₀ + 1)) * Γ t) (𝓝[>] 0) (𝓝 0))
    (n : ℤ) (hn : (k₀ : ℤ) + 1 ≤ |n|) :
    ∫ x in (0 : ℝ)..(Real.pi / 2), F (x : ℂ) * expMode n (x : ℂ) = 0 := by
  have hnR : (k₀ : ℝ) + 1 ≤ |(n : ℝ)| := by exact_mod_cast hn
  have hG : Differentiable ℂ (fun w => F w * expMode n w) := hF.mul (differentiable_expMode n)
  have hGp : ∀ w, (fun w => F w * expMode n w) (w + (Real.pi : ℂ) / 2) =
      (fun w => F w * expMode n w) w := by
    intro w
    simp only [hper, expMode_add_half_pi]
  have hbound : ∀ Y : ℝ, 0 < Y →
      ‖∫ x in (0 : ℝ)..(Real.pi / 2), F (x : ℂ) * expMode n (x : ℂ)‖ ≤
        (Real.pi / 2) * (a⁻¹ ^ (4 * (k₀ + 1)) *
          ((a * Real.exp (-Y)) ^ (4 * (k₀ + 1)) * Γ (a * Real.exp (-Y)))) := by
    intro Y hY
    obtain ⟨y, hy, hny⟩ : ∃ y : ℝ, |y| = Y ∧ (n : ℝ) * y = -(|(n : ℝ)| * Y) := by
      rcases le_total 0 n with hsign | hsign
      · refine ⟨-Y, by simp [abs_of_pos hY], ?_⟩
        have hsign' : (0 : ℝ) ≤ n := by exact_mod_cast hsign
        rw [abs_of_nonneg hsign']
        ring
      · refine ⟨Y, abs_of_pos hY, ?_⟩
        have hsign' : (n : ℝ) ≤ 0 := by exact_mod_cast hsign
        rw [abs_of_nonpos hsign']
        ring
    have hconst : a⁻¹ ^ (4 * (k₀ + 1)) *
        ((a * Real.exp (-Y)) ^ (4 * (k₀ + 1)) * Γ (a * Real.exp (-Y))) =
        Real.exp (-Y) ^ (4 * (k₀ + 1)) * Γ (a * Real.exp (-Y)) := by
      rw [mul_pow, ← mul_assoc, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ ha.ne', one_pow, one_mul]
    rw [hconst, ← intervalIntegral_horizontal_line_eq hG hGp y]
    have hpt : ∀ x : ℝ, ‖F ((x : ℂ) + (y : ℂ) * Complex.I) *
        expMode n ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
        Real.exp (-Y) ^ (4 * (k₀ + 1)) * Γ (a * Real.exp (-Y)) := by
      intro x
      have hFx : ‖F ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ Γ (a * Real.exp (-Y)) := by
        have hbxy := hb x y
        rw [hy, mul_comm Complex.I] at hbxy
        exact hbxy
      have hexp : Real.exp (4 * (n : ℝ) * y) ≤ Real.exp (-Y) ^ (4 * (k₀ + 1)) := by
        rw [← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        have hlin : 4 * (n : ℝ) * y = -(4 * |(n : ℝ)| * Y) := by
          rw [mul_assoc, hny]
          ring
        rw [hlin]
        push_cast
        nlinarith
      rw [norm_mul, norm_expMode, mul_comm (Real.exp (-Y) ^ _)]
      exact mul_le_mul hFx hexp (Real.exp_pos _).le ((norm_nonneg _).trans hFx)
    have hint := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := Real.pi / 2) (fun x _ => hpt x)
    have hlen : |Real.pi / 2 - 0| = Real.pi / 2 := by
      rw [sub_zero, abs_of_pos (by positivity)]
    rw [hlen] at hint
    rw [mul_comm (Real.pi / 2)]
    exact hint
  have hto : Tendsto (fun Y : ℝ => a * Real.exp (-Y)) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun Y => ?_⟩
    · simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul a
    · exact mul_pos ha (Real.exp_pos _)
  have hlim : Tendsto (fun Y : ℝ => (Real.pi / 2) * (a⁻¹ ^ (4 * (k₀ + 1)) *
      ((a * Real.exp (-Y)) ^ (4 * (k₀ + 1)) * Γ (a * Real.exp (-Y))))) atTop (𝓝 0) := by
    have hc := ((hg.comp hto).const_mul (a⁻¹ ^ (4 * (k₀ + 1)))).const_mul (Real.pi / 2)
    simpa using hc
  have hle : ‖∫ x in (0 : ℝ)..(Real.pi / 2), F (x : ℂ) * expMode n (x : ℂ)‖ ≤ 0 :=
    ge_of_tendsto hlim ((eventually_gt_atTop 0).mono hbound)
  exact norm_le_zero_iff.mp hle
theorem fourier_coe_eq_expMode [Fact (0 < Real.pi / 2)] (m : ℤ) (x : ℝ) :
    (fourier m (x : AddCircle (Real.pi / 2)) : ℂ) = expMode (-m) (x : ℂ) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [fourier_coe_apply]
  unfold expMode
  congr 1
  push_cast
  field_simp
  ring
theorem exists_eq_finite_fourier_sum {F : ℂ → ℂ} (hF : Continuous F)
    (hper : ∀ w, F (w + (Real.pi : ℂ) / 2) = F w) (k₀ : ℕ)
    (hz : ∀ n : ℤ, (k₀ : ℤ) + 1 ≤ |n| →
      ∫ x in (0 : ℝ)..(Real.pi / 2), F (x : ℂ) * expMode n (x : ℂ) = 0) :
    ∃ coeff : ℤ → ℂ, ∀ x : ℝ,
      F (x : ℂ) = ∑ n ∈ Finset.Icc (-(k₀ : ℤ)) k₀, coeff n * expMode (-n) (x : ℂ) := by
  have : Fact (0 < Real.pi / 2) := ⟨by positivity⟩
  have hP : Function.Periodic (fun x : ℝ => F (x : ℂ)) (Real.pi / 2) := by
    intro x
    have hx := hper (x : ℂ)
    simpa using hx
  have hcont : Continuous hP.lift := by
    refine continuous_coinduced_dom.mpr ?_
    exact hF.comp Complex.continuous_ofReal
  let f : C(AddCircle (Real.pi / 2), ℂ) := ⟨hP.lift, hcont⟩
  have hfx : ∀ x : ℝ, f (x : AddCircle (Real.pi / 2)) = F (x : ℂ) := fun x => rfl
  have hzero : ∀ n : ℤ, n ∉ Finset.Icc (-(k₀ : ℤ)) k₀ → fourierCoeff f n = 0 := by
    intro n hn
    have hn' : (k₀ : ℤ) + 1 ≤ |n| := by
      rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
      rcases hn with hlt | hlt
      · exact le_abs.mpr (Or.inr (by omega))
      · exact le_abs.mpr (Or.inl (by omega))
    rw [fourierCoeff_eq_intervalIntegral f n 0]
    have hint : ∫ x in (0 : ℝ)..(0 + Real.pi / 2),
        (fourier (-n) (x : AddCircle (Real.pi / 2)) : ℂ) • f x = 0 := by
      rw [zero_add, ← hz n hn']
      refine intervalIntegral.integral_congr fun x _ => ?_
      have hfm := fourier_coe_eq_expMode (-n) x
      simp only [neg_neg] at hfm
      simp only [smul_eq_mul, hfx, hfm]
      ring
    rw [hint, smul_zero]
  have hsum : Summable (fourierCoeff f) := summable_of_ne_finset_zero hzero
  refine ⟨fourierCoeff f, fun x => ?_⟩
  have hpw := has_pointwise_sum_fourier_series_of_summable hsum (x : AddCircle (Real.pi / 2))
  have hfin : HasSum (fun i => fourierCoeff f i • (fourier i (x : AddCircle (Real.pi / 2)) : ℂ))
      (∑ n ∈ Finset.Icc (-(k₀ : ℤ)) k₀,
        fourierCoeff f n • (fourier n (x : AddCircle (Real.pi / 2)) : ℂ)) :=
    hasSum_sum_of_ne_finset_zero fun n hn => by simp [hzero n hn]
  rw [← hfx, hpw.unique hfin]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [smul_eq_mul, fourier_coe_eq_expMode]
theorem cos_eq_expMode_average (n : ℤ) (w : ℂ) :
    Complex.cos (4 * (n : ℂ) * w) = (expMode n w + expMode (-n) w) / 2 := by
  unfold expMode
  rw [Complex.cos]
  push_cast
  have hfirst : 4 * (n : ℂ) * w * Complex.I = -(4 * -(n : ℂ) * Complex.I * w) := by ring
  have hsecond : -(4 * (n : ℂ) * w) * Complex.I = -(4 * (n : ℂ) * Complex.I * w) := by ring
  rw [hfirst, hsecond, add_comm]
theorem expMode_neg_neg (n : ℤ) (w : ℂ) : expMode (-n) (-w) = expMode n w := by
  unfold expMode
  congr 1
  push_cast
  ring
theorem exists_cos_sum_over_nonneg (b : ℤ → ℝ) (m : ℕ) :
    ∃ c : Fin (m + 1) → ℝ, ∀ w : ℂ,
      ∑ n ∈ Finset.Icc (-(m : ℤ)) m, (b n : ℂ) * Complex.cos (4 * (n : ℂ) * w) =
        ∑ k : Fin (m + 1), (c k : ℂ) * Complex.cos (((4 * (k : ℕ) : ℕ) : ℂ) * w) := by
  induction m with
  | zero =>
    refine ⟨fun _ => b 0, fun w => ?_⟩
    simp
  | succ m ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨Fin.snoc c (b ((m : ℤ) + 1) + b (-((m : ℤ) + 1))), fun w => ?_⟩
    have hIcc : Finset.Icc (-((m + 1 : ℕ) : ℤ)) ((m + 1 : ℕ) : ℤ) =
        insert ((m : ℤ) + 1) (insert (-((m : ℤ) + 1)) (Finset.Icc (-(m : ℤ)) m)) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_insert]
      push_cast
      omega
    have hnotneg : (-((m : ℤ) + 1)) ∉ Finset.Icc (-(m : ℤ)) m := by
      simp only [Finset.mem_Icc]
      omega
    have hnotpos : ((m : ℤ) + 1) ∉ insert (-((m : ℤ) + 1)) (Finset.Icc (-(m : ℤ)) m) := by
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hIcc, Finset.sum_insert hnotpos, Finset.sum_insert hnotneg, hc w,
      Fin.sum_univ_castSucc (n := m + 1)]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
    have hcosneg : Complex.cos (4 * (((-((m : ℤ) + 1) : ℤ)) : ℂ) * w) =
        Complex.cos (4 * ((((m : ℤ) + 1 : ℤ)) : ℂ) * w) := by
      rw [← Complex.cos_neg]
      congr 1
      push_cast
      ring
    have hcast : (((4 * (m + 1) : ℕ)) : ℂ) * w = 4 * ((((m : ℤ) + 1 : ℤ)) : ℂ) * w := by
      push_cast
      ring
    rw [hcosneg, hcast]
    push_cast
    ring
theorem eq_finite_cos_sum {F : ℂ → ℂ} {Γ : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hF : Differentiable ℂ F) (hper : ∀ w, F (w + (Real.pi : ℂ) / 2) = F w)
    (heven : ∀ w, F (-w) = F w) (hreal : ∀ x : ℝ, (F (x : ℂ)).im = 0)
    (hb : ∀ x y : ℝ, ‖F ((x : ℂ) + Complex.I * (y : ℂ))‖ ≤ Γ (a * Real.exp (-|y|)))
    (k₀ : ℕ) (hg : Tendsto (fun t : ℝ => t ^ (4 * (k₀ + 1)) * Γ t) (𝓝[>] 0) (𝓝 0)) :
    ∃ c : Fin (k₀ + 1) → ℝ, ∀ w : ℂ,
      F w = ∑ k : Fin (k₀ + 1), (c k : ℂ) * Complex.cos (((4 * (k : ℕ) : ℕ) : ℂ) * w) := by
  obtain ⟨coeff, hcoeff⟩ := exists_eq_finite_fourier_sum hF.continuous hper k₀
    (fourierIntegral_eq_zero_of_growth ha hF hper hb k₀ hg)
  have hcos : ∀ x : ℝ, F (x : ℂ) =
      ∑ n ∈ Finset.Icc (-(k₀ : ℤ)) k₀, coeff n * Complex.cos (4 * (n : ℂ) * (x : ℂ)) := by
    intro x
    have hrefl : F (x : ℂ) = ∑ n ∈ Finset.Icc (-(k₀ : ℤ)) k₀, coeff n * expMode n (x : ℂ) := by
      have hneg := hcoeff (-x)
      rw [Complex.ofReal_neg, heven] at hneg
      rw [hneg]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [expMode_neg_neg]
    have hhalf : F (x : ℂ) = (F (x : ℂ) + F (x : ℂ)) / 2 := by ring
    rw [hhalf]
    nth_rewrite 1 [hcoeff x]
    rw [hrefl, ← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [cos_eq_expMode_average]
    ring
  have hre : ∀ x : ℝ, F (x : ℂ) = ∑ n ∈ Finset.Icc (-(k₀ : ℤ)) k₀,
      (((coeff n).re : ℝ) : ℂ) * Complex.cos (4 * (n : ℂ) * (x : ℂ)) := by
    intro x
    have hcr : ∀ n : ℤ, Complex.cos (4 * (n : ℂ) * (x : ℂ)) =
        ((Real.cos (4 * (n : ℝ) * x) : ℝ) : ℂ) := by
      intro n
      push_cast
      rfl
    apply Complex.ext
    · rw [hcos x, Complex.re_sum, Complex.re_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [hcr n, Complex.re_mul_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
    · rw [hreal x, Complex.im_sum]
      symm
      refine Finset.sum_eq_zero fun n _ => ?_
      rw [hcr n, ← Complex.ofReal_mul, Complex.ofReal_im]
  obtain ⟨c, hc⟩ := exists_cos_sum_over_nonneg (fun n => (coeff n).re) k₀
  refine ⟨c, ?_⟩
  have hpoly : Differentiable ℂ (fun w : ℂ => ∑ k : Fin (k₀ + 1),
      (c k : ℂ) * Complex.cos (((4 * (k : ℕ) : ℕ) : ℂ) * w)) := by
    fun_prop
  have hseq : Tendsto (fun n : ℕ => (((1 / ((n : ℝ) + 1) : ℝ)) : ℂ)) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have hlim := (Complex.continuous_ofReal.tendsto 0).comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      simp only [Complex.ofReal_zero] at hlim
      exact hlim
    · have hne : (((1 / ((n : ℝ) + 1) : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
      exact hne
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), F z = ∑ k : Fin (k₀ + 1),
      (c k : ℂ) * Complex.cos (((4 * (k : ℕ) : ℕ) : ℂ) * z) := by
    refine hseq.frequently (Eventually.frequently (Eventually.of_forall fun n => ?_))
    rw [hre, ← hc]
  have heq := AnalyticOnNhd.eq_of_frequently_eq (fun z _ => hF.analyticAt z)
    (fun z _ => hpoly.analyticAt z) hfreq
  exact fun w => congrFun heq w
theorem statement_of_entireAngleContinuation (hent : EntireAngleContinuation.Statement) :
    HarmonicCountFromGrowth.Statement := by
  intro St S φ hS hP hφ k₀ hg r hr
  have hcont := (hent St S hS hP φ hφ r hr).1
  have ha : 0 < (2 : ℝ) ^ (-(1 / 2) : ℝ) * r := by positivity
  exact eq_finite_cos_sum ha (differentiable_of_isHolomorphicVia hcont.isAngleFunction.holomorphic)
    hcont.periodic hcont.even hcont.im_ofReal hcont.norm_le k₀ hg
end YangMills.Construction.TwoPoints.HarmonicCountFromGrowth
end
