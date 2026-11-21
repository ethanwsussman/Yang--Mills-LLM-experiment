import YangMills.Construction.RotationInvariance.FinitelyManyHarmonicsOnPencils
import YangMills.Construction.RotationInvariance.InvariantTwoPointFunctionHasTopFrequencyZeroProof
import Mathlib
set_option autoImplicit false
open Complex (I)
open scoped Topology
noncomputable section
namespace YangMills.Construction
open RealPlane ForwardTube Filter
open Matrices.GroupLieProduct.Subspaces.AnalyticCalculus (scalarEquiv)
namespace EuclideanFunctionals.PencilHarmonics
section QuarterPeriodic
variable {f : ℂ → ℂ}
theorem differentiable_of_entire (hf : Entire f) : Differentiable ℂ f := by apply _root_.YangMills.Construction.EuclideanFunctionals.TwoPointTopFrequency.differentiable_of_entire <;> assumption
theorem exp_quarter_period (n : ℤ) (z : ℂ) :
    Complex.exp (-(4 * I * (n : ℂ) * (z + ((Real.pi / 2 : ℝ) : ℂ)))) =
      Complex.exp (-(4 * I * (n : ℂ) * z)) := by
  have key : -(4 * I * (n : ℂ) * (z + ((Real.pi / 2 : ℝ) : ℂ))) =
      -(4 * I * (n : ℂ) * z) + ((-n : ℤ) : ℂ) * (2 * Real.pi * I) := by
    push_cast
    ring
  rw [key, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
theorem intervalIntegral_horizontal_line_eq (hf : Differentiable ℂ f)
    (hperiod : (fun w : ℂ => f (w + ((Real.pi / 2 : ℝ) : ℂ))) = f) (n : ℤ) (s : ℝ) :
    (∫ t : ℝ in (0 : ℝ)..(Real.pi / 2),
        f ((t : ℂ) + I * (s : ℂ)) * Complex.exp (-(4 * I * (n : ℂ) * ((t : ℂ) + I * (s : ℂ))))) =
      ∫ t : ℝ in (0 : ℝ)..(Real.pi / 2), f (t : ℂ) * Complex.exp (-(4 * I * (n : ℂ) * (t : ℂ))) := by
  set g : ℂ → ℂ := fun z => f z * Complex.exp (-(4 * I * (n : ℂ) * z)) with hgdef
  have hgdiff : Differentiable ℂ g := hf.mul (by fun_prop)
  have hgper : ∀ z, g (z + ((Real.pi / 2 : ℝ) : ℂ)) = g z := fun z => by
    simp only [hgdef]
    rw [exp_quarter_period, congrFun hperiod z]
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn g 0
    (((Real.pi / 2 : ℝ) : ℂ) + (s : ℂ) * I) hgdiff.differentiableOn
  have hre : (((Real.pi / 2 : ℝ) : ℂ) + (s : ℂ) * I).re = Real.pi / 2 := by simp
  have him : (((Real.pi / 2 : ℝ) : ℂ) + (s : ℂ) * I).im = s := by simp
  rw [hre, him] at hrect
  simp only [Complex.zero_re, Complex.zero_im, Complex.ofReal_zero, zero_mul, add_zero,
    zero_add] at hrect
  have hvert : (∫ y : ℝ in (0 : ℝ)..s, g (((Real.pi / 2 : ℝ) : ℂ) + (y : ℂ) * I)) =
      ∫ y : ℝ in (0 : ℝ)..s, g ((y : ℂ) * I) :=
    intervalIntegral.integral_congr fun y _ => by
      show g (((Real.pi / 2 : ℝ) : ℂ) + (y : ℂ) * I) = g ((y : ℂ) * I)
      rw [add_comm]
      exact hgper _
  rw [hvert] at hrect
  have hhor : (∫ t : ℝ in (0 : ℝ)..(Real.pi / 2),
        f ((t : ℂ) + I * (s : ℂ)) * Complex.exp (-(4 * I * (n : ℂ) * ((t : ℂ) + I * (s : ℂ))))) =
      ∫ t : ℝ in (0 : ℝ)..(Real.pi / 2), g ((t : ℂ) + (s : ℂ) * I) :=
    intervalIntegral.integral_congr fun t _ => by
      simp only [hgdef, mul_comm I (s : ℂ)]
  rw [hhor]
  simp only [smul_eq_mul] at hrect
  linear_combination -hrect
theorem norm_exp_horizontal_line (n : ℤ) (t s : ℝ) :
    ‖Complex.exp (-(4 * I * (n : ℂ) * ((t : ℂ) + I * (s : ℂ))))‖ =
      Real.exp (4 * (n : ℝ) * s) := by
  have key : -(4 * I * (n : ℂ) * ((t : ℂ) + I * (s : ℂ))) =
      ((4 * (n : ℝ) * s : ℝ) : ℂ) + ((-(4 * (n : ℝ) * t) : ℝ) : ℂ) * I := by
    push_cast
    linear_combination (-(4 * (n : ℂ) * (s : ℂ))) * Complex.I_sq
  rw [Complex.norm_exp, key]
  simp
theorem norm_le_of_horizontal_integral {c : ℂ} {n : ℤ} {s : ℝ}
    (hc : c = ((2 / Real.pi : ℝ) : ℂ) *
      ∫ t : ℝ in (0 : ℝ)..(Real.pi / 2),
        f ((t : ℂ) + I * (s : ℂ)) * Complex.exp (-(4 * I * (n : ℂ) * ((t : ℂ) + I * (s : ℂ)))))
    (hbdd : BddAbove (Set.range fun t : ℝ => ‖f ((t : ℂ) + I * (s : ℂ))‖)) :
    ‖c‖ ≤ Real.exp (4 * (n : ℝ) * s) * ⨆ t : ℝ, ‖f ((t : ℂ) + I * (s : ℂ))‖ := by
  set B := ⨆ t : ℝ, ‖f ((t : ℂ) + I * (s : ℂ))‖ with hB
  have hest := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ))
    (b := Real.pi / 2) (C := B * Real.exp (4 * (n : ℝ) * s))
    (f := fun t : ℝ =>
      f ((t : ℂ) + I * (s : ℂ)) * Complex.exp (-(4 * I * (n : ℂ) * ((t : ℂ) + I * (s : ℂ)))))
    (fun t _ => by
      rw [norm_mul, norm_exp_horizontal_line]
      exact mul_le_mul_of_nonneg_right (le_ciSup hbdd t) (Real.exp_pos _).le)
  have hlen : |Real.pi / 2 - 0| = Real.pi / 2 := by
    rw [sub_zero, abs_of_pos (by positivity)]
  rw [hlen] at hest
  rw [hc, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc 2 / Real.pi * _ ≤ 2 / Real.pi * (B * Real.exp (4 * (n : ℝ) * s) * (Real.pi / 2)) :=
        mul_le_mul_of_nonneg_left hest (by positivity)
    _ = Real.exp (4 * (n : ℝ) * s) * B := by
        field_simp
theorem eq_zero_of_growth_bounds {c : ℂ} {n : ℤ} {C E : ℝ}
    (hc : ∀ s : ℝ, ‖c‖ ≤ Real.exp (4 * (n : ℝ) * s) * ⨆ t : ℝ, ‖f ((t : ℂ) + I * (s : ℂ))‖)
    (hgrowth : ∀ t s : ℝ, ‖f ((t : ℂ) + I * (s : ℂ))‖ ≤ C * Real.exp (E * |s|))
    (hE : E < 4 * |(n : ℝ)|) : c = 0 := by
  set δ := 4 * |(n : ℝ)| - E with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hsup : ∀ s : ℝ, (⨆ t : ℝ, ‖f ((t : ℂ) + I * (s : ℂ))‖) ≤ C * Real.exp (E * |s|) :=
    fun s => ciSup_le fun t => hgrowth t s
  have hdecay : ∀ r : ℝ, 0 ≤ r → ‖c‖ ≤ C * Real.exp (-(δ * r)) := by
    intro r hr
    have step : ∀ s : ℝ, |s| = r → 4 * (n : ℝ) * s = -(4 * |(n : ℝ)| * r) →
        ‖c‖ ≤ C * Real.exp (-(δ * r)) := by
      intro s hs hn
      refine (hc s).trans ?_
      calc Real.exp (4 * (n : ℝ) * s) * ⨆ t : ℝ, ‖f ((t : ℂ) + I * (s : ℂ))‖
          ≤ Real.exp (4 * (n : ℝ) * s) * (C * Real.exp (E * |s|)) :=
            mul_le_mul_of_nonneg_left (hsup s) (Real.exp_pos _).le
        _ = C * Real.exp (-(δ * r)) := by
            rw [hs, hn, hδ, mul_left_comm, ← Real.exp_add]
            congr 2
            ring
    rcases le_total 0 (n : ℝ) with hn | hn
    · refine step (-r) (by rw [abs_neg, abs_of_nonneg hr]) ?_
      rw [abs_of_nonneg hn]
      ring
    · refine step r (abs_of_nonneg hr) ?_
      rw [abs_of_nonpos hn]
      ring
  have hlim : Tendsto (fun r : ℝ => C * Real.exp (-(δ * r))) atTop (𝓝 (C * 0)) := by
    refine Tendsto.const_mul C (Real.tendsto_exp_atBot.comp ?_)
    exact tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hδpos)
  rw [mul_zero] at hlim
  have hle : ‖c‖ ≤ 0 :=
    ge_of_tendsto hlim ((eventually_ge_atTop 0).mono fun r hr => hdecay r hr)
  exact norm_le_zero_iff.mp hle
theorem eq_finset_sum_of_real (hf : Continuous f)
    (hperiod : (fun w : ℂ => f (w + ((Real.pi / 2 : ℝ) : ℂ))) = f) {c : ℤ → ℂ}
    (hc : ∀ n, c n = ((2 / Real.pi : ℝ) : ℂ) *
      ∫ t : ℝ in (0 : ℝ)..(Real.pi / 2), f (t : ℂ) * Complex.exp (-(4 * I * (n : ℂ) * (t : ℂ))))
    (F : Finset ℤ) (hF : ∀ n ∉ F, c n = 0) (x : ℝ) :
    f (x : ℂ) = ∑ n ∈ F, c n * Complex.exp (4 * I * (n : ℂ) * (x : ℂ)) := by
  have : Fact (0 < Real.pi / 2) := ⟨by positivity⟩
  have hp : Function.Periodic (fun t : ℝ => f (t : ℂ)) (Real.pi / 2) := fun t => by
    have := congrFun hperiod (t : ℂ)
    simpa using this
  let g : C(AddCircle (Real.pi / 2), ℂ) :=
    ⟨hp.lift, continuous_coinduced_dom.mpr (by
      exact (hf.comp Complex.continuous_ofReal))⟩
  have hgx : ∀ t : ℝ, g (t : AddCircle (Real.pi / 2)) = f (t : ℂ) := fun t => hp.lift_coe t
  have hchar : ∀ (k : ℤ) (t : ℝ), fourier k (t : AddCircle (Real.pi / 2)) =
      Complex.exp (4 * I * (k : ℂ) * (t : ℂ)) := by
    intro k t
    rw [fourier_coe_apply]
    congr 1
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp
    ring
  have hcoeff : ∀ k, fourierCoeff g k = c k := by
    intro k
    rw [fourierCoeff_eq_intervalIntegral _ k 0, hc k, zero_add]
    have hint : (∫ t : ℝ in (0 : ℝ)..(Real.pi / 2),
          fourier (-k) (t : AddCircle (Real.pi / 2)) • g (t : AddCircle (Real.pi / 2))) =
        ∫ t : ℝ in (0 : ℝ)..(Real.pi / 2),
          f (t : ℂ) * Complex.exp (-(4 * I * (k : ℂ) * (t : ℂ))) :=
      intervalIntegral.integral_congr fun t _ => by
        show fourier (-k) (t : AddCircle (Real.pi / 2)) • g (t : AddCircle (Real.pi / 2)) = _
        rw [hgx, hchar, smul_eq_mul, mul_comm]
        congr 2
        push_cast
        ring
    rw [hint, Complex.real_smul]
    congr 2
    rw [one_div, inv_div]
  have hsumm : Summable (fourierCoeff g) :=
    summable_of_ne_finset_zero (s := F) fun n hn => by rw [hcoeff]; exact hF n hn
  have e1 := has_pointwise_sum_fourier_series_of_summable hsumm (x : AddCircle (Real.pi / 2))
  have e2 : HasSum (fun i => fourierCoeff g i • fourier i (x : AddCircle (Real.pi / 2)))
      (∑ n ∈ F, fourierCoeff g n • fourier n (x : AddCircle (Real.pi / 2))) :=
    hasSum_sum_of_ne_finset_zero fun n hn => by
      rw [hcoeff, hF n hn, zero_smul]
  rw [← hgx, e1.unique e2]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [hcoeff, hchar, smul_eq_mul]
theorem eq_of_eq_real {g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (heq : ∀ x : ℝ, f (x : ℂ) = g (x : ℂ)) (z : ℂ) : f z = g z := by
  have hfreq : ∃ᶠ w in 𝓝[≠] (0 : ℂ), f w = g w := by
    have ht : Tendsto (fun k : ℕ => (((1 / ((k : ℝ) + 1) : ℝ)) : ℂ)) atTop (𝓝[≠] (0 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun k => ?_⟩
      · have := (Complex.continuous_ofReal.tendsto 0).comp
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
        simpa [Function.comp_def] using this
      · have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact_mod_cast this.ne'
    exact ht.frequently (Frequently.of_forall fun k => heq _)
  have hall := (hf.differentiableOn.analyticOnNhd isOpen_univ).eqOn_of_preconnected_of_frequently_eq
    (hg.differentiableOn.analyticOnNhd isOpen_univ) isPreconnected_univ (Set.mem_univ 0) hfreq
  exact hall (Set.mem_univ z)
theorem coeff_neg_eq_conj (hreal : ∀ t : ℝ, (f (t : ℂ)).im = 0) (n : ℤ) :
    ((2 / Real.pi : ℝ) : ℂ) *
        (∫ t : ℝ in (0 : ℝ)..(Real.pi / 2),
          f (t : ℂ) * Complex.exp (-(4 * I * ((-n : ℤ) : ℂ) * (t : ℂ)))) =
      (starRingEnd ℂ) (((2 / Real.pi : ℝ) : ℂ) *
        ∫ t : ℝ in (0 : ℝ)..(Real.pi / 2),
          f (t : ℂ) * Complex.exp (-(4 * I * (n : ℂ) * (t : ℂ)))) := by
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  rw [map_mul, Complex.conj_ofReal, intervalIntegral.integral_of_le hpi,
    intervalIntegral.integral_of_le hpi, ← integral_conj]
  congr 1
  refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun t => ?_)
  show f (t : ℂ) * Complex.exp (-(4 * I * ((-n : ℤ) : ℂ) * (t : ℂ))) =
    (starRingEnd ℂ) (f (t : ℂ) * Complex.exp (-(4 * I * (n : ℂ) * (t : ℂ))))
  rw [map_mul, ← Complex.exp_conj, Complex.conj_eq_iff_im.mpr (hreal t)]
  congr 2
  simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal, map_intCast, map_ofNat]
  push_cast
  ring
end QuarterPeriodic
section Translation
variable {q : ℕ}
theorem successiveDifferences_add_const (y : Fin (q + 1) → RealPlane) (u : RealPlane) :
    successiveDifferences (fun i => y i + u) = successiveDifferences y := by
  funext i
  simp [successiveDifferences]
theorem isAngleFunction_add_const (S : ConnFamily) (θ : openingAngles) (y : Fin (q + 1) → RealPlane)
    (u : RealPlane) (φ : Fin (q + 1) → realLabels) :
    IsAngleFunction S θ (fun i => y i + u) φ = IsAngleFunction S θ y φ := by
  have hdiff : planeTupleDiffs (fun i => y i + u) = planeTupleDiffs y := by
    unfold planeTupleDiffs
    rw [successiveDifferences_add_const]
  funext b
  refine propext ⟨fun hb => ⟨hb.entire, fun υ t s hts => ?_⟩,
    fun hb => ⟨hb.entire, fun υ t s hts => ?_⟩⟩
  · rw [hb.apply_eq_planeKernel υ t s hts, hdiff]
  · rw [hb.apply_eq_planeKernel υ t s hts, hdiff]
theorem angleFunction_add_const (S : ConnFamily) (θ : openingAngles) (y : Fin (q + 1) → RealPlane)
    (u : RealPlane) (φ : Fin (q + 1) → realLabels) :
    angleFunction S θ (fun i => y i + u) φ = angleFunction S θ y φ := by
  unfold angleFunction
  rw [isAngleFunction_add_const]
end Translation
theorem holds (hangle : AngleFunctionOnPencil.Holds) : Holds := by
  intro m S d q hq y hy φ
  obtain ⟨-, hfun, -, hvals, -, hgrow⟩ := hangle m S d q hq y hy φ
  obtain ⟨-, -, hper, hreal⟩ := hvals
  have hf : Differentiable ℂ (angleFunction S d.angle y φ) :=
    differentiable_of_entire hfun.entire
  have hg := fun t s => (hgrow t s).1.trans (hgrow t s).2
  have hc : ∀ n, angleHarmonic S d.angle y φ n = ((2 / Real.pi : ℝ) : ℂ) *
      ∫ t : ℝ in (0 : ℝ)..(Real.pi / 2),
        angleFunction S d.angle y φ (t : ℂ) *
          Complex.exp (-(4 * I * (n : ℂ) * (t : ℂ))) := fun _ => rfl
  have hline : ∀ (n : ℤ) (s : ℝ), angleHarmonic S d.angle y φ n =
      ((2 / Real.pi : ℝ) : ℂ) *
        ∫ t : ℝ in (0 : ℝ)..(Real.pi / 2),
          angleFunction S d.angle y φ ((t : ℂ) + I * (s : ℂ)) *
            Complex.exp (-(4 * I * (n : ℂ) * ((t : ℂ) + I * (s : ℂ)))) := fun n s => by
    rw [intervalIntegral_horizontal_line_eq hf hper, hc]
  have hbdd : ∀ s : ℝ, BddAbove (Set.range fun t : ℝ =>
      ‖angleFunction S d.angle y φ ((t : ℂ) + I * (s : ℂ))‖) := fun s =>
    ⟨_, by rintro _ ⟨t, rfl⟩; exact hg t s⟩
  have hnorm := fun (n : ℤ) (s : ℝ) => norm_le_of_horizontal_integral (hline n s) (hbdd s)
  have hvanish : VanishAbove d y φ := by
    intro n hn
    refine eq_zero_of_growth_bounds (f := angleFunction S d.angle y φ) (hnorm n) hg ?_
    unfold harmonicBound at hn
    linarith
  refine ⟨hvanish, ?_, ?_, ?_, hbdd, fun n s => ⟨hline n s, hnorm n s⟩⟩
  · intro t s
    have hF : ∀ n ∉ Finset.Icc (-⌊harmonicBound d q⌋) ⌊harmonicBound d q⌋,
        angleHarmonic S d.angle y φ n = 0 := by
      intro n hn
      apply hvanish n
      rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
      rcases hn with h | h
      · have h' : ⌊harmonicBound d q⌋ < -n := by omega
        have h'' := Int.floor_lt.mp h'
        push_cast at h''
        exact h''.trans_le (neg_le_abs _)
      · exact (Int.floor_lt.mp h).trans_le (le_abs_self _)
    exact eq_of_eq_real
      (g := fun z => ∑ n ∈ Finset.Icc (-⌊harmonicBound d q⌋) ⌊harmonicBound d q⌋,
        angleHarmonic S d.angle y φ n * Complex.exp (4 * I * (n : ℂ) * z))
      hf (by fun_prop)
      (fun x => eq_finset_sum_of_real hf.continuous hper hc _ hF x) _
  · intro u
    refine ⟨?_, fun n => ?_⟩
    · show ∀ i, successiveDifferences (fun i => y i + u) i ∈ coneSector d.angle
      rw [successiveDifferences_add_const]
      exact hy
    · simp only [angleHarmonic, angleFunction_add_const]
  · intro n
    have h := coeff_neg_eq_conj hreal n
    rw [← hc, ← hc] at h
    exact h
end EuclideanFunctionals.PencilHarmonics
end YangMills.Construction
end
