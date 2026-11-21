import YangMills.Construction.PeriodicOperators.RealLogarithmOfTheDeterminantOfLinearMaps
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology ContDiff
noncomputable section
namespace YangMills.Construction.PeriodicOperators.RealLogDet
open YangMills.Construction.Coordinates
open YangMills.Construction.Coordinates.ComplexCoordinates (derivAlongLine secondDeriv)
open YangMills.Construction.Coordinates.ComplexCoordinates.LogDetSecondDeriv
  (seriesLog scalarSecondDeriv asLine)
open YangMills.Construction.PeriodicOperators.LogDetOfMaps (detRatio logDetRatio)
theorem seriesLog_ofReal {x : ℝ} (hx : ‖(x : ℂ) - 1‖ < 1) :
    seriesLog (x : ℂ) = (Real.log x : ℂ) := by
  have hpos : 0 < x := by
    have habs : |x - 1| < 1 := by
      have e : ((x : ℂ) - 1) = ((x - 1 : ℝ) : ℂ) := by push_cast; ring
      rw [e, Complex.norm_real] at hx
      simpa using hx
    have := (abs_lt.mp habs).1
    linarith
  have hsum := Complex.hasSum_taylorSeries_log hx
  have hsum' := (hasSum_nat_add_iff' 1).mpr hsum
  have hcl : Complex.log (1 + ((x : ℂ) - 1)) = (Real.log x : ℂ) := by
    rw [Complex.ofReal_log hpos.le]
    congr 1
    ring
  rw [hcl] at hsum'
  unfold seriesLog
  have := hsum'.tsum_eq
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, div_zero, sub_zero] at this
  rw [← this]
  refine tsum_congr fun n => ?_
  have hsgn : (-1 : ℂ) ^ (n + 1 + 1) = (-1) ^ n := by
    rw [pow_succ, pow_succ]
    ring
  rw [hsgn]
theorem ofReal_re_eq_of_im_eq_zero {w : ℂ} (hw : w.im = 0) : ((w.re : ℝ) : ℂ) = w :=
  Complex.ext (by simp) (by simp [hw])
theorem det_im_eq_zero_of_real_entries {ι : Type} [Finite ι] (A : Module.End ℂ (ι → ℂ))
    (hA : ∀ i j, (linearMapEntry A i j).im = 0) : (LinearMap.det A).im = 0 := by
  classical
  have := Fintype.ofFinite ι
  let R : Matrix ι ι ℝ := fun i j => (linearMapEntry A i j).re
  have hR : LinearMap.toMatrix' A = Complex.ofRealHom.mapMatrix R := by
    ext i j
    have hij : LinearMap.toMatrix' A i j = linearMapEntry A i j := by
      rw [LinearMap.toMatrix'_apply]
      unfold linearMapEntry
      congr 1
    have hmap : Complex.ofRealHom.mapMatrix R i j = (((linearMapEntry A i j).re : ℝ) : ℂ) := rfl
    rw [hij, hmap]
    exact (ofReal_re_eq_of_im_eq_zero (hA i j)).symm
  rw [← LinearMap.det_toMatrix', hR, ← RingHom.map_det]
  simp
theorem detRatio_mul_det {ι : Type} {n : ℕ} (M : ComplexCoordinates n → Module.End ℂ (ι → ℂ))
    (hM : IsUnit (M 0)) (z : ComplexCoordinates n) :
    detRatio M z * LinearMap.det (M 0) = LinearMap.det (M z) := by
  have hinv : LinearMap.det (Ring.inverse (M 0)) * LinearMap.det (M 0) = 1 := by
    rw [← map_mul, Ring.inverse_mul_cancel _ hM, map_one]
  unfold detRatio
  rw [map_mul]
  calc LinearMap.det (Ring.inverse (M 0)) * LinearMap.det (M z) * LinearMap.det (M 0)
      = (LinearMap.det (Ring.inverse (M 0)) * LinearMap.det (M 0)) * LinearMap.det (M z) := by ring
    _ = LinearMap.det (M z) := by rw [hinv, one_mul]
theorem logDetRatio_eq_realLogAbsDetDiff {ι : Type} [Finite ι] {n : ℕ}
    (M : ComplexCoordinates n → Module.End ℂ (ι → ℂ)) (hM : IsUnit (M 0))
    (hM0 : ∀ i j, (linearMapEntry (M 0) i j).im = 0) (v : Fin n → ℝ)
    (hMv : ∀ i j, (linearMapEntry (M (realEmbed v)) i j).im = 0)
    (hnear : ‖detRatio M (realEmbed v) - 1‖ < 1) :
    LinearMap.det (M (realEmbed v)) ≠ 0 ∧
      logDetRatio M (realEmbed v) = (realLogAbsDetDiff M v : ℂ) := by
  have hav := ofReal_re_eq_of_im_eq_zero (det_im_eq_zero_of_real_entries _ hMv)
  have hbv := ofReal_re_eq_of_im_eq_zero (det_im_eq_zero_of_real_entries _ hM0)
  set p : ℝ := (LinearMap.det (M (realEmbed v))).re with hp
  set q : ℝ := (LinearMap.det (M 0)).re with hq
  have hq0 : q ≠ 0 := by
    intro hz
    have := (hM.map (LinearMap.det : Module.End ℂ (ι → ℂ) →* ℂ)).ne_zero
    rw [← hbv, hz] at this
    simp at this
  have hratio : detRatio M (realEmbed v) = ((p / q : ℝ) : ℂ) := by
    have h := detRatio_mul_det M hM (realEmbed v)
    rw [← hav, ← hbv] at h
    have hqc : (q : ℂ) ≠ 0 := by exact_mod_cast hq0
    push_cast
    rw [eq_div_iff hqc]
    exact h
  rw [hratio] at hnear
  have hlog := seriesLog_ofReal hnear
  have hpq : 0 < p / q := by
    have habs : |p / q - 1| < 1 := by
      have e : (((p / q : ℝ) : ℂ) - 1) = ((p / q - 1 : ℝ) : ℂ) := by push_cast; ring
      rw [e, Complex.norm_real] at hnear
      simpa using hnear
    have := (abs_lt.mp habs).1
    linarith
  have hp0 : p ≠ 0 := by
    intro hz
    rw [hz] at hpq
    simp at hpq
  refine ⟨?_, ?_⟩
  · rw [← hav]
    exact_mod_cast hp0
  · unfold logDetRatio
    rw [hratio, hlog]
    unfold realLogAbsDetDiff
    rw [← hav, ← hbv, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      Real.log_abs, Real.log_abs, Real.log_div hp0 hq0]
def realCLM (n : ℕ) : (Fin n → ℝ) →L[ℝ] ComplexCoordinates n :=
  ContinuousLinearMap.pi fun j => Complex.ofRealCLM.comp (ContinuousLinearMap.proj j)
theorem realCLM_apply {n : ℕ} (v : Fin n → ℝ) : realCLM n v = realEmbed v := rfl
theorem eq_realCLM_add_I_smul {n : ℕ} (z : ComplexCoordinates n) :
    z = realCLM n (fun j => (z j).re) + Complex.I • realCLM n (fun j => (z j).im) := by
  funext j
  simp only [realCLM_apply, realEmbed, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [mul_comm]
  exact (Complex.re_add_im (z j)).symm
theorem claim_holds (hP : YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hH : YangMills.Construction.SeparatedFrame.HolomorphicDerivatives.Claim) : Claim := by
  intro ι _ n U M hU hU0 hM hdisc hhol hre
  have hC : ContDiffOn ℝ ∞ (asLine (logDetRatio M)) U :=
    ((hP.1 n U hU).1 1 (asLine (logDetRatio M)) hhol).2.1
  obtain ⟨hDiff, ⟨Q, hQ⟩, -⟩ := (hH n 1 U (asLine (logDetRatio M)) hhol).2 0 hU0
  set F := asLine (logDetRatio M) with hFdef
  set e := realCLM n with he
  set g : (Fin n → ℝ) → ℝ := realLogAbsDetDiff M with hg
  have he0 : e 0 = 0 := map_zero e
  have hzero : realEmbed (0 : Fin n → ℝ) = 0 := by
    funext j
    simp [realEmbed]
  have hre0 : ∀ i j, (linearMapEntry (M 0) i j).im = 0 := by
    have := hre.self_of_nhds
    rwa [hzero] at this
  have hUnear : ∀ᶠ v : Fin n → ℝ in 𝓝 0, e v ∈ U :=
    e.continuous.continuousAt.eventually (by rw [he0]; exact hU.mem_nhds hU0)
  have hgood : ∀ᶠ v : Fin n → ℝ in 𝓝 0, e v ∈ U ∧
      LinearMap.det (M (realEmbed v)) ≠ 0 ∧
      logDetRatio M (realEmbed v) = (g v : ℂ) := by
    filter_upwards [hUnear, hre] with v hv hr
    exact ⟨hv, logDetRatio_eq_realLogAbsDetDiff M hM hre0 v hr (hdisc _ hv)⟩
  let π : ComplexCoordinates 1 →L[ℝ] ℂ := ContinuousLinearMap.proj 0
  let φ : (Fin n → ℝ) → ℂ := fun v => π (F (e v))
  have hφ : ∀ v, φ v = logDetRatio M (realEmbed v) := fun v => rfl
  have hφC : ∀ v, e v ∈ U → ContDiffAt ℝ ∞ φ v := fun v hv =>
    π.contDiff.contDiffAt.comp v
      (((hC.contDiffAt (hU.mem_nhds hv))).comp v e.contDiff.contDiffAt)
  have hgφ : ∀ᶠ v in 𝓝 (0 : Fin n → ℝ), g =ᶠ[𝓝 v] fun w => (φ w).re := by
    have : ∀ᶠ v in 𝓝 (0 : Fin n → ℝ), ∀ᶠ w in 𝓝 v, e w ∈ U ∧
        LinearMap.det (M (realEmbed w)) ≠ 0 ∧
        logDetRatio M (realEmbed w) = (g w : ℂ) := hgood.eventually_nhds
    filter_upwards [this] with v hv
    filter_upwards [hv] with w hw
    rw [hφ, hw.2.2]
    simp
  have hreC : ∀ v, e v ∈ U → ContDiffAt ℝ ∞ (fun w => (φ w).re) v := fun v hv =>
    Complex.reCLM.contDiff.contDiffAt.comp v (hφC v hv)
  have hgdiff : ∀ᶠ v in 𝓝 (0 : Fin n → ℝ), DifferentiableAt ℝ g v := by
    filter_upwards [hgφ, hUnear] with v hv hvU
    exact ((hreC v hvU).differentiableAt (by simp)).congr_of_eventuallyEq hv
  have hsecond : DifferentiableAt ℝ (fderiv ℝ g) (0 : Fin n → ℝ) := by
    have h00 : e 0 ∈ U := by rw [he0]; exact hU0
    have h1 : DifferentiableAt ℝ (fderiv ℝ fun w => (φ w).re) (0 : Fin n → ℝ) :=
      ((hreC 0 h00).fderiv_right (m := 1) (by norm_cast)).differentiableAt (by simp)
    exact h1.congr_of_eventuallyEq hgφ.self_of_nhds.fderiv
  have hfirst : ∀ᶠ v in 𝓝 (0 : Fin n → ℝ), ∀ b : Fin n → ℝ,
      ((fderiv ℝ g v b : ℝ) : ℂ) = fderiv ℝ F (e v) (e b) 0 := by
    have hnear : ∀ᶠ v in 𝓝 (0 : Fin n → ℝ), (fun w => (g w : ℂ)) =ᶠ[𝓝 v] φ := by
      filter_upwards [hgood.eventually_nhds] with v hv
      filter_upwards [hv] with w hw
      rw [hφ, hw.2.2]
    filter_upwards [hnear, hgdiff, hUnear] with v hv hd hvU b
    have hF1 : HasFDerivAt F (fderiv ℝ F (e v)) (e v) :=
      ((hC.contDiffAt (hU.mem_nhds hvU)).differentiableAt (by simp)).hasFDerivAt
    have hA : HasFDerivAt φ (π.comp ((fderiv ℝ F (e v)).comp e)) v :=
      π.hasFDerivAt.comp v (hF1.comp v e.hasFDerivAt)
    have hB : HasFDerivAt (fun w => (g w : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ g v)) v :=
      Complex.ofRealCLM.hasFDerivAt.comp v hd.hasFDerivAt
    have := (hB.congr_of_eventuallyEq hv.symm).unique hA
    exact congrArg (fun L => L b) this
  have hT : ∀ a b : Fin n → ℝ,
      ((fderiv ℝ (fderiv ℝ g) 0 a b : ℝ) : ℂ) = Q (e a) (e b) 0 := by
    intro a b
    have hline : HasDerivAt (fun s : ℝ => s • a) a 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const a
    have hfd : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) 0) ((0 : ℝ) • a) := by
      simpa using hsecond.hasFDerivAt
    have hL : HasDerivAt (fun s : ℝ => fderiv ℝ g (s • a)) (fderiv ℝ (fderiv ℝ g) 0 a) 0 :=
      hfd.comp_hasDerivAt (0 : ℝ) hline
    have hL' : HasDerivAt (fun s : ℝ => fderiv ℝ g (s • a) b) (fderiv ℝ (fderiv ℝ g) 0 a b) 0 :=
      hL.clm_apply (hasDerivAt_const (0 : ℝ) b) |>.congr_deriv (by simp)
    have hLc := hL'.ofReal_comp
    have hG : HasDerivAt (derivAlongLine F 0 (e a) (e b))
        (secondDeriv F 0 (e a) (e b)) 0 :=
      (hDiff (e a) (e b)).hasDerivAt
    have hG0 : HasDerivAt (fun s : ℝ => derivAlongLine F 0 (e a) (e b) s 0)
        (secondDeriv F 0 (e a) (e b) 0) 0 :=
      (hasDerivAt_pi.mp hG) 0
    have hs : Tendsto (fun s : ℝ => s • a) (𝓝 0) (𝓝 0) := by
      simpa using hline.continuousAt.tendsto
    have hev : (fun s : ℝ => ((fderiv ℝ g (s • a) b : ℝ) : ℂ)) =ᶠ[𝓝 0]
        fun s => derivAlongLine F 0 (e a) (e b) s 0 := by
      filter_upwards [hs.eventually hfirst] with s hsv
      rw [hsv b]
      simp [derivAlongLine]
    have := (hLc.congr_of_eventuallyEq hev.symm).unique hG0
    rw [this, hQ]
  refine ⟨?_, hgdiff, hsecond, ?_⟩
  · filter_upwards [hgood] with v hv
    exact hv.2.1
  · intro z z'
    have hz : scalarSecondDeriv (logDetRatio M) 0 z z' = Q z z' 0 := by
      rw [hQ]
      rfl
    rw [hz]
    conv_rhs => rw [eq_realCLM_add_I_smul z, eq_realCLM_add_I_smul z']
    have hT' : ∀ a b : Fin n → ℝ, Q (realCLM n a) (realCLM n b) 0 =
        ((fderiv ℝ (fderiv ℝ g) 0 a b : ℝ) : ℂ) := fun a b => (hT a b).symm
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, hT']
    push_cast
    linear_combination
      (-((fderiv ℝ (fderiv ℝ g) 0 (fun j => (z j).im) (fun j => (z' j).im) : ℝ) : ℂ)) * Complex.I_sq
end YangMills.Construction.PeriodicOperators.RealLogDet
end
