import YangMills.Construction.SummableBoundsOfTheFlow.SizesOfObservablesOfTheWeightProof
import YangMills.Construction.SummableBoundsOfTheFlow.SizesOfTheDerivativesOfTheCut
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Interpolation.CutoffDerivatives
open Set Filter Topology MeasureTheory ColdStepAtMirrorFrames
section BallLaw
variable {ι : Type} [Fintype ι] {ρ : ℝ} {p : ℝ → ℝ} {Ψ : BondField ι → ℝ}
def bondBall (ι : Type) (ρ : ℝ) : Set (BondField ι) := {η | ∀ b, ‖η b‖ < ρ}
theorem isOpen_bondBall [Finite ι] (ρ : ℝ) : IsOpen (bondBall ι ρ) := by apply _root_.YangMills.Construction.Interpolation.WeightMoments.isOpen_openPolyBall <;> assumption
theorem ballDensity_nonneg (ρ : ℝ) (p : ℝ → ℝ) (Ψ : BondField ι → ℝ) (η : BondField ι) :
    0 ≤ ballDensity (cutoffFactor ρ p) Ψ η := by apply _root_.YangMills.Construction.ConvexMeasures.LocalCovariance.ballDensity_nonneg <;> assumption
theorem ballDensity_eq_zero_of_not_mem {η : BondField ι} (h : η ∉ bondBall ι ρ) :
    ballDensity (cutoffFactor ρ p) Ψ η = 0 := by apply _root_.YangMills.Construction.Interpolation.WeightMoments.ballDensity_eq_zero_of_not_mem <;> assumption
theorem continuous_ballDensity (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ) (hp : IsCutoff ρ p)
    (hΨ : Continuous Ψ) : Continuous (ballDensity (cutoffFactor ρ p) Ψ) := by apply _root_.YangMills.Construction.Interpolation.WeightMoments.continuous_ballDensity <;> assumption
theorem integral_ballDensity_pos (hR : CutoffFactorIsRadialCutoff) (hρ : 0 < ρ) (hp : IsCutoff ρ p)
    (hΨ : Continuous Ψ) : 0 < ∫ η, ballDensity (cutoffFactor ρ p) Ψ η := by apply _root_.YangMills.Construction.Interpolation.WeightMoments.integral_ballDensity_pos <;> assumption
theorem ballExpectation_mono {f g : BondField ι → ℝ} (hm : 0 < ∫ η, ballDensity (cutoffFactor ρ p) Ψ η)
    (hf : Integrable fun η => f η * ballDensity (cutoffFactor ρ p) Ψ η)
    (hg : Integrable fun η => g η * ballDensity (cutoffFactor ρ p) Ψ η)
    (h : ∀ η ∈ bondBall ι ρ, f η ≤ g η) :
    ballExpectation (cutoffFactor ρ p) Ψ f ≤ ballExpectation (cutoffFactor ρ p) Ψ g := by apply _root_.YangMills.Construction.Interpolation.WeightMoments.ballExpectation_mono <;> assumption
theorem ballExpectation_const (hm : 0 < ∫ η, ballDensity (cutoffFactor ρ p) Ψ η) (c : ℝ) :
    ballExpectation (cutoffFactor ρ p) Ψ (fun _ => c) = c := by apply _root_.YangMills.Construction.Interpolation.WeightMoments.ballExpectation_const <;> assumption
theorem ballExpectation_add {f g : BondField ι → ℝ}
    (hf : Integrable fun η => f η * ballDensity (cutoffFactor ρ p) Ψ η)
    (hg : Integrable fun η => g η * ballDensity (cutoffFactor ρ p) Ψ η) :
    ballExpectation (cutoffFactor ρ p) Ψ (fun η => f η + g η) =
      ballExpectation (cutoffFactor ρ p) Ψ f + ballExpectation (cutoffFactor ρ p) Ψ g := by apply _root_.YangMills.Construction.Interpolation.WeightMoments.ballExpectation_add <;> assumption
theorem ballExpectation_const_mul (c : ℝ) (f : BondField ι → ℝ) :
    ballExpectation (cutoffFactor ρ p) Ψ (fun η => c * f η) = c * ballExpectation (cutoffFactor ρ p) Ψ f := by apply _root_.YangMills.Construction.Interpolation.WeightMoments.ballExpectation_const_mul <;> assumption
end BallLaw
theorem add_pow_le_two_pow_mul (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (q : ℕ) :
    (a + b) ^ q ≤ 2 ^ q * (a ^ q + b ^ q) := by
  rcases le_total a b with h | h
  · calc (a + b) ^ q ≤ (2 * b) ^ q := pow_le_pow_left₀ (by positivity) (by linarith) q
      _ = 2 ^ q * b ^ q := mul_pow _ _ _
      _ ≤ 2 ^ q * (a ^ q + b ^ q) := by
        have : 0 ≤ a ^ q := by positivity
        gcongr
        linarith
  · calc (a + b) ^ q ≤ (2 * a) ^ q := pow_le_pow_left₀ (by positivity) (by linarith) q
      _ = 2 ^ q * a ^ q := mul_pow _ _ _
      _ ≤ 2 ^ q * (a ^ q + b ^ q) := by
        have : 0 ≤ b ^ q := by positivity
        gcongr
        linarith
def radialProfile (p : ℝ → ℝ) (j : ℕ) (c : ℝ) (u : ℝ) : ℝ := c * (u ^ j * iteratedDeriv j p u)
theorem iteratedDeriv_eq_zero_of_lt {ρ : ℝ} {p : ℝ → ℝ} (hp : IsCutoff ρ p) {j : ℕ} (hj : 1 ≤ j) {u : ℝ}
    (h0 : 0 < u) (h1 : u < 5 * ρ / 8) : iteratedDeriv j p u = 0 := by
  have hev : p =ᶠ[𝓝 u] fun _ => (0 : ℝ) := by
    filter_upwards [Ioo_mem_nhds h0 h1] with z hz
    exact hp.vanish_small z hz.1.le hz.2.le
  rw [(hev.iteratedDeriv j).eq_of_nhds]
  rw [iteratedDeriv_eq_iteratedFDeriv, iteratedFDeriv_const_of_ne (by omega)]
  simp
theorem radialProfile_eq_zero_of_lt {ρ : ℝ} {p : ℝ → ℝ} (hp : IsCutoff ρ p) {j : ℕ} (hj : 1 ≤ j) (c : ℝ)
    {u : ℝ} (h0 : 0 ≤ u) (h1 : u < 5 * ρ / 8) : radialProfile p j c u = 0 := by
  rcases h0.eq_or_lt with rfl | h0
  · simp [radialProfile, zero_pow (show j ≠ 0 by omega)]
  · simp [radialProfile, iteratedDeriv_eq_zero_of_lt hp hj h0 h1]
theorem contDiffAt_of_isCutoff {ρ : ℝ} {p : ℝ → ℝ} (hp : IsCutoff ρ p) (n : ℕ) {u : ℝ} (h0 : 0 < u)
    (h1 : u < ρ) : ContDiffAt ℝ n p u :=
  (hp.smooth.contDiffAt (Ico_mem_nhds h0 h1)).of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
theorem contDiffAt_iteratedDeriv {ρ : ℝ} {p : ℝ → ℝ} (hp : IsCutoff ρ p) (j : ℕ) {u : ℝ} (h0 : 0 < u)
    (h1 : u < ρ) : ContDiffAt ℝ 2 (iteratedDeriv j p) u := by
  have h2 : ContDiffAt ℝ ((j + 2 : ℕ) : WithTop ℕ∞) p u := contDiffAt_of_isCutoff hp _ h0 h1
  have h3 : ContDiffAt ℝ 2 (iteratedFDeriv ℝ j p) u := h2.iteratedFDeriv_right (by norm_cast; omega)
  have h4 : iteratedDeriv j p = fun x => iteratedFDeriv ℝ j p x fun _ => 1 := by
    funext x
    exact iteratedDeriv_eq_iteratedFDeriv
  rw [h4]
  exact ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => ℝ) ℝ fun _ => 1).contDiff.contDiffAt).comp u h3
theorem hasDerivAt_radialProfile {ρ : ℝ} {p : ℝ → ℝ} (hp : IsCutoff ρ p) {j : ℕ} (c : ℝ) {u : ℝ}
    (h0 : 0 < u) (h1 : u < ρ) :
    HasDerivAt (radialProfile p j c)
      (c * ((j : ℝ) * u ^ (j - 1) * iteratedDeriv j p u + u ^ j * iteratedDeriv (j + 1) p u)) u := by
  have h2 : DifferentiableAt ℝ (iteratedDeriv j p) u :=
    (contDiffAt_iteratedDeriv hp j h0 h1).differentiableAt (by norm_num)
  have h3 := h2.hasDerivAt
  have h4 : HasDerivAt (fun z : ℝ => z ^ j) ((j : ℝ) * u ^ (j - 1)) u := hasDerivAt_pow j u
  have h5 := (h4.mul h3).const_mul c
  rw [← iteratedDeriv_succ] at h5
  exact h5
theorem contDiffOn_radialProfile_norm {ρ : ℝ} {p : ℝ → ℝ} (hρ : 0 < ρ) (hp : IsCutoff ρ p) {j : ℕ}
    (hj : 1 ≤ j) (c : ℝ) :
    ContDiffOn ℝ 1 (fun v : BondVector => radialProfile p j c ‖v‖) (Metric.ball 0 ρ) := by
  intro v hv
  have hvρ : ‖v‖ < ρ := by simpa using hv
  refine ContDiffAt.contDiffWithinAt ?_
  by_cases h0 : v = 0
  · subst h0
    have hev : (fun v : BondVector => radialProfile p j c ‖v‖) =ᶠ[𝓝 0] fun _ => (0 : ℝ) := by
      have hb : Metric.ball (0 : BondVector) (5 * ρ / 8) ∈ 𝓝 (0 : BondVector) :=
        Metric.ball_mem_nhds _ (by positivity)
      filter_upwards [hb] with z hz
      exact radialProfile_eq_zero_of_lt hp hj c (norm_nonneg z) (by simpa using hz)
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hn : 0 < ‖v‖ := norm_pos_iff.mpr h0
    have h1 : ContDiffAt ℝ 1 (radialProfile p j c) ‖v‖ := by
      refine contDiffAt_const.mul (ContDiffAt.mul (contDiffAt_id.pow j) ?_)
      exact (contDiffAt_iteratedDeriv hp j hn hvρ).of_le (by norm_num)
    exact ContDiffAt.comp (g := radialProfile p j c) v h1 (contDiffAt_norm ℝ h0)
theorem norm_fderiv_radialProfile_norm_le {ρ : ℝ} {p : ℝ → ℝ} (hρ : 0 < ρ) (hp : IsCutoff ρ p) {j : ℕ}
    (hj : 1 ≤ j) {c : ℝ} (hc : 0 ≤ c) {v : BondVector} (hv : ‖v‖ < ρ) :
    ‖fderiv ℝ (fun v : BondVector => radialProfile p j c ‖v‖) v‖ ≤
      c * ((j : ℝ) * ρ ^ (j - 1) * |iteratedDeriv j p ‖v‖| + ρ ^ j * |iteratedDeriv (j + 1) p ‖v‖|) := by
  have hpos : 0 ≤ c * ((j : ℝ) * ρ ^ (j - 1) * |iteratedDeriv j p ‖v‖| +
      ρ ^ j * |iteratedDeriv (j + 1) p ‖v‖|) := by
    positivity
  by_cases h0 : ‖v‖ < 5 * ρ / 8
  · have hev : (fun v : BondVector => radialProfile p j c ‖v‖) =ᶠ[𝓝 v] fun _ => (0 : ℝ) := by
      have hs : {z : BondVector | ‖z‖ < 5 * ρ / 8} ∈ 𝓝 v :=
        (isOpen_lt continuous_norm continuous_const).mem_nhds h0
      filter_upwards [hs] with z hz
      exact radialProfile_eq_zero_of_lt hp hj c (norm_nonneg z) hz
    rw [hev.fderiv_eq]
    simpa using hpos
  · have hn : 0 < ‖v‖ := by
      have : 5 * ρ / 8 ≤ ‖v‖ := not_lt.mp h0
      have : 0 < 5 * ρ / 8 := by positivity
      linarith
    have hv0 : v ≠ 0 := norm_pos_iff.mp hn
    have h1 := hasDerivAt_radialProfile (j := j) hp c hn hv
    have h2 : HasFDerivAt (fun v : BondVector => ‖v‖) (fderiv ℝ (fun v : BondVector => ‖v‖) v) v :=
      ((contDiffAt_norm ℝ hv0 : ContDiffAt ℝ 1 _ v).differentiableAt (by norm_num)).hasFDerivAt
    have h3 := h1.comp_hasFDerivAt v h2
    have e : (fun v : BondVector => radialProfile p j c ‖v‖) =
        radialProfile p j c ∘ fun v : BondVector => ‖v‖ := rfl
    rw [e, h3.fderiv, norm_smul, Real.norm_eq_abs]
    have h4 : ‖fderiv ℝ (fun v : BondVector => ‖v‖) v‖ ≤ 1 := by
      have := norm_fderiv_le_of_lipschitz ℝ (x₀ := v) (lipschitzWith_one_norm (E := BondVector))
      simpa using this
    have h5 : |c * ((j : ℝ) * ‖v‖ ^ (j - 1) * iteratedDeriv j p ‖v‖ + ‖v‖ ^ j * iteratedDeriv (j + 1) p ‖v‖)| ≤
        c * ((j : ℝ) * ρ ^ (j - 1) * |iteratedDeriv j p ‖v‖| + ρ ^ j * |iteratedDeriv (j + 1) p ‖v‖|) := by
      rw [abs_mul, abs_of_nonneg hc]
      refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans ?_) hc
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (j : ℝ)),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖v‖ ^ (j - 1)), abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖v‖ ^ j)]
      have a1 : ‖v‖ ^ (j - 1) ≤ ρ ^ (j - 1) := pow_le_pow_left₀ hn.le hv.le _
      have a2 : ‖v‖ ^ j ≤ ρ ^ j := pow_le_pow_left₀ hn.le hv.le _
      gcongr
    calc _ ≤ |c * ((j : ℝ) * ‖v‖ ^ (j - 1) * iteratedDeriv j p ‖v‖ +
          ‖v‖ ^ j * iteratedDeriv (j + 1) p ‖v‖)| * 1 := by
          gcongr
      _ ≤ _ := by rw [mul_one]; exact h5
theorem moment_le_of_dominated (hR : CutoffFactorIsRadialCutoff) {ι : Type} [Fintype ι] {ρ : ℝ}
    {p : ℝ → ℝ} {Ψ : BondField ι → ℝ} (hρ : 0 < ρ) (hp : IsCutoff ρ p) (hΨ : Continuous Ψ)
    {f g : BondField ι → ℝ} (hf : ContinuousOn f (bondBall ι ρ))
    (hg : Integrable fun η => g η * ballDensity (cutoffFactor ρ p) Ψ η) {q : ℕ}
    (h : ∀ η ∈ bondBall ι ρ, |f η| ^ q ≤ g η) :
    (Integrable fun η => |f η| ^ q * ballDensity (cutoffFactor ρ p) Ψ η) ∧
      ballExpectation (cutoffFactor ρ p) Ψ (fun η => |f η| ^ q) ≤ ballExpectation (cutoffFactor ρ p) Ψ g := by
  have hU := (isOpen_bondBall (ι := ι) ρ).measurableSet
  have hc := continuous_ballDensity hR hρ hp hΨ
  have hm : AEStronglyMeasurable (fun η => |f η| ^ q * ballDensity (cutoffFactor ρ p) Ψ η) volume := by
    have h1 : AEStronglyMeasurable (fun η => |f η| ^ q * ballDensity (cutoffFactor ρ p) Ψ η)
        (volume.restrict (bondBall ι ρ)) :=
      ((hf.abs.pow q).mul hc.continuousOn).aestronglyMeasurable hU
    have h2 : (bondBall ι ρ).indicator (fun η => |f η| ^ q * ballDensity (cutoffFactor ρ p) Ψ η) =
        fun η => |f η| ^ q * ballDensity (cutoffFactor ρ p) Ψ η := by
      funext η
      by_cases h : η ∈ bondBall ι ρ
      · simp [h]
      · simp [h, ballDensity_eq_zero_of_not_mem h]
    rw [← h2]
    exact (aestronglyMeasurable_indicator_iff hU).mpr h1
  have hi : Integrable fun η => |f η| ^ q * ballDensity (cutoffFactor ρ p) Ψ η := by
    refine hg.mono' hm (Eventually.of_forall fun η => ?_)
    by_cases hη : η ∈ bondBall ι ρ
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ballDensity_nonneg _ _ _ η), abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_right (h η hη) (ballDensity_nonneg _ _ _ η)
    · simp [ballDensity_eq_zero_of_not_mem hη]
  exact ⟨hi, ballExpectation_mono (integral_ballDensity_pos hR hρ hp hΨ) hi hg h⟩
end Interpolation.CutoffDerivatives
theorem Interpolation.cutoffDerivSizesStatement_holds (hR : ColdStepAtMirrorFrames.CutoffFactorIsRadialCutoff) :
    Interpolation.cutoffDerivSizesStatement := by
  open Set Filter Topology MeasureTheory ColdStepAtMirrorFrames Interpolation
    Interpolation.CutoffDerivatives in
  intro ρ p Cr j hρ hp hj hCr
  set D₁ : ℕ → ℝ := fun q => (ρ ^ j) ^ q * Cr j q (j * q) with hD₁
  set D₂ : ℕ → ℝ := fun q => 2 ^ q * (((j : ℝ) * ρ ^ (j - 1)) ^ q * Cr j q (j * q) +
    (ρ ^ j) ^ q * Cr (j + 1) q (j * q)) with hD₂
  have hD₁n : ∀ q, 0 ≤ D₁ q := fun q => mul_nonneg (by positivity) (hCr _ _ _)
  have hD₂n : ∀ q, 0 ≤ D₂ q := fun q => by
    have := hCr j q (j * q)
    have := hCr (j + 1) q (j * q)
    simp only [hD₂]
    positivity
  refine ⟨fun q => 1 + D₁ q + D₂ q, fun q => by
    have := hD₁n q
    have := hD₂n q
    positivity, ?_⟩
  intro ι _ _ b₀ l κ Ψ dZ hl hl1 hΨ hd hrim
  have hlinv : 0 < l⁻¹ := by positivity
  have hl1' : 1 ≤ l⁻¹ := (one_le_inv₀ hl).mpr hl1
  set x : ℝ := l⁻¹ ^ 2 with hx
  set c : ℝ := l⁻¹ ^ j with hc
  have hc0 : 0 ≤ c := by positivity
  have hH : (fun η : BondField ι => ‖(l⁻¹ • η) b₀‖ ^ j * iteratedDeriv j p (l * ‖(l⁻¹ • η) b₀‖)) =
      fun η => radialProfile p j c ‖η b₀‖ := by
    funext η
    have e : ‖(l⁻¹ • η) b₀‖ = l⁻¹ * ‖η b₀‖ := by
      rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg hlinv.le]
    simp only [radialProfile, hc]
    rw [e, ← mul_assoc l, mul_inv_cancel₀ hl.ne', one_mul, mul_pow, mul_assoc]
  rw [hH]
  set h : BondField ι → ℝ := fun η => radialProfile p j c ‖η b₀‖ with hh
  have hproj : ContDiff ℝ 1 (fun η : BondField ι => η b₀) := contDiff_apply ℝ BondVector b₀
  have hmaps : ∀ η ∈ bondBall ι ρ, η b₀ ∈ Metric.ball (0 : BondVector) ρ := fun η hη => by
    simpa using hη b₀
  have hC : ContDiffOn ℝ 1 h (bondBall ι ρ) :=
    (contDiffOn_radialProfile_norm hρ hp hj c).comp hproj.contDiffOn hmaps
  have hBo := isOpen_bondBall (ι := ι) ρ
  have hpow : ∀ q : ℕ, c ^ q * ((x ^ (j * q))⁻¹) ≤ 1 := by
    intro q
    have h1 : c ^ q * ((x ^ (j * q))⁻¹) = l ^ (j * q) := by
      have e1 : c ^ q = (l ^ (j * q))⁻¹ := by
        rw [hc, ← pow_mul, inv_pow]
      have e2 : x ^ (j * q) = ((l ^ (j * q))⁻¹) ^ 2 := by
        rw [hx, ← pow_mul, ← inv_pow, ← pow_mul, mul_comm]
      rw [e1, e2]
      field_simp
    rw [h1]
    exact pow_le_one₀ hl.le hl1
  have hmass := integral_ballDensity_pos (Ψ := Ψ) hR hρ hp hΨ
  have hmom : ∀ q : ℕ, 1 ≤ q →
      MomentBound (cutoffFactor ρ p) Ψ (fun η => h η - 0) q ((1 + D₁ q + D₂ q) * 1) := by
    intro q hq
    obtain ⟨hi, hm⟩ := hrim j q (j * q) b₀ hj hq
    set g : BondField ι → ℝ := fun η => (c * ρ ^ j) ^ q * |iteratedDeriv j p ‖η b₀‖| ^ q with hg
    have hgi : Integrable fun η => g η * ballDensity (cutoffFactor ρ p) Ψ η := by
      have := hi.const_mul ((c * ρ ^ j) ^ q)
      simpa [hg, mul_assoc] using this
    have hf : ContinuousOn (fun η => h η - 0) (bondBall ι ρ) := by simpa using hC.continuousOn
    obtain ⟨h1, h2⟩ := moment_le_of_dominated hR hρ hp hΨ hf hgi (q := q) (fun η hη => by
      have h3 : |h η - 0| ≤ c * ρ ^ j * |iteratedDeriv j p ‖η b₀‖| := by
        simp only [sub_zero, hh, radialProfile]
        rw [abs_mul, abs_mul, abs_of_nonneg hc0, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖η b₀‖ ^ j), mul_assoc]
        have : ‖η b₀‖ ^ j ≤ ρ ^ j := pow_le_pow_left₀ (norm_nonneg _) (hη b₀).le _
        gcongr
      have h4 := pow_le_pow_left₀ (abs_nonneg _) h3 q
      rwa [mul_pow] at h4)
    refine ⟨h1, h2.trans ?_⟩
    have e : ballExpectation (cutoffFactor ρ p) Ψ g =
        (c * ρ ^ j) ^ q * ballExpectation (cutoffFactor ρ p) Ψ fun η => |iteratedDeriv j p ‖η b₀‖| ^ q :=
      ballExpectation_const_mul _ _
    rw [e]
    have h5 : (c * ρ ^ j) ^ q * ballExpectation (cutoffFactor ρ p) Ψ (fun η => |iteratedDeriv j p ‖η b₀‖| ^ q) ≤
        (c * ρ ^ j) ^ q * (Cr j q (j * q) * (x ^ (j * q))⁻¹) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    have h6 : (c * ρ ^ j) ^ q * (Cr j q (j * q) * (x ^ (j * q))⁻¹) ≤ D₁ q := by
      have : (c * ρ ^ j) ^ q * (Cr j q (j * q) * (x ^ (j * q))⁻¹) = D₁ q * (c ^ q * (x ^ (j * q))⁻¹) := by
        simp only [hD₁, mul_pow]
        ring
      rw [this]
      exact mul_le_of_le_one_right (hD₁n q) (hpow q)
    have h7 : 1 ≤ (1 + D₁ q + D₂ q) * 1 := by
      have := hD₁n q
      have := hD₂n q
      linarith
    have h8 : (1 + D₁ q + D₂ q) * 1 ≤ ((1 + D₁ q + D₂ q) * 1) ^ q := le_self_pow₀ h7 (by omega)
    have h9 := hD₂n q
    linarith
  have e0 : (fun η => h η - 0) = h := by
    funext η
    simp
  refine ⟨hC, fun q hq => e0 ▸ hmom q hq, fun η hη => (hC.contDiffAt (hBo.mem_nhds hη)).differentiableAt (by norm_num), 0,
    fun q hq => ⟨hmom q hq, fun b => ?_⟩⟩
  · have hfd : ∀ η ∈ bondBall ι ρ, fderiv ℝ h η =
        (fderiv ℝ (fun v : BondVector => radialProfile p j c ‖v‖) (η b₀)).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) b₀) := by
      intro η hη
      have h1 : DifferentiableAt ℝ (fun v : BondVector => radialProfile p j c ‖v‖) (η b₀) :=
        ((contDiffOn_radialProfile_norm hρ hp hj c).contDiffAt
          (Metric.isOpen_ball.mem_nhds (hmaps η hη))).differentiableAt (by norm_num)
      have h2 := h1.hasFDerivAt.comp η
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) b₀).hasFDerivAt
      exact h2.fderiv
    have hcont : ContinuousOn (bondGradNorm h b) (bondBall ι ρ) := by
      have h1 : ContinuousOn (fderiv ℝ h) (bondBall ι ρ) := hC.continuousOn_fderiv_of_isOpen hBo le_rfl
      unfold bondGradNorm
      have h2 : ContinuousOn (fun η => (fderiv ℝ h η).comp
          (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b)) (bondBall ι ρ) :=
        h1.clm_comp continuousOn_const
      exact h2.norm
    have hsx : 1 ≤ Real.sqrt x := by
      rw [hx, Real.sqrt_sq hlinv.le]
      exact hl1'
    have hS1 : 1 ≤ 1 + D₁ q + D₂ q := by
      have := hD₁n q
      have := hD₂n q
      linarith
    by_cases hb : b = b₀
    · subst hb
      rw [hd]
      have hPN : ∀ η ∈ bondBall ι ρ,
          bondGradNorm h b η = ‖fderiv ℝ (fun v : BondVector => radialProfile p j c ‖v‖) (η b)‖ := by
        intro η hη
        unfold bondGradNorm
        rw [hfd η hη]
        congr 1
        ext1 v
        simp
      obtain ⟨hi, hm⟩ := hrim j q (j * q) b hj hq
      obtain ⟨hi', hm'⟩ := hrim (j + 1) q (j * q) b (by omega) hq
      set a : ℝ := (j : ℝ) * ρ ^ (j - 1) with ha
      set e₁ : ℝ := ρ ^ j with he₁
      set g : BondField ι → ℝ := fun η => (c ^ q * 2 ^ q * a ^ q) * |iteratedDeriv j p ‖η b‖| ^ q +
        (c ^ q * 2 ^ q * e₁ ^ q) * |iteratedDeriv (j + 1) p ‖η b‖| ^ q with hg
      have hi₁ : Integrable fun η => ((c ^ q * 2 ^ q * a ^ q) * |iteratedDeriv j p ‖η b‖| ^ q) *
          ballDensity (cutoffFactor ρ p) Ψ η := by
        simpa [mul_assoc] using hi.const_mul (c ^ q * 2 ^ q * a ^ q)
      have hi₂ : Integrable fun η => ((c ^ q * 2 ^ q * e₁ ^ q) * |iteratedDeriv (j + 1) p ‖η b‖| ^ q) *
          ballDensity (cutoffFactor ρ p) Ψ η := by
        simpa [mul_assoc] using hi'.const_mul (c ^ q * 2 ^ q * e₁ ^ q)
      have hgi : Integrable fun η => g η * ballDensity (cutoffFactor ρ p) Ψ η := by
        have := hi₁.add hi₂
        refine this.congr (Eventually.of_forall fun η => ?_)
        simp only [hg, Pi.add_apply, add_mul]
      obtain ⟨h1, h2⟩ := moment_le_of_dominated hR hρ hp hΨ hcont hgi (q := q) (fun η hη => by
        have h3 := norm_fderiv_radialProfile_norm_le hρ hp hj hc0 (v := η b) (hη b)
        rw [← hPN η hη] at h3
        have h4 : |bondGradNorm h b η| ^ q ≤
            (c * (a * |iteratedDeriv j p ‖η b‖| + e₁ * |iteratedDeriv (j + 1) p ‖η b‖|)) ^ q := by
          rw [abs_of_nonneg (by unfold bondGradNorm; positivity)]
          exact pow_le_pow_left₀ (by unfold bondGradNorm; positivity) h3 q
        refine h4.trans ?_
        rw [mul_pow]
        have h5 := add_pow_le_two_pow_mul (a * |iteratedDeriv j p ‖η b‖|)
          (e₁ * |iteratedDeriv (j + 1) p ‖η b‖|) (by positivity) (by positivity) q
        have h6 := mul_le_mul_of_nonneg_left h5 (by positivity : 0 ≤ c ^ q)
        refine h6.trans (le_of_eq ?_)
        simp only [hg, mul_pow]
        ring)
      refine ⟨h1, h2.trans ?_⟩
      have e : ballExpectation (cutoffFactor ρ p) Ψ g =
          (c ^ q * 2 ^ q * a ^ q) * ballExpectation (cutoffFactor ρ p) Ψ (fun η => |iteratedDeriv j p ‖η b‖| ^ q) +
          (c ^ q * 2 ^ q * e₁ ^ q) *
            ballExpectation (cutoffFactor ρ p) Ψ (fun η => |iteratedDeriv (j + 1) p ‖η b‖| ^ q) := by
        simp only [hg]
        rw [ballExpectation_add hi₁ hi₂, ballExpectation_const_mul, ballExpectation_const_mul]
      rw [e]
      have h5 : (c ^ q * 2 ^ q * a ^ q) *
            ballExpectation (cutoffFactor ρ p) Ψ (fun η => |iteratedDeriv j p ‖η b‖| ^ q) +
          (c ^ q * 2 ^ q * e₁ ^ q) *
            ballExpectation (cutoffFactor ρ p) Ψ (fun η => |iteratedDeriv (j + 1) p ‖η b‖| ^ q) ≤
          D₂ q * (c ^ q * (x ^ (j * q))⁻¹) := by
        have a1 := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ c ^ q * 2 ^ q * a ^ q)
        have a2 := mul_le_mul_of_nonneg_left hm' (by positivity : 0 ≤ c ^ q * 2 ^ q * e₁ ^ q)
        refine (add_le_add a1 a2).trans (le_of_eq ?_)
        simp only [hD₂]
        ring
      refine h5.trans ((mul_le_of_le_one_right (hD₂n q) (hpow q)).trans ?_)
      have h6 : (1 + D₁ q + D₂ q) ≤ (1 + D₁ q + D₂ q) * Real.sqrt x * 1 * Real.exp (-(2 * κ * 0)) := by
        simp only [mul_zero, neg_zero, Real.exp_zero, mul_one]
        exact le_mul_of_one_le_right (by linarith) hsx
      have h7 : (1 + D₁ q + D₂ q) ≤ (1 + D₁ q + D₂ q) ^ q := le_self_pow₀ hS1 (by omega)
      have h8 := pow_le_pow_left₀ (by linarith) h6 q
      have h9 := hD₁n q
      linarith
    · have hPN : ∀ η ∈ bondBall ι ρ, bondGradNorm h b η = 0 := by
        intro η hη
        unfold bondGradNorm
        rw [hfd η hη]
        have hz : ((fderiv ℝ (fun v : BondVector => radialProfile p j c ‖v‖) (η b₀)).comp
            (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) b₀)).comp
            (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b) = 0 := by
          ext1 v
          simp [Ne.symm hb]
        rw [hz, norm_zero]
      have hq0 : q ≠ 0 := by omega
      obtain ⟨h1, h2⟩ := moment_le_of_dominated (g := fun _ => 0) hR hρ hp hΨ hcont (by simp) (q := q)
        (fun η hη => by
          rw [hPN η hη]
          simp [hq0])
      refine ⟨h1, h2.trans ?_⟩
      rw [ballExpectation_const hmass]
      positivity
end YangMills.Construction
end
