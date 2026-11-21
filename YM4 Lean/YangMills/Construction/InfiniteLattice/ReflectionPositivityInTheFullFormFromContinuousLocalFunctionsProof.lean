import YangMills.Construction.InfiniteLattice.ActionOfTheLatticeIsometriesOnConfigurationsAndFunctions
import YangMills.Construction.InfiniteLattice.AdmissiblePositionsOfAMirror
import YangMills.Construction.InfiniteLattice.AlmostEveryConditionalMeasureIsAPeriodicGibbsStateProof
import YangMills.Construction.InfiniteLattice.ApproximationInTheQuadraticMeanByFunctionsOfFinitelyManyBonds
import YangMills.Construction.InfiniteLattice.ReflectionPositivityInTheFullFormFromContinuousLocalFunctions
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
open scoped ComplexOrder ComplexConjugate Topology ENNReal
noncomputable section
namespace YangMills.Construction.GibbsAtFixedSpacing.FullReflectionPositivityFromContinuousLocal
open InfiniteLattice (GaugeField IsSymmetricUnder IsBoundedObservable LatticeSymmetry)
open LatticeConventions (NormalHyperplane conjFun)
open LatticeConventions.NormalHyperplane (reflectSymmetry)
open QuadraticMeanApproximation (RegionMeasurableApproximable TendstoForMeasure)
section CauchySchwarz
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
theorem integrable_of_norm_le {f : Ω → ℂ} (hf : Measurable f) {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) :
    Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable M (Eventually.of_forall hM)
theorem integrable_of_abs_le {f : Ω → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ x, |f x| ≤ M) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable M (Eventually.of_forall hM)
def secondMoment (μ : Measure Ω) (f : Ω → ℂ) : ℝ := ∫ x, ‖f x‖ ^ 2 ∂μ
theorem integrable_norm_sq {f : Ω → ℂ} (hf : Measurable f) {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) :
    Integrable (fun x => ‖f x‖ ^ 2) μ := by
  refine integrable_of_abs_le (M := M ^ 2) (hf.norm.pow_const 2) fun x => ?_
  rw [abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hM x) 2
omit [IsProbabilityMeasure μ] in
theorem secondMoment_nonneg (f : Ω → ℂ) : 0 ≤ secondMoment μ f :=
  integral_nonneg fun _ => by positivity
theorem sq_norm_integral_mul_le {f g : Ω → ℂ} (hf : Measurable f) (hg : Measurable g) {M N : ℝ}
    (hfM : ∀ x, ‖f x‖ ≤ M) (hgN : ∀ x, ‖g x‖ ≤ N) :
    ‖∫ x, f x * g x ∂μ‖ ^ 2 ≤ secondMoment μ f * secondMoment μ g := by
  have hff := integrable_norm_sq (μ := μ) hf hfM
  have hgg := integrable_norm_sq (μ := μ) hg hgN
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hfM (Classical.choice (μ.nonempty_of_neZero)))
  have hfg : Integrable (fun x => ‖f x‖ * ‖g x‖) μ := by
    refine integrable_of_abs_le (M := M * N) (hf.norm.mul hg.norm) fun x => ?_
    rw [abs_of_nonneg (by positivity)]
    exact mul_le_mul (hfM x) (hgN x) (norm_nonneg _) hM0
  set S := ∫ x, ‖f x‖ * ‖g x‖ ∂μ with hS
  have hquad : ∀ t : ℝ, 0 ≤ secondMoment μ f * (t * t) + (-2 * S) * t + secondMoment μ g := by
    intro t
    have hint : ∫ x, (t * ‖f x‖ - ‖g x‖) ^ 2 ∂μ =
        secondMoment μ f * (t * t) + (-2 * S) * t + secondMoment μ g := by
      have e : ∀ x, (t * ‖f x‖ - ‖g x‖) ^ 2 =
          (t * t) * ‖f x‖ ^ 2 + (-2 * t) * (‖f x‖ * ‖g x‖) + ‖g x‖ ^ 2 := fun x => by ring
      simp only [e]
      rw [integral_add (f := fun x => t * t * ‖f x‖ ^ 2 + -2 * t * (‖f x‖ * ‖g x‖))
          (g := fun x => ‖g x‖ ^ 2) ((hff.const_mul _).add (hfg.const_mul _)) hgg,
        integral_add (f := fun x => t * t * ‖f x‖ ^ 2) (g := fun x => -2 * t * (‖f x‖ * ‖g x‖))
          (hff.const_mul _) (hfg.const_mul _), integral_const_mul, integral_const_mul]
      simp only [secondMoment, hS]
      ring
    rw [← hint]
    exact integral_nonneg fun _ => by positivity
  have hdisc := discrim_le_zero hquad
  have hSsq : S ^ 2 ≤ secondMoment μ f * secondMoment μ g := by
    simp only [discrim] at hdisc
    nlinarith
  have hle : ‖∫ x, f x * g x ∂μ‖ ≤ S := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    simp only [norm_mul, hS]
  exact (pow_le_pow_left₀ (norm_nonneg _) hle 2).trans hSsq
theorem norm_integral_mul_le_sqrt {f g : Ω → ℂ} (hf : Measurable f) (hg : Measurable g) {M N : ℝ}
    (hfM : ∀ x, ‖f x‖ ≤ M) (hgN : ∀ x, ‖g x‖ ≤ N) :
    ‖∫ x, f x * g x ∂μ‖ ≤ √(secondMoment μ f) * √(secondMoment μ g) := by
  rw [← Real.sqrt_mul (secondMoment_nonneg f)]
  exact Real.le_sqrt_of_sq_le (sq_norm_integral_mul_le hf hg hfM hgN)
theorem secondMoment_le_two_mul {f g : Ω → ℂ} (hf : Measurable f) (hg : Measurable g) {M N : ℝ}
    (hfM : ∀ x, ‖f x‖ ≤ M) (hgN : ∀ x, ‖g x‖ ≤ N) :
    secondMoment μ g ≤ 2 * secondMoment μ f + 2 * secondMoment μ (fun x => f x - g x) := by
  have hff := integrable_norm_sq (μ := μ) hf hfM
  have hgg := integrable_norm_sq (μ := μ) hg hgN
  have hd : Integrable (fun x => ‖f x - g x‖ ^ 2) μ :=
    integrable_norm_sq (M := M + N) (hf.sub hg) fun x =>
      (norm_sub_le _ _).trans (add_le_add (hfM x) (hgN x))
  have hrhs : 2 * secondMoment μ f + 2 * secondMoment μ (fun x => f x - g x) =
      ∫ x, (2 * ‖f x‖ ^ 2 + 2 * ‖f x - g x‖ ^ 2) ∂μ := by
    rw [integral_add (hff.const_mul _) (hd.const_mul _), integral_const_mul, integral_const_mul]
    rfl
  rw [hrhs]
  refine integral_mono hgg ((hff.const_mul _).add (hd.const_mul _)) fun x => ?_
  have h1 : ‖g x‖ ≤ ‖f x‖ + ‖f x - g x‖ := by
    have := norm_sub_le (f x) (f x - g x)
    simpa using this
  have h2 := norm_nonneg (g x)
  show ‖g x‖ ^ 2 ≤ 2 * ‖f x‖ ^ 2 + 2 * ‖f x - g x‖ ^ 2
  nlinarith [sq_nonneg (‖f x‖ - ‖f x - g x‖), norm_nonneg (f x), norm_nonneg (f x - g x)]
omit [IsProbabilityMeasure μ] in
theorem secondMoment_eq_toReal_lintegral {f : Ω → ℂ} (hf : Measurable f) :
    secondMoment μ f = (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ).toReal := by
  rw [secondMoment, integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => by positivity)
    (hf.norm.pow_const 2).aestronglyMeasurable]
  congr 1
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
end CauchySchwarz
variable {a : ℝ}
theorem isBoundedObservable_sub {F G : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (hG : IsBoundedObservable G) : IsBoundedObservable fun U => F U - G U := by apply _root_.YangMills.Construction.LatticePhases.ConditionalGibbsProof.isBoundedObservable_sub <;> assumption
def reflectedInner {P : NormalHyperplane} (hP : P.IsLatticeMirror a) (ν : BorelProb a)
    (F G : GaugeField a → ℂ) : ℂ :=
  ∫ U, conj ((reflectSymmetry hP).actOn F U) * G U ∂ν.1
theorem reflectedPairing_eq_reflectedInner {P : NormalHyperplane} (hP : P.IsLatticeMirror a)
    (ν : BorelProb a) (F : GaugeField a → ℂ) : reflectedPairing hP ν F = reflectedInner hP ν F F :=
  rfl
section Invariant
variable (hAct : LatticeSymmetryActionOnFields) (ha : 0 < a)
  {P : NormalHyperplane} (hP : P.IsLatticeMirror a) (ν : BorelProb a)
include hAct ha in
theorem isBoundedObservable_actOn {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) :
    IsBoundedObservable ((reflectSymmetry hP).actOn F) :=
  (hAct a ha (reflectSymmetry hP) (reflectSymmetry hP)).2.2.1.1 F hF
include hAct ha in
theorem isBoundedObservable_conj_mul {F G : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (hG : IsBoundedObservable G) :
    IsBoundedObservable fun U => conj ((reflectSymmetry hP).actOn F U) * G U := by
  obtain ⟨hm, M, hM⟩ := isBoundedObservable_actOn hAct ha hP hF
  obtain ⟨hGm, N, hN⟩ := hG
  refine ⟨(Complex.continuous_conj.measurable.comp hm).mul hGm, M * N, fun U => ?_⟩
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul (hM U) (hN U) (norm_nonneg _) ((norm_nonneg _).trans (hM U))
theorem secondMoment_actOn (hinv : IsSymmetricUnder ν.1 (reflectSymmetry hP))
    {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) :
    secondMoment ν.1 ((reflectSymmetry hP).actOn F) = secondMoment ν.1 F := by
  obtain ⟨hFm, M, hM⟩ := hF
  have hobs : IsBoundedObservable fun U => ((‖F U‖ ^ 2 : ℝ) : ℂ) := by
    refine ⟨Complex.measurable_ofReal.comp (hFm.norm.pow_const 2), M ^ 2, fun U => ?_⟩
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hM U) 2
  have e : ∫ U, ((‖(reflectSymmetry hP).actOn F U‖ ^ 2 : ℝ) : ℂ) ∂ν.1 =
      ∫ U, ((‖F U‖ ^ 2 : ℝ) : ℂ) ∂ν.1 := hinv _ hobs
  rw [integral_complex_ofReal, integral_complex_ofReal] at e
  exact Complex.ofReal_injective e
include hAct ha in
theorem norm_reflectedInner_le (hinv : IsSymmetricUnder ν.1 (reflectSymmetry hP))
    {F G : GaugeField a → ℂ} (hF : IsBoundedObservable F) (hG : IsBoundedObservable G) :
    ‖reflectedInner hP ν F G‖ ≤ √(secondMoment ν.1 F) * √(secondMoment ν.1 G) := by
  have : IsProbabilityMeasure ν.1 := ν.2
  obtain ⟨hm, M, hM⟩ := isBoundedObservable_actOn hAct ha hP hF
  obtain ⟨hGm, N, hN⟩ := hG
  have hq : secondMoment ν.1 (fun U => conj ((reflectSymmetry hP).actOn F U)) =
      secondMoment ν.1 F := by
    rw [← secondMoment_actOn hP ν hinv hF]
    simp only [secondMoment, Complex.norm_conj]
  have h := norm_integral_mul_le_sqrt (μ := ν.1) (Complex.continuous_conj.measurable.comp hm) hGm
    (M := M) (N := N) (fun U => by simpa using hM U) hN
  rw [← hq]
  exact h
include hAct ha in
theorem norm_reflectedPairing_sub_le (hinv : IsSymmetricUnder ν.1 (reflectSymmetry hP))
    {F G : GaugeField a → ℂ} (hF : IsBoundedObservable F) (hG : IsBoundedObservable G) :
    ‖reflectedPairing hP ν F - reflectedPairing hP ν G‖ ≤
      √(secondMoment ν.1 fun U => F U - G U) *
        (√(secondMoment ν.1 F) + √(secondMoment ν.1 G)) := by
  have : IsProbabilityMeasure ν.1 := ν.2
  have hd := isBoundedObservable_sub hF hG
  have hint : ∀ {H K : GaugeField a → ℂ}, IsBoundedObservable H → IsBoundedObservable K →
      Integrable (fun U => conj ((reflectSymmetry hP).actOn H U) * K U) ν.1 := by
    intro H K hH hK
    obtain ⟨hm, M, hM⟩ := isBoundedObservable_conj_mul hAct ha hP hH hK
    exact integrable_of_norm_le hm hM
  have hsplit : reflectedPairing hP ν F - reflectedPairing hP ν G =
      reflectedInner hP ν (fun U => F U - G U) F + reflectedInner hP ν G (fun U => F U - G U) := by
    simp only [reflectedPairing_eq_reflectedInner, reflectedInner]
    rw [← integral_sub (hint hF hF) (hint hG hG), ← integral_add (hint hd hF) (hint hG hd)]
    refine integral_congr_ae (Eventually.of_forall fun U => ?_)
    simp only [LatticeSymmetry.actOn, map_sub]
    ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have h₁ := norm_reflectedInner_le hAct ha hP ν hinv hd hF
  have h₂ := norm_reflectedInner_le hAct ha hP ν hinv hG hd
  calc _ ≤ _ := add_le_add h₁ h₂
    _ = _ := by ring
include hAct ha in
theorem reflectedPairing_nonneg_of_tendsto (hinv : IsSymmetricUnder ν.1 (reflectSymmetry hP))
    {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) {Fn : ℕ → GaugeField a → ℂ}
    (hFn : ∀ n, 1 ≤ n → IsBoundedObservable (Fn n))
    (hpos : ∀ n, 1 ≤ n → 0 ≤ reflectedPairing hP ν (Fn n))
    (hlim : Tendsto (fun n => ∫⁻ U, ‖F U - Fn n U‖ₑ ^ 2 ∂ν.1) atTop (𝓝 0)) :
    0 ≤ reflectedPairing hP ν F := by
  have : IsProbabilityMeasure ν.1 := ν.2
  have hn1 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  have hx : Tendsto (fun n => secondMoment ν.1 fun U => F U - Fn n U) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
    simp only [ENNReal.toReal_zero] at h
    refine h.congr' (hn1.mono fun n hn => ?_)
    exact (secondMoment_eq_toReal_lintegral (isBoundedObservable_sub hF (hFn n hn)).1).symm
  have hd : Tendsto (fun n => √(secondMoment ν.1 fun U => F U - Fn n U) *
      (√(secondMoment ν.1 F) +
        √(2 * secondMoment ν.1 F + 2 * secondMoment ν.1 fun U => F U - Fn n U))) atTop (𝓝 0) := by
    have h := ((Real.continuous_sqrt.tendsto _).comp hx).mul
      (tendsto_const_nhds (x := √(secondMoment ν.1 F)) |>.add
        ((Real.continuous_sqrt.tendsto _).comp
          ((tendsto_const_nhds (x := 2 * secondMoment ν.1 F)).add
            ((tendsto_const_nhds (x := (2 : ℝ))).mul hx))))
    simpa using h
  have hconv : Tendsto (fun n => reflectedPairing hP ν (Fn n)) atTop
      (𝓝 (reflectedPairing hP ν F)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (hn1.mono fun n hn => ?_) hd
    rw [norm_sub_rev]
    refine (norm_reflectedPairing_sub_le hAct ha hP ν hinv hF (hFn n hn)).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    refine add_le_add le_rfl (Real.sqrt_le_sqrt ?_)
    obtain ⟨hFm, M, hM⟩ := hF
    obtain ⟨hGm, N, hN⟩ := hFn n hn
    exact secondMoment_le_two_mul hFm hGm hM hN
  exact ge_of_tendsto hconv (hn1.mono hpos)
end Invariant
theorem holds (hAct : LatticeSymmetryActionOnFields)
    (hAdm : MirrorPositionsAndReflectionRules)
    (hApp : QuadraticMeanApproximation.Statement) :
    Statement := by
  intro a ha P hP ν hinv hpos
  have hplus : ∀ F ∈ boundedMeasurableIn a P.upperHalfSpace, 0 ≤ reflectedPairing hP ν F := by
    intro F hF
    obtain ⟨Fn, hFn, hFm, -, hlim⟩ := (hApp a ha ν).2 _ F hF
    exact reflectedPairing_nonneg_of_tendsto hAct ha hP ν hinv ⟨hFm, hF.2⟩
      (fun n hn => ⟨(hFn n hn).1.measurable, (hFn n hn).2.2.2⟩)
      (fun n hn => hpos _ (hFn n hn).2.1 (hFn n hn).1) hlim
  refine ⟨hplus, fun F hF => ?_⟩
  obtain ⟨-, -, hFm, -, -⟩ := (hApp a ha ν).2 _ F hF
  have hFobs : IsBoundedObservable F := ⟨hFm, hF.2⟩
  have hside : (reflectSymmetry hP).setImage P.lowerHalfSpace = P.upperHalfSpace :=
    (hAdm a ha P).2.2.2.2.2.2.1
  have himage := (hAct a ha (reflectSymmetry hP) (reflectSymmetry hP)).2.1.2.2.1
    P.lowerHalfSpace
  have hF' : (reflectSymmetry hP).actOn F ∈ boundedMeasurableIn a P.upperHalfSpace := by
    rw [← hside, ← himage]
    exact ⟨F, hF, rfl⟩
  have hinvF : reflectedPairing hP ν ((reflectSymmetry hP).actOn F) =
      reflectedPairing hP ν F :=
    hinv _ (isBoundedObservable_conj_mul hAct ha hP hFobs hFobs)
  rw [← hinvF]
  exact hplus _ hF'
end YangMills.Construction.GibbsAtFixedSpacing.FullReflectionPositivityFromContinuousLocal
end
