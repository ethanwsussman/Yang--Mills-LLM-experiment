import YangMills.Construction.InfiniteLattice.WeakLimitsInvariantFunctionsAndACriterionForErgodicity
import YangMills.Construction.InfiniteLattice.WeakLimitsOfStatesAndACriterionForErgodicity
import YangMills.Construction.InfiniteLattice.WilsonMeasureOfAPeriodLatticeAndItsExtensionAreStatesProof
import YangMills.Construction.ReflectionPositivity.FunctionsOfTheBondsInASet
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ComplexConjugate ComplexOrder Topology
namespace YangMills.Construction.ReflectionPositivity.LatticeAtSpacing
open YangMills.Construction.InfiniteLattice (GaugeField IsSymmetricUnder IsLocalObservable
  IsBoundedObservable LatticeSymmetry regionObservables)
open YangMills.Construction.GibbsAtFixedSpacing (BorelProb continuousLocal)
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes (MirrorPair)
variable {a : ℝ}
theorem isBoundedObservable_actOn (r : LatticeSymmetry a) {H : GaugeField a → ℂ}
    (hH : IsBoundedObservable H) : IsBoundedObservable (r.actOn H) := by apply _root_.YangMills.Construction.InfiniteLattice.LiftedGibbsStates.isBoundedObservable_actOn <;> assumption
theorem memLp_two_of_bounded (μ : BorelProb a) {H : GaugeField a → ℂ}
    (hH : IsBoundedObservable H) : MemLp H 2 μ.1 := by
  have := μ.2
  obtain ⟨C, hC⟩ := hH.2
  exact MemLp.of_bound hH.1.aestronglyMeasurable C (Eventually.of_forall hC)
theorem integrable_norm_sq_of_bounded (μ : BorelProb a) {H : GaugeField a → ℂ}
    (hH : IsBoundedObservable H) : Integrable (fun U => ‖H U‖ ^ 2) μ.1 :=
  (memLp_two_of_bounded μ hH).integrable_norm_pow two_ne_zero
theorem integrable_conj_mul_of_bounded (μ : BorelProb a) {G H : GaugeField a → ℂ}
    (hG : IsBoundedObservable G) (hH : IsBoundedObservable H) :
    Integrable (fun U => conj (G U) * H U) μ.1 := by
  have := μ.2
  obtain ⟨C, hC⟩ := hG.2
  obtain ⟨D, hD⟩ := hH.2
  refine Integrable.of_bound
    ((Complex.continuous_conj.measurable.comp hG.1).mul hH.1).aestronglyMeasurable (C * D)
    (Eventually.of_forall fun U => ?_)
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul (hC U) (hD U) (norm_nonneg _) ((norm_nonneg _).trans (hC U))
theorem l2Norm_eq_sqrt (μ : BorelProb a) (H : GaugeField a → ℂ) :
    l2Norm μ H = √(∫ U, ‖H U‖ ^ 2 ∂μ.1) :=
  (Real.sqrt_eq_rpow _).symm
theorem norm_integral_conj_mul_le_l2Norm (μ : BorelProb a) {G H : GaugeField a → ℂ}
    (hG : IsBoundedObservable G) (hH : IsBoundedObservable H) :
    ‖∫ U, conj (G U) * H U ∂μ.1‖ ≤ l2Norm μ G * l2Norm μ H := by
  have h := integral_mul_norm_le_Lp_mul_Lq (μ := μ.1) (f := G) (g := H) (p := 2) (q := 2)
    Real.HolderConjugate.two_two (by simpa using memLp_two_of_bounded μ hG)
    (by simpa using memLp_two_of_bounded μ hH)
  simp only [Real.rpow_two] at h
  calc ‖∫ U, conj (G U) * H U ∂μ.1‖ ≤ ∫ U, ‖conj (G U) * H U‖ ∂μ.1 :=
        norm_integral_le_integral_norm _
    _ = ∫ U, ‖G U‖ * ‖H U‖ ∂μ.1 := by
        simp only [norm_mul, Complex.norm_conj]
    _ ≤ l2Norm μ G * l2Norm μ H := h
theorem l2Norm_actOn (μ : BorelProb a) {r : LatticeSymmetry a}
    (hsym : IsSymmetricUnder μ.1 r) {H : GaugeField a → ℂ} (hH : IsBoundedObservable H) :
    l2Norm μ (r.actOn H) = l2Norm μ H := by
  have hG : IsBoundedObservable fun U => ((‖H U‖ ^ 2 : ℝ) : ℂ) := by
    obtain ⟨C, hC⟩ := hH.2
    refine ⟨Complex.measurable_ofReal.comp (hH.1.norm.pow_const 2), C ^ 2, fun U => ?_⟩
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hC U) 2
  have h : ((∫ U, ‖H (r.pullbackField U)‖ ^ 2 ∂μ.1 : ℝ) : ℂ) =
      ((∫ U, ‖H U‖ ^ 2 ∂μ.1 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal, ← integral_complex_ofReal]
    exact hsym _ hG
  have h' : ∫ U, ‖H (r.pullbackField U)‖ ^ 2 ∂μ.1 = ∫ U, ‖H U‖ ^ 2 ∂μ.1 :=
    Complex.ofReal_injective h
  rw [l2Norm_eq_sqrt, l2Norm_eq_sqrt]
  exact congrArg _ h'
theorem norm_mirrorReflectionForm_sub_le (P : MirrorPair a) (μ : BorelProb a)
    (hsym : IsSymmetricUnder μ.1 P.reflect) {F F' : GaugeField a → ℂ}
    (hF : IsBoundedObservable F) (hF' : IsBoundedObservable F') :
    ‖mirrorReflectionForm μ P F - mirrorReflectionForm μ P F'‖ ≤
      l2Norm μ (F - F') * (l2Norm μ F + l2Norm μ F') := by
  have hD : IsBoundedObservable (F - F') := by
    obtain ⟨C, hC⟩ := hF.2
    obtain ⟨D, hD⟩ := hF'.2
    exact ⟨hF.1.sub hF'.1, C + D, fun U => (norm_sub_le _ _).trans (add_le_add (hC U) (hD U))⟩
  have hθD := isBoundedObservable_actOn P.reflect hD
  have hθF' := isBoundedObservable_actOn P.reflect hF'
  have hsplit : mirrorReflectionForm μ P F - mirrorReflectionForm μ P F' =
      (∫ U, conj (P.reflect.actOn (F - F') U) * F U ∂μ.1) +
        ∫ U, conj (P.reflect.actOn F' U) * (F - F') U ∂μ.1 := by
    have hθF := isBoundedObservable_actOn P.reflect hF
    change (∫ U, conj (P.reflect.actOn F U) * F U ∂μ.1) -
      (∫ U, conj (P.reflect.actOn F' U) * F' U ∂μ.1) = _
    rw [← integral_sub (integrable_conj_mul_of_bounded μ hθF hF)
        (integrable_conj_mul_of_bounded μ hθF' hF'),
      ← integral_add (integrable_conj_mul_of_bounded μ hθD hF)
        (integrable_conj_mul_of_bounded μ hθF' hD)]
    refine integral_congr_ae (Eventually.of_forall fun U => ?_)
    simp only [LatticeSymmetry.actOn, Pi.sub_apply, map_sub]
    ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have h₁ := norm_integral_conj_mul_le_l2Norm μ hθD hF
  have h₂ := norm_integral_conj_mul_le_l2Norm μ hθF' hD
  rw [l2Norm_actOn μ hsym hD] at h₁
  rw [l2Norm_actOn μ hsym hF'] at h₂
  calc _ ≤ l2Norm μ (F - F') * l2Norm μ F +
        l2Norm μ F' * l2Norm μ (F - F') := add_le_add h₁ h₂
    _ = _ := by ring
theorem integral_norm_sq_le_of_sub (μ : BorelProb a) {F F' : GaugeField a → ℂ}
    (hF : IsBoundedObservable F) (hD : IsBoundedObservable (F - F'))
    (hF' : IsBoundedObservable F') :
    ∫ U, ‖F' U‖ ^ 2 ∂μ.1 ≤
      2 * (∫ U, ‖F U‖ ^ 2 ∂μ.1) + 2 * ∫ U, ‖(F - F') U‖ ^ 2 ∂μ.1 := by
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((integrable_norm_sq_of_bounded μ hF).const_mul 2)
      ((integrable_norm_sq_of_bounded μ hD).const_mul 2)]
  refine integral_mono (integrable_norm_sq_of_bounded μ hF')
    (((integrable_norm_sq_of_bounded μ hF).const_mul 2).add
      ((integrable_norm_sq_of_bounded μ hD).const_mul 2))
    fun U => ?_
  have h : ‖F' U‖ ≤ ‖F U‖ + ‖(F - F') U‖ := by
    have := norm_sub_le (F U) ((F - F') U)
    simpa using this
  simp only
  nlinarith [sq_nonneg (‖F U‖ - ‖(F - F') U‖), norm_nonneg (F' U), norm_nonneg (F U),
    norm_nonneg ((F - F') U)]
theorem mirrorReflectionForm_nonneg (hB : RegionFunctions.RegionFunctionsStatement) (ha : 0 < a)
    (P : MirrorPair a) (μ : BorelProb a) (hsym : IsSymmetricUnder μ.1 P.reflect)
    (hpos : ∀ F ∈ continuousLocal a, F ∈ regionObservables a P.upperHalf →
      0 ≤ mirrorReflectionForm μ P F)
    {F : GaugeField a → ℂ} (hl : IsLocalObservable F) (hF : F ∈ regionObservables a P.upperHalf) :
    0 ≤ mirrorReflectionForm μ P F := by
  obtain ⟨-, ⟨-, -, hside⟩, -, -⟩ := hB a ha P.upperHalf P.upperHalf
  obtain ⟨Q, hQ, hFQ⟩ := (hside F hF.1).mp ⟨hF, hl⟩
  obtain ⟨-, -, -, happrox⟩ := hB a ha (P.upperHalf ∩ Q) (P.upperHalf ∩ Q)
  obtain ⟨-, -, hcont⟩ := happrox μ F hF.1
  obtain ⟨Fn, hFn, hlim⟩ := hcont hFQ
  have hobs : ∀ n, IsBoundedObservable (Fn n) := fun n => (hFn n).2.1
  have hdiff : ∀ n, IsBoundedObservable (F - Fn n) := fun n => by
    obtain ⟨C, hC⟩ := hF.1.2
    obtain ⟨D, hD⟩ := (hobs n).2
    exact ⟨hF.1.1.sub (hobs n).1, C + D,
      fun U => (norm_sub_le _ _).trans (add_le_add (hC U) (hD U))⟩
  have hnn : ∀ n, 0 ≤ mirrorReflectionForm μ P (Fn n) := fun n => by
    obtain ⟨hn, hnl⟩ := (hside _ (hobs n)).mpr ⟨Q, hQ, (hFn n).2⟩
    exact hpos _ ⟨(hFn n).1, hobs n, hnl⟩ hn
  have hm : Tendsto (fun n => ∫ U, ‖(F - Fn n) U‖ ^ 2 ∂μ.1) atTop (𝓝 0) := by
    have h := (Complex.continuous_re.tendsto 0).comp hlim
    refine h.congr fun n => ?_
    change (∫ U, ((‖(F - Fn n) U‖ ^ 2 : ℝ) : ℂ) ∂μ.1).re = _
    rw [integral_complex_ofReal, Complex.ofReal_re]
  set M : ℝ := ∫ U, ‖F U‖ ^ 2 ∂μ.1 with hM
  have hbound : Tendsto (fun n => √(∫ U, ‖(F - Fn n) U‖ ^ 2 ∂μ.1) *
      (l2Norm μ F + √(2 * M + 2 * ∫ U, ‖(F - Fn n) U‖ ^ 2 ∂μ.1))) atTop (𝓝 0) := by
    have h₁ : Tendsto (fun n => √(∫ U, ‖(F - Fn n) U‖ ^ 2 ∂μ.1)) atTop (𝓝 0) := by
      have h₀ := (Real.continuous_sqrt.tendsto 0).comp hm
      rw [Real.sqrt_zero] at h₀
      exact h₀
    have h₂ : Tendsto (fun n => l2Norm μ F + √(2 * M + 2 * ∫ U, ‖(F - Fn n) U‖ ^ 2 ∂μ.1))
        atTop (𝓝 (l2Norm μ F + √(2 * M + 2 * 0))) :=
      tendsto_const_nhds.add ((Real.continuous_sqrt.tendsto _).comp
        (tendsto_const_nhds.add (hm.const_mul 2)))
    simpa using h₁.mul h₂
  have hle : ∀ n, ‖mirrorReflectionForm μ P F - mirrorReflectionForm μ P (Fn n)‖ ≤
      √(∫ U, ‖(F - Fn n) U‖ ^ 2 ∂μ.1) *
        (l2Norm μ F + √(2 * M + 2 * ∫ U, ‖(F - Fn n) U‖ ^ 2 ∂μ.1)) := fun n => by
    refine (norm_mirrorReflectionForm_sub_le P μ hsym hF.1 (hobs n)).trans ?_
    rw [l2Norm_eq_sqrt μ (F - Fn n)]
    refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (Real.sqrt_nonneg _)
    rw [l2Norm_eq_sqrt μ (Fn n)]
    exact Real.sqrt_le_sqrt (integral_norm_sq_le_of_sub μ hF.1 (hdiff n) (hobs n))
  have hconv : Tendsto (fun n => mirrorReflectionForm μ P (Fn n)) atTop
      (𝓝 (mirrorReflectionForm μ P F)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hbound
    rw [norm_sub_rev]
    exact hle n
  exact ge_of_tendsto' hconv hnn
theorem weakLimitsAndErgodicity_holds
    (hW : GibbsAtFixedSpacing.LimitsAndErgodicity.Statement)
    (hB : RegionFunctions.RegionFunctionsStatement) : WeakLimitsAndErgodicity := by
  intro a ha
  refine ⟨(hW a ha).1, fun P μ hsym => ⟨fun F F' hF hF' =>
    norm_mirrorReflectionForm_sub_le P μ hsym hF hF', fun hpos F hl hF =>
    mirrorReflectionForm_nonneg hB ha P μ hsym hpos hl hF⟩, ?_⟩
  intro ρ D hTI hsub hdense hzero
  have h := (hW a ha).2.2.2 ρ D hTI hsub hdense fun A hA =>
    (InfiniteLattice.longRangeOrderParameter_eq_plateauVariance ρ.1 A).symm.trans (hzero A hA)
  exact ⟨⟨⊤, inferInstance, fun v _ => hTI v⟩, h.2.2⟩
end YangMills.Construction.ReflectionPositivity.LatticeAtSpacing
