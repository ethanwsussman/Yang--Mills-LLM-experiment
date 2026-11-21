import YangMills.Construction.ColdStepAtMirrorFrames.CurvesOfTheFrames
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionNearAFlatTopProof
import YangMills.Construction.ColdStepAtMirrorFrames.TopFamiliesReadOnTori
import YangMills.Construction.ColdStepAtMirrorFrames.ZeroFamilyIsAnExpansion
import YangMills.Construction.RunningCouplingSlope.ContoursAtTheLeastFieldHaveKernelsProof
import YangMills.Construction.SummableBoundsOfTheFlow.ParityOfTheScaledMeans
import YangMills.Construction.SummableBoundsOfTheFlow.TheBirthsBetween
import YangMills.Construction.SummableBoundsOfTheFlow.TheDensitiesAreMeansAtAScale
import YangMills.Construction.SummableBoundsOfTheFlow.TheDensitiesAtTheScaleZero
import YangMills.Construction.SummableBoundsOfTheFlow.TheDensityOfTheStepHasItsLowOrders
import YangMills.Construction.SummableBoundsOfTheFlow.TheMeansMoveWithTheirWeight
import YangMills.Construction.SummableBoundsOfTheFlow.TheScaledPartsAreSmooth
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation ScaledVariables StepDensities TorusComparison MeasureTheory Filter
open scoped Topology
namespace ScaleZeroLimit
variable {F F' : BlockFrame}
private def zeroFamily : LocalFamily := fun _ _ _ => 0
private theorem bondDeriv_zero_order {j : ℕ} (G : F.GaugeField j → ℝ) (W : F.GaugeField j)
    (c : Fin 0 → F.Site j × Fin 4) (X : Fin 0 → imaginaryQuaternions) : bondDeriv G W c X = G W := by apply _root_.YangMills.SharedProofs.p8307 <;> assumption
private theorem bondDeriv_congr {j k : ℕ} {G G' : F.GaugeField j → ℝ} {W : F.GaugeField j}
    {c : Fin k → F.Site j × Fin 4} {X : Fin k → imaginaryQuaternions}
    (h : ∀ᶠ τ : Fin k → ℝ in 𝓝 0, G (leftTranslate (bondSpread c X τ) W) = G' (leftTranslate (bondSpread c X τ) W)) :
    bondDeriv G W c X = bondDeriv G' W c X := by
  unfold bondDeriv
  have e : (fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) W)) =ᶠ[𝓝 0]
      fun τ => G' (leftTranslate (bondSpread c X τ) W) := h
  rw [(Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) e k).eq_of_nhds]
private theorem bondDeriv_neg {j k : ℕ} (G : F.GaugeField j → ℝ) (W : F.GaugeField j)
    (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions) :
    bondDeriv (fun W' => -G W') W c X = -bondDeriv G W c X := by
  unfold bondDeriv
  have e := iteratedFDeriv_neg_apply (𝕜 := ℝ) (i := k)
    (f := fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) W)) (x := 0)
  exact congrArg (fun A => A fun l => Pi.single l 1) e
private theorem isSmallCurvature_mono {j : ℕ} {s s' : ℝ} (h : s ≤ s') {V : F.GaugeField j}
    (hV : IsSmallCurvature s V) : IsSmallCurvature s' V := fun p hp => (hV p hp).trans_le h
private theorem eventually_isSmallCurvature_leftTranslate {k : ℕ} (hs : ∀ i, 1 ≤ F.extent i) {s : ℝ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) {V : F.GaugeField F.top}
    (hV : IsSmallCurvature s V) :
    ∀ᶠ τ : Fin k → ℝ in 𝓝 0, IsSmallCurvature s (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V) := by
  have hne : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by
    simp only [BlockFrame.period, Nat.sub_self, pow_zero, mul_one]
    have := hs i
    omega⟩
  have hfin : Finite F.Cell := by
    have : ∀ i, Finite (ZMod (F.period F.top i)) := fun i => by
      have := hne i
      exact inferInstance
    exact Pi.finite
  have hf : Finite (F.Site F.top × Fin 4 × Fin 4) := inferInstance
  exact show ∀ᶠ τ : Fin k → ℝ in 𝓝 0, ∀ p : F.Site F.top × Fin 4 × Fin 4, p.2.1 < p.2.2 →
      plaquetteDefect (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V) p < s from by
    rw [Filter.eventually_all]
    intro p
    by_cases hp : p.2.1 < p.2.2
    · have h2 : plaquetteDefect (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X 0) V) p < s := by
        rw [FrameCurves.leftTranslate_bondSpread_zero]
        exact hV p hp
      filter_upwards [(FrameCurves.continuous_plaquetteDefect c X V p).continuousAt.eventually_lt
        continuousAt_const h2] with τ hτ _ using hτ
    · exact Filter.Eventually.of_forall fun τ h => absurd h hp
abbrev _root_.YangMills.SharedProofs.p42166 := @eventually_isSmallCurvature_leftTranslate
private theorem isSmallCurvature_gaugeTransform {s : ℝ} (γ : F.Cell → UnitQuaternion) {V : F.GaugeField F.top}
    (hV : IsSmallCurvature s V) : IsSmallCurvature s (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.NearFlatExpansion.isSmallCurvature_gaugeTransform <;> assumption
private theorem isSmallCurvature_translateField {s : ℝ} (h : F.Cell) {V : F.GaugeField F.top}
    (hV : IsSmallCurvature s V) : IsSmallCurvature s (translateField h V) := by
  rintro ⟨x, μ, ν⟩ hp
  have hc := hV (x - h, μ, ν) hp
  unfold plaquetteDefect at hc ⊢
  have e : plaquetteHolonomy (translateField h V) (x, μ, ν) = plaquetteHolonomy V (x - h, μ, ν) := by
    simp only [plaquetteHolonomy, pathHolonomy, linkValue, stepDisplacement, if_true, Bool.false_eq_true, if_false,
      translateField, add_sub_right_comm, sub_right_comm x (unitStep F.top μ) h, sub_right_comm x (unitStep F.top ν) h]
  rw [e]
  exact hc
private theorem interpolatedCoords_zero (a ρA : ℝ) (m : ℕ) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) :
    interpolatedCoords 0 a ρA m V η = coordsAboveFrame true a ρA 0 V η := by apply _root_.YangMills.SharedProofs.p718 <;> assumption
private theorem interpolatedBirthAt_zero (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (x : ℝ) (F : BlockFrame) (Y : F.Cell)
    (V : F.GaugeField F.top) (f : LocalFamily) :
    interpolatedBirthAt T x 0 F Y V = interactionDensity true T.a T.ρA T.ballRadius T.lam x 0 T.p f Y V := by
  have e1 : ∀ τ : ℝ, weightLawExponent 0 T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) τ V =
      fun η => τ * stepExponent true T.a T.ρA x 0 f 0 V η + (1 - τ) * totalQuadratic T.lam x η := by
    intro τ
    funext η
    simp only [weightLawExponent, interpolatedExponent, stepExponent, interpolatedField, fieldAboveFrame,
      interpolatedCoords_zero, zero_mul, sub_zero]
    rfl
  have e2 : cellExponentRemainder 0 T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) Y V =
      fun η => cellExponent true T.a T.ρA x 0 Y V η - cellQuadratic T.lam x Y η := by
    funext η
    simp only [cellExponentRemainder, interpolatedBlockExponent, cellExponent, interpolatedField, fieldAboveFrame,
      interpolatedCoords_zero]
    rfl
  unfold interpolatedBirthAt interpolatedBirth interactionDensity
  simp only [e1, e2]
private theorem zeroFamily_bounded (hz : ZeroFamilyIsRegular) {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} (hT : T.IsOrdered) (t : ℕ) :
    T.IsBoundedFamilyOrderSix (fun _ => 0) t zeroFamily := by
  have hE : 0 ≤ T.E := zero_le_one.trans hT.one_le_E
  have hE₃ : 0 ≤ T.energyRatio := div_nonneg hE hT.η₃_pos.le
  have r := hz T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio hE hE₃
  refine ⟨⟨r.smooth, r.gauge_invariant, r.translation_invariant, r.decay, r.locality⟩, ⟨?_, ?_, ?_⟩⟩
  · intro F _ y W _ j c X
    exact contDiffAt_const
  · intro F _ y W γ _
    rfl
  · intro F _ y W j c X _ _ _ _
    have e : bondDeriv (zeroFamily F y) W c X = 0 := by
      unfold bondDeriv zeroFamily
      rw [iteratedFDeriv_fun_zero]
      rfl
    rw [e]
    simp
private structure CloseToGaussianLimit (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (l₁ D : ℝ) : Prop where
  pos : 0 < l₁
  bound : ∀ (t : ℕ) (F : BlockFrame) (Y : F.Cell) (V : F.GaugeField F.top), IsCubicTopTorus T.L t T.n₀ F →
    IsSmallCurvature (5 / 4 * T.σ) V → ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
    k ≤ 3 → AreUnitVectors X → ∀ l : ℝ, 0 < l → l ≤ l₁ →
    |bondDeriv (interpolatedBirthAt T (l⁻¹ ^ 2) 0 F Y) V c X -
      bondDeriv (ReferenceDensity.stepDensity T.a T.ρA T.lam Y) V c X| ≤ D * l ^ 2
  regular : ∀ (t : ℕ) (F : BlockFrame) (Y : F.Cell) (V : F.GaugeField F.top), IsCubicTopTorus T.L t T.n₀ F →
    IsSmallCurvature (5 / 4 * T.σ) V → ContDiffThreeAlongBonds (ReferenceDensity.stepDensity T.a T.ρA T.lam Y) V
private theorem one_le_extent {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {t : ℕ} (hn : 1 ≤ T.n₀) (h : IsCubicTopTorus T.L t T.n₀ F) :
    ∀ i, 1 ≤ F.extent i := by
  obtain ⟨_, _, n, hs, hle⟩ := h
  intro i
  rw [hs i]
  omega
private theorem closeToGaussianLimit (hz : ZeroFamilyIsRegular) (hP : scaledMeanParity)
    (hZ : DensitiesAtScaleZero) (hM : DensitiesAreRescaledMeans)
    (hW : meansDifferentiableInWeightStatement) (hS : rescaledPartsSmoothStatement) :
    EventuallyOrdered fun T => ∃ l₁ D : ℝ, CloseToGaussianLimit T l₁ D := by
  refine EventuallyOrdered.mono ((((hP.and hZ).and hM).and hW).and hS) ?_
  rintro T hT hn ⟨⟨⟨⟨p, z⟩, m⟩, w⟩, s⟩
  obtain ⟨lp, C, hlp, hC, p⟩ := p fun _ => 0
  obtain ⟨lm, hlm, m⟩ := m
  obtain ⟨lw, hlw, w⟩ := w fun _ => 0
  obtain ⟨ls, K, hls, hK, s⟩ := s fun _ => 0
  have hl₀ : 0 < min (min lp lm) (min lw ls) := lt_min (lt_min hlp hlm) (lt_min hlw hls)
  have hl₀p : min (min lp lm) (min lw ls) ≤ lp := (min_le_left _ _).trans (min_le_left _ _)
  have hl₀m : min (min lp lm) (min lw ls) ≤ lm := (min_le_left _ _).trans (min_le_right _ _)
  have hl₀w : min (min lp lm) (min lw ls) ≤ lw := (min_le_right _ _).trans (min_le_left _ _)
  have hl₀s : min (min lp lm) (min lw ls) ≤ ls := (min_le_right _ _).trans (min_le_right _ _)
  generalize min (min lp lm) (min lw ls) = l₂ at hl₀ hl₀p hl₀m hl₀w hl₀s
  obtain ⟨l₁, hl₁, hl₁p, hl₁m, hl₁w, hl₁s, hl₁d⟩ : ∃ l₁ : ℝ, 0 < l₁ ∧ l₁ ≤ lp ∧ l₁ ≤ lm ∧ l₁ ≤ lw ∧ l₁ ≤ ls ∧
      2 * l₁ ≤ ls :=
    ⟨l₂ / 2, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
  refine ⟨l₁, C * K, hl₁, ?_, ?_⟩
  · intro t F Y V htop hV k c X hk hX l hl0 hl1
    have hfam := zeroFamily_bounded hz hT t
    have hs := one_le_extent hn htop
    have hsm : IsSmoothAtSmallCurvature (5 / 4 * T.σ) T.κ T.ballRadius l₁ K Y
        fun l ζ V' => rescaledCellRemainder T.a T.ρA T.lam l Y V' ζ :=
      fun V' hV' => (s l₁ hl₁ hl₁s t zeroFamily F V' Y hfam htop hV').1
    have hsd : IsSmoothAtSmallCurvature (5 / 4 * T.σ) T.κ T.ballRadius (2 * l₁) K Y
        fun l ζ V' => rescaledCellRemainder T.a T.ρA T.lam l Y V' ζ :=
      fun V' hV' => (s (2 * l₁) (by positivity) hl₁d t zeroFamily F V' Y hfam htop hV').1
    have hmv := w l₁ hl₁ hl₁w t zeroFamily F V Y StepLaw.interpolated K _ k c X hfam htop hV (Or.inr rfl) hK hsm hX
    obtain ⟨hsc, hze⟩ := hmv.1 hk
    have hsc := hsc l hl0 hl1
    have eZ := hze.deriv_integral_eq
    have eS := hsc.deriv_integral_eq
    have gZ : bondDeriv (ReferenceDensity.stepDensity T.a T.ρA T.lam Y) V c X =
        -∫ θ in (0 : ℝ)..1, bondDeriv (observableGaussianMean T.a T.ρA T.lam zeroFamily (.interpolated θ)
          (fun l ζ V' => rescaledCellRemainder T.a T.ρA T.lam l Y V' ζ)) V c X := by
      rw [← eZ, ← bondDeriv_neg]
      refine bondDeriv_congr ?_
      filter_upwards [eventually_isSmallCurvature_leftTranslate hs c X hV] with τ hτ
      exact ((z t zeroFamily F _ Y htop hτ).1).symm
    have gS : bondDeriv (interpolatedBirthAt T (l⁻¹ ^ 2) 0 F Y) V c X =
        -∫ θ in (0 : ℝ)..1, bondDeriv (observableMean T.a T.ρA T.ballRadius T.lam T.p zeroFamily (.interpolated θ)
          (fun l ζ V' => rescaledCellRemainder T.a T.ρA T.lam l Y V' ζ) l) V c X := by
      rw [← eS, ← bondDeriv_neg]
      refine bondDeriv_congr ?_
      filter_upwards [eventually_isSmallCurvature_leftTranslate hs c X hV] with τ hτ
      rw [interpolatedBirthAt_zero T _ F Y _ zeroFamily]
      exact (m t F _ zeroFamily l Y htop hτ hl0 ((hl1.trans hl₁m))).2.2.1
    rw [gS, gZ, neg_sub_neg, ← intervalIntegral.integral_sub hze.integrable hsc.integrable]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1) (C := C * K * l ^ 2)
      (f := fun θ => bondDeriv (observableGaussianMean T.a T.ρA T.lam zeroFamily (.interpolated θ)
          (fun l ζ V' => rescaledCellRemainder T.a T.ρA T.lam l Y V' ζ)) V c X -
        bondDeriv (observableMean T.a T.ρA T.ballRadius T.lam T.p zeroFamily (.interpolated θ)
          (fun l ζ V' => rescaledCellRemainder T.a T.ρA T.lam l Y V' ζ) l) V c X) ?_
    · simpa using hb
    · intro θ hθ
      rw [Set.uIoc_of_le zero_le_one] at hθ
      have hpar := p l₁ hl₁ hl₁p t zeroFamily F V Y (.interpolated θ) K _ k c X hfam htop hV
        ⟨hθ.1.le, hθ.2⟩ hK hsd hX
      have hn' := hpar.sub_gaussianMean_le hk l hl0 hl1
      have hexp : Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y c)) ≤ 1 := by
        refine Real.exp_le_one_iff.mpr ?_
        have := hT.κ_pos
        have : 0 ≤ T.κ / 2 ^ 6 * (bondSpan Y c : ℝ) := by positivity
        linarith
      have hCK : 0 ≤ C * K * l ^ 2 := by positivity
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact hn'.trans (by nlinarith)
  · intro t F Y V htop hV k c X
    have hfam := zeroFamily_bounded hz hT t
    have hs := one_le_extent hn htop
    have hsm : IsSmoothAtSmallCurvature (5 / 4 * T.σ) T.κ T.ballRadius l₁ K Y
        fun l ζ V' => rescaledCellRemainder T.a T.ρA T.lam l Y V' ζ :=
      fun V' hV' => (s l₁ hl₁ hl₁s t zeroFamily F V' Y hfam htop hV').1
    have hmv := w l₁ hl₁ hl₁w t zeroFamily F V Y StepLaw.interpolated K _ 0 Fin.elim0 Fin.elim0 hfam htop hV
      (Or.inr rfl) hK hsm (fun l => l.elim0)
    have hreg := ((hmv.1 (by omega)).2).contDiff k c X
    refine hreg.neg.congr_of_eventuallyEq ?_
    filter_upwards [eventually_isSmallCurvature_leftTranslate hs c X hV] with τ hτ
    exact ((z t zeroFamily F _ Y htop hτ).1).symm
private theorem tendsto_bondDeriv_birth {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {l₁ D : ℝ} (h : CloseToGaussianLimit T l₁ D) {t : ℕ}
    {F : BlockFrame} (Y : F.Cell) {V : F.GaugeField F.top} (htop : IsCubicTopTorus T.L t T.n₀ F)
    (hV : IsSmallCurvature (5 / 4 * T.σ) V)
    {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (hk : k ≤ 3) (hX : AreUnitVectors X) :
    Tendsto (fun l : ℝ => bondDeriv (interpolatedBirthAt T (l⁻¹ ^ 2) 0 F Y) V c X) (𝓝[>] 0)
      (𝓝 (bondDeriv (ReferenceDensity.stepDensity T.a T.ρA T.lam Y) V c X)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hz : Tendsto (fun l : ℝ => D * l ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have : Continuous fun l : ℝ => D * l ^ 2 := by fun_prop
    have h0 := this.tendsto 0
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hz
  filter_upwards [Ioc_mem_nhdsGT h.pos] with l hl
  exact h.bound t F Y V htop hV k c X hk hX l hl.1 hl.2
private theorem tendsto_birth {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {l₁ D : ℝ} (h : CloseToGaussianLimit T l₁ D) {t : ℕ}
    {F : BlockFrame} (Y : F.Cell) {V : F.GaugeField F.top} (htop : IsCubicTopTorus T.L t T.n₀ F)
    (hV : IsSmallCurvature (5 / 4 * T.σ) V) :
    Tendsto (fun l : ℝ => interpolatedBirthAt T (l⁻¹ ^ 2) 0 F Y V) (𝓝[>] 0)
      (𝓝 (ReferenceDensity.stepDensity T.a T.ρA T.lam Y V)) := by
  have e := tendsto_bondDeriv_birth h Y htop hV (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)
    (Fin.elim0 : Fin 0 → imaginaryQuaternions) (by omega) (fun l => l.elim0)
  simpa only [bondDeriv_zero_order] using e
private theorem eventually_le_inv_sq (y : ℝ) : ∀ᶠ l : ℝ in 𝓝[>] 0, y ≤ l⁻¹ ^ 2 := by
  have h : Tendsto (fun l : ℝ => l⁻¹ ^ 2) (𝓝[>] 0) atTop :=
    (tendsto_pow_atTop (two_ne_zero)).comp tendsto_inv_nhdsGT_zero
  exact h.eventually_ge_atTop y
theorem stepDensityLowOrder_holds (hB : interpolatedBirthBoundsStatement)
    (hP : scaledMeanParity) (hZ : DensitiesAtScaleZero)
    (hM : DensitiesAreRescaledMeans) (hW : meansDifferentiableInWeightStatement)
    (hS : rescaledPartsSmoothStatement) (hR : TopFamilyOnTori)
    (hz : ZeroFamilyIsRegular) : TorusLumps.stepDensityLowOrderStatement := by
  have hB' : EventuallyOrdered fun T => ∀ (t : ℕ) (x s : ℝ), T.coupling ≤ x → 0 ≤ s → s ≤ 1 →
      InterpolatedBirthBounds T t x s :=
    EventuallyInParameters.mono hB fun T h _ _ => h
  refine EventuallyOrdered.mono (hB'.and (closeToGaussianLimit hz hP hZ hM hW hS)) ?_
  rintro T hT hn ⟨b, l₁, D, h⟩ ℓ hℓ _ t
  have hσ := hT.σ_pos
  have c54 : ∀ {F : BlockFrame} {V : F.GaugeField F.top}, IsSmallCurvature T.σ V →
      IsSmallCurvature (5 / 4 * T.σ) V :=
    isSmallCurvature_mono (by linarith)
  have c98 : ∀ {F : BlockFrame} {V : F.GaugeField F.top}, IsSmallCurvature T.σ V →
      IsSmallCurvature (9 / 8 * T.σ) V :=
    isSmallCurvature_mono (by linarith)
  have birth : ∀ᶠ l : ℝ in 𝓝[>] 0, InterpolatedBirthBounds T t (l⁻¹ ^ 2) 0 := by
    filter_upwards [eventually_le_inv_sq T.coupling] with l hl
    exact b t _ 0 hl le_rfl zero_le_one
  have hdensity : IsLocalDensity T.L t T.n₀ T.σ fun _ Y V => ReferenceDensity.stepDensity T.a T.ρA T.lam Y V := by
    refine ⟨?_, ?_, ?_⟩
    · intro F htop Y V hV
      exact h.regular t F Y V htop (c54 hV)
    · intro F htop Y V γ hV
      refine tendsto_nhds_unique
        ((tendsto_birth h Y htop (c54 (isSmallCurvature_gaugeTransform γ hV))).congr' ?_)
        (tendsto_birth h Y htop (c54 hV))
      filter_upwards [birth] with l hl
      exact hl.isLocalDensity.gauge_invariant F htop Y V γ (c54 hV)
    · intro F htop Y u V hV
      refine tendsto_nhds_unique
        ((tendsto_birth h (Y + u) htop (c54 (isSmallCurvature_translateField u hV))).congr' ?_)
        (tendsto_birth h Y htop (c54 hV))
      filter_upwards [birth] with l hl
      exact hl.isLocalDensity.translation_invariant F htop Y u V (c54 hV)
  have hdecay : DerivDecay T.L t T.n₀ T.σ (fun _ Y V => ReferenceDensity.stepDensity T.a T.ρA T.lam Y V)
      fun _ n => T.Cs * Real.exp (-(T.κ / 2 ^ 6 * n)) := by
    intro F htop Y V k c X hV h1 h3 hX
    refine le_of_tendsto (tendsto_bondDeriv_birth h Y htop (c54 hV) c X h3 hX).abs ?_
    filter_upwards [birth] with l hl
    exact hl.decay F htop Y V k c X (c54 hV) h1 h3 hX
  have hcompare : IsLocalOnTori T.L t T.n₀ T.σ (fun _ Y V => ReferenceDensity.stepDensity T.a T.ρA T.lam Y V)
      fun r => T.Cs * Real.exp (-(T.κ / 2 ^ 9 * r)) := by
    intro F F' htop htop' Y Y' V V' r k e X hV hV' hag hk he hX
    refine le_of_tendsto (((tendsto_bondDeriv_birth h Y htop (c54 hV) (bondsAt Y e) X (by omega) hX).sub
      (tendsto_bondDeriv_birth h Y' htop' (c54 hV') (bondsAt Y' e) X (by omega) hX)).abs) ?_
    filter_upwards [birth] with l hl
    exact hl.isLocalOnTori F F' htop htop' Y Y' V V' r k e X (c98 hV) (c98 hV') hag hk he hX
  obtain ⟨d1, d2, d3, -⟩ := hR T.L t T.n₀ T.σ (fun _ Y V => ReferenceDensity.stepDensity T.a T.ρA T.lam Y V) (by omega)
  obtain ⟨p1, p2, p3⟩ := d1 hdensity
  have q2 := d2 _ hdecay
  have q3 := d3 _ hcompare
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro n _ hn' y W hW
    exact p1 n (hℓ.n₀_eq ▸ hn') y W (hℓ.threshold_eq ▸ hW)
  · intro n _ hn' y g W hW
    exact p2 n (hℓ.n₀_eq ▸ hn') y g W (hℓ.threshold_eq ▸ hW)
  · intro n _ hn' y u W hW
    exact p3 n (hℓ.n₀_eq ▸ hn') y u W (hℓ.threshold_eq ▸ hW)
  · intro n _ hn' y W hW k c X h1 h3 hX
    exact q2 n (hℓ.n₀_eq ▸ hn') y W (hℓ.threshold_eq ▸ hW) k c X h1 h3 hX
  · intro n n' _ _ hn1 hn2 y y' W W' m h1 h2 hW hW' hag k e X hk he hX
    exact q3 n n' (hℓ.n₀_eq ▸ hn1) (hℓ.n₀_eq ▸ hn2) y y' W W' m h1 h2 (hℓ.threshold_eq ▸ hW)
      (hℓ.threshold_eq ▸ hW') hag k e X hk he hX
end ScaleZeroLimit
end YangMills.Construction
end
