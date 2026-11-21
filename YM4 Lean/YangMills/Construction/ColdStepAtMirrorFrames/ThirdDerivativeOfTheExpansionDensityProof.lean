import YangMills.Construction.ColdStepAtMirrorFrames.DensityNearTheFrameProof
import YangMills.Construction.ColdStepAtMirrorFrames.ThirdDerivativeOfTheExpansionDensity
import YangMills.Construction.SummableBoundsOfTheFlow.MeanOnASegmentIsSmooth
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology
namespace YangMills.Construction
open BlockAverages FamilyNorms GibbsInterpolation BlockMeans Estimates TorusFields
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
namespace StepDensityThirdDeriv
private theorem eventually_isSmallCurvature (hfin : Finite F.Cell) {s : ℝ} {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) {V : F.GaugeField F.top}
    (hV : IsSmallCurvature s V) :
    ∀ᶠ τ : Fin k → ℝ in 𝓝 0, IsSmallCurvature s (leftTranslate (bondSpread c X τ) V) := by apply _root_.YangMills.SharedProofs.p38544 <;> assumption
private theorem gibbsMean_congr_ae {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {A A' H H' : Ω → ℝ}
    (hA : A =ᵐ[μ] A') (hH : H =ᵐ[μ] H') : gibbsMean μ A H = gibbsMean μ A' H' := by apply _root_.YangMills.Construction.InterpolatedBirths.gibbsMean_congr_ae <;> assumption
private theorem stepExponent_eq_sub (a ρA x : ℝ) (m : ℕ) (f : LocalFamily) (ν : ℝ) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) :
    stepExponent false a ρA x m f ν V η = stepExponent false a ρA x m (fun _ _ _ => 0) 0 V η -
      ν * ∑ y ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion false a ρA m f y η V := by
  simp [stepExponent]
private theorem stepExponent_smul (a ρA x : ℝ) (m : ℕ) (f : LocalFamily) (ν : ℝ) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) :
    stepExponent false a ρA x m (ν • f) 1 V η = stepExponent false a ρA x m f ν V η := by
  have hrow : ∀ y, centredExpansion false a ρA m (ν • f) y η V = ν * centredExpansion false a ρA m f y η V := fun y => by
    simp [centredExpansion, subtractTrivial, mul_sub]
  simp only [stepExponent, hrow, one_mul, ← Finset.mul_sum]
private theorem isNormBoundedLocalFamily_smul {L t n₀ : ℕ} {σ δ E E₃ ν : ℝ} {f : LocalFamily}
    (hf : IsRegularFamily L t n₀ σ δ E E₃ f) (h0 : 0 ≤ ν) (h1 : ν ≤ 1) :
    IsNormBoundedLocalFamily L t n₀ σ δ E E₃ (ν • f) := by apply _root_.YangMills.SharedProofs.p82607 <;> assumption
private theorem abs_bondDeriv_expansionDensity_le {a ρA ρ x κ δ E E₃ C s D : ℝ} {L m k : ℕ} {p : ℝ → ℝ}
    {f : LocalFamily} {V : F.GaugeField F.top} (hρ : 0 < ρ) (hcut : IsCutoff ρ p) (hfin : Finite F.Cell)
    (hRim : CutoffMeanIsGibbsMean) (hSeg : InterpolatedGibbsMeanSmooth)
    (hE : ∀ V' : F.GaugeField F.top, IsSmallCurvature s V' → CellExponentBounds false a ρA ρ x κ C m V')
    (hR : CentredExpansionBounds false a ρA ρ κ δ E E₃ C L m f V) (hV : IsSmallCurvature s V) (Y : F.Cell)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (hk : k ≤ 3) (M : ℝ → F.GaugeField F.top → ℝ)
    (hM : ∀ v V', M v V' = cutoffMean ρ p (stepExponent false a ρA x m f v V') fun η =>
      cellCentredExpansion false a ρA m f Y η V')
    (hb : ∀ v ∈ Set.Icc (0 : ℝ) 1, |bondDeriv (M v) V c X| ≤ D) :
    |bondDeriv (expansionDensity false a ρA ρ x m p f Y) V c X| ≤ D := by
  classical
  obtain ⟨hfinμ, hμ0, hμb, hμm⟩ := hRim F ρ p hρ hcut
  have := hfinμ
  set μ := cutoffLaw F ρ p with hμ
  have hμc : ∀ᵐ η ∂μ, ∀ b, ‖η b‖ ≤ ρ := by
    filter_upwards [hμb] with η hη b using (hη b).le
  set Vt : (Fin k → ℝ) → F.GaugeField F.top := fun τ => leftTranslate (bondSpread c X τ) V with hVt
  set A : (Fin k → ℝ) × StepVariable (finiteCells F) → ℝ := fun z =>
    ∑ Y' ∈ finiteCells F, cellExponent false a ρA x m Y' (Vt z.1) z.2 with hA
  set R : (Fin k → ℝ) × StepVariable (finiteCells F) → ℝ := fun z =>
    ∑ y ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion false a ρA m f y z.2 (Vt z.1) with hRdef
  set H : (Fin k → ℝ) × StepVariable (finiteCells F) → ℝ := fun z =>
    cellCentredExpansion false a ρA m f Y z.2 (Vt z.1) with hH
  have hEV := hE V hV
  have hsm : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ ρ) →
      ContDiffAt ℝ 3 A (0, η) ∧ ContDiffAt ℝ 3 R (0, η) ∧ ContDiffAt ℝ 3 H (0, η) := fun η hη => by
    refine ⟨ContDiffAt.sum fun Y' _ => hEV.smooth Y' η k c X hη,
      ContDiffAt.sum fun y _ => hR.smooth y η k c X hη, ?_⟩
    have : H = fun z => ∑ y ∈ (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y),
        centredExpansion false a ρA m f y z.2 (Vt z.1) := by
      funext z
      simp only [hH, cellCentredExpansion]
    rw [this]
    exact ContDiffAt.sum fun y _ => hR.smooth y η k c X hη
  obtain ⟨-, -, hs₃⟩ := hSeg _ k ρ μ A R H hμ0 hμc hsm
  have heq : ∀ᶠ τ : Fin k → ℝ in 𝓝 0, ∀ v : ℝ, M v (Vt τ) = interpolatedGibbsMean μ A R H v τ := by
    filter_upwards [eventually_isSmallCurvature hfin c X hV] with τ hτ v
    rw [hM, hμm]
    unfold interpolatedGibbsMean
    apply gibbsMean_congr_ae
    · filter_upwards [hμb] with η hη
      rw [stepExponent_eq_sub, (hE (Vt τ) hτ).sum_eq η hη]
    · exact Filter.EventuallyEq.rfl
  have hev : ∀ v : ℝ, (fun τ : Fin k → ℝ => M v (Vt τ)) =ᶠ[𝓝 0] interpolatedGibbsMean μ A R H v := fun v => by
    filter_upwards [heq] with τ hτ using hτ v
  have hint : (fun τ : Fin k → ℝ => expansionDensity false a ρA ρ x m p f Y (Vt τ)) =ᶠ[𝓝 0]
      fun τ => ∫ v in (0 : ℝ)..1, interpolatedGibbsMean μ A R H v τ := by
    filter_upwards [heq] with τ hτ
    unfold expansionDensity
    exact intervalIntegral.integral_congr fun v _ => (hM v (Vt τ)).symm.trans (hτ v)
  set e : Fin k → Fin k → ℝ := fun l => Pi.single l 1 with he
  obtain ⟨-, hi⟩ := hs₃ k hk e
  have d1 : bondDeriv (expansionDensity false a ρA ρ x m p f Y) V c X =
      ∫ v in (0 : ℝ)..1, iteratedFDeriv ℝ k (interpolatedGibbsMean μ A R H v) 0 e := by
    show iteratedFDeriv ℝ k (fun τ => expansionDensity false a ρA ρ x m p f Y (Vt τ)) 0 e = _
    rw [(Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hint k).self_of_nhds]
    exact hi
  have d2 : ∀ v, bondDeriv (M v) V c X = iteratedFDeriv ℝ k (interpolatedGibbsMean μ A R H v) 0 e := fun v => by
    show iteratedFDeriv ℝ k (fun τ => M v (Vt τ)) 0 e = _
    rw [(Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) (hev v) k).self_of_nhds]
  rw [d1]
  have hbd := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1) (C := D)
    (f := fun v => iteratedFDeriv ℝ k (interpolatedGibbsMean μ A R H v) 0 e) (fun v hv => by
      have hv' : v ∈ Set.Icc (0 : ℝ) 1 := by
        rw [Set.uIoc_of_le zero_le_one] at hv
        exact Set.Ioc_subset_Icc_self hv
      have h1 := hb v hv'
      rw [d2 v] at h1
      exact h1)
  simpa using hbd
private def ThirdDerivBoundAt (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (C : ℝ) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily), T.coupling ≤ x → IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f →
    ∀ F, IsCubicTopTorus T.L t T.n₀ F → ∀ (Y : F.Cell) (V : F.GaugeField F.top) (c : Fin 3 → F.Site F.top × Fin 4)
      (X : Fin 3 → imaginaryQuaternions), IsSmallCurvature (5 / 4 * T.σ) V → AreUnitVectors X →
      |bondDeriv (stepDensityFamily T x f F Y) V c X| ≤
        2⁻¹ ^ 6 * T.energyRatio / torusDecayFactor T.L T.decayRate (bondSpan Y c) +
          C * x ^ (-(1 / 2 : ℝ)) * Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y c))
private theorem thirdDerivBound_of_means (hRim : CutoffMeanIsGibbsMean)
    (hSeg : InterpolatedGibbsMeanSmooth) (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (hT : T.IsOrdered) (hn : 2 ≤ T.n₀)
    (hO : SingleTorusMeanBoundsAt T) (hX : CellExponentsBoundedAt T)
    (hR : CentredExpansionsBoundedAt T) : ThirdDerivBoundAt T (T.CE * T.E) := by
  intro t x f hx hf F hF Y V c X hV hU
  have hρ : 0 < T.ballRadius := by
    have := hT.σ_pos
    show 0 < T.σ / 64
    positivity
  have hfin : Finite F.Cell := by
    obtain ⟨-, -, n, hside, hn'⟩ := hF
    have hper : ∀ i, F.period F.top i = F.extent i := fun i => by simp [BlockFrame.period]
    have hne : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by
      rw [hper, hside]
      omega⟩
    exact Pi.finite
  have hE0 : 0 < T.E := by linarith [hT.one_le_E]
  have hMc : ∀ v ∈ Set.Icc (0 : ℝ) 1, SingleTorusMeanBounds false T.a T.chainParams.ρA T.σ x T.κ T.decayRate T.E
      (T.E / T.η₃) T.CE T.L t T.n₀ (frameRadius x) T.p (v • f) f := fun v hv =>
    hO t x (v • f) f T.E false hx hE0 (isNormBoundedLocalFamily_smul hf hv.1 hv.2) hf
  refine abs_bondDeriv_expansionDensity_le (a := T.a) (ρA := T.chainParams.ρA) (ρ := T.ballRadius) (x := x) (m := frameRadius x)
    (p := T.p) (f := f) hρ hT.cutoff hfin hRim hSeg
    (fun V' hV' => (hX t x F V' false hx hF hV').1) (hR t x f F V false hx hf hF hV) hV Y c X le_rfl
    (fun v => conditionalExpansionMean false T.a T.chainParams.ρA (T.σ / 64) x (frameRadius x) T.p (v • f) f F Y)
    (fun v V' => ?_) (fun v hv => ?_)
  · show cutoffMean T.ballRadius T.p (stepExponent false T.a T.chainParams.ρA x (frameRadius x) (v • f) 1 V') _ = _
    congr 1
    funext η
    exact stepExponent_smul _ _ _ _ _ _ _ _
  · have h := (hMc v hv).decay F hF Y V 3 c X hV (by norm_num) le_rfl hU
    beta_reduce at h
    rw [if_pos rfl] at h
    exact h
private theorem eventuallyInParameters_of_rescale {Q' Q : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → Prop}
    (h : ∀ T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters, 1 ≤ T.E → Q' { T with CE := T.CE / T.E } → Q T) (hq : EventuallyInParameters Q') :
    EventuallyInParameters Q := by apply _root_.YangMills.SharedProofs.p51044 <;> assumption
end StepDensityThirdDeriv
open StepDensityThirdDeriv in
theorem stepDensityThirdDerivStatement_holds (hJ : EventuallyInParametersCombines)
    (hO : singleTorusMeanStatement) (hX : CellExponentsBounded)
    (hR : CentredExpansionsBounded) (hRim : CutoffMeanIsGibbsMean)
    (hSeg : InterpolatedGibbsMeanSmooth) : stepDensityThirdDerivStatement := by
  obtain ⟨join, weaken⟩ := hJ
  have h2 : EventuallyInParameters fun T => 2 ≤ T.n₀ := fun _ _ => ⟨0, fun _ _ _ _ _ => ⟨0, fun _ _ =>
    ⟨1, one_pos, fun _ _ _ => ⟨1, one_pos, fun _ _ _ _ => ⟨0, fun _ _ => ⟨1, one_pos,
      fun _ _ _ _ _ => ⟨0, fun _ _ _ _ => ⟨2, fun _ h => ⟨0, fun _ _ => ⟨0, fun _ _ => h⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have base : EventuallyInParameters fun T => ThirdDerivBoundAt T (T.CE * T.E) :=
    weaken _ _ (fun T hT h => thirdDerivBound_of_means hRim hSeg T hT h.1 h.2.1 h.2.2.1 h.2.2.2)
      (join _ _ h2 (join _ _ hO (join _ _ hX hR)))
  refine eventuallyInParameters_of_rescale (Q' := fun T => ThirdDerivBoundAt T (T.CE * T.E)) (fun T hE h => ?_) base
  have hE0 : T.E ≠ 0 := by
    have : 0 < T.E := by linarith
    exact this.ne'
  have h1 : ThirdDerivBoundAt T (T.CE / T.E * T.E) := h
  rw [div_mul_cancel₀ _ hE0] at h1
  exact h1
end ColdStepAtMirrorFrames
end YangMills.Construction
end
