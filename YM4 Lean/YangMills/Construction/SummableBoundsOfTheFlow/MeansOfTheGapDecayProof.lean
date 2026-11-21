import YangMills.Construction.SummableBoundsOfTheFlow.BlockExpansionHasTheConditionsOfThirdOrderProof
import YangMills.Construction.SummableBoundsOfTheFlow.CumulantsOfExpansionsAtATopProof
import YangMills.Construction.SummableBoundsOfTheFlow.CumulantsOfTheMeanAtATopProof
import YangMills.Construction.SummableBoundsOfTheFlow.ExpansionOfTheMeanOfASlope
import YangMills.Construction.SummableBoundsOfTheFlow.FromTheMirrorFramesToTheLeastFieldProof
import YangMills.Construction.SummableBoundsOfTheFlow.GapLawAtATopFromTheFrames
import YangMills.Construction.SummableBoundsOfTheFlow.MeanAtATopProof
import YangMills.Construction.SummableBoundsOfTheFlow.MeanOfASlopeAtATop
import YangMills.Construction.SummableBoundsOfTheFlow.MeanOfASlopeOfTheCut
import YangMills.Construction.SummableBoundsOfTheFlow.SlopeOfACutHasItsSize
import YangMills.Construction.SummableBoundsOfTheFlow.ThirdOrderOfTheGapObservableForm
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Quaternion RealInnerProductSpace Topology
namespace YangMills.Construction
open MeasureTheory
open BlockAverages hiding bondSpread
open ColdStepAtMirrorFrames Interpolation Cumulants Estimates
namespace BlockMeans.GapMeans
variable {F : BlockFrame}
theorem eventually_isSmallCurvature_leftTranslate {k : ℕ} (hfin : Finite F.Cell) {s : ℝ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) {V : F.GaugeField F.top}
    (hV : IsSmallCurvature s V) :
    ∀ᶠ τ : Fin k → ℝ in 𝓝 0, IsSmallCurvature s (leftTranslate (bondSpread c X τ) V) := by apply _root_.YangMills.Construction.InterpolatedBirths.eventually_isSmallCurvature_translate <;> assumption
theorem bondDeriv_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (G : F.GaugeField F.top → E)
    (W : F.GaugeField F.top) (c : Fin 0 → F.Site F.top × Fin 4) (X : Fin 0 → imaginaryQuaternions) :
    bondDeriv G W c X = G W := by apply _root_.YangMills.Construction.Cumulants.MeanAtTop.bondDeriv_zero <;> assumption
theorem inner_toImaginary (v : BondVector) (w : imaginaryQuaternions) :
    ⟪((toImaginary v : imaginaryQuaternions) : ℍ[ℝ]), (w : ℍ[ℝ])⟫ = ⟪v, _root_.YangMills.Construction.Interpolation.imaginaryCoords w⟫ := by apply _root_.YangMills.Construction.FrameInterpolationProof.inner_toImaginary <;> assumption
theorem norm_imaginaryCoords (w : imaginaryQuaternions) : ‖_root_.YangMills.Construction.Interpolation.imaginaryCoords w‖ = ‖w‖ := by apply _root_.YangMills.SharedProofs.p6124 <;> assumption
def imaginaryCoordsCLM : imaginaryQuaternions →L[ℝ] BondVector :=
  LinearMap.toContinuousLinearMap
    { toFun := _root_.YangMills.Construction.Interpolation.imaginaryCoords
      map_add' := fun u v => by
        ext i
        fin_cases i <;> simp [_root_.YangMills.Construction.Interpolation.imaginaryCoords]
      map_smul' := fun r u => by
        ext i
        fin_cases i <;> simp [_root_.YangMills.Construction.Interpolation.imaginaryCoords] }
theorem imaginaryCoordsCLM_apply (w : imaginaryQuaternions) : imaginaryCoordsCLM w = _root_.YangMills.Construction.Interpolation.imaginaryCoords w := rfl
def blockFrameGap (a ρA : ℝ) (m : ℕ) (Y : F.Cell) (V : F.GaugeField F.top) : StepVariable (finiteCells F) :=
  fun b => if enclosingCell b.1.1 = Y then _root_.YangMills.Construction.Interpolation.imaginaryCoords (frameGap a ρA m b.1 V) else 0
theorem blockGapObservable_eq (a ρA : ℝ) (m : ℕ) (p : ℝ → ℝ) (Y : F.Cell) (V : F.GaugeField F.top) :
    blockGapObservable a ρA m p Y V = fun η => cutoffSlopeAlong p (blockFrameGap a ρA m Y) η V := by
  funext η
  unfold blockGapObservable cutoffSlopeAlong cutoffSlope blockFrameGap
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs with h
  · rw [inner_toImaginary]
  · simp
def cutoffSlopeCLM (p : ℝ → ℝ) (η : StepVariable (finiteCells F)) : StepVariable (finiteCells F) →L[ℝ] ℝ :=
  ∑ b, (deriv p ‖η b‖ * ‖η b‖⁻¹) •
    (innerSL ℝ (η b)).comp (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : ↥(chordBonds (finiteCells F)) => BondVector) b)
theorem cutoffSlopeCLM_apply (p : ℝ → ℝ) (η e : StepVariable (finiteCells F)) :
    cutoffSlopeCLM p η e = cutoffSlope p e η := by
  unfold cutoffSlopeCLM cutoffSlope
  simp [_root_.sum_apply]
theorem fieldDeriv_cutoffSlopeAlong (p : ℝ → ℝ) (e : F.GaugeField F.top → StepVariable (finiteCells F))
    (V : F.GaugeField F.top) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (he : ContDiffAt ℝ k (fun τ : Fin k → ℝ => e (leftTranslate (bondSpread c X τ) V)) 0) :
    fieldDeriv (cutoffSlopeAlong p e) V c X = cutoffSlope p (bondDeriv e V c X) := by
  funext η
  have hco := (cutoffSlopeCLM p η).iteratedFDeriv_comp_left he (i := k) le_rfl
  have h1 : (fun τ : Fin k → ℝ => cutoffSlopeAlong p e η (leftTranslate (bondSpread c X τ) V)) =
      (cutoffSlopeCLM p η) ∘ fun τ : Fin k → ℝ => e (leftTranslate (bondSpread c X τ) V) := by
    funext τ
    simp only [Function.comp, cutoffSlopeCLM_apply, cutoffSlopeAlong]
  unfold fieldDeriv bondDeriv
  rw [h1, hco, ← cutoffSlopeCLM_apply]
  rfl
theorem norm_bondDeriv_blockFrameGap_le (a ρA : ℝ) (m : ℕ) (Y : F.Cell) (V : F.GaugeField F.top) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (b : ↥(chordBonds (finiteCells F)))
    (he : ContDiffAt ℝ k (fun τ : Fin k → ℝ => blockFrameGap a ρA m Y (leftTranslate (bondSpread c X τ) V)) 0)
    (hd : ContDiffAt ℝ k (fun τ : Fin k → ℝ => frameGap a ρA m b.1 (leftTranslate (bondSpread c X τ) V)) 0) :
    ‖bondDeriv (blockFrameGap a ρA m Y) V c X b‖ ≤ if enclosingCell b.1.1 = Y then
      ‖bondDeriv (frameGap a ρA m b.1) V c X‖ else 0 := by
  have hpr := (ContinuousLinearMap.proj (R := ℝ)
    (φ := fun _ : ↥(chordBonds (finiteCells F)) => BondVector) b).iteratedFDeriv_comp_left he (i := k) le_rfl
  have e1 : bondDeriv (blockFrameGap a ρA m Y) V c X b = iteratedFDeriv ℝ k
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ↥(chordBonds (finiteCells F)) => BondVector) b) ∘
        fun τ : Fin k → ℝ => blockFrameGap a ρA m Y (leftTranslate (bondSpread c X τ) V)) 0
        (fun l => Pi.single l 1) := by
    rw [hpr]
    rfl
  rw [e1]
  split_ifs with h
  · have e2 : ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ↥(chordBonds (finiteCells F)) => BondVector) b) ∘
        fun τ : Fin k → ℝ => blockFrameGap a ρA m Y (leftTranslate (bondSpread c X τ) V)) =
        imaginaryCoordsCLM ∘ fun τ : Fin k → ℝ => frameGap a ρA m b.1 (leftTranslate (bondSpread c X τ) V) := by
      funext τ
      simp only [Function.comp, ContinuousLinearMap.proj_apply, blockFrameGap, if_pos h, imaginaryCoordsCLM_apply]
    rw [e2, imaginaryCoordsCLM.iteratedFDeriv_comp_left hd (i := k) le_rfl]
    show ‖imaginaryCoordsCLM (bondDeriv (frameGap a ρA m b.1) V c X)‖ ≤ _
    rw [imaginaryCoordsCLM_apply, norm_imaginaryCoords]
  · have e2 : ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ↥(chordBonds (finiteCells F)) => BondVector) b) ∘
        fun τ : Fin k → ℝ => blockFrameGap a ρA m Y (leftTranslate (bondSpread c X τ) V)) = fun _ => 0 := by
      funext τ
      simp only [Function.comp, ContinuousLinearMap.proj_apply, blockFrameGap, if_neg h]
    rw [e2]
    simp
theorem bondSpan_le_two_mul (Y : F.Cell) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) :
    bondSpan Y c ≤ 2 * bondListDistance Y c := by
  have h1 : ∀ l, cellSupDist Y (c l).1 ≤ bondListDistance Y c := fun l =>
    Finset.le_sup (f := fun l : Fin k => cellSupDist Y (c l).1) (Finset.mem_univ l)
  refine max_le (Finset.sup_le fun l _ => ?_) (Finset.sup_le fun l _ => Finset.sup_le fun l' _ => ?_)
  · have := h1 l
    change cellSupDist Y (c l).1 ≤ _
    omega
  · have h2 := PatchLocality.cellSupDist_triangle (c l).1 Y (c l').1
    have h3 : cellSupDist (c l).1 Y = cellSupDist Y (c l).1 := PatchLocality.cellSupDist_comm _ _
    have h4 := h1 l
    have h5 := h1 l'
    change cellSupDist (c l).1 (c l').1 ≤ _
    omega
section Sizes
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem pow_le_pow_of_abs_le {B B' : ℝ} (q : ℕ) (h : |B| ≤ B') : B ^ q ≤ B' ^ q :=
  (le_abs_self _).trans ((abs_pow B q).le.trans (pow_le_pow_left₀ (abs_nonneg _) h q))
theorem hasLocalSize_mono {ρ x κ h h' : ℝ} {r : ℝ → ℝ} {Ψ Φ : BondField ι → ℝ} {Cz Cz' : ℕ → ℝ} {dZ : ι → ℝ}
    {H : BondField ι → ℝ} (hd : ballDensity r Φ = ballDensity r Ψ) (h0 : 0 ≤ h) (hle : h ≤ h')
    (hC : ∀ q, |Cz q| ≤ Cz' q) (hs : HasLocalSize ρ r Φ Cz x κ h dZ H) : HasLocalSize ρ r Ψ Cz' x κ h' dZ H := by
  obtain ⟨hd1, H₀, hm⟩ := hs
  refine ⟨hd1, H₀, fun q hq => ?_⟩
  obtain ⟨⟨i1, m1⟩, hg⟩ := hm q hq
  have hmean : ∀ u : BondField ι → ℝ, ballExpectation r Φ u = ballExpectation r Ψ u := fun u => by
    simp only [ballExpectation, hd]
  have hC0 := (abs_nonneg _).trans (hC q)
  refine ⟨⟨by rw [← hd]; exact i1, ?_⟩, fun b => ?_⟩
  · rw [← hmean]
    refine m1.trans (pow_le_pow_of_abs_le q ?_)
    rw [abs_mul, abs_of_nonneg h0]
    exact mul_le_mul (hC q) hle h0 hC0
  · obtain ⟨i2, m2⟩ := hg b
    refine ⟨by rw [← hd]; exact i2, ?_⟩
    rw [← hmean]
    refine m2.trans (pow_le_pow_of_abs_le q ?_)
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg x), abs_of_nonneg h0,
      abs_of_nonneg (Real.exp_pos _).le]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    exact mul_le_mul (mul_le_mul_of_nonneg_right (hC q) (Real.sqrt_nonneg x)) hle h0
      (mul_nonneg hC0 (Real.sqrt_nonneg x))
end Sizes
theorem fieldDeriv_bounded (hT : UniformDerivBoundNearCompact) {ρ : ℝ} {V : F.GaugeField F.top}
    {G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ} (hG : JointlyContDiffOnBalls ρ V G) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (hk : k ≤ 3) :
    ∃ D : ℝ, ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ ρ) → |fieldDeriv G V c X η| ≤ D := by apply _root_.YangMills.Construction.Cumulants.ExpansionBound.fieldDeriv_bounded <;> assumption
theorem contDiffAt_slice {ρ : ℝ} {V : F.GaugeField F.top}
    {G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ}
    (hG : JointlyContDiffOnBalls ρ V G) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (hk : k ≤ 3)
    {η : StepVariable (finiteCells F)} (hη : ∀ b, ‖η b‖ ≤ ρ) :
    ContDiffAt ℝ k (fun τ : Fin k → ℝ => G η (leftTranslate (bondSpread c X τ) V)) 0 := by apply _root_.YangMills.Construction.Cumulants.MeanAtTop.contDiffAt_slice <;> assumption
theorem fieldDeriv_sum {α : Type} (S : Finset α) (G : α → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
    {V : F.GaugeField F.top} {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (η : StepVariable (finiteCells F))
    (hG : ∀ a ∈ S, ContDiffAt ℝ k (fun τ : Fin k → ℝ => G a η (leftTranslate (bondSpread c X τ) V)) 0) :
    fieldDeriv (fun η V' => ∑ a ∈ S, G a η V') V c X η = ∑ a ∈ S, fieldDeriv (G a) V c X η := by apply _root_.YangMills.Construction.Cumulants.MeanAtTop.fieldDeriv_sum <;> assumption
theorem fieldDeriv_continuousOn (hS : SmoothSlices.IteratedFDerivSlices) {ρ : ℝ} {V : F.GaugeField F.top}
    {G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ} (hG : JointlyContDiffOnBalls ρ V G)
    (c : Fin 3 → F.Site F.top × Fin 4) (X : Fin 3 → imaginaryQuaternions) :
    ContinuousOn (fieldDeriv G V c X) {η | ∀ b, ‖η b‖ < ρ} := by
  intro η hη
  have h3 := hG 3 c X η fun b => (hη b).le
  have h := hS.2.1 (Fin 3 → ℝ) (StepVariable (finiteCells F))
    (fun q => G q.2 (leftTranslate (bondSpread c X q.1) V)) 3 0 (fun l => Pi.single l 1) η
    (by simpa using h3)
  exact (ContDiffAt.continuousAt h).continuousWithinAt
section Linear
variable {ι : Type} [Fintype ι] {ρ : ℝ} {p : ℝ → ℝ} {Φ : BondField ι → ℝ}
theorem ballDensity_eq_zero {η : BondField ι} (h : ¬ ∀ b, ‖η b‖ < ρ) :
    ballDensity (cutoffFactor ρ p) Φ η = 0 := by apply _root_.YangMills.Construction.Interpolation.PartMeanDeriv.ballDensity_eq_zero_of_not_mem <;> assumption
theorem ballDensity_congr {Ψ : BondField ι → ℝ}
    (h : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → Φ η = Ψ η) :
    ballDensity (cutoffFactor ρ p) Φ = ballDensity (cutoffFactor ρ p) Ψ := by
  funext η
  by_cases hη : ∀ b, ‖η b‖ < ρ
  · unfold ballDensity
    rw [h η hη]
  · rw [ballDensity_eq_zero hη, ballDensity_eq_zero hη]
theorem ballExpectation_congr {u u' : BondField ι → ℝ} (h : ∀ η, (∀ b, ‖η b‖ < ρ) → u η = u' η) :
    ballExpectation (cutoffFactor ρ p) Φ u = ballExpectation (cutoffFactor ρ p) Φ u' := by apply _root_.YangMills.Construction.Interpolation.PartMeanDeriv.ballExpectation_congr <;> assumption
theorem ballCovariance_congr {f f' g g' : BondField ι → ℝ} (hf : ∀ η, (∀ b, ‖η b‖ < ρ) → f η = f' η)
    (hg : ∀ η, (∀ b, ‖η b‖ < ρ) → g η = g' η) :
    ballCovariance (cutoffFactor ρ p) Φ f g = ballCovariance (cutoffFactor ρ p) Φ f' g' := by apply _root_.YangMills.Construction.Cumulants.MeanAtTop.ballCovariance_congr <;> assumption
theorem ballCovariance_sum {α : Type} (S : Finset α) (f : BondField ι → ℝ) (g : α → BondField ι → ℝ)
    (r : ℝ → ℝ)
    (h1 : ∀ a ∈ S, Integrable fun η => f η * g a η * ballDensity r Φ η)
    (h2 : ∀ a ∈ S, Integrable fun η => g a η * ballDensity r Φ η) :
    ballCovariance r Φ f (fun η => ∑ a ∈ S, g a η) = ∑ a ∈ S, ballCovariance r Φ f (g a) := by
  have e1 : ballExpectation r Φ (fun η => f η * ∑ a ∈ S, g a η) =
      ∑ a ∈ S, ballExpectation r Φ fun η => f η * g a η := by
    unfold ballExpectation
    rw [← Finset.sum_div, ← integral_finsetSum _ h1]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    show f η * (∑ a ∈ S, g a η) * _ = ∑ a ∈ S, _
    rw [Finset.mul_sum, Finset.sum_mul]
  have e2 : ballExpectation r Φ (fun η => ∑ a ∈ S, g a η) = ∑ a ∈ S, ballExpectation r Φ (g a) := by
    unfold ballExpectation
    rw [← Finset.sum_div, ← integral_finsetSum _ h2]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    show (∑ a ∈ S, g a η) * _ = ∑ a ∈ S, _
    rw [Finset.sum_mul]
  unfold ballCovariance
  rw [e1, e2, Finset.mul_sum, ← Finset.sum_sub_distrib]
theorem ballCovariance_neg (f g : BondField ι → ℝ) (r : ℝ → ℝ) :
    ballCovariance r Φ f (fun η => - g η) = - ballCovariance r Φ f g := by
  have e1 : ∀ u : BondField ι → ℝ, ballExpectation r Φ (fun η => - u η) = - ballExpectation r Φ u :=
    fun u => by
    unfold ballExpectation
    rw [← neg_div, ← integral_neg]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    show - u η * _ = - (u η * _)
    ring
  have e2 : (fun η => f η * - g η) = fun η => - (f η * g η) := by
    funext η
    ring
  unfold ballCovariance
  rw [e2, e1, e1]
  ring
theorem integrable_mul_bounded {u g : BondField ι → ℝ}
    (hI : Integrable fun η => u η * ballDensity (cutoffFactor ρ p) Φ η)
    (hc : ContinuousOn g {η | ∀ b, ‖η b‖ < ρ}) {D : ℝ} (hb : ∀ η, (∀ b, ‖η b‖ < ρ) → |g η| ≤ D) :
    Integrable fun η => u η * g η * ballDensity (cutoffFactor ρ p) Φ η := by
  classical
  set U : Set (BondField ι) := {η | ∀ b, ‖η b‖ < ρ} with hU
  have hUo : IsOpen U := by
    have : U = ⋂ b, {η : BondField ι | ‖η b‖ < ρ} := by
      ext η
      simp [hU]
    rw [this]
    exact isOpen_iInter_of_finite fun b => isOpen_lt (continuous_apply b).norm continuous_const
  set G : BondField ι → ℝ := U.indicator g with hG
  have hgm : AEStronglyMeasurable G volume :=
    (aestronglyMeasurable_indicator_iff hUo.measurableSet).mpr (hc.aestronglyMeasurable hUo.measurableSet)
  have hgb : ∀ η, ‖G η‖ ≤ |D| := fun η => by
    by_cases hη : η ∈ U
    · rw [hG, Set.indicator_of_mem hη, Real.norm_eq_abs]
      exact (hb η hη).trans (le_abs_self _)
    · rw [hG, Set.indicator_of_notMem hη, norm_zero]
      exact abs_nonneg _
  have hmul := hI.bdd_mul hgm (Filter.Eventually.of_forall hgb)
  refine hmul.congr (Filter.Eventually.of_forall fun η => ?_)
  by_cases hη : η ∈ U
  · simp only [hG, Set.indicator_of_mem hη]
    ring
  · have h0 : ¬ ∀ b, ‖η b‖ < ρ := hη
    simp only [hG, Set.indicator_of_notMem hη, ballDensity_eq_zero h0, mul_zero]
end Linear
theorem integrable_of_hasLocalSize {ι : Type} [Fintype ι] [DecidableEq ι] {ρ x κ h : ℝ} {p : ℝ → ℝ}
    {Φ : BondField ι → ℝ} {Cq : ℕ → ℝ} {dZ : ι → ℝ} {H : BondField ι → ℝ}
    (hI : Integrable (ballDensity (cutoffFactor ρ p) Φ))
    (hc : ContinuousOn H {η | ∀ b, ‖η b‖ < ρ})
    (hs : HasLocalSize ρ (cutoffFactor ρ p) Φ Cq x κ h dZ H) :
    Integrable fun η => H η * ballDensity (cutoffFactor ρ p) Φ η := by
  obtain ⟨-, H₀, hm⟩ := hs
  have h1 := (hm 1 le_rfl).1.1
  set U : Set (BondField ι) := {η | ∀ b, ‖η b‖ < ρ} with hU
  have hUo : IsOpen U := by
    have : U = ⋂ b, {η : BondField ι | ‖η b‖ < ρ} := by
      ext η
      simp [hU]
    rw [this]
    exact isOpen_iInter_of_finite fun b => isOpen_lt (continuous_apply b).norm continuous_const
  have hm1 : AEStronglyMeasurable (U.indicator fun η => H η - H₀) volume :=
    (aestronglyMeasurable_indicator_iff hUo.measurableSet).mpr
      ((hc.sub continuousOn_const).aestronglyMeasurable hUo.measurableSet)
  have hmm : AEStronglyMeasurable (fun η => (H η - H₀) * ballDensity (cutoffFactor ρ p) Φ η) volume := by
    refine (hm1.mul hI.aestronglyMeasurable).congr (Filter.Eventually.of_forall fun η => ?_)
    by_cases hη : η ∈ U
    · simp [Set.indicator_of_mem hη]
    · have h0 : ¬ ∀ b, ‖η b‖ < ρ := hη
      simp [Set.indicator_of_notMem hη, ballDensity_eq_zero h0]
  have h2 : Integrable fun η => (H η - H₀) * ballDensity (cutoffFactor ρ p) Φ η := by
    refine h1.mono hmm (Filter.Eventually.of_forall fun η => ?_)
    simp only [pow_one, Real.norm_eq_abs, abs_mul, abs_abs, le_refl]
  have h3 := h2.add (hI.const_mul H₀)
  refine h3.congr (Filter.Eventually.of_forall fun η => ?_)
  simp only [Pi.add_apply]
  ring
theorem frameGap_eq_sub (a ρA : ℝ) (m : ℕ) (b : F.Site F.depth × Fin 4) (V : F.GaugeField F.top) :
    frameGap a ρA m b V = interpolatedFrame 1 a ρA m b V - interpolatedFrame 0 a ρA m b V := by
  simp [frameGap, interpolatedFrame]
set_option maxHeartbeats 1600000 in
theorem gapMeansDecayAt_of (hLaw : interpolatedLawAtTopFromFrames)
    (hCum : slopeCumulantsAtTopBound) (hMean : slopeMeanDerivBounds)
    (hExp : CutoffSlopeMeanExpansion) (hSz : cutoffSlopeSize)
    (hMS : cutoffSlopeMeanBoundStatement) (hRim : CutoffMeanIsGibbsMean)
    (hS : SmoothSlices.IteratedFDerivSlices) (hTube : UniformDerivBoundNearCompact) (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters)
    {Cq Cz : ℕ → ℝ} {Cr : ℕ → ℕ → ℕ → ℝ} {C : ℝ} {Ck : ℕ → ℝ} (hR : InterpolatedLawHypotheses T Cq Cz Cr C Ck)
    (hκδ : T.κ ≤ T.chainParams.δ₂ / 2 ^ 14) (hCt : 0 ≤ T.Ct) (hthird : gapObservableThirdOrderBoundAt T) :
    GapMeansDecayAt T := by
  classical
  intro N
  have hD := hR.ordered
  have hκ := hD.κ_pos
  have hσ := hD.σ_pos
  have hρ : 0 < T.ballRadius := by
    show 0 < T.σ / 64
    positivity
  have hlam : 0 < T.chainParams.lam := hD.chain_admissible.positivity.2.2.1
  have hη₃ := hD.η₃_pos
  have hE1 : 1 ≤ T.E := hD.one_le_E
  have hCs1 : 1 ≤ T.Cs := hR.one_le_Cs
  obtain ⟨n₁, hn₁⟩ : ∃ n₁ : ℕ, n₁ = 4 * T.L ^ 4 := ⟨_, rfl⟩
  obtain ⟨n₂, hn₂⟩ : ∃ n₂ : ℕ, n₂ = 1 + (centredCube T.L).card := ⟨_, rfl⟩
  obtain ⟨Cq₁, hCq₁, hsz⟩ := hSz T.ballRadius T.p Cr n₁ N hρ hD.cutoff
  let Cs : ℕ → ℝ := fun q => |Cz q| + Cq₁ q
  have hCs0 : ∀ q, 0 ≤ Cs q := fun q => add_nonneg (abs_nonneg _) (hCq₁ q)
  obtain ⟨B, hB0, hB⟩ := hCum n₁ n₂ T.κ T.chainParams.lam hκ hlam
  obtain ⟨C₃, hC₃⟩ := hthird N
  obtain ⟨β, hβdef⟩ : ∃ β, β = T.Cs * (1 + T.E / T.η₃) := ⟨_, rfl⟩
  have hβ0 : 0 ≤ β := by
    rw [hβdef]
    positivity
  obtain ⟨G, hGdef⟩ : ∃ G, G = T.Ct * (1 + T.σ) := ⟨_, rfl⟩
  have hG0 : 0 ≤ G := by
    rw [hGdef]
    positivity
  have hBc := hB0 Cs hCs0
  obtain ⟨c₁, hc₁⟩ : ∃ c₁, c₁ = (n₁ : ℝ) * |Cr 1 1 N| * G := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c₂, c₂ = B Cs * (G * β) := ⟨_, rfl⟩
  obtain ⟨c₃, hc₃⟩ : ∃ c₃, c₃ = B Cs * (G * β ^ 2) := ⟨_, rfl⟩
  obtain ⟨c₄, hc₄⟩ : ∃ c₄, c₄ = B Cs * (G * β ^ 3) := ⟨_, rfl⟩
  obtain ⟨c₅, hc₅⟩ : ∃ c₅, c₅ = c₂ + |C₃| * T.Cs := ⟨_, rfl⟩
  have hc₁0 : 0 ≤ c₁ := by
    rw [hc₁]
    positivity
  have hc₂0 : 0 ≤ c₂ := by
    rw [hc₂]
    positivity
  have hc₃0 : 0 ≤ c₃ := by
    rw [hc₃]
    positivity
  have hc₄0 : 0 ≤ c₄ := by
    rw [hc₄]
    positivity
  have hc₅0 : 0 ≤ c₅ := by
    rw [hc₅]
    positivity
  refine ⟨c₁ + (6 * c₂ + c₅ + 6 * c₃ + c₄) + 3 * c₂ + c₃ + 1, by positivity, ?_⟩
  intro t x s φ F Y V k c X hx h0 h1 hφ hF hV hk hX
  have hx1 : 1 ≤ x := hR.one_le.trans hx
  have hx0 : 0 < x := by linarith
  obtain ⟨ω, hω⟩ : ∃ ω, ω = Real.exp (-(T.chainParams.δ₂ / 4 * frameRadius x)) := ⟨_, rfl⟩
  have hω0 : 0 < ω := by
    rw [hω]
    exact Real.exp_pos _
  obtain ⟨y, hy⟩ : ∃ y, y = (x ^ N)⁻¹ := ⟨_, rfl⟩
  have hy0 : 0 < y := by
    rw [hy]
    positivity
  have hfin : Finite F.Cell := by
    obtain ⟨-, -, n, hside, hn⟩ := hF
    have hper : ∀ i, F.period F.top i = F.extent i := fun i => by simp [BlockFrame.period]
    have hne : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by
      have := hR.two_le
      rw [hper, hside]
      omega⟩
    exact Pi.finite
  have hcold := eventually_isSmallCurvature_leftTranslate hfin c X hV
  have hfr := fun (V' : F.GaugeField F.top) (hV' : IsSmallCurvature (5 / 4 * T.σ) V') (s' : ℝ) (a0 : 0 ≤ s')
    (a1 : s' ≤ 1) => (hR.frames t x hx).one_torus F V' s' hF hV' a0 a1
  by_cases hbig : ∀ i, 4 * frameRadius x + 5 < F.extent i
  swap
  · have hz : ∀ V' : F.GaugeField F.top, IsSmallCurvature (5 / 4 * T.σ) V' →
        gapObservableMean T x s φ Y V' = 0 := by
      intro V' hV'
      have hd : ∀ b : F.Site F.depth × Fin 4, frameGap T.a T.chainParams.ρA (frameRadius x) b V' = 0 := by
        intro b
        have e1 := (hfr V' hV' 1 zero_le_one le_rfl).near_minimizer.eq_on_small_torus hbig b
        have e2 : interpolatedFrame 1 T.a T.chainParams.ρA (frameRadius x) b V' =
            stepFrame false T.a T.chainParams.ρA (frameRadius x) b V' := by
          simp [interpolatedFrame]
        unfold frameGap
        rw [← e2, e1]
        exact sub_self _
      have hO : blockGapObservable T.a T.chainParams.ρA (frameRadius x) T.p Y V' = fun _ => 0 := by
        funext η
        unfold blockGapObservable
        refine Finset.sum_eq_zero fun b _ => ?_
        rw [hd b.1]
        simp
      unfold gapObservableMean
      rw [hO]
      simp [ballExpectation]
    have ev : (fun τ : Fin k → ℝ => gapObservableMean T x s φ Y (leftTranslate (bondSpread c X τ) V)) =ᶠ[𝓝 0]
        fun _ => 0 := by
      filter_upwards [hcold] with τ hτ using hz _ hτ
    have e0 : bondDeriv (gapObservableMean T x s φ Y) V c X = 0 := by
      unfold bondDeriv
      have h2 := (ev.iteratedFDeriv ℝ k).self_of_nhds
      rw [h2]
      simp
    rw [e0, abs_zero]
    positivity
  subst hβdef hn₁ hn₂
  obtain ⟨hL₀, hsumE, Φ, d, hmom, hdens⟩ := hLaw T Cq Cz Cr C Ck hR t x s φ F V hx h0 h1 hφ hF hV
  set A : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ :=
    interpolatedExponentOfTerms s T.a T.chainParams.ρA x (frameRadius x) φ with hA
  set e : F.GaugeField F.top → StepVariable (finiteCells F) :=
    blockFrameGap T.a T.chainParams.ρA (frameRadius x) Y with he
  set H : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ := cutoffSlopeAlong T.p e with hH
  have hC : ∀ q, |(fun q => |Cz q|) q| ≤ Cs q := fun q => by
    have := hCq₁ q
    simp only [abs_abs, Cs]
    linarith
  have hC₁ : ∀ q, |Cq₁ q| ≤ Cs q := fun q => by
    rw [abs_of_nonneg (hCq₁ q)]
    have := abs_nonneg (Cz q)
    simp only [Cs]
    linarith
  have hL : InterpolatedLawAtTop s T.a T.chainParams.ρA x (frameRadius x) (T.σ / 64) T.chainParams.lam T.κ
      (T.Cs * (1 + T.E / T.η₃)) T.p Cs (4 * T.L ^ 4) (1 + (centredCube T.L).card) φ V :=
    { hL₀ with
      Cq_nonneg := hCs0
      size_cell := fun Z k' c' X' a b => hasLocalSize_mono rfl
        (mul_nonneg hL₀.β_nonneg (Real.exp_pos _).le) le_rfl hC (hL₀.size_cell Z k' c' X' a b)
      size_site := fun z k' c' X' a b => hasLocalSize_mono rfl
        (mul_nonneg hL₀.β_nonneg (Real.exp_pos _).le) le_rfl hC (hL₀.size_site z k' c' X' a b) }
  have hone := hfr V hV s h0 h1
  have one0 := hfr V hV 0 le_rfl zero_le_one
  have one1 := hfr V hV 1 zero_le_one le_rfl
  have hAs : JointlyContDiffOnBalls T.ballRadius V A := fun k' c' X' η hη =>
    ContDiffAt.sum fun q _ => hL.smooth_term q k' c' X' η hη
  have hfd : ∀ (b : ↥(chordBonds (finiteCells F))) (k' : ℕ) (c' : Fin k' → F.Site F.top × Fin 4)
      (X' : Fin k' → imaginaryQuaternions), ContDiffAt ℝ 3 (fun τ : Fin k' → ℝ =>
        frameGap T.a T.chainParams.ρA (frameRadius x) b.1 (leftTranslate (bondSpread c' X' τ) V)) 0 := by
    intro b k' c' X'
    have a1 := one1.small.analytic b.1 b.2 k' c' X'
    have a0 := one0.small.analytic b.1 b.2 k' c' X'
    have e1 : (fun τ : Fin k' → ℝ =>
        frameGap T.a T.chainParams.ρA (frameRadius x) b.1 (leftTranslate (bondSpread c' X' τ) V)) =
        (fun σ : Fin k' → ℝ => interpolatedFrame 1 T.a T.chainParams.ρA (frameRadius x) b.1
            (rotatedField (BlockAverages.bondSpread c' X' σ) V)) -
          (fun σ : Fin k' → ℝ => interpolatedFrame 0 T.a T.chainParams.ρA (frameRadius x) b.1
            (rotatedField (BlockAverages.bondSpread c' X' σ) V)) :=
      funext fun τ => frameGap_eq_sub _ _ _ _ _
    rw [e1]
    exact (a1.sub a0).contDiffAt
  have he3 : ∀ (k' : ℕ) (c' : Fin k' → F.Site F.top × Fin 4) (X' : Fin k' → imaginaryQuaternions),
      ContDiffAt ℝ 3 (fun τ : Fin k' → ℝ => e (leftTranslate (bondSpread c' X' τ) V)) 0 := by
    intro k' c' X'
    refine contDiffAt_pi.mpr fun b => ?_
    by_cases hb : enclosingCell b.1.1 = Y
    · have e1 : (fun τ : Fin k' → ℝ => e (leftTranslate (bondSpread c' X' τ) V) b) =
          imaginaryCoordsCLM ∘ fun τ : Fin k' → ℝ =>
            frameGap T.a T.chainParams.ρA (frameRadius x) b.1 (leftTranslate (bondSpread c' X' τ) V) := by
        funext τ
        simp only [he, blockFrameGap, if_pos hb, Function.comp, imaginaryCoordsCLM_apply]
      rw [e1]
      exact imaginaryCoordsCLM.contDiff.contDiffAt.comp 0 (hfd b k' c' X')
    · have e1 : (fun τ : Fin k' → ℝ => e (leftTranslate (bondSpread c' X' τ) V) b) = fun _ => 0 := by
        funext τ
        simp only [he, blockFrameGap, if_neg hb]
      rw [e1]
      exact contDiffAt_const
  obtain ⟨hfin2, hμ0, hμb, hrm⟩ := hRim F T.ballRadius T.p hρ hD.cutoff
  have hexp := hExp F T.ballRadius T.p V A e hρ hD.cutoff hAs he3
  have hwm : ∀ f, gibbsMean (cutoffLaw F T.ballRadius T.p) (fun η => A η V) f =
      ballExpectation (cutoffFactor T.ballRadius T.p) (fun η => A η V) f := fun f => (hrm _ f).symm
  have hmeanΦ : ∀ f, ballExpectation (cutoffFactor T.ballRadius T.p) Φ f =
      ballExpectation (cutoffFactor T.ballRadius T.p) (fun η => A η V) f := fun f => by
    simp only [ballExpectation, hdens]
  have hIΦ : Integrable (ballDensity (cutoffFactor T.ballRadius T.p) Φ) := by
    rw [hdens]
    exact hL₀.integrable
  have hcard : (Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1 = Y).card ≤
      4 * T.L ^ 4 := hL₀.card_bonds_le Y
  have hgap : frameGapBound T (frameRadius x) = T.Ct * ω := by
    rw [hω]
    rfl
  have hgapG : frameGapBound T (frameRadius x) ≤ G * ω := by
    rw [hgap, hGdef]
    have : 0 ≤ T.Ct * T.σ * ω := by positivity
    nlinarith
  have hdb : ∀ (j₀ : ℕ) (c₀ : Fin j₀ → F.Site F.top × Fin 4) (X₀ : Fin j₀ → imaginaryQuaternions), j₀ ≤ 3 →
      AreUnitVectors X₀ → ∀ b, ‖bondDeriv e V c₀ X₀ b‖ ≤
        G * ω * Real.exp (-(T.chainParams.δ₂ / 4 * bondListDistance Y c₀)) := by
    intro j₀ c₀ X₀ hj hX₀ b
    have h2 := norm_bondDeriv_blockFrameGap_le T.a T.chainParams.ρA (frameRadius x) Y V c₀ X₀ b
      ((he3 j₀ c₀ X₀).of_le (by exact_mod_cast hj)) ((hfd b j₀ c₀ X₀).of_le (by exact_mod_cast hj))
    refine h2.trans ?_
    split_ifs with hb
    · rcases Nat.eq_zero_or_pos j₀ with rfl | hpos
      · rw [bondDeriv_zero]
        have h3 := (hone.near_minimizer.norm_eq_and_le b.1 b.2).2
        have h4 : bondListDistance Y c₀ = 0 := by
          simp [bondListDistance]
        rw [h4]
        simp only [Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, mul_one]
        have h5 : frameGapBound T (frameRadius x) * T.σ ≤ G * ω := by
          rw [hgap, hGdef]
          have : 0 ≤ T.Ct * ω := by positivity
          nlinarith
        exact h3.trans h5
      · have h3 := hone.near_minimizer.deriv_decay b.1 b.2 j₀ c₀ X₀ hpos hj hX₀
        rw [hb] at h3
        exact h3.trans (mul_le_mul_of_nonneg_right hgapG (Real.exp_pos _).le)
    · positivity
  have hnot : ∀ (j₀ : ℕ) (c₀ : Fin j₀ → F.Site F.top × Fin 4) (X₀ : Fin j₀ → imaginaryQuaternions), j₀ ≤ 3 →
      ∀ b, b ∉ (Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1 = Y) →
        bondDeriv e V c₀ X₀ b = 0 := by
    intro j₀ c₀ X₀ hj b hb
    have hb' : enclosingCell b.1.1 ≠ Y := fun h => hb (by simp [h])
    have h2 := norm_bondDeriv_blockFrameGap_le T.a T.chainParams.ρA (frameRadius x) Y V c₀ X₀ b
      ((he3 j₀ c₀ X₀).of_le (by exact_mod_cast hj)) ((hfd b j₀ c₀ X₀).of_le (by exact_mod_cast hj))
    rw [if_neg hb'] at h2
    exact norm_le_zero_iff.mp h2
  have hexA : ∀ {j₀ : ℕ} (c₀ : Fin j₀ → F.Site F.top × Fin 4),
      Real.exp (-(T.chainParams.δ₂ / 4 * bondListDistance Y c₀)) ≤
        Real.exp (-(2 ^ 4 * T.κ * (bondSpan Y c₀ : ℝ))) := by
    intro j₀ c₀
    apply Real.exp_le_exp.mpr
    have h2 : (bondSpan Y c₀ : ℝ) ≤ 2 * (bondListDistance Y c₀ : ℝ) := by
      exact_mod_cast bondSpan_le_two_mul Y c₀
    have h3 : (0 : ℝ) ≤ bondListDistance Y c₀ := Nat.cast_nonneg _
    have h4 : 2 ^ 4 * T.κ * (bondSpan Y c₀ : ℝ) ≤ 2 ^ 4 * T.κ * (2 * (bondListDistance Y c₀ : ℝ)) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have h5 : 2 ^ 4 * T.κ * 2 ≤ T.chainParams.δ₂ / 4 := by linarith
    have h6 := mul_le_mul_of_nonneg_right h5 h3
    nlinarith
  have hexB : ∀ {j₀ : ℕ} (c₀ : Fin j₀ → F.Site F.top × Fin 4),
      Real.exp (-(2 ^ 4 * T.κ * (bondSpan Y c₀ : ℝ))) ≤ Real.exp (-(T.κ / 2 ^ 6 * (bondSpan Y c₀ : ℝ))) := by
    intro j₀ c₀
    apply Real.exp_le_exp.mpr
    have h3 : (0 : ℝ) ≤ bondSpan Y c₀ := Nat.cast_nonneg _
    have h4 : T.κ / 2 ^ 6 ≤ 2 ^ 4 * T.κ := by linarith
    have := mul_le_mul_of_nonneg_right h4 h3
    linarith
  have hSl : ∀ (j₀ : ℕ) (c₀ : Fin j₀ → F.Site F.top × Fin 4) (X₀ : Fin j₀ → imaginaryQuaternions), j₀ ≤ 3 →
      AreUnitVectors X₀ →
      CutoffSlopeBoundAtCell s T.a T.chainParams.ρA x (frameRadius x) (T.σ / 64) T.κ (G * ω * y) T.p Cs φ V Y c₀
        (fieldDeriv H V c₀ X₀) := by
    intro j₀ c₀ X₀ hj hX₀
    have hT := fieldDeriv_cutoffSlopeAlong T.p e V c₀ X₀ ((he3 j₀ c₀ X₀).of_le (by exact_mod_cast hj))
    have hE₀ : 0 ≤ G * ω * Real.exp (-(T.chainParams.δ₂ / 4 * bondListDistance Y c₀)) := by positivity
    obtain ⟨s1, s2⟩ := hsz _ x T.κ T.Cs Cq d Φ
      (Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1 = Y)
      (fun b => (cellSupDist (enclosingCell b.1.1) Y : ℝ)) (bondDeriv e V c₀ X₀) _ hx1 hE₀ hcard hmom hIΦ
      (hnot j₀ c₀ X₀ hj) (fun b hb => by
        have hb' : enclosingCell b.1.1 = Y := by simpa using hb
        rw [hb', PatchLocality.cellSupDist_self]
        simp) (hdb j₀ c₀ X₀ hj hX₀)
    refine ⟨?_, ?_⟩
    · rw [hT]
      exact s1
    · rw [hT]
      refine hasLocalSize_mono hdens (mul_nonneg hE₀ (by rw [← hy]; exact hy0.le)) ?_ hC₁ s2
      rw [← hy]
      calc G * ω * Real.exp (-(T.chainParams.δ₂ / 4 * bondListDistance Y c₀)) * y
          = G * ω * y * Real.exp (-(T.chainParams.δ₂ / 4 * bondListDistance Y c₀)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hexA c₀) (by positivity)
  have hα0 : 0 ≤ G * ω * y := by positivity
  have hsmall := hB F s T.a T.chainParams.ρA x (frameRadius x) (T.σ / 64) (G * ω * y)
    (T.Cs * (1 + T.E / T.η₃)) T.p Cs φ V hL hα0 Y H
    (fun j₀ c₀ X₀ hj hX₀ => hSl j₀ c₀ X₀ (by omega) hX₀)
  have hmid : ∀ (k' : ℕ) (c' : Fin k' → F.Site F.top × Fin 4) (X' : Fin k' → imaginaryQuaternions), k' ≤ 3 →
      AreUnitVectors X' →
      |gibbsMean (cutoffLaw F T.ballRadius T.p) (fun η => A η V) (fieldDeriv H V c' X')| ≤
        (c₁ * (ω * y)) * Real.exp (-(T.κ / 2 ^ 6 * (bondSpan Y c' : ℝ))) := by
    intro k' c' X' hk' hX'
    have hT := fieldDeriv_cutoffSlopeAlong T.p e V c' X' ((he3 k' c' X').of_le (by exact_mod_cast hk'))
    have hE₀ : 0 ≤ G * ω * Real.exp (-(T.chainParams.δ₂ / 4 * bondListDistance Y c')) := by positivity
    have h2 := hMS T.ballRadius T.p Cr (4 * T.L ^ 4) N _ x T.κ T.Cs Cq d Φ
      (Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1 = Y)
      (bondDeriv e V c' X') _ hE₀ hx0 hcard hmom (hnot k' c' X' hk') (hdb k' c' X' hk' hX')
    rw [hwm, hT, ← hmeanΦ]
    refine h2.trans ?_
    rw [← hy, hc₁]
    have h3 := (hexA c').trans (hexB c')
    have h4 : 0 ≤ ((4 * T.L ^ 4 : ℕ) : ℝ) * |Cr 1 1 N| * G * (ω * y) := by positivity
    calc ((4 * T.L ^ 4 : ℕ) : ℝ) * |Cr 1 1 N| *
          (G * ω * Real.exp (-(T.chainParams.δ₂ / 4 * bondListDistance Y c')) * y)
        = ((4 * T.L ^ 4 : ℕ) : ℝ) * |Cr 1 1 N| * G * (ω * y) *
            Real.exp (-(T.chainParams.δ₂ / 4 * bondListDistance Y c')) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 h4
  have hf0 : fieldDeriv H V (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)
      (Fin.elim0 : Fin 0 → imaginaryQuaternions) = fun η => H η V := by
    funext η
    unfold fieldDeriv
    rw [bondDeriv_zero]
  have hU : ∀ {η : StepVariable (finiteCells F)}, (∀ b, ‖η b‖ < T.ballRadius) → ∀ b, ‖η b‖ ≤ T.ballRadius :=
    fun hη b => (hη b).le
  have hcellJ : JointlyContDiffOnBalls T.ballRadius V
      (interpolatedCellExponent s T.a T.chainParams.ρA x (frameRadius x) φ) :=
    fun k' c' X' η hη => ContDiffAt.sum fun Z _ => hL.smooth_term (Sum.inl Z) k' c' X' η hη
  have hfI : Integrable fun η => H η V *
      ballDensity (cutoffFactor T.ballRadius T.p) (fun η => A η V) η := by
    have h2 := hSl 0 Fin.elim0 Fin.elim0 (by norm_num) (fun l => l.elim0)
    have hsm := h2.smooth
    have hsi := h2.size
    rw [hf0] at hsm hsi
    exact integrable_of_hasLocalSize hL.integrable hsm.continuousOn hsi
  have hDI : Integrable fun η => (1 : ℝ) * ballDensity (cutoffFactor T.ballRadius T.p) (fun η => A η V) η := by
    simp only [one_mul]
    exact hL.integrable
  have hcov3 : ∀ (c' : Fin 3 → F.Site F.top × Fin 4) (X' : Fin 3 → imaginaryQuaternions), AreUnitVectors X' →
      |ballCovariance (cutoffFactor T.ballRadius T.p) (fun η => A η V) (fun η => H η V) (fieldDeriv A V c' X')| ≤
        (c₅ * (ω * y)) * Real.exp (-(T.κ / 2 ^ 6 * (bondSpan Y c' : ℝ))) := by
    intro c' X' hX'
    let gO : Option ↥(sitesOfCells (finiteCells F) F.depth) → StepVariable (finiteCells F) → ℝ := fun o =>
      match o with
      | none => fieldDeriv (interpolatedCellExponent s T.a T.chainParams.ρA x (frameRadius x) φ) V c' X'
      | some y' => fieldDeriv
          (interpolatedExponentTerm s T.a T.chainParams.ρA x (frameRadius x) φ (Sum.inr y')) V c' X'
    have hsp : ∀ η, (∀ b, ‖η b‖ < T.ballRadius) → fieldDeriv A V c' X' η = ∑ o, gO o η := by
      intro η hη
      have e1 : A = fun η V' => ∑ q ∈ (Finset.univ : Finset (LawAtTop.TermPlace F)),
          interpolatedExponentTerm s T.a T.chainParams.ρA x (frameRadius x) φ q η V' := rfl
      rw [e1, fieldDeriv_sum _ (interpolatedExponentTerm s T.a T.chainParams.ρA x (frameRadius x) φ) c' X' η
        (fun q _ => contDiffAt_slice (hL.smooth_term q) c' X' (by norm_num) (hU hη)), Fintype.sum_sum_type,
        Fintype.sum_option]
      have e2 : (interpolatedCellExponent s T.a T.chainParams.ρA x (frameRadius x) φ :
          StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) = fun η V' =>
          ∑ Z ∈ (Finset.univ : Finset ↥(finiteCells F)),
            interpolatedExponentTerm s T.a T.chainParams.ρA x (frameRadius x) φ (Sum.inl Z) η V' := rfl
      have e3 : gO none η = ∑ Z : ↥(finiteCells F),
          fieldDeriv (interpolatedExponentTerm s T.a T.chainParams.ρA x (frameRadius x) φ (Sum.inl Z))
            V c' X' η := by
        show fieldDeriv (interpolatedCellExponent s T.a T.chainParams.ρA x (frameRadius x) φ) V c' X' η = _
        rw [e2]
        exact fieldDeriv_sum _
          (fun Z => interpolatedExponentTerm s T.a T.chainParams.ρA x (frameRadius x) φ (Sum.inl Z)) c' X' η
          (fun Z _ => contDiffAt_slice (hL.smooth_term _) c' X' (by norm_num) (hU hη))
      rw [e3]
    have hbd : ∀ o, ∃ D : ℝ, ContinuousOn (gO o) {η | ∀ b, ‖η b‖ < T.ballRadius} ∧
        ∀ η, (∀ b, ‖η b‖ < T.ballRadius) → |gO o η| ≤ D := by
      intro o
      cases o with
      | none =>
        obtain ⟨D, hDb⟩ := fieldDeriv_bounded hTube hcellJ c' X' (by norm_num)
        exact ⟨D, fieldDeriv_continuousOn hS hcellJ c' X', fun η hη => hDb η (hU hη)⟩
      | some y' =>
        obtain ⟨D, hDb⟩ := fieldDeriv_bounded hTube (hL.smooth_term (Sum.inr y')) c' X' (by norm_num)
        exact ⟨D, fieldDeriv_continuousOn hS (hL.smooth_term (Sum.inr y')) c' X', fun η hη => hDb η (hU hη)⟩
    have i1 : ∀ o ∈ (Finset.univ : Finset (Option ↥(sitesOfCells (finiteCells F) F.depth))),
        Integrable fun η => H η V * gO o η *
          ballDensity (cutoffFactor T.ballRadius T.p) (fun η => A η V) η := fun o _ => by
      obtain ⟨D, h2, h3⟩ := hbd o
      exact integrable_mul_bounded hfI h2 h3
    have i2 : ∀ o ∈ (Finset.univ : Finset (Option ↥(sitesOfCells (finiteCells F) F.depth))),
        Integrable fun η => gO o η *
          ballDensity (cutoffFactor T.ballRadius T.p) (fun η => A η V) η := fun o _ => by
      obtain ⟨D, h2, h3⟩ := hbd o
      simpa using integrable_mul_bounded hDI h2 h3
    have key : ballCovariance (cutoffFactor T.ballRadius T.p) (fun η => A η V) (fun η => H η V)
        (fieldDeriv A V c' X') =
        ∑ o, ballCovariance (cutoffFactor T.ballRadius T.p) (fun η => A η V) (fun η => H η V) (gO o) := by
      rw [ballCovariance_congr (ρ := T.ballRadius) (f' := fun η => H η V) (g' := fun η => ∑ o, gO o η)
        (fun _ _ => rfl) hsp]
      exact ballCovariance_sum _ _ _ _ i1 i2
    rw [key, Fintype.sum_option]
    have t1 := hsmall.covariance_cells 0 3 3 (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)
      (Fin.elim0 : Fin 0 → imaginaryQuaternions) c' X' c'
      (by norm_num) le_rfl (fun l => l.elim0) hX' (fun l => Or.inr ⟨l, rfl⟩)
    rw [hf0] at t1
    have hdf : ballDensity (cutoffFactor T.ballRadius T.p) (fun η => A η V) =
        ballDensity (cutoffFactor T.ballRadius T.p)
          (familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ V) := ballDensity_congr hsumE
    have hrow : ∀ y' : ↥(sitesOfCells (finiteCells F) F.depth),
        |ballCovariance (cutoffFactor T.ballRadius T.p) (fun η => A η V) (fun η => H η V) (gO (some y'))| =
        |ballCovariance (cutoffFactor T.ballRadius T.p)
          (familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ V)
          (blockGapObservable T.a T.chainParams.ρA (frameRadius x) T.p Y V)
          (fun η => bondDeriv (interpolatedExpansion s T.a T.chainParams.ρA (frameRadius x) φ y'.1 η) V c' X')| := by
      intro y'
      have e3 : gO (some y') = fun η =>
          - bondDeriv (interpolatedExpansion s T.a T.chainParams.ρA (frameRadius x) φ y'.1 η) V c' X' := by
        funext η
        show fieldDeriv (interpolatedExponentTerm s T.a T.chainParams.ρA x (frameRadius x) φ (Sum.inr y'))
          V c' X' η = _
        unfold fieldDeriv bondDeriv
        have e4 : (fun τ : Fin 3 → ℝ =>
            interpolatedExponentTerm s T.a T.chainParams.ρA x (frameRadius x) φ (Sum.inr y') η
              (leftTranslate (bondSpread c' X' τ) V)) = - fun τ : Fin 3 → ℝ =>
            interpolatedExpansion s T.a T.chainParams.ρA (frameRadius x) φ y'.1 η
              (leftTranslate (bondSpread c' X' τ) V) := rfl
        rw [e4, iteratedFDeriv_neg_apply]
        rfl
      have hcc : ∀ f g : StepVariable (finiteCells F) → ℝ,
          ballCovariance (cutoffFactor T.ballRadius T.p) (fun η => A η V) f g =
            ballCovariance (cutoffFactor T.ballRadius T.p)
              (familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ V) f g := fun f g => by
        simp only [ballCovariance, ballExpectation, hdf]
      rw [e3, ballCovariance_neg, abs_neg, blockGapObservable_eq, hcc]
    have t2 := hC₃ t x s φ F V Y c' X' hx h0 h1 hφ hF hV hX' hbig
    have hsum : ∑ y' : ↥(sitesOfCells (finiteCells F) F.depth),
        |ballCovariance (cutoffFactor T.ballRadius T.p) (fun η => A η V) (fun η => H η V) (gO (some y'))| ≤
        C₃ * (x ^ N)⁻¹ * (T.Cs * Real.exp (-(T.chainParams.δ₂ / 4 * frameRadius x))) *
          Real.exp (-(T.κ / 2 ^ 5 * bondSpan Y c')) := by
      simp only [hrow]
      rw [Finset.sum_coe_sort (sitesOfCells (finiteCells F) F.depth) (fun y' =>
        |ballCovariance (cutoffFactor T.ballRadius T.p)
          (familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ V)
          (blockGapObservable T.a T.chainParams.ρA (frameRadius x) T.p Y V)
          (fun η => bondDeriv (interpolatedExpansion s T.a T.chainParams.ρA (frameRadius x) φ y' η) V c' X')|)]
      exact t2
    rw [← hω, ← hy] at hsum
    have hsp0 : (0 : ℝ) ≤ bondSpan Y c' := Nat.cast_nonneg _
    have ex1 : Real.exp (-(T.κ / 16 * (bondSpan Y c' : ℝ))) ≤
        Real.exp (-(T.κ / 2 ^ 6 * (bondSpan Y c' : ℝ))) := by
      apply Real.exp_le_exp.mpr
      have h4 : T.κ / 2 ^ 6 ≤ T.κ / 16 := by linarith
      have := mul_le_mul_of_nonneg_right h4 hsp0
      linarith
    have ex2 : Real.exp (-(T.κ / 2 ^ 5 * (bondSpan Y c' : ℝ))) ≤
        Real.exp (-(T.κ / 2 ^ 6 * (bondSpan Y c' : ℝ))) := by
      apply Real.exp_le_exp.mpr
      have h4 : T.κ / 2 ^ 6 ≤ T.κ / 2 ^ 5 := by linarith
      have := mul_le_mul_of_nonneg_right h4 hsp0
      linarith
    obtain ⟨E₆, hE₆⟩ : ∃ E₆, E₆ = Real.exp (-(T.κ / 2 ^ 6 * (bondSpan Y c' : ℝ))) := ⟨_, rfl⟩
    rw [← hE₆] at ex1 ex2 ⊢
    have hE₆0 : 0 ≤ E₆ := by
      rw [hE₆]
      exact (Real.exp_pos _).le
    have b1 : |ballCovariance (cutoffFactor T.ballRadius T.p) (fun η => A η V) (fun η => H η V) (gO none)| ≤
        c₂ * (ω * y) * E₆ := by
      refine t1.trans ?_
      have h2 : B Cs * (G * ω * y * (T.Cs * (1 + T.E / T.η₃))) = c₂ * (ω * y) := by
        rw [hc₂]
        ring
      rw [h2]
      exact mul_le_mul_of_nonneg_left ex1 (by positivity)
    have b2 : |∑ y' : ↥(sitesOfCells (finiteCells F) F.depth),
        ballCovariance (cutoffFactor T.ballRadius T.p) (fun η => A η V) (fun η => H η V) (gO (some y'))| ≤
        |C₃| * T.Cs * (ω * y) * E₆ := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (hsum.trans ?_)
      have h2 : C₃ * y * (T.Cs * ω) ≤ |C₃| * T.Cs * (ω * y) := by
        have h3 : C₃ * (y * (T.Cs * ω)) ≤ |C₃| * (y * (T.Cs * ω)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        nlinarith
      have h5 : 0 ≤ |C₃| * T.Cs * (ω * y) := by positivity
      calc C₃ * y * (T.Cs * ω) * Real.exp (-(T.κ / 2 ^ 5 * (bondSpan Y c' : ℝ)))
          ≤ |C₃| * T.Cs * (ω * y) * Real.exp (-(T.κ / 2 ^ 5 * (bondSpan Y c' : ℝ))) :=
            mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
        _ ≤ _ := mul_le_mul_of_nonneg_left ex2 h5
    refine (abs_add_le _ _).trans ((add_le_add b1 b2).trans (le_of_eq ?_))
    rw [hc₅]
    ring
  have hgm : ∀ V' : F.GaugeField F.top, IsSmallCurvature (5 / 4 * T.σ) V' →
      gapObservableMean T x s φ Y V' = gibbsMeanAt (cutoffLaw F T.ballRadius T.p) A H V' := by
    intro V' hV'
    obtain ⟨-, hs', -⟩ := hLaw T Cq Cz Cr C Ck hR t x s φ F V' hx h0 h1 hφ hF hV'
    have hd' : ballDensity (cutoffFactor T.ballRadius T.p)
        (familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ V') =
        ballDensity (cutoffFactor T.ballRadius T.p) (fun η => A η V') :=
      (ballDensity_congr hs').symm
    unfold gapObservableMean gibbsMeanAt
    rw [blockGapObservable_eq, ← hrm]
    show ballExpectation (cutoffFactor T.ballRadius T.p)
        (familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ V') (fun η => H η V') =
        ballExpectation (cutoffFactor T.ballRadius T.p) (fun η => A η V') (fun η => H η V')
    simp only [ballExpectation, hd']
  have hcong : bondDeriv (gapObservableMean T x s φ Y) V c X =
      bondDeriv (gibbsMeanAt (cutoffLaw F T.ballRadius T.p) A H) V c X := by
    have ev : (fun τ : Fin k → ℝ => gapObservableMean T x s φ Y (leftTranslate (bondSpread c X τ) V)) =ᶠ[𝓝 0]
        fun τ => gibbsMeanAt (cutoffLaw F T.ballRadius T.p) A H (leftTranslate (bondSpread c X τ) V) := by
      filter_upwards [hcold] with τ hτ using hgm _ hτ
    unfold bondDeriv
    rw [(ev.iteratedFDeriv ℝ k).self_of_nhds]
  have hb₂ : 0 ≤ B Cs * (G * ω * y * (T.Cs * (1 + T.E / T.η₃))) := by positivity
  have hb₃ : 0 ≤ B Cs * (G * ω * y * (T.Cs * (1 + T.E / T.η₃)) ^ 2) := by positivity
  have hb₄ : 0 ≤ B Cs * (G * ω * y * (T.Cs * (1 + T.E / T.η₃)) ^ 3) := by positivity
  obtain ⟨r1, r2⟩ := hMean F s T.a T.chainParams.ρA x (frameRadius x) T.ballRadius T.κ T.p φ V Y H
    (cutoffLaw F T.ballRadius T.p)
    (c₁ * (ω * y)) _ _ _ (c₅ * (ω * y)) hκ hb₂ hb₃ hb₄ hexp.2 hwm hsmall hmid hcov3
  rw [hcong]
  obtain ⟨E₆, hE₆⟩ : ∃ E₆, E₆ = Real.exp (-(T.κ / 2 ^ 6 * (bondSpan Y c : ℝ))) := ⟨_, rfl⟩
  have hE₆0 : 0 ≤ E₆ := by
    rw [hE₆]
    exact (Real.exp_pos _).le
  have i₂ : B Cs * (G * ω * y * (T.Cs * (1 + T.E / T.η₃))) = c₂ * (ω * y) := by
    rw [hc₂]
    ring
  have i₃ : B Cs * (G * ω * y * (T.Cs * (1 + T.E / T.η₃)) ^ 2) = c₃ * (ω * y) := by
    rw [hc₃]
    ring
  have i₄ : B Cs * (G * ω * y * (T.Cs * (1 + T.E / T.η₃)) ^ 3) = c₄ * (ω * y) := by
    rw [hc₄]
    ring
  have hwy : 0 ≤ ω * y := by positivity
  rw [← hy, ← hω]
  by_cases hk2 : k ≤ 2
  · have h2 := r1 k c X hk2 hX
    rw [i₂, i₃, ← hE₆] at h2
    rw [← hE₆]
    refine h2.trans ?_
    have : (c₁ * (ω * y) + 3 * (c₂ * (ω * y)) + c₃ * (ω * y)) ≤
        (c₁ + (6 * c₂ + c₅ + 6 * c₃ + c₄) + 3 * c₂ + c₃ + 1) * y * ω := by
      nlinarith [mul_nonneg (add_nonneg (add_nonneg (add_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 6) hc₂0) hc₅0)
        (mul_nonneg (by norm_num : (0:ℝ) ≤ 6) hc₃0)) hc₄0) hwy, hwy]
    exact mul_le_mul_of_nonneg_right this hE₆0
  · have hk3 : k = 3 := by omega
    subst hk3
    have h2 := r2 c X hX
    rw [i₂, i₃, i₄, ← hE₆] at h2
    rw [← hE₆]
    refine h2.trans ?_
    have : (c₁ * (ω * y) + (6 * (c₂ * (ω * y)) + c₅ * (ω * y) + 6 * (c₃ * (ω * y)) + c₄ * (ω * y))) ≤
        (c₁ + (6 * c₂ + c₅ + 6 * c₃ + c₄) + 3 * c₂ + c₃ + 1) * y * ω := by
      nlinarith [mul_nonneg hc₂0 hwy, mul_nonneg hc₃0 hwy, hwy]
    exact mul_le_mul_of_nonneg_right this hE₆0
def ParametersUsed (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) : Prop :=
  2 ≤ T.n₀ ∧ 1 ≤ T.coupling ∧ 1 ≤ T.Cs ∧ 0 ≤ T.Ct ∧ T.κ ≤ T.chainParams.δ₂ / 2 ^ 14
theorem eventually_parametersUsed : EventuallyInParameters ParametersUsed := by
  intro a _
  refine ⟨0, fun L _ _ c hc => ⟨0, fun Ct hCt => ⟨c.δ₂ / 2 ^ 14, ?_, fun κ _ hκ => ⟨1, one_pos,
    fun η₃ _ _ _ => ⟨0, fun nss _ => ⟨1, one_pos, fun σ _ _ p _ => ⟨1, fun Cs hCs E _ => ⟨2,
    fun n₀ hn => ⟨0, fun CE _ => ⟨1, fun y₁ hy => ⟨hn, hy, hCs, hCt, hκ⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  obtain ⟨⟨-, -, -, h, -⟩, -⟩ := hc.classical
  positivity
theorem gapMeansDecay_holds (hframes : interpolatedFramesStatement)
    (hTr : transportBoundsStatement) (hParts : interpolatedPartsSmoothStatement)
    (hThird : gapObservableThirdOrderBound) (hJ : EventuallyInParametersCombines)
    (hLaw : interpolatedLawAtTopFromFrames) (hCum : slopeCumulantsAtTopBound)
    (hMean : slopeMeanDerivBounds) (hExp : CutoffSlopeMeanExpansion)
    (hSz : cutoffSlopeSize) (hMS : cutoffSlopeMeanBoundStatement)
    (hRim : CutoffMeanIsGibbsMean) (hS : SmoothSlices.IteratedFDerivSlices)
    (hTube : UniformDerivBoundNearCompact) : gapMeansDecay := by
  obtain ⟨Cq, Cz, Cr, hfb⟩ := hframes
  obtain ⟨C, Ck, -, -, htr⟩ := hTr
  have j := hJ.1
  have J := j _ _ eventually_parametersUsed (j _ _ hfb (j _ _ htr (j _ _ hParts hThird)))
  refine hJ.2 _ _ (fun T hT h => ?_) J
  obtain ⟨⟨h2, h1, hCs, hCt, hκ⟩, hf, ht, hp, h3⟩ := h
  exact gapMeansDecayAt_of hLaw hCum hMean hExp hSz hMS hRim hS hTube T
    ⟨hT, h2, h1, hCs, hf, ht, hp⟩ hκ hCt h3
end BlockMeans.GapMeans
end YangMills.Construction
end
