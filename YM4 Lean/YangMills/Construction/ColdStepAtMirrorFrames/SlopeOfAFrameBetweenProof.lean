import YangMills.Construction.ColdStepAtMirrorFrames.CurvesOfTheFrames
import YangMills.Construction.ColdStepAtMirrorFrames.ExponentialOfTheLieAlgebra
import YangMills.Construction.ColdStepAtMirrorFrames.FramesAreSmall
import YangMills.Construction.ColdStepAtMirrorFrames.HolonomyIsLipschitz
import YangMills.Construction.ColdStepAtMirrorFrames.SlopeOfAFrameBetween
import YangMills.Construction.RunningCouplingSlope.EnergyAtTheLeastFieldHasKernelsProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages Interpolation Calculus QuaternionExp
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
namespace InterpolatedSlopeLemmas
def imaginaryCoordL (α : Fin 3) : imaginaryQuaternions →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (imaginaryCoord α)
theorem abs_imaginaryCoord_le_norm (α : Fin 3) (w : imaginaryQuaternions) : |imaginaryCoord α w| ≤ ‖w‖ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FrameCurves.abs_imaginaryCoord_le <;> assumption
theorem chartCoordinates_add_smul (dw₁ dw₂ : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (dv₁ dv₂ : F.Site F.top → Fin 4 → imaginaryQuaternions) (θ : ℝ) :
    chartCoordinates (fun x i => dw₁ x i + θ • dw₂ x i) (fun y i => dv₁ y i + θ • dv₂ y i) =
      chartCoordinates dw₁ dv₁ + θ • chartCoordinates dw₂ dv₂ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FrameCurves.chartCoordinates_add_smul <;> assumption
theorem analyticAt_chartCoordinates {k : ℕ} (f : F.Site F.depth → Fin 4 → (Fin k → ℝ) → imaginaryQuaternions)
    (g : F.Site F.top → Fin 4 → (Fin k → ℝ) → imaginaryQuaternions)
    (hf : ∀ b ∈ chordBonds (finiteCells F), AnalyticAt ℝ (f b.1 b.2) 0)
    (hg : ∀ y i, AnalyticAt ℝ (g y i) 0) :
    AnalyticAt ℝ (fun τ => chartCoordinates (fun x i => f x i τ) (fun y i => g y i τ)) 0 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FrameCurves.analyticAt_chartCoordinates <;> assumption
theorem iteratedFDeriv_chartCoordinates {k p : ℕ} (f : F.Site F.depth → Fin 4 → (Fin k → ℝ) → imaginaryQuaternions)
    (g : F.Site F.top → Fin 4 → (Fin k → ℝ) → imaginaryQuaternions)
    (hf : ∀ b ∈ chordBonds (finiteCells F), AnalyticAt ℝ (f b.1 b.2) 0)
    (hg : ∀ y i, AnalyticAt ℝ (g y i) 0) (vs : Fin p → Fin k → ℝ) :
    iteratedFDeriv ℝ p (fun τ => chartCoordinates (fun x i => f x i τ) (fun y i => g y i τ)) 0 vs =
      chartCoordinates (fun x i => iteratedFDeriv ℝ p (f x i) 0 vs) (fun y i => iteratedFDeriv ℝ p (g y i) 0 vs) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FrameCurves.iteratedFDeriv_chartCoordinates <;> assumption
theorem iteratedFDeriv_single_eq_bondDeriv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {j k p : ℕ}
    (G : F.GaugeField j → E) (W : F.GaugeField j) (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions)
    (e' : Fin p → Fin k)
    (hG : ContDiffAt ℝ p (fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) W)) 0) :
    iteratedFDeriv ℝ p (fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) W)) 0 (fun l => Pi.single (e' l) 1) =
      bondDeriv G W (c ∘ e') (X ∘ e') := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FrameCurves.iteratedFDeriv_single_eq_bondDeriv <;> assumption
theorem leftTranslate_bondSpread_zero {j k : ℕ} (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions)
    (W : F.GaugeField j) : leftTranslate (bondSpread c X 0) W = W := by apply _root_.YangMills.SharedProofs.p1939 <;> assumption
def bondSpreadCLM {j k : ℕ} (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions) (y : F.Site j)
    (i : Fin 4) : (Fin k → ℝ) →L[ℝ] imaginaryQuaternions :=
  ∑ l, (ContinuousLinearMap.proj l : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (if c l = (y, i) then X l else 0)
theorem bondSpreadCLM_apply {j k : ℕ} (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions)
    (y : F.Site j) (i : Fin 4) (τ : Fin k → ℝ) : bondSpreadCLM c X y i τ = bondSpread c X τ y i := by
  simp only [bondSpreadCLM, bondSpread, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp
theorem weightedNorm_chartCoordinates_le (ψ : F.Cell → ℝ) (hψ : ∀ z, 0 ≤ ψ z)
    (dw : F.Site F.depth → Fin 4 → imaginaryQuaternions) (dv : F.Site F.top → Fin 4 → imaginaryQuaternions) :
    _root_.YangMills.Construction.Calculus.weightedNorm (fun n => ψ (directionCell (chartDirections F n))) (chartCoordinates dw dv) ≤
      3 * (∑ b : ↥(chordBonds (finiteCells F)), ‖dw b.1.1 b.1.2‖ * ψ (enclosingCell b.1.1) +
        ∑ b : ↥(innerBonds (finiteCells F) F.top), ‖dv b.1.1 b.1.2‖ * ψ b.1.1) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FrameCurves.weightedNorm_chartCoordinates_le <;> assumption
def minimizerCurve (a ρ : ℝ) (m : ℕ) (V : F.GaugeField F.top) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ) : Fin (chartDimension F) → ℝ :=
  chartCoordinates (fun x i => stepFrame true a ρ m (x, i) (leftTranslate (bondSpread c X τ) V) - stepFrame true a ρ m (x, i) V)
    (bondSpread c X τ)
def frameGapCurve (a ρ : ℝ) (m : ℕ) (V : F.GaugeField F.top) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ) : Fin (chartDimension F) → ℝ :=
  chartCoordinates (fun x i => frameGap a ρ m (x, i) (leftTranslate (bondSpread c X τ) V)) (fun _ _ => 0)
open Classical in
def bondBump (b : F.Site F.depth × Fin 4) (e : imaginaryQuaternions) (x : F.Site F.depth) (i : Fin 4) :
    imaginaryQuaternions := if (x, i) = b then e else 0
def bondBumpCoordinates (b : F.Site F.depth × Fin 4) (e : imaginaryQuaternions) : Fin (chartDimension F) → ℝ :=
  chartCoordinates (bondBump b e) (fun _ _ => 0)
def chartedEnergyAtMinimizer (a ρ : ℝ) (m : ℕ) (V : F.GaugeField F.top) : (Fin (chartDimension F) → ℝ) → ℝ :=
  chartRestriction a (fun x i => stepFrame true a ρ m (x, i) V) V (chartDirections F)
theorem chartedEnergyAtMinimizer_on_curve (hCE : ChartedEnergyInCoordinates) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) (a ρ : ℝ) (m : ℕ) (V : F.GaugeField F.top) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (τ : Fin k → ℝ) (θ u : ℝ) (b : F.Site F.depth × Fin 4) (e : imaginaryQuaternions) :
    chartedEnergyAtMinimizer a ρ m V (minimizerCurve a ρ m V c X τ + θ • frameGapCurve a ρ m V c X τ + u • bondBumpCoordinates b e) =
      chartedEnergy a (fun x i => interpolatedFrame θ a ρ m (x, i) (leftTranslate (bondSpread c X τ) V) + u • bondBump b e x i)
        (leftTranslate (bondSpread c X τ) V) := by
  have e1 : minimizerCurve a ρ m V c X τ + θ • frameGapCurve a ρ m V c X τ + u • bondBumpCoordinates b e =
      chartCoordinates (fun x i => ((stepFrame true a ρ m (x, i) (leftTranslate (bondSpread c X τ) V) - stepFrame true a ρ m (x, i) V) +
          θ • frameGap a ρ m (x, i) (leftTranslate (bondSpread c X τ) V)) + u • bondBump b e x i)
        (fun y i => (bondSpread c X τ y i + θ • (0 : imaginaryQuaternions)) + u • (0 : imaginaryQuaternions)) := by
    rw [chartCoordinates_add_smul, chartCoordinates_add_smul]
    rfl
  unfold chartedEnergyAtMinimizer
  rw [e1, (hCE F a _ _ V _ hL hs).1]
  have e2 : (fun y i => (bondSpread c X τ y i + θ • (0 : imaginaryQuaternions)) + u • (0 : imaginaryQuaternions)) =
      bondSpread c X τ := by
    funext y i
    simp
  rw [e2]
  congr 1
  funext x i
  simp only [interpolatedFrame, frameGap]
  module
theorem update_add_smul_eq_bondBump (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (b : F.Site F.depth × Fin 4)
    (e : imaginaryQuaternions) (u : ℝ) :
    Function.update w b.1 (Function.update (w b.1) b.2 (w b.1 b.2 + u • e)) = fun x i => w x i + u • bondBump b e x i := by
  classical
  funext x i
  obtain ⟨b1, b2⟩ := b
  by_cases hx : x = b1
  · subst hx
    by_cases hi : i = b2
    · subst hi
      simp [bondBump]
    · simp [bondBump, Function.update_of_ne hi, hi]
  · have : (x, i) ≠ (b1, b2) := fun h => hx (congrArg Prod.fst h)
    simp [bondBump, Function.update_of_ne hx, this]
theorem interpolatedSlope_eq_fderiv (hCE : ChartedEnergyInCoordinates) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (a ρ : ℝ) (m : ℕ) (V : F.GaugeField F.top) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (τ : Fin k → ℝ) (θ : ℝ) (b : F.Site F.depth × Fin 4) (e : imaginaryQuaternions)
    (hd : DifferentiableAt ℝ (chartedEnergyAtMinimizer a ρ m V) (minimizerCurve a ρ m V c X τ + θ • frameGapCurve a ρ m V c X τ)) :
    interpolatedSlope θ a ρ m b e (leftTranslate (bondSpread c X τ) V) =
      fderiv ℝ (chartedEnergyAtMinimizer a ρ m V) (minimizerCurve a ρ m V c X τ + θ • frameGapCurve a ρ m V c X τ)
        (bondBumpCoordinates b e) := by
  unfold interpolatedSlope chartedSlope
  have hline : (fun u : ℝ => chartedEnergy a (Function.update (fun z i => interpolatedFrame θ a ρ m (z, i) (leftTranslate (bondSpread c X τ) V)) b.1
      (Function.update ((fun z i => interpolatedFrame θ a ρ m (z, i) (leftTranslate (bondSpread c X τ) V)) b.1) b.2
        ((fun z i => interpolatedFrame θ a ρ m (z, i) (leftTranslate (bondSpread c X τ) V)) b.1 b.2 + u • e))) (leftTranslate (bondSpread c X τ) V)) =
      fun u : ℝ => chartedEnergyAtMinimizer a ρ m V (minimizerCurve a ρ m V c X τ + θ • frameGapCurve a ρ m V c X τ + u • bondBumpCoordinates b e) := by
    funext u
    rw [chartedEnergyAtMinimizer_on_curve hCE hL hs, update_add_smul_eq_bondBump]
  rw [hline]
  have h1 : HasDerivAt (fun u : ℝ => minimizerCurve a ρ m V c X τ + θ • frameGapCurve a ρ m V c X τ + u • bondBumpCoordinates b e)
      (bondBumpCoordinates b e) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (bondBumpCoordinates b e)).const_add
      (minimizerCurve a ρ m V c X τ + θ • frameGapCurve a ρ m V c X τ)
  have h2 : HasFDerivAt (chartedEnergyAtMinimizer a ρ m V) (fderiv ℝ (chartedEnergyAtMinimizer a ρ m V) (minimizerCurve a ρ m V c X τ + θ • frameGapCurve a ρ m V c X τ))
      ((fun u : ℝ => minimizerCurve a ρ m V c X τ + θ • frameGapCurve a ρ m V c X τ + u • bondBumpCoordinates b e) 0) := by
    simpa using hd.hasFDerivAt
  exact (h2.comp_hasDerivAt (0 : ℝ) h1).deriv
theorem chartedSlope_eq_zero_of_minimizing {a ρ : ℝ} {S : Finset F.Cell} {V : F.GaugeField F.top}
    {w : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (hS : S = finiteCells F) (h : IsMinimizingChart a S V ρ w) (b : F.Site F.depth × Fin 4) (e : imaginaryQuaternions) :
    chartedSlope a w V b e = 0 := by
  subst hS
  unfold chartedSlope
  apply IsLocalMin.deriv_eq_zero
  refine Filter.Eventually.of_forall fun u => ?_
  simp only [zero_smul, add_zero, Function.update_eq_self]
  exact h.2.2 _
theorem chartCoordinates_zero : chartCoordinates (F := F) (fun _ _ => 0) (fun _ _ => 0) = 0 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FrameCurves.chartCoordinates_zero <;> assumption
theorem minimizerCurve_zero (a ρ : ℝ) (m : ℕ) (V : F.GaugeField F.top) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) : minimizerCurve a ρ m V c X 0 = 0 := by
  unfold minimizerCurve
  rw [leftTranslate_bondSpread_zero]
  have e : bondSpread c X 0 = fun _ _ => 0 := by
    funext y i
    simp [bondSpread]
  simp only [sub_self, e]
  exact chartCoordinates_zero
theorem frameGapCurve_zero (a ρ : ℝ) (m : ℕ) (V : F.GaugeField F.top) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) :
    frameGapCurve a ρ m V c X 0 = chartCoordinates (fun x i => frameGap a ρ m (x, i) V) (fun _ _ => 0) := by
  unfold frameGapCurve
  rw [leftTranslate_bondSpread_zero]
theorem analyticAt_curves {a ρ : ℝ} {m : ℕ} {V : F.GaugeField F.top}
    (h1 : ∀ b ∈ chordBonds (finiteCells F), IsBondAnalyticAt (stepFrame true a ρ m b) V)
    (h2 : ∀ b ∈ chordBonds (finiteCells F), IsBondAnalyticAt (stepFrame false a ρ m b) V)
    {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) :
    AnalyticAt ℝ (minimizerCurve a ρ m V c X) 0 ∧ AnalyticAt ℝ (frameGapCurve a ρ m V c X) 0 := by
  have hmove : ∀ y i, AnalyticAt ℝ (fun τ : Fin k → ℝ => bondSpread c X τ y i) 0 := by
    intro y i
    have e : (fun τ : Fin k → ℝ => bondSpread c X τ y i) = bondSpreadCLM c X y i := by
      funext τ
      rw [bondSpreadCLM_apply]
    rw [e]
    exact (bondSpreadCLM c X y i).analyticAt 0
  refine ⟨?_, ?_⟩
  · refine analyticAt_chartCoordinates (fun x i τ => stepFrame true a ρ m (x, i) (leftTranslate (bondSpread c X τ) V) - stepFrame true a ρ m (x, i) V)
      (fun y i τ => bondSpread c X τ y i) (fun b hb => ?_) hmove
    exact (h1 b hb k c X).sub analyticAt_const
  · refine analyticAt_chartCoordinates (fun x i τ => frameGap a ρ m (x, i) (leftTranslate (bondSpread c X τ) V))
      (fun _ _ _ => 0) (fun b hb => ?_) (fun _ _ => analyticAt_const)
    exact (h2 b hb k c X).sub (h1 b hb k c X)
theorem chartedEnergyAtMinimizer_shift (hCE : ChartedEnergyInCoordinates) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (a ρ : ℝ) (m : ℕ) (V : F.GaugeField F.top) (θ : ℝ) (σ : Fin (chartDimension F) → ℝ) :
    chartedEnergyAtMinimizer a ρ m V (θ • chartCoordinates (fun x i => frameGap a ρ m (x, i) V) (fun _ _ => 0) + σ) =
      chartRestriction a (fun x i => interpolatedFrame θ a ρ m (x, i) V) V (chartDirections F) σ := by
  have e1 : θ • chartCoordinates (fun x i => frameGap a ρ m (x, i) V) (fun _ _ => 0) =
      chartCoordinates (fun x i => (0 : imaginaryQuaternions) + θ • frameGap a ρ m (x, i) V)
        (fun _ _ => (0 : imaginaryQuaternions) + θ • (0 : imaginaryQuaternions)) := by
    rw [chartCoordinates_add_smul, chartCoordinates_zero, zero_add]
  have e2 : (fun _ _ => (0 : imaginaryQuaternions) + θ • (0 : imaginaryQuaternions)) =
      (fun (_ : F.Site F.top) (_ : Fin 4) => (0 : imaginaryQuaternions)) := by
    funext y i
    simp
  unfold chartedEnergyAtMinimizer
  rw [e1, e2, (hCE F a _ _ V (fun _ _ => 0) hL hs).2 σ]
  congr 1
  funext x i
  simp only [interpolatedFrame, frameGap]
  module
theorem analyticAt_of_shift {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (A B : E → ℝ) (p : E)
    (h : ∀ σ, A (p + σ) = B σ) (hB : AnalyticAt ℝ B 0) : AnalyticAt ℝ A p := by
  have e : A = B ∘ fun σ => σ - p := by
    funext σ
    simp only [Function.comp]
    rw [← h]
    simp
  rw [e]
  have h0 : AnalyticAt ℝ B ((fun σ : E => σ - p) p) := by simpa using hB
  have h1 : AnalyticAt ℝ (fun σ : E => σ - p) p := by fun_prop
  exact AnalyticAt.comp (f := fun σ : E => σ - p) h0 h1
theorem analyticAt_chartedEnergyAtMinimizer (hCE : ChartedEnergyInCoordinates) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) (a ρ : ℝ) (m : ℕ) (V : F.GaugeField F.top) (θ : ℝ)
    (hB : AnalyticAt ℝ (chartRestriction a (fun x i => interpolatedFrame θ a ρ m (x, i) V) V (chartDirections F)) 0) :
    AnalyticAt ℝ (chartedEnergyAtMinimizer a ρ m V) (θ • chartCoordinates (fun x i => frameGap a ρ m (x, i) V) (fun _ _ => 0)) :=
  analyticAt_of_shift _ _ _ (chartedEnergyAtMinimizer_shift hCE hL hs a ρ m V θ) hB
theorem iteratedFDeriv_comp_add_left_zero {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup H]
    [NormedSpace ℝ H] (f : E → H) (n : ℕ) (p : E) :
    iteratedFDeriv ℝ n (fun z => f (p + z)) 0 = iteratedFDeriv ℝ n f p := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FrameCurves.iteratedFDeriv_comp_add_left_zero <;> assumption
theorem iteratedFDeriv_fderiv_apply {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (A : E → ℝ)
    (v p : E) (hA : AnalyticAt ℝ A p) (l : ℕ) (m : Fin l → E) :
    iteratedFDeriv ℝ l (fun σ => fderiv ℝ A σ v) p m = (iteratedFDeriv ℝ l (fderiv ℝ A) p m) v := by
  have h1 : ContDiffAt ℝ l (fderiv ℝ A) p := hA.fderiv.contDiffAt
  have h2 := ContinuousLinearMap.iteratedFDeriv_comp_left (ContinuousLinearMap.apply ℝ ℝ v) h1 (i := l) le_rfl
  have h3 := congrArg (fun T => T m) h2
  simpa [Function.comp_def] using h3
theorem iteratedFDeriv_fderiv_apply_eq_succ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (A : E → ℝ) (w p : E)
    (l : ℕ) (m : Fin l → E) :
    (iteratedFDeriv ℝ l (fderiv ℝ A) p m) w = iteratedFDeriv ℝ (l + 1) A p (Fin.snoc m w) := by
  rw [iteratedFDeriv_succ_apply_right]
  simp [Fin.init_snoc]
theorem norm_directionVector_chartDirections (n : Fin (chartDimension F)) :
    ‖directionVector (chartDirections F n)‖ = 1 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FrameCurves.norm_directionVector_chartDirections <;> assumption
theorem iteratedFDeriv_single_chartRestriction (a : ℝ) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (V : F.GaugeField F.top) {N l : ℕ} (q : Fin N → ChartDirection F)
    (ρ : Fin l → Fin N) (hB : AnalyticAt ℝ (chartRestriction a w V q) 0) :
    iteratedFDeriv ℝ l (chartRestriction a w V q) 0 (fun j => Pi.single (ρ j) 1) = chartMixedDeriv a w V (q ∘ ρ) := by apply _root_.YangMills.SharedProofs.p3455 <;> assumption
theorem snoc_single_eq {N l : ℕ} (r : Fin l → Fin N) (n : Fin N) :
    (Fin.snoc (fun i => Pi.single (r i) (1 : ℝ)) (Pi.single n 1) : Fin (l + 1) → Fin N → ℝ) =
      fun j => Pi.single ((Fin.snoc r n : Fin (l + 1) → Fin N) j) 1 := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp
  · simp
theorem bondBumpCoordinates_eq_sum (b : F.Site F.depth × Fin 4) (hb : b ∈ chordBonds (finiteCells F))
    (e : imaginaryQuaternions) :
    bondBumpCoordinates b e = ∑ α, imaginaryCoord α e •
      (Pi.single (chartCoordinateEquiv F (.inl (⟨b, hb⟩, α))) (1 : ℝ) : Fin (chartDimension F) → ℝ) := by
  classical
  funext n
  obtain ⟨ι, rfl⟩ := (chartCoordinateEquiv F).surjective n
  simp only [bondBumpCoordinates, chartCoordinates, Equiv.symm_apply_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Pi.single_apply, (chartCoordinateEquiv F).injective.eq_iff]
  rcases ι with ⟨b', β⟩ | ⟨t, β⟩
  · by_cases hbb : b' = ⟨b, hb⟩
    · subst hbb
      simp only [coordinateOfIndex, bondBump]
      simp [Prod.mk.injEq]
    · have hne : (b'.1.1, b'.1.2) ≠ b := fun h => hbb (Subtype.ext h)
      simp only [coordinateOfIndex, bondBump, if_neg hne, map_zero]
      symm
      refine Finset.sum_eq_zero fun α _ => ?_
      rw [if_neg, mul_zero]
      intro h
      have := Sum.inl.inj h
      exact hbb (congrArg Prod.fst this)
  · simp [coordinateOfIndex]
theorem abs_iteratedFDeriv_slope_le (hCE : ChartedEnergyInCoordinates) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (a ρ : ℝ) (m : ℕ) (V : F.GaugeField F.top) (θ : ℝ) (b : F.Site F.depth × Fin 4) (hb : b ∈ chordBonds (finiteCells F))
    (e : imaginaryQuaternions) (he : ‖e‖ = 1) (δ₁ β : ℝ) (hδ₁ : 0 ≤ δ₁) (hβ0 : 0 ≤ β) (l : ℕ) (hl : 1 ≤ l)
    (hβ : (l : ℝ) * β ≤ δ₁) (Ckl : ℝ)
    (hB : AnalyticAt ℝ (chartRestriction a (fun x i => interpolatedFrame θ a ρ m (x, i) V) V (chartDirections F)) 0)
    (hker : ∀ q' : Fin (l + 1) → ChartDirection F, (∀ j, ‖directionVector (q' j)‖ = 1) →
      |chartMixedDeriv a (fun x i => interpolatedFrame θ a ρ m (x, i) V) V q'| ≤
        Ckl * Real.exp (-(δ₁ * directionDiameter q')))
    (r : Fin l → Fin (chartDimension F)) :
    |iteratedFDeriv ℝ l (fun σ => fderiv ℝ (chartedEnergyAtMinimizer a ρ m V) σ (bondBumpCoordinates b e))
        (θ • chartCoordinates (fun x i => frameGap a ρ m (x, i) V) (fun _ _ => 0)) (fun i => Pi.single (r i) 1)| ≤
      3 * Ckl * ∏ i, Real.exp (-(β * cellSupDist (directionCell (chartDirections F (r i))) (enclosingCell b.1))) := by
  classical
  have hA := analyticAt_chartedEnergyAtMinimizer hCE hL hs a ρ m V θ hB
  obtain ⟨p, hp⟩ : ∃ p, p = θ • chartCoordinates (F := F) (fun x i => frameGap a ρ m (x, i) V) (fun _ _ => 0) := ⟨_, rfl⟩
  rw [← hp] at hA ⊢
  rw [iteratedFDeriv_fderiv_apply _ _ _ hA, bondBumpCoordinates_eq_sum b hb e, map_sum]
  simp only [map_smul, smul_eq_mul]
  have hshift : (fun z => chartedEnergyAtMinimizer a ρ m V (p + z)) =
      chartRestriction a (fun x i => interpolatedFrame θ a ρ m (x, i) V) V (chartDirections F) := by
    funext z
    rw [hp, chartedEnergyAtMinimizer_shift hCE hL hs]
  have hterm : ∀ α : Fin 3, |(iteratedFDeriv ℝ l (fderiv ℝ (chartedEnergyAtMinimizer a ρ m V)) p fun i => Pi.single (r i) 1)
      (Pi.single (chartCoordinateEquiv F (.inl (⟨b, hb⟩, α))) (1 : ℝ))| ≤
      Ckl * ∏ i, Real.exp (-(β * cellSupDist (directionCell (chartDirections F (r i))) (enclosingCell b.1))) := by
    intro α
    rw [iteratedFDeriv_fderiv_apply_eq_succ, ← iteratedFDeriv_comp_add_left_zero, hshift, snoc_single_eq,
      iteratedFDeriv_single_chartRestriction _ _ _ _ _ hB]
    obtain ⟨q', hq'⟩ : ∃ q', q' = chartDirections F ∘
        (Fin.snoc r (chartCoordinateEquiv F (.inl (⟨b, hb⟩, α))) : Fin (l + 1) → Fin (chartDimension F)) := ⟨_, rfl⟩
    rw [← hq']
    have hu : ∀ j, ‖directionVector (q' j)‖ = 1 := fun j => by
      rw [hq']
      exact norm_directionVector_chartDirections _
    refine (hker q' hu).trans ?_
    have hlast : directionCell (q' (Fin.last l)) = enclosingCell b.1 := by
      rw [hq']
      simp [chartDirections, directionOfIndex, directionCell]
    have hcast : ∀ i, q' (Fin.castSucc i) = chartDirections F (r i) := fun i => by
      rw [hq']
      simp
    have hd : ∀ i, cellSupDist (directionCell (chartDirections F (r i))) (enclosingCell b.1) ≤ directionDiameter q' := by
      intro i
      rw [← hcast, ← hlast]
      unfold directionDiameter
      refine le_trans ?_ (Finset.le_sup (f := fun l₁ => Finset.univ.sup fun l₂ =>
        cellSupDist (directionCell (q' l₁)) (directionCell (q' l₂))) (Finset.mem_univ (Fin.castSucc i)))
      exact Finset.le_sup (f := fun l₂ => cellSupDist (directionCell (q' (Fin.castSucc i))) (directionCell (q' l₂)))
        (Finset.mem_univ (Fin.last l))
    have hCk0 : 0 ≤ Ckl := by
      have h0 := hker q' hu
      have h1 := (abs_nonneg _).trans h0
      exact nonneg_of_mul_nonneg_left h1 (Real.exp_pos _)
    refine mul_le_mul_of_nonneg_left ?_ hCk0
    rw [← Real.exp_sum]
    apply Real.exp_le_exp.mpr
    rw [Finset.sum_neg_distrib, neg_le_neg_iff, ← Finset.mul_sum]
    have h2 : ∑ i, (cellSupDist (directionCell (chartDirections F (r i))) (enclosingCell b.1) : ℝ) ≤
        l * directionDiameter q' := by
      calc ∑ i, (cellSupDist (directionCell (chartDirections F (r i))) (enclosingCell b.1) : ℝ)
          ≤ ∑ _i : Fin l, (directionDiameter q' : ℝ) := Finset.sum_le_sum fun i _ => by exact_mod_cast hd i
        _ = l * directionDiameter q' := by simp
    have h3 : (0 : ℝ) ≤ directionDiameter q' := by positivity
    calc β * ∑ i, (cellSupDist (directionCell (chartDirections F (r i))) (enclosingCell b.1) : ℝ)
          ≤ β * (l * directionDiameter q') := mul_le_mul_of_nonneg_left h2 hβ0
      _ = ((l : ℝ) * β) * directionDiameter q' := by ring
      _ ≤ δ₁ * directionDiameter q' := mul_le_mul_of_nonneg_right hβ h3
  have hcoef : ∀ α : Fin 3, |imaginaryCoord α e| ≤ 1 := fun α => by
    have := abs_imaginaryCoord_le_norm α e
    rwa [he] at this
  have hP0 : 0 ≤ ∏ i, Real.exp (-(β * cellSupDist (directionCell (chartDirections F (r i))) (enclosingCell b.1))) :=
    Finset.prod_nonneg fun i _ => (Real.exp_pos _).le
  have hCkP : 0 ≤ Ckl * ∏ i, Real.exp (-(β * cellSupDist (directionCell (chartDirections F (r i))) (enclosingCell b.1))) :=
    (abs_nonneg _).trans (hterm 0)
  calc |∑ α, imaginaryCoord α e * (iteratedFDeriv ℝ l (fderiv ℝ (chartedEnergyAtMinimizer a ρ m V)) p fun i =>
          Pi.single (r i) 1) (Pi.single (chartCoordinateEquiv F (.inl (⟨b, hb⟩, α))) (1 : ℝ))|
      ≤ ∑ _α : Fin 3, Ckl * ∏ i, Real.exp (-(β * cellSupDist (directionCell (chartDirections F (r i))) (enclosingCell b.1))) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun α _ => ?_)
        rw [abs_mul]
        exact (mul_le_mul (hcoef α) (hterm α) (abs_nonneg _) zero_le_one).trans (by rw [one_mul])
    _ = 3 * Ckl * ∏ i, Real.exp (-(β * cellSupDist (directionCell (chartDirections F (r i))) (enclosingCell b.1))) := by
        simp
        ring
theorem norm_coe_unitQuaternion (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
theorem eventually_isSmallCurvature_leftTranslate (hexp : ExpUnitLipschitzInjective) (hhol : PathHolonomyLipschitz)
    {j k : ℕ} (hfin : Finite (F.Site j)) {s : ℝ} {W : F.GaugeField j} (hW : IsSmallCurvature s W)
    (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions) :
    ∀ᶠ τ in nhds (0 : Fin k → ℝ), IsSmallCurvature s (leftTranslate (bondSpread c X τ) W) := by
  classical
  have hall : ∀ p : F.Site j × Fin 4 × Fin 4, ∀ᶠ τ in nhds (0 : Fin k → ℝ), p.2.1 < p.2.2 →
      plaquetteDefect (leftTranslate (bondSpread c X τ) W) p < s := by
    intro p
    by_cases hp : p.2.1 < p.2.2
    · have hc : ContinuousAt (fun τ : Fin k → ℝ => plaquetteDefect W p + 4 * ∑ l, |τ l| * ‖X l‖) 0 := by
        have h3 : Continuous fun τ : Fin k → ℝ => ∑ l, |τ l| * ‖X l‖ :=
          continuous_finset_sum _ fun l _ => ((continuous_apply l).abs).mul continuous_const
        exact (continuous_const.add (continuous_const.mul h3)).continuousAt
      have h0 : plaquetteDefect W p + 4 * ∑ l, |(0 : Fin k → ℝ) l| * ‖X l‖ < s := by
        simpa using hW p hp
      filter_upwards [hc.eventually_lt continuousAt_const h0] with τ hτ _
      refine lt_of_le_of_lt ?_ hτ
      have hb : ∀ y i, ‖((leftTranslate (bondSpread c X τ) W y i : UnitQuaternion) : ℍ[ℝ]) -
          ((W y i : UnitQuaternion) : ℍ[ℝ])‖ ≤ ∑ l, |τ l| * ‖X l‖ := by
        intro y i
        have e1 : ((leftTranslate (bondSpread c X τ) W y i : UnitQuaternion) : ℍ[ℝ]) - ((W y i : UnitQuaternion) : ℍ[ℝ]) =
            (((expUnit (bondSpread c X τ y i) : UnitQuaternion) : ℍ[ℝ]) - ((expUnit 0 : UnitQuaternion) : ℍ[ℝ])) *
              ((W y i : UnitQuaternion) : ℍ[ℝ]) := by
          have h0 : ((expUnit (0 : imaginaryQuaternions) : UnitQuaternion) : ℍ[ℝ]) = 1 := by
            simp [expUnit]
          rw [h0, sub_mul, one_mul]
          rfl
        rw [e1, norm_mul, norm_coe_unitQuaternion, mul_one]
        refine (hexp.1 _ _).trans ?_
        rw [sub_zero]
        unfold bondSpread
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
        split_ifs
        · rw [norm_smul, Real.norm_eq_abs]
        · rw [norm_zero]
          positivity
      have h1 := hhol F j _ _ _ hb p.1 [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)]
      unfold plaquetteDefect plaquetteHolonomy
      have h3 := norm_sub_le_norm_sub_add_norm_sub
        (((pathHolonomy (leftTranslate (bondSpread c X τ) W) p.1
          [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] : UnitQuaternion)) : ℍ[ℝ])
        (((pathHolonomy W p.1 [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] : UnitQuaternion)) : ℍ[ℝ]) 1
      simp only [List.length_cons, List.length_nil] at h1
      push_cast at h1
      linarith
    · exact Filter.Eventually.of_forall fun τ h => absurd h hp
  have hfin2 : Finite (F.Site j × Fin 4 × Fin 4) := inferInstance
  filter_upwards [Filter.eventually_all.mpr hall] with τ hτ p hp
  exact hτ p hp
theorem bondDeriv_coe {j k : ℕ} (G : F.GaugeField j → imaginaryQuaternions) (W : F.GaugeField j)
    (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions)
    (hG : ContDiffAt ℝ k (fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) W)) 0) :
    bondDeriv (fun V => (G V : ℍ[ℝ])) W c X = ((bondDeriv G W c X : imaginaryQuaternions) : ℍ[ℝ]) := by
  unfold bondDeriv
  have h1 := ContinuousLinearMap.iteratedFDeriv_comp_left imaginaryQuaternions.subtypeL hG (i := k) le_rfl
  have h2 := congrArg (fun T => T (fun l => (Pi.single l 1 : Fin k → ℝ))) h1
  simpa [Function.comp_def] using h2
theorem frameGap_norm_bounds {a : ℝ} {L : ℕ} {c : ColdChainParameters} (ha : 1 ≤ a) (hL : Odd L) (hc : c.Admissible a L)
    (hMF : ReflectedFrameChainBounds) {m : ℕ} (hm : 16 ≤ m) {σ : ℝ} (hσ : 0 < σ)
    (hσs : 5 / 4 * σ ≤ c.s₀) (hF : IsBlockTorus L F) {V : F.GaugeField F.top} (hV : IsSmallCurvature (5 / 4 * σ) V)
    (h1 : ∀ b ∈ chordBonds (finiteCells F), IsBondAnalyticAt (stepFrame true a c.ρA m b) V)
    (h2 : ∀ b ∈ chordBonds (finiteCells F), IsBondAnalyticAt (stepFrame false a c.ρA m b) V)
    (b : F.Site F.depth × Fin 4) (hb : b ∈ chordBonds (finiteCells F)) :
    ‖frameGap a c.ρA m b V‖ ≤ frameDecayBound (frameBoundConstant c) c.δ₂ m * σ ∧
    ∀ (k : ℕ) (e : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 → AreUnitVectors X →
      ‖bondDeriv (frameGap a c.ρA m b) V e X‖ ≤
        frameDecayBound (frameBoundConstant c) c.δ₂ m *
          Real.exp (-(c.δ₂ / 4 * bondListDistance (enclosingCell b.1) e)) := by
  classical
  have hCf0 : 0 < frameBoundConstant c := by
    obtain ⟨⟨_, _, _, _, _, hK, _, hKk⟩, _⟩ := hc.classical
    unfold frameBoundConstant
    have h1 := hKk 3
    have h2 : 0 < (16 ^ 3 + 1) * (c.Kk 1 + c.Kk 2 + c.Kk 3) := by
      have a1 := hKk 1
      have a2 := hKk 2
      positivity
    linarith
  have hδ := hc.classical.1.2.2.2.1
  have hgap0 : 0 ≤ frameDecayBound (frameBoundConstant c) c.δ₂ m := by
    unfold frameDecayBound
    positivity
  by_cases hbig : ∀ i, 4 * m + 5 < F.extent i
  · have hfacts := hMF a L c ha hL hc F m σ V hF hm hσ hσs hbig hV
    have hex : frameDeviation a c.ρA m b = fun V' => ((frameGap a c.ρA m b V' : imaginaryQuaternions) : ℍ[ℝ]) := by
      funext V'
      simp [frameDeviation, frameGap, stepFrame, torusCoordinate]
    refine ⟨?_, fun k e X hk hk3 hX => ?_⟩
    · have h3 := ((hfacts.near_minimizer b hb).1)
      rw [hex] at h3
      exact h3
    · have h3 := (hfacts.near_minimizer b hb).2 k e X hk hk3 hX
      rw [hex, bondDeriv_coe _ V e X ((((h2 b hb k e X).sub (h1 b hb k e X))).contDiffAt)] at h3
      rw [Submodule.coe_norm]
      refine h3.trans ?_
      unfold frameDecayBound
      rw [mul_assoc, ← Real.exp_add]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hCf0.le
      have hmx : ((bondListDistance (enclosingCell b.1) e : ℕ) : ℝ) ≤
          ((max m (bondListDistance (enclosingCell b.1) e) : ℕ) : ℝ) := by
        exact_mod_cast le_max_right _ _
      have := mul_le_mul_of_nonneg_left hmx (by positivity : 0 ≤ c.δ₂ / 4)
      nlinarith
  · have hz : ∀ V' : F.GaugeField F.top, frameGap a c.ρA m b V' = 0 := by
      intro V'
      simp [frameGap, stepFrame, bondFrameCoord, if_neg hbig]
    have hfun : frameGap a c.ρA m b = fun _ => 0 := funext hz
    refine ⟨by rw [hz, norm_zero]; positivity, fun k e X _ _ _ => ?_⟩
    rw [hfun]
    unfold bondDeriv
    have : iteratedFDeriv ℝ k (fun _ : Fin k → ℝ => (0 : imaginaryQuaternions)) 0 = 0 := by
      rw [iteratedFDeriv_zero_fun]
      rfl
    simp only [this]
    simp only [ContinuousMultilinearMap.zero_apply, norm_zero]
    positivity
theorem sum_norm_mul_exp_le {Y : F.Cell} {β β₀ κ M G Sq : ℝ} (hβ₀ : 0 ≤ β₀) (hβ₀κ : β₀ ≤ κ) (hM : 0 ≤ M)
    (dw : F.Site F.depth → Fin 4 → imaginaryQuaternions) (Db : F.Site F.depth × Fin 4 → ℕ)
    (hd : ∀ b ∈ chordBonds (finiteCells F), ‖dw b.1 b.2‖ ≤ M * Real.exp (-(κ * Db b)))
    (hG : ∀ b ∈ chordBonds (finiteCells F), G ≤ Db b + cellSupDist (enclosingCell b.1) Y)
    (hSq : ∑ b ∈ chordBonds (finiteCells F), Real.exp (-((β - β₀) * cellSupDist (enclosingCell b.1) Y)) ≤ Sq) :
    ∑ b : ↥(chordBonds (finiteCells F)), ‖dw b.1.1 b.1.2‖ * Real.exp (-(β * cellSupDist (enclosingCell b.1.1) Y)) ≤
      M * Sq * Real.exp (-(β₀ * G)) := by
  rw [Finset.sum_coe_sort (chordBonds (finiteCells F))
    (fun b => ‖dw b.1 b.2‖ * Real.exp (-(β * cellSupDist (enclosingCell b.1) Y)))]
  have hterm : ∀ b ∈ chordBonds (finiteCells F), ‖dw b.1 b.2‖ * Real.exp (-(β * cellSupDist (enclosingCell b.1) Y)) ≤
      M * Real.exp (-(β₀ * G)) * Real.exp (-((β - β₀) * cellSupDist (enclosingCell b.1) Y)) := by
    intro b hb
    have h1 := hd b hb
    have h2 := hG b hb
    calc ‖dw b.1 b.2‖ * Real.exp (-(β * cellSupDist (enclosingCell b.1) Y))
        ≤ (M * Real.exp (-(κ * Db b))) * Real.exp (-(β * cellSupDist (enclosingCell b.1) Y)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = M * Real.exp (-(κ * Db b) + -(β * cellSupDist (enclosingCell b.1) Y)) := by rw [Real.exp_add]; ring
      _ ≤ M * Real.exp (-(β₀ * G) + -((β - β₀) * cellSupDist (enclosingCell b.1) Y)) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hM
          have hD0 : (0 : ℝ) ≤ Db b := by positivity
          have h3 : β₀ * Db b ≤ κ * Db b := mul_le_mul_of_nonneg_right hβ₀κ hD0
          have h4 := mul_le_mul_of_nonneg_left h2 hβ₀
          nlinarith
      _ = _ := by rw [Real.exp_add]; ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  calc M * Real.exp (-(β₀ * G)) * ∑ b ∈ chordBonds (finiteCells F), Real.exp (-((β - β₀) * cellSupDist (enclosingCell b.1) Y))
      ≤ M * Real.exp (-(β₀ * G)) * Sq := mul_le_mul_of_nonneg_left hSq (by positivity)
    _ = _ := by ring
theorem iteratedFDeriv_continuousLinearMap_eq_zero {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H] (M : E →L[ℝ] H) (p : ℕ) (hp : 2 ≤ p) (vs : Fin p → E) :
    iteratedFDeriv ℝ p M 0 vs = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  rw [iteratedFDeriv_succ_apply_right]
  have e : (fun y => fderiv ℝ M y) = fun _ => M := by
    funext y
    exact M.fderiv
  rw [e, iteratedFDeriv_const_of_ne (by omega)]
  rfl
theorem iteratedFDeriv_one_bondSpread {j k : ℕ} (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions)
    (y : F.Site j) (i : Fin 4) (e₀ : Fin k) (vs : Fin 1 → Fin k → ℝ) (hvs : vs 0 = Pi.single e₀ 1) :
    iteratedFDeriv ℝ 1 (fun τ : Fin k → ℝ => bondSpread c X τ y i) 0 vs = if c e₀ = (y, i) then X e₀ else 0 := by
  classical
  have e : (fun τ : Fin k → ℝ => bondSpread c X τ y i) = bondSpreadCLM c X y i := by
    funext τ
    rw [bondSpreadCLM_apply]
  rw [e, iteratedFDeriv_one_apply, (bondSpreadCLM c X y i).fderiv, hvs, bondSpreadCLM_apply]
  simp only [bondSpread]
  rw [Finset.sum_eq_single e₀]
  · simp
  · intro b _ hb
    split_ifs
    · simp [Pi.single_apply, hb]
    · rfl
  · simp
end InterpolatedSlopeLemmas
set_option maxHeartbeats 4000000 in
open InterpolatedSlopeLemmas in
theorem interpolatedSlopeBounds_holds (hcover : BlocksCoverLowerLevel)
    (hMF : ReflectedFrameChainBounds) (hKer : ChartEnergyKernelBound)
    (hCE : ChartedEnergyInCoordinates) (hSeg : IteratedDerivAlongSegmentBound)
    (hSm : framesSmallStatement) (hGeo : CubicTorusCellGeometry)
    (hexp : ExpUnitLipschitzInjective) (hhol : PathHolonomyLipschitz) :
    interpolatedSlopeBounds := by
  classical
  intro a L c ha hL hL40 hc
  obtain ⟨⟨hρ0, hρ1, hs₀, hδ, hκ, hK, hC, hKk⟩, hcl⟩ := hc.classical
  have hδ₁ : 0 < c.δ₁ := hc.positivity.1
  have h64 : 2 ^ 6 * c.δ₂ ≤ c.δ₁ := hc.inequalities.2.1
  obtain ⟨Ck, hCk, hker⟩ := hKer a L c ha hL hL40 hc
  obtain ⟨Csm, σs, hCsm, hσs0, hsmall⟩ := hSm a L c ha hL hc
  obtain ⟨β, hβdef⟩ : ∃ β, β = c.δ₁ / 4 := ⟨_, rfl⟩
  obtain ⟨β₀, hβ₀def⟩ : ∃ β₀, β₀ = c.δ₂ / 4 := ⟨_, rfl⟩
  have hβ₀0 : 0 < β₀ := by rw [hβ₀def]; positivity
  have hββ₀ : β₀ < β := by rw [hβ₀def, hβdef]; linarith
  have hβ0 : 0 < β := by linarith
  have hβκ : β₀ ≤ c.κ₂ := by rw [hβ₀def]; linarith
  obtain ⟨Sg, hSg, hsum⟩ := hGeo.2 (β - β₀) (by linarith)
  have hLpos : (0 : ℝ) < L := by
    have : 0 < L := lt_of_lt_of_le (by positivity) hL40
    exact_mod_cast this
  obtain ⟨Sq, hSqdef⟩ : ∃ Sq, Sq = Sg * (L : ℝ) ^ 4 := ⟨_, rfl⟩
  have hSq0 : 0 ≤ Sq := by rw [hSqdef]; positivity
  have hKs0 : 0 < c.Kk 1 + c.Kk 2 + c.Kk 3 := by
    have a1 := hKk 1
    have a2 := hKk 2
    have a3 := hKk 3
    linarith
  obtain ⟨Ms, hMsdef⟩ : ∃ Ms, Ms = 16 ^ 3 * (c.Kk 1 + c.Kk 2 + c.Kk 3) := ⟨_, rfl⟩
  have hMs0 : 0 ≤ Ms := by rw [hMsdef]; positivity
  obtain ⟨Km, hKmdef⟩ : ∃ Km, Km = 3 * (Ck 2 + Ck 3 + Ck 4 + Ck 5) := ⟨_, rfl⟩
  have hKm0 : 0 ≤ Km := by
    rw [hKmdef]
    have a2 := hCk 2
    have a3 := hCk 3
    have a4 := hCk 4
    have a5 := hCk 5
    positivity
  obtain ⟨C₁, hC₁def⟩ : ∃ C₁, C₁ = 3 * (Ms * Sq + 1 + Sq) + 1 := ⟨_, rfl⟩
  have hC₁1 : 1 ≤ C₁ := by
    rw [hC₁def]
    have : 0 ≤ Ms * Sq := by positivity
    linarith
  have hseg : ∀ k, 0 ≤ segmentConstant k Km C₁ := fun k => by
    unfold segmentConstant
    have : 0 ≤ C₁ := by linarith
    positivity
  obtain ⟨Cf, hCfdef⟩ : ∃ Cf, Cf = 1 + segmentConstant 0 Km C₁ + segmentConstant 1 Km C₁ + segmentConstant 2 Km C₁ +
      segmentConstant 3 Km C₁ := ⟨_, rfl⟩
  have hCf1 : 1 ≤ Cf := by
    rw [hCfdef]
    have a0 := hseg 0
    have a1 := hseg 1
    have a2 := hseg 2
    have a3 := hseg 3
    linarith
  refine ⟨Cf, min (min σs 1) (min (4 / 5 * c.s₀) (1 / (64 * L * (Csm + 1)))), hCf1, ?_, ?_⟩
  · refine lt_min (lt_min hσs0 one_pos) (lt_min (by positivity) ?_)
    have : 0 < Csm + 1 := by linarith
    positivity
  intro σ m F V hσ hσ₁ hm hgap hF hV s hs b hb e
  have hσsm : σ ≤ σs := hσ₁.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hσ1 : σ ≤ 1 := hσ₁.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hσs : 5 / 4 * σ ≤ c.s₀ := by
    have : σ ≤ 4 / 5 * c.s₀ := hσ₁.trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hσL : (Csm + 1) * σ ≤ 1 / (64 * L) := by
    have h1 : σ ≤ 1 / (64 * L * (Csm + 1)) := hσ₁.trans ((min_le_right _ _).trans (min_le_right _ _))
    have h2 : 0 < Csm + 1 := by linarith
    rw [le_div_iff₀ (by positivity)] at h1
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hspos : 0 < 5 / 4 * σ := by positivity
  have hσA : 5 / 4 * σ ≤ c.σA := by
    have h1 := hc.inequalities.2.2.1
    linarith
  obtain ⟨hFL, n, hn, hside⟩ := id hF
  have hOdd : Odd F.blockSide := hFL ▸ hL
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by rw [hside]; omega
  have hs0 : ∀ i, 0 < F.extent i := fun i => by have := hs2 i; omega
  have hfr := hsmall σ m F V hσ hσsm hm hgap hF hV
  have hSt := hfr.1 true
  have hSf := hfr.1 false
  have hnc := hfr.2
  have h1 := hSt.analytic
  have h2 := hSf.analytic
  have hdiff := fun b' hb' => frameGap_norm_bounds ha hL hc hMF hm hσ hσs hF hV h1 h2 b' hb'
  obtain ⟨ω, hωdef⟩ : ∃ ω, ω = frameDecayBound (frameBoundConstant c) c.δ₂ m := ⟨_, rfl⟩
  rw [← hωdef] at hgap hdiff ⊢
  have hω0 : 0 ≤ ω := by
    have := (hdiff b hb).1
    have h3 := (norm_nonneg _).trans this
    exact nonneg_of_mul_nonneg_left h3 hσ
  have hω1 : ω ≤ 1 := by
    have h3 : (2 : ℝ)⁻¹ ^ 10 * σ ≤ 1 := by
      have : (2 : ℝ)⁻¹ ^ 10 = 1 / 1024 := by norm_num
      rw [this]
      linarith
    linarith
  have hεσ : ω * σ ≤ σ / 1024 := by
    have h3 := mul_le_mul_of_nonneg_right hgap hσ.le
    have h4 : (2 : ℝ)⁻¹ ^ 10 * σ * σ ≤ (2 : ℝ)⁻¹ ^ 10 * σ * 1 := mul_le_mul_of_nonneg_left hσ1 (by positivity)
    have h5 : (2 : ℝ)⁻¹ ^ 10 * σ * 1 = σ / 1024 := by
      norm_num
      ring
    linarith
  have hclose : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ b' ∈ chordBonds (finiteCells F),
      ‖interpolatedFrame θ a c.ρA m b' V - stepFrame true a c.ρA m b' V‖ ≤ σ / 1024 := by
    intro θ hθ b' hb'
    have e1 : interpolatedFrame θ a c.ρA m b' V - stepFrame true a c.ρA m b' V = θ • frameGap a c.ρA m b' V := by
      simp only [interpolatedFrame, frameGap]
      module
    rw [e1, norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ.1]
    have h3 := (hdiff b' hb').1
    have h4 := norm_nonneg (frameGap a c.ρA m b' V)
    have h5 : θ * ‖frameGap a c.ρA m b' V‖ ≤ ‖frameGap a c.ρA m b' V‖ := by nlinarith [hθ.2]
    linarith
  have hpoint : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      IsAdmissibleChartPoint L c.σA (fun x i => interpolatedFrame θ a c.ρA m (x, i) V) V := by
    intro θ hθ
    refine ⟨fun b' hb' => ?_, ?_⟩
    · have h3 := hclose θ hθ b' hb'
      have h4 := hSt.norm_le b' hb'
      have h5 := norm_le_norm_add_norm_sub' (interpolatedFrame θ a c.ρA m b' V) (stepFrame true a c.ρA m b' V)
      have h6 : Csm * σ + σ / 1024 ≤ (Csm + 1) * σ := by nlinarith
      exact h5.trans (by linarith)
    · have h3 := hnc (fun x i => interpolatedFrame θ a c.ρA m (x, i) V) (fun b' hb' => by
        have h4 := hclose θ hθ b' hb'
        have e1 : stepFrame true a c.ρA m b' V = minimizingCoordinates a (finiteCells F) V c.ρA b'.1 b'.2 := by
          simp [stepFrame, minimizingBondCoordinate]
        rw [← e1]
        exact h4)
      intro p hp
      refine (h3 p hp).trans_le ?_
      linarith
  have hker' := fun θ hθ => hker F _ V hF (hpoint θ hθ)
  have hB : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      AnalyticAt ℝ (chartRestriction a (fun x i => interpolatedFrame θ a c.ρA m (x, i) V) V (chartDirections F)) 0 :=
    fun θ hθ => (hker' θ hθ _ (chartDirections F)).1
  obtain ⟨D₀, hD₀⟩ : ∃ D₀, D₀ = chartCoordinates (F := F) (fun x i => frameGap a c.ρA m (x, i) V) (fun _ _ => 0) :=
    ⟨_, rfl⟩
  have hA : ∀ θ ∈ Set.Icc (0 : ℝ) 1, AnalyticAt ℝ (chartedEnergyAtMinimizer a c.ρA m V) (θ • D₀) := fun θ hθ => by
    rw [hD₀]
    exact analyticAt_chartedEnergyAtMinimizer hCE hOdd hs2 a c.ρA m V θ (hB θ hθ)
  obtain ⟨v, hv⟩ : ∃ v, v = bondBumpCoordinates b e := ⟨_, rfl⟩
  have hval : ∀ {k : ℕ} (c' : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (θ : ℝ),
      minimizerCurve a c.ρA m V c' X 0 + θ • frameGapCurve a c.ρA m V c' X 0 = θ • D₀ := by
    intro k c' X θ
    rw [minimizerCurve_zero, frameGapCurve_zero, zero_add, hD₀]
  have hev : ∀ (k : ℕ) (c' : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      (fun τ : Fin k → ℝ => interpolatedSlope θ a c.ρA m b e (leftTranslate (bondSpread c' X τ) V)) =ᶠ[nhds 0]
        (fun σ' => fderiv ℝ (chartedEnergyAtMinimizer a c.ρA m V) σ' v) ∘
          fun τ => minimizerCurve a c.ρA m V c' X τ + θ • frameGapCurve a c.ρA m V c' X τ := by
    intro k c' X θ hθ
    obtain ⟨hP, hD⟩ := analyticAt_curves h1 h2 c' X
    have hcont : ContinuousAt (fun τ => minimizerCurve a c.ρA m V c' X τ + θ • frameGapCurve a c.ρA m V c' X τ) 0 :=
      hP.continuousAt.add (hD.continuousAt.const_smul θ)
    have hev0 := (hA θ hθ).eventually_analyticAt
    have hev1 : ∀ᶠ y in nhds (minimizerCurve a c.ρA m V c' X 0 + θ • frameGapCurve a c.ρA m V c' X 0),
        AnalyticAt ℝ (chartedEnergyAtMinimizer a c.ρA m V) y := by
      rw [hval]
      exact hev0
    filter_upwards [hcont.eventually hev1] with τ hτ
    simp only [Function.comp]
    rw [hv]
    exact interpolatedSlope_eq_fderiv hCE hOdd hs2 a c.ρA m V c' X τ θ b e hτ.differentiableAt
  have hgA : ∀ (k : ℕ) (c' : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      AnalyticAt ℝ ((fun σ' => fderiv ℝ (chartedEnergyAtMinimizer a c.ρA m V) σ' v) ∘
        fun τ => minimizerCurve a c.ρA m V c' X τ + θ • frameGapCurve a c.ρA m V c' X τ) 0 := by
    intro k c' X θ hθ
    obtain ⟨hP, hD⟩ := analyticAt_curves h1 h2 c' X
    have h3 : AnalyticAt ℝ (fun σ' => fderiv ℝ (chartedEnergyAtMinimizer a c.ρA m V) σ' v)
        (minimizerCurve a c.ρA m V c' X 0 + θ • frameGapCurve a c.ρA m V c' X 0) := by
      rw [hval]
      have h4 := (hA θ hθ).fderiv
      have h5 : AnalyticAt ℝ (fun M : (Fin (chartDimension F) → ℝ) →L[ℝ] ℝ => M v)
          (fderiv ℝ (chartedEnergyAtMinimizer a c.ρA m V) (θ • D₀)) :=
        (ContinuousLinearMap.apply ℝ ℝ v).analyticAt _
      exact h5.comp h4
    have hc : AnalyticAt ℝ (fun τ => minimizerCurve a c.ρA m V c' X τ + θ • frameGapCurve a c.ρA m V c' X τ) 0 := by
      fun_prop
    exact AnalyticAt.comp (f := fun τ => minimizerCurve a c.ρA m V c' X τ + θ • frameGapCurve a c.ρA m V c' X τ) h3 hc
  refine ⟨?_, fun k c' X => ((hgA k c' X s hs).contDiffAt).congr_of_eventuallyEq (hev k c' X s hs), ?_⟩
  · have hfun : energyAlongInterpolatedBond s a c.ρA m b e V =
        fun u => chartedEnergyAtMinimizer a c.ρA m V (s • D₀ + u • v) := by
      funext u
      have h3 := chartedEnergyAtMinimizer_on_curve hCE hOdd hs2 a c.ρA m V (fun l : Fin 0 => l.elim0)
        (fun l : Fin 0 => l.elim0) 0 s u b e
      rw [minimizerCurve_zero, frameGapCurve_zero, zero_add, leftTranslate_bondSpread_zero, ← hD₀] at h3
      rw [hv, h3]
      unfold energyAlongInterpolatedBond
      exact congrArg (fun w => chartedEnergy a w V)
        (update_add_smul_eq_bondBump (fun z i => interpolatedFrame s a c.ρA m (z, i) V) b e u)
    rw [hfun]
    have h3 : DifferentiableAt ℝ (chartedEnergyAtMinimizer a c.ρA m V) ((fun u : ℝ => s • D₀ + u • v) 0) := by
      simpa using (hA s hs).differentiableAt
    exact h3.comp (0 : ℝ) (by fun_prop)
  · intro he k c' X hk3 hX
    obtain ⟨hP, hD⟩ := analyticAt_curves h1 h2 c' X
    obtain ⟨Y, hY⟩ : ∃ Y, Y = enclosingCell b.1 := ⟨_, rfl⟩
    obtain ⟨hsym, htri⟩ : (∀ x y : F.Cell, cellSupDist x y = cellSupDist y x) ∧
        (∀ x y z : F.Cell, cellSupDist x z ≤ cellSupDist x y + cellSupDist y z) := by
      have h3 := hGeo.1 F hOdd hF.2
      exact ⟨h3.2.2.1, h3.2.2.2.1⟩
    have hSqsum : ∑ b' ∈ chordBonds (finiteCells F), Real.exp (-((β - β₀) * cellSupDist (enclosingCell b'.1) Y)) ≤ Sq := by
      have h3 := hsum F hOdd hF.2 Y
      rw [hFL] at h3
      rw [hSqdef]
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => (Real.exp_pos _).le) h3
      intro b' hb'
      have h4 := (Finset.mem_filter.mp hb').1
      have h5 := (Finset.mem_filter.mp h4).1
      exact h5
    have hGb : ∀ (p : ℕ) (e' : Fin p → Fin k), ∀ b' ∈ chordBonds (finiteCells F),
        ((bondListDistance Y (c' ∘ e') : ℕ) : ℝ) ≤
          bondListDistance (enclosingCell b'.1) (c' ∘ e') + cellSupDist (enclosingCell b'.1) Y := by
      intro p e' b' _
      have h3 : bondListDistance Y (c' ∘ e') ≤
          bondListDistance (enclosingCell b'.1) (c' ∘ e') + cellSupDist (enclosingCell b'.1) Y := by
        refine Finset.sup_le fun l _ => ?_
        have h4 := htri Y (enclosingCell b'.1) ((c' ∘ e') l).1
        have h5 : cellSupDist (enclosingCell b'.1) ((c' ∘ e') l).1 ≤ bondListDistance (enclosingCell b'.1) (c' ∘ e') :=
          Finset.le_sup (f := fun l => cellSupDist (enclosingCell b'.1) ((c' ∘ e') l).1) (Finset.mem_univ l)
        have h6 := hsym Y (enclosingCell b'.1)
        omega
      exact_mod_cast h3
    have hsup : ∀ (p : ℕ) (e' : Fin p → Fin k),
        ((Finset.univ.image e').sup fun l => cellSupDist Y (c' l).1) = bondListDistance Y (c' ∘ e') := by
      intro p e'
      rw [Finset.sup_image]
      rfl
    have hunits : ∀ (p : ℕ) (e' : Fin p → Fin k), AreUnitVectors (X ∘ e') := fun p e' l => hX (e' l)
    have hψ : ∀ z : F.Cell, 0 ≤ Real.exp (-(β * cellSupDist z Y)) := fun z => (Real.exp_pos _).le
    have hNP : ∀ (p : ℕ) (e' : Fin p → Fin k), 0 < p → Function.Injective e' →
        _root_.YangMills.Construction.Calculus.weightedNorm (fun n => Real.exp (-(β * cellSupDist (directionCell (chartDirections F n)) Y)))
          (iteratedFDeriv ℝ p (minimizerCurve a c.ρA m V c' X) 0 (fun l => Pi.single (e' l) 1)) ≤
          C₁ * Real.exp (-(β₀ * (((Finset.univ.image e').sup fun l => cellSupDist Y (c' l).1 : ℕ) : ℝ))) := by
      intro p e' hp hinj
      rw [hsup]
      have hpk : p ≤ k := by simpa using Fintype.card_le_of_injective e' hinj
      have hp3 : p ≤ 3 := hpk.trans hk3
      have hf : ∀ b' ∈ chordBonds (finiteCells F), AnalyticAt ℝ (fun τ : Fin k → ℝ =>
          stepFrame true a c.ρA m (b'.1, b'.2) (leftTranslate (bondSpread c' X τ) V) -
            stepFrame true a c.ρA m (b'.1, b'.2) V) 0 :=
        fun b' hb' => (h1 b' hb' k c' X).sub analyticAt_const
      have hg : ∀ (y : F.Site F.top) (i : Fin 4), AnalyticAt ℝ (fun τ : Fin k → ℝ => bondSpread c' X τ y i) 0 := by
        intro y i
        have e1 : (fun τ : Fin k → ℝ => bondSpread c' X τ y i) = bondSpreadCLM c' X y i := by
          funext τ
          rw [bondSpreadCLM_apply]
        rw [e1]
        exact (bondSpreadCLM c' X y i).analyticAt 0
      have hform := iteratedFDeriv_chartCoordinates (fun x i τ => stepFrame true a c.ρA m (x, i) (leftTranslate (bondSpread c' X τ) V) -
        stepFrame true a c.ρA m (x, i) V) (fun y i τ => bondSpread c' X τ y i) hf hg (fun l => Pi.single (e' l) 1)
      change _root_.YangMills.Construction.Calculus.weightedNorm _ (iteratedFDeriv ℝ p (fun τ => chartCoordinates (fun x i =>
        stepFrame true a c.ρA m (x, i) (leftTranslate (bondSpread c' X τ) V) - stepFrame true a c.ρA m (x, i) V)
        (fun y i => bondSpread c' X τ y i)) 0 (fun l => Pi.single (e' l) 1)) ≤ _
      rw [hform]
      refine (weightedNorm_chartCoordinates_le (fun z => Real.exp (-(β * cellSupDist z Y))) hψ _ _).trans ?_
      have hdw : ∀ b' ∈ chordBonds (finiteCells F), ‖iteratedFDeriv ℝ p (fun τ : Fin k → ℝ =>
          stepFrame true a c.ρA m (b'.1, b'.2) (leftTranslate (bondSpread c' X τ) V) - stepFrame true a c.ρA m (b'.1, b'.2) V) 0
          (fun l => Pi.single (e' l) 1)‖ ≤
            Ms * Real.exp (-(c.κ₂ * bondListDistance (enclosingCell b'.1) (c' ∘ e'))) := by
        intro b' hb'
        have hGc : ContDiffAt ℝ p (fun τ : Fin k → ℝ => stepFrame true a c.ρA m b' (leftTranslate (bondSpread c' X τ) V)) 0 :=
          (h1 b' hb' k c' X).contDiffAt
        have e1 : (fun τ : Fin k → ℝ => stepFrame true a c.ρA m (b'.1, b'.2) (leftTranslate (bondSpread c' X τ) V) -
            stepFrame true a c.ρA m (b'.1, b'.2) V) =
            (fun τ : Fin k → ℝ => stepFrame true a c.ρA m b' (leftTranslate (bondSpread c' X τ) V)) -
              fun _ => stepFrame true a c.ρA m b' V := rfl
        rw [e1, iteratedFDeriv_sub_apply hGc contDiffAt_const, iteratedFDeriv_const_of_ne hp.ne']
        simp only [sub_zero, Pi.zero_apply, ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.zero_apply]
        rw [iteratedFDeriv_single_eq_bondDeriv _ V c' X e' hGc]
        refine (hSt.deriv_bound b' hb' p (c' ∘ e') (X ∘ e') hp (hunits p e')).trans ?_
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        rw [hMsdef]
        have a1 := hKk 1
        have a2 := hKk 2
        have a3 := hKk 3
        have hpw : (16 : ℝ) ^ p ≤ 16 ^ 3 := pow_le_pow_right₀ (by norm_num) hp3
        have hkp : c.Kk p ≤ c.Kk 1 + c.Kk 2 + c.Kk 3 := by
          interval_cases p <;> linarith
        exact mul_le_mul hpw hkp (hKk p).le (by norm_num)
      have hc1 := sum_norm_mul_exp_le (Y := Y) (β := β) hβ₀0.le hβκ hMs0
        (fun x i => iteratedFDeriv ℝ p (fun τ : Fin k → ℝ => stepFrame true a c.ρA m (x, i) (leftTranslate (bondSpread c' X τ) V) -
          stepFrame true a c.ρA m (x, i) V) 0 (fun l => Pi.single (e' l) 1))
        (fun b' => bondListDistance (enclosingCell b'.1) (c' ∘ e')) hdw (hGb p e') hSqsum
      have htop : ∑ t : ↥(innerBonds (finiteCells F) F.top), ‖iteratedFDeriv ℝ p (fun τ : Fin k → ℝ =>
          bondSpread c' X τ t.1.1 t.1.2) 0 (fun l => Pi.single (e' l) 1)‖ * Real.exp (-(β * cellSupDist t.1.1 Y)) ≤
          Real.exp (-(β₀ * (bondListDistance Y (c' ∘ e') : ℝ))) := by
        by_cases hp1 : p = 1
        · subst hp1
          have hform2 : ∀ (y : F.Site F.top) (i : Fin 4), iteratedFDeriv ℝ 1 (fun τ : Fin k → ℝ => bondSpread c' X τ y i) 0
              (fun l => Pi.single (e' l) 1) = if c' (e' 0) = (y, i) then X (e' 0) else 0 :=
            fun y i => iteratedFDeriv_one_bondSpread c' X y i (e' 0) _ rfl
          simp only [hform2]
          have hEnn := (Real.exp_pos (-(β₀ * (bondListDistance Y (c' ∘ e') : ℝ)))).le
          by_cases hmem : c' (e' 0) ∈ innerBonds (finiteCells F) F.top
          · rw [Finset.sum_eq_single (⟨c' (e' 0), hmem⟩ : ↥(innerBonds (finiteCells F) F.top))]
            · simp only [Prod.mk.eta, if_true]
              rw [hX (e' 0), one_mul]
              apply Real.exp_le_exp.mpr
              have h3 : bondListDistance Y (c' ∘ e') ≤ cellSupDist (c' (e' 0)).1 Y := by
                refine Finset.sup_le fun l _ => ?_
                have : l = 0 := Subsingleton.elim _ _
                subst this
                exact le_of_eq (hsym _ _)
              have h4 : ((bondListDistance Y (c' ∘ e') : ℕ) : ℝ) ≤ cellSupDist (c' (e' 0)).1 Y := by exact_mod_cast h3
              have h5 : (0 : ℝ) ≤ cellSupDist (c' (e' 0)).1 Y := by positivity
              have h6 := mul_le_mul_of_nonneg_left h4 hβ₀0.le
              have h7 := mul_le_mul_of_nonneg_right hββ₀.le h5
              linarith
            · intro t _ ht
              have hne : c' (e' 0) ≠ (t.1.1, t.1.2) := fun h => ht (Subtype.ext h.symm)
              rw [if_neg hne, norm_zero, zero_mul]
            · intro h
              exact absurd (Finset.mem_univ _) h
          · refine le_trans (le_of_eq (Finset.sum_eq_zero fun t _ => ?_)) hEnn
            have hne : c' (e' 0) ≠ (t.1.1, t.1.2) := fun h => hmem (h ▸ t.2)
            rw [if_neg hne, norm_zero, zero_mul]
        · have hz : ∀ (y : F.Site F.top) (i : Fin 4), iteratedFDeriv ℝ p (fun τ : Fin k → ℝ => bondSpread c' X τ y i) 0
              (fun l => Pi.single (e' l) 1) = 0 := by
            intro y i
            have e1 : (fun τ : Fin k → ℝ => bondSpread c' X τ y i) = bondSpreadCLM c' X y i := by
              funext τ
              rw [bondSpreadCLM_apply]
            rw [e1]
            exact iteratedFDeriv_continuousLinearMap_eq_zero _ p (by omega) _
          simp only [hz, norm_zero, zero_mul, Finset.sum_const_zero]
          exact (Real.exp_pos _).le
      have hE := Real.exp_pos (-(β₀ * (bondListDistance Y (c' ∘ e') : ℝ)))
      have hfin : 3 * (Ms * Sq * Real.exp (-(β₀ * (bondListDistance Y (c' ∘ e') : ℝ))) +
          Real.exp (-(β₀ * (bondListDistance Y (c' ∘ e') : ℝ)))) ≤
            C₁ * Real.exp (-(β₀ * (bondListDistance Y (c' ∘ e') : ℝ))) := by
        rw [hC₁def]
        have h3 : 0 ≤ Sq * Real.exp (-(β₀ * (bondListDistance Y (c' ∘ e') : ℝ))) := by positivity
        nlinarith
      refine le_trans ?_ hfin
      exact mul_le_mul_of_nonneg_left (add_le_add hc1 htop) (by norm_num)
    have hND : ∀ (p : ℕ) (e' : Fin p → Fin k), 0 < p → Function.Injective e' →
        _root_.YangMills.Construction.Calculus.weightedNorm (fun n => Real.exp (-(β * cellSupDist (directionCell (chartDirections F n)) Y)))
          (iteratedFDeriv ℝ p (frameGapCurve a c.ρA m V c' X) 0 (fun l => Pi.single (e' l) 1)) ≤
          C₁ * ω * Real.exp (-(β₀ * (((Finset.univ.image e').sup fun l => cellSupDist Y (c' l).1 : ℕ) : ℝ))) := by
      intro p e' hp hinj
      rw [hsup]
      have hpk : p ≤ k := by simpa using Fintype.card_le_of_injective e' hinj
      have hp3 : p ≤ 3 := hpk.trans hk3
      have hf : ∀ b' ∈ chordBonds (finiteCells F), AnalyticAt ℝ (fun τ : Fin k → ℝ =>
          frameGap a c.ρA m (b'.1, b'.2) (leftTranslate (bondSpread c' X τ) V)) 0 :=
        fun b' hb' => (h2 b' hb' k c' X).sub (h1 b' hb' k c' X)
      have hform := iteratedFDeriv_chartCoordinates (fun x i τ => frameGap a c.ρA m (x, i) (leftTranslate (bondSpread c' X τ) V))
        (fun _ _ _ => 0) hf (fun _ _ => analyticAt_const) (fun l => Pi.single (e' l) 1)
      change _root_.YangMills.Construction.Calculus.weightedNorm _ (iteratedFDeriv ℝ p (fun τ => chartCoordinates (fun x i =>
        frameGap a c.ρA m (x, i) (leftTranslate (bondSpread c' X τ) V)) (fun _ _ => 0)) 0 (fun l => Pi.single (e' l) 1)) ≤ _
      rw [hform]
      refine (weightedNorm_chartCoordinates_le (fun z => Real.exp (-(β * cellSupDist z Y))) hψ _ _).trans ?_
      have hdw : ∀ b' ∈ chordBonds (finiteCells F), ‖iteratedFDeriv ℝ p (fun τ : Fin k → ℝ =>
          frameGap a c.ρA m (b'.1, b'.2) (leftTranslate (bondSpread c' X τ) V)) 0
          (fun l => Pi.single (e' l) 1)‖ ≤ ω * Real.exp (-(β₀ * bondListDistance (enclosingCell b'.1) (c' ∘ e'))) := by
        intro b' hb'
        have hGc : ContDiffAt ℝ p (fun τ : Fin k → ℝ => frameGap a c.ρA m b' (leftTranslate (bondSpread c' X τ) V)) 0 :=
          (hf b' hb').contDiffAt
        have hs1 := iteratedFDeriv_single_eq_bondDeriv (frameGap a c.ρA m b') V c' X e' hGc
        change ‖iteratedFDeriv ℝ p (fun τ : Fin k → ℝ => frameGap a c.ρA m b' (leftTranslate (bondSpread c' X τ) V)) 0 _‖ ≤ _
        rw [hs1, hβ₀def]
        exact (hdiff b' hb').2 p _ _ hp hp3 (hunits p e')
      have hc1 := sum_norm_mul_exp_le (Y := Y) (β := β) hβ₀0.le le_rfl hω0
        (fun x i => iteratedFDeriv ℝ p (fun τ : Fin k → ℝ => frameGap a c.ρA m (x, i) (leftTranslate (bondSpread c' X τ) V)) 0
          (fun l => Pi.single (e' l) 1))
        (fun b' => bondListDistance (enclosingCell b'.1) (c' ∘ e')) hdw (hGb p e') hSqsum
      simp only [iteratedFDeriv_zero_fun, Pi.zero_apply, ContinuousMultilinearMap.zero_apply, norm_zero, zero_mul,
        Finset.sum_const_zero, add_zero]
      have hE := Real.exp_pos (-(β₀ * (bondListDistance Y (c' ∘ e') : ℝ)))
      have h3 : 3 * (ω * Sq * Real.exp (-(β₀ * (bondListDistance Y (c' ∘ e') : ℝ)))) ≤
          C₁ * ω * Real.exp (-(β₀ * (bondListDistance Y (c' ∘ e') : ℝ))) := by
        have h4 : 3 * Sq ≤ C₁ := by
          rw [hC₁def]
          have : 0 ≤ Ms * Sq := by positivity
          linarith
        have h5 : 0 ≤ ω * Real.exp (-(β₀ * (bondListDistance Y (c' ∘ e') : ℝ))) := by positivity
        nlinarith
      exact (mul_le_mul_of_nonneg_left hc1 (by norm_num)).trans h3
    have hD0 : _root_.YangMills.Construction.Calculus.weightedNorm (fun n => Real.exp (-(β * cellSupDist (directionCell (chartDirections F n)) Y)))
        (frameGapCurve a c.ρA m V c' X 0) ≤ C₁ * ω := by
      rw [frameGapCurve_zero]
      refine (weightedNorm_chartCoordinates_le (fun z => Real.exp (-(β * cellSupDist z Y))) hψ _ _).trans ?_
      have hdw : ∀ b' ∈ chordBonds (finiteCells F), ‖frameGap a c.ρA m (b'.1, b'.2) V‖ ≤
          ω * Real.exp (-(β₀ * ((fun _ : F.Site F.depth × Fin 4 => (0 : ℕ)) b' : ℝ))) := by
        intro b' hb'
        have h3 := (hdiff b' hb').1
        simp only [Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, mul_one]
        nlinarith
      have hc1 := sum_norm_mul_exp_le (Y := Y) (β := β) (G := 0) hβ₀0.le le_rfl hω0
        (fun x i => frameGap a c.ρA m (x, i) V) (fun _ => 0) hdw (fun b' _ => by positivity) hSqsum
      simp only [Pi.zero_apply, norm_zero, zero_mul, Finset.sum_const_zero, add_zero, mul_zero, neg_zero, Real.exp_zero,
        mul_one] at hc1 ⊢
      have h4 : 3 * Sq ≤ C₁ := by
        rw [hC₁def]
        have : 0 ≤ Ms * Sq := by positivity
        linarith
      nlinarith
    have hprod : ∀ cc : OrderedFinpartition k, ∏ i, Real.exp (-(β₀ * (((Finset.univ.image (cc.emb i)).sup
        fun l => cellSupDist Y (c' l).1 : ℕ) : ℝ))) ≤ Real.exp (-(β₀ * bondListDistance Y c')) := by
      intro cc
      have hone : ∀ I : Finset (Fin k), Real.exp (-(β₀ * ((I.sup fun l => cellSupDist Y (c' l).1 : ℕ) : ℝ))) ≤ 1 := by
        intro I
        apply Real.exp_le_one_iff.mpr
        have : (0 : ℝ) ≤ ((I.sup fun l => cellSupDist Y (c' l).1 : ℕ) : ℝ) := by positivity
        have := mul_nonneg hβ₀0.le this
        linarith
      by_cases hD0' : bondListDistance Y c' = 0
      · rw [hD0']
        simp only [Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero]
        exact Finset.prod_le_one (fun i _ => (Real.exp_pos _).le) fun i _ => hone _
      · obtain ⟨l₀, _, hl₀⟩ : ∃ l₀ ∈ (Finset.univ : Finset (Fin k)), bondListDistance Y c' = cellSupDist Y (c' l₀).1 := by
          have hne : (Finset.univ : Finset (Fin k)).Nonempty := by
            by_contra hcon
            rw [Finset.not_nonempty_iff_eq_empty] at hcon
            apply hD0'
            unfold bondListDistance
            rw [hcon, Finset.sup_empty]
            rfl
          exact Finset.exists_mem_eq_sup _ hne _
        obtain ⟨i₀, j₀, hij⟩ : ∃ i₀ j₀, cc.emb i₀ j₀ = l₀ := ⟨_, _, cc.emb_invEmbedding l₀⟩
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i₀)]
        have h3 : Real.exp (-(β₀ * (((Finset.univ.image (cc.emb i₀)).sup fun l => cellSupDist Y (c' l).1 : ℕ) : ℝ))) ≤
            Real.exp (-(β₀ * bondListDistance Y c')) := by
          apply Real.exp_le_exp.mpr
          have h4 : bondListDistance Y c' ≤ (Finset.univ.image (cc.emb i₀)).sup fun l => cellSupDist Y (c' l).1 := by
            rw [hl₀]
            exact Finset.le_sup (f := fun l => cellSupDist Y (c' l).1)
              (Finset.mem_image.mpr ⟨j₀, Finset.mem_univ _, hij⟩)
          have h5 : (bondListDistance Y c' : ℝ) ≤
              (((Finset.univ.image (cc.emb i₀)).sup fun l => cellSupDist Y (c' l).1 : ℕ) : ℝ) := by
            exact_mod_cast h4
          have := mul_le_mul_of_nonneg_left h5 hβ₀0.le
          linarith
        have h6 : ∏ i ∈ Finset.univ.erase i₀, Real.exp (-(β₀ * (((Finset.univ.image (cc.emb i)).sup
            fun l => cellSupDist Y (c' l).1 : ℕ) : ℝ))) ≤ 1 :=
          Finset.prod_le_one (fun i _ => (Real.exp_pos _).le) fun i _ => hone _
        have h7 : 0 ≤ ∏ i ∈ Finset.univ.erase i₀, Real.exp (-(β₀ * (((Finset.univ.image (cc.emb i)).sup
            fun l => cellSupDist Y (c' l).1 : ℕ) : ℝ))) := Finset.prod_nonneg fun i _ => (Real.exp_pos _).le
        exact (mul_le_mul h3 h6 h7 (Real.exp_pos _).le).trans (by rw [mul_one])
    have hH0 : iteratedFDeriv ℝ k ((fun σ' => fderiv ℝ (chartedEnergyAtMinimizer a c.ρA m V) σ' v) ∘
        minimizerCurve a c.ρA m V c' X) 0 (fun l => Pi.single l 1) = 0 := by
      have hfinS : Finite (F.Site F.top) := by
        have : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by
          simp only [BlockFrame.period, Nat.sub_self, pow_zero, mul_one]
          have := hs0 i
          omega⟩
        have : ∀ i, Finite (ZMod (F.period F.top i)) := fun i => inferInstance
        exact Pi.finite
      have hz : ∀ᶠ τ in nhds (0 : Fin k → ℝ),
          interpolatedSlope 0 a c.ρA m b e (leftTranslate (bondSpread c' X τ) V) = 0 := by
        filter_upwards [eventually_isSmallCurvature_leftTranslate hexp hhol hfinS hV c' X] with τ hτ
        have hl := (hcl F (5 / 4 * σ) (leftTranslate (bondSpread c' X τ) V) hF hspos hσs hτ).1
        unfold interpolatedSlope
        have e1 : (fun z i => interpolatedFrame 0 a c.ρA m (z, i) (leftTranslate (bondSpread c' X τ) V)) =
            minimizingCoordinates a (finiteCells F) (leftTranslate (bondSpread c' X τ) V) c.ρA := by
          funext z i
          simp [interpolatedFrame, stepFrame, minimizingBondCoordinate]
        rw [e1]
        exact chartedSlope_eq_zero_of_minimizing rfl hl b e
      have h3 := hev k c' X 0 (Set.left_mem_Icc.mpr zero_le_one)
      have e0 : (fun τ => minimizerCurve a c.ρA m V c' X τ + (0 : ℝ) • frameGapCurve a c.ρA m V c' X τ) =
          minimizerCurve a c.ρA m V c' X := by
        funext τ
        simp
      rw [e0] at h3
      have h4 : ((fun σ' => fderiv ℝ (chartedEnergyAtMinimizer a c.ρA m V) σ' v) ∘ minimizerCurve a c.ρA m V c' X) =ᶠ[nhds 0]
          fun _ => 0 :=
        h3.symm.trans hz
      rw [(Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) h4 k).eq_of_nhds, iteratedFDeriv_zero_fun]
      rfl
    have hKb : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ (l : ℕ), 1 ≤ l → l ≤ k + 1 → ∀ r : Fin l → Fin (chartDimension F),
        |iteratedFDeriv ℝ l (fun σ' => fderiv ℝ (chartedEnergyAtMinimizer a c.ρA m V) σ' v)
          (θ • frameGapCurve a c.ρA m V c' X 0) (fun i => Pi.single (r i) 1)| ≤
          Km * ∏ i, Real.exp (-(β * cellSupDist (directionCell (chartDirections F (r i))) Y)) := by
      intro θ hθ l hl1 hl2 r
      rw [frameGapCurve_zero, hv, hY]
      have hl4 : l ≤ 4 := by omega
      have hl5 : (l : ℝ) * β ≤ c.δ₁ := by
        have h3 : (l : ℝ) ≤ 4 := by exact_mod_cast hl4
        rw [hβdef]
        nlinarith
      have h3 := abs_iteratedFDeriv_slope_le hCE hOdd hs2 a c.ρA m V θ b hb e he c.δ₁ β hδ₁.le hβ0.le l hl1 hl5 (Ck (l + 1))
        (hB θ hθ) (fun q' hu => (hker' θ hθ _ q').2 (by omega) hu) r
      refine h3.trans (mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun i _ => (Real.exp_pos _).le))
      rw [hKmdef]
      have a2 := hCk 2
      have a3 := hCk 3
      have a4 := hCk 4
      have a5 := hCk 5
      interval_cases l <;> simp <;> linarith
    have hmain := hSeg (chartDimension F) k (chartedEnergyAtMinimizer a c.ρA m V) v (minimizerCurve a c.ρA m V c' X)
      (frameGapCurve a c.ρA m V c' X)
      (fun n => Real.exp (-(β * cellSupDist (directionCell (chartDirections F n)) Y))) Km C₁ ω s
      (Real.exp (-(β₀ * bondListDistance Y c')))
      (fun I => Real.exp (-(β₀ * ((I.sup fun l => cellSupDist Y (c' l).1 : ℕ) : ℝ))))
      (fun _ => (Real.exp_pos _).le) (minimizerCurve_zero a c.ρA m V c' X) hP hD
      (fun θ hθ => by
        rw [frameGapCurve_zero, ← hD₀]
        exact hA θ hθ)
      hKb hH0 hNP hND hD0
      (fun I => ⟨(Real.exp_pos _).le, by
        apply Real.exp_le_one_iff.mpr
        have : (0 : ℝ) ≤ ((I.sup fun l => cellSupDist Y (c' l).1 : ℕ) : ℝ) := by positivity
        have := mul_nonneg hβ₀0.le this
        linarith⟩) hprod hKm0 hC₁1 hω0 hω1 hs
    have hdev : bondDeriv (interpolatedSlope s a c.ρA m b e) V c' X =
        iteratedFDeriv ℝ k ((fun σ' => fderiv ℝ (chartedEnergyAtMinimizer a c.ρA m V) σ' v) ∘
          fun τ => minimizerCurve a c.ρA m V c' X τ + s • frameGapCurve a c.ρA m V c' X τ) 0 (fun l => Pi.single l 1) := by
      unfold bondDeriv
      rw [(Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) (hev k c' X s hs) k).eq_of_nhds]
    rw [hdev]
    refine hmain.trans ?_
    have hsegk : segmentConstant k Km C₁ ≤ Cf := by
      rw [hCfdef]
      have a0 := hseg 0
      have a1 := hseg 1
      have a2 := hseg 2
      have a3 := hseg 3
      interval_cases k <;> linarith
    have hexpb : Real.exp (-(β₀ * bondListDistance Y c')) ≤
        Real.exp (-(c.δ₂ / 8 * bondListDistance (enclosingCell b.1) c')) := by
      rw [← hY, hβ₀def]
      apply Real.exp_le_exp.mpr
      have h3 : (0 : ℝ) ≤ bondListDistance Y c' := by positivity
      have h4 := mul_nonneg hδ.le h3
      nlinarith
    exact mul_le_mul (mul_le_mul_of_nonneg_right hsegk hω0) hexpb (Real.exp_pos _).le
      (mul_nonneg (by linarith) hω0)
end ColdStepAtMirrorFrames
end YangMills.Construction
end
