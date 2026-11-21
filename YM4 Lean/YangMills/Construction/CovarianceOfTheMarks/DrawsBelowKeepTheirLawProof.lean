import YangMills.Construction.CovarianceOfTheMarks.DrawsBelowKeepTheirLaw
import YangMills.Construction.ResponseInTheExpansion.LawOfTheDrawsBelowProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.BoxMarks
open StepSettings StepCosts TorusFields TorusLumps WeightedResponses ResponseInTheExpansion ColdStepAtMirrorFrames
section ProductKernel
variable {A D : Type} {mA : MeasurableSpace A} {mD : MeasurableSpace D} {μ : Measure A} {ρ : Measure D} [SFinite ρ]
private theorem map_fst_prod_withDensity [IsProbabilityMeasure μ] {w : A × D → ℝ} (hw : Measurable w)
    (hmass : ∀ a, ∫⁻ d, ENNReal.ofReal (w (a, d)) ∂ρ = 1) :
    Measure.map (Prod.fst : A × D → A) ((μ.prod ρ).withDensity fun u => ENNReal.ofReal (w u)) = μ := by
  ext B hB
  rw [Measure.map_apply measurable_fst hB, ← Set.prod_univ, withDensity_apply _ (hB.prod .univ),
    ← Measure.prod_restrict, Measure.restrict_univ, lintegral_prod _ hw.ennreal_ofReal.aemeasurable]
  simp [hmass]
end ProductKernel
section Outcomes
variable {ℓ : TorusLumps.StepParameters}
private instance (m : ℕ) [NeZero m] : Fintype (BondSet m) := inferInstanceAs (Fintype (Finset (TorusBond m)))
private theorem measurable_of_stepOutcome {X : Type} [MeasurableSpace X] {n : ℕ} [NeZero n]
    {f : X × StepOutcome ℓ n → ℝ}
    (h : ∀ (b : BaseChoice ℓ.side n) (bad : BondSet (n * ℓ.side)),
      Measurable fun q : X × TorusField n => f (q.1, (b, q.2, bad))) : Measurable f := by apply _root_.YangMills.SharedProofs.p21057 <;> assumption
private instance (ℓ : TorusLumps.StepParameters) (n : ℕ) [NeZero n] : IsFiniteMeasure (stepReferenceMeasure ℓ n) := by
  unfold stepReferenceMeasure
  infer_instance
end Outcomes
section SingleStep
variable (R : StepSetup) {n : ℕ} [NeZero n]
private theorem measurable_stepOutcomeDensity (hS : StepTransitionDensityBounds)
    (hB : ∀ bad : Finset (TorusBond (n * R.params.side)),
      Measurable fun q : TorusField (n * R.params.side) × TorusField n => markLaw R q.1 q.2 bad) :
    Measurable fun q : TorusField (n * R.params.side) × StepOutcome R.params n => stepOutcomeDensity R q.1 q.2 :=
  measurable_of_stepOutcome fun b bad => ((hS R.params R.coupling n).1 b).mul (hB bad)
private theorem lintegral_stepOutcomeDensity (hS : StepTransitionDensityBounds) (hM : ScoreProductStepMean)
    (hf : R.params.Admissible) (hfl : 11 * 2 ^ 12 * R.params.baseDepth < R.params.side)
    (hc : IsCutoff R.ballRadius R.barrierFn)
    (hB : ∀ bad : Finset (TorusBond (n * R.params.side)),
      Measurable fun q : TorusField (n * R.params.side) × TorusField n => markLaw R q.1 q.2 bad)
    (W : TorusField (n * R.params.side)) :
    ∫⁻ d, ENNReal.ofReal (stepOutcomeDensity R W d) ∂(stepReferenceMeasure R.params n) = 1 := by apply _root_.YangMills.SharedProofs.p27860 <;> assumption
end SingleStep
section Tower
variable {ℓ : TorusLumps.StepParameters}
private theorem stage_isCutoff (T : StageTower ℓ) (h : IsCutoff (ℓ.threshold / 64) T.base.barrierFn) (t : ℕ) :
    IsCutoff (T.stage t).toStepSetup.ballRadius (T.stage t).toStepSetup.barrierFn := by apply _root_.YangMills.SharedProofs.p16 <;> assumption
private theorem measurable_topField : ∀ s n : ℕ, Measurable (topField ℓ s n)
  | 0, _ => measurable_id
  | s + 1, n => by
    exact show Measurable fun u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n => u.2.2.1 from
      measurable_fst.comp (measurable_snd.comp measurable_snd)
private theorem measurable_sampleBelow (s : ℕ) : ∀ d n : ℕ, Measurable (sampleBelow ℓ s d n)
  | 0, _ => measurable_id
  | d + 1, n => (measurable_sampleBelow s d (n * ℓ.side)).comp measurable_fst
variable (hS : StepTransitionDensityBounds) (hM : ScoreProductStepMean)
  (hf : ℓ.Admissible) (hfl : 11 * 2 ^ 12 * ℓ.baseDepth < ℓ.side) (T : StageTower ℓ)
  (hcut : IsCutoff (ℓ.threshold / 64) T.base.barrierFn) (hcoin : T.MarksMeasurable) (β : ℝ)
private def stageKernel (T : StageTower ℓ) (s n : ℕ) [NeZero n]
    (u : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n) : ℝ :=
  stepOutcomeDensity (T.stage s).toStepSetup (topField ℓ s (n * ℓ.side) u.1) u.2
include hS hcoin in
private theorem measurable_stageKernel (s n : ℕ) [NeZero n] : Measurable (stageKernel T s n) := by apply _root_.YangMills.DeltaSharedProofs.p500627 <;> assumption
include hS hM hf hfl hcut hcoin in
private theorem lintegral_stageKernel (s n : ℕ) [NeZero n] (a : MarkedSample ℓ s (n * ℓ.side)) :
    ∫⁻ d, ENNReal.ofReal (stageKernel T s n (a, d)) ∂(stepReferenceMeasure ℓ n) = 1 := by apply _root_.YangMills.DeltaSharedProofs.p501759 <;> assumption
include hS hM hf hfl hcut hcoin in
private theorem isProbabilityMeasure_markedSampleLaw (s : ℕ) :
    ∀ (n : ℕ) [NeZero n], IsProbabilityMeasure (markedSampleLaw T β s n) := by apply _root_.YangMills.SharedProofs.p20096 <;> assumption
include hS hM hf hfl hcut hcoin in
private theorem map_fst_markedSampleLaw (s n : ℕ) [NeZero n] :
    Measure.map (fun u : MarkedSample ℓ (s + 1) n => u.1) (markedSampleLaw T β (s + 1) n) =
      markedSampleLaw T β s (n * ℓ.side) := by
  have := isProbabilityMeasure_markedSampleLaw hS hM hf hfl T hcut hcoin β s (n * ℓ.side)
  exact map_fst_prod_withDensity (μ := markedSampleLaw T β s (n * ℓ.side)) (ρ := stepReferenceMeasure ℓ n)
    (w := stageKernel T s n)
    (measurable_stageKernel hS T hcoin s n) (lintegral_stageKernel hS hM hf hfl T hcut hcoin s n)
include hS hM hf hfl hcut hcoin in
private theorem map_sampleBelow (k s : ℕ) : ∀ (n : ℕ) [NeZero n],
    Measure.map (sampleBelow ℓ k s n) (markedSampleLaw T β (k + s) n) =
      markedSampleLaw T β k (fineSide ℓ.side s n) := by
  induction s with
  | zero =>
    intro n _
    exact Measure.map_id
  | succ s ih =>
    intro n _
    have h1 := map_fst_markedSampleLaw hS hM hf hfl T hcut hcoin β (k + s) n
    have h2 : Measurable fun u : MarkedSample ℓ (k + s + 1) n => u.1 :=
      (measurable_fst : Measurable (Prod.fst : MarkedSample ℓ (k + s) (n * ℓ.side) × StepOutcome ℓ n → _))
    have h3 := Measure.map_map (μ := markedSampleLaw T β (k + s + 1) n) (measurable_sampleBelow k s (n * ℓ.side)) h2
    rw [h1, ih (n * ℓ.side)] at h3
    exact h3.symm
end Tower
theorem lowerMarginal (hS : StepTransitionDensityBounds) (hM : ScoreProductStepMean) :
    lowerMarginalStatement := by
  intro ℓ hf hfl T hcut hcoin β k s N _
  exact map_sampleBelow hS hM hf hfl T hcut hcoin β k s N
end YangMills.Construction.BoxMarks
end
