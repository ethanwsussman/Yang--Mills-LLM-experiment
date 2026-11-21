import YangMills.Construction.ClusterExpansionOfAStep.WilsonWeightHasAnExpansion
import YangMills.Construction.ResponseInTheExpansion.ScoresOfABond
import YangMills.Construction.ResponseInTheExpansion.WeightsOfAnExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.WeightedResponses
open TorusLumps TorusFields StepCosts BlockAverages LumpContours
instance (L n : ℕ) : MeasurableSpace (BaseChoice L n) := ⊤
def ChainSample (p : StepParameters) : ℕ → ℕ → Type
  | 0, n => TorusField n
  | s + 1, n => ChainSample p s (n * p.side) × BaseChoice p.side n × TorusField n
instance chainSampleMeasurableSpace (p : StepParameters) : (s n : ℕ) → MeasurableSpace (ChainSample p s n)
  | 0, n => inferInstanceAs (MeasurableSpace (TorusField n))
  | s + 1, n =>
    letI := chainSampleMeasurableSpace p s (n * p.side)
    inferInstanceAs (MeasurableSpace (ChainSample p s (n * p.side) × BaseChoice p.side n × TorusField n))
def finalField (p : StepParameters) : (s n : ℕ) → ChainSample p s n → TorusField n
  | 0, _, W => W
  | _ + 1, _, u => u.2.2
def initialField (p : StepParameters) : (s n : ℕ) → ChainSample p s n → TorusField (fineSide p.side s n)
  | 0, _, W => W
  | s + 1, n, u => initialField p s (n * p.side) u.1
def chainReferenceMeasure (p : StepParameters) : (s n : ℕ) → [NeZero n] → Measure (ChainSample p s n)
  | 0, n, _ => fieldHaar n
  | s + 1, n, _ =>
    letI := chainSampleMeasurableSpace p s (n * p.side)
    (chainReferenceMeasure p s (n * p.side)).prod
      ((Measure.count : Measure (BaseChoice p.side n)).prod (fieldHaar n))
def stepTransitionDensity (p : StepParameters) (x : ℝ) {n : ℕ} [NeZero n] (W : TorusField (n * p.side))
    (b : BaseChoice p.side n) (V : TorusField n) : ℝ :=
  open Classical in
  if b ∈ baseChoices p (readAtLevel (stepBlockFrame p.side n) 0 W) then
    (1 / ((baseChoices p (readAtLevel (stepBlockFrame p.side n) 0 W)).card : ℝ)) *
      ∏ c : (stepBlockFrame p.side n).Cell × Fin 4,
        bondKernel p x (readAtLevel (stepBlockFrame p.side n) 0 W) (readAtLevel (stepBlockFrame p.side n) 1 V) b c
  else 0
def chainJointDensity (p : StepParameters) (β : ℝ) (x : ℕ → ℝ) :
    (s n : ℕ) → [NeZero n] → ChainSample p s n → ℝ
  | 0, n, _, W => wilsonWeight β n W / ∫ W', wilsonWeight β n W' ∂(fieldHaar n)
  | s + 1, n, _, u =>
    chainJointDensity p β x s (n * p.side) u.1 *
      stepTransitionDensity p (x s) (finalField p s (n * p.side) u.1) u.2.1 u.2.2
def chainJointLaw (p : StepParameters) (β : ℝ) (x : ℕ → ℝ) (s n : ℕ) [NeZero n] : Measure (ChainSample p s n) :=
  (chainReferenceMeasure p s n).withDensity fun u => ENNReal.ofReal (chainJointDensity p β x s n u)
def chainFunctional (p : StepParameters) (β : ℝ) (x : ℕ → ℝ) : ℕ → TorusFunctional
  | 0 => wilsonWeight β
  | s + 1 => kernelImage p (x s) (chainFunctional p β x s)
def ScoreWeights (p : StepParameters) (m : ℕ) : ℕ → ℕ → Type
  | 0, _ => Unit
  | s + 1, n => ScoreWeights p m s (n * p.side) × (Fin m → TorusBond n → ℝ)
def ScoreWeights.Disjoint {p : StepParameters} {m : ℕ} : (s n : ℕ) → ScoreWeights p m s n → Prop
  | 0, _, _ => True
  | s + 1, n, w => ScoreWeights.Disjoint s (n * p.side) w.1 ∧
      ∀ (c : TorusBond n) (i i' : Fin m), i ≠ i' → w.2 i c = 0 ∨ w.2 i' c = 0
def weightedScoreSum (p : StepParameters) (x : ℕ → ℝ) {m : ℕ} :
    (s n : ℕ) → [NeZero n] → ScoreWeights p m s n → Fin m → ChainSample p s n → ℝ
  | 0, _, _, _, _, _ => 0
  | s + 1, n, _, w, i, u => weightedScoreSum p x s (n * p.side) w.1 i u.1 +
      ∑ c : TorusBond n, w.2 i c * bondScore p (x s) (finalField p s (n * p.side) u.1) u.2.2 u.2.1 c
end YangMills.Construction.WeightedResponses
end
