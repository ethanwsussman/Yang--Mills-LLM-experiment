import YangMills.Construction.CellOfTheFlow.WindowsOfACell
import YangMills.Construction.ResponseInTheExpansion.CurvatureOfALevelOnTheDraws
import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
open YangMills.Construction.TorusLumps YangMills.Construction.WeightedResponses
open YangMills.Construction.ResponseInTheExpansion YangMills.Construction.RenormalizationStepParameters
def CoarserSteps (p : StepParameters) : ℕ → ℕ → Type
  | 0, _ => Unit
  | d + 1, n => CoarserSteps p d (n * p.side) × StepOutcome p n
instance CoarserSteps.instMeasurableSpace (p : StepParameters) : (d n : ℕ) → MeasurableSpace (CoarserSteps p d n)
  | 0, _ => inferInstanceAs (MeasurableSpace Unit)
  | d + 1, n =>
    letI := CoarserSteps.instMeasurableSpace p d (n * p.side)
    inferInstanceAs (MeasurableSpace (CoarserSteps p d (n * p.side) × StepOutcome p n))
def coarserStepsOf (p : StepParameters) (s : ℕ) : (d n : ℕ) → MarkedSample p (s + d) n → CoarserSteps p d n
  | 0, _, _ => ()
  | d + 1, n, u => (coarserStepsOf p s d (n * p.side) u.1, u.2)
def coarseSigma {p : StepParameters} (T : StageTower p) (s d n : ℕ) [NeZero n] : MeasurableSpace (MarkedSample p (s + d) n) :=
  MeasurableSpace.comap
    (fun u => (stageState T s (fineSide p.side d n) (sampleBelow p s d n u), coarserStepsOf p s d n u)) inferInstance
def conditionalBoundLiftsStatement : Prop :=
  HoldsAtAdmissibleParameters fun Tb y => ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (s d : ℕ),
    IsTowerAtParametersMeasurable Tb y T β (s + d) →
    ∀ (n : ℕ) [NeZero n] (E : Set (MarkedSample (Tb.stepParameters y) s (fineSide (Tb.stepParameters y).side d n)))
      (c : ENNReal),
      MeasurableSet E →
      (∀ A', MeasurableSet[stageSigma T s (fineSide (Tb.stepParameters y).side d n)] A' →
        markedSampleLaw T β s (fineSide (Tb.stepParameters y).side d n) (A' ∩ E) ≤
          c * markedSampleLaw T β s (fineSide (Tb.stepParameters y).side d n) A') →
      ∀ B, MeasurableSet[coarseSigma T s d n] B →
        markedSampleLaw T β (s + d) n (B ∩ {u | sampleBelow (Tb.stepParameters y) s d n u ∈ E}) ≤
          c * markedSampleLaw T β (s + d) n B
end YangMills.Construction.CellWindows
end
