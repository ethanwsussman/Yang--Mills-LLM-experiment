import YangMills.Construction.ClusterExpansionOfAStep.BasesAtABlock
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.TorusLumps
open BlockAverages LumpContours TorusFields
def BondKernelBorel : Prop :=
  ∀ (ℓ : StepParameters) (x : ℝ) (n : ℕ) [NeZero n],
    (Set.range fun W : TorusField (n * ℓ.side) => fineHotLumps ℓ (fineLevelField ℓ n W)).Finite ∧
    (Set.range fun W : TorusField (n * ℓ.side) => baseChoices ℓ (fineLevelField ℓ n W)).Finite ∧
    (∀ H, MeasurableSet {W : TorusField (n * ℓ.side) | fineHotLumps ℓ (fineLevelField ℓ n W) = H}) ∧
    (∀ A, MeasurableSet {W : TorusField (n * ℓ.side) | baseChoices ℓ (fineLevelField ℓ n W) = A}) ∧
    (∀ (H : Finset (Finset ((stepBlockFrame ℓ.side n).Site 0)))
      (b : (stepBlockFrame ℓ.side n).Cell → (stepBlockFrame ℓ.side n).Site 0)
      (c : (stepBlockFrame ℓ.side n).Cell × Fin 4),
      ContinuousOn (fun W : TorusField (n * ℓ.side) =>
          contourMean ℓ.baseDepth (fineHotLumps ℓ (fineLevelField ℓ n W)) b (fineLevelField ℓ n W) c)
        {W | fineHotLumps ℓ (fineLevelField ℓ n W) = H}) ∧
    (∀ (b : (stepBlockFrame ℓ.side n).Cell → (stepBlockFrame ℓ.side n).Site 0)
      (c : (stepBlockFrame ℓ.side n).Cell × Fin 4),
      Measurable fun p : TorusField (n * ℓ.side) × TorusField n =>
        bondKernel ℓ x (fineLevelField ℓ n p.1) (coarseLevelField ℓ n p.2) b c) ∧
    (Measurable fun p : TorusField (n * ℓ.side) × TorusField n =>
        averagedKernel ℓ x (fineLevelField ℓ n p.1) (coarseLevelField ℓ n p.2)) ∧
    ∀ (W : (stepBlockFrame ℓ.side n).GaugeField 0)
      (b : (stepBlockFrame ℓ.side n).Cell → (stepBlockFrame ℓ.side n).Site 0)
      (c : (stepBlockFrame ℓ.side n).Cell × Fin 4) (V : TorusField n) (k : ℕ) (e : Fin k → TorusBond n)
      (X : Fin k → imaginaryQuaternions),
      AnalyticAt ℝ (fun t : Fin k → ℝ => bondKernel ℓ x W (coarseLevelField ℓ n (perturb e X t V)) b c) 0
end YangMills.Construction.TorusLumps
end
