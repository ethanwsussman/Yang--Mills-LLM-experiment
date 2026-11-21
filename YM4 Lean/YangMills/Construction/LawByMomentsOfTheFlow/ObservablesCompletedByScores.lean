import YangMills.Construction.ResponseInTheExpansion.StatesAlongTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace WeightedResponses
open TorusLumps StepSettings
variable {p : StepParameters}
def cumulativeSource (T : StageTower p) (α : ℕ → ℝ) :
    (s n : ℕ) → [NeZero n] → PlaquetteWeight (fineSide p.side s n) → MarkedSample p s n → ℝ
  | 0, _, _, _, _ => 0
  | s + 1, n, _, w, x => cumulativeSource T α s (n * p.side) w x.1 + sourceTerm T α s n w x
def completedObservable (T : StageTower p) (α : ℕ → ℝ) (s n : ℕ) [NeZero n]
    (w : PlaquetteWeight (fineSide p.side s n)) (x : MarkedSample p s n) : ℝ :=
  curvatureObservable w (bottomField p s n x) + cumulativeSource T α s n w x
def conditionalCenteredProduct (T : StageTower p) (β : ℝ) (α : ℕ → ℝ) (s n : ℕ) [NeZero n] {k : ℕ}
    (w : Fin k → PlaquetteWeight (fineSide p.side s n)) (B : Finset (Fin k)) (c : Fin k → ℝ) :
    MarkedSample p s n → ℝ :=
  (markedSampleLaw T β s n)[fun x => ∏ i ∈ B, (completedObservable T α s n (w i) x - c i) | stageSigma T s n]
end WeightedResponses
end YangMills.Construction
end
