import YangMills.Construction.FreeEnergiesOfTheFlow.MomentsOfTheFlow
import YangMills.Construction.LawByMomentsOfTheFlow.ObservablesCompletedByScores
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.FreeEnergies
open TorusLumps TorusFields StepGas StepSettings WeightedResponses ResponseInTheExpansion ClusterExpansionOfAStep
variable {ℓ : StepParameters} {T : StageTower ℓ}
def functionSites (L : ℕ) [NeZero L] (f : FinePlaquetteFunction) (s n : ℕ) [NeZero n] : Finset (TorusSite n) :=
  weightSupportSites L s n (fineWeight f (fineSide L s n))
def fittedResponse (S : ScoredStageTower T) (f : FinePlaquetteFunction) (s n : ℕ) [NeZero n]
    (q : StageState T s n) : ℝ :=
  ∑ z ∈ functionSites ℓ.side f s n,
    centeredHullResponse (S.setup s).cold (S.setup s).hull n z q.1 q.2.1 q.2.2 (fineWeight f _)
def scoreMeanOver (S : ScoredStageTower T) (f : FinePlaquetteFunction) (s n : ℕ) [NeZero n]
    (q : StageState T s n) : ℝ :=
  meanSiteScore (S.setup s).score (functionSites ℓ.side f s n) q.2.1 q.2.2
def centering (S : ScoredStageTower T) (f : FinePlaquetteFunction) : (s n : ℕ) → [NeZero n] → ℝ
  | 0, _, _ => 0
  | s + 1, n, _ => centering S f s (n * ℓ.side) +
      caseMean (T.stage s).toStepSetup (n := n) ∅ (trivialField n) (emptyCoarseState _)
        (supportResponseSum (S.setup s) (trivialField n) (fineWeight f _))
def completedCentered (S : ScoredStageTower T) (f : FinePlaquetteFunction) (s n : ℕ) [NeZero n]
    (u : MarkedSample ℓ s n) : ℝ :=
  completedObservable T S.coeffs s n (fineWeight f _) u - centering S f s n
def conditionalProduct (S : ScoredStageTower T) (β : ℝ) {k : ℕ} (f : Fin k → FinePlaquetteFunction)
    (I : Finset (Fin k)) (s n : ℕ) [NeZero n] : MarkedSample ℓ s n → ℝ :=
  (markedSampleLaw T β s n)[fun u => ∏ i ∈ I, completedCentered S (f i) s n u | stageSigma T s n]
variable (T)
def caseLift (s n : ℕ) [NeZero n] (F : TorusField n → CaseFunction (T.stage s).toStepSetup n)
    (x : MarkedSample ℓ (s + 1) n) : ℝ :=
  F x.2.2.1 (topField ℓ s (n * ℓ.side) x.1) (stageState T s (n * ℓ.side) x.1).2.1
    (stageState T s (n * ℓ.side) x.1).2.2 x.2.2.2 x.2.1
def caseMeanAtSample (s n : ℕ) [NeZero n] (F : TorusField n → CaseFunction (T.stage s).toStepSetup n)
    (x : MarkedSample ℓ (s + 1) n) : ℝ :=
  caseMean (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup x.2.2.1) x.2.2.1
    (stageState T (s + 1) n x).2 (F x.2.2.1)
def CaseIntegrableAtSample (s n : ℕ) [NeZero n] (F : TorusField n → CaseFunction (T.stage s).toStepSetup n)
    (x : MarkedSample ℓ (s + 1) n) : Prop :=
  CaseIntegrable (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup x.2.2.1) x.2.2.1
    (stageState T (s + 1) n x).2 (F x.2.2.1)
end YangMills.Construction.FreeEnergies
end
