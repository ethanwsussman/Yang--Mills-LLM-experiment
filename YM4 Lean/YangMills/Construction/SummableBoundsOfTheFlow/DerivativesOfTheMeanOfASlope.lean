import YangMills.Construction.ColdStepAtMirrorFrames.DerivativesOfAWeightedMean
import YangMills.Construction.ColdStepAtMirrorFrames.RimMeanIsAWeightedMean
import YangMills.Construction.SummableBoundsOfTheFlow.ExplicitCumulantsOfMeans
import YangMills.Construction.SummableBoundsOfTheFlow.LogarithmAlongAMovingCut
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.Estimates
namespace YangMills.Construction.Cumulants
def cutoffSlopeMeanDerivFormulas : Prop :=
  ∀ (F : BlockFrame) (ρ : ℝ) (p : ℝ → ℝ) (k : ℕ) (B : Set (Fin k → ℝ)) (K : ℝ)
    (A : (Fin k → ℝ) → StepVariable (finiteCells F) → ℝ)
    (e : (Fin k → ℝ) → StepVariable (finiteCells F)), 0 < ρ → IsCutoff ρ p → IsOpen B →
    IsDominatedSmoothFamily (cutoffLaw F ρ p) 3 B K A → ContDiffOn ℝ 3 e B →
    (∀ j, j ≤ 3 → ∀ t ∈ B, ‖iteratedFDeriv ℝ j e t‖ ≤ K) →
    ContDiffOn ℝ 3 (fun t => ballExpectation (cutoffFactor ρ p) (A t) (cutoffSlope p (e t))) B ∧
      ∀ t ∈ B, ∀ u v w : Fin k → ℝ,
        iteratedFDeriv ℝ 1 (fun t => ballExpectation (cutoffFactor ρ p) (A t) (cutoffSlope p (e t))) t ![u] =
          ballExpectation (cutoffFactor ρ p) (A t) (cutoffSlope p (iteratedFDeriv ℝ 1 e t ![u])) -
            ballCovariance (cutoffFactor ρ p) (A t) (cutoffSlope p (e t)) (paramIteratedDeriv A ![u] t) ∧
        iteratedFDeriv ℝ 2 (fun t => ballExpectation (cutoffFactor ρ p) (A t) (cutoffSlope p (e t))) t ![v, u] =
          ballExpectation (cutoffFactor ρ p) (A t) (cutoffSlope p (iteratedFDeriv ℝ 2 e t ![v, u])) -
            ballCovariance (cutoffFactor ρ p) (A t) (cutoffSlope p (iteratedFDeriv ℝ 1 e t ![u]))
              (paramIteratedDeriv A ![v] t) -
            ballCovariance (cutoffFactor ρ p) (A t) (cutoffSlope p (iteratedFDeriv ℝ 1 e t ![v]))
              (paramIteratedDeriv A ![u] t) -
            ballCovariance (cutoffFactor ρ p) (A t) (cutoffSlope p (e t)) (paramIteratedDeriv A ![v, u] t) +
            ballThirdCumulant (cutoffFactor ρ p) (A t) (cutoffSlope p (e t)) (paramIteratedDeriv A ![u] t)
              (paramIteratedDeriv A ![v] t) ∧
        iteratedFDeriv ℝ 3 (fun t => ballExpectation (cutoffFactor ρ p) (A t) (cutoffSlope p (e t))) t ![w, v, u] =
          ballExpectation (cutoffFactor ρ p) (A t) (cutoffSlope p (iteratedFDeriv ℝ 3 e t ![w, v, u])) -
            ballCovariance (cutoffFactor ρ p) (A t) (cutoffSlope p (iteratedFDeriv ℝ 2 e t ![v, u]))
              (paramIteratedDeriv A ![w] t) -
            ballCovariance (cutoffFactor ρ p) (A t) (cutoffSlope p (iteratedFDeriv ℝ 2 e t ![w, u]))
              (paramIteratedDeriv A ![v] t) -
            ballCovariance (cutoffFactor ρ p) (A t) (cutoffSlope p (iteratedFDeriv ℝ 2 e t ![w, v]))
              (paramIteratedDeriv A ![u] t) -
            ballCovariance (cutoffFactor ρ p) (A t) (cutoffSlope p (iteratedFDeriv ℝ 1 e t ![u]))
              (paramIteratedDeriv A ![w, v] t) -
            ballCovariance (cutoffFactor ρ p) (A t) (cutoffSlope p (iteratedFDeriv ℝ 1 e t ![v]))
              (paramIteratedDeriv A ![w, u] t) -
            ballCovariance (cutoffFactor ρ p) (A t) (cutoffSlope p (iteratedFDeriv ℝ 1 e t ![w]))
              (paramIteratedDeriv A ![v, u] t) +
            ballThirdCumulant (cutoffFactor ρ p) (A t) (cutoffSlope p (iteratedFDeriv ℝ 1 e t ![u]))
              (paramIteratedDeriv A ![v] t) (paramIteratedDeriv A ![w] t) +
            ballThirdCumulant (cutoffFactor ρ p) (A t) (cutoffSlope p (iteratedFDeriv ℝ 1 e t ![v]))
              (paramIteratedDeriv A ![u] t) (paramIteratedDeriv A ![w] t) +
            ballThirdCumulant (cutoffFactor ρ p) (A t) (cutoffSlope p (iteratedFDeriv ℝ 1 e t ![w]))
              (paramIteratedDeriv A ![u] t) (paramIteratedDeriv A ![v] t) -
            ballCovariance (cutoffFactor ρ p) (A t) (cutoffSlope p (e t)) (paramIteratedDeriv A ![w, v, u] t) +
            ballThirdCumulant (cutoffFactor ρ p) (A t) (cutoffSlope p (e t)) (paramIteratedDeriv A ![v, u] t)
              (paramIteratedDeriv A ![w] t) +
            ballThirdCumulant (cutoffFactor ρ p) (A t) (cutoffSlope p (e t)) (paramIteratedDeriv A ![w, u] t)
              (paramIteratedDeriv A ![v] t) +
            ballThirdCumulant (cutoffFactor ρ p) (A t) (cutoffSlope p (e t)) (paramIteratedDeriv A ![w, v] t)
              (paramIteratedDeriv A ![u] t) -
            ballFourthCumulant (cutoffFactor ρ p) (A t) (cutoffSlope p (e t)) (paramIteratedDeriv A ![u] t)
              (paramIteratedDeriv A ![v] t) (paramIteratedDeriv A ![w] t)
end YangMills.Construction.Cumulants
end
