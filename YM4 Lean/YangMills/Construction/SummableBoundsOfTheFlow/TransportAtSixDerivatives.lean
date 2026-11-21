import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAboveTheFrames
import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAndTheirLaws
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace Interpolation
variable {F : BlockFrame}
structure IsTransportBounded (s a ρA κ δ C : ℝ) (Ck : ℕ → ℝ) (L m k : ℕ) (e : ℕ → ℝ) (f : LocalFamily)
    (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)) : Prop where
  smooth : ∀ (y : F.Site F.depth) (l j : ℕ) (b : Fin l → ↥(chordBonds (finiteCells F)))
    (u : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin j → F.Site F.top × Fin 4) (X : Fin j → imaginaryQuaternions),
    (∀ i, ‖u i‖ = 1) → AreUnitVectors X →
    ContDiffAt ℝ k (jointDisplacement (interpolatedExpansion s a ρA m f y) η V b u c X) 0
  decay : ∀ (y : F.Site F.depth) (j : ℕ) (c : Fin j → F.Site F.top × Fin 4) (X : Fin j → imaginaryQuaternions),
    1 ≤ j → j ≤ k → AreUnitVectors X →
    |bondDeriv (interpolatedExpansion s a ρA m f y η) V c X| ≤ C * runningMax e j *
      ((torusDecayFactor L δ ((L : ℝ) * bondSpan (enclosingCell y) c / 16))⁻¹ +
        Real.exp (-(2 ^ 6 * κ * bondSpan (enclosingCell y) c)))
  jointDeriv_le : ∀ (y : F.Site F.depth) (l j : ℕ) (b : Fin l → ↥(chordBonds (finiteCells F)))
    (u : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin j → F.Site F.top × Fin 4) (X : Fin j → imaginaryQuaternions),
    1 ≤ l + j → l + j ≤ k → (∀ i, ‖u i‖ = 1) → AreUnitVectors X →
    |jointMixedDeriv (interpolatedExpansion s a ρA m f y) η V b u c X| ≤ C * runningMax e (l + j) *
      Real.exp (-(2 ^ 7 * κ *
        cellSetDiameter (insert (enclosingCell y) (chordBondCells b ∪ topBondCells c))))
  blockDeriv_le : ∀ (Y : F.Cell) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
    AreUnitVectors X →
    |bondDeriv (interpolatedBlockExpansion s a ρA m f Y η) V c X| ≤
      (1 / 4 * e k + Ck k * runningMax e (k - 1)) / torusDecayFactor L δ (bondSpan Y c)
def rateParameters (T : StepParameters) : StepParameters :=
  { T with η₃ := 0, blockIndex := 0, σ := 0, p := 0, Cs := 0, E := 0, n₀ := 0, CE := 0, coupling := 0 }
def TransportBoundsAt (T : StepParameters) (C : ℝ) (Ck : ℕ → ℝ) : Prop :=
  ∀ (x : ℝ) (t k : ℕ) (e : ℕ → ℝ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top) (s : ℝ)
    (η : StepVariable (finiteCells F)), T.coupling ≤ x → 3 ≤ k → k ≤ 6 → (∀ j, 0 ≤ e j) →
    HasBoundedDerivatives T.L t T.n₀ T.σ T.decayRate k e f → IsCubicTopTorus T.L t T.n₀ F →
    IsSmallCurvature (5 / 4 * T.σ) V → 0 ≤ s → s ≤ 1 → (∀ b, ‖η b‖ ≤ T.ballRadius) →
    IsTransportBounded s T.a T.chainParams.ρA T.κ T.decayRate C Ck T.L (frameRadius x) k e f V η
def transportBoundsStatement : Prop :=
  ∃ (C : StepParameters → ℝ) (Ck : StepParameters → ℕ → ℝ), (∀ T, 0 < C T) ∧ (∀ T k, 0 < Ck T k) ∧
    EventuallyInParameters fun T => TransportBoundsAt T (C (rateParameters T)) (Ck (rateParameters T))
end Interpolation
end YangMills.Construction
end
