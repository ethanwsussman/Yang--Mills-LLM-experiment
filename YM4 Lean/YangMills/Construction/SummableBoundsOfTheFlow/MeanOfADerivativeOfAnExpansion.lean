import YangMills.Construction.ColdStepAtMirrorFrames.MeansOfACutMeasure
import YangMills.Construction.SummableBoundsOfTheFlow.CumulantsOfTheMeanAtATop
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAboveTheFrames
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Estimates Interpolation
namespace Cumulants
open Classical in
def meanFieldDerivNearValueStatement : Prop :=
  ∀ (F : BlockFrame) (star : Bool) (a ρA : ℝ) (m : ℕ) (ρ κ Cg ε₃ W₀ N₀ M₂ t : ℝ) (p : ℝ → ℝ)
    (Φ : StepVariable (finiteCells F) → ℝ) (h : LocalFamily) (V : F.GaugeField F.top) (Y : F.Cell),
    0 < ρ → 0 < κ → 0 ≤ Cg → 0 ≤ ε₃ → 0 < t → 0 ≤ W₀ → 0 ≤ N₀ → 0 ≤ M₂ →
    (∀ y, JointlyContDiffOnBalls ρ V (centredExpansion star a ρA m h y)) →
    IsPositiveUnitalForm ρ p Φ →
    (∀ (y : F.Site F.depth) (ζ : StepVariable (finiteCells F)) (b : ↥(chordBonds (finiteCells F)))
      (u : EuclideanSpace ℝ (Fin 3)) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
      (∀ b, ‖ζ b‖ ≤ ρ) → ‖u‖ = 1 → k ≤ 2 → AreUnitVectors X →
      |jointMixedDeriv (centredExpansion star a ρA m h y) ζ V ![b] ![u] c X| ≤ Cg * ε₃ *
        Real.exp (-(2 ^ 7 * κ *
          cellSetDiameter (insert (enclosingCell y) (chordBondCells ![b] ∪ topBondCells c))))) →
    (∀ b : ↥(chordBonds (finiteCells F)), ballExpectation (cutoffFactor ρ p) Φ (fun η => ‖η b‖ ^ 2) ≤ M₂) →
    (∑ b : ↥(chordBonds (finiteCells F)),
      Real.exp (-(2 ^ 6 * κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) ≤ W₀) →
    (((sitesOfCells (finiteCells F) F.depth).filter fun y => enclosingCell y = Y).card : ℝ) ≤ N₀ →
    ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 2 → AreUnitVectors X →
      |ballExpectation (cutoffFactor ρ p) Φ (fieldDeriv (cellExpansionInField star a ρA m h Y) V c X) -
        fieldDeriv (cellExpansionInField star a ρA m h Y) V c X 0| ≤
        N₀ * (Cg * ε₃) * W₀ * (t / 2 + M₂ / (2 * t)) * Real.exp (-(κ / 2 ^ 6 * (bondSpan Y c : ℝ)))
end Cumulants
end YangMills.Construction
end
