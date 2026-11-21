import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAboveTheFrames
import YangMills.Construction.SummableBoundsOfTheFlow.ExpansionOfAMeanInTheTop
import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAndTheirLaws
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation
namespace Estimates
def expansionAboveFrameStatement : Prop :=
  ∀ (K : ℕ → ℝ) (r κ : ℝ) (L : ℕ), (∀ k, 0 ≤ K k) → 0 < κ → 2 ^ 9 * κ ≤ r → Odd L → 2 ^ 40 ≤ L →
    ∃ C : ℝ, 0 < C ∧ ∀ (F : BlockFrame) (n₀ m : ℕ) (σ s a ρA ρ : ℝ) (e : ℕ → ℝ) (f : LocalFamily)
      (V : F.GaugeField F.top) (y : F.Site F.depth),
      F.blockSide = L → IsLargeCubicTorus F → IsCubicTorusAbove L F.depth n₀ F → (∀ j, 0 ≤ e j) →
      HasBoundedDerivatives L F.depth n₀ σ (κ / 2 ^ 10) 3 e f →
      (∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ ρ) →
        IsSmallCurvature σ (interpolatedField s a ρA m V η)) →
      (∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ ρ) → ∀ x i, ¬ IsAxialTreeBond (x, i) →
        ‖interpolatedCoords s a ρA m V η x i‖ ≤ 1) →
      (∀ d ∈ chordBonds (finiteCells F), IsBondAnalyticAt (interpolatedFrame s a ρA m d) V) →
      (∀ d ∈ chordBonds (finiteCells F), ∀ (k' : ℕ) (c' : Fin k' → F.Site F.top × Fin 4)
        (X' : Fin k' → imaginaryQuaternions),
        1 ≤ k' → AreUnitVectors X' →
        ‖bondDeriv (interpolatedFrame s a ρA m d) V c' X'‖ ≤
          K k' * Real.exp (-(r * bondListDistance (enclosingCell d.1) c'))) →
      JointlyContDiffOnBalls ρ V (fun ζ V' => interpolatedExpansion s a ρA m f y ζ V') ∧
      ∀ (η : StepVariable (finiteCells F)) (l k : ℕ) (b : Fin l → ↥(chordBonds (finiteCells F)))
        (v : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin k → F.Site F.top × Fin 4)
        (X : Fin k → imaginaryQuaternions),
        (∀ b, ‖η b‖ ≤ ρ) → (∀ i, ‖v i‖ = 1) → AreUnitVectors X → 1 ≤ l + k → l + k ≤ 3 →
        |jointMixedDeriv (fun ζ V' => interpolatedExpansion s a ρA m f y ζ V') η V b v c X| ≤
          C * runningMax e (l + k) *
            Real.exp (-(2 ^ 7 * κ * cellSetDiameter
              (insert (enclosingCell y) (chordBondCells b ∪ topBondCells c))))
end Estimates
end YangMills.Construction
end
