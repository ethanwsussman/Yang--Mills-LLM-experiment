import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAboveTheFrames
import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAndTheirLaws
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.Interpolation
def HaarLogRatioDerivBounds : Prop :=
  ∀ (K : ℕ → ℝ) (r κ : ℝ), (∀ k, 0 ≤ K k) → 0 ≤ r → 0 ≤ κ → 2 ^ 9 * κ ≤ r →
    ∃ D : ℕ → ℕ → ℝ, (∀ l j, 0 < D l j) ∧
      ∀ (F : BlockFrame) (s a ρA : ℝ) (m : ℕ) (V : F.GaugeField F.top)
        (η : StepVariable (finiteCells F))
        (b₀ : ↥(chordBonds (finiteCells F))),
        ‖toImaginary (η b₀) + interpolatedFrame s a ρA m b₀.1 V‖ ≤ 1 →
        IsBondAnalyticAt (interpolatedFrame s a ρA m b₀.1) V →
        (∀ (k : ℕ) (c' : Fin k → F.Site F.top × Fin 4) (X' : Fin k → imaginaryQuaternions),
          1 ≤ k → AreUnitVectors X' →
          ‖bondDeriv (interpolatedFrame s a ρA m b₀.1) V c' X'‖ ≤
            K k * Real.exp (-(r * bondListDistance (enclosingCell b₀.1.1) c'))) →
        ∀ (l j : ℕ) (b : Fin l → ↥(chordBonds (finiteCells F)))
          (u : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin j → F.Site F.top × Fin 4)
          (X : Fin j → imaginaryQuaternions),
          1 ≤ l + j → (∀ i, ‖u i‖ = 1) → AreUnitVectors X →
          ContDiffAt ℝ (l + j : ℕ) (jointDisplacement (fun ζ V' =>
            haarLogRatio (interpolatedCoords s a ρA m V' ζ b₀.1.1 b₀.1.2)) η V b u c X) 0 ∧
          |jointMixedDeriv (fun ζ V' =>
            haarLogRatio (interpolatedCoords s a ρA m V' ζ b₀.1.1 b₀.1.2)) η V b u c X| ≤
            D l j * Real.exp (-(2 ^ 8 * κ *
              cellSetDiameter ({enclosingCell b₀.1.1} ∪ chordBondCells b ∪ topBondCells c)))
end YangMills.Construction.RunningCouplingSlope
end
