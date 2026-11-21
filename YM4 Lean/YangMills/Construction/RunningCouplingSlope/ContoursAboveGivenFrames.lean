import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAboveTheFrames
import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAndTheirLaws
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.Interpolation
open BlockAverages ColdStepAtMirrorFrames
def logContourDerivBounds : Prop :=
  ∀ (K : ℕ → ℝ) (r κ : ℝ) (L : ℕ), (∀ k, 0 ≤ K k) → 0 ≤ κ → 2 ^ 9 * κ ≤ r → Odd L →
    ∃ D : ℕ → ℕ → ℝ, (∀ l j, 0 < D l j) ∧
      ∀ (F : BlockFrame) (s a ρA ε : ℝ) (m : ℕ) (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)),
        F.blockSide = L → IsLargeCubicTorus F → 0 ≤ ε → ε * (10 * L) ≤ 1 →
        (∀ d ∈ chordBonds (finiteCells F), ‖interpolatedCoords s a ρA m V η d.1 d.2‖ ≤ ε) →
        (∀ d ∈ chordBonds (finiteCells F), IsBondAnalyticAt (interpolatedFrame s a ρA m d) V) →
        (∀ d ∈ chordBonds (finiteCells F), ∀ (k : ℕ) (c' : Fin k → F.Site F.top × Fin 4) (X' : Fin k → imaginaryQuaternions),
          1 ≤ k → AreUnitVectors X' →
          ‖bondDeriv (interpolatedFrame s a ρA m d) V c' X'‖ ≤
            K k * Real.exp (-(r * bondListDistance (enclosingCell d.1) c'))) →
        ∀ (c₀ : F.Site F.top × Fin 4) (l j : ℕ) (b : Fin l → ↥(chordBonds (finiteCells F)))
          (u : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin j → F.Site F.top × Fin 4) (X : Fin j → imaginaryQuaternions),
          1 ≤ l + j → (∀ i, ‖u i‖ = 1) → AreUnitVectors X →
          ContDiffAt ℝ (l + j : ℕ) (jointDisplacement (fun ζ V' => Real.log ‖contourAverage (interpolatedField s a ρA m V' ζ) c₀‖) η V b u c X) 0 ∧
          |jointMixedDeriv (fun ζ V' => Real.log ‖contourAverage (interpolatedField s a ρA m V' ζ) c₀‖) η V b u c X| ≤
            D l j * Real.exp (-(2 ^ 8 * κ * cellSetDiameter ({c₀.1} ∪ chordBondCells b ∪ topBondCells c)))
end YangMills.Construction.Interpolation
end
