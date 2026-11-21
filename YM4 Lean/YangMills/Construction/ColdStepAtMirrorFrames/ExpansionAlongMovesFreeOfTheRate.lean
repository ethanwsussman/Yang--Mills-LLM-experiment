import YangMills.Construction.SummableBoundsOfTheFlow.BoundAlongMovesAboveTheFrames
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.Estimates YangMills.Construction.Interpolation
namespace YangMills.Construction.ColdStepAtMirrorFrames
def ExpansionAlongPerturbationsAt (K : ℕ → ℝ) (r : ℝ) (L : ℕ) (C : ℝ) : Prop :=
  ∀ κ : ℝ, 0 < κ → 2 ^ 9 * κ ≤ r →
    ∀ (F : BlockFrame) (n₀ k p m : ℕ) (σ s a ρA : ℝ) (e : ℕ → ℝ) (f : LocalFamily)
      (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)) (w : Fin p → Perturbation F)
      (y : F.Site F.depth),
      F.blockSide = L → IsLargeCubicTorus F → IsCubicTorusAbove L F.depth n₀ F → k ≤ 6 → (∀ j, 0 ≤ e j) →
      HasBoundedDerivatives L F.depth n₀ σ (κ / 2 ^ 10) k e f →
      IsSmallCurvature σ (interpolatedField s a ρA m V η) →
      (∀ x i, ¬ IsAxialTreeBond (x, i) → ‖interpolatedCoords s a ρA m V η x i‖ ≤ 1) →
      (∀ d ∈ chordBonds (finiteCells F), IsBondAnalyticAt (interpolatedFrame s a ρA m d) V) →
      (∀ d ∈ chordBonds (finiteCells F), ∀ (k' : ℕ) (c' : Fin k' → F.Site F.top × Fin 4)
        (X' : Fin k' → imaginaryQuaternions),
        1 ≤ k' → AreUnitVectors X' →
        ‖bondDeriv (interpolatedFrame s a ρA m d) V c' X'‖ ≤
          K k' * Real.exp (-(r * bondListDistance (enclosingCell d.1) c'))) →
      (∀ l, (w l).IsUnit) →
      ContDiffAt ℝ k (fun τ => subtractTrivial f F y (perturbedField s a ρA m V η w τ)) 0 ∧
      (1 ≤ p → p ≤ k →
        |iteratedFDeriv ℝ p (fun τ => subtractTrivial f F y (perturbedField s a ρA m V η w τ)) 0
          fun l => Pi.single l 1| ≤
          C * runningMax e p *
            Real.exp (-(2 ^ 7 * κ * cellSetDiameter (insert (enclosingCell y) (perturbationCells w)))))
def ExpansionAlongPerturbationsUniformInRate : Prop :=
  ∀ (K : ℕ → ℝ) (r : ℝ) (L : ℕ), (∀ k, 0 ≤ K k) → 0 < r → Odd L → 2 ^ 40 ≤ L →
    ∃ C : ℝ, 0 < C ∧ ExpansionAlongPerturbationsAt K r L C
end YangMills.Construction.ColdStepAtMirrorFrames
end
