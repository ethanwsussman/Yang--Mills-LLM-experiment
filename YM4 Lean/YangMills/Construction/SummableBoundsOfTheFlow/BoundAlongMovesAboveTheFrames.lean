import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAboveTheFrames
import YangMills.Construction.SummableBoundsOfTheFlow.MotionAboveTheFrames
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Estimates
open BlockAverages ColdStepAtMirrorFrames Interpolation
variable {F : BlockFrame}
def Perturbation.cell : Perturbation F → F.Cell
  | .bulk b _ => enclosingCell b.1.1
  | .top c _ => c.1
def perturbationCells {p : ℕ} (w : Fin p → Perturbation F) : Finset F.Cell :=
  Finset.univ.image fun l => (w l).cell
def perturbedField {p : ℕ} (s a ρA : ℝ) (m : ℕ) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) (w : Fin p → Perturbation F) (τ : Fin p → ℝ) :
    F.GaugeField F.depth :=
  interpolatedField s a ρA m (perturbedTop V w τ) (perturbedVariable η w τ)
def boundAlongPerturbationsStatement : Prop :=
  ∀ (K : ℕ → ℝ) (r κ : ℝ) (L : ℕ), (∀ k, 0 ≤ K k) → 0 < κ → 2 ^ 9 * κ ≤ r → Odd L → 2 ^ 40 ≤ L →
    ∃ C : ℝ, 0 < C ∧ ∀ (F : BlockFrame) (n₀ k p m : ℕ) (σ s a ρA : ℝ) (e : ℕ → ℝ) (f : LocalFamily)
      (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)) (w : Fin p → Perturbation F)
      (y : F.Site F.depth),
      F.blockSide = L → IsLargeCubicTorus F → IsCubicTorusAbove L F.depth n₀ F → k ≤ 6 → (∀ j, 0 ≤ e j) →
      HasBoundedDerivatives L F.depth n₀ σ (κ / 2 ^ 10) k e f →
      IsSmallCurvature σ (interpolatedField s a ρA m V η) →
      (∀ x i, ¬ IsAxialTreeBond (x, i) → ‖interpolatedCoords s a ρA m V η x i‖ ≤ 1) →
      (∀ d ∈ chordBonds (finiteCells F), IsBondAnalyticAt (interpolatedFrame s a ρA m d) V) →
      (∀ d ∈ chordBonds (finiteCells F), ∀ (k' : ℕ) (c' : Fin k' → F.Site F.top × Fin 4)
        (X' : Fin k' → imaginaryQuaternions), 1 ≤ k' → AreUnitVectors X' →
        ‖bondDeriv (interpolatedFrame s a ρA m d) V c' X'‖ ≤
          K k' * Real.exp (-(r * bondListDistance (enclosingCell d.1) c'))) →
      (∀ l, (w l).IsUnit) →
      ContDiffAt ℝ k (fun τ => ColdStepAtMirrorFrames.subtractTrivial f F y
        (perturbedField s a ρA m V η w τ)) 0 ∧
      (1 ≤ p → p ≤ k →
        |iteratedFDeriv ℝ p (fun τ => ColdStepAtMirrorFrames.subtractTrivial f F y
            (perturbedField s a ρA m V η w τ)) 0 fun l => Pi.single l 1| ≤
          C * runningMax e p *
            Real.exp (-(2 ^ 7 * κ * cellSetDiameter
              (insert (enclosingCell y) (perturbationCells w)))))
end Estimates
end YangMills.Construction
end
