import YangMills.Construction.ClusterExpansionOfAStep.AMoveReadAtZero
import YangMills.Construction.ClusterExpansionOfAStep.MarkAlongAMove
import YangMills.Construction.ClusterExpansionOfAStep.MarksOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusFields TorusLumps StepCosts StepMarks BondMoves
namespace MovedTopMarks
variable {n : ℕ}
def frameAlongMove (ℓ : StepParameters) (ρA : ℝ) (t m : ℕ) (V : TorusField n) {k : ℕ}
    (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (b : TorusBond (n * ℓ.side)) (u : Fin k → ℝ) : ℍ[ℝ] :=
  ((frameCoord ℓ ρA t m (perturb c X u V) b : imaginaryQuaternions) : ℍ[ℝ])
def GoodMarkAlongMove : Prop :=
  ∀ (ℓ : StepParameters) (ρA : ℝ) (p : ℝ → ℝ) (t m n : ℕ) [NeZero n] (V : TorusField n)
    (W : TorusField (n * ℓ.side)) (k : ℕ)
    (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (b : TorusBond (n * ℓ.side)),
    (∃ a₀ : ℍ[ℝ], ∀ u, goodMark ℓ ρA p t m (perturb c X u V) W b =
      cutoffFactor (ℓ.threshold / 64) p ‖a₀ - frameAlongMove ℓ ρA t m V c X b u‖) ∨
    ((∃ l, c l = (parentBlock ℓ.side b.1, b.2)) ∧ ∃ g : UnitQuaternion, ∀ u,
      goodMark ℓ ρA p t m (perturb c X u V) W b =
      markAlongLog (fun v => cutoffFactor (ℓ.threshold / 64) p ‖v‖)
        (bondMoveLinear c X (parentBlock ℓ.side b.1, b.2)) g
        (frameAlongMove ℓ ρA t m V c X b) u)
end MovedTopMarks
end YangMills.Construction
end
