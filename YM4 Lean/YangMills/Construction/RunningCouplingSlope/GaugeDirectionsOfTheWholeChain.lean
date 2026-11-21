import YangMills.Construction.RunningCouplingSlope.HessianOfTheWholeChain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower
def GaugeDirectionsAreFlat : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 1 ≤ k → 0 < n →
    (∀ τ : LevelTriple L n k, deriv (fun u : ℝ => tripleFreeEnergy a (u • τ)) 0 = 0) ∧
    ∀ (l : Tower.vertexFunctionSpace L n k 0) (A : Tower.edgeFormSpace L n k 0),
      (A : Tower.Edge L n k 0 → Matrices.ComplexMatrix2) =
        Tower.vertexCoboundary (l : Tower.Vertex L n k 0 → Matrices.ComplexMatrix2) →
      ∀ τ : LevelTriple L n k, RunningCouplingSlope.hessianOfFreeEnergy a (backgroundOnlyTriple A) τ = 0
end YangMills.Construction.RunningCouplingSlope
end
