import YangMills.Construction.Towers.CovariantLinearAverages
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
namespace Tower
def CovariantIterRelations : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ n k j : ℕ, 0 < n → j ≤ k →
    ∀ U ∈ smallIterateFields L n k,
      (∀ B ∈ complexEdgeForms L n k 0,
        iterCovariantDeriv L n k U j B =
          complexIterDeriv L n k j U B +
            covDiff (PeriodicLattice.complexBlockFieldAtLevel j U)
              (iterContourLogDrift L n k U j B)) ∧
      (∀ f : Vertex L n k 0 → Matrices.ComplexMatrix2,
        (∀ x, f x ∈ Matrices.ComplexMatrix2.traceless) →
        iterAdjointCubeAverage L n k U j f =
          restrictVertexFunction j f + iterContourLogDrift L n k U j (covDiff U f) ∧
        iterCovariantDeriv L n k U j (covDiff U f) =
          covDiff (PeriodicLattice.complexBlockFieldAtLevel j U)
            (iterAdjointCubeAverage L n k U j f)) ∧
      ∃ T : (pairedFunctions (Vertex L n k 0)).complexSubmodule →ₗ[ℂ]
          (pairedFunctions (Vertex L n k j)).complexSubmodule,
        (∀ f : (pairedFunctions (Vertex L n k 0)).complexSubmodule,
          (T f : (pairedFunctions (Vertex L n k j)).index → Matrices.ComplexMatrix2) =
            iterAdjointCubeAverage L n k U j
              (f : (pairedFunctions (Vertex L n k 0)).index → Matrices.ComplexMatrix2)) ∧
        PairedFunctionSpace.PreservesFiniteSupport T ∧
        ∀ g : (pairedFunctions (Vertex L n k j)).complexSubmodule,
          (T (PairedFunctionSpace.transposeMap T g) :
              (pairedFunctions (Vertex L n k j)).index → Matrices.ComplexMatrix2) =
            (PeriodicLattice.inverseFourthPowerWeight L ^ j : ℂ) •
              (g : (pairedFunctions (Vertex L n k j)).index → Matrices.ComplexMatrix2)
end Tower
end YangMills.Construction
end
