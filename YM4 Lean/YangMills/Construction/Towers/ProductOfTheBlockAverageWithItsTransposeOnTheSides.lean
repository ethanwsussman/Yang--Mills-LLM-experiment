import YangMills.Construction.Towers.CovariantLinearAverages
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
def AdjointCubeAverageMulTranspose : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ n k j : ℕ, 0 < n → j < k →
    ∀ V ∈ smallComplexFields L n k j,
      ∃ T : (pairedFunctions (Vertex L n k j)).complexSubmodule →ₗ[ℂ]
          (pairedFunctions (Vertex L n k (j + 1))).complexSubmodule,
        (∀ f : (pairedFunctions (Vertex L n k j)).complexSubmodule,
          (T f : (pairedFunctions (Vertex L n k (j + 1))).index → Matrices.ComplexMatrix2) =
            adjointCubeAverage V
              (f : (pairedFunctions (Vertex L n k j)).index → Matrices.ComplexMatrix2)) ∧
        PairedFunctionSpace.PreservesFiniteSupport T ∧
        ∀ g : (pairedFunctions (Vertex L n k (j + 1))).complexSubmodule,
          (T (PairedFunctionSpace.transposeMap T g) :
              (pairedFunctions (Vertex L n k (j + 1))).index → Matrices.ComplexMatrix2) =
            PeriodicLattice.inverseFourthPowerWeight L •
              (g : (pairedFunctions (Vertex L n k (j + 1))).index → Matrices.ComplexMatrix2)
end Tower
end YangMills.Construction
end
