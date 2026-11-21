import YangMills.Construction.Towers.CovariantLinearAverages
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace
def CubeAverageMulTranspose.Statement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k j : ℕ, j < k →
    ∀ V ∈ FullSpace.smallComplexFields L k j,
      ∃ T : (pairedFunctions (FullSpace.Vertex L k j)).complexSubmodule →ₗ[ℂ]
          (pairedFunctions (FullSpace.Vertex L k (j + 1))).complexSubmodule,
        (∀ f : (pairedFunctions (FullSpace.Vertex L k j)).complexSubmodule,
          (T f).val = FullSpace.adjointCubeAverage V f.val) ∧
        PairedFunctionSpace.PreservesFiniteSupport T ∧
        ∀ g : (pairedFunctions (FullSpace.Vertex L k (j + 1))).complexSubmodule,
          (T (PairedFunctionSpace.transposeMap T g)).val =
            PeriodicLattice.inverseFourthPowerWeight L • g.val
end YangMills.Construction.Tower.FullSpace
end
