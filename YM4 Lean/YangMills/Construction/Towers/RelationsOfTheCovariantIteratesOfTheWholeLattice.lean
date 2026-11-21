import YangMills.Construction.Towers.CovariantLinearAverages
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace
def CovariantIterRelations : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k j : ℕ, j ≤ k →
    ∀ U ∈ smallIterateFields L k,
      (∀ B ∈ complexEdgeForms (meshAt L k 0),
        iterCovariantDeriv L k U j B =
          complexIterDeriv L k j U B +
            covDiff (complexIter L k j U) (iterContourLogDrift L k U j B)) ∧
      (∀ f : Vertex L k 0 → Matrices.ComplexMatrix2,
        (∀ x, f x ∈ Matrices.ComplexMatrix2.traceless) →
        iterAdjointCubeAverage L k U j f =
          restrictVertexFunction (meshAt L k j) f +
            iterContourLogDrift L k U j (covDiff U f) ∧
        iterCovariantDeriv L k U j (covDiff U f) =
          covDiff (complexIter L k j U) (iterAdjointCubeAverage L k U j f)) ∧
      ∃ T : (pairedFunctions (Vertex L k 0)).complexSubmodule →ₗ[ℂ]
          (pairedFunctions (Vertex L k j)).complexSubmodule,
        (∀ f : (pairedFunctions (Vertex L k 0)).complexSubmodule,
          (T f : (pairedFunctions (Vertex L k j)).index → Matrices.ComplexMatrix2) =
            iterAdjointCubeAverage L k U j
              (f : (pairedFunctions (Vertex L k 0)).index → Matrices.ComplexMatrix2)) ∧
        PairedFunctionSpace.PreservesFiniteSupport T ∧
        ∀ g : (pairedFunctions (Vertex L k j)).complexSubmodule,
          (T (PairedFunctionSpace.transposeMap T g) :
              (pairedFunctions (Vertex L k j)).index → Matrices.ComplexMatrix2) =
            (PeriodicLattice.inverseFourthPowerWeight L ^ j : ℂ) •
              (g : (pairedFunctions (Vertex L k j)).index → Matrices.ComplexMatrix2)
end YangMills.Construction.Tower.FullSpace
end
