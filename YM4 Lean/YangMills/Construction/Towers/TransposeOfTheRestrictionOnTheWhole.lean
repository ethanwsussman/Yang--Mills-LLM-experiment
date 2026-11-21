import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.TheLeftChart
import Mathlib
noncomputable section
namespace YangMills.Construction
open InfiniteLattice (AmbientSpace)
namespace Tower.FullSpace.RestrictionTranspose
structure TransposeProperties {L k i l : ℕ}
    (T : (pairedFunctions (Vertex L k i)).complexSubmodule →ₗ[ℂ]
      (pairedFunctions (Vertex L k l)).complexSubmodule) : Prop where
  preservesFiniteSupport : PairedFunctionSpace.PreservesFiniteSupport T
  isTransposeMap : PairedFunctionSpace.IsTransposeMap T (PairedFunctionSpace.transposeMap T)
  apply_of_coe_eq : ∀ (g : (pairedFunctions (Vertex L k l)).complexSubmodule) (x : Vertex L k i)
    (y : Vertex L k l), (y : AmbientSpace) = x → (PairedFunctionSpace.transposeMap T g).1 x = g.1 y
  apply_of_not_mem : ∀ (g : (pairedFunctions (Vertex L k l)).complexSubmodule) (x : Vertex L k i),
    (¬ ∃ y : Vertex L k l, (y : AmbientSpace) = x) → (PairedFunctionSpace.transposeMap T g).1 x = 0
  restrict_transposeMap : ∀ g : (pairedFunctions (Vertex L k l)).complexSubmodule,
    restrictVertexFunction (meshAt L k l) (PairedFunctionSpace.transposeMap T g).1 = g.1
def MainStatement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k i l : ℕ, i ≤ l → l ≤ k →
    ∀ T : (pairedFunctions (Vertex L k i)).complexSubmodule →ₗ[ℂ]
      (pairedFunctions (Vertex L k l)).complexSubmodule,
      (∀ f, (T f).1 = restrictVertexFunction (meshAt L k l) f.1) → TransposeProperties T
end Tower.FullSpace.RestrictionTranspose
end YangMills.Construction
end
