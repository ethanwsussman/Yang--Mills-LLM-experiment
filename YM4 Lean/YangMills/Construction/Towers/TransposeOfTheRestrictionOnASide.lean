import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.TheLeftChart
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open PeriodicLattice (FourTorus)
namespace Tower.RestrictionTranspose
structure TransposeFacts {L m k i l : ℕ}
    (T : (pairedFunctions (Vertex L m k i)).complexSubmodule →ₗ[ℂ]
      (pairedFunctions (Vertex L m k l)).complexSubmodule) : Prop where
  preservesFiniteSupport : PairedFunctionSpace.PreservesFiniteSupport T
  isTranspose : PairedFunctionSpace.IsTransposeMap T (PairedFunctionSpace.transposeMap T)
  transpose_apply_of_coarse : ∀ (g : (pairedFunctions (Vertex L m k l)).complexSubmodule)
    (x : Vertex L m k i) (y : Vertex L m k l), (y : FourTorus L m) = x →
      (PairedFunctionSpace.transposeMap T g).1 x = g.1 y
  transpose_apply_of_not_coarse : ∀ (g : (pairedFunctions (Vertex L m k l)).complexSubmodule)
    (x : Vertex L m k i), (¬ ∃ y : Vertex L m k l, (y : FourTorus L m) = x) →
      (PairedFunctionSpace.transposeMap T g).1 x = 0
  restrict_transpose : ∀ g : (pairedFunctions (Vertex L m k l)).complexSubmodule,
    restrictVertexFunction l (PairedFunctionSpace.transposeMap T g).1 = g.1
def Statement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ m k i l : ℕ, 0 < m → i ≤ l → l ≤ k →
    ∀ T : (pairedFunctions (Vertex L m k i)).complexSubmodule →ₗ[ℂ]
        (pairedFunctions (Vertex L m k l)).complexSubmodule,
      (∀ f, (T f).1 = restrictVertexFunction l f.1) → TransposeFacts T
end Tower.RestrictionTranspose
end YangMills.Construction
end
