import YangMills.Construction.SourcesAndGluing.PredicatesOfSimilaritiesOfLattices
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SourcesAndGluing
def LatticeRescalingCubeAlgebrasClaim : Prop :=
  ∀ (D : GluingSetup) (Ψ : LatticeRescaling D) (g : CubicGrid D) (hg : g.IsMirrorGrid),
    Ψ.MapsCubeAlgebras g hg
end YangMills.Construction.SourcesAndGluing
end
