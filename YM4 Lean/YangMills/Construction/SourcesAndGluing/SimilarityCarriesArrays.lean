import YangMills.Construction.SourcesAndGluing.PredicatesOfSimilaritiesOfLattices
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SourcesAndGluing
def LatticeRescalingReflectionProductsClaim : Prop :=
  ∀ (D : GluingSetup) (Ψ : LatticeRescaling D) (g : CubicGrid D) (hg : g.IsMirrorGrid),
    Ψ.MapsReflectionProducts g hg
end YangMills.Construction.SourcesAndGluing
end
