import YangMills.Construction.SourcesAndGluing.PredicatesOfSimilaritiesOfLattices
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SourcesAndGluing
def RescalingKeepsGridScalesAndCubes.Statement : Prop :=
  ∀ (D : GluingSetup) (Ψ : LatticeRescaling D),
    Ψ.MapsGridScales ∧ ∀ (g : CubicGrid D) (hg : g.IsMirrorGrid), Ψ.MapsCubes g hg
end YangMills.Construction.SourcesAndGluing
end
