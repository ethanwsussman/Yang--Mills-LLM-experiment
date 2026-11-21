import YangMills.Construction.SourcesAndGluing.PredicatesOfSimilaritiesOfLattices
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SourcesAndGluing
def RescalingMapsInfiniteLatticeClaim : Prop :=
  ∀ (D : GluingSetup) (Ψ : LatticeRescaling D), Ψ.MapsInfiniteLattice
end YangMills.Construction.SourcesAndGluing
end
