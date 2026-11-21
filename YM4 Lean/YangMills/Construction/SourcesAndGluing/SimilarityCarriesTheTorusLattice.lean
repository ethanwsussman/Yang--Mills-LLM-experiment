import YangMills.Construction.SourcesAndGluing.PredicatesOfSimilaritiesOfLattices
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SourcesAndGluing
def RescalingMapsPeriodicLatticeClaim : Prop :=
  ∀ (D : GluingSetup) (Ψ : LatticeRescaling D), Ψ.MapsPeriodicLattice
end YangMills.Construction.SourcesAndGluing
end
