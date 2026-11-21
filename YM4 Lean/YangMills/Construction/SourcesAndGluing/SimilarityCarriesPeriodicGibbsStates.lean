import YangMills.Construction.SourcesAndGluing.PredicatesOfSimilaritiesOfLattices
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SourcesAndGluing
def RescalingGibbsClaim : Prop :=
  ∀ (D : GluingSetup) (Ψ : LatticeRescaling D), Ψ.MapsPeriodicGibbs
end YangMills.Construction.SourcesAndGluing
end
