import YangMills.Construction.SourcesAndGluing.PredicatesOfSimilaritiesOfLattices
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SourcesAndGluing
def RescalingLipschitzClaim : Prop :=
  ∀ (D : GluingSetup) (Ψ : LatticeRescaling D),
    Ψ.MapsLipschitzOnTorus ∧ Ψ.MapsLipschitzOnSpace
end YangMills.Construction.SourcesAndGluing
end
