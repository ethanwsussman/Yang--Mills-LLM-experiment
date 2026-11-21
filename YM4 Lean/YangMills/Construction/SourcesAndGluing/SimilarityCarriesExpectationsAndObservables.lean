import YangMills.Construction.SourcesAndGluing.PredicatesOfSimilaritiesOfLattices
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SourcesAndGluing
def RescalingKeepsExpectationsAndObservables.Statement : Prop :=
  ∀ (D : GluingSetup) (Ψ : LatticeRescaling D),
    Ψ.PreservesExpectation ∧ Ψ.MapsPeriodicObservables ∧ Ψ.MapsSmearedEnergies
end YangMills.Construction.SourcesAndGluing
end
