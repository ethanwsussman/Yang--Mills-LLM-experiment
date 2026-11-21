import YangMills.Construction.Continuum.SymbolsTheMapIntoFiniteSequencesAndTheActionsOnSequences
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.OSSpaces
section TensorForm
variable {s : Conventions.StandingParameters} (P : PeriodicSpace.Params)
  (S : AmbientPoints.ConnectedFamily s .euclidean)
def vacuumSequence : ReflectionSpaces.finiteUpperSequences P :=
  ⟨Pi.single 0 (1 : ℂ), fun n => by
      by_cases hn : n = 0
      · subst hn
        exact Submodule.mem_top
      · rw [Pi.single_eq_of_ne hn]
        exact Submodule.zero_mem _,
    1, fun n hn => Pi.single_eq_of_ne (by omega) _⟩
end TensorForm
section SequenceMap
variable (P : PeriodicSpace.Params) (T : TorusTransport.TransportData)
abbrev symbolToSequence :
    TimeAxisSymbols.PosSymbolSpan T →ₗ[ℂ] ReflectionSpaces.finiteUpperSequences P :=
  SymbolSequences.spanSequence P
theorem symbolToSequence_posUnitSymbol :
    symbolToSequence P T (TorusTransport.TupleVectors.basisVec TimeAxisSymbols.posUnitSymbol) =
      vacuumSequence P := by
  rw [SymbolSequences.spanSequence_basisVec]
  rfl
end SequenceMap
end YangMills.Construction.OSSpaces
end
