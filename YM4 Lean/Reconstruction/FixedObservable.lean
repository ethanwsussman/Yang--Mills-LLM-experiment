import Formulation.FixedObservableContinuum
import Reconstruction.WightmanAssembly

namespace YangMills
open Construction

/-- Every component in the fixed-observable SU(2) continuum construction admits
a Schwinger representative with the OS axioms and scalar Wightman reconstruction. -/
theorem su2_fixed_observable_wightman_reconstruction :
    FixedObservableLimit (FixedObservableContinuumWith (fun D T =>
      SystemsWithFiveBounds.OSAxioms D T ∧ SystemsWithFiveBounds.IsWightmanSchwingerSequence T)) := by
  apply fixed_observable_continuum_of_components
  intro M θ d η D σ hc
  obtain ⟨T, hT, _⟩ := hc.growth
  exact ⟨T, hT, hc.componentOS T hT, TheStatementsProvedTogether.wightman_of_fieldData hc.fieldData hT⟩

end YangMills
