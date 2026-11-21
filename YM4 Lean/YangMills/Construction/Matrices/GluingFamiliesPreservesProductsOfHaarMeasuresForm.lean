import YangMills.Construction.Matrices.FunctionsAndOperatorsOfSeveralVariablesOnG
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SpinHarmonics
open MeasureTheory Matrices.ComplexMatrix2
def GlueMeasurePreserving : Prop :=
  ∀ (J : Type) [Finite J] (B : Set J),
    MeasurePreserving (fun p : (↥B → specialUnitary) × (↥Bᶜ → specialUnitary) => glue B p.1 p.2)
      ((haarPi ↥B).prod (haarPi ↥Bᶜ)) (haarPi J)
end YangMills.Construction.SpinHarmonics
end
