import YangMills.Construction.PeriodicOperators.PeriodicIndexSetsOperatorsAndSymbols
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators
open YangMills.Construction.TorusMetric (l1NormVec)
def DecayFromStripSymbol : Prop :=
  ∀ I I' : PeriodicData, IsPeriodic I → IsPeriodic I' →
    ∀ (T : I'.Carrier → I.Carrier → ℂ) (υ : ℝ), 0 < υ → IsShiftInvariant I I' T →
      SymbolSummableOn I I' T (imStrip υ) →
      ∃ C : ℝ, 0 < C ∧ ∀ ι' ι,
        ‖T ι' ι‖ ≤ C * Real.exp (-υ * l1NormVec (I'.pos ι' - I.pos ι))
end YangMills.Construction.PeriodicOperators
end
