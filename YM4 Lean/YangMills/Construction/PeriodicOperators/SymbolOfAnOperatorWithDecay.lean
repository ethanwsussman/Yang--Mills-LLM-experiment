import YangMills.Construction.PeriodicOperators.EntriesAtTheClassesAndMapsIntoHom
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.ExpDecaySymbol
open TorusMetric (l1NormVec)
def HolomorphicOnStrip : Prop :=
  ∀ I I' : PeriodicData, IsPeriodic I → IsPeriodic I' →
    ∀ (υ : ℝ), 0 < υ → ∀ (C : ℝ) (T : I'.Carrier → I.Carrier → ℂ), IsPeriodicKernel I I' T →
      (∀ i' i, ‖T i' i‖ ≤ C * Real.exp (-υ * l1NormVec (I'.pos i' - I.pos i))) →
        SymbolSummableOn I I' T (openImStrip υ) ∧
          QuotHomFamilyHolomorphicOn (n := 4) (openImStrip υ) (symbolHom I I' T)
end YangMills.Construction.PeriodicOperators.ExpDecaySymbol
end
