import YangMills.Construction.Measures.SupportOfProbabilityMeasure
import Mathlib
set_option autoImplicit false
open MeasureTheory
namespace YangMills.Construction.Measures
def SupportFullMeasureAndL2Rank : Prop :=
  ∀ (Y : Type) [TopologicalSpace Y] [TopologicalSpace.MetrizableSpace Y]
    [TopologicalSpace.SeparableSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (m : Measure Y) [IsProbabilityMeasure m],
    (IsClosed (probabilitySupport m) ∧ m (probabilitySupport m) = 1) ∧
    ((probabilitySupport m).Nonempty ∧
      (∀ E : Set Y, MeasurableSet E → 0 < m E → (E ∩ probabilitySupport m).Nonempty) ∧
      ∀ C : Set Y, IsClosed C → m C = 1 → probabilitySupport m ⊆ C) ∧
    (CompactSpace Y → probabilitySupport m = Set.univ →
      Cardinal.toENat (Module.rank ℂ (Lp ℂ 2 m)) = ENat.card Y)
end YangMills.Construction.Measures
