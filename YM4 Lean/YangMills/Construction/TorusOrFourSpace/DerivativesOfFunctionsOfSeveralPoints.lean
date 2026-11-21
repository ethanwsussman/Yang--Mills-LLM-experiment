import YangMills.Construction.TorusOrFourSpace.FunctionsOfSeveralPoints
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.TupleDerivatives
open Kind
def Statement : Prop :=
  ∀ (P : Params) (Y : Kind) (p : ℕ+),
    (∀ (ν : ℕ) (F : Y.Tuple P p → ℂ), Tuple.IsClassC P Y ν F →
      ∀ α : CoordIndex p, α.degree ≤ ν →
        (∃! H : Y.Tuple P p → ℂ, H ∘ Tuple.proj P Y =
          Coords.iterPartial α (F ∘ Tuple.proj P Y)) ∧
        Tuple.partialDeriv P Y α F ∘ Tuple.proj P Y =
          Coords.iterPartial α (F ∘ Tuple.proj P Y) ∧
        Tuple.IsContinuousT P Y (Tuple.partialDeriv P Y α F) ∧
        Tuple.IsClassC P Y (ν - α.degree) (Tuple.partialDeriv P Y α F) ∧
        (∀ β : CoordIndex p, β.degree ≤ ν - α.degree →
          Tuple.partialDeriv P Y β (Tuple.partialDeriv P Y α F) =
            Tuple.partialDeriv P Y (α + β) F) ∧
        Tuple.supportT P Y (Tuple.partialDeriv P Y α F) ⊆
          Tuple.supportT P Y F) ∧
    ∀ (ν : ℕ) (F : Y.Tuple P p → ℂ), Tuple.IsClassC P Y ν F →
      Tuple.IsCompactT P Y (Tuple.supportT P Y F) →
        Tuple.cNorm P Y ν F < ⊤
end YangMills.Construction.PeriodicSpace.TupleDerivatives
