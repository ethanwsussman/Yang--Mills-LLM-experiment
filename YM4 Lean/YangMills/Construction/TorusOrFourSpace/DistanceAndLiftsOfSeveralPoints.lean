import YangMills.Construction.TorusOrFourSpace.FunctionsOfSeveralPoints
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.TupleMetric
open PeriodicSpace.Kind
def QuotientDistanceAndLifts : Prop :=
  ∀ (P : Params) (Y : Kind) (p : ℕ+),
    (Function.Surjective (Tuple.proj P Y : Coords p → Y.Tuple P p) ∧
      ∀ a b : Coords p,
        Tuple.proj P Y a = Tuple.proj P Y b ↔
          a - b ∈ Tuple.periodSet P Y p) ∧
    (∀ a b : Coords p,
      IsLeast {r | ∃ k ∈ Tuple.periodSet P Y p, r = Real.sqrt (∑ j, (a - b - k) j ^ 2)}
          (Tuple.tupleDist P Y (Tuple.proj P Y a) (Tuple.proj P Y b)) ∧
        Tuple.tupleDist P Y (Tuple.proj P Y a) (Tuple.proj P Y b) ≤
          Real.sqrt (∑ j, (a - b) j ^ 2)) ∧
    ((∀ s t : Y.Tuple P p, 0 ≤ Tuple.tupleDist P Y s t) ∧
      (∀ s t : Y.Tuple P p, Tuple.tupleDist P Y s t = 0 ↔ s = t) ∧
      (∀ s t : Y.Tuple P p, Tuple.tupleDist P Y s t = Tuple.tupleDist P Y t s) ∧
      ∀ s t u : Y.Tuple P p,
        Tuple.tupleDist P Y s u ≤ Tuple.tupleDist P Y s t + Tuple.tupleDist P Y t u) ∧
    (∀ (a : Coords p) (t : Y.Tuple P p), ∃ b, Tuple.IsLiftOf P Y t b ∧
      Real.sqrt (∑ j, (a - b) j ^ 2) = Tuple.tupleDist P Y (Tuple.proj P Y a) t) ∧
    ∀ s t : Y.Tuple P p, ∃! r : ℝ, ∀ a b : Coords p,
      Tuple.IsLiftOf P Y s a → Tuple.IsLiftOf P Y t b →
        IsLeast {r | ∃ k ∈ Tuple.periodSet P Y p, r = Real.sqrt (∑ j, (a - b - k) j ^ 2)} r
end YangMills.Construction.PeriodicSpace.TupleMetric
