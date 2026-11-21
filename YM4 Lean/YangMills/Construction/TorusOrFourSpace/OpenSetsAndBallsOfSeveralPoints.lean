import YangMills.Construction.TorusOrFourSpace.FunctionsOfSeveralPoints
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.TupleTopology
open PeriodicSpace.Kind
def QuotientOpenAndBalls : Prop :=
  ∀ (P : Params) (Y : Kind) (p : ℕ+),
    MetricNotions.IsContinuousWrt (fun a b : Coords p => Real.sqrt (∑ j, (a - b) j ^ 2))
      (Tuple.tupleDist P Y) (Tuple.proj P Y : Coords p → Y.Tuple P p) ∧
    (∀ U : Set (Coords p), IsOpen U →
      Tuple.IsOpenT P Y ((Tuple.proj P Y : Coords p → Y.Tuple P p) '' U)) ∧
    (∀ W : Set (Y.Tuple P p),
      Tuple.IsOpenT P Y W ↔ IsOpen ((Tuple.proj P Y : Coords p → Y.Tuple P p) ⁻¹' W)) ∧
    (∀ F : Y.Tuple P p → ℂ,
      Tuple.IsContinuousT P Y F ↔
        Continuous (F ∘ (Tuple.proj P Y : Coords p → Y.Tuple P p))) ∧
    ∀ (s : Y.Tuple P p) (r : ℝ), 0 < r →
      Tuple.IsOpenT P Y {t | Tuple.tupleDist P Y t s < r} ∧
        (∀ a ∈ {t | Tuple.tupleDist P Y t s < r},
          ∀ b ∈ {t | Tuple.tupleDist P Y t s < r},
            Tuple.tupleDist P Y a b < 2 * r) ∧
        Tuple.IsCompactT P Y {t | Tuple.tupleDist P Y t s ≤ r}
end YangMills.Construction.PeriodicSpace.TupleTopology
