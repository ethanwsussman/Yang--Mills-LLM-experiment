import Mathlib
namespace YangMills.Construction.Segment
def SegmentDeterminesEndpoints : Prop :=
  ∀ x x' y y' : Fin 4 → ℝ,
    {z : Fin 4 → ℝ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = x + t • (x' - x)} =
      {z : Fin 4 → ℝ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = y + t • (y' - y)} →
    (y = x ∧ y' = x') ∨ (y = x' ∧ y' = x)
end YangMills.Construction.Segment
