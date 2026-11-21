import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.FormsOnTowers
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open InfiniteLattice (AmbientSpace)
namespace Tower.FullSpace
def crossingSites (L k i j : ℕ) (c : Edge L k j) (b : Edge L k i) :
    Set (Vertex L k i) :=
  {x | (x : AmbientSpace) ∈ cubeOfOrder L (Tower.meshAt L k i) (j - i) c.initial ∧
    b ∈ crossingPath c x}
def CrossingCounts : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k i j : ℕ, 1 ≤ k → i ≤ j → j ≤ k →
    (∀ c : PositiveEdge (Tower.meshAt L k j),
      (Function.support fun b : PositiveEdge (Tower.meshAt L k i) =>
        ((crossingSites L k i j c.1 b.1).ncard : ℝ)).Finite ∧
      ∑ᶠ b : PositiveEdge (Tower.meshAt L k i), ((crossingSites L k i j c.1 b.1).ncard : ℝ) =
        (L : ℝ) ^ (5 * (j - i))) ∧
    (∀ b : PositiveEdge (Tower.meshAt L k i),
      (Function.support fun c : PositiveEdge (Tower.meshAt L k j) =>
        ((crossingSites L k i j c.1 b.1).ncard : ℝ)).Finite ∧
      ∑ᶠ c : PositiveEdge (Tower.meshAt L k j), ((crossingSites L k i j c.1 b.1).ncard : ℝ) =
        (L : ℝ) ^ (j - i)) ∧
    (∀ (c : PositiveEdge (Tower.meshAt L k j)) (x : Vertex L k i),
      (x : AmbientSpace) ∈ cubeOfOrder L (Tower.meshAt L k i) (j - i) c.1.initial →
        (crossingPath c.1 x).Nodup ∧ ∀ b ∈ crossingPath c.1 x, b.IsPositivelyOriented) ∧
    ∀ (c : PositiveEdge (Tower.meshAt L k j)) (b : PositiveEdge (Tower.meshAt L k i)),
      (crossingSites L k i j c.1 b.1).Nonempty →
        ∀ ρ, |(b.1.initial : AmbientSpace) ρ - (c.1.initial : AmbientSpace) ρ| ≤
          3 / 2 * Tower.meshAt L k j
end Tower.FullSpace
end YangMills.Construction
end
