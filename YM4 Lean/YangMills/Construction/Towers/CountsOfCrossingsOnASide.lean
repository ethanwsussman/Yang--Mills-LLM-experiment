import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.FormsOnTowers
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
open PeriodicLattice (FourTorus refinedBlock crossingPath)
def crossingSites (L m k i j : ℕ) (c : Edge L m k j) (b : Edge L m k i) : Set (Vertex L m k i) :=
  {x | (x : FourTorus L m) ∈ refinedBlock (j - i) c.source ∧ b ∈ crossingPath c x}
def CrossingCountsOnTorus : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ m k i j : ℕ, 0 < m → 1 ≤ k → i ≤ j → j ≤ k →
    (∀ c : PositiveEdge L m k j,
      ∑ᶠ b : PositiveEdge L m k i, ((crossingSites L m k i j c.1 b.1).ncard : ℝ) =
        (L : ℝ) ^ (5 * (j - i))) ∧
    (∀ b : PositiveEdge L m k i,
      ∑ᶠ c : PositiveEdge L m k j, ((crossingSites L m k i j c.1 b.1).ncard : ℝ) =
        (L : ℝ) ^ (j - i)) ∧
    ∀ (c : PositiveEdge L m k j) (x : Vertex L m k i),
      (x : FourTorus L m) ∈ refinedBlock (j - i) c.1.source →
        (crossingPath c.1 x).Nodup ∧ ∀ b ∈ crossingPath c.1 x, b.IsPositivelyOriented
end YangMills.Construction.Tower
end
