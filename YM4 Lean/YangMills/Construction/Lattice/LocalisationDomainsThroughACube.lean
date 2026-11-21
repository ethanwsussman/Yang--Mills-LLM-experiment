import YangMills.Construction.Lattice.LevelsPresentOnTheTorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set PolymerActivities.DomainCounting
namespace TorusBound
namespace Setup
variable (D : Setup)
def regionsContaining (d : DomainKind) (j : ℕ) (Q : Set D.Torus) : Set (Set D.Torus) :=
  {X | X ∈ D.regionsBy d j ∧ Q ⊆ X}
def treeCountBound (E : ℕ) : ℕ := 16 * 8 ^ (2 * E) * 2 ^ (16 * (E + 1))
end Setup
namespace RegionsThroughCube
def CountAndTailBound : Prop :=
  ∀ (T : Setup) (d : DomainKind) (j : ℕ), j ≤ T.K → T.LevelFits j →
    ∀ Q ∈ T.cubesAt j,
      (∀ E : ℕ,
        {X | X ∈ T.regionsContaining d j Q ∧ T.extent j X = (E : ℝ)}.encard ≤
            (Setup.treeCountBound E : ℕ∞) ∧
          (Setup.treeCountBound E : ℝ) = 2 ^ 20 * Real.exp (countingRate * (E : ℝ))) ∧
      ∀ κ' D : ℝ, countingRate < κ' → 0 ≤ D →
        ∑ᶠ X ∈ {X | X ∈ T.regionsContaining d j Q ∧ D ≤ T.extent j X},
            Real.exp (-κ' * T.extent j X) ≤
          rateSum κ' * Real.exp (-(κ' - countingRate) * D)
end RegionsThroughCube
end TorusBound
end YangMills.Construction
end
