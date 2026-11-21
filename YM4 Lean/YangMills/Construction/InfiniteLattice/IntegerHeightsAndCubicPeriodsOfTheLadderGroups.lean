import YangMills.Construction.InfiniteLattice.PeriodGroupsOfOneFamily
import Mathlib
set_option autoImplicit false
open scoped Matrix
noncomputable section
namespace YangMills.Construction.NormalFamilies
open InfiniteLattice
def IntegerLevelsAndCubicPeriods.Statement : Prop :=
  ∀ n ∈ normalSet, ∀ h : ℤ, Even h → 2 ≤ h →
    n ⬝ᵥ firstNonzeroBasisVec n = 1 ∧
    (∀ x ∈ latticeSubgroup 1, ∃ k : ℤ, n ⬝ᵥ x = (k : ℝ)) ∧
    latticeSubgroup (2 * (h : ℝ)) ≤ normalPeriodLattice n h
end YangMills.Construction.NormalFamilies
end
