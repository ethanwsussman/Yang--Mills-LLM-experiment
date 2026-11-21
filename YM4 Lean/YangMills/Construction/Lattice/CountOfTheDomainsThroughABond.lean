import YangMills.Construction.Lattice.NumbersOfConnectedSetsRegionsAndDomainsAtACube
import YangMills.Construction.PolymerActivities.DomainCountingRate
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.LevelUnitPartition
variable (S : LevelUnitPartition)
abbrev Bond : Type := BondAtLevel S.params.L S.params.m S.params.K S.level
def domainsMeetingBond (D : Set (Set S.Points)) (b : S.Bond) : Set (Set S.Points) :=
  {Y | Y ∈ D ∧ ((b.source : S.Points) ∈ Y ∨ (b.target : S.Points) ∈ Y)}
def DomainCountBoundAt (κ κ' : ℝ) (D : Set (Set S.Points)) (b : S.Bond) : Prop :=
  (S.domainsMeetingBond D b).Finite ∧
    ∑ᶠ Y ∈ S.domainsMeetingBond D b, Real.exp (-κ' * S.domainLinearSize Y) ≤
      2 * PolymerActivities.DomainCounting.rateSum κ' ∧
    2 * PolymerActivities.DomainCounting.rateSum κ' ≤
      2 * PolymerActivities.DomainCounting.rateSum κ
end YangMills.Construction.PeriodicLattice.LevelUnitPartition
end
