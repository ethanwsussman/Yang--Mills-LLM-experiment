import YangMills.Construction.InfiniteLattice.PropertiesOfToriArraysAndPerturbedMeasures
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def PeriodicLiftIsFaithful : Prop :=
  ∀ (a : ℝ), 0 < a → ∀ Γ : PeriodSublattice a, Γ.LiftIsFaithful
end YangMills.Construction.InfiniteLattice
