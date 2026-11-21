import YangMills.Construction.InfiniteLattice.PropertiesOfToriArraysAndPerturbedMeasures
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def QuotientTorusFaithful.Statement : Prop :=
  ∀ (a : ℝ), 0 < a → ∀ Γ : PeriodSublattice a, Γ.IsFaithfulQuotient
end YangMills.Construction.InfiniteLattice
