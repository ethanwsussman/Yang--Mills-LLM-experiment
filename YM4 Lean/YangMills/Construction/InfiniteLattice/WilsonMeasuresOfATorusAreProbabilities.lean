import YangMills.Construction.InfiniteLattice.PropertiesOfToriArraysAndPerturbedMeasures
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def QuotientGibbsMeasuresProbability.Statement : Prop :=
  ∀ β : ℝ, 0 < β → ∀ (a : ℝ), 0 < a → ∀ Γ : PeriodSublattice a, Γ.GibbsMeasuresAreProbability β
end YangMills.Construction.InfiniteLattice
