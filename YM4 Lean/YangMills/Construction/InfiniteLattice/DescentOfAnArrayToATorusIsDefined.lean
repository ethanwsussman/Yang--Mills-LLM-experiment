import YangMills.Construction.InfiniteLattice.PropertiesOfToriArraysAndPerturbedMeasures
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def PeriodicDescentDefined.Statement : Prop :=
  ∀ β : ℝ, 0 < β → ∀ (A : LocalObservableArray) (t : ℝ) (Γ : PeriodSublattice 1),
    A.FitsPeriods Γ → A.PeriodicDescentWellDefined Γ β t
end YangMills.Construction.InfiniteLattice
