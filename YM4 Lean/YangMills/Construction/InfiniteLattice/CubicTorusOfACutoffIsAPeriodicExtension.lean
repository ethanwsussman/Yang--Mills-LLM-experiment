import YangMills.Construction.InfiniteLattice.PropertiesOfToriArraysAndPerturbedMeasures
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def CubicTorusAtCutoffLifts.Statement : Prop :=
  ∀ β : ℝ, 0 < β → ∀ d : Conventions.StandingParameters, CubicTorusLiftsPeriodically d β
end YangMills.Construction.InfiniteLattice
