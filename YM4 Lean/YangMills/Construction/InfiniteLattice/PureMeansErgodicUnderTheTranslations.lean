import YangMills.Construction.InfiniteLattice.ErgodicPhases
import YangMills.Construction.InfiniteLattice.OneLatticeItsConfigurationsAndMeasuresOnCompactSpaces
import YangMills.Construction.InfiniteLattice.PeriodicGibbsAndTorusLimitSets
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.InfiniteLattice
noncomputable section
namespace YangMills.Construction.LatticePhases
def ExtremalIffShiftErgodicStatement : Prop :=
  ∀ S : Setup,
    (∀ μ ∈ periodicGibbsSet S.L S.K S.β, IsExtremalPeriodicGibbs S.β μ ↔ IsShiftErgodic μ) ∧
    extremalPhases S.L S.K S.β = {μ | μ ∈ periodicGibbsSet S.L S.K S.β ∧ IsExtremalPeriodicGibbs S.β μ}
end YangMills.Construction.LatticePhases
