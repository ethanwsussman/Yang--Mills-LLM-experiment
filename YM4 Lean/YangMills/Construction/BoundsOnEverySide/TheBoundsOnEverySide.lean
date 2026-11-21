import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import YangMills.Construction.Lattice.ObservablesAndTestNorms
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.BoundsOnEverySide
open MeasureTheory TestFunctions
open InfiniteLattice (AmbientSpace)
structure SideFamily where
  L : ℕ
  admissible : Conventions.IsAdmissibleBlockingFactor L
  M : ℝ
  one_le_M : 1 ≤ M
  sideSet : Set ℝ
  exists_side_ge : ∀ l : ℝ, ∃ m : ℕ+,
    PeriodicLattice.torusSide L m ∈ sideSet ∧ l ≤ PeriodicLattice.torusSide L m
  IsFirstPassage : ℕ+ → ℝ → Prop
  pos_of_isFirstPassage : ∀ K β, IsFirstPassage K β → 0 < β
def torusMean (L : ℕ) (m K : ℕ+) (β : ℝ) (f : AmbientSpace → ℝ) : ℝ :=
  PeriodicLattice.gibbsExpectation L m K β
    (PeriodicLattice.smearedObservable (periodize (PeriodicLattice.torusSide L m) f))
end YangMills.Construction.BoundsOnEverySide
end
