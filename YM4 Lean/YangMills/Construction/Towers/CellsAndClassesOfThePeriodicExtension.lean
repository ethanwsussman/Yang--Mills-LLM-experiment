import YangMills.Construction.Towers.PropertiesOfPeriodicExtensionsAndPeriodisation
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.LocalKernels.PeriodicLiftCells
open YangMills.Construction.LocalKernels.Periodisation YangMills.Construction.Tower
def CellsAndClassesHold : Prop :=
  ∀ L : ℕ, YangMills.Construction.Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 0 < n →
    (∀ j ≤ k, ProjCellsClassified L n k j ∧ ProjEdgesCompatible L n k j) ∧
    ∀ I : WeightedIndexSet k, QuotientClassesPeriodic L n I
end YangMills.Construction.LocalKernels.PeriodicLiftCells
