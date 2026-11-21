import YangMills.Construction.Towers.CovariantLinearAverages
import YangMills.Construction.Towers.TranslationsAndIsometriesOfATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace
open YangMills.Construction.PeriodicOperators (castVec)
open YangMills.Construction.Tower.FullSpace.Translations (spaceShift)
def ComplexSmoothingCommutesWithIntShift : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k j : ℕ, j < k → ∀ N : Fin 4 → ℤ,
    ∀ V ∈ smallComplexFields L k j,
      pushField (spaceShift (castVec N)) V ∈ smallComplexFields L k j ∧
      smoothingMap L k j V ∈ fieldsValuedIn L k (j + 1) PeriodicLattice.complexGaugeGroup ∧
      smoothingMap L k j (pushField (spaceShift (castVec N)) V) ∈
        fieldsValuedIn L k (j + 1) PeriodicLattice.complexGaugeGroup ∧
      smoothingMap L k j (pushField (spaceShift (castVec N)) V) =
        pushField (spaceShift (castVec N)) (smoothingMap L k j V)
end YangMills.Construction.Tower.FullSpace
end
