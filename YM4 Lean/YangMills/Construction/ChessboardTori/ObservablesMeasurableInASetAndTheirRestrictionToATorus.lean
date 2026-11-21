import YangMills.Construction.ChessboardTori.NamesOfAMirrorGridOnATorus
import YangMills.Construction.ChessboardTori.SignsOfPeriodicStatesAgainstTheTori
import YangMills.Construction.Lattice.ToriLatticesNormsAndFunctionsOfFinitelyManyVariables
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace ChessboardTori
open YangMills.Construction.InfiniteLattice (AmbientSpace)
namespace ChessboardSetup
variable (D : ChessboardSetup)
def liftToCompactFields (A : D.GaugeField → ℂ) :
    PeriodicLattice.CompactGaugeField D.L D.m ((D.K : ℕ) : ℤ) → ℂ :=
  fun W => D.liftedObservable A W.1
def RegionMeasurableDependsOnLinks (S : Set AmbientSpace) : Prop :=
  ∀ A : D.GaugeField → ℂ, InfiniteLattice.IsBoundedObservable A →
    InfiniteLattice.IsRegionMeasurable S A →
    ∀ U U' : D.GaugeField, (∀ b ∈ D.positiveLinksOn S, U b = U' b) → A U = A U'
def RegionMeasurableIffLinkFunction (S : Set AmbientSpace) : Prop :=
  ∀ A : D.GaugeField → ℂ, InfiniteLattice.IsBoundedObservable A →
    (InfiniteLattice.IsRegionMeasurable S A ↔
      ∃ f : InfiniteLattice.LinkVariables (D.positiveLinksOn S) → ℂ,
        Measurable[borel (InfiniteLattice.LinkVariables (D.positiveLinksOn S))] f ∧
          (∃ C : ℝ, ∀ V, ‖f V‖ ≤ C) ∧
          ∀ U : D.GaugeField, A U = f (InfiniteLattice.restrictField U (D.positiveLinksOn S)))
def CellObservablesEqInteriorMeasurable : Prop :=
  ∀ g : ReflectionGrid D, g.IsCoarse → ∀ C ∈ g.cellSet,
    ReflectionGrid.cellObservables (D := D) C =
      {A | InfiniteLattice.IsBoundedObservable A ∧ InfiniteLattice.IsRegionMeasurable (interior C) A}
def CellObservablesMonotone : Prop :=
  ∀ g g' : ReflectionGrid D, g.IsCoarse → g'.IsCoarse → ∀ C ∈ g.cellSet, ∀ C' ∈ g'.cellSet,
    interior C ⊆ interior C' →
      ReflectionGrid.cellObservables (D := D) C ⊆ ReflectionGrid.cellObservables (D := D) C'
def LiftedObservableProperties : Prop :=
  ∀ A A' : D.GaugeField → ℂ, InfiniteLattice.IsBoundedObservable A →
    InfiniteLattice.IsBoundedObservable A' →
    (Measurable[borel (PeriodicLattice.CompactGaugeField D.L D.m ((D.K : ℕ) : ℤ))]
        (D.liftToCompactFields A) ∧
      ∃ C : ℝ, ∀ W, ‖D.liftToCompactFields A W‖ ≤ C) ∧
    D.periodicExpectation (D.liftedObservable A) = D.liftedExpectation A ∧
    (∀ W, D.liftToCompactFields (fun U => A U + A' U) W =
      D.liftToCompactFields A W + D.liftToCompactFields A' W) ∧
    (∀ W, D.liftToCompactFields (fun U => A U * A' U) W =
      D.liftToCompactFields A W * D.liftToCompactFields A' W) ∧
    ∀ W, D.liftToCompactFields (fun U => starRingEnd ℂ (A U)) W =
      starRingEnd ℂ (D.liftToCompactFields A W)
end ChessboardSetup
def MeasurableObservablesAndLifts.Statement : Prop :=
  ∀ D : ChessboardSetup,
    (∀ S : Set AmbientSpace, D.RegionMeasurableDependsOnLinks S) ∧
      (∀ S : Set AmbientSpace, D.RegionMeasurableIffLinkFunction S) ∧
      D.CellObservablesEqInteriorMeasurable ∧
      D.CellObservablesMonotone ∧
      D.LiftedObservableProperties
end ChessboardTori
end YangMills.Construction
end
