import YangMills.Construction.ChessboardTori.SignsOfPeriodicStatesAgainstTheTori
import YangMills.Construction.ChessboardTori.UnitAndStandardGrids
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.ChessboardTori
open InfiniteLattice (IsSymmetricUnder IsReflectionPositiveAt IsShiftInvariant LatticeMirror
  ReflectionClass)
def ChessboardSetup.IsGridSymmetric (D : ChessboardSetup) (ν : Measure D.GaugeField) : Prop :=
  (∀ g : ReflectionGrid D, g.IsCoarse → ∀ r : g.reflectionGroup,
      IsSymmetricUnder ν (g.toLatticeSym r)) ∧
    ∀ r : D.unitReflectionGroup, IsSymmetricUnder ν (D.unitReflectionGrid.toLatticeSym r)
def GridGroupInvariance.Statement : Prop :=
  ∀ D : ChessboardSetup,
    (∀ (ν : Measure D.GaugeField) [IsProbabilityMeasure ν] (μ : Fin 4) (P : LatticeMirror D.mesh),
      P.cls = ReflectionClass.axial μ → P.BisectsLinks →
        IsShiftInvariant ν → IsReflectionPositiveAt ν P →
          IsSymmetricUnder ν P.symmetry) ∧
    (∀ (ν : Measure D.GaugeField) [IsProbabilityMeasure ν], IsShiftInvariant ν →
      (∀ (μ : Fin 4) (P : LatticeMirror D.mesh), P.cls = ReflectionClass.axial μ →
        P.BisectsLinks → IsReflectionPositiveAt ν P) →
          D.IsGridSymmetric ν) ∧
    ∀ ν ∈ D.periodicStates, D.IsGridSymmetric ν
end YangMills.Construction.ChessboardTori
end
