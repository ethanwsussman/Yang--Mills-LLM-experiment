import YangMills.Construction.Conventions.TorusBoundDefs
import YangMills.Construction.Lattice.CompactGaugeFieldSpaceAndPartitionBounds
import YangMills.Construction.Lattice.SettingOfTheTorusBound
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.TorusBound
namespace Setup
variable (D : Setup)
abbrev gaugeFieldSet : Set D.LinkConfig :=
  PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ)
variable {n : ℕ}
def familyGeneratingFun (f : Fin n → D.Torus → ℝ) (z : Coordinates.ComplexCoordinates n) : ℂ :=
  D.expect fun U => Complex.exp (∑ i, z i * ((D.obs (f i) U : ℝ) : ℂ))
def logGenDomain (f : Fin n → D.Torus → ℝ) : Set (Coordinates.ComplexCoordinates n) :=
  {z | ‖D.familyGeneratingFun f z - 1‖ < 1}
def logFamilyGeneratingFun (f : Fin n → D.Torus → ℝ) (z : Coordinates.ComplexCoordinates n) : ℂ :=
  TorusBoundNotation.principalLog (D.familyGeneratingFun f z)
def logPartitionFun (f : Fin n → D.Torus → ℝ) (z : Coordinates.ComplexCoordinates n) : ℂ :=
  ((Real.log (D.partitionFun 0).re : ℝ) : ℂ) + D.logFamilyGeneratingFun f z
end Setup
namespace ObservableCumulants
variable (D : Setup)
def ObservableProperties : Prop :=
  (∀ w w' : D.Torus → ℂ, D.IsWeight w → D.IsWeight w' → ∀ c : ℂ, ∀ U ∈ D.gaugeFieldSet,
    D.obs (w + c • w') U = D.obs w U + c * D.obs w' U) ∧
  (∀ w : D.Torus → ℂ, D.IsWeight w → ∀ U ∈ D.gaugeFieldSet,
    (starRingEnd ℂ) (D.obs w U) = D.obs (fun x => (starRingEnd ℂ) (w x)) U) ∧
  ∀ w : D.Torus → ℂ, D.IsWeight w →
    @Continuous D.gaugeFieldSet ℂ
      (PeriodicLattice.GaugeFieldSpace.productTopology D.L D.m D.K) _ (fun U => D.obs w U.1) ∧
    (∃ C : ℝ, ∀ U ∈ D.gaugeFieldSet, ‖D.obs w U‖ ≤ C) ∧
    ((∀ x, (w x).im = 0) → ∀ U ∈ D.gaugeFieldSet, (D.obs w U).im = 0)
def PartitionRatio : Prop :=
  D.partitionFun 0 = (PeriodicLattice.partitionFunction D.L D.m D.K D.β : ℂ) ∧
    0 < PeriodicLattice.partitionFunction D.L D.m D.K D.β ∧
    ∀ w : D.Torus → ℂ, D.IsWeight w →
      D.expect (fun U => Complex.exp (D.obs w U)) =
        D.partitionFun w / D.partitionFun 0
def FamilyGeneratingFunProperties {n : ℕ} (f : Fin n → D.Torus → ℝ) : Prop :=
  (∀ z : Coordinates.ComplexCoordinates n,
    D.familyGeneratingFun f z = D.partitionFun (D.smear z f) / D.partitionFun 0) ∧
  ComplexVariables.IsEntireFun (D.familyGeneratingFun f) ∧
  D.familyGeneratingFun f 0 = 1 ∧
  IsOpen (D.logGenDomain f) ∧
  (0 : Coordinates.ComplexCoordinates n) ∈ D.logGenDomain f ∧
  ComplexVariables.IsHolomorphicScalar (D.logGenDomain f) (D.logFamilyGeneratingFun f) ∧
  TorusBoundNotation.MixedDerivFormed (D.logGenDomain f) (D.logPartitionFun f) ∧
  D.truncatedCorrelation f = TorusBoundNotation.mixedDeriv (D.logPartitionFun f) 0 ∧
  ((∃ i, ∀ x, f i x = 0) → D.truncatedCorrelation f = 0)
def Statement : Prop :=
  ∀ D : Setup, ObservableProperties D ∧ PartitionRatio D ∧
    ∀ (n : ℕ) (f : Fin n → D.Torus → ℝ), D.IsRealFamily f → FamilyGeneratingFunProperties D f
end ObservableCumulants
end YangMills.Construction.TorusBound
end
