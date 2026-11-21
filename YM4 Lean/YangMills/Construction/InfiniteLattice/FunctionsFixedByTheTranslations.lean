import YangMills.Construction.InfiniteLattice.OneLatticeItsConfigurationsAndMeasuresOnCompactSpaces
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.InfiniteLattice
noncomputable section
namespace YangMills.Construction
namespace LatticePhases
variable {a : ℝ}
def shiftFixedSet (X : GaugeField a → ℂ) : Set (GaugeField a) :=
  {U | ∀ v : LatticePoint a, (shift v).actOn X U = X U}
namespace ShiftFixedFunctions
def FixedEverywhereIsInvariantMeasurable (D : Setup) : Prop :=
  ∀ J : GaugeField D.mesh → ℂ, Measurable J →
    (∀ (v : LatticePoint D.mesh) (U : GaugeField D.mesh), (shift v).actOn J U = J U) →
    Measurable[shiftInvariantSigma D.mesh] J
def FixedAlmostSurelyHasInvariantRepresentative (D : Setup) (ρ : ProbMeasure (GaugeField D.mesh)) : Prop :=
  ∀ X : GaugeField D.mesh → ℂ, Measurable X →
    (∀ v : LatticePoint D.mesh, ρ.HoldsAS fun U => (shift v).actOn X U = X U) →
    MeasurableSet[shiftInvariantSigma D.mesh] (shiftFixedSet X) ∧
      ρ.toMeasure (shiftFixedSet X) = 1 ∧
      Measurable[shiftInvariantSigma D.mesh] ((shiftFixedSet X).indicator X) ∧
      ρ.HoldsAS fun U => (shiftFixedSet X).indicator X U = X U
def Assertion : Prop :=
  ∀ D : Setup, FixedEverywhereIsInvariantMeasurable D ∧
    ∀ ρ : ProbMeasure (GaugeField D.mesh), FixedAlmostSurelyHasInvariantRepresentative D ρ
end ShiftFixedFunctions
end LatticePhases
end YangMills.Construction
