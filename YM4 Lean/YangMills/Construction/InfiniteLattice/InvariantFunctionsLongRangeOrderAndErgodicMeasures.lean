import YangMills.Construction.InfiniteLattice.IntegrableVersionsAndVariance
import YangMills.Construction.InfiniteLattice.OneLatticeItsConfigurationsAndMeasuresOnCompactSpaces
import YangMills.Construction.InfiniteLattice.RepresentativesAndThePlateauForm
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.InfiniteLattice
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction
namespace LatticePhases
variable (D : Setup)
def ShiftInvariantFunctionsAreFixed : Prop :=
  ∀ J : GaugeField D.mesh → ℂ, Measurable[shiftInvariantSigma D.mesh] J →
    ∀ v : LatticePoint D.mesh, (shift v).actOn J = J
def PlateauVarianceEqVariance : Prop :=
  ∀ ρ : ProbMeasure (GaugeField D.mesh), IsShiftInvariant ρ.toMeasure →
    ∀ A : GaugeField D.mesh → ℂ, IsBoundedObservable A →
      ∀ Y : GaugeField D.mesh → ℂ, IsIntegrableCondExpRepresentative ρ.toMeasure A Y →
        plateauVariance ρ.toMeasure A = ((varianceOf ρ.toMeasure Y : ℝ) : ℂ) ∧
          0 ≤ varianceOf ρ.toMeasure Y
def ErgodicInvariantFunctionsConstant : Prop :=
  ∀ ρ : ProbMeasure (GaugeField D.mesh), IsShiftErgodic ρ.toMeasure →
    (∀ J : GaugeField D.mesh → ℂ, Measurable[shiftInvariantSigma D.mesh] J →
      ∃ c : ℂ, ρ.HoldsAS fun U => J U = c) ∧
    ∀ A B : GaugeField D.mesh → ℂ, IsBoundedObservable A → IsBoundedObservable B →
      (∀ Y : GaugeField D.mesh → ℂ, IsIntegrableCondExpRepresentative ρ.toMeasure A Y →
        ρ.HoldsAS fun U => Y U = ρ.eval A) ∧
      plateauPairing ρ.toMeasure A B = conj (ρ.eval A) * ρ.eval B ∧
      plateauVariance ρ.toMeasure A = 0
def InvariantFunctionsAndErgodicity : Prop :=
  ∀ D : Setup, ShiftInvariantFunctionsAreFixed D ∧ PlateauVarianceEqVariance D ∧
    ErgodicInvariantFunctionsConstant D
end LatticePhases
end YangMills.Construction
