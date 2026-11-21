import YangMills.Construction.InfiniteLattice.OneLatticeItsConfigurationsAndMeasuresOnCompactSpaces
import YangMills.Construction.InfiniteLattice.PeriodicGibbsAndTorusLimitSets
import YangMills.Construction.InfiniteLattice.WilsonKernelOfBondsWithOneOrientation
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.InfiniteLattice
noncomputable section
namespace YangMills.Construction.LatticePhases
def densityMeasure {a : ℝ} (ν : Measure (GaugeField a)) (h : GaugeField a → ℂ) :
    Measure (GaugeField a) :=
  ν.withDensity fun U => ENNReal.ofReal (h U).re
def InvariantDensityLaws : Prop :=
  ∀ (D : Setup) (ν : periodicGibbsSet D.L D.K D.β) (h : GaugeField D.mesh → ℂ),
    Measurable[shiftInvariantSigma D.mesh] h → (∃ C : ℝ, ∀ U, ‖h U‖ ≤ C) →
    (∀ (W : OrientedLinkSet D.mesh) (F : GaugeField D.mesh → ℂ),
      F ∈ continuousLocalFunctions D.mesh →
        ∫ U, h U * W.heatBath D.β F U ∂ν.1 = ∫ U, h U * F U ∂ν.1) ∧
    (∀ (v : LatticePoint D.mesh) (F : GaugeField D.mesh → ℂ), IsBoundedObservable F →
      ∫ U, h U * (shift v).actOn F U ∂ν.1 = ∫ U, h U * F U ∂ν.1) ∧
    ((∀ U, (h U).im = 0 ∧ 0 ≤ (h U).re) → ∫ U, h U ∂ν.1 = 1 →
      IsProbabilityMeasure (densityMeasure ν.1 h) ∧
      (∀ F : GaugeField D.mesh → ℂ, IsBoundedObservable F →
        ∫ U, F U ∂(densityMeasure ν.1 h) = ∫ U, h U * F U ∂ν.1) ∧
      densityMeasure ν.1 h ∈ periodicGibbsSet D.L D.K D.β)
end YangMills.Construction.LatticePhases
