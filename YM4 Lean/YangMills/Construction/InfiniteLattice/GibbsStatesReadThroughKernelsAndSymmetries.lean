import YangMills.Construction.InfiniteLattice.LatticeIsometriesMirrorsAndTheClassOfReflectionPositiveMeasures
import YangMills.Construction.InfiniteLattice.PeriodicGibbsAndTorusLimitSets
import YangMills.Construction.InfiniteLattice.WilsonKernelOfBondsWithOneOrientation
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.InfiniteLattice
noncomputable section
namespace YangMills.Construction.LatticePhases.GibbsKernelsAndSymmetries
def HeatBathInvariant {a : ℝ} (β' : ℝ) (ρ : ProbMeasure (GaugeField a)) : Prop :=
  ∀ W : OrientedLinkSet a, ∀ F ∈ continuousLocalFunctions a,
    ρ.eval (W.heatBath β' F) = ρ.eval F
def Assertion : Prop :=
  ∀ (D : Setup) (β' : ℝ), 0 < β' →
    (∀ ρ : ProbMeasure (GaugeField D.mesh),
      IsGibbs β' ρ.toMeasure ↔ HeatBathInvariant β' ρ) ∧
    (∀ ρ : ProbMeasure (GaugeField D.mesh), IsPeriodicGibbs β' ρ.toMeasure →
      (∀ r : latticeMotions D.mesh,
        IsSymmetricUnder ρ.toMeasure (latticeMotionSymmetry r)) ∧
      IsShiftInvariant ρ.toMeasure ∧
      ∀ P : LatticeMirror D.mesh, IsReflectionPositiveAt ρ P) ∧
    (∀ ρ : ProbMeasure (GaugeField D.mesh), ρ.toMeasure ∈ periodicGibbsSet D.L D.K β' →
      ρ ∈ D.reflectionPositiveStates) ∧
    (periodicGibbsSet D.L D.K β').Nonempty
end YangMills.Construction.LatticePhases.GibbsKernelsAndSymmetries
end
