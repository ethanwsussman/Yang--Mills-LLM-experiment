import YangMills.Construction.InfiniteLattice.PeriodOrbitsArraysOfOneGeneratorAndPerturbedKernels
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.InfiniteLattice
noncomputable section
namespace YangMills.Construction.GibbsAtFixedSpacing.SingleGeneratorArray
variable {a : ℝ} (A : SingleGeneratorArray a) (Γ : InfiniteLattice.PeriodSublattice a)
def PeriodsWithin : Prop := Γ.periods ≤ A.sublattice
abbrev QuotientClasses : Type := A.sublattice ⧸ Γ.periods.addSubgroupOf A.sublattice
def classRep (q : A.QuotientClasses Γ) : A.sublattice := Quotient.out q
def foldedSum (U : Γ.QuotientField) : ℝ :=
  ∑ᶠ q : A.QuotientClasses Γ, Γ.periodize (A.translate (A.classRep Γ q)) U
def tiltWeight (β t : ℝ) (U : Γ.QuotientField) : ℝ :=
  Real.exp (t * A.foldedSum Γ U - β * ∑ᶠ p : Γ.QuotientPlaquette, Γ.quotientFaceEnergy U p)
variable {Γ}
def tiltNormalizer (_h : A.PeriodsWithin Γ) (β t : ℝ) : ℝ :=
  ∫ U, A.tiltWeight Γ β t U ∂Γ.quotientHaar
def tiltMeasure (h : A.PeriodsWithin Γ) (β t : ℝ) : Measure Γ.QuotientField :=
  (ENNReal.ofReal (A.tiltNormalizer h β t))⁻¹ •
    Γ.quotientHaar.withDensity fun U => ENNReal.ofReal (A.tiltWeight Γ β t U)
def liftedTiltMeasure (h : A.PeriodsWithin Γ) (β t : ℝ) :
    Measure (InfiniteLattice.GaugeField a) :=
  (A.tiltMeasure h β t).map Γ.lift
variable (Γ) in
theorem tiltWeight_zero (β : ℝ) : A.tiltWeight Γ β 0 = Γ.boltzmannWeight β := by
  funext U
  simp [tiltWeight, InfiniteLattice.PeriodSublattice.boltzmannWeight]
theorem tiltNormalizer_zero (h : A.PeriodsWithin Γ) (β : ℝ) :
    A.tiltNormalizer h β 0 = Γ.partitionFunction β := by
  simp only [tiltNormalizer, tiltWeight_zero, InfiniteLattice.PeriodSublattice.partitionFunction]
theorem tiltMeasure_zero (h : A.PeriodsWithin Γ) (β : ℝ) :
    A.tiltMeasure h β 0 = Γ.gibbsMeasure β := by
  simp only [tiltMeasure, tiltNormalizer_zero, tiltWeight_zero,
    InfiniteLattice.PeriodSublattice.gibbsMeasure]
theorem liftedTiltMeasure_zero (h : A.PeriodsWithin Γ) (β : ℝ) :
    A.liftedTiltMeasure h β 0 = Γ.liftedGibbsMeasure β := by
  simp only [liftedTiltMeasure, tiltMeasure_zero,
    InfiniteLattice.PeriodSublattice.liftedGibbsMeasure]
end YangMills.Construction.GibbsAtFixedSpacing.SingleGeneratorArray
