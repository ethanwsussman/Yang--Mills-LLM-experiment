import YangMills.Construction.InfiniteLattice.LatticeOfACutoffItsIsometriesAndTimeReflections
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
variable {a : ℝ}
def abovePlane (s : ℝ) : Set AmbientSpace := {x | s < x timeAxis}
def localObsAbove (s : halfSpacingTimes a) : Set (GaugeField a → ℂ) :=
  {F | IsBoundedObservable F ∧
    ∃ R : Set AmbientSpace, R ⊆ abovePlane s ∧ Bornology.IsBounded R ∧ IsRegionMeasurable R F}
def reflectionForm (μ : Measure (GaugeField a)) (s : halfSpacingTimes a)
    (G F : GaugeField a → ℂ) : ℂ :=
  ∫ U, timeConj s G U * F U ∂μ
def ReflectionFormNonneg (μ : Measure (GaugeField a)) (s : halfSpacingTimes a)
    (F : GaugeField a → ℂ) : Prop :=
  (reflectionForm μ s F F).im = 0 ∧ 0 ≤ (reflectionForm μ s F F).re
def reflectionSeminorm (μ : Measure (GaugeField a)) (s : halfSpacingTimes a)
    (F : GaugeField a → ℂ) : ℝ :=
  Real.sqrt (reflectionForm μ s F F).re
end InfiniteLattice
end YangMills.Construction
