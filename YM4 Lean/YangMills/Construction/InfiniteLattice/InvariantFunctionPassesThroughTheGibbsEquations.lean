import YangMills.Construction.HilbertSpace.FormCompletionsAndBorelPVMs
import YangMills.Construction.InfiniteLattice.GibbsKernelAndPeriodicGibbsStatesOfTheUnitLattice
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def weightedGibbsUnit (h : GaugeField (1 : ℝ) → ℂ) (ν : Measure (GaugeField (1 : ℝ))) :
    Measure (GaugeField (1 : ℝ)) :=
  YangMills.Construction.FormHilbert.densityMeasure (fun U => (h U).re) ν
def ShiftInvariantWeightPassesGibbsEquations : Prop :=
  ∀ β : ℝ, 0 < β →
  ∀ (ν : Measure (GaugeField (1 : ℝ))) (Z : AddSubgroup (LatticePoint (1 : ℝ))),
    ν ∈ periodicGibbsUnit β → IsPeriodSubgroup ν Z →
  ∀ h : GaugeField (1 : ℝ) → ℂ, Measurable[shiftInvariantSigma 1] h →
    (∃ C : ℝ, ∀ U, ‖h U‖ ≤ C) →
    (∀ (W : Finset (Link (1 : ℝ)))
        (hW : YangMills.Construction.GibbsAtFixedSpacing.HasNoOppositePairs
          (W : Set (Link (1 : ℝ))))
        (F : GaugeField (1 : ℝ) → ℂ),
        F ∈ YangMills.Construction.GibbsAtFixedSpacing.continuousLocal 1 →
      ∫ U, h U * gibbsKernelUnit β W hW F U ∂ν = ∫ U, h U * F U ∂ν) ∧
    (∀ v ∈ Z, ∀ F : GaugeField (1 : ℝ) → ℂ, IsBoundedObservable F →
      ∫ U, h U * (shift v).actOn F U ∂ν = ∫ U, h U * F U ∂ν) ∧
    ((∀ U, 0 ≤ h U) → ∫ U, h U ∂ν = 1 →
      IsProbabilityMeasure (weightedGibbsUnit h ν) ∧
      (∀ F : GaugeField (1 : ℝ) → ℂ, IsBoundedObservable F →
        ∫ U, F U ∂weightedGibbsUnit h ν = ∫ U, h U * F U ∂ν) ∧
      weightedGibbsUnit h ν ∈ periodicGibbsUnit β ∧
      IsPeriodSubgroup (weightedGibbsUnit h ν) Z)
end YangMills.Construction.InfiniteLattice
