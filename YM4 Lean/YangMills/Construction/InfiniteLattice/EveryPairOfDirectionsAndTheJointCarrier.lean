import YangMills.Construction.EnergyMomentum.ChordSlopeConstant
import YangMills.Construction.InfiniteLattice.ConeInequalityInTheLinkPicture
import YangMills.Construction.InfiniteLattice.GeneratorsAndJointSpectrumOfTheTimePicture
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace LatticeConventions
namespace DirectionPairsSupport
open MeasureTheory Set
open YangMills.Construction.ComplexHilbert
open YangMills.Construction.JointSpectrum
open YangMills.Construction.InfiniteLattice (GaugeField IsShiftInvariant)
open scoped ENNReal
section Variables
variable {μ : Direction}
def energyOfTime (t : unitInterval) : ℝ≥0∞ :=
  open Classical in if (t : ℝ) = 0 then ∞ else ENNReal.ofReal (-Real.log (t : ℝ))
def momentumAngle (ζ : TransverseDirection μ → Circle) (l : TransverseDirection μ) : ℝ :=
  principalArg (ζ l : ℂ)
def supAngle (ζ : TransverseDirection μ → Circle) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun l => |momentumAngle ζ l|
variable (μ)
def coshCosRegion : Set (SpectralDomain (TransverseDirection μ)) :=
  {p | 0 < (p.1 : ℝ) ∧
    ∀ l, 2 ≤ Real.cosh (energyOfTime p.1).toReal + Real.cos (momentumAngle p.2 l)}
def linearConeRegion : Set (SpectralDomain (TransverseDirection μ)) :=
  {p | ENNReal.ofReal (YangMills.Construction.EnergyMomentum.chordSlopeConstant * supAngle p.2) ≤
    energyOfTime p.1}
def zeroTimeSet : Set (SpectralDomain (TransverseDirection μ)) :=
  {p | (p.1 : ℝ) = 0}
end Variables
def SiteConeInequality (a : Spacing) {μ ν' : Direction} (hne : μ ≠ ν')
    (ν : Measure (GaugeField (a : ℝ))) [IsProbabilityMeasure ν] : Prop :=
  OpGE
      ((idOp (SiteFrame.SiteHilbertSpace a μ ν) - SiteFrame.transferOperator a μ ν) ^ 2)
      (SiteFrame.transferOperator a μ ν *
        ((2 : ℂ) • idOp (SiteFrame.SiteHilbertSpace a μ ν)
          - SiteFrame.transverseShift a μ ν ⟨ν', hne.symm⟩
          - ContinuousLinearMap.adjoint (SiteFrame.transverseShift a μ ν ⟨ν', hne.symm⟩))) ∧
    SpectralMapSupportedOn (SiteFrame.singleShiftSpectralMeasure a μ ν ⟨ν', hne.symm⟩)
      (coneInteriorOf (SingleTransverse (μ := μ) ⟨ν', hne.symm⟩))
def JointSupport (a : Spacing) (μ : Direction) (ν : Measure (GaugeField (a : ℝ)))
    [IsProbabilityMeasure ν] : Prop :=
  SpectralMapSupportedOn (LinkFrame.allShiftsSpectralMeasure a μ ν) (coshCosRegion μ) ∧
    coshCosRegion μ ⊆ linearConeRegion μ ∧
    SpectralMapSupportedOn (SiteFrame.allShiftsSpectralMeasure a μ ν)
      (coshCosRegion μ ∪ zeroTimeSet μ) ∧
    ∀ p ∈ zeroTimeSet μ, energyOfTime p.1 = ∞
def PairwiseConeAndJointSupport : Prop :=
  (LinkConeInequality ∧
    ∀ (a : Spacing) (μ ν' : Direction) (hne : μ ≠ ν')
      (ν : Measure (GaugeField (a : ℝ))) [IsProbabilityMeasure ν],
      PairConditions hne ν → SiteConeInequality a hne ν) ∧
  ∀ (a : Spacing) (ν : Measure (GaugeField (a : ℝ))) [IsProbabilityMeasure ν],
    IsShiftInvariant ν → IsReflectionPositiveAtEveryMirror ν →
      ∀ μ : Direction, JointSupport a μ ν
end DirectionPairsSupport
end LatticeConventions
end YangMills.Construction
end
