import YangMills.Construction.InfiniteLattice.JointSpectralMeasuresOfThePictures
import YangMills.Construction.JointSpectrum.DiscAndCone
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
open OneLoopNotation ComplexHilbert
open JointSpectrum DiscGeometry
namespace LatticeConventions
open InfiniteLattice (GaugeField)
def coneInteriorOf (J : Type*) [Unique J] : Set (SpectralDomain J) :=
  {p | (1 - (p.1 : ℝ)) ^ 2 ≥ (p.1 : ℝ) * ‖1 - (p.2 default : ℂ)‖ ^ 2}
def coneDefectNonnegSet (J : Type*) [Unique J] : Set (SpectralDomain J) :=
  {p | 0 ≤ coneDefect p.1 (p.2 default)}
def LinkConeInequality : Prop :=
  ∀ (a : Spacing) (μ lam : Direction) (hne : μ ≠ lam)
    (ν : Measure (GaugeField (a : ℝ))) [IsProbabilityMeasure ν],
    PairConditions hne ν →
      OpGE
          ((idOp (LinkFrame.LinkHilbertSpace a μ ν) - LinkFrame.transferOperator a μ ν) ^ 2)
          (LinkFrame.transferOperator a μ ν *
            ((2 : ℂ) • idOp (LinkFrame.LinkHilbertSpace a μ ν)
              - LinkFrame.transverseShift a μ ν ⟨lam, hne.symm⟩
              - ContinuousLinearMap.adjoint (LinkFrame.transverseShift a μ ν ⟨lam, hne.symm⟩))) ∧
        IsClosed (coneInteriorOf (SingleTransverse (μ := μ) ⟨lam, hne.symm⟩)) ∧
        coneInteriorOf (SingleTransverse (μ := μ) ⟨lam, hne.symm⟩) =
          coneDefectNonnegSet (SingleTransverse (μ := μ) ⟨lam, hne.symm⟩) ∧
        SpectralMapSupportedOn (LinkFrame.singleShiftSpectralMeasure a μ ν ⟨lam, hne.symm⟩)
          (coneInteriorOf (SingleTransverse (μ := μ) ⟨lam, hne.symm⟩)) ∧
        LinkFrame.singleShiftSpectralMeasure a μ ν ⟨lam, hne.symm⟩
          (coneExteriorOf (SingleTransverse (μ := μ) ⟨lam, hne.symm⟩)) = 0
end LatticeConventions
end YangMills.Construction
end
