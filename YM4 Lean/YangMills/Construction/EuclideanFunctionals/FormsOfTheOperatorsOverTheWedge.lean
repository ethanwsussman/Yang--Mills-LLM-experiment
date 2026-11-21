import YangMills.Construction.EuclideanFunctionals.OperatorsOfTheForwardTubeOverTheWedge
import YangMills.Construction.ForwardTube.ClosedTubeAndShiftedTuples
import YangMills.Construction.SpectralTheory.FactsOnResolvedOperators
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
namespace SpectralPoint
def planeProj (p : EMPoints) : EPlanePoints := ⟨![energyOf p, momentumOf p 0], mem_univ _⟩
theorem measurable_planeProj : Measurable planeProj := by
  refine Measurable.subtype_mk (measurable_pi_iff.mpr fun i => ?_)
  fin_cases i
  · exact measurable_energyOf
  · exact measurable_momentumOf_apply 0
def planeExponent (v : ℂ × ℂ) (p : EMPoints) : ℂ :=
  -(v.1 * (energyOf p : ℂ)) + Complex.I * v.2 * (momentumOf p 0 : ℂ)
end SpectralPoint
namespace EuclidFunctionalWithRecon
open HilbertSpaceBasics (UnboundedOp)
variable {c : SharpScale} {S : ConnFamily} (σ : EuclidFunctionalWithRecon c S)
def lightConeOpPlus : UnboundedOp σ.space :=
  ResolvedFacts.realSpectralIntegral σ.planeMeasure SpectralPoint.lightConePlus
def lightConeOpMinus : UnboundedOp σ.space :=
  ResolvedFacts.realSpectralIntegral σ.planeMeasure SpectralPoint.lightConeMinus
def wedgeIntegralOp (v : ℂ × ℂ) : σ.space →L[ℂ] σ.space :=
  σ.planeMeasure.integralOpOn SpectralPoint.wedge fun p => SpectralPoint.planeExpKernel v p.1
end EuclidFunctionalWithRecon
namespace TubeOperatorForms
open HilbertSpaceBasics (UnboundedOp ofBounded IsContraction)
open OperatorTransport (IsNonnegUnbounded)
open BorelSpectral
open ResolvedOps (IsDiagonalized StronglyCommute expComplex)
open ResolvedFacts (rightClosedHalfPlane rightOpenHalfPlane)
open EuclidFunctionalWithRecon
variable {c : SharpScale} {S : ConnFamily} (σ : EuclidFunctionalWithRecon c S)
def PlaneMeasureIsPushforward : Prop :=
  ∀ Δ' : BorelSubsets SpectralPoint.EPlanePoints,
    σ.planeMeasure Δ' =
      σ.jointMeasure ⟨SpectralPoint.planeProj ⁻¹' Δ'.1, SpectralPoint.measurable_planeProj Δ'.2⟩
def WedgeInLightConeCoords : Prop :=
  SpectralPoint.wedge.1 =
      {p | 0 ≤ SpectralPoint.lightConePlus p ∧ 0 ≤ SpectralPoint.lightConeMinus p} ∧
  (∀ (p : SpectralPoint.EPlanePoints) (v : ℂ × ℂ),
    v.1 * (p.1 0 : ℂ) - Complex.I * v.2 * (p.1 1 : ℂ) =
        ForwardTube.lightConePlus v * (SpectralPoint.lightConePlus p : ℂ) +
          ForwardTube.lightConeMinus v * (SpectralPoint.lightConeMinus p : ℂ) ∧
      SpectralPoint.planeExpKernel v p =
        Complex.exp (-(ForwardTube.lightConePlus v * (SpectralPoint.lightConePlus p : ℂ)) -
          ForwardTube.lightConeMinus v * (SpectralPoint.lightConeMinus p : ℂ)) ∧
      ‖SpectralPoint.planeExpKernel v p‖ =
        Real.exp (-((ForwardTube.lightConePlus v).re * SpectralPoint.lightConePlus p) -
          (ForwardTube.lightConeMinus v).re * SpectralPoint.lightConeMinus p)) ∧
  ∀ v ∈ ForwardTube.closedForwardTube, ∀ p ∈ SpectralPoint.wedge.1,
    ‖SpectralPoint.planeExpKernel v p‖ ≤ 1
def ConeConditionIffOffWedgeNull : Prop :=
  σ.ConeCondition ↔ σ.planeMeasure ⟨SpectralPoint.wedge.1ᶜ, SpectralPoint.wedge.2.compl⟩ = 0
def IsContractiveHolSemigroup {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A : UnboundedOp H) : Prop :=
  (∀ ζ ∈ rightClosedHalfPlane, IsContraction (expComplex A ζ)) ∧
  (∀ ζ ∈ rightClosedHalfPlane, ∀ ζ' ∈ rightClosedHalfPlane,
    expComplex A ζ * expComplex A ζ' = expComplex A (ζ + ζ')) ∧
  BanachValued.IsOperatorHolomorphicOn rightOpenHalfPlane
    (fun z : Coordinates.ComplexCoordinates 1 => expComplex A (z 0))
def LightConeOpsFacts : Prop :=
  IsDiagonalized σ.lightConeOpPlus ∧ IsDiagonalized σ.lightConeOpMinus ∧
  OperatorTransport.IsSelfAdjointUnbounded σ.lightConeOpPlus ∧
  OperatorTransport.IsSelfAdjointUnbounded σ.lightConeOpMinus ∧
  StronglyCommute σ.lightConeOpPlus σ.lightConeOpMinus ∧
  IsNonnegUnbounded σ.lightConeOpPlus ∧ IsNonnegUnbounded σ.lightConeOpMinus ∧
  (∀ (ψ : σ.space) (hH : ψ ∈ σ.recon.ham.domain)
      (hP : ψ ∈ (σ.recon.mom 0).domain),
    (∃ h : ψ ∈ σ.lightConeOpPlus.domain,
      σ.lightConeOpPlus ⟨ψ, h⟩ = (1 / 2 : ℂ) •
        (σ.recon.ham ⟨ψ, hH⟩ - σ.recon.mom 0 ⟨ψ, hP⟩)) ∧
    ∃ h : ψ ∈ σ.lightConeOpMinus.domain,
      σ.lightConeOpMinus ⟨ψ, h⟩ = (1 / 2 : ℂ) •
        (σ.recon.ham ⟨ψ, hH⟩ + σ.recon.mom 0 ⟨ψ, hP⟩)) ∧
  (∀ ζ ∈ rightClosedHalfPlane, ∀ ζ' ∈ rightClosedHalfPlane,
    Commute (expComplex σ.lightConeOpPlus ζ) (expComplex σ.lightConeOpMinus ζ')) ∧
  IsContractiveHolSemigroup σ.lightConeOpPlus ∧
  IsContractiveHolSemigroup σ.lightConeOpMinus
def TubeOpIsExpProduct (v : ℂ × ℂ) : Prop :=
  σ.tubeOp v = ofBounded (σ.wedgeIntegralOp v) ∧
  ‖σ.wedgeIntegralOp v‖ ≤ 1 ∧
  σ.tubeOp v = ofBounded
    (expComplex σ.lightConeOpPlus (ForwardTube.lightConePlus v) *
      expComplex σ.lightConeOpMinus (ForwardTube.lightConeMinus v)) ∧
  σ.tubeOp v = ofBounded
    (expComplex σ.lightConeOpMinus (ForwardTube.lightConeMinus v) *
      expComplex σ.lightConeOpPlus (ForwardTube.lightConePlus v))
def TubeOpIsPyramidIntegral (v : ℂ × ℂ) : Prop :=
  σ.tubeOp v =
    σ.jointMeasure.setIntegralOp SpectralPoint.pyramid
      (fun p => Complex.exp (SpectralPoint.planeExponent v p.1)) ∧
  ∀ p : SpectralPoint.EMPoints, SpectralPoint.planeExponent v p =
    -(ForwardTube.lightConePlus v *
        (((SpectralPoint.energyOf p - SpectralPoint.momentumOf p 0) / 2 : ℝ) : ℂ)) -
      ForwardTube.lightConeMinus v *
        (((SpectralPoint.energyOf p + SpectralPoint.momentumOf p 0) / 2 : ℝ) : ℂ)
def Holds : Prop :=
  ∀ (c : SharpScale) (S : ConnFamily) (σ : EuclidFunctionalWithRecon c S) (v : ℂ × ℂ),
    v ∈ ForwardTube.closedForwardTube →
      PlaneMeasureIsPushforward σ ∧
      WedgeInLightConeCoords ∧
      ConeConditionIffOffWedgeNull σ ∧
      (σ.ConeCondition →
        TubeOpIsExpProduct σ v ∧ LightConeOpsFacts σ) ∧
      (σ.ConeCondition → TubeOpIsPyramidIntegral σ v)
end TubeOperatorForms
end YangMills.Construction.EuclideanFunctionals
