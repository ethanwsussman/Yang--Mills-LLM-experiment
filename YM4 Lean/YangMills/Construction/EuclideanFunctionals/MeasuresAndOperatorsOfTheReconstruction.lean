import YangMills.Construction.EuclideanFunctionals.FirstFactsOnAReconstruction
import YangMills.Construction.EuclideanFunctionals.SignsOfTheCalculusOfAProjectionValuedMeasure
import YangMills.Construction.SpectralTheory.BorelFunctionalCalculusLaws
import YangMills.Construction.SpectralTheory.ProjectionValuedBorelMeasuresOnTheWholeSpaceAndSimpleFunctions
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
open BorelSpectral
open WholeSpaceSpectral (restrictToUniv diagSetFn)
open BorelCalculus (IsBoundedFn)
open SpectralTheorem (IsSpectralMeasureFor spectralIntegralOp pushforwardToLine)
open HilbertSpaceBasics (IsContraction ofBounded)
open ResolvedOps (boxSet IsJointSpectralMeasure)
namespace SpectralPoint
def planeEnergyCoord (p : EPlanePoints) : ℝ := p.1 0
def planeMomentumCoord (p : EPlanePoints) : ℝ := p.1 1
theorem measurable_planeEnergyCoord : Measurable planeEnergyCoord :=
  (measurable_pi_apply 0).comp measurable_subtype_coe
theorem measurable_planeMomentumCoord : Measurable planeMomentumCoord :=
  (measurable_pi_apply 1).comp measurable_subtype_coe
end SpectralPoint
namespace EuclidFunctionalWithRecon
open SpectralPoint
variable {c : SharpScale} {S : ConnFamily} (σ : EuclidFunctionalWithRecon c S)
def planePushforward : SpectralMeasure EPlanePoints σ.space :=
  σ.jointMeasure.pushforward (by norm_num) MeasurableSet.univ energyMomentumPlane
    measurable_energyMomentumPlane
def HasRectangleValues (F : SpectralMeasure EPlanePoints σ.space) : Prop :=
  ∀ A B : BorelSubsets ℝ, F (boxSet ![A, B]) =
    SpectralTheorem.spectralMeasure σ.recon.ham (realLineSet A) *
      SpectralTheorem.spectralMeasure (σ.recon.mom 0) (realLineSet B)
structure MeasureFacts : Prop where
  isJoint : IsJointSpectralMeasure
    (hamMomFamily σ.recon.ham σ.recon.mom)
    σ.jointMeasure
  spectralMeasureAt_eq : ∀ (ψ : σ.space) (A : BorelSubsets (Fin 4 → ℝ)),
    (((σ.spectralMeasureAt ψ).real (restrictToUniv A).1 : ℝ) : ℂ) = diagSetFn σ.jointMeasure ψ A
  pushforward_hasValues : σ.HasRectangleValues σ.planePushforward
  pushforward_unique : ∀ F : SpectralMeasure EPlanePoints σ.space,
    σ.HasRectangleValues F → F = σ.planePushforward
  pushforward_eq : σ.planePushforward = σ.planeMeasure
  planeMeasure_apply : ∀ A : BorelSubsets EPlanePoints, σ.planeMeasure A =
    σ.jointMeasure
      ⟨energyMomentumPlane ⁻¹' A.1, measurable_energyMomentumPlane A.2⟩
  planeDiagMeasure_eq : ∀ ψ : σ.space,
    σ.planeDiagMeasure ψ = (σ.spectralMeasureAt ψ).map energyMomentumPlane
  planeIntegralOp_eq : ∀ f : EPlanePoints → ℂ, Measurable f → IsBoundedFn f →
    σ.planeIntegralOp f = σ.jointMeasure.integralOp (f ∘ energyMomentumPlane)
  pushforwardToLine_energy : pushforwardToLine σ.jointMeasure SpectralPoint.energyOf
      SpectralPoint.measurable_energyOf =
    SpectralTheorem.spectralMeasure σ.recon.ham
  pushforwardToLine_planeEnergy :
    pushforwardToLine σ.planeMeasure planeEnergyCoord measurable_planeEnergyCoord =
      SpectralTheorem.spectralMeasure σ.recon.ham
  pushforwardToLine_planeMomentum :
    pushforwardToLine σ.planeMeasure planeMomentumCoord measurable_planeMomentumCoord =
      SpectralTheorem.spectralMeasure (σ.recon.mom 0)
  isSpectralMeasureFor_ham : IsSpectralMeasureFor
    (SpectralTheorem.spectralMeasure σ.recon.ham) σ.recon.ham
  isSpectralMeasureFor_mom : IsSpectralMeasureFor
    (SpectralTheorem.spectralMeasure (σ.recon.mom 0)) (σ.recon.mom 0)
def BoundedOnCarrierIntegrals : Prop :=
  σ.jointMeasure.IsCarriedBy SpectralPoint.nonnegEnergy ∧
    ∀ C : BorelSubsets EMPoints, σ.jointMeasure.IsCarriedBy C → ∀ Φ : EMPoints → ℂ, Measurable Φ →
      IsBoundedFn (fun y : C.1 => Φ y.1) →
        spectralIntegralOp σ.jointMeasure Φ =
          ofBounded (σ.jointMeasure.integralOpOn C fun y => Φ y.1)
def LaplaceFourierRep : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∀ x : Fin 3 → ℝ,
    σ.heatSemigroup t * σ.translOp (spatialEmbed x) =
        σ.jointMeasure.integralOpOn SpectralPoint.nonnegEnergy
          (laplaceFourierKernel t (spatialEmbed x)) ∧
      IsContraction (σ.heatSemigroup t)
def VacEnergyZero : Prop :=
  ‖σ.recon.vac‖ = 1 ∧
    (∀ t : ℝ, 0 ≤ t → σ.heatSemigroup t σ.recon.vac = σ.recon.vac) ∧
    σ.spectralMeasureAt σ.recon.vac {p | SpectralPoint.energyOf p ≠ 0} = 0
def TranslateClasses : Prop :=
  ∀ x : R4, 0 ≤ x 3 → ∀ F : finCombIn upperHalf,
    ∃ h : (EuclidMotion.transl x).actFree F.1 ∈ finCombIn upperHalf,
      σ.heatSemigroup (x 3)
          (σ.translOp (spatialEmbed (spatialProj x)) (σ.recon.cls F)) =
        σ.recon.cls ⟨_, h⟩
def CommutesWithRotations : Prop :=
  (∀ (w : timeStabilizer) (t : ℝ), 0 ≤ t →
    σ.recon.rotOp w ∘ₗ
        (σ.heatSemigroup t : σ.space →ₗ[ℂ] σ.space) =
      (σ.heatSemigroup t : σ.space →ₗ[ℂ] σ.space) ∘ₗ
        σ.recon.rotOp w) ∧
    ∀ (w : timeStabilizer), ∀ v ∈ spatialVecs,
      (w : EuclidMotion) v ∈ spatialVecs ∧
        σ.recon.rotOp w ∘ₗ
            (σ.translOp v : σ.space →ₗ[ℂ] σ.space) ∘ₗ
              (σ.recon.rotOp_unitary w).inv =
          (σ.translOp ((w : EuclidMotion) v) : σ.space →ₗ[ℂ] σ.space)
end EuclidFunctionalWithRecon
def ReconstructionMeasureOperatorFacts : Prop :=
  ∀ (c : SharpScale) (S : ConnFamily) (σ : EuclidFunctionalWithRecon c S),
    σ.MeasureFacts ∧ σ.BoundedOnCarrierIntegrals ∧
      σ.LaplaceFourierRep ∧ σ.VacEnergyZero ∧ σ.TranslateClasses ∧
      σ.CommutesWithRotations
end YangMills.Construction.EuclideanFunctionals
