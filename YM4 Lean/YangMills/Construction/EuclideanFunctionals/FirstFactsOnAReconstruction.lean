import YangMills.Construction.EuclideanFunctionals.JointSpectralMeasureOfAReconstructionAndTheConeCondition
import YangMills.Construction.SpectralTheory.FunctionsOfSelfAdjointOperators
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
namespace SpectralPoint
def spatialEmbed (u : Fin 3 → ℝ) : R4 := Fin.snoc (α := fun _ => ℝ) u 0
def IsUnitVec3 (n : Fin 3 → ℝ) : Prop := dot3 n n = 1
def rotSpatial (w : timeStabilizer) (u : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun j => (w : EuclidMotion) (spatialEmbed u) j.castSucc
def rotPoint (w : timeStabilizer) (p : EMPoints) : EMPoints :=
  ⟨Fin.cons (α := fun _ => ℝ) (energyOf p) (rotSpatial w (momentumOf p)), mem_univ _⟩
def laplaceFourierKernel (t : ℝ) (v : R4) (p : nonnegEnergy.1) : ℂ :=
  Complex.exp (-(t : ℂ) * (energyOf p.1 : ℂ) + Complex.I * (dotR4 v (momentumOf p.1) : ℂ))
end SpectralPoint
namespace EuclidFunctionalWithRecon
open SpectralPoint
variable {c : SharpScale} {S : ConnFamily}
def withRecon (σ : EuclidFunctionalWithRecon c S) {ℋ : Type}
    [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] (R : OSReconstruction ℋ S) :
    EuclidFunctionalWithRecon c S where
  symm := σ.symm
  invariant := σ.invariant
  positive := σ.positive
  clusterConst := σ.clusterConst
  cluster := σ.cluster
  space := ℋ
  recon := R
theorem withRecon_self (σ : EuclidFunctionalWithRecon c S) :
    σ.withRecon σ.recon = σ :=
  rfl
variable (σ : EuclidFunctionalWithRecon c S)
def heatSemigroup (t : ℝ) : σ.space →L[ℂ] σ.space :=
  ResolvedOps.expComplex σ.recon.ham (t : ℂ)
def translOp (v : R4) : σ.space →L[ℂ] σ.space :=
  spatialTranslOp σ.jointMeasure v
def SpectralGeneratorsAndKernel : Prop :=
  SpectralTheorem.IsSpectralIntegralOf σ.recon.ham σ.jointMeasure
      (fun p => ((SpectralPoint.energyOf p : ℝ) : ℂ)) ∧
    (∀ j : Fin 3, SpectralTheorem.IsSpectralIntegralOf (σ.recon.mom j) σ.jointMeasure
      (fun p => ((SpectralPoint.momentumOf p j : ℝ) : ℂ))) ∧
    σ.jointMeasure.IsCarriedBy SpectralPoint.nonnegEnergy ∧
    ∀ t : ℝ, 0 ≤ t → ∀ v ∈ spatialVecs,
      σ.heatSemigroup t * σ.translOp v =
          σ.translOp v * σ.heatSemigroup t ∧
        σ.heatSemigroup t * σ.translOp v =
          σ.jointMeasure.integralOpOn SpectralPoint.nonnegEnergy (laplaceFourierKernel t v)
def TranslUnitaryGroup : Prop :=
  (∀ v ∈ spatialVecs,
    OperatorTransport.IsUnitaryMap (σ.translOp v : σ.space →ₗ[ℂ] σ.space)) ∧
    σ.translOp 0 = 1 ∧
    (∀ v ∈ spatialVecs, ∀ v' ∈ spatialVecs,
      σ.translOp v * σ.translOp v' = σ.translOp (v + v')) ∧
    (∀ v ∈ spatialVecs, OperatorTransport.IsBoundedAdjoint (σ.translOp (-v)) (σ.translOp v)) ∧
    (∀ ψ : σ.space, Continuous fun v : spatialVecs => σ.translOp v ψ) ∧
    (∀ v ∈ spatialVecs, σ.translOp v =
      SelfAdjointFunctions.expI (σ.recon.mom 0) (v 0) *
        SelfAdjointFunctions.expI (σ.recon.mom 1) (v 1) *
          SelfAdjointFunctions.expI (σ.recon.mom 2) (v 2)) ∧
    ∀ n : Fin 3 → ℝ, IsUnitVec3 n →
      ResolvedOps.IsDiagonalized (σ.dirMomentum n) ∧
        OperatorTransport.IsSelfAdjointUnbounded (σ.dirMomentum n) ∧
        ∀ s : ℝ, σ.translOp (spatialEmbed (s • n)) =
          SelfAdjointFunctions.expI (σ.dirMomentum n) s
def SpectralMeasureUniqueness : Prop :=
  ∀ (𝒦 : Type) [NormedAddCommGroup 𝒦] [InnerProductSpace ℂ 𝒦] [CompleteSpace 𝒦]
    (V : σ.space →ₗ[ℂ] 𝒦) (hV : OperatorTransport.IsUnitaryMap V)
    (E' : BorelSpectral.SpectralMeasure EMPoints 𝒦),
    E'.IsCarriedBy SpectralPoint.nonnegEnergy →
    (∀ k : ℕ, ∀ v ∈ spatialVecs,
      (E'.integralOpOn SpectralPoint.nonnegEnergy (laplaceFourierKernel k v) : 𝒦 →ₗ[ℂ] 𝒦) =
        V ∘ₗ (σ.heatSemigroup k : σ.space →ₗ[ℂ] σ.space) ∘ₗ
          (σ.translOp v : σ.space →ₗ[ℂ] σ.space) ∘ₗ hV.inv) →
    ∀ Δ, (E' Δ : 𝒦 →ₗ[ℂ] 𝒦) = σ.jointMeasure.unitaryPushforward hV Δ
def VacuumInvariance : Prop :=
  ‖σ.recon.vac‖ = 1 ∧
    (∀ t : ℝ, 0 ≤ t → σ.heatSemigroup t σ.recon.vac = σ.recon.vac) ∧
    (∀ v ∈ spatialVecs,
      σ.translOp v σ.recon.vac = σ.recon.vac) ∧
    (∀ w : timeStabilizer,
      σ.recon.rotOp w σ.recon.vac = σ.recon.vac) ∧
    σ.spectralMeasureAt σ.recon.vac = Measure.dirac ⟨0, mem_univ _⟩ ∧
    (∃ h : σ.recon.vac ∈ σ.recon.ham.domain,
      σ.recon.ham ⟨σ.recon.vac, h⟩ = 0) ∧
    ∀ j : Fin 3, ∃ h : σ.recon.vac ∈ (σ.recon.mom j).domain,
      σ.recon.mom j ⟨σ.recon.vac, h⟩ = 0
def RotationCovariance : Prop :=
  (∀ t : ℝ, 0 ≤ t → ∀ w : timeStabilizer,
    σ.recon.rotOp w ∘ₗ
        (σ.heatSemigroup t : σ.space →ₗ[ℂ] σ.space) =
      (σ.heatSemigroup t : σ.space →ₗ[ℂ] σ.space) ∘ₗ
        σ.recon.rotOp w) ∧
    (∀ (w : timeStabilizer), ∀ v ∈ spatialVecs,
      σ.recon.rotOp w ∘ₗ
          (σ.translOp v : σ.space →ₗ[ℂ] σ.space) ∘ₗ
            (σ.recon.rotOp_unitary w).inv =
        (σ.translOp ((w : EuclidMotion) v) : σ.space →ₗ[ℂ] σ.space)) ∧
    (∀ w w' : timeStabilizer,
      σ.recon.rotOp w ∘ₗ σ.recon.rotOp w' =
        σ.recon.rotOp (w * w')) ∧
    (∀ (w : timeStabilizer) (Δ : BorelSpectral.BorelSubsets EMPoints),
      ∃ h : MeasurableSet (rotPoint w '' Δ.1),
        σ.jointMeasure.unitaryPushforward (σ.recon.rotOp_unitary w) Δ =
          (σ.jointMeasure ⟨rotPoint w '' Δ.1, h⟩ :
            σ.space →ₗ[ℂ] σ.space)) ∧
    (∀ w : timeStabilizer,
      OperatorTransport.conjOp (σ.recon.rotOp_unitary w)
        σ.recon.ham = σ.recon.ham) ∧
    ∀ (w : timeStabilizer) (n : Fin 3 → ℝ), IsUnitVec3 n →
      OperatorTransport.conjOp (σ.recon.rotOp_unitary w)
        (σ.dirMomentum n) = σ.dirMomentum (rotSpatial w n)
end EuclidFunctionalWithRecon
def ReconstructionBasicFacts : Prop :=
  ∀ (c : SharpScale) (S : ConnFamily) (σ : EuclidFunctionalWithRecon c S) (ℋ : Type)
    [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] (R : OSReconstruction ℋ S),
    (σ.withRecon R).SpectralGeneratorsAndKernel ∧
      (σ.withRecon R).TranslUnitaryGroup ∧
      (σ.withRecon R).SpectralMeasureUniqueness ∧
      (σ.withRecon R).VacuumInvariance ∧
      (σ.withRecon R).RotationCovariance
end YangMills.Construction.EuclideanFunctionals
