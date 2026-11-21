import YangMills.Construction.Lattice.GaugeSplittingOperators
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open ScaledFun
variable {d N : ℕ}
namespace Scales
variable {L j : ℕ} (S : Scales d L j N) (Λ' : Set (GridPoint d S.coarseMesh))
def splittingCoordMap :
    (LinearMap.ker S.fineFormAverage × S.axialGaugeForms Λ' × S.gaugeParamSpace Λ') →ₗ[ℝ]
      OneForm d S.fineMesh :=
  (LinearMap.ker S.fineFormAverage).subtype.coprod
    ((S.formExtension ∘ₗ (S.axialGaugeForms Λ').subtype).coprod
      (-(discreteGrad S.fineMesh ∘ₗ S.harmonicExtension ∘ₗ (S.gaugeParamSpace Λ').subtype)))
def gaugeShift (A₀ : OneForm d S.fineMesh) : SiteFun d S.unitMesh :=
  S.gaugeParamCovariance Λ' (LinearMap.adjoint S.harmonicExtension
    (discreteLaplacian S.fineMesh (LinearMap.adjoint (discreteGrad S.fineMesh) A₀)))
def gaugeBlock : OneForm d S.fineMesh →ₗ[ℝ] OneForm d S.fineMesh :=
  discreteGrad S.fineMesh ∘ₗ S.harmonicExtension ∘ₗ S.gaugeParamCovariance Λ' ∘ₗ
    LinearMap.adjoint S.harmonicExtension ∘ₗ LinearMap.adjoint (discreteGrad S.fineMesh)
def gaugeCorrectionOp : OneForm d S.fineMesh →ₗ[ℝ] OneForm d S.fineMesh :=
  discreteGrad S.fineMesh ∘ₗ S.laplacianHarmonicExtension ∘ₗ S.gaugeParamCovariance Λ' ∘ₗ
    LinearMap.adjoint S.harmonicExtension ∘ₗ LinearMap.adjoint (discreteGrad S.fineMesh)
def centralCovariance : OneForm d S.fineMesh →ₗ[ℝ] OneForm d S.fineMesh :=
  S.constrainedCovariance +
    S.formExtension ∘ₗ S.axialGaugeCovariance Λ' 1 ∘ₗ LinearMap.adjoint S.formExtension
def resolventRepresentation : OneForm d S.fineMesh →ₗ[ℝ] OneForm d S.fineMesh :=
  S.gaugeBlock Λ' +
    LinearMap.adjoint (LinearMap.id - S.gaugeCorrectionOp Λ') ∘ₗ S.centralCovariance Λ' ∘ₗ
      (LinearMap.id - S.gaugeCorrectionOp Λ')
end Scales
end YangMills.Construction.PeriodicLattice
