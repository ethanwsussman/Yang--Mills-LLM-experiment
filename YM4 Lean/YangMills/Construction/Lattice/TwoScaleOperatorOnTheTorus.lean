import YangMills.Construction.Lattice.LocalizedDecayBounds
import YangMills.Construction.Lattice.TwoScaleResolventRepresentation
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open ScaledFun
variable {d N : ℕ}
namespace Scales
variable {L j : ℕ} (S : Scales d L j N) (Λ' : Set (GridPoint d S.coarseMesh))
def twoScaleOpGaugeFixed : OneForm d S.fineMesh →ₗ[ℝ] OneForm d S.fineMesh :=
  fieldLaplacian S.fineMesh (Fin d) -
    discreteGrad S.fineMesh ∘ₗ S.gaugeProjCompl Λ' ∘ₗ LinearMap.adjoint (discreteGrad S.fineMesh) +
    S.averagedPenalty Λ' 1
structure TwoScaleRepresentationProps (δ c : ℝ) : Prop where
  opInv_eq : ∀ h : IsUnit (S.twoScaleOp Λ' 1 : Module.End ℝ (OneForm d S.fineMesh)),
    S.twoScaleOpInv Λ' 1 h = S.resolventRepresentation Λ'
  formExtension_eq : S.formExtension =
    S.singleScaleOpRingInv 1 ∘ₗ LinearMap.adjoint S.fineFormAverage ∘ₗ S.averagedResolventInv 1
  constrainedCovariance_eq : S.constrainedCovariance = S.singleScaleOpRingInv 1 -
    S.singleScaleOpRingInv 1 ∘ₗ LinearMap.adjoint S.fineFormAverage ∘ₗ S.averagedResolventInv 1 ∘ₗ
      S.fineFormAverage ∘ₗ S.singleScaleOpRingInv 1
  gaugeParamCovariance_norm_le : ∀ φ : SiteFun d S.unitMesh,
    ‖S.gaugeParamCovariance Λ' φ‖ ≤ 1 / 16 * (d : ℝ) * (L : ℝ) ^ 4 * ‖φ‖
  axialGaugeCovariance_norm_le : ∀ B : OneForm d S.unitMesh,
    ‖S.axialGaugeCovariance Λ' 1 B‖ ≤ 1 / axialCoercivityConst d L * ‖B‖
  gaugeParamCovariance_mem : S.gaugeParamCovariance Λ' ∈
    (expDecayClass δ c : Set (SiteFun d S.unitMesh →ₗ[ℝ] SiteFun d S.unitMesh))
  axialGaugeCovariance_mem : S.axialGaugeCovariance Λ' 1 ∈
    (expDecayClass δ c : Set (OneForm d S.unitMesh →ₗ[ℝ] OneForm d S.unitMesh))
  averagedResolventInv_mem :
    (S.averagedResolventInv 1 : OneForm d S.unitMesh →ₗ[ℝ] OneForm d S.unitMesh) ∈
      (expDecayClass δ c : Set (OneForm d S.unitMesh →ₗ[ℝ] OneForm d S.unitMesh))
  blockEnergyOp_mem : S.blockEnergyOp ∈
    (expDecayClass δ c : Set (OneForm d S.unitMesh →ₗ[ℝ] OneForm d S.unitMesh))
  extensionEnergyOp_mem : S.extensionEnergyOp ∈
    (expDecayClass δ c : Set (SiteFun d S.unitMesh →ₗ[ℝ] SiteFun d S.unitMesh))
structure TwoScaleConclusions (δ c : ℝ) (k : DecayConstants) : Prop where
  twoScaleOp_pos : ∀ A : OneForm d S.fineMesh, A ≠ 0 → 0 < inner ℝ A (S.twoScaleOp Λ' 1 A)
  isUnit_twoScaleOp : IsUnit (S.twoScaleOp Λ' 1 : Module.End ℝ (OneForm d S.fineMesh))
  twoScaleOpInv_eq_ringInverse :
    ∀ h : IsUnit (S.twoScaleOp Λ' 1 : Module.End ℝ (OneForm d S.fineMesh)),
      S.twoScaleOpInv Λ' 1 h =
        Ring.inverse (S.twoScaleOpGaugeFixed Λ' : Module.End ℝ (OneForm d S.fineMesh))
  twoScaleOpInv_isSymmetric :
    ∀ h : IsUnit (S.twoScaleOp Λ' 1 : Module.End ℝ (OneForm d S.fineMesh)),
      LinearMap.IsSymmetric (S.twoScaleOpInv Λ' 1 h)
  twoScaleOpInv_pos :
    ∀ (h : IsUnit (S.twoScaleOp Λ' 1 : Module.End ℝ (OneForm d S.fineMesh)))
      (A : OneForm d S.fineMesh), A ≠ 0 → 0 < inner ℝ A (S.twoScaleOpInv Λ' 1 h A)
  representation : S.TwoScaleRepresentationProps Λ' δ c
  localizedDecay : ∀ h : IsUnit (S.twoScaleOp Λ' 1 : Module.End ℝ (OneForm d S.fineMesh)),
    S.HasLocalizedDecay δ k (S.twoScaleOpInv Λ' 1 h)
end Scales
instance decayConstants_nonempty : Nonempty DecayConstants :=
  ⟨{ base := 1
     holder := fun _ => 1
     grad := fun _ => 1
     gradHolder := fun _ _ => 1
     base_pos := one_pos
     holder_pos := fun _ _ _ => one_pos
     grad_pos := fun _ _ _ => one_pos
     gradHolder_pos := fun _ _ _ _ _ => one_pos }⟩
structure TwoScaleUniformConstants (d L : ℕ) (δ c : ℝ) (k : DecayConstants) : Prop where
  rate_pos : 0 < δ
  bound_pos : 0 < c
  conclusions : ∀ (j N : ℕ) (S : Scales d L j N) (Λ' : Set (GridPoint d S.coarseMesh)),
    S.TwoScaleConclusions Λ' δ c k
def twoScaleConstants (d L : ℕ) : ℝ × ℝ × DecayConstants :=
  Classical.epsilon fun p => TwoScaleUniformConstants d L p.1 p.2.1 p.2.2
def twoScaleDecayRate (d L : ℕ) : ℝ := (twoScaleConstants d L).1
def twoScaleNormBound (d L : ℕ) : ℝ := (twoScaleConstants d L).2.1
end YangMills.Construction.PeriodicLattice
