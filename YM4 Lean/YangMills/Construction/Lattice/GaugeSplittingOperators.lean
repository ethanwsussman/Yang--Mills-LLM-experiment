import YangMills.Construction.Lattice.DecayingKernels
import YangMills.Construction.Lattice.TwoScaleOperatorDefs
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open ScaledFun
variable {d N : ℕ}
namespace Scales
variable {L j : ℕ} (S : Scales d L j N) (Λ' : Set (GridPoint d S.coarseMesh))
def IsLaplacianMinimalExtension (φ : SiteFun d S.unitMesh) (l : SiteFun d S.fineMesh) : Prop :=
  S.fineSiteAverage l = φ ∧
    ∀ l' : SiteFun d S.fineMesh, S.fineSiteAverage l' = φ →
      ‖discreteLaplacian S.fineMesh l‖ ^ 2 ≤ ‖discreteLaplacian S.fineMesh l'‖ ^ 2
def harmonicExtension : SiteFun d S.unitMesh →ₗ[ℝ] SiteFun d S.fineMesh :=
  Classical.epsilon fun H => ∀ φ, S.IsLaplacianMinimalExtension φ (H φ)
def laplacianHarmonicExtension : SiteFun d S.unitMesh →ₗ[ℝ] SiteFun d S.fineMesh :=
  discreteLaplacian S.fineMesh ∘ₗ S.harmonicExtension
def extensionEnergyOp : SiteFun d S.unitMesh →ₗ[ℝ] SiteFun d S.unitMesh :=
  LinearMap.adjoint S.laplacianHarmonicExtension ∘ₗ S.laplacianHarmonicExtension
def gaugeParamSpace : Submodule ℝ (SiteFun d S.unitMesh) where
  carrier := {ω | (∀ y, y ∉ S.coarseRegion Λ' → ω y = 0) ∧ S.coarseSiteAverage ω = 0}
  add_mem' {f g} hf hg := ⟨fun y hy => by simp [hf.1 y hy, hg.1 y hy], by
    rw [map_add, hf.2, hg.2, add_zero]⟩
  zero_mem' := ⟨fun _ _ => rfl, map_zero _⟩
  smul_mem' c f hf := ⟨fun y hy => by simp [hf.1 y hy], by rw [map_smul, hf.2, smul_zero]⟩
def gaugeParamCovariance : SiteFun d S.unitMesh →ₗ[ℝ] SiteFun d S.unitMesh :=
  subspaceInverse (S.gaugeParamSpace Λ') S.extensionEnergyOp
def axialGaugeForms : Submodule ℝ (OneForm d S.unitMesh) where
  carrier := {B | ∀ y' ∈ Λ', ∀ b ∈ S.treeLinks y', B b = 0}
  add_mem' {f g} hf hg y' hy b hb := by simp [hf y' hy b hb, hg y' hy b hb]
  zero_mem' _ _ _ _ := rfl
  smul_mem' c f hf y' hy b hb := by simp [hf y' hy b hb]
def singleScaleOpRingInv (a : ℝ) : Module.End ℝ (OneForm d S.fineMesh) :=
  Ring.inverse (S.singleScaleOp a : Module.End ℝ (OneForm d S.fineMesh))
def constrainedCovariance : OneForm d S.fineMesh →ₗ[ℝ] OneForm d S.fineMesh :=
  subspaceInverse (LinearMap.ker S.fineFormAverage) S.singleScaleGaugeOp
def IsEnergyMinimalFormExtension (B : OneForm d S.unitMesh) (A : OneForm d S.fineMesh) : Prop :=
  S.fineFormAverage A = B ∧
    ∀ A' : OneForm d S.fineMesh, S.fineFormAverage A' = B →
      inner ℝ A (S.singleScaleGaugeOp A) ≤ inner ℝ A' (S.singleScaleGaugeOp A')
def formExtension : OneForm d S.unitMesh →ₗ[ℝ] OneForm d S.fineMesh :=
  Classical.epsilon fun H => ∀ B, S.IsEnergyMinimalFormExtension B (H B)
def blockEnergyOp : OneForm d S.unitMesh →ₗ[ℝ] OneForm d S.unitMesh :=
  LinearMap.adjoint S.formExtension ∘ₗ S.singleScaleGaugeOp ∘ₗ S.formExtension
def averagedResolvent (a : ℝ) : Module.End ℝ (OneForm d S.unitMesh) :=
  S.fineFormAverage ∘ₗ S.singleScaleOpRingInv a ∘ₗ LinearMap.adjoint S.fineFormAverage
def averagedResolventInv (a : ℝ) : Module.End ℝ (OneForm d S.unitMesh) :=
  Ring.inverse (S.averagedResolvent a)
def axialQuadOp (a : ℝ) : OneForm d S.unitMesh →ₗ[ℝ] OneForm d S.unitMesh :=
  a • S.twoScaleQuadOp Λ' + S.blockEnergyOp
def axialGaugeCovariance (a : ℝ) : OneForm d S.unitMesh →ₗ[ℝ] OneForm d S.unitMesh :=
  subspaceInverse (S.axialGaugeForms Λ') (S.axialQuadOp Λ' a)
end Scales
def axialCoercivityConst (d L : ℕ) : ℝ :=
  (1 + 12 * (d : ℝ) ^ 2 * (8 * d + 3) * (L : ℝ) ^ (d + 1))⁻¹
namespace Scales
variable {L j : ℕ} (S : Scales d L j N) (Λ' : Set (GridPoint d S.coarseMesh))
end Scales
end YangMills.Construction.PeriodicLattice
