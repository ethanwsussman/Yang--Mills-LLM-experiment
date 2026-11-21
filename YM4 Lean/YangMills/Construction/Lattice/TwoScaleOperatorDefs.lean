import YangMills.Construction.Lattice.PeriodicTorus
import Mathlib
set_option autoImplicit false
open Finset
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open ScaledFun
variable {d N : ℕ}
def linksMeeting {s : Mesh N} (X : Set (GridPoint d s)) : Set (Link d s) :=
  {e | Link.source e ∈ X ∨ Link.target e ∈ X}
def linksAvoiding {s : Mesh N} (X : Set (GridPoint d s)) : Set (Link d s) :=
  {e | Link.source e ∉ X ∧ Link.target e ∉ X}
open Classical in
def oneFormRestrict {s : Mesh N} (X : Set (Link d s)) : OneForm d s →ₗ[ℝ] OneForm d s where
  toFun A := ofMap fun e => if e ∈ X then A e else 0
  map_add' A B := ScaledFun.ext fun e => by
    by_cases h : e ∈ X <;> simp [h]
  map_smul' c A := ScaledFun.ext fun e => by
    by_cases h : e ∈ X <;> simp [h]
namespace Scales
variable {L j : ℕ} (S : Scales d L j N) (Λ' : Set (GridPoint d S.coarseMesh))
def coarseRegion : Set (GridPoint d S.unitMesh) :=
  ⋃ y' ∈ Λ', (S.coarseCell y' : Set (GridPoint d S.unitMesh))
def constrainedSiteFuns : Submodule ℝ (SiteFun d S.fineMesh) where
  carrier := {f | (∀ y, y ∉ S.coarseRegion Λ' → S.fineSiteAverage f y = 0) ∧
    ∀ y' ∈ Λ', S.coarseSiteAverage (S.fineSiteAverage f) y' = 0}
  add_mem' {f g} hf hg := ⟨fun y hy => by simp [hf.1 y hy, hg.1 y hy],
    fun y' hy' => by simp [hf.2 y' hy', hg.2 y' hy']⟩
  zero_mem' := ⟨fun y _ => by simp; rfl, fun y' _ => by simp; rfl⟩
  smul_mem' c f hf := ⟨fun y hy => by simp [hf.1 y hy],
    fun y' hy' => by simp [hf.2 y' hy']⟩
def twoScaleQuadOp : OneForm d S.unitMesh →ₗ[ℝ] OneForm d S.unitMesh :=
  oneFormRestrict (linksAvoiding (S.coarseRegion Λ')) +
    ((L : ℝ) ^ 2)⁻¹ • (LinearMap.adjoint S.coarseFormAverage ∘ₗ oneFormRestrict (linksMeeting Λ') ∘ₗ
      S.coarseFormAverage)
def gaugeProj : SiteFun d S.fineMesh →ₗ[ℝ] SiteFun d S.fineMesh :=
  (((S.constrainedSiteFuns Λ').map (discreteLaplacian S.fineMesh)).starProjection :
    SiteFun d S.fineMesh →ₗ[ℝ] SiteFun d S.fineMesh)
def gaugeProjCompl : SiteFun d S.fineMesh →ₗ[ℝ] SiteFun d S.fineMesh :=
  LinearMap.id - S.gaugeProj Λ'
def averagedPenalty (a : ℝ) : OneForm d S.fineMesh →ₗ[ℝ] OneForm d S.fineMesh :=
  a • (LinearMap.adjoint S.fineFormAverage ∘ₗ S.twoScaleQuadOp Λ' ∘ₗ S.fineFormAverage)
def twoScaleOp (a : ℝ) : OneForm d S.fineMesh →ₗ[ℝ] OneForm d S.fineMesh :=
  LinearMap.adjoint (discreteCurl S.fineMesh) ∘ₗ discreteCurl S.fineMesh +
    discreteGrad S.fineMesh ∘ₗ S.gaugeProj Λ' ∘ₗ LinearMap.adjoint (discreteGrad S.fineMesh) +
    S.averagedPenalty Λ' a
def twoScaleOpInv (a : ℝ) (h : IsUnit (S.twoScaleOp Λ' a : Module.End ℝ (OneForm d S.fineMesh))) :
    Module.End ℝ (OneForm d S.fineMesh) :=
  ↑h.unit⁻¹
def singleScaleGaugeProj : SiteFun d S.fineMesh →ₗ[ℝ] SiteFun d S.fineMesh := S.gaugeProj ∅
def singleScaleGaugeProjCompl : SiteFun d S.fineMesh →ₗ[ℝ] SiteFun d S.fineMesh :=
  LinearMap.id - S.singleScaleGaugeProj
def singleScaleGaugeOp : OneForm d S.fineMesh →ₗ[ℝ] OneForm d S.fineMesh :=
  LinearMap.adjoint (discreteCurl S.fineMesh) ∘ₗ discreteCurl S.fineMesh +
    discreteGrad S.fineMesh ∘ₗ S.singleScaleGaugeProj ∘ₗ LinearMap.adjoint (discreteGrad S.fineMesh)
def singleScaleOp (a : ℝ) : OneForm d S.fineMesh →ₗ[ℝ] OneForm d S.fineMesh :=
  S.singleScaleGaugeOp +
    a • (LinearMap.adjoint S.fineFormAverage ∘ₗ S.fineFormAverage)
end Scales
end YangMills.Construction.PeriodicLattice
