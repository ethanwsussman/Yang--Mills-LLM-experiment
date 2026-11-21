import YangMills.Construction.MirrorGridsOfEverySide.ActionOnTheCellAlgebrasAtEveryMirrorGrid
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open InfiniteLattice (AmbientSpace)
open ChessboardTori (ReflectionGrid)
namespace MirrorGridsAllSides
namespace GroupAction
variable {D : GridSetup} (g : ReflectionGrid D)
theorem actOn_mul (r s : g.reflectionGroup) (F : D.GaugeField → ℂ) :
    (g.toLatticeSym (r * s)).actOn F =
      (g.toLatticeSym r).actOn ((g.toLatticeSym s).actOn F) := by
  funext U
  change F ((g.toLatticeSym (r * s)).pullbackField U) =
    F ((g.toLatticeSym s).pullbackField ((g.toLatticeSym r).pullbackField U))
  congr 1
theorem actOn_one (F : D.GaugeField → ℂ) :
    (g.toLatticeSym 1).actOn F = F := by
  funext U
  change F ((g.toLatticeSym 1).pullbackField U) = F U
  congr 1
theorem continuous_reflect (μ : Fin 4) (k : ℤ) : Continuous (g.reflect μ k) := by
  have h : g.reflect μ k = fun x : AmbientSpace =>
      x - (2 * (x μ - g.origin μ - k * g.cellSide)) • ChessboardTori.coordVec μ := rfl
  rw [h]
  fun_prop
theorem continuous_of_mem_reflectionGroup {r : Equiv.Perm AmbientSpace} (hr : r ∈ g.reflectionGroup) :
    Continuous r ∧ Continuous (r⁻¹ : Equiv.Perm AmbientSpace) := by
  induction hr using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨⟨μ, k⟩, rfl⟩ := hx
    exact ⟨continuous_reflect g μ k, continuous_reflect g μ k⟩
  | one => exact ⟨continuous_id, continuous_id⟩
  | mul x y _ _ hx hy =>
    refine ⟨hx.1.comp hy.1, ?_⟩
    rw [mul_inv_rev]
    exact hy.2.comp hx.2
  | inv x _ hx =>
    refine ⟨hx.2, ?_⟩
    rw [inv_inv]
    exact hx.1
def toHomeomorph (r : g.reflectionGroup) : AmbientSpace ≃ₜ AmbientSpace where
  toEquiv := r.1
  continuous_toFun := (continuous_of_mem_reflectionGroup g r.2).1
  continuous_invFun := (continuous_of_mem_reflectionGroup g r.2).2
theorem image_interior_eq (r : g.reflectionGroup) (S : Set AmbientSpace) :
    r.1 '' interior S = interior (r.1 '' S) :=
  (toHomeomorph g r).image_interior S
theorem linkMap_mem_interiorLinks (r : g.reflectionGroup) {S : Set AmbientSpace} {b : D.Link}
    (hb : b ∈ ReflectionGrid.interiorLinks (D := D) S) :
    (g.toLatticeSym r).linkMap b ∈ ReflectionGrid.interiorLinks (D := D) (r.1 '' S) := by
  change (((g.toLatticeSym r).linkMap b).initial : AmbientSpace) ∈ interior (r.1 '' S) ∧
    (((g.toLatticeSym r).linkMap b).terminal : AmbientSpace) ∈ interior (r.1 '' S)
  rw [← image_interior_eq]
  exact ⟨⟨_, hb.1, rfl⟩, ⟨_, hb.2, rfl⟩⟩
theorem actOn_mem_cellObservables (r : g.reflectionGroup) {S : Set AmbientSpace} {F : D.GaugeField → ℂ}
    (hF : F ∈ ReflectionGrid.cellObservables (D := D) S) :
    (g.toLatticeSym r).actOn F ∈ ReflectionGrid.cellObservables (D := D) (r.1 '' S) := by
  obtain ⟨f, hf, ⟨C, hC⟩, rfl⟩ := hF
  refine ⟨fun u => f fun b => u ⟨(g.toLatticeSym r).linkMap b.1,
    linkMap_mem_interiorLinks g r b.2⟩, ?_, ⟨C, fun u => hC _⟩, rfl⟩
  exact hf.comp (measurable_pi_lambda _ fun b => measurable_pi_apply _)
end GroupAction
open GroupAction in
theorem allGridsActOnCellObservables_holds : AllGridsActOnCellObservables := by
  intro D g _
  refine ⟨fun r s F => actOn_mul g r s F, fun r S _ => ⟨?_, ?_⟩⟩
  · apply Subset.antisymm
    · rintro _ ⟨F, hF, rfl⟩
      exact actOn_mem_cellObservables g r hF
    · intro F' hF'
      have h := actOn_mem_cellObservables g r⁻¹ hF'
      have hS : (r⁻¹ : g.reflectionGroup).1 '' (r.1 '' S) = S := by
        have hc : (⇑(r⁻¹ : g.reflectionGroup).1 ∘ ⇑r.1 : AmbientSpace → AmbientSpace) = id := by
          funext x
          exact (r.1).symm_apply_apply x
        rw [← image_comp, hc, image_id]
      rw [hS] at h
      refine ⟨_, h, ?_⟩
      rw [← actOn_mul, mul_inv_cancel, actOn_one]
  · intro F _ F' _ c
    exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
end MirrorGridsAllSides
end YangMills.Construction
end
