import YangMills.Construction.Torus.SymmetricAndPositiveDefiniteOperatorsOnForms
import YangMills.Construction.Torus.QuadraticFormsAndMatricesOfTheAverages
import YangMills.Construction.Torus.ScalarProductsTransposesAndProjectionsOfASettingProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.GeneralTorus.ClosedFormsAndLaplacian
section Generic
variable {V U : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup U] [Module ℝ U]
structure IsInnerForm (p : V → V → ℝ) : Prop where
  add_left : ∀ u v w, p (u + v) w = p u w + p v w
  smul_left : ∀ (r : ℝ) u v, p (r • u) v = r * p u v
  symm : ∀ u v, p u v = p v u
  pos : ∀ v, v ≠ 0 → 0 < p v v
namespace IsInnerForm
variable {p : V → V → ℝ} (hp : IsInnerForm p)
include hp
theorem add_right (u v w : V) : p u (v + w) = p u v + p u w := by
  rw [hp.symm, hp.add_left, hp.symm v, hp.symm w]
theorem smul_right (r : ℝ) (u v : V) : p u (r • v) = r * p u v := by
  rw [hp.symm, hp.smul_left, hp.symm v]
theorem zero_left (v : V) : p 0 v = 0 := by
  have := hp.smul_left 0 0 v
  simpa using this
theorem zero_right (v : V) : p v 0 = 0 := by
  rw [hp.symm, hp.zero_left]
theorem sub_left (u v w : V) : p (u - v) w = p u w - p v w := by
  have h1 := hp.add_left (u - v) v w
  rw [sub_add_cancel] at h1
  linarith
theorem nonneg (v : V) : 0 ≤ p v v := by
  by_cases h : v = 0
  · rw [h, hp.zero_left]
  · exact (hp.pos v h).le
theorem eq_zero_of_self_eq_zero (v : V) (h : p v v = 0) : v = 0 := by
  by_contra hv
  exact (hp.pos v hv).ne' h
theorem restrict (E : Submodule ℝ V) : IsInnerForm (fun a b : ↥E => p a b) where
  add_left u v w := by simpa using hp.add_left u v w
  smul_left r u v := by simpa using hp.smul_left r u v
  symm u v := hp.symm u v
  pos v hv := hp.pos v (by simpa using hv)
end IsInnerForm
theorem exists_isAdjointFor [FiniteDimensional ℝ V] {p : V → V → ℝ} {q : U → U → ℝ}
    (hp : IsInnerForm p) (hq : IsInnerForm q) (K : V →ₗ[ℝ] U) :
    ∃ T : U →ₗ[ℝ] V, IsAdjointFor p q K T := by
  let Φ : V →ₗ[ℝ] Module.Dual ℝ V :=
    LinearMap.mk₂ ℝ p hp.add_left hp.smul_left hp.add_right hp.smul_right
  have hinj : Function.Injective Φ := by
    refine (injective_iff_map_eq_zero Φ).2 fun v hv => hp.eq_zero_of_self_eq_zero v ?_
    have : Φ v v = 0 := by rw [hv]; rfl
    exact this
  let e := LinearMap.linearEquivOfInjective Φ hinj (Subspace.dual_finrank_eq).symm
  let F : U →ₗ[ℝ] Module.Dual ℝ V :=
    LinearMap.mk₂ ℝ (fun u v => q (K v) u)
      (fun u u' v => hq.add_right _ _ _)
      (fun r u v => hq.smul_right _ _ _)
      (fun u v v' => by simp only [map_add]; exact hq.add_left _ _ _)
      (fun r u v => by simp only [map_smul]; exact hq.smul_left _ _ _)
  refine ⟨e.symm.toLinearMap ∘ₗ F, fun v u => ?_⟩
  have h : Φ (e.symm (F u)) = F u := e.apply_symm_apply (F u)
  have h2 : Φ (e.symm (F u)) v = F u v := by rw [h]
  have h3 : p (e.symm (F u)) v = q (K v) u := h2
  rw [← h3, hp.symm]
  rfl
end Generic
section Numbers
variable (D : ScaleData)
theorem levelSpacing_pos (n : ℕ) : 0 < D.levelSpacing n := by apply _root_.YangMills.Construction.GeneralTorus.ChainStructureProof.levelSpacing_pos <;> assumption
theorem finite_latticeBond {S σ : ℝ} [Finite (LatticeSite S σ)] : Finite (LatticeBond S σ) := by apply _root_.YangMills.Construction.GeneralTorus.RegionObjects.finite_latticeBond <;> assumption
theorem finite_latticePlaquette {S σ : ℝ} [Finite (LatticeSite S σ)] :
    Finite (LatticePlaquette S σ) := by apply _root_.YangMills.Construction.GeneralTorus.RegionObjects.finite_latticePlaquette <;> assumption
instance finiteBaseBond : Finite D.BaseBond :=
  have : Finite (D.BondAt 0) := finite_latticeBond
  Subtype.finite
instance finiteBasePlaquette : Finite D.BasePlaquette := finite_latticePlaquette
end Numbers
theorem finite_coarseBond (W : GaugeSetting) : Finite W.CoarseBond := by apply _root_.YangMills.Construction.GeneralTorus.InnerProductsAdjointsProjections.finite_coarseBond <;> assumption
section Form
variable (W : GaugeSetting)
end Form
end YangMills.Construction.GeneralTorus.ClosedFormsAndLaplacian
