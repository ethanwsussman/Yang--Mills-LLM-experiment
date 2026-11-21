import YangMills.Construction.Torus.ObjectsOfASequenceOfRegionsOnAGeneralTorusProof
import YangMills.Construction.Torus.ScalarProductsTransposesAndProjectionsOfASetting
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric
namespace GeneralTorus.InnerProductsAdjointsProjections
section Generic
variable {V U : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup U] [Module ℝ U]
theorem exists_isAdjointFor [FiniteDimensional ℝ V] {p : V → V → ℝ} {q : U → U → ℝ}
    (hp : IsInnerProductForm p) (hq : IsInnerProductForm q) (M : V →ₗ[ℝ] U) :
    ∃ T : U →ₗ[ℝ] V, IsAdjointFor p q M T := by
  let toDual : V →ₗ[ℝ] Module.Dual ℝ V :=
    LinearMap.mk₂ ℝ p hp.add_left hp.smul_left hp.add_right hp.smul_right
  have hinj : Function.Injective toDual := by
    refine (injective_iff_map_eq_zero toDual).2 fun x hx => hp.eq_zero_of_self_eq_zero x ?_
    exact show toDual x x = 0 from by rw [hx]; rfl
  let eqv := LinearMap.linearEquivOfInjective toDual hinj (Subspace.dual_finrank_eq).symm
  let G : U →ₗ[ℝ] Module.Dual ℝ V :=
    LinearMap.mk₂ ℝ (fun y x => q (M x) y)
      (fun y y' x => hq.add_right _ _ _)
      (fun c y x => hq.smul_right _ _ _)
      (fun y x x' => by simp only [map_add]; exact hq.add_left _ _ _)
      (fun c y x => by simp only [map_smul]; exact hq.smul_left _ _ _)
  refine ⟨eqv.symm.toLinearMap ∘ₗ G, fun x y => ?_⟩
  have h₁ : toDual (eqv.symm (G y)) = G y := eqv.apply_symm_apply (G y)
  have h₂ : toDual (eqv.symm (G y)) x = G y x := by rw [h₁]
  have h₃ : p (eqv.symm (G y)) x = q (M x) y := h₂
  rw [← h₃, hp.symm]
  rfl
end Generic
section Numbers
variable (D : ScaleData)
theorem levelSpacing_pos (n : ℕ) : 0 < D.levelSpacing n := by apply _root_.YangMills.Construction.GeneralTorus.ChainStructureProof.levelSpacing_pos <;> assumption
theorem isEvenMultipleOf_levelSpacing {n : ℕ} (h : n ≤ D.lastLevel) :
    IsEvenMultipleOf D.torusSide (D.levelSpacing n) := by apply _root_.YangMills.Construction.GeneralTorus.RegionObjects.isEvenMultipleOf_levelSpacing <;> assumption
theorem finite_latticeBond {S σ : ℝ} [Finite (LatticeSite S σ)] : Finite (LatticeBond S σ) := by apply _root_.YangMills.Construction.GeneralTorus.RegionObjects.finite_latticeBond <;> assumption
instance finite_baseBond : Finite D.BaseBond :=
  have : Finite (D.BondAt 0) := finite_latticeBond
  Subtype.finite
end Numbers
theorem finite_coarseBond (W : GaugeSetting) : Finite W.CoarseBond := by
  have h : ∀ n : Fin (W.data.lastLevel + 1), Finite ↥(W.coarseBondsAt n) := fun n => by
    have : Finite (W.data.SiteAt n) :=
      finite_latticeSite (isEvenMultipleOf_levelSpacing W.data (Nat.lt_succ_iff.1 n.2))
    have : Finite (W.data.BondAt n) := finite_latticeBond
    exact Subtype.finite
  infer_instance
end GeneralTorus.InnerProductsAdjointsProjections
end YangMills.Construction
end
