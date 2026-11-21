import YangMills.Construction.Torus.FormsAveragesAndOperatorsOnAGeneralTorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.GeneralTorus
structure IsInnerProductForm {V : Type*} [AddCommGroup V] [Module ℝ V] (p : V → V → ℝ) : Prop where
  add_left : ∀ u v w, p (u + v) w = p u w + p v w
  smul_left : ∀ (r : ℝ) u v, p (r • u) v = r * p u v
  symm : ∀ u v, p u v = p v u
  pos : ∀ v, v ≠ 0 → 0 < p v v
namespace IsInnerProductForm
variable {V : Type*} [AddCommGroup V] [Module ℝ V] {p : V → V → ℝ} (hform : IsInnerProductForm p)
include hform
theorem add_right (x y z : V) : p x (y + z) = p x y + p x z := by
  rw [hform.symm, hform.add_left, hform.symm y, hform.symm z]
theorem smul_right (c : ℝ) (x y : V) : p x (c • y) = c * p x y := by
  rw [hform.symm, hform.smul_left, hform.symm y]
theorem zero_left (y : V) : p 0 y = 0 := by
  have key := hform.smul_left 0 0 y
  simpa using key
theorem zero_right (y : V) : p y 0 = 0 := by
  rw [hform.symm, hform.zero_left]
theorem sub_left (x y z : V) : p (x - y) z = p x z - p y z := by
  have hsum := hform.add_left (x - y) y z
  rw [sub_add_cancel] at hsum
  linarith
theorem sub_right (x y z : V) : p x (y - z) = p x y - p x z := by
  rw [hform.symm, hform.sub_left, hform.symm y, hform.symm z]
theorem eq_zero_of_self_eq_zero (x : V) (hxx : p x x = 0) : x = 0 := by
  by_contra hne
  exact (hform.pos x hne).ne' hxx
end IsInnerProductForm
namespace InnerProductsAdjointsProjections
def SettingInnerProductFacts : Prop :=
  ∀ S : GaugeSetting,
    Finite S.CoarseBond ∧
    IsInnerProductForm S.data.siteInner ∧
    IsInnerProductForm S.data.bondInner ∧
    IsInnerProductForm S.coarseInner ∧
    IsInnerProductForm S.chain.dirichletInner ∧
    IsInnerProductForm S.formInner ∧
    IsAdjointFor S.data.siteInner S.data.bondInner S.data.grad S.data.gradAdjoint ∧
    IsAdjointFor S.formInner S.coarseInner S.meanOp S.meanOpAdjoint ∧
    IsOrthProjFor S.data.siteInner S.chain.dirichletSites S.chain.siteProj ∧
    IsOrthProjFor S.data.bondInner S.formSubspace S.formProj ∧
    ∀ E : Submodule ℝ ↥S.chain.dirichletSites,
      IsOrthProjFor S.chain.dirichletInner E
        (orthProjFor S.chain.dirichletInner E)
end InnerProductsAdjointsProjections
end YangMills.Construction.GeneralTorus
end
