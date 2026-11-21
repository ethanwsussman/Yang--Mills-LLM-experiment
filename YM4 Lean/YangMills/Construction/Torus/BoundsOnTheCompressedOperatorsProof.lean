import YangMills.Construction.SeparatedSequences.ExplicitConstants
import YangMills.Construction.Torus.SymmetricAndPositiveDefiniteOperatorsOnForms
import YangMills.Construction.Torus.DifferencesAndAveragesOnAGeneralTorus
import YangMills.Construction.Torus.QuadraticFormsAndMatricesOfTheAverages
import YangMills.Construction.Torus.ScalarProductsTransposesAndProjectionsOfASettingProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.GeneralTorus.CompressedBoundsProof
section Generic
variable {V U : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup U] [Module ℝ U]
structure IsRealInnerForm (p : V → V → ℝ) : Prop where
  add_left : ∀ u v w, p (u + v) w = p u w + p v w
  smul_left : ∀ (r : ℝ) u v, p (r • u) v = r * p u v
  symm : ∀ u v, p u v = p v u
  pos : ∀ v, v ≠ 0 → 0 < p v v
namespace IsRealInnerForm
variable {p : V → V → ℝ} (hp : IsRealInnerForm p)
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
theorem sub_right (u v w : V) : p u (v - w) = p u v - p u w := by
  rw [hp.symm, hp.sub_left, hp.symm v, hp.symm w]
theorem nonneg (v : V) : 0 ≤ p v v := by
  by_cases h : v = 0
  · rw [h, hp.zero_left]
  · exact (hp.pos v h).le
theorem eq_zero_of_self_eq_zero (v : V) (h : p v v = 0) : v = 0 := by
  by_contra hv
  exact (hp.pos v hv).ne' h
theorem restrictSubmodule (E : Submodule ℝ V) : IsRealInnerForm (fun a b : ↥E => p a b) where
  add_left u v w := by simpa using hp.add_left u v w
  smul_left r u v := by simpa using hp.smul_left r u v
  symm u v := hp.symm u v
  pos v hv := hp.pos v (by simpa using hv)
end IsRealInnerForm
end Generic
section Numbers
variable (D : ScaleData)
theorem levelSpacing_pos (n : ℕ) : 0 < D.levelSpacing n := by apply _root_.YangMills.Construction.GeneralTorus.ChainStructureProof.levelSpacing_pos <;> assumption
theorem finite_latticeBond {S σ : ℝ} [Finite (LatticeSite S σ)] : Finite (LatticeBond S σ) := by apply _root_.YangMills.Construction.GeneralTorus.RegionObjects.finite_latticeBond <;> assumption
end Numbers
section SeriesExpansions
variable (W : GaugeSetting)
theorem finite_coarseBond : Finite W.CoarseBond := by apply _root_.YangMills.Construction.GeneralTorus.InnerProductsAdjointsProjections.finite_coarseBond <;> assumption
theorem coarseSpacing_pos (c : W.CoarseBond) : 0 < GaugeSetting.coarseSpacing c :=
  levelSpacing_pos W.data _
end SeriesExpansions
end YangMills.Construction.GeneralTorus.CompressedBoundsProof
