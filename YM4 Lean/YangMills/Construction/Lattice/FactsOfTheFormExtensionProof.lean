import YangMills.Construction.Lattice.DifferenceOperatorsOfTheBareLattice
import YangMills.Construction.Lattice.ExistenceOfTheOperatorsOfASeparatedSequence
import YangMills.Construction.Lattice.GaugeInvarianceOfTheConditionsOfASequence
import YangMills.Construction.Lattice.ProductsOfTheFormGreenOperator
import YangMills.Construction.LinearAlgebra.ConstrainedMinimisation
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set PeriodicLattice PeriodicLattice.DirichletOperators FiniteDimReal RealInnerForms
namespace SeparatedSequences.OneExtensionProof
section Pairings
variable {V : Type} [AddCommGroup V] [Module ℝ V]
structure IsRealInner (ip : V → V → ℝ) : Prop where
  add_left : ∀ a b c, ip (a + b) c = ip a c + ip b c
  smul_left : ∀ (r : ℝ) a b, ip (r • a) b = r * ip a b
  symm : ∀ a b, ip a b = ip b a
  pos : ∀ a, a ≠ 0 → 0 < ip a a
namespace IsRealInner
variable {ip : V → V → ℝ} (h : IsRealInner ip)
include h
theorem zero_left (b : V) : ip 0 b = 0 := by
  have := h.smul_left 0 0 b
  simpa using this
theorem sub_left (a b c : V) : ip (a - b) c = ip a c - ip b c := by
  have h1 := h.add_left (a - b) b c
  rw [sub_add_cancel] at h1
  linarith
theorem add_right (a b c : V) : ip a (b + c) = ip a b + ip a c := by
  rw [h.symm, h.add_left, h.symm b, h.symm c]
theorem self_nonneg (a : V) : 0 ≤ ip a a := by
  by_cases ha : a = 0
  · rw [ha, h.zero_left]
  · exact (h.pos a ha).le
theorem eq_zero_of_self_eq_zero (a : V) (ha : ip a a = 0) : a = 0 := by
  by_contra hne
  exact (h.pos a hne).ne' ha
theorem restrict (p : Submodule ℝ V) : IsRealInner (fun a b : p => ip a.1 b.1) where
  add_left _ _ _ := h.add_left _ _ _
  smul_left _ _ _ := h.smul_left _ _ _
  symm _ _ := h.symm _ _
  pos _ ha := h.pos _ fun e => ha (Subtype.ext e)
@[instance_reducible]
def innerCore : InnerProductSpace.Core ℝ V where
  inner := ip
  conj_inner_symm x y := by
    simpa using h.symm y x
  re_inner_nonneg x := by
    simpa using h.self_nonneg x
  add_left := h.add_left
  smul_left x y r := by
    simpa using h.smul_left r x y
  definite x hx := h.eq_zero_of_self_eq_zero x hx
end IsRealInner
end Pairings
section Lift
variable {V W : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
end Lift
section Euclidean
variable {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
end Euclidean
section Transport
variable {V W : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W] {ipV : V → V → ℝ} {ipW : W → W → ℝ}
omit [FiniteDimensional ℝ V] in
theorem inner_proj_eq {ip : V → V → ℝ} {p : Submodule ℝ V} {P : V →ₗ[ℝ] V} (h : IsRealInner ip)
    (hP : IsOrthogonalProjectionFor ip p P) (f g : V) : ip f (P g) = ip (P f) (P g) := by
  have := (hP f).2 _ (hP g).1
  rw [h.sub_left] at this
  linarith
end Transport
section Sums
theorem finsum_pos_of_nonneg {ι : Type} [Finite ι] (f : ι → ℝ) (h0 : ∀ i, 0 ≤ f i) (i : ι)
    (hi : 0 < f i) : 0 < ∑ᶠ j, f j := by
  classical
  haveI := Fintype.ofFinite ι
  rw [finsum_eq_sum_of_fintype]
  exact Finset.sum_pos' (fun j _ => h0 j) ⟨i, Finset.mem_univ _, hi⟩
end Sums
section Sequence
open BaseParameters
variable (D : BaseParameters) (Ω : ℕ → Set D.Torus) (φ : BondFrame)
theorem levelMeshRatio_pos (n : ℕ) : 0 < D.levelMeshRatio n := by
  have hL : (0 : ℝ) < D.L := by
    have := D.three_le_L
    exact_mod_cast (by omega : 0 < D.L)
  simp only [levelMeshRatio, ScaleData.levelMesh]
  exact zpow_pos hL _
theorem finestMesh_pos : 0 < finestMeshInLevelUnits D.L D.t := by
  rw [← D.levelMeshRatio_zero]
  exact levelMeshRatio_pos D 0
abbrev gaugeFixedForm : Module.End ℝ (D.RegionOneForms Ω φ) :=
  D.regionCurlCurl Ω φ + D.gaugeFixingTerm Ω φ
theorem normSq_nonneg {ι : Type} (g : ι → ℝ) : 0 ≤ D.normSq g :=
  mul_nonneg (pow_pos (finestMesh_pos D) 4).le (finsum_nonneg fun _ => mul_self_nonneg _)
end Sequence
end SeparatedSequences.OneExtensionProof
end YangMills.Construction
end
