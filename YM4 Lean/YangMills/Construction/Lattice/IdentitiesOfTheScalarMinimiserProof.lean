import YangMills.Construction.Lattice.FactsOfTheFormExtensionProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ZeroFormMinimizerProof
open Set PeriodicLattice PeriodicLattice.DirichletOperators FiniteDimReal
section Pairings
variable {V : Type} [AddCommGroup V] [Module ℝ V]
structure IsInnerForm (ip : V → V → ℝ) : Prop where
  add_left : ∀ a b c, ip (a + b) c = ip a c + ip b c
  smul_left : ∀ (r : ℝ) a b, ip (r • a) b = r * ip a b
  symm : ∀ a b, ip a b = ip b a
  pos : ∀ a, a ≠ 0 → 0 < ip a a
namespace IsInnerForm
variable {ip : V → V → ℝ} (h : IsInnerForm ip)
include h
theorem zero_left (b : V) : ip 0 b = 0 := by
  have := h.smul_left 0 0 b
  simpa using this
theorem zero_right (b : V) : ip b 0 = 0 := by
  rw [h.symm, h.zero_left]
theorem add_right (a b c : V) : ip a (b + c) = ip a b + ip a c := by
  rw [h.symm, h.add_left, h.symm b, h.symm c]
theorem self_nonneg (a : V) : 0 ≤ ip a a := by
  by_cases ha : a = 0
  · rw [ha, h.zero_left]
  · exact (h.pos a ha).le
theorem eq_zero_of_self (a : V) (ha : ip a a = 0) : a = 0 := by
  by_contra hne
  exact (h.pos a hne).ne' ha
theorem restrict (p : Submodule ℝ V) : IsInnerForm (fun a b : p => ip a.1 b.1) where
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
  definite x hx := h.eq_zero_of_self x hx
end IsInnerForm
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
theorem exists_isAdjointFor (hV : IsInnerForm ipV) (hW : IsInnerForm ipW) (T : V →ₗ[ℝ] W) :
    ∃ T' : W →ₗ[ℝ] V, IsAdjointFor ipV ipW T T' := by
  let nV : NormedAddCommGroup V :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ V _ _ _ hV.innerCore
  let sV : InnerProductSpace ℝ V := InnerProductSpace.ofCore hV.innerCore.toCore
  let nW : NormedAddCommGroup W :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ W _ _ _ hW.innerCore
  let sW : InnerProductSpace ℝ W := InnerProductSpace.ofCore hW.innerCore.toCore
  exact ⟨LinearMap.adjoint T, fun f g => (LinearMap.adjoint_inner_left T f g).symm⟩
end Transport
section Sums
theorem finsum_pos_of_nonneg {ι : Type} [Finite ι] (f : ι → ℝ) (h0 : ∀ i, 0 ≤ f i) (i : ι)
    (hi : 0 < f i) : 0 < ∑ᶠ j, f j := by apply _root_.YangMills.Construction.SeparatedSequences.OneExtensionProof.finsum_pos_of_nonneg <;> assumption
end Sums
section Sequence
open SeparatedSequences SeparatedSequences.BaseParameters
variable (D : BaseParameters) (Ω : ℕ → Set D.Torus)
theorem levelMeshRatio_pos (n : ℕ) : 0 < D.levelMeshRatio n := by apply _root_.YangMills.Construction.SeparatedSequences.OneExtensionProof.levelMeshRatio_pos <;> assumption
theorem finestMesh_pos : 0 < finestMeshInLevelUnits D.L D.t := by apply _root_.YangMills.Construction.SeparatedSequences.OneExtensionProof.finestMesh_pos <;> assumption
theorem isInnerForm_coarseZeroInner : IsInnerForm (D.coarseZeroInner Ω) where
  add_left a b c := by
    simp only [coarseZeroInner, pointValue_add, add_mul, finsum_add_finite, mul_add,
      Finset.sum_add_distrib]
  smul_left r a b := by
    simp only [coarseZeroInner, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [pointValue_smul, mul_assoc, finsum_const_mul_finite]
    ring
  symm a b := by
    simp only [coarseZeroInner]
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 1
    exact finsum_congr fun c => mul_comm _ _
  pos a ha := by
    obtain ⟨⟨y, hy⟩, hi⟩ := Function.ne_iff.mp ha
    obtain ⟨⟨n, z⟩, hn, hz, hzy⟩ := D.exists_levelSite Ω ⟨y, hy⟩
    have hzy' : (z : D.Torus) = y := hzy
    subst hzy'
    have hb : pointValue a (z : D.Torus) = a ⟨_, hy⟩ := dif_pos hy
    refine Finset.sum_pos' (fun k _ => mul_nonneg (pow_pos (levelMeshRatio_pos D k) _).le
      (finsum_nonneg fun _ => mul_self_nonneg _))
      ⟨n, Finset.mem_range.mpr (Nat.lt_succ_of_le hn), ?_⟩
    exact mul_pos (pow_pos (levelMeshRatio_pos D n) _)
      (finsum_pos_of_nonneg _ (fun _ => mul_self_nonneg _)
        ⟨z, hz⟩ (mul_self_pos.mpr (by rw [hb]; exact hi)))
theorem normSq_nonneg {ι : Type} (g : ι → ℝ) : 0 ≤ D.normSq g :=
  mul_nonneg (pow_pos (finestMesh_pos D) 4).le (finsum_nonneg fun _ => mul_self_nonneg _)
end Sequence
end YangMills.Construction.ZeroFormMinimizerProof
end
