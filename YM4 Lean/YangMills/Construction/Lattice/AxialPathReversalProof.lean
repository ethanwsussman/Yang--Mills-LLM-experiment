import YangMills.Construction.Lattice.AxialPathReversal
import YangMills.Construction.Lattice.PivotBondsOfTheCoarseBondsLieApartProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
namespace AxialReversal
variable {L m : ℕ} {j : ℤ}
theorem torusSide_eq_mul_meshSize (hL : 0 < L) (j : ℤ) :
    torusSide L m = 2 * (L : ℝ) ^ ((m : ℤ) + j) * meshSize L j := by
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  rw [torusSide, meshSize, zpow_neg, zpow_add₀ hL0, zpow_natCast]
  have : (L : ℝ) ^ j ≠ 0 := zpow_ne_zero _ hL0
  field_simp
theorem int_eq_zero_of_smul_meshSize_coe_eq_zero (hL : 0 < L) {c : ℤ}
    (hc : |(c : ℝ)| < 2 * (L : ℝ) ^ ((m : ℤ) + j))
    (h : (((c : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) = 0) : c = 0 := by
  rw [AddCircle.coe_eq_zero_iff] at h
  obtain ⟨t, ht⟩ := h
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  have hsp : meshSize L j ≠ 0 := zpow_ne_zero _ hLp.ne'
  have hM : (0 : ℝ) < (L : ℝ) ^ ((m : ℤ) + j) := zpow_pos hLp _
  rw [torusSide_eq_mul_meshSize hL j, zsmul_eq_mul] at ht
  have h1 : (t : ℝ) * (2 * (L : ℝ) ^ ((m : ℤ) + j)) = c := by
    apply mul_right_cancel₀ hsp
    rw [← ht]
    ring
  have h2 : |(t : ℝ)| < 1 := by
    rw [← h1, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * (L : ℝ) ^ ((m : ℤ) + j))] at hc
    by_contra hcon
    rw [not_lt] at hcon
    nlinarith
  have h3 : t = 0 := by
    have : |t| < 1 := by exact_mod_cast h2
    exact Int.abs_lt_one_iff.mp this
  rw [h3] at h1
  have : (c : ℝ) = 0 := by simpa using h1.symm
  exact_mod_cast this
theorem zsmul_unitStep_apply_self (n : ℤ) (μ : Fin 4) :
    ((n • unitStep L m j μ : Site L m j) : FourTorus L m) μ =
      (((n : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) := by apply _root_.YangMills.SharedProofs.p4610 <;> assumption
theorem zsmul_unitStep_apply_of_ne (n : ℤ) {μ ν : Fin 4} (h : ν ≠ μ) :
    ((n • unitStep L m j μ : Site L m j) : FourTorus L m) ν = 0 := by
  simp [unitStep, pointOnAxis, Pi.single_eq_of_ne h]
theorem axial_displacement_unique (hL : 0 < L) {a b : ℤ} {μ ν : Fin 4} (ha0 : a ≠ 0)
    (ha : ((|a| : ℤ) : ℝ) < (L : ℝ) ^ ((m : ℤ) + j))
    (hb : ((|b| : ℤ) : ℝ) < (L : ℝ) ^ ((m : ℤ) + j))
    (h : a • unitStep L m j μ = b • unitStep L m j ν) : ν = μ ∧ b = a := by
  have hc : ((a • unitStep L m j μ : Site L m j) : FourTorus L m) μ =
      ((b • unitStep L m j ν : Site L m j) : FourTorus L m) μ :=
    congrArg (fun s : Site L m j => (s : FourTorus L m) μ) h
  rw [zsmul_unitStep_apply_self] at hc
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  have hM : (0 : ℝ) < (L : ℝ) ^ ((m : ℤ) + j) := zpow_pos hLp _
  by_cases hνμ : ν = μ
  · subst hνμ
    rw [zsmul_unitStep_apply_self, ← sub_eq_zero, ← AddCircle.coe_sub, ← sub_mul,
      ← Int.cast_sub] at hc
    refine ⟨rfl, ?_⟩
    have := int_eq_zero_of_smul_meshSize_coe_eq_zero (m := m) (j := j) hL (c := a - b) (by
      have e1 : |((a - b : ℤ) : ℝ)| ≤ ((|a| : ℤ) : ℝ) + ((|b| : ℤ) : ℝ) := by
        push_cast
        exact abs_sub _ _
      linarith) hc
    omega
  · rw [zsmul_unitStep_apply_of_ne b (Ne.symm hνμ)] at hc
    have := int_eq_zero_of_smul_meshSize_coe_eq_zero (m := m) (j := j) hL (c := a) (by
      have e1 : |(a : ℝ)| = ((|a| : ℤ) : ℝ) := by push_cast; rfl
      rw [e1]
      linarith) hc
    exact absurd this ha0
theorem axialPath_eq_flowAlong (hL : 0 < L) {x x' : Site L m j} {μ : Fin 4} {n : ℤ}
    (h : IsAxialDisplacement x x' μ n) : axialPath x x' = flowAlong x μ n := by
  have hex : ∃ q : Fin 4 × ℤ, IsAxialDisplacement x x' q.1 q.2 := ⟨(μ, n), h⟩
  rw [axialPath, dif_pos hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  by_cases hn : n = 0
  · subst hn
    have hk : hex.choose.2 = 0 := by
      by_contra hk
      have := axial_displacement_unique (m := m) (j := j) hL (μ := hex.choose.1) (ν := μ)
        (b := 0) hk h2 h.2 (h1.symm.trans h.1)
      exact hk this.2.symm
    rw [hk]
    simp [flowAlong, forwardAxisPath]
  · obtain ⟨e1, e2⟩ := axial_displacement_unique (m := m) (j := j) hL hn h.2 h2
      (h.1.symm.trans h1)
    rw [e1, e2]
theorem backwardFlow_succ (y : Site L m j) (μ : Fin 4) (N : ℕ) :
    backwardAxisPath y μ (N + 1) =
      backwardAxisPath y μ N ++ [Bond.backwardFrom (y - N • unitStep L m j μ) μ] := by
  induction N generalizing y with
  | zero => simp [backwardAxisPath]
  | succ N ih =>
    rw [backwardAxisPath, ih (y - unitStep L m j μ), backwardAxisPath, List.cons_append]
    congr 3
    rw [succ_nsmul']
    abel
theorem forwardFlow_succ (y : Site L m j) (μ : Fin 4) (N : ℕ) :
    forwardAxisPath y μ (N + 1) =
      forwardAxisPath y μ N ++ [Bond.forwardFrom (y + N • unitStep L m j μ) μ] := by
  induction N generalizing y with
  | zero => simp [forwardAxisPath]
  | succ N ih =>
    rw [forwardAxisPath, ih (y + unitStep L m j μ), forwardAxisPath, List.cons_append]
    congr 3
    rw [succ_nsmul']
    abel
theorem reversePath_cons (b : Bond L m j) (Γ : List (Bond L m j)) :
    reversePath (b :: Γ) = reversePath Γ ++ [b.opposite] := by
  simp [reversePath]
theorem opposite_forwardFrom (x : Site L m j) (μ : Fin 4) :
    (Bond.forwardFrom x μ).opposite = Bond.backwardFrom (x + unitStep L m j μ) μ := by
  apply Bond.ext
  · rfl
  · simp [Bond.opposite, Bond.forwardFrom, Bond.backwardFrom]
theorem opposite_backwardFrom (x : Site L m j) (μ : Fin 4) :
    (Bond.backwardFrom x μ).opposite = Bond.forwardFrom (x - unitStep L m j μ) μ := by
  apply Bond.ext
  · rfl
  · simp [Bond.opposite, Bond.forwardFrom, Bond.backwardFrom]
theorem reversePath_forwardFlow (x : Site L m j) (μ : Fin 4) (N : ℕ) :
    reversePath (forwardAxisPath x μ N) = backwardAxisPath (x + N • unitStep L m j μ) μ N := by
  induction N generalizing x with
  | zero => simp [forwardAxisPath, backwardAxisPath, reversePath]
  | succ N ih =>
    have e : x + unitStep L m j μ + N • unitStep L m j μ = x + (N + 1) • unitStep L m j μ := by
      rw [succ_nsmul']
      abel
    rw [forwardAxisPath, reversePath_cons, ih, backwardFlow_succ, e, opposite_forwardFrom]
    congr 3
    rw [succ_nsmul']
    abel
theorem reversePath_backwardFlow (x : Site L m j) (μ : Fin 4) (N : ℕ) :
    reversePath (backwardAxisPath x μ N) = forwardAxisPath (x - N • unitStep L m j μ) μ N := by
  induction N generalizing x with
  | zero => simp [forwardAxisPath, backwardAxisPath, reversePath]
  | succ N ih =>
    have e : x - unitStep L m j μ - N • unitStep L m j μ = x - (N + 1) • unitStep L m j μ := by
      rw [succ_nsmul']
      abel
    rw [backwardAxisPath, reversePath_cons, ih, forwardFlow_succ, e, opposite_backwardFrom]
    congr 3
    rw [succ_nsmul']
    abel
theorem flowAlong_neg {x x' : Site L m j} {μ : Fin 4} {n : ℤ}
    (h : x' - x = n • unitStep L m j μ) :
    flowAlong x' μ (-n) = reversePath (flowAlong x μ n) := by
  have hx' : x' = x + n • unitStep L m j μ := by rw [← h]; abel
  rcases lt_trichotomy n 0 with hn | hn | hn
  · obtain ⟨N, rfl⟩ : ∃ N : ℕ, n = -(N : ℤ) := ⟨(-n).toNat, by omega⟩
    have h1 : ¬ (0 : ℤ) ≤ -(N : ℤ) := by omega
    rw [flowAlong, flowAlong, if_neg h1, neg_neg, if_pos (by omega)]
    simp only [Int.toNat_natCast]
    rw [reversePath_backwardFlow, hx']
    congr 1
    simp [sub_eq_add_neg]
  · subst hn
    simp [flowAlong, forwardAxisPath, reversePath]
  · obtain ⟨N, rfl⟩ : ∃ N : ℕ, n = (N : ℤ) := ⟨n.toNat, by omega⟩
    have h1 : ¬ (0 : ℤ) ≤ -(N : ℤ) := by omega
    rw [flowAlong, flowAlong, if_neg h1, if_pos (by omega)]
    simp only [Int.toNat_natCast, neg_neg]
    rw [reversePath_forwardFlow, hx']
    congr 1
theorem pathHolonomy_reversePath (U : Bond L m j → Matrices.ComplexMatrix2)
    (Γ : List (Bond L m j)) (h : ∀ b ∈ Γ, U b.opposite = (U b)⁻¹) :
    pathHolonomy U (reversePath Γ) = (pathHolonomy U Γ)⁻¹ := by
  induction Γ with
  | nil => simp [pathHolonomy, reversePath]
  | cons b Γ ih =>
    have ih' := ih fun c hc => h c (List.mem_cons_of_mem _ hc)
    have hb := h b List.mem_cons_self
    rw [reversePath_cons]
    simp only [pathHolonomy] at ih' ⊢
    rw [List.map_append, List.prod_append, ih']
    simp [hb, Matrix.mul_inv_rev]
theorem bondFormSumAlong_reversePath (A : Bond L m j → Matrices.ComplexMatrix2)
    (Γ : List (Bond L m j)) (h : ∀ b : Bond L m j, A b.opposite = -A b) :
    bondFormSumAlong A (reversePath Γ) = -bondFormSumAlong A Γ := by
  induction Γ with
  | nil => simp [bondFormSumAlong, reversePath]
  | cons b Γ ih =>
    rw [reversePath_cons]
    simp only [bondFormSumAlong] at ih ⊢
    rw [List.map_append, List.sum_append, ih]
    simp [h b, add_comm]
end AxialReversal
open AxialReversal in
theorem axialPathReversal_holds : AxialPathReversal := by
  intro L m hL _ j _ x x' μ n hd
  have hL0 : 0 < L := by have := hL.2; omega
  have hback : IsAxialDisplacement x' x μ (-n) := by
    refine ⟨?_, by simpa using hd.2⟩
    rw [neg_smul, ← hd.1]
    abel
  have hpath : axialPath x' x = reversePath (axialPath x x') := by
    rw [axialPath_eq_flowAlong hL0 hback, axialPath_eq_flowAlong hL0 hd, flowAlong_neg hd.1]
  refine ⟨⟨(μ, -n), hback⟩, hpath, ?_, ?_⟩
  · intro U hU
    rw [hpath]
    exact pathHolonomy_reversePath U _ fun b hb => hU.2 b (Or.inl hb)
  · intro A hA
    rw [hpath]
    exact bondFormSumAlong_reversePath A _ hA.2
end YangMills.Construction.PeriodicLattice
