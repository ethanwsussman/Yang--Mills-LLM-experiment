import YangMills.Construction.Lattice.PeriodicLattices
import Mathlib
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice

namespace MatrixValued
variable {L m : ℕ} {j : ℤ}
theorem coe_small_multiple_meshSize_ne_zero (hL : 2 ≤ L) (hj : -(m : ℤ) < j) {c : ℤ}
    (hc0 : 0 < c) (hc : c ≤ 2) :
    (((c : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) ≠ 0 := by
  intro h
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (m : ℤ) + j = (N : ℤ) + 1 :=
    ⟨((m : ℤ) + j - 1).toNat, by omega⟩
  have hL0 : (L : ℝ) ≠ 0 := by
    have : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
    exact this.ne'
  rw [AddCircle.coe_eq_zero_iff] at h
  obtain ⟨n, hn⟩ := h
  have hside : torusSide L m = 2 * (L : ℝ) ^ ((N : ℤ) + 1) * meshSize L j := by
    rw [torusSide, meshSize, ← hN, zpow_neg, zpow_add₀ hL0, zpow_natCast]
    have : (L : ℝ) ^ j ≠ 0 := zpow_ne_zero _ hL0
    field_simp
  have hs : meshSize L j ≠ 0 := zpow_ne_zero _ hL0
  rw [hside, zsmul_eq_mul] at hn
  have h1 : (n : ℝ) * (2 * (L : ℝ) ^ ((N : ℤ) + 1)) = c := by
    apply mul_right_cancel₀ hs
    rw [← hn]; ring
  have h2 : n * (2 * (L : ℤ) ^ (N + 1)) = c := by
    have : ((n * (2 * (L : ℤ) ^ (N + 1)) : ℤ) : ℝ) = (c : ℝ) := by
      push_cast
      rw [← h1, zpow_add₀ hL0, zpow_natCast, pow_succ, zpow_one]
    exact_mod_cast this
  have hLN : (2 : ℤ) ≤ (L : ℤ) ^ (N + 1) := by
    have h3 : (2 : ℤ) ≤ (L : ℤ) := by exact_mod_cast hL
    calc (2 : ℤ) ≤ L := h3
      _ = (L : ℤ) ^ 1 := (pow_one _).symm
      _ ≤ (L : ℤ) ^ (N + 1) := pow_le_pow_right₀ (by omega) (by omega)
  have hn1 : 1 ≤ n := by
    by_contra hcon
    have : n ≤ 0 := by omega
    nlinarith
  nlinarith
theorem unitStep_add_unitStep_ne_zero (hL : 2 ≤ L) (hj : -(m : ℤ) < j) (μ ν : Fin 4) :
    unitStep L m j μ + unitStep L m j ν ≠ 0 := by
  intro h
  have h' := congrArg (fun s : Site L m j => (s : FourTorus L m) μ) h
  by_cases hμν : ν = μ
  · subst hμν
    have := coe_small_multiple_meshSize_ne_zero (m := m) hL hj (c := 2) (by norm_num) le_rfl
    apply this
    simpa [unitStep, pointOnAxis, two_mul] using h'
  · have := coe_small_multiple_meshSize_ne_zero (m := m) hL hj (c := 1) (by norm_num)
      (by norm_num)
    apply this
    simpa [unitStep, pointOnAxis, Pi.single_eq_of_ne (Ne.symm hμν)] using h'
theorem unitStep_ne_unitStep (hL : 2 ≤ L) (hj : -(m : ℤ) < j) {μ ν : Fin 4} (hμν : μ ≠ ν) :
    unitStep L m j μ ≠ unitStep L m j ν := by
  intro h
  have h' := congrArg (fun s : Site L m j => (s : FourTorus L m) μ) h
  have := coe_small_multiple_meshSize_ne_zero (m := m) hL hj (c := 1) (by norm_num)
    (by norm_num)
  apply this
  simpa [unitStep, pointOnAxis, Pi.single_eq_of_ne hμν] using h'
theorem xor_isPositivelyOriented_opposite (hL : 2 ≤ L) (hj : -(m : ℤ) < j) (b : Bond L m j) :
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := by
  obtain ⟨μ, h | h⟩ := b.isNeighbour
  · refine Or.inl ⟨⟨μ, h⟩, ?_⟩
    rintro ⟨ν, hν⟩
    apply unitStep_add_unitStep_ne_zero hL hj μ ν
    rw [← h, ← hν]
    show b.target - b.source + (b.source - b.target) = 0
    abel
  · refine Or.inr ⟨⟨μ, ?_⟩, ?_⟩
    · show b.source - b.target = unitStep L m j μ
      rw [← neg_sub, h, neg_neg]
    · rintro ⟨ν, hν⟩
      apply unitStep_add_unitStep_ne_zero hL hj ν μ
      rw [← hν, eq_neg_iff_add_eq_zero.mp h]
theorem axis_forwardFrom (hL : 2 ≤ L) (hj : -(m : ℤ) < j) (x : Site L m j) (μ : Fin 4) :
    (Bond.forwardFrom x μ).axis = μ := by
  have hspec := (Bond.forwardFrom x μ).isNeighbour.choose_spec
  have hd : (Bond.forwardFrom x μ).target - (Bond.forwardFrom x μ).source =
      unitStep L m j μ := by
    simp [Bond.forwardFrom]
  change (Bond.forwardFrom x μ).isNeighbour.choose = μ
  generalize (Bond.forwardFrom x μ).isNeighbour.choose = d at hspec
  rw [hd] at hspec
  by_contra hne
  rcases hspec with h | h
  · exact unitStep_ne_unitStep hL hj (Ne.symm hne) h
  · apply unitStep_add_unitStep_ne_zero hL hj μ d
    rw [h]
    abel
end MatrixValued
end YangMills.Construction.PeriodicLattice
