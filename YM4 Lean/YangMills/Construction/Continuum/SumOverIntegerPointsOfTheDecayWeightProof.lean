import YangMills.Construction.Continuum.SumOverIntegerPointsOfTheDecayWeight
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigSpace
namespace LatticeDecaySum
def latticeBox (n l : ℕ) : Finset (Fin n → Fin 4 → ℤ) :=
  Fintype.piFinset fun _ => Fintype.piFinset fun _ => Finset.Icc (-(l : ℤ)) l
theorem mem_latticeBox {n l : ℕ} {x : Fin n → Fin 4 → ℤ} :
    x ∈ latticeBox n l ↔ ∀ i c, |x i c| ≤ (l : ℤ) := by
  simp [latticeBox, Fintype.mem_piFinset, abs_le]
theorem latticeBox_mono {n l m : ℕ} (hlm : l ≤ m) : latticeBox n l ⊆ latticeBox n m := by
  intro x hx
  rw [mem_latticeBox] at hx ⊢
  intro i c
  exact (hx i c).trans (by exact_mod_cast hlm)
theorem card_latticeBox (n l : ℕ) :
    ((latticeBox n l).card : ℝ) = (2 * (l : ℝ) + 1) ^ (4 * n) := by
  have h : (Finset.Icc (-(l : ℤ)) l).card = 2 * l + 1 := by
    rw [Int.card_Icc]
    omega
  simp only [latticeBox, Fintype.card_piFinset, h, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  push_cast
  rw [pow_mul]
theorem coordSupNorm_intCast_nonneg {n : ℕ} (x : Fin n → Fin 4 → ℤ) :
    0 ≤ coordSupNorm (fun i c => (x i c : ℝ)) :=
  Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => abs_nonneg _
theorem abs_le_coordSupNorm_intCast {n : ℕ} (x : Fin n → Fin 4 → ℤ) (i : Fin n) (c : Fin 4) :
    |(x i c : ℝ)| ≤ coordSupNorm (fun i c => (x i c : ℝ)) :=
  (le_ciSup (f := fun c => |(x i c : ℝ)|) (Set.finite_range _).bddAbove c).trans
    (le_ciSup (f := fun i => ⨆ c, |(x i c : ℝ)|) (Set.finite_range _).bddAbove i)
def supLevel {n : ℕ} (x : Fin n → Fin 4 → ℤ) : ℕ := ⌊coordSupNorm (fun i c => (x i c : ℝ))⌋₊
theorem supLevel_le_coordSupNorm {n : ℕ} (x : Fin n → Fin 4 → ℤ) :
    (supLevel x : ℝ) ≤ coordSupNorm (fun i c => (x i c : ℝ)) :=
  Nat.floor_le (coordSupNorm_intCast_nonneg x)
theorem mem_latticeBox_supLevel {n : ℕ} (x : Fin n → Fin 4 → ℤ) :
    x ∈ latticeBox n (supLevel x) := by
  rw [mem_latticeBox]
  intro i c
  have h : (((x i c).natAbs : ℕ) : ℝ) ≤ coordSupNorm (fun i c => (x i c : ℝ)) := by
    have h1 := abs_le_coordSupNorm_intCast x i c
    rwa [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast] at h1
  have h2 : (x i c).natAbs ≤ supLevel x := Nat.le_floor h
  rw [Int.abs_eq_natAbs]
  exact_mod_cast h2
theorem supLevel_le_of_mem_latticeBox {n l : ℕ} {x : Fin n → Fin 4 → ℤ}
    (hx : x ∈ latticeBox n l) : supLevel x ≤ l := by
  apply Nat.floor_le_of_le
  refine Real.iSup_le (fun i => Real.iSup_le (fun c => ?_) (Nat.cast_nonneg l)) (Nat.cast_nonneg l)
  have h1 := mem_latticeBox.1 hx i c
  rw [← Int.cast_abs]
  exact_mod_cast h1
theorem decayWeight_le_inv_pow {n : ℕ} (x : Fin n → Fin 4 → ℤ) :
    (1 + Real.pi * coordSupNorm (fun i c => (x i c : ℝ))) ^ (-(4 * (n : ℤ)) - 1) ≤
      ((2 * (supLevel x : ℝ) + 1) ^ (4 * n + 1))⁻¹ := by
  have hM := coordSupNorm_intCast_nonneg x
  have hs := supLevel_le_coordSupNorm x
  have h : 2 * (supLevel x : ℝ) + 1 ≤ 1 + Real.pi * coordSupNorm (fun i c => (x i c : ℝ)) := by
    nlinarith [Real.pi_gt_three]
  have e : -(4 * (n : ℤ)) - 1 = -((4 * n + 1 : ℕ) : ℤ) := by
    push_cast
    ring
  rw [e, zpow_neg, zpow_natCast]
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) h _)
theorem pow_succ_sub_pow_succ_le (a b : ℝ) (hb : 0 ≤ b) (hab : b ≤ a) (k : ℕ) :
    a ^ (k + 1) - b ^ (k + 1) ≤ ((k : ℝ) + 1) * (a - b) * a ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ha : 0 ≤ a := hb.trans hab
    have h1 : b ^ (k + 1) ≤ a ^ (k + 1) := pow_le_pow_left₀ hb hab _
    have h2 : a * (a ^ (k + 1) - b ^ (k + 1)) ≤ a * (((k : ℝ) + 1) * (a - b) * a ^ k) :=
      mul_le_mul_of_nonneg_left ih ha
    have h3 : (a - b) * b ^ (k + 1) ≤ (a - b) * a ^ (k + 1) :=
      mul_le_mul_of_nonneg_left h1 (sub_nonneg.2 hab)
    have h4 : a ^ (k + 1 + 1) - b ^ (k + 1 + 1) =
        a * (a ^ (k + 1) - b ^ (k + 1)) + (a - b) * b ^ (k + 1) := by ring
    have h5 : (((k + 1 : ℕ) : ℝ) + 1) * (a - b) * a ^ (k + 1) =
        a * (((k : ℝ) + 1) * (a - b) * a ^ k) + (a - b) * a ^ (k + 1) := by
      push_cast
      ring
    rw [h4, h5]
    linarith
theorem card_filter_supLevel_le (n L m : ℕ) :
    (((latticeBox n L).filter (fun x => supLevel x = m + 1)).card : ℝ) ≤
      (2 * (m : ℝ) + 3) ^ (4 * n) - (2 * (m : ℝ) + 1) ^ (4 * n) := by
  have hsub : (latticeBox n L).filter (fun x => supLevel x = m + 1) ⊆
      latticeBox n (m + 1) \ latticeBox n m := by
    intro x hx
    have h := (Finset.mem_filter.1 hx).2
    refine Finset.mem_sdiff.2 ⟨h ▸ mem_latticeBox_supLevel x, fun h' => ?_⟩
    have h2 := supLevel_le_of_mem_latticeBox h'
    omega
  have h1 : (((latticeBox n L).filter (fun x => supLevel x = m + 1)).card : ℝ) ≤
      ((latticeBox n (m + 1) \ latticeBox n m).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have h2 : ((latticeBox n (m + 1) \ latticeBox n m).card : ℝ) + ((latticeBox n m).card : ℝ) =
      ((latticeBox n (m + 1)).card : ℝ) := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card (latticeBox_mono (Nat.le_succ m))
  have h3 := card_latticeBox n m
  have h4 := card_latticeBox n (m + 1)
  have h5 : 2 * ((m + 1 : ℕ) : ℝ) + 1 = 2 * (m : ℝ) + 3 := by
    push_cast
    ring
  rw [h5] at h4
  linarith
theorem card_filter_supLevel_mul_inv_le (n L m : ℕ) (hn : 1 ≤ n) :
    (((latticeBox n L).filter (fun x => supLevel x = m + 1)).card : ℝ) *
        ((2 * ((m + 1 : ℕ) : ℝ) + 1) ^ (4 * n + 1))⁻¹ ≤
      8 * (n : ℝ) * (1 / ((m : ℝ) + 1) - 1 / ((m : ℝ) + 2)) := by
  obtain ⟨k, hk⟩ : ∃ k, 4 * n = k + 1 := ⟨4 * n - 1, by omega⟩
  have hkn : (k : ℝ) + 1 = 4 * (n : ℝ) := by
    have : ((k + 1 : ℕ) : ℝ) = ((4 * n : ℕ) : ℝ) := by rw [hk]
    push_cast at this
    linarith
  have ha : (0 : ℝ) < 2 * (m : ℝ) + 3 := by positivity
  have h5 : 2 * ((m + 1 : ℕ) : ℝ) + 1 = 2 * (m : ℝ) + 3 := by
    push_cast
    ring
  have hc : (((latticeBox n L).filter (fun x => supLevel x = m + 1)).card : ℝ) ≤
      8 * (n : ℝ) * (2 * (m : ℝ) + 3) ^ k := by
    have h1 := card_filter_supLevel_le n L m
    have h2 := pow_succ_sub_pow_succ_le (2 * (m : ℝ) + 3) (2 * (m : ℝ) + 1) (by positivity)
      (by linarith) k
    rw [hk] at h1
    have h3 : ((k : ℝ) + 1) * (2 * (m : ℝ) + 3 - (2 * (m : ℝ) + 1)) * (2 * (m : ℝ) + 3) ^ k =
        8 * (n : ℝ) * (2 * (m : ℝ) + 3) ^ k := by
      rw [hkn]
      ring
    linarith
  rw [h5, hk]
  have hinv : (0 : ℝ) ≤ ((2 * (m : ℝ) + 3) ^ (k + 1 + 1))⁻¹ := by positivity
  have h6 : 8 * (n : ℝ) * (2 * (m : ℝ) + 3) ^ k * ((2 * (m : ℝ) + 3) ^ (k + 1 + 1))⁻¹ =
      8 * (n : ℝ) * (1 / (2 * (m : ℝ) + 3) ^ 2) := by
    have hne : (2 * (m : ℝ) + 3) ≠ 0 := ha.ne'
    field_simp
    ring
  have h7 : 1 / (2 * (m : ℝ) + 3) ^ 2 ≤ 1 / ((m : ℝ) + 1) - 1 / ((m : ℝ) + 2) := by
    have h8 : 1 / ((m : ℝ) + 1) - 1 / ((m : ℝ) + 2) = 1 / (((m : ℝ) + 1) * ((m : ℝ) + 2)) := by
      field_simp
      ring
    rw [h8]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  calc _ ≤ 8 * (n : ℝ) * (2 * (m : ℝ) + 3) ^ k * ((2 * (m : ℝ) + 3) ^ (k + 1 + 1))⁻¹ :=
        mul_le_mul_of_nonneg_right hc hinv
    _ = 8 * (n : ℝ) * (1 / (2 * (m : ℝ) + 3) ^ 2) := h6
    _ ≤ _ := mul_le_mul_of_nonneg_left h7 (by positivity)
theorem sum_range_le_of_telescoping (a : ℕ → ℝ) (c : ℝ) (h0 : a 0 ≤ 1)
    (h : ∀ m : ℕ, a (m + 1) ≤ c * (1 / ((m : ℝ) + 1) - 1 / ((m : ℝ) + 2))) (K : ℕ) :
    ∑ l ∈ Finset.range (K + 1), a l ≤ 1 + c - c / ((K : ℝ) + 1) := by
  induction K with
  | zero => simpa using h0
  | succ K ih =>
    rw [Finset.sum_range_succ]
    have h1 := h K
    have h2 : 1 + c - c / ((K : ℝ) + 1) + c * (1 / ((K : ℝ) + 1) - 1 / ((K : ℝ) + 2)) =
        1 + c - c / (((K + 1 : ℕ) : ℝ) + 1) := by
      push_cast
      field_simp
      ring
    linarith
theorem sum_latticeBox_inv_pow_le (n L : ℕ) (hn : 1 ≤ n) :
    ∑ x ∈ latticeBox n L, ((2 * (supLevel x : ℝ) + 1) ^ (4 * n + 1))⁻¹ ≤ 1 + 8 * (n : ℝ) := by
  have hmaps : ∀ x ∈ latticeBox n L, supLevel x ∈ Finset.range (L + 1) := fun x hx =>
    Finset.mem_range.2 (Nat.lt_succ_of_le (supLevel_le_of_mem_latticeBox hx))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ l ∈ Finset.range (L + 1),
      ∑ x ∈ (latticeBox n L).filter (fun x => supLevel x = l),
          ((2 * (supLevel x : ℝ) + 1) ^ (4 * n + 1))⁻¹ =
        (((latticeBox n L).filter (fun x => supLevel x = l)).card : ℝ) *
          ((2 * (l : ℝ) + 1) ^ (4 * n + 1))⁻¹ := by
    intro l _
    rw [Finset.sum_congr rfl (g := fun _ => ((2 * (l : ℝ) + 1) ^ (4 * n + 1))⁻¹)
      (fun x hx => by rw [(Finset.mem_filter.1 hx).2])]
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_congr rfl hfib]
  have h0 : (((latticeBox n L).filter (fun x => supLevel x = 0)).card : ℝ) *
      ((2 * ((0 : ℕ) : ℝ) + 1) ^ (4 * n + 1))⁻¹ ≤ 1 := by
    have hsub : (latticeBox n L).filter (fun x => supLevel x = 0) ⊆ latticeBox n 0 := by
      intro x hx
      have h := (Finset.mem_filter.1 hx).2
      exact h ▸ mem_latticeBox_supLevel x
    have h1 : (((latticeBox n L).filter (fun x => supLevel x = 0)).card : ℝ) ≤
        ((latticeBox n 0).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    rw [card_latticeBox] at h1
    simpa using h1
  have h := sum_range_le_of_telescoping
    (fun l => (((latticeBox n L).filter (fun x => supLevel x = l)).card : ℝ) *
      ((2 * (l : ℝ) + 1) ^ (4 * n + 1))⁻¹) (8 * (n : ℝ)) h0
    (fun m => card_filter_supLevel_mul_inv_le n L m hn) L
  have hL : 0 ≤ 8 * (n : ℝ) / ((L : ℝ) + 1) := by positivity
  linarith
end LatticeDecaySum
open LatticeDecaySum in
theorem integerLatticeDecaySum_holds : IntegerLatticeDecaySum := by
  intro n hn
  have hg0 : 0 ≤ fun x : Fin n → Fin 4 → ℤ =>
      (1 + Real.pi * coordSupNorm (fun i c => (x i c : ℝ))) ^ (-(4 * (n : ℤ)) - 1) := by
    intro x
    have h := mul_nonneg Real.pi_pos.le (coordSupNorm_intCast_nonneg x)
    exact zpow_nonneg (by linarith) _
  have hfin : ∀ u : Finset (Fin n → Fin 4 → ℤ),
      ∑ x ∈ u, (1 + Real.pi * coordSupNorm (fun i c => (x i c : ℝ))) ^ (-(4 * (n : ℤ)) - 1) ≤
        1 + 8 * (n : ℝ) := by
    intro u
    have hsub : u ⊆ latticeBox n (u.sup supLevel) := fun x hx =>
      latticeBox_mono (Finset.le_sup hx) (mem_latticeBox_supLevel x)
    calc _ ≤ ∑ x ∈ u, ((2 * (supLevel x : ℝ) + 1) ^ (4 * n + 1))⁻¹ :=
          Finset.sum_le_sum fun x _ => decayWeight_le_inv_pow x
      _ ≤ ∑ x ∈ latticeBox n (u.sup supLevel), ((2 * (supLevel x : ℝ) + 1) ^ (4 * n + 1))⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      _ ≤ _ := sum_latticeBox_inv_pow_le n _ hn
  exact ⟨summable_of_sum_le hg0 hfin, Real.tsum_le_of_sum_le hg0 hfin⟩
end YangMills.Construction.ConfigSpace
