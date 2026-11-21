import YangMills.Construction.SystemOfAdmissibleConstants.TentsOfASmallSide
import YangMills.Construction.Torus.PointsAndTuplesOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace SystemOfAdmissibleConstants
open YangMills.Construction.TestFunctions YangMills.Construction.TorusMetric
private theorem abs_add_le_abs_add_abs (a b : ℝ) : |a + b| ≤ |a| + |b| := by
  simpa using norm_add_le a b
private theorem abs_prod_sub_prod_le_sum {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (hb : ∀ i, 0 ≤ b i ∧ b i ≤ 1) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, |a i - b i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
    have hA : |∏ j ∈ s, a j| ≤ 1 := by
      rw [abs_of_nonneg (Finset.prod_nonneg fun j _ => (ha j).1)]
      exact Finset.prod_le_one (fun j _ => (ha j).1) (fun j _ => (ha j).2)
    have hB : |b i| ≤ 1 := by
      rw [abs_of_nonneg (hb i).1]
      exact (hb i).2
    have e : a i * ∏ j ∈ s, a j - b i * ∏ j ∈ s, b j =
        (a i - b i) * ∏ j ∈ s, a j + b i * (∏ j ∈ s, a j - ∏ j ∈ s, b j) := by ring
    rw [e]
    refine (abs_add_le_abs_add_abs _ _).trans ?_
    rw [abs_mul, abs_mul]
    have h1 : |a i - b i| * |∏ j ∈ s, a j| ≤ |a i - b i| * 1 :=
      mul_le_mul_of_nonneg_left hA (abs_nonneg _)
    have h2 : |b i| * |∏ j ∈ s, a j - ∏ j ∈ s, b j| ≤ 1 * |∏ j ∈ s, a j - ∏ j ∈ s, b j| :=
      mul_le_mul_of_nonneg_right hB (abs_nonneg _)
    linarith
private theorem sum_fin_four_le_two_sqrt_sum_sq (w : Fin 4 → ℝ) :
    ∑ μ, w μ ≤ 2 * Real.sqrt (∑ μ, w μ ^ 2) := by
  have h : (∑ μ, w μ) ^ 2 ≤ 4 * ∑ μ, w μ ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin 4))) (f := w)
  have hS : 0 ≤ ∑ μ, w μ ^ 2 := Finset.sum_nonneg fun μ _ => sq_nonneg _
  have hr := Real.sqrt_nonneg (∑ μ, w μ ^ 2)
  have hr2 := Real.sq_sqrt hS
  by_contra hc
  nlinarith
private theorem sqrt_sum_sq_le_two_mul {w : Fin 4 → ℝ} {ε : ℝ} (hε : 0 < ε) (hw : ∀ μ, |w μ| ≤ ε) :
    Real.sqrt (∑ μ, w μ ^ 2) ≤ 2 * ε := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h : ∀ μ, w μ ^ 2 ≤ ε ^ 2 := fun μ => by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hw μ) 2
  have := h 0
  have := h 1
  have := h 2
  have := h 3
  rw [Fin.sum_univ_four]
  nlinarith
private theorem hatFactor_mem_unitInterval {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε) :
    0 ≤ max 0 (1 - r / ε) ∧ max 0 (1 - r / ε) ≤ 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (by have := div_nonneg hr hε.le; linarith)⟩
private theorem hatFactor_eq_zero_of_le {r ε : ℝ} (hε : 0 < ε) (h : ε ≤ r) :
    max 0 (1 - r / ε) = 0 := by
  have : 1 ≤ r / ε := (one_le_div hε).mpr h
  exact max_eq_left (by linarith)
private theorem hatProduct_mem_unitInterval {r : Fin 4 → ℝ} {ε : ℝ} (hr : ∀ μ, 0 ≤ r μ)
    (hε : 0 < ε) :
    0 ≤ ∏ μ, max 0 (1 - r μ / ε) ∧ ∏ μ, max 0 (1 - r μ / ε) ≤ 1 :=
  ⟨Finset.prod_nonneg fun μ _ => (hatFactor_mem_unitInterval (hr μ) hε).1,
    Finset.prod_le_one (fun μ _ => (hatFactor_mem_unitInterval (hr μ) hε).1)
      (fun μ _ => (hatFactor_mem_unitInterval (hr μ) hε).2)⟩
private theorem lt_of_hatProduct_ne_zero {r : Fin 4 → ℝ} {ε : ℝ} (hε : 0 < ε)
    (h : ∏ μ, max 0 (1 - r μ / ε) ≠ 0) (μ : Fin 4) : r μ < ε := by
  have h1 := (Finset.prod_ne_zero_iff.mp h) μ (Finset.mem_univ μ)
  by_contra hc
  exact h1 (hatFactor_eq_zero_of_le hε (not_lt.mp hc))
private theorem abs_hatProduct_sub_le {r r' D : Fin 4 → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hr : ∀ μ, 0 ≤ r μ) (hr' : ∀ μ, 0 ≤ r' μ) (hD : ∀ μ, |r μ - r' μ| ≤ D μ) :
    |∏ μ, max 0 (1 - r μ / ε) - ∏ μ, max 0 (1 - r' μ / ε)| ≤
      2 / ε * Real.sqrt (∑ μ, D μ ^ 2) := by
  have h1 := abs_prod_sub_prod_le_sum Finset.univ (fun μ => max 0 (1 - r μ / ε))
    (fun μ => max 0 (1 - r' μ / ε)) (fun μ => hatFactor_mem_unitInterval (hr μ) hε)
    (fun μ => hatFactor_mem_unitInterval (hr' μ) hε)
  have h2 : ∀ μ, |max 0 (1 - r μ / ε) - max 0 (1 - r' μ / ε)| ≤ D μ / ε := by
    intro μ
    have h3 := abs_max_sub_max_le_abs (1 - r μ / ε) (1 - r' μ / ε) 0
    rw [max_comm 0, max_comm 0]
    refine h3.trans ?_
    have e : (1 - r μ / ε) - (1 - r' μ / ε) = -((r μ - r' μ) / ε) := by ring
    rw [e, abs_neg, abs_div, abs_of_pos hε]
    exact div_le_div_of_nonneg_right (hD μ) hε.le
  have h4 := sum_fin_four_le_two_sqrt_sum_sq D
  calc |∏ μ, max 0 (1 - r μ / ε) - ∏ μ, max 0 (1 - r' μ / ε)|
      ≤ ∑ μ, |max 0 (1 - r μ / ε) - max 0 (1 - r' μ / ε)| := h1
    _ ≤ ∑ μ, D μ / ε := Finset.sum_le_sum fun μ _ => h2 μ
    _ = (∑ μ, D μ) / ε := by rw [Finset.sum_div]
    _ ≤ (2 * Real.sqrt (∑ μ, D μ ^ 2)) / ε := div_le_div_of_nonneg_right h4 hε.le
    _ = 2 / ε * Real.sqrt (∑ μ, D μ ^ 2) := by ring
section Cutoff
variable {X : Type*}
private theorem bestLipschitzConstant_nonneg (d : X → X → ℝ) (f : X → ℝ) :
    0 ≤ bestLipschitzConstant d f :=
  Real.sInf_nonneg fun _ hc => hc.1
private theorem bestLipschitzConstant_le {d : X → X → ℝ} {f : X → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x y, ‖f x - f y‖ ≤ C * d x y) : bestLipschitzConstant d f ≤ C :=
  csInf_le ⟨0, fun _ hc => hc.1⟩ ⟨hC, h⟩
private theorem norm_sub_le_bestLipschitzConstant_mul (d : X → X → ℝ) (hd : ∀ x y, 0 ≤ d x y)
    {f : X → ℝ} (hf : IsLipschitzFor d f) (x y : X) :
    ‖f x - f y‖ ≤ bestLipschitzConstant d f * d x y := by
  obtain ⟨C, hC, hCb⟩ := hf
  rcases (hd x y).eq_or_lt with h0 | h0
  · have := hCb x y
    rw [← h0, mul_zero] at this
    rw [← h0, mul_zero]
    exact this
  · rw [← div_le_iff₀ h0]
    refine le_csInf ⟨C, hC, hCb⟩ ?_
    rintro c ⟨-, hc⟩
    rw [div_le_iff₀ h0]
    exact hc x y
abbrev _root_.YangMills.SharedProofs.p9400 := @norm_sub_le_bestLipschitzConstant_mul
private theorem norm_le_uniformNorm {f : X → ℝ} (hf : IsBoundedFun f) (x : X) :
    ‖f x‖ ≤ uniformNorm f := by
  obtain ⟨C, hC⟩ := hf
  refine le_ciSup (f := fun x => ‖f x‖) ⟨C, ?_⟩ x
  rintro _ ⟨y, rfl⟩
  exact hC y
abbrev _root_.YangMills.SharedProofs.p10108 := @norm_le_uniformNorm
private theorem mul_cutoff_estimates [Nonempty X] (d : X → X → ℝ) (hd : ∀ x y, 0 ≤ d x y)
    {ε M : ℝ} (hε : 0 < ε) (hM : 1 ≤ M) (h2 : 2 * ε ≤ 1) {χ : X → ℝ}
    (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (hL : ∀ x z, |χ x - χ z| ≤ 2 / ε * d x z)
    {f : X → ℝ} (hb : IsBoundedFun f) (hl : IsLipschitzFor d f) :
    IsLipschitzFor d (fun x => χ x * f x) ∧
      max (uniformNorm fun x => χ x * f x)
          (2 * ε * bestLipschitzConstant d fun x => χ x * f x) ≤
        5 * max (uniformNorm f) (40 * M * bestLipschitzConstant d f) := by
  have hfS : ∀ x, |f x| ≤ uniformNorm f := fun x => by simpa using norm_le_uniformNorm hb x
  have hS0 : 0 ≤ uniformNorm f := (abs_nonneg _).trans (hfS (Classical.arbitrary X))
  have hΛ0 : 0 ≤ bestLipschitzConstant d f := bestLipschitzConstant_nonneg d f
  have hfΛ : ∀ x y, |f x - f y| ≤ bestLipschitzConstant d f * d x y :=
    fun x y => by simpa using norm_sub_le_bestLipschitzConstant_mul d hd hl x y
  generalize uniformNorm f = S at *
  generalize bestLipschitzConstant d f = Λ at *
  have hC : 0 ≤ Λ + 2 / ε * S := by positivity
  have hp : ∀ x z, ‖χ x * f x - χ z * f z‖ ≤ (Λ + 2 / ε * S) * d x z := by
    intro x z
    have e : χ x * f x - χ z * f z = χ x * (f x - f z) + (χ x - χ z) * f z := by ring
    rw [Real.norm_eq_abs, e]
    have h1 : |χ x * (f x - f z)| ≤ Λ * d x z := by
      rw [abs_mul, abs_of_nonneg (hχ x).1]
      have := mul_le_mul_of_nonneg_right (hχ x).2 (abs_nonneg (f x - f z))
      linarith [hfΛ x z]
    have h3 : |(χ x - χ z) * f z| ≤ 2 / ε * d x z * S := by
      rw [abs_mul]
      exact mul_le_mul (hL x z) (hfS z) (abs_nonneg _)
        (mul_nonneg (by positivity) (hd x z))
    have h4 := abs_add_le_abs_add_abs (χ x * (f x - f z)) ((χ x - χ z) * f z)
    have e2 : (Λ + 2 / ε * S) * d x z = Λ * d x z + 2 / ε * d x z * S := by ring
    rw [e2]
    linarith
  refine ⟨⟨_, hC, hp⟩, ?_⟩
  have hsup : uniformNorm (fun x => χ x * f x) ≤ S := by
    refine ciSup_le fun x => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hχ x).1]
    have := mul_le_mul_of_nonneg_right (hχ x).2 (abs_nonneg (f x))
    linarith [hfS x]
  have hlip : 2 * ε * bestLipschitzConstant d (fun x => χ x * f x) ≤ 2 * ε * Λ + 4 * S := by
    have h5 := mul_le_mul_of_nonneg_left (bestLipschitzConstant_le hC hp)
      (by positivity : 0 ≤ 2 * ε)
    have e3 : 2 * ε * (Λ + 2 / ε * S) = 2 * ε * Λ + 4 * S := by
      field_simp
      ring
    rw [e3] at h5
    exact h5
  have hN1 : S ≤ max S (40 * M * Λ) := le_max_left _ _
  have hN2 : 40 * M * Λ ≤ max S (40 * M * Λ) := le_max_right _ _
  have h6 : 2 * ε * Λ ≤ 40 * M * Λ := by
    refine mul_le_mul_of_nonneg_right ?_ hΛ0
    linarith
  refine max_le ?_ ?_ <;> linarith
end Cutoff
private theorem mul_floor_le_and_lt {s ε : ℝ} (hε : 0 < ε) :
    ε * (⌊s / ε⌋ : ℝ) ≤ s ∧ s < ε * ((⌊s / ε⌋ : ℝ) + 1) := by
  have hl : ((⌊s / ε⌋ : ℤ) : ℝ) ≤ s / ε := Int.floor_le _
  have hu : s / ε < (⌊s / ε⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  exact ⟨(le_div_iff₀' hε).mp hl, (div_lt_iff₀' hε).mp hu⟩
private theorem le_abs_sub_mul_int_of_ne {s ε : ℝ} (hε : 0 < ε) {k : ℤ} (h0 : k ≠ ⌊s / ε⌋)
    (h1 : k ≠ ⌊s / ε⌋ + 1) : ε ≤ |s - ε * (k : ℝ)| := by
  obtain ⟨hl, hu⟩ := mul_floor_le_and_lt (s := s) hε
  generalize ⌊s / ε⌋ = n at *
  rcases lt_or_gt_of_ne h0 with h | h
  · have h2 : (k : ℝ) + 1 ≤ n := by exact_mod_cast h
    have h3 := mul_le_mul_of_nonneg_left h2 hε.le
    refine le_trans ?_ (le_abs_self _)
    linarith
  · have h2 : n + 2 ≤ k := by omega
    have h3 : (n : ℝ) + 2 ≤ k := by exact_mod_cast h2
    have h4 := mul_le_mul_of_nonneg_left h3 hε.le
    refine le_trans ?_ (neg_le_abs _)
    linarith
private theorem floor_neighbours_hat_sum {s ε : ℝ} (hε : 0 < ε) :
    |s - ε * ((⌊s / ε⌋ : ℤ) : ℝ)| ≤ ε ∧ |s - ε * ((⌊s / ε⌋ + 1 : ℤ) : ℝ)| ≤ ε ∧
      max 0 (1 - |s - ε * ((⌊s / ε⌋ : ℤ) : ℝ)| / ε) +
        max 0 (1 - |s - ε * ((⌊s / ε⌋ + 1 : ℤ) : ℝ)| / ε) = 1 := by
  obtain ⟨hl, hu⟩ := mul_floor_le_and_lt (s := s) hε
  generalize ⌊s / ε⌋ = n at *
  push_cast
  have e0 : |s - ε * (n : ℝ)| = s - ε * n := abs_of_nonneg (by linarith)
  have e1 : |s - ε * ((n : ℝ) + 1)| = ε * ((n : ℝ) + 1) - s := by
    rw [abs_of_nonpos (by linarith)]
    ring
  rw [e0, e1]
  have hr0 : (s - ε * n) / ε ≤ 1 := (div_le_one hε).mpr (by nlinarith)
  have hr1 : (ε * ((n : ℝ) + 1) - s) / ε ≤ 1 := (div_le_one hε).mpr (by linarith)
  refine ⟨by nlinarith, by linarith, ?_⟩
  rw [max_eq_right (by linarith), max_eq_right (by linarith)]
  field_simp
  ring
private theorem card_Ioo_floor_ceil_le (c : ℝ) {w : ℝ} (hw : 0 < w) :
    (((Finset.Ioo ⌊c - w⌋ ⌈c + w⌉).card : ℕ) : ℝ) ≤ 2 * w + 1 := by
  rw [Int.card_Ioo]
  have h1 : ((⌈c + w⌉ : ℤ) : ℝ) < c + w + 1 := Int.ceil_lt_add_one _
  have h2 : c - w < (⌊c - w⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  generalize ⌈c + w⌉ = a at *
  generalize ⌊c - w⌋ = b at *
  rcases le_total 0 (a - b - 1) with h | h
  · have e : (((a - b - 1).toNat : ℕ) : ℝ) = (((a - b - 1).toNat : ℤ) : ℝ) := by push_cast; rfl
    rw [e, Int.toNat_of_nonneg h]
    push_cast
    linarith
  · rw [Int.toNat_of_nonpos h]
    simp only [Nat.cast_zero]
    linarith
private theorem card_piFinset_Ioo_le (c : Fin 4 → ℝ) {w : ℝ} (hw : 0 < w) :
    (((Fintype.piFinset fun μ => Finset.Ioo ⌊c μ - w⌋ ⌈c μ + w⌉).card : ℕ) : ℝ) ≤
      (2 * w + 1) ^ 4 := by
  rw [Fintype.card_piFinset]
  push_cast
  calc ∏ μ, (((Finset.Ioo ⌊c μ - w⌋ ⌈c μ + w⌉).card : ℕ) : ℝ)
      ≤ ∏ _μ : Fin 4, (2 * w + 1) :=
        Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
          (fun μ _ => card_Ioo_floor_ceil_le (c μ) hw)
    _ = (2 * w + 1) ^ 4 := by simp
private theorem mem_Ioo_of_abs_sub_mul_lt {s ε R : ℝ} (hε : 0 < ε) {k : ℤ}
    (h : |s - ε * (k : ℝ)| < R + ε) :
    k ∈ Finset.Ioo ⌊s / ε - (R / ε + 1)⌋ ⌈s / ε + (R / ε + 1)⌉ := by
  rw [abs_lt] at h
  obtain ⟨h1, h2⟩ := h
  have e : R / ε + 1 = (R + ε) / ε := by field_simp
  rw [e, Finset.mem_Ioo, Int.floor_lt, Int.lt_ceil, ← sub_div, ← add_div]
  constructor
  · rw [div_lt_iff₀' hε]
    linarith
  · rw [lt_div_iff₀' hε]
    linarith
private theorem ncard_le_card_of_subset_image {ι : Type*} {A : Set (Fin 4 → ℝ)} {F : Finset ι}
    (g : ι → Fin 4 → ℝ) (h : A ⊆ g '' (F : Set ι)) : A.ncard ≤ F.card := by
  refine (Set.ncard_le_ncard h (F.finite_toSet.image g)).trans ?_
  refine (Set.ncard_image_le F.finite_toSet).trans ?_
  rw [Set.ncard_coe_finset]
private def intLatticePoint (ε : ℝ) (k : Fin 4 → ℤ) : Fin 4 → ℝ := fun μ => ε * (k μ : ℝ)
private theorem intLatticePoint_injective {ε : ℝ} (hε : 0 < ε) :
    Function.Injective (intLatticePoint ε) := by
  intro k k' h
  funext μ
  have h1 : ε * (k μ : ℝ) = ε * (k' μ : ℝ) := congrFun h μ
  exact_mod_cast mul_left_cancel₀ hε.ne' h1
abbrev _root_.YangMills.DeltaSharedProofs.p4422 := @intLatticePoint_injective
private theorem scaledIntLattice_eq_range (ε : ℝ) :
    scaledIntLattice ε = Set.range (intLatticePoint ε) := by
  ext α
  constructor
  · intro h
    choose k hk using h
    exact ⟨k, funext fun μ => (hk μ).symm⟩
  · rintro ⟨k, rfl⟩ μ
    exact ⟨k μ, rfl⟩
private theorem hatFunction_mem_unitInterval {ε : ℝ} (hε : 0 < ε) (α x : Fin 4 → ℝ) :
    0 ≤ hatFunction ε α x ∧ hatFunction ε α x ≤ 1 :=
  hatProduct_mem_unitInterval (fun _ => abs_nonneg _) hε
private theorem abs_sub_lt_of_hatFunction_ne_zero {ε : ℝ} (hε : 0 < ε) {α x : Fin 4 → ℝ}
    (h : hatFunction ε α x ≠ 0) (μ : Fin 4) : |x μ - α μ| < ε :=
  lt_of_hatProduct_ne_zero (r := fun μ => |x μ - α μ|) hε h μ
private theorem mem_piFinset_of_hatFunction_ne_zero {ε : ℝ} (hε : 0 < ε) {x : Fin 4 → ℝ}
    {k : Fin 4 → ℤ} (h : hatFunction ε (intLatticePoint ε k) x ≠ 0) :
    k ∈ Fintype.piFinset fun μ => ({⌊x μ / ε⌋, ⌊x μ / ε⌋ + 1} : Finset ℤ) := by
  rw [Fintype.mem_piFinset]
  intro μ
  by_contra hc
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  have h1 := le_abs_sub_mul_int_of_ne (s := x μ) hε hc.1 hc.2
  have h2 := abs_sub_lt_of_hatFunction_ne_zero hε h μ
  exact absurd h2 (not_lt.mpr h1)
private theorem hatFunction_support_finite {ε : ℝ} (hε : 0 < ε) (x : Fin 4 → ℝ) :
    {α | α ∈ scaledIntLattice ε ∧ hatFunction ε α x ≠ 0}.Finite := by
  classical
  refine ((Fintype.piFinset fun μ =>
    ({⌊x μ / ε⌋, ⌊x μ / ε⌋ + 1} : Finset ℤ)).finite_toSet.image
    (intLatticePoint ε)).subset ?_
  rintro α ⟨hα, h⟩
  rw [scaledIntLattice_eq_range] at hα
  obtain ⟨k, rfl⟩ := hα
  exact ⟨k, mem_piFinset_of_hatFunction_ne_zero hε h, rfl⟩
private theorem hatFunction_finsum_eq_one {ε : ℝ} (hε : 0 < ε) (x : Fin 4 → ℝ) :
    ∑ᶠ α : scaledIntLattice ε, hatFunction ε α x = 1 := by
  classical
  rw [finsum_set_coe_eq_finsum_mem (f := fun α => hatFunction ε α x) (scaledIntLattice ε),
    scaledIntLattice_eq_range,
    finsum_mem_range (f := fun α => hatFunction ε α x) (intLatticePoint_injective hε)]
  rw [finsum_eq_sum_of_support_subset
    (s := Fintype.piFinset fun μ => ({⌊x μ / ε⌋, ⌊x μ / ε⌋ + 1} : Finset ℤ))]
  · have e : ∀ k : Fin 4 → ℤ, hatFunction ε (intLatticePoint ε k) x =
        ∏ μ, max 0 (1 - |x μ - ε * (k μ : ℝ)| / ε) := fun _ => rfl
    simp_rw [e]
    rw [← Finset.prod_univ_sum (fun μ => ({⌊x μ / ε⌋, ⌊x μ / ε⌋ + 1} : Finset ℤ))
      (fun μ j => max 0 (1 - |x μ - ε * (j : ℝ)| / ε))]
    refine Finset.prod_eq_one fun μ _ => ?_
    rw [Finset.sum_pair (by omega)]
    exact (floor_neighbours_hat_sum hε).2.2
  · intro k hk
    exact mem_piFinset_of_hatFunction_ne_zero hε hk
private theorem tsupport_hatFunction_subset {ε : ℝ} (hε : 0 < ε) (α : Fin 4 → ℝ) :
    tsupport (hatFunction ε α) ⊆ closedBallR4 α (2 * ε) := by
  have hclosed : IsClosed {y : Fin 4 → ℝ | ∀ μ, |y μ - α μ| ≤ ε} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun μ =>
      isClosed_le (((continuous_apply μ).sub continuous_const).abs) continuous_const
  have hsub : tsupport (hatFunction ε α) ⊆ {y : Fin 4 → ℝ | ∀ μ, |y μ - α μ| ≤ ε} :=
    closure_minimal (fun y hy μ => (abs_sub_lt_of_hatFunction_ne_zero hε hy μ).le) hclosed
  intro y hy
  exact sqrt_sum_sq_le_two_mul (w := y - α) hε (hsub hy)
private theorem abs_hatFunction_sub_le {ε : ℝ} (hε : 0 < ε) (α x z : Fin 4 → ℝ) :
    |hatFunction ε α x - hatFunction ε α z| ≤ 2 / ε * euclidDistR4 x z := by
  have h := abs_hatProduct_sub_le (r := fun μ => |x μ - α μ|) (r' := fun μ => |z μ - α μ|)
    (D := fun μ => |x μ - z μ|) hε (fun _ => abs_nonneg _) (fun _ => abs_nonneg _) (fun μ => by
      have := abs_norm_sub_norm_le (x μ - α μ) (z μ - α μ)
      simpa using this)
  simpa [hatFunction, euclidDistR4, euclidNormVec, sq_abs] using h
private theorem abs_sub_le_of_mem_closedBallR4 {x y : Fin 4 → ℝ} {R : ℝ}
    (h : x ∈ closedBallR4 y R) (μ : Fin 4) : |x μ - y μ| ≤ R := by
  have h1 : (x μ - y μ) ^ 2 ≤ ∑ ν, (x ν - y ν) ^ 2 :=
    Finset.single_le_sum (f := fun ν => (x ν - y ν) ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ μ)
  exact (Real.abs_le_sqrt h1).trans h
private theorem hatFunction_count_le {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R)
    {f : (Fin 4 → ℝ) → ℝ} (hf : ∃ y, tsupport f ⊆ closedBallR4 y R) :
    {α | α ∈ scaledIntLattice ε ∧ ∃ x, hatFunction ε α x * f x ≠ 0}.Finite ∧
      ({α | α ∈ scaledIntLattice ε ∧ ∃ x, hatFunction ε α x * f x ≠ 0}.ncard : ℝ) ≤
        (2 * R / ε + 3) ^ 4 := by
  classical
  obtain ⟨y, hy⟩ := hf
  have hsub : {α | α ∈ scaledIntLattice ε ∧ ∃ x, hatFunction ε α x * f x ≠ 0} ⊆
      intLatticePoint ε ''
      ((Fintype.piFinset fun μ => Finset.Ioo ⌊y μ / ε - (R / ε + 1)⌋ ⌈y μ / ε + (R / ε + 1)⌉ :
        Finset (Fin 4 → ℤ)) : Set (Fin 4 → ℤ)) := by
    rintro α ⟨hα, x, hx⟩
    rw [scaledIntLattice_eq_range] at hα
    obtain ⟨k, rfl⟩ := hα
    refine ⟨k, ?_, rfl⟩
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro μ
    have h1 := abs_sub_lt_of_hatFunction_ne_zero hε (left_ne_zero_of_mul hx) μ
    have h2 : x ∈ tsupport f := subset_tsupport f (right_ne_zero_of_mul hx)
    have h3 := abs_sub_le_of_mem_closedBallR4 (hy h2) μ
    refine mem_Ioo_of_abs_sub_mul_lt hε ?_
    have h4 : y μ - ε * (k μ : ℝ) = (x μ - ε * (k μ : ℝ)) - (x μ - y μ) := by ring
    have h5 : |x μ - ε * (k μ : ℝ)| < ε := h1
    rw [h4]
    have h6 := abs_add_le_abs_add_abs (x μ - ε * (k μ : ℝ)) (-(x μ - y μ))
    rw [abs_neg, ← sub_eq_add_neg] at h6
    linarith
  refine ⟨(Finset.finite_toSet _ |>.image _).subset hsub, ?_⟩
  have h1 := ncard_le_card_of_subset_image _ hsub
  have h2 := card_piFinset_Ioo_le (fun μ => y μ / ε) (by positivity : 0 < R / ε + 1)
  have e : 2 * (R / ε + 1) + 1 = 2 * R / ε + 3 := by ring
  rw [e] at h2
  exact (Nat.cast_le.mpr h1).trans h2
private theorem torusEuclidNorm_eq_sqrt {ℓ : ℝ} (x : Torus4 ℓ) :
    torusEuclidNorm x = Real.sqrt (∑ μ, ‖x μ‖ ^ 2) := by apply _root_.YangMills.Construction.AmbientPoints.torusEuclidNorm_eq_sqrt <;> assumption
private theorem euclidDistTorus_nonneg {ℓ : ℝ} (x z : Torus4 ℓ) : 0 ≤ euclidDistTorus x z := by
  rw [euclidDistTorus, torusEuclidNorm_eq_sqrt]
  exact Real.sqrt_nonneg _
abbrev _root_.YangMills.SharedProofs.p31350 := @euclidDistTorus_nonneg
private theorem norm_apply_le_torusEuclidNorm {ℓ : ℝ} (x : Torus4 ℓ) (μ : Fin 4) :
    ‖x μ‖ ≤ torusEuclidNorm x := by
  rw [torusEuclidNorm_eq_sqrt]
  have h1 : ‖x μ‖ ^ 2 ≤ ∑ ν, ‖x ν‖ ^ 2 :=
    Finset.single_le_sum (f := fun ν => ‖x ν‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ μ)
  exact (le_abs_self _).trans (Real.abs_le_sqrt h1)
abbrev _root_.YangMills.SharedProofs.p28925 := @norm_apply_le_torusEuclidNorm
private theorem torusHatFunction_mem_unitInterval {ℓ ε : ℝ} (hε : 0 < ε) (α : Fin 4 → ℝ)
    (x : Torus4 ℓ) : 0 ≤ torusHatFunction ε α x ∧ torusHatFunction ε α x ≤ 1 :=
  hatProduct_mem_unitInterval (fun _ => norm_nonneg _) hε
private theorem norm_sub_lt_of_torusHatFunction_ne_zero {ℓ ε : ℝ} (hε : 0 < ε)
    {α : Fin 4 → ℝ} {x : Torus4 ℓ} (h : torusHatFunction ε α x ≠ 0) (μ : Fin 4) :
    ‖x μ - ((α μ : ℝ) : AddCircle ℓ)‖ < ε :=
  lt_of_hatProduct_ne_zero (r := fun μ => ‖x μ - ((α μ : ℝ) : AddCircle ℓ)‖) hε h μ
private theorem tsupport_torusHatFunction_subset {ℓ ε : ℝ} (hε : 0 < ε) (α : Fin 4 → ℝ) :
    tsupport (torusHatFunction (ℓ := ℓ) ε α) ⊆ closedBallTorus (torusProj ℓ α) (2 * ε) := by
  have hclosed : IsClosed {y : Torus4 ℓ | ∀ μ, ‖y μ - ((α μ : ℝ) : AddCircle ℓ)‖ ≤ ε} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun μ =>
      isClosed_le (((continuous_apply μ).sub continuous_const).norm) continuous_const
  have hsub : tsupport (torusHatFunction (ℓ := ℓ) ε α) ⊆
      {y : Torus4 ℓ | ∀ μ, ‖y μ - ((α μ : ℝ) : AddCircle ℓ)‖ ≤ ε} :=
    closure_minimal (fun y hy μ => (norm_sub_lt_of_torusHatFunction_ne_zero hε hy μ).le) hclosed
  intro y hy
  change torusEuclidNorm (y - torusProj ℓ α) ≤ 2 * ε
  rw [torusEuclidNorm_eq_sqrt]
  exact sqrt_sum_sq_le_two_mul (w := fun μ => ‖(y - torusProj ℓ α) μ‖) hε
    (fun μ => by rw [abs_norm]; exact hsub hy μ)
private theorem abs_torusHatFunction_sub_le {ℓ ε : ℝ} (hε : 0 < ε) (α : Fin 4 → ℝ)
    (x z : Torus4 ℓ) :
    |torusHatFunction ε α x - torusHatFunction ε α z| ≤ 2 / ε * euclidDistTorus x z := by
  rw [euclidDistTorus, torusEuclidNorm_eq_sqrt]
  refine abs_hatProduct_sub_le (r := fun μ => ‖x μ - ((α μ : ℝ) : AddCircle ℓ)‖)
    (r' := fun μ => ‖z μ - ((α μ : ℝ) : AddCircle ℓ)‖) (D := fun μ => ‖(x - z) μ‖) hε
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) (fun μ => ?_)
  have h := abs_norm_sub_norm_le (x μ - ((α μ : ℝ) : AddCircle ℓ))
    (z μ - ((α μ : ℝ) : AddCircle ℓ))
  rwa [sub_sub_sub_cancel_right] at h
private theorem le_norm_coe_sub_mul_int {ε ℓ : ℝ} (hε : 0 < ε) {q : ℕ} (hℓ : ℓ = q * ε) (s : ℝ)
    {k : ℤ} (h : ∀ c : ℤ, k + c * q ≠ ⌊s / ε⌋ ∧ k + c * q ≠ ⌊s / ε⌋ + 1) :
    ε ≤ ‖((s - ε * (k : ℝ) : ℝ) : AddCircle ℓ)‖ := by
  rw [AddCircle.norm_eq]
  have h1 := le_abs_sub_mul_int_of_ne (s := s) hε (h (round (ℓ⁻¹ * (s - ε * (k : ℝ))))).1
    (h (round (ℓ⁻¹ * (s - ε * (k : ℝ))))).2
  generalize round (ℓ⁻¹ * (s - ε * (k : ℝ))) = j at *
  have e : s - ε * ((k + j * q : ℤ) : ℝ) = s - ε * (k : ℝ) - (j : ℝ) * ℓ := by
    push_cast
    rw [hℓ]
    ring
  rwa [e] at h1
private theorem norm_coe_add_int_mul_eq_abs {ε ℓ : ℝ} (hε : 0 < ε) {q : ℕ} (hq : 3 ≤ q)
    (hℓ : ℓ = q * ε) {r : ℝ} (hr : |r| ≤ ε) (c : ℤ) :
    ‖((r + (c : ℝ) * ℓ : ℝ) : AddCircle ℓ)‖ = |r| := by
  have hq' : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hℓ3 : 3 * ε ≤ ℓ := by
    rw [hℓ]
    exact mul_le_mul_of_nonneg_right hq' hε.le
  have hpos : 0 < ℓ := by linarith
  have h0 : (((c : ℝ) * ℓ : ℝ) : AddCircle ℓ) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨c, by simp⟩
  rw [AddCircle.coe_add, h0, add_zero, AddCircle.norm_coe_eq_abs_iff ℓ hpos.ne', abs_of_pos hpos]
  linarith
private theorem addCircle_hat_sum_eq_one {ε ℓ : ℝ} (hε : 0 < ε) {q : ℕ} (hq : 3 ≤ q)
    (hℓ : ℓ = q * ε) (t : AddCircle ℓ) :
    ∑ j ∈ Finset.Ico (0 : ℤ) q, max 0 (1 - ‖t - ((ε * (j : ℝ) : ℝ) : AddCircle ℓ)‖ / ε) = 1 := by
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective t
  change ∑ j ∈ Finset.Ico (0 : ℤ) q, max 0 (1 - ‖(s : AddCircle ℓ) -
    ((ε * (j : ℝ) : ℝ) : AddCircle ℓ)‖ / ε) = 1
  simp_rw [← AddCircle.coe_sub]
  have hq0 : (0 : ℤ) < q := by exact_mod_cast (by omega : 0 < q)
  obtain ⟨h0, h1, hsum⟩ := floor_neighbours_hat_sum (s := s) hε
  have hmod : ∀ m : ℤ, ∃ c : ℤ, m % (q : ℤ) = m + c * q :=
    fun m => ⟨-(m / q), by rw [Int.emod_def]; ring⟩
  have hin : ∀ m : ℤ, m % (q : ℤ) ∈ Finset.Ico (0 : ℤ) q := fun m =>
    Finset.mem_Ico.mpr ⟨Int.emod_nonneg _ hq0.ne', Int.emod_lt_of_pos _ hq0⟩
  have hback : ∀ (j : ℤ) (c : ℤ), j ∈ Finset.Ico (0 : ℤ) q → (j + c * q) % (q : ℤ) = j := by
    intro j c hj
    rw [Int.add_mul_emod_self_right]
    exact Int.emod_eq_of_lt (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2
  have hne : ⌊s / ε⌋ % (q : ℤ) ≠ (⌊s / ε⌋ + 1) % (q : ℤ) := by
    intro h
    have h2 : (q : ℤ) ∣ (⌊s / ε⌋ + 1) - ⌊s / ε⌋ := Int.ModEq.dvd h
    have h3 : (q : ℤ) ∣ 1 := by simpa using h2
    have := Int.le_of_dvd one_pos h3
    omega
  have value : ∀ (m : ℤ), |s - ε * (m : ℝ)| ≤ ε →
      ‖((s - ε * ((m % (q : ℤ) : ℤ) : ℝ) : ℝ) : AddCircle ℓ)‖ = |s - ε * (m : ℝ)| := by
    intro m hm
    obtain ⟨c, hc⟩ := hmod m
    have e : s - ε * ((m % (q : ℤ) : ℤ) : ℝ) = (s - ε * (m : ℝ)) + ((-c : ℤ) : ℝ) * ℓ := by
      rw [hc, hℓ]
      push_cast
      ring
    rw [e]
    exact norm_coe_add_int_mul_eq_abs hε hq hℓ hm (-c)
  rw [Finset.sum_eq_add (⌊s / ε⌋ % (q : ℤ)) ((⌊s / ε⌋ + 1) % (q : ℤ)) hne ?_
    (fun h => absurd (hin _) h) (fun h => absurd (hin _) h)]
  · rw [value _ h0, value _ h1]
    exact hsum
  · rintro j hj ⟨hja, hjb⟩
    refine hatFactor_eq_zero_of_le hε
      (le_norm_coe_sub_mul_int hε hℓ s fun c => ⟨fun h => hja ?_, fun h => hjb ?_⟩)
    · rw [← h]
      exact (hback j c hj).symm
    · rw [← h]
      exact (hback j c hj).symm
private theorem scaledIntLatticeFundDomain_eq_image {ℓ ε : ℝ} (hε : 0 < ε) {q : ℕ}
    (hℓ : ℓ = q * ε) :
    scaledIntLatticeFundDomain ℓ ε = intLatticePoint ε ''
      ((Fintype.piFinset fun _ : Fin 4 => Finset.Ico (0 : ℤ) q : Finset (Fin 4 → ℤ)) :
        Set (Fin 4 → ℤ)) := by
  ext α
  constructor
  · rintro ⟨hα, hr⟩
    rw [scaledIntLattice_eq_range] at hα
    obtain ⟨k, rfl⟩ := hα
    refine ⟨k, ?_, rfl⟩
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro μ
    obtain ⟨h0, h1⟩ := hr μ
    have h0' : ε * 0 ≤ ε * (k μ : ℝ) := by simpa [intLatticePoint] using h0
    have h1' : ε * (k μ : ℝ) < ε * (q : ℝ) := by
      have : ε * (k μ : ℝ) < ℓ := h1
      rwa [hℓ, mul_comm (q : ℝ)] at this
    have h2 : (0 : ℝ) ≤ k μ := le_of_mul_le_mul_left h0' hε
    have h3 : (k μ : ℝ) < q := lt_of_mul_lt_mul_left h1' hε.le
    exact Finset.mem_Ico.mpr ⟨by exact_mod_cast h2, by exact_mod_cast h3⟩
  · rintro ⟨k, hk, rfl⟩
    rw [Finset.mem_coe, Fintype.mem_piFinset] at hk
    refine ⟨by rw [scaledIntLattice_eq_range]; exact ⟨k, rfl⟩, fun μ => ?_⟩
    obtain ⟨h0, h1⟩ := Finset.mem_Ico.mp (hk μ)
    have h2 : (0 : ℝ) ≤ k μ := by exact_mod_cast h0
    have h3 : (k μ : ℝ) < q := by exact_mod_cast h1
    refine ⟨mul_nonneg hε.le h2, ?_⟩
    change ε * (k μ : ℝ) < ℓ
    rw [hℓ, mul_comm (q : ℝ)]
    exact mul_lt_mul_of_pos_left h3 hε
private theorem torusHatFunction_finsum_eq_one {ℓ ε : ℝ} (hε : 0 < ε) {q : ℕ} (hq : 3 ≤ q)
    (hℓ : ℓ = q * ε) (x : Torus4 ℓ) :
    ∑ᶠ α : scaledIntLatticeFundDomain ℓ ε, torusHatFunction ε α x = 1 := by
  classical
  rw [finsum_set_coe_eq_finsum_mem (f := fun α => torusHatFunction ε α x)
      (scaledIntLatticeFundDomain ℓ ε),
    scaledIntLatticeFundDomain_eq_image hε hℓ,
    finsum_mem_image (f := fun α => torusHatFunction ε α x) (intLatticePoint_injective hε).injOn,
    finsum_mem_coe_finset]
  have e : ∀ k : Fin 4 → ℤ, torusHatFunction ε (intLatticePoint ε k) x =
      ∏ μ, max 0 (1 - ‖x μ - ((ε * (k μ : ℝ) : ℝ) : AddCircle ℓ)‖ / ε) := fun _ => rfl
  simp_rw [e]
  rw [← Finset.prod_univ_sum (fun _ : Fin 4 => Finset.Ico (0 : ℤ) q)
    (fun μ j => max 0 (1 - ‖x μ - ((ε * (j : ℝ) : ℝ) : AddCircle ℓ)‖ / ε))]
  exact Finset.prod_eq_one fun μ _ => addCircle_hat_sum_eq_one hε hq hℓ (x μ)
private theorem torusHatFunction_count_le {ℓ ε R : ℝ} (hε : 0 < ε) {q : ℕ} (hq : 3 ≤ q)
    (hℓ : ℓ = q * ε) (hR : 0 < R) {f : Torus4 ℓ → ℝ} (hf : ∃ y, tsupport f ⊆ closedBallTorus y R) :
    ({α | α ∈ scaledIntLatticeFundDomain ℓ ε ∧ ∃ x, torusHatFunction ε α x * f x ≠ 0}.ncard : ℝ) ≤
      min ((2 * R / ε + 3) ^ 4) ((ℓ / ε) ^ 4) := by
  classical
  obtain ⟨y, hy⟩ := hf
  choose s hs _ using fun μ => exists_coe_eq_abs_eq_norm (y μ)
  refine le_min ?_ ?_
  · have hsub : {α | α ∈ scaledIntLatticeFundDomain ℓ ε ∧
          ∃ x, torusHatFunction ε α x * f x ≠ 0} ⊆
        (fun k' : Fin 4 → ℤ => intLatticePoint ε fun μ => k' μ % (q : ℤ)) ''
        ((Fintype.piFinset fun μ =>
          Finset.Ioo ⌊s μ / ε - (R / ε + 1)⌋ ⌈s μ / ε + (R / ε + 1)⌉ : Finset (Fin 4 → ℤ)) :
            Set (Fin 4 → ℤ)) := by
      rintro α ⟨hα, x, hx⟩
      rw [scaledIntLatticeFundDomain_eq_image hε hℓ] at hα
      obtain ⟨k, hk, rfl⟩ := hα
      rw [Finset.mem_coe, Fintype.mem_piFinset] at hk
      have hlift : ∀ μ, ∃ k' : ℤ, k' % (q : ℤ) = k μ ∧ |s μ - ε * (k' : ℝ)| < R + ε := by
        intro μ
        have h1 := norm_sub_lt_of_torusHatFunction_ne_zero hε (left_ne_zero_of_mul hx) μ
        have h2 : x ∈ tsupport f := subset_tsupport f (right_ne_zero_of_mul hx)
        have h3 : ‖(x - y) μ‖ ≤ R := (norm_apply_le_torusEuclidNorm _ μ).trans (hy h2)
        have h4 : ‖y μ - ((ε * (k μ : ℝ) : ℝ) : AddCircle ℓ)‖ < R + ε := by
          have e : y μ - ((ε * (k μ : ℝ) : ℝ) : AddCircle ℓ) =
              (x μ - ((ε * (k μ : ℝ) : ℝ) : AddCircle ℓ)) - (x - y) μ := by
            simp only [Pi.sub_apply]
            abel
          have h1' : ‖x μ - ((ε * (k μ : ℝ) : ℝ) : AddCircle ℓ)‖ < ε := h1
          rw [e]
          have := norm_sub_le (x μ - ((ε * (k μ : ℝ) : ℝ) : AddCircle ℓ)) ((x - y) μ)
          linarith
        rw [← hs μ, ← AddCircle.coe_sub, AddCircle.norm_eq] at h4
        generalize round (ℓ⁻¹ * (s μ - ε * (k μ : ℝ))) = j at h4
        refine ⟨k μ + j * q, ?_, ?_⟩
        · rw [Int.add_mul_emod_self_right]
          obtain ⟨h0, h1⟩ := Finset.mem_Ico.mp (hk μ)
          exact Int.emod_eq_of_lt h0 h1
        · have e : s μ - ε * ((k μ + j * q : ℤ) : ℝ) = s μ - ε * (k μ : ℝ) - (j : ℝ) * ℓ := by
            push_cast
            rw [hℓ]
            ring
          rwa [e]
      choose k' hk'1 hk'2 using hlift
      refine ⟨k', ?_, ?_⟩
      · rw [Finset.mem_coe, Fintype.mem_piFinset]
        exact fun μ => mem_Ioo_of_abs_sub_mul_lt hε (hk'2 μ)
      · change intLatticePoint ε (fun μ => k' μ % (q : ℤ)) = intLatticePoint ε k
        congr 1
        exact funext hk'1
    have h1 := ncard_le_card_of_subset_image _ hsub
    have h2 := card_piFinset_Ioo_le (fun μ => s μ / ε) (by positivity : 0 < R / ε + 1)
    have e : 2 * (R / ε + 1) + 1 = 2 * R / ε + 3 := by ring
    rw [e] at h2
    exact (Nat.cast_le.mpr h1).trans h2
  · have hsub2 : {α | α ∈ scaledIntLatticeFundDomain ℓ ε ∧
          ∃ x, torusHatFunction ε α x * f x ≠ 0} ⊆ intLatticePoint ε ''
        ((Fintype.piFinset fun _ : Fin 4 => Finset.Ico (0 : ℤ) q : Finset (Fin 4 → ℤ)) :
          Set (Fin 4 → ℤ)) := by
      intro α h
      have h1 := h.1
      rwa [scaledIntLatticeFundDomain_eq_image hε hℓ] at h1
    have h1 := ncard_le_card_of_subset_image _ hsub2
    have e : (((Fintype.piFinset fun _ : Fin 4 => Finset.Ico (0 : ℤ) q).card : ℕ) : ℝ) =
        (ℓ / ε) ^ 4 := by
      rw [Fintype.card_piFinset, hℓ]
      simp [Int.card_Ico, hε.ne']
    rw [← e]
    exact Nat.cast_le.mpr h1
theorem hatPartitionOfUnity_prop_holds : hatPartitionOfUnity_prop := by
  refine ⟨fun ε hε => ⟨hatFunction_mem_unitInterval hε,
    fun x => ⟨hatFunction_support_finite hε x, hatFunction_finsum_eq_one hε x⟩,
    fun α x h μ => abs_sub_lt_of_hatFunction_ne_zero hε h μ, tsupport_hatFunction_subset hε,
    abs_hatFunction_sub_le hε, ?_, fun R hR f hf => hatFunction_count_le hε hR hf⟩,
    fun ℓ ε hε q hq hℓ => ⟨torusHatFunction_mem_unitInterval hε,
      torusHatFunction_finsum_eq_one hε hq hℓ, tsupport_torusHatFunction_subset hε,
      abs_torusHatFunction_sub_le hε, ?_, fun R hR f hf => torusHatFunction_count_le hε hq hℓ hR hf⟩⟩
  · intro M hM h2 f hb hl α
    exact mul_cutoff_estimates euclidDistR4 (fun _ _ => Real.sqrt_nonneg _) hε hM h2
      (hatFunction_mem_unitInterval hε α) (abs_hatFunction_sub_le hε α) hb hl
  · intro M hM h2 f hb hl α
    exact mul_cutoff_estimates euclidDistTorus euclidDistTorus_nonneg hε hM h2
      (torusHatFunction_mem_unitInterval hε α) (abs_torusHatFunction_sub_le hε α) hb hl
end SystemOfAdmissibleConstants
end YangMills.Construction
end
