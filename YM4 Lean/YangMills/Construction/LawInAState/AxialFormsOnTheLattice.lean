import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace AxialForms
def intervalSum : ℤ → (ℤ → ℝ) → ℝ
  | Int.ofNat k, F => ∑ i ∈ Finset.range k, F i
  | Int.negSucc k, F => -∑ i ∈ Finset.range (k + 1), F (-(i : ℤ) - 1)
theorem intervalSum_zero (F : ℤ → ℝ) : intervalSum 0 F = 0 := by
  change intervalSum (Int.ofNat 0) F = 0
  simp [intervalSum]
theorem intervalSum_succ (m : ℤ) (F : ℤ → ℝ) : intervalSum (m + 1) F = intervalSum m F + F m := by
  cases m with
  | ofNat k =>
    have e : (Int.ofNat k + 1 : ℤ) = Int.ofNat (k + 1) := rfl
    rw [e]
    simp [intervalSum, Finset.sum_range_succ]
  | negSucc k =>
    cases k with
    | zero =>
      have e : (Int.negSucc 0 + 1 : ℤ) = Int.ofNat 0 := rfl
      rw [e]
      simp [intervalSum]
    | succ k =>
      have e : (Int.negSucc (k + 1) + 1 : ℤ) = Int.negSucc k := by
        simp only [Int.negSucc_eq]
        push_cast
        ring
      rw [e]
      simp only [intervalSum]
      rw [Finset.sum_range_succ _ (k + 1)]
      have e2 : (-((k + 1 : ℕ) : ℤ) - 1) = Int.negSucc (k + 1) := by
        simp only [Int.negSucc_eq]
        push_cast
        ring
      rw [e2]
      ring
theorem intervalSum_eq_sub (S F : ℤ → ℝ) (hS : ∀ m, S (m + 1) = S m + F m) (m : ℤ) :
    intervalSum m F = S m - S 0 := by
  induction m using Int.induction_on with
  | zero => simp [intervalSum_zero]
  | succ i ih =>
    rw [intervalSum_succ, ih, hS]
    ring
  | pred i ih =>
    have h1 := intervalSum_succ (-(i : ℤ) - 1) F
    have h2 := hS (-(i : ℤ) - 1)
    have e : (-(i : ℤ) - 1 + 1) = -(i : ℤ) := by ring
    rw [e] at h1 h2
    rw [ih] at h1
    linarith
theorem intervalSum_sub (m : ℤ) (F G : ℤ → ℝ) :
    intervalSum m (fun j => F j - G j) = intervalSum m F - intervalSum m G := by
  have h := intervalSum_eq_sub (fun m => intervalSum m F - intervalSum m G) (fun j => F j - G j)
    (fun m => by simp only [intervalSum_succ]; ring) m
  simpa [intervalSum_zero] using h
theorem intervalSum_const_mul (m : ℤ) (r : ℝ) (F : ℤ → ℝ) :
    intervalSum m (fun j => r * F j) = r * intervalSum m F := by
  have h := intervalSum_eq_sub (fun m => r * intervalSum m F) (fun j => r * F j)
    (fun m => by simp only [intervalSum_succ]; ring) m
  simpa [intervalSum_zero] using h
theorem intervalSum_congr (m : ℤ) {F G : ℤ → ℝ} (hFG : ∀ j, F j = G j) :
    intervalSum m F = intervalSum m G := by
  rw [funext hFG]
theorem abs_intervalSum_le (m : ℤ) (F : ℤ → ℝ) (K : ℝ) (hF : ∀ j, |j| ≤ |m| → |F j| ≤ K) :
    |intervalSum m F| ≤ |(m : ℝ)| * K := by
  cases m with
  | ofNat k =>
    simp only [intervalSum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ K fun i hi => hF _ ?_).trans ?_
    · have := Finset.mem_range.1 hi
      simp only [Int.ofNat_eq_natCast, abs_of_nonneg (Int.natCast_nonneg _)]
      omega
    · simp
  | negSucc k =>
    simp only [intervalSum, abs_neg]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ K fun i hi => hF _ ?_).trans ?_
    · have := Finset.mem_range.1 hi
      rw [Int.negSucc_eq, abs_of_nonpos (by omega : (-(i : ℤ) - 1) ≤ 0), abs_of_nonpos (by omega)]
      omega
    · have e : |((Int.negSucc k : ℤ) : ℝ)| = ((k + 1 : ℕ) : ℝ) := by
        rw [Int.negSucc_eq]
        push_cast
        rw [abs_of_nonpos (by positivity |> fun h : (0 : ℝ) ≤ (k : ℝ) => by linarith)]
        ring
      rw [e]
      simp
def truncate (a : Fin 4 → ℤ) (ν : Fin 4) (j : ℤ) : Fin 4 → ℤ :=
  fun i => if i < ν then a i else if i = ν then j else 0
def axialPathSum (B : (Fin 4 → ℤ) → Fin 4 → ℝ) (a : Fin 4 → ℤ) : ℝ :=
  ∑ ν, intervalSum (a ν) fun j => B (truncate a ν j) ν
def latticeCurl (B : (Fin 4 → ℤ) → Fin 4 → ℝ) (a : Fin 4 → ℤ) (μ ν : Fin 4) : ℝ :=
  B a μ + B (a + Pi.single μ 1) ν - B (a + Pi.single ν 1) μ - B a ν
def axialForm (D : (Fin 4 → ℤ) → Fin 4 → Fin 4 → ℝ) (c : (Fin 4 → ℤ) × Fin 4) : ℝ :=
  -∑ ν, if c.2 < ν then intervalSum (c.1 ν) (fun j => D (truncate c.1 ν j) c.2 ν) else 0
private theorem truncate_add_single_of_le {a : Fin 4 → ℤ} {μ ν : Fin 4} (h : ν ≤ μ) (j : ℤ) :
    truncate (a + Pi.single μ 1) ν j = truncate a ν j := by
  funext i
  simp only [truncate]
  by_cases hi : i < ν
  · have : i ≠ μ := by
      rintro rfl
      exact absurd hi (not_lt.2 h)
    simp [hi, this]
  · simp [hi]
abbrev _root_.YangMills.DeltaSharedProofs.p502521 := @truncate_add_single_of_le
private theorem truncate_add_single_of_lt {a : Fin 4 → ℤ} {μ ν : Fin 4} (h : μ < ν) (j : ℤ) :
    truncate (a + Pi.single μ 1) ν j = truncate a ν j + Pi.single μ 1 := by
  funext i
  simp only [truncate, Pi.add_apply]
  by_cases hi : i < ν
  · simp [hi]
  · have h1 : i ≠ μ := by
      rintro rfl
      exact hi h
    simp [hi, h1]
private theorem truncate_add_single_self (a : Fin 4 → ℤ) (ν : Fin 4) (j : ℤ) :
    truncate a ν j + Pi.single ν 1 = truncate a ν (j + 1) := by
  funext i
  simp only [truncate, Pi.add_apply]
  by_cases hi : i < ν
  · have : i ≠ ν := ne_of_lt hi
    simp [hi, this]
  · by_cases h2 : i = ν
    · subst h2
      simp
    · simp [hi, h2]
abbrev _root_.YangMills.DeltaSharedProofs.p501433 := @truncate_add_single_self
private theorem intervalSum_shift_sub (B : (Fin 4 → ℤ) → Fin 4 → ℝ) (a : Fin 4 → ℤ) {μ ν : Fin 4} (h : μ < ν) :
    (intervalSum (a ν) fun j => B (truncate a ν j + Pi.single μ 1) ν) -
        (intervalSum (a ν) fun j => B (truncate a ν j) ν) =
      (intervalSum (a ν) fun j => latticeCurl B (truncate a ν j) μ ν) + B (truncate a ν (a ν)) μ -
        B (truncate a ν 0) μ := by
  rw [← intervalSum_sub]
  have hs := intervalSum_eq_sub
    (fun m => (intervalSum m fun j => latticeCurl B (truncate a ν j) μ ν) + B (truncate a ν m) μ)
    (fun j => B (truncate a ν j + Pi.single μ 1) ν - B (truncate a ν j) ν)
    (fun m => by
      simp only [intervalSum_succ, latticeCurl, truncate_add_single_self]
      ring) (a ν)
  rw [hs]
  simp only [intervalSum_zero]
  ring
theorem eq_pathSum_sub_add_axialForm (B : (Fin 4 → ℤ) → Fin 4 → ℝ) (a : Fin 4 → ℤ) (μ : Fin 4) :
    B a μ = axialPathSum B (a + Pi.single μ 1) - axialPathSum B a + axialForm (latticeCurl B) (a, μ) := by
  have key : ∀ ν : Fin 4,
      ((intervalSum ((a + Pi.single μ 1 : Fin 4 → ℤ) ν) fun j => B (truncate (a + Pi.single μ 1) ν j) ν) -
        intervalSum (a ν) fun j => B (truncate a ν j) ν) -
          (if μ < ν then intervalSum (a ν) (fun j => latticeCurl B (truncate a ν j) μ ν) else 0) =
      if ν < μ then 0 else if ν = μ then B (truncate a μ (a μ)) μ
        else B (truncate a ν (a ν)) μ - B (truncate a ν 0) μ := by
    intro ν
    rcases lt_trichotomy ν μ with h | h | h
    · have h1 : ¬ μ < ν := not_lt.2 h.le
      have h2 : (a + Pi.single μ 1 : Fin 4 → ℤ) ν = a ν := by simp [ne_of_lt h]
      simp only [h1, h, if_true, if_false, h2, truncate_add_single_of_le h.le]
      ring
    · subst h
      have h2 : (a + Pi.single ν 1 : Fin 4 → ℤ) ν = a ν + 1 := by simp
      simp only [lt_irrefl, if_false, if_true, h2, truncate_add_single_of_le le_rfl, intervalSum_succ]
      ring
    · have h1 : ¬ ν < μ := not_lt.2 h.le
      have h3 : ν ≠ μ := ne_of_gt h
      have h2 : (a + Pi.single μ 1 : Fin 4 → ℤ) ν = a ν := by simp [h3]
      simp only [h, h1, h3, if_true, if_false, h2, truncate_add_single_of_lt h]
      rw [intervalSum_shift_sub B a h]
      ring
  have hs : ∑ ν : Fin 4, (if ν < μ then (0 : ℝ) else if ν = μ then B (truncate a μ (a μ)) μ else
      B (truncate a ν (a ν)) μ - B (truncate a ν 0) μ) = B a μ := by
    have t3 : truncate a 3 (a 3) = a := by
      funext i
      fin_cases i <;> simp [truncate]
    have t2 : truncate a 3 0 = truncate a 2 (a 2) := by
      funext i
      fin_cases i <;> simp [truncate]
    have t1 : truncate a 2 0 = truncate a 1 (a 1) := by
      funext i
      fin_cases i <;> simp [truncate]
    have t0 : truncate a 1 0 = truncate a 0 (a 0) := by
      funext i
      fin_cases i <;> simp [truncate]
    rw [Fin.sum_univ_four]
    fin_cases μ <;> simp [t0, t1, t2, t3]
  simp only [axialPathSum, axialForm]
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun ν (_ : ν ∈ Finset.univ) => key ν)
  rw [hs, Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hsum
  linarith
end AxialForms
end YangMills.Construction
end
