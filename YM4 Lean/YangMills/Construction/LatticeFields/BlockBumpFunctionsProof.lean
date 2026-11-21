import YangMills.Construction.LatticeFields.BlockBumpFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFields.BlockBumpFunctions
def quarticBump (t : ℝ) : ℝ := if 0 ≤ t ∧ t ≤ 1 then t ^ 2 * (1 - t) ^ 2 else 0
def quarticBumpDeriv (t : ℝ) : ℝ := if 0 ≤ t ∧ t ≤ 1 then 2 * t * (1 - t) * (1 - 2 * t) else 0
theorem quarticBump_nonneg (t : ℝ) : 0 ≤ quarticBump t := by
  unfold quarticBump
  split_ifs
  · positivity
  · exact le_rfl
theorem quarticBump_le (t : ℝ) : quarticBump t ≤ 1 / 16 := by
  unfold quarticBump
  split_ifs with ht
  · obtain ⟨ht0, ht1⟩ := ht
    have hprod : t * (1 - t) ≤ 1 / 4 := by nlinarith [sq_nonneg (t - 1 / 2)]
    have hprod0 : 0 ≤ t * (1 - t) := mul_nonneg ht0 (by linarith)
    have : (t * (1 - t)) ^ 2 ≤ (1 / 4) ^ 2 := pow_le_pow_left₀ hprod0 hprod 2
    nlinarith
  · norm_num
theorem quarticBump_of_neg {t : ℝ} (ht : t < 0) : quarticBump t = 0 := by
  unfold quarticBump
  rw [if_neg]
  exact fun h => absurd h.1 (not_le.mpr ht)
theorem quarticBump_of_one_lt {t : ℝ} (ht : 1 < t) : quarticBump t = 0 := by
  unfold quarticBump
  rw [if_neg]
  exact fun h => absurd h.2 (not_le.mpr ht)
theorem taylor_remainder_left {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb : b < 0) :
    |-(a ^ 2 * (1 - a) ^ 2) - 2 * a * (1 - a) * (1 - 2 * a) * (b - a)| ≤ (b - a) ^ 2 := by
  obtain ⟨e, he, rfl⟩ : ∃ e, 0 ≤ e ∧ b = -e := ⟨-b, by linarith, by ring⟩
  rw [abs_le]
  constructor
  · have p1 : 0 ≤ 2 - 4 * a + 3 * a ^ 2 := by nlinarith [sq_nonneg (a - 2 / 3)]
    have p2 : 0 ≤ 2 - 3 * a + 2 * a ^ 2 := by nlinarith [sq_nonneg (a - 3 / 4)]
    have q2 : 0 ≤ a ^ 2 * (2 - 4 * a + 3 * a ^ 2) := by positivity
    have q3 : 0 ≤ 2 * a * e * (2 - 3 * a + 2 * a ^ 2) := by positivity
    nlinarith
  · have q2 : 0 ≤ (e + a - a * (1 - a) * (1 - 2 * a)) ^ 2 := sq_nonneg _
    have q3 : 0 ≤ (a * (1 - a)) ^ 2 * (4 * a * (1 - a)) := by positivity
    nlinarith
theorem quarticBump_taylor (a b : ℝ) :
    |quarticBump b - quarticBump a - quarticBumpDeriv a * (b - a)| ≤ (b - a) ^ 2 := by
  by_cases ha : 0 ≤ a ∧ a ≤ 1
  · obtain ⟨ha0, ha1⟩ := ha
    by_cases hb : 0 ≤ b ∧ b ≤ 1
    · obtain ⟨hb0, hb1⟩ := hb
      have hid : quarticBump b - quarticBump a - quarticBumpDeriv a * (b - a) =
          (b - a) ^ 2 * (1 - 4 * a - 2 * b + 3 * a ^ 2 + 2 * a * b + b ^ 2) := by
        simp only [quarticBump, quarticBumpDeriv, if_pos (And.intro ha0 ha1),
          if_pos (And.intro hb0 hb1)]
        ring
      have hbound : |1 - 4 * a - 2 * b + 3 * a ^ 2 + 2 * a * b + b ^ 2| ≤ 1 := by
        rw [abs_le]
        constructor
        · nlinarith [sq_nonneg (a + b - 1), sq_nonneg a, sq_nonneg (1 - a)]
        · nlinarith [mul_nonneg ha0 (sub_nonneg.mpr ha1), mul_nonneg hb0 (sub_nonneg.mpr hb1),
            mul_nonneg ha0 (sub_nonneg.mpr hb1), mul_nonneg hb0 (sub_nonneg.mpr ha1)]
      rw [hid, abs_mul, abs_of_nonneg (sq_nonneg (b - a))]
      nlinarith [sq_nonneg (b - a)]
    · have hda : quarticBumpDeriv a = 2 * a * (1 - a) * (1 - 2 * a) := by
        simp only [quarticBumpDeriv, if_pos (And.intro ha0 ha1)]
      have hva : quarticBump a = a ^ 2 * (1 - a) ^ 2 := by
        simp only [quarticBump, if_pos (And.intro ha0 ha1)]
      have hvb : quarticBump b = 0 := by simp only [quarticBump, if_neg hb]
      rw [hda, hva, hvb]
      by_cases hneg : b < 0
      · have := taylor_remainder_left ha0 ha1 hneg
        convert this using 2
        ring
      · have hgt : 1 < b := by
          by_contra hc
          exact hb ⟨not_lt.mp hneg, not_lt.mp hc⟩
        have := taylor_remainder_left (a := 1 - a) (b := 1 - b) (by linarith) (by linarith)
          (by linarith)
        have hsq : (1 - b - (1 - a)) ^ 2 = (b - a) ^ 2 := by ring
        rw [hsq] at this
        convert this using 2
        ring
  · have hda : quarticBumpDeriv a = 0 := by simp only [quarticBumpDeriv, if_neg ha]
    have hva : quarticBump a = 0 := by simp only [quarticBump, if_neg ha]
    rw [hda, hva]
    by_cases hb : 0 ≤ b ∧ b ≤ 1
    · obtain ⟨hb0, hb1⟩ := hb
      have hvb : quarticBump b = b ^ 2 * (1 - b) ^ 2 := by
        simp only [quarticBump, if_pos (And.intro hb0 hb1)]
      have hle : b ^ 2 * (1 - b) ^ 2 ≤ (b - a) ^ 2 := by
        by_cases hneg : a < 0
        · have c1 : (1 - b) ^ 2 ≤ 1 := by nlinarith
          have c2 : b ^ 2 ≤ (b - a) ^ 2 := by nlinarith
          nlinarith [sq_nonneg b]
        · have hgt : 1 < a := by
            by_contra hc
            exact ha ⟨not_lt.mp hneg, not_lt.mp hc⟩
          have c1 : b ^ 2 ≤ 1 := by nlinarith
          have c2 : (1 - b) ^ 2 ≤ (b - a) ^ 2 := by nlinarith
          nlinarith [sq_nonneg (1 - b)]
      rw [hvb]
      have : 0 ≤ b ^ 2 * (1 - b) ^ 2 := by positivity
      simpa [abs_of_nonneg this] using hle
    · have hvb : quarticBump b = 0 := by simp only [quarticBump, if_neg hb]
      rw [hvb]
      simpa using sq_nonneg (b - a)
theorem quarticBump_secondDiff (u e : ℝ) :
    |quarticBump (u + e) + quarticBump (u - e) - 2 * quarticBump u| ≤ 2 * e ^ 2 := by
  have hp := quarticBump_taylor u (u + e)
  have hm := quarticBump_taylor u (u - e)
  have c1 : u + e - u = e := by ring
  have c2 : u - e - u = -e := by ring
  rw [c1] at hp
  rw [c2] at hm
  rw [abs_le] at hp hm ⊢
  constructor <;> nlinarith [hp.1, hp.2, hm.1, hm.2]
theorem sum_range_odd_sq (n : ℕ) :
    ∑ j ∈ Finset.range n, (2 * (j : ℝ) + 1) ^ 2 = (n : ℝ) * (4 * (n : ℝ) ^ 2 - 1) / 3 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring
theorem sum_range_odd_cube (n : ℕ) :
    ∑ j ∈ Finset.range n, (2 * (j : ℝ) + 1) ^ 3 = (n : ℝ) ^ 2 * (2 * (n : ℝ) ^ 2 - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring
theorem sum_range_odd_pow_four (n : ℕ) :
    ∑ j ∈ Finset.range n, (2 * (j : ℝ) + 1) ^ 4 =
      (n : ℝ) * (48 * (n : ℝ) ^ 4 - 40 * (n : ℝ) ^ 2 + 7) / 15 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring
def midpointBump (N : ℕ) (i : ℤ) : ℝ := quarticBump (((i : ℝ) + 1 / 2) / N)
theorem midpointBump_of_lt {N : ℕ} (hN : 0 < N) {j : ℕ} (hj : j < N) :
    midpointBump N j = (2 * (j : ℝ) + 1) ^ 2 / (4 * (N : ℝ) ^ 2) -
      (2 * (j : ℝ) + 1) ^ 3 / (4 * (N : ℝ) ^ 3) + (2 * (j : ℝ) + 1) ^ 4 / (16 * (N : ℝ) ^ 4) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hjr : (j : ℝ) + 1 ≤ N := by exact_mod_cast hj
  have h0 : 0 ≤ (((j : ℤ) : ℝ) + 1 / 2) / N := by
    simp only [Int.cast_natCast]
    positivity
  have h1 : (((j : ℤ) : ℝ) + 1 / 2) / N ≤ 1 := by
    simp only [Int.cast_natCast]
    rw [div_le_one hNr]
    linarith
  unfold midpointBump quarticBump
  rw [if_pos (And.intro h0 h1)]
  simp only [Int.cast_natCast]
  field_simp
  ring
theorem sum_midpointBump {N : ℕ} (hN : 0 < N) :
    ∑ j ∈ Finset.range N, midpointBump N j = (N : ℝ) / 30 + 7 / (240 * (N : ℝ) ^ 3) := by
  have hNr : (N : ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
  rw [Finset.sum_congr rfl fun j hj => midpointBump_of_lt hN (Finset.mem_range.mp hj)]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div,
    ← Finset.sum_div, sum_range_odd_sq, sum_range_odd_cube, sum_range_odd_pow_four]
  field_simp
  ring
def midpointMean (N : ℕ) : ℝ := (∑ j ∈ Finset.range N, midpointBump N j) / N
theorem midpointMean_ge {N : ℕ} (hN : 0 < N) : 1 / 30 ≤ midpointMean N := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  unfold midpointMean
  rw [sum_midpointBump hN, le_div_iff₀ hNr]
  have : 0 ≤ 7 / (240 * (N : ℝ) ^ 3) := by positivity
  linarith
section Line
variable {N : ℕ}
theorem midpointBump_nonneg (N : ℕ) (i : ℤ) : 0 ≤ midpointBump N i := quarticBump_nonneg _
theorem midpointBump_le (N : ℕ) (i : ℤ) : midpointBump N i ≤ 1 / 16 := quarticBump_le _
theorem midpointBump_of_neg (hN : 0 < N) {i : ℤ} (hi : i < 0) : midpointBump N i = 0 := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hir : (i : ℝ) + 1 ≤ 0 := by exact_mod_cast hi
  apply quarticBump_of_neg
  apply div_neg_of_neg_of_pos _ hNr
  linarith
theorem midpointBump_of_ge (hN : 0 < N) {i : ℤ} (hi : (N : ℤ) ≤ i) : midpointBump N i = 0 := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hir : (N : ℝ) ≤ i := by exact_mod_cast hi
  apply quarticBump_of_one_lt
  rw [one_lt_div hNr]
  linarith
theorem midpointBump_secondDiff (hN : 0 < N) (i : ℤ) :
    |midpointBump N (i + 1) + midpointBump N (i - 1) - 2 * midpointBump N i| ≤
      2 * ((N : ℝ)⁻¹) ^ 2 := by
  have hNr : (N : ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
  have := quarticBump_secondDiff (((i : ℝ) + 1 / 2) / N) ((N : ℝ)⁻¹)
  have c1 : (((i + 1 : ℤ) : ℝ) + 1 / 2) / N = ((i : ℝ) + 1 / 2) / N + (N : ℝ)⁻¹ := by
    push_cast
    field_simp
    ring
  have c2 : (((i - 1 : ℤ) : ℝ) + 1 / 2) / N = ((i : ℝ) + 1 / 2) / N - (N : ℝ)⁻¹ := by
    push_cast
    field_simp
    ring
  unfold midpointBump
  rw [c1, c2]
  exact this
def lineProfile (N : ℕ) (W : ℤ → ℝ) (s : ℤ) : ℝ := W (s / N) * midpointBump N (s % N)
theorem lineProfile_of_cell (hN : 0 < N) (W : ℤ → ℝ) (q r : ℤ) (hr0 : 0 ≤ r) (hr1 : r < N) :
    lineProfile N W (q * N + r) = W q * midpointBump N r := by
  have hNz : (0 : ℤ) < N := by exact_mod_cast hN
  have hdiv : (q * N + r) / N = q := by
    rw [add_comm, Int.add_mul_ediv_right _ _ hNz.ne', Int.ediv_eq_zero_of_lt hr0 hr1, zero_add]
  have hmod : (q * N + r) % N = r := by
    rw [add_comm, Int.add_mul_emod_self_right, Int.emod_eq_of_lt hr0 hr1]
  unfold lineProfile
  rw [hdiv, hmod]
theorem lineProfile_near (hN : 0 < N) (W : ℤ → ℝ) (q i : ℤ) (hi0 : -1 ≤ i) (hi1 : i ≤ N) :
    lineProfile N W (q * N + i) = W q * midpointBump N i + W (q + 1) * midpointBump N (i - N) +
      W (q - 1) * midpointBump N (i + N) := by
  have hNz : (0 : ℤ) < N := by exact_mod_cast hN
  rcases eq_or_lt_of_le hi0 with rfl | hi0'
  · have c : q * N + -1 = (q - 1) * N + (N - 1) := by ring
    rw [c, lineProfile_of_cell hN W (q - 1) (N - 1) (by omega) (by omega),
      midpointBump_of_neg hN (i := -1) (by omega), midpointBump_of_neg hN (i := -1 - N) (by omega)]
    have c2 : (-1 + (N : ℤ)) = N - 1 := by ring
    rw [c2]
    ring
  rcases eq_or_lt_of_le hi1 with rfl | hi1'
  · have c : q * N + N = (q + 1) * N + 0 := by ring
    rw [c, lineProfile_of_cell hN W (q + 1) 0 le_rfl hNz, midpointBump_of_ge hN (i := N) le_rfl,
      midpointBump_of_ge hN (i := N + N) (by omega)]
    have c2 : ((N : ℤ) - N) = 0 := by ring
    rw [c2]
    ring
  · rw [lineProfile_of_cell hN W q i (by omega) hi1', midpointBump_of_neg hN (i := i - N) (by omega),
      midpointBump_of_ge hN (i := i + N) (by omega)]
    ring
theorem lineProfile_secondDiff (hN : 0 < N) (W : ℤ → ℝ) (s : ℤ) :
    |lineProfile N W (s + 1) + lineProfile N W (s - 1) - 2 * lineProfile N W s| ≤
      2 * ((N : ℝ)⁻¹) ^ 2 * (|W (s / N)| + |W (s / N + 1)| + |W (s / N - 1)|) := by
  have hNz : (0 : ℤ) < N := by exact_mod_cast hN
  set q := s / N with hq
  set r := s % N with hr
  have hs : s = q * N + r := by
    rw [hq, hr, mul_comm]
    exact (Int.mul_ediv_add_emod s N).symm
  have hr0 : 0 ≤ r := Int.emod_nonneg _ hNz.ne'
  have hr1 : r < N := Int.emod_lt_of_pos _ hNz
  have hs1 : s + 1 = q * N + (r + 1) := by omega
  have hs2 : s - 1 = q * N + (r - 1) := by omega
  have p1 := lineProfile_near hN W q (r + 1) (by omega) (by omega)
  have p2 := lineProfile_near hN W q (r - 1) (by omega) (by omega)
  have p3 := lineProfile_near hN W q r (by omega) (by omega)
  rw [← hs1] at p1
  rw [← hs2] at p2
  rw [← hs] at p3
  set D : ℤ → ℝ := fun i => midpointBump N (i + 1) + midpointBump N (i - 1) -
    2 * midpointBump N i with hD
  have hDb : ∀ i, |D i| ≤ 2 * ((N : ℝ)⁻¹) ^ 2 := fun i => midpointBump_secondDiff hN i
  have key : lineProfile N W (s + 1) + lineProfile N W (s - 1) - 2 * lineProfile N W s =
      W q * D r + W (q + 1) * D (r - N) + W (q - 1) * D (r + N) := by
    rw [p1, p2, p3]
    simp only [hD]
    have c1 : r + 1 - (N : ℤ) = r - N + 1 := by ring
    have c2 : r - 1 - (N : ℤ) = r - N - 1 := by ring
    have c3 : r + 1 + (N : ℤ) = r + N + 1 := by ring
    have c4 : r - 1 + (N : ℤ) = r + N - 1 := by ring
    rw [c1, c2, c3, c4]
    ring
  rw [key]
  have t1 : |W q * D r| ≤ |W q| * (2 * ((N : ℝ)⁻¹) ^ 2) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hDb _) (abs_nonneg _)
  have t2 : |W (q + 1) * D (r - N)| ≤ |W (q + 1)| * (2 * ((N : ℝ)⁻¹) ^ 2) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hDb _) (abs_nonneg _)
  have t3 : |W (q - 1) * D (r + N)| ≤ |W (q - 1)| * (2 * ((N : ℝ)⁻¹) ^ 2) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hDb _) (abs_nonneg _)
  calc _ ≤ |W q * D r| + |W (q + 1) * D (r - N)| + |W (q - 1) * D (r + N)| :=
        abs_add_three _ _ _
    _ ≤ _ := by linarith
end Line
section Coordinates
variable {d : ℕ}
def latticePoint (N : ℕ) (n : Fin d → ℤ) : scaledIntLattice d N :=
  ⟨fun μ => latticeSpacing N * n μ, fun μ => ⟨n μ, rfl⟩⟩
def torusSite (N : ℕ) (ℓ : Fin d → ℕ) (hℓ : ∀ μ, 1 ≤ ℓ μ) (n : Fin d → ℤ) :
    LatticeSite N (LatticeShape.torus ℓ hℓ) :=
  toSite N _ (latticePoint N n)
variable {ℓ : Fin d → ℕ} {hℓ : ∀ μ, 1 ≤ ℓ μ}
theorem exists_latticePoint {N : ℕ} (v : scaledIntLattice d N) :
    ∃ n : Fin d → ℤ, v = latticePoint N n := by
  choose a ha using v.2
  exact ⟨a, Subtype.ext (funext ha)⟩
theorem torusSite_surjective (N : ℕ) : Function.Surjective (torusSite N ℓ hℓ) := by
  intro x
  obtain ⟨v, rfl⟩ := toSite_surjective N _ x
  obtain ⟨n, rfl⟩ := exists_latticePoint v
  exact ⟨n, rfl⟩
theorem torusSite_eq_iff {N : ℕ} [NeZero N] {n n' : Fin d → ℤ} :
    torusSite N ℓ hℓ n = torusSite N ℓ hℓ n' ↔ ∀ μ, ∃ k : ℤ, n μ - n' μ = N * ℓ μ * k := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  unfold torusSite
  rw [← sub_eq_zero, ← map_sub, toSite_eq_zero_iff]
  show (∀ μ, ∃ k : ℤ, latticeSpacing N * (n μ : ℝ) - latticeSpacing N * (n' μ : ℝ) =
    (ℓ μ : ℝ) * k) ↔ _
  constructor
  · intro h μ
    obtain ⟨k, hk⟩ := h μ
    refine ⟨k, ?_⟩
    have : (n μ : ℝ) - n' μ = N * ℓ μ * k := by
      calc (n μ : ℝ) - n' μ =
            N * (latticeSpacing N * (n μ : ℝ) - latticeSpacing N * (n' μ : ℝ)) := by
            rw [latticeSpacing]
            field_simp
        _ = N * ℓ μ * k := by
            rw [hk]
            ring
    exact_mod_cast this
  · intro h μ
    obtain ⟨k, hk⟩ := h μ
    refine ⟨k, ?_⟩
    have : (n μ : ℝ) - n' μ = N * ℓ μ * k := by exact_mod_cast hk
    calc latticeSpacing N * (n μ : ℝ) - latticeSpacing N * (n' μ : ℝ) =
          latticeSpacing N * ((n μ : ℝ) - n' μ) := by
          ring
      _ = (ℓ μ : ℝ) * k := by
          rw [this, latticeSpacing]
          field_simp
theorem torusSite_add_unitStep (N : ℕ) (n : Fin d → ℤ) (μ : Fin d) :
    torusSite N ℓ hℓ n + unitStep N (LatticeShape.torus ℓ hℓ) μ =
      torusSite N ℓ hℓ (Function.update n μ (n μ + 1)) := by
  unfold torusSite unitStep
  rw [← map_add]
  congr 1
  apply Subtype.ext
  funext ν
  show latticeSpacing N * (n ν : ℝ) + (Pi.single μ (latticeSpacing N) : Fin d → ℝ) ν =
    latticeSpacing N * ((Function.update n μ (n μ + 1) ν : ℤ) : ℝ)
  by_cases h : ν = μ
  · subst h
    simp only [Pi.single_eq_same, Function.update_self]
    push_cast
    ring
  · simp [Pi.single_eq_of_ne h, Function.update_of_ne h]
theorem torusSite_sub_unitStep (N : ℕ) (n : Fin d → ℤ) (μ : Fin d) :
    torusSite N ℓ hℓ n - unitStep N (LatticeShape.torus ℓ hℓ) μ =
      torusSite N ℓ hℓ (Function.update n μ (n μ - 1)) := by
  apply sub_eq_of_eq_add
  rw [torusSite_add_unitStep]
  simp
theorem finite_torusSites (N : ℕ) [NeZero N] : Finite (LatticeSite N (LatticeShape.torus ℓ hℓ)) := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hpos : ∀ μ, (0 : ℤ) < (N : ℤ) * ℓ μ := fun μ => by
    have := hℓ μ
    positivity
  refine Finite.of_surjective
    (fun m : (μ : Fin d) → Fin (N * ℓ μ) => torusSite N ℓ hℓ fun μ => ((m μ : ℕ) : ℤ)) ?_
  intro x
  obtain ⟨n, rfl⟩ := torusSite_surjective N x
  have hb : ∀ μ, (n μ % ((N : ℤ) * ℓ μ)).toNat < N * ℓ μ := fun μ => by
    have h1 := Int.emod_nonneg (n μ) (hpos μ).ne'
    have h2 := Int.emod_lt_of_pos (n μ) (hpos μ)
    zify
    rw [Int.toNat_of_nonneg h1]
    exact h2
  refine ⟨fun μ => ⟨_, hb μ⟩, ?_⟩
  rw [torusSite_eq_iff]
  intro μ
  refine ⟨-(n μ / ((N : ℤ) * ℓ μ)), ?_⟩
  have h1 := Int.emod_nonneg (n μ) (hpos μ).ne'
  show (((n μ % ((N : ℤ) * ℓ μ)).toNat : ℕ) : ℤ) - n μ = _
  rw [Int.toNat_of_nonneg h1, Int.emod_def]
  ring
end Coordinates
section Bump
variable {d N : ℕ} {ℓ : Fin d → ℕ} {hℓ : ∀ μ, 1 ≤ ℓ μ}
def bumpCoeff (N : ℕ) (ω : ScalarField 1 (LatticeShape.torus ℓ hℓ)) (n : Fin d → ℤ) : ℝ :=
  ScalarField.eval ω (torusSite 1 ℓ hℓ fun ν => n ν / N) *
    ((midpointMean N)⁻¹ ^ d * ∏ ν, midpointBump N (n ν % N))
theorem bumpCoeff_periodic [NeZero N] (ω : ScalarField 1 (LatticeShape.torus ℓ hℓ))
    {n n' : Fin d → ℤ} (h : torusSite N ℓ hℓ n = torusSite N ℓ hℓ n') :
    bumpCoeff N ω n = bumpCoeff N ω n' := by
  have hNz : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  rw [torusSite_eq_iff] at h
  choose k hk using h
  have hn : ∀ ν, n ν = n' ν + N * (ℓ ν * k ν) := fun ν => by linarith [hk ν]
  have hdiv : ∀ ν, n ν / N = n' ν / N + ℓ ν * k ν := fun ν => by
    rw [hn ν, Int.add_mul_ediv_left _ _ hNz]
  have hmod : ∀ ν, n ν % N = n' ν % N := fun ν => by
    rw [hn ν, Int.add_mul_emod_self_left]
  have hsite : torusSite 1 ℓ hℓ (fun ν => n ν / N) = torusSite 1 ℓ hℓ (fun ν => n' ν / N) := by
    rw [torusSite_eq_iff]
    intro ν
    refine ⟨k ν, ?_⟩
    rw [hdiv ν]
    push_cast
    ring
  unfold bumpCoeff
  rw [hsite]
  simp only [hmod]
def bumpField (N : ℕ) (ω : ScalarField 1 (LatticeShape.torus ℓ hℓ)) :
    ScalarField N (LatticeShape.torus ℓ hℓ) :=
  fun x _ => bumpCoeff N ω (Function.surjInv (torusSite_surjective N) x)
theorem bumpField_apply [NeZero N] (ω : ScalarField 1 (LatticeShape.torus ℓ hℓ))
    (n : Fin d → ℤ) (i : Fin 0 → Fin d) :
    bumpField N ω (torusSite N ℓ hℓ n) i = bumpCoeff N ω n :=
  bumpCoeff_periodic ω (Function.surjInv_eq (torusSite_surjective N) _)
def coarseCoords (y : LatticeSite 1 (LatticeShape.torus ℓ hℓ)) : Fin d → ℤ :=
  Function.surjInv (torusSite_surjective 1) y
theorem torusSite_coarseCoords (y : LatticeSite 1 (LatticeShape.torus ℓ hℓ)) :
    torusSite 1 ℓ hℓ (coarseCoords y) = y :=
  Function.surjInv_eq (torusSite_surjective 1) y
def cellCoords (N : ℕ) (y : LatticeSite 1 (LatticeShape.torus ℓ hℓ)) (r : Fin d → Fin N) :
    Fin d → ℤ :=
  fun μ => N * coarseCoords y μ + ((r μ : ℕ) : ℤ)
def cellSite (N : ℕ) (p : LatticeSite 1 (LatticeShape.torus ℓ hℓ) × (Fin d → Fin N)) :
    LatticeSite N (LatticeShape.torus ℓ hℓ) :=
  torusSite N ℓ hℓ (cellCoords N p.1 p.2)
theorem natMul_add_fin_ediv [NeZero N] (q : ℤ) (r : Fin N) :
    ((N : ℤ) * q + ((r : ℕ) : ℤ)) / N = q := by
  have hNz : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have h0 : (0 : ℤ) ≤ ((r : ℕ) : ℤ) := by positivity
  have h1 : ((r : ℕ) : ℤ) < N := by exact_mod_cast r.2
  rw [add_comm, Int.add_mul_ediv_left _ _ hNz, Int.ediv_eq_zero_of_lt h0 h1, zero_add]
theorem natMul_add_fin_emod [NeZero N] (q : ℤ) (r : Fin N) :
    ((N : ℤ) * q + ((r : ℕ) : ℤ)) % N = ((r : ℕ) : ℤ) := by
  have h0 : (0 : ℤ) ≤ ((r : ℕ) : ℤ) := by positivity
  have h1 : ((r : ℕ) : ℤ) < N := by exact_mod_cast r.2
  rw [add_comm, Int.add_mul_emod_self_left, Int.emod_eq_of_lt h0 h1]
theorem cellSite_injective [NeZero N] :
    Function.Injective (cellSite (ℓ := ℓ) (hℓ := hℓ) N) := by
  have hNz : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  rintro ⟨y, r⟩ ⟨y', r'⟩ h
  have h' := torusSite_eq_iff.mp h
  choose k hk using h'
  simp only [cellCoords] at hk
  have hn : ∀ μ, (N : ℤ) * coarseCoords y μ + ((r μ : ℕ) : ℤ) =
      (N : ℤ) * coarseCoords y' μ + ((r' μ : ℕ) : ℤ) + N * (ℓ μ * k μ) := fun μ => by
    linarith [hk μ]
  have hr : ∀ μ, ((r μ : ℕ) : ℤ) = ((r' μ : ℕ) : ℤ) := fun μ => by
    have := congrArg (· % (N : ℤ)) (hn μ)
    simp only [Int.add_mul_emod_self_left, natMul_add_fin_emod] at this
    exact this
  have hq : ∀ μ, coarseCoords y μ = coarseCoords y' μ + ℓ μ * k μ := fun μ => by
    have := congrArg (· / (N : ℤ)) (hn μ)
    simp only [Int.add_mul_ediv_left _ _ hNz, natMul_add_fin_ediv] at this
    exact this
  have hy : y = y' := by
    rw [← torusSite_coarseCoords y, ← torusSite_coarseCoords y', torusSite_eq_iff]
    intro μ
    refine ⟨k μ, ?_⟩
    rw [hq μ]
    push_cast
    ring
  have hrr : r = r' := by
    funext μ
    apply Fin.ext
    exact_mod_cast hr μ
  rw [hy, hrr]
theorem cellSite_surjective [NeZero N] :
    Function.Surjective (cellSite (ℓ := ℓ) (hℓ := hℓ) N) := by
  have hN0 : (0 : ℤ) < N := by
    have := Nat.pos_of_ne_zero (NeZero.ne N)
    exact_mod_cast this
  intro x
  obtain ⟨n, rfl⟩ := torusSite_surjective N x
  have hb : ∀ μ, (n μ % (N : ℤ)).toNat < N := fun μ => by
    have h1 := Int.emod_nonneg (n μ) hN0.ne'
    have h2 := Int.emod_lt_of_pos (n μ) hN0
    zify
    rw [Int.toNat_of_nonneg h1]
    exact h2
  refine ⟨(torusSite 1 ℓ hℓ fun μ => n μ / N, fun μ => ⟨_, hb μ⟩), ?_⟩
  have hy := torusSite_eq_iff.mp (torusSite_coarseCoords (torusSite 1 ℓ hℓ fun μ => n μ / N))
  choose k hk using hy
  apply torusSite_eq_iff.mpr
  intro μ
  refine ⟨k μ, ?_⟩
  simp only [cellCoords]
  have h1 := Int.emod_nonneg (n μ) hN0.ne'
  rw [Int.toNat_of_nonneg h1, Int.emod_def]
  have := hk μ
  push_cast at this
  have e : coarseCoords (torusSite 1 ℓ hℓ fun μ => n μ / N) μ = n μ / N + ℓ μ * k μ := by
    linarith
  rw [e]
  ring
def cellSiteEquiv (N : ℕ) [NeZero N] :
    LatticeSite 1 (LatticeShape.torus ℓ hℓ) × (Fin d → Fin N) ≃
      LatticeSite N (LatticeShape.torus ℓ hℓ) :=
  Equiv.ofBijective (cellSite N) ⟨cellSite_injective, cellSite_surjective⟩
theorem coarseBlock_eq_range [NeZero N] (y : LatticeSite 1 (LatticeShape.torus ℓ hℓ)) :
    coarseBlock N y = Set.range fun r : Fin d → Fin N => cellSite N (y, r) := by
  have hN : (0 : ℝ) < N := by
    have := Nat.pos_of_ne_zero (NeZero.ne N)
    exact_mod_cast this
  ext x
  constructor
  · rintro ⟨w, v, hw, hv, hin⟩
    obtain ⟨a, rfl⟩ := exists_latticePoint w
    obtain ⟨n, rfl⟩ := exists_latticePoint v
    have hlo : ∀ μ, (N : ℤ) * a μ ≤ n μ := fun μ => by
      have h := (hin μ).1
      have h' : (a μ : ℝ) ≤ (N : ℝ)⁻¹ * n μ := by simpa [latticePoint, latticeSpacing] using h
      have h2 : (N : ℝ) * a μ ≤ n μ := by
        have := mul_le_mul_of_nonneg_left h' hN.le
        rwa [← mul_assoc, mul_inv_cancel₀ hN.ne', one_mul] at this
      exact_mod_cast h2
    have hhi : ∀ μ, n μ < (N : ℤ) * a μ + N := fun μ => by
      have h := (hin μ).2
      have h' : (N : ℝ)⁻¹ * n μ < a μ + 1 := by simpa [latticePoint, latticeSpacing] using h
      have h2 : (n μ : ℝ) < (N : ℝ) * a μ + N := by
        have := mul_lt_mul_of_pos_left h' hN
        rw [← mul_assoc, mul_inv_cancel₀ hN.ne', one_mul] at this
        linarith
      exact_mod_cast h2
    have hb : ∀ μ, (n μ - (N : ℤ) * a μ).toNat < N := fun μ => by
      have h1 : 0 ≤ n μ - (N : ℤ) * a μ := by linarith [hlo μ]
      zify
      rw [Int.toNat_of_nonneg h1]
      linarith [hhi μ]
    refine ⟨fun μ => ⟨_, hb μ⟩, ?_⟩
    rw [← hv]
    have hy : torusSite 1 ℓ hℓ (coarseCoords y) = torusSite 1 ℓ hℓ a := by
      rw [torusSite_coarseCoords]
      exact hw.symm
    have hy' := torusSite_eq_iff.mp hy
    choose k hk using hy'
    apply torusSite_eq_iff.mpr
    intro μ
    refine ⟨k μ, ?_⟩
    simp only [cellCoords]
    have h1 : 0 ≤ n μ - (N : ℤ) * a μ := by linarith [hlo μ]
    rw [Int.toNat_of_nonneg h1]
    have := hk μ
    push_cast at this
    have e : coarseCoords y μ = a μ + ℓ μ * k μ := by linarith
    rw [e]
    ring
  · rintro ⟨r, rfl⟩
    refine ⟨latticePoint 1 (coarseCoords y), latticePoint N (cellCoords N y r),
      torusSite_coarseCoords y, rfl, ?_⟩
    intro μ
    have hr : ((r μ : ℕ) : ℝ) < N := by exact_mod_cast (r μ).2
    have hr0 : (0 : ℝ) ≤ ((r μ : ℕ) : ℝ) := by positivity
    have e : (latticePoint N (cellCoords N y r) : Fin d → ℝ) μ =
        (coarseCoords y μ : ℝ) + (N : ℝ)⁻¹ * ((r μ : ℕ) : ℝ) := by
      show latticeSpacing N * ((cellCoords N y r μ : ℤ) : ℝ) = _
      simp only [cellCoords, latticeSpacing]
      push_cast
      field_simp
    have e' : (latticePoint 1 (coarseCoords y) : Fin d → ℝ) μ = (coarseCoords y μ : ℝ) := by
      show latticeSpacing 1 * ((coarseCoords y μ : ℤ) : ℝ) = _
      simp [latticeSpacing]
    rw [e, e']
    constructor
    · have : 0 ≤ (N : ℝ)⁻¹ * ((r μ : ℕ) : ℝ) := by positivity
      linarith
    · have : (N : ℝ)⁻¹ * ((r μ : ℕ) : ℝ) < 1 := by
        rw [inv_mul_lt_iff₀ hN]
        linarith
      linarith
theorem bumpCoeff_cellCoords [NeZero N] (ω : ScalarField 1 (LatticeShape.torus ℓ hℓ))
    (y : LatticeSite 1 (LatticeShape.torus ℓ hℓ)) (r : Fin d → Fin N) :
    bumpCoeff N ω (cellCoords N y r) =
      ScalarField.eval ω y * ((midpointMean N)⁻¹ ^ d * ∏ ν, midpointBump N ((r ν : ℕ) : ℤ)) := by
  unfold bumpCoeff
  simp only [cellCoords, natMul_add_fin_ediv, natMul_add_fin_emod]
  have : (torusSite 1 ℓ hℓ fun ν => coarseCoords y ν) = y := torusSite_coarseCoords y
  rw [this]
theorem siteBlockAvg_bumpField [NeZero N] (ω : ScalarField 1 (LatticeShape.torus ℓ hℓ)) :
    siteBlockAvg (bumpField N ω) = ω := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hN : (N : ℝ) ≠ 0 := (Nat.cast_pos.mpr hN0).ne'
  have hm : midpointMean N ≠ 0 := by
    have := midpointMean_ge hN0
    intro h
    rw [h] at this
    norm_num at this
  funext y i
  have hi : i = scalarIndex := Subsingleton.elim _ _
  subst hi
  show ∑ᶠ x ∈ coarseBlock N y, latticeSpacing N ^ d * ScalarField.eval (bumpField N ω) x =
    ScalarField.eval ω y
  have hinj : Function.Injective fun r : Fin d → Fin N =>
      cellSite (ℓ := ℓ) (hℓ := hℓ) N (y, r) :=
    fun r r' h => (Prod.ext_iff.mp (cellSite_injective h)).2
  rw [coarseBlock_eq_range, finsum_mem_range hinj, finsum_eq_sum_of_fintype]
  have hval : ∀ r : Fin d → Fin N, latticeSpacing N ^ d *
      ScalarField.eval (bumpField N ω) (cellSite (ℓ := ℓ) (hℓ := hℓ) N (y, r)) =
      latticeSpacing N ^ d * (ScalarField.eval ω y * (midpointMean N)⁻¹ ^ d) *
        ∏ ν, midpointBump N ((r ν : ℕ) : ℤ) := fun r => by
    show latticeSpacing N ^ d * bumpField N ω (torusSite N ℓ hℓ (cellCoords N y r)) scalarIndex = _
    rw [bumpField_apply, bumpCoeff_cellCoords]
    ring
  rw [Finset.sum_congr rfl fun r _ => hval r, ← Finset.mul_sum]
  have hprod : ∑ r : Fin d → Fin N, ∏ ν, midpointBump N ((r ν : ℕ) : ℤ) =
      ((N : ℝ) * midpointMean N) ^ d := by
    have h1 := Finset.prod_univ_sum (fun _ : Fin d => (Finset.univ : Finset (Fin N)))
      (fun _ j => midpointBump N ((j : ℕ) : ℤ))
    rw [Fintype.piFinset_univ] at h1
    rw [← h1, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Fin.sum_univ_eq_sum_range (fun j : ℕ => midpointBump N (j : ℤ)) N]
    unfold midpointMean
    congr 1
    field_simp
  rw [hprod]
  have : latticeSpacing N ^ d * (midpointMean N)⁻¹ ^ d * ((N : ℝ) * midpointMean N) ^ d = 1 := by
    rw [← mul_pow, ← mul_pow, latticeSpacing]
    have : (N : ℝ)⁻¹ * (midpointMean N)⁻¹ * ((N : ℝ) * midpointMean N) = 1 := by
      field_simp
    rw [this, one_pow]
  calc _ = ScalarField.eval ω y * (latticeSpacing N ^ d * (midpointMean N)⁻¹ ^ d *
        ((N : ℝ) * midpointMean N) ^ d) := by
        ring
    _ = _ := by rw [this, mul_one]
theorem bumpField_eq_zero_of_coarse [NeZero N] (ω : ScalarField 1 (LatticeShape.torus ℓ hℓ))
    (y : LatticeSite 1 (LatticeShape.torus ℓ hℓ)) (hy : ScalarField.eval ω y = 0)
    (x : LatticeSite N (LatticeShape.torus ℓ hℓ)) (hx : x ∈ coarseBlock N y) :
    ScalarField.eval (bumpField N ω) x = 0 := by
  rw [coarseBlock_eq_range] at hx
  obtain ⟨r, rfl⟩ := hx
  show bumpField N ω (torusSite N ℓ hℓ (cellCoords N y r)) scalarIndex = 0
  rw [bumpField_apply, bumpCoeff_cellCoords, hy, zero_mul]
end Bump
section Laplacian
variable {d N : ℕ}
theorem tensorLaplacian_scalar {κ : LatticeShape d} (F : ScalarField N κ) (x : LatticeSite N κ)
    (i : Fin 0 → Fin d) :
    tensorLaplacian F x i = ∑ μ, backwardDiff μ (forwardDiff μ F) x i := by
  unfold tensorLaplacian tensorGradAdjoint
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [backwardDiff, shiftBackward, tensorGrad, Pi.smul_apply, Pi.sub_apply, Fin.cons_zero,
    Fin.tail_cons]
theorem backwardDiff_forwardDiff_scalar {κ : LatticeShape d} (F : ScalarField N κ) (μ : Fin d)
    (x : LatticeSite N κ) (i : Fin 0 → Fin d) :
    backwardDiff μ (forwardDiff μ F) x i =
      -((N : ℝ) ^ 2 * (F (x + unitStep N κ μ) i + F (x - unitStep N κ μ) i - 2 * F x i)) := by
  simp only [backwardDiff, forwardDiff, shiftForward, shiftBackward, Pi.smul_apply, Pi.sub_apply,
    smul_eq_mul, latticeSpacing, inv_inv, sub_add_cancel]
  ring
theorem one_div_sixteen_pow {d : ℕ} (hd : 1 ≤ d) :
    (1 / 16 : ℝ) ^ (d - 1) = 16 ^ (1 - (d : ℤ)) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  have h : (1 - ((e + 1 : ℕ) : ℤ)) = -(e : ℤ) := by
    push_cast
    ring
  rw [h, zpow_neg, zpow_natCast, Nat.add_sub_cancel, one_div, inv_pow]
def transverseFactor (N : ℕ) (n : Fin d → ℤ) (μ : Fin d) : ℝ :=
  (midpointMean N)⁻¹ ^ d * ∏ ν ∈ Finset.univ.erase μ, midpointBump N (n ν % N)
theorem transverseFactor_nonneg [NeZero N] (n : Fin d → ℤ) (μ : Fin d) :
    0 ≤ transverseFactor N n μ := by
  have hm : 0 < midpointMean N :=
    lt_of_lt_of_le (by norm_num) (midpointMean_ge (Nat.pos_of_ne_zero (NeZero.ne N)))
  exact mul_nonneg (pow_nonneg (inv_nonneg.mpr hm.le) d)
    (Finset.prod_nonneg fun _ _ => midpointBump_nonneg _ _)
theorem transverseFactor_le [NeZero N] (n : Fin d → ℤ) (μ : Fin d) :
    transverseFactor N n μ ≤ 30 ^ d * 16 ^ (1 - (d : ℤ)) := by
  have hge := midpointMean_ge (Nat.pos_of_ne_zero (NeZero.ne N))
  have hm : 0 < midpointMean N := lt_of_lt_of_le (by norm_num) hge
  have h1 : (midpointMean N)⁻¹ ≤ 30 := by
    have := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 30) hge
    norm_num at this
    exact this
  have h2 : (midpointMean N)⁻¹ ^ d ≤ 30 ^ d := pow_le_pow_left₀ (inv_nonneg.mpr hm.le) h1 d
  have h3 : ∏ ν ∈ Finset.univ.erase μ, midpointBump N (n ν % N) ≤ 16 ^ (1 - (d : ℤ)) := by
    rw [← one_div_sixteen_pow (Nat.succ_le_of_lt μ.pos)]
    calc ∏ ν ∈ Finset.univ.erase μ, midpointBump N (n ν % N)
        ≤ ∏ _ν ∈ Finset.univ.erase μ, (1 / 16 : ℝ) :=
          Finset.prod_le_prod (fun _ _ => midpointBump_nonneg _ _) (fun _ _ => midpointBump_le _ _)
      _ = (1 / 16 : ℝ) ^ (d - 1) := by
          rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
            Fintype.card_fin]
  exact mul_le_mul h2 h3 (Finset.prod_nonneg fun _ _ => midpointBump_nonneg _ _) (by positivity)
variable {ℓ : Fin d → ℕ} {hℓ : ∀ μ, 1 ≤ ℓ μ}
def coarseLineValues (N : ℕ) (ω : ScalarField 1 (LatticeShape.torus ℓ hℓ)) (n : Fin d → ℤ)
    (μ : Fin d) (q : ℤ) : ℝ :=
  ScalarField.eval ω (torusSite 1 ℓ hℓ (Function.update (fun ν => n ν / (N : ℤ)) μ q))
theorem bumpCoeff_update (ω : ScalarField 1 (LatticeShape.torus ℓ hℓ)) (n : Fin d → ℤ)
    (μ : Fin d) (s : ℤ) :
    bumpCoeff N ω (Function.update n μ s) =
      transverseFactor N n μ * lineProfile N (coarseLineValues N ω n μ) s := by
  have h1 : (fun ν => Function.update n μ s ν / (N : ℤ)) =
      Function.update (fun ν => n ν / (N : ℤ)) μ (s / N) := by
    funext ν
    by_cases h : ν = μ
    · subst h
      simp
    · simp [Function.update_of_ne h]
  have h2 : ∏ ν, midpointBump N (Function.update n μ s ν % N) =
      midpointBump N (s % N) * ∏ ν ∈ Finset.univ.erase μ, midpointBump N (n ν % N) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ μ)]
    simp only [Function.update_self]
    congr 1
    exact Finset.prod_congr rfl fun ν hν => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hν)]
  unfold bumpCoeff transverseFactor lineProfile coarseLineValues
  rw [h1, h2]
  ring
theorem bumpCoeff_secondDiff [NeZero N] (ω : ScalarField 1 (LatticeShape.torus ℓ hℓ))
    (n : Fin d → ℤ) (μ : Fin d) :
    |bumpCoeff N ω (Function.update n μ (n μ + 1)) +
        bumpCoeff N ω (Function.update n μ (n μ - 1)) - 2 * bumpCoeff N ω n| ≤
      transverseFactor N n μ * (2 * ((N : ℝ)⁻¹) ^ 2 *
        (|ScalarField.eval ω (torusSite 1 ℓ hℓ fun ν => n ν / (N : ℤ))| +
          |ScalarField.eval ω
            (torusSite 1 ℓ hℓ (fun ν => n ν / (N : ℤ)) + unitStep 1 (LatticeShape.torus ℓ hℓ) μ)| +
          |ScalarField.eval ω
            (torusSite 1 ℓ hℓ (fun ν => n ν / (N : ℤ)) -
              unitStep 1 (LatticeShape.torus ℓ hℓ) μ)|)) := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have e0 : bumpCoeff N ω n =
      transverseFactor N n μ * lineProfile N (coarseLineValues N ω n μ) (n μ) := by
    have := bumpCoeff_update (N := N) ω n μ (n μ)
    rwa [Function.update_eq_self] at this
  have w0 : coarseLineValues N ω n μ (n μ / N) =
      ScalarField.eval ω (torusSite 1 ℓ hℓ fun ν => n ν / (N : ℤ)) := by
    show ScalarField.eval ω (torusSite 1 ℓ hℓ (Function.update (fun ν => n ν / (N : ℤ)) μ
      ((fun ν => n ν / (N : ℤ)) μ))) = _
    rw [Function.update_eq_self]
  have w1 : coarseLineValues N ω n μ (n μ / N + 1) = ScalarField.eval ω
      (torusSite 1 ℓ hℓ (fun ν => n ν / (N : ℤ)) + unitStep 1 (LatticeShape.torus ℓ hℓ) μ) := by
    rw [torusSite_add_unitStep]
    rfl
  have w2 : coarseLineValues N ω n μ (n μ / N - 1) = ScalarField.eval ω
      (torusSite 1 ℓ hℓ (fun ν => n ν / (N : ℤ)) - unitStep 1 (LatticeShape.torus ℓ hℓ) μ) := by
    rw [torusSite_sub_unitStep]
    rfl
  have hP := lineProfile_secondDiff hN0 (coarseLineValues N ω n μ) (n μ)
  rw [w0, w1, w2] at hP
  rw [bumpCoeff_update, bumpCoeff_update, e0]
  have hc := transverseFactor_nonneg (N := N) n μ
  have hl : ∀ a b c : ℝ, transverseFactor N n μ * a + transverseFactor N n μ * b -
      2 * (transverseFactor N n μ * c) = transverseFactor N n μ * (a + b - 2 * c) :=
    fun a b c => by ring
  rw [hl, abs_mul, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left hP hc
theorem abs_backwardDiff_forwardDiff_le [NeZero N] (ω : ScalarField 1 (LatticeShape.torus ℓ hℓ))
    (y : LatticeSite 1 (LatticeShape.torus ℓ hℓ)) (r : Fin d → Fin N) (μ : Fin d) :
    |backwardDiff μ (forwardDiff μ (bumpField N ω)) (cellSite N (y, r)) scalarIndex| ≤
      2 * (30 ^ d * 16 ^ (1 - (d : ℤ))) *
        (|ScalarField.eval ω y| +
          |ScalarField.eval ω (y + unitStep 1 (LatticeShape.torus ℓ hℓ) μ)| +
          |ScalarField.eval ω (y - unitStep 1 (LatticeShape.torus ℓ hℓ) μ)|) := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  set n := cellCoords N y r with hn
  have hb : (torusSite 1 ℓ hℓ fun ν => n ν / (N : ℤ)) = y := by
    simp only [hn, cellCoords, natMul_add_fin_ediv]
    exact torusSite_coarseCoords y
  have L := bumpCoeff_secondDiff (N := N) ω n μ
  rw [hb] at L
  have hx : (cellSite N (y, r) : LatticeSite N (LatticeShape.torus ℓ hℓ)) = torusSite N ℓ hℓ n :=
    rfl
  rw [backwardDiff_forwardDiff_scalar, hx, torusSite_add_unitStep, torusSite_sub_unitStep,
    bumpField_apply, bumpField_apply, bumpField_apply, abs_neg, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 2)]
  set B := |ScalarField.eval ω y| +
    |ScalarField.eval ω (y + unitStep 1 (LatticeShape.torus ℓ hℓ) μ)| +
    |ScalarField.eval ω (y - unitStep 1 (LatticeShape.torus ℓ hℓ) μ)| with hB
  have hB0 : 0 ≤ B := by positivity
  calc _ ≤ (N : ℝ) ^ 2 * (transverseFactor N n μ * (2 * ((N : ℝ)⁻¹) ^ 2 * B)) :=
        mul_le_mul_of_nonneg_left L (by positivity)
    _ = 2 * transverseFactor N n μ * B := by
        field_simp
    _ ≤ _ := by
        have := transverseFactor_le (N := N) n μ
        exact mul_le_mul_of_nonneg_right (by linarith) hB0
theorem fieldInner_self_eq_sum {κ : LatticeShape d} [Fintype (LatticeSite N κ)]
    (F : ScalarField N κ) :
    fieldInner F F = ∑ x, latticeSpacing N ^ d * ScalarField.eval F x ^ 2 := by
  unfold fieldInner
  rw [tsum_fintype, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_unique]
  have hi : (default : Fin 0 → Fin d) = scalarIndex := Subsingleton.elim _ _
  rw [hi]
  simp only [ScalarField.eval]
  ring
variable [Fintype (LatticeSite N (LatticeShape.torus ℓ hℓ))]
  [Fintype (LatticeSite 1 (LatticeShape.torus ℓ hℓ))]
theorem fieldNorm_tensorLaplacian_bumpField_le [NeZero N]
    (ω : ScalarField 1 (LatticeShape.torus ℓ hℓ)) :
    fieldNorm (tensorLaplacian (bumpField N ω)) ≤
      6 * (d : ℝ) * 30 ^ d * 16 ^ (1 - (d : ℤ)) * fieldNorm ω := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  set C : ℝ := 30 ^ d * 16 ^ (1 - (d : ℤ)) with hC
  set Ω : ℝ := ∑ y, ScalarField.eval ω y ^ 2 with hΩ
  set A : LatticeSite 1 (LatticeShape.torus ℓ hℓ) → Fin d → ℝ := fun y μ =>
    ScalarField.eval ω y ^ 2 +
    ScalarField.eval ω (y + unitStep 1 (LatticeShape.torus ℓ hℓ) μ) ^ 2 +
    ScalarField.eval ω (y - unitStep 1 (LatticeShape.torus ℓ hℓ) μ) ^ 2 with hA
  have hT : ∀ y (r : Fin d → Fin N) μ,
      backwardDiff μ (forwardDiff μ (bumpField N ω)) (cellSite N (y, r)) scalarIndex ^ 2 ≤
        12 * C ^ 2 * A y μ := fun y r μ => by
    have h := abs_backwardDiff_forwardDiff_le (N := N) ω y r μ
    rw [← hC] at h
    set T := backwardDiff μ (forwardDiff μ (bumpField N ω)) (cellSite N (y, r)) scalarIndex
    set a := |ScalarField.eval ω y|
    set b := |ScalarField.eval ω (y + unitStep 1 (LatticeShape.torus ℓ hℓ) μ)|
    set c := |ScalarField.eval ω (y - unitStep 1 (LatticeShape.torus ℓ hℓ) μ)|
    have ha : a ^ 2 = ScalarField.eval ω y ^ 2 := sq_abs _
    have hb : b ^ 2 = ScalarField.eval ω (y + unitStep 1 (LatticeShape.torus ℓ hℓ) μ) ^ 2 :=
      sq_abs _
    have hc : c ^ 2 = ScalarField.eval ω (y - unitStep 1 (LatticeShape.torus ℓ hℓ) μ) ^ 2 :=
      sq_abs _
    have h1 : T ^ 2 ≤ (2 * C * (a + b + c)) ^ 2 := sq_le_sq' (abs_le.mp h).1 (abs_le.mp h).2
    have h2 : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
    have h3 : (2 * C * (a + b + c)) ^ 2 ≤ 12 * C ^ 2 * (a ^ 2 + b ^ 2 + c ^ 2) := by
      have : 0 ≤ C ^ 2 := sq_nonneg C
      nlinarith
    simp only [hA]
    rw [← ha, ← hb, ← hc]
    exact h1.trans h3
  have hV : ∀ y (r : Fin d → Fin N),
      ScalarField.eval (tensorLaplacian (bumpField N ω)) (cellSite N (y, r)) ^ 2 ≤
        (d : ℝ) * ∑ μ, 12 * C ^ 2 * A y μ := fun y r => by
    have e : ScalarField.eval (tensorLaplacian (bumpField N ω)) (cellSite N (y, r)) =
        ∑ μ, backwardDiff μ (forwardDiff μ (bumpField N ω)) (cellSite N (y, r)) scalarIndex :=
      tensorLaplacian_scalar _ _ _
    rw [e]
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
      (f := fun μ => backwardDiff μ (forwardDiff μ (bumpField N ω)) (cellSite N (y, r))
        scalarIndex)
    rw [Finset.card_univ, Fintype.card_fin] at h
    refine h.trans ?_
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun μ _ => hT y r μ) (by positivity)
  have hshift : ∀ μ, ∑ y, A y μ = 3 * Ω := fun μ => by
    simp only [hA]
    have s1 : ∑ y, ScalarField.eval ω (y + unitStep 1 (LatticeShape.torus ℓ hℓ) μ) ^ 2 = Ω :=
      Equiv.sum_comp (Equiv.addRight (unitStep 1 (LatticeShape.torus ℓ hℓ) μ))
        (fun y => ScalarField.eval ω y ^ 2)
    have s2 : ∑ y, ScalarField.eval ω (y - unitStep 1 (LatticeShape.torus ℓ hℓ) μ) ^ 2 = Ω :=
      Equiv.sum_comp (Equiv.subRight (unitStep 1 (LatticeShape.torus ℓ hℓ) μ))
        (fun y => ScalarField.eval ω y ^ 2)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, s1, s2, ← hΩ]
    ring
  have hvol : latticeSpacing N ^ d * ((Finset.univ : Finset (Fin d → Fin N)).card : ℝ) = 1 := by
    have : ((Finset.univ : Finset (Fin d → Fin N)).card : ℝ) = (N : ℝ) ^ d := by simp
    rw [this, ← mul_pow, latticeSpacing, inv_mul_cancel₀ hN, one_pow]
  have hS : fieldInner (tensorLaplacian (bumpField N ω)) (tensorLaplacian (bumpField N ω)) ≤
      (6 * (d : ℝ) * C) ^ 2 * Ω := by
    rw [fieldInner_self_eq_sum,
      ← Equiv.sum_comp (cellSiteEquiv (ℓ := ℓ) (hℓ := hℓ) N), Fintype.sum_prod_type]
    have hη : 0 ≤ latticeSpacing N ^ d := by
      unfold latticeSpacing
      positivity
    calc ∑ y, ∑ r : Fin d → Fin N, latticeSpacing N ^ d *
          ScalarField.eval (tensorLaplacian (bumpField N ω)) (cellSiteEquiv N (y, r)) ^ 2
        ≤ ∑ y, ∑ _r : Fin d → Fin N, latticeSpacing N ^ d *
            ((d : ℝ) * ∑ μ, 12 * C ^ 2 * A y μ) :=
          Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun r _ =>
            mul_le_mul_of_nonneg_left (hV y r) hη
      _ = ∑ y, (d : ℝ) * ∑ μ, 12 * C ^ 2 * A y μ := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, mul_comm _ (latticeSpacing N ^ d),
            hvol, one_mul]
      _ = (d : ℝ) * ∑ μ, 12 * C ^ 2 * ∑ y, A y μ := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          simp only [Finset.mul_sum]
      _ = (6 * (d : ℝ) * C) ^ 2 * Ω := by
          simp only [hshift]
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hΩ' : fieldInner ω ω = Ω := by
    rw [fieldInner_self_eq_sum]
    simp [latticeSpacing, hΩ]
  have hK : 0 ≤ 6 * (d : ℝ) * C := by positivity
  have hgoal : 6 * (d : ℝ) * 30 ^ d * 16 ^ (1 - (d : ℤ)) * fieldNorm ω =
      6 * (d : ℝ) * C * Real.sqrt Ω := by
    rw [fieldNorm, hΩ', hC]
    ring
  rw [hgoal, fieldNorm]
  calc Real.sqrt (fieldInner (tensorLaplacian (bumpField N ω)) (tensorLaplacian (bumpField N ω)))
      ≤ Real.sqrt ((6 * (d : ℝ) * C) ^ 2 * Ω) := Real.sqrt_le_sqrt hS
    _ = 6 * (d : ℝ) * C * Real.sqrt Ω := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hK]
end Laplacian
theorem claim_holds : BlockBumpFunctions.Claim := by
  intro d L k _ hL ℓ hℓ ω
  have : NeZero (L ^ k) := ⟨pow_ne_zero _ (by omega)⟩
  have := finite_torusSites (ℓ := ℓ) (hℓ := hℓ) (L ^ k)
  have := finite_torusSites (ℓ := ℓ) (hℓ := hℓ) 1
  let := Fintype.ofFinite (LatticeSite (L ^ k) (LatticeShape.torus ℓ hℓ))
  let := Fintype.ofFinite (LatticeSite 1 (LatticeShape.torus ℓ hℓ))
  exact ⟨bumpField (L ^ k) ω, fun y hy x hx => bumpField_eq_zero_of_coarse ω y hy x hx,
    siteBlockAvg_bumpField ω, fieldNorm_tensorLaplacian_bumpField_le ω⟩
end YangMills.Construction.LatticeFields.BlockBumpFunctions
