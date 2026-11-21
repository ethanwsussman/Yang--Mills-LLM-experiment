import YangMills.Construction.Towers.ThirdOrderVanishingAsACubicBound
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.Coordinates YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy
noncomputable section
namespace YangMills.Construction.Tower.CubicVanishing
theorem eq_zero_of_norm_le_const_mul {E : Type*} [NormedAddCommGroup E] (v : E) (M η : ℝ) (hη : 0 < η)
    (h : ∀ t : ℝ, 0 < t → t < η → ‖v‖ ≤ M * t) : v = 0 := by
  by_contra hv
  have hv' : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hM : 0 < M := by
    have h1 := h (η / 2) (by positivity) (by linarith)
    by_contra hM
    have h2 : M * (η / 2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hM) (by positivity)
    linarith
  have ht0 : 0 < min (η / 2) (‖v‖ / (2 * M)) := lt_min (by positivity) (by positivity)
  have ht1 : min (η / 2) (‖v‖ / (2 * M)) < η := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have ht2 : min (η / 2) (‖v‖ / (2 * M)) ≤ ‖v‖ / (2 * M) := min_le_right _ _
  have h1 := h _ ht0 ht1
  have h3 : M * min (η / 2) (‖v‖ / (2 * M)) ≤ ‖v‖ / 2 := by
    calc M * min (η / 2) (‖v‖ / (2 * M)) ≤ M * (‖v‖ / (2 * M)) :=
          mul_le_mul_of_nonneg_left ht2 hM.le
      _ = ‖v‖ / 2 := by field_simp
  linarith
theorem quadratic_coeffs_eq_zero_of_cubic_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (a b d : E) (K η : ℝ) (hη : 0 < η)
    (h : ∀ t : ℝ, 0 < t → t < η → ‖a + (t : ℂ) • b + ((t : ℂ) ^ 2) • d‖ ≤ K * t ^ 3) :
    a = 0 ∧ b = 0 ∧ d = 0 := by
  have hη1 : 0 < min η 1 := lt_min hη one_pos
  have hnb : ∀ (t : ℝ) (x : E), 0 < t → ‖(t : ℂ) • x‖ = t * ‖x‖ := by
    intro t x ht
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  have hnd : ∀ (t : ℝ) (x : E), 0 < t → ‖((t : ℂ) ^ 2) • x‖ = t ^ 2 * ‖x‖ := by
    intro t x ht
    rw [norm_smul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  have hK : K ≤ |K| := le_abs_self K
  have hK0 : 0 ≤ |K| := abs_nonneg K
  have ha : a = 0 := by
    refine eq_zero_of_norm_le_const_mul a (|K| + ‖b‖ + ‖d‖) (min η 1) hη1 ?_
    intro t ht0 ht1
    have h1 : t < η := lt_of_lt_of_le ht1 (min_le_left _ _)
    have h2 : t < 1 := lt_of_lt_of_le ht1 (min_le_right _ _)
    have h3 := h t ht0 h1
    have h4 : ‖a‖ ≤ ‖a + (t : ℂ) • b + ((t : ℂ) ^ 2) • d‖ + ‖(t : ℂ) • b‖ + ‖((t : ℂ) ^ 2) • d‖ := by
      calc ‖a‖ = ‖(a + (t : ℂ) • b + ((t : ℂ) ^ 2) • d) + -((t : ℂ) • b)
              + -(((t : ℂ) ^ 2) • d)‖ := by congr 1; abel
        _ ≤ _ := norm_add₃_le
        _ = _ := by rw [norm_neg, norm_neg]
    rw [hnb t b ht0, hnd t d ht0] at h4
    have h5 : t ^ 3 ≤ t := by nlinarith [mul_pos ht0 ht0, mul_pos (mul_pos ht0 ht0) ht0]
    have h6 : t ^ 2 ≤ t := by nlinarith
    have h7 : K * t ^ 3 ≤ |K| * t := by
      calc K * t ^ 3 ≤ |K| * t ^ 3 := mul_le_mul_of_nonneg_right hK (by positivity)
        _ ≤ |K| * t := mul_le_mul_of_nonneg_left h5 hK0
    have h8 : t ^ 2 * ‖d‖ ≤ t * ‖d‖ := mul_le_mul_of_nonneg_right h6 (norm_nonneg d)
    nlinarith
  subst ha
  have hb : b = 0 := by
    refine eq_zero_of_norm_le_const_mul b (|K| + ‖d‖) (min η 1) hη1 ?_
    intro t ht0 ht1
    have h1 : t < η := lt_of_lt_of_le ht1 (min_le_left _ _)
    have h2 : t < 1 := lt_of_lt_of_le ht1 (min_le_right _ _)
    have h3 := h t ht0 h1
    have e : (0 : E) + (t : ℂ) • b + ((t : ℂ) ^ 2) • d = (t : ℂ) • (b + (t : ℂ) • d) := by
      module
    rw [e, hnb t _ ht0] at h3
    have h4 : ‖b + (t : ℂ) • d‖ ≤ K * t ^ 2 := by
      have h5 : t * ‖b + (t : ℂ) • d‖ ≤ t * (K * t ^ 2) := by
        calc t * ‖b + (t : ℂ) • d‖ ≤ K * t ^ 3 := h3
          _ = t * (K * t ^ 2) := by ring
      exact le_of_mul_le_mul_left h5 ht0
    have h6 : ‖b‖ ≤ ‖b + (t : ℂ) • d‖ + ‖(t : ℂ) • d‖ := by
      calc ‖b‖ = ‖(b + (t : ℂ) • d) + -((t : ℂ) • d)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
        _ = _ := by rw [norm_neg]
    rw [hnb t d ht0] at h6
    have h7 : t ^ 2 ≤ t := by nlinarith
    have h8 : K * t ^ 2 ≤ |K| * t := by
      calc K * t ^ 2 ≤ |K| * t ^ 2 := mul_le_mul_of_nonneg_right hK (by positivity)
        _ ≤ |K| * t := mul_le_mul_of_nonneg_left h7 hK0
    nlinarith
  subst hb
  have hd : d = 0 := by
    refine eq_zero_of_norm_le_const_mul d |K| η hη ?_
    intro t ht0 h1
    have h3 := h t ht0 h1
    have e : (0 : E) + (t : ℂ) • (0 : E) + ((t : ℂ) ^ 2) • d = ((t : ℂ) ^ 2) • d := by simp
    rw [e, hnd t d ht0] at h3
    have h5 : t ^ 2 * ‖d‖ ≤ t ^ 2 * (K * t) := by
      calc t ^ 2 * ‖d‖ ≤ K * t ^ 3 := h3
        _ = t ^ 2 * (K * t) := by ring
    have h6 : ‖d‖ ≤ K * t := le_of_mul_le_mul_left h5 (by positivity)
    have h7 : K * t ≤ |K| * t := mul_le_mul_of_nonneg_right hK ht0.le
    linarith
  exact ⟨rfl, rfl, hd⟩
def lowOrderIndices : Finset (Fin 2 → ℕ) :=
  {![0, 0], ![1, 0], ![0, 1], ![2, 0], ![1, 1], ![0, 2]}
theorem mem_lowOrderIndices (m : Fin 2 → ℕ) : m ∈ lowOrderIndices ↔ m 0 + m 1 < 3 := by
  constructor
  · intro h
    simp only [lowOrderIndices, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro h
    obtain ⟨a, b, rfl⟩ : ∃ a b : ℕ, m = ![a, b] :=
      ⟨m 0, m 1, by ext i; fin_cases i <;> rfl⟩
    have h' : a + b < 3 := by simpa using h
    have ha : a < 3 := by omega
    have hb : b < 3 := by omega
    interval_cases a <;> interval_cases b <;> first | omega | decide
theorem sum_lowOrderIndices (c : (Fin 2 → ℕ) → ComplexCoordinates 4) (z : ComplexCoordinates 2) :
    ∑ m ∈ lowOrderIndices, monomialTerm c 0 z m =
      c ![0, 0] + z 0 • c ![1, 0] + z 1 • c ![0, 1] + (z 0) ^ 2 • c ![2, 0] +
        (z 0 * z 1) • c ![1, 1] + (z 1) ^ 2 • c ![0, 2] := by
  unfold lowOrderIndices
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [monomialTerm, Fin.prod_univ_two]
  simp
  abel
theorem norm_monomialTerm_le_cube (c : (Fin 2 → ℕ) → ComplexCoordinates 4) (r : ℝ) (hr : 0 < r)
    (z : ComplexCoordinates 2) (hz : ‖z‖ ≤ r) (m : Fin 2 → ℕ) (hm : 3 ≤ m 0 + m 1) :
    ‖monomialTerm c 0 z m‖ ≤ (‖z‖ / r) ^ 3 * ‖monomialTerm c 0 (fun _ => (r : ℂ)) m‖ := by
  obtain ⟨k, hk⟩ : ∃ k, m 0 + m 1 = k + 3 := ⟨m 0 + m 1 - 3, by omega⟩
  have h0 : ‖z 0‖ ≤ ‖z‖ := norm_le_pi_norm z 0
  have h1 : ‖z 1‖ ≤ ‖z‖ := norm_le_pi_norm z 1
  have e1 : ‖monomialTerm c 0 z m‖ = ‖z 0‖ ^ m 0 * ‖z 1‖ ^ m 1 * ‖c m‖ := by
    simp [monomialTerm, Fin.prod_univ_two, norm_smul]
  have e2 : ‖monomialTerm c 0 (fun _ => (r : ℂ)) m‖ = r ^ (k + 3) * ‖c m‖ := by
    rw [← hk, pow_add]
    simp [monomialTerm, Fin.prod_univ_two, norm_smul, abs_of_pos hr]
  rw [e1, e2]
  have h2 : ‖z 0‖ ^ m 0 * ‖z 1‖ ^ m 1 ≤ ‖z‖ ^ (k + 3) := by
    rw [← hk, pow_add]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) h0 _)
      (pow_le_pow_left₀ (norm_nonneg _) h1 _) (by positivity) (by positivity)
  have h3 : ‖z‖ ^ (k + 3) ≤ (‖z‖ / r) ^ 3 * r ^ (k + 3) := by
    have e3 : (‖z‖ / r) ^ 3 * r ^ (k + 3) = r ^ k * ‖z‖ ^ 3 := by
      field_simp
      ring
    rw [e3, pow_add]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hz _) (by positivity)
  calc ‖z 0‖ ^ m 0 * ‖z 1‖ ^ m 1 * ‖c m‖ ≤ (‖z‖ / r) ^ 3 * r ^ (k + 3) * ‖c m‖ :=
        mul_le_mul_of_nonneg_right (h2.trans h3) (norm_nonneg _)
    _ = _ := by ring
theorem norm_sub_sum_lowOrderIndices_le (c : (Fin 2 → ℕ) → ComplexCoordinates 4) (r A : ℝ) (hr : 0 < r)
    (z : ComplexCoordinates 2) (hz : ‖z‖ ≤ r) (F : ComplexCoordinates 4)
    (hF : HasSum (monomialTerm c 0 z) F)
    (hA : HasSum (fun m => ‖monomialTerm c 0 (fun _ => (r : ℂ)) m‖) A) :
    ‖F - ∑ m ∈ lowOrderIndices, monomialTerm c 0 z m‖ ≤ (‖z‖ / r) ^ 3 * A := by
  have h1 : HasSum (fun m => if m ∈ lowOrderIndices then monomialTerm c 0 z m else 0)
      (∑ m ∈ lowOrderIndices, monomialTerm c 0 z m) := by
    have h2 : HasSum (fun m => if m ∈ lowOrderIndices then monomialTerm c 0 z m else 0)
        (∑ m ∈ lowOrderIndices, (if m ∈ lowOrderIndices then monomialTerm c 0 z m else 0)) :=
      hasSum_sum_of_ne_finset_zero (fun b hb => by simp [hb])
    have e : ∑ m ∈ lowOrderIndices, (if m ∈ lowOrderIndices then monomialTerm c 0 z m else 0) =
        ∑ m ∈ lowOrderIndices, monomialTerm c 0 z m :=
      Finset.sum_congr rfl (fun m hm => by simp [hm])
    rwa [e] at h2
  refine (hF.sub h1).norm_le_of_bounded (hA.mul_left _) ?_
  intro m
  by_cases hm : m ∈ lowOrderIndices
  · simp only [hm, if_true, sub_self, norm_zero]
    positivity
  · simp only [hm, if_false, sub_zero]
    exact norm_monomialTerm_le_cube c r hr z hz m (not_lt.mp (fun h => hm ((mem_lowOrderIndices m).mpr h)))
theorem exists_hasSum_norm_monomialTerm (c : (Fin 2 → ℕ) → ComplexCoordinates 4)
    (f : ComplexCoordinates 2 → ComplexCoordinates 4) (ρ : ℝ) (hρ : 0 < ρ)
    (hc : ∀ z ∈ openPolydisk 0 ρ, HasSum (monomialTerm c 0 z) (f z)) :
    ∃ A : ℝ, 0 ≤ A ∧
      HasSum (fun m => ‖monomialTerm c 0 (fun _ => (((ρ / 2 : ℝ)) : ℂ)) m‖) A := by
  have hw : (fun _ => (((ρ / 2 : ℝ)) : ℂ)) ∈ openPolydisk (0 : ComplexCoordinates 2) ρ := by
    intro j
    simp only [Pi.zero_apply, sub_zero, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (by positivity)]
    linarith
  have hs : Summable fun m => ‖monomialTerm c 0 (fun _ => (((ρ / 2 : ℝ)) : ℂ)) m‖ :=
    summable_norm_iff.mpr (hc _ hw).summable
  exact ⟨_, tsum_nonneg (fun _ => norm_nonneg _), hs.hasSum⟩
theorem mem_openPolydisk_of_norm_lt (ρ : ℝ) (z : ComplexCoordinates 2) (hz : ‖z‖ < ρ) :
    z ∈ openPolydisk (0 : ComplexCoordinates 2) ρ := by
  intro j
  simpa using lt_of_le_of_lt (norm_le_pi_norm z j) hz
theorem exists_closedPolydisk_subset (U : Set (ComplexCoordinates 2)) (hU : IsOpen U)
    (h0 : (0 : ComplexCoordinates 2) ∈ U) : ∃ ρ : ℝ, 0 < ρ ∧ closedPolydisk 0 ρ ⊆ U := by
  obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp hU 0 h0
  refine ⟨ε / 2, by positivity, fun z hz => hb ?_⟩
  rw [Metric.mem_ball, dist_zero_right]
  have h1 : ‖z‖ ≤ ε / 2 := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j => ?_
    simpa using hz j
  linarith
theorem cubic_bound_of_low_coeffs_eq_zero (f : ComplexCoordinates 2 → ComplexCoordinates 4)
    (c : (Fin 2 → ℕ) → ComplexCoordinates 4) (ρ : ℝ) (hρ : 0 < ρ)
    (hc : ∀ z ∈ openPolydisk 0 ρ, HasSum (monomialTerm c 0 z) (f z))
    (hlow : ∀ m : Fin 2 → ℕ, m 0 + m 1 < 3 → c m = 0) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ z : ComplexCoordinates 2, ‖z‖ < δ → ‖f z‖ ≤ C * ‖z‖ ^ 3 := by
  obtain ⟨A, hA0, hA⟩ := exists_hasSum_norm_monomialTerm c f ρ hρ hc
  have hr : 0 < ρ / 2 := by positivity
  refine ⟨A / (ρ / 2) ^ 3 + 1, ρ / 2, by positivity, hr, fun z hz => ?_⟩
  have hzρ : ‖z‖ < ρ := by linarith
  have h1 := norm_sub_sum_lowOrderIndices_le c (ρ / 2) A hr z hz.le (f z)
    (hc z (mem_openPolydisk_of_norm_lt ρ z hzρ)) hA
  have h2 : ∑ m ∈ lowOrderIndices, monomialTerm c 0 z m = 0 := by
    refine Finset.sum_eq_zero fun m hm => ?_
    simp [monomialTerm, hlow m ((mem_lowOrderIndices m).mp hm)]
  rw [h2, sub_zero] at h1
  have e : (‖z‖ / (ρ / 2)) ^ 3 * A = A / (ρ / 2) ^ 3 * ‖z‖ ^ 3 := by
    rw [div_pow]
    ring
  rw [e] at h1
  have h3 : 0 ≤ ‖z‖ ^ 3 := by positivity
  nlinarith
theorem low_coeff_eq_zero_of_cubic_bound (f : ComplexCoordinates 2 → ComplexCoordinates 4)
    (c : (Fin 2 → ℕ) → ComplexCoordinates 4) (ρ : ℝ) (hρ : 0 < ρ)
    (hc : ∀ z ∈ openPolydisk 0 ρ, HasSum (monomialTerm c 0 z) (f z))
    (C δ : ℝ) (hC : 0 < C) (hδ : 0 < δ)
    (hb : ∀ z : ComplexCoordinates 2, ‖z‖ < δ → ‖f z‖ ≤ C * ‖z‖ ^ 3)
    (m : Fin 2 → ℕ) (hm : m 0 + m 1 < 3) : c m = 0 := by
  obtain ⟨A, hA0, hA⟩ := exists_hasSum_norm_monomialTerm c f ρ hρ hc
  have hr : 0 < ρ / 2 := by positivity
  have hbound : ∀ z : ComplexCoordinates 2, ‖z‖ < ρ / 2 → ‖z‖ < δ →
      ‖∑ m ∈ lowOrderIndices, monomialTerm c 0 z m‖ ≤ (C + A / (ρ / 2) ^ 3) * ‖z‖ ^ 3 := by
    intro z hz1 hz2
    have hzρ : ‖z‖ < ρ := by linarith
    have h1 := norm_sub_sum_lowOrderIndices_le c (ρ / 2) A hr z hz1.le (f z)
      (hc z (mem_openPolydisk_of_norm_lt ρ z hzρ)) hA
    have h2 := hb z hz2
    have e : (‖z‖ / (ρ / 2)) ^ 3 * A = A / (ρ / 2) ^ 3 * ‖z‖ ^ 3 := by
      rw [div_pow]
      ring
    rw [e] at h1
    have h3 : ‖∑ m ∈ lowOrderIndices, monomialTerm c 0 z m‖ ≤
        ‖f z‖ + ‖f z - ∑ m ∈ lowOrderIndices, monomialTerm c 0 z m‖ := by
      calc ‖∑ m ∈ lowOrderIndices, monomialTerm c 0 z m‖
          = ‖f z + -(f z - ∑ m ∈ lowOrderIndices, monomialTerm c 0 z m)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
        _ = _ := by rw [norm_neg]
    calc _ ≤ _ := h3
      _ ≤ C * ‖z‖ ^ 3 + A / (ρ / 2) ^ 3 * ‖z‖ ^ 3 := add_le_add h2 h1
      _ = _ := by ring
  have hK : 0 ≤ C + A / (ρ / 2) ^ 3 := by positivity
  have hη : 0 < min (ρ / 2) δ := lt_min hr hδ
  have line : ∀ p q : ℂ, ‖p‖ ≤ 1 → ‖q‖ ≤ 1 →
      c ![0, 0] = 0 ∧ p • c ![1, 0] + q • c ![0, 1] = 0 ∧
        (p ^ 2) • c ![2, 0] + (p * q) • c ![1, 1] + (q ^ 2) • c ![0, 2] = 0 := by
    intro p q hp hq
    refine quadratic_coeffs_eq_zero_of_cubic_bound _ _ _ (C + A / (ρ / 2) ^ 3) (min (ρ / 2) δ) hη ?_
    intro t ht0 ht1
    have hnorm : ‖(![(t : ℂ) * p, (t : ℂ) * q] : ComplexCoordinates 2)‖ ≤ t := by
      refine (pi_norm_le_iff_of_nonneg ht0.le).mpr fun j => ?_
      have ht : ‖(t : ℂ)‖ = t := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
      fin_cases j
      · simp only [Fin.zero_eta, Matrix.cons_val_zero, norm_mul, ht]
        nlinarith
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, norm_mul, ht]
        nlinarith
    have h1 : t < ρ / 2 := lt_of_lt_of_le ht1 (min_le_left _ _)
    have h2 : t < δ := lt_of_lt_of_le ht1 (min_le_right _ _)
    have h3 := hbound ![(t : ℂ) * p, (t : ℂ) * q] (lt_of_le_of_lt hnorm h1)
      (lt_of_le_of_lt hnorm h2)
    have e : ∑ m ∈ lowOrderIndices, monomialTerm c 0 ![(t : ℂ) * p, (t : ℂ) * q] m =
        c ![0, 0] + (t : ℂ) • (p • c ![1, 0] + q • c ![0, 1]) +
          ((t : ℂ) ^ 2) • ((p ^ 2) • c ![2, 0] + (p * q) • c ![1, 1] + (q ^ 2) • c ![0, 2]) := by
      rw [sum_lowOrderIndices]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      module
    rw [e] at h3
    calc _ ≤ _ := h3
      _ ≤ (C + A / (ρ / 2) ^ 3) * t ^ 3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm 3) hK
  obtain ⟨h00, h10, h20⟩ := line 1 0 (by simp) (by simp)
  obtain ⟨-, h01, h02⟩ := line 0 1 (by simp) (by simp)
  obtain ⟨-, -, h11⟩ := line 1 1 (by simp) (by simp)
  simp only [one_smul, zero_smul, add_zero, zero_add, one_pow, mul_zero, mul_one,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h10 h20 h01 h02 h11
  rw [h20, h02] at h11
  simp only [add_zero, zero_add] at h11
  have hmem := (mem_lowOrderIndices m).mpr hm
  simp only [lowOrderIndices, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h00
  · exact h10
  · exact h01
  · exact h20
  · exact h11
  · exact h02
theorem vanishingOrderThreeIffCubicBound_of_powerSeries
    (h : ComplexCoordinates.PowerSeriesHolomorphy.Properties) :
    Tower.VanishingOrderThreeIffCubicBound := by
  intro U f h0 hf
  obtain ⟨ρ, hρ, hsub⟩ := exists_closedPolydisk_subset U hf.1 h0
  constructor
  · intro hv
    obtain ⟨c, hc, -⟩ := ((h.1 2 U hf.1).1 4 f hf).1 0 h0 ρ hρ hsub
    exact cubic_bound_of_low_coeffs_eq_zero f c ρ hρ hc (hv ρ hρ hsub c hc)
  · rintro ⟨C, δ, hC, hδ, hb⟩ ρ' hρ' _ c hc m hm
    exact low_coeff_eq_zero_of_cubic_bound f c ρ' hρ' hc C δ hC hδ hb m hm
end YangMills.Construction.Tower.CubicVanishing
end
