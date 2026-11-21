import YangMills.Construction.Torus.CoefficientsOfATestFunctionOnTheBox
import YangMills.Construction.Torus.WeightedSumOfTheCoefficientsOfATestFunction
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Torus.FourierBox.WeightedCoeffSum
theorem euclidNormInt_nonneg (v : Fin 4 → ℤ) : 0 ≤ euclidNormInt v :=
  Real.sqrt_nonneg _
theorem supNormInt_zero {D : ℕ} : supNormInt (0 : Fin D → ℤ) = 0 :=
  le_antisymm (Finset.sup_le fun _ _ => by simp) (Nat.zero_le _)
theorem natAbs_le_supNormInt {D : ℕ} (k : Fin D → ℤ) (j : Fin D) :
    (k j).natAbs ≤ supNormInt k :=
  Finset.le_sup (f := fun j => (k j).natAbs) (Finset.mem_univ j)
theorem euclidNormInt_blockOf_le {n : ℕ} (k : Fin (4 * n) → ℤ) (i : Fin n) :
    euclidNormInt (blockOf k i) ≤ 2 * (supNormInt k : ℝ) := by
  have hsq : ∀ μ : Fin 4, ((blockOf k i μ : ℤ) : ℝ) ^ 2 ≤ (supNormInt k : ℝ) ^ 2 := by
    intro μ
    have h1 : (blockOf k i μ).natAbs ≤ supNormInt k := natAbs_le_supNormInt k _
    have h2 : |((blockOf k i μ : ℤ) : ℝ)| ≤ (supNormInt k : ℝ) := by
      rw [← Int.cast_abs, Int.abs_eq_natAbs]
      exact_mod_cast h1
    have h3 := sq_le_sq' (neg_le_of_abs_le h2) (le_of_abs_le h2)
    exact h3
  unfold euclidNormInt TorusMetric.euclidNormVec
  refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
  calc ∑ μ : Fin 4, ((blockOf k i μ : ℤ) : ℝ) ^ 2
      ≤ ∑ _μ : Fin 4, (supNormInt k : ℝ) ^ 2 := Finset.sum_le_sum fun μ _ => hsq μ
    _ = (2 * (supNormInt k : ℝ)) ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
theorem weight_nonneg {n : ℕ} {l : ℝ} (hl : 0 < l) (k : Fin (4 * n) → ℤ) :
    0 ≤ ∏ i, (1 + euclidNormInt (blockOf k i) / l) :=
  Finset.prod_nonneg fun i _ => by
    have := euclidNormInt_nonneg (blockOf k i)
    positivity
theorem weight_le {n : ℕ} {l : ℝ} (hl : 0 < l) (k : Fin (4 * n) → ℤ) :
    ∏ i, (1 + euclidNormInt (blockOf k i) / l) ≤
      (1 + 2 * (supNormInt k : ℝ) / l) ^ n := by
  calc ∏ i, (1 + euclidNormInt (blockOf k i) / l)
      ≤ ∏ _i : Fin n, (1 + 2 * (supNormInt k : ℝ) / l) := by
        refine Finset.prod_le_prod (fun i _ => ?_) (fun i _ => ?_)
        · have := euclidNormInt_nonneg (blockOf k i)
          positivity
        · have := euclidNormInt_blockOf_le k i
          gcongr
    _ = (1 + 2 * (supNormInt k : ℝ) / l) ^ n := by simp
theorem summable_weighted {n : ℕ} {l : ℝ} (hl : 0 < l) (c : (Fin (4 * n) → ℤ) → ℝ)
    (hc : ∀ k, 0 ≤ c k)
    (hs : Summable fun k => c k * (1 + (supNormInt k : ℝ)) ^ (n : ℝ)) :
    Summable fun k => c k * ∏ i, (1 + euclidNormInt (blockOf k i) / l) := by
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (hc k) (weight_nonneg hl k)) (fun k => ?_)
    (hs.mul_left ((1 + 2 / l) ^ n))
  rw [Real.rpow_natCast]
  have h1 : 1 + 2 * (supNormInt k : ℝ) / l ≤ (1 + 2 / l) * (1 + (supNormInt k : ℝ)) := by
    have e : (1 + 2 / l) * (1 + (supNormInt k : ℝ)) =
        1 + 2 * (supNormInt k : ℝ) / l + ((supNormInt k : ℝ) + 2 / l) := by ring
    have h2 : 0 ≤ 2 / l := by positivity
    rw [e]
    linarith
  have h0 : 0 ≤ 1 + 2 * (supNormInt k : ℝ) / l := by positivity
  calc c k * ∏ i, (1 + euclidNormInt (blockOf k i) / l)
      ≤ c k * (1 + 2 * (supNormInt k : ℝ) / l) ^ n :=
        mul_le_mul_of_nonneg_left (weight_le hl k) (hc k)
    _ ≤ c k * ((1 + 2 / l) * (1 + (supNormInt k : ℝ))) ^ n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h1 n) (hc k)
    _ = (1 + 2 / l) ^ n * (c k * (1 + (supNormInt k : ℝ)) ^ n) := by
        rw [mul_pow]
        ring
theorem sum_inv_sq_le_two (T : ℕ) :
    ∑ m ∈ Finset.range T, 1 / ((m : ℝ) + 1) ^ 2 ≤ 2 := by
  have key : ∀ T : ℕ,
      ∑ m ∈ Finset.range (T + 1), 1 / ((m : ℝ) + 1) ^ 2 ≤ 2 - 1 / ((T : ℝ) + 1) := by
    intro T
    induction T with
    | zero => norm_num
    | succ T ih =>
      rw [Finset.sum_range_succ]
      have hT : (0 : ℝ) ≤ T := Nat.cast_nonneg T
      have h : 1 / (((T + 1 : ℕ) : ℝ) + 1) ^ 2 ≤
          1 / ((T : ℝ) + 1) - 1 / (((T + 1 : ℕ) : ℝ) + 1) := by
        push_cast
        rw [div_sub_div _ _ (by positivity) (by positivity),
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith
  cases T with
  | zero => simp
  | succ T =>
    have h := key T
    have h' : 0 ≤ 1 / ((T : ℝ) + 1) := by positivity
    linarith
theorem shell_factor_le (n : ℕ) {l m : ℝ} (hl : 0 < l) (hm : 1 ≤ m) :
    (l / m) ^ (5 * n + 1) * (1 + 2 * m / l) ^ n ≤
      l ^ (4 * n + 1) * (l + 2) ^ n / m ^ (4 * n + 1) := by
  have h1 : (l / m) ^ (5 * n + 1) * (1 + 2 * m / l) ^ n =
      (l / m) ^ (4 * n + 1) * (l / m + 2) ^ n := by
    have e : l / m + 2 = (l / m) * (1 + 2 * m / l) := by
      field_simp
    rw [e, mul_pow, show 5 * n + 1 = (4 * n + 1) + n by ring, pow_add]
    ring
  have h2 : l / m ≤ l := div_le_self hl.le hm
  rw [h1, div_pow, div_mul_eq_mul_div]
  gcongr
theorem partial_sum_le {n : ℕ} (hn : 1 ≤ n) {l M : ℝ} (hl : 0 < l) (hM : 0 ≤ M)
    (c : (Fin (4 * n) → ℤ) → ℝ) (hc : ∀ k, 0 ≤ c k) (hc0 : c 0 ≤ M)
    (hdec : ∀ k, k ≠ 0 → c k ≤ (l / (supNormInt k : ℝ)) ^ (5 * n + 1) * M)
    (hcount : ∀ m : ℕ, 1 ≤ m → (modesWithSupNorm (4 * n) m).Finite ∧
      ((modesWithSupNorm (4 * n) m).ncard : ℝ) ≤ 8 * (n : ℝ) * (3 * (m : ℝ)) ^ (4 * n - 1))
    (T : ℕ) :
    ∑ k ∈ modesWithin T, c k * ∏ i, (1 + euclidNormInt (blockOf k i) / l) ≤
      (1 + 16 * (n : ℝ) * 3 ^ (4 * n - 1) * l ^ (4 * n + 1) * (l + 2) ^ n) * M := by
  set a : (Fin (4 * n) → ℤ) → ℝ :=
    fun k => c k * ∏ i, (1 + euclidNormInt (blockOf k i) / l) with ha
  have ha0 : ∀ k, 0 ≤ a k := fun k => mul_nonneg (hc k) (weight_nonneg hl k)
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = 8 * (n : ℝ) * 3 ^ (4 * n - 1) * l ^ (4 * n + 1) * (l + 2) ^ n * M :=
    ⟨_, rfl⟩
  have hB : 0 ≤ B := by rw [hBdef]; positivity
  have hshell : ∀ m ∈ Finset.range T,
      ∑ k ∈ (modesWithin T).filter (fun k => supNormInt k = m + 1), a k ≤
        B * (1 / ((m : ℝ) + 1) ^ 2) := by
    intro m _
    obtain ⟨S, hS⟩ : ∃ S : Finset (Fin (4 * n) → ℤ),
        S = (modesWithin T).filter (fun k => supNormInt k = m + 1) := ⟨_, rfl⟩
    rw [← hS]
    have hm1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith
    have hmpos : (0 : ℝ) < (m : ℝ) + 1 := by linarith
    have hterm : ∀ k ∈ S, a k ≤
        l ^ (4 * n + 1) * (l + 2) ^ n / ((m : ℝ) + 1) ^ (4 * n + 1) * M := by
      intro k hk
      rw [hS] at hk
      have hsk : supNormInt k = m + 1 := (Finset.mem_filter.mp hk).2
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [supNormInt_zero] at hsk
        omega
      have hw := weight_le (n := n) hl k
      have hd := hdec k hk0
      rw [hsk] at hw hd
      push_cast at hw hd
      calc a k ≤ ((l / ((m : ℝ) + 1)) ^ (5 * n + 1) * M) * (1 + 2 * ((m : ℝ) + 1) / l) ^ n :=
            mul_le_mul hd hw (weight_nonneg hl k) (by positivity)
        _ = ((l / ((m : ℝ) + 1)) ^ (5 * n + 1) * (1 + 2 * ((m : ℝ) + 1) / l) ^ n) * M := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (shell_factor_le n hl hm1) hM
    have hcard : (S.card : ℝ) ≤ 8 * (n : ℝ) * (3 * ((m : ℝ) + 1)) ^ (4 * n - 1) := by
      obtain ⟨hfin, hle⟩ := hcount (m + 1) (by omega)
      have hsub : (S : Set (Fin (4 * n) → ℤ)) ⊆ modesWithSupNorm (4 * n) (m + 1) := by
        intro k hk
        rw [hS] at hk
        exact (Finset.mem_filter.mp (Finset.mem_coe.mp hk)).2
      have h1 := Set.ncard_le_ncard hsub hfin
      rw [Set.ncard_coe_finset] at h1
      push_cast at hle
      exact le_trans (by exact_mod_cast h1) hle
    have hpow : ((m : ℝ) + 1) ^ (4 * n + 1) = ((m : ℝ) + 1) ^ (4 * n - 1) * ((m : ℝ) + 1) ^ 2 := by
      rw [← pow_add]
      congr 1
      omega
    calc ∑ k ∈ S, a k
        ≤ S.card • (l ^ (4 * n + 1) * (l + 2) ^ n / ((m : ℝ) + 1) ^ (4 * n + 1) * M) :=
          Finset.sum_le_card_nsmul _ _ _ hterm
      _ = (S.card : ℝ) * (l ^ (4 * n + 1) * (l + 2) ^ n / ((m : ℝ) + 1) ^ (4 * n + 1) * M) :=
          nsmul_eq_mul _ _
      _ ≤ (8 * (n : ℝ) * (3 * ((m : ℝ) + 1)) ^ (4 * n - 1)) *
            (l ^ (4 * n + 1) * (l + 2) ^ n / ((m : ℝ) + 1) ^ (4 * n + 1) * M) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = B * (1 / ((m : ℝ) + 1) ^ 2) := by
          rw [hBdef, hpow, mul_pow]
          have hx : ((m : ℝ) + 1) ^ (4 * n - 1) ≠ 0 := pow_ne_zero _ hmpos.ne'
          field_simp
  have hmaps : ∀ k ∈ (modesWithin T : Finset (Fin (4 * n) → ℤ)),
      supNormInt k ∈ Finset.range (T + 1) := by
    intro k hk
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le ((mem_modesWithin T k).mp hk))
  have hzero : ∑ k ∈ (modesWithin T).filter (fun k => supNormInt k = 0), a k ≤ M := by
    have hsub : (modesWithin T).filter (fun k : Fin (4 * n) → ℤ => supNormInt k = 0) ⊆ {0} := by
      intro k hk
      have hsk : supNormInt k = 0 := (Finset.mem_filter.mp hk).2
      refine Finset.mem_singleton.mpr (funext fun j => ?_)
      have := natAbs_le_supNormInt k j
      rw [hsk] at this
      exact Int.natAbs_eq_zero.mp (Nat.le_zero.mp this)
    have h0 : a 0 ≤ M := by
      have hw := weight_le (n := n) hl 0
      rw [supNormInt_zero] at hw
      have h1 : ∏ i, (1 + euclidNormInt (blockOf (0 : Fin (4 * n) → ℤ) i) / l) ≤ 1 := by
        simpa using hw
      calc a 0 ≤ c 0 * 1 := mul_le_mul_of_nonneg_left h1 (hc 0)
        _ ≤ M := by simpa using hc0
    calc ∑ k ∈ (modesWithin T).filter (fun k => supNormInt k = 0), a k
        ≤ ∑ k ∈ ({0} : Finset (Fin (4 * n) → ℤ)), a k :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => ha0 _
      _ = a 0 := Finset.sum_singleton _ _
      _ ≤ M := h0
  have hsum2 : ∑ m ∈ Finset.range T,
      ∑ k ∈ (modesWithin T).filter (fun k => supNormInt k = m + 1), a k ≤ B * 2 := by
    calc _ ≤ ∑ m ∈ Finset.range T, B * (1 / ((m : ℝ) + 1) ^ 2) := Finset.sum_le_sum hshell
      _ = B * ∑ m ∈ Finset.range T, 1 / ((m : ℝ) + 1) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ B * 2 := mul_le_mul_of_nonneg_left (sum_inv_sq_le_two T) hB
  rw [← Finset.sum_fiberwise_of_maps_to hmaps a, Finset.sum_range_succ']
  have e : (1 + 16 * (n : ℝ) * 3 ^ (4 * n - 1) * l ^ (4 * n + 1) * (l + 2) ^ n) * M = B * 2 + M := by
    rw [hBdef]
    ring
  rw [e]
  exact add_le_add hsum2 hzero
theorem bumpNumber_pos (n : ℕ) {ρ : ℝ} (hρ : 0 < ρ) : 0 < AmbientPoints.bumpNumber n ρ := by
  have hl : 0 < AmbientPoints.bumpScale ρ := by
    unfold AmbientPoints.bumpScale
    positivity
  unfold AmbientPoints.bumpNumber
  positivity
theorem weightedCoeffSumBound_of_fourierCoeffBounds (h : FourierCoeffBounds) :
    WeightedCoeffSumBound := by
  intro s n ρ hn hρ F hF
  have hP : 0 < 4 * ρ := by positivity
  obtain ⟨-, hFall, hcount, -⟩ := h s n (4 * ρ) hn hP
  obtain ⟨hsup, -, hdecay, hsum⟩ := hFall F hF
  have hl : 0 < AmbientPoints.bumpScale ρ := by
    unfold AmbientPoints.bumpScale
    positivity
  have hz := bumpNumber_pos n hρ
  have hsummable := summable_weighted hl (fun k => ‖fourierCoeff (4 * ρ) F k‖)
    (fun _ => norm_nonneg _) (hsum n (Nat.cast_nonneg n))
  refine ⟨hsummable, ?_⟩
  by_cases hN : AmbientPoints.cnNorm (5 * n + 1) F = ⊤
  · rw [hN, ENNReal.mul_top (by simpa using hz)]
    exact le_top
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = (AmbientPoints.cnNorm (5 * n + 1) F).toReal := ⟨_, rfl⟩
  have hNM : AmbientPoints.cnNorm (5 * n + 1) F = ENNReal.ofReal M := by
    rw [hMdef]
    exact (ENNReal.ofReal_toReal hN).symm
  have hM : 0 ≤ M := by
    rw [hMdef]
    exact ENNReal.toReal_nonneg
  have hc0 : ‖fourierCoeff (4 * ρ) F 0‖ ≤ M := by
    have h1 := hsup 0
    rw [AmbientPoints.tupleSupNorm_eq_cnNorm_zero] at h1
    have h2 : AmbientPoints.cnNorm 0 F ≤ AmbientPoints.cnNorm (5 * n + 1) F := by
      unfold AmbientPoints.cnNorm
      exact iSup_mono fun α => iSup_le fun hα =>
        le_iSup_of_le (hα.trans (Nat.zero_le _)) le_rfl
    have h3 := h1.trans (h2.trans hNM.le)
    exact (ENNReal.ofReal_le_ofReal_iff hM).mp h3
  have hdec : ∀ k : Fin (4 * n) → ℤ, k ≠ 0 → ‖fourierCoeff (4 * ρ) F k‖ ≤
      (AmbientPoints.bumpScale ρ / (supNormInt k : ℝ)) ^ (5 * n + 1) * M := by
    intro k hk
    have h1 := hdecay k hk (5 * n + 1)
    have e : 4 * ρ / (2 * Real.pi * (supNormInt k : ℝ)) =
        AmbientPoints.bumpScale ρ / (supNormInt k : ℝ) := by
      rw [← div_div]
      congr 1
      unfold AmbientPoints.bumpScale
      field_simp
      ring
    rw [e, hNM, ← ENNReal.ofReal_mul (by positivity)] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
  have hcount' : ∀ m : ℕ, 1 ≤ m → (modesWithSupNorm (4 * n) m).Finite ∧
      ((modesWithSupNorm (4 * n) m).ncard : ℝ) ≤ 8 * (n : ℝ) * (3 * (m : ℝ)) ^ (4 * n - 1) := by
    intro m hm
    obtain ⟨hfin, heq, hle1, hle2⟩ := hcount m hm
    refine ⟨hfin, ?_⟩
    have h1 : ((modesWithSupNorm (4 * n) m).ncard : ℤ) ≤
        2 * (4 * (n : ℤ)) * (3 * (m : ℤ)) ^ (4 * n - 1) := by
      rw [heq]
      exact hle1.trans hle2
    have h2 : (((modesWithSupNorm (4 * n) m).ncard : ℤ) : ℝ) ≤
        ((2 * (4 * (n : ℤ)) * (3 * (m : ℤ)) ^ (4 * n - 1) : ℤ) : ℝ) := Int.cast_le.mpr h1
    push_cast at h2
    linarith
  have htsum : ∑' k : Fin (4 * n) → ℤ, ‖fourierCoeff (4 * ρ) F k‖ *
      ∏ i, (1 + euclidNormInt (blockOf k i) / AmbientPoints.bumpScale ρ) ≤
        AmbientPoints.bumpNumber n ρ * M := by
    refine hsummable.tsum_le_of_sum_le fun S => ?_
    have hsub : S ⊆ modesWithin (S.sup supNormInt) := fun k hk =>
      (mem_modesWithin _ k).mpr (Finset.le_sup hk)
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ =>
      mul_nonneg (norm_nonneg _) (weight_nonneg hl k)).trans ?_
    exact partial_sum_le hn hl hM (fun k => ‖fourierCoeff (4 * ρ) F k‖) (fun _ => norm_nonneg _)
      hc0 hdec hcount' _
  rw [hNM, ← ENNReal.ofReal_mul hz.le]
  exact ENNReal.ofReal_le_ofReal htsum
end YangMills.Construction.Torus.FourierBox.WeightedCoeffSum
