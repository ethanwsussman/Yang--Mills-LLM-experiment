import YangMills.Construction.ColdChainAtEveryLevel.PinnedQuarticGaugeProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFractionalIntegration.CubicKernelTrace
theorem two_pow_clog_le_two_mul (d : ℕ) (hd : 1 ≤ d) : 2 ^ Nat.clog 2 d ≤ 2 * d := by
  rcases Nat.lt_or_ge 1 d with h | h
  · have h1 := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h
    have h2 : 0 < Nat.clog 2 d := Nat.clog_pos (by norm_num) (by omega)
    obtain ⟨k, hk⟩ : ∃ k, Nat.clog 2 d = k + 1 := ⟨Nat.clog 2 d - 1, by omega⟩
    rw [hk] at h1 ⊢
    simp only [Nat.pred_eq_sub_one, Nat.add_sub_cancel] at h1
    rw [pow_succ]
    omega
  · have : d = 1 := by omega
    subst this
    simp
theorem sum_pow_four_le_card_pow_three_mul {ι : Type} (s : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ s, f i) ^ 4 ≤ (s.card : ℝ) ^ 3 * ∑ i ∈ s, f i ^ 4 := by apply _root_.YangMills.Construction.PinnedGauge.sum_pow_four_le <;> assumption
theorem card_supNorm_ball_le (D : Finset Lattice4) (x : Lattice4) (r : ℕ) :
    ((D.filter fun y => supNorm (x - y) ≤ r).card : ℝ) ≤ (2 * (r : ℝ) + 1) ^ 4 := by
  have hs : (D.filter fun y => supNorm (x - y) ≤ r) ⊆
      Fintype.piFinset fun i => Finset.Icc (x i - r) (x i + r) := by
    intro y hy
    have hy2 := (Finset.mem_filter.1 hy).2
    rw [Fintype.mem_piFinset]
    intro i
    have h3 : ((x - y) i).natAbs ≤ supNorm (x - y) :=
      Finset.le_sup (f := fun i => ((x - y) i).natAbs) (Finset.mem_univ i)
    have h4 : ((x i - y i)).natAbs ≤ r := by
      have : (x - y) i = x i - y i := rfl
      rw [this] at h3
      omega
    rw [Finset.mem_Icc]
    omega
  have hc := Finset.card_le_card hs
  rw [Fintype.card_piFinset] at hc
  have e : ∀ i : Fin 4, (Finset.Icc (x i - r) (x i + r)).card = 2 * r + 1 := by
    intro i
    rw [Int.card_Icc]
    omega
  simp only [e, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hc
  have : ((D.filter fun y => supNorm (x - y) ≤ r).card : ℝ) ≤ ((2 * r + 1) ^ 4 : ℕ) := by
    exact_mod_cast hc
  simpa using this
theorem sum_pow_four_le_weighted {ι : Type} (s : Finset ι) (c S : ι → ℝ) (hc : ∀ i ∈ s, 0 < c i)
    (hS : ∀ i ∈ s, 0 ≤ S i) :
    (∑ i ∈ s, S i) ^ 4 ≤ (∑ i ∈ s, c i) ^ 3 * ∑ i ∈ s, S i ^ 4 / c i ^ 3 := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  have hC : 0 < ∑ i ∈ s, c i := Finset.sum_pos hc hne
  set Cs := ∑ i ∈ s, c i with hCs
  have h := Real.pow_arith_mean_le_arith_mean_pow s (fun i => c i / Cs) (fun i => S i * Cs / c i)
    (fun i hi => (div_pos (hc i hi) hC).le) (by rw [← Finset.sum_div]; exact div_self hC.ne')
    (fun i hi => div_nonneg (mul_nonneg (hS i hi) hC.le) (hc i hi).le) 4
  have e1 : ∑ i ∈ s, c i / Cs * (S i * Cs / c i) = ∑ i ∈ s, S i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have := (hc i hi).ne'
    field_simp
  have e2 : ∑ i ∈ s, c i / Cs * (S i * Cs / c i) ^ 4 = Cs ^ 3 * ∑ i ∈ s, S i ^ 4 / c i ^ 3 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have := (hc i hi).ne'
    field_simp
  rw [e1, e2] at h
  exact h
theorem cubicKernelTrace_holds : cubicKernelTraceStatement := by
  intro θ hθ
  set ρ : ℝ := (2 : ℝ) ^ (-θ) with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  refine ⟨2 ^ 36 * (2 : ℝ) ^ (4 * θ) / (1 - ρ) ^ 4, by
    have : 0 < 1 - ρ := by linarith
    positivity, ?_⟩
  intro D E μ f A R hR hA hμ hf hdiam hball
  have hRr : (0 : ℝ) < R := by exact_mod_cast hR
  set m := Nat.clog 2 R with hm
  have hmR : (2 : ℝ) ^ m ≤ 2 * R := by exact_mod_cast two_pow_clog_le_two_mul R hR
  have h1ρ : 0 < 1 - ρ := by linarith
  let sh : Lattice4 → Lattice4 → ℕ := fun x y => Nat.clog 2 (max 1 (supNorm (x - y)))
  let T : ℕ → Lattice4 → ℝ := fun k x => ∑ y ∈ D.filter (fun y => sh x y = k), cubicKernel (x - y) * f y
  let c : ℕ → ℝ := fun k => ρ ^ (m - k)
  have hc : ∀ k ∈ Finset.range (m + 1), 0 < c k := fun k _ => pow_pos hρ0 _
  have hT0 : ∀ x k, 0 ≤ T k x := fun x k => Finset.sum_nonneg fun y _ =>
    mul_nonneg (by unfold cubicKernel; positivity) (hf y)
  have hsplit : ∀ x ∈ E, ∑ y ∈ D, cubicKernel (x - y) * f y = ∑ k ∈ Finset.range (m + 1), T k x := by
    intro x hx
    refine (Finset.sum_fiberwise_of_maps_to (g := fun y => sh x y) ?_ _).symm
    intro y hy
    have h1 : max 1 (supNorm (x - y)) ≤ R := max_le hR (hdiam x hx y hy)
    have h2 : sh x y ≤ m := Nat.clog_mono_right 2 h1
    exact Finset.mem_range.2 (by omega)
  have hCs : ∑ k ∈ Finset.range (m + 1), c k ≤ 1 / (1 - ρ) := by
    have e : ∑ k ∈ Finset.range (m + 1), c k = ∑ k ∈ Finset.range (m + 1), ρ ^ k := by
      have := Finset.sum_range_reflect (fun k => ρ ^ k) (m + 1)
      rw [← this]
      refine Finset.sum_congr rfl fun k hk => ?_
      have : k ≤ m := by have := Finset.mem_range.1 hk; omega
      show ρ ^ (m - k) = ρ ^ (m + 1 - 1 - k)
      simp
    rw [e, geom_sum_eq hρ1.ne, one_div, ← neg_sub, ← neg_sub (1 : ℝ) ρ, neg_div_neg_eq]
    rw [div_eq_mul_inv]
    have : 0 ≤ (1 - ρ)⁻¹ := by positivity
    have h3 : 1 - ρ ^ (m + 1) ≤ 1 := by
      have := pow_pos hρ0 (m + 1)
      linarith
    nlinarith
  have hCs0 : 0 ≤ ∑ k ∈ Finset.range (m + 1), c k := Finset.sum_nonneg fun k hk => (hc k hk).le
  set Fs := ∑ y ∈ D, f y ^ 4 with hFs
  have hshell : ∀ x k, T k x ^ 4 ≤ 2 ^ 36 * ∑ y ∈ D.filter (fun y => supNorm (x - y) ≤ 2 ^ k), f y ^ 4 := by
    intro x k
    have hk0 : (0 : ℝ) < 2 ^ k := by positivity
    set B := D.filter (fun y => supNorm (x - y) ≤ 2 ^ k) with hB
    have h1 : T k x ≤ 8 / (2 ^ k) ^ 3 * ∑ y ∈ B, f y := by
      rw [Finset.mul_sum]
      calc T k x ≤ ∑ y ∈ D.filter (fun y => sh x y = k), 8 / (2 ^ k) ^ 3 * f y := by
            refine Finset.sum_le_sum fun y hy => ?_
            have hy2 : sh x y = k := (Finset.mem_filter.1 hy).2
            refine mul_le_mul_of_nonneg_right ?_ (hf y)
            have hd : (2 : ℝ) ^ k ≤ 2 * (max 1 (supNorm (x - y)) : ℕ) := by
              have := two_pow_clog_le_two_mul (max 1 (supNorm (x - y))) (le_max_left _ _)
              rw [show Nat.clog 2 (max 1 (supNorm (x - y))) = k from hy2] at this
              exact_mod_cast this
            unfold cubicKernel
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            have h3 : ((2 : ℝ) ^ k) ^ 3 ≤ (2 * ((max 1 (supNorm (x - y)) : ℕ) : ℝ)) ^ 3 :=
              pow_le_pow_left₀ hk0.le hd 3
            nlinarith
        _ ≤ ∑ y ∈ B, 8 / (2 ^ k) ^ 3 * f y := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun y _ _ =>
              mul_nonneg (by positivity) (hf y)
            intro y hy
            obtain ⟨hy1, hy2⟩ := Finset.mem_filter.1 hy
            refine Finset.mem_filter.2 ⟨hy1, ?_⟩
            have h5 : max 1 (supNorm (x - y)) ≤ 2 ^ Nat.clog 2 (max 1 (supNorm (x - y))) :=
              Nat.le_pow_clog (by norm_num) _
            rw [show Nat.clog 2 (max 1 (supNorm (x - y))) = k from hy2] at h5
            exact le_trans (le_max_right _ _) h5
    have h2 := sum_pow_four_le_card_pow_three_mul B f
    have h3 := card_supNorm_ball_le D x (2 ^ k)
    have h4 : (2 * (((2 ^ k : ℕ)) : ℝ) + 1) ^ 4 ≤ (4 * (2 : ℝ) ^ k) ^ 4 := by
      push_cast
      have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      exact pow_le_pow_left₀ (by positivity) (by linarith) 4
    have h5 : (B.card : ℝ) ≤ (4 * (2 : ℝ) ^ k) ^ 4 := le_trans h3 h4
    have hs0 : 0 ≤ ∑ y ∈ B, f y ^ 4 := Finset.sum_nonneg fun y _ => by positivity
    calc T k x ^ 4 ≤ (8 / (2 ^ k) ^ 3 * ∑ y ∈ B, f y) ^ 4 := pow_le_pow_left₀ (hT0 x k) h1 4
      _ = (8 / (2 ^ k) ^ 3) ^ 4 * (∑ y ∈ B, f y) ^ 4 := by ring
      _ ≤ (8 / (2 ^ k) ^ 3) ^ 4 * (((4 * (2 : ℝ) ^ k) ^ 4) ^ 3 * ∑ y ∈ B, f y ^ 4) := by
          refine mul_le_mul_of_nonneg_left (le_trans h2 ?_) (by positivity)
          refine mul_le_mul_of_nonneg_right ?_ hs0
          exact pow_le_pow_left₀ (Nat.cast_nonneg _) h5 3
      _ = 2 ^ 36 * ∑ y ∈ B, f y ^ 4 := by
          field_simp
          ring
  have hmeas : ∀ k ∈ Finset.range (m + 1), ∑ x ∈ E, μ x * T k x ^ 4 ≤
      2 ^ 36 * (A * ((2 : ℝ) ^ (4 * θ) * (ρ ^ (m - k)) ^ 4) * Fs) := by
    intro k hk
    have hkm : k ≤ m := by have := Finset.mem_range.1 hk; omega
    have e1 : ∑ x ∈ E, μ x * T k x ^ 4 ≤
        2 ^ 36 * ∑ y ∈ D, f y ^ 4 * ∑ x ∈ E.filter (fun x => supNorm (x - y) ≤ 2 ^ k), μ x := by
      calc ∑ x ∈ E, μ x * T k x ^ 4
          ≤ ∑ x ∈ E, μ x * (2 ^ 36 * ∑ y ∈ D.filter (fun y => supNorm (x - y) ≤ 2 ^ k), f y ^ 4) :=
            Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hshell x k) (hμ x)
        _ = 2 ^ 36 * ∑ y ∈ D, f y ^ 4 * ∑ x ∈ E.filter (fun x => supNorm (x - y) ≤ 2 ^ k), μ x := by
            rw [Finset.mul_sum]
            simp_rw [Finset.sum_filter, Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun x _ => ?_
            refine Finset.sum_congr rfl fun y _ => ?_
            split_ifs <;> ring
    refine le_trans e1 ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [show A * ((2 : ℝ) ^ (4 * θ) * (ρ ^ (m - k)) ^ 4) * Fs =
      ∑ y ∈ D, f y ^ 4 * (A * ((2 : ℝ) ^ (4 * θ) * (ρ ^ (m - k)) ^ 4)) by
        rw [hFs, Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        ring]
    refine Finset.sum_le_sum fun y hy => mul_le_mul_of_nonneg_left ?_ (by positivity)
    set r := min (2 ^ k) R with hr
    have hr1 : 1 ≤ r := le_min Nat.one_le_two_pow hR
    have hrR : r ≤ R := min_le_right _ _
    have hsub : E.filter (fun x => supNorm (x - y) ≤ 2 ^ k) ⊆ E.filter (fun b => supNorm (b - y) ≤ r) := by
      intro x hx
      obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
      exact Finset.mem_filter.2 ⟨hx1, le_min hx2 (hdiam x hx1 y hy)⟩
    have h6 := hball y r hr1 hrR
    have h7 : ∑ x ∈ E.filter (fun x => supNorm (x - y) ≤ 2 ^ k), μ x ≤
        ∑ b ∈ E.filter (fun b => supNorm (b - y) ≤ r), μ b :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ => hμ x
    refine le_trans h7 (le_trans h6 ?_)
    refine mul_le_mul_of_nonneg_left ?_ hA
    have h8 : (r : ℝ) / R ≤ 2 * (1 / 2) ^ (m - k) := by
      have hr2 : (r : ℝ) ≤ 2 ^ k := by exact_mod_cast min_le_left _ _
      rw [div_le_iff₀ hRr]
      have e3 : (2 : ℝ) ^ m = 2 ^ k * 2 ^ (m - k) := by
        rw [← pow_add]
        congr 1
        omega
      have h9 : (2 : ℝ) ^ k * 2 ^ (m - k) ≤ 2 * R := e3 ▸ hmR
      have e4 : (1 / 2 : ℝ) ^ (m - k) = 1 / 2 ^ (m - k) := by rw [one_div_pow]
      rw [e4]
      calc (r : ℝ) ≤ 2 ^ k := hr2
        _ = (2 ^ k * 2 ^ (m - k)) / 2 ^ (m - k) := by field_simp
        _ ≤ (2 * R) / 2 ^ (m - k) := by gcongr
        _ = 2 * (1 / 2 ^ (m - k)) * R := by ring
    have hr0 : (0 : ℝ) ≤ (r : ℝ) / R := by positivity
    calc ((r : ℝ) / R) ^ (4 * θ) ≤ (2 * (1 / 2) ^ (m - k)) ^ (4 * θ) :=
          Real.rpow_le_rpow hr0 h8 (by positivity)
      _ = (2 : ℝ) ^ (4 * θ) * (ρ ^ (m - k)) ^ 4 := by
          rw [Real.mul_rpow (by norm_num) (by positivity)]
          congr 1
          have a1 : ((1 / 2 : ℝ) ^ (m - k)) = (2 : ℝ) ^ (-((m - k : ℕ) : ℝ)) := by
            rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div_pow, one_div]
          have a2 : (((2 : ℝ) ^ (-θ)) ^ (m - k)) ^ 4 = (2 : ℝ) ^ (-θ * ((m - k : ℕ) : ℝ) * 4) := by
            rw [Real.rpow_mul (by norm_num), Real.rpow_mul (by positivity), Real.rpow_natCast, ]
            norm_cast
          rw [hρ, a1, ← Real.rpow_mul (by norm_num), a2]
          congr 1
          ring
  have hall : ∑ x ∈ E, μ x * (∑ y ∈ D, cubicKernel (x - y) * f y) ^ 4 ≤
      (1 / (1 - ρ)) ^ 3 * ∑ k ∈ Finset.range (m + 1), (∑ x ∈ E, μ x * T k x ^ 4) / c k ^ 3 := by
    calc ∑ x ∈ E, μ x * (∑ y ∈ D, cubicKernel (x - y) * f y) ^ 4
        ≤ ∑ x ∈ E, μ x * ((1 / (1 - ρ)) ^ 3 * ∑ k ∈ Finset.range (m + 1), T k x ^ 4 / c k ^ 3) := by
          refine Finset.sum_le_sum fun x hx => mul_le_mul_of_nonneg_left ?_ (hμ x)
          rw [hsplit x hx]
          refine le_trans (sum_pow_four_le_weighted _ c (fun k => T k x) hc fun k _ => hT0 x k) ?_
          refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hCs0 hCs 3) ?_
          exact Finset.sum_nonneg fun k hk => div_nonneg (by positivity) (pow_pos (hc k hk) 3).le
      _ = _ := by
          simp_rw [mul_left_comm (μ _) ((1 / (1 - ρ)) ^ 3)]
          rw [← Finset.mul_sum]
          congr 1
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl fun x _ => ?_
          ring
  refine le_trans hall ?_
  have hsum : ∑ k ∈ Finset.range (m + 1), (∑ x ∈ E, μ x * T k x ^ 4) / c k ^ 3 ≤
      ∑ k ∈ Finset.range (m + 1), 2 ^ 36 * (A * (2 : ℝ) ^ (4 * θ) * Fs) * c k := by
    refine Finset.sum_le_sum fun k hk => ?_
    have hck := hc k hk
    rw [div_le_iff₀ (pow_pos hck 3)]
    refine le_trans (hmeas k hk) (le_of_eq ?_)
    show _ = 2 ^ 36 * (A * (2 : ℝ) ^ (4 * θ) * Fs) * ρ ^ (m - k) * (ρ ^ (m - k)) ^ 3
    ring
  calc (1 / (1 - ρ)) ^ 3 * ∑ k ∈ Finset.range (m + 1), (∑ x ∈ E, μ x * T k x ^ 4) / c k ^ 3
      ≤ (1 / (1 - ρ)) ^ 3 * ∑ k ∈ Finset.range (m + 1), 2 ^ 36 * (A * (2 : ℝ) ^ (4 * θ) * Fs) * c k :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (1 / (1 - ρ)) ^ 3 * (2 ^ 36 * (A * (2 : ℝ) ^ (4 * θ) * Fs) * ∑ k ∈ Finset.range (m + 1), c k) := by
        rw [← Finset.mul_sum]
    _ ≤ (1 / (1 - ρ)) ^ 3 * (2 ^ 36 * (A * (2 : ℝ) ^ (4 * θ) * Fs) * (1 / (1 - ρ))) := by
        gcongr
    _ = 2 ^ 36 * (2 : ℝ) ^ (4 * θ) / (1 - ρ) ^ 4 * A * Fs := by
        field_simp
end YangMills.Construction.LatticeFractionalIntegration.CubicKernelTrace
end
