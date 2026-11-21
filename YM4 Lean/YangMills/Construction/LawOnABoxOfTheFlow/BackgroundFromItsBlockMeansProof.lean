import YangMills.Construction.SummableBoundsOfTheFlow.LeastActionOfAFrameOnItsTorus
import YangMills.Construction.ClusterExpansionOfAStep.OffsetsOfABlock
import YangMills.Construction.LawOnABoxOfTheFlow.BackgroundFromItsBlockMeans
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.BoxGaussian
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
private theorem norm_step_sub_first_le (a : ℕ → E) (ε : ℝ) (T : ℕ)
    (h : ∀ u, u + 2 ≤ T → ‖a (u + 2) - (2 : ℝ) • a (u + 1) + a u‖ ≤ ε) :
    ∀ t, t + 1 ≤ T → ‖a (t + 1) - a t - (a 1 - a 0)‖ ≤ (t : ℝ) * ε := by
  intro t
  induction t with
  | zero => intro _; simp
  | succ t ih =>
    intro ht
    have h1 := ih (by omega)
    have h2 := h t (by omega)
    have e : a (t + 1 + 1) - a (t + 1) - (a 1 - a 0) =
        (a (t + 2) - (2 : ℝ) • a (t + 1) + a t) + (a (t + 1) - a t - (a 1 - a 0)) := by
      module
    rw [e]
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ ε + (t : ℝ) * ε := add_le_add h2 h1
      _ = ((t + 1 : ℕ) : ℝ) * ε := by push_cast; ring
private theorem norm_sub_linear_le (a : ℕ → E) (ε : ℝ) (hε : 0 ≤ ε) (T : ℕ)
    (h : ∀ u, u + 2 ≤ T → ‖a (u + 2) - (2 : ℝ) • a (u + 1) + a u‖ ≤ ε) :
    ∀ t, t ≤ T → ‖a t - a 0 - (t : ℝ) • (a 1 - a 0)‖ ≤ (t : ℝ) ^ 2 * ε := by
  intro t
  induction t with
  | zero => intro _; simp
  | succ t ih =>
    intro ht
    have h1 := ih (by omega)
    have h2 := norm_step_sub_first_le a ε T h t (by omega)
    have e : a (t + 1) - a 0 - ((t + 1 : ℕ) : ℝ) • (a 1 - a 0) =
        (a t - a 0 - (t : ℝ) • (a 1 - a 0)) + (a (t + 1) - a t - (a 1 - a 0)) := by
      push_cast
      module
    rw [e]
    have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ (t : ℝ) ^ 2 * ε + (t : ℝ) * ε := add_le_add h1 h2
      _ ≤ ((t + 1 : ℕ) : ℝ) ^ 2 * ε := by
        push_cast
        nlinarith [mul_nonneg ht0 hε]
private theorem norm_le_of_ends (a : ℕ → E) (ε B : ℝ) (hε : 0 ≤ ε) (lam r : ℕ) (hlam : 0 < lam) (hr : r ≤ lam)
    (h : ∀ u, u + 2 ≤ lam → ‖a (u + 2) - (2 : ℝ) • a (u + 1) + a u‖ ≤ ε)
    (h0 : ‖a 0‖ ≤ B) (h1 : ‖a lam‖ ≤ B) :
    ‖a r‖ ≤ B + 2 * (lam : ℝ) ^ 2 * ε := by
  have tl := norm_sub_linear_le a ε hε lam h lam le_rfl
  have tr := norm_sub_linear_le a ε hε lam h r hr
  have hl : (0 : ℝ) < lam := by exact_mod_cast hlam
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = (r : ℝ) / lam := ⟨_, rfl⟩
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  have hθ1 : θ ≤ 1 := by
    rw [hθ, div_le_one hl]
    exact_mod_cast hr
  have hrl : (r : ℝ) = θ * lam := by rw [hθ]; field_simp
  rw [hrl] at tr
  have e : a r = (1 - θ) • a 0 + θ • a lam - θ • (a lam - a 0 - (lam : ℝ) • (a 1 - a 0)) +
      (a r - a 0 - (θ * lam) • (a 1 - a 0)) := by
    module
  rw [e]
  have n1 : ‖(1 - θ) • a 0‖ ≤ (1 - θ) * B := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    exact mul_le_mul_of_nonneg_left h0 (by linarith)
  have n2 : ‖θ • a lam‖ ≤ θ * B := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ0]
    exact mul_le_mul_of_nonneg_left h1 hθ0
  have n3 : ‖θ • (a lam - a 0 - (lam : ℝ) • (a 1 - a 0))‖ ≤ (lam : ℝ) ^ 2 * ε := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ0]
    calc _ ≤ 1 * ‖a lam - a 0 - (lam : ℝ) • (a 1 - a 0)‖ :=
          mul_le_mul_of_nonneg_right hθ1 (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact tl
  have n4 : (θ * (lam : ℝ)) ^ 2 * ε ≤ (lam : ℝ) ^ 2 * ε := by
    apply mul_le_mul_of_nonneg_right _ hε
    rw [mul_pow]
    have : θ ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg (lam : ℝ)]
  calc _ ≤ ‖(1 - θ) • a 0 + θ • a lam - θ • (a lam - a 0 - (lam : ℝ) • (a 1 - a 0))‖ +
        ‖a r - a 0 - (θ * lam) • (a 1 - a 0)‖ := norm_add_le _ _
    _ ≤ (‖(1 - θ) • a 0 + θ • a lam‖ + ‖θ • (a lam - a 0 - (lam : ℝ) • (a 1 - a 0))‖) +
        ‖a r - a 0 - (θ * lam) • (a 1 - a 0)‖ := by
      gcongr
      exact norm_sub_le _ _
    _ ≤ (((1 - θ) * B + θ * B) + (lam : ℝ) ^ 2 * ε) + (lam : ℝ) ^ 2 * ε := by
      have := norm_add_le ((1 - θ) • a 0) (θ • a lam)
      linarith [tr]
    _ = B + 2 * (lam : ℝ) ^ 2 * ε := by ring
private theorem sum_range_odd_cast (h : ℕ) : ∑ t ∈ Finset.range (2 * h + 1), (t : ℝ) = (2 * (h : ℝ) + 1) * h := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [show 2 * (h + 1) + 1 = 2 * h + 1 + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    push_cast
    ring
private theorem norm_average_sub_mid_le (a : ℕ → E) (ε : ℝ) (hε : 0 ≤ ε) (h : ℕ)
    (hd : ∀ u, u + 2 ≤ 2 * h + 1 → ‖a (u + 2) - (2 : ℝ) • a (u + 1) + a u‖ ≤ ε) :
    ‖(1 / ((2 * h + 1 : ℕ) : ℝ)) • ∑ t ∈ Finset.range (2 * h + 1), a t - a h‖ ≤
      2 * ((2 * h + 1 : ℕ) : ℝ) ^ 2 * ε := by
  have tl := norm_sub_linear_le a ε hε (2 * h + 1) hd
  obtain ⟨l, hl⟩ : ∃ l : ℝ, l = ((2 * h + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  have hl0 : 0 < l := by rw [hl]; positivity
  have hsum : ∑ t ∈ Finset.range (2 * h + 1), (a t - a 0 - (t : ℝ) • (a 1 - a 0)) =
      ∑ t ∈ Finset.range (2 * h + 1), a t - l • a 0 - (l * h) • (a 1 - a 0) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      ← Finset.sum_smul, sum_range_odd_cast, hl, Nat.cast_smul_eq_nsmul]
    push_cast
    rfl
  have e : (1 / l) • ∑ t ∈ Finset.range (2 * h + 1), a t - a h =
      (1 / l) • ∑ t ∈ Finset.range (2 * h + 1), (a t - a 0 - (t : ℝ) • (a 1 - a 0)) -
        (a h - a 0 - (h : ℝ) • (a 1 - a 0)) := by
    rw [hsum, smul_sub, smul_sub, smul_smul, smul_smul]
    have h1 : 1 / l * l = 1 := by field_simp
    have h2 : 1 / l * (l * h) = h := by field_simp
    rw [h1, h2]
    module
  rw [← hl, e]
  have b1 : ‖∑ t ∈ Finset.range (2 * h + 1), (a t - a 0 - (t : ℝ) • (a 1 - a 0))‖ ≤ l * (l ^ 2 * ε) := by
    calc _ ≤ ∑ t ∈ Finset.range (2 * h + 1), ‖a t - a 0 - (t : ℝ) • (a 1 - a 0)‖ := norm_sum_le _ _
      _ ≤ ∑ t ∈ Finset.range (2 * h + 1), l ^ 2 * ε := by
        apply Finset.sum_le_sum
        intro t ht
        have ht' := Finset.mem_range.mp ht
        refine (tl t ht'.le).trans (mul_le_mul_of_nonneg_right ?_ hε)
        have : (t : ℝ) ≤ l := by rw [hl]; exact_mod_cast ht'.le
        have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
        nlinarith
      _ = l * (l ^ 2 * ε) := by
        rw [Finset.sum_const, Finset.card_range, hl, nsmul_eq_mul]
  have b2 : ‖a h - a 0 - (h : ℝ) • (a 1 - a 0)‖ ≤ l ^ 2 * ε := by
    refine (tl h (by omega)).trans (mul_le_mul_of_nonneg_right ?_ hε)
    have : (h : ℝ) ≤ l := by rw [hl]; push_cast; linarith [(Nat.cast_nonneg h : (0 : ℝ) ≤ h)]
    have ht0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
    nlinarith
  have b3 : ‖(1 / l) • ∑ t ∈ Finset.range (2 * h + 1), (a t - a 0 - (t : ℝ) • (a 1 - a 0))‖ ≤ l ^ 2 * ε := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc _ ≤ 1 / l * (l * (l ^ 2 * ε)) := mul_le_mul_of_nonneg_left b1 (by positivity)
      _ = l ^ 2 * ε := by field_simp
  calc _ ≤ _ := norm_sub_le _ _
    _ ≤ l ^ 2 * ε + l ^ 2 * ε := add_le_add b3 b2
    _ = 2 * l ^ 2 * ε := by ring
private abbrev basisVec (m : Fin 4) : Fin 4 → ℤ := Pi.single m 1
private theorem abs_add_smul_basisVec_sub_le (z c : Fin 4 → ℤ) (m k : Fin 4) (t : ℤ) (ht : 0 ≤ t) :
    |(z + t • basisVec m) k - c k| ≤ |z k - c k| + t := by
  by_cases h : k = m
  · subst h
    have : (z + t • basisVec k) k - c k = (z k - c k) + t := by
      simp [basisVec]
      ring
    rw [this]
    calc _ ≤ |z k - c k| + |t| := abs_add_le _ _
      _ = _ := by rw [abs_of_nonneg ht]
  · have : (z + t • basisVec m) k = z k := by simp [basisVec, h]
    rw [this]
    linarith
private def SecondDiffBound (G : (Fin 4 → ℤ) → E) (c : Fin 4 → ℤ) (ρ : ℤ) (ε : ℝ) : Prop :=
  ∀ (m : Fin 4) (z : Fin 4 → ℤ), (∀ k, |z k - c k| ≤ ρ) →
    ‖G (z + basisVec m + basisVec m) - (2 : ℝ) • G (z + basisVec m) + G z‖ ≤ ε
private theorem secondDiff_along_line {G : (Fin 4 → ℤ) → E} {c : Fin 4 → ℤ} {ρ : ℤ} {ε : ℝ}
    (hG : SecondDiffBound G c ρ ε)
    (z : Fin 4 → ℤ) (m : Fin 4) (T : ℕ) (hz : ∀ k, |z k - c k| + T ≤ ρ) (u : ℕ) (hu : u + 2 ≤ T) :
    ‖G (z + ((u + 2 : ℕ) : ℤ) • basisVec m) - (2 : ℝ) • G (z + ((u + 1 : ℕ) : ℤ) • basisVec m) +
      G (z + (u : ℤ) • basisVec m)‖ ≤ ε := by
  have h := hG m (z + (u : ℤ) • basisVec m) (fun k => by
    have := abs_add_smul_basisVec_sub_le z c m k u (by positivity)
    have := hz k
    have : (u : ℤ) ≤ T := by omega
    linarith)
  have e1 : z + (u : ℤ) • basisVec m + basisVec m + basisVec m = z + ((u + 2 : ℕ) : ℤ) • basisVec m := by
    push_cast
    module
  have e2 : z + (u : ℤ) • basisVec m + basisVec m = z + ((u + 1 : ℕ) : ℤ) • basisVec m := by
    push_cast
    module
  rwa [e1, e2] at h
private def iteratedMean (lam : ℕ) (G : (Fin 4 → ℤ) → E) : List (Fin 4) → (Fin 4 → ℤ) → E
  | [], z => G z
  | d :: D, z => (1 / (lam : ℝ)) • ∑ t ∈ Finset.range lam, iteratedMean lam G D (z + (t : ℤ) • basisVec d)
private def iteratedShift (h : ℤ) : List (Fin 4) → (Fin 4 → ℤ)
  | [] => 0
  | d :: D => h • basisVec d + iteratedShift h D
private theorem abs_add_iteratedShift_sub_le (h : ℤ) (hh : 0 ≤ h) (D : List (Fin 4)) (z c : Fin 4 → ℤ)
    (k : Fin 4) :
    |(z + iteratedShift h D) k - c k| ≤ |z k - c k| + D.length * h := by
  induction D generalizing z with
  | nil => simp [iteratedShift]
  | cons d D ih =>
    have e : z + iteratedShift h (d :: D) = (z + h • basisVec d) + iteratedShift h D := by
      simp only [iteratedShift]
      abel
    rw [e]
    have h1 := ih (z + h • basisVec d)
    have h2 := abs_add_smul_basisVec_sub_le z c d k h hh
    simp only [List.length_cons]
    push_cast
    linarith
private theorem norm_iteratedMean_sub_le {G : (Fin 4 → ℤ) → E} {c : Fin 4 → ℤ} {ρ : ℤ} {ε : ℝ} (hε : 0 ≤ ε)
    (hG : SecondDiffBound G c ρ ε) (h : ℕ) :
    ∀ (D : List (Fin 4)) (z : Fin 4 → ℤ), (∀ k, |z k - c k| + (D.length : ℤ) * (2 * h + 1) ≤ ρ) →
      ‖iteratedMean (2 * h + 1) G D z - G (z + iteratedShift h D)‖ ≤
        (D.length : ℝ) * (2 * ((2 * h + 1 : ℕ) : ℝ) ^ 2 * ε) := by
  intro D
  induction D with
  | nil => intro z _; simp [iteratedMean, iteratedShift]
  | cons d D ih =>
    intro z hz
    obtain ⟨l, hl⟩ : ∃ l : ℝ, l = ((2 * h + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
    have hl0 : 0 < l := by rw [hl]; positivity
    simp only [List.length_cons] at hz
    push_cast at hz
    have hh0 : (0 : ℤ) ≤ h := by positivity
    have b1 : ∀ t ∈ Finset.range (2 * h + 1),
        ‖iteratedMean (2 * h + 1) G D (z + (t : ℤ) • basisVec d) -
            G (z + (t : ℤ) • basisVec d + iteratedShift h D)‖ ≤
          (D.length : ℝ) * (2 * l ^ 2 * ε) := by
      intro t ht
      have ht' := Finset.mem_range.mp ht
      rw [hl]
      refine ih _ fun k => ?_
      have h1 := abs_add_smul_basisVec_sub_le z c d k t (by positivity)
      have h2 := hz k
      nlinarith
    have b2 := norm_average_sub_mid_le (fun u : ℕ => G ((z + iteratedShift h D) + (u : ℤ) • basisVec d)) ε hε h
      (fun u hu => by
        refine secondDiff_along_line hG (z + iteratedShift h D) d (2 * h + 1) (fun k => ?_) u hu
        have h1 := abs_add_iteratedShift_sub_le h hh0 D z c k
        have h2 := hz k
        push_cast
        nlinarith)
    rw [← hl] at b2
    have e : iteratedMean (2 * h + 1) G (d :: D) z - G (z + iteratedShift h (d :: D)) =
        (1 / l) • ∑ t ∈ Finset.range (2 * h + 1),
            (iteratedMean (2 * h + 1) G D (z + (t : ℤ) • basisVec d) -
              G (z + (t : ℤ) • basisVec d + iteratedShift h D)) +
          ((1 / l) • ∑ t ∈ Finset.range (2 * h + 1), G ((z + iteratedShift h D) + (t : ℤ) • basisVec d) -
            G ((z + iteratedShift h D) + (h : ℤ) • basisVec d)) := by
      have e1 : z + iteratedShift h (d :: D) = (z + iteratedShift h D) + (h : ℤ) • basisVec d := by
        simp only [iteratedShift]
        abel
      have e2 : ∀ t : ℕ, z + (t : ℤ) • basisVec d + iteratedShift h D =
          (z + iteratedShift h D) + (t : ℤ) • basisVec d := by
        intro t
        abel
      simp only [iteratedMean, e1, e2, Finset.sum_sub_distrib, smul_sub, hl]
      abel
    rw [e]
    have b3 : ‖(1 / l) • ∑ t ∈ Finset.range (2 * h + 1),
        (iteratedMean (2 * h + 1) G D (z + (t : ℤ) • basisVec d) -
          G (z + (t : ℤ) • basisVec d + iteratedShift h D))‖ ≤
          (D.length : ℝ) * (2 * l ^ 2 * ε) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc _ ≤ 1 / l * ∑ t ∈ Finset.range (2 * h + 1), (D.length : ℝ) * (2 * l ^ 2 * ε) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact (norm_sum_le _ _).trans (Finset.sum_le_sum b1)
        _ = _ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← hl]
          field_simp
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ (D.length : ℝ) * (2 * l ^ 2 * ε) + 2 * l ^ 2 * ε := add_le_add b3 b2
      _ = _ := by
        rw [← hl]
        simp only [List.length_cons]
        push_cast
        ring
private theorem norm_le_of_lattice_bound {G : (Fin 4 → ℤ) → E} {c g : Fin 4 → ℤ} {ρ r : ℤ} {ε B : ℝ}
    (hε : 0 ≤ ε)
    (hG : SecondDiffBound G c ρ ε) (lam : ℕ) (hlam : 0 < lam) (hρ : r + 2 * lam ≤ ρ)
    (hgrid : ∀ z : Fin 4 → ℤ, (∀ k, (lam : ℤ) ∣ z k - g k) → (∀ k, |z k - c k| ≤ r + lam) → ‖G z‖ ≤ B)
    (S : Finset (Fin 4)) :
    ∀ z : Fin 4 → ℤ, (∀ k ∈ S, |z k - c k| ≤ r) →
      (∀ k, k ∉ S → (lam : ℤ) ∣ z k - g k ∧ |z k - c k| ≤ r + lam) →
      ‖G z‖ ≤ B + (S.card : ℝ) * (2 * (lam : ℝ) ^ 2 * ε) := by
  have hl : (0 : ℤ) < lam := by exact_mod_cast hlam
  induction S using Finset.induction_on with
  | empty =>
    intro z _ hz
    simpa using hgrid z (fun k => (hz k (by simp)).1) (fun k => (hz k (by simp)).2)
  | insert m S hm ih =>
    intro z hin hout
    have hzm : |z m - c m| ≤ r := hin m (Finset.mem_insert_self m S)
    obtain ⟨w, hw⟩ : ∃ w : ℤ, w = (z m - g m) % lam := ⟨_, rfl⟩
    have hw0 : 0 ≤ w := by rw [hw]; exact Int.emod_nonneg _ hl.ne'
    have hw1 : w < lam := by rw [hw]; exact Int.emod_lt_of_pos _ hl
    have hdvd : (lam : ℤ) ∣ z m - g m - w := by rw [hw]; exact Int.dvd_self_sub_emod
    obtain ⟨r', hr'⟩ : ∃ r' : ℕ, (r' : ℤ) = w := ⟨w.toNat, Int.toNat_of_nonneg hw0⟩
    have hr'l : r' ≤ lam := by omega
    obtain ⟨zl, hzl⟩ : ∃ zl : Fin 4 → ℤ, zl = z - w • basisVec m := ⟨_, rfl⟩
    have czm : zl m = z m - w := by simp [hzl, basisVec]
    have czk : ∀ k, k ≠ m → zl k = z k := by
      intro k hk
      simp [hzl, basisVec, hk]
    have hend : ∀ q : ℕ, (q = 0 ∨ q = lam) → ‖G (zl + (q : ℤ) • basisVec m)‖ ≤
        B + (S.card : ℝ) * (2 * (lam : ℝ) ^ 2 * ε) := by
      intro q hq
      have cm : (zl + (q : ℤ) • basisVec m) m = z m - w + q := by simp [czm, basisVec]
      have ck : ∀ k, k ≠ m → (zl + (q : ℤ) • basisVec m) k = z k := by
        intro k hk
        simp [czk k hk, basisVec, hk]
      have habs := abs_le.mp hzm
      refine ih _ (fun k hk => ?_) (fun k hk => ?_)
      · have hkm : k ≠ m := fun h => hm (h ▸ hk)
        rw [ck k hkm]
        exact hin k (Finset.mem_insert_of_mem hk)
      · by_cases hkm : k = m
        · subst hkm
          rw [cm]
          refine ⟨?_, ?_⟩
          · rcases hq with hq | hq
            · have : z k - w + (q : ℤ) - g k = z k - g k - w := by rw [hq]; push_cast; ring
              rw [this]
              exact hdvd
            · have : z k - w + (q : ℤ) - g k = (z k - g k - w) + lam := by rw [hq]; ring
              rw [this]
              exact dvd_add hdvd dvd_rfl
          · rw [abs_le]
            rcases hq with hq | hq
            · rw [hq]; push_cast; constructor <;> linarith
            · rw [hq]; constructor <;> linarith
        · rw [ck k hkm]
          exact hout k (fun h => by
            rcases Finset.mem_insert.mp h with h | h
            · exact hkm h
            · exact hk h)
    have hline := norm_le_of_ends (fun u : ℕ => G (zl + (u : ℤ) • basisVec m)) ε
      (B + (S.card : ℝ) * (2 * (lam : ℝ) ^ 2 * ε)) hε lam r' hlam hr'l
      (fun u hu => secondDiff_along_line hG zl m lam (fun k => by
        have hk : |zl k - c k| ≤ r + lam := by
          by_cases hkm : k = m
          · subst hkm
            rw [czm]
            have habs := abs_le.mp hzm
            rw [abs_le]
            constructor <;> linarith
          · rw [czk k hkm]
            by_cases hkS : k ∈ S
            · have := hin k (Finset.mem_insert_of_mem hkS)
              linarith
            · exact (hout k (fun h => by
                rcases Finset.mem_insert.mp h with h | h
                · exact hkm h
                · exact hkS h)).2
        linarith) u hu)
      (by simpa using hend 0 (Or.inl rfl)) (hend lam (Or.inr rfl))
    have ez : zl + (r' : ℤ) • basisVec m = z := by
      rw [hr', hzl]
      abel
    simp only [ez] at hline
    rw [Finset.card_insert_of_notMem hm]
    push_cast
    calc _ ≤ _ := hline
      _ = _ := by ring
private theorem siteOfInt_add_int {N : ℕ} (u v : Fin 4 → ℤ) :
    (TorusFields.siteOfInt (u + v) : TorusFields.TorusSite N) =
      TorusFields.siteOfInt u + TorusFields.siteOfInt v := by apply _root_.YangMills.Construction.BlockOffsets.siteOfInt_add <;> assumption
private theorem siteOfInt_basisVec {N : ℕ} (m : Fin 4) :
    (TorusFields.siteOfInt (basisVec m) : TorusFields.TorusSite N) = TorusFields.unitStep N m := by apply _root_.YangMills.Construction.FrameTorusAction.siteOfInt_single <;> assumption
private theorem siteOfInt_nat_smul_basisVec {N : ℕ} (t : ℕ) (m : Fin 4) :
    (TorusFields.siteOfInt ((t : ℤ) • basisVec m) : TorusFields.TorusSite N) = t • TorusFields.unitStep N m := by
  funext k
  by_cases h : k = m
  · subst h
    simp [TorusFields.siteOfInt, TorusFields.unitStep, basisVec]
  · simp [TorusFields.siteOfInt, TorusFields.unitStep, basisVec, h]
private theorem supDist_le_of_lift {n : ℕ} [NeZero n] (x y : TorusFields.TorusSite n) (u : Fin 4 → ℤ) (K : ℕ)
    (hu : ∀ k, ((u k : ℤ) : ZMod n) = x k - y k) (hb : ∀ k, |u k| ≤ (K : ℤ)) :
    TorusFields.supDist x y ≤ K := by
  unfold TorusFields.supDist
  refine Finset.sup_le fun k _ => ?_
  have h1 : ((x k - y k).valMinAbs).natAbs ≤ (u k).natAbs :=
    ZMod.natAbs_min_of_le_div_two n _ _ (by rw [ZMod.coe_valMinAbs, hu k]) (ZMod.natAbs_valMinAbs_le _)
  have h2 := hb k
  rw [Int.abs_eq_natAbs] at h2
  omega
private theorem ediv_cast_eq_iff {n lam N : ℕ} [NeZero n] [NeZero N] (hN : N = n * lam) (hlam : 0 < lam)
    (h : ℤ) (Y : ℤ) (c : ZMod N) :
    (((((c.cast : ℤ) + h) / (lam : ℤ) : ℤ)) : ZMod n) = (Y : ZMod n) ↔
      ∃ u : ℕ, u < lam ∧ ((((lam : ℤ) * Y - h + u : ℤ)) : ZMod N) = c := by
  have hl : (0 : ℤ) < lam := by exact_mod_cast hlam
  have hNz : (N : ℤ) = n * lam := by exact_mod_cast hN
  constructor
  · intro hc
    obtain ⟨w, hw⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hc.symm
    obtain ⟨x, hx⟩ : ∃ x : ℤ, x = (c.cast : ℤ) + h := ⟨_, rfl⟩
    rw [← hx] at hw
    have hdm := Int.mul_ediv_add_emod x (lam : ℤ)
    have hm0 : 0 ≤ x % lam := Int.emod_nonneg _ hl.ne'
    have hm1 : x % lam < lam := Int.emod_lt_of_pos _ hl
    refine ⟨(x % lam).toNat, by omega, ?_⟩
    have e : (lam : ℤ) * Y - h + ((x % lam).toNat : ℤ) = (c.cast : ℤ) - (N : ℤ) * w := by
      rw [Int.toNat_of_nonneg hm0, hNz]
      have : Y = x / lam - n * w := by linarith
      rw [this]
      linear_combination hdm + hx
    rw [e]
    push_cast
    simp
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨v, hv⟩ : ∃ v : ℤ, v = (lam : ℤ) * Y - h + u := ⟨_, rfl⟩
    rw [← hv, ZMod.coe_intCast]
    have hdm := Int.mul_ediv_add_emod v (N : ℤ)
    have e : v % (N : ℤ) + h = (u : ℤ) + (lam : ℤ) * (Y - n * (v / (N : ℤ))) := by
      rw [hNz] at hdm ⊢
      linear_combination hdm + hv
    rw [e, Int.add_mul_ediv_left _ _ hl.ne', Int.ediv_eq_zero_of_lt (by positivity) (by exact_mod_cast hu)]
    push_cast
    simp
private theorem eq_of_cast_add_eq {N lam : ℕ} (hle : lam ≤ N) (a : ℤ) (u u' : ℕ) (hu : u < lam) (hu' : u' < lam)
    (h : (((a + u : ℤ)) : ZMod N) = ((a + u' : ℤ) : ZMod N)) : u = u' := by
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h
  have e : a + (u' : ℤ) - (a + u) = (u' : ℤ) - u := by ring
  rw [e] at hd
  have hlt : |(u' : ℤ) - u| < N := by
    rw [abs_lt]
    constructor <;> omega
  have := Int.eq_zero_of_abs_lt_dvd hd hlt
  omega
private theorem siteAbove_apply (L : ℕ) [NeZero L] (hL : Odd L) :
    ∀ (d n : ℕ) [NeZero n] (y : TorusFields.TorusSite (WeightedResponses.fineSide L d n)) (k : Fin 4),
      ResponseInTheExpansion.siteAbove L d n y k =
        (((((y k).cast : ℤ) + ((L : ℤ) ^ d - 1) / 2) / (L : ℤ) ^ d : ℤ) : ZMod n) := by
  intro d
  induction d with
  | zero =>
    intro n _ y k
    have e : ((((y k).cast : ℤ) + ((L : ℤ) ^ 0 - 1) / 2) / (L : ℤ) ^ 0) = ((y k).cast : ℤ) := by simp
    rw [e]
    exact (ZMod.intCast_zmod_cast (y k)).symm
  | succ d ih =>
    intro n _ y k
    have : NeZero (n * L) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
    have h1 := ih (n * L) y k
    obtain ⟨l, hl⟩ := hL
    obtain ⟨a, ha⟩ : Odd (L ^ d) := Odd.pow ⟨l, hl⟩
    have hLz : (L : ℤ) = 2 * l + 1 := by exact_mod_cast hl
    have hAz : (L : ℤ) ^ d = 2 * a + 1 := by exact_mod_cast ha
    have h1e : ((L : ℤ) - 1) / 2 = l := by rw [hLz]; omega
    have hde : ((L : ℤ) ^ d - 1) / 2 = a := by rw [hAz]; omega
    have hd1e : ((L : ℤ) ^ (d + 1) - 1) / 2 = 2 * a * l + a + l := by
      rw [pow_succ, hAz, hLz]
      have : ((2 * (a : ℤ) + 1) * (2 * l + 1) - 1) = 2 * (2 * a * l + a + l) := by ring
      rw [this]
      simp
    obtain ⟨x, hx⟩ : ∃ x : ℤ, x = ((y k).cast : ℤ) := ⟨_, rfl⟩
    have hL0 : (L : ℤ) ≠ 0 := by rw [hLz]; omega
    have hA0 : (0 : ℤ) < (L : ℤ) ^ d := by rw [hAz]; omega
    obtain ⟨u, hu⟩ : ∃ u : ℤ, u = (x + a) / (L : ℤ) ^ d := ⟨_, rfl⟩
    have h2 : ResponseInTheExpansion.siteAbove L d (n * L) y k = ((u : ℤ) : ZMod (n * L)) := by
      rw [hu, hx, ← hde]
      exact h1
    show TorusLumps.parentBlock L (ResponseInTheExpansion.siteAbove L d (n * L) y) k = _
    have hB : (u + l) / (L : ℤ) = (x + (2 * a * l + a + l)) / (L : ℤ) ^ (d + 1) := by
      have e1 : u + l = (x + a + (L : ℤ) ^ d * l) / (L : ℤ) ^ d := by
        rw [Int.add_mul_ediv_left _ _ hA0.ne', hu]
      rw [e1, Int.ediv_ediv_of_nonneg hA0.le, ← pow_succ]
      congr 1
      rw [hAz]
      ring
    have hC : ((u % ((n * L : ℕ) : ℤ) + l) / (L : ℤ)) = (u + l) / (L : ℤ) - n * (u / ((n * L : ℕ) : ℤ)) := by
      have hdm := Int.mul_ediv_add_emod u ((n * L : ℕ) : ℤ)
      have e : u + l = (u % ((n * L : ℕ) : ℤ) + l) + (L : ℤ) * (n * (u / ((n * L : ℕ) : ℤ))) := by
        push_cast at hdm ⊢
        linear_combination -hdm
      rw [e, Int.add_mul_ediv_left _ _ hL0]
      ring_nf
    simp only [TorusLumps.parentBlock]
    rw [h2, ZMod.coe_intCast, h1e, hC, hB, hd1e, ← hx]
    push_cast
    simp
private theorem sum_indicator_smul {α : Type} (S : Finset α) (F : α → BlockAverages.imaginaryQuaternions)
    (t : α) (ht : t ∈ S) (d : ∀ p, Decidable (p = t)) :
    ∑ p ∈ S, (@ite ℝ (p = t) (d p) 1 0) • F p = F t := by
  rw [Finset.sum_eq_single t]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd ht h
private def cornerVec (b : Fin 4 → ℤ) (x : ℕ × ℕ × ℕ × ℕ) : Fin 4 → ℤ :=
  b + (x.1 : ℤ) • basisVec 0 + (x.2.1 : ℤ) • basisVec 1 + (x.2.2.1 : ℤ) • basisVec 2 + (x.2.2.2 : ℤ) • basisVec 3
private theorem cornerVec_apply (b : Fin 4 → ℤ) (x : ℕ × ℕ × ℕ × ℕ) (k : Fin 4) :
    cornerVec b x k = b k + ((![x.1, x.2.1, x.2.2.1, x.2.2.2] k : ℕ) : ℤ) := by
  fin_cases k <;> simp [cornerVec, basisVec]
private theorem siteAbove_eq_iff (L s n h : ℕ) [NeZero L] [NeZero n] (hodd : Odd L) (hlam : L ^ s = 2 * h + 1)
    (Y b : Fin 4 → ℤ) (hb : ∀ k, b k = ((2 * h + 1 : ℕ) : ℤ) * Y k - h)
    (y : TorusFields.TorusSite (WeightedResponses.fineSide L s n)) :
    ResponseInTheExpansion.siteAbove L s n y = TorusFields.siteOfInt Y ↔
      ∀ k, ∃ u : ℕ, u < 2 * h + 1 ∧
        (((b k + u : ℤ)) : ZMod (WeightedResponses.fineSide L s n)) = y k := by
  have hN : WeightedResponses.fineSide L s n = n * (2 * h + 1) := by
    rw [WeightedResponses.fineSide_eq, hlam]
  have hz : (L : ℤ) ^ s = ((2 * h + 1 : ℕ) : ℤ) := by exact_mod_cast hlam
  have hhalf : ((L : ℤ) ^ s - 1) / 2 = h := by
    rw [hz]
    push_cast
    omega
  have hcore : ∀ k, ResponseInTheExpansion.siteAbove L s n y k = (Y k : ZMod n) ↔
      ∃ u : ℕ, u < 2 * h + 1 ∧ (((b k + u : ℤ)) : ZMod (WeightedResponses.fineSide L s n)) = y k := by
    intro k
    rw [siteAbove_apply L hodd s n y k, hhalf, hz,
      ediv_cast_eq_iff hN (by omega) (h : ℤ) (Y k) (y k), hb k]
  constructor
  · intro hy k
    exact (hcore k).mp (congrFun hy k)
  · intro hy
    funext k
    exact (hcore k).mpr (hy k)
private theorem sum_filter_siteAbove (L s n h : ℕ) [NeZero L] [NeZero n] (hodd : Odd L)
    (hlam : L ^ s = 2 * h + 1)
    (Y b : Fin 4 → ℤ) (hb : ∀ k, b k = ((2 * h + 1 : ℕ) : ℤ) * Y k - h)
    (f : TorusFields.TorusSite (WeightedResponses.fineSide L s n) → BlockAverages.imaginaryQuaternions)
    (inst : DecidablePred fun y : TorusFields.TorusSite (WeightedResponses.fineSide L s n) =>
      ResponseInTheExpansion.siteAbove L s n y = TorusFields.siteOfInt Y) :
    ∑ y ∈ Finset.univ.filter (fun y : TorusFields.TorusSite (WeightedResponses.fineSide L s n) =>
        ResponseInTheExpansion.siteAbove L s n y = TorusFields.siteOfInt Y), f y =
      ∑ u0 ∈ Finset.range (2 * h + 1), ∑ u1 ∈ Finset.range (2 * h + 1), ∑ u2 ∈ Finset.range (2 * h + 1),
        ∑ u3 ∈ Finset.range (2 * h + 1), f (TorusFields.siteOfInt (cornerVec b (u0, u1, u2, u3))) := by
  have hN : WeightedResponses.fineSide L s n = n * (2 * h + 1) := by
    rw [WeightedResponses.fineSide_eq, hlam]
  have hle : 2 * h + 1 ≤ WeightedResponses.fineSide L s n := by
    rw [hN]
    exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (NeZero.ne n))
  have hU : ∀ x ∈ Finset.range (2 * h + 1) ×ˢ Finset.range (2 * h + 1) ×ˢ Finset.range (2 * h + 1) ×ˢ
      Finset.range (2 * h + 1), ∀ k : Fin 4, (![x.1, x.2.1, x.2.2.1, x.2.2.2] k : ℕ) < 2 * h + 1 := by
    intro x hx k
    simp only [Finset.mem_product, Finset.mem_range] at hx
    fin_cases k
    · exact hx.1
    · exact hx.2.1
    · exact hx.2.2.1
    · exact hx.2.2.2
  have key : ∑ y ∈ Finset.univ.filter (fun y : TorusFields.TorusSite (WeightedResponses.fineSide L s n) =>
        ResponseInTheExpansion.siteAbove L s n y = TorusFields.siteOfInt Y), f y =
      ∑ x ∈ Finset.range (2 * h + 1) ×ˢ Finset.range (2 * h + 1) ×ˢ Finset.range (2 * h + 1) ×ˢ
        Finset.range (2 * h + 1), f (TorusFields.siteOfInt (cornerVec b x)) := by
    symm
    refine Finset.sum_bij (fun x _ => TorusFields.siteOfInt (cornerVec b x)) ?_ ?_ ?_ ?_
    · intro x hx
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (siteAbove_eq_iff L s n h hodd hlam Y b hb _).mpr fun k => ?_⟩
      refine ⟨_, hU x hx k, ?_⟩
      show _ = ((cornerVec b x k : ℤ) : ZMod (WeightedResponses.fineSide L s n))
      rw [cornerVec_apply]
    · intro x hx x' hx' heq
      have hk : ∀ k : Fin 4, (![x.1, x.2.1, x.2.2.1, x.2.2.2] k : ℕ) = ![x'.1, x'.2.1, x'.2.2.1, x'.2.2.2] k := by
        intro k
        refine eq_of_cast_add_eq hle (b k) _ _ (hU x hx k) (hU x' hx' k) ?_
        have := congrFun heq k
        simp only [TorusFields.siteOfInt, cornerVec_apply] at this
        exact this
      have h0 := hk 0
      have h1 := hk 1
      have h2 := hk 2
      have h3 := hk 3
      simp at h0 h1 h2 h3
      exact Prod.ext h0 (Prod.ext h1 (Prod.ext h2 h3))
    · intro y hy
      have hy' := (siteAbove_eq_iff L s n h hodd hlam Y b hb y).mp (Finset.mem_filter.mp hy).2
      choose u hu hu2 using hy'
      refine ⟨(u 0, u 1, u 2, u 3), ?_, ?_⟩
      · simp only [Finset.mem_product, Finset.mem_range]
        exact ⟨hu 0, hu 1, hu 2, hu 3⟩
      · funext k
        show ((cornerVec b (u 0, u 1, u 2, u 3) k : ℤ) : ZMod (WeightedResponses.fineSide L s n)) = y k
        rw [cornerVec_apply]
        fin_cases k
        · exact hu2 0
        · exact hu2 1
        · exact hu2 2
        · exact hu2 3
    · intro x _
      rfl
  rw [key]
  simp only [Finset.sum_product]
private theorem sum_blockWeight_smul (L s n h : ℕ) [NeZero L] [NeZero n] (hodd : Odd L)
    (hlam : L ^ s = 2 * h + 1)
    (F : TorusFields.TorusPlaquette (WeightedResponses.fineSide L s n) → BlockAverages.imaginaryQuaternions)
    (i j : Fin 4) (hij : i < j) (Y b : Fin 4 → ℤ)
    (hb : ∀ k, b k = ((2 * h + 1 : ℕ) : ℤ) * Y k - h) :
    ∑ p ∈ TorusFields.plaquettesIn (Finset.univ : Finset (TorusFields.TorusSite (WeightedResponses.fineSide L s n))),
        BoxEvents.blockWeight L s ((TorusFields.siteOfInt Y : TorusFields.TorusSite n), i, j) p • F p =
      ((2 * h + 1 : ℕ) : ℝ) ^ 2 •
        iteratedMean (2 * h + 1) (fun z => F (TorusFields.siteOfInt z, i, j)) [0, 1, 2, 3, i, j] b := by
  have hmem : ∀ t : TorusFields.TorusSite (WeightedResponses.fineSide L s n),
      (t, i, j) ∈ TorusFields.plaquettesIn
        (Finset.univ : Finset (TorusFields.TorusSite (WeightedResponses.fineSide L s n))) := by
    intro t
    simp [TorusFields.plaquettesIn, hij]
  simp only [BoxEvents.blockWeight, mul_smul, Finset.sum_smul]
  rw [← Finset.smul_sum, Finset.sum_comm]
  have step : ∀ y : TorusFields.TorusSite (WeightedResponses.fineSide L s n),
      ∑ p ∈ TorusFields.plaquettesIn
          (Finset.univ : Finset (TorusFields.TorusSite (WeightedResponses.fineSide L s n))),
        ∑ a ∈ Finset.range (L ^ s), ∑ c ∈ Finset.range (L ^ s),
          (if p = (y + a • TorusFields.unitStep (WeightedResponses.fineSide L s n) i +
              c • TorusFields.unitStep (WeightedResponses.fineSide L s n) j, i, j)
            then (1 : ℝ) else 0) • F p =
      ∑ a ∈ Finset.range (L ^ s), ∑ c ∈ Finset.range (L ^ s),
        F (y + a • TorusFields.unitStep (WeightedResponses.fineSide L s n) i +
          c • TorusFields.unitStep (WeightedResponses.fineSide L s n) j, i, j) := by
    intro y
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    exact sum_indicator_smul _ _ _ (hmem _) _
  rw [Finset.sum_congr rfl fun y _ => step y, sum_filter_siteAbove L s n h hodd hlam Y b hb]
  have hl0 : (0 : ℝ) < ((2 * h + 1 : ℕ) : ℝ) := by positivity
  have hc : 1 / (L : ℝ) ^ (4 * s) = (1 / ((2 * h + 1 : ℕ) : ℝ)) ^ 4 := by
    have : (L : ℝ) ^ s = ((2 * h + 1 : ℕ) : ℝ) := by exact_mod_cast hlam
    rw [pow_mul', this, one_div_pow]
  rw [hc, hlam]
  simp only [iteratedMean, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun u0 _ => Finset.sum_congr rfl fun u1 _ => Finset.sum_congr rfl fun u2 _ =>
    Finset.sum_congr rfl fun u3 _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  have e : (TorusFields.siteOfInt (b + (u0 : ℤ) • basisVec 0 + (u1 : ℤ) • basisVec 1 + (u2 : ℤ) • basisVec 2 +
      (u3 : ℤ) • basisVec 3 + (a : ℤ) • basisVec i + (c : ℤ) • basisVec j) :
        TorusFields.TorusSite (WeightedResponses.fineSide L s n)) =
      TorusFields.siteOfInt (cornerVec b (u0, u1, u2, u3)) +
        a • TorusFields.unitStep (WeightedResponses.fineSide L s n) i +
        c • TorusFields.unitStep (WeightedResponses.fineSide L s n) j := by
    rw [siteOfInt_add_int, siteOfInt_add_int, siteOfInt_nat_smul_basisVec, siteOfInt_nat_smul_basisVec]
    rfl
  rw [e]
  congr 1
  field_simp
private theorem coarseningSteps_bounds (L R : ℕ) (hL : 3 ≤ L) (hR : 1 ≤ R) :
    (R : ℝ) ^ (2 / 3 : ℝ) ≤ (L : ℝ) ^ coarseningSteps L R ∧
      (L : ℝ) ^ coarseningSteps L R ≤ L * (R : ℝ) ^ (2 / 3 : ℝ) := by
  have hL1 : (1 : ℝ) < L := by
    have : (3 : ℝ) ≤ L := by exact_mod_cast hL
    linarith
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hρ1 : 1 ≤ (R : ℝ) ^ (2 / 3 : ℝ) := Real.one_le_rpow hR1 (by norm_num)
  have hne : {s : ℕ | (R : ℝ) ^ (2 / 3 : ℝ) ≤ (L : ℝ) ^ s}.Nonempty := by
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt ((R : ℝ) ^ (2 / 3 : ℝ)) hL1
    exact ⟨m, hm.le⟩
  have hmem := Nat.sInf_mem hne
  unfold coarseningSteps
  refine ⟨hmem, ?_⟩
  rcases hs : sInf {s : ℕ | (R : ℝ) ^ (2 / 3 : ℝ) ≤ (L : ℝ) ^ s} with _ | t
  · simp only [pow_zero]
    nlinarith
  · have hnot : t ∉ {s : ℕ | (R : ℝ) ^ (2 / 3 : ℝ) ≤ (L : ℝ) ^ s} := Nat.notMem_of_lt_sInf (by omega)
    have hlt : (L : ℝ) ^ t < (R : ℝ) ^ (2 / 3 : ℝ) := not_le.mp hnot
    rw [pow_succ, mul_comm]
    exact mul_le_mul_of_nonneg_left hlt.le (by linarith)
private theorem mul_rpow_two_thirds_le (L R : ℕ) (hR : (128 * L) ^ 3 ≤ R) :
    128 * (L : ℝ) * (R : ℝ) ^ (2 / 3 : ℝ) ≤ R := by
  have hcube : ((R : ℝ) ^ (2 / 3 : ℝ)) ^ 3 = (R : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hRr : (128 * (L : ℝ)) ^ 3 ≤ R := by exact_mod_cast hR
  refine le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (by positivity) ?_
  rw [mul_pow, hcube]
  calc _ ≤ (R : ℝ) * (R : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hRr (by positivity)
    _ = (R : ℝ) ^ 3 := by ring
theorem backgroundFromBlockMeans : backgroundFromBlockMeansStatement := by
  intro L _ hodd hL3 C₂
  refine ⟨13 + 20 * (L : ℝ) ^ 2 * |C₂|, (128 * L) ^ 3, ?_⟩
  intro s n R _ o δ F hR hs _ hδ hsec hmean p hp
  obtain ⟨x, i, j⟩ := p
  have hL0 : 0 < L := by omega
  have hR1 : 1 ≤ R := le_trans (Nat.one_le_pow _ _ (by omega)) hR
  have hRr : (0 : ℝ) < R := by exact_mod_cast hR1
  obtain ⟨hlo, hhi⟩ := coarseningSteps_bounds L R hL3 hR1
  rw [← hs] at hlo hhi
  have hroom := mul_rpow_two_thirds_le L R hR
  obtain ⟨h, hh⟩ : ∃ h, L ^ s = 2 * h + 1 := (Odd.pow hodd : Odd (L ^ s))
  obtain ⟨ρh, hρh⟩ : ∃ ρh : ℝ, ρh = (R : ℝ) ^ (2 / 3 : ℝ) := ⟨_, rfl⟩
  rw [← hρh] at hlo hhi hroom
  have hρ1 : 1 ≤ ρh := by
    rw [hρh]
    exact Real.one_le_rpow (by exact_mod_cast hR1) (by norm_num)
  obtain ⟨l, hl⟩ : ∃ l : ℝ, l = ((2 * h + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  have hlL : (L : ℝ) ^ s = l := by rw [hl]; exact_mod_cast hh
  rw [hlL] at hlo hhi hmean
  have hl0 : 0 < l := by rw [hl]; positivity
  have hbig : 72 * (2 * h + 1) + 24 ≤ R := by
    have h1 : 1 ≤ (L : ℝ) * ρh := by nlinarith
    have : (72 : ℝ) * l + 24 ≤ R := by linarith
    rw [hl] at this
    exact_mod_cast this
  obtain ⟨r, hr⟩ : ∃ r : ℕ, r = R / 8 := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℕ, q = R / 4 := ⟨_, rfl⟩
  have hrq : r + 9 * (2 * h + 1) + 2 ≤ q := by omega
  have hqr : (q : ℝ) ≤ (R : ℝ) / 4 := by
    have := Nat.cast_div_le (α := ℝ) (m := R) (n := 4)
    rw [hq]
    simpa using this
  have hrr : (r : ℝ) ≤ (R : ℝ) / 8 := by
    have := Nat.cast_div_le (α := ℝ) (m := R) (n := 8)
    rw [hr]
    simpa using this
  have hp' := hp
  simp only [TorusFields.plaquettesIn, Finset.mem_filter, Finset.mem_univ, true_and] at hp'
  obtain ⟨hij, hcor⟩ := hp'
  have hxr : TorusFields.supDist x o ≤ r := by
    have hxm : x ∈ ResponseInTheExpansion.supBall o ((R : ℝ) / 8) := hcor x (by simp [TorusFields.plaquetteVertices])
    have h1 : (TorusFields.supDist x o : ℝ) ≤ (R : ℝ) / 8 := (Finset.mem_filter.mp hxm).2
    have h2 : ((8 * TorusFields.supDist x o : ℕ) : ℝ) ≤ R := by
      push_cast
      linarith
    have h3 : 8 * TorusFields.supDist x o ≤ R := by exact_mod_cast h2
    omega
  obtain ⟨c, hc⟩ : ∃ c : Fin 4 → ℤ, c = fun k => ((o k).cast : ℤ) := ⟨_, rfl⟩
  have hoc : ∀ k, ((c k : ℤ) : ZMod (WeightedResponses.fineSide L s n)) = o k := by
    intro k
    rw [hc]
    exact ZMod.intCast_zmod_cast _
  have hbox : ∀ (K : ℕ) (rr : ℝ), (K : ℝ) ≤ rr → ∀ z : Fin 4 → ℤ, (∀ k, |z k - c k| ≤ (K : ℤ)) →
      (TorusFields.siteOfInt z : TorusFields.TorusSite (WeightedResponses.fineSide L s n)) ∈
        ResponseInTheExpansion.supBall o rr := by
    intro K rr hK z hz
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_trans ?_ hK⟩
    have h1 := supDist_le_of_lift
      (TorusFields.siteOfInt z : TorusFields.TorusSite (WeightedResponses.fineSide L s n)) o (z - c) K
      (fun k => by
        rw [← hoc k]
        simp [TorusFields.siteOfInt]) (fun k => hz k)
    exact_mod_cast h1
  obtain ⟨G, hGdef⟩ : ∃ G : (Fin 4 → ℤ) → BlockAverages.imaginaryQuaternions,
      G = fun z => F (TorusFields.siteOfInt z, i, j) := ⟨_, rfl⟩
  obtain ⟨ε, hεd⟩ : ∃ ε : ℝ, ε = |C₂| * ((R : ℝ) ^ 2)⁻¹ * δ := ⟨_, rfl⟩
  have hε : 0 ≤ ε := by rw [hεd]; positivity
  have cu : ∀ (w : Fin 4 → ℤ) (m k : Fin 4), |(w + basisVec m) k - c k| ≤ |w k - c k| + 1 := by
    intro w m k
    simpa using abs_add_smul_basisVec_sub_le w c m k 1 (by norm_num)
  have hsd : SecondDiffBound G c ((q : ℤ) - 2) ε := by
    intro m z hz
    have hin := hbox q ((R : ℝ) / 4) hqr
    have hp2 : ((TorusFields.siteOfInt z : TorusFields.TorusSite (WeightedResponses.fineSide L s n)), i, j) ∈
        TorusFields.plaquettesIn (ResponseInTheExpansion.supBall o ((R : ℝ) / 4)) := by
      simp only [TorusFields.plaquettesIn, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hij, ?_⟩
      intro w hw
      simp only [TorusFields.plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · exact hin z fun k => by linarith [hz k]
      · rw [← siteOfInt_basisVec, ← siteOfInt_add_int]
        exact hin _ fun k => by linarith [hz k, cu z i k]
      · rw [← siteOfInt_basisVec, ← siteOfInt_add_int]
        exact hin _ fun k => by linarith [hz k, cu z j k]
      · rw [← siteOfInt_basisVec, ← siteOfInt_basisVec, ← siteOfInt_add_int, ← siteOfInt_add_int]
        exact hin _ fun k => by linarith [hz k, cu z i k, cu (z + basisVec i) j k]
    have hb := hsec [m, m] rfl _ hp2
    have e : iteratedDiff [m, m] F
        ((TorusFields.siteOfInt z : TorusFields.TorusSite (WeightedResponses.fineSide L s n)), i, j) =
        G (z + basisVec m + basisVec m) - (2 : ℝ) • G (z + basisVec m) + G z := by
      rw [hGdef]
      simp only [iteratedDiff, List.foldr, forwardDiff, siteOfInt_add_int, siteOfInt_basisVec]
      module
    rw [← e]
    refine hb.trans ?_
    rw [hεd]
    have : C₂ ≤ |C₂| := le_abs_self _
    gcongr
  have hh0 : (0 : ℤ) ≤ h := by positivity
  have hzl : (L : ℤ) ^ s = ((2 * h + 1 : ℕ) : ℤ) := by exact_mod_cast hh
  have hhalf : ((L : ℤ) ^ s - 1) / 2 = h := by
    rw [hzl]
    push_cast
    omega
  obtain ⟨g, hgd⟩ : ∃ g : Fin 4 → ℤ, g = iteratedShift (h : ℤ) [i, j] := ⟨_, rfl⟩
  have hne : i ≠ j := hij.ne
  have hg : ∀ k, 0 ≤ g k ∧ g k ≤ h := by
    intro k
    have e : g k = (if k = i then (h : ℤ) else 0) + (if k = j then (h : ℤ) else 0) := by
      rw [hgd]
      simp [iteratedShift, basisVec, Pi.single_apply]
    rw [e]
    by_cases h1 : k = i
    · have h2 : k ≠ j := fun e => hne (h1.symm.trans e)
      simp [h1, hne, hh0]
    · by_cases h2 : k = j
      · simp [h2, hne.symm, hh0]
      · simp [h1, h2, hh0]
  have hshift : ∀ k, iteratedShift (h : ℤ) [0, 1, 2, 3, i, j] k = h + g k := by
    intro k
    rw [hgd]
    have e : ∀ X : Fin 4 → ℤ, ((h : ℤ) • basisVec 0 + ((h : ℤ) • basisVec 1 + ((h : ℤ) • basisVec 2 +
        ((h : ℤ) • basisVec 3 + X)))) k = h + X k := by
      intro X
      fin_cases k <;> simp [basisVec]
    exact e (iteratedShift (h : ℤ) [i, j])
  have hO : ∀ k, ResponseInTheExpansion.siteAbove L s n o k =
      ((((c k + h) / ((2 * h + 1 : ℕ) : ℤ) : ℤ)) : ZMod n) := by
    intro k
    rw [siteAbove_apply L hodd s n o k, hhalf, hzl, hc]
  have hgrid : ∀ z : Fin 4 → ℤ, (∀ k, ((2 * h + 1 : ℕ) : ℤ) ∣ z k - g k) →
      (∀ k, |z k - c k| ≤ (r : ℤ) + ((2 * h + 1 : ℕ) : ℤ)) → ‖G z‖ ≤ 13 * δ / l + 6 * (2 * l ^ 2 * ε) := by
    intro z hdiv hzb
    choose Y hY using hdiv
    obtain ⟨b, hbd⟩ : ∃ b : Fin 4 → ℤ, b = z - iteratedShift (h : ℤ) [0, 1, 2, 3, i, j] := ⟨_, rfl⟩
    have hbk : ∀ k, b k = ((2 * h + 1 : ℕ) : ℤ) * Y k - h := by
      intro k
      rw [hbd, Pi.sub_apply, hshift k]
      linarith [hY k]
    have hclose := norm_iteratedMean_sub_le hε hsd h [0, 1, 2, 3, i, j] b (fun k => by
      have h1 := abs_le.mp (hzb k)
      have h2 := hg k
      have e : b k - c k = (z k - c k) - g k - h := by
        rw [hbd, Pi.sub_apply, hshift k]
        ring
      have h3 : |b k - c k| ≤ (r : ℤ) + ((2 * h + 1 : ℕ) : ℤ) + 2 * h := by
        rw [e, abs_le]
        constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
      simp only [List.length_cons, List.length_nil]
      push_cast at h3 ⊢
      linarith)
    have hbz : b + iteratedShift (h : ℤ) [0, 1, 2, 3, i, j] = z := by
      rw [hbd]
      abel
    rw [hbz, ← hl] at hclose
    have hYb : ∀ k, ((2 * h + 1 : ℕ) : ℤ) * |Y k - (c k + h) / ((2 * h + 1 : ℕ) : ℤ)| ≤
        (r : ℤ) + 2 * ((2 * h + 1 : ℕ) : ℤ) := by
      intro k
      have hpos : (0 : ℤ) < ((2 * h + 1 : ℕ) : ℤ) := by positivity
      have hdm := Int.mul_ediv_add_emod (c k + h) ((2 * h + 1 : ℕ) : ℤ)
      have hm0 := Int.emod_nonneg (c k + h) hpos.ne'
      have hm1 := Int.emod_lt_of_pos (c k + h) hpos
      have h1 := abs_le.mp (hzb k)
      have h2 := hg k
      have h3 := hY k
      rw [← abs_of_pos hpos, ← abs_mul, abs_of_pos hpos, abs_le]
      obtain ⟨O, hOd⟩ : ∃ O : ℤ, O = (c k + h) / ((2 * h + 1 : ℕ) : ℤ) := ⟨_, rfl⟩
      rw [← hOd] at hdm ⊢
      have e : ((2 * h + 1 : ℕ) : ℤ) * (Y k - O) =
          (z k - c k) - g k + (c k + h) % ((2 * h + 1 : ℕ) : ℤ) - h := by
        linear_combination -h3 - hdm
      rw [e]
      push_cast at h1 hm0 hm1 ⊢
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    obtain ⟨K, hK⟩ : ∃ K : ℕ, K = (r + 2 * (2 * h + 1)) / (2 * h + 1) := ⟨_, rfl⟩
    have hKb : ∀ k, |Y k - (c k + h) / ((2 * h + 1 : ℕ) : ℤ)| ≤ (K : ℤ) := by
      intro k
      have h1 := hYb k
      rw [Int.abs_eq_natAbs] at h1 ⊢
      have h2 : (Y k - (c k + h) / ((2 * h + 1 : ℕ) : ℤ)).natAbs * (2 * h + 1) ≤ r + 2 * (2 * h + 1) := by
        rw [mul_comm]
        exact_mod_cast h1
      have h3 := (Nat.le_div_iff_mul_le (by omega)).mpr h2
      rw [← hK] at h3
      exact_mod_cast h3
    have htd : TorusFields.supDist (TorusFields.siteOfInt Y : TorusFields.TorusSite n)
        (ResponseInTheExpansion.siteAbove L s n o) ≤ K :=
      supDist_le_of_lift _ _ (fun k => Y k - (c k + h) / ((2 * h + 1 : ℕ) : ℤ)) K
        (fun k => by
          rw [hO k]
          simp [TorusFields.siteOfInt]) hKb
    have hKl : K * (2 * h + 1) ≤ r + 2 * (2 * h + 1) := by
      rw [hK]
      exact Nat.div_mul_le_self _ _
    have hdist : l * (TorusFields.supDist (TorusFields.siteOfInt Y : TorusFields.TorusSite n)
        (ResponseInTheExpansion.siteAbove L s n o) : ℝ) ≤ (R : ℝ) / 8 + 2 * l := by
      have h1 : (TorusFields.supDist (TorusFields.siteOfInt Y : TorusFields.TorusSite n)
          (ResponseInTheExpansion.siteAbove L s n o) : ℝ) ≤ K := by exact_mod_cast htd
      have h2 : (K : ℝ) * l ≤ r + 2 * l := by
        rw [hl]
        exact_mod_cast hKl
      nlinarith
    have hm := hmean ((TorusFields.siteOfInt Y : TorusFields.TorusSite n), i, j)
      (by simp [TorusFields.plaquettesIn, hij]) hdist
    rw [sum_blockWeight_smul L s n h hodd hh F i j hij Y b hbk, norm_smul, ← hl, ← hGdef, Real.norm_eq_abs,
      abs_of_pos (by positivity)] at hm
    have hM : ‖iteratedMean (2 * h + 1) G [0, 1, 2, 3, i, j] b‖ ≤ 13 * δ / l := by
      rw [le_div_iff₀ hl0]
      have h1 : l * (‖iteratedMean (2 * h + 1) G [0, 1, 2, 3, i, j] b‖ * l) ≤ l * (13 * δ) := by
        calc _ = l ^ 2 * ‖iteratedMean (2 * h + 1) G [0, 1, 2, 3, i, j] b‖ := by ring
          _ ≤ 13 * l * δ := hm
          _ = _ := by ring
      exact le_of_mul_le_mul_left h1 hl0
    have hzn : ‖G z‖ ≤ ‖iteratedMean (2 * h + 1) G [0, 1, 2, 3, i, j] b‖ +
        ‖iteratedMean (2 * h + 1) G [0, 1, 2, 3, i, j] b - G z‖ := by
      have := norm_sub_norm_le (G z) (iteratedMean (2 * h + 1) G [0, 1, 2, 3, i, j] b)
      rw [norm_sub_rev] at this
      linarith
    simp only [List.length_cons, List.length_nil] at hclose
    push_cast at hclose
    calc _ ≤ _ := hzn
      _ ≤ 13 * δ / l + 6 * (2 * l ^ 2 * ε) := by linarith
  obtain ⟨w, hwd⟩ : ∃ w : Fin 4 → ℤ, w = fun k => (x k - o k).valMinAbs := ⟨_, rfl⟩
  have hwb : ∀ k, |(c + w) k - c k| ≤ (r : ℤ) := by
    intro k
    have e : (c + w) k - c k = (x k - o k).valMinAbs := by
      rw [hwd]
      simp
    rw [e, Int.abs_eq_natAbs]
    have h1 : ((x k - o k).valMinAbs).natAbs ≤ TorusFields.supDist x o :=
      Finset.le_sup (f := fun i => ((x i - o i).valMinAbs).natAbs) (Finset.mem_univ k)
    have h2 := h1.trans hxr
    exact_mod_cast h2
  have hzx : (TorusFields.siteOfInt (c + w) : TorusFields.TorusSite (WeightedResponses.fineSide L s n)) = x := by
    funext k
    rw [hwd]
    simp [TorusFields.siteOfInt, hoc k, ZMod.coe_valMinAbs]
  have hfin := norm_le_of_lattice_bound hε hsd (2 * h + 1) (by omega) (by push_cast; linarith) hgrid
    Finset.univ (c + w) (fun k _ => hwb k) (fun k hk => absurd (Finset.mem_univ k) hk)
  have hGF : G (c + w) = F (x, i, j) := by
    rw [hGdef]
    simp only [hzx]
  rw [hGF, Finset.card_univ, Fintype.card_fin, ← hl] at hfin
  refine hfin.trans ?_
  have hρ0 : 0 < ρh := by linarith
  have hneg : (R : ℝ) ^ (-(2 / 3 : ℝ)) = ρh⁻¹ := by
    rw [hρh, Real.rpow_neg hRr.le]
  have hcube : (R : ℝ) ^ 2 = ρh ^ 3 := by
    rw [hρh, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hRr.le]
    norm_num
  have hε2 : l ^ 2 * ε ≤ (L : ℝ) ^ 2 * |C₂| * ρh⁻¹ * δ := by
    have h1 : l ^ 2 ≤ ((L : ℝ) * ρh) ^ 2 := by
      have : 0 ≤ l := hl0.le
      gcongr
    calc _ ≤ ((L : ℝ) * ρh) ^ 2 * ε := mul_le_mul_of_nonneg_right h1 hε
      _ = _ := by
        rw [hεd, hcube]
        field_simp
  have h13 : 13 * δ / l ≤ 13 * ρh⁻¹ * δ := by
    rw [div_le_iff₀ hl0]
    have h1 : 1 ≤ ρh⁻¹ * l := by
      rw [inv_mul_eq_div, one_le_div₀ hρ0]
      exact hlo
    nlinarith
  rw [hneg]
  have e : (13 + 20 * (L : ℝ) ^ 2 * |C₂|) * ρh⁻¹ * δ =
      13 * ρh⁻¹ * δ + 20 * ((L : ℝ) ^ 2 * |C₂| * ρh⁻¹ * δ) := by ring
  rw [e]
  push_cast
  linarith
end YangMills.Construction.BoxGaussian
end
