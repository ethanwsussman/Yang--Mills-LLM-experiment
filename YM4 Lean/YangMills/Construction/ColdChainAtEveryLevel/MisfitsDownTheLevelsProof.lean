import YangMills.Construction.ColdChainAtEveryLevel.FallOfTheVariations
import YangMills.Construction.ColdChainAtEveryLevel.GapsOfTheLevelsNearACell
import YangMills.Construction.ColdChainAtEveryLevel.SumsOverTheEvaluations
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.MisfitDecay
open BlockAverages BlockLines NearCellNorms VariationDecay MisfitVariation MisfitSums BlockWeights FiniteDifferences
variable {F : BlockFrame}
theorem card_bondsOver_singleton_le (hodd : Odd F.blockSide) (S : Finset F.Cell) (z : F.Cell) (i : ℕ) :
    ((bondsOver S {z} i).card : ℝ) ≤ 4 * ((F.blockSide : ℝ) ^ (F.top - i)) ^ 4 := by
  classical
  have hsub : bondsOver S {z} i ⊆ sitesOfCells ({z} : Finset F.Cell) i ×ˢ (Finset.univ : Finset (Fin 4)) := by
    intro b hb
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hb
    have h3 := (Finset.mem_filter.1 h1).1
    exact Finset.mem_product.2 ⟨mem_sitesOfCells_of_enclosingCell_mem hodd (Finset.mem_product.1 h3).1 h2, Finset.mem_univ _⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fin] at h1
  have h2 := card_sitesOfCells_le hodd ({z} : Finset F.Cell) i
  rw [Finset.card_singleton, one_mul] at h2
  have h3 : (bondsOver S {z} i).card ≤ (F.blockSide ^ (F.top - i)) ^ 4 * 4 := h1.trans (Nat.mul_le_mul_right 4 h2)
  have h4 : ((bondsOver S {z} i).card : ℝ) ≤ (((F.blockSide ^ (F.top - i)) ^ 4 * 4 : ℕ) : ℝ) := by exact_mod_cast h3
  refine h4.trans (le_of_eq ?_)
  push_cast
  ring
theorem le_pow_four_of_le_rpow_mul {E X : ℝ} (hE : 0 ≤ E) (hX : 0 ≤ X) (h : 3 / 8 * E ≤ E ^ (3 / 4 : ℝ) * X) :
    E ≤ (8 / 3 * X) ^ 4 := by
  rcases hE.eq_or_lt with h0 | hp
  · rw [← h0]
    positivity
  · have e1 : E = E ^ (3 / 4 : ℝ) * E ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_add hp]
      norm_num
    have hq : 0 < E ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hp _
    have h1 : 3 / 8 * E ^ (1 / 4 : ℝ) ≤ X := by
      have h2 : E ^ (3 / 4 : ℝ) * (3 / 8 * E ^ (1 / 4 : ℝ)) ≤ E ^ (3 / 4 : ℝ) * X := by
        calc _ = 3 / 8 * (E ^ (3 / 4 : ℝ) * E ^ (1 / 4 : ℝ)) := by ring
          _ = 3 / 8 * E := by rw [← e1]
          _ ≤ _ := h
      exact le_of_mul_le_mul_left h2 hq
    have h3 : E ^ (1 / 4 : ℝ) ≤ 8 / 3 * X := by linarith
    have h4 := pow_le_pow_left₀ (Real.rpow_nonneg hE _) h3 4
    refine le_trans (le_of_eq ?_) h4
    rw [← Real.rpow_natCast, ← Real.rpow_mul hE]
    norm_num
theorem geom_sum_le_two {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1 / 2) (t : ℕ) : ∑ k ∈ Finset.range t, r ^ k ≤ 2 := by apply _root_.YangMills.Construction.EvaluationSums.geom_sum_le_two <;> assumption
theorem sum_filter_range_le {t j : ℕ} (hjt : j < t) {P Q r : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2)
    (f : ℕ → ℝ) (hft : f t ≤ P) (hfi : ∀ i, j < i → i < t → f i ≤ Q * r ^ (t - 1 - i)) :
    ∑ i ∈ (Finset.range (t + 1)).filter (fun i => j < i), f i ≤ P + 2 * Q := by
  classical
  rw [Finset.range_add_one, Finset.filter_insert, if_pos hjt, Finset.sum_insert (by simp)]
  refine add_le_add hft ?_
  have h1 : ∑ i ∈ (Finset.range t).filter (fun i => j < i), f i ≤ ∑ i ∈ Finset.range t, Q * r ^ (t - 1 - i) := by
    refine le_trans (Finset.sum_le_sum fun i hi => hfi i (Finset.mem_filter.1 hi).2
      (Finset.mem_range.1 (Finset.mem_filter.1 hi).1)) ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => by positivity
  refine h1.trans ?_
  rw [← Finset.mul_sum, Finset.sum_range_reflect (fun k => r ^ k) t]
  have := mul_le_mul_of_nonneg_left (geom_sum_le_two hr0 hr t) hQ
  linarith
theorem top_term_le {Lr hC β q r : ℝ} {m : ℕ} (hm : 1 ≤ m) (hL : 0 ≤ Lr) (hC0 : 0 ≤ hC) (hβ : 0 ≤ β) (hq0 : 0 ≤ q)
    (hqr : q ≤ r) (hr : 0 < r) : 13 * Lr * hC * (11 * (2 * β)) * q ^ (m - 1) ≤ (286 * Lr * hC / r) * β * r ^ m := by
  have h1 : q ^ (m - 1) ≤ r ^ (m - 1) := pow_le_pow_left₀ hq0 hqr _
  have e1 : r ^ m = r ^ (m - 1) * r := by
    rw [← pow_succ]
    congr 1
    omega
  have e2 : (286 * Lr * hC / r) * β * r ^ m = 13 * Lr * hC * (11 * (2 * β)) * r ^ (m - 1) := by
    rw [e1]
    field_simp
    ring
  rw [e2]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)
theorem middle_term_le {ε Lr hC B β q r : ℝ} {k a m b : ℕ} (hk : 2 * k + a = m + b) (hε : 0 ≤ ε) (hL : 0 ≤ Lr)
    (hC0 : 0 ≤ hC) (hq0 : 0 ≤ q) (hqr : q ≤ r) (hr : 0 ≤ r) :
    20 * ε * Lr * hC * (11 * (B * β * r ^ k)) ^ 2 * q ^ a ≤ (20 * ε * Lr * hC * 121 * B ^ 2 * β ^ 2 * r ^ m) * r ^ b := by
  have h1 : q ^ a ≤ r ^ a := pow_le_pow_left₀ hq0 hqr _
  have e1 : (20 * ε * Lr * hC * 121 * B ^ 2 * β ^ 2 * r ^ m) * r ^ b =
      20 * ε * Lr * hC * (11 * (B * β * r ^ k)) ^ 2 * r ^ a := by
    have : r ^ m * r ^ b = r ^ (2 * k) * r ^ a := by
      rw [← pow_add, ← pow_add, hk]
    calc _ = 20 * ε * Lr * hC * 121 * B ^ 2 * β ^ 2 * (r ^ m * r ^ b) := by ring
      _ = 20 * ε * Lr * hC * 121 * B ^ 2 * β ^ 2 * (r ^ (2 * k) * r ^ a) := by rw [this]
      _ = _ := by rw [pow_mul']; ring
  rw [e1]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)
section Down
variable {S : Finset F.Cell} {R : F.FieldChain} {U : ChainChart F} {W : F.GaugeField F.top} {t ρ β s Db B : ℝ}
theorem finLpNorm_referenceDefect_le (hodd : Odd F.blockSide) (hs0 : 0 ≤ s) (hDb : 0 ≤ Db) {j : ℕ} (z : F.Cell) {m : ℕ}
    (hm : j + 1 + m = F.top)
    (hmis : ∀ c ∈ innerBonds S (j + 1), normSubOne (referenceDefect R j c) ≤ Db * s * levelScale F (j + 1) ^ 3) :
    finLpNorm (bondsOver S {z} (j + 1)) 4 (fun c => normSubOne (referenceDefect R j c)) ≤
      2 * Db * s * (4 / (F.blockSide : ℝ) ^ 2) ^ m := by
  have hLr : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  have hnm : F.top - (j + 1) = m := by omega
  set l : ℝ := levelScale F (j + 1) with hl
  have hl' : l = (1 / (F.blockSide : ℝ)) ^ m := by
    rw [hl]
    unfold levelScale
    rw [hnm]
  have hl0 : 0 ≤ l := by rw [hl']; positivity
  set M : ℝ := (F.blockSide : ℝ) ^ m with hM
  have hlM : l * M = 1 := by
    rw [hl', hM, ← mul_pow, one_div, inv_mul_cancel₀ hLr.ne', one_pow]
  have hl2 : l ^ 2 ≤ (4 / (F.blockSide : ℝ) ^ 2) ^ m := by
    rw [hl', ← pow_mul, mul_comm m 2, pow_mul]
    refine pow_le_pow_left₀ (by positivity) ?_ m
    rw [one_div, inv_pow, ← one_div]
    exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
  have h1 : finLpNorm (bondsOver S {z} (j + 1)) 4 (fun c => normSubOne (referenceDefect R j c)) ≤ 2 * Db * s * l ^ 2 := by
    refine finLpNorm_le_of_sum_rpow_le _ (by norm_num) (fun _ _ => norm_nonneg _) (by positivity) ?_
    simp only [rpow_four_eq_pow]
    have h2 : ∀ c ∈ bondsOver S {z} (j + 1), normSubOne (referenceDefect R j c) ^ 4 ≤ (Db * s * l ^ 3) ^ 4 :=
      fun c hc => pow_le_pow_left₀ (norm_nonneg _) (hmis c (Finset.mem_filter.1 hc).1) 4
    refine (Finset.sum_le_sum h2).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hc := card_bondsOver_singleton_le hodd S z (j + 1)
    rw [hnm] at hc
    have h3 := mul_le_mul_of_nonneg_right hc (by positivity : (0 : ℝ) ≤ (Db * s * l ^ 3) ^ 4)
    refine h3.trans ?_
    have e : 4 * M ^ 4 * (Db * s * l ^ 3) ^ 4 = 4 * (Db * s) ^ 4 * l ^ 8 * (l * M) ^ 4 := by ring
    rw [e, hlM, one_pow, mul_one]
    have e2 : (2 * Db * s * l ^ 2) ^ 4 = 16 * (Db * s) ^ 4 * l ^ 8 := by ring
    rw [e2]
    have : 0 ≤ (Db * s) ^ 4 * l ^ 8 := by positivity
    nlinarith
  refine h1.trans ?_
  exact mul_le_mul_of_nonneg_left hl2 (by positivity)
theorem cellMisfit_le_of_finLpNorm_le {j : ℕ} (hj : j + 1 < F.top) (z : F.Cell) {Y : ℝ} (hY0 : 0 ≤ Y)
    (hsum : finLpNorm (bondsOver S {z} (j + 1)) 4 (fun c => ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖) +
      finLpNorm (bondsOver S {z} (j + 1)) 4 (fun c => normSubOne (referenceDefect R j c)) ≤ Y) :
    cellMisfitSum S R U W j 4 z ≤ Y ^ 4 := by
  have h1 : finLpNorm (bondsOver S {z} (j + 1)) 4 (fun c => normSubOne (chartBondMisfit R U W j c)) ≤ Y := by
    have h2 := finLpNorm_mono (bondsOver S {z} (j + 1)) (p := 4) (by norm_num)
      (f := fun c => normSubOne (chartBondMisfit R U W j c))
      (g := fun c => ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ + normSubOne (referenceDefect R j c)) (fun _ _ => norm_nonneg _)
      (fun c _ => by
        rw [blockMisfit_of_lt R U W hj c]
        exact (norm_coe_mul_sub_one_le _ _).trans (add_le_add (norm_exp_sub_one_le (U.coarse j c.1 c.2).2) le_rfl))
    have h3 := finLpNorm_add_le (bondsOver S {z} (j + 1)) (p := 4) (by norm_num)
      (f := fun c => ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖)
      (g := fun c => normSubOne (referenceDefect R j c)) (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _)
    exact h2.trans (h3.trans hsum)
  have h2 := sum_rpow_eq_finLpNorm_rpow (bondsOver S {z} (j + 1)) (p := 4) (by norm_num)
    (f := fun c => normSubOne (chartBondMisfit R U W j c)) (fun _ _ => norm_nonneg _)
  simp only [rpow_four_eq_pow] at h2
  unfold cellMisfitSum
  rw [h2]
  exact pow_le_pow_left₀ (finLpNorm_nonneg _ _ fun _ _ => norm_nonneg _) h1 4
theorem add_le_of_root_bounds {A1 A2 X Dl Db s β K3 Qc B w : ℝ} (hw : 0 ≤ w) (hβ : 0 ≤ β) (hsβ : s ≤ β) (hDb : 0 ≤ Db)
    (h1 : A1 ≤ 8 / 3 * X) (h2 : A2 ≤ 2 * Db * s * w) (hX : X ≤ Dl + (K3 * β * w + 2 * (Qc * w)))
    (hDl : Dl ≤ 2 * Db * s * w) (hBig : 8 / 3 * (2 * Db + K3) + 2 * Db ≤ B / 2) (hsm : 8 / 3 * (2 * Qc) ≤ B / 2 * β) :
    A1 + A2 ≤ B * β * w := by
  have a1 : 2 * Db * s * w ≤ 2 * Db * β * w := by
    have : 0 ≤ 2 * Db * w := by positivity
    nlinarith
  have a2 := mul_le_mul_of_nonneg_right hBig (mul_nonneg hβ hw)
  have a3 := mul_le_mul_of_nonneg_right hsm hw
  nlinarith
theorem cellMisfit_le_all (hodd : Odd F.blockSide) (hL : 4 ≤ F.blockSide) (hs : NearReference S R U t ρ) (ht0 : 0 ≤ t)
    (ht : 2 * F.blockSide * t ≤ 1 / 4) (hρ0 : 0 ≤ ρ) (hε : 17 * F.blockSide * t + ρ ≤ 1 / 2) {a : ℝ} (ha : a ≠ 0)
    (hcrit : ∀ A : ChainChart F, IsStationaryAlong a S R W U A)
    (hβ0 : 0 ≤ β) (hs0 : 0 ≤ s) (hsβ : s ≤ β) (hDb : 0 ≤ Db) (hB : 2 ≤ B) (hβ1 : β ≤ 1)
    (hmu : ∀ i, i + 1 < F.top → ∀ c ∈ innerBonds S (i + 1), ‖(U.coarse i c.1 c.2 : ℍ[ℝ])‖ ≤ β)
    (hmis : ∀ i, i + 1 < F.top → ∀ c ∈ innerBonds S (i + 1),
      normSubOne (referenceDefect R i c) ≤ Db * s * levelScale F (i + 1) ^ 3)
    (htop : ∀ c ∈ innerBonds S F.top, normSubOne (chartBondMisfit R U W F.depth c) ≤ β)
    (hq : 1 / (F.blockSide : ℝ) ^ 2 + 50 * (17 * F.blockSide * t + ρ) * F.blockSide * hullLpConst F.blockSide ≤
      2 / (F.blockSide : ℝ) ^ 2)
    (hBig : 8 / 3 * (2 * Db + 286 * F.blockSide * hullLpConst F.blockSide / (4 / (F.blockSide : ℝ) ^ 2)) + 2 * Db ≤ B / 2)
    (hsm : 8 / 3 * (2 * (20 * (17 * F.blockSide * t + ρ) * F.blockSide * hullLpConst F.blockSide * 121 * B ^ 2 * β ^ 2)) ≤
      B / 2 * β) :
    ∀ (m j : ℕ), j + 1 + m = F.top → ∀ z ∈ S, cellMisfitSum S R U W j 4 z ≤
      (if m = 0 then 2 * β else B * β * (4 / (F.blockSide : ℝ) ^ 2) ^ m) ^ 4 := by
  classical
  have hLpos : 0 < F.blockSide := by omega
  have hL4 : (4 : ℝ) ≤ F.blockSide := by exact_mod_cast hL
  have hn : F.top = F.depth + 1 := rfl
  set r : ℝ := 4 / (F.blockSide : ℝ) ^ 2 with hr
  set q : ℝ := 2 / (F.blockSide : ℝ) ^ 2 with hqd
  have hr0 : 0 < r := by positivity
  have hq0 : 0 ≤ q := by positivity
  have hqr : q ≤ r := div_le_div_of_nonneg_right (by norm_num) (by positivity)
  have hr2 : r ≤ 1 / 2 := by
    rw [hr, div_le_iff₀ (by positivity)]
    nlinarith
  set ε : ℝ := 17 * F.blockSide * t + ρ with hεd
  have hε0 : 0 ≤ ε := by positivity
  set hC := hullLpConst F.blockSide with hhC
  have hC0 : 0 ≤ hC := hullLpConst_nonneg _
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro j hjm z hz
    by_cases hm0 : m = 0
    · subst hm0
      have hjt : j = F.depth := by omega
      subst hjt
      rw [if_pos rfl]
      unfold cellMisfitSum
      have h1 : ∀ c ∈ bondsOver S {z} (F.depth + 1), normSubOne (chartBondMisfit R U W F.depth c) ^ 4 ≤ β ^ 4 :=
        fun c hc => pow_le_pow_left₀ (norm_nonneg _) (htop c (Finset.mem_filter.1 hc).1) 4
      refine (Finset.sum_le_sum h1).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      have hc := card_bondsOver_singleton_le hodd S z (F.depth + 1)
      have e : F.top - (F.depth + 1) = 0 := by omega
      rw [e, pow_zero, one_pow, mul_one] at hc
      have h0 : 0 ≤ β ^ 4 := by positivity
      nlinarith
    · rw [if_neg hm0]
      have hj : j + 1 < F.top := by omega
      have hjt : j < F.depth := by omega
      have hmt : m = F.depth - j := by omega
      set e : ℕ → ℝ := fun i => if F.depth - i = 0 then 2 * β else B * β * r ^ (F.depth - i) with hedef
      have he : ∀ i, 0 ≤ e i := fun i => by
        simp only [hedef]
        split_ifs <;> positivity
      have hG : ∀ i, j < i → i < F.top → ∀ y ∈ S, cellMisfitSum S R U W i 4 y ≤ e i ^ 4 :=
        fun i hji hin y hy => ih (F.depth - i) (by omega) i (by omega) y hy
      have hw : ∀ c ∈ innerBonds S (j + 1), ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ ≤ 1 :=
        fun c hc => (hmu j hj c hc).trans hβ1
      have hsrc := sum_coarse_pow_four_le (S := S) R U j z W hodd hL hs ht0 ht hρ0 hε hj ha (hcrit _) hw e he hG hq
      rw [levelDerivNorm_first R U j z hLpos hodd] at hsrc
      set Ez := ∑ c ∈ bondsOver S {z} (j + 1), ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 4 with hEz
      have hEz0 : 0 ≤ Ez := Finset.sum_nonneg fun _ _ => by positivity
      set Dl := finLpNorm (bondsOver S {z} (j + 1)) 4 (fun c => normSubOne (referenceDefect R j c)) with hDl
      have hDl0 : 0 ≤ Dl := finLpNorm_nonneg _ _ fun _ _ => norm_nonneg _
      have hDlb : Dl ≤ 2 * Db * s * r ^ m := finLpNorm_referenceDefect_le hodd hs0 hDb z (by omega) (hmis j hj)
      set f : ℕ → ℝ := fun i => if i = F.depth then 13 * F.blockSide * hC * (11 * e i) * q ^ (i - (j + 1)) else
        20 * ε * F.blockSide * hC * (11 * e i) ^ 2 * q ^ (i - (j + 1)) with hf
      have hf0 : ∀ i, 0 ≤ f i := fun i => by
        simp only [hf]
        have := he i
        split_ifs <;> positivity
      have hsumf : ∑ i ∈ (Finset.range F.top).filter (fun i => j < i), f i ≤
          (286 * F.blockSide * hC / r) * β * r ^ m + 2 * (20 * ε * F.blockSide * hC * 121 * B ^ 2 * β ^ 2 * r ^ m) := by
        refine sum_filter_range_le (t := F.depth) hjt (by positivity) (by positivity) hr0.le hr2 f ?_ ?_
        · simp only [hf, if_true]
          have e1 : e F.depth = 2 * β := by
            simp [hedef]
          rw [e1]
          have e2 : F.depth - (j + 1) = m - 1 := by omega
          rw [e2]
          exact top_term_le (by omega) (by positivity) hC0 hβ0 hq0 hqr hr0
        · intro i hji hit
          have hne : i ≠ F.depth := by omega
          simp only [hf, if_neg hne]
          have e1 : e i = B * β * r ^ (F.depth - i) := by
            simp only [hedef]
            rw [if_neg (by omega)]
          rw [e1]
          exact middle_term_le (by omega) hε0 (by positivity) hC0 hq0 hqr hr0.le
      set X := Dl + ∑ i ∈ (Finset.range F.top).filter (fun i => j < i), f i with hX
      have hX0 : 0 ≤ X := add_nonneg hDl0 (Finset.sum_nonneg fun i _ => hf0 i)
      have hroot := le_pow_four_of_le_rpow_mul hEz0 hX0 hsrc
      have hlpw : finLpNorm (bondsOver S {z} (j + 1)) 4 (fun c => ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖) ≤ 8 / 3 * X := by
        refine finLpNorm_le_of_sum_rpow_le _ (by norm_num) (fun _ _ => norm_nonneg _) (by positivity) ?_
        simp only [rpow_four_eq_pow]
        exact hroot
      have hXb : X ≤ Dl + ((286 * F.blockSide * hC / r) * β * r ^ m +
          2 * (20 * ε * F.blockSide * hC * 121 * B ^ 2 * β ^ 2 * r ^ m)) := by
        rw [hX]
        linarith
      have hY := add_le_of_root_bounds (w := r ^ m) (by positivity) hβ0 hsβ hDb hlpw hDlb hXb hDlb hBig hsm
      exact cellMisfit_le_of_finLpNorm_le hj z (by positivity) hY
end Down
theorem innerBonds_mem_sitesOfCells {S : Finset F.Cell} {j : ℕ} {c : F.Site j × Fin 4} (hc : c ∈ innerBonds S j) :
    c.1 ∈ sitesOfCells S j ∧ c.1 + unitStep j c.2 ∈ sitesOfCells S j := ChartCoordinates.innerBonds_ends hc
theorem cellMisfit_two_le (hodd : Odd F.blockSide) {S : Finset F.Cell} {R : F.FieldChain} {U : ChainChart F}
    {W : F.GaugeField F.top} {j m : ℕ} (hm : j + 1 + m = F.top) (z : F.Cell) {Y : ℝ} (hY0 : 0 ≤ Y)
    (h4 : cellMisfitSum S R U W j 4 z ≤ Y ^ 4) :
    cellMisfitSum S R U W j 2 z ≤ (2 * ((F.blockSide : ℝ) ^ m * Y)) ^ 2 := by
  have hnm : F.top - (j + 1) = m := by omega
  unfold cellMisfitSum at h4 ⊢
  set A := bondsOver S {z} (j + 1) with hA
  have h1 := sq_sum_le_card_mul_sum_sq (s := A) (f := fun c => normSubOne (chartBondMisfit R U W j c) ^ 2)
  have hc := card_bondsOver_singleton_le hodd S z (j + 1)
  rw [hnm] at hc
  have h2 : ∑ c ∈ A, (normSubOne (chartBondMisfit R U W j c) ^ 2) ^ 2 ≤ Y ^ 4 := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun c _ => ?_)) h4
    ring
  have h3 := mul_le_mul hc h2 (Finset.sum_nonneg fun c _ => by positivity) (by positivity)
  have h5 : (∑ c ∈ A, normSubOne (chartBondMisfit R U W j c) ^ 2) ^ 2 ≤ ((2 * ((F.blockSide : ℝ) ^ m * Y)) ^ 2) ^ 2 := by
    refine h1.trans (h3.trans ?_)
    have e : 4 * ((F.blockSide : ℝ) ^ m) ^ 4 * Y ^ 4 = (2 * ((F.blockSide : ℝ) ^ m * Y) ^ 2) ^ 2 := by ring
    rw [e]
    refine pow_le_pow_left₀ (by positivity) ?_ 2
    nlinarith [sq_nonneg ((F.blockSide : ℝ) ^ m * Y)]
  exact le_of_not_gt fun hlt => absurd h5 (not_le.2 (pow_lt_pow_left₀ hlt (by positivity) (by norm_num)))
theorem ratio_le_of_small {Lr hC Ke ε β : ℝ} (hL : 0 < Lr) (hC0 : 0 ≤ hC) (hε1 : ε ≤ Ke * β)
    (hp : 50 * Ke * Lr * hC * Lr ^ 2 * β ≤ 1) : 1 / Lr ^ 2 + 50 * ε * Lr * hC ≤ 2 / Lr ^ 2 := by
  have h1 : 50 * ε * Lr * hC ≤ 1 / Lr ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have h2 := mul_le_mul_of_nonneg_right hε1 (by positivity : (0 : ℝ) ≤ 50 * Lr * hC * Lr ^ 2)
    nlinarith
  have e : 2 / Lr ^ 2 = 1 / Lr ^ 2 + 1 / Lr ^ 2 := by ring
  rw [e]
  linarith
theorem quadratic_term_le_of_small {Lr hC Ke ε β B : ℝ} (hL : 0 < Lr) (hC0 : 0 ≤ hC) (hK0 : 0 ≤ Ke) (hε1 : ε ≤ Ke * β)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hB0 : 0 ≤ B) (hp : 8 / 3 * 80 * 121 * Ke * Lr * hC * B * β ≤ 1) :
    8 / 3 * (2 * (20 * ε * Lr * hC * 121 * B ^ 2 * β ^ 2)) ≤ B / 2 * β := by
  have hK : 0 ≤ 20 * Lr * hC * 121 * B ^ 2 * β ^ 2 := by positivity
  have h1 := mul_le_mul_of_nonneg_right hε1 hK
  have h3 : (8 / 3 * 80 * 121 * Ke * Lr * hC * B * β) * (B / 2 * β) ≤ 1 * (B / 2 * β) :=
    mul_le_mul_of_nonneg_right hp (by positivity)
  have hββ : β ^ 2 ≤ β := by nlinarith
  have h4 : 8 / 3 * (2 * (Ke * β * (20 * Lr * hC * 121 * B ^ 2 * β ^ 2))) ≤
      (8 / 3 * 80 * 121 * Ke * Lr * hC * B * β) * (B / 2 * β) := by
    have h5 : 0 ≤ 8 / 3 * 40 * 121 * Ke * Lr * hC * B ^ 2 * β ^ 2 := by positivity
    have h6 := mul_le_mul_of_nonneg_left hββ h5
    nlinarith
  have e : 20 * ε * Lr * hC * 121 * B ^ 2 * β ^ 2 = ε * (20 * Lr * hC * 121 * B ^ 2 * β ^ 2) := by ring
  rw [e]
  linarith
theorem norm_coarse_le (hodd : Odd F.blockSide) {S : Finset F.Cell} {R : F.FieldChain} {U : ChainChart F} {β : ℝ}
    (hβ0 : 0 ≤ β) (hN : ∀ z ∈ S, localNorm S R U (oneSiteWeights F) z ≤ β) :
    ∀ i, i + 1 < F.top → ∀ c' ∈ innerBonds S (i + 1), ‖(U.coarse i c'.1 c'.2 : ℍ[ℝ])‖ ≤ β := by
  classical
  intro i hi c' hc'
  have hz : enclosingCell c'.1 ∈ S := enclosingCell_mem hodd (innerBonds_mem_sitesOfCells hc').1
  have h1 := (localNorm_parts_le S R U (oneSiteWeights F) (enclosingCell c'.1) hβ0 (hN _ hz)).2.2 i hi
  have hb' : c' ∈ bondsOver S (cellBall S (enclosingCell c'.1) 3) (i + 1) :=
    Finset.mem_filter.2 ⟨hc', singleton_subset_cellBall hz (by simp)⟩
  have h2 := Finset.single_le_sum (f := fun c : F.Site (i + 1) × Fin 4 =>
    (oneSiteWeights F (i + 1) c.1 * ‖U.coarse i c.1 c.2‖) ^ 2) (fun _ _ => by positivity) hb'
  have h3 := h2.trans h1
  simp only [oneSiteWeights, one_mul] at h3
  exact le_of_not_gt fun hlt => absurd h3 (not_le.2 (pow_lt_pow_left₀ hlt hβ0 (by norm_num)))
theorem normSubOne_chartField_le (hodd : Odd F.blockSide) {S : Finset F.Cell} {R : F.FieldChain} {U : ChainChart F}
    {B0 : ℝ} (hB0 : 0 ≤ B0)
    (h : ∀ z ∈ S, ∀ i, i < F.top → ∑ b ∈ bondsOver S {z} i, normSubOne (chartGap R U i b.1 b.2) ^ 4 ≤ B0 ^ 4) :
    ∀ i, i < F.top → ∀ b ∈ innerBonds S i, normSubOne (chartField R U i b.1 b.2 * (R i b.1 b.2)⁻¹) ≤ B0 := by
  classical
  intro i hi b hb
  have hz : enclosingCell b.1 ∈ S := enclosingCell_mem hodd (innerBonds_mem_sitesOfCells hb).1
  have h1 := h _ hz i hi
  have hb' : b ∈ bondsOver S {enclosingCell b.1} i := Finset.mem_filter.2 ⟨hb, by simp⟩
  have h2 := Finset.single_le_sum (f := fun b : F.Site i × Fin 4 => normSubOne (chartGap R U i b.1 b.2) ^ 4)
    (fun _ _ => by positivity) hb'
  exact le_of_not_gt fun hlt => absurd (h2.trans h1) (not_le.2 (pow_lt_pow_left₀ hlt hB0 (by norm_num)))
theorem cellMisfit_bounds (hodd : Odd F.blockSide) {S : Finset F.Cell} {R : F.FieldChain} {U : ChainChart F}
    {W : F.GaugeField F.top} {B β : ℝ} (hB : 2 ≤ B) (hβ0 : 0 ≤ β)
    (hall : ∀ (m j : ℕ), j + 1 + m = F.top → ∀ z ∈ S, cellMisfitSum S R U W j 4 z ≤
      (if m = 0 then 2 * β else B * β * (4 / (F.blockSide : ℝ) ^ 2) ^ m) ^ 4) {j : ℕ} (z : F.Cell) (hj : j < F.top) :
    cellMisfitSum S R U W j 4 z ≤ (4 * B * β * (4 / (F.blockSide : ℝ) ^ 2) ^ (F.top - 1 - j)) ^ 4 ∧
      cellMisfitSum S R U W j 2 z ≤ (4 * B * β * (4 / (F.blockSide : ℝ)) ^ (F.top - 1 - j)) ^ 2 := by
  have hLr : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  obtain ⟨m', hm'⟩ : ∃ m', j + 1 + m' = F.top := ⟨F.top - 1 - j, by omega⟩
  have e0 : F.top - 1 - j = m' := by omega
  rw [e0]
  have hr0 : 0 ≤ (4 / (F.blockSide : ℝ) ^ 2) ^ m' := by positivity
  have hB0 : 0 ≤ B := by linarith
  have hY : cellMisfitSum S R U W j 4 z ≤ (2 * B * β * (4 / (F.blockSide : ℝ) ^ 2) ^ m') ^ 4 := by
    by_cases hz : z ∈ S
    · have h1 := hall m' j hm' z hz
      refine h1.trans (pow_le_pow_left₀ (by split_ifs <;> positivity) ?_ 4)
      split_ifs with h0
      · rw [h0]
        simp only [pow_zero, mul_one]
        nlinarith
      · nlinarith [mul_nonneg (mul_nonneg hB0 hβ0) hr0]
    · have h0 : cellMisfitSum S R U W j 4 z = 0 := by
        unfold cellMisfitSum
        refine Finset.sum_eq_zero fun c' hc' => ?_
        exfalso
        obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hc'
        apply hz
        rw [← Finset.mem_singleton.1 h2]
        exact enclosingCell_mem hodd (innerBonds_mem_sitesOfCells h1).1
      rw [h0]
      positivity
  refine ⟨hY.trans (pow_le_pow_left₀ (by positivity) ?_ 4), ?_⟩
  · have : 0 ≤ B * β * (4 / (F.blockSide : ℝ) ^ 2) ^ m' := by positivity
    nlinarith
  · have h2 := cellMisfit_two_le hodd hm' z (by positivity) hY
    refine h2.trans (le_of_eq ?_)
    have e1 : (F.blockSide : ℝ) ^ m' * (4 / (F.blockSide : ℝ) ^ 2) ^ m' = (4 / (F.blockSide : ℝ)) ^ m' := by
      rw [← mul_pow]
      congr 1
      field_simp
    have e2 : 2 * ((F.blockSide : ℝ) ^ m' * (2 * B * β * (4 / (F.blockSide : ℝ) ^ 2) ^ m')) =
        4 * B * β * ((F.blockSide : ℝ) ^ m' * (4 / (F.blockSide : ℝ) ^ 2) ^ m') := by ring
    rw [e2, e1]
theorem misfitDecayDownLevels (hGaps : levelGapNearCellStatement) (hB : referenceBoundsStatement) :
    misfitDecayDownLevelsStatement := by
  obtain ⟨Cg, hCg, Lg, hGaps⟩ := hGaps
  obtain ⟨Db, cb, L1, hDb, hcb, hBd⟩ := hB
  intro a ha
  refine ⟨max (max Lg L1) 5, fun L hL hge => ?_⟩
  have hLg : Lg ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hge)
  have hL1 : L1 ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hge)
  have hL5 : 5 ≤ L := (le_max_right _ _).trans hge
  obtain ⟨cg, hcg, hGL⟩ := hGaps L hL hLg
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL.pos
  obtain ⟨hC, hC0, hhC⟩ : ∃ hC : ℝ, 0 ≤ hC ∧ hC = hullLpConst L := ⟨_, hullLpConst_nonneg L, rfl⟩
  obtain ⟨Ke, hKe0, hKe⟩ : ∃ Ke : ℝ, 0 ≤ Ke ∧ Ke = 17 * L * Cg + Db := ⟨_, by positivity, rfl⟩
  obtain ⟨B, hB2, hBig⟩ : ∃ B : ℝ, 2 ≤ B ∧ 8 / 3 * (2 * Db + 286 * L * hC / (4 / (L : ℝ) ^ 2)) + 2 * Db ≤ B / 2 := by
    have h0 : 0 ≤ 8 / 3 * (2 * Db + 286 * L * hC / (4 / (L : ℝ) ^ 2)) + 2 * Db := by positivity
    exact ⟨2 + 2 * (8 / 3 * (2 * Db + 286 * L * hC / (4 / (L : ℝ) ^ 2)) + 2 * Db), by linarith, by linarith⟩
  have hB0 : 0 ≤ B := by linarith
  obtain ⟨c, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7⟩ : ∃ c : ℝ, 0 < c ∧ c ≤ cg ∧ c ≤ cb ∧ c ≤ 1 ∧ 8 * L * Cg * c ≤ 1 ∧
      2 * Ke * c ≤ 1 ∧ 50 * Ke * L * hC * (L : ℝ) ^ 2 * c ≤ 1 ∧ 8 / 3 * 80 * 121 * Ke * L * hC * B * c ≤ 1 := by
    obtain ⟨D, hD1, hDdef⟩ : ∃ D : ℝ, 1 ≤ D ∧ D = 1 + (8 * L * Cg + 2 * Ke + 50 * Ke * L * hC * (L : ℝ) ^ 2 +
        8 / 3 * 80 * 121 * Ke * L * hC * B) := by
      refine ⟨_, ?_, rfl⟩
      have : 0 ≤ 8 * L * Cg + 2 * Ke + 50 * Ke * L * hC * (L : ℝ) ^ 2 + 8 / 3 * 80 * 121 * Ke * L * hC * B := by
        positivity
      linarith
    have hD0 : 0 < D := by linarith
    have hz : 0 < min (min cg cb) (1 / D) := lt_min (lt_min hcg hcb) (by positivity)
    have hzD : D * min (min cg cb) (1 / D) ≤ 1 := by
      have h1 : min (min cg cb) (1 / D) ≤ 1 / D := min_le_right _ _
      have := mul_le_mul_of_nonneg_left h1 hD0.le
      rwa [mul_one_div_cancel hD0.ne'] at this
    set y := min (min cg cb) (1 / D) with hy
    rw [hDdef] at hzD
    have p1 : 0 ≤ 8 * L * Cg * y := by positivity
    have p2 : 0 ≤ 2 * Ke * y := by positivity
    have p3 : 0 ≤ 50 * Ke * L * hC * (L : ℝ) ^ 2 * y := by positivity
    have p4 : 0 ≤ 8 / 3 * 80 * 121 * Ke * L * hC * B * y := by positivity
    exact ⟨y, hz, (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  refine ⟨c, 4 * B, hc0, by positivity, ?_⟩
  intro F m S hFL hamb hm hreg s V W hs0 hsc hcold U β hsβ hβc hN htop hcrit j z hj
  subst hFL
  have hodd : Odd F.blockSide := hL
  have hLpos : 0 < F.blockSide := hodd.pos
  have hL1r : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hLpos
  have hLr' : (0 : ℝ) < F.blockSide := hLr
  obtain ⟨-, -, b3, -, b5, -⟩ := hBd F m S hodd hL1 hamb hm hreg s V hs0 (hsc.trans hc2) hcold
  have hβ0 : 0 ≤ β := hs0.le.trans hsβ
  have hβ1 : β ≤ 1 := hβc.trans hc3
  have hgap := normSubOne_chartField_le hodd (B0 := Cg * β) (by positivity) fun z hz i hi =>
    (hGL F m S rfl hamb hm hreg s V hs0 (hsc.trans hc1) hcold U z β hz hβ0 (hβc.trans hc1) (hN z hz) i hi).2
  have hs : NearReference S (referenceFieldChain S V) U (Cg * β) (Db * s) := by
    refine ⟨hgap, fun i hi c' hc' => ?_⟩
    refine ⟨polarUnit (contourAverage (referenceFieldChain S V i) c'), fun h hh π => ?_⟩
    have h1 := b5 i hi c' hc' h hh π
    refine h1.trans ?_
    have hl : levelScale F (i + 1) ^ 2 ≤ 1 := by
      unfold levelScale
      exact pow_le_one₀ (by positivity)
        (pow_le_one₀ (by positivity) (by rw [one_div]; exact inv_le_one_of_one_le₀ hL1r))
    exact mul_le_of_le_one_right (by positivity) hl
  have hε1 : 17 * (F.blockSide : ℝ) * (Cg * β) + Db * s ≤ Ke * β := by
    rw [hKe]
    have := mul_le_mul_of_nonneg_left hsβ hDb.le
    nlinarith
  have hmul : ∀ {x : ℝ}, 0 ≤ x → x * c ≤ 1 → x * β ≤ 1 := fun hx h => (mul_le_mul_of_nonneg_left hβc hx).trans h
  have h8 : 8 * (F.blockSide : ℝ) * Cg * β ≤ 1 := hmul (by positivity) hc4
  have h2K : 2 * Ke * β ≤ 1 := hmul (by positivity) hc5
  have hall := cellMisfit_le_all (R := referenceFieldChain S V) (W := W) (Db := Db) (B := B) hodd (by omega) hs
    (by positivity) (by nlinarith) (by positivity) (by nlinarith) ha.ne' hcrit hβ0 hs0.le hsβ hDb.le hB2 hβ1
    (norm_coarse_le hodd hβ0 hN) (fun i hi c' hc' => b3 i hi c' hc') htop
    (by rw [← hhC]; exact ratio_le_of_small hLr' hC0 hε1 (hmul (by positivity) hc6)) (by rw [← hhC]; exact hBig)
    (by rw [← hhC]; exact quadratic_term_le_of_small hLr' hC0 hKe0 hε1 hβ0 hβ1 hB0 (hmul (by positivity) hc7))
  exact cellMisfit_bounds hodd hB2 hβ0 hall z hj
end YangMills.Construction.MisfitDecay
end
