import YangMills.Construction.ColdChainAtEveryLevel.SumsAlongAMisfit
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.VariationDecay
open BlockAverages BlockLines BondHull BondVariation MisfitVariation NearCellNorms MisfitSums
variable {F : BlockFrame}
theorem sum_mul_le_finLpNorm_mul {ι : Type} (A : Finset ι) {f g : ι → ℝ} (hf : ∀ i ∈ A, 0 ≤ f i)
    (hg : ∀ i ∈ A, 0 ≤ g i) :
    ∑ i ∈ A, f i * g i ≤ finLpNorm A (4 / 3) f * finLpNorm A 4 g := by
  have h := finLpNorm_mul_le A (a := 4 / 3) (b := 4) (c := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hf hg
  have e : finLpNorm A 1 (fun i => f i * g i) = ∑ i ∈ A, f i * g i := by
    unfold finLpNorm
    simp
  rwa [e] at h
theorem finLpNorm_mono_set {ι : Type} {A B : Finset ι} (hAB : A ⊆ B) {f : ι → ℝ} (hf : ∀ i ∈ B, 0 ≤ f i) {p : ℝ}
    (hp : 0 < p) : finLpNorm A p f ≤ finLpNorm B p f := by
  unfold finLpNorm
  refine Real.rpow_le_rpow (Finset.sum_nonneg fun i hi => Real.rpow_nonneg (hf i (hAB hi)) _) ?_ (by positivity)
  exact Finset.sum_le_sum_of_subset_of_nonneg hAB fun i hi _ => Real.rpow_nonneg (hf i hi) _
theorem pow_three_rpow_four_thirds {x : ℝ} (hx : 0 ≤ x) : (x ^ 3) ^ (4 / 3 : ℝ) = x ^ 4 := by
  rw [← Real.rpow_natCast x 3, ← Real.rpow_mul hx, ← Real.rpow_natCast x 4]
  norm_num
theorem rpow_four_eq_pow (x : ℝ) : x ^ (4 : ℝ) = x ^ 4 := by
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
section Fixed
variable (R : F.FieldChain) (U : ChainChart F) (j : ℕ) (z : F.Cell) {S : Finset F.Cell} {i : ℕ} {t ρ : ℝ}
theorem finLpNorm_hullDerivSum_le (hodd : Odd F.blockSide) (hi : i < F.top) :
    finLpNorm (innerBonds S (i + 1)) (4 / 3) (fun c => hullDerivSum R U j z i c) ≤
      hullLpConst F.blockSide * levelDerivNorm R U j z S i := by
  have hp : (0 : ℝ) < 4 / 3 := by norm_num
  set d : F.Site i × Fin 4 → ℝ := fun b => linkDerivNorm R U j z i b.1 b.2 with hd
  have hd0 : ∀ b, 0 ≤ d b := fun b => linkDerivNorm_nonneg _ _ _ _ _ _ _
  refine finLpNorm_le_of_sum_rpow_le _ hp (fun c _ => hullDerivSum_nonneg _ _ _ _ _ _)
    (mul_nonneg (hullLpConst_nonneg _) (levelDerivNorm_nonneg _ _ _ _ _)) ?_
  have h1 : ∀ c ∈ innerBonds S (i + 1), hullDerivSum R U j z i c ^ (4 / 3 : ℝ) ≤
      ((4 * (hullBox F.blockSide).card : ℕ) : ℝ) ^ ((4 / 3 : ℝ) - 1) * hullSum (fun b => d b ^ (4 / 3 : ℝ)) c :=
    fun c _ => hullSum_rpow_le d hd0 c
  refine (Finset.sum_le_sum h1).trans ?_
  rw [← Finset.mul_sum]
  have h2 := sum_hullSum_le hi hodd (innerBonds S (i + 1)) subset_rfl (fun b => d b ^ (4 / 3 : ℝ))
    (fun b => Real.rpow_nonneg (hd0 b) _)
  have h3 := mul_le_mul_of_nonneg_left h2
    (by positivity : (0 : ℝ) ≤ ((4 * (hullBox F.blockSide).card : ℕ) : ℝ) ^ ((4 / 3 : ℝ) - 1))
  refine h3.trans (le_of_eq ?_)
  rw [Real.mul_rpow (hullLpConst_nonneg _) (levelDerivNorm_nonneg _ _ _ _ _)]
  have e1 : levelDerivNorm R U j z S i ^ (4 / 3 : ℝ) = ∑ b ∈ innerBonds S i, d b ^ (4 / 3 : ℝ) :=
    (sum_rpow_eq_finLpNorm_rpow _ hp fun b _ => hd0 b).symm
  have e2 : hullLpConst F.blockSide ^ (4 / 3 : ℝ) =
      ((4 * (hullBox F.blockSide).card : ℕ) : ℝ) ^ ((4 / 3 : ℝ) - 1) * (16 * ((hullBox F.blockSide).card : ℝ)) := by
    unfold hullLpConst
    rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hp.ne', Real.rpow_one]
  rw [e1, e2]
  ring
theorem finLpNorm_lineBlockAverage_le (hodd : Odd F.blockSide) (hi : i < F.top) :
    finLpNorm (innerBonds S (i + 1)) (4 / 3) (fun c => lineBlockAverage (linkDerivNorm R U j z i) c) ≤
      (1 / (F.blockSide : ℝ) ^ 2) * levelDerivNorm R U j z S i := by
  have hp : (0 : ℝ) < 4 / 3 := by norm_num
  have hLr : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  have hd0 : ∀ x k, 0 ≤ linkDerivNorm R U j z i x k := fun x k => linkDerivNorm_nonneg _ _ _ _ _ _ _
  refine finLpNorm_le_of_sum_rpow_le _ hp (fun c _ => lineBlockAverage_nonneg hd0 c)
    (mul_nonneg (by positivity) (levelDerivNorm_nonneg _ _ _ _ _)) ?_
  have h1 := sum_lineBlockAverage_rpow_le hi hodd (innerBonds S (i + 1)) subset_rfl (linkDerivNorm R U j z i) hd0
    (p := 4 / 3) (by norm_num)
  refine h1.trans (le_of_eq ?_)
  rw [Real.mul_rpow (by positivity) (levelDerivNorm_nonneg _ _ _ _ _)]
  have e1 : levelDerivNorm R U j z S i ^ (4 / 3 : ℝ) =
      ∑ b ∈ innerBonds S i, linkDerivNorm R U j z i b.1 b.2 ^ (4 / 3 : ℝ) :=
    (sum_rpow_eq_finLpNorm_rpow _ hp fun b _ => hd0 b.1 b.2).symm
  have e2 : (1 / (F.blockSide : ℝ) ^ 2) ^ (4 / 3 : ℝ) = (F.blockSide : ℝ) ^ ((4 / 3 : ℝ) - 4) := by
    rw [one_div, ← Real.rpow_natCast (F.blockSide : ℝ) 2, Real.inv_rpow (by positivity), ← Real.rpow_mul hLr.le,
      ← Real.rpow_neg hLr.le]
    congr 1
    push_cast
    ring
  rw [e1, e2]
theorem levelDerivNorm_succ_le_mul (hodd : Odd F.blockSide) (hs : NearReference S R U t ρ) (ht0 : 0 ≤ t)
    (ht : 2 * F.blockSide * t ≤ 1 / 4) (hρ0 : 0 ≤ ρ) (hε : 17 * F.blockSide * t + ρ ≤ 1 / 2) (hji : j < i)
    (hi : i + 1 < F.top) :
    levelDerivNorm R U j z S (i + 1) ≤
      (1 / (F.blockSide : ℝ) ^ 2 + 50 * (17 * F.blockSide * t + ρ) * F.blockSide * hullLpConst F.blockSide) *
        levelDerivNorm R U j z S i := by
  have hp : (0 : ℝ) < 4 / 3 := by norm_num
  have hin : i < F.top := by omega
  have hLr : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  have hreg := hs.chartIsRegular hodd ht0 ht hρ0 hε
  have hd0 : ∀ x k, 0 ≤ linkDerivNorm R U j z i x k := fun x k => linkDerivNorm_nonneg _ _ _ _ _ _ _
  set K := 50 * (17 * (F.blockSide : ℝ) * t + ρ) * F.blockSide with hK
  have hK0 : 0 ≤ K := by positivity
  have h1 : levelDerivNorm R U j z S (i + 1) ≤ finLpNorm (innerBonds S (i + 1)) (4 / 3)
      (fun c => lineBlockAverage (linkDerivNorm R U j z i) c + K * hullDerivSum R U j z i c) := by
    refine finLpNorm_mono _ hp (fun _ _ => linkDerivNorm_nonneg _ _ _ _ _ _ _) fun c hc => ?_
    obtain ⟨v, hv⟩ := hs.contour_near i hin c hc
    exact linkDerivNorm_succ_le R U j z hodd hreg hji hi hc v ht0 ht hρ0 hε (hs.hull_le hodd hin hc) hv
  have h2 := finLpNorm_add_le (innerBonds S (i + 1)) (p := 4 / 3) (by norm_num)
    (f := fun c => lineBlockAverage (linkDerivNorm R U j z i) c)
    (g := fun c => K * hullDerivSum R U j z i c) (fun c _ => lineBlockAverage_nonneg hd0 c)
    (fun c _ => mul_nonneg hK0 (hullDerivSum_nonneg _ _ _ _ _ _))
  have h3 := finLpNorm_const_mul (innerBonds S (i + 1)) hp hK0 (f := fun c => hullDerivSum R U j z i c)
    (fun c _ => hullDerivSum_nonneg _ _ _ _ _ _)
  have h4 := finLpNorm_lineBlockAverage_le (S := S) R U j z hodd hin
  have h5 := mul_le_mul_of_nonneg_left (finLpNorm_hullDerivSum_le (S := S) R U j z hodd hin) hK0
  calc _ ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ (1 / (F.blockSide : ℝ) ^ 2) * levelDerivNorm R U j z S i +
        K * (hullLpConst F.blockSide * levelDerivNorm R U j z S i) := by
        rw [h3]
        exact add_le_add h4 h5
    _ = _ := by ring
theorem levelDerivNorm_le_pow (hodd : Odd F.blockSide) (hs : NearReference S R U t ρ) (ht0 : 0 ≤ t)
    (ht : 2 * F.blockSide * t ≤ 1 / 4) (hρ0 : 0 ≤ ρ) (hε : 17 * F.blockSide * t + ρ ≤ 1 / 2) {q : ℝ}
    (hq : 1 / (F.blockSide : ℝ) ^ 2 + 50 * (17 * F.blockSide * t + ρ) * F.blockSide * hullLpConst F.blockSide ≤ q) :
    ∀ m, j + 1 + m < F.top → levelDerivNorm R U j z S (j + 1 + m) ≤ q ^ m * levelDerivNorm R U j z S (j + 1) := by
  have hLr : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  have hq0 : 0 ≤ q := le_trans (add_nonneg (by positivity)
    (mul_nonneg (by positivity) (hullLpConst_nonneg _))) hq
  intro m
  induction m with
  | zero =>
    intro _
    simp
  | succ m ih =>
    intro hm
    have h1 := levelDerivNorm_succ_le_mul (S := S) R U j z hodd hs ht0 ht hρ0 hε (i := j + 1 + m) (by omega) (by omega)
    have h2 := ih (by omega)
    have h3 := mul_le_mul_of_nonneg_right hq (levelDerivNorm_nonneg R U j z (S := S) (j + 1 + m))
    calc levelDerivNorm R U j z S (j + 1 + (m + 1)) = levelDerivNorm R U j z S (j + 1 + m + 1) := rfl
      _ ≤ _ := h1
      _ ≤ q * levelDerivNorm R U j z S (j + 1 + m) := h3
      _ ≤ q * (q ^ m * levelDerivNorm R U j z S (j + 1)) := mul_le_mul_of_nonneg_left h2 hq0
      _ = _ := by ring
variable (W : F.GaugeField F.top)
theorem sum_misfit_pow_four_le {e : ℝ} (he : 0 ≤ e) (hG : ∀ y ∈ S, cellMisfitSum S R U W i 4 y ≤ e ^ 4) :
    ∑ c ∈ bondsOver S (cellBall S z 5) (i + 1), normSubOne (chartBondMisfit R U W i c) ^ 4 ≤ (11 * e) ^ 4 := by
  classical
  have hmaps : ∀ c ∈ bondsOver S (cellBall S z 5) (i + 1), enclosingCell c.1 ∈ cellBall S z 5 :=
    fun c hc => (Finset.mem_filter.1 hc).2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have h1 : ∀ y ∈ cellBall S z 5, ∑ c ∈ bondsOver S (cellBall S z 5) (i + 1) with enclosingCell c.1 = y,
      normSubOne (chartBondMisfit R U W i c) ^ 4 ≤ e ^ 4 := by
    intro y hy
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (t := bondsOver S {y} (i + 1)) ?_
      fun _ _ _ => by positivity) (hG y (Finset.mem_filter.1 hy).1)
    intro c hc
    obtain ⟨h2, h3⟩ := Finset.mem_filter.1 hc
    exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 h2).1, by simp [h3]⟩
  refine (Finset.sum_le_sum h1).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hc : ((cellBall S z 5).card : ℝ) ≤ 14641 := by exact_mod_cast card_cellBall_five S z
  have h0 : 0 ≤ e ^ 4 := by positivity
  nlinarith
theorem finLpNorm_misfit_le {e : ℝ} (he : 0 ≤ e) (hG : ∀ y ∈ S, cellMisfitSum S R U W i 4 y ≤ e ^ 4) :
    finLpNorm (bondsOver S (cellBall S z 5) (i + 1)) 4 (fun c => normSubOne (chartBondMisfit R U W i c)) ≤ 11 * e := by
  refine finLpNorm_le_of_sum_rpow_le _ (by norm_num) (fun _ _ => norm_nonneg _) (by positivity) ?_
  simp only [rpow_four_eq_pow]
  exact sum_misfit_pow_four_le R U z W he hG
theorem finLpNorm_misfit_sq_le {e : ℝ} (he : 0 ≤ e) (hG : ∀ y ∈ S, cellMisfitSum S R U W i 4 y ≤ e ^ 4) :
    finLpNorm (bondsOver S (cellBall S z 5) (i + 1)) 4 (fun c => normSubOne (chartBondMisfit R U W i c) ^ 2) ≤
      (11 * e) ^ 2 := by
  refine finLpNorm_le_of_sum_rpow_le _ (by norm_num) (fun _ _ => by positivity) (by positivity) ?_
  simp only [rpow_four_eq_pow]
  have h1 := sum_misfit_pow_four_le R U z W he hG
  set g : F.Site (i + 1) × Fin 4 → ℝ := fun c => normSubOne (chartBondMisfit R U W i c) ^ 4 with hg
  have hg0 : ∀ c, 0 ≤ g c := fun c => by positivity
  have h2 : ∑ c ∈ bondsOver S (cellBall S z 5) (i + 1), g c ^ 2 ≤
      (∑ c ∈ bondsOver S (cellBall S z 5) (i + 1), g c) ^ 2 := by
    rw [sq (∑ c ∈ bondsOver S (cellBall S z 5) (i + 1), g c), Finset.sum_mul]
    refine Finset.sum_le_sum fun c hc => ?_
    rw [sq]
    exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun c _ => hg0 c) hc) (hg0 c)
  have h3 := pow_le_pow_left₀ (Finset.sum_nonneg fun c _ => hg0 c) h1 2
  have e1 : ∑ c ∈ bondsOver S (cellBall S z 5) (i + 1), (normSubOne (chartBondMisfit R U W i c) ^ 2) ^ 4 =
      ∑ c ∈ bondsOver S (cellBall S z 5) (i + 1), g c ^ 2 := by
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [hg]
    ring
  rw [e1]
  refine h2.trans (h3.trans (le_of_eq ?_))
  ring
theorem sum_mul_hullDerivSum_le (hodd : Odd F.blockSide) (hL : 4 ≤ F.blockSide) (hi : j + 1 ≤ i) (hin : i < F.top)
    (g : F.Site (i + 1) × Fin 4 → ℝ) (hg : ∀ c, 0 ≤ g c) {B : ℝ}
    (hB : finLpNorm (bondsOver S (cellBall S z 5) (i + 1)) 4 g ≤ B) :
    ∑ c ∈ innerBonds S (i + 1), g c * hullDerivSum R U j z i c ≤
      (hullLpConst F.blockSide * levelDerivNorm R U j z S i) * B := by
  classical
  have hsub : bondsOver S (cellBall S z 5) (i + 1) ⊆ innerBonds S (i + 1) := Finset.filter_subset _ _
  have e : ∑ c ∈ innerBonds S (i + 1), g c * hullDerivSum R U j z i c =
      ∑ c ∈ bondsOver S (cellBall S z 5) (i + 1), hullDerivSum R U j z i c * g c := by
    rw [← Finset.sum_subset hsub]
    · exact Finset.sum_congr rfl fun c _ => mul_comm _ _
    · intro c hc hc'
      have h1 : enclosingCell c.1 ∉ cellBall S z 5 := fun h => hc' (Finset.mem_filter.2 ⟨hc, h⟩)
      rw [hullDerivSum_eq_zero_of_not_mem R U j z hodd hL hi hin hc h1, mul_zero]
  rw [e]
  have h1 := sum_mul_le_finLpNorm_mul (bondsOver S (cellBall S z 5) (i + 1)) (f := fun c => hullDerivSum R U j z i c)
    (g := g) (fun _ _ => hullDerivSum_nonneg _ _ _ _ _ _) (fun c _ => hg c)
  refine h1.trans ?_
  have h2 := finLpNorm_mono_set hsub (f := fun c => hullDerivSum R U j z i c) (fun _ _ => hullDerivSum_nonneg _ _ _ _ _ _)
    (by norm_num : (0 : ℝ) < 4 / 3)
  have h3 := h2.trans (finLpNorm_hullDerivSum_le (S := S) R U j z hodd hin)
  exact mul_le_mul h3 hB (finLpNorm_nonneg _ _ fun c _ => hg c)
    (mul_nonneg (hullLpConst_nonneg _) (levelDerivNorm_nonneg _ _ _ _ _))
theorem levelDerivNorm_first (hL : 0 < F.blockSide) (hodd : Odd F.blockSide) :
    levelDerivNorm R U j z S (j + 1) =
      (∑ c ∈ bondsOver S {z} (j + 1), ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 4) ^ (3 / 4 : ℝ) := by
  classical
  unfold levelDerivNorm finLpNorm
  have e1 : (1 / (4 / 3 : ℝ)) = 3 / 4 := by norm_num
  rw [e1]
  congr 1
  have hsub : bondsOver S {z} (j + 1) ⊆ innerBonds S (j + 1) := Finset.filter_subset _ _
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun c hc => ?_
    have hcz : enclosingCell c.1 = z := Finset.mem_singleton.1 (Finset.mem_filter.1 hc).2
    show linkDerivNorm R U j z (j + 1) c.1 c.2 ^ (4 / 3 : ℝ) = _
    rw [linkDerivNorm_of_mem R U j z hcz, pow_three_rpow_four_thirds (norm_nonneg _)]
  · intro c hc hc'
    have hcz : enclosingCell c.1 ≠ z := fun h => hc' (Finset.mem_filter.2 ⟨hc, by simp [h]⟩)
    show linkDerivNorm R U j z (j + 1) c.1 c.2 ^ (4 / 3 : ℝ) = _
    rw [linkDerivNorm_of_not_mem R U j z hcz, Real.zero_rpow (by norm_num)]
theorem sum_coarse_pow_four_le (hodd : Odd F.blockSide) (hL : 4 ≤ F.blockSide) (hs : NearReference S R U t ρ)
    (ht0 : 0 ≤ t) (ht : 2 * F.blockSide * t ≤ 1 / 4) (hρ0 : 0 ≤ ρ) (hε : 17 * F.blockSide * t + ρ ≤ 1 / 2)
    (hj : j + 1 < F.top) {a : ℝ} (ha : a ≠ 0) (hcrit : IsStationaryAlong a S R W U (selfScaledDirection U j z))
    (hw : ∀ c ∈ innerBonds S (j + 1), ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ ≤ 1)
    (e : ℕ → ℝ) (he : ∀ i, 0 ≤ e i)
    (hG : ∀ i, j < i → i < F.top → ∀ y ∈ S, cellMisfitSum S R U W i 4 y ≤ e i ^ 4) {q : ℝ}
    (hq : 1 / (F.blockSide : ℝ) ^ 2 + 50 * (17 * F.blockSide * t + ρ) * F.blockSide * hullLpConst F.blockSide ≤ q) :
    3 / 8 * ∑ c ∈ bondsOver S {z} (j + 1), ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 4 ≤ levelDerivNorm R U j z S (j + 1) *
      (finLpNorm (bondsOver S {z} (j + 1)) 4 (fun c => normSubOne (referenceDefect R j c)) +
        ∑ i ∈ (Finset.range F.top).filter (fun i => j < i),
          (if i = F.depth then
            13 * F.blockSide * hullLpConst F.blockSide * (11 * e i) * q ^ (i - (j + 1)) else
            20 * (17 * F.blockSide * t + ρ) * F.blockSide * hullLpConst F.blockSide * (11 * e i) ^ 2 *
              q ^ (i - (j + 1)))) := by
  classical
  have hLpos : 0 < F.blockSide := by omega
  have hreg := hs.chartIsRegular hodd ht0 ht hρ0 hε
  set ε := 17 * (F.blockSide : ℝ) * t + ρ with hεdef
  set hC := hullLpConst F.blockSide with hhC
  have hC0 : 0 ≤ hC := hullLpConst_nonneg _
  set l1 := levelDerivNorm R U j z S (j + 1) with hl1
  set D : ℕ → ℝ := fun i => ∑ c ∈ innerBonds S (i + 1), deriv (fun τ => fitAlong R U j z W i τ c) 0 with hD
  have hsum := sum_deriv_fitAlong_eq_zero (S := S) R U j z W hodd hreg ha hcrit
  have hsplit : ∑ i ∈ Finset.range F.top, D i = D j + ∑ i ∈ (Finset.range F.top).filter (fun i => j < i), D i := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range F.top) (fun i => j < i)]
    rw [add_comm]
    congr 1
    refine Finset.sum_eq_single_of_mem j (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), by omega⟩) ?_
    intro i hi hij
    have hi' := (Finset.mem_filter.1 hi).2
    have hlt : i < j := by omega
    exact Finset.sum_eq_zero fun c _ => deriv_fitAlong_of_lt R U j z W hlt (by omega) c
  have hDj : 3 / 8 * ∑ c ∈ bondsOver S {z} (j + 1), ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 4 -
      l1 * finLpNorm (bondsOver S {z} (j + 1)) 4 (fun c => normSubOne (referenceDefect R j c)) ≤ D j := by
    have hsub : bondsOver S {z} (j + 1) ⊆ innerBonds S (j + 1) := Finset.filter_subset _ _
    have e0 : D j = ∑ c ∈ bondsOver S {z} (j + 1), deriv (fun τ => fitAlong R U j z W j τ c) 0 := by
      refine (Finset.sum_subset hsub ?_).symm
      intro c hc hc'
      have hcz : enclosingCell c.1 ≠ z := fun h => hc' (Finset.mem_filter.2 ⟨hc, by simp [h]⟩)
      exact deriv_fitAlong_of_not_mem R U j z W hj hcz
    have hbelow : ∀ c ∈ bondsOver S {z} (j + 1), 3 / 8 * ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 4 -
        ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 3 * normSubOne (referenceDefect R j c) ≤
          deriv (fun τ => fitAlong R U j z W j τ c) 0 := by
      intro c hc
      have hcS := hsub hc
      have hcz : enclosingCell c.1 = z := Finset.mem_singleton.1 (Finset.mem_filter.1 hc).2
      obtain ⟨v, hv⟩ := hs.contour_near j (by omega) c hcS
      obtain ⟨-, -, -, -, f5⟩ := bond_estimates_of_near hodd (by omega) (chartField R U j) (R j) c v ht0 ht
        (hs.hull_le hodd (by omega) hcS) hv
      have hnear := norm_gaugedContourAverage_sub_le hodd (by omega) (chartField R U j) (R j) c (v : ℍ[ℝ]) f5
      obtain ⟨-, hlow, -⟩ := normalize_near (norm_coe_unitQuaternion v) hnear hε
      have hr1 : ‖gaugedContourAverage (chartField R U j) (balancingGauge (chartField R U j) (R j)) c‖ ≤ 1 := by
        rw [gaugedContourAverage_balancingGauge_eq (by omega)]
        exact norm_smul_sum_perm_le hodd _ _ fun h _ π => (norm_coe_unitQuaternion _).le
      exact deriv_fitAlong_ge R U j z W hj hcz (hw c hcS) (by linarith) hr1
    rw [e0]
    refine le_trans ?_ (Finset.sum_le_sum hbelow)
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    have h1 := sum_mul_le_finLpNorm_mul (bondsOver S {z} (j + 1)) (f := fun c => ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 3)
      (g := fun c => normSubOne (referenceDefect R j c)) (fun _ _ => by positivity) (fun _ _ => norm_nonneg _)
    have e1 : finLpNorm (bondsOver S {z} (j + 1)) (4 / 3) (fun c => ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 3) = l1 := by
      rw [hl1, levelDerivNorm_first R U j z hLpos hodd]
      unfold finLpNorm
      have e2 : (1 / (4 / 3 : ℝ)) = 3 / 4 := by norm_num
      rw [e2]
      congr 1
      refine Finset.sum_congr rfl fun c _ => ?_
      exact pow_three_rpow_four_thirds (norm_nonneg _)
    rw [e1] at h1
    linarith
  have hup : ∀ i ∈ (Finset.range F.top).filter (fun i => j < i), |D i| ≤ l1 *
      (if i = F.depth then 13 * F.blockSide * hC * (11 * e i) * q ^ (i - (j + 1)) else
        20 * ε * F.blockSide * hC * (11 * e i) ^ 2 * q ^ (i - (j + 1))) := by
    intro i hi
    obtain ⟨hi1, hji⟩ := Finset.mem_filter.1 hi
    have hin := Finset.mem_range.1 hi1
    have hlev : levelDerivNorm R U j z S i ≤ q ^ (i - (j + 1)) * l1 := by
      have h1 := levelDerivNorm_le_pow (S := S) R U j z hodd hs ht0 ht hρ0 hε hq (i - (j + 1)) (by omega)
      have e2 : j + 1 + (i - (j + 1)) = i := by omega
      rw [e2] at h1
      exact h1
    have hle0 := he i
    split_ifs with hit
    · subst hit
      have h1 : |D F.depth| ≤ ∑ c ∈ innerBonds S (F.depth + 1), |deriv (fun τ => fitAlong R U j z W F.depth τ c) 0| :=
        Finset.abs_sum_le_sum_abs _ _
      have h2 : ∀ c ∈ innerBonds S (F.depth + 1), |deriv (fun τ => fitAlong R U j z W F.depth τ c) 0| ≤
          (13 * F.blockSide) * (normSubOne (chartBondMisfit R U W F.depth c) * hullDerivSum R U j z F.depth c) := by
        intro c hc
        obtain ⟨v, hv⟩ := hs.contour_near F.depth hin c hc
        have := abs_deriv_fitAlong_depth_le R U j z W hodd hreg hc v ht0 ht hρ0 hε (hs.hull_le hodd hin hc) hv
        refine this.trans (le_of_eq ?_)
        rw [show distFromOne (chartBondMisfit R U W F.depth c) = normSubOne (chartBondMisfit R U W F.depth c) from rfl]
        ring
      have h3 := sum_mul_hullDerivSum_le (S := S) R U j z hodd hL (by omega) hin
        (fun c => normSubOne (chartBondMisfit R U W F.depth c))
        (fun c => norm_nonneg _) (finLpNorm_misfit_le R U z W hle0 (hG F.depth hji hin))
      refine h1.trans ((Finset.sum_le_sum h2).trans ?_)
      rw [← Finset.mul_sum]
      refine (mul_le_mul_of_nonneg_left h3 (by positivity)).trans ?_
      have h4 := mul_le_mul_of_nonneg_left hlev
        (by positivity : (0 : ℝ) ≤ 13 * F.blockSide * (hC * (11 * e F.depth)))
      calc _ = 13 * F.blockSide * (hC * (11 * e F.depth)) * levelDerivNorm R U j z S F.depth := by ring
        _ ≤ _ := h4
        _ = _ := by ring
    · have hi1' : i + 1 < F.top := by
        have e2 : F.top = F.depth + 1 := rfl
        omega
      have h1 : |D i| ≤ ∑ c ∈ innerBonds S (i + 1), |deriv (fun τ => fitAlong R U j z W i τ c) 0| :=
        Finset.abs_sum_le_sum_abs _ _
      have h2 : ∀ c ∈ innerBonds S (i + 1), |deriv (fun τ => fitAlong R U j z W i τ c) 0| ≤
          (20 * ε * F.blockSide) * (normSubOne (chartBondMisfit R U W i c) ^ 2 * hullDerivSum R U j z i c) := by
        intro c hc
        obtain ⟨v, hv⟩ := hs.contour_near i hin c hc
        have := abs_deriv_fitAlong_le R U j z W hodd hreg hji hi1' hc v ht0 ht hρ0 hε (hs.hull_le hodd hin hc) hv
        refine this.trans (le_of_eq ?_)
        rw [show distFromOne (chartBondMisfit R U W i c) = normSubOne (chartBondMisfit R U W i c) from rfl, hεdef]
        ring
      have h3 := sum_mul_hullDerivSum_le (S := S) R U j z hodd hL (by omega) hin
        (fun c => normSubOne (chartBondMisfit R U W i c) ^ 2)
        (fun c => by positivity) (finLpNorm_misfit_sq_le R U z W hle0 (hG i hji hin))
      refine h1.trans ((Finset.sum_le_sum h2).trans ?_)
      rw [← Finset.mul_sum]
      refine (mul_le_mul_of_nonneg_left h3 (by positivity)).trans ?_
      have h4 := mul_le_mul_of_nonneg_left hlev
        (by positivity : (0 : ℝ) ≤ 20 * ε * F.blockSide * (hC * (11 * e i) ^ 2))
      calc _ = 20 * ε * F.blockSide * (hC * (11 * e i) ^ 2) * levelDerivNorm R U j z S i := by ring
        _ ≤ _ := h4
        _ = _ := by ring
  have hT : - ∑ i ∈ (Finset.range F.top).filter (fun i => j < i), D i ≤ l1 *
      ∑ i ∈ (Finset.range F.top).filter (fun i => j < i),
        (if i = F.depth then 13 * F.blockSide * hC * (11 * e i) * q ^ (i - (j + 1)) else
          20 * ε * F.blockSide * hC * (11 * e i) ^ 2 * q ^ (i - (j + 1))) := by
    rw [Finset.mul_sum]
    have h1 : - ∑ i ∈ (Finset.range F.top).filter (fun i => j < i), D i ≤
        |∑ i ∈ (Finset.range F.top).filter (fun i => j < i), D i| :=
      neg_le_abs _
    exact h1.trans ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hup))
  have hsum' : ∑ i ∈ Finset.range F.top, D i = 0 := hsum
  rw [hsplit] at hsum'
  rw [mul_add]
  linarith
end Fixed
end YangMills.Construction.VariationDecay
end
