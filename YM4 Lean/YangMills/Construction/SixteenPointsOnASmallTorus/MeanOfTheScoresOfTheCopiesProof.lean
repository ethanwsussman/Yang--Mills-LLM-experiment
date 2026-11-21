import YangMills.Construction.Towers.TransposesOfTheIteratedAveragesOfTheScaledPictureOnTheWholeProof
import YangMills.Construction.ResponseInTheExpansion.MajorantsOverAStepOfAnArray
import YangMills.Construction.ResponseInTheExpansion.MassAlongTheLevels
import YangMills.Construction.ResponseInTheExpansion.RunningCouplingSlope
import YangMills.Construction.SixteenPointsOnASmallTorus.CopiesAtTheLevelOfTheirRadiusProof
import YangMills.Construction.SixteenPointsOnASmallTorus.CouplingAtTheLevelOfARadius
import YangMills.Construction.SixteenPointsOnASmallTorus.MeanOfTheScoresOfTheCopies
import YangMills.Construction.SixteenPointsOnASmallTorus.ScoreAtAnyCoupling
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.SmallTorusCopies
open TorusFields TorusLumps StepSettings RenormalizationStepParameters WeightedResponses ResponseInTheExpansion ClusterExpansionOfAStep TestFunctions
section SiteScores
variable {n : ℕ} [NeZero n] {Ω : Type}
omit [NeZero n] in
private theorem siteScore_nonneg {s : Ω → ℝ} (hs : ∀ w, 0 ≤ s w) (Y : Finset (TorusSite n)) (ω : Y → Ω) (y : TorusSite n) :
    0 ≤ siteScore s Y ω y := by apply _root_.YangMills.SharedProofs.p42827 <;> assumption
omit [NeZero n] in
private theorem one_le_meanSiteScore {s : Ω → ℝ} (hs : ∀ w, 0 ≤ s w) (B Y : Finset (TorusSite n)) (ω : Y → Ω) :
    1 ≤ meanSiteScore s B Y ω := by
  have h1 : 0 ≤ ∑ y ∈ B, siteScore s Y ω y := Finset.sum_nonneg fun y _ => siteScore_nonneg hs Y ω y
  have h2 : 0 ≤ (B.card : ℝ)⁻¹ * ∑ y ∈ B, siteScore s Y ω y := by positivity
  unfold meanSiteScore
  linarith
abbrev _root_.YangMills.SharedProofs.p106812 := @one_le_meanSiteScore
private theorem sum_siteScore {s : Ω → ℝ} (Y : Finset (TorusSite n)) (ω : Y → Ω) :
    ∑ y, siteScore s Y ω y = ∑ z : Y, s (ω z) := by
  classical
  have h1 : ∑ y, siteScore s Y ω y = ∑ y ∈ Y, siteScore s Y ω y := by
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun y _ hy => ?_
    simp [siteScore, hy]
  rw [h1, ← Finset.sum_coe_sort]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp [siteScore, z.2]
abbrev _root_.YangMills.SharedProofs.p15197 := @sum_siteScore
private theorem meanSiteScore_le {s : Ω → ℝ} (hs : ∀ w, 0 ≤ s w) {B : Finset (TorusSite n)} (hB : B.Nonempty) (Y : Finset (TorusSite n))
    (ω : Y → Ω) : meanSiteScore s B Y ω ≤ 1 + ∑ z : Y, s (ω z) := by
  have h1 : ∑ y ∈ B, siteScore s Y ω y ≤ ∑ y, siteScore s Y ω y :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun y _ _ => siteScore_nonneg hs Y ω y
  have h0 : 0 ≤ ∑ y ∈ B, siteScore s Y ω y := Finset.sum_nonneg fun y _ => siteScore_nonneg hs Y ω y
  have hc : (1 : ℝ) ≤ B.card := by exact_mod_cast hB.card_pos
  have hinv : (B.card : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc
  have h2 : (B.card : ℝ)⁻¹ * ∑ y ∈ B, siteScore s Y ω y ≤ ∑ y ∈ B, siteScore s Y ω y := by
    nlinarith
  unfold meanSiteScore
  rw [sum_siteScore] at h1
  linarith
end SiteScores
section RealBounds
private theorem one_add_pow_le_factorial {S : ℝ} (hS : 0 ≤ S) {q k : ℕ} (hq : q ≤ k) :
    (1 + S) ^ q ≤ (k.factorial : ℝ) * Real.exp 1 * Real.exp S := by
  have h1 := Real.pow_div_factorial_le_exp (1 + S) (by linarith) q
  have hf : (0 : ℝ) < (q.factorial : ℝ) := by exact_mod_cast q.factorial_pos
  rw [div_le_iff₀ hf, Real.exp_add] at h1
  have h2 : (q.factorial : ℝ) ≤ (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_le hq
  calc (1 + S) ^ q ≤ Real.exp 1 * Real.exp S * (q.factorial : ℝ) := h1
    _ ≤ Real.exp 1 * Real.exp S * (k.factorial : ℝ) := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring
private theorem sum_exp_neg_le {x : ℕ → ℝ} {lam c₅ κ : ℝ} {K : ℕ} (hlam : 0 < lam) (hκ : 0 < κ) (hxK : 0 ≤ x K)
    (hs : ∀ i ≤ K, lam * ((K : ℝ) - i) - c₅ ≤ x i - x K) :
    ∑ l ∈ Finset.range K, Real.exp (-(κ * x l)) ≤
      Real.exp (κ * c₅) / (1 - Real.exp (-(κ * lam))) := by
  set r := Real.exp (-(κ * lam)) with hr
  have hr1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]
    have : 0 < κ * lam := by positivity
    linarith
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hterm : ∀ l ∈ Finset.range K, Real.exp (-(κ * x l)) ≤ Real.exp (κ * c₅) * r ^ (K - 1 - l) := by
    intro l hl
    have hl' : l < K := Finset.mem_range.mp hl
    have h1 := hs l hl'.le
    rw [hr, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hc : ((K - 1 - l : ℕ) : ℝ) ≤ (K : ℝ) - l := by
      have : K - 1 - l ≤ K - l := by omega
      calc ((K - 1 - l : ℕ) : ℝ) ≤ ((K - l : ℕ) : ℝ) := by exact_mod_cast this
        _ = (K : ℝ) - l := by rw [Nat.cast_sub hl'.le]
    have h2 : κ * (lam * ((K - 1 - l : ℕ) : ℝ)) ≤ κ * (lam * ((K : ℝ) - l)) := by
      gcongr
    have h3 : κ * (lam * ((K : ℝ) - l)) ≤ κ * (x l + c₅) := by
      apply mul_le_mul_of_nonneg_left _ hκ.le
      linarith
    nlinarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum, div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  have hrefl := Finset.sum_range_reflect (fun i : ℕ => r ^ i) K
  rw [hrefl, ← tsum_geometric_of_lt_one hr0 hr1]
  exact (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum _ fun i _ => pow_nonneg hr0 i
private theorem clusterRange_le_of_step {x x' B : ℝ} (hx : 1 ≤ x) (hx' : 1 ≤ x') (hB : 0 ≤ B) (hm : x' ≤ x + 2 * B) :
    (clusterRange x' : ℝ) ≤ 2 * (1 + 2 * B) * x ^ ((1 : ℝ) / 100) := by
  have hw : 1 ≤ x ^ ((1 : ℝ) / 100) := Real.one_le_rpow hx (by norm_num)
  have hB1 : 1 ≤ 1 + 2 * B := by linarith
  have h1 : x' ≤ (1 + 2 * B) * x := by nlinarith
  have h2 : x' ^ ((1 : ℝ) / 100) ≤ (1 + 2 * B) * x ^ ((1 : ℝ) / 100) := by
    calc x' ^ ((1 : ℝ) / 100) ≤ ((1 + 2 * B) * x) ^ ((1 : ℝ) / 100) :=
          Real.rpow_le_rpow (by linarith) h1 (by norm_num)
      _ = (1 + 2 * B) ^ ((1 : ℝ) / 100) * x ^ ((1 : ℝ) / 100) :=
          Real.mul_rpow (by linarith) (by linarith)
      _ ≤ (1 + 2 * B) * x ^ ((1 : ℝ) / 100) := by
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          calc (1 + 2 * B) ^ ((1 : ℝ) / 100) ≤ (1 + 2 * B) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le hB1 (by norm_num)
            _ = 1 + 2 * B := Real.rpow_one _
  have h3 : (clusterRange x' : ℝ) < x' ^ ((1 : ℝ) / 100) + 1 := by
    unfold clusterRange
    exact Nat.ceil_lt_add_one (Real.rpow_nonneg (by linarith) _)
  have h4 : 1 ≤ (1 + 2 * B) * x ^ ((1 : ℝ) / 100) := by nlinarith
  linarith
private theorem one_add_log_le_rpow {x : ℝ} (hx : 1 ≤ x) : 1 + Real.log x ≤ 100 * x ^ ((1 : ℝ) / 100) := by
  have hx0 : 0 < x := by linarith
  have hw : 0 < x ^ ((1 : ℝ) / 100) := Real.rpow_pos_of_pos hx0 _
  have h1 := Real.log_le_sub_one_of_pos hw
  rw [Real.log_rpow hx0] at h1
  linarith
private theorem boundary_term_le {x B n r L : ℝ} (hx : 1 ≤ x) (hB : 0 ≤ B) (hL : 0 ≤ L) (hn0 : 0 ≤ n)
    (hr : r ≤ 2 * (1 + 2 * B) * x ^ ((1 : ℝ) / 100)) (hn : n ≤ 2 ^ 14 * L * r) :
    (1 + Real.log x) * n ^ 4 ≤ 100 * (2 ^ 15 * L * (1 + 2 * B)) ^ 4 * x ^ ((1 : ℝ) / 20) := by
  set w := x ^ ((1 : ℝ) / 100) with hw
  have hw5 : w ^ 5 = x ^ ((1 : ℝ) / 20) := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num
  set G : ℝ := 2 ^ 15 * L * (1 + 2 * B) with hG
  have hnG : n ≤ G * w := by
    have h1 : 2 ^ 14 * L * r ≤ 2 ^ 14 * L * (2 * (1 + 2 * B) * w) :=
      mul_le_mul_of_nonneg_left hr (by positivity)
    linarith
  have h4 : n ^ 4 ≤ (G * w) ^ 4 := pow_le_pow_left₀ hn0 hnG 4
  calc (1 + Real.log x) * n ^ 4 ≤ (100 * w) * (G * w) ^ 4 :=
        mul_le_mul (one_add_log_le_rpow hx) h4 (by positivity) (by positivity)
    _ = 100 * G ^ 4 * w ^ 5 := by ring
    _ = _ := by rw [hw5]
private theorem coupling_rpow_bound {x C₁ l : ℝ} (hx : 0 ≤ x) (hC : 0 ≤ C₁) (hl : 0 < l)
    (h : x ≤ C₁ * (1 + TorusBound.logPos (1 / (l / 4)))) :
    x ^ ((1 : ℝ) / 20) ≤ C₁ ^ ((1 : ℝ) / 20) * (4 + TorusBound.logPos (1 / l) ^ ((1 : ℝ) / 20)) := by
  set v := TorusBound.logPos (1 / l) with hv
  have hv0 : 0 ≤ v := le_max_right _ _
  have hlog : Real.log (1 / (l / 4)) ≤ 3 + v := by
    have e : 1 / (l / 4) = 4 * (1 / l) := by
      field_simp
    rw [e, Real.log_mul (by norm_num) (by positivity)]
    have h4 : Real.log 4 ≤ 4 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    have h5 : Real.log (1 / l) ≤ v := le_max_left _ _
    linarith
  have hlp : TorusBound.logPos (1 / (l / 4)) ≤ 3 + v := max_le hlog (by linarith)
  have h1 : x ≤ C₁ * (4 + v) := h.trans (mul_le_mul_of_nonneg_left (by linarith) hC)
  calc x ^ ((1 : ℝ) / 20) ≤ (C₁ * (4 + v)) ^ ((1 : ℝ) / 20) := Real.rpow_le_rpow hx h1 (by norm_num)
    _ = C₁ ^ ((1 : ℝ) / 20) * (4 + v) ^ ((1 : ℝ) / 20) := Real.mul_rpow hC (by linarith)
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hC _)
        have h2 : (4 + v) ^ ((1 : ℝ) / 20) ≤ (4 : ℝ) ^ ((1 : ℝ) / 20) + v ^ ((1 : ℝ) / 20) :=
          Real.rpow_add_le_add_rpow (by norm_num) hv0 (by norm_num) (by norm_num)
        have h3 : (4 : ℝ) ^ ((1 : ℝ) / 20) ≤ 4 := by
          calc (4 : ℝ) ^ ((1 : ℝ) / 20) ≤ (4 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 4 := Real.rpow_one _
        linarith
end RealBounds
section Stages
private theorem cellLength_eq {L K κ p : ℕ} (hL : L ≠ 0) (hp : p ≤ κ) :
    cellLength L K κ = (L : ℝ) ^ (κ - p) * levelSpacing L K p := by
  have h0 : (L : ℝ) ≠ 0 := by exact_mod_cast hL
  have e : (L : ℝ) ^ κ = (L : ℝ) ^ (κ - p) * (L : ℝ) ^ p := by
    rw [← pow_add, Nat.sub_add_cancel hp]
  unfold cellLength levelSpacing
  rw [e, zpow_sub₀ h0, zpow_sub₀ h0]
  simp only [zpow_natCast, Nat.cast_zero]
  field_simp
private theorem levelSpacing_pos {L : ℕ} (hL : L ≠ 0) (K t : ℕ) : 0 < levelSpacing L K t := by
  have h0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero hL
  exact zpow_pos h0 _
private theorem levelSpacing_self (L K : ℕ) : levelSpacing L K K = 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.IterTransposesOnFullSpace.meshAt_self <;> assumption
private theorem twoCellSide_eq_fineSide {L κ s u : ℕ} (h : s + u ≤ κ) :
    twoCellSide L κ s = fineSide L u (twoCellSide L κ (s + u)) := by
  rw [fineSide_eq]
  unfold twoCellSide
  rw [mul_assoc, ← pow_add]
  congr 2
  omega
private theorem radiusLevel_mono {ℓ : StepParameters} {β : ℝ} {K s : ℕ} {ρ ρ' : ℝ} (hρ : ρ ≤ ρ')
    (hs : radiusLevel ℓ β K ρ = some s) :
    ∃ s', radiusLevel ℓ β K ρ' = some s' ∧ s ≤ s' ∧ s' ≤ K ∧ ∀ t, s' < t → t ≤ K → ¬ FitsAtLevel ℓ β K ρ' t := by
  classical
  unfold radiusLevel at hs
  split_ifs at hs with h
  obtain ⟨t, ht, hf⟩ := h
  have hs' : Nat.findGreatest (FitsAtLevel ℓ β K ρ) K = s := by simpa using hs
  have hfs : FitsAtLevel ℓ β K ρ s := hs' ▸ Nat.findGreatest_spec ht hf
  have hsK : s ≤ K := hs' ▸ Nat.findGreatest_le K
  have hfs' : FitsAtLevel ℓ β K ρ' s := le_trans hfs hρ
  refine ⟨Nat.findGreatest (FitsAtLevel ℓ β K ρ') K, ?_, Nat.le_findGreatest hsK hfs', Nat.findGreatest_le K, ?_⟩
  · unfold radiusLevel
    rw [if_pos ⟨s, hsK, hfs'⟩]
  · intro t h1 h2
    exact Nat.findGreatest_is_greatest h1 h2
end Stages
section StateIntegrals
private theorem stateLIntegral_le_mul {R : StepSetup} {n : ℕ} [NeZero n] {H H' : StateFunction R n} {c : ℝ} (hc : 0 ≤ c)
    (hH : ∀ W Y ω, 0 ≤ H W Y ω) (h : ∀ (W : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → R.labels.Ω), H W Y ω ≤ c * H' W Y ω) :
    stateLIntegral R n H ≤ ENNReal.ofReal c * stateLIntegral R n H' := by
  classical
  unfold stateLIntegral
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun W => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun Y _ => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun ω => ?_
  by_cases hq : 0 < R.labelWeight n W Y ω
  · rw [← ENNReal.ofReal_mul hc]
    apply ENNReal.ofReal_le_ofReal
    have := h W Y ω
    nlinarith
  · have h0 : R.labelWeight n W Y ω * H W Y ω ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hq) (hH W Y ω)
    rw [ENNReal.ofReal_of_nonpos h0]
    exact bot_le
end StateIntegrals
section ParentImages
variable {L : ℕ} [NeZero L]
private def parentImage (L : ℕ) [NeZero L] {ι : Type} : (u n : ℕ) → [NeZero n] → (ι → Finset (TorusSite (fineSide L u n))) →
    ι → Finset (TorusSite n)
  | 0, _, _, B => B
  | u + 1, n, _, B => fun i => open Classical in (parentImage L u (n * L) B i).image (parentBlock L)
private theorem parentImage_nonempty {ι : Type} {i : ι} : ∀ (u n : ℕ) [NeZero n] (B : ι → Finset (TorusSite (fineSide L u n))),
    (B i).Nonempty → (parentImage L u n B i).Nonempty
  | 0, _, _, _, h => h
  | u + 1, n, _, B, h => by
    classical
    exact (parentImage_nonempty u (n * L) B h).image _
end ParentImages
section Ascent
variable {T : ParameterAssignment} {RK : ResponseParameters} {y β : ℝ} {hL : ∀ c : ChainStage (T.stepParameters y), CoarseLabelFacts c.toStepSetup}
  {z₀ : StageWithResponse (T.stepParameters y)}
private theorem isBlockTorusSide_mul {ℓ : StepParameters} {n : ℕ} (h : IsBlockTorusSide ℓ n) (hL : 1 ≤ ℓ.side) :
    IsBlockTorusSide ℓ (n * ℓ.side) :=
  ⟨Dvd.intro_left n rfl, h.2.trans (Nat.le_mul_of_pos_right _ hL)⟩
private def majorantRate (ch : ℝ) (z : ℕ → StageWithResponse (T.stepParameters y)) (q t : ℕ) : ℝ :=
  2 ^ q * (q.factorial : ℝ) * Real.exp (-(7 * ch * (z t).1.coupling))
private theorem majorants_iterate
    (hMj : ∀ (R : StepSetup) (A : ResponseSetup R), A.responseParams = RK → OnStepParameters T y A → R.IsSymmetricWeight →
      ∀ (h : CoarseLabelFacts R) (x'' : ℝ)
      (n : ℕ) [NeZero n], IsBlockTorusSide R.params n → ∀ (ι : Type) (I : Finset ι) (B : ι → Finset (TorusSite (n * R.params.side))),
      (∀ i ∈ I, (B i).Nonempty) →
      stateLIntegral R (n * R.params.side) (fun _ Y ω => ∏ i ∈ I, meanSiteScore A.score (B i) Y ω) ≤
        ENNReal.ofReal (Real.exp (2 ^ I.card * (I.card.factorial : ℝ) * Real.exp (-(7 * T.gasRate * R.coupling)))) *
          stateLIntegral (nextStepSetup R h T.lam x'') n (fun _ Y ω => ∏ i ∈ I, meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score)
            (open Classical in (B i).image (parentBlock R.params.side)) Y ω))
    (hL1 : 1 ≤ T.side) {ι : Type} (I : Finset ι) (t : ℕ) :
    ∀ (u n : ℕ) [NeZero n] (B : ι → Finset (TorusSite (fineSide T.side u n))), IsBlockTorusSide (T.stepParameters y) n →
      (∀ i ∈ I, (B i).Nonempty) →
      (∀ j < u, StageOnFlow T RK y β (t + j) (flowStages T y β hL z₀ (t + j))) →
      stateLIntegral (flowStages T y β hL z₀ t).1.toStepSetup (fineSide T.side u n)
          (fun _ Y ω => ∏ i ∈ I, meanSiteScore (flowStages T y β hL z₀ t).2.score (B i) Y ω) ≤
        ENNReal.ofReal (Real.exp (∑ j ∈ Finset.range u,
            majorantRate T.gasRate (flowStages T y β hL z₀) I.card (t + j))) *
          stateLIntegral (flowStages T y β hL z₀ (t + u)).1.toStepSetup n
            (fun _ Y ω => ∏ i ∈ I, meanSiteScore (flowStages T y β hL z₀ (t + u)).2.score (parentImage T.side u n B i) Y ω) := by
  intro u
  induction u with
  | zero =>
    intro n _ B _ _ _
    simp only [Finset.range_zero, Finset.sum_empty, Real.exp_zero, ENNReal.ofReal_one, one_mul]
    exact le_rfl
  | succ u ih =>
    intro n _ B hbs hne hst
    have h₁ := ih (n * T.side) B (isBlockTorusSide_mul hbs hL1) hne fun j hj => hst j (by omega)
    have hsu := hst u (by omega)
    have hne' : ∀ i ∈ I, (parentImage T.side u (n * T.side) B i).Nonempty := fun i hi =>
      parentImage_nonempty u (n * T.side) B (hne i hi)
    have h₂ := hMj (flowStages T y β hL z₀ (t + u)).1.toStepSetup (flowStages T y β hL z₀ (t + u)).2 hsu.params_eq hsu.onFamily
      hsu.isSymmetricWeight (hL _) (couplingsAlongFlow (T.stepParameters y) β (t + u + 2)) n hbs ι I (parentImage T.side u (n * T.side) B) hne'
    refine h₁.trans ?_
    rw [Finset.sum_range_succ, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le, mul_assoc]
    exact mul_le_mul' le_rfl h₂
private theorem unitIntegral_iterate
    (hMs : ∀ (R : StepSetup) (A : ResponseSetup R), A.responseParams = RK → OnStepParameters T y A → R.IsSymmetricWeight →
      ∀ (h : CoarseLabelFacts R) (x'' : ℝ)
      (n : ℕ) [NeZero n], IsBlockTorusSide R.params n →
      stateLIntegral R (n * R.params.side) (fun _ _ _ => 1) = stateLIntegral (nextStepSetup R h T.lam x'') n fun _ _ _ => 1)
    (hL1 : 1 ≤ T.side) (t : ℕ) :
    ∀ (u n : ℕ) [NeZero n], IsBlockTorusSide (T.stepParameters y) n →
      (∀ j < u, StageOnFlow T RK y β (t + j) (flowStages T y β hL z₀ (t + j))) →
      stateLIntegral (flowStages T y β hL z₀ t).1.toStepSetup (fineSide T.side u n) (fun _ _ _ => 1) =
        stateLIntegral (flowStages T y β hL z₀ (t + u)).1.toStepSetup n fun _ _ _ => 1 := by
  intro u
  induction u with
  | zero => intro n _ _ _; rfl
  | succ u ih =>
    intro n _ hbs hst
    have h₁ := ih (n * T.side) (isBlockTorusSide_mul hbs hL1) fun j hj => hst j (by omega)
    have hsu := hst u (by omega)
    exact h₁.trans (hMs _ _ hsu.params_eq hsu.onFamily hsu.isSymmetricWeight (hL _) (couplingsAlongFlow (T.stepParameters y) β (t + u + 2)) n hbs)
private theorem sixteen_means_le
    (hMj : ∀ (R : StepSetup) (A : ResponseSetup R), A.responseParams = RK → OnStepParameters T y A → R.IsSymmetricWeight →
      ∀ (h : CoarseLabelFacts R) (x'' : ℝ)
      (n : ℕ) [NeZero n], IsBlockTorusSide R.params n → ∀ (ι : Type) (I : Finset ι) (B : ι → Finset (TorusSite (n * R.params.side))),
      (∀ i ∈ I, (B i).Nonempty) →
      stateLIntegral R (n * R.params.side) (fun _ Y ω => ∏ i ∈ I, meanSiteScore A.score (B i) Y ω) ≤
        ENNReal.ofReal (Real.exp (2 ^ I.card * (I.card.factorial : ℝ) * Real.exp (-(7 * T.gasRate * R.coupling)))) *
          stateLIntegral (nextStepSetup R h T.lam x'') n (fun _ Y ω => ∏ i ∈ I, meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score)
            (open Classical in (B i).image (parentBlock R.params.side)) Y ω))
    (hMs : ∀ (R : StepSetup) (A : ResponseSetup R), A.responseParams = RK → OnStepParameters T y A → R.IsSymmetricWeight →
      ∀ (h : CoarseLabelFacts R) (x'' : ℝ)
      (n : ℕ) [NeZero n], IsBlockTorusSide R.params n →
      stateLIntegral R (n * R.params.side) (fun _ _ _ => 1) = stateLIntegral (nextStepSetup R h T.lam x'') n fun _ _ _ => 1)
    (hL1 : 1 ≤ T.side) {s u n : ℕ} [NeZero n] (hbs : IsBlockTorusSide (T.stepParameters y) n)
    (hst : ∀ t ≤ s + u, StageOnFlow T RK y β t (flowStages T y β hL z₀ t)) {Q E : ℝ}
    (hQ : ∑ j ∈ Finset.range u, Real.exp (-(7 * T.gasRate * (flowStages T y β hL z₀ (s + j)).1.coupling)) ≤ Q)
    (hTop : stateLIntegral (flowStages T y β hL z₀ (s + u)).1.toStepSetup n
        (fun _ Y ω => Real.exp (∑ z : Y, (flowStages T y β hL z₀ (s + u)).2.score (ω z))) ≤
      ENNReal.ofReal (Real.exp E) * stateLIntegral (flowStages T y β hL z₀ (s + u)).1.toStepSetup n fun _ _ _ => 1)
    (m : ℕ) [NeZero m] (hm : m = fineSide T.side u n) (B : (Fin 4 → Fin 2) → Finset (TorusSite m)) :
    stateLIntegral (flowStages T y β hL z₀ s).1.toStepSetup m
        (fun _ Y ω => ∏ k, meanSiteScore (flowStages T y β hL z₀ s).2.score (B k) Y ω) ≤
      ENNReal.ofReal (Real.exp (2 ^ 16 * ((16 : ℕ).factorial : ℝ) * Q) * (((16 : ℕ).factorial : ℝ) * Real.exp 1) * Real.exp E) *
        stateLIntegral (flowStages T y β hL z₀ s).1.toStepSetup m fun _ _ _ => 1 := by
  classical
  subst hm
  set J : Finset (Fin 4 → Fin 2) := Finset.univ.filter fun k => (B k).Nonempty with hJ
  have hNe : ∀ k ∈ J, (B k).Nonempty := fun k hk => (Finset.mem_filter.mp hk).2
  have hJ16 : J.card ≤ 16 := by
    calc J.card ≤ (Finset.univ : Finset (Fin 4 → Fin 2)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = 16 := by simp
  have hNJ : (fun (_ : TorusField (fineSide T.side u n)) (Y : Finset (TorusSite (fineSide T.side u n)))
      (ω : Y → (flowStages T y β hL z₀ s).1.labels.Ω) => ∏ k, meanSiteScore (flowStages T y β hL z₀ s).2.score (B k) Y ω) =
      fun _ Y ω => ∏ k ∈ J, meanSiteScore (flowStages T y β hL z₀ s).2.score (B k) Y ω := by
    funext W Y ω
    simp only [hJ]
    rw [Finset.prod_filter]
    refine Finset.prod_congr rfl fun k _ => ?_
    split_ifs with h
    · rfl
    · rw [Finset.not_nonempty_iff_eq_empty.mp h]
      simp [meanSiteScore]
  rw [hNJ]
  have c₃ := majorants_iterate (T := T) (RK := RK) (y := y) (β := β) (hL := hL) (z₀ := z₀) hMj hL1 J s u n B hbs hNe
    (fun j hj => hst (s + j) (by omega))
  set Rt := (flowStages T y β hL z₀ (s + u)).1.toStepSetup with hRt
  set At := (flowStages T y β hL z₀ (s + u)).2 with hAt
  have ht := hst (s + u) le_rfl
  have hsc' := ht.onFamily.admissible.price.nonneg
  have c₄ : stateLIntegral Rt n (fun _ Y ω => ∏ k ∈ J, meanSiteScore At.score (parentImage T.side u n B k) Y ω) ≤
      ENNReal.ofReal (((16 : ℕ).factorial : ℝ) * Real.exp 1) *
        stateLIntegral Rt n (fun _ Y ω => Real.exp (∑ z : Y, At.score (ω z))) := by
    refine stateLIntegral_le_mul (by positivity)
      (fun W Y ω => Finset.prod_nonneg fun k _ => by linarith [one_le_meanSiteScore hsc' (parentImage T.side u n B k) Y ω])
      fun W Y ω => ?_
    have hS : 0 ≤ ∑ z : Y, At.score (ω z) := Finset.sum_nonneg fun z _ => hsc' _
    calc ∏ k ∈ J, meanSiteScore At.score (parentImage T.side u n B k) Y ω ≤ ∏ _k ∈ J, (1 + ∑ z : Y, At.score (ω z)) :=
          Finset.prod_le_prod (fun k _ => by linarith [one_le_meanSiteScore hsc' (parentImage T.side u n B k) Y ω])
            fun k hk => meanSiteScore_le hsc' (parentImage_nonempty u n B (hNe k hk)) Y ω
      _ = (1 + ∑ z : Y, At.score (ω z)) ^ J.card := by rw [Finset.prod_const]
      _ ≤ _ := one_add_pow_le_factorial hS hJ16
  have hck0 : (0 : ℝ) ≤ 2 ^ 16 * ((16 : ℕ).factorial : ℝ) := by positivity
  have hexp : Real.exp (∑ j ∈ Finset.range u, majorantRate T.gasRate (flowStages T y β hL z₀) J.card (s + j)) ≤
      Real.exp (2 ^ 16 * ((16 : ℕ).factorial : ℝ) * Q) := by
    apply Real.exp_le_exp.mpr
    unfold majorantRate
    rw [← Finset.mul_sum]
    have e₁ : (2 : ℝ) ^ J.card * (J.card.factorial : ℝ) ≤ 2 ^ 16 * ((16 : ℕ).factorial : ℝ) := by
      have a₁ : (2 : ℝ) ^ J.card ≤ 2 ^ 16 := pow_le_pow_right₀ (by norm_num) hJ16
      have a₂ : (J.card.factorial : ℝ) ≤ ((16 : ℕ).factorial : ℝ) := by exact_mod_cast Nat.factorial_le hJ16
      exact mul_le_mul a₁ a₂ (by positivity) (by positivity)
    have h0 : 0 ≤ ∑ j ∈ Finset.range u, Real.exp (-(7 * T.gasRate * (flowStages T y β hL z₀ (s + j)).1.coupling)) :=
      Finset.sum_nonneg fun j _ => (Real.exp_pos _).le
    exact mul_le_mul e₁ hQ h0 hck0
  have hMass := unitIntegral_iterate (T := T) (RK := RK) (y := y) (β := β) (hL := hL) (z₀ := z₀) hMs hL1 s u n hbs
    (fun j hj => hst (s + j) (by omega))
  have e₀ : ENNReal.ofReal (Real.exp (2 ^ 16 * ((16 : ℕ).factorial : ℝ) * Q) * (((16 : ℕ).factorial : ℝ) * Real.exp 1) *
      Real.exp E) = ENNReal.ofReal (Real.exp (2 ^ 16 * ((16 : ℕ).factorial : ℝ) * Q)) *
        ENNReal.ofReal (((16 : ℕ).factorial : ℝ) * Real.exp 1) * ENNReal.ofReal (Real.exp E) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
  rw [e₀, hMass, mul_assoc, mul_assoc]
  refine c₃.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hexp) (c₄.trans ?_))
  exact mul_le_mul' le_rfl hTop
end Ascent
section MainBound
variable {T : ParameterAssignment} {RK : ResponseParameters} {y : ℝ}
private theorem gasRate_pos (hT : T.Admissible) (hfit : (T.stepParameters y).Admissible) : 0 < 7 * T.gasRate := by
  have h1 := hT.cE_pos
  have h2 := hfit.κ_pos
  have h3 := hfit.κ₁_pos
  have h4 : 0 < T.threshold := hfit.σ_pos
  have h5 : 0 < T.κ * T.threshold ^ 2 := mul_pos h2 (by positivity)
  have h6 : 0 < T.κ₁ * T.threshold ^ 2 := mul_pos h3 (by positivity)
  have : 0 < T.gasRate := mul_pos (by norm_num) (lt_min h1 (lt_min h5 h6))
  linarith
private theorem bound_at_floor (hT : T.Admissible) (hy0 : T.floorMin ≤ y) (hy1 : 1 ≤ y) {Ξ lam c₅ c C₁ : ℝ}
    (hΞ : y + 2 * T.B ≤ Ξ) (hlam : 0 < lam) (hS : HasLinearDescent (T.stepParameters y) lam c₅) (hc : 0 ≤ c) (hC₁ : 0 ≤ C₁)
    (hMj : ∀ (R : StepSetup) (A : ResponseSetup R), A.responseParams = RK → OnStepParameters T y A → R.IsSymmetricWeight →
      ∀ (h : CoarseLabelFacts R) (x'' : ℝ)
      (n : ℕ) [NeZero n], IsBlockTorusSide R.params n → ∀ (ι : Type) (I : Finset ι) (B : ι → Finset (TorusSite (n * R.params.side))),
      (∀ i ∈ I, (B i).Nonempty) →
      stateLIntegral R (n * R.params.side) (fun _ Y ω => ∏ i ∈ I, meanSiteScore A.score (B i) Y ω) ≤
        ENNReal.ofReal (Real.exp (2 ^ I.card * (I.card.factorial : ℝ) * Real.exp (-(7 * T.gasRate * R.coupling)))) *
          stateLIntegral (nextStepSetup R h T.lam x'') n (fun _ Y ω => ∏ i ∈ I, meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score)
            (open Classical in (B i).image (parentBlock R.params.side)) Y ω))
    (hMs : ∀ (R : StepSetup) (A : ResponseSetup R), A.responseParams = RK → OnStepParameters T y A → R.IsSymmetricWeight →
      ∀ (h : CoarseLabelFacts R) (x'' : ℝ)
      (n : ℕ) [NeZero n], IsBlockTorusSide R.params n →
      stateLIntegral R (n * R.params.side) (fun _ _ _ => 1) = stateLIntegral (nextStepSetup R h T.lam x'') n fun _ _ _ => 1)
    (hLv : ∀ (β : ℝ) (K κ : ℕ) (ρ : ℝ), IsAdmissibleFlow (T.stepParameters y) Ξ β K → 2 ≤ κ → 0 < ρ →
      ρ ≤ cellLength T.side K κ / 4 → ∀ s : ℕ, radiusLevel (T.stepParameters y) β K ρ = some s →
      s ≤ K ∧ ∀ t ≤ s, FitsAtLevel (T.stepParameters y) β K ρ t ∧ t < κ ∧
        2 ^ 13 * rangeAtLevel (T.stepParameters y) β t ≤ (T.side : ℝ) ^ (κ - t) ∧ IsBlockTorusSide (T.stepParameters y) (twoCellSide T.side κ t))
    (hCp : ∀ (β : ℝ) (K : ℕ) (ρ : ℝ), IsAdmissibleFlow (T.stepParameters y) Ξ β K → 0 < ρ →
      ∀ s : ℕ, radiusLevel (T.stepParameters y) β K ρ = some s →
        (couplingFlow (T.stepParameters y) β s).1 ≤ C₁ * (1 + TorusBound.logPos (1 / ρ)))
    (hTp : ∀ (R : StepSetup) (s : R.labels.Ω → ℝ) (n : ℕ) [NeZero n], R.params = T.stepParameters y → y ≤ R.coupling → R.HasExpansions →
      PriceBoundsScore R.params R.coupling R.labels R.clusterFactor R.siteDensity s → IsBlockTorusSide R.params n →
      stateLIntegral R n (fun _ Y ω => Real.exp (∑ z : Y, s (ω z))) ≤
        ENNReal.ofReal (Real.exp (c * (1 + Real.log R.coupling) * (n : ℝ) ^ 4)) * stateLIntegral R n fun _ _ _ => 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ForAllInitialStages T y fun β hL z₀ => ∀ (K κ s : ℕ) (ρ H : ℝ) (Λ : NNReal) (h : EuclideanFourSpace → ℝ),
        IsAdmissibleFlow (T.stepParameters y) Ξ β K → 2 ≤ κ → 0 < ρ → ρ ≤ cellLength T.side K κ / 4 →
        IsLocalizedSource (cellLength T.side K κ) ρ H Λ h → radiusLevel (T.stepParameters y) β K ρ = some s →
        StagesOnFlowUpTo T RK y β hL z₀ K →
        stateLIntegral (flowStages T y β hL z₀ s).1.toStepSetup (twoCellSide T.side κ s) (prodMeanSiteScores T y β hL z₀ K κ s (twoCellSide T.side κ s) h) ≤
          ENNReal.ofReal (Real.exp (C * (1 + cellLength T.side K κ ^ 4 + TorusBound.logPos (1 / cellLength T.side K κ) ^ ((1 : ℝ) / 20)))) *
            stateLIntegral (flowStages T y β hL z₀ s).1.toStepSetup (twoCellSide T.side κ s) fun _ _ _ => 1 := by
  have hfit : (T.stepParameters y).Admissible := hT.fits y hy0
  have hB1 : 1 ≤ T.B := hT.B_ge
  have hL1 : 1 ≤ T.side := by
    have := hT.L_ge
    omega
  have hne : T.side ≠ 0 := by omega
  have hLr : (0 : ℝ) ≤ T.side := by positivity
  have hΞ1 : 1 ≤ Ξ := by linarith
  have hκ : 0 < 7 * T.gasRate := gasRate_pos hT hfit
  set Q : ℝ := Real.exp (7 * T.gasRate * c₅) / (1 - Real.exp (-(7 * T.gasRate * lam))) with hQdef
  have hr1 : Real.exp (-(7 * T.gasRate * lam)) < 1 := by
    rw [Real.exp_lt_one_iff]
    have : 0 < 7 * T.gasRate * lam := by positivity
    linarith
  set ck : ℝ := 2 ^ 16 * ((16 : ℕ).factorial : ℝ) with hck
  set D : ℝ := 100 * (2 ^ 15 * (T.side : ℝ) * (1 + 2 * T.B)) ^ 4 with hD
  have hD0 : 0 ≤ D := by positivity
  set P : ℝ := C₁ ^ ((1 : ℝ) / 20) with hP
  have hf1 : (1 : ℝ) ≤ ((16 : ℕ).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos 16
  set A₀ : ℝ := ck * Q + Real.log ((16 : ℕ).factorial : ℝ) + 1 with hA₀
  have hA₀0 : 0 ≤ A₀ := by positivity
  have hlΞ : 0 ≤ Real.log Ξ := Real.log_nonneg hΞ1
  set B₁ : ℝ := 16 * c * (1 + Real.log Ξ) + 4 * c * D * P with hB₁
  refine ⟨A₀ + B₁, by positivity, fun β hL z₀ hz K κ s ρ H Λ h hd hκ2 hρ0 hρ hsrc hlev hLS => ?_⟩
  set l : ℝ := cellLength T.side K κ with hl
  have hl0 : 0 < l := by linarith
  obtain ⟨s', hlev', hss', hs'K, hnot⟩ := radiusLevel_mono (ρ' := l / 4) hρ hlev
  obtain ⟨-, hall⟩ := hLv β K κ (l / 4) hd hκ2 (by positivity) le_rfl s' hlev'
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hss'
  have hsκ : s + u < κ := (hall (s + u) le_rfl).2.1
  have hbs : IsBlockTorusSide (T.stepParameters y) (twoCellSide T.side κ (s + u)) := (hall (s + u) le_rfl).2.2.2
  have hst : ∀ t ≤ s + u, StageOnFlow T RK y β t (flowStages T y β hL z₀ t) := fun t ht => hLS t (by omega)
  set x := couplingsAlongFlow (T.stepParameters y) β with hxdef
  have hyβ : y ≤ β := hd.coupling_ge 0 (Nat.zero_le _)
  have hfl : ∀ j ≤ K, y ≤ x j := fun j hj => hd.coupling_ge j hj
  have hxl : ∀ j ≤ s + u, (flowStages T y β hL z₀ j).1.coupling = x j := fun j hj => (hst j hj).coupling_eq
  have hxK : y ≤ x (s + u) := hfl _ hs'K
  have hx1 : 1 ≤ x (s + u) := hy1.trans hxK
  have hsum := sum_exp_neg_le (x := x) (lam := lam) (c₅ := c₅) (κ := 7 * T.gasRate) (K := s + u) hlam hκ (by linarith)
    (fun i hi => hS β hyβ (s + u) (fun j hj => hd.coupling_ge j (by omega)) i hi)
  have hsplit := Finset.sum_range_add (fun j => Real.exp (-(7 * T.gasRate * x j))) s u
  have hQ : ∑ j ∈ Finset.range u, Real.exp (-(7 * T.gasRate * (flowStages T y β hL z₀ (s + j)).1.coupling)) ≤ Q := by
    have e : ∑ j ∈ Finset.range u, Real.exp (-(7 * T.gasRate * (flowStages T y β hL z₀ (s + j)).1.coupling)) =
        ∑ j ∈ Finset.range u, Real.exp (-(7 * T.gasRate * x (s + j))) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hxl (s + j) (by have := Finset.mem_range.mp hj; omega)]
    have h0 : 0 ≤ ∑ j ∈ Finset.range s, Real.exp (-(7 * T.gasRate * x j)) :=
      Finset.sum_nonneg fun j _ => (Real.exp_pos _).le
    rw [e]
    linarith
  have hsK := hst (s + u) le_rfl
  have hcoup : (flowStages T y β hL z₀ (s + u)).1.toStepSetup.coupling = x (s + u) := hsK.coupling_eq
  have hTopL : stateLIntegral (flowStages T y β hL z₀ (s + u)).1.toStepSetup (twoCellSide T.side κ (s + u))
        (fun _ Y ω => Real.exp (∑ z : Y, (flowStages T y β hL z₀ (s + u)).2.score (ω z))) ≤
      ENNReal.ofReal (Real.exp (c * (1 + Real.log (x (s + u))) * ((twoCellSide T.side κ (s + u) : ℕ) : ℝ) ^ 4)) *
        stateLIntegral (flowStages T y β hL z₀ (s + u)).1.toStepSetup (twoCellSide T.side κ (s + u)) fun _ _ _ => 1 := by
    have h₁ := hTp (flowStages T y β hL z₀ (s + u)).1.toStepSetup (flowStages T y β hL z₀ (s + u)).2.score (twoCellSide T.side κ (s + u)) rfl
      (by rw [hcoup]; exact hxK) hsK.onFamily.onFamily.isStep.1 hsK.onFamily.admissible.price hbs
    rwa [hcoup] at h₁
  have hcop := sixteen_means_le (T := T) (RK := RK) (y := y) (β := β) (hL := hL) (z₀ := z₀) (s := s) (u := u)
    (n := twoCellSide T.side κ (s + u)) hMj hMs hL1 hbs hst hQ hTopL (twoCellSide T.side κ s) (twoCellSide_eq_fineSide hsκ.le)
    (fun k => weightSupportSites (T.stepParameters y).side (flowStages T y β hL z₀ s).1.depth (twoCellSide T.side κ s)
      (reflectedWeightsAtStage T y β hL z₀ K κ s (twoCellSide T.side κ s) h k))
  refine le_trans hcop (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
  set w : ℝ := TorusBound.logPos (1 / l) ^ ((1 : ℝ) / 20) with hw
  have hw0 : 0 ≤ w := Real.rpow_nonneg (show (0 : ℝ) ≤ TorusBound.logPos (1 / l) from le_max_right _ _) _
  have hl4 : 0 ≤ l ^ 4 := by positivity
  set S : ℝ := 1 + l ^ 4 + w with hSdef
  have hS1 : 1 ≤ S := by linarith
  set n : ℝ := ((twoCellSide T.side κ (s + u) : ℕ) : ℝ) with hn
  have hnE : n = 2 * (T.side : ℝ) ^ (κ - (s + u)) := by
    rw [hn]
    unfold twoCellSide
    push_cast
    ring
  have hE : c * (1 + Real.log (x (s + u))) * n ^ 4 ≤ B₁ * S := by
    have hc16 : 0 ≤ 16 * c * (1 + Real.log Ξ) := by positivity
    rcases hs'K.eq_or_lt with hK | hK
    · have hKκ : K < κ := hK ▸ hsκ
      have hlL : l = (T.side : ℝ) ^ (κ - K) := by
        rw [hl, cellLength_eq hne hKκ.le, levelSpacing_self, mul_one]
      have hn2 : n = 2 * l := by
        rw [hnE, hlL, hK]
      have hxΞ : x (s + u) ≤ Ξ := by
        rw [hK]
        exact hd.coupling_le
      have hlog : Real.log (x (s + u)) ≤ Real.log Ξ := Real.log_le_log (by linarith) hxΞ
      have h1 : c * (1 + Real.log (x (s + u))) * n ^ 4 ≤ 16 * c * (1 + Real.log Ξ) * l ^ 4 := by
        rw [hn2]
        have h2 : c * (1 + Real.log (x (s + u))) ≤ c * (1 + Real.log Ξ) :=
          mul_le_mul_of_nonneg_left (by linarith) hc
        calc c * (1 + Real.log (x (s + u))) * (2 * l) ^ 4 ≤ c * (1 + Real.log Ξ) * (2 * l) ^ 4 :=
              mul_le_mul_of_nonneg_right h2 (by positivity)
          _ = _ := by ring
      have h3 : 16 * c * (1 + Real.log Ξ) * l ^ 4 ≤ 16 * c * (1 + Real.log Ξ) * S :=
        mul_le_mul_of_nonneg_left (by linarith) hc16
      have h4 : 0 ≤ 4 * c * D * P * S := by positivity
      rw [hB₁, add_mul]
      linarith
    · have hnf := hnot (s + u + 1) (by omega) hK
      have hx1' : 1 ≤ x (s + u + 1) := hy1.trans (hfl _ hK)
      have hmv : |x (s + u + 1) - x (s + u)| ≤ 2 * T.B := by
        have hm : |(flowStages T y β hL z₀ (s + u)).1.toStepSetup.nextCoupling - (flowStages T y β hL z₀ (s + u)).1.toStepSetup.coupling| ≤ 2 * T.B :=
          hsK.onFamily.abs_sub_le
        have e₁ : (flowStages T y β hL z₀ (s + u)).1.toStepSetup.nextCoupling = x (s + u + 1) := hsK.nextCoupling_eq
        rw [e₁, hcoup] at hm
        exact hm
      have hr := clusterRange_le_of_step hx1 hx1' (B := T.B) (by linarith) (by linarith [(abs_le.mp hmv).2])
      have hp : s + u + 1 ≤ κ := hsκ
      have hlE : l = (T.side : ℝ) ^ (κ - (s + u + 1)) * levelSpacing T.side K (s + u + 1) := cellLength_eq hne hp
      have ha := levelSpacing_pos hne K (s + u + 1)
      have hlt : (T.side : ℝ) ^ (κ - (s + u + 1)) < 2 ^ 13 * (clusterRange (x (s + u + 1)) : ℝ) := by
        by_contra hge
        push Not at hge
        apply hnf
        show 2 ^ 11 * (clusterRange (x (s + u + 1)) : ℝ) * levelSpacing T.side K (s + u + 1) ≤ l / 4
        have := mul_le_mul_of_nonneg_right hge ha.le
        rw [hlE]
        linarith
      have hne' : κ - (s + u) = κ - (s + u + 1) + 1 := by omega
      have hn14 : n ≤ 2 ^ 14 * (T.side : ℝ) * (clusterRange (x (s + u + 1)) : ℝ) := by
        rw [hnE, hne', pow_succ]
        have := mul_le_mul_of_nonneg_right hlt.le hLr
        linarith
      have hn0 : 0 ≤ n := by rw [hn]; positivity
      have hfar := boundary_term_le hx1 (B := T.B) (by linarith) hLr hn0 hr hn14
      have hroot := coupling_rpow_bound (x := x (s + u)) (by linarith) hC₁ hl0 (hCp β K (l / 4) hd (by positivity) (s + u) hlev')
      have h1 : (1 + Real.log (x (s + u))) * n ^ 4 ≤ D * (P * (4 + w)) :=
        hfar.trans (mul_le_mul_of_nonneg_left hroot hD0)
      have h2 : c * (1 + Real.log (x (s + u))) * n ^ 4 ≤ c * (D * (P * (4 + w))) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left h1 hc
      have h3 : c * (D * (P * (4 + w))) ≤ 4 * c * D * P * S := by
        have h4 : 4 + w ≤ 4 * S := by linarith
        have h5 : 0 ≤ c * D * P := by positivity
        calc c * (D * (P * (4 + w))) = c * D * P * (4 + w) := by ring
          _ ≤ c * D * P * (4 * S) := mul_le_mul_of_nonneg_left h4 h5
          _ = 4 * c * D * P * S := by ring
      have h6 : 0 ≤ 16 * c * (1 + Real.log Ξ) * S := by positivity
      rw [hB₁, add_mul]
      linarith
  have hA : A₀ ≤ A₀ * S := le_mul_of_one_le_right hA₀0 hS1
  have e₁ : Real.exp (ck * Q) * (((16 : ℕ).factorial : ℝ) * Real.exp 1) * Real.exp (c * (1 + Real.log (x (s + u))) * n ^ 4) =
      Real.exp (A₀ + c * (1 + Real.log (x (s + u))) * n ^ 4) := by
    have e₂ : ((16 : ℕ).factorial : ℝ) = Real.exp (Real.log ((16 : ℕ).factorial : ℝ)) :=
      (Real.exp_log (by positivity)).symm
    rw [hA₀, Real.exp_add, Real.exp_add, Real.exp_add, ← e₂]
    ring
  rw [e₁]
  apply Real.exp_le_exp.mpr
  rw [add_mul]
  linarith
end MainBound
theorem scoreMeanBound_holds (hLv : levelsBelowRadiusStatement) (hCp : couplingAtRadiusLevelStatement)
    (hSc : scoreExpMeanBoundStatement) (hSl : FlowDescendsLinearly)
    (hMaj : stepMajorantBoundOfSymmetric) (hMass : StateMassPreservedByStep) :
    scoreMeanBoundStatement := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, hr₁, gV⟩ := hLv a ha
  obtain ⟨L₂, r₂, C₂, hr₂, gC⟩ := hCp a ha
  obtain ⟨L₃, r₃, hr₃, gS⟩ := hSl a ha
  obtain ⟨r₄, hr₄, gJ⟩ := hMaj
  obtain ⟨r₅, hr₅, gA⟩ := hMass
  refine ⟨max (max L₁ L₂) L₃, fun c => min (r₁ c) (min (r₂ c) (min (r₃ c) (min (r₄ c) (r₅ c)))), max C₁ C₂,
    fun c => lt_min (hr₁ c) (lt_min (hr₂ c) (lt_min (hr₃ c) (lt_min (hr₄ c) (hr₅ c)))),
    fun L hLo hLL T hTa hTL hT hCS hOn hrt hCd Kr => ?_⟩
  have t₁ := hrt.trans (min_le_left _ _)
  have u₁ := hrt.trans (min_le_right _ _)
  have t₂ := u₁.trans (min_le_left _ _)
  have u₂ := u₁.trans (min_le_right _ _)
  have t₃ := u₂.trans (min_le_left _ _)
  have u₃ := u₂.trans (min_le_right _ _)
  have t₄ := u₃.trans (min_le_left _ _)
  have t₅ := u₃.trans (min_le_right _ _)
  have hL₁ : L₁ ≤ L := (le_trans (le_max_left _ _) (le_max_left _ _)).trans hLL
  have hL₂ : L₂ ≤ L := (le_trans (le_max_right _ _) (le_max_left _ _)).trans hLL
  have hL₃ : L₃ ≤ L := (le_max_right _ _).trans hLL
  obtain ⟨lam, c₅, hlam, gS⟩ := gS L hLo hL₃
  obtain ⟨y₁, gV⟩ := gV L hLo hL₁ T hTa hTL hT hCS hOn t₁ ((le_max_left _ _).trans hCd)
  obtain ⟨y₂, gC⟩ := gC L hLo hL₂ T hTa hTL hT hCS hOn t₂ ((le_max_right _ _).trans hCd)
  obtain ⟨y₃, gS⟩ := gS T hTa hTL hT t₃
  obtain ⟨y₄, gJ⟩ := gJ T hT t₄ Kr
  obtain ⟨y₅, gA⟩ := gA T hT t₅ Kr
  obtain ⟨c, hc, y₆, gT⟩ := hSc T hT
  refine ⟨max (max (max y₁ y₂) (max y₃ y₄)) (max (max y₅ y₆) (max T.floorMin 1)), fun y hy hRet hW Ξ hΞ => ?_⟩
  have e₀ : max (max y₁ y₂) (max y₃ y₄) ≤ y := (le_max_left _ _).trans hy
  have e₀' : max (max y₅ y₆) (max T.floorMin 1) ≤ y := (le_max_right _ _).trans hy
  have e₁ : y₁ ≤ y := (le_trans (le_max_left _ _) (le_max_left _ _)).trans e₀
  have e₂ : y₂ ≤ y := (le_trans (le_max_right _ _) (le_max_left _ _)).trans e₀
  have e₃ : y₃ ≤ y := (le_trans (le_max_left _ _) (le_max_right _ _)).trans e₀
  have e₄ : y₄ ≤ y := (le_trans (le_max_right _ _) (le_max_right _ _)).trans e₀
  have e₅ : y₅ ≤ y := (le_trans (le_max_left _ _) (le_max_left _ _)).trans e₀'
  have e₆ : y₆ ≤ y := (le_trans (le_max_right _ _) (le_max_left _ _)).trans e₀'
  have e₇ : T.floorMin ≤ y := (le_trans (le_max_left _ _) (le_max_right _ _)).trans e₀'
  have e₈ : 1 ≤ y := (le_trans (le_max_right _ _) (le_max_right _ _)).trans e₀'
  obtain ⟨C, hC, gC⟩ := gC y e₂ hRet hW Ξ hΞ
  exact bound_at_floor (RK := Kr) hT e₇ e₈ hΞ hlam (gS y e₃ hRet hW) hc hC
    (fun R A hK hAt => gJ y e₄ R A hK hAt) (fun R A hK hAt => gA y e₅ R A hK hAt)
    (fun β K κ ρ hd h2 h0 h1 s hs => gV y e₁ hRet hW Ξ β K κ ρ hd h2 h0 h1 s hs)
    (fun β K ρ hd h0 s hs => (gC β K ρ hd h0).1 s hs)
    (fun R s n _ hℓ hyx hrow hsp hbs => gT y R s n e₆ hℓ hyx hrow hsp hbs)
end YangMills.Construction.SmallTorusCopies
end
