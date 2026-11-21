import YangMills.Construction.ColdChainAtEveryLevel.CellContexts
import YangMills.Construction.ColdChainAtEveryLevel.DerivativesOfTheChainTotal
import YangMills.Construction.ColdChainAtEveryLevel.EvaluationsOfAComplexChain
import YangMills.Construction.ColdChainAtEveryLevel.MixedDerivativeFromSecondDifferences
import YangMills.Construction.ColdChainAtEveryLevel.SmallCoordinatesAreRegular
import YangMills.Construction.ColdChainAtEveryLevel.TermsAtACellAreAnalytic
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator Topology
open Metric Filter
namespace YangMills.Construction.ChartActionDerivatives
open BlockAverages CellSpans Analytic CoordinateSeminorms CellSources ComplexCells ComplexLevels HullBounds
  ComplexDifferences CellBounds CellContexts LevelRecursion ComplexifiedQuaternions
variable {F : BlockFrame} {k : ℕ}
section Cells
theorem analyticAt_const_add_sum_smul {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (c₀ : E) (c : Fin k → E)
    (t₀ : Fin k → ℂ) : AnalyticAt ℂ (fun w : Fin k → ℂ => c₀ + ∑ l, w l • c l) t₀ := by
  refine analyticAt_const.add (Finset.analyticAt_fun_sum _ fun l _ => ?_)
  exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) l).analyticAt t₀).smul analyticAt_const
theorem spanLocalNorm_add_single_le (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (A : Fin k → ChainChart F)
    (t : Fin k → ℂ) (τ : ℂ) (l₀ : Fin k) (z : F.Cell) :
    spanLocalNorm S R U A (t + τ • (Pi.single l₀ 1 : Fin k → ℂ)) z ≤
      spanLocalNorm S R U A t z + ‖τ‖ * localNorm S R (A l₀) (constOneWeights F) z := by
  classical
  unfold spanLocalNorm
  have hn : ∀ l, 0 ≤ localNorm S R (A l) (constOneWeights F) z := fun l => Real.sqrt_nonneg _
  have h1 : ∀ l, ‖(t + τ • (Pi.single l₀ 1 : Fin k → ℂ)) l‖ * localNorm S R (A l) (constOneWeights F) z ≤
      ‖t l‖ * localNorm S R (A l) (constOneWeights F) z +
        (if l = l₀ then ‖τ‖ * localNorm S R (A l) (constOneWeights F) z else 0) := by
    intro l
    by_cases h : l = l₀
    · subst h
      simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, if_true]
      rw [← add_mul]
      exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (hn _)
    · simp [h]
  have h2 := Finset.sum_le_sum fun l (_ : l ∈ Finset.univ) => h1 l
  rw [Finset.sum_add_distrib] at h2
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
  linarith
theorem analyticAt_complexCellTerms (han : complexCellTermsAnalyticStatement) (hamb : IsAdmissibleAmbient F)
    (hodd : Odd F.blockSide) (a : ℝ) {S : Finset F.Cell} {z : F.Cell} {R : F.FieldChain} (V : F.GaugeField F.top)
    {C₀ s y : ℝ} (ctx : CellHypotheses S z R C₀ s y) (U : ChainChart F) (A : Fin k → ChainChart F) {t₀ : Fin k → ℂ}
    (h0 : spanLocalNorm S R U A t₀ z ≤ y) :
    AnalyticAt ℂ (fun t => complexCellTerms a S R (spanChart U A t) V z) t₀ := by
  have hL1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  have hy := ctx.small
  have hy0 := hy.pos
  have hy1 := hy.le_bound
  have hsz := sourceBounds_spanChart hodd R U A t₀ h0
  obtain ⟨hss, hball⟩ := deviationBall_of_finsetLpNorm_le (ctx.level_le (spanChart U A t₀)) hsz.base_le hsz.upper_le
    (by linarith)
  have hH0 := hullBondCount_nonneg F.blockSide
  have ha := hy.count_le_radius
  have hsmall : 8 * (F.blockSide : ℝ) * (hullBondCount F.blockSide * (8 * y)) ≤ 1 / 1024 := by
    have h1 : 48 * (48 * hullBondCount F.blockSide + 1) * y * (8192 * (F.blockSide : ℝ)) ≤ 1 := by
      unfold hullBallRadius at ha
      rw [le_div_iff₀ (by positivity)] at ha
      exact ha
    have h2 : 0 ≤ hullBondCount F.blockSide * y * F.blockSide := by positivity
    have e1 : 48 * (48 * hullBondCount F.blockSide + 1) * y * (8192 * (F.blockSide : ℝ)) =
        48 * 48 * 8192 * (hullBondCount F.blockSide * y * F.blockSide) + 48 * 8192 * (y * F.blockSide) := by ring
    have h3 : 0 ≤ y * (F.blockSide : ℝ) := by positivity
    have e2 : 8 * (F.blockSide : ℝ) * (hullBondCount F.blockSide * (8 * y)) =
        64 * (hullBondCount F.blockSide * y * F.blockSide) := by ring
    rw [e2]
    rw [e1] at h1
    linarith
  refine (han F S R V a hodd hamb).2 k (spanChart U A) t₀ z (8 * y) (C₀ * s) (by positivity) (by linarith)
    ((ctx.const_mul_scale_le).trans (by linarith)) hsmall ?_ ?_ ?_ ?_ hball.norm_deviation_le ?_
  · intro b _
    have e : (fun w => complexifiedImaginary ((spanChart U A w).re.fine b.1 b.2) ((spanChart U A w).im.fine b.1 b.2)) =
        fun w => ofQuat (U.fine b.1 b.2 : ℍ[ℝ]) + ∑ l, w l • ofQuat ((A l).fine b.1 b.2 : ℍ[ℝ]) := by
      funext w
      exact baseSource_spanChart U A w b.1 b.2
    rw [e]
    exact analyticAt_const_add_sum_smul _ _ _
  · intro b hb
    exact (hss.base_le b hb).trans (by norm_num)
  · intro j _ b _
    have e : (fun w => complexifiedImaginary ((spanChart U A w).re.coarse j b.1 b.2)
        ((spanChart U A w).im.coarse j b.1 b.2)) =
        fun w => ofQuat (U.coarse j b.1 b.2 : ℍ[ℝ]) + ∑ l, w l • ofQuat ((A l).coarse j b.1 b.2 : ℍ[ℝ]) := by
      funext w
      exact upperSource_spanChart U A w ⟨j, b⟩
    rw [e]
    exact analyticAt_const_add_sum_smul _ _ _
  · intro j hj b hb
    exact (hss.upper_le _ (mem_lowerBonds hj hb)).trans (by norm_num)
  · intro j hj c hc h hh π
    refine (ctx.near j hj c hc h hh π).trans ?_
    have hCs : 0 ≤ C₀ * s := mul_nonneg ctx.const_pos.le ctx.scale_pos.le
    have h3 : ((1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1))) ^ 2 ≤ 1 :=
      pow_le_one₀ (by positivity) (inv_pow_le_one hodd.pos _)
    exact mul_le_of_le_one_right hCs h3
end Cells
section Mixed
theorem continuous_spanLocalNorm (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (A : Fin k → ChainChart F)
    (z : F.Cell) : Continuous fun t : Fin k → ℂ => spanLocalNorm S R U A t z := by
  unfold spanLocalNorm
  fun_prop
set_option maxHeartbeats 2000000 in
theorem norm_iteratedFDeriv_complexCellTerms_le_of_pos (hmix : mixedDerivativeOfSecondDifferencesStatement)
    (han : complexCellTermsAnalyticStatement) (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (h2 : 2 ≤ F.blockSide) (a : ℝ) {S : Finset F.Cell} {z : F.Cell} {R : F.FieldChain} (V : F.GaugeField F.top)
    {C₀ s y : ℝ} (ctx : CellHypotheses S z R C₀ s y) (U : ChainChart F) {k' : ℕ} (A : Fin (k' + 2) → ChainChart F)
    (hU : localNorm S R U (constOneWeights F) z ≤ y / 2) {l1 l2 : Fin (k' + 2)} (hne : l1 ≠ l2) {φ : F.Cell → ℝ}
    {del θ : ℝ} (hdel : 0 ≤ del) (hφ : ∀ y y', |φ y - φ y'| ≤ del * cellSupDist y y') (hθ : |θ| ≤ 1 / 8)
    (p : F.Site 0) {ε : ℝ} (hε : 0 < ε) :
    ‖iteratedFDeriv ℂ (k' + 2) (fun t => complexCellTerms a S R (spanChart U A t) V z) 0 (fun l => Pi.single l 1)‖ ≤
      cauchyHalvingConstant k' * (cellSecondDiffConst (hullFactor F.blockSide) (200000 * (F.blockSide : ℝ) ^ 2)
          (1 / (2 * (200000 * (F.blockSide : ℝ) ^ 2))) a *
          9 * Real.exp (2 * del) * localNorm S R (A l1) (classWeight F φ θ p) z *
          localNorm S R (A l2) (invertedWeights (classWeight F φ θ p)) z) / 1 ^ k' *
        ∏ l ∈ (Finset.univ.erase l1).erase l2,
          ((localNorm S R (A l) (constOneWeights F) z + ε) / (y / (4 * ((k' : ℝ) + 2)))) := by
  have hy0 : 0 < y := ctx.small.pos
  set near : Fin (k' + 2) → ℝ := fun l => localNorm S R (A l) (constOneWeights F) z with hnear
  have hnear0 : ∀ l, 0 ≤ near l := fun l => Real.sqrt_nonneg _
  set ρ := y / (4 * ((k' : ℝ) + 2)) with hρ
  have hρ0 : 0 < ρ := by positivity
  set r : Fin (k' + 2) → ℝ := fun l => ρ / (near l + ε) with hr
  have hd : ∀ l, 0 < near l + ε := fun l => by
    have := hnear0 l
    linarith
  have hr0 : ∀ l, 0 < r l := fun l => div_pos hρ0 (hd l)
  set G : (Fin (k' + 2) → ℂ) → ℂ := fun t => complexCellTerms a S R (spanChart U A t) V z with hG
  set Ω : Set (Fin (k' + 2) → ℂ) := {t | spanLocalNorm S R U A t z < y} with hΩ
  have hΩo : IsOpen Ω := isOpen_lt (continuous_spanLocalNorm S R U A z) continuous_const
  have hGan : ∀ t ∈ Ω, AnalyticAt ℂ G t := fun t ht =>
    analyticAt_complexCellTerms han hamb hodd a V ctx U A (le_of_lt ht)
  set T : (Fin (k' + 2) → ℂ) →L[ℂ] (Fin (k' + 2) → ℂ) :=
    ContinuousLinearMap.pi fun l => (r l : ℂ) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (k' + 2) => ℂ) l
    with hT
  have hTa : ∀ t l, T t l = (r l : ℂ) * t l := fun t l => by
    simp [hT]
  have hnear_T : ∀ t ∈ ball (0 : Fin (k' + 2) → ℂ) 1, spanLocalNorm S R U A (T t) z ≤ 3 * y / 4 := by
    intro t ht
    have ht1 : ‖t‖ < 1 := by simpa using ht
    have h1 : ∀ l ∈ (Finset.univ : Finset (Fin (k' + 2))), ‖T t l‖ * near l ≤ ρ := by
      intro l _
      rw [hTa, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hr0 l)]
      have h3 : ‖t l‖ ≤ 1 := (norm_le_pi_norm t l).trans ht1.le
      have h4 : r l * near l ≤ ρ := by
        simp only [hr]
        rw [div_mul_eq_mul_div, div_le_iff₀ (hd l)]
        have := hnear0 l
        nlinarith
      calc r l * ‖t l‖ * near l = (r l * near l) * ‖t l‖ := by ring
        _ ≤ ρ * 1 := mul_le_mul h4 h3 (norm_nonneg _) hρ0.le
        _ = ρ := mul_one _
    have h5 := Finset.sum_le_card_nsmul _ _ _ h1
    rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h5
    have e : (((k' + 2 : ℕ)) : ℝ) * ρ = y / 4 := by
      rw [hρ]
      push_cast
      field_simp
    rw [e] at h5
    unfold spanLocalNorm
    linarith
  have hball : ∀ t ∈ ball (0 : Fin (k' + 2) → ℂ) 1, T t ∈ Ω := fun t ht => by
    have := hnear_T t ht
    show spanLocalNorm S R U A (T t) z < y
    linarith
  set Gt : (Fin (k' + 2) → ℂ) → ℂ := G ∘ T with hGt
  have hGtan : AnalyticOnNhd ℂ Gt (ball 0 1) := fun t ht =>
    (hGan (T t) (hball t ht)).comp (T.analyticAt t)
  set v : Fin (k' + 2) → Fin (k' + 2) → ℂ := fun l => Pi.single l ((r l : ℂ)⁻¹) with hv
  have hTv : ∀ l, T (v l) = Pi.single l 1 := by
    intro l
    funext m
    rw [hTa]
    by_cases h : m = l
    · subst h
      have : (r m : ℂ) ≠ 0 := by exact_mod_cast (hr0 m).ne'
      simp [hv, this]
    · simp [hv, Pi.single_eq_of_ne h]
  set Mc := cellSecondDiffConst (hullFactor F.blockSide) (200000 * (F.blockSide : ℝ) ^ 2)
    (1 / (2 * (200000 * (F.blockSide : ℝ) ^ 2))) a with hMc
  have hMc0 : 0 ≤ Mc := by
    have hF := hullFactor_nonneg F.blockSide
    rw [hMc]
    unfold cellSecondDiffConst secondDiffConst
    positivity
  set N₁ := localNorm S R (A l1) (classWeight F φ θ p) z with hN₁
  set N₂ := localNorm S R (A l2) (invertedWeights (classWeight F φ θ p)) z with hN₂
  have hN₁0 : 0 ≤ N₁ := Real.sqrt_nonneg _
  have hN₂0 : 0 ≤ N₂ := Real.sqrt_nonneg _
  set M := Mc * 9 * Real.exp (2 * del) * N₁ * N₂ with hM
  have hM0 : 0 ≤ M := by positivity
  have hsd : ∀ t ∈ ball (0 : Fin (k' + 2) → ℂ) 1, ∃ δ : ℝ, 0 < δ ∧ ∀ τ₁ τ₂ : ℂ, ‖τ₁‖ < δ → ‖τ₂‖ < δ →
      ‖Gt (t + τ₁ • v l1 + τ₂ • v l2) - Gt (t + τ₁ • v l1) - Gt (t + τ₂ • v l2) + Gt t‖ ≤ M * ‖τ₁‖ * ‖τ₂‖ := by
    intro t ht
    have hT3 := hnear_T t ht
    have hnn : 0 < near l1 + near l2 + 1 := by
      have := hnear0 l1
      have := hnear0 l2
      linarith
    refine ⟨y / (8 * (near l1 + near l2 + 1)), by positivity, fun τ₁ τ₂ h₁ h₂ => ?_⟩
    have hδ₁ : ‖τ₁‖ * near l1 ≤ y / 8 := by
      have h3 : near l1 ≤ near l1 + near l2 + 1 := by
        have := hnear0 l2
        linarith
      calc ‖τ₁‖ * near l1 ≤ y / (8 * (near l1 + near l2 + 1)) * (near l1 + near l2 + 1) :=
            mul_le_mul h₁.le h3 (hnear0 _) (by positivity)
        _ = y / 8 := by field_simp
    have hδ₂ : ‖τ₂‖ * near l2 ≤ y / 8 := by
      have h3 : near l2 ≤ near l1 + near l2 + 1 := by
        have := hnear0 l1
        linarith
      calc ‖τ₂‖ * near l2 ≤ y / (8 * (near l1 + near l2 + 1)) * (near l1 + near l2 + 1) :=
            mul_le_mul h₂.le h3 (hnear0 _) (by positivity)
        _ = y / 8 := by field_simp
    set t' := T t with ht'
    have m₁ := spanLocalNorm_add_single_le S R U A t' τ₁ l1 z
    have m₂ := spanLocalNorm_add_single_le S R U A t' τ₂ l2 z
    have m₃ := spanLocalNorm_add_single_le S R U A (t' + τ₁ • (Pi.single l1 1 : Fin (k' + 2) → ℂ)) τ₂ l2 z
    have hb := norm_second_diff_complexCellTerms_le hamb hodd h2 a V ctx U A t' τ₁ τ₂ l1 l2 (by linarith)
      (by linarith) (by linarith) (by linarith) hdel hφ hθ p
    have e₁ : T (t + τ₁ • v l1 + τ₂ • v l2) =
        t' + τ₁ • (Pi.single l1 1 : Fin (k' + 2) → ℂ) + τ₂ • (Pi.single l2 1 : Fin (k' + 2) → ℂ) := by
      rw [map_add, map_add, map_smul, map_smul, hTv, hTv]
    have e₂ : T (t + τ₁ • v l1) = t' + τ₁ • (Pi.single l1 1 : Fin (k' + 2) → ℂ) := by
      rw [map_add, map_smul, hTv]
    have e₃ : T (t + τ₂ • v l2) = t' + τ₂ • (Pi.single l2 1 : Fin (k' + 2) → ℂ) := by
      rw [map_add, map_smul, hTv]
    simp only [hGt, Function.comp_apply, e₁, e₂, e₃, hG]
    refine hb.trans (le_of_eq ?_)
    have hN : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by
      have : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
      positivity
    have eN : ((F.blockSide : ℝ) ^ F.top) ^ (-θ) * ((F.blockSide : ℝ) ^ F.top) ^ θ = 1 := by
      rw [← Real.rpow_add hN]
      simp
    have eE : Real.exp (del - φ z) * Real.exp (del + φ z) = Real.exp (2 * del) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc _ = Mc * 9 * (Real.exp (del - φ z) * Real.exp (del + φ z)) *
          (((F.blockSide : ℝ) ^ F.top) ^ (-θ) * ((F.blockSide : ℝ) ^ F.top) ^ θ) * (‖τ₁‖ * N₁) * (‖τ₂‖ * N₂) := by
          ring
      _ = _ := by
        rw [eN, eE, hM]
        ring
  have hm := hmix (k' + 2) k' Gt 1 M v l1 l2 hne one_pos hM0 hGtan hsd
  have h0Ω : (0 : Fin (k' + 2) → ℂ) ∈ Ω := by
    show spanLocalNorm S R U A 0 z < y
    have : spanLocalNorm S R U A 0 z = localNorm S R U (constOneWeights F) z := by
      simp [spanLocalNorm]
    rw [this]
    linarith
  have hcd : ContDiffOn ℂ (k' + 2 : ℕ) G Ω := fun x hx => (hGan x hx).contDiffAt.contDiffWithinAt
  have hs' : IsOpen (T ⁻¹' Ω) := hΩo.preimage T.continuous
  have hmem : (0 : Fin (k' + 2) → ℂ) ∈ T ⁻¹' Ω := by
    simpa using h0Ω
  have h3 := T.iteratedFDerivWithin_comp_right hcd hΩo.uniqueDiffOn hs'.uniqueDiffOn hmem (i := k' + 2) le_rfl
  rw [iteratedFDerivWithin_of_isOpen (k' + 2) hs' hmem, map_zero,
    iteratedFDerivWithin_of_isOpen (k' + 2) hΩo h0Ω] at h3
  have e4 : iteratedFDeriv ℂ (k' + 2) Gt 0 v = iteratedFDeriv ℂ (k' + 2) G 0 (fun l => Pi.single l 1) := by
    rw [show Gt = G ∘ T from rfl, h3]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext l
    exact hTv l
  rw [← e4]
  refine hm.trans (le_of_eq ?_)
  congr 1
  refine Finset.prod_congr rfl fun l _ => ?_
  have e5 : ‖v l‖ = (r l)⁻¹ := by
    simp only [hv]
    rw [Pi.norm_single, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hr0 l)]
  rw [e5]
  simp only [hr]
  rw [inv_div]
end Mixed
section Limit
theorem norm_iteratedFDeriv_complexCellTerms_le (hmix : mixedDerivativeOfSecondDifferencesStatement)
    (han : complexCellTermsAnalyticStatement) (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (h2 : 2 ≤ F.blockSide) (a : ℝ) {S : Finset F.Cell} {z : F.Cell} {R : F.FieldChain} (V : F.GaugeField F.top)
    {C₀ s y : ℝ} (ctx : CellHypotheses S z R C₀ s y) (U : ChainChart F) {k' : ℕ} (A : Fin (k' + 2) → ChainChart F)
    (hU : localNorm S R U (constOneWeights F) z ≤ y / 2) {l1 l2 : Fin (k' + 2)} (hne : l1 ≠ l2) {φ : F.Cell → ℝ}
    {del θ : ℝ} (hdel : 0 ≤ del) (hφ : ∀ y y', |φ y - φ y'| ≤ del * cellSupDist y y') (hθ : |θ| ≤ 1 / 8)
    (p : F.Site 0) :
    ‖iteratedFDeriv ℂ (k' + 2) (fun t => complexCellTerms a S R (spanChart U A t) V z) 0 (fun l => Pi.single l 1)‖ ≤
      cauchyHalvingConstant k' * (cellSecondDiffConst (hullFactor F.blockSide) (200000 * (F.blockSide : ℝ) ^ 2)
          (1 / (2 * (200000 * (F.blockSide : ℝ) ^ 2))) a *
          9 * Real.exp (2 * del) * localNorm S R (A l1) (classWeight F φ θ p) z *
          localNorm S R (A l2) (invertedWeights (classWeight F φ θ p)) z) / 1 ^ k' *
        ∏ l ∈ (Finset.univ.erase l1).erase l2,
          ((localNorm S R (A l) (constOneWeights F) z + 0) / (y / (4 * ((k' : ℝ) + 2)))) := by
  set B := cauchyHalvingConstant k' * (cellSecondDiffConst (hullFactor F.blockSide)
          (200000 * (F.blockSide : ℝ) ^ 2) (1 / (2 * (200000 * (F.blockSide : ℝ) ^ 2))) a *
          9 * Real.exp (2 * del) * localNorm S R (A l1) (classWeight F φ θ p) z *
          localNorm S R (A l2) (invertedWeights (classWeight F φ θ p)) z) / 1 ^ k' with hB
  have hcont : Continuous fun ε : ℝ => B * ∏ l ∈ (Finset.univ.erase l1).erase l2,
      ((localNorm S R (A l) (constOneWeights F) z + ε) / (y / (4 * ((k' : ℝ) + 2)))) := by
    refine continuous_const.mul (continuous_finsetProd _ fun l _ => ?_)
    exact (continuous_const.add continuous_id).div_const _
  have ht : Tendsto (fun ε : ℝ => B * ∏ l ∈ (Finset.univ.erase l1).erase l2,
      ((localNorm S R (A l) (constOneWeights F) z + ε) / (y / (4 * ((k' : ℝ) + 2))))) (𝓝[>] 0)
      (𝓝 (B * ∏ l ∈ (Finset.univ.erase l1).erase l2,
        ((localNorm S R (A l) (constOneWeights F) z + 0) / (y / (4 * ((k' : ℝ) + 2)))))) :=
    (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto ht ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact norm_iteratedFDeriv_complexCellTerms_le_of_pos hmix han hamb hodd h2 a V ctx U A hU hne hdel hφ hθ p hε
end Limit
section Extension
variable {m : ℕ}
theorem exists_isBoundedHolomorphicExtension {f : (Fin m → ℝ) → ℝ} {g : (Fin m → ℂ) → ℂ} (hg : AnalyticAt ℂ g 0)
    (he : ∀ᶠ t in 𝓝 (0 : Fin m → ℝ), (f t : ℂ) = g (complexifyCLM t)) :
    ∃ ρ M : ℝ, IsBoundedHolomorphicExtension Complex.ofRealCLM f g ρ M := by
  have h1 : ∀ᶠ x in 𝓝 (0 : Fin m → ℂ), AnalyticAt ℂ g x := hg.eventually_analyticAt
  have h2 : ∀ᶠ x in 𝓝 (0 : Fin m → ℂ), ‖g x‖ < ‖g 0‖ + 1 :=
    hg.continuousAt.norm.eventually_lt continuousAt_const (by linarith)
  obtain ⟨ρ₁, hρ₁, h3⟩ := Metric.eventually_nhds_iff_ball.1 (h1.and h2)
  obtain ⟨ρ₂, hρ₂, h4⟩ := Metric.eventually_nhds_iff_ball.1 he
  refine ⟨min ρ₁ ρ₂, ‖g 0‖ + 1, lt_min hρ₁ hρ₂, fun x hx => (h3 x (ball_subset_ball (min_le_left _ _) hx)).1,
    fun x hx => (h3 x (ball_subset_ball (min_le_left _ _) hx)).2.le, fun t ht => ?_⟩
  exact h4 t (by
    rw [mem_ball_zero_iff]
    exact lt_of_lt_of_le ht (min_le_right _ _))
theorem ofReal_iteratedFDeriv_eq {f : (Fin m → ℝ) → ℝ} {g : (Fin m → ℂ) → ℂ} {ρ M : ℝ}
    (h : IsBoundedHolomorphicExtension Complex.ofRealCLM f g ρ M) :
    ((iteratedFDeriv ℝ m f 0 (fun l => Pi.single l 1) : ℝ) : ℂ) =
      iteratedFDeriv ℂ m g 0 (fun l => Pi.single l 1) := by
  have hP : ∀ a : ℝ, Complex.reCLM (Complex.ofRealCLM a) = a := fun a => by simp
  have hf : ContDiffAt ℝ m f 0 := (h.analyticAt_of_leftInverse Complex.reCLM hP).contDiffAt
  have h0 : (0 : Fin m → ℂ) ∈ ball (0 : Fin m → ℂ) ρ := by simpa using h.radius_pos
  have hgC : ContDiffAt ℂ m g 0 := (h.analyticOnNhd 0 h0).contDiffAt
  have e1 : Complex.ofRealCLM (iteratedFDeriv ℝ m f 0 (fun l => Pi.single l 1)) =
      iteratedFDeriv ℝ m (Complex.ofRealCLM ∘ f) 0 (fun l => Pi.single l 1) := by
    rw [Complex.ofRealCLM.iteratedFDeriv_comp_left hf le_rfl]
    rfl
  have e2 : iteratedFDeriv ℝ m (Complex.ofRealCLM ∘ f) 0 = iteratedFDeriv ℝ m (g ∘ complexifyCLM) 0 :=
    (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) h.eventuallyEq_comp m).self_of_nhds
  have hs : IsOpen (ball (0 : Fin m → ℂ) ρ) := isOpen_ball
  have hs' : IsOpen ((complexifyCLM (ι := Fin m)) ⁻¹' ball (0 : Fin m → ℂ) ρ) :=
    hs.preimage (complexifyCLM (ι := Fin m)).continuous
  have hcd : ContDiffOn ℝ m g (ball (0 : Fin m → ℂ) ρ) := fun x hx =>
    ((h.analyticOnNhd x hx).contDiffAt.restrict_scalars ℝ).contDiffWithinAt
  have hmem : (0 : Fin m → ℝ) ∈ (complexifyCLM (ι := Fin m)) ⁻¹' ball (0 : Fin m → ℂ) ρ := by
    simpa using h0
  have e3 : iteratedFDeriv ℝ m (g ∘ complexifyCLM) 0 =
      (iteratedFDeriv ℝ m g 0).compContinuousLinearMap fun _ => complexifyCLM (ι := Fin m) := by
    have h3 := (complexifyCLM (ι := Fin m)).iteratedFDerivWithin_comp_right hcd hs.uniqueDiffOn hs'.uniqueDiffOn
      hmem (i := m) le_rfl
    rw [iteratedFDerivWithin_of_isOpen m hs' hmem, map_zero, iteratedFDerivWithin_of_isOpen m hs h0] at h3
    exact h3
  have e4 : iteratedFDeriv ℝ m g 0 = (iteratedFDeriv ℂ m g 0).restrictScalars ℝ :=
    (hgC.restrictScalars_iteratedFDeriv (𝕜 := ℝ)).symm
  have e5 : ((iteratedFDeriv ℝ m f 0 (fun l => Pi.single l 1) : ℝ) : ℂ) =
      Complex.ofRealCLM (iteratedFDeriv ℝ m f 0 (fun l => Pi.single l 1)) := rfl
  rw [e5, e1, e2, e3, e4]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, ContinuousMultilinearMap.coe_restrictScalars]
  congr 1
  funext l
  funext i
  by_cases hh : i = l
  · subst hh
    simp [complexifyCLM_apply]
  · simp [complexifyCLM_apply, Pi.single_eq_of_ne hh]
end Extension
section Total
theorem supWeightedNorm_chartShiftMulti_le {S : Finset F.Cell} (hL : 0 < F.blockSide) {del : ℝ} (hdel : 0 ≤ del)
    (R : F.FieldChain) (U : ChainChart F) (A : Fin k → ChainChart F) (t : Fin k → ℝ) :
    supWeightedNorm S del R (chartShiftMulti U A t) ≤
      supWeightedNorm S del R U + ∑ l, |t l| * supWeightedNorm S del R (A l) := by
  classical
  set mc : Finset (Fin k) → ChainChart F := fun s =>
    ⟨fun x i => U.fine x i + ∑ l ∈ s, t l • (A l).fine x i,
      fun j y i => U.coarse j y i + ∑ l ∈ s, t l • (A l).coarse j y i⟩ with hmc
  have h0 : mc ∅ = U := by
    apply chainChart_ext
    · funext x i
      simp [hmc]
    · funext j y i
      simp [hmc]
  have hins : ∀ (a : Fin k) (s : Finset (Fin k)), a ∉ s → mc (insert a s) = chartMove (mc s) (A a) (t a) := by
    intro a s ha
    apply chainChart_ext
    · funext x i
      simp only [hmc, chartMove, Finset.sum_insert ha]
      abel
    · funext j y i
      simp only [hmc, chartMove, Finset.sum_insert ha]
      abel
  have key : ∀ s : Finset (Fin k), supWeightedNorm S del R (mc s) ≤
      supWeightedNorm S del R U + ∑ l ∈ s, |t l| * supWeightedNorm S del R (A l) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [h0]
    | insert a s ha ih =>
      rw [hins a s ha, Finset.sum_insert ha]
      have := supWeightedNorm_chartMove_le S hL del hdel R (mc s) (A a) (t a)
      linarith
  exact key Finset.univ
theorem spanChart_complexify (U : ChainChart F) (A : Fin k → ChainChart F) (t : Fin k → ℝ) :
    spanChart U A (complexifyCLM t) = realChart (chartShiftMulti U A t) := by
  have e1 : chartShiftMulti U A (fun l => (complexifyCLM t l).re) = chartShiftMulti U A t := by
    congr 1
  have e2 : chartShiftMulti (zeroChart F) A (fun l => (complexifyCLM t l).im) =
      (⟨fun _ _ => 0, fun _ _ _ => 0⟩ : ChainChart F) := by
    apply chainChart_ext
    · funext x i
      simp [chartShiftMulti, zeroChart, complexifyCLM_apply]
    · funext j y i
      simp [chartShiftMulti, zeroChart, complexifyCLM_apply]
  simp only [spanChart, realChart, e1, e2]
theorem spanLocalNorm_zero (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (A : Fin k → ChainChart F)
    (z : F.Cell) : spanLocalNorm S R U A 0 z = localNorm S R U (constOneWeights F) z := by
  simp [spanLocalNorm]
theorem analyticAt_sum_complexCellTerms (han : complexCellTermsAnalyticStatement) (hamb : IsAdmissibleAmbient F)
    (hodd : Odd F.blockSide) (a : ℝ) {S : Finset F.Cell} {R : F.FieldChain} (V : F.GaugeField F.top)
    {C₀ s y del c₂ : ℝ} (hdel : 0 ≤ del) (hctx : ∀ z ∈ S, CellHypotheses S z R C₀ s y)
    (hreg : ∀ U : ChainChart F, supWeightedNorm S del R U ≤ c₂ → ChartIsRegular S R U)
    (U : ChainChart F) (hnear : ∀ z ∈ S, localNorm S R U (constOneWeights F) z ≤ y / 2)
    (hy : 0 < y) (hU : supWeightedNorm S del R U < c₂) (A : Fin k → ChainChart F) :
    AnalyticAt ℂ (fun t => ∑ z ∈ S, complexCellTerms a S R (spanChart U A t) V z) 0 ∧
      ∀ᶠ t in 𝓝 (0 : Fin k → ℝ), (chartAction a S R (chartShiftMulti U A t) V : ℂ) =
        ∑ z ∈ S, complexCellTerms a S R (spanChart U A (complexifyCLM t)) V z := by
  constructor
  · refine Finset.analyticAt_fun_sum _ fun z hz => ?_
    refine analyticAt_complexCellTerms han hamb hodd a V (hctx z hz) U A ?_
    rw [spanLocalNorm_zero]
    have := hnear z hz
    linarith
  · have hcont : Continuous fun t : Fin k → ℝ =>
        supWeightedNorm S del R U + ∑ l, |t l| * supWeightedNorm S del R (A l) := by
      fun_prop
    have h1 : ∀ᶠ t in 𝓝 (0 : Fin k → ℝ),
        supWeightedNorm S del R U + ∑ l, |t l| * supWeightedNorm S del R (A l) < c₂ :=
      hcont.continuousAt.eventually_lt continuousAt_const (by simpa using hU)
    filter_upwards [h1] with t ht
    have hr := hreg _ ((supWeightedNorm_chartShiftMulti_le hodd.pos hdel R U A t).trans ht.le)
    rw [← BlockAverages.ComplexChartCoordinates.complexTotalOverTop_realChart a R _ V hr, spanChart_complexify,
      ((han F S R V a hodd hamb).1 (realChart (chartShiftMulti U A t)))]
end Total
section TotalMixed
theorem prod_eq_mul_mul_prod_erase_erase {n : ℕ} (sel : Fin n → ℝ) {l1 l2 : Fin n} (hne : l1 ≠ l2) :
    ∏ l, sel l = sel l1 * sel l2 * ∏ l ∈ (Finset.univ.erase l1).erase l2, sel l := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ sel (Finset.mem_univ l1),
    ← Finset.mul_prod_erase (Finset.univ.erase l1) sel (Finset.mem_erase.2 ⟨hne.symm, Finset.mem_univ l2⟩)]
  ring
theorem card_erase_erase {k' : ℕ} {l1 l2 : Fin (k' + 2)} (hne : l1 ≠ l2) :
    ((Finset.univ.erase l1).erase l2).card = k' := by
  rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hne.symm, Finset.mem_univ l2⟩),
    Finset.card_erase_of_mem (Finset.mem_univ l1), Finset.card_univ, Fintype.card_fin]
  omega
set_option maxHeartbeats 1000000 in
theorem abs_iteratedFDeriv_chartAction_le (hmix : mixedDerivativeOfSecondDifferencesStatement)
    (han : complexCellTermsAnalyticStatement) (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (h2 : 2 ≤ F.blockSide) (a : ℝ) {S : Finset F.Cell} {R : F.FieldChain} (V : F.GaugeField F.top)
    {C₀ s y del c₂ : ℝ} (hdel : 0 ≤ del) (hctx : ∀ z ∈ S, CellHypotheses S z R C₀ s y)
    (hreg : ∀ U : ChainChart F, supWeightedNorm S del R U ≤ c₂ → ChartIsRegular S R U)
    (U : ChainChart F) (hnear : ∀ z ∈ S, localNorm S R U (constOneWeights F) z ≤ y / 2) (hy : 0 < y)
    (hU : supWeightedNorm S del R U < c₂) {k' : ℕ} (A : Fin (k' + 2) → ChainChart F) {l1 l2 : Fin (k' + 2)}
    (hne : l1 ≠ l2) {φ : F.Cell → ℝ} {θ : ℝ} (hφ : ∀ y y', |φ y - φ y'| ≤ del * cellSupDist y y')
    (hθ : |θ| ≤ 1 / 8) (p : F.Site 0) :
    |iteratedFDeriv ℝ (k' + 2) (fun t : Fin (k' + 2) → ℝ => chartAction a S R (chartShiftMulti U A t) V) 0
        (fun l => Pi.single l 1)| ≤
      cauchyHalvingConstant k' * (cellSecondDiffConst (hullFactor F.blockSide) (200000 * (F.blockSide : ℝ) ^ 2)
          (1 / (2 * (200000 * (F.blockSide : ℝ) ^ 2))) a *
          9 * Real.exp (2 * del)) / (y / (4 * ((k' : ℝ) + 2))) ^ k' *
        ∑ z ∈ S, ∏ l, localNorm S R (A l) (if l = l1 then classWeight F φ θ p
          else if l = l2 then invertedWeights (classWeight F φ θ p) else constOneWeights F) z := by
  obtain ⟨hg, hev⟩ := analyticAt_sum_complexCellTerms (k := k' + 2) han hamb hodd a V hdel hctx hreg U hnear hy hU A
  obtain ⟨ρ, M, hE⟩ := exists_isBoundedHolomorphicExtension hg hev
  have e := ofReal_iteratedFDeriv_eq hE
  have hcd : ∀ z ∈ S, ContDiffAt ℂ (k' + 2 : ℕ) (fun t => complexCellTerms a S R (spanChart U A t) V z) 0 :=
    fun z hz =>
    (analyticAt_complexCellTerms han hamb hodd a V (hctx z hz) U A (by
      rw [spanLocalNorm_zero]
      have := hnear z hz
      linarith)).contDiffAt
  have e2 := iteratedFDeriv_fun_sum_apply (𝕜 := ℂ) (u := S)
    (f := fun z t => complexCellTerms a S R (spanChart U A t) V z) (n := k' + 2) (x := 0) hcd
  rw [e2, ContinuousMultilinearMap.sum_apply] at e
  have habs : ∀ x : ℝ, |x| = ‖(x : ℂ)‖ := fun x => by rw [Complex.norm_real, Real.norm_eq_abs]
  rw [habs, e]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun z hz => ?_
  refine (norm_iteratedFDeriv_complexCellTerms_le hmix han hamb hodd h2 a V (hctx z hz) U A (hnear z hz) hne hdel
    hφ hθ p).trans (le_of_eq ?_)
  rw [prod_eq_mul_mul_prod_erase_erase _ hne]
  simp only [if_true, if_neg hne.symm]
  have hrest : ∏ l ∈ (Finset.univ.erase l1).erase l2,
      localNorm S R (A l) (if l = l1 then classWeight F φ θ p
        else if l = l2 then invertedWeights (classWeight F φ θ p) else constOneWeights F) z =
      ∏ l ∈ (Finset.univ.erase l1).erase l2, localNorm S R (A l) (constOneWeights F) z := by
    refine Finset.prod_congr rfl fun l hl => ?_
    have h1 : l ≠ l2 := (Finset.mem_erase.1 hl).1
    have h3 : l ≠ l1 := (Finset.mem_erase.1 (Finset.mem_erase.1 hl).2).1
    simp [h1, h3]
  rw [hrest]
  simp only [add_zero]
  rw [Finset.prod_div_distrib, Finset.prod_const, card_erase_erase hne, one_pow, div_one]
  have hρ : y / (4 * ((k' : ℝ) + 2)) ≠ 0 := by positivity
  field_simp
end TotalMixed
section Taylor
def axisPoint (x : ℝ) : Fin 2 → ℝ := ![x, 0]
theorem hasDerivAt_iteratedFDeriv_axisPoint {Q : (Fin 2 → ℝ) → ℝ} {x : ℝ} (hQ : AnalyticAt ℝ Q (axisPoint x))
    (n : ℕ) (v : Fin n → Fin 2 → ℝ) :
    HasDerivAt (fun x' => iteratedFDeriv ℝ n Q (axisPoint x') v)
      (iteratedFDeriv ℝ (n + 1) Q (axisPoint x) (Fin.cons ![1, 0] v)) x := by
  have hc : ContDiffAt ℝ (n + 1 : ℕ) Q (axisPoint x) := hQ.contDiffAt
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ n Q) (axisPoint x) :=
    (hc.differentiableAt_iteratedFDeriv (m := n) (by exact_mod_cast Nat.lt_succ_self n))
  have hp : HasDerivAt axisPoint ![1, 0] x := by
    refine hasDerivAt_pi.2 fun i => ?_
    fin_cases i
    · exact hasDerivAt_id' x
    · exact hasDerivAt_const x (0 : ℝ)
  have h1 := hd.hasFDerivAt.comp_hasDerivAt x hp
  have h3 : HasDerivAt (fun x' => (iteratedFDeriv ℝ n Q (axisPoint x')) v)
      ((fderiv ℝ (iteratedFDeriv ℝ n Q) (axisPoint x) ![1, 0]) v) x := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Fin 2 → ℝ) ℝ v).hasFDerivAt.comp_hasDerivAt x h1
  have e : iteratedFDeriv ℝ (n + 1) Q (axisPoint x) (Fin.cons ![1, 0] v) =
      (fderiv ℝ (iteratedFDeriv ℝ n Q) (axisPoint x) ![1, 0]) v := by
    rw [iteratedFDeriv_succ_apply_left]
    simp
  rw [e]
  exact h3
theorem abs_taylor_axisPoint_le {Q : (Fin 2 → ℝ) → ℝ} {B : ℝ}
    (hQ : ∀ x ∈ Set.Icc (0 : ℝ) 1, AnalyticAt ℝ Q (axisPoint x))
    (hB : ∀ x ∈ Set.Icc (0 : ℝ) 1, |iteratedFDeriv ℝ 3 Q (axisPoint x) ![![1, 0], ![1, 0], ![0, 1]]| ≤ B) :
    |iteratedFDeriv ℝ 1 Q (axisPoint 1) ![![0, 1]] - iteratedFDeriv ℝ 1 Q (axisPoint 0) ![![0, 1]] -
      iteratedFDeriv ℝ 2 Q (axisPoint 0) ![![1, 0], ![0, 1]]| ≤ B := by
  set h : ℝ → ℝ := fun x => iteratedFDeriv ℝ 1 Q (axisPoint x) ![![0, 1]] with hh
  set h' : ℝ → ℝ := fun x => iteratedFDeriv ℝ 2 Q (axisPoint x) ![![1, 0], ![0, 1]] with hh'
  set h'' : ℝ → ℝ := fun x => iteratedFDeriv ℝ 3 Q (axisPoint x) ![![1, 0], ![1, 0], ![0, 1]] with hh''
  have d1 : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt h (h' x) x := fun x hx => by
    have := hasDerivAt_iteratedFDeriv_axisPoint (hQ x hx) 1 ![![0, 1]]
    exact this
  have d2 : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt h' (h'' x) x := fun x hx => by
    have := hasDerivAt_iteratedFDeriv_axisPoint (hQ x hx) 2 ![![1, 0], ![0, 1]]
    exact this
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 (by simp))
  have hconv : Convex ℝ (Set.Icc (0 : ℝ) 1) := convex_Icc 0 1
  have m1 : ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖h' x - h' 0‖ ≤ B := by
    intro x hx
    have := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le (f := h') (f' := h'') (C := B) (x := 0) (y := x)
      (fun y hy => (d2 y hy).hasDerivWithinAt) (fun y hy => hB y hy) (by simp) hx
    refine this.trans ?_
    have h1 : ‖x - 0‖ ≤ 1 := by
      rw [sub_zero, Real.norm_eq_abs, abs_of_nonneg hx.1]
      exact hx.2
    exact mul_le_of_le_one_right hB0 h1
  have d3 : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (fun x' => h x' - x' * h' 0) (h' x - h' 0) x := fun x hx => by
    have := (d1 x hx).fun_sub ((hasDerivAt_id' x).mul_const (h' 0))
    simpa using this
  have := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun x' => h x' - x' * h' 0)
    (f' := fun x => h' x - h' 0) (C := B) (x := 0) (y := 1)
    (fun y hy => (d3 y hy).hasDerivWithinAt) (fun y hy => m1 y hy) (by simp) (by simp)
  simp only [sub_zero, norm_one, mul_one, zero_mul, one_mul] at this
  rw [Real.norm_eq_abs] at this
  have e : h 1 - h' 0 - h 0 = h 1 - h 0 - h' 0 := by ring
  rw [e] at this
  exact this
end Taylor
section Third
def planeChartAction (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain) (V : F.GaugeField F.top) (U B : ChainChart F) :
    (Fin 2 → ℝ) → ℝ := fun t => chartAction a S R (chartShiftMulti (zeroChart F) ![U, B] t) V
def scaledChart (U : ChainChart F) (x : ℝ) : ChainChart F := chartMove (zeroChart F) U x
theorem chartAction_chartShiftMulti_scaledChart (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain)
    (V : F.GaugeField F.top) (U B : ChainChart F) (x : ℝ) (t : Fin 2 → ℝ) :
    chartAction a S R (chartShiftMulti (scaledChart U x) ![U, B] t) V =
      planeChartAction a S R V U B (t + axisPoint x) := by
  unfold planeChartAction
  congr 1
  apply chainChart_ext
  · funext y i
    simp only [chartShiftMulti, scaledChart, chartMove, zeroChart, Fin.sum_univ_two, axisPoint, Pi.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, add_smul, zero_smul]
    simp
    abel
  · funext j y i
    simp only [chartShiftMulti, scaledChart, chartMove, zeroChart, Fin.sum_univ_two, axisPoint, Pi.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, add_smul, zero_smul]
    simp
    abel
theorem analyticAt_planeChartAction (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain) (V : F.GaugeField F.top)
    (U B : ChainChart F) (x : ℝ)
    (h : AnalyticAt ℝ (fun t : Fin 2 → ℝ => chartAction a S R (chartShiftMulti (scaledChart U x) ![U, B] t) V) 0) :
    AnalyticAt ℝ (planeChartAction a S R V U B) (axisPoint x) := by
  have e : planeChartAction a S R V U B =
      (fun t : Fin 2 → ℝ => chartAction a S R (chartShiftMulti (scaledChart U x) ![U, B] t) V) ∘
      fun y => y - axisPoint x := by
    funext y
    simp only [Function.comp_apply]
    rw [chartAction_chartShiftMulti_scaledChart, sub_add_cancel]
  rw [e]
  refine AnalyticAt.comp ?_ ((analyticAt_id).sub analyticAt_const)
  simpa using h
def mergeFirstTwoCLM : (Fin 3 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearMap.pi fun i : Fin 2 => if i = 0 then
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0 +
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 1
    else ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 2
theorem mergeFirstTwoCLM_apply (t : Fin 3 → ℝ) : mergeFirstTwoCLM t = ![t 0 + t 1, t 2] := by
  funext i
  fin_cases i <;> simp [mergeFirstTwoCLM]
theorem chartAction_chartShiftMulti_scaledChart_three (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain)
    (V : F.GaugeField F.top) (U B : ChainChart F) (x : ℝ) (t : Fin 3 → ℝ) :
    chartAction a S R (chartShiftMulti (scaledChart U x) ![U, U, B] t) V =
      planeChartAction a S R V U B (mergeFirstTwoCLM t + axisPoint x) := by
  unfold planeChartAction
  rw [mergeFirstTwoCLM_apply]
  congr 1
  apply chainChart_ext
  · funext y i
    simp only [chartShiftMulti, scaledChart, chartMove, zeroChart, Fin.sum_univ_two, Fin.sum_univ_three, axisPoint,
      Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, add_smul, zero_smul]
    simp
    abel
  · funext j y i
    simp only [chartShiftMulti, scaledChart, chartMove, zeroChart, Fin.sum_univ_two, Fin.sum_univ_three, axisPoint,
      Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, add_smul, zero_smul]
    simp
    abel
theorem iteratedFDeriv_three_comp_mergeFirstTwo {Q : (Fin 2 → ℝ) → ℝ} {x : ℝ} (hQ : AnalyticAt ℝ Q (axisPoint x)) :
    iteratedFDeriv ℝ 3 (fun t : Fin 3 → ℝ => Q (mergeFirstTwoCLM t + axisPoint x)) 0 (fun l => Pi.single l 1) =
      iteratedFDeriv ℝ 3 Q (axisPoint x) ![![1, 0], ![1, 0], ![0, 1]] := by
  set f : (Fin 2 → ℝ) → ℝ := fun y => Q (y + axisPoint x) with hf
  set Ω : Set (Fin 2 → ℝ) := {y | AnalyticAt ℝ f y} with hΩ
  have hΩo : IsOpen Ω := isOpen_analyticAt ℝ f
  have h0 : (0 : Fin 2 → ℝ) ∈ Ω := by
    show AnalyticAt ℝ f 0
    refine AnalyticAt.comp (g := Q) (f := fun y : Fin 2 → ℝ => y + axisPoint x) ?_
      (analyticAt_id.add analyticAt_const)
    simpa using hQ
  have hcd : ContDiffOn ℝ (3 : ℕ) f Ω := fun y hy => (show AnalyticAt ℝ f y from hy).contDiffAt.contDiffWithinAt
  have hs' : IsOpen (mergeFirstTwoCLM ⁻¹' Ω) := hΩo.preimage mergeFirstTwoCLM.continuous
  have hmem : (0 : Fin 3 → ℝ) ∈ mergeFirstTwoCLM ⁻¹' Ω := by simpa using h0
  have h3 := mergeFirstTwoCLM.iteratedFDerivWithin_comp_right hcd hΩo.uniqueDiffOn hs'.uniqueDiffOn hmem (i := 3)
    le_rfl
  rw [iteratedFDerivWithin_of_isOpen 3 hs' hmem, map_zero, iteratedFDerivWithin_of_isOpen 3 hΩo h0] at h3
  have e1 : (fun t : Fin 3 → ℝ => Q (mergeFirstTwoCLM t + axisPoint x)) = f ∘ mergeFirstTwoCLM := rfl
  rw [e1, h3]
  have e2 : iteratedFDeriv ℝ 3 f 0 = iteratedFDeriv ℝ 3 Q (0 + axisPoint x) :=
    (iteratedFDeriv_comp_add_right' (𝕜 := ℝ) (f := Q) 3 (axisPoint x)) ▸ rfl
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [e2, zero_add]
  congr 1
  funext l
  fin_cases l <;> simp [mergeFirstTwoCLM_apply]
end Third
section Main
def secondAxisCLM : (Fin 1 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearMap.pi fun i : Fin 2 =>
    if i = 0 then 0 else ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0
theorem fderiv_eq_iteratedFDeriv_one_secondAxis {Q : (Fin 2 → ℝ) → ℝ} {x : ℝ}
    (hQ : DifferentiableAt ℝ Q (axisPoint x)) {g : (Fin 1 → ℝ) → ℝ} (hg : ∀ t, g t = Q (![x, t 0])) :
    fderiv ℝ g 0 (Pi.single 0 1) = iteratedFDeriv ℝ 1 Q (axisPoint x) ![![0, 1]] := by
  have hι : ∀ t : Fin 1 → ℝ, ![x, t 0] = axisPoint x + secondAxisCLM t := by
    intro t
    funext i
    fin_cases i <;> simp [axisPoint, secondAxisCLM]
  have h1 : HasFDerivAt (fun t : Fin 1 → ℝ => axisPoint x + secondAxisCLM t) secondAxisCLM 0 :=
    secondAxisCLM.hasFDerivAt.const_add _
  have h0 : (fun t : Fin 1 → ℝ => axisPoint x + secondAxisCLM t) 0 = axisPoint x := by simp
  have h3 : HasFDerivAt Q (fderiv ℝ Q (axisPoint x))
      ((fun t : Fin 1 → ℝ => axisPoint x + secondAxisCLM t) 0) := by
    rw [h0]
    exact hQ.hasFDerivAt
  have h4 := h3.comp (0 : Fin 1 → ℝ) h1
  have e : g = Q ∘ fun t : Fin 1 → ℝ => axisPoint x + secondAxisCLM t := by
    funext t
    simp only [Function.comp_apply]
    rw [hg, hι]
  rw [e, h4.fderiv, iteratedFDeriv_one_apply]
  simp only [ContinuousLinearMap.comp_apply]
  congr 1
  funext i
  fin_cases i <;> simp [secondAxisCLM]
variable {a : ℝ} {S : Finset F.Cell} {R : F.FieldChain} {V : F.GaugeField F.top} {C₀ s y del c₂ c : ℝ}
theorem analyticAt_chartAction (han : complexCellTermsAnalyticStatement) (hamb : IsAdmissibleAmbient F)
    (hodd : Odd F.blockSide) (hdel : 0 ≤ del) (hy : 0 < y) (hctx : ∀ z ∈ S, CellHypotheses S z R C₀ s y)
    (hreg : ∀ U : ChainChart F, supWeightedNorm S del R U ≤ c₂ →
      ChartIsRegular S R U ∧ ∀ z ∈ S, localNorm S R U (oneSiteWeights F) z ≤ 2 * supWeightedNorm S del R U)
    (hc2 : c < c₂) (hcy : 4 * c ≤ y) (U : ChainChart F) (hU : supWeightedNorm S del R U ≤ c) {k : ℕ}
    (A : Fin k → ChainChart F) :
    AnalyticAt ℝ (fun t : Fin k → ℝ => chartAction a S R (chartShiftMulti U A t) V) 0 := by
  have hnear : ∀ z ∈ S, localNorm S R U (constOneWeights F) z ≤ y / 2 := fun z hz => by
    have h1 := (hreg U (hU.trans hc2.le)).2 z hz
    have h3 : localNorm S R U (constOneWeights F) z = localNorm S R U (oneSiteWeights F) z := rfl
    rw [h3]
    linarith
  obtain ⟨hg, hev⟩ := analyticAt_sum_complexCellTerms han hamb hodd a V hdel hctx (fun W hW => (hreg W hW).1) U
    hnear hy (lt_of_le_of_lt hU hc2) A
  obtain ⟨ρ, M, hE⟩ := exists_isBoundedHolomorphicExtension hg hev
  exact hE.analyticAt_of_leftInverse Complex.reCLM (fun a => by simp)
theorem abs_iteratedFDeriv_chartAction_le_of_two_le (hmix : mixedDerivativeOfSecondDifferencesStatement)
    (han : complexCellTermsAnalyticStatement) (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (h2 : 2 ≤ F.blockSide) (hdel : 0 ≤ del) (hy : 0 < y) (hctx : ∀ z ∈ S, CellHypotheses S z R C₀ s y)
    (hreg : ∀ U : ChainChart F, supWeightedNorm S del R U ≤ c₂ →
      ChartIsRegular S R U ∧ ∀ z ∈ S, localNorm S R U (oneSiteWeights F) z ≤ 2 * supWeightedNorm S del R U)
    (hc2 : c < c₂) (hcy : 4 * c ≤ y) {Ck : ℕ → ℝ}
    (hCk : ∀ k', cauchyHalvingConstant k' * (cellSecondDiffConst (hullFactor F.blockSide)
      (200000 * (F.blockSide : ℝ) ^ 2) (1 / (2 * (200000 * (F.blockSide : ℝ) ^ 2))) a * 9 * Real.exp (2 * del)) /
        (y / (4 * ((k' : ℝ) + 2))) ^ k' ≤ Ck (k' + 2))
    (U : ChainChart F) (hU : supWeightedNorm S del R U ≤ c) {k : ℕ} (hk : 2 ≤ k) (A : Fin k → ChainChart F)
    {φ : F.Cell → ℝ} {θ : ℝ} (p : F.Site 0) {l1 l2 : Fin k} (hne : l1 ≠ l2) (hθ : |θ| ≤ 1 / 8)
    (hφ : ∀ y y', |φ y - φ y'| ≤ del * cellSupDist y y') :
    |iteratedFDeriv ℝ k (fun t : Fin k → ℝ => chartAction a S R (chartShiftMulti U A t) V) 0
        (fun l => Pi.single l 1)| ≤
      Ck k * ∑ z ∈ S, ∏ l, localNorm S R (A l) (if l = l1 then classWeight F φ θ p
          else if l = l2 then invertedWeights (classWeight F φ θ p) else constOneWeights F) z := by
  obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le' hk
  have hnear : ∀ z ∈ S, localNorm S R U (constOneWeights F) z ≤ y / 2 := fun z hz => by
    have h1 := (hreg U (hU.trans hc2.le)).2 z hz
    have h3 : localNorm S R U (constOneWeights F) z = localNorm S R U (oneSiteWeights F) z := rfl
    rw [h3]
    linarith
  refine (abs_iteratedFDeriv_chartAction_le hmix han hamb hodd h2 a V hdel hctx (fun W hW => (hreg W hW).1) U hnear
    hy (lt_of_le_of_lt hU hc2) A hne hφ hθ p).trans ?_
  refine mul_le_mul_of_nonneg_right (hCk k') ?_
  refine Finset.sum_nonneg fun z _ => Finset.prod_nonneg fun l _ => Real.sqrt_nonneg _
set_option maxHeartbeats 1000000 in
theorem abs_fderiv_sub_sub_le (hmix : mixedDerivativeOfSecondDifferencesStatement)
    (han : complexCellTermsAnalyticStatement) (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (h2 : 2 ≤ F.blockSide) (hdel : 0 ≤ del) (hy : 0 < y) (hctx : ∀ z ∈ S, CellHypotheses S z R C₀ s y)
    (hreg : ∀ U : ChainChart F, supWeightedNorm S del R U ≤ c₂ →
      ChartIsRegular S R U ∧ ∀ z ∈ S, localNorm S R U (oneSiteWeights F) z ≤ 2 * supWeightedNorm S del R U)
    (hc2 : c < c₂) (hcy : 4 * c ≤ y) {Ck : ℕ → ℝ} (hCk0 : 0 < Ck 3)
    (hCk : ∀ k', cauchyHalvingConstant k' * (cellSecondDiffConst (hullFactor F.blockSide)
      (200000 * (F.blockSide : ℝ) ^ 2) (1 / (2 * (200000 * (F.blockSide : ℝ) ^ 2))) a * 9 * Real.exp (2 * del)) /
        (y / (4 * ((k' : ℝ) + 2))) ^ k' ≤ Ck (k' + 2))
    (U : ChainChart F) (hU : supWeightedNorm S del R U ≤ c) (A : Fin 1 → ChainChart F)
    {φ : F.Cell → ℝ} {θ : ℝ} (p : F.Site 0) (hθ : |θ| ≤ 1 / 8)
    (hφ : ∀ y y', |φ y - φ y'| ≤ del * cellSupDist y y') :
    |fderiv ℝ (fun t : Fin 1 → ℝ => chartAction a S R (chartShiftMulti U A t) V) 0 (Pi.single 0 1) -
        fderiv ℝ (fun t : Fin 1 → ℝ => chartAction a S R (chartShiftMulti (zeroChart F) A t) V) 0 (Pi.single 0 1) -
        iteratedFDeriv ℝ 2 (fun t : Fin 2 → ℝ => chartAction a S R
          (chartShiftMulti (zeroChart F) ![U, A 0] t) V) 0 (fun l => Pi.single l 1)| ≤
      2 * Ck 3 * supWeightedNorm S del R U * weightedNorm S R U (classWeight F φ θ p) *
        weightedNorm S R (A 0) (invertedWeights (classWeight F φ θ p)) := by
  have hL : 0 < F.blockSide := hodd.pos
  set B := A 0 with hBd
  set Q := planeChartAction a S R V U B with hQd
  have hnS : 0 ≤ supWeightedNorm S del R U := supWeightedNorm_nonneg S del R U
  have hbase : ∀ x ∈ Set.Icc (0 : ℝ) 1, supWeightedNorm S del R (scaledChart U x) ≤ c := by
    intro x hx
    unfold scaledChart
    rw [supWeightedNorm_smul S hL del R U x, abs_of_nonneg hx.1]
    exact (mul_le_of_le_one_left hnS hx.2).trans hU
  have hQan : ∀ x ∈ Set.Icc (0 : ℝ) 1, AnalyticAt ℝ Q (axisPoint x) := fun x hx =>
    analyticAt_planeChartAction a S R V U B x
      (analyticAt_chartAction han hamb hodd hdel hy hctx hreg hc2 hcy _ (hbase x hx) _)
  set w := classWeight F φ θ p with hw
  set w' := invertedWeights w with hw'
  set Sum := ∑ z ∈ S, localNorm S R U (constOneWeights F) z * localNorm S R U w z * localNorm S R B w' z with hSum
  have hBnd : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |iteratedFDeriv ℝ 3 Q (axisPoint x) ![![1, 0], ![1, 0], ![0, 1]]| ≤ Ck 3 * Sum := by
    intro x hx
    have e1 := iteratedFDeriv_three_comp_mergeFirstTwo (hQan x hx)
    rw [← e1]
    have e2 : (fun t : Fin 3 → ℝ => Q (mergeFirstTwoCLM t + axisPoint x)) =
        fun t => chartAction a S R (chartShiftMulti (scaledChart U x) ![U, U, B] t) V := by
      funext t
      rw [chartAction_chartShiftMulti_scaledChart_three]
    rw [e2]
    have h3 := abs_iteratedFDeriv_chartAction_le_of_two_le (a := a) (V := V) hmix han hamb hodd h2 hdel hy hctx hreg
      hc2 hcy hCk (scaledChart U x) (hbase x hx) (k := 3) (by norm_num) ![U, U, B] (φ := φ) (θ := θ) p (l1 := 1)
      (l2 := 2) (by decide) hθ hφ
    refine h3.trans (le_of_eq ?_)
    congr 1
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Fin.prod_univ_three]
    simp
    rfl
  have hT := abs_taylor_axisPoint_le hQan hBnd
  have e1 : fderiv ℝ (fun t : Fin 1 → ℝ => chartAction a S R (chartShiftMulti U A t) V) 0 (Pi.single 0 1) =
      iteratedFDeriv ℝ 1 Q (axisPoint 1) ![![0, 1]] := by
    refine fderiv_eq_iteratedFDeriv_one_secondAxis (hQan 1 (by simp)).differentiableAt fun t => ?_
    show chartAction a S R (chartShiftMulti U A t) V =
      chartAction a S R (chartShiftMulti (zeroChart F) ![U, B] ![1, t 0]) V
    congr 1
    apply chainChart_ext
    · funext x i
      simp [chartShiftMulti, zeroChart, Fin.sum_univ_two, hBd]
    · funext j x i
      simp [chartShiftMulti, zeroChart, Fin.sum_univ_two, hBd]
  have e2 : fderiv ℝ (fun t : Fin 1 → ℝ => chartAction a S R (chartShiftMulti (zeroChart F) A t) V) 0
      (Pi.single 0 1) = iteratedFDeriv ℝ 1 Q (axisPoint 0) ![![0, 1]] := by
    refine fderiv_eq_iteratedFDeriv_one_secondAxis (hQan 0 (by simp)).differentiableAt fun t => ?_
    show chartAction a S R (chartShiftMulti (zeroChart F) A t) V =
      chartAction a S R (chartShiftMulti (zeroChart F) ![U, B] ![0, t 0]) V
    congr 1
    apply chainChart_ext
    · funext x i
      simp [chartShiftMulti, zeroChart, Fin.sum_univ_two, hBd]
    · funext j x i
      simp [chartShiftMulti, zeroChart, Fin.sum_univ_two, hBd]
  have e3 : iteratedFDeriv ℝ 2 (fun t : Fin 2 → ℝ => chartAction a S R
      (chartShiftMulti (zeroChart F) ![U, A 0] t) V) 0 (fun l => Pi.single l 1) =
      iteratedFDeriv ℝ 2 Q (axisPoint 0) ![![1, 0], ![0, 1]] := by
    have e4 : axisPoint 0 = (0 : Fin 2 → ℝ) := by
      funext i
      fin_cases i <;> simp [axisPoint]
    rw [e4]
    have e5 : (fun l : Fin 2 => (Pi.single l 1 : Fin 2 → ℝ)) = ![![1, 0], ![0, 1]] := by
      funext l i
      fin_cases l <;> fin_cases i <;> simp
    rw [e5]
    rfl
  rw [e1, e2, e3]
  refine hT.trans ?_
  have h3 : Sum ≤ (2 * supWeightedNorm S del R U) * ∑ z ∈ S, localNorm S R U w z * localNorm S R B w' z := by
    rw [hSum, Finset.mul_sum]
    refine Finset.sum_le_sum fun z hz => ?_
    have h4 := (hreg U (hU.trans hc2.le)).2 z hz
    have h5 : localNorm S R U (constOneWeights F) z = localNorm S R U (oneSiteWeights F) z := rfl
    have h6 : 0 ≤ localNorm S R U w z * localNorm S R B w' z := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right (h5 ▸ h4) h6
  have h4 : ∑ z ∈ S, localNorm S R U w z * localNorm S R B w' z ≤ weightedNorm S R U w * weightedNorm S R B w' := by
    have := sum_mul_le_finsetLpNorm_two_mul S (fun z => localNorm S R U w z) (fun z => localNorm S R B w' z)
    rw [finsetLpNorm_two_eq_sqrt, finsetLpNorm_two_eq_sqrt] at this
    exact this
  have h5 : Ck 3 * Sum ≤ Ck 3 * ((2 * supWeightedNorm S del R U) * (weightedNorm S R U w * weightedNorm S R B w')) :=
    mul_le_mul_of_nonneg_left (h3.trans (mul_le_mul_of_nonneg_left h4 (by positivity))) hCk0.le
  refine h5.trans (le_of_eq ?_)
  ring
end Main
theorem chartActionDerivativeBounds (hrec : UniformQuarticBoundAcrossLevels) (hbd : referenceBoundsStatement)
    (hsm : smallChartIsRegularStatement) (hmix : mixedDerivativeOfSecondDifferencesStatement)
    (han : complexCellTermsAnalyticStatement) : chartActionDerivativeBoundsStatement := by
  obtain ⟨C, L1, hC, hctx⟩ := cellHypotheses_of_referenceBounds hrec hbd
  obtain ⟨Lr, hregL⟩ := hsm
  refine ⟨max (max L1 Lr) 5, ?_⟩
  intro L a θ del hodd hL ha hθ0 hθ8 hd0 hd8
  have hL1 : L1 ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hLr : Lr ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have h5 : 5 ≤ L := (le_max_right _ _).trans hL
  obtain ⟨c₁, y₀, hc₁, hy₀, hc⟩ := hctx L hodd hL1 h5
  obtain ⟨c₂, hc₂, hr⟩ := hregL L hodd hLr del hd0 hd8
  have hF0 : 0 ≤ hullFactor L := hullFactor_nonneg L
  set Mc := cellSecondDiffConst (hullFactor L) (200000 * (L : ℝ) ^ 2) (1 / (2 * (200000 * (L : ℝ) ^ 2))) a * 9 *
    Real.exp (2 * del) with hMc
  have hMc0 : 0 ≤ Mc := by
    rw [hMc]
    unfold cellSecondDiffConst secondDiffConst
    positivity
  set Ck : ℕ → ℝ := fun k => cauchyHalvingConstant (k - 2) * Mc /
    (y₀ / (4 * (((k - 2 : ℕ) : ℝ) + 2))) ^ (k - 2) + 1 with hCkd
  have hCk0 : ∀ k, 0 < Ck k := fun k => by
    have h1 := cauchyHalvingConstant_pos (k - 2)
    simp only [hCkd]
    positivity
  have hc0 : 0 < min (min c₁ (c₂ / 2)) (min (y₀ / 4) (y₀ / (26 * C))) := by
    refine lt_min (lt_min hc₁ (by positivity)) (lt_min (by positivity) (by positivity))
  refine ⟨min (min c₁ (c₂ / 2)) (min (y₀ / 4) (y₀ / (26 * C))), 2 * Ck 3, Ck, hc0, by
    have := hCk0 3
    positivity, hCk0, ?_⟩
  intro F m S hFL hamb hm hreg s V hs hsc hcold U hU
  have hc_c₁ : min (min c₁ (c₂ / 2)) (min (y₀ / 4) (y₀ / (26 * C))) ≤ c₁ :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hc_c₂ : min (min c₁ (c₂ / 2)) (min (y₀ / 4) (y₀ / (26 * C))) ≤ c₂ / 2 :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hc_y : min (min c₁ (c₂ / 2)) (min (y₀ / 4) (y₀ / (26 * C))) ≤ y₀ / 4 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hc_s : min (min c₁ (c₂ / 2)) (min (y₀ / 4) (y₀ / (26 * C))) ≤ y₀ / (26 * C) :=
    (min_le_right _ _).trans (min_le_right _ _)
  set c := min (min c₁ (c₂ / 2)) (min (y₀ / 4) (y₀ / (26 * C))) with hcd
  have h26 : 26 * C * s ≤ y₀ := by
    have h1 : s ≤ y₀ / (26 * C) := hsc.trans hc_s
    rw [le_div_iff₀ (by positivity)] at h1
    linarith
  have hreg' := fun W hW => hr F m S hFL hamb hm hreg s V hs (hsc.trans (hc_c₂.trans (by linarith))) hcold W hW
  have hct : ∀ z ∈ S, CellHypotheses S z (referenceFieldChain S V) C s y₀ := fun z _ =>
    hc F m S hFL hamb hm hreg s V hs (hsc.trans hc_c₁) hcold z y₀ h26 le_rfl
  have hc2 : c < c₂ := by linarith
  have hcy : 4 * c ≤ y₀ := by linarith
  have hoddF : Odd F.blockSide := hFL ▸ hodd
  have h2F : 2 ≤ F.blockSide := by omega
  have hCk : ∀ k', cauchyHalvingConstant k' * (cellSecondDiffConst (hullFactor F.blockSide)
      (200000 * (F.blockSide : ℝ) ^ 2) (1 / (2 * (200000 * (F.blockSide : ℝ) ^ 2))) a * 9 * Real.exp (2 * del)) /
        (y₀ / (4 * ((k' : ℝ) + 2))) ^ k' ≤ Ck (k' + 2) := by
    intro k'
    rw [hFL]
    simp only [hCkd, Nat.add_sub_cancel]
    linarith
  have hd0' : 0 ≤ del := hd0.le
  refine ⟨fun k A => analyticAt_chartAction han hamb hoddF hd0' hy₀ hct hreg' hc2 hcy U hU A, ?_, ?_⟩
  · intro k hk A φ θ' p l1 l2 hne hθ' hφ
    have habs : |θ'| ≤ 1 / 8 := by
      rcases hθ' with h | h | h
      · rw [h, abs_of_nonneg hθ0]
        exact hθ8
      · rw [h]
        norm_num
      · rw [h, abs_neg, abs_of_nonneg hθ0]
        exact hθ8
    exact abs_iteratedFDeriv_chartAction_le_of_two_le hmix han hamb hoddF h2F hd0' hy₀ hct hreg' hc2 hcy hCk U hU
      hk A p hne habs hφ
  · intro A φ θ' p hθ' hφ
    have habs : |θ'| ≤ 1 / 8 := by
      rcases hθ' with h | h | h
      · rw [h, abs_of_nonneg hθ0]
        exact hθ8
      · rw [h]
        norm_num
      · rw [h, abs_neg, abs_of_nonneg hθ0]
        exact hθ8
    exact abs_fderiv_sub_sub_le hmix han hamb hoddF h2F hd0' hy₀ hct hreg' hc2 hcy (hCk0 3) hCk U hU A p habs hφ
end YangMills.Construction.ChartActionDerivatives
end
