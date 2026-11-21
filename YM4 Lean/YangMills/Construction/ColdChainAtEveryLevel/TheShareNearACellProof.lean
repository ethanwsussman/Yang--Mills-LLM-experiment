import YangMills.Construction.ColdChainAtEveryLevel.LandauOnALine
import YangMills.Construction.ColdChainAtEveryLevel.SharesOfAgreeingPairsProof
import YangMills.Construction.ColdChainAtEveryLevel.TopOfAShare
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator Topology
open Metric Filter
namespace YangMills.Construction.CellShare
open BlockAverages BlockAverages.ChartCoordinates LowerShare ReferenceShare ComplexTopFit NearbyCellTerms ComplexLineChart
  LandauInequality BlockLines CellSpans ComplexLevels ComplexDifferences ComplexCells CellNormBounds CellContexts Analytic
variable {F : BlockFrame} {S : Finset F.Cell} {Y : F.Cell} {R : F.FieldChain} {V : F.GaugeField F.top}
open Classical in
def topBondsAtCell (S : Finset F.Cell) (Y : F.Cell) : Finset (F.Site F.top × Fin 4) :=
  (innerBonds S F.top).filter fun b => b.1 = Y ∨ b.1 + unitStep F.top b.2 = Y
theorem localCellShare_congr (hodd : Odd F.blockSide) (a : ℝ) (R : F.FieldChain) (V : F.GaugeField F.top) (Y : F.Cell)
    {U U' : ChainChart F} (h : ChartEqOnBonds S U U') (v : F.Site F.top → Fin 4 → imaginaryQuaternions) :
    localCellShare a S R V Y U v = localCellShare a S R V Y U' v := by
  classical
  have hf := chartField_congr hodd R h
  unfold localCellShare gaugedCellShare
  have h0 : 0 < F.top := Nat.succ_pos _
  rw [chartChain_of_lt R U _ h0, chartChain_of_lt R U' _ h0]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun p hp => ?_) (congrArg (a * ·) (Finset.sum_congr rfl fun j hj =>
    Finset.sum_congr rfl fun c hc => ?_))
  · have := pathHolonomy_congr (D := (sitesOfCells S 0 : Set (F.Site 0))) (fun x i hx hx' => hf 0 h0 x i hx hx') p.1 _ 0
      (allAlong_plaquette hp)
    rw [add_siteOfCoords_zero] at this
    unfold plaquetteHolonomy
    rw [this]
  · have hjn : j < F.top := Finset.mem_range.1 hj
    rw [chartChain_of_lt R U _ hjn, chartChain_of_lt R U' _ hjn]
    unfold gaugedBlockFit chartGauge
    rw [show gaugedContourAverage (chartField R U j) (balancingGauge (chartField R U j) (R j)) c =
      gaugedContourAverage (chartField R U' j) (balancingGauge (chartField R U' j) (R j)) c from
        BlockAverages.ChartCoordinates.gaugedContourAverage_congr hodd hjn (R j) (hf j hjn) hc]
    by_cases htop : j + 1 < F.top
    · rw [chartChain_of_lt R U _ htop, chartChain_of_lt R U' _ htop,
        hf (j + 1) htop c.1 c.2 (innerBonds_ends hc).1 (innerBonds_ends hc).2]
    · obtain rfl : j = F.depth := by
        have hn : F.top = F.depth + 1 := rfl
        omega
      rw [chartChain_top R U _, chartChain_top R U' _]
section Top
theorem enclosingCell_top (x : F.Cell) : enclosingCell x = x := by apply _root_.YangMills.Construction.PotentialMeans.enclosingCell_self <;> assumption
theorem mem_topBondsAtCell_of_bondWeight_ne_zero {b : F.Site (F.depth + 1) × Fin 4} (hb : bondWeight Y b ≠ 0) :
    b ∈ innerBonds S (F.depth + 1) → b ∈ topBondsAtCell S Y := by
  classical
  intro hS
  refine Finset.mem_filter.2 ⟨hS, ?_⟩
  by_contra hcon
  push Not at hcon
  apply hb
  unfold bondWeight
  rw [if_neg (by rw [enclosingCell_top]; exact hcon.1), if_neg (by rw [enclosingCell_top]; exact hcon.2)]
  simp
theorem topRestriction_eq_sum_topBondsAtCell (a : ℝ) (U : ChainChart F) (v : F.Site F.top → Fin 4 → imaginaryQuaternions) :
    topRestriction a S R V Y U v = ∑ b ∈ topBondsAtCell S Y, (a * bondWeight Y b) *
      gaugedBlockFit (chartField R U F.depth) (chartGauge R U (F.depth + 1)) (rotatedField v V) b := by
  classical
  unfold topRestriction
  rw [Finset.mul_sum]
  have e : ∑ b ∈ innerBonds S (F.depth + 1), a * (bondWeight Y b *
      gaugedBlockFit (chartField R U F.depth) (chartGauge R U (F.depth + 1)) (rotatedField v V) b) =
      ∑ b ∈ (innerBonds S (F.depth + 1)).filter (fun b => bondWeight Y b ≠ 0), a * (bondWeight Y b *
      gaugedBlockFit (chartField R U F.depth) (chartGauge R U (F.depth + 1)) (rotatedField v V) b) :=
    (Finset.sum_filter_of_ne (p := fun b => bondWeight Y b ≠ 0) fun b _ hn h0 => hn (by rw [h0]; ring)).symm
  rw [e]
  have hsub : (innerBonds S (F.depth + 1)).filter (fun b => bondWeight Y b ≠ 0) ⊆ topBondsAtCell S Y := fun b hb =>
    mem_topBondsAtCell_of_bondWeight_ne_zero (Finset.mem_filter.1 hb).2 (Finset.mem_filter.1 hb).1
  rw [Finset.sum_subset hsub fun b hb hn => ?_]
  · exact Finset.sum_congr rfl fun b _ => by ring
  · have h1 : b ∈ innerBonds S (F.depth + 1) := (Finset.mem_filter.1 hb).1
    have h2 : bondWeight Y b = 0 := by
      by_contra h0
      exact hn (Finset.mem_filter.2 ⟨h1, h0⟩)
    rw [h2]
    ring
theorem card_topBondsAtCell_le : (topBondsAtCell S Y).card ≤ 8 := by
  classical
  have h1 : ((topBondsAtCell S Y).filter fun b => b.1 = Y).card ≤ 4 := by
    have hinj : Set.InjOn (fun c : F.Site F.top × Fin 4 => c.2)
        (((topBondsAtCell S Y).filter fun b => b.1 = Y : Finset _) : Set (F.Site F.top × Fin 4)) := by
      intro c hc c' hc' e
      have h1 := (Finset.mem_filter.1 (Finset.mem_coe.1 hc)).2
      have h2 := (Finset.mem_filter.1 (Finset.mem_coe.1 hc')).2
      exact Prod.ext (by rw [h1, h2]) e
    have := Finset.card_le_card_of_injOn _ (fun _ _ => Finset.mem_univ _) hinj
    simpa using this
  have h2 : ((topBondsAtCell S Y).filter fun b => ¬ b.1 = Y).card ≤ 4 := by
    have hinj : Set.InjOn (fun c : F.Site F.top × Fin 4 => c.2)
        (((topBondsAtCell S Y).filter fun b => ¬ b.1 = Y : Finset _) : Set (F.Site F.top × Fin 4)) := by
      intro c hc c' hc' e
      have m1 := Finset.mem_filter.1 (Finset.mem_coe.1 hc)
      have m2 := Finset.mem_filter.1 (Finset.mem_coe.1 hc')
      have k1 := (Finset.mem_filter.1 m1.1).2.resolve_left m1.2
      have k2 := (Finset.mem_filter.1 m2.1).2.resolve_left m2.2
      have e' : c.2 = c'.2 := e
      refine Prod.ext ?_ e
      have : c.1 + unitStep F.top c.2 = c'.1 + unitStep F.top c.2 := by
        rw [k1, e', k2]
      exact add_right_cancel this
    have := Finset.card_le_card_of_injOn _ (fun _ _ => Finset.mem_univ _) hinj
    simpa using this
  have h3 := Finset.card_filter_add_card_filter_not (s := topBondsAtCell S Y) (fun b => b.1 = Y)
  omega
theorem isBoundedHolomorphicExtension_sum {ι κ : Type} [Fintype ι] {T : Finset κ} {f : κ → (ι → ℝ) → ℝ}
    {g : κ → (ι → ℂ) → ℂ} {ρ M : ℝ} (hρ : 0 < ρ) (wt : κ → ℝ) (hw : ∀ b, 0 ≤ wt b)
    (h : ∀ b ∈ T, IsBoundedHolomorphicExtension Complex.ofRealCLM (f b) (g b) ρ M) :
    IsBoundedHolomorphicExtension Complex.ofRealCLM (fun t => ∑ b ∈ T, wt b * f b t)
      (fun ζ => ∑ b ∈ T, (wt b : ℂ) * g b ζ) ρ ((∑ b ∈ T, wt b) * M) := by
  refine ⟨hρ, fun ζ hζ => ?_, fun ζ hζ => ?_, fun t ht => ?_⟩
  · exact Finset.analyticAt_fun_sum _ fun b hb => analyticAt_const.mul ((h b hb).analyticOnNhd ζ hζ)
  · refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun b hb => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw b)]
    exact mul_le_mul_of_nonneg_left ((h b hb).norm_le ζ hζ) (hw b)
  · simp only [Complex.ofRealCLM_apply]
    push_cast
    refine Finset.sum_congr rfl fun b hb => ?_
    have := (h b hb).agrees_real t ht
    simp only [Complex.ofRealCLM_apply] at this
    rw [this]
structure TopHypotheses (S : Finset F.Cell) (Y : F.Cell) (R : F.FieldChain) (c σ ε₀ : ℝ) : Prop where
  const_pos : 0 < c
  two_const_le : 2 * c ≤ 1 / 4000
  blockSide_const_le : 4 * (F.blockSide : ℝ) * (16 * c) ≤ 1 / 1024
  const_lt_one : 16 * c < 1
  spread_le : σ ≤ 1 / 64
  radius_pos : 0 < ε₀
  radius_lt_hull : 3 * (ε₀ + σ) < hullBallRadius F.blockSide
  blockSide_sq_radius_le : 200000 * (F.blockSide : ℝ) ^ 2 * (ε₀ + σ) ≤ 1
  hull_const_lt : hullBondCount F.blockSide * (16 * c) < ε₀
  contourAverage_norm_le : ∀ b ∈ innerBonds (cellBall S Y 1) (F.depth + 1), ‖_root_.YangMills.Construction.BlockAverages.contourAverage (R F.depth) b‖ ≤ 1
  reference_near : ∀ j, j + 1 ≤ F.top → ∀ c ∈ innerBonds (cellBall S Y 1) (j + 1), ∀ h ∈ centredCube F.blockSide, ∀ π,
    ‖ofUnit (pathHolonomy (R j) (_root_.YangMills.Construction.BlockAverages.refineSite c.1) (bondContour F.blockSide h π c.2) *
      (polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage (R j) c))⁻¹) - 1‖ ≤ σ
  level_bound : ∀ W : ComplexChainChart F,
    Real.sqrt (Real.sqrt (∑ b ∈ innerBonds (cellBall S Y 1) 0, ‖levelDeviation R W 0 b.1 b.2‖ ^ 4)) ≤ 4 * c →
    (∀ j, j + 1 < F.top → Real.sqrt (∑ c ∈ innerBonds (cellBall S Y 1) (j + 1), ‖levelSource W j c.1 c.2 - 1‖ ^ 2) ≤ 4 * c) →
    ∀ j, j < F.top → Real.sqrt (Real.sqrt (∑ b ∈ innerBonds (cellBall S Y 1) j, ‖levelDeviation R W j b.1 b.2‖ ^ 4)) ≤ 16 * c
theorem mem_innerBonds_cellBall_of_mem_topBondsAtCell (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    {b : F.Site (F.depth + 1) × Fin 4} (hb : b ∈ topBondsAtCell S Y) :
    b ∈ innerBonds (cellBall S Y 1) (F.depth + 1) := by
  classical
  obtain ⟨hS, hY⟩ := Finset.mem_filter.1 hb
  refine mem_innerBonds_cellBall_of_bondWeight_ne_zero hamb hodd (by simp [BlockFrame.top]) hS ?_
  unfold bondWeight
  rcases hY with h | h
  · rw [if_pos (by rw [enclosingCell_top]; exact h)]
    split_ifs <;> norm_num
  · rw [if_pos (c := enclosingCell (b.1 + unitStep (F.depth + 1) b.2) = Y) (by rw [enclosingCell_top]; exact h)]
    split_ifs <;> norm_num
theorem exists_isBoundedHolomorphicExtension_topInChart (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    {a c σ ε₀ : ℝ} (ha : 0 ≤ a) (T : TopHypotheses S Y R c σ ε₀) {U : ChainChart F}
    (hU : localNorm S R U (oneSiteWeights F) Y ≤ c)
    {ι : Type} [Fintype ι] (A : ι → ChainChart F) (e : ι → F.Site F.top → Fin 4 → imaginaryQuaternions) (w q : ι → ℝ)
    (hw : ∀ l, 0 ≤ w l) {ρ : ℝ} (hρ : 0 < ρ) (hbud : ρ * ∑ l, w l * q l ≤ c)
    (hq : ∀ l, localDirectionSize S R (topBondsAtCell S Y) Y (A l) (e l) ≤ q l) :
    ∃ g, IsBoundedHolomorphicExtension Complex.ofRealCLM (fun t : ι → ℝ => topRestriction a S R V Y
      (chartShiftAlong U A (fun l => w l * t l)) (topVariationAlong e (fun l => w l * t l))) g ρ
        (8 * a * complexTopFitBound ε₀) := by
  classical
  have hbox : ∀ k, innerBonds (cellBall S Y 1) k ⊆ bondsOver S (cellBall S Y 3) k := fun k b hb =>
    mem_bondsOver_of_mem_innerBonds_cellBall hodd S Y k hb
  have hnear : ∀ l, localNorm S R (A l) (oneSiteWeights F) Y ≤ q l := fun l => by
    have h1 := hq l
    have h2 : 0 ≤ topVariationNorm (topBondsAtCell S Y) (e l) := Finset.sum_nonneg fun _ _ => norm_nonneg _
    unfold localDirectionSize at h1
    linarith
  have hext : ∀ b ∈ topBondsAtCell S Y, IsBoundedHolomorphicExtension Complex.ofRealCLM (fun t : ι → ℝ =>
      gaugedBlockFit (chartField R (chartShiftAlong U A (fun l => w l * t l)) F.depth)
        (chartGauge R (chartShiftAlong U A (fun l => w l * t l)) (F.depth + 1))
        (rotatedField (topVariationAlong e (fun l => w l * t l)) V) b)
      (complexTopFit R V b U A w (fun l => e l b.1 b.2)) ρ (complexTopFitBound ε₀) := by
    intro b hb
    have hbD := mem_innerBonds_cellBall_of_mem_topBondsAtCell hamb hodd hb
    refine isBoundedHolomorphicExtension_gaugedBlockFit hamb hodd hbD T.const_pos T.two_const_le T.blockSide_const_le
      T.const_lt_one T.spread_le T.radius_pos T.radius_lt_hull T.blockSide_sq_radius_le T.hull_const_lt
      (T.contourAverage_norm_le b hbD) T.reference_near T.level_bound
      U A e _ (fun l => rfl) w q hw hρ hbud ((finsetLpNorm_fine_le_localNorm S R U Y (hbox 0)).trans hU)
      (fun j hj => (finsetLpNorm_coarse_le_localNorm S R U Y hj (hbox (j + 1))).trans hU)
      (fun l => (finsetLpNorm_fine_le_localNorm S R (A l) Y (hbox 0)).trans (hnear l))
      (fun l j hj => (finsetLpNorm_coarse_le_localNorm S R (A l) Y hj (hbox (j + 1))).trans (hnear l)) (fun l => ?_)
    have h1 : ‖e l b.1 b.2‖ ≤ topVariationNorm (topBondsAtCell S Y) (e l) :=
      Finset.single_le_sum (f := fun b : F.Site F.top × Fin 4 => ‖e l b.1 b.2‖) (fun _ _ => norm_nonneg _) hb
    have h2 : 0 ≤ localNorm S R (A l) (oneSiteWeights F) Y := Real.sqrt_nonneg _
    have h3 := hq l
    unfold localDirectionSize at h3
    linarith
  have hs := isBoundedHolomorphicExtension_sum (T := topBondsAtCell S Y) hρ (fun b => a * bondWeight Y b)
    (fun b => mul_nonneg ha (bondWeight_nonneg Y b)) hext
  have hM : 0 ≤ complexTopFitBound ε₀ := by
    have := T.radius_pos
    unfold complexTopFitBound
    positivity
  have hc : ∑ b ∈ topBondsAtCell S Y, a * bondWeight Y b ≤ 8 * a := by
    rw [← Finset.mul_sum]
    have h1 : ∑ b ∈ topBondsAtCell S Y, bondWeight Y b ≤ (topBondsAtCell S Y).card • (1 : ℝ) :=
      Finset.sum_le_card_nsmul _ _ _ fun b _ => bondWeight_le_one Y b
    have h2 : ((topBondsAtCell S Y).card : ℝ) ≤ 8 := by exact_mod_cast card_topBondsAtCell_le
    rw [nsmul_eq_mul, mul_one] at h1
    nlinarith
  refine ⟨fun ζ => ∑ b ∈ topBondsAtCell S Y, ((a * bondWeight Y b : ℝ) : ℂ) *
    complexTopFit R V b U A w (fun l => e l b.1 b.2) ζ, ?_⟩
  have e1 : (fun t : ι → ℝ => topRestriction a S R V Y (chartShiftAlong U A (fun l => w l * t l))
      (topVariationAlong e (fun l => w l * t l))) = fun t => ∑ b ∈ topBondsAtCell S Y, (a * bondWeight Y b) *
        gaugedBlockFit (chartField R (chartShiftAlong U A (fun l => w l * t l)) F.depth)
          (chartGauge R (chartShiftAlong U A (fun l => w l * t l)) (F.depth + 1))
          (rotatedField (topVariationAlong e (fun l => w l * t l)) V) b :=
    funext fun t => topRestriction_eq_sum_topBondsAtCell a _ _
  rw [e1]
  exact ⟨hs.radius_pos, hs.analyticOnNhd, fun x hx => (hs.norm_le x hx).trans (mul_le_mul_of_nonneg_right hc hM),
    hs.agrees_real⟩
end Top
section Line
theorem localDirectionSize_nonneg (S : Finset F.Cell) (R : F.FieldChain) (B : Finset (F.Site F.top × Fin 4)) (z : F.Cell)
    (A : ChainChart F) (e : F.Site F.top → Fin 4 → imaginaryQuaternions) : 0 ≤ localDirectionSize S R B z A e := by apply _root_.YangMills.Construction.BlockAverages.AnalyticCellShares.localDirectionSize_nonneg <;> assumption
variable {C₀ s y c σ ε₀ : ℝ}
theorem const_add_smul_single (t h : ℂ) :
    (fun _ : Fin 1 => t) + h • (Pi.single 0 1 : Fin 1 → ℂ) = fun _ => t + h := by
  funext l
  have : l = 0 := Subsingleton.elim _ _
  subst this
  simp
theorem spanLocalNorm_line (U A : ChainChart F) (z : ℂ) :
    spanLocalNorm S R U (fun _ : Fin 1 => A) (fun _ => z) Y =
      localNorm S R U (constOneWeights F) Y + ‖z‖ * localNorm S R A (constOneWeights F) Y := by
  simp [spanLocalNorm]
def lineEmbedding : ℂ →L[ℂ] (Fin 1 → ℂ) := ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℂ ℂ
theorem lineEmbedding_apply (z : ℂ) : lineEmbedding z = fun _ => z := rfl
theorem norm_const_fin_one (z : ℂ) : ‖(fun _ : Fin 1 => z)‖ = ‖z‖ := by
  simp [pi_norm_const]
theorem norm_const_fin_one_real (t : ℝ) : ‖(fun _ : Fin 1 => t)‖ = |t| := by
  simp [pi_norm_const]
theorem exists_lipschitz_deriv_lowerInChart (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (h2 : 2 ≤ F.blockSide) (a : ℝ) (V : F.GaugeField F.top)
    (ctx : ∀ z, CellHypotheses S z R C₀ s y) (U A : ChainChart F) {q r : ℝ} (hr : 0 < r)
    (hU : localNorm S R U (constOneWeights F) Y + r * q ≤ y) (hq : localNorm S R A (constOneWeights F) Y ≤ q) :
    ∃ f' : ℝ → ℝ, (∀ t, |t| < r → HasDerivAt (fun τ : ℝ => lowerEvaluation a S R Y
        (chartShiftAlong U (fun _ : Fin 1 => A) (fun _ => τ))) (f' t) t) ∧
      ∀ t h, |t| < r → |t + h| < r → |f' (t + h) - f' t| ≤ 9 * lowerSecondDiffConst F.blockSide a * q ^ 2 * |h| := by
  have hA0 : 0 ≤ localNorm S R A (constOneWeights F) Y := Real.sqrt_nonneg _
  have hsize : ∀ z : ℂ, ‖z‖ < r → spanLocalNorm S R U (fun _ : Fin 1 => A) (fun _ => z) Y ≤ y := by
    intro z hz
    rw [spanLocalNorm_line]
    have : ‖z‖ * localNorm S R A (constOneWeights F) Y ≤ r * q :=
      mul_le_mul hz.le hq hA0 hr.le
    linarith
  have hg : ∀ z : ℂ, ‖z‖ < r → AnalyticAt ℂ (fun z : ℂ => lowerExtension a S Y R
      (spanChart U (fun _ : Fin 1 => A) (fun _ => z)) V) z := by
    intro z hz
    have h1 := analyticAt_lowerExtension_spanChart (V := V) hamb hodd a ctx U (fun _ : Fin 1 => A)
      (t₀ := lineEmbedding z) (hsize z hz)
    exact h1.comp (lineEmbedding.analyticAt z)
  have hf : ∀ t : ℝ, |t| < r → ((lowerEvaluation a S R Y (chartShiftAlong U (fun _ : Fin 1 => A) (fun _ => t)) : ℝ) : ℂ) =
      lowerExtension a S Y R (spanChart U (fun _ : Fin 1 => A) (fun _ => (t : ℂ))) V := by
    intro t ht
    have hz : ‖(t : ℂ)‖ < r := by simpa using ht
    have hcast : (fun _ : Fin 1 => (t : ℂ)) = complexifyCLM (fun _ : Fin 1 => t) := rfl
    rw [hcast, spanChart_complexify]
    refine ofReal_lowerSlice_eq_lowerExtension hamb hodd a V _ fun z hzb j hj c hc => ?_
    have := ((analyticAt_cellTerms_spanChart hamb hodd (cellSupDist_le_of_mem_cellBall hzb) V (ctx z) U
      (fun _ : Fin 1 => A) (t₀ := complexifyCLM (fun _ : Fin 1 => t)) (hsize _ hz)).2 j hj c hc).2
    rwa [spanChart_complexify] at this
  have hs : ∀ t h₁ h₂ : ℂ, ‖t‖ < r → ‖t + h₁‖ < r → ‖t + h₂‖ < r → ‖t + h₁ + h₂‖ < r →
      ‖lowerExtension a S Y R (spanChart U (fun _ : Fin 1 => A) (fun _ => t + h₁ + h₂)) V -
        lowerExtension a S Y R (spanChart U (fun _ : Fin 1 => A) (fun _ => t + h₁)) V -
        lowerExtension a S Y R (spanChart U (fun _ : Fin 1 => A) (fun _ => t + h₂)) V +
        lowerExtension a S Y R (spanChart U (fun _ : Fin 1 => A) (fun _ => t)) V‖ ≤
        9 * lowerSecondDiffConst F.blockSide a * q ^ 2 * ‖h₁‖ * ‖h₂‖ := by
    intro t h₁ h₂ n₀ n₁ n₂ n₃
    have e1 := const_add_smul_single t h₁
    have e2 := const_add_smul_single t h₂
    have e3 := const_add_smul_single (t + h₁) h₂
    have hb := norm_lowerExtension_secondDiff_le (V := V) hamb hodd h2 a ctx U (fun _ : Fin 1 => A) (fun _ => t)
      h₁ h₂ 0 0 (hsize t n₀)
      (by rw [e1]; exact hsize _ n₁) (by rw [e2]; exact hsize _ n₂) (by rw [e1, e3]; exact hsize _ n₃)
    rw [e1, e3, e2] at hb
    refine hb.trans ?_
    have hL := lowerSecondDiffConst_nonneg F.blockSide a
    have h3 : localNorm S R A (constOneWeights F) Y ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ hA0 hq 2
    have h4 : 0 ≤ ‖h₁‖ * ‖h₂‖ := by positivity
    calc _ = 9 * lowerSecondDiffConst F.blockSide a * (localNorm S R A (constOneWeights F) Y ^ 2) *
          (‖h₁‖ * ‖h₂‖) := by ring
      _ ≤ 9 * lowerSecondDiffConst F.blockSide a * q ^ 2 * (‖h₁‖ * ‖h₂‖) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 (by positivity)) h4
      _ = _ := by ring
  exact exists_lipschitz_deriv_of_second_diff hg hf hs
theorem exists_lipschitz_deriv_topInChart (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {a : ℝ}
    (ha : 0 ≤ a) (T : TopHypotheses S Y R c σ ε₀) {U A : ChainChart F}
    {e : F.Site F.top → Fin 4 → imaginaryQuaternions} (hU : localNorm S R U (oneSiteWeights F) Y ≤ c) {q r : ℝ}
    (hr : 0 < r) (hbud : r * q ≤ c) (hq : localDirectionSize S R (topBondsAtCell S Y) Y A e ≤ q) :
    ∃ f' : ℝ → ℝ, (∀ t, |t| < r → HasDerivAt (fun τ : ℝ => topRestriction a S R V Y
        (chartShiftAlong U (fun _ : Fin 1 => A) (fun _ => τ)) (topVariationAlong (fun _ : Fin 1 => e) (fun _ => τ)))
          (f' t) t) ∧
      ∀ t, |t| < r / 4 → |f' t - f' 0| ≤ 8 * a * complexTopFitBound ε₀ / (r / 4) / (r / 8) * |t| := by
  obtain ⟨g, hg⟩ := exists_isBoundedHolomorphicExtension_topInChart (V := V) hamb hodd ha T hU
    (fun _ : Fin 1 => A) (fun _ : Fin 1 => e) (fun _ => 1)
    (fun _ => q) (fun _ => zero_le_one) hr (by simpa using hbud) (fun _ => hq)
  refine exists_lipschitz_deriv_of_bounded_extension (g := fun z => g (lineEmbedding z)) hr (fun z hz => ?_)
    (fun z hz => ?_) (fun t ht => ?_)
  · have hz' : lineEmbedding z ∈ ball (0 : Fin 1 → ℂ) r := by
      rw [mem_ball_zero_iff, lineEmbedding_apply, norm_const_fin_one]
      exact hz
    exact (hg.analyticOnNhd _ hz').comp (lineEmbedding.analyticAt z)
  · have hz' : lineEmbedding z ∈ ball (0 : Fin 1 → ℂ) r := by
      rw [mem_ball_zero_iff, lineEmbedding_apply, norm_const_fin_one]
      exact hz
    exact hg.norm_le _ hz'
  · have h1 := hg.agrees_real (fun _ => t) (by rw [norm_const_fin_one_real]; exact ht)
    simp only [one_mul, Complex.ofRealCLM_apply] at h1
    rw [h1]
    rfl
def lineDerivConst (L : ℕ) (a ε₀ c : ℝ) : ℝ :=
  9 * lowerSecondDiffConst L a + 32 * (8 * a * complexTopFitBound ε₀) / c ^ 2
theorem exists_lipschitz_deriv_cellShareInChart (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (h2 : 2 ≤ F.blockSide) {a : ℝ} (ha : 0 ≤ a)
    (ctx : ∀ z, CellHypotheses S z R C₀ s y) (T : TopHypotheses S Y R c σ ε₀) (hy : c + c ≤ y)
    {U A : ChainChart F} {e : F.Site F.top → Fin 4 → imaginaryQuaternions}
    (hU : localNorm S R U (oneSiteWeights F) Y ≤ c) {q : ℝ} (hq0 : 0 < q)
    (hq : localDirectionSize S R (topBondsAtCell S Y) Y A e ≤ q) :
    ∃ f' : ℝ → ℝ, (∀ t, |t| < c / q → HasDerivAt (fun τ : ℝ => localCellShare a S R V Y
        (chartShiftAlong U (fun _ : Fin 1 => A) (fun _ => τ)) (topVariationAlong (fun _ : Fin 1 => e) (fun _ => τ)))
          (f' t) t) ∧
      ∀ t, |t| < c / q / 4 → |f' t - f' 0| ≤ lineDerivConst F.blockSide a ε₀ c * q ^ 2 * |t| := by
  have hc := T.const_pos
  have hr : 0 < c / q := by positivity
  have hrq : c / q * q = c := by field_simp
  have hts : 0 ≤ topVariationNorm (topBondsAtCell S Y) e := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hA : localNorm S R A (constOneWeights F) Y ≤ q := by
    have h1 := hq
    unfold localDirectionSize at h1
    have : localNorm S R A (oneSiteWeights F) Y = localNorm S R A (constOneWeights F) Y := rfl
    linarith
  have hU' : localNorm S R U (constOneWeights F) Y ≤ c := hU
  obtain ⟨l', hl, hl2⟩ := exists_lipschitz_deriv_lowerInChart (Y := Y) hamb hodd h2 a V ctx U A (q := q) hr
    (by rw [hrq]; linarith) hA
  obtain ⟨t', ht, ht2⟩ := exists_lipschitz_deriv_topInChart (V := V) hamb hodd ha T hU hr (q := q) (e := e) (A := A)
    (by rw [hrq]) hq
  refine ⟨fun t => l' t + t' t, fun t hlt => ?_, fun t hlt => ?_⟩
  · have e1 : (fun τ : ℝ => localCellShare a S R V Y (chartShiftAlong U (fun _ : Fin 1 => A) (fun _ => τ))
        (topVariationAlong (fun _ : Fin 1 => e) (fun _ => τ))) = fun τ =>
        lowerEvaluation a S R Y (chartShiftAlong U (fun _ : Fin 1 => A) (fun _ => τ)) +
          topRestriction a S R V Y (chartShiftAlong U (fun _ : Fin 1 => A) (fun _ => τ))
            (topVariationAlong (fun _ : Fin 1 => e) (fun _ => τ)) :=
      funext fun τ => cellShareInChart_eq_lowerShareInChart_add_topShareInChart a S R V Y _ _
    rw [e1]
    exact (hl t hlt).add (ht t hlt)
  · have hlt' : |t| < c / q := by
      have : c / q / 4 < c / q := by linarith
      linarith
    have h0 : |(0 : ℝ)| < c / q := by simpa using hr
    have h1 := hl2 0 t h0 (by simpa using hlt')
    rw [zero_add] at h1
    have h3 := ht2 t hlt
    have e2 : 8 * a * complexTopFitBound ε₀ / (c / q / 4) / (c / q / 8) =
        32 * (8 * a * complexTopFitBound ε₀) / c ^ 2 * q ^ 2 := by
      field_simp
      ring
    rw [e2] at h3
    have e3 : (l' t + t' t) - (l' 0 + t' 0) = (l' t - l' 0) + (t' t - t' 0) := by ring
    show |(l' t + t' t) - (l' 0 + t' 0)| ≤ _
    rw [e3]
    refine (abs_add_le _ _).trans ?_
    unfold lineDerivConst
    nlinarith [add_le_add h1 h3]
theorem cellShareInChart_nonneg {a : ℝ} (ha : 0 ≤ a) (U : ChainChart F)
    (v : F.Site F.top → Fin 4 → imaginaryQuaternions) : 0 ≤ localCellShare a S R V Y U v := by
  rw [cellShareInChart_eq_lowerShareInChart_add_topShareInChart]
  refine add_nonneg (lowerEvaluation_nonneg ha U) (mul_nonneg ha (Finset.sum_nonneg fun b _ => ?_))
  exact mul_nonneg (bondWeight_nonneg Y b) (PatchLocality.gaugedBlockFit_nonneg _ _ _ _)
end Line
section Sizes
variable {C₀ s y c σ ε₀ : ℝ}
theorem localNorm_zeroChart (S : Finset F.Cell) (R : F.FieldChain) (Y : F.Cell) :
    localNorm S R (zeroChart F) (oneSiteWeights F) Y = 0 := by
  simp [localNorm, localNormSq, zeroChart, linearizedCurl, _root_.YangMills.Construction.BlockAverages.adjointAction]
theorem chartShiftAlong_zero (U : ChainChart F) {k : ℕ} (A : Fin k → ChainChart F) :
    ChartEqOnBonds S (chartShiftAlong U A 0) U :=
  ⟨fun b _ => by simp [chartShiftAlong], fun j _ c _ => by simp [chartShiftAlong]⟩
theorem chartShiftAlong_zeroChart_one (U : ChainChart F) :
    ChartEqOnBonds S (chartShiftAlong (zeroChart F) (fun _ : Fin 1 => U) (fun _ => 1)) U :=
  ⟨fun b _ => by simp [chartShiftAlong, zeroChart], fun j _ c _ => by simp [chartShiftAlong, zeroChart]⟩
theorem topVariationAlong_zero_directions {k : ℕ} (t : Fin k → ℝ) :
    topVariationAlong (fun _ : Fin k => (fun _ _ => 0 : F.Site F.top → Fin 4 → imaginaryQuaternions)) t =
      fun _ _ => 0 := by
  funext y i
  simp [topVariationAlong]
theorem topVariationAlong_zero {k : ℕ} (e : Fin k → F.Site F.top → Fin 4 → imaginaryQuaternions) :
    topVariationAlong e 0 = fun _ _ => 0 := by
  funext y i
  simp [topVariationAlong]
theorem cellShareInChart_le_sq (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (h2 : 2 ≤ F.blockSide)
    {a : ℝ} (ha : 0 ≤ a) (ctx : ∀ z, CellHypotheses S z R C₀ s y) (T : TopHypotheses S Y R c σ ε₀)
    (hy : c + c ≤ y) (hs : 0 < s) {Cv : ℝ}
    (hCv : 0 ≤ Cv) (hK : 0 ≤ lineDerivConst F.blockSide a ε₀ c)
    (hv0 : localCellShare a S R V Y (zeroChart F) (fun _ _ => 0) ≤ Cv * s ^ 2) {U : ChainChart F}
    (hQ : s + localNorm S R U (oneSiteWeights F) Y < c / 4) :
    localCellShare a S R V Y U (fun _ _ => 0) ≤
      (2 * Cv + 2 * lineDerivConst F.blockSide a ε₀ c) * (s + localNorm S R U (oneSiteWeights F) Y) ^ 2 := by
  classical
  have hn0 : 0 ≤ localNorm S R U (oneSiteWeights F) Y := Real.sqrt_nonneg _
  obtain ⟨Q, hQd⟩ : ∃ Q, Q = s + localNorm S R U (oneSiteWeights F) Y := ⟨_, rfl⟩
  rw [← hQd] at hQ ⊢
  have hQ0 : 0 < Q := by
    rw [hQd]
    linarith
  have hc := T.const_pos
  set K₁ := lineDerivConst F.blockSide a ε₀ c with hK₁
  have hslot : localDirectionSize S R (topBondsAtCell S Y) Y U (fun _ _ => 0) ≤ Q := by
    unfold localDirectionSize topVariationNorm
    simp only [norm_zero, Finset.sum_const_zero, add_zero]
    rw [hQd]
    linarith
  obtain ⟨f', hd, hl⟩ := exists_lipschitz_deriv_cellShareInChart (V := V) hamb hodd h2 ha ctx T hy
    (U := zeroChart F) (A := U) (e := fun _ _ => 0)
    (by rw [localNorm_zeroChart]; exact hc.le) hQ0 hslot
  have hr : 1 < c / Q / 4 := by
    rw [div_div, lt_div_iff₀ (by positivity)]
    linarith
  have hd' : ∀ t, |t| ≤ 1 → HasDerivAt _ (f' t) t := fun t ht => hd t (by linarith)
  have hl' : ∀ t, |t| ≤ 1 → |f' t - f' 0| ≤ K₁ * Q ^ 2 * |t| := fun t ht => hl t (by linarith)
  have hKQ : 0 ≤ K₁ * Q ^ 2 := mul_nonneg hK (sq_nonneg Q)
  have hsQ : s ≤ Q := by
    rw [hQd]
    linarith
  have hρ0 : 0 < s / Q := by positivity
  have hρ1 : s / Q ≤ 1 := (div_le_one hQ0).2 hsQ
  have hland := abs_deriv_le_of_nonneg (f := fun τ : ℝ => localCellShare a S R V Y
      (chartShiftAlong (zeroChart F) (fun _ : Fin 1 => U) (fun _ => τ))
      (topVariationAlong (fun _ : Fin 1 => (fun _ _ => 0 : F.Site F.top → Fin 4 → imaginaryQuaternions)) (fun _ => τ)))
    hρ0 hKQ (fun t _ => cellShareInChart_nonneg ha _ _) (fun t ht => hd' t (ht.trans hρ1))
    (fun t ht => hl' t (ht.trans hρ1))
  have htan := abs_sub_tangent_le (f := fun τ : ℝ => localCellShare a S R V Y
      (chartShiftAlong (zeroChart F) (fun _ : Fin 1 => U) (fun _ => τ))
      (topVariationAlong (fun _ : Fin 1 => (fun _ _ => 0 : F.Site F.top → Fin 4 → imaginaryQuaternions)) (fun _ => τ)))
    one_pos hKQ hd' hl' (x := 1) (by simp)
  simp only [] at hland htan
  have e0 : localCellShare a S R V Y (chartShiftAlong (zeroChart F) (fun _ : Fin 1 => U) (fun _ => 0))
      (topVariationAlong (fun _ : Fin 1 => (fun _ _ => 0 : F.Site F.top → Fin 4 → imaginaryQuaternions)) (fun _ => 0)) =
      localCellShare a S R V Y (zeroChart F) (fun _ _ => 0) := by
    rw [topVariationAlong_zero_directions]
    exact localCellShare_congr hodd a R V Y (chartShiftAlong_zero (zeroChart F) (fun _ : Fin 1 => U)) _
  have e1 : localCellShare a S R V Y (chartShiftAlong (zeroChart F) (fun _ : Fin 1 => U) (fun _ => 1))
      (topVariationAlong (fun _ : Fin 1 => (fun _ _ => 0 : F.Site F.top → Fin 4 → imaginaryQuaternions)) (fun _ => 1)) =
      localCellShare a S R V Y U (fun _ _ => 0) := by
    rw [topVariationAlong_zero_directions]
    exact localCellShare_congr hodd a R V Y (chartShiftAlong_zeroChart_one U) _
  rw [e0] at hland htan
  rw [e1] at htan
  obtain ⟨f₀, hf₀⟩ : ∃ f₀, f₀ = localCellShare a S R V Y (zeroChart F) (fun _ _ => 0) := ⟨_, rfl⟩
  rw [← hf₀] at hland htan hv0
  have h1 : f₀ / (s / Q) ≤ Cv * s * Q := by
    rw [div_div_eq_mul_div, div_le_iff₀ hs]
    nlinarith
  have h2' : K₁ * Q ^ 2 * (s / Q) = K₁ * Q * s := by
    field_simp
  have h3 : |f' 0| ≤ Cv * s * Q + K₁ * Q * s := by
    rw [h2'] at hland
    linarith
  have h4 := (abs_le.1 htan).2
  simp only [abs_one, mul_one, one_mul] at h4
  have h5 := (le_abs_self (f' 0)).trans h3
  have h6 : Cv * s * Q ≤ Cv * Q ^ 2 := by
    have := mul_le_mul_of_nonneg_left hsQ (mul_nonneg hCv hQ0.le)
    nlinarith
  have h7 : K₁ * Q * s ≤ K₁ * Q ^ 2 := by
    have := mul_le_mul_of_nonneg_left hsQ (mul_nonneg hK hQ0.le)
    nlinarith
  have h8 : Cv * s ^ 2 ≤ Cv * Q ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs.le hsQ 2) hCv
  nlinarith
theorem norm_sliceIteratedDeriv_one_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (h2 : 2 ≤ F.blockSide) {a : ℝ} (ha : 0 ≤ a)
    (ctx : ∀ z, CellHypotheses S z R C₀ s y) (T : TopHypotheses S Y R c σ ε₀) (hy : c + c ≤ y) (hs : 0 < s)
    {Cq : ℝ} (hCq : 0 ≤ Cq) (hK : 0 ≤ lineDerivConst F.blockSide a ε₀ c) {U : ChainChart F}
    (hQ : s + localNorm S R U (oneSiteWeights F) Y < c / 4)
    (hval : localCellShare a S R V Y U (fun _ _ => 0) ≤ Cq * (s + localNorm S R U (oneSiteWeights F) Y) ^ 2)
    (A : ChainChart F) (e : F.Site F.top → Fin 4 → imaginaryQuaternions)
    (han : AnalyticAt ℝ (fun t : Fin 1 → ℝ => localCellShare a S R V Y (chartShiftAlong U (fun _ => A) t)
      (topVariationAlong (fun _ => e) t)) 0) :
    ‖localIteratedDeriv (localCellShare a S R V Y) U (fun _ : Fin 1 => A) (fun _ => e)‖ ≤
      (Cq + lineDerivConst F.blockSide a ε₀ c) * (s + localNorm S R U (oneSiteWeights F) Y) *
        localDirectionSize S R (topBondsAtCell S Y) Y A e := by
  classical
  have hn0 : 0 ≤ localNorm S R U (oneSiteWeights F) Y := Real.sqrt_nonneg _
  obtain ⟨Q, hQd⟩ : ∃ Q, Q = s + localNorm S R U (oneSiteWeights F) Y := ⟨_, rfl⟩
  rw [← hQd] at hQ hval ⊢
  have hQ0 : 0 < Q := by
    rw [hQd]
    linarith
  have hc := T.const_pos
  set K₁ := lineDerivConst F.blockSide a ε₀ c with hK₁
  have hUc : localNorm S R U (oneSiteWeights F) Y ≤ c := by
    have : localNorm S R U (oneSiteWeights F) Y ≤ Q := by
      rw [hQd]
      linarith
    linarith
  set p := localDirectionSize S R (topBondsAtCell S Y) Y A e with hp
  have hp0 : 0 ≤ p := localDirectionSize_nonneg S R (topBondsAtCell S Y) Y A e
  have hline : ∀ q, p < q →
      ‖localIteratedDeriv (localCellShare a S R V Y) U (fun _ : Fin 1 => A) (fun _ => e)‖ ≤
        (Cq + K₁) * Q * q := by
    intro q hq
    have hq0 : 0 < q := lt_of_le_of_lt hp0 hq
    obtain ⟨f', hd, hl⟩ := exists_lipschitz_deriv_cellShareInChart (V := V) hamb hodd h2 ha ctx T hy
      (U := U) (A := A) (e := e) hUc hq0 hq.le
    have hρ0 : 0 < Q / q := by positivity
    have hρ4 : Q / q < c / q / 4 := by
      rw [div_div, div_lt_div_iff₀ hq0 (by positivity)]
      nlinarith
    have hland := abs_deriv_le_of_nonneg (f := fun τ : ℝ => localCellShare a S R V Y
        (chartShiftAlong U (fun _ : Fin 1 => A) (fun _ => τ))
        (topVariationAlong (fun _ : Fin 1 => e) (fun _ => τ))) hρ0 (mul_nonneg hK (sq_nonneg q))
      (fun t _ => cellShareInChart_nonneg ha _ _) (fun t ht => hd t (by linarith)) (fun t ht => hl t (by linarith))
    have h0 : |(0 : ℝ)| < c / q := by
      rw [abs_zero]
      positivity
    have e0 : localCellShare a S R V Y (chartShiftAlong U (fun _ : Fin 1 => A) (fun _ => 0))
        (topVariationAlong (fun _ : Fin 1 => e) (fun _ => 0)) = localCellShare a S R V Y U (fun _ _ => 0) := by
      have := topVariationAlong_zero (fun _ : Fin 1 => e)
      have h3 : (fun _ : Fin 1 => (0 : ℝ)) = 0 := rfl
      rw [h3, this]
      exact localCellShare_congr hodd a R V Y (chartShiftAlong_zero U (fun _ : Fin 1 => A)) _
    simp only [] at hland
    rw [e0] at hland
    have hrd : localIteratedDeriv (localCellShare a S R V Y) U (fun _ : Fin 1 => A) (fun _ => e) = f' 0 := by
      unfold localIteratedDeriv
      rw [iteratedFDeriv_one_apply]
      have hD := han.differentiableAt.hasFDerivAt
      have hι : HasDerivAt (fun τ : ℝ => (fun _ : Fin 1 => τ)) (Pi.single 0 1 : Fin 1 → ℝ) 0 := by
        rw [hasDerivAt_pi]
        intro i
        have : i = 0 := Subsingleton.elim _ _
        subst this
        simp only [Pi.single_eq_same]
        exact hasDerivAt_id' (0 : ℝ)
      have hD' : HasFDerivAt (fun t : Fin 1 → ℝ => localCellShare a S R V Y (chartShiftAlong U (fun _ => A) t)
          (topVariationAlong (fun _ => e) t)) (fderiv ℝ (fun t : Fin 1 → ℝ => localCellShare a S R V Y
          (chartShiftAlong U (fun _ => A) t) (topVariationAlong (fun _ => e) t)) 0)
          ((fun τ : ℝ => (fun _ : Fin 1 => τ)) 0) := hD
      have hcomp := hD'.comp_hasDerivAt (0 : ℝ) hι
      exact hcomp.unique (hd 0 h0)
    rw [hrd, Real.norm_eq_abs]
    refine hland.trans ?_
    have h1 : localCellShare a S R V Y U (fun _ _ => 0) / (Q / q) ≤ Cq * Q * q := by
      rw [div_div_eq_mul_div, div_le_iff₀ hQ0]
      have := mul_le_mul_of_nonneg_right hval hq0.le
      nlinarith
    have h2' : K₁ * q ^ 2 * (Q / q) = K₁ * Q * q := by
      field_simp
    rw [h2']
    nlinarith
  have hlim : Tendsto (fun q : ℝ => (Cq + K₁) * Q * q) (𝓝[>] p) (𝓝 ((Cq + K₁) * Q * p)) := by
    have hc' : Continuous fun q : ℝ => (Cq + K₁) * Q * q := by fun_prop
    exact (hc'.tendsto p).mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact hline q hq
end Sizes
section Assemble
variable {C₀ s y c σ ε₀ : ℝ}
theorem analyticAt_lowerObservable_chartShiftAlong (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (a : ℝ)
    (V : F.GaugeField F.top) (ctx : ∀ z, CellHypotheses S z R C₀ s y) (U : ChainChart F) {ι : Type} [Fintype ι]
    (A : ι → ChainChart F) (hU : localNorm S R U (constOneWeights F) Y < y) :
    AnalyticAt ℝ (fun t : ι → ℝ => lowerEvaluation a S R Y (chartShiftAlong U A t)) 0 := by
  classical
  let eq := Fintype.equivFin ι
  let Tm : (ι → ℝ) →L[ℝ] (Fin (Fintype.card ι) → ℝ) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (eq.symm i)
  have h1 := analyticAt_lowerObservable (k := Fintype.card ι) hamb hodd a V ctx U (fun i => A (eq.symm i)) hU
  have h2 : AnalyticAt ℝ (fun t : Fin (Fintype.card ι) → ℝ => lowerEvaluation a S R Y
      (chartShiftAlong U (fun i => A (eq.symm i)) t)) (Tm 0) := by
    rw [map_zero]
    exact h1
  have h3 := h2.comp (Tm.analyticAt 0)
  refine h3.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [Function.comp]
  have e : chartShiftAlong U (fun i => A (eq.symm i)) (Tm t) = chartShiftAlong U A t := by
    have e1 : ∀ x i', ∑ l, (Tm t) l • (A (eq.symm l)).fine x i' = ∑ l, t l • (A l).fine x i' := fun x i' =>
      Fintype.sum_equiv eq.symm _ _ fun l => rfl
    have e2 : ∀ j x i', ∑ l, (Tm t) l • (A (eq.symm l)).coarse j x i' = ∑ l, t l • (A l).coarse j x i' :=
      fun j x i' => Fintype.sum_equiv eq.symm _ _ fun l => rfl
    simp only [chartShiftAlong, e1, e2]
  rw [e]
theorem analyticAt_topObservable_chartShiftAlong (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {a : ℝ}
    (ha : 0 ≤ a) (T : TopHypotheses S Y R c σ ε₀)
    {U : ChainChart F} (hU : localNorm S R U (oneSiteWeights F) Y ≤ c) {ι : Type} [Fintype ι]
    (A : ι → ChainChart F) (e : ι → F.Site F.top → Fin 4 → imaginaryQuaternions) :
    AnalyticAt ℝ (fun t : ι → ℝ => topRestriction a S R V Y (chartShiftAlong U A t) (topVariationAlong e t)) 0 := by
  have hc := T.const_pos
  set q : ι → ℝ := fun l => localDirectionSize S R (topBondsAtCell S Y) Y (A l) (e l) with hqd
  have hq0 : ∀ l, 0 ≤ q l := fun l => localDirectionSize_nonneg _ _ _ _ _ _
  have hsum : 0 ≤ ∑ l, q l := Finset.sum_nonneg fun l _ => hq0 l
  have hρ : 0 < c / (∑ l, q l + 1) := by positivity
  have hbud : c / (∑ l, q l + 1) * ∑ l, (1 : ℝ) * q l ≤ c := by
    simp only [one_mul]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨g, hg⟩ := exists_isBoundedHolomorphicExtension_topInChart (V := V) hamb hodd ha T hU A e (fun _ => 1) q
    (fun _ => zero_le_one) hρ hbud (fun l => le_rfl)
  have h := hg.analyticAt_of_leftInverse Complex.reCLM fun x => by simp
  simpa only [one_mul] using h
theorem norm_iteratedFDeriv_topShare_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {a : ℝ}
    (ha : 0 ≤ a) (T : TopHypotheses S Y R c σ ε₀)
    {U : ChainChart F} (hU : localNorm S R U (oneSiteWeights F) Y ≤ c) {m : ℕ} (A : Fin m → ChainChart F)
    (e : Fin m → F.Site F.top → Fin 4 → imaginaryQuaternions) :
    ‖iteratedFDeriv ℝ m (fun t : Fin m → ℝ => topRestriction a S R V Y (chartShiftAlong U A t) (topVariationAlong e t)) 0
        (fun l => Pi.single l 1)‖ ≤
      cauchyHalvingConstant m * (8 * a * complexTopFitBound ε₀) / (c / ((m : ℝ) + 1)) ^ m *
        ∏ l, localDirectionSize S R (topBondsAtCell S Y) Y (A l) (e l) := by
  have hc := T.const_pos
  refine le_mul_prod_of_scaled (fun l => localDirectionSize S R (topBondsAtCell S Y) Y (A l) (e l))
    (fun l => localDirectionSize_nonneg _ _ _ _ _ _) fun w hw hwq => ?_
  have hk1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hbud : c / ((m : ℝ) + 1) * ∑ l, w l * localDirectionSize S R (topBondsAtCell S Y) Y (A l) (e l) ≤ c := by
    have h1 : ∑ l, w l * localDirectionSize S R (topBondsAtCell S Y) Y (A l) (e l) ≤ m := by
      refine (Finset.sum_le_sum fun l _ => hwq l).trans ?_
      simp
    rw [div_mul_eq_mul_div, div_le_iff₀ hk1]
    nlinarith
  obtain ⟨g, hg⟩ := exists_isBoundedHolomorphicExtension_topInChart (V := V) hamb hodd ha T hU A e w _
    (fun l => (hw l).le) (by positivity) hbud (fun l => le_rfl)
  have h1 := hg.norm_iteratedFDeriv_basis_le Complex.reCLM (fun x => by simp) (fun x => by simp)
  have h2 := iteratedFDeriv_comp_diagonalScaling (fun t : Fin m → ℝ => topRestriction a S R V Y
    (chartShiftAlong U A t) (topVariationAlong e t)) w (fun l => (hw l).ne')
  rw [h2, norm_smul, Real.norm_of_nonneg (Finset.prod_nonneg fun l _ => (hw l).le)] at h1
  exact h1
theorem localNorm_le_localDirectionSize {S : Finset F.Cell} {R : F.FieldChain} {B : Finset (F.Site F.top × Fin 4)}
    {Y : F.Cell} (A : ChainChart F) (e : F.Site F.top → Fin 4 → imaginaryQuaternions) :
    localNorm S R A (constOneWeights F) Y ≤ localDirectionSize S R B Y A e := by
  have h2 : 0 ≤ topVariationNorm B e := Finset.sum_nonneg fun _ _ => norm_nonneg _
  unfold localDirectionSize
  have : localNorm S R A (oneSiteWeights F) Y = localNorm S R A (constOneWeights F) Y := rfl
  linarith
theorem norm_sliceIteratedDeriv_le_of_two_le (hmix : mixedDerivativeOfSecondDifferencesStatement)
    (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (h2 : 2 ≤ F.blockSide) {a : ℝ} (ha : 0 ≤ a) (ctx : ∀ z, CellHypotheses S z R C₀ s y) (hy0 : 0 < y)
    (T : TopHypotheses S Y R c σ ε₀) {U : ChainChart F} (hUc : localNorm S R U (oneSiteWeights F) Y ≤ c)
    (hUy : localNorm S R U (constOneWeights F) Y ≤ y / 2) {k' : ℕ} (A : Fin (k' + 2) → ChainChart F)
    (e : Fin (k' + 2) → F.Site F.top → Fin 4 → imaginaryQuaternions) :
    ‖localIteratedDeriv (localCellShare a S R V Y) U A e‖ ≤
      (higherDerivConst (lowerSecondDiffConst F.blockSide a) y k' + cauchyHalvingConstant (k' + 2) *
        (8 * a * complexTopFitBound ε₀) / (c / (((k' + 2 : ℕ) : ℝ) + 1)) ^ (k' + 2)) *
          ∏ l, localDirectionSize S R (topBondsAtCell S Y) Y (A l) (e l) := by
  have hL : AnalyticAt ℝ (fun t : Fin (k' + 2) → ℝ => lowerEvaluation a S R Y (chartShiftAlong U A t)) 0 :=
    analyticAt_lowerObservable_chartShiftAlong hamb hodd a V ctx U A (by linarith)
  have hT : AnalyticAt ℝ (fun t : Fin (k' + 2) → ℝ => topRestriction a S R V Y (chartShiftAlong U A t)
      (topVariationAlong e t)) 0 :=
    analyticAt_topObservable_chartShiftAlong hamb hodd ha T hUc A e
  have e1 : (fun t : Fin (k' + 2) → ℝ => localCellShare a S R V Y (chartShiftAlong U A t) (topVariationAlong e t)) =
      (fun t => lowerEvaluation a S R Y (chartShiftAlong U A t)) +
        fun t => topRestriction a S R V Y (chartShiftAlong U A t) (topVariationAlong e t) :=
    funext fun t => cellShareInChart_eq_lowerShareInChart_add_topShareInChart a S R V Y _ _
  have hLc : ContDiffAt ℝ (k' + 2 : ℕ) (fun t : Fin (k' + 2) → ℝ => lowerEvaluation a S R Y (chartShiftAlong U A t)) 0 :=
    hL.contDiffAt.of_le (by exact_mod_cast le_top)
  have hTc : ContDiffAt ℝ (k' + 2 : ℕ) (fun t : Fin (k' + 2) → ℝ => topRestriction a S R V Y (chartShiftAlong U A t)
      (topVariationAlong e t)) 0 := hT.contDiffAt.of_le (by exact_mod_cast le_top)
  unfold localIteratedDeriv
  rw [e1, iteratedFDeriv_add_apply hLc hTc]
  simp only [ContinuousMultilinearMap.add_apply]
  refine (norm_add_le _ _).trans ?_
  have h1 := norm_iteratedFDeriv_lowerShare_le (Y := Y) hmix hamb hodd h2 a V ctx hy0 U A hUy
  have h3 := norm_iteratedFDeriv_topShare_le (V := V) hamb hodd ha T hUc A e
  have hP : ∏ l, localNorm S R (A l) (constOneWeights F) Y ≤
      ∏ l, localDirectionSize S R (topBondsAtCell S Y) Y (A l) (e l) :=
    Finset.prod_le_prod (fun l _ => Real.sqrt_nonneg _) fun l _ => localNorm_le_localDirectionSize _ _
  have hS : 0 ≤ higherDerivConst (lowerSecondDiffConst F.blockSide a) y k' := by
    have := lowerSecondDiffConst_nonneg F.blockSide a
    have := cauchyHalvingConstant_pos k'
    unfold higherDerivConst
    positivity
  have h4 := mul_le_mul_of_nonneg_left hP hS
  rw [add_mul]
  linarith
end Assemble
section Zero
theorem rotatedField_zero (V : F.GaugeField F.top) : rotatedField (fun _ _ => (0 : imaginaryQuaternions)) V = V := by apply _root_.YangMills.Construction.BlockAverages.AnalyticCellShares.rotatedField_zero <;> assumption
theorem cellShareInChart_eq_zero_of_not_mem (hodd : Odd F.blockSide) (a : ℝ) {Y : F.Cell} (hY : Y ∉ S)
    (R : F.FieldChain) (V : F.GaugeField F.top)
    (U : ChainChart F) (v : F.Site F.top → Fin 4 → imaginaryQuaternions) : localCellShare a S R V Y U v = 0 := by apply _root_.YangMills.Construction.BlockAverages.AgreeingPairShares.cellShareInChart_eq_zero_of_not_mem <;> assumption
end Zero
theorem blockSide_mul_half_le (hodd : Odd F.blockSide) {y : ℝ} (hy : SmallParameter F.blockSide y) :
    4 * (F.blockSide : ℝ) * (16 * (y / 2)) ≤ 1 / 1024 := by
  have hL1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  have hH := hullBondCount_nonneg F.blockSide
  have hy0 := hy.pos
  have ha := hy.count_le_radius
  have h1 : 48 * (48 * hullBondCount F.blockSide + 1) * y * (8192 * (F.blockSide : ℝ)) ≤ 1 := by
    unfold hullBallRadius at ha
    rw [le_div_iff₀ (by positivity)] at ha
    exact ha
  have h4 : 0 ≤ hullBondCount F.blockSide * (y * F.blockSide) := by positivity
  nlinarith
set_option maxHeartbeats 4000000 in
theorem cellShareIsLocal (hrec : UniformQuarticBoundAcrossLevels) (hbd : referenceBoundsStatement)
    (hmix : mixedDerivativeOfSecondDifferencesStatement) : cellShareIsLocalStatement := by
  classical
  intro a ha
  obtain ⟨C, L1, hC, hctx⟩ := cellHypotheses_of_referenceBounds hrec hbd
  obtain ⟨C', c', L2, hC', hc', hb⟩ := hbd
  refine ⟨max (max L1 L2) 5, fun L hL hge => ?_⟩
  have g1 : L1 ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hge)
  have g2 : L2 ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hge)
  have g5 : 5 ≤ L := (le_max_right _ _).trans hge
  obtain ⟨c₀, y₀, hc₀, hy₀, hcx⟩ := hctx L hL g1 g5
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL.pos
  obtain ⟨c, hcv⟩ : ∃ c : ℝ, c = y₀ / 2 := ⟨_, rfl⟩
  have hc : 0 < c := by
    rw [hcv]
    positivity
  obtain ⟨ε₀, hε₀v⟩ : ∃ ε₀ : ℝ, ε₀ = 1 / (2 * (200000 * (L : ℝ) ^ 2)) := ⟨_, rfl⟩
  have hε₀ : 0 < ε₀ := by
    rw [hε₀v]
    positivity
  have hfb : 0 ≤ complexTopFitBound ε₀ := by
    unfold complexTopFitBound
    positivity
  obtain ⟨K₁, hK₁v⟩ : ∃ K₁ : ℝ, K₁ = lineDerivConst L a ε₀ c := ⟨_, rfl⟩
  have hK₁ : 0 ≤ K₁ := by
    rw [hK₁v]
    have := lowerSecondDiffConst_nonneg L a
    unfold lineDerivConst
    positivity
  obtain ⟨Cv, hCvv⟩ : ∃ Cv : ℝ, Cv = 81 * (1296 * C ^ 2) + a * (26 * C) ^ 2 + 8 * a * C' ^ 2 := ⟨_, rfl⟩
  have hCv : 0 ≤ Cv := by
    rw [hCvv]
    positivity
  obtain ⟨Cq, hCqv⟩ : ∃ Cq : ℝ, Cq = 2 * Cv + 2 * K₁ := ⟨_, rfl⟩
  have hCq : 0 ≤ Cq := by
    rw [hCqv]
    positivity
  obtain ⟨Ck, hCkv⟩ : ∃ Ck : ℕ → ℝ, Ck = fun n => if n = 0 then Cq else if n = 1 then Cq + K₁ else
      higherDerivConst (lowerSecondDiffConst L a) y₀ (n - 2) + cauchyHalvingConstant n *
        (8 * a * complexTopFitBound ε₀) / (c / ((n : ℝ) + 1)) ^ n := ⟨_, rfl⟩
  have hCk : ∀ n, 0 ≤ Ck n := by
    intro n
    rw [hCkv]
    show 0 ≤ if n = 0 then Cq else if n = 1 then Cq + K₁ else
      higherDerivConst (lowerSecondDiffConst L a) y₀ (n - 2) + cauchyHalvingConstant n *
        (8 * a * complexTopFitBound ε₀) / (c / ((n : ℝ) + 1)) ^ n
    split_ifs
    · exact hCq
    · linarith
    · have h1 := lowerSecondDiffConst_nonneg L a
      have h2 := cauchyHalvingConstant_pos (n - 2)
      have h3 := cauchyHalvingConstant_pos n
      have h4 : 0 ≤ higherDerivConst (lowerSecondDiffConst L a) y₀ (n - 2) := by
        unfold higherDerivConst
        positivity
      positivity
  obtain ⟨cD, hcDv⟩ : ∃ cD : ℝ, cD = min (min c₀ c') (min (y₀ / (26 * C)) (min (c / 16) 1)) := ⟨_, rfl⟩
  have hcD : 0 < cD := by
    rw [hcDv]
    exact lt_min (lt_min hc₀ hc') (lt_min (by positivity) (lt_min (by positivity) one_pos))
  have d1 : cD ≤ c₀ := by
    rw [hcDv]
    exact (min_le_left _ _).trans (min_le_left _ _)
  have d2 : cD ≤ c' := by
    rw [hcDv]
    exact (min_le_left _ _).trans (min_le_right _ _)
  have d3 : cD ≤ y₀ / (26 * C) := by
    rw [hcDv]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have d4 : cD ≤ c / 16 := by
    rw [hcDv]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have d5 : cD ≤ 1 := by
    rw [hcDv]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨cD, Ck, hcD, hCk, ?_⟩
  intro F m S hFL hamb hm hreg s V hs hsc hcold U Y B hB hU
  subst hFL
  have hodd : Odd F.blockSide := hL
  have h2 : 2 ≤ F.blockSide := by omega
  have hBe : B = topBondsAtCell S Y := by
    ext b
    rw [hB b]
    unfold topBondsAtCell
    simp [Finset.mem_filter]
  subst hBe
  obtain ⟨R, hRv⟩ : ∃ R : F.FieldChain, R = referenceFieldChain S V := ⟨_, rfl⟩
  rw [← hRv] at hU ⊢
  have hCs26 : 26 * C * s ≤ y₀ := by
    have h1 := hsc.trans d3
    rw [le_div_iff₀ (by positivity)] at h1
    linarith
  have ctx : ∀ z, CellHypotheses S z R C s y₀ := fun z => by
    rw [hRv]
    exact hcx F m S rfl hamb hm hreg s V hs (hsc.trans d1) hcold z y₀ hCs26 le_rfl
  have ctxs : ∀ z, CellHypotheses S z R C s (26 * C * s) := fun z => by
    rw [hRv]
    exact hcx F m S rfl hamb hm hreg s V hs (hsc.trans d1) hcold z _ le_rfl hCs26
  by_cases hY : Y ∈ S
  swap
  · have hz : localCellShare a S R V Y = fun _ _ => 0 := by
      funext U' v
      exact cellShareInChart_eq_zero_of_not_mem hodd a hY R V U' v
    have hzd : ∀ (n : ℕ) (A : Fin n → ChainChart F) (e : Fin n → F.Site F.top → Fin 4 → imaginaryQuaternions),
        localIteratedDeriv (localCellShare a S R V Y) U A e = 0 := by
      intro n A e
      rw [hz]
      unfold localIteratedDeriv
      simp
    have hn0 : 0 ≤ s + localNorm S R U (oneSiteWeights F) Y := add_nonneg hs.le (Real.sqrt_nonneg _)
    refine ⟨⟨fun _ _ _ _ => by rw [hz], fun A e => by rw [hz]; exact analyticAt_const, fun n A e => ?_⟩, ?_,
      fun n A e _ => ?_⟩
    · rw [hzd, norm_zero]
      exact mul_nonneg (hCk n) (Finset.prod_nonneg fun l _ => localDirectionSize_nonneg _ _ _ _ _ _)
    · rw [hz]
      simp only [abs_zero]
      exact mul_nonneg (hCk 0) (sq_nonneg _)
    · rw [hzd, norm_zero]
      exact mul_nonneg (mul_nonneg (hCk 1) hn0) (Finset.prod_nonneg fun l _ => localDirectionSize_nonneg _ _ _ _ _ _)
  have hnY := hU hY
  have hnY' : localNorm S R U (constOneWeights F) Y ≤ cD := hnY
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hb F m S hodd (by omega) hamb hm hreg s V hs (hsc.trans d2) hcold
  rw [← hRv] at b4 b6
  have hmean : ∀ j, j < F.top → ∀ c ∈ innerBonds S (j + 1), ‖_root_.YangMills.Construction.BlockAverages.contourAverage (R j) c‖ ≤ 1 := fun j hj c hc => by
    have := (b6 j hj c hc).1
    linarith
  have hsy := (ctx Y).small
  have hCs : C * s ≤ y₀ := (ctx Y).const_mul_scale_le
  have hCs0 : 0 ≤ C * s := by positivity
  have hy1 := hsy.le_bound
  have hL1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  have hK0 : (0 : ℝ) < 200000 * (F.blockSide : ℝ) ^ 2 := by positivity
  have hKε : 200000 * (F.blockSide : ℝ) ^ 2 * ε₀ = 1 / 2 := by
    rw [hε₀v]
    field_simp
  have T : TopHypotheses S Y R c (C * s) ε₀ := by
    refine ⟨hc, ?_, ?_, ?_, ?_, hε₀, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hcv]
      linarith
    · rw [hcv]
      exact blockSide_mul_half_le hodd hsy
    · rw [hcv]
      linarith
    · linarith
    · have hr := hsy.le_radius
      have h3 : 3 * ε₀ < hullBallRadius F.blockSide / 2 := by
        rw [hε₀v]
        unfold hullBallRadius
        have e1 : 3 * (1 / (2 * (200000 * (F.blockSide : ℝ) ^ 2))) = 3 / (400000 * (F.blockSide : ℝ) ^ 2) := by
          field_simp
          ring
        rw [e1, div_div, div_lt_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith
    · have hf := hsy.scale_le
      have h3 : 200000 * (F.blockSide : ℝ) ^ 2 * (C * s) ≤ 200000 * (F.blockSide : ℝ) ^ 2 * y₀ :=
        mul_le_mul_of_nonneg_left hCs hK0.le
      rw [mul_add, hKε]
      linarith
    · have hg := hsy.count_scale_le
      have hH := hullBondCount_nonneg F.blockSide
      have e1 : hullBondCount F.blockSide * (16 * c) = 8 * (hullBondCount F.blockSide * y₀) := by
        rw [hcv]
        ring
      rw [e1]
      have e2 : (200000 * (F.blockSide : ℝ) ^ 2) * (8 * (hullBondCount F.blockSide * y₀)) ≤ 1 / 576 := by
        nlinarith
      have e3 : (200000 * (F.blockSide : ℝ) ^ 2) * (8 * (hullBondCount F.blockSide * y₀)) <
          (200000 * (F.blockSide : ℝ) ^ 2) * ε₀ := by
        rw [hKε]
        linarith
      exact lt_of_mul_lt_mul_left e3 hK0.le
    · intro b hbD
      exact hmean F.depth (by simp [BlockFrame.top]) b (innerBonds_mono (cellBall_subset S Y 1) _ hbD)
    · intro j hj c₂ hc₂ h hh π
      refine ((ctx Y).near j hj c₂ hc₂ h hh π).trans ?_
      have h3 : ((1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1))) ^ 2 ≤ 1 :=
        pow_le_one₀ (by positivity) (inv_pow_le_one hodd.pos _)
      exact mul_le_of_le_one_right hCs0 h3
    · intro W h0 hm'
      have e4 : 4 * c = 2 * y₀ := by
        rw [hcv]
        ring
      have e16 : 16 * c = 4 * (2 * y₀) := by
        rw [hcv]
        ring
      rw [e4] at h0
      have hm2 : ∀ j, j + 1 < F.top →
          Real.sqrt (∑ c ∈ innerBonds (cellBall S Y 1) (j + 1), ‖levelSource W j c.1 c.2 - 1‖ ^ 2) ≤ 2 * y₀ :=
        fun j hj => by
          have := hm' j hj
          rwa [e4] at this
      rw [e16]
      exact (ctx Y).level_le W h0 hm2
  have hyc : c + c ≤ y₀ := by
    rw [hcv]
    linarith
  have hUc : localNorm S R U (oneSiteWeights F) Y ≤ c := by
    have : cD ≤ c := d4.trans (by linarith)
    linarith
  have hn0 : 0 ≤ localNorm S R U (oneSiteWeights F) Y := Real.sqrt_nonneg _
  have hsc' : s ≤ c / 16 := hsc.trans d4
  have hQ : s + localNorm S R U (oneSiteWeights F) Y < c / 4 := by
    have : localNorm S R U (oneSiteWeights F) Y ≤ c / 16 := hnY.trans d4
    linarith
  have hQ1 : s + localNorm S R U (oneSiteWeights F) Y ≤ 2 := by
    have h3 := hsc.trans d5
    have h4 := hnY.trans d5
    linarith
  have hv0 : localCellShare a S R V Y (zeroChart F) (fun _ _ => 0) ≤ Cv * s ^ 2 := by
    rw [cellShareInChart_eq_lowerShareInChart_add_topShareInChart]
    have hl := lowerEvaluation_zeroChart_le (Y := Y) hamb hodd ha.le (by positivity) ctxs
      (fun j hj c hc => hmean j (by omega) c hc)
    have ht : topRestriction a S R V Y (zeroChart F) (fun _ _ => 0) ≤ 8 * a * (C' * s) ^ 2 := by
      rw [topRestriction_eq_sum_topBondsAtCell]
      have hterm : ∀ b ∈ topBondsAtCell S Y, (a * bondWeight Y b) * gaugedBlockFit (chartField R (zeroChart F) F.depth)
          (chartGauge R (zeroChart F) (F.depth + 1)) (rotatedField (fun _ _ => 0) V) b ≤ a * (C' * s) ^ 2 := by
        intro b hbt
        have hbS : b ∈ innerBonds S F.top := (Finset.mem_filter.1 hbt).1
        have e1 : rotatedField (fun _ _ => (0 : imaginaryQuaternions)) V = R (F.depth + 1) := by
          rw [rotatedField_zero, hRv]
          unfold referenceFieldChain
          exact (Function.update_self _ _ _).symm
        rw [ChartFits.chartField_zeroChart hodd, chartGauge_zeroChart hodd, e1]
        have h3 := gaugedBlockFit_one_le (R F.depth) (R (F.depth + 1)) b (hmean F.depth (by simp [BlockFrame.top]) b hbS)
        have h4 : unitDeviation (referenceDefect R F.depth b) ≤ C' * s := by
          have := b4 b hbS
          simpa using this
        have h5 : ‖((R (F.depth + 1) b.1 b.2 * (polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage (R F.depth) b))⁻¹ : UnitQuaternion) :
            ℍ[ℝ]) - 1‖ ^ 2 ≤ (C' * s) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h4 2
        have h6 : 0 ≤ gaugedBlockFit (R F.depth) (fun _ => 1) (R (F.depth + 1)) b :=
          PatchLocality.gaugedBlockFit_nonneg _ _ _ _
        have h7 := mul_le_of_le_one_left h6 (bondWeight_le_one Y b)
        calc _ = a * (bondWeight Y b * gaugedBlockFit (R F.depth) (fun _ => 1) (R (F.depth + 1)) b) := by ring
          _ ≤ a * (C' * s) ^ 2 := mul_le_mul_of_nonneg_left (h7.trans (h3.trans h5)) ha.le
      refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
      rw [nsmul_eq_mul]
      have hc8 : ((topBondsAtCell S Y).card : ℝ) ≤ 8 := by exact_mod_cast card_topBondsAtCell_le
      have := mul_le_mul_of_nonneg_right hc8 (mul_nonneg ha.le (sq_nonneg (C' * s)))
      linarith
    have e1 : Cv * s ^ 2 = 81 * (1296 * (C * s) ^ 2) + a * (26 * C * s) ^ 2 + 8 * a * (C' * s) ^ 2 := by
      rw [hCvv]
      ring
    rw [e1]
    linarith
  have hK' : 0 ≤ lineDerivConst F.blockSide a ε₀ c := by
    rw [← hK₁v]
    exact hK₁
  have hval := cellShareInChart_le_sq (V := V) hamb hodd h2 ha.le ctx T hyc hs hCv hK' hv0 hQ
  rw [← hK₁v, ← hCqv] at hval
  have hshare0 : 0 ≤ localCellShare a S R V Y U fun _ _ => 0 := cellShareInChart_nonneg ha.le _ _
  have hUy : localNorm S R U (constOneWeights F) Y ≤ y₀ / 2 := by
    rw [← hcv]
    exact hUc
  have hUl : localNorm S R U (constOneWeights F) Y < y₀ := by
    have : 0 < y₀ := hy₀
    linarith
  have hAn : ∀ {ι : Type} [Fintype ι] (A : ι → ChainChart F) (e : ι → F.Site F.top → Fin 4 → imaginaryQuaternions),
      AnalyticAt ℝ (fun t : ι → ℝ => localCellShare a S R V Y (chartShiftAlong U A t) (topVariationAlong e t)) 0 := by
    intro ι _ A e
    have e1 : (fun t : ι → ℝ => localCellShare a S R V Y (chartShiftAlong U A t) (topVariationAlong e t)) = fun t =>
        lowerEvaluation a S R Y (chartShiftAlong U A t) + topRestriction a S R V Y (chartShiftAlong U A t) (topVariationAlong e t) :=
      funext fun t => cellShareInChart_eq_lowerShareInChart_add_topShareInChart a S R V Y _ _
    rw [e1]
    exact (analyticAt_lowerObservable_chartShiftAlong hamb hodd a V ctx U A hUl).add
      (analyticAt_topObservable_chartShiftAlong hamb hodd ha.le T hUc A e)
  have hfirst : ∀ (n : ℕ) (A : Fin n → ChainChart F) (e : Fin n → F.Site F.top → Fin 4 → imaginaryQuaternions), n = 1 →
      ‖localIteratedDeriv (localCellShare a S R V Y) U A e‖ ≤
        (Cq + K₁) * (s + localNorm S R U (oneSiteWeights F) Y) *
          ∏ l, localDirectionSize S R (topBondsAtCell S Y) Y (A l) (e l) := by
    intro n A e hn
    subst hn
    have eA : A = fun _ => A 0 := by
      funext l
      rw [Subsingleton.elim l 0]
    have ee : e = fun _ => e 0 := by
      funext l
      rw [Subsingleton.elim l 0]
    have h3 := norm_sliceIteratedDeriv_one_le (V := V) hamb hodd h2 ha.le ctx T hyc hs hCq hK' hQ hval (A 0) (e 0)
      (hAn (fun _ : Fin 1 => A 0) (fun _ : Fin 1 => e 0))
    rw [← hK₁v] at h3
    rw [eA, ee]
    simpa using h3
  have hsum2 : (s + localNorm S R U (oneSiteWeights F) Y) ^ 2 ≤ 4 := by
    have h0 : 0 ≤ s + localNorm S R U (oneSiteWeights F) Y := by positivity
    nlinarith
  have hc1 : c ≤ 1 := by
    rw [hcv]
    linarith
  have hQ1' : s + localNorm S R U (oneSiteWeights F) Y ≤ 1 := by linarith
  have hQ0' : 0 ≤ s + localNorm S R U (oneSiteWeights F) Y := by positivity
  have hCk0 : Ck 0 = Cq := by
    rw [hCkv]
    simp
  have hCk1 : Ck 1 = Cq + K₁ := by
    rw [hCkv]
    simp
  refine ⟨⟨fun U' U'' v hh => localCellShare_congr hodd a R V Y hh v, fun A e => hAn A e, fun n A e => ?_⟩, ?_, ?_⟩
  · rcases n with _ | _ | k'
    · have e1 : localIteratedDeriv (localCellShare a S R V Y) U A e =
          localCellShare a S R V Y U (fun _ _ => 0) := by
        unfold localIteratedDeriv
        rw [iteratedFDeriv_zero_apply, topVariationAlong_zero]
        exact localCellShare_congr hodd a R V Y (chartShiftAlong_zero U A) _
      rw [e1, Real.norm_eq_abs, abs_of_nonneg hshare0, hCk0]
      simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
      refine hval.trans ?_
      have h3 : (s + localNorm S R U (oneSiteWeights F) Y) ^ 2 ≤ 1 := by nlinarith
      exact mul_le_of_le_one_right hCq h3
    · have h3 := hfirst 1 A e rfl
      have hP : 0 ≤ ∏ l, localDirectionSize S R (topBondsAtCell S Y) Y (A l) (e l) :=
        Finset.prod_nonneg fun l _ => localDirectionSize_nonneg _ _ _ _ _ _
      have hCf : 0 ≤ Cq + K₁ := by linarith
      have e0 : (0 : ℕ) + 1 = 1 := rfl
      simp only [e0]
      rw [hCk1]
      refine h3.trans ?_
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hCf hQ1') hP
    · have h3 := norm_sliceIteratedDeriv_le_of_two_le (V := V) hmix hamb hodd h2 ha.le ctx hy₀ T hUc hUy A e
      have e1 : Ck (k' + 1 + 1) = higherDerivConst (lowerSecondDiffConst F.blockSide a) y₀ k' +
          cauchyHalvingConstant (k' + 2) * (8 * a * complexTopFitBound ε₀) /
            (c / (((k' + 2 : ℕ) : ℝ) + 1)) ^ (k' + 2) := by
        rw [hCkv]
        simp
        have e2 : (k' : ℝ) + 1 + 1 + 1 = (k' : ℝ) + 2 + 1 := by ring
        rw [e2]
      rw [e1]
      exact h3
  · rw [abs_of_nonneg hshare0, hCk0]
    exact hval
  · intro n A e hn
    rw [hCk1]
    exact hfirst n A e hn
end YangMills.Construction.CellShare
end
