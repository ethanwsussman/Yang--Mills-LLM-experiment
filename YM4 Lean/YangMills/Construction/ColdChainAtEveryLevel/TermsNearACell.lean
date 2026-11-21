import YangMills.Construction.ColdChainAtEveryLevel.DerivativesOfTheChainTotalProof
import YangMills.Construction.ColdChainAtEveryLevel.LocalFirstVariationProof
import YangMills.Construction.ColdChainAtEveryLevel.SecondDifferencesOfTheTerms
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction.NearbyCellTerms
open BlockAverages ComplexifiedQuaternions LevelRecursion CellSpans CellSources CellNormBounds ComplexLevels
  ComplexCells ComplexChainStep ComplexRemainders ComplexContours CellBounds CellSecondDifferences ComplexBondTerms
  ComplexPlaquettes PlaquettesNearCell ComplexDifferences HullBounds
variable {F : BlockFrame} {k : ℕ}
theorem analyticAt_affine_sum {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (c₀ : E) (c : Fin k → E)
    (t₀ : Fin k → ℂ) : AnalyticAt ℂ (fun w : Fin k → ℂ => c₀ + ∑ l, w l • c l) t₀ := by apply _root_.YangMills.Construction.ChartActionDerivatives.analyticAt_const_add_sum_smul <;> assumption
section Boxes
variable {S : Finset F.Cell} {Y z : F.Cell}
theorem mem_cellBall_three_of_mem_cellBall_one (hz : cellSupDist Y z ≤ 1) {y : F.Cell} (hy : y ∈ cellBall S z 1) :
    y ∈ cellBall S Y 3 := by
  classical
  obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hy
  refine Finset.mem_filter.2 ⟨h1, ?_⟩
  have := BlockAverages.PatchLocality.cellSupDist_triangle Y z y
  omega
theorem mem_bondsOver_of_mem_innerBonds (hL : Odd F.blockSide) (hz : cellSupDist Y z ≤ 1) (j : ℕ)
    {b : F.Site j × Fin 4} (hb : b ∈ innerBonds (cellBall S z 1) j) : b ∈ bondsOver S (cellBall S Y 3) j := by
  classical
  have h1 : b ∈ innerBonds S j := BlockLines.innerBonds_mono (BlockLines.cellBall_subset S z 1) j hb
  have h2 : b.1 ∈ sitesOfCells (cellBall S z 1) j := by
    simp only [innerBonds, Finset.mem_filter, Finset.mem_product] at hb
    exact hb.1.1
  exact Finset.mem_filter.2 ⟨h1, mem_cellBall_three_of_mem_cellBall_one hz (BlockLines.enclosingCell_mem hL h2)⟩
theorem finsetLpNorm_fine_le_localNorm (hL : Odd F.blockSide) (S : Finset F.Cell) (hz : cellSupDist Y z ≤ 1)
    (R : F.FieldChain) (U : ChainChart F) (w : F.SiteWeights) :
    finsetLpNorm 4 (innerBonds (cellBall S z 1) 0) (fun b => w 0 b.1 * ‖U.fine b.1 b.2‖) ≤ localNorm S R U w Y := by
  refine le_localNorm_of_sq ?_
  rw [finsetLpNorm_four_eq_sqrt_sqrt, Real.sq_sqrt (Real.sqrt_nonneg _)]
  unfold localNormSq
  have h1 : ∑ b ∈ innerBonds (cellBall S z 1) 0, (w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4 ≤
      ∑ b ∈ bondsOver S (cellBall S Y 3) 0, (w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4 :=
    Finset.sum_le_sum_of_subset_of_nonneg (fun b hb => mem_bondsOver_of_mem_innerBonds hL hz 0 hb)
      fun _ _ _ => by positivity
  have h2 := Real.sqrt_le_sqrt h1
  have h3 : 0 ≤ ∑ p ∈ plaquettesOver S (cellBall S Y 3) 0, (w 0 p.1 * ‖linearizedCurl (R 0) U.fine p‖) ^ 2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  have h4 : 0 ≤ ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (cellBall S Y 3) (j + 1),
      (w (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  linarith
theorem finsetLpNorm_coarse_le_localNorm (hL : Odd F.blockSide) (S : Finset F.Cell) (hz : cellSupDist Y z ≤ 1)
    (R : F.FieldChain) (U : ChainChart F) (w : F.SiteWeights) : finsetLpNorm 2 (lowerBonds (cellBall S z 1))
      (fun x => w (x.1 + 1) x.2.1 * ‖U.coarse x.1 x.2.1 x.2.2‖) ≤ localNorm S R U w Y := by
  refine le_localNorm_of_sq ?_
  rw [finsetLpNorm_two_eq_sqrt, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
  unfold localNormSq
  have h1 : ∑ x ∈ lowerBonds (cellBall S z 1), (w (x.1 + 1) x.2.1 * ‖U.coarse x.1 x.2.1 x.2.2‖) ^ 2 ≤
      ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (cellBall S Y 3) (j + 1),
        (w (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 := by
    rw [lowerBonds, Finset.sum_sigma]
    exact Finset.sum_le_sum fun j _ => Finset.sum_le_sum_of_subset_of_nonneg
      (fun b hb => mem_bondsOver_of_mem_innerBonds hL hz (j + 1) hb) fun _ _ _ => by positivity
  have h3 : 0 ≤ ∑ p ∈ plaquettesOver S (cellBall S Y 3) 0, (w 0 p.1 * ‖linearizedCurl (R 0) U.fine p‖) ^ 2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  have h4 : 0 ≤ Real.sqrt (∑ b ∈ bondsOver S (cellBall S Y 3) 0, (w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4) :=
    Real.sqrt_nonneg _
  linarith
theorem finsetLpNorm_curl_le_localNorm (hL : Odd F.blockSide) (S : Finset F.Cell) (hz : cellSupDist Y z ≤ 1)
    (R : F.FieldChain) (U : ChainChart F) (w : F.SiteWeights) :
    finsetLpNorm 2 (plaquettesOver S {z} 0) (fun q => w 0 q.1 * ‖linearizedCurl (R 0) U.fine q‖) ≤
      localNorm S R U w Y := by
  classical
  refine le_localNorm_of_sq ?_
  rw [finsetLpNorm_two_eq_sqrt, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
  unfold localNormSq
  have h1 : ∑ q ∈ plaquettesOver S {z} 0, (w 0 q.1 * ‖linearizedCurl (R 0) U.fine q‖) ^ 2 ≤
      ∑ q ∈ plaquettesOver S (cellBall S Y 3) 0, (w 0 q.1 * ‖linearizedCurl (R 0) U.fine q‖) ^ 2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun q hq => ?_) fun _ _ _ => by positivity
    obtain ⟨hqS, hc⟩ := Finset.mem_filter.1 hq
    have hcz : enclosingCell q.1 = z := Finset.mem_singleton.1 hc
    refine Finset.mem_filter.2 ⟨hqS, ?_⟩
    rw [hcz]
    have hq1 : q.1 ∈ sitesOfCells S 0 := (Finset.mem_product.1 (Finset.mem_filter.1 hqS).1).1
    have hzS : z ∈ S := hcz ▸ BlockLines.enclosingCell_mem hL hq1
    refine Finset.mem_filter.2 ⟨hzS, ?_⟩
    omega
  have h3 : 0 ≤ ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (cellBall S Y 3) (j + 1),
      (w (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  have h4 : 0 ≤ Real.sqrt (∑ b ∈ bondsOver S (cellBall S Y 3) 0, (w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4) :=
    Real.sqrt_nonneg _
  linarith
theorem sourceBounds_spanChart (hL : Odd F.blockSide) (hz : cellSupDist Y z ≤ 1) (R : F.FieldChain) (U : ChainChart F)
    (A : Fin k → ChainChart F) (t : Fin k → ℂ) {y : ℝ} (hy : spanLocalNorm S R U A t Y ≤ y) :
    SourceBounds S z R (spanChart U A t) y := by
  have hc : ∀ l, 0 ≤ ‖t l‖ := fun _ => norm_nonneg _
  have one_mul' : ∀ {j : ℕ} (x : F.Site j) (c : ℝ), constOneWeights F j x * c = c := fun _ c => one_mul c
  refine ⟨?_, ?_, ?_⟩
  · have h1 := finsetLpNorm_span_le (P := 4) (by norm_num) (innerBonds (cellBall S z 1) 0)
      (fun b => ‖U.fine b.1 b.2‖) (fun l b => ‖(A l).fine b.1 b.2‖) (fun l => ‖t l‖) hc
    have hU := finsetLpNorm_fine_le_localNorm hL S hz R U (constOneWeights F)
    simp only [one_mul'] at hU
    have hA : ∀ l, finsetLpNorm 4 (innerBonds (cellBall S z 1) 0) (fun b => ‖(A l).fine b.1 b.2‖) ≤
        localNorm S R (A l) (constOneWeights F) Y := fun l => by
      have := finsetLpNorm_fine_le_localNorm hL S hz R (A l) (constOneWeights F)
      simpa only [one_mul'] using this
    refine le_trans (finsetLpNorm_le_of_le (by norm_num) (fun _ _ => norm_nonneg _) fun b _ => ?_) (h1.trans ?_)
    · rw [baseSource_spanChart]
      refine (norm_add_le _ _).trans (add_le_add (le_of_eq (norm_ofQuat_imaginary _)) ((norm_sum_le _ _).trans ?_))
      refine Finset.sum_le_sum fun l _ => ?_
      rw [norm_smul, norm_ofQuat_imaginary]
    · refine le_trans (add_le_add hU (Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hA l) (hc l))) hy
  · have h1 := finsetLpNorm_span_le (P := 2) (by norm_num) (lowerBonds (cellBall S z 1))
      (fun x => ‖U.coarse x.1 x.2.1 x.2.2‖) (fun l x => ‖(A l).coarse x.1 x.2.1 x.2.2‖) (fun l => ‖t l‖) hc
    have hU := finsetLpNorm_coarse_le_localNorm hL S hz R U (constOneWeights F)
    simp only [one_mul'] at hU
    have hA : ∀ l, finsetLpNorm 2 (lowerBonds (cellBall S z 1)) (fun x => ‖(A l).coarse x.1 x.2.1 x.2.2‖) ≤
        localNorm S R (A l) (constOneWeights F) Y := fun l => by
      have := finsetLpNorm_coarse_le_localNorm hL S hz R (A l) (constOneWeights F)
      simpa only [one_mul'] using this
    refine le_trans (finsetLpNorm_le_of_le (by norm_num) (fun _ _ => norm_nonneg _) fun x _ => ?_) (h1.trans ?_)
    · rw [upperSource_spanChart]
      refine (norm_add_le _ _).trans (add_le_add (le_of_eq (norm_ofQuat_imaginary _)) ((norm_sum_le _ _).trans ?_))
      refine Finset.sum_le_sum fun l _ => ?_
      rw [norm_smul, norm_ofQuat_imaginary]
    · refine le_trans (add_le_add hU (Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hA l) (hc l))) hy
  · have h1 := finsetLpNorm_span_le (P := 2) (by norm_num) (plaquettesOver S {z} 0)
      (fun q => ‖linearizedCurl (R 0) U.fine q‖) (fun l q => ‖linearizedCurl (R 0) (A l).fine q‖) (fun l => ‖t l‖) hc
    have hU := finsetLpNorm_curl_le_localNorm hL S hz R U (constOneWeights F)
    simp only [one_mul'] at hU
    have hA : ∀ l, finsetLpNorm 2 (plaquettesOver S {z} 0) (fun q => ‖linearizedCurl (R 0) (A l).fine q‖) ≤
        localNorm S R (A l) (constOneWeights F) Y := fun l => by
      have := finsetLpNorm_curl_le_localNorm hL S hz R (A l) (constOneWeights F)
      simpa only [one_mul'] using this
    refine le_trans (finsetLpNorm_le_of_le (by norm_num) (fun _ _ => norm_nonneg _) fun q _ => ?_) (h1.trans ?_)
    · rw [baseSource_spanChart_eq, covariantCurl_add, covariantCurl_sum, covariantCurl_ofQuatForm]
      refine (norm_add_le _ _).trans (add_le_add (le_of_eq (norm_ofQuat _)) ((norm_sum_le _ _).trans ?_))
      refine Finset.sum_le_sum fun l _ => ?_
      rw [covariantCurl_smul, covariantCurl_ofQuatForm, norm_smul, norm_ofQuat]
    · refine le_trans (add_le_add hU (Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hA l) (hc l))) hy
theorem scaleWeight_zero (hodd : Odd F.blockSide) (p : F.Site 0) (m : ℕ) (x : F.Site m) : scaleWeight p 0 m x = 1 := by
  simp [scaleWeight]
theorem sourceDiff_le_localNorm (hL : Odd F.blockSide) (hz : cellSupDist Y z ≤ 1) (R : F.FieldChain) (B : ChainChart F)
    (τ : ℂ) (p : F.Site 0) :
    weightedScaleNorm (cellBall S z 1) p 0 4 0 (fun x i => ‖τ • ofQuat (B.fine x i : ℍ[ℝ])‖) +
      finsetLpNorm 2 (lowerBonds (cellBall S z 1))
        (fun x => lowerScaleWeight p 0 x * ‖τ • ofQuat (B.coarse x.1 x.2.1 x.2.2 : ℍ[ℝ])‖) +
      finsetLpNorm 2 (plaquettesOver S {z} 0)
        (fun q => scaleWeight p 0 0 q.1 * ‖τ • ofQuat (linearizedCurl (R 0) B.fine q)‖) ≤
      3 * (‖τ‖ * localNorm S R B (constOneWeights F) Y) := by
  have hc0 : 0 ≤ ‖τ‖ := norm_nonneg _
  have t1 : weightedScaleNorm (cellBall S z 1) p 0 4 0 (fun x i => ‖τ • ofQuat (B.fine x i : ℍ[ℝ])‖) ≤
      ‖τ‖ * localNorm S R B (constOneWeights F) Y := by
    have c1 := finsetLpNorm_const_mul_le (P := 4) (by norm_num) (innerBonds (cellBall S z 1) 0)
      (fun b => constOneWeights F 0 b.1 * ‖B.fine b.1 b.2‖) (a := ‖τ‖) hc0
    refine le_trans (finsetLpNorm_le_of_le (by norm_num)
      (fun b _ => mul_nonneg (scaleWeight_pos hL p 0 0 b.1).le (norm_nonneg _)) fun b hb => ?_)
      (c1.trans (mul_le_mul_of_nonneg_left (finsetLpNorm_fine_le_localNorm hL S hz R B _) hc0))
    beta_reduce
    rw [norm_smul, norm_ofQuat_imaginary, scaleWeight_zero hL]
    simp [constOneWeights]
  have t2 : finsetLpNorm 2 (lowerBonds (cellBall S z 1))
      (fun x => lowerScaleWeight p 0 x * ‖τ • ofQuat (B.coarse x.1 x.2.1 x.2.2 : ℍ[ℝ])‖) ≤
      ‖τ‖ * localNorm S R B (constOneWeights F) Y := by
    have c1 := finsetLpNorm_const_mul_le (P := 2) (by norm_num) (lowerBonds (cellBall S z 1))
      (fun x => constOneWeights F (x.1 + 1) x.2.1 * ‖B.coarse x.1 x.2.1 x.2.2‖) (a := ‖τ‖) hc0
    refine le_trans (finsetLpNorm_le_of_le (by norm_num)
      (fun x _ => mul_nonneg (lowerScaleWeight_pos hL p 0 x).le (norm_nonneg _)) fun x hx => ?_)
      (c1.trans (mul_le_mul_of_nonneg_left (finsetLpNorm_coarse_le_localNorm hL S hz R B _) hc0))
    rw [norm_smul, norm_ofQuat_imaginary]
    simp [lowerScaleWeight, scaleWeight_zero hL, constOneWeights]
  have t3 : finsetLpNorm 2 (plaquettesOver S {z} 0)
      (fun q => scaleWeight p 0 0 q.1 * ‖τ • ofQuat (linearizedCurl (R 0) B.fine q)‖) ≤
      ‖τ‖ * localNorm S R B (constOneWeights F) Y := by
    have c1 := finsetLpNorm_const_mul_le (P := 2) (by norm_num) (plaquettesOver S {z} 0)
      (fun q => constOneWeights F 0 q.1 * ‖linearizedCurl (R 0) B.fine q‖) (a := ‖τ‖) hc0
    refine le_trans (finsetLpNorm_le_of_le (by norm_num)
      (fun q _ => mul_nonneg (scaleWeight_pos hL p 0 0 q.1).le (norm_nonneg _)) fun q hq => ?_)
      (c1.trans (mul_le_mul_of_nonneg_left (finsetLpNorm_curl_le_localNorm hL S hz R B _) hc0))
    rw [norm_smul, norm_ofQuat, scaleWeight_zero hL]
    simp [constOneWeights]
  linarith
end Boxes
section Span
variable {S : Finset F.Cell} {Y z : F.Cell}
theorem cellSecondDiffSum_spanChart_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (h2 : 2 ≤ F.blockSide)
    (a : ℝ) (hz : cellSupDist Y z ≤ 1) {R : F.FieldChain} (V : F.GaugeField F.top) {C₀ s y : ℝ}
    (ctx : CellHypotheses S z R C₀ s y) (U : ChainChart F) (A : Fin k → ChainChart F) (t : Fin k → ℂ)
    (τ₁ τ₂ : ℂ) (l₁ l₂ : Fin k)
    (n₀ : spanLocalNorm S R U A t Y ≤ y) (n₁ : spanLocalNorm S R U A (t + τ₁ • (Pi.single l₁ 1 : Fin k → ℂ)) Y ≤ y)
    (n₂ : spanLocalNorm S R U A (t + τ₂ • (Pi.single l₂ 1 : Fin k → ℂ)) Y ≤ y)
    (n₃ : spanLocalNorm S R U A (t + τ₁ • (Pi.single l₁ 1 : Fin k → ℂ) + τ₂ • (Pi.single l₂ 1 : Fin k → ℂ)) Y ≤ y) :
    cellSecondDiffSum a S z R V (spanChart U A t) (spanChart U A (t + τ₁ • (Pi.single l₁ 1 : Fin k → ℂ)))
        (spanChart U A (t + τ₂ • (Pi.single l₂ 1 : Fin k → ℂ)))
        (spanChart U A (t + τ₁ • (Pi.single l₁ 1 : Fin k → ℂ) + τ₂ • (Pi.single l₂ 1 : Fin k → ℂ))) ≤
      cellSecondDiffConst (hullFactor F.blockSide) (200000 * (F.blockSide : ℝ) ^ 2)
          (1 / (2 * (200000 * (F.blockSide : ℝ) ^ 2))) a *
        ((3 * (‖τ₁‖ * localNorm S R (A l₁) (constOneWeights F) Y)) *
          (3 * (‖τ₂‖ * localNorm S R (A l₂) (constOneWeights F) Y))) := by
  have hpar := sourceParallelogram_spanChart U A (t₀ := t) (t₁ := t + τ₁ • (Pi.single l₁ 1 : Fin k → ℂ))
    (t₂ := t + τ₂ • (Pi.single l₂ 1 : Fin k → ℂ))
    (t₃ := t + τ₁ • (Pi.single l₁ 1 : Fin k → ℂ) + τ₂ • (Pi.single l₂ 1 : Fin k → ℂ)) (by abel)
  have hb := cellSecondDiffSum_le_of_sourceBounds hamb hodd h2 a V hpar ctx.small ctx.const_pos ctx.scale_pos
    ctx.const_mul_scale_le ctx.near ctx.defect_le ctx.plaquette_le
    (sourceBounds_spanChart hodd hz R U A _ n₀) (sourceBounds_spanChart hodd hz R U A _ n₁)
    (sourceBounds_spanChart hodd hz R U A _ n₂) (sourceBounds_spanChart hodd hz R U A _ n₃) ctx.level_le
    (θ := 0) (by norm_num) (0 : F.Site 0)
  refine hb.trans ?_
  simp only [neg_zero]
  have d₁ := sourceDiff_le_localNorm (S := S) hodd hz R (A l₁) τ₁ (0 : F.Site 0)
  have d₂ := sourceDiff_le_localNorm (S := S) hodd hz R (A l₂) τ₂ (0 : F.Site 0)
  obtain ⟨u₁, m₁⟩ := source_sub_single U A t τ₁ l₁
  obtain ⟨u₂, m₂⟩ := source_sub_single U A t τ₂ l₂
  simp only [u₁, u₂, m₁, m₂, covariantCurl_sourceDiff_single]
  have hK : 0 ≤ cellSecondDiffConst (hullFactor F.blockSide) (200000 * (F.blockSide : ℝ) ^ 2)
      (1 / (2 * (200000 * (F.blockSide : ℝ) ^ 2))) a := by
    have hF := hullFactor_nonneg F.blockSide
    unfold cellSecondDiffConst secondDiffConst
    positivity
  refine mul_le_mul_of_nonneg_left ?_ hK
  refine mul_le_mul d₁ d₂ ?_ ?_
  · exact add_nonneg (add_nonneg (finsetLpNorm_nonneg _ _ _) (finsetLpNorm_nonneg _ _ _)) (finsetLpNorm_nonneg _ _ _)
  · exact (add_nonneg (add_nonneg (finsetLpNorm_nonneg _ _ _) (finsetLpNorm_nonneg _ _ _))
      (finsetLpNorm_nonneg _ _ _)).trans d₁
end Span
section Operations
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] {w₀ : P} {j : ℕ}
theorem analyticAt_complexBlockFit {M X : P → ComplexQuat} (hM : AnalyticAt ℂ M w₀)
    (hs : (M w₀).det ∈ Complex.slitPlane) (hX : AnalyticAt ℂ X w₀) :
    AnalyticAt ℂ (fun w => complexBlockFit (M w) (X w)) w₀ := by apply _root_.YangMills.SharedProofs.p33576 <;> assumption
theorem analyticAt_complexGaugedContourAverage (hodd : Odd F.blockSide) {X : P → F.ComplexField j}
    (R : F.GaugeField j) (hj : j + 1 ≤ F.top) {c : F.Site (j + 1) × Fin 4} {t σ : ℝ} (ht : 0 ≤ t)
    (hτ : 4 * (F.blockSide : ℝ) * t ≤ 1 / 1024) (hg : ContoursNearReal (X w₀) R t σ c)
    (hX : HoldsOnHull c (fun b i => AnalyticAt ℂ (fun w => X w b i) w₀)) :
    AnalyticAt ℂ (fun w => complexGaugedContourAverage (X w) (complexBalancingGauge (X w) R) c) w₀ := by
  have hleg : ∀ h ∈ centredCube F.blockSide, ∀ π,
      AnalyticAt ℂ (fun w => complexPathHolonomy (X w) (refineSite c.1) (axisPath h π)) w₀ :=
    fun h hh π => ComplexAnalyticity.analyticAt_complexPathHolonomy
      (pathBondsSatisfy_axisPath _ hodd.pos (fun v hv k hk => (hX.1 v hv k hk).1) hh π)
  have hleg' : ∀ h ∈ centredCube F.blockSide, ∀ π, AnalyticAt ℂ
      (fun w => complexPathHolonomy (X w) (refineSite (c.1 + unitStep (j + 1) c.2)) (axisPath h π)) w₀ :=
    fun h hh π => ComplexAnalyticity.analyticAt_complexPathHolonomy
      (pathBondsSatisfy_axisPath _ hodd.pos (fun v hv k hk => (hX.1 v hv k hk).2) hh π)
  have hline : ∀ h ∈ centredCube F.blockSide, AnalyticAt ℂ
      (fun w => complexPathHolonomy (X w) (refineSite c.1 + siteOfCoords j h)
        (List.replicate F.blockSide (c.2, true))) w₀ :=
    fun h hh => ComplexAnalyticity.analyticAt_complexPathHolonomy
      (pathBondsSatisfy_replicate _ _ _ fun r hr => hX.2 h hh r hr)
  have hcm : AnalyticAt ℂ (fun w => complexContourAverage (X w) c) w₀ := by
    simp only [complexContourAverage]
    have hs : AnalyticAt ℂ (fun w => ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
        complexPathHolonomy (X w) (refineSite c.1) (bondContour F.blockSide h π c.2)) w₀ := by
      refine Finset.analyticAt_fun_sum _ fun h hh => Finset.analyticAt_fun_sum _ fun π _ => ?_
      simp only [complexPathHolonomy_bondContour hj]
      exact ((hleg h hh π).mul (hline h hh)).mul (ComplexAnalyticity.analyticAt_adjugate (hleg' h hh π))
    exact ComplexAnalyticity.analyticAt_const_smul_complexQuat _ hs
  have hτ8 : 4 * (F.blockSide : ℝ) * t ≤ 1 / 8 := by linarith
  have hk := ComplexAnalyticity.analyticAt_complexBalancingGauge hodd R ht hτ8 hleg hg.nearLegs
  have hk' := ComplexAnalyticity.analyticAt_complexBalancingGauge hodd R ht hτ8 hleg' hg.nearFarLegs
  simp only [complexGaugedContourAverage]
  exact (hk.mul hcm).mul (ComplexAnalyticity.analyticAt_adjugate hk')
end Operations
section Each
theorem analyticAt_cellTerms {S : Finset F.Cell} {R : F.FieldChain} (V : F.GaugeField F.top) (hodd : Odd F.blockSide)
    (hamb : IsAdmissibleAmbient F) {m : ℕ} (W : (Fin m → ℂ) → ComplexChainChart F) (t₀ : Fin m → ℂ) (z : F.Cell)
    (t σ : ℝ) (ht : 0 ≤ t) (ht1 : t < 1) (hσ : σ ≤ 1 / 64)
    (hsm : 8 * (F.blockSide : ℝ) * (hullBondCount F.blockSide * t) ≤ 1 / 1024)
    (hu : ∀ b ∈ innerBonds (cellBall S z 1) 0,
      AnalyticAt ℂ (fun w => complexifiedImaginary ((W w).re.fine b.1 b.2) ((W w).im.fine b.1 b.2)) t₀)
    (hu1 : ∀ b ∈ innerBonds (cellBall S z 1) 0,
      ‖complexifiedImaginary ((W t₀).re.fine b.1 b.2) ((W t₀).im.fine b.1 b.2)‖ ≤ 1 / 16)
    (hmu : ∀ j, j + 1 < F.top → ∀ b ∈ innerBonds (cellBall S z 1) (j + 1),
      AnalyticAt ℂ (fun w => complexifiedImaginary ((W w).re.coarse j b.1 b.2) ((W w).im.coarse j b.1 b.2)) t₀)
    (hmu1 : ∀ j, j + 1 < F.top → ∀ b ∈ innerBonds (cellBall S z 1) (j + 1),
      ‖complexifiedImaginary ((W t₀).re.coarse j b.1 b.2) ((W t₀).im.coarse j b.1 b.2)‖ ≤ 1 / 16)
    (hgap : ∀ j, j < F.top → ∀ b ∈ innerBonds (cellBall S z 1) j, ‖levelDeviation R (W t₀) j b.1 b.2‖ ≤ t)
    (href : ∀ j, j + 1 ≤ F.top → ∀ c ∈ innerBonds (cellBall S z 1) (j + 1), ∀ h ∈ centredCube F.blockSide, ∀ π,
      ‖ofUnit (pathHolonomy (R j) (refineSite c.1) (bondContour F.blockSide h π c.2) *
        (polarUnit (contourAverage (R j) c))⁻¹) - 1‖ ≤ σ) :
    (∀ p ∈ plaquettesOver S {z} 0,
      AnalyticAt ℂ (fun w => complexPlaquetteTerm (complexChartField R (W w) 0) p) t₀) ∧
    ∀ j, j + 1 < F.top → ∀ c ∈ bondsOver S {z} (j + 1),
      AnalyticAt ℂ (fun w => complexBondTerm R (W w) V j c) t₀ ∧
        0 < (complexGaugedContourAverage (complexChartField R (W t₀) j)
          (complexBalancingGauge (complexChartField R (W t₀) j) (R j)) c).det.re := by
  have hL1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  have hτ : 4 * (F.blockSide : ℝ) * t ≤ 1 / 1024 := by
    have hc : (1 : ℝ) ≤ hullBondCount F.blockSide := by
      unfold hullBondCount
      have h1 : (1 : ℝ) ≤ (F.blockSide : ℝ) ^ 4 := one_le_pow₀ hL1
      have h2 : (0 : ℝ) ≤ (F.blockSide : ℝ) ^ 5 := by positivity
      linarith
    have h1 : t ≤ hullBondCount F.blockSide * t := le_mul_of_one_le_left ht hc
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 8 * (F.blockSide : ℝ))
    have h3 : 0 ≤ (F.blockSide : ℝ) * t := by positivity
    linarith
  have hF := ComplexAnalyticity.analyticAt_complexChartField hodd R ht ht1 hσ hτ hu hu1 hmu hmu1 hgap href
  have hF0 : ∀ b ∈ innerBonds (cellBall S z 1) 0,
      AnalyticAt ℂ (fun w => complexChartField R (W w) 0 b.1 b.2) t₀ := by
    intro b hb
    simp only [complexChartField]
    exact (ComplexAnalyticity.analyticAt_unitExp (hu b hb) (hu1 b hb)).mul analyticAt_const
  have hplaq : ∀ p ∈ plaquettesOver S {z} 0,
      AnalyticAt ℂ (fun w => complexPlaquetteTerm (complexChartField R (W w) 0) p) t₀ := by
    intro p hp
    obtain ⟨b1, b2, b3, b4⟩ := plaquette_bonds_mem_innerBonds hamb hodd hp
    have hpath : PathBondsSatisfy (fun b i => AnalyticAt ℂ (fun w => complexChartField R (W w) 0 b i) t₀) p.1
        [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] := by
      have e3 : p.1 + unitStep 0 p.2.1 + unitStep 0 p.2.2 - unitStep 0 p.2.1 = p.1 + unitStep 0 p.2.2 := by abel
      have e4 : p.1 + unitStep 0 p.2.1 + unitStep 0 p.2.2 + -unitStep 0 p.2.1 - unitStep 0 p.2.2 = p.1 := by abel
      simp only [PathBondsSatisfy, crossedBond, stepDisplacement, if_true, Bool.false_eq_true, if_false, e3, e4,
        and_true]
      exact ⟨hF0 (p.1, p.2.1) b1, hF0 (p.1 + unitStep 0 p.2.1, p.2.2) b2, hF0 (p.1 + unitStep 0 p.2.2, p.2.1) b3,
        hF0 (p.1, p.2.2) b4⟩
    simp only [complexPlaquetteTerm, complexPlaquetteHolonomy]
    exact analyticAt_const.sub
      (ComplexAnalyticity.analyticAt_trace (ComplexAnalyticity.analyticAt_complexPathHolonomy hpath)).div_const
  have hmean : ∀ j, j < F.top → ∀ c ∈ innerBonds (cellBall S z 1) (j + 1),
      AnalyticAt ℂ (fun w => complexGaugedContourAverage (complexChartField R (W w) j)
        (complexBalancingGauge (complexChartField R (W w) j) (R j)) c) t₀ ∧
        0 < (complexGaugedContourAverage (complexChartField R (W t₀) j)
          (complexBalancingGauge (complexChartField R (W t₀) j) (R j)) c).det.re := by
    intro j hj c hc
    have hgood : ∀ b ∈ innerBonds (cellBall S z 1) j,
        BondNearReal (complexChartField R (W t₀) j) (R j) t b.1 b.2 := fun b hb =>
      ⟨hgap j hj b hb, det_complexChartField_of_norm_lt_one R (W t₀) j _ _ (lt_of_le_of_lt (hgap j hj b hb) ht1)⟩
    have hhull : HoldsOnHull c (fun b i => BondNearReal (complexChartField R (W t₀) j) (R j) t b i) :=
      holdsOnHull_of_innerBonds hj hodd hc hgood
    have hcg : ContoursNearReal (complexChartField R (W t₀) j) (R j) t σ c :=
      ⟨fun h hh π => pathNearReal_axisPath _ hodd.pos (fun v hv k hk => (hhull.1 v hv k hk).1) hh π,
        fun h hh => pathNearReal_replicate _ _ _ fun r hr => hhull.2 h hh r hr,
        fun h hh π => pathNearReal_axisPath _ hodd.pos (fun v hv k hk => (hhull.1 v hv k hk).2) hh π,
        fun h hh π => href j (by omega) c hc h hh π⟩
    have hX : HoldsOnHull c (fun b i => AnalyticAt ℂ (fun w => complexChartField R (W w) j b i) t₀) :=
      holdsOnHull_of_innerBonds hj hodd hc fun b hb => hF j hj b hb
    exact ⟨analyticAt_complexGaugedContourAverage (X := fun w => complexChartField R (W w) j) hodd (R j)
        (by omega) ht hτ hcg hX,
      (unitPart_and_sqrt_near hodd (by omega) ht hσ hτ hcg).1⟩
  refine ⟨hplaq, fun j hj c hc => ?_⟩
  have hj' : j < F.top := by omega
  have hcD : c ∈ innerBonds (cellBall S z 1) (j + 1) :=
    BlockLines.mem_innerBonds_cellBall_of_mem_bondsOver hamb hodd S z (by omega) hc
  obtain ⟨hM, hre⟩ := hmean j hj' c hcD
  refine ⟨?_, hre⟩
  have e : (fun w => complexBondTerm R (W w) V j c) = fun w =>
      complexBlockFit (complexGaugedContourAverage (complexChartField R (W w) j)
          (complexBalancingGauge (complexChartField R (W w) j) (R j)) c)
        (complexChartField R (W w) (j + 1) c.1 c.2) := by
    funext w
    simp only [complexBondTerm, complexFieldChain_of_ne R (W w) V (k := j) (by omega),
      complexFieldChain_of_ne R (W w) V (k := j + 1) (by omega), complexBalancingGauges]
  rw [e]
  exact analyticAt_complexBlockFit hM (Or.inl hre) (hF (j + 1) (by omega) c hcD)
theorem analyticAt_cellTerms_spanChart {S : Finset F.Cell} {Y z : F.Cell} {R : F.FieldChain}
    (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (hz : cellSupDist Y z ≤ 1) (V : F.GaugeField F.top)
    {C₀ s y : ℝ} (ctx : CellHypotheses S z R C₀ s y) (U : ChainChart F) (A : Fin k → ChainChart F)
    {t₀ : Fin k → ℂ} (h0 : spanLocalNorm S R U A t₀ Y ≤ y) :
    (∀ p ∈ plaquettesOver S {z} 0,
      AnalyticAt ℂ (fun t => complexPlaquetteTerm (complexChartField R (spanChart U A t) 0) p) t₀) ∧
    ∀ j, j + 1 < F.top → ∀ c ∈ bondsOver S {z} (j + 1),
      AnalyticAt ℂ (fun t => complexBondTerm R (spanChart U A t) V j c) t₀ ∧
        0 < (complexGaugedContourAverage (complexChartField R (spanChart U A t₀) j)
          (complexBalancingGauge (complexChartField R (spanChart U A t₀) j) (R j)) c).det.re := by
  have hL1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  have hy := ctx.small
  have hy0 := hy.pos
  have hy1 := hy.le_bound
  have hsz := sourceBounds_spanChart hodd hz R U A t₀ h0
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
  refine analyticAt_cellTerms V hodd hamb (spanChart U A) t₀ z (8 * y) (C₀ * s) (by positivity) (by linarith)
    ((ctx.const_mul_scale_le).trans (by linarith)) hsmall ?_ ?_ ?_ ?_ hball.norm_deviation_le ?_
  · intro b _
    have e : (fun w => complexifiedImaginary ((spanChart U A w).re.fine b.1 b.2) ((spanChart U A w).im.fine b.1 b.2)) =
        fun w => ofQuat (U.fine b.1 b.2 : ℍ[ℝ]) + ∑ l, w l • ofQuat ((A l).fine b.1 b.2 : ℍ[ℝ]) := by
      funext w
      exact baseSource_spanChart U A w b.1 b.2
    rw [e]
    exact analyticAt_affine_sum _ _ _
  · intro b hb
    exact (hss.base_le b hb).trans (by norm_num)
  · intro j _ b _
    have e : (fun w => complexifiedImaginary ((spanChart U A w).re.coarse j b.1 b.2)
        ((spanChart U A w).im.coarse j b.1 b.2)) =
        fun w => ofQuat (U.coarse j b.1 b.2 : ℍ[ℝ]) + ∑ l, w l • ofQuat ((A l).coarse j b.1 b.2 : ℍ[ℝ]) := by
      funext w
      exact upperSource_spanChart U A w ⟨j, b⟩
    rw [e]
    exact analyticAt_affine_sum _ _ _
  · intro j hj b hb
    exact (hss.upper_le _ (mem_lowerBonds hj hb)).trans (by norm_num)
  · intro j hj c hc h hh π
    refine (ctx.near j hj c hc h hh π).trans ?_
    have hCs : 0 ≤ C₀ * s := mul_nonneg ctx.const_pos.le ctx.scale_pos.le
    have h3 : ((1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1))) ^ 2 ≤ 1 :=
      pow_le_one₀ (by positivity) (inv_pow_le_one hodd.pos _)
    exact mul_le_of_le_one_right hCs h3
end Each
end YangMills.Construction.NearbyCellTerms
end
