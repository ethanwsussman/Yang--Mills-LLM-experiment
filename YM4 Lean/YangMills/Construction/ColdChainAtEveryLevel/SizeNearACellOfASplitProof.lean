import YangMills.Construction.ColdChainAtEveryLevel.GapsOfTheLevelsNearACellProof
import YangMills.Construction.ColdChainAtEveryLevel.SizeNearACellOfASplit
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
namespace SplitChartNearCell
variable {F : BlockFrame}
theorem cellSupDist_comm (y z : F.Cell) : cellSupDist y z = cellSupDist z y := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_comm <;> assumption
theorem sum_pow_rpow_inv_le_add {ι : Type*} (s : Finset ι) (p : ℕ) (hp : 1 ≤ p) (f g h : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i) (hh : ∀ i ∈ s, 0 ≤ h i)
    (hle : ∀ i ∈ s, f i ≤ g i + h i) :
    (∑ i ∈ s, f i ^ p) ^ (1 / (p : ℝ)) ≤
      (∑ i ∈ s, g i ^ p) ^ (1 / (p : ℝ)) + (∑ i ∈ s, h i ^ p) ^ (1 / (p : ℝ)) := by apply _root_.YangMills.Construction.LevelGaps.finset_minkowski_natPow <;> assumption
def fineQuarticPart (S B : Finset F.Cell) (U : ChainChart F) : ℝ :=
  (∑ b ∈ bondsOver S B 0, ‖U.fine b.1 b.2‖ ^ 4) ^ (1 / ((4 : ℕ) : ℝ))
def curlPart (S B : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) : ℝ :=
  (∑ p ∈ plaquettesOver S B 0, ‖linearizedCurl (R 0) U.fine p‖ ^ 2) ^ (1 / ((2 : ℕ) : ℝ))
def coarsePart (S B : Finset F.Cell) (U : ChainChart F) : ℝ :=
  (∑ c ∈ (Finset.range (F.top - 1)).sigma fun j => bondsOver S B (j + 1),
    ‖U.coarse c.1 c.2.1 c.2.2‖ ^ 2) ^ (1 / ((2 : ℕ) : ℝ))
theorem fineQuarticPart_nonneg (S B : Finset F.Cell) (U : ChainChart F) : 0 ≤ fineQuarticPart S B U :=
  Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => by positivity) _
theorem curlPart_nonneg (S B : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) :
    0 ≤ curlPart S B R U :=
  Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => by positivity) _
theorem coarsePart_nonneg (S B : Finset F.Cell) (U : ChainChart F) : 0 ≤ coarsePart S B U :=
  Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => by positivity) _
theorem localNormSq_oneSiteWeights (S B : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) :
    localNormSq S B R U (oneSiteWeights F) =
      fineQuarticPart S B U ^ 2 + curlPart S B R U ^ 2 + coarsePart S B U ^ 2 := by
  have h4 : 0 ≤ ∑ b ∈ bondsOver S B 0, ‖U.fine b.1 b.2‖ ^ 4 :=
    Finset.sum_nonneg fun _ _ => by positivity
  have h2 : 0 ≤ ∑ p ∈ plaquettesOver S B 0, ‖linearizedCurl (R 0) U.fine p‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  have h3 : 0 ≤ ∑ c ∈ (Finset.range (F.top - 1)).sigma fun j => bondsOver S B (j + 1),
      ‖U.coarse c.1 c.2.1 c.2.2‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  unfold localNormSq fineQuarticPart curlPart coarsePart oneSiteWeights
  simp only [one_mul]
  rw [Finset.sum_sigma' (Finset.range (F.top - 1)) (fun j => bondsOver S B (j + 1))
    (fun j c => ‖U.coarse j c.1 c.2‖ ^ 2)]
  have e4 : ((∑ b ∈ bondsOver S B 0, ‖U.fine b.1 b.2‖ ^ 4) ^ (1 / ((4 : ℕ) : ℝ))) ^ 2 =
      Real.sqrt (∑ b ∈ bondsOver S B 0, ‖U.fine b.1 b.2‖ ^ 4) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul h4]
    norm_num
  have e2 : ∀ x : ℝ, 0 ≤ x → (x ^ (1 / ((2 : ℕ) : ℝ))) ^ 2 = x := by
    intro x hx
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    norm_num
  rw [e4, e2 _ h2, e2 _ h3]
theorem localNorm_oneSiteWeights (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (z : F.Cell) :
    localNorm S R U (oneSiteWeights F) z =
      (∑ i : Fin 3, (![fineQuarticPart S (cellBall S z 3) U, curlPart S (cellBall S z 3) R U,
        coarsePart S (cellBall S z 3) U] i) ^ 2) ^ (1 / ((2 : ℕ) : ℝ)) := by
  unfold localNorm
  rw [localNormSq_oneSiteWeights, Real.sqrt_eq_rpow, Fin.sum_univ_three]
  norm_num
  rfl
theorem innerBonds_of_mem_innerPlaquettes {S : Finset F.Cell} {p : F.Site 0 × Fin 4 × Fin 4}
    (hp : p ∈ innerPlaquettes S 0) :
    (p.1, p.2.1) ∈ innerBonds S 0 ∧ (p.1 + unitStep 0 p.2.1, p.2.2) ∈ innerBonds S 0 ∧
      (p.1 + unitStep 0 p.2.2, p.2.1) ∈ innerBonds S 0 ∧ (p.1, p.2.2) ∈ innerBonds S 0 := by
  have hc := (Finset.mem_filter.1 hp).2.2
  have c1 : p.1 ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
  have c2 : p.1 + unitStep 0 p.2.1 ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
  have c3 : p.1 + unitStep 0 p.2.2 ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
  have c4 : p.1 + unitStep 0 p.2.1 + unitStep 0 p.2.2 ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
  have c4' : p.1 + unitStep 0 p.2.2 + unitStep 0 p.2.1 ∈ sitesOfCells S 0 := by
    rw [add_right_comm]
    exact c4
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
  · exact ⟨c1, c2⟩
  · exact ⟨c2, c4⟩
  · exact ⟨c3, c4'⟩
  · exact ⟨c1, c3⟩
theorem adjointAction_add (g : UnitQuaternion) (x y : ℍ[ℝ]) :
    adjointAction g (x + y) = adjointAction g x + adjointAction g y := by apply _root_.YangMills.Construction.BlockAverages.adjointAction_add <;> assumption
theorem linearizedCurl_eq_add (R : F.GaugeField 0) (U A B : ChainChart F) (S : Finset F.Cell)
    (hs : ChartEqOnBonds S U (chartSum A B)) {p : F.Site 0 × Fin 4 × Fin 4}
    (hp : p ∈ innerPlaquettes S 0) :
    linearizedCurl R U.fine p = linearizedCurl R A.fine p + linearizedCurl R B.fine p := by
  obtain ⟨b1, b2, b3, b4⟩ := innerBonds_of_mem_innerPlaquettes hp
  have e : ∀ b ∈ innerBonds S 0,
      (U.fine b.1 b.2 : ℍ[ℝ]) = (A.fine b.1 b.2 : ℍ[ℝ]) + (B.fine b.1 b.2 : ℍ[ℝ]) := by
    intro b hb
    rw [hs.1 b hb]
    simp [chartSum, chartMove]
  have e1 := e _ b1
  have e2 := e _ b2
  have e3 := e _ b3
  have e4 := e _ b4
  simp only at e1 e2 e3 e4
  unfold linearizedCurl
  simp only [e1, e2, e3, e4, adjointAction_add]
  abel
theorem localNorm_le_add (S : Finset F.Cell) (R : F.FieldChain) (U A B : ChainChart F) (z : F.Cell)
    (hs : ChartEqOnBonds S U (chartSum A B)) :
    localNorm S R U (oneSiteWeights F) z ≤
      localNorm S R A (oneSiteWeights F) z + localNorm S R B (oneSiteWeights F) z := by
  have hbond : ∀ b ∈ bondsOver S (cellBall S z 3) 0,
      ‖U.fine b.1 b.2‖ ≤ ‖A.fine b.1 b.2‖ + ‖B.fine b.1 b.2‖ := by
    intro b hb
    have hb' : b ∈ innerBonds S 0 := (Finset.mem_filter.1 hb).1
    rw [hs.1 b hb']
    simp only [chartSum, chartMove, one_smul]
    exact norm_add_le _ _
  have h4 : fineQuarticPart S (cellBall S z 3) U ≤
      fineQuarticPart S (cellBall S z 3) A + fineQuarticPart S (cellBall S z 3) B :=
    sum_pow_rpow_inv_le_add _ 4 (by norm_num) _ _ _ (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _)
      (fun _ _ => norm_nonneg _) hbond
  have hcurl : ∀ p ∈ plaquettesOver S (cellBall S z 3) 0, ‖linearizedCurl (R 0) U.fine p‖ ≤
      ‖linearizedCurl (R 0) A.fine p‖ + ‖linearizedCurl (R 0) B.fine p‖ := by
    intro p hp
    rw [linearizedCurl_eq_add (R 0) U A B S hs (Finset.mem_filter.1 hp).1]
    exact norm_add_le _ _
  have h2 : curlPart S (cellBall S z 3) R U ≤
      curlPart S (cellBall S z 3) R A + curlPart S (cellBall S z 3) R B :=
    sum_pow_rpow_inv_le_add _ 2 (by norm_num) _ _ _ (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _)
      (fun _ _ => norm_nonneg _) hcurl
  have hco : ∀ c ∈ (Finset.range (F.top - 1)).sigma (fun j => bondsOver S (cellBall S z 3) (j + 1)),
      ‖U.coarse c.1 c.2.1 c.2.2‖ ≤ ‖A.coarse c.1 c.2.1 c.2.2‖ + ‖B.coarse c.1 c.2.1 c.2.2‖ := by
    intro c hc
    obtain ⟨hj, hb⟩ := Finset.mem_sigma.1 hc
    have hj' : c.1 + 1 < F.top := by
      have := Finset.mem_range.1 hj
      omega
    rw [hs.2 c.1 hj' c.2 (Finset.mem_filter.1 hb).1]
    simp only [chartSum, chartMove, one_smul]
    exact norm_add_le _ _
  have h3 : coarsePart S (cellBall S z 3) U ≤
      coarsePart S (cellBall S z 3) A + coarsePart S (cellBall S z 3) B :=
    sum_pow_rpow_inv_le_add _ 2 (by norm_num) _ _ _ (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _)
      (fun _ _ => norm_nonneg _) hco
  rw [localNorm_oneSiteWeights, localNorm_oneSiteWeights, localNorm_oneSiteWeights]
  refine sum_pow_rpow_inv_le_add Finset.univ 2 (by norm_num) _ _ _ ?_ ?_ ?_ ?_
  · intro i _
    fin_cases i
    · exact fineQuarticPart_nonneg _ _ _
    · exact curlPart_nonneg _ _ _ _
    · exact coarsePart_nonneg _ _ _
  · intro i _
    fin_cases i
    · exact fineQuarticPart_nonneg _ _ _
    · exact curlPart_nonneg _ _ _ _
    · exact coarsePart_nonneg _ _ _
  · intro i _
    fin_cases i
    · exact fineQuarticPart_nonneg _ _ _
    · exact curlPart_nonneg _ _ _ _
    · exact coarsePart_nonneg _ _ _
  · intro i _
    fin_cases i
    · exact h4
    · exact h2
    · exact h3
theorem sq_mul_localNormSq_le (S B : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F)
    (w : F.SiteWeights) (l : ℝ)
    (hl : 0 ≤ l) (hw : ∀ (j : ℕ) (x : F.Site j), enclosingCell x ∈ B → l ≤ w j x) :
    l ^ 2 * localNormSq S B R U (oneSiteWeights F) ≤ localNormSq S B R U w := by
  unfold localNormSq oneSiteWeights
  simp only [one_mul]
  have hsq : ∀ (x y : ℝ), 0 ≤ y → l ≤ x → l ^ 2 * y ^ 2 ≤ (x * y) ^ 2 := by
    intro x y hy hx
    have : l * y ≤ x * y := mul_le_mul_of_nonneg_right hx hy
    have := pow_le_pow_left₀ (mul_nonneg hl hy) this 2
    calc l ^ 2 * y ^ 2 = (l * y) ^ 2 := by ring
      _ ≤ _ := this
  have hA : l ^ 2 * Real.sqrt (∑ b ∈ bondsOver S B 0, ‖U.fine b.1 b.2‖ ^ 4) ≤
      Real.sqrt (∑ b ∈ bondsOver S B 0, (w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4) := by
    have h1 : l ^ 2 = Real.sqrt (l ^ 4) := by
      rw [show l ^ 4 = (l ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    rw [h1, ← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b hb => ?_
    have hx := hw 0 b.1 (Finset.mem_filter.1 hb).2
    have : l * ‖U.fine b.1 b.2‖ ≤ w 0 b.1 * ‖U.fine b.1 b.2‖ :=
      mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    have := pow_le_pow_left₀ (mul_nonneg hl (norm_nonneg _)) this 4
    calc l ^ 4 * ‖U.fine b.1 b.2‖ ^ 4 = (l * ‖U.fine b.1 b.2‖) ^ 4 := by ring
      _ ≤ _ := this
  have hB : l ^ 2 * ∑ p ∈ plaquettesOver S B 0, ‖linearizedCurl (R 0) U.fine p‖ ^ 2 ≤
      ∑ p ∈ plaquettesOver S B 0, (w 0 p.1 * ‖linearizedCurl (R 0) U.fine p‖) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun p hp => hsq _ _ (norm_nonneg _) (hw 0 p.1 (Finset.mem_filter.1 hp).2)
  have hC : l ^ 2 * ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S B (j + 1), ‖U.coarse j c.1 c.2‖ ^ 2 ≤
      ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S B (j + 1),
        (w (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun c hc => hsq _ _ (norm_nonneg _) (hw (j + 1) c.1 (Finset.mem_filter.1 hc).2)
  calc _ = l ^ 2 * Real.sqrt (∑ b ∈ bondsOver S B 0, ‖U.fine b.1 b.2‖ ^ 4) +
        l ^ 2 * ∑ p ∈ plaquettesOver S B 0, ‖linearizedCurl (R 0) U.fine p‖ ^ 2 +
        l ^ 2 * ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S B (j + 1), ‖U.coarse j c.1 c.2‖ ^ 2 := by
        ring
    _ ≤ _ := add_le_add (add_le_add hA hB) hC
theorem localNorm_le_exp_mul_decayWeights (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F)
    (δ : ℝ) (hδ : 0 ≤ δ) (p : F.Site 0) (z : F.Cell) :
    localNorm S R U (oneSiteWeights F) z ≤
      Real.exp (3 * δ) * localNorm S R U (decayWeights F δ 0 p z) z := by
  have hw : ∀ (j : ℕ) (x : F.Site j), enclosingCell x ∈ cellBall S z 3 →
      Real.exp (-(3 * δ)) ≤ decayWeights F δ 0 p z j x := by
    intro j x hx
    have hdist : cellSupDist z (enclosingCell x) ≤ 3 := (Finset.mem_filter.1 hx).2
    simp only [decayWeights, neg_zero, Real.rpow_zero, mul_one]
    refine Real.exp_le_exp.2 ?_
    rw [cellSupDist_comm]
    have : ((cellSupDist z (enclosingCell x) : ℕ) : ℝ) ≤ 3 := by exact_mod_cast hdist
    nlinarith
  have h := sq_mul_localNormSq_le S (cellBall S z 3) R U (decayWeights F δ 0 p z) _
    (Real.exp_pos _).le hw
  unfold localNorm
  have hE : Real.exp (3 * δ) = Real.sqrt ((Real.exp (3 * δ)) ^ 2) :=
    (Real.sqrt_sq (Real.exp_pos _).le).symm
  rw [hE, ← Real.sqrt_mul (by positivity)]
  refine Real.sqrt_le_sqrt ?_
  have hee : Real.exp (3 * δ) ^ 2 * Real.exp (-(3 * δ)) ^ 2 = 1 := by
    rw [← mul_pow, ← Real.exp_add]
    simp
  calc localNormSq S (cellBall S z 3) R U (oneSiteWeights F)
      = Real.exp (3 * δ) ^ 2 *
          (Real.exp (-(3 * δ)) ^ 2 * localNormSq S (cellBall S z 3) R U (oneSiteWeights F)) := by
        rw [← mul_assoc, hee, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)
theorem localNorm_le_weightedNorm (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F)
    (w : F.SiteWeights) {z : F.Cell} (hz : z ∈ S) : localNorm S R U w z ≤ weightedNorm S R U w := by apply _root_.YangMills.Construction.BlockWeights.localNorm_le_weightedNorm <;> assumption
theorem exp_three_mul_le_two {δ : ℝ} (hδ : δ ≤ 1 / 8) : Real.exp (3 * δ) ≤ 2 := by
  have h1 : Real.exp (3 * δ) ≤ Real.exp (1 / 2) := Real.exp_le_exp.2 (by linarith)
  have h2 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h3 := Real.exp_one_lt_d9
  have h4 : 0 < Real.exp (1 / 2) := Real.exp_pos _
  nlinarith
end SplitChartNearCell
open SplitChartNearCell in
theorem splitChartNearCell : splitChartNearCellStatement := by
  intro F S R U Ul Ur δ A B z hz hδ hδ8 hsame hA hB
  have e1 := localNorm_le_exp_mul_decayWeights S R Ul δ hδ 0 z
  have e2 := localNorm_le_exp_mul_decayWeights S R Ur δ hδ 0 z
  have f1 := (localNorm_le_weightedNorm S R Ul (decayWeights F δ 0 0 z) hz).trans hA
  have f2 := (localNorm_le_weightedNorm S R Ur (decayWeights F δ 0 0 z) hz).trans hB
  have hE := exp_three_mul_le_two hδ8
  have g1 : Real.exp (3 * δ) * localNorm S R Ul (decayWeights F δ 0 0 z) z ≤ 2 * A :=
    mul_le_mul hE f1 (Real.sqrt_nonneg _) (by norm_num)
  have g2 : Real.exp (3 * δ) * localNorm S R Ur (decayWeights F δ 0 0 z) z ≤ 2 * B :=
    mul_le_mul hE f2 (Real.sqrt_nonneg _) (by norm_num)
  have := localNorm_le_add S R U Ul Ur z hsame
  linarith
end YangMills.Construction.BlockAverages
end
