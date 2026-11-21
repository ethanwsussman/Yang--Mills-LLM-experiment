import YangMills.Construction.ColdChainAtEveryLevel.AnalyticSharesOfAColdTopProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
namespace ComparedMixedDeriv
variable {F : BlockFrame}
theorem topVariationNorm_partSpread_le {k p : ℕ} (B : Finset (F.Site F.top × Fin 4))
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (hX : AreUnitVectors X)
    {M : ℝ} (hM : 1 ≤ M) (hp : 1 ≤ p) (f : Fin p ↪ Fin k) :
    topVariationNorm B (partSpread c X f) ≤ M := by apply _root_.YangMills.Construction.BlockAverages.AnalyticCellShares.topVariationNorm_partSpread_le <;> assumption
theorem offsetChartGapNorm_nonneg {F' : BlockFrame} (S : Finset F.Cell) (R : F.FieldChain)
    (z Y : F.Cell) (Y' : F'.Cell) (A : ChainChart F) (A' : ChainChart F') :
    0 ≤ offsetChartGapNorm S R z Y Y' A A' :=
  Real.sqrt_nonneg _
theorem localDirectionSize_nonneg (S : Finset F.Cell) (R : F.FieldChain)
    (B : Finset (F.Site F.top × Fin 4)) (z : F.Cell) (A : ChainChart F)
    (e : F.Site F.top → Fin 4 → imaginaryQuaternions) : 0 ≤ localDirectionSize S R B z A e := by apply _root_.YangMills.Construction.BlockAverages.AnalyticCellShares.localDirectionSize_nonneg <;> assumption
theorem localIteratedDeriv_congr {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Finset F.Cell} {m : ℕ}
    {Φ : ChainChart F → (F.Site F.top → Fin 4 → imaginaryQuaternions) → E} {U : ChainChart F}
    (hΦ : ∀ U' U'' v, ChartEqOnBonds S U' U'' → Φ U' v = Φ U'' v) {A A' : Fin m → ChainChart F}
    (e : Fin m → F.Site F.top → Fin 4 → imaginaryQuaternions)
    (h : ∀ l, ChartEqOnBonds S (A l) (A' l)) :
    localIteratedDeriv Φ U A e = localIteratedDeriv Φ U A' e := by
  unfold localIteratedDeriv
  congr 2
  funext t
  refine hΦ _ _ _ ⟨fun b hb => ?_, fun j hj c hc => ?_⟩
  · simp only [chartShiftAlong]
    congr 1
    exact Finset.sum_congr rfl fun l _ => by rw [(h l).1 b hb]
  · simp only [chartShiftAlong]
    congr 1
    exact Finset.sum_congr rfl fun l _ => by rw [(h l).2 j hj c hc]
end ComparedMixedDeriv
theorem comparedMixedDerivStatement_holds (hMix : localMixedDerivStatement) :
    comparedMixedDerivStatement := by
  classical
  open ComparedMixedDeriv in
  intro F F' E _ _ _ S S' R R' Y Y' B B' Ck Ck' Cm Dk U U' Φ Φ' del G Gb r₀ k c c' X T T' hdel hG hGb hCk hCk' hCm hDk
    hΦ hΦ' hcmp hX hB hB' h0 h0' hu hmu hu' hmu' hdec hdec' hgU hgA hturn m e hm
  obtain ⟨-, hexp, -⟩ := hMix F E S R Y B Ck Dk U Φ del r₀ k c X T hdel hCk hDk hΦ hX hB h0 hu hmu hdec
  obtain ⟨-, hexp', -⟩ := hMix F' E S' R' Y' B' Ck' Dk U' Φ' del r₀ k c' X T' hdel hCk' hDk hΦ' hX hB' h0' hu' hmu' hdec'
  obtain ⟨A, hA, hE⟩ := hexp m e hm
  obtain ⟨A', hA', hE'⟩ := hexp' m e hm
  rw [hE, hE', ← Finset.sum_sub_distrib]
  unfold comparisonConstant
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun cP _ => ?_)
  rw [localIteratedDeriv_congr hΦ.congr_of_agree _ (hA cP),
    localIteratedDeriv_congr hΦ'.congr_of_agree _ (hA' cP)]
  set M : ℝ := Real.exp (del * r₀) with hMdef
  have hM1 : 1 ≤ M := Real.one_le_exp (by positivity)
  have hlen : 1 ≤ cP.length := cP.length_pos (by omega)
  have hte : ∀ l, ∀ b ∈ B, partSpread c X (partEmbedding e cP l) b.1 b.2 =
      partSpread c' X (partEmbedding e cP l) (cellAtSameOffset Y Y' b.1) b.2 := by
    intro l b hb
    simp only [partSpread, bondSpread]
    refine Finset.sum_congr rfl fun l' _ => ?_
    have h1 := hturn l' b hb
    have h2 : c l' = (b.1, b.2) ↔ c' l' = (cellAtSameOffset Y Y' b.1, b.2) := h1
    by_cases h3 : c l' = (b.1, b.2)
    · rw [if_pos h3, if_pos (h2.1 h3)]
    · rw [if_neg h3, if_neg (fun h4 => h3 (h2.2 h4))]
  refine (hcmp.deriv _ _ _ _ _ hlen hte).trans ?_
  have hslot : ∀ i, localDirectionSize S R B Y (mixedDerivativeChart T (partEmbedding e cP i))
      (partSpread c X (partEmbedding e cP i)) ≤ Dk (cP.partSize i) + M := by
    intro i
    have hp : 1 ≤ cP.partSize i := cP.partSize_pos i
    have h1 := hdec _ (partEmbedding e cP i) hp
    have h2 : Real.exp (-del * bondListDistance Y (c ∘ partEmbedding e cP i)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by
        have : (0 : ℝ) ≤ bondListDistance Y (c ∘ partEmbedding e cP i) := by positivity
        nlinarith)
    have h3 := mul_le_mul_of_nonneg_left h2 (hDk (cP.partSize i))
    unfold localDirectionSize
    exact add_le_add (by linarith) (topVariationNorm_partSpread_le B c X hX hM1 hp _)
  have hK : ∀ i, 0 ≤ Dk (cP.partSize i) + M := fun i => add_nonneg (hDk _) (by linarith)
  have hg0 : 0 ≤ offsetChartGapNorm S R Y Y Y' U U' := offsetChartGapNorm_nonneg _ _ _ _ _ _ _
  have p1 : offsetChartGapNorm S R Y Y Y' U U' *
        ∏ l, localDirectionSize S R B Y (mixedDerivativeChart T (partEmbedding e cP l))
          (partSpread c X (partEmbedding e cP l)) ≤ G * ∏ i, (Dk (cP.partSize i) + M) :=
    mul_le_mul hgU (Finset.prod_le_prod (fun i _ => localDirectionSize_nonneg _ _ _ _ _ _) fun i _ => hslot i)
      (Finset.prod_nonneg fun i _ => localDirectionSize_nonneg _ _ _ _ _ _) hG
  have hslot2 : ∀ i, localDirectionSize S R B Y (mixedDerivativeChart T (partEmbedding e cP i))
        (partSpread c X (partEmbedding e cP i)) +
      offsetChartGapNorm S R Y Y Y' (mixedDerivativeChart T (partEmbedding e cP i))
        (mixedDerivativeChart T' (partEmbedding e cP i)) ≤
      Dk (cP.partSize i) + M + Gb := fun i =>
    add_le_add (hslot i) ((hgA _ _ (cP.partSize_pos i)).trans hGb)
  have hnn : ∀ i, 0 ≤ localDirectionSize S R B Y (mixedDerivativeChart T (partEmbedding e cP i))
        (partSpread c X (partEmbedding e cP i)) +
      offsetChartGapNorm S R Y Y Y' (mixedDerivativeChart T (partEmbedding e cP i))
        (mixedDerivativeChart T' (partEmbedding e cP i)) :=
    fun i => add_nonneg (localDirectionSize_nonneg _ _ _ _ _ _) (offsetChartGapNorm_nonneg _ _ _ _ _ _ _)
  have p2 : ∑ l, offsetChartGapNorm S R Y Y Y' (mixedDerivativeChart T (partEmbedding e cP l))
        (mixedDerivativeChart T' (partEmbedding e cP l)) *
        ∏ l' ∈ Finset.univ.erase l,
          (localDirectionSize S R B Y (mixedDerivativeChart T (partEmbedding e cP l'))
            (partSpread c X (partEmbedding e cP l')) +
          offsetChartGapNorm S R Y Y Y' (mixedDerivativeChart T (partEmbedding e cP l'))
            (mixedDerivativeChart T' (partEmbedding e cP l'))) ≤
      ∑ l, G * ∏ i ∈ Finset.univ.erase l, (Dk (cP.partSize i) + M + Gb) := by
    refine Finset.sum_le_sum fun l _ => ?_
    exact mul_le_mul (hgA _ _ (cP.partSize_pos l))
      (Finset.prod_le_prod (fun i _ => hnn i) fun i _ => hslot2 i)
      (Finset.prod_nonneg fun i _ => hnn i) hG
  have e3 : Cm cP.length * (∏ i, (Dk (cP.partSize i) + M) +
        ∑ l, ∏ i ∈ Finset.univ.erase l, (Dk (cP.partSize i) + M + Gb)) * G =
      Cm cP.length * (G * ∏ i, (Dk (cP.partSize i) + M) +
        ∑ l, G * ∏ i ∈ Finset.univ.erase l, (Dk (cP.partSize i) + M + Gb)) := by
    rw [← Finset.mul_sum]
    ring
  rw [e3]
  exact mul_le_mul_of_nonneg_left (add_le_add p1 p2) (hCm _)
end YangMills.Construction.BlockAverages
end
