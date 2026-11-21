import YangMills.Construction.ColdChainAtEveryLevel.SeminormsOfCoordinates
import YangMills.Construction.HoleBesideASecondHole.TermsOfAChainAtACell
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open YangMills.Construction.BlockAverages YangMills.Construction.CellTerms
namespace LocalNorms
variable {F : BlockFrame}
theorem localNormSq_le_of_mul_weight_le (S B : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F)
    (w w' : F.SiteWeights) (κ : ℝ)
    (hκ : 0 ≤ κ) (hw : ∀ j (x : F.Site j), 0 ≤ w j x)
    (h : ∀ j (x : F.Site j), enclosingCell x ∈ B → κ * w j x ≤ w' j x) :
    κ ^ 2 * localNormSq S B R U w ≤ localNormSq S B R U w' := by
  classical
  have hfour : ∀ (j : ℕ) (x : F.Site j) (t : ℝ), 0 ≤ t → enclosingCell x ∈ B →
      (κ ^ 2) ^ 2 * (w j x * t) ^ 4 ≤ (w' j x * t) ^ 4 := by
    intro j x t ht hx
    have e : (κ ^ 2) ^ 2 * (w j x * t) ^ 4 = (κ * w j x * t) ^ 4 := by ring
    rw [e]
    exact pow_le_pow_left₀ (mul_nonneg (mul_nonneg hκ (hw j x)) ht)
      (mul_le_mul_of_nonneg_right (h j x hx) ht) 4
  have htwo : ∀ (j : ℕ) (x : F.Site j) (t : ℝ), 0 ≤ t → enclosingCell x ∈ B →
      κ ^ 2 * (w j x * t) ^ 2 ≤ (w' j x * t) ^ 2 := by
    intro j x t ht hx
    have e : κ ^ 2 * (w j x * t) ^ 2 = (κ * w j x * t) ^ 2 := by ring
    rw [e]
    exact pow_le_pow_left₀ (mul_nonneg (mul_nonneg hκ (hw j x)) ht)
      (mul_le_mul_of_nonneg_right (h j x hx) ht) 2
  unfold localNormSq
  rw [mul_add, mul_add]
  refine add_le_add (add_le_add ?_ ?_) ?_
  · have e : κ ^ 2 * Real.sqrt (∑ b ∈ bondsOver S B 0, (w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4) =
        Real.sqrt ((κ ^ 2) ^ 2 * ∑ b ∈ bondsOver S B 0, (w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    rw [e]
    refine Real.sqrt_le_sqrt ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun b hb => hfour 0 b.1 _ (norm_nonneg _) (Finset.mem_filter.1 hb).2
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun p hp => htwo 0 p.1 _ (norm_nonneg _) (Finset.mem_filter.1 hp).2
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun c hc => htwo (j + 1) c.1 _ (norm_nonneg _) (Finset.mem_filter.1 hc).2
theorem localNormSq_nonneg (S B : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (w : F.SiteWeights) :
    0 ≤ localNormSq S B R U w := by apply _root_.YangMills.Construction.CoordinateSeminorms.localNormSq_nonneg <;> assumption
theorem decayWeights_zero_zero_apply (δ : ℝ) (y : F.Cell) (j : ℕ) (x : F.Site j) :
    decayWeights F δ 0 0 y j x = Real.exp (-δ * cellSupDist (enclosingCell x) y) := by
  simp [decayWeights]
theorem unweightedLocalNorm_le_exp_mul_supWeightedNorm (δ : ℝ) (hδ : 0 < δ) (S : Finset F.Cell)
    (R : F.FieldChain) (U : ChainChart F)
    (z : F.Cell) (hz : z ∈ S) : unweightedLocalNorm S R U z ≤ Real.exp (3 * δ) * supWeightedNorm S δ R U := by
  classical
  set e := Real.exp (-(3 * δ)) with he
  have he0 : 0 < e := Real.exp_pos _
  have hw0 : ∀ (y : F.Cell) j (x : F.Site j), 0 ≤ decayWeights F δ 0 0 y j x := fun y j x => by
    rw [decayWeights_zero_zero_apply]
    exact (Real.exp_pos _).le
  have hw1 : ∀ (y : F.Cell) j (x : F.Site j), decayWeights F δ 0 0 y j x ≤ 1 := fun y j x => by
    rw [decayWeights_zero_zero_apply]
    refine Real.exp_le_one_iff.2 ?_
    have : (0 : ℝ) ≤ cellSupDist (enclosingCell x) y := by positivity
    nlinarith
  have hbdd : BddAbove (Set.range fun y₀ : F.Cell => weightedNorm S R U (decayWeights F δ 0 0 y₀)) := by
    refine ⟨Real.sqrt (∑ y ∈ S, localNorm S R U (fun _ _ => 1) y ^ 2), ?_⟩
    rintro _ ⟨y₀, rfl⟩
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun y _ => ?_)
    unfold localNorm
    rw [Real.sq_sqrt (localNormSq_nonneg _ _ _ _ _), Real.sq_sqrt (localNormSq_nonneg _ _ _ _ _)]
    have := localNormSq_le_of_mul_weight_le S (cellBall S y 3) R U (decayWeights F δ 0 0 y₀) (fun _ _ => 1) 1
      (by norm_num) (hw0 y₀) (fun j x _ => by simpa using hw1 y₀ j x)
    simpa using this
  have h1 : weightedNorm S R U (decayWeights F δ 0 0 z) ≤ supWeightedNorm S δ R U := le_ciSup hbdd z
  have h2 : localNorm S R U (decayWeights F δ 0 0 z) z ≤ weightedNorm S R U (decayWeights F δ 0 0 z) := by
    unfold weightedNorm
    refine Real.le_sqrt_of_sq_le ?_
    exact Finset.single_le_sum (f := fun y => localNorm S R U (decayWeights F δ 0 0 z) y ^ 2)
      (fun _ _ => sq_nonneg _) hz
  have h3 : e ^ 2 * localNormSq S (cellBall S z 3) R U (fun _ _ => 1) ≤
      localNormSq S (cellBall S z 3) R U (decayWeights F δ 0 0 z) := by
    refine localNormSq_le_of_mul_weight_le S _ R U _ _ e he0.le (fun _ _ => by norm_num) fun j x hx => ?_
    rw [decayWeights_zero_zero_apply, mul_one, he]
    refine Real.exp_le_exp.2 ?_
    have hd : cellSupDist z (enclosingCell x) ≤ 3 := (Finset.mem_filter.1 hx).2
    have hd' : (cellSupDist (enclosingCell x) z : ℝ) ≤ 3 := by
      rw [YangMills.Construction.BlockLines.cellSupDist_comm]
      exact_mod_cast hd
    nlinarith
  have h4 : e * unweightedLocalNorm S R U z ≤ localNorm S R U (decayWeights F δ 0 0 z) z := by
    unfold unweightedLocalNorm localNorm
    have e1 : e * Real.sqrt (localNormSq S (cellBall S z 3) R U fun _ _ => 1) =
        Real.sqrt (e ^ 2 * localNormSq S (cellBall S z 3) R U fun _ _ => 1) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq he0.le]
    rw [e1]
    exact Real.sqrt_le_sqrt h3
  have h5 : e * unweightedLocalNorm S R U z ≤ supWeightedNorm S δ R U := h4.trans (h2.trans h1)
  have h6 : Real.exp (3 * δ) * e = 1 := by
    rw [he, ← Real.exp_add]
    simp
  calc unweightedLocalNorm S R U z = Real.exp (3 * δ) * (e * unweightedLocalNorm S R U z) := by
        rw [← mul_assoc, h6, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left h5 (Real.exp_pos _).le
theorem unweightedLocalNorm_parts_le (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (z : F.Cell) :
    ∑ b ∈ bondsOver S (cellBall S z 3) 0, ‖U.fine b.1 b.2‖ ^ 4 ≤ unweightedLocalNorm S R U z ^ 4 ∧
    ∑ p ∈ plaquettesOver S (cellBall S z 3) 0, ‖linearizedCurl (R 0) U.fine p‖ ^ 2 ≤
      unweightedLocalNorm S R U z ^ 2 ∧
    ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1), ‖U.coarse j c.1 c.2‖ ^ 2 ≤
      unweightedLocalNorm S R U z ^ 2 := by
  have hsq : unweightedLocalNorm S R U z ^ 2 = localNormSq S (cellBall S z 3) R U fun _ _ => 1 := by
    unfold unweightedLocalNorm localNorm
    exact Real.sq_sqrt (localNormSq_nonneg _ _ _ _ _)
  have h1 : 0 ≤ ∑ b ∈ bondsOver S (cellBall S z 3) 0, ‖U.fine b.1 b.2‖ ^ 4 :=
    Finset.sum_nonneg fun _ _ => by positivity
  have h2 : 0 ≤ ∑ p ∈ plaquettesOver S (cellBall S z 3) 0, ‖linearizedCurl (R 0) U.fine p‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  have h3 : 0 ≤ ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
      ‖U.coarse j c.1 c.2‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  have e : localNormSq S (cellBall S z 3) R U (fun _ _ => 1) =
      Real.sqrt (∑ b ∈ bondsOver S (cellBall S z 3) 0, ‖U.fine b.1 b.2‖ ^ 4) +
        ∑ p ∈ plaquettesOver S (cellBall S z 3) 0, ‖linearizedCurl (R 0) U.fine p‖ ^ 2 +
        ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
          ‖U.coarse j c.1 c.2‖ ^ 2 := by
    simp [localNormSq]
  have hs := Real.sqrt_nonneg (∑ b ∈ bondsOver S (cellBall S z 3) 0, ‖U.fine b.1 b.2‖ ^ 4)
  refine ⟨?_, by rw [hsq, e]; linarith, by rw [hsq, e]; linarith⟩
  have h4 : Real.sqrt (∑ b ∈ bondsOver S (cellBall S z 3) 0, ‖U.fine b.1 b.2‖ ^ 4) ≤
      unweightedLocalNorm S R U z ^ 2 := by
    rw [hsq, e]
    linarith
  have h5 := Real.sq_sqrt h1
  calc _ = Real.sqrt (∑ b ∈ bondsOver S (cellBall S z 3) 0, ‖U.fine b.1 b.2‖ ^ 4) ^ 2 := h5.symm
    _ ≤ (unweightedLocalNorm S R U z ^ 2) ^ 2 := pow_le_pow_left₀ hs h4 2
    _ = _ := by ring
end LocalNorms
end YangMills.Construction
end
