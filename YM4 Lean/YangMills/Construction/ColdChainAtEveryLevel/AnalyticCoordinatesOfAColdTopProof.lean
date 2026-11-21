import YangMills.Construction.ClusterExpansionOfAStep.TreesOfABlock
import YangMills.Construction.ColdChainAtEveryLevel.AnalyticCoordinatesOfAColdTop
import YangMills.Construction.ColdChainAtEveryLevel.AnalyticSharesOfAColdTopProof
import YangMills.Construction.ColdChainAtEveryLevel.BoundsOfASplitCriticalPointProof
import YangMills.Construction.ColdChainAtEveryLevel.ChartCoordinatesOfACriticalChain
import YangMills.Construction.ColdChainAtEveryLevel.ChartsOfAgreeingPairs
import YangMills.Construction.ColdChainAtEveryLevel.SeminormsOfCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction.BlockAverages
namespace AnalyticChart
open LocalPartition
variable {F : BlockFrame} {S : Finset F.Cell}
section Sizes
theorem adjointAction_add (g : UnitQuaternion) (x y : ℍ[ℝ]) :
    adjointAction g (x + y) = adjointAction g x + adjointAction g y := by apply _root_.YangMills.Construction.BlockAverages.adjointAction_add <;> assumption
theorem linearizedCurl_chartAdd (R : F.GaugeField 0) (A B : ChainChart F) (p : F.Site 0 × Fin 4 × Fin 4) :
    linearizedCurl R (chartSum A B).fine p = linearizedCurl R A.fine p + linearizedCurl R B.fine p := by
  simp only [linearizedCurl, chartSum, chartMove, one_smul, Submodule.coe_add, adjointAction_add]
  abel
theorem sq_add_le_two_mul (x y : ℝ) : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
  nlinarith [sq_nonneg (x - y)]
theorem pow_four_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : (x + y) ^ 4 ≤ 8 * (x ^ 4 + y ^ 4) := by apply _root_.YangMills.Construction.BlockAverages.SplitCriticalPointBounds.add_pow_four_le <;> assumption
theorem sqrt_add_le_add_sqrt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by apply _root_.YangMills.Construction.CoordinateSeminorms.sqrt_add_le_add_sqrt <;> assumption
theorem norm_add_sq_le (x y : ℍ[ℝ]) : ‖x + y‖ ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) :=
  (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le x y) 2).trans (sq_add_le_two_mul _ _)
theorem localNormSq_chartAdd_le (R : F.FieldChain) (B : Finset F.Cell) (A A' : ChainChart F) :
    localNormSq S B R (chartSum A A') (oneSiteWeights F) ≤
      3 * (localNormSq S B R A (oneSiteWeights F) + localNormSq S B R A' (oneSiteWeights F)) := by
  unfold localNormSq
  have w1 : ∀ {j : ℕ} (x : F.Site j), oneSiteWeights F j x = 1 := fun _ => rfl
  simp only [w1, one_mul]
  have f1 : ∑ b ∈ bondsOver S B 0, ‖(chartSum A A').fine b.1 b.2‖ ^ 4 ≤
      8 * (∑ b ∈ bondsOver S B 0, ‖A.fine b.1 b.2‖ ^ 4 + ∑ b ∈ bondsOver S B 0, ‖A'.fine b.1 b.2‖ ^ 4) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum fun b _ => ?_
    have h1 : ‖(chartSum A A').fine b.1 b.2‖ ≤ ‖A.fine b.1 b.2‖ + ‖A'.fine b.1 b.2‖ := by
      simpa [chartSum, chartMove] using norm_add_le (A.fine b.1 b.2) (A'.fine b.1 b.2)
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 4).trans (pow_four_add_le (norm_nonneg _) (norm_nonneg _))
  have f2 : ∑ p ∈ plaquettesOver S B 0, ‖linearizedCurl (R 0) (chartSum A A').fine p‖ ^ 2 ≤
      2 * (∑ p ∈ plaquettesOver S B 0, ‖linearizedCurl (R 0) A.fine p‖ ^ 2 +
        ∑ p ∈ plaquettesOver S B 0, ‖linearizedCurl (R 0) A'.fine p‖ ^ 2) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum fun p _ => ?_
    rw [linearizedCurl_chartAdd]
    exact norm_add_sq_le _ _
  have f3 : ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S B (j + 1),
        ‖(chartSum A A').coarse j c.1 c.2‖ ^ 2 ≤
      2 * (∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S B (j + 1), ‖A.coarse j c.1 c.2‖ ^ 2 +
        ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S B (j + 1), ‖A'.coarse j c.1 c.2‖ ^ 2) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum fun c _ => ?_
    have h1 : ‖(chartSum A A').coarse j c.1 c.2‖ ≤ ‖A.coarse j c.1 c.2‖ + ‖A'.coarse j c.1 c.2‖ := by
      simpa [chartSum, chartMove] using norm_add_le (A.coarse j c.1 c.2) (A'.coarse j c.1 c.2)
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans (sq_add_le_two_mul _ _)
  set a1 := ∑ b ∈ bondsOver S B 0, ‖A.fine b.1 b.2‖ ^ 4
  set a2 := ∑ b ∈ bondsOver S B 0, ‖A'.fine b.1 b.2‖ ^ 4
  have ha1 : 0 ≤ a1 := Finset.sum_nonneg fun _ _ => by positivity
  have ha2 : 0 ≤ a2 := Finset.sum_nonneg fun _ _ => by positivity
  have hs : Real.sqrt (∑ b ∈ bondsOver S B 0, ‖(chartSum A A').fine b.1 b.2‖ ^ 4) ≤
      3 * (Real.sqrt a1 + Real.sqrt a2) := by
    refine (Real.sqrt_le_sqrt f1).trans ?_
    have h1 : Real.sqrt (8 * (a1 + a2)) ≤ 3 * Real.sqrt (a1 + a2) := by
      rw [Real.sqrt_le_left (by positivity)]
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      nlinarith
    have h2 : Real.sqrt (a1 + a2) ≤ Real.sqrt a1 + Real.sqrt a2 := sqrt_add_le_add_sqrt ha1 ha2
    linarith
  have n1 : 0 ≤ ∑ p ∈ plaquettesOver S B 0, ‖linearizedCurl (R 0) A.fine p‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  have n2 : 0 ≤ ∑ p ∈ plaquettesOver S B 0, ‖linearizedCurl (R 0) A'.fine p‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  have n3 : 0 ≤ ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S B (j + 1), ‖A.coarse j c.1 c.2‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  have n4 : 0 ≤ ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S B (j + 1), ‖A'.coarse j c.1 c.2‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  linarith
theorem localNorm_congr {R : F.FieldChain} {A A' : ChainChart F} (z : F.Cell) (h : ChartEqOnBonds S A A') :
    localNorm S R A (oneSiteWeights F) z = localNorm S R A' (oneSiteWeights F) z := by
  classical
  have f1 : ∑ b ∈ bondsOver S (cellBall S z 3) 0, (oneSiteWeights F 0 b.1 * ‖A.fine b.1 b.2‖) ^ 4 =
      ∑ b ∈ bondsOver S (cellBall S z 3) 0, (oneSiteWeights F 0 b.1 * ‖A'.fine b.1 b.2‖) ^ 4 := by
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [h.1 b (Finset.mem_filter.1 hb).1]
  have f2 : ∑ p ∈ plaquettesOver S (cellBall S z 3) 0,
        (oneSiteWeights F 0 p.1 * ‖linearizedCurl (R 0) A.fine p‖) ^ 2 =
      ∑ p ∈ plaquettesOver S (cellBall S z 3) 0,
        (oneSiteWeights F 0 p.1 * ‖linearizedCurl (R 0) A'.fine p‖) ^ 2 := by
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' := (Finset.mem_filter.1 hp).1
    obtain ⟨x, μ, ν⟩ := p
    have hc := (Finset.mem_filter.1 hp').2.2
    have c0 : x ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
    have c1 : x + unitStep 0 μ ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
    have c2 : x + unitStep 0 ν ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
    have c3 : x + unitStep 0 μ + unitStep 0 ν ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
    have mk : ∀ (y : F.Site 0) (i : Fin 4), y ∈ sitesOfCells S 0 → y + unitStep 0 i ∈ sitesOfCells S 0 →
        (y, i) ∈ innerBonds S 0 := fun y i h1 h2 => by
      simp [innerBonds, h1, h2]
    have e1 := h.1 _ (mk x μ c0 c1)
    have e2 := h.1 _ (mk (x + unitStep 0 μ) ν c1 c3)
    have e3 := h.1 _ (mk (x + unitStep 0 ν) μ c2 (by rw [add_right_comm]; exact c3))
    have e4 := h.1 _ (mk x ν c0 c2)
    simp only [] at e1 e2 e3 e4
    simp only [linearizedCurl, e1, e2, e3, e4]
  have f3 : ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
        (oneSiteWeights F (j + 1) c.1 * ‖A.coarse j c.1 c.2‖) ^ 2 =
      ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
        (oneSiteWeights F (j + 1) c.1 * ‖A'.coarse j c.1 c.2‖) ^ 2 := by
    refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun c hc => ?_
    have hj' : j + 1 < F.top := by
      have := Finset.mem_range.1 hj
      simp only [BlockFrame.top] at this ⊢
      omega
    rw [h.2 j hj' c (Finset.mem_filter.1 hc).1]
  unfold localNorm localNormSq
  rw [f1, f2, f3]
theorem cellSupDist_comm (y z : F.Cell) : cellSupDist y z = cellSupDist z y := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_comm <;> assumption
theorem decayWeights_apply (rate : ℝ) (p : F.Site 0) (z : F.Cell) {j : ℕ} (x : F.Site j) :
    decayWeights F rate 0 p z j x = Real.exp (-rate * cellSupDist (enclosingCell x) z) := by
  simp [decayWeights]
theorem exp_le_decayWeights (rate : ℝ) (hrate : 0 ≤ rate) (p : F.Site 0) (z : F.Cell) {j : ℕ} (x : F.Site j)
    (hx : cellSupDist z (enclosingCell x) ≤ 3) : Real.exp (-(3 * rate)) ≤ decayWeights F rate 0 p z j x := by
  rw [decayWeights_apply, cellSupDist_comm]
  refine Real.exp_le_exp.2 ?_
  have : (cellSupDist z (enclosingCell x) : ℝ) ≤ 3 := by exact_mod_cast hx
  nlinarith
theorem localNormSq_le_decay (R : F.FieldChain) (rate : ℝ) (hrate : 0 ≤ rate) (p : F.Site 0) (z : F.Cell)
    (A : ChainChart F) :
    localNormSq S (cellBall S z 3) R A (oneSiteWeights F) ≤
      Real.exp (6 * rate) * localNormSq S (cellBall S z 3) R A (decayWeights F rate 0 p z) := by
  unfold localNormSq
  have w1 : ∀ {j : ℕ} (x : F.Site j), oneSiteWeights F j x = 1 := fun _ => rfl
  simp only [w1, one_mul]
  have hq : Real.exp (6 * rate) * Real.exp (-(3 * rate)) ^ 2 = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    simp only [Nat.cast_ofNat]
    have : 6 * rate + 2 * -(3 * rate) = 0 := by ring
    rw [this, Real.exp_zero]
  have hq2 : Real.exp (12 * rate) * Real.exp (-(3 * rate)) ^ 4 = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    simp only [Nat.cast_ofNat]
    have : 12 * rate + 4 * -(3 * rate) = 0 := by ring
    rw [this, Real.exp_zero]
  have mem : ∀ {j : ℕ} {b : F.Site j × Fin 4}, b ∈ bondsOver S (cellBall S z 3) j →
      cellSupDist z (enclosingCell b.1) ≤ 3 := by
    intro j b hb
    exact (Finset.mem_filter.1 (Finset.mem_filter.1 hb).2).2
  have memp : ∀ {p' : F.Site 0 × Fin 4 × Fin 4}, p' ∈ plaquettesOver S (cellBall S z 3) 0 →
      cellSupDist z (enclosingCell p'.1) ≤ 3 := by
    intro p' hb
    exact (Finset.mem_filter.1 (Finset.mem_filter.1 hb).2).2
  have f1 : ∑ b ∈ bondsOver S (cellBall S z 3) 0, ‖A.fine b.1 b.2‖ ^ 4 ≤
      Real.exp (12 * rate) * ∑ b ∈ bondsOver S (cellBall S z 3) 0,
        (decayWeights F rate 0 p z 0 b.1 * ‖A.fine b.1 b.2‖) ^ 4 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b hb => ?_
    have h1 := exp_le_decayWeights rate hrate p z b.1 (mem hb)
    have h2 : (Real.exp (-(3 * rate)) * ‖A.fine b.1 b.2‖) ^ 4 ≤
        (decayWeights F rate 0 p z 0 b.1 * ‖A.fine b.1 b.2‖) ^ 4 :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)) 4
    calc ‖A.fine b.1 b.2‖ ^ 4 = Real.exp (12 * rate) * (Real.exp (-(3 * rate)) * ‖A.fine b.1 b.2‖) ^ 4 := by
          rw [mul_pow, ← mul_assoc, hq2, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
  have f2 : ∑ q ∈ plaquettesOver S (cellBall S z 3) 0, ‖linearizedCurl (R 0) A.fine q‖ ^ 2 ≤
      Real.exp (6 * rate) * ∑ q ∈ plaquettesOver S (cellBall S z 3) 0,
        (decayWeights F rate 0 p z 0 q.1 * ‖linearizedCurl (R 0) A.fine q‖) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun q hq' => ?_
    have h1 := exp_le_decayWeights rate hrate p z q.1 (memp hq')
    have h2 : (Real.exp (-(3 * rate)) * ‖linearizedCurl (R 0) A.fine q‖) ^ 2 ≤
        (decayWeights F rate 0 p z 0 q.1 * ‖linearizedCurl (R 0) A.fine q‖) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)) 2
    calc ‖linearizedCurl (R 0) A.fine q‖ ^ 2 =
          Real.exp (6 * rate) * (Real.exp (-(3 * rate)) * ‖linearizedCurl (R 0) A.fine q‖) ^ 2 := by
          rw [mul_pow, ← mul_assoc, hq, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
  have f3 : ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1), ‖A.coarse j c.1 c.2‖ ^ 2 ≤
      Real.exp (6 * rate) * ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
        (decayWeights F rate 0 p z (j + 1) c.1 * ‖A.coarse j c.1 c.2‖) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun c hc => ?_
    have h1 := exp_le_decayWeights rate hrate p z c.1 (mem hc)
    have h2 : (Real.exp (-(3 * rate)) * ‖A.coarse j c.1 c.2‖) ^ 2 ≤
        (decayWeights F rate 0 p z (j + 1) c.1 * ‖A.coarse j c.1 c.2‖) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)) 2
    calc ‖A.coarse j c.1 c.2‖ ^ 2 = Real.exp (6 * rate) * (Real.exp (-(3 * rate)) * ‖A.coarse j c.1 c.2‖) ^ 2 := by
          rw [mul_pow, ← mul_assoc, hq, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
  have hs1 : Real.sqrt (∑ b ∈ bondsOver S (cellBall S z 3) 0, ‖A.fine b.1 b.2‖ ^ 4) ≤
      Real.exp (6 * rate) * Real.sqrt (∑ b ∈ bondsOver S (cellBall S z 3) 0,
        (decayWeights F rate 0 p z 0 b.1 * ‖A.fine b.1 b.2‖) ^ 4) := by
    refine (Real.sqrt_le_sqrt f1).trans ?_
    have e : Real.exp (12 * rate) = Real.exp (6 * rate) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq (Real.exp_pos _).le]
  rw [mul_add, mul_add]
  linarith
theorem localNorm_le_of_split (R : F.FieldChain) (rate : ℝ) (hrate : 0 ≤ rate) (p : F.Site 0) {z : F.Cell}
    (hz : z ∈ S) {U A B : ChainChart F} {x y : ℝ} (hs : ChartEqOnBonds S U (chartSum A B))
    (hA : weightedNorm S R A (decayWeights F rate 0 p z) ≤ x)
    (hB : weightedNorm S R B (decayWeights F rate 0 p z) ≤ y) :
    localNorm S R U (oneSiteWeights F) z ≤ 3 * Real.exp (3 * rate) * (x + y) := by
  have near : ∀ C : ChainChart F, localNorm S R C (decayWeights F rate 0 p z) z ≤
      weightedNorm S R C (decayWeights F rate 0 p z) := by
    intro C
    unfold weightedNorm
    refine Real.le_sqrt_of_sq_le ?_
    exact Finset.single_le_sum (f := fun z' => localNorm S R C (decayWeights F rate 0 p z) z' ^ 2)
      (fun _ _ => sq_nonneg _) hz
  have unit : ∀ C : ChainChart F, Real.sqrt (localNormSq S (cellBall S z 3) R C (oneSiteWeights F)) ≤
      Real.exp (3 * rate) * weightedNorm S R C (decayWeights F rate 0 p z) := by
    intro C
    refine (Real.sqrt_le_sqrt (localNormSq_le_decay R rate hrate p z C)).trans ?_
    have e : Real.exp (6 * rate) = Real.exp (3 * rate) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_left (near C) (Real.exp_pos _).le
  rw [localNorm_congr z hs]
  unfold localNorm
  have hsq := localNormSq_chartAdd_le (S := S) R (cellBall S z 3) A B
  have a0 : 0 ≤ localNormSq S (cellBall S z 3) R A (oneSiteWeights F) := by
    unfold localNormSq
    positivity
  have b0 : 0 ≤ localNormSq S (cellBall S z 3) R B (oneSiteWeights F) := by
    unfold localNormSq
    positivity
  have h1 : Real.sqrt (localNormSq S (cellBall S z 3) R (chartSum A B) (oneSiteWeights F)) ≤
      3 * (Real.sqrt (localNormSq S (cellBall S z 3) R A (oneSiteWeights F)) +
        Real.sqrt (localNormSq S (cellBall S z 3) R B (oneSiteWeights F))) := by
    refine (Real.sqrt_le_sqrt hsq).trans ?_
    have h2 := sqrt_add_le_add_sqrt a0 b0
    have h3 : Real.sqrt (3 * (localNormSq S (cellBall S z 3) R A (oneSiteWeights F) +
        localNormSq S (cellBall S z 3) R B (oneSiteWeights F))) ≤
        3 * Real.sqrt (localNormSq S (cellBall S z 3) R A (oneSiteWeights F) +
          localNormSq S (cellBall S z 3) R B (oneSiteWeights F)) := by
      rw [Real.sqrt_le_left (by positivity)]
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      nlinarith
    linarith
  have hE : 0 < Real.exp (3 * rate) := Real.exp_pos _
  have u1 := unit A
  have u2 := unit B
  have v1 := mul_le_mul_of_nonneg_left hA hE.le
  have v2 := mul_le_mul_of_nonneg_left hB hE.le
  nlinarith
end Sizes
section Near
theorem rotatedField_zero (V : F.GaugeField F.top) :
    rotatedField (fun _ _ => (0 : imaginaryQuaternions)) V = V := by apply _root_.YangMills.Construction.BlockAverages.AnalyticCellShares.rotatedField_zero <;> assumption
theorem bondSpread_zero {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) :
    bondSpread c X (0 : Fin k → ℝ) = fun _ _ => 0 := by apply _root_.YangMills.Construction.BlockAverages.AnalyticCellShares.bondSpread_zero <;> assumption
theorem continuous_bondSpread {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (y : F.Site F.top) (i : Fin 4) :
    Continuous fun ζ : Fin k → ℝ => bondSpread c X ζ y i := by
  unfold bondSpread
  refine continuous_finset_sum _ fun l _ => ?_
  split_ifs
  · exact (continuous_apply l).smul continuous_const
  · exact continuous_const
theorem continuous_rotatedField_apply {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (V : F.GaugeField F.top) (y : F.Site F.top) (i : Fin 4) :
    Continuous fun ζ : Fin k → ℝ => ((rotatedField (bondSpread c X ζ) V y i : UnitQuaternion) : ℍ[ℝ]) := by
  show Continuous fun ζ : Fin k → ℝ =>
    NormedSpace.exp ((bondSpread c X ζ y i : imaginaryQuaternions) : ℍ[ℝ]) * ((V y i : UnitQuaternion) : ℍ[ℝ])
  refine Continuous.mul ?_ continuous_const
  have hexp : Continuous fun q : ℍ[ℝ] => NormedSpace.exp q :=
    continuous_iff_continuousAt.2 fun q => (NormedSpace.exp_analytic (𝕂 := ℝ) q).continuousAt
  exact hexp.comp (continuous_subtype_val.comp (continuous_bondSpread c X y i))
theorem continuous_pathHolonomy {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (V : F.GaugeField F.top) (l : List PathStep) (x : F.Site F.top) :
    Continuous fun ζ : Fin k → ℝ => ((pathHolonomy (rotatedField (bondSpread c X ζ) V) x l : UnitQuaternion) : ℍ[ℝ]) := by
  induction l generalizing x with
  | nil => exact continuous_const
  | cons st t ih =>
    simp only [pathHolonomy, Submonoid.coe_mul]
    refine Continuous.mul ?_ (ih _)
    obtain ⟨i, b⟩ := st
    cases b
    · simp only [linkValue, Bool.false_eq_true, if_false]
      have : Continuous fun ζ : Fin k → ℝ =>
          star ((rotatedField (bondSpread c X ζ) V (x - unitStep F.top i) i : UnitQuaternion) : ℍ[ℝ]) :=
        continuous_star.comp (continuous_rotatedField_apply c X V _ i)
      exact this
    · simp only [linkValue, if_true]
      exact continuous_rotatedField_apply c X V x i
theorem eventually_isCold_rotated {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    {V : F.GaugeField F.top} {s : ℝ} (hcold : IsCold S F.top s V) :
    ∀ᶠ ζ : Fin k → ℝ in 𝓝 0, IsCold S F.top s (rotatedField (bondSpread c X ζ) V) := by
  have : ∀ᶠ ζ : Fin k → ℝ in 𝓝 0, ∀ p ∈ innerPlaquettes S F.top,
      plaquetteDefect (rotatedField (bondSpread c X ζ) V) p < s := by
    refine (Finset.eventually_all _).2 fun p hp => ?_
    have hc : Continuous fun ζ : Fin k → ℝ => plaquetteDefect (rotatedField (bondSpread c X ζ) V) p := by
      unfold plaquetteDefect plaquetteHolonomy
      exact ((continuous_pathHolonomy c X V _ _).sub continuous_const).norm
    have h0 : plaquetteDefect (rotatedField (bondSpread c X (0 : Fin k → ℝ)) V) p < s := by
      rw [bondSpread_zero, rotatedField_zero]
      exact hcold p hp
    exact hc.continuousAt.eventually_lt continuousAt_const h0
  exact this
theorem norm_bondSpread_le {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) {X : Fin k → imaginaryQuaternions}
    (hX : AreUnitVectors X) (ζ : Fin k → ℝ) (y : F.Site F.top) (i : Fin 4) :
    ‖bondSpread c X ζ y i‖ ≤ ∑ l, |ζ l| := by
  unfold bondSpread
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  split_ifs
  · rw [norm_smul, hX l, mul_one, Real.norm_eq_abs]
  · simp
theorem cellSupDist_self (z : F.Cell) : cellSupDist z z = 0 := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_self <;> assumption
theorem isBondAnalyticAt_of_unit {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (G : F.GaugeField F.top → E)
    (V : F.GaugeField F.top)
    (h : ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k →
      AreUnitVectors X → AnalyticAt ℝ (fun σ : Fin k → ℝ => G (rotatedField (bondSpread c X σ) V)) 0) :
    IsBondAnalyticAt G V := by apply _root_.YangMills.Construction.BlockAverages.AnalyticCellShares.isBondAnalyticAt_of_unit <;> assumption
end Near
section Box
variable {F' : BlockFrame} {S' : Finset F'.Cell} {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top}
  {Y : F.Cell} {Y' : F'.Cell} {r : ℕ}
theorem agreeOnBall_shift (hag : AgreeOnBall S V S' V' Y Y' r) {h : Fin 4 → ℤ} {r' : ℕ}
    (hr : ∀ i, |h i| + r' ≤ (r : ℤ)) :
    AgreeOnBall S V S' V' (Y + siteOfCoords F.top h) (Y' + siteOfCoords F'.top h) r' := by
  obtain ⟨hs, hs', hS, hV⟩ := hag
  have hrr : r' ≤ r := by
    have := hr 0
    have h0 := abs_nonneg (h 0)
    omega
  refine ⟨fun i => (hs i).imp_right fun h1 => by omega, fun i => (hs' i).imp_right fun h1 => by omega, ?_, ?_⟩
  · intro g hg
    rw [add_assoc, add_assoc, ← siteOfCoords_add, ← siteOfCoords_add]
    refine hS _ fun i => ?_
    have a1 := abs_add_le (h i) (g i)
    simp only [Pi.add_apply]
    linarith [hr i, hg i]
  · intro b hb
    rw [add_assoc, add_assoc, ← siteOfCoords_add, ← siteOfCoords_add]
    refine hV (h + b.1, b.2) ⟨fun i => ?_, fun i => ?_⟩
    · have a1 := abs_add_le (h i) (b.1 i)
      simp only [Pi.add_apply]
      linarith [hr i, hb.1 i]
    · have a1 := abs_add_le (h i) ((b.1 + Pi.single b.2 1 : Fin 4 → ℤ) i)
      have a2 := hb.2 i
      simp only [Pi.add_apply, add_assoc] at a1 a2 ⊢
      linarith [hr i]
theorem period_top (F : BlockFrame) (i : Fin 4) : F.period F.top i = F.extent i := by simp [BlockFrame.period]
theorem iteratedFDeriv_congr_of_eventuallyEq {A W : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f g : A → W} {x : A} (h : f =ᶠ[𝓝 x] g) (n : ℕ) : iteratedFDeriv ℝ n f x = iteratedFDeriv ℝ n g x := by
  rw [← iteratedFDerivWithin_univ, ← iteratedFDerivWithin_univ]
  exact Filter.EventuallyEq.iteratedFDerivWithin_eq (by simpa using h) h.self_of_nhds n
theorem valMinAbs_depth (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (i : Fin 4) {A : ℤ}
    (hA : 2 * |A| < (F.blockSide : ℤ)) :
    ((A : ZMod (F.period F.depth i))).valMinAbs = A := by
  apply valMinAbs_intCast_of_small
  have hp : F.period F.depth i = F.extent i * F.blockSide := by
    simp [BlockFrame.period, BlockFrame.top]
  rcases hamb with h | h
  · left
    rw [hp, h i, zero_mul]
  · right
    rw [hp]
    push_cast
    have h1 : (64 : ℤ) ≤ F.extent i := by exact_mod_cast h i
    nlinarith
theorem two_abs_lt_of_mem_centredCube {L : ℕ} (hodd : Odd L) {h : Fin 4 → ℤ} (hh : h ∈ centredCube L) (i : Fin 4) :
    2 * |h i| < (L : ℤ) := by apply _root_.YangMills.Construction.BlockTrees.two_mul_abs_lt_of_mem_centredCube <;> assumption
theorem cellSupDist_topBondsAt_le (b : F.Site F.depth × Fin 4) {z : F.Cell} (hz : enclosingCell b.1 = z) :
    ∀ x ∈ topBondsAt b, cellSupDist z x.1 ≤ 1 := by
  intro x hx
  unfold topBondsAt at hx
  split_ifs at hx
  · rw [Finset.mem_singleton.1 hx, hz, cellSupDist_self]
    omega
  · simp at hx
theorem valMinAbs_top_of_small (hs : ∀ i, F.extent i = 0 ∨ 2 * r + 2 < F.extent i) (i : Fin 4) {A : ℤ}
    (hA : |A| ≤ (r : ℤ) + 1) :
    ((A : ZMod (F.period F.top i))).valMinAbs = A := by apply _root_.YangMills.Construction.BlockAverages.AnalyticCellShares.valMinAbs_of_withinRadius <;> assumption
theorem siteOfCoords_injOn_ball (hs : ∀ i, F.extent i = 0 ∨ 2 * r + 2 < F.extent i) {a b : Fin 4 → ℤ}
    (ha : WithinRadius r a) (hb : WithinRadius r b)
    (h : siteOfCoords (F := F) F.top a = siteOfCoords F.top b) : a = b := by
  funext i
  have h1 := congrArg ZMod.valMinAbs (congrFun h i)
  simp only [siteOfCoords] at h1
  rwa [valMinAbs_top_of_small hs i (by linarith [ha i]), valMinAbs_top_of_small hs i (by linarith [hb i])] at h1
theorem abs_le_cellSupDist (hs : ∀ i, F.extent i = 0 ∨ 2 * r + 2 < F.extent i) {h : Fin 4 → ℤ}
    (hh : WithinRadius r h) (i : Fin 4) :
    |h i| ≤ (cellSupDist Y (Y + siteOfCoords F.top h) : ℤ) := by
  have h1 : ((Y i - (Y + siteOfCoords F.top h : F.Cell) i).valMinAbs).natAbs ≤
      cellSupDist Y (Y + siteOfCoords F.top h) :=
    Finset.le_sup (f := fun i => ((Y i - (Y + siteOfCoords F.top h : F.Cell) i).valMinAbs).natAbs)
      (Finset.mem_univ i)
  have e : Y i - (Y + siteOfCoords F.top h : F.Cell) i = ((-h i : ℤ) : ZMod (F.period F.top i)) := by
    simp [siteOfCoords]
  rw [e, valMinAbs_top_of_small hs i (by rw [abs_neg]; linarith [hh i])] at h1
  rw [Int.abs_eq_natAbs]
  have : (-h i).natAbs = (h i).natAbs := Int.natAbs_neg _
  rw [this] at h1
  exact_mod_cast h1
theorem cellSupDist_le_radius (hs : ∀ i, F.extent i = 0 ∨ 2 * r + 2 < F.extent i) {h : Fin 4 → ℤ}
    (hh : WithinRadius r h) :
    cellSupDist Y (Y + siteOfCoords F.top h) ≤ r := by
  refine Finset.sup_le fun i _ => ?_
  have e : Y i - (Y + siteOfCoords F.top h : F.Cell) i = ((-h i : ℤ) : ZMod (F.period F.top i)) := by
    simp [siteOfCoords]
  rw [e, valMinAbs_top_of_small hs i (by rw [abs_neg]; linarith [hh i]), Int.natAbs_neg]
  have := hh i
  rw [Int.abs_eq_natAbs] at this
  exact_mod_cast this
theorem le_abs_valMinAbs {n : ℕ} {A q : ℤ} (hq : q ≤ |A|) (hn : n = 0 ∨ q + |A| ≤ (n : ℤ)) :
    q ≤ |((A : ZMod n)).valMinAbs| := by apply _root_.YangMills.Construction.BlockAverages.AnalyticCellShares.le_abs_valMinAbs <;> assumption
theorem le_cellSupDist_of_not_bondWithinRadius (hs : ∀ i, F.extent i = 0 ∨ 2 * r + 2 < F.extent i)
    {h p : Fin 4 → ℤ} {r' q : ℕ}
    (hh : ∀ i, |h i| + r' ≤ (r : ℤ)) (hp : WithinRadius r p) (hq : 2 * q ≤ r') {i₀ : Fin 4}
    (hnot : ¬ BondWithinRadius q (p - h, i₀)) :
    q ≤ cellSupDist (Y + siteOfCoords F.top h) (Y + siteOfCoords F.top p) + 1 := by apply _root_.YangMills.Construction.BlockAverages.AnalyticCellShares.le_cellSupDist_of_not_bondWithinRadius <;> assumption
end Box
end AnalyticChart
set_option maxHeartbeats 2000000 in
theorem analyticChartCoords (hCrit : rotatedCriticalChainsStatement)
    (hRead : minimizerEqCriticalChainChartStatement) (hLoc : chartLocalityStatement)
    (hMix : localMixedDerivStatement) (hCmp : comparedMixedDerivStatement)
    (hAg : agreeingChartsComparedStatement) : analyticChartCoordsStatement := by
  classical
  open AnalyticChart LocalPartition in
  intro a ha
  haveI : FiniteDimensional ℝ imaginaryQuaternions := inferInstance
  haveI : CompleteSpace imaginaryQuaternions := FiniteDimensional.complete ℝ imaginaryQuaternions
  obtain ⟨θ, del, Ca, hθ, hθ8, hd, hd8, hCa, L₁, hC⟩ := hCrit a ha
  obtain ⟨L₂, hR⟩ := hRead a θ del Ca ha hθ hθ8 hd hd8 hCa
  obtain ⟨L₃, hL⟩ := hLoc
  obtain ⟨L₄, hA⟩ := hAg
  refine ⟨del / 4, by positivity, fun δ hδ hδ4 => ⟨max L₁ (max L₂ (max L₃ L₄)), fun L hLo hge ρ hρ hρ1 => ?_⟩⟩
  have g1 : L₁ ≤ L := le_of_max_le_left hge
  have g2 : L₂ ≤ L := le_of_max_le_left (le_of_max_le_right hge)
  have g3 : L₃ ≤ L := le_of_max_le_left (le_of_max_le_right (le_of_max_le_right hge))
  have g4 : L₄ ≤ L := le_of_max_le_right (le_of_max_le_right (le_of_max_le_right hge))
  obtain ⟨rL, r', sL, CL, Ck, hrL, hr'0, hr'rL, hsL, hCL, hCk, hcrit, hcomp⟩ := hC L hLo g1
  obtain ⟨σR, N0, hσR, hN0, hr⟩ := hR L hLo g2 CL ρ hCL hρ hρ1
  obtain ⟨c₁, Ck₁, hc₁, hCk₁, hloc⟩ := hL L hLo g3
  obtain ⟨c₂, r₀, Cm, hc₂, hCm, hagr⟩ := hA L hLo g4
  have hCk0 : ∀ m, 0 ≤ Ck m := fun m => (hCk m).le
  set M : ℝ := Real.exp (del * ((1 : ℕ) : ℝ)) with hM
  have hM0 : 0 ≤ M := (Real.exp_pos _).le
  set Rc : ℕ → ℝ := mixedDerivConstant Ck₁ Ck M with hRc
  have hRc0 : ∀ k, 0 ≤ Rc k := fun k =>
    Finset.sum_nonneg fun c _ => mul_nonneg (hCk₁ _) (Finset.prod_nonneg fun i _ => add_nonneg (hCk0 _) hM0)
  set cN : ℝ := min c₁ c₂ with hcN
  have hcN0 : 0 < cN := lt_min hc₁ hc₂
  set K0 : ℝ := 3 * Real.exp (3 * del) * (Ca + CL) with hK0
  have hK0pos : 0 < K0 := by positivity
  set σ : ℝ := min (min sL (σR / 2)) (min cN (min 1 (cN / K0))) with hσ
  have hσ0 : 0 < σ := lt_min (lt_min hsL (by positivity)) (lt_min hcN0 (lt_min one_pos (by positivity)))
  set R₁ : ℕ := max r₀ 108 with hR₁
  set E₁ : ℝ := Real.exp (del * ((R₁ : ℝ) + 2)) with hE₁
  have hE₁1 : 1 ≤ E₁ := Real.one_le_exp (by positivity)
  set Dc : ℕ → ℝ := fun k => comparisonConstant Cm Ck M (CL + ∑ m ∈ Finset.range (k + 1), Ck m) k *
    (CL + ∑ m ∈ Finset.range (k + 1), Ck m) with hDc
  have hDc0 : ∀ k, 0 ≤ Dc k := by
    intro k
    have hGb : 0 ≤ CL + ∑ m ∈ Finset.range (k + 1), Ck m :=
      add_nonneg hCL.le (Finset.sum_nonneg fun m _ => hCk0 m)
    refine mul_nonneg (Finset.sum_nonneg fun c _ => mul_nonneg (hCm _) ?_) hGb
    exact add_nonneg (Finset.prod_nonneg fun i _ => add_nonneg (hCk0 _) hM0)
      (Finset.sum_nonneg fun l _ => Finset.prod_nonneg fun i _ => add_nonneg (add_nonneg (hCk0 _) hM0) hGb)
  set N : ℕ → ℝ := fun k => 1 + 2 * Rc k * E₁ + Dc k + Cm 0 * CL + 2 * N0 * E₁ with hN
  have hNpos : ∀ k, 0 < N k := by
    intro k
    have h1 := hRc0 k
    have h2 := hDc0 k
    have h3 := hCm 0
    simp only [hN]
    positivity
  have hCmCL : 0 ≤ Cm 0 * CL := mul_nonneg (hCm 0) hCL.le
  have hN0E : 0 ≤ 2 * N0 * E₁ := by positivity
  have hRE : ∀ k, 0 ≤ 2 * Rc k * E₁ := fun k => mul_nonneg (mul_nonneg (by norm_num) (hRc0 k)) (by linarith)
  have nR2 : ∀ k, 2 * Rc k * E₁ ≤ N k := fun k => by
    have := hDc0 k
    show 2 * Rc k * E₁ ≤ 1 + 2 * Rc k * E₁ + Dc k + Cm 0 * CL + 2 * N0 * E₁
    linarith
  have nR1 : ∀ k, Rc k ≤ N k := fun k => by
    have h1 : Rc k * 1 ≤ Rc k * E₁ := mul_le_mul_of_nonneg_left hE₁1 (hRc0 k)
    have h2 := nR2 k
    have h3 := hRc0 k
    linarith
  have nD : ∀ k, Dc k ≤ N k := fun k => by
    have := hRE k
    show Dc k ≤ 1 + 2 * Rc k * E₁ + Dc k + Cm 0 * CL + 2 * N0 * E₁
    linarith
  have nC : Cm 0 * CL ≤ N 0 := by
    have := hRE 0
    have := hDc0 0
    show Cm 0 * CL ≤ 1 + 2 * Rc 0 * E₁ + Dc 0 + Cm 0 * CL + 2 * N0 * E₁
    linarith
  have nN : 2 * N0 * E₁ ≤ N 0 := by
    have := hRE 0
    have := hDc0 0
    show 2 * N0 * E₁ ≤ 1 + 2 * Rc 0 * E₁ + Dc 0 + Cm 0 * CL + 2 * N0 * E₁
    linarith
  have first : ∀ (F : BlockFrame) (S : Finset F.Cell) (V : F.GaugeField F.top) (s : ℝ) (U : ChainChart F) (k : ℕ)
      (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (T : (Fin k → ℝ) → ChainChart F)
      (b : F.Site F.depth × Fin 4), 1 ≤ k →
      IsLocalRepresentation S (referenceFieldChain S V) (enclosingCell b.1) (topBondsAt b) Ck₁ U
        (bondChartCoord (referenceFieldChain S V) V b) →
      IsRotatedChain a θ del Ca rL r' CL s Ck S V c X U T → AreUnitVectors X →
      (∀ᶠ ζ : Fin k → ℝ in 𝓝 0, minimizingBondCoordinate a ρ S b (rotatedField (bondSpread c X ζ) V) =
        bondChartCoord (referenceFieldChain S V) V b (T ζ) (bondSpread c X ζ)) →
      AnalyticAt ℝ (fun ζ : Fin k → ℝ => minimizingBondCoordinate a ρ S b (rotatedField (bondSpread c X ζ) V)) 0 ∧
      mixedBondDerivative (minimizingBondCoordinate a ρ S b) V c X =
        iteratedFDeriv ℝ k
          (fun ζ : Fin k → ℝ => bondChartCoord (referenceFieldChain S V) V b (T ζ) (bondSpread c X ζ)) 0
          (fun l => Pi.single l 1) ∧
      ‖mixedBondDerivative (minimizingBondCoordinate a ρ S b) V c X‖ ≤
        Rc k * Real.exp (-del * bondListDistance (enclosingCell b.1) c) := by
    intro F S V s U k c X T b hk hl hT hX hev
    have hB : ∀ x ∈ topBondsAt b, cellSupDist (enclosingCell b.1) x.1 ≤ 1 := by
      intro x hx
      unfold topBondsAt at hx
      split_ifs at hx
      · rw [Finset.mem_singleton.1 hx, cellSupDist_self]
        omega
      · simp at hx
    obtain ⟨an, -, bd⟩ := hMix F imaginaryQuaternions S (referenceFieldChain S V) (enclosingCell b.1) (topBondsAt b)
      Ck₁ Ck U (bondChartCoord (referenceFieldChain S V) V b) del 1 k c X T hd.le hCk₁ hCk0 hl hX hB
      hT.eq_at_zero hT.analyticAt_fine hT.analyticAt_coarse (fun m e hm => hT.decay m e _ hm)
    have heq : mixedBondDerivative (minimizingBondCoordinate a ρ S b) V c X =
        iteratedFDeriv ℝ k
          (fun ζ : Fin k → ℝ => bondChartCoord (referenceFieldChain S V) V b (T ζ) (bondSpread c X ζ)) 0
          (fun l => Pi.single l 1) := by
      unfold mixedBondDerivative
      rw [iteratedFDeriv_congr_of_eventuallyEq hev k]
    refine ⟨an.congr (Filter.EventuallyEq.symm hev), heq, ?_⟩
    rw [heq]
    exact bd k (Function.Embedding.refl _) hk
  have pair : ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
      IsOrthantRegular S m →
      ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ σ → IsCold S F.top s V →
      ∃ U : ChainChart F, IsSliceCriticalPoint a θ del Ca rL CL s S V U ∧
        (∀ z ∈ S, localNorm S (referenceFieldChain S V) U (oneSiteWeights F) z ≤ cN) ∧
        (∀ b ∈ chordBonds S, minimizingBondCoordinate a ρ S b V =
            bondChartCoord (referenceFieldChain S V) V b U (fun _ _ => 0) ∧
          ‖minimizingBondCoordinate a ρ S b V‖ ≤ N0 * s) ∧
        (∀ b, b ∉ chordBonds S → minimizingBondCoordinate a ρ S b V = 0) ∧
        ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k → AreUnitVectors X →
          ∃ T : (Fin k → ℝ) → ChainChart F, IsRotatedChain a θ del Ca rL r' CL s Ck S V c X U T ∧
            ∀ᶠ ζ : Fin k → ℝ in 𝓝 0,
              (∀ b ∈ chordBonds S, minimizingBondCoordinate a ρ S b (rotatedField (bondSpread c X ζ) V) =
                bondChartCoord (referenceFieldChain S V) V b (T ζ) (bondSpread c X ζ)) ∧
              ∀ b, b ∉ chordBonds S → minimizingBondCoordinate a ρ S b (rotatedField (bondSpread c X ζ) V) = 0 := by
    intro F m S hFL hamb hm hreg s V hs hsσ hcold
    have s1 : s ≤ sL := hsσ.trans ((min_le_left _ _).trans (min_le_left _ _))
    have s2 : s ≤ σR / 2 := hsσ.trans ((min_le_left _ _).trans (min_le_right _ _))
    have s3 : s ≤ cN := hsσ.trans ((min_le_right _ _).trans (min_le_left _ _))
    have s4 : s ≤ 1 := hsσ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have s5 : s ≤ cN / K0 := hsσ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    obtain ⟨U, hU, hB, hfam⟩ := hcrit F m S hFL hamb hm hreg s V hs s1 hcold
    refine ⟨U, hU, ?_, ?_, ?_, ?_⟩
    · intro z hz
      obtain ⟨Ul, Ur, hsame, hbd⟩ := hU.split
      obtain ⟨x1, x2⟩ := hbd 0 z 0 (Or.inr rfl)
      refine (localNorm_le_of_split _ del hd.le 0 hz hsame x1 x2).trans ?_
      have h1 : K0 * s ≤ cN := by
        rw [le_div_iff₀ hK0pos] at s5
        linarith
      have h2 : Ca * s + CL * s ^ 2 ≤ (Ca + CL) * s := by
        have hss : s ^ 2 ≤ s := by
          rw [sq]
          exact mul_le_of_le_one_left hs.le s4
        have : CL * s ^ 2 ≤ CL * s := mul_le_mul_of_nonneg_left hss hCL.le
        linarith
      have h3 : 3 * Real.exp (3 * del) * (Ca * s + CL * s ^ 2) ≤ 3 * Real.exp (3 * del) * ((Ca + CL) * s) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      have h4 : 3 * Real.exp (3 * del) * ((Ca + CL) * s) = K0 * s := by
        rw [hK0]
        ring
      linarith
    all_goals
      have hV0 : IsCriticalChainOverTop a θ del Ca CL s S V (rotatedField (fun _ _ => 0) V) U := by
        rw [rotatedField_zero]
        exact ⟨hU.critical, hU.split, hB.quartic, hB.curvature_and_misfits, hB.misfits_on_cells⟩
      have h0 := hr F m S hFL hamb hm hreg s V (fun _ _ => 0) hs (by linarith) hcold
        (fun _ _ => by simpa using hs.le) (by rw [rotatedField_zero]; exact hcold) U hV0
      rw [rotatedField_zero] at h0
    · exact h0.1
    · exact h0.2
    · intro k c X hk hX
      obtain ⟨T, hT⟩ := hfam k c X hk hX
      refine ⟨T, hT, ?_⟩
      have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have hk0 : (0 : ℝ) < k := by linarith
      set t : ℝ := min s (min (σR / 2) (r' / 2)) with ht
      have ht0 : 0 < t := lt_min hs (lt_min (by positivity) (by positivity))
      set σ' : ℝ := t / k with hσ'
      have hσ'0 : 0 < σ' := by positivity
      have hkσ : (k : ℝ) * σ' = t := by
        rw [hσ']
        field_simp
      have hlt : σ' < r' / k := by
        rw [hσ']
        refine div_lt_div_of_pos_right ?_ hk0
        have : t ≤ r' / 2 := (min_le_right _ _).trans (min_le_right _ _)
        linarith
      have ev1 : ∀ᶠ ζ : Fin k → ℝ in 𝓝 0, ∀ l, |ζ l| ≤ σ' := by
        have : Metric.ball (0 : Fin k → ℝ) σ' ∈ 𝓝 (0 : Fin k → ℝ) := Metric.ball_mem_nhds _ hσ'0
        filter_upwards [this] with ζ hζ l
        have h1 : ‖ζ‖ < σ' := by simpa using hζ
        exact (norm_le_pi_norm ζ l).trans h1.le
      filter_upwards [ev1, eventually_isCold_rotated c X hcold] with ζ hz hc
      have hcr := hT.critical ζ σ' hz hlt
      have hpos : 0 < s + k * σ' := by positivity
      have hle : s + k * σ' ≤ σR := by
        have : t ≤ σR / 2 := (min_le_right _ _).trans (min_le_left _ _)
        rw [hkσ]
        linarith
      have hnorm : ∀ y i, ‖bondSpread c X ζ y i‖ ≤ s + k * σ' := by
        intro y i
        refine (norm_bondSpread_le c hX ζ y i).trans ?_
        have h1 : ∑ l, |ζ l| ≤ ∑ _l : Fin k, σ' := Finset.sum_le_sum fun l _ => hz l
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
        linarith
      have hmono : ∀ {W : F.GaugeField F.top}, IsCold S F.top s W → IsCold S F.top (s + k * σ') W :=
        fun {W} h p hp => (h p hp).trans_le (by
          have : (0 : ℝ) ≤ k * σ' := by positivity
          linarith)
      have hres := hr F m S hFL hamb hm hreg (s + k * σ') V (bondSpread c X ζ) hpos hle (hmono hcold) hnorm
        (hmono hc) (T ζ) hcr
      exact ⟨fun b hb => (hres.1 b hb).1, hres.2⟩
  refine ⟨σ, N, hσ0, hNpos, ?_⟩
  intro F m S hFL hamb hm hreg s V hs hsσ hcold
  have hodd : Odd F.blockSide := hFL ▸ hLo
  have s1 : s ≤ sL := hsσ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have s3 : s ≤ cN := hsσ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have s4 : s ≤ 1 := hsσ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨U, hU, hnear, ord0, off0, fam⟩ := pair F m S hFL hamb hm hreg s V hs hsσ hcold
  have hlocal : ∀ b ∈ chordBonds S, IsLocalRepresentation S (referenceFieldChain S V) (enclosingCell b.1) (topBondsAt b)
      Ck₁ U (bondChartCoord (referenceFieldChain S V) V b) := fun b hb =>
    hloc F m S hFL hamb hm hreg s V hs (s3.trans (min_le_left _ _)) hcold U
      (fun z hz => (hnear z hz).trans (min_le_left _ _)) b hb
  have hδd : δ ≤ del := by linarith
  have hexp1 : ∀ x : ℝ, 0 ≤ x → Real.exp (-del * x) ≤ Real.exp (-δ * x) := fun x hx =>
    Real.exp_le_exp.2 (by
      have := mul_le_mul_of_nonneg_right hδd hx
      linarith)
  refine ⟨fun b hb => ⟨isBondAnalyticAt_of_unit _ _ fun k c X hk hX => ?_, fun k c X hk hX => ?_⟩, ?_⟩
  · obtain ⟨T, hT, hev⟩ := fam k c X hk hX
    exact (first F S V s U k c X T b hk (hlocal b hb) hT hX (hev.mono fun ζ h => h.1 b hb)).1
  · obtain ⟨T, hT, hev⟩ := fam k c X hk hX
    refine (first F S V s U k c X T b hk (hlocal b hb) hT hX (hev.mono fun ζ h => h.1 b hb)).2.2.trans ?_
    have h1 := hexp1 (bondListDistance (enclosingCell b.1) c) (by positivity)
    exact mul_le_mul (nR1 k) h1 (Real.exp_pos _).le (hNpos k).le
  intro F' S' V' Y Y' r hF'L ht hamb' hreg' hcold' hag
  have hodd' : Odd F'.blockSide := hF'L ▸ hLo
  obtain ⟨U', hU', hnear', ord0', off0', fam'⟩ := pair F' m S' hF'L hamb' hm hreg' s V' hs hsσ hcold'
  have hs1 := hag.1
  have hs2 := hag.2.1
  have hsm := hag.2.2.1
  intro h o i ho hb hbox hend
  set z : F.Cell := Y + siteOfCoords F.top h with hz
  set z' : F'.Cell := Y' + siteOfCoords F'.top h with hz'
  set d : ℕ := cellSupDist Y z with hdd
  have hdr : d ≤ r := cellSupDist_le_radius hs1 hbox
  set r' : ℕ := r - d with hr'
  have hhd : ∀ l, |h l| + r' ≤ (r : ℤ) := by
    intro l
    have h1 := abs_le_cellSupDist (Y := Y) hs1 hbox l
    have h2 : (r' : ℤ) = (r : ℤ) - d := by
      rw [hr']
      push_cast [hdr]
      ring
    rw [h2]
    have h3 : |h l| ≤ (d : ℤ) := h1
    omega
  have hag' := agreeOnBall_shift hag hhd
  have hcube : ∀ {G : BlockFrame}, G.blockSide = L → o ∈ centredCube G.blockSide := fun {G} hG => by
    rw [hG, ← hFL]
    exact ho
  have hcell : enclosingCell (fineBondAt Y h o i).1 = z := by
    refine enclosingCell_cellCentre_add hodd z o ?_
    have : F.top - F.depth = 1 := by simp [BlockFrame.top]
    rw [this, pow_one]
    exact ho
  have hcell' : enclosingCell (fineBondAt Y' h o i).1 = z' := by
    refine enclosingCell_cellCentre_add hodd' z' o ?_
    have : F'.top - F'.depth = 1 := by simp [BlockFrame.top]
    rw [this, pow_one]
    exact hcube hF'L
  rw [hcell]
  have hreal : (r : ℝ) - (d : ℝ) = (r' : ℝ) := by
    rw [hr']
    push_cast [hdr]
    ring
  rw [hreal]
  have hr'0 : (0 : ℝ) ≤ r' := by positivity
  set b := fineBondAt Y h o i with hbdef
  set b' := fineBondAt Y' h o i with hb'def
  have hbeq : (depthSiteAtSameOffset z z' b.1, b.2) = b' := by
    have e1 : b.1 - cellCentre F.depth z = siteOfCoords F.depth o := by
      simp [hbdef, fineBondAt, hz]
    have e2 : (fun l => ((b.1 - cellCentre F.depth z) l).valMinAbs) = o := by
      funext l
      rw [e1]
      exact valMinAbs_depth hamb hodd l (two_abs_lt_of_mem_centredCube hodd ho l)
    show (cellCentre F'.depth z' + siteOfCoords F'.depth (fun l => ((b.1 - cellCentre F.depth z) l).valMinAbs), b.2) = b'
    rw [e2]
    rfl
  have hlocal' : ∀ x ∈ chordBonds S', IsLocalRepresentation S' (referenceFieldChain S' V') (enclosingCell x.1)
      (topBondsAt x) Ck₁ U' (bondChartCoord (referenceFieldChain S' V') V' x) := fun x hx =>
    hloc F' m S' hF'L hamb' hm hreg' s V' hs (s3.trans (min_le_left _ _)) hcold' U'
      (fun y hy => (hnear' y hy).trans (min_le_left _ _)) x hx
  have hcoe : ∀ (x y : imaginaryQuaternions), ‖(x : ℍ[ℝ]) - (y : ℍ[ℝ])‖ ≤ ‖x‖ + ‖y‖ := fun x y => norm_sub_le _ _
  by_cases hbig : R₁ ≤ r'
  · have hr₀ : r₀ ≤ r' := (le_max_left _ _).trans hbig
    have h8 : 108 ≤ r' := (le_max_right _ _).trans hbig
    obtain ⟨hmem, hcmp'⟩ := hagr F F' m S S' hFL hF'L ht hamb hamb' hm hreg hreg' s V V' z z' r' hs
      (s3.trans (min_le_right _ _)) hcold hcold' hr₀ hag' U U' (fun y hy => (hnear y hy).trans (min_le_right _ _))
      (fun y hy => (hnear' y hy).trans (min_le_right _ _)) b hb hcell
    rw [hbeq] at hmem hcmp'
    obtain ⟨hd1, hd2⟩ := hcomp F F' m S S' hFL hF'L ht hamb hamb' hm hreg hreg' s V V' z z' r' hs s1 hcold hcold' h8
      hag' U U' hU hU'
    have hgap : offsetChartGapNorm S (referenceFieldChain S V) z z z' U U' ≤ CL * s * Real.exp (-del * r' / 4) :=
      hd1 z (by rw [cellSupDist_self]; omega)
    have hexp4 : Real.exp (-del * r' / 4) ≤ Real.exp (-δ * r') := Real.exp_le_exp.2 (by
      have := mul_le_mul_of_nonneg_right hδ4 hr'0
      linarith)
    have hexp4pos : 0 < Real.exp (-del * r' / 4) := Real.exp_pos _
    refine ⟨?_, fun k h' X hk hbx hX => ?_⟩
    · rw [(ord0 b hb).1, (ord0' b' hmem).1]
      have hv := hcmp'.value
      refine le_trans (le_of_eq ?_) (hv.trans ?_)
      · rfl
      · have h1 := mul_le_mul_of_nonneg_left hgap (hCm 0)
        have h2 : Cm 0 * CL ≤ N 0 := nC
        refine h1.trans ?_
        calc Cm 0 * (CL * s * Real.exp (-del * r' / 4)) = (Cm 0 * CL) * s * Real.exp (-del * r' / 4) := by ring
          _ ≤ N 0 * s * Real.exp (-δ * r') := by
            refine mul_le_mul (mul_le_mul_of_nonneg_right h2 hs.le) hexp4 hexp4pos.le ?_
            exact mul_nonneg (hNpos 0).le hs.le
    · obtain ⟨T, hT, hev⟩ := fam k (offsetBonds Y h') X hk hX
      obtain ⟨T', hT', hev'⟩ := fam' k (offsetBonds Y' h') X hk hX
      have f1 := first F S V s U k _ X T b hk (hlocal b hb) hT hX (hev.mono fun ζ hh => hh.1 b hb)
      have f2 := first F' S' V' s U' k _ X T' b' hk (hlocal' b' hmem) hT' hX (hev'.mono fun ζ hh => hh.1 b' hmem)
      by_cases hall : ∀ l, BondWithinRadius (r' / 2) ((h' l).1 - h, (h' l).2)
      · have e1 : offsetBonds z (fun l => ((h' l).1 - h, (h' l).2)) = offsetBonds Y h' := by
          funext l
          simp only [offsetBonds, hz]
          rw [add_assoc, ← siteOfCoords_add]
          simp
        have e1' : offsetBonds z' (fun l => ((h' l).1 - h, (h' l).2)) = offsetBonds Y' h' := by
          funext l
          simp only [offsetBonds, hz']
          rw [add_assoc, ← siteOfCoords_add]
          simp
        have hd3 := hd2 k _ X hk hall hX T T' (by rw [e1]; exact hT) (by rw [e1']; exact hT')
        set G : ℝ := (CL + ∑ m ∈ Finset.range (k + 1), Ck m) * Real.exp (-del * r' / 4) with hG
        have hsum0 : 0 ≤ ∑ m ∈ Finset.range (k + 1), Ck m := Finset.sum_nonneg fun m _ => hCk0 m
        have hG0 : 0 ≤ G := by positivity
        have hGGb : G ≤ CL + ∑ m ∈ Finset.range (k + 1), Ck m := by
          have h0 : 0 ≤ del * r' := by positivity
          have h1 : Real.exp (-del * r' / 4) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
          exact mul_le_of_le_one_right (by positivity) h1
        have hgU : offsetChartGapNorm S (referenceFieldChain S V) z z z' U U' ≤ G := by
          refine hgap.trans ?_
          refine mul_le_mul_of_nonneg_right ?_ hexp4pos.le
          have h5 : CL * s ≤ CL * 1 := mul_le_mul_of_nonneg_left s4 hCL.le
          linarith
        have hgA : ∀ (m' : ℕ) (e : Fin m' ↪ Fin k), 1 ≤ m' →
            offsetChartGapNorm S (referenceFieldChain S V) z z z' (mixedDerivativeChart T e)
              (mixedDerivativeChart T' e) ≤ G := by
          intro m' e hm'
          have hle : m' ≤ k := by simpa using Fintype.card_le_of_embedding e
          refine (hd3 m' e z hm' (by rw [cellSupDist_self]; omega)).trans ?_
          refine mul_le_mul_of_nonneg_right ?_ hexp4pos.le
          have := Finset.single_le_sum (f := Ck) (fun m _ => hCk0 m) (Finset.mem_range.2 (Nat.lt_succ_of_le hle))
          linarith
        have hturn : ∀ l, ∀ x ∈ topBondsAt b,
            offsetBonds Y h' l = x ↔ offsetBonds Y' h' l = (cellAtSameOffset z z' x.1, x.2) := by
          intro l x hx
          unfold topBondsAt at hx
          split_ifs at hx
          · have hxe := Finset.mem_singleton.1 hx
            have htop : cellAtSameOffset z z' z = z' := by
              have e0 : (fun l => ((z - z : F.Cell) l).valMinAbs) = (0 : Fin 4 → ℤ) := by
                funext l
                simp
              unfold cellAtSameOffset
              rw [e0, siteOfCoords_zero, add_zero]
            rw [hxe, hcell]
            simp only [htop, offsetBonds, Prod.mk.injEq]
            refine and_congr_left fun _ => ⟨fun e => ?_, fun e => ?_⟩
            · have := siteOfCoords_injOn_ball hs1 (hbx l).1 hbox (add_left_cancel e)
              rw [this]
            · have := siteOfCoords_injOn_ball hs2 (hbx l).1 hbox (add_left_cancel e)
              rw [this]
          · simp at hx
        have hfin := hCmp F F' imaginaryQuaternions S S' (referenceFieldChain S V) (referenceFieldChain S' V') z z'
          (topBondsAt b) (topBondsAt b')
          Ck₁ Ck₁ Cm Ck U U' (bondChartCoord (referenceFieldChain S V) V b)
          (bondChartCoord (referenceFieldChain S' V') V' b')
          del G (CL + ∑ m ∈ Finset.range (k + 1), Ck m) 1 k (offsetBonds Y h') (offsetBonds Y' h') X T T' hd.le hG0
          hGGb hCk₁ hCk₁ hCm hCk0
          (hcell ▸ hlocal b hb) (hcell' ▸ hlocal' b' hmem) hcmp' hX (cellSupDist_topBondsAt_le b hcell)
          (cellSupDist_topBondsAt_le b' hcell')
          hT.eq_at_zero hT'.eq_at_zero hT.analyticAt_fine hT.analyticAt_coarse hT'.analyticAt_fine
          hT'.analyticAt_coarse
          (fun m' e hm' => hT.decay m' e z hm') (fun m' e hm' => hT'.decay m' e z' hm') hgU hgA hturn k
          (Function.Embedding.refl _) hk
        rw [f1.2.1, f2.2.1]
        refine le_trans (le_of_eq ?_) (hfin.trans ?_)
        · rfl
        · have h2 : Dc k ≤ N k := nD k
          calc comparisonConstant Cm Ck (Real.exp (del * ((1 : ℕ) : ℝ))) (CL + ∑ m ∈ Finset.range (k + 1), Ck m) k
                  * G =
                Dc k * Real.exp (-del * r' / 4) := by
                simp only [hDc, hG, hM]
                ring
            _ ≤ N k * Real.exp (-δ * r') :=
                mul_le_mul h2 hexp4 hexp4pos.le (hNpos k).le
      · push Not at hall
        obtain ⟨l, hl⟩ := hall
        have hq : 2 * (r' / 2) ≤ r' := by omega
        have hf := le_cellSupDist_of_not_bondWithinRadius (Y := Y) hs1 hhd (hbx l).1 hq hl
        have hf' := le_cellSupDist_of_not_bondWithinRadius (Y := Y') hs2 hhd (hbx l).1 hq hl
        have far : ∀ t : ℕ, r' / 2 ≤ t + 1 →
            Rc k * Real.exp (-del * t) ≤ Rc k * E₁ * Real.exp (-δ * r') := by
          intro t ht'
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ (hRc0 k)
          rw [hE₁, ← Real.exp_add]
          refine Real.exp_le_exp.2 ?_
          have h1 : (r' : ℝ) ≤ 2 * t + 3 := by
            have : r' ≤ 2 * t + 3 := by omega
            exact_mod_cast this
          have h2 : (0 : ℝ) ≤ R₁ := by positivity
          have h3 : δ * r' ≤ del / 4 * r' := mul_le_mul_of_nonneg_right hδ4 hr'0
          have h4 : del * r' ≤ del * (2 * t + 3) := mul_le_mul_of_nonneg_left h1 hd.le
          have h5 : 0 ≤ del * R₁ := by positivity
          have h6 : 0 ≤ del * t := by positivity
          have h7 : 0 ≤ del * r' := by positivity
          linarith
        have l1 : cellSupDist z (offsetBonds Y h' l).1 ≤ bondListDistance z (offsetBonds Y h') :=
          Finset.le_sup (f := fun l' => cellSupDist z (offsetBonds Y h' l').1) (Finset.mem_univ l)
        have l2 : cellSupDist z' (offsetBonds Y' h' l).1 ≤ bondListDistance z' (offsetBonds Y' h') :=
          Finset.le_sup (f := fun l' => cellSupDist z' (offsetBonds Y' h' l').1) (Finset.mem_univ l)
        have d1 := f1.2.2
        have d2 := f2.2.2
        rw [hcell] at d1
        rw [hcell'] at d2
        have b1 := d1.trans (far _ (hf.trans (by simpa [offsetBonds] using Nat.add_le_add_right l1 1)))
        have b2 := d2.trans (far _ (hf'.trans (by simpa [offsetBonds] using Nat.add_le_add_right l2 1)))
        refine (hcoe _ _).trans ?_
        have h2 : 2 * Rc k * E₁ ≤ N k := nR2 k
        have hep := (Real.exp_pos (-δ * r')).le
        have h3 := mul_le_mul_of_nonneg_right h2 hep
        have e2 : ‖mixedBondDerivative (minimizingBondCoordinate a ρ S b) V (offsetBonds Y h') X‖ +
            ‖mixedBondDerivative (minimizingBondCoordinate a ρ S' b') V' (offsetBonds Y' h') X‖ ≤
              2 * Rc k * E₁ * Real.exp (-δ * r') := by
          linarith
        exact e2.trans h3
  · have hEr : 1 ≤ E₁ * Real.exp (-δ * r') := by
      rw [hE₁, ← Real.exp_add]
      refine Real.one_le_exp ?_
      have h1 : (r' : ℝ) ≤ R₁ := by
        have : r' ≤ R₁ := by omega
        exact_mod_cast this
      have h2 : (0 : ℝ) ≤ R₁ := by positivity
      have h3 : δ * r' ≤ del * R₁ := mul_le_mul hδd h1 hr'0 hd.le
      have h4 : 0 ≤ del * R₁ := by positivity
      have h5 : del * ((R₁ : ℝ) + 2) = del * R₁ + 2 * del := by ring
      linarith
    have hw : ‖minimizingBondCoordinate a ρ S b V‖ ≤ N0 * s := (ord0 b hb).2
    have hw' : ‖minimizingBondCoordinate a ρ S' b' V'‖ ≤ N0 * s := by
      by_cases hm' : b' ∈ chordBonds S'
      · exact (ord0' b' hm').2
      · rw [off0' b' hm', norm_zero]
        positivity
    refine ⟨?_, fun k h' X hk hbx hX => ?_⟩
    · refine (hcoe _ _).trans ?_
      have h2 : 2 * N0 * E₁ ≤ N 0 := nN
      have hex : 2 * N0 * s ≤ N 0 * s * Real.exp (-δ * r') := by
        have h3 : 2 * N0 * s * 1 ≤ 2 * N0 * s * (E₁ * Real.exp (-δ * r')) :=
          mul_le_mul_of_nonneg_left hEr (by positivity)
        have h4 : (2 * N0 * E₁) * s * Real.exp (-δ * r') ≤ N 0 * s * Real.exp (-δ * r') :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 hs.le) (Real.exp_pos _).le
        have e5 : 2 * N0 * s * (E₁ * Real.exp (-δ * r')) = (2 * N0 * E₁) * s * Real.exp (-δ * r') := by ring
        linarith
      linarith
    · obtain ⟨T, hT, hev⟩ := fam k (offsetBonds Y h') X hk hX
      obtain ⟨T', hT', hev'⟩ := fam' k (offsetBonds Y' h') X hk hX
      have hexp1' : ∀ t : ℝ, 0 ≤ t → Rc k * Real.exp (-del * t) ≤ Rc k := fun t ht' => by
        have h0 : 0 ≤ del * t := mul_nonneg hd.le ht'
        have : Real.exp (-del * t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
        exact mul_le_of_le_one_right (hRc0 k) this
      have d1 : ‖mixedBondDerivative (minimizingBondCoordinate a ρ S b) V (offsetBonds Y h') X‖ ≤ Rc k :=
        ((first F S V s U k _ X T b hk (hlocal b hb) hT hX (hev.mono fun ζ hh => hh.1 b hb)).2.2).trans
          (hexp1' _ (by positivity))
      have d2 : ‖mixedBondDerivative (minimizingBondCoordinate a ρ S' b') V' (offsetBonds Y' h') X‖ ≤ Rc k := by
        by_cases hm' : b' ∈ chordBonds S'
        · exact ((first F' S' V' s U' k _ X T' b' hk (hlocal' b' hm') hT' hX
            (hev'.mono fun ζ hh => hh.1 b' hm')).2.2).trans (hexp1' _ (by positivity))
        · have h0 : (fun σ' : Fin k → ℝ =>
              minimizingBondCoordinate a ρ S' b' (rotatedField (bondSpread (offsetBonds Y' h') X σ') V')) =ᶠ[𝓝 0]
              fun _ => (0 : imaginaryQuaternions) := hev'.mono fun ζ hh => hh.2 b' hm'
          unfold mixedBondDerivative
          rw [iteratedFDeriv_congr_of_eventuallyEq h0 k]
          have : iteratedFDeriv ℝ k (fun _ : Fin k → ℝ => (0 : imaginaryQuaternions)) 0 = 0 := by
            rw [iteratedFDeriv_const_of_ne (by omega)]
            rfl
          rw [this]
          simpa using hRc0 k
      refine (hcoe _ _).trans ?_
      have h2 : 2 * Rc k * E₁ ≤ N k := nR2 k
      have hRk := hRc0 k
      have h3 : 2 * Rc k * 1 ≤ 2 * Rc k * (E₁ * Real.exp (-δ * r')) :=
        mul_le_mul_of_nonneg_left hEr (by positivity)
      have h4 := mul_le_mul_of_nonneg_right h2 (Real.exp_pos (-δ * r')).le
      have e5 : 2 * Rc k * (E₁ * Real.exp (-δ * r')) = 2 * Rc k * E₁ * Real.exp (-δ * r') := by ring
      linarith
end YangMills.Construction.BlockAverages
end
