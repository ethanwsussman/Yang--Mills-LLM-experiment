import YangMills.Construction.ColdChainAtEveryLevel.LinesOfTheBlocksOfABond
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockWeights
open BlockAverages BlockLines LatticePaths
variable {F : BlockFrame}
def shiftedRadius (F : BlockFrame) (p : F.Site 0) (j : ℕ) (x : F.Site j) : ℝ :=
  min ((F.blockSide : ℝ) ^ F.top) ((baseDistance x p : ℝ) + 4 * (F.blockSide : ℝ) ^ j)
def shiftedWeight (F : BlockFrame) (θ : ℝ) (p : F.Site 0) : F.SiteWeights :=
  fun j x => (shiftedRadius F p j x / (F.blockSide : ℝ) ^ F.top) ^ (-θ)
open Classical in
def cellsNearPoint (S : Finset F.Cell) (p : F.Site 0) : Finset F.Cell :=
  S.filter fun z => cellSupDist z (enclosingCell p) ≤ 2
theorem natAbs_valMinAbs_intCast_le {m : ℕ} (A : ℤ) : ((A : ZMod m).valMinAbs).natAbs ≤ A.natAbs := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact le_of_eq (by simp [ZMod.valMinAbs]; rfl)
  · have : NeZero m := ⟨hm.ne'⟩
    exact ZMod.natAbs_min_of_le_div_two m _ A (by simp) (ZMod.natAbs_valMinAbs_le _)
theorem natAbs_valMinAbs_add_le_add {m : ℕ} (a b : ZMod m) :
    ((a + b).valMinAbs).natAbs ≤ (a.valMinAbs).natAbs + (b.valMinAbs).natAbs :=
  (ZMod.natAbs_valMinAbs_add_le a b).trans (Int.natAbs_add_le _ _)
theorem baseDistance_add_le {j : ℕ} (hj : j ≤ F.top) (x : F.Site j) (v : Fin 4 → ℤ) (p : F.Site 0) (B : ℕ)
    (hv : ∀ i, (v i).natAbs ≤ B) :
    baseDistance (x + siteOfCoords j v) p ≤ baseDistance x p + F.blockSide ^ j * B := by
  unfold baseDistance
  refine Finset.sup_le fun i _ => ?_
  rw [baseSite_add j hj x v]
  have e : ((baseSite x + siteOfCoords 0 (fun i => (F.blockSide : ℤ) ^ j * v i) - p : F.Site 0)) i =
      ((baseSite x - p : F.Site 0)) i + (siteOfCoords (F := F) 0 (fun i => (F.blockSide : ℤ) ^ j * v i)) i := by
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  rw [e]
  refine (natAbs_valMinAbs_add_le_add _ _).trans (Nat.add_le_add ?_ ?_)
  · exact Finset.le_sup (f := fun i => (((baseSite x - p : F.Site 0) i).valMinAbs).natAbs) (Finset.mem_univ i)
  · refine (natAbs_valMinAbs_intCast_le _).trans ?_
    rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
    exact Nat.mul_le_mul_left _ (hv i)
theorem baseDistance_refineSite {j : ℕ} (hj : j + 1 ≤ F.top) (y : F.Site (j + 1)) (p : F.Site 0) :
    baseDistance (refineSite y) p = baseDistance y p := by
  unfold baseDistance
  rw [baseSite_refineSite j hj]
theorem shiftedRadius_pos (hL : 0 < F.blockSide) (p : F.Site 0) (j : ℕ) (x : F.Site j) :
    0 < shiftedRadius F p j x := by
  exact lt_min (by positivity) (by positivity)
theorem shiftedRadius_le_cellSide (p : F.Site 0) (j : ℕ) (x : F.Site j) :
    shiftedRadius F p j x ≤ (F.blockSide : ℝ) ^ F.top :=
  min_le_left _ _
theorem rpow_neg_le_rpow_neg {a b θ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hθ : 0 ≤ θ) : b ^ (-θ) ≤ a ^ (-θ) :=
  Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith) (Set.mem_Ioi.2 ha)
    (Set.mem_Ioi.2 (lt_of_lt_of_le ha hab)) hab
theorem one_le_shiftedWeight (hL : 0 < F.blockSide) {θ : ℝ} (hθ : 0 ≤ θ) (p : F.Site 0) (j : ℕ) (x : F.Site j) :
    1 ≤ shiftedWeight F θ p j x := by
  have hN : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by positivity
  refine Real.one_le_rpow_of_pos_of_le_one_of_nonpos (div_pos (shiftedRadius_pos hL p j x) hN) ?_ (by linarith)
  rw [div_le_one hN]
  exact shiftedRadius_le_cellSide p j x
theorem shiftedWeight_succ_le (hL : 2 ≤ F.blockSide) {θ : ℝ} (hθ : 0 ≤ θ) (p : F.Site 0) {j : ℕ} (hj : j < F.top)
    (y : F.Site (j + 1)) (a : Fin 4 → ℤ) (ha : ∀ i, (a i).natAbs ≤ 2 * F.blockSide) :
    shiftedWeight F θ p (j + 1) y ≤ shiftedWeight F θ p j (refineSite y + siteOfCoords j a) := by
  have hL0 : 0 < F.blockSide := by omega
  have hLr : (2 : ℝ) ≤ F.blockSide := by exact_mod_cast hL
  have hN : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by positivity
  have hd := baseDistance_add_le (F := F) (j := j) (by omega) (refineSite y) a p (2 * F.blockSide) ha
  rw [baseDistance_refineSite (by omega)] at hd
  have hd' : (baseDistance (refineSite y + siteOfCoords j a) p : ℝ) ≤
      (baseDistance y p : ℝ) + (F.blockSide : ℝ) ^ j * (2 * F.blockSide) := by
    exact_mod_cast hd
  have hr : shiftedRadius F p j (refineSite y + siteOfCoords j a) ≤ shiftedRadius F p (j + 1) y := by
    refine min_le_min_left _ ?_
    have hp : (0 : ℝ) < (F.blockSide : ℝ) ^ j := by positivity
    have e : (F.blockSide : ℝ) ^ (j + 1) = (F.blockSide : ℝ) ^ j * F.blockSide := pow_succ _ _
    rw [e]
    nlinarith
  exact rpow_neg_le_rpow_neg (div_pos (shiftedRadius_pos hL0 p j _) hN) (div_le_div_of_nonneg_right hr hN.le) hθ
theorem rpow_le_shiftedWeight (hL : 0 < F.blockSide) {θ : ℝ} (hθ : 0 ≤ θ) (p : F.Site 0) {j : ℕ} (x : F.Site j)
    {r : ℝ} (hr : (baseDistance x p : ℝ) + 4 * (F.blockSide : ℝ) ^ j ≤ r) :
    (r / (F.blockSide : ℝ) ^ F.top) ^ (-θ) ≤ shiftedWeight F θ p j x := by
  have hN : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by positivity
  exact rpow_neg_le_rpow_neg (div_pos (shiftedRadius_pos hL p j x) hN)
    (div_le_div_of_nonneg_right ((min_le_right _ _).trans hr) hN.le) hθ
theorem shiftedWeight_le_exp_mul_decayWeights (hL : 0 < F.blockSide) {θ : ℝ} (hθ : 0 ≤ θ) (δ : ℝ) (p : F.Site 0)
    (y₀ : F.Cell) (j : ℕ) (x : F.Site j) : shiftedWeight F θ p j x ≤
      Real.exp (δ * cellSupDist (enclosingCell x) y₀) * decayWeights F δ θ p y₀ j x := by
  have hN : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by positivity
  have hp : (0 : ℝ) < (F.blockSide : ℝ) ^ j := by positivity
  have hlr : 0 < scaleRadius F j p x := by
    unfold scaleRadius
    exact lt_min hN (lt_of_lt_of_le hp (le_max_left _ _))
  have hle : scaleRadius F j p x ≤ shiftedRadius F p j x := by
    unfold scaleRadius shiftedRadius
    refine min_le_min_left _ (max_le ?_ ?_)
    · have : (0 : ℝ) ≤ (baseDistance x p : ℝ) := by positivity
      linarith
    · linarith
  have h1 : shiftedWeight F θ p j x ≤ (scaleRadius F j p x / (F.blockSide : ℝ) ^ F.top) ^ (-θ) :=
    rpow_neg_le_rpow_neg (div_pos hlr hN) (div_le_div_of_nonneg_right hle hN.le) hθ
  unfold decayWeights
  rw [← mul_assoc, ← Real.exp_add]
  have : δ * (cellSupDist (enclosingCell x) y₀ : ℝ) + -δ * (cellSupDist (enclosingCell x) y₀ : ℝ) = 0 := by ring
  rw [this, Real.exp_zero, one_mul]
  exact h1
theorem card_cellsNearPoint_le (S : Finset F.Cell) (p : F.Site 0) : (cellsNearPoint S p).card ≤ 625 := by
  classical
  have hc : (centredCube 5).card = 625 := by
    rw [card_centredCube (by decide : Odd 5)]
    norm_num
  rw [← hc]
  set z := enclosingCell (F := F) p with hz
  apply Finset.card_le_card_of_injOn (fun y i => ((z - y : F.Cell) i).valMinAbs)
  · intro y hy
    have hy' : cellSupDist y z ≤ 2 := (Finset.mem_filter.1 (Finset.mem_coe.1 hy)).2
    rw [cellSupDist_comm] at hy'
    refine Finset.mem_coe.2 ((mem_centredCube_iff _ _).2 fun i => ?_)
    have h1 : (((z - y : F.Cell) i).valMinAbs).natAbs ≤ cellSupDist z y :=
      Finset.le_sup (f := fun i => (((z - y : F.Cell) i).valMinAbs).natAbs) (Finset.mem_univ i)
    norm_num
    change -2 ≤ ((z - y : F.Cell) i).valMinAbs ∧ ((z - y : F.Cell) i).valMinAbs ≤ 2
    omega
  · intro y _ y' _ e
    funext i
    have h1 := congrFun e i
    have h2 := ZMod.injective_valMinAbs h1
    have h3 : (z - y : F.Cell) i = (z - y' : F.Cell) i := h2
    simpa using h3
theorem localNorm_le_weightedNorm (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (w : F.SiteWeights)
    {z : F.Cell} (hz : z ∈ S) : localNorm S R U w z ≤ weightedNorm S R U w := by
  unfold weightedNorm
  refine Real.le_sqrt_of_sq_le ?_
  exact Finset.single_le_sum (f := fun z => localNorm S R U w z ^ 2) (fun _ _ => by positivity) hz
theorem localNorm_parts_le (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (w : F.SiteWeights)
    (z : F.Cell) {β : ℝ} (hβ : 0 ≤ β) (hN : localNorm S R U w z ≤ β) :
    ∑ b ∈ bondsOver S (cellBall S z 3) 0, (w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4 ≤ β ^ 4 ∧
      ∑ q ∈ plaquettesOver S (cellBall S z 3) 0, (w 0 q.1 * ‖linearizedCurl (R 0) U.fine q‖) ^ 2 ≤ β ^ 2 ∧
      ∀ j, j + 1 < F.top → ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
        (w (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 ≤ β ^ 2 := by
  have hN' := (Real.sqrt_le_iff.1 hN).2
  unfold localNormSq at hN'
  have hA : 0 ≤ Real.sqrt (∑ b ∈ bondsOver S (cellBall S z 3) 0, (w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4) :=
    Real.sqrt_nonneg _
  have hB : 0 ≤ ∑ q ∈ plaquettesOver S (cellBall S z 3) 0, (w 0 q.1 * ‖linearizedCurl (R 0) U.fine q‖) ^ 2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hC : 0 ≤ ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
      (w (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  refine ⟨?_, by linarith, ?_⟩
  · have h1 : Real.sqrt (∑ b ∈ bondsOver S (cellBall S z 3) 0, (w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4) ≤ β ^ 2 := by
      linarith
    refine ((Real.sqrt_le_iff.1 h1).2).trans (le_of_eq ?_)
    ring
  · intro j hj
    have hmem : j ∈ Finset.range (F.top - 1) := Finset.mem_range.2 (by omega)
    have h2 := Finset.single_le_sum (f := fun j => ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
      (w (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) hmem
    exact h2.trans (by linarith)
theorem sum_innerBonds_le_sum_cells (hL : Odd F.blockSide) {D S : Finset F.Cell} (hD : D ⊆ S) (j : ℕ)
    (g : F.Site j × Fin 4 → ℝ) (hg : ∀ b, 0 ≤ g b) :
    ∑ b ∈ innerBonds D j, g b ≤ ∑ z ∈ D, ∑ b ∈ bondsOver S {z} j, g b := by
  classical
  have hmaps : ∀ b ∈ innerBonds D j, enclosingCell b.1 ∈ D := fun b hb => by
    simp only [innerBonds, Finset.mem_filter, Finset.mem_product] at hb
    exact enclosingCell_mem hL hb.1.1
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_le_sum fun z _ => ?_
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun b hb => ?_) fun b _ _ => hg b
  obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hb
  exact Finset.mem_filter.2 ⟨innerBonds_mono hD j h1, by simp [h2]⟩
theorem singleton_subset_cellBall {S : Finset F.Cell} {z : F.Cell} (hz : z ∈ S) :
    ({z} : Finset F.Cell) ⊆ cellBall S z 3 := by
  classical
  intro y hy
  rw [Finset.mem_singleton.1 hy]
  exact Finset.mem_filter.2 ⟨hz, by rw [cellSupDist_self]; omega⟩
theorem bondsOver_singleton_subset {S : Finset F.Cell} {z : F.Cell} (hz : z ∈ S) (j : ℕ) :
    bondsOver S {z} j ⊆ bondsOver S (cellBall S z 3) j := by
  classical
  intro b hb
  obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hb
  exact Finset.mem_filter.2 ⟨h1, singleton_subset_cellBall hz h2⟩
theorem one_le_decayWeights_self (hL : 0 < F.blockSide) {θ : ℝ} (hθ : 0 ≤ θ) (δ : ℝ) (p : F.Site 0) (j : ℕ)
    (x : F.Site j) : 1 ≤ decayWeights F δ θ p (enclosingCell x) j x := by
  have hN : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by positivity
  have hp : (0 : ℝ) < (F.blockSide : ℝ) ^ j := by positivity
  unfold decayWeights
  rw [show cellSupDist (enclosingCell x) (enclosingCell x) = 0 by rw [cellSupDist_self]]
  simp only [Nat.cast_zero, mul_zero, Real.exp_zero, one_mul]
  refine Real.one_le_rpow_of_pos_of_le_one_of_nonpos (div_pos ?_ hN) ?_ (by linarith)
  · unfold scaleRadius
    exact lt_min hN (lt_of_lt_of_le hp (le_max_left _ _))
  · rw [div_le_one hN]
    exact min_le_left _ _
end BlockWeights
end YangMills.Construction
end
