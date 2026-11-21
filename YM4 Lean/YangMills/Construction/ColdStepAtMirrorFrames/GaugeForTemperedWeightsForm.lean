import YangMills.Construction.ColdStepAtMirrorFrames.EnergyOfAFlatChainNearACellProof
import YangMills.Construction.ColdStepAtMirrorFrames.CellMeansTakenOffAGauge
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.BlockAverages
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
theorem iteratedLineAverage_sub (B D : LevelForm F 0) (j : ℕ) :
    iteratedLineAverage (B - D) j = iteratedLineAverage B j - iteratedLineAverage D j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show lineAverage (iteratedLineAverage (B - D) j) =
      lineAverage (iteratedLineAverage B j) - lineAverage (iteratedLineAverage D j)
    rw [ih, lineAverage_sub]
theorem iteratedLineAverage_latticeGradient {j : ℕ} (hj : j ≤ F.top) (φ : F.Site 0 → ℝ) :
    iteratedLineAverage (latticeGradient φ) j = latticeGradient (iteratedBlockAverage φ j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show lineAverage (iteratedLineAverage (latticeGradient φ) j) =
      latticeGradient (blockAverage (iteratedBlockAverage φ j))
    rw [ih (by omega), lineAverage_latticeGradient hj]
theorem iteratedBlockAverage_top (hL : Odd F.blockSide) (φ : F.Site 0 → ℝ) (y : F.Cell) :
    iteratedBlockAverage φ F.top y = cellAverage φ y := by
  rw [iteratedBlockAverage_eq hL le_rfl]
  unfold cellAverage
  push_cast
  rfl
theorem sum_allSites_top_centredCube_range (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) (k : Fin 4)
    (G : F.Site 0 → ℝ) :
    ∑ y ∈ allSites F F.top, ∑ h ∈ centredCube (cellSide F), ∑ l ∈ Finset.range (cellSide F),
        G (_root_.YangMills.Construction.ColdStepAtMirrorFrames.refineSite 0 F.top y + siteOfCoords 0 h + axisOffset 0 k (l : ℤ)) =
      (cellSide F : ℝ) * ∑ x ∈ allSites F 0, G x := by
  have h0 : 0 ≤ F.top := Nat.zero_le _
  have e : ∀ l : ℕ, ∑ y ∈ allSites F F.top, ∑ h ∈ centredCube (cellSide F),
      G (_root_.YangMills.Construction.ColdStepAtMirrorFrames.refineSite 0 F.top y + siteOfCoords 0 h + axisOffset 0 k (l : ℤ)) = ∑ x ∈ allSites F 0, G x := by
    intro l
    have := sum_allSites_eq_sum_blocks hL hs h0 le_rfl (fun x => G (x + axisOffset 0 k (l : ℤ)))
    rw [sum_allSites_add_right hL hs h0 _ G] at this
    exact this.symm
  calc _ = ∑ y ∈ allSites F F.top, ∑ l ∈ Finset.range (cellSide F), ∑ h ∈ centredCube (cellSide F),
        G (_root_.YangMills.Construction.ColdStepAtMirrorFrames.refineSite 0 F.top y + siteOfCoords 0 h + axisOffset 0 k (l : ℤ)) :=
        Finset.sum_congr rfl fun y _ => Finset.sum_comm
    _ = ∑ l ∈ Finset.range (cellSide F), ∑ y ∈ allSites F F.top, ∑ h ∈ centredCube (cellSide F),
        G (_root_.YangMills.Construction.ColdStepAtMirrorFrames.refineSite 0 F.top y + siteOfCoords 0 h + axisOffset 0 k (l : ℤ)) := Finset.sum_comm
    _ = _ := by
        simp [e]
theorem weightedNormSq_iteratedLineAverage_le (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i)
    (u : F.Cell → ℝ) (w : F.Site 0 → ℝ) (κ : ℝ)
    (hκ : 0 ≤ κ) (hw : ∀ k y, ∀ h ∈ centredCube (cellSide F), ∀ l ∈ Finset.range (cellSide F),
      u y ^ 2 ≤ κ * w (_root_.YangMills.Construction.ColdStepAtMirrorFrames.refineSite 0 F.top y + siteOfCoords 0 h + axisOffset 0 k (l : ℤ)) ^ 2)
    (X : LevelForm F 0) :
    _root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq u (iteratedLineAverage X F.top) ≤ κ / (cellSide F : ℝ) ^ 2 * _root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq w X := by
  obtain ⟨a, ha⟩ := hL.pow (n := F.top)
  have ha' : cellSide F = 2 * a + 1 := ha
  have hNr : (0 : ℝ) < cellSide F := by exact_mod_cast cellSide_pos hL
  have hc : ((centredCube (cellSide F)).card : ℝ) = (cellSide F : ℝ) ^ 4 := by
    rw [card_centredCube ha']
    push_cast
    rfl
  unfold weightedNormSq
  rw [Finset.sum_comm, Finset.sum_comm (s := allSites F 0), Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have hy : ∀ y, (u y * iteratedLineAverage X F.top y k) ^ 2 ≤ κ / (cellSide F : ℝ) ^ 3 *
      ∑ h ∈ centredCube (cellSide F), ∑ l ∈ Finset.range (cellSide F),
        (w (refineSite 0 F.top y + siteOfCoords 0 h + axisOffset 0 k (l : ℤ)) *
          X (refineSite 0 F.top y + siteOfCoords 0 h + axisOffset 0 k (l : ℤ)) k) ^ 2 := by
    intro y
    have et : iteratedLineAverage X F.top y k = (1 / (cellSide F : ℝ) ^ 4) * ∑ h ∈ centredCube (cellSide F),
        ∑ l ∈ Finset.range (cellSide F), X (_root_.YangMills.Construction.ColdStepAtMirrorFrames.refineSite 0 F.top y + siteOfCoords 0 h + axisOffset 0 k (l : ℤ)) k :=
      iteratedLineAverage_eq hL le_rfl X y k
    rw [et]
    have c1 := sq_sum_sum_le_card_mul (centredCube (cellSide F)) (Finset.range (cellSide F))
      (fun h l => X (_root_.YangMills.Construction.ColdStepAtMirrorFrames.refineSite 0 F.top y + siteOfCoords 0 h + axisOffset 0 k (l : ℤ)) k)
    rw [hc, Finset.card_range] at c1
    have c2 : u y ^ 2 * ∑ h ∈ centredCube (cellSide F), ∑ l ∈ Finset.range (cellSide F),
          X (_root_.YangMills.Construction.ColdStepAtMirrorFrames.refineSite 0 F.top y + siteOfCoords 0 h + axisOffset 0 k (l : ℤ)) k ^ 2 ≤
        κ * ∑ h ∈ centredCube (cellSide F), ∑ l ∈ Finset.range (cellSide F),
          (w (refineSite 0 F.top y + siteOfCoords 0 h + axisOffset 0 k (l : ℤ)) *
            X (_root_.YangMills.Construction.ColdStepAtMirrorFrames.refineSite 0 F.top y + siteOfCoords 0 h + axisOffset 0 k (l : ℤ)) k) ^ 2 := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun h hh => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun l hl => ?_
      rw [mul_pow, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hw k y h hh l hl) (sq_nonneg _)
    have hu := sq_nonneg (u y)
    calc _ = u y ^ 2 * (1 / (cellSide F : ℝ) ^ 8) *
          (∑ h ∈ centredCube (cellSide F), ∑ l ∈ Finset.range (cellSide F),
          X (refineSite 0 F.top y + siteOfCoords 0 h + axisOffset 0 k (l : ℤ)) k) ^ 2 := by
          field_simp
      _ ≤ u y ^ 2 * (1 / (cellSide F : ℝ) ^ 8) * (((cellSide F : ℝ) ^ 4 * (cellSide F : ℝ)) *
          ∑ h ∈ centredCube (cellSide F), ∑ l ∈ Finset.range (cellSide F),
          X (_root_.YangMills.Construction.ColdStepAtMirrorFrames.refineSite 0 F.top y + siteOfCoords 0 h + axisOffset 0 k (l : ℤ)) k ^ 2) :=
          mul_le_mul_of_nonneg_left c1 (by positivity)
      _ = (1 / (cellSide F : ℝ) ^ 3) * (u y ^ 2 * ∑ h ∈ centredCube (cellSide F),
          ∑ l ∈ Finset.range (cellSide F),
          X (_root_.YangMills.Construction.ColdStepAtMirrorFrames.refineSite 0 F.top y + siteOfCoords 0 h + axisOffset 0 k (l : ℤ)) k ^ 2) := by
          field_simp
      _ ≤ (1 / (cellSide F : ℝ) ^ 3) * (κ * ∑ h ∈ centredCube (cellSide F), ∑ l ∈ Finset.range (cellSide F),
          (w (refineSite 0 F.top y + siteOfCoords 0 h + axisOffset 0 k (l : ℤ)) *
            X (_root_.YangMills.Construction.ColdStepAtMirrorFrames.refineSite 0 F.top y + siteOfCoords 0 h + axisOffset 0 k (l : ℤ)) k) ^ 2) :=
          mul_le_mul_of_nonneg_left c2 (by positivity)
      _ = _ := by
          field_simp
  calc _ ≤ ∑ y ∈ allSites F F.top, κ / (cellSide F : ℝ) ^ 3 *
      ∑ h ∈ centredCube (cellSide F), ∑ l ∈ Finset.range (cellSide F),
        (w (refineSite 0 F.top y + siteOfCoords 0 h + axisOffset 0 k (l : ℤ)) *
          X (_root_.YangMills.Construction.ColdStepAtMirrorFrames.refineSite 0 F.top y + siteOfCoords 0 h + axisOffset 0 k (l : ℤ)) k) ^ 2 :=
        Finset.sum_le_sum fun y _ => hy y
    _ = κ / (cellSide F : ℝ) ^ 3 * ((cellSide F : ℝ) * ∑ x ∈ allSites F 0, (w x * X x k) ^ 2) := by
        rw [← Finset.mul_sum, sum_allSites_top_centredCube_range hL hs k (fun x => (w x * X x k) ^ 2)]
    _ = _ := by
        field_simp
theorem weightedNormSq_le_three_mul {j : ℕ} (w : F.Site j → ℝ) (T X Y Z : LevelForm F j)
    (h : ∀ x k, (T x k) ^ 2 ≤ 3 * (X x k ^ 2 + Y x k ^ 2 + Z x k ^ 2)) :
    _root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq w T ≤ 3 * (_root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq w X + _root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq w Y + _root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq w Z) := by
  unfold weightedNormSq
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have := mul_le_mul_of_nonneg_left (h x k) (sq_nonneg (w x))
  nlinarith
theorem sq_add_add_le_three_mul (a b c : ℝ) : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
theorem sq_sub_sub_le_three_mul (a b c : ℝ) : (a - b - c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a + b), sq_nonneg (b - c), sq_nonneg (a + c)]
theorem weightedNormSq_add_add_add_le {j : ℕ} (w : F.Site j → ℝ) (X Y Z V : LevelForm F j) :
    _root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq w (X + Y + Z + V) ≤
      4 * (_root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq w X + _root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq w Y + _root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq w Z + _root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq w V) := by
  unfold weightedNormSq
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (w x * X x k - w x * Y x k), sq_nonneg (w x * X x k - w x * Z x k),
    sq_nonneg (w x * X x k - w x * V x k), sq_nonneg (w x * Y x k - w x * Z x k),
    sq_nonneg (w x * Y x k - w x * V x k), sq_nonneg (w x * Z x k - w x * V x k)]
theorem siteOfCoords_zero_vector (j : ℕ) : (siteOfCoords j ![0, 0, 0, 0] : F.Site j) = 0 := by
  funext i
  fin_cases i <;> simp [siteOfCoords]
def gaugeConstant (K : ℝ) : ℝ :=
  3 * (16 * K + 1200 * K ^ 2 * (1 + 16 * K + (16 * K) ^ 2 + (16 * K) ^ 3) +
    3 * (16 * K * (16 * K) ^ 3) * (1 + 16 * K ^ 2 + K * (1200 * K ^ 2 * (1 + 16 * K + (16 * K) ^ 2 + (16 * K) ^ 3))))
theorem gaugeConstant_pos {K : ℝ} (hK : 1 ≤ K) : 0 < gaugeConstant K := by
  have : 0 < K := by linarith
  unfold gaugeConstant
  positivity
theorem gaugeConstant_bound_aux {K P A T a b : ℝ} (hK : 0 ≤ K) (hP : 0 ≤ P) (hA : 0 ≤ A) (hT : 0 ≤ T)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    3 * (16 * K * P * T + P * (a * A) + P * (16 * K * b * (3 * (T + 16 * K ^ 2 * T + K * (a * A))))) ≤
      3 * (16 * K + a + 3 * (16 * K * b) * (1 + 16 * K ^ 2 + K * a)) * P * (A + T) := by
  have h1 : 0 ≤ 3 * P * (16 * K * A + a * T + 3 * (16 * K * b) * ((1 + 16 * K ^ 2) * A + K * a * T)) := by
    positivity
  linarith
set_option maxHeartbeats 1000000 in
theorem exists_cellAverage_eq_zero_weightedNormSq_addGradient_le (hL : Odd F.blockSide)
    (hs : ∀ i, 0 < F.extent i) (w : F.Site 0 → ℝ) (u : F.Cell → ℝ) (K : ℝ)
    (hK : 1 ≤ K) (hT : IsTemperedWeight w K)
    (hup : ∀ x, ∀ a ∈ windowEnds, ∀ b ∈ windowEnds, ∀ c ∈ windowEnds, ∀ d ∈ windowEnds,
      w x ^ 2 ≤ K * u (enclosingCell x + siteOfCoords F.top ![d, c, b, a]) ^ 2)
    (hdown : ∀ k y, ∀ h ∈ centredCube (cellSide F), ∀ l ∈ Finset.range (cellSide F),
      u y ^ 2 ≤ K * w (_root_.YangMills.Construction.ColdStepAtMirrorFrames.refineSite 0 F.top y + siteOfCoords 0 h + axisOffset 0 k (l : ℤ)) ^ 2)
    (B : LevelForm F 0) :
    ∃ φ : F.Site 0 → ℝ, (∀ v, cellAverage φ v = 0) ∧
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq w (addGradient B fun y => - φ y) ≤
        gaugeConstant K * (cellSide F : ℝ) ^ 2 *
          (weightedCurlNormSq w B + _root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq u (iteratedLineAverage B F.top)) := by
  have hNr : (0 : ℝ) < cellSide F := by exact_mod_cast cellSide_pos hL
  have hK0 : 0 ≤ K := by linarith
  set Z1 := windowProjection B 0 with hZ1
  set Z2 := windowProjection Z1 1 with hZ2
  set Z3 := windowProjection Z2 2 with hZ3
  set Z4 := windowProjection Z3 3 with hZ4
  set φ₀ : F.Site 0 → ℝ := fun x => directionGauge B 0 x + directionGauge Z1 1 x + directionGauge Z2 2 x +
    directionGauge Z3 3 x with hφ₀
  set R : LevelForm F 0 := directionDefect B 0 + directionDefect Z1 1 + directionDefect Z2 2 +
    directionDefect Z3 3 with hR
  have hsplit : ∀ x k, B x k = Z4 x k + latticeGradient φ₀ x k + R x k := by
    intro x k
    have s0 := eq_windowProjection_add_latticeGradient_add_directionDefect hL B 0 k x
    have s1 := eq_windowProjection_add_latticeGradient_add_directionDefect hL Z1 1 k x
    have s2 := eq_windowProjection_add_latticeGradient_add_directionDefect hL Z2 2 k x
    have s3 := eq_windowProjection_add_latticeGradient_add_directionDefect hL Z3 3 k x
    have eg : latticeGradient φ₀ x k = latticeGradient (directionGauge B 0) x k +
        latticeGradient (directionGauge Z1 1) x k +
        latticeGradient (directionGauge Z2 2) x k + latticeGradient (directionGauge Z3 3) x k := by
      simp only [latticeGradient, hφ₀]
      ring
    have eR : R x k = directionDefect B 0 x k + directionDefect Z1 1 x k + directionDefect Z2 2 x k +
        directionDefect Z3 3 x k := rfl
    rw [eg, eR]
    linarith
  set m : F.Cell → ℝ := cellAverage φ₀ with hm
  set ξ : F.Site 0 → ℝ := cellSpread m with hξ
  refine ⟨fun x => φ₀ x - ξ x, ?_, ?_⟩
  · intro v
    have e1 : cellAverage (fun x => φ₀ x - ξ x) v = cellAverage φ₀ v - cellAverage ξ v := by
      unfold cellAverage
      rw [Finset.sum_sub_distrib, mul_sub]
    rw [e1, hξ, cellAverage_cellSpread hL, hm, sub_self]
  set A := weightedCurlNormSq w B with hA
  set T := _root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq u (iteratedLineAverage B F.top) with hTdef
  set P := (cellSide F : ℝ) ^ 2 with hP
  have hP0 : 0 < P := by positivity
  have hA0 : 0 ≤ A := weightedCurlNormSq_nonneg _ _
  have hT0 : 0 ≤ T := _root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq_nonneg _ _
  set c : ℝ := 16 * K with hc
  have hc0 : 0 ≤ c := by positivity
  set a₁ : ℝ := 1200 * K ^ 2 * (1 + c + c ^ 2 + c ^ 3) with ha₁
  have ha₁0 : 0 ≤ a₁ := by positivity
  set b : ℝ := c ^ 3 with hb
  have hb0 : 0 ≤ b := by positivity
  have w1 : weightedCurlNormSq w Z1 ≤ c * A := weightedCurlNormSq_windowProjection_le hL hs hK0 hT B 0
  have w2 : weightedCurlNormSq w Z2 ≤ c ^ 2 * A := by
    have := weightedCurlNormSq_windowProjection_le hL hs hK0 hT Z1 1
    nlinarith [mul_le_mul_of_nonneg_left w1 hc0]
  have w3 : weightedCurlNormSq w Z3 ≤ c ^ 3 * A := by
    have := weightedCurlNormSq_windowProjection_le hL hs hK0 hT Z2 2
    nlinarith [mul_le_mul_of_nonneg_left w2 hc0]
  have hq : 0 ≤ 300 * P * K ^ 2 := by positivity
  have l0 := _root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq_directionDefect_le hL hs hK hT B 0
  have l1 := (_root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq_directionDefect_le hL hs hK hT Z1 1).trans (mul_le_mul_of_nonneg_left w1 hq)
  have l2 := (_root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq_directionDefect_le hL hs hK hT Z2 2).trans (mul_le_mul_of_nonneg_left w2 hq)
  have l3 := (_root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq_directionDefect_le hL hs hK hT Z3 3).trans (mul_le_mul_of_nonneg_left w3 hq)
  have hRn : _root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq w R ≤ P * (a₁ * A) := by
    have := _root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq_add_add_add_le w (directionDefect B 0) (directionDefect Z1 1)
      (directionDefect Z2 2) (directionDefect Z3 3)
    calc _root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq w R ≤ 4 * (_root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq w (directionDefect B 0) +
          _root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq w (directionDefect Z1 1) + _root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq w (directionDefect Z2 2) +
          _root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq w (directionDefect Z3 3)) := this
      _ ≤ 4 * (300 * P * K ^ 2 * weightedCurlNormSq w B + 300 * P * K ^ 2 * (c * A) +
          300 * P * K ^ 2 * (c ^ 2 * A) + 300 * P * K ^ 2 * (c ^ 3 * A)) := by linarith
      _ = _ := by
          rw [ha₁]
          ring
  have hZn : _root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq w Z4 ≤ 16 * K * P * T :=
    _root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq_stackedWindowProjection_le hL hs w u K hK0 hup B
  have hgm : latticeGradient m =
      iteratedLineAverage B F.top - iteratedLineAverage Z4 F.top - iteratedLineAverage R F.top := by
    have e1 : latticeGradient m = iteratedLineAverage (latticeGradient φ₀) F.top := by
      rw [iteratedLineAverage_latticeGradient le_rfl]
      congr 1
      funext y
      rw [iteratedBlockAverage_top hL]
    have e2 : latticeGradient φ₀ = B - Z4 - R := by
      funext x k
      have := hsplit x k
      simp only [Pi.sub_apply]
      linarith
    rw [e1, e2, iteratedLineAverage_sub, iteratedLineAverage_sub]
  have hTZ : _root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq u (iteratedLineAverage Z4 F.top) ≤ K / P * _root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq w Z4 :=
    _root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq_iteratedLineAverage_le hL hs u w K hK0 hdown Z4
  have hTR : _root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq u (iteratedLineAverage R F.top) ≤ K / P * _root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq w R :=
    _root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq_iteratedLineAverage_le hL hs u w K hK0 hdown R
  have hKP : 0 ≤ K / P := by positivity
  have hTZ' : _root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq u (iteratedLineAverage Z4 F.top) ≤ 16 * K ^ 2 * T := by
    refine hTZ.trans ((mul_le_mul_of_nonneg_left hZn hKP).trans (le_of_eq ?_))
    field_simp
  have hTR' : _root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq u (iteratedLineAverage R F.top) ≤ K * (a₁ * A) := by
    refine hTR.trans ((mul_le_mul_of_nonneg_left hRn hKP).trans (le_of_eq ?_))
    field_simp
  have hmn : _root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq u (latticeGradient m) ≤ 3 * (T + 16 * K ^ 2 * T + K * (a₁ * A)) := by
    have := _root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq_le_three_mul u (latticeGradient m) (iteratedLineAverage B F.top)
      (iteratedLineAverage Z4 F.top) (iteratedLineAverage R F.top) (fun y k => by
      rw [hgm]
      exact sq_sub_sub_le_three_mul _ _ _)
    linarith
  have hξn : _root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq w (latticeGradient ξ) ≤ P * (16 * K * b * _root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq u (latticeGradient m)) := by
    have hd : ∀ k, ∑ x ∈ allSites F 0,
        (w x * (m (enclosingCell x + unitStep F.top k) - m (enclosingCell x))) ^ 2 ≤
        K * (P ^ 2 * ∑ y ∈ allSites F F.top, (u y * latticeGradient m y k) ^ 2) := by
      intro k
      have e1 : ∀ x, (w x * (m (enclosingCell x + unitStep F.top k) - m (enclosingCell x))) ^ 2 ≤
          K * (u (enclosingCell x) * latticeGradient m (enclosingCell x) k) ^ 2 := by
        intro x
        have := hup x 0 (by simp [windowEnds]) 0 (by simp [windowEnds]) 0 (by simp [windowEnds]) 0
          (by simp [windowEnds])
        rw [siteOfCoords_zero_vector, add_zero] at this
        unfold latticeGradient
        rw [mul_pow, mul_pow, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
      calc _ ≤ ∑ x ∈ allSites F 0, K * (u (enclosingCell x) * latticeGradient m (enclosingCell x) k) ^ 2 :=
            Finset.sum_le_sum fun x _ => e1 x
        _ = K * ∑ x ∈ allSites F 0, (u (enclosingCell x) * latticeGradient m (enclosingCell x) k) ^ 2 := by
            rw [Finset.mul_sum]
        _ = _ := by
            rw [sum_allSites_enclosingCell hL hs (fun y => (u y * latticeGradient m y k) ^ 2), hP]
            ring
    have hk : ∀ k, ∑ x ∈ allSites F 0, (w x * latticeGradient ξ x k) ^ 2 ≤
        P * (16 * K * b * ∑ y ∈ allSites F F.top, (u y * latticeGradient m y k) ^ 2) := by
      intro k
      have s := sum_sq_latticeGradient_cellSpread_le hL hs hK0 hT m k
      have hcc : 0 ≤ (16 * K) ^ 3 * (16 / (cellSide F : ℝ) ^ 2) := by positivity
      refine s.trans ((mul_le_mul_of_nonneg_left (hd k) hcc).trans (le_of_eq ?_))
      rw [hb, hc, hP]
      field_simp
    unfold _root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq
    rw [Finset.sum_comm, Finset.sum_comm (s := allSites F F.top)]
    calc _ ≤ ∑ k : Fin 4, P * (16 * K * b * ∑ y ∈ allSites F F.top, (u y * latticeGradient m y k) ^ 2) :=
          Finset.sum_le_sum fun k _ => hk k
      _ = _ := by
          rw [← Finset.mul_sum, ← Finset.mul_sum]
  have hres : _root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq w (addGradient B fun y => - (φ₀ y - ξ y)) ≤
      3 * (_root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq w Z4 + _root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq w R + _root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq w (latticeGradient ξ)) := by
    refine _root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq_le_three_mul w _ Z4 R (latticeGradient ξ) fun x k => ?_
    have e : addGradient B (fun y => - (φ₀ y - ξ y)) x k = Z4 x k + R x k + latticeGradient ξ x k := by
      have := hsplit x k
      simp only [addGradient, latticeGradient] at this ⊢
      linarith
    rw [e]
    exact sq_add_add_le_three_mul _ _ _
  have hKc : gaugeConstant K = 3 * (16 * K + a₁ + 3 * (16 * K * b) * (1 + 16 * K ^ 2 + K * a₁)) := by
    unfold gaugeConstant
    rw [ha₁, hb, hc]
  have hfin : 3 * (16 * K * P * T + P * (a₁ * A) +
      P * (16 * K * b * (3 * (T + 16 * K ^ 2 * T + K * (a₁ * A))))) ≤
      gaugeConstant K * P * (A + T) := by
    rw [hKc]
    exact gaugeConstant_bound_aux hK0 hP0.le hA0 hT0 ha₁0 hb0
  calc _ ≤ 3 * (_root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq w Z4 + _root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq w R + _root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq w (latticeGradient ξ)) := hres
    _ ≤ 3 * (16 * K * P * T + P * (a₁ * A) +
        P * (16 * K * b * (3 * (T + 16 * K ^ 2 * T + K * (a₁ * A))))) := by
        have : P * (16 * K * b * _root_.YangMills.Construction.ColdStepAtMirrorFrames.weightedNormSq u (latticeGradient m)) ≤
            P * (16 * K * b * (3 * (T + 16 * K ^ 2 * T + K * (a₁ * A)))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmn (by positivity)) hP0.le
        linarith
    _ ≤ _ := hfin
end ColdStepAtMirrorFrames
end YangMills.Construction
end
