import YangMills.Construction.ColdStepAtMirrorFrames.PiecesOfTheTestOfAFlatChain
import YangMills.Construction.ColdStepAtMirrorFrames.PositionsAboutAPointForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
def shiftLength (F : BlockFrame) (m j : ℕ) : ℤ := (m : ℤ) * (F.blockSide : ℤ) ^ (F.depth - j)
def shiftForm (i : Fin 4) (m j : ℕ) (X : LevelForm F j) : LevelForm F j :=
  fun x k => X (x + axisOffset j i (shiftLength F m j)) k
theorem blockSide_mul_shiftLength_succ (m : ℕ) {j : ℕ} (hj : j + 1 ≤ F.depth) :
    (F.blockSide : ℤ) * shiftLength F m (j + 1) = shiftLength F m j := by
  unfold shiftLength
  have e : F.depth - j = (F.depth - (j + 1)) + 1 := by omega
  rw [e, pow_succ]
  ring
theorem refineSite_add_axisOffset {j : ℕ} (hj : j + 1 ≤ F.top) (y : F.Site (j + 1)) (i : Fin 4) (s : ℤ) :
    BlockAverages.refineSite (y + axisOffset (j + 1) i s) =
      BlockAverages.refineSite y + axisOffset j i ((F.blockSide : ℤ) * s) := by
  unfold axisOffset
  rw [blockRefine_add_siteOfCoords hj, mul_single]
theorem lineAverage_shiftForm {j : ℕ} (hj : j + 1 ≤ F.depth) (i : Fin 4) (m : ℕ) (X : LevelForm F j) :
    lineAverage (shiftForm i m j X) = shiftForm i m (j + 1) (lineAverage X) := by
  have hj' : j + 1 ≤ F.top := by
    unfold BlockFrame.top
    omega
  funext y k
  unfold lineAverage shiftForm
  beta_reduce
  rw [refineSite_add_axisOffset hj', blockSide_mul_shiftLength_succ m hj]
  congr 1
  refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun l _ => ?_
  have e : BlockAverages.refineSite y + siteOfCoords j h + siteOfCoords j (Pi.single k (l : ℤ)) +
      axisOffset j i (shiftLength F m j) =
      BlockAverages.refineSite y + axisOffset j i (shiftLength F m j) + siteOfCoords j h +
      siteOfCoords j (Pi.single k (l : ℤ)) := by abel
  rw [e]
def pathGauge (B₀ : LevelForm F 0) (i : Fin 4) (m : ℕ) : F.Site 0 → ℝ :=
  fun x => lineSum B₀ x i (m * F.blockSide ^ F.depth)
def shiftDifference (B : FormChain F) (i : Fin 4) (m : ℕ) : FormChain F := fun j =>
  shiftForm i m j (B j) - B j - latticeGradient (iteratedBlockAverage (pathGauge (B 0) i m) j)
theorem shiftDifference_zero_apply (B : FormChain F) (i : Fin 4) (m : ℕ) (x : F.Site 0) (k : Fin 4) :
    shiftDifference B i m 0 x k = ∑ l ∈ Finset.range (m * F.blockSide ^ F.depth),
      plaquetteCurl (B 0) (x + axisOffset 0 i (l : ℤ)) i k := by
  rw [← sub_lineSum_eq_sum_plaquetteCurl]
  have e : (shiftLength F m 0) = ((m * F.blockSide ^ F.depth : ℕ) : ℤ) := by
    unfold shiftLength
    push_cast
    rfl
  simp only [shiftDifference, shiftForm, Pi.sub_apply, e]
  rfl
theorem chainMisfit_shiftDifference (B : FormChain F) (i : Fin 4) (m : ℕ) {j : ℕ} (hj : j + 1 ≤ F.depth) :
    chainMisfit (shiftDifference B i m) j = shiftForm i m (j + 1) (chainMisfit B j) - chainMisfit B j := by
  have hj' : j + 1 ≤ F.top := by
    unfold BlockFrame.top
    omega
  funext y k
  have e : lineAverage (shiftDifference B i m j) =
      shiftForm i m (j + 1) (lineAverage (B j)) - lineAverage (B j) -
      latticeGradient (iteratedBlockAverage (pathGauge (B 0) i m) (j + 1)) := by
    unfold shiftDifference
    rw [lineAverage_sub, lineAverage_sub, lineAverage_shiftForm hj, lineAverage_latticeGradient hj']
    rfl
  unfold chainMisfit
  rw [e]
  simp only [shiftDifference, shiftForm, Pi.sub_apply]
  ring
theorem plaquetteCurl_shiftForm (i : Fin 4) (m j : ℕ) (X : LevelForm F j) (x : F.Site j) (k l : Fin 4) :
    plaquetteCurl (shiftForm i m j X) x k l =
      plaquetteCurl X (x + axisOffset j i (shiftLength F m j)) k l := by
  unfold plaquetteCurl shiftForm
  rw [add_right_comm x (unitStep j k), add_right_comm x (unitStep j l)]
theorem plaquetteCurl_shiftDifference (B : FormChain F) (i : Fin 4) (m j : ℕ) (x : F.Site j) (k l : Fin 4) :
    plaquetteCurl (shiftDifference B i m j) x k l =
      plaquetteCurl (B j) (x + axisOffset j i (shiftLength F m j)) k l - plaquetteCurl (B j) x k l := by
  unfold shiftDifference
  rw [plaquetteCurl_sub, plaquetteCurl_sub, plaquetteCurl_latticeGradient, plaquetteCurl_shiftForm, sub_zero]
def cutoff (c : Fin 4 → ℝ) (j : ℕ) (x : F.Site j) : ℝ := min 1 (max 0 (2 - distFromPoint c x / 2))
theorem cutoff_nonneg (c : Fin 4 → ℝ) {j : ℕ} (x : F.Site j) : 0 ≤ cutoff c j x :=
  le_min zero_le_one (le_max_left _ _)
theorem cutoff_le_one (c : Fin 4 → ℝ) {j : ℕ} (x : F.Site j) : cutoff c j x ≤ 1 := min_le_left _ _
theorem cutoff_eq_one (c : Fin 4 → ℝ) {j : ℕ} (x : F.Site j) (h : distFromPoint c x ≤ 2) :
    cutoff c j x = 1 := by
  unfold cutoff
  apply min_eq_left
  exact le_max_of_le_right (by linarith)
theorem cutoff_eq_zero (c : Fin 4 → ℝ) {j : ℕ} (x : F.Site j) (h : 4 ≤ distFromPoint c x) :
    cutoff c j x = 0 := by
  unfold cutoff
  have : max 0 (2 - distFromPoint c x / 2) = 0 := max_eq_left (by linarith)
  rw [this]
  exact min_eq_right zero_le_one
theorem abs_cutoff_sub_le (c : Fin 4 → ℝ) {j l : ℕ} (x : F.Site j) (x' : F.Site l) :
    |cutoff c l x' - cutoff c j x| ≤ 1 / 2 * |distFromPoint c x' - distFromPoint c x| := by
  unfold cutoff
  have h1 : |min (1 : ℝ) (max 0 (2 - distFromPoint c x' / 2)) - min 1 (max 0 (2 - distFromPoint c x / 2))| ≤
      |max (0 : ℝ) (2 - distFromPoint c x' / 2) - max 0 (2 - distFromPoint c x / 2)| := by
    have := abs_min_sub_min_le_max (1 : ℝ) (max 0 (2 - distFromPoint c x' / 2)) 1
      (max 0 (2 - distFromPoint c x / 2))
    simpa using this
  have h2 : |max (0 : ℝ) (2 - distFromPoint c x' / 2) - max 0 (2 - distFromPoint c x / 2)| ≤
      |(2 - distFromPoint c x' / 2) - (2 - distFromPoint c x / 2)| := by
    have := abs_max_sub_max_le_max (0 : ℝ) (2 - distFromPoint c x' / 2) 0 (2 - distFromPoint c x / 2)
    simpa using this
  have e : (2 - distFromPoint c x' / 2) - (2 - distFromPoint c x / 2) =
      -(1 / 2) * (distFromPoint c x' - distFromPoint c x) := by ring
  rw [e, abs_mul] at h2
  have : |(-(1 / 2) : ℝ)| = 1 / 2 := by norm_num
  rw [this] at h2
  linarith
def ballIndicator (c : Fin 4 → ℝ) (r : ℝ) (j : ℕ) (x : F.Site j) : ℝ :=
  open Classical in if distFromPoint c x ≤ r then 1 else 0
def localEnergy (c : Fin 4 → ℝ) (a : ℝ) (B : FormChain F) : ℝ :=
  weightedCurlNormSq (ballIndicator c (15 / 2) 0) (B 0) + a * totalMisfit (ballIndicator c (15 / 2)) B
theorem localEnergy_nonneg (c : Fin 4 → ℝ) {a : ℝ} (ha : 0 ≤ a) (B : FormChain F) : 0 ≤ localEnergy c a B :=
  add_nonneg (weightedCurlNormSq_nonneg _ _) (mul_nonneg ha (totalMisfit_nonneg _ _))
theorem nearWeight_sq_le_ballIndicator_sq (c : Fin 4 → ℝ) {r r' : ℝ} {j : ℕ} (x : F.Site j)
    (hr : r + readReach F j ≤ r') :
    nearWeight c r j x ^ 2 ≤ ballIndicator c r' j x ^ 2 := by
  unfold nearWeight ballIndicator
  by_cases h : j ≤ F.depth ∧ distFromPoint c x ≤ r + readReach F j
  · rw [if_pos h, if_pos (h.2.trans hr)]
  · rw [if_neg h]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact sq_nonneg _
end ColdStepAtMirrorFrames
end YangMills.Construction
end
