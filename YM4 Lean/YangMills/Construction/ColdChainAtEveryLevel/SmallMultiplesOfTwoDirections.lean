import YangMills.Construction.ColdChainAtEveryLevel.TermsOfTheLevelsBelowTheTop
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction.SmallMultiples
open BlockAverages (BlockFrame ChainChart chartMove zeroChart linearPart parallelAverage adjointAction
  UnitQuaternion imaginaryQuaternions innerBonds)
open LevelRecursion (finsetLpNorm finsetLpNorm_mono finsetLpNorm_nonneg weightedScaleNorm)
open ComplexDifferences (hullBallRadius firstDiffFactor secondDiffFactor finsetLpNorm_const_mul_le)
open ComplexLevels (hullBondCount)
open HullBounds (hullFactor)
open ComplexRemainders (bondHullNorm bondHullNorm_add_le bondHullNorm_smul)
open ComplexifiedQuaternions (ComplexQuat)
open RealDirections (abs_le_finsetLpNorm weightedScaleNorm_le_mul)
variable {F : BlockFrame}
def scaledChart (U : ChainChart F) (ε : ℝ) : ChainChart F := chartMove (zeroChart F) U ε
def scaledSumChart (U A : ChainChart F) (ε : ℝ) : ChainChart F := chartMove (chartMove (zeroChart F) U ε) A ε
theorem scaledChart_fine (U : ChainChart F) (ε : ℝ) (x : F.Site 0) (i : Fin 4) :
    (scaledChart U ε).fine x i = ε • U.fine x i := by
  simp [scaledChart, chartMove, zeroChart]
theorem scaledChart_coarse (U : ChainChart F) (ε : ℝ) (m : ℕ) (y : F.Site (m + 1)) (i : Fin 4) :
    (scaledChart U ε).coarse m y i = ε • U.coarse m y i := by
  simp [scaledChart, chartMove, zeroChart]
theorem scaledSumChart_fine (U A : ChainChart F) (ε : ℝ) (x : F.Site 0) (i : Fin 4) :
    (scaledSumChart U A ε).fine x i = (scaledChart U ε).fine x i + (scaledChart A ε).fine x i := by
  simp [scaledSumChart, scaledChart, chartMove, zeroChart]
theorem scaledSumChart_coarse (U A : ChainChart F) (ε : ℝ) (m : ℕ) (y : F.Site (m + 1)) (i : Fin 4) :
    (scaledSumChart U A ε).coarse m y i = (scaledChart U ε).coarse m y i + (scaledChart A ε).coarse m y i := by
  simp [scaledSumChart, scaledChart, chartMove, zeroChart]
theorem parallelAverage_smul {j : ℕ} (R : F.GaugeField j) (ε : ℝ) (f : F.Site j → Fin 4 → ℍ[ℝ])
    (c : F.Site (j + 1) × Fin 4) :
    parallelAverage R (fun x i => ε • f x i) c = ε • parallelAverage R f c := by
  have hs : ∀ (g : UnitQuaternion) (a : ℍ[ℝ]), _root_.YangMills.Construction.BlockAverages.adjointAction g (ε • a) = ε • _root_.YangMills.Construction.BlockAverages.adjointAction g a := by
    intro g a
    simp [_root_.YangMills.Construction.BlockAverages.adjointAction]
  simp only [parallelAverage, hs, ← Finset.smul_sum]
  rw [smul_comm]
theorem linearPart_scaledChart (R : F.FieldChain) (U : ChainChart F) (ε : ℝ) (m : ℕ) (x : F.Site m) (i : Fin 4) :
    linearPart R (scaledChart U ε) m x i = ε • linearPart R U m x i := by
  induction m generalizing i with
  | zero =>
    simp only [linearPart, scaledChart_fine]
    rfl
  | succ m ih =>
    have h : linearPart R (scaledChart U ε) m = fun x i => ε • linearPart R U m x i := by
      funext x' i'
      exact ih x' i'
    simp only [linearPart]
    rw [h, parallelAverage_smul]
    split_ifs with hc
    · rw [scaledChart_coarse, smul_add]
      rfl
    · simp
def smallnessThreshold (L : ℕ) : ℝ :=
  1 / (10 ^ 7 * (L : ℝ) * (1 + 200000 * (L : ℝ) ^ 2) * (1 + hullFactor L) * (1 + hullBondCount L))
theorem hullBondCount_nonneg (L : ℕ) : 0 ≤ hullBondCount L := by apply _root_.YangMills.Construction.ComplexCells.hullBondCount_nonneg <;> assumption
theorem smallness_bounds (hodd : Odd F.blockSide) {C₀ s η T : ℝ} (hx0 : 0 ≤ C₀ * s)
    (hx : C₀ * s ≤ smallnessThreshold F.blockSide) (hη0 : 0 ≤ η)
    (hη : η * (1 + hullBondCount F.blockSide + hullFactor F.blockSide) ≤ smallnessThreshold F.blockSide)
    (hT0 : 0 ≤ T) (hT : T ≤ smallnessThreshold F.blockSide) :
    C₀ * s ≤ 1 / 64 ∧ 24 * (6 * (hullBondCount F.blockSide * η) + C₀ * s) < hullBallRadius F.blockSide ∧
    3 * (2 * (hullBondCount F.blockSide * η) + C₀ * s) < hullBallRadius F.blockSide ∧
    12 * (200000 * (F.blockSide : ℝ) ^ 2) * (6 * (hullBondCount F.blockSide * η) + C₀ * s) ≤ 1 ∧
    2 * (hullBondCount F.blockSide * η) ≤ 1 ∧ 9 * η ≤ 1 ∧
    568 * secondDiffFactor F.blockSide C₀ s η * hullFactor F.blockSide ≤ 1 ∧
    568 * firstDiffFactor F.blockSide C₀ s η * hullFactor F.blockSide ≤ 1 ∧
    24 * (2 * T + C₀ * s) < hullBallRadius F.blockSide ∧
    12 * (200000 * (F.blockSide : ℝ) ^ 2) * (2 * T + C₀ * s) ≤ 1 ∧
    200000 * (F.blockSide : ℝ) ^ 2 * (T + C₀ * s) ≤ 1 ∧
    8 * (F.blockSide : ℝ) * T ≤ 1 / 1024 ∧ T ≤ 1 / 64 ∧ η < 1 := by
  have hL1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  have hF0 := LowerLevelTerms.hullFactor_nonneg (F := F) hodd
  have hH0 := hullBondCount_nonneg F.blockSide
  set K := 200000 * (F.blockSide : ℝ) ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  set H := hullBondCount F.blockSide with hH
  set Fh := hullFactor F.blockSide with hFh
  set κ := smallnessThreshold F.blockSide with hκ
  have hL0 : (0 : ℝ) < F.blockSide := by linarith
  have hκ0 : 0 < κ := by
    simp only [hκ, smallnessThreshold]
    positivity
  have hP : κ * (10 ^ 7 * (F.blockSide : ℝ) * (1 + K) * (1 + Fh) * (1 + H)) = 1 := by
    have : (10 ^ 7 * (F.blockSide : ℝ) * (1 + K) * (1 + Fh) * (1 + H)) ≠ 0 := by positivity
    exact one_div_mul_cancel this
  have a1 : κ * (F.blockSide : ℝ) * (1 + K) * (1 + Fh) ≤ 1 / 10 ^ 7 := by
    have h1 : 0 ≤ κ * (F.blockSide : ℝ) * (1 + K) * (1 + Fh) := by positivity
    have h3 : κ * (F.blockSide : ℝ) * (1 + K) * (1 + Fh) * 10 ^ 7 ≤ 1 := by
      have : κ * (F.blockSide : ℝ) * (1 + K) * (1 + Fh) * 10 ^ 7 * 1 ≤
          κ * (F.blockSide : ℝ) * (1 + K) * (1 + Fh) * 10 ^ 7 * (1 + H) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    norm_num at h3 ⊢
    linarith
  have a2 : κ * (1 + K) * (1 + Fh) ≤ 1 / 10 ^ 7 := by
    have : κ * (1 + K) * (1 + Fh) * 1 ≤ κ * (1 + K) * (1 + Fh) * (F.blockSide : ℝ) :=
      mul_le_mul_of_nonneg_left hL1 (by positivity)
    have e : κ * (1 + K) * (1 + Fh) * (F.blockSide : ℝ) = κ * (F.blockSide : ℝ) * (1 + K) * (1 + Fh) := by ring
    linarith
  have a3 : κ * (1 + K) ≤ 1 / 10 ^ 7 := by
    have : κ * (1 + K) * 1 ≤ κ * (1 + K) * (1 + Fh) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have a4 : κ ≤ 1 / 10 ^ 7 := by
    have : κ * 1 ≤ κ * (1 + K) := mul_le_mul_of_nonneg_left (by linarith) hκ0.le
    linarith
  have a5 : κ * (F.blockSide : ℝ) ≤ 1 / 10 ^ 7 := by
    have h1 : κ * (F.blockSide : ℝ) * 1 ≤ κ * (F.blockSide : ℝ) * ((1 + K) * (1 + Fh)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have : 1 * 1 ≤ (1 + K) * (1 + Fh) := mul_le_mul (by linarith) (by linarith) (by norm_num) (by linarith)
      linarith
    have e : κ * (F.blockSide : ℝ) * ((1 + K) * (1 + Fh)) = κ * (F.blockSide : ℝ) * (1 + K) * (1 + Fh) := by ring
    linarith
  have hη1 : η ≤ κ := by
    have : η * 1 ≤ η * (1 + H + Fh) := mul_le_mul_of_nonneg_left (by linarith) hη0
    linarith
  have hηH : H * η ≤ κ := by
    have : η * H ≤ η * (1 + H + Fh) := mul_le_mul_of_nonneg_left (by linarith) hη0
    linarith
  have hηF : Fh * η ≤ κ := by
    have : η * Fh ≤ η * (1 + H + Fh) := mul_le_mul_of_nonneg_left (by linarith) hη0
    linarith
  have hrad : (1 / 10 ^ 4 : ℝ) / (F.blockSide : ℝ) ≤ hullBallRadius F.blockSide := by
    unfold hullBallRadius
    rw [div_le_div_iff₀ hL0 (by positivity)]
    nlinarith
  have hκr : κ ≤ (1 / 10 ^ 7 : ℝ) / (F.blockSide : ℝ) := by
    rw [le_div_iff₀ hL0]
    exact a5
  have hr2 : (1 / 10 ^ 7 : ℝ) / (F.blockSide : ℝ) * 1000 = (1 / 10 ^ 4 : ℝ) / (F.blockSide : ℝ) := by ring
  have fac : ∀ {y : ℝ}, 0 ≤ y → y ≤ 200 * κ * (1 + K) → 568 * y * Fh ≤ 1 := by
    intro y hy0 hy
    have h1 : y * Fh ≤ 200 * κ * (1 + K) * (1 + Fh) := mul_le_mul hy (by linarith) hF0 (by positivity)
    have e : 200 * κ * (1 + K) * (1 + Fh) = 200 * (κ * (1 + K) * (1 + Fh)) := by ring
    rw [e] at h1
    have e2 : 568 * y * Fh = 568 * (y * Fh) := by ring
    rw [e2]
    norm_num at a2
    linarith
  have hKκ : K * κ ≤ 1 / 10 ^ 7 := by
    have e : κ * (1 + K) = κ + K * κ := by ring
    rw [e] at a3
    linarith
  refine ⟨by norm_num at a4; linarith, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : 24 * (6 * (H * η) + C₀ * s) ≤ 24 * (6 * κ + κ) := by linarith
    have h0 : 0 < κ := hκ0
    linarith
  · have : 3 * (2 * (H * η) + C₀ * s) ≤ 3 * (2 * κ + κ) := by linarith
    have h0 : 0 < κ := hκ0
    linarith
  · have h1 : K * (6 * (H * η) + C₀ * s) ≤ K * (7 * κ) := mul_le_mul_of_nonneg_left (by linarith) hK0
    have e : 12 * K * (6 * (H * η) + C₀ * s) = 12 * (K * (6 * (H * η) + C₀ * s)) := by ring
    rw [e]
    norm_num at hKκ
    linarith
  · norm_num at a4
    linarith
  · norm_num at a4
    linarith
  · refine fac (by unfold secondDiffFactor; positivity) ?_
    unfold secondDiffFactor
    have h1 : 24 * K * (6 * (H * η) + C₀ * s) ≤ 24 * K * (7 * κ) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have e : 200 * κ * (1 + K) = 200 * κ + 200 * (K * κ) := by ring
    have hKκ0 : 0 ≤ K * κ := by positivity
    rw [e, ← hK, ← hH]
    linarith
  · refine fac (by unfold firstDiffFactor; positivity) ?_
    unfold firstDiffFactor
    have h1 : 24 * K * (2 * (Fh * η) + 5 * (C₀ * s)) ≤ 24 * K * (7 * κ) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have e : 200 * κ * (1 + K) = 200 * κ + 200 * (K * κ) := by ring
    have hKκ0 : 0 ≤ K * κ := by positivity
    rw [e, ← hK, ← hFh]
    linarith
  · have : 24 * (2 * T + C₀ * s) ≤ 24 * (3 * κ) := by linarith
    have h0 : 0 < κ := hκ0
    linarith
  · have h1 : K * (2 * T + C₀ * s) ≤ K * (3 * κ) := mul_le_mul_of_nonneg_left (by linarith) hK0
    have e : 12 * K * (2 * T + C₀ * s) = 12 * (K * (2 * T + C₀ * s)) := by ring
    rw [e]
    norm_num at hKκ
    linarith
  · have h1 : K * (T + C₀ * s) ≤ K * (2 * κ) := mul_le_mul_of_nonneg_left (by linarith) hK0
    norm_num at hKκ
    linarith
  · have h1 : (F.blockSide : ℝ) * T ≤ (F.blockSide : ℝ) * κ := mul_le_mul_of_nonneg_left hT hL0.le
    have e : 8 * (F.blockSide : ℝ) * T = 8 * ((F.blockSide : ℝ) * T) := by ring
    rw [e]
    norm_num at a5
    linarith
  · norm_num at a4
    linarith
  · norm_num at a4
    linarith
theorem bondHullNorm_sub_le {j : ℕ} (c : F.Site (j + 1) × Fin 4) (a b : F.Site j → Fin 4 → ComplexQuat) :
    bondHullNorm c (a - b) ≤ bondHullNorm c a + bondHullNorm c b := by
  have e : a - b = a + (-1 : ℂ) • b := by
    funext x i
    simp [sub_eq_add_neg]
  rw [e]
  refine (bondHullNorm_add_le c a _).trans (le_of_eq ?_)
  rw [bondHullNorm_smul]
  simp
structure DominatedBy (U A : ChainChart F) (ε : ℝ) (W : ChainChart F) : Prop where
  fine : ∀ x i, ‖(W.fine x i : ℍ[ℝ])‖ ≤ ε * (‖(U.fine x i : ℍ[ℝ])‖ + ‖(A.fine x i : ℍ[ℝ])‖)
  coarse : ∀ m y i, ‖(W.coarse m y i : ℍ[ℝ])‖ ≤ ε * (‖(U.coarse m y i : ℍ[ℝ])‖ + ‖(A.coarse m y i : ℍ[ℝ])‖)
theorem norm_coe_smul_imaginary (ε : ℝ) (hε : 0 ≤ ε) (x : imaginaryQuaternions) :
    ‖((ε • x : imaginaryQuaternions) : ℍ[ℝ])‖ = ε * ‖(x : ℍ[ℝ])‖ := by
  have : ((ε • x : imaginaryQuaternions) : ℍ[ℝ]) = ε • (x : ℍ[ℝ]) := rfl
  rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg hε]
theorem dominatedBy_scaledChart_left (U A : ChainChart F) {ε : ℝ} (hε : 0 ≤ ε) :
    DominatedBy U A ε (scaledChart U ε) where
  fine x i := by
    rw [scaledChart_fine, norm_coe_smul_imaginary ε hε]
    exact mul_le_mul_of_nonneg_left (by linarith [norm_nonneg (A.fine x i : ℍ[ℝ])]) hε
  coarse m y i := by
    rw [scaledChart_coarse, norm_coe_smul_imaginary ε hε]
    exact mul_le_mul_of_nonneg_left (by linarith [norm_nonneg (A.coarse m y i : ℍ[ℝ])]) hε
theorem dominatedBy_scaledChart_right (U A : ChainChart F) {ε : ℝ} (hε : 0 ≤ ε) :
    DominatedBy U A ε (scaledChart A ε) where
  fine x i := by
    rw [scaledChart_fine, norm_coe_smul_imaginary ε hε]
    exact mul_le_mul_of_nonneg_left (by linarith [norm_nonneg (U.fine x i : ℍ[ℝ])]) hε
  coarse m y i := by
    rw [scaledChart_coarse, norm_coe_smul_imaginary ε hε]
    exact mul_le_mul_of_nonneg_left (by linarith [norm_nonneg (U.coarse m y i : ℍ[ℝ])]) hε
theorem dominatedBy_scaledSumChart (U A : ChainChart F) {ε : ℝ} (hε : 0 ≤ ε) :
    DominatedBy U A ε (scaledSumChart U A ε) where
  fine x i := by
    rw [scaledSumChart_fine, scaledChart_fine, scaledChart_fine]
    have e : ((ε • U.fine x i + ε • A.fine x i : imaginaryQuaternions) : ℍ[ℝ]) =
        ((ε • U.fine x i : imaginaryQuaternions) : ℍ[ℝ]) + ((ε • A.fine x i : imaginaryQuaternions) : ℍ[ℝ]) := rfl
    rw [e]
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_coe_smul_imaginary ε hε, norm_coe_smul_imaginary ε hε]
    ring
  coarse m y i := by
    rw [scaledSumChart_coarse, scaledChart_coarse, scaledChart_coarse]
    have e : ((ε • U.coarse m y i + ε • A.coarse m y i : imaginaryQuaternions) : ℍ[ℝ]) =
        ((ε • U.coarse m y i : imaginaryQuaternions) : ℍ[ℝ]) +
          ((ε • A.coarse m y i : imaginaryQuaternions) : ℍ[ℝ]) := rfl
    rw [e]
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_coe_smul_imaginary ε hε, norm_coe_smul_imaginary ε hε]
    ring
theorem dominatedBy_zeroChart (U A : ChainChart F) {ε : ℝ} (hε : 0 ≤ ε) : DominatedBy U A ε (zeroChart F) where
  fine x i := by
    have : (((zeroChart F).fine x i : imaginaryQuaternions) : ℍ[ℝ]) = 0 := rfl
    rw [this, norm_zero]
    positivity
  coarse m y i := by
    have : (((zeroChart F).coarse m y i : imaginaryQuaternions) : ℍ[ℝ]) = 0 := rfl
    rw [this, norm_zero]
    positivity
def pairSize (D : Finset F.Cell) (U A : ChainChart F) : ℝ :=
  finsetLpNorm 4 (innerBonds D 0) (fun b => ‖(U.fine b.1 b.2 : ℍ[ℝ])‖ + ‖(A.fine b.1 b.2 : ℍ[ℝ])‖) +
    ∑ m ∈ Finset.range F.top, finsetLpNorm 2 (innerBonds D (m + 1))
      (fun b => ‖(U.coarse m b.1 b.2 : ℍ[ℝ])‖ + ‖(A.coarse m b.1 b.2 : ℍ[ℝ])‖)
theorem pairSize_nonneg (D : Finset F.Cell) (U A : ChainChart F) : 0 ≤ pairSize D U A :=
  add_nonneg (finsetLpNorm_nonneg _ _ _) (Finset.sum_nonneg fun _ _ => finsetLpNorm_nonneg _ _ _)
theorem DominatedBy.finsetLpNorm_fine_le {U A W : ChainChart F} {ε : ℝ} (h : DominatedBy U A ε W) (hε : 0 ≤ ε)
    (D : Finset F.Cell) :
    finsetLpNorm 4 (innerBonds D 0) (fun b => ‖(W.fine b.1 b.2 : ℍ[ℝ])‖) ≤ ε * pairSize D U A := by
  have s1 : finsetLpNorm 4 (innerBonds D 0) (fun b => ‖(W.fine b.1 b.2 : ℍ[ℝ])‖) ≤ finsetLpNorm 4 (innerBonds D 0)
      (fun b => ε * (‖(U.fine b.1 b.2 : ℍ[ℝ])‖ + ‖(A.fine b.1 b.2 : ℍ[ℝ])‖)) := by
    refine finsetLpNorm_mono (by norm_num) _ fun b _ => ?_
    rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by positivity)]
    exact h.fine _ _
  refine s1.trans ((finsetLpNorm_const_mul_le (by norm_num) _ _ hε).trans (mul_le_mul_of_nonneg_left ?_ hε))
  have : 0 ≤ ∑ m ∈ Finset.range F.top, finsetLpNorm 2 (innerBonds D (m + 1))
      (fun b => ‖(U.coarse m b.1 b.2 : ℍ[ℝ])‖ + ‖(A.coarse m b.1 b.2 : ℍ[ℝ])‖) :=
    Finset.sum_nonneg fun _ _ => finsetLpNorm_nonneg _ _ _
  simp only [pairSize]
  linarith
theorem DominatedBy.finsetLpNorm_coarse_le {U A W : ChainChart F} {ε : ℝ} (h : DominatedBy U A ε W)
    (hε : 0 ≤ ε) (D : Finset F.Cell) {m : ℕ} (hm : m < F.top) :
    finsetLpNorm 2 (innerBonds D (m + 1)) (fun b => ‖(W.coarse m b.1 b.2 : ℍ[ℝ])‖) ≤ ε * pairSize D U A := by
  have s1 : finsetLpNorm 2 (innerBonds D (m + 1)) (fun b => ‖(W.coarse m b.1 b.2 : ℍ[ℝ])‖) ≤
      finsetLpNorm 2 (innerBonds D (m + 1))
        (fun b => ε * (‖(U.coarse m b.1 b.2 : ℍ[ℝ])‖ + ‖(A.coarse m b.1 b.2 : ℍ[ℝ])‖)) := by
    refine finsetLpNorm_mono (by norm_num) _ fun b _ => ?_
    rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by positivity)]
    exact h.coarse _ _ _
  refine s1.trans ((finsetLpNorm_const_mul_le (by norm_num) _ _ hε).trans (mul_le_mul_of_nonneg_left ?_ hε))
  have h1 := Finset.single_le_sum (f := fun m => finsetLpNorm 2 (innerBonds D (m + 1))
    (fun b => ‖(U.coarse m b.1 b.2 : ℍ[ℝ])‖ + ‖(A.coarse m b.1 b.2 : ℍ[ℝ])‖)) (fun _ _ => finsetLpNorm_nonneg _ _ _)
    (Finset.mem_range.2 hm)
  have h2 := finsetLpNorm_nonneg 4 (innerBonds D 0)
    (fun b => ‖(U.fine b.1 b.2 : ℍ[ℝ])‖ + ‖(A.fine b.1 b.2 : ℍ[ℝ])‖)
  simp only [pairSize]
  linarith
theorem DominatedBy.norm_fine_le {U A W : ChainChart F} {ε : ℝ} (h : DominatedBy U A ε W) (hε : 0 ≤ ε)
    {D : Finset F.Cell} {b : F.Site 0 × Fin 4} (hb : b ∈ innerBonds D 0) :
    ‖(W.fine b.1 b.2 : ℍ[ℝ])‖ ≤ ε * pairSize D U A := by
  have h1 := abs_le_finsetLpNorm (P := 4) (by norm_num) (innerBonds D 0) (fun b => ‖(W.fine b.1 b.2 : ℍ[ℝ])‖) hb
  rw [abs_of_nonneg (norm_nonneg _)] at h1
  exact h1.trans (h.finsetLpNorm_fine_le hε D)
theorem DominatedBy.norm_coarse_le {U A W : ChainChart F} {ε : ℝ} (h : DominatedBy U A ε W) (hε : 0 ≤ ε)
    {D : Finset F.Cell} {m : ℕ} (hm : m < F.top) {b : F.Site (m + 1) × Fin 4} (hb : b ∈ innerBonds D (m + 1)) :
    ‖(W.coarse m b.1 b.2 : ℍ[ℝ])‖ ≤ ε * pairSize D U A := by
  have h1 := abs_le_finsetLpNorm (P := 2) (by norm_num) (innerBonds D (m + 1))
    (fun b => ‖(W.coarse m b.1 b.2 : ℍ[ℝ])‖) hb
  rw [abs_of_nonneg (norm_nonneg _)] at h1
  exact h1.trans (h.finsetLpNorm_coarse_le hε D hm)
def linearPartError (L : ℕ) (Ln c₀ T B : ℝ) : ℝ :=
  hullFactor L * (142 * (5 * Ln * (T * B)) + 284 * (3 * T * B +
    5 * (4 + 200000 * (L : ℝ) ^ 2) * c₀ * (hullFactor L * (82272 * B)) +
    5 * (200000 * (L : ℝ) ^ 2) * T * Ln * (hullFactor L * (82272 * B)))) +
  200000 * (L : ℝ) ^ 2 * (T + c₀) * (5 * (hullFactor L * (82272 * B)))
structure PairWeightedNorms (D : Finset F.Cell) (p : F.Site 0) (θ : ℝ) (U A : ChainChart F) (Bu Ba : ℝ) :
    Prop where
  fine_le : weightedScaleNorm D p θ 4 0 (fun x i => ‖(U.fine x i : ℍ[ℝ])‖) ≤ Bu
  coarse_le : ∀ m, m + 1 < F.top →
    weightedScaleNorm D p θ 2 (m + 1) (fun y d => ‖(U.coarse m y d : ℍ[ℝ])‖) ≤ Bu
  fine_inv_le : weightedScaleNorm D p (-θ) 4 0 (fun x i => ‖(A.fine x i : ℍ[ℝ])‖) ≤ Ba
  coarse_inv_le : ∀ m, m + 1 < F.top →
    weightedScaleNorm D p (-θ) 2 (m + 1) (fun y d => ‖(A.coarse m y d : ℍ[ℝ])‖) ≤ Ba
theorem weightedScaleNorm_le_of_abs_le (hodd : Odd F.blockSide) {D : Finset F.Cell} (p : F.Site 0) (θ : ℝ)
    {P : ℕ} (hP : 1 ≤ P) (m : ℕ) {f g : F.Site m → Fin 4 → ℝ} {ε B : ℝ} (hε : 0 ≤ ε)
    (hfg : ∀ b ∈ innerBonds D m, |f b.1 b.2| ≤ ε * g b.1 b.2)
    (hg : ∀ x d, 0 ≤ g x d) (hB : weightedScaleNorm D p θ P m g ≤ B) : weightedScaleNorm D p θ P m f ≤ ε * B :=
  (weightedScaleNorm_le_mul hodd p θ hP m hε hfg fun b _ => hg _ _).trans (mul_le_mul_of_nonneg_left hB hε)
end YangMills.Construction.SmallMultiples
end
