import YangMills.Construction.ColdChainAtEveryLevel.BondNormsAndSiteNorms
import YangMills.Construction.ColdChainAtEveryLevel.PoincareOnACell
import YangMills.Construction.ColdChainAtEveryLevel.RestOnCells
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
open BondSiteNorms PatchDifferences CellPoincare GaugeMap
variable {F : BlockFrame} {S : Finset F.Cell}
theorem mul_sum_div_add_le_mul_sum {g h : F.Cell → ℝ} {N Cr Cq s : ℝ} {B : Finset F.Cell} (hN : 0 < N)
    (hCr : 0 ≤ Cr) (hs : 0 ≤ s) (hg : ∀ y ∈ B, g y ≤ Cq * N * h y) :
    Cr * s * ∑ y ∈ B, (g y / N + h y) ≤ Cr * s * ((Cq + 1) * ∑ y ∈ B, h y) := by
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCr hs)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun y hy => ?_
  have h1 : g y / N ≤ Cq * h y := by
    rw [div_le_iff₀ hN]
    have := hg y hy
    linarith
  linarith
theorem cellBondNorm_nonneg (q : ℝ) (f : F.Site 0 → Fin 4 → ℍ[ℝ])
    (z : F.Cell) (w : F.Site 0 → ℝ) (hw : ∀ x, 0 ≤ w x) : 0 ≤ cellBondNorm q S w f z :=
  Real.rpow_nonneg (Finset.sum_nonneg fun _ _ =>
    Real.rpow_nonneg (mul_nonneg (hw _) (norm_nonneg _)) _) _
theorem cellBondNorm_le_of_formNormOn_le {q : ℝ} (hq : 1 ≤ q) {w : F.Site 0 → ℝ} (hw : ∀ x, 0 ≤ w x)
    {f g : F.Site 0 → Fin 4 → ℍ[ℝ]} {A : ℝ} (hA : 0 ≤ A) {z₀ : F.Cell}
    (h : weightedLpNormOnCell q S w (formNormOn S f) z₀ ≤
      A * ∑ y ∈ cellBall S z₀ 22, weightedLpNormOnCell q S w (formNormOn S g) y) :
    cellBondNorm q S w f z₀ ≤ (16 * A) * ∑ y ∈ cellBall S z₀ 22, cellBondNorm q S w g y := by
  have h1 := cellBondNorm_le (S := S) hq hw f z₀
  have h2 : ∑ y ∈ cellBall S z₀ 22, weightedLpNormOnCell q S w (formNormOn S g) y ≤
      4 * ∑ y ∈ cellBall S z₀ 22, cellBondNorm q S w g y := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun y _ => weightedLpNormOnCell_formNormOn_le hq hw g y
  have h3 := mul_le_mul_of_nonneg_left h2 hA
  calc cellBondNorm q S w f z₀ ≤ 4 * weightedLpNormOnCell q S w (formNormOn S f) z₀ := h1
    _ ≤ 4 * (A * (4 * ∑ y ∈ cellBall S z₀ 22, cellBondNorm q S w g y)) :=
        mul_le_mul_of_nonneg_left (h.trans h3) (by norm_num)
    _ = _ := by ring
theorem gaugeMapOnDifferencesStatement_holds (hKc : cellKernelBoundsStatement)
    (hRc : gaugeRemainderCellBoundStatement) (hPc : cellPoincareStatement) :
    gaugeMapOnDifferencesStatement := by
  classical
  obtain ⟨K, hK0, hKer⟩ := hKc
  obtain ⟨Cr, cr, L1r, hCr, hcr, hR⟩ := hRc K hK0
  obtain ⟨Cq, cq, L1q, hCq, hcq, hQ⟩ := hPc K hK0
  obtain ⟨C1, hC1d⟩ : ∃ C1, C1 = 16 * (Cr * (Cq + 1)) := ⟨_, rfl⟩
  have hC10 : 0 < C1 := by rw [hC1d]; positivity
  refine ⟨min cr cq, C1 * 45 ^ 4 + 4 * Cq + C1 + 1, max L1r L1q, lt_min hcr hcq, by positivity, ?_⟩
  intro F m S hodd hL1 hamb hm hreg s V hs hsc hcold
  have hL := hodd.pos
  have hN0 : (0 : ℝ) < cellSideLength F := by exact_mod_cast cellSideLength_pos (F := F) hL
  obtain ⟨hMF, hRest⟩ := hR F m S hodd ((le_max_left _ _).trans hL1) hamb hm hreg s V hs
    (hsc.trans (min_le_left _ _)) hcold
  refine ⟨hMF, fun ξ hξ => ?_⟩
  obtain ⟨hMFr, hNorm⟩ := hRest ξ hξ
  have hPo := hQ F m S hodd ((le_max_right _ _).trans hL1) hamb hm hreg s V hs
    (hsc.trans (min_le_right _ _)) hcold ξ hξ
  obtain ⟨hW, hPl⟩ := hKer F m S hodd hamb hm hreg
  have hCle1 : C1 ≤ C1 * 45 ^ 4 + 4 * Cq + C1 + 1 := by
    have : 0 ≤ C1 * 45 ^ 4 := by positivity
    linarith
  have hCle2 : C1 * 45 ^ 4 ≤ C1 * 45 ^ 4 + 4 * Cq + C1 + 1 := by linarith
  have hCle3 : 4 * Cq ≤ C1 * 45 ^ 4 + 4 * Cq + C1 + 1 := by
    have : 0 ≤ C1 * 45 ^ 4 := by positivity
    linarith
  obtain ⟨Ct, hCt⟩ : ∃ Ct, Ct = C1 * 45 ^ 4 + 4 * Cq + C1 + 1 := ⟨_, rfl⟩
  rw [← hCt] at hCle1 hCle2 hCle3 ⊢
  have hCt0 : 0 ≤ Ct := by linarith
  obtain ⟨Dξ, hDξ⟩ : ∃ Dξ, Dξ = covariantDiff (referenceFieldChain S V 0) ξ := ⟨_, rfl⟩
  obtain ⟨DR, hDR⟩ : ∃ DR, DR = covariantDiff (referenceFieldChain S V 0) (gaugeRemainder S V ξ) :=
    ⟨_, rfl⟩
  rw [← hDξ, ← hDR]
  rw [← hDξ] at hPo
  have hfam : ∀ {q : ℝ} {w : F.Site 0 → ℝ} {Lf : (F.Site 0 → ℝ) → F.Cell → ℝ}
      {Sr : (F.Site 0 → ℝ) → F.Cell → ℝ} {σ : F.Cell → ℝ}, 1 ≤ q → (∀ x, 0 ≤ w x) →
      CellNormFamily S (weightedLpNormOnCell q S w) Lf Sr σ K → ∀ z₀ ∈ S,
      cellBondNorm q S w DR z₀ ≤ (C1 * s) * ∑ y ∈ cellBall S z₀ 22, cellBondNorm q S w Dξ y := by
    intro q w Lf Sr σ hq hw hN z₀ hz₀
    have h1 := hNorm _ Lf Sr σ hN z₀ hz₀
    rw [← hDξ, ← hDR] at h1
    have h2 := mul_sum_div_add_le_mul_sum (B := cellBall S z₀ 22)
      (g := weightedLpNormOnCell q S w (sectionNormOn S ξ))
      (h := weightedLpNormOnCell q S w (formNormOn S Dξ)) (Cq := Cq) hN0 hCr.le hs.le
      (fun y hy => (hPo y (Finset.mem_filter.1 hy).1).1 _ Lf Sr σ hN)
    have h3 := cellBondNorm_le_of_formNormOn_le (S := S) (g := Dξ) (f := DR) hq hw
      (A := Cr * s * (Cq + 1)) (by positivity) (z₀ := z₀)
      (by
        refine h1.trans (h2.trans (le_of_eq ?_))
        ring)
    refine h3.trans (le_of_eq ?_)
    rw [hC1d]
    ring
  refine ⟨hMFr, fun φ θ del p hθ hdel hlip => ?_, fun B hB z hz => ?_, fun z hz => ?_⟩
  · have hw : ∀ x, 0 ≤ classWeight F φ θ p 0 x := fun x => by
      unfold classWeight
      have hLr : (0 : ℝ) < F.blockSide := by exact_mod_cast hL
      have h1 : 0 ≤ scaleRadius F 0 p x := by
        unfold scaleRadius
        exact le_min (by positivity) (le_trans (by norm_num) (le_max_left _ _))
      exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (by positivity) _)
    have hN := hW φ θ del p hθ hdel hlip
    have hcell := hfam (q := 4) (by norm_num) hw hN
    obtain ⟨w, hwd⟩ : ∃ w, w = classWeight F φ θ p 0 := ⟨_, rfl⟩
    rw [← hwd] at hw hcell hN ⊢
    have ha : ∀ z, 0 ≤ cellBondNorm 4 S w DR z := fun z =>
      cellBondNorm_nonneg _ _ _ _ hw
    have hb : ∀ z, 0 ≤ cellBondNorm 4 S w Dξ z := fun z =>
      cellBondNorm_nonneg _ _ _ _ hw
    have hPcell : ∀ z ∈ S, cellSiteNorm 4 S w ξ z ≤
        (4 * Cq) * (cellSideLength F : ℝ) * cellBondNorm 4 S w Dξ z := by
      intro z hz
      rw [cellSiteNorm_eq hw]
      have h1 := (hPo z hz).1 _ _ _ _ hN
      have h2 := weightedLpNormOnCell_formNormOn_le (S := S) (p := 4) (by norm_num) hw Dξ z
      have h3 : 0 ≤ Cq * (cellSideLength F : ℝ) := by positivity
      calc _ ≤ Cq * (cellSideLength F : ℝ) * weightedLpNormOnCell 4 S w (formNormOn S Dξ) z := h1
        _ ≤ Cq * (cellSideLength F : ℝ) * (4 * cellBondNorm 4 S w Dξ z) :=
            mul_le_mul_of_nonneg_left h2 h3
        _ = _ := by ring
    refine ⟨?_, ?_, fun z₀ hz₀ => ?_, fun z hz => ?_⟩
    · rw [cellwiseL4Norm_eq, cellwiseL4Norm_eq]
      have h1 := sum_sq_le_of_le_sum_cellBall (S := S) hamb _ _ ha hb (C := C1 * s) (by positivity) hcell
      have h2 : Real.sqrt (∑ z ∈ S, cellBondNorm 4 S w DR z ^ 2) ≤
          (C1 * s * 45 ^ 4) * Real.sqrt (∑ z ∈ S, cellBondNorm 4 S w Dξ z ^ 2) := by
        rw [← Real.sqrt_sq (by positivity : 0 ≤ C1 * s * 45 ^ 4), ← Real.sqrt_mul (by positivity)]
        exact Real.sqrt_le_sqrt h1
      refine h2.trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
      have : C1 * s * 45 ^ 4 = (C1 * 45 ^ 4) * s := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right hCle2 hs.le
    · rw [cellwiseL4Norm_eq]
      have h1 : ∑ z ∈ S, cellSiteNorm 4 S w ξ z ^ 2 ≤
          ((4 * Cq) * (cellSideLength F : ℝ)) ^ 2 * ∑ z ∈ S, cellBondNorm 4 S w Dξ z ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun z hz => ?_
        rw [← mul_pow]
        have h0 : 0 ≤ cellSiteNorm 4 S w ξ z := by
          rw [cellSiteNorm_eq hw]
          exact hN.isSeminorm_base.nonneg _ _
        exact pow_le_pow_left₀ h0 (hPcell z hz) 2
      have h2 : Real.sqrt (∑ z ∈ S, cellSiteNorm 4 S w ξ z ^ 2) ≤
          ((4 * Cq) * (cellSideLength F : ℝ)) * Real.sqrt (∑ z ∈ S, cellBondNorm 4 S w Dξ z ^ 2) := by
        rw [← Real.sqrt_sq (by positivity : 0 ≤ (4 * Cq) * (cellSideLength F : ℝ)),
          ← Real.sqrt_mul (by positivity)]
        exact Real.sqrt_le_sqrt h1
      refine h2.trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
      exact mul_le_mul_of_nonneg_right hCle3 hN0.le
    · refine (hcell z₀ hz₀).trans (mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun _ _ => hb _))
      exact mul_le_mul_of_nonneg_right hCle1 hs.le
    · refine (hPcell z hz).trans (mul_le_mul_of_nonneg_right ?_ (hb z))
      exact mul_le_mul_of_nonneg_right hCle3 hN0.le
  · have hw : ∀ x : F.Site 0, (0 : ℝ) ≤ (fun _ => (1 : ℝ)) x := fun _ => by norm_num
    have hcell := hfam (q := 3) (by norm_num) hw hPl z hz
    have hB0 : 0 ≤ B := (cellBondNorm_nonneg _ _ _ _ hw).trans (hB z hz)
    have hcard : ((cellBall S z 22).card : ℝ) ≤ 45 ^ 4 := by
      have h1 := card_le_of_cellSupDist_le hamb z 22 (cellBall S z 22) fun y hy =>
        (Finset.mem_filter.1 hy).2
      have h2 : ((cellBall S z 22).card : ℝ) ≤ (((2 * 22 + 1) ^ 4 : ℕ) : ℝ) := by exact_mod_cast h1
      norm_num at h2 ⊢
      exact h2
    have h1 : ∑ y ∈ cellBall S z 22, cellBondNorm 3 S (fun _ => 1) Dξ y ≤ 45 ^ 4 * B := by
      calc _ ≤ ∑ _y ∈ cellBall S z 22, B := Finset.sum_le_sum fun y hy => hB y (Finset.mem_filter.1 hy).1
        _ = ((cellBall S z 22).card : ℝ) * B := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right hcard hB0
    refine hcell.trans ?_
    calc C1 * s * ∑ y ∈ cellBall S z 22, cellBondNorm 3 S (fun _ => 1) Dξ y ≤ C1 * s * (45 ^ 4 * B) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (C1 * 45 ^ 4) * s * B := by ring
      _ ≤ Ct * s * B := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCle2 hs.le) hB0
  · have hw : ∀ x : F.Site 0, (0 : ℝ) ≤ (fun _ => (1 : ℝ)) x := fun _ => by norm_num
    have hb0 : 0 ≤ cellBondNorm 3 S (fun _ => 1) Dξ z :=
      cellBondNorm_nonneg _ _ _ _ hw
    have h4 := weightedLpNormOnCell_formNormOn_le (S := S) (p := 3) (by norm_num) hw Dξ z
    constructor
    · rw [cellSiteNorm_eq hw]
      have h1 := (hPo z hz).1 _ _ _ _ hPl
      have h3 : 0 ≤ Cq * (cellSideLength F : ℝ) := by positivity
      calc _ ≤ Cq * (cellSideLength F : ℝ) * weightedLpNormOnCell 3 S (fun _ => 1) (formNormOn S Dξ) z := h1
        _ ≤ Cq * (cellSideLength F : ℝ) * (4 * cellBondNorm 3 S (fun _ => 1) Dξ z) :=
            mul_le_mul_of_nonneg_left h4 h3
        _ = (4 * Cq) * (cellSideLength F : ℝ) * cellBondNorm 3 S (fun _ => 1) Dξ z := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCle3 hN0.le) hb0
    · rw [cellSiteNorm_eq hw]
      have h1 := (hPo z hz).2
      calc _ ≤ Cq * weightedLpNormOnCell 3 S (fun _ => 1) (formNormOn S Dξ) z := h1
        _ ≤ Cq * (4 * cellBondNorm 3 S (fun _ => 1) Dξ z) := mul_le_mul_of_nonneg_left h4 hCq.le
        _ = (4 * Cq) * cellBondNorm 3 S (fun _ => 1) Dξ z := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hCle3 hb0
end YangMills.Construction.BlockAverages
end
