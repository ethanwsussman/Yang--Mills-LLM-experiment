import YangMills.Construction.ColdChainAtEveryLevel.EvaluationsOfAChain
import YangMills.Construction.ColdChainAtEveryLevel.FramedChainsOverATopProof
import YangMills.Construction.HoleBesideASecondHole.BlocksOfTheLevels
import YangMills.Construction.HoleBesideASecondHole.CostBelowTheTotalOfCoordinates
import YangMills.Construction.HoleBesideASecondHole.CostOnWholeCellsIsTheLeastAction
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages CellTerms
namespace LumpContours.ChartActionLowerBound
open BlockLevels
variable {F : BlockFrame}
theorem gaugedBlockFit_gaugeTransform {j : ℕ} (γ : F.Site (j + 1) → UnitQuaternion) (X : F.GaugeField j)
    (k : F.Site (j + 1) → UnitQuaternion) (X' : F.GaugeField (j + 1)) (c : F.Site (j + 1) × Fin 4) :
    gaugedBlockFit X (fun y => γ y * k y) (gaugeTransform γ X') c = gaugedBlockFit X k X' c := by apply _root_.YangMills.Construction.BlockAverages.GaugedChains.gaugedBlockFit_gaugeTransform <;> assumption
def partialGaugedAction (a : ℝ) (S : Finset F.Cell) (X : F.FieldChain) (k : F.SiteGauge) (j : ℕ) : ℝ :=
  wilsonAction S (X 0) + a * ∑ i ∈ Finset.range j, ∑ c ∈ innerBonds S (i + 1),
    gaugedBlockFit (X i) (k (i + 1)) (X (i + 1)) c
theorem wilsonAction_gaugeTransform (hG : gaugeCovarianceStatement) (hL : 0 < F.blockSide)
    (S : Finset F.Cell) (γ : F.Site 0 → UnitQuaternion) (U : F.GaugeField 0) :
    wilsonAction S (gaugeTransform γ U) = wilsonAction S U := by apply _root_.YangMills.Construction.BlockAverages.GaugedChains.wilsonAction_gaugeTransform <;> assumption
theorem blockFit_gaugeTransform_eq (hG : gaugeCovarianceStatement) (hL : 0 < F.blockSide) {j : ℕ}
    (hj : j < F.top) (γ : F.Site j → UnitQuaternion) (k : F.Site (j + 1) → UnitQuaternion)
    (hγ : ∀ y, γ (refineSite y) = k y)
    (X : F.GaugeField j) (X' : F.GaugeField (j + 1)) (c : F.Site (j + 1) × Fin 4) :
    blockFit (gaugeTransform γ X) X' c = gaugedBlockFit X k X' c := by apply _root_.YangMills.Construction.BlockAverages.GaugedChains.blockFit_gaugeTransform_eq <;> assumption
theorem partialGaugedAction_update (hG : gaugeCovarianceStatement) (a : ℝ) (hL : 0 < F.blockSide)
    (S : Finset F.Cell) {j : ℕ} (hj : j < F.top) (X : F.FieldChain) (k : F.SiteGauge)
    (γ : F.Site j → UnitQuaternion) :
    partialGaugedAction a S (Function.update X j (gaugeTransform γ (X j)))
        (Function.update k j (fun y => γ y * k j y)) j =
      partialGaugedAction a S X k j := by
  set W := gaugeTransform γ (X j) with hW
  set X2 : F.FieldChain := Function.update X j W with hX2
  set k2 : F.SiteGauge := Function.update k j (fun y => γ y * k j y) with hk2
  have hX2j : X2 j = W := by simp [hX2]
  cases j with
  | zero =>
    simp only [partialGaugedAction, Finset.range_zero, Finset.sum_empty, mul_zero, add_zero, hX2j]
    exact wilsonAction_gaugeTransform hG hL S γ (X 0)
  | succ i =>
    have hlo : ∀ m, m ≤ i → X2 m = X m := fun m hm => Function.update_of_ne (by omega) _ _
    have hkl : ∀ m, m ≤ i → k2 m = k m := fun m hm => Function.update_of_ne (by omega) _ _
    simp only [partialGaugedAction]
    rw [hlo 0 (Nat.zero_le _), Finset.sum_range_succ, Finset.sum_range_succ]
    have h1 : ∑ m ∈ Finset.range i, ∑ c ∈ innerBonds S (m + 1),
        gaugedBlockFit (X2 m) (k2 (m + 1)) (X2 (m + 1)) c =
        ∑ m ∈ Finset.range i, ∑ c ∈ innerBonds S (m + 1),
          gaugedBlockFit (X m) (k (m + 1)) (X (m + 1)) c := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mem_range] at hm
      rw [hlo m (by omega), hlo (m + 1) (by omega), hkl (m + 1) (by omega)]
    have h2 : ∑ c ∈ innerBonds S (i + 1), gaugedBlockFit (X2 i) (k2 (i + 1)) (X2 (i + 1)) c =
        ∑ c ∈ innerBonds S (i + 1), gaugedBlockFit (X i) (k (i + 1)) (X (i + 1)) c := by
      rw [hlo i le_rfl, hX2j]
      have : k2 (i + 1) = fun y => γ y * k (i + 1) y := by simp [hk2]
      rw [this]
      exact Finset.sum_congr rfl fun c _ => gaugedBlockFit_gaugeTransform γ _ _ _ c
    rw [h1, h2]
open Classical in
def levelGauge {j : ℕ} (k : F.Site (j + 1) → UnitQuaternion) (z : F.Site j) : UnitQuaternion :=
  if h : ∃ y, refineSite y = z then k h.choose else 1
theorem levelGauge_refineSite (hG : gaugeCovarianceStatement) (hL : 0 < F.blockSide) {j : ℕ}
    (hj : j < F.top) (k : F.Site (j + 1) → UnitQuaternion) (y : F.Site (j + 1)) :
    levelGauge k (refineSite y) = k y := by
  have hinj := (hG F j hj hL).1
  have hex : ∃ y', refineSite y' = refineSite y := ⟨y, rfl⟩
  simp only [levelGauge, dif_pos hex]
  rw [hinj hex.choose_spec]
theorem minimalAction_le_partial (hG : gaugeCovarianceStatement) (hV : minimalChainExistenceStatement)
    (a : ℝ) (ha : 0 ≤ a) (hL : 0 < F.blockSide) (S : Finset F.Cell) :
    ∀ j, j ≤ F.top → ∀ (X : F.FieldChain) (k : F.SiteGauge),
      minimalAction a S j (X j) ≤ partialGaugedAction a S X k j := by apply _root_.YangMills.Construction.BlockAverages.GaugedChains.minimalAction_le_partialGaugedAction <;> assumption
theorem blockEnergy_le_gaugedChainAction (hG : gaugeCovarianceStatement) (hV : minimalChainExistenceStatement)
    (a : ℝ) (ha : 0 ≤ a) (hL : 0 < F.blockSide) (S : Finset F.Cell) (X : F.FieldChain) (k : F.SiteGauge) :
    blockEnergy a S F.depth (gaugeTransform (centreGauge (k F.top)) (X F.depth)) (X F.top) ≤
      gaugedChainAction a S X k := by
  classical
  have hj : F.depth < F.top := Nat.lt_succ_self _
  set γ : F.Site F.depth → UnitQuaternion := centreGauge (k F.top) with hγ
  have hγd : ∀ y, γ (refineSite y) = k (F.depth + 1) y := levelGauge_refineSite hG hL hj (k (F.depth + 1))
  set W := gaugeTransform γ (X F.depth) with hW
  have hlow := minimalAction_le_partial hG hV a ha hL S F.depth (Nat.le_succ _) (Function.update X F.depth W)
    (Function.update k F.depth (fun y => γ y * k F.depth y))
  have hX2j : (Function.update X F.depth W) F.depth = W := by simp
  rw [hX2j, partialGaugedAction_update hG a hL S hj X k γ] at hlow
  have hfit : ∑ c ∈ innerBonds S F.top, blockFit W (X F.top) c =
      ∑ c ∈ innerBonds S F.top, gaugedBlockFit (X F.depth) (k F.top) (X F.top) c :=
    Finset.sum_congr rfl fun c _ => blockFit_gaugeTransform_eq hG hL hj γ _ hγd _ _ c
  calc blockEnergy a S F.depth W (X F.top) =
        minimalAction a S F.depth W + a * ∑ c ∈ innerBonds S F.top, blockFit W (X F.top) c := rfl
    _ ≤ partialGaugedAction a S X k F.depth +
          a * ∑ c ∈ innerBonds S F.top, gaugedBlockFit (X F.depth) (k F.top) (X F.top) c := by
        rw [hfit]
        gcongr
    _ = _ := by
        simp only [partialGaugedAction, gaugedChainAction]
        have e := Finset.sum_range_succ
          (fun i => ∑ c ∈ innerBonds S (i + 1), gaugedBlockFit (X i) (k (i + 1)) (X (i + 1)) c) F.depth
        rw [show Finset.range F.top = Finset.range (F.depth + 1) from rfl, e]
        ring
theorem chartChain_of_lt (R : F.FieldChain) (U : ChainChart F) (V : F.GaugeField F.top) {j : ℕ}
    (hj : j < F.top) : chartChain R U V j = chartField R U j := by apply _root_.YangMills.Construction.BlockAverages.ChartCoordinates.chartChain_of_lt <;> assumption
theorem chartChain_top (R : F.FieldChain) (U : ChainChart F) (V : F.GaugeField F.top) :
    chartChain R U V F.top = V := by apply _root_.YangMills.Construction.BlockAverages.ChartCoordinates.chartChain_top <;> assumption
theorem chartActionLowerBound (hG : gaugeCovarianceStatement) (hV : minimalChainExistenceStatement)
    (hF : gaugedChainLowerBoundStatement) (hC : CutActionEqualsMinimalAction)
    (hE : WholeCellCostEqualsMinimalAction) : chartActionLowerBoundStatement := by
  intro F a S ha hL R U V
  constructor
  · have h1 := (hF F a S ha hL.pos).1 (chartChain R U V) (chartGauge R U)
    rw [chartChain_top] at h1
    have e : sitesOfCells S F.top = S := by
      ext y
      rw [mem_sitesOfCells_iff le_rfl hL, enclosingCell_cell hL.pos]
    have h2 := (hC F a ha).2 hL S F.top le_rfl V
    rw [e] at h2
    rw [h2]
    exact h1
  · rw [(hE F a S hL ha).2.2]
    have h := blockEnergy_le_gaugedChainAction hG hV a ha hL.pos S (chartChain R U V) (chartGauge R U)
    rw [chartChain_of_lt R U V (Nat.lt_succ_self _), chartChain_top] at h
    exact h
end LumpContours.ChartActionLowerBound
end YangMills.Construction
end
