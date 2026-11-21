import YangMills.Construction.ColdStepAtMirrorFrames.BlockEnergyUnderGaugesAndShifts
import YangMills.Construction.ColdStepAtMirrorFrames.ChartEnergyInCoordinatesProof
import YangMills.Construction.ColdStepAtMirrorFrames.ColdChainOneLevelBelow
import YangMills.Construction.ColdStepAtMirrorFrames.ConvexAboveAChartPointProof
import YangMills.Construction.ColdStepAtMirrorFrames.GaugeOfTheLeastChartProof
import YangMills.Construction.ColdStepAtMirrorFrames.TranslationOfTheLeastChartProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
namespace CellEnergyShareInvariance
theorem cellCentre_add (hs : ∀ i, 2 ≤ F.extent i) {j : ℕ} (hj : j ≤ F.top) (z h : F.Cell) :
    (cellCentre j (z + h) : F.Site j) = cellCentre j z + cellCentre j h := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.Translation.cellCentre_add <;> assumption
theorem cellCentre_top (hs : ∀ i, 2 ≤ F.extent i) (h : F.Cell) : (cellCentre F.top h : F.Cell) = h := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.Translation.cellCentre_top <;> assumption
theorem cellCentre_neg (hs : ∀ i, 2 ≤ F.extent i) {j : ℕ} (hj : j ≤ F.top) (h : F.Cell) :
    (cellCentre j (-h) : F.Site j) = - cellCentre j h := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.Translation.cellCentre_neg <;> assumption
theorem translate_mem_innerBonds (hs : ∀ i, 2 ≤ F.extent i) {j : ℕ} (hj : j ≤ F.top) (h : F.Cell)
    {c : F.Site j × Fin 4} (hc : c ∈ innerBonds (finiteCells F) j) :
    (c.1 + cellCentre j h, c.2) ∈ innerBonds (finiteCells F) j := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.Translation.add_cellCentre_mem_innerBonds <;> assumption
theorem blockFit_translateField (hL : 0 < F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) {j : ℕ} (hj : j < F.top)
    (h : F.Cell) (W : F.GaugeField j) (V : F.GaugeField (j + 1)) (c : F.Site (j + 1) × Fin 4) :
    blockFit (translateField (cellCentre j h) W) (translateField (cellCentre (j + 1) h) V)
      (c.1 + cellCentre (j + 1) h, c.2) = blockFit W V c := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.Translation.blockFit_translateField <;> assumption
theorem expUnit_adjointMap (g : UnitQuaternion) (v : imaginaryQuaternions) :
    expUnit (adjointMap g v) = g * expUnit v * g⁻¹ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.MinimalChart.expUnit_adjointMap <;> assumption
theorem chartedField_congr (hcover : BlocksCoverLowerLevel) (hL : Odd F.blockSide) (hs0 : ∀ i, 0 < F.extent i)
    {w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions} (V : F.GaugeField F.top)
    (h : ∀ b ∈ chordBonds (finiteCells F), w b.1 b.2 = w' b.1 b.2) : chartedField w V = chartedField w' V := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.HessianConvexity.chartedField_congr <;> assumption
theorem mem_innerBonds_top (hs : ∀ i, 2 ≤ F.extent i) (b : F.Site F.top × Fin 4) :
    b ∈ innerBonds (finiteCells F) F.top := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartedEnergyCoordinates.mem_innerBonds_top <;> assumption
end CellEnergyShareInvariance
open CellEnergyShareInvariance in
theorem CellEnergyShareInvariance.cellEnergyShareInvariant_holds (hch : ColdEstimatesAtEveryDepth)
    (hS : SiteDecomposition) (hG : gaugeCovarianceStatement) (hcover : BlocksCoverLowerLevel) :
    CellEnergyShareInvariant := by
  classical
  intro a L c ha hLo hL40 hc F w w' V hF hsm Y
  obtain ⟨N, hN0, hNc⟩ := hch a L c ha hLo hL40 hc
  have hold := hNc.1 F c.σA (chartedField w V) hF hc.positivity.2.2.2.1 le_rfl hsm.small_curvature
  have hFL : F.blockSide = L := hF.1
  obtain ⟨nside, h64, hside⟩ := hF.2
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by
    rw [hside i]
    omega
  have hs0 : ∀ i, 0 < F.extent i := fun i => by
    have := hs i
    omega
  have hL : Odd F.blockSide := by rw [hFL]; exact hLo
  have hLpos : 0 < F.blockSide := hL.pos
  have hcov := hcover F hL hs0
  refine ⟨fun γ hw => ?_, fun h hw => ?_⟩
  · obtain ⟨Γ, hΓ⟩ : ∃ Γ : F.Site F.depth → UnitQuaternion, Γ = fun x => γ (enclosingCell x) := ⟨_, rfl⟩
    have hdown : ∀ y : F.Cell, enclosingCell (refineSite y : F.Site F.depth) = y := by
      intro y
      have hk : (0 : Fin 4 → ℤ) ∈ centredCube F.blockSide := by
        obtain ⟨k, hk⟩ := hL
        have hLz : (F.blockSide : ℤ) = 2 * k + 1 := by exact_mod_cast hk
        unfold centredCube
        rw [Fintype.mem_piFinset]
        intro i
        simp only [Pi.zero_apply, Finset.mem_Icc]
        rw [hLz]
        omega
      have h1 := ((hS F hL hs).1 y 0 hk).1
      have e1 : (siteOfCoords F.depth (0 : Fin 4 → ℤ) : F.Site F.depth) = 0 := by
        funext i
        simp [siteOfCoords]
      rw [e1, add_zero] at h1
      have e2 : (cellCentre F.depth y : F.Site F.depth) = refineSite y := by
        funext i
        simp [cellCentre, refineSite, siteOfCoords, BlockFrame.top]
      rw [e2] at h1
      exact h1
    have hfield : chartedField w' (gaugeTransform γ V) = gaugeTransform Γ (chartedField w V) := by
      have e1 : chartedField w' (gaugeTransform γ V) =
          chartedField (fun x i => adjointMap (γ (enclosingCell x)) (w x i)) (gaugeTransform γ V) :=
        chartedField_congr hcover hL hs0 _ fun b hb => Subtype.ext (hw b hb)
      rw [e1]
      funext x i
      simp only [chartedField, gaugeTransform, hΓ]
      by_cases hc' : IsCrossingBond (x, i)
      · have hnext : enclosingCell (x + unitStep F.depth i) = enclosingCell x + unitStep F.top i := by
          rcases (hS F hL hs).2.2.2 x i with h | h
          · exact absurd h hc'
          · exact h
        simp only [if_pos hc', hnext, expUnit_adjointMap]
        group
      · have hsame : enclosingCell (x + unitStep F.depth i) = enclosingCell x := by
          by_contra hne
          exact hc' hne
        simp only [if_neg hc', hsame]
        by_cases ht : IsAxialTreeBond (x, i)
        · simp [if_pos ht]
        · simp only [if_neg ht, expUnit_adjointMap]
    unfold cellEnergyShare
    rw [hfield]
    refine congrArg₂ (· + ·) ?_ (congrArg (fun u => a / 2 * u) ?_)
    · exact Finset.sum_congr rfl fun y _ => hold.siteShare_gauge_invariant y Γ
    · refine Finset.sum_congr rfl fun c' _ => ?_
      exact (hG F F.depth (by simp [BlockFrame.top]) hLpos).2.2.2 Γ γ _ V c' (by simp only [hΓ, hdown])
        (by simp only [hΓ, hdown])
  · have htle : F.depth ≤ F.top := by simp [BlockFrame.top]
    have hcell : ∀ (h' : F.Cell) (x : F.Site F.depth),
        enclosingCell (x + cellCentre F.depth h') = enclosingCell x + h' ∧
        cellOffset (x + cellCentre F.depth h') = cellOffset x := by
      intro h' x
      obtain ⟨hx, ho⟩ := (hS F hL hs).2.1 x
      have e : x + cellCentre F.depth h' =
          cellCentre F.depth (enclosingCell x + h') + siteOfCoords F.depth (cellOffset x) := by
        rw [cellCentre_add hs htle]
        nth_rewrite 1 [← hx]
        abel
      rw [e]
      exact (hS F hL hs).1 _ _ ho
    have hcross : ∀ (h' : F.Cell) (x : F.Site F.depth) (i : Fin 4),
        IsCrossingBond (x + cellCentre F.depth h', i) ↔ IsCrossingBond (x, i) := by
      intro h' x i
      rw [(hS F hL hs).2.2.1, (hS F hL hs).2.2.1, (hcell h' x).2]
    have htree : ∀ (h' : F.Cell) (x : F.Site F.depth) (i : Fin 4),
        IsAxialTreeBond (x + cellCentre F.depth h', i) ↔ IsAxialTreeBond (x, i) := by
      intro h' x i
      unfold IsAxialTreeBond
      simp only
      rw [hcross, (hcell h' x).2]
    have hchartS : ∀ (h' : F.Cell) (b : F.Site F.depth × Fin 4), b ∈ chordBonds (finiteCells F) →
        (b.1 + cellCentre F.depth h', b.2) ∈ chordBonds (finiteCells F) := by
      intro h' b hb
      unfold chordBonds at hb ⊢
      rw [Finset.mem_filter] at hb ⊢
      refine ⟨translate_mem_innerBonds hs htle h' hb.1, ?_⟩
      rw [htree]
      exact hb.2
    have hu : ∀ x : F.Site F.depth, x - cellCentre F.depth h = x + cellCentre F.depth (-h) := by
      intro x
      rw [cellCentre_neg hs htle, sub_eq_add_neg]
    have hfield : chartedField w' (translateField h V) =
        translateField (cellCentre F.depth h) (chartedField w V) := by
      have e1 : chartedField w' (translateField h V) =
          chartedField (fun x i => w (x - cellCentre F.depth h) i) (translateField h V) := by
        refine chartedField_congr hcover hL hs0 _ fun b hb => ?_
        have h3 : (b.1 - cellCentre F.depth h, b.2) ∈ chordBonds (finiteCells F) := by
          rw [hu]
          exact hchartS (-h) b hb
        have h4 := hw _ h3
        simp only [sub_add_cancel] at h4
        exact h4
      rw [e1]
      funext x i
      simp only [chartedField, translateField]
      have hx : x = (x - cellCentre F.depth h) + cellCentre F.depth h := by abel
      have hc1 : IsCrossingBond (x, i) ↔ IsCrossingBond (x - cellCentre F.depth h, i) := by
        conv_lhs => rw [hx]
        exact hcross h _ i
      have ht1 : IsAxialTreeBond (x, i) ↔ IsAxialTreeBond (x - cellCentre F.depth h, i) := by
        conv_lhs => rw [hx]
        exact htree h _ i
      by_cases hc' : IsCrossingBond (x - cellCentre F.depth h, i)
      · rw [if_pos (hc1.mpr hc'), if_pos hc']
        have e : enclosingCell x - h = enclosingCell (x - cellCentre F.depth h) := by
          have := (hcell h (x - cellCentre F.depth h)).1
          rw [← hx] at this
          rw [this]
          abel
        rw [e]
      · rw [if_neg (fun h' => hc' (hc1.mp h')), if_neg hc']
        by_cases ht : IsAxialTreeBond (x - cellCentre F.depth h, i)
        · rw [if_pos (ht1.mpr ht), if_pos ht]
        · rw [if_neg (fun h' => ht (ht1.mp h')), if_neg ht]
    have hadd : ∀ x : F.Site F.depth, x + cellCentre F.depth (-h) + cellCentre F.depth h = x := by
      intro x
      rw [cellCentre_neg hs htle]
      abel
    have hadd' : ∀ x : F.Site F.depth, x + cellCentre F.depth h + cellCentre F.depth (-h) = x := by
      intro x
      rw [cellCentre_neg hs htle]
      abel
    unfold cellEnergyShare
    rw [hfield]
    refine congrArg₂ (· + ·) ?_ (congrArg (fun u => a / 2 * u) ?_)
    · refine Finset.sum_bij' (fun y _ => y + cellCentre F.depth (-h)) (fun y _ => y + cellCentre F.depth h)
        ?_ ?_ ?_ ?_ ?_
      · intro y hy
        have h1 := (Finset.mem_filter.mp hy).2
        refine Finset.mem_filter.mpr ⟨hcov _, ?_⟩
        rw [(hcell _ _).1, h1]
        abel
      · intro y hy
        have h1 := (Finset.mem_filter.mp hy).2
        refine Finset.mem_filter.mpr ⟨hcov _, ?_⟩
        rw [(hcell _ _).1, h1]
      · intro y _
        exact hadd y
      · intro y _
        exact hadd' y
      · intro y _
        have h1 := hold.siteShare_translate (y + cellCentre F.depth (-h)) (cellCentre F.depth h)
        rw [hadd] at h1
        exact h1
    · have htop : translateField h V = translateField (cellCentre (F.depth + 1) h) V := by
        have := cellCentre_top hs h
        change translateField h V = translateField (cellCentre F.top h) V
        rw [this]
      have hct : (cellCentre (F.depth + 1) h : F.Cell) = h := cellCentre_top hs h
      have hctn : (cellCentre (F.depth + 1) (-h) : F.Cell) = -h := cellCentre_top hs (-h)
      rw [htop]
      refine Finset.sum_bij' (fun c' _ => (c'.1 + -h, c'.2)) (fun c' _ => (c'.1 + h, c'.2)) ?_ ?_ ?_ ?_ ?_
      · intro c' hc'
        have h1 := (Finset.mem_filter.mp hc').2
        refine Finset.mem_filter.mpr ⟨mem_innerBonds_top hs _, ?_⟩
        rcases h1 with h1 | h1
        · left
          change c'.1 + -h = Y
          rw [h1]
          abel
        · right
          change c'.1 + -h + unitStep F.top c'.2 = Y
          have : c'.1 + -h + unitStep F.top c'.2 = (c'.1 + unitStep F.top c'.2) + -h := by abel
          rw [this, h1]
          abel
      · intro c' hc'
        have h1 := (Finset.mem_filter.mp hc').2
        refine Finset.mem_filter.mpr ⟨mem_innerBonds_top hs _, ?_⟩
        rcases h1 with h1 | h1
        · left
          change c'.1 + h = Y + h
          rw [h1]
        · right
          change c'.1 + h + unitStep F.top c'.2 = Y + h
          have : c'.1 + h + unitStep F.top c'.2 = (c'.1 + unitStep F.top c'.2) + h := by abel
          rw [this, h1]
      · intro c' _
        simp
      · intro c' _
        simp
      · intro c' _
        have h1 := blockFit_translateField hLpos hs (j := F.depth) (by simp [BlockFrame.top]) h
          (chartedField w V) V (c'.1 + -h, c'.2)
        rw [hct] at h1
        simp only [neg_add_cancel_right] at h1
        rw [← h1, hct]
end ColdStepAtMirrorFrames
end YangMills.Construction
end
