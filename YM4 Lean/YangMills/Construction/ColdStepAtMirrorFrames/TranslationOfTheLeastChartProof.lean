import YangMills.Construction.ColdStepAtMirrorFrames.SitesOfABlock
import YangMills.Construction.ColdStepAtMirrorFrames.SumOfTheSharesProof
import YangMills.Construction.ColdStepAtMirrorFrames.TranslationOfTheLeastChart
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
namespace Translation
theorem period_top (i : Fin 4) : F.period F.top i = F.extent i := by simp [BlockFrame.period]
theorem mem_finiteCells (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell) : z ∈ finiteCells F := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CellShares.mem_finiteCells <;> assumption
theorem intCast_pow_mul_eq {j : ℕ} (i : Fin 4) (hj : j ≤ F.top) {p q : ℤ}
    (h : ((p : ℤ) : ZMod (F.period F.top i)) = ((q : ℤ) : ZMod (F.period F.top i))) :
    ((((F.blockSide : ℤ) ^ (F.top - j) * p : ℤ)) : ZMod (F.period j i)) = (((F.blockSide : ℤ) ^ (F.top - j) * q : ℤ) : ZMod (F.period j i)) := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h ⊢
  obtain ⟨w, hw⟩ := h
  refine ⟨w, ?_⟩
  have e1 : ((F.period j i : ℕ) : ℤ) = ((F.period F.top i : ℕ) : ℤ) * (F.blockSide : ℤ) ^ (F.top - j) := by
    simp only [BlockFrame.period, Nat.sub_self, pow_zero, mul_one]
    push_cast
    ring
  rw [e1]
  linear_combination ((F.blockSide : ℤ) ^ (F.top - j)) * hw
theorem intCast_siteCoords_top (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell) (i : Fin 4) :
    ((siteCoords z i : ℤ) : ZMod (F.period F.top i)) = z i := ZMod.intCast_zmod_cast (z i)
theorem cellCentre_add (hs : ∀ i, 2 ≤ F.extent i) {j : ℕ} (hj : j ≤ F.top) (z h : F.Cell) :
    (cellCentre j (z + h) : F.Site j) = cellCentre j z + cellCentre j h := by
  funext i
  simp only [cellCentre, siteOfCoords, Pi.add_apply]
  rw [← Int.cast_add, ← mul_add]
  apply intCast_pow_mul_eq i hj
  push_cast
  rw [intCast_siteCoords_top hs, intCast_siteCoords_top hs, intCast_siteCoords_top hs]
  rfl
theorem cellCentre_top (hs : ∀ i, 2 ≤ F.extent i) (h : F.Cell) : (cellCentre F.top h : F.Cell) = h := by
  funext i
  simp only [cellCentre, siteOfCoords, Nat.sub_self, pow_zero, one_mul]
  exact intCast_siteCoords_top hs h i
theorem period_neZero (hL : 0 < F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (j : ℕ) (i : Fin 4) : NeZero (F.period j i) := ⟨by
  simp only [BlockFrame.period]
  have h1 : 0 < F.extent i := by have := hs i; omega
  positivity⟩
theorem intCast_siteCoords (hL : 0 < F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) {j : ℕ} (y : F.Site j) (i : Fin 4) :
    ((siteCoords y i : ℤ) : ZMod (F.period j i)) = y i := by
  have := period_neZero hL hs j i
  exact ZMod.intCast_zmod_cast (y i)
theorem refineSite_add_cellCentre (hL : 0 < F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) {j : ℕ} (hj : j < F.top) (y : F.Site (j + 1)) (h : F.Cell) :
    (refineSite (y + cellCentre (j + 1) h) : F.Site j) = refineSite y + cellCentre j h := by
  funext i
  have hper : ((F.period j i : ℕ) : ℤ) = ((F.period (j + 1) i : ℕ) : ℤ) * (F.blockSide : ℤ) := by
    simp only [BlockFrame.period]
    have : F.top - j = (F.top - (j + 1)) + 1 := by omega
    rw [this, pow_succ]
    push_cast
    ring
  have hpow : (F.blockSide : ℤ) ^ (F.top - j) = (F.blockSide : ℤ) * (F.blockSide : ℤ) ^ (F.top - (j + 1)) := by
    have : F.top - j = (F.top - (j + 1)) + 1 := by omega
    rw [this, pow_succ]
    ring
  change (((F.blockSide : ℤ) * siteCoords (y + cellCentre (j + 1) h) i : ℤ) : ZMod (F.period j i)) =
    (((F.blockSide : ℤ) * siteCoords y i : ℤ) : ZMod (F.period j i)) + (((F.blockSide : ℤ) ^ (F.top - j) * siteCoords h i : ℤ) : ZMod (F.period j i))
  rw [← Int.cast_add, hpow, mul_assoc, ← mul_add]
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  have h1 : ((siteCoords (y + cellCentre (j + 1) h) i : ℤ) : ZMod (F.period (j + 1) i)) =
      ((siteCoords y i + (F.blockSide : ℤ) ^ (F.top - (j + 1)) * siteCoords h i : ℤ) : ZMod (F.period (j + 1) i)) := by
    rw [intCast_siteCoords hL hs]
    push_cast
    rw [intCast_siteCoords hL hs]
    simp [cellCentre, siteOfCoords]
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
  obtain ⟨w, hw⟩ := h1
  refine ⟨w, ?_⟩
  rw [hper]
  linear_combination ((F.blockSide : ℤ)) * hw
theorem cellCentre_neg (hs : ∀ i, 2 ≤ F.extent i) {j : ℕ} (hj : j ≤ F.top) (h : F.Cell) :
    (cellCentre j (-h) : F.Site j) = - cellCentre j h := by
  have h1 := cellCentre_add hs hj (-h) h
  have h0 : (cellCentre j (0 : F.Cell) : F.Site j) = 0 := by
    funext i
    simp [cellCentre, siteOfCoords, siteCoords]
  rw [neg_add_cancel, h0] at h1
  exact eq_neg_of_add_eq_zero_left h1.symm
theorem add_cellCentre_mem_sitesOfCells (hs : ∀ i, 2 ≤ F.extent i) {j : ℕ} (hj : j ≤ F.top) (h : F.Cell) {x : F.Site j}
    (hx : x ∈ sitesOfCells (finiteCells F) j) : x + cellCentre j h ∈ sitesOfCells (finiteCells F) j := by
  classical
  unfold sitesOfCells at hx ⊢
  rw [Finset.mem_biUnion] at hx ⊢
  obtain ⟨z, _, hz⟩ := hx
  rw [Finset.mem_image] at hz
  obtain ⟨o, ho, e⟩ := hz
  refine ⟨z + h, mem_finiteCells hs _, ?_⟩
  rw [Finset.mem_image]
  refine ⟨o, ho, ?_⟩
  rw [cellCentre_add hs hj, ← e]
  abel
theorem linkValue_translateField {j : ℕ} (u : F.Site j) (X : F.GaugeField j) (x : F.Site j) (st : PathStep) :
    linkValue (translateField u X) (x + u) st = linkValue X x st := by
  unfold linkValue translateField
  split_ifs
  · simp
  · have e : x + u - unitStep j st.1 - u = x - unitStep j st.1 := by abel
    rw [e]
theorem pathHolonomy_translateField {j : ℕ} (u : F.Site j) (X : F.GaugeField j) (x : F.Site j) (l : List PathStep) :
    pathHolonomy (translateField u X) (x + u) l = pathHolonomy X x l := by
  induction l generalizing x with
  | nil => rfl
  | cons st r ih =>
    simp only [pathHolonomy]
    have e : x + u + stepDisplacement j st = (x + stepDisplacement j st) + u := by abel
    rw [linkValue_translateField, e, ih]
theorem add_cellCentre_mem_innerBonds (hs : ∀ i, 2 ≤ F.extent i) {j : ℕ} (hj : j ≤ F.top) (h : F.Cell) {c : F.Site j × Fin 4}
    (hc : c ∈ innerBonds (finiteCells F) j) : (c.1 + cellCentre j h, c.2) ∈ innerBonds (finiteCells F) j := by
  classical
  unfold innerBonds at hc ⊢
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hc ⊢
  refine ⟨add_cellCentre_mem_sitesOfCells hs hj h hc.1, ?_⟩
  have e : c.1 + cellCentre j h + unitStep j c.2 = (c.1 + unitStep j c.2) + cellCentre j h := by abel
  rw [e]
  exact add_cellCentre_mem_sitesOfCells hs hj h hc.2
theorem add_cellCentre_mem_innerPlaquettes (hs : ∀ i, 2 ≤ F.extent i) (h : F.Cell) {p : F.Site 0 × Fin 4 × Fin 4}
    (hp : p ∈ innerPlaquettes (finiteCells F) 0) : (p.1 + cellCentre 0 h, p.2) ∈ innerPlaquettes (finiteCells F) 0 := by
  classical
  unfold innerPlaquettes at hp ⊢
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hp ⊢
  obtain ⟨h1, h2, h3⟩ := hp
  refine ⟨add_cellCentre_mem_sitesOfCells hs (Nat.zero_le _) h h1, h2, ?_⟩
  intro x hx
  unfold plaquetteCorners at hx h3
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  have hc : ∀ y ∈ ({p.1, p.1 + unitStep 0 p.2.1, p.1 + unitStep 0 p.2.2, p.1 + unitStep 0 p.2.1 + unitStep 0 p.2.2} :
      Finset (F.Site 0)), y + cellCentre 0 h ∈ sitesOfCells (finiteCells F) 0 := fun y hy =>
    add_cellCentre_mem_sitesOfCells hs (Nat.zero_le _) h (h3 hy)
  rcases hx with rfl | rfl | rfl | rfl
  · exact hc _ (by simp)
  · have e : p.1 + cellCentre 0 h + unitStep 0 p.2.1 = (p.1 + unitStep 0 p.2.1) + cellCentre 0 h := by abel
    rw [e]
    exact hc _ (by simp)
  · have e : p.1 + cellCentre 0 h + unitStep 0 p.2.2 = (p.1 + unitStep 0 p.2.2) + cellCentre 0 h := by abel
    rw [e]
    exact hc _ (by simp)
  · have e : p.1 + cellCentre 0 h + unitStep 0 p.2.1 + unitStep 0 p.2.2 =
        (p.1 + unitStep 0 p.2.1 + unitStep 0 p.2.2) + cellCentre 0 h := by abel
    rw [e]
    exact hc _ (by simp)
theorem blockFit_translateField (hL : 0 < F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) {j : ℕ} (hj : j < F.top) (h : F.Cell) (W : F.GaugeField j)
    (V : F.GaugeField (j + 1)) (c : F.Site (j + 1) × Fin 4) :
    blockFit (translateField (cellCentre j h) W) (translateField (cellCentre (j + 1) h) V) (c.1 + cellCentre (j + 1) h, c.2) = blockFit W V c := by
  have hm : contourAverage (translateField (cellCentre j h) W) (c.1 + cellCentre (j + 1) h, c.2) = contourAverage W c := by
    unfold contourAverage
    simp only
    rw [refineSite_add_cellCentre hL hs hj]
    simp only [pathHolonomy_translateField]
  unfold blockFit
  rw [hm]
  simp [translateField]
def translateEquiv {j : ℕ} (u : F.Site j) : F.GaugeField j ≃ F.GaugeField j where
  toFun := translateField u
  invFun := translateField (-u)
  left_inv X := by
    funext x i
    simp [translateField]
  right_inv X := by
    funext x i
    simp [translateField]
end Translation
open Translation in
theorem minimalAction_translate : MinimalActionTranslationInvariant := by
  classical
  intro F a h j hL hs
  induction j with
  | zero =>
    intro _ X
    change wilsonAction (finiteCells F) (translateField (cellCentre 0 h) X) = wilsonAction (finiteCells F) X
    unfold wilsonAction
    refine Finset.sum_bij' (fun p _ => (p.1 + cellCentre 0 (-h), p.2)) (fun p _ => (p.1 + cellCentre 0 h, p.2))
      (fun p hp => add_cellCentre_mem_innerPlaquettes hs _ hp) (fun p hp => add_cellCentre_mem_innerPlaquettes hs _ hp) ?_ ?_ ?_
    · intro p _
      rw [cellCentre_neg hs (Nat.zero_le _)]
      simp
    · intro p _
      rw [cellCentre_neg hs (Nat.zero_le _)]
      simp
    · intro p _
      have e : plaquetteHolonomy (translateField (cellCentre 0 h) X) p =
          plaquetteHolonomy X (p.1 + cellCentre 0 (-h), p.2) := by
        rw [cellCentre_neg hs (Nat.zero_le _)]
        unfold plaquetteHolonomy
        have e2 : p.1 = (p.1 + -cellCentre 0 h) + cellCentre 0 h := by abel
        conv_lhs => rw [e2]
        rw [pathHolonomy_translateField]
      rw [e]
  | succ j ih =>
    intro hj X
    have hjn : j < F.top := hj
    change (⨅ W : F.GaugeField j, (minimalAction a (finiteCells F) j W + a * ∑ c ∈ innerBonds (finiteCells F) (j + 1),
        blockFit W (translateField (cellCentre (j + 1) h) X) c)) =
      ⨅ W : F.GaugeField j, (minimalAction a (finiteCells F) j W + a * ∑ c ∈ innerBonds (finiteCells F) (j + 1), blockFit W X c)
    rw [← (translateEquiv (cellCentre j h)).iInf_comp]
    refine iInf_congr fun W => ?_
    change minimalAction a (finiteCells F) j (translateField (cellCentre j h) W) + a * ∑ c ∈ innerBonds (finiteCells F) (j + 1),
      blockFit (translateField (cellCentre j h) W) (translateField (cellCentre (j + 1) h) X) c = _
    rw [ih (by omega)]
    congr 2
    refine Finset.sum_bij' (fun c _ => (c.1 + cellCentre (j + 1) (-h), c.2))
      (fun c _ => (c.1 + cellCentre (j + 1) h, c.2))
      (fun c hc => add_cellCentre_mem_innerBonds hs hj _ hc) (fun c hc => add_cellCentre_mem_innerBonds hs hj _ hc) ?_ ?_ ?_
    · intro c _
      rw [cellCentre_neg hs hj]
      simp
    · intro c _
      rw [cellCentre_neg hs hj]
      simp
    · intro c _
      have := blockFit_translateField hL hs hjn h W X (c.1 + cellCentre (j + 1) (-h), c.2)
      rw [← this, cellCentre_neg hs hj]
      simp
open Translation in
theorem siteTranslationByCell_of_decomposition (hS : SiteDecomposition) : SiteTranslationByCell := by
  intro F h' x hL hs
  obtain ⟨hx, ho⟩ := (hS F hL hs).2.1 x
  have e : x + cellCentre F.depth h' = cellCentre F.depth (enclosingCell x + h') + siteOfCoords F.depth (cellOffset x) := by
    rw [cellCentre_add hs (by simp [BlockFrame.top])]
    nth_rewrite 1 [← hx]
    abel
  rw [e]
  exact (hS F hL hs).1 _ _ ho
set_option maxHeartbeats 1000000 in
open Translation in
theorem minimizingChartTranslation_of (hS : SiteDecomposition) (hcar : MinimalActionTranslationInvariant) :
    MinimizingChartTranslation := by
  classical
  intro F a ρ V w h hL hs hw
  have hLpos : 0 < F.blockSide := by
    obtain ⟨k, hk⟩ := hL
    omega
  have htle : F.depth ≤ F.top := by simp [BlockFrame.top]
  obtain ⟨hz, hr, hmin⟩ := hw
  have hcell : ∀ (h' : F.Cell) (x : F.Site F.depth), enclosingCell (x + cellCentre F.depth h') = enclosingCell x + h' ∧
      cellOffset (x + cellCentre F.depth h') = cellOffset x := by
    intro h' x
    obtain ⟨hx, ho⟩ := (hS F hL hs).2.1 x
    have e : x + cellCentre F.depth h' = cellCentre F.depth (enclosingCell x + h') + siteOfCoords F.depth (cellOffset x) := by
      rw [cellCentre_add hs htle]
      nth_rewrite 1 [← hx]
      abel
    rw [e]
    exact (hS F hL hs).1 _ _ ho
  have hcross : ∀ (h' : F.Cell) (x : F.Site F.depth) (i : Fin 4), IsCrossingBond (x + cellCentre F.depth h', i) ↔ IsCrossingBond (x, i) := by
    intro h' x i
    rw [(hS F hL hs).2.2.1, (hS F hL hs).2.2.1, (hcell h' x).2]
  have htree : ∀ (h' : F.Cell) (x : F.Site F.depth) (i : Fin 4), IsAxialTreeBond (x + cellCentre F.depth h', i) ↔ IsAxialTreeBond (x, i) := by
    intro h' x i
    unfold IsAxialTreeBond
    simp only
    rw [hcross, (hcell h' x).2]
  have hchartS : ∀ (h' : F.Cell) (b : F.Site F.depth × Fin 4), b ∈ chordBonds (finiteCells F) →
      (b.1 + cellCentre F.depth h', b.2) ∈ chordBonds (finiteCells F) := by
    intro h' b hb
    unfold chordBonds at hb ⊢
    rw [Finset.mem_filter] at hb ⊢
    refine ⟨add_cellCentre_mem_innerBonds hs htle h' hb.1, ?_⟩
    rw [htree]
    exact hb.2
  have hu : ∀ x : F.Site F.depth, x - cellCentre F.depth h = x + cellCentre F.depth (-h) := by
    intro x
    rw [cellCentre_neg hs htle, sub_eq_add_neg]
  have hfield : chartedField (fun x i => w (x - cellCentre F.depth h) i) (translateField h V) =
      translateField (cellCentre F.depth h) (chartedField w V) := by
    funext x i
    simp only [chartedField, translateField]
    have hx : x = (x - cellCentre F.depth h) + cellCentre F.depth h := by abel
    have hc1 : IsCrossingBond (x, i) ↔ IsCrossingBond (x - cellCentre F.depth h, i) := by
      conv_lhs => rw [hx]
      exact hcross h _ i
    have ht1 : IsAxialTreeBond (x, i) ↔ IsAxialTreeBond (x - cellCentre F.depth h, i) := by
      conv_lhs => rw [hx]
      exact htree h _ i
    by_cases hc : IsCrossingBond (x - cellCentre F.depth h, i)
    · rw [if_pos (hc1.mpr hc), if_pos hc]
      have e : enclosingCell x - h = enclosingCell (x - cellCentre F.depth h) := by
        have := (hcell h (x - cellCentre F.depth h)).1
        rw [← hx] at this
        rw [this]
        abel
      rw [e]
    · rw [if_neg (fun h' => hc (hc1.mp h')), if_neg hc]
      by_cases ht : IsAxialTreeBond (x - cellCentre F.depth h, i)
      · rw [if_pos (ht1.mpr ht), if_pos ht]
      · rw [if_neg (fun h' => ht (ht1.mp h')), if_neg ht]
  have henergy : ∀ W : F.GaugeField F.depth, blockEnergy a (finiteCells F) F.depth (translateField (cellCentre F.depth h) W) (translateField h V) =
      blockEnergy a (finiteCells F) F.depth W V := by
    intro W
    unfold blockEnergy
    rw [hcar F a h F.depth hLpos hs htle]
    congr 2
    have htop : translateField h V = translateField (cellCentre (F.depth + 1) h) V := by
      have := cellCentre_top hs h
      change translateField h V = translateField (cellCentre F.top h) V
      rw [this]
    rw [htop]
    refine Finset.sum_bij' (fun c _ => (c.1 + cellCentre (F.depth + 1) (-h), c.2))
      (fun c _ => (c.1 + cellCentre (F.depth + 1) h, c.2))
      (fun c hc => add_cellCentre_mem_innerBonds hs le_rfl _ hc) (fun c hc => add_cellCentre_mem_innerBonds hs le_rfl _ hc) ?_ ?_ ?_
    · intro c _
      rw [cellCentre_neg hs le_rfl]
      simp
    · intro c _
      rw [cellCentre_neg hs le_rfl]
      simp
    · intro c _
      have := blockFit_translateField hLpos hs (j := F.depth) (by simp [BlockFrame.top]) h W V (c.1 + cellCentre (F.depth + 1) (-h), c.2)
      rw [← this, cellCentre_neg hs le_rfl]
      simp
  refine ⟨fun b hb => ?_, fun b hb => ?_, fun W' => ?_⟩
  · have hb' : (b.1 - cellCentre F.depth h, b.2) ∉ chordBonds (finiteCells F) := by
      intro hcon
      apply hb
      have := hchartS h _ hcon
      simpa using this
    exact hz _ hb'
  · have h3 : (b.1 - cellCentre F.depth h, b.2) ∈ chordBonds (finiteCells F) := by
      rw [hu]
      exact hchartS (-h) b hb
    exact hr (b.1 - cellCentre F.depth h, b.2) h3
  · rw [hfield, henergy]
    have e := henergy ((translateEquiv (cellCentre F.depth h)).symm W')
    have e2 : translateField (cellCentre F.depth h) ((translateEquiv (cellCentre F.depth h)).symm W') = W' :=
      (translateEquiv (cellCentre F.depth h)).apply_symm_apply W'
    rw [e2] at e
    rw [e]
    exact hmin _
theorem translationOfMinimizingChart_holds (hS : SiteDecomposition) : TranslationOfMinimizingChart :=
  ⟨minimalAction_translate, siteTranslationByCell_of_decomposition hS, minimizingChartTranslation_of hS minimalAction_translate⟩
end YangMills.Construction.ColdStepAtMirrorFrames
end
