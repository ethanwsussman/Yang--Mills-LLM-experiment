import YangMills.Construction.ClusterExpansionOfAStep.ColdIntegralIsTheMarkedIntegralOfAllBlocksProof
import YangMills.Construction.ClusterExpansionOfAStep.ShareOfAChainSplitsProof
import YangMills.Construction.ClusterExpansionOfAStep.ShareOfALevelIsTheShareBelow
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ShareEvaluation
open BlockAverages ColdStepAtMirrorFrames RenormalizationStepParameters StepCosts
open TorusFields (TorusSite TorusField readAtLevel torusFrame cellsOfSites plaquettesIn plaquetteVertices
  plaquetteEnergy)
theorem mem_finiteCells_of_pos {H : BlockFrame} (hs : ∀ i, 0 < H.extent i) (z : H.Cell) :
    z ∈ finiteCells H := by apply _root_.YangMills.Construction.FrameTorusAction.mem_finiteCells <;> assumption
theorem mem_sitesOfCells_finiteCells (H : BlockFrame) (hL : Odd H.blockSide) (hs : ∀ i, 0 < H.extent i)
    (j : ℕ) (hj : j ≤ H.top) (x : H.Site j) : x ∈ sitesOfCells (finiteCells H) j := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.mem_sitesOfCells_finiteCells <;> assumption
section Carry
theorem zmod_cast_cast_eq (P Q : ℕ) (h : P = Q) (a : ZMod P) :
    ((((a.cast : ℤ) : ZMod Q)).cast : ℤ) = (a.cast : ℤ) := by apply _root_.YangMills.Construction.FrameTorusAction.cast_intCast_cast <;> assumption
theorem zmod_cast_roundtrip (P Q : ℕ) (h : P = Q) (a : ZMod P) :
    (((((a.cast : ℤ) : ZMod Q)).cast : ℤ) : ZMod P) = a := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LevelShare.cast_cast_of_eq <;> assumption
theorem zmod_cast_intCast (P Q : ℕ) (h : P = Q) (z : ℤ) :
    ((((z : ZMod P)).cast : ℤ) : ZMod Q) = (z : ZMod Q) := by apply _root_.YangMills.Construction.FrameTorusAction.intCast_cast_intCast <;> assumption
variable (L k n : ℕ)
abbrev deepFrame : BlockFrame := torusFrame L (k + 1) n
abbrev wideFrame : BlockFrame := torusFrame L k (n * L)
variable {L k n}
theorem wideFrame_period_eq {j : ℕ} (hj : j ≤ k + 1) (i : Fin 4) :
    (wideFrame L k n).period j i = (deepFrame L k n).period j i := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LevelShare.period_upper_eq <;> assumption
def toDeep (j : ℕ) (x : (wideFrame L k n).Site j) : (deepFrame L k n).Site j := siteOfCoords j (siteCoords x)
def toWide (j : ℕ) (x : (deepFrame L k n).Site j) : (wideFrame L k n).Site j := siteOfCoords j (siteCoords x)
theorem toDeep_toWide {j : ℕ} (hj : j ≤ k + 1) (x : (deepFrame L k n).Site j) : toDeep j (toWide j x) = x := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LevelShare.toLower_toUpper <;> assumption
theorem toWide_toDeep {j : ℕ} (hj : j ≤ k + 1) (x : (wideFrame L k n).Site j) : toWide j (toDeep j x) = x := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LevelShare.toUpper_toLower <;> assumption
theorem siteCoords_toDeep {j : ℕ} (hj : j ≤ k + 1) (x : (wideFrame L k n).Site j) :
    siteCoords (toDeep j x) = siteCoords x := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LevelShare.siteCoords_toLower <;> assumption
theorem toDeep_add {j : ℕ} (hj : j ≤ k + 1) (x y : (wideFrame L k n).Site j) :
    toDeep j (x + y) = toDeep j x + toDeep j y := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LevelShare.toLower_add <;> assumption
theorem toDeep_siteOfCoords {j : ℕ} (hj : j ≤ k + 1) (z : Fin 4 → ℤ) :
    toDeep j (siteOfCoords (F := wideFrame L k n) j z) = siteOfCoords j z := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LevelShare.toLower_siteOfCoords <;> assumption
theorem toDeep_unitStep {j : ℕ} (hj : j ≤ k + 1) (i : Fin 4) :
    toDeep j (unitStep (F := wideFrame L k n) j i) = unitStep j i := toDeep_siteOfCoords hj _
def liftField {j : ℕ} (X : (deepFrame L k n).GaugeField j) : (wideFrame L k n).GaugeField j :=
  fun s i => X (toDeep j s) i
def lowerField {j : ℕ} (X : (wideFrame L k n).GaugeField j) : (deepFrame L k n).GaugeField j :=
  fun s i => X (toWide j s) i
theorem pathHolonomy_liftField {j : ℕ} (hj : j ≤ k + 1) (X : (deepFrame L k n).GaugeField j)
    (x : (wideFrame L k n).Site j) (l : List PathStep) :
    pathHolonomy (liftField X) x l = pathHolonomy X (toDeep j x) l := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LevelShare.pathHolonomy_liftField <;> assumption
theorem plaquetteHolonomy_liftField {j : ℕ} (hj : j ≤ k + 1) (X : (deepFrame L k n).GaugeField j)
    (p : (wideFrame L k n).Site j × Fin 4 × Fin 4) :
    plaquetteHolonomy (liftField X) p = plaquetteHolonomy X (toDeep j p.1, p.2) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LevelShare.plaquetteHolonomy_liftField <;> assumption
theorem contourAverage_liftField {j : ℕ} (hj : j + 1 ≤ k + 1) (X : (deepFrame L k n).GaugeField j)
    (c : (wideFrame L k n).Site (j + 1) × Fin 4) :
    _root_.YangMills.Construction.BlockAverages.contourAverage (j := j) (liftField X) c = contourAverage (j := j) X (toDeep (j + 1) c.1, c.2) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LevelShare.contourAverage_liftField <;> assumption
theorem blockFit_liftField {j : ℕ} (hj : j + 1 ≤ k + 1) (X : (deepFrame L k n).GaugeField j)
    (X' : (deepFrame L k n).GaugeField (j + 1)) (c : (wideFrame L k n).Site (j + 1) × Fin 4) :
    blockFit (j := j) (liftField X) (liftField X') c = blockFit (j := j) X X' (toDeep (j + 1) c.1, c.2) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LevelShare.blockFit_liftField <;> assumption
end Carry
section Chains
variable {L k n : ℕ}
def liftChain (X : (deepFrame L k n).FieldChain) : (wideFrame L k n).FieldChain := fun _ => liftField (X _)
def lowerChain (Z : (wideFrame L k n).FieldChain) : (deepFrame L k n).FieldChain := fun _ => lowerField (Z _)
theorem liftChain_lowerChain (Z : (wideFrame L k n).FieldChain) {j : ℕ} (hj : j ≤ k + 1) :
    liftChain (lowerChain Z) j = Z j := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LevelShare.liftChain_lowerChain <;> assumption
section Whole
variable (hL : Odd L) (hn : 0 < n)
include hL hn
theorem deepFrame_extent_pos : ∀ i, 0 < (deepFrame L k n).extent i := fun _ => hn
theorem wideFrame_extent_pos : ∀ i, 0 < (wideFrame L k n).extent i := fun _ => Nat.mul_pos hn hL.pos
theorem sum_innerPlaquettes_toDeep (g : (deepFrame L k n).Site 0 × Fin 4 × Fin 4 → ℝ) :
    ∑ p ∈ innerPlaquettes (finiteCells (wideFrame L k n)) 0, g (toDeep 0 p.1, p.2) =
      ∑ p ∈ innerPlaquettes (finiteCells (deepFrame L k n)) 0, g p := by
  have hA := mem_sitesOfCells_finiteCells (deepFrame L k n) hL (deepFrame_extent_pos hL hn) 0 (by simp)
  have hB := mem_sitesOfCells_finiteCells (wideFrame L k n) hL (wideFrame_extent_pos hL hn) 0 (by simp)
  have h0 : 0 ≤ k + 1 := by omega
  apply Finset.sum_nbij (fun p => (toDeep 0 p.1, p.2))
  · intro p hp
    have h1 := (Finset.mem_filter.1 hp).2.1
    unfold innerPlaquettes
    refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hA _, by simp⟩, h1, fun x _ => hA x⟩
  · rintro ⟨p, μ, ν⟩ _ ⟨p', μ', ν'⟩ _ h
    simp only [Prod.mk.injEq] at h
    have := congrArg (toWide 0) h.1
    rw [toWide_toDeep h0, toWide_toDeep h0] at this
    simp [this, h.2.1, h.2.2]
  · rintro ⟨p, μ, ν⟩ hp
    have h1 := (Finset.mem_filter.1 (Finset.mem_coe.1 hp)).2.1
    refine ⟨(toWide 0 p, μ, ν), ?_, ?_⟩
    · unfold innerPlaquettes
      exact Finset.mem_coe.2 (Finset.mem_filter.2
        ⟨Finset.mem_product.2 ⟨hB _, by simp⟩, h1, fun x _ => hB x⟩)
    · simp [toDeep_toWide h0]
  · intro p _
    rfl
theorem sum_innerBonds_toDeep {j : ℕ} (hj : j ≤ k + 1) (g : (deepFrame L k n).Site j × Fin 4 → ℝ) :
    ∑ c ∈ innerBonds (finiteCells (wideFrame L k n)) j, g (toDeep j c.1, c.2) =
      ∑ c ∈ innerBonds (finiteCells (deepFrame L k n)) j, g c := by
  have hA := mem_sitesOfCells_finiteCells (deepFrame L k n) hL (deepFrame_extent_pos hL hn) j
    (by show j ≤ k + 1 + 1; omega)
  have hB := mem_sitesOfCells_finiteCells (wideFrame L k n) hL (wideFrame_extent_pos hL hn) j hj
  apply Finset.sum_nbij (fun c => (toDeep j c.1, c.2))
  · intro c _
    unfold innerBonds
    exact Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hA _, by simp⟩, hA _⟩
  · rintro ⟨c, i⟩ _ ⟨c', i'⟩ _ h
    simp only [Prod.mk.injEq] at h
    have := congrArg (toWide j) h.1
    rw [toWide_toDeep hj, toWide_toDeep hj] at this
    simp [this, h.2]
  · rintro ⟨c, i⟩ _
    refine ⟨(toWide j c, i), ?_, ?_⟩
    · unfold innerBonds
      exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hB _, by simp⟩, hB _⟩)
    · simp [toDeep_toWide hj]
  · intro c _
    rfl
theorem chainAction_liftChain (a : ℝ) (X : (deepFrame L k n).FieldChain) :
    chainAction a (finiteCells (wideFrame L k n)) (liftChain X) =
      chainActionBelow a (finiteCells (deepFrame L k n)) X := by
  have a1 : ∑ p ∈ innerPlaquettes (finiteCells (wideFrame L k n)) 0,
      (1 - ((plaquetteHolonomy (liftChain X 0) p : UnitQuaternion) : ℍ[ℝ]).re) =
      ∑ p ∈ innerPlaquettes (finiteCells (deepFrame L k n)) 0,
        (1 - ((plaquetteHolonomy (X 0) p : UnitQuaternion) : ℍ[ℝ]).re) := by
    rw [← sum_innerPlaquettes_toDeep hL hn]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [show liftChain X 0 = liftField (X 0) from rfl, plaquetteHolonomy_liftField (by omega)]
  have a2 : ∀ j ∈ Finset.range (k + 1), ∑ c ∈ innerBonds (finiteCells (wideFrame L k n)) (j + 1),
      blockFit (j := j) (liftChain X j) (liftChain X (j + 1)) c =
      ∑ c ∈ innerBonds (finiteCells (deepFrame L k n)) (j + 1), blockFit (j := j) (X j) (X (j + 1)) c := by
    intro j hj
    have hj' : j + 1 ≤ k + 1 := Finset.mem_range.1 hj
    rw [← sum_innerBonds_toDeep hL hn hj']
    refine Finset.sum_congr rfl fun c _ => ?_
    exact blockFit_liftField hj' _ _ c
  show ∑ p ∈ innerPlaquettes (finiteCells (wideFrame L k n)) 0,
      (1 - ((plaquetteHolonomy (liftChain X 0) p : UnitQuaternion) : ℍ[ℝ]).re) +
    a * ∑ j ∈ Finset.range (k + 1), ∑ c ∈ innerBonds (finiteCells (wideFrame L k n)) (j + 1),
      blockFit (j := j) (liftChain X j) (liftChain X (j + 1)) c = _
  rw [a1, Finset.sum_congr rfl a2]
  rfl
theorem chainAction_congr (a : ℝ) (Z Z' : (wideFrame L k n).FieldChain) (h : ∀ j, j ≤ k + 1 → Z j = Z' j) :
    chainAction a (finiteCells (wideFrame L k n)) Z = chainAction a (finiteCells (wideFrame L k n)) Z' := by
  have a2 : ∀ j ∈ Finset.range (k + 1), ∑ c ∈ innerBonds (finiteCells (wideFrame L k n)) (j + 1),
      blockFit (j := j) (Z j) (Z (j + 1)) c =
      ∑ c ∈ innerBonds (finiteCells (wideFrame L k n)) (j + 1), blockFit (j := j) (Z' j) (Z' (j + 1)) c := by
    intro j hj
    have hj' : j + 1 ≤ k + 1 := Finset.mem_range.1 hj
    rw [h j (by omega), h (j + 1) hj']
  show wilsonAction (finiteCells (wideFrame L k n)) (Z 0) +
    a * ∑ j ∈ Finset.range (k + 1), ∑ c ∈ innerBonds (finiteCells (wideFrame L k n)) (j + 1),
      blockFit (j := j) (Z j) (Z (j + 1)) c = _
  rw [Finset.sum_congr rfl a2, h 0 (by omega)]
  rfl
theorem chainActionBelow_lowerChain (a : ℝ) (Z : (wideFrame L k n).FieldChain) :
    chainActionBelow a (finiteCells (deepFrame L k n)) (lowerChain Z) =
      chainAction a (finiteCells (wideFrame L k n)) Z := by
  rw [← chainAction_liftChain hL hn]
  exact chainAction_congr hL hn a _ _ fun j hj => liftChain_lowerChain Z hj
end Whole
theorem enclosingCell_eq_toWide_iff {j : ℕ} (hj : j ≤ k + 1) (x : (wideFrame L k n).Site j)
    (y : (deepFrame L k n).Site (k + 1)) :
    (enclosingCell x : (wideFrame L k n).Cell) = toWide (k + 1) y ↔
      ancestorSite (F := deepFrame L k n) (k + 1) (toDeep j x) = y := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LevelShare.enclosingCell_eq_toUpper_iff <;> assumption
end Chains
section Shares
variable {L k n : ℕ}
theorem mem_plaquetteCorners {H : BlockFrame} {j : ℕ} (q : H.Site j × Fin 4 × Fin 4) (x : H.Site j) :
    x ∈ plaquetteCorners q ↔ x = q.1 ∨ x = q.1 + unitStep j q.2.1 ∨ x = q.1 + unitStep j q.2.2 ∨
      x = q.1 + unitStep j q.2.1 + unitStep j q.2.2 := by
  simp [plaquetteCorners]
open Classical in
theorem sum_plaquetteCorners_weights (p : (wideFrame L k n).Site 0 × Fin 4 × Fin 4)
    (y : (deepFrame L k n).Site (k + 1)) :
    (∑ x ∈ plaquetteCorners p,
        if (enclosingCell x : (wideFrame L k n).Cell) = toWide (k + 1) y then (1 / 4 : ℝ) else 0) =
      ∑ x ∈ plaquetteCorners ((toDeep 0 p.1, p.2) : (deepFrame L k n).Site 0 × Fin 4 × Fin 4),
        if ancestorSite (F := deepFrame L k n) (k + 1) x = y then (1 / 4 : ℝ) else 0 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LevelShare.cornerWeights_toLower <;> assumption
open Classical in
theorem cellShare_liftChain (hL : Odd L) (hn : 0 < n) (a : ℝ) (X : (deepFrame L k n).FieldChain)
    (y : (deepFrame L k n).Site (k + 1)) :
    cellShare a (finiteCells (wideFrame L k n)) (toWide (k + 1) y) (liftChain X) =
      chainSiteShare a (finiteCells (deepFrame L k n)) y X := by
  have a1 : ∑ p ∈ innerPlaquettes (finiteCells (wideFrame L k n)) 0,
      (∑ x ∈ plaquetteCorners p,
        if (enclosingCell x : (wideFrame L k n).Cell) = toWide (k + 1) y then (1 / 4 : ℝ) else 0) *
        (1 - ((plaquetteHolonomy (liftChain X 0) p : UnitQuaternion) : ℍ[ℝ]).re) =
      ∑ p ∈ innerPlaquettes (finiteCells (deepFrame L k n)) 0,
        (∑ x ∈ plaquetteCorners p,
          if ancestorSite (F := deepFrame L k n) (k + 1) x = y then (1 / 4 : ℝ) else 0) *
          (1 - ((plaquetteHolonomy (X 0) p : UnitQuaternion) : ℍ[ℝ]).re) := by
    rw [← sum_innerPlaquettes_toDeep hL hn]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [sum_plaquetteCorners_weights, show liftChain X 0 = liftField (X 0) from rfl,
      plaquetteHolonomy_liftField (by omega)]
  have a2 : ∀ j ∈ Finset.range (k + 1), ∑ c ∈ innerBonds (finiteCells (wideFrame L k n)) (j + 1),
      ((if (enclosingCell c.1 : (wideFrame L k n).Cell) = toWide (k + 1) y then (1 / 2 : ℝ) else 0) +
        (if (enclosingCell (c.1 + unitStep (j + 1) c.2) : (wideFrame L k n).Cell) = toWide (k + 1) y
          then (1 / 2 : ℝ) else 0)) *
        blockFit (j := j) (liftChain X j) (liftChain X (j + 1)) c =
      ∑ c ∈ innerBonds (finiteCells (deepFrame L k n)) (j + 1),
        ((if ancestorSite (F := deepFrame L k n) (k + 1) c.1 = y then (1 / 2 : ℝ) else 0) +
          (if ancestorSite (F := deepFrame L k n) (k + 1) (c.1 + unitStep (j + 1) c.2) = y
            then (1 / 2 : ℝ) else 0)) *
          blockFit (j := j) (X j) (X (j + 1)) c := by
    intro j hj
    have hj' : j + 1 ≤ k + 1 := Finset.mem_range.1 hj
    rw [← sum_innerBonds_toDeep hL hn hj']
    refine Finset.sum_congr rfl fun c _ => ?_
    have e1 := enclosingCell_eq_toWide_iff hj' c.1 y
    have e2 := enclosingCell_eq_toWide_iff hj' (c.1 + unitStep (j + 1) c.2) y
    rw [toDeep_add hj', toDeep_unitStep hj'] at e2
    rw [if_congr e1 rfl rfl, if_congr e2 rfl rfl]
    congr 1
    exact blockFit_liftField hj' _ _ c
  unfold cellShare chainSiteShare
  convert congrArg₂ (· + ·) a1 (congrArg (a * ·) (Finset.sum_congr rfl a2)) using 1
  all_goals congr!
end Shares
section Level
theorem cellsOfSites_univ {H : BlockFrame} (hs : ∀ i, 0 < H.extent i) {m : ℕ} [NeZero m]
    (hm : ∀ i, H.period H.top i = m) :
    cellsOfSites H (Finset.univ : Finset (TorusSite m)) = finiteCells H := by
  ext z
  constructor
  · intro _
    exact _root_.YangMills.Construction.ShareEvaluation.mem_finiteCells_of_pos hs z
  · intro _
    refine Finset.mem_image.2 ⟨fun i => (((siteCoords z i : ℤ)) : ZMod m), Finset.mem_univ _, ?_⟩
    funext i
    exact zmod_cast_roundtrip _ _ (hm i) (z i)
end Level
section Final
section Helpers
variable {H : BlockFrame} {m : ℕ}
theorem toTorusSite_torusSiteInFrame (j : ℕ) (hm : ∀ i, H.period j i = m) (x : TorusSite m) :
    TorusLumps.toTorusSite m (torusSiteInFrame H j x) = x := by apply _root_.YangMills.Construction.TorusLevels.toTorusSite_torusSiteInFrame <;> assumption
theorem torusSiteInFrame_toTorusSite (j : ℕ) (hm : ∀ i, H.period j i = m) (y : H.Site j) :
    torusSiteInFrame H j (TorusLumps.toTorusSite m y) = y := by apply _root_.YangMills.Construction.TorusLevels.torusSiteInFrame_toTorusSite <;> assumption
theorem torusSiteInFrame_add (j : ℕ) (hm : ∀ i, H.period j i = m) (x y : TorusSite m) :
    torusSiteInFrame H j (x + y) = torusSiteInFrame H j x + torusSiteInFrame H j y := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.torusSiteInFrame_add <;> assumption
theorem torusSiteInFrame_unitStep (j : ℕ) (hm : ∀ i, H.period j i = m) (i : Fin 4) :
    torusSiteInFrame H j (TorusFields.unitStep m i) = unitStep j i := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.torusSiteInFrame_unitStep <;> assumption
theorem torusSiteInFrame_neg (j : ℕ) (hm : ∀ i, H.period j i = m) (x : TorusSite m) :
    torusSiteInFrame H j (-x) = - torusSiteInFrame H j x := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.torusSiteInFrame_neg <;> assumption
theorem torusSiteInFrame_sub (j : ℕ) (hm : ∀ i, H.period j i = m) (x y : TorusSite m) :
    torusSiteInFrame H j (x - y) = torusSiteInFrame H j x - torusSiteInFrame H j y := by
  rw [sub_eq_add_neg, torusSiteInFrame_add j hm, torusSiteInFrame_neg j hm, sub_eq_add_neg]
def torusPathHolonomy (W : TorusField m) : TorusSite m → List PathStep → UnitQuaternion
  | _, [] => 1
  | x, st :: r =>
    (if st.2 then W x st.1 else (W (x - TorusFields.unitStep m st.1) st.1)⁻¹) *
      torusPathHolonomy W (x + (if st.2 then TorusFields.unitStep m st.1 else - TorusFields.unitStep m st.1)) r
theorem readAtLevel_torusSiteInFrame (j : ℕ) (hm : ∀ i, H.period j i = m) (W : TorusField m)
    (x : TorusSite m) (i : Fin 4) :
    readAtLevel H j W (torusSiteInFrame H j x) i = W x i := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.readAtLevel_torusSiteInFrame <;> assumption
theorem pathHolonomy_readAtLevel (j : ℕ) (hm : ∀ i, H.period j i = m) (W : TorusField m) (x : TorusSite m)
    (l : List PathStep) :
    pathHolonomy (readAtLevel H j W) (torusSiteInFrame H j x) l = torusPathHolonomy W x l := by
  induction l generalizing x with
  | nil => rfl
  | cons st r ih =>
    have hv : stepDisplacement j st + torusSiteInFrame H j x =
        torusSiteInFrame H j (x + (if st.2 then TorusFields.unitStep m st.1 else - TorusFields.unitStep m st.1)) := by
      rw [torusSiteInFrame_add j hm]
      rcases st with ⟨i, b⟩
      cases b
      · simp [stepDisplacement, torusSiteInFrame_neg j hm, torusSiteInFrame_unitStep j hm, add_comm]
      · simp [stepDisplacement, torusSiteInFrame_unitStep j hm, add_comm]
    simp only [pathHolonomy, torusPathHolonomy]
    rw [add_comm (torusSiteInFrame H j x), hv, ih]
    congr 1
    rcases st with ⟨i, b⟩
    cases b
    · simp only [linkValue, Bool.false_eq_true, if_false]
      rw [← torusSiteInFrame_unitStep j hm, ← torusSiteInFrame_sub j hm, readAtLevel_torusSiteInFrame j hm]
    · simp only [linkValue, if_true]
      rw [readAtLevel_torusSiteInFrame j hm]
theorem torusPathHolonomy_plaquette {m : ℕ} (W : TorusField m) (x : TorusSite m) (μ ν : Fin 4) :
    torusPathHolonomy W x [(μ, true), (ν, true), (μ, false), (ν, false)] = TorusFields.holonomy W x μ ν := by
  simp only [torusPathHolonomy, TorusFields.holonomy]
  simp [mul_assoc, add_assoc, sub_eq_add_neg]
theorem plaquetteDefect_readAtLevel {H : BlockFrame} {j m : ℕ} (hm : ∀ i, H.period j i = m)
    (W : TorusField m) (p : H.Site j × Fin 4 × Fin 4) :
    plaquetteDefect (readAtLevel H j W) p =
      TorusFields.curvature W (TorusLumps.toTorusSite m p.1) p.2.1 p.2.2 := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.plaquetteDefect_readAtLevel_torus <;> assumption
end Helpers
variable {L k n : ℕ}
theorem readAtLevel_wideFrame_top (W : TorusField (n * L)) (s : (wideFrame L k n).Site (k + 1)) (i : Fin 4) :
    readAtLevel (wideFrame L k n) (k + 1) W s i = readAtLevel (deepFrame L k n) (k + 1) W (toDeep (k + 1) s) i := by
  have hc := siteCoords_toDeep (L := L) (k := k) (n := n) le_rfl s
  show W (fun j => ((siteCoords s j : ℤ) : ZMod (n * L))) i =
    W (fun j => ((siteCoords (toDeep (k + 1) s) j : ℤ) : ZMod (n * L))) i
  rw [hc]
theorem torusSiteInFrame_wideFrame (y : TorusSite (n * L)) :
    torusSiteInFrame (wideFrame L k n) (k + 1) y = toWide (k + 1) (torusSiteInFrame (deepFrame L k n) (k + 1) y) := by
  funext i
  exact (zmod_cast_intCast _ _ (wideFrame_period_eq (L := L) (k := k) (n := n) (j := k + 1) le_rfl i).symm _).symm
theorem levelShare_succ (T : ParameterAssignment) (hT : T.Admissible) (k n : ℕ) [NeZero n] (hn : T.n₀ ≤ n)
    (hlv : minimalChainExistenceStatement) (W : TorusField (n * T.side)) (hW : TorusFields.IsCold T.threshold W)
    (y : TorusSite (n * T.side)) :
    levelShare T.coupling T.side (k + 1) Finset.univ y W =
      minimalSiteShare (F := deepFrame T.side k n) T.coupling (torusSiteInFrame (deepFrame T.side k n) (k + 1) y)
        (readAtLevel (deepFrame T.side k n) (k + 1) W) := by
  have hL : Odd T.side := hT.L_odd
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have ha : 0 ≤ T.coupling := by have := hT.a_ge; linarith
  have hsB := wideFrame_extent_pos (k := k) hL hn0
  have hptop : ∀ i, (wideFrame T.side k n).period (wideFrame T.side k n).top i = n * T.side := fun i => by
    show n * T.side * T.side ^ (k + 1 - (k + 1)) = n * T.side
    simp
  have hS : cellsOfSites (wideFrame T.side k n) (Finset.univ : Finset (TorusSite (n * T.side))) =
      finiteCells (wideFrame T.side k n) :=
    cellsOfSites_univ hsB hptop
  have hlhs : levelShare T.coupling T.side (k + 1) Finset.univ y W =
      minimalCellShare T.coupling (finiteCells (wideFrame T.side k n))
        (torusSiteInFrame (wideFrame T.side k n) (k + 1) y) (readAtLevel (wideFrame T.side k n) (k + 1) W) := by
    show minimalCellShare T.coupling (cellsOfSites (wideFrame T.side k n) Finset.univ) _ _ = _
    rw [hS]
  have htopB : ∀ X : (deepFrame T.side k n).FieldChain, X (k + 1) = readAtLevel (deepFrame T.side k n) (k + 1) W →
      liftChain X (k + 1) = readAtLevel (wideFrame T.side k n) (k + 1) W := by
    intro X hX
    funext s i
    show X (k + 1) (toDeep (k + 1) s) i = _
    rw [hX, readAtLevel_wideFrame_top]
  have htopA : ∀ Z : (wideFrame T.side k n).FieldChain, Z (k + 1) = readAtLevel (wideFrame T.side k n) (k + 1) W →
      lowerChain Z (k + 1) = readAtLevel (deepFrame T.side k n) (k + 1) W := by
    intro Z hZ
    funext s i
    show Z (k + 1) (toWide (k + 1) s) i = _
    rw [hZ, readAtLevel_wideFrame_top, toDeep_toWide le_rfl]
  have hminB : ∀ X, IsMinimizingChainBelow T.coupling (finiteCells (deepFrame T.side k n))
      (readAtLevel (deepFrame T.side k n) (k + 1) W) X →
      IsMinimalChain T.coupling (finiteCells (wideFrame T.side k n))
        (readAtLevel (wideFrame T.side k n) (k + 1) W) (liftChain X) := by
    intro X hX
    refine ⟨htopB X hX.1, fun Z hZ => ?_⟩
    rw [chainAction_liftChain hL hn0, ← chainActionBelow_lowerChain hL hn0]
    exact hX.2 _ (htopA Z hZ)
  have hminA : ∀ Z, IsMinimalChain T.coupling (finiteCells (wideFrame T.side k n))
      (readAtLevel (wideFrame T.side k n) (k + 1) W) Z →
      IsMinimizingChainBelow T.coupling (finiteCells (deepFrame T.side k n))
        (readAtLevel (deepFrame T.side k n) (k + 1) W) (lowerChain Z) := by
    intro Z hZ
    refine ⟨htopA Z hZ.1, fun X hX => ?_⟩
    rw [chainActionBelow_lowerChain hL hn0, ← chainAction_liftChain hL hn0]
    exact hZ.2 _ (htopB X hX)
  obtain ⟨Z, hZ, -⟩ := (hlv (wideFrame T.side k n) T.coupling (finiteCells (wideFrame T.side k n)) ha).2.2.2
    (readAtLevel (wideFrame T.side k n) (k + 1) W)
  have hex : ∃ X, IsMinimizingChainBelow T.coupling (finiteCells (deepFrame T.side k n))
      (readAtLevel (deepFrame T.side k n) (k + 1) W) X := ⟨lowerChain Z, hminA Z hZ⟩
  have hamb : IsAdmissibleAmbient (wideFrame T.side k n) := by
    refine Or.inr fun i => ?_
    have h1 : 4096 ≤ T.n₀ := hT.n₀_ge
    have h2 : 1 ≤ T.side := hL.pos
    show 64 ≤ n * T.side
    nlinarith
  have hreg : IsOrthantRegular (finiteCells (wideFrame T.side k n)) 1024 := fun z =>
    ⟨fun _ => 1, fun _ => Or.inl rfl, fun q _ _ _ _ _ => _root_.YangMills.Construction.ShareEvaluation.mem_finiteCells_of_pos hsB _⟩
  have hcoldB : IsCold (finiteCells (wideFrame T.side k n)) (wideFrame T.side k n).top T.threshold
      (readAtLevel (wideFrame T.side k n) (k + 1) W) := by
    intro p hp
    have h1 : p.2.1 < p.2.2 := (Finset.mem_filter.1 hp).2.1
    exact lt_of_eq_of_lt (plaquetteDefect_readAtLevel (H := wideFrame T.side k n) hptop W p) (hW _ _ _ h1)
  have hσ : T.threshold ≤ T.σA := by have := hT.σ_le; have := hT.σ_pos; linarith
  have hchain := hT.chain.2.2.2.2.2.2.2.2 (wideFrame T.side k n) 1024 (finiteCells (wideFrame T.side k n)) rfl
    hamb le_rfl hreg T.threshold (readAtLevel (wideFrame T.side k n) (k + 1) W) hT.σ_pos hσ hcoldB
  have hclause := hchain.2.2.1.2.2.1 _ (hminB _ hex.choose_spec)
    (torusSiteInFrame (wideFrame T.side k n) (k + 1) y)
  unfold minimalSiteShare
  rw [dif_pos hex, hlhs, ← hclause, torusSiteInFrame_wideFrame]
  exact cellShare_liftChain hL hn0 T.coupling _ _
end Final
section Zero
variable {n : ℕ}
abbrev baseFrame (L n : ℕ) : BlockFrame := torusFrame L 0 n
theorem ancestorSite_zero {L : ℕ} (x : (baseFrame L n).Site 0) : ancestorSite (F := baseFrame L n) 0 x = x := by
  funext i
  show (((siteCoords x i + ((L : ℤ) ^ (0 - 0) - 1) / 2) / (L : ℤ) ^ (0 - 0) : ℤ) : ZMod _) = x i
  simp [siteCoords]
theorem plaquetteVertices_nodup {m : ℕ} (hm : 2 ≤ m) (x : TorusSite m) {μ ν : Fin 4} (h : μ < ν) :
    (plaquetteVertices x μ ν).Nodup := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LevelShare.nodup_plaquetteVertices <;> assumption
open Classical in
theorem levelShare_zero (T : ParameterAssignment) (hT : T.Admissible) (n : ℕ) [NeZero n] (hn : T.n₀ ≤ n)
    (W : TorusField (n * T.side)) (y : TorusSite (n * T.side)) :
    levelShare T.coupling T.side 0 Finset.univ y W =
      minimalSiteShare (F := baseFrame T.side n) T.coupling (torusSiteInFrame (baseFrame T.side n) 0 y)
        (readAtLevel (baseFrame T.side n) 0 W) := by
  have hL : Odd T.side := hT.L_odd
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hm2 : 2 ≤ n * T.side := by
    have h1 : 4096 ≤ T.n₀ := hT.n₀_ge
    have h2 : 1 ≤ T.side := hL.pos
    nlinarith
  have hm : ∀ i, (baseFrame T.side n).period 0 i = n * T.side := fun i => by
    show n * T.side ^ (0 + 1 - 0) = n * T.side
    simp
  have hcov := mem_sitesOfCells_finiteCells (baseFrame T.side n) hL (fun _ => hn0) 0 (by simp)
  let X₀ : (baseFrame T.side n).FieldChain := fun j => match j with
    | 0 => readAtLevel (baseFrame T.side n) 0 W
    | _ + 1 => fun _ _ => 1
  have hex : ∃ X, IsMinimizingChainBelow T.coupling (finiteCells (baseFrame T.side n))
      (readAtLevel (baseFrame T.side n) 0 W) X := by
    refine ⟨X₀, rfl, fun X' hX' => ?_⟩
    have e : X' 0 = X₀ 0 := hX'
    show wilsonAction _ (X₀ 0) + T.coupling * ∑ j ∈ Finset.range 0, _ ≤
      wilsonAction _ (X' 0) + T.coupling * ∑ j ∈ Finset.range 0, _
    rw [e]
    simp
  unfold minimalSiteShare
  rw [dif_pos hex]
  have hX : hex.choose 0 = readAtLevel (baseFrame T.side n) 0 W := hex.choose_spec.1
  show _ = ∑ p ∈ innerPlaquettes (finiteCells (baseFrame T.side n)) 0, _ + T.coupling * ∑ j ∈ Finset.range 0, _
  simp only [Finset.range_zero, Finset.sum_empty, mul_zero, add_zero]
  show ∑ p ∈ plaquettesIn Finset.univ, _ = _
  apply Finset.sum_nbij (fun q => (torusSiteInFrame (baseFrame T.side n) 0 q.1, q.2))
  · intro q hq
    have h1 := (Finset.mem_filter.1 hq).2.1
    unfold innerPlaquettes
    exact Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hcov _, by simp⟩, h1, fun x _ => hcov x⟩
  · rintro ⟨q, μ, ν⟩ _ ⟨q', μ', ν'⟩ _ h
    simp only [Prod.mk.injEq] at h
    have e := congrArg (TorusLumps.toTorusSite (n * T.side)) h.1
    rw [toTorusSite_torusSiteInFrame _ hm, toTorusSite_torusSiteInFrame _ hm] at e
    simp [e, h.2.1, h.2.2]
  · rintro ⟨p, μ, ν⟩ hp
    have h1 := (Finset.mem_filter.1 (Finset.mem_coe.1 hp)).2.1
    refine ⟨(TorusLumps.toTorusSite (n * T.side) p, μ, ν), ?_, ?_⟩
    · exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, h1, fun _ _ => Finset.mem_univ _⟩)
    · simp [torusSiteInFrame_toTorusSite _ hm]
  · rintro ⟨q, μ, ν⟩ hq
    have h1 : μ < ν := (Finset.mem_filter.1 hq).2.1
    have inj : ∀ a b : TorusSite (n * T.side),
        torusSiteInFrame (baseFrame T.side n) 0 a = torusSiteInFrame (baseFrame T.side n) 0 b ↔ a = b := by
      intro a b
      refine ⟨fun h => ?_, fun h => by rw [h]⟩
      have e := congrArg (TorusLumps.toTorusSite (n * T.side)) h
      rwa [toTorusSite_torusSiteInFrame _ hm, toTorusSite_torusSiteInFrame _ hm] at e
    have e1 : torusSiteInFrame (baseFrame T.side n) 0 q + unitStep 0 μ =
        torusSiteInFrame (baseFrame T.side n) 0 (q + TorusFields.unitStep _ μ) := by
      rw [torusSiteInFrame_add _ hm, torusSiteInFrame_unitStep _ hm]
    have e2 : torusSiteInFrame (baseFrame T.side n) 0 q + unitStep 0 ν =
        torusSiteInFrame (baseFrame T.side n) 0 (q + TorusFields.unitStep _ ν) := by
      rw [torusSiteInFrame_add _ hm, torusSiteInFrame_unitStep _ hm]
    have e3 : torusSiteInFrame (baseFrame T.side n) 0 q + unitStep 0 μ + unitStep 0 ν =
        torusSiteInFrame (baseFrame T.side n) 0 (q + TorusFields.unitStep _ μ + TorusFields.unitStep _ ν) := by
      rw [torusSiteInFrame_add _ hm, torusSiteInFrame_add _ hm, torusSiteInFrame_unitStep _ hm,
        torusSiteInFrame_unitStep _ hm]
    have hiff : y ∈ plaquetteVertices q μ ν ↔
        torusSiteInFrame (baseFrame T.side n) 0 y ∈ plaquetteCorners ((torusSiteInFrame (baseFrame T.side n) 0 q, μ, ν) :
          (baseFrame T.side n).Site 0 × Fin 4 × Fin 4) := by
      rw [mem_plaquetteCorners]
      simp only [plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false]
      rw [e3, e1, e2]
      simp only [inj]
    have hpv : plaquetteHolonomy (readAtLevel (baseFrame T.side n) 0 W)
        ((torusSiteInFrame (baseFrame T.side n) 0 q, μ, ν) : (baseFrame T.side n).Site 0 × Fin 4 × Fin 4) =
          TorusFields.holonomy W q μ ν :=
      (pathHolonomy_readAtLevel 0 hm W q _).trans (torusPathHolonomy_plaquette W q μ ν)
    have hw : ∑ x ∈ plaquetteCorners ((torusSiteInFrame (baseFrame T.side n) 0 q, μ, ν) :
          (baseFrame T.side n).Site 0 × Fin 4 × Fin 4),
        (if ancestorSite (F := baseFrame T.side n) 0 x = torusSiteInFrame (baseFrame T.side n) 0 y
          then (1 / 4 : ℝ) else 0) =
        if y ∈ plaquetteVertices q μ ν then 1 / 4 else 0 := by
      by_cases hy : y ∈ plaquetteVertices q μ ν
      · rw [if_pos hy, Finset.sum_eq_single (torusSiteInFrame (baseFrame T.side n) 0 y)]
        · simp [ancestorSite_zero]
        · intro b _ hb
          simp [ancestorSite_zero, hb]
        · intro h
          exact absurd (hiff.1 hy) h
      · rw [if_neg hy]
        apply Finset.sum_eq_zero
        intro x hx
        rw [ancestorSite_zero, if_neg]
        rintro rfl
        exact hy (hiff.2 hx)
    have key : (((plaquetteVertices q μ ν).count y : ℕ) : ℝ) / 4 * plaquetteEnergy W q μ ν =
        (∑ x ∈ plaquetteCorners ((torusSiteInFrame (baseFrame T.side n) 0 q, μ, ν) :
            (baseFrame T.side n).Site 0 × Fin 4 × Fin 4),
          (if ancestorSite (F := baseFrame T.side n) 0 x = torusSiteInFrame (baseFrame T.side n) 0 y
            then (1 / 4 : ℝ) else 0)) *
        (1 - ((plaquetteHolonomy (readAtLevel (baseFrame T.side n) 0 W)
          ((torusSiteInFrame (baseFrame T.side n) 0 q, μ, ν) : (baseFrame T.side n).Site 0 × Fin 4 × Fin 4) :
            UnitQuaternion) : ℍ[ℝ]).re) := by
      rw [hw, hpv, (plaquetteVertices_nodup hm2 q h1).count]
      unfold plaquetteEnergy
      split_ifs <;> norm_num
    rw [hX]
    convert key using 3
    congr!
end Zero
theorem levelShareEqMinimalSiteShare_of_minimalChainExistence (hlv : minimalChainExistenceStatement) :
    LevelShareEqMinimalSiteShare := by
  intro T hT t n _ hn W hW y
  cases t with
  | zero => exact levelShare_zero T hT n hn W y
  | succ k => exact levelShare_succ T hT k n hn hlv W hW y
end YangMills.Construction.ShareEvaluation
end
