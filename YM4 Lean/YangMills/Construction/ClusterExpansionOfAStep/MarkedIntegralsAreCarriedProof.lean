import YangMills.Construction.ClusterExpansionOfAStep.ImageStateKeepsTranslationsProof
import YangMills.Construction.ClusterExpansionOfAStep.FitsOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.GaugeCarriesTheKernel
import YangMills.Construction.ClusterExpansionOfAStep.HaarOfFieldsIsKept
import YangMills.Construction.ClusterExpansionOfAStep.IsometriesCarryTheKernel
import YangMills.Construction.ClusterExpansionOfAStep.MarkedIntegralsAreCarried
import YangMills.Construction.ClusterExpansionOfAStep.WilsonWeightHasTheExpansionProof
import YangMills.Construction.ColdChainAtEveryLevel.SecondDifferenceOfAPlaquette
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.StepInvariance
open YangMills.Construction.BlockAverages YangMills.Construction.LumpContours YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.StepSettings YangMills.Construction.StepMarks YangMills.Construction.StepCosts YangMills.Construction.MarkedIntegrals YangMills.Construction.StepFrames YangMills.Construction.FieldHaar YangMills.Construction.ColdChain
section Adjoint
def adjointAction (g : UnitQuaternion) (w : imaginaryQuaternions) : imaginaryQuaternions :=
  ⟨(g : ℍ[ℝ]) * (w : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]), by
    have hw : (w : ℍ[ℝ]).re = 0 := w.2
    have hs : star (w : ℍ[ℝ]) = -(w : ℍ[ℝ]) := by
      ext <;> simp [hw]
    set q : ℍ[ℝ] := (g : ℍ[ℝ]) * (w : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) with hq
    have h1 : star q = -q := by
      rw [hq, coe_inv_unitQuaternion, star_mul, star_mul, star_star, hs]
      noncomm_ring
    have h2 : (star q).re = q.re := by simp
    rw [h1] at h2
    show q.re = 0
    simp only [Quaternion.re_neg] at h2
    linarith⟩
theorem coe_adjointAction (g : UnitQuaternion) (w : imaginaryQuaternions) :
    ((adjointAction g w : imaginaryQuaternions) : ℍ[ℝ]) =
      (g : ℍ[ℝ]) * (w : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) := rfl
theorem norm_conj_unitQuaternion (g : UnitQuaternion) (q : ℍ[ℝ]) :
    ‖(g : ℍ[ℝ]) * q * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ = ‖q‖ := by apply _root_.YangMills.Construction.PlaquetteSecondDifference.norm_conj <;> assumption
theorem norm_adjointAction (g : UnitQuaternion) (w : imaginaryQuaternions) :
    ‖((adjointAction g w : imaginaryQuaternions) : ℍ[ℝ])‖ = ‖(w : ℍ[ℝ])‖ := by
  rw [coe_adjointAction, norm_conj_unitQuaternion]
theorem expUnit_adjointAction (g : UnitQuaternion) (w : imaginaryQuaternions) :
    expUnit (adjointAction g w) = g * expUnit w * g⁻¹ := by
  apply Subtype.ext
  have hgg : (g : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := by
    rw [← Submonoid.coe_mul]
    simp
  have hc : ∀ c : ℝ, ((c : ℝ) : ℍ[ℝ]) = c • (1 : ℍ[ℝ]) := fun c => by ext <;> simp
  change NormedSpace.exp ((adjointAction g w : imaginaryQuaternions) : ℍ[ℝ]) =
    (g : ℍ[ℝ]) * NormedSpace.exp (w : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])
  rw [TopLevelSites.exp_imaginary, TopLevelSites.exp_imaginary, norm_adjointAction, hc]
  change _ + _ • ((g : ℍ[ℝ]) * (w : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])) = _
  simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, mul_one, hgg]
theorem minimalLog_conj (k h : UnitQuaternion) (hh : ‖(minimalLog h : ℍ[ℝ])‖ < Real.pi) :
    minimalLog (k * h * k⁻¹) = adjointAction k (minimalLog h) := by
  have e : k * h * k⁻¹ = expUnit (adjointAction k (minimalLog h)) := by
    rw [expUnit_adjointAction, GaugeFixing.expUnit_minimalLog]
  rw [e]
  exact GaugeFixing.minimalLog_expUnit _ (by rw [norm_adjointAction]; exact hh)
theorem le_norm_sub_of_norm_eq_pi {ρ : ℝ} (hρ : ρ ≤ 1) {w f : imaginaryQuaternions}
    (hw : ‖(w : ℍ[ℝ])‖ = Real.pi) (hf : ‖(f : ℍ[ℝ])‖ ≤ 1) :
    ρ ≤ ‖((w - f : imaginaryQuaternions) : ℍ[ℝ])‖ := by
  have h1 : ‖(w : ℍ[ℝ])‖ - ‖(f : ℍ[ℝ])‖ ≤ ‖(w : ℍ[ℝ]) - (f : ℍ[ℝ])‖ := norm_sub_norm_le _ _
  have h2 : ((w - f : imaginaryQuaternions) : ℍ[ℝ]) = (w : ℍ[ℝ]) - (f : ℍ[ℝ]) := rfl
  rw [h2]
  have := Real.pi_gt_three
  linarith
theorem cutoffFactor_conj (ρ : ℝ) (p : ℝ → ℝ) (hρ : ρ ≤ 1) (k h : UnitQuaternion)
    (f f' : imaginaryQuaternions) (hf : ‖(f : ℍ[ℝ])‖ ≤ 1)
    (hf' : (f' : ℍ[ℝ]) = (k : ℍ[ℝ]) * (f : ℍ[ℝ]) * ((k⁻¹ : UnitQuaternion) : ℍ[ℝ])) :
    cutoffFactor ρ p ‖((minimalLog (k * h * k⁻¹) - f' : imaginaryQuaternions) : ℍ[ℝ])‖ =
      cutoffFactor ρ p ‖((minimalLog h - f : imaginaryQuaternions) : ℍ[ℝ])‖ := by
  have hf'n : ‖(f' : ℍ[ℝ])‖ ≤ 1 := by rw [hf', norm_conj_unitQuaternion]; exact hf
  rcases lt_or_eq_of_le (GaugeFixing.norm_minimalLog_le_pi h) with hlt | heq
  · rw [minimalLog_conj k h hlt]
    have e : ((adjointAction k (minimalLog h) - f' : imaginaryQuaternions) : ℍ[ℝ]) =
        (k : ℍ[ℝ]) * ((minimalLog h - f : imaginaryQuaternions) : ℍ[ℝ]) *
          ((k⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
      have e1 : ((adjointAction k (minimalLog h) - f' : imaginaryQuaternions) : ℍ[ℝ]) =
          ((adjointAction k (minimalLog h) : imaginaryQuaternions) : ℍ[ℝ]) - (f' : ℍ[ℝ]) := rfl
      have e2 : ((minimalLog h - f : imaginaryQuaternions) : ℍ[ℝ]) =
          (minimalLog h : ℍ[ℝ]) - (f : ℍ[ℝ]) := rfl
      rw [e1, e2, coe_adjointAction, hf']
      noncomm_ring
    rw [e, norm_conj_unitQuaternion]
  · have heq' : ‖(minimalLog (k * h * k⁻¹) : ℍ[ℝ])‖ = Real.pi := by
      rcases lt_or_eq_of_le (GaugeFixing.norm_minimalLog_le_pi (k * h * k⁻¹)) with hlt | e
      · exfalso
        have h1 := minimalLog_conj k⁻¹ (k * h * k⁻¹) hlt
        have e2 : k⁻¹ * (k * h * k⁻¹) * k⁻¹⁻¹ = h := by group
        rw [e2] at h1
        rw [h1, norm_adjointAction] at heq
        exact hlt.ne heq
      · exact e
    have h1 := le_norm_sub_of_norm_eq_pi hρ heq hf
    have h2 := le_norm_sub_of_norm_eq_pi hρ heq' hf'n
    unfold cutoffFactor
    rw [if_neg (not_lt.mpr h1), if_neg (not_lt.mpr h2)]
end Adjoint
section Size
theorem norm_minimizingCoordinates_le {F : BlockFrame} (a : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) (S : Finset F.Cell)
    (V : F.GaugeField F.top) (x : F.Site F.depth) (i : Fin 4) :
    ‖(minimizingCoordinates a S V ρ x i : ℍ[ℝ])‖ ≤ ρ := by
  classical
  unfold minimizingCoordinates
  split_ifs with h
  · have hs := h.choose_spec
    by_cases hb : (x, i) ∈ chordBonds S
    · exact hs.2.1 (x, i) hb
    · rw [show h.choose x i = 0 from hs.1 (x, i) hb]
      simpa using hρ
  · simpa using hρ
theorem norm_frameCoord_le {n : ℕ} (ℓ : StepParameters) {ρA : ℝ} (hρ : 0 ≤ ρA) (t m : ℕ) (V : TorusField n)
    (b : TorusBond (n * ℓ.side)) :
    ‖(frameCoord ℓ ρA t m V b : ℍ[ℝ])‖ ≤ ρA := by
  unfold frameCoord bondFrameCoord
  split_ifs
  · unfold reflectedBondCoord BlockAverages.minimizingBondCoordinate
    exact norm_minimizingCoordinates_le _ hρ _ _ _ _
  · unfold BlockAverages.minimizingBondCoordinate
    exact norm_minimizingCoordinates_le _ hρ _ _ _ _
end Size
section Chart
variable {F : BlockFrame}
open Classical in
def chartElement (V : F.GaugeField F.top) (W : F.GaugeField F.depth) (b : F.Site F.depth × Fin 4) :
    UnitQuaternion :=
  if IsCrossingBond b then
    BlockAverages.gaugeTransform (axialGauge 1 W) W b.1 b.2 * (V (enclosingCell b.1) b.2)⁻¹
  else BlockAverages.gaugeTransform (axialGauge 1 W) W b.1 b.2
theorem bondCoordinate_eq_minimalLog (V : F.GaugeField F.top) (W : F.GaugeField F.depth)
    (b : F.Site F.depth × Fin 4) :
    LumpContours.bondCoordinate 1 V W b = minimalLog (chartElement V W b) := by
  unfold LumpContours.bondCoordinate chartElement
  split_ifs <;> rfl
theorem enclosingCell_cellCentre (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell) :
    enclosingCell (cellCentre F.depth z) = z := by
  have h0 : (0 : Fin 4 → ℤ) ∈ centredCube F.blockSide := by
    rw [TopLevelSites.mem_centredCube_iff]
    intro i
    have : 0 ≤ TopLevelSites.halfWidth F.blockSide := by
      unfold TopLevelSites.halfWidth
      have := hL.pos
      omega
    simpa using this
  have := TopLevelSites.enclosingCell_centre_add hL hs z 0 h0
  rwa [siteOfCoords_zero, add_zero] at this
theorem axialGauge_gaugeTransform (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (γ : F.Cell → UnitQuaternion) (W : F.GaugeField F.depth) (x : F.Site F.depth) :
    axialGauge 1 (BlockAverages.gaugeTransform (fun z => γ (enclosingCell z)) W) x =
      γ (enclosingCell x) * axialGauge 1 W x * (γ (enclosingCell x))⁻¹ := by
  obtain ⟨_, hx⟩ := TopLevelSites.centre_cellOffset hL hs x
  have h1 : cellCentre F.depth (enclosingCell x) +
      GaugeFixing.pathDisplacement (F := F) F.depth (axisPath (cellOffset x) 1) = x := by
    have : GaugeFixing.pathDisplacement (F := F) F.depth (axisPath (cellOffset x) 1) =
        siteOfCoords (F := F) F.depth (cellOffset x) :=
      TopLevelSites.axisPath_displacement (F := F) _
    rw [this]
    exact hx
  unfold axialGauge
  rw [GaugeFixing.pathHolonomy_gaugeTransform, h1]
  simp only [enclosingCell_cellCentre hL hs]
theorem axialGauge_link_gaugeTransform (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (γ : F.Cell → UnitQuaternion) (W : F.GaugeField F.depth) (x : F.Site F.depth) (i : Fin 4) :
    BlockAverages.gaugeTransform (axialGauge 1 (BlockAverages.gaugeTransform (fun z => γ (enclosingCell z)) W))
        (BlockAverages.gaugeTransform (fun z => γ (enclosingCell z)) W) x i =
      γ (enclosingCell x) * BlockAverages.gaugeTransform (axialGauge 1 W) W x i *
        (γ (enclosingCell (x + BlockAverages.unitStep F.depth i)))⁻¹ := by
  change axialGauge 1 (BlockAverages.gaugeTransform (fun z => γ (enclosingCell z)) W) x *
      (γ (enclosingCell x) * W x i * (γ (enclosingCell (x + BlockAverages.unitStep F.depth i)))⁻¹) *
      (axialGauge 1 (BlockAverages.gaugeTransform (fun z => γ (enclosingCell z)) W)
        (x + BlockAverages.unitStep F.depth i))⁻¹ =
    γ (enclosingCell x) * (axialGauge 1 W x * W x i *
      (axialGauge 1 W (x + BlockAverages.unitStep F.depth i))⁻¹) *
      (γ (enclosingCell (x + BlockAverages.unitStep F.depth i)))⁻¹
  rw [axialGauge_gaugeTransform hL hs, axialGauge_gaugeTransform hL hs]
  group
theorem chartElement_gaugeTransform (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (γ : F.Cell → UnitQuaternion) (V : F.GaugeField F.top) (W : F.GaugeField F.depth)
    (b : F.Site F.depth × Fin 4) :
    chartElement (BlockAverages.gaugeTransform γ V)
        (BlockAverages.gaugeTransform (fun z => γ (enclosingCell z)) W) b =
      γ (enclosingCell b.1) * chartElement V W b * (γ (enclosingCell b.1))⁻¹ := by
  obtain ⟨x, i⟩ := b
  unfold chartElement
  by_cases hc : IsCrossingBond (x, i)
  · rw [if_pos hc, if_pos hc]
    simp only
    rw [axialGauge_link_gaugeTransform hL hs, TopLevelSites.enclosingCell_add_unitStep hL hs x i hc]
    change _ * (γ (enclosingCell x) * V (enclosingCell x) i *
      (γ (enclosingCell x + BlockAverages.unitStep F.top i))⁻¹)⁻¹ = _
    group
  · have e : enclosingCell (x + BlockAverages.unitStep F.depth i) = enclosingCell x := by
      by_contra hne
      exact hc hne
    rw [if_neg hc, if_neg hc]
    simp only
    rw [axialGauge_link_gaugeTransform hL hs, e]
def blockTranslation (u : Fin 4 → ℤ) : F.Site F.depth :=
  siteOfCoords F.depth fun i => (F.blockSide : ℤ) * u i
theorem cellCentre_add_offset_add_blockTranslation (u : Fin 4 → ℤ) (z : F.Cell) (h : Fin 4 → ℤ) :
    cellCentre F.depth z + siteOfCoords F.depth h + blockTranslation u =
      cellCentre F.depth (z + siteOfCoords F.top u) + siteOfCoords F.depth h := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.cellCentre_add_add_translation <;> assumption
theorem cellCentre_add_blockTranslation (u : Fin 4 → ℤ) (z : F.Cell) :
    cellCentre F.depth z + blockTranslation u = cellCentre F.depth (z + siteOfCoords F.top u) := by
  rw [BlockAverages.cellCentre_add F.depth (by simp [BlockFrame.top])]
  unfold blockTranslation
  simp only [TopLevelSites.top_sub_depth, pow_one]
theorem enclosingCell_add_blockTranslation (u : Fin 4 → ℤ) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (x : F.Site F.depth) :
    enclosingCell (x + blockTranslation u) = enclosingCell x + siteOfCoords F.top u := by
  obtain ⟨z, h, hh, rfl⟩ := TopLevelSites.exists_centre_add hL hs x
  rw [cellCentre_add_offset_add_blockTranslation, TopLevelSites.enclosingCell_centre_add hL hs _ _ hh,
    TopLevelSites.enclosingCell_centre_add hL hs _ _ hh]
theorem cellOffset_add_blockTranslation (u : Fin 4 → ℤ) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (x : F.Site F.depth) :
    cellOffset (x + blockTranslation u) = cellOffset x := by
  obtain ⟨z, h, hh, rfl⟩ := TopLevelSites.exists_centre_add hL hs x
  rw [cellCentre_add_offset_add_blockTranslation, TopLevelSites.cellOffset_centre_add hL hs _ _ hh,
    TopLevelSites.cellOffset_centre_add hL hs _ _ hh]
theorem isCrossingBond_add_blockTranslation (u : Fin 4 → ℤ) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) (x : F.Site F.depth) (i : Fin 4) :
    IsCrossingBond (x + blockTranslation u, i) ↔ IsCrossingBond (x, i) := by
  obtain ⟨z, h, hh, rfl⟩ := TopLevelSites.exists_centre_add hL hs x
  rw [cellCentre_add_offset_add_blockTranslation, TopLevelSites.isCrossingBond_iff hL hs _ _ hh,
    TopLevelSites.isCrossingBond_iff hL hs _ _ hh]
theorem isAxialTreeBond_add_blockTranslation (u : Fin 4 → ℤ) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) (x : F.Site F.depth) (i : Fin 4) :
    IsAxialTreeBond (x + blockTranslation u, i) ↔ IsAxialTreeBond (x, i) := by
  obtain ⟨z, h, hh, rfl⟩ := TopLevelSites.exists_centre_add hL hs x
  rw [cellCentre_add_offset_add_blockTranslation, TopLevelSites.isAxialTreeBond_iff hL hs _ _ hh,
    TopLevelSites.isAxialTreeBond_iff hL hs _ _ hh]
theorem pathHolonomy_translate {j : ℕ} (τ : F.Site j) (X : F.GaugeField j) (x : F.Site j) (l : List PathStep) :
    pathHolonomy (fun y i => X (y + τ) i) x l = pathHolonomy X (x + τ) l := by
  induction l generalizing x with
  | nil => rfl
  | cons st r ih =>
    have e : linkValue (fun y i => X (y + τ) i) x st = linkValue X (x + τ) st := by
      unfold linkValue
      split_ifs
      · rfl
      · have e1 : x - BlockAverages.unitStep j st.1 + τ = x + τ - BlockAverages.unitStep j st.1 := by abel
        show (X (x - BlockAverages.unitStep j st.1 + τ) st.1)⁻¹ = _
        rw [e1]
    have e2 : x + stepDisplacement j st + τ = x + τ + stepDisplacement j st := by abel
    simp only [pathHolonomy, e, ih, e2]
theorem axialGauge_translate (u : Fin 4 → ℤ) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (W : F.GaugeField F.depth) (x : F.Site F.depth) :
    axialGauge 1 (fun y i => W (y + blockTranslation u) i) x = axialGauge 1 W (x + blockTranslation u) := by
  unfold axialGauge
  rw [pathHolonomy_translate, enclosingCell_add_blockTranslation u hL hs,
    cellOffset_add_blockTranslation u hL hs, cellCentre_add_blockTranslation]
theorem chartElement_translate (u : Fin 4 → ℤ) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (V : F.GaugeField F.top) (W : F.GaugeField F.depth) (b : F.Site F.depth × Fin 4) :
    chartElement (fun c i => V (c + siteOfCoords F.top u) i) (fun y i => W (y + blockTranslation u) i) b =
      chartElement V W (b.1 + blockTranslation u, b.2) := by
  obtain ⟨x, i⟩ := b
  have e : BlockAverages.gaugeTransform (axialGauge 1 fun y i => W (y + blockTranslation u) i)
      (fun y i => W (y + blockTranslation u) i) x i =
      BlockAverages.gaugeTransform (axialGauge 1 W) W (x + blockTranslation u) i := by
    change axialGauge 1 (fun y i => W (y + blockTranslation u) i) x * W (x + blockTranslation u) i *
        (axialGauge 1 (fun y i => W (y + blockTranslation u) i) (x + BlockAverages.unitStep F.depth i))⁻¹ =
      axialGauge 1 W (x + blockTranslation u) * W (x + blockTranslation u) i *
        (axialGauge 1 W (x + blockTranslation u + BlockAverages.unitStep F.depth i))⁻¹
    have e2 : x + BlockAverages.unitStep F.depth i + blockTranslation u =
        x + blockTranslation u + BlockAverages.unitStep F.depth i := by abel
    rw [axialGauge_translate u hL hs, axialGauge_translate u hL hs, e2]
  unfold chartElement
  by_cases hc : IsCrossingBond (x, i)
  · rw [if_pos hc, if_pos ((isCrossingBond_add_blockTranslation u hL hs x i).mpr hc)]
    simp only
    rw [e, enclosingCell_add_blockTranslation u hL hs]
  · rw [if_neg hc, if_neg (fun h => hc ((isCrossingBond_add_blockTranslation u hL hs x i).mp h))]
    simp only
    rw [e]
end Chart
section Torus
theorem stepBlockFrame_period_zero (L n : ℕ) [NeZero n] (i : Fin 4) : (stepBlockFrame L n).period 0 i = n * L :=
  TopLevelSites.period_depth_of_extent (F := stepBlockFrame L n) (n := n) (fun _ => rfl) i
theorem stepBlockFrame_period_one (L n : ℕ) [NeZero n] (i : Fin 4) : (stepBlockFrame L n).period 1 i = n :=
  TopLevelSites.period_top_of_extent (F := stepBlockFrame L n) (n := n) (fun _ => rfl) i
variable {n : ℕ} [NeZero n]
theorem readAtLevel_gaugeTransform {F : BlockFrame} {j N : ℕ} [NeZero N] (hp : ∀ i, F.period j i = N)
    (g : TorusSite N → UnitQuaternion) (W : TorusField N) :
    readAtLevel F j (TorusFields.gaugeTransform g W) =
      BlockAverages.gaugeTransform (fun c => g (toTorusSite N c)) (readAtLevel F j W) := by apply _root_.YangMills.Construction.SettingFits.readAtLevel_gaugeTransform <;> assumption
variable {L : ℕ} [NeZero L]
theorem toTorusSite_enclosingCell (x : TorusSite (n * L)) :
    toTorusSite n (enclosingCell (torusSiteInFrame (stepBlockFrame L n) 0 x)) = parentBlock L x := by
  haveI : NeZero (n * (stepBlockFrame L n).blockSide) := (inferInstance : NeZero (n * L))
  have h := TopLevelSites.enclosingCell_torusSiteInFrame (F := stepBlockFrame L n) (n := n) (fun _ => rfl) x
  have h' : enclosingCell (torusSiteInFrame (stepBlockFrame L n) 0 x) =
      torusSiteInFrame (stepBlockFrame L n) 1 (parentBlock L x) := h
  rw [h']
  exact TopLevelSites.toTorusSite_torusSiteInFrame (stepBlockFrame_period_one L n) _
theorem blockConstantGauge_toTorusSite (g : TorusSite n → UnitQuaternion) (z : (stepBlockFrame L n).Site 0) :
    blockConstantGauge L g (toTorusSite (n * L) z) = g (toTorusSite n (enclosingCell z)) := by
  have h := toTorusSite_enclosingCell (n := n) (L := L) (toTorusSite (n * L) z)
  rw [TopLevelSites.torusSiteInFrame_toTorusSite (stepBlockFrame_period_zero L n)] at h
  rw [h]
  rfl
theorem readAtLevel_zero_blockConstantGauge (g : TorusSite n → UnitQuaternion) (W : TorusField (n * L)) :
    readAtLevel (stepBlockFrame L n) 0 (TorusFields.gaugeTransform (blockConstantGauge L g) W) =
      BlockAverages.gaugeTransform (F := stepBlockFrame L n)
        (fun z => (fun c => g (toTorusSite n c)) (enclosingCell z)) (readAtLevel (stepBlockFrame L n) 0 W) := by
  rw [readAtLevel_gaugeTransform (stepBlockFrame_period_zero L n)]
  congr 1
  funext z
  exact blockConstantGauge_toTorusSite g z
theorem chartCoord_eq_minimalLog (ℓ : StepParameters) (V : TorusField n) (W : TorusField (n * ℓ.side))
    (b : TorusBond (n * ℓ.side)) :
    chartCoord ℓ V W b = minimalLog (chartElement (F := stepBlockFrame ℓ.side n)
      (readAtLevel (stepBlockFrame ℓ.side n) 1 V) (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
      (torusSiteInFrame (stepBlockFrame ℓ.side n) 0 b.1, b.2)) :=
  bondCoordinate_eq_minimalLog (F := stepBlockFrame ℓ.side n) _ _ _
theorem chartElement_torus_gaugeTransform (hL : Odd L) (h2 : 2 ≤ n) (g : TorusSite n → UnitQuaternion)
    (V : TorusField n) (W : TorusField (n * L)) (b : TorusBond (n * L)) :
    chartElement (F := stepBlockFrame L n) (readAtLevel (stepBlockFrame L n) 1 (TorusFields.gaugeTransform g V))
        (readAtLevel (stepBlockFrame L n) 0 (TorusFields.gaugeTransform (blockConstantGauge L g) W))
        (torusSiteInFrame (stepBlockFrame L n) 0 b.1, b.2) =
      g (parentBlock L b.1) * chartElement (F := stepBlockFrame L n) (readAtLevel (stepBlockFrame L n) 1 V)
        (readAtLevel (stepBlockFrame L n) 0 W) (torusSiteInFrame (stepBlockFrame L n) 0 b.1, b.2) *
        (g (parentBlock L b.1))⁻¹ := by
  rw [readAtLevel_zero_blockConstantGauge, readAtLevel_gaugeTransform (stepBlockFrame_period_one L n)]
  have := chartElement_gaugeTransform (F := stepBlockFrame L n) hL (fun _ => h2) (fun c => g (toTorusSite n c))
    (readAtLevel (stepBlockFrame L n) 1 V) (readAtLevel (stepBlockFrame L n) 0 W)
    (torusSiteInFrame (stepBlockFrame L n) 0 b.1, b.2)
  refine this.trans ?_
  show g (toTorusSite n (enclosingCell (torusSiteInFrame (stepBlockFrame L n) 0 b.1))) * _ *
      (g (toTorusSite n (enclosingCell (torusSiteInFrame (stepBlockFrame L n) 0 b.1))))⁻¹ = _
  rw [toTorusSite_enclosingCell]
theorem bondMark_gaugeTransform (R : StepSetup) (hL : Odd R.params.side) (h2 : 2 ≤ n)
    (hσ : R.params.threshold ≤ 1) (hρ0 : 0 ≤ R.anchorRadius) (hρ1 : R.anchorRadius ≤ 1)
    (g : TorusSite n → UnitQuaternion) (V : TorusField n) (W : TorusField (n * R.params.side))
    (b : TorusBond (n * R.params.side))
    (hfr : (frameCoord R.params R.anchorRadius R.depth R.frameReach (TorusFields.gaugeTransform g V) b : ℍ[ℝ]) =
      (g (parentBlock R.params.side b.1) : ℍ[ℝ]) *
        (frameCoord R.params R.anchorRadius R.depth R.frameReach V b : ℍ[ℝ]) *
        (((g (parentBlock R.params.side b.1))⁻¹ : UnitQuaternion) : ℍ[ℝ])) :
    R.bondMark (TorusFields.gaugeTransform g V)
        (TorusFields.gaugeTransform (blockConstantGauge R.params.side g) W) b = R.bondMark V W b := by
  unfold StepSetup.bondMark goodMark frameDeviation
  rw [chartCoord_eq_minimalLog, chartCoord_eq_minimalLog, chartElement_torus_gaugeTransform hL h2]
  exact cutoffFactor_conj _ _ (by linarith) _ _ _ _
    ((norm_frameCoord_le _ hρ0 _ _ _ _).trans hρ1) hfr
def blockShift (L : ℕ) (n : ℕ) (v : Fin 4 → ℤ) : TorusSite (n * L) := siteOfInt fun i => (L : ℤ) * v i
abbrev levelZeroTranslation (L n : ℕ) (v : Fin 4 → ℤ) : (stepBlockFrame L n).Site 0 :=
  blockTranslation (F := stepBlockFrame L n) v
theorem torusSiteInFrame_add_blockShift (x : TorusSite (n * L)) (v : Fin 4 → ℤ) :
    torusSiteInFrame (stepBlockFrame L n) 0 (x + blockShift L n v) =
      torusSiteInFrame (stepBlockFrame L n) 0 x + levelZeroTranslation L n v := by
  rw [TopLevelSites.torusSiteInFrame_add (stepBlockFrame_period_zero L n)]
  unfold blockShift
  rw [TopLevelSites.torusSiteInFrame_siteOfInt (stepBlockFrame_period_zero L n)]
  rfl
theorem readAtLevel_zero_translate (v : Fin 4 → ℤ) (W : TorusField (n * L)) :
    readAtLevel (stepBlockFrame L n) 0 (TorusFields.translate (blockShift L n v) W) =
      fun y i => readAtLevel (stepBlockFrame L n) 0 W (y + levelZeroTranslation L n v) i := by
  funext x i
  change W (toTorusSite (n * L) x + blockShift L n v) i =
    W (toTorusSite (n * L) (x + levelZeroTranslation L n v)) i
  rw [TopLevelSites.toTorusSite_add (stepBlockFrame_period_zero L n)]
  have e : toTorusSite (n * L) (levelZeroTranslation L n v) = blockShift L n v :=
    TopLevelSites.toTorusSite_siteOfCoords (stepBlockFrame_period_zero L n) _
  rw [e]
theorem readAtLevel_one_translate (v : Fin 4 → ℤ) (V : TorusField n) :
    readAtLevel (stepBlockFrame L n) 1 (TorusFields.translate (siteOfInt v) V) =
      fun c i => readAtLevel (stepBlockFrame L n) 1 V (c + siteOfCoords 1 v) i := by
  funext x i
  change V (toTorusSite n x + siteOfInt v) i = V (toTorusSite n (x + siteOfCoords 1 v)) i
  rw [TopLevelSites.toTorusSite_add (stepBlockFrame_period_one L n),
    TopLevelSites.toTorusSite_siteOfCoords (stepBlockFrame_period_one L n)]
theorem chartElement_torus_translate (hL : Odd L) (h2 : 2 ≤ n) (v : Fin 4 → ℤ) (V : TorusField n)
    (W : TorusField (n * L)) (b : TorusBond (n * L)) :
    chartElement (F := stepBlockFrame L n) (readAtLevel (stepBlockFrame L n) 1 (TorusFields.translate (siteOfInt v) V))
        (readAtLevel (stepBlockFrame L n) 0 (TorusFields.translate (blockShift L n v) W))
        (torusSiteInFrame (stepBlockFrame L n) 0 b.1, b.2) =
      chartElement (F := stepBlockFrame L n) (readAtLevel (stepBlockFrame L n) 1 V)
        (readAtLevel (stepBlockFrame L n) 0 W)
        (torusSiteInFrame (stepBlockFrame L n) 0 (b.1 + blockShift L n v), b.2) := by
  have e1 := readAtLevel_zero_translate (n := n) (L := L) v W
  have e2 := readAtLevel_one_translate (n := n) (L := L) v V
  have e3 := torusSiteInFrame_add_blockShift (n := n) (L := L) b.1 v
  rw [e1, e2, e3]
  exact chartElement_translate (F := stepBlockFrame L n) v hL (fun _ => h2) _ _
    (torusSiteInFrame (stepBlockFrame L n) 0 b.1, b.2)
theorem bondMark_translate (R : StepSetup) (hL : Odd R.params.side) (h2 : 2 ≤ n) (v : Fin 4 → ℤ)
    (V : TorusField n) (W : TorusField (n * R.params.side)) (b : TorusBond (n * R.params.side))
    (hfr : frameCoord R.params R.anchorRadius R.depth R.frameReach (TorusFields.translate (siteOfInt v) V) b =
      frameCoord R.params R.anchorRadius R.depth R.frameReach V (b.1 + blockShift R.params.side n v, b.2)) :
    R.bondMark (TorusFields.translate (siteOfInt v) V) (TorusFields.translate (blockShift R.params.side n v) W) b =
      R.bondMark V W (b.1 + blockShift R.params.side n v, b.2) := by
  unfold StepSetup.bondMark goodMark frameDeviation
  rw [chartCoord_eq_minimalLog, chartCoord_eq_minimalLog, chartElement_torus_translate hL h2, hfr]
theorem isAxialTreeBond_add_blockShift (hL : Odd L) (h2 : 2 ≤ n) (v : Fin 4 → ℤ) (b : TorusBond (n * L)) :
    IsAxialTreeBond (F := stepBlockFrame L n)
        (torusSiteInFrame (stepBlockFrame L n) 0 (b.1 + blockShift L n v), b.2) ↔
      IsAxialTreeBond (F := stepBlockFrame L n) (torusSiteInFrame (stepBlockFrame L n) 0 b.1, b.2) := by
  rw [torusSiteInFrame_add_blockShift]
  exact isAxialTreeBond_add_blockTranslation (F := stepBlockFrame L n) v hL (fun _ => h2) _ _
theorem parentBlock_add_blockShift (hL : Odd L) (h2 : 2 ≤ n) (v : Fin 4 → ℤ) (x : TorusSite (n * L)) :
    parentBlock L (x + blockShift L n v) = parentBlock L x + siteOfInt v := by
  have h := enclosingCell_add_blockTranslation (F := stepBlockFrame L n) v hL (fun _ => h2)
    (torusSiteInFrame (stepBlockFrame L n) 0 x)
  have h' : enclosingCell (torusSiteInFrame (stepBlockFrame L n) 0 x + levelZeroTranslation L n v) =
      (enclosingCell (torusSiteInFrame (stepBlockFrame L n) 0 x) : (stepBlockFrame L n).Site 1) +
        siteOfCoords 1 v := h
  rw [← torusSiteInFrame_add_blockShift] at h'
  have e := congrArg (toTorusSite n) h'
  rw [toTorusSite_enclosingCell] at e
  have e2 := TopLevelSites.toTorusSite_add (F := stepBlockFrame L n) (j := 1) (stepBlockFrame_period_one L n)
    (enclosingCell (torusSiteInFrame (stepBlockFrame L n) 0 x)) (siteOfCoords 1 v)
  have e3 := TopLevelSites.toTorusSite_siteOfCoords (F := stepBlockFrame L n) (j := 1)
    (stepBlockFrame_period_one L n) v
  exact e.trans (e2.trans (congrArg₂ (· + ·) (toTorusSite_enclosingCell x) e3))
theorem mem_chartBondsInBlocks_image (hL : Odd L) (h2 : 2 ≤ n) (v : Fin 4 → ℤ) (A : Finset (TorusSite n))
    (b : TorusBond (n * L)) :
    (b.1 + blockShift L n v, b.2) ∈ chartBondsInBlocks L (A.image (· + siteOfInt v)) ↔
      b ∈ chartBondsInBlocks L A := by
  classical
  unfold chartBondsInBlocks StepCosts.chartBonds
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [isAxialTreeBond_add_blockShift hL h2, parentBlock_add_blockShift hL h2]
  simp
theorem prod_chartBondsInBlocks_image (R : StepSetup) (hL : Odd R.params.side) (h2 : 2 ≤ n) (v : Fin 4 → ℤ)
    (A : Finset (TorusSite n)) (f f' : TorusBond (n * R.params.side) → ℝ)
    (h : ∀ b ∈ chartBondsInBlocks R.params.side A, f b = f' (b.1 + blockShift R.params.side n v, b.2)) :
    ∏ b ∈ chartBondsInBlocks R.params.side A, f b =
      ∏ b ∈ chartBondsInBlocks R.params.side (A.image (· + siteOfInt v)), f' b := by
  refine Finset.prod_nbij' (fun b => (b.1 + blockShift R.params.side n v, b.2))
    (fun b => (b.1 - blockShift R.params.side n v, b.2)) ?_ ?_ ?_ ?_ h
  · intro b hb
    exact (mem_chartBondsInBlocks_image hL h2 v A b).mpr hb
  · intro b hb
    refine (mem_chartBondsInBlocks_image hL h2 v A _).mp ?_
    simpa using hb
  · intro b _
    simp
  · intro b _
    simp
end Torus
section Hull
variable {ℓ : StepParameters} {N : ℕ} [NeZero N]
theorem torusHotLumps_gaugeTransform (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ N)
    (g : TorusSite N → UnitQuaternion) (W : TorusField N) :
    torusHotLumps ℓ (TorusFields.gaugeTransform g W) = torusHotLumps ℓ W := by apply _root_.YangMills.Construction.WilsonExpansion.torusHotLumps_gaugeTransform <;> assumption
theorem isHullState_gaugeTransform (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ N) (r : ℕ)
    (g : TorusSite N → UnitQuaternion) (W : TorusField N) (Y : Finset (TorusSite N)) :
    IsHullState ℓ r (TorusFields.gaugeTransform g W) Y ↔ IsHullState ℓ r W Y := by
  unfold IsHullState torusHotSites
  rw [torusHotLumps_gaugeTransform hfit hLn]
theorem mem_torusHotSites {W : TorusField N} {z : TorusSite N} :
    z ∈ torusHotSites ℓ W ↔ ∃ l ∈ torusHotLumps ℓ W, z ∈ l := by
  simp only [torusHotSites, Finset.mem_biUnion, id_eq]
theorem mem_torusHotSites_of_translate (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ N) (W : TorusField N)
    (v : Fin 4 → ℤ) {a : TorusSite N}
    (ha : a ∈ torusHotSites ℓ (TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) * v i) W)) :
    a + siteOfInt (fun i => (ℓ.side : ℤ) * v i) ∈ torusHotSites ℓ W := by apply _root_.YangMills.Construction.WilsonExpansion.add_mem_torusHotSites_of_translate <;> assumption
theorem translate_neg_translate (u : TorusSite N) (W : TorusField N) :
    TorusFields.translate (-u) (TorusFields.translate u W) = W := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.translate_neg_translate <;> assumption
theorem siteOfInt_side_mul_neg (ℓ : StepParameters) (v : Fin 4 → ℤ) :
    (siteOfInt (fun i => (ℓ.side : ℤ) * (-v) i) : TorusSite N) = -siteOfInt fun i => (ℓ.side : ℤ) * v i := by apply _root_.YangMills.Construction.WilsonExpansion.siteOfInt_block_neg <;> assumption
theorem mem_torusHotSites_translate (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ N) (W : TorusField N)
    (v : Fin 4 → ℤ) {a : TorusSite N}
    (h : a + siteOfInt (fun i => (ℓ.side : ℤ) * v i) ∈ torusHotSites ℓ W) :
    a ∈ torusHotSites ℓ (TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) * v i) W) := by
  have h1 := mem_torusHotSites_of_translate hfit hLn
    (TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) * v i) W) (-v)
    (a := a + siteOfInt (fun i => (ℓ.side : ℤ) * v i))
  rw [siteOfInt_side_mul_neg, translate_neg_translate] at h1
  simpa using h1 h
theorem mem_translateSet (u : TorusSite N) (Y : Finset (TorusSite N)) (z : TorusSite N) :
    z ∈ translateSet u Y ↔ z + u ∈ Y := by
  classical
  unfold translateSet
  simp
theorem chainConnected_sub {r : ℕ} {Y : Finset (TorusSite N)} (u : TorusSite N) {a b : TorusSite N}
    (h : ChainConnected r Y a b) : ChainConnected r (translateSet u Y) (a - u) (b - u) := by
  unfold ChainConnected at h ⊢
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hcd ih =>
    refine ih.tail ?_
    obtain ⟨h1, h2, h3⟩ := hcd
    refine ⟨(mem_translateSet u Y _).mpr (by simpa using h1), (mem_translateSet u Y _).mpr (by simpa using h2), ?_⟩
    rw [← supDist_add_right _ _ u]
    simpa using h3
theorem isHullState_translate (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ N) (r : ℕ) (W : TorusField N)
    (Y : Finset (TorusSite N)) (v : Fin 4 → ℤ) (h : IsHullState ℓ r W Y) :
    IsHullState ℓ r (TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) * v i) W)
      (translateSet (siteOfInt fun i => (ℓ.side : ℤ) * v i) Y) := by
  set u : TorusSite N := siteOfInt fun i => (ℓ.side : ℤ) * v i with hu
  refine ⟨fun a ha => ?_, fun X' hX' => ?_⟩
  · obtain ⟨b, hb, hab⟩ := (mem_thickening _ _ _).mp ha
    refine (mem_translateSet u Y a).mpr
      (h.1 ((mem_thickening _ _ _).mpr ⟨b + u, mem_torusHotSites_of_translate hfit hLn W v hb, ?_⟩))
    rw [supDist_add_right]
    exact hab
  · classical
    obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hX'
    have hy : y' + u ∈ Y := (mem_translateSet u Y y').mp hy'
    obtain ⟨l, hl, z, hz⟩ := h.2 _ (Finset.mem_image.mpr ⟨y' + u, hy, rfl⟩)
    obtain ⟨hzl, hzX⟩ := Finset.mem_inter.mp hz
    obtain ⟨hzY, hJ⟩ := Finset.mem_filter.mp hzX
    have hback : z - u ∈ torusHotSites ℓ (TorusFields.translate u W) :=
      mem_torusHotSites_translate hfit hLn W v (by simpa [hu] using mem_torusHotSites.mpr ⟨l, hl, hzl⟩)
    obtain ⟨l', hl', hzl'⟩ := mem_torusHotSites.mp hback
    refine ⟨l', hl', z - u, Finset.mem_inter.mpr ⟨hzl', Finset.mem_filter.mpr
      ⟨(mem_translateSet u Y _).mpr (by simpa using hzY), ?_⟩⟩⟩
    have := chainConnected_sub u hJ
    simpa using this
end Hull
section Labels
variable {N : ℕ} [NeZero N]
def labelActionEquiv (Λ : LabelSpace) (Y : Finset (TorusSite N)) (g : TorusSite N → UnitQuaternion) :
    (Y → Λ.Ω) ≃ᵐ (Y → Λ.Ω) where
  toFun := Λ.act Y g
  invFun := Λ.act Y g⁻¹
  left_inv ω := by
    show Λ.act Y g⁻¹ (Λ.act Y g ω) = ω
    rw [← Λ.act_mul, inv_mul_cancel]
    exact Λ.act_one Y ω
  right_inv ω := by
    show Λ.act Y g (Λ.act Y g⁻¹ ω) = ω
    rw [← Λ.act_mul, mul_inv_cancel]
    exact Λ.act_one Y ω
  measurable_toFun := (Λ.act_keeps Y g).measurable
  measurable_invFun := (Λ.act_keeps Y g⁻¹).measurable
def translateSetEquiv (u : TorusSite N) (Y : Finset (TorusSite N)) : Y ≃ translateSet u Y where
  toFun z := ⟨z.1 - u, (mem_translateSet u Y _).mpr (by simp)⟩
  invFun z := ⟨z.1 + u, (mem_translateSet u Y _).mp z.2⟩
  left_inv z := by simp
  right_inv z := by simp
theorem lintegral_translateLabel {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]
    (u : TorusSite N) (Y : Finset (TorusSite N)) (f : (translateSet u Y → Ω) → ENNReal) :
    ∫⁻ ω, f (translateLabel u Y ω) ∂(Measure.pi fun _ : Y => μ) =
      ∫⁻ ω, f ω ∂(Measure.pi fun _ : translateSet u Y => μ) := by
  have hmp := measurePreserving_arrowCongr' (fun _ : Y => μ) (fun _ : translateSet u Y => μ)
    (translateSetEquiv u Y) (MeasurableEquiv.refl Ω) (fun _ => MeasurePreserving.id _)
  have h := hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) f
  exact h
end Labels
section Lower
variable {n : ℕ} [NeZero n]
theorem avoidingPart_gaugeTransform (R : StepSetup)
    (hH : HullExpansion R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight
      R.clusterFactor R.siteDensity)
    (hfit : R.params.Admissible) (hn : R.params.n₀ ≤ n)
    (A : Finset (TorusSite n)) (γ : TorusSite (n * R.params.side) → UnitQuaternion)
    (W : TorusField (n * R.params.side)) :
    R.avoidingPart A (TorusFields.gaugeTransform γ W) = R.avoidingPart A W := by
  classical
  have hLn : R.params.side ∣ n * R.params.side := Dvd.intro_left n rfl
  have hside : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨hLn, by rw [mul_comm]; exact Nat.mul_le_mul_right _ hn⟩
  unfold StepSetup.avoidingPart
  refine congrArg ENNReal.toReal (Finset.sum_congr (Finset.filter_congr fun Y _ => ?_) fun Y hY => ?_)
  · rw [isHullState_gaugeTransform hfit hLn]
  have hhull := (Finset.mem_filter.mp hY).2.1
  have h := (R.labels.act_keeps Y γ).lintegral_comp_emb (labelActionEquiv R.labels Y γ).measurableEmbedding
    (fun ω => ENNReal.ofReal (R.labelWeight (n * R.params.side) (TorusFields.gaugeTransform γ W) Y ω))
  rw [← h]
  exact lintegral_congr fun ω => by rw [hH.gauge _ hside W Y ω γ hhull]
theorem avoidingPart_translate (R : StepSetup)
    (hH : HullExpansion R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight
      R.clusterFactor R.siteDensity)
    (hfit : R.params.Admissible) (h2 : 2 ≤ n) (hn : R.params.n₀ ≤ n)
    (A : Finset (TorusSite n)) (v : Fin 4 → ℤ) (W : TorusField (n * R.params.side)) :
    R.avoidingPart A (TorusFields.translate (blockShift R.params.side n v) W) =
      R.avoidingPart (A.image (· + siteOfInt v)) W := by
  classical
  have hLn : R.params.side ∣ n * R.params.side := Dvd.intro_left n rfl
  have hside : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨hLn, by rw [mul_comm]; exact Nat.mul_le_mul_right _ hn⟩
  set w : TorusSite (n * R.params.side) := blockShift R.params.side n v with hw
  have hodd := hfit.L_odd
  unfold StepSetup.avoidingPart
  refine congrArg ENNReal.toReal ?_
  symm
  refine Finset.sum_nbij' (translateSet w) (translateSet (-w)) ?_ ?_ ?_ ?_ ?_
  · intro Y hY
    obtain ⟨-, hhull, hdis⟩ := Finset.mem_filter.mp hY
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, isHullState_translate hfit hLn _ W Y v hhull, ?_⟩
    rw [Finset.disjoint_left] at hdis ⊢
    intro z hz hz'
    refine hdis ((mem_translateSet w Y z).mp hz) ?_
    have hb : parentBlock R.params.side z ∈ A := (Finset.mem_filter.mp hz').2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [hw, parentBlock_add_blockShift hodd h2]
    exact Finset.mem_image_of_mem _ hb
  · intro Y hY
    obtain ⟨-, hhull, hdis⟩ := Finset.mem_filter.mp hY
    have hm := isHullState_translate hfit hLn _ (TorusFields.translate w W) Y (-v) hhull
    have ew : (siteOfInt (fun i => (R.params.side : ℤ) * (-v) i) : TorusSite (n * R.params.side)) = -w :=
      siteOfInt_side_mul_neg R.params v
    rw [ew, translate_neg_translate] at hm
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm, ?_⟩
    rw [Finset.disjoint_left] at hdis ⊢
    intro z hz hz'
    have hzY : z + -w ∈ Y := (mem_translateSet (-w) Y z).mp hz
    refine hdis hzY ?_
    have hb : parentBlock R.params.side z ∈ A.image (· + siteOfInt v) := (Finset.mem_filter.mp hz').2
    obtain ⟨a, ha, e⟩ := Finset.mem_image.mp hb
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have e2 := parentBlock_add_blockShift (n := n) hodd h2 v (z + -w)
    have e3 : z + -w + blockShift R.params.side n v = z := by rw [← hw]; abel
    rw [e3, ← e] at e2
    have e4 : parentBlock R.params.side (z + -w) = a := add_right_cancel e2.symm
    rw [e4]
    exact ha
  · intro Y _
    ext z
    simp [mem_translateSet]
  · intro Y _
    ext z
    simp [mem_translateSet]
  · intro Y hY
    obtain ⟨-, hhull, -⟩ := Finset.mem_filter.mp hY
    have h := lintegral_translateLabel R.labels.μ w Y
      (fun ω => ENNReal.ofReal (R.labelWeight (n * R.params.side) (TorusFields.translate w W) (translateSet w Y) ω))
    rw [← h]
    exact lintegral_congr fun ω => by rw [hH.translation _ hside W Y ω w ⟨v, rfl⟩ hhull]
end Lower
section Carried
variable {m : ℕ} [NeZero m]
theorem transports_translate (g : TorusIsometry) (hp : g.axisPerm = 1) (hs : ∀ i, g.axisSign i = 1)
    (t : Fin 4 → ℤ) (ht : ∀ i, g.offset i = - t i) (W : TorusField m) :
    g.Transports W (TorusFields.translate (siteOfInt t) W) := by
  intro x k
  have e : g.axisPerm.symm k = k := by rw [hp]; rfl
  rw [if_pos (by rw [e]; exact hs k), e]
  have hx : g.mapSite x + siteOfInt t = x := by
    funext i
    simp [TorusIsometry.mapSite, hp, hs, ht, siteOfInt]
  simp [TorusFields.translate, hx]
theorem measurePreserving_translate (hh : HaarInvariantUnderSymmetries) (t : Fin 4 → ℤ) :
    MeasurePreserving (TorusFields.translate (siteOfInt t)) (fieldHaar m) (fieldHaar m) := by
  obtain ⟨Ψ, hΨ, hc⟩ := (hh m).2 ⟨1, fun _ => 1, -t, fun _ => Or.inl rfl⟩
  have e : Ψ = TorusFields.translate (siteOfInt t) := by
    funext W y k
    have h := hc W (y + siteOfInt t) k
    rw [if_pos rfl] at h
    have hy : TorusIsometry.mapSite (⟨1, fun _ => 1, -t, fun _ => Or.inl rfl⟩ : TorusIsometry)
        (y + siteOfInt t) = y := by
      funext i
      simp [TorusIsometry.mapSite, siteOfInt]
    rw [hy] at h
    exact h
  rwa [e] at hΨ
theorem siteOfInt_neg (t : Fin 4 → ℤ) : (siteOfInt (-t) : TorusSite m) = - siteOfInt t := by
  funext i
  simp [siteOfInt]
def translateEquiv (hh : HaarInvariantUnderSymmetries) (t : Fin 4 → ℤ) : TorusField m ≃ᵐ TorusField m where
  toFun := TorusFields.translate (siteOfInt t)
  invFun := TorusFields.translate (siteOfInt (-t))
  left_inv W := by
    show TorusFields.translate (siteOfInt (-t)) (TorusFields.translate (siteOfInt t) W) = W
    rw [siteOfInt_neg, translate_neg_translate]
  right_inv W := by
    show TorusFields.translate (siteOfInt t) (TorusFields.translate (siteOfInt (-t)) W) = W
    funext x i
    simp [TorusFields.translate, siteOfInt_neg]
  measurable_toFun := (measurePreserving_translate hh t).measurable
  measurable_invFun := (measurePreserving_translate hh (-t)).measurable
def gaugeTransformEquiv (hh : HaarInvariantUnderSymmetries) (γ : TorusSite m → UnitQuaternion) :
    TorusField m ≃ᵐ TorusField m where
  toFun := TorusFields.gaugeTransform γ
  invFun := TorusFields.gaugeTransform γ⁻¹
  left_inv W := by
    funext x i
    simp [TorusFields.gaugeTransform, mul_assoc]
  right_inv W := by
    funext x i
    simp [TorusFields.gaugeTransform, mul_assoc]
  measurable_toFun := ((hh m).1 γ).measurable
  measurable_invFun := ((hh m).1 γ⁻¹).measurable
variable {n : ℕ} [NeZero n]
theorem markedIntegral_gaugeTransform (R : StepSetup)
    (hH : HullExpansion R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight
      R.clusterFactor R.siteDensity)
    (hfit : R.params.Admissible) (hn : R.params.n₀ ≤ n) (h2 : 2 ≤ n) (hσ : R.params.threshold ≤ 1)
    (hρ0 : 0 ≤ R.anchorRadius) (hρ1 : R.anchorRadius ≤ 1)
    (hk : KernelGaugeInvariance) (hh : HaarInvariantUnderSymmetries) (A : Finset (TorusSite n))
    (V : TorusField n) (g : TorusSite n → UnitQuaternion)
    (hfr : ∀ b ∈ StepCosts.chartBonds R.params.side n,
      (frameCoord R.params R.anchorRadius R.depth R.frameReach (TorusFields.gaugeTransform g V) b : ℍ[ℝ]) =
        (g (parentBlock R.params.side b.1) : ℍ[ℝ]) *
          (frameCoord R.params R.anchorRadius R.depth R.frameReach V b : ℍ[ℝ]) *
          (((g (parentBlock R.params.side b.1))⁻¹ : UnitQuaternion) : ℍ[ℝ])) :
    R.markedIntegral A (TorusFields.gaugeTransform g V) = R.markedIntegral A V := by
  classical
  have hmp : MeasurePreserving
      (gaugeTransformEquiv (m := n * R.params.side) hh (blockConstantGauge R.params.side g))
      (fieldHaar (n * R.params.side)) (fieldHaar (n * R.params.side)) :=
    (hh (n * R.params.side)).1 (blockConstantGauge R.params.side g)
  unfold StepSetup.markedIntegral
  rw [← hmp.integral_comp']
  refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
  show R.avoidingPart A (TorusFields.gaugeTransform (blockConstantGauge R.params.side g) W) *
      averagedKernel R.params R.coupling
        (readAtLevel (stepBlockFrame R.params.side n) 0
          (TorusFields.gaugeTransform (blockConstantGauge R.params.side g) W))
        (readAtLevel (stepBlockFrame R.params.side n) 1 (TorusFields.gaugeTransform g V)) *
      ∏ b ∈ chartBondsInBlocks R.params.side A, R.bondMark (TorusFields.gaugeTransform g V)
        (TorusFields.gaugeTransform (blockConstantGauge R.params.side g) W) b = _
  rw [avoidingPart_gaugeTransform R hH hfit hn A, ((hk R.params hfit n g W V).2.2 R.coupling).2]
  congr 1
  refine Finset.prod_congr rfl fun b hb => ?_
  exact bondMark_gaugeTransform R hfit.L_odd h2 hσ hρ0 hρ1 g V W b (hfr b (Finset.mem_filter.mp hb).1)
theorem markedIntegral_translate (R : StepSetup)
    (hH : HullExpansion R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight
      R.clusterFactor R.siteDensity)
    (hfit : R.params.Admissible) (hn : R.params.n₀ ≤ n) (h2 : 2 ≤ n) (hi : IsometriesPreserveAveragedKernel)
    (hh : HaarInvariantUnderSymmetries) (A : Finset (TorusSite n)) (V : TorusField n) (v : Fin 4 → ℤ)
    (hfr : ∀ b ∈ StepCosts.chartBonds R.params.side n,
      frameCoord R.params R.anchorRadius R.depth R.frameReach (TorusFields.translate (siteOfInt v) V) b =
        frameCoord R.params R.anchorRadius R.depth R.frameReach V (b.1 + blockShift R.params.side n v, b.2)) :
    R.markedIntegral A (TorusFields.translate (siteOfInt v) V) = R.markedIntegral (A.image (· + siteOfInt v)) V := by
  classical
  set t : Fin 4 → ℤ := fun i => (R.params.side : ℤ) * v i with ht
  have hmp : MeasurePreserving (translateEquiv (m := n * R.params.side) hh t)
      (fieldHaar (n * R.params.side)) (fieldHaar (n * R.params.side)) :=
    measurePreserving_translate (m := n * R.params.side) hh t
  unfold StepSetup.markedIntegral
  rw [← hmp.integral_comp']
  refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
  show R.avoidingPart A (TorusFields.translate (blockShift R.params.side n v) W) *
      averagedKernel R.params R.coupling
        (readAtLevel (stepBlockFrame R.params.side n) 0 (TorusFields.translate (blockShift R.params.side n v) W))
        (readAtLevel (stepBlockFrame R.params.side n) 1 (TorusFields.translate (siteOfInt v) V)) *
      ∏ b ∈ chartBondsInBlocks R.params.side A,
        R.bondMark (TorusFields.translate (siteOfInt v) V)
          (TorusFields.translate (blockShift R.params.side n v) W) b = _
  have hker := hi R.params hfit R.coupling n hn ⟨1, fun _ => 1, -v, fun _ => Or.inl rfl⟩ W
    (TorusFields.translate (blockShift R.params.side n v) W) V (TorusFields.translate (siteOfInt v) V)
    (transports_translate _ rfl (fun _ => rfl) t (fun i => by simp [TorusIsometry.scaledLift, ht]) W)
    (transports_translate _ rfl (fun _ => rfl) v (fun _ => rfl) V)
  rw [avoidingPart_translate R hH hfit h2 hn A v, hker]
  congr 1
  refine prod_chartBondsInBlocks_image R hfit.L_odd h2 v A _ _ fun b hb => ?_
  have hc : b ∈ StepCosts.chartBonds R.params.side n := (Finset.mem_filter.mp hb).1
  exact bondMark_translate R hfit.L_odd h2 v V W b (hfr b hc)
end Carried
section Floor
theorem pow_le_clusterRange {y : ℝ} {k : ℕ} (hy : (2 : ℝ) ^ (100 * k) ≤ y) : 2 ^ k ≤ clusterRange y := by
  have h0 : (0 : ℝ) ≤ (2 : ℝ) ^ (100 * k) := by positivity
  have h1 : ((2 : ℝ) ^ (100 * k)) ^ ((1 : ℝ) / 100) ≤ y ^ ((1 : ℝ) / 100) :=
    Real.rpow_le_rpow h0 hy (by norm_num)
  have h2 : ((2 : ℝ) ^ (100 * k)) ^ ((1 : ℝ) / 100) = 2 ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  rw [h2] at h1
  have h3 : ((2 : ℝ) ^ k) ≤ ((clusterRange y : ℕ) : ℝ) := h1.trans (Nat.le_ceil _)
  exact_mod_cast h3
end Floor
theorem markedIntegralInvariance (hfr : FrameCovariance) (hk : KernelGaugeInvariance)
    (hi : IsometriesPreserveAveragedKernel) (hh : HaarInvariantUnderSymmetries) :
    MarkedIntegralInvariance := by
  refine ⟨fun _ => 1, fun _ => one_pos, fun T hd _ => ⟨max T.floorMin (2 ^ 1700), fun y hy R hR _ => ?_⟩⟩
  intro n _ hn V A hV
  have hy0 : T.floorMin ≤ y := le_trans (le_max_left _ _) hy
  have hy1 : (2 : ℝ) ^ 1700 ≤ y := le_trans (le_max_right _ _) hy
  have hfit : R.params.Admissible := by
    rw [hR.params_eq]
    exact hd.fits y hy0
  have hstep := hR.isStep
  have hH : HullExpansion R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight
      R.clusterFactor R.siteDensity := hstep.1.2
  have hx : (2 : ℝ) ^ 1700 ≤ R.coupling := hy1.trans hR.le_coupling
  have hx' : (2 : ℝ) ^ 1600 ≤ R.nextCoupling := by
    have h1 := hstep.2.1
    have h2 : (2 : ℝ) ^ 1700 = 2 ^ 100 * 2 ^ 1600 := by rw [← pow_add]
    have h3 : (0 : ℝ) < 2 ^ 1600 := by positivity
    have h4 : (2 : ℝ) ≤ 2 ^ 100 := by norm_num
    have key : ∀ P Q a b : ℝ, 0 < P → 2 ≤ Q → Q * P ≤ a → a ≤ 1.01 * b → P ≤ b := by
      intro P Q a b hP hQ h5 h6
      nlinarith
    exact key _ _ _ _ h3 h4 (h2 ▸ hx) h1
  have hrf : RangesAdmissible R.range R.nextRange := by
    refine ⟨hstep.2.2, pow_le_clusterRange (k := 16) (by norm_num; exact hx'), ?_⟩
    have h3 : 2 ^ 17 ≤ R.range := pow_le_clusterRange (k := 17) (by norm_num; exact hx)
    show 16 ≤ R.range / 2 ^ 11
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    exact le_trans (by norm_num) h3
  have hch : ColdChainConstants R.params.coupling T.δ₁ R.params.side T.lam R.anchorRadius T.σA T.cg T.N := by
    rw [hR.params_eq, hR.anchorRadius_eq]
    exact hd.chain
  have hσ2 : 2 * R.params.threshold ≤ T.σA := by
    rw [hR.params_eq]
    exact hd.σ_le
  have hσ1 : R.params.threshold ≤ 1 := by
    rw [hR.params_eq]
    exact hd.σ_one
  have hρ0 : 0 ≤ R.anchorRadius := hch.2.2.2.1.le
  have hρ1 : R.anchorRadius ≤ 1 := hch.2.2.2.2.1
  have h2 : 2 ≤ n := by
    have := hfit.n₀_ge
    omega
  have hsit : IsStepSituation R.params R.nextRange V Finset.univ ∅ (9 / 8 * R.params.threshold) :=
    Or.inr ⟨hn, hV, rfl, rfl, rfl⟩
  have hframes := hfr R.params T.δ₁ T.lam R.anchorRadius T.σA T.cg T.N hfit hch hσ2 R.depth R.range
    R.nextRange n V Finset.univ ∅ _ hrf hsit
  refine ⟨fun g => ?_, fun u => ?_⟩
  · exact markedIntegral_gaugeTransform R hH hfit hn h2 hσ1 hρ0 hρ1 hk hh A V g
      fun b hb => (hframes b hb (Finset.notMem_empty _)).1 g
  · have hu : u = siteOfInt fun i => ((u i).cast : ℤ) := eq_siteOfInt_cast u
    rw [hu]
    refine markedIntegral_translate R hH hfit hn h2 hi hh A V _ fun b hb => ?_
    have hb' : (b.1 + blockShift R.params.side n (fun i => ((u i).cast : ℤ)), b.2) ∈
        StepCosts.chartBonds R.params.side n := by
      classical
      unfold StepCosts.chartBonds at hb ⊢
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      rw [isAxialTreeBond_add_blockShift hfit.L_odd h2]
      exact hb
    have := (hframes _ hb' (Finset.notMem_empty _)).2 fun i => ((u i).cast : ℤ)
    have e : (b.1 + blockShift R.params.side n (fun i => ((u i).cast : ℤ))) -
        siteOfInt (fun i => (R.params.side : ℤ) * ((u i).cast : ℤ)) = b.1 := add_sub_cancel_right _ _
    simp only [e] at this
    exact this
end YangMills.Construction.StepInvariance
end
