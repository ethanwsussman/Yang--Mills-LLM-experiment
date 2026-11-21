import YangMills.Construction.ClusterExpansionOfAStep.FitsOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.FramesUnderGaugesAndTranslations
import YangMills.Construction.ColdStepAtMirrorFrames.ChartUnderGaugesAndShiftsProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames TopLevelSites TorusFields TorusLumps TorusMirror StepCosts StepMarks
namespace StepFrames
namespace Covariance
section AdjointAction
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
theorem norm_adjointAction (g : UnitQuaternion) (w : imaginaryQuaternions) :
    ‖((_root_.YangMills.Construction.StepFrames.Covariance.adjointAction g w : imaginaryQuaternions) : ℍ[ℝ])‖ = ‖(w : ℍ[ℝ])‖ := by
  change ‖(g : ℍ[ℝ]) * (w : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ = _
  rw [norm_mul, norm_mul, norm_unitQuaternion, norm_unitQuaternion, one_mul, mul_one]
theorem adjointAction_zero (g : UnitQuaternion) : _root_.YangMills.Construction.StepFrames.Covariance.adjointAction g 0 = 0 := by
  apply Subtype.ext
  change (g : ℍ[ℝ]) * ((0 : imaginaryQuaternions) : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 0
  simp
theorem expUnit_adjointAction (g : UnitQuaternion) (w : imaginaryQuaternions) :
    expUnit (_root_.YangMills.Construction.StepFrames.Covariance.adjointAction g w) = g * expUnit w * g⁻¹ := by
  apply Subtype.ext
  have hgg : (g : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := by
    rw [← Submonoid.coe_mul]
    simp
  have hc : ∀ c : ℝ, ((c : ℝ) : ℍ[ℝ]) = c • (1 : ℍ[ℝ]) := fun c => by ext <;> simp
  change NormedSpace.exp ((_root_.YangMills.Construction.StepFrames.Covariance.adjointAction g w : imaginaryQuaternions) : ℍ[ℝ]) =
    (g : ℍ[ℝ]) * NormedSpace.exp (w : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])
  rw [exp_imaginary, exp_imaginary, norm_adjointAction, hc]
  change _ + _ • ((g : ℍ[ℝ]) * (w : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])) = _
  simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, mul_one, hgg]
end AdjointAction
section Energy
variable {F : BlockFrame} {a : ℝ} {S : Finset F.Cell}
theorem blockEnergy_gaugeTransform (hcov : gaugeCovarianceStatement) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) (γ : F.Cell → UnitQuaternion) (W : F.GaugeField F.depth)
    (V : F.GaugeField F.top) :
    blockEnergy a S F.depth (BlockAverages.gaugeTransform (fun x => γ (enclosingCell x)) W)
      (BlockAverages.gaugeTransform γ V) = blockEnergy a S F.depth W V := by apply _root_.YangMills.Construction.ChartSymmetries.blockEnergy_gaugeTransform <;> assumption
theorem gaugeTransform_chartedField (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (γ : F.Cell → UnitQuaternion) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (V : F.GaugeField F.top) (x : F.Site F.depth) (i : Fin 4) :
    BlockAverages.gaugeTransform (fun x => γ (enclosingCell x)) (chartedField w V) x i =
      chartedField (fun x i => _root_.YangMills.Construction.StepFrames.Covariance.adjointAction (γ (enclosingCell x)) (w x i))
        (BlockAverages.gaugeTransform γ V) x i := by
  unfold chartedField BlockAverages.gaugeTransform
  beta_reduce
  by_cases hc : IsCrossingBond (x, i)
  · rw [if_pos hc, if_pos hc, enclosingCell_add_unitStep hL hs x i hc, expUnit_adjointAction]
    group
  · have e : enclosingCell (x + BlockAverages.unitStep F.depth i) = enclosingCell x := by
      by_contra hne
      exact hc hne
    rw [if_neg hc, if_neg hc, e]
    by_cases ht : IsAxialTreeBond (x, i)
    · rw [if_pos ht, if_pos ht]
      group
    · rw [if_neg ht, if_neg ht, expUnit_adjointAction]
theorem isMinimizingChart_gaugeTransform (hcov : gaugeCovarianceStatement) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) {ρ : ℝ} {V : F.GaugeField F.top}
    {w : F.Site F.depth → Fin 4 → imaginaryQuaternions} (γ : F.Cell → UnitQuaternion)
    (h : IsMinimizingChart a S V ρ w) :
    IsMinimizingChart a S (BlockAverages.gaugeTransform γ V) ρ
      (fun x i => _root_.YangMills.Construction.StepFrames.Covariance.adjointAction (γ (enclosingCell x)) (w x i)) := by
  refine ⟨fun b hb => ?_, fun b hb => ?_, fun W' => ?_⟩
  · simp only
    rw [h.1 b hb, _root_.YangMills.Construction.StepFrames.Covariance.adjointAction_zero]
  · simp only
    have := h.2.1 b hb
    change ‖((_root_.YangMills.Construction.StepFrames.Covariance.adjointAction (γ (enclosingCell b.1)) (w b.1 b.2) : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ ρ
    rw [norm_adjointAction]
    exact this
  · have e : chartedField (fun x i => _root_.YangMills.Construction.StepFrames.Covariance.adjointAction (γ (enclosingCell x)) (w x i))
          (BlockAverages.gaugeTransform γ V) =
        BlockAverages.gaugeTransform (fun x => γ (enclosingCell x)) (chartedField w V) := by
      funext x i
      exact (_root_.YangMills.Construction.StepFrames.Covariance.gaugeTransform_chartedField hL hs γ w V x i).symm
    rw [e, _root_.YangMills.Construction.StepFrames.Covariance.blockEnergy_gaugeTransform hcov hL hs]
    have e2 : W' = BlockAverages.gaugeTransform (fun x => γ (enclosingCell x))
        (BlockAverages.gaugeTransform (fun x => (γ (enclosingCell x))⁻¹) W') := by
      funext x i
      simp only [BlockAverages.gaugeTransform]
      group
    rw [e2, _root_.YangMills.Construction.StepFrames.Covariance.blockEnergy_gaugeTransform hcov hL hs]
    exact h.2.2 _
theorem minimizingCoordinates_gaugeTransform (hcov : gaugeCovarianceStatement) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) {ρ N0 s : ℝ} (hπ : ρ < Real.pi) {V : F.GaugeField F.top}
    (γ : F.Cell → UnitQuaternion) (hone : HasColdMinimizer a ρ N0 s S V)
    (hone' : HasColdMinimizer a ρ N0 s S (BlockAverages.gaugeTransform γ V)) (x : F.Site F.depth)
    (i : Fin 4) :
    minimizingCoordinates a S (BlockAverages.gaugeTransform γ V) ρ x i =
      _root_.YangMills.Construction.StepFrames.Covariance.adjointAction (γ (enclosingCell x)) (minimizingCoordinates a S V ρ x i) := by
  obtain ⟨w, hw, _, hl⟩ := minimizingCoordinates_eq hL hs hπ le_rfl hone
  obtain ⟨w', hw', _, hl'⟩ := minimizingCoordinates_eq hL hs hπ le_rfl hone'
  have hρ : IsMinimizingChart a S V ρ w :=
    ⟨hw.1, fun b hb => (hw.2.1 b hb).trans (min_le_left _ _), hw.2.2⟩
  have hρ' : IsMinimizingChart a S (BlockAverages.gaugeTransform γ V) ρ w' :=
    ⟨hw'.1, fun b hb => (hw'.2.1 b hb).trans (min_le_left _ _), hw'.2.2⟩
  obtain ⟨w'', hw'', _, hu⟩ := hone'
  have h₂ : IsMinimizingChart a S (BlockAverages.gaugeTransform γ V) ρ w'' :=
    ⟨hw''.1, fun b hb => (hw''.2.1 b hb).trans (min_le_left _ _), hw''.2.2⟩
  have e1 := minimizingChart_unique hL hs hπ (_root_.YangMills.Construction.StepFrames.Covariance.isMinimizingChart_gaugeTransform hcov hL hs γ hρ) h₂ hu
  have e2 := minimizingChart_unique hL hs hπ hρ' h₂ hu
  rw [hl, hl', e2, ← e1]
end Energy
section Shift
variable {F : BlockFrame} (u : Fin 4 → ℤ)
def levelShift (j : ℕ) : F.Site j := siteOfCoords j fun i => (F.blockSide : ℤ) ^ (F.top - j) * u i
def shiftField {j : ℕ} (X : F.GaugeField j) : F.GaugeField j := fun x i => X (x + levelShift u j) i
theorem shiftField_shiftField_neg {j : ℕ} (X : F.GaugeField j) : shiftField u (shiftField (-u) X) = X := by apply _root_.YangMills.Construction.ChartSymmetries.translateBy_translateBy_neg <;> assumption
theorem pathHolonomy_shiftField {j : ℕ} (X : F.GaugeField j) (x : F.Site j) (l : List PathStep) :
    pathHolonomy (shiftField u X) x l = pathHolonomy X (x + levelShift u j) l := by apply _root_.YangMills.Construction.ChartSymmetries.pathHolonomy_translateBy <;> assumption
theorem blockFit_shiftField {j : ℕ} (hj : j + 1 ≤ F.top) (W : F.GaugeField j) (V : F.GaugeField (j + 1))
    (c : F.Site (j + 1) × Fin 4) :
    blockFit (shiftField u W) (shiftField u V) c = blockFit W V (c.1 + levelShift u (j + 1), c.2) := by apply _root_.YangMills.Construction.ChartSymmetries.blockFit_translateBy <;> assumption
theorem minimalAction_shiftField (hs : ∀ i, 0 < F.extent i) {a : ℝ} :
    ∀ (j : ℕ), j ≤ F.top → ∀ X : F.GaugeField j,
      minimalAction a (finiteCells F) j (shiftField u X) = minimalAction a (finiteCells F) j X := by apply _root_.YangMills.Construction.ChartSymmetries.minimalAction_translateBy <;> assumption
theorem blockEnergy_shiftField (hs : ∀ i, 0 < F.extent i) {a : ℝ} (W : F.GaugeField F.depth)
    (V : F.GaugeField F.top) :
    blockEnergy a (finiteCells F) F.depth (shiftField u W) (shiftField u V) =
      blockEnergy a (finiteCells F) F.depth W V := by apply _root_.YangMills.Construction.ChartSymmetries.blockEnergy_translateBy <;> assumption
theorem levelShift_top : (levelShift u F.top : F.Cell) = siteOfCoords F.top u := by apply _root_.YangMills.Construction.ChartSymmetries.latticeTranslation_top <;> assumption
theorem cellCentre_add_levelShift (z : F.Cell) (h : Fin 4 → ℤ) :
    cellCentre F.depth z + siteOfCoords F.depth h + levelShift u F.depth =
      cellCentre F.depth (z + siteOfCoords F.top u) + siteOfCoords F.depth h := by apply _root_.YangMills.Construction.ChartSymmetries.cellCentre_add_latticeTranslation <;> assumption
theorem enclosingCell_add_levelShift (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (x : F.Site F.depth) :
    enclosingCell (x + levelShift u F.depth) = enclosingCell x + siteOfCoords F.top u := by apply _root_.YangMills.Construction.ChartSymmetries.enclosingCell_add_latticeTranslation <;> assumption
theorem cellOffset_add_levelShift (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (x : F.Site F.depth) :
    cellOffset (x + levelShift u F.depth) = cellOffset x := by
  obtain ⟨z, h, hh, rfl⟩ := exists_centre_add hL hs x
  rw [cellCentre_add_levelShift, cellOffset_centre_add hL hs _ _ hh, cellOffset_centre_add hL hs _ _ hh]
theorem chartedField_shiftField (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top) :
    chartedField (fun x i => w (x + levelShift u F.depth) i) (shiftField u V) =
      shiftField u (chartedField w V) := by apply _root_.YangMills.Construction.ChartSymmetries.chartedField_translateBy <;> assumption
theorem mem_chordBonds_add_levelShift (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (b : F.Site F.depth × Fin 4) :
    (b.1 + levelShift u F.depth, b.2) ∈ chordBonds (finiteCells F) ↔ b ∈ chordBonds (finiteCells F) := by apply _root_.YangMills.Construction.ChartSymmetries.add_latticeTranslation_mem_chordBonds_iff <;> assumption
theorem isMinimizingChart_shiftField (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) {a ρ : ℝ}
    {V : F.GaugeField F.top} {w : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (h : IsMinimizingChart a (finiteCells F) V ρ w) :
    IsMinimizingChart a (finiteCells F) (shiftField u V) ρ (fun x i => w (x + levelShift u F.depth) i) := by
  have hs0 : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  refine ⟨fun b hb => ?_, fun b hb => ?_, fun W' => ?_⟩
  · exact h.1 (b.1 + levelShift u F.depth, b.2) fun h' => hb ((mem_chordBonds_add_levelShift u hL hs b).mp h')
  · exact h.2.1 (b.1 + levelShift u F.depth, b.2) ((mem_chordBonds_add_levelShift u hL hs b).mpr hb)
  · rw [chartedField_shiftField u hL hs, blockEnergy_shiftField u hs0]
    have e2 : W' = shiftField u (shiftField (-u) W') := (shiftField_shiftField_neg u W').symm
    rw [e2, blockEnergy_shiftField u hs0]
    exact h.2.2 _
theorem minimizingCoordinates_shiftField (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) {a ρ N0 s : ℝ}
    (hπ : ρ < Real.pi) {V : F.GaugeField F.top} (hone : HasColdMinimizer a ρ N0 s (finiteCells F) V)
    (hone' : HasColdMinimizer a ρ N0 s (finiteCells F) (shiftField u V)) (x : F.Site F.depth) (i : Fin 4) :
    minimizingCoordinates a (finiteCells F) (shiftField u V) ρ x i =
      minimizingCoordinates a (finiteCells F) V ρ (x + levelShift u F.depth) i := by
  obtain ⟨w, hw, _, hl⟩ := minimizingCoordinates_eq hL hs hπ le_rfl hone
  obtain ⟨w', hw', _, hl'⟩ := minimizingCoordinates_eq hL hs hπ le_rfl hone'
  have hρ : IsMinimizingChart a (finiteCells F) V ρ w :=
    ⟨hw.1, fun b hb => (hw.2.1 b hb).trans (min_le_left _ _), hw.2.2⟩
  have hρ' : IsMinimizingChart a (finiteCells F) (shiftField u V) ρ w' :=
    ⟨hw'.1, fun b hb => (hw'.2.1 b hb).trans (min_le_left _ _), hw'.2.2⟩
  obtain ⟨w'', hw'', _, hu⟩ := hone'
  have h₂ : IsMinimizingChart a (finiteCells F) (shiftField u V) ρ w'' :=
    ⟨hw''.1, fun b hb => (hw''.2.1 b hb).trans (min_le_left _ _), hw''.2.2⟩
  have e1 := minimizingChart_unique hL hs hπ (isMinimizingChart_shiftField u hL hs hρ) h₂ hu
  have e2 := minimizingChart_unique hL hs hπ hρ' h₂ hu
  rw [hl, hl', e2, ← e1]
end Shift
section Mirror
variable {n : ℕ} [NeZero n]
theorem mirrorField_gaugeTransform {m : ℕ} (hm : 0 < m) (g : TorusSite n → UnitQuaternion) (y : TorusSite n)
    (V : TorusField n) :
    mirrorField m y (TorusFields.gaugeTransform g V) =
      TorusFields.gaugeTransform (fun z => g (y + siteOfInt (foldSite m z))) (mirrorField m y V) := by
  haveI : NeZero (4 * m) := ⟨by omega⟩
  funext z i
  have hslope : foldSite m (z + TorusFields.unitStep (4 * m) i) i = foldSite m z i + 1 ∨
      foldSite m (z + TorusFields.unitStep (4 * m) i) i = foldSite m z i - 1 := by
    rw [foldSite_add_unitStep_self hm]
    exact triangleFold_add_one m _
  have hev : ∀ b : Fin 4 → ℤ, y + siteOfInt b + TorusFields.unitStep n i =
      y + siteOfInt (b + Pi.single i 1) := by
    intro b
    rw [add_siteOfInt_add, unitStep_eq_siteOfInt]
  unfold mirrorField TorusFields.gaugeTransform
  beta_reduce
  by_cases hup : foldSite m (z + TorusFields.unitStep (4 * m) i) i = foldSite m z i + 1
  · rw [if_pos hup, if_pos hup, hev, foldSite_of_up hup]
  · rw [if_neg hup, if_neg hup]
    have e := foldSite_of_down (hslope.resolve_left hup)
    rw [hev, ← e]
    group
theorem mirrorField_translate {m : ℕ} (u : TorusSite n) (y : TorusSite n) (V : TorusField n) :
    mirrorField m (y - u) (TorusFields.translate u V) = mirrorField m y V := by
  funext z i
  have e : ∀ b : Fin 4 → ℤ, y - u + siteOfInt b + u = y + siteOfInt b := fun b => by abel
  unfold mirrorField TorusFields.translate
  simp only [e]
theorem readAtLevel_gaugeTransform {F : BlockFrame} {j N : ℕ} [NeZero N] (hp : ∀ i, F.period j i = N)
    (g : TorusSite N → UnitQuaternion) (W : TorusField N) :
    readAtLevel F j (TorusFields.gaugeTransform g W) =
      BlockAverages.gaugeTransform (fun c => g (toTorusSite N c)) (readAtLevel F j W) := by apply _root_.YangMills.Construction.SettingFits.readAtLevel_gaugeTransform <;> assumption
theorem frameCoord_of_large {ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters} {ρA : ℝ} {t m : ℕ} (V : TorusField n)
    (b : TorusBond (n * ℓ.side)) [NeZero (n * ℓ.side)] (hL : Odd ℓ.side) (hbig : 4 * m + 5 < n) :
    frameCoord ℓ ρA t m V b = minimizingBondCoordinate ℓ.coupling ρA
      (finiteCells (reflectedFrame (torusFrame ℓ.side t n) m))
      (reflectedBond (F := torusFrame ℓ.side t n) m
        (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth b.1, b.2))
      (reflectedField m (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top (parentBlock ℓ.side b.1))
        (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V)) := by
  have hn : ∀ i, (torusFrame ℓ.side t n).extent i = n := fun _ => rfl
  haveI : NeZero (n * (torusFrame ℓ.side t n).blockSide) := ‹_›
  have hcell : enclosingCell (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth b.1) =
      torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top (parentBlock ℓ.side b.1) :=
    enclosingCell_torusSiteInFrame hn b.1
  unfold frameCoord bondFrameCoord
  rw [if_pos (fun i => by rw [hn]; exact hbig)]
  unfold reflectedBondCoord
  simp only
  rw [hcell]
theorem frameCoord_of_small {ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters} {ρA : ℝ} {t m : ℕ} (V : TorusField n)
    (b : TorusBond (n * ℓ.side)) (hbig : ¬ 4 * m + 5 < n) :
    frameCoord ℓ ρA t m V b = minimizingBondCoordinate ℓ.coupling ρA (finiteCells (torusFrame ℓ.side t n))
      (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth b.1, b.2)
      (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V) := by
  unfold frameCoord bondFrameCoord
  rw [if_neg (fun h => hbig (h 0))]
theorem isCold_of_finiteCells {F : BlockFrame} (hn : ∀ i, F.extent i = n) {s : ℝ} {V : TorusField n}
    (h : BlockAverages.IsCold (finiteCells F) F.top s (readAtLevel F F.top V)) : TorusFields.IsCold s V := by
  classical
  intro z μ ν hlt
  have hs : ∀ i, 0 < F.extent i := fun i => by rw [hn]; exact Nat.pos_of_ne_zero (NeZero.ne n)
  have hp : ((torusSiteInFrame F F.top z, μ, ν) : F.Cell × Fin 4 × Fin 4) ∈
      innerPlaquettes (finiteCells F) F.top := by
    unfold innerPlaquettes
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨mem_sitesOfCells_top.mpr (_root_.YangMills.Construction.TopLevelSites.mem_finiteCells hs _), by simp⟩, hlt, ?_⟩
    intro c _
    exact mem_sitesOfCells_top.mpr (_root_.YangMills.Construction.TopLevelSites.mem_finiteCells hs _)
  have := h _ hp
  rwa [TopLevelSites.plaquetteDefect_readAtLevel_eq (period_top_of_extent hn),
    toTorusSite_torusSiteInFrame (period_top_of_extent hn)] at this
end Mirror
end Covariance
open Covariance in
theorem frameCovariance_holds (hc : ComplementOfThickenedLumpsRegular)
    (hcov : gaugeCovarianceStatement) : FrameCovariance := by
  intro ℓ δ lam ρA σA cg N hfit hch hσ t r r' n _ V S C s hr hsit b hb hy
  obtain ⟨δpos, _, _, _, ρle, _, _, Npos, hbody⟩ := hch
  have hπ : ρA < Real.pi := lt_of_le_of_lt ρle (by linarith [Real.pi_gt_three])
  obtain ⟨spos, sle, n4096, hF⟩ := stepSituation_regular_and_cold hc hfit hsit
  have hone : ∀ (F : BlockFrame) (S' : Finset F.Cell) (V' : F.GaugeField F.top), F.blockSide = ℓ.side →
      IsAdmissibleAmbient F → IsOrthantRegular S' 2047 →
      BlockAverages.IsCold S' F.top s V' → HasColdMinimizer ℓ.coupling ρA (N 0) s S' V' :=
    fun F S' V' h1 h2 h3 h4 =>
      (hbody F 2047 S' h1 h2 (by norm_num) h3 s V' spos (sle.trans hσ) h4).1
  have hn : ∀ i, (torusFrame ℓ.side t n).extent i = n := fun _ => rfl
  have hodd : Odd (torusFrame ℓ.side t n).blockSide := hfit.L_odd
  have h2 : 2 ≤ n := by omega
  have hs2 : ∀ i, 2 ≤ (torusFrame ℓ.side t n).extent i := fun i => by rw [hn]; omega
  have hs0 : ∀ i, 0 < (torusFrame ℓ.side t n).extent i := fun i => by rw [hn]; omega
  have hLpos : 0 < ℓ.side := hfit.L_odd.pos
  haveI hne0 : NeZero (n * ℓ.side) := ⟨(Nat.mul_pos (by omega) hLpos).ne'⟩
  haveI : NeZero (n * (torusFrame ℓ.side t n).blockSide) := hne0
  have hamb : IsAdmissibleAmbient (torusFrame ℓ.side t n) := Or.inr fun i => by rw [hn]; omega
  set m := r / 2 ^ 11 with hm
  have hm16 : 16 ≤ m := hr.frame_radius
  have hm0 : 0 < m := by omega
  haveI : NeZero (4 * m) := ⟨by omega⟩
  have hs' : ∀ i, 2 ≤ (reflectedFrame (torusFrame ℓ.side t n) m).extent i := fun i => by
    change 2 ≤ 4 * m
    omega
  have hs0' : ∀ i, 0 < (reflectedFrame (torusFrame ℓ.side t n) m).extent i := fun i => by
    have := hs' i; omega
  have hamb' : IsAdmissibleAmbient (reflectedFrame (torusFrame ℓ.side t n) m) := Or.inr fun i => by
    change 64 ≤ 4 * m
    omega
  have hp' : ∀ i, (reflectedFrame (torusFrame ℓ.side t n) m).period
      (reflectedFrame (torusFrame ℓ.side t n) m).top i = 4 * m :=
    fun i => by rw [period_top]; rfl
  have hne' : ∀ i, NeZero ((reflectedFrame (torusFrame ℓ.side t n) m).period
      (reflectedFrame (torusFrame ℓ.side t n) m).top i) :=
    fun i => ⟨by rw [hp']; exact NeZero.ne _⟩
  have hreg' := isOrthantRegular_finiteCells hs0' 2047
  have hregT := isOrthantRegular_finiteCells hs0 2047
  have hcell0 : ∀ o ∈ centredCube ℓ.side, enclosingCell
      (siteOfCoords (reflectedFrame (torusFrame ℓ.side t n) m).depth o :
        (reflectedFrame (torusFrame ℓ.side t n) m).Site (reflectedFrame (torusFrame ℓ.side t n) m).depth) = 0 := by
    intro o ho
    have e2 : (cellCentre (reflectedFrame (torusFrame ℓ.side t n) m).depth
        (0 : (reflectedFrame (torusFrame ℓ.side t n) m).Cell) :
        (reflectedFrame (torusFrame ℓ.side t n) m).Site (reflectedFrame (torusFrame ℓ.side t n) m).depth) = 0 := by
      funext l
      have := hne' l
      simp [cellCentre, siteOfCoords, siteCoords]
    have := enclosingCell_centre_add (F := reflectedFrame (torusFrame ℓ.side t n) m) hfit.L_odd hs' 0 o ho
    rwa [e2, zero_add] at this
  obtain ⟨hoc, _⟩ := centre_cellOffset hfit.L_odd hs2
    (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth b.1)
  refine ⟨fun g => ?_, fun u => ?_⟩
  · by_cases hbig : 4 * m + 5 < n
    · obtain ⟨_, hboxcold⟩ := stepSituation_box_of_not_mem hfit hr hsit hy
      have c₁ := isCold_reflectedField (F := torusFrame ℓ.side t n) hn hm0 spos V
        (parentBlock ℓ.side b.1) hboxcold
      have c₂ := isCold_reflectedField (F := torusFrame ℓ.side t n) hn hm0 spos
        (TorusFields.gaugeTransform g V) (parentBlock ℓ.side b.1)
        (fun a μ ν hlt hd => by rw [_root_.YangMills.Construction.TorusFields.curvature_gaugeTransform]; exact hboxcold a μ ν hlt hd)
      have one₁ := hone _ _ _ rfl hamb' hreg' c₁
      have one₂ := hone _ _ _ rfl hamb' hreg' c₂
      set γ' : (reflectedFrame (torusFrame ℓ.side t n) m).Cell → UnitQuaternion :=
        fun c => g (parentBlock ℓ.side b.1 + siteOfInt (foldSite m (toTorusSite (4 * m) c))) with hγ'
      have he : reflectedField m
          (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top (parentBlock ℓ.side b.1))
          (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top (TorusFields.gaugeTransform g V)) =
          BlockAverages.gaugeTransform γ' (reflectedField m
            (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top (parentBlock ℓ.side b.1))
            (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V)) := by
        rw [reflectedField_readAtLevel hn hm0, reflectedField_readAtLevel hn hm0,
          _root_.YangMills.Construction.StepFrames.Covariance.mirrorField_gaugeTransform hm0, _root_.YangMills.Construction.StepFrames.Covariance.readAtLevel_gaugeTransform hp']
      rw [he] at one₂
      have hco := _root_.YangMills.Construction.StepFrames.Covariance.minimizingCoordinates_gaugeTransform hcov hfit.L_odd hs' hπ γ' one₁ one₂
        (reflectedBond (F := torusFrame ℓ.side t n) m
          (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth b.1, b.2)).1
        (reflectedBond (F := torusFrame ℓ.side t n) m
          (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth b.1, b.2)).2
      have hγ0 : γ' (enclosingCell (reflectedBond (F := torusFrame ℓ.side t n) m
          (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth b.1, b.2)).1) =
          g (parentBlock ℓ.side b.1) := by
        have e1 := hcell0 _ hoc
        have e2 : (toTorusSite (4 * m) (0 : (reflectedFrame (torusFrame ℓ.side t n) m).Cell) :
            TorusSite (4 * m)) = 0 := by
          have := toTorusSite_siteOfCoords (F := reflectedFrame (torusFrame ℓ.side t n) m) hp' 0
          rw [siteOfCoords_zero] at this
          rw [this]
          funext l
          simp [siteOfInt]
        have e3 : foldSite m (0 : TorusSite (4 * m)) = 0 := by
          funext l
          simp [foldSite, triangleFold]
        have e4 : (siteOfInt 0 : TorusSite n) = 0 := by
          funext l
          simp [siteOfInt]
        simp only [hγ', reflectedBond, e1, e2, e3, e4, add_zero]
      rw [frameCoord_of_large _ _ hfit.L_odd hbig, frameCoord_of_large _ _ hfit.L_odd hbig, he]
      unfold minimizingBondCoordinate
      rw [hco, hγ0]
      rfl
    · have hS := stepSituation_eq_univ_of_small hfit hr hsit hy hbig
      obtain ⟨_, hcold⟩ := hF (torusFrame ℓ.side t n) hn
      rw [hS, cellsOfSites_univ hn] at hcold
      have hV := isCold_of_finiteCells hn hcold
      have hVg : TorusFields.IsCold s (TorusFields.gaugeTransform g V) := fun z μ ν hlt => by
        rw [_root_.YangMills.Construction.TorusFields.curvature_gaugeTransform]
        exact hV z μ ν hlt
      have one₁ := hone _ _ _ rfl hamb hregT hcold
      have one₂ := hone _ (finiteCells (torusFrame ℓ.side t n)) _ rfl hamb hregT (isCold_readAtLevel hn hVg)
      rw [_root_.YangMills.Construction.StepFrames.Covariance.readAtLevel_gaugeTransform (period_top_of_extent hn)] at one₂
      have hco := _root_.YangMills.Construction.StepFrames.Covariance.minimizingCoordinates_gaugeTransform hcov hfit.L_odd hs2 hπ _ one₁ one₂
        (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth b.1) b.2
      have hγ0 : toTorusSite n (enclosingCell
          (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth b.1)) =
          parentBlock ℓ.side b.1 := by
        have hcell : enclosingCell (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth b.1) =
            torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top (parentBlock ℓ.side b.1) :=
          enclosingCell_torusSiteInFrame hn b.1
        rw [hcell, toTorusSite_torusSiteInFrame (period_top_of_extent hn)]
      rw [frameCoord_of_small _ _ hbig, frameCoord_of_small _ _ hbig,
        _root_.YangMills.Construction.StepFrames.Covariance.readAtLevel_gaugeTransform (period_top_of_extent hn)]
      unfold minimizingBondCoordinate
      simp only
      rw [hco]
      change ((g (toTorusSite n _) : UnitQuaternion) : ℍ[ℝ]) * _ *
        (((g (toTorusSite n _))⁻¹ : UnitQuaternion) : ℍ[ℝ]) = _
      rw [hγ0]
  · have hpF : ∀ i, (torusFrame ℓ.side t n).period (torusFrame ℓ.side t n).depth i = n * ℓ.side :=
      fun i => period_depth_of_extent (F := torusFrame ℓ.side t n) hn i
    have hxx : torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth
        (b.1 - siteOfInt (fun i => (ℓ.side : ℤ) * u i)) + levelShift u (torusFrame ℓ.side t n).depth =
        torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth b.1 := by
      apply toTorusSite_injective hpF
      have e : (fun i => ((torusFrame ℓ.side t n).blockSide : ℤ) ^
          ((torusFrame ℓ.side t n).top - (torusFrame ℓ.side t n).depth) * u i) =
          fun i => (ℓ.side : ℤ) * u i := by
        funext i
        rw [_root_.YangMills.Construction.TopLevelSites.top_sub_depth, pow_one]
        rfl
      unfold levelShift
      rw [toTorusSite_add hpF, toTorusSite_torusSiteInFrame hpF, toTorusSite_torusSiteInFrame hpF,
        toTorusSite_siteOfCoords hpF, e]
      abel
    have hcl := enclosingCell_add_levelShift (F := torusFrame ℓ.side t n) u hfit.L_odd hs2
      (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth
        (b.1 - siteOfInt (fun i => (ℓ.side : ℤ) * u i)))
    have hof := cellOffset_add_levelShift (F := torusFrame ℓ.side t n) u hfit.L_odd hs2
      (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth
        (b.1 - siteOfInt (fun i => (ℓ.side : ℤ) * u i)))
    rw [hxx] at hcl hof
    have c1 : enclosingCell (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth b.1) =
        torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top (parentBlock ℓ.side b.1) :=
      enclosingCell_torusSiteInFrame hn b.1
    have c2 : enclosingCell (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth
        (b.1 - siteOfInt (fun i => (ℓ.side : ℤ) * u i))) =
        torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top
          (parentBlock ℓ.side (b.1 - siteOfInt (fun i => (ℓ.side : ℤ) * u i))) :=
      enclosingCell_torusSiteInFrame hn _
    rw [c1, c2] at hcl
    have hblock : parentBlock ℓ.side (b.1 - siteOfInt (fun i => (ℓ.side : ℤ) * u i)) =
        parentBlock ℓ.side b.1 - siteOfInt u := by
      have e := congrArg (toTorusSite n) hcl
      rw [toTorusSite_torusSiteInFrame (period_top_of_extent hn), toTorusSite_add (period_top_of_extent hn),
        toTorusSite_torusSiteInFrame (period_top_of_extent hn),
        toTorusSite_siteOfCoords (period_top_of_extent hn)] at e
      rw [e]
      abel
    by_cases hbig : 4 * m + 5 < n
    · have hmf : reflectedField m (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top
            (parentBlock ℓ.side (b.1 - siteOfInt (fun i => (ℓ.side : ℤ) * u i))))
            (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top (TorusFields.translate (siteOfInt u) V)) =
          reflectedField m (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top
            (parentBlock ℓ.side b.1))
            (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V) := by
        rw [reflectedField_readAtLevel hn hm0, reflectedField_readAtLevel hn hm0, hblock, mirrorField_translate]
      rw [frameCoord_of_large _ _ hfit.L_odd hbig, frameCoord_of_large _ _ hfit.L_odd hbig]
      rw [hmf]
      unfold reflectedBond
      simp only
      rw [hof]
    · have hS := stepSituation_eq_univ_of_small hfit hr hsit hy hbig
      obtain ⟨_, hcold⟩ := hF (torusFrame ℓ.side t n) hn
      rw [hS, cellsOfSites_univ hn] at hcold
      have hV := isCold_of_finiteCells hn hcold
      have hVs : TorusFields.IsCold s (TorusFields.translate (siteOfInt u) V) := fun z μ ν hlt => by
        rw [curvature_translate]
        exact hV _ μ ν hlt
      have hshift : readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top
          (TorusFields.translate (siteOfInt u) V) =
          shiftField u (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V) := by
        funext c i
        change V (toTorusSite n c + siteOfInt u) i =
          V (toTorusSite n (c + levelShift u (torusFrame ℓ.side t n).top)) i
        rw [levelShift_top, toTorusSite_add (period_top_of_extent hn),
          toTorusSite_siteOfCoords (period_top_of_extent hn)]
      have one₁ := hone _ _ _ rfl hamb hregT hcold
      have one₂ := hone _ (finiteCells (torusFrame ℓ.side t n)) _ rfl hamb hregT (isCold_readAtLevel hn hVs)
      rw [hshift] at one₂
      have hco := minimizingCoordinates_shiftField u hfit.L_odd hs2 hπ one₁ one₂
        (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth
          (b.1 - siteOfInt (fun i => (ℓ.side : ℤ) * u i))) b.2
      rw [frameCoord_of_small _ _ hbig, frameCoord_of_small _ _ hbig, hshift]
      unfold minimizingBondCoordinate
      simp only
      rw [hco, hxx]
end StepFrames
end YangMills.Construction
end
