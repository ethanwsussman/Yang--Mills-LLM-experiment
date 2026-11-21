import YangMills.Construction.ResponseInTheExpansion.RemainderOfTheResponseReturnsProof
import YangMills.Construction.ClusterExpansionOfAStep.ColdIntegralIsTheColdStepProof
import YangMills.Construction.ResponseInTheExpansion.BlockRemainderAboveTheFrameProof
import YangMills.Construction.ResponseInTheExpansion.ColdLawOfAStepIsALaw
import YangMills.Construction.ResponseInTheExpansion.ScoresAboveTheFrames
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction
namespace ColdFrameRestriction
theorem zmod_cast_intCast (P m : ℕ) (h : P = m) (z : ℤ) :
    ((((z : ZMod m)).cast : ℤ) : ZMod P) = (z : ZMod P) := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.cast_intCast_of_eq <;> assumption
variable {H : BlockAverages.BlockFrame} {m : ℕ}
theorem toTorusSite_torusSiteInFrame (j : ℕ) (hm : ∀ i, H.period j i = m) (x : TorusFields.TorusSite m) :
    TorusLumps.toTorusSite m (StepCosts.torusSiteInFrame H j x) = x := by apply _root_.YangMills.Construction.TorusLevels.toTorusSite_torusSiteInFrame <;> assumption
theorem torusSiteInFrame_toTorusSite (j : ℕ) (hm : ∀ i, H.period j i = m) (y : H.Site j) :
    StepCosts.torusSiteInFrame H j (TorusLumps.toTorusSite m y) = y := by apply _root_.YangMills.Construction.TorusLevels.torusSiteInFrame_toTorusSite <;> assumption
theorem torusSiteInFrame_add (j : ℕ) (hm : ∀ i, H.period j i = m) (x y : TorusFields.TorusSite m) :
    StepCosts.torusSiteInFrame H j (x + y) =
      StepCosts.torusSiteInFrame H j x + StepCosts.torusSiteInFrame H j y := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.torusSiteInFrame_add <;> assumption
theorem torusSiteInFrame_unitStep (j : ℕ) (hm : ∀ i, H.period j i = m) (i : Fin 4) :
    StepCosts.torusSiteInFrame H j (TorusFields.unitStep m i) = BlockAverages.unitStep j i := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.torusSiteInFrame_unitStep <;> assumption
theorem torusSiteInFrame_neg (j : ℕ) (hm : ∀ i, H.period j i = m) (x : TorusFields.TorusSite m) :
    StepCosts.torusSiteInFrame H j (-x) = - StepCosts.torusSiteInFrame H j x := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.torusSiteInFrame_neg <;> assumption
theorem torusSiteInFrame_sub (j : ℕ) (hm : ∀ i, H.period j i = m) (x y : TorusFields.TorusSite m) :
    StepCosts.torusSiteInFrame H j (x - y) =
      StepCosts.torusSiteInFrame H j x - StepCosts.torusSiteInFrame H j y := by
  rw [sub_eq_add_neg, torusSiteInFrame_add j hm, torusSiteInFrame_neg j hm, sub_eq_add_neg]
def torusPathHolonomy (W : TorusFields.TorusField m) :
    TorusFields.TorusSite m → List BlockAverages.PathStep → BlockAverages.UnitQuaternion
  | _, [] => 1
  | x, st :: r =>
    (if st.2 then W x st.1 else (W (x - TorusFields.unitStep m st.1) st.1)⁻¹) *
      torusPathHolonomy W
        (x + (if st.2 then TorusFields.unitStep m st.1 else - TorusFields.unitStep m st.1)) r
theorem readAtLevel_torusSiteInFrame (j : ℕ) (hm : ∀ i, H.period j i = m) (W : TorusFields.TorusField m)
    (x : TorusFields.TorusSite m) (i : Fin 4) :
    TorusFields.readAtLevel H j W (StepCosts.torusSiteInFrame H j x) i = W x i := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.readAtLevel_torusSiteInFrame <;> assumption
theorem pathHolonomy_readAtLevel (j : ℕ) (hm : ∀ i, H.period j i = m) (W : TorusFields.TorusField m)
    (x : TorusFields.TorusSite m) (l : List BlockAverages.PathStep) :
    BlockAverages.pathHolonomy (TorusFields.readAtLevel H j W) (StepCosts.torusSiteInFrame H j x) l =
      torusPathHolonomy W x l := by
  induction l generalizing x with
  | nil => rfl
  | cons st r ih =>
    have hv : BlockAverages.stepDisplacement j st + StepCosts.torusSiteInFrame H j x =
        StepCosts.torusSiteInFrame H j
          (x + (if st.2 then TorusFields.unitStep m st.1 else - TorusFields.unitStep m st.1)) := by
      rw [torusSiteInFrame_add j hm]
      rcases st with ⟨i, b⟩
      cases b
      · simp [BlockAverages.stepDisplacement, torusSiteInFrame_neg j hm, torusSiteInFrame_unitStep j hm,
          add_comm]
      · simp [BlockAverages.stepDisplacement, torusSiteInFrame_unitStep j hm, add_comm]
    simp only [BlockAverages.pathHolonomy, torusPathHolonomy]
    rw [add_comm (StepCosts.torusSiteInFrame H j x), hv, ih]
    congr 1
    rcases st with ⟨i, b⟩
    cases b
    · simp only [BlockAverages.linkValue, Bool.false_eq_true, if_false]
      rw [← torusSiteInFrame_unitStep j hm, ← torusSiteInFrame_sub j hm, readAtLevel_torusSiteInFrame j hm]
    · simp only [BlockAverages.linkValue, if_true]
      rw [readAtLevel_torusSiteInFrame j hm]
section Blocks
variable {H : BlockAverages.BlockFrame} {n : ℕ}
theorem period_depth (hs : ∀ i, H.extent i = n) (i : Fin 4) : H.period H.depth i = n * H.blockSide := by
  simp [BlockAverages.BlockFrame.period, hs]
theorem period_top (hs : ∀ i, H.extent i = n) (i : Fin 4) : H.period H.top i = n := by
  simp [BlockAverages.BlockFrame.period, hs]
theorem zmod_cast_cast_int (P m : ℕ) (h : P = m) (a : ZMod m) :
    ((((a.cast : ℤ) : ZMod P)).cast : ℤ) = (a.cast : ℤ) := by
  subst h; simp
theorem siteCoords_torusSiteInFrame {m : ℕ} (j : ℕ) (hm : ∀ i, H.period j i = m)
    (x : TorusFields.TorusSite m) (k : Fin 4) :
    BlockAverages.siteCoords (StepCosts.torusSiteInFrame H j x) k = ((x k).cast : ℤ) :=
  zmod_cast_cast_int _ _ (hm k) (x k)
def blockCentre (L : ℕ) (Y : TorusFields.TorusSite n) : TorusFields.TorusSite (n * L) :=
  fun i => (((L : ℤ) * ((Y i).cast : ℤ) : ℤ) : ZMod (n * L))
theorem enclosingCell_torusSiteInFrame (hs : ∀ i, H.extent i = n) (x : TorusFields.TorusSite (n * H.blockSide)) :
    BlockAverages.enclosingCell (StepCosts.torusSiteInFrame H H.depth x) =
      StepCosts.torusSiteInFrame H H.top (TorusLumps.parentBlock H.blockSide x) := by
  funext k
  have he : H.top - H.depth = 1 := by simp [BlockAverages.BlockFrame.top]
  have h1 := siteCoords_torusSiteInFrame (H := H) H.depth (period_depth hs) x k
  show ((((BlockAverages.siteCoords (StepCosts.torusSiteInFrame H H.depth x) k +
      ((H.blockSide : ℤ) ^ (H.top - H.depth) - 1) / 2) /
    (H.blockSide : ℤ) ^ (H.top - H.depth) : ℤ)) : ZMod (H.period H.top k)) = _
  rw [h1, he, pow_one]
  exact (zmod_cast_intCast _ _ (period_top hs k) _).symm
theorem torusSiteInFrame_injective {m : ℕ} (j : ℕ) (hm : ∀ i, H.period j i = m) :
    Function.Injective (StepCosts.torusSiteInFrame (n := m) H j) := by
  intro x y h
  rw [← toTorusSite_torusSiteInFrame j hm x, h, toTorusSite_torusSiteInFrame j hm y]
theorem refineSite_torusSiteInFrame (hs : ∀ i, H.extent i = n) (Y : TorusFields.TorusSite n) :
    BlockAverages.refineSite (j := H.depth) (StepCosts.torusSiteInFrame H H.top Y) =
      StepCosts.torusSiteInFrame H H.depth (blockCentre H.blockSide Y) := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.refineSite_torusSiteInFrame <;> assumption
def blockContourAverage (L : ℕ) (W : TorusFields.TorusField (n * L)) (Y : TorusFields.TorusSite n)
    (i : Fin 4) : ℍ[ℝ] :=
  (1 / (24 * (L : ℝ) ^ 4)) • ∑ h ∈ BlockAverages.centredCube L, ∑ π : Equiv.Perm (Fin 4),
    ((torusPathHolonomy W (blockCentre L Y) (BlockAverages.bondContour L h π i) :
      BlockAverages.UnitQuaternion) : ℍ[ℝ])
theorem contourAverage_readAtLevel (hs : ∀ i, H.extent i = n) (W : TorusFields.TorusField (n * H.blockSide))
    (Y : TorusFields.TorusSite n) (i : Fin 4) :
    BlockAverages.contourAverage (j := H.depth) (TorusFields.readAtLevel H H.depth W)
        (StepCosts.torusSiteInFrame H H.top Y, i) = blockContourAverage H.blockSide W Y i := by
  unfold BlockAverages.contourAverage blockContourAverage
  simp only [refineSite_torusSiteInFrame hs, pathHolonomy_readAtLevel H.depth (period_depth hs)]
end Blocks
section Plain
variable {H : BlockAverages.BlockFrame} {n : ℕ}
theorem contourMean_no_lumps (hs : ∀ i, H.extent i = n) (hn : 0 < n) (hL : Odd H.blockSide) (J₀ : ℕ)
    (W : H.GaugeField H.depth) (c : H.Cell × Fin 4) :
    LumpContours.contourMean J₀ (∅ : Finset (Finset (H.Site H.depth)))
        (fun y => BlockAverages.cellCentre H.depth y) W c =
      BlockAverages.contourAverage (j := H.depth) W c := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.contourMean_empty <;> assumption
end Plain
section Field
variable {R : StepSettings.StepSetup} {n : ℕ} [NeZero n]
abbrev coarseFrame (R : StepSettings.StepSetup) (n : ℕ) : BlockAverages.BlockFrame :=
  TorusFields.torusFrame R.params.side R.depth n
theorem mem_finiteCells (z : (coarseFrame R n).Cell) : z ∈ ColdStepAtMirrorFrames.finiteCells (coarseFrame R n) := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.mem_finiteCells <;> assumption
abbrev topField (V : TorusFields.TorusField n) : (coarseFrame R n).GaugeField (coarseFrame R n).top :=
  TorusFields.readAtLevel (coarseFrame R n) (coarseFrame R n).top V
end Field
section Cost
variable {R : StepSettings.StepSetup} {n : ℕ} [NeZero n]
omit [NeZero n] in
theorem stepHotLumps_of_cold (ℓ : TorusLumps.StepParameters) (W : TorusFields.TorusField (n * ℓ.side))
    (hW : TorusFields.IsCold ℓ.threshold W) : StepCosts.stepHotLumps ℓ W = ∅ := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.stepHotLumps_eq_empty <;> assumption
omit [NeZero n] in
theorem torusHotSites_of_cold (ℓ : TorusLumps.StepParameters) (W : TorusFields.TorusField (n * ℓ.side))
    (hW : TorusFields.IsCold ℓ.threshold W) : TorusLumps.torusHotSites ℓ W = ∅ := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.torusHotSites_eq_empty <;> assumption
theorem thickening_empty (m : ℕ) : TorusLumps.thickening m (∅ : Finset (TorusFields.TorusSite n)) = ∅ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ColdChart.thickening_empty <;> assumption
def blockFitOnTorus (L : ℕ) (W : TorusFields.TorusField (n * L)) (V : TorusFields.TorusField n)
    (Y : TorusFields.TorusSite n) (i : Fin 4) : ℝ :=
  ‖blockContourAverage L W Y i‖ - (blockContourAverage L W Y i * ((V Y i)⁻¹ : BlockAverages.UnitQuaternion)).re
omit [NeZero n] in
theorem blockFit_readAtLevel {H : BlockAverages.BlockFrame} (hs : ∀ i, H.extent i = n)
    (W : TorusFields.TorusField (n * H.blockSide)) (V : TorusFields.TorusField n) (Y : TorusFields.TorusSite n)
    (i : Fin 4) :
    BlockAverages.blockFit (j := H.depth) (TorusFields.readAtLevel H H.depth W) (TorusFields.readAtLevel H H.top V)
        (StepCosts.torusSiteInFrame H H.top Y, i) = blockFitOnTorus H.blockSide W V Y i := by
  unfold BlockAverages.blockFit blockFitOnTorus
  rw [contourAverage_readAtLevel hs]
  have h := readAtLevel_torusSiteInFrame (H := H) H.top (period_top hs) V Y i
  simp only [h]
theorem meanNorm_of_cold (ℓ : TorusLumps.StepParameters) (hodd : Odd ℓ.side) (W : TorusFields.TorusField (n * ℓ.side))
    (hW : TorusFields.IsCold ℓ.threshold W) (c : TorusFields.TorusBond n) :
    StepCosts.meanNorm ℓ W (fun y => BlockAverages.cellCentre 0 y) c = ‖blockContourAverage ℓ.side W c.1 c.2‖ := by
  unfold StepCosts.meanNorm
  rw [stepHotLumps_of_cold ℓ W hW]
  have h := contourMean_no_lumps (H := TorusLumps.stepBlockFrame ℓ.side n) (n := n) (fun _ => rfl)
    (Nat.pos_of_ne_zero (NeZero.ne n)) hodd ℓ.baseDepth (TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side n) 0 W)
    (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 c.1, c.2)
  exact (congrArg norm h).trans
    (congrArg _ (contourAverage_readAtLevel (H := TorusLumps.stepBlockFrame ℓ.side n) (fun _ => rfl) W c.1 c.2))
end Cost
section Sums
variable {R : StepSettings.StepSetup} {n : ℕ} [NeZero n]
theorem mem_sitesOfCells_top (z : (coarseFrame R n).Cell) :
    z ∈ BlockAverages.sitesOfCells (ColdStepAtMirrorFrames.finiteCells (coarseFrame R n)) (coarseFrame R n).top := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.mem_sitesOfCells_top <;> assumption
theorem mem_innerBonds_top (c : (coarseFrame R n).Site (coarseFrame R n).top × Fin 4) :
    c ∈ BlockAverages.innerBonds (ColdStepAtMirrorFrames.finiteCells (coarseFrame R n)) (coarseFrame R n).top := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.mem_innerBonds_top <;> assumption
omit [NeZero n] in
theorem unitStep_ne_zero (hn : 2 ≤ n) (i : Fin 4) : TorusFields.unitStep n i ≠ 0 := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.unitStep_ne_zero <;> assumption
omit [NeZero n] in
theorem frameUnitStep_top_ne_zero (hn : 2 ≤ n) (i : Fin 4) :
    BlockAverages.unitStep (F := coarseFrame R n) (coarseFrame R n).top i ≠ 0 := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.unitStep_top_ne_zero <;> assumption
open Classical in
theorem sum_bonds_at_cell (hn : 2 ≤ n) (g : (coarseFrame R n).Site (coarseFrame R n).top × Fin 4 → ℝ)
    (Y : (coarseFrame R n).Cell) :
    ∑ c ∈ (BlockAverages.innerBonds (ColdStepAtMirrorFrames.finiteCells (coarseFrame R n)) (coarseFrame R n).top).filter
        (fun c => c.1 = Y ∨ c.1 + BlockAverages.unitStep (coarseFrame R n).top c.2 = Y), g c =
      ∑ i : Fin 4, (g (Y, i) + g (Y - BlockAverages.unitStep (coarseFrame R n).top i, i)) := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.sum_bonds_touching <;> assumption
open Classical in
theorem sum_sites_in_block (hcov : ColdStepAtMirrorFrames.BlocksCoverLowerLevel) (hodd : Odd R.params.side)
    (g : (coarseFrame R n).Site (coarseFrame R n).depth → ℝ) (Y : TorusFields.TorusSite n) :
    ∑ y ∈ (BlockAverages.sitesOfCells (ColdStepAtMirrorFrames.finiteCells (coarseFrame R n)) (coarseFrame R n).depth).filter
        (fun y => BlockAverages.enclosingCell y = StepCosts.torusSiteInFrame (coarseFrame R n) (coarseFrame R n).top Y),
        g y =
      ∑ x ∈ TorusLumps.sitesInBlocks R.params.side {Y},
        g (StepCosts.torusSiteInFrame (coarseFrame R n) (coarseFrame R n).depth x) := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.sum_sites_in_cell <;> assumption
end Sums
section Read
variable {R : StepSettings.StepSetup} {n : ℕ} [NeZero n]
omit [NeZero n] in
theorem torusSiteInFrame_sub_unitStep (Y : TorusFields.TorusSite n) (i : Fin 4) :
    StepCosts.torusSiteInFrame (coarseFrame R n) (coarseFrame R n).top Y -
        BlockAverages.unitStep (coarseFrame R n).top i =
      StepCosts.torusSiteInFrame (coarseFrame R n) (coarseFrame R n).top (Y - TorusFields.unitStep n i) := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.torusSiteInFrame_sub_unitStep <;> assumption
theorem blockCost_eq_cellEnergyShare (hcov : ColdStepAtMirrorFrames.BlocksCoverLowerLevel) (hodd : Odd R.params.side)
    (hn : 2 ≤ n) (W : TorusFields.TorusField (n * R.params.side)) (hW : TorusFields.IsCold R.params.threshold W)
    (hsh : ∀ y, StepCosts.levelShare R.params.coupling R.params.side R.depth Finset.univ y W =
      ColdStepAtMirrorFrames.minimalSiteShare (F := coarseFrame R n) R.params.coupling
        (StepCosts.torusSiteInFrame (coarseFrame R n) (coarseFrame R n).depth y)
        (TorusFields.readAtLevel (coarseFrame R n) (coarseFrame R n).depth W))
    (V : TorusFields.TorusField n)
    (w : (coarseFrame R n).Site (coarseFrame R n).depth → Fin 4 → BlockAverages.imaginaryQuaternions)
    (hX : BlockAverages.chartedField w (topField (R := R) V) =
      TorusFields.readAtLevel (coarseFrame R n) (coarseFrame R n).depth W) (Y : TorusFields.TorusSite n) :
    StepCosts.blockCost R.params R.depth W V (fun y => BlockAverages.cellCentre 0 y) Y =
      ColdStepAtMirrorFrames.cellEnergyShare R.params.coupling
        (StepCosts.torusSiteInFrame (coarseFrame R n) (coarseFrame R n).top Y) w (topField V) := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.blockCost_eq_cellEnergyShare <;> assumption
end Read
section Pointwise
variable {R : StepSettings.StepSetup} {n : ℕ} [NeZero n] {V : TorusFields.TorusField n}
theorem restrictToTorus_readAtLevel {H : BlockAverages.BlockFrame} {j m : ℕ} (hm : ∀ i, H.period j i = m)
    (W : TorusFields.TorusField m) :
    ColdStepAtMirrorFrames.restrictToTorus m (TorusFields.readAtLevel H j W) = W := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.restrictToTorus_readAtLevel <;> assumption
omit [NeZero n] in
theorem localFamilyOfDensity_readAtLevel (g : TorusLumps.LocalDensity) (x : TorusFields.TorusSite (n * R.params.side))
    (W : TorusFields.TorusField (n * R.params.side)) :
    ColdStepAtMirrorFrames.localFamilyOfDensity g (coarseFrame R n)
        (StepCosts.torusSiteInFrame (coarseFrame R n) (coarseFrame R n).depth x)
        (TorusFields.readAtLevel (coarseFrame R n) (coarseFrame R n).depth W) =
      g (n * R.params.side) x W := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.localFamilyOfDensity_readAtLevel <;> assumption
omit [NeZero n] in
theorem subtractTrivial_readAtLevel (g : TorusLumps.LocalDensity) (x : TorusFields.TorusSite (n * R.params.side))
    (W : TorusFields.TorusField (n * R.params.side)) :
    ColdStepAtMirrorFrames.subtractTrivial (ColdStepAtMirrorFrames.localFamilyOfDensity g) (coarseFrame R n)
        (StepCosts.torusSiteInFrame (coarseFrame R n) (coarseFrame R n).depth x)
        (TorusFields.readAtLevel (coarseFrame R n) (coarseFrame R n).depth W) =
      TorusLumps.centered g (n * R.params.side) x W := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.subtractTrivial_readAtLevel <;> assumption
theorem cellsOfSites_univ :
    TorusFields.cellsOfSites (coarseFrame R n) (Finset.univ : Finset (TorusFields.TorusSite n)) =
      ColdStepAtMirrorFrames.finiteCells (coarseFrame R n) := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.cellsOfSites_univ <;> assumption
theorem levelShare_top (Y : TorusFields.TorusSite n) :
    StepCosts.levelShare R.params.coupling R.params.side (R.depth + 1) Finset.univ Y V =
      BlockAverages.minimalCellShare R.params.coupling (ColdStepAtMirrorFrames.finiteCells (coarseFrame R n))
        (StepCosts.torusSiteInFrame (coarseFrame R n) (coarseFrame R n).top Y) (topField (R := R) V) := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.levelShare_top <;> assumption
end Pointwise
section Frames
variable {F : BlockAverages.BlockFrame} (a ρA : ℝ) (m : ℕ) (W : F.GaugeField F.top)
  (k : ColdStepAtMirrorFrames.StepVariable (ColdStepAtMirrorFrames.finiteCells F))
theorem interpolatedField_one :
    Interpolation.interpolatedField 1 a ρA m W k = ColdStepAtMirrorFrames.fieldAboveFrame false a ρA m W k := by apply _root_.YangMills.SharedProofs.p24311 <;> assumption
end Frames
end ColdFrameRestriction
namespace ResponseInTheExpansion
namespace ScoreBounds
open ColdFrameRestriction
variable {R : StepSettings.StepSetup} {n : ℕ} [NeZero n]
theorem readAtLevel_restrictToTorus (X : (coarseFrame R n).GaugeField (coarseFrame R n).depth) :
    TorusFields.readAtLevel (coarseFrame R n) (coarseFrame R n).depth
      (ColdStepAtMirrorFrames.restrictToTorus (n * R.params.side) X) = X := by apply _root_.YangMills.Construction.ResponseInTheExpansion.RemainderBounds.readAtLevel_restrictToTorus <;> assumption
theorem readAtLevel_coldFieldAboveFrames (V : TorusFields.TorusField n)
    (k : ColdStepAtMirrorFrames.StepVariable (ColdStepAtMirrorFrames.finiteCells (coarseFrame R n))) :
    TorusFields.readAtLevel (coarseFrame R n) (coarseFrame R n).depth (ResponseInTheExpansion.coldFieldAboveFrames R V k) =
      Interpolation.interpolatedField 1 R.params.coupling R.anchorRadius R.frameReach
        (ResponseInTheExpansion.coldTopField R V) k :=
  readAtLevel_restrictToTorus _
theorem meanNorm_eq_contourAverageSize (hodd : Odd R.params.side) (V : TorusFields.TorusField n)
    (k : ColdStepAtMirrorFrames.StepVariable (ColdStepAtMirrorFrames.finiteCells (coarseFrame R n)))
    (hW : TorusFields.IsCold R.params.threshold (ResponseInTheExpansion.coldFieldAboveFrames R V k))
    (c : TorusFields.TorusBond n) :
    StepCosts.meanNorm R.params (ResponseInTheExpansion.coldFieldAboveFrames R V k)
        (StepSettings.coldChartSetting R V).bases c =
      (ResponseInTheExpansion.coldHalfLawOf R).contourAverageSize (ResponseInTheExpansion.torusBondInFrame R c) k
        (ResponseInTheExpansion.coldTopField R V) := by
  rw [show (StepSettings.coldChartSetting R V).bases = fun y => BlockAverages.cellCentre 0 y from rfl,
    meanNorm_of_cold _ hodd _ hW c]
  show _ = ‖BlockAverages.contourAverage (Interpolation.interpolatedField 1 R.params.coupling R.anchorRadius
    R.frameReach (ResponseInTheExpansion.coldTopField R V) k) (ResponseInTheExpansion.torusBondInFrame R c)‖
  rw [← readAtLevel_coldFieldAboveFrames]
  exact congrArg _ (contourAverage_readAtLevel (H := coarseFrame R n) (n := n) (fun _ => rfl) _ c.1 c.2).symm
theorem meanNorm_le_one (W : TorusFields.TorusField (n * R.params.side))
    (b : StepCosts.BaseChoice R.params.side n) (c : TorusFields.TorusBond n) :
    StepCosts.meanNorm R.params W b c ≤ 1 :=
  WeightedResponses.norm_contourMean_le _ _ _ _ _
theorem abs_bondFit_le_two (W : TorusFields.TorusField (n * R.params.side)) (V : TorusFields.TorusField n)
    (b : StepCosts.BaseChoice R.params.side n) (c : TorusFields.TorusBond n) :
    |StepCosts.bondFit R.params W V b c| ≤ 2 := by
  have h1 : ‖LumpContours.contourMean R.params.baseDepth (StepCosts.stepHotLumps R.params W) b
      (TorusFields.readAtLevel (TorusLumps.stepBlockFrame R.params.side n) 0 W)
      (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame R.params.side n) 1 c.1, c.2)‖ ≤ 1 :=
    WeightedResponses.norm_contourMean_le _ _ _ _ _
  unfold StepCosts.bondFit LumpContours.contourFit
  refine (abs_sub _ _).trans ?_
  rw [abs_norm]
  have := WeightedResponses.abs_re_mul_inv_le
    (LumpContours.contourMean R.params.baseDepth (StepCosts.stepHotLumps R.params W) b
      (TorusFields.readAtLevel (TorusLumps.stepBlockFrame R.params.side n) 0 W)
      (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame R.params.side n) 1 c.1, c.2))
    (TorusFields.readAtLevel (TorusLumps.stepBlockFrame R.params.side n) 1 V
      (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame R.params.side n) 1 c.1) c.2)
  linarith
theorem bondScore_eq_of_cold (hscore : WeightedResponses.BondScoreProperties)
    (hweyl : ColdStepAtMirrorFrames.WeylIntegrationFormula) (htail : WeightedResponses.ScoreRemainderExpansion)
    (hfit : R.params.Admissible) (hodd : Odd R.params.side) (V : TorusFields.TorusField n)
    (k : ColdStepAtMirrorFrames.StepVariable (ColdStepAtMirrorFrames.finiteCells (coarseFrame R n)))
    (hW : TorusFields.IsCold R.params.threshold (ResponseInTheExpansion.coldFieldAboveFrames R V k))
    (c : TorusFields.TorusBond n)
    (hr : 1 / 2 ≤ StepCosts.meanNorm R.params (ResponseInTheExpansion.coldFieldAboveFrames R V k)
      (StepSettings.coldChartSetting R V).bases c)
    (hax : 2 ≤ R.params.coupling * R.coupling) :
    WeightedResponses.bondScore R.params R.coupling (ResponseInTheExpansion.coldFieldAboveFrames R V k) V
        (StepSettings.coldChartSetting R V).bases c =
      StepCosts.bondFit R.params (ResponseInTheExpansion.coldFieldAboveFrames R V k) V
          (StepSettings.coldChartSetting R V).bases c - 3 / (2 * R.params.coupling * R.coupling) -
        (R.coupling ^ 2)⁻¹ * (ResponseInTheExpansion.coldHalfLawOf R).scoreRemainderAt
          (ResponseInTheExpansion.torusBondInFrame R c) k (ResponseInTheExpansion.coldTopField R V) := by
  have e1 := (hscore R.params hfit R.coupling n (StepSettings.coldChartSetting R V).bases c).1
    (ResponseInTheExpansion.coldFieldAboveFrames R V k)
  have hom : TorusLumps.logPartitionGap = ColdStepAtMirrorFrames.haarGap := funext hweyl.2.2
  unfold WeightedResponses.bondScore
  rw [e1, hom]
  have hs := meanNorm_eq_contourAverageSize hodd V k hW c
  set r := StepCosts.meanNorm R.params (ResponseInTheExpansion.coldFieldAboveFrames R V k)
    (StepSettings.coldChartSetting R V).bases c with hrdef
  have e2 := htail.1 (ResponseInTheExpansion.coldHalfLawOf R) r (by
    show 1 ≤ R.params.coupling * R.coupling * r
    nlinarith) (by linarith)
  have e3 : (ResponseInTheExpansion.coldHalfLawOf R).scoreRemainderAt (ResponseInTheExpansion.torusBondInFrame R c) k
      (ResponseInTheExpansion.coldTopField R V) = (ResponseInTheExpansion.coldHalfLawOf R).scoreRemainder r := by
    unfold WeightedResponses.ColdHalfLaw.scoreRemainderAt
    rw [hs]
  rw [e3]
  have e4 : r * deriv ColdStepAtMirrorFrames.haarGap (R.params.coupling * R.coupling * r) =
      3 / (2 * R.params.coupling * R.coupling) +
        (R.coupling ^ 2)⁻¹ * (ResponseInTheExpansion.coldHalfLawOf R).scoreRemainder r := e2
  rw [e4]
  ring
theorem integrable_mul_of_bounded {Z : Type} [MeasurableSpace Z] {μ : Measure Z} {d g : Z → ℝ}
    (hd : Integrable d μ) (hg : Measurable g) {B : ℝ} (hb : ∀ k, |g k| ≤ B) :
    Integrable (fun k => g k * d k) μ :=
  hd.bdd_mul (c := B) hg.aestronglyMeasurable (Filter.Eventually.of_forall fun k => by
    rw [Real.norm_eq_abs]
    exact hb k)
theorem integrable_bondScore_mul (hscore : WeightedResponses.BondScoreProperties)
    (hM : TorusLumps.MeasurableContourMeanStatement) (hfit : R.params.Admissible) (V : TorusFields.TorusField n)
    (c : TorusFields.TorusBond n) (hd : Integrable (ResponseInTheExpansion.coldHalfDensity R V))
    (hm : Measurable (ResponseInTheExpansion.coldFieldAboveFrames R V)) :
    Integrable fun k => WeightedResponses.bondScore R.params R.coupling (ResponseInTheExpansion.coldFieldAboveFrames R V k) V
      (StepSettings.coldChartSetting R V).bases c * ResponseInTheExpansion.coldHalfDensity R V k := by
  have hsc := hscore R.params hfit R.coupling n (StepSettings.coldChartSetting R V).bases c
  have hf : Measurable fun W : TorusFields.TorusField (n * R.params.side) =>
      StepCosts.bondFit R.params W V (StepSettings.coldChartSetting R V).bases c :=
    hM R.params n (StepSettings.coldChartSetting R V).bases
      (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame R.params.side n) 1 c.1, c.2)
      (fun q => ‖q‖ - (q * ((((TorusFields.readAtLevel (TorusLumps.stepBlockFrame R.params.side n) 1 V)
        (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame R.params.side n) 1 c.1) c.2)⁻¹ :
          BlockAverages.UnitQuaternion) : ℍ[ℝ])).re)
      (continuous_norm.sub (Quaternion.continuous_re.comp (continuous_id.mul continuous_const)))
  have hr : Measurable fun W : TorusFields.TorusField (n * R.params.side) =>
      StepCosts.meanNorm R.params W (StepSettings.coldChartSetting R V).bases c :=
    hM R.params n (StepSettings.coldChartSetting R V).bases
      (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame R.params.side n) 1 c.1, c.2) (fun q => ‖q‖)
      continuous_norm
  have hs : Measurable fun W : TorusFields.TorusField (n * R.params.side) =>
      WeightedResponses.bondScore R.params R.coupling W V (StepSettings.coldChartSetting R V).bases c := by
    have e : (fun W : TorusFields.TorusField (n * R.params.side) =>
        WeightedResponses.bondScore R.params R.coupling W V (StepSettings.coldChartSetting R V).bases c) = fun W =>
        StepCosts.bondFit R.params W V (StepSettings.coldChartSetting R V).bases c -
          StepCosts.meanNorm R.params W (StepSettings.coldChartSetting R V).bases c *
          deriv TorusLumps.logPartitionGap (R.params.coupling * R.coupling *
            StepCosts.meanNorm R.params W (StepSettings.coldChartSetting R V).bases c) := by
      funext W
      unfold WeightedResponses.bondScore
      rw [hsc.1 W]
    rw [e]
    exact hf.sub (hr.mul ((measurable_deriv TorusLumps.logPartitionGap).comp (measurable_const.mul hr)))
  exact integrable_mul_of_bounded hd (hs.comp hm) fun k => hsc.2.2.1 _ _
theorem integrable_bondFit_mul (hM : TorusLumps.MeasurableContourMeanStatement) (V : TorusFields.TorusField n)
    (c : TorusFields.TorusBond n) (hd : Integrable (ResponseInTheExpansion.coldHalfDensity R V))
    (hm : Measurable (ResponseInTheExpansion.coldFieldAboveFrames R V)) :
    Integrable fun k => StepCosts.bondFit R.params (ResponseInTheExpansion.coldFieldAboveFrames R V k) V
      (StepSettings.coldChartSetting R V).bases c * ResponseInTheExpansion.coldHalfDensity R V k := by
  have hf : Measurable fun W : TorusFields.TorusField (n * R.params.side) =>
      StepCosts.bondFit R.params W V (StepSettings.coldChartSetting R V).bases c :=
    hM R.params n (StepSettings.coldChartSetting R V).bases
      (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame R.params.side n) 1 c.1, c.2)
      (fun q => ‖q‖ - (q * ((((TorusFields.readAtLevel (TorusLumps.stepBlockFrame R.params.side n) 1 V)
        (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame R.params.side n) 1 c.1) c.2)⁻¹ :
          BlockAverages.UnitQuaternion) : ℍ[ℝ])).re)
      (continuous_norm.sub (Quaternion.continuous_re.comp (continuous_id.mul continuous_const)))
  exact integrable_mul_of_bounded hd (hf.comp hm) fun k => abs_bondFit_le_two _ _ _ _
theorem integrable_scoreRemainderAt_mul (hM : TorusLumps.MeasurableContourMeanStatement)
    (htail : WeightedResponses.ScoreRemainderExpansion) (hodd : Odd R.params.side)
    (ha : 1 ≤ R.params.coupling) (hx : 2 ≤ R.coupling) (V : TorusFields.TorusField n) (c : TorusFields.TorusBond n)
    (hd : Integrable (ResponseInTheExpansion.coldHalfDensity R V))
    (hm : Measurable (ResponseInTheExpansion.coldFieldAboveFrames R V))
    (hz : ∀ k : ColdStepAtMirrorFrames.StepVariable (ColdStepAtMirrorFrames.finiteCells (coarseFrame R n)),
      (¬ ∀ b, ‖k b‖ < R.ballRadius) → ResponseInTheExpansion.coldHalfDensity R V k = 0)
    (hcold : ∀ k : ColdStepAtMirrorFrames.StepVariable (ColdStepAtMirrorFrames.finiteCells (coarseFrame R n)),
      (∀ b, ‖k b‖ < R.ballRadius) →
        TorusFields.IsCold R.params.threshold (ResponseInTheExpansion.coldFieldAboveFrames R V k))
    (hsize : ∀ k : ColdStepAtMirrorFrames.StepVariable (ColdStepAtMirrorFrames.finiteCells (coarseFrame R n)),
      (∀ b, ‖k b‖ < R.ballRadius) →
        1 / 2 ≤ StepCosts.meanNorm R.params (ResponseInTheExpansion.coldFieldAboveFrames R V k)
          (StepSettings.coldChartSetting R V).bases c) :
    Integrable fun k => (ResponseInTheExpansion.coldHalfLawOf R).scoreRemainderAt (ResponseInTheExpansion.torusBondInFrame R c) k
      (ResponseInTheExpansion.coldTopField R V) * ResponseInTheExpansion.coldHalfDensity R V k := by
  obtain ⟨C, hC⟩ := htail.2 R.params.coupling ha 0
  have hQ : 2 / R.params.coupling ≤ (ResponseInTheExpansion.coldHalfLawOf R).coupling := by
    show 2 / R.params.coupling ≤ R.coupling
    have : 2 / R.params.coupling ≤ 2 := div_le_self (by norm_num) ha
    linarith
  obtain ⟨hc1, hc2⟩ := hC (ResponseInTheExpansion.coldHalfLawOf R) rfl hQ
  have h12 : (1 / 2 : ℝ) ≤ 1 := by norm_num
  have hcon : ContinuousOn (ResponseInTheExpansion.coldHalfLawOf R).scoreRemainder (Set.Icc (1 / 2) 1) := hc1.continuousOn
  set fe : ℝ → ℝ := Set.IccExtend h12
    ((Set.Icc (1 / 2 : ℝ) 1).restrict (ResponseInTheExpansion.coldHalfLawOf R).scoreRemainder) with hfe
  have hfc : Continuous fe := (continuousOn_iff_continuous_restrict.1 hcon).Icc_extend'
  have hfb : ∀ r, |fe r| ≤ C := by
    intro r
    have := hc2 (Set.projIcc (1 / 2 : ℝ) 1 h12 r) (Set.projIcc (1 / 2 : ℝ) 1 h12 r).2
    rw [iteratedDerivWithin_zero] at this
    exact this
  have hmr0 : Measurable fun W : TorusFields.TorusField (n * R.params.side) =>
      StepCosts.meanNorm R.params W (StepSettings.coldChartSetting R V).bases c :=
    hM R.params n (StepSettings.coldChartSetting R V).bases
      (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame R.params.side n) 1 c.1, c.2) (fun q => ‖q‖)
      continuous_norm
  have hI := integrable_mul_of_bounded hd (hfc.measurable.comp (hmr0.comp hm)) fun k => hfb _
  refine hI.congr (Filter.Eventually.of_forall fun k => ?_)
  by_cases hk : ∀ b, ‖k b‖ < R.ballRadius
  · have hs := meanNorm_eq_contourAverageSize hodd V k (hcold k hk) c
    have hmem : StepCosts.meanNorm R.params (ResponseInTheExpansion.coldFieldAboveFrames R V k)
        (StepSettings.coldChartSetting R V).bases c ∈ Set.Icc (1 / 2 : ℝ) 1 :=
      ⟨hsize k hk, meanNorm_le_one _ _ _⟩
    show fe _ * _ = (ResponseInTheExpansion.coldHalfLawOf R).scoreRemainder
      ((ResponseInTheExpansion.coldHalfLawOf R).contourAverageSize (ResponseInTheExpansion.torusBondInFrame R c) k
        (ResponseInTheExpansion.coldTopField R V)) * _
    rw [← hs]
    simp only [Function.comp, hfe]
    rw [Set.IccExtend_of_mem _ _ hmem]
    rfl
  · show _ * ResponseInTheExpansion.coldHalfDensity R V k = _ * ResponseInTheExpansion.coldHalfDensity R V k
    rw [hz k hk, mul_zero, mul_zero]
end ScoreBounds
open ColdFrameRestriction ScoreBounds in
theorem scoresAboveFramesStatement_holds (hlaw : ResponseInTheExpansion.coldHalfLawIsLawStatement)
    (hcs : StepSettings.ColdChartSettingIsCold) (hshare : ShareEvaluation.LevelShareEqMinimalSiteShare)
    (hcontour : ClusterExpansionOfAStep.ContourMeanAtColdField) (hscore : WeightedResponses.BondScoreProperties)
    (hweyl : ColdStepAtMirrorFrames.WeylIntegrationFormula) (htail : WeightedResponses.ScoreRemainderExpansion)
    (hM : TorusLumps.MeasurableContourMeanStatement) (hcov : ColdStepAtMirrorFrames.BlocksCoverLowerLevel) :
    ResponseInTheExpansion.scoresAboveFramesStatement := by
  intro T hT hC
  obtain ⟨y₁, hl⟩ := hlaw T hT hC
  obtain ⟨y₂, hr⟩ := hcontour T hT
  obtain ⟨y₃, hc3⟩ := hcs T hT
  refine ⟨max y₁ (max y₂ (max y₃ (max T.floorMin 2))), fun y hy R hR n _ hn V hV => ?_⟩
  have h1 : y₁ ≤ y := le_trans (le_max_left _ _) hy
  have hy2 := le_trans (le_max_right _ _) hy
  have h2 : y₂ ≤ y := le_trans (le_max_left _ _) hy2
  have hy3 := le_trans (le_max_right _ _) hy2
  have h5 : y₃ ≤ y := le_trans (le_max_left _ _) hy3
  have hy4 := le_trans (le_max_right _ _) hy3
  have h3 : T.floorMin ≤ y := le_trans (le_max_left _ _) hy4
  have h4 : 2 ≤ y := le_trans (le_max_right _ _) hy4
  obtain ⟨hL, hcF, hpt, -, -⟩ := hl y h1 R hR n hn V hV
  have hfit : R.params.Admissible := by
    rw [hR.params_eq]
    exact hT.fits y h3
  have hodd : Odd R.params.side := by
    rw [hR.params_eq]
    exact hT.L_odd
  have hn2 : 2 ≤ n := by
    have := hT.n₀_ge
    omega
  have hσ : R.params.threshold = T.threshold := by rw [hR.params_eq]; rfl
  have hσ0 : 0 < T.threshold := hT.σ_pos
  have hx : 2 ≤ R.coupling := h4.trans hR.le_coupling
  have ha : 1 ≤ R.params.coupling := by
    rw [hR.params_eq]
    exact hT.a_ge
  have hax : 2 ≤ R.params.coupling * R.coupling := by nlinarith
  have hcold : ∀ k : ColdStepAtMirrorFrames.StepVariable (ColdStepAtMirrorFrames.finiteCells (coarseFrame R n)),
      (∀ b, ‖k b‖ < R.ballRadius) →
        TorusFields.IsCold R.params.threshold (ResponseInTheExpansion.coldFieldAboveFrames R V k) := by
    intro k hk x μ ν hμ
    obtain ⟨η, hη, e⟩ := hpt k hk
    have := hc3 y h5 R hR n hn V hV η (fun b => (hη b).le) x μ ν hμ
    rw [← e, hσ]
    linarith
  have hsize : ∀ (k : ColdStepAtMirrorFrames.StepVariable (ColdStepAtMirrorFrames.finiteCells (coarseFrame R n)))
      (c : TorusFields.TorusBond n), (∀ b, ‖k b‖ < R.ballRadius) →
      1 / 2 ≤ StepCosts.meanNorm R.params (ResponseInTheExpansion.coldFieldAboveFrames R V k)
        (StepSettings.coldChartSetting R V).bases c := by
    intro k c hk
    obtain ⟨η, hη, e⟩ := hpt k hk
    rw [← e]
    exact hr y h2 R hR n hn V hV η (fun b => (hη b).le) c
  have hsh : ∀ (W : TorusFields.TorusField (n * R.params.side)), TorusFields.IsCold R.params.threshold W → ∀ y',
      StepCosts.levelShare R.params.coupling R.params.side R.depth Finset.univ y' W =
        ColdStepAtMirrorFrames.minimalSiteShare (F := coarseFrame R n) R.params.coupling
          (StepCosts.torusSiteInFrame (coarseFrame R n) (coarseFrame R n).depth y')
          (TorusFields.readAtLevel (coarseFrame R n) (coarseFrame R n).depth W) := by
    obtain ⟨ℓ, t, x, x', D, f, Λ, Dq, Φ, φ, ρA, p⟩ := R
    have e1 : ℓ = T.stepParameters y := hR.params_eq
    subst e1
    intro W hW y'
    exact hshare T hT t n hn W hW y'
  refine ⟨fun k Y hk => ?_, fun h k Y => ?_, fun Y => ?_, fun Y i back => ?_, fun c => ?_⟩
  · have h := blockCost_eq_cellEnergyShare hcov hodd hn2 _ (hcold k hk) (hsh _ (hcold k hk)) V
      (Interpolation.interpolatedCoords 1 R.params.coupling R.anchorRadius R.frameReach
        (ResponseInTheExpansion.coldTopField R V) k) (readAtLevel_coldFieldAboveFrames V k).symm Y
    unfold StepCosts.blockCost at h
    rw [torusHotSites_of_cold R.params _ (hcold k hk), thickening_empty, Finset.sdiff_empty] at h
    exact h
  · unfold ColdStepAtMirrorFrames.cellCentredExpansion
    rw [sum_sites_in_block hcov hodd]
    refine Finset.sum_congr rfl fun y' _ => ?_
    unfold ColdStepAtMirrorFrames.centredExpansion
    rw [← interpolatedField_one, ← readAtLevel_coldFieldAboveFrames]
    exact subtractTrivial_readAtLevel h y' _
  · exact levelShare_top Y
  · cases back
    · simp [WeightedResponses.cellBond, ResponseInTheExpansion.torusBondInFrame]
    · simp only [WeightedResponses.cellBond, ResponseInTheExpansion.torusBondInFrame, if_true]
      rw [torusSiteInFrame_sub_unitStep]
  · have hm := hcF.measurable
    exact ⟨fun k hk => bondScore_eq_of_cold hscore hweyl htail hfit hodd V k (hcold k hk) c (hsize k c hk) hax,
      integrable_bondScore_mul hscore hM hfit V c hL.integrable hm, integrable_bondFit_mul hM V c hL.integrable hm,
      integrable_scoreRemainderAt_mul hM htail hodd ha hx V c hL.integrable hm (fun k hk => hL.eq_zero_outside k hk)
        hcold fun k hk => hsize k c hk⟩
end ResponseInTheExpansion
end YangMills.Construction
end
