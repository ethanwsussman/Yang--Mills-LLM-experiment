import YangMills.Construction.ColdChainAtEveryLevel.ChainsAtTheSameOffsets
import YangMills.Construction.ColdChainAtEveryLevel.FloorOfTheChartFormProof
import YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderOfTheExpansionAtAFlatTopProof
import YangMills.Construction.RunningCouplingSlope.GapsAtTheLeastFieldAreSmallProof
import YangMills.Construction.RunningCouplingSlope.MomentOfTheExpansionAtTheLeastFieldProof
import YangMills.Construction.SummableBoundsOfTheFlow.MixturesOfTwoLevels
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction.RunningCouplingSlope
namespace MinimizerTangents
section Offsets
private theorem cellCentre_add_siteOfCoords {F : BlockAverages.BlockFrame} (Y : F.Cell) (h : Fin 4 → ℤ) :
    BlockAverages.cellCentre F.depth (Y + BlockAverages.siteOfCoords F.top h) =
      BlockAverages.SameOffsets.siteAtOffset Y F.depth (BlockAverages.SameOffsets.scaleOffset F.blockSide h) := by
  have hj : F.depth + 1 ≤ F.top := le_rfl
  have e := BlockAverages.SameOffsets.refineSite_siteAtOffset (F := F) (j := F.depth) hj Y h
  rw [← e]
  have e2 : BlockAverages.SameOffsets.siteAtOffset Y (F.depth + 1) h = Y + BlockAverages.siteOfCoords F.top h := by
    show BlockAverages.cellCentre F.top Y + BlockAverages.siteOfCoords F.top h = _
    rw [BlockAverages.cellCentre_top]
  rw [e2]
  have e3 := BlockAverages.ChartCoordinates.refineSite_cellCentre F.depth hj (Y + BlockAverages.siteOfCoords F.top h)
  rw [← e3]
  congr 1
  exact BlockAverages.cellCentre_top (F := F) _
abbrev _root_.YangMills.SharedProofs.p18452 := @cellCentre_add_siteOfCoords
private def offsetInBlock (L : ℕ) (p : Fin 4 → ℤ) : Fin 4 → ℤ :=
  p - BlockAverages.SameOffsets.scaleOffset L (CongruentBoxes.coarseOffset L p)
private theorem offsetInBlock_mem {L : ℕ} (hL : Odd L) (p : Fin 4 → ℤ) :
    offsetInBlock L p ∈ BlockAverages.centredCube L := by
  rw [ColdStepAtMirrorFrames.BlockOffsets.mem_centredCube_iff]
  intro i
  obtain ⟨k, hk⟩ := hL
  have hh : ColdStepAtMirrorFrames.BlockOffsets.halfSide L = k := by
    unfold ColdStepAtMirrorFrames.BlockOffsets.halfSide
    omega
  simp only [offsetInBlock, BlockAverages.SameOffsets.scaleOffset, CongruentBoxes.coarseOffset, Pi.sub_apply]
  have hLp : (0 : ℤ) < L := by omega
  have e := Int.emod_add_mul_ediv (p i + ((L : ℤ) - 1) / 2) (L : ℤ)
  have h1 := Int.emod_nonneg (p i + ((L : ℤ) - 1) / 2) hLp.ne'
  have h2 := Int.emod_lt_of_pos (p i + ((L : ℤ) - 1) / 2) hLp
  have hh2 : ((L : ℤ) - 1) / 2 = k := by omega
  rw [hh]
  rw [hh2] at e h1 h2 ⊢
  generalize (L : ℤ) * ((p i + (k : ℤ)) / (L : ℤ)) = P at *
  generalize (p i + (k : ℤ)) % (L : ℤ) = R at *
  constructor <;> omega
abbrev _root_.YangMills.DeltaSharedProofs.p502368 := @offsetInBlock_mem
private theorem abs_coarseOffset_le {L : ℕ} (hL : Odd L) {c : ℤ} (hc : 0 ≤ c) {p : Fin 4 → ℤ} {i : Fin 4}
    (hp : |p i| ≤ c * L) : |CongruentBoxes.coarseOffset L p i| ≤ c := by apply _root_.YangMills.SharedProofs.p21677 <;> assumption
private theorem siteAtOffset_eq_cellCentre_add {F : BlockAverages.BlockFrame} (Y : F.Cell) (p : Fin 4 → ℤ) :
    BlockAverages.SameOffsets.siteAtOffset Y F.depth p =
      BlockAverages.cellCentre F.depth (Y + BlockAverages.siteOfCoords F.top (CongruentBoxes.coarseOffset F.blockSide p)) +
        BlockAverages.siteOfCoords F.depth (offsetInBlock F.blockSide p) := by
  rw [cellCentre_add_siteOfCoords]
  show _ = BlockAverages.SameOffsets.siteAtOffset Y F.depth _ + _
  rw [← BlockAverages.SameOffsets.siteAtOffset_add]
  congr 1
  simp [offsetInBlock]
abbrev _root_.YangMills.DeltaSharedProofs.p502588 := @siteAtOffset_eq_cellCentre_add
end Offsets
section Sites
variable {L u m : ℕ} [NeZero L] [NeZero m]
private theorem period_depth_torusFrame (i : Fin 4) :
    (TorusFields.torusFrame L u m).period (TorusFields.torusFrame L u m).depth i = m * L :=
  TopLevelSites.period_depth_of_extent (F := TorusFields.torusFrame L u m) (n := m) (fun _ => rfl) i
private theorem period_top_torusFrame (i : Fin 4) :
    (TorusFields.torusFrame L u m).period (TorusFields.torusFrame L u m).top i = m :=
  TorusFrame.period_torusFrame i
private theorem torusSiteInFrame_depth_siteOfInt (z : Fin 4 → ℤ) :
    StepCosts.torusSiteInFrame (TorusFields.torusFrame L u m) (TorusFields.torusFrame L u m).depth
        (TorusFields.siteOfInt z : TorusFields.TorusSite (m * L)) =
      BlockAverages.siteOfCoords (TorusFields.torusFrame L u m).depth z := by
  rw [← TopLevelSites.toTorusSite_siteOfCoords period_depth_torusFrame z,
    TopLevelSites.torusSiteInFrame_toTorusSite period_depth_torusFrame]
private theorem torusSiteInFrame_blockCentre_add (Y : TorusFields.TorusSite m) (p : Fin 4 → ℤ) :
    StepCosts.torusSiteInFrame (TorusFields.torusFrame L u m) (TorusFields.torusFrame L u m).depth
        (CongruentBoxes.blockCentre L Y + TorusFields.siteOfInt p : TorusFields.TorusSite (m * L)) =
      BlockAverages.SameOffsets.siteAtOffset
        (StepCosts.torusSiteInFrame (TorusFields.torusFrame L u m) (TorusFields.torusFrame L u m).top Y)
        (TorusFields.torusFrame L u m).depth p := by
  rw [TopLevelSites.torusSiteInFrame_add period_depth_torusFrame]
  unfold BlockAverages.SameOffsets.siteAtOffset
  congr 1
  · rw [show CongruentBoxes.blockCentre L Y = TorusFields.siteOfInt fun i => (L : ℤ) * ((Y i).cast : ℤ) from rfl,
      torusSiteInFrame_depth_siteOfInt]
    unfold BlockAverages.cellCentre
    congr 1
    funext i
    rw [TopLevelSites.siteCoords_torusSiteInFrame period_top_torusFrame Y i,
      ColdStepAtMirrorFrames.BlockOffsets.top_sub_depth, pow_one]
    rfl
  · exact torusSiteInFrame_depth_siteOfInt p
abbrev _root_.YangMills.SharedProofs.p4320 := @torusSiteInFrame_blockCentre_add
private theorem torusSiteInFrame_top_add_siteOfInt (Y : TorusFields.TorusSite m) (e : Fin 4 → ℤ) :
    StepCosts.torusSiteInFrame (TorusFields.torusFrame L u m) (TorusFields.torusFrame L u m).top
        (Y + TorusFields.siteOfInt e) =
      StepCosts.torusSiteInFrame (TorusFields.torusFrame L u m) (TorusFields.torusFrame L u m).top Y +
        BlockAverages.siteOfCoords (TorusFields.torusFrame L u m).top e := by
  rw [TorusChain.torusSiteInFrame_add period_top_torusFrame,
    TorusChain.torusSiteInFrame_siteOfInt period_top_torusFrame]
private theorem cellSupDist_add_le (Y : TorusFields.TorusSite m) {e : Fin 4 → ℤ} {c : ℕ}
    (he : ∀ i, (e i).natAbs ≤ c) :
    BlockAverages.cellSupDist
      (StepCosts.torusSiteInFrame (TorusFields.torusFrame L u m) (TorusFields.torusFrame L u m).top Y)
      (StepCosts.torusSiteInFrame (TorusFields.torusFrame L u m) (TorusFields.torusFrame L u m).top Y +
        BlockAverages.siteOfCoords (TorusFields.torusFrame L u m).top e) ≤ c := by
  rw [← torusSiteInFrame_top_add_siteOfInt, TorusChain.cellSupDist_torusSiteInFrame period_top_torusFrame]
  exact TorusFields.supDist_add_siteOfInt_le Y e c he
end Sites
section Chain
variable {F : BlockAverages.BlockFrame}
private theorem isCold_flatTopField {s : ℝ} (hs : 0 < s) (S : Finset F.Cell) :
    BlockAverages.IsCold S F.top s (BlockAverages.flatTopField : F.GaugeField F.top) := by apply _root_.YangMills.SharedProofs.p30906 <;> assumption
private theorem minimizingBondCoordinate_of_not_mem {a ρ : ℝ} {S : Finset F.Cell} {b : F.Site F.depth × Fin 4}
    (hb : b ∉ BlockAverages.chordBonds S) (V : F.GaugeField F.top) :
    BlockAverages.minimizingBondCoordinate a ρ S b V = 0 := by apply _root_.YangMills.SharedProofs.p70322 <;> assumption
private def coordSlope (F : BlockAverages.BlockFrame) (X : BlockAverages.imaginaryQuaternions) (a ρ : ℝ)
    (b : F.Site F.depth × Fin 4) (c : F.Site F.top × Fin 4) : BlockAverages.imaginaryQuaternions :=
  ColdStepAtMirrorFrames.bondDeriv (ColdStepAtMirrorFrames.torusCoordinate a ρ b)
    (ColdStepAtMirrorFrames.uniformField F F.top) ![c] ![X]
private theorem coordSlope_of_not_mem {a ρ : ℝ} {X : BlockAverages.imaginaryQuaternions}
    {b : F.Site F.depth × Fin 4} (hb : b ∉ BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells F))
    (c : F.Site F.top × Fin 4) : coordSlope F X a ρ b c = 0 := by
  unfold coordSlope ColdStepAtMirrorFrames.bondDeriv
  have e : (fun τ : Fin 1 → ℝ => ColdStepAtMirrorFrames.torusCoordinate a ρ b
      (ColdStepAtMirrorFrames.leftTranslate (ColdStepAtMirrorFrames.bondSpread ![c] ![X] τ)
        (ColdStepAtMirrorFrames.uniformField F F.top))) = fun _ => 0 := by
    funext τ
    exact minimizingBondCoordinate_of_not_mem hb _
  rw [e, iteratedFDeriv_fun_zero]
  rfl
private theorem bondListDistance_single (Y : F.Cell) (c : F.Site F.top × Fin 4) :
    BlockAverages.bondListDistance Y ![c] = BlockAverages.cellSupDist Y c.1 := by
  simp [BlockAverages.bondListDistance]
variable {a ρ δ lam σA cg : ℝ} {N : ℕ → ℝ} {L : ℕ}
private theorem flatTop_coordinates (hc : ColdChain.ColdChainConstants a δ L lam ρ σA cg N) {u m : ℕ} [NeZero m]
    (hm : 64 ≤ m) :
    BlockAverages.HasRegularCoordinates a δ ρ N (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L u m))
      (BlockAverages.flatTopField) ∧
    ∀ (m' : ℕ) [NeZero m'], 64 ≤ m' → ∀ (Y : (TorusFields.torusFrame L u m).Cell)
      (Y' : (TorusFields.torusFrame L u m').Cell) (r : ℕ),
      BlockAverages.AgreeOnBall (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L u m))
        BlockAverages.flatTopField
        (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L u m')) BlockAverages.flatTopField Y Y' r →
      BlockAverages.HasComparableCoordinates a δ ρ σA N
        (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L u m)) BlockAverages.flatTopField
        (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L u m')) BlockAverages.flatTopField Y Y' r := by
  obtain ⟨_, _, _, _, _, hσ, _, _, hmain⟩ := hc
  have pos : ∀ {k : ℕ}, 64 ≤ k → ∀ i, 0 < (TorusFields.torusFrame L u k).extent i := fun {k} hk _ =>
    (show 0 < k by omega)
  have h := hmain (TorusFields.torusFrame L u m) 1024 (ColdStepAtMirrorFrames.finiteCells _) rfl
    (Or.inr fun _ => hm) le_rfl
    (TopLevelSites.isOrthantRegular_finiteCells (pos hm) 1024) σA BlockAverages.flatTopField hσ le_rfl
    (isCold_flatTopField hσ _)
  refine ⟨h.2.2.2.1, fun m' _ hm' Y Y' r hag => ?_⟩
  exact (h.2.2.2.2.2 (TorusFields.torusFrame L u m') (ColdStepAtMirrorFrames.finiteCells _)
    BlockAverages.flatTopField Y Y' r rfl rfl
    (Or.inr fun _ => hm') (TopLevelSites.isOrthantRegular_finiteCells (pos hm') 1024)
    (isCold_flatTopField hσ _) hag).2
abbrev _root_.YangMills.SharedProofs.p11303 := @flatTop_coordinates
private theorem norm_coordSlope_le (hc : ColdChain.ColdChainConstants a δ L lam ρ σA cg N) {u m : ℕ} [NeZero m]
    (hm : 64 ≤ m) {X : BlockAverages.imaginaryQuaternions}
    (hX : ‖X‖ = 1) (b : (TorusFields.torusFrame L u m).Site (TorusFields.torusFrame L u m).depth × Fin 4)
    (c : (TorusFields.torusFrame L u m).Site (TorusFields.torusFrame L u m).top × Fin 4) :
    ‖coordSlope (TorusFields.torusFrame L u m) X a ρ b c‖ ≤
      N 1 * Real.exp (-δ * (BlockAverages.cellSupDist (BlockAverages.enclosingCell b.1) c.1 : ℝ)) := by
  have hN : 0 < N 1 := hc.2.2.2.2.2.2.2.1 1
  by_cases hb : b ∈ BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L u m))
  · have h := ((flatTop_coordinates hc (u := u) hm).1 b hb).2 1 ![c] ![X] le_rfl
      (fun l => by fin_cases l; exact hX)
    rw [bondListDistance_single] at h
    exact h
  · rw [coordSlope_of_not_mem hb, norm_zero]
    positivity
end Chain
section Compare
variable {a ρ δ lam σA cg : ℝ} {N : ℕ → ℝ} {L : ℕ}
private theorem siteAtOffset_mem_sitesOfCells {F : BlockAverages.BlockFrame} (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) (Y : F.Cell) (p : Fin 4 → ℤ) :
    BlockAverages.SameOffsets.siteAtOffset Y F.depth p ∈
      BlockAverages.sitesOfCells (ColdStepAtMirrorFrames.finiteCells F) F.depth := by
  simp only [BlockAverages.sitesOfCells, Finset.mem_biUnion, Finset.mem_image]
  refine ⟨_, ColdStepAtMirrorFrames.BlockOffsets.mem_finiteCells hs
    (Y + BlockAverages.siteOfCoords F.top (CongruentBoxes.coarseOffset F.blockSide p)),
    offsetInBlock F.blockSide p, ?_, (siteAtOffset_eq_cellCentre_add Y p).symm⟩
  rw [ColdStepAtMirrorFrames.BlockOffsets.top_sub_depth, pow_one]
  exact offsetInBlock_mem hL p
abbrev _root_.YangMills.SharedProofs.p15166 := @siteAtOffset_mem_sitesOfCells
private theorem isAxialTreeBond_cellCentre_add_iff {F : BlockAverages.BlockFrame} (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell) {o : Fin 4 → ℤ}
    (ho : o ∈ BlockAverages.centredCube F.blockSide) (i : Fin 4) :
    BlockAverages.IsAxialTreeBond
        ((BlockAverages.cellCentre F.depth z + BlockAverages.siteOfCoords F.depth o : F.Site F.depth), i) ↔
      ¬ o i = ColdStepAtMirrorFrames.BlockOffsets.halfSide F.blockSide ∧ ∀ l, i < l → o l = 0 := by
  unfold BlockAverages.IsAxialTreeBond
  rw [ColdStepAtMirrorFrames.BlockOffsets.isCrossingBond_iff hL hs z o ho i]
  simp only [ColdStepAtMirrorFrames.BlockOffsets.cellOffset_offset hL hs z o ho]
private theorem mem_chordBonds {F : BlockAverages.BlockFrame} {S : Finset F.Cell} {b : F.Site F.depth × Fin 4} :
    b ∈ BlockAverages.chordBonds S ↔ b ∈ BlockAverages.innerBonds S F.depth ∧ ¬ BlockAverages.IsAxialTreeBond b := by apply _root_.YangMills.Construction.BlockAverages.ChartFloor.mem_chordBonds_iff <;> assumption
private theorem coordSlope_eq_mixed {F : BlockAverages.BlockFrame} (X : BlockAverages.imaginaryQuaternions)
    (a ρ : ℝ) (b : F.Site F.depth × Fin 4) (c : F.Site F.top × Fin 4) :
    ((coordSlope F X a ρ b c : BlockAverages.imaginaryQuaternions) : ℍ[ℝ]) =
      ((BlockAverages.mixedBondDerivative
        (BlockAverages.minimizingBondCoordinate a ρ (ColdStepAtMirrorFrames.finiteCells F) b)
        BlockAverages.flatTopField ![c] ![X] : BlockAverages.imaginaryQuaternions) : ℍ[ℝ]) := rfl
private theorem abs_basisVector_le (i j : Fin 4) : |(Pi.single i 1 : Fin 4 → ℤ) j| ≤ 1 := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.abs_single_one_le <;> assumption
private theorem norm_coordSlope_sub_le [NeZero L] (hc : ColdChain.ColdChainConstants a δ L lam ρ σA cg N)
    (hodd : Odd L) {u n n' r : ℕ} [NeZero n] [NeZero n']
    (hn : 64 ≤ n) (hn' : 64 ≤ n') (hr : 16 ≤ r) (h2 : 2 * r + 2 < n) (h2' : 2 * r + 2 < n')
    (Y : TorusFields.TorusSite n) (Y' : TorusFields.TorusSite n') {p : Fin 4 → ℤ} (hp : ∀ i, |p i| ≤ 2 * (L : ℤ))
    (i : Fin 4) {e : Fin 4 → ℤ} {k : Fin 4}
    (he : BlockAverages.BondWithinRadius r (e, k)) {X : BlockAverages.imaginaryQuaternions} (hXu : ‖X‖ = 1) :
    ‖((coordSlope (TorusFields.torusFrame L u n) X a ρ
        (BlockAverages.SameOffsets.siteAtOffset
          (StepCosts.torusSiteInFrame (TorusFields.torusFrame L u n) (TorusFields.torusFrame L u n).top Y)
          (TorusFields.torusFrame L u n).depth p, i)
        (StepCosts.torusSiteInFrame (TorusFields.torusFrame L u n) (TorusFields.torusFrame L u n).top Y +
          BlockAverages.siteOfCoords (TorusFields.torusFrame L u n).top e, k) :
            BlockAverages.imaginaryQuaternions) : ℍ[ℝ]) -
      ((coordSlope (TorusFields.torusFrame L u n') X a ρ
        (BlockAverages.SameOffsets.siteAtOffset
          (StepCosts.torusSiteInFrame (TorusFields.torusFrame L u n') (TorusFields.torusFrame L u n').top Y')
          (TorusFields.torusFrame L u n').depth p, i)
        (StepCosts.torusSiteInFrame (TorusFields.torusFrame L u n') (TorusFields.torusFrame L u n').top Y' +
          BlockAverages.siteOfCoords (TorusFields.torusFrame L u n').top e, k) :
            BlockAverages.imaginaryQuaternions) : ℍ[ℝ])‖ ≤
      N 1 * Real.exp (-δ * ((r : ℝ) - 2)) := by
  have hδ : 0 < δ := hc.1
  have hN : 0 < N 1 := hc.2.2.2.2.2.2.2.1 1
  have hs : ∀ i, 2 ≤ (TorusFields.torusFrame L u n).extent i := fun _ => (show 2 ≤ n by omega)
  have hs' : ∀ i, 2 ≤ (TorusFields.torusFrame L u n').extent i := fun _ => (show 2 ≤ n' by omega)
  have hLo : Odd (TorusFields.torusFrame L u n).blockSide := hodd
  have hLo' : Odd (TorusFields.torusFrame L u n').blockSide := hodd
  obtain ⟨Yc, hYc⟩ : ∃ Yc, Yc = StepCosts.torusSiteInFrame (TorusFields.torusFrame L u n)
      (TorusFields.torusFrame L u n).top Y := ⟨_, rfl⟩
  obtain ⟨Yd, hYd⟩ : ∃ Yd, Yd = StepCosts.torusSiteInFrame (TorusFields.torusFrame L u n')
      (TorusFields.torusFrame L u n').top Y' := ⟨_, rfl⟩
  rw [← hYc, ← hYd]
  obtain ⟨h, hh0⟩ : ∃ h, h = CongruentBoxes.coarseOffset L p := ⟨_, rfl⟩
  obtain ⟨o, ho0⟩ : ∃ o, o = offsetInBlock L p := ⟨_, rfl⟩
  have ho : o ∈ BlockAverages.centredCube L := ho0 ▸ offsetInBlock_mem hodd p
  have hh : ∀ i, |h i| ≤ 2 := fun i => by
    rw [hh0]
    exact abs_coarseOffset_le hodd (by norm_num) (hp i)
  have hX : BlockAverages.SameOffsets.siteAtOffset Yc (TorusFields.torusFrame L u n).depth p =
      (BlockAverages.fineBondAt Yc h o i).1 := by
    rw [hh0, ho0]
    exact siteAtOffset_eq_cellCentre_add Yc p
  have hX' : BlockAverages.SameOffsets.siteAtOffset Yd (TorusFields.torusFrame L u n').depth p =
      (BlockAverages.fineBondAt Yd h o i).1 := by
    rw [hh0, ho0]
    exact siteAtOffset_eq_cellCentre_add Yd p
  have hB : (BlockAverages.SameOffsets.siteAtOffset Yc (TorusFields.torusFrame L u n).depth p, i) =
      BlockAverages.fineBondAt Yc h o i := by rw [hX]; rfl
  have hB' : (BlockAverages.SameOffsets.siteAtOffset Yd (TorusFields.torusFrame L u n').depth p, i) =
      BlockAverages.fineBondAt Yd h o i := by rw [hX']; rfl
  rw [hB, hB']
  have hEe : (BlockAverages.fineBondAt Yc h o i :
      (TorusFields.torusFrame L u n).Site (TorusFields.torusFrame L u n).depth × Fin 4) =
      (BlockAverages.cellCentre (TorusFields.torusFrame L u n).depth
        (Yc + BlockAverages.siteOfCoords (TorusFields.torusFrame L u n).top h) +
          BlockAverages.siteOfCoords (TorusFields.torusFrame L u n).depth o, i) := rfl
  have hEe' : (BlockAverages.fineBondAt Yd h o i :
      (TorusFields.torusFrame L u n').Site (TorusFields.torusFrame L u n').depth × Fin 4) =
      (BlockAverages.cellCentre (TorusFields.torusFrame L u n').depth
        (Yd + BlockAverages.siteOfCoords (TorusFields.torusFrame L u n').top h) +
          BlockAverages.siteOfCoords (TorusFields.torusFrame L u n').depth o, i) := rfl
  have hbound : 0 ≤ N 1 * Real.exp (-δ * ((r : ℝ) - 2)) := by positivity
  by_cases ht : BlockAverages.IsAxialTreeBond (BlockAverages.fineBondAt Yc h o i)
  · have ht' : BlockAverages.IsAxialTreeBond (BlockAverages.fineBondAt Yd h o i) := by
      rw [hEe'] at *
      rw [hEe] at ht
      exact (isAxialTreeBond_cellCentre_add_iff hLo' hs' _ ho i).mpr
        ((isAxialTreeBond_cellCentre_add_iff hLo hs _ ho i).mp ht)
    have off : BlockAverages.fineBondAt Yc h o i ∉
        BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L u n)) :=
      fun hm => (mem_chordBonds.mp hm).2 ht
    have off' : BlockAverages.fineBondAt Yd h o i ∉
        BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L u n')) :=
      fun hm => (mem_chordBonds.mp hm).2 ht'
    rw [coordSlope_of_not_mem off, coordSlope_of_not_mem off']
    simpa using hbound
  · have hmem : BlockAverages.fineBondAt Yc h o i ∈
        BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L u n)) := by
      refine mem_chordBonds.mpr ⟨?_, ht⟩
      simp only [BlockAverages.innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
      rw [← hX, BlockAverages.SameOffsets.siteAtOffset_add_unitStep]
      exact ⟨siteAtOffset_mem_sitesOfCells hLo hs Yc p, siteAtOffset_mem_sitesOfCells hLo hs Yc _⟩
    have hag : BlockAverages.AgreeOnBall (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L u n))
        BlockAverages.flatTopField
        (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L u n')) BlockAverages.flatTopField Yc Yd r :=
      ⟨fun _ => Or.inr h2, fun _ => Or.inr h2', fun _ => by
        simp [ColdStepAtMirrorFrames.BlockOffsets.mem_finiteCells hs,
          ColdStepAtMirrorFrames.BlockOffsets.mem_finiteCells hs'], fun _ _ => rfl⟩
    have hloc := (flatTop_coordinates hc (u := u) hn).2 n' hn' Yc Yd r hag
    have hbox : BlockAverages.WithinRadius r h := fun i => by
      have := hh i
      have : (2 : ℤ) ≤ r := by omega
      omega
    have hnext : BlockAverages.cellSupDist Yc (BlockAverages.enclosingCell
        ((BlockAverages.fineBondAt Yc h o i).1 + BlockAverages.unitStep (TorusFields.torusFrame L u n).depth i)) ≤ r := by
      rw [← hX, BlockAverages.SameOffsets.siteAtOffset_add_unitStep,
        siteAtOffset_eq_cellCentre_add Yc (p + LatticeFractionalIntegration.basisVector i),
        ColdStepAtMirrorFrames.BlockOffsets.enclosingCell_offset hLo hs _ _ (offsetInBlock_mem hLo _), hYc]
      refine le_trans (cellSupDist_add_le Y (c := 3) fun j => ?_) (by omega)
      have hb : |(p + LatticeFractionalIntegration.basisVector i) j| ≤ 3 * (L : ℤ) := by
        have h1 := hp j
        have h2 : |(LatticeFractionalIntegration.basisVector i : Fin 4 → ℤ) j| ≤ 1 := abs_basisVector_le i j
        have h3 : (1 : ℤ) ≤ L := by exact_mod_cast hodd.pos
        calc |(p + LatticeFractionalIntegration.basisVector i) j| ≤
              |p j| + |(LatticeFractionalIntegration.basisVector i : Fin 4 → ℤ) j| := abs_add_le _ _
          _ ≤ 3 * (L : ℤ) := by omega
      have := abs_le.mp (abs_coarseOffset_le hodd (c := 3) (by norm_num) hb)
      show (CongruentBoxes.coarseOffset L (p + LatticeFractionalIntegration.basisVector i) j).natAbs ≤ 3
      omega
    have hmain := (hloc h o i ho hmem hbox hnext).2 1 ![(e, k)] ![X] le_rfl
      (fun l => by fin_cases l; exact he) (fun l => by fin_cases l; exact hXu)
    have hbs : BlockAverages.offsetBonds Yc ![(e, k)] =
        ![(Yc + BlockAverages.siteOfCoords (TorusFields.torusFrame L u n).top e, k)] := by
      funext l; fin_cases l; rfl
    have hbs' : BlockAverages.offsetBonds Yd ![(e, k)] =
        ![(Yd + BlockAverages.siteOfCoords (TorusFields.torusFrame L u n').top e, k)] := by
      funext l; fin_cases l; rfl
    rw [hbs, hbs'] at hmain
    rw [coordSlope_eq_mixed, coordSlope_eq_mixed]
    refine le_trans hmain ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hN.le
    have hcd : BlockAverages.cellSupDist Yc (BlockAverages.enclosingCell (BlockAverages.fineBondAt Yc h o i).1) ≤ 2 := by
      rw [← hX, siteAtOffset_eq_cellCentre_add Yc p,
        ColdStepAtMirrorFrames.BlockOffsets.enclosingCell_offset hLo hs _ _ (offsetInBlock_mem hLo _), hYc]
      refine cellSupDist_add_le Y (c := 2) fun j => ?_
      have := hh j
      rw [hh0] at this
      have := abs_le.mp this
      show (CongruentBoxes.coarseOffset L p j).natAbs ≤ 2
      omega
    have hcd' : (BlockAverages.cellSupDist Yc
        (BlockAverages.enclosingCell (BlockAverages.fineBondAt Yc h o i).1) : ℝ) ≤ 2 := by exact_mod_cast hcd
    nlinarith
end Compare
section Flat
private theorem hasColdMinimizer_of_admissible {Tb : RenormalizationStepParameters.ParameterAssignment} (hD : Tb.Admissible)
    {F : BlockAverages.BlockFrame} (hFL : F.blockSide = Tb.side) (hamb : BlockAverages.IsAdmissibleAmbient F)
    (S : Finset F.Cell) (hS : ∀ z, z ∈ S) (s : ℝ) (hs : 0 < s) (hsA : s ≤ Tb.σA) (V : F.GaugeField F.top)
    (hV : BlockAverages.IsCold S F.top s V) : BlockAverages.HasColdMinimizer Tb.coupling Tb.ρA (Tb.N 0) s S V := by
  obtain ⟨-, -, -, -, -, -, -, -, h⟩ := hD.chain
  have hreg : BlockAverages.IsOrthantRegular S 1024 := fun z =>
    ⟨fun _ => 1, fun _ => Or.inl rfl, fun _ _ _ _ _ _ => hS _⟩
  exact (h F 1024 S hFL hamb le_rfl hreg s V hs hsA hV).1
private theorem isMinimizingChart_zero {Tb : RenormalizationStepParameters.ParameterAssignment} (hD : Tb.Admissible)
    (hFlat : BlockAverages.flatTopVanishingStatement) (hOne : ColdStepAtMirrorFrames.MinimizingChartUnique)
    {F : BlockAverages.BlockFrame} (hFL : F.blockSide = Tb.side) (hside : ∀ i, 64 ≤ F.extent i) :
    BlockAverages.IsMinimizingChart Tb.coupling (ColdStepAtMirrorFrames.finiteCells F)
      (BlockAverages.flatField F F.top) Tb.ρA fun _ _ => 0 := by
  have ha : 0 ≤ Tb.coupling := by linarith [hD.a_ge]
  have hodd : Odd F.blockSide := hFL ▸ hD.L_odd
  obtain ⟨-, -, -, hρ0, hρ1, hσ, -, hN, -⟩ := hD.chain
  have h2 : ∀ i, 2 ≤ F.extent i := fun i => le_trans (by norm_num) (hside i)
  have hall : ∀ z, z ∈ ColdStepAtMirrorFrames.finiteCells F := ColdStepAtMirrorFrames.BlockOffsets.mem_finiteCells h2
  have hfl := hFlat F Tb.coupling (ColdStepAtMirrorFrames.finiteCells F) ha hodd
  have hch : ∀ s, 0 < s → s ≤ Tb.σA → BlockAverages.HasColdMinimizer Tb.coupling Tb.ρA (Tb.N 0) s
      (ColdStepAtMirrorFrames.finiteCells F) (BlockAverages.flatField F F.top) :=
    fun s hs hsA => hasColdMinimizer_of_admissible hD hFL (Or.inr hside) _ hall s hs hsA _ (hfl.1 F.top s hs)
  have hwide : ∀ (w : F.Site F.depth → Fin 4 → BlockAverages.imaginaryQuaternions) (r : ℝ),
      BlockAverages.IsMinimizingChart Tb.coupling (ColdStepAtMirrorFrames.finiteCells F)
        (BlockAverages.flatField F F.top) (min Tb.ρA r) w →
      BlockAverages.IsMinimizingChart Tb.coupling (ColdStepAtMirrorFrames.finiteCells F)
        (BlockAverages.flatField F F.top) Tb.ρA w := fun w r h =>
    ⟨h.1, fun b hb => le_trans (h.2.1 b hb) (min_le_left _ _), h.2.2⟩
  obtain ⟨w, hw, -, -⟩ := hch Tb.σA hσ le_rfl
  have hw' := hwide w _ hw
  have huniq := (hOne F Tb.coupling Tb.ρA (Tb.N 0) Tb.σA (BlockAverages.flatField F F.top) w hodd h2 hρ1
    (hch Tb.σA hσ le_rfl) hw').1
  have hsmall : ∀ b ∈ BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells F), ∀ s, 0 < s → s ≤ Tb.σA →
      ‖w b.1 b.2‖ ≤ Tb.N 0 * s := by
    intro b hb s hs hsA
    obtain ⟨ws, hws, -, -⟩ := hch s hs hsA
    have e := huniq ws (hwide ws _ hws)
    rw [← e]
    exact le_trans (hws.2.1 b hb) (min_le_right _ _)
  have hz : w = fun _ _ => 0 := by
    funext x i
    by_cases hb : (x, i) ∈ BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells F)
    · by_contra hne
      have hp : 0 < ‖w x i‖ := norm_pos_iff.2 hne
      have hN0 := hN 0
      have hs : 0 < min Tb.σA (‖w x i‖ / (2 * Tb.N 0)) := lt_min hσ (by positivity)
      have h1 := hsmall (x, i) hb _ hs (min_le_left _ _)
      have h3 : Tb.N 0 * min Tb.σA (‖w x i‖ / (2 * Tb.N 0)) ≤ Tb.N 0 * (‖w x i‖ / (2 * Tb.N 0)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hN0.le
      have h4 : Tb.N 0 * (‖w x i‖ / (2 * Tb.N 0)) = ‖w x i‖ / 2 := by
        field_simp
      have h5 : ‖w x i‖ ≤ ‖w x i‖ / 2 := le_trans h1 (by rw [← h4]; exact h3)
      linarith
    · exact hw.1 (x, i) hb
  rw [← hz]
  exact hw'
private theorem minimizerCoord_trivialField {T : RenormalizationStepParameters.ParameterAssignment} (hD : T.Admissible)
    (hFlat : BlockAverages.flatTopVanishingStatement) (hOne : ColdStepAtMirrorFrames.MinimizingChartUnique)
    {t n : ℕ} [NeZero n] (hn : 64 ≤ n) (b : TorusFields.TorusBond (n * T.side)) :
    TwoLevelMixtures.minimizerCoord T.coupling T.side T.ρA t (TorusFields.trivialField n) b = 0 := by
  obtain ⟨-, -, -, hρ0, hρ1, hσ, -, hN, -⟩ := hD.chain
  have hside : ∀ i, 64 ≤ (TorusFields.torusFrame T.side t n).extent i := fun _ => hn
  have h2 : ∀ i, 2 ≤ (TorusFields.torusFrame T.side t n).extent i := fun i => le_trans (by norm_num) (hside i)
  have hodd : Odd (TorusFields.torusFrame T.side t n).blockSide := hD.L_odd
  have hl := isMinimizingChart_zero hD hFlat hOne (F := TorusFields.torusFrame T.side t n) rfl hside
  have h1 := hasColdMinimizer_of_admissible hD (F := TorusFields.torusFrame T.side t n) rfl (Or.inr hside) _
    (ColdStepAtMirrorFrames.BlockOffsets.mem_finiteCells h2) T.σA hσ le_rfl
    (BlockAverages.flatField (TorusFields.torusFrame T.side t n) (TorusFields.torusFrame T.side t n).top)
    ((hFlat (TorusFields.torusFrame T.side t n) T.coupling (ColdStepAtMirrorFrames.finiteCells _)
      (by linarith [hD.a_ge]) hodd).1 _ T.σA hσ)
  have huniq := (hOne _ T.coupling T.ρA (T.N 0) T.σA _ _ hodd h2 hρ1 h1 hl).1
  have hex : ∃ w, BlockAverages.IsMinimizingChart T.coupling
      (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame T.side t n))
      (BlockAverages.flatField (TorusFields.torusFrame T.side t n) (TorusFields.torusFrame T.side t n).top) T.ρA w :=
    ⟨_, hl⟩
  have e : BlockAverages.minimizingCoordinates T.coupling
      (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame T.side t n))
      (BlockAverages.flatField (TorusFields.torusFrame T.side t n) (TorusFields.torusFrame T.side t n).top) T.ρA =
      fun _ _ => 0 := by
    unfold BlockAverages.minimizingCoordinates
    rw [dif_pos hex]
    exact huniq _ hex.choose_spec
  show BlockAverages.minimizingCoordinates T.coupling
    (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame T.side t n))
    (BlockAverages.flatField (TorusFields.torusFrame T.side t n) (TorusFields.torusFrame T.side t n).top) T.ρA _ _ = 0
  rw [e]
end Flat
section Tangents
variable {a ρ δ lam σA cg : ℝ} {N : ℕ → ℝ} {L t n : ℕ}
private abbrev fineBondInFrame (L t n : ℕ) (b : TorusFields.TorusBond (n * L)) :
    (TorusFields.torusFrame L t n).Site (TorusFields.torusFrame L t n).depth × Fin 4 :=
  (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).depth b.1, b.2)
private abbrev coarseBondInFrame (L t n : ℕ) (c : TorusFields.TorusBond n) :
    (TorusFields.torusFrame L t n).Site (TorusFields.torusFrame L t n).top × Fin 4 :=
  (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top c.1, c.2)
open Classical in
private def minimizerTangent (a ρ : ℝ) (L t n : ℕ) (c : TorusFields.TorusBond n)
    (X : BlockAverages.imaginaryQuaternions) (b : TorusFields.TorusBond (n * L)) :
    BlockAverages.imaginaryQuaternions :=
  coordSlope (TorusFields.torusFrame L t n) X a ρ (fineBondInFrame L t n b) (coarseBondInFrame L t n c) +
    if TorusCharts.IsBlockEndBond L b.1 b.2 ∧ TorusLumps.parentBlock L b.1 = c.1 ∧ b.2 = c.2 then X else 0
variable [NeZero L] [NeZero n]
private theorem minimizerOnFinerTorus_eq_torusChart (hL : Odd L) (h2 : 2 ≤ n) (a ρ : ℝ)
    (V : TorusFields.TorusField n) (x : TorusFields.TorusSite (n * L)) (i : Fin 4) :
    SlopeCoefficient.minimizerOnFinerTorus a ρ L t n V x i =
      TorusCharts.torusChart L (fun b => TwoLevelMixtures.minimizerCoord a L ρ t V b) V x i := by
  have hn : ∀ i, (TorusFields.torusFrame L t n).extent i = n := fun _ => rfl
  haveI : NeZero (n * (TorusFields.torusFrame L t n).blockSide) := inferInstanceAs (NeZero (n * L))
  have e₁ := TorusCharts.chartedField_readAtLevel (F := TorusFields.torusFrame L t n) hn hL h2
    (ColdStepAtMirrorFrames.coordsAboveFrame true a ρ 0
      (TorusFields.readAtLevel (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top V) 0) V x i
  have e₀ : SlopeCoefficient.minimizerOnFinerTorus a ρ L t n V x i =
      BlockAverages.chartedField (ColdStepAtMirrorFrames.coordsAboveFrame true a ρ 0
        (TorusFields.readAtLevel (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top V) 0)
      (TorusFields.readAtLevel (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top V)
      (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).depth x) i := rfl
  refine e₀.trans (e₁.trans ?_)
  refine TorusCharts.torusChart_congr V ?_
  show ColdStepAtMirrorFrames.stepFrame true a ρ 0 _ _ + ColdStepAtMirrorFrames.stepCoordinates
    (0 : ColdStepAtMirrorFrames.StepVariable (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L t n))) _ _ = _
  have e0 : ∀ (x : (TorusFields.torusFrame L t n).Site (TorusFields.torusFrame L t n).depth) (i : Fin 4),
      ColdStepAtMirrorFrames.stepCoordinates
        (0 : ColdStepAtMirrorFrames.StepVariable (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L t n)))
        x i = 0 := by
    intro x i
    unfold ColdStepAtMirrorFrames.stepCoordinates
    split_ifs
    · apply Subtype.ext
      simp [ColdStepAtMirrorFrames.toImaginary]
      rfl
    · rfl
  rw [e0, add_zero]
  simp [ColdStepAtMirrorFrames.stepFrame, TwoLevelMixtures.minimizerCoord, ColdStepAtMirrorFrames.torusCoordinate]
  rfl
private def coarseBondsInFrame {k : ℕ} (L t : ℕ) (c : Fin k → TorusFields.TorusBond n) :
    Fin k → (TorusFields.torusFrame L t n).Site (TorusFields.torusFrame L t n).top × Fin 4 :=
  fun l => (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top (c l).1,
    (c l).2)
private theorem readAtLevel_perturb_eq {k : ℕ} (c : Fin k → TorusFields.TorusBond n)
    (X : Fin k → BlockAverages.imaginaryQuaternions) (σ : Fin k → ℝ) (V : TorusFields.TorusField n) :
    TorusFields.readAtLevel (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top
        (TorusFields.perturb c X σ V) =
      ColdStepAtMirrorFrames.leftTranslate (ColdStepAtMirrorFrames.bondSpread (coarseBondsInFrame L t c) X σ)
        (TorusFields.readAtLevel (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top V) := by
  have per_eq : ∀ i, (TorusFields.torusFrame L t n).period (TorusFields.torusFrame L t n).top i = n :=
    fun i => TopLevelSites.period_top i
  funext x i
  have e : (∑ l, if c l = (TorusLumps.toTorusSite n x, i) then σ l • X l else 0) =
      ColdStepAtMirrorFrames.bondSpread (coarseBondsInFrame L t c) X σ x i := by
    unfold ColdStepAtMirrorFrames.bondSpread
    refine Finset.sum_congr rfl fun l _ => ?_
    have : c l = (TorusLumps.toTorusSite n x, i) ↔ coarseBondsInFrame L t c l = (x, i) := by
      constructor
      · intro h
        simp only [coarseBondsInFrame, h, TopLevelSites.torusSiteInFrame_toTorusSite per_eq]
      · intro h
        have h1 := congrArg Prod.fst h
        have h2 := congrArg Prod.snd h
        simp only [coarseBondsInFrame] at h1 h2
        refine Prod.ext ?_ h2
        rw [← h1, TopLevelSites.toTorusSite_torusSiteInFrame per_eq]
    simp only [this]
  show BlockAverages.expUnit (∑ l, if c l = (TorusLumps.toTorusSite n x, i) then σ l • X l else 0) *
    V (TorusLumps.toTorusSite n x) i = _
  rw [e]
  rfl
abbrev _root_.YangMills.DeltaSharedProofs.p502130 := @readAtLevel_perturb_eq
private theorem minimizerCoord_perturb {k : ℕ} (c : Fin k → TorusFields.TorusBond n)
    (X : Fin k → BlockAverages.imaginaryQuaternions) (σ : Fin k → ℝ) (b : TorusFields.TorusBond (n * L)) :
    TwoLevelMixtures.minimizerCoord a L ρ t (TorusFields.perturb c X σ (TorusFields.trivialField n)) b =
      ColdStepAtMirrorFrames.torusCoordinate (F := TorusFields.torusFrame L t n) a ρ (fineBondInFrame L t n b)
        (ColdStepAtMirrorFrames.leftTranslate (ColdStepAtMirrorFrames.bondSpread (coarseBondsInFrame L t c) X σ)
          (ColdStepAtMirrorFrames.uniformField (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top)) := by
  unfold TwoLevelMixtures.minimizerCoord
  rw [readAtLevel_perturb_eq]
  rfl
private theorem analyticAt_minimizerCoord (hc : ColdChain.ColdChainConstants a δ L lam ρ σA cg N) (hn : 64 ≤ n)
    {k : ℕ} (c : Fin k → TorusFields.TorusBond n)
    (X : Fin k → BlockAverages.imaginaryQuaternions) (b : TorusFields.TorusBond (n * L)) :
    AnalyticAt ℝ (fun σ : Fin k → ℝ =>
      TwoLevelMixtures.minimizerCoord a L ρ t (TorusFields.perturb c X σ (TorusFields.trivialField n)) b) 0 := by
  simp only [minimizerCoord_perturb]
  by_cases hb : fineBondInFrame L t n b ∈
      BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L t n))
  · exact ((flatTop_coordinates hc (u := t) hn).1 _ hb).1 k (coarseBondsInFrame L t c) X
  · have : (fun σ : Fin k → ℝ => ColdStepAtMirrorFrames.torusCoordinate (F := TorusFields.torusFrame L t n) a ρ
        (fineBondInFrame L t n b)
        (ColdStepAtMirrorFrames.leftTranslate (ColdStepAtMirrorFrames.bondSpread (coarseBondsInFrame L t c) X σ)
          (ColdStepAtMirrorFrames.uniformField (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top))) =
        fun _ => 0 := funext fun σ => minimizingBondCoordinate_of_not_mem hb _
    rw [this]
    exact analyticAt_const
private theorem contDiffAt_expUnit {k : ℕ} {w : (Fin k → ℝ) → BlockAverages.imaginaryQuaternions}
    (hw : ContDiffAt ℝ 2 w 0) :
    ContDiffAt ℝ 2 (fun σ => ((BlockAverages.expUnit (w σ) : BlockAverages.UnitQuaternion) : ℍ[ℝ])) 0 := by
  have h1 : ContDiffAt ℝ 2 (fun σ => ((w σ : BlockAverages.imaginaryQuaternions) : ℍ[ℝ])) 0 :=
    BlockAverages.imaginaryQuaternions.subtypeL.contDiff.contDiffAt.comp (0 : Fin k → ℝ) hw
  exact ContDiffAt.comp (g := (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ])) (0 : Fin k → ℝ)
    (NormedSpace.exp_analytic (𝕂 := ℝ) _).contDiffAt h1
private theorem perturb_trivialField_apply {k : ℕ} (c : Fin k → TorusFields.TorusBond n)
    (X : Fin k → BlockAverages.imaginaryQuaternions) (σ : Fin k → ℝ) (y : TorusFields.TorusSite n) (i : Fin 4) :
    TorusFields.perturb c X σ (TorusFields.trivialField n) y i =
      BlockAverages.expUnit (FlatFieldJets.perturbationForm c X σ (y, i)) := by
  rw [FlatFieldJets.perturb_trivialField]
  rfl
private theorem contDiffAt_minimizer (hL : Odd L) (hc : ColdChain.ColdChainConstants a δ L lam ρ σA cg N)
    (hn : 64 ≤ n) (k : ℕ) (c : Fin k → TorusFields.TorusBond n) (X : Fin k → BlockAverages.imaginaryQuaternions)
    (b : TorusFields.TorusBond (n * L)) :
    ContDiffAt ℝ 2 (fun σ : Fin k → ℝ => ((SlopeCoefficient.minimizerOnFinerTorus a ρ L t n
      (TorusFields.perturb c X σ (TorusFields.trivialField n)) b.1 b.2 : BlockAverages.UnitQuaternion) : ℍ[ℝ])) 0 := by
  have h2 : 2 ≤ n := by omega
  have hw : ContDiffAt ℝ 2 (fun σ : Fin k → ℝ =>
      TwoLevelMixtures.minimizerCoord a L ρ t (TorusFields.perturb c X σ (TorusFields.trivialField n)) b) 0 :=
    (analyticAt_minimizerCoord hc hn c X b).contDiffAt
  simp only [minimizerOnFinerTorus_eq_torusChart hL h2]
  unfold TorusCharts.torusChart
  by_cases h1 : TorusCharts.IsBlockEndBond L b.1 b.2
  · simp only [if_pos h1]
    have hm : ContDiffAt ℝ 2 (fun σ : Fin k → ℝ => ((TorusFields.perturb c X σ (TorusFields.trivialField n)
        (TorusLumps.parentBlock L b.1) b.2 : BlockAverages.UnitQuaternion) : ℍ[ℝ])) 0 := by
      simp only [perturb_trivialField_apply]
      exact contDiffAt_expUnit (((ContinuousLinearMap.proj (TorusLumps.parentBlock L b.1, b.2) :
        (TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions) →L[ℝ] BlockAverages.imaginaryQuaternions).comp
          (FlatFieldJets.perturbationForm c X)).contDiff.contDiffAt)
    exact (contDiffAt_expUnit hw).mul hm
  · simp only [if_neg h1]
    by_cases h3 : TorusCharts.IsBlockTreeBond L b.1 b.2
    · simp only [if_pos h3]
      exact contDiffAt_const
    · simp only [if_neg h3]
      exact contDiffAt_expUnit hw
private theorem hasDerivAt_expUnit (u : ℝ → BlockAverages.imaginaryQuaternions)
    (u' : BlockAverages.imaginaryQuaternions) (h0 : u 0 = 0) (hu : HasDerivAt u u' 0) :
    HasDerivAt (fun s => ((BlockAverages.expUnit (u s) : BlockAverages.UnitQuaternion) : ℍ[ℝ])) (u' : ℍ[ℝ]) 0 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlatTopExpansionHessian.hasDerivAt_expUnit_path <;> assumption
private theorem single_eq_smul (s : ℝ) : (![s] : Fin 1 → ℝ) = s • (Pi.single 0 1 : Fin 1 → ℝ) := by
  funext l
  fin_cases l
  simp
private theorem coarseBondsInFrame_single (c : TorusFields.TorusBond n) :
    coarseBondsInFrame L t ![c] = ![coarseBondInFrame L t n c] := by
  funext l
  fin_cases l
  rfl
private theorem hasDerivAt_minimizerCoord (hc : ColdChain.ColdChainConstants a δ L lam ρ σA cg N) (hn : 64 ≤ n)
    (c : TorusFields.TorusBond n) (X : BlockAverages.imaginaryQuaternions) (b : TorusFields.TorusBond (n * L)) :
    HasDerivAt (fun s : ℝ => TwoLevelMixtures.minimizerCoord a L ρ t
        (TorusFields.perturb ![c] ![X] ![s] (TorusFields.trivialField n)) b)
      (coordSlope (TorusFields.torusFrame L t n) X a ρ (fineBondInFrame L t n b) (coarseBondInFrame L t n c)) 0 := by
  set G : (Fin 1 → ℝ) → BlockAverages.imaginaryQuaternions := fun τ =>
    TwoLevelMixtures.minimizerCoord a L ρ t (TorusFields.perturb ![c] ![X] τ (TorusFields.trivialField n)) b with hG
  have hd : DifferentiableAt ℝ G 0 :=
    (analyticAt_minimizerCoord hc hn ![c] ![X] b).differentiableAt
  have e : coordSlope (TorusFields.torusFrame L t n) X a ρ (fineBondInFrame L t n b) (coarseBondInFrame L t n c) =
      fderiv ℝ G 0 (Pi.single 0 1) := by
    have h1 : G = fun τ : Fin 1 → ℝ => ColdStepAtMirrorFrames.torusCoordinate (F := TorusFields.torusFrame L t n)
        a ρ (fineBondInFrame L t n b)
        (ColdStepAtMirrorFrames.leftTranslate (ColdStepAtMirrorFrames.bondSpread ![coarseBondInFrame L t n c] ![X] τ)
          (ColdStepAtMirrorFrames.uniformField (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top)) := by
      funext τ
      rw [hG]
      simp only [minimizerCoord_perturb, coarseBondsInFrame_single]
    rw [h1]
    unfold coordSlope ColdStepAtMirrorFrames.bondDeriv
    rw [iteratedFDeriv_one_apply]
  have hp : HasDerivAt (fun s : ℝ => s • (Pi.single 0 1 : Fin 1 → ℝ)) (Pi.single 0 1) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (Pi.single 0 1 : Fin 1 → ℝ)
  have h1 : HasFDerivAt G (fderiv ℝ G 0) ((0 : ℝ) • (Pi.single 0 1 : Fin 1 → ℝ)) := by
    simpa using hd.hasFDerivAt
  have h2 := h1.comp_hasDerivAt (0 : ℝ) hp
  rw [e]
  have h3 : (fun s : ℝ => TwoLevelMixtures.minimizerCoord a L ρ t
      (TorusFields.perturb ![c] ![X] ![s] (TorusFields.trivialField n)) b) =
      G ∘ fun s : ℝ => s • (Pi.single 0 1 : Fin 1 → ℝ) := by
    funext s
    simp only [hG, Function.comp, single_eq_smul]
  rw [h3]
  exact h2
private theorem perturb_single_zero (c : TorusFields.TorusBond n) (X : BlockAverages.imaginaryQuaternions) :
    TorusFields.perturb ![c] ![X] ![(0 : ℝ)] (TorusFields.trivialField n) = TorusFields.trivialField n := by
  funext x i
  simp [TorusFields.perturb, TorusFields.trivialField, FlatFieldJets.expUnit_zero]
open Classical in
private theorem hasDerivAt_minimizer (hL : Odd L) (hc : ColdChain.ColdChainConstants a δ L lam ρ σA cg N)
    (hn : 64 ≤ n)
    (hz : ∀ b : TorusFields.TorusBond (n * L), TwoLevelMixtures.minimizerCoord a L ρ t (TorusFields.trivialField n) b = 0)
    (c : TorusFields.TorusBond n) (X : BlockAverages.imaginaryQuaternions) (b : TorusFields.TorusBond (n * L)) :
    HasDerivAt (fun s : ℝ => ((SlopeCoefficient.minimizerOnFinerTorus a ρ L t n
        (TorusFields.perturb ![c] ![X] ![s] (TorusFields.trivialField n)) b.1 b.2 : BlockAverages.UnitQuaternion) :
          ℍ[ℝ]))
      ((minimizerTangent a ρ L t n c X b : BlockAverages.imaginaryQuaternions) : ℍ[ℝ]) 0 := by
  have h2 : 2 ≤ n := by omega
  have hw := hasDerivAt_minimizerCoord (t := t) hc hn c X b
  have h0 : TwoLevelMixtures.minimizerCoord a L ρ t
      (TorusFields.perturb ![c] ![X] ![(0 : ℝ)] (TorusFields.trivialField n)) b = 0 := by
    rw [perturb_single_zero]
    exact hz b
  have he := hasDerivAt_expUnit _ _ h0 hw
  simp only [minimizerOnFinerTorus_eq_torusChart hL h2]
  unfold TorusCharts.torusChart minimizerTangent
  by_cases h1 : TorusCharts.IsBlockEndBond L b.1 b.2
  · simp only [if_pos h1]
    set v : ℝ → BlockAverages.imaginaryQuaternions := fun s =>
      FlatFieldJets.perturbationForm ![c] ![X] ![s] (TorusLumps.parentBlock L b.1, b.2) with hv
    have hv' : ∀ s, v s = s • (if c = (TorusLumps.parentBlock L b.1, b.2) then X else 0) := by
      intro s
      by_cases hq : c = (TorusLumps.parentBlock L b.1, b.2)
      · simp [hv, FlatFieldJets.perturbationForm_apply, hq]
      · simp [hv, FlatFieldJets.perturbationForm_apply, hq]
    have hvd : HasDerivAt v (if c = (TorusLumps.parentBlock L b.1, b.2) then X else 0) 0 := by
      have : v = fun s => s • (if c = (TorusLumps.parentBlock L b.1, b.2) then X else 0) := funext hv'
      rw [this]
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const (if c = (TorusLumps.parentBlock L b.1, b.2) then X else 0)
    have hm := hasDerivAt_expUnit v _ (by simp [hv']) hvd
    have hmul := he.mul hm
    have e0 : ((BlockAverages.expUnit (TwoLevelMixtures.minimizerCoord a L ρ t
        (TorusFields.perturb ![c] ![X] ![(0 : ℝ)] (TorusFields.trivialField n)) b) :
          BlockAverages.UnitQuaternion) : ℍ[ℝ]) = 1 := by
      rw [h0, FlatFieldJets.expUnit_zero]
      rfl
    have e1 : ((BlockAverages.expUnit (v 0) : BlockAverages.UnitQuaternion) : ℍ[ℝ]) = 1 := by
      rw [hv' 0, zero_smul, FlatFieldJets.expUnit_zero]
      rfl
    rw [e0, e1, mul_one, one_mul] at hmul
    have e2 : (fun σ : ℝ => ((BlockAverages.expUnit (TwoLevelMixtures.minimizerCoord a L ρ t
        (TorusFields.perturb ![c] ![X] ![σ] (TorusFields.trivialField n)) b) *
        TorusFields.perturb ![c] ![X] ![σ] (TorusFields.trivialField n) (TorusLumps.parentBlock L b.1) b.2 :
          BlockAverages.UnitQuaternion) : ℍ[ℝ])) =
        (fun s => ((BlockAverages.expUnit (TwoLevelMixtures.minimizerCoord a L ρ t
          (TorusFields.perturb ![c] ![X] ![s] (TorusFields.trivialField n)) b) : BlockAverages.UnitQuaternion) :
            ℍ[ℝ])) *
          fun s => ((BlockAverages.expUnit (v s) : BlockAverages.UnitQuaternion) : ℍ[ℝ]) := by
      funext σ
      rw [perturb_trivialField_apply]
      rfl
    rw [e2]
    refine hmul.congr_deriv ?_
    have e3 : (TorusCharts.IsBlockEndBond L b.1 b.2 ∧ TorusLumps.parentBlock L b.1 = c.1 ∧ b.2 = c.2) ↔
        c = (TorusLumps.parentBlock L b.1, b.2) := by
      constructor
      · rintro ⟨-, h3, h4⟩
        exact Prod.ext h3.symm h4.symm
      · intro h3
        exact ⟨h1, by rw [h3], by rw [h3]⟩
    by_cases q : c = (TorusLumps.parentBlock L b.1, b.2)
    · rw [if_pos (e3.mpr q), if_pos q]
      rfl
    · rw [if_neg (fun h => q (e3.mp h)), if_neg q]
      rfl
  · have hcond : ¬ (TorusCharts.IsBlockEndBond L b.1 b.2 ∧ TorusLumps.parentBlock L b.1 = c.1 ∧ b.2 = c.2) :=
      fun h => h1 h.1
    simp only [if_neg h1, if_neg hcond, add_zero]
    by_cases h3 : TorusCharts.IsBlockTreeBond L b.1 b.2
    · simp only [if_pos h3]
      have hn' : ∀ i, (TorusFields.torusFrame L t n).extent i = n := fun _ => rfl
      haveI : NeZero (n * (TorusFields.torusFrame L t n).blockSide) := inferInstanceAs (NeZero (n * L))
      have ht : BlockAverages.IsAxialTreeBond (fineBondInFrame L t n b) :=
        (TopLevelSites.isAxialTreeBond_torusSiteInFrame_iff hn' hL h2 b.1 b.2).mpr h3
      rw [coordSlope_of_not_mem (fun hm => (mem_chordBonds.mp hm).2 ht)]
      simpa using hasDerivAt_const (0 : ℝ) (1 : ℍ[ℝ])
    · simp only [if_neg h3]
      exact he
open Classical in
private theorem norm_minimizerTangent_le (hc : ColdChain.ColdChainConstants a δ L lam ρ σA cg N) (hn : 64 ≤ n)
    {X : BlockAverages.imaginaryQuaternions} (hX : ‖X‖ = 1) (c : TorusFields.TorusBond n)
    (b : TorusFields.TorusBond (n * L)) :
    ‖minimizerTangent a ρ L t n c X b‖ ≤
      (N 1 + 1) * Real.exp (-(δ * (TorusFields.supDist (TorusLumps.parentBlock L b.1) c.1 : ℝ))) := by
  haveI : NeZero (n * (TorusFields.torusFrame L t n).blockSide) := inferInstanceAs (NeZero (n * L))
  have hcell : BlockAverages.enclosingCell
      (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).depth b.1) =
      StepCosts.torusSiteInFrame (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top
        (TorusLumps.parentBlock L b.1) :=
    TopLevelSites.enclosingCell_torusSiteInFrame (F := TorusFields.torusFrame L t n) (n := n) (fun _ => rfl) b.1
  have hd : BlockAverages.cellSupDist (BlockAverages.enclosingCell
      (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).depth b.1))
      (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top c.1) =
      TorusFields.supDist (TorusLumps.parentBlock L b.1) c.1 := by
    rw [hcell, TorusChain.cellSupDist_torusSiteInFrame period_top_torusFrame]
  have hs := norm_coordSlope_le (a := a) (ρ := ρ) hc (u := t) hn hX (fineBondInFrame L t n b)
    (coarseBondInFrame L t n c)
  simp only [hd] at hs
  have hE : 0 < Real.exp (-(δ * (TorusFields.supDist (TorusLumps.parentBlock L b.1) c.1 : ℝ))) := Real.exp_pos _
  unfold minimizerTangent
  refine (norm_add_le _ _).trans ?_
  rw [add_mul, one_mul]
  refine add_le_add ?_ ?_
  · simpa [neg_mul] using hs
  · split_ifs with hq
    · have h0 : TorusFields.supDist (TorusLumps.parentBlock L b.1) c.1 = 0 := by
        rw [hq.2.1]
        exact TorusFields.supDist_self _
      rw [h0, hX]
      simp
    · simpa using hE.le
private theorem blockCentre_add_siteOfInt_eq (w p : Fin 4 → ℤ) :
    CongruentBoxes.blockCentre L (TorusFields.siteOfInt w : TorusFields.TorusSite n) + TorusFields.siteOfInt p =
      TorusFields.siteOfInt (BlockAverages.SameOffsets.scaleOffset L w + p) := by
  rw [CongruentBoxes.blockCentre_add_siteOfInt]
  funext j
  simp only [TorusFields.siteOfInt, BlockAverages.SameOffsets.scaleOffset, Pi.add_apply]
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  have hc : (((w j : ZMod n)).cast : ℤ) = w j % (n : ℤ) := ZMod.coe_intCast _
  rw [hc, Int.emod_def]
  refine ⟨w j / (n : ℤ), ?_⟩
  push_cast
  ring
private theorem isBlockEndBond_siteOfInt_iff (hL : Odd L) (v : Fin 4 → ℤ) (i : Fin 4) :
    TorusCharts.IsBlockEndBond L (TorusFields.siteOfInt v : TorusFields.TorusSite (n * L)) i ↔
      LumpContours.offsetFromCentre L (v i) = TopLevelSites.halfWidth L := by
  have hL0 : 0 < L := hL.pos
  unfold TorusCharts.IsBlockEndBond
  have hc : (((TorusFields.siteOfInt v : TorusFields.TorusSite (n * L)) i).cast : ℤ) =
      v i + (L : ℤ) * (-((n : ℤ) * (v i / ((n * L : ℕ) : ℤ)))) := by
    have : (((v i : ZMod (n * L))).cast : ℤ) = v i % ((n * L : ℕ) : ℤ) := ZMod.coe_intCast _
    show (((v i : ZMod (n * L))).cast : ℤ) = _
    rw [this, Int.emod_def]
    push_cast
    ring
  rw [hc, TorusLumps.offsetFromCentre_add_dvd hL0 hL _ _ (Dvd.intro _ rfl)]
open Classical in
private theorem norm_minimizerTangent_sub_le (hc : ColdChain.ColdChainConstants a δ L lam ρ σA cg N) (hodd : Odd L)
    {n' r : ℕ} [NeZero n']
    (hn : 64 ≤ n) (hn' : 64 ≤ n') (hr : 16 ≤ r) (h2 : 2 * r + 2 < n) (h2' : 2 * r + 2 < n') (v e : Fin 4 → ℤ)
    (i k : Fin 4) {X : BlockAverages.imaginaryQuaternions} (hX : ‖X‖ = 1)
    (he : ∀ j, |e j - CongruentBoxes.coarseOffset L v j| + 1 ≤ (r : ℤ)) :
    ‖((minimizerTangent a ρ L t n (TorusFields.siteOfInt e, k) X (TorusFields.siteOfInt v, i) :
        BlockAverages.imaginaryQuaternions) : ℍ[ℝ]) -
      ((minimizerTangent a ρ L t n' (TorusFields.siteOfInt e, k) X (TorusFields.siteOfInt v, i) :
        BlockAverages.imaginaryQuaternions) : ℍ[ℝ])‖ ≤ N 1 * Real.exp (-δ * ((r : ℝ) - 2)) := by
  obtain ⟨bk, hbk⟩ : ∃ bk, bk = CongruentBoxes.coarseOffset L v := ⟨_, rfl⟩
  obtain ⟨p, hp0⟩ : ∃ p, p = offsetInBlock L v := ⟨_, rfl⟩
  have hvp : BlockAverages.SameOffsets.scaleOffset L bk + p = v := by
    rw [hbk, hp0]
    simp [offsetInBlock]
  have hpc : p ∈ BlockAverages.centredCube L := hp0 ▸ offsetInBlock_mem hodd v
  have hpb : ∀ j, |p j| ≤ 2 * (L : ℤ) := by
    intro j
    have h1 := (ColdStepAtMirrorFrames.BlockOffsets.mem_centredCube_iff _).mp hpc j
    have h3 : (1 : ℤ) ≤ L := by exact_mod_cast hodd.pos
    have h4 : ColdStepAtMirrorFrames.BlockOffsets.halfSide L ≤ L := by
      unfold ColdStepAtMirrorFrames.BlockOffsets.halfSide
      omega
    obtain ⟨h5, h6⟩ := h1
    exact abs_le.mpr ⟨by omega, by omega⟩
  have hv₁ : CongruentBoxes.blockCentre L (TorusFields.siteOfInt bk : TorusFields.TorusSite n) +
      TorusFields.siteOfInt p = (TorusFields.siteOfInt v : TorusFields.TorusSite (n * L)) := by
    rw [blockCentre_add_siteOfInt_eq, hvp]
  have hv₂ : CongruentBoxes.blockCentre L (TorusFields.siteOfInt bk : TorusFields.TorusSite n') +
      TorusFields.siteOfInt p = (TorusFields.siteOfInt v : TorusFields.TorusSite (n' * L)) := by
    rw [blockCentre_add_siteOfInt_eq, hvp]
  have hc₁ : (TorusFields.siteOfInt bk : TorusFields.TorusSite n) + TorusFields.siteOfInt (e - bk) =
      TorusFields.siteOfInt e := by
    rw [← TorusFields.siteOfInt_add]
    simp
  have hc₂ : (TorusFields.siteOfInt bk : TorusFields.TorusSite n') + TorusFields.siteOfInt (e - bk) =
      TorusFields.siteOfInt e := by
    rw [← TorusFields.siteOfInt_add]
    simp
  have hbox : BlockAverages.BondWithinRadius r (e - bk, k) := by
    constructor
    · intro j
      have := he j
      rw [← hbk] at this
      show |(e - bk) j| ≤ (r : ℤ)
      simp only [Pi.sub_apply]
      omega
    · intro j
      have h3 := he j
      rw [← hbk] at h3
      have h4 : |(Pi.single k 1 : Fin 4 → ℤ) j| ≤ 1 := abs_basisVector_le k j
      show |((e - bk) + (Pi.single k 1 : Fin 4 → ℤ)) j| ≤ (r : ℤ)
      simp only [Pi.add_apply, Pi.sub_apply]
      exact (abs_add_le _ _).trans (by omega)
  have hsl := norm_coordSlope_sub_le (a := a) (ρ := ρ) hc hodd (u := t) hn hn' hr h2 h2'
    (TorusFields.siteOfInt bk : TorusFields.TorusSite n) (TorusFields.siteOfInt bk : TorusFields.TorusSite n')
    hpb i hbox hX
  rw [← torusSiteInFrame_blockCentre_add, ← torusSiteInFrame_blockCentre_add, hv₁, hv₂,
    ← torusSiteInFrame_top_add_siteOfInt, ← torusSiteInFrame_top_add_siteOfInt, hc₁, hc₂] at hsl
  have hbo₁ : TorusLumps.parentBlock L (TorusFields.siteOfInt v : TorusFields.TorusSite (n * L)) =
      TorusFields.siteOfInt bk := by
    rw [CongruentBoxes.parentBlock_siteOfInt, hbk]
    rfl
  have hbo₂ : TorusLumps.parentBlock L (TorusFields.siteOfInt v : TorusFields.TorusSite (n' * L)) =
      TorusFields.siteOfInt bk := by
    rw [CongruentBoxes.parentBlock_siteOfInt, hbk]
    rfl
  have hsmall : ∀ j, |bk j - e j| < (r : ℤ) := by
    intro j
    have := he j
    rw [← hbk, abs_sub_comm] at this
    omega
  have hiff₁ : (TorusFields.siteOfInt bk : TorusFields.TorusSite n) = TorusFields.siteOfInt e ↔ bk = e :=
    ⟨fun h => TorusLumps.eq_of_siteOfInt_eq h fun j => by have := hsmall j; omega, fun h => by rw [h]⟩
  have hiff₂ : (TorusFields.siteOfInt bk : TorusFields.TorusSite n') = TorusFields.siteOfInt e ↔ bk = e :=
    ⟨fun h => TorusLumps.eq_of_siteOfInt_eq h fun j => by have := hsmall j; omega, fun h => by rw [h]⟩
  have hcond : (TorusCharts.IsBlockEndBond L (TorusFields.siteOfInt v : TorusFields.TorusSite (n * L)) i ∧
        TorusLumps.parentBlock L (TorusFields.siteOfInt v : TorusFields.TorusSite (n * L)) =
          TorusFields.siteOfInt e ∧ i = k) ↔
      (TorusCharts.IsBlockEndBond L (TorusFields.siteOfInt v : TorusFields.TorusSite (n' * L)) i ∧
        TorusLumps.parentBlock L (TorusFields.siteOfInt v : TorusFields.TorusSite (n' * L)) =
          TorusFields.siteOfInt e ∧ i = k) := by
    rw [isBlockEndBond_siteOfInt_iff hodd, isBlockEndBond_siteOfInt_iff hodd, hbo₁, hbo₂, hiff₁, hiff₂]
  unfold minimizerTangent
  simp only []
  by_cases q : TorusCharts.IsBlockEndBond L (TorusFields.siteOfInt v : TorusFields.TorusSite (n * L)) i ∧
      TorusLumps.parentBlock L (TorusFields.siteOfInt v : TorusFields.TorusSite (n * L)) =
        TorusFields.siteOfInt e ∧ i = k
  · rw [if_pos q, if_pos (hcond.mp q)]
    simpa using hsl
  · rw [if_neg q, if_neg (fun h => q (hcond.mpr h))]
    simpa using hsl
end Tangents
end MinimizerTangents
open MinimizerTangents in
theorem minimizerDerivativeDecay_holds (hFlat : BlockAverages.flatTopVanishingStatement)
    (hOne : ColdStepAtMirrorFrames.MinimizingChartUnique) : MinimizerDerivativeDecay := by
  intro T hD
  have hc := hD.chain
  have hodd := hD.L_odd
  have hδ : 0 < T.δ₁ := hc.1
  have hN : 0 < T.N 1 := hc.2.2.2.2.2.2.2.1 1
  refine ⟨(T.N 1 + 1) * Real.exp (2 * T.δ₁), T.δ₁, by positivity, hδ,
    fun t n => minimizerTangent T.coupling T.ρA T.side t n,
    fun t => ⟨fun n _ hn => ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩⟩
  · have h2 : 2 ≤ n := by omega
    funext x i
    rw [minimizerOnFinerTorus_eq_torusChart hodd h2]
    have hz := fun b => minimizerCoord_trivialField (t := t) hD hFlat hOne hn b
    unfold TorusCharts.torusChart
    simp only [hz]
    split_ifs <;> simp [TorusFields.trivialField, FlatFieldJets.expUnit_zero]
  · exact fun k c X b => contDiffAt_minimizer hodd hc hn k c X b
  · exact fun c X b => hasDerivAt_minimizer hodd hc hn (fun b => minimizerCoord_trivialField hD hFlat hOne hn b) c X b
  · intro c X b hX
    refine (norm_minimizerTangent_le hc hn hX c b).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    have h1 : (1 : ℝ) ≤ Real.exp (2 * T.δ₁) := Real.one_le_exp (by positivity)
    nlinarith
  · intro n n' _ _ r u e i k X hn hn' hr h2 h2' hX he
    refine (norm_minimizerTangent_sub_le hc hodd hn hn' hr h2 h2' u e i k hX he).trans ?_
    have h1 : Real.exp (-T.δ₁ * ((r : ℝ) - 2)) = Real.exp (2 * T.δ₁) * Real.exp (-(T.δ₁ * (r : ℝ))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [h1, mul_assoc]
    refine mul_le_mul_of_nonneg_right (by linarith) (by positivity)
end YangMills.Construction.RunningCouplingSlope
end
