import YangMills.Construction.ClusterExpansionOfAStep.AdmissionEqualInBoxes
import YangMills.Construction.HoleBesideASecondHole.CarriedSitesAndPaths
import YangMills.Construction.ClusterExpansionOfAStep.OffsetsOfABlock
import YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderOfADensityAtConstantCurvatureProof
import YangMills.Construction.HoleBesideASecondHole.ActionAtIsACutAction
import YangMills.Construction.HoleBesideASecondHole.BasesAtTwoFrames
import YangMills.Construction.HoleBesideASecondHole.LumpsAtTwoFrames
import YangMills.Construction.HoleBesideASecondHole.TorusAtAFrameDefs
import YangMills.Construction.HoleBesideASecondHole.WhatAHoleSavesOnTori
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.HoleOnTori
open BlockAverages LumpContours FrameTransfer HoleBounds TorusFields TorusLumps StepCosts
namespace FrameComparison
theorem intCast_cast_of_eq {m m' : ℕ} (h : m = m') (v : ℤ) :
    (((ZMod.cast (v : ZMod m) : ℤ)) : ZMod m') = (v : ZMod m') := by apply _root_.YangMills.Construction.FrameTorusAction.intCast_cast_intCast <;> assumption
section General
variable {F F' : BlockFrame} {j j' m : ℕ}
theorem transferSite_torusSiteInFrame (h : ∀ i, F.period j i = m) (h' : ∀ i, F'.period j' i = m)
    (x : TorusSite m) :
    transferSite F' j' (torusSiteInFrame F j x) = torusSiteInFrame F' j' x :=
  funext fun i => intCast_cast_of_eq ((h i).trans (h' i).symm) _
theorem toTorusSite_torusSiteInFrame (h : ∀ i, F.period j i = m) (x : TorusSite m) :
    toTorusSite m (torusSiteInFrame F j x) = x := by apply _root_.YangMills.Construction.FrameTransfer.frameToTorus_torusToFrame <;> assumption
theorem torusSiteInFrame_injective (h : ∀ i, F.period j i = m) :
    Function.Injective (torusSiteInFrame (n := m) F j) := by apply _root_.YangMills.Construction.FrameTransfer.torusToFrame_injective <;> assumption
theorem torusSiteInFrame_toTorusSite (h : ∀ i, F.period j i = m) (y : F'.Site j') :
    torusSiteInFrame F j (toTorusSite m y) = transferSite F j y :=
  funext fun i => intCast_cast_of_eq (h i).symm _
theorem readAtLevel_torusSiteInFrame (h : ∀ i, F.period j i = m) (W : TorusField m) (x : TorusSite m)
    (i : Fin 4) :
    readAtLevel F j W (torusSiteInFrame F j x) i = W x i := by apply _root_.YangMills.Construction.FrameTransfer.readAtLevel_torusToFrame <;> assumption
theorem lumpsNeighbourhood_eq_thicken (H : Finset (Finset (F.Site j))) :
    lumpsNeighbourhood H = thicken lumpRange (H.biUnion id) := by
  rw [lumpsNeighbourhood, thicken, Finset.biUnion_biUnion]
  rfl
end General
section Step
variable (L t n : ℕ)
theorem period_torusFrame_depth : ∀ i, (torusFrame L t n).period (torusFrame L t n).depth i = n * L := by apply _root_.YangMills.Construction.CongruentAdmission.torusFrame_period_depth <;> assumption
theorem period_torusFrame_top : ∀ i, (torusFrame L t n).period (torusFrame L t n).top i = n := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderAtConstantCurvature.torusFrame_period_top <;> assumption
theorem period_stepBlockFrame_zero : ∀ i, (stepBlockFrame L n).period 0 i = n * L := by apply _root_.YangMills.Construction.BlockOffsets.period_zero <;> assumption
theorem period_stepBlockFrame_one : ∀ i, (stepBlockFrame L n).period 1 i = n := by apply _root_.YangMills.Construction.BlockOffsets.period_one <;> assumption
end Step
variable (ℓ : StepParameters) (cE : ℝ) (t : ℕ) {n : ℕ}
theorem sitesOfTorus_eq_image (X : Finset (TorusSite (n * ℓ.side))) :
    sitesOfTorus (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth X =
      X.image (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth) := rfl
theorem stepHotLumps_eq_transfer (hLu : LumpTransfer.lumpTransferStatement)
    (X : Finset (TorusSite (n * ℓ.side))) (W : TorusField (n * ℓ.side)) :
    stepHotLumps ℓ X W = transferLumps (stepBlockFrame ℓ.side n) 0
      (hotLumps ℓ.grid ℓ.threshold (sitesOfTorus (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth X)
        (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth W)) := by
  obtain ⟨-, l2, -, -, -, l6⟩ := hLu (torusFrame ℓ.side t n) (stepBlockFrame ℓ.side n)
    (torusFrame ℓ.side t n).depth 0
    (fun i => (period_torusFrame_depth ℓ.side t n i).trans (period_stepBlockFrame_zero ℓ.side n i).symm)
  rw [← (l6 ℓ.grid).2, l2]
  unfold stepHotLumps
  congr 1
  unfold transferSet sitesOfTorus
  rw [Finset.image_image]
  exact Finset.image_congr fun x _ =>
    (transferSite_torusSiteInFrame (period_torusFrame_depth ℓ.side t n)
      (period_stepBlockFrame_zero ℓ.side n) x).symm
theorem card_transferLumps (hLu : LumpTransfer.lumpTransferStatement)
    (h : Finset (Finset ((torusFrame ℓ.side t n).Site (torusFrame ℓ.side t n).depth))) :
    (transferLumps (stepBlockFrame ℓ.side n) 0 h).card = h.card := by
  obtain ⟨l1, -⟩ := hLu (torusFrame ℓ.side t n) (stepBlockFrame ℓ.side n) (torusFrame ℓ.side t n).depth 0
    (fun i => (period_torusFrame_depth ℓ.side t n i).trans (period_stepBlockFrame_zero ℓ.side n i).symm)
  refine Finset.card_image_of_injective _ fun A B hAB => ?_
  have hinj : Function.Injective (transferSite (F := torusFrame ℓ.side t n) (j := (torusFrame ℓ.side t n).depth)
      (stepBlockFrame ℓ.side n) 0) := Function.LeftInverse.injective l1
  exact Finset.image_injective hinj hAB
theorem sitesOfTorus_stepLumpSites (hLu : LumpTransfer.lumpTransferStatement)
    (h : Finset (Finset ((torusFrame ℓ.side t n).Site (torusFrame ℓ.side t n).depth))) :
    sitesOfTorus (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth
        (stepLumpSites ℓ (transferLumps (stepBlockFrame ℓ.side n) 0 h)) = h.biUnion id := by
  classical
  obtain ⟨l1, -⟩ := hLu (torusFrame ℓ.side t n) (stepBlockFrame ℓ.side n) (torusFrame ℓ.side t n).depth 0
    (fun i => (period_torusFrame_depth ℓ.side t n i).trans (period_stepBlockFrame_zero ℓ.side n i).symm)
  ext x
  simp only [sitesOfTorus, stepLumpSites, transferLumps, transferSet, Finset.mem_image, Finset.mem_biUnion,
    id]
  constructor
  · rintro ⟨y, ⟨l', ⟨l, hl, rfl⟩, hy⟩, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hy
    obtain ⟨z', hz', rfl⟩ := Finset.mem_image.1 hz
    refine ⟨l, hl, ?_⟩
    have e := torusSiteInFrame_toTorusSite (F := torusFrame ℓ.side t n) (F' := stepBlockFrame ℓ.side n)
      (j := (torusFrame ℓ.side t n).depth) (j' := 0) (period_torusFrame_depth ℓ.side t n)
      (transferSite (stepBlockFrame ℓ.side n) 0 z')
    have e2 : torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth
        (toTorusSite (n * ℓ.side) (transferSite (F := torusFrame ℓ.side t n) (stepBlockFrame ℓ.side n) 0 z')) =
          z' := e.trans (l1 z')
    show torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth _ ∈ l
    rw [e2]
    exact hz'
  · rintro ⟨l, hl, hx⟩
    refine ⟨toTorusSite (n * ℓ.side) (transferSite (F := torusFrame ℓ.side t n) (stepBlockFrame ℓ.side n) 0 x),
      ⟨transferSet (stepBlockFrame ℓ.side n) 0 l, ⟨l, hl, rfl⟩, ?_⟩, ?_⟩
    · exact ⟨_, Finset.mem_image.2 ⟨x, hx, rfl⟩, rfl⟩
    · exact (torusSiteInFrame_toTorusSite (F := torusFrame ℓ.side t n) (F' := stepBlockFrame ℓ.side n)
        (j := (torusFrame ℓ.side t n).depth) (j' := 0) (period_torusFrame_depth ℓ.side t n) _).trans (l1 x)
theorem transferBases_transferBases (hLu : LumpTransfer.lumpTransferStatement) (b : BaseChoice ℓ.side n) :
    transferBases (F := torusFrame ℓ.side t n) (stepBlockFrame ℓ.side n)
      (transferBases (F := stepBlockFrame ℓ.side n) (torusFrame ℓ.side t n) b) = b := by
  obtain ⟨l1, -⟩ := hLu (stepBlockFrame ℓ.side n) (torusFrame ℓ.side t n) 0 (torusFrame ℓ.side t n).depth
    (fun i => (period_stepBlockFrame_zero ℓ.side n i).trans (period_torusFrame_depth ℓ.side t n i).symm)
  obtain ⟨l1', -⟩ := hLu (stepBlockFrame ℓ.side n) (torusFrame ℓ.side t n) 1 (torusFrame ℓ.side t n).top
    (fun i => (period_stepBlockFrame_one ℓ.side n i).trans (period_torusFrame_top ℓ.side t n i).symm)
  funext y
  exact (congrArg (fun y' => transferSite (stepBlockFrame ℓ.side n) 0
    (transferSite (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth (b y'))) (l1' y)).trans (l1 (b y))
theorem holeSaving_of_working [NeZero n] (hA : ActionAtLevelIsCutAction)
    (hLu : LumpTransfer.lumpTransferStatement) (hB : BasesAgreeAcrossFrames)
    (hW : TorusFrames.torusAtFrameStatement) (hodd : Odd ℓ.side)
    (ha : 0 ≤ ℓ.coupling) (hcE : 0 ≤ cE) (S₀ S : Finset (TorusSite n))
    (hV : Finset (Finset (torusFrame ℓ.side t n).Cell)) (m : ℕ) (hm : hV.card = m) (V : TorusField n)
    (W Wl : TorusField (n * ℓ.side)) (b : BaseChoice ℓ.side n)
    (hs : HoleSavingWorkingForm ℓ.grid ℓ.coupling ℓ.κ ℓ.threshold cE ℓ.baseDepth
      (cellsOfSites (torusFrame ℓ.side t n) S₀)
      (cellsOfSites (torusFrame ℓ.side t n) S) hV
      (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V)
      (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth W)
      (transferBases (F := stepBlockFrame ℓ.side n) (torusFrame ℓ.side t n) b)
      (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth Wl)) :
    HoleSavingOnTorus ℓ cE t S₀ S m V W Wl b := by
  classical
  obtain ⟨hA1, hA2⟩ := hA ℓ.coupling ha ℓ.side hodd n (torusFrame ℓ.side t n) rfl (fun _ => rfl)
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, -⟩ := hW ℓ.side hodd n (torusFrame ℓ.side t n) rfl (fun _ => rfl)
  obtain ⟨-, l2, -⟩ := hLu (torusFrame ℓ.side t n) (stepBlockFrame ℓ.side n) (torusFrame ℓ.side t n).depth 0
    (fun i => (period_torusFrame_depth ℓ.side t n i).trans (period_stepBlockFrame_zero ℓ.side n i).symm)
  obtain ⟨-, l2', -⟩ := hLu (torusFrame ℓ.side t n) (stepBlockFrame ℓ.side n) (torusFrame ℓ.side t n).top 1
    (fun i => (period_torusFrame_top ℓ.side t n i).trans (period_stepBlockFrame_one ℓ.side n i).symm)
  obtain ⟨-, -, -, -, b5, b6⟩ := hB (torusFrame ℓ.side t n) (stepBlockFrame ℓ.side n) rfl rfl
  unfold HoleSavingWorkingForm at hs
  unfold HoleSavingOnTorus
  set X := sitesInBlocks ℓ.side S₀ with hX
  set WF := readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth W with hWF
  set WlF := readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth Wl with hWlF
  set VF := readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V with hVF
  set bF := transferBases (F := stepBlockFrame ℓ.side n) (torusFrame ℓ.side t n) b with hbF
  rw [← w1 S₀, ← hX] at hs
  set hF := hotLumps ℓ.grid ℓ.threshold
    (sitesOfTorus (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth X) WF with hhF
  have hh : stepHotLumps ℓ X W = transferLumps (stepBlockFrame ℓ.side n) 0 hF :=
    stepHotLumps_eq_transfer ℓ t hLu X W
  have hcard : (stepHotLumps ℓ X W).card = hF.card := by
    rw [hh]
    exact card_transferLumps ℓ t hLu hF
  have e1 : cutEffectiveAction ℓ.coupling (torusFrame ℓ.side t n).top
      (cellsOfSites (torusFrame ℓ.side t n) S) VF =
      actionAtLevel ℓ.coupling ℓ.side (t + 1) S V := hA1 S V
  have e2 : cutEffectiveAction ℓ.coupling (torusFrame ℓ.side t n).depth
      (sitesOfTorus (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth X \ lumpsNeighbourhood hF) WF =
      actionAtLevel ℓ.coupling ℓ.side t (X \ thickening lumpRange (stepLumpSites ℓ (stepHotLumps ℓ X W))) W := by
    have e3 : lumpsNeighbourhood hF = sitesOfTorus (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth
        (thickening lumpRange (stepLumpSites ℓ (stepHotLumps ℓ X W))) := by
      rw [w5, hh, sitesOfTorus_stepLumpSites ℓ t hLu hF, lumpsNeighbourhood_eq_thicken]
    have e4 : sitesOfTorus (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth X \ lumpsNeighbourhood hF =
        sitesOfTorus (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth
          (X \ thickening lumpRange (stepLumpSites ℓ (stepHotLumps ℓ X W))) := by
      rw [e3, sitesOfTorus_eq_image, sitesOfTorus_eq_image, sitesOfTorus_eq_image]
      exact (Finset.image_sdiff _ _ (torusSiteInFrame_injective (period_torusFrame_depth ℓ.side t n))).symm
    rw [e4]
    exact hA2 _ W
  have e5 : ∑ c ∈ cutBonds (cellsOfSites (torusFrame ℓ.side t n) S₀), contourFit ℓ.baseDepth hF bF WF VF c =
      ∑ c ∈ bondsWithin S₀, bondFit ℓ (stepHotLumps ℓ X W) W V b c := by
    rw [w6 S₀, Finset.sum_image]
    · refine Finset.sum_congr rfl fun c _ => ?_
      have h5 := ((b5 ℓ.baseDepth hF bF).2 WF
        (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top c.1, c.2)).2 VF
      rw [← h5, hh]
      unfold bondFit
      have hb : transferBases (F := torusFrame ℓ.side t n) (stepBlockFrame ℓ.side n) bF = b :=
        transferBases_transferBases ℓ t hLu b
      have hc : transferBond (F := torusFrame ℓ.side t n) (stepBlockFrame ℓ.side n) (stepBlockFrame ℓ.side n).top
          (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top c.1, c.2) =
          (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 c.1, c.2) :=
        Prod.ext (transferSite_torusSiteInFrame (period_torusFrame_top ℓ.side t n)
          (period_stepBlockFrame_one ℓ.side n) c.1) rfl
      have hw : transferField (stepBlockFrame ℓ.side n) (stepBlockFrame ℓ.side n).depth WF =
          readAtLevel (stepBlockFrame ℓ.side n) 0 W := l2 _ W
      have hv : transferField (stepBlockFrame ℓ.side n) (stepBlockFrame ℓ.side n).top VF =
          readAtLevel (stepBlockFrame ℓ.side n) 1 V := l2' _ V
      rw [hb, hc, hw, hv]
      rfl
    · intro c _ c' _ hcc
      obtain ⟨h1, h2⟩ := Prod.mk.inj hcc
      exact Prod.ext (torusSiteInFrame_injective (period_torusFrame_top ℓ.side t n) h1) h2
  have e6 : (chartDeviationSites ℓ (ℓ.threshold / 128) S V W Wl).card ≤
      (chartDeviantCells (ℓ.threshold / 128) (cellsOfSites (torusFrame ℓ.side t n) S) VF WF WlF).card := by
    refine Finset.card_le_card_of_injOn (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top) ?_
      ((torusSiteInFrame_injective (period_torusFrame_top ℓ.side t n)).injOn)
    intro y hy
    have hy' := Finset.mem_filter.1 (Finset.mem_coe.1 hy)
    obtain ⟨hyS, c, hc, hcy, hr⟩ := hy'
    refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨y, hyS, rfl⟩, ?_⟩)
    refine ⟨(torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth c.1, c.2), ?_, ?_, ?_⟩
    · rw [← w1 S, w7]
      exact Finset.mem_image.2 ⟨c, hc, rfl⟩
    · simp only
      rw [w3, hcy]
    · have hcoord : ∀ U : TorusField (n * ℓ.side),
          bondCoordinate 1 VF (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth U)
            (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth c.1, c.2) =
            chartCoord ℓ V U c := by
        intro U
        have h6 := b6 1 VF (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth U)
          (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth c.1, c.2)
        rw [← h6]
        have hw : transferField (stepBlockFrame ℓ.side n) (stepBlockFrame ℓ.side n).depth
            (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth U) =
            readAtLevel (stepBlockFrame ℓ.side n) 0 U := l2 _ U
        have hv : transferField (stepBlockFrame ℓ.side n) (stepBlockFrame ℓ.side n).top VF =
            readAtLevel (stepBlockFrame ℓ.side n) 1 V := l2' _ V
        have hc' : transferBond (F := torusFrame ℓ.side t n) (stepBlockFrame ℓ.side n) (stepBlockFrame ℓ.side n).depth
            (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth c.1, c.2) =
            (torusSiteInFrame (stepBlockFrame ℓ.side n) 0 c.1, c.2) :=
          Prod.ext (transferSite_torusSiteInFrame (period_torusFrame_depth ℓ.side t n)
            (period_stepBlockFrame_zero ℓ.side n) c.1) rfl
        rw [hw, hv, hc']
        rfl
      rw [hcoord W, hcoord Wl]
      exact hr
  rw [e1, e2, e5, hm, ← hcard] at hs
  have h6 : cE * ((chartDeviationSites ℓ (ℓ.threshold / 128) S V W Wl).card : ℝ) ≤
      cE * ((chartDeviantCells (ℓ.threshold / 128) (cellsOfSites (torusFrame ℓ.side t n) S) VF WF WlF).card : ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast e6) hcE
  linarith
theorem cellsOfSites_thickening [NeZero n]
    (w4 : ∀ (m : ℕ) (X : Finset (TorusSite n)),
      cellsOfSites (torusFrame ℓ.side t n) (thickening m X) = thicken m (cellsOfSites (torusFrame ℓ.side t n) X))
    (H : Finset (Finset (TorusSite n))) :
    cellsOfSites (torusFrame ℓ.side t n) (thickening lumpRange (H.biUnion id)) =
      lumpsNeighbourhood (H.image (cellsOfSites (torusFrame ℓ.side t n))) := by
  classical
  rw [w4, lumpsNeighbourhood_eq_thicken]
  congr 1
  unfold cellsOfSites
  rw [Finset.image_biUnion, Finset.biUnion_image]
  rfl
theorem cellsOfSites_injective :
    Function.Injective (cellsOfSites (n := n) (torusFrame ℓ.side t n)) :=
  Finset.image_injective (torusSiteInFrame_injective (period_torusFrame_top ℓ.side t n))
theorem isBaseChoice_transferBases (hLu : LumpTransfer.lumpTransferStatement) (hB : BasesAgreeAcrossFrames)
    (X : Finset (TorusSite (n * ℓ.side))) (W : TorusField (n * ℓ.side)) (b : BaseChoice ℓ.side n)
    (h : IsBaseChoice ℓ.baseDepth (stepHotLumps ℓ X W) b) :
    IsBaseChoice ℓ.baseDepth (hotLumps ℓ.grid ℓ.threshold
        (sitesOfTorus (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth X)
        (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth W))
      (transferBases (F := stepBlockFrame ℓ.side n) (torusFrame ℓ.side t n) b) := by
  obtain ⟨-, -, -, -, b5, -⟩ := hB (torusFrame ℓ.side t n) (stepBlockFrame ℓ.side n) rfl rfl
  refine (b5 ℓ.baseDepth _ _).1.1 ?_
  rw [transferBases_transferBases ℓ t hLu b]
  have := stepHotLumps_eq_transfer ℓ t hLu X W
  rw [this] at h
  exact h
end FrameComparison
theorem holeSavingOnTori (hA : ActionAtLevelIsCutAction) (hLu : LumpTransfer.lumpTransferStatement)
    (hB : BasesAgreeAcrossFrames) (hW : TorusFrames.torusAtFrameStatement) :
    holeSavingOnToriStatement := by
  intro ℓ cE hodd ha hcE hS
  refine ⟨?_, ?_⟩
  · intro t n _ hdvd hn H hH V W Wl b hap hleast hag hbases
    classical
    obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12⟩ :=
      hW ℓ.side hodd n (torusFrame ℓ.side t n) rfl (fun _ => rfl)
    obtain ⟨w13, w14⟩ := w12 ℓ rfl hdvd
    have hinjS := FrameComparison.torusSiteInFrame_injective (FrameComparison.period_torusFrame_top ℓ.side t n)
    have e1 : cellsOffLumps (torusFrame ℓ.side t n) (H.image (cellsOfSites (torusFrame ℓ.side t n))) =
        cellsOfSites (torusFrame ℓ.side t n) (awayFromLumps H) := by
      unfold cellsOffLumps awayFromLumps
      rw [← FrameComparison.cellsOfSites_thickening ℓ t w4 H, ← w8]
      exact (Finset.image_sdiff _ _ hinjS).symm
    have e2 : hotLumps ℓ.grid ℓ.threshold
        (cellsOffLumps (torusFrame ℓ.side t n) (H.image (cellsOfSites (torusFrame ℓ.side t n))))
        (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V) =
        (topHotLumps ℓ (awayFromLumps H) V).image (cellsOfSites (torusFrame ℓ.side t n)) := by
      rw [e1]
      exact w14 _ V
    have e3 : cellsOffLumps (torusFrame ℓ.side t n) (H.image (cellsOfSites (torusFrame ℓ.side t n))) \
        lumpsNeighbourhood (hotLumps ℓ.grid ℓ.threshold
          (cellsOffLumps (torusFrame ℓ.side t n) (H.image (cellsOfSites (torusFrame ℓ.side t n))))
          (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V)) =
        cellsOfSites (torusFrame ℓ.side t n) (awayFromLumps H \
          thickening lumpRange ((topHotLumps ℓ (awayFromLumps H) V).biUnion id)) := by
      rw [e2, ← FrameComparison.cellsOfSites_thickening ℓ t w4, e1]
      exact (Finset.image_sdiff _ _ hinjS).symm
    have hlumps : ∀ l ∈ H.image (cellsOfSites (torusFrame ℓ.side t n)), IsLump ℓ.grid l := by
      intro l hl
      obtain ⟨l', hl', rfl⟩ := Finset.mem_image.1 hl
      exact (w13 l').1 (hH l' hl')
    have hapF : CellsSeparated (2 * wallMargin)
        (lumpsNeighbourhood (hotLumps ℓ.grid ℓ.threshold
          (cellsOffLumps (torusFrame ℓ.side t n) (H.image (cellsOfSites (torusFrame ℓ.side t n))))
          (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V)))
        (lumpsNeighbourhood (H.image (cellsOfSites (torusFrame ℓ.side t n)))) := by
      rw [e2, ← FrameComparison.cellsOfSites_thickening ℓ t w4, ← FrameComparison.cellsOfSites_thickening ℓ t w4]
      intro x hx y hy
      obtain ⟨x', hx', rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨y', hy', rfl⟩ := Finset.mem_image.1 hy
      have := hap x' hx' y' hy'
      rw [← w2] at this
      exact this
    have hagF : AgreesWithMinimizerNear (lumpsNeighbourhood (H.image (cellsOfSites (torusFrame ℓ.side t n))))
        (cellsOffLumps (torusFrame ℓ.side t n) (H.image (cellsOfSites (torusFrame ℓ.side t n))) \
          lumpsNeighbourhood (hotLumps ℓ.grid ℓ.threshold
            (cellsOffLumps (torusFrame ℓ.side t n) (H.image (cellsOfSites (torusFrame ℓ.side t n))))
            (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V)))
        (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth W)
        (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth Wl) := by
      rw [e3, ← FrameComparison.cellsOfSites_thickening ℓ t w4]
      intro bd hb z hz hd
      rw [← w1, w7] at hb
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hb
      obtain ⟨z', hz', rfl⟩ := Finset.mem_image.1 hz
      have hd' : supDist (parentBlock ℓ.side c.1) z' ≤ wallMargin := by
        have h1 := w3 c.1
        rw [← w2]
        exact h1 ▸ hd
      have h2 := hag c hc z' hz' hd'
      have r1 := FrameComparison.readAtLevel_torusSiteInFrame
        (FrameComparison.period_torusFrame_depth ℓ.side t n) W c.1 c.2
      have r2 := FrameComparison.readAtLevel_torusSiteInFrame
        (FrameComparison.period_torusFrame_depth ℓ.side t n) Wl c.1 c.2
      exact r1.trans (h2.trans r2.symm)
    have hbF : IsBaseChoice ℓ.baseDepth (hotLumps ℓ.grid ℓ.threshold
        (cutBelow (torusFrame ℓ.side t n).depth
          (cellsOffLumps (torusFrame ℓ.side t n) (H.image (cellsOfSites (torusFrame ℓ.side t n)))))
        (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth W))
        (transferBases (F := stepBlockFrame ℓ.side n) (torusFrame ℓ.side t n) b) := by
      rw [e1, ← w1]
      exact FrameComparison.isBaseChoice_transferBases ℓ t hLu hB _ W b hbases
    have hl : IsMinimizingField ℓ.coupling
        (cellsOffLumps (torusFrame ℓ.side t n) (H.image (cellsOfSites (torusFrame ℓ.side t n))) \
        lumpsNeighbourhood (hotLumps ℓ.grid ℓ.threshold
          (cellsOffLumps (torusFrame ℓ.side t n) (H.image (cellsOfSites (torusFrame ℓ.side t n))))
          (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V)))
        (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V)
        (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth Wl) := by
      rw [e3]
      exact hleast
    have h := hS.holed (torusFrame ℓ.side t n) rfl ⟨fun _ => rfl, hn⟩ hdvd _ hlumps
      (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V)
      (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth W)
      (transferBases (F := stepBlockFrame ℓ.side n) (torusFrame ℓ.side t n) b)
      (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth Wl) hapF hl hagF hbF
    rw [e3, e2, e1] at h
    exact FrameComparison.holeSaving_of_working ℓ cE t hA hLu hB hW hodd ha hcE _ _ _ _
      (Finset.card_image_of_injective _ (FrameComparison.cellsOfSites_injective ℓ t)) V W Wl b h
  · intro t n _ hn V W Wl b hcold hleast hbases
    classical
    obtain ⟨w1, -, -, -, -, -, -, w8, -, -, w11, -⟩ :=
      hW ℓ.side hodd n (torusFrame ℓ.side t n) rfl (fun _ => rfl)
    have hbF : IsBaseChoice ℓ.baseDepth (hotLumps ℓ.grid ℓ.threshold
        (cutBelow (torusFrame ℓ.side t n).depth (torusCells (torusFrame ℓ.side t n)))
        (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth W))
        (transferBases (F := stepBlockFrame ℓ.side n) (torusFrame ℓ.side t n) b) := by
      rw [← w8, ← w1]
      exact FrameComparison.isBaseChoice_transferBases ℓ t hLu hB _ W b hbases
    have h := hS.cold (torusFrame ℓ.side t n) rfl ⟨fun _ => rfl, hn⟩
      (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V)
      (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth W)
      (transferBases (F := stepBlockFrame ℓ.side n) (torusFrame ℓ.side t n) b)
      (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth Wl) ((w11 _ V).2 hcold)
      (by rw [← w8]; exact hleast) hbF
    rw [← w8] at h
    exact FrameComparison.holeSaving_of_working ℓ cE t hA hLu hB hW hodd ha hcE _ _ ∅ 0 rfl V W Wl b h
end YangMills.Construction.HoleOnTori
end
