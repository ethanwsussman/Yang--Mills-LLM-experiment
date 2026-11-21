import YangMills.Construction.ClusterExpansionOfAStep.AttachedSetOfFarSets
import YangMills.Construction.ClusterExpansionOfAStep.CountFloorCanBeMet
import YangMills.Construction.ClusterExpansionOfAStep.TestOfAFamily
import YangMills.Construction.ClusterExpansionOfAStep.ZonesOfAFamily
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
namespace FamilyRecovery
variable {R : StepSettings.StepSetup} {n : ℕ} [NeZero n]
theorem coarseStateOf_eq_state_of_isColdCase {G : StepGas.GasGround R n} (hcold : G.IsColdCase)
    (W : TorusFields.TorusField (n * R.params.side)) (Y : Finset (TorusFields.TorusSite (n * R.params.side)))
    (ω : Y → R.labels.Ω) (bad : Finset (TorusFields.TorusBond (n * R.params.side)))
    (b : StepCosts.BaseChoice R.params.side n) :
    StepSettings.coarseStateOf R G.cut W Y ω bad b = G.state := by
  classical
  have hattached : TorusLumps.attachedSites R.params.side R.range bad Y G.cut = ∅ := by
    unfold TorusLumps.attachedSites
    rw [hcold.cut_eq]
    simp [TorusLumps.sitesInBlocks]
  have hstored : TorusLumps.storedBlocks R.params.side R.range bad Y G.cut = ∅ := by
    unfold TorusLumps.storedBlocks TorusLumps.coreBlocks
    rw [hattached, hcold.cut_eq]
    simp [TorusLumps.thickening]
  have hhull : TorusLumps.coarseHull R.params.side R.range R.nextRange bad Y G.cut = ∅ := by
    unfold TorusLumps.coarseHull
    rw [hstored]
    simp [TorusLumps.thickening]
  have hstate : G.state = ⟨G.state.1, G.state.2⟩ := rfl
  rw [hstate]
  unfold StepSettings.coarseStateOf
  refine FamilyZones.coarseState_ext (hhull.trans hcold.state_empty.symm) fun y hy hy' => ?_
  rw [hhull] at hy
  simp at hy
section Hot
variable {G : StepGas.GasGround R n} {Γ : Finset G.GasSpin} {Z : Finset (TorusFields.TorusSite n)}
open Classical in
theorem not_mem_core_of_mem_zone (hZ : BlockZones.IsRetainedZone G Z) (hfar : 64 * R.params.side ≤ R.range)
    {y : TorusFields.TorusSite n} (hy : y ∈ Z) (i : Γ) : y ∉ i.1.1.core :=
  fun h => FamilyZones.not_mem_zone_of_mem_core hZ hfar i.1 h hy
theorem parentBlock_mem_core_of_mem_sites (i : G.GasSpin) {z : TorusFields.TorusSite (n * R.params.side)}
    (hz : z ∈ i.1.sites) : TorusLumps.parentBlock R.params.side z ∈ i.1.core :=
  BlockZones.parentBlock_mem_coreBlocks_of_near hz (by rw [TorusFields.supDist_self]; omega)
end Hot
end FamilyRecovery
open FamilyRecovery in
theorem familyRecoversState_of_farSets_of_floor (hA : AttachedUnchangedByFarSets)
    (hfloor : TorusLumps.CouplingFloorExists) : FamilyRecoversState := by
  classical
  intro T hT
  obtain ⟨y₁, hfloor⟩ := hfloor 1 (64 * T.side) T.rt one_pos
  refine ⟨max y₁ T.floorMin, fun y hy R hR hx' n _ G hG Γ hΓ c hall η hin ν hν => ?_⟩
  have hy₁ : y₁ ≤ y := le_trans (by simp) hy
  have hy₀ : T.floorMin ≤ y := le_trans (by simp) hy
  have hadm : R.params.Admissible := by rw [hR.params_eq]; exact hT.fits y hy₀
  have hside : R.params.side = T.side := by rw [hR.params_eq]; rfl
  have hfar : 64 * R.params.side ≤ R.range := by
    have := (hfloor R.coupling (hy₁.trans hR.le_coupling)).1
    rw [hside]
    exact this
  have hside_pos : 1 ≤ R.params.side := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hdisj := SpinFamilies.coresDisjoint_familyData hΓ (by omega) c
  rcases hG with hcold | hhot
  · exact coarseStateOf_eq_state_of_isColdCase hcold _ _ _ _ _
  · obtain ⟨W₀, Y₀, ω₀, bad₀, b₀, hq, -, hall₀, hbad, hsites, hZ, hrec⟩ := FamilyZones.exists_hot_data hhot
    refine Eq.trans ?_ hq
    have hanchor : G.anchorSites = TorusLumps.attachedSites R.params.side R.range bad₀ Y₀ G.cut := by
      rw [BlockZones.attachedSites_eq_of_subset hall₀]
      unfold StepGas.GasGround.anchorSites
      rw [hbad, hsites]
    have hstored : TorusLumps.storedBlocks R.params.side R.range (G.familyBadBonds Γ) (G.familySites Γ) G.cut =
        TorusLumps.storedBlocks R.params.side R.range bad₀ Y₀ G.cut := by
      have e := hA n R.params.side R.range bad₀ (Γ.biUnion fun i => i.1.1) Y₀ (Γ.biUnion fun i => i.1.2) G.cut hall₀ (by
        intro z hz u hu
        have hzi : ∃ i ∈ Γ, z ∈ i.1.sites := by
          rcases Finset.mem_union.mp hz with a | a
          · obtain ⟨⟨x, k⟩, hb, rfl⟩ := Finset.mem_image.mp a
            obtain ⟨i, hi, hbi⟩ := Finset.mem_biUnion.mp hb
            exact ⟨i, hi, Finset.mem_union_left _ (Finset.mem_image_of_mem _ hbi)⟩
          · obtain ⟨i, hi, hzi⟩ := Finset.mem_biUnion.mp a
            exact ⟨i, hi, Finset.mem_union_right _ hzi⟩
        obtain ⟨i, hi, hzi⟩ := hzi
        refine i.2.far_from_anchor z hzi u ?_
        rw [hanchor, BlockZones.attachedSites_eq_of_subset hall₀]
        rcases Finset.mem_union.mp hu with a | a
        · rcases Finset.mem_union.mp a with b | b
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ b)
          · exact Finset.mem_union_right _ b
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ a))
      unfold TorusLumps.storedBlocks
      have e2 : TorusLumps.attachedSites R.params.side R.range (G.familyBadBonds Γ) (G.familySites Γ) G.cut =
          TorusLumps.attachedSites R.params.side R.range bad₀ Y₀ G.cut := by
        unfold StepGas.GasGround.familyBadBonds StepGas.GasGround.familySites
        rw [hbad, hsites, e, BlockZones.attachedSites_eq_of_subset hall₀]
        ext z
        simp only [Finset.mem_union]
        tauto
      rw [e2]
    refine FamilyZones.coarseStateOf_congr hstored fun y hy => ?_
    rw [hstored] at hy ⊢
    have hnc : ∀ i : Γ, y ∉ i.1.1.core := fun i => not_mem_core_of_mem_zone hZ hfar hy i
    have hp0 : ∀ k, (TorusLumps.stepBlockFrame R.params.side n).period 0 k = n * R.params.side :=
      fun k => BlockTrees.stepBlockFrame_period_zero k
    have hp1 : ∀ k, (TorusLumps.stepBlockFrame R.params.side n).period 1 k = n :=
      fun k => BlockTrees.stepBlockFrame_period_one k
    refine FamilyZones.blockConfig_ext rfl ?_ ?_ ?_ ?_
    · funext q
      show decide ((StepSettings.blockSite y q.1, q.2) ∈ G.familyBadBonds Γ) =
        decide ((StepSettings.blockSite y q.1, q.2) ∈ bad₀)
      refine decide_eq_decide.mpr ⟨fun h => ?_, fun h => Finset.mem_union_left _ (hbad ▸ h)⟩
      rcases Finset.mem_union.mp h with a | a
      · exact hbad ▸ a
      · exfalso
        obtain ⟨i, hi, hbi⟩ := Finset.mem_biUnion.mp a
        have hb := parentBlock_mem_core_of_mem_sites i (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hbi))
        rw [show ((StepSettings.blockSite y q.1, q.2) : TorusFields.TorusBond (n * R.params.side)).1 =
          StepSettings.blockSite y q.1 from rfl, BlockPlaces.parentBlock_blockSite] at hb
        exact hnc ⟨i, hi⟩ hb
    · funext o
      have hbz : TorusLumps.parentBlock R.params.side (StepSettings.blockSite y o) = y :=
        BlockPlaces.parentBlock_blockSite _ _
      have hiff : StepSettings.blockSite y o ∈ G.familySites Γ ↔ StepSettings.blockSite y o ∈ Y₀ := by
        constructor
        · intro h
          rcases Finset.mem_union.mp h with a | a
          · exact hsites ▸ a
          · exfalso
            obtain ⟨i, hi, hzi⟩ := Finset.mem_biUnion.mp a
            have hb := parentBlock_mem_core_of_mem_sites i (Finset.mem_union_right _ hzi)
            rw [hbz] at hb
            exact hnc ⟨i, hi⟩ hb
        · exact fun h => Finset.mem_union_left _ (hsites ▸ h)
      show (if h : StepSettings.blockSite y o ∈ G.familySites Γ then
          Sum.inr (G.state.fillLabels _ ν ⟨_, h⟩) else Sum.inl ()) =
        if h : StepSettings.blockSite y o ∈ Y₀ then Sum.inr (ω₀ ⟨_, h⟩) else Sum.inl ()
      by_cases hz : StepSettings.blockSite y o ∈ Y₀
      · rw [dif_pos (hiff.mpr hz), dif_pos hz]
        congr 1
        have hl : G.state.labelAt (StepSettings.blockSite y o) = Sum.inr (ω₀ ⟨_, hz⟩) := by
          unfold StepSettings.CoarseState.labelAt
          rw [hrec, hbz, if_pos hy]
          simp only [StepSettings.blockConfigAt, FamilyZones.siteOffset_blockSite]
          rw [dif_pos hz]
        exact FamilyZones.fillLabels_of_labelled ν _ hl
      · rw [dif_neg (fun h => hz (hiff.mp h)), dif_neg hz]
    · have hon : TorusLumps.toTorusSite (F := TorusLumps.stepBlockFrame R.params.side n) (j := 1) n
          (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame R.params.side n) 1 y) = y :=
        TopLevelSites.toTorusSite_torusSiteInFrame hp1 y
      have hbase : (G.familySetting c).bases
          (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame R.params.side n) 1 y) =
          StepGas.frameBlockSite R.params.side n y (StepSettings.baseOffset R b₀ y) := by
        rw [SpinFamilies.bases_familySetting hdisj]
        unfold StepGas.GasGround.basesOfOffsets
        rw [dif_neg]
        · unfold StepGas.GasGround.groundBases
          rw [hon, hrec, if_pos hy]
          rfl
        · rintro ⟨i, hi⟩
          exact hnc i (hon ▸ hi)
      show StepSettings.siteOffset (TorusLumps.toTorusSite (n * R.params.side) ((G.familySetting c).bases
        (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame R.params.side n) 1 y))) = _
      rw [hbase]
      unfold StepGas.frameBlockSite
      rw [TopLevelSites.toTorusSite_torusSiteInFrame hp0, FamilyZones.siteOffset_blockSite]
      rfl
    · funext q
      have hbx : TorusLumps.parentBlock R.params.side (StepSettings.blockSite (L := R.params.side) y q.1) = y :=
        BlockPlaces.parentBlock_blockSite _ _
      show (if TorusLumps.parentBlock R.params.side (StepSettings.blockSite (L := R.params.side) y q.1 +
            TorusFields.unitStep (n * R.params.side) q.2) ∈ _ then
          Sum.inr ((G.familySetting c).field η (StepSettings.blockSite y q.1) q.2) else Sum.inl ()) =
        if TorusLumps.parentBlock R.params.side (StepSettings.blockSite (L := R.params.side) y q.1 +
            TorusFields.unitStep (n * R.params.side) q.2) ∈ _ then
          Sum.inr (W₀ (StepSettings.blockSite y q.1) q.2) else Sum.inl ()
      by_cases hcond : TorusLumps.parentBlock R.params.side (StepSettings.blockSite (L := R.params.side) y q.1 +
          TorusFields.unitStep (n * R.params.side) q.2) ∈ TorusLumps.storedBlocks R.params.side R.range bad₀ Y₀ G.cut
      · rw [if_pos hcond, if_pos hcond]
        congr 1
        have hst : G.IsRecorded (StepSettings.blockSite y q.1, q.2) :=
          (hZ.bond_iff _).mpr ⟨by simpa only [hbx] using hy, hcond⟩
        have hnf : (StepSettings.blockSite y q.1, q.2) ∉ (G.familySetting c).free :=
          fun h => ((FamilyZones.mem_free_familySetting_iff c hdisj).mp h).2.1 hst
        have hj : ∀ j : Γ, (StepSettings.blockSite y q.1, q.2) ∉ j.1.1.coreBonds := fun j h =>
          FamilyZones.not_isRecorded_of_mem_coreBonds hZ hfar h hst
        have e1 : (G.familySetting c).field η (StepSettings.blockSite y q.1) q.2 =
            (G.familySetting c).fine (StepSettings.blockSite y q.1) q.2 := by
          unfold StepSettings.ChartSetting.field
          exact dif_neg hnf
        rw [e1, FamilyZones.fine_familySetting_eq_ground c hnf hj]
        unfold StepSettings.CoarseState.fieldWithStoredLinks
        rw [hrec, hbx, if_pos hy]
        simp only [StepSettings.blockConfigAt, FamilyZones.siteOffset_blockSite]
        rw [if_pos hcond]
      · rw [if_neg hcond, if_neg hcond]
end YangMills.Construction.ClusterExpansionOfAStep
end
