import YangMills.Construction.ClusterExpansionOfAStep.HotGroundIsOfItsStateProof
import YangMills.Construction.ClusterExpansionOfAStep.SettingsOfAgreeingGrounds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages TorusFields TorusLumps StepGas StepSettings StepCosts
namespace GroundSettings
section Places
variable {L n : ℕ} [NeZero L] [NeZero n]
theorem siteOffset_fineSite (Y : TorusSite n) (h o : Fin 4 → ℤ) :
    siteOffset (fineSite L Y h o : TorusSite (n * L)) =
      fun i => Fin.ofNat L (((o i + ((L : ℤ) - 1) / 2) % (L : ℤ)).toNat) := by apply _root_.YangMills.Construction.BoxAgreement.siteOffset_fineSite <;> assumption
end Places
section Main
variable {R : StepSetup} {n n' : ℕ} [NeZero n] [NeZero n']
theorem fieldAt_empty (b : TorusBond (n * R.params.side)) :
    (GasFamily.empty : GasFamily R n).fieldAt b = Sum.inl () := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.fieldAt_empty <;> assumption
theorem baseAt_empty (y : TorusSite n) : (GasFamily.empty : GasFamily R n).baseAt y = Sum.inl () := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.baseAt_empty <;> assumption
theorem sites_empty : (GasFamily.empty : GasFamily R n).sites = ∅ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.sites_empty <;> assumption
theorem mem_free_iff (G : GasGround R n) (b : TorusBond (n * R.params.side)) :
    b ∈ G.groundSetting.free ↔ b ∈ markedBonds R G.cut ∧ ¬ G.IsRecorded b := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HotGround.mem_free_iff <;> assumption
theorem mem_support_iff (G : GasGround R n) (z : TorusSite (n * R.params.side)) :
    z ∈ G.groundSetting.support ↔ (G.state.labelAt z).isRight = true := by
  classical
  show z ∈ G.recordedSites ∪ GasFamily.empty.sites ↔ _
  rw [sites_empty, Finset.union_empty]
  unfold GasGround.recordedSites
  simp
theorem labelAt_eq_labelling (G : GasGround R n) (z : TorusSite (n * R.params.side))
    (hz : z ∈ G.groundSetting.support) :
    G.state.labelAt z = Sum.inr (G.groundSetting.labelling ⟨z, hz⟩) := by apply _root_.YangMills.Construction.StepGas.labelAt_of_mem_groundSetting_support <;> assumption
theorem fine_of_not_mem_free (G : GasGround R n) (_hL : Odd R.params.side)
    {b : TorusBond (n * R.params.side)} (hb : b ∉ G.groundSetting.free) :
    G.groundSetting.fine b.1 b.2 = G.state.fieldWithStoredLinks (trivialField _) b.1 b.2 := by
  have h1 : (G.settingWithFamily GasFamily.empty).field 0 b.1 b.2 =
      (G.settingWithFamily GasFamily.empty).fine b.1 b.2 :=
    BlockZones.field_of_not_mem_free (s := G.settingWithFamily GasFamily.empty) (η := 0) hb
  have h2 : (G.settingWithFamily GasFamily.empty).fine b.1 b.2 =
      G.state.fieldWithStoredLinks (trivialField _) b.1 b.2 := by
    show (match (GasFamily.empty : GasFamily R n).fieldAt (b.1, b.2) with
      | Sum.inr g => g
      | Sum.inl _ => G.state.fieldWithStoredLinks (trivialField _) b.1 b.2) = _
    rw [fieldAt_empty]
  exact h1.trans h2
theorem bases_eq_groundBases (G : GasGround R n) (c : (stepBlockFrame R.params.side n).Cell) :
    G.groundSetting.bases c = G.groundBases c := by
  show (match (GasFamily.empty : GasFamily R n).baseAt
      (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) with
    | Sum.inr o => _
    | Sum.inl _ => G.groundBases c) = _
  rw [baseAt_empty]
theorem mem_chartBonds_fineSite_iff (hodd : Odd R.params.side) (hn : 2 ≤ n) (hn' : 2 ≤ n')
    (Y : TorusSite n) (Y' : TorusSite n')
    (h o : Fin 4 → ℤ) (ho : o ∈ centredCube R.params.side) (i : Fin 4) :
    ((fineSite R.params.side Y h o, i) : TorusBond (n * R.params.side)) ∈ chartBonds R.params.side n ↔
      ((fineSite R.params.side Y' h o, i) : TorusBond (n' * R.params.side)) ∈
        chartBonds R.params.side n' := by apply _root_.YangMills.Construction.BoxAgreement.fineSite_mem_chartBonds_iff <;> assumption
theorem blockSite_eq_fineSite (hodd : Odd R.params.side) (Y : TorusSite n) (h : Fin 4 → ℤ)
    (b : BlockOffset R.params.side) :
    ∃ o ∈ centredCube R.params.side, blockSite (Y + siteOfInt h) b = fineSite R.params.side Y h o ∧
      ∀ {k : ℕ} [NeZero k] (Z : TorusSite k) (h' : Fin 4 → ℤ),
        blockSite (Z + siteOfInt h') b = fineSite R.params.side Z h' o := by apply _root_.YangMills.Construction.BoxAgreement.exists_blockSite_eq_fineSite <;> assumption
theorem toTorusSite_cellCentre (Y : TorusSite n) (h : Fin 4 → ℤ) :
    toTorusSite (n * R.params.side) (cellCentre (F := stepBlockFrame R.params.side n) 0
      (torusSiteInFrame (stepBlockFrame R.params.side n) 1 (Y + siteOfInt h))) =
      fineSite R.params.side Y h 0 := by apply _root_.YangMills.Construction.BoxAgreement.toTorusSite_cellCentre <;> assumption
end Main
end GroundSettings
open GroundSettings in
theorem StepSettings.settingsAgreeOfGroundsAgree_holds : StepSettings.SettingsAgreeOfGroundsAgree := by
  classical
  intro R n n' _ _ G G' Y Y' m hodd hn hn' hag
  have hplace : ∀ h o, siteOffset (fineSite R.params.side Y h o : TorusSite (n * R.params.side)) =
      siteOffset (fineSite R.params.side Y' h o : TorusSite (n' * R.params.side)) := by
    intro h o
    rw [siteOffset_fineSite, siteOffset_fineSite]
  have hblock : ∀ h o, o ∈ centredCube R.params.side →
      parentBlock R.params.side (fineSite R.params.side Y h o : TorusSite (n * R.params.side)) =
        Y + siteOfInt h :=
    fun h o ho => BlockOffsets.parentBlock_fineSite hodd Y h o ho
  have hblock' : ∀ h o, o ∈ centredCube R.params.side →
      parentBlock R.params.side (fineSite R.params.side Y' h o : TorusSite (n' * R.params.side)) =
        Y' + siteOfInt h :=
    fun h o ho => BlockOffsets.parentBlock_fineSite hodd Y' h o ho
  have hlabel : ∀ h o, OffsetInBox m h → o ∈ centredCube R.params.side →
      G.state.labelAt (fineSite R.params.side Y h o) = G'.state.labelAt (fineSite R.params.side Y' h o) := by
    intro h o hh ho
    unfold CoarseState.labelAt
    rw [hblock h o ho, hblock' h o ho, hag.marking_eq h hh, hplace]
  have hfree : ∀ (q : NearBondIndex), IsNearIndex R.params.side m q →
      (nearBond R.params.side Y q ∈ G.groundSetting.free ↔
        nearBond R.params.side Y' q ∈ G'.groundSetting.free) := by
    rintro ⟨h, o, i⟩ ⟨hh, ho⟩
    show ((fineSite R.params.side Y h o, i) : TorusBond (n * R.params.side)) ∈ G.groundSetting.free ↔
      ((fineSite R.params.side Y' h o, i) : TorusBond (n' * R.params.side)) ∈ G'.groundSetting.free
    rw [mem_free_iff, mem_free_iff]
    have hm : ((fineSite R.params.side Y h o, i) : TorusBond (n * R.params.side)) ∈ markedBonds R G.cut ↔
        ((fineSite R.params.side Y' h o, i) : TorusBond (n' * R.params.side)) ∈ markedBonds R G'.cut := by
      unfold markedBonds
      simp only [Finset.mem_filter]
      rw [mem_chartBonds_fineSite_iff hodd hn hn' Y Y' h o ho i, hblock h o ho, hblock' h o ho,
        hag.cut_iff h hh]
    have hs : G.IsRecorded ((fineSite R.params.side Y h o, i) : TorusBond (n * R.params.side)) ↔
        G'.IsRecorded ((fineSite R.params.side Y' h o, i) : TorusBond (n' * R.params.side)) := by
      unfold GasGround.IsRecorded
      simp only
      rw [hblock h o ho, hblock' h o ho, hag.marking_eq h hh, hplace]
    rw [hm, hs]
  refine ⟨hag.lt_extent, hag.lt_extent', hag.coarse_agree, hfree, ?_, ?_, ?_, ?_⟩
  · rintro ⟨h, o, i⟩ ⟨hh, ho⟩ hf
    have hf' : nearBond R.params.side Y' (h, o, i) ∉ G'.groundSetting.free :=
      fun h' => hf ((hfree _ ⟨hh, ho⟩).mpr h')
    have e1 := fine_of_not_mem_free G hodd hf
    have e2 := fine_of_not_mem_free G' hodd hf'
    show G.groundSetting.fine (nearBond R.params.side Y (h, o, i)).1 (nearBond R.params.side Y (h, o, i)).2 =
      G'.groundSetting.fine (nearBond R.params.side Y' (h, o, i)).1 (nearBond R.params.side Y' (h, o, i)).2
    rw [e1, e2]
    show G.state.fieldWithStoredLinks (trivialField _) (fineSite R.params.side Y h o) i =
      G'.state.fieldWithStoredLinks (trivialField _) (fineSite R.params.side Y' h o) i
    unfold CoarseState.fieldWithStoredLinks
    rw [hblock h o ho, hblock' h o ho, ← hag.marking_eq h hh, hplace h o]
    cases G.state.markAt (Y + siteOfInt h) with
    | none => rfl
    | some s =>
      cases s.linkValue (siteOffset (fineSite R.params.side Y' h o), i) <;> rfl
  · intro h o hh ho
    rw [mem_support_iff, mem_support_iff, hlabel h o hh ho]
  · intro h o hz hz' hh ho
    have e1 := labelAt_eq_labelling G _ hz
    have e2 := labelAt_eq_labelling G' _ hz'
    rw [hlabel h o hh ho, e2] at e1
    exact (Sum.inr.inj e1).symm
  · intro h hh
    have ec : toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n
        (torusSiteInFrame (stepBlockFrame R.params.side n) 1 (Y + siteOfInt h)) = Y + siteOfInt h :=
      TopLevelSites.toTorusSite_torusSiteInFrame BlockTrees.stepBlockFrame_period_one _
    have ec' : toTorusSite (F := stepBlockFrame R.params.side n') (j := 1) n'
        (torusSiteInFrame (stepBlockFrame R.params.side n') 1 (Y' + siteOfInt h)) = Y' + siteOfInt h :=
      TopLevelSites.toTorusSite_torusSiteInFrame BlockTrees.stepBlockFrame_period_one _
    have hst := hag.marking_eq h hh
    have b1 : G.groundSetting.bases (torusSiteInFrame (stepBlockFrame R.params.side n) 1 (Y + siteOfInt h)) =
        G.groundBases (torusSiteInFrame (stepBlockFrame R.params.side n) 1 (Y + siteOfInt h)) :=
      bases_eq_groundBases G _
    have b2 : G'.groundSetting.bases (torusSiteInFrame (stepBlockFrame R.params.side n') 1 (Y' + siteOfInt h)) =
        G'.groundBases (torusSiteInFrame (stepBlockFrame R.params.side n') 1 (Y' + siteOfInt h)) :=
      bases_eq_groundBases G' _
    rw [b1, b2]
    cases hs : G.state.markAt (Y + siteOfInt h) with
    | none =>
      have hs' : G'.state.markAt (Y' + siteOfInt h) = none := by rw [← hst, hs]
      have h0 : (0 : Fin 4 → ℤ) ∈ centredCube R.params.side := by
        rw [BlockOffsets.mem_centredCube_iff]
        intro i
        have hpos : (1 : ℤ) ≤ R.params.side := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
        have : 0 ≤ ((R.params.side : ℤ) - 1) / 2 := by omega
        simpa using this
      refine ⟨0, h0, ?_, ?_⟩
      · unfold GasGround.groundBases
        simp only [ec, hs]
        exact toTorusSite_cellCentre Y h
      · unfold GasGround.groundBases
        simp only [ec', hs']
        exact toTorusSite_cellCentre Y' h
    | some s =>
      have hs' : G'.state.markAt (Y' + siteOfInt h) = some s := by rw [← hst, hs]
      obtain ⟨o, ho, e1, e2⟩ := blockSite_eq_fineSite hodd Y h s.basePoint
      refine ⟨o, ho, ?_, ?_⟩
      · unfold GasGround.groundBases
        simp only [ec, hs, frameBlockSite]
        rw [TopLevelSites.toTorusSite_torusSiteInFrame BlockTrees.stepBlockFrame_period_zero]
        exact e1
      · unfold GasGround.groundBases
        simp only [ec', hs', frameBlockSite]
        rw [TopLevelSites.toTorusSite_torusSiteInFrame BlockTrees.stepBlockFrame_period_zero]
        exact e2 Y' h
end YangMills.Construction
end
