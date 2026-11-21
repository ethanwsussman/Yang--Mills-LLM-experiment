import YangMills.Construction.ClusterExpansionOfAStep.ClassesOfTheGas
import YangMills.Construction.ClusterExpansionOfAStep.LocalityOfTheDensities
import YangMills.Construction.ClusterExpansionOfAStep.ShiftsOfTwoSettings
import YangMills.Construction.ClusterExpansionOfAStep.ZonesOfAGround
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
open TorusFields TorusLumps StepGas StepSettings StepCosts BlockOffsets BlockAverages BlockTrees TopLevelSites
  SettingShifts BlockZones
namespace BoxAgreement
section EvaluationMaps
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem fieldAt_eq_of_mem_coreBonds {γ : GasFamily R n} (hs : γ.CoresDisjoint) {θ : GasSupport R n}
    (h : γ.Occupies θ) {b : TorusBond (n * R.params.side)} (hb : b ∈ θ.coreBonds) :
    γ.fieldAt b = Sum.inr ((γ.state h).1 ⟨b, hb⟩) := by
  classical
  have hex : ∃ θ, γ.Occupies θ ∧ b ∈ θ.coreBonds := ⟨θ, h, hb⟩
  unfold GasFamily.fieldAt
  rw [dif_pos hex]
  have e : hex.choose = θ :=
    hs _ _ hex.choose_spec.1 h _ (GasSupport.parentBlock_mem_core_of_mem_coreBonds hex.choose_spec.2)
      (GasSupport.parentBlock_mem_core_of_mem_coreBonds hb)
  exact congrArg Sum.inr (GasFamily.state_link_congr γ e _ h _ hb)
theorem fieldAt_eq_inl_of_forall_not_mem {γ : GasFamily R n} {b : TorusBond (n * R.params.side)}
    (h : ∀ θ, γ.Occupies θ → b ∉ θ.coreBonds) : γ.fieldAt b = Sum.inl () := by
  classical
  unfold GasFamily.fieldAt
  rw [dif_neg]
  rintro ⟨θ, h1, h2⟩
  exact h θ h1 h2
theorem baseAt_eq_of_mem_core {γ : GasFamily R n} (hs : γ.CoresDisjoint) {θ : GasSupport R n}
    (h : γ.Occupies θ) {y : TorusSite n} (hy : y ∈ θ.core) :
    γ.baseAt y = Sum.inr ((γ.state h).2.2 ⟨y, hy⟩) := by
  classical
  have hex : ∃ θ, γ.Occupies θ ∧ y ∈ θ.core := ⟨θ, h, hy⟩
  unfold GasFamily.baseAt
  rw [dif_pos hex]
  have e : hex.choose = θ := hs _ _ hex.choose_spec.1 h _ hex.choose_spec.2 hy
  exact congrArg Sum.inr (GasFamily.state_base_congr γ e _ h _ hy)
theorem baseAt_eq_inl_of_forall_not_mem {γ : GasFamily R n} {y : TorusSite n}
    (h : ∀ θ, γ.Occupies θ → y ∉ θ.core) : γ.baseAt y = Sum.inl () := by
  classical
  unfold GasFamily.baseAt
  rw [dif_neg]
  rintro ⟨θ, h1, h2⟩
  exact h θ h1 h2
theorem mem_settingOf_free_iff (G : GasGround R n) (γ : GasFamily R n) (b : TorusBond (n * R.params.side)) :
    b ∈ (G.settingOf γ).free ↔
      (b ∈ markedBonds R G.cut ∧ ¬ G.IsRecorded b) ∧ γ.fieldAt b = Sum.inl () := by
  classical
  show b ∈ G.freeBonds.filter (fun b => γ.fieldAt b = Sum.inl ()) ↔ _
  simp only [GasGround.freeBonds, Finset.mem_filter]
theorem mem_settingOf_support_iff (G : GasGround R n) (γ : GasFamily R n) (z : TorusSite (n * R.params.side)) :
    z ∈ (G.settingOf γ).support ↔ (G.state.labelAt z).isRight = true ∨ z ∈ γ.sites := by
  classical
  show z ∈ G.recordedSites ∪ γ.sites ↔ _
  unfold GasGround.recordedSites
  simp
theorem settingOf_labelling_of_mem_sites (G : GasGround R n) (γ : GasFamily R n)
    {z : TorusSite (n * R.params.side)} (hz : z ∈ (G.settingOf γ).support)
    (hs : z ∈ γ.sites) : (G.settingOf γ).labelling ⟨z, hz⟩ = γ.labelAt hs := by
  classical
  show dite (z ∈ γ.sites) _ _ = _
  rw [dif_pos hs]
theorem labelAt_eq_settingOf_labelling (G : GasGround R n) (γ : GasFamily R n)
    {z : TorusSite (n * R.params.side)} (hz : z ∈ (G.settingOf γ).support)
    (hs : z ∉ γ.sites) : G.state.labelAt z = Sum.inr ((G.settingOf γ).labelling ⟨z, hz⟩) := by
  classical
  show G.state.labelAt z = Sum.inr (dite (z ∈ γ.sites) _ _)
  rw [dif_neg hs]
  exact (Sum.inr_getRight _ _).symm
theorem settingOf_fine_of_not_mem_free (G : GasGround R n) (γ : GasFamily R n)
    {b : TorusBond (n * R.params.side)} (hb : b ∉ (G.settingOf γ).free) :
    (G.settingOf γ).fine b.1 b.2 = match γ.fieldAt b with
      | Sum.inr g => g
      | Sum.inl _ => G.state.fieldWithStoredLinks (trivialField _) b.1 b.2 :=
  field_of_not_mem_free (s := G.settingWithFamily γ) (η := 0) hb
theorem settingOf_bases_torusSiteInFrame (G : GasGround R n) (γ : GasFamily R n) (y : TorusSite n) :
    (G.settingOf γ).bases (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y) = match γ.baseAt y with
      | Sum.inr o => frameBlockSite R.params.side n y o
      | Sum.inl _ => G.groundBases (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y) := by
  have ec : toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n
      (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y) = y :=
    toTorusSite_torusSiteInFrame stepBlockFrame_period_one _
  show (match γ.baseAt (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n
        (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y)) with
      | Sum.inr o => frameBlockSite R.params.side n (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n
        (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y)) o
      | Sum.inl _ => G.groundBases (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y)) = _
  rw [ec]
end EvaluationMaps
section Places
variable {L n : ℕ} [NeZero L] [NeZero n]
theorem siteOffset_fineSite (Y : TorusSite n) (h o : Fin 4 → ℤ) :
    siteOffset (fineSite L Y h o : TorusSite (n * L)) =
      fun i => Fin.ofNat L (((o i + ((L : ℤ) - 1) / 2) % (L : ℤ)).toNat) := by
  have : NeZero (n * L) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
  funext i
  simp only [siteOffset]
  congr 2
  set a : ℤ := (L : ℤ) * (((Y i).cast : ℤ) + h i) + o i with ha
  have hc : (((fineSite L Y h o : TorusSite (n * L)) i).cast : ℤ) = a % ((n * L : ℕ) : ℤ) := by
    simp only [fineSite, siteOfInt]
    exact ZMod.coe_intCast _
  have hd : (L : ℤ) ∣ ((n * L : ℕ) : ℤ) := ⟨n, by push_cast; ring⟩
  rw [hc, Int.add_emod, Int.emod_emod_of_dvd a hd, ← Int.add_emod, ha]
  have e : (L : ℤ) * (((Y i).cast : ℤ) + h i) + o i + ((L : ℤ) - 1) / 2 =
      (o i + ((L : ℤ) - 1) / 2) + (L : ℤ) * (((Y i).cast : ℤ) + h i) := by ring
  rw [e, Int.add_mul_emod_self_left]
theorem isAxialTreeBond_blockPoint_iff (hodd : Odd L) (hn : 2 ≤ n) (A o : Fin 4 → ℤ) (ho : o ∈ centredCube L)
    (i : Fin 4) :
    IsAxialTreeBond (F := stepBlockFrame L n) (siteOfCoords 0 (blockPoint L A o), i) ↔
      o + Pi.single i 1 ∈ centredCube L ∧ ∀ l, i < l → o l = 0 := by
  have hf := cellOffset_blockPoint (n := n) hodd A o ho
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun l hl => ?_⟩
    · by_contra hc
      exact h1 ((isCrossingBond_blockPoint_iff hodd hn A o ho i).mpr hc)
    · have := h2 l hl
      change cellOffset (F := stepBlockFrame L n) (siteOfCoords 0 (blockPoint L A o)) l = 0 at this
      rwa [hf] at this
  · rintro ⟨h1, h2⟩
    exact isAxialTreeBond_blockPoint hodd hn A o ho i h1 h2
end Places
section TwoGrounds
variable {R : StepSetup} {n n' : ℕ} [NeZero n] [NeZero n']
theorem fineSite_mem_chartBonds_iff (hodd : Odd R.params.side) (hn : 2 ≤ n) (hn' : 2 ≤ n') (Y : TorusSite n)
    (Y' : TorusSite n') (h o : Fin 4 → ℤ) (ho : o ∈ centredCube R.params.side) (i : Fin 4) :
    ((fineSite R.params.side Y h o, i) : TorusBond (n * R.params.side)) ∈ chartBonds R.params.side n ↔
      ((fineSite R.params.side Y' h o, i) : TorusBond (n' * R.params.side)) ∈ chartBonds R.params.side n' := by
  classical
  unfold chartBonds
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have e : ∀ {k : ℕ} [NeZero k] (Z : TorusSite k),
      torusSiteInFrame (stepBlockFrame R.params.side k) 0 (fineSite R.params.side Z h o) =
      siteOfCoords 0 (blockPoint R.params.side (fun i => ((Z i).cast : ℤ) + h i) o) := by
    intro k _ Z
    exact BlockOffsets.torusSiteInFrame_siteOfInt _
  rw [e, e, isAxialTreeBond_blockPoint_iff (L := R.params.side) hodd hn _ o ho,
    isAxialTreeBond_blockPoint_iff (L := R.params.side) hodd hn' _ o ho]
theorem exists_blockSite_eq_fineSite (hodd : Odd R.params.side) (Y : TorusSite n) (h : Fin 4 → ℤ)
    (b : BlockOffset R.params.side) :
    ∃ o ∈ centredCube R.params.side, StepSettings.blockSite (Y + siteOfInt h) b = fineSite R.params.side Y h o ∧
      ∀ {k : ℕ} [NeZero k] (Z : TorusSite k) (h' : Fin 4 → ℤ),
        StepSettings.blockSite (Z + siteOfInt h') b = fineSite R.params.side Z h' o := by
  obtain ⟨H, hH⟩ := hodd
  have hL : ((R.params.side : ℤ) - 1) / 2 = (H : ℤ) := by
    rw [hH]
    push_cast
    omega
  have key : ∀ {k : ℕ} [NeZero k] (Z : TorusSite k) (h' : Fin 4 → ℤ),
      StepSettings.blockSite (Z + siteOfInt h') b =
        fineSite R.params.side Z h' (fun i => ((b i : ℕ) : ℤ) - (H : ℤ)) := by
    intro k _ Z h'
    rw [fineSite_eq_add_siteOfInt]
    funext i
    simp only [StepSettings.blockSite, fineSite, siteOfInt, hL, Pi.zero_apply]
    push_cast
    ring_nf
  refine ⟨fun i => ((b i : ℕ) : ℤ) - (H : ℤ), ?_, key Y h, fun Z h' => key Z h'⟩
  rw [BlockOffsets.mem_centredCube_iff, hL]
  intro i
  have h2 := (b i).isLt
  omega
theorem toTorusSite_cellCentre (Y : TorusSite n) (h : Fin 4 → ℤ) :
    toTorusSite (n * R.params.side) (cellCentre (F := stepBlockFrame R.params.side n) 0
      (torusSiteInFrame (stepBlockFrame R.params.side n) 1 (Y + siteOfInt h))) =
      fineSite R.params.side Y h 0 := by
  rw [fineSite_eq_add_siteOfInt]
  set y := Y + siteOfInt h with hy
  have e1 : cellCentre (F := stepBlockFrame R.params.side n) 0 (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y) =
      torusSiteInFrame (stepBlockFrame R.params.side n) 0 (fineSite R.params.side y 0 0) := by
    have e0 : (fineSite R.params.side y 0 0 : TorusSite (n * R.params.side)) =
        siteOfInt (blockPoint R.params.side (fun i => ((y i).cast : ℤ) + (0 : Fin 4 → ℤ) i) 0) := rfl
    rw [e0, BlockOffsets.torusSiteInFrame_siteOfInt]
    unfold cellCentre
    congr 1
    funext i
    have hc : siteCoords (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y :
        (stepBlockFrame R.params.side n).Site 1) i = ((y i).cast : ℤ) :=
      cast_intCast_cast (stepBlockFrame_period_one i) (y i)
    have hp : ((stepBlockFrame R.params.side n).blockSide : ℤ) ^ ((stepBlockFrame R.params.side n).top - 0) =
        (R.params.side : ℤ) := by
      simp [stepBlockFrame, BlockFrame.top]
    show ((stepBlockFrame R.params.side n).blockSide : ℤ) ^ ((stepBlockFrame R.params.side n).top - 0) *
      siteCoords (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y : (stepBlockFrame R.params.side n).Site 1) i = _
    rw [hp, hc]
    simp [blockPoint]
  rw [e1]
  exact toTorusSite_torusSiteInFrame stepBlockFrame_period_zero _
structure FamiliesMatchNear (γ : GasFamily R n) (γ' : GasFamily R n') (Y : TorusSite n) (Y' : TorusSite n')
    (m : ℕ) : Prop where
  fieldAt_eq : ∀ q, IsNearIndex R.params.side m q →
    γ.fieldAt (nearBond R.params.side Y q) = γ'.fieldAt (nearBond R.params.side Y' q)
  mem_sites_iff : ∀ h o, OffsetInBox m h → o ∈ centredCube R.params.side →
    (fineSite R.params.side Y h o ∈ γ.sites ↔ fineSite R.params.side Y' h o ∈ γ'.sites)
  labelAt_eq : ∀ h o (hz : fineSite R.params.side Y h o ∈ γ.sites) (hz' : fineSite R.params.side Y' h o ∈ γ'.sites),
    OffsetInBox m h → o ∈ centredCube R.params.side → γ.labelAt hz = γ'.labelAt hz'
  baseAt_eq : ∀ h, OffsetInBox m h → γ.baseAt (Y + siteOfInt h) = γ'.baseAt (Y' + siteOfInt h)
theorem settingsAgreeAwayFromFrames_of_match {G : GasGround R n} {G' : GasGround R n'} {γ : GasFamily R n}
    {γ' : GasFamily R n'} {Y : TorusSite n} {Y' : TorusSite n'} {m : ℕ} (hodd : Odd R.params.side) (hn : 2 ≤ n)
    (hn' : 2 ≤ n') (hag : GroundsAgreeNear G G' Y Y' m) (M : FamiliesMatchNear γ γ' Y Y' m) :
    SettingsAgreeAwayFromFrames (G.settingOf γ) (G'.settingOf γ') Y Y' m := by
  classical
  have hplace : ∀ h o, siteOffset (fineSite R.params.side Y h o : TorusSite (n * R.params.side)) =
      siteOffset (fineSite R.params.side Y' h o : TorusSite (n' * R.params.side)) := by
    intro h o
    rw [siteOffset_fineSite, siteOffset_fineSite]
  have hblock : ∀ h o, o ∈ centredCube R.params.side →
      parentBlock R.params.side (fineSite R.params.side Y h o : TorusSite (n * R.params.side)) = Y + siteOfInt h :=
    fun h o ho => parentBlock_fineSite hodd Y h o ho
  have hblock' : ∀ h o, o ∈ centredCube R.params.side →
      parentBlock R.params.side (fineSite R.params.side Y' h o : TorusSite (n' * R.params.side)) =
        Y' + siteOfInt h :=
    fun h o ho => parentBlock_fineSite hodd Y' h o ho
  have hlabel : ∀ h o, OffsetInBox m h → o ∈ centredCube R.params.side →
      G.state.labelAt (fineSite R.params.side Y h o) = G'.state.labelAt (fineSite R.params.side Y' h o) := by
    intro h o hh ho
    unfold CoarseState.labelAt
    rw [hblock h o ho, hblock' h o ho, hag.marking_eq h hh, hplace]
  have hfree : ∀ (q : NearBondIndex), IsNearIndex R.params.side m q →
      (nearBond R.params.side Y q ∈ (G.settingOf γ).free ↔
        nearBond R.params.side Y' q ∈ (G'.settingOf γ').free) := by
    rintro ⟨h, o, i⟩ ⟨hh, ho⟩
    rw [mem_settingOf_free_iff, mem_settingOf_free_iff, M.fieldAt_eq _ ⟨hh, ho⟩]
    show (((fineSite R.params.side Y h o, i) : TorusBond (n * R.params.side)) ∈ markedBonds R G.cut ∧
        ¬ G.IsRecorded ((fineSite R.params.side Y h o, i) : TorusBond (n * R.params.side))) ∧ _ ↔
      (((fineSite R.params.side Y' h o, i) : TorusBond (n' * R.params.side)) ∈ markedBonds R G'.cut ∧
        ¬ G'.IsRecorded ((fineSite R.params.side Y' h o, i) : TorusBond (n' * R.params.side))) ∧ _
    have hm : ((fineSite R.params.side Y h o, i) : TorusBond (n * R.params.side)) ∈ markedBonds R G.cut ↔
        ((fineSite R.params.side Y' h o, i) : TorusBond (n' * R.params.side)) ∈ markedBonds R G'.cut := by
      unfold markedBonds
      simp only [Finset.mem_filter]
      rw [fineSite_mem_chartBonds_iff hodd hn hn' Y Y' h o ho i, hblock h o ho, hblock' h o ho, hag.cut_iff h hh]
    have hs : G.IsRecorded ((fineSite R.params.side Y h o, i) : TorusBond (n * R.params.side)) ↔
        G'.IsRecorded ((fineSite R.params.side Y' h o, i) : TorusBond (n' * R.params.side)) := by
      unfold GasGround.IsRecorded
      simp only
      rw [hblock h o ho, hblock' h o ho, hag.marking_eq h hh, hplace]
    rw [hm, hs]
  refine ⟨hag.lt_extent, hag.lt_extent', hag.coarse_agree, hfree, ?_, ?_, ?_, ?_⟩
  · rintro ⟨h, o, i⟩ ⟨hh, ho⟩ hf
    have hf' : nearBond R.params.side Y' (h, o, i) ∉ (G'.settingOf γ').free :=
      fun h' => hf ((hfree _ ⟨hh, ho⟩).mpr h')
    have e1 := settingOf_fine_of_not_mem_free G γ hf
    have e2 := settingOf_fine_of_not_mem_free G' γ' hf'
    show (G.settingOf γ).fine (nearBond R.params.side Y (h, o, i)).1 (nearBond R.params.side Y (h, o, i)).2 =
      (G'.settingOf γ').fine (nearBond R.params.side Y' (h, o, i)).1 (nearBond R.params.side Y' (h, o, i)).2
    rw [e1, e2, M.fieldAt_eq _ ⟨hh, ho⟩]
    cases γ'.fieldAt (nearBond R.params.side Y' (h, o, i)) with
    | inr g => rfl
    | inl u =>
      show G.state.fieldWithStoredLinks (trivialField _) (fineSite R.params.side Y h o) i =
        G'.state.fieldWithStoredLinks (trivialField _) (fineSite R.params.side Y' h o) i
      unfold CoarseState.fieldWithStoredLinks
      rw [hblock h o ho, hblock' h o ho, ← hag.marking_eq h hh, hplace h o]
      cases G.state.markAt (Y + siteOfInt h) with
      | none => rfl
      | some s =>
        cases s.linkValue (siteOffset (fineSite R.params.side Y' h o), i) <;> rfl
  · intro h o hh ho
    rw [mem_settingOf_support_iff, mem_settingOf_support_iff, hlabel h o hh ho, M.mem_sites_iff h o hh ho]
  · intro h o hz hz' hh ho
    by_cases hs : fineSite R.params.side Y h o ∈ γ.sites
    · have hs' := (M.mem_sites_iff h o hh ho).mp hs
      rw [settingOf_labelling_of_mem_sites G γ hz hs, settingOf_labelling_of_mem_sites G' γ' hz' hs',
        M.labelAt_eq h o hs hs' hh ho]
    · have hs' : fineSite R.params.side Y' h o ∉ γ'.sites := fun c => hs ((M.mem_sites_iff h o hh ho).mpr c)
      have e1 := labelAt_eq_settingOf_labelling G γ hz hs
      have e2 := labelAt_eq_settingOf_labelling G' γ' hz' hs'
      rw [hlabel h o hh ho, e2] at e1
      exact (Sum.inr.inj e1).symm
  · intro h hh
    have ec : toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n
        (torusSiteInFrame (stepBlockFrame R.params.side n) 1 (Y + siteOfInt h)) =
        Y + siteOfInt h := toTorusSite_torusSiteInFrame stepBlockFrame_period_one _
    have ec' : toTorusSite (F := stepBlockFrame R.params.side n') (j := 1) n'
        (torusSiteInFrame (stepBlockFrame R.params.side n') 1 (Y' + siteOfInt h)) =
        Y' + siteOfInt h := toTorusSite_torusSiteInFrame stepBlockFrame_period_one _
    have hst := hag.marking_eq h hh
    rw [settingOf_bases_torusSiteInFrame, settingOf_bases_torusSiteInFrame, ← M.baseAt_eq h hh]
    cases hb : γ.baseAt (Y + siteOfInt h) with
    | inr o₀ =>
      obtain ⟨o, ho, e1, e2⟩ := exists_blockSite_eq_fineSite hodd Y h o₀
      refine ⟨o, ho, ?_, ?_⟩
      · simp only [frameBlockSite]
        rw [toTorusSite_torusSiteInFrame stepBlockFrame_period_zero]
        exact e1
      · simp only [frameBlockSite]
        rw [toTorusSite_torusSiteInFrame stepBlockFrame_period_zero]
        exact e2 Y' h
    | inl u =>
      cases hs : G.state.markAt (Y + siteOfInt h) with
      | none =>
        have hs' : G'.state.markAt (Y' + siteOfInt h) = none := by rw [← hst, hs]
        have h0 : (0 : Fin 4 → ℤ) ∈ centredCube R.params.side := by
          rw [BlockOffsets.mem_centredCube_iff]
          intro i
          have hpos : (1 : ℤ) ≤ R.params.side := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
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
        obtain ⟨o, ho, e1, e2⟩ := exists_blockSite_eq_fineSite hodd Y h s.basePoint
        refine ⟨o, ho, ?_, ?_⟩
        · unfold GasGround.groundBases
          simp only [ec, hs, frameBlockSite]
          rw [toTorusSite_torusSiteInFrame stepBlockFrame_period_zero]
          exact e1
        · unfold GasGround.groundBases
          simp only [ec', hs', frameBlockSite]
          rw [toTorusSite_torusSiteInFrame stepBlockFrame_period_zero]
          exact e2 Y' h
end TwoGrounds
end BoxAgreement
end YangMills.Construction
end
