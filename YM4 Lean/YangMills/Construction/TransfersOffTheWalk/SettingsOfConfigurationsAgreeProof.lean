import YangMills.Construction.ClusterExpansionOfAStep.GasesEqualInBoxes
import YangMills.Construction.ClusterExpansionOfAStep.AllowedStatesReadTheirBoxProof
import YangMills.Construction.ClusterExpansionOfAStep.WeightOfTheGasIsBorelProof
import YangMills.Construction.TransfersOffTheWalk.SettingsOfConfigurationsAgree
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open TorusFields TorusLumps StepSettings StepGas BlockAverages
namespace ConfigurationSettings
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem exists_centredCube_blockSite_eq (hodd : Odd R.params.side) (Y : TorusSite n) (h : Fin 4 → ℤ)
    (b : BlockOffset R.params.side) :
    ∃ o ∈ centredCube R.params.side, blockSite (Y + siteOfInt h) b = fineSite R.params.side Y h o := by
  obtain ⟨H, hH⟩ := hodd
  have hL : ((R.params.side : ℤ) - 1) / 2 = (H : ℤ) := by
    rw [hH]
    push_cast
    omega
  refine ⟨fun i => ((b i : ℕ) : ℤ) - (H : ℤ), ?_, ?_⟩
  · rw [BlockOffsets.mem_centredCube_iff, hL]
    intro i
    have h2 := (b i).isLt
    omega
  · rw [SettingShifts.fineSite_eq_add_siteOfInt]
    funext i
    simp only [blockSite, fineSite, siteOfInt, hL, Pi.zero_apply]
    push_cast
    ring_nf
private theorem toTorusSite_cellCentre_eq_fineSite (Y : TorusSite n) (h : Fin 4 → ℤ) :
    toTorusSite (n * R.params.side) (cellCentre (F := stepBlockFrame R.params.side n) 0
      (StepCosts.torusSiteInFrame (stepBlockFrame R.params.side n) 1 (Y + siteOfInt h))) =
      fineSite R.params.side Y h 0 := by apply _root_.YangMills.Construction.BoxAgreement.toTorusSite_cellCentre <;> assumption
private theorem choose_eq_of_iff {α : Type*} {P Q : α → Prop} (h : ∀ a, P a ↔ Q a) (hp : ∃ a, P a)
    (hq : ∃ a, Q a) : hp.choose = hq.choose := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GasWeight.exists_choose_congr <;> assumption
private theorem getRight_congr_of_eq {α β : Type*} {u v : α ⊕ β} (e : u = v) (h : u.isRight = true)
    (h' : v.isRight = true) : u.getRight h = v.getRight h' := by
  subst e
  rfl
private theorem familyOf_congr (G : GasGround R n) {σ σ' : G.Config} {θ : GasSupport R n}
    (h : ∀ hs : G.IsGasSupport θ, σ ⟨θ, hs⟩ = σ' ⟨θ, hs⟩) : G.familyOf σ θ = G.familyOf σ' θ := by
  classical
  unfold GasGround.familyOf
  by_cases hs : G.IsGasSupport θ
  · rw [dif_pos hs, dif_pos hs, h hs]
  · rw [dif_neg hs, dif_neg hs]
private theorem parentBlock_mem_core (θ : GasSupport R n) {z : TorusSite (n * R.params.side)} (hz : z ∈ θ.2) :
    parentBlock R.params.side z ∈ θ.core := by apply _root_.YangMills.Construction.StepGas.GasSupport.parentBlock_mem_core_of_mem_sites <;> assumption
variable {γ γ' : GasFamily R n}
private theorem occupies_iff_of_eq {θ : GasSupport R n} (h : γ θ = γ' θ) : γ.Occupies θ ↔ γ'.Occupies θ := by apply _root_.YangMills.Construction.InBoxTransfer.occupies_congr <;> assumption
private theorem state_heq {θ θ' : GasSupport R n} (e : θ = θ') (h : γ θ = γ' θ) (h₁ : γ.Occupies θ)
    (h₂ : γ'.Occupies θ') : HEq (γ.state h₁) (γ'.state h₂) := by
  subst e
  exact heq_of_eq (getRight_congr_of_eq h h₁ h₂)
private theorem fieldAt_congr {b : TorusBond (n * R.params.side)}
    (h : ∀ θ : GasSupport R n, b ∈ θ.coreBonds → γ θ = γ' θ) : γ.fieldAt b = γ'.fieldAt b := by apply _root_.YangMills.Construction.InBoxTransfer.fieldAt_congr <;> assumption
private theorem baseAt_congr {y : TorusSite n} (h : ∀ θ : GasSupport R n, y ∈ θ.core → γ θ = γ' θ) :
    γ.baseAt y = γ'.baseAt y := by apply _root_.YangMills.Construction.InBoxTransfer.baseAt_congr <;> assumption
private theorem mem_sites_iff_of_congr {z : TorusSite (n * R.params.side)}
    (h : ∀ θ : GasSupport R n, z ∈ θ.2 → γ θ = γ' θ) : z ∈ γ.sites ↔ z ∈ γ'.sites := by
  classical
  constructor
  · intro hz
    obtain ⟨θ, hθ, hzθ⟩ := GasFamily.exists_of_mem_sites hz
    exact Finset.mem_biUnion.mpr
      ⟨θ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (occupies_iff_of_eq (h θ hzθ)).mp hθ⟩, hzθ⟩
  · intro hz
    obtain ⟨θ, hθ, hzθ⟩ := GasFamily.exists_of_mem_sites hz
    exact Finset.mem_biUnion.mpr
      ⟨θ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (occupies_iff_of_eq (h θ hzθ)).mpr hθ⟩, hzθ⟩
private theorem labelAt_congr {z : TorusSite (n * R.params.side)}
    (h : ∀ θ : GasSupport R n, z ∈ θ.2 → γ θ = γ' θ) (hz : z ∈ γ.sites) (hz' : z ∈ γ'.sites) :
    γ.labelAt hz = γ'.labelAt hz' := by
  classical
  have hiff : ∀ θ, (γ.Occupies θ ∧ z ∈ θ.2) ↔ (γ'.Occupies θ ∧ z ∈ θ.2) := fun θ =>
    ⟨fun a => ⟨(occupies_iff_of_eq (h θ a.2)).mp a.1, a.2⟩,
      fun a => ⟨(occupies_iff_of_eq (h θ a.2)).mpr a.1, a.2⟩⟩
  have hc := choose_eq_of_iff hiff (GasFamily.exists_of_mem_sites hz) (GasFamily.exists_of_mem_sites hz')
  have key : ∀ (θ θ' : GasSupport R n) (e : θ = θ') (h₁ : γ.Occupies θ) (h₂ : γ'.Occupies θ')
      (b₁ : z ∈ θ.2) (b₂ : z ∈ θ'.2), (γ.state h₁).2.1 ⟨z, b₁⟩ = (γ'.state h₂).2.1 ⟨z, b₂⟩ := by
    intro θ θ' e h₁ h₂ b₁ b₂
    subst e
    rw [eq_of_heq (state_heq rfl (h θ b₁) h₁ h₂)]
  exact key _ _ hc _ _ _ _
section NearAgreement
variable (G : GasGround R n) (γ γ' : GasFamily R n) (Y : TorusSite n) (m : ℕ)
private theorem fieldAt_fineSite_congr (hodd : Odd R.params.side)
    (hbox : ∀ (θ : GasSupport R n) (h : Fin 4 → ℤ), OffsetInBox m h → Y + siteOfInt h ∈ θ.core → γ θ = γ' θ)
    (h o : Fin 4 → ℤ) (i : Fin 4) (hh : OffsetInBox m h) (ho : o ∈ centredCube R.params.side) :
    γ.fieldAt (fineSite R.params.side Y h o, i) = γ'.fieldAt (fineSite R.params.side Y h o, i) := by
  refine fieldAt_congr fun θ hb => hbox θ h hh ?_
  have := (Finset.mem_filter.mp hb).2.1
  rwa [BlockOffsets.parentBlock_fineSite hodd Y h o ho] at this
private theorem mem_free_settingOf_iff (b : TorusBond (n * R.params.side)) :
    b ∈ (G.settingOf γ).free ↔ b ∈ G.freeBonds ∧ γ.fieldAt b = Sum.inl () := by
  classical
  exact Finset.mem_filter
private theorem fine_settingOf_of_not_mem_free {b : TorusBond (n * R.params.side)}
    (hf : b ∉ (G.settingOf γ).free) :
    (G.settingOf γ).fine b.1 b.2 = match γ.fieldAt b with
      | Sum.inr g => g
      | Sum.inl _ => G.state.fieldWithStoredLinks (trivialField _) b.1 b.2 := by apply _root_.YangMills.Construction.BoxAgreement.settingOf_fine_of_not_mem_free <;> assumption
private theorem mem_support_settingOf_iff (z : TorusSite (n * R.params.side)) :
    z ∈ (G.settingOf γ).support ↔ z ∈ G.recordedSites ∨ z ∈ γ.sites :=
  Finset.mem_union
private theorem labelling_of_mem_sites {z : TorusSite (n * R.params.side)} (hz : z ∈ (G.settingOf γ).support)
    (hg : z ∈ γ.sites) : (G.settingOf γ).labelling ⟨z, hz⟩ = γ.labelAt hg := dif_pos hg
private theorem labelling_of_not_mem_sites {z : TorusSite (n * R.params.side)}
    (hz : z ∈ (G.settingOf γ).support) (hg : z ∉ γ.sites) :
    (G.settingOf γ).labelling ⟨z, hz⟩ =
      G.recordedLabel ⟨z, (Finset.mem_union.mp hz).resolve_right hg⟩ := dif_neg hg
private theorem bases_settingOf (c : (stepBlockFrame R.params.side n).Cell) :
    (G.settingOf γ).bases c =
      match γ.baseAt (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) with
      | Sum.inr o => frameBlockSite R.params.side n (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) o
      | Sum.inl _ => G.groundBases c := rfl
private theorem exists_bases_settingOf_eq_fineSite (hodd : Odd R.params.side) (h : Fin 4 → ℤ) :
    ∃ o, o ∈ centredCube R.params.side ∧
      toTorusSite (n * R.params.side) ((G.settingOf γ).bases
        (StepCosts.torusSiteInFrame (stepBlockFrame R.params.side n) 1 (Y + siteOfInt h))) =
        fineSite R.params.side Y h o := by
  have ec : toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n
      (StepCosts.torusSiteInFrame (stepBlockFrame R.params.side n) 1 (Y + siteOfInt h)) = Y + siteOfInt h :=
    TopLevelSites.toTorusSite_torusSiteInFrame BlockTrees.stepBlockFrame_period_one _
  have e0 := bases_settingOf G γ (StepCosts.torusSiteInFrame (stepBlockFrame R.params.side n) 1 (Y + siteOfInt h))
  rw [ec] at e0
  rw [e0]
  rcases γ.baseAt (Y + siteOfInt h) with u | b
  · show ∃ o, o ∈ centredCube R.params.side ∧ toTorusSite (n * R.params.side) (G.groundBases _) = _
    unfold GasGround.groundBases
    simp only [ec]
    cases hs : G.state.markAt (Y + siteOfInt h) with
    | none =>
      have h0 : (0 : Fin 4 → ℤ) ∈ centredCube R.params.side := by
        rw [BlockOffsets.mem_centredCube_iff]
        intro i
        have hpos : (1 : ℤ) ≤ R.params.side := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
        have : 0 ≤ ((R.params.side : ℤ) - 1) / 2 := by omega
        simpa using this
      exact ⟨0, h0, toTorusSite_cellCentre_eq_fineSite Y h⟩
    | some s =>
      obtain ⟨o, ho, e1⟩ := exists_centredCube_blockSite_eq hodd Y h s.basePoint
      refine ⟨o, ho, ?_⟩
      simp only [frameBlockSite]
      rw [TopLevelSites.toTorusSite_torusSiteInFrame BlockTrees.stepBlockFrame_period_zero]
      exact e1
  · obtain ⟨o, ho, e1⟩ := exists_centredCube_blockSite_eq hodd Y h b
    refine ⟨o, ho, ?_⟩
    simp only [frameBlockSite]
    rw [TopLevelSites.toTorusSite_torusSiteInFrame BlockTrees.stepBlockFrame_period_zero]
    exact e1
private theorem settingsAgreeNear_settingOf (hodd : Odd R.params.side) (hside : 2 * m + 2 < n)
    (hbox : ∀ (θ : GasSupport R n) (h : Fin 4 → ℤ), OffsetInBox m h → Y + siteOfInt h ∈ θ.core → γ θ = γ' θ) :
    SettingsAgreeNear (G.settingOf γ) (G.settingOf γ') Y Y m := by
  classical
  have hsite : ∀ h o, OffsetInBox m h → o ∈ centredCube R.params.side → ∀ θ : GasSupport R n,
      fineSite R.params.side Y h o ∈ θ.2 → γ θ = γ' θ := by
    intro h o hh ho θ hz
    refine hbox θ h hh ?_
    have := parentBlock_mem_core θ hz
    rwa [BlockOffsets.parentBlock_fineSite hodd Y h o ho] at this
  have hfree : ∀ q : NearBondIndex, IsNearIndex R.params.side m q →
      (nearBond R.params.side Y q ∈ (G.settingOf γ).free ↔ nearBond R.params.side Y q ∈ (G.settingOf γ').free) := by
    rintro ⟨h, o, i⟩ ⟨hh, ho⟩
    rw [mem_free_settingOf_iff, mem_free_settingOf_iff]
    show _ ∧ γ.fieldAt (fineSite R.params.side Y h o, i) = _ ↔
      _ ∧ γ'.fieldAt (fineSite R.params.side Y h o, i) = _
    rw [fieldAt_fineSite_congr γ γ' Y m hodd hbox h o i hh ho]
  have hstored : ∀ q, IsNearIndex R.params.side m q → nearBond R.params.side Y q ∉ (G.settingOf γ).free →
      (G.settingOf γ).fine (nearBond R.params.side Y q).1 q.2.2 =
        (G.settingOf γ').fine (nearBond R.params.side Y q).1 q.2.2 := by
    rintro ⟨h, o, i⟩ ⟨hh, ho⟩ hf
    have hf' : nearBond R.params.side Y (h, o, i) ∉ (G.settingOf γ').free :=
      fun h' => hf ((hfree _ ⟨hh, ho⟩).mpr h')
    have e1 := fine_settingOf_of_not_mem_free G γ hf
    have e2 := fine_settingOf_of_not_mem_free G γ' hf'
    have e3 : γ.fieldAt (nearBond R.params.side Y (h, o, i)) = γ'.fieldAt (nearBond R.params.side Y (h, o, i)) :=
      fieldAt_fineSite_congr γ γ' Y m hodd hbox h o i hh ho
    show (G.settingOf γ).fine (nearBond R.params.side Y (h, o, i)).1 (nearBond R.params.side Y (h, o, i)).2 =
      (G.settingOf γ').fine (nearBond R.params.side Y (h, o, i)).1 (nearBond R.params.side Y (h, o, i)).2
    rw [e1, e2, e3]
  have hstate : ∀ h o, OffsetInBox m h → o ∈ centredCube R.params.side →
      (fineSite R.params.side Y h o ∈ (G.settingOf γ).support ↔
        fineSite R.params.side Y h o ∈ (G.settingOf γ').support) := by
    intro h o hh ho
    rw [mem_support_settingOf_iff, mem_support_settingOf_iff, mem_sites_iff_of_congr (hsite h o hh ho)]
  have hlabels : ∀ h o (hz : fineSite R.params.side Y h o ∈ (G.settingOf γ).support)
      (hz' : fineSite R.params.side Y h o ∈ (G.settingOf γ').support), OffsetInBox m h →
      o ∈ centredCube R.params.side →
      (G.settingOf γ).labelling ⟨_, hz⟩ = (G.settingOf γ').labelling ⟨_, hz'⟩ := by
    intro h o hz hz' hh ho
    have hs := mem_sites_iff_of_congr (γ := γ) (γ' := γ') (hsite h o hh ho)
    by_cases hg : fineSite R.params.side Y h o ∈ γ.sites
    · rw [labelling_of_mem_sites G γ hz hg, labelling_of_mem_sites G γ' hz' (hs.mp hg)]
      exact labelAt_congr (hsite h o hh ho) hg (hs.mp hg)
    · rw [labelling_of_not_mem_sites G γ hz hg, labelling_of_not_mem_sites G γ' hz' fun a => hg (hs.mpr a)]
  have hbases : ∀ h, OffsetInBox m h → ∃ o, o ∈ centredCube R.params.side ∧
      toTorusSite (n * R.params.side) ((G.settingOf γ).bases
        (StepCosts.torusSiteInFrame (stepBlockFrame R.params.side n) 1 (Y + siteOfInt h))) =
        fineSite R.params.side Y h o ∧
      toTorusSite (n * R.params.side) ((G.settingOf γ').bases
        (StepCosts.torusSiteInFrame (stepBlockFrame R.params.side n) 1 (Y + siteOfInt h))) =
        fineSite R.params.side Y h o := by
    intro h hh
    have ec : toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n
        (StepCosts.torusSiteInFrame (stepBlockFrame R.params.side n) 1 (Y + siteOfInt h)) = Y + siteOfInt h :=
      TopLevelSites.toTorusSite_torusSiteInFrame BlockTrees.stepBlockFrame_period_one _
    have hb : γ.baseAt (Y + siteOfInt h) = γ'.baseAt (Y + siteOfInt h) :=
      baseAt_congr fun θ hc => hbox θ h hh hc
    have eb : (G.settingOf γ).bases (StepCosts.torusSiteInFrame (stepBlockFrame R.params.side n) 1 (Y + siteOfInt h)) =
        (G.settingOf γ').bases (StepCosts.torusSiteInFrame (stepBlockFrame R.params.side n) 1 (Y + siteOfInt h)) := by
      have e0 := bases_settingOf G γ (StepCosts.torusSiteInFrame (stepBlockFrame R.params.side n) 1 (Y + siteOfInt h))
      have e1 := bases_settingOf G γ' (StepCosts.torusSiteInFrame (stepBlockFrame R.params.side n) 1 (Y + siteOfInt h))
      rw [ec] at e0 e1
      rw [e0, e1, hb]
    obtain ⟨o, ho, e1⟩ := exists_bases_settingOf_eq_fineSite G γ Y hodd h
    exact ⟨o, ho, e1, eb ▸ e1⟩
  have hV : (G.settingOf γ).coarse = (G.settingOf γ').coarse := rfl
  exact { lt_extent := hside, lt_extent' := hside, coarse_agree := by rw [hV]; intro b _; rfl,
          free_iff := hfree, fine_eq := hstored,
          frame_eq := fun q _ _ => by simp only [ChartSetting.frame, hV], support_iff := hstate,
          labelling_eq := hlabels, bases_match := hbases }
end NearAgreement
theorem localSettingsAgree : LocalSettingsAgree := by
  intro R n _ G σ σ' Y m hodd hside hag
  exact settingsAgreeNear_settingOf G (G.familyOf σ) (G.familyOf σ') Y m hodd hside
    fun θ h hh hc => familyOf_congr G fun hs => hag ⟨θ, hs⟩ ⟨h, hh, hc⟩
end ConfigurationSettings
end YangMills.Construction
end
