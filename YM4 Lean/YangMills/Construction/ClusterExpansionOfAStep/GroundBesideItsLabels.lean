import YangMills.Construction.ClusterExpansionOfAStep.ZetaOfAGroundIsBorelProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open TorusFields TorusLumps StepSettings StepGas BlockAverages LumpContours
variable {R : StepSetup} {n : ℕ} [NeZero n]
def TorusLumps.BlockLabels.forgetLabels {Ω : Type} {L : ℕ} (s : BlockLabels Ω L) : BlockLabels Unit L :=
  { isCore := s.isCore
    badBond := s.badBond
    siteLabel := fun k => (s.siteLabel k).map id fun _ => ()
    basePoint := s.basePoint
    linkValue := s.linkValue }
def StepSettings.CoarseState.AgreeUpToLabels (q q' : CoarseState R n) : Prop :=
  ∀ y, (q.markAt y).map BlockLabels.forgetLabels = (q'.markAt y).map BlockLabels.forgetLabels
namespace StepGas
variable {q q' : CoarseState R n}
theorem markAt_some_of_agree (h : q.AgreeUpToLabels q') {y : TorusSite n}
    {s : BlockLabels R.labels.Ω R.params.side} (hs : q.markAt y = some s) :
    ∃ s', q'.markAt y = some s' ∧ s.forgetLabels = s'.forgetLabels := by
  have := h y
  rw [hs] at this
  cases hq : q'.markAt y with
  | none => rw [hq] at this; simp at this
  | some s' =>
    rw [hq] at this
    exact ⟨s', rfl, by simpa using this⟩
theorem agreeUpToLabels_symm (h : q.AgreeUpToLabels q') : q'.AgreeUpToLabels q := fun y => (h y).symm
theorem markAt_none_of_agree (h : q.AgreeUpToLabels q') {y : TorusSite n} (hs : q.markAt y = none) :
    q'.markAt y = none := by
  have := h y
  rw [hs] at this
  cases hq : q'.markAt y with
  | none => rfl
  | some s' => rw [hq] at this; simp at this
theorem siteLabel_isRight_of_forget {Ω : Type} {L : ℕ} {s : BlockLabels Ω L} {s' : BlockLabels Ω L}
    (h : s.forgetLabels = s'.forgetLabels) (k : BlockOffset L) :
    (s.siteLabel k).isRight = (s'.siteLabel k).isRight := by
  have := congrArg (fun t : BlockLabels Unit L => t.siteLabel k) h
  simp only [BlockLabels.forgetLabels] at this
  cases h1 : s.siteLabel k <;> cases h2 : s'.siteLabel k <;> simp_all
theorem linkValue_eq_of_forget {Ω : Type} {L : ℕ} {s s' : BlockLabels Ω L}
    (h : s.forgetLabels = s'.forgetLabels) : s.linkValue = s'.linkValue := by
  have := congrArg (fun t : BlockLabels Unit L => t.linkValue) h
  exact this
theorem badBond_eq_of_forget {Ω : Type} {L : ℕ} {s s' : BlockLabels Ω L}
    (h : s.forgetLabels = s'.forgetLabels) : s.badBond = s'.badBond := by
  have := congrArg (fun t : BlockLabels Unit L => t.badBond) h
  exact this
theorem fieldWithStoredLinks_eq_of_agree (h : q.AgreeUpToLabels q') (W : TorusField (n * R.params.side)) :
    q.fieldWithStoredLinks W = q'.fieldWithStoredLinks W := by
  funext x i
  unfold CoarseState.fieldWithStoredLinks
  cases hq : q.markAt (parentBlock R.params.side x) with
  | none => simp only [markAt_none_of_agree h hq]
  | some s =>
    obtain ⟨s', hs', e⟩ := markAt_some_of_agree h hq
    simp only [hs', linkValue_eq_of_forget e]
theorem recordedBad_eq_of_agree (h : q.AgreeUpToLabels q') (top C : Finset (TorusSite n)) (V : TorusField n) :
    (⟨top, C, V, q⟩ : GasGround R n).recordedBad = (⟨top, C, V, q'⟩ : GasGround R n).recordedBad := by
  classical
  ext b
  simp only [GasGround.recordedBad, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨s, hs, hb⟩
    obtain ⟨s', hs', e⟩ := markAt_some_of_agree h hs
    exact ⟨s', hs', by rw [← hb, badBond_eq_of_forget e]⟩
  · rintro ⟨s, hs, hb⟩
    obtain ⟨s', hs', e⟩ := markAt_some_of_agree (agreeUpToLabels_symm h) hs
    exact ⟨s', hs', by rw [← hb, badBond_eq_of_forget e]⟩
theorem labelAt_isRight_eq_of_agree (h : q.AgreeUpToLabels q') (z : TorusSite (n * R.params.side)) :
    (q.labelAt z).isRight = (q'.labelAt z).isRight := by
  unfold CoarseState.labelAt
  cases hq : q.markAt (parentBlock R.params.side z) with
  | none => simp only [markAt_none_of_agree h hq]
  | some s =>
    obtain ⟨s', hs', e⟩ := markAt_some_of_agree h hq
    simp only [hs']
    exact siteLabel_isRight_of_forget e _
theorem recordedSites_eq_of_agree (h : q.AgreeUpToLabels q') (top C : Finset (TorusSite n)) (V : TorusField n) :
    (⟨top, C, V, q⟩ : GasGround R n).recordedSites = (⟨top, C, V, q'⟩ : GasGround R n).recordedSites := by
  classical
  ext z
  simp only [GasGround.recordedSites, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [labelAt_isRight_eq_of_agree h z]
theorem isRecorded_iff_of_agree (h : q.AgreeUpToLabels q') (top C : Finset (TorusSite n)) (V : TorusField n)
    (b : TorusBond (n * R.params.side)) :
    (⟨top, C, V, q⟩ : GasGround R n).IsRecorded b ↔ (⟨top, C, V, q'⟩ : GasGround R n).IsRecorded b := by
  unfold GasGround.IsRecorded
  constructor
  · rintro ⟨s, hs, hb⟩
    obtain ⟨s', hs', e⟩ := markAt_some_of_agree h hs
    exact ⟨s', hs', by rw [← hb, linkValue_eq_of_forget e]⟩
  · rintro ⟨s, hs, hb⟩
    obtain ⟨s', hs', e⟩ := markAt_some_of_agree (agreeUpToLabels_symm h) hs
    exact ⟨s', hs', by rw [← hb, linkValue_eq_of_forget e]⟩
theorem freeBonds_eq_of_agree (h : q.AgreeUpToLabels q') (top C : Finset (TorusSite n)) (V : TorusField n) :
    (⟨top, C, V, q⟩ : GasGround R n).freeBonds = (⟨top, C, V, q'⟩ : GasGround R n).freeBonds := by
  classical
  ext b
  simp only [GasGround.freeBonds, Finset.mem_filter]
  rw [isRecorded_iff_of_agree h top C V b]
theorem chartSetting_field_zero_congr {s s' : ChartSetting R n} (hV : s.coarse = s'.coarse)
    (hb : s.fine = s'.fine) (hf : s.free = s'.free) : s.field 0 = s'.field 0 := by
  funext x i
  unfold ChartSetting.field
  by_cases hx : (x, i) ∈ s.free
  · have hx' : (x, i) ∈ s'.free := hf ▸ hx
    rw [dif_pos hx, dif_pos hx']
    simp only [Pi.zero_apply, chartLink, ChartSetting.frame, hV, hb]
  · have hx' : (x, i) ∉ s'.free := hf ▸ hx
    rw [dif_neg hx, dif_neg hx', hb]
theorem gasFamily_empty_sites : (GasFamily.empty : GasFamily R n).sites = ∅ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.sites_empty <;> assumption
theorem settingWithFamily_free_eq_of_agree (h : q.AgreeUpToLabels q') (top C : Finset (TorusSite n))
    (V : TorusField n) (γ : GasFamily R n) :
    ((⟨top, C, V, q⟩ : GasGround R n).settingWithFamily γ).free =
      ((⟨top, C, V, q'⟩ : GasGround R n).settingWithFamily γ).free := by
  simp only [GasGround.settingWithFamily]
  rw [freeBonds_eq_of_agree h top C V]
theorem settingWithFamily_fine_eq_of_agree (h : q.AgreeUpToLabels q') (top C : Finset (TorusSite n))
    (V : TorusField n) (γ : GasFamily R n) :
    ((⟨top, C, V, q⟩ : GasGround R n).settingWithFamily γ).fine =
      ((⟨top, C, V, q'⟩ : GasGround R n).settingWithFamily γ).fine := by
  funext x i
  simp only [GasGround.settingWithFamily]
  rw [fieldWithStoredLinks_eq_of_agree h]
theorem groundSetting_fine_eq_of_agree (h : q.AgreeUpToLabels q') (top C : Finset (TorusSite n)) (V : TorusField n) :
    (⟨top, C, V, q⟩ : GasGround R n).groundSetting.fine = (⟨top, C, V, q'⟩ : GasGround R n).groundSetting.fine :=
  chartSetting_field_zero_congr rfl (settingWithFamily_fine_eq_of_agree h top C V _)
    (settingWithFamily_free_eq_of_agree h top C V _)
theorem groundSetting_support (G : GasGround R n) : G.groundSetting.support = G.recordedSites := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.groundSetting_support <;> assumption
theorem labelAt_of_mem_groundSetting_support (G : GasGround R n) (z : TorusSite (n * R.params.side))
    (hz : z ∈ G.groundSetting.support) :
    G.state.labelAt z = Sum.inr (G.groundSetting.labelling ⟨z, hz⟩) := by
  classical
  have hz' : z ∈ G.recordedSites := by rwa [groundSetting_support] at hz
  have hs : z ∉ (GasFamily.empty : GasFamily R n).sites := by rw [gasFamily_empty_sites]; simp
  have h1 : G.groundSetting.labelling ⟨z, hz⟩ = G.recordedLabel ⟨z, hz'⟩ := by
    show (if h : z ∈ (GasFamily.empty : GasFamily R n).sites then _ else _) = _
    rw [dif_neg hs]
  rw [h1]
  unfold GasGround.recordedLabel
  exact (Sum.inr_getRight _ _).symm
end StepGas
end YangMills.Construction
end
