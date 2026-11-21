import YangMills.Construction.ClusterExpansionOfAStep.ClassBesideAFamilyProof
import YangMills.Construction.ClusterExpansionOfAStep.ClassesOfAStepAreCounted
import YangMills.Construction.ClusterExpansionOfAStep.ColumnFloor
import YangMills.Construction.ClusterExpansionOfAStep.ColumnsOfTheGas
import YangMills.Construction.ClusterExpansionOfAStep.ConditionalLawsOfAWeight
import YangMills.Construction.ClusterExpansionOfAStep.ConfigurationsOfTheGasAreSettings
import YangMills.Construction.ClusterExpansionOfAStep.CountFloorCanBeMet
import YangMills.Construction.ClusterExpansionOfAStep.DoubleRatiosOfASetting
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace YangMills.Construction.ClusterExpansionOfAStep
open TorusFields TorusLumps CoreColumns StepGas StepSettings
namespace GasColumns
section Blocks
variable {n : ℕ} [NeZero n] {L : ℕ} [NeZero L]
theorem supDist_le_of_parentBlock_eq {x y : TorusSite (n * L)} (h : parentBlock L x = parentBlock L y) :
    supDist x y ≤ L := by apply _root_.YangMills.Construction.TorusLumps.supDist_le_of_parentBlock_eq <;> assumption
theorem supDist_parentBlock_le (x y : TorusSite (n * L)) :
    supDist (parentBlock L x) (parentBlock L y) ≤ supDist x y / L + 1 := by apply _root_.YangMills.Construction.TorusBalls.supDist_parentBlock_le_div_add_one <;> assumption
end Blocks
variable {R : StepSetup} {n : ℕ} [NeZero n]
section Geometry
theorem parentBlock_mem_core (θ : GasSupport R n) {z : TorusSite (n * R.params.side)} (hz : z ∈ θ.sites) :
    parentBlock R.params.side z ∈ θ.core := by apply _root_.YangMills.Construction.StepGas.GasSupport.parentBlock_mem_core <;> assumption
theorem core_disjoint_of_farApart {θ θ' : GasSupport R n} (h : θ.FarApart θ') (hL : R.params.side ≤ R.range)
    {y : TorusSite n} (hy : y ∈ θ.core) (hy' : y ∈ θ'.core) : False := by
  classical
  obtain ⟨x, hx⟩ := (Finset.mem_filter.mp hy).2
  obtain ⟨x', hx'⟩ := (Finset.mem_filter.mp hy').2
  obtain ⟨hb, hw⟩ := Finset.mem_inter.mp hx
  obtain ⟨hb', hw'⟩ := Finset.mem_inter.mp hx'
  obtain ⟨z, hz, hxz⟩ := (mem_thickening _ _ _).mp hw
  obtain ⟨z', hz', hxz'⟩ := (mem_thickening _ _ _).mp hw'
  have e1 : parentBlock R.params.side x = y := Finset.mem_singleton.mp (Finset.mem_filter.mp hb).2
  have e2 : parentBlock R.params.side x' = y := Finset.mem_singleton.mp (Finset.mem_filter.mp hb').2
  have hxx := supDist_le_of_parentBlock_eq (e1.trans e2.symm)
  have h1 := supDist_triangle z x z'
  have h2 := supDist_triangle x x' z'
  have h3 := h z hz z' hz'
  rw [supDist_comm z x] at h1
  omega
theorem setGap_le_nearGap {θ θ' : GasSupport R n} (h : ¬ θ.FarApart θ') :
    setGap θ.core θ'.core ≤ nearGap R.params.side R.range := by
  simp only [GasSupport.FarApart, not_forall, not_lt] at h
  obtain ⟨z, hz, z', hz', hzz⟩ := h
  have h1 : setGap θ.core θ'.core ≤ supDist (parentBlock R.params.side z) (parentBlock R.params.side z') :=
    Nat.sInf_le ⟨_, parentBlock_mem_core θ hz, _, parentBlock_mem_core θ' hz', rfl⟩
  have h2 := supDist_parentBlock_le (L := R.params.side) z z'
  have h3 : supDist z z' / R.params.side ≤ 10 * R.range / R.params.side := Nat.div_le_div_right hzz
  unfold nearGap
  omega
theorem mem_core_of_meets {θ : GasSupport R n} {Y : TorusSite n} (h : θ.Meets Y) : Y ∈ θ.core := by
  classical
  rcases h with ⟨b, hb, e⟩ | ⟨z, hz, e⟩
  · rw [← e]
    exact parentBlock_mem_core θ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hb))
  · rw [← e]
    exact parentBlock_mem_core θ (Finset.mem_union_right _ hz)
theorem mem_sites_of_mem_free (θ : GasSupport R n) {z : TorusSite (n * R.params.side)} (hz : z ∈ θ.2) :
    z ∈ θ.sites :=
  Finset.mem_union_right _ hz
theorem one_le_supportUnitCount {r : ℕ} {θ : GasSupport R n} (h : IsClusterSupport R.params.side r θ) :
    1 ≤ supportUnitCount R.params.side r θ := by
  classical
  obtain ⟨z, hz⟩ := h.1
  rcases Finset.mem_union.mp hz with h1 | h2
  · obtain ⟨b, hb, _⟩ := Finset.mem_image.mp h1
    have : 0 < badBlockCount R.params.side θ := Finset.card_pos.mpr ⟨_, Finset.mem_image_of_mem _ hb⟩
    unfold supportUnitCount
    omega
  · have hne : {k | ∃ C : Finset (TorusSite (n * R.params.side)), C.card = k ∧ θ.2 ⊆ thickening (4 * r) C}.Nonempty :=
      ⟨_, θ.2, rfl, fun y hy => (mem_thickening _ _ _).2 ⟨y, hy, by simp [supDist_self]⟩⟩
    obtain ⟨C, hC, hcov⟩ := Nat.sInf_mem hne
    have : ballCoverNumber (4 * r) θ.2 ≠ 0 := by
      intro h0
      have hC0 : C.card = 0 := hC.trans h0
      rw [Finset.card_eq_zero] at hC0
      subst hC0
      obtain ⟨x, hx, _⟩ := (mem_thickening _ _ _).mp (hcov h2)
      simp at hx
    unfold supportUnitCount
    omega
end Geometry
section Gas
variable (G : GasGround R n)
theorem exists_choose_congr {α : Type*} {p q : α → Prop} (hpq : p = q) (h : ∃ a, p a) (h' : ∃ a, q a) :
    h.choose = h'.choose := by apply _root_.YangMills.Construction.SeparatedClasses.LastNonempty.choose_eq_of_eq <;> assumption
theorem state_congr {γ γ' : GasFamily R n} {θ : GasSupport R n} (e : γ θ = γ' θ) (h₁ : γ.Occupies θ)
    (h₂ : γ'.Occupies θ) : γ.state h₁ = γ'.state h₂ := by apply _root_.YangMills.Construction.InBoxTransfer.state_congr <;> assumption
theorem occupies_iff {γ γ' : GasFamily R n} {θ : GasSupport R n} (e : γ θ = γ' θ) :
    γ.Occupies θ ↔ γ'.Occupies θ := by apply _root_.YangMills.Construction.InBoxTransfer.occupies_congr <;> assumption
theorem fieldAt_congr {γ γ' : GasFamily R n} {b : TorusBond (n * R.params.side)}
    (h : ∀ θ : GasSupport R n, b ∈ θ.coreBonds → γ θ = γ' θ) : γ.fieldAt b = γ'.fieldAt b := by apply _root_.YangMills.Construction.InBoxTransfer.fieldAt_congr <;> assumption
theorem baseAt_congr {γ γ' : GasFamily R n} {y : TorusSite n}
    (h : ∀ θ : GasSupport R n, y ∈ θ.core → γ θ = γ' θ) : γ.baseAt y = γ'.baseAt y := by apply _root_.YangMills.Construction.InBoxTransfer.baseAt_congr <;> assumption
theorem mem_sites_iff {γ : GasFamily R n} {z : TorusSite (n * R.params.side)} :
    z ∈ γ.sites ↔ ∃ θ, γ.Occupies θ ∧ z ∈ θ.2 := by apply _root_.YangMills.Construction.InBoxTransfer.mem_sites_iff <;> assumption
theorem labelAt_congr {γ γ' : GasFamily R n} {z : TorusSite (n * R.params.side)}
    (h : ∀ θ : GasSupport R n, z ∈ θ.2 → γ θ = γ' θ) (hz : z ∈ γ.sites) (hz' : z ∈ γ'.sites) :
    γ.labelAt hz = γ'.labelAt hz' := by
  have hp : (fun θ : GasSupport R n => γ.Occupies θ ∧ z ∈ θ.2) = fun θ => γ'.Occupies θ ∧ z ∈ θ.2 := by
    funext θ
    apply propext
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(occupies_iff (h θ h2)).mp h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(occupies_iff (h θ h2)).mpr h1, h2⟩
  have hc := exists_choose_congr hp (GasFamily.exists_of_mem_sites hz) (GasFamily.exists_of_mem_sites hz')
  have key : ∀ (θ₁ θ₂ : GasSupport R n), θ₁ = θ₂ → ∀ (h₁ : γ.Occupies θ₁) (h₂ : γ'.Occupies θ₂)
      (m₁ : z ∈ θ₁.2) (m₂ : z ∈ θ₂.2), (γ.state h₁).2.1 ⟨z, m₁⟩ = (γ'.state h₂).2.1 ⟨z, m₂⟩ := by
    intro θ₁ θ₂ e h₁ h₂ m₁ m₂
    subst e
    rw [state_congr (h θ₁ m₁) h₁ h₂]
  exact key _ _ hc _ _ _ _
theorem mem_coreBonds_of_bad (θ : GasSupport R n) (hr : 1 ≤ R.range) {b : TorusBond (n * R.params.side)}
    (hb : b ∈ θ.1) : b ∈ θ.coreBonds := by
  classical
  have h1 : b.1 ∈ θ.sites := Finset.mem_union_left _ (Finset.mem_image_of_mem _ hb)
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, parentBlock_mem_core θ h1, ?_⟩
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, b.1 + unitStep (n * R.params.side) b.2, ?_⟩
  refine Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_singleton_self _⟩, ?_⟩
  refine (mem_thickening _ _ _).mpr ⟨b.1, h1, ?_⟩
  rw [supDist_comm]
  have := supDist_add_unitStep_le b.1 b.2
  omega
theorem bases_congr {γ γ' : GasFamily R n} {c : (stepBlockFrame R.params.side n).Cell}
    (h : γ.baseAt (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) =
      γ'.baseAt (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c)) :
    (G.settingOf γ).bases c = (G.settingOf γ').bases c := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.bases_settingOf_congr <;> assumption
theorem agreeOn_of_eq {γ γ' : GasFamily R n} (hr : 1 ≤ R.range) (B : TorusBond (n * R.params.side) → Prop)
    (Q : Finset (TorusSite n))
    (hb : ∀ b, B b → ∀ θ : GasSupport R n, b ∈ θ.coreBonds → γ θ = γ' θ)
    (hz : ∀ z, parentBlock R.params.side z ∈ Q → ∀ θ : GasSupport R n, z ∈ θ.2 → γ θ = γ' θ)
    (hy : ∀ y ∈ Q, ∀ θ : GasSupport R n, y ∈ θ.core → γ θ = γ' θ) :
    (G.settingOf γ).AgreeOn (G.settingOf γ') B Q := by
  classical
  have hfree : ∀ b, B b → (b ∈ (G.settingOf γ).free ↔ b ∈ (G.settingOf γ').free) := by
    intro b hB
    change b ∈ G.freeBonds.filter (fun b => γ.fieldAt b = Sum.inl ()) ↔
      b ∈ G.freeBonds.filter (fun b => γ'.fieldAt b = Sum.inl ())
    simp only [Finset.mem_filter, fieldAt_congr (hb b hB)]
  have hsites : ∀ z, parentBlock R.params.side z ∈ Q → (z ∈ γ.sites ↔ z ∈ γ'.sites) := by
    intro z hq
    rw [mem_sites_iff, mem_sites_iff]
    exact exists_congr fun θ => ⟨fun ⟨h1, h2⟩ => ⟨(occupies_iff (hz z hq θ h2)).mp h1, h2⟩,
      fun ⟨h1, h2⟩ => ⟨(occupies_iff (hz z hq θ h2)).mpr h1, h2⟩⟩
  refine ⟨hfree, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hB
    have key : ∀ θ : GasSupport R n, b ∈ θ.1 → (γ.Occupies θ ↔ γ'.Occupies θ) := fun θ h =>
      occupies_iff (hb b hB θ (mem_coreBonds_of_bad θ hr h))
    change b ∈ (G.recordedBad ∪ (Finset.univ.filter fun θ => γ.Occupies θ).biUnion Prod.fst ∪ _) ↔
      b ∈ (G.recordedBad ∪ (Finset.univ.filter fun θ => γ'.Occupies θ).biUnion Prod.fst ∪ _)
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ((h | ⟨θ, h1, h2⟩) | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr ⟨θ, (key θ h2).mp h1, h2⟩)
      · exact Or.inr h
    · rintro ((h | ⟨θ, h1, h2⟩) | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr ⟨θ, (key θ h2).mpr h1, h2⟩)
      · exact Or.inr h
  · intro b hB hnf
    have hnf' : b ∉ (G.settingOf γ').free := fun c => hnf ((hfree b hB).mpr c)
    have e1 : (G.settingOf γ).fine b.1 b.2 = (G.settingWithFamily γ).fine b.1 b.2 := by
      change (G.settingWithFamily γ).field 0 b.1 b.2 = _
      unfold ChartSetting.field
      exact dif_neg (show (b.1, b.2) ∉ (G.settingWithFamily γ).free from hnf)
    have e2 : (G.settingOf γ').fine b.1 b.2 = (G.settingWithFamily γ').fine b.1 b.2 := by
      change (G.settingWithFamily γ').field 0 b.1 b.2 = _
      unfold ChartSetting.field
      exact dif_neg (show (b.1, b.2) ∉ (G.settingWithFamily γ').free from hnf')
    rw [e1, e2]
    change (match γ.fieldAt (b.1, b.2) with
      | Sum.inr g => g
      | Sum.inl _ => G.state.fieldWithStoredLinks (trivialField _) b.1 b.2) = match γ'.fieldAt (b.1, b.2) with
      | Sum.inr g => g
      | Sum.inl _ => G.state.fieldWithStoredLinks (trivialField _) b.1 b.2
    rw [fieldAt_congr (hb b hB)]
  · intro z hq
    change z ∈ G.recordedSites ∪ γ.sites ↔ z ∈ G.recordedSites ∪ γ'.sites
    simp only [Finset.mem_union, hsites z hq]
  · intro z hz₁ hz₂ hq
    change (if h : z ∈ γ.sites then γ.labelAt h else
        G.recordedLabel ⟨z, (Finset.mem_union.mp hz₁).resolve_right h⟩) =
      (if h : z ∈ γ'.sites then γ'.labelAt h else
        G.recordedLabel ⟨z, (Finset.mem_union.mp hz₂).resolve_right h⟩)
    by_cases h : z ∈ γ.sites
    · have h' := (hsites z hq).mp h
      rw [dif_pos h, dif_pos h']
      exact labelAt_congr (hz z hq) h h'
    · have h' := fun c => h ((hsites z hq).mpr c)
      rw [dif_neg h, dif_neg h']
  · intro y hq
    have ey : toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n
        (StepCosts.torusSiteInFrame (stepBlockFrame R.params.side n) 1 y) = y :=
      TopLevelSites.toTorusSite_torusSiteInFrame
        (fun i => by simp [stepBlockFrame, BlockAverages.BlockFrame.period]) y
    exact bases_congr G (by rw [ey]; exact baseAt_congr (hy y hq))
theorem familyOf_congr {c c' : G.Config} {θ : GasSupport R n} (h : ∀ k : G.GasSpin, k.1 = θ → c k = c' k) :
    G.familyOf c θ = G.familyOf c' θ := by
  classical
  unfold GasGround.familyOf
  by_cases hθ : G.IsGasSupport θ
  · rw [dif_pos hθ, dif_pos hθ, h ⟨θ, hθ⟩ rfl]
  · rw [dif_neg hθ, dif_neg hθ]
theorem agreeOn_of_spins_eq {c c' : G.Config} (hr : 1 ≤ R.range) (D : G.GasSpin → Prop)
    (hD : ∀ k, ¬ D k → c k = c' k)
    (B : TorusBond (n * R.params.side) → Prop) (Q : Finset (TorusSite n))
    (h1 : ∀ k, D k → ∀ b, B b → b ∉ k.1.coreBonds)
    (h2 : ∀ k, D k → ∀ z, parentBlock R.params.side z ∈ Q → z ∉ k.1.2)
    (h3 : ∀ k, D k → ∀ y ∈ Q, y ∉ k.1.core) :
    (G.settingOf (G.familyOf c)).AgreeOn (G.settingOf (G.familyOf c')) B Q := by
  refine agreeOn_of_eq G hr B Q (fun b hB θ hθ => familyOf_congr G fun k e => hD k fun hk => ?_)
    (fun z hq θ hθ => familyOf_congr G fun k e => hD k fun hk => ?_)
    (fun y hq θ hθ => familyOf_congr G fun k e => hD k fun hk => ?_)
  · exact h1 k hk b hB (e ▸ hθ)
  · exact h2 k hk z hq (e ▸ hθ)
  · exact h3 k hk y hq (e ▸ hθ)
theorem weight_eq_integral {c : G.Config} (hs : G.pairConstraint.IsAdmissible c)
    (hp : 0 < (G.settingOf (G.familyOf c)).integral) :
    G.weight c = (G.settingOf (G.familyOf c)).integral := by
  classical
  set s := G.settingOf (G.familyOf c) with hsdef
  have hnn : ∀ η, 0 ≤ s.cutoffProduct η * Real.exp (-s.potential η) := by
    intro η
    refine mul_nonneg (Finset.prod_nonneg fun b _ => ?_) (Real.exp_pos _).le
    unfold ColdStepAtMirrorFrames.cutoffFactor
    split_ifs
    · exact (Real.exp_pos _).le
    · exact le_rfl
  have hint : Integrable (fun η => s.cutoffProduct η * Real.exp (-s.potential η)) := by
    by_contra hc
    have : s.integral = 0 := integral_undef hc
    linarith
  unfold GasGround.weight
  rw [if_pos hs]
  change (∫⁻ η, ENNReal.ofReal (s.cutoffProduct η * Real.exp (-s.potential η))).toReal = s.integral
  unfold ChartSetting.integral
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnn) hint.aestronglyMeasurable]
theorem isAdmissible_update_vacant {σ : G.Config} {i : G.GasSpin} {s : G.SpinValue i}
    (hσ : G.pairConstraint.IsAdmissible (Function.update σ i s)) :
    G.pairConstraint.IsAdmissible (Function.update σ i (G.pairConstraint.vacant i)) := by
  intro k l hkl
  by_cases hk : k = i
  · subst hk
    simp only [Function.update_self, Function.update_of_ne hkl.symm]
    exact G.pairConstraint.vacant_compatible _ _ _
  · by_cases hl : l = i
    · subst hl
      simp only [Function.update_self, Function.update_of_ne hk]
      exact G.pairConstraint.compatible_symm _ _ _ _ (G.pairConstraint.vacant_compatible _ _ _)
    · have := hσ k l hkl
      simpa only [Function.update_of_ne hk, Function.update_of_ne hl] using this
end Gas
section Ratios
variable (G : GasGround R n)
def fourConfig (i : G.GasSpin) (σ σ' : G.Config) (s : G.SpinValue i) (a b : Fin 2) : G.Config :=
  Function.update (if b = 1 then σ else σ') i (if a = 1 then s else G.pairConstraint.vacant i)
theorem doubleRatioBound_of_farApart (hr : 1 ≤ R.range) (hL : R.params.side ≤ R.range)
    (hset : ∀ c : G.Config, G.pairConstraint.IsAdmissible c → (G.settingOf (G.familyOf c)).IsAdmissible)
    (hdr : ∀ (s : Fin 2 → Fin 2 → ChartSetting R n) (θ θ' : Finset (TorusSite (n * R.params.side))),
      (∀ i j, (s i j).IsAdmissible) → CompatibleSupports s θ θ' →
      IsFourSettings s (coreBlocks R.params.side R.range θ) (coreBlocks R.params.side R.range θ') →
      (∀ i j, 0 < (s i j).integral) ∧
      ∀ D : ℕ, (∀ y ∈ coreBlocks R.params.side R.range θ, ∀ y' ∈ coreBlocks R.params.side R.range θ',
          D ≤ supDist y y') →
        |Real.log ((s 1 1).integral * (s 0 0).integral / ((s 1 0).integral * (s 0 1).integral))| ≤
          min ((coreBlocks R.params.side R.range θ).card : ℝ) (coreBlocks R.params.side R.range θ').card *
            Real.exp (-(R.params.rt * D / 8)))
    {i j : G.GasSpin} (hij : i ≠ j) (hA : i.1.FarApart j.1) :
    G.pairConstraint.DoubleRatioBound G.weight i j
      ((i.1.core.card : ℝ) * Real.exp (-(R.params.rt * (setGap i.1.core j.1.core : ℝ) / 8))) := by
  classical
  intro σ σ' s hs hs' hd
  set f : ℝ := (i.1.core.card : ℝ) * Real.exp (-(R.params.rt * (setGap i.1.core j.1.core : ℝ) / 8)) with hf
  have hf0 : 0 ≤ f := by positivity
  have hwn : ∀ c : G.Config, 0 ≤ G.weight c := by
    intro c
    unfold GasGround.weight
    split_ifs
    · exact ENNReal.toReal_nonneg
    · exact le_rfl
  have htriv : ∀ (u v : ℝ), 0 ≤ u → 0 ≤ v → u * v ≤ Real.exp f * (u * v) := by
    intro u v hu hv
    have h1 : 1 ≤ Real.exp f := Real.one_le_exp hf0
    have h2 : 0 ≤ u * v := mul_nonneg hu hv
    nlinarith
  by_cases hsame : σ j = σ' j
  · have e : σ = σ' := by
      funext k
      by_cases hk : k = j
      · subst hk
        exact hsame
      · exact hd k hk
    subst e
    exact htriv _ _ (hwn _) (hwn _)
  by_cases hsa : s = G.pairConstraint.vacant i
  · subst hsa
    rw [mul_comm (G.weight (Function.update σ' i _))]
    refine (le_of_eq (mul_comm _ _)).trans ?_
    rw [mul_comm (G.weight (Function.update σ i _))]
    exact htriv _ _ (hwn _) (hwn _)
  set c := fourConfig G i σ σ' s with hc
  have c11 : c 1 1 = Function.update σ i s := by simp [hc, fourConfig]
  have c10 : c 1 0 = Function.update σ' i s := by simp [hc, fourConfig]
  have c01 : c 0 1 = Function.update σ i (G.pairConstraint.vacant i) := by simp [hc, fourConfig]
  have c00 : c 0 0 = Function.update σ' i (G.pairConstraint.vacant i) := by simp [hc, fourConfig]
  have hadm : ∀ a b, G.pairConstraint.IsAdmissible (c a b) := by
    intro a b
    fin_cases a <;> fin_cases b
    · exact c00 ▸ isAdmissible_update_vacant G hs'
    · exact c01 ▸ isAdmissible_update_vacant G hs
    · exact c10 ▸ hs'
    · exact c11 ▸ hs
  set st : Fin 2 → Fin 2 → ChartSetting R n := fun a b => G.settingOf (G.familyOf (c a b)) with hst
  have hsets : ∀ a b, (st a b).IsAdmissible := fun a b => hset _ (hadm a b)
  have hcore : ∀ {k l : G.GasSpin} {y : TorusSite n}, k.1.FarApart l.1 → y ∈ k.1.core → y ∉ l.1.core :=
    fun h h1 h2 => core_disjoint_of_farApart h hL h1 h2
  have hoff : ∀ a b b', ∀ k, k ≠ j → c a b k = c a b' k := by
    intro a b b' k hk
    simp only [hc, fourConfig]
    by_cases hki : k = i
    · subst hki
      simp
    · simp only [Function.update_of_ne hki]
      split_ifs <;> first | rfl | exact hd k hk | exact (hd k hk).symm
  have hoff' : ∀ a a' b, ∀ k, k ≠ i → c a b k = c a' b k := by
    intro a a' b k hk
    simp only [hc, fourConfig, Function.update_of_ne hk]
  have hoff2 : ∀ a b a' b', ∀ k, ¬ (k = i ∨ k = j) → c a b k = c a' b' k := by
    intro a b a' b' k hk
    rw [hoff' a a' b k fun e => hk (Or.inl e), hoff a' b b' k fun e => hk (Or.inr e)]
  have hcompat : CompatibleSupports st i.1.sites j.1.sites := by
    refine ⟨hA, fun a b z hz => ?_⟩
    rcases Finset.mem_union.mp hz with h1 | h1
    · refine Or.inr (Or.inr fun z' hz' => ?_)
      have hat : z ∈ G.anchorSites := Finset.mem_union_right _ h1
      rcases Finset.mem_union.mp hz' with h2 | h2
      · rw [supDist_comm]
        exact i.2.far_from_anchor z' h2 z hat
      · rw [supDist_comm]
        exact j.2.far_from_anchor z' h2 z hat
    · obtain ⟨θ, hθ, hzθ⟩ := mem_sites_iff.mp h1
      have hsup : G.IsGasSupport θ := by
        by_contra hns
        unfold GasFamily.Occupies GasGround.familyOf at hθ
        rw [dif_neg hns] at hθ
        simp at hθ
      set k : G.GasSpin := ⟨θ, hsup⟩ with hk
      by_cases hki : k = i
      · exact Or.inl (hki ▸ mem_sites_of_mem_free k.1 hzθ)
      by_cases hkj : k = j
      · exact Or.inr (Or.inl (hkj ▸ mem_sites_of_mem_free k.1 hzθ))
      have hkp : c a b k ≠ G.pairConstraint.vacant k := by
        intro hca
        unfold GasFamily.Occupies GasGround.familyOf at hθ
        rw [dif_pos hsup] at hθ
        have : c a b ⟨θ, hsup⟩ = Sum.inl () := hca
        rw [this] at hθ
        simp at hθ
      have hval : σ k = c a b k := by
        simp only [hc, fourConfig, Function.update_of_ne hki]
        split_ifs
        · rfl
        · exact hd k hkj
      have hkσ : σ k ≠ G.pairConstraint.vacant k := hval ▸ hkp
      have hki' : k.1.FarApart i.1 := by
        have := hs k i hki
        simp only [Function.update_self, Function.update_of_ne hki] at this
        rcases this with h | h | h
        · exact absurd h hkσ
        · exact absurd h hsa
        · exact h
      have hkj' : k.1.FarApart j.1 := by
        by_cases hj : σ j = G.pairConstraint.vacant j
        · have hj' : σ' j ≠ G.pairConstraint.vacant j := fun e => hsame (hj.trans e.symm)
          have := hs' k j hkj
          simp only [Function.update_of_ne hki, Function.update_of_ne (Ne.symm hij)] at this
          rw [← hd k hkj] at this
          rcases this with h | h | h
          · exact absurd h hkσ
          · exact absurd h hj'
          · exact h
        · have := hs k j hkj
          simp only [Function.update_of_ne hki, Function.update_of_ne (Ne.symm hij)] at this
          rcases this with h | h | h
          · exact absurd h hkσ
          · exact absurd h hj
          · exact h
      refine Or.inr (Or.inr fun z' hz' => ?_)
      have hzs : z ∈ k.1.sites := mem_sites_of_mem_free k.1 hzθ
      rcases Finset.mem_union.mp hz' with h2 | h2
      · exact hki' z hzs z' h2
      · exact hkj' z hzs z' h2
  have hfour : IsFourSettings st (coreBlocks R.params.side R.range i.1.sites)
      (coreBlocks R.params.side R.range j.1.sites) := by
    refine ⟨fun _ _ _ _ => ⟨rfl, rfl⟩, fun a b b' => ?_, fun a a' b => ?_, fun a b a' b' => ?_⟩
    · refine agreeOn_of_spins_eq G hr (fun k => k = j) (fun k hk => hoff a b b' k hk) _ _ ?_ ?_ ?_
      · rintro k rfl b₀ hb₀ hst₀
        exact hcore hA hb₀.1 (Finset.mem_filter.mp hst₀).2.1
      · rintro k rfl z hz₀ hz₁
        exact hcore hA hz₀ (parentBlock_mem_core k.1 (mem_sites_of_mem_free k.1 hz₁))
      · rintro k rfl y hy₀ hy₁
        exact hcore hA hy₀ hy₁
    · refine agreeOn_of_spins_eq G hr (fun k => k = i) (fun k hk => hoff' a a' b k hk) _ _ ?_ ?_ ?_
      · rintro k rfl b₀ hb₀ hst₀
        exact hcore hA (Finset.mem_filter.mp hst₀).2.1 hb₀.1
      · rintro k rfl z hz₀ hz₁
        exact hcore hA (parentBlock_mem_core k.1 (mem_sites_of_mem_free k.1 hz₁)) hz₀
      · rintro k rfl y hy₀ hy₁
        exact hcore hA hy₁ hy₀
    · refine agreeOn_of_spins_eq G hr (fun k => k = i ∨ k = j) (fun k hk => hoff2 a b a' b' k hk) _ _ ?_ ?_ ?_
      · rintro k (rfl | rfl) b₀ hb₀ hst₀
        · exact hb₀.1 (Finset.mem_filter.mp hst₀).2
        · exact hb₀.2 (Finset.mem_filter.mp hst₀).2
      · rintro k (rfl | rfl) z hz₀ hz₁
        · exact (Finset.mem_sdiff.mp hz₀).2
            (Finset.mem_union_left _ (parentBlock_mem_core k.1 (mem_sites_of_mem_free k.1 hz₁)))
        · exact (Finset.mem_sdiff.mp hz₀).2
            (Finset.mem_union_right _ (parentBlock_mem_core k.1 (mem_sites_of_mem_free k.1 hz₁)))
      · rintro k (rfl | rfl) y hy₀ hy₁
        · exact (Finset.mem_sdiff.mp hy₀).2 (Finset.mem_union_left _ hy₁)
        · exact (Finset.mem_sdiff.mp hy₀).2 (Finset.mem_union_right _ hy₁)
  obtain ⟨hpos, hlog⟩ := hdr st i.1.sites j.1.sites hsets hcompat hfour
  have hbound := hlog (setGap i.1.core j.1.core) fun y hy y' hy' => Nat.sInf_le ⟨y, hy, y', hy', rfl⟩
  have hw : ∀ a b, G.weight (c a b) = (st a b).integral := fun a b =>
    weight_eq_integral G (hadm a b) (hpos a b)
  have e11 := hw 1 1
  have e10 := hw 1 0
  have e01 := hw 0 1
  have e00 := hw 0 0
  rw [c11] at e11
  rw [c10] at e10
  rw [c01] at e01
  rw [c00] at e00
  rw [e11, e10, e01, e00]
  have p11 := hpos 1 1
  have p10 := hpos 1 0
  have p01 := hpos 0 1
  have p00 := hpos 0 0
  have hX : 0 < (st 1 1).integral * (st 0 0).integral / ((st 1 0).integral * (st 0 1).integral) :=
    div_pos (mul_pos p11 p00) (mul_pos p10 p01)
  have hlog' : Real.log ((st 1 1).integral * (st 0 0).integral / ((st 1 0).integral * (st 0 1).integral)) ≤ f := by
    refine (le_abs_self _).trans (hbound.trans ?_)
    apply mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.exp_pos _).le
  have hle := (Real.log_le_iff_le_exp hX).mp hlog'
  rw [div_le_iff₀ (mul_pos p10 p01)] at hle
  exact hle
end Ratios
end GasColumns
open GasColumns in
theorem gasColumnsSmall_proof (hw : GasIsActivityBounded) (hs : GasConfigIsAdmissibleSetting)
    (hcl : Dobrushin.ActivityConditionalLawsStatement) (hk : ColumnsOfActivityWithCores)
    (hcount : ClusterSumBound) (hf1 : CouplingFloorExists)
    (hf2 : ColumnFloorExists) (hd : DoubleRatioDecay) :
    GasColumnsSmall := by
  classical
  obtain ⟨a₁, ha₁, hw⟩ := hw
  obtain ⟨a₂, ha₂, hd⟩ := hd
  refine ⟨fun c => min (a₁ c) (a₂ c), fun c => lt_min (ha₁ c) (ha₂ c), fun T hT hrt => ?_⟩
  have hσ := hT.σ_pos
  have hκ := hT.κ_pos
  have hcE := hT.cE_pos
  have hκ₁ : 0 < T.κ₁ := by
    unfold RenormalizationStepParameters.ParameterAssignment.κ₁
    positivity
  have hc : 0 < T.gasRate := by
    unfold RenormalizationStepParameters.ParameterAssignment.gasRate
    positivity
  have hLpos : 0 < T.side := Nat.pos_of_ne_zero (NeZero.ne _)
  obtain ⟨y₁, hw⟩ := hw T hT (hrt.trans (min_le_left _ _))
  obtain ⟨y₂, hd⟩ := hd T hT (hrt.trans (min_le_right _ _))
  obtain ⟨y₃, hs⟩ := hs T hT
  obtain ⟨y₄, hf1⟩ := hf1 T.gasRate T.side T.rt hc
  obtain ⟨y₅, hf2⟩ := hf2 T.gasRate T.rt T.side hc hT.rt_pos hLpos
  refine ⟨max y₁ (max y₂ (max y₃ (max y₄ (max y₅ T.floorMin)))), fun y hy R hR hxx n _ G hG off => ?_⟩
  have b₁ : y₁ ≤ y := (le_max_left _ _).trans hy
  have b₂ : y₂ ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have b₃ : y₃ ≤ y := ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hy
  have b₄ : y₄ ≤ y := ((le_max_left _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _)))).trans hy
  have b₅ : y₅ ≤ y := ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))))).trans hy
  have b₆ : T.floorMin ≤ y := ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))))).trans hy
  have hx := hR.le_coupling
  have eL : R.params.side = T.side := by rw [hR.params_eq]; rfl
  have ert : R.params.rt = T.rt := by rw [hR.params_eq]; rfl
  have en₀ : R.params.n₀ = T.n₀ := by rw [hR.params_eq]; rfl
  have hfit : R.params.Admissible := by rw [hR.params_eq]; exact hT.fits y b₆
  have hcf : R.params.RangeFloor T.gasRate := by
    rw [hR.params_eq]
    exact fun x hx' => hf1 x (b₄.trans hx')
  have hy₁ : R.params.y₁ ≤ R.coupling := by
    rw [hR.params_eq]
    exact hx
  obtain ⟨hLr, -⟩ := hcf R.coupling hy₁
  have hLr' : R.params.side ≤ R.range := hLr
  have hr1 : 1 ≤ R.range := (Nat.pos_of_ne_zero (NeZero.ne R.params.side)).trans_le hLr'
  obtain ⟨hcx, hcol⟩ := hf2 R.coupling (b₅.trans hx)
  have hn₀ : T.n₀ ≤ n := by
    rcases hG with h | h
    · rw [← en₀]
      exact h.n₀_le
    · rw [← en₀]
      obtain ⟨hdvd, hle⟩ := h.isBlockSide
      exact (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (NeZero.ne R.params.side))).trans hle
  have hset := fun c => hs y b₃ R hR hxx n G hG c
  have hdr := hd y b₂ R hR n
  have h := hw y b₁ R hR hxx n G hG off
  have hrt' : 0 < R.params.rt := ert ▸ hT.rt_pos
  have hexp1 : ∀ t : ℝ, 1 ≤ t → Real.exp (-t) ≤ 1 / 2 := by
    intro t ht
    have h1 : Real.exp (-t) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    have h3 : Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1
    have h4 : (Real.exp 1)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) h2
    rw [h3] at h1
    linarith
  have hz : ∀ i : G.GasSpin, G.spinActivity T.gasRate i ≤ 1 / 2 := by
    intro i
    have hu := one_le_supportUnitCount i.2.isCluster
    have hu' : (1 : ℝ) ≤ (supportUnitCount R.params.side R.range i.1 : ℝ) := by exact_mod_cast hu
    refine hexp1 _ ?_
    nlinarith
  have hcore : ∀ i : G.GasSpin, i.1.core.Nonempty := by
    intro i
    obtain ⟨z, hz'⟩ := i.2.isCluster.1
    exact ⟨_, parentBlock_mem_core i.1 hz'⟩
  have hsum : ∀ y' : TorusSite n, ∑ i : G.GasSpin with y' ∈ i.1.core,
      G.spinActivity T.gasRate i * (i.1.core.card : ℝ) ^ 4 *
      Real.exp (2 * R.params.rt * (siteDiameter i.1.core : ℝ)) ≤ Real.exp (-(8 * T.gasRate * R.coupling)) := by
    intro y'
    have hcnt := hcount R.params T.gasRate hfit hc hcf R.coupling hy₁ n y'
    refine le_trans ?_ hcnt
    set F : Finset G.GasSpin := Finset.univ.filter fun i : G.GasSpin => y' ∈ i.1.core with hF
    have hinj : Set.InjOn (Subtype.val : G.GasSpin → GasSupport R n) F := Subtype.val_injective.injOn
    have e1 := Finset.sum_image (f := fun θ : GasSupport R n =>
        clusterWeight R.params.side T.gasRate R.coupling (clusterRange R.coupling) θ *
        ((supportCore R.params.side (clusterRange R.coupling) θ).card : ℝ) ^ 4 *
        Real.exp (2 * R.params.rt * (siteDiameter (supportCore R.params.side (clusterRange R.coupling) θ) : ℝ))) hinj
    refine le_trans (le_of_eq e1.symm) ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun θ _ _ => ?_
    · intro θ hθ
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hθ
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.2.isCluster, (Finset.mem_filter.mp hi).2⟩
    · exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg (Nat.cast_nonneg _) 4)) (Real.exp_pos _).le
  have hnear : ∀ i j : G.GasSpin, G.IsNear i j → setGap i.1.core j.1.core ≤ nearGap R.params.side R.range :=
    fun i j hn => setGap_le_nearGap hn
  have hfar : ∀ i j : G.GasSpin, i ≠ j → ¬ G.IsNear i j → G.pairConstraint.AllCompatible i j ∧
      G.pairConstraint.DoubleRatioBound G.weight i j
      ((i.1.core.card : ℝ) * Real.exp (-(R.params.rt * (setGap i.1.core j.1.core : ℝ) / 8))) := by
    intro i j hij hn
    have hA : i.1.FarApart j.1 := not_not.mp hn
    refine ⟨fun _ _ => Or.inr (Or.inr hA), doubleRatioBound_of_farApart G hr1 hLr' hset ?_ hij hA⟩
    intro s θ θ' h1 h2 h3
    obtain ⟨p1, -, p3⟩ := hdr hn₀ s θ θ' h1 h2 h3
    exact ⟨p1, p3⟩
  obtain ⟨m1, m2, m3⟩ := hk n G.GasSpin G.SpinValue G.pairConstraint (G.referenceMeasureOff off) G.weight
    (G.spinActivity T.gasRate) h (fun i => i.1.core) G.IsNear R.params.rt
    (Real.exp (-(8 * T.gasRate * R.coupling))) (nearGap R.params.side R.range) hrt' hz hcore hsum hnear hfar
  obtain ⟨p1, p2, p3, -⟩ := hcl G.GasSpin G.SpinValue G.pairConstraint (G.referenceMeasureOff off) G.weight
    (G.spinActivity T.gasRate) h
  have hcol' : 8 * columnConstant R.params.rt (nearGap R.params.side R.range) ≤
      Real.exp (2 * T.gasRate * R.coupling) := by
    rw [ert, eL]
    exact hcol
  refine ⟨h, ⟨p1, p2, p3, ?_, ?_, m1, ?_, ?_⟩⟩
  · intro Y F hF hb h0
    refine (m3 Y F hF hb fun σ hσ => h0 σ fun i hi => hσ i (mem_core_of_meets hi)).trans ?_
    rw [Real.exp_le_exp]
    nlinarith
  · intro i j
    have := h.activity_nonneg i
    simp only [GasGround.influenceMatrix, spinInfluence]
    split_ifs
    · positivity
    · refine mul_nonneg (by positivity) (le_min (by norm_num) ?_)
      positivity
  · intro Y j
    refine (m2 Y j).trans ?_
    have hw0 : 0 ≤ G.coreWeightFrom Y j := by
      unfold GasGround.coreWeightFrom coreWeight
      positivity
    change coreWeight (R.params.rt / 2 ^ 6) Y j.1.core * _ ≤ G.coreWeightFrom Y j * _
    apply mul_le_mul_of_nonneg_left _ hw0
    have e : Real.exp (-(6 * T.gasRate * R.coupling)) =
        Real.exp (-(8 * T.gasRate * R.coupling)) * Real.exp (2 * T.gasRate * R.coupling) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [e]
    calc 8 * Real.exp (-(8 * T.gasRate * R.coupling)) * columnConstant R.params.rt (nearGap R.params.side R.range)
        = Real.exp (-(8 * T.gasRate * R.coupling)) *
          (8 * columnConstant R.params.rt (nearGap R.params.side R.range)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcol' (Real.exp_pos _).le
  · refine hexp1 _ ?_
    nlinarith
end YangMills.Construction.ClusterExpansionOfAStep
end
