import YangMills.Construction.ClusterExpansionOfAStep.ClassesOfTheGas
import YangMills.Construction.ClusterExpansionOfAStep.ImageAtAGroundIsTheSumOverTheGas
import YangMills.Construction.ClusterExpansionOfAStep.ProductOfMaybeMeasures
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace YangMills.Construction
open TorusLumps TorusFields StepGas StepSettings StepCosts
variable {R : StepSetup} {n : ℕ} [NeZero n]
def StepGas.GasGround.IsPairwiseFarApart (G : GasGround R n) (Γ : Finset G.GasSpin) : Prop :=
  ∀ i ∈ Γ, ∀ j ∈ Γ, i ≠ j → i.1.FarApart j.1
open Classical in
def StepGas.GasGround.familyBadBonds (G : GasGround R n) (Γ : Finset G.GasSpin) :
    Finset (TorusBond (n * R.params.side)) :=
  G.recordedBad ∪ Γ.biUnion fun i => i.1.1
open Classical in
def StepGas.GasGround.familySites (G : GasGround R n) (Γ : Finset G.GasSpin) :
    Finset (TorusSite (n * R.params.side)) :=
  G.recordedSites ∪ Γ.biUnion fun i => i.1.2
abbrev SpinFamilies.FamilyState (G : GasGround R n) (Γ : Finset G.GasSpin) : Type :=
  ∀ i : Γ, SupportState i.1.1
open Classical in
def StepGas.GasGround.familyData (G : GasGround R n) {Γ : Finset G.GasSpin}
    (c : SpinFamilies.FamilyState G Γ) : GasFamily R n := fun θ =>
  if h : G.IsGasSupport θ then valuesOn (S := fun i : G.GasSpin => SupportState i.1) Γ c ⟨θ, h⟩ else Sum.inl ()
def StepGas.GasGround.familySetting (G : GasGround R n) {Γ : Finset G.GasSpin}
    (c : SpinFamilies.FamilyState G Γ) : ChartSetting R n :=
  G.settingOf (G.familyData c)
def StepGas.GasGround.overwriteField (G : GasGround R n) {Γ : Finset G.GasSpin}
    (c : SpinFamilies.FamilyState G Γ) (W : TorusField (n * R.params.side)) :
    TorusField (n * R.params.side) := fun x i =>
  match (G.familyData c).fieldAt (x, i) with
  | Sum.inr g => g
  | Sum.inl _ => W x i
open Classical in
def StepGas.GasGround.allowedActivity (G : GasGround R n) (i : G.GasSpin) (s : SupportState i.1) : ℝ≥0∞ :=
  if G.IsAllowed i.1 s then ENNReal.ofReal (G.activity i.1 s) else 0
def SpinFamilies.cellBlock (L n : ℕ) [NeZero L] (c : (stepBlockFrame L n).Cell) : TorusSite n :=
  toTorusSite (F := stepBlockFrame L n) (j := 1) n c
open Classical in
def StepGas.GasGround.basesOfOffsets (G : GasGround R n) (Γ : Finset G.GasSpin)
    (o : ∀ i : Γ, i.1.1.core → BlockOffset R.params.side) : BaseChoice R.params.side n := fun c =>
  if h : ∃ i : Γ, SpinFamilies.cellBlock R.params.side n c ∈ i.1.1.core then
    frameBlockSite R.params.side n (SpinFamilies.cellBlock R.params.side n c) (o h.choose ⟨_, h.choose_spec⟩)
  else G.groundBases c
open Classical in
def StepGas.GasGround.freeBlocks (G : GasGround R n) (Γ : Finset G.GasSpin) : Finset (TorusSite n) :=
  Finset.univ \ (G.cut ∪ coreBlocks R.params.side R.range G.anchorSites ∪ Γ.biUnion fun i => i.1.core)
open Classical in
def StepGas.GasGround.remainingMarks (G : GasGround R n) (free bad : Finset (TorusBond (n * R.params.side)))
    (W : TorusField (n * R.params.side)) : ℝ :=
  ∏ β ∈ markedBonds R G.cut \ free,
    if β ∈ bad then 1 - bondMark R G.coarse W β else bondMark R G.coarse W β
open Classical in
def StepGas.GasGround.restIntegrand (G : GasGround R n) (F : ClusterExpansionOfAStep.CaseFunctional R n)
    (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n)
    (free : Finset (TorusBond (n * R.params.side)))
    (ν : G.state.unlabelled Yt → R.labels.Ω) (W : TorusField (n * R.params.side)) : ℝ≥0∞ :=
  if IsHullState R.params R.range W Yt ∧ coarseStateOf R G.cut W Yt (G.state.fillLabels Yt ν) bad b = G.state then
    F W Yt (G.state.fillLabels Yt ν) bad b *
      ENNReal.ofReal (R.labelWeight (n * R.params.side) W Yt (G.state.fillLabels Yt ν) * baseLaw W b *
        (∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
          bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
            (readAtLevel (stepBlockFrame R.params.side n) 1 G.coarse) b c) *
        G.remainingMarks free bad W)
  else 0
namespace SpinFamilies
variable {G : GasGround R n} {Γ : Finset G.GasSpin}
theorem familyData_self (c : FamilyState G Γ) (i : Γ) : G.familyData c i.1.1 = Sum.inr (c i) := by
  classical
  unfold GasGround.familyData
  rw [dif_pos i.1.2]
  show valuesOn (S := fun i : G.GasSpin => SupportState i.1) Γ c i.1 = _
  unfold valuesOn
  rw [dif_pos i.2]
theorem familyData_of_forall_ne (c : FamilyState G Γ) {θ : GasSupport R n} (h : ∀ i : Γ, i.1.1 ≠ θ) :
    G.familyData c θ = Sum.inl () := by
  classical
  unfold GasGround.familyData
  by_cases hs : G.IsGasSupport θ
  · rw [dif_pos hs]
    unfold valuesOn
    rw [dif_neg fun hm => h ⟨_, hm⟩ rfl]
  · rw [dif_neg hs]
theorem occupies_familyData_iff (c : FamilyState G Γ) {θ : GasSupport R n} :
    (G.familyData c).Occupies θ ↔ ∃ i : Γ, i.1.1 = θ := by
  classical
  constructor
  · intro h
    by_contra hn
    push Not at hn
    unfold GasFamily.Occupies at h
    rw [familyData_of_forall_ne c hn] at h
    simp at h
  · rintro ⟨i, rfl⟩
    unfold GasFamily.Occupies
    rw [familyData_self]
    rfl
theorem coresDisjoint_familyData (hΓ : G.IsPairwiseFarApart Γ) (hr : R.params.side ≤ 2 * R.range)
    (c : FamilyState G Γ) : (G.familyData c).CoresDisjoint := by
  intro θ θ' h h' y hy hy'
  obtain ⟨i, rfl⟩ := (occupies_familyData_iff c).mp h
  obtain ⟨j, rfl⟩ := (occupies_familyData_iff c).mp h'
  by_contra hne
  have hij : i.1 ≠ j.1 := fun e => hne (congrArg Subtype.val e)
  exact (hΓ i.1 i.2 j.1 j.2 hij).false_of_mem_cores hr hy hy'
theorem state_familyData (c : FamilyState G Γ) (i : Γ) (h : (G.familyData c).Occupies i.1.1) :
    (G.familyData c).state h = c i := by
  unfold GasFamily.state
  simp only [familyData_self]
  rfl
theorem fieldAt_familyData {c : FamilyState G Γ} (hs : (G.familyData c).CoresDisjoint) (i : Γ)
    {β : TorusBond (n * R.params.side)} (hb : β ∈ i.1.1.coreBonds) :
    (G.familyData c).fieldAt β = Sum.inr ((c i).1 ⟨β, hb⟩) := by
  classical
  have hi : (G.familyData c).Occupies i.1.1 := (occupies_familyData_iff c).mpr ⟨i, rfl⟩
  have hex : ∃ θ, (G.familyData c).Occupies θ ∧ β ∈ θ.coreBonds := ⟨_, hi, hb⟩
  unfold GasFamily.fieldAt
  rw [dif_pos hex]
  have he : hex.choose = i.1.1 := hs _ _ hex.choose_spec.1 hi _
    (GasSupport.parentBlock_mem_core_of_mem_coreBonds hex.choose_spec.2)
    (GasSupport.parentBlock_mem_core_of_mem_coreBonds hb)
  rw [GasFamily.state_link_congr _ he hex.choose_spec.1 hi hex.choose_spec.2 hb, state_familyData]
theorem fieldAt_familyData_of_forall_not_mem (c : FamilyState G Γ) {β : TorusBond (n * R.params.side)}
    (h : ∀ i : Γ, β ∉ i.1.1.coreBonds) : (G.familyData c).fieldAt β = Sum.inl () := by
  classical
  unfold GasFamily.fieldAt
  rw [dif_neg]
  rintro ⟨θ, hθ, hb⟩
  obtain ⟨i, rfl⟩ := (occupies_familyData_iff c).mp hθ
  exact h i hb
theorem baseAt_familyData {c : FamilyState G Γ} (hs : (G.familyData c).CoresDisjoint) (i : Γ)
    {y : TorusSite n} (hy : y ∈ i.1.1.core) : (G.familyData c).baseAt y = Sum.inr ((c i).2.2 ⟨y, hy⟩) := by
  classical
  have hi : (G.familyData c).Occupies i.1.1 := (occupies_familyData_iff c).mpr ⟨i, rfl⟩
  have hex : ∃ θ, (G.familyData c).Occupies θ ∧ y ∈ θ.core := ⟨_, hi, hy⟩
  unfold GasFamily.baseAt
  rw [dif_pos hex]
  have he : hex.choose = i.1.1 := hs _ _ hex.choose_spec.1 hi _ hex.choose_spec.2 hy
  rw [GasFamily.state_base_congr _ he hex.choose_spec.1 hi hex.choose_spec.2 hy, state_familyData]
theorem baseAt_familyData_of_forall_not_mem (c : FamilyState G Γ) {y : TorusSite n}
    (h : ∀ i : Γ, y ∉ i.1.1.core) : (G.familyData c).baseAt y = Sum.inl () := by
  classical
  unfold GasFamily.baseAt
  rw [dif_neg]
  rintro ⟨θ, hθ, hb⟩
  obtain ⟨i, rfl⟩ := (occupies_familyData_iff c).mp hθ
  exact h i hb
theorem bases_familySetting {c : FamilyState G Γ} (hs : (G.familyData c).CoresDisjoint) :
    (G.familySetting c).bases = G.basesOfOffsets Γ fun i => (c i).2.2 := by
  classical
  funext e
  show (match (G.familyData c).baseAt (cellBlock R.params.side n e) with
    | Sum.inr o => frameBlockSite R.params.side n (cellBlock R.params.side n e) o
    | Sum.inl _ => G.groundBases e) = _
  unfold GasGround.basesOfOffsets
  by_cases h : ∃ i : Γ, cellBlock R.params.side n e ∈ i.1.1.core
  · rw [dif_pos h, baseAt_familyData hs h.choose h.choose_spec]
  · rw [dif_neg h, baseAt_familyData_of_forall_not_mem c fun i hi => h ⟨i, hi⟩]
theorem familyOf_valuesOn (τ : ∀ i : Γ, G.SpinState i.1) :
    G.familyOf (valuesOn Γ τ) = G.familyData fun i => (τ i).1 := by
  classical
  funext θ
  unfold GasGround.familyOf GasGround.familyData
  by_cases hθ : G.IsGasSupport θ
  · simp only [dif_pos hθ]
    unfold valuesOn
    by_cases hm : (⟨θ, hθ⟩ : G.GasSpin) ∈ Γ
    · simp only [dif_pos hm]
    · simp only [dif_neg hm]
  · simp only [dif_neg hθ]
theorem isAdmissible_valuesOn (hΓ : G.IsPairwiseFarApart Γ) (τ : ∀ i : Γ, G.SpinState i.1) :
    G.pairConstraint.IsAdmissible (valuesOn Γ τ) := by
  classical
  intro i j hij
  by_cases hi : i ∈ Γ
  · by_cases hj : j ∈ Γ
    · exact Or.inr (Or.inr (hΓ i hi j hj hij))
    · exact Or.inr (Or.inl (by simp [valuesOn, hj]))
  · exact Or.inl (by simp [valuesOn, hi])
theorem badBondsOf_valuesOn (τ : ∀ i : Γ, G.SpinState i.1) :
    G.badBondsOf (valuesOn Γ τ) = G.familyBadBonds Γ := by
  classical
  unfold GasGround.badBondsOf GasGround.familyBadBonds
  rw [familyOf_valuesOn]
  congr 1
  ext β
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨θ, hθ, hb⟩
    obtain ⟨i, rfl⟩ := (occupies_familyData_iff _).mp hθ
    exact ⟨i.1, i.2, hb⟩
  · rintro ⟨i, hi, hb⟩
    exact ⟨i.1, (occupies_familyData_iff _).mpr ⟨⟨i, hi⟩, rfl⟩, hb⟩
theorem gasIntegrand_valuesOn (hΓ : G.IsPairwiseFarApart Γ) (F : ClusterExpansionOfAStep.CaseFunctional R n)
    (τ : ∀ i : Γ, G.SpinState i.1) :
    G.gasIntegrand F (valuesOn Γ τ) =
      (G.familySetting fun i => (τ i).1).settingIntegral F (G.familyBadBonds Γ) := by
  classical
  unfold GasGround.gasIntegrand
  rw [if_pos (isAdmissible_valuesOn hΓ τ), badBondsOf_valuesOn, familyOf_valuesOn]
  rfl
theorem sites_familyData (c : FamilyState G Γ) : (G.familyData c).sites = Γ.biUnion fun i => i.1.2 := by
  classical
  ext z
  unfold GasFamily.sites
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨θ, hθ, hz⟩
    obtain ⟨i, rfl⟩ := (occupies_familyData_iff c).mp hθ
    exact ⟨i.1, i.2, hz⟩
  · rintro ⟨i, hi, hz⟩
    exact ⟨i.1, (occupies_familyData_iff c).mpr ⟨⟨i, hi⟩, rfl⟩, hz⟩
theorem support_familySetting (c : FamilyState G Γ) : (G.familySetting c).support = G.familySites Γ := by
  show G.recordedSites ∪ (G.familyData c).sites = _
  rw [sites_familyData]
  rfl
end SpinFamilies
end YangMills.Construction
end
