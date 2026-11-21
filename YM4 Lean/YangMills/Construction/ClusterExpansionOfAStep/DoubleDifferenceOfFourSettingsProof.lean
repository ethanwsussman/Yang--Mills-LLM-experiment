import YangMills.Construction.ClusterExpansionOfAStep.AdmissionReadsVOnItsHullProof
import YangMills.Construction.ClusterExpansionOfAStep.ContoursFromBases
import YangMills.Construction.ClusterExpansionOfAStep.DoubleRatiosOfASettingProof
import YangMills.Construction.ClusterExpansionOfAStep.LocalityOfTheKernel
import YangMills.Construction.ClusterExpansionOfAStep.PotentialsAtFourStates
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open TorusFields TorusLumps StepSettings BlockOffsets TorusBalls StepCosts
namespace MixedDifference
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem agreeOn_of_two {s s' : ChartSetting R n} {B₁ B₂ B : TorusBond (n * R.params.side) → Prop}
    {Q₁ Q₂ Q : Finset (TorusSite n)}
    (h₁ : s.AgreeOn s' B₁ Q₁) (h₂ : s.AgreeOn s' B₂ Q₂) (hB : ∀ b, B b → B₁ b ∨ B₂ b)
    (hQ : ∀ y ∈ Q, y ∈ Q₁ ∨ y ∈ Q₂) : s.AgreeOn s' B Q := by exact _root_.YangMills.Construction.ClusterExpansionOfAStep.HeldBondRatios.agreeOn_of_two h₁ h₂ hB hQ
structure AgreeOnBlocks (s s' : ChartSetting R n) (η : FreeCoords s.free) (η' : FreeCoords s'.free)
    (Q : Finset (TorusSite n)) : Prop where
  agree : s.AgreeOn s' (fun b => parentBlock R.params.side b.1 ∈ Q) Q
  coord_eq : ∀ b, parentBlock R.params.side b.1 ∈ Q → s.freeCoordinate η b = s'.freeCoordinate η' b
  coarse_eq : s.coarse = s'.coarse
theorem settingsAgreeNear_of_agreeOnBlocks {s s' : ChartSetting R n} {η : FreeCoords s.free}
    {η' : FreeCoords s'.free} {Q : Finset (TorusSite n)} (hfit : R.params.Admissible) (hs : s.IsAdmissible)
    (hp : AgreeOnBlocks s s' η η' Q) (Y : TorusSite n) (k : ℕ)
    (hside : 2 * k + 2 < n) (hQ : ∀ h, OffsetInBox k h → Y + siteOfInt h ∈ Q) :
    SettingsAgreeNear s s' Y Y k := by
  have hodd := hfit.L_odd
  have hL1 : 1 ≤ (stepBlockFrame R.params.side n).blockSide := Nat.pos_of_ne_zero (NeZero.ne R.params.side)
  have hp1 : ∀ i, (stepBlockFrame R.params.side n).period 1 i = n := fun i => period_one i
  have hblock : ∀ q : NearBondIndex, IsNearIndex R.params.side k q →
      parentBlock R.params.side (nearBond R.params.side Y q).1 ∈ Q := by
    intro q hq
    show parentBlock R.params.side (fineSite R.params.side Y q.1 q.2.1) ∈ Q
    rw [parentBlock_fineSite hodd Y q.1 q.2.1 hq.2]
    exact hQ _ hq.1
  refine ⟨hside, hside, ?_, fun q hq => hp.agree.free_iff _ (hblock q hq), fun q hq hnot =>
    hp.agree.fine_eq _ (hblock q hq) hnot, fun q _ _ => ?_, fun h o hh ho => ?_, fun h o hz hz' hh ho => ?_,
    fun h hh => ?_⟩
  · intro b _
    rw [hp.coarse_eq]
  · simp only [ChartSetting.frame, hp.coarse_eq]
  · refine hp.agree.support_iff _ ?_
    rw [parentBlock_fineSite hodd Y h o ho]
    exact hQ h hh
  · refine hp.agree.labelling_eq _ hz hz' ?_
    rw [parentBlock_fineSite hodd Y h o ho]
    exact hQ h hh
  · set c := torusSiteInFrame (stepBlockFrame R.params.side n) 1 (Y + siteOfInt h) with hc
    have hcell : toTorusSite n c = Y + siteOfInt h :=
      TopLevelSites.toTorusSite_torusSiteInFrame (F := stepBlockFrame R.params.side n) (j := 1) hp1 _
    obtain ⟨z, hz, e⟩ := TorusContours.exists_centredCube_of_isBaseChoice
      (F := stepBlockFrame R.params.side n) hL1 hs.isBaseChoice c
    have hbl := (TorusContours.parentBlock_siteAtOffset (L := R.params.side) (n := n) c hz).trans hcell
    obtain ⟨o, ho, hx⟩ := exists_fineSite_of_parentBlock hodd (Y + siteOfInt h) _ hbl
    have hfine : fineSite R.params.side (Y + siteOfInt h) 0 o = fineSite R.params.side Y h o := by
      have h1 := siteOfInt_blockPoint (n := n) (NeZero.ne R.params.side) (fun i => ((Y i).cast : ℤ) + h i) o
      rw [siteOfInt_cast_add] at h1
      exact h1.symm
    have hb' : s'.bases c = s.bases c := (hp.agree.bases_eq _ (hQ h hh)).symm
    refine ⟨o, ho, ?_, ?_⟩
    · exact (congrArg (toTorusSite (n * R.params.side)) e).trans (hx.trans hfine)
    · exact (congrArg (toTorusSite (n * R.params.side)) (hb'.trans e)).trans (hx.trans hfine)
theorem coordsByIndex_eq (s : ChartSetting R n) (Y : TorusSite n) (η : FreeCoords s.free) (q : NearBondIndex) :
    s.coordsByIndex Y η q = s.freeCoordinate η (nearBond R.params.side Y q) := rfl
theorem fieldsAgreeNear_of_agreeOnBlocks {s s' : ChartSetting R n} {η : FreeCoords s.free}
    {η' : FreeCoords s'.free} {Q : Finset (TorusSite n)} (hfit : R.params.Admissible) (hs : s.IsAdmissible)
    (hp : AgreeOnBlocks s s' η η' Q) (Y : TorusSite n) (k : ℕ)
    (hk : 1 ≤ k) (hside : 2 * k + 2 < n) (hQ : ∀ h, OffsetInBox k h → Y + siteOfInt h ∈ Q) (o : Fin 4 → ℤ)
    (ho : o ∈ BlockAverages.centredCube R.params.side) :
    FieldsAgreeNear (s.field η) (s'.field η') (fineSite R.params.side Y 0 o) (fineSite R.params.side Y 0 o)
      (R.params.side * k - R.params.side) := by
  have hodd := hfit.L_odd
  have hag := settingsAgreeNear_of_agreeOnBlocks hfit hs hp Y k hside hQ
  refine fieldsAgreeNear_of_settings hodd (by omega) (by omega) hs.subset_chart hag hk le_rfl (fun q hq => ?_) ho
  rw [coordsByIndex_eq, coordsByIndex_eq]
  refine hp.coord_eq _ ?_
  show parentBlock R.params.side (fineSite R.params.side Y q.1 q.2.1) ∈ Q
  rw [parentBlock_fineSite hodd Y q.1 q.2.1 hq.2]
  exact hQ _ hq.1
theorem field_eq_of_agreeOnBlocks {s s' : ChartSetting R n} {η : FreeCoords s.free} {η' : FreeCoords s'.free}
    {Q : Finset (TorusSite n)} (hfit : R.params.Admissible) (hs : s.IsAdmissible) (hp : AgreeOnBlocks s s' η η' Q)
    (x : TorusSite (n * R.params.side)) (i : Fin 4) (hside : 6 < n)
    (hQ : ∀ h, OffsetInBox 2 h → parentBlock R.params.side x + siteOfInt h ∈ Q) :
    s.field η x i = s'.field η' x i := by
  obtain ⟨o, ho, e⟩ := exists_fineSite_of_parentBlock hfit.L_odd (parentBlock R.params.side x) x rfl
  have h := fieldsAgreeNear_of_agreeOnBlocks hfit hs hp (parentBlock R.params.side x) 2 (by norm_num)
    (by omega) hQ o ho
  have hL : 1 ≤ R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hb : BondOffsetInBox (R.params.side * 2 - R.params.side) ((0 : Fin 4 → ℤ), i) := by
    have h1 : R.params.side * 2 - R.params.side = R.params.side := by omega
    rw [h1]
    have hLz : (1 : ℤ) ≤ R.params.side := by exact_mod_cast hL
    refine ⟨fun l => ?_, fun l => ?_⟩
    · show |(0 : ℤ)| ≤ _
      simp
    · show |(((0 : Fin 4 → ℤ) + Pi.single i 1 : Fin 4 → ℤ)) l| ≤ (R.params.side : ℤ)
      by_cases hl : l = i
      · subst hl
        simp only [Pi.add_apply, Pi.zero_apply, Pi.single_eq_same, zero_add, abs_one]
        exact hLz
      · simp only [Pi.add_apply, Pi.zero_apply, Pi.single_eq_of_ne hl, zero_add, abs_zero]
        omega
  have := h _ hb
  simp only [bondFrom] at this
  have e0 : (siteOfInt (0 : Fin 4 → ℤ) : TorusSite (n * R.params.side)) = 0 := by
    funext l
    simp [siteOfInt]
  rw [e0, add_zero, ← e] at this
  exact this
theorem prod_mul_prod_swap_of_agree {ι : Type} [Fintype ι] (f : Fin 2 → Fin 2 → ι → ℝ)
    (h : ∀ c, (∀ i, f i 1 c = f i 0 c) ∨ (∀ j, f 1 j c = f 0 j c)) :
    (∏ c, f 1 1 c) * (∏ c, f 0 0 c) = (∏ c, f 1 0 c) * (∏ c, f 0 1 c) := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun c _ => ?_
  rcases h c with h1 | h1
  · rw [h1 1, h1 0]
  · rw [h1 1, h1 0]
    ring
theorem fieldsAgreeNear_mono {n₁ : ℕ} {W W' : TorusField n₁} {y y' : TorusSite n₁} {m m' : ℕ} (h : m ≤ m')
    (hW : FieldsAgreeNear W W' y y' m') : FieldsAgreeNear W W' y y' m := by
  intro b hb
  refine hW b ⟨fun l => ?_, fun l => ?_⟩
  · exact (hb.1 l).trans (by exact_mod_cast h)
  · exact (hb.2 l).trans (by exact_mod_cast h)
theorem exists_cellCentreOnTorus_eq_fineSite (hfit : R.params.Admissible)
    (y : (stepBlockFrame R.params.side n).Cell) :
    ∃ o ∈ BlockAverages.centredCube R.params.side,
      cellCentreOnTorus R.params.side y = fineSite R.params.side (toTorusSite n y) 0 o := by
  have h0 : (0 : Fin 4 → ℤ) ∈ BlockAverages.centredCube R.params.side := by
    rw [_root_.YangMills.Construction.BlockOffsets.mem_centredCube_iff]
    intro i
    have : 0 ≤ ((R.params.side : ℤ) - 1) / 2 := by
      have : (1 : ℤ) ≤ R.params.side := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne R.params.side)
      omega
    simpa using this
  have hb := TorusContours.parentBlock_siteAtOffset (L := R.params.side) (n := n) y h0
  have e : (siteAtOffset y 0 : (stepBlockFrame R.params.side n).Site 0) = BlockAverages.cellCentre 0 y := by
    rw [siteAtOffset, TorusContours.siteOfCoords_zero, add_zero]
    rfl
  rw [e] at hb
  exact exists_fineSite_of_parentBlock hfit.L_odd (toTorusSite n y) _ hb
theorem bondKernel_eq_of_agreeOnBlocks {s s' : ChartSetting R n} {η : FreeCoords s.free}
    {η' : FreeCoords s'.free} {Q : Finset (TorusSite n)} (hK : BondKernelLocality) (hfit : R.params.Admissible)
    (hJ : 11 * 2 ^ 12 * R.params.baseDepth < R.params.side)
    (hn : 16 ≤ n) (hs : s.IsAdmissible) (hs' : s'.IsAdmissible) (hp : AgreeOnBlocks s s' η η' Q)
    (y : (stepBlockFrame R.params.side n).Cell) (i : Fin 4)
    (hQ : ∀ h, OffsetInBox 5 h → toTorusSite n y + siteOfInt h ∈ Q) :
    bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 (s.field η))
        (readAtLevel (stepBlockFrame R.params.side n) 1 s.coarse) s.bases (y, i) =
      bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 (s'.field η'))
        (readAtLevel (stepBlockFrame R.params.side n) 1 s'.coarse) s'.bases (y, i) := by
  have hp1 : ∀ i, (stepBlockFrame R.params.side n).period 1 i = n := fun i => period_one i
  have hL1 : 1 ≤ (stepBlockFrame R.params.side n).blockSide := Nat.pos_of_ne_zero (NeZero.ne R.params.side)
  set y₂ : (stepBlockFrame R.params.side n).Cell := y + BlockAverages.unitStep 1 i with hy₂
  have hn₂ : toTorusSite n y₂ = toTorusSite n y + TorusFields.unitStep n i := by
    have h1 := TopLevelSites.toTorusSite_add (F := stepBlockFrame R.params.side n) (j := 1) hp1 y
      (BlockAverages.unitStep 1 i)
    have h2 := TopLevelSites.toTorusSite_unitStep (F := stepBlockFrame R.params.side n) (j := 1) (N := n) hp1 i
    rw [h2] at h1
    exact h1
  have hQ₁ : ∀ h, OffsetInBox 4 h → toTorusSite n y + siteOfInt h ∈ Q := fun h hh =>
    hQ h fun l => (hh l).trans (by norm_num)
  have hQ₂ : ∀ h, OffsetInBox 4 h → toTorusSite n y₂ + siteOfInt h ∈ Q := by
    intro h hh
    rw [hn₂, unitStep_eq_siteOfInt, add_assoc, ← siteOfInt_add]
    refine hQ _ fun l => ?_
    have h1 := hh l
    have h2 : |(Pi.single i 1 : Fin 4 → ℤ) l| ≤ 1 := by
      by_cases hl : l = i
      · subst hl
        simp
      · simp [hl]
    have h3 := abs_add_le ((Pi.single i 1 : Fin 4 → ℤ) l) (h l)
    simp only [Pi.add_apply]
    push_cast at h1 ⊢
    omega
  have agree : ∀ (c : (stepBlockFrame R.params.side n).Cell),
      (∀ h, OffsetInBox 4 h → toTorusSite n c + siteOfInt h ∈ Q) →
      FieldsAgreeNear (s.field η) (s'.field η') (cellCentreOnTorus R.params.side c)
        (cellCentreOnTorus R.params.side c) (3 * R.params.side) := by
    intro c hc
    obtain ⟨o, ho, e⟩ := exists_cellCentreOnTorus_eq_fineSite hfit c
    have h := fieldsAgreeNear_of_agreeOnBlocks hfit hs hp (toTorusSite n c) 4 (by norm_num) (by omega) hc o ho
    rw [e]
    have e2 : R.params.side * 4 - R.params.side = 3 * R.params.side := by omega
    rwa [e2] at h
  have hl₁ := hK R.params hfit hJ n n hn hn (s.field η) (s'.field η') y y
  have hl₂ := hK R.params hfit hJ n n hn hn (s.field η) (s'.field η') y₂ y₂
  have hA₁ := agree y hQ₁
  have hA₂ := agree y₂ hQ₂
  have hs₁ := hl₁.2.1 hA₁
  have hs₂ := hl₂.2.1 hA₂
  obtain ⟨z₀, hz₀, e₀⟩ := TorusContours.exists_centredCube_of_isBaseChoice
    (F := stepBlockFrame R.params.side n) hL1 hs.isBaseChoice y
  obtain ⟨z₁, hz₁, e₁⟩ := TorusContours.exists_centredCube_of_isBaseChoice
    (F := stepBlockFrame R.params.side n) hL1 hs.isBaseChoice y₂
  have hb : ∀ c : (stepBlockFrame R.params.side n).Cell, toTorusSite n c ∈ Q → s'.bases c = s.bases c := by
    intro c hc
    have h1 := hp.agree.bases_eq _ hc
    have e3 : torusSiteInFrame (stepBlockFrame R.params.side n) 1 (toTorusSite n c) = c :=
      TopLevelSites.torusSiteInFrame_toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) hp1 c
    rw [show s.bases (torusSiteInFrame (stepBlockFrame R.params.side n) 1 (toTorusSite n c)) = s.bases c from
        congrArg _ e3,
      show s'.bases (torusSiteInFrame (stepBlockFrame R.params.side n) 1 (toTorusSite n c)) = s'.bases c from
        congrArg _ e3] at h1
    exact h1.symm
  have z0 : (siteOfInt (0 : Fin 4 → ℤ) : TorusSite n) = 0 := by
    funext l
    simp [siteOfInt]
  have hin₁ : toTorusSite n y ∈ Q := by
    have := hQ₁ 0 fun l => by simp
    rwa [z0, add_zero] at this
  have hin₂ : toTorusSite n y₂ ∈ Q := by
    have := hQ₂ 0 fun l => by simp
    rwa [z0, add_zero] at this
  have hmain := hl₁.2.2.2 i R.coupling (readAtLevel (stepBlockFrame R.params.side n) 1 s.coarse)
    (readAtLevel (stepBlockFrame R.params.side n) 1 s'.coarse) s.bases s'.bases
    z₀ z₁ hz₀ hz₁ e₀ (by rw [hb y hin₁]; exact e₀) e₁ (by rw [hb y₂ hin₂]; exact e₁)
    (fieldsAgreeNear_mono (by omega) hA₁) hs₁ hs₂
  refine hmain.2 ?_
  rw [hp.coarse_eq]
theorem mem_sitesInBlocks (L : ℕ) [NeZero L] (S : Finset (TorusSite n)) (x : TorusSite (n * L)) :
    x ∈ sitesInBlocks L S ↔ parentBlock L x ∈ S := by apply _root_.YangMills.Construction.CongruentBoxes.mem_sitesInBlocks <;> assumption
theorem card_sitesInBlocks_le (L : ℕ) [NeZero L] (hodd : Odd L) (Q : Finset (TorusSite n)) :
    (sitesInBlocks L Q).card ≤ L ^ 4 * Q.card := by
  classical
  have h1 := Finset.card_le_mul_card_image (s := sitesInBlocks L Q) (f := parentBlock L) (L ^ 4) (by
    intro Y _
    have hsub : (sitesInBlocks L Q).filter (fun x => parentBlock L x = Y) ⊆
        (BlockAverages.centredCube L).image (fineSite L Y 0) := by
      intro x hx
      obtain ⟨o, ho, e⟩ := exists_fineSite_of_parentBlock hodd Y x (Finset.mem_filter.mp hx).2
      exact Finset.mem_image.mpr ⟨o, ho, e.symm⟩
    calc _ ≤ ((BlockAverages.centredCube L).image (fineSite L Y 0)).card := Finset.card_le_card hsub
      _ ≤ (BlockAverages.centredCube L).card := Finset.card_image_le
      _ = L ^ 4 := card_centredCube hodd)
  have h2 : ((sitesInBlocks L Q).image (parentBlock L)).card ≤ Q.card := by
    refine Finset.card_le_card fun Y hY => ?_
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hY
    exact (_root_.YangMills.Construction.ClusterExpansionOfAStep.MixedDifference.mem_sitesInBlocks L Q x).mp hx
  exact h1.trans (Nat.mul_le_mul_left _ h2)
theorem card_thickening_le (m : ℕ) (Q : Finset (TorusSite n)) :
    (thickening m Q).card ≤ (2 * m + 1) ^ 4 * Q.card := by
  classical
  have hsub : thickening m Q ⊆ Q.biUnion fun y => thickening m ({y} : Finset (TorusSite n)) := by
    intro z hz
    obtain ⟨y, hy, hd⟩ := (mem_thickening m Q z).mp hz
    exact Finset.mem_biUnion.mpr ⟨y, hy, (mem_thickening m _ z).mpr ⟨y, by simp, hd⟩⟩
  calc _ ≤ (Q.biUnion fun y => thickening m ({y} : Finset (TorusSite n))).card := Finset.card_le_card hsub
    _ ≤ Q.card * (2 * m + 1) ^ 4 :=
      Finset.card_biUnion_le_card_mul _ _ _ fun y _ => card_thickening_singleton_le m y
    _ = _ := mul_comm _ _
theorem supDist_add_siteOfInt_le_of_box (Y : TorusSite n) (h : Fin 4 → ℤ) (m : ℕ) (hh : OffsetInBox m h) :
    _root_.YangMills.Construction.TorusFields.supDist Y (Y + siteOfInt h) ≤ m := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.supDist_add_le_of_inBox <;> assumption
theorem add_siteOfInt_not_mem_of_far {P P' : Finset (TorusSite n)} {g : ℕ}
    (hfar : ∀ y ∈ P, ∀ y' ∈ P', g ≤ _root_.YangMills.Construction.TorusFields.supDist y y') {Y y : TorusSite n}
    (hy : y ∈ P) {k m : ℕ} (hk : _root_.YangMills.Construction.TorusFields.supDist Y y ≤ k) (hg : k + m < g) {h : Fin 4 → ℤ} (hh : OffsetInBox m h) :
    Y + siteOfInt h ∉ P' := by
  intro hin
  have h1 := hfar y hy _ hin
  have h2 := _root_.YangMills.Construction.TorusFields.supDist_triangle y Y (Y + siteOfInt h)
  have h3 := _root_.YangMills.Construction.ClusterExpansionOfAStep.MixedDifference.supDist_add_siteOfInt_le_of_box Y h m hh
  rw [_root_.YangMills.Construction.TorusFields.supDist_comm y Y] at h2
  omega
def haarFactor (s : ChartSetting R n) (η : FreeCoords s.free) (b : TorusBond (n * R.params.side)) : ℝ :=
  open Classical in
  if b ∈ s.free then ColdStepAtMirrorFrames.haarLogDensity (toCoords (s.frame b) + s.freeCoordinate η b) else 1
theorem haarJacobian_eq_prod (s : ChartSetting R n) (η : FreeCoords s.free) :
    s.haarJacobian η = ∏ b, haarFactor s η b := by
  classical
  have h1 : s.haarJacobian η = ∏ b : s.free,
      ColdStepAtMirrorFrames.haarLogDensity (toCoords (s.frame b.1) + s.freeCoordinate η b.1) := by
    unfold ChartSetting.haarJacobian
    refine Finset.prod_congr rfl fun b _ => ?_
    have : s.freeCoordinate η b.1 = η b := by
      simp [ChartSetting.freeCoordinate]
    rw [this]
  rw [h1, Finset.prod_coe_sort s.free fun b =>
    ColdStepAtMirrorFrames.haarLogDensity (toCoords (s.frame b) + s.freeCoordinate η b)]
  simp only [haarFactor]
  rw [← Finset.prod_filter]
  congr 1
  ext b
  simp
theorem haarFactor_congr {s s' : ChartSetting R n} {η : FreeCoords s.free} {η' : FreeCoords s'.free}
    {b : TorusBond (n * R.params.side)} (hV : s.coarse = s'.coarse) (hf : b ∈ s.free ↔ b ∈ s'.free)
    (hc : s.freeCoordinate η b = s'.freeCoordinate η' b) : haarFactor s η b = haarFactor s' η' b := by
  classical
  have hfr : s.frame b = s'.frame b := by
    simp only [ChartSetting.frame, hV]
  simp only [haarFactor, hf, hc, hfr]
end MixedDifference
open MixedDifference in
theorem mixedDifferenceDecay_of_potential_bound (hpots : potentialMixedDifferenceBound)
    (hK : BondKernelLocality) : MixedDifferenceDecay := by
  intro T hT
  obtain ⟨C, y₀, hC⟩ := hpots T hT
  refine ⟨|C| * (5 * (T.side : ℝ)) ^ 4, max (max y₀ T.floorMin) 1,
    fun y hy R hR hρA hyx hrow n _ hn s η P P' g hset hin hfs hfp hfar hg16 hr hcl => ?_⟩
  have hy1 : y₀ ≤ y := ((le_max_left _ _).trans (le_max_left _ _)).trans hy
  have hy2 : T.floorMin ≤ y := ((le_max_right _ _).trans (le_max_left _ _)).trans hy
  have hy3 : (1 : ℝ) ≤ y := (le_max_right _ _).trans hy
  have hfit : R.params.Admissible := by
    rw [hR]
    exact hT.fits y hy2
  have hLeq : R.params.side = T.side := by
    rw [hR]
    rfl
  have hJ : 11 * 2 ^ 12 * R.params.baseDepth < R.params.side := by
    rw [hR]
    exact hT.L_gt
  have hn16 : 4096 ≤ n := hT.n₀_ge.trans hn
  have hx : 0 < R.coupling := by linarith
  have hL2 : 2 ≤ R.params.side := by
    have := hfit.L_ge
    omega
  have pr : ∀ i j i' j', AgreeOnBlocks (s i j) (s i' j') (η i j) (η i' j') (Finset.univ \ (P ∪ P')) := by
    intro i j i' j'
    have hoff : ∀ b : TorusBond (n * R.params.side), parentBlock R.params.side b.1 ∈ Finset.univ \ (P ∪ P') →
        ¬ BondJoinsBlocks R.params.side P b ∧ ¬ BondJoinsBlocks R.params.side P' b := by
      intro b hb
      have h1 := (Finset.mem_sdiff.mp hb).2
      exact ⟨fun h => h1 (Finset.mem_union_left _ h.1), fun h => h1 (Finset.mem_union_right _ h.1)⟩
    exact ⟨agreeOn_of_two (hfs.rest_agree i j i' j') (hfs.rest_agree i j i' j') (fun b hb => Or.inl (hoff b hb))
      (fun y hy => Or.inl hy), fun b hb => hfp.rest_agree i j i' j' b (hoff b hb).1 (hoff b hb).2,
      (hfs.coarse_eq i j i' j').1⟩
  have p1 : ∀ i j j', AgreeOnBlocks (s i j) (s i j') (η i j) (η i j') (Finset.univ \ P') := by
    intro i j j'
    have hoff : ∀ b : TorusBond (n * R.params.side), parentBlock R.params.side b.1 ∈ Finset.univ \ P' →
        ¬ BondJoinsBlocks R.params.side P' b := by
      intro b hb h
      exact (Finset.mem_sdiff.mp hb).2 h.1
    refine ⟨agreeOn_of_two (hfs.first_agree i j j') (hfs.rest_agree i j i j') (fun b hb => ?_) (fun y hy => ?_),
      fun b hb => ?_, (hfs.coarse_eq i j i j').1⟩
    · by_cases h : BondJoinsBlocks R.params.side P b
      · exact Or.inl h
      · exact Or.inr ⟨h, hoff b hb⟩
    · by_cases h : y ∈ P
      · exact Or.inl h
      · refine Or.inr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h2 => ?_⟩)
        rcases Finset.mem_union.mp h2 with h3 | h3
        · exact h h3
        · exact (Finset.mem_sdiff.mp hy).2 h3
    · by_cases h : BondJoinsBlocks R.params.side P b
      · exact hfp.first_agree i j j' b h
      · exact hfp.rest_agree i j i j' b h (hoff b hb)
  have p2 : ∀ i i' j, AgreeOnBlocks (s i j) (s i' j) (η i j) (η i' j) (Finset.univ \ P) := by
    intro i i' j
    have hoff : ∀ b : TorusBond (n * R.params.side), parentBlock R.params.side b.1 ∈ Finset.univ \ P →
        ¬ BondJoinsBlocks R.params.side P b := by
      intro b hb h
      exact (Finset.mem_sdiff.mp hb).2 h.1
    refine ⟨agreeOn_of_two (hfs.second_agree i i' j) (hfs.rest_agree i j i' j) (fun b hb => ?_) (fun y hy => ?_),
      fun b hb => ?_, (hfs.coarse_eq i j i' j).1⟩
    · by_cases h : BondJoinsBlocks R.params.side P' b
      · exact Or.inl h
      · exact Or.inr ⟨hoff b hb, h⟩
    · by_cases h : y ∈ P'
      · exact Or.inl h
      · refine Or.inr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h2 => ?_⟩)
        rcases Finset.mem_union.mp h2 with h3 | h3
        · exact (Finset.mem_sdiff.mp hy).2 h3
        · exact h h3
    · by_cases h : BondJoinsBlocks R.params.side P' b
      · exact hfp.second_agree i i' j b h
      · exact hfp.rest_agree i j i' j b (hoff b hb) h
  have hfar' : ∀ y ∈ P', ∀ y' ∈ P, g ≤ _root_.YangMills.Construction.TorusFields.supDist y y' := fun y hy y' hy' => by
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
    exact hfar y' hy' y hy
  set Pf := sitesInBlocks R.params.side (thickening 2 P) with hPf
  set Pf' := sitesInBlocks R.params.side (thickening 2 P') with hPf'
  have mem_near : ∀ {Q : Finset (TorusSite n)} {x : TorusSite (n * R.params.side)},
      x ∈ sitesInBlocks R.params.side (thickening 2 Q) →
      ∃ y ∈ Q, _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side x) y ≤ 2 := by
    intro Q x hx
    exact (mem_thickening 2 Q _).mp ((_root_.YangMills.Construction.ClusterExpansionOfAStep.MixedDifference.mem_sitesInBlocks _ _ _).mp hx)
  have not_near : ∀ {Q : Finset (TorusSite n)} {x : TorusSite (n * R.params.side)},
      x ∉ sitesInBlocks R.params.side (thickening 2 Q) →
      ∀ h, OffsetInBox 2 h → parentBlock R.params.side x + siteOfInt h ∉ Q := by
    intro Q x hx h hh hin
    apply hx
    refine (_root_.YangMills.Construction.ClusterExpansionOfAStep.MixedDifference.mem_sitesInBlocks _ _ _).mpr
      ((mem_thickening 2 Q _).mpr ⟨_, hin, _root_.YangMills.Construction.ClusterExpansionOfAStep.MixedDifference.supDist_add_siteOfInt_le_of_box _ h 2 hh⟩)
  have step_near : ∀ {Q : Finset (TorusSite n)} (b : TorusBond (n * R.params.side)),
      (b.1 ∈ sitesInBlocks R.params.side (thickening 2 Q) ∨
        b.1 + TorusFields.unitStep (n * R.params.side) b.2 ∈ sitesInBlocks R.params.side (thickening 2 Q)) →
      ∃ y ∈ Q, _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side b.1) y ≤ 3 := by
    intro Q b hb
    rcases hb with hb | hb
    · obtain ⟨y, hy, hd⟩ := mem_near hb
      exact ⟨y, hy, by omega⟩
    · obtain ⟨y, hy, hd⟩ := mem_near hb
      have h1 := _root_.YangMills.Construction.TorusBalls.supDist_parentBlock_le_div_add_one R.params.side b.1
        (b.1 + TorusFields.unitStep (n * R.params.side) b.2)
      have h2 := _root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le b.1 b.2
      have h3 : _root_.YangMills.Construction.TorusFields.supDist b.1 (b.1 + TorusFields.unitStep (n * R.params.side) b.2) / R.params.side = 0 :=
        Nat.div_eq_of_lt (by omega)
      have h4 := _root_.YangMills.Construction.TorusFields.supDist_triangle (parentBlock R.params.side b.1)
        (parentBlock R.params.side (b.1 + TorusFields.unitStep (n * R.params.side) b.2)) y
      exact ⟨y, hy, by omega⟩
  have fs : FourCornerStates Pf Pf' (fun i j => (s i j).field (η i j)) (fun i j => (s i j).support)
      (fun i j => (s i j).labelling) := by
    refine ⟨fun i j i' j' b h1 _ => ?_, fun i j j' b h => ?_, fun i i' j b h => ?_, fun i j i' j' z h => ?_,
      fun i j j' z h => ?_, fun i i' j z h => ?_, fun i j i' j' z hz hz' h => ?_,
      fun i j j' z hz hz' h => ?_, fun i i' j z hz hz' h => ?_⟩
    · refine field_eq_of_agreeOnBlocks hfit (hset i j) (pr i j i' j') b.1 b.2 (by omega) fun h hh => ?_
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h2 => ?_⟩
      rcases Finset.mem_union.mp h2 with h3 | h3
      · exact not_near (fun hc => h1 (Finset.mem_union_left _ hc)) h hh h3
      · exact not_near (fun hc => h1 (Finset.mem_union_right _ hc)) h hh h3
    · obtain ⟨y, hy, hd⟩ := step_near b h
      refine field_eq_of_agreeOnBlocks hfit (hset i j) (p1 i j j') b.1 b.2 (by omega) fun h' hh => ?_
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, add_siteOfInt_not_mem_of_far hfar hy hd (by omega) hh⟩
    · obtain ⟨y, hy, hd⟩ := step_near b h
      refine field_eq_of_agreeOnBlocks hfit (hset i j) (p2 i i' j) b.1 b.2 (by omega) fun h' hh => ?_
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, add_siteOfInt_not_mem_of_far hfar' hy hd (by omega) hh⟩
    · refine (pr i j i' j').agree.support_iff z (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h2 => ?_⟩)
      have z0 : (siteOfInt (0 : Fin 4 → ℤ) : TorusSite n) = 0 := by
        funext l
        simp [siteOfInt]
      have hb0 : OffsetInBox 2 (0 : Fin 4 → ℤ) := fun l => by simp
      rcases Finset.mem_union.mp h2 with h3 | h3
      · have := not_near (fun hc => h (Finset.mem_union_left _ hc)) 0 hb0
        rw [z0, add_zero] at this
        exact this h3
      · have := not_near (fun hc => h (Finset.mem_union_right _ hc)) 0 hb0
        rw [z0, add_zero] at this
        exact this h3
    · obtain ⟨y, hy, hd⟩ := mem_near h
      refine (p1 i j j').agree.support_iff z (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h2 => ?_⟩)
      have h3 := hfar y hy _ h2
      rw [supDist_comm] at h3
      omega
    · obtain ⟨y, hy, hd⟩ := mem_near h
      refine (p2 i i' j).agree.support_iff z (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h2 => ?_⟩)
      have h3 := hfar' y hy _ h2
      rw [supDist_comm] at h3
      omega
    · refine (pr i j i' j').agree.labelling_eq z hz hz'
        (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h2 => ?_⟩)
      have z0 : (siteOfInt (0 : Fin 4 → ℤ) : TorusSite n) = 0 := by
        funext l
        simp [siteOfInt]
      have hb0 : OffsetInBox 2 (0 : Fin 4 → ℤ) := fun l => by simp
      rcases Finset.mem_union.mp h2 with h3 | h3
      · have := not_near (fun hc => h (Finset.mem_union_left _ hc)) 0 hb0
        rw [z0, add_zero] at this
        exact this h3
      · have := not_near (fun hc => h (Finset.mem_union_right _ hc)) 0 hb0
        rw [z0, add_zero] at this
        exact this h3
    · obtain ⟨y, hy, hd⟩ := mem_near h
      refine (p1 i j j').agree.labelling_eq z hz hz' (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h2 => ?_⟩)
      have h3 := hfar y hy _ h2
      rw [supDist_comm] at h3
      omega
    · obtain ⟨y, hy, hd⟩ := mem_near h
      refine (p2 i i' j).agree.labelling_eq z hz hz' (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h2 => ?_⟩)
      have h3 := hfar' y hy _ h2
      rw [supDist_comm] at h3
      omega
  have hd : ∀ z ∈ Pf, ∀ z' ∈ Pf', R.params.side * (g - 5) ≤ _root_.YangMills.Construction.TorusFields.supDist z z' := by
    intro z hz z' hz'
    obtain ⟨y, hy, hd⟩ := mem_near hz
    obtain ⟨y', hy', hd'⟩ := mem_near hz'
    have h1 := hfar y hy y' hy'
    have h2 := _root_.YangMills.Construction.TorusFields.supDist_triangle y (parentBlock R.params.side z) y'
    have h3 := _root_.YangMills.Construction.TorusFields.supDist_triangle (parentBlock R.params.side z) (parentBlock R.params.side z') y'
    have h4 := _root_.YangMills.Construction.TorusBalls.supDist_parentBlock_le_div_add_one R.params.side z z'
    have e1 := _root_.YangMills.Construction.TorusFields.supDist_comm y (parentBlock R.params.side z)
    have h5 : g - 5 ≤ _root_.YangMills.Construction.TorusFields.supDist z z' / R.params.side := by omega
    calc R.params.side * (g - 5) ≤ R.params.side * (_root_.YangMills.Construction.TorusFields.supDist z z' / R.params.side) := Nat.mul_le_mul_left _ h5
      _ ≤ _root_.YangMills.Construction.TorusFields.supDist z z' := Nat.mul_div_le _ _
  have hk : (s 1 1).kernelProduct (η 1 1) * (s 0 0).kernelProduct (η 0 0) =
      (s 1 0).kernelProduct (η 1 0) * (s 0 1).kernelProduct (η 0 1) := by
    refine prod_mul_prod_swap_of_agree (fun i j c => bondKernel R.params R.coupling
      (readAtLevel (stepBlockFrame R.params.side n) 0 ((s i j).field (η i j)))
      (readAtLevel (stepBlockFrame R.params.side n) 1 (s i j).coarse)
      (s i j).bases c) ?_
    rintro ⟨c, i⟩
    by_cases hc : ∀ h, OffsetInBox 5 h → toTorusSite n c + siteOfInt h ∉ P'
    · left
      intro i₀
      exact bondKernel_eq_of_agreeOnBlocks hK hfit hJ (by omega) (hset i₀ 1) (hset i₀ 0) (p1 i₀ 1 0) c i
        fun h hh => Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hc h hh⟩
    · right
      intro j₀
      push Not at hc
      obtain ⟨h, hh, hin'⟩ := hc
      refine bondKernel_eq_of_agreeOnBlocks hK hfit hJ (by omega) (hset 1 j₀) (hset 0 j₀) (p2 1 0 j₀) c i
        fun h' hh' => Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
      exact add_siteOfInt_not_mem_of_far (k := 5) (m := 5) hfar' hin'
        (_root_.YangMills.Construction.ClusterExpansionOfAStep.MixedDifference.supDist_add_siteOfInt_le_of_box _ h 5 hh) (by omega) hh'
  have hj : (s 1 1).haarJacobian (η 1 1) * (s 0 0).haarJacobian (η 0 0) =
      (s 1 0).haarJacobian (η 1 0) * (s 0 1).haarJacobian (η 0 1) := by
    simp only [haarJacobian_eq_prod]
    refine prod_mul_prod_swap_of_agree (fun i j b => haarFactor (s i j) (η i j) b) fun b => ?_
    by_cases h : BondJoinsBlocks R.params.side P b
    · left
      intro i₀
      exact haarFactor_congr (hfs.coarse_eq i₀ 1 i₀ 0).1 ((hfs.first_agree i₀ 1 0).free_iff b h)
        (hfp.first_agree i₀ 1 0 b h)
    · by_cases h' : BondJoinsBlocks R.params.side P' b
      · right
        intro j₀
        exact haarFactor_congr (hfs.coarse_eq 1 j₀ 0 j₀).1 ((hfs.second_agree 1 0 j₀).free_iff b h')
          (hfp.second_agree 1 0 j₀ b h')
      · left
        intro i₀
        exact haarFactor_congr (hfs.coarse_eq i₀ 1 i₀ 0).1 ((hfs.rest_agree i₀ 1 i₀ 0).free_iff b ⟨h, h'⟩)
          (hfp.rest_agree i₀ 1 i₀ 0 b h h')
  have hmain := hC y hy1 R hR hρA hyx hrow n hn s η Pf Pf' (R.params.side * (g - 5)) hset hin fs hd hr hcl hk hj
  refine hmain.trans ?_
  set E := Real.exp (-(R.params.decayRate * ((R.params.side * (g - 5) : ℕ) : ℝ) / 3)) with hE
  have hcard : ∀ Q : Finset (TorusSite n), ((sitesInBlocks R.params.side (thickening 2 Q)).card : ℝ) ≤
      (5 * (T.side : ℝ)) ^ 4 * Q.card := by
    intro Q
    have h1 := card_sitesInBlocks_le R.params.side hfit.L_odd (thickening 2 Q)
    have h2 := card_thickening_le 2 Q
    have h3 : (sitesInBlocks R.params.side (thickening 2 Q)).card ≤ R.params.side ^ 4 * (5 ^ 4 * Q.card) :=
      h1.trans (Nat.mul_le_mul_left _ h2)
    have h4 : ((sitesInBlocks R.params.side (thickening 2 Q)).card : ℝ) ≤
        (R.params.side : ℝ) ^ 4 * (5 ^ 4 * Q.card) := by
      exact_mod_cast h3
    have hLr : (R.params.side : ℝ) = T.side := congrArg _ hLeq
    refine h4.trans (le_of_eq ?_)
    rw [hLr]
    ring
  have hmin : min (Pf.card : ℝ) Pf'.card ≤ (5 * (T.side : ℝ)) ^ 4 * min (P.card : ℝ) P'.card := by
    rw [mul_min_of_nonneg _ _ (by positivity)]
    exact min_le_min (hcard P) (hcard P')
  calc C * R.coupling * min (Pf.card : ℝ) Pf'.card * E
      ≤ |C| * R.coupling * min (Pf.card : ℝ) Pf'.card * E := by
        have := le_abs_self C
        gcongr
    _ ≤ |C| * R.coupling * ((5 * (T.side : ℝ)) ^ 4 * min (P.card : ℝ) P'.card) * E := by
        gcongr
    _ = |C| * (5 * (T.side : ℝ)) ^ 4 * R.coupling * min (P.card : ℝ) P'.card * E := by ring
end YangMills.Construction.ClusterExpansionOfAStep
end
