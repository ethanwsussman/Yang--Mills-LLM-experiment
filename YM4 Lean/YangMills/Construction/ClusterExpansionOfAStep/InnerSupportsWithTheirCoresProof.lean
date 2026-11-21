import YangMills.Construction.ClusterExpansionOfAStep.AllowedStatesReadTheirBoxProof
import YangMills.Construction.ClusterExpansionOfAStep.InnerSupportsWithTheirCores
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
open Dobrushin TorusFields TorusLumps StepGas StepSettings RenormalizationStepParameters StepFloors BlockAverages LumpContours
  ColdStepAtMirrorFrames CongruentBoxes CongruentAdmission CongruentStates BoxAgreement BlockOffsets
namespace ClusterExpansionOfAStep
namespace InnerSupports
section Translation
variable {p p' : ℕ} [NeZero p] [NeZero p'] {y : TorusSite p} {y' : TorusSite p'} {M : ℕ}
open Classical in
def boxTranslate (y : TorusSite p) (y' : TorusSite p') (M : ℕ) (z : TorusSite p) : TorusSite p' :=
  if h : ∃ a, OffsetInBox M a ∧ z = y + siteOfInt a then y' + siteOfInt h.choose else 0
theorem boxTranslate_apply (hp : 2 * M + 2 < p) {a : Fin 4 → ℤ} (ha : OffsetInBox M a) :
    boxTranslate y y' M (y + siteOfInt a) = y' + siteOfInt a := by
  have hex : ∃ b, OffsetInBox M b ∧ y + siteOfInt a = y + siteOfInt b := ⟨a, ha, rfl⟩
  unfold boxTranslate
  rw [dif_pos hex]
  have := eq_of_add_siteOfInt_eq hp ha hex.choose_spec.1 hex.choose_spec.2
  rw [← this]
theorem congruentInBoxes_image_boxTranslate (hp : 2 * M + 2 < p) (hp' : 2 * M + 2 < p') {X : Finset (TorusSite p)}
    (hX : ∀ z ∈ X, ∃ a, OffsetInBox M a ∧ z = y + siteOfInt a) :
    CongruentInBoxes X (X.image (boxTranslate y y' M)) y y' M := by
  refine ⟨hX, ?_, fun a ha => ⟨fun h => ?_, fun h => ?_⟩⟩
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hz
    obtain ⟨a, ha, rfl⟩ := hX x hx
    exact ⟨a, ha, boxTranslate_apply hp ha⟩
  · exact Finset.mem_image.2 ⟨_, h, boxTranslate_apply hp ha⟩
  · obtain ⟨x, hx, e⟩ := Finset.mem_image.1 h
    obtain ⟨b, hb, rfl⟩ := hX x hx
    rw [boxTranslate_apply hp hb] at e
    have := eq_of_add_siteOfInt_eq hp' hb ha e
    rwa [this] at hx
theorem mem_image_bond_boxTranslate_iff (hp : 2 * M + 2 < p) (hp' : 2 * M + 2 < p')
    {B : Finset (TorusSite p × Fin 4)}
    (hB : ∀ b ∈ B, ∃ a, OffsetInBox M a ∧ b.1 = y + siteOfInt a) {a : Fin 4 → ℤ} (ha : OffsetInBox M a)
    (i : Fin 4) :
    (y + siteOfInt a, i) ∈ B ↔ (y' + siteOfInt a, i) ∈ B.image fun b => (boxTranslate y y' M b.1, b.2) := by
  constructor
  · intro h
    exact Finset.mem_image.2 ⟨_, h, by simp only [boxTranslate_apply hp ha]⟩
  · intro h
    obtain ⟨b, hb, e⟩ := Finset.mem_image.1 h
    obtain ⟨c, hc, e1⟩ := hB b hb
    have e2 : boxTranslate y y' M b.1 = y' + siteOfInt a := congrArg Prod.fst e
    have e3 : b.2 = i := congrArg Prod.snd e
    rw [e1, boxTranslate_apply hp hc] at e2
    have e4 := eq_of_add_siteOfInt_eq hp' hc ha e2
    have : b = (y + siteOfInt a, i) := Prod.ext (by rw [e1, e4]) e3
    rwa [this] at hb
theorem card_eq_of_congruentInBoxes (hp : 2 * M + 2 < p) (hp' : 2 * M + 2 < p') {A : Finset (TorusSite p)}
    {A' : Finset (TorusSite p')} (h : CongruentInBoxes A A' y y' M) : A.card = A'.card := by
  have e : A' = A.image (boxTranslate y y' M) :=
    eq_of_congruentInBoxes_of_congruentInBoxes h (congruentInBoxes_image_boxTranslate hp hp' h.1)
  rw [e, Finset.card_image_of_injOn]
  intro z hz w hw hzw
  obtain ⟨a, ha, rfl⟩ := h.1 z hz
  obtain ⟨b, hb, rfl⟩ := h.1 w hw
  simp only [boxTranslate_apply hp ha, boxTranslate_apply hp hb] at hzw
  rw [eq_of_add_siteOfInt_eq hp' ha hb hzw]
theorem supDist_self (z : TorusSite p) : TorusFields.supDist z z = 0 := by apply _root_.YangMills.Construction.TorusFields.supDist_self <;> assumption
theorem ballCoverNumber_le_of_congruent (hp : 2 * M + 2 < p) (hp' : 2 * M + 2 < p') {X : Finset (TorusSite p)}
    {X' : Finset (TorusSite p')} {ρ : ℕ} (hS : CongruentInBoxes X X' y y' M) (hd : BallsInBox y M X ρ) :
    ballCoverNumber ρ X' ≤ ballCoverNumber ρ X := by
  classical
  have hne : {k | ∃ C : Finset (TorusSite p), C.card = k ∧ X ⊆ thickening ρ C}.Nonempty :=
    ⟨X.card, X, rfl, fun z hz => (mem_thickening _ _ _).2 ⟨z, hz, by rw [supDist_self]; exact Nat.zero_le _⟩⟩
  obtain ⟨C, hC, hcov⟩ := Nat.sInf_mem hne
  set C₁ := C.filter fun c => ∃ z ∈ X, supDist z c ≤ ρ with hC₁d
  have hC₁ : ∀ c ∈ C₁, ∃ b, OffsetInBox M b ∧ c = y + siteOfInt b := by
    intro c hc
    obtain ⟨z, hz, hzc⟩ := (Finset.mem_filter.1 hc).2
    obtain ⟨a, ha, rfl⟩ := hS.1 z hz
    obtain ⟨e, he, hb⟩ := exists_offset_of_supDist (y + siteOfInt a) c
    refine ⟨a + e, hd a ha hz e fun i => abs_le_natCast_of_natAbs_le ((hb i).trans hzc), ?_⟩
    rw [he, add_siteOfInt_add]
  have hcov' : X' ⊆ thickening ρ (C₁.image (boxTranslate y y' M)) := by
    intro z' hz'
    obtain ⟨a, ha, rfl⟩ := hS.2.1 z' hz'
    have hz := (hS.2.2 a ha).2 hz'
    obtain ⟨c, hc, hd'⟩ := (mem_thickening _ _ _).1 (hcov hz)
    have hc₁ : c ∈ C₁ := Finset.mem_filter.2 ⟨hc, _, hz, hd'⟩
    obtain ⟨b, hb, rfl⟩ := hC₁ c hc₁
    refine (mem_thickening _ _ _).2 ⟨_, Finset.mem_image.2 ⟨_, hc₁, boxTranslate_apply hp hb⟩, ?_⟩
    exact supDist_le_transfer hp (hd a ha hz) hb hd'
  have h1 : ballCoverNumber ρ X' ≤ (C₁.image (boxTranslate y y' M)).card := Nat.sInf_le ⟨_, rfl, hcov'⟩
  have h2 : (C₁.image (boxTranslate y y' M)).card ≤ C.card :=
    Finset.card_image_le.trans (Finset.card_filter_le _ _)
  rw [hC] at h2
  exact h1.trans h2
end Translation
section Refinement
variable {L : ℕ} [NeZero L] {n : ℕ} [NeZero n]
theorem mem_centredCube_iff (L : ℕ) (h : Fin 4 → ℤ) :
    h ∈ centredCube L ↔ ∀ i, -(((L : ℤ) - 1) / 2) ≤ h i ∧ h i ≤ ((L : ℤ) - 1) / 2 := by apply _root_.YangMills.Construction.LumpContours.CutAction.mem_centredCube <;> assumption
theorem fineSite_eq_blockCentre_add (Z : TorusSite n) (h o : Fin 4 → ℤ) :
    (fineSite L Z h o : TorusSite (n * L)) = blockCentre L Z + siteOfInt (fun i => (L : ℤ) * h i + o i) := by
  rw [blockCentre_add_siteOfInt]
  funext i
  simp only [fineSite, siteOfInt]
  push_cast
  ring_nf
theorem exists_block_decomposition (hodd : Odd L) {N : ℕ} {a : Fin 4 → ℤ}
    (ha : OffsetInBox (refinedRadius L N) a) :
    ∃ h o, OffsetInBox N h ∧ o ∈ centredCube L ∧ a = (fun i => (L : ℤ) * h i + o i) ∧ coarseOffset L a = h := by apply _root_.YangMills.Construction.InBoxTransfer.exists_split_of_offsetInBox <;> assumption
theorem offsetInBox_refinedRadius_of_block (hodd : Odd L) {N : ℕ} {h o : Fin 4 → ℤ} (hh : OffsetInBox N h)
    (ho : o ∈ centredCube L) : OffsetInBox (refinedRadius L N) (fun i => (L : ℤ) * h i + o i) := by
  intro i
  have h1 := hh i
  have h2 := (mem_centredCube_iff L o).1 ho i
  have hL := side_pos_int (L := L)
  rw [abs_le] at h1 ⊢
  have hr : ((refinedRadius L N : ℕ) : ℤ) = (L : ℤ) * (N : ℤ) + ((L : ℤ) - 1) / 2 := by
    unfold refinedRadius
    rw [Nat.cast_add, Nat.cast_mul, natCast_half hodd]
  rw [hr]
  have a1 := mul_le_mul_of_nonneg_left h1.2 hL.le
  have a2 := mul_le_mul_of_nonneg_left h1.1 hL.le
  constructor <;> nlinarith [h2.1, h2.2]
end Refinement
section Grounds
variable {R : StepSetup} {n n' : ℕ} [NeZero n] [NeZero n'] {G : GasGround R n} {G' : GasGround R n'}
  {Y : TorusSite n} {Y' : TorusSite n'} {N m : ℕ} {A : Finset (TorusSite n)} {A' : Finset (TorusSite n')}
structure InnerBoxPair (G : GasGround R n) (G' : GasGround R n') (Y : TorusSite n) (Y' : TorusSite n')
    (N m : ℕ) : Prop where
  side_odd : Odd R.params.side
  groundsAgree : GroundsAgreeNear G G' Y Y' N
  gap_eq : m + R.frameReach + 1 = N
  range_le : 16 * R.range ≤ R.params.side * R.frameReach
theorem groundsAgreeNear_symm {M : ℕ} (h : GroundsAgreeNear G G' Y Y' M) : GroundsAgreeNear G' G Y' Y M :=
  ⟨h.lt_extent', h.lt_extent, fun b hb => (h.coarse_agree b hb).symm, fun a ha => (h.cut_iff a ha).symm,
    fun a ha => (h.marking_eq a ha).symm⟩
theorem InnerBoxPair.symm (B : InnerBoxPair G G' Y Y' N m) : InnerBoxPair G' G Y' Y N m :=
  ⟨B.side_odd, groundsAgreeNear_symm B.groundsAgree, B.gap_eq, B.range_le⟩
theorem InnerBoxPair.refinedRadius_lt (B : InnerBoxPair G G' Y Y' N m) :
    2 * refinedRadius R.params.side N + 2 < n * R.params.side :=
  refinedRadius_lt_side B.side_odd B.groundsAgree.lt_extent
theorem InnerBoxPair.refinedRadius_lt' (B : InnerBoxPair G G' Y Y' N m) :
    2 * refinedRadius R.params.side N + 2 < n' * R.params.side :=
  refinedRadius_lt_side B.side_odd B.groundsAgree.lt_extent'
theorem InnerBoxPair.refinedRadius_add_le (B : InnerBoxPair G G' Y Y' N m) :
    refinedRadius R.params.side m + 16 * R.range ≤ refinedRadius R.params.side N := by
  have h := B.range_le
  have e : R.params.side * N = R.params.side * m + R.params.side * R.frameReach + R.params.side := by
    rw [← B.gap_eq]
    ring
  unfold refinedRadius
  omega
theorem InnerBoxPair.two_le (B : InnerBoxPair G G' Y Y' N m) : 2 ≤ n := by
  have := B.groundsAgree.lt_extent
  omega
theorem InnerBoxPair.two_le' (B : InnerBoxPair G G' Y Y' N m) : 2 ≤ n' := by
  have := B.groundsAgree.lt_extent'
  omega
theorem offsetInBox_mono {a b : ℕ} {h : Fin 4 → ℤ} (hab : a ≤ b) (hh : OffsetInBox a h) : OffsetInBox b h := by apply _root_.YangMills.Construction.InBoxTransfer.offsetInBox_mono <;> assumption
theorem mem_gasSupport_sites {θ : GasSupport R n} {z : TorusSite (n * R.params.side)} :
    z ∈ θ.sites ↔ (∃ b ∈ θ.1, b.1 = z) ∨ z ∈ θ.2 := by
  classical
  simp [GasSupport.sites, clusterSupportSites]
theorem exists_offset_of_mem_sites (B : InnerBoxPair G G' Y Y' N m) {θ : GasSupport R n}
    (hc : ∀ y ∈ θ.core, ∃ h, OffsetInBox m h ∧ y = Y + siteOfInt h) {z : TorusSite (n * R.params.side)}
    (hz : z ∈ θ.sites) :
    ∃ a, OffsetInBox (refinedRadius R.params.side m) a ∧ z = blockCentre R.params.side Y + siteOfInt a := by
  obtain ⟨h, hh, e⟩ := hc _ (GasSupport.parentBlock_mem_core hz)
  exact ⟨_, offsetInBox_refinedOffset B.side_odd hh _, eq_blockCentre_add_of_parentBlock e⟩
theorem ballsInBox_of_inner (B : InnerBoxPair G G' Y Y' N m) {S : Finset (TorusSite (n * R.params.side))} {ρ : ℕ}
    (hρ : ρ ≤ 16 * R.range)
    (hS : ∀ z ∈ S, ∃ a, OffsetInBox (refinedRadius R.params.side m) a ∧
      z = blockCentre R.params.side Y + siteOfInt a) :
    BallsInBox (blockCentre R.params.side Y) (refinedRadius R.params.side N) S ρ := by
  intro a ha hz e he i
  obtain ⟨a₀, h0, e0⟩ := hS _ hz
  have hw := B.refinedRadius_add_le
  have hmono : refinedRadius R.params.side m ≤ refinedRadius R.params.side N := by omega
  have : a = a₀ := eq_of_add_siteOfInt_eq B.refinedRadius_lt ha (offsetInBox_mono hmono h0) e0
  subst this
  have h1 := h0 i
  have h2 := he i
  rw [abs_le] at h1 h2 ⊢
  have h3 : ((refinedRadius R.params.side m : ℕ) : ℤ) + ((ρ : ℕ) : ℤ) ≤
      ((refinedRadius R.params.side N : ℕ) : ℤ) := by
    exact_mod_cast (by omega : refinedRadius R.params.side m + ρ ≤ refinedRadius R.params.side N)
  simp only [Pi.add_apply]
  constructor <;> omega
theorem siteOffset_fineSite_eq (Y : TorusSite n) (Y' : TorusSite n') (h o : Fin 4 → ℤ) :
    siteOffset (fineSite R.params.side Y h o : TorusSite (n * R.params.side)) =
      siteOffset (fineSite R.params.side Y' h o : TorusSite (n' * R.params.side)) := by
  rw [siteOffset_fineSite, siteOffset_fineSite]
theorem mem_freeBonds_iff (B : InnerBoxPair G G' Y Y' N m) {a : Fin 4 → ℤ}
    (ha : OffsetInBox (refinedRadius R.params.side N) a) (i : Fin 4) :
    ((blockCentre R.params.side Y + siteOfInt a, i) : TorusBond (n * R.params.side)) ∈ G.freeBonds ↔
      ((blockCentre R.params.side Y' + siteOfInt a, i) : TorusBond (n' * R.params.side)) ∈ G'.freeBonds := by
  classical
  obtain ⟨h, o, hh, ho, rfl, -⟩ := exists_block_decomposition B.side_odd ha
  rw [← fineSite_eq_blockCentre_add, ← fineSite_eq_blockCentre_add]
  have hag := B.groundsAgree
  have hblock := parentBlock_fineSite B.side_odd Y h o ho
  have hblock' := parentBlock_fineSite B.side_odd Y' h o ho
  have hm : ((fineSite R.params.side Y h o, i) : TorusBond (n * R.params.side)) ∈ markedBonds R G.cut ↔
      ((fineSite R.params.side Y' h o, i) : TorusBond (n' * R.params.side)) ∈ markedBonds R G'.cut := by
    unfold markedBonds
    simp only [Finset.mem_filter]
    rw [fineSite_mem_chartBonds_iff B.side_odd B.two_le B.two_le' Y Y' h o ho i, hblock, hblock',
      hag.cut_iff h hh]
  have hs : G.IsRecorded ((fineSite R.params.side Y h o, i) : TorusBond (n * R.params.side)) ↔
      G'.IsRecorded ((fineSite R.params.side Y' h o, i) : TorusBond (n' * R.params.side)) := by
    unfold GasGround.IsRecorded
    simp only
    rw [hblock, hblock', hag.marking_eq h hh, siteOffset_fineSite_eq Y Y' h o]
  unfold GasGround.freeBonds
  simp only [Finset.mem_filter]
  rw [hm, hs]
theorem mem_anchorSites_iff (B : InnerBoxPair G G' Y Y' N m) {a : Fin 4 → ℤ}
    (ha : OffsetInBox (refinedRadius R.params.side N) a) :
    (blockCentre R.params.side Y + siteOfInt a : TorusSite (n * R.params.side)) ∈ G.anchorSites ↔
      (blockCentre R.params.side Y' + siteOfInt a : TorusSite (n' * R.params.side)) ∈ G'.anchorSites := by
  classical
  obtain ⟨h, o, hh, ho, rfl, -⟩ := exists_block_decomposition B.side_odd ha
  rw [← fineSite_eq_blockCentre_add, ← fineSite_eq_blockCentre_add]
  have hag := B.groundsAgree
  have hblock := parentBlock_fineSite B.side_odd Y h o ho
  have hblock' := parentBlock_fineSite B.side_odd Y' h o ho
  have hst := hag.marking_eq h hh
  have hp := siteOffset_fineSite_eq (R := R) Y Y' h o
  have h1 : fineSite R.params.side Y h o ∈ sitesInBlocks R.params.side G.cut ↔
      fineSite R.params.side Y' h o ∈ sitesInBlocks R.params.side G'.cut := by
    rw [mem_sitesInBlocks, mem_sitesInBlocks, hblock, hblock']
    exact hag.cut_iff h hh
  have h2 : fineSite R.params.side Y h o ∈ G.recordedBad.image Prod.fst ↔
      fineSite R.params.side Y' h o ∈ G'.recordedBad.image Prod.fst := by
    simp only [GasGround.recordedBad, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨z, i⟩, ⟨s, e1, e2⟩, e3⟩
      simp only at e1 e2 e3
      subst e3
      exact ⟨(fineSite R.params.side Y' h o, i),
        ⟨s, by rw [hblock', ← hst, ← hblock]; exact e1, by rw [← hp]; exact e2⟩, rfl⟩
    · rintro ⟨⟨z, i⟩, ⟨s, e1, e2⟩, e3⟩
      simp only at e1 e2 e3
      subst e3
      exact ⟨(fineSite R.params.side Y h o, i),
        ⟨s, by rw [hblock, hst, ← hblock']; exact e1, by rw [hp]; exact e2⟩, rfl⟩
  have h3 : fineSite R.params.side Y h o ∈ G.recordedSites ↔ fineSite R.params.side Y' h o ∈ G'.recordedSites := by
    simp only [GasGround.recordedSites, Finset.mem_filter, Finset.mem_univ, true_and]
    have : G.state.labelAt (fineSite R.params.side Y h o) = G'.state.labelAt (fineSite R.params.side Y' h o) := by
      unfold CoarseState.labelAt
      rw [hblock, hblock', hst, hp]
    rw [this]
  unfold GasGround.anchorSites
  simp only [Finset.mem_union]
  rw [h1, h2, h3]
def SupportsCorrespond (θ : GasSupport R n) (θ' : GasSupport R n') (Y : TorusSite n) (Y' : TorusSite n')
    (N : ℕ) : Prop :=
  SameSupportNear θ θ' Y Y' N ∧ ∀ h, OffsetInBox N h → (Y + siteOfInt h ∈ θ.core ↔ Y' + siteOfInt h ∈ θ'.core)
theorem SupportsCorrespond.symm {θ : GasSupport R n} {θ' : GasSupport R n'} (h : SupportsCorrespond θ θ' Y Y' N) :
    SupportsCorrespond θ' θ Y' Y N :=
  ⟨⟨h.1.core_mem', h.1.core_mem, fun q hq => (h.1.bad_iff q hq).symm,
    fun a o ha ho => (h.1.sites_iff a o ha ho).symm⟩, fun a ha => (h.2 a ha).symm⟩
theorem exists_parentBlock_of_congruent (hodd : Odd R.params.side) (hn : 2 * N + 2 < n)
    {W : Finset (TorusSite (n * R.params.side))} {W' : Finset (TorusSite (n' * R.params.side))}
    (hW : CongruentInBoxes W W' (blockCentre R.params.side Y) (blockCentre R.params.side Y')
      (refinedRadius R.params.side N)) {h : Fin 4 → ℤ} (hh : OffsetInBox N h)
    (hx : ∃ x ∈ W, parentBlock R.params.side x = Y + siteOfInt h) :
    ∃ x ∈ W', parentBlock R.params.side x = Y' + siteOfInt h := by
  obtain ⟨x, hx, e⟩ := hx
  obtain ⟨a, ha, rfl⟩ := hW.1 x hx
  rw [parentBlock_blockCentre_add] at e
  have bs : OffsetInBox N (coarseOffset R.params.side a) := (offsetInBox_refinedRadius_iff hodd).mp ha
  have := eq_of_add_siteOfInt_eq hn bs hh e
  exact ⟨_, (hW.2.2 a ha).1 hx, by rw [parentBlock_blockCentre_add, this]⟩
theorem mem_coreBlocks_iff_of_congruent (B : InnerBoxPair G G' Y Y' N m)
    {S : Finset (TorusSite (n * R.params.side))} {S' : Finset (TorusSite (n' * R.params.side))}
    (hS : CongruentInBoxes S S' (blockCentre R.params.side Y) (blockCentre R.params.side Y')
      (refinedRadius R.params.side N))
    (hd : BallsInBox (blockCentre R.params.side Y) (refinedRadius R.params.side N) S (4 * R.range))
    {h : Fin 4 → ℤ} (hh : OffsetInBox N h) :
    Y + siteOfInt h ∈ coreBlocks R.params.side R.range S ↔ Y' + siteOfInt h ∈ coreBlocks R.params.side R.range S' := by
  have hW := congruentInBoxes_thickening B.refinedRadius_lt B.refinedRadius_lt' hS hd
  rw [mem_coreBlocks_iff, mem_coreBlocks_iff]
  exact ⟨exists_parentBlock_of_congruent B.side_odd B.groundsAgree.lt_extent hW hh,
    exists_parentBlock_of_congruent B.side_odd B.groundsAgree.lt_extent' (congruentInBoxes_symm hW) hh⟩
theorem exists_corresponding_spin (B : InnerBoxPair G G' Y Y' N m) (hA : BlockSetsAgreeNear A A' Y Y' N)
    (i : G.GasSpin) (hi : G.IsInnerSpin Y m A i) :
    ∃ i' : G'.GasSpin, G'.IsInnerSpin Y' m A' i' ∧ SupportsCorrespond i.1 i'.1 Y Y' N := by
  classical
  set θ : GasSupport R n := i.1 with hθ
  set y := blockCentre R.params.side Y with hy
  set y' := blockCentre R.params.side Y' with hy'
  set M := refinedRadius R.params.side N with hM
  have hp := B.refinedRadius_lt
  have hp' := B.refinedRadius_lt'
  have hmono : refinedRadius R.params.side m ≤ M := by
    have := B.refinedRadius_add_le
    omega
  have hin := fun z (hz : z ∈ θ.sites) => exists_offset_of_mem_sites B hi.core_near hz
  have hinM : ∀ z ∈ θ.sites, ∃ a, OffsetInBox M a ∧ z = y + siteOfInt a := fun z hz => by
    obtain ⟨a, ha, e⟩ := hin z hz
    exact ⟨a, offsetInBox_mono hmono ha, e⟩
  have h2M : ∀ z ∈ θ.2, ∃ a, OffsetInBox M a ∧ z = y + siteOfInt a := fun z hz =>
    hinM z (mem_gasSupport_sites.2 (Or.inr hz))
  have h1M : ∀ b ∈ θ.1, ∃ a, OffsetInBox M a ∧ b.1 = y + siteOfInt a := fun b hb =>
    hinM b.1 (mem_gasSupport_sites.2 (Or.inl ⟨b, hb, rfl⟩))
  obtain ⟨θ', hθ'⟩ : ∃ θ' : GasSupport R n',
      θ' = (θ.1.image fun b => (boxTranslate y y' M b.1, b.2), θ.2.image (boxTranslate y y' M)) :=
    ⟨_, rfl⟩
  have hsame2 : CongruentInBoxes θ.2 θ'.2 y y' M := by
    rw [hθ']
    exact congruentInBoxes_image_boxTranslate hp hp' h2M
  have hsame1 : ∀ a, OffsetInBox M a → ∀ i₁, ((y + siteOfInt a, i₁) ∈ θ.1 ↔ (y' + siteOfInt a, i₁) ∈ θ'.1) := by
    intro a ha i₁
    rw [hθ']
    exact mem_image_bond_boxTranslate_iff hp hp' h1M ha i₁
  have h1M' : ∀ b ∈ θ'.1, ∃ a, OffsetInBox M a ∧ b.1 = y' + siteOfInt a ∧ (y + siteOfInt a, b.2) ∈ θ.1 := by
    intro b hb
    rw [hθ'] at hb
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hb
    obtain ⟨a, ha, e⟩ := h1M c hc
    refine ⟨a, ha, ?_, ?_⟩
    · simp only [e]
      exact boxTranslate_apply hp ha
    · have : c = (y + siteOfInt a, c.2) := Prod.ext e rfl
      simpa using this ▸ hc
  have hsites : CongruentInBoxes θ.sites θ'.sites y y' M := by
    refine ⟨hinM, ?_, fun a ha => ?_⟩
    · intro z hz
      rcases mem_gasSupport_sites.1 hz with ⟨b, hb, rfl⟩ | hz
      · obtain ⟨a, ha, e, _⟩ := h1M' b hb
        exact ⟨a, ha, e⟩
      · exact hsame2.2.1 z hz
    · rw [mem_gasSupport_sites, mem_gasSupport_sites]
      refine or_congr ⟨?_, ?_⟩ (hsame2.2.2 a ha)
      · rintro ⟨b, hb, e⟩
        have : b = (y + siteOfInt a, b.2) := Prod.ext e rfl
        exact ⟨(y' + siteOfInt a, b.2), (hsame1 a ha b.2).1 (this ▸ hb), rfl⟩
      · rintro ⟨b, hb, e⟩
        have : b = (y' + siteOfInt a, b.2) := Prod.ext e rfl
        exact ⟨(y + siteOfInt a, b.2), (hsame1 a ha b.2).2 (this ▸ hb), rfl⟩
  have hdeep : ∀ ρ, ρ ≤ 16 * R.range → BallsInBox y M θ.sites ρ := fun ρ hρ => ballsInBox_of_inner B hρ hin
  have hcore : ∀ h, OffsetInBox N h → (Y + siteOfInt h ∈ θ.core ↔ Y' + siteOfInt h ∈ θ'.core) := fun h hh =>
    mem_coreBlocks_iff_of_congruent B hsites (hdeep _ (by omega)) hh
  have hW := congruentInBoxes_thickening hp hp' hsites (hdeep (4 * R.range) (by omega))
  have hcore' : ∀ w ∈ θ'.core, ∃ h, OffsetInBox m h ∧ w = Y' + siteOfInt h := by
    intro w hw
    obtain ⟨x', hx', rfl⟩ := mem_coreBlocks_iff.1 hw
    obtain ⟨a, ha, rfl⟩ := hW.2.1 x' hx'
    have hx := (hW.2.2 a ha).2 hx'
    have bs : OffsetInBox N (coarseOffset R.params.side a) := (offsetInBox_refinedRadius_iff B.side_odd).mp ha
    have hc : Y + siteOfInt (coarseOffset R.params.side a) ∈ θ.core := by
      refine mem_coreBlocks_iff.2 ⟨_, hx, ?_⟩
      exact parentBlock_blockCentre_add _ _
    obtain ⟨h₀, h0, e⟩ := hi.core_near _ hc
    have e2 := eq_of_add_siteOfInt_eq B.groundsAgree.lt_extent bs
      (offsetInBox_mono (by have := B.gap_eq; omega) h0) e
    exact ⟨h₀, h0, by rw [parentBlock_blockCentre_add, e2]⟩
  have hsup := i.2
  have hcl : IsClusterSupport R.params.side R.range θ' := by
    refine ⟨?_, fun u hu v hv => ?_⟩
    · obtain ⟨z, hz⟩ := hsup.isCluster.1
      obtain ⟨a, ha, rfl⟩ := hinM z hz
      exact ⟨_, (hsites.2.2 a ha).1 hz⟩
    · obtain ⟨a, ha, rfl⟩ := hsites.2.1 u hu
      obtain ⟨b, hb, rfl⟩ := hsites.2.1 v hv
      have hu' := (hsites.2.2 a ha).2 hu
      have hv' := (hsites.2.2 b hb).2 hv
      exact chainConnected_transfer hp hsites (hdeep _ (by omega)) ha hb hu' (hsup.isCluster.2 _ hu' _ hv')
  have hfree : θ'.1 ⊆ G'.freeBonds := by
    intro b hb
    obtain ⟨a, ha, e, hb'⟩ := h1M' b hb
    have h1 := (mem_freeBonds_iff B ha b.2).1 (hsup.bad_subset_free hb')
    have : b = (y' + siteOfInt a, b.2) := Prod.ext e rfl
    rw [this]
    exact h1
  have happ : ∀ z ∈ θ'.sites, ∀ z' ∈ G'.anchorSites, 10 * R.range < supDist z z' := by
    intro z hz z' hz'
    by_contra hc
    have hle : supDist z z' ≤ 10 * R.range := by omega
    obtain ⟨a, ha, rfl⟩ := hsites.2.1 z hz
    have hzs := (hsites.2.2 a ha).2 hz
    obtain ⟨e, he, hb⟩ := exists_offset_of_supDist (y' + siteOfInt a) z'
    have habs : ∀ l, |e l| ≤ ((10 * R.range : ℕ) : ℤ) := fun l =>
      abs_le_natCast_of_natAbs_le ((hb l).trans hle)
    have hae : OffsetInBox M (a + e) := hdeep (10 * R.range) (by omega) a ha hzs e habs
    have e1 : z' = y' + siteOfInt (a + e) := by rw [he, add_siteOfInt_add]
    have hat := (mem_anchorSites_iff B hae).2 (e1 ▸ hz')
    have h1 := hsup.far_from_anchor _ hzs _ hat
    have h2 : supDist (y + siteOfInt a) (y + siteOfInt (a + e)) ≤ 10 * R.range :=
      supDist_le_of_abs_sub_le fun l => by simpa using habs l
    exact (not_le.2 h1) h2
  refine ⟨⟨θ', ⟨hcl, hfree, happ⟩⟩, ⟨?_, hcore'⟩, ⟨⟨?_, ?_, ?_, ?_⟩, hcore⟩⟩
  · rintro (⟨b, hb, e⟩ | ⟨z, hz, e⟩)
    · obtain ⟨a, ha, e1, hb'⟩ := h1M' b hb
      refine hi.not_touches (Or.inl ⟨_, hb', ?_⟩)
      have bs : OffsetInBox N (coarseOffset R.params.side a) := (offsetInBox_refinedRadius_iff B.side_odd).mp ha
      rw [e1, parentBlock_blockCentre_add] at e
      show parentBlock R.params.side (y + siteOfInt a) ∈ A
      rw [parentBlock_blockCentre_add]
      exact (hA _ bs).2 e
    · obtain ⟨a, ha, rfl⟩ := hsame2.2.1 z hz
      refine hi.not_touches (Or.inr ⟨_, (hsame2.2.2 a ha).2 hz, ?_⟩)
      have bs : OffsetInBox N (coarseOffset R.params.side a) := (offsetInBox_refinedRadius_iff B.side_odd).mp ha
      rw [parentBlock_blockCentre_add] at e ⊢
      exact (hA _ bs).2 e
  · intro w hw
    obtain ⟨h, hh, e⟩ := hi.core_near w hw
    exact ⟨h, offsetInBox_mono (by have := B.gap_eq; omega) hh, e⟩
  · intro w hw
    obtain ⟨h, hh, e⟩ := hcore' w hw
    exact ⟨h, offsetInBox_mono (by have := B.gap_eq; omega) hh, e⟩
  · rintro ⟨h, o, i₁⟩ ⟨hh, ho⟩
    have e1 := fineSite_eq_blockCentre_add (L := R.params.side) Y h o
    have e2 := fineSite_eq_blockCentre_add (L := R.params.side) Y' h o
    simp only [nearBond]
    rw [e1, e2]
    exact hsame1 _ (offsetInBox_refinedRadius_of_block B.side_odd hh ho) i₁
  · intro h o hh ho
    rw [fineSite_eq_blockCentre_add, fineSite_eq_blockCentre_add]
    exact hsame2.2.2 _ (offsetInBox_refinedRadius_of_block B.side_odd hh ho)
section Pairs
variable {θ : GasSupport R n} {θ' : GasSupport R n'}
theorem mem_bonds_iff (B : InnerBoxPair G G' Y Y' N m) (h : SupportsCorrespond θ θ' Y Y' N) {a : Fin 4 → ℤ}
    (ha : OffsetInBox (refinedRadius R.params.side N) a) (i : Fin 4) :
    ((blockCentre R.params.side Y + siteOfInt a, i) : TorusBond (n * R.params.side)) ∈ θ.1 ↔
      ((blockCentre R.params.side Y' + siteOfInt a, i) : TorusBond (n' * R.params.side)) ∈ θ'.1 := by
  obtain ⟨c, o, hc, ho, rfl, -⟩ := exists_block_decomposition B.side_odd ha
  rw [← fineSite_eq_blockCentre_add, ← fineSite_eq_blockCentre_add]
  exact h.1.bad_iff (c, o, i) ⟨hc, ho⟩
theorem mem_extra_iff (B : InnerBoxPair G G' Y Y' N m) (h : SupportsCorrespond θ θ' Y Y' N) {a : Fin 4 → ℤ}
    (ha : OffsetInBox (refinedRadius R.params.side N) a) :
    (blockCentre R.params.side Y + siteOfInt a : TorusSite (n * R.params.side)) ∈ θ.2 ↔
      (blockCentre R.params.side Y' + siteOfInt a : TorusSite (n' * R.params.side)) ∈ θ'.2 := by
  obtain ⟨c, o, hc, ho, rfl, -⟩ := exists_block_decomposition B.side_odd ha
  rw [← fineSite_eq_blockCentre_add, ← fineSite_eq_blockCentre_add]
  exact h.1.sites_iff c o hc ho
theorem exists_outer_offset_of_mem_sites (B : InnerBoxPair G G' Y Y' N m)
    (hc : ∀ y ∈ θ.core, ∃ h, OffsetInBox m h ∧ y = Y + siteOfInt h)
    {z : TorusSite (n * R.params.side)} (hz : z ∈ θ.sites) :
    ∃ a, OffsetInBox (refinedRadius R.params.side N) a ∧ z = blockCentre R.params.side Y + siteOfInt a := by
  obtain ⟨a, ha, e⟩ := exists_offset_of_mem_sites B hc hz
  have := B.refinedRadius_add_le
  exact ⟨a, offsetInBox_mono (by omega) ha, e⟩
theorem congruent_extraSites (B : InnerBoxPair G G' Y Y' N m) (h : SupportsCorrespond θ θ' Y Y' N)
    (hc : ∀ y ∈ θ.core, ∃ h, OffsetInBox m h ∧ y = Y + siteOfInt h)
    (hc' : ∀ y ∈ θ'.core, ∃ h, OffsetInBox m h ∧ y = Y' + siteOfInt h) :
    CongruentInBoxes θ.2 θ'.2 (blockCentre R.params.side Y) (blockCentre R.params.side Y')
      (refinedRadius R.params.side N) :=
  ⟨fun z hz => exists_outer_offset_of_mem_sites B hc (mem_gasSupport_sites.2 (Or.inr hz)),
    fun z hz => exists_outer_offset_of_mem_sites B.symm hc' (mem_gasSupport_sites.2 (Or.inr hz)),
    fun a ha => mem_extra_iff B h ha⟩
theorem congruent_sites (B : InnerBoxPair G G' Y Y' N m) (h : SupportsCorrespond θ θ' Y Y' N)
    (hc : ∀ y ∈ θ.core, ∃ h, OffsetInBox m h ∧ y = Y + siteOfInt h)
    (hc' : ∀ y ∈ θ'.core, ∃ h, OffsetInBox m h ∧ y = Y' + siteOfInt h) :
    CongruentInBoxes θ.sites θ'.sites (blockCentre R.params.side Y) (blockCentre R.params.side Y')
      (refinedRadius R.params.side N) := by
  refine ⟨fun z hz => exists_outer_offset_of_mem_sites B hc hz,
    fun z hz => exists_outer_offset_of_mem_sites B.symm hc' hz, fun a ha => ?_⟩
  rw [mem_gasSupport_sites, mem_gasSupport_sites]
  refine or_congr ⟨?_, ?_⟩ (mem_extra_iff B h ha)
  · rintro ⟨b, hb, e⟩
    have : b = (blockCentre R.params.side Y + siteOfInt a, b.2) := Prod.ext e rfl
    exact ⟨(blockCentre R.params.side Y' + siteOfInt a, b.2), (mem_bonds_iff B h ha b.2).1 (this ▸ hb), rfl⟩
  · rintro ⟨b, hb, e⟩
    have : b = (blockCentre R.params.side Y' + siteOfInt a, b.2) := Prod.ext e rfl
    exact ⟨(blockCentre R.params.side Y + siteOfInt a, b.2), (mem_bonds_iff B h ha b.2).2 (this ▸ hb), rfl⟩
theorem SupportsCorrespond.meets (B : InnerBoxPair G G' Y Y' N m) (h : SupportsCorrespond θ θ' Y Y' N)
    (hc : ∀ y ∈ θ.core, ∃ h, OffsetInBox m h ∧ y = Y + siteOfInt h) (hm : θ.Meets Y) : θ'.Meets Y' := by
  have zero_of : ∀ {a : Fin 4 → ℤ}, OffsetInBox (refinedRadius R.params.side N) a →
      Y + siteOfInt (coarseOffset R.params.side a) = Y → coarseOffset R.params.side a = 0 := by
    intro a ha e
    refine eq_of_add_siteOfInt_eq (y := Y) B.groundsAgree.lt_extent
      ((offsetInBox_refinedRadius_iff B.side_odd).mp ha) (fun i => by simp) ?_
    rw [e, siteOfInt_zero_offset, add_zero]
  rcases hm with ⟨b, hb, e⟩ | ⟨z, hz, e⟩
  · obtain ⟨a, ha, e1⟩ := exists_outer_offset_of_mem_sites B hc (mem_gasSupport_sites.2 (Or.inl ⟨b, hb, rfl⟩))
    rw [e1, parentBlock_blockCentre_add] at e
    have hz := zero_of ha e
    have hb' : b = (blockCentre R.params.side Y + siteOfInt a, b.2) := Prod.ext e1 rfl
    refine Or.inl ⟨_, (mem_bonds_iff B h ha b.2).1 (hb' ▸ hb), ?_⟩
    show parentBlock R.params.side (blockCentre R.params.side Y' + siteOfInt a) = Y'
    rw [parentBlock_blockCentre_add, hz, siteOfInt_zero_offset, add_zero]
  · obtain ⟨a, ha, rfl⟩ := exists_outer_offset_of_mem_sites B hc (mem_gasSupport_sites.2 (Or.inr hz))
    rw [parentBlock_blockCentre_add] at e
    have h0 := zero_of ha e
    refine Or.inr ⟨_, (mem_extra_iff B h ha).1 hz, ?_⟩
    rw [parentBlock_blockCentre_add, h0, siteOfInt_zero_offset, add_zero]
theorem congruent_badBlocks (B : InnerBoxPair G G' Y Y' N m) (h : SupportsCorrespond θ θ' Y Y' N)
    (hc : ∀ y ∈ θ.core, ∃ h, OffsetInBox m h ∧ y = Y + siteOfInt h)
    (hc' : ∀ y ∈ θ'.core, ∃ h, OffsetInBox m h ∧ y = Y' + siteOfInt h) :
    CongruentInBoxes (open Classical in θ.1.image fun b => parentBlock R.params.side b.1)
      (open Classical in θ'.1.image fun b => parentBlock R.params.side b.1) Y Y' N := by
  classical
  have fwd : ∀ {k k' : ℕ} [NeZero k] [NeZero k'] {H : GasGround R k} {H' : GasGround R k'} {Z : TorusSite k}
      {Z' : TorusSite k'} {ϑ : GasSupport R k} {ϑ' : GasSupport R k'}, InnerBoxPair H H' Z Z' N m →
      SupportsCorrespond ϑ ϑ' Z Z' N → (∀ y ∈ ϑ.core, ∃ h, OffsetInBox m h ∧ y = Z + siteOfInt h) →
      ∀ {c : Fin 4 → ℤ}, OffsetInBox N c →
      Z + siteOfInt c ∈ ϑ.1.image (fun b => parentBlock R.params.side b.1) →
      Z' + siteOfInt c ∈ ϑ'.1.image (fun b => parentBlock R.params.side b.1) := by
    intro k k' _ _ H H' Z Z' ϑ ϑ' B h hc c hcb hm
    obtain ⟨b, hb, e⟩ := Finset.mem_image.1 hm
    obtain ⟨a, ha, e1⟩ := exists_outer_offset_of_mem_sites B hc (mem_gasSupport_sites.2 (Or.inl ⟨b, hb, rfl⟩))
    have e2 := e
    simp only [e1, parentBlock_blockCentre_add] at e2
    have bs := (offsetInBox_refinedRadius_iff B.side_odd).mp ha
    have e3 := eq_of_add_siteOfInt_eq B.groundsAgree.lt_extent bs hcb e2
    have hb' : b = (blockCentre R.params.side Z + siteOfInt a, b.2) := Prod.ext e1 rfl
    refine Finset.mem_image.2 ⟨_, (mem_bonds_iff B h ha b.2).1 (hb' ▸ hb), ?_⟩
    simp only [parentBlock_blockCentre_add, e3]
  have inb : ∀ {k : ℕ} [NeZero k] {Z : TorusSite k} {ϑ : GasSupport R k},
      (∀ y ∈ ϑ.core, ∃ h, OffsetInBox m h ∧ y = Z + siteOfInt h) →
      ∀ z ∈ ϑ.1.image (fun b => parentBlock R.params.side b.1), ∃ a, OffsetInBox N a ∧ z = Z + siteOfInt a := by
    intro k _ Z ϑ hc z hz
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hz
    obtain ⟨a, ha, e⟩ := hc _ (GasSupport.parentBlock_mem_core (mem_gasSupport_sites.2 (Or.inl ⟨b, hb, rfl⟩)))
    exact ⟨a, offsetInBox_mono (by have := B.gap_eq; omega) ha, e⟩
  exact ⟨inb hc, inb hc', fun a ha => ⟨fwd B h hc ha, fwd B.symm h.symm hc' ha⟩⟩
theorem supportUnitCount_eq (B : InnerBoxPair G G' Y Y' N m) (h : SupportsCorrespond θ θ' Y Y' N)
    (hc : ∀ y ∈ θ.core, ∃ h, OffsetInBox m h ∧ y = Y + siteOfInt h)
    (hc' : ∀ y ∈ θ'.core, ∃ h, OffsetInBox m h ∧ y = Y' + siteOfInt h) :
    supportUnitCount R.params.side R.range θ = supportUnitCount R.params.side R.range θ' := by
  have h1 : badBlockCount R.params.side θ = badBlockCount R.params.side θ' :=
    card_eq_of_congruentInBoxes B.groundsAgree.lt_extent B.groundsAgree.lt_extent' (congruent_badBlocks B h hc hc')
  have hs := congruent_extraSites B h hc hc'
  have d1 : BallsInBox (blockCentre R.params.side Y) (refinedRadius R.params.side N) θ.2 (4 * R.range) :=
    ballsInBox_of_inner B (by omega) fun z hz => exists_offset_of_mem_sites B hc (mem_gasSupport_sites.2 (Or.inr hz))
  have d2 : BallsInBox (blockCentre R.params.side Y') (refinedRadius R.params.side N) θ'.2 (4 * R.range) :=
    d1.of_congruent hs
  have h2 : ballCoverNumber (4 * R.range) θ.2 = ballCoverNumber (4 * R.range) θ'.2 :=
    le_antisymm (ballCoverNumber_le_of_congruent B.refinedRadius_lt' B.refinedRadius_lt (congruentInBoxes_symm hs) d2)
      (ballCoverNumber_le_of_congruent B.refinedRadius_lt B.refinedRadius_lt' hs d1)
  unfold supportUnitCount
  rw [h1, h2]
theorem GasSupport.FarApart.of_correspond (B : InnerBoxPair G G' Y Y' N m) {θ₂ : GasSupport R n}
    {θ₂' : GasSupport R n'} (h₁ : SupportsCorrespond θ θ' Y Y' N) (h₂ : SupportsCorrespond θ₂ θ₂' Y Y' N)
    (c₁ : ∀ y ∈ θ.core, ∃ h, OffsetInBox m h ∧ y = Y + siteOfInt h)
    (c₁' : ∀ y ∈ θ'.core, ∃ h, OffsetInBox m h ∧ y = Y' + siteOfInt h)
    (c₂ : ∀ y ∈ θ₂.core, ∃ h, OffsetInBox m h ∧ y = Y + siteOfInt h)
    (c₂' : ∀ y ∈ θ₂'.core, ∃ h, OffsetInBox m h ∧ y = Y' + siteOfInt h)
    (ha : θ.FarApart θ₂) : θ'.FarApart θ₂' := by
  intro z hz w hw
  by_contra hc
  have hle : supDist z w ≤ 10 * R.range := by omega
  have s₁ := congruent_sites B h₁ c₁ c₁'
  have s₂ := congruent_sites B h₂ c₂ c₂'
  obtain ⟨a, haM, rfl⟩ := s₁.2.1 z hz
  obtain ⟨b, hbM, rfl⟩ := s₂.2.1 w hw
  have d : BallsInBox (blockCentre R.params.side Y') (refinedRadius R.params.side N) θ'.sites (10 * R.range) :=
    ballsInBox_of_inner B.symm (by omega) fun z hz => exists_offset_of_mem_sites B.symm c₁' hz
  have := supDist_le_transfer (y' := blockCentre R.params.side Y) B.refinedRadius_lt' (d a haM hz) hbM hle
  have h3 := ha _ ((s₁.2.2 a haM).2 hz) _ ((s₂.2.2 b hbM).2 hw)
  exact (not_le.2 h3) this
theorem SupportsCorrespond.unique (B : InnerBoxPair G G' Y Y' N m) {θ'' : GasSupport R n'}
    (h₁ : SupportsCorrespond θ θ' Y Y' N) (h₂ : SupportsCorrespond θ θ'' Y Y' N)
    (c' : ∀ y ∈ θ'.core, ∃ h, OffsetInBox m h ∧ y = Y' + siteOfInt h)
    (c'' : ∀ y ∈ θ''.core, ∃ h, OffsetInBox m h ∧ y = Y' + siteOfInt h) :
    θ' = θ'' := by
  have key : ∀ {ϑ ϑ' : GasSupport R n'}, SupportsCorrespond θ ϑ Y Y' N → SupportsCorrespond θ ϑ' Y Y' N →
      (∀ y ∈ ϑ.core, ∃ h, OffsetInBox m h ∧ y = Y' + siteOfInt h) → ϑ.1 ⊆ ϑ'.1 ∧ ϑ.2 ⊆ ϑ'.2 := by
    intro ϑ ϑ' r r' c
    refine ⟨fun b hb => ?_, fun z hz => ?_⟩
    · obtain ⟨a, ha, e⟩ := exists_outer_offset_of_mem_sites B.symm c (mem_gasSupport_sites.2 (Or.inl ⟨b, hb, rfl⟩))
      have hb' : b = (blockCentre R.params.side Y' + siteOfInt a, b.2) := Prod.ext e rfl
      rw [hb'] at hb ⊢
      exact (mem_bonds_iff B r' ha _).1 ((mem_bonds_iff B r ha _).2 hb)
    · obtain ⟨a, ha, rfl⟩ := exists_outer_offset_of_mem_sites B.symm c (mem_gasSupport_sites.2 (Or.inr hz))
      exact (mem_extra_iff B r' ha).1 ((mem_extra_iff B r ha).2 hz)
  exact Prod.ext (Finset.Subset.antisymm (key h₁ h₂ c').1 (key h₂ h₁ c'').1)
    (Finset.Subset.antisymm (key h₁ h₂ c').2 (key h₂ h₁ c'').2)
end Pairs
end Grounds
theorem exists_equiv_of_bijective_relation {α β : Type} {P : α → Prop} {Q : β → Prop} (Rl : α → β → Prop)
    (h1 : ∀ a, P a → ∃ b, Q b ∧ Rl a b) (h2 : ∀ b, Q b → ∃ a, P a ∧ Rl a b)
    (u1 : ∀ a b b', P a → Q b → Q b' → Rl a b → Rl a b' → b = b')
    (u2 : ∀ a a' b, P a → P a' → Q b → Rl a b → Rl a' b → a = a') :
    ∃ e : {a // P a} ≃ {b // Q b}, ∀ a, Rl a.1 (e a).1 := by
  choose f hf using h1
  choose g hg using h2
  refine ⟨{ toFun := fun a => ⟨f a.1 a.2, (hf a.1 a.2).1⟩
            invFun := fun b => ⟨g b.1 b.2, (hg b.1 b.2).1⟩
            left_inv := fun a => ?_
            right_inv := fun b => ?_ }, fun a => (hf a.1 a.2).2⟩
  · exact Subtype.ext (u2 _ _ _ (hg _ _).1 a.2 (hf a.1 a.2).1 (hg _ _).2 (hf a.1 a.2).2)
  · exact Subtype.ext (u1 _ _ _ (hg b.1 b.2).1 (hf _ _).1 b.2 (hf _ _).2 (hg b.1 b.2).2)
end InnerSupports
open InnerSupports in
theorem innerSupportsCorrespondWithCores_of_floors (hFl : EventuallyFloorConditions) :
    InnerSupportsCorrespondWithCores := by
  classical
  intro T hT
  obtain ⟨y₁, hy₁⟩ := hFl T hT (2 ^ 12) 1 (by norm_num) one_pos
  refine ⟨max y₁ T.floorMin, fun y hy R hR n n' _ _ G G' Y Y' N A A' hN hag hbl => ?_⟩
  obtain ⟨a₁, a₂⟩ := max_le_iff.mp hy
  have hfit : R.params.Admissible := by
    rw [hR.params_eq]
    exact hT.fits y a₂
  have hr : 2 ^ 12 ≤ R.range := by
    have := (hy₁ R.coupling (a₁.trans hR.le_coupling)).range_ge
    show 2 ^ 12 ≤ clusterRange R.coupling
    exact_mod_cast this
  have hL := hfit.L_ge
  have hm₀ : R.frameReach = R.range / 2 ^ 11 := rfl
  have hm2 : 2 ≤ R.frameReach := by
    rw [hm₀]
    omega
  have hbig : 16 * R.range ≤ R.params.side * R.frameReach := by
    have h1 : R.range < 2 ^ 11 * (R.frameReach + 1) := by
      rw [hm₀]
      omega
    calc 16 * R.range ≤ 2 ^ 16 * R.frameReach := by omega
      _ ≤ R.params.side * R.frameReach := Nat.mul_le_mul_right _ hL
  set m := N - R.frameReach - 1 with hm
  have B : InnerBoxPair G G' Y Y' N m := ⟨hfit.L_odd, hag, by omega, hbig⟩
  have hbl' : BlockSetsAgreeNear A' A Y' Y N := fun a ha => (hbl a ha).symm
  obtain ⟨e, he⟩ := exists_equiv_of_bijective_relation (P := G.IsInnerSpin Y m A) (Q := G'.IsInnerSpin Y' m A')
    (fun i i' => SupportsCorrespond i.1 i'.1 Y Y' N)
    (fun i hi => exists_corresponding_spin B hbl i hi)
    (fun i' hi => by
      obtain ⟨i, h1, h2⟩ := exists_corresponding_spin B.symm hbl' i' hi
      exact ⟨i, h1, h2.symm⟩)
    (fun i i' i'' _ h1 h2 r r' => Subtype.ext (SupportsCorrespond.unique B r r' h1.core_near h2.core_near))
    (fun i i₂ i' h1 h2 _ r r' =>
      Subtype.ext (SupportsCorrespond.unique B.symm r.symm r'.symm h1.core_near h2.core_near))
  refine ⟨e, fun j => ⟨(he j).1, (he j).2, ?_, ?_, fun j' _ => ?_⟩⟩
  · exact ⟨SupportsCorrespond.meets B (he j) j.2.core_near,
      SupportsCorrespond.meets B.symm (he j).symm (e j).2.core_near⟩
  · exact supportUnitCount_eq B (he j) j.2.core_near (e j).2.core_near
  · exact ⟨GasSupport.FarApart.of_correspond B (he j) (he j') j.2.core_near (e j).2.core_near j'.2.core_near
        (e j').2.core_near,
      GasSupport.FarApart.of_correspond B.symm (he j).symm (he j').symm (e j).2.core_near j.2.core_near
        (e j').2.core_near j'.2.core_near⟩
end ClusterExpansionOfAStep
end YangMills.Construction
end
