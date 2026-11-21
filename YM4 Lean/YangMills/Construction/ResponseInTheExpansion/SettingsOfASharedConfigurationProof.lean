import YangMills.Construction.ClusterExpansionOfAStep.AllowedStatesReadTheirBoxProof
import YangMills.Construction.ClusterExpansionOfAStep.CountFloorCanBeMet
import YangMills.Construction.ClusterExpansionOfAStep.SettingsOfASharedGasProof
import YangMills.Construction.ResponseInTheExpansion.SettingsOfASharedConfiguration
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open Dobrushin BlockAverages LumpContours TorusFields TorusLumps StepGas StepSettings RenormalizationStepParameters CongruentBoxes
  CongruentAdmission CongruentStates BoxAgreement BlockOffsets
namespace SharedConfiguration
section Fine
variable {L : ℕ} [NeZero L] {n : ℕ} [NeZero n]
theorem fineSite_eq_blockCentre_add (Z : TorusSite n) (h o : Fin 4 → ℤ) :
    (fineSite L Z h o : TorusSite (n * L)) = blockCentre L Z + siteOfInt (fun i => (L : ℤ) * h i + o i) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.InnerSupports.fineSite_eq_blockCentre_add <;> assumption
theorem exists_split_of_offsetInBox (hodd : Odd L) {N : ℕ} {a : Fin 4 → ℤ}
    (ha : OffsetInBox (refinedRadius L N) a) :
    ∃ h o, OffsetInBox N h ∧ o ∈ centredCube L ∧ a = (fun i => (L : ℤ) * h i + o i) ∧ coarseOffset L a = h := by apply _root_.YangMills.Construction.InBoxTransfer.exists_split_of_offsetInBox <;> assumption
end Fine
section Block
variable {L : ℕ} [NeZero L]
theorem parentBlock_add_unitStep (hodd : Odd L) (h o : Fin 4 → ℤ) (ho : o ∈ centredCube L) (i : Fin 4) :
    ∃ h₂ : Fin 4 → ℤ, (∀ l, |h₂ l - h l| ≤ 1) ∧ ∀ (k : ℕ) [NeZero k] (Z : TorusSite k),
      parentBlock L (fineSite L Z h o + TorusFields.unitStep (k * L) i) = Z + siteOfInt h₂ := by apply _root_.YangMills.Construction.InBoxTransfer.exists_parentBlock_add_unitStep <;> assumption
end Block
section Grounds
variable {R : StepSetup} {n n' : ℕ} [NeZero n] [NeZero n'] {G : GasGround R n} {G' : GasGround R n'}
  {Y : TorusSite n} {Y' : TorusSite n'} {N m : ℕ} {A : Finset (TorusSite n)} {A' : Finset (TorusSite n')}
structure NestedBoxes (G : GasGround R n) (G' : GasGround R n') (Y : TorusSite n) (Y' : TorusSite n')
    (N m : ℕ) : Prop where
  side_odd : Odd R.params.side
  groundsAgree : GroundsAgreeNear G G' Y Y' N
  radius_eq : m + R.frameReach + 1 = N
  frame_wide : 16 * R.range ≤ R.params.side * R.frameReach
theorem groundsAgreeNear_symm {M : ℕ} (h : GroundsAgreeNear G G' Y Y' M) : GroundsAgreeNear G' G Y' Y M := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.InnerSupports.groundsAgreeNear_symm <;> assumption
theorem NestedBoxes.symm (B : NestedBoxes G G' Y Y' N m) : NestedBoxes G' G Y' Y N m :=
  ⟨B.side_odd, groundsAgreeNear_symm B.groundsAgree, B.radius_eq, B.frame_wide⟩
theorem NestedBoxes.refined_lt (B : NestedBoxes G G' Y Y' N m) :
    2 * refinedRadius R.params.side N + 2 < n * R.params.side :=
  refinedRadius_lt_side B.side_odd B.groundsAgree.lt_extent
theorem NestedBoxes.refined_lt' (B : NestedBoxes G G' Y Y' N m) :
    2 * refinedRadius R.params.side N + 2 < n' * R.params.side :=
  refinedRadius_lt_side B.side_odd B.groundsAgree.lt_extent'
theorem NestedBoxes.refinedRadius_add_le (B : NestedBoxes G G' Y Y' N m) :
    refinedRadius R.params.side m + 16 * R.range ≤ refinedRadius R.params.side N := by
  have h := B.frame_wide
  have e : R.params.side * N = R.params.side * m + R.params.side * R.frameReach + R.params.side := by
    rw [← B.radius_eq]
    ring
  unfold refinedRadius
  omega
theorem NestedBoxes.two_le (B : NestedBoxes G G' Y Y' N m) : 2 ≤ n := by
  have := B.groundsAgree.lt_extent
  omega
theorem NestedBoxes.two_le' (B : NestedBoxes G G' Y Y' N m) : 2 ≤ n' := by
  have := B.groundsAgree.lt_extent'
  omega
theorem offsetInBox_mono {a b : ℕ} {h : Fin 4 → ℤ} (hab : a ≤ b) (hh : OffsetInBox a h) : OffsetInBox b h := by apply _root_.YangMills.Construction.InBoxTransfer.offsetInBox_mono <;> assumption
theorem mem_gasSupport_sites {θ : GasSupport R n} {z : TorusSite (n * R.params.side)} :
    z ∈ θ.sites ↔ (∃ b ∈ θ.1, b.1 = z) ∨ z ∈ θ.2 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.InnerSupports.mem_gasSupport_sites <;> assumption
theorem exists_offset_of_mem_sites (B : NestedBoxes G G' Y Y' N m) {θ : GasSupport R n}
    (hc : ∀ y ∈ θ.core, ∃ h, OffsetInBox m h ∧ y = Y + siteOfInt h) {z : TorusSite (n * R.params.side)}
    (hz : z ∈ θ.sites) :
    ∃ a, OffsetInBox (refinedRadius R.params.side m) a ∧ z = blockCentre R.params.side Y + siteOfInt a := by
  obtain ⟨h, hh, e⟩ := hc _ (GasSupport.parentBlock_mem_core hz)
  exact ⟨_, offsetInBox_refinedOffset B.side_odd hh _, eq_blockCentre_add_of_parentBlock e⟩
theorem ballsInBox_of_inner (B : NestedBoxes G G' Y Y' N m) {S : Finset (TorusSite (n * R.params.side))} {ρ : ℕ}
    (hρ : ρ ≤ 16 * R.range)
    (hS : ∀ z ∈ S, ∃ a, OffsetInBox (refinedRadius R.params.side m) a ∧
      z = blockCentre R.params.side Y + siteOfInt a) :
    BallsInBox (blockCentre R.params.side Y) (refinedRadius R.params.side N) S ρ := by
  intro a ha hz e he i
  obtain ⟨a₀, h0, e0⟩ := hS _ hz
  have hw := B.refinedRadius_add_le
  have hmono : refinedRadius R.params.side m ≤ refinedRadius R.params.side N := by omega
  have : a = a₀ := eq_of_add_siteOfInt_eq B.refined_lt ha (offsetInBox_mono hmono h0) e0
  subst this
  have h1 := h0 i
  have h2 := he i
  rw [abs_le] at h1 h2 ⊢
  have h3 : ((refinedRadius R.params.side m : ℕ) : ℤ) + ((ρ : ℕ) : ℤ) ≤
      ((refinedRadius R.params.side N : ℕ) : ℤ) := by
    exact_mod_cast (by omega : refinedRadius R.params.side m + ρ ≤ refinedRadius R.params.side N)
  simp only [Pi.add_apply]
  constructor <;> omega
theorem exists_parent_of_congruent (hodd : Odd R.params.side) (hn : 2 * N + 2 < n)
    {W : Finset (TorusSite (n * R.params.side))} {W' : Finset (TorusSite (n' * R.params.side))}
    (hW : CongruentInBoxes W W' (blockCentre R.params.side Y) (blockCentre R.params.side Y')
      (refinedRadius R.params.side N)) {h : Fin 4 → ℤ} (hh : OffsetInBox N h)
    (hx : ∃ x ∈ W, parentBlock R.params.side x = Y + siteOfInt h) :
    ∃ x ∈ W', parentBlock R.params.side x = Y' + siteOfInt h := by exact _root_.YangMills.Construction.ClusterExpansionOfAStep.InnerSupports.exists_parentBlock_of_congruent (R := R) (n := n) (n' := n') hodd hn hW hh hx
theorem mem_coreBlocks_iff_of_congruent (B : NestedBoxes G G' Y Y' N m)
    {S : Finset (TorusSite (n * R.params.side))} {S' : Finset (TorusSite (n' * R.params.side))}
    (hS : CongruentInBoxes S S' (blockCentre R.params.side Y) (blockCentre R.params.side Y')
      (refinedRadius R.params.side N))
    (hd : BallsInBox (blockCentre R.params.side Y) (refinedRadius R.params.side N) S (4 * R.range))
    {h : Fin 4 → ℤ} (hh : OffsetInBox N h) :
    Y + siteOfInt h ∈ coreBlocks R.params.side R.range S ↔ Y' + siteOfInt h ∈ coreBlocks R.params.side R.range S' := by
  have hW := congruentInBoxes_thickening B.refined_lt B.refined_lt' hS hd
  rw [mem_coreBlocks_iff, mem_coreBlocks_iff]
  exact ⟨exists_parent_of_congruent B.side_odd B.groundsAgree.lt_extent hW hh,
    exists_parent_of_congruent B.side_odd B.groundsAgree.lt_extent' (congruentInBoxes_symm hW) hh⟩
variable {θ : GasSupport R n} {θ' : GasSupport R n'}
theorem bad_mem_iff (B : NestedBoxes G G' Y Y' N m) (h : SameSupportNear θ θ' Y Y' N) {a : Fin 4 → ℤ}
    (ha : OffsetInBox (refinedRadius R.params.side N) a) (i : Fin 4) :
    ((blockCentre R.params.side Y + siteOfInt a, i) : TorusBond (n * R.params.side)) ∈ θ.1 ↔
      ((blockCentre R.params.side Y' + siteOfInt a, i) : TorusBond (n' * R.params.side)) ∈ θ'.1 := by
  obtain ⟨c, o, hc, ho, rfl, -⟩ := exists_split_of_offsetInBox B.side_odd ha
  rw [← fineSite_eq_blockCentre_add, ← fineSite_eq_blockCentre_add]
  exact h.bad_iff (c, o, i) ⟨hc, ho⟩
theorem set_mem_iff (B : NestedBoxes G G' Y Y' N m) (h : SameSupportNear θ θ' Y Y' N) {a : Fin 4 → ℤ}
    (ha : OffsetInBox (refinedRadius R.params.side N) a) :
    (blockCentre R.params.side Y + siteOfInt a : TorusSite (n * R.params.side)) ∈ θ.2 ↔
      (blockCentre R.params.side Y' + siteOfInt a : TorusSite (n' * R.params.side)) ∈ θ'.2 := by
  obtain ⟨c, o, hc, ho, rfl, -⟩ := exists_split_of_offsetInBox B.side_odd ha
  rw [← fineSite_eq_blockCentre_add, ← fineSite_eq_blockCentre_add]
  exact h.sites_iff c o hc ho
theorem exists_outer_offset_of_mem_sites (B : NestedBoxes G G' Y Y' N m)
    (hc : ∀ y ∈ θ.core, ∃ h, OffsetInBox m h ∧ y = Y + siteOfInt h)
    {z : TorusSite (n * R.params.side)} (hz : z ∈ θ.sites) :
    ∃ a, OffsetInBox (refinedRadius R.params.side N) a ∧ z = blockCentre R.params.side Y + siteOfInt a := by
  obtain ⟨a, ha, e⟩ := exists_offset_of_mem_sites B hc hz
  have := B.refinedRadius_add_le
  exact ⟨a, offsetInBox_mono (by omega) ha, e⟩
theorem congruentInBoxes_sites (B : NestedBoxes G G' Y Y' N m) (h : SameSupportNear θ θ' Y Y' N)
    (hc : ∀ y ∈ θ.core, ∃ h, OffsetInBox m h ∧ y = Y + siteOfInt h)
    (hc' : ∀ y ∈ θ'.core, ∃ h, OffsetInBox m h ∧ y = Y' + siteOfInt h) :
    CongruentInBoxes θ.sites θ'.sites (blockCentre R.params.side Y) (blockCentre R.params.side Y')
      (refinedRadius R.params.side N) := by
  refine ⟨fun z hz => exists_outer_offset_of_mem_sites B hc hz,
    fun z hz => exists_outer_offset_of_mem_sites B.symm hc' hz, fun a ha => ?_⟩
  rw [mem_gasSupport_sites, mem_gasSupport_sites]
  refine or_congr ⟨?_, ?_⟩ (set_mem_iff B h ha)
  · rintro ⟨b, hb, e⟩
    have : b = (blockCentre R.params.side Y + siteOfInt a, b.2) := Prod.ext e rfl
    exact ⟨(blockCentre R.params.side Y' + siteOfInt a, b.2), (bad_mem_iff B h ha b.2).1 (this ▸ hb), rfl⟩
  · rintro ⟨b, hb, e⟩
    have : b = (blockCentre R.params.side Y' + siteOfInt a, b.2) := Prod.ext e rfl
    exact ⟨(blockCentre R.params.side Y + siteOfInt a, b.2), (bad_mem_iff B h ha b.2).2 (this ▸ hb), rfl⟩
theorem mem_core_iff (B : NestedBoxes G G' Y Y' N m) (hs : SameSupportNear θ θ' Y Y' N)
    (hc : ∀ y ∈ θ.core, ∃ h, OffsetInBox m h ∧ y = Y + siteOfInt h)
    (hc' : ∀ y ∈ θ'.core, ∃ h, OffsetInBox m h ∧ y = Y' + siteOfInt h)
    {h : Fin 4 → ℤ} (hh : OffsetInBox N h) : Y + siteOfInt h ∈ θ.core ↔ Y' + siteOfInt h ∈ θ'.core :=
  mem_coreBlocks_iff_of_congruent B (congruentInBoxes_sites B hs hc hc')
    (ballsInBox_of_inner B (by omega) fun z hz => exists_offset_of_mem_sites B hc hz) hh
theorem mem_coreBonds_iff (B : NestedBoxes G G' Y Y' N m) (hs : SameSupportNear θ θ' Y Y' N)
    (hc : ∀ h, OffsetInBox N h → (Y + siteOfInt h ∈ θ.core ↔ Y' + siteOfInt h ∈ θ'.core)) {q : NearBondIndex}
    (hq : IsNearIndex R.params.side N q) :
    nearBond R.params.side Y q ∈ θ.coreBonds ↔ nearBond R.params.side Y' q ∈ θ'.coreBonds := by
  classical
  obtain ⟨h, o, i⟩ := q
  obtain ⟨hh, ho⟩ := hq
  have hodd := B.side_odd
  have hn := B.groundsAgree.lt_extent
  have hn' := B.groundsAgree.lt_extent'
  obtain ⟨h₂, hd, hb⟩ := parentBlock_add_unitStep hodd h o ho i
  have hh₂ : ∀ {k : ℕ} [NeZero k] (Z : TorusSite k) {a : Fin 4 → ℤ}, 2 * N + 2 < k → OffsetInBox N a →
      Z + siteOfInt h₂ = Z + siteOfInt a → h₂ = a := by
    intro k _ Z a hk ha e
    refine eq_of_siteOfInt_eq (n := k) (add_left_cancel e) fun l => ?_
    have a1 := abs_le.1 (hd l)
    have a2 := abs_le.1 ((show OffsetInBox N h from hh) l)
    have a3 := abs_le.1 (ha l)
    rw [abs_lt]
    constructor <;> omega
  have hmem : ∀ {k : ℕ} [NeZero k] (ϑ : GasSupport R k) (b : TorusBond (k * R.params.side)),
      b ∈ ϑ.coreBonds ↔ parentBlock R.params.side b.1 ∈ ϑ.core ∧
        parentBlock R.params.side (b.1 + TorusFields.unitStep (k * R.params.side) b.2) ∈ ϑ.core := by
    intro k _ ϑ b
    unfold GasSupport.coreBonds
    simp
  rw [hmem θ, hmem θ']
  simp only [nearBond]
  rw [parentBlock_fineSite hodd Y h o ho, parentBlock_fineSite hodd Y' h o ho, hb n Y, hb n' Y', hc h hh]
  refine and_congr_right fun _ => ⟨fun hy => ?_, fun hy => ?_⟩
  · obtain ⟨a, ha, e⟩ := hs.core_mem _ hy
    have := hh₂ Y hn ha e
    subst this
    exact (hc _ ha).1 hy
  · obtain ⟨a, ha, e⟩ := hs.core_mem' _ hy
    have := hh₂ Y' hn' ha e
    subst this
    exact (hc _ ha).2 hy
theorem mem_gasFamily_sites_iff {p : ℕ} [NeZero p] {γ : GasFamily R p} {z : TorusSite (p * R.params.side)} :
    z ∈ γ.sites ↔ ∃ θ, γ.Occupies θ ∧ z ∈ θ.2 := by apply _root_.YangMills.Construction.InBoxTransfer.mem_sites_iff <;> assumption
section Shared
variable (g : SharedInnerGas G G' Y Y' N m A A') (τ : g.Config)
theorem extendFirst_inner (j : G.InnerSpin Y m A) : g.extendFirst τ j.1 = τ j := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.SharedGasSettings.extendFirst_apply <;> assumption
theorem extendSecond_image (j : G.InnerSpin Y m A) :
    g.extendSecond τ (g.spinEquiv j).1 = g.valueEquiv j (τ j) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.SharedGasSettings.extendSecond_apply <;> assumption
theorem extendSecond_of_not_image {i : G'.GasSpin} (h : ∀ j : G.InnerSpin Y m A, (g.spinEquiv j).1 ≠ i) :
    g.extendSecond τ i = Sum.inl () := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.SharedGasSettings.extendSecond_of_forall_ne <;> assumption
theorem valueEquiv_eq_inl_iff (j : G.InnerSpin Y m A) {s : G.SpinValue j.1} :
    g.valueEquiv j s = Sum.inl () ↔ s = Sum.inl () := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.SharedGasSettings.valueEquiv_eq_inl_iff <;> assumption
theorem extendSecond_admissible (hτ : G.pairConstraint.IsAdmissible (g.extendFirst τ)) :
    G'.pairConstraint.IsAdmissible (g.extendSecond τ) := by
  classical
  intro i i' hii
  by_cases h1 : ∃ j : G.InnerSpin Y m A, (g.spinEquiv j).1 = i
  · obtain ⟨j, rfl⟩ := h1
    by_cases h2 : ∃ j' : G.InnerSpin Y m A, (g.spinEquiv j').1 = i'
    · obtain ⟨j', rfl⟩ := h2
      have hne : j ≠ j' := fun h => hii (by rw [h])
      rw [extendSecond_image g τ j, extendSecond_image g τ j']
      have := hτ j.1 j'.1 fun h => hne (Subtype.ext h)
      rw [extendFirst_inner g τ j, extendFirst_inner g τ j'] at this
      rcases this with h | h | h
      · exact Or.inl ((valueEquiv_eq_inl_iff g j).mpr h)
      · exact Or.inr (Or.inl ((valueEquiv_eq_inl_iff g j').mpr h))
      · exact Or.inr (Or.inr ((g.farApart_iff j j' hne).mp h))
    · rw [extendSecond_of_not_image g τ fun j' hj => h2 ⟨j', hj⟩]
      exact Or.inr (Or.inl rfl)
  · rw [extendSecond_of_not_image g τ fun j hj => h1 ⟨j, hj⟩]
    exact Or.inl rfl
theorem exists_inner_of_occupies_first {θ : GasSupport R n} (h : (G.familyOf (g.extendFirst τ)).Occupies θ) :
    ∃ j : G.InnerSpin Y m A, j.1.1 = θ ∧ τ j ≠ Sum.inl () := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.SharedGasSettings.exists_inner_of_occupies_first <;> assumption
theorem exists_inner_of_occupies_second {θ : GasSupport R n'}
    (h : (G'.familyOf (g.extendSecond τ)).Occupies θ) :
    ∃ j : G.InnerSpin Y m A, (g.spinEquiv j).1.1 = θ ∧ τ j ≠ Sum.inl () := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.SharedGasSettings.exists_inner_of_occupies_second <;> assumption
theorem occupies_of_ne_vacant (j : G.InnerSpin Y m A) (hj : τ j ≠ Sum.inl ()) :
    ∃ (h₁ : (G.familyOf (g.extendFirst τ)).Occupies j.1.1)
      (h₂ : (G'.familyOf (g.extendSecond τ)).Occupies (g.spinEquiv j).1.1),
      SameStateNear j.1.1 (g.spinEquiv j).1.1 ((G.familyOf (g.extendFirst τ)).state h₁)
        ((G'.familyOf (g.extendSecond τ)).state h₂) Y Y' N := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.SharedGasSettings.exists_sameStateNear <;> assumption
end Shared
theorem familiesMatchNear_of_shared (B : NestedBoxes G G' Y Y' N m) (hr : R.params.side ≤ 2 * R.range)
    (g : SharedInnerGas G G' Y Y' N m A A') (τ : g.Config)
    (hτ : G.pairConstraint.IsAdmissible (g.extendFirst τ)) :
    FamiliesMatchNear (G.familyOf (g.extendFirst τ)) (G'.familyOf (g.extendSecond τ)) Y Y' N := by
  classical
  have sep := G.coresDisjoint_familyOf hτ hr
  have sep' := G'.coresDisjoint_familyOf (extendSecond_admissible g τ hτ) hr
  have hcore : ∀ j : G.InnerSpin Y m A, ∀ h, OffsetInBox N h →
      (Y + siteOfInt h ∈ j.1.1.core ↔ Y' + siteOfInt h ∈ (g.spinEquiv j).1.1.core) := fun j h hh =>
    mem_core_iff B (g.sameSupport j) j.2.core_near (g.spinEquiv j).2.core_near hh
  refine ⟨fun q hq => ?_, fun h o hh ho => ?_, fun h o hz hz' hh ho => ?_, fun h hh => ?_⟩
  · by_cases hex : ∃ j : G.InnerSpin Y m A, τ j ≠ Sum.inl () ∧ nearBond R.params.side Y q ∈ j.1.1.coreBonds
    · obtain ⟨j, hj, hb⟩ := hex
      have hb' := (mem_coreBonds_iff B (g.sameSupport j) (hcore j) hq).1 hb
      obtain ⟨h₁, h₂, e⟩ := occupies_of_ne_vacant g τ j hj
      rw [fieldAt_eq_of_mem_coreBonds sep h₁ hb, fieldAt_eq_of_mem_coreBonds sep' h₂ hb']
      exact congrArg Sum.inr (e.field_eq q hb hb' hq)
    · rw [fieldAt_eq_inl_of_forall_not_mem fun θ h hb => ?_, fieldAt_eq_inl_of_forall_not_mem fun θ h hb => ?_]
      · obtain ⟨j, rfl, hj⟩ := exists_inner_of_occupies_second g τ h
        exact hex ⟨j, hj, (mem_coreBonds_iff B (g.sameSupport j) (hcore j) hq).2 hb⟩
      · obtain ⟨j, rfl, hj⟩ := exists_inner_of_occupies_first g τ h
        exact hex ⟨j, hj, hb⟩
  · constructor
    · intro hz
      obtain ⟨θ, h₁, h₂⟩ := mem_gasFamily_sites_iff.mp hz
      obtain ⟨j, rfl, hj⟩ := exists_inner_of_occupies_first g τ h₁
      obtain ⟨-, h₃, -⟩ := occupies_of_ne_vacant g τ j hj
      exact mem_gasFamily_sites_iff.mpr ⟨_, h₃, ((g.sameSupport j).sites_iff h o hh ho).1 h₂⟩
    · intro hz
      obtain ⟨θ, h₁, h₂⟩ := mem_gasFamily_sites_iff.mp hz
      obtain ⟨j, rfl, hj⟩ := exists_inner_of_occupies_second g τ h₁
      obtain ⟨h₃, -, -⟩ := occupies_of_ne_vacant g τ j hj
      exact mem_gasFamily_sites_iff.mpr ⟨_, h₃, ((g.sameSupport j).sites_iff h o hh ho).2 h₂⟩
  · obtain ⟨θ, h₁, h₂⟩ := mem_gasFamily_sites_iff.mp hz
    obtain ⟨j, rfl, hj⟩ := exists_inner_of_occupies_first g τ h₁
    obtain ⟨h₃, h₄, e⟩ := occupies_of_ne_vacant g τ j hj
    have h₂' := ((g.sameSupport j).sites_iff h o hh ho).1 h₂
    rw [GasFamily.labelAt_eq_of_mem _ sep hz h₃ h₂, GasFamily.labelAt_eq_of_mem _ sep' hz' h₄ h₂']
    exact e.label_eq h o h₂ h₂' hh ho
  · by_cases hex : ∃ j : G.InnerSpin Y m A, τ j ≠ Sum.inl () ∧ Y + siteOfInt h ∈ j.1.1.core
    · obtain ⟨j, hj, hy⟩ := hex
      have hy' := (hcore j h hh).1 hy
      obtain ⟨h₁, h₂, e⟩ := occupies_of_ne_vacant g τ j hj
      rw [baseAt_eq_of_mem_core sep h₁ hy, baseAt_eq_of_mem_core sep' h₂ hy']
      exact congrArg Sum.inr (e.base_eq h hy hy' hh)
    · rw [baseAt_eq_inl_of_forall_not_mem fun θ c hy => ?_, baseAt_eq_inl_of_forall_not_mem fun θ c hy => ?_]
      · obtain ⟨j, rfl, hj⟩ := exists_inner_of_occupies_second g τ c
        exact hex ⟨j, hj, (hcore j h hh).2 hy⟩
      · obtain ⟨j, rfl, hj⟩ := exists_inner_of_occupies_first g τ c
        exact hex ⟨j, hj, hy⟩
end Grounds
end SharedConfiguration
open SharedConfiguration in
theorem sharedConfigurationSettingsAgree (hFl : StepFloors.EventuallyFloorConditions)
    (hCF : TorusLumps.CouplingFloorExists) :
    SharedConfigurationSettingsAgree := by
  classical
  intro T hT
  obtain ⟨y₁, hy₁⟩ := hFl T hT (2 ^ 12) 1 (by norm_num) one_pos
  obtain ⟨y₂, hy₂⟩ := hCF 1 T.side T.rt one_pos
  refine ⟨max y₁ (max y₂ T.floorMin), fun y hy R hR hx' n n' _ _ G G' Y Y' N g τ hG hG' hN hag hτ => ?_⟩
  obtain ⟨a₁, hy⟩ := max_le_iff.mp hy
  obtain ⟨a₃, a₂⟩ := max_le_iff.mp hy
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
  have B : NestedBoxes G G' Y Y' N (N - R.frameReach - 1) := ⟨hfit.L_odd, hag, by omega, hbig⟩
  have hLr : R.params.side ≤ 2 * R.range := by
    have h1 : T.side ≤ clusterRange R.coupling := (hy₂ R.coupling (a₃.trans hR.le_coupling)).1
    have h2 : R.params.side = T.side := by
      rw [hR.params_eq]
      rfl
    have h3 : R.range = clusterRange R.coupling := rfl
    omega
  exact settingsAgreeAwayFromFrames_of_match hfit.L_odd B.two_le B.two_le' hag
    (familiesMatchNear_of_shared B hLr g τ hτ)
end YangMills.Construction.ResponseInTheExpansion
end
