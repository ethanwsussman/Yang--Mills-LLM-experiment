import YangMills.Construction.ClusterExpansionOfAStep.AllowedStatesReadTheirBoxProof
import YangMills.Construction.ClusterExpansionOfAStep.ClassBesideAFamily
import YangMills.Construction.ClusterExpansionOfAStep.ConfigurationsOfTheGasAreSettings
import YangMills.Construction.ClusterExpansionOfAStep.DifferencesOfTheDensities
import YangMills.Construction.ClusterExpansionOfAStep.GasSumsAtABlockProof
import YangMills.Construction.ClusterExpansionOfAStep.InnerSupportsWithTheirCoresProof
import YangMills.Construction.ClusterExpansionOfAStep.SharedGasOfTwoGrounds
import YangMills.Construction.ClusterExpansionOfAStep.TwoRatiosOfSettings
import Mathlib
set_option autoImplicit false

noncomputable section
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
def SharedGasSettingsPaired : Prop :=
  ∃ rt₀ : RenormalizationStepParameters.ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧
    ∀ T : RenormalizationStepParameters.ParameterAssignment, T.Admissible → T.rt ≤ rt₀ T.toChainParameters →
    ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSettings.StepSetup, R.OnParameters T y →
      R.nextCoupling ≤ 1.01 * R.coupling → ∀ (n n' : ℕ) [NeZero n] [NeZero n']
      (G : StepGas.GasGround R n) (G' : StepGas.GasGround R n') (Y : TorusFields.TorusSite n)
      (Y' : TorusFields.TorusSite n') (N : ℕ)
      (A : Finset (TorusFields.TorusSite n)) (A' : Finset (TorusFields.TorusSite n'))
      (g : StepGas.SharedInnerGas G G' Y Y' N (N - R.frameReach - 1) A A') (τ : g.Config)
      (j : G.InnerSpin Y (N - R.frameReach - 1) A)
      (s : G.SpinValue j.1) (d k : ℕ),
      G.IsAdmissibleGround → G'.IsAdmissibleGround → 16 * R.frameReach ≤ N →
      StepGas.GroundsAgreeNear G G' Y Y' N → StepGas.BlockSetsAgreeNear A A' Y Y' N →
      G.pairConstraint.IsAdmissible (g.extendFirst (Function.update τ j s)) →
      (∀ h ∈ G.coreOffsets Y (N - R.frameReach - 1) j.1,
        TorusFields.OffsetInBox (N - R.frameReach - (k + d)) h) →
      k + d ≤ N - R.frameReach →
      PairedSettings
        (G.settingOf (G.familyOf (g.extendFirst (Function.update τ j (Sum.inl ())))))
        (G.settingOf (G.familyOf (g.extendFirst (Function.update τ j s))))
        (G'.settingOf (G'.familyOf (g.extendSecond (Function.update τ j (Sum.inl ())))))
        (G'.settingOf (G'.familyOf (g.extendSecond (Function.update τ j s))))
        (G.coreOffsets Y (N - R.frameReach - 1) j.1) Y Y' d k
end YangMills.Construction.ClusterExpansionOfAStep
end

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction
open Dobrushin TorusFields TorusLumps StepGas StepSettings StepCosts BlockOffsets BlockTrees BlockZones CongruentBoxes
  CongruentAdmission BoxAgreement
namespace ClusterExpansionOfAStep
namespace SharedGasSettings
variable {R : StepSetup} {n : ℕ} [NeZero n]
section Families
theorem eq_inr_getRight {α : Type} (a : WithNone α) (h : a.isRight = true) : a = Sum.inr (a.getRight h) := by apply _root_.YangMills.Construction.InBoxTransfer.eq_inr_getRight <;> assumption
variable {γ γ' : GasFamily R n} {θ θ' : GasSupport R n}
theorem apply_eq_inr_state (h : γ.Occupies θ) : γ θ = Sum.inr (γ.state h) := eq_inr_getRight _ h
theorem mem_sites_iff {z : TorusSite (n * R.params.side)} : z ∈ γ.sites ↔ ∃ θ, γ.Occupies θ ∧ z ∈ θ.2 := by apply _root_.YangMills.Construction.InBoxTransfer.mem_sites_iff <;> assumption
end Families
section TopOffset
theorem cellOffset_torusFrame_blockPoint {L n : ℕ} [NeZero L] [NeZero n] (t : ℕ) (hodd : Odd L) (A o : Fin 4 → ℤ)
    (ho : o ∈ BlockAverages.centredCube L) :
    BlockAverages.cellOffset (F := torusFrame L t n)
      (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).depth
        (siteOfInt (blockPoint L A o) : TorusSite (n * L))) = o := by apply _root_.YangMills.Construction.InBoxTransfer.cellOffset_torusFrame <;> assumption
end TopOffset
section Refined
variable {L : ℕ} [NeZero L] {n : ℕ} [NeZero n]
theorem fineSite_eq_blockCentre_add (Z : TorusSite n) (h o : Fin 4 → ℤ) :
    (fineSite L Z h o : TorusSite (n * L)) = blockCentre L Z + siteOfInt (fun i => (L : ℤ) * h i + o i) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.InnerSupports.fineSite_eq_blockCentre_add <;> assumption
theorem exists_block_offset_split (hodd : Odd L) {N : ℕ} {a : Fin 4 → ℤ} (ha : OffsetInBox (refinedRadius L N) a) :
    ∃ h o, OffsetInBox N h ∧ o ∈ BlockAverages.centredCube L ∧ a = (fun i => (L : ℤ) * h i + o i) ∧
      coarseOffset L a = h := by apply _root_.YangMills.Construction.InBoxTransfer.exists_split_of_offsetInBox <;> assumption
end Refined
section Grounds
variable {R : StepSetup} {n n' : ℕ} [NeZero n] [NeZero n'] {G : GasGround R n} {G' : GasGround R n'}
  {Y : TorusSite n} {Y' : TorusSite n'} {N m : ℕ} {A : Finset (TorusSite n)} {A' : Finset (TorusSite n')}
structure MatchedBox (G : GasGround R n) (G' : GasGround R n') (Y : TorusSite n) (Y' : TorusSite n') (N m : ℕ) :
    Prop where
  side_odd : Odd R.params.side
  groundsAgree : GroundsAgreeNear G G' Y Y' N
  radius_eq : m + R.frameReach + 1 = N
  range_le : 16 * R.range ≤ R.params.side * R.frameReach
theorem groundsAgreeNear_symm {M : ℕ} (h : GroundsAgreeNear G G' Y Y' M) : GroundsAgreeNear G' G Y' Y M := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.InnerSupports.groundsAgreeNear_symm <;> assumption
theorem MatchedBox.symm (B : MatchedBox G G' Y Y' N m) : MatchedBox G' G Y' Y N m :=
  ⟨B.side_odd, groundsAgreeNear_symm B.groundsAgree, B.radius_eq, B.range_le⟩
theorem MatchedBox.refinedRadius_lt (B : MatchedBox G G' Y Y' N m) :
    2 * refinedRadius R.params.side N + 2 < n * R.params.side :=
  refinedRadius_lt_side B.side_odd B.groundsAgree.lt_extent
theorem MatchedBox.refinedRadius_lt' (B : MatchedBox G G' Y Y' N m) :
    2 * refinedRadius R.params.side N + 2 < n' * R.params.side :=
  refinedRadius_lt_side B.side_odd B.groundsAgree.lt_extent'
theorem MatchedBox.refinedRadius_add_le (B : MatchedBox G G' Y Y' N m) :
    refinedRadius R.params.side m + 16 * R.range ≤ refinedRadius R.params.side N := by
  have h := B.range_le
  have e : R.params.side * N = R.params.side * m + R.params.side * R.frameReach + R.params.side := by
    rw [← B.radius_eq]
    ring
  unfold refinedRadius
  omega
theorem MatchedBox.two_le (B : MatchedBox G G' Y Y' N m) : 2 ≤ n := by
  have := B.groundsAgree.lt_extent
  omega
theorem MatchedBox.two_le' (B : MatchedBox G G' Y Y' N m) : 2 ≤ n' := by
  have := B.groundsAgree.lt_extent'
  omega
theorem offsetInBox_mono {a b : ℕ} {h : Fin 4 → ℤ} (hab : a ≤ b) (hh : OffsetInBox a h) : OffsetInBox b h := by apply _root_.YangMills.Construction.InBoxTransfer.offsetInBox_mono <;> assumption
theorem mem_gasSupport_sites_iff {θ : GasSupport R n} {z : TorusSite (n * R.params.side)} :
    z ∈ θ.sites ↔ (∃ b ∈ θ.1, b.1 = z) ∨ z ∈ θ.2 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.InnerSupports.mem_gasSupport_sites <;> assumption
theorem exists_offset_of_mem_sites (B : MatchedBox G G' Y Y' N m) {θ : GasSupport R n}
    (hc : ∀ y ∈ θ.core, ∃ h, OffsetInBox m h ∧ y = Y + siteOfInt h) {z : TorusSite (n * R.params.side)}
    (hz : z ∈ θ.sites) :
    ∃ a, OffsetInBox (refinedRadius R.params.side m) a ∧ z = blockCentre R.params.side Y + siteOfInt a := by
  obtain ⟨h, hh, e⟩ := hc _ (GasSupport.parentBlock_mem_core hz)
  exact ⟨_, offsetInBox_refinedOffset B.side_odd hh _, eq_blockCentre_add_of_parentBlock e⟩
theorem ballsInBox_of_inner (B : MatchedBox G G' Y Y' N m) {S : Finset (TorusSite (n * R.params.side))} {ρ : ℕ}
    (hρ : ρ ≤ 16 * R.range)
    (hS : ∀ z ∈ S, ∃ a, OffsetInBox (refinedRadius R.params.side m) a ∧ z = blockCentre R.params.side Y + siteOfInt a) :
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
  have h3 : ((refinedRadius R.params.side m : ℕ) : ℤ) + ((ρ : ℕ) : ℤ) ≤ ((refinedRadius R.params.side N : ℕ) : ℤ) := by
    exact_mod_cast (by omega : refinedRadius R.params.side m + ρ ≤ refinedRadius R.params.side N)
  simp only [Pi.add_apply]
  constructor <;> omega
theorem exists_parentBlock_of_congruent (hodd : Odd R.params.side) (hn : 2 * N + 2 < n)
    {W : Finset (TorusSite (n * R.params.side))} {W' : Finset (TorusSite (n' * R.params.side))}
    (hW : CongruentInBoxes W W' (blockCentre R.params.side Y) (blockCentre R.params.side Y')
      (refinedRadius R.params.side N)) {h : Fin 4 → ℤ} (hh : OffsetInBox N h)
    (hx : ∃ x ∈ W, parentBlock R.params.side x = Y + siteOfInt h) :
    ∃ x ∈ W', parentBlock R.params.side x = Y' + siteOfInt h := by exact _root_.YangMills.Construction.ClusterExpansionOfAStep.InnerSupports.exists_parentBlock_of_congruent (R := R) (n := n) (n' := n') hodd hn hW hh hx
theorem mem_coreBlocks_iff_of_congruent (B : MatchedBox G G' Y Y' N m) {S : Finset (TorusSite (n * R.params.side))}
    {S' : Finset (TorusSite (n' * R.params.side))}
    (hS : CongruentInBoxes S S' (blockCentre R.params.side Y) (blockCentre R.params.side Y')
      (refinedRadius R.params.side N))
    (hd : BallsInBox (blockCentre R.params.side Y) (refinedRadius R.params.side N) S (4 * R.range))
    {h : Fin 4 → ℤ} (hh : OffsetInBox N h) :
    Y + siteOfInt h ∈ coreBlocks R.params.side R.range S ↔ Y' + siteOfInt h ∈ coreBlocks R.params.side R.range S' := by
  have hW := congruentInBoxes_thickening B.refinedRadius_lt B.refinedRadius_lt' hS hd
  rw [mem_coreBlocks_iff, mem_coreBlocks_iff]
  exact ⟨exists_parentBlock_of_congruent B.side_odd B.groundsAgree.lt_extent hW hh,
    exists_parentBlock_of_congruent B.side_odd B.groundsAgree.lt_extent' (congruentInBoxes_symm hW) hh⟩
section Pairs
variable {θ : GasSupport R n} {θ' : GasSupport R n'}
theorem mem_bad_iff (B : MatchedBox G G' Y Y' N m) (h : SameSupportNear θ θ' Y Y' N) {a : Fin 4 → ℤ}
    (ha : OffsetInBox (refinedRadius R.params.side N) a) (i : Fin 4) :
    ((blockCentre R.params.side Y + siteOfInt a, i) : TorusBond (n * R.params.side)) ∈ θ.1 ↔
      ((blockCentre R.params.side Y' + siteOfInt a, i) : TorusBond (n' * R.params.side)) ∈ θ'.1 := by
  obtain ⟨c, o, hc, ho, rfl, -⟩ := exists_block_offset_split B.side_odd ha
  rw [← fineSite_eq_blockCentre_add, ← fineSite_eq_blockCentre_add]
  exact h.bad_iff (c, o, i) ⟨hc, ho⟩
theorem mem_snd_iff (B : MatchedBox G G' Y Y' N m) (h : SameSupportNear θ θ' Y Y' N) {a : Fin 4 → ℤ}
    (ha : OffsetInBox (refinedRadius R.params.side N) a) :
    (blockCentre R.params.side Y + siteOfInt a : TorusSite (n * R.params.side)) ∈ θ.2 ↔
      (blockCentre R.params.side Y' + siteOfInt a : TorusSite (n' * R.params.side)) ∈ θ'.2 := by
  obtain ⟨c, o, hc, ho, rfl, -⟩ := exists_block_offset_split B.side_odd ha
  rw [← fineSite_eq_blockCentre_add, ← fineSite_eq_blockCentre_add]
  exact h.sites_iff c o hc ho
theorem exists_refined_offset_of_mem_sites (B : MatchedBox G G' Y Y' N m)
    (hc : ∀ y ∈ θ.core, ∃ h, OffsetInBox m h ∧ y = Y + siteOfInt h) {z : TorusSite (n * R.params.side)}
    (hz : z ∈ θ.sites) :
    ∃ a, OffsetInBox (refinedRadius R.params.side N) a ∧ z = blockCentre R.params.side Y + siteOfInt a := by
  obtain ⟨a, ha, e⟩ := exists_offset_of_mem_sites B hc hz
  have := B.refinedRadius_add_le
  exact ⟨a, offsetInBox_mono (by omega) ha, e⟩
theorem congruentInBoxes_sites (B : MatchedBox G G' Y Y' N m) (h : SameSupportNear θ θ' Y Y' N)
    (hc : ∀ y ∈ θ.core, ∃ h, OffsetInBox m h ∧ y = Y + siteOfInt h)
    (hc' : ∀ y ∈ θ'.core, ∃ h, OffsetInBox m h ∧ y = Y' + siteOfInt h) :
    CongruentInBoxes θ.sites θ'.sites (blockCentre R.params.side Y) (blockCentre R.params.side Y')
      (refinedRadius R.params.side N) := by
  refine ⟨fun z hz => exists_refined_offset_of_mem_sites B hc hz,
    fun z hz => exists_refined_offset_of_mem_sites B.symm hc' hz, fun a ha => ?_⟩
  rw [mem_gasSupport_sites_iff, mem_gasSupport_sites_iff]
  refine or_congr ⟨?_, ?_⟩ (mem_snd_iff B h ha)
  · rintro ⟨b, hb, e⟩
    have : b = (blockCentre R.params.side Y + siteOfInt a, b.2) := Prod.ext e rfl
    exact ⟨(blockCentre R.params.side Y' + siteOfInt a, b.2), (mem_bad_iff B h ha b.2).1 (this ▸ hb), rfl⟩
  · rintro ⟨b, hb, e⟩
    have : b = (blockCentre R.params.side Y' + siteOfInt a, b.2) := Prod.ext e rfl
    exact ⟨(blockCentre R.params.side Y + siteOfInt a, b.2), (mem_bad_iff B h ha b.2).2 (this ▸ hb), rfl⟩
end Pairs
theorem core_mem_iff_of_sameSupport (B : MatchedBox G G' Y Y' N m) {θ : GasSupport R n} {θ' : GasSupport R n'}
    (hs : SameSupportNear θ θ' Y Y' N) (hc : ∀ y ∈ θ.core, ∃ h, OffsetInBox m h ∧ y = Y + siteOfInt h)
    (hc' : ∀ y ∈ θ'.core, ∃ h, OffsetInBox m h ∧ y = Y' + siteOfInt h) :
    ∀ h, OffsetInBox N h → (Y + siteOfInt h ∈ θ.core ↔ Y' + siteOfInt h ∈ θ'.core) := fun h hh =>
  mem_coreBlocks_iff_of_congruent B (congruentInBoxes_sites B hs hc hc')
    (ballsInBox_of_inner B (by omega) fun z hz => exists_offset_of_mem_sites B hc hz) hh
theorem exists_parentBlock_add_unitStep {L : ℕ} [NeZero L] (hodd : Odd L) (h o : Fin 4 → ℤ)
    (ho : o ∈ BlockAverages.centredCube L) (i : Fin 4) :
    ∃ h₂ : Fin 4 → ℤ, (∀ l, |h₂ l - h l| ≤ 1) ∧ ∀ (k : ℕ) [NeZero k] (Z : TorusSite k),
      parentBlock L (fineSite L Z h o + unitStep (k * L) i) = Z + siteOfInt h₂ := by apply _root_.YangMills.Construction.InBoxTransfer.exists_parentBlock_add_unitStep <;> assumption
theorem nearBond_mem_coreBonds_iff (B : MatchedBox G G' Y Y' N m) {θ : GasSupport R n} {θ' : GasSupport R n'}
    (hs : SameSupportNear θ θ' Y Y' N)
    (hcs : ∀ h, OffsetInBox N h → (Y + siteOfInt h ∈ θ.core ↔ Y' + siteOfInt h ∈ θ'.core)) :
    ∀ q, IsNearIndex R.params.side N q →
      (nearBond R.params.side Y q ∈ θ.coreBonds ↔ nearBond R.params.side Y' q ∈ θ'.coreBonds) := by
  classical
  rintro ⟨h, o, i⟩ ⟨hh, ho⟩
  have hh' : OffsetInBox N h := hh
  have hodd := B.side_odd
  have hn := B.groundsAgree.lt_extent
  have hn' := B.groundsAgree.lt_extent'
  obtain ⟨h₂, hd, hb⟩ := exists_parentBlock_add_unitStep hodd h o ho i
  have hh₂ : ∀ {k : ℕ} [NeZero k] (Z : TorusSite k) {a : Fin 4 → ℤ}, 2 * N + 2 < k → OffsetInBox N a →
      Z + siteOfInt h₂ = Z + siteOfInt a → h₂ = a := by
    intro k _ Z a hk ha e
    refine eq_of_siteOfInt_eq (n := k) (add_left_cancel e) fun l => ?_
    have a1 := abs_le.1 (hd l)
    have a2 := abs_le.1 (hh' l)
    have a3 := abs_le.1 (ha l)
    rw [abs_lt]
    constructor <;> omega
  have hmem : ∀ {k : ℕ} [NeZero k] (ϑ : GasSupport R k) (b : TorusBond (k * R.params.side)),
      b ∈ ϑ.coreBonds ↔ parentBlock R.params.side b.1 ∈ ϑ.core ∧
        parentBlock R.params.side (b.1 + unitStep (k * R.params.side) b.2) ∈ ϑ.core := by
    intro k _ ϑ b
    unfold GasSupport.coreBonds
    simp
  rw [hmem θ, hmem θ']
  simp only [nearBond]
  rw [parentBlock_fineSite hodd Y h o ho, parentBlock_fineSite hodd Y' h o ho, hb n Y, hb n' Y', hcs h hh]
  refine and_congr_right fun _ => ⟨fun hy => ?_, fun hy => ?_⟩
  · obtain ⟨a, ha, e⟩ := hs.core_mem _ hy
    have := hh₂ Y hn ha e
    subst this
    exact (hcs _ ha).1 hy
  · obtain ⟨a, ha, e⟩ := hs.core_mem' _ hy
    have := hh₂ Y' hn' ha e
    subst this
    exact (hcs _ ha).2 hy
section Shared
variable {g : SharedInnerGas G G' Y Y' N m A A'}
theorem extendSecond_index_injective (g : SharedInnerGas G G' Y Y' N m A A') :
    Function.Injective fun j => (g.spinEquiv j).1 :=
  Subtype.val_injective.comp g.spinEquiv.injective
theorem embedConfig_apply {I : Type} [Fintype I] [DecidableEq I] {S : I → Type} [∀ i, MeasurableSpace (S i)]
    (Sys : PairConstraint S) {J : Type} {T : J → Type} {e : J → I} (v : ∀ j, T j → S (e j))
    (he : Function.Injective e) (τ : ∀ j, T j) (j : J) :
    Sys.embedConfig e v τ (e j) = v j (τ j) := by
  have key : ∀ (j' : J) (hj : e j' = e j), (hj ▸ v j' (τ j') : S (e j)) = v j (τ j) := by
    intro j' hj
    obtain rfl := he hj
    rfl
  unfold PairConstraint.embedConfig
  rw [dif_pos ⟨j, rfl⟩]
  exact key _ _
theorem embedConfig_of_forall_ne {I : Type} [Fintype I] [DecidableEq I] {S : I → Type} [∀ i, MeasurableSpace (S i)]
    (Sys : PairConstraint S) {J : Type} {T : J → Type} {e : J → I} (v : ∀ j, T j → S (e j)) (τ : ∀ j, T j) {i : I}
    (h : ∀ j, e j ≠ i) : Sys.embedConfig e v τ i = Sys.vacant i := by
  unfold PairConstraint.embedConfig
  rw [dif_neg]
  rintro ⟨j, hj⟩
  exact h j hj
theorem extendFirst_apply (g : SharedInnerGas G G' Y Y' N m A A') (τ : g.Config) (j : G.InnerSpin Y m A) :
    g.extendFirst τ j.1 = τ j :=
  embedConfig_apply G.pairConstraint (fun _ s => s) Subtype.val_injective τ j
theorem extendSecond_apply (g : SharedInnerGas G G' Y Y' N m A A') (τ : g.Config) (j : G.InnerSpin Y m A) :
    g.extendSecond τ (g.spinEquiv j).1 = g.valueEquiv j (τ j) :=
  embedConfig_apply G'.pairConstraint (e := fun j => (g.spinEquiv j).1) (fun j => g.valueEquiv j)
    (extendSecond_index_injective g) τ j
theorem extendFirst_of_not_inner (g : SharedInnerGas G G' Y Y' N m A A') (τ : g.Config) {i : G.GasSpin}
    (h : ¬ G.IsInnerSpin Y m A i) : g.extendFirst τ i = Sum.inl () :=
  embedConfig_of_forall_ne G.pairConstraint (fun _ s => s) τ fun j hj => h (hj ▸ j.2)
theorem extendSecond_of_forall_ne (g : SharedInnerGas G G' Y Y' N m A A') (τ : g.Config) {i : G'.GasSpin}
    (h : ∀ j : G.InnerSpin Y m A, (g.spinEquiv j).1 ≠ i) : g.extendSecond τ i = Sum.inl () :=
  embedConfig_of_forall_ne G'.pairConstraint (e := fun j => (g.spinEquiv j).1) (fun j => g.valueEquiv j) τ h
theorem valueEquiv_eq_inl_iff (g : SharedInnerGas G G' Y Y' N m A A') (j : G.InnerSpin Y m A)
    {s : G.SpinValue j.1} : g.valueEquiv j s = Sum.inl () ↔ s = Sum.inl () := by
  constructor
  · intro h
    exact (g.valueEquiv j).injective (h.trans (g.map_vacant j).symm)
  · rintro rfl
    exact g.map_vacant j
def IsCompatible (g : SharedInnerGas G G' Y Y' N m A A') (τ : g.Config) : Prop :=
  ∀ j j' : G.InnerSpin Y m A, j ≠ j' → τ j = Sum.inl () ∨ τ j' = Sum.inl () ∨ j.1.1.FarApart j'.1.1
theorem isCompatible_of_admissible (g : SharedInnerGas G G' Y Y' N m A A') {τ : g.Config}
    (h : G.pairConstraint.IsAdmissible (g.extendFirst τ)) : IsCompatible g τ := by
  intro j j' hne
  have hne' : j.1 ≠ j'.1 := fun e => hne (Subtype.ext e)
  have := h j.1 j'.1 hne'
  rw [extendFirst_apply g τ j, extendFirst_apply g τ j'] at this
  exact this
theorem admissible_extendFirst (g : SharedInnerGas G G' Y Y' N m A A') {τ : g.Config} (hτ : IsCompatible g τ) :
    G.pairConstraint.IsAdmissible (g.extendFirst τ) := by
  intro i i' hii
  by_cases h1 : G.IsInnerSpin Y m A i
  · by_cases h2 : G.IsInnerSpin Y m A i'
    · have hne : (⟨i, h1⟩ : G.InnerSpin Y m A) ≠ ⟨i', h2⟩ := fun h => hii (congrArg Subtype.val h)
      have := hτ _ _ hne
      rw [extendFirst_apply g τ ⟨i, h1⟩, extendFirst_apply g τ ⟨i', h2⟩]
      exact this
    · rw [extendFirst_of_not_inner g τ h2]
      exact Or.inr (Or.inl rfl)
  · rw [extendFirst_of_not_inner g τ h1]
    exact Or.inl rfl
theorem admissible_extendSecond (g : SharedInnerGas G G' Y Y' N m A A') {τ : g.Config} (hτ : IsCompatible g τ) :
    G'.pairConstraint.IsAdmissible (g.extendSecond τ) := by
  intro i i' hii
  by_cases h1 : ∃ j : G.InnerSpin Y m A, (g.spinEquiv j).1 = i
  · obtain ⟨j, rfl⟩ := h1
    by_cases h2 : ∃ j' : G.InnerSpin Y m A, (g.spinEquiv j').1 = i'
    · obtain ⟨j', rfl⟩ := h2
      have hne : j ≠ j' := fun h => hii (by rw [h])
      rw [extendSecond_apply g τ j, extendSecond_apply g τ j']
      rcases hτ _ _ hne with h | h | h
      · exact Or.inl ((valueEquiv_eq_inl_iff g j).mpr h)
      · exact Or.inr (Or.inl ((valueEquiv_eq_inl_iff g j').mpr h))
      · exact Or.inr (Or.inr ((g.farApart_iff j j' hne).mp h))
    · rw [extendSecond_of_forall_ne g τ fun j' hj => h2 ⟨j', hj⟩]
      exact Or.inr (Or.inl rfl)
  · rw [extendSecond_of_forall_ne g τ fun j hj => h1 ⟨j, hj⟩]
    exact Or.inl rfl
theorem isCompatible_update_vacant (g : SharedInnerGas G G' Y Y' N m A A') {τ : g.Config} {j : G.InnerSpin Y m A}
    {s : G.SpinValue j.1} (h : IsCompatible g (Function.update τ j s)) :
    IsCompatible g (Function.update τ j (Sum.inl ())) := by
  intro a b hne
  by_cases ea : a = j
  · subst ea
    exact Or.inl (by simp)
  · by_cases eb : b = j
    · subst eb
      exact Or.inr (Or.inl (by simp))
    · have := h a b hne
      rwa [Function.update_of_ne ea, Function.update_of_ne eb] at this ⊢
theorem exists_occupies_of_apply_eq_inr {p : ℕ} [NeZero p] {H : GasGround R p} {σ : H.Config} {i : H.GasSpin}
    {st : H.SpinState i} (e : σ i = Sum.inr st) :
    ∃ h : (H.familyOf σ).Occupies i.1, (H.familyOf σ).state h = st.1 := by
  classical
  obtain ⟨θ₀, h₀⟩ := i
  have e1 : H.familyOf σ θ₀ = Sum.inr st.1 := by
    simp only [GasGround.familyOf, dif_pos h₀, e]
  have hh : (H.familyOf σ).Occupies θ₀ := by
    unfold GasFamily.Occupies
    rw [e1]
    rfl
  exact ⟨hh, Sum.inr.inj ((apply_eq_inr_state hh).symm.trans e1)⟩
theorem exists_inner_of_occupies_first (g : SharedInnerGas G G' Y Y' N m A A') {τ : g.Config} {θ : GasSupport R n}
    (h : (G.familyOf (g.extendFirst τ)).Occupies θ) : ∃ j : G.InnerSpin Y m A, j.1.1 = θ ∧ τ j ≠ Sum.inl () := by
  obtain ⟨i, rfl, hi⟩ := G.exists_spin_of_occupies h
  by_cases hin : G.IsInnerSpin Y m A i
  · refine ⟨⟨i, hin⟩, rfl, fun e => hi ?_⟩
    rw [← extendFirst_apply g τ ⟨i, hin⟩] at e
    exact e
  · exact absurd (extendFirst_of_not_inner g τ hin) hi
theorem exists_inner_of_occupies_second (g : SharedInnerGas G G' Y Y' N m A A') {τ : g.Config}
    {θ : GasSupport R n'} (h : (G'.familyOf (g.extendSecond τ)).Occupies θ) :
    ∃ j : G.InnerSpin Y m A, (g.spinEquiv j).1.1 = θ ∧ τ j ≠ Sum.inl () := by
  obtain ⟨i, rfl, hi⟩ := G'.exists_spin_of_occupies h
  by_cases hin : ∃ j : G.InnerSpin Y m A, (g.spinEquiv j).1 = i
  · obtain ⟨j, rfl⟩ := hin
    refine ⟨j, rfl, fun e => hi ?_⟩
    rw [extendSecond_apply g τ j, (valueEquiv_eq_inl_iff g j).2 e]
  · exact absurd (extendSecond_of_forall_ne g τ fun j hj => hin ⟨j, hj⟩) hi
theorem exists_sameStateNear (g : SharedInnerGas G G' Y Y' N m A A') (τ : g.Config) (j : G.InnerSpin Y m A)
    (hj : τ j ≠ Sum.inl ()) :
    ∃ (h₁ : (G.familyOf (g.extendFirst τ)).Occupies j.1.1)
      (h₂ : (G'.familyOf (g.extendSecond τ)).Occupies (g.spinEquiv j).1.1),
      SameStateNear j.1.1 (g.spinEquiv j).1.1 ((G.familyOf (g.extendFirst τ)).state h₁)
        ((G'.familyOf (g.extendSecond τ)).state h₂) Y Y' N := by
  obtain ⟨st, hst⟩ : ∃ st, τ j = Sum.inr st := by
    cases h : τ j with
    | inl u => exact absurd (by rw [h]) hj
    | inr st => exact ⟨st, rfl⟩
  obtain ⟨s', hv, hss⟩ := g.map_occupied j st
  have e1 : g.extendFirst τ j.1 = Sum.inr st := by rw [extendFirst_apply g τ j, hst]
  have e2 : g.extendSecond τ (g.spinEquiv j).1 = Sum.inr s' := by
    rw [extendSecond_apply g τ j, hst]
    exact hv
  obtain ⟨h₁, a₁⟩ := exists_occupies_of_apply_eq_inr e1
  obtain ⟨h₂, a₂⟩ := exists_occupies_of_apply_eq_inr e2
  exact ⟨h₁, h₂, by rw [a₁, a₂]; exact hss⟩
theorem familiesMatchNear_extend (B : MatchedBox G G' Y Y' N m) (hr : R.params.side ≤ 2 * R.range)
    (g : SharedInnerGas G G' Y Y' N m A A') {τ : g.Config} (hτ : IsCompatible g τ) :
    FamiliesMatchNear (G.familyOf (g.extendFirst τ)) (G'.familyOf (g.extendSecond τ)) Y Y' N := by
  classical
  have sep := G.coresDisjoint_familyOf (admissible_extendFirst g hτ) hr
  have sep' := G'.coresDisjoint_familyOf (admissible_extendSecond g hτ) hr
  have cs := fun j : G.InnerSpin Y m A =>
    core_mem_iff_of_sameSupport B (g.sameSupport j) j.2.core_near (g.spinEquiv j).2.core_near
  refine ⟨fun q hq => ?_, fun h o hh ho => ?_, fun h o hz hz' hh ho => ?_, fun h hh => ?_⟩
  · by_cases hex : ∃ j : G.InnerSpin Y m A, τ j ≠ Sum.inl () ∧ nearBond R.params.side Y q ∈ j.1.1.coreBonds
    · obtain ⟨j, hj, hb⟩ := hex
      obtain ⟨h₁, h₂, hss⟩ := exists_sameStateNear g τ j hj
      have hb' := (nearBond_mem_coreBonds_iff B (g.sameSupport j) (cs j) q hq).1 hb
      rw [fieldAt_eq_of_mem_coreBonds sep h₁ hb, fieldAt_eq_of_mem_coreBonds sep' h₂ hb']
      exact congrArg Sum.inr (hss.field_eq q hb hb' hq)
    · rw [fieldAt_eq_inl_of_forall_not_mem fun θ hθ hb => ?_, fieldAt_eq_inl_of_forall_not_mem fun θ hθ hb => ?_]
      · obtain ⟨j, rfl, hj⟩ := exists_inner_of_occupies_second g hθ
        exact hex ⟨j, hj, (nearBond_mem_coreBonds_iff B (g.sameSupport j) (cs j) q hq).2 hb⟩
      · obtain ⟨j, rfl, hj⟩ := exists_inner_of_occupies_first g hθ
        exact hex ⟨j, hj, hb⟩
  · rw [mem_sites_iff, mem_sites_iff]
    constructor
    · rintro ⟨θ, hθ, hz⟩
      obtain ⟨j, rfl, hj⟩ := exists_inner_of_occupies_first g hθ
      obtain ⟨_, h₂, _⟩ := exists_sameStateNear g τ j hj
      exact ⟨_, h₂, ((g.sameSupport j).sites_iff h o hh ho).1 hz⟩
    · rintro ⟨θ, hθ, hz⟩
      obtain ⟨j, rfl, hj⟩ := exists_inner_of_occupies_second g hθ
      obtain ⟨h₁, _, _⟩ := exists_sameStateNear g τ j hj
      exact ⟨_, h₁, ((g.sameSupport j).sites_iff h o hh ho).2 hz⟩
  · obtain ⟨θ, hθ, hzθ⟩ := mem_sites_iff.1 hz
    obtain ⟨j, rfl, hj⟩ := exists_inner_of_occupies_first g hθ
    obtain ⟨h₁, h₂, hss⟩ := exists_sameStateNear g τ j hj
    have hzθ' := ((g.sameSupport j).sites_iff h o hh ho).1 hzθ
    rw [GasFamily.labelAt_eq_of_mem _ sep hz h₁ hzθ, GasFamily.labelAt_eq_of_mem _ sep' hz' h₂ hzθ']
    exact hss.label_eq h o hzθ hzθ' hh ho
  · by_cases hex : ∃ j : G.InnerSpin Y m A, τ j ≠ Sum.inl () ∧ Y + siteOfInt h ∈ j.1.1.core
    · obtain ⟨j, hj, hy⟩ := hex
      obtain ⟨h₁, h₂, hss⟩ := exists_sameStateNear g τ j hj
      have hy' := (cs j h hh).1 hy
      rw [baseAt_eq_of_mem_core sep h₁ hy, baseAt_eq_of_mem_core sep' h₂ hy']
      exact congrArg Sum.inr (hss.base_eq h hy hy' hh)
    · rw [baseAt_eq_inl_of_forall_not_mem fun θ hθ hb => ?_, baseAt_eq_inl_of_forall_not_mem fun θ hθ hb => ?_]
      · obtain ⟨j, rfl, hj⟩ := exists_inner_of_occupies_second g hθ
        exact hex ⟨j, hj, (cs j h hh).2 hb⟩
      · obtain ⟨j, rfl, hj⟩ := exists_inner_of_occupies_first g hθ
        exact hex ⟨j, hj, hb⟩
end Shared
theorem settingsAgreeNear_of_awayFromFrames {s : ChartSetting R n} {s' : ChartSetting R n'} {M m' : ℕ}
    (hodd : Odd R.params.side) (hfit : R.params.Admissible) (hfr : FrameLocality.FrameCoordLocal)
    (hm₀ : 0 < R.frameReach) (hoff : SettingsAgreeAwayFromFrames s s' Y Y' M) (hm : m' + R.frameReach ≤ M)
    (hside : 4 * R.frameReach + 5 < n) (hside' : 4 * R.frameReach + 5 < n') : SettingsAgreeNear s s' Y Y' m' := by
  have hm'm : m' ≤ M := by omega
  refine ⟨by have := hoff.lt_extent; omega, by have := hoff.lt_extent'; omega, ?_,
    fun q hq => hoff.free_iff q ⟨offsetInBox_mono hm'm hq.1, hq.2⟩,
    fun q hq => hoff.fine_eq q ⟨offsetInBox_mono hm'm hq.1, hq.2⟩, ?_,
    fun h o hh ho => hoff.support_iff h o (offsetInBox_mono hm'm hh) ho,
    fun h o hz hz' hh ho => hoff.labelling_eq h o hz hz' (offsetInBox_mono hm'm hh) ho,
    fun h hh => hoff.bases_match h (offsetInBox_mono hm'm hh)⟩
  · intro b hb
    exact hoff.coarse_agree b ⟨offsetInBox_mono hm'm hb.1, offsetInBox_mono hm'm hb.2⟩
  · rintro ⟨h, o, i⟩ hq _
    have ho : o ∈ BlockAverages.centredCube R.params.side := hq.2
    have hh : OffsetInBox m' h := hq.1
    have hoff₁ := cellOffset_torusFrame_blockPoint (L := R.params.side) (n := n) R.depth hodd
      (fun i => ((Y i).cast : ℤ) + h i) o ho
    have hoff₂ := cellOffset_torusFrame_blockPoint (L := R.params.side) (n := n') R.depth hodd
      (fun i => ((Y' i).cast : ℤ) + h i) o ho
    refine hfr R.params R.anchorRadius R.depth R.frameReach n n' s.coarse s'.coarse _ _ hfit hm₀ hside hside' rfl
      (hoff₁.trans hoff₂.symm) ?_
    show FieldsAgreeNear s.coarse s'.coarse (parentBlock R.params.side (fineSite R.params.side Y h o))
      (parentBlock R.params.side (fineSite R.params.side Y' h o)) R.frameReach
    rw [parentBlock_fineSite hodd Y h o ho, parentBlock_fineSite hodd Y' h o ho]
    intro b hb
    have hbox : BondOffsetInBox M (h + b.1, b.2) := by
      constructor
      · intro l
        have h3 := abs_add_le (h l) (b.1 l)
        have h1 := hh l
        have h2 := hb.1 l
        show |h l + b.1 l| ≤ (M : ℤ)
        linarith
      · intro l
        have h1 := hh l
        have h2 : |(b.1 + Pi.single b.2 1 : Fin 4 → ℤ) l| ≤ (R.frameReach : ℤ) := hb.2 l
        have e : ((h + b.1) + Pi.single b.2 1 : Fin 4 → ℤ) l = h l + (b.1 + Pi.single b.2 1 : Fin 4 → ℤ) l := by
          simp only [Pi.add_apply]
          ring
        show |((h + b.1) + Pi.single b.2 1 : Fin 4 → ℤ) l| ≤ (M : ℤ)
        rw [e]
        have h3 := abs_add_le (h l) ((b.1 + Pi.single b.2 1 : Fin 4 → ℤ) l)
        linarith
    have hh₂ := hoff.coarse_agree (h + b.1, b.2) hbox
    have e1 : ∀ (k : ℕ) [NeZero k] (Z : TorusSite k),
        (bondFrom (Z + siteOfInt h) b).1 = (bondFrom Z (h + b.1, b.2)).1 := by
      intro k _ Z
      simp only [bondFrom]
      rw [add_assoc, ← siteOfInt_add]
    show s.coarse (bondFrom (Y + siteOfInt h) b).1 b.2 = s'.coarse (bondFrom (Y' + siteOfInt h) b).1 b.2
    rw [e1, e1]
    exact hh₂
theorem settingsAgreeNear_symm {p : ℕ} [NeZero p] {s s' : ChartSetting R p} {y : TorusSite p} {k : ℕ}
    (h : SettingsAgreeNear s s' y y k) : SettingsAgreeNear s' s y y k :=
  ⟨h.lt_extent', h.lt_extent, fun b hb => (h.coarse_agree b hb).symm, fun q hq => (h.free_iff q hq).symm,
    fun q hq hn => (h.fine_eq q hq fun c => hn ((h.free_iff q hq).1 c)).symm,
    fun q hq hn => (h.frame_eq q hq ((h.free_iff q hq).2 hn)).symm,
    fun a o ha ho => (h.support_iff a o ha ho).symm,
    fun a o hz hz' ha ho => (h.labelling_eq a o hz' hz ha ho).symm, fun a ha => by
      obtain ⟨o, ho, e, e'⟩ := h.bases_match a ha
      exact ⟨o, ho, e', e⟩⟩
theorem isGasFamily_familyOf {p : ℕ} [NeZero p] {H : GasGround R p} {σ : H.Config}
    (hadm : H.pairConstraint.IsAdmissible σ) : H.IsGasFamily (H.familyOf σ) := by
  refine ⟨fun θ h => ?_, fun θ θ' h h' hne => ?_⟩
  · obtain ⟨j, rfl, _⟩ := H.exists_spin_of_occupies h
    exact j.2
  · obtain ⟨j, rfl, hj⟩ := H.exists_spin_of_occupies h
    obtain ⟨j', rfl, hj'⟩ := H.exists_spin_of_occupies h'
    have hjj : j ≠ j' := fun e => hne (congrArg Subtype.val e)
    rcases hadm j j' hjj with e | e | e
    · exact absurd e hj
    · exact absurd e hj'
    · exact e
theorem settingsAgreeNear_update_of_far {p : ℕ} [NeZero p] {H : GasGround R p} (hCB : ComponentBesideFamily)
    (h8 : 2 ^ 8 * R.params.side ≤ R.range) (hρ : 0 < R.ballRadius) (hodd : Odd R.params.side)
    (h2 : 2 ≤ R.params.side) (hH : H.IsAdmissibleGround) {σ₀ : H.Config} {i : H.GasSpin} (hi : σ₀ i = Sum.inl ())
    {w : H.SpinValue i} (hset : (H.settingOf (H.familyOf σ₀)).IsAdmissible)
    (hadm0 : H.pairConstraint.IsAdmissible σ₀) (hadm : H.pairConstraint.IsAdmissible (Function.update σ₀ i w))
    {y : TorusSite p} {k : ℕ} (hne : i.1.core.Nonempty) (hfar : ∀ y₀ ∈ i.1.core, k + 2 ≤ supDist y₀ y) :
    SettingsAgreeNear (H.settingOf (H.familyOf σ₀)) (H.settingOf (H.familyOf (Function.update σ₀ i w))) y y k := by
  classical
  have hside : 2 * k + 2 < p := by
    obtain ⟨y₀, hy₀⟩ := hne
    have h1 := hfar y₀ hy₀
    have h3 := two_mul_supDist_le y₀ y
    omega
  cases w with
  | inl u =>
    have e : Function.update σ₀ i (Sum.inl u) = σ₀ := by
      have : (Sum.inl u : H.SpinValue i) = σ₀ i := by rw [hi]
      rw [this, Function.update_eq_self]
    rw [e]
    exact SettingShifts.settingsAgreeNear_refl _ hset y k hside
  | inr st =>
    rw [H.familyOf_update σ₀ i st]
    have hap : ∀ θ', (H.familyOf σ₀).Occupies θ' → i.1.FarApart θ' := by
      intro θ' h'
      obtain ⟨j, rfl, hj⟩ := H.exists_spin_of_occupies h'
      have hji : j ≠ i := fun e => hj (by rw [e]; exact hi)
      rcases hadm i j hji.symm with e | e | e
      · simp at e
      · rw [Function.update_of_ne hji] at e
        exact absurd e hj
      · exact e
    have hc := (hCB R p H (H.familyOf σ₀) h8 hρ hodd h2 hH (isGasFamily_familyOf hadm0)).2.2.2 i.1 st.1 i.2 hap hset
    exact settingsAgreeNear_symm (hc.2.2.1 y k hfar hside)
theorem extendFirst_update (g : SharedInnerGas G G' Y Y' N m A A') (τ : g.Config) (j : G.InnerSpin Y m A)
    (s : G.SpinValue j.1) :
    g.extendFirst (Function.update τ j s) =
      Function.update (g.extendFirst (Function.update τ j (Sum.inl ()))) j.1 s := by
  classical
  funext i
  by_cases e : i = j.1
  · subst e
    rw [Function.update_self, extendFirst_apply g _ j, Function.update_self]
  · rw [Function.update_of_ne e]
    by_cases hin : G.IsInnerSpin Y m A i
    · have hne : (⟨i, hin⟩ : G.InnerSpin Y m A) ≠ j := fun h => e (congrArg Subtype.val h)
      have a := extendFirst_apply g (Function.update τ j s) ⟨i, hin⟩
      have b := extendFirst_apply g (Function.update τ j (Sum.inl ())) ⟨i, hin⟩
      rw [Function.update_of_ne hne] at a b
      exact a.trans b.symm
    · rw [extendFirst_of_not_inner g _ hin, extendFirst_of_not_inner g _ hin]
theorem extendSecond_update (g : SharedInnerGas G G' Y Y' N m A A') (τ : g.Config) (j : G.InnerSpin Y m A)
    (s : G.SpinValue j.1) :
    g.extendSecond (Function.update τ j s) =
      Function.update (g.extendSecond (Function.update τ j (Sum.inl ()))) (g.spinEquiv j).1 (g.valueEquiv j s) := by
  classical
  funext i
  by_cases e : i = (g.spinEquiv j).1
  · subst e
    rw [Function.update_self, extendSecond_apply g _ j, Function.update_self]
  · rw [Function.update_of_ne e]
    by_cases hex : ∃ j₂ : G.InnerSpin Y m A, (g.spinEquiv j₂).1 = i
    · obtain ⟨j₂, rfl⟩ := hex
      have hne : j₂ ≠ j := fun h => e (by rw [h])
      rw [extendSecond_apply g _ j₂, extendSecond_apply g _ j₂, Function.update_of_ne hne, Function.update_of_ne hne]
    · have hoff : ∀ j₂ : G.InnerSpin Y m A, (g.spinEquiv j₂).1 ≠ i := fun j₂ hj => hex ⟨j₂, hj⟩
      rw [extendSecond_of_forall_ne g _ hoff, extendSecond_of_forall_ne g _ hoff]
theorem core_nonempty {p : ℕ} [NeZero p] {H : GasGround R p} (i : H.GasSpin) : i.1.core.Nonempty := by apply _root_.YangMills.Construction.StepGas.core_nonempty_of_gasSpin <;> assumption
set_option maxHeartbeats 1000000 in
theorem pairedSettings_update (hCB : ComponentBesideFamily) (hFr : FrameLocality.FrameCoordLocal)
    (B : MatchedBox G G' Y Y' N m) (hfit : R.params.Admissible) (h8 : 2 ^ 8 * R.params.side ≤ R.range)
    (hρ : 0 < R.ballRadius) (h2L : 2 ≤ R.params.side) (hm₀ : 0 < R.frameReach) (hr2 : R.params.side ≤ 2 * R.range)
    (hside : 4 * R.frameReach + 5 < n) (hside' : 4 * R.frameReach + 5 < n') (hG : G.IsAdmissibleGround)
    (hG' : G'.IsAdmissibleGround) (g : SharedInnerGas G G' Y Y' N m A A') (τ : g.Config) (j : G.InnerSpin Y m A)
    (s : G.SpinValue j.1) (d k : ℕ) (hadm : G.pairConstraint.IsAdmissible (g.extendFirst (Function.update τ j s)))
    (hpl : ∀ h ∈ G.coreOffsets Y m j.1, ∀ l, |h l| ≤ ((N - R.frameReach - (k + d) : ℕ) : ℤ))
    (hkd : k + d ≤ N - R.frameReach)
    (set₀ : (G.settingOf (G.familyOf (g.extendFirst (Function.update τ j (Sum.inl ()))))).IsAdmissible)
    (set₀' : (G'.settingOf (G'.familyOf (g.extendSecond (Function.update τ j (Sum.inl ()))))).IsAdmissible) :
    PairedSettings
        (G.settingOf (G.familyOf (g.extendFirst (Function.update τ j (Sum.inl ())))))
        (G.settingOf (G.familyOf (g.extendFirst (Function.update τ j s))))
        (G'.settingOf (G'.familyOf (g.extendSecond (Function.update τ j (Sum.inl ())))))
        (G'.settingOf (G'.familyOf (g.extendSecond (Function.update τ j s))))
        (G.coreOffsets Y m j.1) Y Y' d k := by
  classical
  have hodd := hfit.L_odd
  have hn := B.groundsAgree.lt_extent
  have hn' := B.groundsAgree.lt_extent'
  have sh1 := isCompatible_of_admissible g hadm
  have sh0 := isCompatible_update_vacant g sh1
  have M₁ := familiesMatchNear_extend B hr2 g sh1
  have M₀ := familiesMatchNear_extend B hr2 g sh0
  have hgap := B.radius_eq
  have ag₁ := settingsAgreeNear_of_awayFromFrames (M := N) (m' := N - R.frameReach) hodd hfit hFr hm₀
    (settingsAgreeAwayFromFrames_of_match hodd B.two_le B.two_le' B.groundsAgree M₁) (by omega) hside hside'
  have ag₀ := settingsAgreeNear_of_awayFromFrames (M := N) (m' := N - R.frameReach) hodd hfit hFr hm₀
    (settingsAgreeAwayFromFrames_of_match hodd B.two_le B.two_le' B.groundsAgree M₀) (by omega) hside hside'
  have ad₀ := admissible_extendFirst g sh0
  have ad₀' := admissible_extendSecond g sh0
  have ad₁ := admissible_extendFirst g sh1
  have ad₁' := admissible_extendSecond g sh1
  have hcs := core_mem_iff_of_sameSupport B (g.sameSupport j) j.2.core_near (g.spinEquiv j).2.core_near
  have memH : ∀ h, OffsetInBox m h → Y + siteOfInt h ∈ j.1.1.core → h ∈ G.coreOffsets Y m j.1 := by
    intro h hh hc
    refine Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun i => Finset.mem_Icc.2 (abs_le.1 (hh i)), hc⟩
  have hbound : ∀ h ∈ G.coreOffsets Y m j.1, ∀ g₁, OffsetInBox (d - 1) g₁ → ∀ l,
      |(h + g₁) l| + k ≤ ((N - R.frameReach : ℕ) : ℤ) := by
    intro h hh g₁ hg l
    have b1 := hpl h hh l
    have b2 : |g₁ l| ≤ ((d - 1 : ℕ) : ℤ) := hg l
    have b3 : |(h + g₁) l| ≤ |h l| + |g₁ l| := abs_add_le _ _
    have b4 : ((N - R.frameReach - (k + d) : ℕ) : ℤ) + ((d - 1 : ℕ) : ℤ) + (k : ℤ) ≤
        ((N - R.frameReach : ℕ) : ℤ) := by omega
    linarith
  have hboxN : ∀ h ∈ G.coreOffsets Y m j.1, ∀ g₁, OffsetInBox (d - 1) g₁ → OffsetInBox N (h + g₁) := by
    intro h hh g₁ hg l
    have b1 := hbound h hh g₁ hg l
    have b2 : ((N - R.frameReach : ℕ) : ℤ) ≤ (N : ℤ) := by omega
    have b3 : (0 : ℤ) ≤ k := by positivity
    linarith
  refine ⟨fun y₀ k₀ hfar => ?_, fun y₀ k₀ hfar => ?_,
    fun h hh g₁ hg => SettingShifts.settingsAgreeNear_shift ag₀ (hbound h hh g₁ hg),
    fun h hh g₁ hg => SettingShifts.settingsAgreeNear_shift ag₁ (hbound h hh g₁ hg),
    fun h hh h₂ hh₂ g₁ g₂ hg hg₂ => ?_, fun h hh h₂ hh₂ g₁ g₂ hg hg₂ => ?_⟩
  · rw [extendFirst_update g τ j s] at ad₁ ⊢
    refine settingsAgreeNear_update_of_far hCB h8 hρ hodd h2L hG ?_ set₀ ad₀ ad₁ (core_nonempty j.1)
      fun y₁ hy₁ => ?_
    · rw [extendFirst_apply g _ j, Function.update_self]
    · obtain ⟨h, hh, rfl⟩ := j.2.core_near y₁ hy₁
      rw [supDist_comm]
      exact hfar h (memH h hh hy₁)
  · rw [extendSecond_update g τ j s] at ad₁' ⊢
    refine settingsAgreeNear_update_of_far hCB h8 hρ hodd h2L hG' ?_ set₀' ad₀' ad₁'
      (core_nonempty (g.spinEquiv j).1) fun y₁ hy₁ => ?_
    · rw [extendSecond_apply g _ j, Function.update_self]
      exact g.map_vacant j
    · obtain ⟨h, hh, rfl⟩ := (g.spinEquiv j).2.core_near y₁ hy₁
      rw [supDist_comm]
      exact hfar h (memH h hh ((hcs h (offsetInBox_mono (by omega) hh)).2 hy₁))
  · exact ⟨fun e => eq_of_add_siteOfInt_eq hn (hboxN h hh g₁ hg) (hboxN h₂ hh₂ g₂ hg₂) e, fun e => by rw [e]⟩
  · exact ⟨fun e => eq_of_add_siteOfInt_eq hn' (hboxN h hh g₁ hg) (hboxN h₂ hh₂ g₂ hg₂) e, fun e => by rw [e]⟩
end Grounds
end SharedGasSettings
open SharedGasSettings in
theorem sharedGasSettingsPaired_holds (hConf : GasConfigIsAdmissibleSetting) (hCB : ComponentBesideFamily)
    (hFr : FrameLocality.FrameCoordLocal) (hFl : StepFloors.EventuallyFloorConditions) :
    SharedGasSettingsPaired := by
  classical
  refine ⟨fun _ => 1, fun _ => one_pos, fun T hT _ => ?_⟩
  obtain ⟨y₁, h₁⟩ := hConf T hT
  obtain ⟨y₂, h₂⟩ := hFl T hT (2 ^ 20 * ((T.side : ℝ) + 1)) 1 (by positivity) one_pos
  refine ⟨max y₁ (max y₂ T.floorMin),
    fun y hy R hR hx n n' _ _ G G' Y Y' N A A' g τ j s d k hG hG' hN hag hbl hadm hpl hkd => ?_⟩
  obtain ⟨a₁, hy⟩ := max_le_iff.mp hy
  obtain ⟨a₂, a₃⟩ := max_le_iff.mp hy
  have hfit : R.params.Admissible := by
    rw [hR.params_eq]
    exact hT.fits y a₃
  have hLL : R.params.side = T.side := by
    rw [hR.params_eq]
    rfl
  have hr : 2 ^ 20 * (R.params.side + 1) ≤ R.range := by
    have := (h₂ R.coupling (a₂.trans hR.le_coupling)).range_ge
    show 2 ^ 20 * (R.params.side + 1) ≤ clusterRange R.coupling
    rw [hLL]
    exact_mod_cast this
  have hL := hfit.L_ge
  have hm₀ : R.frameReach = R.range / 2 ^ 11 := rfl
  have hm2 : 2 ≤ R.frameReach := by
    rw [hm₀]
    have : 2 ^ 20 ≤ R.range := by nlinarith
    omega
  have hbig : 16 * R.range ≤ R.params.side * R.frameReach := by
    have h1 : R.range < 2 ^ 11 * (R.frameReach + 1) := by
      rw [hm₀]
      omega
    calc 16 * R.range ≤ 2 ^ 16 * R.frameReach := by omega
      _ ≤ R.params.side * R.frameReach := Nat.mul_le_mul_right _ hL
  have hρ : 0 < R.ballRadius := by
    have := hfit.σ_pos
    unfold StepSetup.ballRadius
    positivity
  have h8 : 2 ^ 8 * R.params.side ≤ R.range := by nlinarith
  have hr2 : R.params.side ≤ 2 * R.range := by nlinarith
  have h2L : 2 ≤ R.params.side := by omega
  have B : MatchedBox G G' Y Y' N (N - R.frameReach - 1) := ⟨hfit.L_odd, hag, by omega, hbig⟩
  have hn := hag.lt_extent
  have hn' := hag.lt_extent'
  have sh1 := isCompatible_of_admissible g hadm
  have sh0 := isCompatible_update_vacant g sh1
  exact pairedSettings_update hCB hFr B hfit h8 hρ h2L (by omega) hr2 (by omega) (by omega) hG hG' g τ j s d k hadm
    (fun h hh => hpl h hh) hkd (h₁ y a₁ R hR hx n G hG _ (admissible_extendFirst g sh0))
    (h₁ y a₁ R hR hx n' G' hG' _ (admissible_extendSecond g sh0))
end ClusterExpansionOfAStep
end YangMills.Construction
end
