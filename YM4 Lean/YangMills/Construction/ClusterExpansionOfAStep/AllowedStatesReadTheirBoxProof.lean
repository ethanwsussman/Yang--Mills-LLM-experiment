import YangMills.Construction.ClusterExpansionOfAStep.AllowedStatesReadTheirBox
import YangMills.Construction.ClusterExpansionOfAStep.CostsOfTwoSettingsProof
import YangMills.Construction.ClusterExpansionOfAStep.FloorsOfTheParameters
import YangMills.Construction.ClusterExpansionOfAStep.GasesEqualInBoxes
import YangMills.Construction.ClusterExpansionOfAStep.GroundHasWeightAtItsFrames
import YangMills.Construction.HoleBesideASecondHole.CoreAndHolesAsSites
import YangMills.Construction.SeparatedSequences.ObjectsUpToTheLastNonEmptyMemberProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction
open BlockAverages LumpContours BlockTrees BlockZones CongruentBoxes CongruentAdmission BoxAgreement TorusFields
  TorusLumps StepGas StepSettings StepCosts BlockOffsets BlockPlaces
namespace InBoxTransfer
variable {R : StepSetup} {n : ℕ} [NeZero n]
section Places
variable {L : ℕ} [NeZero L]
theorem supDist_le_of_parentBlock_eq {x z : TorusSite (n * L)} (h : parentBlock L x = parentBlock L z) :
    _root_.YangMills.Construction.TorusFields.supDist x z ≤ L := by apply _root_.YangMills.Construction.TorusLumps.supDist_le_of_parentBlock_eq <;> assumption
theorem supDist_le_two_of_mem_plaquetteVertices {m : ℕ} [NeZero m] {x z : TorusSite m} {μ ν : Fin 4}
    (hz : z ∈ plaquetteVertices x μ ν) : _root_.YangMills.Construction.TorusFields.supDist x z ≤ 2 := by
  have a := _root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le (n := m) x μ
  have b := _root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le (n := m) x ν
  have c := _root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le (n := m) (x + TorusFields.unitStep m μ) ν
  have s1 := _root_.YangMills.Construction.TorusFields.supDist_triangle x (x + TorusFields.unitStep m μ) (x + TorusFields.unitStep m μ + TorusFields.unitStep m ν)
  simp only [plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega
  · omega
  · omega
  · omega
theorem torusSiteInFrame_one_add (x y : TorusSite n) :
    torusSiteInFrame (stepBlockFrame L n) 1 (x + y) =
      torusSiteInFrame (stepBlockFrame L n) 1 x + torusSiteInFrame (stepBlockFrame L n) 1 y := by
  funext i
  exact intCast_cast_add (stepBlockFrame_period_one i) (x i) (y i)
theorem torusSiteInFrame_one_add_siteOfInt (x : TorusSite n) (h : Fin 4 → ℤ) :
    torusSiteInFrame (stepBlockFrame L n) 1 x + siteOfCoords 1 h =
      torusSiteInFrame (stepBlockFrame L n) 1 (x + siteOfInt h) := by
  rw [torusSiteInFrame_one_add]
  congr 1
  funext k
  exact (intCast_cast_intCast (stepBlockFrame_period_one k) _).symm
theorem plaquetteDefect_readAtLevel (W : TorusField (n * L)) (x : TorusSite (n * L)) (μ ν : Fin 4) :
    plaquetteDefect (readAtLevel (stepBlockFrame L n) 0 W) (torusSiteInFrame (stepBlockFrame L n) 0 x, μ, ν) =
      curvature W x μ ν := by
  unfold plaquetteDefect curvature holonomy
  set ι := torusSiteInFrame (n := n * L) (stepBlockFrame L n) 0 with hι
  have a1 : ι x + BlockAverages.unitStep 0 μ = ι (x + TorusFields.unitStep (n * L) μ) := by
    rw [hι, torusSiteInFrame_add, torusSiteInFrame_unitStep]
  have a2 : ι (x + TorusFields.unitStep (n * L) μ) + BlockAverages.unitStep 0 ν - BlockAverages.unitStep 0 μ =
      ι (x + TorusFields.unitStep (n * L) ν) := by
    rw [hι, torusSiteInFrame_add, torusSiteInFrame_add, torusSiteInFrame_unitStep, torusSiteInFrame_unitStep]
    abel
  have a3 : ι (x + TorusFields.unitStep (n * L) μ) + BlockAverages.unitStep 0 ν + -BlockAverages.unitStep 0 μ -
      BlockAverages.unitStep 0 ν = ι x := by
    rw [hι, torusSiteInFrame_add, torusSiteInFrame_unitStep]
    abel
  have hv : plaquetteHolonomy (readAtLevel (stepBlockFrame L n) 0 W) (ι x, μ, ν) =
      W x μ * W (x + TorusFields.unitStep (n * L) μ) ν * (W (x + TorusFields.unitStep (n * L) ν) μ)⁻¹ * (W x ν)⁻¹ := by
    simp only [plaquetteHolonomy, pathHolonomy, linkValue, stepDisplacement, if_true, Bool.false_eq_true, if_false,
      mul_one, a2, a3, a1, mul_assoc]
    rw [readAtLevel_torusSiteInFrame (stepBlockFrame L n) 0 stepBlockFrame_period_zero W x μ,
      readAtLevel_torusSiteInFrame (stepBlockFrame L n) 0 stepBlockFrame_period_zero W _ ν,
      readAtLevel_torusSiteInFrame (stepBlockFrame L n) 0 stepBlockFrame_period_zero W _ μ,
      readAtLevel_torusSiteInFrame (stepBlockFrame L n) 0 stepBlockFrame_period_zero W x ν]
  rw [hv]
theorem supDist_le_parentBlock (x z : TorusSite (n * L)) :
    _root_.YangMills.Construction.TorusFields.supDist x z ≤ L * (_root_.YangMills.Construction.TorusFields.supDist (parentBlock L x) (parentBlock L z) + 2) := by
  obtain ⟨e, he, hb⟩ := exists_offset_of_supDist (parentBlock L x) (parentBlock L z)
  have hx := BlockPlaces.blockSite_parentBlock_siteOffset x
  have hz := BlockPlaces.blockSite_parentBlock_siteOffset z
  set d : Fin 4 → ℤ := fun i => (L : ℤ) * e i + ((((siteOffset (L := L) z i : Fin L) : ℕ) : ℤ) -
    (((siteOffset (L := L) x i : Fin L) : ℕ) : ℤ)) with hd
  have hzx : z = x + siteOfInt d := by
    rw [← hz, ← hx]
    funext i
    simp only [blockSite, siteOfInt, Pi.add_apply, ← Int.cast_add]
    apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2
    have hi := congrFun he i
    simp only [Pi.add_apply, siteOfInt] at hi
    have h1 : (((parentBlock L z i).cast : ℤ) : ZMod n) =
        ((((parentBlock L x i).cast : ℤ) + e i : ℤ) : ZMod n) := by
      rw [ZMod.intCast_zmod_cast, Int.cast_add, ZMod.intCast_zmod_cast]
      exact hi
    obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h1
    refine ⟨k, ?_⟩
    push_cast at hk ⊢
    simp only [hd]
    linear_combination (L : ℤ) * hk
  have hfin : _root_.YangMills.Construction.TorusFields.supDist x (x + siteOfInt d) ≤ L * (_root_.YangMills.Construction.TorusFields.supDist (parentBlock L x) (parentBlock L z) + 2) := by
   refine _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le _ _ _ fun i => ?_
   have h1 := (siteOffset (L := L) x i).isLt
   have h2 := (siteOffset (L := L) z i).isLt
   have h3 := hb i
   set D := _root_.YangMills.Construction.TorusFields.supDist (parentBlock L x) (parentBlock L z)
   have h4 : L * (e i).natAbs ≤ L * D := Nat.mul_le_mul_left _ h3
   simp only [hd]
   have h5 : ((L : ℤ) * e i).natAbs = L * (e i).natAbs := by
     rw [Int.natAbs_mul]
     simp
   have h6 := Int.natAbs_add_le ((L : ℤ) * e i) ((((siteOffset (L := L) z i : Fin L) : ℕ) : ℤ) -
     (((siteOffset (L := L) x i : Fin L) : ℕ) : ℤ))
   have h7 : ((((siteOffset (L := L) z i : Fin L) : ℕ) : ℤ) - (((siteOffset (L := L) x i : Fin L) : ℕ) : ℤ)).natAbs ≤ L := by
     omega
   have h8 : L * (D + 2) = L * D + 2 * L := by ring
   omega
  rwa [← hzx] at hfin
end Places
section Classes
variable {m : ℕ} [NeZero m] {r : ℕ} {Y Y₁ : Finset (TorusSite m)}
theorem chainConnected_of_separated (hsep : ∀ u ∈ Y₁, ∀ v ∈ Y, v ∉ Y₁ → r < _root_.YangMills.Construction.TorusFields.supDist u v) {z w : TorusSite m}
    (hz : z ∈ Y₁) (h : ChainConnected r Y z w) : w ∈ Y₁ ∧ ChainConnected r Y₁ z w := by
  induction h with
  | refl => exact ⟨hz, Relation.ReflTransGen.refl⟩
  | @tail c d _ hs ih =>
    obtain ⟨h1, h2⟩ := ih
    have hmem : d ∈ Y₁ := by
      by_contra hc
      have := hsep _ h1 _ hs.2.1 hc
      omega
    exact ⟨hmem, h2.tail ⟨h1, hmem, hs.2.2⟩⟩
theorem chainConnected_mono (hsub : Y₁ ⊆ Y) {z w : TorusSite m} (h : ChainConnected r Y₁ z w) :
    ChainConnected r Y z w := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.tail ⟨hsub hs.1, hsub hs.2.1, hs.2.2⟩
open Classical in
theorem mem_chainComponents_of_separated (hsub : Y₁ ⊆ Y) (hsep : ∀ u ∈ Y₁, ∀ v ∈ Y, v ∉ Y₁ → r < _root_.YangMills.Construction.TorusFields.supDist u v)
    {X : Finset (TorusSite m)} (hX : X ∈ chainComponents r Y) {z : TorusSite m} (hz : z ∈ X) (hz₁ : z ∈ Y₁) :
    X ∈ chainComponents r Y₁ ∧ X ⊆ Y₁ := by
  have e : X = Y₁.filter (ChainConnected r Y₁ z) := by
    rw [eq_filter_of_mem_chainComponents hX hz]
    ext w
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨_, hj⟩
      exact chainConnected_of_separated hsep hz₁ hj
    · rintro ⟨h1, h2⟩
      exact ⟨hsub h1, chainConnected_mono hsub h2⟩
  refine ⟨mem_chainComponents.mpr ⟨z, hz₁, e⟩, ?_⟩
  rw [e]
  exact Finset.filter_subset _ _
open Classical in
theorem exists_mem_of_mem_chainComponents {X : Finset (TorusSite m)} (hX : X ∈ chainComponents r Y) : ∃ z, z ∈ X := by
  obtain ⟨y, hy, rfl⟩ := mem_chainComponents.mp hX
  exact ⟨y, Finset.mem_filter.mpr ⟨hy, Relation.ReflTransGen.refl⟩⟩
end Classes
section Data
theorem eq_inr_getRight {α : Type} (a : WithNone α) (h : a.isRight = true) : a = Sum.inr (a.getRight h) := by
  cases a with
  | inl u => simp at h
  | inr s => rfl
variable {γ γ' : GasFamily R n} {θ θ' : GasSupport R n}
theorem eq_inr_state (h : γ.Occupies θ) : γ θ = Sum.inr (γ.state h) := eq_inr_getRight _ h
theorem single_apply_self (s : SupportState θ) : GasFamily.single θ s θ = Sum.inr s := by
  classical
  unfold GasFamily.single
  rw [Function.update_self]
theorem single_apply_of_ne (s : SupportState θ) (h : θ' ≠ θ) : GasFamily.single θ s θ' = Sum.inl () := by
  classical
  unfold GasFamily.single
  rw [Function.update_of_ne h]
  rfl
theorem not_occupies_empty : ¬ (GasFamily.empty : GasFamily R n).Occupies θ := by
  unfold GasFamily.Occupies GasFamily.empty
  simp
theorem occupies_single_iff (s : SupportState θ) : (GasFamily.single θ s).Occupies θ' ↔ θ' = θ := by
  unfold GasFamily.Occupies
  constructor
  · intro h
    by_contra hc
    rw [single_apply_of_ne s hc] at h
    simp at h
  · rintro rfl
    rw [single_apply_self]
    rfl
theorem exists_choose_congr {α : Type*} {p q : α → Prop} (hpq : p = q) (h : ∃ a, p a) (h' : ∃ a, q a) :
    h.choose = h'.choose := by apply _root_.YangMills.Construction.SeparatedClasses.LastNonempty.choose_eq_of_eq <;> assumption
theorem state_congr (e : γ θ = γ' θ) (h₁ : γ.Occupies θ) (h₂ : γ'.Occupies θ) : γ.state h₁ = γ'.state h₂ := by
  have key : ∀ (a b : WithNone (SupportState θ)), a = b → ∀ (h₁ : a.isRight = true) (h₂ : b.isRight = true),
      a.getRight h₁ = b.getRight h₂ := by
    intro a b e
    subst e
    intro _ _
    rfl
  exact key _ _ e h₁ h₂
theorem occupies_congr (e : γ θ = γ' θ) : γ.Occupies θ ↔ γ'.Occupies θ := by
  unfold GasFamily.Occupies
  rw [e]
theorem fieldAt_congr {b : TorusBond (n * R.params.side)}
    (h : ∀ θ : GasSupport R n, b ∈ θ.coreBonds → γ θ = γ' θ) : γ.fieldAt b = γ'.fieldAt b := by
  classical
  have hp : (fun θ : GasSupport R n => γ.Occupies θ ∧ b ∈ θ.coreBonds) = fun θ => γ'.Occupies θ ∧ b ∈ θ.coreBonds := by
    funext θ
    apply propext
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(occupies_congr (h θ h2)).mp h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(occupies_congr (h θ h2)).mpr h1, h2⟩
  have hiff : (∃ θ, γ.Occupies θ ∧ b ∈ θ.coreBonds) ↔ ∃ θ, γ'.Occupies θ ∧ b ∈ θ.coreBonds :=
    exists_congr fun θ => iff_of_eq (congrFun hp θ)
  unfold GasFamily.fieldAt
  by_cases hx : ∃ θ, γ.Occupies θ ∧ b ∈ θ.coreBonds
  · have hx' := hiff.mp hx
    rw [dif_pos hx, dif_pos hx']
    have hc : hx.choose = hx'.choose := exists_choose_congr hp hx hx'
    have key : ∀ (θ₁ θ₂ : GasSupport R n), θ₁ = θ₂ → ∀ (h₁ : γ.Occupies θ₁) (h₂ : γ'.Occupies θ₂)
        (m₁ : b ∈ θ₁.coreBonds) (m₂ : b ∈ θ₂.coreBonds), (γ.state h₁).1 ⟨b, m₁⟩ = (γ'.state h₂).1 ⟨b, m₂⟩ := by
      intro θ₁ θ₂ e h₁ h₂ m₁ m₂
      subst e
      rw [state_congr (h θ₁ m₁) h₁ h₂]
    exact congrArg Sum.inr (key _ _ hc _ _ _ _)
  · have hx' := fun c => hx (hiff.mpr c)
    rw [dif_neg hx, dif_neg hx']
theorem baseAt_congr {y : TorusSite n}
    (h : ∀ θ : GasSupport R n, y ∈ θ.core → γ θ = γ' θ) : γ.baseAt y = γ'.baseAt y := by
  classical
  have hp : (fun θ : GasSupport R n => γ.Occupies θ ∧ y ∈ θ.core) = fun θ => γ'.Occupies θ ∧ y ∈ θ.core := by
    funext θ
    apply propext
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(occupies_congr (h θ h2)).mp h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(occupies_congr (h θ h2)).mpr h1, h2⟩
  have hiff : (∃ θ, γ.Occupies θ ∧ y ∈ θ.core) ↔ ∃ θ, γ'.Occupies θ ∧ y ∈ θ.core :=
    exists_congr fun θ => iff_of_eq (congrFun hp θ)
  unfold GasFamily.baseAt
  by_cases hx : ∃ θ, γ.Occupies θ ∧ y ∈ θ.core
  · have hx' := hiff.mp hx
    rw [dif_pos hx, dif_pos hx']
    have hc : hx.choose = hx'.choose := exists_choose_congr hp hx hx'
    have key : ∀ (θ₁ θ₂ : GasSupport R n), θ₁ = θ₂ → ∀ (h₁ : γ.Occupies θ₁) (h₂ : γ'.Occupies θ₂)
        (m₁ : y ∈ θ₁.core) (m₂ : y ∈ θ₂.core), (γ.state h₁).2.2 ⟨y, m₁⟩ = (γ'.state h₂).2.2 ⟨y, m₂⟩ := by
      intro θ₁ θ₂ e h₁ h₂ m₁ m₂
      subst e
      rw [state_congr (h θ₁ m₁) h₁ h₂]
    exact congrArg Sum.inr (key _ _ hc _ _ _ _)
  · have hx' := fun c => hx (hiff.mpr c)
    rw [dif_neg hx, dif_neg hx']
theorem mem_sites_iff {z : TorusSite (n * R.params.side)} : z ∈ γ.sites ↔ ∃ θ, γ.Occupies θ ∧ z ∈ θ.2 := by
  classical
  constructor
  · exact GasFamily.exists_of_mem_sites
  · rintro ⟨θ, h1, h2⟩
    exact Finset.mem_biUnion.mpr ⟨θ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩, h2⟩
theorem mem_sites_single (s : SupportState θ) {z : TorusSite (n * R.params.side)} :
    z ∈ (GasFamily.single θ s).sites ↔ z ∈ θ.2 := by
  rw [mem_sites_iff]
  constructor
  · rintro ⟨θ', h1, h2⟩
    rw [(occupies_single_iff s).mp h1] at h2
    exact h2
  · intro h
    exact ⟨θ, (occupies_single_iff s).mpr rfl, h⟩
theorem not_mem_sites_empty {z : TorusSite (n * R.params.side)} : z ∉ (GasFamily.empty : GasFamily R n).sites := by
  rw [mem_sites_iff]
  rintro ⟨θ', h1, _⟩
  exact not_occupies_empty h1
end Data
section EvaluationMaps
variable {G : GasGround R n} {γ γ₁ : GasFamily R n}
theorem free_subset_chartBonds : (G.settingOf γ).free ⊆ chartBonds R.params.side n := by
  classical
  intro b hb
  have h := (mem_free_settingOf hb).1
  unfold markedBonds at h
  exact (Finset.mem_filter.mp h).1
theorem free_subset_chartBonds_withFamily : (G.settingWithFamily γ).free ⊆ chartBonds R.params.side n :=
  free_subset_chartBonds
theorem fine_eq_field_zero (hL : Odd R.params.side) (hn : 2 ≤ n) :
    (G.settingOf γ).fine = (G.settingOf γ).field 0 := by
  classical
  have htr : ∀ x, blockGauge R.params.side (G.settingOf γ).fine x =
      blockGauge R.params.side (G.settingWithFamily γ).fine x := fun x =>
    blockGauge_field free_subset_chartBonds_withFamily hL hn 0 x
  funext x i
  show (G.settingWithFamily γ).field 0 x i = (G.settingOf γ).field 0 x i
  unfold ChartSetting.field
  by_cases hf : (x, i) ∈ (G.settingWithFamily γ).free
  · rw [dif_pos hf, dif_pos (show (x, i) ∈ (G.settingOf γ).free from hf)]
    unfold chartLink
    show (blockGauge R.params.side (G.settingWithFamily γ).fine x)⁻¹ * _ *
        blockGauge R.params.side (G.settingWithFamily γ).fine (x + TorusFields.unitStep (n * R.params.side) i) =
      (blockGauge R.params.side (G.settingOf γ).fine x)⁻¹ * _ *
        blockGauge R.params.side (G.settingOf γ).fine (x + TorusFields.unitStep (n * R.params.side) i)
    rw [htr, htr]
    rfl
  · rw [dif_neg hf, dif_neg (show (x, i) ∉ (G.settingOf γ).free from hf)]
    show _ = (G.settingWithFamily γ).field 0 x i
    unfold ChartSetting.field
    rw [dif_neg hf]
theorem field_zero_eq_frameField (hL : Odd R.params.side) (hn : 2 ≤ n) :
    (G.settingOf γ).field 0 = G.frameField γ :=
  (fine_eq_field_zero hL hn).symm
def AgreeNear (γ γ₁ : GasFamily R n) (x : TorusSite (n * R.params.side)) (d : ℕ) : Prop :=
  ∀ θ : GasSupport R n, ∀ u, _root_.YangMills.Construction.TorusFields.supDist x u ≤ d → parentBlock R.params.side u ∈ θ.core → γ θ = γ₁ θ
theorem settingWithFamily_fine_congr (x : TorusSite (n * R.params.side)) (i : Fin 4)
    (h : ∀ θ : GasSupport R n, (x, i) ∈ θ.coreBonds → γ θ = γ₁ θ) :
    (G.settingWithFamily γ).fine x i = (G.settingWithFamily γ₁).fine x i := by
  simp only [GasGround.settingWithFamily]
  rw [fieldAt_congr h]
theorem blockGauge_settingWithFamily_congr (hL : Odd R.params.side) (hn : 2 ≤ n) {x : TorusSite (n * R.params.side)}
    (h : ∀ θ : GasSupport R n, parentBlock R.params.side x ∈ θ.core → γ θ = γ₁ θ) :
    blockGauge R.params.side (G.settingWithFamily γ).fine x = blockGauge R.params.side (G.settingWithFamily γ₁).fine x := by
  classical
  apply blockGauge_congr hL hn
  intro z i hz _
  apply settingWithFamily_fine_congr
  intro θ hst
  apply h
  rw [← hz]
  exact (Finset.mem_filter.mp hst).2.1
theorem frameField_congr (hL : Odd R.params.side) (hn : 2 ≤ n) {x : TorusSite (n * R.params.side)} {i : Fin 4}
    (h : ∀ θ : GasSupport R n, parentBlock R.params.side x ∈ θ.core ∨
      parentBlock R.params.side (x + TorusFields.unitStep (n * R.params.side) i) ∈ θ.core → γ θ = γ₁ θ) :
    G.frameField γ x i = G.frameField γ₁ x i := by
  classical
  have hst : ∀ θ : GasSupport R n, (x, i) ∈ θ.coreBonds → γ θ = γ₁ θ := fun θ hs =>
    h θ (Or.inl (Finset.mem_filter.mp hs).2.1)
  have hf : γ.fieldAt (x, i) = γ₁.fieldAt (x, i) := fieldAt_congr hst
  have t1 := blockGauge_settingWithFamily_congr (G := G) hL hn (x := x) fun θ hθ => h θ (Or.inl hθ)
  have t2 := blockGauge_settingWithFamily_congr (G := G) hL hn (x := x + TorusFields.unitStep (n * R.params.side) i)
    fun θ hθ => h θ (Or.inr hθ)
  have hiff : (x, i) ∈ (G.settingWithFamily γ).free ↔ (x, i) ∈ (G.settingWithFamily γ₁).free := by
    show (x, i) ∈ G.freeBonds.filter (fun b => γ.fieldAt b = Sum.inl ()) ↔
      (x, i) ∈ G.freeBonds.filter (fun b => γ₁.fieldAt b = Sum.inl ())
    simp only [Finset.mem_filter]
    rw [hf]
  show (G.settingWithFamily γ).field 0 x i = (G.settingWithFamily γ₁).field 0 x i
  unfold ChartSetting.field
  by_cases hm : (x, i) ∈ (G.settingWithFamily γ).free
  · rw [dif_pos hm, dif_pos (hiff.mp hm)]
    unfold chartLink
    show (blockGauge R.params.side (G.settingWithFamily γ).fine x)⁻¹ * _ *
        blockGauge R.params.side (G.settingWithFamily γ).fine (x + TorusFields.unitStep (n * R.params.side) i) =
      (blockGauge R.params.side (G.settingWithFamily γ₁).fine x)⁻¹ * _ *
        blockGauge R.params.side (G.settingWithFamily γ₁).fine (x + TorusFields.unitStep (n * R.params.side) i)
    rw [t1, t2]
    rfl
  · rw [dif_neg hm, dif_neg fun c => hm (hiff.mpr c)]
    exact settingWithFamily_fine_congr x i hst
theorem frameField_eq_of_agreeNear (hL : Odd R.params.side) (hn : 2 ≤ n) {x : TorusSite (n * R.params.side)} {d : ℕ}
    (h : AgreeNear γ γ₁ x d) {z : TorusSite (n * R.params.side)} (i : Fin 4) (hz : _root_.YangMills.Construction.TorusFields.supDist x z + 1 ≤ d) :
    G.frameField γ z i = G.frameField γ₁ z i := by
  apply frameField_congr hL hn
  rintro θ (hθ | hθ)
  · exact h θ z (by omega) hθ
  · refine h θ _ ?_ hθ
    have h1 := _root_.YangMills.Construction.TorusFields.supDist_triangle x z (z + TorusFields.unitStep (n * R.params.side) i)
    have h2 := _root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le z i
    omega
theorem curvature_eq_of_agreeNear (hL : Odd R.params.side) (hn : 2 ≤ n) {x : TorusSite (n * R.params.side)}
    {μ ν : Fin 4} (h : AgreeNear γ γ₁ x 2) :
    curvature (G.frameField γ) x μ ν = curvature (G.frameField γ₁) x μ ν := by
  have e1 := _root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le (n := n * R.params.side) x μ
  have e2 := _root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le (n := n * R.params.side) x ν
  have e0 := _root_.YangMills.Construction.TorusFields.supDist_self x
  unfold curvature holonomy
  rw [frameField_eq_of_agreeNear hL hn h (z := x) μ (by omega), frameField_eq_of_agreeNear hL hn h (z := x) ν (by omega),
    frameField_eq_of_agreeNear hL hn h (z := x + TorusFields.unitStep (n * R.params.side) μ) ν (by omega),
    frameField_eq_of_agreeNear hL hn h (z := x + TorusFields.unitStep (n * R.params.side) ν) μ (by omega)]
theorem exists_site_near_of_mem_core {θ : GasSupport R n} {u : TorusSite (n * R.params.side)}
    (h : parentBlock R.params.side u ∈ θ.core) :
    ∃ z ∈ θ.sites, _root_.YangMills.Construction.TorusFields.supDist u z ≤ 4 * R.range + R.params.side := by
  classical
  obtain ⟨x, hx⟩ := (Finset.mem_filter.mp h).2
  obtain ⟨hb, hw⟩ := Finset.mem_inter.mp hx
  obtain ⟨z, hz, hxz⟩ := (mem_thickening _ _ _).mp hw
  have e : parentBlock R.params.side x = parentBlock R.params.side u := Finset.mem_singleton.mp (Finset.mem_filter.mp hb).2
  have h0 := _root_.YangMills.Construction.InBoxTransfer.supDist_le_of_parentBlock_eq e
  have h1 := _root_.YangMills.Construction.TorusFields.supDist_triangle u x z
  rw [_root_.YangMills.Construction.TorusFields.supDist_comm u x] at h1
  exact ⟨z, hz, by omega⟩
theorem parentBlock_mem_core (θ : GasSupport R n) {z x : TorusSite (n * R.params.side)} (hz : z ∈ θ.sites)
    (h : _root_.YangMills.Construction.TorusFields.supDist x z ≤ 4 * R.range) : parentBlock R.params.side x ∈ θ.core := parentBlock_mem_coreBlocks_of_near hz h
theorem mem_anchorSites_of_mem_recorded {z : TorusSite (n * R.params.side)} (h : z ∈ G.recordedSites) :
    z ∈ G.anchorSites := by
  classical
  unfold GasGround.anchorSites
  exact Finset.mem_union_right _ h
theorem mem_sites_of_mem_snd (θ : GasSupport R n) {z : TorusSite (n * R.params.side)} (hz : z ∈ θ.2) : z ∈ θ.sites :=
  Finset.mem_union_right _ hz
end EvaluationMaps
section Bases
variable {G : GasGround R n} {γ : GasFamily R n}
theorem enclosingCell_mem_of_lumpOf_subset {F : BlockFrame} {L : ℕ} (g : LumpGrid L) (hL : Odd L)
    (hodd : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) (X : Finset F.Cell) (x : F.Site F.depth)
    (hsub : lumpOf g x ⊆ cutBelow F.depth X) : enclosingCell x ∈ X := by
  have hxl : x ∈ lumpOf g x := HoleSites.mem_lumpOf hL.pos hL g x
  exact (BlockSites.mem_cutBelow_iff hodd hs).mp (hsub hxl)
theorem exists_hot_plaquette_of_mem_nearbyLumps {F : BlockFrame} {L : ℕ} (g : LumpGrid L) (hL : Odd L)
    (hodd : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) (s : ℝ)
    (X : Finset (F.Site F.depth)) (W : F.GaugeField F.depth) (y : F.Cell) (l : Finset (F.Site F.depth))
    (hl : l ∈ nearbyLumps (hotLumps g s X W) y) :
    ∃ p ∈ cutPlaquettes X, s ≤ plaquetteDefect W p ∧ ∃ x ∈ plaquetteCorners p,
      enclosingCell x ∈ cellBall y 2 ∧ l = lumpOf g x := by
  classical
  unfold nearbyLumps at hl
  obtain ⟨hl, hsub⟩ := Finset.mem_filter.mp hl
  unfold hotLumps at hl
  obtain ⟨p, hp, hlp⟩ := Finset.mem_biUnion.mp hl
  obtain ⟨hpc, hhot⟩ := Finset.mem_filter.mp hp
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hlp
  exact ⟨p, hpc, hhot, x, hx, enclosingCell_mem_of_lumpOf_subset g hL hodd hs _ x hsub, rfl⟩
theorem mem_plaquetteCorners {F : BlockFrame} {j : ℕ} {p : F.Site j × Fin 4 × Fin 4} {x : F.Site j}
    (h : x ∈ plaquetteCorners p) :
    x = p.1 ∨ x = p.1 + BlockAverages.unitStep j p.2.1 ∨ x = p.1 + BlockAverages.unitStep j p.2.2 ∨
      x = p.1 + BlockAverages.unitStep j p.2.1 + BlockAverages.unitStep j p.2.2 := by
  simpa [plaquetteCorners] using h
theorem lt_of_mem_cutPlaquettes {F : BlockFrame} {j : ℕ} {X : Finset (F.Site j)} {p : F.Site j × Fin 4 × Fin 4}
    (hp : p ∈ cutPlaquettes X) : p.2.1 < p.2.2 := by
  simp only [cutPlaquettes, Finset.mem_filter] at hp
  exact hp.2.1
theorem nearbyLumps_subset (hL : Odd R.params.side) (hn : 2 ≤ n) (W W' : TorusField (n * R.params.side))
    (c₀ : TorusSite n)
    (hyp : ∀ (x₁ p₁ : TorusSite (n * R.params.side)) (μ ν : Fin 4), μ < ν → x₁ ∈ plaquetteVertices p₁ μ ν →
      _root_.YangMills.Construction.TorusFields.supDist c₀ (parentBlock R.params.side x₁) ≤ 2 → R.params.threshold ≤ curvature W p₁ μ ν →
        R.params.threshold ≤ curvature W' p₁ μ ν) :
    nearbyLumps (stepHotLumps R.params W) (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c₀) ⊆
      nearbyLumps (stepHotLumps R.params W') (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c₀) := by
  classical
  intro l hlm
  have hs : ∀ i, 0 < (stepBlockFrame R.params.side n).extent i := fun _ => by
    show 0 < n
    omega
  have hodd' : Odd (stepBlockFrame R.params.side n).blockSide := hL
  obtain ⟨p, hpc, hhot, x, hx, hu, hlx⟩ := exists_hot_plaquette_of_mem_nearbyLumps (F := stepBlockFrame R.params.side n)
    R.params.grid hL hodd' hs R.params.threshold _ _ _ l hlm
  have hsub := (Finset.mem_filter.mp hlm).2
  refine Finset.mem_filter.mpr ⟨?_, hsub⟩
  refine Finset.mem_biUnion.mpr ⟨p, Finset.mem_filter.mpr ⟨hpc, ?_⟩, Finset.mem_image.mpr ⟨x, hx, hlx.symm⟩⟩
  obtain ⟨h, hh, hcell⟩ := Finset.mem_image.mp hu
  obtain ⟨x₁, rfl⟩ := torusSiteInFrame_surjective (stepBlockFrame R.params.side n) 0 stepBlockFrame_period_zero x
  obtain ⟨p₀, μ, ν⟩ := p
  obtain ⟨p₁, rfl⟩ := torusSiteInFrame_surjective (stepBlockFrame R.params.side n) 0 stepBlockFrame_period_zero p₀
  have hμν : μ < ν := lt_of_mem_cutPlaquettes hpc
  have hhot' : R.params.threshold ≤ curvature W p₁ μ ν := le_of_le_of_eq hhot (plaquetteDefect_readAtLevel _ p₁ μ ν)
  have hcorner : x₁ ∈ plaquetteVertices p₁ μ ν := by
    have e1 : torusSiteInFrame (stepBlockFrame R.params.side n) 0 p₁ + BlockAverages.unitStep 0 μ =
        torusSiteInFrame (stepBlockFrame R.params.side n) 0 (p₁ + TorusFields.unitStep (n * R.params.side) μ) := by
      rw [torusSiteInFrame_add, torusSiteInFrame_unitStep]
    have e2 : torusSiteInFrame (stepBlockFrame R.params.side n) 0 p₁ + BlockAverages.unitStep 0 ν =
        torusSiteInFrame (stepBlockFrame R.params.side n) 0 (p₁ + TorusFields.unitStep (n * R.params.side) ν) := by
      rw [torusSiteInFrame_add, torusSiteInFrame_unitStep]
    have e3 : torusSiteInFrame (stepBlockFrame R.params.side n) 0 p₁ + BlockAverages.unitStep 0 μ +
        BlockAverages.unitStep 0 ν = torusSiteInFrame (stepBlockFrame R.params.side n) 0
          (p₁ + TorusFields.unitStep (n * R.params.side) μ + TorusFields.unitStep (n * R.params.side) ν) := by
      rw [torusSiteInFrame_add, torusSiteInFrame_add, torusSiteInFrame_unitStep, torusSiteInFrame_unitStep]
    have hi := torusSiteInFrame_injective (m := n * R.params.side) (stepBlockFrame R.params.side n) 0
      stepBlockFrame_period_zero
    simp only [plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false]
    rcases mem_plaquetteCorners hx with h1 | h1 | h1 | h1
    · exact Or.inl (hi h1)
    · exact Or.inr (Or.inl (hi (h1.trans e1)))
    · exact Or.inr (Or.inr (Or.inl (hi (h1.trans e2))))
    · exact Or.inr (Or.inr (Or.inr (hi (h1.trans e3))))
  have hblock : parentBlock R.params.side x₁ = c₀ + siteOfInt h := by
    have h1 := hcell.trans (enclosingCell_torusSiteInFrame x₁)
    apply torusSiteInFrame_injective (stepBlockFrame R.params.side n) 1 stepBlockFrame_period_one
    rw [← torusSiteInFrame_one_add_siteOfInt]
    exact h1.symm
  have hdist : _root_.YangMills.Construction.TorusFields.supDist c₀ (parentBlock R.params.side x₁) ≤ 2 := by
    rw [hblock]
    refine _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le _ _ _ fun i => ?_
    have := Fintype.mem_piFinset.1 hh i
    rw [Finset.mem_Icc] at this
    norm_num at this
    omega
  exact le_of_le_of_eq (hyp x₁ p₁ μ ν hμν hcorner hdist hhot') (plaquetteDefect_readAtLevel _ p₁ μ ν).symm
theorem supDist_le_of_parentBlock_near {L : ℕ} [NeZero L] {x₁ v : TorusSite (n * L)} {c₀ : TorusSite n}
    (hv : parentBlock L v = c₀) (hd : _root_.YangMills.Construction.TorusFields.supDist c₀ (parentBlock L x₁) ≤ 2) : _root_.YangMills.Construction.TorusFields.supDist x₁ v ≤ 4 * L := by
  have h1 := _root_.YangMills.Construction.InBoxTransfer.supDist_le_parentBlock v x₁
  rw [hv] at h1
  have h2 : L * (_root_.YangMills.Construction.TorusFields.supDist c₀ (parentBlock L x₁) + 2) ≤ L * 4 := Nat.mul_le_mul_left _ (by omega)
  rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
  omega
theorem bases_congr {γ₁ : GasFamily R n} {c₀ : TorusSite n}
    (h : ∀ θ : GasSupport R n, c₀ ∈ θ.core → γ θ = γ₁ θ) :
    (G.settingOf γ).bases (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c₀) =
      (G.settingOf γ₁).bases (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c₀) := by
  have e : γ.baseAt (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n
        (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c₀)) =
      γ₁.baseAt (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n
        (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c₀)) := by
    rw [TopLevelSites.toTorusSite_torusSiteInFrame (fun i => stepBlockFrame_period_one i) c₀]
    exact baseAt_congr h
  change (G.settingWithFamily γ).bases _ = (G.settingWithFamily γ₁).bases _
  simp only [GasGround.settingWithFamily]
  rw [e]
theorem isBaseChoice_of_baseUniformWeight_ne_zero {W : TorusField (n * R.params.side)}
    {b : BaseChoice R.params.side n} {y : TorusSite n} (h : baseUniformWeight W b y ≠ 0) :
    IsBaseChoice R.params.baseDepth (stepHotLumps R.params W) b := by
  classical
  have h1 : b ∈ baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W) := by
    by_contra hn
    apply h
    unfold baseUniformWeight
    rw [if_neg hn]
  exact (Finset.mem_filter.mp h1).2
theorem isBaseChoice_of_baseLaw_ne_zero {W : TorusField (n * R.params.side)} {b : BaseChoice R.params.side n}
    (h : baseLaw (R := R) W b ≠ 0) : IsBaseChoice R.params.baseDepth (stepHotLumps R.params W) b := by
  classical
  have h1 : b ∈ baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W) := by
    by_contra hn
    apply h
    unfold baseLaw
    rw [if_neg hn]
  exact (Finset.mem_filter.mp h1).2
end Bases
section Sites
variable {L n : ℕ} [NeZero L] [NeZero n]
theorem toTorusSite_injective {x x' : (stepBlockFrame L n).Site 0}
    (e : (toTorusSite (n * L) x : TorusSite (n * L)) = toTorusSite (n * L) x') : x = x' := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockCosts.eq_of_toTorusSite_eq <;> assumption
theorem toTorusSite_siteAtOffset (Y : TorusSite n) (h o : Fin 4 → ℤ) :
    (toTorusSite (n * L) (siteAtOffset (F := stepBlockFrame L n)
      (torusSiteInFrame (stepBlockFrame L n) 1 (Y + siteOfInt h)) o) : TorusSite (n * L)) = fineSite L Y h o := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockCosts.toTorusSite_siteAtOffset <;> assumption
theorem cellCentreOnTorus_eq (Y : TorusSite n) (h : Fin 4 → ℤ) :
    cellCentreOnTorus L (torusSiteInFrame (stepBlockFrame L n) 1 (Y + siteOfInt h)) = fineSite L Y h 0 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockCosts.cellCentreOnTorus_eq_fineSite <;> assumption
end Sites
section EvaluationInBox
variable {n' : ℕ} [NeZero n']
theorem cellOffset_torusFrame {L n : ℕ} [NeZero L] [NeZero n] (t : ℕ) (hodd : Odd L) (A o : Fin 4 → ℤ)
    (ho : o ∈ centredCube L) :
    cellOffset (F := torusFrame L t n)
      (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).depth
        (siteOfInt (blockPoint L A o) : TorusSite (n * L))) = o := by
  have hper : ∀ i, (torusFrame L t n).period t i = n * L := fun i => by
    simp [BlockFrame.period, torusFrame, BlockFrame.top]
  have hper1 : ∀ i, (torusFrame L t n).period (t + 1) i = n := fun i => by
    simp [BlockFrame.period, torusFrame, BlockFrame.top]
  have hne : NeZero (n * L) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
  have hsite : torusSiteInFrame (torusFrame L t n) t (siteOfInt (blockPoint L A o) : TorusSite (n * L)) =
      siteOfCoords (F := torusFrame L t n) t (blockPoint L A o) := by
    funext i
    simp only [torusSiteInFrame, siteOfCoords, siteOfInt]
    exact intCast_cast_of_eq (n * L) _ (hper i).symm _
  obtain ⟨H, hH⟩ := id hodd
  have hL : ((L : ℤ) - 1) / 2 = (H : ℤ) := by subst hH; push_cast; omega
  have hLH : (L : ℤ) = 2 * H + 1 := by subst hH; push_cast; ring
  have hLpos : (0 : ℤ) < L := by omega
  have hcoord : ∀ (z : Fin 4 → ℤ) i, siteCoords (siteOfCoords (F := torusFrame L t n) t z) i =
      z i % ((n * L : ℕ) : ℤ) := by
    intro z i
    have h := ZMod.coe_intCast (n := (torusFrame L t n).period t i) (z i)
    simp only [siteCoords, siteOfCoords]
    rw [h, hper]
  have hcoord1 : ∀ (z : Fin 4 → ℤ) i, siteCoords (siteOfCoords (F := torusFrame L t n) (t + 1) z) i =
      z i % (n : ℤ) := by
    intro z i
    have h := ZMod.coe_intCast (n := (torusFrame L t n).period (t + 1) i) (z i)
    simp only [siteCoords, siteOfCoords]
    rw [h, hper1]
  have hpow : ((torusFrame L t n).blockSide : ℤ) ^ ((torusFrame L t n).top - t) = (L : ℤ) := by
    simp [torusFrame, BlockFrame.top]
  have hcell : @enclosingCell (torusFrame L t n) t (siteOfCoords t (blockPoint L A o)) = siteOfCoords (t + 1) A := by
    funext i
    have hb := (BlockOffsets.mem_centredCube_iff o).mp ho i
    rw [hL] at hb
    simp only [enclosingCell, siteOfCoords]
    rw [hpow]
    have h1 := hcoord (blockPoint L A o) i
    have h2 : siteCoords (j := t) (siteOfCoords (F := torusFrame L t n) t (blockPoint L A o)) i =
        blockPoint L A o i % ((n * L : ℕ) : ℤ) := h1
    rw [h2]
    set Z := blockPoint L A o i with hZ
    set k := Z / ((n * L : ℕ) : ℤ) with hk
    have hmod : Z % ((n * L : ℕ) : ℤ) = Z - ((n * L : ℕ) : ℤ) * k := by
      rw [Int.emod_def]
    have hq : (Z % ((n * L : ℕ) : ℤ) + ((L : ℤ) - 1) / 2) / (L : ℤ) = A i - (n : ℤ) * k := by
      have := (Int.ediv_emod_unique (a := Z % ((n * L : ℕ) : ℤ) + ((L : ℤ) - 1) / 2) (b := (L : ℤ))
        (r := o i + H) (q := A i - (n : ℤ) * k) hLpos).mpr ⟨?_, by omega, by omega⟩
      · exact this.1
      · rw [hmod, hL, hZ]
        simp only [blockPoint]
        push_cast
        ring
    rw [hq]
    exact intCast_sub_mul_of_eq _ n (hper1 i) (A i) k
  have hcentre : cellCentre (F := torusFrame L t n) t (siteOfCoords (t + 1) A) =
      siteOfCoords t fun i => (L : ℤ) * A i := by
    funext i
    simp only [cellCentre, siteOfCoords]
    rw [hpow]
    have hc : siteCoords (j := t + 1) (siteOfCoords (F := torusFrame L t n) (t + 1) A) i = A i % (n : ℤ) :=
      hcoord1 A i
    show (Int.cast ((L : ℤ) * siteCoords (j := t + 1) (siteOfCoords (F := torusFrame L t n) (t + 1) A) i) :
      ZMod ((torusFrame L t n).period t i)) = Int.cast ((L : ℤ) * A i)
    rw [hc]
    have h1 : (L : ℤ) * (A i % (n : ℤ)) = (L : ℤ) * A i - ((n * L : ℕ) : ℤ) * (A i / (n : ℤ)) := by
      rw [Int.emod_def]
      push_cast
      ring
    rw [h1]
    exact intCast_sub_mul_of_eq _ (n * L) (hper i) _ _
  funext i
  have hb := (BlockOffsets.mem_centredCube_iff o).mp ho i
  rw [hL] at hb
  show (((torusSiteInFrame (torusFrame L t n) t (siteOfInt (blockPoint L A o) : TorusSite (n * L))) -
    cellCentre (F := torusFrame L t n) t (@enclosingCell (torusFrame L t n) t
      (torusSiteInFrame (torusFrame L t n) t (siteOfInt (blockPoint L A o) : TorusSite (n * L))))) i).valMinAbs = o i
  rw [hsite, hcell, hcentre]
  have hne2 : NeZero ((torusFrame L t n).period t i) := by
    rw [hper]
    exact hne
  rw [ZMod.valMinAbs_spec]
  constructor
  · simp [siteOfCoords, blockPoint]
  · rw [hper]
    have hn : (1 : ℤ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
    have hLn : (L : ℤ) ≤ (n : ℤ) * L := by nlinarith [(show (0 : ℤ) ≤ L by positivity)]
    constructor
    · push_cast; omega
    · push_cast; omega
theorem gaugeAt_eq_of_settingsAgree {s : ChartSetting R n} {s' : ChartSetting R n'} {Y : TorusSite n}
    {Y' : TorusSite n'} {m : ℕ} (hodd : Odd R.params.side) (hn : 2 ≤ n) (hf : s.free ⊆ chartBonds R.params.side n)
    (hag : SettingsAgreeAwayFromFrames s s' Y Y' m) (kk o : Fin 4 → ℤ) (hkk : OffsetInBox m kk)
    (ho : o ∈ centredCube R.params.side) :
    gaugeAt (R := R) s.fine (fineSite R.params.side Y kk o) = gaugeAt (R := R) s'.fine (fineSite R.params.side Y' kk o) := by
  set A : Fin 4 → ℤ := fun i => ((Y i).cast : ℤ) + kk i with hA
  set A' : Fin 4 → ℤ := fun i => ((Y' i).cast : ℤ) + kk i with hA'
  show gaugeAt (R := R) s.fine (siteOfInt (blockPoint R.params.side A o)) =
    gaugeAt (R := R) s'.fine (siteOfInt (blockPoint R.params.side A' o))
  rw [gaugeAt_blockPoint hodd _ A o ho, gaugeAt_blockPoint hodd _ A' o ho]
  have hc := (BlockOffsets.mem_centredCube_iff o).mp ho
  have key := pathHolonomy_congr (L := R.params.side) s.fine s'.fine (fun i => (R.params.side : ℤ) * A i)
    (fun i => (R.params.side : ℤ) * A' i) (axisPath o 1) 0 ?_
  · simpa only [add_zero] using key
  · intro b hb
    obtain ⟨g1, g2, g3⟩ := isAxialBond_of_mem_axisPath hc b hb
    have hb1 : b.1 ∈ centredCube R.params.side := (BlockOffsets.mem_centredCube_iff _).mpr g1
    have hb2 : b.1 + Pi.single b.2 1 ∈ centredCube R.params.side := (BlockOffsets.mem_centredCube_iff _).mpr g2
    have nf := blockPoint_not_mem_free s hodd hn hf A b.1 b.2 hb1 hb2 g3
    exact hag.fine_eq (kk, b.1, b.2) ⟨hkk, hb1⟩ nf
theorem field_eq_of_settingsAgree {s : ChartSetting R n} {s' : ChartSetting R n'} {Y : TorusSite n}
    {Y' : TorusSite n'} {m k : ℕ} {η : FreeCoords s.free} {η' : FreeCoords s'.free} (hodd : Odd R.params.side)
    (hn : 2 ≤ n) (hn' : 2 ≤ n') (hf : s.free ⊆ chartBonds R.params.side n)
    (hag : SettingsAgreeAwayFromFrames s s' Y Y' m) (hk : k ≤ m)
    (hnear : CoordsAgreeNear s s' Y Y' k η η') (kk o : Fin 4 → ℤ) (i : Fin 4) (ho : o ∈ centredCube R.params.side)
    (hframe : nearBond R.params.side Y (kk, o, i) ∈ s.free →
      s.frame (nearBond R.params.side Y (kk, o, i)) = s'.frame (nearBond R.params.side Y' (kk, o, i)))
    (hkk : ∀ l, |kk l| + 1 ≤ (k : ℤ)) :
    s.field η (fineSite R.params.side Y kk o) i = s'.field η' (fineSite R.params.side Y' kk o) i := by
  have hin : OffsetInBox k kk := fun l => by have := hkk l; omega
  have hinm : OffsetInBox m kk := fun l => by have := hkk l; omega
  have hin1 : OffsetInBox m (kk + Pi.single i 1) := fun l => by
    have h1 := hkk l
    have h2 : |(kk + Pi.single i (1 : ℤ) : Fin 4 → ℤ) l| ≤ |kk l| + 1 := by
      simp only [Pi.add_apply, Pi.single_apply]
      split_ifs
      · exact (abs_add_le _ _).trans (by simp)
      · simp
    omega
  have hnr : IsNearIndex R.params.side k (kk, o, i) := ⟨hin, ho⟩
  have hnm : IsNearIndex R.params.side m (kk, o, i) := ⟨hinm, ho⟩
  by_cases hfr : nearBond R.params.side Y (kk, o, i) ∈ s.free
  · have hfr' := (hag.free_iff _ hnm).mp hfr
    have h1 := hnear _ hnr
    simp only [ChartSetting.coordsByIndex] at h1
    rw [dif_pos hfr, dif_pos hfr'] at h1
    have hfm := hframe hfr
    have e1 : s.field η (fineSite R.params.side Y kk o) i = chartLink s (fineSite R.params.side Y kk o) i
        (s.frame (nearBond R.params.side Y (kk, o, i)) + ColdStepAtMirrorFrames.toImaginary (η ⟨_, hfr⟩)) :=
      dif_pos hfr
    have e2 : s'.field η' (fineSite R.params.side Y' kk o) i = chartLink s' (fineSite R.params.side Y' kk o) i
        (s'.frame (nearBond R.params.side Y' (kk, o, i)) + ColdStepAtMirrorFrames.toImaginary (η' ⟨_, hfr'⟩)) :=
      dif_pos hfr'
    rw [e1, e2, h1, hfm]
    unfold chartLink
    rw [gaugeAt_eq_of_settingsAgree hodd hn hf hag kk o hinm ho, fineSite_add_unitStep, fineSite_add_unitStep]
    have hcr : ∀ (N : ℕ) [NeZero N], 2 ≤ N → ∀ (Z : TorusSite N),
        IsCrossingBond (F := stepBlockFrame R.params.side N)
          (torusSiteInFrame (stepBlockFrame R.params.side N) 0 (fineSite R.params.side Z kk o), i) ↔
          o + Pi.single i 1 ∉ centredCube R.params.side := by
      intro N _ hN Z
      show IsCrossingBond (F := stepBlockFrame R.params.side N) (torusSiteInFrame (stepBlockFrame R.params.side N) 0
        (siteOfInt (blockPoint R.params.side (fun i => ((Z i).cast : ℤ) + kk i) o)), i) ↔ _
      rw [torusSiteInFrame_siteOfInt]
      exact isCrossingBond_blockPoint_iff hodd hN _ o ho i
    have hblock : ∀ (N : ℕ) [NeZero N] (Z : TorusSite N),
        parentBlock R.params.side (fineSite R.params.side Z kk o) = Z + siteOfInt kk := by
      intro N _ Z
      show parentBlock R.params.side (siteOfInt (blockPoint R.params.side (fun i => ((Z i).cast : ℤ) + kk i) o) :
        TorusSite (N * R.params.side)) = _
      rw [parentBlock_blockPoint hodd _ o ho, siteOfInt_cast_add]
    by_cases hcube : o + Pi.single i 1 ∈ centredCube R.params.side
    · rw [if_neg (fun h => ((hcr n hn Y).mp h) hcube), if_neg (fun h => ((hcr n' hn' Y').mp h) hcube),
        gaugeAt_eq_of_settingsAgree hodd hn hf hag kk _ hinm hcube]
    · have hV : s.coarse (parentBlock R.params.side (fineSite R.params.side Y kk o)) i =
          s'.coarse (parentBlock R.params.side (fineSite R.params.side Y' kk o)) i := by
        rw [hblock, hblock]
        exact hag.coarse_agree (kk, i) ⟨hinm, hin1⟩
      rw [if_pos ((hcr n hn Y).mpr hcube), if_pos ((hcr n' hn' Y').mpr hcube), hV, fineSite_wrap, fineSite_wrap]
      have hwrap : o + Pi.single i 1 - (R.params.side : ℤ) • Pi.single i 1 ∈ centredCube R.params.side := by
        obtain ⟨H, hH⟩ := hodd
        have hL : ((R.params.side : ℤ) - 1) / 2 = (H : ℤ) := by rw [hH]; push_cast; omega
        have hLH : (R.params.side : ℤ) = 2 * H + 1 := by rw [hH]; push_cast; ring
        have hb := (BlockOffsets.mem_centredCube_iff o).mp ho
        rw [hL] at hb
        have hoi : o i = H := by
          by_contra hne
          apply hcube
          rw [BlockOffsets.mem_centredCube_iff, hL]
          intro l
          by_cases hl : l = i
          · subst hl
            have := hb l
            simp only [Pi.add_apply, Pi.single_eq_same]
            omega
          · have := hb l
            simpa [Pi.single_apply, hl] using this
        rw [BlockOffsets.mem_centredCube_iff, hL]
        intro l
        by_cases hl : l = i
        · subst hl
          simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
          omega
        · have := hb l
          simpa [Pi.single_apply, hl] using this
      rw [gaugeAt_eq_of_settingsAgree hodd hn hf hag _ _ hin1 hwrap]
  · have hfr' : nearBond R.params.side Y' (kk, o, i) ∉ s'.free := fun h => hfr ((hag.free_iff _ hnm).mpr h)
    have e1 : s.field η (fineSite R.params.side Y kk o) i = s.fine (fineSite R.params.side Y kk o) i := dif_neg hfr
    have e2 : s'.field η' (fineSite R.params.side Y' kk o) i = s'.fine (fineSite R.params.side Y' kk o) i :=
      dif_neg hfr'
    rw [e1, e2]
    exact hag.fine_eq _ hnm hfr
end EvaluationInBox
section Box
variable {n' : ℕ} [NeZero n'] {G : GasGround R n} {G' : GasGround R n'} {Y : TorusSite n} {Y' : TorusSite n'}
  {N m : ℕ} {θ : GasSupport R n} {θ' : GasSupport R n'} {s : SupportState θ} {s' : SupportState θ'}
theorem mem_centredCube_iff' (L : ℕ) (h : Fin 4 → ℤ) :
    h ∈ centredCube L ↔ ∀ i, -(((L : ℤ) - 1) / 2) ≤ h i ∧ h i ≤ ((L : ℤ) - 1) / 2 := by apply _root_.YangMills.Construction.LumpContours.CutAction.mem_centredCube <;> assumption
theorem fineSite_eq_blockCentre_add {L : ℕ} [NeZero L] (Z : TorusSite n) (h o : Fin 4 → ℤ) :
    (fineSite L Z h o : TorusSite (n * L)) = blockCentre L Z + siteOfInt (fun i => (L : ℤ) * h i + o i) := by
  rw [blockCentre_add_siteOfInt]
  funext i
  simp only [fineSite, siteOfInt]
  push_cast
  ring_nf
theorem exists_split_of_offsetInBox {L : ℕ} [NeZero L] (hodd : Odd L) {M : ℕ} {a : Fin 4 → ℤ}
    (ha : OffsetInBox (refinedRadius L M) a) :
    ∃ h o, OffsetInBox M h ∧ o ∈ centredCube L ∧ a = (fun i => (L : ℤ) * h i + o i) ∧ coarseOffset L a = h := by
  have hL := side_pos_int (L := L)
  have hbox := (offsetInBox_refinedRadius_iff hodd).mp ha
  obtain ⟨l, hl⟩ := hodd
  have hl2 : ((L : ℤ) - 1) / 2 = (l : ℤ) := by omega
  refine ⟨coarseOffset L a, fun i => a i - (L : ℤ) * coarseOffset L a i, hbox, ?_, ?_, rfl⟩
  · refine (mem_centredCube_iff' L _).2 fun i => ?_
    have h1 := Int.mul_ediv_add_emod (a i + ((L : ℤ) - 1) / 2) (L : ℤ)
    have h2 := Int.emod_nonneg (a i + ((L : ℤ) - 1) / 2) hL.ne'
    have h3 := Int.emod_lt_of_pos (a i + ((L : ℤ) - 1) / 2) hL
    simp only [coarseOffset]
    rw [hl2] at h1 h2 h3 ⊢
    constructor <;> omega
  · funext i
    ring
theorem offsetInBox_mono {a b : ℕ} {h : Fin 4 → ℤ} (hab : a ≤ b) (hh : OffsetInBox a h) : OffsetInBox b h :=
  fun i => (hh i).trans (by exact_mod_cast hab)
theorem state_single (s : SupportState θ) (h : (GasFamily.single θ s).Occupies θ) :
    (GasFamily.single θ s).state h = s := by
  have e := eq_inr_state h
  rw [single_apply_self] at e
  exact (Sum.inr.inj e).symm
theorem coresDisjoint_single (s : SupportState θ) : (GasFamily.single θ s).CoresDisjoint := by
  intro a b ha hb _ _ _
  rw [(occupies_single_iff s).1 ha, (occupies_single_iff s).1 hb]
theorem exists_parentBlock_add_unitStep {L : ℕ} [NeZero L] (hodd : Odd L) (h o : Fin 4 → ℤ)
    (ho : o ∈ centredCube L) (i : Fin 4) :
    ∃ h₂ : Fin 4 → ℤ, (∀ l, |h₂ l - h l| ≤ 1) ∧ ∀ (k : ℕ) [NeZero k] (Z : TorusSite k),
      parentBlock L (fineSite L Z h o + TorusFields.unitStep (k * L) i) = Z + siteOfInt h₂ := by
  have hadd : ∀ (k : ℕ) [NeZero k] (Z : TorusSite k),
      (fineSite L Z h o + TorusFields.unitStep (k * L) i : TorusSite (k * L)) = fineSite L Z h (o + Pi.single i 1) := by
    intro k _ Z
    rw [BlockOffsets.unitStep_eq_siteOfInt]
    funext l
    simp only [fineSite, siteOfInt, Pi.add_apply]
    push_cast
    ring
  by_cases hc : o + Pi.single i 1 ∈ centredCube L
  · refine ⟨h, fun l => by simp, fun k _ Z => ?_⟩
    rw [hadd, parentBlock_fineSite hodd Z h _ hc]
  · refine ⟨h + Pi.single i 1, fun l => ?_, fun k _ Z => ?_⟩
    · by_cases e : l = i
      · subst e
        simp
      · simp [e]
    · have hL : ((L : ℤ) - 1) / 2 + ((L : ℤ) - 1) / 2 + 1 = (L : ℤ) := by
        obtain ⟨m, rfl⟩ := hodd
        push_cast
        omega
      have hcm := (mem_centredCube_iff' _ _).1 ho
      have hi : o i = ((L : ℤ) - 1) / 2 := by
        by_contra hne
        refine hc ((mem_centredCube_iff' _ _).2 fun l => ?_)
        have := hcm l
        by_cases e : l = i
        · subst e
          simp only [Pi.add_apply, Pi.single_eq_same]
          omega
        · simpa [Pi.single_apply, e] using this
      have e2 : (fineSite L Z h (o + Pi.single i 1) : TorusSite (k * L)) =
          fineSite L Z (h + Pi.single i 1) (o + Pi.single i 1 - (L : ℤ) • Pi.single i 1) := by
        funext l
        simp only [fineSite, siteOfInt, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        push_cast
        ring
      have hm : o + Pi.single i 1 - (L : ℤ) • Pi.single i 1 ∈ centredCube L := by
        refine (mem_centredCube_iff' _ _).2 fun l => ?_
        have := hcm l
        by_cases e : l = i
        · subst e
          simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
          omega
        · simpa [Pi.single_apply, e] using this
      rw [hadd, e2, parentBlock_fineSite hodd Z _ _ hm]
structure TransferData (G : GasGround R n) (G' : GasGround R n') (Y : TorusSite n) (Y' : TorusSite n') (N m : ℕ)
    (θ : GasSupport R n) (θ' : GasSupport R n') (s : SupportState θ) (s' : SupportState θ') : Prop where
  admissible : R.params.Admissible
  hasExpansions : R.HasExpansions
  groundsAgree : GroundsAgreeNear G G' Y Y' N
  gap_eq : m + R.frameReach + 1 = N
  deep : 16 * R.frameReach ≤ N
  frameReach_pos : 1 ≤ R.frameReach
  range_le : 16 * R.range ≤ R.params.side * R.frameReach
  side_le_range : 64 * R.params.side ≤ R.range
  range_ge : 2 ^ 16 ≤ R.range
  isBlockSide : IsBlockTorusSide R.params (n * R.params.side)
  isBlockSide' : IsBlockTorusSide R.params (n' * R.params.side)
  isSupport : G.IsGasSupport θ
  isSupport' : G'.IsGasSupport θ'
  core_mem_box : ∀ y ∈ θ.core, ∃ h, OffsetInBox m h ∧ y = Y + siteOfInt h
  core_mem_box' : ∀ y ∈ θ'.core, ∃ h, OffsetInBox m h ∧ y = Y' + siteOfInt h
  sameSupport : SameSupportNear θ θ' Y Y' N
  core_iff : ∀ h, OffsetInBox N h → (Y + siteOfInt h ∈ θ.core ↔ Y' + siteOfInt h ∈ θ'.core)
  sameState : SameStateNear θ θ' s s' Y Y' N
  ground_weight : G.HasWeightAt GasFamily.empty 0
  ground_weight' : G'.HasWeightAt GasFamily.empty 0
  frameLocal : FrameLocality.FrameCoordLocal
  kernelLocal : BondKernelLocality
namespace TransferData
variable (P : TransferData G G' Y Y' N m θ θ' s s')
include P
theorem side_odd : Odd R.params.side := P.admissible.L_odd
theorem two_le : 2 ≤ n := by
  have := P.groundsAgree.lt_extent
  omega
theorem two_le' : 2 ≤ n' := by
  have := P.groundsAgree.lt_extent'
  omega
theorem coreBonds_iff : ∀ q, IsNearIndex R.params.side N q →
    (nearBond R.params.side Y q ∈ θ.coreBonds ↔ nearBond R.params.side Y' q ∈ θ'.coreBonds) := by
  classical
  rintro ⟨h, o, i⟩ ⟨hh, ho⟩
  have hh' : OffsetInBox N h := hh
  have hodd := P.side_odd
  have hn := P.groundsAgree.lt_extent
  have hn' := P.groundsAgree.lt_extent'
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
        parentBlock R.params.side (b.1 + TorusFields.unitStep (k * R.params.side) b.2) ∈ ϑ.core := by
    intro k _ ϑ b
    unfold GasSupport.coreBonds
    simp
  rw [hmem θ, hmem θ']
  simp only [nearBond]
  rw [parentBlock_fineSite hodd Y h o ho, parentBlock_fineSite hodd Y' h o ho, hb n Y, hb n' Y', P.core_iff h hh]
  refine and_congr_right fun _ => ⟨fun hy => ?_, fun hy => ?_⟩
  · obtain ⟨a, ha, e⟩ := P.sameSupport.core_mem _ hy
    have := hh₂ Y hn ha e
    subst this
    exact (P.core_iff _ ha).1 hy
  · obtain ⟨a, ha, e⟩ := P.sameSupport.core_mem' _ hy
    have := hh₂ Y' hn' ha e
    subst this
    exact (P.core_iff _ ha).2 hy
theorem familiesMatch : FamiliesMatchNear (GasFamily.single θ s) (GasFamily.single θ' s') Y Y' N := by
  classical
  have hθ : (GasFamily.single θ s).Occupies θ := (occupies_single_iff s).2 rfl
  have hθ' : (GasFamily.single θ' s').Occupies θ' := (occupies_single_iff s').2 rfl
  refine ⟨fun q hq => ?_, fun h o hh ho => ?_, fun h o hz hz' hh ho => ?_, fun h hh => ?_⟩
  · by_cases hb : nearBond R.params.side Y q ∈ θ.coreBonds
    · have hb' := (P.coreBonds_iff q hq).1 hb
      rw [fieldAt_eq_of_mem_coreBonds (coresDisjoint_single s) hθ hb,
        fieldAt_eq_of_mem_coreBonds (coresDisjoint_single s') hθ' hb', state_single, state_single]
      exact congrArg Sum.inr (P.sameState.field_eq q hb hb' hq)
    · have hb' : nearBond R.params.side Y' q ∉ θ'.coreBonds := fun c => hb ((P.coreBonds_iff q hq).2 c)
      rw [fieldAt_eq_inl_of_forall_not_mem fun a ha => by rwa [(occupies_single_iff s).1 ha],
        fieldAt_eq_inl_of_forall_not_mem fun a ha => by rwa [(occupies_single_iff s').1 ha]]
  · rw [mem_sites_single, mem_sites_single]
    exact P.sameSupport.sites_iff h o hh ho
  · have h1 := (mem_sites_single s).1 hz
    have h2 := (mem_sites_single s').1 hz'
    rw [GasFamily.labelAt_eq_of_mem _ (coresDisjoint_single s) hz hθ h1,
      GasFamily.labelAt_eq_of_mem _ (coresDisjoint_single s') hz' hθ' h2, state_single, state_single]
    exact P.sameState.label_eq h o h1 h2 hh ho
  · by_cases hy : Y + siteOfInt h ∈ θ.core
    · have hy' := (P.core_iff h hh).1 hy
      rw [baseAt_eq_of_mem_core (coresDisjoint_single s) hθ hy, baseAt_eq_of_mem_core (coresDisjoint_single s') hθ' hy',
        state_single, state_single]
      exact congrArg Sum.inr (P.sameState.base_eq h hy hy' hh)
    · have hy' : Y' + siteOfInt h ∉ θ'.core := fun c => hy ((P.core_iff h hh).2 c)
      rw [baseAt_eq_inl_of_forall_not_mem fun a ha => by rwa [(occupies_single_iff s).1 ha],
        baseAt_eq_inl_of_forall_not_mem fun a ha => by rwa [(occupies_single_iff s').1 ha]]
theorem settingsAgree : SettingsAgreeAwayFromFrames (G.settingOf (GasFamily.single θ s))
    (G'.settingOf (GasFamily.single θ' s')) Y Y' N :=
  settingsAgreeAwayFromFrames_of_match P.side_odd P.two_le P.two_le' P.groundsAgree P.familiesMatch
end TransferData
end Box
section Hot
variable {n' : ℕ} [NeZero n'] {G : GasGround R n} {G' : GasGround R n'} {Y : TorusSite n} {Y' : TorusSite n'}
  {N m : ℕ} {θ : GasSupport R n} {θ' : GasSupport R n'} {s : SupportState θ} {s' : SupportState θ'}
theorem abs_add_le_of_box {A B : ℤ} {a e : Fin 4 → ℤ} (ha : ∀ l, |a l| ≤ A) (he : ∀ l, |e l| ≤ B) (l : Fin 4) :
    |(a + e) l| ≤ A + B := (abs_add_le _ _).trans (add_le_add (ha l) (he l))
theorem refinedRadius_succ (L m : ℕ) : refinedRadius L (m + 1) = refinedRadius L m + L := by
  unfold refinedRadius
  ring
theorem agreeNear_single_empty_of_far (hsup : G.IsGasSupport θ) (s : SupportState θ)
    {v x : TorusSite (n * R.params.side)} {d : ℕ} (hv : v ∈ G.anchorSites)
    (hd : _root_.YangMills.Construction.TorusFields.supDist x v + d + R.params.side ≤ 6 * R.range) : AgreeNear (GasFamily.single θ s) GasFamily.empty x d := by
  intro θ₁ u hu hc
  show GasFamily.single θ s θ₁ = Sum.inl ()
  by_cases e : θ₁ = θ
  · exfalso
    subst e
    obtain ⟨z', hz', hd'⟩ := exists_site_near_of_mem_core hc
    have ap := hsup.far_from_anchor z' hz' v hv
    have t1 := _root_.YangMills.Construction.TorusFields.supDist_triangle z' u v
    have t2 := _root_.YangMills.Construction.TorusFields.supDist_triangle u x v
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm z' u] at t1
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm u x] at t2
    omega
  · exact single_apply_of_ne s e
theorem agreeNear_single_empty_of_clear (s : SupportState θ) {x : TorusSite (n * R.params.side)} {d : ℕ}
    (h : ¬ ∃ u, _root_.YangMills.Construction.TorusFields.supDist x u ≤ d ∧ parentBlock R.params.side u ∈ θ.core) :
    AgreeNear (GasFamily.single θ s) GasFamily.empty x d := by
  intro θ₁ u hu hc
  show GasFamily.single θ s θ₁ = Sum.inl ()
  by_cases e : θ₁ = θ
  · subst e
    exact absurd ⟨u, hu, hc⟩ h
  · exact single_apply_of_ne s e
theorem mem_support_single {z : TorusSite (n * R.params.side)} :
    z ∈ (G.settingOf (GasFamily.single θ s)).support ↔ z ∈ G.recordedSites ∨ z ∈ θ.2 := by
  show z ∈ G.recordedSites ∪ (GasFamily.single θ s).sites ↔ _
  rw [Finset.mem_union, mem_sites_single]
namespace TransferData
variable (P : TransferData G G' Y Y' N m θ θ' s s')
include P
theorem add_two_le : m + 2 ≤ N := by
  have := P.gap_eq
  have := P.frameReach_pos
  omega
theorem refinedRadius_lt : 2 * refinedRadius R.params.side N + 2 < n * R.params.side :=
  refinedRadius_lt_side P.side_odd P.groundsAgree.lt_extent
theorem refinedRadius_lt' : 2 * refinedRadius R.params.side N + 2 < n' * R.params.side :=
  refinedRadius_lt_side P.side_odd P.groundsAgree.lt_extent'
theorem refinedRadius_add_le : refinedRadius R.params.side (m + 1) + 16 * R.range ≤ refinedRadius R.params.side N := by
  have h := P.range_le
  have e : R.params.side * N = R.params.side * (m + 1) + R.params.side * R.frameReach := by
    rw [← P.gap_eq]
    ring
  unfold refinedRadius
  omega
theorem frame_eq {kk o : Fin 4 → ℤ} (hkk : OffsetInBox (m + 1) kk) (ho : o ∈ centredCube R.params.side) (i : Fin 4) :
    (G.settingOf (GasFamily.single θ s)).frame (nearBond R.params.side Y (kk, o, i)) =
      (G'.settingOf (GasFamily.single θ' s')).frame (nearBond R.params.side Y' (kk, o, i)) := by
  have hodd := P.side_odd
  have hgap := P.gap_eq
  have hside : 4 * R.frameReach + 5 < n := by
    have := P.groundsAgree.lt_extent
    have := P.deep
    have := P.frameReach_pos
    omega
  have hside' : 4 * R.frameReach + 5 < n' := by
    have := P.groundsAgree.lt_extent'
    have := P.deep
    have := P.frameReach_pos
    omega
  have hoff₁ := cellOffset_torusFrame (L := R.params.side) (n := n) R.depth hodd (fun i => ((Y i).cast : ℤ) + kk i) o ho
  have hoff₂ := cellOffset_torusFrame (L := R.params.side) (n := n') R.depth hodd (fun i => ((Y' i).cast : ℤ) + kk i) o ho
  refine P.frameLocal R.params R.anchorRadius R.depth R.frameReach n n' G.coarse G'.coarse _ _ P.admissible
    (by have := P.frameReach_pos; omega) hside hside' rfl (hoff₁.trans hoff₂.symm) ?_
  show FieldsAgreeNear G.coarse G'.coarse (parentBlock R.params.side (fineSite R.params.side Y kk o))
    (parentBlock R.params.side (fineSite R.params.side Y' kk o)) R.frameReach
  rw [parentBlock_fineSite hodd Y kk o ho, parentBlock_fineSite hodd Y' kk o ho]
  intro b hb
  have hbox : BondOffsetInBox N (kk + b.1, b.2) := by
    constructor
    · intro l
      have h3 := abs_add_le_of_box (A := ((m + 1 : ℕ) : ℤ)) (B := (R.frameReach : ℤ)) hkk hb.1 l
      have e : (((m + 1 : ℕ) : ℤ) + (R.frameReach : ℤ)) = (N : ℤ) := by
        rw [← hgap]
        push_cast
        ring
      rwa [e] at h3
    · intro l
      have h3 := abs_add_le_of_box (A := ((m + 1 : ℕ) : ℤ)) (B := (R.frameReach : ℤ)) hkk hb.2 l
      have e : (((m + 1 : ℕ) : ℤ) + (R.frameReach : ℤ)) = (N : ℤ) := by
        rw [← hgap]
        push_cast
        ring
      rw [e] at h3
      have e2 : ((kk + b.1) + Pi.single b.2 1 : Fin 4 → ℤ) = kk + (b.1 + Pi.single b.2 1) := by
        rw [add_assoc]
      show |((kk + b.1) + Pi.single b.2 1 : Fin 4 → ℤ) l| ≤ (N : ℤ)
      rw [e2]
      exact h3
  have hh := P.groundsAgree.coarse_agree (kk + b.1, b.2) hbox
  have e1 : ∀ (k : ℕ) [NeZero k] (Z : TorusSite k),
      (bondFrom (Z + siteOfInt kk) b).1 = (bondFrom Z (kk + b.1, b.2)).1 := by
    intro k _ Z
    simp only [bondFrom]
    rw [add_assoc, ← siteOfInt_add]
  show G.coarse (bondFrom (Y + siteOfInt kk) b).1 b.2 = G'.coarse (bondFrom (Y' + siteOfInt kk) b).1 b.2
  rw [e1, e1]
  exact hh
theorem frameField_eq_box {kk o : Fin 4 → ℤ} (hkk : OffsetInBox (m + 1) kk) (ho : o ∈ centredCube R.params.side)
    (i : Fin 4) :
    G.frameField (GasFamily.single θ s) (fineSite R.params.side Y kk o) i =
      G'.frameField (GasFamily.single θ' s') (fineSite R.params.side Y' kk o) i := by
  rw [← field_zero_eq_frameField P.side_odd P.two_le, ← field_zero_eq_frameField P.side_odd P.two_le']
  have hN := P.add_two_le
  refine field_eq_of_settingsAgree (k := N) P.side_odd P.two_le P.two_le' free_subset_chartBonds P.settingsAgree le_rfl ?_
    kk o i ho ?_ ?_
  · intro q _
    simp only [ChartSetting.coordsByIndex]
    split_ifs <;> simp
  · intro _
    exact P.frame_eq hkk ho i
  · intro l
    have h1 := hkk l
    omega
theorem frameField_eq_offset {a : Fin 4 → ℤ} (ha : OffsetInBox (refinedRadius R.params.side (m + 1)) a) (i : Fin 4) :
    G.frameField (GasFamily.single θ s) (blockCentre R.params.side Y + siteOfInt a) i =
      G'.frameField (GasFamily.single θ' s') (blockCentre R.params.side Y' + siteOfInt a) i := by
  obtain ⟨h, o, hh, ho, rfl, -⟩ := exists_split_of_offsetInBox P.side_odd ha
  rw [← fineSite_eq_blockCentre_add, ← fineSite_eq_blockCentre_add]
  exact P.frameField_eq_box hh ho i
theorem curvature_eq_box {a : Fin 4 → ℤ} (hb : ∀ l, |a l| + 1 ≤ ((refinedRadius R.params.side (m + 1) : ℕ) : ℤ))
    (μ ν : Fin 4) :
    curvature (G.frameField (GasFamily.single θ s)) (blockCentre R.params.side Y + siteOfInt a) μ ν =
      curvature (G'.frameField (GasFamily.single θ' s')) (blockCentre R.params.side Y' + siteOfInt a) μ ν := by
  have hA : OffsetInBox (refinedRadius R.params.side (m + 1)) a := fun l => by
    have := hb l
    omega
  have hs : ∀ i : Fin 4, OffsetInBox (refinedRadius R.params.side (m + 1)) (a + Pi.single i 1) := by
    intro i l
    have h1 := hb l
    have h3 : |(Pi.single i (1 : ℤ) : Fin 4 → ℤ) l| ≤ 1 := by
      by_cases e : l = i
      · subst e
        simp
      · simp [e]
    have h4 : |(a + Pi.single i (1 : ℤ) : Fin 4 → ℤ) l| ≤ |a l| + 1 := (abs_add_le _ _).trans (by linarith)
    linarith
  have e₁ : ∀ i, (blockCentre R.params.side Y + siteOfInt a : TorusSite (n * R.params.side)) +
      TorusFields.unitStep (n * R.params.side) i = blockCentre R.params.side Y + siteOfInt (a + Pi.single i 1) :=
    fun i => by rw [TorusLumps.unitStep_eq_siteOfInt, add_siteOfInt_add]
  have e₂ : ∀ i, (blockCentre R.params.side Y' + siteOfInt a : TorusSite (n' * R.params.side)) +
      TorusFields.unitStep (n' * R.params.side) i = blockCentre R.params.side Y' + siteOfInt (a + Pi.single i 1) :=
    fun i => by rw [TorusLumps.unitStep_eq_siteOfInt, add_siteOfInt_add]
  unfold curvature holonomy
  rw [P.frameField_eq_offset hA μ, P.frameField_eq_offset hA ν, e₁, e₁, e₂, e₂, P.frameField_eq_offset (hs μ) ν,
    P.frameField_eq_offset (hs ν) μ]
end TransferData
end Hot
private theorem mem_torusHotSites {m : ℕ} {ℓ : StepParameters} {W : TorusField m} {z : TorusSite m} :
    z ∈ torusHotSites ℓ W ↔ ∃ l ∈ torusHotLumps ℓ W, z ∈ l := by
  simp only [torusHotSites, Finset.mem_biUnion, id_eq]
section Hull
variable {n' : ℕ} [NeZero n'] {G : GasGround R n} {G' : GasGround R n'} {Y : TorusSite n} {Y' : TorusSite n'}
  {N m : ℕ} {θ : GasSupport R n} {θ' : GasSupport R n'} {s : SupportState θ} {s' : SupportState θ'}
theorem mem_hot_of_curvature_eq {p p' : ℕ} [NeZero p] [NeZero p'] {ℓ : StepParameters} (hfit : ℓ.Admissible)
    (hL' : ℓ.side ∣ p') {W : TorusField p} {W' : TorusField p'} {y : TorusSite p} {y' : TorusSite p'}
    {a d : Fin 4 → ℤ} {μ ν : Fin 4} (hμ : μ < ν)
    (hs : ℓ.threshold ≤ curvature W (y + siteOfInt a) μ ν)
    (he : curvature W (y + siteOfInt a) μ ν = curvature W' (y' + siteOfInt a) μ ν)
    (hd : d ∈ plaquetteOffsets μ ν) : torusLumpOf ℓ (y' + siteOfInt (a + d)) ∈ torusHotLumps ℓ W' :=
  (mem_torusHotLumps_iff ℓ hfit hL' _ _).mpr ⟨y' + siteOfInt a, μ, ν, hμ, he ▸ hs, _,
    (mem_plaquetteVertices_iff_offset _ _ _ _).2 ⟨d, hd, add_siteOfInt_add _ _ _⟩, rfl⟩
namespace TransferData
variable (P : TransferData G G' Y Y' N m θ θ' s s')
include P
theorem side_dvd' : R.params.side ∣ n' * R.params.side := Dvd.intro_left n' rfl
theorem side_dvd : R.params.side ∣ n * R.params.side := Dvd.intro_left n rfl
theorem lt_torus : 2 ^ 17 < n * R.params.side := lt_of_isBlockTorusSide P.admissible P.isBlockSide
theorem lt_torus' : 2 ^ 17 < n' * R.params.side := lt_of_isBlockTorusSide P.admissible P.isBlockSide'
theorem exists_offset_of_core' {u : TorusSite (n' * R.params.side)} (hu : parentBlock R.params.side u ∈ θ'.core) :
    ∃ c, OffsetInBox (refinedRadius R.params.side m) c ∧ u = blockCentre R.params.side Y' + siteOfInt c := by
  obtain ⟨h, hh, e⟩ := P.core_mem_box' _ hu
  exact ⟨_, offsetInBox_refinedOffset P.side_odd hh _, eq_blockCentre_add_of_parentBlock e⟩
theorem exists_offset_of_core {u : TorusSite (n * R.params.side)} (hu : parentBlock R.params.side u ∈ θ.core) :
    ∃ c, OffsetInBox (refinedRadius R.params.side m) c ∧ u = blockCentre R.params.side Y + siteOfInt c := by
  obtain ⟨h, hh, e⟩ := P.core_mem_box _ hu
  exact ⟨_, offsetInBox_refinedOffset P.side_odd hh _, eq_blockCentre_add_of_parentBlock e⟩
theorem exists_offset_near {x u : TorusSite (n' * R.params.side)} (hu : _root_.YangMills.Construction.TorusFields.supDist x u ≤ 2)
    (hc : parentBlock R.params.side u ∈ θ'.core) :
    ∃ a, x = blockCentre R.params.side Y' + siteOfInt a ∧
      ∀ l, |a l| + 3 ≤ ((refinedRadius R.params.side (m + 1) : ℕ) : ℤ) := by
  obtain ⟨c, hc', rfl⟩ := P.exists_offset_of_core' hc
  obtain ⟨e, he, hb⟩ := exists_offset_of_supDist (blockCentre R.params.side Y' + siteOfInt c) x
  rw [_root_.YangMills.Construction.TorusFields.supDist_comm] at hu
  refine ⟨c + e, by rw [he, add_siteOfInt_add], fun l => ?_⟩
  have h1 := abs_add_le_of_box (A := ((refinedRadius R.params.side m : ℕ) : ℤ)) (B := 2) hc'
    (fun l => abs_le_natCast_of_natAbs_le ((hb l).trans hu)) l
  have h2 : ((refinedRadius R.params.side (m + 1) : ℕ) : ℤ) =
      ((refinedRadius R.params.side m : ℕ) : ℤ) + R.params.side := by
    rw [refinedRadius_succ]
    push_cast
    ring
  have h3 : (2 ^ 16 : ℤ) ≤ R.params.side := by exact_mod_cast P.admissible.L_ge
  omega
theorem recorded_iff {a : Fin 4 → ℤ} (ha : OffsetInBox (refinedRadius R.params.side N) a) :
    (blockCentre R.params.side Y + siteOfInt a : TorusSite (n * R.params.side)) ∈ G.recordedSites ↔
      (blockCentre R.params.side Y' + siteOfInt a : TorusSite (n' * R.params.side)) ∈ G'.recordedSites := by
  classical
  obtain ⟨h, o, hh, ho, rfl, -⟩ := exists_split_of_offsetInBox P.side_odd ha
  rw [← fineSite_eq_blockCentre_add, ← fineSite_eq_blockCentre_add]
  simp only [GasGround.recordedSites, Finset.mem_filter, Finset.mem_univ, true_and]
  have : G.state.labelAt (fineSite R.params.side Y h o) = G'.state.labelAt (fineSite R.params.side Y' h o) := by
    unfold CoarseState.labelAt
    rw [parentBlock_fineSite P.side_odd Y h o ho, parentBlock_fineSite P.side_odd Y' h o ho,
      P.groundsAgree.marking_eq h hh, siteOffset_fineSite, siteOffset_fineSite]
  rw [this]
theorem snd_iff {a : Fin 4 → ℤ} (ha : OffsetInBox (refinedRadius R.params.side N) a) :
    (blockCentre R.params.side Y + siteOfInt a : TorusSite (n * R.params.side)) ∈ θ.2 ↔
      (blockCentre R.params.side Y' + siteOfInt a : TorusSite (n' * R.params.side)) ∈ θ'.2 := by
  obtain ⟨c, o, hc, ho, rfl, -⟩ := exists_split_of_offsetInBox P.side_odd ha
  rw [← fineSite_eq_blockCentre_add, ← fineSite_eq_blockCentre_add]
  exact P.sameSupport.sites_iff c o hc ho
theorem isHull_ground' : IsHullState R.params R.range (G'.frameField GasFamily.empty) G'.recordedSites := by
  have h := P.ground_weight'.isHull
  rw [field_zero_eq_frameField P.side_odd P.two_le'] at h
  have e : (G'.settingOf GasFamily.empty).support = G'.recordedSites := by
    show G'.recordedSites ∪ (GasFamily.empty : GasFamily R n').sites = G'.recordedSites
    rw [Finset.eq_empty_of_forall_notMem fun z => not_mem_sites_empty (z := z), Finset.union_empty]
  rwa [e] at h
theorem hot_cases' {l : Finset (TorusSite (n' * R.params.side))}
    (hl : l ∈ torusHotLumps R.params (G'.frameField (GasFamily.single θ' s'))) :
    (∃ a d μ ν, μ < ν ∧ (∀ k, |a k| + 3 ≤ ((refinedRadius R.params.side (m + 1) : ℕ) : ℤ)) ∧
      d ∈ plaquetteOffsets μ ν ∧ l = torusLumpOf R.params (blockCentre R.params.side Y' + siteOfInt (a + d)) ∧
      torusLumpOf R.params (blockCentre R.params.side Y + siteOfInt (a + d)) ∈
        torusHotLumps R.params (G.frameField (GasFamily.single θ s))) ∨
      l ∈ torusHotLumps R.params (G'.frameField GasFamily.empty) := by
  classical
  obtain ⟨x, μ, ν, hμ, hs, z, hz, rfl⟩ := (mem_torusHotLumps_iff R.params P.admissible P.side_dvd' _ _).mp hl
  by_cases hc : ∃ u, _root_.YangMills.Construction.TorusFields.supDist x u ≤ 2 ∧ parentBlock R.params.side u ∈ θ'.core
  · obtain ⟨u, hu, hcu⟩ := hc
    obtain ⟨a, rfl, hb⟩ := P.exists_offset_near hu hcu
    obtain ⟨d, hd, rfl⟩ := (mem_plaquetteVertices_iff_offset _ _ _ _).1 hz
    have hb1 : ∀ l, |a l| + 1 ≤ ((refinedRadius R.params.side (m + 1) : ℕ) : ℤ) := fun l => by
      have := hb l
      omega
    refine Or.inl ⟨a, d, μ, ν, hμ, hb, hd, by rw [add_siteOfInt_add], ?_⟩
    exact mem_hot_of_curvature_eq P.admissible P.side_dvd hμ hs (P.curvature_eq_box hb1 μ ν).symm hd
  · refine Or.inr ((mem_torusHotLumps_iff R.params P.admissible P.side_dvd' _ _).mpr ⟨x, μ, ν, hμ, ?_, z, hz, rfl⟩)
    rw [← curvature_eq_of_agreeNear P.side_odd P.two_le' (agreeNear_single_empty_of_clear s' hc)]
    exact hs
theorem thickening_subset_support (hA : G.IsAllowed θ s) :
    thickening (2 * R.range) (torusHotSites R.params (G'.frameField (GasFamily.single θ' s'))) ⊆
      (G'.settingOf (GasFamily.single θ' s')).support := by
  classical
  intro u hu
  obtain ⟨x₁, hx₁, hux⟩ := (mem_thickening _ _ _).mp hu
  obtain ⟨l, hl, hxl⟩ := mem_torusHotSites.mp hx₁
  rcases P.hot_cases' hl with ⟨a, d, μ, ν, hμ, hb, hd, rfl, hlump⟩ | hl₀
  · obtain ⟨e, he, rfl⟩ := exists_offset_of_mem_torusLumpOf P.admissible P.side_dvd' hxl
    have he' : ∀ l, |e l| ≤ 2 ^ 15 := fun l => by exact_mod_cast he l
    have hback : blockCentre R.params.side Y + siteOfInt (a + d + e) ∈
        torusLumpOf R.params (blockCentre R.params.side Y + siteOfInt (a + d)) := by
      refine mem_torusLumpOf_transfer P.admissible P.side_dvd' P.side_dvd P.lt_torus'
        (sameBlockPosition_blockCentre Y' Y) he' ?_
      rw [add_siteOfInt_add _ (a + d) e]
      exact hxl
    have hx₂ : blockCentre R.params.side Y + siteOfInt (a + d + e) ∈
        torusHotSites R.params (G.frameField (GasFamily.single θ s)) :=
      mem_torusHotSites.mpr ⟨_, hlump, hback⟩
    rw [← add_siteOfInt_add] at hux
    obtain ⟨e₂, he₂, hb₂⟩ := exists_offset_of_supDist (blockCentre R.params.side Y' + siteOfInt (a + d + e)) u
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm] at hux
    have hbox : OffsetInBox (refinedRadius R.params.side N) (a + d + e + e₂) := by
      intro k
      have h1 := hb k
      have h2 := abs_le_two_of_mem_plaquetteOffsets hd k
      have h3 := he' k
      have h4 : |e₂ k| ≤ ((2 * R.range : ℕ) : ℤ) := abs_le_natCast_of_natAbs_le ((hb₂ k).trans hux)
      have h5 : ((refinedRadius R.params.side (m + 1) + 16 * R.range : ℕ) : ℤ) ≤
          ((refinedRadius R.params.side N : ℕ) : ℤ) := by
        exact_mod_cast P.refinedRadius_add_le
      have h6 : (2 ^ 16 : ℤ) ≤ R.range := by exact_mod_cast P.range_ge
      have h7 := abs_add_le (a k + d k + e k) (e₂ k)
      have h8 := abs_add_le (a k + d k) (e k)
      have h9 := abs_add_le (a k) (d k)
      simp only [Pi.add_apply]
      push_cast at h4 h5
      linarith
    have hclose : _root_.YangMills.Construction.TorusFields.supDist (blockCentre R.params.side Y + siteOfInt (a + d + e + e₂) : TorusSite (n * R.params.side))
        (blockCentre R.params.side Y + siteOfInt (a + d + e)) ≤ 2 * R.range := by
      rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
      refine _root_.YangMills.Construction.CongruentBoxes.supDist_le_of_abs_sub_le fun k => ?_
      have h4 : |e₂ k| ≤ ((2 * R.range : ℕ) : ℤ) := abs_le_natCast_of_natAbs_le ((hb₂ k).trans hux)
      simpa using h4
    have hin := hA.1.1 ((mem_thickening _ _ _).mpr ⟨_, hx₂, hclose⟩)
    have e3 : u = blockCentre R.params.side Y' + siteOfInt (a + d + e + e₂) := by
      rw [he₂]
      simp only [add_siteOfInt_add]
    rw [e3]
    rcases mem_support_single.1 hin with c | c
    · exact mem_support_single.2 (Or.inl ((P.recorded_iff hbox).1 c))
    · exact mem_support_single.2 (Or.inr ((P.snd_iff hbox).1 c))
  · have h1 := P.isHull_ground'.1 ((mem_thickening _ _ _).mpr ⟨x₁, mem_torusHotSites.mpr ⟨l, hl₀, hxl⟩, hux⟩)
    exact mem_support_single.2 (Or.inl h1)
theorem lt_supDist_recorded' {u v : TorusSite (n' * R.params.side)} (hu : u ∈ θ'.2) (hv : v ∈ G'.recordedSites) :
    R.range < _root_.YangMills.Construction.TorusFields.supDist u v := by
  have := P.isSupport'.far_from_anchor u (mem_sites_of_mem_snd θ' hu) v (mem_anchorSites_of_mem_recorded hv)
  omega
theorem lt_supDist_recorded {u v : TorusSite (n * R.params.side)} (hu : u ∈ θ.2) (hv : v ∈ G.recordedSites) :
    R.range < _root_.YangMills.Construction.TorusFields.supDist u v := by
  have := P.isSupport.far_from_anchor u (mem_sites_of_mem_snd θ hu) v (mem_anchorSites_of_mem_recorded hv)
  omega
theorem mem_hot_of_ground' {l : Finset (TorusSite (n' * R.params.side))}
    (hl : l ∈ torusHotLumps R.params (G'.frameField GasFamily.empty)) :
    l ∈ torusHotLumps R.params (G'.frameField (GasFamily.single θ' s')) := by
  classical
  have hfar := P.side_le_range
  have hbig := P.range_ge
  obtain ⟨x, μ, ν, hμ, hs, z, hz, hlz⟩ := (mem_torusHotLumps_iff R.params P.admissible P.side_dvd' _ _).mp hl
  have hzl : z ∈ l := by
    rw [hlz]
    exact mem_torusLumpOf_self z
  have hst : z ∈ G'.recordedSites := P.isHull_ground'.1 ((mem_thickening _ _ _).mpr
    ⟨z, mem_torusHotSites.mpr ⟨l, hl, hzl⟩, by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega⟩)
  have hd := _root_.YangMills.Construction.InBoxTransfer.supDist_le_two_of_mem_plaquetteVertices hz
  have ag := agreeNear_single_empty_of_far (x := x) (d := 2) P.isSupport' s' (mem_anchorSites_of_mem_recorded hst)
    (by omega)
  refine (mem_torusHotLumps_iff R.params P.admissible P.side_dvd' _ _).mpr ⟨x, μ, ν, hμ, ?_, z, hz, hlz⟩
  rw [curvature_eq_of_agreeNear P.side_odd P.two_le' ag]
  exact hs
theorem congruent_snd : CongruentInBoxes θ.2 θ'.2 (blockCentre R.params.side Y) (blockCentre R.params.side Y')
    (refinedRadius R.params.side N) := by
  have hmono : refinedRadius R.params.side m ≤ refinedRadius R.params.side N := by
    have := P.refinedRadius_add_le
    have := refinedRadius_succ R.params.side m
    omega
  refine ⟨fun z hz => ?_, fun z hz => ?_, fun a ha => P.snd_iff ha⟩
  · obtain ⟨c, hc, e⟩ := P.exists_offset_of_core (GasSupport.parentBlock_mem_core_of_mem_sites hz)
    exact ⟨c, offsetInBox_mono hmono hc, e⟩
  · obtain ⟨c, hc, e⟩ := P.exists_offset_of_core' (GasSupport.parentBlock_mem_core_of_mem_sites hz)
    exact ⟨c, offsetInBox_mono hmono hc, e⟩
theorem ballInBox_of_mem_sites {a : Fin 4 → ℤ}
    (hz : (blockCentre R.params.side Y + siteOfInt a : TorusSite (n * R.params.side)) ∈ θ.sites)
    (ha : OffsetInBox (refinedRadius R.params.side N) a) : BallInBox (refinedRadius R.params.side m) (4 * R.range) a := by
  intro e he
  have hw := P.refinedRadius_add_le
  have hst := refinedRadius_succ R.params.side m
  have hmono : refinedRadius R.params.side m ≤ refinedRadius R.params.side N := by omega
  obtain ⟨c, hc, e0⟩ := P.exists_offset_of_core (GasSupport.parentBlock_mem_core hz)
  have e1 : a = c := eq_of_add_siteOfInt_eq P.refinedRadius_lt ha (offsetInBox_mono hmono hc) e0
  subst e1
  have hbox : OffsetInBox (refinedRadius R.params.side N) (a + e) := by
    intro l
    have h1 := abs_add_le_of_box (A := ((refinedRadius R.params.side m : ℕ) : ℤ)) (B := ((4 * R.range : ℕ) : ℤ)) hc he l
    have h2 : ((refinedRadius R.params.side m + 4 * R.range : ℕ) : ℤ) ≤ ((refinedRadius R.params.side N : ℕ) : ℤ) := by
      exact_mod_cast (by omega : refinedRadius R.params.side m + 4 * R.range ≤ refinedRadius R.params.side N)
    push_cast at h1 h2 ⊢
    linarith
  have hcore : parentBlock R.params.side (blockCentre R.params.side Y + siteOfInt (a + e)) ∈ θ.core := by
    refine parentBlock_mem_core θ hz ?_
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
    exact _root_.YangMills.Construction.CongruentBoxes.supDist_le_of_abs_sub_le fun l => by simpa using he l
  obtain ⟨h₀, h0, e2⟩ := P.core_mem_box _ hcore
  rw [parentBlock_blockCentre_add] at e2
  have bs := (offsetInBox_refinedRadius_iff P.side_odd).mp hbox
  have e3 := eq_of_add_siteOfInt_eq P.groundsAgree.lt_extent bs (offsetInBox_mono (by have := P.add_two_le; omega) h0) e2
  exact (offsetInBox_refinedRadius_iff P.side_odd).mpr (e3 ▸ h0)
theorem ballsInBox_snd : BallsInBox (blockCentre R.params.side Y) (refinedRadius R.params.side N) θ.2 (4 * R.range) := by
  intro a ha hz e he
  have h := P.ballInBox_of_mem_sites (mem_sites_of_mem_snd θ hz) ha e he
  have hw := P.refinedRadius_add_le
  have hst := refinedRadius_succ R.params.side m
  exact offsetInBox_mono (by omega) h
theorem mem_chainComponents_support {K : Finset (TorusSite (n * R.params.side))} (hK : K ∈ chainComponents R.range θ.2) :
    K ∈ chainComponents R.range (G.settingOf (GasFamily.single θ s)).support := by
  classical
  obtain ⟨z, hz, rfl⟩ := mem_chainComponents.mp hK
  have hzY : z ∈ (G.settingOf (GasFamily.single θ s)).support := mem_support_single.2 (Or.inr hz)
  have hsub : θ.2 ⊆ (G.settingOf (GasFamily.single θ s)).support := fun w hw => mem_support_single.2 (Or.inr hw)
  have hsep : ∀ u ∈ θ.2, ∀ v ∈ (G.settingOf (GasFamily.single θ s)).support, v ∉ θ.2 → R.range < _root_.YangMills.Construction.TorusFields.supDist u v := by
    intro u hu v hv hn
    rcases mem_support_single.1 hv with c | c
    · exact P.lt_supDist_recorded hu c
    · exact absurd c hn
  refine mem_chainComponents.mpr ⟨z, hzY, ?_⟩
  ext w
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨hsub h1, chainConnected_mono hsub h2⟩
  · rintro ⟨_, h2⟩
    exact chainConnected_of_separated hsep hz h2
theorem exists_hot_meets (hA : G.IsAllowed θ s) :
    ∀ X ∈ chainComponents R.range (G'.settingOf (GasFamily.single θ' s')).support,
      ∃ l ∈ torusHotLumps R.params (G'.frameField (GasFamily.single θ' s')), (l ∩ X).Nonempty := by
  classical
  intro X hX
  obtain ⟨z, hz⟩ := exists_mem_of_mem_chainComponents hX
  have hsubY : ∀ {Y₁ : Finset (TorusSite (n' * R.params.side))},
      (∀ w ∈ Y₁, w ∈ (G'.settingOf (GasFamily.single θ' s')).support) →
        Y₁ ⊆ (G'.settingOf (GasFamily.single θ' s')).support := fun h w hw => h w hw
  rcases mem_support_single.1 (subset_of_mem_chainComponents hX hz) with a | a
  · have key := mem_chainComponents_of_separated (Y₁ := G'.recordedSites)
      (hsubY fun w hw => mem_support_single.2 (Or.inl hw))
      (fun u hu v hv hn => by
        rcases mem_support_single.1 hv with c | c
        · exact absurd c hn
        · rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
          exact P.lt_supDist_recorded' c hu) hX hz a
    obtain ⟨l, hl, hw⟩ := P.isHull_ground'.2 X key.1
    exact ⟨l, P.mem_hot_of_ground' hl, hw⟩
  · have key := mem_chainComponents_of_separated (Y₁ := θ'.2) (hsubY fun w hw => mem_support_single.2 (Or.inr hw))
      (fun u hu v hv hn => by
        rcases mem_support_single.1 hv with c | c
        · exact P.lt_supDist_recorded' hu c
        · exact absurd c hn) hX hz a
    have hr : R.range ≤ 4 * R.range := by omega
    obtain ⟨K, hK, hKX⟩ := exists_congruent_component_symm P.refinedRadius_lt P.refinedRadius_lt' P.congruent_snd
      (P.ballsInBox_snd.mono (Finset.Subset.refl _) hr) key.1
    obtain ⟨l, hl, w, hw⟩ := hA.1.2 K (P.mem_chainComponents_support hK)
    obtain ⟨hwl, hwK⟩ := Finset.mem_inter.mp hw
    have hw2 : w ∈ θ.2 := subset_of_mem_chainComponents hK hwK
    obtain ⟨x, μ, ν, hμ, hs, z₂, hz₂, rfl⟩ := (mem_torusHotLumps_iff R.params P.admissible P.side_dvd _ _).mp hl
    obtain ⟨c, hc, rfl⟩ := P.exists_offset_of_core (GasSupport.parentBlock_mem_core_of_mem_sites hw2)
    obtain ⟨e₁, he₁, hwe⟩ := exists_offset_of_mem_torusLumpOf P.admissible P.side_dvd hwl
    obtain ⟨d, hd, rfl⟩ := (mem_plaquetteVertices_iff_offset _ _ _ _).1 hz₂
    have hx : x = blockCentre R.params.side Y + siteOfInt (c - e₁ - d) := by
      have e5 : (blockCentre R.params.side Y + siteOfInt c : TorusSite (n * R.params.side)) =
          blockCentre R.params.side Y + siteOfInt (c - e₁ - d) + siteOfInt d + siteOfInt e₁ := by
        simp only [← add_siteOfInt_add]
        congr 2
        ring
      rw [e5] at hwe
      exact (add_right_cancel (add_right_cancel hwe)).symm
    subst hx
    have hLz : (2 ^ 16 : ℤ) ≤ R.params.side := by exact_mod_cast P.admissible.L_ge
    have hrad : ((refinedRadius R.params.side (m + 1) : ℕ) : ℤ) =
        ((refinedRadius R.params.side m : ℕ) : ℤ) + R.params.side := by
      rw [refinedRadius_succ]
      push_cast
      ring
    have hb : ∀ k, |(c - e₁ - d) k| + 1 ≤ ((refinedRadius R.params.side (m + 1) : ℕ) : ℤ) := by
      intro k
      have h1 := hc k
      have h2 : |e₁ k| ≤ 2 ^ 15 := by exact_mod_cast he₁ k
      have h3 := abs_le_two_of_mem_plaquetteOffsets hd k
      have h4 : |(c - e₁ - d) k| ≤ |c k| + |e₁ k| + |d k| := by
        simp only [Pi.sub_apply]
        have a1 := abs_sub (c k - e₁ k) (d k)
        have a2 := abs_sub (c k) (e₁ k)
        linarith
      linarith
    have hlump := mem_hot_of_curvature_eq P.admissible P.side_dvd' hμ hs (P.curvature_eq_box hb μ ν) hd
    have he' : ∀ k, |e₁ k| ≤ 2 ^ 15 := fun k => by exact_mod_cast he₁ k
    have ec : c - e₁ - d + d + e₁ = c := by abel
    have hcM : OffsetInBox (refinedRadius R.params.side N) c := by
      have := P.refinedRadius_add_le
      have := refinedRadius_succ R.params.side m
      exact offsetInBox_mono (by omega) hc
    have hp : blockCentre R.params.side Y' + siteOfInt (c - e₁ - d + d + e₁) ∈
        torusLumpOf R.params (blockCentre R.params.side Y' + siteOfInt (c - e₁ - d + d)) := by
      refine mem_torusLumpOf_transfer P.admissible P.side_dvd P.side_dvd' P.lt_torus
        (sameBlockPosition_blockCentre Y Y') he' ?_
      rw [ec, add_siteOfInt_add _ (c - e₁ - d) d]
      exact hwl
    rw [ec] at hp
    exact ⟨_, hlump, _, Finset.mem_inter.mpr ⟨hp, (hKX.2.2 c hcM).1 hwK⟩⟩
theorem labelling_congr' {s₀ : ChartSetting R n'} {z z' : TorusSite (n' * R.params.side)} (e : z = z')
    (hz : z ∈ s₀.support) (hz' : z' ∈ s₀.support) : s₀.labelling ⟨z, hz⟩ = s₀.labelling ⟨z', hz'⟩ := by
  subst e
  rfl
theorem labelling_congr {s₀ : ChartSetting R n} {z z' : TorusSite (n * R.params.side)} (e : z = z')
    (hz : z ∈ s₀.support) (hz' : z' ∈ s₀.support) : s₀.labelling ⟨z, hz⟩ = s₀.labelling ⟨z', hz'⟩ := by
  subst e
  rfl
theorem clusterFactor_eq {K : Finset (TorusSite (n * R.params.side))} {K' : Finset (TorusSite (n' * R.params.side))}
    (hKK : CongruentInBoxes K K' (blockCentre R.params.side Y) (blockCentre R.params.side Y')
      (refinedRadius R.params.side N)) (hK : K ⊆ θ.2) (hK' : K' ⊆ θ'.2) :
    R.clusterFactor (n * R.params.side) (G.frameField (GasFamily.single θ s)) (G.settingOf (GasFamily.single θ s)).support
        (G.settingOf (GasFamily.single θ s)).labelling K =
      R.clusterFactor (n' * R.params.side) (G'.frameField (GasFamily.single θ' s'))
        (G'.settingOf (GasFamily.single θ' s')).support (G'.settingOf (GasFamily.single θ' s')).labelling K' := by
  refine P.hasExpansions.2.one_rule (n * R.params.side) (n' * R.params.side) P.isBlockSide P.isBlockSide' _ _ _ _ _ _
    K K' _ _ _ P.refinedRadius_lt P.refinedRadius_lt'
    (fun z hz => mem_support_single.2 (Or.inr (hK hz))) (fun z hz => mem_support_single.2 (Or.inr (hK' hz)))
    (sameBlockPosition_blockCentre Y Y') hKK ?_ ?_
  · intro b hb h1 _
    have hst := refinedRadius_succ R.params.side m
    have hw := P.refinedRadius_add_le
    obtain ⟨c, hc, e⟩ := P.exists_offset_of_core (GasSupport.parentBlock_mem_core_of_mem_sites (hK h1))
    have e1 : b.1 = c := eq_of_add_siteOfInt_eq P.refinedRadius_lt hb.1 (offsetInBox_mono (by omega) hc) e
    have hbox : OffsetInBox (refinedRadius R.params.side (m + 1)) b.1 := by
      rw [e1]
      exact offsetInBox_mono (by omega) hc
    exact P.frameField_eq_offset hbox b.2
  · intro a ha hz hz' hx
    obtain ⟨c, o, hc, ho, ea, -⟩ := exists_split_of_offsetInBox P.side_odd ha
    subst ea
    have e1 := fineSite_eq_blockCentre_add (L := R.params.side) Y c o
    have e2 := fineSite_eq_blockCentre_add (L := R.params.side) Y' c o
    have hz₁ : fineSite R.params.side Y c o ∈ (G.settingOf (GasFamily.single θ s)).support := by rw [e1]; exact hz
    have hz₂ : fineSite R.params.side Y' c o ∈ (G'.settingOf (GasFamily.single θ' s')).support := by rw [e2]; exact hz'
    have := P.settingsAgree.labelling_eq c o hz₁ hz₂ hc ho
    rw [P.labelling_congr e1.symm hz hz₁, P.labelling_congr' e2.symm hz' hz₂]
    exact this
theorem clusterFactor_ne_zero (hA : G.IsAllowed θ s) : ∀ X ∈ chainComponents R.range θ'.2,
    R.clusterFactor (n' * R.params.side) (G'.frameField (GasFamily.single θ' s'))
      (G'.settingOf (GasFamily.single θ' s')).support (G'.settingOf (GasFamily.single θ' s')).labelling X ≠ 0 := by
  intro X hX
  have hr : R.range ≤ 4 * R.range := by omega
  obtain ⟨K, hK, hKX⟩ := exists_congruent_component_symm P.refinedRadius_lt P.refinedRadius_lt' P.congruent_snd
    (P.ballsInBox_snd.mono (Finset.Subset.refl _) hr) hX
  rw [← P.clusterFactor_eq hKX (subset_of_mem_chainComponents hK) (subset_of_mem_chainComponents hX)]
  exact hA.2.1 K hK
theorem gaugeAt_eq {kk o : Fin 4 → ℤ} (hkk : OffsetInBox (m + 1) kk) (ho : o ∈ centredCube R.params.side) :
    gaugeAt (R := R) (G.frameField (GasFamily.single θ s)) (fineSite R.params.side Y kk o) =
      gaugeAt (R := R) (G'.frameField (GasFamily.single θ' s')) (fineSite R.params.side Y' kk o) := by
  have hodd := P.side_odd
  set A : Fin 4 → ℤ := fun i => ((Y i).cast : ℤ) + kk i with hA
  set A' : Fin 4 → ℤ := fun i => ((Y' i).cast : ℤ) + kk i with hA'
  show gaugeAt (R := R) _ (siteOfInt (blockPoint R.params.side A o)) =
    gaugeAt (R := R) _ (siteOfInt (blockPoint R.params.side A' o))
  rw [gaugeAt_blockPoint hodd _ A o ho, gaugeAt_blockPoint hodd _ A' o ho]
  have hc := (BlockOffsets.mem_centredCube_iff o).mp ho
  have key := pathHolonomy_congr (L := R.params.side) (G.frameField (GasFamily.single θ s))
    (G'.frameField (GasFamily.single θ' s')) (fun i => (R.params.side : ℤ) * A i)
    (fun i => (R.params.side : ℤ) * A' i) (axisPath o 1) 0 ?_
  · simpa only [add_zero] using key
  · intro b hb
    obtain ⟨g1, g2, g3⟩ := isAxialBond_of_mem_axisPath hc b hb
    have hb1 : b.1 ∈ centredCube R.params.side := (BlockOffsets.mem_centredCube_iff _).mpr g1
    exact P.frameField_eq_box hkk hb1 b.2
theorem chartCoord_eq {kk o : Fin 4 → ℤ} (hkk : OffsetInBox m kk) (ho : o ∈ centredCube R.params.side) (i : Fin 4) :
    chartCoord R.params G.coarse (G.frameField (GasFamily.single θ s)) (fineSite R.params.side Y kk o, i) =
      chartCoord R.params G'.coarse (G'.frameField (GasFamily.single θ' s')) (fineSite R.params.side Y' kk o, i) := by
  classical
  have hodd := P.side_odd
  have hkk1 : OffsetInBox (m + 1) kk := offsetInBox_mono (by omega) hkk
  have hcr : ∀ (k : ℕ) [NeZero k], 2 ≤ k → ∀ (Z : TorusSite k),
      IsCrossingBond (F := stepBlockFrame R.params.side k)
        (torusSiteInFrame (stepBlockFrame R.params.side k) 0 (fineSite R.params.side Z kk o), i) ↔
          o + Pi.single i 1 ∉ centredCube R.params.side := by
    intro k _ hk Z
    show IsCrossingBond (F := stepBlockFrame R.params.side k) (torusSiteInFrame (stepBlockFrame R.params.side k) 0
      (siteOfInt (blockPoint R.params.side (fun i => ((Z i).cast : ℤ) + kk i) o)), i) ↔ _
    rw [torusSiteInFrame_siteOfInt]
    exact isCrossingBond_blockPoint_iff hodd hk _ o ho i
  rw [BlockTrees.chartCoord_eq, BlockTrees.chartCoord_eq]
  simp only
  have t1 : blockGauge R.params.side (G.frameField (GasFamily.single θ s)) (fineSite R.params.side Y kk o) =
      blockGauge R.params.side (G'.frameField (GasFamily.single θ' s')) (fineSite R.params.side Y' kk o) :=
    P.gaugeAt_eq hkk1 ho
  have t3 := P.frameField_eq_box hkk1 ho i
  by_cases hcube : o + Pi.single i 1 ∈ centredCube R.params.side
  · have t2 : blockGauge R.params.side (G.frameField (GasFamily.single θ s))
          (fineSite R.params.side Y kk o + TorusFields.unitStep (n * R.params.side) i) =
        blockGauge R.params.side (G'.frameField (GasFamily.single θ' s'))
          (fineSite R.params.side Y' kk o + TorusFields.unitStep (n' * R.params.side) i) := by
      rw [fineSite_add_unitStep, fineSite_add_unitStep]
      exact P.gaugeAt_eq hkk1 hcube
    rw [if_neg (fun h => ((hcr n P.two_le Y).mp h) hcube), if_neg (fun h => ((hcr n' P.two_le' Y').mp h) hcube),
      t1, t2, t3]
  · have hwrap : o + Pi.single i 1 - (R.params.side : ℤ) • Pi.single i 1 ∈ centredCube R.params.side := by
      have hL : ((R.params.side : ℤ) - 1) / 2 + ((R.params.side : ℤ) - 1) / 2 + 1 = (R.params.side : ℤ) := by
        obtain ⟨H, hH⟩ := hodd
        rw [hH]
        push_cast
        omega
      have hcm := (mem_centredCube_iff' _ _).1 ho
      have hi : o i = ((R.params.side : ℤ) - 1) / 2 := by
        by_contra hne
        refine hcube ((mem_centredCube_iff' _ _).2 fun l => ?_)
        have := hcm l
        by_cases e : l = i
        · subst e
          simp only [Pi.add_apply, Pi.single_eq_same]
          omega
        · simpa [Pi.single_apply, e] using this
      refine (mem_centredCube_iff' _ _).2 fun l => ?_
      have := hcm l
      by_cases e : l = i
      · subst e
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
        omega
      · simpa [Pi.single_apply, e] using this
    have hin1 : OffsetInBox (m + 1) (kk + Pi.single i 1) := by
      intro l
      have h1 := hkk l
      have h3 : |(Pi.single i (1 : ℤ) : Fin 4 → ℤ) l| ≤ 1 := by
        by_cases e : l = i
        · subst e
          simp
        · simp [e]
      have h4 : |(kk + Pi.single i (1 : ℤ) : Fin 4 → ℤ) l| ≤ |kk l| + 1 := (abs_add_le _ _).trans (by linarith)
      push_cast
      linarith
    have t2 : blockGauge R.params.side (G.frameField (GasFamily.single θ s))
          (fineSite R.params.side Y kk o + TorusFields.unitStep (n * R.params.side) i) =
        blockGauge R.params.side (G'.frameField (GasFamily.single θ' s'))
          (fineSite R.params.side Y' kk o + TorusFields.unitStep (n' * R.params.side) i) := by
      rw [fineSite_add_unitStep, fineSite_add_unitStep, fineSite_wrap, fineSite_wrap]
      exact P.gaugeAt_eq hin1 hwrap
    have hV : G.coarse (parentBlock R.params.side (fineSite R.params.side Y kk o)) i =
        G'.coarse (parentBlock R.params.side (fineSite R.params.side Y' kk o)) i := by
      rw [parentBlock_fineSite hodd Y kk o ho, parentBlock_fineSite hodd Y' kk o ho]
      have hN := P.add_two_le
      exact P.groundsAgree.coarse_agree (kk, i) ⟨offsetInBox_mono (by omega) hkk, offsetInBox_mono (by omega) hin1⟩
    rw [if_pos ((hcr n P.two_le Y).mpr hcube), if_pos ((hcr n' P.two_le' Y').mpr hcube), t1, t2, t3, hV]
theorem offsetInBox_of_mem_coreBonds {q : NearBondIndex} (hq : IsNearIndex R.params.side N q)
    (hb : nearBond R.params.side Y q ∈ θ.coreBonds) : OffsetInBox m q.1 := by
  have hc := GasSupport.parentBlock_mem_core_of_mem_coreBonds hb
  have e0 : parentBlock R.params.side (nearBond R.params.side Y q).1 = Y + siteOfInt q.1 :=
    parentBlock_fineSite P.side_odd Y q.1 q.2.1 hq.2
  rw [e0] at hc
  obtain ⟨h₀, h0, e⟩ := P.core_mem_box _ hc
  have := eq_of_add_siteOfInt_eq P.groundsAgree.lt_extent hq.1 (offsetInBox_mono (by have := P.add_two_le; omega) h0) e
  rw [this]
  exact h0
theorem bondMark_eq {q : NearBondIndex} (hq : IsNearIndex R.params.side N q)
    (hb : nearBond R.params.side Y q ∈ θ.coreBonds) :
    bondMark R G.coarse (G.frameField (GasFamily.single θ s)) (nearBond R.params.side Y q) =
      bondMark R G'.coarse (G'.frameField (GasFamily.single θ' s')) (nearBond R.params.side Y' q) := by
  obtain ⟨h, o, i⟩ := q
  have hm := P.offsetInBox_of_mem_coreBonds hq hb
  have ho : o ∈ centredCube R.params.side := hq.2
  unfold bondMark
  have e1 : chartCoord R.params G.coarse (G.frameField (GasFamily.single θ s)) (nearBond R.params.side Y (h, o, i)) =
      chartCoord R.params G'.coarse (G'.frameField (GasFamily.single θ' s')) (nearBond R.params.side Y' (h, o, i)) :=
    P.chartCoord_eq hm ho i
  have e2 : frameCoord R.params R.anchorRadius R.depth R.frameReach G.coarse (nearBond R.params.side Y (h, o, i)) =
      frameCoord R.params R.anchorRadius R.depth R.frameReach G'.coarse (nearBond R.params.side Y' (h, o, i)) :=
    P.frame_eq (offsetInBox_mono (by omega) hm) ho i
  rw [e1, e2]
theorem mem_markedBonds_iff {q : NearBondIndex} (hq : IsNearIndex R.params.side N q) :
    nearBond R.params.side Y q ∈ markedBonds R G.cut ↔ nearBond R.params.side Y' q ∈ markedBonds R G'.cut := by
  classical
  obtain ⟨h, o, i⟩ := q
  have ho : o ∈ centredCube R.params.side := hq.2
  show ((fineSite R.params.side Y h o, i) : TorusBond (n * R.params.side)) ∈ markedBonds R G.cut ↔
    ((fineSite R.params.side Y' h o, i) : TorusBond (n' * R.params.side)) ∈ markedBonds R G'.cut
  unfold markedBonds
  simp only [Finset.mem_filter]
  rw [fineSite_mem_chartBonds_iff P.side_odd P.two_le P.two_le' Y Y' h o ho i, parentBlock_fineSite P.side_odd Y h o ho,
    parentBlock_fineSite P.side_odd Y' h o ho, P.groundsAgree.cut_iff h hq.1]
theorem exists_index_of_mem_coreBonds {b : TorusBond (n * R.params.side)} (hb : b ∈ θ.coreBonds) :
    ∃ q, IsNearIndex R.params.side N q ∧ b = nearBond R.params.side Y q := by
  obtain ⟨h, hh, e⟩ := P.sameSupport.core_mem _ (GasSupport.parentBlock_mem_core_of_mem_coreBonds hb)
  obtain ⟨c, hc, e2⟩ := (show ∃ c, OffsetInBox (refinedRadius R.params.side N) c ∧
      b.1 = blockCentre R.params.side Y + siteOfInt c from
    ⟨_, offsetInBox_refinedOffset P.side_odd hh _, eq_blockCentre_add_of_parentBlock e⟩)
  obtain ⟨k, o, hk, ho, rfl, -⟩ := exists_split_of_offsetInBox P.side_odd hc
  exact ⟨(k, o, b.2), ⟨hk, ho⟩, Prod.ext (by rw [e2]; exact (fineSite_eq_blockCentre_add Y k o).symm) rfl⟩
theorem exists_index_of_mem_coreBonds' {b : TorusBond (n' * R.params.side)} (hb : b ∈ θ'.coreBonds) :
    ∃ q, IsNearIndex R.params.side N q ∧ b = nearBond R.params.side Y' q := by
  obtain ⟨h, hh, e⟩ := P.sameSupport.core_mem' _ (GasSupport.parentBlock_mem_core_of_mem_coreBonds hb)
  obtain ⟨c, hc, e2⟩ := (show ∃ c, OffsetInBox (refinedRadius R.params.side N) c ∧
      b.1 = blockCentre R.params.side Y' + siteOfInt c from
    ⟨_, offsetInBox_refinedOffset P.side_odd hh _, eq_blockCentre_add_of_parentBlock e⟩)
  obtain ⟨k, o, hk, ho, rfl, -⟩ := exists_split_of_offsetInBox P.side_odd hc
  exact ⟨(k, o, b.2), ⟨hk, ho⟩, Prod.ext (by rw [e2]; exact (fineSite_eq_blockCentre_add Y' k o).symm) rfl⟩
theorem index_injective {k : ℕ} [NeZero k] (Z : TorusSite k) (hk : 2 * N + 2 < k) {q q' : NearBondIndex}
    (hq : IsNearIndex R.params.side N q) (hq' : IsNearIndex R.params.side N q')
    (e : nearBond R.params.side Z q = nearBond R.params.side Z q') : q = q' := by
  obtain ⟨h, o, i⟩ := q
  obtain ⟨h', o', i'⟩ := q'
  have e1 : fineSite R.params.side Z h o = fineSite R.params.side Z h' o' := congrArg Prod.fst e
  have e2 : i = i' := congrArg Prod.snd e
  have hb := congrArg (parentBlock R.params.side) e1
  rw [parentBlock_fineSite P.side_odd Z h o hq.2, parentBlock_fineSite P.side_odd Z h' o' hq'.2] at hb
  have h1 : h = h' := eq_of_add_siteOfInt_eq hk hq.1 hq'.1 hb
  subst h1
  have h2 := fineSite_injective Z h P.side_odd hq.2 hq'.2 e1
  exact Prod.ext rfl (Prod.ext h2 e2)
theorem supportMarks_eq : G.supportMarks θ (G.frameField (GasFamily.single θ s)) =
    G'.supportMarks θ' (G'.frameField (GasFamily.single θ' s')) := by
  classical
  unfold GasGround.supportMarks
  refine prod_eq_prod_of_rel (fun b b' => ∃ q, IsNearIndex R.params.side N q ∧ b = nearBond R.params.side Y q ∧
    b' = nearBond R.params.side Y' q) _ _ ?_ ?_ ?_ ?_ ?_
  · intro b hb
    obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hb
    obtain ⟨q, hq, rfl⟩ := P.exists_index_of_mem_coreBonds h1
    exact ⟨_, Finset.mem_inter.mpr ⟨(P.coreBonds_iff q hq).1 h1, (P.mem_markedBonds_iff hq).1 h2⟩, q, hq, rfl, rfl⟩
  · intro b hb
    obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hb
    obtain ⟨q, hq, rfl⟩ := P.exists_index_of_mem_coreBonds' h1
    exact ⟨_, Finset.mem_inter.mpr ⟨(P.coreBonds_iff q hq).2 h1, (P.mem_markedBonds_iff hq).2 h2⟩, q, hq, rfl, rfl⟩
  · rintro _ _ _ _ _ _ ⟨q, hq, rfl, rfl⟩ ⟨q', hq', e, rfl⟩
    rw [P.index_injective Y P.groundsAgree.lt_extent hq hq' e]
  · rintro _ _ _ _ _ _ ⟨q, hq, rfl, rfl⟩ ⟨q', hq', rfl, e⟩
    rw [P.index_injective Y' P.groundsAgree.lt_extent' hq hq' e]
  · rintro _ ha _ _ ⟨q, hq, rfl, rfl⟩
    have hs := (Finset.mem_inter.mp ha).1
    have hbad : nearBond R.params.side Y q ∈ θ.1 ↔ nearBond R.params.side Y' q ∈ θ'.1 := P.sameSupport.bad_iff q hq
    have hm := P.bondMark_eq hq hs
    by_cases hb : nearBond R.params.side Y q ∈ θ.1
    · rw [if_pos hb, if_pos (hbad.1 hb), hm]
    · rw [if_neg hb, if_neg (fun c => hb (hbad.2 c)), hm]
theorem bondMark_ne_zero (hA : G.IsAllowed θ s) : ∀ b ∈ θ'.coreBonds ∩ markedBonds R G'.cut, b ∉ θ'.1 →
    bondMark R G'.coarse (G'.frameField (GasFamily.single θ' s')) b ≠ 0 := by
  intro b hb hn
  obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hb
  obtain ⟨q, hq, rfl⟩ := P.exists_index_of_mem_coreBonds' h1
  have hs := (P.coreBonds_iff q hq).2 h1
  rw [← P.bondMark_eq hq hs]
  exact hA.2.2.1 _ (Finset.mem_inter.mpr ⟨hs, (P.mem_markedBonds_iff hq).2 h2⟩)
    fun c => hn ((P.sameSupport.bad_iff q hq).1 c)
end TransferData
end Hull
section NearbyLumps
theorem isBaseChoice_iff {F : BlockFrame} {J₀ : ℕ} {h : Finset (Finset (F.Site F.depth))}
    {b : F.Cell → F.Site F.depth} : IsBaseChoice J₀ h b ↔ ∀ y, b y ∈ baseSitesAt J₀ h y := by
  classical
  unfold IsBaseChoice baseSitesAt
  refine forall_congr' fun y => ?_
  by_cases c : nearbyLumps h y = ∅ ∨ IsCrowded J₀ h y
  · rw [if_pos c]
    simp [c]
  · rw [if_neg c]
    simp only [c, false_imp_iff, true_and, not_false_eq_true, true_imp_iff, Finset.mem_filter]
theorem baseSitesAt_congr {F : BlockFrame} {J₀ : ℕ} {H H' : Finset (Finset (F.Site F.depth))} {y : F.Cell}
    (e : nearbyLumps H y = nearbyLumps H' y) : baseSitesAt J₀ H y = baseSitesAt J₀ H' y := by
  classical
  have hc : IsCrowded J₀ H y ↔ IsCrowded J₀ H' y := by
    unfold IsCrowded
    rw [e]
  have hbx : excludedBoxes J₀ H y = excludedBoxes J₀ H' y := by
    unfold excludedBoxes
    by_cases h : IsCrowded J₀ H y
    · rw [if_pos h, if_pos (hc.mp h)]
    · rw [if_neg h, if_neg fun c => h (hc.mpr c), e]
  unfold baseSitesAt
  rw [e, hbx]
  by_cases h : nearbyLumps H' y = ∅ ∨ IsCrowded J₀ H y
  · rw [if_pos h, if_pos (h.imp id hc.mp)]
  · rw [if_neg h, if_neg fun c => h (c.imp id hc.mpr)]
theorem exists_hot_plaquette_near (hL : Odd R.params.side) (hn : 2 ≤ n) (W : TorusField (n * R.params.side))
    (c₀ : TorusSite n) {l : Finset ((stepBlockFrame R.params.side n).Site 0)}
    (hlm : l ∈ nearbyLumps (stepHotLumps R.params W) (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c₀)) :
    ∃ (x₁ p₁ : TorusSite (n * R.params.side)) (μ ν : Fin 4), μ < ν ∧ x₁ ∈ plaquetteVertices p₁ μ ν ∧
      _root_.YangMills.Construction.TorusFields.supDist c₀ (parentBlock R.params.side x₁) ≤ 2 ∧ R.params.threshold ≤ curvature W p₁ μ ν := by
  classical
  have hs : ∀ i, 0 < (stepBlockFrame R.params.side n).extent i := fun _ => by
    show 0 < n
    omega
  have hodd' : Odd (stepBlockFrame R.params.side n).blockSide := hL
  obtain ⟨p, hpc, hhot, x, hx, hu, hlx⟩ := exists_hot_plaquette_of_mem_nearbyLumps (F := stepBlockFrame R.params.side n)
    R.params.grid hL hodd' hs R.params.threshold _ _ _ l hlm
  obtain ⟨h, hh, hcell⟩ := Finset.mem_image.mp hu
  obtain ⟨x₁, rfl⟩ := torusSiteInFrame_surjective (stepBlockFrame R.params.side n) 0 stepBlockFrame_period_zero x
  obtain ⟨p₀, μ, ν⟩ := p
  obtain ⟨p₁, rfl⟩ := torusSiteInFrame_surjective (stepBlockFrame R.params.side n) 0 stepBlockFrame_period_zero p₀
  have hμν : μ < ν := lt_of_mem_cutPlaquettes hpc
  have hhot' : R.params.threshold ≤ curvature W p₁ μ ν := le_of_le_of_eq hhot (plaquetteDefect_readAtLevel _ p₁ μ ν)
  have hcorner : x₁ ∈ plaquetteVertices p₁ μ ν := by
    have e1 : torusSiteInFrame (stepBlockFrame R.params.side n) 0 p₁ + BlockAverages.unitStep 0 μ =
        torusSiteInFrame (stepBlockFrame R.params.side n) 0 (p₁ + TorusFields.unitStep (n * R.params.side) μ) := by
      rw [torusSiteInFrame_add, torusSiteInFrame_unitStep]
    have e2 : torusSiteInFrame (stepBlockFrame R.params.side n) 0 p₁ + BlockAverages.unitStep 0 ν =
        torusSiteInFrame (stepBlockFrame R.params.side n) 0 (p₁ + TorusFields.unitStep (n * R.params.side) ν) := by
      rw [torusSiteInFrame_add, torusSiteInFrame_unitStep]
    have e3 : torusSiteInFrame (stepBlockFrame R.params.side n) 0 p₁ + BlockAverages.unitStep 0 μ +
        BlockAverages.unitStep 0 ν = torusSiteInFrame (stepBlockFrame R.params.side n) 0
          (p₁ + TorusFields.unitStep (n * R.params.side) μ + TorusFields.unitStep (n * R.params.side) ν) := by
      rw [torusSiteInFrame_add, torusSiteInFrame_add, torusSiteInFrame_unitStep, torusSiteInFrame_unitStep]
    have hi := torusSiteInFrame_injective (m := n * R.params.side) (stepBlockFrame R.params.side n) 0
      stepBlockFrame_period_zero
    simp only [plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false]
    rcases mem_plaquetteCorners hx with h1 | h1 | h1 | h1
    · exact Or.inl (hi h1)
    · exact Or.inr (Or.inl (hi (h1.trans e1)))
    · exact Or.inr (Or.inr (Or.inl (hi (h1.trans e2))))
    · exact Or.inr (Or.inr (Or.inr (hi (h1.trans e3))))
  have hblock : parentBlock R.params.side x₁ = c₀ + siteOfInt h := by
    have h1 := hcell.trans (enclosingCell_torusSiteInFrame x₁)
    apply torusSiteInFrame_injective (stepBlockFrame R.params.side n) 1 stepBlockFrame_period_one
    rw [← torusSiteInFrame_one_add_siteOfInt]
    exact h1.symm
  have hdist : _root_.YangMills.Construction.TorusFields.supDist c₀ (parentBlock R.params.side x₁) ≤ 2 := by
    rw [hblock]
    refine _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le _ _ _ fun i => ?_
    have := Fintype.mem_piFinset.1 hh i
    rw [Finset.mem_Icc] at this
    norm_num at this
    omega
  exact ⟨x₁, p₁, μ, ν, hμν, hcorner, hdist, hhot'⟩
theorem nearbyLumps_eq_empty {H : GasGround R n} {ϑ : GasSupport R n} {σ : SupportState ϑ}
    (hfit : R.params.Admissible) (hn : 2 ≤ n) (hfar : 64 * R.params.side ≤ R.range) (hsup : H.IsGasSupport ϑ)
    (hull : thickening (2 * R.range) (torusHotSites R.params (H.frameField (GasFamily.single ϑ σ))) ⊆
      (H.settingOf (GasFamily.single ϑ σ)).support)
    {c₀ : TorusSite n} (hc : c₀ ∈ ϑ.core) {v : TorusSite (n * R.params.side)} (hv : parentBlock R.params.side v = c₀)
    (hclear : ∀ z ∈ ϑ.2, 5 * R.params.side < _root_.YangMills.Construction.TorusFields.supDist v z) :
    nearbyLumps (stepHotLumps R.params (H.frameField (GasFamily.single ϑ σ)))
      (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c₀) = ∅ := by
  classical
  refine Finset.eq_empty_of_forall_notMem fun l hl => ?_
  obtain ⟨x₁, p₁, μ, ν, hμ, hc₁, hd, hs⟩ := exists_hot_plaquette_near hfit.L_odd hn _ c₀ hl
  have hdv : R.params.side ∣ n * R.params.side := Dvd.intro_left n rfl
  have hlump : torusLumpOf R.params x₁ ∈ torusHotLumps R.params (H.frameField (GasFamily.single ϑ σ)) :=
    (mem_torusHotLumps_iff R.params hfit hdv _ _).mpr ⟨p₁, μ, ν, hμ, hs, x₁, hc₁, rfl⟩
  have hin := hull ((mem_thickening _ _ _).mpr ⟨x₁, mem_torusHotSites.mpr ⟨_, hlump, mem_torusLumpOf_self x₁⟩,
    by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega⟩)
  have h1 := _root_.YangMills.Construction.InBoxTransfer.supDist_le_of_parentBlock_near hv hd
  rcases mem_support_single.1 hin with a | a
  · obtain ⟨z, hz, hzd⟩ := exists_site_near_of_mem_core (hv ▸ hc)
    have ap := hsup.far_from_anchor z hz x₁ (mem_anchorSites_of_mem_recorded a)
    have t := _root_.YangMills.Construction.TorusFields.supDist_triangle z v x₁
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm z v, _root_.YangMills.Construction.TorusFields.supDist_comm v x₁] at t
    omega
  · have := hclear x₁ a
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm] at h1
    omega
theorem isBaseChoice_update_iff {F : BlockFrame} [inst : DecidableEq F.Cell] {J₀ : ℕ}
    {H : Finset (Finset (F.Site F.depth))} {b : F.Cell → F.Site F.depth} (hb : IsBaseChoice J₀ H b) (c : F.Cell)
    (x : F.Site F.depth) : IsBaseChoice J₀ H (Function.update b c x) ↔ x ∈ baseSitesAt J₀ H c := by
  rw [isBaseChoice_iff]
  constructor
  · intro h
    have := h c
    rwa [Function.update_self] at this
  · intro hx c'
    by_cases e : c' = c
    · subst e
      rwa [Function.update_self]
    · rw [Function.update_of_ne e]
      exact isBaseChoice_iff.1 hb c'
open Classical in
theorem update_mem_baseChoices_iff {W : TorusField (n * R.params.side)} {b : BaseChoice R.params.side n}
    (hb : IsBaseChoice R.params.baseDepth (stepHotLumps R.params W) b) (c : (stepBlockFrame R.params.side n).Cell)
    (x : (stepBlockFrame R.params.side n).Site 0) :
    Function.update b c x ∈ baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W) ↔
      x ∈ baseSitesAt R.params.baseDepth (stepHotLumps R.params W) c := by
  unfold baseChoices
  exact ⟨fun h => (isBaseChoice_update_iff (F := stepBlockFrame R.params.side n) hb c x).1 (Finset.mem_filter.1 h).2,
    fun h => Finset.mem_filter.2 ⟨Finset.mem_univ _, (isBaseChoice_update_iff (F := stepBlockFrame R.params.side n) hb c x).2 h⟩⟩
theorem frameBlockSite_eq_siteAtOffset (Y : TorusSite n) (h : Fin 4 → ℤ) (o : BlockOffset R.params.side) :
    frameBlockSite R.params.side n (Y + siteOfInt h) o =
      siteAtOffset (F := stepBlockFrame R.params.side n)
        (torusSiteInFrame (stepBlockFrame R.params.side n) 1 (Y + siteOfInt h)) (refinedOffset R.params.side 0 o) := by
  apply toTorusSite_injective
  have e₁ := toTorusSite_siteAtOffset (L := R.params.side) Y h (refinedOffset R.params.side 0 o)
  have e₂ := TopLevelSites.toTorusSite_torusSiteInFrame (F := stepBlockFrame R.params.side n) (j := 0)
    (fun i => stepBlockFrame_period_zero i) (blockSite (Y + siteOfInt h) o)
  refine Eq.trans e₂ (Eq.trans ?_ e₁.symm)
  rw [blockSite_add_eq, fineSite_eq_blockCentre_add]
  congr 2
  funext i
  simp [refinedOffset]
end NearbyLumps
section Last
variable {n' : ℕ} [NeZero n'] {G : GasGround R n} {G' : GasGround R n'} {Y : TorusSite n} {Y' : TorusSite n'}
  {N m : ℕ} {θ : GasSupport R n} {θ' : GasSupport R n'} {s : SupportState θ} {s' : SupportState θ'}
namespace TransferData
variable (P : TransferData G G' Y Y' N m θ θ' s s')
include P
theorem sixteen_le : 16 ≤ n := by
  have := P.groundsAgree.lt_extent
  have := P.deep
  have := P.frameReach_pos
  omega
theorem sixteen_le' : 16 ≤ n' := by
  have := P.groundsAgree.lt_extent'
  have := P.deep
  have := P.frameReach_pos
  omega
theorem sameNearbyLumps (hA : G.IsAllowed θ s) {h : Fin 4 → ℤ} (hh : OffsetInBox m h) (hc : Y + siteOfInt h ∈ θ.core) :
    SameNearbyLumps (stepHotLumps R.params (G.frameField (GasFamily.single θ s)))
      (stepHotLumps R.params (G'.frameField (GasFamily.single θ' s')))
      (torusSiteInFrame (stepBlockFrame R.params.side n) 1 (Y + siteOfInt h))
      (torusSiteInFrame (stepBlockFrame R.params.side n') 1 (Y' + siteOfInt h)) := by
  classical
  have hfar := P.side_le_range
  have hbig := P.range_ge
  have hodd := P.side_odd
  have hst := refinedRadius_succ R.params.side m
  have hw := P.refinedRadius_add_le
  have hmono : refinedRadius R.params.side m ≤ refinedRadius R.params.side N := by omega
  have h0 : (0 : Fin 4 → ℤ) ∈ centredCube R.params.side := by
    refine (mem_centredCube_iff' _ _).2 fun i => ?_
    have : (0 : ℤ) ≤ ((R.params.side : ℤ) - 1) / 2 := by
      have := P.admissible.L_ge
      omega
    simpa using this
  have hNh : OffsetInBox N h := offsetInBox_mono (by have := P.add_two_le; omega) hh
  set v := fineSite R.params.side Y h 0 with hv
  set v' := fineSite R.params.side Y' h 0 with hv'
  have bv : parentBlock R.params.side v = Y + siteOfInt h := parentBlock_fineSite hodd Y h 0 h0
  have bv' : parentBlock R.params.side v' = Y' + siteOfInt h := parentBlock_fineSite hodd Y' h 0 h0
  have haM : OffsetInBox (refinedRadius R.params.side N) (fun i => (R.params.side : ℤ) * h i + (0 : Fin 4 → ℤ) i) := by
    have h1 := offsetInBox_refinedOffset hodd hNh
      (fun _ => ⟨(R.params.side - 1) / 2, by have := P.admissible.L_ge; omega⟩)
    intro i
    have h2 := (show OffsetInBox (refinedRadius R.params.side N) (refinedOffset R.params.side h
      fun _ => ⟨(R.params.side - 1) / 2, by have := P.admissible.L_ge; omega⟩) from h1) i
    have h3 : refinedOffset R.params.side h (fun _ => ⟨(R.params.side - 1) / 2, by have := P.admissible.L_ge; omega⟩) i =
        (R.params.side : ℤ) * h i + (0 : Fin 4 → ℤ) i := by
      simp only [refinedOffset, Pi.zero_apply]
      have := natCast_half hodd
      push_cast at this ⊢
      omega
    rwa [h3] at h2
  have ev : v = blockCentre R.params.side Y + siteOfInt (fun i => (R.params.side : ℤ) * h i + (0 : Fin 4 → ℤ) i) :=
    fineSite_eq_blockCentre_add Y h 0
  have ev' : v' = blockCentre R.params.side Y' + siteOfInt (fun i => (R.params.side : ℤ) * h i + (0 : Fin 4 → ℤ) i) :=
    fineSite_eq_blockCentre_add Y' h 0
  set a₀ : Fin 4 → ℤ := fun i => (R.params.side : ℤ) * h i + (0 : Fin 4 → ℤ) i with ha₀
  by_cases hnear : ∃ z ∈ θ.2, _root_.YangMills.Construction.TorusFields.supDist v z ≤ 5 * R.params.side
  · obtain ⟨z, hz, hzd⟩ := hnear
    obtain ⟨c, hc₀, rfl⟩ := P.exists_offset_of_core (GasSupport.parentBlock_mem_core_of_mem_sites hz)
    have hcM : OffsetInBox (refinedRadius R.params.side N) c := offsetInBox_mono hmono hc₀
    have hball := P.ballInBox_of_mem_sites (mem_sites_of_mem_snd θ hz) hcM
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm] at hzd
    obtain ⟨e, he, hb⟩ := exists_offset_of_supDist (blockCentre R.params.side Y + siteOfInt c) v
    have hen : ∀ l, |e l| ≤ ((5 * R.params.side : ℕ) : ℤ) := fun l =>
      abs_le_natCast_of_natAbs_le ((hb l).trans hzd)
    have hce : OffsetInBox (refinedRadius R.params.side N) (c + e) := offsetInBox_mono hmono (hball e fun l =>
      (hen l).trans (by exact_mod_cast (by omega : 5 * R.params.side ≤ 4 * R.range)))
    have e1 : a₀ = c + e := eq_of_add_siteOfInt_eq P.refinedRadius_lt haM hce (by rw [← ev, he, add_siteOfInt_add])
    have F : FieldsAgreeNear (G.frameField (GasFamily.single θ s)) (G'.frameField (GasFamily.single θ' s'))
        (cellCentreOnTorus R.params.side (torusSiteInFrame (stepBlockFrame R.params.side n) 1 (Y + siteOfInt h)))
        (cellCentreOnTorus R.params.side (torusSiteInFrame (stepBlockFrame R.params.side n') 1 (Y' + siteOfInt h)))
        (3 * R.params.side) := by
      rw [cellCentreOnTorus_eq, cellCentreOnTorus_eq]
      intro b hb₁
      have hbox : OffsetInBox (refinedRadius R.params.side (m + 1)) (a₀ + b.1) := by
        have hb₂ : ∀ l, |(e + b.1) l| ≤ ((4 * R.range : ℕ) : ℤ) := by
          intro l
          have h1 := abs_add_le_of_box (A := ((5 * R.params.side : ℕ) : ℤ)) (B := ((3 * R.params.side : ℕ) : ℤ))
            hen hb₁.1 l
          have h2 : ((5 * R.params.side : ℕ) : ℤ) + ((3 * R.params.side : ℕ) : ℤ) ≤ ((4 * R.range : ℕ) : ℤ) := by
            exact_mod_cast (by omega : 5 * R.params.side + 3 * R.params.side ≤ 4 * R.range)
          linarith
        have := hball (e + b.1) hb₂
        rw [e1, add_assoc]
        exact offsetInBox_mono (by omega) this
      have e2 : ∀ (k : ℕ) [NeZero k] (Z : TorusSite k),
          (blockCentre R.params.side Z + siteOfInt a₀ : TorusSite (k * R.params.side)) + siteOfInt b.1 =
            blockCentre R.params.side Z + siteOfInt (a₀ + b.1) := fun k _ Z => (add_siteOfInt_add _ _ _).symm
      show G.frameField (GasFamily.single θ s) (v + siteOfInt b.1) b.2 =
        G'.frameField (GasFamily.single θ' s') (v' + siteOfInt b.1) b.2
      rw [ev, ev', e2, e2]
      exact P.frameField_eq_offset hbox b.2
    exact (P.kernelLocal R.params P.admissible P.admissible.depth_lt n n' P.sixteen_le P.sixteen_le' _ _ _ _).2.1 F
  · have hcl : ∀ z ∈ θ.2, 5 * R.params.side < _root_.YangMills.Construction.TorusFields.supDist v z := fun z hz => by
      by_contra hc₂
      exact hnear ⟨z, hz, by omega⟩
    have hcl' : ∀ z ∈ θ'.2, 5 * R.params.side < _root_.YangMills.Construction.TorusFields.supDist v' z := by
      intro z hz
      by_contra hc₂
      obtain ⟨b, hb, rfl⟩ := P.congruent_snd.2.1 z hz
      have hdeep := P.ballsInBox_snd.of_congruent P.congruent_snd
      have hball : BallInBox (refinedRadius R.params.side N) (5 * R.params.side) b :=
        ballInBox_mono (hdeep b hb hz) (by omega)
      have hle : _root_.YangMills.Construction.TorusFields.supDist (blockCentre R.params.side Y' + siteOfInt b : TorusSite (n' * R.params.side))
          (blockCentre R.params.side Y' + siteOfInt a₀) ≤ 5 * R.params.side := by
        rw [← ev', _root_.YangMills.Construction.TorusFields.supDist_comm]
        omega
      have := _root_.YangMills.Construction.CongruentBoxes.supDist_le_transfer (y' := blockCentre R.params.side Y) P.refinedRadius_lt' hball haM hle
      have h2 := hcl _ ((P.snd_iff hb).2 hz)
      rw [ev, _root_.YangMills.Construction.TorusFields.supDist_comm] at h2
      omega
    have e1 := nearbyLumps_eq_empty P.admissible P.two_le hfar P.isSupport hA.1.1 hc bv hcl
    have e2 := nearbyLumps_eq_empty P.admissible P.two_le' hfar P.isSupport' (P.thickening_subset_support hA)
      ((P.core_iff h hNh).1 hc) bv' hcl'
    exact ⟨∅, by simp, by rw [e1]; simp, by rw [e2]; simp⟩
theorem nearbyLumps_eq_ground (hA : G.IsAllowed θ s) {c₀ : TorusSite n'} (hy : c₀ ∉ θ'.core) :
    nearbyLumps (stepHotLumps R.params (G'.frameField (GasFamily.single θ' s')))
        (torusSiteInFrame (stepBlockFrame R.params.side n') 1 c₀) =
      nearbyLumps (stepHotLumps R.params (G'.frameField GasFamily.empty))
        (torusSiteInFrame (stepBlockFrame R.params.side n') 1 c₀) := by
  classical
  have hfar := P.side_le_range
  have hbig := P.range_ge
  obtain ⟨v, hv⟩ : ∃ v : TorusSite (n' * R.params.side), parentBlock R.params.side v = c₀ :=
    ⟨blockSite c₀ (fun _ => 0), parentBlock_blockSite _ _⟩
  apply Finset.Subset.antisymm
  · apply nearbyLumps_subset P.side_odd P.two_le'
    intro x₁ p₁ μ ν hμ hc hd hs
    by_cases hex : ∃ u, _root_.YangMills.Construction.TorusFields.supDist p₁ u ≤ 2 ∧ parentBlock R.params.side u ∈ θ'.core
    · exfalso
      obtain ⟨u, hu, hcore⟩ := hex
      have hl : torusLumpOf R.params x₁ ∈ torusHotLumps R.params (G'.frameField (GasFamily.single θ' s')) :=
        (mem_torusHotLumps_iff R.params P.admissible P.side_dvd' _ _).mpr ⟨p₁, μ, ν, hμ, hs, x₁, hc, rfl⟩
      have h2 := _root_.YangMills.Construction.InBoxTransfer.supDist_le_two_of_mem_plaquetteVertices hc
      have hin := P.thickening_subset_support hA ((mem_thickening _ _ _).mpr
        ⟨x₁, mem_torusHotSites.mpr ⟨_, hl, mem_torusLumpOf_self x₁⟩, by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega⟩)
      rcases mem_support_single.1 hin with a | a
      · obtain ⟨z, hz, hzd⟩ := exists_site_near_of_mem_core hcore
        have ap := P.isSupport'.far_from_anchor z hz x₁ (mem_anchorSites_of_mem_recorded a)
        have t1 := _root_.YangMills.Construction.TorusFields.supDist_triangle z u x₁
        have t2 := _root_.YangMills.Construction.TorusFields.supDist_triangle u p₁ x₁
        rw [_root_.YangMills.Construction.TorusFields.supDist_comm z u] at t1
        rw [_root_.YangMills.Construction.TorusFields.supDist_comm u p₁] at t2
        omega
      · have h1 := _root_.YangMills.Construction.InBoxTransfer.supDist_le_of_parentBlock_near hv hd
        refine hy ?_
        rw [← hv]
        rw [_root_.YangMills.Construction.TorusFields.supDist_comm] at h1
        exact parentBlock_mem_core θ' (mem_sites_of_mem_snd θ' a) (by omega)
    · rw [← curvature_eq_of_agreeNear P.side_odd P.two_le' (agreeNear_single_empty_of_clear s' hex)]
      exact hs
  · apply nearbyLumps_subset P.side_odd P.two_le'
    intro x₁ p₁ μ ν hμ hc hd hs
    have hl : torusLumpOf R.params x₁ ∈ torusHotLumps R.params (G'.frameField GasFamily.empty) :=
      (mem_torusHotLumps_iff R.params P.admissible P.side_dvd' _ _).mpr ⟨p₁, μ, ν, hμ, hs, x₁, hc, rfl⟩
    have hst : x₁ ∈ G'.recordedSites := P.isHull_ground'.1 ((mem_thickening _ _ _).mpr
      ⟨x₁, mem_torusHotSites.mpr ⟨_, hl, mem_torusLumpOf_self x₁⟩, by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega⟩)
    have h2 := _root_.YangMills.Construction.InBoxTransfer.supDist_le_two_of_mem_plaquetteVertices hc
    have ag := agreeNear_single_empty_of_far (x := p₁) (d := 2) P.isSupport' s' (mem_anchorSites_of_mem_recorded hst)
      (by omega)
    rw [curvature_eq_of_agreeNear P.side_odd P.two_le' ag]
    exact hs
theorem isBaseChoice_source (hA : G.IsAllowed θ s) {c : TorusSite n} (hc : c ∈ θ.core) :
    IsBaseChoice R.params.baseDepth (stepHotLumps R.params (G.frameField (GasFamily.single θ s)))
      (G.settingOf (GasFamily.single θ s)).bases :=
  isBaseChoice_of_baseUniformWeight_ne_zero (hA.2.2.2 c hc)
theorem isBaseChoice_target (hA : G.IsAllowed θ s) (hne : θ.core.Nonempty) :
    IsBaseChoice R.params.baseDepth (stepHotLumps R.params (G'.frameField (GasFamily.single θ' s')))
      (G'.settingOf (GasFamily.single θ' s')).bases := by
  classical
  refine (isBaseChoice_iff (F := stepBlockFrame R.params.side n')).2 fun c => ?_
  obtain ⟨c₀, rfl⟩ := torusSiteInFrame_surjective (stepBlockFrame R.params.side n') 1 stepBlockFrame_period_one c
  by_cases hc : c₀ ∈ θ'.core
  · obtain ⟨h, hh, rfl⟩ := P.core_mem_box' c₀ hc
    have hN : OffsetInBox N h := offsetInBox_mono (by have := P.add_two_le; omega) hh
    have hc₁ := (P.core_iff h hN).2 hc
    have hsrc := isBaseChoice_iff.1 (P.isBaseChoice_source hA hc₁)
      (torusSiteInFrame (stepBlockFrame R.params.side n) 1 (Y + siteOfInt h))
    obtain ⟨o, ho, e, e'⟩ := P.settingsAgree.bases_match h hN
    have b0 : (G.settingOf (GasFamily.single θ s)).bases
          (torusSiteInFrame (stepBlockFrame R.params.side n) 1 (Y + siteOfInt h)) =
        siteAtOffset (torusSiteInFrame (stepBlockFrame R.params.side n) 1 (Y + siteOfInt h)) o :=
      toTorusSite_injective (e.trans (toTorusSite_siteAtOffset Y h o).symm)
    have b0' : (G'.settingOf (GasFamily.single θ' s')).bases
          (torusSiteInFrame (stepBlockFrame R.params.side n') 1 (Y' + siteOfInt h)) =
        siteAtOffset (torusSiteInFrame (stepBlockFrame R.params.side n') 1 (Y' + siteOfInt h)) o :=
      toTorusSite_injective (e'.trans (toTorusSite_siteAtOffset Y' h o).symm)
    have S := P.sameNearbyLumps hA hh hc₁
    have K := (P.kernelLocal R.params P.admissible P.admissible.depth_lt n n' P.sixteen_le P.sixteen_le'
      (G.frameField (GasFamily.single θ s)) (G'.frameField (GasFamily.single θ' s')) _ _).2.2.1 S
    rw [b0] at hsrc
    rw [b0']
    exact (K.2 o ho).1 hsrc
  · have e1 : (G'.settingOf (GasFamily.single θ' s')).bases (torusSiteInFrame (stepBlockFrame R.params.side n') 1 c₀) =
        (G'.settingOf GasFamily.empty).bases (torusSiteInFrame (stepBlockFrame R.params.side n') 1 c₀) := by
      refine bases_congr fun θ₁ hθ₁ => ?_
      show GasFamily.single θ' s' θ₁ = Sum.inl ()
      by_cases e : θ₁ = θ'
      · subst e
        exact absurd hθ₁ hc
      · exact single_apply_of_ne s' e
    have h0 := P.ground_weight'.baseLaw_ne_zero
    rw [field_zero_eq_frameField P.side_odd P.two_le'] at h0
    have hb := isBaseChoice_of_baseLaw_ne_zero h0
    rw [e1, baseSitesAt_congr (P.nearbyLumps_eq_ground hA hc)]
    exact isBaseChoice_iff.1 hb _
theorem baseUniformWeight_eq (hA : G.IsAllowed θ s) {h : Fin 4 → ℤ} (hh : OffsetInBox m h)
    (hc : Y + siteOfInt h ∈ θ.core) :
    baseUniformWeight (G.frameField (GasFamily.single θ s)) (G.settingOf (GasFamily.single θ s)).bases (Y + siteOfInt h) =
      baseUniformWeight (G'.frameField (GasFamily.single θ' s')) (G'.settingOf (GasFamily.single θ' s')).bases
        (Y' + siteOfInt h) := by
  classical
  have hB := P.isBaseChoice_source hA hc
  have hB' := P.isBaseChoice_target hA ⟨_, hc⟩
  have m₁ : (G.settingOf (GasFamily.single θ s)).bases ∈
      baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 (G.frameField (GasFamily.single θ s))) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hB⟩
  have m₂ : (G'.settingOf (GasFamily.single θ' s')).bases ∈
      baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n') 0 (G'.frameField (GasFamily.single θ' s'))) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hB'⟩
  have S := P.sameNearbyLumps hA hh hc
  have K := (P.kernelLocal R.params P.admissible P.admissible.depth_lt n n' P.sixteen_le P.sixteen_le'
    (G.frameField (GasFamily.single θ s)) (G'.frameField (GasFamily.single θ' s')) _ _).2.2.1 S
  unfold baseUniformWeight
  rw [if_pos m₁, if_pos m₂]
  congr 2
  apply congrArg Finset.card
  ext o
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [frameBlockSite_eq_siteAtOffset Y h o, frameBlockSite_eq_siteAtOffset Y' h o]
  exact (update_mem_baseChoices_iff hB _ _).trans
    ((K.2 _ (refinedOffset_mem_centredCube P.side_odd o)).trans (update_mem_baseChoices_iff hB' _ _).symm)
theorem isAllowed (hA : G.IsAllowed θ s) : G'.IsAllowed θ' s' := by
  refine ⟨⟨P.thickening_subset_support hA, P.exists_hot_meets hA⟩, P.clusterFactor_ne_zero hA, P.bondMark_ne_zero hA,
    fun y hy => ?_⟩
  obtain ⟨h, hh, rfl⟩ := P.core_mem_box' y hy
  have hc₁ := (P.core_iff h (offsetInBox_mono (by have := P.add_two_le; omega) hh)).2 hy
  rw [← P.baseUniformWeight_eq hA hh hc₁]
  exact hA.2.2.2 _ hc₁
theorem activity_eq (hA : G.IsAllowed θ s) : G.activity θ s = G'.activity θ' s' := by
  classical
  unfold GasGround.activity
  rw [P.supportMarks_eq]
  congr 1
  · congr 1
    have hr : R.range ≤ 4 * R.range := by omega
    have hd := P.ballsInBox_snd.mono (Finset.Subset.refl _) hr
    refine prod_eq_prod_of_rel (fun K K' => CongruentInBoxes K K' (blockCentre R.params.side Y)
      (blockCentre R.params.side Y') (refinedRadius R.params.side N)) _ _
      (fun K hK => exists_congruent_component P.refinedRadius_lt P.refinedRadius_lt' P.congruent_snd hd hK)
      (fun K hK => exists_congruent_component_symm P.refinedRadius_lt P.refinedRadius_lt' P.congruent_snd hd hK)
      (fun _ _ _ _ _ _ r r' => eq_of_congruentInBoxes_of_congruentInBoxes r r')
      (fun _ _ _ _ _ _ r r' => eq_of_congruentInBoxes_of_congruentInBoxes (congruentInBoxes_symm r)
        (congruentInBoxes_symm r'))
      (fun K hK K' hK' r => P.clusterFactor_eq r (subset_of_mem_chainComponents hK) (subset_of_mem_chainComponents hK'))
  · refine prod_eq_prod_of_rel (fun c c' => ∃ h, OffsetInBox m h ∧ c = Y + siteOfInt h ∧ c' = Y' + siteOfInt h) _ _
      ?_ ?_ ?_ ?_ ?_
    · intro c hc
      obtain ⟨h, hh, rfl⟩ := P.core_mem_box c hc
      exact ⟨_, (P.core_iff h (offsetInBox_mono (by have := P.add_two_le; omega) hh)).1 hc, h, hh, rfl, rfl⟩
    · intro c hc
      obtain ⟨h, hh, rfl⟩ := P.core_mem_box' c hc
      exact ⟨_, (P.core_iff h (offsetInBox_mono (by have := P.add_two_le; omega) hh)).2 hc, h, hh, rfl, rfl⟩
    · rintro _ _ _ _ _ _ ⟨h, hh, rfl, rfl⟩ ⟨h', hh', e, rfl⟩
      have hm : 2 * m + 2 < n := by
        have := P.groundsAgree.lt_extent
        have := P.add_two_le
        omega
      rw [eq_of_add_siteOfInt_eq hm hh hh' e]
    · rintro _ _ _ _ _ _ ⟨h, hh, rfl, rfl⟩ ⟨h', hh', rfl, e⟩
      have hm : 2 * m + 2 < n' := by
        have := P.groundsAgree.lt_extent'
        have := P.add_two_le
        omega
      rw [eq_of_add_siteOfInt_eq hm hh hh' e]
    · rintro _ ha _ _ ⟨h, hh, rfl, rfl⟩
      exact P.baseUniformWeight_eq hA hh ha
end TransferData
end Last
end InBoxTransfer
open InBoxTransfer in
theorem ClusterExpansionOfAStep.allowedStatesTransferInBox_holds (hGW : GroundWeightAtEmpty)
    (hFr : FrameLocality.FrameCoordLocal) (hK : BondKernelLocality) (hFl : StepFloors.EventuallyFloorConditions) :
    ClusterExpansionOfAStep.AllowedStatesTransferInBox := by
  classical
  intro T hT
  obtain ⟨y₁, h₁⟩ := hGW T hT
  obtain ⟨y₂, h₂⟩ := hFl T hT (2 ^ 20 * ((T.side : ℝ) + 1)) 1 (by positivity) one_pos
  refine ⟨max y₁ (max y₂ T.floorMin), fun y hy R hR hx n n' _ _ G G' Y Y' N i i' s s' hG hG' hN hag hc hc' hs hcc hst hA =>
    ?_⟩
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
  have hside : ∀ {k : ℕ} [NeZero k] {H : GasGround R k}, H.IsAdmissibleGround →
      IsBlockTorusSide R.params (k * R.params.side) := by
    intro k _ H hH
    refine ⟨Dvd.intro_left k rfl, ?_⟩
    rcases hH with c | c
    · rw [mul_comm]
      exact Nat.mul_le_mul_right _ c.n₀_le
    · have h1 := c.isBlockSide.2
      have h2 : k ≤ k * R.params.side := Nat.le_mul_of_pos_right k (by omega)
      omega
  have P : TransferData G G' Y Y' N (N - R.frameReach - 1) i.1 i'.1 s s' :=
    { admissible := hfit
      hasExpansions := hR.isStep.1
      groundsAgree := hag
      gap_eq := by omega
      deep := hN
      frameReach_pos := by omega
      range_le := hbig
      side_le_range := by nlinarith
      range_ge := by nlinarith
      isBlockSide := hside hG
      isBlockSide' := hside hG'
      isSupport := i.2
      isSupport' := i'.2
      core_mem_box := hc
      core_mem_box' := hc'
      sameSupport := hs
      core_iff := hcc
      sameState := hst
      ground_weight := h₁ y a₁ R hR hx n G hG
      ground_weight' := h₁ y a₁ R hR hx n' G' hG'
      frameLocal := hFr
      kernelLocal := hK }
  exact ⟨P.isAllowed hA, P.activity_eq hA⟩
end YangMills.Construction
end
