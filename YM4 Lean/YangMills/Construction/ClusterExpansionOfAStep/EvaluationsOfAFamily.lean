import YangMills.Construction.ClusterExpansionOfAStep.AllowedStatesReadTheirBoxProof
import YangMills.Construction.ClusterExpansionOfAStep.ConfigurationsOfTheGasAreSettingsProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction
open BlockAverages LumpContours HoleSavings HoleSites StepCosts TorusLumps TorusFields StepGas
  StepSettings BlockZones BlockPlaces BlockTrees
open BlockSites hiding supDist_comm
open TopLevelSites hiding torusSiteInFrame_add
namespace FamilyRestrictions
variable {R : StepSetup} {n : ℕ} [NeZero n]
section Places
variable {L : ℕ} [NeZero L]
theorem supDist_le_of_parentBlock_eq {x z : TorusSite (n * L)} (h : parentBlock L x = parentBlock L z) :
    _root_.YangMills.Construction.TorusFields.supDist x z ≤ L := by apply _root_.YangMills.Construction.TorusLumps.supDist_le_of_parentBlock_eq <;> assumption
theorem supDist_le_two_of_mem_plaquetteVertices {m : ℕ} [NeZero m] {x z : TorusSite m} {μ ν : Fin 4}
    (hz : z ∈ plaquetteVertices x μ ν) : _root_.YangMills.Construction.TorusFields.supDist x z ≤ 2 := by apply _root_.YangMills.Construction.InBoxTransfer.supDist_le_two_of_mem_plaquetteVertices <;> assumption
theorem plaquetteDefect_readAtLevel (W : TorusField (n * L)) (x : TorusSite (n * L)) (μ ν : Fin 4) :
    plaquetteDefect (readAtLevel (stepBlockFrame L n) 0 W) (torusSiteInFrame (stepBlockFrame L n) 0 x, μ, ν) =
      curvature W x μ ν := by apply _root_.YangMills.Construction.InBoxTransfer.plaquetteDefect_readAtLevel <;> assumption
end Places
section Classes
variable {m : ℕ} [NeZero m] {r : ℕ} {Y Y₁ : Finset (TorusSite m)}
theorem chainConnected_of_separated (hsep : ∀ u ∈ Y₁, ∀ v ∈ Y, v ∉ Y₁ → r < _root_.YangMills.Construction.TorusFields.supDist u v) {z w : TorusSite m}
    (hz : z ∈ Y₁) (h : ChainConnected r Y z w) : w ∈ Y₁ ∧ ChainConnected r Y₁ z w := by apply _root_.YangMills.Construction.InBoxTransfer.chainConnected_of_separated <;> assumption
theorem chainConnected_mono (hsub : Y₁ ⊆ Y) {z w : TorusSite m} (h : ChainConnected r Y₁ z w) :
    ChainConnected r Y z w := by apply _root_.YangMills.Construction.InBoxTransfer.chainConnected_mono <;> assumption
open Classical in
theorem mem_chainComponents_of_separated (hsub : Y₁ ⊆ Y)
    (hsep : ∀ u ∈ Y₁, ∀ v ∈ Y, v ∉ Y₁ → r < _root_.YangMills.Construction.TorusFields.supDist u v)
    {X : Finset (TorusSite m)} (hX : X ∈ chainComponents r Y) {z : TorusSite m} (hz : z ∈ X) (hz₁ : z ∈ Y₁) :
    X ∈ chainComponents r Y₁ ∧ X ⊆ Y₁ := by apply _root_.YangMills.Construction.InBoxTransfer.mem_chainComponents_of_separated <;> assumption
open Classical in
theorem exists_mem_of_mem_chainComponents {X : Finset (TorusSite m)} (hX : X ∈ chainComponents r Y) :
    ∃ z, z ∈ X := by apply _root_.YangMills.Construction.InBoxTransfer.exists_mem_of_mem_chainComponents <;> assumption
end Classes
section Data
theorem withNone_eq_inr {α : Type} (a : WithNone α) (h : a.isRight = true) : a = Sum.inr (a.getRight h) := by apply _root_.YangMills.Construction.InBoxTransfer.eq_inr_getRight <;> assumption
theorem withNone_eq_inl {α : Type} (a : WithNone α) (h : ¬ a.isRight = true) : a = Sum.inl () := by
  cases a with
  | inl u => rfl
  | inr s => simp at h
variable {γ γ' : GasFamily R n} {θ θ' : GasSupport R n}
theorem apply_eq_inr_of_occupies (h : γ.Occupies θ) : γ θ = Sum.inr (γ.state h) := withNone_eq_inr _ h
theorem apply_eq_inl_of_not_occupies (h : ¬ γ.Occupies θ) : γ θ = Sum.inl () := withNone_eq_inl _ h
theorem single_apply_self (s : SupportState θ) : GasFamily.single θ s θ = Sum.inr s := by apply _root_.YangMills.Construction.InBoxTransfer.single_apply_self <;> assumption
theorem single_apply_of_ne (s : SupportState θ) (h : θ' ≠ θ) : GasFamily.single θ s θ' = Sum.inl () := by apply _root_.YangMills.Construction.InBoxTransfer.single_apply_of_ne <;> assumption
theorem occupies_single_iff (s : SupportState θ) : (GasFamily.single θ s).Occupies θ' ↔ θ' = θ := by apply _root_.YangMills.Construction.InBoxTransfer.occupies_single_iff <;> assumption
theorem mem_sites_iff {z : TorusSite (n * R.params.side)} : z ∈ γ.sites ↔ ∃ θ, γ.Occupies θ ∧ z ∈ θ.2 := by apply _root_.YangMills.Construction.InBoxTransfer.mem_sites_iff <;> assumption
theorem mem_sites_single_iff (s : SupportState θ) {z : TorusSite (n * R.params.side)} :
    z ∈ (GasFamily.single θ s).sites ↔ z ∈ θ.2 := by apply _root_.YangMills.Construction.InBoxTransfer.mem_sites_single <;> assumption
theorem not_mem_sites_empty {z : TorusSite (n * R.params.side)} : z ∉ (GasFamily.empty : GasFamily R n).sites := by apply _root_.YangMills.Construction.InBoxTransfer.not_mem_sites_empty <;> assumption
end Data
section EvaluationMaps
variable {G : GasGround R n} {γ γ₁ : GasFamily R n}
theorem fine_settingOf_eq (hL : Odd R.params.side) (hn : 2 ≤ n) :
    (G.settingOf γ).fine = (G.settingOf γ).field 0 := by apply _root_.YangMills.Construction.InBoxTransfer.fine_eq_field_zero <;> assumption
theorem field_zero_settingOf (hL : Odd R.params.side) (hn : 2 ≤ n) :
    (G.settingOf γ).field 0 = G.frameField γ :=
  (fine_settingOf_eq hL hn).symm
def AgreeNear (γ γ₁ : GasFamily R n) (x : TorusSite (n * R.params.side)) (d : ℕ) : Prop :=
  ∀ θ : GasSupport R n, ∀ u, _root_.YangMills.Construction.TorusFields.supDist x u ≤ d → parentBlock R.params.side u ∈ θ.core → γ θ = γ₁ θ
theorem frameField_congr (hL : Odd R.params.side) (hn : 2 ≤ n) {x : TorusSite (n * R.params.side)} {i : Fin 4}
    (h : ∀ θ : GasSupport R n, parentBlock R.params.side x ∈ θ.core ∨
      parentBlock R.params.side (x + TorusFields.unitStep (n * R.params.side) i) ∈ θ.core → γ θ = γ₁ θ) :
    G.frameField γ x i = G.frameField γ₁ x i := by apply _root_.YangMills.Construction.InBoxTransfer.frameField_congr <;> assumption
theorem frameField_eq_of_agreeNear (hL : Odd R.params.side) (hn : 2 ≤ n) {x : TorusSite (n * R.params.side)}
    {d : ℕ} (h : AgreeNear γ γ₁ x d) {z : TorusSite (n * R.params.side)} (i : Fin 4) (hz : _root_.YangMills.Construction.TorusFields.supDist x z + 1 ≤ d) :
    G.frameField γ z i = G.frameField γ₁ z i := by apply _root_.YangMills.Construction.InBoxTransfer.frameField_eq_of_agreeNear <;> assumption
theorem curvature_eq_of_agreeNear (hL : Odd R.params.side) (hn : 2 ≤ n) {x : TorusSite (n * R.params.side)}
    {μ ν : Fin 4} (h : AgreeNear γ γ₁ x 2) :
    curvature (G.frameField γ) x μ ν = curvature (G.frameField γ₁) x μ ν := by apply _root_.YangMills.Construction.InBoxTransfer.curvature_eq_of_agreeNear <;> assumption
theorem chartCoord_eq_of_agreeNear (hL : Odd R.params.side) (hn : 2 ≤ n) {V : TorusField n}
    {b : TorusBond (n * R.params.side)} (h : AgreeNear γ γ₁ b.1 (R.params.side + 3)) :
    chartCoord R.params V (G.frameField γ) b = chartCoord R.params V (G.frameField γ₁) b := by apply _root_.YangMills.Construction.GasSettings.chartCoord_eq_of_agreeNear <;> assumption
theorem exists_site_near_of_mem_core {θ : GasSupport R n} {u : TorusSite (n * R.params.side)}
    (h : parentBlock R.params.side u ∈ θ.core) :
    ∃ z ∈ θ.sites, _root_.YangMills.Construction.TorusFields.supDist u z ≤ 4 * R.range + R.params.side := by apply _root_.YangMills.Construction.InBoxTransfer.exists_site_near_of_mem_core <;> assumption
theorem parentBlock_mem_core (θ : GasSupport R n) {z x : TorusSite (n * R.params.side)} (hz : z ∈ θ.sites)
    (h : _root_.YangMills.Construction.TorusFields.supDist x z ≤ 4 * R.range) : parentBlock R.params.side x ∈ θ.core :=
  parentBlock_mem_coreBlocks_of_near hz h
theorem mem_anchorSites_of_mem_recordedSites {z : TorusSite (n * R.params.side)} (h : z ∈ G.recordedSites) :
    z ∈ G.anchorSites := by apply _root_.YangMills.Construction.InBoxTransfer.mem_anchorSites_of_mem_recorded <;> assumption
theorem mem_sites_of_mem_snd (θ : GasSupport R n) {z : TorusSite (n * R.params.side)} (hz : z ∈ θ.2) :
    z ∈ θ.sites :=
  Finset.mem_union_right _ hz
end EvaluationMaps
structure IsReadable (G : GasGround R n) (γ : GasFamily R n) : Prop where
  isFamily : G.IsGasFamily γ
  admissible : R.params.Admissible
  hasExpansions : R.HasExpansions
  blockSide : IsBlockTorusSide R.params (n * R.params.side)
  two_le : 2 ≤ n
  far : 64 * R.params.side ≤ R.range
  big : 2 ^ 16 ≤ R.range
  groundWeight : G.HasWeightAt GasFamily.empty 0
  exists_zone : ∃ Z, IsRetainedZone G Z
section Fields
variable {G : GasGround R n} {γ : GasFamily R n} (hF : IsReadable G γ)
include hF
theorem side_odd : Odd R.params.side := hF.admissible.L_odd
theorem agreeNear_single_of_mem_sites {θ : GasSupport R n} (h : γ.Occupies θ) {z x : TorusSite (n * R.params.side)}
    {d : ℕ} (hz : z ∈ θ.sites) (hd : _root_.YangMills.Construction.TorusFields.supDist x z + d + R.params.side ≤ 6 * R.range) :
    AgreeNear γ (GasFamily.single θ (γ.state h)) x d := by
  intro θ' u hu hc
  by_cases e : θ' = θ
  · subst e
    rw [single_apply_self]
    exact apply_eq_inr_of_occupies h
  · rw [single_apply_of_ne _ e]
    apply apply_eq_inl_of_not_occupies
    intro h'
    obtain ⟨z', hz', hd'⟩ := exists_site_near_of_mem_core hc
    have ap := hF.isFamily.2 θ θ' h h' (Ne.symm e) z hz z' hz'
    have t1 := _root_.YangMills.Construction.TorusFields.supDist_triangle z x z'
    have t2 := _root_.YangMills.Construction.TorusFields.supDist_triangle x u z'
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm z x] at t1
    omega
theorem agreeNear_single_of_mem_core {θ : GasSupport R n} (h : γ.Occupies θ) {v x : TorusSite (n * R.params.side)}
    {d : ℕ} (hv : parentBlock R.params.side v ∈ θ.core) (hd : _root_.YangMills.Construction.TorusFields.supDist x v + d + 2 * R.params.side ≤ 2 * R.range) :
    AgreeNear γ (GasFamily.single θ (γ.state h)) x d := by
  obtain ⟨z, hz, hvz⟩ := exists_site_near_of_mem_core hv
  have t := _root_.YangMills.Construction.TorusFields.supDist_triangle x v z
  exact agreeNear_single_of_mem_sites hF h hz (by omega)
theorem agreeNear_empty_of_mem_anchor {v x : TorusSite (n * R.params.side)} {d : ℕ} (hv : v ∈ G.anchorSites)
    (hd : _root_.YangMills.Construction.TorusFields.supDist x v + d + R.params.side ≤ 6 * R.range) : AgreeNear γ GasFamily.empty x d := by
  intro θ' u hu hc
  show γ θ' = Sum.inl ()
  apply apply_eq_inl_of_not_occupies
  intro h'
  obtain ⟨z', hz', hd'⟩ := exists_site_near_of_mem_core hc
  have ap := (hF.isFamily.1 θ' h').far_from_anchor z' hz' v hv
  have t1 := _root_.YangMills.Construction.TorusFields.supDist_triangle z' u v
  have t2 := _root_.YangMills.Construction.TorusFields.supDist_triangle u x v
  rw [_root_.YangMills.Construction.TorusFields.supDist_comm z' u] at t1
  rw [_root_.YangMills.Construction.TorusFields.supDist_comm u x] at t2
  omega
omit hF in
theorem agreeNear_empty_of_forall {x : TorusSite (n * R.params.side)} {d : ℕ}
    (h : ∀ θ : GasSupport R n, γ.Occupies θ → ∀ u, _root_.YangMills.Construction.TorusFields.supDist x u ≤ d → parentBlock R.params.side u ∉ θ.core) :
    AgreeNear γ GasFamily.empty x d := by apply _root_.YangMills.Construction.GasSettings.agreeNear_empty_of_forall <;> assumption
theorem side_dvd : R.params.side ∣ n * R.params.side := Dvd.intro_left n rfl
theorem isHullState_empty :
    IsHullState R.params R.range (G.frameField GasFamily.empty) (G.settingOf GasFamily.empty).support := by
  have h := hF.groundWeight.isHull
  rwa [field_zero_settingOf (side_odd hF) hF.two_le] at h
theorem mem_recordedSites_of_hot_empty {z : TorusSite (n * R.params.side)}
    (hz : z ∈ torusHotSites R.params (G.frameField GasFamily.empty)) : z ∈ G.recordedSites := by
  have h := (isHullState_empty hF).1 ((mem_thickening _ _ _).mpr ⟨z, hz, by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega⟩)
  rcases Finset.mem_union.mp h with a | a
  · exact a
  · exact absurd a not_mem_sites_empty
theorem mem_of_hot_single {θ : GasSupport R n} (h : γ.Occupies θ)
    (hh : IsHullState R.params R.range (G.frameField (GasFamily.single θ (γ.state h)))
      (G.settingOf (GasFamily.single θ (γ.state h))).support)
    {z : TorusSite (n * R.params.side)}
    (hz : z ∈ torusHotSites R.params (G.frameField (GasFamily.single θ (γ.state h)))) :
    z ∈ G.recordedSites ∨ z ∈ θ.2 := by
  have h' := hh.1 ((mem_thickening _ _ _).mpr ⟨z, hz, by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega⟩)
  rcases Finset.mem_union.mp h' with a | a
  · exact Or.inl a
  · exact Or.inr ((mem_sites_single_iff _).mp a)
theorem mem_torusHotLumps_of_empty {l : Finset (TorusSite (n * R.params.side))}
    (hl : l ∈ torusHotLumps R.params (G.frameField GasFamily.empty)) :
    l ∈ torusHotLumps R.params (G.frameField γ) := by
  classical
  have hfar := hF.far
  have hbig := hF.big
  obtain ⟨x, μ, ν, hμ, hs, z, hz, hlz⟩ := (mem_torusHotLumps_iff R.params hF.admissible (side_dvd hF) _ _).mp hl
  have hzl : z ∈ l := by
    rw [hlz]
    exact mem_torusLumpOf_self z
  have hst := mem_recordedSites_of_hot_empty hF (mem_torusHotSites_iff.mpr ⟨l, hl, hzl⟩)
  have hd := _root_.YangMills.Construction.FamilyRestrictions.supDist_le_two_of_mem_plaquetteVertices hz
  have ag := agreeNear_empty_of_mem_anchor hF (x := x) (d := 2) (mem_anchorSites_of_mem_recordedSites hst)
    (by omega)
  refine (mem_torusHotLumps_iff R.params hF.admissible (side_dvd hF) _ _).mpr ⟨x, μ, ν, hμ, ?_, z, hz, hlz⟩
  rw [curvature_eq_of_agreeNear (side_odd hF) hF.two_le ag]
  exact hs
theorem range_lt_supDist_recorded {θ : GasSupport R n} (h : γ.Occupies θ) {u v : TorusSite (n * R.params.side)}
    (hu : u ∈ θ.2) (hv : v ∈ G.recordedSites) : R.range < _root_.YangMills.Construction.TorusFields.supDist u v := by
  have := (hF.isFamily.1 θ h).far_from_anchor u (mem_sites_of_mem_snd θ hu) v
    (mem_anchorSites_of_mem_recordedSites hv)
  omega
theorem range_lt_supDist_of_ne {θ θ' : GasSupport R n} (h : γ.Occupies θ) (h' : γ.Occupies θ') (e : θ ≠ θ')
    {u v : TorusSite (n * R.params.side)} (hu : u ∈ θ.2) (hv : v ∈ θ'.2) : R.range < _root_.YangMills.Construction.TorusFields.supDist u v := by
  have := hF.isFamily.2 θ θ' h h' e u (mem_sites_of_mem_snd θ hu) v (mem_sites_of_mem_snd θ' hv)
  omega
omit hF in
theorem support_settingOf_empty : (G.settingOf GasFamily.empty).support = G.recordedSites := by apply _root_.YangMills.Construction.GasSettings.support_settingOf_empty <;> assumption
theorem mem_chainComponents_recorded {X : Finset (TorusSite (n * R.params.side))}
    (hX : X ∈ chainComponents R.range (G.settingOf γ).support)
    {z : TorusSite (n * R.params.side)} (hz : z ∈ X) (hzs : z ∈ G.recordedSites) :
    X ∈ chainComponents R.range (G.settingOf GasFamily.empty).support ∧ X ⊆ G.recordedSites := by
  have key := mem_chainComponents_of_separated (Y₁ := G.recordedSites) Finset.subset_union_left
    (fun u hu v hv hn => by
      rcases Finset.mem_union.mp hv with a | a
      · exact absurd a hn
      · obtain ⟨θ, h, hvθ⟩ := mem_sites_iff.mp a
        rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
        exact range_lt_supDist_recorded hF h hvθ hu) hX hz hzs
  exact ⟨by rw [support_settingOf_empty]; exact key.1, key.2⟩
theorem mem_chainComponents_single {θ : GasSupport R n} (h : γ.Occupies θ)
    {X : Finset (TorusSite (n * R.params.side))}
    (hX : X ∈ chainComponents R.range (G.settingOf γ).support) {z : TorusSite (n * R.params.side)} (hz : z ∈ X)
    (hzθ : z ∈ θ.2) :
    X ∈ chainComponents R.range θ.2 ∧ X ⊆ θ.2 ∧
      X ∈ chainComponents R.range (G.settingOf (GasFamily.single θ (γ.state h))).support := by
  have a : (θ.2 : Finset (TorusSite (n * R.params.side))) ⊆ (G.settingOf γ).support := fun w hw =>
    Finset.mem_union_right _ (mem_sites_iff.mpr ⟨θ, h, hw⟩)
  have k1 := mem_chainComponents_of_separated (Y₁ := θ.2) a (fun u hu v hv hn => by
    rcases Finset.mem_union.mp hv with b | b
    · exact range_lt_supDist_recorded hF h hu b
    · obtain ⟨θ', h', hvθ⟩ := mem_sites_iff.mp b
      have e : θ ≠ θ' := fun e => hn (e ▸ hvθ)
      exact range_lt_supDist_of_ne hF h h' e hu hvθ) hX hz hzθ
  have a' : (G.settingOf (GasFamily.single θ (γ.state h))).support ⊆ (G.settingOf γ).support := fun w hw => by
    rcases Finset.mem_union.mp hw with b | b
    · exact Finset.mem_union_left _ b
    · exact a ((mem_sites_single_iff _).mp b)
  have k2 := mem_chainComponents_of_separated (Y₁ := (G.settingOf (GasFamily.single θ (γ.state h))).support) a'
    (fun u hu v hv hn => by
      have hv1 : v ∉ G.recordedSites := fun c => hn (Finset.mem_union_left _ c)
      have hv2 : v ∉ θ.2 := fun c => hn (Finset.mem_union_right _ ((mem_sites_single_iff _).mpr c))
      rcases Finset.mem_union.mp hv with b | b
      · exact absurd b hv1
      · obtain ⟨θ', h', hvθ⟩ := mem_sites_iff.mp b
        have e : θ ≠ θ' := fun e => hv2 (e ▸ hvθ)
        rcases Finset.mem_union.mp hu with c | c
        · rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
          exact range_lt_supDist_recorded hF h' hvθ c
        · exact range_lt_supDist_of_ne hF h h' e ((mem_sites_single_iff _).mp c) hvθ) hX hz
    (Finset.mem_union_right _ ((mem_sites_single_iff _).mpr hzθ))
  exact ⟨k1.1, k1.2, k2.1⟩
omit hF in
theorem labelling_congr {γ₁ : GasFamily R n} {z : TorusSite (n * R.params.side)}
    (h₁ : z ∈ (G.settingOf γ).support) (h₂ : z ∈ (G.settingOf γ₁).support)
    (hs : ∀ θ : GasSupport R n, z ∈ θ.2 → γ θ = γ₁ θ) :
    (G.settingOf γ).labelling ⟨z, h₁⟩ = (G.settingOf γ₁).labelling ⟨z, h₂⟩ := by apply _root_.YangMills.Construction.GasSettings.labelling_congr <;> assumption
omit hF in
theorem isBaseChoice_of_local {F : BlockFrame} {J₀ : ℕ} {H : Finset (Finset (F.Site F.depth))}
    {b : F.Cell → F.Site F.depth}
    (hy : ∀ y, ∃ (H' : Finset (Finset (F.Site F.depth))) (b' : F.Cell → F.Site F.depth),
      IsBaseChoice J₀ H' b' ∧ nearbyLumps H y = nearbyLumps H' y ∧ b y = b' y) : IsBaseChoice J₀ H b := by
  classical
  intro y
  obtain ⟨H', b', hb, e1, e2⟩ := hy y
  have hc : IsCrowded J₀ H y ↔ IsCrowded J₀ H' y := by
    unfold IsCrowded
    rw [e1]
  have hbx : excludedBoxes J₀ H y = excludedBoxes J₀ H' y := by
    unfold excludedBoxes
    by_cases h : IsCrowded J₀ H y
    · rw [if_pos h, if_pos (hc.mp h)]
    · rw [if_neg h, if_neg fun c => h (hc.mpr c), e1]
  obtain ⟨a1, a2⟩ := hb y
  rw [e2, e1, hbx]
  exact ⟨fun c => a1 (c.imp id hc.mp), fun c => a2 fun d => c (d.imp id hc.mpr)⟩
omit hF in
theorem nearbyLumps_mono (hL : Odd R.params.side) (hn : 2 ≤ n) (W W' : TorusField (n * R.params.side))
    (c₀ : TorusSite n)
    (hyp : ∀ (x₁ p₁ : TorusSite (n * R.params.side)) (μ ν : Fin 4), μ < ν → x₁ ∈ plaquetteVertices p₁ μ ν →
      _root_.YangMills.Construction.TorusFields.supDist c₀ (parentBlock R.params.side x₁) ≤ 2 → R.params.threshold ≤ curvature W p₁ μ ν →
        R.params.threshold ≤ curvature W' p₁ μ ν) :
    nearbyLumps (stepHotLumps R.params W) (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c₀) ⊆
      nearbyLumps (stepHotLumps R.params W') (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c₀) := by apply _root_.YangMills.Construction.InBoxTransfer.nearbyLumps_subset <;> assumption
omit hF in
theorem supDist_le_four_mul {L : ℕ} [NeZero L] {x₁ v : TorusSite (n * L)} {c₀ : TorusSite n}
    (hv : parentBlock L v = c₀) (hd : _root_.YangMills.Construction.TorusFields.supDist c₀ (parentBlock L x₁) ≤ 2) : _root_.YangMills.Construction.TorusFields.supDist x₁ v ≤ 4 * L := by apply _root_.YangMills.Construction.InBoxTransfer.supDist_le_of_parentBlock_near <;> assumption
theorem nearbyLumps_eq_single {θ : GasSupport R n} (h : γ.Occupies θ) {c₀ : TorusSite n} (hy : c₀ ∈ θ.core) :
    nearbyLumps (stepHotLumps R.params (G.frameField γ)) (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c₀) =
      nearbyLumps (stepHotLumps R.params (G.frameField (GasFamily.single θ (γ.state h))))
        (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c₀) := by
  classical
  have hfar := hF.far
  have hbig := hF.big
  obtain ⟨v, hv⟩ : ∃ v : TorusSite (n * R.params.side), parentBlock R.params.side v = c₀ :=
    ⟨blockSite c₀ (fun _ => 0), parentBlock_blockSite _ _⟩
  have ag : ∀ (x₁ p₁ : TorusSite (n * R.params.side)) (μ ν : Fin 4), x₁ ∈ plaquetteVertices p₁ μ ν →
      _root_.YangMills.Construction.TorusFields.supDist c₀ (parentBlock R.params.side x₁) ≤ 2 → AgreeNear γ (GasFamily.single θ (γ.state h)) p₁ 2 := by
    intro x₁ p₁ μ ν hc hd
    have h1 := _root_.YangMills.Construction.FamilyRestrictions.supDist_le_four_mul hv hd
    have h2 := supDist_le_two_of_mem_plaquetteVertices hc
    have h3 := _root_.YangMills.Construction.TorusFields.supDist_triangle p₁ x₁ v
    exact agreeNear_single_of_mem_core hF h (v := v) (by rw [hv]; exact hy) (by omega)
  apply Finset.Subset.antisymm
  · apply nearbyLumps_mono (side_odd hF) hF.two_le
    intro x₁ p₁ μ ν _ hc hd hs
    rw [← curvature_eq_of_agreeNear (side_odd hF) hF.two_le (ag x₁ p₁ μ ν hc hd)]
    exact hs
  · apply nearbyLumps_mono (side_odd hF) hF.two_le
    intro x₁ p₁ μ ν _ hc hd hs
    rw [curvature_eq_of_agreeNear (side_odd hF) hF.two_le (ag x₁ p₁ μ ν hc hd)]
    exact hs
theorem nearbyLumps_eq_empty
    (hH : ∀ (θ : GasSupport R n) (h : γ.Occupies θ),
      IsHullState R.params R.range (G.frameField (GasFamily.single θ (γ.state h)))
        (G.settingOf (GasFamily.single θ (γ.state h))).support)
    {c₀ : TorusSite n} (hy : ∀ θ : GasSupport R n, γ.Occupies θ → c₀ ∉ θ.core) :
    nearbyLumps (stepHotLumps R.params (G.frameField γ)) (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c₀) =
      nearbyLumps (stepHotLumps R.params (G.frameField GasFamily.empty))
        (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c₀) := by
  classical
  have hfar := hF.far
  have hbig := hF.big
  obtain ⟨v, hv⟩ : ∃ v : TorusSite (n * R.params.side), parentBlock R.params.side v = c₀ :=
    ⟨blockSite c₀ (fun _ => 0), parentBlock_blockSite _ _⟩
  apply Finset.Subset.antisymm
  · apply nearbyLumps_mono (side_odd hF) hF.two_le
    intro x₁ p₁ μ ν hμ hc hd hs
    by_cases hex : ∃ θ : GasSupport R n, γ.Occupies θ ∧
        ∃ u, _root_.YangMills.Construction.TorusFields.supDist p₁ u ≤ 2 ∧ parentBlock R.params.side u ∈ θ.core
    · exfalso
      obtain ⟨θ, h, u, hu, hcore⟩ := hex
      have ag := agreeNear_single_of_mem_core hF h (x := p₁) (d := 2) hcore (by omega)
      rw [curvature_eq_of_agreeNear (side_odd hF) hF.two_le ag] at hs
      have hl : torusLumpOf R.params x₁ ∈ torusHotLumps R.params (G.frameField (GasFamily.single θ (γ.state h))) :=
        (mem_torusHotLumps_iff R.params hF.admissible (side_dvd hF) _ _).mpr ⟨p₁, μ, ν, hμ, hs, x₁, hc, rfl⟩
      have h2 := _root_.YangMills.Construction.FamilyRestrictions.supDist_le_two_of_mem_plaquetteVertices hc
      rcases mem_of_hot_single hF h (hH θ h) (mem_torusHotSites_iff.mpr ⟨_, hl, mem_torusLumpOf_self x₁⟩) with a | a
      · obtain ⟨z, hz, hzd⟩ := exists_site_near_of_mem_core hcore
        have ap := (hF.isFamily.1 θ h).far_from_anchor z hz x₁ (mem_anchorSites_of_mem_recordedSites a)
        have t1 := _root_.YangMills.Construction.TorusFields.supDist_triangle z u x₁
        have t2 := _root_.YangMills.Construction.TorusFields.supDist_triangle u p₁ x₁
        rw [_root_.YangMills.Construction.TorusFields.supDist_comm z u] at t1
        rw [_root_.YangMills.Construction.TorusFields.supDist_comm u p₁] at t2
        omega
      · have h1 := _root_.YangMills.Construction.FamilyRestrictions.supDist_le_four_mul hv hd
        refine hy θ h ?_
        rw [← hv]
        rw [_root_.YangMills.Construction.TorusFields.supDist_comm] at h1
        exact parentBlock_mem_core θ (mem_sites_of_mem_snd θ a) (by omega)
    · rw [← curvature_eq_of_agreeNear (side_odd hF) hF.two_le
        (agreeNear_empty_of_forall fun θ h u hu hcore => hex ⟨θ, h, u, hu, hcore⟩)]
      exact hs
  · apply nearbyLumps_mono (side_odd hF) hF.two_le
    intro x₁ p₁ μ ν hμ hc hd hs
    have hl : torusLumpOf R.params x₁ ∈ torusHotLumps R.params (G.frameField GasFamily.empty) :=
      (mem_torusHotLumps_iff R.params hF.admissible (side_dvd hF) _ _).mpr ⟨p₁, μ, ν, hμ, hs, x₁, hc, rfl⟩
    have hst := mem_recordedSites_of_hot_empty hF (mem_torusHotSites_iff.mpr ⟨_, hl, mem_torusLumpOf_self x₁⟩)
    have h2 := supDist_le_two_of_mem_plaquetteVertices hc
    have ag := agreeNear_empty_of_mem_anchor hF (x := p₁) (d := 2) (mem_anchorSites_of_mem_recordedSites hst)
      (by omega)
    rw [curvature_eq_of_agreeNear (side_odd hF) hF.two_le ag]
    exact hs
omit hF in
theorem bases_settingOf_congr {γ₁ : GasFamily R n} {c₀ : TorusSite n}
    (h : ∀ θ : GasSupport R n, c₀ ∈ θ.core → γ θ = γ₁ θ) :
    (G.settingOf γ).bases (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c₀) =
      (G.settingOf γ₁).bases (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c₀) := by apply _root_.YangMills.Construction.InBoxTransfer.bases_congr <;> assumption
omit hF in
theorem isBaseChoice_of_baseUniformWeight_ne_zero {W : TorusField (n * R.params.side)}
    {b : BaseChoice R.params.side n} {y : TorusSite n} (h : baseUniformWeight W b y ≠ 0) :
    IsBaseChoice R.params.baseDepth (stepHotLumps R.params W) b := by apply _root_.YangMills.Construction.InBoxTransfer.isBaseChoice_of_baseUniformWeight_ne_zero <;> assumption
omit hF in
theorem isBaseChoice_of_baseLaw_ne_zero {W : TorusField (n * R.params.side)} {b : BaseChoice R.params.side n}
    (h : baseLaw (R := R) W b ≠ 0) : IsBaseChoice R.params.baseDepth (stepHotLumps R.params W) b := by apply _root_.YangMills.Construction.InBoxTransfer.isBaseChoice_of_baseLaw_ne_zero <;> assumption
end Fields
end FamilyRestrictions
end YangMills.Construction
end
