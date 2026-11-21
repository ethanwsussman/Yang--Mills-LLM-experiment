import YangMills.Construction.ClusterExpansionOfAStep.AllowedStatesReadTheirBoxProof
import YangMills.Construction.ClusterExpansionOfAStep.ZetaOfAGroundIsBorelProof
import YangMills.Construction.ClusterExpansionOfAStep.SettingsOfASharedGasProof
import YangMills.Construction.ClusterExpansionOfAStep.SettingsOfPointsOfWeight
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction
namespace GasSettings
open TorusFields TorusLumps StepGas StepSettings StepCosts BlockAverages BlockTrees BlockZones LumpContours
  HoleSites BlockSites TopLevelSites RenormalizationStepParameters
variable {R : StepSetup} {n : ℕ} [NeZero n]
section Places
variable {L : ℕ} [NeZero L]
theorem supDist_le_of_parentBlock_eq {x z : TorusSite (n * L)} (h : parentBlock L x = parentBlock L z) :
    _root_.YangMills.Construction.TorusFields.supDist x z ≤ L := by apply _root_.YangMills.Construction.TorusLumps.supDist_le_of_parentBlock_eq <;> assumption
theorem supDist_le_two_of_mem_plaquetteVertices {m : ℕ} [NeZero m] {x z : TorusSite m} {μ ν : Fin 4}
    (hz : z ∈ plaquetteVertices x μ ν) : _root_.YangMills.Construction.TorusFields.supDist x z ≤ 2 := by apply _root_.YangMills.Construction.InBoxTransfer.supDist_le_two_of_mem_plaquetteVertices <;> assumption
end Places
section Classes
variable {m : ℕ} [NeZero m] {r : ℕ} {Y Y₁ : Finset (TorusSite m)}
open Classical in
theorem mem_chainComponents_of_separated (hsub : Y₁ ⊆ Y) (hsep : ∀ u ∈ Y₁, ∀ v ∈ Y, v ∉ Y₁ → r < _root_.YangMills.Construction.TorusFields.supDist u v)
    {X : Finset (TorusSite m)} (hX : X ∈ chainComponents r Y) {z : TorusSite m} (hz : z ∈ X) (hz₁ : z ∈ Y₁) :
    X ∈ chainComponents r Y₁ ∧ X ⊆ Y₁ := by apply _root_.YangMills.Construction.InBoxTransfer.mem_chainComponents_of_separated <;> assumption
open Classical in
theorem exists_mem_of_mem_chainComponents {X : Finset (TorusSite m)} (hX : X ∈ chainComponents r Y) : ∃ z, z ∈ X := by apply _root_.YangMills.Construction.InBoxTransfer.exists_mem_of_mem_chainComponents <;> assumption
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
theorem not_occupies_empty : ¬ (GasFamily.empty : GasFamily R n).Occupies θ := by apply _root_.YangMills.Construction.InBoxTransfer.not_occupies_empty <;> assumption
theorem exists_choose_congr {α : Type*} {p q : α → Prop} (hpq : p = q) (h : ∃ a, p a) (h' : ∃ a, q a) :
    h.choose = h'.choose := by apply _root_.YangMills.Construction.SeparatedClasses.LastNonempty.choose_eq_of_eq <;> assumption
theorem state_congr (e : γ θ = γ' θ) (h₁ : γ.Occupies θ) (h₂ : γ'.Occupies θ) : γ.state h₁ = γ'.state h₂ := by apply _root_.YangMills.Construction.InBoxTransfer.state_congr <;> assumption
theorem occupies_iff_of_eq (e : γ θ = γ' θ) : γ.Occupies θ ↔ γ'.Occupies θ := by apply _root_.YangMills.Construction.InBoxTransfer.occupies_congr <;> assumption
theorem mem_sites_iff {z : TorusSite (n * R.params.side)} : z ∈ γ.sites ↔ ∃ θ, γ.Occupies θ ∧ z ∈ θ.2 := by apply _root_.YangMills.Construction.InBoxTransfer.mem_sites_iff <;> assumption
theorem labelAt_congr {z : TorusSite (n * R.params.side)}
    (h : ∀ θ : GasSupport R n, z ∈ θ.2 → γ θ = γ' θ) (hz : z ∈ γ.sites) (hz' : z ∈ γ'.sites) :
    γ.labelAt hz = γ'.labelAt hz' := by
  have hp : (fun θ : GasSupport R n => γ.Occupies θ ∧ z ∈ θ.2) = fun θ => γ'.Occupies θ ∧ z ∈ θ.2 := by
    funext θ
    apply propext
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(occupies_iff_of_eq (h θ h2)).mp h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(occupies_iff_of_eq (h θ h2)).mpr h1, h2⟩
  have hc := exists_choose_congr hp (GasFamily.exists_of_mem_sites hz) (GasFamily.exists_of_mem_sites hz')
  have key : ∀ (θ₁ θ₂ : GasSupport R n), θ₁ = θ₂ → ∀ (h₁ : γ.Occupies θ₁) (h₂ : γ'.Occupies θ₂) (m₁ : z ∈ θ₁.2)
      (m₂ : z ∈ θ₂.2), (γ.state h₁).2.1 ⟨z, m₁⟩ = (γ'.state h₂).2.1 ⟨z, m₂⟩ := by
    intro θ₁ θ₂ e h₁ h₂ m₁ m₂
    subst e
    rw [state_congr (h θ₁ m₁) h₁ h₂]
  exact key _ _ hc _ _ _ _
theorem mem_sites_single_iff (s : SupportState θ) {z : TorusSite (n * R.params.side)} :
    z ∈ (GasFamily.single θ s).sites ↔ z ∈ θ.2 := by apply _root_.YangMills.Construction.InBoxTransfer.mem_sites_single <;> assumption
theorem not_mem_sites_empty {z : TorusSite (n * R.params.side)} : z ∉ (GasFamily.empty : GasFamily R n).sites := by apply _root_.YangMills.Construction.InBoxTransfer.not_mem_sites_empty <;> assumption
end Data
section EvaluationMaps
variable {G : GasGround R n} {γ γ₁ : GasFamily R n}
theorem fine_settingOf_eq_field_zero (hL : Odd R.params.side) (hn : 2 ≤ n) :
    (G.settingOf γ).fine = (G.settingOf γ).field 0 := by apply _root_.YangMills.Construction.InBoxTransfer.fine_eq_field_zero <;> assumption
theorem field_zero_settingOf (hL : Odd R.params.side) (hn : 2 ≤ n) : (G.settingOf γ).field 0 = G.frameField γ :=
  (fine_settingOf_eq_field_zero hL hn).symm
def AgreeNear (γ γ₁ : GasFamily R n) (x : TorusSite (n * R.params.side)) (d : ℕ) : Prop :=
  ∀ θ : GasSupport R n, ∀ u, _root_.YangMills.Construction.TorusFields.supDist x u ≤ d → parentBlock R.params.side u ∈ θ.core → γ θ = γ₁ θ
theorem frameField_congr (hL : Odd R.params.side) (hn : 2 ≤ n) {x : TorusSite (n * R.params.side)} {i : Fin 4}
    (h : ∀ θ : GasSupport R n, parentBlock R.params.side x ∈ θ.core ∨
      parentBlock R.params.side (x + TorusFields.unitStep (n * R.params.side) i) ∈ θ.core → γ θ = γ₁ θ) :
    G.frameField γ x i = G.frameField γ₁ x i := by apply _root_.YangMills.Construction.InBoxTransfer.frameField_congr <;> assumption
theorem frameField_eq_of_agreeNear (hL : Odd R.params.side) (hn : 2 ≤ n) {x : TorusSite (n * R.params.side)} {d : ℕ}
    (h : AgreeNear γ γ₁ x d) {z : TorusSite (n * R.params.side)} (i : Fin 4) (hz : _root_.YangMills.Construction.TorusFields.supDist x z + 1 ≤ d) :
    G.frameField γ z i = G.frameField γ₁ z i := by apply _root_.YangMills.Construction.InBoxTransfer.frameField_eq_of_agreeNear <;> assumption
theorem curvature_eq_of_agreeNear (hL : Odd R.params.side) (hn : 2 ≤ n) {x : TorusSite (n * R.params.side)}
    {μ ν : Fin 4} (h : AgreeNear γ γ₁ x 2) :
    TorusFields.curvature (G.frameField γ) x μ ν = TorusFields.curvature (G.frameField γ₁) x μ ν := by apply _root_.YangMills.Construction.InBoxTransfer.curvature_eq_of_agreeNear <;> assumption
theorem chartCoord_eq_of_agreeNear (hL : Odd R.params.side) (hn : 2 ≤ n) {V : TorusField n}
    {b : TorusBond (n * R.params.side)} (h : AgreeNear γ γ₁ b.1 (R.params.side + 3)) :
    chartCoord R.params V (G.frameField γ) b = chartCoord R.params V (G.frameField γ₁) b := by
  have e := _root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le (n := n * R.params.side) b.1 b.2
  have t1 : blockGauge R.params.side (G.frameField γ) b.1 = blockGauge R.params.side (G.frameField γ₁) b.1 := by
    apply blockGauge_congr hL hn
    intro z i hz _
    have h1 := supDist_le_of_parentBlock_eq hz
    rw [TorusFields.supDist_comm] at h1
    exact frameField_eq_of_agreeNear hL hn h i (by omega)
  have t2 : blockGauge R.params.side (G.frameField γ) (b.1 + TorusFields.unitStep (n * R.params.side) b.2) =
      blockGauge R.params.side (G.frameField γ₁) (b.1 + TorusFields.unitStep (n * R.params.side) b.2) := by
    apply blockGauge_congr hL hn
    intro z i hz _
    have h1 := supDist_le_of_parentBlock_eq hz
    rw [TorusFields.supDist_comm] at h1
    have h2 := _root_.YangMills.Construction.TorusFields.supDist_triangle b.1 (b.1 + TorusFields.unitStep (n * R.params.side) b.2) z
    exact frameField_eq_of_agreeNear hL hn h i (by omega)
  have t3 : G.frameField γ b.1 b.2 = G.frameField γ₁ b.1 b.2 :=
    frameField_eq_of_agreeNear hL hn h b.2 (by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega)
  rw [chartCoord_eq, chartCoord_eq, t1, t2, t3]
theorem exists_site_near_of_mem_core {θ : GasSupport R n} {u : TorusSite (n * R.params.side)}
    (h : parentBlock R.params.side u ∈ θ.core) :
    ∃ z ∈ θ.sites, _root_.YangMills.Construction.TorusFields.supDist u z ≤ 4 * R.range + R.params.side := by apply _root_.YangMills.Construction.InBoxTransfer.exists_site_near_of_mem_core <;> assumption
theorem parentBlock_mem_core (θ : GasSupport R n) {z x : TorusSite (n * R.params.side)} (hz : z ∈ θ.sites)
    (h : _root_.YangMills.Construction.TorusFields.supDist x z ≤ 4 * R.range) : parentBlock R.params.side x ∈ θ.core :=
  parentBlock_mem_coreBlocks_of_near hz h
theorem mem_anchorSites_of_mem_recorded {z : TorusSite (n * R.params.side)} (h : z ∈ G.recordedSites) :
    z ∈ G.anchorSites := by apply _root_.YangMills.Construction.InBoxTransfer.mem_anchorSites_of_mem_recorded <;> assumption
theorem mem_sites_of_mem_snd (θ : GasSupport R n) {z : TorusSite (n * R.params.side)} (hz : z ∈ θ.2) :
    z ∈ θ.sites :=
  Finset.mem_union_right _ hz
end EvaluationMaps
structure IsAdmissibleFamily (G : GasGround R n) (γ : GasFamily R n) : Prop where
  isGasFamily : G.IsGasFamily γ
  isAllowed : ∀ (θ : GasSupport R n) (h : γ.Occupies θ), G.IsAllowed θ (γ.state h)
  admissible : R.params.Admissible
  hasExpansions : R.HasExpansions
  isBlockSide : IsBlockTorusSide R.params (n * R.params.side)
  two_le : 2 ≤ n
  side_le_range : 64 * R.params.side ≤ R.range
  range_ge : 2 ^ 16 ≤ R.range
  groundWeight : G.HasWeightAt GasFamily.empty 0
  exists_zone : ∃ Z, IsRetainedZone G Z
section Fields
variable {G : GasGround R n} {γ : GasFamily R n} (hF : IsAdmissibleFamily G γ)
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
    have ap := hF.isGasFamily.2 θ θ' h h' (Ne.symm e) z hz z' hz'
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
theorem agreeNear_empty_of_anchor {v x : TorusSite (n * R.params.side)} {d : ℕ} (hv : v ∈ G.anchorSites)
    (hd : _root_.YangMills.Construction.TorusFields.supDist x v + d + R.params.side ≤ 6 * R.range) : AgreeNear γ GasFamily.empty x d := by
  intro θ' u hu hc
  show γ θ' = Sum.inl ()
  apply apply_eq_inl_of_not_occupies
  intro h'
  obtain ⟨z', hz', hd'⟩ := exists_site_near_of_mem_core hc
  have ap := (hF.isGasFamily.1 θ' h').far_from_anchor z' hz' v hv
  have t1 := _root_.YangMills.Construction.TorusFields.supDist_triangle z' u v
  have t2 := _root_.YangMills.Construction.TorusFields.supDist_triangle u x v
  rw [_root_.YangMills.Construction.TorusFields.supDist_comm z' u] at t1
  rw [_root_.YangMills.Construction.TorusFields.supDist_comm u x] at t2
  omega
omit hF in
theorem agreeNear_empty_of_forall {x : TorusSite (n * R.params.side)} {d : ℕ}
    (h : ∀ θ : GasSupport R n, γ.Occupies θ → ∀ u, _root_.YangMills.Construction.TorusFields.supDist x u ≤ d → parentBlock R.params.side u ∉ θ.core) :
    AgreeNear γ GasFamily.empty x d := by
  intro θ' u hu hc
  show γ θ' = Sum.inl ()
  apply apply_eq_inl_of_not_occupies
  exact fun h' => h θ' h' u hu hc
theorem side_dvd : R.params.side ∣ n * R.params.side := Dvd.intro_left n rfl
theorem isHullState_single {θ : GasSupport R n} (h : γ.Occupies θ) :
    IsHullState R.params R.range (G.frameField (GasFamily.single θ (γ.state h)))
      (G.settingOf (GasFamily.single θ (γ.state h))).support := (hF.isAllowed θ h).1
theorem isHullState_empty :
    IsHullState R.params R.range (G.frameField GasFamily.empty) (G.settingOf GasFamily.empty).support := by
  have h := hF.groundWeight.isHull
  rwa [field_zero_settingOf (side_odd hF) hF.two_le] at h
theorem mem_torusHotLumps_cases {l : Finset (TorusSite (n * R.params.side))}
    (hl : l ∈ torusHotLumps R.params (G.frameField γ)) :
    (∃ (θ : GasSupport R n) (h : γ.Occupies θ), l ∈ torusHotLumps R.params (G.frameField (GasFamily.single θ (γ.state h)))) ∨
      l ∈ torusHotLumps R.params (G.frameField GasFamily.empty) := by
  classical
  obtain ⟨x, μ, ν, hμ, hs, z, hz, rfl⟩ := (mem_torusHotLumps_iff R.params hF.admissible (side_dvd hF) _ _).mp hl
  have hfar := hF.side_le_range
  have hbig := hF.range_ge
  by_cases hc : ∃ θ : GasSupport R n, γ.Occupies θ ∧ ∃ u, _root_.YangMills.Construction.TorusFields.supDist x u ≤ 2 ∧ parentBlock R.params.side u ∈ θ.core
  · obtain ⟨θ, h, u, hu, hcore⟩ := hc
    have ag := agreeNear_single_of_mem_core hF h (x := x) (d := 2) hcore (by omega)
    refine Or.inl ⟨θ, h, (mem_torusHotLumps_iff R.params hF.admissible (side_dvd hF) _ _).mpr
      ⟨x, μ, ν, hμ, ?_, z, hz, rfl⟩⟩
    rw [← curvature_eq_of_agreeNear (side_odd hF) hF.two_le ag]
    exact hs
  · refine Or.inr ((mem_torusHotLumps_iff R.params hF.admissible (side_dvd hF) _ _).mpr
      ⟨x, μ, ν, hμ, ?_, z, hz, rfl⟩)
    rw [← curvature_eq_of_agreeNear (side_odd hF) hF.two_le
      (agreeNear_empty_of_forall fun θ h u hu hcore => hc ⟨θ, h, u, hu, hcore⟩)]
    exact hs
theorem mem_recorded_of_hot_empty {z : TorusSite (n * R.params.side)}
    (hz : z ∈ torusHotSites R.params (G.frameField GasFamily.empty)) : z ∈ G.recordedSites := by
  have h := (isHullState_empty hF).1 ((mem_thickening _ _ _).mpr ⟨z, hz, by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega⟩)
  rcases Finset.mem_union.mp h with a | a
  · exact a
  · exact absurd a not_mem_sites_empty
theorem mem_recorded_or_of_hot_single {θ : GasSupport R n} (h : γ.Occupies θ) {z : TorusSite (n * R.params.side)}
    (hz : z ∈ torusHotSites R.params (G.frameField (GasFamily.single θ (γ.state h)))) :
    z ∈ G.recordedSites ∨ z ∈ θ.2 := by
  have h' := (isHullState_single hF h).1 ((mem_thickening _ _ _).mpr ⟨z, hz, by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega⟩)
  rcases Finset.mem_union.mp h' with a | a
  · exact Or.inl a
  · exact Or.inr ((mem_sites_single_iff _).mp a)
theorem mem_torusHotLumps_of_empty {l : Finset (TorusSite (n * R.params.side))}
    (hl : l ∈ torusHotLumps R.params (G.frameField GasFamily.empty)) :
    l ∈ torusHotLumps R.params (G.frameField γ) := by
  classical
  have hfar := hF.side_le_range
  have hbig := hF.range_ge
  obtain ⟨x, μ, ν, hμ, hs, z, hz, hlz⟩ := (mem_torusHotLumps_iff R.params hF.admissible (side_dvd hF) _ _).mp hl
  have hzl : z ∈ l := by
    rw [hlz]
    exact mem_torusLumpOf_self z
  have hst := mem_recorded_of_hot_empty hF (mem_torusHotSites_iff.mpr ⟨l, hl, hzl⟩)
  have hd := _root_.YangMills.Construction.GasSettings.supDist_le_two_of_mem_plaquetteVertices hz
  have ag := agreeNear_empty_of_anchor hF (x := x) (d := 2) (mem_anchorSites_of_mem_recorded hst) (by omega)
  refine (mem_torusHotLumps_iff R.params hF.admissible (side_dvd hF) _ _).mpr ⟨x, μ, ν, hμ, ?_, z, hz, hlz⟩
  rw [curvature_eq_of_agreeNear (side_odd hF) hF.two_le ag]
  exact hs
theorem mem_torusHotLumps_of_single {θ : GasSupport R n} (h : γ.Occupies θ) {l : Finset (TorusSite (n * R.params.side))}
    (hl : l ∈ torusHotLumps R.params (G.frameField (GasFamily.single θ (γ.state h))))
    {w u : TorusSite (n * R.params.side)} (hw : w ∈ l)
    (hu : u ∈ θ.sites) (hd : _root_.YangMills.Construction.TorusFields.supDist w u ≤ 4 * R.range) : l ∈ torusHotLumps R.params (G.frameField γ) := by
  classical
  have hfar := hF.side_le_range
  have hbig := hF.range_ge
  obtain ⟨x, μ, ν, hμ, hs, z, hz, hlz⟩ := (mem_torusHotLumps_iff R.params hF.admissible (side_dvd hF) _ _).mp hl
  have hzl : z ∈ l := by
    rw [hlz]
    exact mem_torusLumpOf_self z
  have h1 := _root_.YangMills.Construction.TorusLumps.supDist_lt_of_mem_torusHotLumps hF.admissible (side_dvd hF) hl hzl hw
  have h2 := _root_.YangMills.Construction.GasSettings.supDist_le_two_of_mem_plaquetteVertices hz
  have t1 := _root_.YangMills.Construction.TorusFields.supDist_triangle x z u
  have t2 := _root_.YangMills.Construction.TorusFields.supDist_triangle z w u
  have ag := agreeNear_single_of_mem_sites hF h (x := x) (d := 2) hu (by omega)
  refine (mem_torusHotLumps_iff R.params hF.admissible (side_dvd hF) _ _).mpr ⟨x, μ, ν, hμ, ?_, z, hz, hlz⟩
  rw [curvature_eq_of_agreeNear (side_odd hF) hF.two_le ag]
  exact hs
theorem range_lt_supDist_recorded {θ : GasSupport R n} (h : γ.Occupies θ) {u v : TorusSite (n * R.params.side)}
    (hu : u ∈ θ.2) (hv : v ∈ G.recordedSites) : R.range < _root_.YangMills.Construction.TorusFields.supDist u v := by
  have := (hF.isGasFamily.1 θ h).far_from_anchor u (mem_sites_of_mem_snd θ hu) v (mem_anchorSites_of_mem_recorded hv)
  omega
theorem range_lt_supDist_of_ne {θ θ' : GasSupport R n} (h : γ.Occupies θ) (h' : γ.Occupies θ') (e : θ ≠ θ')
    {u v : TorusSite (n * R.params.side)} (hu : u ∈ θ.2) (hv : v ∈ θ'.2) : R.range < _root_.YangMills.Construction.TorusFields.supDist u v := by
  have := hF.isGasFamily.2 θ θ' h h' e u (mem_sites_of_mem_snd θ hu) v (mem_sites_of_mem_snd θ' hv)
  omega
omit hF in
theorem support_settingOf_empty : (G.settingOf GasFamily.empty).support = G.recordedSites := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.groundSetting_support <;> assumption
theorem chainComponent_of_recorded {X : Finset (TorusSite (n * R.params.side))}
    (hX : X ∈ chainComponents R.range (G.settingOf γ).support)
    {z : TorusSite (n * R.params.side)} (hz : z ∈ X) (hzs : z ∈ G.recordedSites) :
    X ∈ chainComponents R.range (G.settingOf GasFamily.empty).support ∧ X ⊆ G.recordedSites := by
  have key := mem_chainComponents_of_separated (Y₁ := G.recordedSites) Finset.subset_union_left (fun u hu v hv hn => by
    rcases Finset.mem_union.mp hv with a | a
    · exact absurd a hn
    · obtain ⟨θ, h, hvθ⟩ := mem_sites_iff.mp a
      rw [TorusFields.supDist_comm]
      exact range_lt_supDist_recorded hF h hvθ hu) hX hz hzs
  exact ⟨by rw [support_settingOf_empty]; exact key.1, key.2⟩
theorem chainComponent_of_single {θ : GasSupport R n} (h : γ.Occupies θ) {X : Finset (TorusSite (n * R.params.side))}
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
      · rw [TorusFields.supDist_comm]
        exact range_lt_supDist_recorded hF h' hvθ c
      · exact range_lt_supDist_of_ne hF h h' e ((mem_sites_single_iff _).mp c) hvθ) hX hz
    (Finset.mem_union_right _ ((mem_sites_single_iff _).mpr hzθ))
  exact ⟨k1.1, k1.2, k2.1⟩
theorem isHullState_family : IsHullState R.params R.range (G.frameField γ) (G.settingOf γ).support := by
  classical
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨x, hx, hzx⟩ := (mem_thickening _ _ _).mp hz
    obtain ⟨l, hl, hxl⟩ := mem_torusHotSites_iff.mp hx
    rcases mem_torusHotLumps_cases hF hl with ⟨θ, h, hl'⟩ | hl'
    · have h1 := (isHullState_single hF h).1
        ((mem_thickening _ _ _).mpr ⟨x, mem_torusHotSites_iff.mpr ⟨l, hl', hxl⟩, hzx⟩)
      rcases Finset.mem_union.mp h1 with a | a
      · exact Finset.mem_union_left _ a
      · exact Finset.mem_union_right _ (mem_sites_iff.mpr ⟨θ, h, (mem_sites_single_iff _).mp a⟩)
    · have h1 := (isHullState_empty hF).1 ((mem_thickening _ _ _).mpr ⟨x, mem_torusHotSites_iff.mpr ⟨l, hl', hxl⟩, hzx⟩)
      rcases Finset.mem_union.mp h1 with a | a
      · exact Finset.mem_union_left _ a
      · exact absurd a not_mem_sites_empty
  · intro X hX
    obtain ⟨z, hz⟩ := exists_mem_of_mem_chainComponents hX
    rcases Finset.mem_union.mp (subset_of_mem_chainComponents hX hz) with a | a
    · obtain ⟨l, hl, hw⟩ := (isHullState_empty hF).2 X (chainComponent_of_recorded hF hX hz a).1
      exact ⟨l, mem_torusHotLumps_of_empty hF hl, hw⟩
    · obtain ⟨θ, h, hzθ⟩ := mem_sites_iff.mp a
      obtain ⟨h1, h2, h3⟩ := chainComponent_of_single hF h hX hz hzθ
      obtain ⟨l, hl, w, hw⟩ := (isHullState_single hF h).2 X h3
      obtain ⟨hwl, hwX⟩ := Finset.mem_inter.mp hw
      exact ⟨l, mem_torusHotLumps_of_single hF h hl hwl (mem_sites_of_mem_snd θ (h2 hwX))
        (by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega), w, hw⟩
omit hF in
theorem labelling_congr {γ₁ : GasFamily R n} {z : TorusSite (n * R.params.side)} (h₁ : z ∈ (G.settingOf γ).support)
    (h₂ : z ∈ (G.settingOf γ₁).support) (hs : ∀ θ : GasSupport R n, z ∈ θ.2 → γ θ = γ₁ θ) :
    (G.settingOf γ).labelling ⟨z, h₁⟩ = (G.settingOf γ₁).labelling ⟨z, h₂⟩ := by
  classical
  have hiff : z ∈ γ.sites ↔ z ∈ γ₁.sites := by
    rw [mem_sites_iff, mem_sites_iff]
    exact exists_congr fun θ =>
      ⟨fun ⟨a, b⟩ => ⟨(occupies_iff_of_eq (hs θ b)).mp a, b⟩, fun ⟨a, b⟩ => ⟨(occupies_iff_of_eq (hs θ b)).mpr a, b⟩⟩
  show (G.settingWithFamily γ).labelling ⟨z, h₁⟩ = (G.settingWithFamily γ₁).labelling ⟨z, h₂⟩
  simp only [GasGround.settingWithFamily]
  by_cases hz : z ∈ γ.sites
  · rw [dif_pos hz, dif_pos (hiff.mp hz)]
    exact labelAt_congr hs _ _
  · rw [dif_neg hz, dif_neg fun c => hz (hiff.mpr c)]
theorem clusterFactor_ne_zero : ∀ X ∈ chainComponents R.range (G.settingOf γ).support,
    R.clusterFactor (n * R.params.side) (G.frameField γ) (G.settingOf γ).support (G.settingOf γ).labelling X ≠ 0 := by
  classical
  intro X hX
  have hfar := hF.side_le_range
  have hbig := hF.range_ge
  obtain ⟨z, hz⟩ := exists_mem_of_mem_chainComponents hX
  rcases Finset.mem_union.mp (subset_of_mem_chainComponents hX hz) with a | a
  · obtain ⟨hc, hs⟩ := chainComponent_of_recorded hF hX hz a
    have e : R.clusterFactor (n * R.params.side) (G.frameField γ) (G.settingOf γ).support (G.settingOf γ).labelling X =
        R.clusterFactor (n * R.params.side) (G.frameField GasFamily.empty) (G.settingOf GasFamily.empty).support
          (G.settingOf GasFamily.empty).labelling X := by
      refine hF.hasExpansions.2.reads_class (n * R.params.side) hF.isBlockSide _ _ _ _ _ _ X
        (subset_of_mem_chainComponents hX) (subset_of_mem_chainComponents hc) ?_ ?_
      · intro b hb _
        have ag := agreeNear_empty_of_anchor hF (x := b.1) (d := 1) (mem_anchorSites_of_mem_recorded (hs hb))
          (by rw [supDist_self]; omega)
        exact frameField_eq_of_agreeNear (side_odd hF) hF.two_le ag b.2 (by rw [supDist_self])
      · intro w hw hw' hwX
        have ag := agreeNear_empty_of_anchor hF (x := w) (d := 0) (mem_anchorSites_of_mem_recorded (hs hwX))
          (by rw [supDist_self]; omega)
        exact labelling_congr _ _ fun θ hθ => ag θ w (by rw [_root_.YangMills.Construction.TorusFields.supDist_self])
          (parentBlock_mem_core θ (mem_sites_of_mem_snd θ hθ) (by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega))
    rw [e]
    have h0 := hF.groundWeight.factor_ne_zero X hc
    rwa [field_zero_settingOf (side_odd hF) hF.two_le] at h0
  · obtain ⟨θ, h, hzθ⟩ := mem_sites_iff.mp a
    obtain ⟨h1, h2, h3⟩ := chainComponent_of_single hF h hX hz hzθ
    have e : R.clusterFactor (n * R.params.side) (G.frameField γ) (G.settingOf γ).support (G.settingOf γ).labelling X =
        R.clusterFactor (n * R.params.side) (G.frameField (GasFamily.single θ (γ.state h)))
          (G.settingOf (GasFamily.single θ (γ.state h))).support
          (G.settingOf (GasFamily.single θ (γ.state h))).labelling X := by
      refine hF.hasExpansions.2.reads_class (n * R.params.side) hF.isBlockSide _ _ _ _ _ _ X
        (subset_of_mem_chainComponents hX) (subset_of_mem_chainComponents h3) ?_ ?_
      · intro b hb _
        have ag := agreeNear_single_of_mem_sites hF h (x := b.1) (d := 1) (mem_sites_of_mem_snd θ (h2 hb))
          (by rw [supDist_self]; omega)
        exact frameField_eq_of_agreeNear (side_odd hF) hF.two_le ag b.2 (by rw [supDist_self])
      · intro w hw hw' hwX
        have ag := agreeNear_single_of_mem_sites hF h (x := w) (d := 0) (mem_sites_of_mem_snd θ (h2 hwX))
          (by rw [supDist_self]; omega)
        exact labelling_congr _ _ fun θ' hθ => ag θ' w (by rw [_root_.YangMills.Construction.TorusFields.supDist_self])
          (parentBlock_mem_core θ' (mem_sites_of_mem_snd θ' hθ) (by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega))
    rw [e]
    exact (hF.isAllowed θ h).2.1 X h1
omit hF in
theorem exists_anchor_near_of_mem_zone {Z : Finset (TorusSite n)} (hZ : IsRetainedZone G Z)
    {u : TorusSite (n * R.params.side)} (hu : parentBlock R.params.side u ∈ Z) :
    ∃ v ∈ G.anchorSites, _root_.YangMills.Construction.TorusFields.supDist u v ≤ 4 * R.range + R.params.side := by
  classical
  rw [hZ.zone_eq] at hu
  rcases Finset.mem_union.mp hu with a | a
  · refine ⟨u, ?_, by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega⟩
    unfold GasGround.anchorSites
    refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, a⟩
  · obtain ⟨x, hx⟩ := (Finset.mem_filter.mp a).2
    obtain ⟨hb, hw⟩ := Finset.mem_inter.mp hx
    obtain ⟨z, hz, hxz⟩ := (mem_thickening _ _ _).mp hw
    have e : parentBlock R.params.side x = parentBlock R.params.side u :=
      Finset.mem_singleton.mp (Finset.mem_filter.mp hb).2
    have h0 := _root_.YangMills.Construction.GasSettings.supDist_le_of_parentBlock_eq e
    have h1 := _root_.YangMills.Construction.TorusFields.supDist_triangle u x z
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm u x] at h1
    exact ⟨z, hz, by omega⟩
theorem bondMark_ne_zero_family : ∀ b ∈ chartBonds R.params.side n, b ∉ (G.settingOf γ).free →
    b ∉ (G.settingOf γ).bad → bondMark R G.coarse (G.frameField γ) b ≠ 0 := by
  classical
  intro b hc hnf hnb
  have hfar := hF.side_le_range
  have hbig := hF.range_ge
  have hnC : parentBlock R.params.side b.1 ∉ G.cut := fun hC =>
    hnb (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hc, hC⟩))
  have hmk : b ∈ markedBonds R G.cut := Finset.mem_filter.mpr ⟨hc, hnC⟩
  by_cases hf : γ.fieldAt b = Sum.inl ()
  · have hst : G.IsRecorded b := by
      by_contra hns
      exact hnf (show b ∈ G.freeBonds.filter (fun b => γ.fieldAt b = Sum.inl ()) from
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hmk, hns⟩, hf⟩)
    obtain ⟨Z, hZ⟩ := hF.exists_zone
    obtain ⟨v, hv, hd⟩ := exists_anchor_near_of_mem_zone hZ ((hZ.bond_iff b).mp hst).1
    have ag := agreeNear_empty_of_anchor hF (x := b.1) (d := R.params.side + 3) hv (by omega)
    have hnf₀ : b ∉ (G.settingOf GasFamily.empty).free := fun hb => (mem_free_settingOf hb).2.1 hst
    have hnb₀ : b ∉ (G.settingOf GasFamily.empty).bad := by
      intro hb
      have h1 : b ∈ G.recordedBad ∪
          (Finset.univ.filter fun θ => (GasFamily.empty : GasFamily R n).Occupies θ).biUnion Prod.fst ∪
          (chartBonds R.params.side n).filter fun b => parentBlock R.params.side b.1 ∈ G.cut := hb
      rcases Finset.mem_union.mp h1 with h2 | h2
      · rcases Finset.mem_union.mp h2 with h3 | h3
        · exact hnb (Finset.mem_union_left _ (Finset.mem_union_left _ h3))
        · obtain ⟨θ, hθ, _⟩ := Finset.mem_biUnion.mp h3
          exact not_occupies_empty (Finset.mem_filter.mp hθ).2
      · exact hnb (Finset.mem_union_right _ h2)
    have h0 := hF.groundWeight.bondMark_ne_zero b hc hnf₀ hnb₀
    rw [field_zero_settingOf (side_odd hF) hF.two_le] at h0
    unfold bondMark at h0 ⊢
    rw [chartCoord_eq_of_agreeNear (side_odd hF) hF.two_le ag]
    exact h0
  · have hex : ∃ θ : GasSupport R n, γ.Occupies θ ∧ b ∈ θ.coreBonds := by
      by_contra hne
      apply hf
      unfold GasFamily.fieldAt
      rw [dif_neg hne]
    obtain ⟨θ, h, hst⟩ := hex
    have hbad : b ∉ θ.1 := fun hb => hnb (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨θ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, hb⟩)))
    have h3 := (hF.isAllowed θ h).2.2.1 b (Finset.mem_inter.mpr ⟨hst, hmk⟩) hbad
    have ag := agreeNear_single_of_mem_core hF h (v := b.1) (x := b.1) (d := R.params.side + 3)
      (Finset.mem_filter.mp hst).2.1 (by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega)
    unfold bondMark at h3 ⊢
    rw [chartCoord_eq_of_agreeNear (side_odd hF) hF.two_le ag]
    exact h3
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
theorem nearbyLumps_mono (hL : Odd R.params.side) (hn : 2 ≤ n) (W W' : TorusField (n * R.params.side)) (c₀ : TorusSite n)
    (hyp : ∀ (x₁ p₁ : TorusSite (n * R.params.side)) (μ ν : Fin 4), μ < ν → x₁ ∈ plaquetteVertices p₁ μ ν →
      _root_.YangMills.Construction.TorusFields.supDist c₀ (parentBlock R.params.side x₁) ≤ 2 → R.params.threshold ≤ TorusFields.curvature W p₁ μ ν →
      R.params.threshold ≤ TorusFields.curvature W' p₁ μ ν) :
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
  have hfar := hF.side_le_range
  have hbig := hF.range_ge
  obtain ⟨v, hv⟩ : ∃ v : TorusSite (n * R.params.side), parentBlock R.params.side v = c₀ :=
    ⟨blockSite c₀ (fun _ => 0), BlockPlaces.parentBlock_blockSite _ _⟩
  have ag : ∀ (x₁ p₁ : TorusSite (n * R.params.side)) (μ ν : Fin 4), x₁ ∈ plaquetteVertices p₁ μ ν →
      _root_.YangMills.Construction.TorusFields.supDist c₀ (parentBlock R.params.side x₁) ≤ 2 → AgreeNear γ (GasFamily.single θ (γ.state h)) p₁ 2 := by
    intro x₁ p₁ μ ν hc hd
    have h1 := _root_.YangMills.Construction.GasSettings.supDist_le_four_mul hv hd
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
theorem nearbyLumps_eq_empty {c₀ : TorusSite n} (hy : ∀ θ : GasSupport R n, γ.Occupies θ → c₀ ∉ θ.core) :
    nearbyLumps (stepHotLumps R.params (G.frameField γ)) (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c₀) =
      nearbyLumps (stepHotLumps R.params (G.frameField GasFamily.empty))
        (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c₀) := by
  classical
  have hfar := hF.side_le_range
  have hbig := hF.range_ge
  obtain ⟨v, hv⟩ : ∃ v : TorusSite (n * R.params.side), parentBlock R.params.side v = c₀ :=
    ⟨blockSite c₀ (fun _ => 0), BlockPlaces.parentBlock_blockSite _ _⟩
  apply Finset.Subset.antisymm
  · apply nearbyLumps_mono (side_odd hF) hF.two_le
    intro x₁ p₁ μ ν hμ hc hd hs
    by_cases hex : ∃ θ : GasSupport R n, γ.Occupies θ ∧ ∃ u, _root_.YangMills.Construction.TorusFields.supDist p₁ u ≤ 2 ∧ parentBlock R.params.side u ∈ θ.core
    · exfalso
      obtain ⟨θ, h, u, hu, hcore⟩ := hex
      have ag := agreeNear_single_of_mem_core hF h (x := p₁) (d := 2) hcore (by omega)
      rw [curvature_eq_of_agreeNear (side_odd hF) hF.two_le ag] at hs
      have hl : torusLumpOf R.params x₁ ∈ torusHotLumps R.params (G.frameField (GasFamily.single θ (γ.state h))) :=
        (mem_torusHotLumps_iff R.params hF.admissible (side_dvd hF) _ _).mpr ⟨p₁, μ, ν, hμ, hs, x₁, hc, rfl⟩
      have h2 := _root_.YangMills.Construction.GasSettings.supDist_le_two_of_mem_plaquetteVertices hc
      rcases mem_recorded_or_of_hot_single hF h (mem_torusHotSites_iff.mpr ⟨_, hl, mem_torusLumpOf_self x₁⟩) with a | a
      · obtain ⟨z, hz, hzd⟩ := exists_site_near_of_mem_core hcore
        have ap := (hF.isGasFamily.1 θ h).far_from_anchor z hz x₁ (mem_anchorSites_of_mem_recorded a)
        have t1 := _root_.YangMills.Construction.TorusFields.supDist_triangle z u x₁
        have t2 := _root_.YangMills.Construction.TorusFields.supDist_triangle u p₁ x₁
        rw [_root_.YangMills.Construction.TorusFields.supDist_comm z u] at t1
        rw [_root_.YangMills.Construction.TorusFields.supDist_comm u p₁] at t2
        omega
      · have h1 := _root_.YangMills.Construction.GasSettings.supDist_le_four_mul hv hd
        refine hy θ h ?_
        rw [← hv]
        rw [TorusFields.supDist_comm] at h1
        exact parentBlock_mem_core θ (mem_sites_of_mem_snd θ a) (by omega)
    · rw [← curvature_eq_of_agreeNear (side_odd hF) hF.two_le
        (agreeNear_empty_of_forall fun θ h u hu hcore => hex ⟨θ, h, u, hu, hcore⟩)]
      exact hs
  · apply nearbyLumps_mono (side_odd hF) hF.two_le
    intro x₁ p₁ μ ν hμ hc hd hs
    have hl : torusLumpOf R.params x₁ ∈ torusHotLumps R.params (G.frameField GasFamily.empty) :=
      (mem_torusHotLumps_iff R.params hF.admissible (side_dvd hF) _ _).mpr ⟨p₁, μ, ν, hμ, hs, x₁, hc, rfl⟩
    have hst := mem_recorded_of_hot_empty hF (mem_torusHotSites_iff.mpr ⟨_, hl, mem_torusLumpOf_self x₁⟩)
    have h2 := supDist_le_two_of_mem_plaquetteVertices hc
    have ag := agreeNear_empty_of_anchor hF (x := p₁) (d := 2) (mem_anchorSites_of_mem_recorded hst) (by omega)
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
theorem baseLaw_ne_zero_family : baseLaw (R := R) (G.frameField γ) (G.settingOf γ).bases ≠ 0 := by
  classical
  have hfar := hF.side_le_range
  have hb : IsBaseChoice R.params.baseDepth (stepHotLumps R.params (G.frameField γ)) (G.settingOf γ).bases := by
    apply isBaseChoice_of_local
    intro c
    obtain ⟨c₀, rfl⟩ := torusSiteInFrame_surjective (stepBlockFrame R.params.side n) 1 stepBlockFrame_period_one c
    by_cases hc : ∃ θ : GasSupport R n, γ.Occupies θ ∧ c₀ ∈ θ.core
    · obtain ⟨θ, h, hy⟩ := hc
      refine ⟨_, _, isBaseChoice_of_baseUniformWeight_ne_zero ((hF.isAllowed θ h).2.2.2 c₀ hy),
        nearbyLumps_eq_single hF h hy, bases_settingOf_congr ?_⟩
      intro θ' hθ'
      obtain ⟨v, hv⟩ : ∃ v : TorusSite (n * R.params.side), parentBlock R.params.side v = c₀ :=
        ⟨blockSite c₀ (fun _ => 0), BlockPlaces.parentBlock_blockSite _ _⟩
      have ag := agreeNear_single_of_mem_core hF h (x := v) (d := 0) (v := v) (by rw [hv]; exact hy)
        (by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega)
      exact ag θ' v (by rw [_root_.YangMills.Construction.TorusFields.supDist_self]) (by rw [hv]; exact hθ')
    · have hy : ∀ θ : GasSupport R n, γ.Occupies θ → c₀ ∉ θ.core := fun θ h hθ => hc ⟨θ, h, hθ⟩
      have h0 := hF.groundWeight.baseLaw_ne_zero
      rw [field_zero_settingOf (side_odd hF) hF.two_le] at h0
      refine ⟨_, _, isBaseChoice_of_baseLaw_ne_zero h0, nearbyLumps_eq_empty hF hy, bases_settingOf_congr ?_⟩
      intro θ' hθ'
      show γ θ' = Sum.inl ()
      exact apply_eq_inl_of_not_occupies fun h' => hy θ' h' hθ'
  have hmem : (G.settingOf γ).bases ∈ baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 (G.frameField γ)) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩
  unfold baseLaw
  rw [if_pos hmem]
  have hne : (baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 (G.frameField γ))).card ≠ 0 :=
    Finset.card_ne_zero.mpr ⟨_, hmem⟩
  exact one_div_ne_zero (Nat.cast_ne_zero.mpr hne)
theorem hasWeightAt_family : G.HasWeightAt γ 0 := by
  have hz := field_zero_settingOf (G := G) (γ := γ) (side_odd hF) hF.two_le
  have hρ : 0 < R.ballRadius := by
    have := hF.admissible.σ_pos
    unfold StepSetup.ballRadius
    positivity
  refine ⟨fun b => ?_, ?_, ?_, ?_, ?_⟩
  · simpa [coordNorm, norm_toImaginary, Pi.zero_apply] using hρ
  · rw [hz]
    exact isHullState_family hF
  · rw [hz]
    exact clusterFactor_ne_zero hF
  · rw [hz]
    exact baseLaw_ne_zero_family hF
  · rw [hz]
    exact bondMark_ne_zero_family hF
end Fields
section Configurations
variable {G : GasGround R n}
theorem exists_spin_of_occupies {σ : G.Config} {θ : GasSupport R n} (h : (G.familyOf σ).Occupies θ) :
    ∃ (hs : G.IsGasSupport θ) (s : G.SpinState ⟨θ, hs⟩), σ ⟨θ, hs⟩ = Sum.inr s ∧ G.familyOf σ θ = Sum.inr s.1 := by
  classical
  by_cases hs : G.IsGasSupport θ
  · have e : G.familyOf σ θ = (match σ ⟨θ, hs⟩ with
        | Sum.inr s => Sum.inr s.1
        | Sum.inl _ => Sum.inl ()) := dif_pos hs
    cases hv : σ ⟨θ, hs⟩ with
    | inl u =>
      rw [hv] at e
      exfalso
      unfold GasFamily.Occupies at h
      rw [e] at h
      simp at h
    | inr s =>
      rw [hv] at e
      exact ⟨hs, s, hv, e⟩
  · exfalso
    have e : G.familyOf σ θ = Sum.inl () := dif_neg hs
    unfold GasFamily.Occupies at h
    rw [e] at h
    simp at h
theorem isGasFamily_familyOf {σ : G.Config} (hσ : G.pairConstraint.IsAdmissible σ) : G.IsGasFamily (G.familyOf σ) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.SharedGasSettings.isGasFamily_familyOf <;> assumption
theorem isAllowed_familyOf {σ : G.Config} {θ : GasSupport R n} (h : (G.familyOf σ).Occupies θ) :
    G.IsAllowed θ ((G.familyOf σ).state h) := by
  obtain ⟨hs, s, _, e⟩ := exists_spin_of_occupies h
  have e2 : (G.familyOf σ).state h = s.1 := Sum.inr.inj ((apply_eq_inr_of_occupies h).symm.trans e)
  rw [e2]
  exact s.2
end Configurations
end GasSettings
namespace ClusterExpansionOfAStep
open TorusFields TorusLumps StepGas StepSettings StepCosts RenormalizationStepParameters BlockZones GasSettings
theorem gasConfigIsAdmissibleSetting_holds (hs : SettingAdmissibleOfHasWeight) (hg : GroundWeightAtEmpty) :
    GasConfigIsAdmissibleSetting := by
  classical
  intro T hT
  obtain ⟨y₁, hy₁⟩ := hs T hT
  obtain ⟨y₂, hy₂⟩ := hg T hT
  set A : ℕ := max (2 ^ 16) (64 * T.side) with hA
  refine ⟨max (max y₁ y₂) (max T.floorMin ((A : ℝ) ^ 100 + 1)), fun y hy R hOn hx n _ G hG σ hσ => ?_⟩
  have hy1 : y₁ ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy
  have hy2 : y₂ ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hy
  have hy3 : T.floorMin ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hy
  have hy4 : (A : ℝ) ^ 100 ≤ y := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hy
    linarith
  have hfit : R.params.Admissible := by
    rw [hOn.params_eq]
    exact hT.fits y hy3
  have eL : R.params.side = T.side := by rw [hOn.params_eq]; rfl
  have en : R.params.n₀ = T.n₀ := by rw [hOn.params_eq]; rfl
  have hxA : (A : ℝ) ≤ R.coupling ^ ((1 : ℝ) / 100) := by
    have e : ((A : ℝ) ^ 100) ^ ((1 : ℝ) / 100) = A := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg A)]
      norm_num
    calc (A : ℝ) = ((A : ℝ) ^ 100) ^ ((1 : ℝ) / 100) := e.symm
      _ ≤ R.coupling ^ ((1 : ℝ) / 100) :=
        Real.rpow_le_rpow (by positivity) (hy4.trans hOn.le_coupling) (by norm_num)
  have hr : A ≤ R.range := by
    have h1 : (A : ℝ) ≤ (R.range : ℝ) := hxA.trans (Nat.le_ceil _)
    exact_mod_cast h1
  have hn₁ : R.params.n₀ ≤ n := by
    rcases hG with hc | hc
    · exact hc.n₀_le
    · exact le_trans (Nat.le_mul_of_pos_left _ (NeZero.pos _)) hc.isBlockSide.2
  have hblock : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Dvd.intro_left n rfl, by rw [mul_comm]; exact Nat.mul_le_mul_right _ hn₁⟩
  have hn₂ : 2 ≤ n := by
    have h4 := hT.n₀_ge
    rw [en] at hn₁
    omega
  have hF : IsAdmissibleFamily G (G.familyOf σ) :=
    { isGasFamily := isGasFamily_familyOf hσ
      isAllowed := fun θ h => isAllowed_familyOf h
      admissible := hfit
      hasExpansions := hOn.isStep.1
      isBlockSide := hblock
      two_le := hn₂
      side_le_range := by rw [eL]; exact le_trans (le_max_right _ _) hr
      range_ge := le_trans (le_max_left _ _) hr
      groundWeight := hy₂ y hy2 R hOn hx n G hG
      exists_zone := exists_isAdmissibleZone G hG }
  exact hy₁ y hy1 R hOn hx n G hG _ hF.isGasFamily 0 (hasWeightAt_family hF)
end ClusterExpansionOfAStep
end YangMills.Construction
end
