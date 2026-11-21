import YangMills.Construction.ClusterExpansionOfAStep.CasesOfAGroundAreFamilies
import YangMills.Construction.ClusterExpansionOfAStep.ClustersHaveClassSupports
import YangMills.Construction.ClusterExpansionOfAStep.CountFloorCanBeMet
import YangMills.Construction.ClusterExpansionOfAStep.OffNearDensitiesMoveLittleProof
import YangMills.Construction.ClusterExpansionOfAStep.ZonesOfAFamily
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
open TorusFields TorusLumps StepSettings StepGas StepCosts BlockZones FamilyZones
namespace StepGas.FamilyCases
variable {R : StepSetup} {n : ℕ} [NeZero n] {G : GasGround R n} {Γ Γ' : Finset G.GasSpin}
theorem fst_mem_sites_of_mem_bad (i : G.GasSpin) {b : TorusBond (n * R.params.side)} (hb : b ∈ i.1.1) :
    b.1 ∈ i.1.sites :=
  Finset.mem_union_left _ (Finset.mem_image_of_mem _ hb)
theorem mem_anchorSites_of_mem_recordedBad {b : TorusBond (n * R.params.side)} (hb : b ∈ G.recordedBad) :
    b.1 ∈ G.anchorSites := by
  classical
  unfold GasGround.anchorSites
  exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hb))
theorem not_mem_recordedBad_of_mem_bad (i : G.GasSpin) {b : TorusBond (n * R.params.side)} (hb : b ∈ i.1.1) :
    b ∉ G.recordedBad := fun h => by
  have := i.2.far_from_anchor _ (fst_mem_sites_of_mem_bad i hb) _ (mem_anchorSites_of_mem_recordedBad h)
  rw [supDist_self] at this
  omega
theorem exists_of_mem_familyBadBonds {b : TorusBond (n * R.params.side)} (hb : b ∈ G.familyBadBonds Γ)
    (hn : b ∉ G.recordedBad) : ∃ i ∈ Γ, b ∈ i.1.1 := by
  classical
  rcases Finset.mem_union.mp hb with a | a
  · exact absurd a hn
  · exact Finset.mem_biUnion.mp a
theorem exists_of_mem_familySites {z : TorusSite (n * R.params.side)} (hz : z ∈ G.familySites Γ)
    (hn : z ∉ G.recordedSites) : ∃ i ∈ Γ, z ∈ i.1.2 := by
  classical
  rcases Finset.mem_union.mp hz with a | a
  · exact absurd a hn
  · exact Finset.mem_biUnion.mp a
theorem exists_spin_of_mem_sites (h1 : G.familyBadBonds Γ = G.familyBadBonds Γ')
    (h2 : G.familySites Γ = G.familySites Γ') {i : G.GasSpin} (hi : i ∈ Γ)
    {z : TorusSite (n * R.params.side)} (hz : z ∈ i.1.sites) : ∃ j ∈ Γ', z ∈ j.1.sites := by
  classical
  rcases Finset.mem_union.mp hz with a | a
  · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp a
    have hb' : b ∈ G.familyBadBonds Γ' :=
      h1 ▸ Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, hi, hb⟩)
    obtain ⟨j, hj, hbj⟩ := exists_of_mem_familyBadBonds hb' (not_mem_recordedBad_of_mem_bad i hb)
    exact ⟨j, hj, fst_mem_sites_of_mem_bad j hbj⟩
  · have hz' : z ∈ G.familySites Γ' :=
      h2 ▸ Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, hi, a⟩)
    obtain ⟨j, hj, hzj⟩ := exists_of_mem_familySites hz' (not_mem_recordedSites_of_mem_sites i a)
    exact ⟨j, hj, Finset.mem_union_right _ hzj⟩
theorem sites_subset_of_common_site (hΓ' : G.IsPairwiseFarApart Γ')
    (h1 : G.familyBadBonds Γ = G.familyBadBonds Γ') (h2 : G.familySites Γ = G.familySites Γ')
    {i j : G.GasSpin} (hi : i ∈ Γ) (hj : j ∈ Γ') {z : TorusSite (n * R.params.side)} (hz : z ∈ i.1.sites)
    (hzj : z ∈ j.1.sites) : ∀ w ∈ i.1.sites, w ∈ j.1.sites := by
  classical
  intro w hw
  have hJ := i.2.isCluster.2 z hz w hw
  have key : ∀ v, ChainConnected (10 * R.range) (clusterSupportSites R.params.side i.1) z v → v ∈ j.1.sites := by
    intro v hv
    induction hv with
    | refl => exact hzj
    | @tail c d _ hs ih =>
      obtain ⟨k, hk, hdk⟩ := exists_spin_of_mem_sites h1 h2 hi hs.2.1
      by_cases e : k = j
      · exact e ▸ hdk
      · have := hΓ' k hk j hj e d hdk c ih
        have h3 := hs.2.2
        rw [_root_.YangMills.Construction.TorusFields.supDist_comm] at h3
        omega
  exact key w hJ
theorem eq_of_common_site (hΓ : G.IsPairwiseFarApart Γ) {k j : G.GasSpin} (hk : k ∈ Γ) (hj : j ∈ Γ)
    {w : TorusSite (n * R.params.side)} (h1 : w ∈ k.1.sites) (h2 : w ∈ j.1.sites) : k = j := by
  by_contra e
  have := hΓ k hk j hj e w h1 w h2
  rw [supDist_self] at this
  omega
theorem mem_of_family_eq (hΓ : G.IsPairwiseFarApart Γ) (hΓ' : G.IsPairwiseFarApart Γ')
    (h1 : G.familyBadBonds Γ = G.familyBadBonds Γ') (h2 : G.familySites Γ = G.familySites Γ')
    {i : G.GasSpin} (hi : i ∈ Γ) : i ∈ Γ' := by
  classical
  obtain ⟨z, hz⟩ := i.2.isCluster.1
  obtain ⟨j, hj, hzj⟩ := exists_spin_of_mem_sites h1 h2 hi hz
  have s1 := sites_subset_of_common_site hΓ' h1 h2 hi hj hz hzj
  have s2 := sites_subset_of_common_site hΓ h1.symm h2.symm hj hi hzj hz
  have e1 : i.1.1 = j.1.1 := by
    ext b
    constructor
    · intro hb
      have hb' : b ∈ G.familyBadBonds Γ' :=
        h1 ▸ Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, hi, hb⟩)
      obtain ⟨k, hk, hbk⟩ := exists_of_mem_familyBadBonds hb' (not_mem_recordedBad_of_mem_bad i hb)
      rw [← eq_of_common_site hΓ' hk hj (fst_mem_sites_of_mem_bad k hbk)
        (s1 _ (fst_mem_sites_of_mem_bad i hb))]
      exact hbk
    · intro hb
      have hb' : b ∈ G.familyBadBonds Γ :=
        h1 ▸ Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, hj, hb⟩)
      obtain ⟨k, hk, hbk⟩ := exists_of_mem_familyBadBonds hb' (not_mem_recordedBad_of_mem_bad j hb)
      rw [← eq_of_common_site hΓ hk hi (fst_mem_sites_of_mem_bad k hbk)
        (s2 _ (fst_mem_sites_of_mem_bad j hb))]
      exact hbk
  have e2 : i.1.2 = j.1.2 := by
    ext w
    constructor
    · intro hw
      have hw' : w ∈ G.familySites Γ' :=
        h2 ▸ Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, hi, hw⟩)
      obtain ⟨k, hk, hwk⟩ := exists_of_mem_familySites hw' (not_mem_recordedSites_of_mem_sites i hw)
      rw [← eq_of_common_site hΓ' hk hj (Finset.mem_union_right _ hwk)
        (s1 _ (Finset.mem_union_right _ hw))]
      exact hwk
    · intro hw
      have hw' : w ∈ G.familySites Γ :=
        h2 ▸ Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, hj, hw⟩)
      obtain ⟨k, hk, hwk⟩ := exists_of_mem_familySites hw' (not_mem_recordedSites_of_mem_sites j hw)
      rw [← eq_of_common_site hΓ hk hi (Finset.mem_union_right _ hwk)
        (s2 _ (Finset.mem_union_right _ hw))]
      exact hwk
  have e : i = j := Subtype.ext (Prod.ext e1 e2)
  exact e ▸ hj
theorem caseAvoids_iff (A : Finset (TorusSite n)) :
    G.CaseAvoids A (G.familyBadBonds Γ) (G.familySites Γ) ↔ ∀ i ∈ Γ, ¬ i.1.Touches A := by
  classical
  constructor
  · rintro ⟨h1, h2⟩ i hi (⟨b, hb, hA⟩ | ⟨z, hz, hA⟩)
    · exact h1 b (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, hi, hb⟩))
        (not_mem_recordedBad_of_mem_bad i hb) hA
    · exact h2 z (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, hi, hz⟩))
        (not_mem_recordedSites_of_mem_sites i hz) hA
  · intro h
    refine ⟨fun c hc hn hA => ?_, fun z hz hn hA => ?_⟩
    · obtain ⟨i, hi, hb⟩ := exists_of_mem_familyBadBonds hc hn
      exact h i hi (Or.inl ⟨c, hb, hA⟩)
    · obtain ⟨i, hi, hzi⟩ := exists_of_mem_familySites hz hn
      exact h i hi (Or.inr ⟨z, hzi, hA⟩)
section Components
variable {m : ℕ} [NeZero m] {r : ℕ} {U : Finset (TorusSite m)}
open Classical in
theorem exists_component_mem {u : TorusSite m} (hu : u ∈ U) : ∃ X ∈ chainComponents r U, u ∈ X := by apply _root_.YangMills.Construction.TorusLumps.exists_mem_chainComponents <;> assumption
open Classical in
theorem component_eq_of_mem {X X' : Finset (TorusSite m)} (hX : X ∈ chainComponents r U)
    (hX' : X' ∈ chainComponents r U) {u : TorusSite m} (h : u ∈ X) (h' : u ∈ X') : X = X' := by
  rw [eq_filter_of_mem_chainComponents hX h, eq_filter_of_mem_chainComponents hX' h']
open Classical in
theorem lt_supDist_of_component_ne {X X' : Finset (TorusSite m)} (hX : X ∈ chainComponents r U)
    (hX' : X' ∈ chainComponents r U) (hne : X ≠ X') {u v : TorusSite m} (hu : u ∈ X) (hv : v ∈ X') :
    r < supDist u v := by exact _root_.YangMills.Construction.FarBlocks.lt_supDist_of_mem_chainComponents_of_ne hX hX' hne hu hv
end Components
open Classical in
theorem exists_family_of_coarseState_eq (hCs : FreeComponentsAreClusterSupports) {Z : Finset (TorusSite n)}
    (hZ : IsRetainedZone G Z) (hfar : 64 * R.params.side ≤ R.range) (hbig : 1 ≤ R.range)
    {bad : Finset (TorusBond (n * R.params.side))} {Yt : Finset (TorusSite (n * R.params.side))}
    {b : BaseChoice R.params.side n} {W : TorusField (n * R.params.side)} {ω : Yt → R.labels.Ω}
    (hbm : bad ⊆ markedBonds R G.cut) (hs : coarseStateOf R G.cut W Yt ω bad b = G.state) :
    ∃ Γ, G.IsPairwiseFarApart Γ ∧ bad = G.familyBadBonds Γ ∧ Yt = G.familySites Γ := by
  set U := bad.image Prod.fst ∪ Yt ∪ sitesInBlocks R.params.side G.cut with hU
  set Att := attachedSites R.params.side R.range bad Yt G.cut with hAtt
  set Z' := storedBlocks R.params.side R.range bad Yt G.cut with hZ'
  have hrec : ∀ y, G.state.markAt y =
      if y ∈ Z' then some (blockConfigAt R G.cut Z' W Yt ω bad b y) else none := fun y =>
    (congrArg (fun q => CoarseState.markAt q y) hs).symm.trans (markAt_coarseStateOf G.cut W Yt ω bad b y)
  have hZZ : Z' = Z := by
    ext y
    rw [← hZ.recorded_iff, hrec]
    by_cases h : y ∈ Z'
    · simp [h]
    · simp [h]
  have hcomp : ∀ X ∈ chainComponents (10 * R.range) U, (X ∩ sitesInBlocks R.params.side G.cut).Nonempty →
      ∀ u ∈ X, u ∈ Att := by
    intro X hX hm u hu
    exact Finset.mem_biUnion.mpr ⟨X, Finset.mem_filter.mpr ⟨hX, hm⟩, hu⟩
  have hnear : ∀ u ∈ U, parentBlock R.params.side u ∈ Z' → u ∈ Att := by
    intro u hu hb
    obtain ⟨X, hX, huX⟩ := exists_component_mem (r := 10 * R.range) hu
    rcases Finset.mem_union.mp hb with a | a
    · exact hcomp X hX ⟨u, Finset.mem_inter.mpr ⟨huX, Finset.mem_filter.mpr ⟨Finset.mem_univ _, a⟩⟩⟩ u huX
    · obtain ⟨p, hp⟩ := (Finset.mem_filter.mp a).2
      obtain ⟨hb', hw⟩ := Finset.mem_inter.mp hp
      obtain ⟨v, hv, hpv⟩ := (mem_thickening _ _ _).mp hw
      have e : parentBlock R.params.side p = parentBlock R.params.side u :=
        Finset.mem_singleton.mp (Finset.mem_filter.mp hb').2
      have h0 := supDist_le_of_parentBlock_eq R.params.side e
      have h1 := supDist_triangle u p v
      rw [_root_.YangMills.Construction.TorusFields.supDist_comm u p] at h1
      obtain ⟨X', hf, hvX⟩ := Finset.mem_biUnion.mp hv
      obtain ⟨hX', hm⟩ := Finset.mem_filter.mp hf
      by_cases e' : X = X'
      · exact hcomp X' hX' hm u (e' ▸ huX)
      · have := lt_supDist_of_component_ne hX hX' e' huX hvX
        omega
  have hAz : ∀ u ∈ Att, parentBlock R.params.side u ∈ Z' := fun u hu =>
    Finset.mem_union_right _ (parentBlock_mem_coreBlocks hu)
  have hbadiff : ∀ c, c ∈ G.recordedBad ↔ c ∈ bad ∧ c.1 ∈ Att := by
    intro c
    unfold GasGround.recordedBad
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hrec]
    constructor
    · rintro ⟨s, h1, h2⟩
      by_cases hy : parentBlock R.params.side c.1 ∈ Z'
      · rw [if_pos hy] at h1
        have := Option.some.inj h1
        subst this
        unfold blockConfigAt at h2
        simp only [decide_eq_true_eq, BlockZones.blockSite_parentBlock_siteOffset] at h2
        exact ⟨h2, hnear _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ h2))) hy⟩
      · rw [if_neg hy] at h1
        exact absurd h1 (by simp)
    · rintro ⟨h1, h2⟩
      refine ⟨_, if_pos (hAz _ h2), ?_⟩
      unfold blockConfigAt
      simp only [decide_eq_true_eq, BlockZones.blockSite_parentBlock_siteOffset]
      exact h1
  have hsiteiff : ∀ z, z ∈ G.recordedSites ↔ z ∈ Yt ∧ z ∈ Att := by
    intro z
    unfold GasGround.recordedSites CoarseState.labelAt
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hrec]
    constructor
    · intro h
      by_cases hy : parentBlock R.params.side z ∈ Z'
      · rw [if_pos hy] at h
        simp only [blockConfigAt, BlockZones.blockSite_parentBlock_siteOffset] at h
        have hz : z ∈ Yt := by
          by_contra hz
          simp [hz] at h
        exact ⟨hz, hnear _ (Finset.mem_union_left _ (Finset.mem_union_right _ hz)) hy⟩
      · rw [if_neg hy] at h
        simp at h
    · rintro ⟨hz, h2⟩
      rw [if_pos (hAz _ h2)]
      simp only [blockConfigAt, BlockZones.blockSite_parentBlock_siteOffset]
      simp [hz]
  have hatt : ∀ z ∈ G.anchorSites, z ∈ Att := by
    intro z hz
    unfold GasGround.anchorSites at hz
    rcases Finset.mem_union.mp hz with a | a
    · rcases Finset.mem_union.mp a with c | c
      · have hc : z ∈ sitesInBlocks R.params.side G.cut := c
        exact hnear z (Finset.mem_union_right _ hc)
          (Finset.mem_union_left _ (Finset.mem_filter.mp hc).2)
      · obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp c
        exact ((hbadiff c').mp hc').2
    · exact ((hsiteiff z).mp a).2
  set X₀ := (chainComponents (10 * R.range) U).filter
    fun X => ¬ (X ∩ sitesInBlocks R.params.side G.cut).Nonempty with hX₀
  have hoff : ∀ X ∈ X₀, ∀ u ∈ X, u ∉ Att := by
    intro X hX u hu hA
    obtain ⟨hXc, hn⟩ := Finset.mem_filter.mp hX
    obtain ⟨X', hf, huX⟩ := Finset.mem_biUnion.mp hA
    obtain ⟨hX', hm⟩ := Finset.mem_filter.mp hf
    exact hn (component_eq_of_mem hXc hX' hu huX ▸ hm)
  have hCl : ∀ X ∈ X₀, clusterSupportSites R.params.side (supportOfComponent R.params.side bad Yt X) = X ∧
      IsClusterSupport R.params.side R.range (supportOfComponent R.params.side bad Yt X) := by
    intro X hX
    obtain ⟨hXc, hn⟩ := Finset.mem_filter.mp hX
    exact hCs n R.params.side R.range bad Yt G.cut X hXc
      (Finset.disjoint_iff_inter_eq_empty.mpr (Finset.not_nonempty_iff_eq_empty.mp hn))
  have hsup : ∀ X ∈ X₀, G.IsGasSupport (supportOfComponent R.params.side bad Yt X) := by
    intro X hX
    obtain ⟨hXc, hn⟩ := Finset.mem_filter.mp hX
    refine ⟨(hCl X hX).2, fun c hc => ?_, fun z hz z' hz' => ?_⟩
    · obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hc
      refine Finset.mem_filter.mpr ⟨hbm h1, fun hst => hoff X hX c.1 h2 ?_⟩
      refine hnear c.1 (subset_of_mem_chainComponents hXc h2) ?_
      rw [hZZ]
      exact ((hZ.bond_iff c).mp hst).1
    · have hzX : z ∈ X := by
        have := (hCl X hX).1
        exact this ▸ hz
      obtain ⟨X', hf, hvX⟩ := Finset.mem_biUnion.mp (hatt z' hz')
      obtain ⟨hX', hm⟩ := Finset.mem_filter.mp hf
      exact lt_supDist_of_component_ne hXc hX' (fun e => hn (e ▸ hm)) hzX hvX
  set Γ : Finset G.GasSpin := X₀.attach.image
    fun X => (⟨supportOfComponent R.params.side bad Yt X.1, hsup X.1 X.2⟩ : G.GasSpin) with hΓ
  have hmemΓ : ∀ X (hX : X ∈ X₀), (⟨supportOfComponent R.params.side bad Yt X, hsup X hX⟩ : G.GasSpin) ∈ Γ :=
    fun X hX => Finset.mem_image.mpr ⟨⟨X, hX⟩, Finset.mem_attach _ _, rfl⟩
  have hcompOf : ∀ u ∈ U, u ∉ Att → ∃ X ∈ X₀, u ∈ X := by
    intro u hu hn
    obtain ⟨X, hX, huX⟩ := exists_component_mem (r := 10 * R.range) hu
    exact ⟨X, Finset.mem_filter.mpr ⟨hX, fun hm => hn (hcomp X hX hm u huX)⟩, huX⟩
  refine ⟨Γ, ?_, ?_, ?_⟩
  · intro i hi j hj hij z hz z' hz'
    obtain ⟨⟨X, hX⟩, -, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨⟨X', hX'⟩, -, rfl⟩ := Finset.mem_image.mp hj
    have hne : X ≠ X' := fun e => hij (by subst e; rfl)
    have h1 : z ∈ X := by
      have := (hCl X hX).1
      exact this ▸ hz
    have h2 : z' ∈ X' := by
      have := (hCl X' hX').1
      exact this ▸ hz'
    exact lt_supDist_of_component_ne (Finset.mem_filter.mp hX).1 (Finset.mem_filter.mp hX').1 hne h1 h2
  · ext c
    constructor
    · intro hc
      by_cases hA : c.1 ∈ Att
      · exact Finset.mem_union_left _ ((hbadiff c).mpr ⟨hc, hA⟩)
      · obtain ⟨X, hX, hcX⟩ := hcompOf c.1
          (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hc))) hA
        refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨_, hmemΓ X hX, ?_⟩)
        exact Finset.mem_filter.mpr ⟨hc, hcX⟩
    · intro hc
      rcases Finset.mem_union.mp hc with a | a
      · exact ((hbadiff c).mp a).1
      · obtain ⟨i, hi, hci⟩ := Finset.mem_biUnion.mp a
        obtain ⟨⟨X, hX⟩, -, rfl⟩ := Finset.mem_image.mp hi
        exact (Finset.mem_filter.mp hci).1
  · ext z
    constructor
    · intro hz
      by_cases hA : z ∈ Att
      · exact Finset.mem_union_left _ ((hsiteiff z).mpr ⟨hz, hA⟩)
      · obtain ⟨X, hX, hzX⟩ := hcompOf z (Finset.mem_union_left _ (Finset.mem_union_right _ hz)) hA
        refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨_, hmemΓ X hX, ?_⟩)
        exact Finset.mem_inter.mpr ⟨hz, hzX⟩
    · intro hz
      rcases Finset.mem_union.mp hz with a | a
      · exact ((hsiteiff z).mp a).1
      · obtain ⟨i, hi, hzi⟩ := Finset.mem_biUnion.mp a
        obtain ⟨⟨X, hX⟩, -, rfl⟩ := Finset.mem_image.mp hi
        exact (Finset.mem_inter.mp hzi).1
theorem recordedBad_subset_markedBonds (hG : G.IsAdmissibleGround) : G.recordedBad ⊆ markedBonds R G.cut := by
  classical
  rcases hG with hc | hh
  · obtain ⟨Z, hZ⟩ := exists_isAdmissibleZone G (Or.inl hc)
    intro c hc'
    exfalso
    have hst := (Finset.mem_filter.mp hc')
    have hq : G.state.markAt (parentBlock R.params.side c.1) = none := by
      unfold CoarseState.markAt
      rw [dif_neg]
      rw [hc.state_empty]
      simp
    obtain ⟨s, h1, -⟩ := hst.2
    rw [hq] at h1
    cases h1
  · obtain ⟨W', Y', ω', bad', b', hq, hm, hall, hbad, hs, hZ, hrec⟩ := exists_hot_data hh
    rw [hbad]
    exact hm
end StepGas.FamilyCases
namespace ClusterExpansionOfAStep
open StepGas.FamilyCases in
theorem groundCasesAreFamilies_of_supports (hCs : FreeComponentsAreClusterSupports)
    (hfloor : CouplingFloorExists) : GroundCasesAreFamilies := by
  classical
  intro T hT
  obtain ⟨y₁, hfloor⟩ := hfloor 1 (64 * T.side) T.rt one_pos
  refine ⟨y₁, fun y hy R hR hx' n _ G hG => ?_⟩
  have eL : R.params.side = T.side := by rw [hR.params_eq]; rfl
  have hfar : 64 * R.params.side ≤ R.range := by
    have := (hfloor R.coupling (hy.trans hR.le_coupling)).1
    rw [eL]
    exact this
  have hL1 : 1 ≤ R.params.side := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hbig : 1 ≤ R.range := by omega
  obtain ⟨Z, hZ⟩ := exists_isAdmissibleZone G hG
  refine ⟨fun Γ hΓ c hc => ?_, fun Γ Γ' hΓ hΓ' h1 h2 => ?_, fun Γ A _ => caseAvoids_iff A,
    fun bad Yt b W ν hbm _ hs => exists_family_of_coarseState_eq hCs hZ hfar hbig hbm hs⟩
  · rcases Finset.mem_union.mp hc with a | a
    · exact recordedBad_subset_markedBonds hG a
    · obtain ⟨i, hi, hci⟩ := Finset.mem_biUnion.mp a
      exact (Finset.mem_filter.mp (i.2.bad_subset_free hci)).1
  · ext i
    exact ⟨fun h => mem_of_family_eq hΓ hΓ' h1 h2 h, fun h => mem_of_family_eq hΓ' hΓ h1.symm h2.symm h⟩
end ClusterExpansionOfAStep
end YangMills.Construction
end
