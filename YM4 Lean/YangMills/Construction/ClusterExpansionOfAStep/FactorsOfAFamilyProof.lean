import YangMills.Construction.ClusterExpansionOfAStep.AllowedOfAWeightProof
import YangMills.Construction.ClusterExpansionOfAStep.ClustersOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.FactorsAtACaseProof
import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfACaseAtAStep
import YangMills.Construction.ClusterExpansionOfAStep.FamiliesOfSpins
import Mathlib
import YangMills.Construction.ClusterExpansionOfAStep.TestOfAFamily
import YangMills.Construction.ClusterExpansionOfAStep.ZonesOfAFamily
set_option autoImplicit false

noncomputable section
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages RenormalizationStepParameters StepSettings StepGas SpinFamilies TorusLumps TorusFields
def FamilyFactorization : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y →
    R.nextCoupling ≤ 1.01 * R.coupling →
    ∀ (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround →
      ∀ Γ, G.IsPairwiseFarApart Γ → ∀ c : FamilyState G Γ, (∀ i : Γ, G.IsAllowed i.1.1 (c i)) →
        0 ≤ (∏ X ∈ chainComponents R.nextRange G.state.1, coarseFactor G.coarse G.state X) ∧
          ∀ η, (G.familySetting c).InBalls η →
          (∏ X ∈ chainComponents R.range (G.familySetting c).support,
              R.clusterFactor (n * R.params.side) ((G.familySetting c).field η) (G.familySetting c).support
                (G.familySetting c).labelling X) *
            baseLaw (R := R) ((G.familySetting c).field η) (G.familySetting c).bases *
            G.remainingMarks (G.familySetting c).free (G.familyBadBonds Γ) ((G.familySetting c).field η) =
          (∏ X ∈ chainComponents R.nextRange G.state.1, coarseFactor G.coarse G.state X) *
            ∏ i : Γ, G.activity i.1.1 (c i)
end YangMills.Construction.ClusterExpansionOfAStep
end

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages LumpContours HoleSavings ColdStepAtMirrorFrames BlockZones SpinFamilies FamilyZones BlockTrees
  FamilyRestrictions TorusLumps TorusFields StepSettings StepGas StepCosts RenormalizationStepParameters TopLevelSites BlockPlaces
namespace FamilyFactors
section Bases
variable {n : ℕ} [NeZero n] {R : StepSetup}
theorem baseSitesAt_congr {F : BlockFrame} (J₀ : ℕ) {h h' : Finset (Finset (F.Site F.depth))} {y : F.Cell}
    (e : nearbyLumps h y = nearbyLumps h' y) : baseSitesAt J₀ h y = baseSitesAt J₀ h' y := by apply _root_.YangMills.Construction.InBoxTransfer.baseSitesAt_congr <;> assumption
theorem isBaseChoice_iff_forall_mem {F : BlockFrame} (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth)))
    (b : F.Cell → F.Site F.depth) :
    IsBaseChoice J₀ h b ↔ ∀ y, b y ∈ baseSitesAt J₀ h y := by apply _root_.YangMills.Construction.InBoxTransfer.isBaseChoice_iff <;> assumption
theorem mem_baseChoices_iff (W : TorusField (n * R.params.side)) (b : BaseChoice R.params.side n) :
    b ∈ baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W) ↔
      ∀ c, b c ∈ baseSitesAt R.params.baseDepth (stepHotLumps R.params W) c := by
  classical
  refine Iff.trans ?_ (isBaseChoice_iff_forall_mem R.params.baseDepth (stepHotLumps R.params W) b)
  exact ⟨fun h => (Finset.mem_filter.mp h).2, fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
open Classical in
theorem card_eq_prod_of_mem_iff {C S : Type} [Fintype C] [Fintype S] (A : Finset (C → S)) (B : C → Finset S)
    (h : ∀ b, b ∈ A ↔ ∀ c, b c ∈ B c) : A.card = ∏ c, (B c).card := by
  have : A = Fintype.piFinset B := by
    ext b
    rw [Fintype.mem_piFinset]
    exact h b
  rw [this, Fintype.card_piFinset]
theorem baseLaw_eq_prod (W : TorusField (n * R.params.side)) (b : BaseChoice R.params.side n)
    (hb : IsBaseChoice R.params.baseDepth (stepHotLumps R.params W) b) :
    baseLaw (R := R) W b = ∏ c : (stepBlockFrame R.params.side n).Cell,
      blockBaseWeight R.params (stepHotLumps R.params W) c (b c) := by
  classical
  have hmem : b ∈ baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩
  have hall := (isBaseChoice_iff_forall_mem _ _ _).mp hb
  have hcard := card_eq_prod_of_mem_iff _ _ (mem_baseChoices_iff (R := R) W)
  have h1 : baseLaw (R := R) W b =
      1 / ((baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W)).card : ℝ) := if_pos hmem
  have h2 : ∀ c, blockBaseWeight R.params (stepHotLumps R.params W) c (b c) =
      1 / ((baseSitesAt R.params.baseDepth (stepHotLumps R.params W) c).card : ℝ) := fun c => if_pos (hall c)
  rw [h1, hcard, Nat.cast_prod]
  simp only [h2, one_div]
  rw [Finset.prod_inv_distrib]
  rfl
theorem blockBaseWeight_eq_baseUniformWeight (hfit : R.params.Admissible) (hn : 0 < n)
    {W₁ W₂ : TorusField (n * R.params.side)} {b₁ b₂ : BaseChoice R.params.side n} {y : TorusSite n}
    (hb₂ : IsBaseChoice R.params.baseDepth (stepHotLumps R.params W₂) b₂)
    (hl : nearbyLumps (stepHotLumps R.params W₁) (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y) =
      nearbyLumps (stepHotLumps R.params W₂) (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y))
    (hc : b₁ (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y) =
      b₂ (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y)) :
    blockBaseWeight R.params (stepHotLumps R.params W₁) (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y)
      (b₁ (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y)) = baseUniformWeight W₂ b₂ y := by
  classical
  set e := torusSiteInFrame (stepBlockFrame R.params.side n) 1 y with he
  have hon : cellBlock R.params.side n e = y :=
    toTorusSite_torusSiteInFrame (fun k => stepBlockFrame_period_one k) y
  have hall := (isBaseChoice_iff_forall_mem _ _ _).mp hb₂
  have hAt : baseSitesAt R.params.baseDepth (stepHotLumps R.params W₁) e =
      baseSitesAt R.params.baseDepth (stepHotLumps R.params W₂) e := baseSitesAt_congr _ hl
  have hmem : b₂ ∈ baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W₂) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb₂⟩
  have hL : blockBaseWeight R.params (stepHotLumps R.params W₁) e (b₁ e) =
      1 / ((baseSitesAt R.params.baseDepth (stepHotLumps R.params W₂) e).card : ℝ) := by
    unfold blockBaseWeight
    rw [hAt, hc]
    exact if_pos (hall e)
  have hR : baseUniformWeight W₂ b₂ y = 1 / (((Finset.univ.filter fun o : BlockOffset R.params.side =>
      Function.update b₂ e (frameBlockSite R.params.side n y o) ∈
        baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W₂)).card : ℕ) : ℝ) :=
    if_pos hmem
  rw [hL, hR]
  have hcard : (Finset.univ.filter fun o : BlockOffset R.params.side =>
      Function.update b₂ e (frameBlockSite R.params.side n y o) ∈
        baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W₂)).card =
      (baseSitesAt R.params.baseDepth (stepHotLumps R.params W₂) e).card := by
    refine Finset.card_bij (fun o _ => frameBlockSite R.params.side n y o) ?_ ?_ ?_
    · intro o ho
      have h1 := (mem_baseChoices_iff W₂ _).mp (Finset.mem_filter.mp ho).2 e
      have h2 : Function.update b₂ e (frameBlockSite R.params.side n y o) e = frameBlockSite R.params.side n y o :=
        Function.update_self _ _ _
      exact h2 ▸ h1
    · intro o _ o' _ h
      exact frameBlockSite_injective y h
    · intro z hz
      have hcz := enclosingCell_of_mem_baseSitesAt hfit hn hz
      refine ⟨siteOffset (toTorusSite (F := stepBlockFrame R.params.side n) (j := 0) (n * R.params.side) z), ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mem_baseChoices_iff W₂ _).mpr ?_⟩
        have hs := eq_frameBlockSite_siteOffset hcz
        rw [hon] at hs
        intro c
        by_cases hce : c = e
        · rw [hce]
          have h2 : Function.update b₂ e (frameBlockSite R.params.side n y
              (siteOffset (toTorusSite (F := stepBlockFrame R.params.side n) (j := 0) (n * R.params.side) z))) e =
              frameBlockSite R.params.side n y
                (siteOffset (toTorusSite (F := stepBlockFrame R.params.side n) (j := 0) (n * R.params.side) z)) :=
            Function.update_self _ _ _
          have hz' : frameBlockSite R.params.side n y
              (siteOffset (toTorusSite (F := stepBlockFrame R.params.side n) (j := 0) (n * R.params.side) z)) ∈
              baseSitesAt R.params.baseDepth (stepHotLumps R.params W₂) e := hs ▸ hz
          exact h2.symm ▸ hz'
        · have h2 : Function.update b₂ e (frameBlockSite R.params.side n y
              (siteOffset (toTorusSite (F := stepBlockFrame R.params.side n) (j := 0) (n * R.params.side) z))) c =
              b₂ c := Function.update_of_ne hce _ _
          exact h2.symm ▸ hall c
      · have hs := eq_frameBlockSite_siteOffset hcz
        rw [hon] at hs
        exact hs.symm
  rw [hcard]
theorem nearbyLumps_trivialField (c : (stepBlockFrame R.params.side n).Cell) (hσ : 0 < R.params.threshold) :
    nearbyLumps (stepHotLumps R.params (trivialField (n * R.params.side))) c = ∅ := by
  classical
  unfold nearbyLumps stepHotLumps hotLumps
  apply Finset.filter_eq_empty_iff.mpr
  intro l hl
  exfalso
  obtain ⟨p, hp, -⟩ := Finset.mem_biUnion.mp hl
  obtain ⟨-, hhot⟩ := Finset.mem_filter.mp hp
  obtain ⟨p₀, μ, ν⟩ := p
  obtain ⟨p₁, rfl⟩ := torusSiteInFrame_surjective (stepBlockFrame R.params.side n) 0 stepBlockFrame_period_zero p₀
  have h1 : R.params.threshold ≤ curvature (trivialField (n * R.params.side)) p₁ μ ν :=
    le_of_le_of_eq hhot (plaquetteDefect_readAtLevel _ p₁ μ ν)
  have h2 : curvature (trivialField (n * R.params.side)) p₁ μ ν = 0 := by
    simp [curvature, holonomy_trivialField]
  linarith
theorem blockBaseWeight_eq_one {H : Finset (Finset ((stepBlockFrame R.params.side n).Site 0))}
    {e : (stepBlockFrame R.params.side n).Cell} {z : (stepBlockFrame R.params.side n).Site 0}
    (hno : nearbyLumps H e = ∅) (hz : z ∈ baseSitesAt R.params.baseDepth H e) :
    blockBaseWeight R.params H e z = 1 := by
  have hcard : (baseSitesAt R.params.baseDepth H e).card = 1 := by
    unfold baseSitesAt
    rw [if_pos (Or.inl hno)]
    exact Finset.card_singleton _
  unfold blockBaseWeight
  rw [if_pos hz, hcard]
  simp
theorem prod_cells_eq_prod_sites (f : (stepBlockFrame R.params.side n).Cell → ℝ) :
    ∏ c, f c = ∏ y : TorusSite n, f (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y) := by
  classical
  have hp : ∀ k, (stepBlockFrame R.params.side n).period 1 k = n := fun k => stepBlockFrame_period_one k
  refine (Fintype.prod_equiv (⟨fun y => torusSiteInFrame (stepBlockFrame R.params.side n) 1 y,
    fun c => cellBlock R.params.side n c,
    fun y => toTorusSite_torusSiteInFrame hp y, fun c => torusSiteInFrame_toTorusSite hp c⟩ :
      TorusSite n ≃ (stepBlockFrame R.params.side n).Cell) _ _ ?_).symm
  intro y
  rfl
open Classical in
theorem mem_chainComponents_of_separated {m : ℕ} [NeZero m] {r : ℕ} {Y Y₁ X : Finset (TorusSite m)} (hsub : Y₁ ⊆ Y)
    (hsep : ∀ u ∈ Y₁, ∀ v ∈ Y, v ∉ Y₁ → r < supDist u v) (hX : X ∈ chainComponents r Y₁) :
    X ∈ chainComponents r Y := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.WeightAdmissible.mem_chainComponents_of_separated_subset <;> assumption
theorem mem_gasFamily_sites {γ : GasFamily R n} {z : TorusSite (n * R.params.side)} :
    z ∈ γ.sites ↔ ∃ θ, γ.Occupies θ ∧ z ∈ θ.2 := by
  classical
  refine ⟨GasFamily.exists_of_mem_sites, fun ⟨θ, h, hz⟩ => ?_⟩
  unfold GasFamily.sites
  exact Finset.mem_biUnion.mpr ⟨θ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, hz⟩
end Bases
section Family
variable {R : StepSetup} {n : ℕ} [NeZero n] {G : GasGround R n} {Γ : Finset G.GasSpin} {Z : Finset (TorusSite n)}
  (c : FamilyState G Γ)
theorem single_state_familyData (i : Γ) (h : (G.familyData c).Occupies i.1.1) :
    GasFamily.single i.1.1 ((G.familyData c).state h) = GasFamily.single i.1.1 (c i) := by
  rw [state_familyData]
theorem occupies_familyData (i : Γ) : (G.familyData c).Occupies i.1.1 := (occupies_familyData_iff c).mpr ⟨i, rfl⟩
variable (hB : IsReadable G (G.familyData c))
include hB
theorem clusterFactor_familyData_eq (i : Γ) {X : Finset (TorusSite (n * R.params.side))}
    (hX : X ⊆ (G.settingOf (G.familyData c)).support) (hXθ : ∀ z ∈ X, z ∈ i.1.1.2) :
    R.clusterFactor (n * R.params.side) (G.frameField (G.familyData c)) (G.settingOf (G.familyData c)).support
        (G.settingOf (G.familyData c)).labelling X =
      R.clusterFactor (n * R.params.side) (G.frameField (GasFamily.single i.1.1 (c i)))
        (G.settingOf (GasFamily.single i.1.1 (c i))).support
        (G.settingOf (GasFamily.single i.1.1 (c i))).labelling X := by
  classical
  have hfar := hB.far
  have hbig := hB.big
  have h := occupies_familyData c i
  rw [← single_state_familyData c i h]
  have hX₁ : X ⊆ (G.settingOf (GasFamily.single i.1.1 ((G.familyData c).state h))).support := fun z hz =>
    Finset.mem_union_right _ ((mem_sites_single_iff _).mpr (hXθ z hz))
  refine hB.hasExpansions.2.reads_class (n * R.params.side) hB.blockSide _ _ _ _ _ _ X hX hX₁ ?_ ?_
  · intro b hb _
    have ag := agreeNear_single_of_mem_sites hB h (x := b.1) (d := 1) (mem_sites_of_mem_snd i.1.1 (hXθ _ hb))
      (by rw [supDist_self]; omega)
    exact frameField_eq_of_agreeNear (side_odd hB) hB.two_le ag b.2 (by rw [supDist_self])
  · intro w hw hw' hwX
    have ag := agreeNear_single_of_mem_sites hB h (x := w) (d := 0) (mem_sites_of_mem_snd i.1.1 (hXθ _ hwX))
      (by rw [supDist_self]; omega)
    exact labelling_congr _ _ fun θ' hθ => ag θ' w (by rw [supDist_self])
      (parentBlock_mem_core θ' (mem_sites_of_mem_snd θ' hθ) (by rw [supDist_self]; omega))
theorem bondMark_familyData_eq (i : Γ) {b : TorusBond (n * R.params.side)} (hst : b ∈ i.1.1.coreBonds) :
    bondMark R G.coarse (G.frameField (G.familyData c)) b =
      bondMark R G.coarse (G.frameField (GasFamily.single i.1.1 (c i))) b := by
  have hfar := hB.far
  have hbig := hB.big
  have h := occupies_familyData c i
  rw [← single_state_familyData c i h]
  have ag := agreeNear_single_of_mem_core hB h (v := b.1) (x := b.1) (d := R.params.side + 3)
    (Finset.mem_filter.mp hst).2.1 (by rw [supDist_self]; omega)
  unfold bondMark
  rw [chartCoord_eq_of_agreeNear (side_odd hB) hB.two_le ag]
theorem nearbyLumps_familyData_eq (i : Γ) {y : TorusSite n} (hy : y ∈ i.1.1.core) :
    nearbyLumps (stepHotLumps R.params (G.frameField (G.familyData c)))
        (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y) =
      nearbyLumps (stepHotLumps R.params (G.frameField (GasFamily.single i.1.1 (c i))))
        (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y) := by
  have h := occupies_familyData c i
  rw [← single_state_familyData c i h]
  exact nearbyLumps_eq_single hB h hy
theorem bases_familyData_eq (i : Γ) {y : TorusSite n} (hy : y ∈ i.1.1.core) :
    (G.settingOf (G.familyData c)).bases (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y) =
      (G.settingOf (GasFamily.single i.1.1 (c i))).bases (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y) := by
  have hfar := hB.far
  have h := occupies_familyData c i
  rw [← single_state_familyData c i h]
  refine bases_settingOf_congr fun θ' hθ' => ?_
  obtain ⟨v, hv⟩ : ∃ v : TorusSite (n * R.params.side), parentBlock R.params.side v = y :=
    ⟨blockSite y (fun _ => 0), parentBlock_blockSite _ _⟩
  have ag := agreeNear_single_of_mem_core hB h (x := v) (d := 0) (v := v) (by rw [hv]; exact hy)
    (by rw [supDist_self]; omega)
  exact ag θ' v (by rw [supDist_self]) (by rw [hv]; exact hθ')
theorem mem_recordedSites_or_exists {z : TorusSite (n * R.params.side)}
    (hz : z ∈ (G.settingOf (G.familyData c)).support) :
    z ∈ G.recordedSites ∨ ∃ i : Γ, z ∈ i.1.1.2 := by
  rcases Finset.mem_union.mp hz with a | a
  · exact Or.inl a
  · obtain ⟨θ, h, hz⟩ := mem_gasFamily_sites.mp a
    obtain ⟨i, rfl⟩ := (occupies_familyData_iff c).mp h
    exact Or.inr ⟨i, hz⟩
open Classical in
theorem chainComponents_support_eq :
    chainComponents R.range (G.settingOf (G.familyData c)).support =
      chainComponents R.range G.recordedSites ∪
        (Finset.univ : Finset Γ).biUnion fun i => chainComponents R.range i.1.1.2 := by
  ext X
  simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · intro hX
    obtain ⟨z, hz⟩ := exists_mem_of_mem_chainComponents hX
    rcases mem_recordedSites_or_exists c hB (subset_of_mem_chainComponents hX hz) with a | ⟨i, a⟩
    · left
      have := (mem_chainComponents_recorded hB hX hz a).1
      rwa [support_settingOf_empty] at this
    · right
      exact ⟨i, (mem_chainComponents_single hB (occupies_familyData c i) hX hz a).1⟩
  · rintro (hX | ⟨i, hX⟩)
    · refine mem_chainComponents_of_separated (Y₁ := G.recordedSites) Finset.subset_union_left
        (fun u hu v hv hn => ?_) hX
      rcases Finset.mem_union.mp hv with b | b
      · exact absurd b hn
      · obtain ⟨θ, h, hvθ⟩ := mem_gasFamily_sites.mp b
        rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
        exact range_lt_supDist_recorded hB h hvθ hu
    · refine mem_chainComponents_of_separated (Y₁ := i.1.1.2)
        (fun w hw => Finset.mem_union_right _ (mem_gasFamily_sites.mpr ⟨_, occupies_familyData c i, hw⟩))
        (fun u hu v hv hn => ?_) hX
      rcases Finset.mem_union.mp hv with b | b
      · exact range_lt_supDist_recorded hB (occupies_familyData c i) hu b
      · obtain ⟨θ', h', hvθ⟩ := mem_gasFamily_sites.mp b
        exact range_lt_supDist_of_ne hB (occupies_familyData c i) h' (fun e => hn (e ▸ hvθ)) hu hvθ
open Classical in
theorem markedBonds_sdiff_free_eq (hZ : IsRetainedZone G Z) (hsep : (G.familyData c).CoresDisjoint) :
    markedBonds R G.cut \ (G.familySetting c).free =
      (markedBonds R G.cut ∩ bondsOverBlocks R.params.side Z) ∪
        (Finset.univ : Finset Γ).biUnion fun i => i.1.1.coreBonds ∩ markedBonds R G.cut := by
  ext β
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hm, hnf⟩
    by_cases hst : G.IsRecorded β
    · exact Or.inl ⟨hm, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hZ.bond_iff β).mp hst⟩⟩
    · by_cases hj : ∃ j : Γ, β ∈ j.1.1.coreBonds
      · obtain ⟨j, hj⟩ := hj
        exact Or.inr ⟨j, hj, hm⟩
      · exact absurd ((mem_free_familySetting_iff c hsep).mpr ⟨hm, hst, fun j h => hj ⟨j, h⟩⟩) hnf
  · rintro (⟨hm, hb⟩ | ⟨j, hj, hm⟩)
    · refine ⟨hm, fun hf => ((mem_free_familySetting_iff c hsep).mp hf).2.1 ?_⟩
      exact (hZ.bond_iff β).mpr (Finset.mem_filter.mp hb).2
    · exact ⟨hm, fun hf => ((mem_free_familySetting_iff c hsep).mp hf).2.2 j hj⟩
theorem mem_familyBadBonds_iff (hZ : IsRetainedZone G Z) (i : Γ) {β : TorusBond (n * R.params.side)}
    (hst : β ∈ i.1.1.coreBonds) :
    β ∈ G.familyBadBonds Γ ↔ β ∈ i.1.1.1 := by
  classical
  have hfar := hB.far
  constructor
  · intro h
    rcases Finset.mem_union.mp h with a | a
    · exfalso
      obtain ⟨u, hu, hd⟩ := FamilyZones.exists_site_near_of_mem_core (Finset.mem_filter.mp hst).2.1
      have hat : β.1 ∈ G.anchorSites := by
        unfold GasGround.anchorSites
        exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ a))
      have := i.1.2.far_from_anchor u hu _ hat
      rw [_root_.YangMills.Construction.TorusFields.supDist_comm] at hd
      omega
    · obtain ⟨j, hj, hb⟩ := Finset.mem_biUnion.mp a
      by_cases e : j = i.1
      · exact e ▸ hb
      · exfalso
        obtain ⟨u, hu, hd⟩ := FamilyZones.exists_site_near_of_mem_core (Finset.mem_filter.mp hst).2.1
        have := hB.isFamily.2 i.1.1 j.1 (occupies_familyData c i) ((occupies_familyData_iff c).mpr ⟨⟨j, hj⟩, rfl⟩)
          (fun h => e (Subtype.ext h.symm)) u hu β.1 (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hb))
        rw [_root_.YangMills.Construction.TorusFields.supDist_comm] at hd
        omega
  · intro h
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i.1, i.2, h⟩)
theorem nearbyLumps_eq_empty (hZ : IsRetainedZone G Z)
    (hull0 : IsHullState R.params R.range (G.frameField (G.familyData c)) (G.settingOf (G.familyData c)).support)
    {y : TorusSite n} (h1 : y ∉ Z) (h2 : ∀ i : Γ, y ∉ i.1.1.core) :
    nearbyLumps (stepHotLumps R.params (G.frameField (G.familyData c)))
      (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y) = ∅ := by
  classical
  have hfar := hB.far
  have hbig := hB.big
  have hsub := nearbyLumps_mono (side_odd hB) hB.two_le (G.frameField (G.familyData c)) (trivialField _) y
    (fun x₁ p₁ μ ν hμν hc' hd hs => by
      exfalso
      have hl : torusLumpOf R.params x₁ ∈ torusHotLumps R.params (G.frameField (G.familyData c)) :=
        (mem_torusHotLumps_iff R.params hB.admissible (side_dvd hB) _ _).mpr ⟨p₁, μ, ν, hμν, hs, x₁, hc', rfl⟩
      have hs' : x₁ ∈ torusHotSites R.params (G.frameField (G.familyData c)) := by
        simp only [torusHotSites, Finset.mem_biUnion, id_eq]
        exact ⟨_, hl, mem_torusLumpOf_self x₁⟩
      have hY := hull0.1 ((mem_thickening _ _ _).mpr ⟨x₁, hs', by rw [supDist_self]; omega⟩)
      obtain ⟨v, hv⟩ : ∃ v : TorusSite (n * R.params.side), parentBlock R.params.side v = y :=
        ⟨blockSite _ (fun _ => 0), parentBlock_blockSite _ _⟩
      have h3 := FamilyRestrictions.supDist_le_four_mul hv hd
      have h4 : supDist v x₁ ≤ 4 * R.range := by
        rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
        omega
      rcases mem_recordedSites_or_exists c hB hY with a | ⟨i, a⟩
      · apply h1
        rw [hZ.zone_eq, ← hv]
        refine Finset.mem_union_right _ (parentBlock_mem_coreBlocks_of_near ?_ h4)
        unfold GasGround.anchorSites
        exact Finset.mem_union_right _ a
      · apply h2 i
        rw [← hv]
        exact parentBlock_mem_coreBlocks_of_near (Finset.mem_union_right _ a) h4)
  have hf := nearbyLumps_trivialField (R := R) (n := n) (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y)
    hB.admissible.σ_pos
  exact Finset.subset_empty.mp (hf ▸ hsub)
set_option maxHeartbeats 2000000 in
open Classical in
theorem frameFactors_eq (hZ : IsRetainedZone G Z) (hsep : (G.familyData c).CoresDisjoint)
    (hall : ∀ i : Γ, G.IsAllowed i.1.1 (c i))
    (hull0 : IsHullState R.params R.range (G.frameField (G.familyData c)) (G.settingOf (G.familyData c)).support)
    (hb : IsBaseChoice R.params.baseDepth (stepHotLumps R.params (G.frameField (G.familyData c)))
      (G.settingOf (G.familyData c)).bases) :
    (∏ X ∈ chainComponents R.range (G.settingOf (G.familyData c)).support,
        R.clusterFactor (n * R.params.side) (G.frameField (G.familyData c))
        (G.settingOf (G.familyData c)).support (G.settingOf (G.familyData c)).labelling X) *
      baseLaw (R := R) (G.frameField (G.familyData c)) (G.settingOf (G.familyData c)).bases *
      G.remainingMarks (G.familySetting c).free (G.familyBadBonds Γ) (G.frameField (G.familyData c)) =
    ((∏ X ∈ chainComponents R.range G.recordedSites, R.clusterFactor (n * R.params.side) (G.frameField (G.familyData c))
        (G.settingOf (G.familyData c)).support (G.settingOf (G.familyData c)).labelling X) *
      (∏ β ∈ markedBonds R G.cut ∩ bondsOverBlocks R.params.side Z,
        if β ∈ G.familyBadBonds Γ then 1 - bondMark R G.coarse (G.frameField (G.familyData c)) β
        else bondMark R G.coarse (G.frameField (G.familyData c)) β) *
      ∏ y ∈ Z, blockBaseWeight R.params (stepHotLumps R.params (G.frameField (G.familyData c)))
        (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y)
        ((G.settingOf (G.familyData c)).bases (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y))) *
      ∏ i : Γ, G.activity i.1.1 (c i) := by
  have hfar := hB.far
  have hbig := hB.big
  have hcore : ∀ i : Γ, ∀ y ∈ i.1.1.core, y ∉ Z := fun i y hy => not_mem_zone_of_mem_core hZ hfar i.1 hy
  have hdisj : ∀ i j : Γ, i ≠ j → ∀ y, y ∈ i.1.1.core → y ∈ j.1.1.core → False := by
    intro i j e y h1 h2
    exact e (Subtype.ext (Subtype.ext (hsep _ _ (occupies_familyData c i) (occupies_familyData c j) y h1 h2)))
  have eΦ : (∏ X ∈ chainComponents R.range (G.settingOf (G.familyData c)).support,
        R.clusterFactor (n * R.params.side) (G.frameField (G.familyData c))
        (G.settingOf (G.familyData c)).support (G.settingOf (G.familyData c)).labelling X) =
      (∏ X ∈ chainComponents R.range G.recordedSites, R.clusterFactor (n * R.params.side)
        (G.frameField (G.familyData c))
        (G.settingOf (G.familyData c)).support (G.settingOf (G.familyData c)).labelling X) *
      ∏ i : Γ, ∏ X ∈ chainComponents R.range i.1.1.2, R.clusterFactor (n * R.params.side)
        (G.frameField (GasFamily.single i.1.1 (c i)))
        (G.settingOf (GasFamily.single i.1.1 (c i))).support
        (G.settingOf (GasFamily.single i.1.1 (c i))).labelling X := by
    rw [chainComponents_support_eq c hB, Finset.prod_union, Finset.prod_biUnion]
    · refine congrArg (fun t => _ * t) ?_
      refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun X hX => ?_
      refine clusterFactor_familyData_eq c hB i (fun z hz => Finset.mem_union_right _
        (mem_gasFamily_sites.mpr ⟨_, occupies_familyData c i, subset_of_mem_chainComponents hX hz⟩))
        fun z hz => subset_of_mem_chainComponents hX hz
    · intro i _ j _ e
      refine Finset.disjoint_left.mpr fun X h1 h2 => ?_
      obtain ⟨z, hz⟩ := exists_mem_of_mem_chainComponents h1
      have a1 := subset_of_mem_chainComponents h1 hz
      have a2 := subset_of_mem_chainComponents h2 hz
      exact hdisj i j e _ (parentBlock_mem_core _ (mem_sites_of_mem_snd _ a1) (by rw [supDist_self]; omega))
        (parentBlock_mem_core _ (mem_sites_of_mem_snd _ a2) (by rw [supDist_self]; omega))
    · refine Finset.disjoint_left.mpr fun X h1 h2 => ?_
      obtain ⟨i, -, h3⟩ := Finset.mem_biUnion.mp h2
      obtain ⟨z, hz⟩ := exists_mem_of_mem_chainComponents h1
      exact not_mem_recordedSites_of_mem_sites i.1 (subset_of_mem_chainComponents h3 hz)
        (subset_of_mem_chainComponents h1 hz)
  have eM : G.remainingMarks (G.familySetting c).free (G.familyBadBonds Γ) (G.frameField (G.familyData c)) =
      (∏ β ∈ markedBonds R G.cut ∩ bondsOverBlocks R.params.side Z,
        if β ∈ G.familyBadBonds Γ then 1 - bondMark R G.coarse (G.frameField (G.familyData c)) β
        else bondMark R G.coarse (G.frameField (G.familyData c)) β) *
      ∏ i : Γ, G.supportMarks i.1.1 (G.frameField (GasFamily.single i.1.1 (c i))) := by
    unfold GasGround.remainingMarks
    rw [markedBonds_sdiff_free_eq c hB hZ hsep, Finset.prod_union, Finset.prod_biUnion]
    · refine congrArg (fun t => _ * t) ?_
      refine Finset.prod_congr rfl fun i _ => ?_
      unfold GasGround.supportMarks
      refine Finset.prod_congr rfl fun β hβ => ?_
      have hst := (Finset.mem_inter.mp hβ).1
      by_cases hbad : β ∈ i.1.1.1
      · rw [if_pos hbad, if_pos ((mem_familyBadBonds_iff c hB hZ i hst).mpr hbad), bondMark_familyData_eq c hB i hst]
      · rw [if_neg hbad, if_neg fun h => hbad ((mem_familyBadBonds_iff c hB hZ i hst).mp h),
          bondMark_familyData_eq c hB i hst]
    · intro i _ j _ e
      refine Finset.disjoint_left.mpr fun β h1 h2 => ?_
      exact hdisj i j e _ (Finset.mem_filter.mp (Finset.mem_inter.mp h1).1).2.1
        (Finset.mem_filter.mp (Finset.mem_inter.mp h2).1).2.1
    · refine Finset.disjoint_left.mpr fun β h1 h2 => ?_
      obtain ⟨i, -, h3⟩ := Finset.mem_biUnion.mp h2
      exact hcore i _ (Finset.mem_filter.mp (Finset.mem_inter.mp h3).1).2.1
        (Finset.mem_filter.mp (Finset.mem_inter.mp h1).2).2.1
  have eB : baseLaw (R := R) (G.frameField (G.familyData c)) (G.settingOf (G.familyData c)).bases =
      (∏ y ∈ Z, blockBaseWeight R.params (stepHotLumps R.params (G.frameField (G.familyData c)))
        (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y)
        ((G.settingOf (G.familyData c)).bases (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y))) *
      ∏ i : Γ, ∏ y ∈ i.1.1.core, baseUniformWeight (G.frameField (GasFamily.single i.1.1 (c i)))
        (G.settingOf (GasFamily.single i.1.1 (c i))).bases y := by
    rw [baseLaw_eq_prod _ _ hb, prod_cells_eq_prod_sites]
    have hU : ∏ y : TorusSite n, blockBaseWeight R.params (stepHotLumps R.params (G.frameField (G.familyData c)))
          (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y)
          ((G.settingOf (G.familyData c)).bases (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y)) =
        ∏ y ∈ Z ∪ (Finset.univ : Finset Γ).biUnion (fun i => i.1.1.core),
          blockBaseWeight R.params (stepHotLumps R.params (G.frameField (G.familyData c)))
          (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y)
          ((G.settingOf (G.familyData c)).bases (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y)) := by
      symm
      refine Finset.prod_subset (Finset.subset_univ _) fun y _ hy => ?_
      have h1 : y ∉ Z := fun h => hy (Finset.mem_union_left _ h)
      have h2 : ∀ i : Γ, y ∉ i.1.1.core := fun i h =>
        hy (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, h⟩))
      exact blockBaseWeight_eq_one (nearbyLumps_eq_empty c hB hZ hull0 h1 h2)
        ((isBaseChoice_iff_forall_mem _ _ _).mp hb _)
    rw [hU, Finset.prod_union, Finset.prod_biUnion]
    · refine congrArg (fun t => _ * t) ?_
      refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun y hy => ?_
      exact blockBaseWeight_eq_baseUniformWeight hB.admissible (by have := hB.two_le; omega)
        (isBaseChoice_of_baseUniformWeight_ne_zero ((hall i).2.2.2 y hy)) (nearbyLumps_familyData_eq c hB i hy)
        (bases_familyData_eq c hB i hy)
    · intro i _ j _ e
      exact Finset.disjoint_left.mpr fun y h1 h2 => hdisj i j e y h1 h2
    · refine Finset.disjoint_left.mpr fun y h1 h2 => ?_
      obtain ⟨i, -, h3⟩ := Finset.mem_biUnion.mp h2
      exact hcore i y h3 h1
  rw [eΦ, eM, eB]
  unfold GasGround.activity
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring
end Family
section Reduce
variable {R : StepSetup} {n : ℕ} [NeZero n]
open Classical in
theorem mem_stepHotLumps_iff (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (W : TorusField (n * ℓ.side))
    (l : Finset ((stepBlockFrame ℓ.side n).Site 0)) :
    l ∈ stepHotLumps ℓ W ↔ l.image (toTorusSite (n * ℓ.side)) ∈ torusHotLumps ℓ W := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.CoarseFactors.mem_stepHotLumps_iff <;> assumption
theorem baseLaw_congr_torusHotLumps {W W' : TorusField (n * R.params.side)}
    (h : torusHotLumps R.params W = torusHotLumps R.params W') (b : BaseChoice R.params.side n) :
    baseLaw (R := R) W b = baseLaw (R := R) W' b := by
  classical
  have e : stepHotLumps R.params W = stepHotLumps R.params W' := by
    ext l
    rw [mem_stepHotLumps_iff, mem_stepHotLumps_iff, h]
  have h2 : baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W) =
      baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W') := by
    show (Finset.univ.filter fun b => IsBaseChoice R.params.baseDepth (stepHotLumps R.params W) b) =
      Finset.univ.filter fun b => IsBaseChoice R.params.baseDepth (stepHotLumps R.params W') b
    rw [e]
  unfold baseLaw
  rw [h2]
theorem cutoffFactor_le_one {ρ : ℝ} {p : ℝ → ℝ} (hc : IsCutoff ρ p) {u : ℝ} (hu : 0 ≤ u) :
    cutoffFactor ρ p u ≤ 1 := by
  unfold cutoffFactor
  split_ifs with h
  · have hρ : 0 < ρ := lt_of_le_of_lt hu h
    have hp : 0 ≤ p u := by
      by_cases h1 : u ≤ 5 * ρ / 8
      · rw [hc.vanish_small u hu h1]
      · push Not at h1
        have ht : 0 < 5 * ρ / 8 := by positivity
        have hup : 0 < u := ht.trans h1
        have hconv := hc.convex.2 (Set.mem_Ico.mpr ⟨le_rfl, hρ⟩ : (0 : ℝ) ∈ Set.Ico 0 ρ)
          (Set.mem_Ico.mpr ⟨hu, h⟩ : u ∈ Set.Ico 0 ρ) (sub_nonneg.mpr ((div_le_one hup).mpr h1.le))
          (by positivity : 0 ≤ 5 * ρ / 8 / u) (by ring : 1 - 5 * ρ / 8 / u + 5 * ρ / 8 / u = 1)
        have e : (1 - 5 * ρ / 8 / u) • (0 : ℝ) + (5 * ρ / 8 / u) • u = 5 * ρ / 8 := by
          simp only [smul_eq_mul, mul_zero, zero_add]
          field_simp
        rw [e, hc.vanish_small _ ht.le le_rfl, hc.vanish_small 0 le_rfl ht.le] at hconv
        simp only [smul_eq_mul, mul_zero, zero_add] at hconv
        exact nonneg_of_mul_nonneg_right hconv (by positivity)
    exact Real.exp_le_one_iff.mpr (by linarith)
  · exact zero_le_one
theorem bondMark_le_one (hc : IsCutoff R.ballRadius R.barrierFn) (V : TorusField n)
    (W : TorusField (n * R.params.side)) (b : TorusBond (n * R.params.side)) :
    bondMark R V W b ≤ 1 := cutoffFactor_le_one hc (norm_nonneg _)
theorem labelSet_state_eq {G : GasGround R n} : G.state.labelSet = G.recordedSites := by
  classical
  ext z
  unfold CoarseState.labelSet GasGround.recordedSites
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rcases h : G.state.labelAt z with u | a
  · simp
  · simp
theorem markedZone_state_eq {G : GasGround R n} {Z : Finset (TorusSite n)} (hZ : IsRetainedZone G Z) :
    G.state.markedZone = Z := by
  classical
  ext y
  unfold CoarseState.markedZone
  rw [Finset.mem_filter, ← hZ.recorded_iff]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    by_contra hn
    unfold CoarseState.markAt at h
    rw [dif_neg hn] at h
    simp at h
end Reduce
end FamilyFactors
set_option maxHeartbeats 1000000 in
open FamilyFactors in
theorem familyFactorization_holds (hCf : GasConfigIsAdmissibleSetting) (hGw : GroundWeightAtEmpty)
    (hTe : FamilyRecoversState) (hFc : CaseFactorProductStatement) (hH : CoarseHullIsHullState)
    (hf1 : CouplingFloorExists) :
    FamilyFactorization := by
  classical
  intro T hT
  obtain ⟨y₁, hCf⟩ := hCf T hT
  obtain ⟨y₂, hGw⟩ := hGw T hT
  obtain ⟨y₃, hTe⟩ := hTe T hT
  obtain ⟨y₄, hf1⟩ := hf1 1 (2 ^ 40 * T.side + 2 ^ 17) T.rt one_pos
  refine ⟨max y₁ (max y₂ (max y₃ (max y₄ T.floorMin))), fun y hy R hR hx' n _ G hG Γ hΓ c hall => ?_⟩
  have b₁ : y₁ ≤ y := le_trans (by simp) hy
  have b₂ : y₂ ≤ y := le_trans (by simp) hy
  have b₃ : y₃ ≤ y := le_trans (by simp) hy
  have b₄ : y₄ ≤ y := le_trans (by simp) hy
  have b₅ : T.floorMin ≤ y := le_trans (by simp) hy
  have hx := hR.le_coupling
  have hfit : R.params.Admissible := by rw [hR.params_eq]; exact hT.fits y b₅
  have eL : R.params.side = T.side := by rw [hR.params_eq]; rfl
  have hrange := (hf1 R.coupling (b₄.trans hx)).1
  have hrr : R.range = clusterRange R.coupling := rfl
  have hL1 : 1 ≤ R.params.side := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hblock : 2 ^ 40 * R.params.side ≤ R.range := by
    rw [eL, hrr]
    omega
  have hbig : 2 ^ 16 ≤ R.range := by
    rw [hrr]
    omega
  have hfar : 64 * R.params.side ≤ R.range := by omega
  have hn₀ : R.params.n₀ ≤ n := by
    rcases hG with g | g
    · exact g.n₀_le
    · exact (Nat.le_mul_of_pos_left _ hL1).trans g.isBlockSide.2
  have hn2 : 2 ≤ n := by
    have := hfit.n₀_ge
    omega
  have hside : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Dvd.intro_left n rfl, by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ hn₀⟩
  have hB : IsReadable G (G.familyData c) :=
    { isFamily := ⟨fun θ h => by
        obtain ⟨i, rfl⟩ := (occupies_familyData_iff c).mp h
        exact i.1.2, fun θ θ' h h' e => by
        obtain ⟨i, rfl⟩ := (occupies_familyData_iff c).mp h
        obtain ⟨j, rfl⟩ := (occupies_familyData_iff c).mp h'
        exact hΓ i.1 i.2 j.1 j.2 fun h => e (congrArg Subtype.val h)⟩
      admissible := hfit, hasExpansions := hR.isStep.1, blockSide := hside, two_le := hn2, far := hfar, big := hbig
      groundWeight := hGw y b₂ R hR hx' n G hG
      exists_zone := exists_isAdmissibleZone G hG }
  obtain ⟨Z, hZ⟩ := exists_isAdmissibleZone G hG
  have hsep := coresDisjoint_familyData hΓ (by omega) c
  have hset : (G.familySetting c).IsAdmissible := by
    have h := hCf y b₁ R hR hx' n G hG (valuesOn (S := fun i : G.GasSpin => G.SpinState i) Γ
      fun i => ⟨c i, hall i⟩) (isAdmissible_valuesOn hΓ _)
    rwa [familyOf_valuesOn] at h
  have hin0 : (G.familySetting c).InBalls 0 := fun b => by
    have hρ : 0 ≤ R.ballRadius := by
      have := hfit.σ_pos
      unfold StepSetup.ballRadius
      positivity
    simpa [coordNorm, norm_toImaginary, Pi.zero_apply] using hρ
  have hz := field_zero_settingOf (G := G) (γ := G.familyData c) hfit.L_odd hn2
  have hull0 : IsHullState R.params R.range (G.frameField (G.familyData c)) (G.settingOf (G.familyData c)).support := by
    rw [← hz]
    exact hset.isHull 0 hin0
  have hb : IsBaseChoice R.params.baseDepth (stepHotLumps R.params (G.frameField (G.familyData c)))
      (G.settingOf (G.familyData c)).bases := hset.isBaseChoice
  have split := frameFactors_eq c hB hZ hsep hall hull0 hb
  have hcut : IsCutoff R.ballRadius R.barrierFn := by
    have e : R.ballRadius = T.ballRadius := by
      show R.params.threshold / 64 = T.threshold / 64
      rw [show R.params.threshold = T.threshold by rw [hR.params_eq]; rfl]
    rw [e, hR.barrierFn_eq]
    exact hT.cut
  have hPhi : (∏ X ∈ chainComponents R.nextRange G.state.1, coarseFactor G.coarse G.state X) =
      (∏ X ∈ chainComponents R.range G.recordedSites, R.clusterFactor (n * R.params.side)
        (G.frameField (G.familyData c))
        (G.settingOf (G.familyData c)).support (G.settingOf (G.familyData c)).labelling X) *
      (∏ β ∈ markedBonds R G.cut ∩ bondsOverBlocks R.params.side Z,
        if β ∈ G.familyBadBonds Γ then 1 - bondMark R G.coarse (G.frameField (G.familyData c)) β
        else bondMark R G.coarse (G.frameField (G.familyData c)) β) *
      ∏ y ∈ Z, blockBaseWeight R.params (stepHotLumps R.params (G.frameField (G.familyData c)))
        (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y)
        ((G.settingOf (G.familyData c)).bases (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y)) := by
    rcases hG with hc | hh
    · have hstore : ∀ y, G.state.markAt y = none := by
        intro y
        unfold CoarseState.markAt
        rw [dif_neg]
        rw [hc.state_empty]
        simp
      have hsites : G.recordedSites = ∅ := by
        unfold GasGround.recordedSites CoarseState.labelAt
        simp [hstore]
      have hZe : Z = ∅ := by
        ext y
        rw [← hZ.recorded_iff, hstore]
        simp
      have hcl : ∀ r : ℕ, chainComponents r (∅ : Finset (TorusSite (n * R.params.side))) = ∅ := fun r => by
        unfold chainComponents
        simp
      have hcl' : chainComponents R.nextRange G.state.1 = ∅ := by
        rw [hc.state_empty]
        unfold chainComponents
        simp
      have hbo : bondsOverBlocks R.params.side (∅ : Finset (TorusSite n)) = ∅ := by
        unfold bondsOverBlocks
        simp
      rw [hsites, hZe, hcl, hcl', hbo]
      simp
    · obtain ⟨W₁, Y₁, ω₁, bad₁, b₁', hq₁, -, -, -, -, -, -⟩ := exists_hot_data hh
      have hRC : R.ReadsCaseTests :=
        { hasExpansions := hR.isStep.1, admissible := hfit, range_le := hR.isStep.2.2, nextRange_ge := by
            have := hR.isStep.2.2
            omega, range_ge_side := hblock }
      have hq : IsHullState R.params R.nextRange G.coarse G.state.1 := by
        have := hH R.params hfit R.range R.nextRange hR.isStep.2.2 (by
          have := hR.isStep.2.2
          omega) n hh.isBlockSide.1 G.coarse bad₁ Y₁
        rw [← hq₁, hh.cut_eq]
        exact this
      have hνm : ∀ z : G.state.unlabelled (G.familySites Γ), z.1 ∈ (G.familySetting c).support := fun z => by
        rw [support_familySetting]
        exact (Finset.mem_filter.mp z.2).1
      set ν : G.state.unlabelled (G.familySites Γ) → R.labels.Ω :=
        fun z => (G.familySetting c).labelling ⟨z.1, hνm z⟩ with hν
      have hνc : ∀ (i : Γ) (z : TorusSite (n * R.params.side)) (hz : z ∈ i.1.1.2)
          (hr : z ∈ G.state.unlabelled (G.familySites Γ)), ν ⟨z, hr⟩ = (c i).2.1 ⟨z, hz⟩ := by
        intro i z hz hr
        have hzs : z ∈ (G.familyData c).sites := mem_gasFamily_sites.mpr ⟨_, occupies_familyData c i, hz⟩
        show (G.settingWithFamily (G.familyData c)).labelling ⟨z, _⟩ = _
        simp only [GasGround.settingWithFamily]
        rw [dif_pos hzs, GasFamily.labelAt_eq_of_mem _ hsep hzs (occupies_familyData c i) hz, state_familyData]
      have hte := hTe y b₃ R hR hx' n G (Or.inr hh) Γ hΓ c hall 0 hin0 ν hνc
      have hsig := familySites_fillLabels_eq c ν hsep hνc
      have hst : coarseStateOf R G.cut (G.frameField (G.familyData c)) (G.settingOf (G.familyData c)).support
          (G.settingOf (G.familyData c)).labelling (G.familyBadBonds Γ) (G.settingOf (G.familyData c)).bases =
          G.state := by
        have h1 := congrArg (fun p : Σ Y : Finset (TorusSite (n * R.params.side)), Y → R.labels.Ω =>
          coarseStateOf R G.cut (G.frameField (G.familyData c)) p.1 p.2 (G.familyBadBonds Γ)
            (G.settingOf (G.familyData c)).bases) hsig
        refine h1.symm.trans ?_
        rw [← hz]
        exact hte
      have hbm : G.familyBadBonds Γ ⊆ markedBonds R G.cut := by
        intro β hβ
        rcases Finset.mem_union.mp hβ with a | a
        · obtain ⟨_, _, _, bad₂, _, _, hm, _, hbad, _⟩ := exists_hot_data hh
          rw [hbad] at a
          exact hm a
        · obtain ⟨i, hi, hci⟩ := Finset.mem_biUnion.mp a
          exact (Finset.mem_filter.mp (i.2.bad_subset_free hci)).1
      have hcase := hFc R hRC n hh.isBlockSide G.coarse G.state (G.frameField (G.familyData c))
        (G.settingOf (G.familyData c)).support (G.settingOf (G.familyData c)).labelling (G.familyBadBonds Γ)
        (G.settingOf (G.familyData c)).bases hq (hh.cut_eq ▸ hbm) hull0 hb (hh.cut_eq ▸ hst)
      rw [labelSet_state_eq, markedZone_state_eq hZ, ← hh.cut_eq] at hcase
      exact hcase
  refine ⟨?_, fun η hin => ?_⟩
  · rw [hPhi]
    refine mul_nonneg (mul_nonneg (Finset.prod_nonneg fun X _ =>
      hR.isStep.1.2.factor_nonneg _ hside _ _ _ _)
      (Finset.prod_nonneg fun β _ => ?_)) (Finset.prod_nonneg fun y _ => ?_)
    · have h0 : 0 ≤ bondMark R G.coarse (G.frameField (G.familyData c)) β := by
        unfold bondMark cutoffFactor
        split_ifs
        · exact (Real.exp_pos _).le
        · exact le_rfl
      have h1 := bondMark_le_one hcut G.coarse (G.frameField (G.familyData c)) β
      split_ifs
      · linarith
      · exact h0
    · unfold blockBaseWeight
      split_ifs
      · positivity
      · exact le_rfl
  · have hnf : ∀ b : TorusBond (n * R.params.side), b.1 ∈ (G.familySetting c).support →
        b ∉ (G.familySetting c).free := by
      intro b hbY hbf
      have h1 := hset.far_from_support b hbf b.1 (Finset.mem_union_left _ hbY)
      rw [supDist_self] at h1
      omega
    have e1 : (∏ X ∈ chainComponents R.range (G.familySetting c).support,
        R.clusterFactor (n * R.params.side) ((G.familySetting c).field η) (G.familySetting c).support
          (G.familySetting c).labelling X) =
        ∏ X ∈ chainComponents R.range (G.settingOf (G.familyData c)).support,
          R.clusterFactor (n * R.params.side) (G.frameField (G.familyData c))
          (G.settingOf (G.familyData c)).support (G.settingOf (G.familyData c)).labelling X := by
      refine Finset.prod_congr rfl fun X hX => ?_
      refine hR.isStep.1.2.reads_class (n * R.params.side) hside _ _ _ _ _ _ X (subset_of_mem_chainComponents hX)
        (subset_of_mem_chainComponents hX) ?_ ?_
      · intro b hb1 _
        exact field_of_not_mem_free (hnf b (subset_of_mem_chainComponents hX hb1))
      · intro z _ _ _
        rfl
    have e2 : baseLaw (R := R) ((G.familySetting c).field η) (G.familySetting c).bases =
        baseLaw (R := R) (G.frameField (G.familyData c)) (G.settingOf (G.familyData c)).bases :=
      baseLaw_congr_torusHotLumps (hset.hotLumps_eq η hin) _
    have e3 : G.remainingMarks (G.familySetting c).free (G.familyBadBonds Γ) ((G.familySetting c).field η) =
        G.remainingMarks (G.familySetting c).free (G.familyBadBonds Γ) (G.frameField (G.familyData c)) := by
      unfold GasGround.remainingMarks
      refine Finset.prod_congr rfl fun β hβ => ?_
      have hnb := (Finset.mem_sdiff.mp hβ).2
      have key : bondMark R G.coarse ((G.familySetting c).field η) β =
          bondMark R G.coarse (G.frameField (G.familyData c)) β := by
        unfold bondMark
        have := chartCoord_field_of_not_mem_free (s := G.familySetting c) hset.subset_chart hfit.L_odd hn2 η hnb
        exact congrArg (fun w => cutoffFactor R.ballRadius R.barrierFn ‖((w : imaginaryQuaternions) : ℍ[ℝ]) -
          ((frameCoord R.params R.anchorRadius R.depth R.frameReach G.coarse β : imaginaryQuaternions) : ℍ[ℝ])‖) this
      rw [key]
    rw [e1, e2, e3, split, hPhi]
end YangMills.Construction.ClusterExpansionOfAStep
end
