import YangMills.Construction.CellOfTheFlow.TheStepGivenItsStateIsTheGas
import YangMills.Construction.ClusterExpansionOfAStep.AZeroFactorKillsTheState
import YangMills.Construction.ClusterExpansionOfAStep.AttachedClustersOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.ClassesOfTheGas
import YangMills.Construction.ClusterExpansionOfAStep.ClustersOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.HullStatesAreGrounds
import YangMills.Construction.ClusterExpansionOfAStep.ImageStateIsAGas
import YangMills.Construction.ClusterExpansionOfAStep.RatiosOfXi
import YangMills.Construction.FreeEnergiesOfTheFlow.ExpansionAlongTheFlow
import YangMills.Construction.FreeEnergiesOfTheFlow.StateOfAStepIsBorelProof
import YangMills.Construction.ResponseInTheExpansion.BoundedFunctionsOfTheCasesAreIntegrable
import YangMills.Construction.ResponseInTheExpansion.CaseMassWithAFunctionIsBorelForm
import YangMills.Construction.ResponseInTheExpansion.CaseMeanIsAMeanOfTheGas
import YangMills.Construction.ResponseInTheExpansion.MassAlongTheLevelsProof
import YangMills.Construction.ResponseInTheExpansion.MeansGivenAStateAreMeansOverItsCases
import YangMills.Construction.ResponseInTheExpansion.StatesAlongTheChainAreBorel
import YangMills.Construction.ResponseInTheExpansion.TheDrawBelowHasItsLaw
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.CellWindows
open StepGas StepSettings TorusLumps TorusFields WeightedResponses RenormalizationStepParameters FreeEnergies ClusterExpansionOfAStep ResponseInTheExpansion
namespace StepGivenState
section Classes
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem chainConnected_mono {r : ℕ} {Y Y' : Finset (TorusSite n)} (h : Y ⊆ Y') {y z : TorusSite n}
    (hj : ChainConnected r Y y z) : ChainConnected r Y' y z := by
  induction hj with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.tail ⟨h hs.1, h hs.2.1, hs.2.2⟩
def AnchorReachesCut (G : GasGround R n) : Prop :=
  ∀ z ∈ G.anchorSites, ∃ u ∈ sitesInBlocks R.params.side G.cut, ChainConnected (10 * R.range) G.anchorSites z u
variable (G : GasGround R n)
private abbrev configSites (σ : G.Config) : Finset (TorusSite (n * R.params.side)) :=
  G.recordedSites ∪ (G.familyOf σ).sites
private abbrev configClusters (σ : G.Config) : Finset (TorusSite (n * R.params.side)) :=
  clusterSites (L := R.params.side) (G.badBondsOf σ) (configSites G σ) G.cut
private theorem mem_configClusters {σ : G.Config} {z : TorusSite (n * R.params.side)} :
    z ∈ configClusters G σ ↔ z ∈ G.anchorSites ∨ ∃ θ, (G.familyOf σ).Occupies θ ∧ z ∈ θ.sites := by
  classical
  constructor
  · intro h
    rcases Finset.mem_union.mp h with h | h
    · rcases Finset.mem_union.mp h with h | h
      · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp h
        rcases Finset.mem_union.mp hc with hc | hc
        · exact Or.inl (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hc)))
        · obtain ⟨θ, hθ, hcθ⟩ := Finset.mem_biUnion.mp hc
          exact Or.inr ⟨θ, (Finset.mem_filter.mp hθ).2,
            Finset.mem_union_left _ (Finset.mem_image_of_mem _ hcθ)⟩
      · rcases Finset.mem_union.mp h with h | h
        · exact Or.inl (Finset.mem_union_right _ h)
        · obtain ⟨θ, hθ, hz⟩ := GasFamily.exists_of_mem_sites h
          exact Or.inr ⟨θ, hθ, Finset.mem_union_right _ hz⟩
    · exact Or.inl (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  · rintro (h | ⟨θ, hθ, hz⟩)
    · rcases Finset.mem_union.mp h with h | h
      · rcases Finset.mem_union.mp h with h | h
        · exact Finset.mem_union_right _ h
        · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp h
          exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _
            (Finset.mem_union_left _ hc)))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_union_left _ h))
    · rcases Finset.mem_union.mp hz with h | h
      · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp h
        exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _
          (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
            ⟨θ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hθ⟩, hc⟩))))
      · refine Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_union_right _ ?_))
        exact Finset.mem_biUnion.mpr ⟨θ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hθ⟩, h⟩
private theorem isGasSupport_of_occupies {σ : G.Config} {θ : GasSupport R n} (h : (G.familyOf σ).Occupies θ) :
    G.IsGasSupport θ := by
  obtain ⟨j, rfl, -⟩ := G.exists_spin_of_occupies h
  exact j.2
private theorem farApart_of_occupies {σ : G.Config} (hadm : G.pairConstraint.IsAdmissible σ) {θ θ' : GasSupport R n}
    (h : (G.familyOf σ).Occupies θ) (h' : (G.familyOf σ).Occupies θ') (hne : θ ≠ θ') : θ.FarApart θ' := by
  obtain ⟨j, rfl, hj⟩ := G.exists_spin_of_occupies h
  obtain ⟨j', rfl, hj'⟩ := G.exists_spin_of_occupies h'
  rcases hadm j j' (fun e => hne (congrArg Subtype.val e)) with e | e | e
  · exact absurd e hj
  · exact absurd e hj'
  · exact e
private theorem eq_of_mem_sites_of_occupies {σ : G.Config} (hadm : G.pairConstraint.IsAdmissible σ) {θ θ' : GasSupport R n}
    (h : (G.familyOf σ).Occupies θ) (h' : (G.familyOf σ).Occupies θ') {z : TorusSite (n * R.params.side)}
    (hz : z ∈ θ.sites) (hz' : z ∈ θ'.sites) : θ = θ' := by
  by_contra hne
  have := farApart_of_occupies G hadm h h' hne z hz z hz'
  rw [supDist_self] at this
  omega
private theorem not_mem_anchorSites {σ : G.Config} {θ : GasSupport R n} (h : (G.familyOf σ).Occupies θ)
    {z : TorusSite (n * R.params.side)} (hz : z ∈ θ.sites) : z ∉ G.anchorSites := fun hz' => by
  have := (isGasSupport_of_occupies G h).far_from_anchor z hz z hz'
  rw [supDist_self] at this
  omega
private theorem mem_sites_of_chainConnected {σ : G.Config} (hadm : G.pairConstraint.IsAdmissible σ) {θ : GasSupport R n}
    (h : (G.familyOf σ).Occupies θ) {z w : TorusSite (n * R.params.side)} (hz : z ∈ θ.sites)
    (hj : ChainConnected (10 * R.range) (configClusters G σ) z w) : w ∈ θ.sites := by
  induction hj with
  | refl => exact hz
  | tail _ hs ih =>
    obtain ⟨-, hb, hd⟩ := hs
    rcases (mem_configClusters G).mp hb with hb | ⟨θ', h', hb⟩
    · have := (isGasSupport_of_occupies G h).far_from_anchor _ ih _ hb
      omega
    · by_cases e : θ = θ'
      · exact e ▸ hb
      · have := farApart_of_occupies G hadm h h' e _ ih _ hb
        omega
private theorem sites_mem_chainComponents {σ : G.Config} (hadm : G.pairConstraint.IsAdmissible σ) {θ : GasSupport R n}
    (h : (G.familyOf σ).Occupies θ) : θ.sites ∈ chainComponents (10 * R.range) (configClusters G σ) := by
  obtain ⟨y, hy⟩ := (isGasSupport_of_occupies G h).isCluster.1
  have hsub : θ.sites ⊆ configClusters G σ := fun u hu => (mem_configClusters G).mpr (Or.inr ⟨θ, h, hu⟩)
  obtain ⟨X, hX, hyX⟩ := exists_mem_chainComponents (r := 10 * R.range) (hsub hy)
  have e : X = θ.sites := by
    ext w
    constructor
    · intro hw
      exact mem_sites_of_chainConnected G hadm h hy (chainConnected_of_mem_chainComponents hX hyX hw)
    · intro hw
      exact mem_of_chainConnected_of_mem_chainComponents hX hyX (hsub hw)
        (chainConnected_mono hsub ((isGasSupport_of_occupies G h).isCluster.2 y hy w hw))
  rwa [e] at hX
private theorem supportOfComponent_sites {σ : G.Config} (hadm : G.pairConstraint.IsAdmissible σ) {θ : GasSupport R n}
    (h : (G.familyOf σ).Occupies θ) :
    supportOfComponent R.params.side (G.badBondsOf σ) (configSites G σ) θ.sites = θ := by
  classical
  refine Prod.ext ?_ ?_
  · ext c
    simp only [supportOfComponent, Finset.mem_filter]
    constructor
    · rintro ⟨hc, hs⟩
      rcases Finset.mem_union.mp hc with hc | hc
      · exact absurd (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hc)))
          (not_mem_anchorSites G h hs)
      · obtain ⟨θ', hθ', hcθ⟩ := Finset.mem_biUnion.mp hc
        have h' := (Finset.mem_filter.mp hθ').2
        have e := eq_of_mem_sites_of_occupies G hadm h h' hs
          (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hcθ))
        exact e ▸ hcθ
    · intro hc
      exact ⟨Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨θ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, hc⟩),
        Finset.mem_union_left _ (Finset.mem_image_of_mem _ hc)⟩
  · ext z
    simp only [supportOfComponent, Finset.mem_inter]
    constructor
    · rintro ⟨hz, hs⟩
      rcases Finset.mem_union.mp hz with hz | hz
      · exact absurd (Finset.mem_union_right _ hz) (not_mem_anchorSites G h hs)
      · obtain ⟨θ', h', hzθ⟩ := GasFamily.exists_of_mem_sites hz
        have e := eq_of_mem_sites_of_occupies G hadm h h' hs (Finset.mem_union_right _ hzθ)
        exact e ▸ hzθ
    · intro hz
      refine ⟨Finset.mem_union_right _ ?_, Finset.mem_union_right _ hz⟩
      exact Finset.mem_biUnion.mpr ⟨θ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, hz⟩
theorem mem_freeSupports_iff_occupies (hat : AnchorReachesCut G) {σ : G.Config} (hadm : G.pairConstraint.IsAdmissible σ)
    (θ : GasSupport R n) :
    θ ∈ freeSupports R G.cut (G.badBondsOf σ) (configSites G σ) ↔ (G.familyOf σ).Occupies θ := by
  classical
  unfold freeSupports
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨X, ⟨hX, hfree⟩, rfl⟩
    have hX' : X ∈ chainComponents (10 * R.range) (configClusters G σ) := hX
    obtain ⟨y, hy, hXy⟩ := mem_chainComponents.mp hX'
    have hyX : y ∈ X := by
      rw [hXy]
      exact Finset.mem_filter.mpr ⟨hy, Relation.ReflTransGen.refl⟩
    rcases (mem_configClusters G).mp hy with hA | ⟨θ', h', hs⟩
    · exfalso
      obtain ⟨u, hu, hj⟩ := hat y hA
      have hsub : G.anchorSites ⊆ configClusters G σ := fun v hv => (mem_configClusters G).mpr (Or.inl hv)
      have huX : u ∈ X := mem_of_chainConnected_of_mem_chainComponents hX' hyX
        (hsub (chainConnected_mem hA hj)) (chainConnected_mono hsub hj)
      exact hfree ⟨u, Finset.mem_inter.mpr ⟨huX, hu⟩⟩
    · have e : X = θ'.sites := eq_of_chainConnected_of_mem_chainComponents hX'
        (sites_mem_chainComponents G hadm h') hyX hs Relation.ReflTransGen.refl
      rw [e, supportOfComponent_sites G hadm h']
      exact h'
  · intro h
    refine ⟨θ.sites, ⟨sites_mem_chainComponents G hadm h, ?_⟩, supportOfComponent_sites G hadm h⟩
    rintro ⟨u, hu⟩
    obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hu
    exact not_mem_anchorSites G h h1 (Finset.mem_union_left _ (Finset.mem_union_left _ h2))
private theorem occupies_iff (σ : G.Config) (θ : GasSupport R n) :
    (G.familyOf σ).Occupies θ ↔ ∃ i : G.GasSpin, i.1 = θ ∧ σ i ≠ Sum.inl () := by
  classical
  refine ⟨G.exists_spin_of_occupies, ?_⟩
  rintro ⟨⟨θ, hθ⟩, rfl, hi⟩
  unfold GasFamily.Occupies GasGround.familyOf
  simp only [dif_pos hθ]
  rcases hv : σ ⟨θ, hθ⟩ with u | s
  · exact absurd (by rw [hv]) hi
  · rfl
theorem anchorReachesCut_of_isHotCase {G : GasGround R n} (h : G.IsHotCase) : AnchorReachesCut G := by
  classical
  obtain ⟨W, Yt, ωt, bad, b, hq, -, -, hall, -⟩ := h.exists_state
  have hbad : G.recordedBad = bad := by
    ext c
    have key : c ∈ G.recordedBad ↔ c ∈ G.state.storedBadBonds := by
      simp [GasGround.recordedBad, mem_storedBadBonds]
    rw [key, ← hq, mem_storedBadBonds_coarseStateOf]
    refine ⟨And.left, fun hc => ⟨hc, parentBlock_mem_storedBlocks R.range bad Yt G.cut
      (hall (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hc)))⟩⟩
  have hsites : G.recordedSites = Yt := by
    ext z
    have key : z ∈ G.recordedSites ↔ z ∈ G.state.labelSet := by
      rw [mem_labelSet]
      simp only [GasGround.recordedSites, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hv : G.state.labelAt z with u | a
      · simp
      · simp
    rw [key, ← hq, mem_labelSet_coarseStateOf]
    exact ⟨And.left, fun hz => ⟨hz, parentBlock_mem_storedBlocks R.range bad Yt G.cut
      (hall (Finset.mem_union_right _ hz))⟩⟩
  have hatt : G.anchorSites = clusterSites (L := R.params.side) bad Yt G.cut := by
    unfold GasGround.anchorSites
    rw [hbad, hsites]
    ext z
    simp only [Finset.mem_union]
    tauto
  intro z hz
  rw [hatt] at hz ⊢
  have hza : z ∈ attachedSites R.params.side R.range bad Yt G.cut := by
    rcases Finset.mem_union.mp hz with h1 | h1
    · exact hall h1
    · exact sitesInBlocks_subset_attachedSites R.range bad Yt G.cut h1
  obtain ⟨X, hX, hzX, u, hu⟩ := (mem_attachedSites_iff R.range bad Yt G.cut).mp hza
  obtain ⟨hu1, hu2⟩ := Finset.mem_inter.mp hu
  exact ⟨u, hu2, chainConnected_of_mem_chainComponents hX hzX hu1⟩
end Classes
section Gas
variable {R : StepSetup} {n : ℕ} [NeZero n]
open Classical in
def allSupportsFree (R : StepSetup) {n : ℕ} [NeZero n] (Θ : Finset (ClusterSupport R.params.side n))
    (C : Finset (TorusSite n)) (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) : ℝ :=
  if Θ ⊆ freeSupports R C bad Yt then 1 else 0
theorem measurableSet_supportsPresent (G : GasGround R n) {off : G.GasSpin → Prop} {z : G.GasSpin → ℝ}
    (h : G.pairConstraint.IsActivityBounded (G.referenceMeasureOff off) G.weight z)
    (Θ : Finset (ClusterSupport R.params.side n)) :
    MeasurableSet (supportsPresent G Θ) := by
  classical
  have e : supportsPresent G Θ = ⋂ θ ∈ Θ, ⋃ i ∈ (Finset.univ.filter fun i : G.GasSpin => i.1 = θ),
      {σ : G.Config | σ i = Sum.inl ()}ᶜ := by
    ext σ
    simp only [supportsPresent, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion, Finset.mem_filter,
      Finset.mem_univ, true_and, Set.mem_compl_iff, exists_prop]
  rw [e]
  refine Finset.measurableSet_biInter _ fun θ _ => Finset.measurableSet_biUnion _ fun i _ => ?_
  exact ((measurable_pi_apply i) (h.measurableSet_vacant i)).compl
open Classical in
theorem allSupportsFree_eq_indicator (G : GasGround R n) (hat : AnchorReachesCut G) {σ : G.Config}
    (hadm : G.pairConstraint.IsAdmissible σ) (Θ : Finset (ClusterSupport R.params.side n)) :
    allSupportsFree R Θ G.cut (G.badBondsOf σ) (configSetting G σ).support =
      (supportsPresent G Θ).indicator 1 σ := by
  have hiff : Θ ⊆ freeSupports R G.cut (G.badBondsOf σ) (configSetting G σ).support ↔
      σ ∈ supportsPresent G Θ := by
    constructor
    · intro h θ hθ
      exact (occupies_iff G σ θ).mp ((mem_freeSupports_iff_occupies G hat hadm θ).mp (h hθ))
    · intro h θ hθ
      exact (mem_freeSupports_iff_occupies G hat hadm θ).mpr ((occupies_iff G σ θ).mpr (h θ hθ))
  unfold allSupportsFree
  by_cases hs : σ ∈ supportsPresent G Θ
  · rw [if_pos (hiff.mpr hs), Set.indicator_of_mem hs]
    rfl
  · rw [if_neg fun h => hs (hiff.mp h), Set.indicator_of_notMem hs]
theorem gasExpectation_allSupportsFree (G : GasGround R n) (hat : AnchorReachesCut G)
    (hae : ∀ᵐ σ ∂G.gibbsLaw ∅, G.pairConstraint.IsAdmissible σ ∧ 0 < ∫ η, chartDensity (configSetting G σ) η)
    (Θ : Finset (ClusterSupport R.params.side n)) (hm : MeasurableSet (supportsPresent G Θ)) :
    gasExpectationOfCase G (fun _ Yt _ bad _ => allSupportsFree R Θ G.cut bad Yt) =
      (G.gibbsLaw ∅).real (supportsPresent G Θ) := by
  unfold gasExpectationOfCase GasGround.expectation
  have e : (fun σ => weightedMean (chartDensity (configSetting G σ)) fun η =>
      allSupportsFree R Θ G.cut (G.badBondsOf σ) (configSetting G σ).support) =ᵐ[G.gibbsLaw ∅]
        (supportsPresent G Θ).indicator 1 := by
    filter_upwards [hae] with σ hσ
    obtain ⟨hadm, hpos⟩ := hσ
    unfold weightedMean
    rw [integral_const_mul, mul_div_assoc, div_self hpos.ne', mul_one]
    exact allSupportsFree_eq_indicator G hat hadm Θ
  rw [integral_congr_ae e, integral_indicator_one hm]
end Gas
section Fibres
variable {X : Type} [MeasurableSpace X]
private theorem measurableSet_sigma_fst_eq {A : Type} {β : A → Type} [∀ a, MeasurableSpace (β a)] (a : A) :
    MeasurableSet {z : Sigma β | z.1 = a} := by apply _root_.YangMills.SharedProofs.p1937 <;> assumption
private theorem measurable_of_measurableSet_fibres {D Z : Type} [Countable D] [MeasurableSpace Z] (f : X → D)
    (hf : ∀ d, MeasurableSet {x | f x = d}) (G : D → X → Z) (hG : ∀ d, Measurable (G d)) :
    Measurable fun x => G (f x) x := by apply _root_.YangMills.SharedProofs.p23008 <;> assumption
end Fibres
private theorem isWellPosed_of_onParameters {T : ParameterAssignment} (hT : T.Admissible) {y : ℝ} (hy₀ : T.floorMin ≤ y)
    (hy₁ : 1 ≤ y) {R : StepSetup} (hon : R.OnParameters T y) (hmoved : |R.nextCoupling - R.coupling| ≤ 2 * T.B)
    (hArr : R.IsSymmetricWeight)
    (hF : T.FloorConditions (2 ^ 40 * T.side + 4 * T.n₀ + 2 ^ 17) 1 R.coupling) : R.IsWellPosed := by apply _root_.YangMills.SharedProofs.p3707 <;> assumption
end StepGivenState
open StepGivenState in
open Classical in
theorem stepGivenStateIsGas_proof (hM : ResponseInTheExpansion.conditionalMeanIsCaseMeanStatement)
    (hCM₀ : WeightedResponses.caseMeanEqGasMeanStatement)
    (hBI : WeightedResponses.boundedCaseFunctionIntegrableStatement)
    (hCB : ResponseInTheExpansion.ConfigurationMassMeasurability) (hCol₀ : ClusterExpansionOfAStep.GasColumnsSmall)
    (hRat : ClusterExpansionOfAStep.PartitionRatioBounds) (hImg₀ : StepSettings.coarseStateGasStatement)
    (hGr₀ : StepGas.HullStateIsHotCase) (hZ : ClusterExpansionOfAStep.CoarseWeightZeroOfFactorZero)
    (hHull : TorusLumps.CoarseHullIsHullState) (hSt : ResponseInTheExpansion.StageStatesMeasurableStatement)
    (hD : WeightedResponses.forgetLastStepStatement) (hRow : FreeEnergies.expansionAlongFlow)
    (hFl : StepFloors.EventuallyFloorConditions) :
    stepGivenStateIsGasStatement := by
  obtain ⟨r1, hr1, hCol⟩ := hCol₀
  obtain ⟨r2, hr2, hImg⟩ := hImg₀
  obtain ⟨r3, hr3, hCM⟩ := hCM₀
  intro a ha
  obtain ⟨L₀, r0, hr0, hM₀⟩ := hM a ha
  refine ⟨L₀, fun c => min (r0 c) (min (r1 c) (min (r2 c) (r3 c))),
    fun c => lt_min (hr0 c) (lt_min (hr1 c) (lt_min (hr2 c) (hr3 c))), fun L hodd hL Tb h1 h2 hTb hrt => ?_⟩
  obtain ⟨y0, hy0⟩ := hM₀ L hodd hL Tb h1 h2 hTb (hrt.trans (min_le_left _ _))
  obtain ⟨y1, hy1⟩ := hCol Tb hTb (hrt.trans ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨y2, hy2⟩ := hImg Tb hTb
    (hrt.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  obtain ⟨y3, hy3⟩ := hCM Tb hTb
    (hrt.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  obtain ⟨y4, hy4⟩ := hGr₀ Tb hTb
  have hCpos : (0 : ℝ) < 2 ^ 40 * Tb.side + 4 * Tb.n₀ + 2 ^ 17 := by positivity
  obtain ⟨y5, hy5⟩ := hFl Tb hTb _ 1 hCpos one_pos
  refine ⟨max y0 (max y1 (max y2 (max y3 (max y4 (max y5 (max Tb.floorMin 1)))))),
    fun y hyy hret hwil T β j hst m _ hb Θ A hA => ?_⟩
  obtain ⟨e0, hyy⟩ := max_le_iff.mp hyy
  obtain ⟨e1, hyy⟩ := max_le_iff.mp hyy
  obtain ⟨e2, hyy⟩ := max_le_iff.mp hyy
  obtain ⟨e3, hyy⟩ := max_le_iff.mp hyy
  obtain ⟨e4, hyy⟩ := max_le_iff.mp hyy
  obtain ⟨e5, hyy⟩ := max_le_iff.mp hyy
  obtain ⟨e6, e7⟩ := max_le_iff.mp hyy
  have hMM := hy0 y e0 hret hwil
  have hstT := hst.onFamily
  have hco := hst.measurable
  have hstj : IsTowerAtParameters Tb y T β j :=
    ⟨hstT.startsAtWilson, fun i hi => hstT.coupling_eq i (by omega), fun i hi => hstT.onFamily i (by omega)⟩
  have hfit : (Tb.stepParameters y).Admissible := hTb.fits y e6
  have hon := hstT.onFamily j (by omega)
  have hDarr : ∀ i, i ≤ j + 1 → (T.stage i).functional = (couplingFlow (Tb.stepParameters y) β i).2 := by
    intro i
    induction i with
    | zero => intro _; exact hstT.startsAtWilson.functional_eq
    | succ i ih =>
      intro hi
      have e := ih (by omega)
      have c := hstT.coupling_eq i (by omega)
      show kernelImage (Tb.stepParameters y) (T.stage i).coupling (T.stage i).functional =
        kernelImage (Tb.stepParameters y) (couplingFlow (Tb.stepParameters y) β i).1
          (couplingFlow (Tb.stepParameters y) β i).2
      rw [e, c]
  have hstand : ExpansionHolds (Tb.stepParameters y) := ⟨hret, fun β' hβ' => hwil β' hβ'⟩
  have hreach : ∀ t, t ≤ j + 1 → CouplingsAboveFloor (Tb.stepParameters y) β t := fun t ht i hi => by
    have c := hstT.coupling_eq i (by omega)
    have o := (hstT.onFamily i (by omega)).le_coupling
    show y ≤ (couplingFlow (Tb.stepParameters y) β i).1
    rw [← c]
    exact o
  have hmove := (hRow (Tb.stepParameters y) hstand β (j + 1) (hreach _ le_rfl)).2 j (by omega)
  have hrow := (hRow (Tb.stepParameters y) hstand β j (hreach _ (by omega))).1
  have hmoved : |(T.stage j).toStepSetup.nextCoupling - (T.stage j).toStepSetup.coupling| ≤ 2 * Tb.B := by
    have c1 := hstT.coupling_eq (j + 1) (by omega)
    have c0 := hstT.coupling_eq j (by omega)
    show |(T.stage (j + 1)).coupling - (T.stage j).coupling| ≤ 2 * Tb.B
    rw [c1, c0]
    exact hmove
  have hArr : (T.stage j).toStepSetup.IsSymmetricWeight := by
    have hd : (T.stage j).toStepSetup.functional = flowFunctional (Tb.stepParameters y) β j := hDarr j (by omega)
    unfold StepSetup.IsSymmetricWeight
    rw [hd]
    exact hrow.1
  have hFl' := hy5 _ (e5.trans hon.le_coupling)
  have hF : (T.stage j).toStepSetup.IsWellPosed := isWellPosed_of_onParameters hTb e6 e7 hon hmoved hArr hFl'
  have hx : (T.stage j).toStepSetup.nextCoupling ≤ 1.01 * (T.stage j).toStepSetup.coupling :=
    (hFl'.stable_nearby.2 _ hmoved).2.1
  have hcut : ColdStepAtMirrorFrames.IsCutoff ((Tb.stepParameters y).threshold / 64) T.base.barrierFn := by
    have hp : T.base.barrierFn = Tb.cutoff := (hstT.onFamily 0 (by omega)).barrierFn_eq
    rw [hp]
    exact hTb.cut
  have hLam := hfit.depth_lt
  have hpres := (hD (Tb.stepParameters y) hfit hLam T hcut hco β j m).2
  haveI : IsProbabilityMeasure (markedSampleLaw T β (j + 1) m) :=
    (hD (Tb.stepParameters y) hfit hLam T hcut hco β (j + 1) m).1
  set R := (T.stage j).toStepSetup with hRdef
  have hn₀ : R.params.n₀ ≤ m := le_trans (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (NeZero.ne _))) hb.2
  have hotSet : ∀ c : Finset (TorusSite m), MeasurableSet {V : TorusField m | hotCoreSites R V = c} :=
    (hCB Tb hTb y R hon hF m hb).1
  let Fn : TorusField m → CaseFunction R m := fun V _ Yt _ bad _ => allSupportsFree R Θ (hotCoreSites R V) bad Yt
  have hfst : Measurable (fun u : MarkedSample (Tb.stepParameters y) (j + 1) m => u.1) := hpres.measurable
  have hsnd : Measurable (fun u : MarkedSample (Tb.stepParameters y) (j + 1) m => u.2) := measurable_snd
  have hVm : Measurable (fun u : MarkedSample (Tb.stepParameters y) (j + 1) m => u.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp hsnd)
  have hBm : Measurable (fun u : MarkedSample (Tb.stepParameters y) (j + 1) m => u.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp hsnd)
  have hStm := (hSt (Tb.stepParameters y) hfit T j (m * (Tb.stepParameters y).side)).comp hfst
  have hg : Measurable fun u : MarkedSample (Tb.stepParameters y) (j + 1) m =>
      Fn u.2.2.1 (topField (Tb.stepParameters y) j (m * (Tb.stepParameters y).side) u.1)
        (stageState T j (m * (Tb.stepParameters y).side) u.1).2.1
        (stageState T j (m * (Tb.stepParameters y).side) u.1).2.2 u.2.2.2 u.2.1 := by
    refine measurable_of_measurableSet_fibres
      (D := Finset (TorusSite (m * (Tb.stepParameters y).side)) ×
        Finset (TorusBond (m * (Tb.stepParameters y).side)) × Finset (TorusSite m))
      (fun u : MarkedSample (Tb.stepParameters y) (j + 1) m =>
        ((stageState T j (m * (Tb.stepParameters y).side) u.1).2.1,
          (u.2.2.2 : Finset (TorusBond (m * (Tb.stepParameters y).side))), hotCoreSites R u.2.2.1)) ?_
      (fun d _ => allSupportsFree R Θ d.2.2 d.2.1 d.1) (fun d => measurable_const)
    rintro ⟨a', b', c'⟩
    have s1 : MeasurableSet {u : MarkedSample (Tb.stepParameters y) (j + 1) m |
        (stageState T j (m * (Tb.stepParameters y).side) u.1).2.1 = a'} :=
      hStm (measurable_snd (measurableSet_sigma_fst_eq a'))
    have s2 : MeasurableSet {u : MarkedSample (Tb.stepParameters y) (j + 1) m |
        (u.2.2.2 : Finset (TorusBond (m * (Tb.stepParameters y).side))) = b'} :=
      hBm (MeasurableSpace.measurableSet_top (s := {b'}))
    have s3 : MeasurableSet {u : MarkedSample (Tb.stepParameters y) (j + 1) m | hotCoreSites R u.2.2.1 = c'} :=
      hVm (hotSet c')
    refine (s1.inter (s2.inter s3)).congr (Set.ext fun u => ⟨fun h => Prod.ext h.1 (Prod.ext h.2.1 h.2.2),
      fun h => ⟨(Prod.mk.inj h).1, (Prod.mk.inj (Prod.mk.inj h).2).1, (Prod.mk.inj (Prod.mk.inj h).2).2⟩⟩)
  have hbL : IsBlockTorusSide (Tb.stepParameters y) (m * (Tb.stepParameters y).side) :=
    ⟨Dvd.intro_left _ rfl, by rw [mul_comm]; exact Nat.mul_le_mul_right _ hn₀⟩
  have hae := hMM T β j m hstj hcut hco hF hbL hb.1 Fn hg
    ⟨1, fun u => by
      dsimp only [Fn, allSupportsFree]
      split_ifs <;> simp⟩
  have hae1 := hMM T β j m hstj hcut hco hF hbL hb.1 (fun _ _ _ _ _ _ => (1 : ℝ)) measurable_const
    ⟨1, fun u => by simp⟩
  have hmle : stageSigma T (j + 1) m ≤ markedSampleMeasurableSpace (Tb.stepParameters y) (j + 1) m :=
    (hSt (Tb.stepParameters y) hfit T (j + 1) m).comap_le
  set g : MarkedSample (Tb.stepParameters y) (j + 1) m → ℝ := fun u =>
      Fn u.2.2.1 (topField (Tb.stepParameters y) j (m * (Tb.stepParameters y).side) u.1)
        (stageState T j (m * (Tb.stepParameters y).side) u.1).2.1
        (stageState T j (m * (Tb.stepParameters y).side) u.1).2.2 u.2.2.2 u.2.1 with hgdef
  have hpt : ∀ᵐ u ∂(markedSampleLaw T β (j + 1) m),
      (stageGround T j m u).gibbsLaw ∅ (supportsPresent (stageGround T j m u) Θ) =
        ENNReal.ofReal (((markedSampleLaw T β (j + 1) m)[g | stageSigma T (j + 1) m]) u) := by
    filter_upwards [hae, hae1] with u h h1
    rw [h]
    have h1' : (1 : ℝ) = caseMean R (hotCoreSites R u.2.2.1) u.2.2.1 (stageState T (j + 1) m u).2
        (fun _ _ _ _ _ => (1 : ℝ)) := by
      rw [← h1]
      have e := condExp_const (μ := markedSampleLaw T β (j + 1) m) hmle (1 : ℝ)
      exact (congrFun e u).symm
    set q : CoarseState R m := (stageState T (j + 1) m u).2 with hq
    set V := u.2.2.1 with hV
    have hull : IsHullState R.params R.nextRange V q.1 :=
      hHull (Tb.stepParameters y) hfit R.range R.nextRange hF.range_le hF.nextRange_ge m hb.1 V u.2.2.2
        (stageState T j (m * (Tb.stepParameters y).side) u.1).2.1
    have hnz : coarseStateWeight R (hotCoreSites R V) V q ≠ 0 := fun h0 => by
      unfold caseMean at h1'
      rw [h0, div_zero] at h1'
      exact one_ne_zero h1'
    have hΦ : ∀ X ∈ chainComponents R.nextRange q.1, coarseFactor V q X ≠ 0 := fun X hX h0 =>
      hnz (hZ R hF m hb V q hull ⟨X, hX, h0⟩)
    have hhot := hy4 y e4 R hon hF m hb V q hull hΦ
    have hG : (hotCaseGround R V q).IsAdmissibleGround := Or.inr hhot
    have cols := fun off => hy1 y e1 R hon hx m (hotCaseGround R V q) hG off
    obtain ⟨-, hcold, -, hms, -⟩ := hy2 y e2 R hon hx m (hotCaseGround R V q) hG
    obtain ⟨-, hpos, -⟩ := hRat R m (hotCaseGround R V q) Tb.gasRate cols
    have hPfin : (hotCaseGround R V q).partitionFunction ∅ ≠ ⊤ := fun e => by
      have hx0 := hpos ∅
      unfold GasGround.xi at hx0
      rw [e] at hx0
      simp at hx0
    have hfin : coarseStateMass R (hotCoreSites R V) V q ≠ ⊤ := by
      have e : coarseStateMass R (hotCoreSites R V) V q = _ := hms
      rw [e]
      exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hPfin
    obtain ⟨hw, hsc⟩ := cols fun i => i.1.Touches ∅
    haveI : IsProbabilityMeasure ((hotCaseGround R V q).gibbsLaw ∅) := hsc.isProbabilityMeasure
    have hmeas : MeasurableSet (supportsPresent (hotCaseGround R V q) Θ) :=
      measurableSet_supportsPresent _ hw Θ
    obtain ⟨hadm, hFn⟩ := hy3 y e3 R hon hx m (hotCaseGround R V q) hG
    obtain ⟨-, heq⟩ := hFn (fun _ Yt _ bad _ => allSupportsFree R Θ (hotCoreSites R V) bad Yt)
      (fun _ _ _ => measurable_const) (fun _ _ _ _ _ _ _ _ _ => rfl)
      (hBI R hF m hn₀ _ _ _ hfin _ 1 (fun _ _ _ => measurable_const) (fun _ _ _ _ _ => by
        dsimp only [allSupportsFree]
        split_ifs <;> simp))
    have hmean := gasExpectation_allSupportsFree (hotCaseGround R V q) (anchorReachesCut_of_isHotCase hhot)
      hadm Θ hmeas
    have hc : caseMean R (hotCoreSites R V) V q (Fn V) =
        ((hotCaseGround R V q).gibbsLaw ∅).real (supportsPresent (hotCaseGround R V q) Θ) :=
      heq.trans hmean
    rw [hc]
    exact (ENNReal.ofReal_toReal (measure_ne_top ((hotCaseGround R V q).gibbsLaw ∅) _)).symm
  have hgE : g = {v | Θ ⊆ freeSupportsAt T j m v}.indicator (fun _ => (1 : ℝ)) := by
    funext u
    by_cases hu : Θ ⊆ freeSupportsAt T j m u
    · rw [Set.indicator_of_mem (by exact hu)]
      exact if_pos hu
    · rw [Set.indicator_of_notMem (by exact hu)]
      exact if_neg hu
  have hE : MeasurableSet {v | Θ ⊆ freeSupportsAt T j m v} := by
    have e : {v | Θ ⊆ freeSupportsAt T j m v} = g ⁻¹' {1} := by
      ext u
      rw [hgE]
      by_cases hu : Θ ⊆ freeSupportsAt T j m u
      · simp [hu]
      · simp [hu]
    rw [e]
    exact hg (measurableSet_singleton 1)
  have hint : Integrable g (markedSampleLaw T β (j + 1) m) := by
    rw [hgE]
    exact (integrable_const (1 : ℝ)).indicator hE
  have hAm : MeasurableSet A := hmle A hA
  have hnn : 0 ≤ᵐ[(markedSampleLaw T β (j + 1) m).restrict A]
      (markedSampleLaw T β (j + 1) m)[g | stageSigma T (j + 1) m] :=
    ae_restrict_of_ae (condExp_nonneg (Filter.Eventually.of_forall fun u => by
      rw [hgE]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) u))
  calc markedSampleLaw T β (j + 1) m (A ∩ {v | Θ ⊆ freeSupportsAt T j m v})
      = ENNReal.ofReal (∫ v in A, g v ∂(markedSampleLaw T β (j + 1) m)) := by
        rw [hgE, setIntegral_indicator hE]
        simp only [integral_const, smul_eq_mul, mul_one, MeasurableSet.univ, measureReal_restrict_apply,
          Set.univ_inter]
        exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ = ENNReal.ofReal (∫ v in A, ((markedSampleLaw T β (j + 1) m)[g | stageSigma T (j + 1) m]) v
          ∂(markedSampleLaw T β (j + 1) m)) := by
        rw [setIntegral_condExp hmle hint hA]
    _ = ∫⁻ v in A, ENNReal.ofReal (((markedSampleLaw T β (j + 1) m)[g | stageSigma T (j + 1) m]) v)
          ∂(markedSampleLaw T β (j + 1) m) :=
        ofReal_integral_eq_lintegral_ofReal integrable_condExp.integrableOn hnn
    _ = ∫⁻ v in A, (stageGround T j m v).gibbsLaw ∅ (supportsPresent (stageGround T j m v) Θ)
          ∂(markedSampleLaw T β (j + 1) m) :=
        lintegral_congr_ae (ae_restrict_of_ae (hpt.mono fun _ h => h.symm))
end YangMills.Construction.CellWindows
end
