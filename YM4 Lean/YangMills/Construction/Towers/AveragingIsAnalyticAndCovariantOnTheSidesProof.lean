import YangMills.Construction.Averaging.RadiiBelowTheExplicitBound
import YangMills.Construction.Lattice.AveragingMapOnSmallSetsAndMeasurability
import YangMills.Construction.Lattice.DomainsOfTheTwoSchemesProof
import YangMills.Construction.Lattice.LocalityAndGaugeCovarianceOfTheAveragingMap
import YangMills.Construction.Towers.AveragingIsAnalyticAndCovariantOnTheSides
import YangMills.Construction.Towers.CovariantAveragesAtTheTrivialConfigurationProof
import YangMills.Construction.Towers.ValuesOfTheAveragesNearTheTrivialConfiguration
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Filter Set Coordinates Matrices Matrices.GroupLieProduct Matrices.GroupLieProduct.Subspaces
open scoped Matrix.Norms.L2Operator Topology
namespace Tower
namespace OnSidesProof
section Powers
variable {P ι : Type} [Fintype P]
private theorem holomorphicVia_of_analyticAt {q : ℕ} (σ : P ≃ Fin q) {U : Set (P → ComplexMatrix2)}
    (hU : IsOpen U) {Φ : (P → ComplexMatrix2) → ComplexMatrix2} (hΦ : ∀ y ∈ U, AnalyticAt ℂ Φ y) :
    ComplexCoordinates.IsHolomorphicVia (GroupLieProduct.matrixPiEquiv σ)
      ComplexCoordinates.matrixEquiv U Φ := by apply _root_.YangMills.SharedProofs.p13839 <;> assumption
variable [Fintype ι]
private theorem exists_analytic_local_form {D : Set (P → ComplexMatrix2)}
    {f : (P → ComplexMatrix2) → ι → ComplexMatrix2}
    (hf : ComplexMatrix2.IsRealAnalyticBetween (fun _ : P => ComplexMatrix2.FactorKind.group)
      (fun _ : ι => ComplexMatrix2.FactorKind.group) D f)
    {x : P → ComplexMatrix2} (hx : x ∈ D) (i : ι) :
    ∃ (U : Set (P → ComplexMatrix2)) (Φ : (P → ComplexMatrix2) → ComplexMatrix2), IsOpen U ∧
      x ∈ U ∧ (∀ y ∈ U, AnalyticAt ℂ Φ y) ∧
      (∀ v ∈ U ∩ unimodularPi P, Φ v ∈ ComplexMatrix2.unitDeterminant) ∧
      ∀ v ∈ U ∩ D, f v i = Φ v := by
  obtain ⟨⟨O', -, hD⟩, hloc⟩ := hf
  obtain ⟨W, h, hxW, ⟨⟨O, hO, hW⟩, hmaps, hgerm⟩, hfe⟩ := hloc x hx
  obtain ⟨G, hGa, hGe⟩ := hgerm x hxW
  have h1 : ∀ᶠ y in 𝓝 x, AnalyticAt ℂ G y := hGa.eventually_analyticAt
  have h2 : ∀ᶠ y in 𝓝 x, y ∈ W → h y = G y := eventually_nhdsWithin_iff.1 hGe
  have h3 : ∀ᶠ y in 𝓝 x, y ∈ D → f y = h y := eventually_nhdsWithin_iff.1 hfe
  have h4 : ∀ᶠ y in 𝓝 x, y ∈ O := hO.mem_nhds (by
    rw [hW] at hxW
    exact hxW.1)
  obtain ⟨U, hsub, hUo, hxU⟩ := eventually_nhds_iff.1 (h1.and (h2.and (h3.and h4)))
  refine ⟨U, fun y => G y i, hUo, hxU, fun y hy => ?_, fun v hv => ?_, fun v hv => ?_⟩
  · exact analyticAt_pi_iff.1 (hsub y hy).1 i
  · have hvW : v ∈ W := by
      rw [hW]
      exact ⟨(hsub v hv.1).2.2.2, hv.2⟩
    have hm := hmaps hvW i
    change G v i ∈ ComplexMatrix2.unitDeterminant
    rw [← (hsub v hv.1).2.1 hvW]
    exact hm
  · have hvW : v ∈ W := by
      rw [hW]
      refine ⟨(hsub v hv.1).2.2.2, fun r => ?_⟩
      have hr : v ∈ ComplexMatrix2.compactProduct fun _ : P => ComplexMatrix2.FactorKind.group := by
        have := hv.2
        rw [hD] at this
        exact this.2
      exact (Matrix.mem_specialUnitaryGroup_iff.1 (hr r)).2
    change f v i = G v i
    rw [(hsub v hv.1).2.2.1 hv.2, (hsub v hv.1).2.1 hvW]
private theorem isRealAnalyticBetween_of_subset {s : P → ComplexMatrix2.FactorKind}
    {t : ι → ComplexMatrix2.FactorKind} {D D' : Set (P → ComplexMatrix2)}
    {f f' : (P → ComplexMatrix2) → ι → ComplexMatrix2}
    (h : ComplexMatrix2.IsRealAnalyticBetween s t D f) (hD : D' ⊆ D)
    (ho : ComplexMatrix2.IsRelativelyOpen (ComplexMatrix2.compactProduct s) D')
    (he : ∀ v ∈ D', f' v = f v) :
    ComplexMatrix2.IsRealAnalyticBetween s t D' f' := by
  refine ⟨ho, fun x hx => ?_⟩
  obtain ⟨W, g, hxW, hg, hfe⟩ := h.2 x (hD hx)
  refine ⟨W, g, hxW, hg, ?_⟩
  filter_upwards [nhdsWithin_mono x hD hfe, self_mem_nhdsWithin] with y hy hy'
  rw [he y hy', hy]
private theorem isRealAnalyticBetween_component {D : Set (P → ComplexMatrix2)}
    {f : (P → ComplexMatrix2) → ι → ComplexMatrix2}
    (hf : ComplexMatrix2.IsRealAnalyticBetween (fun _ : P => ComplexMatrix2.FactorKind.group)
      (fun _ : ι => ComplexMatrix2.FactorKind.group) D f) (i : ι) :
    ComplexMatrix2.IsRealAnalyticBetween (fun _ : P => ComplexMatrix2.FactorKind.group)
      (fun _ : Fin 1 => ComplexMatrix2.FactorKind.group) D fun v _ => f v i := by
  refine ⟨hf.1, fun x hx => ?_⟩
  obtain ⟨W, h, hxW, ⟨hWo, hmaps, hgerm⟩, hfe⟩ := hf.2 x hx
  refine ⟨W, fun y _ => h y i, hxW, ⟨hWo, fun y hy _ => hmaps hy i, fun y hy => ?_⟩, ?_⟩
  · obtain ⟨G, hGa, hGe⟩ := hgerm y hy
    refine ⟨fun z _ => G z i, analyticAt_pi_iff.2 fun _ => analyticAt_pi_iff.1 hGa i, ?_⟩
    filter_upwards [hGe] with z hz
    rw [hz]
  · filter_upwards [hfe] with z hz
    rw [hz]
private theorem isSubspaceAnalyticToProduct_of_components
    (hS : Matrices.UnimodularArguments.HolomorphicAtUnimodular) {R R' : Type} [Fintype R]
    [Fintype R'] {𝒲 : Set (R ⊕ Empty → ComplexMatrix2)} {D : Set (R → ComplexMatrix2)}
    {g : (R → ComplexMatrix2) → R' → ComplexMatrix2}
    {f : (R ⊕ Empty → ComplexMatrix2) → R' ⊕ Empty → ComplexMatrix2}
    (hO : IsOpenInSubspaceTimesGroup (⊥ : Submodule ℝ (Empty → ComplexMatrix2)) 𝒲)
    (hD : ComplexMatrix2.IsRelativelyOpen
      (ComplexMatrix2.compactProduct fun _ : R => ComplexMatrix2.FactorKind.group) D)
    (h𝒲 : ∀ q, q ∈ 𝒲 ↔
      q ∈ subspaceTimesGroup (⊥ : Submodule ℝ (Empty → ComplexMatrix2)) R ∧ groupComponent q ∈ D)
    (hmaps : MapsTo f 𝒲 (subspaceTimesGroup (⊥ : Submodule ℝ (Empty → ComplexMatrix2)) R'))
    (hf : ∀ q ∈ 𝒲, ∀ c, f q (.inl c) = g (groupComponent q) c)
    (hg : ∀ c, ComplexMatrix2.IsRealAnalyticBetween (fun _ : R => ComplexMatrix2.FactorKind.group)
      (fun _ : Fin 1 => ComplexMatrix2.FactorKind.group) D fun v _ => g v c) :
    IsSubspaceAnalyticToProduct (⊥ : Submodule ℝ (Empty → ComplexMatrix2))
      (⊥ : Submodule ℝ (Empty → ComplexMatrix2)) 𝒲 f := by
  refine ⟨hO, bot_le, hmaps, fun p hp => ?_⟩
  have hpD : groupComponent p ∈ D := ((h𝒲 p).1 hp).2
  choose U Φ hUo hpU hΦa hΦG hΦe using fun c => exists_analytic_local_form (hg c) hpD (0 : Fin 1)
  obtain ⟨O, hOo, hDe⟩ := hD
  have hDs : ∀ v ∈ D, v ∈ unimodularPi R := fun v hv r => by
    rw [hDe] at hv
    exact (Matrix.mem_specialUnitaryGroup_iff.1 (hv.2 r)).2
  have hDO : ∀ v ∈ D, v ∈ O := fun v hv => by
    rw [hDe] at hv
    exact hv.1
  let 𝒩 : Set (R → ComplexMatrix2) := (⋂ c, U c) ∩ O
  have h𝒩o : IsOpen 𝒩 := (isOpen_iInter_of_finite hUo).inter hOo
  have hp𝒩 : groupComponent p ∈ 𝒩 := ⟨mem_iInter.2 hpU, hDO _ hpD⟩
  have hcont : Continuous fun x : R ⊕ Empty → ComplexMatrix2 => x ∘ Sum.inl :=
    continuous_pi fun r => continuous_apply _
  let 𝒳 : Set (R ⊕ Empty → ComplexMatrix2) := (fun x : R ⊕ Empty → ComplexMatrix2 => x ∘ Sum.inl) ⁻¹'
    Matrices.UnimodularArguments.unimodularPart 𝒩
  have h𝒳o : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct R Empty) 𝒳 := by
    refine ⟨(fun x : R ⊕ Empty → ComplexMatrix2 => x ∘ Sum.inl) ⁻¹' 𝒩, h𝒩o.preimage hcont, ?_⟩
    ext q
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun i => ?_⟩
      rcases i with r | e
      · exact h2 r
      · exact e.elim
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun r => h2 (.inl r)⟩
  have hin : 𝒳 ∩ subspaceTimesGroup (⊥ : Submodule ℝ (Empty → ComplexMatrix2)) R ⊆ 𝒲 := by
    rintro q ⟨hq, hqS⟩
    refine (h𝒲 q).2 ⟨hqS, ?_⟩
    rw [hDe]
    exact ⟨hq.1.2, hqS.2⟩
  refine ⟨𝒳, ⟨hp𝒩, hDs _ hpD⟩, h𝒳o, hin,
    fun q => ofParts (fun c => Φ c (q ∘ Sum.inl)) Empty.elim,
    fun b => ⟨h𝒳o, fun c => ?_, fun e => e.elim⟩, fun q hq => ?_⟩
  · exact (hS R _ (Fintype.equivFin R) 𝒩 (Φ c) h𝒩o
      (holomorphicVia_of_analyticAt _ h𝒩o fun y hy => hΦa c y (mem_iInter.1 hy.1 c))
      fun V hV => hΦG c V ⟨mem_iInter.1 hV.1.1 c, hV.2⟩).2.2.2 b
  · have hq𝒲 := hin hq
    have hqD : groupComponent q ∈ D := ((h𝒲 q).1 hq𝒲).2
    funext r
    rcases r with c | e
    · have h := hΦe c (groupComponent q) ⟨mem_iInter.1 hq.1.1.1 c, hqD⟩
      change Φ c (groupComponent q) = f q (.inl c)
      rw [hf q hq𝒲 c]
      exact h.symm
    · exact e.elim
end Powers
section Fields
variable {L n k j : ℕ}
private theorem isPositivelyOriented_or_opposite (b : Edge L n k j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
private theorem fieldOfPositiveValues_restrict {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) : fieldOfPositiveValues (restrictToPositiveEdges V) = V := by
  funext b
  unfold fieldOfPositiveValues
  by_cases hb : b.IsPositivelyOriented
  · rw [dif_pos hb]
    rfl
  · rw [dif_neg hb, dif_pos ((isPositivelyOriented_or_opposite b).resolve_left hb)]
    exact (hV.2 b.opposite (mem_univ _)).symm
abbrev _root_.YangMills.SharedProofs.p407 := @fieldOfPositiveValues_restrict
private theorem restrict_fieldOfPositiveValues (w : PositiveEdge L n k j → ComplexMatrix2) :
    restrictToPositiveEdges (fieldOfPositiveValues w) = w := by
  funext ⟨b, hb⟩
  change fieldOfPositiveValues w b = _
  unfold fieldOfPositiveValues
  rw [dif_pos hb]
abbrev _root_.YangMills.SharedProofs.p777 := @restrict_fieldOfPositiveValues
private theorem periodic_fieldOfPositiveValues_values {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) :
    PeriodicLattice.fieldOfPositiveValues (PeriodicLattice.valuesOnPositiveBonds V) = V := by
  funext b
  unfold PeriodicLattice.fieldOfPositiveValues PeriodicLattice.extendByInverses
  by_cases hb : b.IsPositivelyOriented
  · rw [dif_pos (show b ∈ {b : Edge L n k j | b.IsPositivelyOriented} from hb)]
    rfl
  · rw [dif_neg (show b ∉ {b : Edge L n k j | b.IsPositivelyOriented} from hb),
      dif_pos (show b.opposite ∈ {b : Edge L n k j | b.IsPositivelyOriented} from
        (isPositivelyOriented_or_opposite b).resolve_left hb)]
    exact (hV.2 b.opposite (mem_univ _)).symm
private theorem isOpenInSubspaceTimesGroup_of_isOpenFieldSet [Fintype (PositiveEdge L n k j)]
    {𝒰 : Set (Edge L n k j → ComplexMatrix2)}
    (h : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰) :
    IsOpenInSubspaceTimesGroup (R := PositiveEdge L n k j) (S := Empty) ⊥
      {q | fieldOfPositiveValues (groupComponent q) ∈ 𝒰} := by
  refine ⟨bot_le, ?_⟩
  obtain ⟨O, hO, heq⟩ := h.2
  have hg : Continuous (groupComponent (R := PositiveEdge L n k j) (S := Empty)) :=
    continuous_pi fun r => continuous_apply _
  refine ⟨groupComponent ⁻¹' O, hO.preimage hg, ?_⟩
  ext q
  constructor
  · intro hq
    have h1 : groupComponent q ∈ restrictToPositiveEdges '' 𝒰 :=
      ⟨_, hq, restrict_fieldOfPositiveValues _⟩
    rw [heq] at h1
    exact ⟨h1.1, Subsingleton.elim _ _, h1.2⟩
  · rintro ⟨h1, -, h2⟩
    have h3 : groupComponent q ∈ restrictToPositiveEdges '' 𝒰 := by
      rw [heq]
      exact ⟨h1, h2⟩
    obtain ⟨V, hV, hVq⟩ := h3
    change fieldOfPositiveValues (groupComponent q) ∈ 𝒰
    rw [← hVq, fieldOfPositiveValues_restrict (h.1 hV)]
    exact hV
abbrev _root_.YangMills.SharedProofs.p979 := @isOpenInSubspaceTimesGroup_of_isOpenFieldSet
private theorem eventually_mem_of_isOpenNhdOfOne {𝒰 : Set (Edge L n k j → ComplexMatrix2)}
    (h : IsOpenNhdOfOne 𝒰) :
    ∀ᶠ V in 𝓝[fieldSpace L n k j] (fun _ => (1 : ComplexMatrix2)), V ∈ 𝒰 := by
  obtain ⟨⟨hsub, O, hO, heq⟩, h1⟩ := h
  have hρ : Continuous (restrictToPositiveEdges (L := L) (m := n) (k := k) (j := j)) :=
    continuous_pi fun r => continuous_apply _
  have hone : restrictToPositiveEdges (trivialField L n k j) ∈ O := by
    have : restrictToPositiveEdges (trivialField L n k j) ∈ restrictToPositiveEdges '' 𝒰 :=
      ⟨_, h1, rfl⟩
    rw [heq] at this
    exact this.1
  refine eventually_nhdsWithin_iff.2 ?_
  filter_upwards [hρ.continuousAt.eventually (hO.mem_nhds hone)] with V hV hVc
  have hmem : restrictToPositiveEdges V ∈ restrictToPositiveEdges '' 𝒰 := by
    rw [heq]
    exact ⟨hV, fun b => hVc.1 b.1 (mem_univ _)⟩
  obtain ⟨V', hV', he⟩ := hmem
  rw [← fieldOfPositiveValues_restrict hVc, ← he, fieldOfPositiveValues_restrict (hsub hV')]
  exact hV'
abbrev _root_.YangMills.DeltaSharedProofs.p501856 := @eventually_mem_of_isOpenNhdOfOne
end Fields
end OnSidesProof
open OnSidesProof in
theorem smoothingAnalyticCovariantOnSides_holds
    (hS : Matrices.UnimodularArguments.HolomorphicAtUnimodular)
    (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hVal : SmoothingNearTrivialField)
    (hR : Averaging.ExplicitRadii.Holds)
    (hM : PeriodicLattice.BlockAverageSmallSetAndMeasurable)
    (hC : PeriodicLattice.BlockAverageLocalityAndCovariance) :
    SmoothingAnalyticCovariantOnSides := by
  intro L hL n k j hn hj
  have hk : 0 < k := by omega
  let s : Conventions.StandingParameters := ⟨L, hL, ⟨k, hk⟩, ⟨n, hn⟩⟩
  have hfin : ∀ i, i ≤ k → Finite (PositiveEdge L n k i) := fun i hi => by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hb, -⟩ := (hA L hL n i k hn hi).2.1
    exact Subtype.finite
  let i₁ : Fintype (PositiveEdge L n k j) :=
    have := hfin j hj.le
    Fintype.ofFinite _
  let i₂ : Fintype (PositiveEdge L n k (j + 1)) :=
    have := hfin (j + 1) hj
    Fintype.ofFinite _
  obtain ⟨h𝒰, hval⟩ := (hVal L n k hL hn (by omega)).1 j hj
  have hopen := h𝒰.1
  have hconf : commonSmoothingDomain L n k j ⊆ fieldSpace L n k j := hopen.1
  have hD : ComplexMatrix2.IsRelativelyOpen
      (ComplexMatrix2.compactProduct fun _ : PositiveEdge L n k j => ComplexMatrix2.FactorKind.group)
      (restrictToPositiveEdges '' commonSmoothingDomain L n k j) := hopen.2
  have hω : Averaging.smoothingRadius L ∈ Ioc (0 : ℝ) (PeriodicLattice.averagingRadiusCap L) :=
    Averaging.isSmoothingRadius_smoothingRadius hL.1 hL.2
  have hMs := hM s j hj
  have hMc : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
      PeriodicLattice.BlockAverageAnalyticNearOne (Averaging.smoothingRadius L) j c :=
    fun c hc => (hMs.1 c hc).1
  obtain ⟨hmapsAll, -⟩ :
      PeriodicLattice.BlockAverageBorel L n k (Averaging.smoothingRadius L) j := hMs.2
  have hmaps : MapsTo (smoothingStep L n k j) (commonSmoothingDomain L n k j)
      (fieldSpace L n k (j + 1)) := fun V hV => hmapsAll (hconf hV)
  have hsub : ∀ c : Edge L n k (j + 1),
      restrictToPositiveEdges '' commonSmoothingDomain L n k j ⊆
        PeriodicLattice.valuesOnPositiveBonds ''
          (PeriodicLattice.smallPlaquetteFields (Averaging.smoothingRadius L) c :
            Set (Edge L n k j → ComplexMatrix2)) := by
    rintro c _ ⟨V, hV, rfl⟩
    exact ⟨V, mem_iInter.1 hV c, rfl⟩
  have hcov := ((hC L n k hL hn).1 j hj).1
  refine ⟨⟨commonSmoothingDomain L n k j, h𝒰, ?_, fun y x hx => ?_⟩, ?_⟩
  · refine ⟨hopen, hmaps, i₁, i₂, ?_⟩
    refine isSubspaceAnalyticToProduct_of_components
      (g := fun v c => smoothingStep L n k j (fieldOfPositiveValues v) c.1)
      hS (isOpenInSubspaceTimesGroup_of_isOpenFieldSet hopen) hD ?_ ?_ (fun _ _ _ => rfl)
      fun c => ?_
    · intro q
      constructor
      · intro hq
        have hO := (isOpenInSubspaceTimesGroup_of_isOpenFieldSet hopen).2
        obtain ⟨O, -, hOe⟩ := hO
        have hq' := hq
        rw [hOe] at hq'
        exact ⟨hq'.2, _, hq, restrict_fieldOfPositiveValues _⟩
      · rintro ⟨-, V, hV, he⟩
        change fieldOfPositiveValues (groupComponent q) ∈ commonSmoothingDomain L n k j
        rw [← he, fieldOfPositiveValues_restrict (hconf hV)]
        exact hV
    · intro q hq
      exact ⟨Subsingleton.elim _ _, fun c => (hmaps hq).1 c.1 (mem_univ _)⟩
    · refine isRealAnalyticBetween_of_subset ((hMc c.1 c.2).2 i₁) (hsub c.1) hD ?_
      rintro _ ⟨V, hV, rfl⟩
      funext _
      change smoothingStep L n k j (fieldOfPositiveValues (restrictToPositiveEdges V)) c.1 =
        PeriodicLattice.blockAverage (Averaging.smoothingRadius L)
          (PeriodicLattice.fieldOfPositiveValues (PeriodicLattice.valuesOnPositiveBonds V)) c.1
      rw [fieldOfPositiveValues_restrict (hconf hV),
        periodic_fieldOfPositiveValues_values (hconf hV)]
      rfl
  · have hc : (PeriodicLattice.Bond.forwardFrom y 0).IsPositivelyOriented :=
      ⟨0, by simp [PeriodicLattice.Bond.forwardFrom]⟩
    have hy : y ∈ ({(PeriodicLattice.Bond.forwardFrom y 0).source,
        (PeriodicLattice.Bond.forwardFrom y 0).target} : Set (Vertex L n k (j + 1))) := Or.inl rfl
    refine ⟨fun V hV => (hval V hV _ hc).hasContourMean y hy x hx, hopen, i₁, ?_⟩
    have hA' : PeriodicLattice.ContourMeansAnalyticOn
        ({(PeriodicLattice.Bond.forwardFrom y 0).source,
          (PeriodicLattice.Bond.forwardFrom y 0).target} : Set (Vertex L n k (j + 1)))
        (PeriodicLattice.smallPlaquetteFields (Averaging.smoothingRadius L)
          (PeriodicLattice.Bond.forwardFrom y 0) : Set (Edge L n k j → ComplexMatrix2)) :=
      ((hR.2.2.1 s).smallSet (Averaging.smoothingRadius L) hω j hj
        (PeriodicLattice.Bond.forwardFrom y 0)).analytic i₁
    refine isRealAnalyticBetween_of_subset
      (isRealAnalyticBetween_component (P := PositiveEdge L n k j) (hA'.2 y hy x hx).2 0)
      (hsub _) hD ?_
    rintro _ ⟨V, hV, rfl⟩
    funext _
    change PeriodicLattice.meanContourHolonomy
        (fieldOfPositiveValues (restrictToPositiveEdges V)) y x =
      PeriodicLattice.meanContourHolonomy
        (PeriodicLattice.fieldOfPositiveValues (PeriodicLattice.valuesOnPositiveBonds V)) y x
    rw [fieldOfPositiveValues_restrict (hconf hV),
      periodic_fieldOfPositiveValues_values (hconf hV)]
  · refine (eventually_mem_of_isOpenNhdOfOne h𝒰).mono fun V hV u hu => ?_
    obtain ⟨-, hcont, hmap⟩ := hcov V (hconf hV) u hu
    refine ⟨hmap, fun y x hx => ?_⟩
    have hc : (PeriodicLattice.Bond.forwardFrom y 0).IsPositivelyOriented :=
      ⟨0, by simp [PeriodicLattice.Bond.forwardFrom]⟩
    exact (hcont y x hx ((hval V hV _ hc).hasContourMean y (Or.inl rfl) x hx)).2
end Tower
end YangMills.Construction
end
