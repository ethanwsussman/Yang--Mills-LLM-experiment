import YangMills.Construction.ChessboardTori.ChessboardEstimateOnMirrorGridsProof
import YangMills.Construction.ChessboardTori.GroupOnTheTorusAsAQuotient
import YangMills.Construction.ChessboardTori.ThreeEvaluationRules
import YangMills.Construction.MirrorGridsOfEverySide.SimilaritiesOfTheLatticesProof
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction.MirrorGridsAllSides.CellObservablesTorus
open ChessboardTori (ReflectionGrid)
theorem periodicLink_ext_endpoints {E : GridSetup} {b b' : E.PeriodicLink}
    (ht : (b.source : E.Torus) = b'.source)
    (hh : (b.target : E.Torus) = b'.target) : b = b' := by apply _root_.YangMills.Construction.ChessboardTori.ChessboardBoundOnReflectionGrids.link_eq_of_ends <;> assumption
def MapsLinks (E : GridSetup) (r : E.Torus → E.Torus) : Prop :=
  ∀ b : E.PeriodicLink, ∃ b' : E.PeriodicLink,
    (b'.source : E.Torus) = r b.source ∧ (b'.target : E.Torus) = r b.target
theorem imageLink_endpoints {E : GridSetup} {r : E.Torus → E.Torus} (hr : MapsLinks E r)
    (b : E.PeriodicLink) :
    ((E.imageLink r b).source : E.Torus) = r b.source ∧
      ((E.imageLink r b).target : E.Torus) = r b.target :=
  Classical.epsilon_spec (hr b)
theorem one_mem_torusFields (E : GridSetup) :
    (fun _ => 1 : E.PeriodicLink → Matrices.ComplexMatrix2) ∈ E.torusFields :=
  ⟨fun _ _ => one_mem _, fun _ _ => by simp⟩
theorem mapsLinks_of_mem_inducedTorusMaps (hR : ChessboardTori.LiftingRules.Statement)
    {E : GridSetup} {g : ReflectionGrid E} {r' : E.Torus → E.Torus}
    (hr' : r' ∈ g.inducedTorusMaps) :
    MapsLinks E r' := by
  obtain ⟨r, hr, hc⟩ := hr'
  intro b
  obtain ⟨b', h1, h2, -⟩ :=
    (((hR E).2.2.2 (g.toLatticeSym ⟨r, hr⟩) r' hc).2 _ (one_mem_torusFields E)).2 b
  exact ⟨b', h1, h2⟩
theorem pullbackField_mem {E : GridSetup} {r : E.Torus → E.Torus} (hr : MapsLinks E r)
    {U : E.PeriodicLink → Matrices.ComplexMatrix2} (hU : U ∈ E.torusFields) :
    E.pullbackField r U ∈ E.torusFields := by
  refine ⟨fun b _ => hU.1 _ (mem_univ _), fun b _ => ?_⟩
  change U (E.imageLink r b.opposite) = (U (E.imageLink r b))⁻¹
  have h1 : E.imageLink r b.opposite = (E.imageLink r b).opposite :=
    periodicLink_ext_endpoints
      ((imageLink_endpoints hr _).1.trans (imageLink_endpoints hr b).2.symm)
      ((imageLink_endpoints hr _).2.trans (imageLink_endpoints hr b).1.symm)
  rw [h1]
  exact hU.2 _ (mem_univ _)
theorem torusCarrier_spec {E : GridSetup} {g : ReflectionGrid E} (hQ : g.TorusGroupQuotient)
    {C C' : Set E.Torus} (hC : C ∈ g.torusCellSet) (hC' : C' ∈ g.torusCellSet) :
    g.torusCarrier C C' ∈ g.inducedTorusMaps ∧ g.torusCarrier C C' '' C = C' :=
  Classical.epsilon_spec
    (p := fun r' : E.Torus → E.Torus => r' ∈ g.inducedTorusMaps ∧ r' '' C = C')
    (hQ.2.2.2.2.2.2.1 C hC C' hC').exists
theorem torusCellInterior_proj_cell {E : GridSetup} {g : ReflectionGrid E}
    (hsame : g.SameTorusImageCriterion) (k : Fin 4 → ℤ) :
    g.torusCellInterior (E.proj '' g.cell k) = E.proj '' interior (g.cell k) := by
  obtain ⟨h1, h2⟩ := Classical.epsilon_spec
    (p := fun S' : Set InfiniteLattice.AmbientSpace =>
      S' ∈ g.cellSet ∧ E.proj '' S' = E.proj '' g.cell k)
    ⟨g.cell k, ⟨k, rfl⟩, rfl⟩
  change E.proj '' interior (g.liftCell (E.proj '' g.cell k)) = _
  change g.liftCell (E.proj '' g.cell k) ∈ g.cellSet at h1
  change E.proj '' g.liftCell (E.proj '' g.cell k) = _ at h2
  obtain ⟨k', hk'⟩ := h1
  rw [← hk'] at h2 ⊢
  exact (hsame k k').2.2 h2.symm
theorem continuous_signedConj (s : ℤˣ) : Continuous (Conventions.signedConj s : ℂ → ℂ) := by
  by_cases h : s = 1
  · have : (Conventions.signedConj s : ℂ → ℂ) = id :=
      funext fun z => by simp [Conventions.signedConj, h]
    rw [this]
    exact continuous_id
  · have : (Conventions.signedConj s : ℂ → ℂ) = starRingEnd ℂ :=
      funext fun z => by simp [Conventions.signedConj, h]
    rw [this]
    exact Complex.continuous_conj
theorem norm_signedConj (s : ℤˣ) (z : ℂ) : ‖Conventions.signedConj s z‖ = ‖z‖ := by apply _root_.YangMills.Construction.ChessboardTori.ChessboardBoundOnReflectionGrids.norm_signedConj <;> assumption
section CellProduct
variable {E : GridSetup} {g : ReflectionGrid E}
theorem measurable_torusTransport {r : E.Torus → E.Torus} (hr : MapsLinks E r)
    {C : Set E.Torus}
    {f : (g.torusCellLinks C → Conventions.StandingParameters.gaugeGroup) → ℂ}
    (hm : Measurable f)
    {F : (E.PeriodicLink → Matrices.ComplexMatrix2) → ℂ}
    (hF : ∀ U : PeriodicLattice.compactGaugeFields E.L E.m ((E.K : ℕ) : ℤ),
      F U.1 = f (g.torusCellRestrict C U)) :
    Measurable[borel E.torusFields]
      (fun U : E.torusFields => g.torusTransport r F U.1) := by
  let Φ : E.torusFields → E.torusFields :=
    fun U => ⟨E.pullbackField r U.1, pullbackField_mem hr U.2⟩
  have hpull : Continuous (E.pullbackField r) :=
    continuous_pi fun b => continuous_apply (E.imageLink r b)
  have hΦ : Continuous Φ := Continuous.subtype_mk (hpull.comp continuous_subtype_val) _
  have hρ : Continuous (g.torusCellRestrict C) :=
    continuous_pi fun b =>
      Continuous.subtype_mk ((continuous_apply b.1).comp continuous_subtype_val) _
  have e : (fun U : E.torusFields => g.torusTransport r F U.1) =
      fun U => Conventions.signedConj (g.torusSign r) (f (g.torusCellRestrict C (Φ U))) := by
    funext U
    change Conventions.signedConj _ (F (E.pullbackField r U.1)) = _
    rw [show F (E.pullbackField r U.1) = _ from hF (Φ U)]
  rw [e]
  let _ : MeasurableSpace E.torusFields := borel _
  have : BorelSpace E.torusFields := ⟨rfl⟩
  have hρm : Measurable (g.torusCellRestrict C) :=
    measurable_pi_lambda _ fun b => ((continuous_apply b).comp hρ).measurable
  exact (continuous_signedConj _).measurable.comp (hm.comp (hρm.comp hΦ.measurable))
theorem cellProduct_isBoundedBorel (hR : ChessboardTori.LiftingRules.Statement)
    (hQ : g.TorusGroupQuotient) (hpos : 0 < g.cellsAcross) {C : Set E.Torus}
    (hC : C ∈ g.torusCellSet) {F : (E.PeriodicLink → Matrices.ComplexMatrix2) → ℂ}
    (hF : F ∈ g.torusCellObservables C) :
    ReflectionPositivity.CutoffMirrors.IsBoundedBorel
      (fun U : E.torusFields => g.cellProduct C F U.1) := by
  have hfin : g.torusCellSet.Finite := by
    have hcard : Nat.card g.torusCellSet ≠ 0 := by
      intro h0
      have h := hQ.2.2.2.2.2.2.2
      rw [h0] at h
      have : (0 : ℝ) < g.cellsAcross ^ 4 := by positivity
      simp only [Nat.cast_zero] at h
      linarith
    have : Finite g.torusCellSet := Nat.finite_of_card_ne_zero hcard
    exact toFinite _
  obtain ⟨f, hm, ⟨c, hc⟩, hr⟩ := hF
  have e : (fun U : E.torusFields => g.cellProduct C F U.1) =
      fun U => ∏ C' ∈ hfin.toFinset, g.torusTransportTo C C' F U.1 :=
    funext fun U => finprod_mem_eq_finite_toFinset_prod _ hfin
  rw [e]
  refine ⟨?_, ∏ _C' ∈ hfin.toFinset, |c|, fun U => ?_⟩
  · let _ : MeasurableSpace E.torusFields := borel _
    refine Finset.measurable_prod _ fun C' hC' => ?_
    exact measurable_torusTransport (mapsLinks_of_mem_inducedTorusMaps hR
      (torusCarrier_spec hQ hC (hfin.mem_toFinset.1 hC')).1) hm hr
  · rw [norm_prod]
    refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun C' hC' => ?_
    have hex := mapsLinks_of_mem_inducedTorusMaps hR
      (torusCarrier_spec hQ hC (hfin.mem_toFinset.1 hC')).1
    change ‖Conventions.signedConj _ (F (E.pullbackField _ U.1))‖ ≤ _
    rw [norm_signedConj, hr ⟨_, pullbackField_mem hex U.2⟩]
    exact (hc _).trans (le_abs_self _)
end CellProduct
theorem periodicExpectation_congr (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement)
    {E : GridSetup} {A B : (E.PeriodicLink → Matrices.ComplexMatrix2) → ℂ}
    (h : ∀ U ∈ E.torusFields, A U = B U) :
    E.periodicExpectation A = E.periodicExpectation B := by
  have h1 : 1 < E.L := by
    have := E.isAdmissible.2
    omega
  have hnull := (hW E.L E.m E.K E.β h1 E.m.pos E.K.pos).2.2.2.2.2.2.2.2.1
  have hae : ∀ᵐ U ∂(PeriodicLattice.wilsonGibbsMeasure E.L E.m E.K E.β),
      U ∈ PeriodicLattice.compactGaugeFields E.L E.m ((E.K : ℕ) : ℤ) := by
    rw [ae_iff]
    exact hnull
  refine integral_congr_ae ?_
  filter_upwards [hae] with U hU using h U hU
variable {D : GridSetup} (S : ScalingMap D)
theorem image_torusSide :
    PeriodicLattice.torusSide S.image.L S.image.m =
      S.scale * PeriodicLattice.torusSide D.L D.m := by apply _root_.YangMills.SharedProofs.p15016 <;> assumption
theorem gridImage_cellSide (g : ReflectionGrid D) :
    (S.gridImage g).cellSide = S.scale * g.cellSide := by apply _root_.YangMills.Construction.MirrorGridsAllSides.ScalingProof.cellSide_gridImage <;> assumption
variable {S}
theorem torusLinkMap_imageLink (hb : Function.Bijective S.torusMap)
    (hl : ∀ b : D.PeriodicLink, S.IsLinkImage b (S.torusLinkMap b)) {r' : D.Torus → D.Torus}
    (hex : MapsLinks D r') (b : D.PeriodicLink) :
    S.torusLinkMap (D.imageLink r' b) =
      S.image.imageLink (S.conjTorus r') (S.torusLinkMap b) := by
  have hinv : ∀ z, S.torusInv (S.torusMap z) = z := Function.leftInverse_invFun hb.1
  obtain ⟨h1, h2⟩ := imageLink_endpoints hex b
  have ht : ((S.torusLinkMap (D.imageLink r' b)).source : S.image.Torus) =
      S.conjTorus r' (S.torusLinkMap b).source := by
    rw [(hl _).1, h1, (hl b).1]
    change _ = S.torusMap (r' (S.torusInv (S.torusMap b.source)))
    rw [hinv]
  have hh : ((S.torusLinkMap (D.imageLink r' b)).target : S.image.Torus) =
      S.conjTorus r' (S.torusLinkMap b).target := by
    rw [(hl _).2, h2, (hl b).2]
    change _ = S.torusMap (r' (S.torusInv (S.torusMap b.target)))
    rw [hinv]
  have hs := Classical.epsilon_spec (p := fun c : S.image.PeriodicLink =>
    (c.source : S.image.Torus) = S.conjTorus r' (S.torusLinkMap b).source ∧
      (c.target : S.image.Torus) = S.conjTorus r' (S.torusLinkMap b).target) ⟨_, ht, hh⟩
  exact periodicLink_ext_endpoints (ht.trans hs.1.symm) (hh.trans hs.2.symm)
theorem pullbackField_torusPullback (hb : Function.Bijective S.torusMap)
    (hl : ∀ b : D.PeriodicLink, S.IsLinkImage b (S.torusLinkMap b)) {r' : D.Torus → D.Torus}
    (hex : MapsLinks D r') (U' : S.image.PeriodicLink → Matrices.ComplexMatrix2) :
    D.pullbackField r' (S.torusPullback U') =
      S.torusPullback (S.image.pullbackField (S.conjTorus r') U') :=
  funext fun b => congrArg U' (torusLinkMap_imageLink hb hl hex b)
theorem torusMap_image_proj (hm : S.IsTorusLift S.torusMap)
    (A : Set InfiniteLattice.AmbientSpace) :
    S.torusMap '' (D.proj '' A) = S.image.proj '' (S.toFun '' A) := by
  rw [image_image, image_image]
  exact image_congr fun x _ => congrFun hm x
theorem conjTorus_image (hb : Function.Bijective S.torusMap) (r : D.Torus → D.Torus)
    (C : Set D.Torus) :
    S.conjTorus r '' (S.torusMap '' C) = S.torusMap '' (r '' C) := by
  have hinv : ∀ z, S.torusInv (S.torusMap z) = z := Function.leftInverse_invFun hb.1
  rw [image_image, image_image]
  refine image_congr fun x _ => ?_
  change S.torusMap (r (S.torusInv (S.torusMap x))) = _
  rw [hinv]
section Cells
variable {g : ReflectionGrid D}
theorem torusMap_image_torusCellInterior (hm : S.IsTorusLift S.torusMap)
    (hsame : g.SameTorusImageCriterion) (hsame' : (S.gridImage g).SameTorusImageCriterion)
    (hcell : ∀ k, S.toFun '' g.cell k = (S.gridImage g).cell k)
    (hint : ∀ k, S.toFun '' interior (g.cell k) = interior ((S.gridImage g).cell k))
    {C : Set D.Torus} (hC : C ∈ g.torusCellSet) :
    S.torusMap '' g.torusCellInterior C =
      (S.gridImage g).torusCellInterior (S.torusMap '' C) := by
  obtain ⟨_, ⟨k, rfl⟩, rfl⟩ := hC
  change S.torusMap '' g.torusCellInterior (D.proj '' g.cell k) =
    (S.gridImage g).torusCellInterior (S.torusMap '' (D.proj '' g.cell k))
  rw [torusCellInterior_proj_cell hsame, torusMap_image_proj hm, hint k, torusMap_image_proj hm,
    hcell k, torusCellInterior_proj_cell hsame']
theorem torusLinkMap_mem_torusCellLinks_iff (hb : Function.Bijective S.torusMap)
    (hl : ∀ b : D.PeriodicLink, S.IsLinkImage b (S.torusLinkMap b)) {C : Set D.Torus}
    (hopen : S.torusMap '' g.torusCellInterior C =
      (S.gridImage g).torusCellInterior (S.torusMap '' C))
    (b : D.PeriodicLink) :
    b ∈ g.torusCellLinks C ↔
      S.torusLinkMap b ∈ (S.gridImage g).torusCellLinks (S.torusMap '' C) := by
  change ((b.source : D.Torus) ∈ g.torusCellInterior C ∧
      (b.target : D.Torus) ∈ g.torusCellInterior C) ↔
    (((S.torusLinkMap b).source : S.image.Torus) ∈
        (S.gridImage g).torusCellInterior (S.torusMap '' C) ∧
      ((S.torusLinkMap b).target : S.image.Torus) ∈
        (S.gridImage g).torusCellInterior (S.torusMap '' C))
  rw [(hl b).1, (hl b).2, ← hopen, hb.1.mem_set_image, hb.1.mem_set_image]
theorem image_torusCellObservables (hτ : Function.Bijective S.torusLinkMap) {C : Set D.Torus}
    (hmem : ∀ b : D.PeriodicLink, b ∈ g.torusCellLinks C ↔
      S.torusLinkMap b ∈ (S.gridImage g).torusCellLinks (S.torusMap '' C))
    (hreal : ∀ U' ∈ S.image.torusFields, S.torusPullback U' ∈ D.torusFields)
    (honto : ∀ U ∈ D.torusFields, ∃ U' ∈ S.image.torusFields, S.torusPullback U' = U) :
    (fun F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ => F ∘ S.torusPullback) ''
        g.torusCellObservables C =
      (S.gridImage g).torusCellObservables (S.torusMap '' C) := by
  let τ : D.PeriodicLink ≃ S.image.PeriodicLink := Equiv.ofBijective _ hτ
  let e : g.torusCellLinks C ≃ (S.gridImage g).torusCellLinks (S.torusMap '' C) :=
    τ.subtypeEquiv hmem
  have hτ' : ∀ b, τ b = S.torusLinkMap b := fun _ => rfl
  ext F'
  constructor
  · rintro ⟨F, ⟨f, hm, ⟨c, hc⟩, hr⟩, rfl⟩
    refine ⟨fun u => f (u ∘ e), hm.comp (measurable_pi_lambda _ fun b => measurable_pi_apply _),
      ⟨c, fun u => hc _⟩, fun U' => ?_⟩
    exact hr ⟨S.torusPullback U'.1, hreal _ U'.2⟩
  · rintro ⟨f', hm', ⟨c, hc⟩, hr'⟩
    let Y : (D.PeriodicLink → Matrices.ComplexMatrix2) →
        S.image.PeriodicLink → Matrices.ComplexMatrix2 := fun U b' => U (τ.symm b')
    have hY : ∀ U', Y (S.torusPullback U') = U' := fun U' => funext fun b' => by
      change U' (S.torusLinkMap (τ.symm b')) = U' b'
      rw [← hτ', τ.apply_symm_apply]
    refine ⟨F' ∘ Y, ⟨fun u => f' (u ∘ e.symm),
      hm'.comp (measurable_pi_lambda _ fun b => measurable_pi_apply _), ⟨c, fun u => hc _⟩,
      fun U => ?_⟩, funext fun U' => ?_⟩
    · obtain ⟨U', hU', h⟩ := honto U.1 U.2
      have h1 : Y U.1 = U' := by rw [← h, hY]
      change F' (Y U.1) = _
      rw [h1]
      refine (hr' ⟨U', hU'⟩).trans (congrArg f' (funext fun b' => Subtype.ext ?_))
      change U' b'.1 = U.1 (e.symm b').1
      rw [← h]
      change _ = U' (τ (e.symm b').1)
      congr 1
      exact (congrArg Subtype.val (e.apply_symm_apply b')).symm
    · change F' (Y (S.torusPullback U')) = F' U'
      rw [hY]
theorem torusTransportTo_torusPullback (hb : Function.Bijective S.torusMap)
    (hl : ∀ b : D.PeriodicLink, S.IsLinkImage b (S.torusLinkMap b))
    (hR : ChessboardTori.LiftingRules.Statement)
    (hQ : g.TorusGroupQuotient) (hQ' : (S.gridImage g).TorusGroupQuotient)
    (hcells : (fun C : Set D.Torus => S.torusMap '' C) '' g.torusCellSet =
      (S.gridImage g).torusCellSet)
    (hmaps : ∀ r' ∈ g.inducedTorusMaps, S.conjTorus r' ∈ (S.gridImage g).inducedTorusMaps)
    (hsgn : ∀ r ∈ g.inducedTorusMaps,
      (S.gridImage g).torusSign (S.conjTorus r) = g.torusSign r)
    {C C' : Set D.Torus} (hC : C ∈ g.torusCellSet) (hC' : C' ∈ g.torusCellSet)
    (F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ)
    (U' : S.image.PeriodicLink → Matrices.ComplexMatrix2) :
    g.torusTransportTo C C' F (S.torusPullback U') =
      (S.gridImage g).torusTransportTo (S.torusMap '' C) (S.torusMap '' C')
        (F ∘ S.torusPullback) U' := by
  obtain ⟨hr, hrC⟩ := torusCarrier_spec hQ hC hC'
  have hTC : S.torusMap '' C ∈ (S.gridImage g).torusCellSet := hcells ▸ mem_image_of_mem _ hC
  have hTC' : S.torusMap '' C' ∈ (S.gridImage g).torusCellSet :=
    hcells ▸ mem_image_of_mem _ hC'
  have hcarry : (S.gridImage g).torusCarrier (S.torusMap '' C) (S.torusMap '' C') =
      S.conjTorus (g.torusCarrier C C') :=
    (hQ'.2.2.2.2.2.2.1 _ hTC _ hTC').unique (torusCarrier_spec hQ' hTC hTC')
      ⟨hmaps _ hr, by rw [conjTorus_image hb, hrC]⟩
  have hex := mapsLinks_of_mem_inducedTorusMaps hR hr
  rw [ReflectionGrid.torusTransportTo, ReflectionGrid.torusTransportTo, hcarry,
    ReflectionGrid.torusTransport, ReflectionGrid.torusTransport, hsgn _ hr]
  change Conventions.signedConj _ (F (D.pullbackField _ (S.torusPullback U'))) =
    Conventions.signedConj _ (F (S.torusPullback (S.image.pullbackField _ U')))
  rw [pullbackField_torusPullback hb hl hex]
end Cells
theorem holds (hT : ScalingPreservesTorus)
    (hC : ScalingPreservesCellsAndGroup)
    (hG : ScalingPreservesCellsAndGroupTorus)
    (hM : ScalingPreservesMeasures)
    (hQ : ChessboardTori.TorusReflectionGroup.Statement)
    (hP : ChessboardTori.CellsBlocksAndSigns.Statement)
    (hR : ChessboardTori.LiftingRules.Statement)
    (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement) :
    ScalingPreservesCellObservablesTorus := by
  intro D S g hs h2
  obtain ⟨-, hm, hb, -, -, hl, hτ, -⟩ := hT D S
  obtain ⟨hcell, hint, -⟩ := hC D S g hs
  obtain ⟨h2s, -, hN, hcells, ⟨hmaps, -, -⟩, -, hsgn⟩ := hG D S g hs h2
  obtain ⟨⟨h, hh⟩, -, -, -, -, hexp, -⟩ := hM D S
  have h2' : 2 * (S.gridImage g).cellSide ≤ PeriodicLattice.torusSide S.image.L S.image.m := by
    rw [image_torusSide, gridImage_cellSide]
    exact h2s
  have hQg := hQ D g h2
  have hQ' := hQ S.image (S.gridImage g) h2'
  have hsame := ((hP D g).2 h2).1
  have hsame' := ((hP S.image (S.gridImage g)).2 h2').1
  have hreal : ∀ U' ∈ S.image.torusFields, S.torusPullback U' ∈ D.torusFields :=
    fun U' hU' => by
      rw [← hh ⟨U', hU'⟩]
      exact (h ⟨U', hU'⟩).2
  have honto : ∀ U ∈ D.torusFields, ∃ U' ∈ S.image.torusFields, S.torusPullback U' = U :=
    fun U hU => by
      obtain ⟨U', hU'⟩ := h.surjective ⟨U, hU⟩
      exact ⟨U'.1, U'.2, by rw [← hh U', hU']⟩
  have hcopy := fun {C C' : Set D.Torus} (hC : C ∈ g.torusCellSet) (hC' : C' ∈ g.torusCellSet)
      (F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ)
      (U' : S.image.PeriodicLink → Matrices.ComplexMatrix2) =>
    torusTransportTo_torusPullback hb hl hR hQg hQ' hcells hmaps hsgn hC hC' F U'
  have hbij : BijOn (fun C : Set D.Torus => S.torusMap '' C) g.torusCellSet
      (S.gridImage g).torusCellSet :=
    ⟨fun C hC => hcells ▸ mem_image_of_mem _ hC, (image_injective.2 hb.1).injOn, hcells.ge⟩
  have harray : ∀ C ∈ g.torusCellSet, ∀ (F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ)
      (U' : S.image.PeriodicLink → Matrices.ComplexMatrix2),
      g.cellProduct C F (S.torusPullback U') =
        (S.gridImage g).cellProduct (S.torusMap '' C) (F ∘ S.torusPullback) U' :=
    fun C hC F U' => finprod_mem_eq_of_bijOn _ hbij fun C' hC' => hcopy hC hC' F U'
  have hpos : 0 < g.cellsAcross := by
    have h0 : 0 < g.cellSide := zpow_pos (by linarith [D.one_lt_factor]) _
    exact div_pos (by linarith) h0
  refine ⟨fun C hC => ?_, fun C hC C' hC' F _ U' _ => hcopy hC hC' F U',
    fun C hC F _ U' _ => harray C hC F U', fun C hC F hF => ?_⟩
  · exact image_torusCellObservables hτ (torusLinkMap_mem_torusCellLinks_iff hb hl
      (torusMap_image_torusCellInterior hm hsame hsame' hcell hint hC)) hreal honto
  · have h1 : D.periodicExpectation (g.cellProduct C F) =
        S.image.periodicExpectation (g.cellProduct C F ∘ S.torusPullback) :=
      hexp _ (cellProduct_isBoundedBorel hR hQg hpos hC hF)
    have h3 : S.image.periodicExpectation (g.cellProduct C F ∘ S.torusPullback) =
        S.image.periodicExpectation
          ((S.gridImage g).cellProduct (S.torusMap '' C) (F ∘ S.torusPullback)) :=
      periodicExpectation_congr hW fun U' _ => harray C hC F U'
    rw [ReflectionGrid.cellChessboardSeminorm, ReflectionGrid.cellChessboardSeminorm, h1, h3, hN]
end YangMills.Construction.MirrorGridsAllSides.CellObservablesTorus
end
