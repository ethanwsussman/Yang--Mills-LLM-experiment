import YangMills.Construction.ChessboardTori.ChessboardEstimateOnMirrorGridsProof
import YangMills.Construction.MirrorGridsOfEverySide.RulesOfTheCopiesOnTheTorusAtEveryMirrorGridProof
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction.ChessboardTori
open YangMills.Construction.InfiniteLattice (AmbientSpace)
namespace TorusChessboardSeminorms
variable {D : ChessboardSetup} {g : ReflectionGrid D}
abbrev compactSet (D : ChessboardSetup) : Set (D.PeriodicLink → Matrices.ComplexMatrix2) :=
  PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ)
abbrev gibbs (D : ChessboardSetup) : Measure (D.PeriodicLink → Matrices.ComplexMatrix2) :=
  PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.β
structure GridFacts (g : ReflectionGrid D) : Prop where
  quotient : g.TorusGroupQuotient
  coordForm : g.ReflectionGroupCoordForm
  transportRules : g.TransportRules
  lifted : ∀ S ∈ g.cellSet, ∀ F ∈ ReflectionGrid.cellObservables (D := D) S,
    D.liftedObservable F ∈ g.torusCellObservables (D.proj '' S)
  lifted_surj : ∀ S ∈ g.cellSet, ∀ F' ∈ g.torusCellObservables (D.proj '' S),
    ∃ F ∈ ReflectionGrid.cellObservables (D := D) S,
      D.AgreeOnCompactFields (D.liftedObservable F) F'
  transports : ∀ S ∈ g.cellSet, ∀ S' ∈ g.cellSet, ∀ F ∈ ReflectionGrid.cellObservables (D := D) S,
    D.AgreeOnCompactFields (D.liftedObservable (g.transportTo S S' F))
      (g.torusTransportTo (D.proj '' S) (D.proj '' S') (D.liftedObservable F))
  positivity : ∀ C ∈ g.torusCellSet, ∀ F ∈ g.torusCellObservables C,
    (D.periodicExpectation (g.torusProduct F)).im = 0 ∧
      0 ≤ (D.periodicExpectation (g.torusProduct F)).re ∧
      (∀ C' ∈ g.torusCellSet,
        g.torusChessboardNorm (g.torusTransportTo C C' F) = g.torusChessboardNorm F) ∧
      g.torusChessboardNorm F = g.torusChessboardNorm (fun U => starRingEnd ℂ (F U))
  chessboard : ∀ F : Set D.Torus → (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ,
    (∀ C ∈ g.torusCellSet, F C ∈ g.torusCellObservables C) →
      ‖D.periodicExpectation fun U => ∏ᶠ C ∈ g.torusCellSet, F C U‖ ≤
        ∏ᶠ C ∈ g.torusCellSet, g.torusChessboardNorm (F C)
  isProb : IsProbabilityMeasure (gibbs D)
  compact_ae : gibbs D (compactSet D)ᶜ = 0
theorem signedConj_mul (s : ℤˣ) (a b : ℂ) :
    Conventions.signedConj s (a * b) = Conventions.signedConj s a * Conventions.signedConj s b := by apply _root_.YangMills.Construction.MirrorGridsAllSides.TransportLaws.signedConj_mul <;> assumption
theorem signedConj_add (s : ℤˣ) (a b : ℂ) :
    Conventions.signedConj s (a + b) = Conventions.signedConj s a + Conventions.signedConj s b := by apply _root_.YangMills.Construction.MirrorGridsAllSides.TransportLaws.signedConj_add <;> assumption
theorem signedConj_one (s : ℤˣ) : Conventions.signedConj s 1 = 1 := by
  by_cases h : s = 1 <;> simp [Conventions.signedConj, h]
theorem signedConj_conj (s : ℤˣ) (a : ℂ) :
    Conventions.signedConj s (starRingEnd ℂ a) = starRingEnd ℂ (Conventions.signedConj s a) := by apply _root_.YangMills.Construction.MirrorGridsAllSides.TransportLaws.signedConj_starRingEnd <;> assumption
theorem norm_signedConj (s : ℤˣ) (a : ℂ) : ‖Conventions.signedConj s a‖ = ‖a‖ := by apply _root_.YangMills.Construction.ChessboardTori.ChessboardBoundOnReflectionGrids.norm_signedConj <;> assumption
theorem signedConj_exp_of_im_eq_zero (s : ℤˣ) {z : ℂ} (hz : z.im = 0) :
    Conventions.signedConj s (Complex.exp z) = Complex.exp z := by
  by_cases h : s = 1
  · simp [Conventions.signedConj, h]
  · simp only [Conventions.signedConj, if_neg h]
    rw [← Complex.exp_conj, Complex.conj_eq_iff_im.2 hz]
theorem transport_apply (a : D.Torus → D.Torus) (F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ)
    (U : D.PeriodicLink → Matrices.ComplexMatrix2) :
    g.torusTransport a F U = Conventions.signedConj (g.torusSign a) (F (D.pullbackField a U)) := rfl
theorem transport_add (a : D.Torus → D.Torus) (F F' : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ) :
    g.torusTransport a (F + F') = g.torusTransport a F + g.torusTransport a F' := by
  funext U
  simp only [Pi.add_apply, transport_apply, signedConj_add]
theorem transport_mul (a : D.Torus → D.Torus) (F F' : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ) :
    g.torusTransport a (F * F') = g.torusTransport a F * g.torusTransport a F' := by
  funext U
  simp only [Pi.mul_apply, transport_apply, signedConj_mul]
theorem transport_conj (a : D.Torus → D.Torus) (F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ) :
    g.torusTransport a (fun U => starRingEnd ℂ (F U)) =
      fun U => starRingEnd ℂ (g.torusTransport a F U) := by
  funext U
  simp only [transport_apply, signedConj_conj]
theorem transport_smul (a : D.Torus → D.Torus) (c : ℂ)
    (F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ) :
    g.torusTransport a (c • F) = Conventions.signedConj (g.torusSign a) c • g.torusTransport a F := by
  funext U
  simp only [Pi.smul_apply, smul_eq_mul, transport_apply, signedConj_mul]
theorem cellsAcross_pos (g : ReflectionGrid D) : 0 < g.cellsAcross := by apply _root_.YangMills.Construction.ChessboardTori.ChessboardBoundOnReflectionGrids.cellsAcross_pos <;> assumption
theorem inducedTorusMaps_finite (h : GridFacts g) : g.inducedTorusMaps.Finite := by
  have hne : Nat.card g.inducedTorusMaps ≠ 0 := by
    intro h0
    have h2 := h.quotient.2.1
    rw [h0] at h2
    have := cellsAcross_pos g
    simp only [Nat.cast_zero] at h2
    exact absurd h2.symm (by positivity)
  have := Nat.finite_of_card_ne_zero hne
  exact toFinite _
theorem torusCellSet_finite (h : GridFacts g) : g.torusCellSet.Finite := by
  have hne : Nat.card g.torusCellSet ≠ 0 := by
    intro h0
    have h2 := h.quotient.2.2.2.2.2.2.2
    rw [h0] at h2
    have := cellsAcross_pos g
    simp only [Nat.cast_zero] at h2
    exact absurd h2.symm (by positivity)
  have := Nat.finite_of_card_ne_zero hne
  exact toFinite _
theorem bijective_of_mem_inducedTorusMaps (h : GridFacts g) {a : D.Torus → D.Torus}
    (ha : a ∈ g.inducedTorusMaps) : Function.Bijective a := by
  obtain ⟨⟨φ, -, -, hrange⟩, -⟩ := h.quotient
  rw [← hrange] at ha
  obtain ⟨e, -, rfl⟩ := ha
  exact e.bijective
theorem proj_comp_inducingElement {a : D.Torus → D.Torus} (ha : a ∈ g.inducedTorusMaps) :
    D.proj ∘ (g.inducingElement a).1 = a ∘ D.proj := by apply _root_.YangMills.Construction.ChessboardTori.ChessboardBoundOnReflectionGrids.inducingElement_spec <;> assumption
theorem torusCarrier_spec (h : GridFacts g) {C C' : Set D.Torus} (hC : C ∈ g.torusCellSet)
    (hC' : C' ∈ g.torusCellSet) :
    g.torusCarrier C C' ∈ g.inducedTorusMaps ∧ g.torusCarrier C C' '' C = C' :=
  Classical.epsilon_spec (p := fun r' : D.Torus → D.Torus =>
    r' ∈ g.inducedTorusMaps ∧ r' '' C = C') (h.quotient.2.2.2.2.2.2.1 C hC C' hC').exists
theorem image_mem_torusCellSet (h : GridFacts g) {C : Set D.Torus} (hC : C ∈ g.torusCellSet)
    {a : D.Torus → D.Torus} (ha : a ∈ g.inducedTorusMaps) : a '' C ∈ g.torusCellSet :=
  h.quotient.2.2.2.2.2.1 a ha C hC
theorem torusCarrier_image (h : GridFacts g) {C : Set D.Torus} (hC : C ∈ g.torusCellSet)
    {a : D.Torus → D.Torus} (ha : a ∈ g.inducedTorusMaps) : g.torusCarrier C (a '' C) = a :=
  (h.quotient.2.2.2.2.2.2.1 C hC _ (image_mem_torusCellSet h hC ha)).unique
    (torusCarrier_spec h hC (image_mem_torusCellSet h hC ha)) ⟨ha, rfl⟩
theorem torusTransportTo_image (h : GridFacts g) {C : Set D.Torus} (hC : C ∈ g.torusCellSet)
    {a : D.Torus → D.Torus} (ha : a ∈ g.inducedTorusMaps)
    (F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ) :
    g.torusTransportTo C (a '' C) F = g.torusTransport a F := by
  rw [ReflectionGrid.torusTransportTo, torusCarrier_image h hC ha]
theorem bijOn_image_cell (h : GridFacts g) {C : Set D.Torus} (hC : C ∈ g.torusCellSet) :
    BijOn (fun a : D.Torus → D.Torus => a '' C) g.inducedTorusMaps g.torusCellSet := by
  refine ⟨fun a ha => image_mem_torusCellSet h hC ha, fun a ha b hb hab => ?_, fun C' hC' => ?_⟩
  · exact (h.quotient.2.2.2.2.2.2.1 C hC _ (image_mem_torusCellSet h hC ha)).unique ⟨ha, rfl⟩
      ⟨hb, hab.symm⟩
  · obtain ⟨a, ⟨ha, hi⟩, -⟩ := h.quotient.2.2.2.2.2.2.1 C hC C' hC'
    exact ⟨a, ha, hi⟩
theorem image_proj_image {a : D.Torus → D.Torus} (ha : a ∈ g.inducedTorusMaps)
    (S : Set AmbientSpace) :
    a '' (D.proj '' S) = D.proj '' ((g.inducingElement a).1 '' S) := by
  rw [← image_comp, ← proj_comp_inducingElement ha, image_comp]
def MapsLinks (D : ChessboardSetup) (r : D.Torus → D.Torus) : Prop :=
  ∀ b : D.PeriodicLink, ∃ b' : D.PeriodicLink,
    (b'.source : D.Torus) = r b.source ∧ (b'.target : D.Torus) = r b.target
theorem mapsLinks_of_mem (h : GridFacts g) {a : D.Torus → D.Torus} (ha : a ∈ g.inducedTorusMaps) :
    MapsLinks D a := by
  let D₂ : SourcesAndGluing.GluingSetup := ⟨D.toStandingParameters, D.β, D.beta_pos, 0⟩
  let R : SourcesAndGluing.GluingSetup.TorusLatticeIsometry D₂ :=
    ⟨a, ⟨bijective_of_mem_inducedTorusMaps h ha, h.quotient.2.2.1 a ha⟩,
      (h.quotient.2.2.2.2.1 a ha).1⟩
  exact fun b => ⟨R.linkMap b, rfl, rfl⟩
theorem imageLink_endpoints {r : D.Torus → D.Torus} (hr : MapsLinks D r) (b : D.PeriodicLink) :
    ((D.imageLink r b).source : D.Torus) = r b.source ∧
      ((D.imageLink r b).target : D.Torus) = r b.target :=
  Classical.epsilon_spec (hr b)
theorem bond_eq_of_endpoints {b b' : D.PeriodicLink} (ht : (b.source : D.Torus) = b'.source)
    (hh : (b.target : D.Torus) = b'.target) : b = b' := by apply _root_.YangMills.Construction.ChessboardTori.ChessboardBoundOnReflectionGrids.link_eq_of_ends <;> assumption
theorem pullbackField_mem_compactSet {r : D.Torus → D.Torus} (hr : MapsLinks D r)
    {U : D.PeriodicLink → Matrices.ComplexMatrix2} (hU : U ∈ compactSet D) :
    D.pullbackField r U ∈ compactSet D := by
  refine ⟨fun b _ => hU.1 _ (mem_univ _), fun b _ => ?_⟩
  change U (D.imageLink r b.opposite) = (U (D.imageLink r b))⁻¹
  have h1 : D.imageLink r b.opposite = (D.imageLink r b).opposite :=
    bond_eq_of_endpoints ((imageLink_endpoints hr _).1.trans (imageLink_endpoints hr b).2.symm)
      ((imageLink_endpoints hr _).2.trans (imageLink_endpoints hr b).1.symm)
  rw [h1]
  exact hU.2 _ (mem_univ _)
theorem transport_congr {a : D.Torus → D.Torus} (ha : MapsLinks D a)
    {F F' : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ} (hF : ∀ U ∈ compactSet D, F U = F' U) :
    ∀ U ∈ compactSet D, g.torusTransport a F U = g.torusTransport a F' U := by
  intro U hU
  rw [transport_apply, transport_apply, hF _ (pullbackField_mem_compactSet ha hU)]
theorem transportTo_congr (h : GridFacts g) {C C' : Set D.Torus} (hC : C ∈ g.torusCellSet)
    (hC' : C' ∈ g.torusCellSet) {F F' : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ}
    (hF : ∀ U ∈ compactSet D, F U = F' U) :
    ∀ U ∈ compactSet D, g.torusTransportTo C C' F U = g.torusTransportTo C C' F' U :=
  transport_congr (mapsLinks_of_mem h (torusCarrier_spec h hC hC').1) hF
theorem torusProduct_congr (h : GridFacts g) {F F' : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ}
    (hF : ∀ U ∈ compactSet D, F U = F' U) :
    ∀ U ∈ compactSet D, g.torusProduct F U = g.torusProduct F' U := by
  intro U hU
  exact finprod_mem_congr rfl fun a ha => transport_congr (mapsLinks_of_mem h ha) hF U hU
theorem ae_mem_compactSet (h : GridFacts g) : ∀ᵐ U ∂(gibbs D), U ∈ compactSet D := by
  rw [ae_iff]
  exact h.compact_ae
theorem periodicExpectation_congr (h : GridFacts g)
    {A B : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ}
    (hAB : ∀ U ∈ compactSet D, A U = B U) : D.periodicExpectation A = D.periodicExpectation B := by
  refine integral_congr_ae ?_
  filter_upwards [ae_mem_compactSet h] with U hU using hAB U hU
theorem torusChessboardNorm_congr (h : GridFacts g)
    {A B : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ}
    (hAB : ∀ U ∈ compactSet D, A U = B U) :
    g.torusChessboardNorm A = g.torusChessboardNorm B := by
  simp only [ReflectionGrid.torusChessboardNorm,
    periodicExpectation_congr h (torusProduct_congr h hAB)]
theorem mem_torusCellObservables_of_eq {C : Set D.Torus}
    {F F' : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ}
    (hF : F ∈ g.torusCellObservables C) (hFF : ∀ U ∈ compactSet D, F' U = F U) :
    F' ∈ g.torusCellObservables C := by
  obtain ⟨f, hm, hb, hrep⟩ := hF
  exact ⟨f, hm, hb, fun U => (hFF U.1 U.2).trans (hrep U)⟩
theorem one_mem_torusCellObservables (C : Set D.Torus) :
    (fun _ => (1 : ℂ)) ∈ g.torusCellObservables C :=
  ⟨fun _ => 1, measurable_const, ⟨1, fun _ => by simp⟩, fun _ => rfl⟩
theorem exp_mem_torusCellObservables {C : Set D.Torus}
    {H : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ}
    (hH : H ∈ g.torusCellObservables C) :
    (fun U => Complex.exp (H U)) ∈ g.torusCellObservables C := by
  obtain ⟨f, hm, ⟨c, hc⟩, hrep⟩ := hH
  refine ⟨fun w => Complex.exp (f w), Complex.measurable_exp.comp hm, ⟨Real.exp c, fun u => ?_⟩,
    fun U => ?_⟩
  · rw [Complex.norm_exp]
    exact Real.exp_le_exp.2 ((Complex.re_le_norm _).trans (hc u))
  · beta_reduce
    rw [hrep U]
theorem exists_measurable_bounded_representative (h : GridFacts g) {C : Set D.Torus}
    (hC : C ∈ g.torusCellSet) {F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ}
    (hF : F ∈ g.torusCellObservables C) :
    ∃ F' : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ, Measurable F' ∧
      (∃ c : ℝ, ∀ U, ‖F' U‖ ≤ c) ∧ ∀ U ∈ compactSet D, F' U = F U := by
  obtain ⟨S, hS, rfl⟩ := hC
  obtain ⟨F₀, ⟨f, hm, ⟨c, hc⟩, rfl⟩, hsame⟩ := h.lifted_surj S hS F hF
  refine ⟨D.liftedObservable (f ∘ ReflectionGrid.restrictField S), ?_, ⟨c, fun U => hc _⟩, hsame⟩
  have h1 : Measurable (ReflectionGrid.restrictField (D := D) S) := by
    refine measurable_pi_lambda _ fun b => Continuous.measurable ?_
    exact (continuous_apply b.1).comp continuous_subtype_val
  exact (hm.comp h1).comp (InfiniteLattice.measurable_liftField _ _ _)
theorem transportTo_eq_lifted (h : GridFacts g) {S S' : Set AmbientSpace} (hS : S ∈ g.cellSet)
    (hS' : S' ∈ g.cellSet) {F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ}
    {Ft : D.GaugeField → ℂ}
    (hFt : Ft ∈ ReflectionGrid.cellObservables (D := D) S)
    (hsame : D.AgreeOnCompactFields (D.liftedObservable Ft) F) :
    ∀ U ∈ compactSet D, g.torusTransportTo (D.proj '' S) (D.proj '' S') F U =
      D.liftedObservable (g.transportTo S S' Ft) U := by
  intro U hU
  rw [h.transports S hS S' hS' Ft hFt U hU]
  exact (transportTo_congr h ⟨S, hS, rfl⟩ ⟨S', hS', rfl⟩ hsame U hU).symm
theorem transportTo_mem (h : GridFacts g) {C : Set D.Torus} (hC : C ∈ g.torusCellSet)
    {a : D.Torus → D.Torus} (ha : a ∈ g.inducedTorusMaps)
    {F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ}
    (hF : F ∈ g.torusCellObservables C) :
    g.torusTransportTo C (a '' C) F ∈ g.torusCellObservables (a '' C) := by
  obtain ⟨S, hS, rfl⟩ := hC
  have hS' : (g.inducingElement a).1 '' S ∈ g.cellSet :=
    h.coordForm.2.2.2.2.2.1 _ (g.inducingElement a).2 S hS
  change g.torusTransportTo (D.proj '' S) _ F ∈ g.torusCellObservables _
  rw [image_proj_image ha S]
  obtain ⟨Ft, hFt, hsame⟩ := h.lifted_surj S hS F hF
  have m1 := (h.transportRules S hS _ hS' _ hS' (g.inducingElement a) rfl Ft hFt Ft hFt 0).1
  exact mem_torusCellObservables_of_eq (h.lifted _ hS' _ m1)
    (transportTo_eq_lifted h hS hS' hFt hsame)
theorem transportTo_transportTo (h : GridFacts g) {C C'' : Set D.Torus} (hC : C ∈ g.torusCellSet)
    (hC'' : C'' ∈ g.torusCellSet) {a : D.Torus → D.Torus} (ha : a ∈ g.inducedTorusMaps)
    {F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ} (hF : F ∈ g.torusCellObservables C) :
    ∀ U ∈ compactSet D, g.torusTransportTo (a '' C) C'' (g.torusTransportTo C (a '' C) F) U =
      g.torusTransportTo C C'' F U := by
  obtain ⟨S, hS, rfl⟩ := hC
  obtain ⟨S'', hS'', rfl⟩ := hC''
  have hS' : (g.inducingElement a).1 '' S ∈ g.cellSet :=
    h.coordForm.2.2.2.2.2.1 _ (g.inducingElement a).2 S hS
  change ∀ U ∈ compactSet D, g.torusTransportTo (a '' (D.proj '' S)) (D.proj '' S'')
    (g.torusTransportTo (D.proj '' S) (a '' (D.proj '' S)) F) U =
      g.torusTransportTo (D.proj '' S) (D.proj '' S'') F U
  rw [image_proj_image ha S]
  obtain ⟨Ft, hFt, hsame⟩ := h.lifted_surj S hS F hF
  have hr := h.transportRules S hS _ hS' S'' hS'' (g.inducingElement a) rfl Ft hFt Ft hFt 0
  intro U hU
  calc g.torusTransportTo (D.proj '' ((g.inducingElement a).1 '' S)) (D.proj '' S'')
        (g.torusTransportTo (D.proj '' S) (D.proj '' ((g.inducingElement a).1 '' S)) F) U
      = g.torusTransportTo (D.proj '' ((g.inducingElement a).1 '' S)) (D.proj '' S'')
          (D.liftedObservable (g.transportTo S ((g.inducingElement a).1 '' S) Ft)) U :=
        transportTo_congr h ⟨_, hS', rfl⟩ ⟨_, hS'', rfl⟩
          (transportTo_eq_lifted h hS hS' hFt hsame) U hU
    _ = D.liftedObservable (g.transportTo ((g.inducingElement a).1 '' S) S''
          (g.transportTo S ((g.inducingElement a).1 '' S) Ft)) U :=
        (h.transports _ hS' S'' hS'' _ hr.1 U hU).symm
    _ = D.liftedObservable (g.transportTo S S'' Ft) U := by rw [hr.2.2.1]
    _ = g.torusTransportTo (D.proj '' S) (D.proj '' S'') F U :=
        (transportTo_eq_lifted h hS hS'' hFt hsame U hU).symm
theorem torusChessboardNorm_eq_rpow {N : ℕ} (hN : (N : ℝ) = g.cellsAcross ^ 4)
    (F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ) :
    g.torusChessboardNorm F = ‖D.periodicExpectation (g.torusProduct F)‖ ^ (1 / (N : ℝ)) := by
  rw [ReflectionGrid.torusChessboardNorm, hN]
theorem pow_rpow_one_div {N : ℕ} (hN0 : (N : ℝ) ≠ 0) {c : ℝ} (hc : 0 ≤ c) :
    (c ^ N) ^ (1 / (N : ℝ)) = c := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hc, mul_one_div_cancel hN0, Real.rpow_one]
theorem torusChessboardNorm_le_of {N : ℕ} (hN : (N : ℝ) = g.cellsAcross ^ 4) (hN0 : (N : ℝ) ≠ 0)
    {F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ} {c : ℝ} (hc : 0 ≤ c)
    (hle : ‖D.periodicExpectation (g.torusProduct F)‖ ≤ c ^ N) : g.torusChessboardNorm F ≤ c := by
  rw [torusChessboardNorm_eq_rpow hN]
  calc ‖D.periodicExpectation (g.torusProduct F)‖ ^ (1 / (N : ℝ))
      ≤ (c ^ N) ^ (1 / (N : ℝ)) :=
        Real.rpow_le_rpow (norm_nonneg _) hle (by positivity)
    _ = c := pow_rpow_one_div hN0 hc
theorem torusChessboardNorm_nonneg (F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ) :
    0 ≤ g.torusChessboardNorm F :=
  Real.rpow_nonneg (norm_nonneg _) _
theorem periodicExpectation_const_mul (c : ℂ) (A : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ) :
    D.periodicExpectation (fun U => c * A U) = c * D.periodicExpectation A :=
  integral_const_mul c A
theorem torusChessboardNorm_smul (hfin : g.inducedTorusMaps.Finite)
    (hN : (hfin.toFinset.card : ℝ) = g.cellsAcross ^ 4) (hN0 : (hfin.toFinset.card : ℝ) ≠ 0)
    (c : ℂ) (F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ) :
    g.torusChessboardNorm (c • F) = ‖c‖ * g.torusChessboardNorm F := by
  have h1 : g.torusProduct (c • F) = fun U =>
      (∏ a ∈ hfin.toFinset, Conventions.signedConj (g.torusSign a) c) * g.torusProduct F U := by
    funext U
    simp only [ReflectionGrid.torusProduct]
    rw [finprod_mem_eq_finite_toFinset_prod _ hfin, finprod_mem_eq_finite_toFinset_prod _ hfin,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [transport_smul]
    rfl
  have h2 : ‖∏ a ∈ hfin.toFinset, Conventions.signedConj (g.torusSign a) c‖ =
      ‖c‖ ^ hfin.toFinset.card := by
    rw [norm_prod, Finset.prod_congr rfl fun a _ => norm_signedConj (g.torusSign a) c,
      Finset.prod_const]
  rw [torusChessboardNorm_eq_rpow hN, torusChessboardNorm_eq_rpow hN, h1,
    periodicExpectation_const_mul, norm_mul, h2,
    Real.mul_rpow (by positivity) (norm_nonneg _), pow_rpow_one_div hN0 (norm_nonneg _)]
theorem periodicExpectation_one (h : GridFacts g) :
    D.periodicExpectation (fun _ => (1 : ℂ)) = 1 := by
  have := h.isProb
  change ∫ _, (1 : ℂ) ∂(gibbs D) = 1
  simp
theorem torusProduct_one (h : GridFacts g) : g.torusProduct (fun _ => (1 : ℂ)) = fun _ => 1 := by
  funext U
  simp only [ReflectionGrid.torusProduct]
  rw [finprod_mem_eq_finite_toFinset_prod _ (inducedTorusMaps_finite h)]
  exact Finset.prod_eq_one fun a _ => signedConj_one _
theorem torusChessboardNorm_one (h : GridFacts g) : g.torusChessboardNorm (fun _ => (1 : ℂ)) = 1 := by
  simp only [ReflectionGrid.torusChessboardNorm, torusProduct_one h, periodicExpectation_one h]
  simp
theorem torusChessboardNorm_le_iSup (h : GridFacts g) {N : ℕ} (hfin : g.inducedTorusMaps.Finite)
    (hcard : hfin.toFinset.card = N) (hN : (N : ℝ) = g.cellsAcross ^ 4) (hN0 : (N : ℝ) ≠ 0)
    {C : Set D.Torus} {F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ}
    (hF : F ∈ g.torusCellObservables C) :
    g.torusChessboardNorm F ≤ ⨆ U : compactSet D, ‖F U.1‖ := by
  have := h.isProb
  obtain ⟨f, -, ⟨c, hc⟩, hrep⟩ := id hF
  have hbdd : BddAbove (range fun U : compactSet D => ‖F U.1‖) := by
    refine ⟨c, ?_⟩
    rintro _ ⟨U, rfl⟩
    change ‖F U.1‖ ≤ c
    rw [hrep U]
    exact hc _
  have hM : ∀ U ∈ compactSet D, ‖F U‖ ≤ ⨆ U : compactSet D, ‖F U.1‖ := fun U hU =>
    le_ciSup hbdd (⟨U, hU⟩ : compactSet D)
  have hM0 : 0 ≤ ⨆ U : compactSet D, ‖F U.1‖ := Real.iSup_nonneg fun _ => norm_nonneg _
  refine torusChessboardNorm_le_of hN hN0 hM0 ?_
  have hae : ∀ᵐ U ∂(gibbs D), ‖g.torusProduct F U‖ ≤ (⨆ U : compactSet D, ‖F U.1‖) ^ N := by
    filter_upwards [ae_mem_compactSet h] with U hU
    simp only [ReflectionGrid.torusProduct]
    rw [finprod_mem_eq_finite_toFinset_prod _ hfin, norm_prod, ← hcard, ← Finset.prod_const]
    refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun a ha => ?_
    rw [transport_apply, norm_signedConj]
    exact hM _ (pullbackField_mem_compactSet (mapsLinks_of_mem h (hfin.mem_toFinset.1 ha)) hU)
  have h1 := norm_integral_le_of_norm_le_const hae
  change ‖∫ U, g.torusProduct F U ∂(gibbs D)‖ ≤ _
  simpa using h1
theorem prod_ite_mem_subset {α M : Type*} [CommMonoid M] [DecidableEq α] (T Y : Finset α)
    (hY : Y ⊆ T) [DecidablePred (· ∈ Y)] (p q : α → M) :
    ∏ a ∈ T, (if a ∈ Y then p a else q a) = (∏ a ∈ Y, p a) * ∏ a ∈ T \ Y, q a := by
  rw [← Finset.prod_sdiff hY, mul_comm]
  congr 1
  · exact Finset.prod_congr rfl fun a ha => if_pos ha
  · exact Finset.prod_congr rfl fun a ha => if_neg (Finset.mem_sdiff.1 ha).2
open scoped Classical in
theorem norm_expectation_term_le (h : GridFacts g) {C : Set D.Torus} (hC : C ∈ g.torusCellSet)
    {F F' : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ} (hF : F ∈ g.torusCellObservables C)
    (hF' : F' ∈ g.torusCellObservables C) (hfin : g.inducedTorusMaps.Finite)
    {Y : Finset (D.Torus → D.Torus)} (hY : Y ⊆ hfin.toFinset) :
    ‖D.periodicExpectation fun U =>
        (∏ a ∈ Y, g.torusTransport a F U) * ∏ a ∈ hfin.toFinset \ Y, g.torusTransport a F' U‖ ≤
      (∏ _a ∈ Y, g.torusChessboardNorm F) *
        ∏ _a ∈ hfin.toFinset \ Y, g.torusChessboardNorm F' := by
  let Fam : Set D.Torus → (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ := fun C' =>
    if g.torusCarrier C C' ∈ Y then g.torusTransportTo C C' F else g.torusTransportTo C C' F'
  have hmem : ∀ C' ∈ g.torusCellSet, Fam C' ∈ g.torusCellObservables C' := by
    intro C' hC'
    obtain ⟨ha, hi⟩ := torusCarrier_spec h hC hC'
    have key : ∀ G ∈ g.torusCellObservables C,
        g.torusTransportTo C C' G ∈ g.torusCellObservables C' := by
      intro G hG
      have h1 := transportTo_mem h hC ha hG
      rwa [hi] at h1
    simp only [Fam]
    split_ifs
    · exact key F hF
    · exact key F' hF'
  have hbij := bijOn_image_cell h hC
  have hEach : ∀ a ∈ g.inducedTorusMaps,
      Fam (a '' C) = if a ∈ Y then g.torusTransport a F else g.torusTransport a F' := by
    intro a ha
    simp only [Fam, torusCarrier_image h hC ha, torusTransportTo_image h hC ha]
  have hVal : ∀ a ∈ g.inducedTorusMaps, g.torusChessboardNorm (Fam (a '' C)) =
      if a ∈ Y then g.torusChessboardNorm F else g.torusChessboardNorm F' := by
    intro a ha
    rw [hEach a ha]
    split_ifs
    · rw [← torusTransportTo_image h hC ha]
      exact (h.positivity C hC F hF).2.2.1 _ (image_mem_torusCellSet h hC ha)
    · rw [← torusTransportTo_image h hC ha]
      exact (h.positivity C hC F' hF').2.2.1 _ (image_mem_torusCellSet h hC ha)
  have hP : (fun U => ∏ᶠ C' ∈ g.torusCellSet, Fam C' U) = fun U =>
      (∏ a ∈ Y, g.torusTransport a F U) * ∏ a ∈ hfin.toFinset \ Y, g.torusTransport a F' U := by
    funext U
    have e : ∏ᶠ a ∈ g.inducedTorusMaps, Fam (a '' C) U = ∏ᶠ C' ∈ g.torusCellSet, Fam C' U :=
      finprod_mem_eq_of_bijOn (fun a => a '' C) hbij fun _ _ => rfl
    rw [← e, finprod_mem_eq_finite_toFinset_prod _ hfin,
      ← prod_ite_mem_subset hfin.toFinset Y hY (fun a => g.torusTransport a F U)
        (fun a => g.torusTransport a F' U)]
    refine Finset.prod_congr rfl fun a ha => ?_
    rw [hEach a (hfin.mem_toFinset.1 ha)]
    split_ifs <;> rfl
  have hV : ∏ᶠ C' ∈ g.torusCellSet, g.torusChessboardNorm (Fam C') =
      (∏ _a ∈ Y, g.torusChessboardNorm F) *
        ∏ _a ∈ hfin.toFinset \ Y, g.torusChessboardNorm F' := by
    have e : ∏ᶠ a ∈ g.inducedTorusMaps, g.torusChessboardNorm (Fam (a '' C)) =
        ∏ᶠ C' ∈ g.torusCellSet, g.torusChessboardNorm (Fam C') :=
      finprod_mem_eq_of_bijOn (fun a => a '' C) hbij fun _ _ => rfl
    rw [← e, finprod_mem_eq_finite_toFinset_prod _ hfin,
      ← prod_ite_mem_subset hfin.toFinset Y hY (fun _ => g.torusChessboardNorm F)
        (fun _ => g.torusChessboardNorm F')]
    exact Finset.prod_congr rfl fun a ha => hVal a (hfin.mem_toFinset.1 ha)
  have hest := h.chessboard Fam hmem
  rwa [hP, hV] at hest
theorem measurable_transport (r : D.Torus → D.Torus)
    {F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ}
    (hF : Measurable F) : Measurable (g.torusTransport r F) := by apply _root_.YangMills.Construction.ChessboardTori.ChessboardBoundOnReflectionGrids.measurable_torusTransport <;> assumption
theorem norm_prod_transport_le {F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ} {c : ℝ}
    (hc : ∀ U, ‖F U‖ ≤ c) (Y : Finset (D.Torus → D.Torus))
    (U : D.PeriodicLink → Matrices.ComplexMatrix2) :
    ‖∏ a ∈ Y, g.torusTransport a F U‖ ≤ ∏ _a ∈ Y, |c| := by
  rw [norm_prod]
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun a _ => ?_
  rw [transport_apply, norm_signedConj]
  exact (hc _).trans (le_abs_self _)
theorem integrable_of_norm_le (h : GridFacts g) {A : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ}
    (hm : Measurable A) {c : ℝ} (hc : ∀ U, ‖A U‖ ≤ c) : Integrable A (gibbs D) := by
  have := h.isProb
  exact Integrable.of_bound hm.aestronglyMeasurable c (Filter.Eventually.of_forall hc)
open scoped Classical in
theorem torusChessboardNorm_add_le_of_measurable (h : GridFacts g) {C : Set D.Torus}
    (hC : C ∈ g.torusCellSet)
    {F F' : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ} (hF : F ∈ g.torusCellObservables C)
    (hF' : F' ∈ g.torusCellObservables C) (hm : Measurable F) (hm' : Measurable F')
    {c c' : ℝ} (hc : ∀ U, ‖F U‖ ≤ c) (hc' : ∀ U, ‖F' U‖ ≤ c')
    (hfin : g.inducedTorusMaps.Finite)
    (hN : (hfin.toFinset.card : ℝ) = g.cellsAcross ^ 4) (hN0 : (hfin.toFinset.card : ℝ) ≠ 0) :
    g.torusChessboardNorm (F + F') ≤ g.torusChessboardNorm F + g.torusChessboardNorm F' := by
  have hexp : g.torusProduct (F + F') = fun U => ∑ Y ∈ hfin.toFinset.powerset,
      (∏ a ∈ Y, g.torusTransport a F U) * ∏ a ∈ hfin.toFinset \ Y, g.torusTransport a F' U := by
    funext U
    simp only [ReflectionGrid.torusProduct]
    rw [finprod_mem_eq_finite_toFinset_prod _ hfin]
    simp only [transport_add, Pi.add_apply]
    exact Finset.prod_add _ _ _
  have hint : ∀ Y ∈ hfin.toFinset.powerset, Integrable (fun U =>
      (∏ a ∈ Y, g.torusTransport a F U) * ∏ a ∈ hfin.toFinset \ Y, g.torusTransport a F' U)
      (gibbs D) := by
    intro Y _
    refine integrable_of_norm_le h (c := (∏ _a ∈ Y, |c|) * ∏ _a ∈ hfin.toFinset \ Y, |c'|)
      ((Finset.measurable_prod _ fun a _ => measurable_transport a hm).mul
        (Finset.measurable_prod _ fun a _ => measurable_transport a hm')) fun U => ?_
    rw [norm_mul]
    exact mul_le_mul (norm_prod_transport_le hc _ U) (norm_prod_transport_le hc' _ U)
      (norm_nonneg _) (Finset.prod_nonneg fun _ _ => abs_nonneg _)
  have hsum : D.periodicExpectation (g.torusProduct (F + F')) = ∑ Y ∈ hfin.toFinset.powerset,
      D.periodicExpectation fun U =>
        (∏ a ∈ Y, g.torusTransport a F U) * ∏ a ∈ hfin.toFinset \ Y, g.torusTransport a F' U := by
    rw [hexp]
    exact integral_finsetSum _ hint
  refine torusChessboardNorm_le_of hN hN0
    (add_nonneg (torusChessboardNorm_nonneg F) (torusChessboardNorm_nonneg F')) ?_
  rw [hsum]
  calc ‖∑ Y ∈ hfin.toFinset.powerset, D.periodicExpectation fun U =>
          (∏ a ∈ Y, g.torusTransport a F U) * ∏ a ∈ hfin.toFinset \ Y, g.torusTransport a F' U‖
      ≤ ∑ Y ∈ hfin.toFinset.powerset, ‖D.periodicExpectation fun U =>
          (∏ a ∈ Y, g.torusTransport a F U) * ∏ a ∈ hfin.toFinset \ Y, g.torusTransport a F' U‖ :=
        norm_sum_le _ _
    _ ≤ ∑ Y ∈ hfin.toFinset.powerset, (∏ _a ∈ Y, g.torusChessboardNorm F) *
          ∏ _a ∈ hfin.toFinset \ Y, g.torusChessboardNorm F' :=
        Finset.sum_le_sum fun Y hY =>
          norm_expectation_term_le h hC hF hF' hfin (Finset.mem_powerset.1 hY)
    _ = ∏ _a ∈ hfin.toFinset, (g.torusChessboardNorm F + g.torusChessboardNorm F') :=
        (Finset.prod_add _ _ _).symm
    _ = (g.torusChessboardNorm F + g.torusChessboardNorm F') ^ hfin.toFinset.card :=
        Finset.prod_const _
theorem torusChessboardNorm_add_le (h : GridFacts g) {C : Set D.Torus} (hC : C ∈ g.torusCellSet)
    {F F' : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ} (hF : F ∈ g.torusCellObservables C)
    (hF' : F' ∈ g.torusCellObservables C) (hfin : g.inducedTorusMaps.Finite)
    (hN : (hfin.toFinset.card : ℝ) = g.cellsAcross ^ 4) (hN0 : (hfin.toFinset.card : ℝ) ≠ 0) :
    g.torusChessboardNorm (F + F') ≤ g.torusChessboardNorm F + g.torusChessboardNorm F' := by
  obtain ⟨G, hm, ⟨c, hc⟩, hs⟩ := exists_measurable_bounded_representative h hC hF
  obtain ⟨G', hm', ⟨c', hc'⟩, hs'⟩ := exists_measurable_bounded_representative h hC hF'
  have e0 : g.torusChessboardNorm (F + F') = g.torusChessboardNorm (G + G') :=
    torusChessboardNorm_congr h fun U hU => by simp only [Pi.add_apply, hs U hU, hs' U hU]
  rw [e0, torusChessboardNorm_congr h
      (fun U hU => (hs U hU).symm : ∀ U ∈ compactSet D, F U = G U),
    torusChessboardNorm_congr h
      (fun U hU => (hs' U hU).symm : ∀ U ∈ compactSet D, F' U = G' U)]
  exact torusChessboardNorm_add_le_of_measurable h hC (mem_torusCellObservables_of_eq hF hs)
    (mem_torusCellObservables_of_eq hF' hs') hm hm' hc hc' hfin hN hN0
theorem norm_periodicExpectation_le (h : GridFacts g) {C : Set D.Torus} (hC : C ∈ g.torusCellSet)
    {F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ} (hF : F ∈ g.torusCellObservables C) :
    ‖D.periodicExpectation F‖ ≤ g.torusChessboardNorm F := by
  classical
  let Fam : Set D.Torus → (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ := fun C' =>
    if C' = C then F else fun _ => 1
  have hmem : ∀ C' ∈ g.torusCellSet, Fam C' ∈ g.torusCellObservables C' := by
    intro C' _
    by_cases hCC : C' = C
    · simp only [Fam, if_pos hCC]
      rw [hCC]
      exact hF
    · simp only [Fam, if_neg hCC]
      exact one_mem_torusCellObservables C'
  have hf := torusCellSet_finite h
  have hCm : C ∈ hf.toFinset := hf.mem_toFinset.2 hC
  have e1 : (fun U => ∏ᶠ C' ∈ g.torusCellSet, Fam C' U) = F := by
    funext U
    rw [finprod_mem_eq_finite_toFinset_prod _ hf,
      Finset.prod_eq_single_of_mem C hCm fun b _ hb => by simp only [Fam, if_neg hb]]
    simp only [Fam, if_true]
  have e2 : ∏ᶠ C' ∈ g.torusCellSet, g.torusChessboardNorm (Fam C') = g.torusChessboardNorm F := by
    rw [finprod_mem_eq_finite_toFinset_prod _ hf,
      Finset.prod_eq_single_of_mem C hCm fun b _ hb => by
        simp only [Fam, if_neg hb]
        exact torusChessboardNorm_one h]
    simp only [Fam, if_true]
  have hest := h.chessboard Fam hmem
  rwa [e1, e2] at hest
theorem torusProduct_exp (h : GridFacts g) (hfin : g.inducedTorusMaps.Finite)
    {H : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ}
    (hreal : ∀ U ∈ compactSet D, (H U).im = 0) :
    ∀ U ∈ compactSet D, g.torusProduct (fun V => Complex.exp (H V)) U =
      Complex.exp (∑ᶠ a ∈ g.inducedTorusMaps, D.pullbackObservable a H U) := by
  intro U hU
  simp only [ReflectionGrid.torusProduct]
  rw [finprod_mem_eq_finite_toFinset_prod _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    Complex.exp_sum]
  refine Finset.prod_congr rfl fun a ha => ?_
  rw [transport_apply]
  exact signedConj_exp_of_im_eq_zero _
    (hreal _ (pullbackField_mem_compactSet (mapsLinks_of_mem h (hfin.mem_toFinset.1 ha)) hU))
theorem re_periodicExpectation_exp_pos (h : GridFacts g) (hfin : g.inducedTorusMaps.Finite)
    {C : Set D.Torus} (hC : C ∈ g.torusCellSet)
    {H : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ} (hH : H ∈ g.torusCellObservables C)
    (hreal : ∀ U ∈ compactSet D, (H U).im = 0) :
    0 < (D.periodicExpectation fun U =>
      Complex.exp (∑ᶠ a ∈ g.inducedTorusMaps, D.pullbackObservable a H U)).re := by
  have := h.isProb
  obtain ⟨G, hm, ⟨c, hc⟩, hs⟩ := exists_measurable_bounded_representative h hC hH
  have hGreal : ∀ U ∈ compactSet D, (G U).im = 0 := fun U hU => by
    rw [hs U hU]; exact hreal U hU
  set A : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ :=
    g.torusProduct (fun V => Complex.exp (G V)) with hA
  have hAe : ∀ U ∈ compactSet D,
      Complex.exp (∑ᶠ a ∈ g.inducedTorusMaps, D.pullbackObservable a H U) = A U := by
    intro U hU
    rw [hA, ← torusProduct_exp h hfin hreal U hU]
    exact torusProduct_congr h (fun V hV => by simp only [hs V hV]) U hU |>.symm
  have hEmeas : Measurable fun V => Complex.exp (G V) := Complex.measurable_exp.comp hm
  have hAmeas : Measurable A := by
    have h1 : A = fun U =>
        ∏ a ∈ hfin.toFinset, g.torusTransport a (fun V => Complex.exp (G V)) U :=
      funext fun U => finprod_mem_eq_finite_toFinset_prod _ hfin
    rw [h1]
    exact Finset.measurable_prod _ fun a _ => measurable_transport a hEmeas
  have hEbound : ∀ U, ‖Complex.exp (G U)‖ ≤ Real.exp c := fun U => by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.2 ((Complex.re_le_norm _).trans (hc U))
  have hAint : Integrable A (gibbs D) := by
    refine integrable_of_norm_le h (c := ∏ _a ∈ hfin.toFinset, |Real.exp c|) hAmeas fun U => ?_
    have h1 : A U = ∏ a ∈ hfin.toFinset, g.torusTransport a (fun V => Complex.exp (G V)) U :=
      finprod_mem_eq_finite_toFinset_prod _ hfin
    rw [h1]
    exact norm_prod_transport_le hEbound _ U
  set δ : ℝ := Real.exp (-(∑ _a ∈ hfin.toFinset, c)) with hδ
  have hlow : ∀ U ∈ compactSet D, δ ≤ (A U).re := by
    intro U hU
    rw [hA, torusProduct_exp h hfin hGreal U hU, finsum_mem_eq_finite_toFinset_sum _ hfin]
    have him : (∑ a ∈ hfin.toFinset, D.pullbackObservable a G U).im = 0 := by
      rw [Complex.im_sum]
      refine Finset.sum_eq_zero fun a ha => ?_
      exact hGreal _
        (pullbackField_mem_compactSet (mapsLinks_of_mem h (hfin.mem_toFinset.1 ha)) hU)
    rw [Complex.exp_re, him, Real.cos_zero, mul_one]
    refine Real.exp_le_exp.2 ?_
    rw [Complex.re_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun a _ => ?_
    have h2 := (Complex.abs_re_le_norm (D.pullbackObservable a G U)).trans (hc _)
    exact (abs_le.1 h2).1
  have hre : (D.periodicExpectation A).re = ∫ U, (A U).re ∂(gibbs D) :=
    (Complex.reCLM.integral_comp_comm hAint).symm
  have hge : δ ≤ ∫ U, (A U).re ∂(gibbs D) := by
    have h3 : ∫ _U, δ ∂(gibbs D) ≤ ∫ U, (A U).re ∂(gibbs D) := by
      refine integral_mono_ae (integrable_const δ) (Complex.reCLM.integrable_comp hAint) ?_
      filter_upwards [ae_mem_compactSet h] with U hU using hlow U hU
    simpa using h3
  rw [periodicExpectation_congr h hAe, hre]
  exact (Real.exp_pos _).trans_le hge
theorem ofReal_norm_eq_of_im_eq_zero : ∀ z : ℂ, z.im = 0 → 0 ≤ z.re → ((‖z‖ : ℝ) : ℂ) = z := by
  rintro ⟨x, y⟩ him hre
  simp only at him hre
  subst him
  have e : (⟨x, 0⟩ : ℂ) = (x : ℂ) := rfl
  rw [e, Complex.norm_real, Real.norm_of_nonneg hre]
theorem gridFacts_of (hB : TorusReduction.Statement)
    (hE : GridBasicProperties.Statement)
    (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement)
    (g : ReflectionGrid D) (hside : 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m) :
    GridFacts g := by
  obtain ⟨b1, b2, -, -, -, b6, b7⟩ := hB D g hside
  have hEg := hE D g
  obtain ⟨-, hG, -⟩ := hEg.2.2.2.2.2.2 hside
  have hl : 1 < D.L := by
    have := D.isAdmissible.2
    omega
  have hw := hW D.L D.m D.K D.β hl D.m.pos D.K.pos
  exact ⟨hG, hEg.2.2.2.1, hEg.2.2.2.2.1, fun S hS => (b1 S hS).2.1,
    fun S hS => (b1 S hS).2.2.2.2, b2, b6, b7, hw.2.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.2.1⟩
end TorusChessboardSeminorms
theorem TorusChessboardSeminorms.proof
    (hB : TorusReduction.Statement)
    (hP : CellsBlocksAndSigns.Statement)
    (hE : GridBasicProperties.Statement)
    (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement) :
    TorusChessboardSeminorms.Statement := by
  open TorusChessboardSeminorms in
  intro D g hside C hC
  have h : GridFacts g := gridFacts_of hB hE hW g hside
  have hfin := inducedTorusMaps_finite h
  obtain ⟨S, hS, -⟩ := id hC
  have hhalf := ((((hP D g).2 hside).2 (g.block 0) ⟨0, rfl⟩).2 S hS).2
  have hncard := hhalf.2.2.1
  have hodd := hhalf.2.2.2
  have hN : (hfin.toFinset.card : ℝ) = g.cellsAcross ^ 4 := by
    rw [← Set.ncard_eq_toFinset_card _ hfin]
    exact hncard
  have hn0 : g.cellsAcross ^ 4 ≠ 0 := (pow_pos (cellsAcross_pos g) 4).ne'
  have hN0 : (hfin.toFinset.card : ℝ) ≠ 0 := by
    rw [hN]
    exact hn0
  refine ⟨?_, ⟨hncard, hodd⟩, ?_, torusChessboardNorm_one h, ?_⟩
  · intro F hF F' hF' lam a ha C'' hC''
    have e : ∀ G, g.torusTransportTo C (a '' C) G = g.torusTransport a G :=
      torusTransportTo_image h hC ha
    refine ⟨transportTo_mem h hC ha hF, ?_, ?_, ?_, ?_,
      transportTo_transportTo h hC hC'' ha hF⟩
    · intro U _
      simp only [e, transport_add]
    · intro U _
      simp only [e, transport_mul]
    · intro U _
      simp only [e, transport_conj]
    · intro U _
      simp only [e, transport_smul]
  · intro F hF F' hF' lam
    exact ⟨torusChessboardNorm_smul hfin hN hN0 lam F,
      torusChessboardNorm_add_le h hC hF hF' hfin hN hN0,
      ((h.positivity C hC F hF).2.2.2).symm,
      torusChessboardNorm_le_iSup h hfin rfl hN hN0 hF,
      norm_periodicExpectation_le h hC hF⟩
  · intro H hH hreal
    refine ⟨?_, re_periodicExpectation_exp_pos h hfin hC hH hreal⟩
    have hEq := periodicExpectation_congr h (torusProduct_exp h hfin hreal)
    obtain ⟨him, hre, -, -⟩ := h.positivity C hC _ (exp_mem_torusCellObservables hH)
    rw [← hEq, ReflectionGrid.torusChessboardNorm, ← Real.rpow_mul (norm_nonneg _),
      one_div_mul_cancel hn0, Real.rpow_one]
    exact ofReal_norm_eq_of_im_eq_zero _ him hre
end YangMills.Construction.ChessboardTori
end
