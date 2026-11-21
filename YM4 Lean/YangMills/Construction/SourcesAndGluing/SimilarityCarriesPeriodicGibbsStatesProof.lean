import YangMills.Construction.ChessboardTori.ObservablesMeasurableInASetAndTheirRestrictionToATorusProof
import YangMills.Construction.SourcesAndGluing.SimilarityCarriesPeriodicGibbsStates
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.SourcesAndGluing.RescalingGibbs
open InfiniteLattice
theorem condExp_comp_map_of_embedding {α γ : Type*} {mα : MeasurableSpace α} {m mγ : MeasurableSpace γ}
    {T : α → γ} (hT : MeasurableEmbedding T) (ν : Measure α) [IsFiniteMeasure ν] (hm : m ≤ mγ) {g : γ → ℝ} (hg : Integrable g (ν.map T)) :
    (ν.map T)[g|m] ∘ T =ᵐ[ν] ν[g ∘ T|m.comap T] := by
  have hm' : m.comap T ≤ mα := (MeasurableSpace.comap_mono hm).trans hT.measurable.comap_le
  have hmp : MeasurePreserving T ν (ν.map T) := hT.measurable.measurePreserving ν
  have hgT : Integrable (g ∘ T) ν := hT.integrable_map_iff.1 hg
  have hcT : Integrable ((ν.map T)[g|m] ∘ T) ν := hT.integrable_map_iff.1 integrable_condExp
  refine ae_eq_condExp_of_forall_setIntegral_eq hm' hgT (fun s _ _ => hcT.integrableOn) ?_ ?_
  · rintro _ ⟨t, ht, rfl⟩ _
    have h1 := hmp.setIntegral_preimage_emb hT ((ν.map T)[g|m]) t
    have h2 := hmp.setIntegral_preimage_emb hT g t
    simp only [Function.comp_apply]
    rw [h1, h2, setIntegral_condExp hm hg ht]
  · have hs : StronglyMeasurable[m] ((ν.map T)[g|m]) := stronglyMeasurable_condExp
    exact (hs.comp_measurable (comap_measurable T)).aestronglyMeasurable
structure LatticeBijection (a a' : ℝ) where
  onPoints : LatticePoint a ≃ LatticePoint a'
  linearPart : LatticePoint a ≃+ LatticePoint a'
  map_add : ∀ x v, onPoints (x + v) = onPoints x + linearPart v
  linearPart_axisStep : ∀ μ, linearPart (axisStep a μ) = axisStep a' μ
namespace LatticeBijection
variable {a a' : ℝ} (s : LatticeBijection a a')
def symm : LatticeBijection a' a where
  onPoints := s.onPoints.symm
  linearPart := s.linearPart.symm
  map_add x v := by
    apply s.onPoints.injective
    rw [s.map_add]
    simp
  linearPart_axisStep μ := by
    rw [AddEquiv.symm_apply_eq, s.linearPart_axisStep]
theorem map_axisStep (x : LatticePoint a) (μ : Fin 4) :
    s.onPoints (x + axisStep a μ) = s.onPoints x + axisStep a' μ := by
  rw [s.map_add, s.linearPart_axisStep]
theorem map_sub (x y : LatticePoint a) : s.onPoints y - s.onPoints x = s.linearPart (y - x) := by
  have h := s.map_add x (y - x)
  rw [add_sub_cancel] at h
  rw [h]
  abel
def link (c : Link a) : Link a' where
  initial := s.onPoints c.initial
  terminal := s.onPoints c.terminal
  isAdjacent := by
    obtain ⟨μ, h | h⟩ := c.isAdjacent
    · exact ⟨μ, Or.inl (by rw [s.map_sub, h, s.linearPart_axisStep])⟩
    · exact ⟨μ, Or.inr (by rw [s.map_sub, h, map_neg, s.linearPart_axisStep])⟩
theorem symm_link_link (c : Link a) : s.symm.link (s.link c) = c :=
  Link.ext (s.onPoints.symm_apply_apply _) (s.onPoints.symm_apply_apply _)
theorem link_symm_link (c : Link a') : s.link (s.symm.link c) = c :=
  Link.ext (s.onPoints.apply_symm_apply _) (s.onPoints.apply_symm_apply _)
def linkEquiv : Link a ≃ Link a' :=
  ⟨s.link, s.symm.link, s.symm_link_link, s.link_symm_link⟩
theorem link_opposite (c : Link a) : s.link c.opposite = (s.link c).opposite := rfl
theorem link_forwardFrom (x : LatticePoint a) (μ : Fin 4) :
    s.link (Link.forwardFrom x μ) = Link.forwardFrom (s.onPoints x) μ :=
  Link.ext rfl (s.map_axisStep x μ)
theorem link_isPositivelyOriented {c : Link a} (h : c.IsPositivelyOriented) :
    (s.link c).IsPositivelyOriented := by
  obtain ⟨μ, hμ⟩ := h
  refine ⟨μ, ?_⟩
  change s.onPoints c.terminal - s.onPoints c.initial = _
  rw [s.map_sub, hμ, s.linearPart_axisStep]
def face (p : ElementaryPlaquette a) : ElementaryPlaquette a' :=
  ⟨s.onPoints p.corner, p.lowAxis, p.highAxis, p.lowAxis_lt_highAxis⟩
def faceEquiv : ElementaryPlaquette a ≃ ElementaryPlaquette a' where
  toFun := s.face
  invFun := s.symm.face
  left_inv _ := ElementaryPlaquette.ext (s.onPoints.symm_apply_apply _) rfl rfl
  right_inv _ := ElementaryPlaquette.ext (s.onPoints.apply_symm_apply _) rfl rfl
theorem edges_face (p : ElementaryPlaquette a) :
    (s.face p).edges = p.edges.map s.link := by
  simp only [ElementaryPlaquette.edges, face, List.map_cons, List.map_nil, link_forwardFrom,
    map_axisStep]
theorem faceEnergy_face (W : Link a' → Matrices.ComplexMatrix2.specialUnitary)
    (p : ElementaryPlaquette a) :
    faceEnergy W (s.face p) = faceEnergy (W ∘ s.link) p := by
  simp only [faceEnergy, faceHolonomy, face, Function.comp_apply, link_forwardFrom,
    map_axisStep]
def pullback (U' : GaugeField a') : GaugeField a :=
  ⟨fun c => U' (s.link c), fun c => U'.2 (s.link c)⟩
theorem continuous_pullback : Continuous s.pullback := by
  have h : Continuous fun U' : GaugeField a' =>
      (fun c => U'.1 (s.link c) : Link a → Matrices.ComplexMatrix2.specialUnitary) :=
    continuous_pi fun c => (continuous_apply _).comp continuous_subtype_val
  exact h.subtype_mk fun U' => (s.pullback U').2
theorem pullback_symm_pullback (U : GaugeField a) : s.pullback (s.symm.pullback U) = U :=
  Subtype.ext (funext fun c => congrArg U.1 (s.symm_link_link c))
theorem symm_pullback_pullback (U' : GaugeField a') : s.symm.pullback (s.pullback U') = U' :=
  Subtype.ext (funext fun c => congrArg U'.1 (s.link_symm_link c))
def pullbackEquiv : GaugeField a' ≃ᵐ GaugeField a where
  toFun := s.pullback
  invFun := s.symm.pullback
  left_inv := s.symm_pullback_pullback
  right_inv := s.pullback_symm_pullback
  measurable_toFun := s.continuous_pullback.measurable
  measurable_invFun := s.symm.continuous_pullback.measurable
theorem measurableEmbedding_pullback : MeasurableEmbedding s.pullback :=
  s.pullbackEquiv.measurableEmbedding
def mapLinks (𝓛 : Finset (Link a)) : Finset (Link a') :=
  𝓛.map s.linkEquiv.toEmbedding
theorem link_mem_mapLinks (𝓛 : Finset (Link a)) (c : Link a) :
    s.link c ∈ s.mapLinks 𝓛 ↔ c ∈ 𝓛 :=
  Finset.mem_map' s.linkEquiv.toEmbedding
def finsetLinkEquiv (𝓛 : Finset (Link a)) : 𝓛 ≃ s.mapLinks 𝓛 :=
  s.linkEquiv.subtypeEquiv fun c => (s.link_mem_mapLinks 𝓛 c).symm
def transport (𝓛 : Finset (Link a)) :
    (𝓛 → Matrices.ComplexMatrix2.specialUnitary) ≃ᵐ
      (s.mapLinks 𝓛 → Matrices.ComplexMatrix2.specialUnitary) :=
  MeasurableEquiv.piCongrLeft (fun _ => Matrices.ComplexMatrix2.specialUnitary) (s.finsetLinkEquiv 𝓛)
theorem transport_apply (𝓛 : Finset (Link a)) (v : 𝓛 → Matrices.ComplexMatrix2.specialUnitary)
    (i : 𝓛) :
    s.transport 𝓛 v (s.finsetLinkEquiv 𝓛 i) = v i :=
  MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => Matrices.ComplexMatrix2.specialUnitary)
    (s.finsetLinkEquiv 𝓛) v i
theorem measurePreserving_transport (𝓛 : Finset (Link a)) :
    MeasurePreserving (s.transport 𝓛) (Matrices.ComplexMatrix2.haarPi 𝓛)
      (Matrices.ComplexMatrix2.haarPi (s.mapLinks 𝓛)) :=
  ⟨(s.transport 𝓛).measurable,
    Measure.infinitePi_map_piCongrLeft (μ := fun _ => Matrices.ComplexMatrix2.haarProb)
      (s.finsetLinkEquiv 𝓛)⟩
theorem transport_restrictTo (𝓛 : Finset (Link a)) (U' : GaugeField a') :
    s.transport 𝓛 (restrictTo 𝓛 (s.pullback U')) = restrictTo (s.mapLinks 𝓛) U' := by
  funext i'
  obtain ⟨i, rfl⟩ := (s.finsetLinkEquiv 𝓛).surjective i'
  rw [s.transport_apply]
  rfl
theorem patch_comp_link (𝓛 : Finset (Link a)) (v : 𝓛 → Matrices.ComplexMatrix2.specialUnitary)
    (U' : Link a' → Matrices.ComplexMatrix2.specialUnitary) :
    patch (s.mapLinks 𝓛) (s.transport 𝓛 v) U' ∘ s.link = patch 𝓛 v (U' ∘ s.link) := by
  funext c
  by_cases h : c ∈ 𝓛
  · have h' := (s.link_mem_mapLinks 𝓛 c).2 h
    simp only [Function.comp_apply, patch, dif_pos h, dif_pos h']
    exact s.transport_apply 𝓛 v ⟨c, h⟩
  · have h' := mt (s.link_mem_mapLinks 𝓛 c).1 h
    simp only [Function.comp_apply, patch, dif_neg h, dif_neg h']
theorem face_mem_facesTouching (𝓛 : Finset (Link a)) (p : ElementaryPlaquette a) :
    s.faceEquiv p ∈ facesTouching (s.mapLinks 𝓛) ↔ p ∈ facesTouching 𝓛 := by
  change (∃ b ∈ (s.face p).edges, b ∈ s.mapLinks 𝓛) ↔ ∃ b ∈ p.edges, b ∈ 𝓛
  rw [s.edges_face]
  constructor
  · rintro ⟨_, hb, hm⟩
    obtain ⟨b, hb', rfl⟩ := List.mem_map.1 hb
    exact ⟨b, hb', (s.link_mem_mapLinks 𝓛 b).1 hm⟩
  · rintro ⟨b, hb, hm⟩
    exact ⟨s.link b, List.mem_map.2 ⟨b, hb, rfl⟩, (s.link_mem_mapLinks 𝓛 b).2 hm⟩
theorem boltzmannWeight_pullback (β : ℝ) (𝓛 : Finset (Link a)) (U' : GaugeField a')
    (v : 𝓛 → Matrices.ComplexMatrix2.specialUnitary) :
    boltzmannWeight β 𝓛 (s.pullback U') v =
      boltzmannWeight β (s.mapLinks 𝓛) U' (s.transport 𝓛 v) := by
  have hsum : ∑ᶠ p ∈ facesTouching 𝓛, faceEnergy (patch 𝓛 v (s.pullback U')) p =
      ∑ᶠ p ∈ facesTouching (s.mapLinks 𝓛),
        faceEnergy (patch (s.mapLinks 𝓛) (s.transport 𝓛 v) U') p := by
    refine finsum_mem_eq_of_bijOn s.faceEquiv
      (s.faceEquiv.bijOn (s.face_mem_facesTouching 𝓛)) fun p _ => ?_
    change _ = faceEnergy _ (s.face p)
    rw [s.faceEnergy_face, s.patch_comp_link]
    rfl
  rw [boltzmannWeight, boltzmannWeight, hsum]
theorem partitionFunction_pullback (β : ℝ) (𝓛 : Finset (Link a)) (U' : GaugeField a') :
    partitionFunction β 𝓛 (s.pullback U') =
      partitionFunction β (s.mapLinks 𝓛) U' := by
  rw [partitionFunction, partitionFunction,
    ← (s.measurePreserving_transport 𝓛).integral_comp (s.transport 𝓛).measurableEmbedding]
  simp only [s.boltzmannWeight_pullback]
theorem wilsonSpecification_pullback (β : ℝ) (𝓛 : Finset (Link a)) (U' : GaugeField a')
    {B : Set (𝓛 → Matrices.ComplexMatrix2.specialUnitary)} (hB : MeasurableSet B) :
    wilsonSpecification β 𝓛 (s.pullback U') B =
      wilsonSpecification β (s.mapLinks 𝓛) U' ((s.transport 𝓛).symm ⁻¹' B) := by
  have hB' : MeasurableSet ((s.transport 𝓛).symm ⁻¹' B) := (s.transport 𝓛).symm.measurable hB
  have hpre : (s.transport 𝓛) ⁻¹' ((s.transport 𝓛).symm ⁻¹' B) = B := by
    ext v
    simp
  have h := (s.measurePreserving_transport 𝓛).setLIntegral_comp_preimage_emb
    (s.transport 𝓛).measurableEmbedding
    (fun v' => ENNReal.ofReal (boltzmannWeight β (s.mapLinks 𝓛) U' v'))
    ((s.transport 𝓛).symm ⁻¹' B)
  rw [hpre] at h
  simp only [← s.boltzmannWeight_pullback] at h
  rw [wilsonSpecification, wilsonSpecification, s.partitionFunction_pullback, Measure.smul_apply,
    Measure.smul_apply, withDensity_apply _ hB, withDensity_apply _ hB', h]
theorem comap_linkSigma (ℬ : Set (Link a)) :
    (linkSigma ℬ).comap s.pullback = linkSigma (s.link '' ℬ) := by
  simp only [linkSigma, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp, iSup_image]
  rfl
theorem comap_exteriorSigma (𝓛 : Finset (Link a)) :
    (exteriorSigma 𝓛).comap s.pullback = exteriorSigma (s.mapLinks 𝓛) := by
  rw [exteriorSigma, exteriorSigma, s.comap_linkSigma]
  congr 1
  ext c'
  obtain ⟨c, rfl⟩ := s.linkEquiv.surjective c'
  change s.link c ∈ s.link '' _ ↔ s.link c ∉ _ ∧ (s.link c).opposite ∉ _
  rw [s.linkEquiv.injective.mem_set_image (f := s.link), ← s.link_opposite,
    s.link_mem_mapLinks, s.link_mem_mapLinks]
  rfl
end LatticeBijection
section Fields
variable {a : ℝ}
theorem measurable_evalLink (c : Link a) : Measurable fun U : GaugeField a => U c := by apply _root_.YangMills.Construction.ChessboardTori.MeasurableObservables.measurable_link_eval <;> assumption
theorem exteriorSigma_le (𝓛 : Finset (Link a)) :
    exteriorSigma 𝓛 ≤ (inferInstance : MeasurableSpace (GaugeField a)) :=
  iSup₂_le fun c _ => (measurable_evalLink c).comap_le
theorem measurable_restrictTo (𝓛 : Finset (Link a)) :
    Measurable (restrictTo 𝓛 : GaugeField a → 𝓛 → Matrices.ComplexMatrix2.specialUnitary) :=
  measurable_pi_lambda _ fun c => measurable_evalLink c.1
end Fields
namespace LatticeBijection
variable {a a' : ℝ} (s : LatticeBijection a a')
theorem isGibbs_map {β : ℝ} {ν : Measure (GaugeField a')} (h : IsGibbs β ν) :
    IsGibbs β (ν.map s.pullback) := by
  obtain ⟨hp, hν⟩ := h
  refine ⟨Measure.isProbabilityMeasure_map s.continuous_pullback.measurable.aemeasurable,
    fun 𝓛 hL B hB => ?_⟩
  have hL' : ∀ c ∈ s.mapLinks 𝓛, c.IsPositivelyOriented := by
    intro c hc
    obtain ⟨c₀, hc₀, rfl⟩ := Finset.mem_map.1 hc
    exact s.link_isPositivelyOriented (hL c₀ hc₀)
  have hB' : MeasurableSet ((s.transport 𝓛).symm ⁻¹' B) := (s.transport 𝓛).symm.measurable hB
  have h1 := hν (s.mapLinks 𝓛) hL' _ hB'
  have hint : Integrable ((restrictTo 𝓛 ⁻¹' B).indicator fun _ => (1 : ℝ)) (ν.map s.pullback) :=
    (integrable_const 1).indicator (measurable_restrictTo 𝓛 hB)
  have h2 := condExp_comp_map_of_embedding s.measurableEmbedding_pullback ν (exteriorSigma_le 𝓛) hint
  have hcomp : ((restrictTo 𝓛 ⁻¹' B).indicator fun _ => (1 : ℝ)) ∘ s.pullback =
      (restrictTo (s.mapLinks 𝓛) ⁻¹' ((s.transport 𝓛).symm ⁻¹' B)).indicator
        fun _ => (1 : ℝ) := by
    funext U'
    have hmem : s.pullback U' ∈ restrictTo 𝓛 ⁻¹' B ↔
        U' ∈ restrictTo (s.mapLinks 𝓛) ⁻¹' ((s.transport 𝓛).symm ⁻¹' B) := by
      change restrictTo 𝓛 (s.pullback U') ∈ B ↔
        (s.transport 𝓛).symm (restrictTo (s.mapLinks 𝓛) U') ∈ B
      rw [← s.transport_restrictTo, MeasurableEquiv.symm_apply_apply]
    by_cases hU : U' ∈ restrictTo (s.mapLinks 𝓛) ⁻¹' ((s.transport 𝓛).symm ⁻¹' B)
    · rw [Function.comp_apply, indicator_of_mem (hmem.2 hU), indicator_of_mem hU]
    · rw [Function.comp_apply, indicator_of_notMem (mt hmem.1 hU), indicator_of_notMem hU]
  rw [hcomp, s.comap_exteriorSigma] at h2
  have h3 : ∀ᵐ U' ∂ν, (wilsonSpecification β 𝓛 (s.pullback U') B).toReal =
      ((ν.map s.pullback)[(restrictTo 𝓛 ⁻¹' B).indicator fun _ => (1 : ℝ)|exteriorSigma 𝓛])
        (s.pullback U') := by
    filter_upwards [h1, h2] with U' e1 e2
    exact (congrArg ENNReal.toReal (s.wilsonSpecification_pullback β 𝓛 U' hB)).trans
      (e1.trans e2.symm)
  exact s.measurableEmbedding_pullback.ae_map_iff.2 h3
theorem pullbackField_shift_pullback (v : LatticePoint a) (U' : GaugeField a') :
    (shift v).pullbackField (s.pullback U') =
      s.pullback ((shift (s.linearPart v)).pullbackField U') := by
  refine Subtype.ext (funext fun c => congrArg U'.1 ?_)
  exact Link.ext (s.map_add _ _) (s.map_add _ _)
theorem isPeriodicMeasure_map {ν : Measure (GaugeField a')} (h : IsPeriodicMeasure ν) :
    IsPeriodicMeasure (ν.map s.pullback) := by
  obtain ⟨H, hH, hinv⟩ := h
  refine ⟨H.comap (s.linearPart : LatticePoint a →+ LatticePoint a'), ⟨?_⟩, fun v hv A hA => ?_⟩
  · rw [AddSubgroup.index_comap_of_surjective _ s.linearPart.surjective]
    exact hH.index_ne_zero
  · have hA' : IsBoundedObservable (A ∘ s.pullback) := by
      obtain ⟨C, hC⟩ := hA.2
      exact ⟨hA.1.comp s.continuous_pullback.measurable, C, fun U => hC _⟩
    have h := hinv (s.linearPart v) hv (A ∘ s.pullback) hA'
    rw [s.measurableEmbedding_pullback.integral_map, s.measurableEmbedding_pullback.integral_map]
    refine Eq.trans ?_ h
    refine integral_congr_ae (Filter.Eventually.of_forall fun U' => ?_)
    exact congrArg A (s.pullbackField_shift_pullback v U')
theorem isPeriodicGibbs_map {β : ℝ} {ν : Measure (GaugeField a')}
    (h : IsPeriodicGibbs β ν) : IsPeriodicGibbs β (ν.map s.pullback) :=
  ⟨s.isGibbs_map h.1, s.isPeriodicMeasure_map h.2⟩
end LatticeBijection
variable {D : GluingSetup} (Ψ : LatticeRescaling D)
def scaleIso : LatticePoint D.mesh ≃+ LatticePoint Ψ.scaleExponent.target.mesh where
  toFun v := ⟨(D.L : ℝ) ^ Ψ.exp • (v : AmbientSpace), by
    obtain ⟨n, hn⟩ := v.2
    refine ⟨n, fun μ => ?_⟩
    rw [Ψ.target_mesh_eq, Pi.smul_apply, hn μ, smul_eq_mul]
    ring⟩
  invFun w := ⟨((D.L : ℝ) ^ Ψ.exp)⁻¹ • (w : AmbientSpace), by
    obtain ⟨n, hn⟩ := w.2
    refine ⟨n, fun μ => ?_⟩
    rw [Pi.smul_apply, hn μ, Ψ.target_mesh_eq, smul_eq_mul, mul_left_comm,
      inv_mul_cancel_left₀ Ψ.zpow_L_pos.ne']⟩
  left_inv v := Subtype.ext (inv_smul_smul₀ Ψ.zpow_L_pos.ne' _)
  right_inv w := Subtype.ext (smul_inv_smul₀ Ψ.zpow_L_pos.ne' _)
  map_add' x y := Subtype.ext (smul_add _ _ _)
def rescalingBijection : LatticeBijection D.mesh Ψ.scaleExponent.target.mesh where
  onPoints := (Equiv.addRight (⟨Ψ.base, Ψ.base_mem⟩ : LatticePoint D.mesh)).trans (scaleIso Ψ).toEquiv
  linearPart := scaleIso Ψ
  map_add x v := by
    change scaleIso Ψ (x + v + _) = scaleIso Ψ (x + _) + scaleIso Ψ v
    rw [← map_add, add_right_comm]
  linearPart_axisStep μ := by
    refine Subtype.ext ?_
    change (D.L : ℝ) ^ Ψ.exp • (Pi.single μ D.mesh : AmbientSpace) =
      Pi.single μ Ψ.scaleExponent.target.mesh
    rw [Ψ.target_mesh_eq, ← Pi.single_smul, smul_eq_mul]
theorem rescalingBijection_apply (x : LatticePoint D.mesh) :
    (rescalingBijection Ψ).onPoints x = Ψ.toMotion.onPoint x :=
  Subtype.ext (congrFun Ψ.toMotion_onSpace x).symm
theorem pullback_rescalingBijection : (rescalingBijection Ψ).pullback = Ψ.pull := by
  funext U'
  refine Subtype.ext (funext fun c => congrArg U'.1 ?_)
  exact Link.ext (rescalingBijection_apply Ψ _) (rescalingBijection_apply Ψ _)
theorem pullInv_eq : Ψ.pullInv = (rescalingBijection Ψ).symm.pullback := by
  funext U
  have hinj : Function.Injective Ψ.pull := by
    rw [← pullback_rescalingBijection]
    exact (rescalingBijection Ψ).measurableEmbedding_pullback.injective
  have : Nonempty Ψ.scaleExponent.target.GridField :=
    ⟨(rescalingBijection Ψ).symm.pullback U⟩
  have h : Function.invFun Ψ.pull (Ψ.pull ((rescalingBijection Ψ).symm.pullback U)) =
      (rescalingBijection Ψ).symm.pullback U := Function.leftInverse_invFun hinj _
  have h2 : Ψ.pull ((rescalingBijection Ψ).symm.pullback U) = U := by
    rw [← pullback_rescalingBijection]
    exact (rescalingBijection Ψ).pullback_symm_pullback U
  rw [h2] at h
  exact h
theorem rescalingGibbsClaim_holds : RescalingGibbsClaim := by
  intro D Ψ ν _
  have himage : Ψ.pushMeasure ν = ν.map (rescalingBijection Ψ).symm.pullback := by
    rw [LatticeRescaling.pushMeasure, pullInv_eq]
  have hback : (Ψ.pushMeasure ν).map (rescalingBijection Ψ).pullback = ν := by
    have hid : (rescalingBijection Ψ).pullback ∘ (rescalingBijection Ψ).symm.pullback = id :=
      funext (rescalingBijection Ψ).pullback_symm_pullback
    rw [himage, Measure.map_map (rescalingBijection Ψ).continuous_pullback.measurable
      (rescalingBijection Ψ).symm.continuous_pullback.measurable, hid, Measure.map_id]
  constructor
  · intro h
    have h' : IsPeriodicGibbs D.β ν := h
    have h2 := (rescalingBijection Ψ).symm.isPeriodicGibbs_map h'
    rw [himage]
    exact h2
  · intro h
    have h' : IsPeriodicGibbs D.β (Ψ.pushMeasure ν) := h
    have h2 := (rescalingBijection Ψ).isPeriodicGibbs_map h'
    rw [hback] at h2
    exact h2
end YangMills.Construction.SourcesAndGluing.RescalingGibbs
end
