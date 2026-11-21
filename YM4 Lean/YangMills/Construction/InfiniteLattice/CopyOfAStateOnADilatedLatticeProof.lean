import YangMills.Construction.ChessboardTori.ObservablesMeasurableInASetAndTheirRestrictionToATorusProof
import YangMills.Construction.InfiniteLattice.ActionOfTheLatticeIsometriesOnConfigurationsAndFunctionsProof
import YangMills.Construction.InfiniteLattice.CopyOfAStateOnADilatedLattice
import YangMills.Construction.Lattice.ConfigurationsAreAProduct
import Mathlib
set_option autoImplicit false
open MeasureTheory Set YangMills.Construction.InfiniteLattice
open YangMills.Construction.Matrices.ComplexMatrix2 (specialUnitary haarPi)
noncomputable section
namespace YangMills.Construction.InfiniteLattice.Dilation
variable {a c lam : ℝ}
theorem pointScale_add (hc : c = lam * a) (x y : LatticePoint a) :
    pointScale lam hc (x + y) = pointScale lam hc x + pointScale lam hc y :=
  Subtype.ext (smul_add lam (x : AmbientSpace) y)
theorem pointScale_inv_pointScale (hlam : 0 < lam) (hc : c = lam * a) (x : LatticePoint a) :
    pointScale lam⁻¹ (spacing_eq_inv_mul hlam hc) (pointScale lam hc x) = x :=
  Subtype.ext (by simp [pointScale, smul_smul, inv_mul_cancel₀ hlam.ne'])
theorem pointScale_pointScale_inv (hlam : 0 < lam) (hc : c = lam * a) (x : LatticePoint c) :
    pointScale lam hc (pointScale lam⁻¹ (spacing_eq_inv_mul hlam hc) x) = x :=
  Subtype.ext (by simp [pointScale, smul_smul, mul_inv_cancel₀ hlam.ne'])
def pointScaleAddEquiv (hlam : 0 < lam) (hc : c = lam * a) : LatticePoint a ≃+ LatticePoint c where
  toFun := pointScale lam hc
  invFun := pointScale lam⁻¹ (spacing_eq_inv_mul hlam hc)
  left_inv := pointScale_inv_pointScale hlam hc
  right_inv := pointScale_pointScale_inv hlam hc
  map_add' := pointScale_add hc
def linkScaleEquiv (hlam : 0 < lam) (hc : c = lam * a) : Link a ≃ Link c where
  toFun := linkScale lam hc
  invFun := linkScale lam⁻¹ (spacing_eq_inv_mul hlam hc)
  left_inv := linkScale_inv_linkScale hlam hc
  right_inv := linkScale_linkScale_inv hlam hc
def plaquetteScaleEquiv (hlam : 0 < lam) (hc : c = lam * a) :
    ElementaryPlaquette a ≃ ElementaryPlaquette c where
  toFun := plaquetteScale lam hc
  invFun := plaquetteScale lam⁻¹ (spacing_eq_inv_mul hlam hc)
  left_inv p := ElementaryPlaquette.ext (pointScale_inv_pointScale hlam hc p.corner) rfl rfl
  right_inv p := ElementaryPlaquette.ext (pointScale_pointScale_inv hlam hc p.corner) rfl rfl
theorem linkScale_forwardFrom (hc : c = lam * a) (x : LatticePoint a) (μ : Fin 4) :
    linkScale lam hc (Link.forwardFrom x μ) = Link.forwardFrom (pointScale lam hc x) μ := by
  apply Link.ext
  · rfl
  · change pointScale lam hc (x + axisStep a μ) = pointScale lam hc x + axisStep c μ
    rw [pointScale_add, pointScale_axisStep]
theorem isPositivelyOriented_linkScale (hlam : 0 < lam) (hc : c = lam * a) (b : Link a) :
    (linkScale lam hc b).IsPositivelyOriented ↔ b.IsPositivelyOriented := by
  constructor
  · rintro ⟨μ, h⟩
    refine ⟨μ, (pointScaleAddEquiv hlam hc).injective ?_⟩
    change pointScale lam hc (b.terminal - b.initial) = pointScale lam hc (axisStep a μ)
    rw [pointScale_sub, pointScale_axisStep]
    exact h
  · rintro ⟨μ, h⟩
    refine ⟨μ, ?_⟩
    change pointScale lam hc b.terminal - pointScale lam hc b.initial = axisStep c μ
    rw [← pointScale_sub, h, pointScale_axisStep]
theorem edges_plaquetteScale (hc : c = lam * a) (p : ElementaryPlaquette a) :
    (plaquetteScale lam hc p).edges = p.edges.map (linkScale lam hc) := by
  simp [ElementaryPlaquette.edges, plaquetteScale, linkScale_forwardFrom, pointScale_add,
    pointScale_axisStep]
theorem center_plaquetteScale (hc : c = lam * a) (p : ElementaryPlaquette a) :
    (plaquetteScale lam hc p).center = lam • p.center := by
  have key : ∀ μ : Fin 4, (Pi.single μ (c / 2) : AmbientSpace) = lam • Pi.single μ (a / 2) :=
    fun μ => by
      rw [← Pi.single_smul, smul_eq_mul, hc]
      congr 1
      ring
  change lam • (p.corner : AmbientSpace) + Pi.single p.lowAxis (c / 2) +
      Pi.single p.highAxis (c / 2) =
    lam • ((p.corner : AmbientSpace) + Pi.single p.lowAxis (a / 2) + Pi.single p.highAxis (a / 2))
  rw [key, key, smul_add, smul_add]
theorem scaleBijectsCells (hlam : 0 < lam) (hc : c = lam * a) :
    ScaleBijectsCells lam hc := by
  refine ⟨(pointScaleAddEquiv hlam hc).bijective, (linkScaleEquiv hlam hc).bijective, ?_,
    fun b => linkScale_opposite hc b, (plaquetteScaleEquiv hlam hc).bijective,
    fun p => ⟨edges_plaquetteScale hc p, center_plaquetteScale hc p⟩⟩
  ext b'
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact (isPositivelyOriented_linkScale hlam hc b).2 hb
  · intro hb'
    refine ⟨(linkScaleEquiv hlam hc).symm b', (isPositivelyOriented_linkScale hlam hc _).1 ?_,
      (linkScaleEquiv hlam hc).apply_symm_apply b'⟩
    rw [show linkScale lam hc ((linkScaleEquiv hlam hc).symm b') = b' from
      (linkScaleEquiv hlam hc).apply_symm_apply b']
    exact hb'
theorem faceHolonomy_plaquetteScale (hc : c = lam * a) {W' : Link c → specialUnitary}
    {W : Link a → specialUnitary} (h : ∀ b, W' (linkScale lam hc b) = W b)
    (p : ElementaryPlaquette a) :
    faceHolonomy W' (plaquetteScale lam hc p) = faceHolonomy W p := by
  have h1 : ∀ x μ, W' (Link.forwardFrom (pointScale lam hc x) μ) = W (Link.forwardFrom x μ) :=
    fun x μ => by rw [← linkScale_forwardFrom, h]
  change W' (Link.forwardFrom (pointScale lam hc p.corner) p.lowAxis) *
      W' (Link.forwardFrom (pointScale lam hc p.corner + axisStep c p.lowAxis) p.highAxis) *
      (W' (Link.forwardFrom (pointScale lam hc p.corner + axisStep c p.highAxis) p.lowAxis))⁻¹ *
      (W' (Link.forwardFrom (pointScale lam hc p.corner) p.highAxis))⁻¹ = _
  rw [← pointScale_axisStep hc p.lowAxis, ← pointScale_axisStep hc p.highAxis, ← pointScale_add,
    ← pointScale_add, h1, h1, h1, h1]
  rfl
theorem faceEnergy_plaquetteScale (hc : c = lam * a) {W' : Link c → specialUnitary}
    {W : Link a → specialUnitary} (h : ∀ b, W' (linkScale lam hc b) = W b)
    (p : ElementaryPlaquette a) :
    faceEnergy W' (plaquetteScale lam hc p) = faceEnergy W p := by
  simp only [faceEnergy, faceHolonomy_plaquetteScale hc h]
theorem gaugeFieldScale_inv_gaugeFieldScale (hlam : 0 < lam) (hc : c = lam * a)
    (U : GaugeField a) :
    gaugeFieldScale (inv_pos.2 hlam) (spacing_eq_inv_mul hlam hc) (gaugeFieldScale hlam hc U) =
      U :=
  Subtype.ext (funext fun b => congrArg U.1
    (linkScale_linkScale_inv (inv_pos.2 hlam) (spacing_eq_inv_mul hlam hc) b))
theorem gaugeFieldScale_gaugeFieldScale_inv (hlam : 0 < lam) (hc : c = lam * a)
    (U : GaugeField c) :
    gaugeFieldScale hlam hc (gaugeFieldScale (inv_pos.2 hlam) (spacing_eq_inv_mul hlam hc) U) =
      U :=
  Subtype.ext (funext fun b => congrArg U.1
    (linkScale_inv_linkScale (inv_pos.2 hlam) (spacing_eq_inv_mul hlam hc) b))
def gaugeFieldScaleHomeo (hlam : 0 < lam) (hc : c = lam * a) : GaugeField a ≃ₜ GaugeField c where
  toFun := gaugeFieldScale hlam hc
  invFun := gaugeFieldScale (inv_pos.2 hlam) (spacing_eq_inv_mul hlam hc)
  left_inv := gaugeFieldScale_inv_gaugeFieldScale hlam hc
  right_inv := gaugeFieldScale_gaugeFieldScale_inv hlam hc
  continuous_toFun := continuous_gaugeFieldScale hlam hc
  continuous_invFun := continuous_gaugeFieldScale (inv_pos.2 hlam) (spacing_eq_inv_mul hlam hc)
theorem gaugeFieldScale_homeomorph (hlam : 0 < lam) (hc : c = lam * a) :
    GaugeFieldScaleHomeomorph hlam hc :=
  ⟨⟨gaugeFieldScaleHomeo hlam hc, rfl, rfl⟩, fun p U =>
    ⟨faceHolonomy_plaquetteScale hc (gaugeFieldScale_linkScale hlam hc U) p,
      faceEnergy_plaquetteScale hc (gaugeFieldScale_linkScale hlam hc U) p⟩⟩
theorem smearedEnergy_scales (E : Type) [NormedAddCommGroup E] [Module ℝ E] [MeasurableSpace E]
    (hlam : 0 < lam) (hc : c = lam * a) : SmearedEnergyScales E hlam hc := by
  rintro h ⟨hm, ⟨C, hC⟩, hs⟩
  refine ⟨⟨hm.comp (continuous_const_smul lam).measurable, ⟨C, fun x => hC _⟩,
    hs.comp_homeomorph (Homeomorph.smulOfNeZero lam hlam.ne')⟩, fun U => ?_⟩
  unfold smearedEnergy
  rw [← finsum_comp_equiv (plaquetteScaleEquiv hlam hc)]
  refine finsum_congr fun p => ?_
  change faceEnergy (gaugeFieldScale hlam hc U) (plaquetteScale lam hc p) •
    h (plaquetteScale lam hc p).center = _
  rw [faceEnergy_plaquetteScale hc (gaugeFieldScale_linkScale hlam hc U) p,
    center_plaquetteScale]
theorem scaledState_inv_scaledState (hlam : 0 < lam) (hc : c = lam * a)
    (ν : Measure (GaugeField a)) :
    scaledState (inv_pos.2 hlam) (spacing_eq_inv_mul hlam hc) (scaledState hlam hc ν) = ν := by
  unfold scaledState
  rw [Measure.map_map (measurable_gaugeFieldScale _ _) (measurable_gaugeFieldScale _ _)]
  have h : gaugeFieldScale (inv_pos.2 hlam) (spacing_eq_inv_mul hlam hc) ∘
      gaugeFieldScale hlam hc = id := funext (gaugeFieldScale_inv_gaugeFieldScale hlam hc)
  rw [h, Measure.map_id]
theorem scaledState_scaledState_inv (hlam : 0 < lam) (hc : c = lam * a)
    (ν : Measure (GaugeField c)) :
    scaledState hlam hc (scaledState (inv_pos.2 hlam) (spacing_eq_inv_mul hlam hc) ν) = ν := by
  unfold scaledState
  rw [Measure.map_map (measurable_gaugeFieldScale _ _) (measurable_gaugeFieldScale _ _)]
  have h : gaugeFieldScale hlam hc ∘
      gaugeFieldScale (inv_pos.2 hlam) (spacing_eq_inv_mul hlam hc) = id :=
    funext (gaugeFieldScale_gaugeFieldScale_inv hlam hc)
  rw [h, Measure.map_id]
theorem scaledState_cumulants (hlam : 0 < lam) (hc : c = lam * a) :
    ScaledStateCumulants hlam hc := by
  intro ν hν
  refine ⟨inferInstance, scaledState_inv_scaledState hlam hc ν, fun n _ h hh => ?_⟩
  have hT := (gaugeFieldScaleHomeo hlam hc).measurableEmbedding
  have hgen : ∀ t : Fin n → ℂ,
      Cumulants.momentGeneratingFunction (scaledState hlam hc ν)
          (fun i U => smearedEnergy (h i) U) t =
        Cumulants.momentGeneratingFunction ν
          (fun i U => smearedEnergy (fun x => h i (lam • x)) U) t := fun t => by
    unfold Cumulants.momentGeneratingFunction
    change ∫ ω, _ ∂(ν.map ⇑(gaugeFieldScaleHomeo hlam hc)) = _
    rw [hT.integral_map]
    refine integral_congr_ae (ae_of_all _ fun U => ?_)
    have hi : ∀ i, smearedEnergy (h i) ((gaugeFieldScaleHomeo hlam hc) U) =
        smearedEnergy (fun x => h i (lam • x)) U :=
      fun i => ((smearedEnergy_scales ℝ hlam hc) (h i) (hh i)).2 U
    simp only [hi]
  unfold smearedEnergyCumulant Cumulants.mixedCumulant
  simp only [hgen]
theorem shift_gaugeFieldScale (hlam : 0 < lam) (hc : c = lam * a) (v : LatticePoint a)
    (U : GaugeField a) :
    (shift (pointScale lam hc v)).pullbackField (gaugeFieldScale hlam hc U) =
      gaugeFieldScale hlam hc ((shift v).pullbackField U) := by
  refine Subtype.ext (funext fun b' => congrArg U.1 ?_)
  apply Link.ext <;> refine Subtype.ext ?_ <;>
    simp [linkScale, pointScale, LatticeSymmetry.linkMap, LatticeSymmetry.pointMap, shift,
      smul_add, smul_smul, inv_mul_cancel₀ hlam.ne']
theorem isSymmetricUnder_scaledState (hlam : 0 < lam) (hc : c = lam * a)
    {ν : Measure (GaugeField a)} {v : LatticePoint a} (h : IsSymmetricUnder ν (shift v)) :
    IsSymmetricUnder (scaledState hlam hc ν) (shift (pointScale lam hc v)) := by
  intro A hA
  have hT := (gaugeFieldScaleHomeo hlam hc).measurableEmbedding
  have hA' : IsBoundedObservable (A ∘ gaugeFieldScale hlam hc) :=
    ⟨hA.1.comp (measurable_gaugeFieldScale hlam hc),
      let ⟨C, hC⟩ := hA.2; ⟨C, fun U => hC _⟩⟩
  have key := h _ hA'
  change ∫ U, _ ∂(ν.map ⇑(gaugeFieldScaleHomeo hlam hc)) =
    ∫ U, _ ∂(ν.map ⇑(gaugeFieldScaleHomeo hlam hc))
  rw [hT.integral_map, hT.integral_map]
  refine Eq.trans ?_ key
  refine integral_congr_ae (ae_of_all _ fun U => ?_)
  change A ((shift (pointScale lam hc v)).pullbackField (gaugeFieldScale hlam hc U)) =
    A (gaugeFieldScale hlam hc ((shift v).pullbackField U))
  rw [shift_gaugeFieldScale]
theorem isPeriodicMeasure_scaledState (hlam : 0 < lam) (hc : c = lam * a)
    {ν : Measure (GaugeField a)} (h : IsPeriodicMeasure ν) :
    IsPeriodicMeasure (scaledState hlam hc ν) := by
  obtain ⟨H, hH, hinv⟩ := h
  refine ⟨H.map ((pointScaleAddEquiv hlam hc : LatticePoint a ≃+ LatticePoint c) :
    LatticePoint a →+ LatticePoint c), ?_, ?_⟩
  · exact ⟨by rw [AddSubgroup.index_map_equiv]; exact hH.index_ne_zero⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact isSymmetricUnder_scaledState hlam hc (hinv v hv)
theorem condExp_map_comp {Ω Ω' : Type*} {m' : MeasurableSpace Ω'}
    [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω'] (T : Ω ≃ᵐ Ω') (ν : Measure Ω)
    [IsFiniteMeasure ν] (hm' : m' ≤ mΩ') {f : Ω' → ℝ} (hf : Integrable f (ν.map T)) :
    (condExp m' (ν.map T) f) ∘ T =ᵐ[ν] condExp (m'.comap T) ν (f ∘ T) := by
  have hm : m'.comap T ≤ mΩ := (MeasurableSpace.comap_mono hm').trans T.measurable.comap_le
  have hfT : Integrable (f ∘ T) ν := (integrable_map_equiv T f).1 hf
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hfT ?_ ?_ ?_
  · intro s _ _
    exact ((integrable_map_equiv T _).1 integrable_condExp).integrableOn
  · rintro s ⟨s', hs', rfl⟩ _
    have h1 := T.measurableEmbedding.setIntegral_map (μ := ν) (condExp m' (ν.map T) f) s'
    have h2 := T.measurableEmbedding.setIntegral_map (μ := ν) f s'
    have h3 := setIntegral_condExp hm' hf hs'
    exact h1.symm.trans (h3.trans h2)
  · have hTm : @Measurable _ _ (m'.comap T) m' T := fun s hs => ⟨s, hs, rfl⟩
    exact (stronglyMeasurable_condExp.comp_measurable hTm).aestronglyMeasurable
def reindexMeasurableEquiv {S S' : Type} (u : S ≃ S') :
    (S → specialUnitary) ≃ᵐ (S' → specialUnitary) where
  toFun := PeriodicLattice.reindexFactors u
  invFun := PeriodicLattice.reindexFactors u.symm
  left_inv g := by funext s; simp [PeriodicLattice.reindexFactors]
  right_inv g := by funext s; simp [PeriodicLattice.reindexFactors]
  measurable_toFun := measurable_pi_lambda _ fun s => measurable_pi_apply _
  measurable_invFun := measurable_pi_lambda _ fun s => measurable_pi_apply _
def linkSubtypeEquiv (hlam : 0 < lam) (hc : c = lam * a) {𝓛 : Finset (Link a)}
    {𝓛' : Finset (Link c)} (hmem : ∀ b, b ∈ 𝓛 ↔ linkScale lam hc b ∈ 𝓛') : 𝓛 ≃ 𝓛' :=
  (linkScaleEquiv hlam hc).subtypeEquiv hmem
theorem patch_linkScale (hlam : 0 < lam) (hc : c = lam * a) {𝓛 : Finset (Link a)}
    {𝓛' : Finset (Link c)} (hmem : ∀ b, b ∈ 𝓛 ↔ linkScale lam hc b ∈ 𝓛')
    (v : 𝓛 → specialUnitary) {W : Link a → specialUnitary} {W' : Link c → specialUnitary}
    (hW : ∀ b, W' (linkScale lam hc b) = W b) (b : Link a) :
    patch 𝓛' (PeriodicLattice.reindexFactors (linkSubtypeEquiv hlam hc hmem) v) W'
        (linkScale lam hc b) =
      patch 𝓛 v W b := by
  unfold patch
  by_cases hb : b ∈ 𝓛
  · have hb' := (hmem b).1 hb
    rw [dif_pos hb', dif_pos hb]
    exact congrArg v ((linkSubtypeEquiv hlam hc hmem).symm_apply_apply ⟨b, hb⟩)
  · have hb' : linkScale lam hc b ∉ 𝓛' := fun h => hb ((hmem b).2 h)
    rw [dif_neg hb', dif_neg hb]
    exact hW b
theorem boltzmannWeight_scale (hlam : 0 < lam) (hc : c = lam * a) {𝓛 : Finset (Link a)}
    {𝓛' : Finset (Link c)} (hmem : ∀ b, b ∈ 𝓛 ↔ linkScale lam hc b ∈ 𝓛') (β : ℝ)
    (U : GaugeField a) (v : 𝓛 → specialUnitary) :
    boltzmannWeight β 𝓛' (gaugeFieldScale hlam hc U)
        (PeriodicLattice.reindexFactors (linkSubtypeEquiv hlam hc hmem) v) =
      boltzmannWeight β 𝓛 U v := by
  have hp : ∀ p, plaquetteScale lam hc p ∈ facesTouching 𝓛' ↔ p ∈ facesTouching 𝓛 := by
    intro p
    constructor
    · rintro ⟨b', hb, hb'⟩
      rw [edges_plaquetteScale, List.mem_map] at hb
      obtain ⟨b, hb, rfl⟩ := hb
      exact ⟨b, hb, (hmem b).2 hb'⟩
    · rintro ⟨b, hb, hb'⟩
      refine ⟨linkScale lam hc b, ?_, (hmem b).1 hb'⟩
      rw [edges_plaquetteScale]
      exact List.mem_map_of_mem hb
  have hsum : ∑ᶠ p ∈ facesTouching 𝓛, faceEnergy (patch 𝓛 v U) p =
      ∑ᶠ p' ∈ facesTouching 𝓛', faceEnergy
        (patch 𝓛' (PeriodicLattice.reindexFactors (linkSubtypeEquiv hlam hc hmem) v)
          (gaugeFieldScale hlam hc U)) p' :=
    finsum_mem_eq_of_bijOn (plaquetteScaleEquiv hlam hc) ((plaquetteScaleEquiv hlam hc).bijOn hp)
      fun p _ => (faceEnergy_plaquetteScale hc
        (patch_linkScale hlam hc hmem v (gaugeFieldScale_linkScale hlam hc U)) p).symm
  unfold boltzmannWeight
  rw [hsum]
theorem wilsonSpecification_scale (hren : GaugeFieldProduct.ReindexingFactors)
    (hlam : 0 < lam) (hc : c = lam * a) {𝓛 : Finset (Link a)}
    {𝓛' : Finset (Link c)} (hmem : ∀ b, b ∈ 𝓛 ↔ linkScale lam hc b ∈ 𝓛') (β : ℝ)
    (U : GaugeField a) {B' : Set (𝓛' → specialUnitary)} (hB' : MeasurableSet B') :
    wilsonSpecification β 𝓛' (gaugeFieldScale hlam hc U) B' =
      wilsonSpecification β 𝓛 U (reindexMeasurableEquiv (linkSubtypeEquiv hlam hc hmem) ⁻¹' B') := by
  set u := linkSubtypeEquiv hlam hc hmem with hu
  set r := reindexMeasurableEquiv u with hr
  have hH : (haarPi 𝓛).map r = haarPi 𝓛' := (hren _ _ u).2
  have hw : ∀ v, boltzmannWeight β 𝓛' (gaugeFieldScale hlam hc U) (r v) =
      boltzmannWeight β 𝓛 U v := boltzmannWeight_scale hlam hc hmem β U
  have hZ : partitionFunction β 𝓛' (gaugeFieldScale hlam hc U) =
      partitionFunction β 𝓛 U := by
    unfold partitionFunction
    rw [← hH, r.measurableEmbedding.integral_map]
    exact integral_congr_ae (ae_of_all _ hw)
  have hI : (haarPi 𝓛').withDensity (fun v =>
        ENNReal.ofReal (boltzmannWeight β 𝓛' (gaugeFieldScale hlam hc U) v)) B' =
      (haarPi 𝓛).withDensity (fun v =>
        ENNReal.ofReal (boltzmannWeight β 𝓛 U v)) (r ⁻¹' B') := by
    rw [withDensity_apply _ hB', withDensity_apply _ (r.measurable hB'), ← hH,
      r.measurableEmbedding.restrict_map, r.measurableEmbedding.lintegral_map]
    exact lintegral_congr fun v => by rw [hw]
  unfold wilsonSpecification
  rw [Measure.smul_apply, Measure.smul_apply, hZ, hI]
theorem measurable_eval_link (b : Link a) : Measurable fun U : GaugeField a => U b := by apply _root_.YangMills.Construction.ChessboardTori.MeasurableObservables.measurable_link_eval <;> assumption
theorem linkSigma_le (ℬ : Set (Link a)) :
    linkSigma ℬ ≤ (inferInstance : MeasurableSpace (GaugeField a)) := by apply _root_.YangMills.Construction.GibbsAtFixedSpacing.SymmetryActionProof.linkSigma_le_borel <;> assumption
theorem measurable_restrictTo (𝓛 : Finset (Link a)) : Measurable (restrictTo 𝓛) :=
  measurable_pi_lambda _ fun b => measurable_eval_link b.1
theorem exteriorSigma_comap (hlam : 0 < lam) (hc : c = lam * a) {𝓛 : Finset (Link a)}
    {𝓛' : Finset (Link c)} (hmem : ∀ b, b ∈ 𝓛 ↔ linkScale lam hc b ∈ 𝓛') :
    (exteriorSigma 𝓛').comap (gaugeFieldScale hlam hc) = exteriorSigma 𝓛 := by
  have hS : ∀ b : Link a, (b ∉ 𝓛 ∧ b.opposite ∉ 𝓛) ↔
      (linkScale lam hc b ∉ 𝓛' ∧ (linkScale lam hc b).opposite ∉ 𝓛') := fun b => by
    rw [hmem b, hmem b.opposite, linkScale_opposite]
  simp only [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  apply le_antisymm
  · refine iSup₂_le fun b' hb' => ?_
    have hb : linkScale lam hc (linkScale lam⁻¹ (spacing_eq_inv_mul hlam hc) b') = b' :=
      linkScale_linkScale_inv hlam hc b'
    refine le_iSup₂_of_le (linkScale lam⁻¹ (spacing_eq_inv_mul hlam hc) b')
      ((hS _).2 (by rw [hb]; exact hb')) le_rfl
  · refine iSup₂_le fun b hb => ?_
    have h : (fun U : GaugeField a => U b) =
        (fun U : GaugeField c => U (linkScale lam hc b)) ∘ gaugeFieldScale hlam hc :=
      funext fun U => (gaugeFieldScale_linkScale hlam hc U b).symm
    rw [h]
    exact le_iSup₂_of_le (linkScale lam hc b) ((hS b).1 hb) le_rfl
theorem isGibbs_scaledState (hren : GaugeFieldProduct.ReindexingFactors)
    (hlam : 0 < lam) (hc : c = lam * a) {β : ℝ} {ν : Measure (GaugeField a)}
    (hν : IsGibbs β ν) : IsGibbs β (scaledState hlam hc ν) := by
  classical
  obtain ⟨hprob, hg⟩ := hν
  refine ⟨inferInstance, fun 𝓛' hpos B' hB' => ?_⟩
  let 𝓛 : Finset (Link a) := 𝓛'.map (linkScaleEquiv hlam hc).symm.toEmbedding
  have hmem : ∀ b, b ∈ 𝓛 ↔ linkScale lam hc b ∈ 𝓛' := fun b => Finset.mem_map_equiv
  have hpos' : ∀ b ∈ 𝓛, b.IsPositivelyOriented := fun b hb =>
    (isPositivelyOriented_linkScale hlam hc b).1 (hpos _ ((hmem b).1 hb))
  let r := reindexMeasurableEquiv (linkSubtypeEquiv hlam hc hmem)
  let T : GaugeField a ≃ᵐ GaugeField c := (gaugeFieldScaleHomeo hlam hc).toMeasurableEquiv
  have hvalues : ∀ U, restrictTo 𝓛' (gaugeFieldScale hlam hc U) = r (restrictTo 𝓛 U) :=
    fun U => rfl
  have hB : MeasurableSet (r ⁻¹' B') := r.measurable hB'
  have h := hg 𝓛 hpos' (r ⁻¹' B') hB
  have hmeas : MeasurableSet (restrictTo 𝓛' ⁻¹' B') := measurable_restrictTo 𝓛' hB'
  have hcopy : scaledState hlam hc ν = ν.map T := rfl
  have hint : Integrable ((restrictTo 𝓛' ⁻¹' B').indicator fun _ => (1 : ℝ)) (ν.map T) :=
    (integrable_const (1 : ℝ)).indicator hmeas
  have hind : ((restrictTo 𝓛' ⁻¹' B').indicator fun _ => (1 : ℝ)) ∘ T =
      (restrictTo 𝓛 ⁻¹' (r ⁻¹' B')).indicator fun _ => (1 : ℝ) := by
    funext U
    have hiff : T U ∈ restrictTo 𝓛' ⁻¹' B' ↔ U ∈ restrictTo 𝓛 ⁻¹' (r ⁻¹' B') := by
      change restrictTo 𝓛' (gaugeFieldScale hlam hc U) ∈ B' ↔ r (restrictTo 𝓛 U) ∈ B'
      rw [hvalues]
    by_cases hU : U ∈ restrictTo 𝓛 ⁻¹' (r ⁻¹' B')
    · simp only [Function.comp, indicator_of_mem hU, indicator_of_mem (hiff.2 hU)]
    · simp only [Function.comp, indicator_of_notMem hU,
        indicator_of_notMem (fun h' => hU (hiff.1 h'))]
  have hce := condExp_map_comp (m' := exteriorSigma 𝓛') T ν (linkSigma_le _) hint
  have hcomap : (exteriorSigma 𝓛').comap T = exteriorSigma 𝓛 := exteriorSigma_comap hlam hc hmem
  rw [hind, hcomap] at hce
  rw [Filter.EventuallyEq, hcopy, T.measurableEmbedding.ae_map_iff]
  filter_upwards [h, hce] with U h1 h2
  have h3 : wilsonSpecification β 𝓛' (T U) B' = wilsonSpecification β 𝓛 U (r ⁻¹' B') :=
    wilsonSpecification_scale hren hlam hc hmem β U hB'
  rw [h3, h1, ← h2]
  rfl
theorem scaledState_gibbs_iff (hren : GaugeFieldProduct.ReindexingFactors) (hlam : 0 < lam)
    (hc : c = lam * a) : ScaledStateGibbsIff hlam hc := by
  intro β _ ν _
  refine ⟨isGibbs_scaledState hren hlam hc, fun h => ?_⟩
  have h' := isGibbs_scaledState hren (inv_pos.2 hlam) (spacing_eq_inv_mul hlam hc) h
  rwa [scaledState_inv_scaledState] at h'
theorem scaledState_symmetry_iff (hren : GaugeFieldProduct.ReindexingFactors) (hlam : 0 < lam)
    (hc : c = lam * a) : ScaledStateSymmetryIff hlam hc := by
  have hlam' := inv_pos.2 hlam
  have hc' := spacing_eq_inv_mul hlam hc
  refine ⟨fun ν _ => ⟨fun v => ⟨isSymmetricUnder_scaledState hlam hc, fun h => ?_⟩,
    isPeriodicMeasure_scaledState hlam hc, fun h => ?_⟩, fun β _ => ⟨?_, ?_, ?_⟩⟩
  · have h' := isSymmetricUnder_scaledState hlam' hc' h
    rwa [scaledState_inv_scaledState hlam hc, pointScale_inv_pointScale hlam hc] at h'
  · have h' := isPeriodicMeasure_scaledState hlam' hc' h
    rwa [scaledState_inv_scaledState] at h'
  · exact fun ν hν =>
      ⟨isGibbs_scaledState hren hlam hc hν.1, isPeriodicMeasure_scaledState hlam hc hν.2⟩
  · intro ν _ ν' _ h
    rw [← scaledState_inv_scaledState hlam hc ν, h, scaledState_inv_scaledState]
  · intro ν' hν'
    exact ⟨scaledState hlam' hc' ν',
      ⟨isGibbs_scaledState hren hlam' hc' hν'.1, isPeriodicMeasure_scaledState hlam' hc' hν'.2⟩,
      scaledState_scaledState_inv hlam hc ν'⟩
theorem dilatedStateProperties (hproduct : GaugeFieldProduct.Statement) :
    DilatedStateProperties :=
  fun _ _ _ _ hlam hc =>
    ⟨scaleBijectsCells hlam hc, gaugeFieldScale_homeomorph hlam hc,
      smearedEnergy_scales ℝ hlam hc, smearedEnergy_scales ℂ hlam hc, scaledState_cumulants hlam hc,
      scaledState_gibbs_iff hproduct.2 hlam hc, scaledState_symmetry_iff hproduct.2 hlam hc⟩
end YangMills.Construction.InfiniteLattice.Dilation
