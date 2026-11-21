import YangMills.Construction.Lattice.CompactGaugeFieldSpaceAndPartitionBounds
import YangMills.Construction.Lattice.HaarAndGaugeInvariance
import YangMills.Construction.Lattice.WilsonActionGaugeInvariance
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped Topology
noncomputable section
namespace YangMills.Construction
open Matrices
namespace PeriodicLattice.HaarWilsonInvarianceProof
theorem coe_inv (g : ComplexMatrix2.specialUnitary) :
    ((g⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) = (g : ComplexMatrix2)⁻¹ := by
  refine (Matrix.inv_eq_left_inv ?_).symm
  exact show ((g⁻¹ * g : ComplexMatrix2.specialUnitary) : ComplexMatrix2) = 1 from by
    rw [inv_mul_cancel]
    rfl
theorem secondCountableTopology_complexMatrix2 : SecondCountableTopology ComplexMatrix2 :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
attribute [local instance] secondCountableTopology_complexMatrix2
theorem secondCountableTopology_specialUnitary :
    SecondCountableTopology ComplexMatrix2.specialUnitary :=
  Topology.IsInducing.subtypeVal.secondCountableTopology
attribute [local instance] secondCountableTopology_specialUnitary
theorem haarProb_isMulLeftInvariant : ComplexMatrix2.haarProb.IsMulLeftInvariant := by
  unfold ComplexMatrix2.haarProb
  infer_instance
attribute [local instance] haarProb_isMulLeftInvariant
theorem eq_haarProb_of_isMulLeftInvariant (μ : Measure ComplexMatrix2.specialUnitary)
    [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] :
    μ = ComplexMatrix2.haarProb := by
  have hμ := Measure.haarMeasure_unique μ ⊤
  have hone : μ ((⊤ : TopologicalSpace.PositiveCompacts ComplexMatrix2.specialUnitary) :
      Set ComplexMatrix2.specialUnitary) = 1 := by
    simp
  rw [hone, one_smul] at hμ
  exact hμ
theorem haarProb_isMulRightInvariant : ComplexMatrix2.haarProb.IsMulRightInvariant := by
  refine ⟨fun h => ?_⟩
  have : IsProbabilityMeasure (Measure.map (· * h) ComplexMatrix2.haarProb) :=
    Measure.isProbabilityMeasure_map (measurable_mul_const h).aemeasurable
  exact eq_haarProb_of_isMulLeftInvariant _
theorem haarProb_inv : ComplexMatrix2.haarProb.inv = ComplexMatrix2.haarProb := by
  have := haarProb_isMulRightInvariant
  have : IsProbabilityMeasure ComplexMatrix2.haarProb.inv :=
    Measure.isProbabilityMeasure_map measurable_inv.aemeasurable
  exact eq_haarProb_of_isMulLeftInvariant _
theorem haarIsLeftInvariantProbability_holds
    (hspace : GaugeFieldSpace.FieldSpaceAndPartitionBounds) :
    HaarIsLeftInvariantProbability := by
  let s : Conventions.StandingParameters := ⟨13, ⟨by decide, le_rfl⟩, 1, 1⟩
  refine ⟨?_, inferInstance, inferInstance, inferInstance, fun h E _ => ?_⟩
  · refine ((hspace s).2.2).2.1.trans ?_
    unfold ComplexMatrix2.specialUnitaryEntrywiseTopology ComplexMatrix2.entrywiseTopology
    rw [induced_compose]
    rfl
  · exact measure_preimage_mul ComplexMatrix2.haarProb h E
theorem haarIsInversionAndTranslationInvariant_holds :
    HaarIsInversionAndTranslationInvariant := by
  have := haarProb_isMulRightInvariant
  intro E hE
  have hright : ∀ h : ComplexMatrix2.specialUnitary,
      ComplexMatrix2.haarProb ((fun g => g * h) ⁻¹' E) = ComplexMatrix2.haarProb E :=
    fun h => measure_preimage_mul_right ComplexMatrix2.haarProb h E
  refine ⟨?_, hright, fun h h' => ?_⟩
  · have hinv := congrArg (fun μ : Measure ComplexMatrix2.specialUnitary => μ E) haarProb_inv
    simp only [Measure.inv, Measure.map_apply measurable_inv hE] at hinv
    exact hinv
  · have hsplit : (fun g => h * g * h'⁻¹) ⁻¹' E =
        (fun g => h * g) ⁻¹' ((fun g => g * h'⁻¹) ⁻¹' E) := rfl
    rw [hsplit, measure_preimage_mul ComplexMatrix2.haarProb h, hright]
variable {L m : ℕ} {j : ℤ}
theorem opposite_isPositivelyOriented (b : Bond L m j) (h : ¬ b.IsPositivelyOriented) :
    b.opposite.IsPositivelyOriented := by
  obtain ⟨μ, h₁ | h₂⟩ := b.isNeighbour
  · exact absurd ⟨μ, h₁⟩ h
  · refine ⟨μ, ?_⟩
    show b.source - b.target = _
    rw [← neg_sub, h₂, neg_neg]
def conjugateAtBond (w : Site L m j → ComplexMatrix2.specialUnitary) (b : Bond L m j)
    (g : ComplexMatrix2.specialUnitary) : ComplexMatrix2.specialUnitary :=
  w b.source * g * (w b.target)⁻¹
def transformValues (w : Site L m j → ComplexMatrix2.specialUnitary)
    (v : PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary) :
    PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary :=
  fun b => conjugateAtBond w b.1 (v b)
theorem continuous_conjugateAtBond (w : Site L m j → ComplexMatrix2.specialUnitary)
    (b : Bond L m j) : Continuous (conjugateAtBond w b) :=
  (continuous_const.mul continuous_id).mul continuous_const
theorem continuous_transformValues (w : Site L m j → ComplexMatrix2.specialUnitary) :
    Continuous (transformValues w) :=
  continuous_pi fun b => (continuous_conjugateAtBond w b.1).comp (continuous_apply b)
theorem measurable_transformValues (w : Site L m j → ComplexMatrix2.specialUnitary) :
    Measurable (transformValues w) :=
  measurable_pi_lambda _ fun b =>
    (continuous_conjugateAtBond w b.1).measurable.comp (measurable_pi_apply b)
theorem transformValues_inv_transformValues (w : Site L m j → ComplexMatrix2.specialUnitary)
    (v : PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary) :
    transformValues (fun x => (w x)⁻¹) (transformValues w v) = v := by
  funext b
  simp only [transformValues, conjugateAtBond]
  group
theorem transformValues_transformValues_inv (w : Site L m j → ComplexMatrix2.specialUnitary)
    (v : PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary) :
    transformValues w (transformValues (fun x => (w x)⁻¹) v) = v := by
  funext b
  simp only [transformValues, conjugateAtBond]
  group
def transformValuesEquiv (w : Site L m j → ComplexMatrix2.specialUnitary) :
    (PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary) ≃ᵐ
      (PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary) where
  toFun := transformValues w
  invFun := transformValues fun x => (w x)⁻¹
  left_inv := transformValues_inv_transformValues w
  right_inv := transformValues_transformValues_inv w
  measurable_toFun := measurable_transformValues w
  measurable_invFun := measurable_transformValues fun x => (w x)⁻¹
theorem measurePreserving_transformValuesEquiv (w : Site L m j → ComplexMatrix2.specialUnitary) :
    MeasurePreserving (transformValuesEquiv w)
      (ComplexMatrix2.haarPi (PositivelyOrientedBond L m j))
      (ComplexMatrix2.haarPi (PositivelyOrientedBond L m j)) := by
  refine ⟨(transformValuesEquiv w).measurable, ?_⟩
  have hmap : ∀ b : PositivelyOrientedBond L m j,
      Measure.map (conjugateAtBond w b.1) ComplexMatrix2.haarProb = ComplexMatrix2.haarProb := by
    intro b
    refine Measure.ext fun E hE => ?_
    rw [Measure.map_apply (continuous_conjugateAtBond w b.1).measurable hE]
    exact (haarIsInversionAndTranslationInvariant_holds E hE).2.2 _ _
  have hpi := Measure.infinitePi_map_pi
    (μ := fun _ : PositivelyOrientedBond L m j => ComplexMatrix2.haarProb)
    (f := fun b => conjugateAtBond w b.1) fun b => (continuous_conjugateAtBond w b.1).measurable
  simp only [hmap] at hpi
  exact hpi
theorem continuous_gaugeFieldOfPositive :
    Continuous (gaugeFieldOfPositive :
      (PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary) → Bond L m j → ComplexMatrix2) := by
  refine continuous_pi fun b => ?_
  by_cases h : b.IsPositivelyOriented
  · simp only [gaugeFieldOfPositive, dif_pos h]
    exact continuous_subtype_val.comp (continuous_apply _)
  · by_cases h' : b.opposite.IsPositivelyOriented
    · simp only [gaugeFieldOfPositive, dif_neg h, dif_pos h', ← coe_inv]
      exact continuous_subtype_val.comp (continuous_apply _).inv
    · simp only [gaugeFieldOfPositive, dif_neg h, dif_neg h']
      exact continuous_const
theorem gaugeFieldOfPositive_injective :
    Function.Injective (gaugeFieldOfPositive :
      (PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary) → Bond L m j → ComplexMatrix2) := by
  intro v v' h
  funext b
  have hb := congrFun h b.1
  simp only [gaugeFieldOfPositive, dif_pos b.2] at hb
  exact Subtype.ext hb
theorem measurableEmbedding_gaugeFieldOfPositive :
    MeasurableEmbedding (gaugeFieldOfPositive :
      (PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary) → Bond L m j → ComplexMatrix2) :=
  (continuous_gaugeFieldOfPositive.isClosedEmbedding
    gaugeFieldOfPositive_injective).measurableEmbedding
theorem gaugeTransform_gaugeFieldOfPositive (w : Site L m j → ComplexMatrix2.specialUnitary)
    (v : PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary) :
    gaugeTransform (fun x => (w x : ComplexMatrix2)) (gaugeFieldOfPositive v) =
      gaugeFieldOfPositive (transformValues w v) := by
  funext b
  by_cases h : b.IsPositivelyOriented
  · simp only [gaugeTransform, gaugeFieldOfPositive, dif_pos h, transformValues, conjugateAtBond,
      Submonoid.coe_mul, coe_inv]
  · have h' := opposite_isPositivelyOriented b h
    have key : w b.source * (v ⟨b.opposite, h'⟩)⁻¹ * (w b.target)⁻¹ =
        (w b.target * v ⟨b.opposite, h'⟩ * (w b.source)⁻¹)⁻¹ := by group
    have hcancelled' := congrArg Subtype.val key
    simp only [Submonoid.coe_mul, coe_inv] at hcancelled'
    simp only [gaugeTransform, gaugeFieldOfPositive, dif_neg h, dif_pos h', transformValues,
      conjugateAtBond, Submonoid.coe_mul, coe_inv]
    exact hcancelled'
theorem gaugeTransform_mem_compactGaugeFields (w : Site L m j → ComplexMatrix2.specialUnitary)
    {U : Bond L m j → ComplexMatrix2} (hU : U ∈ compactGaugeFields L m j) :
    gaugeTransform (fun x => (w x : ComplexMatrix2)) U ∈ compactGaugeFields L m j := by
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · have hg : ((w b.source * ⟨U b, hU.1 b (mem_univ b)⟩ * (w b.target)⁻¹ :
        ComplexMatrix2.specialUnitary) : ComplexMatrix2) =
        gaugeTransform (fun x => (w x : ComplexMatrix2)) U b := by
      simp only [gaugeTransform, Submonoid.coe_mul, coe_inv]
    rw [← hg]
    exact Subtype.property _
  · let g : ComplexMatrix2.specialUnitary := ⟨U b, hU.1 b (mem_univ b)⟩
    have key : w b.target * g⁻¹ * (w b.source)⁻¹ = (w b.source * g * (w b.target)⁻¹)⁻¹ := by
      group
    have hcancelled' := congrArg Subtype.val key
    simp only [Submonoid.coe_mul, coe_inv] at hcancelled'
    have hopp : U b.opposite = (U b)⁻¹ := hU.2 b (mem_univ b)
    simp only [gaugeTransform]
    rw [hopp]
    exact hcancelled'
theorem gaugeTransform_inv_gaugeTransform (w : Site L m j → ComplexMatrix2.specialUnitary)
    {U : Bond L m j → ComplexMatrix2} (hU : U ∈ compactGaugeFields L m j) :
    gaugeTransform (fun x => (((w x)⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2))
      (gaugeTransform (fun x => (w x : ComplexMatrix2)) U) = U := by
  funext b
  let g : ComplexMatrix2.specialUnitary := ⟨U b, hU.1 b (mem_univ b)⟩
  have key : (w b.source)⁻¹ * (w b.source * g * (w b.target)⁻¹) * ((w b.target)⁻¹)⁻¹ = g := by
    group
  have hcancelled' := congrArg Subtype.val key
  simp only [Submonoid.coe_mul, coe_inv] at hcancelled'
  simp only [gaugeTransform, coe_inv]
  exact hcancelled'
def gaugeTransformEquiv (w : Site L m j → ComplexMatrix2.specialUnitary) :
    compactGaugeFields L m j ≃ compactGaugeFields L m j where
  toFun U := ⟨gaugeTransform (fun x => (w x : ComplexMatrix2)) U.1,
    gaugeTransform_mem_compactGaugeFields w U.2⟩
  invFun U := ⟨gaugeTransform (fun x => (((w x)⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2)) U.1,
    gaugeTransform_mem_compactGaugeFields (fun x => (w x)⁻¹) U.2⟩
  left_inv U := Subtype.ext (gaugeTransform_inv_gaugeTransform w U.2)
  right_inv U := Subtype.ext (by
    have hU := gaugeTransform_inv_gaugeTransform (fun x => (w x)⁻¹) U.2
    simpa only [inv_inv] using hU)
theorem gaugeFieldAtLevelValues_gaugeTransformEquiv {K k : ℕ}
    (w : SiteAtLevel L m K k → ComplexMatrix2.specialUnitary) (U : gaugeFieldsAtLevel L m K k) :
    gaugeFieldAtLevelValues (gaugeTransformEquiv w U) =
      transformValues w (gaugeFieldAtLevelValues U) := by
  funext b
  refine Subtype.ext ?_
  simp only [gaugeFieldAtLevelValues, gaugeTransformEquiv, transformValues, conjugateAtBond,
    gaugeTransform, Equiv.coe_fn_mk, Submonoid.coe_mul, coe_inv]
theorem continuous_gaugeTransformEquiv {K k : ℕ}
    (w : SiteAtLevel L m K k → ComplexMatrix2.specialUnitary) :
    Continuous[gaugeFieldsAtLevelTopology L m K k, gaugeFieldsAtLevelTopology L m K k]
      (gaugeTransformEquiv w) := by
  have hcomp : gaugeFieldAtLevelValues ∘ (gaugeTransformEquiv w) =
      transformValues w ∘ (gaugeFieldAtLevelValues (L := L) (m := m) (K := K) (k := k)) :=
    funext fun U => gaugeFieldAtLevelValues_gaugeTransformEquiv w U
  have hdom : Continuous[gaugeFieldsAtLevelTopology L m K k, _]
      (gaugeFieldAtLevelValues (L := L) (m := m) (K := K) (k := k)) := continuous_induced_dom
  refine continuous_induced_rng.2 ?_
  rw [hcomp]
  exact @Continuous.comp _ _ _ (gaugeFieldsAtLevelTopology L m K k) _ _ _ _
    (continuous_transformValues w) hdom
theorem productHaarMeasure_image_preimage_gaugeTransformEquiv
    (w : Site L m j → ComplexMatrix2.specialUnitary) (E : Set (compactGaugeFields L m j)) :
    productHaarMeasure L m j (Subtype.val '' (gaugeTransformEquiv w ⁻¹' E)) =
      productHaarMeasure L m j (Subtype.val '' E) := by
  have hset : (gaugeFieldOfPositive :
        (PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary) → Bond L m j → ComplexMatrix2) ⁻¹'
        (Subtype.val '' (gaugeTransformEquiv w ⁻¹' E)) =
      transformValuesEquiv w ⁻¹' (gaugeFieldOfPositive ⁻¹' (Subtype.val '' E)) := by
    ext v
    constructor
    · rintro ⟨U, hU, hUv⟩
      refine ⟨gaugeTransformEquiv w U, hU, ?_⟩
      show gaugeTransform (fun x => (w x : ComplexMatrix2)) U.1 =
        gaugeFieldOfPositive (transformValues w v)
      rw [hUv, gaugeTransform_gaugeFieldOfPositive]
    · rintro ⟨U, hU, hUv⟩
      refine ⟨(gaugeTransformEquiv w).symm U, by simpa using hU, ?_⟩
      have hUv' : U.1 = gaugeFieldOfPositive (transformValues w v) := hUv
      show gaugeTransform (fun x => (((w x)⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2)) U.1 =
        gaugeFieldOfPositive v
      rw [hUv', gaugeTransform_gaugeFieldOfPositive, transformValues_inv_transformValues]
  unfold productHaarMeasure gaugeFieldHaar
  rw [measurableEmbedding_gaugeFieldOfPositive.map_apply,
    measurableEmbedding_gaugeFieldOfPositive.map_apply, hset]
  exact (measurePreserving_transformValuesEquiv w).measure_preimage_equiv _
theorem continuous_wilsonAction [Finite (Plaquette L m j)] :
    Continuous (wilsonAction : (Bond L m j → ComplexMatrix2) → ℝ) := by
  have := Fintype.ofFinite (Plaquette L m j)
  have hsum : (wilsonAction : (Bond L m j → ComplexMatrix2) → ℝ) =
      fun U => ∑ p, plaquetteCost U p := by
    funext U
    exact finsum_eq_sum_of_fintype _
  rw [hsum]
  refine continuous_finsetSum _ fun p _ => ?_
  unfold plaquetteCost plaquetteHolonomy pathHolonomy Plaquette.boundaryBonds
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  have hb : ∀ b : Bond L m j, Continuous fun U : Bond L m j → ComplexMatrix2 => U b :=
    fun b => continuous_apply b
  exact continuous_const.sub (continuous_const.mul (Complex.continuous_re.comp
    (((hb _).matrix_mul ((hb _).matrix_mul ((hb _).matrix_mul (hb _)))).matrix_trace)))
theorem integral_wilsonGibbsMeasure (K : ℕ) (β : ℝ) [Finite (Plaquette L m (K : ℤ))]
    (G : (Bond L m (K : ℤ) → ComplexMatrix2) → ℝ) :
    ∫ U, G U ∂wilsonGibbsMeasure L m K β =
      ((ENNReal.ofReal (partitionFunction L m K β))⁻¹).toReal •
        ∫ v, (ENNReal.ofReal (boltzmannWeight β (gaugeFieldOfPositive v))).toReal •
          G (gaugeFieldOfPositive v) ∂ComplexMatrix2.haarPi (PositivelyOrientedBond L m (K : ℤ)) := by
  have hmeas : Measurable fun U : Bond L m (K : ℤ) → ComplexMatrix2 =>
      ENNReal.ofReal (boltzmannWeight β U) := by
    refine ENNReal.measurable_ofReal.comp (Continuous.measurable ?_)
    exact Real.continuous_exp.comp (continuous_const.mul continuous_wilsonAction)
  unfold wilsonGibbsMeasure
  rw [integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul hmeas
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  unfold productHaarMeasure gaugeFieldHaar
  rw [measurableEmbedding_gaugeFieldOfPositive.integral_map]
theorem integral_wilsonGibbsMeasure_gaugeTransform (K : ℕ) (β : ℝ)
    [Finite (Plaquette L m (K : ℤ))] (w : Site L m (K : ℤ) → ComplexMatrix2.specialUnitary)
    (hinv : ∀ v : PositivelyOrientedBond L m (K : ℤ) → ComplexMatrix2.specialUnitary,
      wilsonAction (gaugeTransform (fun x => (w x : ComplexMatrix2)) (gaugeFieldOfPositive v)) =
        wilsonAction (gaugeFieldOfPositive v))
    (F : (Bond L m (K : ℤ) → ComplexMatrix2) → ℝ) :
    ∫ U, F (gaugeTransform (fun x => (w x : ComplexMatrix2)) U) ∂wilsonGibbsMeasure L m K β =
      ∫ U, F U ∂wilsonGibbsMeasure L m K β := by
  rw [integral_wilsonGibbsMeasure, integral_wilsonGibbsMeasure]
  congr 1
  rw [← (measurePreserving_transformValuesEquiv w).integral_comp'
    (fun v => (ENNReal.ofReal (boltzmannWeight β (gaugeFieldOfPositive v))).toReal •
      F (gaugeFieldOfPositive v))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  have h1 : gaugeFieldOfPositive (transformValuesEquiv w v) =
      gaugeTransform (fun x => (w x : ComplexMatrix2)) (gaugeFieldOfPositive v) :=
    (gaugeTransform_gaugeFieldOfPositive w v).symm
  have h2 : boltzmannWeight β (gaugeFieldOfPositive (transformValuesEquiv w v)) =
      boltzmannWeight β (gaugeFieldOfPositive v) := by
    unfold boltzmannWeight
    rw [h1, hinv]
  simp only [h1.symm, h2]
theorem gaugeFieldOfPositive_mem_gaugeFieldsAtLevel {K : ℕ}
    (hb : Function.Bijective (gaugeFieldAtLevelValues (L := L) (m := m) (K := K) (k := 0)))
    (v : PositivelyOrientedBond L m (levelDepth K 0) → ComplexMatrix2.specialUnitary) :
    gaugeFieldOfPositive v ∈ gaugeFieldsAtLevel L m K 0 := by
  obtain ⟨U, hU⟩ := hb.2 v
  have hval : ∀ b : PositivelyOrientedBond L m (levelDepth K 0),
      U.1 b.1 = (v b : ComplexMatrix2) := fun b =>
    congrArg Subtype.val (congrFun hU b)
  have heq : gaugeFieldOfPositive v = U.1 := by
    funext b
    by_cases h : b.IsPositivelyOriented
    · simp only [gaugeFieldOfPositive, dif_pos h]
      exact (hval ⟨b, h⟩).symm
    · have h' := opposite_isPositivelyOriented b h
      have hopp : U.1 b.opposite.opposite = (U.1 b.opposite)⁻¹ :=
        (show IsGaugeField compactGaugeGroup univ U.1 from U.2).2 b.opposite (mem_univ _)
      simp only [gaugeFieldOfPositive, dif_neg h, dif_pos h']
      rw [← hval ⟨b.opposite, h'⟩]
      exact hopp.symm
  rw [heq]
  exact U.2
theorem haarAndWilsonInvariance_holds (hspace : GaugeFieldSpace.FieldSpaceAndPartitionBounds)
    (hgauge : WilsonActionGaugeInvariant) : HaarAndWilsonInvariance := by
  refine ⟨haarIsLeftInvariantProbability_holds hspace,
    haarIsInversionAndTranslationInvariant_holds, fun s u hu => ?_⟩
  let w : SiteAtLevel s.L s.m s.K 0 → ComplexMatrix2.specialUnitary := fun x => ⟨u x, hu x⟩
  have hfield := (hspace s).1
  refine ⟨⟨gaugeTransformEquiv w, fun U => rfl, continuous_gaugeTransformEquiv w, ?_,
    fun E _ => productHaarMeasure_image_preimage_gaugeTransformEquiv w E⟩, fun β _ F _ => ?_⟩
  · have hcont := continuous_gaugeTransformEquiv (K := s.K) (k := 0) fun x => (w x)⁻¹
    exact hcont
  · have : Finite (Plaquette s.L s.m ((s.K : ℕ) : ℤ)) := hfield.2.1
    refine integral_wilsonGibbsMeasure_gaugeTransform (s.K : ℕ) β w (fun v => ?_) F
    exact hgauge s.L s.m s.K s.isAdmissible.1 s.isAdmissible.2 s.m.pos
      s.K.pos _ (gaugeFieldOfPositive_mem_gaugeFieldsAtLevel hfield.2.2.1 v) u hu
end PeriodicLattice.HaarWilsonInvarianceProof
end YangMills.Construction
