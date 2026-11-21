import YangMills.Construction.InfiniteLattice.RulesOfTheActionOfTheLatticeIsometries
import YangMills.Construction.ReflectionPositivity.IntegralOverTheTwoHalvesFactorsProof
import YangMills.Construction.ReflectionPositivity.PerturbedTorusMeasuresHaveAllTheMirrorsOfTheLadderProof
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.InfiniteLattice
namespace SplitTorusPullback
open PeriodSublattice NormalFamilies
variable (Γ : PeriodSublattice 1)
theorem linkMap_opposite (r : LatticeSymmetry 1) (b : Link 1) :
    r.linkMap b.opposite = (r.linkMap b).opposite :=
  InfiniteLattice.Link.ext rfl rfl
theorem link_opposite_opposite (b : Link 1) : b.opposite.opposite = b :=
  InfiniteLattice.Link.ext rfl rfl
theorem linkMap_of_comp_eq {r s t : LatticeSymmetry 1} (h : t.toFun = r.toFun ∘ s.toFun)
    (b : Link 1) : t.linkMap b = r.linkMap (s.linkMap b) :=
  InfiniteLattice.Link.ext (Subtype.ext (congrFun h _)) (Subtype.ext (congrFun h _))
theorem orientedValue_pullbackField {r : LatticeSymmetry 1} (hr : Γ.MapsOrbits r)
    (U : Γ.QuotientField) (b : Link 1) :
    Γ.orientedValue (Γ.pullbackField r U) (Γ.orientedClass b) =
      Γ.orientedValue U (Γ.orientedClass (r.linkMap b)) := by
  by_cases h : b.IsPositivelyOriented
  · rw [Γ.orientedValue_positive _ ⟨b, h⟩, Γ.pullbackField_linkClass hr]
  · have hp := isPositivelyOriented_opposite_of_not h
    have h₁ := Γ.orientedValue_positive (Γ.pullbackField r U) ⟨b.opposite, hp⟩
    rw [Γ.pullbackField_linkClass hr] at h₁
    simp only [Γ.orientedValue_orientedClass] at h₁ ⊢
    rw [Γ.liftValue_opposite, linkMap_opposite, Γ.liftValue_opposite] at h₁
    exact inv_injective h₁
theorem pullbackField_apply_eq (r : LatticeSymmetry 1) (U : Γ.QuotientField) (b : Γ.QuotientLink) :
    Γ.pullbackField r U b =
      Γ.orientedValue U (Γ.orientedClass (r.linkMap (Γ.linkRep b).1)) :=
  rfl
theorem pullbackField_pullbackField {r s t : LatticeSymmetry 1} (hr : Γ.MapsOrbits r)
    (h : t.toFun = r.toFun ∘ s.toFun) (U : Γ.QuotientField) :
    Γ.pullbackField s (Γ.pullbackField r U) = Γ.pullbackField t U := by
  funext b
  rw [pullbackField_apply_eq, orientedValue_pullbackField Γ hr, pullbackField_apply_eq,
    linkMap_of_comp_eq h]
theorem pullbackField_involutive {r : LatticeSymmetry 1} (hr : Γ.MapsOrbits r)
    (h : ∀ x, r.toFun (r.toFun x) = x) :
    Function.Involutive (Γ.pullbackField r) := by
  intro U
  funext b
  have hb : r.linkMap (r.linkMap (Γ.linkRep b).1) = (Γ.linkRep b).1 :=
    InfiniteLattice.Link.ext (Subtype.ext (h _)) (Subtype.ext (h _))
  rw [pullbackField_apply_eq, orientedValue_pullbackField Γ hr, hb, Γ.orientedValue_positive]
  rw [Γ.linkClass_linkRep]
theorem lift_pullbackField {r : LatticeSymmetry 1} (hr : Γ.MapsOrbits r)
    (U : Γ.QuotientField) :
    Γ.lift (Γ.pullbackField r U) = r.pullbackField (Γ.lift U) := by
  apply Subtype.ext
  funext b
  have h := orientedValue_pullbackField Γ hr U b
  rw [Γ.orientedValue_orientedClass, Γ.orientedValue_orientedClass] at h
  exact h
theorem linkImage_injective {r : LatticeSymmetry 1} (hI : Γ.DescendsToQuotient r) :
    Function.Injective (Γ.linkImage r) := by apply _root_.YangMills.Construction.InfiniteLattice.HalvesFactorizationProof.linkImage_injective <;> assumption
open Classical in
def orientationSign (r : LatticeSymmetry 1) (b : Γ.QuotientLink) : ℤ :=
  if Γ.OrientedIsPositive (Γ.descendOrientedLink r (Γ.orientedOfLink b)) then 1 else -1
theorem orientationSign_eq_one_or_neg_one (r : LatticeSymmetry 1) (b : Γ.QuotientLink) :
    orientationSign Γ r b = 1 ∨ orientationSign Γ r b = -1 := by apply _root_.YangMills.Construction.InfiniteLattice.HalvesFactorizationProof.linkSign_eq_one_or_neg_one <;> assumption
theorem pullbackField_eq_relabelInvert {r : LatticeSymmetry 1} (hI : Γ.DescendsToQuotient r)
    (U : Γ.QuotientField) :
    Γ.pullbackField r U =
      Matrices.ComplexMatrix2.relabelInvert (Γ.linkImage r) (orientationSign Γ r) U := by
  funext b
  have hcl : Γ.orientedClass (r.linkMap (Γ.linkRep b).1) =
      Γ.descendOrientedLink r (Γ.orientedOfLink b) :=
    (hI.descendOrientedLink_orientedClass _).symm
  rw [pullbackField_apply_eq, hcl, Matrices.ComplexMatrix2.relabelInvert, orientationSign]
  by_cases h : Γ.OrientedIsPositive (Γ.descendOrientedLink r (Γ.orientedOfLink b))
  · rw [if_pos h, zpow_one, linkImage, dif_pos h]
    have hv := Γ.orientedValue_positive U ⟨_, h⟩
    rwa [Γ.orientedClass_orientedRep] at hv
  · rw [if_neg h, zpow_neg_one, linkImage, dif_neg h]
    have hv := Γ.orientedValue_opposite U ⟨_, isPositivelyOriented_opposite_of_not h⟩
    simp only [link_opposite_opposite, Γ.orientedClass_orientedRep] at hv
    exact hv
theorem isHomeomorph_pullbackField_and_preserves [Finite Γ.QuotientLink]
    (hrel : Matrices.ComplexMatrix2.RelabelInvertPreservesHaar)
    {r : LatticeSymmetry 1} (hI : Γ.DescendsToQuotient r) :
    IsHomeomorph (Γ.pullbackField r) ∧
      PreservesFiniteMeasure (Γ.pullbackField r) Γ.quotientHaar := by
  have hb : Function.Bijective (Γ.linkImage r) :=
    Finite.injective_iff_bijective.1 (linkImage_injective Γ hI)
  obtain ⟨hh, hi⟩ := hrel Γ.QuotientLink Γ.QuotientLink (Γ.linkImage r) (orientationSign Γ r) hb
    (orientationSign_eq_one_or_neg_one Γ r)
  have he : Γ.pullbackField r =
      Matrices.ComplexMatrix2.relabelInvert (Γ.linkImage r) (orientationSign Γ r) :=
    funext (pullbackField_eq_relabelInvert Γ hI)
  rw [he]
  refine ⟨hh, hh.continuous.measurable, ?_, fun F hF hC => hi F hF hC⟩
  unfold quotientHaar Matrices.ComplexMatrix2.haarPi
  infer_instance
theorem quotientFaceEnergy_pullbackField (hrules : SymmetryActionRules.Statement)
    (hE : Γ.QuotientLiftFacts) {r : LatticeSymmetry 1} (hr : Γ.MapsOrbits r)
    (U : Γ.QuotientField) (p : Γ.QuotientPlaquette) :
    Γ.quotientFaceEnergy (Γ.pullbackField r U) p =
      Γ.quotientFaceEnergy U (Γ.descendFace r p) := by
  set q := Γ.plaquetteRep p with hq
  have hself : ∀ q' : ElementaryPlaquette 1, q' ∈ Γ.plaquetteOrbit q' := by
    intro q'
    refine ⟨0, zero_mem _, ?_⟩
    have h0 := (((hrules (shift 0) (shift 0)).2.2.2.1 q').1 q').2
    refine h0 ?_
    have hid : (shift (0 : LatticePoint 1)).pointMap = id := by
      funext x
      apply Subtype.ext
      simp [LatticeSymmetry.pointMap, shift]
    rw [hid, Set.image_id]
  have hrule := congrFun ((hrules r r).2.2.2.1 q).2 (Γ.lift U)
  have hlift : Γ.IsLiftOfPlaquette (r.plaquetteMap q) (Γ.descendFace r p) :=
    hself _
  have hlift' : Γ.IsLiftOfPlaquette (Γ.quotientPlaquette_nonempty (Γ.descendFace r p)).some
      (Γ.descendFace r p) :=
    (Γ.quotientPlaquette_nonempty _).some_mem
  have hl := hE.faceEnergy_lifts_eq _ U _ _ hlift hlift'
  change faceEnergy (Γ.lift (Γ.pullbackField r U)) q =
    faceEnergy (Γ.lift U) _
  rw [lift_pullbackField Γ hr, ← hl]
  exact hrule
theorem totalFaceEnergy_pullbackField (hrules : SymmetryActionRules.Statement)
    (hE : Γ.QuotientLiftFacts) {r : LatticeSymmetry 1} (hr : Γ.MapsOrbits r)
    (hI : Γ.DescendsToQuotient r) (U : Γ.QuotientField) :
    Γ.totalFaceEnergy (Γ.pullbackField r U) = Γ.totalFaceEnergy U := by
  unfold totalFaceEnergy
  simp only [quotientFaceEnergy_pullbackField Γ hrules hE hr U]
  exact finsum_comp_equiv (Equiv.ofBijective _ hI.descendFace_bijective)
theorem totalFaceEnergy_nonneg (hE : Γ.QuotientLiftFacts) (U : Γ.QuotientField) :
    0 ≤ Γ.totalFaceEnergy U := by
  have := hE.finite_quotientPlaquette
  have := Fintype.ofFinite Γ.QuotientPlaquette
  unfold totalFaceEnergy
  rw [finsum_eq_sum_of_fintype]
  exact Finset.sum_nonneg fun p _ => (hE.quotientFaceEnergy_mem_Icc p U).1
theorem boltzmannWeight_eq_exp (β : ℝ) (U : Γ.QuotientField) :
    Γ.boltzmannWeight β U = Real.exp (-β * Γ.totalFaceEnergy U) :=
  rfl
theorem measurable_boltzmannWeight (hE : Γ.QuotientLiftFacts) (β : ℝ) :
    Measurable (Γ.boltzmannWeight β) := by apply _root_.YangMills.Construction.NormalFamilies.RungReflection.measurable_boltzmannWeight <;> assumption
theorem boltzmannWeight_pos (β : ℝ) (U : Γ.QuotientField) : 0 < Γ.boltzmannWeight β U :=
  Real.exp_pos _
theorem boltzmannWeight_le_one (hE : Γ.QuotientLiftFacts) {β : ℝ} (hβ : 0 < β)
    (U : Γ.QuotientField) : Γ.boltzmannWeight β U ≤ 1 := by
  rw [boltzmannWeight_eq_exp, Real.exp_le_one_iff]
  have := mul_nonneg hβ.le (totalFaceEnergy_nonneg Γ hE U)
  linarith
instance isProbabilityMeasure_quotientHaar : IsProbabilityMeasure Γ.quotientHaar := by
  unfold quotientHaar Matrices.ComplexMatrix2.haarPi
  infer_instance
theorem integrable_boltzmannWeight (hE : Γ.QuotientLiftFacts) {β : ℝ} (hβ : 0 < β) :
    Integrable (Γ.boltzmannWeight β) Γ.quotientHaar := by
  refine (integrable_const (1 : ℝ)).mono' (measurable_boltzmannWeight Γ hE β).aestronglyMeasurable
    (Filter.Eventually.of_forall fun U => ?_)
  rw [Real.norm_of_nonneg (boltzmannWeight_pos Γ β U).le]
  exact boltzmannWeight_le_one Γ hE hβ U
theorem integral_withDensity_boltzmannWeight (hE : Γ.QuotientLiftFacts) (β : ℝ)
    (g : Γ.QuotientField → ℂ) :
    ∫ U, g U ∂(Γ.quotientHaar.withDensity fun U => ENNReal.ofReal (Γ.boltzmannWeight β U)) =
      ∫ U, Γ.boltzmannWeight β U • g U ∂Γ.quotientHaar := by
  rw [integral_withDensity_eq_integral_toReal_smul (measurable_boltzmannWeight Γ hE β).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (boltzmannWeight_pos Γ β _).le]
theorem preservesFiniteMeasure_withDensity (hE : Γ.QuotientLiftFacts) {β : ℝ} (hβ : 0 < β)
    {φ : Γ.QuotientField → Γ.QuotientField}
    (hφ : PreservesFiniteMeasure φ Γ.quotientHaar)
    (hw : ∀ U, Γ.boltzmannWeight β (φ U) = Γ.boltzmannWeight β U) :
    PreservesFiniteMeasure φ
      (Γ.quotientHaar.withDensity fun U => ENNReal.ofReal (Γ.boltzmannWeight β U)) := by
  refine ⟨hφ.1, ?_, fun F hF ⟨C, hC⟩ => ?_⟩
  · exact isFiniteMeasure_withDensity_ofReal (integrable_boltzmannWeight Γ hE hβ).2
  · rw [integral_withDensity_boltzmannWeight Γ hE, integral_withDensity_boltzmannWeight Γ hE]
    have hG := hφ.2.2 (fun U => Γ.boltzmannWeight β U • F U)
      ((measurable_boltzmannWeight Γ hE β).smul hF) ⟨C, fun U => ?_⟩
    · simpa only [hw] using hG
    · rw [norm_smul, Real.norm_of_nonneg (boltzmannWeight_pos Γ β U).le]
      have h1 := boltzmannWeight_le_one Γ hE hβ U
      calc Γ.boltzmannWeight β U * ‖F U‖ ≤ 1 * ‖F U‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ ≤ C := by simpa using hC U
theorem preservesFiniteMeasure_gibbsMeasure (hE : Γ.QuotientLiftFacts) {β : ℝ} (hβ : 0 < β)
    {φ : Γ.QuotientField → Γ.QuotientField}
    (hφ : PreservesFiniteMeasure φ
      (Γ.quotientHaar.withDensity fun U => ENNReal.ofReal (Γ.boltzmannWeight β U))) :
    PreservesFiniteMeasure φ (Γ.gibbsMeasure β) := by
  have hZ : 0 < Γ.partitionFunction β := by
    have h := integral_exp_pos (μ := Γ.quotientHaar) (f := fun U => -β * Γ.totalFaceEnergy U)
      (integrable_boltzmannWeight Γ hE hβ)
    exact h
  have hc : (ENNReal.ofReal (Γ.partitionFunction β))⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hZ).ne'
  have := hφ.2.1
  refine ⟨hφ.1, Measure.smul_finite _ hc, fun F hF hC => ?_⟩
  unfold gibbsMeasure
  rw [integral_smul_measure, integral_smul_measure, hφ.2.2 F hF hC]
end SplitTorusPullback
open PeriodSublattice NormalFamilies SplitTorusPullback
theorem splitTorusPullbacks_holds
    (hdesc : SplitTorusDescent)
    (hext : PeriodicQuotient.FinitenessClaim)
    (hrel : Matrices.ComplexMatrix2.RelabelInvertPreservesHaar)
    (hrules : SymmetryActionRules.Statement) :
    SplitTorusPullbacks := by
  intro β hβ Γ n hn z hs
  have hE : Γ.QuotientLiftFacts := hext.1 Γ
  have := hE.finite_quotientLink
  have h0 : IsAllowedLevel 1 n 0 := ⟨fun _ => ⟨0, by simp⟩, fun _ => ⟨0, by simp⟩⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hfam, -, -, -, -⟩ := hdesc Γ n hn z 0 h0 0 hs
  refine ⟨fun c hc => ?_, fun r hr => ?_, fun γ hγ F _ => ?_, fun F _ F' _ => ⟨rfl, rfl⟩,
    fun F _ => rfl⟩
  · intro P
    have hPf : IsClassIsometry n P.reflectSymmetry.toFun :=
      isClassIsometry_reflectAcross hc
    obtain ⟨hC, hI⟩ := hfam _ hPf
    have hinv : ∀ x, P.reflectSymmetry.toFun (P.reflectSymmetry.toFun x) = x := by
      intro x
      change reflectAcross n c (reflectAcross n c x) = x
      have hd : n ⬝ᵥ dualVector n = 1 := dotProduct_dualVector hn
      have h1 : n ⬝ᵥ reflectAcross n c x = 2 * c - n ⬝ᵥ x := by
        simp only [reflectAcross, dotProduct_sub, dotProduct_smul, hd, smul_eq_mul]
        ring
      rw [reflectAcross, h1]
      simp only [reflectAcross]
      ext μ
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hinvol := pullbackField_involutive Γ hC hinv
    refine ⟨hinvol, fun F _ => ?_, fun F F' _ _ => ⟨?_, ?_⟩, fun w F _ => ?_, fun F _ => ?_⟩
    · funext U
      change conj (F (P.reflectSymmetry.pullbackField (Γ.lift U))) =
        conj (F (Γ.lift (Γ.pullbackField P.reflectSymmetry U)))
      rw [lift_pullbackField Γ hC]
    · funext U
      simp [conjReflect, compPullback]
    · funext U
      simp [conjReflect, compPullback]
    · funext U
      simp [conjReflect, compPullback]
    · funext U
      simp only [conjReflect, compPullback, Complex.conj_conj]
      rw [hinvol U]
  · obtain ⟨hC, hI⟩ := hfam r hr
    obtain ⟨hh, hm⟩ := isHomeomorph_pullbackField_and_preserves Γ hrel hI
    have hw : ∀ U, Γ.boltzmannWeight β (Γ.pullbackField r U) = Γ.boltzmannWeight β U := by
      intro U
      rw [boltzmannWeight_eq_exp, boltzmannWeight_eq_exp,
        totalFaceEnergy_pullbackField Γ hrules hE hC hI]
    have hd := preservesFiniteMeasure_withDensity Γ hE hβ hm hw
    refine ⟨hh, hm, fun U b => orientedValue_pullbackField Γ hC U b, fun s _ he => ?_,
      lift_pullbackField Γ hC, fun F _ => ?_,
      fun F ⟨hF, C, hB⟩ => ⟨⟨?_, C, fun U => hB _⟩, ?_, rfl, ?_⟩,
      fun F F' _ _ => rfl, fun s t hs' h F _ => ?_, fun p => ?_, ?_, hd,
      preservesFiniteMeasure_gibbsMeasure Γ hE hβ hd⟩
    · obtain ⟨hC', hI'⟩ := hfam s ‹_›
      funext U b
      rw [pullbackField_apply_eq, pullbackField_apply_eq, ← hI.descendOrientedLink_orientedClass,
        ← hI'.descendOrientedLink_orientedClass, he]
    · funext U
      change F (r.pullbackField (Γ.lift U)) = F (Γ.lift (Γ.pullbackField r U))
      rw [lift_pullbackField Γ hC]
    · exact hF.comp hm.1
    · exact hh.surjective.iSup_comp fun V => ‖F V‖
    · intro 𝓜 hD U U' hUU
      refine hD _ _ fun b hb => ?_
      rw [pullbackField_eq_relabelInvert Γ hI U, pullbackField_eq_relabelInvert Γ hI U',
        Matrices.ComplexMatrix2.relabelInvert, Matrices.ComplexMatrix2.relabelInvert,
        hUU _ ⟨b, hb, rfl⟩]
    · funext U
      change F (Γ.pullbackField s (Γ.pullbackField r U)) = F (Γ.pullbackField t U)
      rw [pullbackField_pullbackField Γ hC h]
    · funext U
      exact quotientFaceEnergy_pullbackField Γ hrules hE hC U p
    · funext U
      exact totalFaceEnergy_pullbackField Γ hrules hE hC hI U
  · funext U
    change F ((shift γ).pullbackField (Γ.lift U)) = F (Γ.lift U)
    rw [hE.lift_shift_invariant U γ hγ]
end YangMills.Construction.InfiniteLattice
