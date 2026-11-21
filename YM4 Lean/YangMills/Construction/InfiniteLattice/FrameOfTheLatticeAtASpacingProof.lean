import YangMills.Construction.InfiniteLattice.ActionsOfALatticeIsometryProof
import YangMills.Construction.InfiniteLattice.FrameOfTheLatticeAtASpacing
import YangMills.Construction.InfiniteLattice.LatticeIsometriesOfASpacingAsMotionsAndTheirActionProof
import YangMills.Construction.InfiniteLattice.ReflectionFormAndTransferOperatorOfAPeriodicGibbsStateProof
import YangMills.Construction.InfiniteLattice.SpaceOfConfigurationsAndSpaceOfMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.LatticeAtSpacing
open YangMills.Construction.InfiniteLattice (Link GaugeField LatticePoint LatticeSymmetry
  IsBoundedObservable IsLocalObservable IsShiftInvariant AmbientSpace condExpShiftInvariant
  shiftInvariantSigma longRangeOrderParameter observableSupNorm stateVariance regionObservables
  plateauPairing shift)
open YangMills.Construction.GibbsAtFixedSpacing (BorelProb continuousFns continuousLocal)
variable {a : ℝ}
namespace LatticeFrameFacts
theorem shiftInvariantSigma_le :
    shiftInvariantSigma a ≤ (inferInstance : MeasurableSpace (GaugeField a)) :=
  fun _ hs => hs.1
section CondExp
variable (μ : Measure (GaugeField a)) [IsProbabilityMeasure μ]
  {F G : GaugeField a → ℂ}
theorem integrable_of_isBoundedObservable (hF : IsBoundedObservable F) : Integrable F μ := by apply _root_.YangMills.Construction.InfiniteLattice.ReflectionPairingProof.integrable_of_isBoundedObservable <;> assumption
omit [IsProbabilityMeasure μ] in
theorem stronglyMeasurable_condExpShiftInvariant (F : GaugeField a → ℂ) :
    StronglyMeasurable (condExpShiftInvariant μ F) :=
  stronglyMeasurable_condExp.mono shiftInvariantSigma_le
omit [IsProbabilityMeasure μ] in
theorem exists_ae_norm_condExpShiftInvariant_le (hF : IsBoundedObservable F) :
    ∃ K : ℝ, ∀ᵐ ω ∂μ, ‖condExpShiftInvariant μ F ω‖ ≤ K := by
  obtain ⟨-, K, hK⟩ := id hF
  have hbd : ∀ᵐ ω ∂μ, |‖F ω‖| ≤ (K.toNNReal : ℝ) := ae_of_all _ fun ω => by
    rw [abs_of_nonneg (norm_nonneg _)]
    exact (hK ω).trans (Real.le_coe_toNNReal K)
  refine ⟨K.toNNReal, ?_⟩
  filter_upwards [norm_condExp_le (μ := μ) (m := shiftInvariantSigma a) F,
    ae_bdd_abs_condExp_of_ae_bdd_abs (m := shiftInvariantSigma a) hbd] with ω h₁ h₂
  exact h₁.trans ((le_abs_self _).trans h₂)
omit [IsProbabilityMeasure μ] in
theorem integrable_condExpShiftInvariant (F : GaugeField a → ℂ) :
    Integrable (condExpShiftInvariant μ F) μ :=
  integrable_condExp
theorem integral_condExpShiftInvariant (F : GaugeField a → ℂ) :
    ∫ ω, condExpShiftInvariant μ F ω ∂μ = ∫ ω, F ω ∂μ :=
  integral_condExp shiftInvariantSigma_le
omit [IsProbabilityMeasure μ] in
theorem integrable_mul_of_ae_norm_le {f g : GaugeField a → ℂ} (hf : StronglyMeasurable f) {K : ℝ}
    (hK : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ K) (hg : Integrable g μ) : Integrable (fun ω => f ω * g ω) μ :=
  hg.bdd_mul hf.aestronglyMeasurable hK
theorem integral_condExp_mul_condExp (hF : IsBoundedObservable F) (hG : IsBoundedObservable G) :
    ∫ ω, condExpShiftInvariant μ F ω * condExpShiftInvariant μ G ω ∂μ =
      ∫ ω, F ω * condExpShiftInvariant μ G ω ∂μ := by
  obtain ⟨K, hK⟩ := exists_ae_norm_condExpShiftInvariant_le μ hG
  have hFi := integrable_of_isBoundedObservable μ hF
  have hprod : Integrable (fun ω => condExpShiftInvariant μ G ω * F ω) μ :=
    integrable_mul_of_ae_norm_le μ (stronglyMeasurable_condExpShiftInvariant μ G) hK hFi
  have hpull := condExp_bilin_of_stronglyMeasurable_left (m := shiftInvariantSigma a) (μ := μ)
    (ContinuousLinearMap.mul ℝ ℂ) (f := condExpShiftInvariant μ G) (g := F)
    stronglyMeasurable_condExp hprod hFi
  have hswap : ∫ ω, condExpShiftInvariant μ G ω * condExpShiftInvariant μ F ω ∂μ =
      ∫ ω, condExpShiftInvariant μ G ω * F ω ∂μ := by
    rw [← integral_condExp (m := shiftInvariantSigma a) (μ := μ) shiftInvariantSigma_le
      (f := fun ω => condExpShiftInvariant μ G ω * F ω)]
    exact integral_congr_ae (hpull.mono fun ω hω => hω.symm)
  simpa only [mul_comm] using hswap
theorem conj_condExpShiftInvariant_ae_eq (hF : IsBoundedObservable F) :
    (fun ω => conj (condExpShiftInvariant μ F ω)) =ᵐ[μ]
      condExpShiftInvariant μ (fun ω => conj (F ω)) :=
  (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp_condExp_comm (m := shiftInvariantSigma a)
    (integrable_of_isBoundedObservable μ hF)
theorem longRangeOrderParameter_eq (hF : IsBoundedObservable F) :
    longRangeOrderParameter μ F =
      ((∫ ω, ‖condExpShiftInvariant μ F ω - ∫ η, F η ∂μ‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  obtain ⟨K, hK⟩ := exists_ae_norm_condExpShiftInvariant_le μ hF
  set E := condExpShiftInvariant μ F with hE
  set m := ∫ η, F η ∂μ with hm
  have hEi : Integrable E μ := integrable_condExpShiftInvariant μ F
  have hEs : StronglyMeasurable E := stronglyMeasurable_condExpShiftInvariant μ F
  have hmean : ∫ ω, E ω ∂μ = m := integral_condExpShiftInvariant μ F
  have hconj : Integrable (fun ω => conj (E ω)) μ :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hEi
  have hsq : Integrable (fun ω => conj (E ω) * E ω) μ := by
    refine integrable_mul_of_ae_norm_le μ (f := fun ω => conj (E ω)) ?_ (K := K) ?_ hEi
    · exact (Complex.continuous_conj.comp_stronglyMeasurable hEs)
    · filter_upwards [hK] with ω hω
      simpa using hω
  have hexpand : ∀ ω, ((‖E ω - m‖ ^ 2 : ℝ) : ℂ) =
      conj (E ω) * E ω - conj m * E ω - m * conj (E ω) + conj m * m := by
    intro ω
    have := Complex.conj_mul' (E ω - m)
    push_cast at this ⊢
    rw [← this, map_sub]
    ring
  rw [← integral_complex_ofReal]
  simp_rw [hexpand]
  have j₁ : Integrable (fun ω => conj m * E ω) μ := hEi.const_mul _
  have j₂ : Integrable (fun ω => m * conj (E ω)) μ := hconj.const_mul _
  have j₃ : Integrable (fun ω => conj (E ω) * E ω - conj m * E ω) μ := hsq.sub j₁
  have j₄ : Integrable (fun ω => conj (E ω) * E ω - conj m * E ω - m * conj (E ω)) μ := j₃.sub j₂
  rw [integral_add j₄ (integrable_const _), integral_sub j₃ j₂, integral_sub hsq j₁,
    integral_const_mul, integral_const_mul, integral_conj, hmean]
  simp only [integral_const, probReal_univ, one_smul]
  have hlro : longRangeOrderParameter μ F = (∫ ω, conj (E ω) * E ω ∂μ) - conj m * m := by
    rw [Complex.conj_mul']
    simp only [longRangeOrderParameter, plateauPairing, hE, hm]
    push_cast
    rfl
  rw [hlro]
  ring
theorem condExpShiftInvariant_shift_ae_eq (hμ : IsShiftInvariant μ) (v : LatticePoint a)
    (hF : IsBoundedObservable F) (hsF : IsBoundedObservable ((shift v).actOn F)) :
    condExpShiftInvariant μ ((shift v).actOn F) =ᵐ[μ] condExpShiftInvariant μ F := by
  have hFi := integrable_of_isBoundedObservable μ hF
  refine (ae_eq_condExp_of_forall_setIntegral_eq (m := shiftInvariantSigma a) shiftInvariantSigma_le
    (integrable_of_isBoundedObservable μ hsF)
    (fun s _ _ => (integrable_condExpShiftInvariant μ F).integrableOn)
    (fun s hs _ => ?_) stronglyMeasurable_condExp.aestronglyMeasurable).symm
  have hsm : MeasurableSet s := hs.1
  have hback : (shift v).pullbackField ⁻¹' s = s :=
    ((shift v).actOn_indicator_eq_iff s).mp (hs.2 v)
  have hcut : (shift v).actOn (s.indicator F) = s.indicator ((shift v).actOn F) := by
    funext ω
    have hω : (shift v).pullbackField ω ∈ s ↔ ω ∈ s := by
      conv_rhs => rw [← hback]
      rfl
    by_cases hin : ω ∈ s
    · simp [LatticeSymmetry.actOn, Set.indicator, hω, hin]
    · simp [LatticeSymmetry.actOn, Set.indicator, hω, hin]
  have hbd : IsBoundedObservable (s.indicator F) := by
    obtain ⟨hmeas, K, hK⟩ := hF
    refine ⟨hmeas.indicator hsm, max K 0, fun ω => ?_⟩
    by_cases hin : ω ∈ s
    · rw [Set.indicator_of_mem hin]
      exact (hK ω).trans (le_max_left _ _)
    · rw [Set.indicator_of_notMem hin, norm_zero]
      exact le_max_right _ _
  refine (setIntegral_condExp shiftInvariantSigma_le hFi hs).trans ?_
  rw [← integral_indicator hsm, ← integral_indicator hsm, ← hcut]
  exact (hμ v _ hbd).symm
theorem plateauPairing_conj (hF : IsBoundedObservable F) (hG : IsBoundedObservable G) :
    plateauPairing μ (fun ω => conj (F ω)) G = ∫ ω, F ω * condExpShiftInvariant μ G ω ∂μ := by
  have hc : IsBoundedObservable (fun ω => conj (F ω)) := by
    obtain ⟨hmeas, K, hK⟩ := hF
    exact ⟨Complex.continuous_conj.measurable.comp hmeas, K, fun ω => by simpa using hK ω⟩
  have hcc := conj_condExpShiftInvariant_ae_eq μ hc
  have hcc' : (fun ω => conj (condExpShiftInvariant μ (fun ω => conj (F ω)) ω)) =ᵐ[μ]
      condExpShiftInvariant μ F := by
    simpa only [Complex.conj_conj] using hcc
  rw [← integral_condExp_mul_condExp μ hF hG]
  exact integral_congr_ae (hcc'.mono fun ω hω => by simp only [hω])
theorem exists_ae_eq_const_of_zero_one
    (hμ : ∀ I : Set (GaugeField a), MeasurableSet[shiftInvariantSigma a] I → μ I = 0 ∨ μ I = 1)
    {J : GaugeField a → ℂ} (hJ : Measurable[shiftInvariantSigma a] J) :
    ∃ z : ℂ, J =ᵐ[μ] fun _ => z := by
  refine Filter.exists_eventuallyEq_const_of_forall_separating MeasurableSet fun W hW => ?_
  have hI : MeasurableSet[shiftInvariantSigma a] (J ⁻¹' W) := hJ hW
  rcases hμ _ hI with h | h
  · exact Or.inr (measure_eq_zero_iff_ae_notMem.mp h)
  · refine Or.inl ?_
    have h₀ : μ (J ⁻¹' W)ᶜ = 0 := (prob_compl_eq_zero_iff (shiftInvariantSigma_le _ hI)).mpr h
    exact measure_eq_zero_iff_ae_notMem.mp h₀ |>.mono fun ω hω => by simpa using hω
theorem const_eq_integral_of_ae_eq_const {J : GaugeField a → ℂ} {z : ℂ}
    (h : J =ᵐ[μ] fun _ => z) : z = ∫ ω, J ω ∂μ := by
  rw [integral_congr_ae h]
  simp
end CondExp
theorem linkMap_linkMap {t r : LatticeSymmetry a}
    (h : Function.LeftInverse t.toFun r.toFun) (e : Link a) : t.linkMap (r.linkMap e) = e := by apply _root_.YangMills.Construction.InfiniteLattice.SymmetryActions.linkMap_linkMap <;> assumption
theorem pullbackField_pullbackField {t r : LatticeSymmetry a}
    (h : Function.LeftInverse r.toFun t.toFun) (U : GaugeField a) :
    t.pullbackField (r.pullbackField U) = U := by apply _root_.YangMills.Construction.InfiniteLattice.SymmetriesAsMotions.pullbackField_pullbackField <;> assumption
end LatticeFrameFacts
open LatticeFrameFacts
theorem compactMetrizableFieldsAndStates_of (a : ℝ)
    (hs : CompactSpace (BorelProb a) ∧ TopologicalSpace.MetrizableSpace (BorelProb a))
    (hf : InfiniteLattice.BasicStructure.CompactAndLocalDense a)
    (ht : InfiniteLattice.BasicStructure.StateFacts a) :
    CompactMetrizableFieldsAndStates a := by
  obtain ⟨hc, hm, -, hsub, -⟩ := hf
  refine ⟨hc, hm, hs.1, hs.2, fun μ μ' h => ?_⟩
  have := ht.1 μ.1 μ'.1 μ.2 μ'.2 fun F hF => h F (hsub hF)
  exact Subtype.ext this
theorem continuousLocalDenseSubalgebra_of (a : ℝ)
    (hf : InfiniteLattice.BasicStructure.CompactAndLocalDense a) :
    ContinuousLocalDenseSubalgebra a := by
  obtain ⟨-, -, -, hsub, hadd, -, hconst, hconj, ⟨𝒟, hc, h𝒟, hd⟩, hdense, -⟩ := hf
  have hsame : InfiniteLattice.continuousLocalFunctions a = continuousLocal a := by
    ext F
    exact ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨h₃, h₁, h₂⟩, fun ⟨h₁, h₂, h₃⟩ => ⟨h₂, h₃, h₁⟩⟩
  rw [hsame] at hsub hadd hconst hconj h𝒟 hdense
  have hne : 𝒟.Nonempty := by
    obtain ⟨H, hH, -⟩ := hd.2 (fun _ => 0) continuous_const 1 one_pos
    exact ⟨H, hH⟩
  obtain ⟨f, hf⟩ := hc.exists_eq_range hne
  refine ⟨hsub, ⟨{ carrier := continuousLocal a
                   mul_mem' := fun hF hF' => (hadd _ hF _ hF').2
                   add_mem' := fun hF hF' => (hadd _ hF _ hF').1
                   one_mem' := hconst 1
                   zero_mem' := hconst 0
                   algebraMap_mem' := fun z => hconst z }, rfl⟩, hconst, hconj, hdense.2,
    f, fun n => h𝒟 (hf ▸ mem_range_self n), fun F hF ε hε => ?_⟩
  obtain ⟨H, hH, hlt⟩ := hd.2 F hF ε hε
  rw [hf] at hH
  obtain ⟨n, rfl⟩ := hH
  exact ⟨n, hlt⟩
theorem symmetryActionProperties_of (ha : 0 < a)
    (h : InfiniteLattice.SymmetryActionOnObservables)
    (r r' : LatticeSymmetry a) : SymmetryActionProperties r r' := by
  obtain ⟨-, hpull, -, hcomp, -, hnorm, -, -, hloc, hinv, -⟩ := h ⟨a, ha⟩
  have hact := (h ⟨a, ha⟩).2.2.1
  obtain ⟨-, ⟨t₀, ht₀⟩, -⟩ := hinv r
  have hsets : ∀ S : Set AmbientSpace, r.actOn '' regionObservables a S =
      regionObservables a (r.setImage S) := (hact r).2
  refine ⟨?_, (hcomp r r').1, ⟨t₀, ht₀⟩, fun t ht => ?_, ?_, fun F F' _ _ => rfl,
    fun F _ => rfl, fun F hF => ((hnorm r).2 F hF).2.2.2, hsets,
    fun F hF => (hcomp r r').2 F hF, fun z z' F F' _ _ => rfl,
    fun F _ hc => hc.comp (hpull r).2.continuous, fun F hF hl => ?_⟩
  · exact Function.bijective_iff_has_inverse.mpr
      ⟨t₀.linkMap, linkMap_linkMap ht₀.1, linkMap_linkMap ht₀.2⟩
  · exact ⟨{ toFun := r.pullbackField
             invFun := t.pullbackField
             left_inv := pullbackField_pullbackField ht.2
             right_inv := pullbackField_pullbackField ht.1
             continuous_toFun := (hpull r).2.continuous
             continuous_invFun := (hpull t).2.continuous }, rfl, rfl⟩
  · rfl
  · obtain ⟨S, hS, hmeas⟩ := hl
    have hmem : F ∈ InfiniteLattice.localRegionObservables a univ := by
      refine mem_iUnion₂.mpr ⟨S, hS, ?_⟩
      rw [univ_inter]
      exact ⟨hF, hmeas⟩
    have himg : r.actOn F ∈ InfiniteLattice.localRegionObservables a (r.setImage univ) := by
      rw [← hloc.1 r univ]
      exact ⟨F, hmem, rfl⟩
    obtain ⟨Q, hQ, hF'⟩ := mem_iUnion₂.mp himg
    exact ⟨r.setImage univ ∩ Q, Bornology.IsBounded.subset hQ inter_subset_right, hF'.2⟩
theorem plateauAndOrderOfInvariantState_of (ha : 0 < a)
    (h : InfiniteLattice.SymmetryActionOnObservables)
    (μ : BorelProb a) (hμ : IsShiftInvariant μ.1) : PlateauAndOrderOfInvariantState μ := by
  have : IsProbabilityMeasure μ.1 := μ.2
  have hact := (h ⟨a, ha⟩).2.2.1
  intro F G hF hG v
  have hsF : IsBoundedObservable ((shift v).actOn F) :=
    ((hact (shift v)).1 F F hF hF).1
  have hsG : IsBoundedObservable ((shift v).actOn G) :=
    ((hact (shift v)).1 G G hG hG).1
  have hdF := condExpShiftInvariant_shift_ae_eq μ.1 hμ v hF hsF
  have hdG := condExpShiftInvariant_shift_ae_eq μ.1 hμ v hG hsG
  have hmean : ∫ ω, condExpShiftInvariant μ.1 F ω ∂μ.1 = ∫ ω, F ω ∂μ.1 :=
    integral_condExpShiftInvariant μ.1 F
  refine ⟨longRangeOrderParameter_eq μ.1 hF, ?_, ?_, hdF, ?_, plateauPairing_conj μ.1 hF hG⟩
  · simp only [stateVariance, hmean]
  · exact integral_nonneg fun ω => by positivity
  · refine integral_congr_ae ?_
    filter_upwards [hdF, hdG] with ω h₁ h₂
    simp only [h₁, h₂]
theorem ergodicInvariantFunctionsConstant_of (μ : BorelProb a) (hμ : IsErgodicState μ) :
    ErgodicInvariantFunctionsConstant μ := by
  have : IsProbabilityMeasure μ.1 := μ.2
  have hconst : ∀ G : GaugeField a → ℂ,
      condExpShiftInvariant μ.1 G =ᵐ[μ.1] fun _ => ∫ ω, G ω ∂μ.1 := by
    intro G
    obtain ⟨z, hz⟩ := exists_ae_eq_const_of_zero_one μ.1 hμ.2 (J := condExpShiftInvariant μ.1 G)
      (stronglyMeasurable_condExp (m := shiftInvariantSigma a) (μ := μ.1) (f := G)).measurable
    have hzi := (const_eq_integral_of_ae_eq_const μ.1 hz).trans (integral_condExpShiftInvariant μ.1 G)
    rw [hzi] at hz
    exact hz
  refine ⟨fun J hJ _ => ?_, fun _ F G _ _ => ⟨hconst G, ?_, ?_⟩⟩
  · obtain ⟨z, hz⟩ := exists_ae_eq_const_of_zero_one μ.1 hμ.2 hJ
    have hzi := const_eq_integral_of_ae_eq_const μ.1 hz
    rwa [hzi] at hz
  · have : plateauPairing μ.1 F G =
        ∫ _ : GaugeField a, conj (∫ ω, F ω ∂μ.1) * ∫ ω, G ω ∂μ.1 ∂μ.1 := by
      refine integral_congr_ae ?_
      filter_upwards [hconst F, hconst G] with ω h₁ h₂
      simp only [h₁, h₂]
    rw [this]
    simp
  · have : plateauPairing μ.1 F F =
        ∫ _ : GaugeField a, conj (∫ ω, F ω ∂μ.1) * ∫ ω, F ω ∂μ.1 ∂μ.1 := by
      refine integral_congr_ae ?_
      filter_upwards [hconst F] with ω h₁
      simp only [h₁]
    rw [longRangeOrderParameter, this]
    simp [Complex.conj_mul']
theorem latticeFrameAtSpacing_holds
    (h₁ : InfiniteLattice.SymmetryActionOnObservables)
    (h₂ : FieldsAtSpacing.CompactFieldsAndMeasures)
    (h₃ : InfiniteLattice.BasicStructure.Statement) :
    LatticeFrameAtSpacing := by
  intro a ha
  obtain ⟨hf, -, ht, -⟩ := h₃.1 a ha 1 one_pos
  exact ⟨compactMetrizableFieldsAndStates_of a (h₂ a ha).2.2.1 hf ht,
    continuousLocalDenseSubalgebra_of a hf, symmetryActionProperties_of ha h₁,
    plateauAndOrderOfInvariantState_of ha h₁,
    fun μ hμ => ergodicInvariantFunctionsConstant_of μ hμ⟩
end YangMills.Construction.ReflectionPositivity.LatticeAtSpacing
