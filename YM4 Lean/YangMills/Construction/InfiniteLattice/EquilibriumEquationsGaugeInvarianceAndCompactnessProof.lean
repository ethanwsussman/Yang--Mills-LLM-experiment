import YangMills.Construction.InfiniteLattice.ElementaryFactsOfBondsSpecificationAndGaugeTransformations
import YangMills.Construction.InfiniteLattice.EquilibriumEquationsGaugeInvarianceAndCompactness
import YangMills.Construction.InfiniteLattice.PeriodicExtensionOfTheWilsonMeasureIsInvariantUnderMotionsKeepingThePeriodsProof
import YangMills.Construction.InfiniteLattice.PeriodsFoldCompactnessAndLimitsOfToriProof
import YangMills.Construction.InfiniteLattice.ReflectionPositivityAndOneTranslationProof
import YangMills.Construction.InfiniteLattice.SpaceOfConfigurationsAndLatticeIsometries
import YangMills.Construction.InfiniteLattice.SpaceOfTheConfigurationsAtACutoffProof
import YangMills.Construction.Matrices.FiniteProductOfSpecialUnitary
import YangMills.Construction.ReflectionPositivity.SpaceOfConfigurationsAndPlaquetteEnergiesAtOneCutoff
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped NNReal Topology
noncomputable section
namespace YangMills.Construction.InfiniteLattice.GibbsClassProof
variable {a : ℝ}
theorem integrable_of_isBoundedObservable (ν : Measure (GaugeField a)) [IsFiniteMeasure ν]
    {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) : Integrable F ν := by apply _root_.YangMills.Construction.LatticeConventions.TranslationReflectionProof.integrable_of_isBoundedObservable <;> assumption
theorem integral_conditionalExpectation {ha : 0 < a} {β : ℝ} (hspec : SpecificationProperties ha β)
    (hloc : LocalFunctionProperties a) {ν : Measure (GaugeField a)}
    (hν : ν ∈ gibbsClass ha β) (W : LinkWindow a) {F : GaugeField a → ℂ}
    (hF : IsBoundedObservable F) :
    ∫ U, W.conditionalExpectation ha β F U ∂ν = ∫ U, F U ∂ν := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hlast⟩ := hspec W
  obtain ⟨μ', hprob, -, hint⟩ := hlast ν hν.1
  have hsep := hloc.2.2.2.2.2.1 μ' ν hprob hν.1 fun G hG =>
    (hint G hG.1).trans (hν.2 W G hG)
  subst hsep
  exact (hint F hF).symm
theorem linkSigma_le (hS : FieldSpace.SymmetryProperties) (ha : 0 < a)
    (ℬ : Set (Link a)) :
    linkSigma ℬ ≤ (inferInstance : MeasurableSpace (GaugeField a)) := by
  rw [(hS a ha).1.2.2]
  exact iSup₂_le fun b _ => le_iSup₂_of_le (f := fun b (_ : b ∈ (univ : Set (Link a))) =>
    MeasurableSpace.comap (fun U : GaugeField a => U b) inferInstance) b (mem_univ b) le_rfl
theorem kernelIsConditionalExpectation (hS : FieldSpace.SymmetryProperties)
    {ha : 0 < a} {β : ℝ} (hspec : SpecificationProperties ha β) (hloc : LocalFunctionProperties a)
    (W : LinkWindow a) : KernelIsConditionalExpectation ha β W := by
  intro F hF
  obtain ⟨-, -, -, -, -, -, h7, h8, -, -, -⟩ := hspec W
  refine ⟨(h7 F hF).2.1, fun ν hν => ?_⟩
  have hprob := hν.1
  have hle : W.exteriorSigma ≤ (inferInstance : MeasurableSpace (GaugeField a)) :=
    linkSigma_le hS ha _
  have key : ∀ H : GaugeField a → ℂ, Measurable[W.exteriorSigma] H → (∃ C : ℝ, ∀ U, ‖H U‖ ≤ C) →
      ∫ U, H U * W.conditionalExpectation ha β F U ∂ν = ∫ U, H U * F U ∂ν := by
    intro H hHm hHb
    have hHo : IsBoundedObservable H := ⟨hHm.mono hle le_rfl, hHb⟩
    have hFH : IsBoundedObservable (F * H) := by
      obtain ⟨C, hC⟩ := hF.2
      obtain ⟨D, hD⟩ := hHb
      refine ⟨hF.1.mul hHo.1, C * D, fun U => ?_⟩
      rw [Pi.mul_apply, norm_mul]
      exact mul_le_mul (hC U) (hD U) (norm_nonneg _) ((norm_nonneg _).trans (hC U))
    have e := integral_conditionalExpectation hspec hloc hν W hFH
    rw [h8 F H hF hHo hHm] at e
    simpa [mul_comm] using e
  refine ⟨key, ?_, integral_conditionalExpectation hspec hloc hν W hF⟩
  have hγ := (h7 F hF).1
  refine ae_eq_condExp_of_forall_setIntegral_eq hle (integrable_of_isBoundedObservable ν hF)
    (fun s _ _ => (integrable_of_isBoundedObservable ν hγ).integrableOn) (fun s hs' _ => ?_)
    ((h7 F hF).2.1.stronglyMeasurable.aestronglyMeasurable)
  have hsm : MeasurableSet s := hle s hs'
  have hind : Measurable[W.exteriorSigma] (s.indicator (1 : GaugeField a → ℂ)) :=
    Measurable.indicator (@measurable_const _ _ _ W.exteriorSigma _) hs'
  have e := key (s.indicator 1) hind
    ⟨1, fun U => by
      by_cases h : U ∈ s <;> simp [h]⟩
  have conv : ∀ G : GaugeField a → ℂ, ∫ U in s, G U ∂ν =
      ∫ U, s.indicator 1 U * G U ∂ν := by
    intro G
    rw [← integral_indicator hsm]
    refine integral_congr_ae (ae_of_all _ fun U => ?_)
    by_cases h : U ∈ s <;> simp [h]
  rw [conv, conv, e]
section Convexity
variable {ν₁ ν₂ : Measure (GaugeField a)}
theorem isProbabilityMeasure_convexCombination [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    {s t : ℝ≥0} (hst : s + t = 1) : IsProbabilityMeasure (s • ν₁ + t • ν₂) := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodicGibbsFoldAndCompactness.isProbabilityMeasure_convexComb <;> assumption
theorem integral_convexCombination [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] (s t : ℝ≥0)
    {G : GaugeField a → ℂ} (hG : IsBoundedObservable G) :
    ∫ U, G U ∂(s • ν₁ + t • ν₂) = s • ∫ U, G U ∂ν₁ + t • ∫ U, G U ∂ν₂ := by
  rw [integral_add_measure (integrable_of_isBoundedObservable _ hG)
      (integrable_of_isBoundedObservable _ hG),
    integral_smul_nnreal_measure, integral_smul_nnreal_measure]
end Convexity
theorem convex_gibbsClass {ha : 0 < a} {β : ℝ} (hspec : SpecificationProperties ha β) :
    Convex ℝ≥0 (gibbsClass ha β) := by
  intro ν₁ h₁ ν₂ h₂ s t _ _ hst
  have := h₁.1
  have := h₂.1
  refine ⟨isProbabilityMeasure_convexCombination hst, fun W F hF => ?_⟩
  obtain ⟨-, -, -, -, -, -, h7, -, -, -, -⟩ := hspec W
  rw [integral_convexCombination s t (h7 F hF.1).1, integral_convexCombination s t hF.1,
    h₁.2 W F hF, h₂.2 W F hF]
theorem convex_subgroupInvariantGibbsClass {ha : 0 < a} {β : ℝ}
    (hspec : SpecificationProperties ha β)
    (hS : FieldSpace.SymmetryProperties) (Q : AddSubgroup (LatticePoint a)) :
    Convex ℝ≥0 (subgroupInvariantGibbsClass ha β Q) := by
  intro ν₁ h₁ ν₂ h₂ s t hs₀ ht₀ hst
  have := h₁.1.1
  have := h₂.1.1
  refine ⟨convex_gibbsClass hspec h₁.1 h₂.1 hs₀ ht₀ hst, fun v hv A hA => ?_⟩
  have hrA : IsBoundedObservable ((shift v).actOn A) :=
    ((hS a ha).2.1 (shift v) (shift v)).2.2.1 A A hA hA |>.1
  rw [integral_convexCombination s t hrA, integral_convexCombination s t hA, h₁.2 v hv A hA,
    h₂.2 v hv A hA]
section Compactness
variable [CompactSpace (GaugeField a)] [T2Space (GaugeField a)]
omit [T2Space (GaugeField a)] in
theorem continuous_integral_probabilityMeasure {F : GaugeField a → ℂ} (hF : Continuous F) :
    Continuous fun ν : ProbabilityMeasure (GaugeField a) =>
      ∫ U, F U ∂(ν : Measure (GaugeField a)) :=
  continuous_iff_continuousAt.mpr fun _ =>
    (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp tendsto_id
      (BoundedContinuousFunction.mkOfCompact ⟨F, hF⟩)
theorem isCompact_weak_of_isClosed {𝒮 : Set (ProbabilityMeasure (GaugeField a))}
    (hc : IsClosed 𝒮) : @IsCompact _ (probabilityMeasuresWeakTopology a) 𝒮 := by
  have hid : @Continuous _ _ inferInstance (probabilityMeasuresWeakTopology a)
      (id : ProbabilityMeasure (GaugeField a) → _) :=
    continuous_iInf_rng.mpr fun F =>
      continuous_induced_rng.mpr (continuous_integral_probabilityMeasure F.continuous)
  have h := @IsCompact.image _ _ _ (probabilityMeasuresWeakTopology a) _ _ hc.isCompact hid
  simpa using h
omit [T2Space (GaugeField a)] in
theorem isClosed_gibbsClass {ha : 0 < a} {β : ℝ} (hspec : SpecificationProperties ha β) :
    IsClosed {ν : ProbabilityMeasure (GaugeField a) |
      (ν : Measure (GaugeField a)) ∈ gibbsClass ha β} := by
  have e : {ν : ProbabilityMeasure (GaugeField a) |
      (ν : Measure (GaugeField a)) ∈ gibbsClass ha β} =
      ⋂ (W : LinkWindow a), ⋂ F ∈ continuousLocalFunctions a,
        {ν : ProbabilityMeasure (GaugeField a) |
          ∫ U, W.conditionalExpectation ha β F U ∂(ν : Measure (GaugeField a)) =
            ∫ U, F U ∂(ν : Measure (GaugeField a))} := by
    ext ν
    simp only [mem_ofPred_eq, mem_iInter, gibbsClass]
    exact ⟨fun h => h.2, fun h => ⟨inferInstance, h⟩⟩
  rw [e]
  refine isClosed_iInter fun W => isClosed_biInter fun F hF => ?_
  obtain ⟨-, -, -, -, -, -, -, -, -, h10, -⟩ := hspec W
  exact isClosed_eq (continuous_integral_probabilityMeasure (h10 F hF).2.2)
    (continuous_integral_probabilityMeasure hF.2.2)
omit [T2Space (GaugeField a)] in
theorem isClosed_subgroupInvariantGibbsClass {ha : 0 < a} {β : ℝ}
    (hspec : SpecificationProperties ha β) (hsym : LatticeSymmetryProperties a)
    (Q : AddSubgroup (LatticePoint a)) :
    IsClosed {ν : ProbabilityMeasure (GaugeField a) |
      (ν : Measure (GaugeField a)) ∈ subgroupInvariantGibbsClass ha β Q} := by
  have e : {ν : ProbabilityMeasure (GaugeField a) |
      (ν : Measure (GaugeField a)) ∈ subgroupInvariantGibbsClass ha β Q} =
      {ν : ProbabilityMeasure (GaugeField a) |
        (ν : Measure (GaugeField a)) ∈ gibbsClass ha β} ∩
      ⋂ v ∈ Q, ⋂ F ∈ continuousLocalFunctions a,
        {ν : ProbabilityMeasure (GaugeField a) |
          ∫ U, (shift v).actOn F U ∂(ν : Measure (GaugeField a)) =
            ∫ U, F U ∂(ν : Measure (GaugeField a))} := by
    ext ν
    have hinv := fun v : LatticePoint a =>
      ((hsym (shift v) (shift v)).2.2.2.2.2.2 (ν : Measure (GaugeField a))
        inferInstance).2.2
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, subgroupInvariantGibbsClass]
    refine and_congr_right fun _ => ⟨fun h v hv F hF => ?_, fun h v hv => ?_⟩
    · exact (hinv v).mp (h v hv) F hF
    · exact (hinv v).mpr fun F hF => h v hv F hF
  rw [e]
  refine (isClosed_gibbsClass hspec).inter
    (isClosed_biInter fun v _ => isClosed_biInter fun F hF => ?_)
  have hr : (shift v).actOn F ∈
      (shift v).actOn '' continuousLocalFunctions a := ⟨F, hF, rfl⟩
  rw [(hsym (shift v) (shift v)).2.2.2.2.1] at hr
  exact isClosed_eq (continuous_integral_probabilityMeasure hr.2.2)
    (continuous_integral_probabilityMeasure hF.2.2)
end Compactness
theorem gaugeField_ext {U U' : GaugeField a}
    (h : ∀ b : Link a, b.IsPositivelyOriented → U b = U' b) : U = U' := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodicGibbsInvariance.gaugeField_ext <;> assumption
theorem glue_apply_of_mem (W : LinkWindow a) (ha : 0 < a) (V : W.Assignments) (U : GaugeField a)
    {b : Link a} (hb : b ∈ W.links) : W.glue ha V U b = V ⟨b, hb⟩ :=
  dif_pos hb
theorem glue_apply_of_not_mem (W : LinkWindow a) (ha : 0 < a) (V : W.Assignments)
    (U : GaugeField a) {b : Link a} (hp : b.IsPositivelyOriented) (hb : b ∉ W.links) :
    W.glue ha V U b = U b := by
  classical
  have h' : b.opposite ∉ W.links := fun h' =>
    Link.opposite_not_isPositivelyOriented ha hp (W.isPositive _ h')
  change (if h : b ∈ W.links then V ⟨b, h⟩ else
    if h' : b.opposite ∈ W.links then (V ⟨b.opposite, h'⟩)⁻¹ else U b) = U b
  rw [dif_neg hb, dif_neg h']
theorem continuous_gaugeField_apply (b : Link a) : Continuous fun U : GaugeField a => U b := by apply _root_.YangMills.Construction.ReflectionPositivity.RepresentativeCovariance.continuous_eval_link <;> assumption
theorem continuous_gaugeField_of_apply {X : Type*} [TopologicalSpace X] {f : X → GaugeField a}
    (h : ∀ b, Continuous fun x => f x b) : Continuous f := by apply _root_.YangMills.Construction.InfiniteLattice.FieldSpace.continuous_of_forall_link <;> assumption
theorem forwardFrom_isPositivelyOriented (x : LatticePoint a) (μ : Fin 4) :
    (Link.forwardFrom x μ).IsPositivelyOriented :=
  ⟨μ, by simp [Link.forwardFrom]⟩
open Classical in
def supportWindow (h : GaugeTransform a) : LinkWindow a where
  links := (h.finite_ne_one.toFinset ×ˢ (Finset.univ : Finset (Fin 4))).image
      (fun q => Link.forwardFrom q.1 q.2) ∪
    (h.finite_ne_one.toFinset ×ˢ (Finset.univ : Finset (Fin 4))).image
      (fun q => Link.forwardFrom (q.1 - axisStep a q.2) q.2)
  isPositive b hb := by
    rcases Finset.mem_union.mp hb with hb | hb <;>
    · obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hb
      exact forwardFrom_isPositivelyOriented _ _
theorem toFun_eq_one_of_not_mem_supportWindow (h : GaugeTransform a) {b : Link a}
    (hp : b.IsPositivelyOriented) (hb : b ∉ (supportWindow h).links) :
    h.toFun b.initial = 1 ∧ h.toFun b.terminal = 1 := by
  classical
  obtain ⟨μ, e⟩ := hp
  constructor
  · by_contra hne
    refine hb (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(b.initial, μ), ?_, ?_⟩))
    · simpa using hne
    · exact Link.ext rfl (by change b.initial + axisStep a μ = b.terminal; rw [← e]; abel)
  · by_contra hne
    refine hb (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(b.terminal, μ), ?_, ?_⟩))
    · simpa using hne
    · refine Link.ext (by change b.terminal - axisStep a μ = b.initial; rw [← e]; abel) ?_
      change b.terminal - axisStep a μ + axisStep a μ = b.terminal
      abel
section Gauge
variable {ha : 0 < a} {β : ℝ}
theorem localWeight_act (hgauge : GaugeTransformProperties a) (W : LinkWindow a)
    (h : GaugeTransform a) (X : GaugeField a) :
    W.localWeight β (h.act X) = W.localWeight β X := by
  have e : ∀ p : ElementaryPlaquette a, faceEnergy (h.act X) p = faceEnergy X p := fun p =>
    congrFun ((hgauge h h).2.2.1 p) X
  simp only [LinkWindow.localWeight, e]
theorem act_glue (W : LinkWindow a) (ha : 0 < a) (h : GaugeTransform a)
    (hW : ∀ b : Link a, b.IsPositivelyOriented → b ∉ W.links →
      h.toFun b.initial = 1 ∧ h.toFun b.terminal = 1)
    (V : W.Assignments) (U : GaugeField a) :
    h.act (W.glue ha V U) = W.glue ha
      ((fun b : W.links => h.toFun b.1.initial) * V *
        fun b : W.links => (h.toFun b.1.terminal)⁻¹) U := by
  refine gaugeField_ext fun b hb => ?_
  change h.toFun b.initial * W.glue ha V U b * (h.toFun b.terminal)⁻¹ = _
  by_cases hbW : b ∈ W.links
  · rw [glue_apply_of_mem _ _ _ _ hbW, glue_apply_of_mem _ _ _ _ hbW]
    rfl
  · obtain ⟨h₁, h₂⟩ := hW b hb hbW
    rw [glue_apply_of_not_mem _ _ _ _ hb hbW, glue_apply_of_not_mem _ _ _ _ hb hbW, h₁, h₂]
    simp
theorem integral_mul_mul_haarPi (hH : Matrices.ComplexMatrix2.FiniteProductGroupStatement)
    (S : Type) [Finite S]
    (f : (S → Matrices.ComplexMatrix2.specialUnitary) → ℂ)
    (l r : S → Matrices.ComplexMatrix2.specialUnitary) :
    ∫ V, f (l * V * r) ∂Matrices.ComplexMatrix2.haarPi S =
      ∫ V, f V ∂Matrices.ComplexMatrix2.haarPi S := by
  obtain ⟨-, -, -, hl, hr⟩ := hH.2.1 S
  exact (integral_mul_left_eq_self (μ := Matrices.ComplexMatrix2.haarPi S)
    (fun V => f (V * r)) l).trans
    (integral_mul_right_eq_self (μ := Matrices.ComplexMatrix2.haarPi S) f r)
theorem conditionalExpectation_pullback (hH : Matrices.ComplexMatrix2.FiniteProductGroupStatement)
    (hgauge : GaugeTransformProperties a) (W : LinkWindow a) (h : GaugeTransform a)
    (hW : ∀ b : Link a, b.IsPositivelyOriented → b ∉ W.links →
      h.toFun b.initial = 1 ∧ h.toFun b.terminal = 1)
    (F : GaugeField a → ℂ) :
    W.conditionalExpectation ha β (h.pullback F) = W.conditionalExpectation ha β F := by
  funext U
  unfold LinkWindow.conditionalExpectation
  congr 1
  have e := integral_mul_mul_haarPi hH W.links
    (fun V => F (W.glue ha V U) * (W.localWeight β (W.glue ha V U) : ℂ))
    (fun b : W.links => h.toFun b.1.initial) (fun b : W.links => (h.toFun b.1.terminal)⁻¹)
  refine Eq.trans ?_ e
  refine integral_congr_ae (ae_of_all _ fun V => ?_)
  have e₁ := act_glue W ha h hW V U
  change F (h.act (W.glue ha V U)) * _ = _
  rw [← localWeight_act hgauge W h (W.glue ha V U), e₁]
theorem integral_pullback (hH : Matrices.ComplexMatrix2.FiniteProductGroupStatement)
    (hspec : SpecificationProperties ha β) (hloc : LocalFunctionProperties a)
    (hgauge : GaugeTransformProperties a) {ν : Measure (GaugeField a)}
    (hν : ν ∈ gibbsClass ha β) {F : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (h : GaugeTransform a) : ∫ U, h.pullback F U ∂ν = ∫ U, F U ∂ν := by
  have hW := fun (b : Link a) (hb : b.IsPositivelyOriented)
      (hb' : b ∉ (supportWindow h).links) =>
    toFun_eq_one_of_not_mem_supportWindow h hb hb'
  have hobs := ((hgauge h h).2.2.2.2.2 F hF).1
  rw [← integral_conditionalExpectation hspec hloc hν (supportWindow h) hobs,
    conditionalExpectation_pullback hH hgauge _ h hW,
    integral_conditionalExpectation hspec hloc hν _ hF]
end Gauge
section Average
variable (Y : Finset (LatticePoint a))
theorem toFun_ofFinsetValues (g : Y → Matrices.ComplexMatrix2.specialUnitary) {x : LatticePoint a}
    (hx : x ∈ Y) : (GaugeTransform.ofFinsetValues Y g).toFun x = g ⟨x, hx⟩ :=
  dif_pos hx
theorem continuous_toFun_ofFinsetValues (x : LatticePoint a) :
    Continuous fun g : Y → Matrices.ComplexMatrix2.specialUnitary =>
      (GaugeTransform.ofFinsetValues Y g).toFun x := by
  by_cases hx : x ∈ Y
  · have e : (fun g : Y → Matrices.ComplexMatrix2.specialUnitary =>
        (GaugeTransform.ofFinsetValues Y g).toFun x) =
        fun g => g ⟨x, hx⟩ := funext fun g => toFun_ofFinsetValues Y g hx
    rw [e]
    exact continuous_apply _
  · have e : (fun g : Y → Matrices.ComplexMatrix2.specialUnitary =>
        (GaugeTransform.ofFinsetValues Y g).toFun x) =
        fun _ => 1 := funext fun g => dif_neg hx
    rw [e]
    exact continuous_const
theorem continuous_ofFinsetValues_act :
    Continuous fun q : (Y → Matrices.ComplexMatrix2.specialUnitary) × GaugeField a =>
      (GaugeTransform.ofFinsetValues Y q.1).act q.2 := by
  refine continuous_gaugeField_of_apply fun b => ?_
  change Continuous fun q : (Y → Matrices.ComplexMatrix2.specialUnitary) × GaugeField a =>
    (GaugeTransform.ofFinsetValues Y q.1).toFun b.initial * q.2 b *
      ((GaugeTransform.ofFinsetValues Y q.1).toFun b.terminal)⁻¹
  exact (((continuous_toFun_ofFinsetValues Y b.initial).comp continuous_fst).mul
    ((continuous_gaugeField_apply b).comp continuous_snd)).mul
      (((continuous_toFun_ofFinsetValues Y b.terminal).comp continuous_fst).inv)
theorem continuous_gaugeAverage_integrand {F : GaugeField a → ℂ} (hF : Continuous F) :
    Continuous fun q : GaugeField a × (Y → Matrices.ComplexMatrix2.specialUnitary) =>
      F ((GaugeTransform.ofFinsetValues Y q.2).act q.1) := by
  have h₁ : Continuous fun q : GaugeField a × (Y → Matrices.ComplexMatrix2.specialUnitary) =>
      (q.2, q.1) :=
    continuous_snd.prodMk continuous_fst
  have h₂ := (continuous_ofFinsetValues_act Y).comp h₁
  exact hF.comp h₂
end Average
section AverageFacts
variable {ha : 0 < a} {β : ℝ}
instance specialUnitary_secondCountable :
    SecondCountableTopology Matrices.ComplexMatrix2.specialUnitary :=
  have : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  TopologicalSpace.Subtype.secondCountableTopology _
theorem integral_gaugeAverage (hH : Matrices.ComplexMatrix2.FiniteProductGroupStatement)
    (hspec : SpecificationProperties ha β) (hloc : LocalFunctionProperties a)
    (hgauge : GaugeTransformProperties a)
    [SecondCountableTopology (GaugeField a)] (Y : Finset (LatticePoint a))
    {F : GaugeField a → ℂ} (hF : F ∈ continuousLocalFunctions a)
    {ν : Measure (GaugeField a)} (hν : ν ∈ gibbsClass ha β) :
    ∫ U, gaugeAverage Y F U ∂ν = ∫ U, F U ∂ν := by
  have := hν.1
  obtain ⟨-, -, hprob, -, -⟩ := hH.2.1 Y
  obtain ⟨C, hC⟩ := hF.1.2
  have hcont := continuous_gaugeAverage_integrand Y hF.2.2
  have hint : Integrable (Function.uncurry fun (U : GaugeField a)
      (g : Y → Matrices.ComplexMatrix2.specialUnitary) =>
      F ((GaugeTransform.ofFinsetValues Y g).act U))
      (ν.prod (Matrices.ComplexMatrix2.haarPi Y)) :=
    Integrable.of_bound hcont.aestronglyMeasurable C (ae_of_all _ fun q => hC _)
  unfold gaugeAverage
  rw [integral_integral_swap hint]
  have e : ∀ g : Y → Matrices.ComplexMatrix2.specialUnitary,
      ∫ U, F ((GaugeTransform.ofFinsetValues Y g).act U) ∂ν = ∫ U, F U ∂ν := fun g =>
    integral_pullback hH hspec hloc hgauge hν hF.1 _
  simp only [e, integral_const, probReal_univ, one_smul]
theorem gaugeAverage_properties (hH : Matrices.ComplexMatrix2.FiniteProductGroupStatement)
    (hloc : LocalFunctionProperties a) (hgauge : GaugeTransformProperties a)
    (hmeas : MeasurableIffDependsOnly a)
    (hfin : FiniteHaarIntegralsBounded a)
    {F : GaugeField a → ℂ} (hF : F ∈ continuousLocalFunctions a)
    (Y : Finset (LatticePoint a)) (hY : (Y : Set (LatticePoint a)) = supportEndpoints F) :
    gaugeAverage Y F ∈ continuousLocalFunctions a ∧
    IsGaugeInvariantFunction (gaugeAverage Y F) ∧
    observableSupport (gaugeAverage Y F) ⊆ observableSupport F ∧
    observableSupNorm (gaugeAverage Y F) ≤ observableSupNorm F := by
  obtain ⟨hdep, hset, hsfin, -⟩ := hloc.2.2.2.2.2.2.2 F hF.1 hF.2.1
  obtain ⟨C, hC⟩ := hF.1.2
  let P := (Y → Matrices.ComplexMatrix2.specialUnitary) × GaugeField a
  let Φ : P → ℂ := fun q => F ((GaugeTransform.ofFinsetValues Y q.1).act q.2)
  have hΦc : Continuous Φ := hF.2.2.comp (continuous_ofFinsetValues_act Y)
  have hΦm : Measurable[borel P] Φ := by
    let _ : MeasurableSpace P := borel P
    have : BorelSpace P := ⟨rfl⟩
    exact hΦc.measurable
  obtain ⟨hobs, hnorm, hcont⟩ := hfin Y Φ hΦm ⟨C, fun q => hC _⟩
  have hav : gaugeAverage Y F = fun U => ∫ g, Φ (g, U) ∂Matrices.ComplexMatrix2.haarPi Y := rfl
  rw [← hav] at hobs hnorm hcont
  have hdepAv : DependsOnlyOn (observableSupport F) (gaugeAverage Y F) := by
    intro U U' hUU
    unfold gaugeAverage
    refine integral_congr_ae (ae_of_all _ fun g => ?_)
    refine hdep _ _ fun b hb => ?_
    change _ * U b * _ = _ * U' b * _
    rw [hUU b hb]
  have hlocal : IsLocalObservable (gaugeAverage Y F) :=
    (hmeas.2.2.2 _ hobs).mpr ⟨_, hset, hsfin, hdepAv⟩
  have hbdd : BddAbove (range fun U => ‖F U‖) := ⟨C, by rintro _ ⟨U, rfl⟩; exact hC U⟩
  have hne : Nonempty P := ⟨(fun _ => 1, ⟨fun _ => 1, fun _ => by simp⟩)⟩
  refine ⟨⟨hobs, hlocal, hcont hΦc⟩, fun h' => ?_,
    ((hloc.2.2.2.2.2.2.2 _ hobs hlocal).2.2.2 _ hset hsfin hdepAv),
    hnorm.trans (ciSup_le fun q => le_ciSup hbdd _)⟩
  funext U
  let k : Y → Matrices.ComplexMatrix2.specialUnitary := fun x => h'.toFun x
  have hval : ∀ (g : Y → Matrices.ComplexMatrix2.specialUnitary) (x : LatticePoint a), x ∈ Y →
      ((GaugeTransform.ofFinsetValues Y g) * h').toFun x =
        (GaugeTransform.ofFinsetValues Y (g * k)).toFun x := by
    intro g x hx
    rw [toFun_ofFinsetValues Y _ hx]
    change (GaugeTransform.ofFinsetValues Y g).toFun x * h'.toFun x = _
    rw [toFun_ofFinsetValues Y _ hx]
    rfl
  have hmem : ∀ b ∈ observableSupport F, b.initial ∈ Y ∧ b.terminal ∈ Y := fun b hb => by
    have h₁ : b.initial ∈ (Y : Set (LatticePoint a)) := hY ▸ ⟨b, hb, Or.inl rfl⟩
    have h₂ : b.terminal ∈ (Y : Set (LatticePoint a)) := hY ▸ ⟨b, hb, Or.inr rfl⟩
    exact ⟨h₁, h₂⟩
  have e : ∀ g : Y → Matrices.ComplexMatrix2.specialUnitary,
      F ((GaugeTransform.ofFinsetValues Y g).act (h'.act U)) =
      F ((GaugeTransform.ofFinsetValues Y (g * k)).act U) := by
    intro g
    rw [← ((hgauge (GaugeTransform.ofFinsetValues Y g) h').2.2.2.1 U)]
    refine hdep _ _ fun b hb => ?_
    change ((GaugeTransform.ofFinsetValues Y g) * h').toFun b.initial * U b *
      (((GaugeTransform.ofFinsetValues Y g) * h').toFun b.terminal)⁻¹ =
      (GaugeTransform.ofFinsetValues Y (g * k)).toFun b.initial * U b *
      ((GaugeTransform.ofFinsetValues Y (g * k)).toFun b.terminal)⁻¹
    rw [hval g _ (hmem b hb).1, hval g _ (hmem b hb).2]
  change gaugeAverage Y F (h'.act U) = gaugeAverage Y F U
  unfold gaugeAverage
  simp only [e]
  obtain ⟨-, -, -, -, hr⟩ := hH.2.1 Y
  exact integral_mul_right_eq_self (μ := Matrices.ComplexMatrix2.haarPi Y)
    (fun g => F ((GaugeTransform.ofFinsetValues Y g).act U)) k
theorem supportEndpoints_finite (hloc : LocalFunctionProperties a)
    {F : GaugeField a → ℂ} (hF : F ∈ continuousLocalFunctions a) :
    (supportEndpoints F).Finite := by
  obtain ⟨-, -, hsfin, -⟩ := hloc.2.2.2.2.2.2.2 F hF.1 hF.2.1
  refine ((hsfin.image Link.initial).union (hsfin.image Link.terminal)).subset ?_
  rintro x ⟨b, hb, rfl | rfl⟩
  · exact Or.inl ⟨b, hb, rfl⟩
  · exact Or.inr ⟨b, hb, rfl⟩
theorem gibbsClassIsGaugeInvariant (hH : Matrices.ComplexMatrix2.FiniteProductGroupStatement)
    (hspec : SpecificationProperties ha β) (hloc : LocalFunctionProperties a)
    (hgauge : GaugeTransformProperties a) (hmeas : MeasurableIffDependsOnly a)
    (hfin : FiniteHaarIntegralsBounded a)
    [SecondCountableTopology (GaugeField a)] :
    GibbsClassIsGaugeInvariant ha β := by
  have avg : ∀ F ∈ continuousLocalFunctions a, ∃ Y : Finset (LatticePoint a),
      (Y : Set (LatticePoint a)) = supportEndpoints F ∧
      gaugeAverage Y F ∈ continuousLocalFunctions a ∧
      IsGaugeInvariantFunction (gaugeAverage Y F) ∧
      observableSupport (gaugeAverage Y F) ⊆ observableSupport F ∧
      observableSupNorm (gaugeAverage Y F) ≤ observableSupNorm F ∧
      ∀ ν ∈ gibbsClass ha β, ∫ U, gaugeAverage Y F U ∂ν = ∫ U, F U ∂ν := by
    intro F hF
    have hf := supportEndpoints_finite hloc hF
    obtain ⟨h₁, h₂, h₃, h₄⟩ :=
      gaugeAverage_properties hH hloc hgauge hmeas hfin hF hf.toFinset hf.coe_toFinset
    exact ⟨hf.toFinset, hf.coe_toFinset, h₁, h₂, h₃, h₄, fun ν hν =>
      integral_gaugeAverage hH hspec hloc hgauge _ hF hν⟩
  refine ⟨fun ν hν F hF h => integral_pullback hH hspec hloc hgauge hν hF h, avg, ?_⟩
  intro ν₁ h₁ ν₂ h₂ hag
  refine hloc.2.2.2.2.2.1 ν₁ ν₂ h₁.1 h₂.1 fun F hF => ?_
  obtain ⟨Y, -, hc, hinv, -, -, hint⟩ := avg F hF
  exact (hint ν₁ h₁).symm.trans ((hag _ hc hinv).trans (hint ν₂ h₂))
end AverageFacts
section Covariance
open scoped Classical
variable (r : LatticeSymmetry a)
def linkOrientationSign (c : Link a) : ℤˣ := if c.IsPositivelyOriented then 1 else -1
theorem apply_eq_zpow_orientedRepresentative (X : GaugeField a) (c : Link a) :
    X c = X c.orientedRepresentative ^ ((linkOrientationSign c : ℤˣ) : ℤ) := by
  by_cases h : c.IsPositivelyOriented
  · simp [linkOrientationSign, Link.orientedRepresentative, h]
  · simp only [linkOrientationSign, Link.orientedRepresentative, h, if_false]
    rw [X.2 c]
    simp
theorem orientedRepresentative_endpoints_mem_iff (c : Link a) (S : Set (LatticePoint a)) :
    (c.orientedRepresentative.initial ∈ S ∧ c.orientedRepresentative.terminal ∈ S) ↔
      (c.initial ∈ S ∧ c.terminal ∈ S) := by
  by_cases h : c.IsPositivelyOriented
  · simp [Link.orientedRepresentative, h]
  · simp only [Link.orientedRepresentative, h, if_false]
    exact and_comm
theorem pointMap_injective {G : Subgroup (Equiv.Perm AmbientSpace)}
    (hG : ∀ f : AmbientSpace → AmbientSpace,
      (∃ r : LatticeSymmetry a, r.toFun = f) ↔ ∃ g ∈ G, ⇑g = f) :
    Function.Injective r.pointMap := by
  obtain ⟨g, -, hg⟩ := (hG r.toFun).mp ⟨r, rfl⟩
  intro x y e
  have e' : r.toFun x = r.toFun y := congrArg Subtype.val e
  rw [← hg] at e'
  exact Subtype.ext (g.injective e')
theorem orientedRepresentative_mem_linkSet_iff
    (hlinks : ∀ (p : ElementaryPlaquette a) (b : Link a),
      b ∈ p.linkSet ↔ b.IsPositivelyOriented ∧ b.initial ∈ p.cornerSet ∧ b.terminal ∈ p.cornerSet)
    (hcor : ∀ p : ElementaryPlaquette a, (r.plaquetteMap p).cornerSet = r.pointMap '' p.cornerSet)
    (hinj : Function.Injective r.pointMap) {c : Link a} (hc : c.IsPositivelyOriented)
    (p : ElementaryPlaquette a) :
    (r.linkMap c).orientedRepresentative ∈ (r.plaquetteMap p).linkSet ↔ c ∈ p.linkSet := by
  rw [hlinks, hlinks, hcor, orientedRepresentative_endpoints_mem_iff]
  change _ ∧ (r.pointMap c.initial ∈ _ ∧ r.pointMap c.terminal ∈ _) ↔ _
  rw [hinj.mem_set_image, hinj.mem_set_image]
  exact ⟨fun h => ⟨hc, h.2⟩,
    fun h => ⟨Link.orientedRepresentative_isPositivelyOriented _, h.2⟩⟩
theorem facesMeeting_image (W : LinkWindow a)
    (hsurj : Function.Surjective r.plaquetteMap)
    (hiff : ∀ {c : Link a}, c.IsPositivelyOriented → ∀ p : ElementaryPlaquette a,
      ((r.linkMap c).orientedRepresentative ∈ (r.plaquetteMap p).linkSet ↔ c ∈ p.linkSet)) :
    facesMeeting ((W.image r).links : Set (Link a)) =
      r.plaquetteMap '' facesMeeting (W.links : Set (Link a)) := by
  ext q
  constructor
  · rintro ⟨b', hb', hW'⟩
    obtain ⟨p, rfl⟩ := hsurj q
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hW')
    exact ⟨p, ⟨c, (hiff (W.isPositive c hc) p).mp hb', Finset.mem_coe.mpr hc⟩, rfl⟩
  · rintro ⟨p, ⟨c, hc, hcW⟩, rfl⟩
    exact ⟨_, (hiff (W.isPositive c hcW) p).mpr hc,
      Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hcW)⟩
theorem faceEnergy_plaquetteMap
    (hloop : ∀ (p : ElementaryPlaquette a) (U : GaugeField a) (b₀ b₁ b₂ b₃ : Link a),
      ({b₀.initial, b₁.initial, b₂.initial, b₃.initial} : Set (LatticePoint a)) = p.cornerSet →
      b₀.terminal = b₁.initial → b₁.terminal = b₂.initial → b₂.terminal = b₃.initial →
      b₃.terminal = b₀.initial →
      (1 / 2) * (Matrices.ComplexMatrix2.fullTrace
        ((U b₀ * U b₁ * U b₂ * U b₃ : Matrices.ComplexMatrix2.specialUnitary) :
          Matrices.ComplexMatrix2)).re =
        (1 / 2) * (Matrices.ComplexMatrix2.fullTrace
          (faceHolonomy U p : Matrices.ComplexMatrix2)).re)
    (hcor : ∀ p : ElementaryPlaquette a, (r.plaquetteMap p).cornerSet = r.pointMap '' p.cornerSet)
    (p : ElementaryPlaquette a) (U : GaugeField a) :
    faceEnergy U (r.plaquetteMap p) = faceEnergy (r.pullbackField U) p := by
  have hcomm : p.corner + axisStep a p.highAxis + axisStep a p.lowAxis =
      p.corner + axisStep a p.lowAxis + axisStep a p.highAxis := add_right_comm _ _ _
  have key := hloop (r.plaquetteMap p) U (r.linkMap (Link.forwardFrom p.corner p.lowAxis))
    (r.linkMap (Link.forwardFrom (p.corner + axisStep a p.lowAxis) p.highAxis))
    (r.linkMap (Link.forwardFrom (p.corner + axisStep a p.highAxis) p.lowAxis).opposite)
    (r.linkMap (Link.forwardFrom p.corner p.highAxis).opposite)
    (by
      rw [hcor]
      simp only [ElementaryPlaquette.cornerSet, image_insert_eq, image_singleton]
      change ({r.pointMap p.corner, r.pointMap (p.corner + axisStep a p.lowAxis),
        r.pointMap (p.corner + axisStep a p.highAxis + axisStep a p.lowAxis),
        r.pointMap (p.corner + axisStep a p.highAxis)} : Set (LatticePoint a)) = _
      rw [hcomm])
    rfl
    (by
      change r.pointMap (p.corner + axisStep a p.lowAxis + axisStep a p.highAxis) =
        r.pointMap (p.corner + axisStep a p.highAxis + axisStep a p.lowAxis)
      rw [hcomm])
    rfl rfl
  have hvar : faceHolonomy (r.pullbackField U) p =
      U (r.linkMap (Link.forwardFrom p.corner p.lowAxis)) *
        U (r.linkMap (Link.forwardFrom (p.corner + axisStep a p.lowAxis) p.highAxis)) *
        U (r.linkMap (Link.forwardFrom (p.corner + axisStep a p.highAxis) p.lowAxis).opposite) *
        U (r.linkMap (Link.forwardFrom p.corner p.highAxis).opposite) := by
    have e₃ := U.2 (r.linkMap (Link.forwardFrom (p.corner + axisStep a p.highAxis) p.lowAxis))
    have e₄ := U.2 (r.linkMap (Link.forwardFrom p.corner p.highAxis))
    change _ = _ * _ *
      U (r.linkMap (Link.forwardFrom (p.corner + axisStep a p.highAxis) p.lowAxis)).opposite *
      U (r.linkMap (Link.forwardFrom p.corner p.highAxis)).opposite
    rw [e₃, e₄]
    rfl
  unfold faceEnergy
  rw [← key, hvar]
theorem coe_image_links_eq (ha : 0 < a) (W : LinkWindow a) :
    ((W.image r).links : Set (Link a)) =
      {b | b.IsPositivelyOriented ∧
        ∃ c ∈ W.links, b = r.linkMap c ∨ b.opposite = r.linkMap c} := by
  ext b
  constructor
  · intro hb
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hb)
    refine ⟨Link.orientedRepresentative_isPositivelyOriented _, c, hc, ?_⟩
    by_cases h : (r.linkMap c).IsPositivelyOriented
    · left
      simp [Link.orientedRepresentative, h]
    · right
      simp only [Link.orientedRepresentative, h, if_false]
      exact Link.ext rfl rfl
  · rintro ⟨hp, c, hc, e | e⟩
    · have e' : (r.linkMap c).orientedRepresentative = b := by
        rw [← e]
        simp [Link.orientedRepresentative, hp]
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨c, hc, e'⟩)
    · have hn : ¬ (r.linkMap c).IsPositivelyOriented := by
        rw [← e]
        exact Link.opposite_not_isPositivelyOriented ha hp
      have e' : (r.linkMap c).orientedRepresentative = b := by
        simp only [Link.orientedRepresentative, hn, if_false]
        rw [← e]
        exact Link.ext rfl rfl
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨c, hc, e'⟩)
theorem integral_relabelInvert {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hC : ReflectionPositivity.CutoffMirrors.RelabelInvertMeasurePreserving)
    {A A' : Type} [Finite A] [Finite A']
    (τ : A' ≃ A) (ε : A' → ℤˣ) (g : (A' → Matrices.ComplexMatrix2.specialUnitary) → E) :
    ∫ x, g (ReflectionPositivity.CutoffMirrors.relabelInvert τ ε x)
        ∂Matrices.ComplexMatrix2.haarPi A =
      ∫ y, g y ∂Matrices.ComplexMatrix2.haarPi A' := by
  obtain ⟨hhom, hmap, -, -⟩ := hC A A' τ ε
  rw [← hmap]
  exact ((hhom.homeomorph _).measurableEmbedding.integral_map g).symm
variable {r}
def imageLinkEquiv
    (hinj : InjOn (fun b => (r.linkMap b).orientedRepresentative) (positiveLinks a))
    (W : LinkWindow a) : W.links ≃ (W.image r).links :=
  Equiv.ofBijective
    (fun b => ⟨(r.linkMap b.1).orientedRepresentative, Finset.mem_image_of_mem _ b.2⟩)
    ⟨fun b c e => Subtype.ext
        (hinj (W.isPositive _ b.2) (W.isPositive _ c.2) (congrArg Subtype.val e)),
      fun b' => by
        obtain ⟨c, hc, e⟩ := Finset.mem_image.mp b'.2
        exact ⟨⟨c, hc⟩, Subtype.ext e⟩⟩
def transportAssignments
    (hinj : InjOn (fun b => (r.linkMap b).orientedRepresentative) (positiveLinks a))
    (W : LinkWindow a) : (W.image r).Assignments → W.Assignments :=
  ReflectionPositivity.CutoffMirrors.relabelInvert (imageLinkEquiv hinj W)
    fun b => linkOrientationSign (r.linkMap b.1)
theorem pullbackField_glue (ha : 0 < a)
    (hinj : InjOn (fun b => (r.linkMap b).orientedRepresentative) (positiveLinks a))
    (W : LinkWindow a) (V : (W.image r).Assignments) (U : GaugeField a) :
    r.pullbackField ((W.image r).glue ha V U) =
      W.glue ha (transportAssignments hinj W V) (r.pullbackField U) := by
  refine gaugeField_ext fun b hb => ?_
  change ((W.image r).glue ha V U) (r.linkMap b) = _
  rw [apply_eq_zpow_orientedRepresentative _ (r.linkMap b)]
  by_cases hbW : b ∈ W.links
  · have hm : (r.linkMap b).orientedRepresentative ∈ (W.image r).links :=
      Finset.mem_image_of_mem _ hbW
    rw [glue_apply_of_mem _ _ _ _ hm, glue_apply_of_mem _ _ _ _ hbW]
    rfl
  · have hm : (r.linkMap b).orientedRepresentative ∉ (W.image r).links := fun h => by
      obtain ⟨c, hc, e⟩ := Finset.mem_image.mp h
      have hcb : c = b := hinj (W.isPositive c hc) hb e
      exact hbW (hcb ▸ hc)
    rw [glue_apply_of_not_mem _ _ _ _ (Link.orientedRepresentative_isPositivelyOriented _) hm,
      glue_apply_of_not_mem _ _ _ _ hb hbW]
    exact (apply_eq_zpow_orientedRepresentative U (r.linkMap b)).symm
theorem localWeight_image {β : ℝ} (W : LinkWindow a)
    (hinjP : Function.Injective r.plaquetteMap)
    (hP : facesMeeting ((W.image r).links : Set (Link a)) =
      r.plaquetteMap '' facesMeeting (W.links : Set (Link a)))
    (hact : ∀ (p : ElementaryPlaquette a) (U : GaugeField a),
      faceEnergy U (r.plaquetteMap p) = faceEnergy (r.pullbackField U) p)
    (X : GaugeField a) :
    (W.image r).localWeight β X = W.localWeight β (r.pullbackField X) := by
  unfold LinkWindow.localWeight
  rw [hP, finsum_mem_image hinjP.injOn]
  simp only [hact]
theorem conditionalExpectation_image {ha : 0 < a} {β : ℝ}
    (hC : ReflectionPositivity.CutoffMirrors.RelabelInvertMeasurePreserving)
    (hinj : InjOn (fun b => (r.linkMap b).orientedRepresentative) (positiveLinks a))
    (W : LinkWindow a)
    (hw : ∀ X : GaugeField a,
      (W.image r).localWeight β X = W.localWeight β (r.pullbackField X))
    (F : GaugeField a → ℂ) :
    (W.image r).conditionalExpectation ha β (r.actOn F) =
      r.actOn (W.conditionalExpectation ha β F) := by
  funext U
  change _ = W.conditionalExpectation ha β F (r.pullbackField U)
  unfold LinkWindow.conditionalExpectation
  have hnum : ∫ V, r.actOn F ((W.image r).glue ha V U) *
        ((W.image r).localWeight β ((W.image r).glue ha V U) : ℂ)
        ∂(W.image r).haarProd =
      ∫ V, F (W.glue ha V (r.pullbackField U)) *
        (W.localWeight β (W.glue ha V (r.pullbackField U)) : ℂ) ∂W.haarProd := by
    refine Eq.trans ?_ (integral_relabelInvert hC (imageLinkEquiv hinj W)
      (fun b => linkOrientationSign (r.linkMap b.1)) fun V =>
        F (W.glue ha V (r.pullbackField U)) *
          (W.localWeight β (W.glue ha V (r.pullbackField U)) : ℂ))
    refine integral_congr_ae (ae_of_all _ fun V => ?_)
    change F (r.pullbackField ((W.image r).glue ha V U)) * _ = _
    rw [hw, pullbackField_glue ha hinj]
    rfl
  have hden : ∫ V, (W.image r).localWeight β ((W.image r).glue ha V U)
        ∂(W.image r).haarProd =
      ∫ V, W.localWeight β (W.glue ha V (r.pullbackField U)) ∂W.haarProd := by
    refine Eq.trans ?_ (integral_relabelInvert hC (imageLinkEquiv hinj W)
      (fun b => linkOrientationSign (r.linkMap b.1)) fun V =>
        W.localWeight β (W.glue ha V (r.pullbackField U)))
    refine integral_congr_ae (ae_of_all _ fun V => ?_)
    change (W.image r).localWeight β ((W.image r).glue ha V U) =
      W.localWeight β (W.glue ha (transportAssignments hinj W V) (r.pullbackField U))
    rw [hw, pullbackField_glue ha hinj]
  rw [hnum, hden]
end Covariance
theorem kernelIsCovariant (hS : FieldSpace.SymmetryProperties)
    (hC : ReflectionPositivity.CutoffMirrors.RelabelInvertMeasurePreserving) {ha : 0 < a} {β : ℝ}
    (hpl : PlaquetteProperties a) (hspec : SpecificationProperties ha β)
    (hsym : LatticeSymmetryProperties a) (W : LinkWindow a) :
    KernelIsCovariant ha β W := by
  intro r
  obtain ⟨-, -, -, -, -, ⟨G, hG⟩, -, -, -, -, -, -, hplaq⟩ := hS a ha
  obtain ⟨hcor, hbij⟩ := hplaq r
  obtain ⟨-, hloop, hlinks, -, -, -⟩ := hpl
  have hpt := pointMap_injective r hG
  have hinj : InjOn (fun b => (r.linkMap b).orientedRepresentative) (positiveLinks a) :=
    (hsym r r).1.injOn
  have hiff := fun {c : Link a} (hc : c.IsPositivelyOriented) (p : ElementaryPlaquette a) =>
    orientedRepresentative_mem_linkSet_iff r hlinks hcor hpt hc p
  have hP := fun W₁ : LinkWindow a => facesMeeting_image r W₁ hbij.surjective hiff
  have hact := faceEnergy_plaquetteMap r hloop hcor
  have cov : ∀ (W₁ : LinkWindow a) (F : GaugeField a → ℂ),
      (W₁.image r).conditionalExpectation ha β (r.actOn F) =
        r.actOn (W₁.conditionalExpectation ha β F) := fun W₁ F =>
    conditionalExpectation_image hC hinj W₁
      (localWeight_image W₁ hbij.injective (hP W₁) hact) F
  refine ⟨coe_image_links_eq r ha W, hP W, hact, fun p => ?_, fun F _ => cov W F,
    fun ν hν => ?_⟩
  · funext U
    exact (hact p U).symm
  have hprob := hν.1
  obtain ⟨hpm, hstate, -⟩ := (hsym r r).2.2.2.2.2.2 ν hprob
  have hrC : ∀ F ∈ continuousLocalFunctions a,
      r.actOn F ∈ continuousLocalFunctions a := fun F hF => by
    have h : r.actOn F ∈ r.actOn '' continuousLocalFunctions a := ⟨F, hF, rfl⟩
    rwa [(hsym r r).2.2.2.2.1] at h
  have chain : ∀ (W₁ : LinkWindow a), ∀ F ∈ continuousLocalFunctions a,
      ∫ U, r.actOn (W₁.conditionalExpectation ha β F) U ∂ν =
          ∫ U, (W₁.image r).conditionalExpectation ha β (r.actOn F) U ∂ν ∧
        ∫ U, (W₁.image r).conditionalExpectation ha β (r.actOn F) U ∂ν =
          ∫ U, r.actOn F U ∂ν := fun W₁ F hF =>
    ⟨by rw [cov W₁ F], hν.2 _ _ (hrC F hF)⟩
  refine ⟨chain W, hstate, hpm, fun W₁ F hF => ?_⟩
  obtain ⟨-, -, -, -, -, -, h7, -, -, -, -⟩ := hspec W₁
  exact (hstate _ (h7 F hF.1).1).trans
    ((chain W₁ F hF).1.trans ((chain W₁ F hF).2.trans (hstate F hF.1).symm))
theorem gibbsClassStructure (hH : Matrices.ComplexMatrix2.FiniteProductGroupStatement)
    (hR : ReflectionPositivity.CutoffMirrors.FieldSpaceAndFaceEnergies.Statement)
    (hE : ElementaryLatticeFacts)
    (hS : FieldSpace.SymmetryProperties) : GibbsClassStructure := by
  intro a ha β hβ
  obtain ⟨-, hpl, hspec, hloc, hgauge, -, hmeas, hsym, hfin⟩ := hE a β ha hβ
  have hC : ReflectionPositivity.CutoffMirrors.RelabelInvertMeasurePreserving :=
    (hR { L := 13, isAdmissible := ⟨by decide, le_rfl⟩, K := 1, m := 1, coupling := 1,
          coupling_pos := one_pos, dir := 0 }).2.1
  obtain ⟨⟨hcomp, hmet, -⟩, -⟩ := hS a ha
  have hsc : SecondCountableTopology (GaugeField a) := by
    let _ := TopologicalSpace.metrizableSpaceMetric (GaugeField a)
    infer_instance
  exact ⟨fun W => kernelIsConditionalExpectation hS hspec hloc W,
    gibbsClassIsGaugeInvariant hH hspec hloc hgauge hmeas hfin,
    ⟨convex_gibbsClass hspec, isCompact_weak_of_isClosed (isClosed_gibbsClass hspec)⟩,
    fun Q => ⟨convex_subgroupInvariantGibbsClass hspec hS Q,
      isCompact_weak_of_isClosed (isClosed_subgroupInvariantGibbsClass hspec hsym Q)⟩,
    fun W => kernelIsCovariant hS hC hpl hspec hsym W⟩
end YangMills.Construction.InfiniteLattice.GibbsClassProof
