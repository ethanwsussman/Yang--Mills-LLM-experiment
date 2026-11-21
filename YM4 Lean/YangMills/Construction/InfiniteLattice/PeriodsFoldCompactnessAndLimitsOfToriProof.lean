import YangMills.Construction.InfiniteLattice.FactsOfToriArraysAndPerturbedMeasures
import YangMills.Construction.InfiniteLattice.FoldInequality
import YangMills.Construction.InfiniteLattice.FunctionsStatesSupportsClassesMirrorsAndPeriodGroups
import YangMills.Construction.InfiniteLattice.PeriodsFoldCompactnessAndLimitsOfTori
import YangMills.Construction.InfiniteLattice.WeakLimitsOfTorusMeasures
import YangMills.Construction.TransferOperators.PeriodicGibbsStatesAreInvariantUnderLinkMirrors
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
open scoped ComplexOrder NNReal Matrix
noncomputable section
namespace YangMills.Construction.InfiniteLattice
open NormalFamilies BasicStructure GibbsAtFixedSpacing
namespace PeriodicGibbsFoldAndCompactness
variable {a : ℝ}
theorem integrable_of_isBoundedObservable {F : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (μ : Measure (GaugeField a)) [IsFiniteMeasure μ] : Integrable F μ := by
  obtain ⟨hμ, C, hC⟩ := hF
  exact Integrable.of_bound hμ.aestronglyMeasurable C (Eventually.of_forall hC)
theorem isBoundedObservable_actOn (hI : SymmetryActionFacts a) (g : LatticeSymmetry a)
    {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) : IsBoundedObservable (g.actOn F) := by
  obtain ⟨hμ, C, hC⟩ := hF
  exact ⟨hμ.comp (hI g g).1.continuous.measurable, C, fun U => hC _⟩
theorem isProbabilityMeasure_convexComb {μ μ' : Measure (GaugeField a)} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ'] {s t : ℝ≥0} (hst : s + t = 1) :
    IsProbabilityMeasure (s • μ + t • μ') := by
  constructor
  simp only [Measure.add_apply, Measure.smul_apply, measure_univ]
  simp [ENNReal.smul_def, ← ENNReal.coe_add, hst]
theorem integral_convexComb_eq {G H : GaugeField a → ℂ} (hG : IsBoundedObservable G)
    (hH : IsBoundedObservable H)
    {μ μ' : Measure (GaugeField a)} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (s t : ℝ≥0) (hμ : ∫ U, G U ∂μ = ∫ U, H U ∂μ) (hμ' : ∫ U, G U ∂μ' = ∫ U, H U ∂μ') :
    ∫ U, G U ∂(s • μ + t • μ') = ∫ U, H U ∂(s • μ + t • μ') := by
  rw [integral_add_measure (integrable_of_isBoundedObservable hG _)
      (integrable_of_isBoundedObservable hG _),
    integral_add_measure (integrable_of_isBoundedObservable hH _)
      (integrable_of_isBoundedObservable hH _),
    integral_smul_nnreal_measure, integral_smul_nnreal_measure, integral_smul_nnreal_measure,
    integral_smul_nnreal_measure, hμ, hμ']
theorem mem_gibbsClass_iff {ha : 0 < a} {β : ℝ} {μ : Measure (GaugeField a)} :
    μ ∈ gibbsClass ha β ↔ IsProbabilityMeasure μ ∧
      ∀ W : LinkWindow a, ∀ F ∈ continuousLocalFunctions a,
        ∫ U, W.conditionalExpectation ha β F U ∂μ = ∫ U, F U ∂μ :=
  Iff.rfl
theorem mem_subgroupInvariantGibbsClass_iff {ha : 0 < a} {β : ℝ} {Q : AddSubgroup (LatticePoint a)}
    {μ : Measure (GaugeField a)} :
    μ ∈ subgroupInvariantGibbsClass ha β Q ↔
      μ ∈ gibbsClass ha β ∧ ∀ v ∈ Q, IsSymmetricUnder μ (shift v) :=
  Iff.rfl
theorem convex_gibbsClass {ha : 0 < a} {β : ℝ} (hK : KernelAndClassFacts ha β) :
    Convex ℝ≥0 (gibbsClass ha β) := by
  intro μ hμ μ' hμ' s t _ _ hst
  obtain ⟨h₁, h₂⟩ := mem_gibbsClass_iff.1 hμ
  obtain ⟨h₁', h₂'⟩ := mem_gibbsClass_iff.1 hμ'
  refine mem_gibbsClass_iff.2 ⟨isProbabilityMeasure_convexComb hst, fun W F hF => ?_⟩
  exact integral_convexComb_eq (hK.1 W F hF.1).1 hF.1 s t (h₂ W F hF) (h₂' W F hF)
theorem convex_subgroupInvariantGibbsClass {ha : 0 < a} {β : ℝ}
    (hK : KernelAndClassFacts ha β) (hI : SymmetryActionFacts a)
    (Q : AddSubgroup (LatticePoint a)) : Convex ℝ≥0 (subgroupInvariantGibbsClass ha β Q) := by
  intro μ hμ μ' hμ' s t hs ht hst
  obtain ⟨h₁, h₂⟩ := mem_subgroupInvariantGibbsClass_iff.1 hμ
  obtain ⟨h₁', h₂'⟩ := mem_subgroupInvariantGibbsClass_iff.1 hμ'
  refine mem_subgroupInvariantGibbsClass_iff.2
    ⟨convex_gibbsClass hK h₁ h₁' hs ht hst, fun v hv A hA => ?_⟩
  have := (mem_gibbsClass_iff.1 h₁).1
  have := (mem_gibbsClass_iff.1 h₁').1
  exact integral_convexComb_eq (isBoundedObservable_actOn hI _ hA) hA s t (h₂ v hv A hA)
    (h₂' v hv A hA)
theorem isCompact_of_subset_of_eqLocus {X I : Type*} [TopologicalSpace X] (f g : I → X → ℂ)
    (hf : ∀ i, Continuous (f i)) (hg : ∀ i, Continuous (g i)) {K T : Set X} (hK : IsCompact K)
    (hT : T ⊆ K) (hTe : T = ⋂ i, {x | f i x = g i x}) : IsCompact T := by
  refine hK.of_isClosed_subset ?_ hT
  rw [hTe]
  exact isClosed_iInter fun i => isClosed_eq (hf i) (hg i)
theorem continuous_integral_weakTopology (F : GaugeField a → ℂ) (hF : Continuous F) :
    @Continuous _ _ (probabilityMeasuresWeakTopology a) _
      (fun μ : ProbabilityMeasure (GaugeField a) => ∫ U, F U ∂(μ : Measure (GaugeField a))) :=
  continuous_iInf_dom (i := (⟨F, hF⟩ : C(GaugeField a, ℂ))) continuous_induced_dom
theorem isWeakCompact_of_integral_equations
    (hall : IsWeakCompact {ρ : Measure (GaugeField a) | IsLatticeState ρ})
    (S : Set (Measure (GaugeField a))) (hS : IsStateFamily S)
    (E : Set ((GaugeField a → ℂ) × (GaugeField a → ℂ)))
    (hE : ∀ e ∈ E, Continuous e.1 ∧ Continuous e.2)
    (h : ∀ ρ : ProbabilityMeasure (GaugeField a), (ρ : Measure (GaugeField a)) ∈ S ↔
      ∀ e ∈ E, ∫ U, e.1 U ∂(ρ : Measure (GaugeField a)) =
        ∫ U, e.2 U ∂(ρ : Measure (GaugeField a))) :
    IsWeakCompact S := by
  refine ⟨hS, ?_⟩
  refine @isCompact_of_subset_of_eqLocus (ProbabilityMeasure (GaugeField a)) E
    (probabilityMeasuresWeakTopology a)
    (fun e ρ => ∫ U, e.1.1 U ∂(ρ : Measure (GaugeField a)))
    (fun e ρ => ∫ U, e.1.2 U ∂(ρ : Measure (GaugeField a)))
    (fun e => continuous_integral_weakTopology _ (hE e.1 e.2).1)
    (fun e => continuous_integral_weakTopology _ (hE e.1 e.2).2) _ _ hall.2 ?_ ?_
  · intro ρ hρ
    exact hS _ hρ
  · ext ρ
    simp only [asProbabilityMeasures, Set.mem_ofPred_eq, Set.mem_iInter, h, Subtype.forall]
theorem isWeakCompact_gibbsClass {ha : 0 < a} {β : ℝ}
    (hK : KernelAndClassFacts ha β)
    (hall : IsWeakCompact {ρ : Measure (GaugeField a) | IsLatticeState ρ}) :
    IsWeakCompact (gibbsClass ha β) := by
  refine isWeakCompact_of_integral_equations hall _ (fun ρ hρ => (mem_gibbsClass_iff.1 hρ).1)
    {e | ∃ (W : LinkWindow a) (F : GaugeField a → ℂ), F ∈ continuousLocalFunctions a ∧
      e = (W.conditionalExpectation ha β F, F)} ?_ ?_
  · rintro e ⟨W, F, hF, rfl⟩
    exact ⟨((hK.1 W F hF.1).2.2.2 hF).2.2, hF.2.2⟩
  · intro ρ
    constructor
    · rintro hρ e ⟨W, F, hF, rfl⟩
      exact (mem_gibbsClass_iff.1 hρ).2 W F hF
    · intro h
      exact mem_gibbsClass_iff.2 ⟨inferInstance, fun W F hF => h _ ⟨W, F, hF, rfl⟩⟩
theorem isWeakCompact_subgroupInvariantGibbsClass {ha : 0 < a} {β : ℝ}
    (hK : KernelAndClassFacts ha β) (hI : SymmetryActionFacts a)
    (hall : IsWeakCompact {ρ : Measure (GaugeField a) | IsLatticeState ρ})
    (hinv : ∀ (μ : Measure (GaugeField a)) (g : LatticeSymmetry a), IsLatticeState μ →
      (IsSymmetricUnder μ g ↔
        ∀ F ∈ continuousFns a, stateEval μ (g.actOn F) = stateEval μ F))
    (Q : AddSubgroup (LatticePoint a)) : IsWeakCompact (subgroupInvariantGibbsClass ha β Q) := by
  refine isWeakCompact_of_integral_equations hall _
    (fun ρ hρ => (mem_gibbsClass_iff.1 (mem_subgroupInvariantGibbsClass_iff.1 hρ).1).1)
    ({e | ∃ (W : LinkWindow a) (F : GaugeField a → ℂ), F ∈ continuousLocalFunctions a ∧
        e = (W.conditionalExpectation ha β F, F)} ∪
      {e | ∃ v ∈ Q, ∃ F ∈ continuousFns a, e = ((shift v).actOn F, F)}) ?_ ?_
  · rintro e (⟨W, F, hF, rfl⟩ | ⟨v, _, F, hF, rfl⟩)
    · exact ⟨((hK.1 W F hF.1).2.2.2 hF).2.2, hF.2.2⟩
    · exact ⟨(hI (shift v) (shift v)).2.2.2.1 F hF, hF⟩
  · intro ρ
    have hρs : IsLatticeState (ρ : Measure (GaugeField a)) :=
      (inferInstance : IsProbabilityMeasure (ρ : Measure (GaugeField a)))
    constructor
    · intro hρ
      obtain ⟨h₁, h₂⟩ := mem_subgroupInvariantGibbsClass_iff.1 hρ
      rintro e (⟨W, F, hF, rfl⟩ | ⟨v, hv, F, hF, rfl⟩)
      · exact (mem_gibbsClass_iff.1 h₁).2 W F hF
      · exact (hinv _ _ hρs).1 (h₂ v hv) F hF
    · intro h
      refine mem_subgroupInvariantGibbsClass_iff.2
        ⟨mem_gibbsClass_iff.2 ⟨inferInstance, fun W F hF => h _ (Or.inl ⟨W, F, hF, rfl⟩)⟩,
          fun v hv => (hinv _ _ hρs).2 fun F hF => h _ (Or.inr ⟨v, hv, F, hF, rfl⟩)⟩
theorem maxNorm_eq_pi_norm (x : AmbientSpace) : WholeSpace.maxNorm x = ‖x‖ := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun i _ => by simpa [Real.norm_eq_abs] using norm_le_pi_norm x i
  · refine (pi_norm_le_iff_of_nonneg ?_).2 fun i => ?_
    · exact (abs_nonneg (x 0)).trans (Finset.le_sup' (fun i => |x i|) (Finset.mem_univ 0))
    · exact Finset.le_sup' (fun i => |x i|) (Finset.mem_univ i)
theorem minSupPeriod_eq_minNonzeroNorm (Γ : PeriodSublattice 1) :
    Γ.minSupPeriod = Γ.minNonzeroNorm := by
  simp only [PeriodSublattice.minSupPeriod, PeriodSublattice.minNonzeroNorm, maxNorm_eq_pi_norm]
theorem closedHalfSpace_one_eq (u : AmbientSpace) (c : ℝ) :
    closedHalfSpace u c 1 = {x | c ≤ u ⬝ᵥ x} := by apply _root_.YangMills.Construction.NormalFamilies.closedHalfSpace_one <;> assumption
theorem closedHalfSpace_neg_one_eq (u : AmbientSpace) (c : ℝ) :
    closedHalfSpace u c (-1) = {x | u ⬝ᵥ x ≤ c} := by apply _root_.YangMills.Construction.NormalFamilies.closedHalfSpace_neg_one <;> assumption
theorem normalLevelPair_ext {P P' : NormalLevelPair 1} (hu : P.normal = P'.normal)
    (hc : P.level = P'.level) : P = P' := by
  cases P
  cases P'
  simp_all
theorem statement_holds
    (hLink : TransferOperators.PeriodicGibbsLinkSymmetry.Statement)
    (hFacts : BasicStructure.Statement)
    (hFold : NormalFamilies.FoldedStateBound)
    (hTori : ToriArraysAndTiltedMeasuresFacts)
    (hLimits : TorusMeasureWeakLimits) : Statement := by
  intro β hβ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨-, -, -, -, -, -, hK, -⟩ := hFacts.1 1 one_pos β hβ
    unfold SinglePeriodGroup
    rw [hK.2.2.1]
    exact (hLink β hβ).2
  · intro L A hA hreal hsupp μ hμ
    have hlies : SupportLiesIn A (L.slab 0) := by
      rw [← L.slabSet_eq_slab_zero]
      exact hsupp
    obtain ⟨μ₀, hμ₀, hall, hle⟩ := hFold β hβ L ⟨A, hA, hreal, hlies⟩ μ hμ
    refine ⟨μ₀, hμ₀, hle, ?_⟩
    rintro P ⟨hu, k, hk⟩
    obtain ⟨P', hu', hc', hinv, hpos⟩ := hall k
    obtain rfl : P = P' := normalLevelPair_ext (hu.trans hu'.symm) (hk.trans hc'.symm)
    refine ⟨fun F hF => hinv F hF, fun F hF => hpos F ?_⟩
    rcases hF with hF | hF
    · left
      rwa [halfSpaceObservables, closedHalfSpace_one_eq, hu] at hF
    · right
      rwa [halfSpaceObservables, closedHalfSpace_neg_one_eq, hu] at hF
  · intro a ha Q
    obtain ⟨-, hI, hS, -, -, -, hK, -⟩ := hFacts.1 a ha β hβ
    have hall := hS.2.2.2.2.2.1
    have hinv := hS.2.2.2.2.2.2.1
    exact ⟨⟨convex_gibbsClass hK, isWeakCompact_gibbsClass hK hall⟩,
      convex_subgroupInvariantGibbsClass hK hI Q,
      isWeakCompact_subgroupInvariantGibbsClass hK hI hall hinv Q⟩
  · refine ⟨fun Γ => ((hTori β hβ).1 1 one_pos Γ).2.2.isProbabilityMeasure_lifted,
      fun Γ hΓ μ hμ hlim => (hLimits β hβ).1 Γ ?_ μ hμ hlim⟩
    unfold PeriodsDiverge
    unfold MinNonzeroNormTendsToInfinity at hΓ
    simpa only [minSupPeriod_eq_minNonzeroNorm] using hΓ
  · intro P μ hμ hinv hpos
    exact (hLimits β hβ).2.2.1 P μ hμ hinv hpos
end PeriodicGibbsFoldAndCompactness
end YangMills.Construction.InfiniteLattice
end
