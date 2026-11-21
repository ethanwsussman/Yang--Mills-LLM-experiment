import YangMills.Construction.InfiniteLattice.ReflectionPositivityAndOneTranslationProof
import YangMills.Construction.InfiniteLattice.AlmostEveryConditionalStateIsAnErgodicPeriodicGibbsState
import YangMills.Construction.InfiniteLattice.ConfigurationsFunctionsAndMeasures
import YangMills.Construction.InfiniteLattice.GibbsStatesByWindowsAndPeriodGroups
import YangMills.Construction.InfiniteLattice.InvariantFunctionsDensitiesAndACriterion
import YangMills.Construction.InfiniteLattice.MeansOverBoxesConvergeToTheConditionalExpectation
import YangMills.Construction.InfiniteLattice.PeriodicGibbsStatesAtEverySpacingAndEveryCoupling
import YangMills.Construction.InfiniteLattice.PropertiesOfTheWilsonKernelOnObservables
import YangMills.Construction.InfiniteLattice.RationalPolynomialsAndTheBorelSetsOfTheStates
import YangMills.Construction.InfiniteLattice.RegularConditionalProbabilitiesGivenTheInvariantField
import YangMills.Construction.InfiniteLattice.StatesDeterminedByContinuousLocalFunctions
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped Topology ENNReal
noncomputable section
namespace YangMills.Construction.InfiniteLattice.ErgodicConditionalStates
open ShiftInvariance (IsCondExpRepresentative)
variable {a : ℝ}
theorem shiftInvariantSigma_le :
    shiftInvariantSigma a ≤ (inferInstance : MeasurableSpace (GaugeField a)) :=
  fun _ h => h.1
theorem compactSpace_gaugeField : CompactSpace (GaugeField a) := by
  have hclosed : IsClosed {U : Link a → Matrices.ComplexMatrix2.specialUnitary |
      ∀ b, U b.opposite = (U b)⁻¹} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun b => isClosed_eq (continuous_apply _) (continuous_apply b).inv
  exact isCompact_iff_compactSpace.mp hclosed.isCompact
theorem integrable_of_bounded {F : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (μ : Measure (GaugeField a)) [IsFiniteMeasure μ] : Integrable F μ := by
  obtain ⟨C, hC⟩ := hF.2
  exact Integrable.of_bound hF.1.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
theorem bounded_of_continuous {F : GaugeField a → ℂ} (hF : Continuous F) :
    IsBoundedObservable F := by
  have := compactSpace_gaugeField (a := a)
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hF.continuousOn
  exact ⟨hF.measurable, C, fun U => hC U (Set.mem_univ U)⟩
theorem bounded_add {F G : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (hG : IsBoundedObservable G) : IsBoundedObservable (F + G) := by
  obtain ⟨C, hC⟩ := hF.2
  obtain ⟨D, hD⟩ := hG.2
  exact ⟨hF.1.add hG.1, C + D, fun U => (norm_add_le _ _).trans (add_le_add (hC U) (hD U))⟩
theorem bounded_smul {F : GaugeField a → ℂ} (c : ℂ) (hF : IsBoundedObservable F) :
    IsBoundedObservable (c • F) := by
  obtain ⟨C, hC⟩ := hF.2
  refine ⟨hF.1.const_smul c, ‖c‖ * C, fun U => ?_⟩
  rw [Pi.smul_apply, norm_smul]
  exact mul_le_mul_of_nonneg_left (hC U) (norm_nonneg c)
theorem bounded_sub {F G : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (hG : IsBoundedObservable G) : IsBoundedObservable (F - G) := by
  obtain ⟨C, hC⟩ := hF.2
  obtain ⟨D, hD⟩ := hG.2
  exact ⟨hF.1.sub hG.1, C + D, fun U => (norm_sub_le _ _).trans (add_le_add (hC U) (hD U))⟩
theorem bounded_mul {F G : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (hG : IsBoundedObservable G) : IsBoundedObservable (F * G) := by
  obtain ⟨C, hC⟩ := hF.2
  obtain ⟨D, hD⟩ := hG.2
  refine ⟨hF.1.mul hG.1, C * D, fun U => ?_⟩
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_mul (hC U) (hD U) (norm_nonneg _) ((norm_nonneg _).trans (hC U))
theorem bounded_const (c : ℂ) : IsBoundedObservable (fun _ : GaugeField a => c) :=
  ⟨measurable_const, ‖c‖, fun _ => le_rfl⟩
theorem bounded_normSq {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) :
    IsBoundedObservable (fun U => ((‖F U‖ ^ 2 : ℝ) : ℂ)) := by
  obtain ⟨C, hC⟩ := hF.2
  refine ⟨Complex.measurable_ofReal.comp (hF.1.norm.pow_const 2), C ^ 2, fun U => ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hC U) 2
theorem bounded_indicator {I : Set (GaugeField a)} (hI : MeasurableSet I) :
    IsBoundedObservable (I.indicator (1 : GaugeField a → ℂ)) := by
  refine ⟨measurable_one.indicator hI, 1, fun U => ?_⟩
  by_cases h : U ∈ I <;> simp [h]
theorem norm_le_supNorm {F : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (U : GaugeField a) : ‖F U‖ ≤ observableSupNorm F := by apply _root_.YangMills.Construction.LatticeConventions.TranslationReflectionProof.norm_le_supNorm <;> assumption
theorem supNorm_nonneg (F : GaugeField a → ℂ) : 0 ≤ observableSupNorm F :=
  Real.iSup_nonneg fun _ => norm_nonneg _
theorem norm_expect_le_supNorm (ρ : GaugeFieldProbability a)
    {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) : ‖ρ.expect F‖ ≤ observableSupNorm F := by
  have := ρ.2
  have h := norm_integral_le_of_norm_le_const (μ := ρ.1) (C := observableSupNorm F)
    (Filter.Eventually.of_forall (norm_le_supNorm hF))
  simpa [GaugeFieldProbability.expect] using h
theorem expect_add (ρ : GaugeFieldProbability a) {F G : GaugeField a → ℂ}
    (hF : IsBoundedObservable F) (hG : IsBoundedObservable G) :
    ρ.expect (F + G) = ρ.expect F + ρ.expect G := by
  have := ρ.2
  exact integral_add (integrable_of_bounded hF ρ.1) (integrable_of_bounded hG ρ.1)
theorem expect_sub (ρ : GaugeFieldProbability a) {F G : GaugeField a → ℂ}
    (hF : IsBoundedObservable F) (hG : IsBoundedObservable G) :
    ρ.expect (F - G) = ρ.expect F - ρ.expect G := by
  have := ρ.2
  exact integral_sub (integrable_of_bounded hF ρ.1) (integrable_of_bounded hG ρ.1)
theorem expect_smul (ρ : GaugeFieldProbability a) (c : ℂ) (F : GaugeField a → ℂ) :
    ρ.expect (c • F) = c * ρ.expect F := by
  simp only [GaugeFieldProbability.expect, Pi.smul_apply, smul_eq_mul]
  exact integral_const_mul c _
theorem integral_indicator_one_mul (μ : Measure (GaugeField a)) {I : Set (GaugeField a)}
    (hI : MeasurableSet I) (J : GaugeField a → ℂ) :
    ∫ U, I.indicator (1 : GaugeField a → ℂ) U * J U ∂μ = ∫ U in I, J U ∂μ := by
  rw [← integral_indicator hI]
  refine integral_congr_ae (ae_of_all _ fun U => ?_)
  by_cases h : U ∈ I <;> simp [h]
theorem integrable_normSq_of_bounded {B : GaugeField a → ℂ} (hB : IsBoundedObservable B)
    (μ : Measure (GaugeField a)) [IsFiniteMeasure μ] :
    Integrable (fun U => ‖B U‖ ^ 2) μ := by
  obtain ⟨C, hC⟩ := hB.2
  refine Integrable.of_bound (hB.1.norm.pow_const 2).aestronglyMeasurable (C ^ 2)
    (Filter.Eventually.of_forall fun U => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hC U) 2
theorem sq_integral_norm_le_integral_sq (ρ : GaugeFieldProbability a) {B : GaugeField a → ℂ}
    (hB : IsBoundedObservable B) : (∫ U, ‖B U‖ ∂ρ.1) ^ 2 ≤ ∫ U, ‖B U‖ ^ 2 ∂ρ.1 := by
  have := ρ.2
  have i1 : Integrable (fun U => ‖B U‖) ρ.1 := (integrable_of_bounded hB ρ.1).norm
  have i2 := integrable_normSq_of_bounded hB ρ.1
  set m := ∫ U, ‖B U‖ ∂ρ.1 with hm
  have h0 : 0 ≤ ∫ U, (‖B U‖ - m) ^ 2 ∂ρ.1 := integral_nonneg fun U => sq_nonneg _
  have e : ∫ U, (‖B U‖ - m) ^ 2 ∂ρ.1 = (∫ U, ‖B U‖ ^ 2 ∂ρ.1) - m ^ 2 := by
    have p : ∀ U, (‖B U‖ - m) ^ 2 = ‖B U‖ ^ 2 - (2 * m) * ‖B U‖ + m ^ 2 := fun U => by ring
    simp only [p]
    have j : Integrable (fun U => ‖B U‖ ^ 2 - (2 * m) * ‖B U‖) ρ.1 := i2.sub (i1.const_mul _)
    rw [integral_add (f := fun U => ‖B U‖ ^ 2 - (2 * m) * ‖B U‖) (g := fun _ => m ^ 2) j
        (integrable_const _),
      integral_sub (f := fun U => ‖B U‖ ^ 2) (g := fun U => (2 * m) * ‖B U‖) i2 (i1.const_mul _),
      integral_const_mul, ← hm]
    simp
    ring
  linarith
structure IsBoundedContraction (T : (GaugeField a → ℂ) → GaugeField a → ℂ) : Prop where
  maps_bounded : ∀ F, IsBoundedObservable F → IsBoundedObservable (T F)
  map_add : ∀ F G, IsBoundedObservable F → IsBoundedObservable G → T (F + G) = T F + T G
  map_smul : ∀ (c : ℂ) F, IsBoundedObservable F → T (c • F) = c • T F
  supNorm_le : ∀ F, IsBoundedObservable F → observableSupNorm (T F) ≤ observableSupNorm F
theorem isBoundedContraction_shift (v : LatticePoint a) :
    IsBoundedContraction (fun F => (shift v).actOn F) where
  maps_bounded F hF := hF.actOn _
  map_add _ _ _ _ := rfl
  map_smul _ _ _ := rfl
  supNorm_le F hF := Real.iSup_le (fun _ => norm_le_supNorm hF _) (supNorm_nonneg F)
theorem isBoundedContraction_kernelOperator {ha : 0 < a} {β : ℝ} {𝓛 : Finset (Link a)}
    {h𝓛 : (𝓛 : Set (Link a)) ⊆ positiveLinkSet a}
    (h : WilsonOperator.WeightAndKernelBounds ha β h𝓛) :
    IsBoundedContraction (WilsonOperator.kernelOperator ha β h𝓛) where
  maps_bounded := h.kernel_isBoundedObservable
  map_add := h.kernel_add
  map_smul := h.kernel_smul
  supNorm_le := h.supNorm_kernel_le
abbrev toComplex (F : GaugeField a → ℝ) : GaugeField a → ℂ := fun U => (F U : ℂ)
theorem bounded_of_ratPoly (hA : RatPolyDense a)
    {F : GaugeField a → ℝ} (hF : F ∈ ratPolyObservables a) :
    IsBoundedObservable (toComplex F) :=
  bounded_of_continuous (hA.2.1 F hF).1
theorem expect_contraction_eq (hA : RatPolyDense a)
    {T : (GaugeField a → ℂ) → GaugeField a → ℂ} (hT : IsBoundedContraction T)
    (ρ : GaugeFieldProbability a)
    (h : ∀ F ∈ ratPolyObservables a,
      ρ.expect (T (toComplex F)) = ρ.expect (toComplex F))
    {F : GaugeField a → ℂ} (hF : Continuous F) : ρ.expect (T F) = ρ.expect F := by
  have hpsi : ∀ ψ ∈ complexRatPolyObservables a,
      IsBoundedObservable ψ ∧ ρ.expect (T ψ) = ρ.expect ψ := by
    rintro ψ ⟨F₁, h₁, F₂, h₂, hψ⟩
    have e : ψ = toComplex F₁ + Complex.I • toComplex F₂ := by
      funext U
      simp [hψ, toComplex]
    have o₁ := bounded_of_ratPoly hA h₁
    have o₂ := bounded_of_ratPoly hA h₂
    have o₃ := bounded_smul Complex.I o₂
    refine ⟨e ▸ bounded_add o₁ o₃, ?_⟩
    rw [e, hT.map_add _ _ o₁ o₃, hT.map_smul _ _ o₂,
      expect_add ρ (hT.maps_bounded _ o₁) (bounded_smul _ (hT.maps_bounded _ o₂)),
      expect_add ρ o₁ o₃, expect_smul, expect_smul, h F₁ h₁, h F₂ h₂]
  have hFo := bounded_of_continuous hF
  have key : ∀ ε : ℝ, 0 < ε → ‖ρ.expect (T F) - ρ.expect F‖ ≤ 0 + ε := by
    intro ε hε
    obtain ⟨ψ, hψ, hle⟩ := hA.2.2.2.2.2.2 F hF (ε / 2) (half_pos hε)
    obtain ⟨oψ, eψ⟩ := hpsi ψ hψ
    have oG := bounded_sub hFo oψ
    have e₁ : T F = T (F - ψ) + T ψ := by
      rw [← hT.map_add _ _ oG oψ, sub_add_cancel]
    have e₂ : ρ.expect F = ρ.expect (F - ψ) + ρ.expect ψ := by
      rw [← expect_add ρ oG oψ, sub_add_cancel]
    have e₃ : ρ.expect (T F) - ρ.expect F = ρ.expect (T (F - ψ)) - ρ.expect (F - ψ) := by
      rw [e₁, expect_add ρ (hT.maps_bounded _ oG) (hT.maps_bounded _ oψ), eψ, e₂]
      ring_nf
    rw [e₃]
    have b₁ := (norm_expect_le_supNorm ρ (hT.maps_bounded _ oG)).trans (hT.supNorm_le _ oG)
    have b₂ := norm_expect_le_supNorm ρ oG
    have := norm_sub_le (ρ.expect (T (F - ψ))) (ρ.expect (F - ψ))
    linarith
  have := le_of_forall_pos_le_add key
  exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
def SatisfiesRatPolyEquations (ha : 0 < a) (β : ℝ) (ρ : GaugeFieldProbability a) : Prop :=
  (∀ v : LatticePoint a, ∀ F ∈ ratPolyObservables a,
      ρ.expect ((shift v).actOn (toComplex F)) =
        ρ.expect (toComplex F)) ∧
    ∀ p : {𝓛 : Finset (Link a) // (𝓛 : Set (Link a)) ⊆ positiveLinkSet a},
      ∀ F ∈ ratPolyObservables a,
        ρ.expect (WilsonOperator.kernelOperator ha β p.2 (toComplex F)) =
          ρ.expect (toComplex F)
theorem mem_periodicGibbsStates_iff {L K : ℕ} {β : ℝ}
    (ha : 0 < PeriodicLattice.meshSize L (K : ℤ))
    (hA : RatPolyDense (PeriodicLattice.meshSize L (K : ℤ)))
    (hI : SymmetriesActOnCylinderFunctions (PeriodicLattice.meshSize L (K : ℤ)))
    (hS : periodicGibbsStates L K β =
      {ν | PeriodicStatesAllScales.IsShiftInvariantGibbs β ν})
    (hW : ∀ (𝓛 : Finset (Link (PeriodicLattice.meshSize L (K : ℤ))))
        (h𝓛 : (𝓛 : Set (Link (PeriodicLattice.meshSize L (K : ℤ)))) ⊆
          positiveLinkSet (PeriodicLattice.meshSize L (K : ℤ))),
        WilsonOperator.WeightAndKernelBounds ha β h𝓛)
    (hG : ∀ ν : GaugeFieldProbability (PeriodicLattice.meshSize L (K : ℤ)),
        WilsonOperator.GibbsPropertyEquivalences ha β ν)
    (ρ : GaugeFieldProbability (PeriodicLattice.meshSize L (K : ℤ))) :
    ρ ∈ periodicGibbsStates L K β ↔ SatisfiesRatPolyEquations ha β ρ := by
  have hT := hG ρ
  unfold WilsonOperator.GibbsPropertyEquivalences at hT
  have h01 := hT.out 0 1
  have h20 := hT.out 2 0
  rw [hS, Set.mem_ofPred_eq]
  unfold PeriodicStatesAllScales.IsShiftInvariantGibbs SatisfiesRatPolyEquations
  constructor
  · rintro ⟨hgibbs, hinv⟩
    refine ⟨fun v F hF => hinv v _ (bounded_of_ratPoly hA hF), fun p F hF => ?_⟩
    exact h01.mp hgibbs p.1 p.2 _ (bounded_of_ratPoly hA hF)
  · rintro ⟨h₁, h₂⟩
    refine ⟨h20.mp fun 𝓛 h𝓛 F hF => ?_, fun v => ?_⟩
    · exact expect_contraction_eq hA (isBoundedContraction_kernelOperator (hW 𝓛 h𝓛)) ρ
        (h₂ ⟨𝓛, h𝓛⟩) hF.1
    · exact (hI (shift v)).2.2 ρ fun F hF =>
        expect_contraction_eq hA (isBoundedContraction_shift v) ρ (h₁ v) hF.1
theorem isCondExpRepresentative_of_disintegration {ν : GaugeFieldProbability a}
    {κ : GaugeField a → GaugeFieldProbability a}
    (hκ : IsInvariantDisintegration ν.1 κ) {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) :
    IsCondExpRepresentative ν.1 F fun U => (κ U).expect F := by
  have := ν.2
  obtain ⟨hm, hae⟩ := hκ.2.2 F hF
  refine ⟨hm, ?_, fun I hI => ?_⟩
  · exact (integrable_condExp (m := shiftInvariantSigma a) (μ := ν.1) (f := F)).congr hae.symm
  · rw [integral_indicator_one_mul _ hI.1, integral_indicator_one_mul _ hI.1,
      integral_congr_ae (ae_restrict_of_ae hae), condExpShiftInvariant]
    exact setIntegral_condExp shiftInvariantSigma_le (integrable_of_bounded hF ν.1) hI
theorem ae_eq_condExp_of_isCondExpRepresentative (ν : GaugeFieldProbability a) {G J : GaugeField a → ℂ}
    (hG : Integrable G ν.1) (h : IsCondExpRepresentative ν.1 G J) :
    J =ᵐ[ν.1] condExpShiftInvariant ν.1 G := by
  have := ν.2
  refine ae_eq_condExp_of_forall_setIntegral_eq shiftInvariantSigma_le hG
    (fun s _ _ => h.2.1.integrableOn) (fun s hs _ => ?_) ?_
  · have e := h.2.2 s hs
    rwa [integral_indicator_one_mul _ hs.1, integral_indicator_one_mul _ hs.1] at e
  · exact (h.1.stronglyMeasurable).aestronglyMeasurable
theorem ae_expect_eq_of_isCondExpRepresentative {ν : GaugeFieldProbability a}
    {κ : GaugeField a → GaugeFieldProbability a}
    (hκ : IsInvariantDisintegration ν.1 κ) {F G : GaugeField a → ℂ}
    (hG : IsBoundedObservable G) (h : IsCondExpRepresentative ν.1 G fun U => (κ U).expect F) :
    ∀ᵐ U ∂ν.1, (κ U).expect G = (κ U).expect F := by
  have := ν.2
  filter_upwards [(hκ.2.2 G hG).2,
    ae_eq_condExp_of_isCondExpRepresentative ν (integrable_of_bounded hG ν.1) h] with U h₁ h₂
  rw [h₁, h₂]
theorem bounded_cornerCubeAverage {G : GaugeField a → ℂ} (hG : IsBoundedObservable G) (n : ℕ) :
    IsBoundedObservable (cornerCubeAverage n G) := by
  classical
  obtain ⟨C, hC⟩ := hG.2
  refine ⟨measurable_const.mul (Finset.measurable_sum _ fun y _ => (hG.actOn _).1),
    ‖((n : ℂ) ^ 4)⁻¹‖ * ∑ _y ∈ cornerCube a n, C, fun U => ?_⟩
  rw [cornerCubeAverage, norm_mul]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_))
    (norm_nonneg _)
  exact hC _
theorem expect_cornerCubeAverage (ha : a ≠ 0) {ρ : GaugeFieldProbability a}
    (hρ : IsShiftInvariant ρ.1) {G : GaugeField a → ℂ} (hG : IsBoundedObservable G) {n : ℕ}
    (hn : 0 < n) : ρ.expect (cornerCubeAverage n G) = ρ.expect G := by
  have := ρ.2
  simp only [GaugeFieldProbability.expect, cornerCubeAverage]
  rw [integral_const_mul,
    integral_finsetSum _ fun y _ => integrable_of_bounded (hG.actOn _) ρ.1]
  have e : ∀ y ∈ cornerCube a n, ∫ U, (shift y).actOn G U ∂ρ.1 = ∫ U, G U ∂ρ.1 :=
    fun y _ => hρ y G hG
  rw [Finset.sum_congr rfl e, Finset.sum_const, card_cornerCube ha, nsmul_eq_mul]
  have hn' : ((n : ℂ) ^ 4) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hn.ne')
  push_cast
  rw [← mul_assoc, inv_mul_cancel₀ hn', one_mul]
theorem indicator_mul_cornerCubeAverage {I : Set (GaugeField a)}
    (hI : MeasurableSet[shiftInvariantSigma a] I) (G : GaugeField a → ℂ) (n : ℕ) :
    (fun U => I.indicator (1 : GaugeField a → ℂ) U * cornerCubeAverage n G U) =
      cornerCubeAverage n (fun U => I.indicator (1 : GaugeField a → ℂ) U * G U) := by
  funext U
  simp only [cornerCubeAverage]
  rw [mul_left_comm, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  have e := congrFun (hI.2 y) U
  simp only [LatticeSymmetry.actOn] at e ⊢
  rw [e]
theorem shiftErgodic_of_averages {L K : ℕ} (hE : ShiftInvariance.FactorizationImpliesErgodic L K)
    (hA : RatPolyDense (PeriodicLattice.meshSize L (K : ℤ)))
    (ha : PeriodicLattice.meshSize L (K : ℤ) ≠ 0)
    (ρ : GaugeFieldProbability (PeriodicLattice.meshSize L (K : ℤ)))
    (hρ : IsShiftInvariant ρ.1)
    (h : ∀ F ∈ ratPolyObservables (PeriodicLattice.meshSize L (K : ℤ)), ∀ ε : ℝ, 0 < ε →
      ∃ n : ℕ, 0 < n ∧ ∫ U, ‖cornerCubeAverage n (toComplex F) U -
        ρ.expect (toComplex F)‖ ^ 2 ∂ρ.1 < ε) :
    IsShiftErgodic ρ.1 := by
  have := ρ.2
  refine hE ρ hρ fun I hI F hF => ?_
  have oF := bounded_of_ratPoly hA hF
  have oI := bounded_indicator hI.1
  have oIF := bounded_mul oI oF
  set c := ρ.expect (toComplex F) with hc
  set x := ρ.expect (fun U => I.indicator (1 : GaugeField _ → ℂ) U * toComplex F U) -
    (((ρ.1 I).toReal : ℝ) : ℂ) * c with hx
  have hI1 : ρ.expect (I.indicator (1 : GaugeField _ → ℂ)) = (((ρ.1 I).toReal : ℝ) : ℂ) := by
    have e := integral_indicator_const (μ := ρ.1) (1 : ℂ) hI.1
    exact show ∫ U, I.indicator (fun _ => (1 : ℂ)) U ∂ρ.1 = (((ρ.1 I).toReal : ℝ) : ℂ) from by
      simpa [Measure.real, Complex.real_smul] using e
  have bound : ∀ n : ℕ, 0 < n →
      ‖x‖ ^ 2 ≤ ∫ U, ‖cornerCubeAverage n (toComplex F) U - c‖ ^ 2 ∂ρ.1 := by
    intro n hn
    have oB : IsBoundedObservable fun U => cornerCubeAverage n (toComplex F) U - c :=
      bounded_sub (bounded_cornerCubeAverage oF n) (bounded_const c)
    have e₀ : ρ.expect (fun U => I.indicator (1 : GaugeField _ → ℂ) U *
        cornerCubeAverage n (toComplex F) U) =
        ρ.expect (fun U => I.indicator (1 : GaugeField _ → ℂ) U * toComplex F U) := by
      rw [indicator_mul_cornerCubeAverage hI]
      exact expect_cornerCubeAverage ha hρ oIF hn
    have e₁ : x = ρ.expect (fun U => I.indicator (1 : GaugeField _ → ℂ) U *
        (cornerCubeAverage n (toComplex F) U - c)) := by
      have s : (fun U => I.indicator (1 : GaugeField _ → ℂ) U *
          (cornerCubeAverage n (toComplex F) U - c)) =
          (fun U => I.indicator (1 : GaugeField _ → ℂ) U *
            cornerCubeAverage n (toComplex F) U) -
          c • I.indicator (1 : GaugeField _ → ℂ) := by
        funext U
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
      have o₁ : IsBoundedObservable fun U => I.indicator (1 : GaugeField _ → ℂ) U *
          cornerCubeAverage n (toComplex F) U := bounded_mul oI (bounded_cornerCubeAverage oF n)
      rw [s, expect_sub ρ o₁ (bounded_smul c oI), expect_smul, e₀, hI1, hx]
      ring
    have e₂ : ‖x‖ ≤ ∫ U, ‖cornerCubeAverage n (toComplex F) U - c‖ ∂ρ.1 := by
      rw [e₁]
      refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
        (ae_of_all _ fun U => norm_nonneg _) (integrable_of_bounded oB ρ.1).norm
        (ae_of_all _ fun U => ?_))
      by_cases hU : U ∈ I <;> simp [hU]
    exact (pow_le_pow_left₀ (norm_nonneg _) e₂ 2).trans (sq_integral_norm_le_integral_sq ρ oB)
  by_contra hne
  have hx0 : x ≠ 0 := fun h0 => hne (sub_eq_zero.mp h0)
  obtain ⟨n, hn, hlt⟩ := h F hF (‖x‖ ^ 2) (by positivity)
  exact absurd (bound n hn) (not_le.mpr hlt)
theorem meanVarianceDefect_eq_integral (ha : a ≠ 0) {ρ : GaugeFieldProbability a}
    (hρ : IsShiftInvariant ρ.1) {F : GaugeField a → ℝ}
    (hF : IsBoundedObservable (toComplex F)) {n : ℕ} (hn : 0 < n) :
    meanVarianceDefect ρ F n =
      ((∫ U, ‖cornerCubeAverage n (toComplex F) U - ρ.expect (toComplex F)‖ ^ 2 ∂ρ.1 : ℝ) :
        ℂ) := by
  have := ρ.2
  set A := cornerCubeAverage n (toComplex F) with hAdef
  set c := ρ.expect (toComplex F) with hc
  have oA : IsBoundedObservable A := bounded_cornerCubeAverage hF n
  have hcim : c.im = 0 := by
    have : c = ((∫ U, F U ∂ρ.1 : ℝ) : ℂ) := integral_complex_ofReal
    rw [this, Complex.ofReal_im]
  have hAim : ∀ U, (A U).im = 0 := by
    intro U
    have : A U = (((((n : ℝ) ^ 4)⁻¹ * ∑ y ∈ cornerCube a n,
        (shift y).actOn F U : ℝ)) : ℂ) := by
      simp [hAdef, cornerCubeAverage, LatticeSymmetry.actOn, toComplex]
    rw [this, Complex.ofReal_im]
  have pt : ∀ U, ((‖A U - c‖ ^ 2 : ℝ) : ℂ) = A U ^ 2 - (2 * c) * A U + c ^ 2 := by
    intro U
    have hz : (A U - c).im = 0 := by simp [hAim U, hcim]
    have e : A U - c = (((A U - c).re : ℝ) : ℂ) := Complex.ext rfl (by simp [hz])
    have : ((‖A U - c‖ ^ 2 : ℝ) : ℂ) = (A U - c) ^ 2 := by
      conv_rhs => rw [e]
      rw [e, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      simp
    rw [this]
    ring
  have oA2 : IsBoundedObservable fun U => A U ^ 2 := by
    have := bounded_mul oA oA
    simpa [sq, Pi.mul_def] using this
  have iA2 := integrable_of_bounded oA2 ρ.1
  have iA := integrable_of_bounded oA ρ.1
  have hmean : ∫ U, A U ∂ρ.1 = c := expect_cornerCubeAverage ha hρ hF hn
  have j : Integrable (fun U => A U ^ 2 - (2 * c) * A U) ρ.1 := iA2.sub (iA.const_mul _)
  have e₁ : ((∫ U, ‖A U - c‖ ^ 2 ∂ρ.1 : ℝ) : ℂ) = ∫ U, A U ^ 2 ∂ρ.1 - c ^ 2 := by
    rw [← integral_complex_ofReal]
    simp only [pt]
    rw [integral_add (f := fun U => A U ^ 2 - (2 * c) * A U) (g := fun _ => c ^ 2) j
        (integrable_const _),
      integral_sub (f := fun U => A U ^ 2) (g := fun U => (2 * c) * A U) iA2 (iA.const_mul _),
      integral_const_mul, hmean]
    simp
    ring
  rw [e₁]
  rfl
theorem tendsto_integral_sq_of_stateL2Norm {ν : GaugeFieldProbability a}
    {φ : ℕ → GaugeField a → ℂ} (h : Tendsto (fun n => stateL2Norm ν (φ n)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ U, ‖φ n U‖ ^ 2 ∂ν.1) atTop (𝓝 0) := by
  have h2 := h.pow 2
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h2
  refine h2.congr fun n => ?_
  rw [stateL2Norm, ← Real.sqrt_eq_rpow, Real.sq_sqrt (integral_nonneg fun U => by positivity)]
theorem ae_satisfiesRatPolyEquations {ν : GaugeFieldProbability a}
    {κ : GaugeField a → GaugeFieldProbability a}
    (hκ : IsInvariantDisintegration ν.1 κ)
    (hA : RatPolyDense a) (ha : 0 < a) {β : ℝ}
    (hτ : ∀ F : GaugeField a → ℂ, IsBoundedObservable F → ∀ J, IsCondExpRepresentative ν.1 F J →
      ∀ v : LatticePoint a, IsCondExpRepresentative ν.1 ((shift v).actOn F) J)
    (hγ : ∀ p : {𝓛 : Finset (Link a) // (𝓛 : Set (Link a)) ⊆ positiveLinkSet a},
      ∀ F : GaugeField a → ℂ, IsBoundedObservable F →
        IsBoundedObservable (WilsonOperator.kernelOperator ha β p.2 F) ∧
        ∀ I : Set (GaugeField a), MeasurableSet[shiftInvariantSigma a] I →
          ν.expect (fun U => I.indicator (1 : GaugeField a → ℂ) U *
            WilsonOperator.kernelOperator ha β p.2 F U) =
          ν.expect (fun U => I.indicator (1 : GaugeField a → ℂ) U * F U)) :
    ∀ᵐ U ∂ν.1, SatisfiesRatPolyEquations ha β (κ U) := by
  have : Countable (Link a) := WilsonOperator.countable_link
  have h₁ : ∀ᵐ U ∂ν.1, ∀ v : LatticePoint a, ∀ F ∈ ratPolyObservables a,
      (κ U).expect ((shift v).actOn (toComplex F)) =
        (κ U).expect (toComplex F) :=
    ae_all_iff.2 fun v => (ae_ball_iff hA.1).2 fun F hF => by
      have o := bounded_of_ratPoly hA hF
      exact ae_expect_eq_of_isCondExpRepresentative hκ (o.actOn _)
        (hτ _ o _ (isCondExpRepresentative_of_disintegration hκ o) v)
  have h₂ : ∀ᵐ U ∂ν.1, ∀ p : {𝓛 : Finset (Link a) // (𝓛 : Set (Link a)) ⊆
        positiveLinkSet a}, ∀ F ∈ ratPolyObservables a,
      (κ U).expect (WilsonOperator.kernelOperator ha β p.2 (toComplex F)) =
        (κ U).expect (toComplex F) :=
    ae_all_iff.2 fun p => (ae_ball_iff hA.1).2 fun F hF => by
      have o := bounded_of_ratPoly hA hF
      have w := isCondExpRepresentative_of_disintegration hκ o
      exact ae_expect_eq_of_isCondExpRepresentative hκ (hγ p _ o).1
        ⟨w.1, w.2.1, fun I hI => (w.2.2 I hI).trans ((hγ p _ o).2 I hI).symm⟩
  exact h₁.and h₂
theorem ae_averages_of_disintegration {ν : GaugeFieldProbability a}
    {κ : GaugeField a → GaugeFieldProbability a}
    (hκ : IsInvariantDisintegration ν.1 κ)
    (hM : ∀ F : GaugeField a → ℂ, IsBoundedObservable F → Tendsto
      (fun n : ℕ => stateL2Norm ν fun U => cornerCubeAverage n F U - condExpShiftInvariant ν.1 F U)
      atTop (𝓝 0))
    (hFix : DisintegrationFixesInvariantObservables ν κ)
    {G : GaugeField a → ℂ} (hG : IsBoundedObservable G) :
    ∀ᵐ U ∂ν.1, ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, 0 < n ∧
      ∫ V, ‖cornerCubeAverage n G V - (κ U).expect G‖ ^ 2 ∂(κ U).1 < ε := by
  have := ν.2
  let J : GaugeField a → ℂ := fun U => (κ U).expect G
  obtain ⟨hJm, hJae⟩ := hκ.2.2 G hG
  have oJ : IsBoundedObservable J := ⟨hJm.mono shiftInvariantSigma_le le_rfl, observableSupNorm G,
    fun U => norm_expect_le_supNorm (κ U) hG⟩
  let D : ℕ → GaugeField a → ℂ := fun n V => cornerCubeAverage n G V - J V
  have oD : ∀ n, IsBoundedObservable (D n) :=
    fun n => bounded_sub (bounded_cornerCubeAverage hG n) oJ
  let S : ℕ → GaugeField a → ℂ := fun n V => ((‖D n V‖ ^ 2 : ℝ) : ℂ)
  have oS : ∀ n, IsBoundedObservable (S n) := fun n => bounded_normSq (oD n)
  let w : ℕ → GaugeField a → ℝ := fun n U => ∫ V, ‖D n V‖ ^ 2 ∂(κ U).1
  have hw : ∀ n U, (κ U).expect (S n) = (w n U : ℂ) := fun n U => integral_complex_ofReal
  have wnn : ∀ n U, 0 ≤ w n U := fun n U => integral_nonneg fun V => by positivity
  have wre : ∀ n, w n = fun U => ((κ U).expect (S n)).re :=
    fun n => funext fun U => by rw [hw, Complex.ofReal_re]
  have wm : ∀ n, Measurable (w n) := fun n => by
    rw [wre]
    exact Complex.measurable_re.comp ((hκ.2.2 _ (oS n)).1.mono shiftInvariantSigma_le le_rfl)
  have wi : ∀ n, Integrable (w n) ν.1 := fun n => by
    rw [wre]
    exact (isCondExpRepresentative_of_disintegration hκ (oS n)).2.1.re
  have wint : ∀ n, ∫ U, w n U ∂ν.1 = ∫ V, ‖D n V‖ ^ 2 ∂ν.1 := fun n => by
    apply Complex.ofReal_injective
    rw [← integral_complex_ofReal, ← integral_complex_ofReal]
    calc ∫ U, ((w n U : ℝ) : ℂ) ∂ν.1 = ∫ U, (κ U).expect (S n) ∂ν.1 :=
          integral_congr_ae (ae_of_all _ fun U => (hw n U).symm)
      _ = ∫ U, condExpShiftInvariant ν.1 (S n) U ∂ν.1 := integral_congr_ae (hκ.2.2 _ (oS n)).2
      _ = ∫ V, S n V ∂ν.1 := integral_condExp shiftInvariantSigma_le
  have hlim : Tendsto (fun n => ∫ V, ‖D n V‖ ^ 2 ∂ν.1) atTop (𝓝 0) := by
    have h₁ : Tendsto (fun n => stateL2Norm ν (D n)) atTop (𝓝 0) := by
      refine (hM G hG).congr fun n => ?_
      unfold stateL2Norm
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [hJae] with U hU
      simp only [D, J, hU]
    exact tendsto_integral_sq_of_stateL2Norm h₁
  let f : ℕ → GaugeField a → ℝ≥0∞ := fun n U => ENNReal.ofReal (w n U)
  have fm : ∀ n, Measurable (f n) := fun n => (wm n).ennreal_ofReal
  have flim : Tendsto (fun n => ∫⁻ U, f n U ∂ν.1) atTop (𝓝 0) := by
    have e : ∀ n, ∫⁻ U, f n U ∂ν.1 = ENNReal.ofReal (∫ V, ‖D n V‖ ^ 2 ∂ν.1) := fun n => by
      rw [← wint n, ofReal_integral_eq_lintegral_ofReal (wi n) (ae_of_all _ (wnn n))]
    simp only [e]
    simpa using ENNReal.tendsto_ofReal hlim
  have fatou := lintegral_liminf_le (μ := ν.1) (u := atTop) fm
  rw [flim.liminf_eq] at fatou
  have hz : ∫⁻ U, liminf (fun n => f n U) atTop ∂ν.1 = 0 := le_antisymm fatou bot_le
  have mlim : Measurable fun U => liminf (fun n => f n U) atTop := Measurable.liminf fm
  have hae := (lintegral_eq_zero_iff mlim).1 hz
  filter_upwards [hae, hFix J oJ hJm] with U hU hU' ε hε
  have hU2 := hU'.2
  have := (κ U).2
  have hc : ∀ᵐ V ∂(κ U).1, J V = J U := by
    have o : IsBoundedObservable fun V => J V - J U := bounded_sub oJ (bounded_const _)
    have z : ∫ V, ‖J V - J U‖ ^ 2 ∂(κ U).1 = 0 := by
      have t : ((∫ V, ‖J V - J U‖ ^ 2 ∂(κ U).1 : ℝ) : ℂ) = 0 := by
        rw [← integral_complex_ofReal]
        exact hU2
      exact_mod_cast t
    have hz' := (integral_eq_zero_iff_of_nonneg (fun V => by positivity)
      (integrable_normSq_of_bounded o (κ U).1)).1 z
    filter_upwards [hz'] with V hV
    have t : ‖J V - J U‖ ^ 2 = 0 := hV
    exact sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.1 t))
  have hU0 : liminf (fun n => f n U) atTop = 0 := hU
  have freq : ∃ᶠ n in atTop, f n U < ENNReal.ofReal ε :=
    frequently_lt_of_liminf_lt (by isBoundedDefault)
      (by rw [hU0]; exact ENNReal.ofReal_pos.2 hε)
  obtain ⟨n, hlt, hn⟩ := (freq.and_eventually (eventually_gt_atTop 0)).exists
  refine ⟨n, hn, ?_⟩
  have e : ∫ V, ‖cornerCubeAverage n G V - (κ U).expect G‖ ^ 2 ∂(κ U).1 = w n U := by
    refine integral_congr_ae ?_
    filter_upwards [hc] with V hV
    simp only [D, hV]
    rfl
  rw [e]
  exact (ENNReal.ofReal_lt_ofReal_iff hε).1 hlt
theorem measurableSet_satisfiesRatPolyEquations (ha : 0 < a) (β : ℝ)
    (hA : RatPolyDense a)
    (hB : RatPolyGeneratesStateBorel a)
    (hγ : ∀ p : {𝓛 : Finset (Link a) // (𝓛 : Set (Link a)) ⊆ positiveLinkSet a},
      ∀ F : GaugeField a → ℂ, IsBoundedObservable F →
        IsBoundedObservable (WilsonOperator.kernelOperator ha β p.2 F)) :
    MeasurableSet {ρ : GaugeFieldProbability a | SatisfiesRatPolyEquations ha β ρ} := by
  have : Countable (Link a) := WilsonOperator.countable_link
  have hm : ∀ G H : GaugeField a → ℂ, IsBoundedObservable G → IsBoundedObservable H →
      MeasurableSet {ρ : GaugeFieldProbability a | ρ.expect G = ρ.expect H} :=
    fun G H oG oH => measurableSet_eq_fun (hB.2.2.2.2 G oG) (hB.2.2.2.2 H oH)
  have e : {ρ : GaugeFieldProbability a | SatisfiesRatPolyEquations ha β ρ} =
      (⋂ v : LatticePoint a, ⋂ F ∈ ratPolyObservables a,
        {ρ : GaugeFieldProbability a | ρ.expect ((shift v).actOn (toComplex F)) =
          ρ.expect (toComplex F)}) ∩
      ⋂ p : {𝓛 : Finset (Link a) // (𝓛 : Set (Link a)) ⊆ positiveLinkSet a},
        ⋂ F ∈ ratPolyObservables a,
        {ρ : GaugeFieldProbability a |
          ρ.expect (WilsonOperator.kernelOperator ha β p.2 (toComplex F)) =
          ρ.expect (toComplex F)} := by
    ext ρ
    simp only [SatisfiesRatPolyEquations, mem_inter_iff, mem_iInter, mem_ofPred_eq]
  rw [e]
  refine MeasurableSet.inter
    (MeasurableSet.iInter fun v => MeasurableSet.biInter hA.1 fun F hF => ?_)
    (MeasurableSet.iInter fun p => MeasurableSet.biInter hA.1 fun F hF => ?_)
  · have o := bounded_of_ratPoly hA hF
    exact hm _ _ (o.actOn _) o
  · have o := bounded_of_ratPoly hA hF
    exact hm _ _ (hγ p _ o) o
theorem measurableSet_tendsto_zero {X : Type*} [MeasurableSpace X] {u : ℕ → X → ℂ}
    (hu : ∀ n, Measurable (u n)) :
    MeasurableSet {x | Tendsto (fun n => u n x) atTop (𝓝 0)} := by
  have e : {x | Tendsto (fun n => u n x) atTop (𝓝 0)} =
      ⋂ k : ℕ, ⋃ N : ℕ, ⋂ n : ℕ, ⋂ _ : N ≤ n, {x | ‖u n x‖ < 1 / ((k : ℝ) + 1)} := by
    ext x
    simp only [mem_iInter, mem_iUnion, mem_ofPred_eq]
    rw [Metric.tendsto_atTop]
    constructor
    · intro h k
      obtain ⟨N, hN⟩ := h (1 / ((k : ℝ) + 1)) Nat.one_div_pos_of_nat
      exact ⟨N, fun n hn => by simpa using hN n hn⟩
    · intro h ε hε
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
      obtain ⟨N, hN⟩ := h k
      exact ⟨N, fun n hn => by simpa using (hN n hn).trans hk⟩
  rw [e]
  exact MeasurableSet.iInter fun k => MeasurableSet.iUnion fun N => MeasurableSet.iInter fun n =>
    MeasurableSet.iInter fun _ => measurableSet_lt (hu n).norm measurable_const
theorem ergodicDecomposition (hDense : RatPolyAndStateBorelSets)
    (hForms : WilsonOperatorProperties)
    (hInv : ShiftInvariance.ShiftInvarianceAndErgodicity)
    (hMeans : MeanErgodicStatement)
    (hProb : CylinderFunctionsDetermineStates.Statement)
    (hRcp : InvariantDisintegrationTheorem)
    (hSym : PeriodicStatesAllScales.AllScalesAllCouplings) : ErgodicDecompositionStatement := by
  intro L K hL hLbig hK β hβ
  have ha : 0 < PeriodicLattice.meshSize L (K : ℤ) :=
    ShiftInvariance.meshSize_pos (by omega) K
  obtain ⟨hA, -, hB, -⟩ := hDense L K hL hLbig hK
  obtain ⟨hW, -, hG⟩ := hForms L K hL hLbig hK ha β hβ
  obtain ⟨-, hI, -⟩ := hProb L K hL hLbig hK
  obtain ⟨hSa, ⟨hSb, -⟩, -⟩ := hSym L K hL hLbig hK β hβ
  obtain ⟨-, -, -, -, hC, hD, hE₁, hE₂⟩ := hInv L K hL hLbig hK
  have hmem := fun ρ => mem_periodicGibbsStates_iff ha hA hI hSb (fun 𝓛 h𝓛 => (hW 𝓛 h𝓛).1) hG ρ
  have hper : ∀ ρ ∈ periodicGibbsStates L K β, IsShiftInvariant ρ.1 :=
    fun ρ hρ v => (hSa ρ hρ).1 v
  have hM := hMeans L K hL hLbig hK
  have herg := shiftErgodic_of_averages hE₂ hA ha.ne'
  have hγobs : ∀ p : {𝓛 : Finset (Link (PeriodicLattice.meshSize L (K : ℤ))) //
      (𝓛 : Set (Link (PeriodicLattice.meshSize L (K : ℤ)))) ⊆
        positiveLinkSet (PeriodicLattice.meshSize L (K : ℤ))},
      ∀ F : GaugeField (PeriodicLattice.meshSize L (K : ℤ)) → ℂ, IsBoundedObservable F →
        IsBoundedObservable (WilsonOperator.kernelOperator ha β p.2 F) :=
    fun p F o => (hW p.1 p.2).1.kernel_isBoundedObservable F o
  have crit : ErgodicIffMeanVarianceVanishes L K β := by
    intro ρ hρ
    have hρi := hper ρ hρ
    have := ρ.2
    constructor
    · intro hergo F hF
      have o := bounded_of_ratPoly hA hF
      obtain ⟨J, hJ, -, -⟩ := ((hC ρ hρi).1 _ o).1
      have e₁ := ae_eq_condExp_of_isCondExpRepresentative ρ (integrable_of_bounded o ρ.1) hJ
      have e₂ := (hE₁ ρ hρi hergo).2 _ o J hJ
      have hlim := tendsto_integral_sq_of_stateL2Norm (hM ρ hρi _ o)
      have hlim' : Tendsto (fun n : ℕ => ∫ U, ‖cornerCubeAverage n (toComplex F) U -
          ρ.expect (toComplex F)‖ ^ 2 ∂ρ.1) atTop (𝓝 0) := by
        refine hlim.congr fun n => integral_congr_ae ?_
        filter_upwards [e₁, e₂] with U h₁ h₂
        rw [← h₁, h₂]
      have hc := (Complex.continuous_ofReal.tendsto 0).comp hlim'
      rw [Complex.ofReal_zero] at hc
      refine hc.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with n hn
      exact (meanVarianceDefect_eq_integral ha.ne' hρi o hn).symm
    · intro h
      refine herg ρ hρi fun F hF ε hε => ?_
      have o := bounded_of_ratPoly hA hF
      obtain ⟨n, hball, hn⟩ := (((h F hF).eventually (Metric.ball_mem_nhds 0 hε)).and
        (eventually_gt_atTop 0)).exists
      refine ⟨n, hn, ?_⟩
      rw [meanVarianceDefect_eq_integral ha.ne' hρi o hn, dist_zero_right, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun U => by positivity)] at hball
      exact hball
  refine ⟨?_, crit, ?_⟩
  · intro ν hν κ hκ
    have := ν.2
    have hνi := hper ν hν
    have hfix := ((hRcp ⟨L, ⟨hL, hLbig⟩, ⟨K, hK⟩, 1⟩ ν hνi).2 κ hκ).2
    have key : ∀ᵐ U ∂ν.1, κ U ∈ periodicGibbsStates L K β ∧
        IsShiftErgodic (κ U).1 := by
      have h₁ := ae_satisfiesRatPolyEquations (β := β) hκ hA ha
        (fun F o J hJ v => (((hC ν hνi).1 F o).2 J hJ).2.2 v)
        (fun p F o => ⟨hγobs p F o, fun I hI =>
          ((hD β hβ ν hν (I.indicator 1) (Measurable.indicator (f := (1 : GaugeField _ → ℂ))
              (@measurable_const _ _ _ (shiftInvariantSigma _) (1 : ℂ)) hI)
            (bounded_indicator hI.1)).1 p.1 p.2 F o)⟩)
      have h₂ : ∀ᵐ U ∂ν.1, ∀ F ∈ ratPolyObservables (PeriodicLattice.meshSize L (K : ℤ)),
          ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, 0 < n ∧ ∫ V, ‖cornerCubeAverage n (toComplex F) V -
            (κ U).expect (toComplex F)‖ ^ 2 ∂(κ U).1 < ε :=
        (ae_ball_iff hA.1).2 fun F hF =>
          ae_averages_of_disintegration hκ (hM ν hνi) hfix (bounded_of_ratPoly hA hF)
      filter_upwards [h₁, h₂] with U u₁ u₂
      have hm := (hmem _).2 u₁
      exact ⟨hm, herg _ (hper _ hm) u₂⟩
    refine ⟨toMeasurable ν.1 {U | ¬(κ U ∈ periodicGibbsStates L K β ∧
      IsShiftErgodic (κ U).1)}, measurableSet_toMeasurable _ _, ?_, fun U hU => ?_⟩
    · rw [measure_toMeasurable]
      exact ae_iff.1 key
    · by_contra hc
      exact hU (subset_toMeasurable _ _ hc)
  · have hset : {ρ : GaugeFieldProbability (PeriodicLattice.meshSize L (K : ℤ)) |
        ρ ∈ periodicGibbsStates L K β ∧ IsShiftErgodic ρ.1} =
        {ρ | SatisfiesRatPolyEquations ha β ρ} ∩
          ⋂ F ∈ ratPolyObservables (PeriodicLattice.meshSize L (K : ℤ)),
            {ρ | Tendsto (meanVarianceDefect ρ F) atTop (𝓝 0)} :=
      Set.ext fun ρ => ⟨fun h => ⟨(hmem ρ).1 h.1, mem_iInter₂.2 fun F hF => (crit ρ h.1).1 h.2 F hF⟩,
        fun h => ⟨(hmem ρ).2 h.1, (crit ρ ((hmem ρ).2 h.1)).2 fun F hF => mem_iInter₂.1 h.2 F hF⟩⟩
    unfold ErgodicPeriodicStatesMeasurable
    rw [hset]
    refine (measurableSet_satisfiesRatPolyEquations ha β hA hB hγobs).inter
      (MeasurableSet.biInter hA.1 fun F hF => ?_)
    have o := bounded_of_ratPoly hA hF
    refine measurableSet_tendsto_zero
      (u := fun n ρ => meanVarianceDefect ρ F n) fun n => ?_
    have oM := bounded_cornerCubeAverage o n
    have oM2 : IsBoundedObservable fun U => cornerCubeAverage n (fun V => (F V : ℂ)) U ^ 2 := by
      have := bounded_mul oM oM
      simpa [sq, Pi.mul_def] using this
    exact (hB.2.2.2.2 _ oM2).sub ((hB.2.2.2.2 _ o).pow_const 2)
end YangMills.Construction.InfiniteLattice.ErgodicConditionalStates
