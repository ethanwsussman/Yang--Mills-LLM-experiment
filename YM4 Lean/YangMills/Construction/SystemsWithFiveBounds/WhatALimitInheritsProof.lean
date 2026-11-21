import YangMills.Construction.SystemsWithFiveBounds.CanonicalDecompositionAlongStatesProof
import YangMills.Construction.SystemsWithFiveBounds.ConditionsAtFixedConstantsProof
import YangMills.Construction.Torus.GeometryTransportLiftAndDilationOfTestPairsProof
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.SystemsWithFiveBounds.GibbsLimitInheritance
section FixedSpacing
variable {a : ℝ} {k : ℕ}
private theorem prod_orderEmbOfFin {M : Type*} [CommMonoid M] {n : ℕ} (J : Finset (Fin n))
    (g : Fin n → M) : ∏ l : Fin J.card, g (J.orderEmbOfFin rfl l) = ∏ i ∈ J, g i := by
  rw [← Finset.prod_coe_sort J g]
  exact Fintype.prod_equiv (J.orderIsoOfFin rfl).toEquiv _ _ fun l => by simp
private theorem boundedCompact_of_mem_c1 {f : InfiniteLattice.AmbientSpace → ℝ}
    (hf : f ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ))) :
    InfiniteLattice.IsBoundedBorelCompactlySupported f := by
  obtain ⟨h₁, h₂, -⟩ := hf
  exact ⟨h₁.continuous.measurable, h₂.exists_bound_of_continuous h₁.continuous, h₂⟩
private def smearedObs (f : Fin k → InfiniteLattice.AmbientSpace → ℝ) :
    Fin k → InfiniteLattice.GaugeField a → ℝ :=
  fun i U => InfiniteLattice.smearedEnergy (f i) U
private def smearedMean (ν : Measure (InfiniteLattice.GaugeField a))
    (f : InfiniteLattice.AmbientSpace → ℝ) : ℝ :=
  ∫ V, InfiniteLattice.smearedEnergy f V ∂ν
private def centredObs (ν : Measure (InfiniteLattice.GaugeField a))
    (f : Fin k → InfiniteLattice.AmbientSpace → ℝ) :
    Fin k → InfiniteLattice.GaugeField a → ℝ :=
  Cumulants.shiftTuple (smearedObs f) fun i => -smearedMean ν (f i)
private theorem smearedObs_bounded (hM : SmearedObservablesWellDefined) (ha : 0 < a)
    {f : Fin k → InfiniteLattice.AmbientSpace → ℝ}
    (hf : ∀ i, InfiniteLattice.IsBoundedBorelCompactlySupported (f i)) (i : Fin k) :
    Probability.IsBoundedRealRV (smearedObs (a := a) f i) :=
  ((hM a ha).1 (f i) (hf i)).2
private theorem centredObs_bounded (hM : SmearedObservablesWellDefined) (ha : 0 < a)
    (ν : Measure (InfiniteLattice.GaugeField a)) {f : Fin k → InfiniteLattice.AmbientSpace → ℝ}
    (hf : ∀ i, InfiniteLattice.IsBoundedBorelCompactlySupported (f i)) (i : Fin k) :
    Probability.IsBoundedRealRV (centredObs ν f i) := by
  obtain ⟨hm, C, hC⟩ := smearedObs_bounded (a := a) hM ha hf i
  refine ⟨hm.add_const _, C + |smearedMean ν (f i)|, fun U => ?_⟩
  have h₁ := abs_le.1 (hC U)
  have h₂ := abs_le.1 (le_refl |smearedMean ν (f i)|)
  change |smearedObs f i U + -smearedMean ν (f i)| ≤ _
  exact abs_le.2 ⟨by linarith [h₁.1, h₂.2], by linarith [h₁.2, h₂.1]⟩
private theorem finsetMoment_centredObs (ρ ν : Measure (InfiniteLattice.GaugeField a))
    (f : Fin k → InfiniteLattice.AmbientSpace → ℝ)
    {J : Finset (Fin k)} (hJ : J ≠ ∅) :
    Cumulants.finsetMoment ρ (centredObs ν f) J =
      ((∫ U, ∏ l, (InfiniteLattice.smearedEnergy (SchwingerFunctions.restrictTuple f J l) U -
          ∫ V, InfiniteLattice.smearedEnergy (SchwingerFunctions.restrictTuple f J l) V ∂ν) ∂ρ : ℝ) : ℂ) := by
  have e : (∫ ω, ((∏ l ∈ J, centredObs ν f l ω : ℝ) : ℂ) ∂ρ) =
      ((∫ ω, ∏ l ∈ J, centredObs ν f l ω ∂ρ : ℝ) : ℂ) :=
    integral_ofReal
  rw [Cumulants.finsetMoment, if_neg hJ, Probability.complexExpectation, e]
  refine congrArg _ (integral_congr_ae (ae_of_all _ fun U => ?_))
  change ∏ l ∈ J, centredObs ν f l U = _
  rw [← prod_orderEmbOfFin J]
  refine Finset.prod_congr rfl fun l _ => ?_
  simp [centredObs, Cumulants.shiftTuple, smearedObs, smearedMean,
    SchwingerFunctions.restrictTuple, sub_eq_add_neg]
private theorem mixedCumulant_centredObs_eq_sum (hC : Cumulants.CumulantMomentRelations)
    (hM : SmearedObservablesWellDefined) (ha : 0 < a)
    (ρ ν : Measure (InfiniteLattice.GaugeField a)) [IsProbabilityMeasure ρ]
    {f : Fin k → InfiniteLattice.AmbientSpace → ℝ}
    (hf : ∀ i, InfiniteLattice.IsBoundedBorelCompactlySupported (f i)) (hk : 1 ≤ k) :
    Cumulants.mixedCumulant ρ (centredObs ν f) =
      ∑ π : SetPartition.PartitionsFin k, (-1 : ℂ) ^ (SetPartition.blockCount π - 1) *
        ((SetPartition.blockCount π - 1).factorial : ℂ) *
          ∏ J ∈ π.parts, ((∫ U, ∏ l, (InfiniteLattice.smearedEnergy
            (SchwingerFunctions.restrictTuple f J l) U -
            ∫ V, InfiniteLattice.smearedEnergy (SchwingerFunctions.restrictTuple f J l) V ∂ν) ∂ρ : ℝ) : ℂ) := by
  rw [(hC (InfiniteLattice.GaugeField a) ρ k (centredObs ν f)
    (centredObs_bounded hM ha ν hf)).2.2.2.2.2.2 hk]
  refine Finset.sum_congr rfl fun π _ => ?_
  congr 1
  exact Finset.prod_congr rfl fun J hJ =>
    finsetMoment_centredObs ρ ν f (π.nonempty_of_mem_parts hJ).ne_empty
private theorem mixedCumulant_centredObs_eq_smeared (hC : Cumulants.CumulantMomentRelations)
    (hM : SmearedObservablesWellDefined) (ha : 0 < a)
    (ρ ν : Measure (InfiniteLattice.GaugeField a)) [IsProbabilityMeasure ρ]
    {f : Fin k → InfiniteLattice.AmbientSpace → ℝ}
    (hf : ∀ i, InfiniteLattice.IsBoundedBorelCompactlySupported (f i)) (hk : 2 ≤ k) :
    Cumulants.mixedCumulant ρ (centredObs ν f) = InfiniteLattice.smearedEnergyCumulant ρ f :=
  (hC (InfiniteLattice.GaugeField a) ρ k (smearedObs f) (smearedObs_bounded hM ha hf)).2.2.2.1 k
    (smearedObs f) _ hk (smearedObs_bounded hM ha hf)
private theorem integrable_smearedEnergy (hM : SmearedObservablesWellDefined) (ha : 0 < a)
    (ρ : Measure (InfiniteLattice.GaugeField a)) [IsProbabilityMeasure ρ]
    {f : InfiniteLattice.AmbientSpace → ℝ}
    (hf : InfiniteLattice.IsBoundedBorelCompactlySupported f) :
    Integrable (InfiniteLattice.smearedEnergy f : InfiniteLattice.GaugeField a → ℝ) ρ := by
  obtain ⟨hm, C, hC⟩ := ((hM a ha).1 f hf).2
  exact Integrable.of_bound hm.aestronglyMeasurable C (ae_of_all _ fun U => hC U)
end FixedSpacing
private theorem pair_mem_disjointSupportTuples (hP : Scales.SeparatedPairsAreTestFunctionsStatement)
    {d ϑ : ℝ} (hd : 0 < d) {f g : InfiniteLattice.AmbientSpace → ℝ}
    (hp : (f, g) ∈ TestFunctions.separatedPairsR4 d ϑ)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    ![f, g] ∈ TestSpaces.disjointSupportTuples (Set.univ : Set (Fin 4 → ℝ)) 2 := by apply _root_.YangMills.SharedProofs.p22880 <;> assumption
private theorem unitIntegralTestFunctions_nonempty : unitIntegralTestFunctions.Nonempty := by
  let b : ContDiffBump (0 : Fin 4 → ℝ) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩
  refine ⟨b.normed volume, ⟨b.contDiff_normed, b.hasCompactSupport_normed, Set.subset_univ _⟩, ?_,
    b.integral_normed⟩
  rw [b.tsupport_normed_eq]
  intro y hy
  have hy' : ‖y‖ ≤ 1 / 4 := mem_closedBall_zero_iff.1 hy
  have hμ : ∀ μ, y μ ^ 2 ≤ 1 / 16 := fun μ => by
    have := abs_le.1 ((norm_le_pi_norm y μ).trans hy')
    nlinarith [this.1, this.2]
  change Real.sqrt _ ≤ 1
  refine Real.sqrt_le_iff.2 ⟨by norm_num, ?_⟩
  simp only [Fin.sum_univ_four, sub_zero, Pi.sub_apply, Pi.zero_apply]
  nlinarith [hμ 0, hμ 1, hμ 2, hμ 3]
private theorem onePointCoefficient_bound {M : ℝ} {c₁ : ℝ → ℝ} {σ : SeparatedTuples.TupleFunctional}
    (hB : OnePointBounded M c₁ σ) {𝔠 : ℝ} (h0 : 0 ≤ c₁ 1)
    (hn : IsOnePointCoefficient σ 𝔠) :
    |𝔠| ≤ c₁ 1 * sInf (TestFunctions.sharpNormR4 M '' unitIntegralTestFunctions) := by
  have each : ∀ f ∈ unitIntegralTestFunctions, |𝔠| ≤ c₁ 1 * TestFunctions.sharpNormR4 M f := by
    rintro f ⟨hf, hs, hi⟩
    have hb := hB 1 one_pos (TestSpaces.singletonSepTuple f hf) ⟨0, hs⟩
    rw [hn] at hb
    have e : (∫ x, (TestSpaces.singletonSepTuple f hf).1 0 x) = 1 := hi
    rw [e, mul_one] at hb
    exact hb
  obtain ⟨f₀, hf₀⟩ := unitIntegralTestFunctions_nonempty
  rcases h0.eq_or_lt with hz | hp
  · have := each f₀ hf₀
    rw [← hz] at this ⊢
    simpa using this
  · rw [← div_le_iff₀' hp]
    refine le_csInf ⟨_, f₀, hf₀, rfl⟩ ?_
    rintro _ ⟨f, hf, rfl⟩
    rw [div_le_iff₀' hp]
    exact each f hf
private theorem twoPointFactor_pos : 0 < LimitTheorem.twoPointFactor := by
  unfold LimitTheorem.twoPointFactor
  have := Real.pi_pos
  positivity
private theorem uniformNorm_pos {f : (Fin 4 → ℝ) → ℝ} (hb : TestFunctions.IsBoundedFun f)
    (hz : ∃ z, f z ≠ 0) : 0 < TestFunctions.uniformNorm f := by apply _root_.YangMills.Construction.TestFunctions.PairTransport.uniformNorm_pos <;> assumption
private theorem inverseEighthKernel_pos (hG : TestPairs.GeometryAndKernelBounds) {d ϑ : ℝ}
    (hd : 0 < d) (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) {f g : (Fin 4 → ℝ) → ℝ}
    (hp : (f, g) ∈ TestFunctions.separatedPairsR4 d ϑ) :
    0 < TestFunctions.inverseEighthKernel f g := by
  have hp' := hp
  simp only [TestFunctions.separatedPairsR4, TestFunctions.separatedPairs, Set.mem_setOf_eq] at hp'
  obtain ⟨x₁, x₂, b₁, b₂, s₁, s₂⟩ := hp'
  have hcent : TestFunctions.IsCentrePairR4 d ϑ x₁ x₂ (f, g) :=
    ⟨⟨b₁.2.2.2.1, b₁.2.2.2.2.1, b₁.2.2.2.2.2⟩, ⟨b₂.2.2.2.1, b₂.2.2.2.2.1, b₂.2.2.2.2.2⟩, s₁, s₂⟩
  obtain ⟨-, -, -, hker, hchain⟩ := (hG.1 d ϑ ⟨hd, hϑ, hϑ1⟩ x₁ x₂ f g hp hcent).1
  have hG₁ : 0 < TestFunctions.uniformNorm f := uniformNorm_pos hker.1 b₁.2.2.1
  have hG₂ : 0 < TestFunctions.uniformNorm g := uniformNorm_pos hker.2.1 b₂.2.2.1
  have hKf : (10 : ℝ) ^ (-8 : ℤ) * ϑ ^ 2 * TestFunctions.uniformNorm f * TestFunctions.uniformNorm g ≤
      TestFunctions.inverseEighthKernel f g :=
    hchain.1.trans hchain.2.1
  exact lt_of_lt_of_le (by positivity) hKf
private theorem twoPointPositive_of_law (hG : TestPairs.GeometryAndKernelBounds) {ϑ : ℝ}
    {C : LimitTheorem.ConditionConstants}
    {σ : SeparatedTuples.TupleFunctional} (hϑ : ϑ ∈ Ioc (0 : ℝ) 1) (hd₀ : C.d₀ < 1)
    (hη : ∀ d ∈ Ioc (0 : ℝ) C.d₀, C.ηBar d ∈ Icc (0 : ℝ) (1 / 3))
    (hT : TwoPointLawHoldsAt ϑ C σ) :
    TwoPointPositive ϑ C σ := by
  intro d hd f g hp hf hg
  obtain ⟨X, hX, η, e, h₁, -⟩ := hT d hd f g hp hf hg
  refine ⟨X, hX, ?_⟩
  rw [e]
  have hK := inverseEighthKernel_pos hG hd.1 hϑ.1 hϑ.2 hp
  have hlog : 0 < Real.log (1 / d) :=
    Real.log_pos (by rw [one_div]; exact (one_lt_inv₀ hd.1).2 (lt_of_le_of_lt hd.2 hd₀))
  have hb := (hη d hd).2
  have hfac : 0 < 1 + η := by
    have hpos : 0 < 1 - C.ηBar d := by linarith
    exact lt_of_lt_of_le (by positivity) h₁
  exact mul_pos (div_pos (mul_pos twoPointFactor_pos hK) (pow_pos hlog 2)) hfac
section AlongCutoffs
variable {L : ℕ} {K : ℕ+ → ℕ+}
private theorem spacingAt_pos (hL : Conventions.IsAdmissibleBlockingFactor L) (K : ℕ) :
    0 < CutoffLattice.spacingAt L K := by apply _root_.YangMills.Construction.CutoffLattice.spacingAt_pos <;> assumption
private theorem centredProduct_eq (L K : ℕ) (ν : Measure (CutoffLattice.FieldsAt L K))
    {n : ℕ} (X : TestSpaces.SepTupleOfCard n) (U : CutoffLattice.FieldsAt L K) :
    InfiniteLattice.CutoffRepresentative.centredProduct L K ν ⟨n, X⟩ U =
      ∏ l, (InfiniteLattice.smearedEnergy (X.1 l) U -
        ∫ V, InfiniteLattice.smearedEnergy (X.1 l) V ∂ν) := rfl
variable {ρ ν : ConfigMeasures L K} {σ : SeparatedTuples.TupleFunctional}
private theorem mixedCumulant_tendsto (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hC : Cumulants.CumulantMomentRelations)
    (hM : SmearedObservablesWellDefined) (hρ : ∀ j, IsProbabilityMeasure (ρ j))
    (h : IsRepresentativeLimit ρ ν σ) {n : ℕ} (hn : 1 ≤ n) (X : TestSpaces.SepTupleOfCard n) :
    Tendsto (fun j => Cumulants.mixedCumulant (ρ j) (centredObs (ν j) X.1)) atTop
      (𝓝 ((LimitTheorem.connectedFn σ X : ℝ) : ℂ)) := by
  have e : (fun j => Cumulants.mixedCumulant (ρ j) (centredObs (ν j) X.1)) = fun j =>
      ∑ π : SetPartition.PartitionsFin n, (-1 : ℂ) ^ (SetPartition.blockCount π - 1) *
        ((SetPartition.blockCount π - 1).factorial : ℂ) *
          ∏ J ∈ π.parts, ((∫ U, InfiniteLattice.CutoffRepresentative.centredProduct L (K j) (ν j)
            ⟨J.card, TestSpaces.sepRestrict X J⟩ U ∂ρ j : ℝ) : ℂ) := by
    funext j
    have := hρ j
    exact mixedCumulant_centredObs_eq_sum hC hM (spacingAt_pos hL (K j)) (ρ j) (ν j)
      (fun i => boundedCompact_of_mem_c1 (X.2.1 i)) hn
  rw [e, LimitTheorem.connectedFn, TestSpaces.cumulant_eq_sum_partitions]
  push_cast
  refine tendsto_finsetSum _ fun π _ => (tendsto_finsetProd _ fun J _ => ?_).const_mul _
  exact (Complex.continuous_ofReal.tendsto _).comp (h ⟨J.card, TestSpaces.sepRestrict X J⟩)
private theorem cumulantsAreLimits_of (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hC : Cumulants.CumulantMomentRelations)
    (hM : SmearedObservablesWellDefined) (hρ : ∀ j, IsProbabilityMeasure (ρ j))
    (h : IsRepresentativeLimit ρ ν σ) : CumulantsAreLimits ρ ν σ := by
  refine ⟨fun X => ?_, fun n hn X => ?_⟩
  · have e : ∀ j, ∫ U, InfiniteLattice.CutoffRepresentative.centredProduct L (K j) (ν j) ⟨1, X⟩ U ∂ρ j =
        (∫ U, InfiniteLattice.smearedEnergy (X.1 0) U ∂ρ j) -
          ∫ U, InfiniteLattice.smearedEnergy (X.1 0) U ∂ν j := fun j => by
      have := hρ j
      simp only [centredProduct_eq, Fin.prod_univ_one]
      rw [integral_sub (integrable_smearedEnergy hM (spacingAt_pos hL (K j)) (ρ j)
        (boundedCompact_of_mem_c1 (X.2.1 0))) (integrable_const _)]
      simp
    have ht := h ⟨1, X⟩
    simp only [e] at ht
    have hc : LimitTheorem.connectedFn σ X = LimitTheorem.evalOnMap σ ⟨1, X⟩ :=
      TestSpaces.cumulant_single _ X
    rwa [hc]
  · refine (mixedCumulant_tendsto hL hC hM hρ h (by omega) X).congr fun j => ?_
    have := hρ j
    exact mixedCumulant_centredObs_eq_smeared hC hM (spacingAt_pos hL (K j)) (ρ j) (ν j)
      (fun i => boundedCompact_of_mem_c1 (X.2.1 i)) hn
private theorem isLipschitzFor_of_mem_c1 {f : InfiniteLattice.AmbientSpace → ℝ}
    (hf : f ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ))) :
    TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 f := by apply _root_.YangMills.DeltaSharedProofs.p3475 <;> assumption
variable (hL : Conventions.IsAdmissibleBlockingFactor L) (hC : Cumulants.CumulantMomentRelations)
  (hM : SmearedObservablesWellDefined) (hρ : ∀ j, IsProbabilityMeasure (ρ j))
  (h : IsRepresentativeLimit ρ ν σ)
include hL hC hM hρ h
private theorem perBallBounds_of_states {M : ℝ} {C : LimitTheorem.ConditionConstants}
    (hB : StatesPerBallBounds M C ρ) : PerBallBoundsAt M C σ := by
  intro n hn R hR d hd X hball hsep
  have ht := ((cumulantsAreLimits_of hL hC hM hρ h).2 n hn X).norm
  rw [Complex.norm_real, Real.norm_eq_abs] at ht
  have hb := fun j => hB j n hn d hd R hR X.1 (fun i => isLipschitzFor_of_mem_c1 (X.2.1 i)) hball
    ⟨hd, hsep⟩
  exact ⟨le_of_tendsto' ht fun j => (hb j).1, le_of_tendsto' ht fun j => (hb j).2⟩
private theorem onePointBounded_of_states {M : ℝ} {c₁ : ℝ → ℝ}
    (hT : StatesOnePointTransfer M c₁ ρ ν) : OnePointBounded M c₁ σ := by
  rintro R hR X ⟨x, hx⟩
  have ht := ((cumulantsAreLimits_of hL hC hM hρ h).1 X).abs
  exact le_of_tendsto' ht fun j => hT j R hR (X.1 0) x (isLipschitzFor_of_mem_c1 (X.2.1 0)) hx
private theorem twoPointLaw_of_states (hP : Scales.SeparatedPairsAreTestFunctionsStatement)
    {ϑ : ℝ} {C : LimitTheorem.ConditionConstants} (hS : StatesObeyTwoPointLaw ϑ C ρ) :
    TwoPointLawHoldsAt ϑ C σ := by
  intro d hd f g hp hf hg
  refine ⟨⟨![f, g], pair_mem_disjointSupportTuples hP hd.1 hp hf hg⟩, rfl, ?_⟩
  have ht := (cumulantsAreLimits_of hL hC hM hρ h).2 2 le_rfl
    ⟨![f, g], pair_mem_disjointSupportTuples hP hd.1 hp hf hg⟩
  have hcomp : IsCompact ((fun t : ℝ => ((twoPointScale d f g * t : ℝ) : ℂ)) ''
      Icc (1 / 2 * (1 - C.ηBar d) ^ 4) (3 / 2 * (1 + C.ηBar d) ^ 4)) :=
    isCompact_Icc.image (by fun_prop)
  obtain ⟨t, ⟨h₁, h₂⟩, e⟩ := hcomp.isClosed.mem_of_tendsto ht
    ((hS d hd f g hp hf hg).mono fun j ⟨t, e, h₁, h₂⟩ => ⟨t, ⟨h₁, h₂⟩, e.symm⟩)
  have e' := Complex.ofReal_injective e
  refine ⟨t - 1, ?_, ?_, ?_⟩
  · rw [← e', twoPointScale]
    ring
  · linarith
  · linarith
end AlongCutoffs
section GrowthRequirement
private theorem mem_flatSchwartzSet {n : ℕ} {φ : TestSpaces.PointTuple n → ℂ}
    (h : φ ∈ ConfigSpace.schwartzFlatOffDiagonal n) : φ ∈ TestSpaces.flatSchwartzSet n := by apply _root_.YangMills.SharedProofs.p12297 <;> assumption
private def flatSequenceOf (U : (p : ℕ) → TestSpaces.flatSchwartzSet p → ℂ) :
    ConfigSpace.FlatSequence
  | 0, c => c.1
  | m + 1, φ => U (m + 1) ⟨φ.1, mem_flatSchwartzSet φ.2⟩
private theorem norm_le_of_ofReal_le
    (hN : Continuum.TwoPresentations.PresentationsAgree) {n k : ℕ} {c : ℝ} {z : ℂ}
    (φ : ConfigSpace.SchwartzFn n) (hc : 0 ≤ c)
    (h : ENNReal.ofReal ‖z‖ ≤ ENNReal.ofReal c * TestSpaces.weightedSeminorm k φ.1) :
    ‖z‖ ≤ c * ConfigSpace.bracketNorm k φ := by apply _root_.YangMills.SharedProofs.p4988 <;> assumption
private theorem isSepFamilyFunctional_evalOnConfig {σ : SeparatedTuples.TupleFunctional}
    (hf : TestSpaces.IsSepFunctional (LimitTheorem.evalOnMap σ)) :
    ConfigSpace.IsSepFamilyFunctional (LimitTheorem.evalOnConfig σ) := by apply _root_.YangMills.SharedProofs.p14370 <;> assumption
private theorem hasSchwingerSequence_flatSequenceOf
    (hN : Continuum.TwoPresentations.PresentationsAgree) {σ : SeparatedTuples.TupleFunctional}
    {U : (p : ℕ) → TestSpaces.flatSchwartzSet p → ℂ}
    (hf : TestSpaces.IsSepFunctional (LimitTheorem.evalOnMap σ))
    (hU : TestSpaces.IsSchwingerFamily (LimitTheorem.evalOnMap σ) U) :
    LimitTheorem.HasSchwingerSequence σ (flatSequenceOf U) := by
  refine ⟨isSepFamilyFunctional_evalOnConfig hf, fun _ => rfl, fun m => ⟨⟨?_, ?_⟩, fun X hX h => ?_⟩⟩
  · intro a b φ ψ χ e
    exact (hU.1 (m + 1) (by omega)).1 a b _ _ _ e
  · obtain ⟨k, c, hk, hc, hb⟩ := (hU.1 (m + 1) (by omega)).2.1
    exact ⟨k, c, hk, hc, fun φ =>
      norm_le_of_ofReal_le hN (ConfigSpace.toSchwartzFn φ) hc (hb ⟨φ.1, mem_flatSchwartzSet φ.2⟩)⟩
  · have hs : TestSpaces.HasSmoothComponents Set.univ X.1 := fun i => by
      obtain ⟨-, h₁, h₂, h₃⟩ := ConfigSpace.mem_realSmoothCompactIn_iff.1 (hX i)
      exact ⟨h₁, h₂, h₃⟩
    have et : ConfigSpace.tensorRealFamily X.1 = TestSpaces.tensorProdComplex X.1 := by
      funext x
      simp [ConfigSpace.tensorRealFamily, ConfigSpace.tensorFamily,
        TestSpaces.tensorProdComplex, TestSpaces.tensorProd]
    have hY : X.1 ∈ TestSpaces.disjointSupportTuples (Set.univ : Set (Fin 4 → ℝ)) (m + 1) :=
      (LimitTheorem.ofConfigTuple ⟨m + 1, X⟩).2.2
    have hv := (hU.1 (m + 1) (by omega)).2.2 ⟨X.1, hY⟩ hs (et ▸ mem_flatSchwartzSet h)
    refine Eq.trans ?_ hv
    exact congrArg (U (m + 1)) (Subtype.ext et)
private theorem growthBound_and_regular (hO : TestSpaces.OnePointFunctional.growth)
    (hD : TestSpaces.OffDiagonal.OffDiagonalFacts)
    (hN : Continuum.TwoPresentations.PresentationsAgree)
    {C : LimitTheorem.ConditionConstants} {σ : SeparatedTuples.TupleFunctional}
    {𝔠 cBar c Cstar Cσ : ℝ}
    (hf : TestSpaces.IsSepFunctional (LimitTheorem.evalOnMap σ)) (hn : IsOnePointCoefficient σ 𝔠)
    (ha : |𝔠| ≤ cBar) (hc : 0 ≤ c) (hs : 0 ≤ Cstar) (hle : Cstar ≤ Cσ) (hκ : 0 ≤ C.κ)
    (hk : 4 < C.kE) (hg : CentredGrowthBound σ C.kE c Cstar C.κ)
    (hcE : C.cE = 1 + c) (hCE : C.CE = TestSpaces.onePointConst C.kE Cσ cBar) :
    1 ≤ C.cE ∧ 0 ≤ C.CE ∧ LimitTheorem.GrowthBound C σ ∧
      TestSpaces.IsRegular (LimitTheorem.evalOnMap σ) := by
  obtain ⟨T, hT, hb⟩ := hg
  have hσ : 0 ≤ Cσ := hs.trans hle
  have hbar : 0 ≤ cBar := (abs_nonneg _).trans ha
  have hb' : ∀ p, 1 ≤ p → ∀ φ : TestSpaces.flatSchwartzSet p,
      ENNReal.ofReal ‖T p φ‖ ≤
        ENNReal.ofReal (c * Cσ ^ p * (p.factorial : ℝ) ^ C.κ) *
          TestSpaces.weightedSeminorm (C.kE * p) φ.1 := by
    intro p hp φ
    have hA : 0 ≤ c * Cσ ^ p * (p.factorial : ℝ) ^ C.κ := by positivity
    have h₁ : ‖T p φ‖ ≤ c * Cσ ^ p * (p.factorial : ℝ) ^ C.κ *
        (TestSpaces.weightedSeminorm (C.kE * p) φ.1).toReal := by
      refine (hb p hp φ).trans (mul_le_mul_of_nonneg_right ?_ ENNReal.toReal_nonneg)
      have h₂ : Cstar ^ p ≤ Cσ ^ p := pow_le_pow_left₀ hs hle p
      gcongr
    calc ENNReal.ofReal ‖T p φ‖
        ≤ ENNReal.ofReal (c * Cσ ^ p * (p.factorial : ℝ) ^ C.κ *
            (TestSpaces.weightedSeminorm (C.kE * p) φ.1).toReal) := ENNReal.ofReal_le_ofReal h₁
      _ = ENNReal.ofReal (c * Cσ ^ p * (p.factorial : ℝ) ^ C.κ) *
            ENNReal.ofReal (TestSpaces.weightedSeminorm (C.kE * p) φ.1).toReal :=
          ENNReal.ofReal_mul hA
      _ ≤ _ := by
        gcongr
        exact ENNReal.ofReal_toReal_le
  obtain ⟨-, -, hC0, hκ0, U, hU, hUb⟩ := (hO C.kE C.κ c Cσ cBar 𝔠 (LimitTheorem.evalOnMap σ) T hk hκ
    hc hσ hbar hf hn ha hT hb').2
  have hE : 0 ≤ C.cE := by rw [hcE]; linarith
  refine ⟨by rw [hcE]; linarith, by rw [hCE]; exact hC0, ⟨flatSequenceOf U,
    hasSchwingerSequence_flatSequenceOf hN hf hU, fun m φ => ?_⟩,
    ((hD 1 one_pos).2.2.1 (LimitTheorem.evalOnMap σ) U hf hU).1⟩
  have hcoef : 0 ≤ C.cE * C.CE ^ (m + 1) * ((m + 1).factorial : ℝ) ^ C.κ := by
    have : 0 ≤ C.CE := by rw [hCE]; exact hC0
    positivity
  refine norm_le_of_ofReal_le hN (ConfigSpace.toSchwartzFn φ) hcoef ?_
  have := hUb (m + 1) (by omega) ⟨φ.1, mem_flatSchwartzSet φ.2⟩
  rw [hcE, hCE]
  exact this
end GrowthRequirement
theorem inheritanceTheorem_of_smearedObservables (hC : Cumulants.CumulantMomentRelations)
    (hM : SmearedObservablesWellDefined)
    (hP : Scales.SeparatedPairsAreTestFunctionsStatement)
    (hG : TestPairs.GeometryAndKernelBounds)
    (hO : TestSpaces.OnePointFunctional.growth)
    (hD : TestSpaces.OffDiagonal.OffDiagonalFacts)
    (hN : Continuum.TwoPresentations.PresentationsAgree) : InheritanceTheorem := by
  refine ⟨fun L hL M ϑ K ρ ν σ hρ h => ⟨cumulantsAreLimits_of hL hC hM hρ h, rfl,
      fun C hB => perBallBounds_of_states hL hC hM hρ h hB, fun c₁ hT => ?_,
      fun C hS => twoPointLaw_of_states hL hC hM hρ h hP hS⟩,
    fun C σ 𝔠 cBar c Cstar Cσ hf hn ha hc hs hle hκ hk hg hcE hCE =>
      growthBound_and_regular hO hD hN hf hn ha hc hs hle hκ hk hg hcE hCE,
    fun ϑ C σ hϑ hd₀ hη hT => twoPointPositive_of_law hG hϑ hd₀ hη hT⟩
  have hb := onePointBounded_of_states hL hC hM hρ h hT
  exact ⟨hb, fun 𝔠 h0 hn => onePointCoefficient_bound hb h0 hn⟩
theorem inheritanceTheorem_holds (hC : Cumulants.CumulantMomentRelations)
    (hM : PeriodicGibbsLimits.ObservablesAndMomentsDefined.Statement)
    (hP : Scales.SeparatedPairsAreTestFunctionsStatement)
    (hG : TestPairs.GeometryAndKernelBounds)
    (hO : TestSpaces.OnePointFunctional.growth)
    (hD : TestSpaces.OffDiagonal.OffDiagonalFacts)
    (hN : Continuum.TwoPresentations.PresentationsAgree) : InheritanceTheorem :=
  inheritanceTheorem_of_smearedObservables hC (smearedObservablesWellDefined_of hM) hP hG hO hD hN
end YangMills.Construction.SystemsWithFiveBounds.GibbsLimitInheritance
end
