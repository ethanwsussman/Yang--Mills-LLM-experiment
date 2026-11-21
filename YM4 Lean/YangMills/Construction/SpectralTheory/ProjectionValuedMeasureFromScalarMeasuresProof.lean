import YangMills.Construction.ComplexMeasures.UniquenessOfMeasuresAndTheIntegralOfAComplexMeasure
import YangMills.Construction.HilbertSpace.BasicHilbertSpaceFacts
import YangMills.Construction.PositiveDefinite.KernelSymmBoundLimit
import YangMills.Construction.SpectralTheory.MeasuresIntegralsProductsImagesAndTransportOfAProjectionValuedMeasure
import YangMills.Construction.SpectralTheory.ProjectionValuedMeasureFromScalarMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ComplexConjugate ComplexOrder InnerProductSpace NNReal
noncomputable section
namespace YangMills.Construction.SpectralFromScalar
open YangMills.Construction.SetFunctions
  (CountablyAdditiveFn IsCountablyAdditive MeasurableSets PairwiseDisjointSeq iUnionSets)
open YangMills.Construction.BorelComplexMeasures
open YangMills.Construction.BorelSpectral YangMills.Construction.BorelSpectral.SpectralMeasure
open YangMills.Construction.MeasureUniqueness
  (IntegralWellDefined IsBoundedMeasurable IntegralRulesBounded IntegralRules)
variable {n : ℕ} {X : Set (Fin n → ℝ)} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
structure SeparatingFamily (G : Set (X → ℂ)) : Prop where
  one_le : 1 ≤ n
  measurableSet : MeasurableSet X
  rules : IntegralRulesBounded
  bounded : AllBoundedMeasurable G
  determines : SeparatesComplexMeasures G
theorem isBoundedMeasurable_const_one : IsBoundedMeasurable (fun _ : X => (1 : ℂ)) :=
  ⟨measurable_const, 1, fun _ => by simp⟩
theorem isBoundedMeasurable_indicator_one (Δ : MeasurableSets X) :
    IsBoundedMeasurable ((Δ : Set X).indicator fun _ => (1 : ℂ)) := by
  refine ⟨measurable_const.indicator Δ.2, 1, fun x => ?_⟩
  by_cases hx : x ∈ (Δ : Set X) <;> simp [hx]
theorem SeparatingFamily.integralRules {G : Set (X → ℂ)} (S : SeparatingFamily G)
    (ν ν' : CountablyAdditiveFn X) (c : ℂ) {g g' : X → ℂ} (hg : IsBoundedMeasurable g)
    (hg' : IsBoundedMeasurable g') :
    IntegralRules ν ν' c g g' id measurable_id g :=
  S.rules n n S.one_le S.one_le X X S.measurableSet S.measurableSet ν ν' c g g' id measurable_id g
    hg hg' hg
def SeparatingFamily.addSMul {G : Set (X → ℂ)} (S : SeparatingFamily G)
    (ν ν' : CountablyAdditiveFn X) (c : ℂ) : CountablyAdditiveFn X :=
  ⟨fun Δ => ν.1 Δ + c * ν'.1 Δ,
    (S.integralRules ν ν' c isBoundedMeasurable_const_one
      isBoundedMeasurable_const_one).add_smul_isCountablyAdditive⟩
theorem SeparatingFamily.eq_of_integralOf_eq {G : Set (X → ℂ)} (S : SeparatingFamily G)
    (ν ν' : CountablyAdditiveFn X) (h : ∀ g ∈ G, integralOf ν.1 g = integralOf ν'.1 g)
    (Δ : MeasurableSets X) : ν.1 Δ = ν'.1 Δ := by
  have h0 : ν.1 Δ + (-1) * ν'.1 Δ = 0 := S.determines (S.addSMul ν ν' (-1)) (fun g hg => by
    have hs := (S.integralRules ν ν' (-1) (S.bounded g hg) (S.bounded g hg)).integralOf_add_smul
    refine hs.trans ?_
    rw [h g hg]
    ring) Δ
  linear_combination h0
theorem hasSum_measureReal_iUnion (m : Measure X) [IsFiniteMeasure m] (A : ℕ → MeasurableSets X)
    (hA : PairwiseDisjointSeq A) :
    HasSum (fun j => ((m.real (A j).1 : ℝ) : ℂ)) ((m.real (iUnionSets A).1 : ℝ) : ℂ) := by
  have hu : m (iUnionSets A).1 = ∑' j, m (A j).1 :=
    measure_iUnion (f := fun j => (A j).1) hA (fun j => (A j).2)
  have hs : ∑' j, m (A j).1 ≠ ⊤ := by
    rw [← hu]
    exact measure_ne_top _ _
  have h := ENNReal.hasSum_toReal hs
  rw [← ENNReal.tsum_toReal_eq fun j => measure_ne_top _ _, ← hu] at h
  exact Complex.hasSum_ofReal.mpr h
def polarizedMeasure (ρ : K → Measure X) (φ ψ : K) (Δ : MeasurableSets X) : ℂ :=
  (1 / 4 : ℂ) * ∑ k ∈ Finset.range 4,
    Complex.I ^ k * (((ρ (ψ + Complex.I ^ k • φ)).real Δ.1 : ℝ) : ℂ)
theorem isCountablyAdditive_polarizedMeasure {ρ : K → Measure X}
    (hρ : ∀ ψ, IsFiniteMeasure (ρ ψ)) (φ ψ : K) :
    IsCountablyAdditive (polarizedMeasure ρ φ ψ) := by
  intro A hA
  have hs : ∀ k ∈ Finset.range 4, HasSum
      (fun j => Complex.I ^ k * (((ρ (ψ + Complex.I ^ k • φ)).real (A j).1 : ℝ) : ℂ))
      (Complex.I ^ k * (((ρ (ψ + Complex.I ^ k • φ)).real (iUnionSets A).1 : ℝ) : ℂ)) :=
    fun k _ => by
      have := hρ (ψ + Complex.I ^ k • φ)
      exact (hasSum_measureReal_iUnion _ A hA).mul_left _
  exact ((hasSum_sum hs).mul_left (1 / 4 : ℂ)).tendsto_sum_nat
theorem quarter_sum_I_pow (a : ℕ → ℂ) :
    (1 / 4 : ℂ) * ∑ k ∈ Finset.range 4, Complex.I ^ k * a k =
      ((1 / 4 : ℂ) * a 0 - (1 / 4 : ℂ) * a 2) +
        Complex.I * ((1 / 4 : ℂ) * a 1 - (1 / 4 : ℂ) * a 3) := by
  have h2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have h3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, h2]; ring
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, h2, h3]
  ring
def quarterMeasure (m : Measure X) : Measure X := (1 / 4 : ℝ≥0) • m
instance (m : Measure X) [IsFiniteMeasure m] : IsFiniteMeasure (quarterMeasure m) := by
  unfold quarterMeasure
  infer_instance
theorem quarterMeasure_real (m : Measure X) (s : Set X) :
    (quarterMeasure m).real s = 1 / 4 * m.real s := by
  simp [quarterMeasure, measureReal_nnreal_smul_apply]
theorem integral_quarterMeasure (m : Measure X) (g : X → ℂ) :
    ∫ x, g x ∂quarterMeasure m = (1 / 4 : ℂ) * ∫ x, g x ∂m := by
  unfold quarterMeasure
  rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  simp
theorem integrable_of_isBoundedMeasurable (m : Measure X) [IsFiniteMeasure m] {g : X → ℂ}
    (hg : IsBoundedMeasurable g) : Integrable g m := by
  obtain ⟨hm, c, hc⟩ := hg
  exact Integrable.of_bound hm.aestronglyMeasurable c (Eventually.of_forall hc)
theorem integrable_quarterMeasure (m : Measure X) [IsFiniteMeasure m] {g : X → ℂ}
    (hg : IsBoundedMeasurable g) : Integrable g (quarterMeasure m) :=
  integrable_of_isBoundedMeasurable _ hg
theorem integralOf_polarizedMeasure (he : IntegralWellDefined) (hn : 1 ≤ n)
    (hX : MeasurableSet X) (pol : HilbertSpace.BasicFacts.FormPolarization K)
    {ρ : K → Measure X} (hρ : ∀ ψ, IsFiniteMeasure (ρ ψ)) {g : X → ℂ}
    (hg : IsBoundedMeasurable g) (T : K →L[ℂ] K) (hT : ∀ ψ, ⟪ψ, T ψ⟫_ℂ = ∫ x, g x ∂ρ ψ)
    (φ ψ : K) : integralOf (polarizedMeasure ρ φ ψ) g = ⟪φ, T ψ⟫_ℂ := by
  let w : ℕ → K := fun k => ψ + Complex.I ^ k • φ
  have := fun k => hρ (w k)
  have hcomb : IsJordanCombination (polarizedMeasure ρ φ ψ) (quarterMeasure (ρ (w 0)))
      (quarterMeasure (ρ (w 2))) (quarterMeasure (ρ (w 1))) (quarterMeasure (ρ (w 3))) := by
    refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, fun Δ => ?_⟩
    have := quarter_sum_I_pow fun k => (((ρ (w k)).real Δ.1 : ℝ) : ℂ)
    simp only [polarizedMeasure, quarterMeasure_real]
    refine this.trans ?_
    push_cast
    ring
  have hv : IsIntegralOf (polarizedMeasure ρ φ ψ) g (combinedIntegral (quarterMeasure (ρ (w 0)))
      (quarterMeasure (ρ (w 2))) (quarterMeasure (ρ (w 1))) (quarterMeasure (ρ (w 3))) g) :=
    ⟨_, _, _, _, hcomb, hg.1, integrable_quarterMeasure _ hg, integrable_quarterMeasure _ hg,
      integrable_quarterMeasure _ hg, integrable_quarterMeasure _ hg, rfl⟩
  have hb : HilbertSpaceBasics.IsSesquilinear fun a c : K => ⟪a, T c⟫_ℂ :=
    { add_left := fun a b c => inner_add_left _ _ _
      smul_left := fun z a c => inner_smul_left _ _ _
      add_right := fun a b c => by simp only [map_add, inner_add_right]
      smul_right := fun z a c => by simp only [map_smul, inner_smul_right] }
  rw [(he n hn X hX).2 _ _ _ hv]
  have hp := pol _ hb φ ψ
  have hq := quarter_sum_I_pow fun k => ⟪w k, T (w k)⟫_ℂ
  simp only [combinedIntegral, integral_quarterMeasure, ← hT]
  refine Eq.trans ?_ (hp.trans hq).symm
  ring
def ofMeasureReal (m : Measure X) (Δ : MeasurableSets X) : ℂ := ((m.real Δ.1 : ℝ) : ℂ)
theorem isCountablyAdditive_ofMeasureReal (m : Measure X) [IsFiniteMeasure m] :
    IsCountablyAdditive (ofMeasureReal m) :=
  fun A hA => (hasSum_measureReal_iUnion m A hA).tendsto_sum_nat
theorem integralOf_ofMeasureReal (he : IntegralWellDefined) (hn : 1 ≤ n)
    (hX : MeasurableSet X) (m : Measure X) [IsFiniteMeasure m] {g : X → ℂ}
    (hg : IsBoundedMeasurable g) : integralOf (ofMeasureReal m) g = ∫ x, g x ∂m := by
  have hv : IsIntegralOf (ofMeasureReal m) g (combinedIntegral m 0 0 0 g) :=
    ⟨m, 0, 0, 0, ⟨inferInstance, inferInstance, inferInstance, inferInstance,
      fun Δ => by simp [ofMeasureReal]⟩, hg.1, integrable_of_isBoundedMeasurable m hg,
      integrable_of_isBoundedMeasurable _ hg, integrable_of_isBoundedMeasurable _ hg,
      integrable_of_isBoundedMeasurable _ hg, rfl⟩
  rw [(he n hn X hX).2 _ _ _ hv]
  simp [combinedIntegral]
theorem kernelPosSemidef_of_sesquilinear {b : K → K → ℂ}
    (hb : HilbertSpaceBasics.IsSesquilinear b) (hp : ∀ u, 0 ≤ b u u) :
    PositiveDefinite.KernelPosSemidefOnSet b := by
  intro m u c
  have h0l : ∀ y, b 0 y = 0 := fun y => by
    have := hb.smul_left 0 0 y
    simpa using this
  have h0r : ∀ y, b y 0 = 0 := fun y => by
    have := hb.smul_right 0 y 0
    simpa using this
  have hl : ∀ (s : Finset (Fin m)) (f : Fin m → K) (y : K),
      b (∑ a ∈ s, f a) y = ∑ a ∈ s, b (f a) y := by
    intro s f y
    induction s using Finset.cons_induction with
    | empty => simpa using h0l y
    | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, hb.add_left, ih]
  have hr : ∀ (s : Finset (Fin m)) (f : Fin m → K) (y : K),
      b y (∑ a ∈ s, f a) = ∑ a ∈ s, b y (f a) := by
    intro s f y
    induction s using Finset.cons_induction with
    | empty => simpa using h0r y
    | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, hb.add_right, ih]
  have key : b (∑ a, c a • u a) (∑ a, c a • u a) =
      ∑ a, ∑ d, conj (c a) * c d * b (u a) (u d) := by
    rw [hl]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hr]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hb.smul_left, hb.smul_right]
    ring
  rw [← key]
  exact hp _
structure ScalarSetting (G : Set (X → ℂ)) (hG : IsConjClosedUnital G)
    (P : G → K →L[ℂ] K) (ρ : K → Measure X) : Prop extends SeparatingFamily G where
  independent : IntegralWellDefined
  polarization : HilbertSpace.BasicFacts.FormPolarization K
  respects : IsStarHomOn hG P
  scalars : HasDiagonalMeasures P ρ
namespace ScalarSetting
variable {G : Set (X → ℂ)} {hG : IsConjClosedUnital G} {P : G → K →L[ℂ] K}
  {ρ : K → Measure X}
theorem isFiniteMeasure (S : ScalarSetting G hG P ρ) (ψ : K) : IsFiniteMeasure (ρ ψ) :=
  (S.scalars ψ).1
theorem isBoundedMeasurable (S : ScalarSetting G hG P ρ) (g : G) : IsBoundedMeasurable g.1 :=
  S.bounded g.1 g.2
def coeffMeasure (S : ScalarSetting G hG P ρ) (φ ψ : K) : CountablyAdditiveFn X :=
  ⟨polarizedMeasure ρ φ ψ, isCountablyAdditive_polarizedMeasure S.isFiniteMeasure φ ψ⟩
theorem integralOf_coeffMeasure (S : ScalarSetting G hG P ρ) (g : G) (φ ψ : K) :
    integralOf (polarizedMeasure ρ φ ψ) g.1 = ⟪φ, P g ψ⟫_ℂ :=
  integralOf_polarizedMeasure S.independent S.one_le S.measurableSet S.polarization
    S.isFiniteMeasure (S.isBoundedMeasurable g) (P g) (fun ψ => (S.scalars ψ).2 g) φ ψ
theorem eq_of_integralOf_eq (S : ScalarSetting G hG P ρ) (ν ν' : CountablyAdditiveFn X)
    (h : ∀ g : G, integralOf ν.1 g.1 = integralOf ν'.1 g.1) (Δ : MeasurableSets X) :
    ν.1 Δ = ν'.1 Δ :=
  S.toSeparatingFamily.eq_of_integralOf_eq ν ν' (fun g hg => h ⟨g, hg⟩) Δ
theorem polarizedMeasure_add_smul_right (S : ScalarSetting G hG P ρ) (φ ψ ψ' : K) (c : ℂ)
    (Δ : MeasurableSets X) :
    polarizedMeasure ρ φ (ψ + c • ψ') Δ =
      polarizedMeasure ρ φ ψ Δ + c * polarizedMeasure ρ φ ψ' Δ := by
  refine S.eq_of_integralOf_eq (S.coeffMeasure φ (ψ + c • ψ'))
    (S.toSeparatingFamily.addSMul (S.coeffMeasure φ ψ) (S.coeffMeasure φ ψ') c) (fun g => ?_) Δ
  have hs := (S.toSeparatingFamily.integralRules (S.coeffMeasure φ ψ) (S.coeffMeasure φ ψ') c
    (S.isBoundedMeasurable g) (S.isBoundedMeasurable g)).integralOf_add_smul
  refine Eq.trans ?_ hs.symm
  show integralOf (polarizedMeasure ρ φ (ψ + c • ψ')) g.1 =
    integralOf (polarizedMeasure ρ φ ψ) g.1 + c * integralOf (polarizedMeasure ρ φ ψ') g.1
  rw [S.integralOf_coeffMeasure, S.integralOf_coeffMeasure, S.integralOf_coeffMeasure, map_add,
    map_smul, inner_add_right, inner_smul_right]
theorem polarizedMeasure_add_smul_left (S : ScalarSetting G hG P ρ) (φ φ' ψ : K) (c : ℂ)
    (Δ : MeasurableSets X) :
    polarizedMeasure ρ (φ + c • φ') ψ Δ =
      polarizedMeasure ρ φ ψ Δ + conj c * polarizedMeasure ρ φ' ψ Δ := by
  refine S.eq_of_integralOf_eq (S.coeffMeasure (φ + c • φ') ψ)
    (S.toSeparatingFamily.addSMul (S.coeffMeasure φ ψ) (S.coeffMeasure φ' ψ) (conj c))
    (fun g => ?_) Δ
  have hs := (S.toSeparatingFamily.integralRules (S.coeffMeasure φ ψ) (S.coeffMeasure φ' ψ)
    (conj c) (S.isBoundedMeasurable g) (S.isBoundedMeasurable g)).integralOf_add_smul
  refine Eq.trans ?_ hs.symm
  show integralOf (polarizedMeasure ρ (φ + c • φ') ψ) g.1 =
    integralOf (polarizedMeasure ρ φ ψ) g.1 + conj c * integralOf (polarizedMeasure ρ φ' ψ) g.1
  rw [S.integralOf_coeffMeasure, S.integralOf_coeffMeasure, S.integralOf_coeffMeasure,
    inner_add_left, inner_smul_left]
theorem polarizedMeasure_zero_right (S : ScalarSetting G hG P ρ) (φ : K) (Δ : MeasurableSets X) :
    polarizedMeasure ρ φ 0 Δ = 0 :=
  S.determines (S.coeffMeasure φ 0)
    (fun g hg => (S.integralOf_coeffMeasure ⟨g, hg⟩ φ 0).trans (by simp)) Δ
theorem polarizedMeasure_zero_left (S : ScalarSetting G hG P ρ) (ψ : K) (Δ : MeasurableSets X) :
    polarizedMeasure ρ 0 ψ Δ = 0 :=
  S.determines (S.coeffMeasure 0 ψ)
    (fun g hg => (S.integralOf_coeffMeasure ⟨g, hg⟩ 0 ψ).trans (by simp)) Δ
theorem isSesquilinear (S : ScalarSetting G hG P ρ) (Δ : MeasurableSets X) :
    HilbertSpaceBasics.IsSesquilinear fun φ ψ : K => polarizedMeasure ρ φ ψ Δ where
  add_left a b c := by simpa using S.polarizedMeasure_add_smul_left a b c 1 Δ
  smul_left z a c := by
    simpa [S.polarizedMeasure_zero_left] using S.polarizedMeasure_add_smul_left 0 a c z Δ
  add_right a b c := by simpa using S.polarizedMeasure_add_smul_right a b c 1 Δ
  smul_right z a c := by
    simpa [S.polarizedMeasure_zero_right] using S.polarizedMeasure_add_smul_right a 0 c z Δ
theorem polarizedMeasure_self (S : ScalarSetting G hG P ρ) (ψ : K) (Δ : MeasurableSets X) :
    polarizedMeasure ρ ψ ψ Δ = ofMeasureReal (ρ ψ) Δ := by
  have := S.isFiniteMeasure ψ
  refine S.eq_of_integralOf_eq (S.coeffMeasure ψ ψ)
    ⟨ofMeasureReal (ρ ψ), isCountablyAdditive_ofMeasureReal _⟩ (fun g => ?_) Δ
  show integralOf (polarizedMeasure ρ ψ ψ) g.1 = integralOf (ofMeasureReal (ρ ψ)) g.1
  rw [S.integralOf_coeffMeasure, integralOf_ofMeasureReal S.independent S.one_le S.measurableSet _
    (S.isBoundedMeasurable g)]
  exact (S.scalars ψ).2 g
theorem measureReal_univ (S : ScalarSetting G hG P ρ) (ψ : K) : (ρ ψ).real univ = ‖ψ‖ ^ 2 := by
  have h := (S.scalars ψ).2 ⟨_, hG.contains_one⟩
  rw [S.respects.preserves_one] at h
  have h' : ((‖ψ‖ ^ 2 : ℝ) : ℂ) = (((ρ ψ).real univ : ℝ) : ℂ) := by
    simpa [inner_self_eq_norm_sq_to_K] using h
  exact_mod_cast h'.symm
theorem exists_selfAdjoint_op (S : ScalarSetting G hG P ρ)
    (hk : PositiveDefinite.KernelSymmBound.SymmBoundLimitProperties)
    (hform : HilbertSpace.BasicFacts.BoundedFormRepresentation K) (Δ : MeasurableSets X) :
    ∃ B : K →L[ℂ] K, (∀ φ ψ, polarizedMeasure ρ φ ψ Δ = ⟪φ, B ψ⟫_ℂ) ∧
      OperatorTransport.IsSelfAdjointCLM B := by
  have hb := S.isSesquilinear Δ
  have hnon : ∀ u, 0 ≤ polarizedMeasure ρ u u Δ := fun u => by
    rw [S.polarizedMeasure_self]
    exact Complex.zero_le_real.mpr measureReal_nonneg
  have hker := kernelPosSemidef_of_sesquilinear hb hnon
  have hfact := (hk K).1 _ hker
  have hm : ∀ u, (ρ u).real Δ.1 ≤ ‖u‖ ^ 2 := fun u => by
    have := S.isFiniteMeasure u
    rw [← S.measureReal_univ]
    exact measureReal_mono (subset_univ _)
  have hbound : ∀ φ ψ : K, ‖polarizedMeasure ρ φ ψ Δ‖ ≤ 1 * ‖φ‖ * ‖ψ‖ := fun φ ψ => by
    have h1 : ((‖polarizedMeasure ρ φ ψ Δ‖ ^ 2 : ℝ) : ℂ) ≤
        polarizedMeasure ρ φ φ Δ * polarizedMeasure ρ ψ ψ Δ :=
      (hfact.1 φ ψ).2
    rw [S.polarizedMeasure_self, S.polarizedMeasure_self] at h1
    simp only [ofMeasureReal] at h1
    rw [← Complex.ofReal_mul] at h1
    have h2 := Complex.real_le_real.mp h1
    have h3 : ‖polarizedMeasure ρ φ ψ Δ‖ ^ 2 ≤ (1 * ‖φ‖ * ‖ψ‖) ^ 2 := by
      calc _ ≤ _ := h2
        _ ≤ ‖φ‖ ^ 2 * ‖ψ‖ ^ 2 := mul_le_mul (hm φ) (hm ψ) measureReal_nonneg (by positivity)
        _ = _ := by ring
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp h3
  obtain ⟨B, hB, -, -, hs⟩ := hform _ 1 hb zero_le_one hbound
  exact ⟨B, hB, hs fun φ ψ => (hfact.1 φ ψ).1⟩
theorem polarizedMeasure_conj (S : ScalarSetting G hG P ρ) (g : G) (φ ψ : K)
    (Δ : MeasurableSets X) :
    polarizedMeasure ρ (P ⟨_, hG.closed_conj g.1 g.2⟩ φ) ψ Δ =
      densityMul g.1 (polarizedMeasure ρ φ ψ) Δ := by
  have hmul : IsCountablyAdditive (densityMul g.1 (polarizedMeasure ρ φ ψ)) :=
    (S.toSeparatingFamily.integralRules (S.coeffMeasure φ ψ) (S.coeffMeasure φ ψ) 1
      (S.isBoundedMeasurable g) (S.isBoundedMeasurable g)).densityMul_isCountablyAdditive
  refine S.eq_of_integralOf_eq (S.coeffMeasure _ ψ) ⟨_, hmul⟩ (fun g' => ?_) Δ
  have hr := (S.toSeparatingFamily.integralRules (S.coeffMeasure φ ψ) (S.coeffMeasure φ ψ) 1
    (S.isBoundedMeasurable g) (S.isBoundedMeasurable g')).integralOf_densityMul
  refine Eq.trans ?_ hr.symm
  show integralOf (polarizedMeasure ρ _ ψ) g'.1 =
    integralOf (polarizedMeasure ρ φ ψ) fun x => g'.1 x * g.1 x
  have hc := S.integralOf_coeffMeasure (⟨_, hG.closed_mul g.1 g.2 g'.1 g'.2⟩ : G) φ ψ
  have hswap : (fun x => g'.1 x * g.1 x) = fun x => g.1 x * g'.1 x :=
    funext fun x => mul_comm _ _
  rw [S.integralOf_coeffMeasure, hswap]
  refine Eq.trans ?_ hc.symm
  rw [S.respects.preserves_mul g g']
  exact (S.respects.preserves_adjoint g φ (P g' ψ)).symm
theorem inner_mul_eq_polarizedMeasure_inter (S : ScalarSetting G hG P ρ)
    {F : MeasurableSets X → K →L[ℂ] K}
    (hF : ∀ Δ φ ψ, polarizedMeasure ρ φ ψ Δ = ⟪φ, F Δ ψ⟫_ℂ) (Δ Δ' : MeasurableSets X) (φ ψ : K) :
    ⟪φ, F Δ (F Δ' ψ)⟫_ℂ = polarizedMeasure ρ φ ψ ⟨Δ.1 ∩ Δ'.1, Δ.2.inter Δ'.2⟩ := by
  have hb' := isBoundedMeasurable_indicator_one Δ'
  have hmul : IsCountablyAdditive
      (densityMul ((Δ' : Set X).indicator fun _ => (1 : ℂ)) (polarizedMeasure ρ φ ψ)) :=
    (S.toSeparatingFamily.integralRules (S.coeffMeasure φ ψ) (S.coeffMeasure φ ψ) 1 hb'
      hb').densityMul_isCountablyAdditive
  have h1 : polarizedMeasure ρ φ (F Δ' ψ) Δ =
      densityMul ((Δ' : Set X).indicator fun _ => (1 : ℂ)) (polarizedMeasure ρ φ ψ) Δ := by
    refine S.eq_of_integralOf_eq (S.coeffMeasure φ (F Δ' ψ)) ⟨_, hmul⟩ (fun g => ?_) Δ
    have hr := (S.toSeparatingFamily.integralRules (S.coeffMeasure φ ψ) (S.coeffMeasure φ ψ) 1
      hb' (S.isBoundedMeasurable g)).integralOf_densityMul
    refine Eq.trans ?_ hr.symm
    show integralOf (polarizedMeasure ρ φ (F Δ' ψ)) g.1 = integralOf (polarizedMeasure ρ φ ψ)
      fun x => g.1 x * (Δ' : Set X).indicator (fun _ => (1 : ℂ)) x
    have hm := S.polarizedMeasure_conj g φ ψ Δ'
    have hswap : (fun x => g.1 x * (Δ' : Set X).indicator (fun _ => (1 : ℂ)) x) =
        fun x => (Δ' : Set X).indicator (fun _ => (1 : ℂ)) x * g.1 x :=
      funext fun x => mul_comm _ _
    have hadj : ⟪φ, P g (F Δ' ψ)⟫_ℂ = ⟪P ⟨_, hG.closed_conj g.1 g.2⟩ φ, F Δ' ψ⟫_ℂ :=
      S.respects.preserves_adjoint g φ _
    rw [S.integralOf_coeffMeasure, hswap, hadj, ← hF Δ']
    exact hm
  rw [← hF Δ φ (F Δ' ψ), h1]
  have hbi := isBoundedMeasurable_indicator_one
    (⟨Δ.1 ∩ Δ'.1, Δ.2.inter Δ'.2⟩ : MeasurableSets X)
  have hi := (S.toSeparatingFamily.integralRules (S.coeffMeasure φ ψ) (S.coeffMeasure φ ψ) 1 hbi
    hbi).integralOf_indicator ⟨Δ.1 ∩ Δ'.1, Δ.2.inter Δ'.2⟩
  have hfun : (fun x => (Δ : Set X).indicator (fun _ => (1 : ℂ)) x *
        (Δ' : Set X).indicator (fun _ => (1 : ℂ)) x) =
      (Δ.1 ∩ Δ'.1).indicator fun _ => (1 : ℂ) := by
    funext x
    by_cases h : x ∈ Δ.1 <;> by_cases h' : x ∈ Δ'.1 <;> simp [h, h', Set.indicator]
  show integralOf (polarizedMeasure ρ φ ψ) (fun x => (Δ : Set X).indicator (fun _ => (1 : ℂ)) x *
    (Δ' : Set X).indicator (fun _ => (1 : ℂ)) x) = _
  rw [hfun]
  exact hi
variable [CompleteSpace K]
theorem exists_spectralMeasure (S : ScalarSetting G hG P ρ)
    (hk : PositiveDefinite.KernelSymmBound.SymmBoundLimitProperties)
    (hform : HilbertSpace.BasicFacts.BoundedFormRepresentation K) :
    ∃ E : SpectralMeasure X K, ∀ (Δ : BorelSubsets X) (φ ψ : K),
      polarizedMeasure ρ φ ψ Δ = ⟪φ, E Δ ψ⟫_ℂ := by
  choose F hF hs using S.exists_selfAdjoint_op hk hform
  have hm : ∀ Δ Δ' : MeasurableSets X, F ⟨Δ.1 ∩ Δ'.1, Δ.2.inter Δ'.2⟩ = F Δ * F Δ' :=
    fun Δ Δ' => by
      refine ContinuousLinearMap.ext fun ψ => ext_inner_left ℂ fun φ => ?_
      exact (hF _ φ ψ).symm.trans (S.inner_mul_eq_polarizedMeasure_inter hF Δ Δ' φ ψ).symm
  have hone : F ⟨univ, MeasurableSet.univ⟩ = 1 := by
    refine ContinuousLinearMap.ext fun ψ => ext_inner_left ℂ fun φ => ?_
    rw [← hF]
    have hbu := isBoundedMeasurable_indicator_one
      (⟨univ, MeasurableSet.univ⟩ : MeasurableSets X)
    have hi := (S.toSeparatingFamily.integralRules (S.coeffMeasure φ ψ) (S.coeffMeasure φ ψ) 1
      hbu hbu).integralOf_indicator ⟨univ, MeasurableSet.univ⟩
    have hfun : (univ : Set X).indicator (fun _ => (1 : ℂ)) = fun _ => 1 := by simp
    have hc := S.integralOf_coeffMeasure (⟨_, hG.contains_one⟩ : G) φ ψ
    rw [S.respects.preserves_one] at hc
    refine hi.symm.trans ?_
    show integralOf (polarizedMeasure ρ φ ψ) ((univ : Set X).indicator fun _ => (1 : ℂ)) = _
    rw [hfun]
    exact hc
  have he : ∀ (D : MeasurableSets X) (ψ : K), ⟪ψ, F D ψ⟫_ℂ = ofMeasureReal (ρ ψ) D :=
    fun D ψ => (hF D ψ ψ).symm.trans (S.polarizedMeasure_self ψ D)
  refine ⟨{ one_le_dimension := S.one_le
            measurableSet_carrier := S.measurableSet
            toFun := F
            isStarProjection := fun Δ => ⟨?_, ?_⟩
            map_univ := hone
            map_inter := hm
            countablyAdditive := fun ψ Δ hd => ?_ }, fun Δ φ ψ => hF Δ φ ψ⟩
  · exact (hm Δ Δ).symm.trans (congrArg F (Subtype.ext (inter_self _)))
  · exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr fun x y => (hs Δ x y).symm
  · have := S.isFiniteMeasure ψ
    simp only [he]
    exact hasSum_measureReal_iUnion (ρ ψ) Δ hd
end ScalarSetting
theorem scalarDeterminationTheorem_holds (hc : SpectralMeasureCalculus.CalculusTheorem)
    (hm : MeasureUniqueness.UniquenessAndIntegral)
    (hf : HilbertSpace.BasicFacts.BasicHilbertSpaceFacts)
    (hk : PositiveDefinite.KernelSymmBound.SymmBoundLimitProperties) :
    ScalarDeterminationTheorem := by
  intro K _ _ _ n hn X hX _ G hGb hGu
  obtain ⟨-, -, -, -, he, hr, -⟩ := hm
  obtain ⟨-, -, pol, -, -, -, -, hform, -, -, -, -⟩ := hf K K
  have S : SeparatingFamily G := ⟨hn, hX, hr, hGb, hGu⟩
  have ha : ∀ E E' : SpectralMeasure X K,
      (∀ g ∈ G, E.integralOp g = E'.integralOp g) → E = E' := by
    intro E E' h
    refine SpectralMeasure.ext_apply fun Δ =>
      ContinuousLinearMap.ext fun ψ => ext_inner_left ℂ fun φ => ?_
    refine S.eq_of_integralOf_eq ⟨_, (hc K n X E).1.isComplexMeasure φ ψ⟩
      ⟨_, (hc K n X E').1.isComplexMeasure φ ψ⟩ (fun g hg => ?_) Δ
    have h₁ := (hc K n X E).2.1.inner_eq g (hGb g hg).1 (hGb g hg).2 φ ψ
    have h₂ := (hc K n X E').2.1.inner_eq g (hGb g hg).1 (hGb g hg).2 φ ψ
    exact h₁.symm.trans ((congrArg (fun T : K →L[ℂ] K => ⟪φ, T ψ⟫_ℂ) (h g hg)).trans h₂)
  refine ⟨ha, ?_, ?_⟩
  · intro E B h Δ
    exact show B * E Δ = E Δ * B from by
      refine ContinuousLinearMap.ext fun ψ => ext_inner_left ℂ fun φ => ?_
      have hB := (hc K n X E).2.2.2.2.2.2.2
      refine S.eq_of_integralOf_eq ⟨_, hB.isComplexMeasure B φ ψ⟩
        ⟨_, (hc K n X E).1.isComplexMeasure φ (B ψ)⟩ (fun g hg => ?_) Δ
      have h₁ := hB.integral_eq B φ ψ g (hGb g hg).1 (hGb g hg).2
      have h₂ := (hc K n X E).2.1.inner_eq g (hGb g hg).1 (hGb g hg).2 φ (B ψ)
      have h₃ : B * E.integralOp g = E.integralOp g * B := h g hg
      refine h₁.trans (Eq.trans ?_ h₂)
      exact congrArg (fun T : K →L[ℂ] K => ⟪φ, T ψ⟫_ℂ) h₃
  · intro hG P ρ hP hρ
    have S' : ScalarSetting G hG P ρ :=
      { toSeparatingFamily := S, independent := he, polarization := pol, respects := hP,
        scalars := hρ }
    obtain ⟨E, hE⟩ := S'.exists_spectralMeasure hk hform
    have hint : ∀ g : G, P g = E.integralOp g := fun g => by
      refine ContinuousLinearMap.ext fun ψ => ext_inner_left ℂ fun φ => ?_
      have hcm : E.matrixCoeff φ ψ = polarizedMeasure ρ φ ψ := funext fun Δ => (hE Δ φ ψ).symm
      rw [(hc K n X E).2.1.inner_eq g.1 (hGb g.1 g.2).1 (hGb g.1 g.2).2 φ ψ, hcm,
        S'.integralOf_coeffMeasure g φ ψ]
    have hscal : ∀ ψ, E.diagMeasure ψ = ρ ψ := fun ψ => by
      have := S'.isFiniteMeasure ψ
      refine Measure.ext fun s hs => ?_
      have h₁ : (((E.diagMeasure ψ).real s : ℝ) : ℂ) = (((ρ ψ).real s : ℝ) : ℂ) :=
        (E.inner_apply_self_eq_diagMeasure ψ ⟨s, hs⟩).symm.trans
          ((hE ⟨s, hs⟩ ψ ψ).symm.trans (S'.polarizedMeasure_self ψ ⟨s, hs⟩))
      have h₂ : (E.diagMeasure ψ).real s = (ρ ψ).real s := by exact_mod_cast h₁
      exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp h₂
    have huniq : ∀ E' : SpectralMeasure X K, (∀ g : G, P g = E'.integralOp g) →
        E' = E := fun E' h => ha _ _ fun g hg => (h ⟨g, hg⟩).symm.trans (hint ⟨g, hg⟩)
    exact ⟨⟨E, hint, huniq⟩, fun E' h ψ => by rw [huniq E' h]; exact hscal ψ⟩
end YangMills.Construction.SpectralFromScalar
