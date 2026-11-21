import YangMills.Construction.SpectralTheory.IntegralAndPushforward
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate ComplexOrder
noncomputable section
namespace YangMills.Construction.SpectralTheory
def IsBoundedComplexFn {n : ℕ} (f : (Fin n → ℝ) → ℂ) : Prop :=
  ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C
variable {n : ℕ} [NeZero n] {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
def toUnboundedOperator (T : H →L[ℂ] H) : UnboundedOperator H :=
  (T : H →ₗ[ℂ] H).toPMap ⊤
namespace ProjectionMeasure
def IsBoundedCalculusOf (E : ProjectionMeasure n H) (f : (Fin n → ℝ) → ℂ) (T : H →L[ℂ] H) :
    Prop :=
  E.functionalCalculus f = toUnboundedOperator T
def boundedCalculus (E : ProjectionMeasure n H) (f : (Fin n → ℝ) → ℂ) : H →L[ℂ] H :=
  Classical.epsilon (E.IsBoundedCalculusOf f)
def imageMeasure {m : ℕ} [NeZero m] (E : ProjectionMeasure n H) (p : (Fin n → ℝ) → Fin m → ℝ)
    (hp : Measurable p) : ProjectionMeasure m H where
  toFun := E.pushforward p hp
  isStarProjection _ := E.isStarProjection _
  map_empty := E.map_empty
  map_univ := E.map_univ
  map_inter A B := E.map_inter ⟨p ⁻¹' A.1, hp A.2⟩ ⟨p ⁻¹' B.1, hp B.2⟩
  tendsto_sum A hA v := by
    have h := E.tendsto_sum (fun r => ⟨p ⁻¹' (A r).1, hp (A r).2⟩)
      (fun r s hrs => (hA hrs).preimage p) v
    have hs : (⟨p ⁻¹' ⋃ r, (A r).1, hp (MeasurableSet.iUnion fun r => (A r).2)⟩ : BorelSets n) =
        ⟨⋃ r, p ⁻¹' (A r).1, MeasurableSet.iUnion fun r => hp (A r).2⟩ :=
      Subtype.ext preimage_iUnion
    simp only [pushforward]
    rw [hs]
    exact h
def unitaryTransport (E : ProjectionMeasure n H) (U : H ≃ₗᵢ[ℂ] K) :
    ProjectionMeasure n K where
  toFun A := (U.toContinuousLinearEquiv : H →L[ℂ] K) ∘L E A ∘L
    (U.symm.toContinuousLinearEquiv : K →L[ℂ] H)
  isStarProjection A := by
    have hP := E.isStarProjection A
    refine ⟨?_, ?_⟩
    · ext v
      have hi : E A (E A (U.symm v)) = E A (U.symm v) :=
        congrArg (fun T : H →L[ℂ] H => T (U.symm v)) hP.isIdempotentElem.eq
      simp [hi]
    · refine ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr fun u v => ?_
      have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hP.isSelfAdjoint
        (U.symm u) (U.symm v)
      have h₁ : ∀ (x : H) (y : K), ⟪U x, y⟫_ℂ = ⟪x, U.symm y⟫_ℂ := fun x y => by
        rw [← U.inner_map_map x (U.symm y), U.apply_symm_apply]
      have h₂ : ∀ (x : K) (y : H), ⟪x, U y⟫_ℂ = ⟪U.symm x, y⟫_ℂ := fun x y => by
        rw [← U.inner_map_map (U.symm x) y, U.apply_symm_apply]
      simpa [h₁, h₂] using hs
  map_empty := by
    ext v
    change U (E ⟨∅, MeasurableSet.empty⟩ (U.symm v)) = 0
    rw [E.map_empty]
    simp
  map_univ := by
    ext v
    simp [E.map_univ]
  map_inter A B := by
    ext v
    simp [E.map_inter]
  tendsto_sum A hA v := by
    have h := (U.continuous.tendsto _).comp (E.tendsto_sum A hA (U.symm v))
    refine h.congr fun N => ?_
    simp [map_sum]
structure CalculusLaws (E : ProjectionMeasure n H) : Prop where
  isOperator : ∀ f : (Fin n → ℝ) → ℂ, Measurable f →
    E.IsApproximantLimitOperator f (E.functionalCalculus f)
  norm_sq : ∀ f : (Fin n → ℝ) → ℂ, Measurable f → ∀ v : (E.functionalCalculus f).domain,
    ‖E.functionalCalculus f v‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂(E.spectralValueMeasure v)
  inner_self : ∀ f : (Fin n → ℝ) → ℂ, Measurable f → ∀ v : (E.functionalCalculus f).domain,
    ⟪(v : H), E.functionalCalculus f v⟫_ℂ = ∫ x, f x ∂(E.spectralValueMeasure v)
  add_const_mul : ∀ f g : (Fin n → ℝ) → ℂ, Measurable f → Measurable g → ∀ (z : ℂ) (v : H)
    (hf : v ∈ (E.functionalCalculus f).domain) (hg : v ∈ (E.functionalCalculus g).domain),
    ∃ h : v ∈ (E.functionalCalculus fun x => f x + z * g x).domain,
      (E.functionalCalculus fun x => f x + z * g x) ⟨v, h⟩ =
        E.functionalCalculus f ⟨v, hf⟩ + z • E.functionalCalculus g ⟨v, hg⟩
  calculus_congr : ∀ (f g : (Fin n → ℝ) → ℂ) (hf : Measurable f) (hg : Measurable g),
    E ⟨{x | f x ≠ g x}, (measurableSet_eq_fun hf hg).compl⟩ = 0 →
      E.functionalCalculus f = E.functionalCalculus g
  calculus_simple : ∀ (h : (Fin n → ℝ) → ℂ) (hh : IsSimpleBorel h),
    E.functionalCalculus h = toUnboundedOperator (simpleIntegral E h hh)
  functionalDomain_eq_univ : ∀ f : (Fin n → ℝ) → ℂ, Measurable f → IsBoundedComplexFn f →
    functionalDomain E f = univ
  isBoundedCalculusOf : ∀ f : (Fin n → ℝ) → ℂ, Measurable f → IsBoundedComplexFn f →
    E.IsBoundedCalculusOf f (E.boundedCalculus f)
  norm_boundedCalculus_le : ∀ f : (Fin n → ℝ) → ℂ, Measurable f → IsBoundedComplexFn f →
    ‖E.boundedCalculus f‖ ≤ ⨆ x, ‖f x‖
  inner_boundedCalculus : ∀ f : (Fin n → ℝ) → ℂ, Measurable f → IsBoundedComplexFn f →
    ∀ u v : H, ⟪u, E.boundedCalculus f v⟫_ℂ = E.polarizedIntegral u v f
  boundedCalculus_mul : ∀ f g : (Fin n → ℝ) → ℂ, Measurable f → Measurable g →
    IsBoundedComplexFn f → IsBoundedComplexFn g →
    E.boundedCalculus f * E.boundedCalculus g = E.boundedCalculus fun x => f x * g x
  star_boundedCalculus : ∀ f : (Fin n → ℝ) → ℂ, Measurable f → IsBoundedComplexFn f →
    star (E.boundedCalculus f) = E.boundedCalculus fun x => conj (f x)
  spectralValueMeasure_boundedCalculus : ∀ f g : (Fin n → ℝ) → ℂ, Measurable f → Measurable g →
    IsBoundedComplexFn g → ∀ v ∈ (E.functionalCalculus f).domain, ∀ A : BorelSets n,
    E.spectralValueMeasure (E.boundedCalculus g v) A.1 =
      ∫⁻ x in A.1, ‖g x‖ₑ ^ 2 ∂(E.spectralValueMeasure v)
  calculus_boundedCalculus : ∀ f g : (Fin n → ℝ) → ℂ, Measurable f → Measurable g →
    IsBoundedComplexFn g → ∀ (v : H) (hv : v ∈ (E.functionalCalculus f).domain),
    ∃ (hw : E.boundedCalculus g v ∈ (E.functionalCalculus f).domain)
      (hfg : v ∈ (E.functionalCalculus fun x => f x * g x).domain),
      E.functionalCalculus f ⟨E.boundedCalculus g v, hw⟩ =
          (E.functionalCalculus fun x => f x * g x) ⟨v, hfg⟩ ∧
        (E.functionalCalculus fun x => f x * g x) ⟨v, hfg⟩ =
          E.boundedCalculus g (E.functionalCalculus f ⟨v, hv⟩)
  loewnerGe_zero_iff : ∀ (f : (Fin n → ℝ) → ℂ) (hf : Measurable f), (∀ x, (f x).im = 0) →
    IsBoundedComplexFn f →
    (LoewnerGe (E.boundedCalculus f) 0 ↔
      E ⟨{x | (f x).re < 0}, measurableSet_lt (Complex.measurable_re.comp hf) measurable_const⟩ = 0)
  imageMeasure_apply : ∀ (m : ℕ) [NeZero m] (p : (Fin n → ℝ) → Fin m → ℝ) (hp : Measurable p)
    (B : BorelSets m), E.imageMeasure p hp B = E.pushforward p hp B
  calculus_imageMeasure : ∀ (m : ℕ) [NeZero m] (p : (Fin n → ℝ) → Fin m → ℝ)
    (hp : Measurable p) (h : (Fin m → ℝ) → ℂ), Measurable h →
    (E.imageMeasure p hp).functionalCalculus h = E.functionalCalculus (h ∘ p)
  unitaryTransport_apply : ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (U : H ≃ₗᵢ[ℂ] K) (A : BorelSets n) (v : K),
    E.unitaryTransport U A v = U (E A (U.symm v))
  unitaryTransport_vanishesOn : ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (U : H ≃ₗᵢ[ℂ] K) (A : BorelSets n),
    (E.unitaryTransport U).VanishesOn A ↔ E.VanishesOn A
  calculus_unitaryTransport : ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (U : H ≃ₗᵢ[ℂ] K) (f : (Fin n → ℝ) → ℂ), Measurable f →
    (E.unitaryTransport U).functionalCalculus f = unitaryConj U (E.functionalCalculus f)
  ext_of_fourier_or_boxes : ∀ F : ProjectionMeasure n H,
    ((∀ x : Fin n → ℝ,
        (F.functionalCalculus fun ξ => Complex.exp (Complex.I * ((∑ i, x i * ξ i : ℝ) : ℂ))) =
          E.functionalCalculus fun ξ => Complex.exp (Complex.I * ((∑ i, x i * ξ i : ℝ) : ℂ))) ∨
      ∀ (Δ : Fin n → Set ℝ) (hΔ : ∀ i, MeasurableSet (Δ i)),
        F ⟨Set.pi univ Δ, MeasurableSet.univ_pi hΔ⟩ = E ⟨Set.pi univ Δ, MeasurableSet.univ_pi hΔ⟩) →
      F = E
  eq_functionalCalculus_iff : ∀ f : (Fin n → ℝ) → ℂ, Measurable f → ∀ T : UnboundedOperator H,
    ((T.domain : Set H) = functionalDomain E f ∧
      ∀ v : T.domain, ⟪(v : H), T v⟫_ℂ = ∫ x, f x ∂(E.spectralValueMeasure v)) ↔
      T = E.functionalCalculus f
  eq_boundedCalculus_iff : ∀ f : (Fin n → ℝ) → ℂ, Measurable f → IsBoundedComplexFn f →
    ∀ T : H →L[ℂ] H,
    (∀ u v : H, ⟪u, T v⟫_ℂ = E.polarizedIntegral u v f) ↔ T = E.boundedCalculus f
end ProjectionMeasure
def SpectralIntegralLawsHold : Prop :=
  ∀ (n : ℕ) [NeZero n] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (E : ProjectionMeasure n H), E.CalculusLaws
end YangMills.Construction.SpectralTheory
