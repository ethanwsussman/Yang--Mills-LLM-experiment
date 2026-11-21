import YangMills.Construction.SpectralTheory.SpectralMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate
noncomputable section
namespace YangMills.Construction.SpectralTheory
section SimpleFunctions
variable {n : ℕ} {g g' : (Fin n → ℝ) → ℂ}
theorem IsSimpleBorel.add_const_mul (hg : IsSimpleBorel g) (hg' : IsSimpleBorel g') (z : ℂ) :
    IsSimpleBorel fun x => g x + z * g' x := by
  refine ⟨hg.1.add (hg'.1.const_mul z), ?_⟩
  refine ((hg.2.prod hg'.2).image fun p : ℂ × ℂ => p.1 + z * p.2).subset ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨(g x, g' x), ⟨⟨x, rfl⟩, ⟨x, rfl⟩⟩, rfl⟩
theorem IsSimpleBorel.mul (hg : IsSimpleBorel g) (hg' : IsSimpleBorel g') :
    IsSimpleBorel fun x => g x * g' x := by
  refine ⟨hg.1.mul hg'.1, ?_⟩
  refine ((hg.2.prod hg'.2).image fun p : ℂ × ℂ => p.1 * p.2).subset ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨(g x, g' x), ⟨⟨x, rfl⟩, ⟨x, rfl⟩⟩, rfl⟩
theorem IsSimpleBorel.conjugate (hg : IsSimpleBorel g) : IsSimpleBorel fun x => conj (g x) := by
  refine ⟨Complex.continuous_conj.measurable.comp hg.1, ?_⟩
  refine (hg.2.image fun z : ℂ => conj z).subset ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨g x, ⟨x, rfl⟩, rfl⟩
theorem IsSimpleBorel.indicator_one (A : BorelSets n) :
    IsSimpleBorel (A.1.indicator fun _ => (1 : ℂ)) := by
  refine ⟨measurable_const.indicator A.2, ?_⟩
  refine (Set.toFinite ({0, 1} : Set ℂ)).subset ?_
  rintro _ ⟨x, rfl⟩
  by_cases hx : x ∈ A.1 <;> simp [hx]
end SimpleFunctions
variable {n : ℕ} [NeZero n] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
namespace ProjectionMeasure
def polarizedIntegral (E : ProjectionMeasure n H) (u v : H) (g : (Fin n → ℝ) → ℂ) : ℂ :=
  (1 / 4 : ℂ) * ∑ k ∈ Finset.range 4,
    Complex.I ^ k * ∫ x, g x ∂(E.spectralValueMeasure (v + Complex.I ^ k • u))
def IsApproximantLimit (E : ProjectionMeasure n H) (f : (Fin n → ℝ) → ℂ) (v w : H) : Prop :=
  ∀ (g : ℕ → (Fin n → ℝ) → ℂ) (hg : ∀ k, IsSimpleBorel (g k)),
    Tendsto (fun k => ∫⁻ x, ‖g k x - f x‖ₑ ^ 2 ∂(E.spectralValueMeasure v)) atTop (𝓝 0) →
      Tendsto (fun k => simpleIntegral E (g k) (hg k) v) atTop (𝓝 w)
def approximantLimit (E : ProjectionMeasure n H) (f : (Fin n → ℝ) → ℂ) (v : H) : H :=
  haveI : Nonempty H := ⟨0⟩
  Classical.epsilon (E.IsApproximantLimit f v)
def IsApproximantLimitOperator (E : ProjectionMeasure n H) (f : (Fin n → ℝ) → ℂ)
    (T : UnboundedOperator H) : Prop :=
  (T.domain : Set H) = functionalDomain E f ∧ ∀ v : T.domain, T v = E.approximantLimit f v
structure SpectralValueMeasureRules (E : ProjectionMeasure n H) : Prop where
  polarization : ∀ (u v : H) (A : BorelSets n), E.spectralPairing u v A =
    (1 / 4 : ℂ) * ∑ k ∈ Finset.range 4, Complex.I ^ k * E.spectralValue (v + Complex.I ^ k • u) A
  linearCombination : ∀ u v : H, ∃ (μ : Fin 4 → Measure (Fin n → ℝ)) (c : Fin 4 → ℂ),
    (∀ k, IsFiniteMeasure (μ k)) ∧
      ∀ A : BorelSets n, E.spectralPairing u v A = ∑ k, c k * (((μ k A.1).toReal : ℝ) : ℂ)
  add_le : ∀ v u : H, E.spectralValueMeasure (v + u) ≤
    (2 : ℝ≥0∞) • E.spectralValueMeasure v + (2 : ℝ≥0∞) • E.spectralValueMeasure u
  smul : ∀ (z : ℂ) (v : H), E.spectralValueMeasure (z • v) = (‖z‖ₑ ^ 2) • E.spectralValueMeasure v
structure SimpleIntegralRules (E : ProjectionMeasure n H) : Prop where
  add_const_mul : ∀ {g g' : (Fin n → ℝ) → ℂ} (hg : IsSimpleBorel g) (hg' : IsSimpleBorel g') (z : ℂ),
    simpleIntegral E _ (hg.add_const_mul hg' z) =
      simpleIntegral E g hg + z • simpleIntegral E g' hg'
  mul : ∀ {g g' : (Fin n → ℝ) → ℂ} (hg : IsSimpleBorel g) (hg' : IsSimpleBorel g'),
    simpleIntegral E _ (hg.mul hg') = simpleIntegral E g hg * simpleIntegral E g' hg'
  conjugate : ∀ {g : (Fin n → ℝ) → ℂ} (hg : IsSimpleBorel g),
    simpleIntegral E _ hg.conjugate = star (simpleIntegral E g hg)
  indicator : ∀ A : BorelSets n, simpleIntegral E _ (IsSimpleBorel.indicator_one A) = E A
  inner : ∀ {g : (Fin n → ℝ) → ℂ} (hg : IsSimpleBorel g) (u v : H),
    ⟪u, simpleIntegral E g hg v⟫_ℂ = E.polarizedIntegral u v g
  norm_sq : ∀ {g : (Fin n → ℝ) → ℂ} (hg : IsSimpleBorel g) (v : H),
    ‖simpleIntegral E g hg v‖ ^ 2 = ∫ x, ‖g x‖ ^ 2 ∂(E.spectralValueMeasure v)
structure ApproximantLimitsExist (E : ProjectionMeasure n H) (f : (Fin n → ℝ) → ℂ) : Prop where
  isSubspace : ∃ S : Submodule ℂ H, (S : Set H) = functionalDomain E f
  dense : Dense (functionalDomain E f)
  exists_simple : ∀ v ∈ functionalDomain E f, ∃ g : ℕ → (Fin n → ℝ) → ℂ,
    (∀ k, IsSimpleBorel (g k)) ∧
      Tendsto (fun k => ∫⁻ x, ‖g k x - f x‖ₑ ^ 2 ∂(E.spectralValueMeasure v)) atTop (𝓝 0)
  existsUnique_limit : ∀ v ∈ functionalDomain E f, ∃! w : H, E.IsApproximantLimit f v w
  isApproximantLimit : ∀ v ∈ functionalDomain E f,
    E.IsApproximantLimit f v (E.approximantLimit f v)
  isLinear : ∃ T : UnboundedOperator H, E.IsApproximantLimitOperator f T
end ProjectionMeasure
namespace IntegralConstruction
def IntegralConstructionHolds : Prop :=
  ∀ (n : ℕ) [NeZero n] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (E : ProjectionMeasure n H),
    E.SpectralValueMeasureRules ∧ E.SimpleIntegralRules ∧
      ∀ f : (Fin n → ℝ) → ℂ, Measurable f → E.ApproximantLimitsExist f
end IntegralConstruction
end YangMills.Construction.SpectralTheory
