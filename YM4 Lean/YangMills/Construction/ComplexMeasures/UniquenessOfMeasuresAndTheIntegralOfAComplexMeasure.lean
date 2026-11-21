import YangMills.Construction.Analysis.EuclideanNormsConesAndSummableFamilies
import YangMills.Construction.MeasureTheory.FourMeasureIntegral
import YangMills.Construction.MeasureTheory.PushforwardAndRestriction
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate ENNReal Matrix NNReal
noncomputable section
namespace YangMills.Construction.MeasureUniqueness
def expLaplaceFourier {r : ℕ} (k : ℕ) (v : Fin r → ℝ)
    (p : Set.Ici (0 : ℝ) × (Fin r → ℝ)) : ℂ :=
  Complex.exp (-(k : ℂ) * (((p.1 : ℝ)) : ℂ) + Complex.I * ((v ⬝ᵥ p.2 : ℝ) : ℂ))
def fourierExp {r : ℕ} (v q : Fin r → ℝ) : ℂ :=
  Complex.exp (Complex.I * ((v ⬝ᵥ q : ℝ) : ℂ))
def laplaceExp (k : ℕ) (E : Set.Ici (0 : ℝ)) : ℂ :=
  Complex.exp (-(k : ℂ) * ((E : ℝ) : ℂ))
def IsBoundedMeasurable {X : Type*} [MeasurableSpace X] (g : X → ℂ) : Prop :=
  Measurable g ∧ ∃ c : ℝ, ∀ x, ‖g x‖ ≤ c
def ZeroOfZeroOnBoxes : Prop :=
  ∀ r : ℕ, 2 ≤ r → ∀ n : Fin r → ℕ, (∀ k, 1 ≤ n k) →
    ∀ X : (k : Fin r) → Set (Fin (n k) → ℝ), (∀ k, MeasurableSet (X k)) →
      ∀ ν : SetFunctions.CountablyAdditiveFn ((k : Fin r) → X k),
        (∀ Δ : (k : Fin r) → SetFunctions.MeasurableSets (X k),
          ν.1 ⟨Set.univ.pi fun k => (Δ k).1, MeasurableSet.univ_pi fun k => (Δ k).2⟩ = 0) →
        ∀ Δ, ν.1 Δ = 0
def EqOfIntegralCompactSupportEq : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ m m' : Measure (Fin n → ℝ), IsFiniteMeasure m → IsFiniteMeasure m' →
    (∀ f ∈ Euclidean.compactSupportContinuous (Fin n → ℝ) ℝ, (∀ x, 0 ≤ f x) →
      ∫ x, f x ∂m = ∫ x, f x ∂m') →
    m = m'
def ZeroOfFourierLaplaceZero : Prop :=
  ∀ r : ℕ, 1 ≤ r → ∀ ν : SetFunctions.CountablyAdditiveFn (Set.Ici (0 : ℝ) × (Fin r → ℝ)),
    (∀ (k : ℕ) (v : Fin r → ℝ),
      BorelComplexMeasures.integralOf ν.1 (expLaplaceFourier k v) = 0) →
    ∀ Δ, ν.1 Δ = 0
def ZeroOfFourierZero : Prop :=
  ∀ r : ℕ, 1 ≤ r → ∀ ν : SetFunctions.CountablyAdditiveFn (Fin r → ℝ),
    (∀ v : Fin r → ℝ, BorelComplexMeasures.integralOf ν.1 (fourierExp v) = 0) →
    ∀ Δ, ν.1 Δ = 0
def ZeroOfLaplaceNatZero : Prop :=
  ∀ ν : SetFunctions.CountablyAdditiveFn (Set.Ici (0 : ℝ)),
    (∀ k : ℕ, BorelComplexMeasures.integralOf ν.1 (laplaceExp k) = 0) → ∀ Δ, ν.1 Δ = 0
def IntegralWellDefined : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ X : Set (Fin n → ℝ), MeasurableSet X →
    (∀ (ν : SetFunctions.MeasurableSets X → ℂ) (μ₁ μ₂ μ₃ μ₄ μ₁' μ₂' μ₃' μ₄' : Measure X)
      (g : X → ℂ),
      BorelComplexMeasures.IsJordanCombination ν μ₁ μ₂ μ₃ μ₄ →
      BorelComplexMeasures.IsJordanCombination ν μ₁' μ₂' μ₃' μ₄' → Measurable g →
      Integrable g μ₁ → Integrable g μ₂ → Integrable g μ₃ → Integrable g μ₄ →
      Integrable g μ₁' → Integrable g μ₂' → Integrable g μ₃' → Integrable g μ₄' →
      BorelComplexMeasures.combinedIntegral μ₁ μ₂ μ₃ μ₄ g =
        BorelComplexMeasures.combinedIntegral μ₁' μ₂' μ₃' μ₄' g) ∧
    ∀ (ν : SetFunctions.MeasurableSets X → ℂ) (g : X → ℂ) (c : ℂ),
      BorelComplexMeasures.IsIntegralOf ν g c → BorelComplexMeasures.integralOf ν g = c
structure IntegralRules {n n' : ℕ} {X : Set (Fin n → ℝ)} {X' : Set (Fin n' → ℝ)}
    (ν ν' : SetFunctions.CountablyAdditiveFn X) (c : ℂ) (g g' : X → ℂ) (κ : X → X')
    (hκ : Measurable κ) (g'' : X' → ℂ) : Prop where
  add_smul_isCountablyAdditive : SetFunctions.IsCountablyAdditive fun Δ => ν.1 Δ + c * ν'.1 Δ
  conj_isCountablyAdditive :
    SetFunctions.IsCountablyAdditive (BorelComplexMeasures.conjMeasure ν.1)
  densityMul_isCountablyAdditive :
    SetFunctions.IsCountablyAdditive (BorelComplexMeasures.densityMul g ν.1)
  pushforward_isCountablyAdditive :
    SetFunctions.IsCountablyAdditive (SetFunctions.pushforward κ hκ ν.1)
  integralOf_linear : ∀ a b : ℂ,
    BorelComplexMeasures.integralOf ν.1 (fun x => a * g x + b * g' x) =
      a * BorelComplexMeasures.integralOf ν.1 g + b * BorelComplexMeasures.integralOf ν.1 g'
  integralOf_indicator : ∀ Δ : SetFunctions.MeasurableSets X,
    BorelComplexMeasures.integralOf ν.1 ((Δ : Set X).indicator fun _ => (1 : ℂ)) = ν.1 Δ
  integralOf_add_smul :
    BorelComplexMeasures.integralOf (fun Δ => ν.1 Δ + c * ν'.1 Δ) g =
      BorelComplexMeasures.integralOf ν.1 g + c * BorelComplexMeasures.integralOf ν'.1 g
  integralOf_conj :
    BorelComplexMeasures.integralOf (BorelComplexMeasures.conjMeasure ν.1) g =
      conj (BorelComplexMeasures.integralOf ν.1 fun x => conj (g x))
  integralOf_densityMul :
    BorelComplexMeasures.integralOf (BorelComplexMeasures.densityMul g ν.1) g' =
      BorelComplexMeasures.integralOf ν.1 fun x => g' x * g x
  integralOf_pushforward :
    BorelComplexMeasures.integralOf (SetFunctions.pushforward κ hκ ν.1) g'' =
      BorelComplexMeasures.integralOf ν.1 (g'' ∘ κ)
def IntegralRulesBounded : Prop :=
  ∀ n n' : ℕ, 1 ≤ n → 1 ≤ n' → ∀ (X : Set (Fin n → ℝ)) (X' : Set (Fin n' → ℝ)),
    MeasurableSet X → MeasurableSet X' →
    ∀ (ν ν' : SetFunctions.CountablyAdditiveFn X) (c : ℂ) (g g' : X → ℂ) (κ : X → X')
      (hκ : Measurable κ) (g'' : X' → ℂ),
      IsBoundedMeasurable g → IsBoundedMeasurable g' → IsBoundedMeasurable g'' →
      IntegralRules ν ν' c g g' κ hκ g''
def LIntegralRules : Prop :=
  ∀ n n' : ℕ, 1 ≤ n → 1 ≤ n' → ∀ (X : Set (Fin n → ℝ)) (X' : Set (Fin n' → ℝ)),
    MeasurableSet X → MeasurableSet X' →
    ∀ (m : Measure X) (κ : X → X') (u : X → ℝ≥0), IsFiniteMeasure m → Measurable κ →
      Measurable u → (∃ c : ℝ≥0, ∀ x, u x ≤ c) →
      (∀ f : X → ℝ≥0, Measurable f →
        ∫⁻ x, (f x : ℝ≥0∞) ∂(m.withDensity fun x => (u x : ℝ≥0∞)) =
          ∫⁻ x, (f x : ℝ≥0∞) * (u x : ℝ≥0∞) ∂m) ∧
      ∀ f'' : X' → ℝ≥0, Measurable f'' →
        ∫⁻ x, (f'' x : ℝ≥0∞) ∂(Measure.map κ m) = ∫⁻ x, (f'' (κ x) : ℝ≥0∞) ∂m
def UniquenessAndIntegral : Prop :=
  ZeroOfZeroOnBoxes ∧
  EqOfIntegralCompactSupportEq ∧
  ZeroOfFourierLaplaceZero ∧
  (ZeroOfFourierZero ∧ ZeroOfLaplaceNatZero) ∧
  IntegralWellDefined ∧
  IntegralRulesBounded ∧
  LIntegralRules
end YangMills.Construction.MeasureUniqueness
end
