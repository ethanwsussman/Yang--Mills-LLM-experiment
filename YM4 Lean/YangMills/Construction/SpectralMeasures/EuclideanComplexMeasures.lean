import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal InnerProductSpace
noncomputable section
namespace YangMills.Construction
namespace EuclideanBorel
abbrev Space (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)
abbrev BorelSubset (n : ℕ) : Type := Subtype (MeasurableSet : Set (Space n) → Prop)
def IsBoundedMeasurableFn {n : ℕ} (f : Space n → ℂ) : Prop :=
  Measurable f ∧ ∃ C : ℝ, ∀ y, ‖f y‖ ≤ C
structure MeasureCombination (n : ℕ) where
  numTerms : ℕ
  one_le_numTerms : 1 ≤ numTerms
  coeff : Fin numTerms → ℂ
  component : Fin numTerms → Measure (Space n)
  isFinite : ∀ j, IsFiniteMeasure (component j)
def MeasureCombination.toSetFunction {n : ℕ} (p : MeasureCombination n) : BorelSubset n → ℂ :=
  fun Δ => ∑ j, p.coeff j * (((p.component j).real Δ.1 : ℝ) : ℂ)
def MeasureCombination.integral {n : ℕ} (p : MeasureCombination n) (f : Space n → ℂ) : ℂ :=
  ∑ j, p.coeff j * ∫ y, f y ∂(p.component j)
def IsFiniteCombinationMeasure {n : ℕ} (ν : BorelSubset n → ℂ) : Prop :=
  ∃ p : MeasureCombination n, p.toSetFunction = ν
open Classical in
def complexIntegral {n : ℕ} (ν : BorelSubset n → ℂ) (f : Space n → ℂ) : ℂ :=
  if h : IsFiniteCombinationMeasure ν then (Classical.choose h).integral f else 0
def weightedBy {n : ℕ} (g : Space n → ℂ) (ν : BorelSubset n → ℂ) : BorelSubset n → ℂ :=
  fun Δ => complexIntegral ν (Δ.1.indicator g)
def IsSupportedOn {n : ℕ} (ν : BorelSubset n → ℂ) (X : BorelSubset n) : Prop :=
  ∀ Δ : BorelSubset n, Δ.1 ⊆ X.1ᶜ → ν Δ = 0
def IsZeroMeasure {n : ℕ} (ν : BorelSubset n → ℂ) : Prop :=
  ∀ Δ : BorelSubset n, ν Δ = 0
def IsPositiveMeasure {n : ℕ} (m : BorelSubset n → ℂ) : Prop :=
  ∃ μ : Measure (Space n), ∀ Δ : BorelSubset n, μ Δ.1 ≠ ∞ ∧ m Δ = ((μ.real Δ.1 : ℝ) : ℂ)
open Classical in
def toMeasure {n : ℕ} (m : BorelSubset n → ℂ) : Measure (Space n) :=
  if h : IsPositiveMeasure m then Classical.choose h else 0
theorem toMeasure_spec {n : ℕ} {m : BorelSubset n → ℂ} (hm : IsPositiveMeasure m)
    (Δ : BorelSubset n) :
    toMeasure m Δ.1 ≠ ∞ ∧ m Δ = (((toMeasure m).real Δ.1 : ℝ) : ℂ) := by
  rw [toMeasure, dif_pos hm]
  exact Classical.choose_spec hm Δ
section Operators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def IsOrthoProjection (P : H →L[ℂ] H) : Prop :=
  P * P = P ∧ ∀ φ ψ : H, ⟪φ, P ψ⟫_ℂ = ⟪P φ, ψ⟫_ℂ
variable {n n' : ℕ}
def crossForm (E : BorelSubset n → H →L[ℂ] H) (φ ψ : H) : BorelSubset n → ℂ :=
  fun Δ => ⟪φ, E Δ ψ⟫_ℂ
def diagonalForm (E : BorelSubset n → H →L[ℂ] H) (ψ : H) : BorelSubset n → ℂ :=
  fun Δ => ⟪ψ, E Δ ψ⟫_ℂ
structure IsPVM (E : BorelSubset n → H →L[ℂ] H) : Prop where
  isOrthoProjection : ∀ Δ, IsOrthoProjection (E Δ)
  map_top : E ⊤ = 1
  map_inter : ∀ Δ Δ', E (Δ ∩ Δ') = E Δ * E Δ'
  isPositiveMeasure : ∀ ψ, IsPositiveMeasure (diagonalForm E ψ)
def diagonalMeasure (E : BorelSubset n → H →L[ℂ] H) (ψ : H) : Measure (Space n) :=
  toMeasure (diagonalForm E ψ)
def IsNull (E : BorelSubset n → H →L[ℂ] H) (Δ : BorelSubset n) : Prop :=
  E Δ = 0
def IsSupportedOnPVM (E : BorelSubset n → H →L[ℂ] H) (X : BorelSubset n) : Prop :=
  IsNull E Xᶜ
def sqIntegrableDomain (E : BorelSubset n → H →L[ℂ] H) (f : Space n → ℂ) : Set H :=
  {ψ | ∫⁻ y, ‖f y‖ₑ ^ 2 ∂(diagonalMeasure E ψ) < ∞}
def cutoff (f : Space n → ℂ) (k : ℕ) : Space n → ℂ :=
  {y | ‖f y‖ ≤ k}.indicator f
def pushforward (E : BorelSubset n → H →L[ℂ] H) (κ : Space n → Space n') (hκ : Measurable κ) :
    BorelSubset n' → H →L[ℂ] H :=
  fun Δ' => E ⟨κ ⁻¹' Δ'.1, hκ Δ'.2⟩
def unitaryConj (U : H ≃ₗᵢ[ℂ] H) (E : BorelSubset n → H →L[ℂ] H) : BorelSubset n → H →L[ℂ] H :=
  fun Δ => (U.toContinuousLinearEquiv : H →L[ℂ] H) * E Δ *
    (U.symm.toContinuousLinearEquiv : H →L[ℂ] H)
end Operators
def appendCoords (n₁ n₂ : ℕ) (p : Space n₁ × Space n₂) : Space (n₁ + n₂) :=
  WithLp.toLp 2 (Fin.append p.1.ofLp p.2.ofLp)
end EuclideanBorel
end YangMills.Construction
