import YangMills.Construction.SpectralMeasures.BorelFunctionOperators
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanBorel
section Operators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {n : ℕ}
def expChar (v : Space n) : Space n → ℂ :=
  fun x => Complex.exp (Complex.I * ((inner ℝ v x : ℝ) : ℂ))
def SpectralIntegralIs (E : BorelSubset n → H →L[ℂ] H) (f : Space n → ℂ) (B : H → H) : Prop :=
  sqIntegrableDomain E f = Set.univ ∧
    ∀ v : sqIntegrableDomain E f, spectralIntegral E f v = B v.1
def IsSpectralMeasureOf (U : Space n → H ≃ₗᵢ[ℂ] H)
    (E : BorelSubset n → H →L[ℂ] H) : Prop :=
  IsPVM E ∧ ∀ v, SpectralIntegralIs E (expChar v) (U v)
def spectralMeasureOf (U : Space n → H ≃ₗᵢ[ℂ] H) : BorelSubset n → H →L[ℂ] H :=
  Classical.epsilon (IsSpectralMeasureOf U)
omit [CompleteSpace H] in
theorem spectralMeasureOf_spec {U : Space n → H ≃ₗᵢ[ℂ] H}
    (h : ∃ E, IsSpectralMeasureOf U E) :
    IsSpectralMeasureOf U (spectralMeasureOf U) :=
  Classical.epsilon_spec h
def IsOpenNull (E : BorelSubset n → H →L[ℂ] H) (W : Set (Space n)) : Prop :=
  ∃ h : IsOpen W, IsNull E ⟨W, h.measurableSet⟩
def IsMaximalOpenNull (E : BorelSubset n → H →L[ℂ] H) (W : Set (Space n)) : Prop :=
  IsOpenNull E W ∧ ∀ W', IsOpenNull E W' → W' ⊆ W
def maxOpenNull (E : BorelSubset n → H →L[ℂ] H) : Set (Space n) :=
  Classical.epsilon (IsMaximalOpenNull E)
def pvmSupport (E : BorelSubset n → H →L[ℂ] H) : Set (Space n) :=
  (maxOpenNull E)ᶜ
def jointSpectrum (E : BorelSubset n → H →L[ℂ] H) : Set (Space n) :=
  pvmSupport E
end Operators
def coordLtAbs {n : ℕ} (i k : Fin n) : BorelSubset n :=
  ⟨{x | x i < |x k|}, (isOpen_lt (by fun_prop) (by fun_prop)).measurableSet⟩
def CoordOpGeAbs {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {n : ℕ} (E : BorelSubset n → H →L[ℂ] H)
    (i k : Fin n) : Prop :=
  E (coordLtAbs i k) = 0
section Momentum
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def momentumExpChar (a : Space 3) : Space (1 + 3) → ℂ :=
  fun x => Complex.exp (Complex.I * ((inner ℝ a (momentumVec x) : ℝ) : ℂ))
def expMomentumOp (E : BorelSubset (1 + 3) → H →L[ℂ] H) (a : Space 3) :
    sqIntegrableDomain E (momentumExpChar a) → H :=
  spectralIntegral E (momentumExpChar a)
end Momentum
end YangMills.Construction.EuclideanBorel
