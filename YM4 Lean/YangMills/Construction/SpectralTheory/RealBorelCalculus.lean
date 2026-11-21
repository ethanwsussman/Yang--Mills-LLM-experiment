import YangMills.Construction.HilbertSpace.SpectralMeasuresSelfAdjoint
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction.SpectralTheory
namespace SpectralMeasure
variable {n : ℕ} [NeZero n] {ℋ : Type*} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
  [CompleteSpace ℋ]
def dyadic (j : ℕ) (k : ℤ) : ℝ := (k : ℝ) * 2 ^ (-(j : ℤ))
def dyadicLevelSet (g : (Fin n → ℝ) → ℝ) (hg : Measurable g) (j : ℕ) (k : ℤ) : BorelSubset n :=
  ⟨{y | dyadic j k ≤ g y ∧ g y < dyadic j (k + 1)},
    (measurableSet_le measurable_const hg).inter (measurableSet_lt hg measurable_const)⟩
def realDomain (E : SpectralMeasure n ℋ) (g : (Fin n → ℝ) → ℝ) : Set ℋ :=
  {ψ | E.lintegral ψ (fun y => ENNReal.ofReal (g y ^ 2)) < ⊤}
def dyadicPartialSum (E : SpectralMeasure n ℋ) (g : (Fin n → ℝ) → ℝ) (hg : Measurable g)
    (j : ℕ) (ψ : ℋ) (N : ℕ) : ℋ :=
  ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ((dyadic j k : ℝ) : ℂ) • E (dyadicLevelSet g hg j k) ψ
def dyadicSum (E : SpectralMeasure n ℋ) (g : (Fin n → ℝ) → ℝ) (hg : Measurable g)
    (j : ℕ) (ψ : ℋ) : ℋ :=
  limUnder atTop (E.dyadicPartialSum g hg j ψ)
def realIntegralApply (E : SpectralMeasure n ℋ) (g : (Fin n → ℝ) → ℝ) (hg : Measurable g)
    (ψ : ℋ) : ℋ :=
  limUnder atTop fun j => E.dyadicSum g hg j ψ
def IsRealIntegralOp (E : SpectralMeasure n ℋ) (g : (Fin n → ℝ) → ℝ)
    (hg : Measurable g) (T : UnboundedOp ℋ) : Prop :=
  (T.domain : Set ℋ) = E.realDomain g ∧ ∀ ψ : T.domain, T ψ = E.realIntegralApply g hg ψ
def nullOpenUnion (E : SpectralMeasure n ℋ) : Set (Fin n → ℝ) :=
  ⋃₀ {U | ∃ hU : IsOpen U, E.IsNull ⟨U, hU.measurableSet⟩}
end SpectralMeasure
def RealBorelCalculus : Prop :=
  ∀ (ℋ : Type) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] (n : ℕ) [NeZero n]
    (E : SpectralMeasure n ℋ) (g : (Fin n → ℝ) → ℝ) (hg : Measurable g),
    (∀ φ ∈ E.realDomain g, ∀ ψ ∈ E.realDomain g, ∀ c : ℂ,
      E.realIntegralApply g hg (φ + ψ) = E.realIntegralApply g hg φ + E.realIntegralApply g hg ψ ∧
      E.realIntegralApply g hg (c • ψ) = c • E.realIntegralApply g hg ψ) ∧
    ∀ ψ ∈ E.realDomain g,
      ⟪ψ, E.realIntegralApply g hg ψ⟫_ℂ = ((E.integral ψ g : ℝ) : ℂ)
end YangMills.Construction.SpectralTheory
