import YangMills.Construction.Coordinates.HolomorphyInCoordinates
import Mathlib
open Filter Set
open scoped ContDiff
noncomputable section
namespace YangMills.Construction
namespace Coordinates
namespace ComplexCoordinates
namespace PowerSeriesHolomorphy
variable {N N' : ℕ}
def openPolydisk (a : ComplexCoordinates N) (ρ : ℝ) : Set (ComplexCoordinates N) :=
  {z | ∀ j, ‖z j - a j‖ < ρ}
def closedPolydisk (a : ComplexCoordinates N) (ρ : ℝ) : Set (ComplexCoordinates N) :=
  {z | ∀ j, ‖z j - a j‖ ≤ ρ}
def monomialTerm (c : (Fin N → ℕ) → ComplexCoordinates N') (a z : ComplexCoordinates N)
    (m : Fin N → ℕ) : ComplexCoordinates N' :=
  (∏ j, (z j - a j) ^ m j) • c m
def HasPowerSeriesSumOn (f : ComplexCoordinates N → ComplexCoordinates N')
    (a : ComplexCoordinates N) (ρ : ℝ) : Prop :=
  ∃ c : (Fin N → ℕ) → ComplexCoordinates N',
    (∀ z ∈ openPolydisk a ρ, HasSum (monomialTerm c a z) (f z)) ∧
    ∀ ρ' < ρ,
      (∀ z ∈ closedPolydisk a ρ', Summable fun m => ‖monomialTerm c a z m‖) ∧
      TendstoUniformlyOn (fun (s : Finset (Fin N → ℕ)) z => ∑ m ∈ s, monomialTerm c a z m) f atTop
        (closedPolydisk a ρ')
def IsPolynomialInComponents {n n' : ℕ} (s : Fin n → Component) (s' : Fin n' → Component)
    (f : ComponentProduct s → ComponentProduct s') : Prop :=
  ∃ P : Fin (productDim s') → MvPolynomial (Fin (productDim s)) ℂ,
    ∀ x k, productEquiv s' (f x) k = MvPolynomial.eval (productEquiv s x) (P k)
def Properties : Prop :=
  (∀ (N : ℕ) (O : Set (ComplexCoordinates N)), IsOpen O →
    (∀ (N' : ℕ) (f : ComplexCoordinates N → ComplexCoordinates N'), IsHolomorphicIn O f →
      (∀ a ∈ O, ∀ ρ > 0, closedPolydisk a ρ ⊆ O → HasPowerSeriesSumOn f a ρ) ∧
      ContDiffOn ℝ ∞ f O ∧
      (∀ b ∈ O, ∃ L : ComplexCoordinates N →L[ℂ] ComplexCoordinates N',
        HasFDerivAt f (L.restrictScalars ℝ) b) ∧
      (∀ (N'' : ℕ) (O' : Set (ComplexCoordinates N''))
          (g : ComplexCoordinates N'' → ComplexCoordinates N),
        IsHolomorphicIn O' g → MapsTo g O' O → IsHolomorphicIn O' (f ∘ g)) ∧
      IsRealAnalyticIn (O ∩ realLocus N) f) ∧
    (∀ (N' : ℕ) (F : ℕ → ComplexCoordinates N → ComplexCoordinates N')
        (f : ComplexCoordinates N → ComplexCoordinates N'),
      (∀ m, IsHolomorphicIn O (F m)) → TendstoUniformlyOn F f atTop O → IsHolomorphicIn O f)) ∧
  (∀ (n n' : ℕ) (s : Fin n → Component) (s' : Fin n' → Component)
      (f : ComponentProduct s → ComponentProduct s'),
    IsPolynomialInComponents s s' f →
      IsHolomorphicVia (productEquiv s) (productEquiv s') univ f) ∧
  IsHolomorphicVia matrixPairEquiv matrixEquiv univ
    (fun p : Matrices.ComplexMatrix2 × Matrices.ComplexMatrix2 => p.1 * p.2) ∧
  IsHolomorphicVia matrixEquiv matrixEquiv {X : Matrices.ComplexMatrix2 | IsUnit X}
    (fun X => X⁻¹) ∧
  IsHolomorphicVia matrixEquiv matrixEquiv univ Matrices.ComplexMatrix2.matExp ∧
  IsHolomorphicVia matrixEquiv matrixEquiv Matrices.ComplexMatrix2.logBall
    Matrices.ComplexMatrix2.logSeries
end PowerSeriesHolomorphy
end ComplexCoordinates
end Coordinates
end YangMills.Construction
