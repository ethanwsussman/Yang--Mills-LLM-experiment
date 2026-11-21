import YangMills.Construction.ComplexAnalysis.PartialDerivativesAndLogarithm
import Mathlib
open Set
noncomputable section
namespace YangMills.Construction.ComplexVariables.HolomorphicFacts
open YangMills.Construction.Coordinates
open YangMills.Construction.PowerSeries
variable {n : ℕ}
def PartialDerivProperties (U : Set (ComplexCoordinates n)) (F : ComplexCoordinates n → ℂ) : Prop :=
  (∀ j, HasPartialDeriv U F j ∧ IsHolomorphicScalar U (partialDeriv j F)) ∧
  (∀ j l, EqOn (partialDeriv j (partialDeriv l F))
    (partialDeriv l (partialDeriv j F)) U) ∧
  (∀ J : Finset (Fin n), HasPartialOverFinset U J F ∧ IsHolomorphicScalar U (partialOverFinset J F)) ∧
  (∀ α : MultiIndex n,
    HasPartialOfIndex U α F ∧ IsHolomorphicScalar U (partialOfIndex α F)) ∧
  (∀ (J : Finset (Fin n)) (l : List (Fin n)), l.Perm J.sort →
    HasIteratedPartials U l F ∧ EqOn (iteratedPartials l F) (partialOverFinset J F) U) ∧
  (∀ (α : MultiIndex n) (l : List (Fin n)), l.Perm (multiIndexSteps α) →
    HasIteratedPartials U l F ∧ EqOn (iteratedPartials l F) (partialOfIndex α F) U) ∧
  (∀ (J : Finset (Fin n)) (s : Fin n), s ∉ J →
    EqOn (partialDeriv s (partialOverFinset J F)) (partialOverFinset (insert s J) F) U) ∧
  (∀ U' : Set (ComplexCoordinates n), IsOpen U' → U' ⊆ U →
    ∀ G : ComplexCoordinates n → ℂ, EqOn G F U' →
      IsHolomorphicScalar U' G ∧
        ∀ J : Finset (Fin n), EqOn (partialOverFinset J G) (partialOverFinset J F) U')
def AlgebraRules (U : Set (ComplexCoordinates n)) : Prop :=
  (∀ c : ℂ, IsHolomorphicScalar U (fun _ => c) ∧
    ∀ s, EqOn (partialDeriv s fun _ => c) (fun _ => 0) U) ∧
  (∀ l : Fin n, IsHolomorphicScalar U fun z => z l) ∧
  (∀ s : Fin n, EqOn (partialDeriv s fun z => z s) (fun _ => 1) U) ∧
  (∀ s l : Fin n, l ≠ s → EqOn (partialDeriv s fun z => z l) (fun _ => 0) U) ∧
  (∀ F F' : ComplexCoordinates n → ℂ, IsHolomorphicScalar U F → IsHolomorphicScalar U F' → ∀ a a' : ℂ,
    IsHolomorphicScalar U (fun z => a * F z + a' * F' z) ∧
    IsHolomorphicScalar U (fun z => F z * F' z) ∧
    ∀ s, EqOn (partialDeriv s fun z => a * F z + a' * F' z)
        (fun z => a * partialDeriv s F z + a' * partialDeriv s F' z) U ∧
      EqOn (partialDeriv s fun z => F z * F' z)
        (fun z => partialDeriv s F z * F' z + F z * partialDeriv s F' z) U) ∧
  (∀ k : ℕ, 1 ≤ k → ∀ F : Fin k → ComplexCoordinates n → ℂ, (∀ i, IsHolomorphicScalar U (F i)) →
    ∀ s, EqOn (partialDeriv s fun z => ∏ i, F i z)
      (fun z => ∑ i, partialDeriv s (F i) z * ∏ i' ∈ Finset.univ.erase i, F i' z) U) ∧
  (∀ p : MvPolynomial (Fin n) ℂ, IsEntireFun fun z => MvPolynomial.eval z p)
def ChainRuleHolds (U : Set (ComplexCoordinates n)) : Prop :=
  ∀ (W : Set ℂ) (V : ComplexCoordinates n → ℂ) (η : ℂ → ℂ), IsOpen W → IsHolomorphicScalar U V →
    MapsTo V U W → DifferentiableOn ℂ η W →
    IsHolomorphicScalar U (η ∘ V) ∧
      ∀ s, EqOn (partialDeriv s (η ∘ V))
        (fun z => deriv η (V z) * partialDeriv s V z) U
def powerSeriesSum (a : MultiIndex n → ℂ) : ComplexCoordinates n → ℂ :=
  fun z => indexSum fun α => a α * MultiIndex.monomial z α
def TermwiseDifferentiable (n : ℕ) : Prop :=
  ∀ a : MultiIndex n → ℂ,
    (∀ z : ComplexCoordinates n, Summable fun α => ‖a α‖ * absMonomial z α) →
    IsEntireFun (powerSeriesSum a) ∧
    (∀ (j : Fin n) (z : ComplexCoordinates n),
      partialDeriv j (powerSeriesSum a) z =
          indexSum (fun β : MultiIndex n =>
            ((β j : ℂ) + 1) * a (β + singleIndex j) * MultiIndex.monomial z β) ∧
        Summable fun β : MultiIndex n =>
          ((β j : ℝ) + 1) * ‖a (β + singleIndex j)‖ * absMonomial z β) ∧
    ∀ α : MultiIndex n,
      partialOfIndex α (powerSeriesSum a) 0 = (MultiIndex.factorial α : ℂ) * a α
def LogExpProperties : Prop :=
  IsOpen nonpositiveRayComplement ∧
  DifferentiableOn ℂ logPrincipal nonpositiveRayComplement ∧
  (∀ w ∈ nonpositiveRayComplement, deriv logPrincipal w = 1 / w) ∧
  (∀ w ∈ nonpositiveRayComplement, Complex.exp (logPrincipal w) = w) ∧
  logPrincipal 1 = 0 ∧
  (∀ w : ℝ, 0 < w → logPrincipal (w : ℂ) = (Real.log w : ℂ)) ∧
  {w : ℂ | ‖w - 1‖ < 1} ⊆ nonpositiveRayComplement ∧
  Differentiable ℂ Complex.exp ∧
  deriv Complex.exp = Complex.exp ∧
  ∀ w : ℂ, Complex.exp w ≠ 0
def ConnectedOpenProperties (n : ℕ) : Prop :=
  (∀ O : Set (ComplexCoordinates n), IsOpen O → ∀ a ∈ O,
    IsOpen (connectedComponentIn O a) ∧ IsConnected (connectedComponentIn O a)) ∧
  (∀ O : Set (ComplexCoordinates n), IsOpen O → IsConnected O →
    (∀ F : ComplexCoordinates n → ℂ, IsHolomorphicScalar O F →
      (∀ j, EqOn (partialDeriv j F) (fun _ => 0) O) → ∃ c : ℂ, ∀ z ∈ O, F z = c) ∧
    (∀ f : ComplexCoordinates n → ℂ, ContinuousOn f O → (∀ z ∈ O, f z ∈ twoPiIMultiples) →
      ∃ c : ℂ, ∀ z ∈ O, f z = c)) ∧
  ∀ w : ℂ, Complex.exp w = 1 → w ∈ twoPiIMultiples
def StandardFacts : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ U : Set (ComplexCoordinates n), IsOpen U →
    (∀ F : ComplexCoordinates n → ℂ, IsHolomorphicScalar U F → PartialDerivProperties U F) ∧
    AlgebraRules U ∧
    ChainRuleHolds U ∧
    TermwiseDifferentiable n ∧
    LogExpProperties ∧
    ConnectedOpenProperties n
end YangMills.Construction.ComplexVariables.HolomorphicFacts
