import YangMills.Construction.TotalDensitiesGiveASystem.FirstExitPathDefs
import YangMills.Construction.TotalDensitiesGiveASystem.LawsOfTheTopStatement
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.TotalDensitySystem
def IsCouplingAtScale (p : TorusLumps.StepParameters) {IsPair : ℕ+ → ℝ → Prop}
    (Q : SystemsWithFiveBounds.PairSequence p.side IsPair) (d x : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ᶠ j in atTop, ∃ k : ℕ, k ≤ (Q.cutoff j : ℕ) ∧
    1 ≤ d / (p.side : ℝ) ^ ((k : ℤ) - ((Q.cutoff j : ℕ) : ℤ)) ∧
    d / (p.side : ℝ) ^ ((k : ℤ) - ((Q.cutoff j : ℕ) : ℤ)) ≤ TotalDensityFlow.coupling p (Q.coupling j) k ∧
    |TotalDensityFlow.coupling p (Q.coupling j) k - x| ≤ ε
namespace ShortDistanceLawAtFewPoints
def Statement : Prop :=
  TotalDensities.HoldsAtAdmissibleParameters fun T y => TotalDensities.ForSmallCoupling fun g =>
    ∀ (Q : SystemsWithFiveBounds.PairSequence (T.stepParameters y).side
        (IsFirstPassagePair (T.stepParameters y) (2 * T.B) g)) (S : LimitTheorem.CumulantFamily),
      Q.Defines S → ∀ (n : ℕ) [NeZero n] (hn : 2 ≤ n), n ≤ 8 → ∀ X : TestSpaces.SepTupleOfCard n,
        ∃ (δ C : ℝ) (i₁ : ℕ) (x : ℕ → ℝ), 0 < δ ∧
          (∀ i, i₁ ≤ i → IsCouplingAtScale (T.stepParameters y) Q (δ / 2 ^ i) (x i)) ∧
          (∀ i, i₁ ≤ i → ∀ Y : TestSpaces.SepTupleOfCard n, Y.1 = TotalDensities.dyadicRescale i X.1 →
            |x i ^ n * S n hn Y - TotalDensities.shortDistanceLimit X.1| ≤ C * x i ^ (-(1 / 100) : ℝ)) ∧
          ∀ A : SeparatedTuples.DecompositionData, A.IsCanonical (LimitTheorem.centredOf S) → ∀ᵐ ξ ∂A.law,
            ∃ i₀ : ℕ, ∀ i, i₀ ≤ i → ∀ Y : TestSpaces.SepTupleOfCard n, Y.1 = TotalDensities.dyadicRescale i X.1 →
              |x i ^ n * LimitTheorem.connectedFn (A.comp ξ) Y - TotalDensities.shortDistanceLimit X.1|
                ≤ C * x i ^ (-(1 / 100) : ℝ)
end ShortDistanceLawAtFewPoints
end YangMills.Construction.TotalDensitySystem
end
