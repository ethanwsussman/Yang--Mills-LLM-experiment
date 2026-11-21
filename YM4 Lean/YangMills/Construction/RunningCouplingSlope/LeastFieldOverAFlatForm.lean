import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.RunningCouplingSlope.FormsOfTheChainAtTheFlatField
import YangMills.Construction.RunningCouplingSlope.TotalsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields
open YangMills.Construction.Conventions YangMills.Construction.FlatLinearization
open YangMills.Construction.SlopeCoefficient
namespace RunningCouplingSlope
def MinimizerOverFlatKernel : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, IsAdmissibleBlockingFactor L → ∀ (t : ℕ) (h : BondKernel)
    (P : (n : ℕ) → TorusBond (n * L) → TorusBond n → ℝ),
    (∀ᶠ m in Filter.atTop, HasHessianAtTrivial (minimalActionTotal a L t) (h m)) →
    (∀ᶠ n in Filter.atTop, ∀ [NeZero n] [NeZero L],
      IsMinimizerFamily a L (h (n * L)) (P n) ∧ IsPositiveOnTreeGauge (n := n) a L (h (n * L))) →
    (∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∀ᶠ n in Filter.atTop,
      minimizerOnFinerTorus a ρ L t n (trivialField n) = trivialField (n * L) ∧
      (∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (b : TorusBond (n * L)),
        ContDiffAt ℝ 2 (fun σ : Fin k → ℝ =>
          ((minimizerOnFinerTorus a ρ L t n (perturb c X σ (trivialField n)) b.1 b.2 : UnitQuaternion) : ℍ[ℝ])) 0) ∧
      ∀ (b : TorusBond (n * L)) (c : TorusBond n) (X : imaginaryQuaternions),
        HasDerivAt (fun s : ℝ =>
          ((minimizerOnFinerTorus a ρ L t n (perturb ![c] ![X] ![s] (trivialField n)) b.1 b.2 : UnitQuaternion) : ℍ[ℝ]))
          (P n b c • (X : ℍ[ℝ])) 0) ∧
    ∀ᶠ n in Filter.atTop, HasHessianAtTrivial (minimalActionTotal a L (t + 1)) (renormalizedKernel a L h P n)
end RunningCouplingSlope
end YangMills.Construction
end
