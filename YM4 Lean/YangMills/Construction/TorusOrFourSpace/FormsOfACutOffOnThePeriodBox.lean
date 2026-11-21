import YangMills.Construction.TorusOrFourSpace.ComplexExtensionOfABoundedForm
import YangMills.Construction.TorusOrFourSpace.PeriodBoxCharactersAndCoefficients
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.PeriodCell
open Kind.Tuple
def CutoffFormsExist : Prop :=
  ∀ (D : Params) (n : ℕ+) (ρ c : ℝ), 0 < ρ → 0 ≤ c →
    ∀ O : Fin (n : ℕ) → Set (Kind.euclidean.Pt D),
      (∀ i, Kind.IsOpenQ D Kind.euclidean (O i)) →
      (∀ i, ∀ u ∈ O i, TorusMetric.euclidNormVec u ≤ ρ) →
    ∀ Bc : (Fin (n : ℕ) → Kind.euclidean.Pt D → ℂ) → ℂ,
      IsBoundedComplexMultiform D Kind.euclidean O c Bc →
    ∃ Tc : (Fin (n : ℕ) → Kind.euclidean.Pt D → ℝ) →
        (Kind.euclidean.Tuple D n → ℂ) → ℂ,
      ∀ χ, IsCutoffFamily D Kind.euclidean O χ →
        IsComplexLinearForm (fun F : cellTestFns D n (4 * ρ) => Tc χ F.1) ∧
        (∀ F ∈ cellTestFns D n (4 * ρ),
          ENNReal.ofReal ‖Tc χ F‖ ≤
            ENNReal.ofReal (2 ^ (n : ℕ) * c * cutoffBound n ρ) *
              (∏ i, c1NormSingleReal D Kind.euclidean (χ i)) *
                cNorm D Kind.euclidean (5 * (n : ℕ) + 1) F) ∧
        ∀ h : Fin (n : ℕ) → Kind.euclidean.Pt D → ℂ,
          (∀ i, h i ∈ singleTestFns D Kind.euclidean (cell (4 * ρ))) →
            Tc χ (tensorProd D Kind.euclidean h) = Bc fun i y => (χ i y : ℂ) * h i y
end YangMills.Construction.PeriodicSpace.PeriodCell
