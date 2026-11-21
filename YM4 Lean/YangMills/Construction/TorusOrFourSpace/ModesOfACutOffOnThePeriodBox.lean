import YangMills.Construction.TorusOrFourSpace.CutOffsOnAProductOfOpenSets
import YangMills.Construction.TorusOrFourSpace.FunctionsOfClassC1SupportsAndNorms
import YangMills.Construction.TorusOrFourSpace.PeriodBoxCharactersAndCoefficients
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.PeriodCell
open Kind.Tuple
def cutoffMode (D : Params) (P : ℝ) (χ : Kind.euclidean.Pt D → ℝ) (κ : Fin 4 → ℤ) :
    Kind.euclidean.Pt D → ℂ :=
  fun y => (χ y : ℂ) * fourierCharR4 P κ y
def CutoffModeBounds : Prop :=
  ∀ (D : Params) (ρ : ℝ), 0 < ρ →
    ∀ O : Set (Kind.euclidean.Pt D), Kind.IsOpenQ D Kind.euclidean O → O ⊆ cell (4 * ρ) →
      singleTestFns D Kind.euclidean O ⊆
        singleTestFns D Kind.euclidean (cell (4 * ρ)) ∧
      (∀ κ : Fin 4 → ℤ,
        IsSmoothT D Kind.euclidean
          (ofSingle D Kind.euclidean (fourierCharR4 (4 * ρ) κ))) ∧
      ∀ χ : Kind.euclidean.Pt D → ℝ,
        (fun y => (χ y : ℂ)) ∈ singleTestFns D Kind.euclidean O →
        (∀ G : Kind.euclidean.Pt D → ℂ,
          IsSmoothT D Kind.euclidean (ofSingle D Kind.euclidean G) →
            (fun y => (χ y : ℂ) * G y) ∈ singleTestFns D Kind.euclidean O ∧
            Kind.supportQ D Kind.euclidean (fun y => (χ y : ℂ) * G y) ⊆
              Kind.supportQ D Kind.euclidean χ) ∧
        ∀ κ : Fin 4 → ℤ,
          c1NormSingle D Kind.euclidean (cutoffMode D (4 * ρ) χ κ) ≤
            c1NormSingleReal D Kind.euclidean χ *
              ENNReal.ofReal (1 + intVecNorm κ / cutoffScale ρ)
end YangMills.Construction.PeriodicSpace.PeriodCell
