import YangMills.Construction.SpectralTheory.FunctionsOfSelfAdjointOperators
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.CoordOps
open BorelSpectral HilbertSpaceBasics SpectralTheorem SelfAdjointFunctions
variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def HasCoordOps (E : SpectralMeasure (FullSpace n) H)
    (A : Fin n → UnboundedOp H) : Prop :=
  ∀ j, IsSpectralIntegralOf (A j) E fun x => ((x.1 j : ℝ) : ℂ)
def coordPair (i k : Fin n) (x : FullSpace n) : FullSpace 2 := ⟨![x.1 i, x.1 k], mem_univ _⟩
theorem measurable_coordPair (i k : Fin n) : Measurable (coordPair i k) := by
  refine Measurable.subtype_mk (measurable_pi_iff.mpr fun j => ?_)
  fin_cases j
  · exact (measurable_pi_apply i).comp measurable_subtype_coe
  · exact (measurable_pi_apply k).comp measurable_subtype_coe
def pairPushforward (E : SpectralMeasure (FullSpace n) H) (i k : Fin n) :
    SpectralMeasure (FullSpace 2) H :=
  E.pushforward (by norm_num) MeasurableSet.univ (coordPair i k) (measurable_coordPair i k)
def CoordOpsTheorem : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (n : ℕ)
    (E : SpectralMeasure (FullSpace n) H),
    (∀ i, IsSelfAdjointOp (coordOperator E i) ∧
      spectralMeasure (coordOperator E i) = E.coordMarginal i ∧
      ∀ f : ℝ → ℂ, Measurable f →
        IsSpectralIntegralOf (fnCalc (coordOperator E i) f) E fun x => f (x.1 i)) ∧
    PairwiseStronglyCommute (coordOperator E) ∧
    HasCoordOps E (coordOperator E) ∧
    (∀ E' : SpectralMeasure (FullSpace n) H,
      HasCoordOps E' (coordOperator E) → E' = E) ∧
    ∀ i k : Fin n, i ≠ k →
      HasCoordOps (pairPushforward E i k) ![coordOperator E i, coordOperator E k] ∧
      (∀ F : SpectralMeasure (FullSpace 2) H,
        HasCoordOps F ![coordOperator E i, coordOperator E k] →
          F = pairPushforward E i k) ∧
      E (setLtAbs i k) = pairPushforward E i k (setLtAbs 0 1) ∧
      ∀ B B' : H →L[ℂ] H, coordOperator E i = ofBounded B →
        coordOperator E k = ofBounded B' →
          ∃ C : H →L[ℂ] H, absOp (coordOperator E k) = ofBounded C ∧ IsSelfAdjoint C ∧
            (E (setLtAbs i k) = 0 ↔ IsPositiveOp (B - C))
end YangMills.Construction.CoordOps
