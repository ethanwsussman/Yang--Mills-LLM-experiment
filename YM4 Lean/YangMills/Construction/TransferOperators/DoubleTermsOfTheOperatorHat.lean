import YangMills.Construction.Matrices.CalculusOfTheFieldsOnPowersOfG
import YangMills.Construction.TransferOperators.PropertiesOfMultiplicationByTheBondKernel
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.Matrices.ComplexMatrix2
noncomputable section
namespace YangMills.Construction.SpinHarmonics
def HatDoubleTerms.Statement : Prop :=
  ∀ (J : Type) [Finite J] [Nonempty J] (β : ℝ) (B : Set J) (f : (↥B → specialUnitary) → ℂ)
    (hf : IsRealEntryPolynomial f) (D : ↥B → ℕ)
    (F : C(J → specialUnitary, ℂ)),
    0 < β → B.Nonempty → HasDegreeBound D f → (F : (J → specialUnitary) → ℂ) ∈ smoothSet →
    (∀ s' s : J → HalfNatural, hatDoubleTerm β B f hf F s' s ∈ prodCoeffSpan s') ∧
    (∀ s' s : J → HalfNatural, hatDoubleTerm β B f hf F s' s ≠ 0 →
      (∀ b, b ∉ B → s' b = s b) ∧
        IsDegreeCompatible D (restrictTo B s) (restrictTo B s')) ∧
    (∀ s' : J → HalfNatural, {s : J → HalfNatural | hatDoubleTerm β B f hf F s' s ≠ 0}.Finite ∧
      {s : J → HalfNatural | hatDoubleTerm β B f hf F s' s ≠ 0}.ncard ≤ ∏ᶠ b, (2 * D b + 1)) ∧
    (∀ s : J → HalfNatural, {s' : J → HalfNatural | hatDoubleTerm β B f hf F s' s ≠ 0}.Finite ∧
      {s' : J → HalfNatural | hatDoubleTerm β B f hf F s' s ≠ 0}.ncard ≤ ∏ᶠ b, (2 * D b + 1)) ∧
    (∀ (p : ℕ) (s' : J → HalfNatural), (1 + weightSum s') ^ p *
        ∑' s : J → HalfNatural,
          ‖toHaarL2 (hatDoubleTerm β B f hf F s' s : (J → specialUnitary) → ℂ)‖ ≤
      mulConst β D * (esupNorm f).toReal *
        (1 + (degreeTotal D : ℝ) / 2) ^ p *
        (sobolevDecay p (toHaarL2 (F : (J → specialUnitary) → ℂ))).toReal *
        (1 + weightSum s') ^ degreeTotal D) ∧
    ∀ w : List (J × Fin 3), Summable fun q : (J → HalfNatural) × (J → HalfNatural) =>
      supNorm (fieldWord w (hatDoubleTerm β B f hf F q.1 q.2))
end YangMills.Construction.SpinHarmonics
end
