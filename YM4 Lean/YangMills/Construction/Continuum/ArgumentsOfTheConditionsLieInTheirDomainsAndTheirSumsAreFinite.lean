import YangMills.Construction.Continuum.AxiomsOfOsterwalderAndSchrader
import YangMills.Construction.Continuum.ConditionsOnASequenceOfFunctionalsOnFlatSpaces
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigSpace
def domainsAndFiniteSumsStatement : Prop :=
  ∀ S : FlatSequence, IsLinearFunctionalSeq S →
    (∀ (m : ℕ) (φ : schwartzFlatOffDiagonal (m + 1)),
      (∀ r : EuclidMotion,
        motionAct r φ.1 ∈ schwartzFlatOffDiagonal (m + 1)) ∧
      (∀ σ : Equiv.Perm (Fin (m + 1)),
        permAct σ φ.1 ∈ schwartzFlatOffDiagonal (m + 1)) ∧
      flipConj φ.1 ∈ schwartzFlatOffDiagonal (m + 1)) ∧
    ∀ Φ Ψ : PosTimeSeq, PosTimeSeq.IsFinitelySupported Φ → PosTimeSeq.IsFinitelySupported Ψ →
      (∀ q : ℕ, flipConjAt (Φ q).1 ∈ flatOffDiagonalAt q) ∧
      (∀ q' : ℕ, (Ψ q').1 ∈ flatOffDiagonalAt q') ∧
      (∀ q q' : ℕ, tensorAt (flipConjAt (Φ q).1) (Ψ q').1 ∈
        flatOffDiagonalAt (q + q')) ∧
      (∀ v ∈ zeroTimeHyperplane, ∀ (t : ℝ) (q q' : ℕ),
        tensorAt (flipConjAt (Φ q).1) (shiftActAt (t • v) (Ψ q').1) ∈
          flatOffDiagonalAt (q + q')) ∧
      {p : ℕ × ℕ |
        S.evalAt (tensorAt (flipConjAt (Φ p.1).1) (Ψ p.2).1) ≠ 0}.Finite ∧
      (∀ v ∈ zeroTimeHyperplane, ∀ t : ℝ,
        {p : ℕ × ℕ | S.evalAt (tensorAt (flipConjAt (Φ p.1).1)
          (shiftActAt (t • v) (Ψ p.2).1)) ≠ 0}.Finite) ∧
      {q : ℕ | S.evalAt (flipConjAt (Φ q).1) ≠ 0}.Finite ∧
      {q' : ℕ | S.evalAt (Ψ q').1 ≠ 0}.Finite
end YangMills.Construction.ConfigSpace
end
