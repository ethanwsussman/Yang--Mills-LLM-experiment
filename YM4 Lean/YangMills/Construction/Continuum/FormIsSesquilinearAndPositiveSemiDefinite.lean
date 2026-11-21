import YangMills.Construction.Continuum.FormOnAdmissibleSequences
import YangMills.Construction.Continuum.LinearCombinationsOfAdmissibleSequences
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.ConfigSpace
def formTermArg (Φ Ψ : AdmissibleSeq) (p q : ℕ) : FnOrScalar (p + q) :=
  tensorAt (flipConjAt (Φ.1 p).1) (Ψ.1 q).1
def FlatSequence.IsSesquilinear (S : FlatSequence) : Prop :=
  (∀ (Φ Ψ : AdmissibleSeq) (p q : ℕ),
      formTermArg Φ Ψ p q ∈ flatOffDiagonalAt (p + q)) ∧
    (∀ Φ Ψ : AdmissibleSeq,
      {m : ℕ × ℕ | S.evalAt (formTermArg Φ Ψ m.1 m.2) ≠ 0}.Finite) ∧
    (∀ (a b : ℂ) (Φ Φ' Φ'' Ψ : AdmissibleSeq),
      IsLinComb a b Φ.1 Φ'.1 Φ''.1 →
        S.reflectionForm Φ'' Ψ =
          conj a * S.reflectionForm Φ Ψ + conj b * S.reflectionForm Φ' Ψ) ∧
    ∀ (a b : ℂ) (Φ Ψ Ψ' Ψ'' : AdmissibleSeq),
      IsLinComb a b Ψ.1 Ψ'.1 Ψ''.1 →
        S.reflectionForm Φ Ψ'' =
          a * S.reflectionForm Φ Ψ + b * S.reflectionForm Φ Ψ'
def FlatSequence.NullSpaceIsSubspace (S : FlatSequence) : Prop :=
  (∀ Φ : AdmissibleSeq, IsZeroSeq Φ.1 → Φ ∈ S.reflectionNullSpace) ∧
    ∀ (a b : ℂ) (Φ Φ' Φ'' : AdmissibleSeq), Φ ∈ S.reflectionNullSpace →
      Φ' ∈ S.reflectionNullSpace →
      IsLinComb a b Φ.1 Φ'.1 Φ''.1 → Φ'' ∈ S.reflectionNullSpace
def FlatSequence.IsPosSemidef (S : FlatSequence) : Prop :=
  (∀ Φ : AdmissibleSeq,
      (S.reflectionForm Φ Φ).im = 0 ∧ 0 ≤ (S.reflectionForm Φ Φ).re) ∧
    (∀ Φ Ψ : AdmissibleSeq,
      S.reflectionForm Ψ Φ = conj (S.reflectionForm Φ Ψ)) ∧
    (∀ Φ Ψ : AdmissibleSeq,
      ‖S.reflectionForm Φ Ψ‖ ^ 2 ≤
        (S.reflectionForm Φ Φ).re * (S.reflectionForm Ψ Ψ).re) ∧
    S.NullSpaceIsSubspace ∧
    S.reflectionNullSpace = {Φ | ∀ Ψ : AdmissibleSeq, S.reflectionForm Φ Ψ = 0}
def SesquilinearPosSemidefStatement : Prop :=
  ∀ S : FlatSequence, IsCLMSequence S →
    S.IsSesquilinear ∧ (IsOSPositive S → S.IsPosSemidef)
end YangMills.Construction.ConfigSpace
end
