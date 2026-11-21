import YangMills.Construction.Conventions.StandingParameters
import Mathlib
set_option autoImplicit false
universe u
namespace YangMills.Construction.Conventions
abbrev AdmissibleBlockingFactors : Type :=
  {L : ℕ // YangMills.Construction.Conventions.IsAdmissibleBlockingFactor L}
abbrev RealTuple : Type := Σ r : ℕ, Fin r → ℝ
inductive DependentObjectKind : Type
  | number
  | tuple
  | realSet
  | tupleSet
  | function (r : ℕ+)
def DependentObjectKind.Carrier : DependentObjectKind → Type
  | .number => ℝ
  | .tuple => RealTuple
  | .realSet => Set ℝ
  | .tupleSet => Set RealTuple
  | .function r => (Fin (r : ℕ) → ℝ) →. ℝ
def FactorsThroughBlockingFactor {D : Type u} (k : DependentObjectKind)
    (L : D → AdmissibleBlockingFactors) (x : D → k.Carrier) : Prop :=
  ∃ X : AdmissibleBlockingFactors → k.Carrier, ∀ d, x d = X (L d)
end YangMills.Construction.Conventions
