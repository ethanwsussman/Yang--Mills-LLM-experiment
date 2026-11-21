import YangMills.Construction.Continuum.FormOnAdmissibleSequences
import YangMills.Construction.Continuum.LinearCombinationsOfAdmissibleSequences
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigSpace
instance instAddCommGroupFnOrScalar : (n : ℕ) → AddCommGroup (FnOrScalar n)
  | 0 => inferInstanceAs (AddCommGroup ℂ)
  | n + 1 => inferInstanceAs (AddCommGroup (Config (n + 1) → ℂ))
instance instModuleFnOrScalar : (n : ℕ) → Module ℂ (FnOrScalar n)
  | 0 => inferInstanceAs (Module ℂ ℂ)
  | n + 1 => inferInstanceAs (Module ℂ (Config (n + 1) → ℂ))
abbrev GradedSeq : Type := (q : ℕ) → FnOrScalar q
def seqValues (Φ : AdmissibleSeq) : GradedSeq := fun q => (Φ.1 q).1
theorem zero_eq_zeroOfDegree (n : ℕ) : (0 : FnOrScalar n) = zeroOfDegree n := by
  cases n <;> rfl
theorem smul_add_smul_eq_linCombAt (c c' : ℂ) {n : ℕ} (φ φ' : FnOrScalar n) :
    c • φ + c' • φ' = linCombAt c c' φ φ' := by
  cases n <;> rfl
def admissibleSpan : Submodule ℂ GradedSeq :=
  Submodule.span ℂ (Set.range seqValues)
def toAdmissibleSpan (Φ : AdmissibleSeq) : admissibleSpan :=
  ⟨seqValues Φ, Submodule.subset_span ⟨Φ, rfl⟩⟩
def SpanOfAdmissible.Statement : Prop :=
  ∀ x : GradedSeq,
    x ∈ admissibleSpan ↔ ∃ Φ : AdmissibleSeq, x = seqValues Φ
end YangMills.Construction.ConfigSpace
end
