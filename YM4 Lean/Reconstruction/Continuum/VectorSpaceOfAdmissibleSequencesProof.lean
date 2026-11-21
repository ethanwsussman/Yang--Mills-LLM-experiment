import YangMills.Construction.Continuum.VectorSpaceOfAdmissibleSequences
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigSpace.SpanOfAdmissible
theorem linComb_admissible (h : LinCombClosure) (a b : ℂ) (Φ Ψ : AdmissibleSeq) :
    ∃ Χ : AdmissibleSeq, a • seqValues Φ + b • seqValues Ψ = seqValues Χ := by
  obtain ⟨-, hc⟩ := h
  obtain ⟨Χ, hadm, hcomb⟩ := hc a b Φ.1 Ψ.1 Φ.2 Ψ.2
  refine ⟨⟨Χ, hadm⟩, funext fun q => ?_⟩
  show a • (Φ.1 q).1 + b • (Ψ.1 q).1 = (Χ q).1
  rw [smul_add_smul_eq_linCombAt, hcomb q]
theorem statement_of_linCombClosure (h : LinCombClosure) : SpanOfAdmissible.Statement := by
  intro x
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨Φ, rfl⟩ := hx
      exact ⟨Φ, rfl⟩
    | zero =>
      obtain ⟨⟨Φ, hadm, hz⟩, -⟩ := h
      exact ⟨⟨Φ, hadm⟩, funext fun q => (zero_eq_zeroOfDegree q).trans (hz q).symm⟩
    | add x y _ _ hx hy =>
      obtain ⟨Φ, rfl⟩ := hx
      obtain ⟨Ψ, rfl⟩ := hy
      obtain ⟨Χ, e⟩ := linComb_admissible h 1 1 Φ Ψ
      exact ⟨Χ, by simpa using e⟩
    | smul c x _ hx =>
      obtain ⟨Φ, rfl⟩ := hx
      obtain ⟨Χ, e⟩ := linComb_admissible h c 0 Φ Φ
      exact ⟨Χ, by simpa using e⟩
  · rintro ⟨Φ, rfl⟩
    exact Submodule.subset_span ⟨Φ, rfl⟩
end YangMills.Construction.ConfigSpace.SpanOfAdmissible
end
