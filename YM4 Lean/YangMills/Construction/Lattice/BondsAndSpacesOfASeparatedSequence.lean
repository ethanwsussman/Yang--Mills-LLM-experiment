import YangMills.Construction.Lattice.PeriodicLattices
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m : ℕ} {j : ℤ}
def Plaquette.ContainsBond (p : Plaquette L m j) (b : Bond L m j) : Prop :=
  b ∈ p.boundaryBonds ∨ b.opposite ∈ p.boundaryBonds
theorem Bond.exists_plaquette_containsBond {b : Bond L m j} (hb : b.IsPositivelyOriented) :
    ∃ p : Plaquette L m j, p.ContainsBond b := by
  obtain ⟨μ, hμ⟩ := hb
  have hf : b = Bond.forwardFrom b.source μ := by
    apply Bond.ext
    · rfl
    · simp only [Bond.forwardFrom, ← hμ]
      abel
  by_cases h0 : μ = 0
  · refine ⟨⟨b.source, μ, 1, by simp [h0]⟩, Or.inl ?_⟩
    simp only [Plaquette.boundaryBonds, List.mem_cons]
    exact Or.inl hf
  · refine ⟨⟨b.source, 0, μ, Fin.pos_iff_ne_zero.mpr h0⟩, Or.inr ?_⟩
    simp only [Plaquette.boundaryBonds, List.mem_cons]
    refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    exact congrArg Bond.opposite hf
end PeriodicLattice
end YangMills.Construction
end
