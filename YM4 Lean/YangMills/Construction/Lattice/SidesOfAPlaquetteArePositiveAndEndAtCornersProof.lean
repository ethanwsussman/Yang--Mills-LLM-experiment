import YangMills.Construction.Lattice.SidesOfAPlaquetteArePositiveAndEndAtCorners
import Mathlib
namespace YangMills.Construction.PeriodicLattice
theorem edgesPositiveWithEndpointsAtVertices_holds : EdgesPositiveWithEndpointsAtVertices := by
  intro L m j p e he
  have hpos : ∀ (x : Site L m j) (μ : Fin 4), (Bond.forwardFrom x μ).IsPositivelyOriented :=
    fun x μ => ⟨μ, add_sub_cancel_left x (unitStep L m j μ)⟩
  have v₁ : p.origin ∈ p.vertices := Or.inl rfl
  have v₂ : p.origin + unitStep L m j p.firstAxis ∈ p.vertices := Or.inr (Or.inl rfl)
  have v₃ : p.origin + unitStep L m j p.firstAxis + unitStep L m j p.secondAxis ∈ p.vertices :=
    Or.inr (Or.inr (Or.inl rfl))
  have v₄ : p.origin + unitStep L m j p.secondAxis ∈ p.vertices := Or.inr (Or.inr (Or.inr rfl))
  have v₃' : p.origin + unitStep L m j p.secondAxis + unitStep L m j p.firstAxis ∈ p.vertices := by
    rw [add_right_comm]
    exact v₃
  rcases he with rfl | rfl | rfl | rfl
  · exact ⟨hpos _ _, v₁, v₂⟩
  · exact ⟨hpos _ _, v₂, v₃⟩
  · exact ⟨hpos _ _, v₄, v₃'⟩
  · exact ⟨hpos _ _, v₁, v₄⟩
end YangMills.Construction.PeriodicLattice
