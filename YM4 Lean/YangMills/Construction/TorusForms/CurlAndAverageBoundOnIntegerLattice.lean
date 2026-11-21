import YangMills.Construction.TorusForms.ObjectsOnTheIntegerLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.IntegerLattice
def unitCubesOver (S : Lattice.LatticeParameters) (Λ' : Set (ScaledSite S.d S.L)) :
    Set (ScaledSite S.d 1) :=
  {x | ∃ y' ∈ Λ', ∀ μ, (y' : Fin S.d → ℤ) μ ≤ (x : Fin S.d → ℤ) μ ∧
    (x : Fin S.d → ℤ) μ < (y' : Fin S.d → ℤ) μ + S.L}
theorem edgesMeeting_finite_of_finite {d s : ℕ} {X : Set (ScaledSite d s)} (hX : X.Finite) :
    (edgesMeeting X).Finite := by
  have hprod : (X ×ˢ (Set.univ : Set (Fin d))).Finite := hX.prod Set.finite_univ
  have hshift : (⋃ μ : Fin d,
      (fun x : ScaledSite d s => ((x - basisStep d s μ, μ) : Edge d s)) '' X).Finite :=
    Set.finite_iUnion fun μ => hX.image _
  refine (hprod.union hshift).subset ?_
  rintro ⟨x, μ⟩ (hx | hx)
  · exact Or.inl ⟨hx, Set.mem_univ _⟩
  · exact Or.inr (Set.mem_iUnion.mpr ⟨μ, x + basisStep d s μ, hx, by simp⟩)
end YangMills.Construction.IntegerLattice
