import YangMills.Construction.TorusForms.BlocksCorridorsAveragesTrees
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace CoveringLattice
section FiniteSupport
variable {ι κ : Type*}
structure IsLocalOperator (T : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) (N : κ → Set ι) : Prop where
  rows_finite : ∀ j, (N j).Finite
  columns_finite : ∀ i, {j | i ∈ N j}.Finite
  eq_zero_of_vanishing : ∀ (f : ι → ℝ) (j : κ), (∀ i ∈ N j, f i = 0) → T f j = 0
variable {T : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)} {N : κ → Set ι}
theorem IsLocalOperator.finite_support (h : IsLocalOperator T N) (f : ι →₀ ℝ) :
    (Function.support (T f)).Finite := by
  refine (f.support.finite_toSet.biUnion fun i _ => h.columns_finite i).subset ?_
  intro j hj
  by_contra hnot
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_coe, Finsupp.mem_support_iff,
    exists_prop, not_exists, not_and] at hnot
  refine hj (h.eq_zero_of_vanishing f j fun i hi => ?_)
  by_contra hi'
  exact hnot i hi' hi
end FiniteSupport
abbrev GridSite (d : ℕ) (ε : ℝ) : Type := Lattice.scaledIntegerLattice d ε
def gridStep (d : ℕ) (ε : ℝ) (μ : Fin d) : GridSite d ε :=
  ⟨ε • Lattice.basisVector μ, (AddSubgroup.mem_pi _).mpr fun ν _ =>
    AddSubgroup.mem_zmultiples_iff.mpr ⟨if ν = μ then 1 else 0, by
      by_cases h : ν = μ <;> simp [Lattice.basisVector, h]⟩⟩
abbrev GridLink (d : ℕ) (ε : ℝ) : Type := GridSite d ε × Fin d
def GridLink.head {d : ℕ} {ε : ℝ} (b : GridLink d ε) : GridSite d ε := b.1 + gridStep d ε b.2
def GridLink.ends {d : ℕ} {ε : ℝ} (b : GridLink d ε) : Set (GridSite d ε) := {b.1, b.head}
section Blocks
variable (S : Lattice.LatticeParameters) {ε' : ℝ}
theorem finite_setOf_inBlockIndexRange (n : ℕ) :
    {σ : Fin S.d → ℤ | BlockSpin.InBlockIndexRange S n σ}.Finite := by
  refine (Set.Finite.pi' fun _ => Set.finite_Icc (-(BlockSpin.blockOffset S n : ℤ))
    ((S.L : ℤ) ^ n - 1 - BlockSpin.blockOffset S n)).subset ?_
  intro σ hσ μ
  exact Set.mem_Icc.mpr (hσ μ)
end Blocks
end CoveringLattice
end YangMills.Construction
