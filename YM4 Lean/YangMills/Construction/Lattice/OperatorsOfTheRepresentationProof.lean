import YangMills.Construction.Lattice.TwoScaleOperatorDefs
import YangMills.Construction.TorusForms.CurlAndAverageBoundOnIntegerLattice
import YangMills.Construction.Lattice.DifferenceOperatorsCellAveragesTrees
import YangMills.Construction.Lattice.GaugeSplittingOperators
import YangMills.Construction.Lattice.OneScaleOperatorBounds
import Mathlib
set_option autoImplicit false
open Finset
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open ScaledFun
namespace GaugeSplitting
variable {d L j N : ℕ}
section Laplacian
variable {s : Mesh N}
end Laplacian
namespace Extension
variable (S : Scales d L j N)
end Extension
section Projections
variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
end Projections
theorem pathSum_nil {s : Mesh N} (A : OneForm d s) : OneForm.pathSum A [] = 0 := rfl
theorem pathSum_cons {s : Mesh N} (A : OneForm d s) (b : Link d s) (Γ : List (Link d s)) :
    OneForm.pathSum A (b :: Γ) = A b + OneForm.pathSum A Γ := List.sum_cons
theorem pathSum_append {s : Mesh N} (A : OneForm d s) (Γ Γ' : List (Link d s)) :
    OneForm.pathSum A (Γ ++ Γ') = OneForm.pathSum A Γ + OneForm.pathSum A Γ' := by
  induction Γ with
  | nil => rw [List.nil_append, pathSum_nil, zero_add]
  | cons b Γ ih => rw [List.cons_append, pathSum_cons, pathSum_cons, ih, add_assoc]
theorem pathSum_add {s : Mesh N} (A B : OneForm d s) (Γ : List (Link d s)) :
    OneForm.pathSum (A + B) Γ = OneForm.pathSum A Γ + OneForm.pathSum B Γ := by
  induction Γ with
  | nil => simp only [pathSum_nil, add_zero]
  | cons b Γ ih =>
    rw [pathSum_cons, pathSum_cons, pathSum_cons, ih]
    change A b + B b + _ = _
    ring
end GaugeSplitting
end YangMills.Construction.PeriodicLattice
