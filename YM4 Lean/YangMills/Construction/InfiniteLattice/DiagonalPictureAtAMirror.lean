import YangMills.Construction.InfiniteLattice.DataOfTheThreePictures
import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace LatticeConventions
namespace DiagonalMirror
open NormalHyperplane
open InfiniteLattice (LatticePoint)
variable (a : Spacing) {μ κ : Direction} (hne : μ ≠ κ) {c : ℝ}
theorem diagonal_isLatticeMirror (hc : ∃ q : ℤ, c = (q : ℝ) * (a : ℝ)) :
    (diagonal μ κ hne c).IsLatticeMirror (a : ℝ) := by
  refine ⟨fun _ => ?_, fun _ => hc⟩
  obtain ⟨q, hq⟩ := hc
  exact ⟨2 * q, by change c = _; rw [hq]; push_cast; ring⟩
theorem shifted_isLatticeMirror (hc : ∃ q : ℤ, c = (q : ℝ) * (a : ℝ)) :
    (diagonal μ κ hne (c + (a : ℝ))).IsLatticeMirror (a : ℝ) := by
  obtain ⟨q, hq⟩ := hc
  exact diagonal_isLatticeMirror a hne ⟨q + 1, by rw [hq]; push_cast; ring⟩
theorem upperHalfSpace_diagonal :
    (diagonal μ κ hne c).upperHalfSpace = {x : Point | c ≤ x μ + x κ} := by
  ext x
  have hx : euclidDot (basisVector μ + basisVector κ) x = x μ + x κ := by
    simp [euclidDot, basisVector, add_mul, Finset.sum_add_distrib, Pi.single_apply]
  change c ≤ euclidDot (basisVector μ + basisVector κ) x ↔ _
  rw [hx]
  rfl
variable (μ κ)
def normalStep : LatticePoint (a : ℝ) :=
  ⟨(a : ℝ) • (basisVector μ + basisVector κ), Pi.single μ 1 + Pi.single κ 1, fun i => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, basisVector, Pi.single_apply]
    split_ifs <;> push_cast <;> ring⟩
def tangentStep : LatticePoint (a : ℝ) :=
  ⟨(a : ℝ) • (basisVector μ - basisVector κ), Pi.single μ 1 - Pi.single κ 1, fun i => by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, basisVector, Pi.single_apply]
    split_ifs <;> push_cast <;> ring⟩
end DiagonalMirror
end LatticeConventions
end YangMills.Construction
end
