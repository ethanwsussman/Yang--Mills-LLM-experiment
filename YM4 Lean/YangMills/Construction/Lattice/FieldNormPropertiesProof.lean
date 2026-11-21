import YangMills.Construction.Lattice.FieldNormProperties
import YangMills.Construction.Lattice.OneScaleGreenOperatorOnCornerCubesProof
import Mathlib
namespace YangMills.Construction.PeriodicLattice
open ScaledFun
variable {d N : ℕ} {a : Mesh N}
namespace FieldNormProofs
theorem finsetSum_apply {X T : Type} (U : Finset T) (g : T → ScaledFun d a X) (q : X) :
    (∑ t ∈ U, g t) q = ∑ t ∈ U, g t q := by apply _root_.YangMills.SharedProofs.p17632 <;> assumption
theorem holderQuotientSup_bddAbove (α : ℝ) (v : GridPoint d a → GridPoint d a → ℝ) :
    BddAbove {t | ∃ x y : GridPoint d a,
      0 < taxicabDist (x : Torus d N) y ∧ taxicabDist (x : Torus d N) y ≤ 1 ∧
        t = taxicabDist (x : Torus d N) y ^ (-α) * v x y} := by
  refine ((Set.finite_range fun p : GridPoint d a × GridPoint d a =>
    taxicabDist (p.1 : Torus d N) p.2 ^ (-α) * v p.1 p.2).subset ?_).bddAbove
  rintro t ⟨x, y, _, _, rfl⟩
  exact ⟨(x, y), rfl⟩
theorem holderQuotientSup_nonneg (α : ℝ) (v : GridPoint d a → GridPoint d a → ℝ)
    (hv : ∀ x y, 0 ≤ v x y) : 0 ≤ holderQuotientSup a α v := by apply _root_.YangMills.Construction.CubeCovering.RescaledGreen.holderQuotientSup_nonneg <;> assumption
section Fields
variable {ι : Type} [Fintype ι]
theorem abs_apply_le_normAt (f : MultiField d a ι) (i : ι) (x : GridPoint d a) :
    |f (i, x)| ≤ f.normAt x :=
  le_ciSup (f := fun i => |f (i, x)|) (Set.finite_range _).bddAbove i
theorem norm_sq_eq_sum_sq (f : MultiField d a ι) :
    ‖f‖ ^ 2 = ∑ i, ∑ x, a.h ^ d * f (i, x) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, MultiField.inner_eq]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => ?_
  ring
end Fields
end FieldNormProofs
end YangMills.Construction.PeriodicLattice
