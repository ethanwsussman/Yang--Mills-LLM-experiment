import YangMills.Construction.LatticeFields.ScaleParameters
import YangMills.Construction.LatticeFields.WeightConjProjComplProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFields.DiffLocality
variable {d : ℕ}
variable {N : ℕ} {κ : LatticeShape d}
section Nbhd
variable (hD : TorusLaws.TorusMetricProps N κ) {U : Set (LatticeSite N κ)}
  {x : LatticeSite N κ}
include hD
end Nbhd
section SquareNorm
variable {I : Type} [Fintype I] [Fintype (LatticeSite N κ)]
theorem fieldInner_self_eq_sum (G : LatticeField N κ I) :
    fieldInner G G = latticeSpacing N ^ d * ∑ x, ∑ i, G x i ^ 2 := by
  unfold fieldInner
  rw [tsum_fintype, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring
end SquareNorm
end YangMills.Construction.LatticeFields.DiffLocality
