import YangMills.Construction.TorusForms.BlocksCorridorsDomains
import Mathlib
noncomputable section
namespace YangMills.Construction
open Lattice BlockSpin
namespace BlockSpin
namespace AverageComposition
variable {P : LatticeParameters} {ℓ : Fin P.d → ℝ} {a a' a'' : ℝ}
theorem coe_nsmul_latticeStep (a : ℝ) (k : ℕ) (μ : Fin P.d) :
    ((k • latticeStep ℓ a μ : LatticeSite ℓ a) : PeriodicTorus ℓ) =
      torusMk ℓ ((k : ℝ) • a • basisVector μ) := by
  change k • torusMk ℓ (a • basisVector μ) = _
  rw [← map_nsmul, Nat.cast_smul_eq_nsmul]
theorem gridPoint_single_natCast (a : ℝ) (k : ℕ) (μ : Fin P.d) :
    gridPoint ℓ a (Pi.single μ (k : ℤ)) = k • latticeStep ℓ a μ := by
  refine Subtype.ext ?_
  rw [coe_nsmul_latticeStep]
  change torusMk ℓ _ = _
  congr 1
  funext ν
  by_cases hν : ν = μ
  · subst hν
    simp [basisVector]
  · simp [basisVector, hν]
theorem sum_range_mul_eq_sum_sum (p q : ℕ) (g : ℕ → ℝ) :
    ∑ m ∈ Finset.range (p * q), g m =
      ∑ j ∈ Finset.range q, ∑ i ∈ Finset.range p, g (p * j + i) := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
end AverageComposition
end BlockSpin
end YangMills.Construction
