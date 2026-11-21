import YangMills.Construction.LatticeFields.BlockAvgAdjoints
import YangMills.Construction.LatticeFields.WeightConjRules
import YangMills.Construction.LatticeFields.WeightConjProjComplProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFields
namespace ConjugatedBlockAveraging
variable {d N : ℕ} {κ : LatticeShape d}
theorem finite_torusSites [NeZero N] (ℓ : Fin d → ℕ) (hℓ : ∀ μ, 1 ≤ ℓ μ) :
    Finite (LatticeSite N (LatticeShape.torus ℓ hℓ)) := by apply _root_.YangMills.Construction.LatticeFields.WeightConjProjComplProof.finite_torusSites <;> assumption
theorem latticeSpacing_nonneg (M : ℕ) : 0 ≤ latticeSpacing M := inv_nonneg.mpr (Nat.cast_nonneg M)
section Norms
variable {M M' : ℕ} {I J : Type}
theorem fieldInner_comm (F G : LatticeField M κ I) : fieldInner F G = fieldInner G F := by
  unfold fieldInner
  exact tsum_congr fun p => by ring
theorem fieldInner_eq_sum [Fintype (LatticeSite M κ)] [Fintype I] (F G : LatticeField M κ I) :
    fieldInner F G = latticeSpacing M ^ d * ∑ p : LatticeSite M κ × I, F p.1 p.2 * G p.1 p.2 := by apply _root_.YangMills.Construction.LatticeFields.WeightConjProjComplProof.fieldInner_eq_sum <;> assumption
theorem fieldInner_self_nonneg [Fintype (LatticeSite M κ)] [Fintype I] (F : LatticeField M κ I) :
    0 ≤ fieldInner F F := by apply _root_.YangMills.Construction.LatticeFields.WeightConjProjComplProof.fieldInner_self_nonneg <;> assumption
theorem fieldNorm_sq [Fintype (LatticeSite M κ)] [Fintype I] (F : LatticeField M κ I) :
    fieldNorm F ^ 2 = fieldInner F F :=
  Real.sq_sqrt (fieldInner_self_nonneg F)
theorem fieldInner_sub_left [Fintype (LatticeSite M κ)] [Fintype I] (F F' G : LatticeField M κ I) :
    fieldInner (F - F') G = fieldInner F G - fieldInner F' G := by
  simp only [fieldInner_eq_sum, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, mul_sub]
theorem fieldInner_sub_right [Fintype (LatticeSite M κ)] [Fintype I] (F G G' : LatticeField M κ I) :
    fieldInner F (G - G') = fieldInner F G - fieldInner F G' := by
  rw [fieldInner_comm, fieldInner_sub_left, fieldInner_comm G, fieldInner_comm G']
end Norms
end ConjugatedBlockAveraging
end YangMills.Construction.LatticeFields
