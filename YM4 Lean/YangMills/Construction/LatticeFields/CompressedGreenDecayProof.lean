import YangMills.Construction.LatticeFields.MassiveLaplacianCoercive
import YangMills.Construction.LatticeFields.SiteSetDecay
import YangMills.Construction.LatticeFields.WeightConjugateBounds
import YangMills.Construction.LatticeFields.WeightConjRules
import YangMills.Construction.LatticeFields.WeightConjDirichletGreenBoundsProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFields
namespace CompressedGreenDecayProof
theorem torus_finite {d : ℕ} (N : ℕ) [NeZero N] (ℓ : Fin d → ℕ) (hℓ : ∀ μ, 1 ≤ ℓ μ) :
    Finite (LatticeSite N (LatticeShape.torus ℓ hℓ)) := by apply _root_.YangMills.Construction.LatticeFields.WeightConjProjComplProof.finite_torusSites <;> assumption
section Inner
variable {d N : ℕ} {κ : LatticeShape d} {I : Type}
theorem fieldInner_symm (F G : LatticeField N κ I) : fieldInner F G = fieldInner G F :=
  tsum_congr fun p => by ring
theorem fieldInner_self_nonneg (F : LatticeField N κ I) : 0 ≤ fieldInner F F :=
  tsum_nonneg fun p => by
    have h : 0 ≤ latticeSpacing N ^ d :=
      pow_nonneg (show 0 ≤ latticeSpacing N from inv_nonneg.mpr (Nat.cast_nonneg N)) d
    rw [mul_assoc]
    exact mul_nonneg h (mul_self_nonneg _)
theorem fieldNorm_sq_eq (F : LatticeField N κ I) : fieldNorm F ^ 2 = fieldInner F F :=
  Real.sq_sqrt (fieldInner_self_nonneg F)
theorem fieldNorm_nonneg (F : LatticeField N κ I) : 0 ≤ fieldNorm F := Real.sqrt_nonneg _
theorem fieldInner_mulBase (g : LatticeSite N κ → ℝ) (F G : LatticeField N κ I) :
    fieldInner F (mulBase g G) = fieldInner (mulBase g F) G :=
  tsum_congr fun p => by simp only [mulBase]; ring
theorem fieldInner_smul (t : ℝ) (F G : LatticeField N κ I) :
    fieldInner F (t • G) = t * fieldInner F G := by
  unfold fieldInner
  rw [← tsum_mul_left]
  exact tsum_congr fun p => by simp only [Pi.smul_apply, smul_eq_mul]; ring
variable [Finite (LatticeSite N κ)] [Finite I]
theorem fieldInner_add (F G H : LatticeField N κ I) :
    fieldInner F (G + H) = fieldInner F G + fieldInner F H := by
  unfold fieldInner
  rw [← Summable.tsum_add Summable.of_finite Summable.of_finite]
  exact tsum_congr fun p => by simp [mul_add]
theorem fieldInner_sub (F G H : LatticeField N κ I) :
    fieldInner F (G - H) = fieldInner F G - fieldInner F H := by
  unfold fieldInner
  rw [← Summable.tsum_sub Summable.of_finite Summable.of_finite]
  exact tsum_congr fun p => by simp [mul_sub]
theorem abs_fieldInner_le (F G : LatticeField N κ I) :
    |fieldInner F G| ≤ fieldNorm F * fieldNorm G := by
  have key : ∀ t : ℝ,
      0 ≤ fieldInner G G * (t * t) + (2 * fieldInner F G) * t + fieldInner F F := by
    intro t
    have h := fieldInner_self_nonneg (F + t • G)
    rw [fieldInner_add, fieldInner_symm (F + t • G) F, fieldInner_symm (F + t • G) (t • G),
      fieldInner_add, fieldInner_add, fieldInner_symm (t • G) F, fieldInner_smul,
      fieldInner_smul, fieldInner_symm (t • G) G, fieldInner_smul] at h
    have e : fieldInner F F + t * fieldInner F G + (t * fieldInner F G + t * (t * fieldInner G G)) =
        fieldInner G G * (t * t) + (2 * fieldInner F G) * t + fieldInner F F := by ring
    rw [← e]
    exact h
  have hd := discrim_le_zero key
  unfold discrim at hd
  have hsq : fieldInner F G ^ 2 ≤ fieldInner F F * fieldInner G G := by nlinarith
  rw [fieldNorm, fieldNorm, ← Real.sqrt_mul (fieldInner_self_nonneg F)]
  exact Real.abs_le_sqrt hsq
theorem fieldNorm_add_le (F G : LatticeField N κ I) :
    fieldNorm (F + G) ≤ fieldNorm F + fieldNorm G := by
  have e : fieldInner (F + G) (F + G) =
      fieldInner F F + 2 * fieldInner F G + fieldInner G G := by
    rw [fieldInner_add, fieldInner_symm (F + G) F, fieldInner_symm (F + G) G,
      fieldInner_add, fieldInner_add, fieldInner_symm G F]
    ring
  refine (abs_le_of_sq_le_sq' ?_ (add_nonneg (fieldNorm_nonneg F) (fieldNorm_nonneg G))).2
  have h := (abs_le.mp (abs_fieldInner_le F G)).2
  rw [fieldNorm_sq_eq, e, add_sq, fieldNorm_sq_eq, fieldNorm_sq_eq]
  linarith
end Inner
section Weights
variable {d N : ℕ} {κ : LatticeShape d} {I : Type}
end Weights
section Bonds
variable {d N : ℕ} {κ : LatticeShape d}
theorem restrictBonds_of_mem {S : Set (LatticeBond N κ)} {A : LatticeOneForm N κ}
    (hA : A ∈ fieldsOnBonds S) : restrictBonds S A = A := by
  classical
  funext x i
  by_cases h : (x, i 0) ∈ S
  · simp [restrictBonds, h]
  · have hi : i = directionIndex (i 0) := by
      funext j
      rw [Subsingleton.elim j 0]
      rfl
    have h0 := hA.2 (x, i 0) h
    simp only [LatticeOneForm.bondValue, LatticeOneForm.coord] at h0
    rw [← hi] at h0
    simp [restrictBonds, h, h0]
theorem fieldInner_restrictBonds (S : Set (LatticeBond N κ)) (A X : LatticeOneForm N κ) :
    fieldInner A (restrictBonds S X) = fieldInner (restrictBonds S A) X :=
  tsum_congr fun p => by simp only [restrictBonds]; ring
end Bonds
section Distance
variable {d N : ℕ} {κ : LatticeShape d}
end Distance
section Constants
end Constants
section Core
variable {d N : ℕ} {ℓ : Fin d → ℕ} {hℓ : ∀ μ, 1 ≤ ℓ μ}
end Core
section Green
variable {P : ScaleData} {ℓ : Fin P.d → ℕ} {hℓ : ∀ μ, 1 ≤ ℓ μ}
end Green
section EvaluationMaps
variable {d N : ℕ} {κ : LatticeShape d}
end EvaluationMaps
end CompressedGreenDecayProof
end YangMills.Construction.LatticeFields
