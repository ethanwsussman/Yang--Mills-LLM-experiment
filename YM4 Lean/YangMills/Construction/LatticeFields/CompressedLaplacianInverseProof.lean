import YangMills.Construction.Lattice.SiteIdentification
import YangMills.Construction.Lattice.TwoScaleOperatorDefs
import YangMills.Construction.LatticeFields.BlockAveraging
import YangMills.Construction.Lattice.LocalizedDecayBounds
import YangMills.Construction.LatticeFields.CompressedGreenDecayProof
import YangMills.Construction.LatticeFields.DifferenceIdentities
import YangMills.Construction.LatticeFields.MassiveLaplacianForms
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFields.CompressedGreenProof
theorem finite_latticeSite_torus {d : ℕ} (N : ℕ) [NeZero N] (ℓ : Fin d → ℕ) (hℓ : ∀ μ, 1 ≤ ℓ μ) :
    Finite (LatticeSite N (LatticeShape.torus ℓ hℓ)) := by apply _root_.YangMills.Construction.LatticeFields.WeightConjProjComplProof.finite_torusSites <;> assumption
theorem le_of_energy_ineq {γ p q n r : ℝ} (hγ : 0 < γ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hn : 0 ≤ n)
    (hr : r = p ∨ r = q) (h : γ * (q ^ 2 + p ^ 2) ≤ r * n) : p ≤ γ⁻¹ * n ∧ q ≤ γ⁻¹ * n := by
  obtain ⟨m, hm⟩ : ∃ m, m = max p q := ⟨_, rfl⟩
  have hpm : p ≤ m := hm ▸ le_max_left _ _
  have hqm : q ≤ m := hm ▸ le_max_right _ _
  have hm0 : 0 ≤ m := hp.trans hpm
  have hrm : r ≤ m := by
    rcases hr with rfl | rfl <;> assumption
  have hm2 : m ^ 2 ≤ q ^ 2 + p ^ 2 := by
    rcases max_choice p q with e | e <;> rw [hm, e] <;> nlinarith [sq_nonneg p, sq_nonneg q]
  have h1 : γ * m ^ 2 ≤ m * n :=
    (mul_le_mul_of_nonneg_left hm2 hγ.le).trans (h.trans (mul_le_mul_of_nonneg_right hrm hn))
  have h2 : γ * m ≤ n := by
    rcases hm0.eq_or_lt with e | e
    · rw [← e]
      simpa using hn
    · have h3 : m * (γ * m) ≤ m * n := by nlinarith
      exact le_of_mul_le_mul_left h3 e
  have h3 : m ≤ γ⁻¹ * n := by
    rw [inv_mul_eq_div, le_div_iff₀ hγ]
    linarith
  exact ⟨hpm.trans h3, hqm.trans h3⟩
section Inner
variable {d N : ℕ} {κ : LatticeShape d} {I : Type}
theorem fieldInner_comm (F G : LatticeField N κ I) : fieldInner F G = fieldInner G F :=
  tsum_congr fun p => by ring
theorem fieldInner_self_nonneg (F : LatticeField N κ I) : 0 ≤ fieldInner F F := by apply _root_.YangMills.Construction.LatticeFields.CompressedGreenDecayProof.fieldInner_self_nonneg <;> assumption
theorem fieldNorm_sq (F : LatticeField N κ I) : fieldNorm F ^ 2 = fieldInner F F := by apply _root_.YangMills.Construction.LatticeFields.CompressedGreenDecayProof.fieldNorm_sq_eq <;> assumption
theorem fieldNorm_nonneg (F : LatticeField N κ I) : 0 ≤ fieldNorm F := Real.sqrt_nonneg _
theorem fieldInner_smul_right (t : ℝ) (F G : LatticeField N κ I) :
    fieldInner F (t • G) = t * fieldInner F G := by apply _root_.YangMills.Construction.LatticeFields.CompressedGreenDecayProof.fieldInner_smul <;> assumption
theorem fieldInner_restrictBonds (S : Set (LatticeBond N κ)) (F G : LatticeOneForm N κ) :
    fieldInner F (restrictBonds S G) = fieldInner (restrictBonds S F) G :=
  tsum_congr fun p => by simp only [restrictBonds]; ring
variable [Finite (LatticeSite N κ)] [Finite I]
theorem fieldSquareSummable_of_finite (F : LatticeField N κ I) : FieldSquareSummable F :=
  Summable.of_finite
theorem fieldInner_add_right (F G H : LatticeField N κ I) :
    fieldInner F (G + H) = fieldInner F G + fieldInner F H := by apply _root_.YangMills.Construction.LatticeFields.CompressedGreenDecayProof.fieldInner_add <;> assumption
theorem fieldInner_sub_right (F G H : LatticeField N κ I) :
    fieldInner F (G - H) = fieldInner F G - fieldInner F H := by apply _root_.YangMills.Construction.LatticeFields.CompressedGreenDecayProof.fieldInner_sub <;> assumption
theorem eq_zero_of_fieldInner_self [NeZero N] (F : LatticeField N κ I) (h : fieldInner F F = 0) :
    F = 0 := by
  have hs : 0 < latticeSpacing N ^ d :=
    pow_pos (inv_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N))) d
  have hnn : ∀ p : LatticeSite N κ × I, 0 ≤ latticeSpacing N ^ d * F p.1 p.2 * F p.1 p.2 := fun p => by
    rw [mul_assoc]
    exact mul_nonneg hs.le (mul_self_nonneg _)
  have hsum : HasSum (fun p : LatticeSite N κ × I => latticeSpacing N ^ d * F p.1 p.2 * F p.1 p.2) 0 := by
    have hsm : Summable fun p : LatticeSite N κ × I => latticeSpacing N ^ d * F p.1 p.2 * F p.1 p.2 :=
      Summable.of_finite
    have hs' := hsm.hasSum
    rwa [show ∑' p : LatticeSite N κ × I, latticeSpacing N ^ d * F p.1 p.2 * F p.1 p.2 = 0 from h] at hs'
  have hz := (hasSum_zero_iff_of_nonneg hnn).mp hsum
  funext x i
  have hq := congrFun hz (x, i)
  have hq' : latticeSpacing N ^ d * (F x i * F x i) = 0 := by
    simpa [mul_assoc] using hq
  simpa using (mul_eq_zero.mp hq').resolve_left hs.ne'
theorem fieldInner_sq_le (F G : LatticeField N κ I) :
    fieldInner F G ^ 2 ≤ fieldInner F F * fieldInner G G := by
  have h : ∀ x : ℝ, 0 ≤ fieldInner G G * (x * x) + (2 * fieldInner F G) * x + fieldInner F F := by
    intro x
    have h0 := fieldInner_self_nonneg (F + x • G)
    have e : fieldInner (F + x • G) (F + x • G) =
        fieldInner G G * (x * x) + (2 * fieldInner F G) * x + fieldInner F F := by
      rw [fieldInner_add_right, fieldInner_comm (F + x • G) F, fieldInner_comm (F + x • G) (x • G),
        fieldInner_add_right F, fieldInner_add_right (x • G), fieldInner_smul_right,
        fieldInner_smul_right, fieldInner_comm (x • G) F, fieldInner_smul_right,
        fieldInner_comm (x • G) G, fieldInner_smul_right]
      ring
    rwa [e] at h0
  have h1 := discrim_le_zero h
  unfold discrim at h1
  nlinarith
theorem fieldInner_le_norm_mul_norm (F G : LatticeField N κ I) :
    fieldInner F G ≤ fieldNorm F * fieldNorm G := by
  have h := Real.abs_le_sqrt (fieldInner_sq_le F G)
  rw [Real.sqrt_mul (fieldInner_self_nonneg F)] at h
  exact (le_abs_self _).trans h
end Inner
section Abstract
variable {d N : ℕ} {κ : LatticeShape d}
theorem restrictBonds_of_mem {S : Set (LatticeBond N κ)} {A : LatticeOneForm N κ}
    (hA : A ∈ fieldsOnBonds S) : restrictBonds S A = A := by apply _root_.YangMills.Construction.LatticeFields.CompressedGreenDecayProof.restrictBonds_of_mem <;> assumption
variable [Finite (LatticeSite N κ)]
theorem fieldInner_bondCompress {S : Set (LatticeBond N κ)}
    (D : LatticeOneForm N κ → LatticeOneForm N κ)
    {A A' : LatticeOneForm N κ} (hA : A ∈ fieldsOnBonds S) (hA' : A' ∈ fieldsOnBonds S) :
    fieldInner A' (bondCompress S D A) = fieldInner A' (D A) := by
  unfold bondCompress
  rw [fieldInner_restrictBonds, restrictBonds_of_mem hA', restrictBonds_of_mem hA]
structure CoerciveSymmOp (γ : ℝ) (D : LatticeOneForm N κ → LatticeOneForm N κ) : Prop where
  pos : 0 < γ
  symm : ∀ A A', fieldInner A' (D A) = fieldInner (D A') A
  coercive : ∀ A, γ * (fieldNorm (tensorGrad A) ^ 2 + fieldNorm A ^ 2) ≤ fieldInner A (D A)
  grad_adjoint : ∀ (A : LatticeOneForm N κ) (K : LatticeTensor N κ (1 + 1)),
    fieldInner (tensorGrad A) K = fieldInner A (tensorGradAdjoint K)
variable [NeZero N]
namespace CoerciveSymmOp
variable {γ : ℝ} {D : LatticeOneForm N κ → LatticeOneForm N κ}
theorem bondCompress_coercive (H : CoerciveSymmOp γ D) {S : Set (LatticeBond N κ)}
    {A : LatticeOneForm N κ} (hA : A ∈ fieldsOnBonds S) :
    γ * (fieldNorm (tensorGrad A) ^ 2 + fieldNorm A ^ 2) ≤ fieldInner A (bondCompress S D A) := by
  rw [fieldInner_bondCompress D hA hA]
  exact H.coercive A
end CoerciveSymmOp
section Laws
variable {γ : ℝ} {D G : LatticeOneForm N κ → LatticeOneForm N κ} {S : Set (LatticeBond N κ)}
theorem mem_fieldsOnBonds_apply (h : IsInvOnBonds S (bondCompress S D) G) (J : LatticeOneForm N κ) :
    G J ∈ fieldsOnBonds S := by
  rw [h.eq_bondCompress (fieldSquareSummable_of_finite J)]
  exact restrictBonds_mem_fieldsOnBonds S (fieldSquareSummable_of_finite _)
theorem bondCompress_apply (h : IsInvOnBonds S (bondCompress S D) G) (J : LatticeOneForm N κ) :
    bondCompress S D (G J) = restrictBonds S J := by
  have hm := restrictBonds_mem_fieldsOnBonds S (fieldSquareSummable_of_finite J)
  have e : G J = G (restrictBonds S J) := by
    rw [h.eq_bondCompress (fieldSquareSummable_of_finite J), restrictBonds_of_mem (h.maps_to _ hm)]
  rw [e]
  exact h.right_inv _ hm
theorem fieldInner_bondCompress_apply (h : IsInvOnBonds S (bondCompress S D) G)
    {A : LatticeOneForm N κ} (hA : A ∈ fieldsOnBonds S) (J : LatticeOneForm N κ) :
    fieldInner A (bondCompress S D (G J)) = fieldInner A J := by
  rw [bondCompress_apply h, fieldInner_restrictBonds, restrictBonds_of_mem hA]
theorem energy_le (H : CoerciveSymmOp γ D) (h : IsInvOnBonds S (bondCompress S D) G)
    (J : LatticeOneForm N κ) :
    γ * (fieldNorm (tensorGrad (G J)) ^ 2 + fieldNorm (G J) ^ 2) ≤ fieldInner (G J) J := by
  have e := H.bondCompress_coercive (mem_fieldsOnBonds_apply h J)
  rwa [fieldInner_bondCompress_apply h (mem_fieldsOnBonds_apply h J)] at e
theorem norm_apply_le (H : CoerciveSymmOp γ D) (h : IsInvOnBonds S (bondCompress S D) G)
    (J : LatticeOneForm N κ) :
    fieldNorm (G J) ≤ γ⁻¹ * fieldNorm J ∧ fieldNorm (tensorGrad (G J)) ≤ γ⁻¹ * fieldNorm J :=
  le_of_energy_ineq H.pos (fieldNorm_nonneg _) (fieldNorm_nonneg _) (fieldNorm_nonneg _)
    (Or.inl rfl) ((energy_le H h J).trans (fieldInner_le_norm_mul_norm _ _))
end Laws
end Abstract
end YangMills.Construction.LatticeFields.CompressedGreenProof
