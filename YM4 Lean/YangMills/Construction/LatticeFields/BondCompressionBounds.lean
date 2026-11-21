import YangMills.Construction.LatticeFields.BlockAveraging
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.LatticeFields
variable {d N : ℕ} {κ : LatticeShape d}
def fieldsOnBonds (S : Set (LatticeBond N κ)) : Set (LatticeOneForm N κ) :=
  {A | FieldSquareSummable A ∧ ∀ b, b ∉ S → LatticeOneForm.bondValue A b = 0}
def fieldsOrthOnBonds (S : Set (LatticeBond N κ)) : Set (LatticeOneForm N κ) :=
  {B | FieldSquareSummable B ∧ ∀ A ∈ fieldsOnBonds S, fieldInner A B = 0}
def bondCompress (S : Set (LatticeBond N κ)) (D : LatticeOneForm N κ → LatticeOneForm N κ) :
    LatticeOneForm N κ → LatticeOneForm N κ :=
  fun A => restrictBonds S (D (restrictBonds S A))
structure IsInvOnBonds (S : Set (LatticeBond N κ))
    (B G : LatticeOneForm N κ → LatticeOneForm N κ) : Prop where
  maps_to : ∀ A ∈ fieldsOnBonds S, G A ∈ fieldsOnBonds S
  right_inv : ∀ A ∈ fieldsOnBonds S, B (G A) = A
  left_inv : ∀ A ∈ fieldsOnBonds S, G (B A) = A
  eq_zero_of_orth : ∀ A ∈ fieldsOrthOnBonds S, G A = 0
  map_add : ∀ A ∈ fieldsOnBonds S, ∀ A' ∈ fieldsOrthOnBonds S, G (A + A') = G A + G A'
section Torus
variable {ℓ : Fin d → ℕ} {hℓ : ∀ μ, 1 ≤ ℓ μ}
end Torus
theorem restrictBonds_mem_fieldsOnBonds (S : Set (LatticeBond N κ)) {J : LatticeOneForm N κ}
    (hJ : FieldSquareSummable J) : restrictBonds S J ∈ fieldsOnBonds S := by
  classical
  refine ⟨?_, ?_⟩
  · refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun p => ?_) hJ
    by_cases h : (p.1, p.2 0) ∈ S <;> simp [restrictBonds, h, sq_nonneg]
  · intro b hb
    have hb' : (b.1, b.2) ∉ S := hb
    simp [LatticeOneForm.bondValue, LatticeOneForm.coord, restrictBonds, directionIndex, hb']
theorem sub_restrictBonds_mem_fieldsOrthOnBonds (S : Set (LatticeBond N κ))
    {J : LatticeOneForm N κ} (hJ : FieldSquareSummable J) :
    J - restrictBonds S J ∈ fieldsOrthOnBonds S := by
  classical
  refine ⟨?_, ?_⟩
  · refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun p => ?_) hJ
    by_cases h : (p.1, p.2 0) ∈ S <;> simp [restrictBonds, h, sq_nonneg]
  · intro A hA
    unfold fieldInner
    have hvanish : ∀ p : LatticeSite N κ × (Fin 1 → Fin d),
        latticeSpacing N ^ d * A p.1 p.2 * (J - restrictBonds S J) p.1 p.2 = 0 := by
      rintro ⟨x, i⟩
      by_cases h : (x, i 0) ∈ S
      · simp [restrictBonds, h]
      · have hi : i = directionIndex (i 0) := by
          funext j
          rw [Subsingleton.elim j 0]
          rfl
        have hAx : A x i = 0 := by
          have := hA.2 (x, i 0) h
          simp only [LatticeOneForm.bondValue, LatticeOneForm.coord] at this
          rwa [← hi] at this
        simp [hAx]
    exact (tsum_congr hvanish).trans tsum_zero
theorem IsInvOnBonds.eq_bondCompress {S : Set (LatticeBond N κ)}
    {B G : LatticeOneForm N κ → LatticeOneForm N κ}
    (hG : IsInvOnBonds S B G) {J : LatticeOneForm N κ} (hJ : FieldSquareSummable J) :
    G J = restrictBonds S (G (restrictBonds S J)) := by
  classical
  have hon := restrictBonds_mem_fieldsOnBonds S hJ
  have horth := sub_restrictBonds_mem_fieldsOrthOnBonds S hJ
  have hsplit : G J = G (restrictBonds S J) := by
    have := hG.map_add _ hon _ horth
    rw [hG.eq_zero_of_orth _ horth, add_zero, add_sub_cancel] at this
    exact this
  have hmaps := hG.maps_to _ hon
  rw [hsplit]
  funext x i
  by_cases hb : (x, i 0) ∈ S
  · simp [restrictBonds, hb]
  · have hi : i = directionIndex (i 0) := by
      funext j
      rw [Subsingleton.elim j 0]
      rfl
    have hx := hmaps.2 (x, i 0) hb
    simp only [LatticeOneForm.bondValue, LatticeOneForm.coord] at hx
    rw [← hi] at hx
    simp [restrictBonds, hb, hx]
section Inequalities
variable {I I' : Type}
end Inequalities
end YangMills.Construction.LatticeFields
