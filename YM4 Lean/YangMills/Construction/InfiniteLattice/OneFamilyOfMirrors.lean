import YangMills.Construction.InfiniteLattice.SixteenFamiliesHeightsPositionsAndSides
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix
noncomputable section
namespace YangMills.Construction
namespace NormalFamilies
open InfiniteLattice
open PeriodicLattice (coordVec)
theorem firstNonzeroIndex_eq {n : AmbientSpace} {μ : Fin 4} (hμ : n μ ≠ 0)
    (hlow : ∀ κ, κ < μ → n κ = 0) : firstNonzeroIndex n = μ := by
  obtain ⟨h1, h2⟩ := firstNonzeroIndex_spec (n := n) ⟨μ, hμ⟩
  exact le_antisymm (not_lt.mp fun hlt => hμ (h2 μ hlt)) (not_lt.mp fun hlt => h1 (hlow _ hlt))
theorem firstNonzeroBasisVec_coordVec (μ : Fin 4) :
    firstNonzeroBasisVec (coordVec μ) = coordVec μ := by
  rw [firstNonzeroBasisVec, firstNonzeroIndex_eq (μ := μ)]
  · simp [coordVec]
  · intro κ hκ
    simp [coordVec, hκ.ne]
theorem firstNonzeroBasisVec_coordVec_add {μ ν : Fin 4} (h : μ < ν) :
    firstNonzeroBasisVec (coordVec μ + coordVec ν) = coordVec μ := by
  rw [firstNonzeroBasisVec, firstNonzeroIndex_eq (μ := μ)]
  · simp [coordVec, h.ne]
  · intro κ hκ
    simp [coordVec, hκ.ne, (hκ.trans h).ne]
theorem firstNonzeroBasisVec_coordVec_sub {μ ν : Fin 4} (h : μ < ν) :
    firstNonzeroBasisVec (coordVec μ - coordVec ν) = coordVec μ := by
  rw [firstNonzeroBasisVec, firstNonzeroIndex_eq (μ := μ)]
  · simp [coordVec, h.ne]
  · intro κ hκ
    simp [coordVec, hκ.ne, (hκ.trans h).ne]
theorem dotProduct_dualVector {n : AmbientSpace} (h : n ∈ normalSet) :
    n ⬝ᵥ dualVector n = 1 := by
  obtain ⟨F, rfl⟩ := exists_reflectionClass h
  rw [dualVector, dotProduct_smul, smul_eq_mul, normSq_eq_dotProduct]
  exact inv_mul_cancel₀ F.realNormal_dot_ne_zero
theorem dotProduct_firstNonzeroBasisVec {n : AmbientSpace} (h : n ∈ normalSet) :
    n ⬝ᵥ firstNonzeroBasisVec n = 1 := by
  rcases h with ⟨μ, rfl⟩ | ⟨μ, ν, hlt, rfl | rfl⟩
  · rw [firstNonzeroBasisVec_coordVec]
    simp [coordVec]
  · rw [firstNonzeroBasisVec_coordVec_add hlt]
    simp [coordVec, hlt.ne']
  · rw [firstNonzeroBasisVec_coordVec_sub hlt]
    simp [coordVec, hlt.ne']
def linearReflect (n : AmbientSpace) : AmbientSpace → AmbientSpace := reflectAcross n 0
theorem linearReflect_apply (n x : AmbientSpace) :
    linearReflect n x = x - (2 * (n ⬝ᵥ x)) • dualVector n := by
  simp [linearReflect, reflectAcross]
theorem closedHalfSpace_one (n : AmbientSpace) (c : ℝ) :
    closedHalfSpace n c 1 = {x | c ≤ n ⬝ᵥ x} := by
  ext x
  simp [closedHalfSpace]
theorem closedHalfSpace_neg_one (n : AmbientSpace) (c : ℝ) :
    closedHalfSpace n c (-1) = {x | n ⬝ᵥ x ≤ c} := by
  ext x
  simp [closedHalfSpace]
def IsGenerator (n : AmbientSpace) (f : AmbientSpace → AmbientSpace) : Prop :=
  (∃ v : LatticePoint 1, f = (shift v).toFun) ∨ ∃ c : ℝ, IsAllowedLevel 1 n c ∧ f = reflectAcross n c
def IsClassIsometry (n : AmbientSpace) (r : AmbientSpace → AmbientSpace) : Prop :=
  ∃ l : List (AmbientSpace → AmbientSpace), (∀ f ∈ l, IsGenerator n f) ∧
    r = l.foldr (· ∘ ·) id
theorem IsGenerator.isClassIsometry {n : AmbientSpace} {f : AmbientSpace → AmbientSpace}
    (h : IsGenerator n f) : IsClassIsometry n f :=
  ⟨[f], by simpa using h, by simp⟩
theorem isClassIsometry_shift (n : AmbientSpace) (v : LatticePoint 1) :
    IsClassIsometry n (shift v).toFun :=
  IsGenerator.isClassIsometry (Or.inl ⟨v, rfl⟩)
theorem isClassIsometry_reflectAcross {n : AmbientSpace} {c : ℝ} (hc : IsAllowedLevel 1 n c) :
    IsClassIsometry n (reflectAcross n c) :=
  IsGenerator.isClassIsometry (Or.inr ⟨c, hc, rfl⟩)
theorem IsClassIsometry.comp {n : AmbientSpace} {r r' : AmbientSpace → AmbientSpace}
    (h : IsClassIsometry n r) (h' : IsClassIsometry n r') :
    IsClassIsometry n (r ∘ r') := by
  obtain ⟨l, hl, rfl⟩ := h
  obtain ⟨l', hl', rfl⟩ := h'
  refine ⟨l ++ l', fun f hf => ?_, ?_⟩
  · rcases List.mem_append.mp hf with hf | hf
    · exact hl f hf
    · exact hl' f hf
  · induction l with
    | nil => simp
    | cons g l ih =>
      simpa [Function.comp_assoc] using congrArg (g ∘ ·) (ih fun f hf => hl f (by simp [hf]))
end NormalFamilies
end YangMills.Construction
