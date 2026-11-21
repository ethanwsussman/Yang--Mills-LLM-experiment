import Mathlib
set_option autoImplicit false
open Matrix
noncomputable section
namespace YangMills.Construction.Orthogonal
abbrev orthogonalGroupThree := Matrix.orthogonalGroup (Fin 3) ℝ
abbrev orthogonalGroupFour := Matrix.orthogonalGroup (Fin 4) ℝ
def spatialProjection (x : Fin 4 → ℝ) : Fin 3 → ℝ := fun i => x i.castSucc
def spacetimePoint (v : Fin 3 → ℝ) (s : ℝ) : Fin 4 → ℝ := Fin.snoc (α := fun _ => ℝ) v s
theorem spacetimePoint_last (v : Fin 3 → ℝ) (s : ℝ) : spacetimePoint v s (Fin.last 3) = s :=
  Fin.snoc_last (α := fun _ => ℝ) s v
theorem spacetimePoint_castSucc (v : Fin 3 → ℝ) (s : ℝ) (i : Fin 3) :
    spacetimePoint v s i.castSucc = v i :=
  Fin.snoc_castSucc (α := fun _ => ℝ) s v i
theorem spacetimePoint_spatialProjection (x : Fin 4 → ℝ) :
    spacetimePoint (spatialProjection x) (x (Fin.last 3)) = x := by
  funext μ
  refine Fin.lastCases ?_ (fun i => ?_) μ
  · rw [spacetimePoint_last]
  · rw [spacetimePoint_castSucc]
    rfl
def blockDiagOne (M : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks M 0 0 (1 : Matrix (Fin 1) (Fin 1) ℝ))
theorem blockDiagOne_castSucc_castSucc (M : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    blockDiagOne M i.castSucc j.castSucc = M i j := by
  have hi : i.castSucc = finSumFinEquiv (Sum.inl i : Fin 3 ⊕ Fin 1) := rfl
  have hj : j.castSucc = finSumFinEquiv (Sum.inl j : Fin 3 ⊕ Fin 1) := rfl
  rw [hi, hj]
  simp [blockDiagOne]
theorem blockDiagOne_castSucc_last (M : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) :
    blockDiagOne M i.castSucc (Fin.last 3) = 0 := by
  have hi : i.castSucc = finSumFinEquiv (Sum.inl i : Fin 3 ⊕ Fin 1) := rfl
  have hl : Fin.last 3 = finSumFinEquiv (Sum.inr 0 : Fin 3 ⊕ Fin 1) := rfl
  rw [hi, hl]
  simp [blockDiagOne]
theorem blockDiagOne_last_castSucc (M : Matrix (Fin 3) (Fin 3) ℝ) (j : Fin 3) :
    blockDiagOne M (Fin.last 3) j.castSucc = 0 := by
  have hj : j.castSucc = finSumFinEquiv (Sum.inl j : Fin 3 ⊕ Fin 1) := rfl
  have hl : Fin.last 3 = finSumFinEquiv (Sum.inr 0 : Fin 3 ⊕ Fin 1) := rfl
  rw [hj, hl]
  simp [blockDiagOne]
theorem blockDiagOne_last_last (M : Matrix (Fin 3) (Fin 3) ℝ) :
    blockDiagOne M (Fin.last 3) (Fin.last 3) = 1 := by
  have hl : Fin.last 3 = finSumFinEquiv (Sum.inr 0 : Fin 3 ⊕ Fin 1) := rfl
  rw [hl]
  simp [blockDiagOne]
theorem blockDiagOne_mulVec (M : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 3 → ℝ) (s : ℝ) :
    blockDiagOne M *ᵥ spacetimePoint v s = spacetimePoint (M *ᵥ v) s := by
  funext μ
  refine Fin.lastCases ?_ (fun i => ?_) μ
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, blockDiagOne_last_castSucc,
      blockDiagOne_last_last, spacetimePoint_last, spacetimePoint_castSucc]
    simp
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, blockDiagOne_castSucc_castSucc,
      blockDiagOne_castSucc_last, spacetimePoint_last, spacetimePoint_castSucc]
    simp
theorem blockDiagOne_mem {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M ∈ orthogonalGroupThree) :
    blockDiagOne M ∈ orthogonalGroupFour := by
  have hMM : M * Mᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).1 hM
  rw [Matrix.mem_orthogonalGroup_iff]
  unfold blockDiagOne
  rw [Matrix.reindex_apply, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv,
    Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  simp [hMM]
def embedOrthogonal (R : orthogonalGroupThree) : orthogonalGroupFour :=
  ⟨blockDiagOne R.1, blockDiagOne_mem R.2⟩
theorem embedOrthogonal_mulVec (R : orthogonalGroupThree) (v : Fin 3 → ℝ) (s : ℝ) :
    (embedOrthogonal R).1 *ᵥ spacetimePoint v s = spacetimePoint (R.1 *ᵥ v) s :=
  blockDiagOne_mulVec R.1 v s
def orthogonalAct {E : Type*} (Q : orthogonalGroupFour) (f : (Fin 4 → ℝ) → E) :
    (Fin 4 → ℝ) → E :=
  fun x => f ((Q⁻¹ : orthogonalGroupFour).1 *ᵥ x)
def matrixOperatorNorm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M‖
abbrev operatorNormTopology (n : ℕ) : TopologicalSpace (Matrix.orthogonalGroup (Fin n) ℝ) :=
  TopologicalSpace.induced
    (fun R => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (R : Matrix (Fin n) (Fin n) ℝ))
    inferInstance
theorem operatorNormTopology_eq (n : ℕ) :
    operatorNormTopology n =
      (inferInstance : TopologicalSpace (Matrix.orthogonalGroup (Fin n) ℝ)) := by
  let e : Matrix (Fin n) (Fin n) ℝ ≃L[ℝ]
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
    LinearEquiv.toContinuousLinearEquiv
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).toAlgEquiv.toLinearEquiv
  have he : (inferInstance : TopologicalSpace (Matrix (Fin n) (Fin n) ℝ)) =
      TopologicalSpace.induced e inferInstance :=
    e.toHomeomorph.isInducing.eq_induced
  have hc : operatorNormTopology n = TopologicalSpace.induced
      (Subtype.val : Matrix.orthogonalGroup (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ)
      (TopologicalSpace.induced e inferInstance) := by
    rw [induced_compose]
    rfl
  rw [hc, ← he]
  rfl
end YangMills.Construction.Orthogonal
