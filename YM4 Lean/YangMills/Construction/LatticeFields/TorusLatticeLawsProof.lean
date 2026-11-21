import YangMills.Construction.LatticeFields.BlockPartitionMassiveLaplacian
import YangMills.Construction.LatticeFields.MetricAdjointCubeFacts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFields.TorusLattice
variable {d : ℕ}
section Metric
variable {N : ℕ} {κ : LatticeShape d}
theorem siteDist_le_sum_abs_lift (x x' : LatticeSite N κ) (v : scaledIntLattice d N)
    (hv : toSite N κ v = x - x') :
    siteDist x x' ≤ ∑ μ, |(v : Fin d → ℝ) μ| := by apply _root_.YangMills.Construction.LatticeFields.MetricAdjointCubes.siteDist_le_sum_abs <;> assumption
def unitStepLift (N : ℕ) (μ : Fin d) : scaledIntLattice d N :=
  ⟨Pi.single μ (latticeSpacing N), by
    intro ν
    by_cases h : ν = μ
    · subst h
      exact ⟨1, by simp⟩
    · exact ⟨0, by simp [Pi.single_eq_of_ne h]⟩⟩
theorem unitStep_eq_toSite (μ : Fin d) : unitStep N κ μ = toSite N κ (unitStepLift N μ) := rfl
theorem sum_abs_unitStepLift (μ : Fin d) :
    ∑ ν, |(unitStepLift N μ : Fin d → ℝ) ν| = latticeSpacing N := by
  have hs : 0 ≤ latticeSpacing N := inv_nonneg.mpr (Nat.cast_nonneg N)
  rw [Finset.sum_eq_single μ]
  · show |(Pi.single μ (latticeSpacing N) : Fin d → ℝ) μ| = latticeSpacing N
    rw [Pi.single_eq_same, abs_of_nonneg hs]
  · intro ν _ hν
    show |(Pi.single μ (latticeSpacing N) : Fin d → ℝ) ν| = 0
    rw [Pi.single_eq_of_ne hν, abs_zero]
  · intro h
    exact absurd (Finset.mem_univ μ) h
theorem siteDist_add_unitStep_le (x : LatticeSite N κ) (μ : Fin d) :
    siteDist x (x + unitStep N κ μ) ≤ latticeSpacing N := by
  have hle := siteDist_le_sum_abs_lift x (x + unitStep N κ μ) (-unitStepLift N μ) (by
    rw [map_neg, ← unitStep_eq_toSite]
    abel)
  have heq : ∑ ν, |((-unitStepLift N μ : scaledIntLattice d N) : Fin d → ℝ) ν| =
      ∑ ν, |(unitStepLift N μ : Fin d → ℝ) ν| :=
    Finset.sum_congr rfl fun ν _ => abs_neg _
  rwa [heq, sum_abs_unitStepLift] at hle
end Metric
section Finiteness
end Finiteness
section Adjoint
variable {N : ℕ} {κ : LatticeShape d} {I : Type}
theorem fieldInner_smul_left (e : ℝ) (F G : LatticeField N κ I) :
    fieldInner (e • F) G = e * fieldInner F G := by apply _root_.YangMills.Construction.LatticeFields.Transverse.fieldInner_smul_left <;> assumption
theorem fieldInner_smul_right (e : ℝ) (F G : LatticeField N κ I) :
    fieldInner F (e • G) = e * fieldInner F G := by apply _root_.YangMills.Construction.LatticeFields.CompressedGreenDecayProof.fieldInner_smul <;> assumption
theorem fieldInner_sub_left [Finite (LatticeSite N κ)] [Finite I] (F F' G : LatticeField N κ I) :
    fieldInner (F - F') G = fieldInner F G - fieldInner F' G := by apply _root_.YangMills.SharedProofs.p65939 <;> assumption
theorem fieldInner_sub_right [Finite (LatticeSite N κ)] [Finite I] (F G G' : LatticeField N κ I) :
    fieldInner F (G - G') = fieldInner F G - fieldInner F G' := by apply _root_.YangMills.Construction.LatticeFields.CompressedGreenDecayProof.fieldInner_sub <;> assumption
theorem fieldSquareSummable_of_finite [Finite (LatticeSite N κ)] [Finite I]
    (F : LatticeField N κ I) : FieldSquareSummable F :=
  Summable.of_finite
end Adjoint
section CoarseBlocks
variable {N : ℕ} {κ : LatticeShape d}
end CoarseBlocks
end YangMills.Construction.LatticeFields.TorusLattice
