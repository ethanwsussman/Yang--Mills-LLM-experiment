import YangMills.Construction.OneLoopLaw.PlaneWavesUnderMotionsOfTheLatticeProof
import YangMills.Construction.Towers.IsometriesAreOrthogonalMotionsProof
import Mathlib
set_option autoImplicit false
open Matrix
noncomputable section
namespace YangMills.Construction.UnitLatticeMotions
open YangMills.Construction.Tower YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.OrthogonalMotions
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.TorusMetric (torusProj)
theorem mem_orthogonalGroup_of_mul_transpose_eq_one {R : Matrix (Fin 4) (Fin 4) ℝ}
    (hR : R * Rᵀ = 1) : R ∈ Matrix.orthogonalGroup (Fin 4) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  simpa [Matrix.star_eq_conjTranspose] using hR
theorem mul_transpose_eq_one_of_mem_orthogonalGroup {R : Matrix (Fin 4) (Fin 4) ℝ}
    (hR : R ∈ Matrix.orthogonalGroup (Fin 4) ℝ) : R * Rᵀ = 1 := by apply _root_.YangMills.Construction.Tower.OrthogonalMotions.orth_mul_transpose_self <;> assumption
theorem permMatrix_mem_orthogonalGroup (σ : Equiv.Perm (Fin 4)) :
    permMatrix σ ∈ Matrix.orthogonalGroup (Fin 4) ℝ := by
  apply mem_orthogonalGroup_of_mul_transpose_eq_one
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [permMatrix, Matrix.transpose_apply, Matrix.of_apply]
  rw [Fintype.sum_equiv σ _
    (fun k => (if i = k then (1 : ℝ) else 0) * (if j = k then 1 else 0)) (fun _ => rfl)]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij, Ne.symm hij]
theorem permMatrix_isIntegerMatrix (σ : Equiv.Perm (Fin 4)) :
    IsIntegerMatrix (permMatrix σ) := by
  intro i j
  by_cases hij : i = σ j
  · exact ⟨1, by simp [permMatrix, hij]⟩
  · exact ⟨0, by simp [permMatrix, hij]⟩
theorem axisReflectionMatrix_mem_orthogonalGroup (a : Fin 4) :
    axisReflectionMatrix a ∈ Matrix.orthogonalGroup (Fin 4) ℝ := by
  apply mem_orthogonalGroup_of_mul_transpose_eq_one
  rw [axisReflectionMatrix, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  congr 1
  funext j
  by_cases hj : j = a <;> simp [hj]
theorem axisReflectionMatrix_isIntegerMatrix (a : Fin 4) :
    IsIntegerMatrix (axisReflectionMatrix a) := by
  intro i j
  by_cases hij : i = j
  · subst hij
    by_cases hi : i = a
    · exact ⟨-1, by simp [axisReflectionMatrix, hi]⟩
    · exact ⟨1, by simp [axisReflectionMatrix, hi]⟩
  · exact ⟨0, by simp [axisReflectionMatrix, hij]⟩
theorem one_isIntegerMatrix : IsIntegerMatrix (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  intro i j
  by_cases hij : i = j
  · subst hij
    exact ⟨1, by simp⟩
  · exact ⟨0, by simp [hij]⟩
theorem castVec_add (u v : Fin 4 → ℤ) : castVec u + castVec v = castVec (u + v) := by
  funext j
  simp [castVec]
theorem exists_mulVec_castVec_eq {R : Matrix (Fin 4) (Fin 4) ℝ} (hR : IsIntegerMatrix R)
    (u : Fin 4 → ℤ) : ∃ v : Fin 4 → ℤ, R *ᵥ castVec u = castVec v := by apply _root_.YangMills.Construction.Tower.OrthogonalMotions.exists_mulVec_intVec <;> assumption
theorem mem_sublattice_levelDepth_zero_iff {L n : ℕ} {x : PeriodicLattice.FourTorus L n} :
    x ∈ PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth 0 0) ↔
      ∃ u : Fin 4 → ℤ, x = torusProj (PeriodicLattice.torusSide L n) (castVec u) := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.mem_sublattice_levelDepth_iff <;> assumption
theorem mapsSublatticeOnto_of_isInducedByMotion {L n : ℕ}
    {f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n}
    {R : Matrix (Fin 4) (Fin 4) ℝ} {t : Fin 4 → ℤ}
    (hR : R ∈ Matrix.orthogonalGroup (Fin 4) ℝ) (hZ : IsIntegerMatrix R)
    (hf : IsInducedByMotion f R t) : MapsSublatticeOnto 0 0 f := by
  unfold MapsSublatticeOnto
  ext y
  simp only [Set.mem_image, SetLike.mem_coe, mem_sublattice_levelDepth_zero_iff]
  constructor
  · rintro ⟨x, ⟨u, rfl⟩, rfl⟩
    obtain ⟨v, hv⟩ := exists_mulVec_castVec_eq hZ u
    exact ⟨v + t, by rw [hf, hv, castVec_add]⟩
  · rintro ⟨u, rfl⟩
    obtain ⟨v, hv⟩ := exists_mulVec_castVec_eq (R := Rᵀ) (fun i j => hZ j i) (u - t)
    refine ⟨torusProj (PeriodicLattice.torusSide L n) (castVec v), ⟨v, rfl⟩, ?_⟩
    rw [hf, ← hv, Matrix.mulVec_mulVec, mul_transpose_eq_one_of_mem_orthogonalGroup hR,
      Matrix.one_mulVec, castVec_add, sub_add_cancel]
theorem statement_of_classification (h : Classification) : Statement := by
  refine ⟨fun σ => ⟨permMatrix_mem_orthogonalGroup σ, permMatrix_isIntegerMatrix σ⟩,
    fun a => ⟨axisReflectionMatrix_mem_orthogonalGroup a, axisReflectionMatrix_isIntegerMatrix a⟩,
    one_isIntegerMatrix, ?_⟩
  intro L n hL hn R hR hZ t
  obtain ⟨f, hf, hiso⟩ := (h.2.2.2 L n hL hn).2.2.2 R hR hZ (castVec t)
  have hind : IsInducedByMotion f R t := hf
  exact ⟨f, hind, hiso, mapsSublatticeOnto_of_isInducedByMotion hR hZ hind⟩
end YangMills.Construction.UnitLatticeMotions
end
