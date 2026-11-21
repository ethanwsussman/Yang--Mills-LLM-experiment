import YangMills.Construction.Towers.MultiplesOfTheKernelOfAnEvaluation
import YangMills.Construction.Towers.TransposesOfTheIteratedAveragesOfTheScaledPictureOnASide
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
open Matrices
open PeriodicOperators (KernelUnique Represents RowFinite)
open PeriodicOperators.RowFiniteKernels (ApplyComp)
open ScalarMultipleKernels (CoeffsRealHomogeneous)
open RescaledConditions
namespace IterTransposesOnTorus
theorem pauliCoeff_real_smul (c : ℝ) (a : Fin 3) (X : ComplexMatrix2) :
    pauliCoeff a (c • X) = (c : ℂ) * pauliCoeff a X := by
  have hc : c • X = (c : ℂ) • X := by
    ext i j
    simp
  rw [hc]
  by_cases hc0 : (c : ℂ) = 0
  · have hzero : pauliCoeff a (0 : ComplexMatrix2) = 0 := by
      unfold pauliCoeff
      rw [dif_pos (Submodule.zero_mem _)]
      have hmap := map_zero (OneLoop.pauliCoordinateEquiv)
      exact congrFun hmap a
    rw [hc0, zero_smul, zero_mul, hzero]
  · unfold pauliCoeff
    by_cases hX : X ∈ ComplexMatrix2.traceless
    · have hcX : (c : ℂ) • X ∈ ComplexMatrix2.traceless := Submodule.smul_mem _ _ hX
      rw [dif_pos hcX, dif_pos hX]
      have hsub : (⟨(c : ℂ) • X, hcX⟩ : ComplexMatrix2.traceless) = (c : ℂ) • ⟨X, hX⟩ := rfl
      rw [hsub, map_smul]
      rfl
    · have hcX : (c : ℂ) • X ∉ ComplexMatrix2.traceless := fun hmem => hX (by
        have hback := Submodule.smul_mem ComplexMatrix2.traceless (c : ℂ)⁻¹ hmem
        rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul] at hback)
      rw [dif_neg hcX, dif_neg hX, mul_zero]
theorem vertexCoordinate_coeffsRealHomogeneous (σ : Type) :
    CoeffsRealHomogeneous (vertexCoordinate σ) := by
  intro c f
  funext ι
  exact pauliCoeff_real_smul c ι.1 (f ι.2)
theorem edgePauliCoordinates_coeffsRealHomogeneous (L n k j : ℕ) :
    CoeffsRealHomogeneous (edgePauliCoordinates L n k j) := by
  intro c f
  funext ι
  exact pauliCoeff_real_smul c ι.1 (f ι.2.1)
theorem smul_kernel_facts (hM : ScalarMultipleKernels.Statement) {r r' : PauliComponentsOfSymmetricKernel}
    {m : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2}
    (hh : CoeffsRealHomogeneous r')
    (hk : PauliComponentsOfSymmetricKernel.HasLocalKernel r r' m)
    (hu : KernelUnique r.Index r'.Index) (c a a' : ℝ) :
    RowFinite (r.kernel r' fun f => c • m f) ∧
    RowFinite (meshTranspose a a' (r.kernel r' fun f => c • m f)) ∧
    Represents (meshTranspose a a' (r.kernel r' fun f => c • m f))
      (((c * (a' ^ 4 * (a ^ 4)⁻¹) : ℝ) : ℂ) • r.transposeOnCoeffs r' m) := by
  obtain ⟨h₁, h₂⟩ := hM r r' m hh hk hu c a a'
  rw [h₂, h₁]
  exact ⟨hk.smul_row_finite _, hk.smul_swap_row_finite _,
    hk.smul_swap_represents _⟩
theorem kernel_facts (hM : ScalarMultipleKernels.Statement) {r r' : PauliComponentsOfSymmetricKernel}
    {m : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2}
    (hh : CoeffsRealHomogeneous r')
    (hk : PauliComponentsOfSymmetricKernel.HasLocalKernel r r' m)
    (hu : KernelUnique r.Index r'.Index) (a a' : ℝ) :
    RowFinite (meshTranspose a a' (r.kernel r' m)) ∧
    Represents (meshTranspose a a' (r.kernel r' m))
      (((1 * (a' ^ 4 * (a ^ 4)⁻¹) : ℝ) : ℂ) • r.transposeOnCoeffs r' m) := by
  have hone : (fun f => (1 : ℝ) • m f) = m := funext fun f => one_smul ℝ (m f)
  have hfacts := smul_kernel_facts hM hh hk hu 1 a a'
  rw [hone] at hfacts
  exact hfacts.2
theorem claim_holds (hComp : PeriodicOperators.RowFiniteKernels.Claim)
    (hThree : ThreeMapKernels.Claim)
    (hSmul : ScalarMultipleKernels.Statement) : Claim := by
  intro L hL k hk n hn U hU
  obtain ⟨hUnit, hDiff, -, hMean⟩ := (hThree L hL k hk).1 n hn
  obtain ⟨hQ, hR⟩ := hMean U hU
  have hD := hDiff U hU.1
  have hL0 : (L : ℝ) ≠ 0 := by
    have := hL.2
    exact Nat.cast_ne_zero.mpr (by omega)
  have htop : meshAt L k k = 1 := by
    simp [meshAt]
  have hfine : finestMesh L k = ((L : ℝ) ^ k)⁻¹ := by
    simp [finestMesh, meshAt, zpow_neg]
  have hfine0 : finestMesh L k ≠ 0 := by
    rw [hfine]
    exact inv_ne_zero (pow_ne_zero _ hL0)
  have hcR : (((1 * (meshAt L k k ^ 4 * (finestMesh L k ^ 4)⁻¹) : ℝ)) : ℂ) =
      (L : ℂ) ^ (4 * k) := by
    rw [htop, hfine]
    push_cast
    rw [pow_mul' (L : ℂ) 4 k]
    simp
  have hcQ : (((finestMesh L k * (meshAt L k k ^ 4 * (finestMesh L k ^ 4)⁻¹) : ℝ)) :
      ℂ) = ((finestMesh L k : ℂ) ^ 3)⁻¹ := by
    rw [htop]
    have hfineC : (finestMesh L k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hfine0
    push_cast
    field_simp
  have hve := (hUnit 0 0 (Nat.zero_le k) (Nat.zero_le k)).2.1
  have hvv := (hUnit 0 k (Nat.zero_le k) le_rfl).1
  have hee := (hUnit 0 k (Nat.zero_le k) le_rfl).2.2.2
  obtain ⟨hRtRows, hRtRep⟩ := kernel_facts hSmul (vertexCoordinate_coeffsRealHomogeneous _) hR hvv
    (finestMesh L k) (meshAt L k k)
  obtain ⟨hQRows, hQtRows, hQtRep⟩ := smul_kernel_facts hSmul
    (edgePauliCoordinates_coeffsRealHomogeneous _ _ _ _)
    hQ hee (finestMesh L k) (finestMesh L k) (meshAt L k k)
  obtain ⟨hDRows, hDtRows, -⟩ := smul_kernel_facts hSmul
    (edgePauliCoordinates_coeffsRealHomogeneous _ _ _ _) hD hve
    (finestMesh L k)⁻¹ (finestMesh L k) (finestMesh L k)
  rw [hcR] at hRtRep
  rw [hcQ] at hQtRep
  have hRRows := hR.row_finite
  refine ⟨hRtRep, hQtRep, ?_, ?_, ?_⟩
  · exact ((hComp.1 _ _ _ hQRows).2 _ _ hQtRows).1
  · exact ((hComp.1 _ _ _ hRtRows).2 _ _ hDRows).1
  · exact ((hComp.1 _ _ _ hDtRows).2 _ _ hRRows).1
end IterTransposesOnTorus
end Tower
end YangMills.Construction
end
