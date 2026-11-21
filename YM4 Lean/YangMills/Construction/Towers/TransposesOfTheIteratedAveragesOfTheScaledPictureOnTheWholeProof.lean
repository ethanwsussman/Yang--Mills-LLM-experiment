import YangMills.Construction.Towers.TransposesOfTheIteratedAveragesOfTheScaledPictureOnASideProof
import YangMills.Construction.Towers.TransposesOfTheIteratedAveragesOfTheScaledPictureOnTheWhole
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace FullSpace
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.RescaledConditions (AverageTransposes)
open YangMills.Construction.Tower.ScalarMultipleKernels (CoeffsRealHomogeneous)
namespace IterTransposesOnFullSpace
theorem pauliCoeff_real_smul (z : ℝ) (a : Fin 3) (X : Matrices.ComplexMatrix2) :
    pauliCoeff a (z • X) = (z : ℂ) * pauliCoeff a X := by apply _root_.YangMills.Construction.Tower.IterTransposesOnTorus.pauliCoeff_real_smul <;> assumption
theorem vertexCoordinate_homogeneous (σ : Type) : CoeffsRealHomogeneous (vertexCoordinate σ) := by apply _root_.YangMills.Construction.Tower.IterTransposesOnTorus.vertexCoordinate_coeffsRealHomogeneous <;> assumption
theorem edgePauliCoordinates_homogeneous (L k j : ℕ) : CoeffsRealHomogeneous (edgePauliCoordinates L k j) := by
  intro z f
  funext ι
  exact pauliCoeff_real_smul z ι.1 (f ι.2.1)
theorem meshAt_self (L k : ℕ) : meshAt L k k = 1 := by
  simp [meshAt]
theorem inv_finestMesh_pow_four (L k : ℕ) :
    (finestMesh L k ^ 4)⁻¹ = (L : ℝ) ^ (4 * k) := by
  have e : finestMesh L k = ((L : ℝ) ^ k)⁻¹ := by
    simp [finestMesh, meshAt, zpow_neg]
  rw [e, inv_pow, inv_inv, ← pow_mul, Nat.mul_comm]
theorem mul_inv_pow_four (e : ℝ) (he : e ≠ 0) : e * (e ^ 4)⁻¹ = (e ^ 3)⁻¹ := by
  field_simp
theorem represents_of_eq {N N' : Type} {T T' : KernelMatrix N N'} {M : (N → ℂ) → N' → ℂ}
    (e : T' = T) (h : Represents T M) : Represents T' M :=
  e ▸ h
theorem meshTranspose_kernel (hM : ScalarMultipleKernels.Statement)
    (r r' : PauliComponentsOfSymmetricKernel) (m : (r.space.index → Matrices.ComplexMatrix2) → r'.space.index → Matrices.ComplexMatrix2)
    (hh : CoeffsRealHomogeneous r') (hk : PauliComponentsOfSymmetricKernel.HasLocalKernel r r' m)
    (ho : KernelUnique r.Index r'.Index) (a a' : ℝ) :
    meshTranspose a a' (r.kernel r' m) =
      ((a' ^ 4 * (a ^ 4)⁻¹ : ℝ) : ℂ) • swapKernel (r.kernel r' m) := by
  have h := (hM r r' m hh hk ho 1 a a').2
  have hfun : (fun f => (1 : ℝ) • m f) = m := by
    funext f
    exact one_smul _ _
  rw [hfun, one_mul] at h
  exact h
theorem claim_holds (hK : ThreeMapKernels.Claim)
    (hP : RowFiniteKernels.Claim)
    (hM : ScalarMultipleKernels.Statement) : Claim := by
  intro L hL k hk U hU
  have hL0 : (L : ℝ) ≠ 0 := by
    have := hL.2
    exact Nat.cast_ne_zero.mpr (by omega)
  have hη : finestMesh L k ≠ 0 := by
    unfold finestMesh meshAt
    exact zpow_ne_zero _ hL0
  obtain ⟨hOne, hD, -, hAv⟩ := (hK L hL k hk).2
  obtain ⟨hQ, hR⟩ := hAv U hU
  have hDU := hD U hU.1
  have hAct := hP.1
  have hR2 := meshTranspose_kernel hM _ _ (iterAdjointCubeAverage L k U k)
    (vertexCoordinate_homogeneous _) hR (hOne 0 k (Nat.zero_le k) le_rfl).1
    (finestMesh L k) (meshAt L k k)
  obtain ⟨hQ1, hQ2⟩ := hM _ _ (iterCovariantDeriv L k U k)
    (edgePauliCoordinates_homogeneous L k k) hQ (hOne 0 k (Nat.zero_le k) le_rfl).2.2.2
    (finestMesh L k) (finestMesh L k) (meshAt L k k)
  obtain ⟨hD1, hD2⟩ := hM _ _ (covDiff U)
    (edgePauliCoordinates_homogeneous L k 0) hDU (hOne 0 0 (Nat.zero_le k) (Nat.zero_le k)).2.1
    (finestMesh L k)⁻¹ (finestMesh L k) (finestMesh L k)
  have eRt : (rescaledOperators L k U).Rt =
      ((L : ℂ) ^ (4 * k)) • swapKernel (iterAverageKernel L k U) := by
    have c : ((meshAt L k k ^ 4 * (finestMesh L k ^ 4)⁻¹ : ℝ) : ℂ) =
        (L : ℂ) ^ (4 * k) := by
      rw [meshAt_self, one_pow, one_mul, inv_finestMesh_pow_four L k]
      push_cast
      rfl
    rw [← c]
    exact hR2
  have eQt : (rescaledOperators L k U).Qt =
      ((finestMesh L k : ℂ) ^ 3)⁻¹ •
        swapKernel (iterCovariantKernel L k U) := by
    have c : ((finestMesh L k * (meshAt L k k ^ 4 * (finestMesh L k ^ 4)⁻¹) : ℝ) : ℂ) =
        ((finestMesh L k : ℂ) ^ 3)⁻¹ := by
      rw [meshAt_self, one_pow, one_mul, mul_inv_pow_four _ hη, Complex.ofReal_inv,
        Complex.ofReal_pow]
    rw [← c]
    exact hQ2
  have rowsR : RowFinite (rescaledOperators L k U).R := hR.row_finite
  have rowsQ : RowFinite (rescaledOperators L k U).Q := by
    have h := hQ.smul_row_finite ((finestMesh L k : ℝ) : ℂ)
    rw [← hQ1] at h
    exact h
  have rowsD : RowFinite (rescaledOperators L k U).D := by
    have h := hDU.smul_row_finite (((finestMesh L k)⁻¹ : ℝ) : ℂ)
    rw [← hD1] at h
    exact h
  have rowsRt : RowFinite (rescaledOperators L k U).Rt := by
    rw [eRt]
    exact hR.smul_swap_row_finite _
  have rowsQt : RowFinite (rescaledOperators L k U).Qt := by
    rw [eQt]
    exact hQ.smul_swap_row_finite _
  have rowsDt : RowFinite (rescaledOperators L k U).Dt := by
    have h := hDU.smul_swap_row_finite
      (((finestMesh L k)⁻¹ * (finestMesh L k ^ 4 * (finestMesh L k ^ 4)⁻¹) : ℝ) : ℂ)
    rw [← hD2] at h
    exact h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact represents_of_eq eRt (hR.smul_swap_represents _)
  · exact represents_of_eq eQt (hQ.smul_swap_represents _)
  · exact ((hAct _ _ _ rowsQ).2 _ _ rowsQt).1
  · exact ((hAct _ _ _ rowsRt).2 _ _ rowsD).1
  · exact ((hAct _ _ _ rowsDt).2 _ _ rowsR).1
end IterTransposesOnFullSpace
end FullSpace
end Tower
end YangMills.Construction
end
