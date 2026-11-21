import YangMills.Construction.Towers.KernelAlgebraOfTheScaledPicture
import YangMills.Construction.Towers.KernelsOfTheScaledOperatorsAtEveryComplexConfiguration
import YangMills.Construction.Towers.RelationsOfTheIteratedAveragesOfTheScaledPictureOnTheWhole
import YangMills.Construction.Towers.SaddleOperatorsOfTheScaledPictureOnTheWhole
import YangMills.Construction.Towers.TheBackgroundKernelAtZeroProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.SaddleScalingProof
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Matrices
open YangMills.Construction.Tower.RescaledConditions (SaddleScaling sumDiagScale gaugeFixedKernel)
section Kernels
variable {N N' N'' : Type}
theorem compKernel_smul_smul (a b : ℂ) (T : N' → N → ℂ) (S : N → N'' → ℂ) :
    compKernel (a • T) (b • S) = (a * b) • compKernel T S := by
  funext i j
  simp only [compKernel, Pi.smul_apply, smul_eq_mul]
  rw [← tsum_mul_left]
  exact tsum_congr fun m => by ring
theorem applyKernel_smul (T : KernelMatrix N N') (z : ℂ) (f : N → ℂ) :
    applyKernel T (z • f) = z • applyKernel T f := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.applyKernel_smul <;> assumption
theorem kernelPairing_smul_of_finite (T : KernelMatrix N N) (z : ℂ) (c : N → ℂ)
    (hc : (Function.support c).Finite) :
    kernelPairing (fun _ => (1 : ℝ)) (z • T) c c = z * ∑' i, c i * applyKernel T c i := by
  classical
  set s := hc.toFinset with hs
  have off : ∀ i, i ∉ s → c i = 0 := fun i hi => by
    by_contra h
    exact hi (hc.mem_toFinset.2 h)
  have act : ∀ i, applyKernel T c i = ∑ j ∈ s, T i j * c j := fun i =>
    tsum_eq_sum fun j hj => by rw [off j hj, mul_zero]
  have rhs : ∑' i, c i * applyKernel T c i = ∑ i ∈ s, c i * applyKernel T c i :=
    tsum_eq_sum fun i hi => by rw [off i hi, zero_mul]
  have lhs : kernelPairing (fun _ => (1 : ℝ)) (z • T) c c =
      ∑ p ∈ s ×ˢ s, (((1 : ℝ) : ℂ)) * c p.1 * (z • T) p.1 p.2 * c p.2 := by
    unfold kernelPairing
    refine finsum_eq_sum_of_support_subset _ fun p hp => ?_
    have h₁ : c p.1 ≠ 0 := fun h => hp (by simp [h])
    have h₂ : c p.2 ≠ 0 := fun h => hp (by simp [h])
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe]
    exact ⟨hc.mem_toFinset.2 h₁, hc.mem_toFinset.2 h₂⟩
  rw [lhs, rhs, Finset.sum_product, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [act i, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_one]
  ring
theorem wPairing_inv_smul {σ : Type} (η : ℝ) (hη : η ≠ 0)
    (T : KernelMatrix (Fin 3 × σ) (Fin 3 × σ)) (c : Fin 3 × σ → ℂ) :
    PeriodicOperators.wPairing (meshWeight η) (((η⁻¹ : ℝ) : ℂ) • c)
        (applyKernel T (((η⁻¹ : ℝ) : ℂ) • c)) =
      (η : ℂ) ^ 2 * ∑' i, c i * applyKernel T c i := by
  have hc : (η : ℂ) ≠ 0 := by exact_mod_cast hη
  unfold PeriodicOperators.wPairing
  rw [applyKernel_smul, ← tsum_mul_left]
  refine tsum_congr fun i => ?_
  simp only [meshWeight, Pi.smul_apply, smul_eq_mul, Complex.ofReal_pow, Complex.ofReal_inv]
  field_simp
end Kernels
theorem saddleScaling_of_multiples {S₀ B₀ S B : Type} (p : RescaledOperators S₀ B₀ S B)
    (Xk : KernelMatrix (Fin 3 × B₀) (Fin 3 × B₀))
    (Qk : KernelMatrix (Fin 3 × B₀) (Fin 3 × B))
    (Dk : KernelMatrix (Fin 3 × S₀) (Fin 3 × B₀))
    (Rk : KernelMatrix (Fin 3 × S₀) (Fin 3 × S)) (hη : (p.eta : ℂ) ≠ 0)
    (hX : ((p.eta : ℂ) ^ 2) • p.X = Xk)
    (hQ : p.Q = (p.eta : ℂ) • Qk)
    (hQt : p.Qt = ((p.eta : ℂ) ^ 3)⁻¹ • swapKernel Qk)
    (hD : p.D = (p.eta : ℂ)⁻¹ • Dk)
    (hDt : p.Dt = (p.eta : ℂ)⁻¹ • swapKernel Dk)
    (hR : p.R = Rk)
    (hRt : p.Rt = ((p.eta : ℂ) ^ 4)⁻¹ • swapKernel Rk) :
    SaddleScaling p (saddleMatrix Xk (swapKernel Qk) Qk)
      (saddleMatrix (compKernel (swapKernel Dk) Dk) (swapKernel Rk) Rk) := by
  constructor
  · funext m' m
    rcases m' with i' | c' <;> rcases m with i | c
    · show Xk i' i = (p.eta : ℂ) ^ 2 * p.X i' i * 1
      rw [← hX]
      simp
    · show swapKernel Qk i' c = (p.eta : ℂ) ^ 2 * p.Qt i' c * (p.eta : ℂ)
      rw [hQt]
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp
    · show Qk c' i = (p.eta : ℂ)⁻¹ * p.Q c' i * 1
      rw [hQ]
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp
    · show (0 : ℂ) = (p.eta : ℂ)⁻¹ * 0 * (p.eta : ℂ)
      simp
  · funext m' m
    rcases m' with i' | c' <;> rcases m with i | c
    · show compKernel (swapKernel Dk) Dk i' i = (p.eta : ℂ) ^ 2 * p.Delta i' i * 1
      have e : p.Delta = ((p.eta : ℂ)⁻¹ * (p.eta : ℂ)⁻¹) • compKernel (swapKernel Dk) Dk := by
        show compKernel p.Dt p.D = _
        rw [hDt, hD, compKernel_smul_smul]
      rw [e]
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp
    · show swapKernel Rk i' c = (p.eta : ℂ) ^ 2 * p.Rt i' c * (p.eta : ℂ) ^ 2
      rw [hRt]
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp
    · show Rk c' i = 1 * p.R c' i * 1
      rw [hR]
      simp
    · show (0 : ℂ) = 1 * 0 * (p.eta : ℂ) ^ 2
      simp
section Coefficients
theorem pauliCoeff_zero (a : Fin 3) : pauliCoeff a (0 : ComplexMatrix2) = 0 := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_zero <;> assumption
theorem vertexCoordinate_homogeneous (σ : Type) :
    ScalarMultipleKernels.CoeffsRealHomogeneous (vertexCoordinate σ) := by apply _root_.YangMills.Construction.Tower.IterTransposesOnTorus.vertexCoordinate_coeffsRealHomogeneous <;> assumption
theorem edgePauliCoordinates_homogeneous (L k j : ℕ) :
    ScalarMultipleKernels.CoeffsRealHomogeneous (edgePauliCoordinates L k j) := by apply _root_.YangMills.Construction.Tower.FullSpace.IterTransposesOnFullSpace.edgePauliCoordinates_homogeneous <;> assumption
theorem toPauliCoeffs_support_finite {σ : Type} {f : σ → ComplexMatrix2} (hf : HasFiniteSupp f) :
    (Function.support (toPauliCoeffs f)).Finite := by
  refine (Set.finite_univ.prod hf).subset fun m hm => ⟨Set.mem_univ _, fun h0 => hm ?_⟩
  show pauliCoeff m.1 (f m.2) = 0
  rw [h0, pauliCoeff_zero]
theorem real_smul_eq_complex_smul {ι : Type} (r : ℝ) (f : ι → ComplexMatrix2) :
    r • f = (r : ℂ) • f := by apply _root_.YangMills.SharedProofs.p7664 <;> assumption
end Coefficients
section Forms
variable {L k : ℕ}
open HessianKernel (finiteSupportComplexForms)
theorem basisForm_mem
    (hx : ∀ b : Edge L k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (a : Fin 3) (b : PositiveEdge (meshAt L k 0)) :
    basisForm a b ∈ finiteSupportComplexForms L k 0 := by
  classical
  refine ⟨?_, ?_⟩
  · unfold basisForm
    refine ⟨fun b' hb' => ?_, fun b' => ?_⟩
    · simp only [extendOddly, if_pos hb']
      split_ifs
      · have : Matrix.trace (ComplexMatrix2.pauliFamily a) = 0 := by
          fin_cases a <;>
            simp [ComplexMatrix2.pauliFamily, OneLoop.pauliX, OneLoop.pauliY,
              OneLoop.pauliZ, Matrix.trace_fin_two]
        exact this
      · exact ComplexMatrix2.traceless.zero_mem
    · rcases hx b' with h | h
      · simp only [extendOddly, if_pos h.1, if_neg h.2]
        rfl
      · simp only [extendOddly, if_pos h.1, if_neg h.2, neg_neg]
  · refine (Set.finite_singleton b.1).subset fun b' hb' => ?_
    by_contra hne
    apply hb'.2
    have hne' : b' ≠ b.1 := hne
    simp only [basisForm, extendOddly, if_pos hb'.1, if_neg hne']
theorem real_smul_mem_finiteSupport (r : ℝ) {B : Edge L k 0 → ComplexMatrix2}
    (hB : B ∈ finiteSupportComplexForms L k 0) : r • B ∈ finiteSupportComplexForms L k 0 := by
  refine ⟨?_, hB.2.subset fun b hb => ⟨hb.1, fun h0 => ?_⟩⟩
  · rw [real_smul_eq_complex_smul]
    exact (complexEdgeForms _).smul_mem _ hB.1
  · apply hb.2
    simp [h0]
theorem sourceForm_zero (U B : Edge L k 0 → ComplexMatrix2) :
    sourceForm U 0 (0 : Edge L k k → ComplexMatrix2) B = 0 := by apply _root_.YangMills.Construction.Tower.FullSpace.KernelAtZeroSources.sourceForm_zero <;> assumption
end Forms
theorem eta_sq_smul_X_eq_backgroundKernel {L k : ℕ}
    (h₁ : RescaledIterRelations)
    (h₂ : RescaledKernelAlgebra.Claim)
    (h₃ : RescaledKernels.KernelsWellFormedEverywhere)
    (h₄ : HessianKernel.KernelProperties)
    (h₅ : KernelAtZeroSources.ZeroSourceKernel)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) {U : Edge L k 0 → ComplexMatrix2}
    (hU : U ∈ smallIterateFields L k) :
    (((rescaledOperators L k U).eta : ℂ) ^ 2) • (rescaledOperators L k U).X =
      backgroundKernel L k U := by
  classical
  have hpos : ∀ j, 0 < meshAt L k j := fun j => by
    have h0 : (0 : ℝ) < L := by
      have := hL.2
      have : 0 < L := by omega
      exact_mod_cast this
    exact zpow_pos h0 _
  have hη : 0 < finestMesh L k := hpos 0
  have hx : ∀ b : Edge L k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    fun b => by
    rcases InfiniteLattice.xor_mem_positiveLinks (hpos 0) b with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨InfiniteLattice.mem_positiveLinks_iff.1 h₁,
        fun h => h₂ (InfiniteLattice.mem_positiveLinks_iff.2 h)⟩
    · exact Or.inr ⟨InfiniteLattice.mem_positiveLinks_iff.1 h₁,
        fun h => h₂ (InfiniteLattice.mem_positiveLinks_iff.2 h)⟩
  have rel := h₁ L hL k hk U hU
  have con : RescaledKernelAlgebra.ProjectionConsequences (rescaledOperators L k U) :=
    h₂ _ _ _ _ _ hη (hpos k)
      ⟨rel.row_finite.2.2.1, rel.row_finite.2.2.2.2.2, rel.row_finite.1,
        rel.row_finite.2.2.2.2.1, ((h₃ L hL k hk).2 U hU.1).H_rowFinite⟩ rel.R_comp_Rt
  obtain ⟨bil, -⟩ := (h₄ L hL k 0 (Nat.zero_le _)).2 U hU.1
  have hH : ∀ m m', (rescaledOperators L k U).H m m' = (rescaledOperators L k U).H m' m :=
    fun m m' => by
    have m₁ := real_smul_mem_finiteSupport (finestMesh L k) (basisForm_mem hx m.1 m.2)
    have m₂ := real_smul_mem_finiteSupport (finestMesh L k) (basisForm_mem hx m'.1 m'.2)
    show (((finestMesh L k ^ 4)⁻¹ : ℝ) : ℂ) * complexActionHessian U _ _ =
      (((finestMesh L k ^ 4)⁻¹ : ℝ) : ℂ) * complexActionHessian U _ _
    rw [(bil 0 _ m₁ _ m₁ _ m₂).2.2]
  have hX : ∀ m m', (rescaledOperators L k U).X m m' = (rescaledOperators L k U).X m' m :=
    fun m m' => by
    rw [con.X_eq]
    show (rescaledOperators L k U).H m m' + RescaledKernelAlgebra.gaugeCorrection _ m m' =
      (rescaledOperators L k U).H m' m + RescaledKernelAlgebra.gaugeCorrection _ m' m
    rw [hH, con.correction_symm]
  refine (h₅ L hL k hk U hU).2.2.2.2.2.2.1 _ ⟨?_, fun B hB hf => ?_⟩
  · funext m m'
    show (((1 : ℝ) / 1 : ℝ) : ℂ) * (_ * (rescaledOperators L k U).X m' m) =
      _ * (rescaledOperators L k U).X m m'
    rw [hX m' m]
    simp
  · have hc : (Function.support ((edgePauliCoordinates L k 0).coeffs B)).Finite :=
      toPauliCoeffs_support_finite hf
    refine (kernelPairing_smul_of_finite _ _ _ hc).trans ?_
    have hb' : (finestMesh L k)⁻¹ • B ∈ (edgePauliCoordinates L k 0).space.complexSubmodule := by
      rw [real_smul_eq_complex_smul]
      exact (complexEdgeForms _).smul_mem _ hB
    have hf' : (edgePauliCoordinates L k 0).space.IsFinitelySupported ((finestMesh L k)⁻¹ • B) := by
      refine Set.Finite.subset hf fun b hb h0 => hb ?_
      show (finestMesh L k)⁻¹ • B b.1 = 0
      have h0' : B b.1 = 0 := h0
      rw [h0', smul_zero]
    have back : (rescaledOperators L k U).eta • (finestMesh L k)⁻¹ • B = B := by
      show finestMesh L k • (finestMesh L k)⁻¹ • B = B
      rw [smul_smul, mul_inv_cancel₀ hη.ne', one_smul]
    have ec : (edgePauliCoordinates L k 0).coeffs ((finestMesh L k)⁻¹ • B) =
        (((finestMesh L k)⁻¹ : ℝ) : ℂ) • (edgePauliCoordinates L k 0).coeffs B :=
      edgePauliCoordinates_homogeneous L k 0 _ B
    have key : backgroundForm L k U B B = ((finestMesh L k : ℂ) ^ 2) *
        ∑' i, (edgePauliCoordinates L k 0).coeffs B i *
          applyKernel (rescaledOperators L k U).X ((edgePauliCoordinates L k 0).coeffs B) i :=
      (congrArg₂ (backgroundForm L k U) back.symm back.symm).trans
        ((rel.background_eq _ hb' hf').trans ((congrArg (fun c' =>
          PeriodicOperators.wPairing (meshWeight (rescaledOperators L k U).eta) c'
            (applyKernel (gaugeFixedKernel (rescaledOperators L k U)) c')) ec).trans
          ((congrArg (fun T => PeriodicOperators.wPairing
              (meshWeight (rescaledOperators L k U).eta)
              ((((finestMesh L k)⁻¹ : ℝ) : ℂ) • (edgePauliCoordinates L k 0).coeffs B)
              (applyKernel T ((((finestMesh L k)⁻¹ : ℝ) : ℂ) •
                (edgePauliCoordinates L k 0).coeffs B))) con.X_eq.symm).trans
            (wPairing_inv_smul _ hη.ne' _ _))))
    refine key.symm.trans ?_
    show _ = backgroundForm L k U B B + sourceForm U 0 0 B
    rw [sourceForm_zero, add_zero]
theorem rescaledSaddleScaling_holds (h₁ : RescaledIterRelations)
    (h₂ : RescaledKernelAlgebra.Claim)
    (h₃ : ScalarMultipleKernels.Statement)
    (h₄ : ThreeMapKernels.Claim)
    (h₅ : RescaledKernels.KernelsWellFormedEverywhere)
    (h₆ : HessianKernel.KernelProperties)
    (h₇ : KernelAtZeroSources.ZeroSourceKernel) : RescaledSaddleScaling := by
  intro L hL k hk U hU
  have hpos : ∀ j, 0 < meshAt L k j := fun j => by
    have h0 : (0 : ℝ) < L := by
      have := hL.2
      have : 0 < L := by omega
      exact_mod_cast this
    exact zpow_pos h0 _
  have hη : 0 < finestMesh L k := hpos 0
  have hηc : ((finestMesh L k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
  have htop : meshAt L k k = 1 := by simp [meshAt]
  have K := (h₄ L hL k hk).2
  have Dk := K.2.1 U hU.1
  obtain ⟨Qk, Rk⟩ := K.2.2.2 U hU
  obtain ⟨mD, tD⟩ := h₃ (vertexCoordinate (Vertex L k 0)) (edgePauliCoordinates L k 0) _
    (edgePauliCoordinates_homogeneous L k 0) Dk (K.1 0 0 (Nat.zero_le _) (Nat.zero_le _)).2.1
    (finestMesh L k)⁻¹ (finestMesh L k) (finestMesh L k)
  obtain ⟨mQ, tQ⟩ := h₃ (edgePauliCoordinates L k 0) (edgePauliCoordinates L k k) _
    (edgePauliCoordinates_homogeneous L k k) Qk (K.1 0 k (Nat.zero_le _) le_rfl).2.2.2
    (finestMesh L k) (finestMesh L k) (meshAt L k k)
  obtain ⟨-, tR⟩ := h₃ (vertexCoordinate (Vertex L k 0)) (vertexCoordinate (Vertex L k k)) _
    (vertexCoordinate_homogeneous _) Rk (K.1 0 k (Nat.zero_le _) le_rfl).1
    1 (finestMesh L k) (meshAt L k k)
  have tR' : (rescaledOperators L k U).Rt =
      (((1 : ℝ) * (meshAt L k k ^ 4 * (finestMesh L k ^ 4)⁻¹) : ℝ) : ℂ) •
        swapKernel (iterAverageKernel L k U) := by
    have e : (vertexCoordinate (Vertex L k 0)).kernel (vertexCoordinate (Vertex L k k))
        (fun f => (1 : ℝ) • iterAdjointCubeAverage L k U k f) = iterAverageKernel L k U :=
      congrArg ((vertexCoordinate (Vertex L k 0)).kernel (vertexCoordinate (Vertex L k k)))
        (funext fun f => one_smul ℝ _)
    exact (congrArg (meshTranspose (finestMesh L k) (meshAt L k k)) e.symm).trans tR
  refine saddleScaling_of_multiples (rescaledOperators L k U) _ _ _ _ hηc
    (eta_sq_smul_X_eq_backgroundKernel h₁ h₂ h₅ h₆ h₇ hL hk hU) mQ ?_ ?_ ?_ rfl ?_
  · have c : ((finestMesh L k * (meshAt L k k ^ 4 * (finestMesh L k ^ 4)⁻¹) : ℝ) : ℂ) =
        ((finestMesh L k : ℂ) ^ 3)⁻¹ := by
      rw [htop]
      push_cast
      field_simp
    exact tQ.trans (congrArg (fun z : ℂ => z • swapKernel (iterCovariantKernel L k U)) c)
  · exact mD.trans (by push_cast; rfl)
  · have c : (((finestMesh L k)⁻¹ * (finestMesh L k ^ 4 * (finestMesh L k ^ 4)⁻¹) : ℝ) : ℂ) =
        (finestMesh L k : ℂ)⁻¹ := by
      push_cast
      field_simp
    exact tD.trans
      (congrArg (fun z : ℂ => z • swapKernel (covDiffKernel L k 0 U)) c)
  · have c : (((1 : ℝ) * (meshAt L k k ^ 4 * (finestMesh L k ^ 4)⁻¹) : ℝ) : ℂ) =
        ((finestMesh L k : ℂ) ^ 4)⁻¹ := by
      rw [htop]
      push_cast
      field_simp
    exact tR'.trans
      (congrArg (fun z : ℂ => z • swapKernel (iterAverageKernel L k U)) c)
end YangMills.Construction.Tower.FullSpace.SaddleScalingProof
end
