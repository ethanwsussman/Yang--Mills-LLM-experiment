import YangMills.Construction.Towers.BlocksOfTheTwoOperatorFunctionsDescendProof
import YangMills.Construction.Towers.MapsOfTheResponseAndTheirTransposes
import YangMills.Construction.Towers.TheCrossingAverageReadAtTheSideInfinity
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.CrossingSmoothingAtInfinity
open Set
open YangMills.Construction.Matrices
open YangMills.Construction.PeriodicOperators (RowFinite KernelMatrix applyKernel swapKernel)
open YangMills.Construction.Tower.PeriodicForm (coeffsOnEdges)
open YangMills.Construction.Tower.CriticalBranchResponse
open YangMills.Construction.Tower.FreeResolvents (trivialRescaledOperators)
open YangMills.Construction.LocalKernels
open YangMills.Construction.LocalKernels.Periodisation
open YangMills.Construction.Tower.OperatorBlocksDescend
open YangMills.Construction.Tower.ScalarMultipleKernels (CoeffsRealHomogeneous)
variable {L n k : ℕ}
theorem edgePauliCoordinates_coeffsRealHomogeneous (L k j : ℕ) :
    CoeffsRealHomogeneous (FullSpace.edgePauliCoordinates L k j) := by apply _root_.YangMills.Construction.Tower.FullSpace.IterTransposesOnFullSpace.edgePauliCoordinates_homogeneous <;> assumption
theorem applyKernel_kernelOnIdx (A A' : CellClass k) (T : KernelMatrix (ColourCell L A) (ColourCell L A'))
    (g : Idx L A.colourPairs → ℂ) (ι' : ColourCell L A') :
    applyKernel (kernelOnIdx L A A' T) g ⟨(), ι'⟩ =
      applyKernel T (fun ι => g ⟨(), ι⟩) ι' := by
  let e : ColourCell L A ≃ Idx L A.colourPairs :=
    { toFun := fun ι => ⟨(), ι⟩
      invFun := fun ι => ι.2
      left_inv := fun _ => rfl
      right_inv := fun ⟨⟨⟩, _⟩ => rfl }
  exact (e.tsum_eq (fun ι => kernelOnIdx L A A' T ⟨(), ι'⟩ ι * g ι)).symm
theorem applyKernel_smul {N N' : Type} (c : ℂ) (T : KernelMatrix N N') (g : N → ℂ) :
    applyKernel (c • T) g = c • applyKernel T g := by apply _root_.YangMills.Construction.Tower.OperatorBlocksDescend.applyKernel_smul <;> assumption
theorem meshAt_self (L k : ℕ) : meshAt L k k = 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.IterTransposesOnFullSpace.meshAt_self <;> assumption
theorem const_one_mem_fieldSpace (L n k : ℕ) : (fun _ => (1 : ComplexMatrix2)) ∈ fieldSpace L n k 0 := by
  refine ⟨fun _ _ => (1 : ComplexMatrix2.specialUnitary).2, fun _ _ => ?_⟩
  simp
theorem claim_holds (hB : OperatorBlocksDescend.BlocksDescend)
    (hMaps : ResponseMaps.ResponseMapsHold)
    (hAt : TrivialFieldAverages.AtTrivialField)
    (hK : ThreeMapKernels.Claim)
    (hM : ScalarMultipleKernels.Statement)
    (hOne : FullSpace.RescaledTrivialSteps) :
    Claim := by
  intro L hL k hk n hn
  have hL0 : (L : ℝ) ≠ 0 := by
    have := hL.2
    exact Nat.cast_ne_zero.mpr (by omega)
  have hη : finestMesh L k ≠ 0 := by
    unfold finestMesh meshAt
    exact zpow_ne_zero _ hL0
  have hηc : (finestMesh L k : ℂ) ≠ 0 := by exact_mod_cast hη
  obtain ⟨hOneK, -, -, hAv⟩ := (hK L hL k hk).2
  obtain ⟨hQ, -⟩ := hAv _ (hOne L hL k hk).1
  obtain ⟨eQ, eQt⟩ := hM _ _ (FullSpace.iterCovariantDeriv L k (fun _ => 1) k)
    (edgePauliCoordinates_coeffsRealHomogeneous L k k) hQ (hOneK 0 k (Nat.zero_le k) le_rfl).2.2.2
    (finestMesh L k) (finestMesh L k) (meshAt L k k)
  have eQ' : (trivialRescaledOperators L k).Q =
      ((finestMesh L k : ℝ) : ℂ) • FullSpace.iterCovariantKernel L k (fun _ => 1) := eQ
  have eQt' : (trivialRescaledOperators L k).Qt =
      (((finestMesh L k : ℂ) ^ 3)⁻¹) •
        swapKernel (FullSpace.iterCovariantKernel L k (fun _ => 1)) := by
    have c : ((finestMesh L k * (meshAt L k k ^ 4 * (finestMesh L k ^ 4)⁻¹) : ℝ) : ℂ) =
        ((finestMesh L k : ℂ) ^ 3)⁻¹ := by
      rw [meshAt_self]
      push_cast
      field_simp
    rw [← c]
    exact eQt
  have hMapsT := hMaps L hL k n hk hn
  have hvals : ∀ A : edgeFormSpace L n k 0, (crossingSmoothingToTop L n k A : Edge L n k k → ComplexMatrix2) =
      iterCovariantDeriv L n k (fun _ => 1) k A := fun A =>
    (hMapsT.crossing_eq A).trans
      ((((hAt L hL).1 n k hn hk).2.1 k le_rfl).1 A A.2).2.1.symm
  have hspec : ∀ A : edgeFormSpace L n k 0,
      (iterCovariantDerivLinear L n k (fun _ => 1) A : Edge L n k k → ComplexMatrix2) =
        iterCovariantDeriv L n k (fun _ => 1) k A :=
    Classical.epsilon_spec
      (p := fun T : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k k => ∀ A : edgeFormSpace L n k 0,
        (T A : Edge L n k k → ComplexMatrix2) = iterCovariantDeriv L n k (fun _ => 1) k A)
      ⟨_, hvals⟩
  have hlin : crossingSmoothingToTop L n k = iterCovariantDerivLinear L n k (fun _ => 1) :=
    LinearMap.ext fun A => Subtype.ext ((hvals A).trans (hspec A).symm)
  have htr : crossingSmoothingTranspose L n k =
      iterCovariantDerivTranspose L n k (fun _ => 1) := by
    unfold crossingSmoothingTranspose iterCovariantDerivTranspose
    rw [hlin]
  have hAtOne := (hB L hL k hk n hn).self_of_nhdsWithin (const_one_mem_fieldSpace L n k)
  have hHolds := hAtOne.2 0 0
  obtain ⟨M, hMat, hDesc⟩ := hHolds.iterCovariant_descends
  obtain ⟨M', hMat', hDesc'⟩ := hHolds.iterCovariant_swap_descends
  refine ⟨?_, ?_, hMapsT.crossing_eq, ?_, ?_⟩
  · rw [eQ']
    exact hQ.smul_row_finite _
  · rw [eQt']
    exact hQ.smul_swap_row_finite _
  · intro A
    have hact : applyKernel (trivialRescaledOperators L k).Q (coeffsOnEdges L n k 0 A) =
        (finestMesh L k : ℂ) • applyKernel (FullSpace.iterCovariantKernel L k (fun _ => 1))
          (coeffsOnEdges L n k 0 A) :=
      (congrArg (fun T => applyKernel T (coeffsOnEdges L n k 0 A)) eQ').trans (applyKernel_smul _ _ _)
    refine Eq.trans ?_ hact.symm
    funext ι'
    have h₁ := congrFun (hDesc.2 (CellClass.quotCoeffsOn L n (edgesAtZero k) A.1)) ⟨(), ι'⟩
    have h₂ := applyKernel_kernelOnIdx (L := L) (edgesAtZero k) (edgesAtTop k)
      (FullSpace.iterCovariantKernel L k (fun _ => 1))
      ((edgesAtZero k).colourPairs.lift L n (CellClass.quotCoeffsOn L n (edgesAtZero k) A.1)) ι'
    have h₃ := congrFun (hMat A) ((edgesAtTop k).colourPairs.proj L n ⟨(), ι'⟩)
    rw [hlin]
    exact congrArg (fun z => (finestMesh L k : ℂ) * z) (h₃.trans (h₁.symm.trans h₂))
  · intro μ
    have hact : applyKernel (trivialRescaledOperators L k).Qt (coeffsOnEdges L n k k μ) =
        (((finestMesh L k : ℂ) ^ 3)⁻¹) •
          applyKernel (swapKernel (FullSpace.iterCovariantKernel L k (fun _ => 1)))
            (coeffsOnEdges L n k k μ) :=
      (congrArg (fun T => applyKernel T (coeffsOnEdges L n k k μ)) eQt').trans (applyKernel_smul _ _ _)
    rw [hact, smul_smul, mul_inv_cancel₀ (pow_ne_zero 3 hηc), one_smul, htr]
    funext ι
    have h₁ := congrFun (hDesc'.2 (CellClass.quotCoeffsOn L n (edgesAtTop k) μ.1)) ⟨(), ι⟩
    have h₂ := applyKernel_kernelOnIdx (L := L) (edgesAtTop k) (edgesAtZero k)
      (swapKernel (FullSpace.iterCovariantKernel L k (fun _ => 1)))
      ((edgesAtTop k).colourPairs.lift L n (CellClass.quotCoeffsOn L n (edgesAtTop k) μ.1)) ι
    have h₃ := congrFun (hMat' μ) ((edgesAtZero k).colourPairs.proj L n ⟨(), ι⟩)
    exact h₃.trans (h₁.symm.trans h₂)
end YangMills.Construction.Tower.CrossingSmoothingAtInfinity
end
