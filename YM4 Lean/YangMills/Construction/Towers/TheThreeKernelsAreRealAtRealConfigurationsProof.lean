import YangMills.Construction.Towers.KernelsOfPeriodicLocalBilinearMapsProof
import YangMills.Construction.Towers.BlocksOfTheTwoOperatorFunctionsDescendProof
import YangMills.Construction.Towers.TheEntriesOfTheBackgroundKernelAreRealAtRealDataProof
import YangMills.Construction.Towers.TheResponseOperatorsProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.RealKernels
open YangMills.Construction.PeriodicOperators YangMills.Construction.Matrices
theorem eq_sum_pauliCoeff_smul {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    X = ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a := by apply _root_.YangMills.Construction.Tower.NearIdentityStepKernels.eq_sum_pauliCoeff_smul <;> assumption
theorem pauliCoeff_im_eq_zero {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.hermitianTraceless)
    (a : Fin 3) : (pauliCoeff a X).im = 0 := by apply _root_.YangMills.SharedProofs.p23717 <;> assumption
theorem sum_smul_pauliFamily_mem {x : Fin 3 → ℂ} (hx : ∀ a, (x a).im = 0) :
    ∑ a, x a • ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.Construction.Tower.ResponseOperators.sum_smul_pauliFamily_mem_hermitianTraceless <;> assumption
theorem mem_hermitianTraceless_of_im_eq_zero {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) (h : ∀ a, (pauliCoeff a X).im = 0) :
    X ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.Construction.Tower.OperatorBlocksDescend.mem_hermitianTraceless_of_im <;> assumption
theorem extendOddly_mem {a : ℝ} (ha : 0 < a) {f : InfiniteLattice.Link a → ComplexMatrix2}
    (hf : ∀ b : InfiniteLattice.Link a, b.IsPositivelyOriented →
      f b ∈ ComplexMatrix2.hermitianTraceless) :
    extendOddly f ∈ edgeFormSpace a := by apply _root_.YangMills.Construction.Tower.FullSpace.RealBackgroundKernel.extendOddly_mem <;> assumption
theorem covDiff_mem {a : ℝ} (ha : 0 < a) {U : InfiniteLattice.Link a → ComplexMatrix2}
    (hU : IsFieldIn PeriodicLattice.compactGaugeGroup U)
    {l : InfiniteLattice.LatticePoint a → ComplexMatrix2}
    (hl : l ∈ vertexFunctionSpace a) : covDiff U l ∈ edgeFormSpace a := by apply _root_.YangMills.Construction.Tower.FullSpace.RealBackgroundKernel.covDiff_mem <;> assumption
structure PreservesReal (r : PauliComponentsOfSymmetricKernel) : Prop where
  ofCoeffs_mem : ∀ c : r.Index → ℂ, (∀ ι, (c ι).im = 0) → r.ofCoeffs c ∈ r.space.realSubmodule
  coeffs_im_eq_zero : ∀ f ∈ r.space.realSubmodule, ∀ ι, (r.coeffs f ι).im = 0
  ofCoeffs_coeffs : ∀ f ∈ r.space.realSubmodule, r.ofCoeffs (r.coeffs f) = f
theorem preservesReal_vertexRepresentation (σ : Type) : PreservesReal (vertexCoordinate σ) where
  ofCoeffs_mem _ hc := fun x _ => sum_smul_pauliFamily_mem fun a => hc (a, x)
  coeffs_im_eq_zero _ hf ι := pauliCoeff_im_eq_zero (hf _ (Set.mem_univ _)) ι.1
  ofCoeffs_coeffs _ hf := funext fun x =>
    (eq_sum_pauliCoeff_smul (hf x (Set.mem_univ _)).2).symm
theorem preservesReal_edgeRepresentation {L k j : ℕ} (hs : 0 < meshAt L k j) :
    PreservesReal (edgePauliCoordinates L k j) where
  ofCoeffs_mem c hc := by
    unfold edgePauliCoordinates
    dsimp only
    refine extendOddly_mem hs fun b hb => ?_
    simp only [dif_pos hb]
    exact sum_smul_pauliFamily_mem fun a => hc (a, ⟨b, hb⟩)
  coeffs_im_eq_zero f hf ι := pauliCoeff_im_eq_zero (hf.1 ι.2.1 ι.2.2) ι.1
  ofCoeffs_coeffs f hf := by
    funext b
    unfold edgePauliCoordinates
    dsimp only
    by_cases hb : b.IsPositivelyOriented
    · simp only [extendOddly, if_pos hb, dif_pos hb]
      exact (eq_sum_pauliCoeff_smul (hf.1 b hb).2).symm
    · have hop := InfiniteLattice.PeriodSublattice.isPositivelyOriented_opposite_of_not hb
      simp only [extendOddly, if_neg hb, dif_pos hop]
      have hval : ofPauliCoeffs (toPauliCoeffs (restrictToPositiveEdges f)) ⟨b.opposite, hop⟩ =
          f b.opposite :=
        (eq_sum_pauliCoeff_smul (hf.1 b.opposite hop).2).symm
      rw [hval, hf.2 b, neg_neg]
def basisVec {N : Type} (ι : N) : N → ℂ :=
  open Classical in fun ι₀ => if ι₀ = ι then 1 else 0
theorem basisVec_im {N : Type} (ι ι₀ : N) : (basisVec ι ι₀).im = 0 := by
  classical
  unfold basisVec
  split_ifs <;> simp
theorem applyKernel_basisVec {N N' : Type} (T : KernelMatrix N N') (ι : N) (ι' : N') :
    applyKernel T (basisVec ι) ι' = T ι' ι := by apply _root_.YangMills.Construction.LocalKernels.LocalBilinearKernels.applyKernel_pointIndicator <;> assumption
theorem kernel_im_eq_zero {r r' : PauliComponentsOfSymmetricKernel} (hr : PreservesReal r) (hr' : PreservesReal r')
    {m : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2}
    (H : Represents (r.kernel r' m) (PauliComponentsOfSymmetricKernel.mapOnCoeffs r r' m))
    (hm : ∀ f ∈ r.space.realSubmodule, m f ∈ r'.space.realSubmodule) (ι' : r'.Index)
    (ι : r.Index) : (r.kernel r' m ι' ι).im = 0 := by
  have hentry := (applyKernel_basisVec _ ι ι').symm.trans (congrFun (H (basisVec ι)).2 ι')
  rw [hentry]
  exact hr'.coeffs_im_eq_zero _ (hm _ (hr.ofCoeffs_mem _ (basisVec_im ι))) ι'
theorem applyKernel_im_eq_zero {N N' : Type} {T : KernelMatrix N N'} {c : N → ℂ}
    (hT : ∀ ι' ι, (T ι' ι).im = 0) (hc : ∀ ι, (c ι).im = 0) (hsum : ApplySummable T c)
    (ι' : N') : (applyKernel T c ι').im = 0 := by
  unfold applyKernel
  rw [Complex.im_tsum (hsum ι').of_norm]
  simp [Complex.mul_im, hT, hc]
theorem transposeOfValues_mem (S S' : PairedFunctionSpace)
    (m : (S.index → ComplexMatrix2) → S'.index → ComplexMatrix2)
    (g : S'.index → ComplexMatrix2) :
    PairedFunctionSpace.transposeOfValues S S' m g ∈ S.complexSubmodule := by apply _root_.YangMills.Construction.Tower.FullSpace.ComplexFieldRescaledRelations.transposeOfValues_mem <;> assumption
theorem transposeOfValues_mem_real {σ : Type} {r' : PauliComponentsOfSymmetricKernel} (hr' : PreservesReal r')
    {m : ((vertexCoordinate σ).space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2}
    (Ht : Represents (swapKernel ((vertexCoordinate σ).kernel r' m))
      (PauliComponentsOfSymmetricKernel.transposeOnCoeffs (vertexCoordinate σ) r' m))
    (hT : ∀ ι' ι, ((vertexCoordinate σ).kernel r' m ι' ι).im = 0)
    {g : r'.space.index → ComplexMatrix2} (hg : g ∈ r'.space.realSubmodule) :
    PairedFunctionSpace.transposeOfValues (pairedFunctions σ) r'.space m g ∈
      GroupLieProduct.hermitianTracelessFunctions σ := by
  have hrep := Ht (r'.coeffs g)
  have hcoeffs : PauliComponentsOfSymmetricKernel.transposeOnCoeffs (vertexCoordinate σ) r' m (r'.coeffs g) =
      toPauliCoeffs (PairedFunctionSpace.transposeOfValues (pairedFunctions σ) r'.space m g) := by
    show toPauliCoeffs (PairedFunctionSpace.transposeOfValues (pairedFunctions σ) r'.space m
      (r'.ofCoeffs (r'.coeffs g))) = _
    rw [hr'.ofCoeffs_coeffs g hg]
  intro x _
  refine mem_hermitianTraceless_of_im_eq_zero
    ((transposeOfValues_mem (pairedFunctions σ) r'.space m g) x (Set.mem_univ _)) fun a => ?_
  have h := applyKernel_im_eq_zero (T := swapKernel ((vertexCoordinate σ).kernel r' m))
    (fun ι' ι => hT ι ι') (hr'.coeffs_im_eq_zero g hg) hrep.1 (a, x)
  rw [hrep.2, hcoeffs] at h
  exact h
theorem kernelsRealAtGroupFields_holds (hIter : IteratesPreserveRealFields.Holds)
    (hKer : ThreeMapKernels.Claim) : KernelsRealAtGroupFields := by
  intro L hL k hk U hU hG
  have hL0 : 0 < L := by
    have := hL.2
    omega
  have hs : ∀ j, 0 < meshAt L k j := fun j => zpow_pos (by exact_mod_cast hL0) _
  have hI := (hIter L hL k hk).2 U hU hG
  have hK := (hKer L hL k hk).2
  have HD := hK.2.1 U hU.1
  have HQ := (hK.2.2.2 U hU).1
  have HA := (hK.2.2.2 U hU).2
  have hV := preservesReal_vertexRepresentation (Vertex L k 0)
  have hVk := preservesReal_vertexRepresentation (Vertex L k k)
  have hE := preservesReal_edgeRepresentation (hs 0)
  have hEk := preservesReal_edgeRepresentation (hs k)
  have kD := kernel_im_eq_zero hV hE HD.represents fun l hl => covDiff_mem (hs 0) hG hl
  have kA := kernel_im_eq_zero hV hVk HA.represents fun l hl => hI.2.2.1 k le_rfl l hl
  have kQ := kernel_im_eq_zero hE hEk HQ.represents fun B hB => (hI.2.1 k le_rfl B hB).2.1
  exact ⟨kD, kA, kQ, fun B hB => transposeOfValues_mem_real hE HD.swap_represents kD hB,
    fun l hl => transposeOfValues_mem_real hVk HA.swap_represents kA hl⟩
end YangMills.Construction.Tower.FullSpace.RealKernels
end
