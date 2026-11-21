import YangMills.Construction.Towers.BracketOfTheFactorsDescends
import YangMills.Construction.Towers.PeriodicExtensionsAndPeriodisation
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LocalKernels.BracketDescent
open Periodisation
open YangMills.Construction.PeriodicOperators
  (BackgroundKernelFactors KernelMatrix swapKernel applyKernel compKernel unitKernel)
section Steps
variable {k : ℕ} {L n : ℕ}
def DescendsWithSwap (L n : ℕ) {k : ℕ} (I I' : WeightedIndexSet k)
    (T : KernelMatrix (Idx L I) (Idx L I'))
    (M : KernelMatrix (I.ImageCarrier L n) (I'.ImageCarrier L n)) : Prop :=
  KernelDescends L n I I' T M ∧
    KernelDescends L n I' I (swapKernel T) (swapKernel M)
theorem isRLocal_mono {I I' : WeightedIndexSet k} {R R' : ℝ} (hRR : R ≤ R')
    {T : KernelMatrix (Idx L I) (Idx L I')} (hT : IsRLocal L I I' R T) :
    IsRLocal L I I' R' T :=
  fun i' i hfar => hT i' i fun hle => hfar (hle.trans hRR)
theorem kernelDescends_zero (I I' : WeightedIndexSet k) :
    KernelDescends L n I I' (0 : KernelMatrix (Idx L I) (Idx L I')) 0 := by
  refine ⟨⟨0, le_rfl, fun _ _ _ => rfl⟩, fun f => ?_⟩
  funext i'
  simp [applyKernel, WeightedIndexSet.lift]
theorem kernelDescends_add (hc : DescendsAlgebra (k := k) L n)
    {I I' : WeightedIndexSet k} {T T' : KernelMatrix (Idx L I) (Idx L I')}
    {M M' : KernelMatrix (I.ImageCarrier L n) (I'.ImageCarrier L n)}
    (hT : KernelDescends L n I I' T M) (hT' : KernelDescends L n I I' T' M') :
    KernelDescends L n I I' (T + T') (M + M') := by
  obtain ⟨⟨R, hR, hloc⟩, -⟩ := id hT
  obtain ⟨⟨R', hR', hloc'⟩, -⟩ := id hT'
  have hmax : 0 ≤ max R R' := le_max_of_le_left hR
  exact (hc I I' I (max R R') hmax T T' 0 M M' 0
    (isRLocal_mono (le_max_left _ _) hloc) (isRLocal_mono (le_max_right _ _) hloc')
    (fun _ _ _ => rfl) hT hT' (kernelDescends_zero I I)).2.2.1
theorem kernelDescends_comp (hc : DescendsAlgebra (k := k) L n)
    {I I' I'' : WeightedIndexSet k} {T : KernelMatrix (Idx L I) (Idx L I')}
    {S : KernelMatrix (Idx L I'') (Idx L I)}
    {M : KernelMatrix (I.ImageCarrier L n) (I'.ImageCarrier L n)}
    {N : KernelMatrix (I''.ImageCarrier L n) (I.ImageCarrier L n)}
    (hT : KernelDescends L n I I' T M) (hS : KernelDescends L n I'' I S N) :
    KernelDescends L n I'' I' (compKernel T S) (compKernel M N) := by
  obtain ⟨⟨R, hR, hloc⟩, -⟩ := id hT
  obtain ⟨⟨R', hR', hloc'⟩, -⟩ := id hS
  have hmax : 0 ≤ max R R' := le_max_of_le_left hR
  have hTloc := isRLocal_mono (L := L) (le_max_left R R') hloc
  exact (hc I I' I'' (max R R') hmax T T S M M N hTloc hTloc
    (isRLocal_mono (le_max_right _ _) hloc') hT hT hS).2.2.2.2.1
theorem kernelDescends_smul (z : ℂ) {I I' : WeightedIndexSet k}
    {T : KernelMatrix (Idx L I) (Idx L I')}
    {M : KernelMatrix (I.ImageCarrier L n) (I'.ImageCarrier L n)}
    (hT : KernelDescends L n I I' T M) : KernelDescends L n I I' (z • T) (z • M) := by
  obtain ⟨⟨R, hR, hloc⟩, hact⟩ := hT
  refine ⟨⟨R, hR, fun i' i hfar => ?_⟩, fun f => ?_⟩
  · simp [hloc i' i hfar]
  · funext i'
    have hi := congrFun (hact f) i'
    simp only [applyKernel, WeightedIndexSet.lift] at hi ⊢
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, tsum_mul_left]
    rw [hi]
theorem kernelDescends_unit (I : WeightedIndexSet k) :
    KernelDescends L n I I (unitKernel (Idx L I)) (unitKernel (I.ImageCarrier L n)) := by
  classical
  refine ⟨⟨0, le_rfl, fun i' i hfar => ?_⟩, fun f => ?_⟩
  · have hne : i' ≠ i := by
      rintro rfl
      exact hfar (by simp [TorusMetric.supNormVec])
    simp [unitKernel, hne]
  · funext i'
    simp [applyKernel, unitKernel, WeightedIndexSet.lift]
theorem swapKernel_compKernel {A B C : Type} (T : KernelMatrix A B) (S : KernelMatrix C A) :
    swapKernel (compKernel T S) = compKernel (swapKernel S) (swapKernel T) := by
  funext c b
  simp only [swapKernel, compKernel, mul_comm]
theorem swapKernel_unitKernel (A : Type) : swapKernel (unitKernel A) = unitKernel A := by
  classical
  funext a b
  simp [swapKernel, unitKernel, eq_comm]
theorem DescendsWithSwap.swap {I I' : WeightedIndexSet k}
    {T : KernelMatrix (Idx L I) (Idx L I')}
    {M : KernelMatrix (I.ImageCarrier L n) (I'.ImageCarrier L n)}
    (hT : DescendsWithSwap L n I I' T M) :
    DescendsWithSwap L n I' I (swapKernel T) (swapKernel M) :=
  ⟨hT.2, hT.1⟩
theorem DescendsWithSwap.add (hc : DescendsAlgebra (k := k) L n)
    {I I' : WeightedIndexSet k} {T T' : KernelMatrix (Idx L I) (Idx L I')}
    {M M' : KernelMatrix (I.ImageCarrier L n) (I'.ImageCarrier L n)}
    (hT : DescendsWithSwap L n I I' T M) (hT' : DescendsWithSwap L n I I' T' M') :
    DescendsWithSwap L n I I' (T + T') (M + M') :=
  ⟨kernelDescends_add hc hT.1 hT'.1, kernelDescends_add hc hT.2 hT'.2⟩
theorem DescendsWithSwap.smul (z : ℂ) {I I' : WeightedIndexSet k}
    {T : KernelMatrix (Idx L I) (Idx L I')}
    {M : KernelMatrix (I.ImageCarrier L n) (I'.ImageCarrier L n)}
    (hT : DescendsWithSwap L n I I' T M) : DescendsWithSwap L n I I' (z • T) (z • M) :=
  ⟨kernelDescends_smul z hT.1, kernelDescends_smul z hT.2⟩
theorem DescendsWithSwap.sub (hc : DescendsAlgebra (k := k) L n)
    {I I' : WeightedIndexSet k} {T T' : KernelMatrix (Idx L I) (Idx L I')}
    {M M' : KernelMatrix (I.ImageCarrier L n) (I'.ImageCarrier L n)}
    (hT : DescendsWithSwap L n I I' T M) (hT' : DescendsWithSwap L n I I' T' M') :
    DescendsWithSwap L n I I' (T - T') (M - M') := by
  have hTsub : T - T' = T + (-1 : ℂ) • T' := by
    funext a b
    simp [sub_eq_add_neg]
  have hMsub : M - M' = M + (-1 : ℂ) • M' := by
    funext a b
    simp [sub_eq_add_neg]
  rw [hTsub, hMsub]
  exact hT.add hc (hT'.smul (-1))
theorem DescendsWithSwap.comp (hc : DescendsAlgebra (k := k) L n)
    {I I' I'' : WeightedIndexSet k} {T : KernelMatrix (Idx L I) (Idx L I')}
    {S : KernelMatrix (Idx L I'') (Idx L I)}
    {M : KernelMatrix (I.ImageCarrier L n) (I'.ImageCarrier L n)}
    {N : KernelMatrix (I''.ImageCarrier L n) (I.ImageCarrier L n)}
    (hT : DescendsWithSwap L n I I' T M) (hS : DescendsWithSwap L n I'' I S N) :
    DescendsWithSwap L n I'' I' (compKernel T S) (compKernel M N) := by
  refine ⟨kernelDescends_comp hc hT.1 hS.1, ?_⟩
  rw [swapKernel_compKernel, swapKernel_compKernel]
  exact kernelDescends_comp hc hS.2 hT.2
theorem DescendsWithSwap.unit (I : WeightedIndexSet k) :
    DescendsWithSwap L n I I (unitKernel (Idx L I)) (unitKernel (I.ImageCarrier L n)) := by
  refine ⟨kernelDescends_unit I, ?_⟩
  rw [swapKernel_unitKernel, swapKernel_unitKernel]
  exact kernelDescends_unit I
theorem assembled_descendsWithSwap (hc : DescendsAlgebra (k := k) L n)
    {I₀ I₁ I₂ : WeightedIndexSet k}
    {F : BackgroundKernelFactors (Idx L I₀) (Idx L I₁) (Idx L I₂)}
    {M : BackgroundKernelFactors (I₀.ImageCarrier L n) (I₁.ImageCarrier L n) (I₂.ImageCarrier L n)}
    (hF : BackgroundFactorsDescend L n F M) :
    DescendsWithSwap L n I₁ I₁ F.assembled M.assembled := by
  have hHess : DescendsWithSwap L n I₁ I₁ F.hess M.hess := ⟨hF.hess, hF.hess_swap⟩
  have hBrk : DescendsWithSwap L n I₁ I₀ F.brk M.brk :=
    ⟨hF.brk, hF.brk_swap⟩
  have hQuad : DescendsWithSwap L n I₁ I₁ F.quad M.quad :=
    ⟨hF.quad, hF.quad_swap⟩
  have hSigma : DescendsWithSwap L n I₁ I₀ F.sigma M.sigma :=
    ⟨hF.sigma, hF.sigma_swap⟩
  have hDiff : DescendsWithSwap L n I₀ I₁ F.diff M.diff :=
    ⟨hF.diff, hF.diff_swap⟩
  have hAvg : DescendsWithSwap L n I₀ I₂ F.avg M.avg :=
    ⟨hF.avg, hF.avg_swap⟩
  have hTau : DescendsWithSwap L n I₁ I₁ F.tauKernel M.tauKernel :=
    (DescendsWithSwap.unit I₁).add hc (hDiff.comp hc hSigma)
  have hCompl : DescendsWithSwap L n I₀ I₀ F.complementKernel M.complementKernel := by
    have hsub := (DescendsWithSwap.unit (L := L) (n := n) I₀).sub hc
      ((hAvg.swap.comp hc hAvg).smul F.scale)
    simpa only [BackgroundKernelFactors.complementKernel, hF.scale] using hsub
  have hSB := hSigma.swap.comp hc hBrk
  exact ((((hHess.add hc (hSB.smul 2)).add hc
    (hSB.comp hc (hDiff.comp hc hSigma))).sub hc
    ((hTau.swap.comp hc hQuad).comp hc hTau)).add hc
    ((hDiff.comp hc hCompl).comp hc (hCompl.comp hc hDiff.swap)))
end Steps
theorem assembledFactorsDescend_holds (hP : PeriodisationHolds) : AssembledFactorsDescend := by
  intro L hL k n hn I₀ I₁ I₂ F M hF
  exact assembled_descendsWithSwap (hP L hL k n hn).2.2.1 hF
end YangMills.Construction.LocalKernels.BracketDescent
end
