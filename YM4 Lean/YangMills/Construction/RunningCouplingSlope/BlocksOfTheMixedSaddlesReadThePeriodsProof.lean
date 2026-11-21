import YangMills.Construction.RunningCouplingSlope.BlocksOfTheMixedSaddlesAndThePeriodsForm
import YangMills.Construction.RunningCouplingSlope.PlainStepNearTheFreeStepProof
import YangMills.Construction.Towers.BlocksOfTheTwoOperatorFunctionsDescendProof
import YangMills.Construction.Towers.CovariantDifferenceIsLocalWithACounterpart
import YangMills.Construction.Towers.PeriodicExtensionOfAConfigurationIsAConfiguration
import YangMills.Construction.Towers.TheThreeKernelsOfATowerDescendProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.PeriodizedBlocks
open Matrices Tower PeriodicOperators
open LocalKernels LocalKernels.Periodisation
section Coefficients
private theorem pauliCombination_mem_traceless (x : Fin 3 → ℂ) :
    ∑ a, x a • ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_smul_pauli_mem <;> assumption
private theorem pauliCoeff_pauliCombination (x : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ b, x b • ComplexMatrix2.pauliFamily b) = x a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
private theorem toPauliCoeffs_ofPauliCoeffs {σ : Type} (c : Fin 3 × σ → ℂ) :
    toPauliCoeffs (ofPauliCoeffs c) = c := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.toPauliCoeffs_ofPauliCoeffs <;> assumption
end Coefficients
section BlockEvaluations
variable {L k j : ℕ}
private theorem full_ofCoeffs_mem (hL : Conventions.IsAdmissibleBlockingFactor L)
    (c : (FullSpace.edgePauliCoordinates L k j).Index → ℂ) :
    (FullSpace.edgePauliCoordinates L k j).ofCoeffs c ∈ FullSpace.complexEdgeForms (meshAt L k j) := by apply _root_.YangMills.Construction.Tower.KernelDescent.edgePauliCoordinates_ofCoeffs_mem <;> assumption
private theorem full_coeffs_ofCoeffs (c : (FullSpace.edgePauliCoordinates L k j).Index → ℂ) :
    (FullSpace.edgePauliCoordinates L k j).coeffs ((FullSpace.edgePauliCoordinates L k j).ofCoeffs c) = c := by apply _root_.YangMills.Construction.Tower.KernelDescent.edgePauliCoordinates_coeffs_ofCoeffs <;> assumption
end BlockEvaluations
section SideEvaluations
variable {L n k j : ℕ}
private theorem periodic_ofCoeffs_of_pos (c : (edgePauliCoordinates L n k j).Index → ℂ) {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) :
    (edgePauliCoordinates L n k j).ofCoeffs c b = ofPauliCoeffs c ⟨b, hb⟩ := by apply _root_.YangMills.SharedProofs.p19922 <;> assumption
private theorem periodic_ofCoeffs_mem
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (c : (edgePauliCoordinates L n k j).Index → ℂ) :
    (edgePauliCoordinates L n k j).ofCoeffs c ∈ complexEdgeForms L n k j := by apply _root_.YangMills.SharedProofs.p1053 <;> assumption
private theorem periodic_coeffs_ofCoeffs (c : (edgePauliCoordinates L n k j).Index → ℂ) :
    (edgePauliCoordinates L n k j).coeffs ((edgePauliCoordinates L n k j).ofCoeffs c) = c :=
  funext fun ι => by
    show pauliCoeff ι.1 ((edgePauliCoordinates L n k j).ofCoeffs c ι.2.1) = c ι
    rw [periodic_ofCoeffs_of_pos c ι.2.2]
    exact pauliCoeff_pauliCombination (fun a => c (a, ι.2)) ι.1
end SideEvaluations
section Kernels
variable {L n k : ℕ}
private abbrev FullPair (L : ℕ) {k : ℕ} (A : CellClass k) : Type :=
  Fin 3 × Cell L k A.level A.cellType
private abbrev QuotPair (L n : ℕ) {k : ℕ} (A : CellClass k) : Type :=
  Fin 3 × QuotientCell L n k A.level A.cellType
private def Descends (L n : ℕ) {k : ℕ} (A A' : CellClass k)
    (T : KernelMatrix (FullPair L A) (FullPair L A'))
    (M : KernelMatrix (QuotPair L n A) (QuotPair L n A')) : Prop :=
  KernelDescends L n A.colourPairs A'.colourPairs (fun ι' ι => T ι'.2 ι.2) (fun κ' κ => M κ'.2.1 κ.2.1)
private def imageCarrierEquiv (A : CellClass k)
    (hs : Function.Surjective
      (Cell.proj n : Cell L k A.level A.cellType → QuotientCell L n k A.level A.cellType)) :
    A.colourPairs.ImageCarrier L n ≃ QuotPair L n A :=
  Equiv.ofBijective (fun κ => κ.2.1) (by
    constructor
    · rintro ⟨⟨⟩, t, ht⟩ ⟨⟨⟩, t', ht'⟩ h
      have h' : t = t' := h
      subst h'
      rfl
    · rintro ⟨a, b⟩
      obtain ⟨x, hx⟩ := hs b
      exact ⟨⟨(), ⟨(a, b), ⟨(a, x), congrArg (Prod.mk a) hx⟩⟩⟩, rfl⟩)
private theorem applyKernel_smul {N N' : Type} (z : ℂ) (T : KernelMatrix N N') (f : N → ℂ) :
    applyKernel (z • T) f = z • applyKernel T f := by apply _root_.YangMills.Construction.Tower.OperatorBlocksDescend.applyKernel_smul <;> assumption
private theorem kernelDescends_smul {I I' : WeightedIndexSet k}
    {T : KernelMatrix (Idx L I) (Idx L I')}
    {M : KernelMatrix (I.ImageCarrier L n) (I'.ImageCarrier L n)} (z : ℂ)
    (h : KernelDescends L n I I' T M) : KernelDescends L n I I' (z • T) (z • M) := by apply _root_.YangMills.Construction.Tower.OperatorBlocksDescend.kernelDescends_smul <;> assumption
private theorem isRLocal_mono {I I' : WeightedIndexSet k} {T : KernelMatrix (Idx L I) (Idx L I')}
    {R R' : ℝ} (h : IsRLocal L I I' R T) (hR : R ≤ R') : IsRLocal L I I' R' T :=
  fun ι' ι hι => h ι' ι fun h' => hι (h'.trans hR)
private theorem descends_smul {A A' : CellClass k} {T : KernelMatrix (FullPair L A) (FullPair L A')}
    {M : KernelMatrix (QuotPair L n A) (QuotPair L n A')} (z : ℂ) (h : Descends L n A A' T M) :
    Descends L n A A' (z • T) (z • M) :=
  kernelDescends_smul z h
private theorem descends_zero (A A' : CellClass k) : Descends L n A A' 0 0 := by
  refine ⟨⟨0, le_rfl, fun _ _ _ => rfl⟩, fun f => ?_⟩
  funext ι
  show (∑' x : Idx L A.colourPairs, (0 : ℂ) * _) = ∑' y : A.colourPairs.ImageCarrier L n, (0 : ℂ) * _
  simp
private theorem descends_add (hSP : DescendsAlgebra (k := k) L n)
    {A A' : CellClass k} {T T' : KernelMatrix (FullPair L A) (FullPair L A')}
    {M M' : KernelMatrix (QuotPair L n A) (QuotPair L n A')} (h : Descends L n A A' T M)
    (h' : Descends L n A A' T' M') : Descends L n A A' (T + T') (M + M') := by
  have h₀ : KernelDescends L n A.colourPairs A.colourPairs
      (0 : KernelMatrix (Idx L A.colourPairs) (Idx L A.colourPairs))
      (0 : KernelMatrix (A.colourPairs.ImageCarrier L n) (A.colourPairs.ImageCarrier L n)) :=
    descends_zero (L := L) (n := n) A A
  obtain ⟨⟨R₁, h₁, l₁⟩, -⟩ := id h
  obtain ⟨⟨R₂, h₂, l₂⟩, -⟩ := id h'
  have hR : 0 ≤ max R₁ R₂ := le_max_of_le_left h₁
  have a₁ := isRLocal_mono l₁ (le_max_left R₁ R₂)
  have a₂ := isRLocal_mono l₂ (le_max_right R₁ R₂)
  have a₀ : IsRLocal L A.colourPairs A.colourPairs (max R₁ R₂)
      (0 : KernelMatrix (Idx L A.colourPairs) (Idx L A.colourPairs)) := fun _ _ _ => rfl
  exact (hSP _ _ _ _ hR _ _ _ _ _ _ a₁ a₂ a₀ h h' h₀).2.2.1
private theorem descends_sub (hSP : DescendsAlgebra (k := k) L n)
    {A A' : CellClass k} {T T' : KernelMatrix (FullPair L A) (FullPair L A')}
    {M M' : KernelMatrix (QuotPair L n A) (QuotPair L n A')} (h : Descends L n A A' T M)
    (h' : Descends L n A A' T' M') : Descends L n A A' (T - T') (M - M') := by
  have e₁ : T - T' = T + (-1 : ℂ) • T' := by
    funext a b
    simp [sub_eq_add_neg]
  have e₂ : M - M' = M + (-1 : ℂ) • M' := by
    funext a b
    simp [sub_eq_add_neg]
  rw [e₁, e₂]
  exact descends_add hSP h (descends_smul _ h')
private theorem descends_comp (hSP : DescendsAlgebra (k := k) L n)
    {A A' A'' : CellClass k}
    (hs : Function.Surjective
      (Cell.proj n : Cell L k A.level A.cellType → QuotientCell L n k A.level A.cellType))
    {T : KernelMatrix (FullPair L A) (FullPair L A')} {S : KernelMatrix (FullPair L A'') (FullPair L A)}
    {M : KernelMatrix (QuotPair L n A) (QuotPair L n A')}
    {N : KernelMatrix (QuotPair L n A'') (QuotPair L n A)}
    (h : Descends L n A A' T M) (h' : Descends L n A'' A S N) :
    Descends L n A'' A' (compKernel T S) (compKernel M N) := by
  obtain ⟨⟨R₁, h₁, l₁⟩, -⟩ := id h
  obtain ⟨⟨R₂, h₂, l₂⟩, -⟩ := id h'
  have hR : 0 ≤ max R₁ R₂ := le_max_of_le_left h₁
  have a₁ := isRLocal_mono l₁ (le_max_left R₁ R₂)
  have a₂ := isRLocal_mono l₂ (le_max_right R₁ R₂)
  have hp := (hSP _ _ _ _ hR _ _ _ _ _ _ a₁ a₁ a₂ h h h').2.2.2.2.1
  have e₁ : (fun (ι' : Idx L A'.colourPairs) (ι : Idx L A''.colourPairs) => compKernel T S ι'.2 ι.2) =
      compKernel (fun (ι' : Idx L A'.colourPairs) (ι : Idx L A.colourPairs) => T ι'.2 ι.2)
        (fun (ι' : Idx L A.colourPairs) (ι : Idx L A''.colourPairs) => S ι'.2 ι.2) := by
    funext ι' ι
    let e : Idx L A.colourPairs ≃ FullPair L A :=
      { toFun := fun ι => ι.2
        invFun := fun c => ⟨(), c⟩
        left_inv := fun ⟨⟨⟩, _⟩ => rfl
        right_inv := fun _ => rfl }
    exact (e.tsum_eq fun c => T ι'.2 c * S c ι.2).symm
  have e₂ : (fun (κ' : A'.colourPairs.ImageCarrier L n) (κ : A''.colourPairs.ImageCarrier L n) =>
        compKernel M N κ'.2.1 κ.2.1) =
      compKernel (fun (κ' : A'.colourPairs.ImageCarrier L n) (κ : A.colourPairs.ImageCarrier L n) =>
          M κ'.2.1 κ.2.1)
        (fun (κ' : A.colourPairs.ImageCarrier L n) (κ : A''.colourPairs.ImageCarrier L n) =>
          N κ'.2.1 κ.2.1) := by
    funext κ' κ
    exact ((imageCarrierEquiv A hs).tsum_eq fun c => M κ'.2.1 c * N c κ.2.1).symm
  show KernelDescends L n A''.colourPairs A'.colourPairs _ _
  rw [e₁, e₂]
  exact hp
private theorem descends_meshTranspose {A A' : CellClass k}
    {T : KernelMatrix (FullPair L A) (FullPair L A')}
    {M : KernelMatrix (QuotPair L n A) (QuotPair L n A')} (a a' : ℝ)
    (h : Descends L n A' A (swapKernel T) (swapKernel M)) :
    Descends L n A' A (meshTranspose a a' T) (meshTranspose a a' M) := by
  have e₁ : meshTranspose a a' T = (((a' ^ 4 / a ^ 4 : ℝ) : ℂ)) • swapKernel T := rfl
  have e₂ : meshTranspose a a' M = (((a' ^ 4 / a ^ 4 : ℝ) : ℂ)) • swapKernel M := rfl
  rw [e₁, e₂]
  exact descends_smul _ h
private theorem descends_entry (hSP : DescendsAlgebra (k := k) L n)
    {A A' : CellClass k} {T : KernelMatrix (FullPair L A) (FullPair L A')}
    {M : KernelMatrix (QuotPair L n A) (QuotPair L n A')} (h : Descends L n A A' T M)
    (ι' : Idx L A'.colourPairs) (ι : Idx L A.colourPairs) :
    M (A'.colourPairs.proj L n ι').2.1 (A.colourPairs.proj L n ι).2.1 =
      periodization (A.colourPairs.toPeriodicData L) (A'.colourPairs.toPeriodicData L)
        (fun ι' ι => T ι'.2 ι.2) (periodSide L n) ι' ι := by
  obtain ⟨⟨R, hR, l⟩, -⟩ := id h
  exact (hSP _ _ _ _ hR _ _ _ _ _ _ l l
    (fun _ _ _ => rfl : IsRLocal L A.colourPairs A.colourPairs R 0) h h
    (descends_zero A A)).1.1 ι' ι
private theorem represents_of_representedOnPairs (hEv : LocalKernelFacts (k := k) L)
    {A A' : CellClass k} {R : ℝ}
    (hR : 0 ≤ R) {T : KernelMatrix (Idx L A.colourPairs) (Idx L A'.colourPairs)}
    (hl : IsRLocal L A.colourPairs A'.colourPairs R T)
    {m : ((CellClass.fullSpace L A).index → ComplexMatrix2) →
      (CellClass.fullSpace L A').index → ComplexMatrix2}
    (hg : IsRepresentedOnPairs L A A' (fun f => m f) T)
    (ofC : (FullPair L A → ℂ) → (CellClass.fullSpace L A).index → ComplexMatrix2)
    (hmem : ∀ c, ofC c ∈ (CellClass.fullSpace L A).complexSubmodule)
    (hread : ∀ c, CellClass.coeffsOn L A (ofC c) = fun ι => c ι.2) :
    Represents (I := FullPair L A) (J := FullPair L A')
      (fun a b => T ⟨(), a⟩ ⟨(), b⟩)
      (fun c a => toPauliCoeffs (CellClass.cellFn L A' (m (ofC c))) a) := by
  intro c
  have hr : CellClass.coeffsOn L A' (m (ofC c)) = applyKernel T (fun ι => c ι.2) := by
    have h := (hg ⟨ofC c, hmem c⟩).2
    simpa only [hread] using h
  have hfin := (hEv A.colourPairs A'.colourPairs R hR T hl).1 (fun ι => c ι.2)
  let e : FullPair L A ≃ Idx L A.colourPairs :=
    { toFun := fun a => ⟨(), a⟩
      invFun := fun ι => ι.2
      left_inv := fun _ => rfl
      right_inv := fun ⟨⟨⟩, _⟩ => rfl }
  constructor
  · intro a
    have hf : (Function.support fun b => ‖T ⟨(), a⟩ ⟨(), b⟩ * c b‖).Finite := by
      refine ((hfin ⟨(), a⟩).preimage e.injective.injOn).subset ?_
      intro b hb
      show T ⟨(), a⟩ ⟨(), b⟩ * c b ≠ 0
      exact norm_ne_zero_iff.1 (Function.mem_support.1 hb)
    exact summable_of_hasFiniteSupport hf
  · funext a
    exact (e.tsum_eq fun ι => T ⟨(), a⟩ ι * c ι.2).trans (congrFun hr ⟨(), a⟩).symm
private theorem kernelT_colourPairs (A A' : CellClass k)
    (T : KernelMatrix (Idx L A.colourPairs) (Idx L A'.colourPairs)) :
    kernelT L A.colourPairs A'.colourPairs T = fun ι' ι => T ι ι' := by apply _root_.YangMills.Construction.Tower.KernelDescent.kernelT_colourPairs <;> assumption
private theorem quotMatrixT_colourPairs (A A' : CellClass k)
    (M : KernelMatrix (A.colourPairs.ImageCarrier L n) (A'.colourPairs.ImageCarrier L n)) :
    quotMatrixT L n A.colourPairs A'.colourPairs M = swapKernel M := by apply _root_.YangMills.Construction.Tower.KernelDescent.quotMatrixT_colourPairs <;> assumption
private theorem descends_of_periodizes (hEv : LocalKernelFacts (k := k) L)
    (hSP : DescendsAlgebra (k := k) L n) {A A' : CellClass k} {R : ℝ}
    (hR : 0 ≤ R) (hs : 2 * R < (periodSide L n : ℝ))
    (sur : Function.Surjective
      (Cell.proj n : Cell L k A.level A.cellType → QuotientCell L n k A.level A.cellType))
    (sur' : Function.Surjective
      (Cell.proj n : Cell L k A'.level A'.cellType → QuotientCell L n k A'.level A'.cellType))
    (fin : Finite (A.colourPairs.ImageCarrier L n))
    {mW : ((CellClass.fullSpace L A).index → ComplexMatrix2) →
      (CellClass.fullSpace L A').index → ComplexMatrix2}
    {mT : ((CellClass.quotSpace L n A).index → ComplexMatrix2) →
      (CellClass.quotSpace L n A').index → ComplexMatrix2}
    (hP : Periodizes L n A A' R mW mT)
    (ofW : (FullPair L A → ℂ) → (CellClass.fullSpace L A).index → ComplexMatrix2)
    (hWm : ∀ c, ofW c ∈ (CellClass.fullSpace L A).complexSubmodule)
    (hWr : ∀ c, CellClass.coeffsOn L A (ofW c) = fun ι => c ι.2)
    (ofT : (QuotPair L n A → ℂ) → (CellClass.quotSpace L n A).index → ComplexMatrix2)
    (hTm : ∀ c, ofT c ∈ (CellClass.quotSpace L n A).complexSubmodule)
    (hTr : ∀ c, CellClass.quotCoeffsOn L n A (ofT c) = fun κ => c κ.2.1)
    (hAW : KernelUnique (FullPair L A) (FullPair L A'))
    (hAT : KernelUnique (QuotPair L n A) (QuotPair L n A')) :
    let KW : KernelMatrix (FullPair L A) (FullPair L A') :=
      kernelOfMap fun c a => toPauliCoeffs (CellClass.cellFn L A' (mW (ofW c))) a
    let KT : KernelMatrix (QuotPair L n A) (QuotPair L n A') :=
      kernelOfMap fun c a => toPauliCoeffs (CellClass.quotCellFn L n A' (mT (ofT c))) a
    Represents KW (fun c a => toPauliCoeffs (CellClass.cellFn L A' (mW (ofW c))) a) ∧
    Represents KT (fun c a => toPauliCoeffs (CellClass.quotCellFn L n A' (mT (ofT c))) a) ∧
    Descends L n A A' KW KT ∧ Descends L n A' A (swapKernel KW) (swapKernel KT) := by
  intro KW KT
  obtain ⟨T, m, hl, hg, hv, ⟨M, hM, hd⟩, ⟨M₂, -, hd₂⟩⟩ := hP
  have gW := represents_of_representedOnPairs hEv hR hl hg ofW hWm hWr
  have gKW : Represents KW (fun c a => toPauliCoeffs (CellClass.cellFn L A' (mW (ofW c))) a) :=
    Classical.epsilon_spec (p := fun T' => Represents T' _) ⟨_, gW⟩
  have eW : (fun a b => T ⟨(), a⟩ ⟨(), b⟩) = KW := hAW _ _ _ gW gKW
  have hT : T = fun ι' ι => KW ι'.2 ι.2 := by
    rw [← eW]
    funext ι' ι
    obtain ⟨⟨⟩, a⟩ := ι'
    obtain ⟨⟨⟩, b⟩ := ι
    rfl
  let ψ := imageCarrierEquiv (L := L) (n := n) A sur
  let ψ' := imageCarrierEquiv (L := L) (n := n) A' sur'
  have finP : Finite (QuotPair L n A) := Finite.of_equiv _ ψ
  have gT : Represents (I := QuotPair L n A) (J := QuotPair L n A')
      (fun a b => M (ψ'.symm a) (ψ.symm b))
      (fun c a => toPauliCoeffs (CellClass.quotCellFn L n A' (mT (ofT c))) a) := by
    intro c
    refine ⟨fun a => summable_of_hasFiniteSupport (Set.toFinite _), ?_⟩
    funext a
    have h₁ := hM ⟨ofT c, hTm c⟩
    rw [hv] at h₁
    have h₂ := congrFun h₁ (ψ'.symm a)
    have h₃ : (ψ'.symm a).2.1 = a := ψ'.apply_symm_apply a
    have h₄ : CellClass.quotCoeffsOn L n A' (mT (ofT c)) (ψ'.symm a) =
        toPauliCoeffs (CellClass.quotCellFn L n A' (mT (ofT c))) a := by
      unfold CellClass.quotCoeffsOn
      rw [h₃]
    show _ = toPauliCoeffs (CellClass.quotCellFn L n A' (mT (ofT c))) a
    rw [← h₄, h₂, hTr]
    show ∑' b, M (ψ'.symm a) (ψ.symm b) * c b = ∑' κ, M (ψ'.symm a) κ * c κ.2.1
    rw [← ψ.tsum_eq fun b => M (ψ'.symm a) (ψ.symm b) * c b]
    refine tsum_congr fun κ => ?_
    rw [Equiv.symm_apply_apply]
    rfl
  have gKT : Represents KT (fun c a => toPauliCoeffs (CellClass.quotCellFn L n A' (mT (ofT c))) a) :=
    Classical.epsilon_spec (p := fun T' => Represents T' _) ⟨_, gT⟩
  have eT : (fun a b => M (ψ'.symm a) (ψ.symm b)) = KT := hAT _ _ _ gT gKT
  have hMe : M = fun κ' κ => KT κ'.2.1 κ.2.1 := by
    rw [← eT]
    funext κ' κ
    show _ = M (ψ'.symm (ψ' κ')) (ψ.symm (ψ κ))
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  have hlt := (hEv _ _ R hR T hl).2.2.1
  obtain ⟨-, -, -, -, -, hlast⟩ := hSP A.colourPairs A'.colourPairs A'.colourPairs R hR T T
    (kernelT L A.colourPairs A'.colourPairs T) M M M₂ hl hl hlt hd hd hd₂
  have hdt := (hlast hs).2.2
  rw [kernelT_colourPairs, quotMatrixT_colourPairs] at hdt
  subst hT
  subst hMe
  exact ⟨gKW, gKT, hd, hdt⟩
private theorem represents_smul {N N' : Type} {T : KernelMatrix N N'} {m : (N → ℂ) → N' → ℂ}
    (z : ℂ) (h : Represents T m) : Represents (z • T) (z • m) := by
  intro f
  refine ⟨fun ι' => ?_, ?_⟩
  · refine ((h f).1 ι').mul_left ‖z‖ |>.congr fun ι => ?_
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, norm_mul]
  · rw [applyKernel_smul, (h f).2]
    rfl
private theorem descends_diagonal (A : CellClass k) [DecidableEq (FullPair L A)]
    [DecidableEq (QuotPair L n A)] (dW : FullPair L A → ℂ) (dT : QuotPair L n A → ℂ)
    (hd : ∀ ι : Idx L A.colourPairs, dW ι.2 = dT (A.colourPairs.proj L n ι).2.1) :
    Descends L n A A (fun ι' ι => if ι' = ι then dW ι else 0)
      (fun κ' κ => if κ' = κ then dT κ else 0) := by
  refine ⟨⟨0, le_rfl, fun ι' ι hι => ?_⟩, fun f => ?_⟩
  · have hne : ι'.2 ≠ ι.2 := by
      intro h
      have h' : ι' = ι := by
        obtain ⟨⟨⟩, a⟩ := ι'
        obtain ⟨⟨⟩, b⟩ := ι
        exact congrArg (Sigma.mk ()) h
      subst h'
      exact hι (by simp [TorusMetric.supNormVec])
    exact if_neg hne
  · funext ι'
    have key₁ : ∀ b : Idx L A.colourPairs, b ≠ ι' → ι'.2 ≠ b.2 := by
      intro b hb h
      apply hb
      obtain ⟨⟨⟩, x⟩ := ι'
      obtain ⟨⟨⟩, y⟩ := b
      exact (congrArg (Sigma.mk ()) h).symm
    have key₂ : ∀ b : A.colourPairs.ImageCarrier L n, b ≠ A.colourPairs.proj L n ι' →
        (A.colourPairs.proj L n ι').2.1 ≠ b.2.1 := by
      intro b hb h
      apply hb
      obtain ⟨⟨⟩, x⟩ := b
      exact (congrArg (Sigma.mk ()) (Subtype.ext h)).symm
    show ∑' ι, _ = ∑' κ, _
    rw [tsum_eq_single ι' fun b hb => mul_eq_zero_of_left (if_neg (key₁ b hb)) _,
      tsum_eq_single (A.colourPairs.proj L n ι') fun b hb =>
        mul_eq_zero_of_left (if_neg (key₂ b hb)) _]
    exact congrArg₂ (· * ·) ((if_pos rfl).trans ((hd ι').trans (if_pos rfl).symm)) rfl
private theorem cellFn_smul {A : CellClass k} (z : ℂ)
    (f : (CellClass.fullSpace L A).index → ComplexMatrix2) (c : Cell L k A.level A.cellType) :
    CellClass.cellFn L A (z • f) c = z • CellClass.cellFn L A f c := by
  obtain ⟨j, h, _ | _ | _⟩ := A <;> rfl
private theorem quotCellFn_smul {A : CellClass k} (z : ℂ)
    (f : (CellClass.quotSpace L n A).index → ComplexMatrix2)
    (c : QuotientCell L n k A.level A.cellType) :
    CellClass.quotCellFn L n A (z • f) c = z • CellClass.quotCellFn L n A f c := by
  obtain ⟨j, h, _ | _ | _⟩ := A <;> rfl
private theorem isLocalWithPeriodicCounterpart_smul {A A' : CellClass k} {R : ℝ} {m t} (w : ℂ)
    (h : IsLocalWithPeriodicCounterpart L n A A' R m t) :
    IsLocalWithPeriodicCounterpart L n A A' R (fun f => w • m f) (fun f => w • t f) := by
  refine ⟨⟨fun f hf => Submodule.smul_mem _ w (h.full.map_mem f hf),
      fun f hf g hg => ?_, fun z f hf => ?_, fun f hf g hg c' hc => ?_⟩,
    ⟨fun f hf => Submodule.smul_mem _ w (h.periodic.map_mem f hf),
      fun f hf g hg => ?_, fun z f hf => ?_⟩, fun f hf c' => ?_⟩
  · simp only [h.full.map_add f hf g hg, smul_add]
  · simp only [h.full.map_smul z f hf]
    exact smul_comm w z _
  · rw [cellFn_smul, cellFn_smul, h.full.local_dependence f hf g hg c' hc]
  · simp only [h.periodic.map_add f hf g hg, smul_add]
  · simp only [h.periodic.map_smul z f hf]
    exact smul_comm w z _
  · rw [cellFn_smul, quotCellFn_smul, h.commutes f hf c']
private theorem real_smul_eq_complex {ι : Type} (r : ℝ) (x : ι → ComplexMatrix2) :
    r • x = (r : ℂ) • x := by apply _root_.YangMills.SharedProofs.p7664 <;> assumption
private theorem isLocalWithPeriodicCounterpart_realSmul {A A' : CellClass k} {R : ℝ} {m t} (r : ℝ)
    (h : IsLocalWithPeriodicCounterpart L n A A' R m t) :
    IsLocalWithPeriodicCounterpart L n A A' R (fun f => r • m f) (fun f => r • t f) := by
  have e₁ : (fun f => r • m f) = fun f => (r : ℂ) • m f := funext fun f => real_smul_eq_complex r _
  have e₂ : (fun f => r • t f) = fun f => (r : ℂ) • t f := funext fun f => real_smul_eq_complex r _
  rw [e₁, e₂]
  exact isLocalWithPeriodicCounterpart_smul _ h
private theorem isLocalWithPeriodicCounterpart_mono {A A' : CellClass k} {R R' : ℝ} {m t}
    (h : IsLocalWithPeriodicCounterpart L n A A' R m t) (hR : R ≤ R') :
    IsLocalWithPeriodicCounterpart L n A A' R' m t :=
  ⟨⟨h.full.map_mem, h.full.map_add, h.full.map_smul, fun f hf g hg c' hc =>
      h.full.local_dependence f hf g hg c' fun c hd => hc c (hd.trans hR)⟩, h.periodic, h.commutes⟩
private theorem periodizes_mono {A A' : CellClass k} {R R' : ℝ} {mW mT}
    (h : Periodizes L n A A' R mW mT) (hR : R ≤ R') : Periodizes L n A A' R' mW mT := by
  obtain ⟨T, m, hl, r⟩ := h
  exact ⟨T, m, isRLocal_mono hl hR, r⟩
private theorem rescaled_X_eq {S₀ B₀ S B : Type} (p : RescaledOperators S₀ B₀ S B) :
    p.X = p.K - compKernel (compKernel p.D p.Rt) (compKernel p.R p.Dt) :=
  add_sub_cancel_right _ _
end Kernels
section BlockEvaluations
variable {L n k : ℕ}
private structure DescentHypotheses (L n k : ℕ) : Prop where
  blocking : Conventions.IsAdmissibleBlockingFactor L
  localKernels : LocalKernelFacts (k := k) L
  algebra : DescendsAlgebra (k := k) L n
  surj : ∀ (j : ℕ) (_ : j ≤ k) (c : CellType),
    Function.Surjective (Cell.proj n : Cell L k j c → QuotientCell L n k j c)
  fin : ∀ A : CellClass k, Finite (A.colourPairs.ImageCarrier L n)
  orientation : ∀ (j : ℕ), j ≤ k → ∀ b : Edge L n k j,
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented
  side_large : 2 * (6 : ℝ) < (periodSide L n : ℝ)
  proj_eq : ∀ j ≤ k, ∀ b : PeriodicOperators.PosEdge L k j,
    (projPositiveEdge L n k j b).1 = FullSpace.projEdge L n k j b.1
  uniqueFull : ∀ i j : ℕ, i ≤ k → j ≤ k →
    KernelUnique (vertexCoordinate (FullSpace.Vertex L k i)).Index
      (vertexCoordinate (FullSpace.Vertex L k j)).Index ∧
    KernelUnique (vertexCoordinate (FullSpace.Vertex L k i)).Index (FullSpace.edgePauliCoordinates L k j).Index ∧
    KernelUnique (FullSpace.edgePauliCoordinates L k i).Index (vertexCoordinate (FullSpace.Vertex L k j)).Index ∧
    KernelUnique (FullSpace.edgePauliCoordinates L k i).Index (FullSpace.edgePauliCoordinates L k j).Index
  uniquePeriodic : ∀ i j : ℕ, i ≤ k → j ≤ k →
    KernelUnique (vertexCoordinate (Vertex L n k i)).Index (vertexCoordinate (Vertex L n k j)).Index ∧
    KernelUnique (vertexCoordinate (Vertex L n k i)).Index (edgePauliCoordinates L n k j).Index ∧
    KernelUnique (edgePauliCoordinates L n k i).Index (vertexCoordinate (Vertex L n k j)).Index ∧
    KernelUnique (edgePauliCoordinates L n k i).Index (edgePauliCoordinates L n k j).Index
private theorem edgeEdgeDescent (S : DescentHypotheses L n k) (i j : ℕ) (hi : i ≤ k) (hj : j ≤ k)
    {mW : ((CellClass.fullSpace L (CellClass.edgeClass k i hi)).index → ComplexMatrix2) →
      (CellClass.fullSpace L (CellClass.edgeClass k j hj)).index → ComplexMatrix2}
    {mT : ((CellClass.quotSpace L n (CellClass.edgeClass k i hi)).index → ComplexMatrix2) →
      (CellClass.quotSpace L n (CellClass.edgeClass k j hj)).index → ComplexMatrix2}
    (h : Periodizes L n (CellClass.edgeClass k i hi) (CellClass.edgeClass k j hj) 6 mW mT) :
    Represents (I := FullPair L (CellClass.edgeClass k i hi))
      (J := FullPair L (CellClass.edgeClass k j hj))
      (kernelOfMap fun c a => toPauliCoeffs (CellClass.cellFn L (CellClass.edgeClass k j hj)
        (mW ((FullSpace.edgePauliCoordinates L k i).ofCoeffs c))) a)
      (fun c a => toPauliCoeffs (CellClass.cellFn L (CellClass.edgeClass k j hj)
        (mW ((FullSpace.edgePauliCoordinates L k i).ofCoeffs c))) a) ∧
    Represents (I := QuotPair L n (CellClass.edgeClass k i hi))
      (J := QuotPair L n (CellClass.edgeClass k j hj))
      (kernelOfMap fun c a => toPauliCoeffs (CellClass.quotCellFn L n
        (CellClass.edgeClass k j hj) (mT ((edgePauliCoordinates L n k i).ofCoeffs c))) a)
      (fun c a => toPauliCoeffs (CellClass.quotCellFn L n (CellClass.edgeClass k j hj)
        (mT ((edgePauliCoordinates L n k i).ofCoeffs c))) a) ∧
    Descends L n (CellClass.edgeClass k i hi) (CellClass.edgeClass k j hj)
      (kernelOfMap fun c a => toPauliCoeffs (CellClass.cellFn L (CellClass.edgeClass k j hj)
        (mW ((FullSpace.edgePauliCoordinates L k i).ofCoeffs c))) a)
      (kernelOfMap fun c a => toPauliCoeffs (CellClass.quotCellFn L n
        (CellClass.edgeClass k j hj) (mT ((edgePauliCoordinates L n k i).ofCoeffs c))) a) ∧
    Descends L n (CellClass.edgeClass k j hj) (CellClass.edgeClass k i hi)
      (swapKernel (kernelOfMap fun c a => toPauliCoeffs (CellClass.cellFn L
        (CellClass.edgeClass k j hj) (mW ((FullSpace.edgePauliCoordinates L k i).ofCoeffs c))) a))
      (swapKernel (kernelOfMap fun c a => toPauliCoeffs (CellClass.quotCellFn L n
        (CellClass.edgeClass k j hj) (mT ((edgePauliCoordinates L n k i).ofCoeffs c))) a)) :=
  by
  have h1 := S.localKernels
  have h2 := S.algebra
  have h3 : ∀ c, (FullSpace.edgePauliCoordinates L k i).ofCoeffs c ∈
      (CellClass.fullSpace L (CellClass.edgeClass k i hi)).complexSubmodule :=
    fun c => full_ofCoeffs_mem S.blocking c
  have h4 : ∀ c, CellClass.coeffsOn L (CellClass.edgeClass k i hi)
      ((FullSpace.edgePauliCoordinates L k i).ofCoeffs c) = fun ι => c ι.2 :=
    fun c => funext fun ι => congrFun (full_coeffs_ofCoeffs c) ι.2
  have h5 : ∀ c, (edgePauliCoordinates L n k i).ofCoeffs c ∈
      (CellClass.quotSpace L n (CellClass.edgeClass k i hi)).complexSubmodule :=
    fun c => periodic_ofCoeffs_mem (S.orientation i hi) c
  have h6 : ∀ c, CellClass.quotCoeffsOn L n (CellClass.edgeClass k i hi)
      ((edgePauliCoordinates L n k i).ofCoeffs c) = fun κ => c κ.2.1 :=
    fun c => funext fun κ => congrFun (periodic_coeffs_ofCoeffs c) κ.2.1
  have h7 := (S.uniqueFull i j hi hj).2.2.2
  have h8 := (S.uniquePeriodic i j hi hj).2.2.2
  have h9 := descends_of_periodizes h1 h2 (R := 6) (by norm_num) S.side_large (S.surj i hi .edge)
    (S.surj j hj .edge) (S.fin _) h (FullSpace.edgePauliCoordinates L k i).ofCoeffs h3 h4
    (edgePauliCoordinates L n k i).ofCoeffs h5 h6 h7 h8
  exact h9
private theorem vertexVertexDescent (S : DescentHypotheses L n k) (i j : ℕ) (hi : i ≤ k)
    (hj : j ≤ k)
    {mW : ((CellClass.fullSpace L (CellClass.vertexClass k i hi)).index → ComplexMatrix2) →
      (CellClass.fullSpace L (CellClass.vertexClass k j hj)).index → ComplexMatrix2}
    {mT : ((CellClass.quotSpace L n (CellClass.vertexClass k i hi)).index → ComplexMatrix2) →
      (CellClass.quotSpace L n (CellClass.vertexClass k j hj)).index → ComplexMatrix2}
    (h : Periodizes L n (CellClass.vertexClass k i hi) (CellClass.vertexClass k j hj) 6 mW mT) :
    Descends L n (CellClass.vertexClass k i hi) (CellClass.vertexClass k j hj)
      (kernelOfMap fun c a => toPauliCoeffs (CellClass.cellFn L (CellClass.vertexClass k j hj)
        (mW (ofPauliCoeffs c))) a)
      (kernelOfMap fun c a => toPauliCoeffs (CellClass.quotCellFn L n
        (CellClass.vertexClass k j hj) (mT (ofPauliCoeffs c))) a) ∧
    Descends L n (CellClass.vertexClass k j hj) (CellClass.vertexClass k i hi)
      (swapKernel (kernelOfMap fun c a => toPauliCoeffs (CellClass.cellFn L
        (CellClass.vertexClass k j hj) (mW (ofPauliCoeffs c))) a))
      (swapKernel (kernelOfMap fun c a => toPauliCoeffs (CellClass.quotCellFn L n
        (CellClass.vertexClass k j hj) (mT (ofPauliCoeffs c))) a)) := by
  have h3 : ∀ c : Fin 3 × FullSpace.Vertex L k i → ℂ, ofPauliCoeffs c ∈
      (CellClass.fullSpace L (CellClass.vertexClass k i hi)).complexSubmodule :=
    fun c => Submodule.mem_pi.2 fun x _ => pauliCombination_mem_traceless _
  have h4 : ∀ c : Fin 3 × FullSpace.Vertex L k i → ℂ,
      CellClass.coeffsOn L (CellClass.vertexClass k i hi) (ofPauliCoeffs c) = fun ι => c ι.2 :=
    fun c => funext fun ι => congrFun (toPauliCoeffs_ofPauliCoeffs c) ι.2
  have h5 : ∀ c : Fin 3 × Vertex L n k i → ℂ, ofPauliCoeffs c ∈
      (CellClass.quotSpace L n (CellClass.vertexClass k i hi)).complexSubmodule :=
    fun c => Submodule.mem_pi.2 fun x _ => pauliCombination_mem_traceless _
  have h6 : ∀ c : Fin 3 × Vertex L n k i → ℂ,
      CellClass.quotCoeffsOn L n (CellClass.vertexClass k i hi) (ofPauliCoeffs c) =
        fun κ => c κ.2.1 :=
    fun c => funext fun κ => congrFun (toPauliCoeffs_ofPauliCoeffs c) κ.2.1
  have h9 := descends_of_periodizes S.localKernels S.algebra (R := 6) (by norm_num) S.side_large
    (S.surj i hi .vertex) (S.surj j hj .vertex) (S.fin _) h ofPauliCoeffs h3 h4 ofPauliCoeffs h5 h6
    (S.uniqueFull i j hi hj).1 (S.uniquePeriodic i j hi hj).1
  exact h9.2.2
private theorem vertexEdgeDescent (S : DescentHypotheses L n k) (hi : 0 ≤ k)
    {mW : ((CellClass.fullSpace L (CellClass.vertexClass k 0 hi)).index → ComplexMatrix2) →
      (CellClass.fullSpace L (CellClass.edgeClass k 0 hi)).index → ComplexMatrix2}
    {mT : ((CellClass.quotSpace L n (CellClass.vertexClass k 0 hi)).index → ComplexMatrix2) →
      (CellClass.quotSpace L n (CellClass.edgeClass k 0 hi)).index → ComplexMatrix2}
    (h : Periodizes L n (CellClass.vertexClass k 0 hi) (CellClass.edgeClass k 0 hi) 6 mW mT) :
    Descends L n (CellClass.vertexClass k 0 hi) (CellClass.edgeClass k 0 hi)
      (kernelOfMap fun c a => toPauliCoeffs (CellClass.cellFn L (CellClass.edgeClass k 0 hi)
        (mW (ofPauliCoeffs c))) a)
      (kernelOfMap fun c a => toPauliCoeffs (CellClass.quotCellFn L n
        (CellClass.edgeClass k 0 hi) (mT (ofPauliCoeffs c))) a) ∧
    Descends L n (CellClass.edgeClass k 0 hi) (CellClass.vertexClass k 0 hi)
      (swapKernel (kernelOfMap fun c a => toPauliCoeffs (CellClass.cellFn L
        (CellClass.edgeClass k 0 hi) (mW (ofPauliCoeffs c))) a))
      (swapKernel (kernelOfMap fun c a => toPauliCoeffs (CellClass.quotCellFn L n
        (CellClass.edgeClass k 0 hi) (mT (ofPauliCoeffs c))) a)) := by
  have h3 : ∀ c : Fin 3 × FullSpace.Vertex L k 0 → ℂ, ofPauliCoeffs c ∈
      (CellClass.fullSpace L (CellClass.vertexClass k 0 hi)).complexSubmodule :=
    fun c => Submodule.mem_pi.2 fun x _ => pauliCombination_mem_traceless _
  have h4 : ∀ c : Fin 3 × FullSpace.Vertex L k 0 → ℂ,
      CellClass.coeffsOn L (CellClass.vertexClass k 0 hi) (ofPauliCoeffs c) = fun ι => c ι.2 :=
    fun c => funext fun ι => congrFun (toPauliCoeffs_ofPauliCoeffs c) ι.2
  have h5 : ∀ c : Fin 3 × Vertex L n k 0 → ℂ, ofPauliCoeffs c ∈
      (CellClass.quotSpace L n (CellClass.vertexClass k 0 hi)).complexSubmodule :=
    fun c => Submodule.mem_pi.2 fun x _ => pauliCombination_mem_traceless _
  have h6 : ∀ c : Fin 3 × Vertex L n k 0 → ℂ,
      CellClass.quotCoeffsOn L n (CellClass.vertexClass k 0 hi) (ofPauliCoeffs c) =
        fun κ => c κ.2.1 :=
    fun c => funext fun κ => congrFun (toPauliCoeffs_ofPauliCoeffs c) κ.2.1
  have h9 := descends_of_periodizes S.localKernels S.algebra (R := 6) (by norm_num) S.side_large
    (S.surj 0 hi .vertex) (S.surj 0 hi .edge) (S.fin _) h ofPauliCoeffs h3 h4 ofPauliCoeffs h5 h6
    (S.uniqueFull 0 0 hi hi).2.1 (S.uniquePeriodic 0 0 hi hi).2.1
  exact h9.2.2
private theorem rescaled_blocks_descend (S : DescentHypotheses L n k) (U : Edge L n k 0 → ComplexMatrix2)
    (hH : Descends L n (edgesAtZero k) (edgesAtZero k)
      (FullSpace.rescaledOperators L k (liftGaugeField L n k 0 U)).H
      (rescaledOperators L n k U).H)
    (hD : Descends L n (verticesAtZero k) (edgesAtZero k)
      (FullSpace.rescaledOperators L k (liftGaugeField L n k 0 U)).D
      (rescaledOperators L n k U).D)
    (hDx : Descends L n (edgesAtZero k) (verticesAtZero k)
      (swapKernel (FullSpace.rescaledOperators L k (liftGaugeField L n k 0 U)).D)
      (swapKernel (rescaledOperators L n k U).D))
    (hR : Descends L n (verticesAtZero k) (CellClass.vertexClass k k le_rfl)
      (FullSpace.rescaledOperators L k (liftGaugeField L n k 0 U)).R
      (rescaledOperators L n k U).R)
    (hRx : Descends L n (CellClass.vertexClass k k le_rfl) (verticesAtZero k)
      (swapKernel (FullSpace.rescaledOperators L k (liftGaugeField L n k 0 U)).R)
      (swapKernel (rescaledOperators L n k U).R)) :
    Descends L n (edgesAtZero k) (edgesAtZero k)
        (FullSpace.rescaledOperators L k (liftGaugeField L n k 0 U)).X
        (rescaledOperators L n k U).X ∧
      Descends L n (verticesAtZero k) (verticesAtZero k)
        (FullSpace.rescaledOperators L k (liftGaugeField L n k 0 U)).Delta
        (rescaledOperators L n k U).Delta ∧
      Descends L n (CellClass.vertexClass k k le_rfl) (verticesAtZero k)
        (FullSpace.rescaledOperators L k (liftGaugeField L n k 0 U)).Rt
        (rescaledOperators L n k U).Rt := by
  have sS := S.surj 0 (Nat.zero_le k) .vertex
  have sB := S.surj 0 (Nat.zero_le k) .edge
  have sK := S.surj k le_rfl .vertex
  have hDt : Descends L n (edgesAtZero k) (verticesAtZero k)
      (FullSpace.rescaledOperators L k (liftGaugeField L n k 0 U)).Dt
      (rescaledOperators L n k U).Dt := descends_meshTranspose _ _ hDx
  have hRt : Descends L n (CellClass.vertexClass k k le_rfl) (verticesAtZero k)
      (FullSpace.rescaledOperators L k (liftGaugeField L n k 0 U)).Rt
      (rescaledOperators L n k U).Rt := descends_meshTranspose _ _ hRx
  have hK : Descends L n (edgesAtZero k) (edgesAtZero k)
      (FullSpace.rescaledOperators L k (liftGaugeField L n k 0 U)).K
      (rescaledOperators L n k U).K := descends_add S.algebra hH (descends_comp S.algebra sS hD hDt)
  refine ⟨?_, descends_comp S.algebra sB hDt hD, hRt⟩
  rw [rescaled_X_eq, rescaled_X_eq]
  exact descends_sub S.algebra hK (descends_comp S.algebra sK (descends_comp S.algebra sS hD hRt)
    (descends_comp S.algebra sS hR hDt))
private theorem noiseCovariance_descends (S : DescentHypotheses L n k) (a : ℝ)
    (U : Edge L n k 0 → ComplexMatrix2) (hd : MeanChainLifts L n k U) :
    ∀ (j : ℕ) (h : j ≤ k), Descends L n (CellClass.edgeClass k j h) (CellClass.edgeClass k j h)
      (FullLattice.noiseCovariance a L k (liftGaugeField L n k 0 U) j)
      (noiseCovariance a L n k U j) := by
  classical
  intro j
  induction j with
  | zero => exact fun h => descends_zero _ _
  | succ j ih =>
    intro h
    have hj : j ≤ k := Nat.le_of_succ_le h
    have hS := edgeEdgeDescent S j (j + 1) hj h (hd.step_periodizes j h)
    have dS : Descends L n (CellClass.edgeClass k j hj) (CellClass.edgeClass k (j + 1) h)
        (FullLattice.meanStepKernel L k (liftGaugeField L n k 0 U) j)
        (meanStepKernel L n k U j) := hS.2.2.1
    have dSx : Descends L n (CellClass.edgeClass k (j + 1) h) (CellClass.edgeClass k j hj)
        (swapKernel (FullLattice.meanStepKernel L k (liftGaugeField L n k 0 U) j))
        (swapKernel (meanStepKernel L n k U j)) := hS.2.2.2
    have dI : Descends L n (CellClass.edgeClass k (j + 1) h) (CellClass.edgeClass k (j + 1) h)
        (FullLattice.invRadiusDiag (liftGaugeField L n k 0 U) j)
        (invRadiusDiag U j) := by
      have e₁ : FullLattice.invRadiusDiag (liftGaugeField L n k 0 U) j =
          fun ι' ι => @ite ℂ (ι' = ι) (Classical.propDecidable _) (FullLattice.meanRadius
            (FullLattice.meanIterate (liftGaugeField L n k 0 U) j) ι.2.1)⁻¹ 0 := by
        funext ι' ι
        unfold FullLattice.invRadiusDiag
        by_cases hh : ι' = ι
        · rw [if_pos hh, if_pos hh]
        · rw [if_neg hh, if_neg hh]
      have e₂ : invRadiusDiag U j = fun ι' ι => @ite ℂ (ι' = ι) (Classical.propDecidable _)
            (meanRadius (meanIterate U j) ι.2.1)⁻¹ 0 := by
        funext ι' ι
        unfold invRadiusDiag
        by_cases hh : ι' = ι
        · rw [if_pos hh, if_pos hh]
        · rw [if_neg hh, if_neg hh]
      rw [e₁, e₂]
      refine @descends_diagonal L n k (CellClass.edgeClass k (j + 1) h)
        (fun a b => Classical.propDecidable _) (fun a b => Classical.propDecidable _)
        (fun ι => (FullLattice.meanRadius
          (FullLattice.meanIterate (liftGaugeField L n k 0 U) j) ι.2.1)⁻¹)
        (fun κ => (meanRadius (meanIterate U j) κ.2.1)⁻¹) fun ι => ?_
      have e := hd.radius_lift j h ι.2.2.1 ι.2.2.2
      have e' := S.proj_eq (j + 1) h ι.2.2
      show (FullLattice.meanRadius _ ι.2.2.1)⁻¹ =
        (meanRadius (meanIterate U j) (projPositiveEdge L n k (j + 1) ι.2.2).1)⁻¹
      rw [e, e']
    have sJ := S.surj j hj .edge
    exact descends_add S.algebra (descends_smul _ dI) (descends_smul _
      (descends_comp S.algebra sJ (descends_comp S.algebra sJ dS (ih hj))
        (descends_meshTranspose _ _ dSx)))
end BlockEvaluations
theorem mixedSaddleBlocks_periodize (hP : LocalKernels.Periodisation.PeriodisationHolds)
    (hK : Tower.ThreeMapKernels.Claim)
    (hC : MeanChainLiftsNearIdentity)
    (hRw : Tower.FullSpace.ComplexFieldRescaledRelations.Statement)
    (hRs : Tower.ComplexFieldRescaledRelations.Statement)
    (hE : LocalKernels.LiftIsGaugeField)
    (hD : LocalKernels.CovDiffLocality.CovDiffIsLocal)
    (h₀ : LocalKernels.Periodisation.LocalLinearMapsPeriodize)
    (hO : PeriodicLattice.LevelBondOrientationDichotomy) :
    MixedSaddleBlocksPeriodizeNearIdentity := by
  intro L hL
  obtain ⟨ρ, hρ, hch⟩ := hC L hL
  refine ⟨ρ, hρ, fun a k n hk hn U hs => ?_⟩
  have hd := hch k n hk hn U hs
  obtain ⟨hcells, hcl, hSP, hEv, -, -, -, hAct, hAvg⟩ := hP L hL k n hn
  have hUc := hs.mem_smallIterate.1
  have s12 : 2 * (6 : ℝ) < (periodSide L n : ℝ) := by
    have h₁ : L ≤ L ^ n := Nat.le_self_pow hn.ne' L
    have h₂ : 13 ≤ L := hL.2
    have h₃ : 12 < periodSide L n := by
      unfold periodSide
      omega
    have h₄ : (12 : ℝ) < (periodSide L n : ℝ) := by exact_mod_cast h₃
    linarith
  have S : DescentHypotheses L n k :=
    { blocking := hL
      localKernels := hEv
      algebra := hSP
      surj := fun j hj c => ((hcells j hj).1 c).1
      fin := fun A => (hcl A.colourPairs).1
      orientation := fun j hj b => by
        rcases hO L n k hL hn (by omega) j hj b with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · exact Or.inl ⟨h₁, h₂⟩
        · exact Or.inr ⟨h₁, h₂⟩
      side_large := s12
      proj_eq := fun j hj b => (hcells j hj).2.2.1 b
      uniqueFull := (hK L hL k hk).2.1
      uniquePeriodic := ((hK L hL k hk).1 n hn).1 }
  have hUw := (hE L n k 0 hL hn (Nat.zero_le k) U).2 hUc
  have hone : meshAt L k 0 ≤ 6 := by
    have h1 : (1 : ℝ) ≤ L := by
      have : (13 : ℝ) ≤ L := by exact_mod_cast hL.2
      linarith
    have := zpow_le_one_of_nonpos₀ (a := (L : ℝ)) (n := ((0 : ℕ) : ℤ) - (k : ℤ)) h1 (by omega)
    unfold meshAt
    linarith
  have pD : Periodizes L n (CellClass.vertexClass k 0 (Nat.zero_le k))
      (CellClass.edgeClass k 0 (Nat.zero_le k)) 6
      (fun l => (finestMesh L k)⁻¹ •
        FullSpace.covDiff (liftGaugeField L n k 0 U) l)
      (fun l => (finestMesh L k)⁻¹ • covDiff U l) :=
    h₀ L hL k n hn _ _ (by simp [CellClass.vertexClass]) (by simp [CellClass.edgeClass]) 6
      (by norm_num) s12 _ _
      (isLocalWithPeriodicCounterpart_mono
        (isLocalWithPeriodicCounterpart_realSmul _ (hD L hL k n hn 0 (Nat.zero_le k) U hUc)) hone)
  have dD := vertexEdgeDescent S (Nat.zero_le k) pD
  have hAv := hAvg hk U hUc
  obtain ⟨-, -, hIt, -, -⟩ := hAv.2 hs.mem_smallIterate 0 (Submodule.zero_mem _)
  obtain ⟨-, -, hA, -⟩ := hIt k le_rfl hk
  have dR := vertexVertexDescent S 0 k (Nat.zero_le k) le_rfl hA
  obtain ⟨-, -, hHd, -⟩ := hAct 0 (Nat.zero_le k) U hUc 0 (Submodule.zero_mem _)
  obtain ⟨gW, gT, dH, -⟩ := edgeEdgeDescent S 0 0 (Nat.zero_le k) (Nat.zero_le k)
    (periodizes_mono hHd (by norm_num))
  have eW := (S.uniqueFull 0 0 (Nat.zero_le k) (Nat.zero_le k)).2.2.2 _ _ _
    (hRw L hL k hk _ hUw).2.1 (represents_smul (((finestMesh L k : ℝ) : ℂ) ^ 2)⁻¹ gW)
  have eT := (S.uniquePeriodic 0 0 (Nat.zero_le k) (Nat.zero_le k)).2.2.2 _ _ _
    (hRs L hL k hk n hn U hUc).2.1 (represents_smul (((finestMesh L k : ℝ) : ℂ) ^ 2)⁻¹ gT)
  have dH' : Descends L n (edgesAtZero k) (edgesAtZero k)
      (FullSpace.rescaledOperators L k (liftGaugeField L n k 0 U)).H
      (rescaledOperators L n k U).H := by
    rw [eW, eT]
    exact descends_smul _ dH
  obtain ⟨dX, dDelta, dRt⟩ := rescaled_blocks_descend S U dH' dD.1 dD.2 dR.1 dR.2
  have dQ := edgeEdgeDescent S 0 k (Nat.zero_le k) le_rfl hd.covariant_periodizes
  have dQ₁ : Descends L n (edgesAtZero k) (CellClass.edgeClass k k le_rfl)
      (FullLattice.meanKernelQ L k (liftGaugeField L n k 0 U))
      (meanKernelQ L n k U) := dQ.2.2.1
  have dQ₂ : Descends L n (CellClass.edgeClass k k le_rfl) (edgesAtZero k)
      (swapKernel (FullLattice.meanKernelQ L k (liftGaugeField L n k 0 U)))
      (swapKernel (meanKernelQ L n k U)) := dQ.2.2.2
  have dQt := descends_meshTranspose (finestMesh L k) (meshAt L k k) dQ₂
  have dRu : Descends L n (verticesAtZero k) (CellClass.vertexClass k k le_rfl)
      (FullLattice.meanKernelR L k (liftGaugeField L n k 0 U))
      (meanKernelR L n k U) :=
    (vertexVertexDescent S 0 k (Nat.zero_le k) le_rfl hd.cubeAverage_periodizes).1
  have dN := noiseCovariance_descends S a U hd k le_rfl
  exact ⟨fun ι' ι => (descends_entry hSP dX ⟨(), ι'⟩ ⟨(), ι⟩).symm,
    fun ι' ι => (descends_entry hSP dQt ⟨(), ι'⟩ ⟨(), ι⟩).symm,
    fun ι' ι => (descends_entry hSP dQ₁ ⟨(), ι'⟩ ⟨(), ι⟩).symm,
    fun ι' ι => (descends_entry hSP dN ⟨(), ι'⟩ ⟨(), ι⟩).symm,
    fun ι' ι => (descends_entry hSP dDelta ⟨(), ι'⟩ ⟨(), ι⟩).symm,
    fun ι' ι => (descends_entry hSP dRt ⟨(), ι'⟩ ⟨(), ι⟩).symm,
    fun ι' ι => (descends_entry hSP dRu ⟨(), ι'⟩ ⟨(), ι⟩).symm⟩
end YangMills.Construction.RunningCouplingSlope.PeriodizedBlocks
end
