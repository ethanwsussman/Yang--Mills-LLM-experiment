import YangMills.Construction.Towers.CommutatorTermAtAPeriodicExtensionDescendsProof
import YangMills.Construction.Towers.KernelsOfPeriodicLocalBilinearMapsProof
import YangMills.Construction.Lattice.LatticesOfATorusAndTheProductTopologyOfConfigurations
import YangMills.Construction.Lattice.LevelBondOrientationDichotomy
import YangMills.Construction.Towers.CommutatorTermAtAPeriodicExtensionDescends
import YangMills.Construction.Towers.CovariantAveragesAtAPeriodicExtensionDescend
import YangMills.Construction.Towers.CovariantDifferenceAtAPeriodicExtensionDescends
import YangMills.Construction.Towers.ExtensionByZeroOfSiteFunctionsDescends
import YangMills.Construction.Towers.FactorsOfTheBackgroundKernelDescend
import YangMills.Construction.Towers.KernelsOfThreeMapsOfATowerProof
import YangMills.Construction.Towers.SecondDifferentialOfTheActionDescends
import YangMills.Construction.Towers.SecondOrderKernelAtAPeriodicExtensionDescends
import YangMills.Construction.Towers.SumsProductsAndTransposesOfDescendingKernels
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.BackgroundFactorsDescent
open LocalKernels LocalKernels.Periodisation
open PeriodicOperators (KernelMatrix BackgroundKernelFactors swapKernel applyKernel compKernel)
open Matrices
open Classical in
theorem applyKernel_indicator {N N' : Type} (K : KernelMatrix N N') (ι : N) (ι' : N') :
    applyKernel K (fun κ => if κ = ι then 1 else 0) ι' = K ι' ι := by apply _root_.YangMills.Construction.LocalKernels.LocalBilinearKernels.applyKernel_pointIndicator <;> assumption
theorem swapKernel_compKernel {J J' J'' : Type} (T : J' → J → ℂ) (S : J → J'' → ℂ) :
    swapKernel (compKernel T S) = compKernel (swapKernel S) (swapKernel T) :=
  funext fun _ => funext fun _ => tsum_congr fun _ => mul_comm _ _
theorem pauliCombination_mem_traceless (x : Fin 3 → ℂ) :
    ∑ a, x a • ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_smul_pauli_mem <;> assumption
theorem pauliCoeff_combination (x : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ b, x b • ComplexMatrix2.pauliFamily b) = x a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
section OddExtension
variable {β : Type} {pos : β → Prop} (rev : β → β)
def oddExtension (c : Fin 3 × {b // pos b} → ℂ) : β → ComplexMatrix2 :=
  open Classical in fun b =>
    if h : pos b then ofPauliCoeffs c ⟨b, h⟩
    else if h' : pos (rev b) then -ofPauliCoeffs c ⟨rev b, h'⟩ else 0
variable {rev}
theorem oddExtension_of_pos (c : Fin 3 × {b // pos b} → ℂ) {b : β} (h : pos b) :
    oddExtension rev c b = ofPauliCoeffs c ⟨b, h⟩ := dif_pos h
theorem oddExtension_mem (c : Fin 3 × {b // pos b} → ℂ) {b : β} (h : pos b) :
    oddExtension rev c b ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.LocalKernels.BracketAtPeriodicLift.antisymmExtend_mem <;> assumption
theorem toPauliCoeffs_oddExtension (c : Fin 3 × {b // pos b} → ℂ) :
    toPauliCoeffs (fun b : {b // pos b} => oddExtension rev c b.1) = c := by apply _root_.YangMills.Construction.LocalKernels.BracketAtPeriodicLift.toPauliCoeffs_antisymmExtend <;> assumption
theorem oddExtension_opposite (hrr : ∀ b, rev (rev b) = b) (hx : ∀ b, Xor (pos b) (pos (rev b)))
    (c : Fin 3 × {b // pos b} → ℂ) (b : β) : oddExtension rev c (rev b) = -oddExtension rev c b := by apply _root_.YangMills.Construction.LocalKernels.BracketAtPeriodicLift.antisymmExtend_rev <;> assumption
end OddExtension
theorem link_opposite_opposite {a : ℝ} (b : InfiniteLattice.Link a) : b.opposite.opposite = b := by apply _root_.YangMills.Construction.InfiniteLattice.Link.opposite_opposite <;> assumption
theorem link_orientation_xor {a : ℝ} (ha : 0 < a) (b : InfiniteLattice.Link a) :
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.Unbounded.xor_isPositivelyOriented_opposite <;> assumption
section Surjectivity
variable {L n k : ℕ}
def CoeffsSurjective (L : ℕ) {k : ℕ} (A : CellClass k) : Prop :=
  ∀ g : Idx L A.colourPairs → ℂ, ∃ f : (CellClass.fullSpace L A).complexSubmodule,
    CellClass.coeffsOn L A f = g
def QuotCoeffsSurjective (L n : ℕ) {k : ℕ} (A : CellClass k) : Prop :=
  ∀ g : A.colourPairs.ImageCarrier L n → ℂ, ∃ f : (CellClass.quotSpace L n A).complexSubmodule,
    CellClass.quotCoeffsOn L n A f = g
theorem coeffsSurjective_vertexClass (j : ℕ) (h : j ≤ k) :
    CoeffsSurjective L (CellClass.vertexClass k j h) := fun g => by
  refine ⟨⟨CellClass.ofCoeffs L (CellClass.vertexClass k j h) g,
    fun _ _ => pauliCombination_mem_traceless _⟩, ?_⟩
  funext ι
  rcases ι with ⟨⟨⟩, p⟩
  exact pauliCoeff_combination (fun a => g ⟨(), (a, p.2)⟩) p.1
theorem quotCoeffsSurjective_vertexClass (j : ℕ) (h : j ≤ k) :
    QuotCoeffsSurjective L n (CellClass.vertexClass k j h) :=
  fun g => by
  classical
  let c : Fin 3 × QuotientCell L n k j .vertex → ℂ := fun p =>
    if hp : p ∈ (CellClass.vertexClass k j h).colourComponent.image L n then g ⟨(), ⟨p, hp⟩⟩ else 0
  refine ⟨⟨ofPauliCoeffs c, fun _ _ => pauliCombination_mem_traceless _⟩, ?_⟩
  funext κ
  rcases κ with ⟨⟨⟩, p, hp⟩
  refine (pauliCoeff_combination (fun a => c (a, p.2)) p.1).trans ?_
  exact dif_pos hp
theorem coeffsSurjective_edgeClass (j : ℕ) (h : j ≤ k) (ha : 0 < meshAt L k j) :
    CoeffsSurjective L (CellClass.edgeClass k j h) := fun g => by
  refine ⟨⟨oddExtension (pos := fun b : FullSpace.Edge L k j => b.IsPositivelyOriented)
      InfiniteLattice.Link.opposite (fun p => g ⟨(), p⟩),
    fun _ hb => oddExtension_mem _ hb,
    oddExtension_opposite link_opposite_opposite (link_orientation_xor ha) _⟩, ?_⟩
  funext ι
  rcases ι with ⟨⟨⟩, p⟩
  exact congrFun (toPauliCoeffs_oddExtension
    (pos := fun b : FullSpace.Edge L k j => b.IsPositivelyOriented)
    (rev := InfiniteLattice.Link.opposite) fun p => g ⟨(), p⟩) p
theorem quotCoeffsSurjective_edgeClass (j : ℕ) (h : j ≤ k)
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented) :
    QuotCoeffsSurjective L n (CellClass.edgeClass k j h) := fun g => by
  classical
  let c : Fin 3 × {b : Edge L n k j // b.IsPositivelyOriented} → ℂ := fun p =>
    if hp : p ∈ (CellClass.edgeClass k j h).colourComponent.image L n then g ⟨(), ⟨p, hp⟩⟩ else 0
  refine ⟨⟨oddExtension (pos := fun b : Edge L n k j => b.IsPositivelyOriented)
      PeriodicLattice.Bond.opposite c,
    fun _ hb => oddExtension_mem _ hb,
    oddExtension_opposite PeriodicLattice.Bond.opposite_opposite hx _⟩, ?_⟩
  funext κ
  rcases κ with ⟨⟨⟩, p, hp⟩
  refine (congrFun (toPauliCoeffs_oddExtension
    (pos := fun b : Edge L n k j => b.IsPositivelyOriented)
    (rev := PeriodicLattice.Bond.opposite) c) p).trans ?_
  exact dif_pos hp
end Surjectivity
section Chosen
variable {L n k : ℕ} {A A' : CellClass k}
open Classical in
theorem kernel_eq_of_represents (hA : CoeffsSurjective L A)
    {m : (CellClass.fullSpace L A).complexSubmodule →
      (CellClass.fullSpace L A').index → ComplexMatrix2}
    {T T' : KernelMatrix (Idx L A.colourPairs) (Idx L A'.colourPairs)}
    (hT : IsRepresentedOnPairs L A A' m T) (hT' : IsRepresentedOnPairs L A A' m T') : T = T' := by
  funext ι' ι
  obtain ⟨f, hf⟩ := hA fun κ => if κ = ι then 1 else 0
  have e := (hT f).2.symm.trans (hT' f).2
  rw [hf] at e
  have e' := congrFun e ι'
  rwa [applyKernel_indicator, applyKernel_indicator] at e'
open Classical in
theorem matrix_eq_of_represents (hA : QuotCoeffsSurjective L n A)
    {m : (CellClass.quotSpace L n A).complexSubmodule → A'.colourPairs.ImageCarrier L n → ℂ}
    {M M' : KernelMatrix (A.colourPairs.ImageCarrier L n) (A'.colourPairs.ImageCarrier L n)}
    (hM : ∀ f : (CellClass.quotSpace L n A).complexSubmodule,
      m f = applyKernel M (CellClass.quotCoeffsOn L n A f))
    (hM' : ∀ f : (CellClass.quotSpace L n A).complexSubmodule,
      m f = applyKernel M' (CellClass.quotCoeffsOn L n A f)) : M = M' := by
  funext κ' κ
  obtain ⟨f, hf⟩ := hA fun c => if c = κ then 1 else 0
  have e := (hM f).symm.trans (hM' f)
  rw [hf] at e
  have e' := congrFun e κ'
  rwa [applyKernel_indicator, applyKernel_indicator] at e'
theorem chosen_of_periodizes (hA : CoeffsSurjective L A) (hA' : QuotCoeffsSurjective L n A) {R : ℝ}
    {mW : ((CellClass.fullSpace L A).index → ComplexMatrix2) →
      (CellClass.fullSpace L A').index → ComplexMatrix2}
    {mT : ((CellClass.quotSpace L n A).index → ComplexMatrix2) →
      (CellClass.quotSpace L n A').index → ComplexMatrix2}
    (hp : Periodizes L n A A' R mW mT) :
    IsRLocal L A.colourPairs A'.colourPairs R (pairKernelOfMap L A A' mW) ∧
      KernelDescends L n A.colourPairs A'.colourPairs (pairKernelOfMap L A A' mW)
        (pairMatrixOfMap L n A A' mT) := by
  obtain ⟨T, m, hloc, hgiv, hm, ⟨M, hM, hdesc⟩, -⟩ := hp
  have hK : pairKernelOfMap L A A' mW = T :=
    kernel_eq_of_represents hA
      (Classical.epsilon_spec (p := fun T => IsRepresentedOnPairs L A A' (fun f => mW f) T)
      ⟨T, hgiv⟩) hgiv
  have hM' : ∀ f : (CellClass.quotSpace L n A).complexSubmodule,
      CellClass.quotCoeffsOn L n A' (mT f) =
        applyKernel M (CellClass.quotCoeffsOn L n A f) := fun f => by
    rw [← hm f]
    exact hM f
  have hN : pairMatrixOfMap L n A A' mT = M :=
    matrix_eq_of_represents (m := fun f => CellClass.quotCoeffsOn L n A' (mT f)) hA'
      (Classical.epsilon_spec (p := fun M => ∀ f : (CellClass.quotSpace L n A).complexSubmodule,
        CellClass.quotCoeffsOn L n A' (mT f) = applyKernel M (CellClass.quotCoeffsOn L n A f))
        ⟨M, hM'⟩) hM'
  rw [hK, hN]
  exact ⟨hloc, hdesc⟩
theorem swap_descends (sp : DescendsAlgebra (k := k) L n) {R : ℝ} (hR : 0 ≤ R)
    (hs : 2 * R < (periodSide L n : ℝ))
    {T : KernelMatrix (Idx L A.colourPairs) (Idx L A'.colourPairs)}
    {M : KernelMatrix (A.colourPairs.ImageCarrier L n) (A'.colourPairs.ImageCarrier L n)}
    (hl : IsRLocal L A.colourPairs A'.colourPairs R T)
    (hd : KernelDescends L n A.colourPairs A'.colourPairs T M) :
    IsRLocal L A'.colourPairs A.colourPairs R (swapKernel T) ∧
      KernelDescends L n A'.colourPairs A.colourPairs (swapKernel T) (swapKernel M) := by
  have zl : IsRLocal L A.colourPairs A.colourPairs R
      (0 : KernelMatrix (Idx L A.colourPairs) (Idx L A.colourPairs)) :=
    fun _ _ _ => rfl
  have zd : KernelDescends L n A.colourPairs A.colourPairs
      (0 : KernelMatrix (Idx L A.colourPairs) (Idx L A.colourPairs))
      (0 : KernelMatrix (A.colourPairs.ImageCarrier L n) (A.colourPairs.ImageCarrier L n)) :=
    ⟨⟨R, hR, zl⟩, fun f => by
      funext ι
      simp [PeriodicOperators.applyKernel, WeightedIndexSet.lift]⟩
  obtain ⟨-, -, -, -, -, h⟩ := sp A.colourPairs A'.colourPairs A.colourPairs R hR T T 0 M M 0
    hl hl zl hd hd zd
  obtain ⟨-, h₂, h₃⟩ := h hs
  have eT : kernelT L A.colourPairs A'.colourPairs T = swapKernel T := by
    funext ι ι'
    show (((1 : ℝ) / (1 : ℝ) : ℝ) : ℂ) * T ι' ι = T ι' ι
    simp
  have eM : quotMatrixT L n A.colourPairs A'.colourPairs M = swapKernel M := by
    funext ι ι'
    show (((1 : ℝ) / (1 : ℝ) : ℝ) : ℂ) * M ι' ι = M ι' ι
    simp
  rw [eT] at h₂ h₃
  rw [eM] at h₃
  exact ⟨h₂, h₃⟩
end Chosen
theorem backgroundFactorsDescendClaim_holds (hSP : LocalKernels.DescendingKernelAlgebra)
    (hExt : LocalKernels.ZeroExtensionOfVertexFunctions.Claim)
    (hIter : LocalKernels.PeriodicLiftDescent.CovariantMeansDescend)
    (hSec : LocalKernels.QuadraticKernelAtExtensionDescends)
    (hComm : LocalKernels.BracketAtPeriodicLift.DescendsClaim)
    (hAct : LocalKernels.HessianAtLifts.HessianDescendsAtLifts)
    (hDiff : LocalKernels.CovDiffAtLift.Claim)
    (hXor : PeriodicLattice.LevelBondOrientationDichotomy) : BackgroundFactorsDescendClaim := by
  intro L hL k hk n hn U hU J hJ μ hμ
  have sp := hSP L hL k n hn
  have hL0 : (0 : ℝ) < (L : ℝ) := by
    have : 0 < L := by
      have := hL.2
      omega
    exact_mod_cast this
  have hside : 2 * (6 : ℝ) < (periodSide L n : ℝ) := by
    have h13 : 13 ≤ L ^ n :=
      hL.2.trans (Nat.le_self_pow (Nat.pos_iff_ne_zero.1 hn) L)
    have : 12 < periodSide L n := by
      unfold periodSide
      omega
    have e : (12 : ℝ) < (periodSide L n : ℝ) := by exact_mod_cast this
    linarith
  have hside2 : 2 * (2 : ℝ) < (periodSide L n : ℝ) := by linarith
  have ha₀ : 0 < meshAt L k 0 := zpow_pos hL0 _
  have hx₀ : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    hXor L n k hL hn hk 0 (Nat.zero_le k)
  have rB := coeffsSurjective_edgeClass (L := L) (k := k) 0 (Nat.zero_le k) ha₀
  have iB := quotCoeffsSurjective_edgeClass (L := L) (n := n) (k := k) 0 (Nat.zero_le k) hx₀
  have rS := coeffsSurjective_vertexClass (L := L) (k := k) 0 (Nat.zero_le k)
  have iS := quotCoeffsSurjective_vertexClass (L := L) (n := n) (k := k) 0 (Nat.zero_le k)
  have rK := coeffsSurjective_vertexClass (L := L) (k := k) k le_rfl
  have iK := quotCoeffsSurjective_vertexClass (L := L) (n := n) (k := k) k le_rfl
  have hUc : U ∈ fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup := hU.1
  have a := chosen_of_periodizes rB iB (hAct L hL k n hn 0 (Nat.zero_le k) U hUc)
  have d := chosen_of_periodizes rS iS (hDiff L hL k n hn 0 (Nat.zero_le k) U hUc)
  have hIt := (hIter L hL k n hn hk U hUc hU) k le_rfl hk
  have g := chosen_of_periodizes rS iS hIt.2.2.1
  have c := chosen_of_periodizes rB iB hIt.2.2.2
  have e := chosen_of_periodizes rK iK (hExt L hL k n hn hk)
  have hC := (hComm L hL k n hn 0 (Nat.zero_le k) U hUc J hJ).2
  have hC' := hC.2.2 _ _ (Classical.epsilon_spec hC.1.exists) (Classical.epsilon_spec hC.2.1.exists)
  have hQ := hSec L hL k n hn hk U hUc hU μ hμ
  have hQ' := hQ.2.2 _ _ (Classical.epsilon_spec hQ.1.exists) (Classical.epsilon_spec hQ.2.1.exists)
  have a' := swap_descends sp (by norm_num) hside2 a.1 a.2
  have d' := swap_descends sp (by norm_num) hside2 d.1 d.2
  have g' := swap_descends sp (by norm_num) hside g.1 g.2
  have c' := swap_descends sp (by norm_num) hside c.1 c.2
  have e' := swap_descends sp (by norm_num) hside e.1 e.2
  have v' := swap_descends sp (by norm_num) hside2 hC'.1 hC'.2.1
  have q' := swap_descends sp (by norm_num) hside hQ'.1 hQ'.2.1
  have hσ := sp _ _ _ 6 (by norm_num) _ _ _ _ _ _ e.1 e.1 c.1 e.2 e.2 c.2
  have hσ' := sp _ _ _ 6 (by norm_num) _ _ _ _ _ _ c'.1 c'.1 e'.1 c'.2 c'.2 e'.2
  exact
    { hess := a.2
      hess_swap := a'.2
      brk := hC'.2.1
      brk_swap := v'.2
      quad := hQ'.2.1
      quad_swap := q'.2
      sigma := hσ.2.2.2.2.1
      sigma_swap := by
        show KernelDescends L n _ _ (swapKernel (compKernel _ _))
          (swapKernel (compKernel _ _))
        rw [swapKernel_compKernel, swapKernel_compKernel]
        exact hσ'.2.2.2.2.1
      diff := d.2
      diff_swap := d'.2
      avg := g.2
      avg_swap := g'.2
      scale := rfl }
end YangMills.Construction.Tower.BackgroundFactorsDescent
end
