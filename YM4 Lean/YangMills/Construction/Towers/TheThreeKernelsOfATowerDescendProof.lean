import YangMills.Construction.Towers.TheFreeOperatorsArePeriodicOperatorsProof
import YangMills.Construction.Towers.DifferencesGiveTheTwoOperatorsAtOneOnTheUnitLatticeProof
import YangMills.Construction.Towers.PeriodicExtensionsAndPeriodisation
import YangMills.Construction.Towers.PolydiscServesAtTheSideInfinityProof
import YangMills.Construction.Towers.TheThreeKernelsOfATowerDescend
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.KernelDescent
open LocalKernels LocalKernels.Periodisation
open PeriodicOperators
section PauliCoordinates
theorem pauli_combination_mem_traceless (x : Fin 3 → ℂ) :
    ∑ a, x a • Matrices.ComplexMatrix2.pauliFamily a ∈ Matrices.ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_smul_pauli_mem <;> assumption
theorem pauliCoeff_combination (x : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ i, x i • Matrices.ComplexMatrix2.pauliFamily i) = x a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
end PauliCoordinates
section EdgeEvaluations
variable {L k j : ℕ}
theorem meshAt_pos (hL : Conventions.IsAdmissibleBlockingFactor L) : 0 < meshAt L k j := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.meshAt_pos <;> assumption
theorem opposite_isPositivelyOriented_of_not {e : FullSpace.Edge L k j}
    (he : ¬e.IsPositivelyOriented) : e.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.InfiniteSideAdmissibility.fullSpace_opposite_isPositivelyOriented <;> assumption
theorem edgePauliCoordinates_ofCoeffs_mem (hL : Conventions.IsAdmissibleBlockingFactor L)
    (c : (FullSpace.edgePauliCoordinates L k j).Index → ℂ) :
    (FullSpace.edgePauliCoordinates L k j).ofCoeffs c ∈ FullSpace.complexEdgeForms (meshAt L k j) := by apply _root_.YangMills.Construction.Tower.FreeOperators.edgePauliCoordinates_ofCoeffs_mem <;> assumption
theorem edgePauliCoordinates_coeffs_ofCoeffs (c : (FullSpace.edgePauliCoordinates L k j).Index → ℂ) :
    (FullSpace.edgePauliCoordinates L k j).coeffs ((FullSpace.edgePauliCoordinates L k j).ofCoeffs c) = c := by apply _root_.YangMills.Construction.Tower.FreeOperators.toPauliCoeffs_restrict_edgeValue <;> assumption
theorem toPauliCoeffs_ofPauliCoeffs {σ : Type} (c : Fin 3 × σ → ℂ) :
    toPauliCoeffs (ofPauliCoeffs c) = c := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.toPauliCoeffs_ofPauliCoeffs <;> assumption
end EdgeEvaluations
section LocalKernelsOnCells
variable {L n k : ℕ}
def colourCellEquiv (L : ℕ) {k : ℕ} (A : CellClass k) :
    (Fin 3 × Cell L k A.level A.cellType) ≃ Idx L A.colourPairs where
  toFun a := ⟨(), a⟩
  invFun ι := ι.2
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨⟩, a⟩
    rfl
theorem represents_of_isRepresentedOnPairs (hEv : LocalKernelFacts (k := k) L)
    {A A' : CellClass k} {R : ℝ}
    (hR : 0 ≤ R) {T : KernelMatrix (Idx L A.colourPairs) (Idx L A'.colourPairs)}
    (hl : IsRLocal L A.colourPairs A'.colourPairs R T)
    {m : ((CellClass.fullSpace L A).index → Matrices.ComplexMatrix2) →
      (CellClass.fullSpace L A').index → Matrices.ComplexMatrix2}
    (hg : IsRepresentedOnPairs L A A' (fun f => m f) T)
    (ofC : (Fin 3 × Cell L k A.level A.cellType → ℂ) →
      (CellClass.fullSpace L A).index → Matrices.ComplexMatrix2)
    (hmem : ∀ c, ofC c ∈ (CellClass.fullSpace L A).complexSubmodule)
    (hread : ∀ c, CellClass.coeffsOn L A (ofC c) = fun ι => c ι.2) :
    Represents (I := Fin 3 × Cell L k A.level A.cellType) (J := Fin 3 × Cell L k A'.level A'.cellType)
      (fun a b => T (colourCellEquiv L A' a) (colourCellEquiv L A b))
      (fun c a => CellClass.coeffsOn L A' (m (ofC c)) (colourCellEquiv L A' a)) := by
  intro c
  have hr : CellClass.coeffsOn L A' (m (ofC c)) = applyKernel T (fun ι => c ι.2) := by
    have h := (hg ⟨ofC c, hmem c⟩).2
    simpa only [hread] using h
  have hfin := (hEv A.colourPairs A'.colourPairs R hR T hl).1 (fun ι => c ι.2)
  constructor
  · intro a
    have hf : (Function.support fun b =>
        ‖T (colourCellEquiv L A' a) (colourCellEquiv L A b) * c b‖).Finite := by
      refine ((hfin (colourCellEquiv L A' a)).preimage (colourCellEquiv L A).injective.injOn).subset ?_
      intro b hb
      show T (colourCellEquiv L A' a) (colourCellEquiv L A b) * c b ≠ 0
      exact norm_ne_zero_iff.1 (Function.mem_support.1 hb)
    exact summable_of_hasFiniteSupport hf
  · funext a
    exact ((colourCellEquiv L A).tsum_eq fun ι => T (colourCellEquiv L A' a) ι * c ι.2).trans
      (congrFun hr (colourCellEquiv L A' a)).symm
theorem eq_of_unique_kernel (hEv : LocalKernelFacts (k := k) L) {A A' : CellClass k} {R : ℝ}
    (hR : 0 ≤ R)
    {m : ((CellClass.fullSpace L A).index → Matrices.ComplexMatrix2) →
      (CellClass.fullSpace L A').index → Matrices.ComplexMatrix2}
    (ofC : (Fin 3 × Cell L k A.level A.cellType → ℂ) →
      (CellClass.fullSpace L A).index → Matrices.ComplexMatrix2)
    (hmem : ∀ c, ofC c ∈ (CellClass.fullSpace L A).complexSubmodule)
    (hread : ∀ c, CellClass.coeffsOn L A (ofC c) = fun ι => c ι.2)
    (K : KernelMatrix (Fin 3 × Cell L k A.level A.cellType) (Fin 3 × Cell L k A'.level A'.cellType))
    (hU : ∀ T : KernelMatrix (Fin 3 × Cell L k A.level A.cellType)
        (Fin 3 × Cell L k A'.level A'.cellType),
      Represents T (fun c a => CellClass.coeffsOn L A' (m (ofC c)) (colourCellEquiv L A' a)) → T = K)
    (T : KernelMatrix (Idx L A.colourPairs) (Idx L A'.colourPairs))
    (hl : IsRLocal L A.colourPairs A'.colourPairs R T)
    (hg : IsRepresentedOnPairs L A A' (fun f => m f) T) :
    T = fun ι' ι => K ι'.2 ι.2 := by
  have h := hU _ (represents_of_isRepresentedOnPairs hEv hR hl hg ofC hmem hread)
  funext ι' ι
  obtain ⟨⟨⟩, a⟩ := ι'
  obtain ⟨⟨⟩, b⟩ := ι
  exact congrFun (congrFun h a) b
theorem kernelT_colourPairs (A A' : CellClass k)
    (T : KernelMatrix (Idx L A.colourPairs) (Idx L A'.colourPairs)) :
    kernelT L A.colourPairs A'.colourPairs T = fun ι' ι => T ι ι' := by
  funext ι' ι
  have h : (A.colourPairs.toPeriodicData L).weightOf ι' = 1 := rfl
  have h' : (A'.colourPairs.toPeriodicData L).weightOf ι = 1 := rfl
  simp [kernelT, PeriodicOperators.wTranspose, h, h']
theorem quotMatrixT_colourPairs (A A' : CellClass k)
    (M : KernelMatrix (A.colourPairs.ImageCarrier L n) (A'.colourPairs.ImageCarrier L n)) :
    quotMatrixT L n A.colourPairs A'.colourPairs M = swapKernel M := by
  funext ι' ι
  have h : A.colourPairs.imageWeight L n ι' = 1 := rfl
  have h' : A'.colourPairs.imageWeight L n ι = 1 := rfl
  simp [quotMatrixT, PeriodicOperators.wTranspose, swapKernel, h, h']
theorem descends_of_periodizes (hEv : LocalKernelFacts (k := k) L)
    (hSP : DescendsAlgebra (k := k) L n) {A A' : CellClass k} {R : ℝ}
    (hR : 0 ≤ R) (hs : 2 * R < (periodSide L n : ℝ))
    {mW : ((CellClass.fullSpace L A).index → Matrices.ComplexMatrix2) →
      (CellClass.fullSpace L A').index → Matrices.ComplexMatrix2}
    {mT : ((CellClass.quotSpace L n A).index → Matrices.ComplexMatrix2) →
      (CellClass.quotSpace L n A').index → Matrices.ComplexMatrix2}
    (hP : Periodizes L n A A' R mW mT)
    (K : KernelMatrix (Fin 3 × Cell L k A.level A.cellType) (Fin 3 × Cell L k A'.level A'.cellType))
    (hK : ∀ T, IsRLocal L A.colourPairs A'.colourPairs R T →
      IsRepresentedOnPairs L A A' (fun f => mW f) T → T = fun ι' ι => K ι'.2 ι.2) :
    ∃ M : KernelMatrix (A.colourPairs.ImageCarrier L n) (A'.colourPairs.ImageCarrier L n),
      (∀ f : (CellClass.quotSpace L n A).complexSubmodule,
        CellClass.quotCoeffsOn L n A' (mT f.1) =
          applyKernel M (CellClass.quotCoeffsOn L n A f.1)) ∧
      KernelDescends L n A.colourPairs A'.colourPairs (fun ι' ι => K ι'.2 ι.2) M ∧
      KernelDescends L n A'.colourPairs A.colourPairs (fun ι' ι => K ι.2 ι'.2) (swapKernel M) := by
  obtain ⟨T, m, hl, hg, hv, ⟨M, hM, hd⟩, ⟨M₂, -, hd₂⟩⟩ := hP
  have hT := hK T hl hg
  have hlt := (hEv _ _ R hR T hl).2.2.1
  obtain ⟨-, -, -, -, -, hlast⟩ := hSP A.colourPairs A'.colourPairs A'.colourPairs R hR T T
    (kernelT L A.colourPairs A'.colourPairs T) M M M₂ hl hl hlt hd hd hd₂
  have hdt := (hlast hs).2.2
  rw [kernelT_colourPairs, quotMatrixT_colourPairs] at hdt
  subst hT
  refine ⟨M, fun f => ?_, hd, hdt⟩
  rw [← hv f]
  exact hM f
theorem twelve_lt_periodSide (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) :
    (12 : ℝ) < (periodSide L n : ℝ) := by
  have h₁ : L ≤ L ^ n := Nat.le_self_pow hn.ne' L
  have h₂ : 13 ≤ L := hL.2
  have h₃ : 12 < periodSide L n := by
    unfold periodSide
    omega
  exact_mod_cast h₃
end LocalKernelsOnCells
theorem threeKernelsDescend (hP : LocalKernels.Periodisation.PeriodisationHolds)
    (hK : ThreeMapKernels.Claim) : ThreeKernelsDescend.DescentStatement := by
  intro L hL k hk n hn U hU
  obtain ⟨-, -, hSP, hEv, -, -, -, hAct, hAvg⟩ := hP L hL k n hn
  have hW := (hK L hL k hk).2
  have hAv := hAvg hk U hU.1
  have hU' := hAv.1.1 hU
  obtain ⟨-, -, hIt, -, -⟩ := hAv.2 hU 0 (Submodule.zero_mem _)
  obtain ⟨-, hQ, hA, -⟩ := hIt k le_rfl hk
  obtain ⟨-, hD, -, -⟩ := hAct 0 (Nat.zero_le k) U hU.1 0 (Submodule.zero_mem _)
  obtain ⟨hq, ha⟩ := hW.2.2.2 _ hU'
  have hd := hW.2.1 _ hU'.1
  have hs := twelve_lt_periodSide hL hn
  have he₀ : ∀ c, (FullSpace.edgePauliCoordinates L k 0).ofCoeffs c ∈
      (CellClass.fullSpace L (edgesAtZero k)).complexSubmodule := edgePauliCoordinates_ofCoeffs_mem hL
  have hv₀ : ∀ c : Fin 3 × FullSpace.Vertex L k 0 → ℂ, ofPauliCoeffs c ∈
      (CellClass.fullSpace L (verticesAtZero k)).complexSubmodule := fun c =>
    Submodule.mem_pi.2 fun x _ => pauli_combination_mem_traceless _
  have hre : ∀ c, CellClass.coeffsOn L (edgesAtZero k) ((FullSpace.edgePauliCoordinates L k 0).ofCoeffs c) =
      fun ι => c ι.2 := fun c => funext fun ι => congrFun (edgePauliCoordinates_coeffs_ofCoeffs c) ι.2
  have hrv : ∀ c : Fin 3 × FullSpace.Vertex L k 0 → ℂ,
      CellClass.coeffsOn L (verticesAtZero k) (ofPauliCoeffs c) = fun ι => c ι.2 := fun c =>
    funext fun ι => congrFun (toPauliCoeffs_ofPauliCoeffs c) ι.2
  refine ⟨descends_of_periodizes hEv hSP (by norm_num) (by linarith) hQ _
      (fun T hl hg => eq_of_unique_kernel (A := edgesAtZero k) (A' := CellClass.edgeClass k k le_rfl)
        (m := FullSpace.iterCovariantDeriv L k (liftGaugeField L n k 0 U) k)
        hEv (by norm_num) (FullSpace.edgePauliCoordinates L k 0).ofCoeffs he₀ hre _ hq.unique T hl hg),
    descends_of_periodizes hEv hSP (by norm_num) (by linarith) hA _
      (fun T hl hg => eq_of_unique_kernel (A := verticesAtZero k)
        (A' := CellClass.vertexClass k k le_rfl)
        (m := FullSpace.iterAdjointCubeAverage L k (liftGaugeField L n k 0 U) k)
        hEv (by norm_num) ofPauliCoeffs hv₀ hrv _ ha.unique T hl hg),
    descends_of_periodizes hEv hSP (by norm_num) (by linarith) hD _
      (fun T hl hg => eq_of_unique_kernel (A := verticesAtZero k) (A' := edgesAtZero k)
        (m := FullSpace.covDiff (liftGaugeField L n k 0 U))
        hEv (by norm_num) ofPauliCoeffs hv₀ hrv _ hd.unique T hl hg)⟩
end YangMills.Construction.Tower.KernelDescent
end
