import YangMills.Construction.Towers.CrossingAverageOnASideProof
import YangMills.Construction.Towers.MeansAtTheTrivialConfigurationOfTheScaledPictureOnASideProof
import YangMills.Construction.Towers.ScaledROnASide
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.RescaledRFiniteSide
theorem pauliFamily_mem_traceless (a : Fin 3) :
    Matrices.ComplexMatrix2.pauliFamily a ∈ Matrices.ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
theorem pauliCoeff_sum_smul (v : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ c, v c • Matrices.ComplexMatrix2.pauliFamily c) = v a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
theorem pauliCoeff_smul (z : ℂ) (a b : Fin 3) :
    pauliCoeff a (z • Matrices.ComplexMatrix2.pauliFamily b) = if a = b then z else 0 := by apply _root_.YangMills.Construction.Tower.CrossingSmoothingContraction.pauliCoeff_smul_pauliFamily <;> assumption
theorem real_smul_eq_complex_smul (z : ℝ) (M : Matrices.ComplexMatrix2) :
    z • M = (z : ℂ) • M := by apply _root_.YangMills.SharedProofs.p9878 <;> assumption
section Entries
variable {L n k : ℕ}
def singlePauli (b : Fin 3) (p : Vertex L n k 0) : Vertex L n k 0 → Matrices.ComplexMatrix2 :=
  open Classical in fun q => if q = p then Matrices.ComplexMatrix2.pauliFamily b else 0
theorem singlePauli_mem (b : Fin 3) (p : Vertex L n k 0) :
    singlePauli b p ∈ Matrices.GroupLieProduct.tracelessFunctions (Vertex L n k 0) := by
  intro q _
  unfold singlePauli
  split_ifs
  · exact pauliFamily_mem_traceless b
  · exact Submodule.zero_mem _
theorem toPauliCoeffs_singlePauli (b : Fin 3) (p : Vertex L n k 0) :
    toPauliCoeffs (singlePauli b p) = open Classical in Pi.single (b, p) 1 := by
  classical
  funext ι
  obtain ⟨c, q⟩ := ι
  show pauliCoeff c (singlePauli b p q) = _
  by_cases hq : q = p
  · subst hq
    have h := pauliCoeff_smul 1 c b
    rw [one_smul] at h
    have e : singlePauli b q q = Matrices.ComplexMatrix2.pauliFamily b := by simp [singlePauli]
    rw [e, h]
    by_cases hc : c = b
    · subst hc
      simp
    · rw [if_neg hc, Pi.single_eq_of_ne]
      intro h'
      exact hc (congrArg Prod.fst h')
  · have e : singlePauli b p q = 0 := by simp [singlePauli, hq]
    have h := pauliCoeff_smul 0 c b
    rw [zero_smul] at h
    rw [e, h, Pi.single_eq_of_ne]
    · simp
    · intro h'
      exact hq (congrArg Prod.snd h')
theorem finsum_singlePauli (b : Fin 3) (p : Vertex L n k 0) (S : Set (Vertex L n k 0)) :
    ∑ᶠ q ∈ S, singlePauli b p q =
      open Classical in if p ∈ S then Matrices.ComplexMatrix2.pauliFamily b else 0 := by
  classical
  rw [finsum_eq_single _ p]
  · rw [finsum_eq_if]
    simp [singlePauli]
  · intro q hq
    simp [singlePauli, hq]
theorem kernel_apply (hM : RescaledConditions.TrivialAverages L n k) (a b : Fin 3)
    (y : Vertex L n k k) (p : Vertex L n k 0) :
    kernel L n k (a, y) (b, p) = open Classical in
      if a = b ∧ p ∈ TrivialLinearization.baseVerticesOfCube L n k k y then
        ((finestMesh L k ^ 4 : ℝ) : ℂ) else 0 := by
  classical
  have h := hM.1 (singlePauli b p) (singlePauli_mem b p) y
  have hact : ∀ ι', PeriodicOperators.applyKernel (rescaledOperators L n k (trivialField L n k 0)).R
      (toPauliCoeffs (singlePauli b p)) ι' = kernel L n k ι' (b, p) := by
    intro ι'
    show ∑' ι, _ * _ = _
    rw [toPauliCoeffs_singlePauli, tsum_eq_single (b, p)]
    · simp [kernel, expConjAtZero]
    · intro ι hι
      rw [Pi.single_eq_of_ne hι, mul_zero]
  have hl : ∑ c, kernel L n k (c, y) (b, p) • Matrices.ComplexMatrix2.pauliFamily c =
      (finestMesh L k ^ 4) •
        ∑ᶠ q ∈ TrivialLinearization.baseVerticesOfCube L n k k y, singlePauli b p q := by
    rw [← h]
    show _ = ∑ c, _ • Matrices.ComplexMatrix2.pauliFamily c
    exact Finset.sum_congr rfl fun c _ => by rw [hact]
  have hc := pauliCoeff_sum_smul (fun c => kernel L n k (c, y) (b, p)) a
  rw [hl, finsum_singlePauli, real_smul_eq_complex_smul] at hc
  rw [← hc]
  by_cases hp : p ∈ TrivialLinearization.baseVerticesOfCube L n k k y
  · rw [if_pos hp, pauliCoeff_smul]
    by_cases hab : a = b
    · simp [hab, hp]
    · simp [hab]
  · have h0 := pauliCoeff_smul 0 a b
    rw [zero_smul] at h0
    rw [if_neg hp, smul_zero, h0]
    simp [hp]
end Entries
section Cubes
variable {L n k : ℕ}
theorem baseVerticesOfCube_finite (hL : 0 < L) (P : RefinedBlocksPartition L n k k k)
    (y : Vertex L n k k) : (TrivialLinearization.baseVerticesOfCube L n k k y).Finite := by apply _root_.YangMills.Construction.Tower.TrivialAveragesOnSide.finite_baseVerticesOfCube <;> assumption
theorem existsUnique_refinedBlock (P : RefinedBlocksPartition L n k k k) :
    ∀ i : ℕ, k - k = i → ∀ p : Vertex L n k i,
      ∃! y : Vertex L n k k, (p : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.refinedBlock k y := by
  intro i e
  subst e
  exact P.existsUnique_mem
end Cubes
theorem opNormLeOne_holds (hSchur : PeriodicOperators.SchurTest.Holds)
    (hMeans : TrivialAveragesOnEverySide)
    (hCubes : BlockPathContourPivotStatement) : OpNormLeOne := by
  classical
  intro L hL n k hn hk
  have hL0 : 0 < L := by
    have := hL.2
    omega
  have hM : RescaledConditions.TrivialAverages L n k := hMeans L hL k hk n hn
  obtain ⟨hPart, -⟩ := (hCubes L hL k k k hk le_rfl le_rfl).1 n hn
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL0
  have hη : 0 < finestMesh L k := by
    unfold finestMesh meshAt
    exact zpow_pos hLr _
  have hη4 : 0 < finestMesh L k ^ 4 := pow_pos hη 4
  have htop : meshAt L k k = 1 := by simp [meshAt]
  let S : Vertex L n k k → Set (Vertex L n k 0) := TrivialLinearization.baseVerticesOfCube L n k k
  let N : Vertex L n k k → Vertex L n k 0 → ℝ :=
    fun y p => if p ∈ S y then finestMesh L k ^ 4 else 0
  have hrow : ∀ y, Summable (N y) ∧ ∑' p, N y p ≤ 1 := by
    intro y
    have hfin := baseVerticesOfCube_finite hL0 hPart y
    have hs : HasSum (N y) (∑ p ∈ hfin.toFinset, N y p) :=
      hasSum_sum_of_ne_finset_zero fun p hp => by
        have hp' : p ∉ S y := by simpa using hp
        simp [N, hp']
    refine ⟨hs.summable, ?_⟩
    rw [hs.tsum_eq]
    have hval : ∑ p ∈ hfin.toFinset, N y p = (hfin.toFinset.card : ℝ) * finestMesh L k ^ 4 := by
      rw [Finset.sum_congr rfl fun p hp => ?_, Finset.sum_const, nsmul_eq_mul]
      have hp' : p ∈ S y := by simpa using hp
      simp [N, hp']
    have hcard : (hfin.toFinset.card : ℝ) = (finestMesh L k ^ 4)⁻¹ := by
      rw [← hM.2.1 y, Set.ncard_eq_toFinset_card _ hfin]
    rw [hval, hcard, inv_mul_cancel₀ hη4.ne']
  have hcol : ∀ p, Summable (fun y => N y p) ∧ ∑' y, N y p ≤ finestMesh L k ^ 4 := by
    intro p
    obtain ⟨y₀, hy₀, huniq⟩ := existsUnique_refinedBlock hPart 0 (Nat.sub_self k) p
    have hs : HasSum (fun y => N y p) (N y₀ p) :=
      hasSum_single y₀ fun y hy => by
        have hp : p ∉ S y := fun h => hy (huniq y h)
        simp [N, hp]
    refine ⟨hs.summable, ?_⟩
    rw [hs.tsum_eq]
    have hp : p ∈ S y₀ := hy₀
    simp [N, hp]
  have hzero : ∀ (b b' : Fin 3) (y : Vertex L n k k) (p : Vertex L n k 0), b' ≠ b →
      kernel L n k (b', y) (b, p) = 0 := by
    intro b b' y p h
    rw [kernel_apply hM, if_neg fun h' => h h'.1]
  have hbound : ∀ (b : Fin 3) (y : Vertex L n k k) (p : Vertex L n k 0),
      ‖kernel L n k (b, y) (b, p)‖ ≤ N y p := by
    intro b y p
    rw [kernel_apply hM]
    by_cases hp : p ∈ S y
    · have hp' : p ∈ TrivialLinearization.baseVerticesOfCube L n k k y := hp
      simp only [N, if_pos hp, true_and, if_pos hp', Complex.norm_real, Real.norm_eq_abs]
      exact (abs_of_pos hη4).le
    · have hp' : p ∉ TrivialLinearization.baseVerticesOfCube L n k k y := hp
      simp [N, hp, hp']
  have hnum : meshAt L k k ^ 4 * (1 * finestMesh L k ^ 4) ≤
      (1 : ℝ) ^ 2 * finestMesh L k ^ 4 := by
    rw [htop]
    simp
  have h := (hSchur.2 (Vertex L n k 0) (Vertex L n k k) (kernel L n k) N
    (meshWeight (finestMesh L k)) (meshWeight (meshAt L k k))
    (finestMesh L k ^ 4) (meshAt L k k ^ 4) 1 (finestMesh L k ^ 4) 1
    hη4 (by rw [htop]; norm_num) zero_le_one (fun _ => rfl) (fun _ => rfl)
    hzero hbound hrow hcol hnum).2 Set.univ
  exact h
end YangMills.Construction.Tower.RescaledRFiniteSide
end
