import YangMills.Construction.Lattice.OppositeBondsAndPositiveValues
import YangMills.Construction.Towers.CrossingAverageOnASideProof
import YangMills.Construction.Towers.KernelsOfThreeMapsOfATowerProof
import YangMills.Construction.Towers.MeansAtTheTrivialConfigurationOfTheScaledPictureOnASide
import YangMills.Construction.Towers.ScaledQOnASide
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.Matrices
namespace Tower
open YangMills.Construction.PeriodicOperators (applyKernel)
open YangMills.Construction.Tower.RescaledConditions
open YangMills.Construction.Tower.TrivialLinearization (baseVerticesOfCube)
namespace RescaledQFiniteSide
theorem pauliFamily_mem_traceless (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
theorem pauliCoeff_sum_smul (x : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ b, x b • ComplexMatrix2.pauliFamily b) = x a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
theorem pauliCoeff_smul_pauliFamily (z : ℂ) (a b : Fin 3) :
    pauliCoeff a (z • ComplexMatrix2.pauliFamily b) = if a = b then z else 0 := by apply _root_.YangMills.Construction.Tower.CrossingSmoothingContraction.pauliCoeff_smul_pauliFamily <;> assumption
theorem real_smul_eq_complex_smul (z : ℝ) (X : ComplexMatrix2) : z • X = (z : ℂ) • X := by apply _root_.YangMills.SharedProofs.p9878 <;> assumption
theorem hasSum_finsum_of_ne_zero {ι : Type} (f : ι → ℝ) (h : ∑ᶠ i, f i ≠ 0) :
    HasSum f (∑ᶠ i, f i) := by
  classical
  have hfin : (Function.support f).Finite := by
    by_contra hi
    exact h (finsum_of_infinite_support hi)
  rw [finsum_eq_sum_of_support_subset f (s := hfin.toFinset) (by simp)]
  exact hasSum_sum_of_ne_finset_zero fun x hx => by simpa using hx
section BasisEntries
variable {L n k : ℕ}
def basisForm (a : Fin 3) (e : PositiveEdge L n k 0) : Edge L n k 0 → ComplexMatrix2 :=
  open Classical in extendOddly fun q => if q = e.1 then ComplexMatrix2.pauliFamily a else 0
theorem basisForm_of_isPositive (a : Fin 3) (e : PositiveEdge L n k 0) {q : Edge L n k 0}
    (hq : q.IsPositivelyOriented) :
    basisForm a e q = open Classical in if q = e.1 then ComplexMatrix2.pauliFamily a else 0 := by
  classical
  simp [basisForm, extendOddly, hq]
theorem basisForm_mem
    (hO : ∀ q : Edge L n k 0, q.opposite.opposite = q ∧
      Xor q.IsPositivelyOriented q.opposite.IsPositivelyOriented)
    (a : Fin 3) (e : PositiveEdge L n k 0) : basisForm a e ∈ complexEdgeForms L n k 0 := by
  classical
  refine ⟨fun q hq => ?_, fun q => ?_⟩
  · rw [basisForm_of_isPositive a e hq]
    split_ifs
    · exact pauliFamily_mem_traceless a
    · exact Submodule.zero_mem _
  · obtain ⟨hr, hx⟩ := hO q
    rcases hx with ⟨hq, hq'⟩ | ⟨hq', hq⟩
    · simp [basisForm, extendOddly, hq, hq', hr]
    · simp [basisForm, extendOddly, hq, hq']
theorem toPauliCoeffs_basisForm (a : Fin 3) (e : PositiveEdge L n k 0) :
    toPauliCoeffs (restrictToPositiveEdges (basisForm a e)) =
      open Classical in Pi.single (a, e) 1 := by
  classical
  funext ι
  obtain ⟨c, q⟩ := ι
  show pauliCoeff c (basisForm a e q.1) = _
  rw [basisForm_of_isPositive a e q.2]
  by_cases hq : q = e
  · subst hq
    have h := pauliCoeff_smul_pauliFamily 1 c a
    rw [one_smul] at h
    rw [if_pos rfl, h]
    by_cases hc : c = a
    · subst hc
      simp
    · rw [if_neg hc, Pi.single_eq_of_ne]
      intro h'
      exact hc (congrArg Prod.fst h')
  · have hq' : q.1 ≠ e.1 := fun h => hq (Subtype.ext h)
    have h := pauliCoeff_smul_pauliFamily 0 c a
    rw [zero_smul] at h
    rw [if_neg hq', h, Pi.single_eq_of_ne]
    · simp
    · intro h'
      exact hq (congrArg Prod.snd h')
theorem finsum_basisForm (a : Fin 3) (e : PositiveEdge L n k 0) (c : PositiveEdge L n k k)
    (hfin : (crossingIncidences L n k c.1).Finite)
    (hpos : ∀ q ∈ crossingIncidences L n k c.1, q.2.IsPositivelyOriented) :
    ∑ᶠ q ∈ crossingIncidences L n k c.1, basisForm a e q.2 =
      (((crossingSites L n k 0 k c.1 e.1).ncard : ℝ) : ℂ) • ComplexMatrix2.pauliFamily a := by
  classical
  set T := hfin.toFinset.filter fun q => q.2 = e.1 with hT
  have himage : crossingSites L n k 0 k c.1 e.1 =
      Prod.fst '' (↑T : Set (Vertex L n k 0 × Edge L n k 0)) := by
    ext x
    constructor
    · rintro ⟨hx, he⟩
      refine ⟨(x, e.1), ?_, rfl⟩
      simp only [hT, Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, and_true]
      exact ⟨hx, he⟩
    · rintro ⟨⟨x', q⟩, hp, rfl⟩
      simp only [hT, Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hp
      obtain ⟨hp₁, hp₂⟩ := hp
      subst hp₂
      exact hp₁
  have hcard : (crossingSites L n k 0 k c.1 e.1).ncard = T.card := by
    rw [himage, Set.InjOn.ncard_image, Set.ncard_coe_finset]
    rintro ⟨x₁, q₁⟩ h₁ ⟨x₂, q₂⟩ h₂ he
    simp only [hT, Finset.coe_filter, Set.mem_ofPred_eq] at h₁ h₂
    have he' : x₁ = x₂ := he
    rw [he', h₁.2, h₂.2]
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin,
    Finset.sum_congr rfl fun q hq => basisForm_of_isPositive a e (hpos q (by simpa using hq)),
    Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, hcard]
  rw [← hT, ← Nat.cast_smul_eq_nsmul ℂ]
  simp
theorem kernel_entry
    (hO : ∀ q : Edge L n k 0, q.opposite.opposite = q ∧
      Xor q.IsPositivelyOriented q.opposite.IsPositivelyOriented)
    (hM : TrivialAverages L n k) (a a' : Fin 3) (c : PositiveEdge L n k k)
    (e : PositiveEdge L n k 0)
    (hfin : (crossingIncidences L n k c.1).Finite)
    (hpos : ∀ q ∈ crossingIncidences L n k c.1, q.2.IsPositivelyOriented) :
    kernel L n k (a', c) (a, e) =
      if a' = a then
        ((finestMesh L k ^ 5 * ((crossingSites L n k 0 k c.1 e.1).ncard : ℝ) : ℝ) : ℂ)
      else 0 := by
  classical
  have h := hM.2.2.1 (basisForm a e) (basisForm_mem hO a e) c
  have hact : ∀ ι', applyKernel (rescaledOperators L n k (trivialField L n k 0)).Q
      (toPauliCoeffs (restrictToPositiveEdges (basisForm a e))) ι' = kernel L n k ι' (a, e) := by
    intro ι'
    show ∑' ι, _ * _ = _
    rw [toPauliCoeffs_basisForm, tsum_eq_single (a, e)]
    · simp [kernel, expConjAtZero]
    · intro ι hι
      rw [Pi.single_eq_of_ne hι, mul_zero]
  have hl : ∑ d, kernel L n k (d, c) (a, e) • ComplexMatrix2.pauliFamily d =
      (finestMesh L k ^ 5) • ∑ᶠ q ∈ crossingIncidences L n k c.1, basisForm a e q.2 := by
    rw [← h]
    show _ = ∑ d, _ • ComplexMatrix2.pauliFamily d
    exact Finset.sum_congr rfl fun d _ => by rw [hact]
  have hc := pauliCoeff_sum_smul (fun d => kernel L n k (d, c) (a, e)) a'
  rw [hl, finsum_basisForm a e c hfin hpos, real_smul_eq_complex_smul, smul_smul,
    pauliCoeff_smul_pauliFamily] at hc
  rw [← hc]
  by_cases haa : a' = a
  · simp [haa]
  · simp [haa]
end BasisEntries
theorem opNorm_le_one_of_schurTest (hSchur : YangMills.Construction.PeriodicOperators.SchurTest.Holds)
    (hMeans : TrivialAveragesOnEverySide)
    (hCounts : CrossingCountsOnTorus)
    (hOrient : YangMills.Construction.PeriodicLattice.OppositeBonds.OppositeAndPositiveRestriction) :
    OpNormLeOne := by
  classical
  intro L hL n k hn hk
  have hL0 : 0 < L := by
    have := hL.2
    omega
  have hM : TrivialAverages L n k := hMeans L hL k hk n hn
  obtain ⟨hrows, hcols, hpaths⟩ := hCounts L hL n k 0 k hn hk (Nat.zero_le k) le_rfl
  have hO : ∀ q : Edge L n k 0, q.opposite.opposite = q ∧
      Xor q.IsPositivelyOriented q.opposite.IsPositivelyOriented := by
    intro q
    have h := (hOrient ⟨L, hL, 1, ⟨n, hn⟩⟩ (YangMills.Construction.PeriodicLattice.levelDepth k 0) (by
      simp [YangMills.Construction.PeriodicLattice.levelDepth]
      omega)).1 q
    exact ⟨h.2.2.1, h.2.2.2.2.2⟩
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL0
  have hη : 0 < finestMesh L k := by
    unfold finestMesh meshAt
    exact zpow_pos hLr _
  have hη4 : 0 < finestMesh L k ^ 4 := pow_pos hη 4
  have htop : meshAt L k k = 1 := by simp [meshAt]
  have hone : (L : ℝ) ^ k * finestMesh L k = 1 := by
    simp [finestMesh, meshAt, zpow_neg, hLr.ne']
  have hfin : ∀ c : PositiveEdge L n k k, (crossingIncidences L n k c.1).Finite := by
    intro c
    apply Set.finite_of_ncard_ne_zero
    intro h0
    have h1 := hM.2.2.2 c
    rw [h0] at h1
    have : (finestMesh L k ^ 5)⁻¹ ≠ 0 := by positivity
    exact this (by simpa using h1.symm)
  have hpos : ∀ c : PositiveEdge L n k k, ∀ q ∈ crossingIncidences L n k c.1,
      q.2.IsPositivelyOriented :=
    fun c q hq => (hpaths c q.1 hq.1).2 q.2 hq.2
  let N : PositiveEdge L n k k → PositiveEdge L n k 0 → ℝ := fun c e =>
    finestMesh L k ^ 5 * ((crossingSites L n k 0 k c.1 e.1).ncard : ℝ)
  have hLpow : ∀ p : ℕ, (L : ℝ) ^ p ≠ 0 := fun p => pow_ne_zero _ hLr.ne'
  have hrow : ∀ c, Summable (N c) ∧ ∑' e, N c e ≤ 1 := by
    intro c
    have hs := hasSum_finsum_of_ne_zero _ (by rw [hrows c]; exact hLpow _)
    rw [hrows c] at hs
    have hs' : HasSum (N c) (finestMesh L k ^ 5 * (L : ℝ) ^ (5 * (k - 0))) := hs.mul_left _
    refine ⟨hs'.summable, ?_⟩
    rw [hs'.tsum_eq]
    have he : finestMesh L k ^ 5 * (L : ℝ) ^ (5 * (k - 0)) =
        ((L : ℝ) ^ k * finestMesh L k) ^ 5 := by
      rw [Nat.sub_zero, mul_pow, ← pow_mul, mul_comm k 5, mul_comm]
    rw [he, hone, one_pow]
  have hcol : ∀ e, Summable (fun c => N c e) ∧ ∑' c, N c e ≤ finestMesh L k ^ 4 := by
    intro e
    have hs := hasSum_finsum_of_ne_zero _ (by rw [hcols e]; exact hLpow _)
    rw [hcols e] at hs
    have hs' : HasSum (fun c => N c e) (finestMesh L k ^ 5 * (L : ℝ) ^ (k - 0)) := hs.mul_left _
    refine ⟨hs'.summable, ?_⟩
    rw [hs'.tsum_eq]
    have he : finestMesh L k ^ 5 * (L : ℝ) ^ (k - 0) =
        finestMesh L k ^ 4 * ((L : ℝ) ^ k * finestMesh L k) := by
      rw [Nat.sub_zero]
      ring
    rw [he, hone, mul_one]
  have hzero : ∀ (a a' : Fin 3) (c : PositiveEdge L n k k) (e : PositiveEdge L n k 0), a' ≠ a →
      kernel L n k (a', c) (a, e) = 0 := by
    intro a a' c e h
    rw [kernel_entry hO hM a a' c e (hfin c) (hpos c), if_neg h]
  have hbound : ∀ (a : Fin 3) (c : PositiveEdge L n k k) (e : PositiveEdge L n k 0),
      ‖kernel L n k (a, c) (a, e)‖ ≤ N c e := by
    intro a c e
    rw [kernel_entry hO hM a a c e (hfin c) (hpos c), if_pos rfl, Complex.norm_real,
      Real.norm_eq_abs]
    exact (abs_of_nonneg (by positivity)).le
  have hnum : meshAt L k k ^ 4 * (1 * finestMesh L k ^ 4) ≤
      (1 : ℝ) ^ 2 * finestMesh L k ^ 4 := by
    rw [htop]
    simp
  have h := (hSchur.2 (PositiveEdge L n k 0) (PositiveEdge L n k k) (kernel L n k) N
    (meshWeight (finestMesh L k)) (meshWeight (meshAt L k k))
    (finestMesh L k ^ 4) (meshAt L k k ^ 4) 1 (finestMesh L k ^ 4) 1
    hη4 (by rw [htop]; norm_num) zero_le_one (fun _ => rfl) (fun _ => rfl)
    hzero hbound hrow hcol hnum).2 Set.univ
  exact h
end RescaledQFiniteSide
end Tower
end YangMills.Construction
end
