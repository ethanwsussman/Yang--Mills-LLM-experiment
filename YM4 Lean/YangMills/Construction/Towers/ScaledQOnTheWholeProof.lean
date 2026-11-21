import YangMills.Construction.Towers.KernelsOfTheScaledOperatorsAtEveryComplexConfigurationProof
import YangMills.Construction.Towers.CountsOfCrossingsOnTheWhole
import YangMills.Construction.Towers.MeansAtTheTrivialConfigurationOfTheScaledPictureOnTheWhole
import YangMills.Construction.Towers.ScaledQOnASideProof
import YangMills.Construction.Towers.ScaledQOnTheWhole
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower
open Matrices
open PeriodicOperators (colourEdges expConj applyKernel bilinDot toComplexVec)
open InfiniteLattice (AmbientSpace)
namespace RescaledQFullSpace
open FullSpace.RescaledConditions (TrivialAverages crossingIncidences)
theorem pauliFamily_mem_traceless (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
theorem pauliCoeff_sum_smul (x : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ b, x b • ComplexMatrix2.pauliFamily b) = x a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
theorem pauliCoeff_smul_pauliFamily (z : ℂ) (a b : Fin 3) :
    pauliCoeff a (z • ComplexMatrix2.pauliFamily b) = if a = b then z else 0 := by apply _root_.YangMills.Construction.Tower.CrossingSmoothingContraction.pauliCoeff_smul_pauliFamily <;> assumption
theorem real_smul_eq_complex_smul (z : ℝ) (X : ComplexMatrix2) : z • X = (z : ℂ) • X := by apply _root_.YangMills.SharedProofs.p9878 <;> assumption
theorem hasSum_finsum_of_ne_zero {ι : Type} (f : ι → ℝ) (h : ∑ᶠ i, f i ≠ 0) :
    HasSum f (∑ᶠ i, f i) := by apply _root_.YangMills.Construction.Tower.RescaledQFiniteSide.hasSum_finsum_of_ne_zero <;> assumption
theorem xor_isPositivelyOriented_opposite {a : ℝ} (ha : 0 < a) (q : InfiniteLattice.Link a) :
    Xor q.IsPositivelyOriented q.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.Unbounded.xor_isPositivelyOriented_opposite <;> assumption
section KernelEntries
variable {L k : ℕ}
def basisForm (a : Fin 3) (b : PeriodicOperators.PosEdge L k 0) :
    FullSpace.Edge L k 0 → ComplexMatrix2 :=
  open Classical in FullSpace.extendOddly fun q =>
    if q = b.1 then ComplexMatrix2.pauliFamily a else 0
theorem basisForm_of_positive (a : Fin 3) (b : PeriodicOperators.PosEdge L k 0)
    {q : FullSpace.Edge L k 0} (hq : q.IsPositivelyOriented) :
    basisForm a b q = open Classical in if q = b.1 then ComplexMatrix2.pauliFamily a else 0 := by
  classical
  simp [basisForm, FullSpace.extendOddly, hq]
theorem basisForm_mem
    (hO : ∀ q : FullSpace.Edge L k 0, Xor q.IsPositivelyOriented q.opposite.IsPositivelyOriented)
    (a : Fin 3) (b : PeriodicOperators.PosEdge L k 0) :
    basisForm a b ∈ FullSpace.complexEdgeForms (meshAt L k 0) := by apply _root_.YangMills.Construction.Tower.RescaledKernels.fullSpace_basisForm_mem <;> assumption
theorem toPauliCoeffs_basisForm (a : Fin 3) (b : PeriodicOperators.PosEdge L k 0) :
    toPauliCoeffs (FullSpace.restrictToPositiveEdges (basisForm a b)) =
      open Classical in Pi.single (a, b) 1 := by
  classical
  funext ι
  obtain ⟨c, q⟩ := ι
  show pauliCoeff c (basisForm a b q.1) = _
  rw [basisForm_of_positive a b q.2]
  by_cases hq : q = b
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
  · have hq' : q.1 ≠ b.1 := fun h => hq (Subtype.ext h)
    have h := pauliCoeff_smul_pauliFamily 0 c a
    rw [zero_smul] at h
    rw [if_neg hq', h, Pi.single_eq_of_ne]
    · simp
    · intro h'
      exact hq (congrArg Prod.snd h')
theorem finsum_basisForm (a : Fin 3) (b : PeriodicOperators.PosEdge L k 0)
    (c : PeriodicOperators.PosEdge L k k) (hfin : (crossingIncidences L k c.1).Finite)
    (hpos : ∀ q ∈ crossingIncidences L k c.1, q.2.IsPositivelyOriented) :
    ∑ᶠ q ∈ crossingIncidences L k c.1, basisForm a b q.2 =
      (((FullSpace.crossingSites L k 0 k c.1 b.1).ncard : ℝ) : ℂ) •
        ComplexMatrix2.pauliFamily a := by
  classical
  set T := hfin.toFinset.filter fun q => q.2 = b.1 with hT
  have himage : FullSpace.crossingSites L k 0 k c.1 b.1 =
      Prod.fst '' (↑T : Set (FullSpace.Vertex L k 0 × FullSpace.Edge L k 0)) := by
    ext x
    constructor
    · rintro ⟨hx, hb⟩
      refine ⟨(x, b.1), ?_, rfl⟩
      simp only [hT, Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, and_true]
      exact ⟨hx, hb⟩
    · rintro ⟨⟨x', q⟩, hp, rfl⟩
      simp only [hT, Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hp
      obtain ⟨hp₁, hp₂⟩ := hp
      subst hp₂
      exact hp₁
  have hcard : (FullSpace.crossingSites L k 0 k c.1 b.1).ncard = T.card := by
    rw [himage, Set.InjOn.ncard_image, Set.ncard_coe_finset]
    rintro ⟨x₁, q₁⟩ h₁ ⟨x₂, q₂⟩ h₂ e
    simp only [hT, Finset.coe_filter, Set.mem_ofPred_eq] at h₁ h₂
    have e' : x₁ = x₂ := e
    rw [e', h₁.2, h₂.2]
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin,
    Finset.sum_congr rfl fun q hq => basisForm_of_positive a b (hpos q (by simpa using hq)),
    Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, hcard]
  rw [← hT, ← Nat.cast_smul_eq_nsmul ℂ]
  simp
theorem Q_entry
    (hO : ∀ q : FullSpace.Edge L k 0, Xor q.IsPositivelyOriented q.opposite.IsPositivelyOriented)
    (hM : TrivialAverages L k) (a a' : Fin 3) (c : PeriodicOperators.PosEdge L k k)
    (b : PeriodicOperators.PosEdge L k 0) (hfin : (crossingIncidences L k c.1).Finite)
    (hpos : ∀ q ∈ crossingIncidences L k c.1, q.2.IsPositivelyOriented) :
    (FullSpace.rescaledOperators L k fun _ => 1).Q (a', c) (a, b) =
      if a' = a then
        ((finestMesh L k ^ 5 * ((FullSpace.crossingSites L k 0 k c.1 b.1).ncard : ℝ) : ℝ) : ℂ)
      else 0 := by
  classical
  have h := hM.2.2.1 (basisForm a b) (basisForm_mem hO a b) c
  have hact : ∀ ι', applyKernel (FullSpace.rescaledOperators L k fun _ => 1).Q
      (toPauliCoeffs (FullSpace.restrictToPositiveEdges (basisForm a b))) ι' =
        (FullSpace.rescaledOperators L k fun _ => 1).Q ι' (a, b) := by
    intro ι'
    show ∑' ι, _ * _ = _
    rw [toPauliCoeffs_basisForm, tsum_eq_single (a, b)]
    · simp
    · intro ι hι
      rw [Pi.single_eq_of_ne hι, mul_zero]
  have hl : ∑ e, (FullSpace.rescaledOperators L k fun _ => 1).Q (e, c) (a, b) •
        ComplexMatrix2.pauliFamily e =
      (finestMesh L k ^ 5) • ∑ᶠ q ∈ crossingIncidences L k c.1, basisForm a b q.2 := by
    rw [← h]
    show _ = ∑ e, _ • ComplexMatrix2.pauliFamily e
    exact Finset.sum_congr rfl fun e _ => by rw [hact]
  have hc := pauliCoeff_sum_smul
    (fun e => (FullSpace.rescaledOperators L k fun _ => 1).Q (e, c) (a, b)) a'
  rw [hl, finsum_basisForm a b c hfin hpos, real_smul_eq_complex_smul, smul_smul,
    pauliCoeff_smul_pauliFamily] at hc
  rw [← hc]
  by_cases haa : a' = a
  · simp [haa]
  · simp [haa]
end KernelEntries
theorem re_bilinDot_le (θ v : AmbientSpace) (hv : ∀ μ, |v μ| ≤ 3 / 2) :
    (bilinDot (toComplexVec θ) (toComplexVec v)).re ≤ 3 / 2 * TorusMetric.l1NormVec θ := by
  have e : (bilinDot (toComplexVec θ) (toComplexVec v)).re = ∑ μ, θ μ * v μ := by
    simp [bilinDot, toComplexVec, Complex.mul_re]
  rw [e]
  unfold TorusMetric.l1NormVec
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun μ _ => ?_
  calc θ μ * v μ ≤ |θ μ * v μ| := le_abs_self _
    _ = |θ μ| * |v μ| := abs_mul _ _
    _ ≤ |θ μ| * (3 / 2) := mul_le_mul_of_nonneg_left (hv μ) (abs_nonneg _)
    _ = 3 / 2 * |θ μ| := by ring
end RescaledQFullSpace
theorem RescaledQFullSpace.opNormLeExp_of_schurTest (hSchur : PeriodicOperators.SchurTest.Holds)
    (hMeans : FullSpace.TrivialFieldMeansCondition)
    (hCounts : FullSpace.CrossingCounts) : RescaledQFullSpace.OpNormLeExp := by
  classical
  intro L hL k hk θ
  have hL0 : 0 < L := by
    have := hL.2
    omega
  have hM := hMeans L hL k hk
  obtain ⟨hrows, hcols, hpaths, hnear⟩ := hCounts L hL k 0 k hk (Nat.zero_le k) le_rfl
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL0
  have hη : 0 < finestMesh L k := by
    unfold finestMesh meshAt
    exact zpow_pos hLr _
  have hmesh : 0 < meshAt L k 0 := hη
  have hO : ∀ q : FullSpace.Edge L k 0,
      Xor q.IsPositivelyOriented q.opposite.IsPositivelyOriented :=
    RescaledQFullSpace.xor_isPositivelyOriented_opposite hmesh
  have hη4 : 0 < finestMesh L k ^ 4 := pow_pos hη 4
  have htop : meshAt L k k = 1 := by simp [meshAt]
  have hone : (L : ℝ) ^ k * finestMesh L k = 1 := by
    simp [finestMesh, meshAt, zpow_neg, hLr.ne']
  have hθ : 0 ≤ TorusMetric.l1NormVec θ := Finset.sum_nonneg fun μ _ => abs_nonneg _
  have hfin : ∀ c : PeriodicOperators.PosEdge L k k,
      (FullSpace.RescaledConditions.crossingIncidences L k c.1).Finite := by
    intro c
    apply Set.finite_of_ncard_ne_zero
    intro h0
    have h1 := hM.2.2.2 c
    rw [h0] at h1
    have : (finestMesh L k ^ 5)⁻¹ ≠ 0 := by positivity
    exact this (by simpa using h1.symm)
  have hpos : ∀ c : PeriodicOperators.PosEdge L k k,
      ∀ q ∈ FullSpace.RescaledConditions.crossingIncidences L k c.1,
        q.2.IsPositivelyOriented :=
    fun c q hq => (hpaths c q.1 hq.1).2 q.2 hq.2
  set E : ℝ := 3 / 2 * TorusMetric.l1NormVec θ with hE
  let N : PeriodicOperators.PosEdge L k k → PeriodicOperators.PosEdge L k 0 → ℝ :=
    fun c b => finestMesh L k ^ 5 * Real.exp E *
      ((FullSpace.crossingSites L k 0 k c.1 b.1).ncard : ℝ)
  have hLpow : ∀ e : ℕ, (L : ℝ) ^ e ≠ 0 := fun e => pow_ne_zero _ hLr.ne'
  have hrow : ∀ c, Summable (N c) ∧ ∑' b, N c b ≤ Real.exp E := by
    intro c
    have hs := RescaledQFullSpace.hasSum_finsum_of_ne_zero _
      (by rw [(hrows c).2]; exact hLpow _)
    rw [(hrows c).2] at hs
    have hs' : HasSum (N c) (finestMesh L k ^ 5 * Real.exp E * (L : ℝ) ^ (5 * (k - 0))) :=
      hs.mul_left _
    refine ⟨hs'.summable, ?_⟩
    rw [hs'.tsum_eq]
    have e : finestMesh L k ^ 5 * Real.exp E * (L : ℝ) ^ (5 * (k - 0)) =
        ((L : ℝ) ^ k * finestMesh L k) ^ 5 * Real.exp E := by
      rw [Nat.sub_zero, mul_pow, ← pow_mul, mul_comm k 5]
      ring
    rw [e, hone, one_pow, one_mul]
  have hcol : ∀ b, Summable (fun c => N c b) ∧
      ∑' c, N c b ≤ finestMesh L k ^ 4 * Real.exp E := by
    intro b
    have hs := RescaledQFullSpace.hasSum_finsum_of_ne_zero _
      (by rw [(hcols b).2]; exact hLpow _)
    rw [(hcols b).2] at hs
    have hs' : HasSum (fun c => N c b)
        (finestMesh L k ^ 5 * Real.exp E * (L : ℝ) ^ (k - 0)) := hs.mul_left _
    refine ⟨hs'.summable, ?_⟩
    rw [hs'.tsum_eq]
    have e : finestMesh L k ^ 5 * Real.exp E * (L : ℝ) ^ (k - 0) =
        finestMesh L k ^ 4 * Real.exp E * ((L : ℝ) ^ k * finestMesh L k) := by
      rw [Nat.sub_zero]
      ring
    rw [e, hone, mul_one]
  have hoff : ∀ (a a' : Fin 3) (c : PeriodicOperators.PosEdge L k k)
      (b : PeriodicOperators.PosEdge L k 0), a' ≠ a →
      RescaledQFullSpace.conjugate L k θ (a', c) (a, b) = 0 := by
    intro a a' c b h
    have := RescaledQFullSpace.Q_entry hO hM a a' c b (hfin c) (hpos c)
    rw [if_neg h] at this
    simp only [RescaledQFullSpace.conjugate, expConj]
    exact mul_eq_zero_of_right _ this
  have hdiag : ∀ (a : Fin 3) (c : PeriodicOperators.PosEdge L k k)
      (b : PeriodicOperators.PosEdge L k 0),
      ‖RescaledQFullSpace.conjugate L k θ (a, c) (a, b)‖ ≤ N c b := by
    intro a c b
    have hent := RescaledQFullSpace.Q_entry hO hM a a c b (hfin c) (hpos c)
    rw [if_pos rfl] at hent
    simp only [RescaledQFullSpace.conjugate, expConj]
    rw [hent]
    show ‖Complex.exp (bilinDot (toComplexVec θ)
      (toComplexVec ((c.1.initial : AmbientSpace) - (b.1.initial : AmbientSpace)))) * _‖ ≤ _
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    by_cases hne : (FullSpace.crossingSites L k 0 k c.1 b.1).Nonempty
    · have hre := RescaledQFullSpace.re_bilinDot_le θ
        ((c.1.initial : AmbientSpace) - (b.1.initial : AmbientSpace))
        (fun μ => by
          have h := hnear c b hne μ
          have h2 : 3 / 2 * meshAt L k k = 3 / 2 := by rw [htop]; norm_num
          have e : ((c.1.initial : AmbientSpace) - (b.1.initial : AmbientSpace)) μ =
              (c.1.initial : AmbientSpace) μ - (b.1.initial : AmbientSpace) μ := rfl
          rw [e, abs_sub_comm]
          linarith)
      have h2 := Real.exp_le_exp.mpr hre
      have h3 : 0 ≤ finestMesh L k ^ 5 *
          ((FullSpace.crossingSites L k 0 k c.1 b.1).ncard : ℝ) := by positivity
      calc _ ≤ Real.exp E * (finestMesh L k ^ 5 *
              ((FullSpace.crossingSites L k 0 k c.1 b.1).ncard : ℝ)) :=
            mul_le_mul_of_nonneg_right h2 h3
        _ = N c b := by simp only [N]; ring
    · have h0 : FullSpace.crossingSites L k 0 k c.1 b.1 = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp hne
      simp [N, h0]
  have hAB : meshAt L k k ^ 4 *
      (Real.exp E * (finestMesh L k ^ 4 * Real.exp E)) ≤
      Real.exp (2 * TorusMetric.l1NormVec θ) ^ 2 * meshAt L k 0 ^ 4 := by
    rw [htop]
    have e1 : Real.exp E * Real.exp E = Real.exp (3 * TorusMetric.l1NormVec θ) := by
      rw [← Real.exp_add, hE]
      congr 1
      ring
    have e2 : Real.exp (2 * TorusMetric.l1NormVec θ) ^ 2 =
        Real.exp (4 * TorusMetric.l1NormVec θ) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    have e3 : finestMesh L k = meshAt L k 0 := rfl
    rw [e2, ← e3]
    calc (1 : ℝ) ^ 4 * (Real.exp E * (finestMesh L k ^ 4 * Real.exp E))
        = Real.exp (3 * TorusMetric.l1NormVec θ) * finestMesh L k ^ 4 := by
          rw [← e1]
          ring
      _ ≤ Real.exp (4 * TorusMetric.l1NormVec θ) * finestMesh L k ^ 4 := by
          refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) hη4.le
          linarith
  have hT := hSchur.2 (PeriodicOperators.PosEdge L k 0)
    (PeriodicOperators.PosEdge L k k) (RescaledQFullSpace.conjugate L k θ) N
    (colourEdges L k 0).weightOf (colourEdges L k k).weightOf
    (meshAt L k 0 ^ 4) (meshAt L k k ^ 4) (Real.exp E)
    (finestMesh L k ^ 4 * Real.exp E) (Real.exp (2 * TorusMetric.l1NormVec θ))
    (pow_pos hmesh 4) (by rw [htop]; norm_num)
    (Real.exp_pos _).le (fun _ => rfl) (fun _ => rfl) hoff hdiag hrow hcol hAB
  exact ⟨fun f hf => hT.1 f hf, (hT.2 _).1, (hT.2 _).2⟩
end YangMills.Construction.Tower
end
