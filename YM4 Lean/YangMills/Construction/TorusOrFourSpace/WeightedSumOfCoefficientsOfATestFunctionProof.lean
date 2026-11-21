import YangMills.Construction.TorusOrFourSpace.CoefficientsOfTestFunctionsOnThePeriodBoxProof
import YangMills.Construction.TorusOrFourSpace.WeightedSumOfCoefficientsOfATestFunction
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.PeriodCell.WeightedSum
theorem natAbs_le_maxAbs {p : ℕ+} (k : IntCoords p) (j : Fin (4 * (p : ℕ))) :
    (k j).natAbs ≤ k.maxAbs :=
  Finset.le_sup (f := fun j => (k j).natAbs) (Finset.mem_univ j)
theorem one_le_maxAbs {p : ℕ+} {k : IntCoords p} (hk : k ≠ 0) : 1 ≤ k.maxAbs := by apply _root_.YangMills.Construction.PeriodicSpace.PeriodCell.Fourier.one_le_maxAbs <;> assumption
theorem intVecNorm_block_le {p : ℕ+} (k : IntCoords p) (i : Fin (p : ℕ)) :
    intVecNorm (k.block i) ≤ 2 * (k.maxAbs : ℝ) := by
  unfold intVecNorm
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  have hsq : ∀ μ : Fin 4, ((k.block i μ : ℤ) : ℝ) ^ 2 ≤ (k.maxAbs : ℝ) ^ 2 := by
    intro μ
    have hcoord : ((k.block i μ).natAbs : ℝ) ≤ k.maxAbs := by
      exact_mod_cast natAbs_le_maxAbs k _
    have habs : |((k.block i μ : ℤ) : ℝ)| = ((k.block i μ).natAbs : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [← sq_abs, habs]
    exact pow_le_pow_left₀ (by positivity) hcoord 2
  calc ∑ μ, ((k.block i μ : ℤ) : ℝ) ^ 2 ≤ ∑ _μ : Fin 4, (k.maxAbs : ℝ) ^ 2 :=
        Finset.sum_le_sum fun μ _ => hsq μ
    _ = (2 * (k.maxAbs : ℝ)) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
theorem freqWeight_pos {n : ℕ+} {ρ : ℝ} (hρ : 0 < ρ) (k : IntCoords n) :
    0 < freqWeight ρ k := by
  have hscale : 0 < cutoffScale ρ := by
    unfold cutoffScale
    have := Real.pi_pos
    positivity
  refine Finset.prod_pos fun i _ => ?_
  have : 0 ≤ intVecNorm (k.block i) := Real.sqrt_nonneg _
  positivity
theorem freqWeight_le_pow {n : ℕ+} {ρ : ℝ} (hρ : 0 < ρ) (k : IntCoords n) :
    freqWeight ρ k ≤ (1 + 2 * (k.maxAbs : ℝ) / cutoffScale ρ) ^ (n : ℕ) := by
  have hscale : 0 < cutoffScale ρ := by
    unfold cutoffScale
    have := Real.pi_pos
    positivity
  unfold freqWeight
  calc ∏ i, (1 + intVecNorm (k.block i) / cutoffScale ρ)
      ≤ ∏ _i : Fin (n : ℕ), (1 + 2 * (k.maxAbs : ℝ) / cutoffScale ρ) := by
        refine Finset.prod_le_prod (fun i _ => ?_) (fun i _ => ?_)
        · have : 0 ≤ intVecNorm (k.block i) := Real.sqrt_nonneg _
          positivity
        · have := div_le_div_of_nonneg_right (intVecNorm_block_le k i) hscale.le
          linarith
    _ = (1 + 2 * (k.maxAbs : ℝ) / cutoffScale ρ) ^ (n : ℕ) := by simp
theorem freqWeight_zero {n : ℕ+} (ρ : ℝ) : freqWeight ρ (0 : IntCoords n) = 1 := by
  simp [freqWeight, intVecNorm, IntCoords.block]
theorem shell_bound {a s : ℝ} (ha : 0 < a) (hs : 1 ≤ s) (n : ℕ) :
    (a / s) ^ (5 * n + 1) * (1 + 2 * s / a) ^ n ≤
      a ^ (4 * n + 1) * (a + 2) ^ n * (s ^ (4 * n + 1))⁻¹ := by
  have hrewrite : (a / s) ^ (5 * n + 1) * (1 + 2 * s / a) ^ n =
      (a / s) ^ (4 * n + 1) * (a / s + 2) ^ n := by
    have hfac : a / s + 2 = (a / s) * (1 + 2 * s / a) := by field_simp
    rw [hfac, mul_pow, ← mul_assoc, ← pow_add]
    congr 2
    ring
  rw [hrewrite, div_pow]
  have hbase : a / s + 2 ≤ a + 2 := by
    have : a / s ≤ a := div_le_self ha.le hs
    linarith
  have hpow : (a / s + 2) ^ n ≤ (a + 2) ^ n := pow_le_pow_left₀ (by positivity) hbase n
  calc a ^ (4 * n + 1) / s ^ (4 * n + 1) * (a / s + 2) ^ n
      ≤ a ^ (4 * n + 1) / s ^ (4 * n + 1) * (a + 2) ^ n :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = a ^ (4 * n + 1) * (a + 2) ^ n * (s ^ (4 * n + 1))⁻¹ := by
        rw [div_eq_mul_inv]
        ring
theorem weightedFourierSum_of_bounds (hcoef : FourierCoeffBounds)
    (hpts : TupleFacts.AllFacts) :
    WeightedFourierSum := by
  intro D n ρ hρ F hF
  have hP : (0 : ℝ) < 4 * ρ := by positivity
  obtain ⟨-, hzero, -, -, -, hdecay, -, -, ⟨hsum, hsumle⟩, -, -⟩ := hcoef D n (4 * ρ) hP
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hfin, -⟩ := hpts D Kind.euclidean n
  have hpi := Real.pi_pos
  obtain ⟨a, haDef⟩ : ∃ a, a = cutoffScale ρ := ⟨_, rfl⟩
  have ha : 0 < a := by
    rw [haDef]
    unfold cutoffScale
    positivity
  obtain ⟨ν, hν⟩ : ∃ ν, ν = 5 * (n : ℕ) + 1 := ⟨_, rfl⟩
  rw [← hν]
  have hN : Kind.Tuple.cNorm D Kind.euclidean ν F ≠ ∞ :=
    (hfin ν F (hF.1 ν) hF.2.1).ne
  obtain ⟨C, hC⟩ : ∃ C, C = (Kind.Tuple.cNorm D Kind.euclidean ν F).toReal :=
    ⟨_, rfl⟩
  have hC0 : 0 ≤ C := hC ▸ ENNReal.toReal_nonneg
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = a ^ (4 * (n : ℕ) + 1) * (a + 2) ^ (n : ℕ) * C := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by
    rw [hA]
    positivity
  have hshell : ∀ q : {q : IntCoords n // q ≠ 0},
      ‖fourierCoeff D (4 * ρ) F q.1‖ * freqWeight ρ q.1 ≤
        A * ((q.1.maxAbs : ℝ) ^ (4 * (n : ℕ) + 1))⁻¹ := by
    intro q
    have hs1 : (1 : ℝ) ≤ (q.1.maxAbs : ℝ) := by exact_mod_cast one_le_maxAbs q.2
    have hs0 : (0 : ℝ) < (q.1.maxAbs : ℝ) := by linarith
    have hdec := hdecay F hF q.1 q.2 ν
    have hne : ENNReal.ofReal ((4 * ρ / (2 * Real.pi * (q.1.maxAbs : ℝ))) ^ ν) *
        Kind.Tuple.cNorm D Kind.euclidean ν F ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hN
    have hreal := (ENNReal.ofReal_le_iff_le_toReal hne).1 hdec
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ← hC] at hreal
    have hratio : 4 * ρ / (2 * Real.pi * (q.1.maxAbs : ℝ)) = a / (q.1.maxAbs : ℝ) := by
      rw [haDef]
      unfold cutoffScale
      field_simp
      ring
    rw [hratio] at hreal
    have hw := freqWeight_le_pow hρ q.1
    rw [← haDef] at hw
    have har := shell_bound ha hs1 (n : ℕ)
    rw [← hν] at har
    calc ‖fourierCoeff D (4 * ρ) F q.1‖ * freqWeight ρ q.1
        ≤ ((a / (q.1.maxAbs : ℝ)) ^ ν * C) *
            (1 + 2 * (q.1.maxAbs : ℝ) / a) ^ (n : ℕ) :=
          mul_le_mul hreal hw (freqWeight_pos hρ q.1).le (by positivity)
      _ = ((a / (q.1.maxAbs : ℝ)) ^ ν * (1 + 2 * (q.1.maxAbs : ℝ) / a) ^ (n : ℕ)) * C := by
          ring
      _ ≤ (a ^ (4 * (n : ℕ) + 1) * (a + 2) ^ (n : ℕ) *
            ((q.1.maxAbs : ℝ) ^ (4 * (n : ℕ) + 1))⁻¹) * C :=
          mul_le_mul_of_nonneg_right har hC0
      _ = A * ((q.1.maxAbs : ℝ) ^ (4 * (n : ℕ) + 1))⁻¹ := by
          rw [hA]
          ring
  have hsub : Summable fun q : {q : IntCoords n // q ≠ 0} =>
      ‖fourierCoeff D (4 * ρ) F q.1‖ * freqWeight ρ q.1 :=
    Summable.of_nonneg_of_le
      (fun q => mul_nonneg (norm_nonneg _) (freqWeight_pos hρ q.1).le) hshell (hsum.mul_left A)
  have hg : Summable fun k : IntCoords n => ‖fourierCoeff D (4 * ρ) F k‖ * freqWeight ρ k :=
    (Set.finite_singleton (0 : IntCoords n)).summable_compl_iff.1 hsub
  refine ⟨hg, ?_⟩
  have hsplit : ∑' k : IntCoords n, ‖fourierCoeff D (4 * ρ) F k‖ * freqWeight ρ k =
      ‖fourierCoeff D (4 * ρ) F 0‖ * freqWeight ρ (0 : IntCoords n) +
        ∑' q : {q : IntCoords n // q ≠ 0},
          ‖fourierCoeff D (4 * ρ) F q.1‖ * freqWeight ρ q.1 := by
    rw [← hg.tsum_subtype_add_tsum_subtype_compl {0}]
    exact congrArg₂ (· + ·) (tsum_singleton (0 : IntCoords n)
      fun k => ‖fourierCoeff D (4 * ρ) F k‖ * freqWeight ρ k) rfl
  have hzeroTerm : ‖fourierCoeff D (4 * ρ) F 0‖ * freqWeight ρ (0 : IntCoords n) ≤ C := by
    rw [freqWeight_zero, mul_one, hC]
    have hmono : Kind.Tuple.cNorm D Kind.euclidean 0 F ≤
        Kind.Tuple.cNorm D Kind.euclidean ν F :=
      biSup_mono fun α hα => hα.trans (Nat.zero_le ν)
    exact (ENNReal.ofReal_le_iff_le_toReal hN).1 ((hzero F hF 0).trans hmono)
  have htail : ∑' q : {q : IntCoords n // q ≠ 0},
      ‖fourierCoeff D (4 * ρ) F q.1‖ * freqWeight ρ q.1 ≤
        A * (4 * (4 * (((n : ℕ)) : ℝ)) * 3 ^ (4 * (n : ℕ) - 1)) := by
    calc _ ≤ ∑' q : {q : IntCoords n // q ≠ 0},
          A * ((q.1.maxAbs : ℝ) ^ (4 * (n : ℕ) + 1))⁻¹ :=
          hsub.tsum_le_tsum hshell (hsum.mul_left A)
      _ = A * ∑' q : {q : IntCoords n // q ≠ 0},
          ((q.1.maxAbs : ℝ) ^ (4 * (n : ℕ) + 1))⁻¹ := tsum_mul_left
      _ ≤ _ := mul_le_mul_of_nonneg_left hsumle hA0
  have hthree : (3 : ℝ) ^ (4 * (n : ℕ)) = 3 * 3 ^ (4 * (n : ℕ) - 1) := by
    rw [← pow_succ']
    congr 1
    have := n.pos
    omega
  have hz : cutoffBound n ρ = 1 + 16 / 3 * (((n : ℕ)) : ℝ) * 3 ^ (4 * (n : ℕ)) *
      a ^ (4 * (n : ℕ) + 1) * (a + 2) ^ (n : ℕ) := by
    rw [haDef]
    rfl
  have hz0 : 0 ≤ cutoffBound n ρ := by
    rw [hz]
    positivity
  have hbound : ∑' k : IntCoords n, ‖fourierCoeff D (4 * ρ) F k‖ * freqWeight ρ k ≤
      cutoffBound n ρ * C := by
    rw [hsplit]
    refine (add_le_add hzeroTerm htail).trans (le_of_eq ?_)
    rw [hz, hA, hthree]
    ring
  calc ENNReal.ofReal (∑' k : IntCoords n, ‖fourierCoeff D (4 * ρ) F k‖ * freqWeight ρ k)
      ≤ ENNReal.ofReal (cutoffBound n ρ * C) := ENNReal.ofReal_le_ofReal hbound
    _ = ENNReal.ofReal (cutoffBound n ρ) *
          Kind.Tuple.cNorm D Kind.euclidean ν F := by
        rw [ENNReal.ofReal_mul hz0, hC, ENNReal.ofReal_toReal hN]
end YangMills.Construction.PeriodicSpace.PeriodCell.WeightedSum
