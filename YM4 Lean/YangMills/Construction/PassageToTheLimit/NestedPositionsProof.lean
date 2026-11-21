import YangMills.Construction.InfiniteLattice.CubicTorusOfACutoffIsAPeriodicExtensionProof
import YangMills.Construction.PassageToTheLimit.NestedPositions
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.LimitSpaces.RefinedCutoffs
variable (s : Conventions.StandingParameters)
theorem one_lt_blockFactor : (1 : ℝ) < (s.L : ℝ) := by apply _root_.YangMills.Construction.InfiniteLattice.CubicTorusAtCutoffLifts.one_lt_L <;> assumption
theorem latticeScale_pos (i : ℕ) : 0 < latticeScale s (i : ℤ) := by
  unfold latticeScale PeriodicLattice.meshSize
  exact zpow_pos (zero_lt_one.trans (one_lt_blockFactor s)) _
theorem latticeScale_eq_pow_mul (i d : ℕ) :
    latticeScale s (i : ℤ) = ((s.L ^ d : ℕ) : ℝ) * latticeScale s ((i + d : ℕ) : ℤ) := by
  have hne : (s.L : ℝ) ≠ 0 := (zero_lt_one.trans (one_lt_blockFactor s)).ne'
  unfold latticeScale PeriodicLattice.meshSize
  push_cast
  rw [neg_add, zpow_add₀ hne]
  simp only [zpow_neg, zpow_natCast]
  field_simp
theorem multiplesOf_latticeScale_mono {i j : ℕ} (hij : i ≤ j) :
    multiplesOf (latticeScale s (i : ℤ)) ⊆ multiplesOf (latticeScale s (j : ℤ)) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  rintro x ⟨n, rfl⟩
  refine ⟨((s.L ^ d : ℕ) : ℤ) * n, ?_⟩
  rw [latticeScale_eq_pow_mul s i d]
  push_cast
  ring
theorem halfShiftedMultiplesOf_latticeScale_mono {i j : ℕ} (hij : i ≤ j) :
    halfShiftedMultiplesOf (latticeScale s (i : ℤ)) ⊆
      halfShiftedMultiplesOf (latticeScale s (j : ℤ)) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  obtain ⟨r, hr⟩ : Odd (s.L ^ d) := s.isAdmissible.1.pow
  rintro x ⟨n, rfl⟩
  refine ⟨((s.L ^ d : ℕ) : ℤ) * n + (r : ℤ), ?_⟩
  rw [latticeScale_eq_pow_mul s i d, hr]
  push_cast
  ring
theorem exists_multiple_near {a : ℝ} (ha : 0 < a) (c : ℝ) :
    ∃ n : ℤ, |c - a * (n : ℝ)| ≤ 1 / 2 * a := by
  refine ⟨⌊c / a + 1 / 2⌋, ?_⟩
  have hlo := mul_le_mul_of_nonneg_left (Int.floor_le (c / a + 1 / 2)) ha.le
  have hhi := mul_le_mul_of_nonneg_left (Int.lt_floor_add_one (c / a + 1 / 2)).le ha.le
  have hc : a * (c / a) = c := by field_simp
  rw [abs_le]
  constructor <;> nlinarith
theorem exists_halfShifted_near {a : ℝ} (ha : 0 < a) (c : ℝ) :
    ∃ n : ℤ, |c - a * ((n : ℝ) + 1 / 2)| ≤ 1 / 2 * a := by
  refine ⟨⌊c / a⌋, ?_⟩
  have hlo := mul_le_mul_of_nonneg_left (Int.floor_le (c / a)) ha.le
  have hhi := mul_le_mul_of_nonneg_left (Int.lt_floor_add_one (c / a)).le ha.le
  have hc : a * (c / a) = c := by field_simp
  rw [abs_le]
  constructor <;> nlinarith
theorem exists_half_latticeScale_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ i : ℕ+, 1 / 2 * latticeScale s ((i : ℕ) : ℤ) < ε := by
  have hL := one_lt_blockFactor s
  have hinv0 : (0 : ℝ) < (s.L : ℝ)⁻¹ := inv_pos.2 (zero_lt_one.trans hL)
  have hinv1 : (s.L : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hL
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hinv1
  refine ⟨Nat.succPNat n, ?_⟩
  have hsc : latticeScale s ((Nat.succPNat n : ℕ) : ℤ) = ((s.L : ℝ)⁻¹) ^ (n + 1) := by
    rw [Nat.succPNat_coe]
    unfold latticeScale PeriodicLattice.meshSize
    rw [zpow_neg, zpow_natCast, inv_pow]
  rw [hsc]
  have hle : ((s.L : ℝ)⁻¹) ^ (n + 1) ≤ ((s.L : ℝ)⁻¹) ^ n :=
    pow_le_pow_of_le_one hinv0.le hinv1.le (Nat.le_succ n)
  have hpos : 0 < ((s.L : ℝ)⁻¹) ^ (n + 1) := pow_pos hinv0 _
  linarith
theorem dense_of_forall_near {S : Set ℝ}
    (hS : ∀ ε : ℝ, 0 < ε → ∀ c : ℝ, ∃ t ∈ S, |c - t| < ε) :
    Dense S := by
  rw [Metric.dense_iff]
  intro x r hr
  obtain ⟨t, ht, hd⟩ := hS r hr x
  refine ⟨t, ?_, ht⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_sub_comm]
  exact hd
theorem claim_holds : Claim := by
  intro s K' hK
  have hK' : (s.K : ℕ) ≤ (K' : ℕ) := (PNat.coe_le_coe _ _).2 hK
  have vertexMono : ∀ i j : ℕ+, i ≤ j → vertexCoords s i ⊆ vertexCoords s j := by
    intro i j hij
    unfold vertexCoords
    exact multiplesOf_latticeScale_mono s ((PNat.coe_le_coe _ _).2 hij)
  have edgeMono : ∀ i j : ℕ+, i ≤ j → edgeMidCoords s i ⊆ edgeMidCoords s j := by
    intro i j hij
    unfold edgeMidCoords
    exact halfShiftedMultiplesOf_latticeScale_mono s ((PNat.coe_le_coe _ _).2 hij)
  refine ⟨multiplesOf_latticeScale_mono s hK', halfShiftedMultiplesOf_latticeScale_mono s hK',
    vertexMono _ _ hK, edgeMono _ _ hK, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro E i j hij P ⟨μ, c, hc, rfl⟩
    exact ⟨μ, c, vertexMono _ _ hij hc, rfl⟩
  · rintro E i j hij P ⟨μ, c, hc, rfl⟩
    exact ⟨μ, c, edgeMono _ _ hij hc, rfl⟩
  · intro i
    exact ⟨0, by simp⟩
  · intro c
    have ha := latticeScale_pos s (s.K : ℕ)
    constructor
    · obtain ⟨n, hn⟩ := exists_multiple_near ha c
      exact iInf₂_le_of_le _ ⟨n, rfl⟩ (ENNReal.ofReal_le_ofReal hn)
    · obtain ⟨n, hn⟩ := exists_halfShifted_near ha c
      exact iInf₂_le_of_le _ ⟨n, rfl⟩ (ENNReal.ofReal_le_ofReal hn)
  · refine dense_of_forall_near fun ε hε c => ?_
    obtain ⟨i, hi⟩ := exists_half_latticeScale_lt s hε
    obtain ⟨n, hn⟩ := exists_multiple_near (latticeScale_pos s (i : ℕ)) c
    exact ⟨_, Set.mem_iUnion.2 ⟨i, n, rfl⟩, hn.trans_lt hi⟩
  · refine dense_of_forall_near fun ε hε c => ?_
    obtain ⟨i, hi⟩ := exists_half_latticeScale_lt s hε
    obtain ⟨n, hn⟩ := exists_halfShifted_near (latticeScale_pos s (i : ℕ)) c
    exact ⟨_, Set.mem_iUnion.2 ⟨i, n, rfl⟩, hn.trans_lt hi⟩
end YangMills.Construction.LimitSpaces.RefinedCutoffs
