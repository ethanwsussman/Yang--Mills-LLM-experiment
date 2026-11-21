import YangMills.Construction.InfiniteLattice.ChessboardEstimateAndRulesOnMirrorGrids
import YangMills.Construction.InfiniteLattice.FunctionOfOneCellBetweenTwoHalfSpaces
import YangMills.Construction.InfiniteLattice.MomentsOfTheColumnOverACell
import YangMills.Construction.InfiniteLattice.ReflectionFormAndTransferOperatorOfAPeriodicGibbsState
import YangMills.Construction.InfiniteLattice.TallColumnOverACellIsBoundedCrudely
import YangMills.Construction.Sequences.LogConvexSequenceBounds
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
noncomputable section
namespace YangMills.Construction
open InfiniteLattice (upperAlgebra observableSupNorm reflectionPairingRoot)
namespace MultipleReflections
theorem le_of_pow_mul_le_const_mul_pow {a b C : ℝ} (hb : 0 ≤ b) {N : ℕ} (hN : 1 ≤ N)
    (h : ∀ n : ℕ, 1 ≤ n → a ^ (N * n) ≤ C * b ^ (N * n)) (ha : 0 ≤ a) : a ≤ b := by
  by_contra hlt
  rw [not_le] at hlt
  have ha0 : 0 < a := hb.trans_lt hlt
  have hr : b / a < 1 := (div_lt_one ha0).2 hlt
  have hr0 : 0 ≤ b / a := div_nonneg hb ha
  have ht : Tendsto (fun n : ℕ => C * (b / a) ^ n) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr).const_mul C
  obtain ⟨m, hm⟩ := eventually_atTop.1 (ht.eventually (eventually_lt_nhds zero_lt_one))
  have hn : 1 ≤ max m 1 := le_max_right _ _
  have hnm : m ≤ N * max m 1 :=
    (le_max_left m 1).trans (Nat.le_mul_of_pos_left _ hN)
  have h1 := hm _ hnm
  have h2 := h _ hn
  rw [div_pow, ← mul_div_assoc, div_lt_one (pow_pos ha0 _)] at h1
  exact absurd h2 (not_le.2 h1)
theorem limsup_mem_Icc_of_bounds {u : ℕ+ → ℝ} {C : ℝ} (h : ∀ i, 0 ≤ u i ∧ u i ≤ C) :
    0 ≤ limsup u atTop ∧ limsup u atTop ≤ C := by
  have hb : IsBoundedUnder (· ≤ ·) atTop u := isBoundedUnder_of ⟨C, fun i => (h i).2⟩
  refine ⟨le_limsup_of_frequently_le (Frequently.of_forall fun i => (h i).1) hb, ?_⟩
  have hb' : IsBoundedUnder (· ≥ ·) atTop u := isBoundedUnder_of ⟨0, fun i => (h i).1⟩
  exact limsup_le_of_le hb'.isCoboundedUnder_le (Eventually.of_forall fun i => (h i).2)
theorem cellObservableBetweenHalfSpaces_holds
    (hReflect : InfiniteLattice.PeriodicGibbsReflectionTransfer)
    (hBoard : ChessboardBoundAndRules)
    (hLogConvex : LogConvexSequence.RatioAndPowerBounds)
    (hCorr : StackCorrelationsLogConvex)
    (hTall : TallStackOverTileBoundedCrudely) :
    CellObservableBetweenHalfSpaces := by
  intro D μ hμ G k
  obtain ⟨-, hPos, -, -⟩ := hReflect D μ hμ (G.wallTimeHalf k 0)
  have hL1 : (1 : ℝ) < D.L := D.one_lt_L
  have hrules : ∀ (ℓ : ℕ+ → PeriodicLattice.torusSides D.L), G.IsStackSideSequence ℓ → ∀ j,
      Setup.Grid.ChessboardNormRules (D := D.atSide (ℓ j) (ℓ j).2) G := by
    intro ℓ hℓ j
    have hside : 2 * G.edge ≤ (D.atSide (ℓ j) (ℓ j).2).side := by
      rw [Setup.side_atSide]
      exact hℓ.2 j
    exact (hBoard (D.atSide (ℓ j) (ℓ j).2) G hside).2.2.2.2.2.2.1
  have hvalue : ∀ (ℓ : ℕ+ → PeriodicLattice.torusSides D.L), G.IsStackSideSequence ℓ →
      ∀ F ∈ G.tileAlgebra k, ∀ j,
        0 ≤ G.chessboardNormAt (ℓ j) (ℓ j).2 k F ∧
          G.chessboardNormAt (ℓ j) (ℓ j).2 k F ≤ observableSupNorm F := by
    intro ℓ hℓ F hF j
    refine ⟨Real.rpow_nonneg (norm_nonneg _) _, ?_⟩
    exact (hrules ℓ hℓ j k k F 1 hF).2.2.1
  have hq : ∀ (ℓ : ℕ+ → PeriodicLattice.torusSides D.L), G.IsStackSideSequence ℓ →
      ∀ F ∈ G.tileAlgebra k,
        0 ≤ G.limsupStackNorm k ℓ F ∧ G.limsupStackNorm k ℓ F ≤ observableSupNorm F :=
    fun ℓ hℓ F hF => limsup_mem_Icc_of_bounds (hvalue ℓ hℓ F hF)
  have hfirst : ∀ F ∈ G.tileAlgebra k, ∀ (ℓ : ℕ+ → PeriodicLattice.torusSides D.L),
      G.IsStackSideSequence ℓ → ∀ X ∈ upperAlgebra (G.wallTimeHalf k 0),
        (G.stackCorrelation k μ F X 1).re ≤
          G.limsupStackNorm k ℓ F ^ 2 * reflectionPairingRoot μ (G.wallTimeHalf k 0) X ^ 2 := by
    intro F hF ℓ hℓ X hX
    obtain ⟨hnn, h0, hcv⟩ := (hCorr D μ hμ G k F hF).1 X hX
    obtain ⟨k₀, hk₀⟩ := hTall D μ hμ G k F hF X hX ℓ hℓ
    have hlog := (hLogConvex (fun n => (G.stackCorrelation k μ F X n).re) (fun n => (hnn n).2) hcv).2
    have hq0 := (hq ℓ hℓ F hF).1
    set q := G.limsupStackNorm k ℓ F with hqdef
    set S := observableSupNorm X with hS
    set N := D.L ^ k₀ with hNdef
    have hN : 1 ≤ N := Nat.one_le_pow _ _ (by have := D.isAdmissible.2; omega)
    have hx0 : (G.stackCorrelation k μ F X 0).re = reflectionPairingRoot μ (G.wallTimeHalf k 0) X ^ 2 := by
      rw [h0, Complex.ofReal_re]
    have hcrude : ∀ n : ℕ, 1 ≤ n →
        (G.stackCorrelation k μ F X (N * n)).re ≤ S ^ 2 * q ^ (2 * (N * n)) :=
      fun n hn => (Complex.re_le_norm _).trans (hk₀ n hn)
    have hx1 := (hnn 1).2
    rw [← hx0]
    rcases (hnn 0).2.eq_or_lt with hz | hz
    · have hn2 : 1 ≤ N * 2 := by omega
      have h := hlog (N * 2) hn2
      have hpow : (G.stackCorrelation k μ F X 0).re ^ (N * 2 - 1) = 0 := by
        rw [← hz]
        exact zero_pow (by omega)
      simp only [hpow, zero_mul] at h
      have hz1 : (G.stackCorrelation k μ F X 1).re = 0 :=
        pow_eq_zero_iff (by omega) |>.1 (le_antisymm h (pow_nonneg hx1 _))
      rw [hz1, ← hz]
      simp
    · have hb : 0 ≤ (G.stackCorrelation k μ F X 0).re * q ^ 2 := by positivity
      have key := le_of_pow_mul_le_const_mul_pow (C := S ^ 2 / (G.stackCorrelation k μ F X 0).re)
        hb hN (fun n hn => ?_) hx1
      · linarith
      · have hpos : 1 ≤ N * n := Nat.mul_pos hN hn
        obtain ⟨p, hp⟩ : ∃ p, N * n = p + 1 := ⟨N * n - 1, by omega⟩
        have h1 := hlog (N * n) hpos
        have h2 := hcrude n hn
        have h3 : (G.stackCorrelation k μ F X 0).re ^ (N * n - 1) *
            (G.stackCorrelation k μ F X (N * n)).re ≤
            (G.stackCorrelation k μ F X 0).re ^ (N * n - 1) * (S ^ 2 * q ^ (2 * (N * n))) :=
          mul_le_mul_of_nonneg_left h2 (pow_nonneg hz.le _)
        refine (h1.trans h3).trans (le_of_eq ?_)
        rw [hp, Nat.add_sub_cancel, mul_pow, ← pow_mul, pow_succ (G.stackCorrelation k μ F X 0).re]
        field_simp
  have hmain : ∀ F ∈ G.tileAlgebra k, ∀ A ∈ upperAlgebra (G.wallTimeHalf k 0),
      ∀ B ∈ upperAlgebra (G.wallTimeHalf k 0), ∀ ℓ : ℕ+ → PeriodicLattice.torusSides D.L,
        G.IsStackSideSequence ℓ →
        ‖∫ U, G.stackReflect k 0 B U * F U * (G.stackShift 1).actOn A U ∂μ‖ ≤
          G.limsupStackNorm k ℓ F * reflectionPairingRoot μ (G.wallTimeHalf k 0) B *
            reflectionPairingRoot μ (G.wallTimeHalf k 0) A := by
    intro F hF A hA B hB ℓ hℓ
    have h1 := (hCorr D μ hμ G k F hF).2 A hA B hB
    have h2 := hfirst F hF ℓ hℓ B hB
    have h3 := mul_le_mul_of_nonneg_right h2
      (sq_nonneg (reflectionPairingRoot μ (G.wallTimeHalf k 0) A))
    have hnB : 0 ≤ reflectionPairingRoot μ (G.wallTimeHalf k 0) B := Real.sqrt_nonneg _
    have hnA : 0 ≤ reflectionPairingRoot μ (G.wallTimeHalf k 0) A := Real.sqrt_nonneg _
    have hq0 := (hq ℓ hℓ F hF).1
    refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 (h1.trans (h3.trans (le_of_eq ?_)))
    ring
  refine ⟨fun A hA => hPos.2.2.2 A hA, fun F hF A hA B hB ℓ hℓ => hmain F hF A hA B hB ℓ hℓ,
    fun A hA B hB => ?_, fun F hF ℓ hℓ => (hq ℓ hℓ F hF).2⟩
  have hmem : ∀ j : ℕ+,
      PeriodicLattice.torusSide D.L ((j : ℕ) + G.edgeExp.natAbs) ∈ PeriodicLattice.torusSides D.L :=
    fun j => ⟨_, by have := j.pos; omega, rfl⟩
  set ℓ : ℕ+ → PeriodicLattice.torusSides D.L := fun j => ⟨_, hmem j⟩ with hℓdef
  have hpowle : ∀ {p r : ℕ}, p ≤ r → (D.L : ℝ) ^ p ≤ (D.L : ℝ) ^ r :=
    fun h => pow_le_pow_right₀ hL1.le h
  have hseq : G.IsStackSideSequence ℓ := by
    refine ⟨⟨fun j => ?_, ?_⟩, fun j => ?_⟩
    · change 2 * (D.L : ℝ) ^ _ ≤ 2 * (D.L : ℝ) ^ _
      have : ((j : ℕ) + G.edgeExp.natAbs) ≤ ((j + 1 : ℕ+) : ℕ) + G.edgeExp.natAbs := by
        simp
      linarith [hpowle this]
    · have h1 : Tendsto (fun j : ℕ+ => (j : ℕ) + G.edgeExp.natAbs) atTop atTop :=
        tendsto_atTop_mono (fun j => Nat.le_add_right _ _) tendsto_PNat_val_atTop_atTop
      exact ((tendsto_pow_atTop_atTop_of_one_lt hL1).comp h1).const_mul_atTop (by norm_num)
    · change 2 * G.edge ≤ 2 * (D.L : ℝ) ^ _
      have he : G.edgeExp ≤ (((j : ℕ) + G.edgeExp.natAbs : ℕ) : ℤ) := by
        have := j.pos
        omega
      have h2 := zpow_le_zpow_right₀ hL1.le he
      rw [zpow_natCast, ← G.edge_eq_zpow_edgeExp] at h2
      linarith
  have hone : G.limsupStackNorm k ℓ (fun _ => 1) = 1 := by
    have : (fun j => G.chessboardNormAt (ℓ j) (ℓ j).2 k (fun _ => 1)) = fun _ => (1 : ℝ) := by
      funext j
      exact (hrules ℓ hseq j k k 1 1 (one_mem _)).2.1
    unfold Setup.Grid.limsupStackNorm
    rw [this, limsup_const]
  have h : ‖∫ U, G.stackReflect k 0 B U * (fun _ : D.GaugeField => (1 : ℂ)) U *
      (G.stackShift 1).actOn A U ∂μ‖ ≤
      G.limsupStackNorm k ℓ (fun _ => 1) * reflectionPairingRoot μ (G.wallTimeHalf k 0) B *
        reflectionPairingRoot μ (G.wallTimeHalf k 0) A :=
    hmain (fun _ => 1) (one_mem (G.tileAlgebra k)) A hA B hB ℓ hseq
  rw [hone] at h
  simpa using h
end MultipleReflections
end YangMills.Construction
end
