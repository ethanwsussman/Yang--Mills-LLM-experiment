import YangMills.Construction.DirichletOperator.DifferenceOperatorsAgreeOnTheLocalTorusProof
import YangMills.Construction.DirichletOperator.DistanceToTheComplementAndTheCuts
import YangMills.Construction.DirichletOperator.SquaresOfTheBumpsOfALevelSumToOne
import YangMills.Construction.DirichletOperator.SquaresOfThePartitionSumToOne
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PartitionCubes.PartitionSquares
variable {𝒮 : RegionSequence.NestedRegions} {M : ℕ}
theorem topLevel_le_s (hne : (𝒮.Ω 0).Nonempty) : topLevel 𝒮 ≤ 𝒮.s := by
  refine csSup_le ⟨0, hne⟩ fun n hn => ?_
  by_contra hlt
  exact (nonempty_iff_ne_empty.mp hn) (𝒮.Ω_eq_empty n (not_le.mp hlt))
theorem Ω_topLevel_succ : 𝒮.Ω (topLevel 𝒮 + 1) = ∅ := by
  by_contra hne
  have hbdd : BddAbove {n | (𝒮.Ω n).Nonempty} := ⟨𝒮.s, fun n hn => by
    by_contra hlt
    exact (nonempty_iff_ne_empty.mp hn) (𝒮.Ω_eq_empty n (not_le.mp hlt))⟩
  have hle : topLevel 𝒮 + 1 ≤ topLevel 𝒮 :=
    le_csSup hbdd (show (𝒮.Ω (topLevel 𝒮 + 1)).Nonempty from nonempty_iff_ne_empty.mpr hne)
  omega
theorem supNorm_zero_le {S : ℝ} : Torus.supNorm (0 : Torus.PeriodicTorus 4 S) ≤ 0 := by apply _root_.YangMills.Construction.PartitionCubes.LocalTorusOperators.supNorm_zero_le <;> assumption
theorem distToOutside_eq_zero {n : ℕ} {x : 𝒮.Point} (hx : x ∈ closure (𝒮.Ω n)ᶜ) :
    distToOutside 𝒮 n x = 0 := by
  refine le_antisymm ?_ bot_le
  refine iInf₂_le_of_le x (mem_singleton x) (iInf₂_le_of_le x hx ?_)
  rw [sub_self]
  exact (ENNReal.ofReal_eq_zero.mpr supNorm_zero_le).le
theorem mollifyRadius_pos (hM : 0 < M) (n : ℕ) : 0 < mollifyRadius 𝒮 M n := by
  have hL : (0 : ℝ) < 𝒮.L := by
    have h13 := 𝒮.thirteen_le_L
    exact_mod_cast (by omega : 0 < 𝒮.L)
  have hside : 0 < cubeSide 𝒮 M n := by
    unfold cubeSide RegionSequence.NestedRegions.scale Torus.scaleSpacing
    exact mul_pos (by exact_mod_cast hM) (mul_pos (zpow_pos hL _) 𝒮.ξ_pos)
  unfold mollifyRadius
  positivity
theorem sinCutoff_zero (x : 𝒮.Point) : sinCutoff 𝒮 M 0 x = 1 := by
  simp [sinCutoff]
theorem sinCutoff_topLevel_succ (hcut : OutsideDistanceAndCutoffs.Claim)
    {K m R₁ : ℕ} (hchain : 𝒮.IsLevelUnitChain K m M R₁) (hM : 0 < M) (x : 𝒮.Point) :
    sinCutoff 𝒮 M (topLevel 𝒮 + 1) x = 0 := by
  have hle := topLevel_le_s hchain.separated.zero_nonempty
  obtain ⟨-, hzero, -⟩ := hcut 𝒮 K m M R₁ hchain (topLevel 𝒮 + 1) (by omega) (by omega)
  have hx : x ∈ closure (𝒮.Ω (topLevel 𝒮 + 1))ᶜ := by
    rw [Ω_topLevel_succ]
    simp
  have hval := hzero x (by
    rw [distToOutside_eq_zero hx]
    exact ENNReal.ofReal_pos.mpr (mollifyRadius_pos hM _))
  simp [sinCutoff, hval]
theorem sinCutoff_sq_mul_succ (hcut : OutsideDistanceAndCutoffs.Claim)
    (hsep : DistanceSeparation.Statement)
    {K m R₁ : ℕ} (hchain : 𝒮.IsLevelUnitChain K m M R₁) (hM : 𝒮.L ^ 5 ≤ M) (hM₀ : 0 < M)
    {n : ℕ} (hn : n ≤ 𝒮.s) (x : 𝒮.Point) :
    sinCutoff 𝒮 M n x ^ 2 * sinCutoff 𝒮 M (n + 1) x ^ 2 = sinCutoff 𝒮 M (n + 1) x ^ 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · rw [sinCutoff_zero]
    ring
  by_cases hzero : sinCutoff 𝒮 M (n + 1) x = 0
  · simp [hzero]
  have hx : x ∈ tsupport (sinCutoff 𝒮 M (n + 1)) :=
    subset_tsupport _ (Function.mem_support.mpr hzero)
  obtain ⟨-, -, -, -, hsupp, -, -⟩ := hcut 𝒮 K m M R₁ hchain (n + 1) (by omega) (by omega)
  have hdist : ENNReal.ofReal (mollifyRadius 𝒮 M (n + 1)) ≤ distToOutside 𝒮 (n + 1) x :=
    hsupp hx
  have hxΩ : x ∈ 𝒮.Ω (n + 1) := by
    by_contra hnot
    rw [distToOutside_eq_zero (subset_closure hnot)] at hdist
    exact absurd hdist (not_le.mpr (ENNReal.ofReal_pos.mpr (mollifyRadius_pos hM₀ _)))
  have hlt : n < 𝒮.s := by
    by_contra hge
    rw [𝒮.Ω_eq_empty (n + 1) (by omega)] at hxΩ
    exact hxΩ
  have hs := hsep K m M R₁ 𝒮 hchain hM
  have htwo : ENNReal.ofReal (2 * mollifyRadius 𝒮 M n) ≤ distToOutside 𝒮 n x := by
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hs.lt_distToOutside n hlt x hxΩ).le
    have hr := hs.mollifyRadius_le n
    have hr₀ := mollifyRadius_pos (𝒮 := 𝒮) hM₀ n
    have hside : 0 ≤ cubeSide 𝒮 M n := by linarith
    have hR : (1 : ℝ) ≤ R₁ := by
      have hgap := hs.L_le_gap
      have h13 := hs.thirteen_le_L
      exact_mod_cast (by omega : 1 ≤ R₁)
    nlinarith
  obtain ⟨-, -, -, -, -, hone, -⟩ := hcut 𝒮 K m M R₁ hchain n hpos (by omega)
  rw [(hone x htwo).1]
  ring
theorem sum_sinCutoff_sq_mul_cosCutoff_sq (hcut : OutsideDistanceAndCutoffs.Claim)
    (hsep : DistanceSeparation.Statement)
    {K m R₁ : ℕ} (hchain : 𝒮.IsLevelUnitChain K m M R₁) (hM : 𝒮.L ^ 5 ≤ M) (hM₀ : 0 < M)
    (x : 𝒮.Point) :
    ∑ n ∈ Finset.range (topLevel 𝒮 + 1),
      sinCutoff 𝒮 M n x ^ 2 * cosCutoff 𝒮 M (n + 1) x ^ 2 = 1 := by
  have hle := topLevel_le_s hchain.separated.zero_nonempty
  have hterm : ∀ n ∈ Finset.range (topLevel 𝒮 + 1),
      sinCutoff 𝒮 M n x ^ 2 * cosCutoff 𝒮 M (n + 1) x ^ 2 =
        sinCutoff 𝒮 M n x ^ 2 - sinCutoff 𝒮 M (n + 1) x ^ 2 := by
    intro n hn
    have hn' : n ≤ topLevel 𝒮 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    obtain ⟨-, -, -, hsq, -⟩ := hcut 𝒮 K m M R₁ hchain (n + 1) (by omega) (by omega)
    have hcos : cosCutoff 𝒮 M (n + 1) x ^ 2 = 1 - sinCutoff 𝒮 M (n + 1) x ^ 2 := by
      linarith [hsq x]
    rw [hcos, mul_sub, mul_one, sinCutoff_sq_mul_succ hcut hsep hchain hM hM₀ (by omega) x]
  rw [Finset.sum_congr rfl hterm,
    Finset.sum_range_sub' (fun n => sinCutoff 𝒮 M n x ^ 2) (topLevel 𝒮 + 1),
    sinCutoff_zero, sinCutoff_topLevel_succ hcut hchain hM₀ x]
  norm_num
theorem finite_productBump_sq_support (hbump : LevelBumpSquares.Statement)
    {K m R₁ : ℕ} (hchain : 𝒮.IsLevelUnitChain K m M R₁) {n : ℕ} (hn : n ≤ topLevel 𝒮)
    (x : 𝒮.Point) :
    ({Q : LevelCube 𝒮 M | Q.level = n} ∩
      Function.support fun Q : LevelCube 𝒮 M => Q.productBump x ^ 2).Finite := by
  by_contra hinf
  have hsum := hbump 𝒮 K m M R₁ hchain n hn x
  rw [finsum_mem_eq_zero_of_infinite hinf] at hsum
  norm_num at hsum
theorem finsum_level_partitionFn_sq (hbump : LevelBumpSquares.Statement)
    {K m R₁ : ℕ} (hchain : 𝒮.IsLevelUnitChain K m M R₁) {n : ℕ} (hn : n ≤ topLevel 𝒮)
    (x : 𝒮.Point) :
    ∑ᶠ Q ∈ {Q : LevelCube 𝒮 M | Q.level = n}, Q.partitionFn x ^ 2 =
      sinCutoff 𝒮 M n x ^ 2 * cosCutoff 𝒮 M (n + 1) x ^ 2 := by
  have hfac : ∀ Q ∈ {Q : LevelCube 𝒮 M | Q.level = n}, Q.partitionFn x ^ 2 =
      sinCutoff 𝒮 M n x ^ 2 * cosCutoff 𝒮 M (n + 1) x ^ 2 * Q.productBump x ^ 2 := by
    intro Q hQ
    have hQ' : Q.level = n := hQ
    unfold LevelCube.partitionFn
    rw [hQ']
    ring
  rw [finsum_mem_congr rfl hfac, ← mul_finsum_mem,
    hbump 𝒮 K m M R₁ hchain n hn x, mul_one]
theorem finite_partitionFn_sq_support (hbump : LevelBumpSquares.Statement)
    {K m R₁ : ℕ} (hchain : 𝒮.IsLevelUnitChain K m M R₁) {n : ℕ} (hn : n ≤ topLevel 𝒮)
    (x : 𝒮.Point) :
    ({Q : LevelCube 𝒮 M | Q.level = n} ∩
      Function.support fun Q : LevelCube 𝒮 M => Q.partitionFn x ^ 2).Finite := by
  refine (finite_productBump_sq_support hbump hchain hn x).subset ?_
  rintro Q ⟨hQ, hne⟩
  refine ⟨hQ, fun hzero => hne ?_⟩
  have hb : Q.productBump x = 0 := by simpa using hzero
  simp [LevelCube.partitionFn, hb]
theorem finsum_active_eq_sum_levels (hbump : LevelBumpSquares.Statement)
    {K m R₁ : ℕ} (hchain : 𝒮.IsLevelUnitChain K m M R₁) (x : 𝒮.Point)
    (hx : ∀ Q : LevelCube 𝒮 M, Q.partitionFn x ≠ 0 → Q ∈ active 𝒮 M) :
    ∑ᶠ Q ∈ active 𝒮 M, Q.partitionFn x ^ 2 =
      ∑ n ∈ Finset.range (topLevel 𝒮 + 1),
        ∑ᶠ Q ∈ {Q : LevelCube 𝒮 M | Q.level = n}, Q.partitionFn x ^ 2 := by
  set f : LevelCube 𝒮 M → ℝ := fun Q => Q.partitionFn x ^ 2 with hf
  have hset : active 𝒮 M ∩ Function.support f =
      ⋃ n ∈ ((Finset.range (topLevel 𝒮 + 1) : Finset ℕ) : Set ℕ),
        ({Q : LevelCube 𝒮 M | Q.level = n} ∩ Function.support f) := by
    ext Q
    simp only [mem_inter_iff, mem_iUnion, Finset.coe_range, mem_Iio, mem_ofPred_eq, exists_prop]
    constructor
    · rintro ⟨-, hQ⟩
      exact ⟨Q.level, Nat.lt_succ_iff.mpr Q.level_le, rfl, hQ⟩
    · rintro ⟨n, -, -, hQ⟩
      refine ⟨hx Q fun hzero => ?_, hQ⟩
      exact hQ (by simp [hf, hzero])
  rw [← finsum_mem_inter_support, hset, finsum_mem_biUnion, finsum_mem_coe_finset]
  · refine Finset.sum_congr rfl fun n _ => ?_
    exact finsum_mem_inter_support f _
  · intro i _ j _ hij
    refine Set.disjoint_left.mpr fun Q hi hj => hij ?_
    exact hi.1.symm.trans hj.1
  · exact Finset.finite_toSet _
  · intro n hn
    have hn' : n ≤ topLevel 𝒮 :=
      Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_coe.mp hn))
    exact finite_partitionFn_sq_support hbump hchain hn' x
theorem statement_holds (hbump : LevelBumpSquares.Statement)
    (hcut : OutsideDistanceAndCutoffs.Claim)
    (hsep : DistanceSeparation.Statement) : Statement := by
  intro K m M R₁ 𝒮 hchain hM
  have hL : 0 < 𝒮.L := by
    have h13 := 𝒮.thirteen_le_L
    omega
  have hM₀ : 0 < M := lt_of_lt_of_le (pow_pos hL 5) hM
  have hall : ∀ x : 𝒮.Point, ∑ n ∈ Finset.range (topLevel 𝒮 + 1),
      ∑ᶠ Q ∈ {Q : LevelCube 𝒮 M | Q.level = n}, Q.partitionFn x ^ 2 = 1 := by
    intro x
    rw [← sum_sinCutoff_sq_mul_cosCutoff_sq hcut hsep hchain hM hM₀ x]
    refine Finset.sum_congr rfl fun n hn => ?_
    exact finsum_level_partitionFn_sq hbump hchain (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)) x
  refine ⟨hall, fun b hb => ?_⟩
  rw [finsum_active_eq_sum_levels hbump hchain (b.source : 𝒮.Point)
    fun Q hQ => ⟨Q.level, Q.level_le, rfl, b, hb, hQ⟩]
  exact hall _
end YangMills.Construction.PartitionCubes.PartitionSquares
