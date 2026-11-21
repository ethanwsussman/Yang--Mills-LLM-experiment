import YangMills.Construction.ConfigurationSpace.MinSeparationProof
import YangMills.Construction.Continuum.LeastSupDistanceOfPointsOfPowersOfFourSpace
import YangMills.Construction.Lattice.IsometriesOfALevelAndTheirCubesProof
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.MinSeparation
open ConfigSpace
theorem iSup_abs_apply_eq_norm (w : Fin 4 → ℝ) : (⨆ c, |w c|) = ‖w‖ := by apply _root_.YangMills.Construction.ConfigurationSpace.MinSep.maxNorm_eq_norm <;> assumption
theorem supNormVec_eq_norm (w : Fin 4 → ℝ) : PeriodicLattice.supNormVec w = ‖w‖ := by apply _root_.YangMills.Construction.PeriodicLattice.LevelIsometryProof.supNormVec_eq_norm <;> assumption
theorem coordSupNorm_eq_iSup_norm {n : ℕ} (y : Config n) : coordSupNorm y = ⨆ i, ‖y i‖ := by
  simp only [coordSupNorm, iSup_abs_apply_eq_norm]
theorem norm_apply_le_coordSupNorm {n : ℕ} (y : Config n) (i : Fin n) :
    ‖y i‖ ≤ coordSupNorm y := by
  rw [coordSupNorm_eq_iSup_norm]
  exact le_ciSup (f := fun i => ‖y i‖) (Set.finite_range _).bddAbove i
theorem coordSupNorm_le_norm {n : ℕ} (hn : 1 ≤ n) (y : Config n) : coordSupNorm y ≤ ‖y‖ := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [coordSupNorm_eq_iSup_norm]
  exact ciSup_le fun i => norm_le_pi_norm y i
theorem minSeparation_le_pair {n : ℕ} (x : Config n) {i j : Fin n} (h : i < j) :
    minSeparation x ≤ ENNReal.ofReal ‖x i - x j‖ := by
  rw [← supNormVec_eq_norm]
  exact (iInf_le _ i).trans ((iInf_le _ j).trans (iInf_le _ h))
theorem exists_pair_eq_minSeparation {n : ℕ} (hn : 2 ≤ n) (x : Config n) :
    ∃ i j : Fin n, i < j ∧ minSeparation x = ENNReal.ofReal ‖x i - x j‖ := by
  let pairs : Finset (Fin n × Fin n) := Finset.univ.filter fun p => p.1 < p.2
  have hne : pairs.Nonempty :=
    ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp [pairs]⟩
  obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image pairs (fun p => ‖x p.1 - x p.2‖) hne
  have hlt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
  refine ⟨p.1, p.2, hlt, le_antisymm (minSeparation_le_pair x hlt) ?_⟩
  refine le_iInf fun k => le_iInf fun k' => le_iInf fun hk => ?_
  rw [supNormVec_eq_norm]
  exact ENNReal.ofReal_le_ofReal (hmin (k, k') (by simp [pairs, hk]))
theorem minSeparation_ne_top {n : ℕ} (hn : 2 ≤ n) (x : Config n) : minSeparation x ≠ ⊤ := by
  obtain ⟨i, j, -, h⟩ := exists_pair_eq_minSeparation hn x
  rw [h]
  exact ENNReal.ofReal_ne_top
theorem toReal_minSeparation_le_add {n : ℕ} (hn : 2 ≤ n) (x y : Config n) {D : ℝ}
    (hD : ∀ i, ‖x i - y i‖ ≤ D) :
    (minSeparation x).toReal ≤ (minSeparation y).toReal + 2 * D := by
  obtain ⟨i, j, hlt, hy⟩ := exists_pair_eq_minSeparation hn y
  have h₁ : (minSeparation x).toReal ≤ ‖x i - x j‖ :=
    ENNReal.toReal_le_of_le_ofReal (norm_nonneg _) (minSeparation_le_pair x hlt)
  have h₂ : (minSeparation y).toReal = ‖y i - y j‖ := by
    rw [hy, ENNReal.toReal_ofReal (norm_nonneg _)]
  have h₃ : x i - x j = (y i - y j) + (x i - y i) - (x j - y j) := by
    abel
  have h₄ : ‖x i - x j‖ ≤ ‖y i - y j‖ + ‖x i - y i‖ + ‖x j - y j‖ := by
    rw [h₃]
    exact (norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
  have h₅ := hD i
  have h₆ := hD j
  rw [h₂]
  linarith
theorem abs_sub_toReal_minSeparation_le {n : ℕ} (hn : 2 ≤ n) (x y : Config n) :
    |(minSeparation x).toReal - (minSeparation y).toReal| ≤ 2 * coordSupNorm (x - y) := by
  have h₁ := toReal_minSeparation_le_add hn x y (D := coordSupNorm (x - y)) fun i =>
    norm_apply_le_coordSupNorm (x - y) i
  have h₂ := toReal_minSeparation_le_add hn y x (D := coordSupNorm (x - y)) fun i => by
    rw [norm_sub_rev]
    exact norm_apply_le_coordSupNorm (x - y) i
  rw [abs_le]
  constructor <;> linarith
theorem continuous_toReal_minSeparation {n : ℕ} (hn : 2 ≤ n) :
    Continuous fun x : Config n => (minSeparation x).toReal := by
  refine (LipschitzWith.of_dist_le_mul (K := 2) fun x y => ?_).continuous
  rw [Real.dist_eq, dist_eq_norm]
  refine (abs_sub_toReal_minSeparation_le hn x y).trans ?_
  have := coordSupNorm_le_norm (by omega : 1 ≤ n) (x - y)
  simpa using mul_le_mul_of_nonneg_left this (by norm_num : (0 : ℝ) ≤ 2)
theorem mem_diagonalSet_iff {n : ℕ} (x : Config n) :
    x ∈ diagonalSet n ↔ ∃ i j : Fin n, i < j ∧ x i = x j := by
  simp [diagonalSet]
theorem diagonalSet_eq_zeroSet (n : ℕ) : diagonalSet n = {x | minSeparation x = 0} := by
  ext x
  rw [mem_diagonalSet_iff]
  show _ ↔ minSeparation x = 0
  constructor
  · rintro ⟨i, j, hlt, hx⟩
    have := minSeparation_le_pair x hlt
    rw [hx, sub_self, norm_zero, ENNReal.ofReal_zero] at this
    exact le_antisymm this bot_le
  · intro h0
    by_cases hn : 2 ≤ n
    · obtain ⟨i, j, hlt, hx⟩ := exists_pair_eq_minSeparation hn x
      rw [h0] at hx
      have hle : ‖x i - x j‖ ≤ 0 := ENNReal.ofReal_eq_zero.mp hx.symm
      exact ⟨i, j, hlt, sub_eq_zero.mp (norm_le_zero_iff.mp hle)⟩
    · have hno : ∀ i j : Fin n, ¬ i < j := by
        intro i j h
        have := j.2
        omega
      simp [minSeparation, hno] at h0
theorem isClosed_diagonalSet (n : ℕ) : IsClosed (diagonalSet n) :=
  isClosed_iUnion_of_finite fun i => isClosed_iUnion_of_finite fun j =>
    isClosed_iUnion_of_finite fun _ => isClosed_eq (continuous_apply i) (continuous_apply j)
theorem compl_diagonalSet (n : ℕ) :
    (diagonalSet n)ᶜ = TestFunctions.injectiveTuples (Fin 4 → ℝ) n := by
  ext x
  rw [Set.mem_compl_iff, mem_diagonalSet_iff]
  constructor
  · intro h i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact h ⟨i, j, hlt, hij⟩
    · exact h ⟨j, i, hgt, hij.symm⟩
  · rintro hinj ⟨i, j, hlt, hx⟩
    exact hlt.ne (hinj hx)
theorem zeroSetProp_holds (n : ℕ) : ZeroSetProp n :=
  ⟨diagonalSet_eq_zeroSet n, isClosed_diagonalSet n⟩
theorem complementProp_holds (n : ℕ) : ComplementProp n :=
  ⟨compl_diagonalSet n, compl_diagonalSet n ▸ (isClosed_diagonalSet n).isOpen_compl⟩
theorem mainClaim_holds : mainClaim :=
  ⟨fun n hn =>
    ⟨⟨minSeparation_ne_top hn, abs_sub_toReal_minSeparation_le hn,
        continuous_toReal_minSeparation hn⟩,
      zeroSetProp_holds n, complementProp_holds n⟩,
    zeroSetProp_holds 1, complementProp_holds 1⟩
end YangMills.Construction.MinSeparation
