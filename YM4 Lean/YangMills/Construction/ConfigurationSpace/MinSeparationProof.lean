import YangMills.Construction.ConfigurationSpace.MinSeparationProperties
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.ConfigurationSpace.MinSep
open YangMills.Construction.ConfigurationSpace
theorem maxNorm_eq_norm (w : Fin 4 → ℝ) : maxNorm w = ‖w‖ := by
  have hnonneg : 0 ≤ maxNorm w := Real.iSup_nonneg fun _ => abs_nonneg _
  apply le_antisymm
  · exact ciSup_le fun c => norm_le_pi_norm w c
  · rw [pi_norm_le_iff_of_nonneg hnonneg]
    intro c
    exact le_ciSup (f := fun c => |w c|) (Set.finite_range _).bddAbove c
theorem norm_apply_le_configMaxNorm {n : ℕ} (y : Config n) (i : Fin n) :
    ‖y i‖ ≤ configMaxNorm y := by
  have hnonneg : 0 ≤ configMaxNorm y := Real.iSup_nonneg fun _ => abs_nonneg _
  rw [pi_norm_le_iff_of_nonneg hnonneg]
  intro c
  exact le_ciSup (f := fun ι => |coords y ι|) (Set.finite_range _).bddAbove (toLex (i, c))
theorem configMaxNorm_le_norm {n : ℕ} (hn : 1 ≤ n) (y : Config n) : configMaxNorm y ≤ ‖y‖ := by
  have : Nonempty (CoordIndex n) := ⟨toLex (⟨0, hn⟩, 0)⟩
  exact ciSup_le fun ι =>
    (norm_le_pi_norm (y (ofLex ι).1) (ofLex ι).2).trans (norm_le_pi_norm y _)
theorem minSeparation_le {n : ℕ} (x : Config n) {p : Fin n × Fin n} (hp : p ∈ orderedPairs n) :
    minSeparation x ≤ ENNReal.ofReal ‖x p.1 - x p.2‖ := by
  rw [← maxNorm_eq_norm]
  exact iInf₂_le p hp
theorem exists_pair_minSeparation_eq {n : ℕ} (hne : (orderedPairs n).Nonempty) (x : Config n) :
    ∃ p ∈ orderedPairs n, minSeparation x = ENNReal.ofReal ‖x p.1 - x p.2‖ := by
  obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image (orderedPairs n) (fun p => ‖x p.1 - x p.2‖) hne
  refine ⟨p, hp, le_antisymm (minSeparation_le x hp) (le_iInf₂ fun q hq => ?_)⟩
  rw [maxNorm_eq_norm]
  exact ENNReal.ofReal_le_ofReal (hmin q hq)
theorem orderedPairs_nonempty {n : ℕ} (hn : 2 ≤ n) : (orderedPairs n).Nonempty :=
  ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp [orderedPairs]⟩
theorem minSeparation_ne_top {n : ℕ} (hne : (orderedPairs n).Nonempty) (x : Config n) :
    minSeparation x ≠ ⊤ := by
  obtain ⟨p, -, hp⟩ := exists_pair_minSeparation_eq hne x
  rw [hp]
  exact ENNReal.ofReal_ne_top
theorem toReal_minSeparation_le_add {n : ℕ} (hne : (orderedPairs n).Nonempty) (x x' : Config n)
    {D : ℝ} (hD : ∀ i, ‖x i - x' i‖ ≤ D) :
    (minSeparation x).toReal ≤ (minSeparation x').toReal + 2 * D := by
  obtain ⟨p, hp, hx'⟩ := exists_pair_minSeparation_eq hne x'
  have h₁ : (minSeparation x).toReal ≤ ‖x p.1 - x p.2‖ :=
    ENNReal.toReal_le_of_le_ofReal (norm_nonneg _) (minSeparation_le x hp)
  have h₂ : (minSeparation x').toReal = ‖x' p.1 - x' p.2‖ := by
    rw [hx', ENNReal.toReal_ofReal (norm_nonneg _)]
  have h₃ : x p.1 - x p.2 = (x' p.1 - x' p.2) + (x p.1 - x' p.1) - (x p.2 - x' p.2) := by
    abel
  have h₄ : ‖x p.1 - x p.2‖ ≤ ‖x' p.1 - x' p.2‖ + ‖x p.1 - x' p.1‖ + ‖x p.2 - x' p.2‖ := by
    rw [h₃]
    exact (norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
  have h₅ := hD p.1
  have h₆ := hD p.2
  rw [h₂]
  linarith
theorem abs_toReal_minSeparation_sub_le {n : ℕ} (hne : (orderedPairs n).Nonempty) (x x' : Config n) :
    |(minSeparation x).toReal - (minSeparation x').toReal| ≤ 2 * configMaxNorm (x - x') := by
  have h₁ := toReal_minSeparation_le_add hne x x' (D := configMaxNorm (x - x')) fun i =>
    norm_apply_le_configMaxNorm (x - x') i
  have h₂ := toReal_minSeparation_le_add hne x' x (D := configMaxNorm (x - x')) fun i => by
    rw [norm_sub_rev]
    exact norm_apply_le_configMaxNorm (x - x') i
  rw [abs_le]
  constructor <;> linarith
theorem continuous_toReal_minSeparation {n : ℕ} (hn : 2 ≤ n) :
    Continuous fun x : Config n => (minSeparation x).toReal := by
  refine (LipschitzWith.of_dist_le_mul (K := 2) fun x x' => ?_).continuous
  rw [Real.dist_eq, dist_eq_norm]
  refine (abs_toReal_minSeparation_sub_le (orderedPairs_nonempty hn) x x').trans ?_
  have := configMaxNorm_le_norm (by omega : 1 ≤ n) (x - x')
  simpa using mul_le_mul_of_nonneg_left this (by norm_num : (0 : ℝ) ≤ 2)
theorem mem_fatDiagonal_iff {n : ℕ} (x : Config n) :
    x ∈ fatDiagonal n ↔ ∃ p ∈ orderedPairs n, x p.1 = x p.2 := by
  simp [fatDiagonal, pairDiagonal]
theorem fatDiagonal_eq_setOf_minSeparation_eq_zero (n : ℕ) :
    fatDiagonal n = {x | minSeparation x = 0} := by
  ext x
  rw [mem_fatDiagonal_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨p, hp, hx⟩
    have := minSeparation_le x hp
    rw [hx, sub_self, norm_zero, ENNReal.ofReal_zero] at this
    exact le_antisymm this bot_le
  · intro h0
    rcases (orderedPairs n).eq_empty_or_nonempty with hempty | hne
    · simp [minSeparation, hempty] at h0
    · obtain ⟨p, hp, hx⟩ := exists_pair_minSeparation_eq hne x
      rw [h0] at hx
      have hle : ‖x p.1 - x p.2‖ ≤ 0 := ENNReal.ofReal_eq_zero.mp hx.symm
      exact ⟨p, hp, sub_eq_zero.mp (norm_le_zero_iff.mp hle)⟩
theorem isClosed_fatDiagonal (n : ℕ) : IsClosed (fatDiagonal n) :=
  isClosed_biUnion_finset fun p _ => isClosed_eq (continuous_apply p.1) (continuous_apply p.2)
theorem fatDiagonal_compl (n : ℕ) :
    (fatDiagonal n)ᶜ = TestFunctions.injectiveTuples (Fin 4 → ℝ) n := by
  ext x
  rw [Set.mem_compl_iff, mem_fatDiagonal_iff]
  constructor
  · intro h i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact h ⟨(i, j), by simp [orderedPairs, hlt], hij⟩
    · exact h ⟨(j, i), by simp [orderedPairs, hgt], hij.symm⟩
  · rintro hinj ⟨p, hp, hx⟩
    have hlt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
    exact hlt.ne (hinj hx)
theorem fatDiagonalEqZeros_holds (n : ℕ) : FatDiagonalEqZeros n :=
  ⟨fatDiagonal_eq_setOf_minSeparation_eq_zero n, isClosed_fatDiagonal n⟩
theorem fatDiagonalComplEqInjective_holds (n : ℕ) : FatDiagonalComplEqInjective n :=
  ⟨fatDiagonal_compl n, fatDiagonal_compl n ▸ (isClosed_fatDiagonal n).isOpen_compl⟩
theorem minSeparationProperties_holds : MinSeparationProperties :=
  ⟨fun n hn =>
    ⟨⟨minSeparation_ne_top (orderedPairs_nonempty hn),
      abs_toReal_minSeparation_sub_le (orderedPairs_nonempty hn),
      continuous_toReal_minSeparation hn⟩, fatDiagonalEqZeros_holds n,
      fatDiagonalComplEqInjective_holds n⟩,
    fatDiagonalEqZeros_holds 1, fatDiagonalComplEqInjective_holds 1⟩
end YangMills.Construction.ConfigurationSpace.MinSep
