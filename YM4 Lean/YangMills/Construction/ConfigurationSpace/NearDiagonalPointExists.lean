import YangMills.Construction.ConfigurationSpace.NearDiagonalPoint
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigurationSpace.NearDiagonal
private theorem sum_coords_sq {n : ℕ} (z : Config n) :
    ∑ ι, coords z ι ^ 2 = ∑ j, ∑ c, z j c ^ 2 := by
  rw [← Fintype.sum_prod_type' (f := fun j c => z j c ^ 2)]
  exact Fintype.sum_equiv ofLex _ _ (fun _ => rfl)
private theorem abs_le_maxNorm (w : Fin 4 → ℝ) (c : Fin 4) : |w c| ≤ maxNorm w :=
  le_ciSup (f := fun c => |w c|) (Set.finite_range _).bddAbove c
private def mergePair {n : ℕ} (x : Config n) (i i' : Fin n) : Config n :=
  fun j c => if j = i ∨ j = i' then (x i c + x i' c) / 2 else x j c
private theorem configNorm_sub_mergePair_le {n : ℕ} (x : Config n) {i i' : Fin n}
    (hne : i ≠ i') {s : ℝ} (hs : ∀ c, |x i c - x i' c| ≤ s) :
    configNorm (x - mergePair x i i') ≤ Real.sqrt 2 * s := by
  have hs0 : 0 ≤ s := (abs_nonneg _).trans (hs 0)
  have hsq : ∀ c, (x i c - x i' c) ^ 2 ≤ s ^ 2 :=
    fun c => sq_le_sq' (abs_le.mp (hs c)).1 (abs_le.mp (hs c)).2
  have hsum : ∑ ι, coords (x - mergePair x i i') ι ^ 2 ≤ 2 * s ^ 2 := by
    rw [sum_coords_sq, Fintype.sum_eq_add i i' hne]
    · have hi : ∀ c, (x - mergePair x i i') i c = (x i c - x i' c) / 2 := by
        intro c
        simp only [Pi.sub_apply, mergePair, true_or, if_true]
        ring
      have hi' : ∀ c, (x - mergePair x i i') i' c = -((x i c - x i' c) / 2) := by
        intro c
        simp only [Pi.sub_apply, mergePair, or_true, if_true]
        ring
      simp only [hi, hi', Fin.sum_univ_four]
      nlinarith [hsq 0, hsq 1, hsq 2, hsq 3]
    · rintro j ⟨hj, hj'⟩
      refine Finset.sum_eq_zero fun c _ => ?_
      simp [mergePair, hj, hj']
  calc configNorm (x - mergePair x i i')
      ≤ Real.sqrt (2 * s ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt 2 * s := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hs0]
theorem existsNearDiagonalPoint_holds : ExistsNearDiagonalPoint := by
  intro n hn x
  have hpairs : (orderedPairs n).Nonempty :=
    ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by
      simp only [orderedPairs, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Fin.mk_lt_mk.mpr Nat.zero_lt_one⟩
  obtain ⟨p, hp, hmin⟩ :=
    Finset.exists_min_image (orderedPairs n) (fun p => maxNorm (x p.1 - x p.2)) hpairs
  have hlt : p.1 < p.2 := by simpa [orderedPairs] using hp
  refine ⟨mergePair x p.1 p.2, ?_, ?_⟩
  · refine Set.mem_iUnion₂.mpr ⟨p, hp, ?_⟩
    funext c
    simp [mergePair]
  · have hbound := configNorm_sub_mergePair_le x hlt.ne
      (s := maxNorm (x p.1 - x p.2)) (fun c => abs_le_maxNorm (x p.1 - x p.2) c)
    have hle : ENNReal.ofReal (maxNorm (x p.1 - x p.2)) ≤ minSeparation x :=
      le_iInf₂ fun q hq => ENNReal.ofReal_le_ofReal (hmin q hq)
    calc ENNReal.ofReal (configNorm (x - mergePair x p.1 p.2))
        ≤ ENNReal.ofReal (Real.sqrt 2 * maxNorm (x p.1 - x p.2)) :=
          ENNReal.ofReal_le_ofReal hbound
      _ = ENNReal.ofReal (Real.sqrt 2) * ENNReal.ofReal (maxNorm (x p.1 - x p.2)) :=
          ENNReal.ofReal_mul (Real.sqrt_nonneg 2)
      _ ≤ ENNReal.ofReal (Real.sqrt 2) * minSeparation x := by gcongr
end YangMills.Construction.ConfigurationSpace.NearDiagonal
end
