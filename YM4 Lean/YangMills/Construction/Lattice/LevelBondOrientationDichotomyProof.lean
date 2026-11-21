import YangMills.Construction.Lattice.LevelBondOrientationDichotomy
import YangMills.Construction.Torus.NeighborCountProof
import Mathlib
namespace YangMills.Construction.PeriodicLattice
theorem addCircle_coe_ne_zero_of_pos_of_lt {p x : ℝ} (hx : 0 < x) (hxp : x < p) :
    ((x : ℝ) : AddCircle p) ≠ 0 := by apply _root_.YangMills.Construction.Torus.NeighborCount.addCircle_coe_ne_zero_of_lt <;> assumption
theorem meshSize_levelDepth_pos_and_two_mul_lt {L m K j : ℕ} (hL : 13 ≤ L) (hm : 0 < m)
    (hj : j ≤ K) :
    0 < meshSize L (levelDepth K j) ∧ 2 * meshSize L (levelDepth K j) < torusSide L m := by
  have hL13 : (13 : ℝ) ≤ L := by exact_mod_cast hL
  have hL1 : (1 : ℝ) ≤ L := by linarith
  obtain ⟨d, hd⟩ : ∃ d : ℕ, levelDepth K j = (d : ℤ) := ⟨K - j, by simp only [levelDepth]; omega⟩
  have hpow : (1 : ℝ) ≤ (L : ℝ) ^ d := one_le_pow₀ hL1
  have hpos : 0 < meshSize L (levelDepth K j) := by
    rw [meshSize, hd, zpow_neg, zpow_natCast]
    positivity
  have hle : meshSize L (levelDepth K j) ≤ 1 := by
    rw [meshSize, hd, zpow_neg, zpow_natCast]
    exact inv_le_one_of_one_le₀ hpow
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n + 1 := ⟨m - 1, by omega⟩
  have hpn : (1 : ℝ) ≤ (L : ℝ) ^ n := one_le_pow₀ hL1
  have hside : (26 : ℝ) ≤ torusSide L (n + 1) := by
    rw [torusSide, pow_succ]
    nlinarith
  exact ⟨hpos, by linarith⟩
theorem unitStep_levelDepth_add_ne_zero {L m K j : ℕ} (hL : 13 ≤ L) (hm : 0 < m) (hj : j ≤ K)
    (μ ν : Fin 4) : unitStep L m (levelDepth K j) μ + unitStep L m (levelDepth K j) ν ≠ 0 := by
  obtain ⟨hpos, hlt⟩ := meshSize_levelDepth_pos_and_two_mul_lt (L := L) (m := m) hL hm hj
  set a := meshSize L (levelDepth K j) with ha
  intro h
  have hc : (((unitStep L m (levelDepth K j) μ + unitStep L m (levelDepth K j) ν :
      Site L m (levelDepth K j)) : FourTorus L m) μ) = 0 := by
    rw [h]
    rfl
  have hsum : pointOnAxis L m μ a μ + pointOnAxis L m ν a μ = 0 := hc
  by_cases hνμ : ν = μ
  · subst hνμ
    simp only [pointOnAxis, Pi.single_eq_same] at hsum
    rw [← AddCircle.coe_add] at hsum
    exact addCircle_coe_ne_zero_of_pos_of_lt (p := torusSide L m) (x := a + a) (by linarith)
      (by linarith) hsum
  · simp only [pointOnAxis, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hνμ), add_zero] at hsum
    exact addCircle_coe_ne_zero_of_pos_of_lt (p := torusSide L m) (x := a) hpos (by linarith) hsum
theorem levelBondOrientationDichotomy_holds : LevelBondOrientationDichotomy := by
  intro L m K hL hm _ j hj b
  have hnot : ¬(b.IsPositivelyOriented ∧ b.opposite.IsPositivelyOriented) := by
    rintro ⟨⟨μ, h⟩, ⟨ν, h'⟩⟩
    refine unitStep_levelDepth_add_ne_zero hL.2 hm hj μ ν ?_
    rw [← h, ← h']
    change b.target - b.source + (b.source - b.target) = 0
    abel
  obtain ⟨μ, h | h⟩ := b.isNeighbour
  · exact Or.inl ⟨⟨μ, h⟩, fun h' => hnot ⟨⟨μ, h⟩, h'⟩⟩
  · have hopp : b.opposite.IsPositivelyOriented := by
      refine ⟨μ, ?_⟩
      change b.source - b.target = _
      rw [← neg_sub, h, neg_neg]
    exact Or.inr ⟨hopp, fun h' => hnot ⟨h', hopp⟩⟩
end YangMills.Construction.PeriodicLattice
