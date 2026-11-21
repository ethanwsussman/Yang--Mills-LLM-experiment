import YangMills.Construction.Lattice.BondOrientationDichotomy
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.PeriodicLattice
theorem coe_intCast_mul_meshSize_ne_zero {L m : ℕ} (hL : 13 ≤ L) {j : ℤ} (hj : -(m : ℤ) < j)
    {e : ℤ} (he₁ : 0 < e) (he₂ : e ≤ 2) :
    (((e : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) ≠ 0 := by
  intro h
  rw [AddCircle.coe_eq_zero_iff] at h
  obtain ⟨n, hn⟩ := h
  obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ (m : ℤ) + j - 1 by omega)
  have hL0 : (L : ℝ) ≠ 0 := by
    have : 0 < L := by omega
    exact_mod_cast this.ne'
  have hm : (L : ℝ) ^ m = (L : ℝ) ^ (d + 1) * meshSize L j := by
    unfold meshSize
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hL0]
    congr 1
    push_cast
    omega
  have hs : meshSize L j ≠ 0 := zpow_ne_zero _ hL0
  have hreal : (n : ℝ) * (2 * (L : ℝ) ^ (d + 1)) = (e : ℝ) := by
    apply mul_right_cancel₀ hs
    rw [← hn, zsmul_eq_mul, torusSide, hm]
    ring
  have hint : n * (2 * (L : ℤ) ^ (d + 1)) = e := by exact_mod_cast hreal
  have hdvd : (L : ℤ) ∣ e := ⟨n * 2 * (L : ℤ) ^ d, by rw [← hint]; ring⟩
  have := Int.le_of_dvd he₁ hdvd
  omega
theorem Bond.not_isPositivelyOriented_and_opposite {L m : ℕ} (hL : 13 ≤ L) {j : ℤ}
    (hj : -(m : ℤ) < j) (b : Bond L m j) (h₁ : b.IsPositivelyOriented)
    (h₂ : b.opposite.IsPositivelyOriented) : False := by
  obtain ⟨μ, hμ⟩ := h₁
  obtain ⟨ν, hν⟩ := h₂
  have hsum : unitStep L m j μ + unitStep L m j ν = 0 := by
    rw [← hμ, ← hν]
    show b.target - b.source + (b.source - b.target) = 0
    abel
  have hc : pointOnAxis L m μ (meshSize L j) μ + pointOnAxis L m ν (meshSize L j) μ = 0 :=
    congrArg (fun s : Site L m j => (s : FourTorus L m) μ) hsum
  by_cases h : ν = μ
  · subst h
    simp only [pointOnAxis, Pi.single_eq_same] at hc
    refine coe_intCast_mul_meshSize_ne_zero hL hj (e := 2) (by norm_num) le_rfl ?_
    rw [← hc, ← AddCircle.coe_add]
    congr 1
    push_cast
    ring
  · simp only [pointOnAxis, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm h), add_zero] at hc
    refine coe_intCast_mul_meshSize_ne_zero hL hj (e := 1) (by norm_num) (by norm_num) ?_
    simpa using hc
theorem bondOrientationDichotomy_holds : BondOrientationDichotomy := by
  intro L m hL _ j hj b
  obtain ⟨μ, h | h⟩ := b.isNeighbour
  · exact Or.inl ⟨⟨μ, h⟩, fun h₂ => Bond.not_isPositivelyOriented_and_opposite hL.2 hj b ⟨μ, h⟩ h₂⟩
  · have hr : b.opposite.IsPositivelyOriented :=
      ⟨μ, by
        show b.source - b.target = _
        rw [← neg_sub, h, neg_neg]⟩
    exact Or.inr ⟨hr, fun h₁ => Bond.not_isPositivelyOriented_and_opposite hL.2 hj b h₁ hr⟩
end YangMills.Construction.PeriodicLattice
