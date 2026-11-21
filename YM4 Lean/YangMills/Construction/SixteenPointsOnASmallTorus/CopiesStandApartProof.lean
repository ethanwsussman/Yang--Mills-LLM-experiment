import YangMills.Construction.ResponseInTheExpansion.SupportsStayApart
import YangMills.Construction.SixteenPointsOnASmallTorus.CopiesStandApart
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SmallTorusCopies
open TorusFields WeightedResponses
private theorem two_mul_le_abs_of_intCast_eq {N M : ℕ} {e u : ℤ} {δ : ℝ} (hN : (N : ℤ) = 4 * (M : ℤ))
    (hu : |(u : ℝ)| ≤ 2 * (M : ℝ) - 2 * δ)
    (he : ((e : ℤ) : ZMod N) = ((2 * (M : ℤ) - u : ℤ) : ZMod N)) : 2 * δ ≤ |(e : ℝ)| := by
  obtain ⟨j, hj⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 he
  rw [hN] at hj
  have hjR : (2 * (M : ℝ) - u) - e = 4 * (M : ℝ) * j := by exact_mod_cast hj
  obtain ⟨hu1, hu2⟩ := abs_le.1 hu
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  rcases le_or_gt j 0 with hj0 | hj0
  · have hjn : (j : ℝ) ≤ 0 := by exact_mod_cast hj0
    have hprod : (M : ℝ) * j ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hM hjn
    exact le_trans (by linarith) (le_abs_self (e : ℝ))
  · have hjp : (1 : ℝ) ≤ j := by exact_mod_cast hj0
    have hprod : (M : ℝ) ≤ (M : ℝ) * j := le_mul_of_one_le_right hM hjp
    exact le_trans (by linarith) (neg_le_abs (e : ℝ))
private theorem two_mul_le_abs_of_reflected_coords {N M : ℕ} (hN : (N : ℤ) = 4 * (M : ℤ)) (i i' : Fin 2)
    (hii : i ≠ i') (x x' : ZMod N) {δ : ℝ}
    (hx : |((((-1 : ZMod N) ^ (i : ℕ) * (x - 2 * (M : ZMod N) * ((i : ℕ) : ZMod N))).valMinAbs : ℤ) : ℝ)| ≤ (M : ℝ) - δ)
    (hx' : |((((-1 : ZMod N) ^ (i' : ℕ) * (x' - 2 * (M : ZMod N) * ((i' : ℕ) : ZMod N))).valMinAbs : ℤ) : ℝ)| ≤ (M : ℝ) - δ)
    {e : ℤ} (he : x' = x + ((e : ℤ) : ZMod N)) : 2 * δ ≤ |(e : ℝ)| := by
  have hcases : (i = 0 ∧ i' = 1) ∨ (i = 1 ∧ i' = 0) :=
    (by decide : ∀ a b : Fin 2, a ≠ b → (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)) i i' hii
  generalize hvv : ((-1 : ZMod N) ^ (i : ℕ) * (x - 2 * (M : ZMod N) * ((i : ℕ) : ZMod N))).valMinAbs = v at hx
  generalize hvv' : ((-1 : ZMod N) ^ (i' : ℕ) * (x' - 2 * (M : ZMod N) * ((i' : ℕ) : ZMod N))).valMinAbs = v' at hx'
  have hc : ((v : ℤ) : ZMod N) = (-1 : ZMod N) ^ (i : ℕ) * (x - 2 * (M : ZMod N) * ((i : ℕ) : ZMod N)) := by
    rw [← hvv, ZMod.coe_valMinAbs]
  have hc' : ((v' : ℤ) : ZMod N) = (-1 : ZMod N) ^ (i' : ℕ) * (x' - 2 * (M : ZMod N) * ((i' : ℕ) : ZMod N)) := by
    rw [← hvv', ZMod.coe_valMinAbs]
  have hsum : |((v + v' : ℤ) : ℝ)| ≤ 2 * (M : ℝ) - 2 * δ := by
    push_cast
    exact (abs_add_le _ _).trans (by linarith)
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, Nat.cast_zero, Nat.cast_one, mul_zero, sub_zero, one_mul,
      mul_one] at hc hc'
    refine two_mul_le_abs_of_intCast_eq hN hsum ?_
    push_cast
    rw [hc, hc']
    have : ((e : ℤ) : ZMod N) = x' - x := by rw [he]; ring
    rw [this]
    ring
  · simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, Nat.cast_zero, Nat.cast_one, mul_zero, sub_zero, one_mul,
      mul_one] at hc hc'
    have hneg := two_mul_le_abs_of_intCast_eq (e := -e) hN hsum (by
      push_cast
      rw [hc, hc']
      have : ((e : ℤ) : ZMod N) = x' - x := by rw [he]; ring
      rw [this]
      ring)
    simpa using hneg
private theorem abs_coord_le_of_inside_cell {M : ℕ} {a₀ ρ : ℝ} {v : ℤ} (ha : 0 < a₀)
    (hin : |a₀ / 2 * (v : ℝ)| + ρ ≤ (M : ℝ) * a₀ / 2) : |(v : ℝ)| ≤ (M : ℝ) - 2 * ρ / a₀ := by
  rw [abs_mul, abs_of_pos (by positivity : 0 < a₀ / 2)] at hin
  have h2 : 2 * ρ / a₀ * a₀ = 2 * ρ := by field_simp
  refine le_of_mul_le_mul_right ?_ ha
  rw [sub_mul, h2]
  linarith
theorem reflectedSupportsSeparated_of_supportsSeparated
    (hS : ResponseInTheExpansion.supportsSeparatedAtLowerLevels) : reflectedSupportsSeparatedStatement := by
  intro L _ hL K κ t ρ H Λ w htκ hρ _ hsrc r r' hrr Y hY Y' hY'
  have hLpos : (0 : ℝ) < L := by
    have := NeZero.pos L
    exact_mod_cast this
  have ha₀ : 0 < levelSpacing L K 0 := zpow_pos hLpos _
  have hat : levelSpacing L K t = levelSpacing L K 0 * (L : ℝ) ^ t := by
    unfold levelSpacing
    rw [← zpow_natCast (L : ℝ) t, ← zpow_add₀ hLpos.ne']
    congr 1
    push_cast
    ring
  obtain ⟨μ, hμ⟩ := Function.ne_iff.1 hrr
  have hN : ((2 * fineSide L t (twoCellSide L κ t) : ℕ) : ℤ) = 4 * ((L ^ κ : ℕ) : ℤ) := by
    have hpow : L ^ (κ - t) * L ^ t = L ^ κ := by rw [← pow_add, Nat.sub_add_cancel htκ]
    rw [fineSide_eq, twoCellSide, ← hpow]
    push_cast
    ring
  have hcell : ∀ (c : Fin 4 → ℕ) (p : TorusPlaquette (fineSide L t (twoCellSide L κ t))),
      reflectedWeight (levelSpacing L K 0) (L ^ κ) c w p ≠ 0 →
      |((((-1 : ZMod (2 * fineSide L t (twoCellSide L κ t))) ^ c μ * (doubledBarycentre p μ -
        2 * ((L ^ κ : ℕ) : ZMod (2 * fineSide L t (twoCellSide L κ t))) *
          (c μ : ZMod (2 * fineSide L t (twoCellSide L κ t))))).valMinAbs : ℤ) : ℝ)| ≤
        ((L ^ κ : ℕ) : ℝ) - 2 * ρ / levelSpacing L K 0 := by
    intro c p hp
    have hf := hsrc.away_from_faces _ hp μ
    refine abs_coord_le_of_inside_cell ha₀ ?_
    have hl : cellLength L K κ / 2 = ((L ^ κ : ℕ) : ℝ) * levelSpacing L K 0 / 2 := by
      rw [cellLength]
      push_cast
      ring
    rw [← hl]
    exact hf
  have hap : SupportsSeparated L t (2 * (ρ / levelSpacing L K t))
      (reflectedWeight (levelSpacing L K 0) (L ^ κ) (fun μ => (r μ : ℕ)) w :
        PlaquetteWeight (fineSide L t (twoCellSide L κ t)))
      (reflectedWeight (levelSpacing L K 0) (L ^ κ) (fun μ => (r' μ : ℕ)) w) := by
    intro p p' hp hp'
    obtain ⟨e, he, hb⟩ := exists_offset_of_supDist (doubledBarycentre p.1) (doubledBarycentre p'.1)
    have hd : doubledBarycentre p'.1 μ = doubledBarycentre p.1 μ + ((e μ : ℤ) : ZMod _) := by
      have := congrFun he μ
      simpa [siteOfInt] using this
    have hgap := two_mul_le_abs_of_reflected_coords hN (r μ) (r' μ) hμ _ _ (hcell _ p.1 hp) (hcell _ p'.1 hp') hd
    have hbR : |(e μ : ℝ)| ≤ (supDist (doubledBarycentre p.1) (doubledBarycentre p'.1) : ℝ) := by
      have h1 := hb μ
      have h2 : |(e μ : ℝ)| = ((e μ).natAbs : ℝ) := by
        rw [Nat.cast_natAbs, Int.cast_abs]
      rw [h2]
      exact_mod_cast h1
    rw [barycentreDist, le_div_iff₀ (by positivity), hat]
    have hLt : (0 : ℝ) < (L : ℝ) ^ t := pow_pos hLpos t
    have hval : 2 * (ρ / (levelSpacing L K 0 * (L : ℝ) ^ t)) * (2 * (L : ℝ) ^ t) =
        2 * (2 * ρ / levelSpacing L K 0) := by
      field_simp
    rw [hval]
    exact hgap.trans hbR
  have hfin := hS L hL t t (twoCellSide L κ t) le_rfl _ _ _ hap Y hY Y' hY'
  simp only [Nat.sub_self, pow_zero, mul_one] at hfin
  linarith
end YangMills.Construction.SmallTorusCopies
end
