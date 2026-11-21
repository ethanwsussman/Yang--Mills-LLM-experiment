import YangMills.Construction.ColdChainAtEveryLevel.SeminormsOfCoordinates
import YangMills.Construction.ColdStepAtMirrorFrames.FormOfTheMeansOfTheCellsFormForm
import YangMills.Construction.ColdStepAtMirrorFrames.PositionsOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.BlockAverages
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
theorem exp_two_mul_le_exp_four {δ s : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hs0 : 0 ≤ s) (hs : s ≤ 2) :
    Real.exp (2 * δ * s) ≤ Real.exp 4 := by
  apply Real.exp_le_exp.2
  nlinarith
theorem abs_single_div_le (i : Fin 4) (m : ℤ) (l : Fin 4) (M s : ℝ) (hM : 0 < M) (hs : 0 ≤ s)
    (hm : (|m| : ℝ) ≤ s * M) :
    |(((Pi.single i m : Fin 4 → ℤ) l : ℤ) : ℝ)| / M ≤ s := by
  rw [div_le_iff₀ hM]
  by_cases h : l = i
  · subst h
    simpa using hm
  · simp only [Pi.single_eq_of_ne h]
    simp only [Int.cast_zero, abs_zero]
    positivity
theorem isTemperedWeight_expWeight (hL : Odd F.blockSide) (hpos : ∀ i, 0 < F.extent i) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (z : F.Cell) :
    IsTemperedWeight (expWeight δ z (j := 0)) (Real.exp 4) := by
  intro i x m hm
  have hNr : (0 : ℝ) < (F.blockSide : ℝ) ^ (F.top - 0) := by
    have : 0 < F.blockSide := hL.pos
    positivity
  have hp : torusSupDist (x + axisOffset 0 i m) z ≤ torusSupDist x z + 2 := by
    refine torusSupDist_add_le hL hpos x _ z 2 fun l => ?_
    refine abs_single_div_le i m l _ 2 hNr (by norm_num) ?_
    have : ((|m| : ℤ) : ℝ) ≤ 2 * (cellSide F : ℝ) := by exact_mod_cast hm
    push_cast at this
    simpa using this
  refine (expWeight_sq_le hδ0 z x _ hp).trans ?_
  exact mul_le_mul_of_nonneg_right (exp_two_mul_le_exp_four hδ0 hδ1 (by norm_num) le_rfl) (sq_nonneg _)
theorem torusSupDist_enclosingCell_le (hL : Odd F.blockSide) (hpos : ∀ i, 0 < F.extent i)
    (x : F.Site 0) (z : F.Cell) :
    torusSupDist (enclosingCell x) z ≤ torusSupDist x z + 1 := by
  obtain ⟨k, hk⟩ := hL.pow (n := F.top)
  have hk' : cellSide F = 2 * k + 1 := hk
  obtain ⟨q, h, hh, hx⟩ := exists_refineSite_add hL (Nat.zero_le F.top) le_rfl x
  have hh' : h ∈ centredCube (cellSide F) := hh
  have hc : enclosingCell x = siteOfCoords F.top q := by
    rw [hx]
    exact enclosingCell_refineSite_add hL _ h hh'
  have hb := (mem_centredCube_iff hk' h).1 hh'
  have e : refineSite 0 F.top (siteOfCoords F.top q : F.Cell) = x + siteOfCoords 0 (-h) := by
    rw [hx, siteOfCoords_neg, add_neg_cancel_right]
  rw [hc, ← torusSupDist_refineSite hL hpos (Nat.zero_le F.top) le_rfl, e]
  refine torusSupDist_add_le hL hpos x _ z 1 fun i => ?_
  have hNr : (0 : ℝ) < (F.blockSide : ℝ) ^ (F.top - 0) := by
    have : 0 < F.blockSide := hL.pos
    positivity
  rw [div_le_one hNr]
  have q1 := hb i
  have hz : ((F.blockSide ^ F.top : ℕ) : ℤ) = 2 * k + 1 := by exact_mod_cast hk
  have : |(-h) i| ≤ ((F.blockSide ^ F.top : ℕ) : ℤ) := by
    rw [abs_le, hz]
    simp only [Pi.neg_apply]
    constructor <;> omega
  have h2 : ((|(-h) i| : ℤ) : ℝ) ≤ (((F.blockSide ^ F.top : ℕ) : ℤ) : ℝ) := by exact_mod_cast this
  push_cast at h2
  simpa using h2
theorem torusSupDist_add_corner_le (hL : Odd F.blockSide) (hpos : ∀ i, 0 < F.extent i) (y z : F.Cell)
    (a b c d : ℤ) (ha : a ∈ windowEnds) (hb : b ∈ windowEnds) (hc : c ∈ windowEnds) (hd : d ∈ windowEnds) :
    torusSupDist (y + siteOfCoords F.top ![d, c, b, a]) z ≤ torusSupDist y z + 1 := by
  refine torusSupDist_add_le hL hpos y _ z 1 fun i => ?_
  simp only [Nat.sub_self, pow_zero, div_one]
  have key : ∀ e ∈ windowEnds, |(e : ℝ)| ≤ 1 := by
    intro e he
    simp only [windowEnds, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl <;> simp
  fin_cases i
  · exact key d hd
  · exact key c hc
  · exact key b hb
  · exact key a ha
theorem expWeight_sq_le_corner (hL : Odd F.blockSide) (hpos : ∀ i, 0 < F.extent i) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (z : F.Cell) (x : F.Site 0) (a b c d : ℤ) (ha : a ∈ windowEnds)
    (hb : b ∈ windowEnds) (hc : c ∈ windowEnds) (hd : d ∈ windowEnds) :
    expWeight δ z x ^ 2 ≤
      Real.exp 4 * expWeight δ z (enclosingCell x + siteOfCoords F.top ![d, c, b, a]) ^ 2 := by
  have h2 : torusSupDist (enclosingCell x + siteOfCoords F.top ![d, c, b, a]) z ≤ torusSupDist x z + 2 := by
    have := torusSupDist_add_corner_le hL hpos (enclosingCell x) z a b c d ha hb hc hd
    have := torusSupDist_enclosingCell_le hL hpos x z
    linarith
  refine (expWeight_sq_le hδ0 z x _ h2).trans ?_
  exact mul_le_mul_of_nonneg_right (exp_two_mul_le_exp_four hδ0 hδ1 (by norm_num) le_rfl) (sq_nonneg _)
theorem expWeight_sq_le_refine (hL : Odd F.blockSide) (hpos : ∀ i, 0 < F.extent i) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (z : F.Cell) (k : Fin 4) (y : F.Cell) (h : Fin 4 → ℤ)
    (hh : h ∈ centredCube (cellSide F)) (l : ℕ) (hl : l ∈ Finset.range (cellSide F)) :
    expWeight δ z y ^ 2 ≤
      Real.exp 4 * expWeight δ z (refineSite 0 F.top y + siteOfCoords 0 h + axisOffset 0 k (l : ℤ)) ^ 2 := by
  obtain ⟨r, hr⟩ := hL.pow (n := F.top)
  have hr' : cellSide F = 2 * r + 1 := hr
  have hb := (mem_centredCube_iff hr' h).1 hh
  have hl' := Finset.mem_range.1 hl
  have hNr : (0 : ℝ) < (F.blockSide : ℝ) ^ (F.top - 0) := by
    have : 0 < F.blockSide := hL.pos
    positivity
  have h2 : torusSupDist (refineSite 0 F.top y + siteOfCoords 0 h + axisOffset 0 k (l : ℤ)) z ≤
      torusSupDist y z + 2 := by
    have e : refineSite 0 F.top y + siteOfCoords 0 h + axisOffset 0 k (l : ℤ) =
        refineSite 0 F.top y + siteOfCoords 0 (h + Pi.single k (l : ℤ)) := by
      unfold axisOffset
      rw [siteOfCoords_add, add_assoc]
    rw [e, ← torusSupDist_refineSite hL hpos (Nat.zero_le F.top) le_rfl y z]
    refine torusSupDist_add_le hL hpos _ _ z 2 fun i => ?_
    rw [div_le_iff₀ hNr]
    have q1 := hb i
    have : |(h + Pi.single k (l : ℤ) : Fin 4 → ℤ) i| ≤ 2 * ((F.blockSide ^ F.top : ℕ) : ℤ) := by
      simp only [Pi.add_apply]
      by_cases hik : i = k
      · subst hik
        simp only [Pi.single_eq_same]
        rw [abs_le]
        constructor <;> omega
      · simp only [Pi.single_eq_of_ne hik, add_zero]
        rw [abs_le]
        constructor <;> omega
    have h3 : ((|(h + Pi.single k (l : ℤ) : Fin 4 → ℤ) i| : ℤ) : ℝ) ≤
        ((2 * ((F.blockSide ^ F.top : ℕ) : ℤ) : ℤ) : ℝ) := by
      exact_mod_cast this
    push_cast at h3
    simpa using h3
  refine (expWeight_sq_le hδ0 z y _ h2).trans ?_
  exact mul_le_mul_of_nonneg_right (exp_two_mul_le_exp_four hδ0 hδ1 (by norm_num) le_rfl) (sq_nonneg _)
theorem sqrt_add_le_sqrt_add_sqrt (A T : ℝ) (hA : 0 ≤ A) (hT : 0 ≤ T) :
    Real.sqrt (A + T) ≤ Real.sqrt A + Real.sqrt T := by apply _root_.YangMills.Construction.CoordinateSeminorms.sqrt_add_le_add_sqrt <;> assumption
theorem extent_pos_of_isLargeCubicTorus (hc : IsLargeCubicTorus F) (i : Fin 4) : 0 < F.extent i := by
  obtain ⟨n, hn, h⟩ := hc
  rw [h i]
  omega
end ColdStepAtMirrorFrames
end YangMills.Construction
end
