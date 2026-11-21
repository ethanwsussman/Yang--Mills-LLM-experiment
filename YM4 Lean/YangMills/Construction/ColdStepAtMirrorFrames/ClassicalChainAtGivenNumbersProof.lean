import YangMills.Construction.ColdChainAtEveryLevel.ChartsOfCellsAndSites
import YangMills.Construction.ColdChainAtEveryLevel.SitesOfAPatch
import YangMills.Construction.ColdStepAtMirrorFrames.ChartIsReadOffItsField
import YangMills.Construction.ColdStepAtMirrorFrames.ClassicalChainAtGivenNumbers
import YangMills.Construction.ColdStepAtMirrorFrames.ContourOfAChartField
import YangMills.Construction.ColdStepAtMirrorFrames.OffsetsInABlock
import YangMills.Construction.ColdStepAtMirrorFrames.SumsThatAgreeNearAPoint
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
namespace AdmissibleParameters
open BlockOffsets
variable {F : BlockFrame}
theorem pow_mul_exp_neg_le_factorial (c n1 : ℝ) (hc : 0 < c) (hn : 0 < n1) (x : ℝ) (hx : 0 ≤ x) :
    (x / n1) ^ 16000 * Real.exp (-(c * x)) ≤ (16000 : ℕ).factorial / (c * n1) ^ 16000 := by
  have h := Real.pow_div_factorial_le_exp (c * x) (by positivity) 16000
  have hf : (0 : ℝ) < ((16000 : ℕ).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have e : (x / n1) ^ 16000 = (c * x) ^ 16000 / (c * n1) ^ 16000 := by
    rw [← div_pow]
    congr 1
    field_simp
  have hE : 0 < Real.exp (c * x) := Real.exp_pos _
  rw [div_le_iff₀ hf] at h
  rw [e, Real.exp_neg, div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
  rw [← div_eq_mul_inv, div_le_iff₀ hE]
  linarith
theorem torusDecayFactor_pos (L : ℕ) (δ x : ℝ) : 0 < BlockAverages.torusDecayFactor L δ x := by
  unfold BlockAverages.torusDecayFactor
  have h1 : (0 : ℝ) < max 1 ((x / (L : ℝ) ^ (1 / 640 : ℝ)) ^ 16000) :=
    lt_of_lt_of_le one_pos (le_max_left _ _)
  exact mul_pos h1 (Real.exp_pos _)
theorem exists_exp_le_div_torusDecayFactor (δ : ℝ) (hδ : 0 < δ) (L : ℕ) (hL : 1 ≤ L) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ x : ℝ, 0 ≤ x → Real.exp (-(δ / 2 * x)) ≤ M / BlockAverages.torusDecayFactor L (δ / 4) x := by
  set n1 : ℝ := (L : ℝ) ^ (1 / 640 : ℝ) with hn1
  have hn : 0 < n1 := by
    have : (0 : ℝ) < L := by exact_mod_cast hL
    positivity
  set B : ℝ := (16000 : ℕ).factorial / (δ / 4 * n1) ^ 16000 with hB
  have hB0 : 0 ≤ B := by positivity
  refine ⟨1 + B, by linarith, ?_⟩
  intro x hx
  rw [le_div_iff₀ (torusDecayFactor_pos L _ x)]
  unfold BlockAverages.torusDecayFactor
  rw [← hn1]
  have h1 := pow_mul_exp_neg_le_factorial (δ / 4) n1 (by positivity) hn x hx
  have e : Real.exp (-(δ / 2 * x)) * (max 1 ((x / n1) ^ 16000) * Real.exp (δ / 4 * x)) =
      max 1 ((x / n1) ^ 16000) * Real.exp (-(δ / 4 * x)) := by
    have : Real.exp (-(δ / 4 * x)) = Real.exp (-(δ / 2 * x)) * Real.exp (δ / 4 * x) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [this]
    ring
  rw [e]
  have hE : Real.exp (-(δ / 4 * x)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ δ / 4 * x := by positivity
    linarith
  rcases le_total 1 ((x / n1) ^ 16000) with h | h
  · rw [max_eq_right h]
    linarith
  · rw [max_eq_left h, one_mul]
    linarith
theorem cellSupDist_comm (a b : F.Cell) : cellSupDist a b = cellSupDist b a := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_comm <;> assumption
theorem cellSupDist_triangle (a b c : F.Cell) : cellSupDist a c ≤ cellSupDist a b + cellSupDist b c := by apply _root_.YangMills.Construction.BlockAverages.PatchLocality.cellSupDist_triangle <;> assumption
theorem bondListDiameter_le_two_mul {k : ℕ} (Y : F.Cell) (c : Fin k → F.Site F.top × Fin 4) :
    bondListDiameter c ≤ 2 * bondListDistance Y c := by
  unfold bondListDiameter
  apply Finset.sup_le
  intro l _
  apply Finset.sup_le
  intro l' _
  have h1 : cellSupDist Y (c l).1 ≤ bondListDistance Y c :=
    Finset.le_sup (f := fun l => cellSupDist Y (c l).1) (Finset.mem_univ l)
  have h2 : cellSupDist Y (c l').1 ≤ bondListDistance Y c :=
    Finset.le_sup (f := fun l => cellSupDist Y (c l).1) (Finset.mem_univ l')
  have h3 := cellSupDist_triangle (c l).1 Y (c l').1
  rw [cellSupDist_comm (c l).1 Y] at h3
  omega
theorem exp_neg_le_of_le_two_mul (δ : ℝ) (hδ : 0 < δ) (d D : ℝ) (hD : D ≤ 2 * d) :
    Real.exp (-δ * d) ≤ Real.exp (-(δ / 2 * D)) := by
  rw [Real.exp_le_exp]
  nlinarith
theorem sixtyFour_le_extent {L : ℕ} (h : IsBlockTorus L F) (i : Fin 4) : 64 ≤ F.extent i := by
  obtain ⟨_, n, hn, hs⟩ := h
  rw [hs]
  exact hn
theorem two_le_extent {L : ℕ} (h : IsBlockTorus L F) (i : Fin 4) : 2 ≤ F.extent i :=
  le_trans (by norm_num) (sixtyFour_le_extent h i)
theorem isAdmissibleAmbient_of_isBlockTorus {L : ℕ} (h : IsBlockTorus L F) : IsAdmissibleAmbient F :=
  Or.inr (sixtyFour_le_extent h)
theorem finiteCells_isOrthantRegular {L : ℕ} (h : IsBlockTorus L F) (m : ℕ) :
    IsOrthantRegular (finiteCells F) m := by
  intro z
  exact ⟨fun _ => 1, fun _ => Or.inl rfl, fun q _ _ _ _ _ => mem_finiteCells (two_le_extent h) _⟩
theorem isCold_of_isSmallCurvature {s : ℝ} {V : F.GaugeField F.top} (h : IsSmallCurvature s V)
    (S : Finset F.Cell) : IsCold S F.top s V :=
  fun p hp => h p (Finset.mem_filter.mp hp).2.1
theorem minimizingCoordinates_spec (hread : ChartDeterminedByField) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) {a ρ N0 s : ℝ} {V : F.GaugeField F.top} (hρ : ρ ≤ 1)
    (h : HasColdMinimizer a ρ N0 s (finiteCells F) V) :
    IsMinimizingChart a (finiteCells F) V ρ (minimizingCoordinates a (finiteCells F) V ρ) ∧
      ∀ b ∈ chordBonds (finiteCells F), ‖minimizingCoordinates a (finiteCells F) V ρ b.1 b.2‖ ≤ N0 * s := by
  obtain ⟨w, ⟨w0, w1, w2⟩, -, huniq⟩ := h
  have hex : ∃ w, IsMinimizingChart a (finiteCells F) V ρ w :=
    ⟨w, w0, fun b hb => (w1 b hb).trans (min_le_left _ _), w2⟩
  have hw' : IsMinimizingChart a (finiteCells F) V ρ (minimizingCoordinates a (finiteCells F) V ρ) := by
    unfold minimizingCoordinates
    rw [dif_pos hex]
    exact hex.choose_spec
  refine ⟨hw', ?_⟩
  obtain ⟨γ, hγ, hsame⟩ := huniq (chartedField (minimizingCoordinates a (finiteCells F) V ρ) V) hw'.2.2
  have e : minimizingCoordinates a (finiteCells F) V ρ = w :=
    hread F w _ V γ hL hs w0 hw'.1 (fun b hb => ((w1 b hb).trans (min_le_left _ _)).trans hρ)
      (fun b hb => (hw'.2.1 b hb).trans hρ) hγ hsame
  intro b hb
  rw [e]
  exact (w1 b hb).trans (min_le_right _ _)
theorem card_centredCube {L : ℕ} (hL : Odd L) : (centredCube L).card = L ^ 4 := by apply _root_.YangMills.Construction.LatticePaths.card_centredCube <;> assumption
theorem one_sub_le_norm_contourAverage (hL : Odd F.blockSide) (W : F.GaugeField F.depth)
    (V : F.GaugeField F.top) (c : F.Site F.top × Fin 4) {ε : ℝ}
    (h : ∀ (u : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)), u ∈ centredCube F.blockSide →
      ‖contourHolonomyDefect W V c u π - 1‖ ≤ ε) :
    1 - ε ≤ ‖contourAverage W c‖ := by
  classical
  set v : ℍ[ℝ] := ((V c.1 c.2 : UnitQuaternion) : ℍ[ℝ]) with hv
  have hvn : ‖v‖ = 1 := _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.norm_coe_unitQuaternion _
  have hLpos : (0 : ℝ) < F.blockSide := by
    have : 0 < F.blockSide := hL.pos
    exact_mod_cast this
  set hol : (Fin 4 → ℤ) → Equiv.Perm (Fin 4) → ℍ[ℝ] := fun u π =>
    ((pathHolonomy W (refineSite c.1) (bondContour F.blockSide u π c.2) : UnitQuaternion) : ℍ[ℝ]) with hhol
  have hne : ∀ u ∈ centredCube F.blockSide, ∀ π, ‖hol u π - v‖ ≤ ε := by
    intro u hu π
    have e : hol u π - v = (contourHolonomyDefect W V c u π - 1) * v := by
      have e0 : contourHolonomyDefect W V c u π * v = hol u π := by
        unfold contourHolonomyDefect
        rw [hv]
        rw [← Submonoid.coe_mul, inv_mul_cancel_right]
      rw [sub_mul, e0, one_mul]
    rw [e, norm_mul, hvn, mul_one]
    exact h u π hu
  have hcount : ∑ _u ∈ centredCube F.blockSide, ∑ _π : Equiv.Perm (Fin 4), v =
      ((24 * (F.blockSide : ℝ) ^ 4 : ℝ)) • v := by
    rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_perm, card_centredCube hL,
      ← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    congr 1
    simp [Nat.factorial]
    ring
  have hD : (24 * (F.blockSide : ℝ) ^ 4) ≠ 0 := by positivity
  have e : contourAverage W c - v =
      (1 / (24 * (F.blockSide : ℝ) ^ 4)) •
        ∑ u ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), (hol u π - v) := by
    simp only [Finset.sum_sub_distrib]
    rw [hcount, smul_sub, smul_smul, one_div, inv_mul_cancel₀ hD, one_smul]
    unfold contourAverage
    rw [one_div]
  have hb : ‖contourAverage W c - v‖ ≤ ε := by
    rw [e, norm_smul]
    have h1 : ‖∑ u ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), (hol u π - v)‖ ≤
        ∑ _u ∈ centredCube F.blockSide, ∑ _π : Equiv.Perm (Fin 4), ε := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u hu => ?_)
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun π _ => hne u hu π)
    have h2 : ∑ _u ∈ centredCube F.blockSide, ∑ _π : Equiv.Perm (Fin 4), ε =
        (24 * (F.blockSide : ℝ) ^ 4) * ε := by
      rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_perm, card_centredCube hL,
        nsmul_eq_mul, nsmul_eq_mul]
      simp [Nat.factorial]
      ring
    rw [h2] at h1
    have h3 : ‖(1 / (24 * (F.blockSide : ℝ) ^ 4))‖ = 1 / (24 * (F.blockSide : ℝ) ^ 4) := by
      rw [Real.norm_of_nonneg (by positivity)]
    rw [h3]
    calc 1 / (24 * (F.blockSide : ℝ) ^ 4) *
          ‖∑ u ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), (hol u π - v)‖
        ≤ 1 / (24 * (F.blockSide : ℝ) ^ 4) * ((24 * (F.blockSide : ℝ) ^ 4) * ε) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ε := by field_simp
  have h4 := norm_sub_norm_le v (v - contourAverage W c)
  rw [sub_sub_cancel, hvn, norm_sub_rev] at h4
  linarith
theorem valMinAbs_intCast_of_two_mul_abs_lt {p : ℕ} {A : ℤ} (h : 2 * |A| < p) :
    ((A : ZMod p)).valMinAbs = A := by
  have hp : p ≠ 0 := by
    rintro rfl
    have := abs_nonneg A
    simp at h
    omega
  have : NeZero p := ⟨hp⟩
  rw [ZMod.valMinAbs_spec]
  refine ⟨rfl, ?_⟩
  have h1 := abs_lt.mp (show |2 * A| < (p : ℤ) by rw [abs_mul]; simpa using h)
  simp only [Set.mem_Ioc]
  omega
theorem le_natAbs_valMinAbs_intCast {n : ℕ} {x : ℤ} {t : ℕ} (hx : |x| < n) (h1 : (t : ℤ) ≤ |x|)
    (h2 : (t : ℤ) ≤ n - |x|) : t ≤ ((x : ZMod n).valMinAbs).natAbs := by
  have hn : n ≠ 0 := by
    rintro rfl
    have := abs_nonneg x
    simp at hx
    omega
  have : NeZero n := ⟨hn⟩
  set u : ℤ := (x : ZMod n).valMinAbs with hu
  have hle : u.natAbs ≤ n / 2 := ZMod.natAbs_valMinAbs_le _
  have hcast : ((u : ℤ) : ZMod n) = (x : ZMod n) := ZMod.coe_valMinAbs _
  have hd : (n : ℤ) ∣ u - x := by
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub x u n).mp hcast.symm
    exact this
  obtain ⟨q, hq⟩ := hd
  have hn0 : (0 : ℤ) < n := by omega
  have hq1 : q < 2 := by
    by_contra hc
    have : (n : ℤ) * 2 ≤ (n : ℤ) * q := by nlinarith
    rcases abs_cases x with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> omega
  have hq2 : -2 < q := by
    by_contra hc
    have : (n : ℤ) * q ≤ (n : ℤ) * (-2) := by nlinarith
    rcases abs_cases x with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> omega
  have hcases : q = -1 ∨ q = 0 ∨ q = 1 := by omega
  rcases hcases with rfl | rfl | rfl <;> rcases abs_cases x with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> omega
theorem le_cellSupDist_add_siteOfCoords (Y : F.Cell) (x : Fin 4 → ℤ) (p : Fin 4) {t : ℕ}
    (hx : |x p| < F.extent p) (h1 : (t : ℤ) ≤ |x p|) (h2 : (t : ℤ) ≤ F.extent p - |x p|) :
    t ≤ cellSupDist Y (Y + siteOfCoords F.top x) := by
  rw [cellSupDist_comm]
  have hp : F.period F.top p = F.extent p := period_top p
  have e : ((Y + siteOfCoords F.top x : F.Cell) p - Y p) = ((x p : ℤ) : ZMod (F.period F.top p)) := by
    simp [siteOfCoords]
  have h3 : t ≤ (((Y + siteOfCoords F.top x : F.Cell) p - Y p).valMinAbs).natAbs := by
    rw [e]
    exact le_natAbs_valMinAbs_intCast (by rw [hp]; exact hx) h1 (by rw [hp]; exact h2)
  exact h3.trans (Finset.le_sup
    (f := fun i => (((Y + siteOfCoords F.top x : F.Cell) i - Y i).valMinAbs).natAbs) (Finset.mem_univ p))
theorem abs_le_cellSupDist_add_siteOfCoords (Y : F.Cell) (x : Fin 4 → ℤ) (p : Fin 4)
    (hx : 2 * |x p| < F.extent p) : |x p| ≤ cellSupDist Y (Y + siteOfCoords F.top x) := by
  rw [cellSupDist_comm]
  have hp : F.period F.top p = F.extent p := period_top p
  have e : ((Y + siteOfCoords F.top x : F.Cell) p - Y p) = ((x p : ℤ) : ZMod (F.period F.top p)) := by
    simp [siteOfCoords]
  have h3 : (((Y + siteOfCoords F.top x : F.Cell) p - Y p).valMinAbs).natAbs = (x p).natAbs := by
    rw [e, valMinAbs_intCast_of_two_mul_abs_lt (by rw [hp]; exact hx)]
  have h4 : (((Y + siteOfCoords F.top x : F.Cell) p - Y p).valMinAbs).natAbs ≤
      cellSupDist (Y + siteOfCoords F.top x) Y :=
    Finset.le_sup (f := fun i => (((Y + siteOfCoords F.top x : F.Cell) i - Y i).valMinAbs).natAbs)
      (Finset.mem_univ p)
  rw [h3] at h4
  rw [Int.abs_eq_natAbs]
  exact_mod_cast h4
theorem cellSupDist_add_siteOfCoords_le (Y : F.Cell) (x : Fin 4 → ℤ) {R : ℕ} (hR : ∀ i, |x i| ≤ (R : ℤ))
    (hs : ∀ i, 2 * R < F.extent i) : cellSupDist (Y + siteOfCoords F.top x) Y ≤ R := by
  unfold cellSupDist
  apply Finset.sup_le
  intro i _
  have hp : F.period F.top i = F.extent i := period_top i
  have e : ((Y + siteOfCoords F.top x : F.Cell) i - Y i) = ((x i : ℤ) : ZMod (F.period F.top i)) := by
    simp [siteOfCoords]
  have hRi := hR i
  have hsi := hs i
  rw [e, valMinAbs_intCast_of_two_mul_abs_lt (by rw [hp]; omega)]
  rw [Int.abs_eq_natAbs] at hRi
  omega
theorem siteOfCoords_add (j : ℕ) (a b : Fin 4 → ℤ) :
    siteOfCoords (F := F) j (a + b) = siteOfCoords j a + siteOfCoords j b := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_add <;> assumption
theorem siteOfCoords_sub (j : ℕ) (a b : Fin 4 → ℤ) :
    siteOfCoords (F := F) j (a - b) = siteOfCoords j a - siteOfCoords j b := by apply _root_.YangMills.Construction.BlockAverages.siteOfCoords_sub <;> assumption
theorem mixedBondDerivative_minimalAction {a : ℝ} {S : Finset F.Cell} {V : F.GaugeField F.top}
    (hsum : ∀ U : F.GaugeField F.top, ∑ Y ∈ S, minimalCellShare a S Y U = minimalAction a S F.top U)
    (hAn : ∀ Y, IsBondAnalyticAt (minimalCellShare a S Y) V) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) :
    mixedBondDerivative (minimalAction a S F.top) V c X =
      ∑ Y ∈ S, mixedBondDerivative (minimalCellShare a S Y) V c X := by
  unfold mixedBondDerivative
  have e : (fun σ : Fin k → ℝ => minimalAction a S F.top (rotatedField (BlockAverages.bondSpread c X σ) V)) =
      fun σ => ∑ Y ∈ S, minimalCellShare a S Y (rotatedField (BlockAverages.bondSpread c X σ) V) :=
    funext fun σ => (hsum _).symm
  rw [e, iteratedFDeriv_fun_sum_apply fun Y _ => (hAn Y k c X).contDiffAt]
  simp only [ContinuousMultilinearMap.sum_apply]
theorem derivativeScale_nonneg {s : ℝ} (hs : 0 ≤ s) (k : ℕ) : 0 ≤ derivativeScale s k := by
  unfold derivativeScale
  split_ifs <;> positivity
theorem abs_mixedBondDerivative_minimalCellShare_le {a δ s : ℝ} {N : ℕ → ℝ} {S : Finset F.Cell}
    {V : F.GaugeField F.top} (h : HasRegularCellShares a δ s N S V) (Y : F.Cell) {j : ℕ}
    (c : Fin (j + 1) → F.Site F.top × Fin 4) (X : Fin (j + 1) → imaginaryQuaternions) (hX : AreUnitVectors X) :
    |mixedBondDerivative (minimalCellShare a S Y) V c X| ≤
      derivativeScale s (j + 1) * N (j + 1) * Real.exp (-δ * bondListDistance Y c) := by
  obtain ⟨-, -, -, -, -, -, h7, -, h9⟩ := h
  cases j with
  | zero =>
    have h10 := h9 Y c X hX
    have e : derivativeScale s (0 + 1) = s := by simp [derivativeScale]
    have e2 : N (0 + 1) = N 1 := rfl
    rw [e, e2, mul_comm s]
    exact h10
  | succ j =>
    have := h7 Y (j + 1 + 1) c X (by omega) hX
    simpa [derivativeScale] using this
theorem abs_mixedBondDerivative_far_le {a δ s : ℝ} {N : ℕ → ℝ} {V : F.GaugeField F.top} (hδ : 0 < δ)
    (hs : 0 ≤ s) (hN : ∀ k, 0 < N k) (hA : HasRegularCellShares a δ s N (finiteCells F) V) {j : ℕ}
    (c : Fin (j + 1) → F.Site F.top × Fin 4) (X : Fin (j + 1) → imaginaryQuaternions) (hX : AreUnitVectors X)
    (m : ℝ) (Y : F.Cell) (hY : m ≤ 2 * (cellSupDist Y (c 0).1 : ℝ)) :
    |mixedBondDerivative (minimalCellShare a (finiteCells F) Y) V c X| ≤
      (derivativeScale s (j + 1) * N (j + 1) * Real.exp (-(δ / 4 * m))) *
        Real.exp (-(δ / 2 * cellSupDist Y (c 0).1)) := by
  refine (abs_mixedBondDerivative_minimalCellShare_le hA Y c X hX).trans ?_
  have hl : cellSupDist Y (c 0).1 ≤ bondListDistance Y c :=
    Finset.le_sup (f := fun l => cellSupDist Y (c l).1) (Finset.mem_univ 0)
  have hlr : (cellSupDist Y (c 0).1 : ℝ) ≤ bondListDistance Y c := by exact_mod_cast hl
  have hB : 0 ≤ derivativeScale s (j + 1) * N (j + 1) :=
    mul_nonneg (derivativeScale_nonneg hs _) (hN _).le
  rw [mul_assoc (derivativeScale s (j + 1) * N (j + 1)), ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left ?_ hB
  rw [Real.exp_le_exp]
  nlinarith
theorem le_bondListDistance_of_not_within (Y : F.Cell) {j : ℕ} (c : Fin (j + 1) → F.Site F.top × Fin 4)
    (l : Fin (j + 1)) (x : Fin 4 → ℤ) (hc : (c l).1 = Y + siteOfCoords F.top x) (i : Fin 4) {r₁ : ℕ}
    (hb : ¬ BondWithinRadius r₁ (x, i)) (hx : ∀ p, |x p| + r₁ < F.extent p) :
    r₁ ≤ bondListDistance Y c := by
  have hex : ∃ p, (r₁ : ℤ) ≤ |x p| := by
    by_contra hcon
    push_neg at hcon
    apply hb
    refine ⟨fun p => (hcon p).le, fun p => ?_⟩
    have h1 := hcon p
    simp only [Pi.add_apply]
    by_cases hp : p = i
    · subst hp
      simp only [Pi.single_eq_same]
      rcases abs_cases (x p) with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
        rcases abs_cases (x p + 1) with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;> omega
    · simp only [Pi.single_eq_of_ne hp, add_zero]
      exact h1.le
  obtain ⟨p, hp⟩ := hex
  have h1 := hx p
  have h2 : r₁ ≤ cellSupDist Y (Y + siteOfCoords F.top x) :=
    le_cellSupDist_add_siteOfCoords Y x p (by omega) hp (by omega)
  have h3 : cellSupDist Y (c l).1 ≤ bondListDistance Y c :=
    Finset.le_sup (f := fun l => cellSupDist Y (c l).1) (Finset.mem_univ l)
  rw [hc] at h3
  exact h2.trans h3
def TorusSumsCompare (β M : ℝ) : Prop :=
  ∀ (F F' : BlockFrame) (G : F.Cell → ℝ) (G' : F'.Cell → ℝ) (z : F.Cell) (z' : F'.Cell) (R : ℕ) (T A : ℝ),
    (∀ i, 2 ≤ F.extent i) → (∀ i, 2 ≤ F'.extent i) → (∀ i, 2 * R < F.extent i) → (∀ i, 2 * R < F'.extent i) →
    0 ≤ T → 0 ≤ A →
    (∀ h : Fin 4 → ℤ, (∀ i, |h i| ≤ (R : ℤ)) →
      |G (z + siteOfCoords F.top h) - G' (z' + siteOfCoords F'.top h)| ≤
        T * Real.exp (-(β * cellSupDist (z + siteOfCoords F.top h) z))) →
    (∀ Y, R < cellSupDist Y z → |G Y| ≤ A * Real.exp (-(β * cellSupDist Y z))) →
    (∀ Y, R < cellSupDist Y z' → |G' Y| ≤ A * Real.exp (-(β * cellSupDist Y z'))) →
    |∑ Y ∈ finiteCells F, G Y - ∑ Y ∈ finiteCells F', G' Y| ≤ (T + 2 * A) * M
theorem abs_sum_sub_sum_le {L : ℕ} {F' : BlockFrame} {a δ s M : ℝ} {N : ℕ → ℝ} {V : F.GaugeField F.top}
    {V' : F'.GaugeField F'.top} (hδ : 0 < δ) (hs : 0 ≤ s) (hN : ∀ k, 0 < N k) (hM : 0 < M)
    (hcmp : TorusSumsCompare (δ / 2) M) (hF : IsBlockTorus L F) (hF' : IsBlockTorus L F')
    (hA : HasRegularCellShares a δ s N (finiteCells F) V) (hA' : HasRegularCellShares a δ s N (finiteCells F') V')
    (hloc : ∀ (Y : F.Cell) (Y' : F'.Cell) (r' : ℕ), AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r' →
      HasComparableCellShares a δ s N (finiteCells F) V (finiteCells F') V' Y Y' r')
    {Y₀ : F.Cell} {Y₀' : F'.Cell} {r : ℕ} (hag : AgreeOnBall (finiteCells F) V (finiteCells F') V' Y₀ Y₀' r)
    {j : ℕ} (e : Fin (j + 1) → (Fin 4 → ℤ) × Fin 4) (X : Fin (j + 1) → imaginaryQuaternions)
    (he : ∀ l, BondWithinRadius r (e l)) (hX : AreUnitVectors X) :
    |∑ Y ∈ finiteCells F, mixedBondDerivative (minimalCellShare a (finiteCells F) Y) V (offsetBonds Y₀ e) X -
        ∑ Y ∈ finiteCells F', mixedBondDerivative (minimalCellShare a (finiteCells F') Y) V' (offsetBonds Y₀' e) X| ≤
      4 * M * (derivativeScale s (j + 1) * N (j + 1)) *
        Real.exp (-(δ / 4 * ((r : ℝ) - cellSupDist Y₀ (Y₀ + siteOfCoords F.top (e 0).1)))) := by
  obtain ⟨hsd, hsd', -, hV⟩ := hag
  have hside : ∀ i, 2 * r + 2 < F.extent i := fun i => by
    rcases hsd i with h | h
    · have := sixtyFour_le_extent hF i
      omega
    · exact h
  have hside' : ∀ i, 2 * r + 2 < F'.extent i := fun i => by
    rcases hsd' i with h | h
    · have := sixtyFour_le_extent hF' i
      omega
    · exact h
  set u₀ : Fin 4 → ℤ := (e 0).1 with hu₀
  have hu₀r : ∀ i, |u₀ i| ≤ (r : ℤ) := (he 0).1
  set d₀ : ℕ := cellSupDist Y₀ (Y₀ + siteOfCoords F.top u₀) with hd₀
  have hd₀r : d₀ ≤ r := by
    rw [hd₀, cellSupDist_comm]
    exact cellSupDist_add_siteOfCoords_le Y₀ u₀ hu₀r fun i => by
      have := hside i
      omega
  have hu₀d : ∀ i, |u₀ i| ≤ (d₀ : ℤ) := fun i =>
    abs_le_cellSupDist_add_siteOfCoords Y₀ u₀ i (by
      have h1 := hu₀r i
      have h2 := hside i
      omega)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, r = d₀ + m := ⟨r - d₀, by omega⟩
  set R : ℕ := m / 2 with hR
  set r₁ : ℕ := m - R with hr₁
  have hmR : 2 * R ≤ m := by omega
  have hmR2 : m ≤ 2 * (R + 1) := by omega
  have hmr : (r : ℝ) - d₀ = m := by
    rw [hm]
    push_cast
    ring
  rw [hmr]
  set B : ℝ := derivativeScale s (j + 1) * N (j + 1) with hB
  have hB0 : 0 ≤ B := mul_nonneg (derivativeScale_nonneg hs _) (hN _).le
  set E : ℝ := Real.exp (-(δ / 4 * (m : ℝ))) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  set z : F.Cell := Y₀ + siteOfCoords F.top u₀ with hz
  set z' : F'.Cell := Y₀' + siteOfCoords F'.top u₀ with hz'
  have hc0 : (offsetBonds Y₀ e 0).1 = z := rfl
  have hc0' : (offsetBonds Y₀' e 0).1 = z' := rfl
  refine (hcmp F F' (fun Y => mixedBondDerivative (minimalCellShare a (finiteCells F) Y) V (offsetBonds Y₀ e) X)
    (fun Y => mixedBondDerivative (minimalCellShare a (finiteCells F') Y) V' (offsetBonds Y₀' e) X) z z' R
    (2 * B * E) (B * E) (two_le_extent hF) (two_le_extent hF')
    (fun i => by
      have := hside i
      omega)
    (fun i => by
      have := hside' i
      omega)
    (mul_nonneg (mul_nonneg (by norm_num) hB0) hE0) (mul_nonneg hB0 hE0) ?_ ?_ ?_).trans (le_of_eq ?_)
  · intro h hh
    set Yh : F.Cell := z + siteOfCoords F.top h with hYh
    set Yh' : F'.Cell := z' + siteOfCoords F'.top h with hYh'
    have hYe : Yh = Y₀ + siteOfCoords F.top (u₀ + h) := by
      rw [hYh, hz, siteOfCoords_add, add_assoc]
    have hYe' : Yh' = Y₀' + siteOfCoords F'.top (u₀ + h) := by
      rw [hYh', hz', siteOfCoords_add, add_assoc]
    have hr₁r : r₁ ≤ r := by omega
    have hsum : d₀ + R + r₁ = r := by omega
    have hagree : AgreeOnBall (finiteCells F) V (finiteCells F') V' Yh Yh' r₁ := by
      refine ⟨fun i => Or.inr (by have := hside i; omega), fun i => Or.inr (by have := hside' i; omega),
        fun _ _ => ⟨fun _ => mem_finiteCells (two_le_extent hF') _, fun _ => mem_finiteCells (two_le_extent hF) _⟩, ?_⟩
      intro b hb
      have hin : BondWithinRadius r (u₀ + h + b.1, b.2) := by
        constructor
        · intro p
          have h1 := hu₀d p
          have h2 := hh p
          have h3 := hb.1 p
          simp only [Pi.add_apply]
          rcases abs_cases (u₀ p) with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
            rcases abs_cases (h p) with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;>
            rcases abs_cases (b.1 p) with ⟨c1, c2⟩ | ⟨c1, c2⟩ <;>
            rcases abs_cases (u₀ p + h p + b.1 p) with ⟨d1, d2⟩ | ⟨d1, d2⟩ <;> omega
        · intro p
          have h1 := hu₀d p
          have h2 := hh p
          have h3 := hb.2 p
          simp only [Pi.add_apply] at h3 ⊢
          set q : ℤ := b.1 p + (Pi.single b.2 1 : Fin 4 → ℤ) p with hq
          have e1 : u₀ p + h p + b.1 p + (Pi.single b.2 1 : Fin 4 → ℤ) p = u₀ p + h p + q := by
            rw [hq]
            ring
          rw [e1]
          rcases abs_cases (u₀ p) with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
            rcases abs_cases (h p) with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;>
            rcases abs_cases q with ⟨c1, c2⟩ | ⟨c1, c2⟩ <;>
            rcases abs_cases (u₀ p + h p + q) with ⟨d1, d2⟩ | ⟨d1, d2⟩ <;> omega
      have := hV _ hin
      simp only at this
      rw [hYe, hYe', add_assoc, add_assoc, ← siteOfCoords_add, ← siteOfCoords_add]
      exact this
    set x : Fin (j + 1) → Fin 4 → ℤ := fun l => (e l).1 - (u₀ + h) with hx
    set e' : Fin (j + 1) → (Fin 4 → ℤ) × Fin 4 := fun l => (x l, (e l).2) with he'
    have hbonds : offsetBonds Yh e' = offsetBonds Y₀ e := by
      funext l
      simp only [offsetBonds, he', hx]
      rw [hYe, siteOfCoords_sub, siteOfCoords_add]
      congr 1
      abel
    have hbonds' : offsetBonds Yh' e' = offsetBonds Y₀' e := by
      funext l
      simp only [offsetBonds, he', hx]
      rw [hYe', siteOfCoords_sub, siteOfCoords_add]
      congr 1
      abel
    have hmain : |mixedBondDerivative (minimalCellShare a (finiteCells F) Yh) V (offsetBonds Y₀ e) X -
        mixedBondDerivative (minimalCellShare a (finiteCells F') Yh') V' (offsetBonds Y₀' e) X| ≤
        2 * B * Real.exp (-(δ * (r₁ : ℝ))) := by
      by_cases hall : ∀ l, BondWithinRadius r₁ (e' l)
      · have h1 := hloc Yh Yh' r₁ hagree (j + 1) e' X hall hX
        rw [hbonds, hbonds'] at h1
        refine h1.trans ?_
        have hcf : derivativeScale s (j + 1) * N (j + 1) = B := rfl
        rw [hcf]
        have h2 : Real.exp (-δ * (r₁ : ℝ)) = Real.exp (-(δ * (r₁ : ℝ))) := by
          congr 1
          ring
        rw [h2]
        have := Real.exp_pos (-(δ * (r₁ : ℝ)))
        nlinarith
      · push_neg at hall
        obtain ⟨l, hl⟩ := hall
        have hxb : ∀ p, |x l p| + r₁ < 2 * r + 2 := by
          intro p
          have h1 := (he l).1 p
          have h2 := hu₀d p
          have h3 := hh p
          simp only [hx, Pi.sub_apply, Pi.add_apply]
          rcases abs_cases ((e l).1 p) with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
            rcases abs_cases (u₀ p) with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;>
            rcases abs_cases (h p) with ⟨c1, c2⟩ | ⟨c1, c2⟩ <;>
            rcases abs_cases ((e l).1 p - (u₀ p + h p)) with ⟨d1, d2⟩ | ⟨d1, d2⟩ <;> omega
        have hd1 : r₁ ≤ bondListDistance Yh (offsetBonds Y₀ e) :=
          le_bondListDistance_of_not_within Yh (offsetBonds Y₀ e) l (x l)
            (by rw [← hbonds]; rfl) (e l).2 hl
            (fun p => by
              have h1 := hxb p
              have h2 := hside p
              omega)
        have hd2 : r₁ ≤ bondListDistance Yh' (offsetBonds Y₀' e) :=
          le_bondListDistance_of_not_within Yh' (offsetBonds Y₀' e) l (x l)
            (by rw [← hbonds']; rfl) (e l).2 hl
            (fun p => by
              have h1 := hxb p
              have h2 := hside' p
              omega)
        have b1 := abs_mixedBondDerivative_minimalCellShare_le hA Yh (offsetBonds Y₀ e) X hX
        have b2 := abs_mixedBondDerivative_minimalCellShare_le hA' Yh' (offsetBonds Y₀' e) X hX
        have hexp : ∀ n : ℕ, r₁ ≤ n → Real.exp (-δ * (n : ℝ)) ≤ Real.exp (-(δ * (r₁ : ℝ))) := by
          intro n hn
          rw [Real.exp_le_exp]
          have : (r₁ : ℝ) ≤ n := by exact_mod_cast hn
          nlinarith
        have c1 := mul_le_mul_of_nonneg_left (hexp _ hd1) hB0
        have c2 := mul_le_mul_of_nonneg_left (hexp _ hd2) hB0
        have := abs_sub (mixedBondDerivative (minimalCellShare a (finiteCells F) Yh) V (offsetBonds Y₀ e) X)
          (mixedBondDerivative (minimalCellShare a (finiteCells F') Yh') V' (offsetBonds Y₀' e) X)
        linarith
    refine hmain.trans ?_
    have hd : cellSupDist Yh z ≤ R := cellSupDist_add_siteOfCoords_le z h hh fun i => by
      have := hside i
      omega
    have hdr : (cellSupDist Yh z : ℝ) ≤ R := by exact_mod_cast hd
    have hd0 : (0 : ℝ) ≤ cellSupDist Yh z := Nat.cast_nonneg _
    have hmr1 : ((r₁ : ℕ) : ℝ) = (m : ℝ) - R := by
      rw [hr₁, Nat.cast_sub (by omega)]
    have hRm : 2 * (R : ℝ) ≤ m := by exact_mod_cast hmR
    rw [mul_assoc (2 * B), ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [Real.exp_le_exp, hmr1]
    nlinarith
  · intro Y hY
    have hYr : (m : ℝ) ≤ 2 * (cellSupDist Y z : ℝ) := by
      have : m ≤ 2 * cellSupDist Y z := by omega
      exact_mod_cast this
    exact abs_mixedBondDerivative_far_le hδ hs hN hA (offsetBonds Y₀ e) X hX m Y hYr
  · intro Y hY
    have hYr : (m : ℝ) ≤ 2 * (cellSupDist Y z' : ℝ) := by
      have : m ≤ 2 * cellSupDist Y z' := by omega
      exact_mod_cast this
    exact abs_mixedBondDerivative_far_le hδ hs hN hA' (offsetBonds Y₀' e) X hX m Y hYr
  · ring
theorem mul_exp_neg_le_mul_exp_neg {c C δ' δ x : ℝ} (hc : 0 ≤ c) (hC : c ≤ C) (hx : 0 ≤ x) (hδ : δ' ≤ δ) :
    c * Real.exp (-δ * x) ≤ C * Real.exp (-(δ' * x)) := by
  have h1 : Real.exp (-δ * x) ≤ Real.exp (-(δ' * x)) := by
    rw [Real.exp_le_exp]
    nlinarith
  calc c * Real.exp (-δ * x) ≤ c * Real.exp (-(δ' * x)) := mul_le_mul_of_nonneg_left h1 hc
    _ ≤ C * Real.exp (-(δ' * x)) := mul_le_mul_of_nonneg_right hC (Real.exp_pos _).le
theorem mul_exp_neg_le_mul_exp_neg' {c C δ' δ x : ℝ} (hc : 0 ≤ c) (hC : c ≤ C) (hx : 0 ≤ x) (hδ : δ' ≤ δ) :
    c * Real.exp (-(δ * x)) ≤ C * Real.exp (-(δ' * x)) := by
  have e : -(δ * x) = -δ * x := by ring
  rw [e]
  exact mul_exp_neg_le_mul_exp_neg hc hC hx hδ
section TorusWeight
variable {a δ ρ s Mw Q : ℝ} {N : ℕ → ℝ}
theorem mul_exp_neg_le_div_torusDecayFactor (hδ : 0 < δ) (hN : ∀ k, 0 < N k) (hMw : 1 ≤ Mw)
    (hM : ∀ x : ℝ, 0 ≤ x → Real.exp (-(δ / 2 * x)) ≤ Mw / BlockAverages.torusDecayFactor F.blockSide (δ / 4) x)
    (k : ℕ) (d D : ℝ) (hD0 : 0 ≤ D) (hD : D ≤ 2 * d) :
    N k * Real.exp (-δ * d) ≤ N k * Mw / BlockAverages.torusDecayFactor F.blockSide (δ / 4) D := by
  have e1 := exp_neg_le_of_le_two_mul δ hδ d D hD
  have e2 := hM D hD0
  have hk := hN k
  calc N k * Real.exp (-δ * d) ≤ N k * (Mw / BlockAverages.torusDecayFactor F.blockSide (δ / 4) D) := by
        gcongr
        exact e1.trans e2
    _ = _ := by ring
theorem hasTorusDerivativeDecay {S : Finset F.Cell} {V : F.GaugeField F.top} (hδ : 0 < δ) (hs : 0 ≤ s)
    (hN : ∀ k, 0 < N k) (hMw : 1 ≤ Mw) (hQ : 1 ≤ Q)
    (hM : ∀ x : ℝ, 0 ≤ x → Real.exp (-(δ / 2 * x)) ≤ Mw / BlockAverages.torusDecayFactor F.blockSide (δ / 4) x)
    (h3 : HasRegularCellShares a δ s N S V) (h4 : HasRegularCoordinates a δ ρ N S V) :
    HasTorusDerivativeDecay a (δ / 4) ρ s (fun k => N k * Mw * Q) S V := by
  have hMQ : ∀ k, N k * Mw ≤ N k * Mw * Q := fun k => by
    have := hN k
    have : 0 ≤ N k * Mw := by positivity
    nlinarith
  have hdec : ∀ (k : ℕ) (d D : ℝ), 0 ≤ D → D ≤ 2 * d →
      N k * Real.exp (-δ * d) ≤ N k * Mw * Q / BlockAverages.torusDecayFactor F.blockSide (δ / 4) D := by
    intro k d D hD0 hD
    refine (mul_exp_neg_le_div_torusDecayFactor hδ hN hMw hM k d D hD0 hD).trans ?_
    exact div_le_div_of_nonneg_right (hMQ k) (torusDecayFactor_pos _ _ _).le
  have hmaxD : ∀ {k : ℕ} (Y : F.Cell) (c : Fin k → F.Site F.top × Fin 4),
      max (bondListDiameter c : ℝ) (bondListDistance Y c : ℝ) ≤ 2 * (bondListDistance Y c : ℝ) := by
    intro k Y c
    apply max_le
    · exact_mod_cast bondListDiameter_le_two_mul Y c
    · have : (0 : ℝ) ≤ bondListDistance Y c := Nat.cast_nonneg _
      linarith
  have hmax0 : ∀ {k : ℕ} (Y : F.Cell) (c : Fin k → F.Site F.top × Fin 4),
      0 ≤ max (bondListDiameter c : ℝ) (bondListDistance Y c : ℝ) := by
    intro k Y c
    exact le_max_of_le_left (Nat.cast_nonneg _)
  obtain ⟨-, -, -, -, -, d1, d2, -, d3⟩ := h3
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k c X hk hX
    refine (d1 k c X hk hX).trans ?_
    exact hdec k _ _ (Nat.cast_nonneg _) (by nlinarith [Nat.cast_nonneg (α := ℝ) (bondListDiameter c)])
  · intro Y k c X hk hX
    refine (d2 Y k c X hk hX).trans ?_
    exact hdec k _ _ (hmax0 Y c) (hmaxD Y c)
  · intro Y c X hX
    refine (d3 Y c X hX).trans ?_
    dsimp only
    have hd : (0 : ℝ) ≤ bondListDistance Y c := Nat.cast_nonneg _
    have := hdec 1 (bondListDistance Y c) (bondListDistance Y c) hd (by linarith)
    calc N 1 * s * Real.exp (-δ * (bondListDistance Y c : ℝ)) =
          (N 1 * Real.exp (-δ * (bondListDistance Y c : ℝ))) * s := by ring
      _ ≤ (N 1 * Mw * Q / BlockAverages.torusDecayFactor F.blockSide (δ / 4) (bondListDistance Y c)) * s := by
          gcongr
      _ = _ := by ring
  · intro b hb k c X hk hX
    refine ((h4 b hb).2 k c X hk hX).trans ?_
    exact hdec k _ _ (hmax0 _ c) (hmaxD _ c)
theorem hasTorusComparison {F' : BlockFrame} {S : Finset F.Cell} {V : F.GaugeField F.top}
    {S' : Finset F'.Cell} {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell} {r : ℕ} (hδ : 0 < δ)
    (hs : 0 ≤ s) (hN : ∀ k, 0 < N k) (hMw : 1 ≤ Mw) (hQ : 1 ≤ Q) (hcf : ∀ k, derivativeScale s k ≤ Q)
    (hM : ∀ x : ℝ, 0 ≤ x → Real.exp (-(δ / 2 * x)) ≤ Mw / BlockAverages.torusDecayFactor F.blockSide (δ / 4) x)
    (l1 : HasComparableCellShares a δ s N S V S' V' Y Y' r)
    (l2 : HasComparableCoordinates a δ ρ s N S V S' V' Y Y' r) :
    HasTorusComparison a (δ / 4) ρ s (fun k => N k * Mw * Q) S V S' V' Y Y' r := by
  have hMQ : ∀ k, N k * Mw ≤ N k * Mw * Q := fun k => by
    have := hN k
    have : 0 ≤ N k * Mw := by positivity
    nlinarith
  refine ⟨?_, ?_⟩
  · intro k h X hb hX
    refine (l1 k h X hb hX).trans ?_
    dsimp only
    have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg _
    have e := mul_exp_neg_le_div_torusDecayFactor hδ hN hMw hM k r r hr (by linarith)
    have hNe : 0 ≤ N k * Real.exp (-δ * (r : ℝ)) := by
      have := hN k
      positivity
    have hQ0 : 0 ≤ Q := by linarith
    calc derivativeScale s k * N k * Real.exp (-δ * (r : ℝ)) =
          derivativeScale s k * (N k * Real.exp (-δ * (r : ℝ))) := by ring
      _ ≤ Q * (N k * Real.exp (-δ * (r : ℝ))) := mul_le_mul_of_nonneg_right (hcf k) hNe
      _ ≤ Q * (N k * Mw / BlockAverages.torusDecayFactor F.blockSide (δ / 4) r) :=
          mul_le_mul_of_nonneg_left e hQ0
      _ = _ := by ring
  · intro h o i ho hb hIn hd1 hd2
    refine ((l2 h o i ho hb hIn hd2).1).trans ?_
    dsimp only
    set x : ℝ := (r : ℝ) - cellSupDist Y (enclosingCell (fineBondAt Y h o i).1) with hx
    have hx0 : 0 ≤ x := by
      rw [hx, sub_nonneg]
      exact_mod_cast hd1
    have e := mul_exp_neg_le_div_torusDecayFactor hδ hN hMw hM 0 x x hx0 (by linarith)
    have e2 : N 0 * Real.exp (-δ * x) ≤ N 0 * Mw * Q / BlockAverages.torusDecayFactor F.blockSide (δ / 4) x :=
      e.trans (div_le_div_of_nonneg_right (hMQ 0) (torusDecayFactor_pos _ _ _).le)
    calc N 0 * s * Real.exp (-δ * x) = (N 0 * Real.exp (-δ * x)) * s := by ring
      _ ≤ (N 0 * Mw * Q / BlockAverages.torusDecayFactor F.blockSide (δ / 4) x) * s :=
          mul_le_mul_of_nonneg_right e2 hs
      _ = _ := by ring
end TorusWeight
end AdmissibleParameters
set_option maxHeartbeats 2000000 in
open AdmissibleParameters BlockOffsets in
theorem AdmissibleParameters.exists_admissible (h1 : ChartedFieldContourBound)
    (h2 : ChartDeterminedByField) (h3 : DecayingSumsClose)
    (h4 : sumCellSharesEqAction) : AdmissibleParametersExist := by
  intro a δ₁ L lam ρA σA cg N ha hL hC
  obtain ⟨hδ, hδ8, hlam, hρ, hρ1, hσ, hcg, hN, hmain⟩ := hC
  have hL1 : 1 ≤ L := hL.pos
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  obtain ⟨Mw, hMw1, hMw⟩ := exists_exp_le_div_torusDecayFactor δ₁ hδ L hL1
  obtain ⟨M, hM, -, hcmp⟩ := h3 (δ₁ / 2) (by positivity)
  have hcmp' : TorusSumsCompare (δ₁ / 2) M := fun F F' G G' z z' R T A => hcmp F F' G G' z z' R T A
  set Q : ℝ := max 1 (σA ^ 2) + max 1 σA with hQ
  have hQ1 : 1 ≤ Q := by
    have e1 := le_max_left 1 (σA ^ 2)
    have e2 := le_max_left 1 σA
    linarith
  set N' : ℕ → ℝ := fun k => N k * Mw * Q with hN'
  have hN'pos : ∀ k, 0 < N' k := fun k => by
    have := hN k
    simp only [hN']
    positivity
  set C : ℝ := 1 + N 0 + 5 * (L : ℝ) * N 0 with hCdef
  have hN0 := hN 0
  have hC1 : 1 ≤ C := by
    have : 0 ≤ 5 * (L : ℝ) * N 0 := by positivity
    simp only [hCdef]
    linarith
  have hC0 : 0 < C := by linarith
  set s₀ : ℝ := min (σA / 16) (min (ρA / (2 * C)) (min (1 / (32 * C)) (min (1 / (64 * (L : ℝ) * C)) 1)))
    with hs₀
  have s1 : s₀ ≤ σA / 16 := min_le_left _ _
  have s2 : s₀ ≤ ρA / (2 * C) := (min_le_right _ _).trans (min_le_left _ _)
  have s3 : s₀ ≤ 1 / (32 * C) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have s4 : s₀ ≤ 1 / (64 * (L : ℝ) * C) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have s5 : s₀ ≤ 1 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hs₀pos : 0 < s₀ := by
    refine lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity) one_pos)))
  have hs₀σ : s₀ ≤ σA := by linarith
  set P : ℝ := 4 * M + 1 with hP
  have hP1 : 1 ≤ P := by
    simp only [hP]
    linarith
  set K : ℝ := P * (N 0 + N 1) with hK
  set Kk : ℕ → ℝ := fun k => P * (N 0 + N 1 + N 2 + N 3 + N k) with hKk
  have hKkpos : ∀ k, 0 < Kk k := fun k => by
    have a0 := hN 0
    have a1 := hN 1
    have a2 := hN 2
    have a3 := hN 3
    have a4 := hN k
    simp only [hKk]
    positivity
  have hKpos : 0 < K := by
    have a1 := hN 1
    simp only [hK]
    positivity
  have hNKk : ∀ k, N k ≤ Kk k := fun k => by
    have a0 := hN 0
    have a1 := hN 1
    have a2 := hN 2
    have a3 := hN 3
    have a4 := hN k
    simp only [hKk]
    nlinarith
  have hNK3 : ∀ k, k ≤ 3 → N k ≤ Kk 3 := by
    intro k hk
    have a0 := hN 0
    have a1 := hN 1
    have a2 := hN 2
    have a3 := hN 3
    simp only [hKk]
    interval_cases k <;> nlinarith
  have hK0 : N 0 ≤ K := by
    have a1 := hN 1
    have e1 : N 0 + N 1 ≤ P * (N 0 + N 1) := le_mul_of_one_le_left (by linarith) hP1
    simp only [hK]
    linarith
  have hK1 : 4 * M * N 1 ≤ K := by
    have a1 := hN 1
    have e1 : 4 * M * N 1 ≤ P * N 1 := mul_le_mul_of_nonneg_right (by simp only [hP]; linarith) a1.le
    have e2 : P * N 1 ≤ P * (N 0 + N 1) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    simp only [hK]
    linarith
  have hKk4 : ∀ (k : ℕ) (c : ℝ), c ≤ N k → 4 * M * c ≤ Kk k := by
    intro k c hc
    have a0 := hN 0
    have a1 := hN 1
    have a2 := hN 2
    have a3 := hN 3
    have a4 := hN k
    have e1 : 4 * M * c ≤ 4 * M * N k := mul_le_mul_of_nonneg_left hc (by positivity)
    have e2 : 4 * M * N k ≤ P * N k := mul_le_mul_of_nonneg_right (by simp only [hP]; linarith) a4.le
    have e3 : P * N k ≤ P * (N 0 + N 1 + N 2 + N 3 + N k) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    simp only [hKk]
    linarith
  have hcfQ : ∀ s, 0 ≤ s → s ≤ σA → ∀ k, derivativeScale s k ≤ Q := by
    intro s hs hsσ k
    have hs2 : s ^ 2 ≤ σA ^ 2 := pow_le_pow_left₀ hs hsσ 2
    have a1 := le_max_right 1 (σA ^ 2)
    have a2 := le_max_left 1 (σA ^ 2)
    have a3 := le_max_right 1 σA
    have a4 := le_max_left 1 σA
    unfold derivativeScale
    split_ifs <;> linarith
  have hcf1 : ∀ s, 0 ≤ s → s ≤ 1 → ∀ k, derivativeScale s k ≤ 1 := by
    intro s hs hs1 k
    unfold derivativeScale
    split_ifs
    · nlinarith
    · exact hs1
    · exact le_rfl
  have hcl := fun (F : BlockFrame) (s : ℝ) (V : F.GaugeField F.top) (hF : IsBlockTorus L F) (hs : 0 < s)
    (hsσ : s ≤ σA) (hc : IsSmallCurvature s V) => hmain F 1024 (finiteCells F) hF.1
      (isAdmissibleAmbient_of_isBlockTorus hF) le_rfl (finiteCells_isOrthantRegular hF _) s V hs hsσ
      (isCold_of_isSmallCurvature hc _)
  refine ⟨⟨δ₁, δ₁ / 4, lam, ρA, σA, cg, s₀, δ₁ / 64, δ₁, K, C, N, N', Kk⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  refine ⟨⟨hδ, by positivity, hlam, hσ, hcg, hN, hN'pos⟩, ⟨hδ8, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · change 2 ^ 6 * (δ₁ / 64) ≤ δ₁
    linarith
  · change 16 * s₀ ≤ σA
    linarith
  · change 2 * C * s₀ ≤ ρA
    have := (le_div_iff₀ (by positivity)).mp s2
    linarith
  · change 2 * C * s₀ ≤ 1 / 16
    have := (le_div_iff₀ (by positivity)).mp s3
    linarith
  · change 64 * (L : ℝ) * C * s₀ ≤ 1
    have := (le_div_iff₀ (by positivity)).mp s4
    linarith
  · intro F s V hF hs hsσ hc
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hcl F s V hF hs hsσ hc
    have hMF : ∀ x : ℝ, 0 ≤ x →
        Real.exp (-(δ₁ / 2 * x)) ≤ Mw / BlockAverages.torusDecayFactor F.blockSide (δ₁ / 4) x := by
      rw [hF.1]
      exact hMw
    refine ⟨c1, c2, c3, c4, hasTorusDerivativeDecay hδ hs.le hN hMw1 hQ1 hMF c3 c4,
      fun W => c5 s le_rfl hsσ W, ?_⟩
    intro F' V' Y Y' r hL' ht hcub hc' hag
    have hF' : IsBlockTorus L F' := ⟨hL'.trans hF.1, hcub⟩
    obtain ⟨l1, l2⟩ := c6 F' (finiteCells F') V' Y Y' r hF'.1 ht (isAdmissibleAmbient_of_isBlockTorus hF')
      (finiteCells_isOrthantRegular hF' _) (isCold_of_isSmallCurvature hc' _) hag
    exact ⟨l1, l2, hasTorusComparison hδ hs.le hN hMw1 hQ1 (hcfQ s hs.le hsσ) hMF l1 l2⟩
  · refine ⟨⟨hρ, hρ1, hs₀pos, by positivity, by linarith, hKpos, hC1, hKkpos⟩, ?_⟩
    intro F s V hF hs hss hc
    have hsσ : s ≤ σA := hss.trans hs₀σ
    have hs1 : s ≤ 1 := hss.trans s5
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hcl F s V hF hs hsσ hc
    have hLF : Odd F.blockSide := by
      rw [hF.1]
      exact hL
    have hsides := two_le_extent hF
    obtain ⟨lc1, lc2⟩ := minimizingCoordinates_spec h2 hLF hsides hρ1 c1
    have hsumF := fun U : F.GaugeField F.top => (h4 F a (fun _ _ => 0) U (by linarith) hLF hsides).1
    have an2 : ∀ Y, IsBondAnalyticAt (minimalCellShare a (finiteCells F) Y) V := by
      have c3' := c3
      obtain ⟨-, an2, -⟩ := c3'
      exact an2
    have hall : ∀ (cc : F.Site F.top × Fin 4) (u : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)),
        u ∈ centredCube F.blockSide →
        ‖contourHolonomyDefect (torusMinimizingField a ρA V) V cc u π - 1‖ ≤ C * s := by
      intro cc u π hu
      have r1 := h1 F (minimizingCoordinates a (finiteCells F) V ρA) V (N 0 * s) hLF hsides (by positivity) lc2
        cc u π hu
      refine r1.trans ?_
      rw [hF.1]
      have : 5 * (L : ℝ) * (N 0 * s) = (5 * (L : ℝ) * N 0) * s := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (by simp only [hCdef]; linarith) hs.le
    refine ⟨lc1, ⟨?_, ?_⟩, ?_, ?_⟩
    · intro b hb
      refine (lc2 b hb).trans (mul_le_mul_of_nonneg_right ?_ hs.le)
      simp only [hCdef]
      have : 0 ≤ 5 * (L : ℝ) * N 0 := by positivity
      linarith
    · intro cc u π hu
      exact ⟨hall cc u π hu, one_sub_le_norm_contourAverage hLF _ V cc (hall cc)⟩
    · intro b hb k c X hk hX
      have r1 := (c4 b hb).2 k c X hk hX
      exact r1.trans (mul_exp_neg_le_mul_exp_neg (hN k).le (hNKk k) (Nat.cast_nonneg _) le_rfl)
    · intro F' V' Y Y' r hF' ht hc' hag
      have hLF' : Odd F'.blockSide := by
        rw [hF'.1]
        exact hL
      have hsides' := two_le_extent hF'
      obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hcl F' s V' hF' hs hsσ hc'
      have hsumF' := fun U : F'.GaugeField F'.top =>
        (h4 F' a (fun _ _ => 0) U (by linarith) hLF' hsides').1
      have an2' : ∀ Y, IsBondAnalyticAt (minimalCellShare a (finiteCells F') Y) V' := by
        have e3' := e3
        obtain ⟨-, an2', -⟩ := e3'
        exact an2'
      have hloc := fun (Y : F.Cell) (Y' : F'.Cell) (r' : ℕ)
          (ag : AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r') =>
        (c6 F' (finiteCells F') V' Y Y' r' hF'.1 ht (isAdmissibleAmbient_of_isBlockTorus hF')
          (finiteCells_isOrthantRegular hF' _) (isCold_of_isSmallCurvature hc' _) ag)
      have hlocS := fun (Y : F.Cell) (Y' : F'.Cell) (r' : ℕ)
          (ag : AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r') => (hloc Y Y' r' ag).1
      have hlocC := (hloc Y Y' r hag).2
      have hsideF : ∀ i, 2 * r + 2 < F.extent i := fun i => by
        rcases hag.1 i with h | h
        · have := sixtyFour_le_extent hF i
          omega
        · exact h
      have hdist : ∀ u : Fin 4 → ℤ, (∀ i, |u i| ≤ (r : ℤ)) →
          (0 : ℝ) ≤ (r : ℝ) - cellSupDist Y (Y + siteOfCoords F.top u) := by
        intro u hu
        rw [sub_nonneg, cellSupDist_comm]
        exact_mod_cast cellSupDist_add_siteOfCoords_le Y u hu fun i => by
          have := hsideF i
          omega
      have hcoord : ∀ (h o : Fin 4 → ℤ) (i : Fin 4), IsFineBondWithinRadius Y r h o i →
          0 ≤ (r : ℝ) - cellSupDist Y (enclosingCell (fineBondAt Y h o i).1) := by
        intro h o i hb
        rw [sub_nonneg]
        exact_mod_cast hb.2.2.2.1
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro h o i hb
        obtain ⟨ho, hch, hin, hd1, hd2⟩ := id hb
        have r1 := (hlocC h o i ho hch hin hd2).1
        have hKs : N 0 * s ≤ K * s := mul_le_mul_of_nonneg_right hK0 hs.le
        exact r1.trans (mul_exp_neg_le_mul_exp_neg (by positivity) hKs (hcoord h o i hb) (by linarith))
      · intro b X hb hX
        have r1 := abs_sum_sub_sum_le (j := 0) hδ hs.le hN hM hcmp' hF hF' c3 e3 hlocS hag (fun _ => b) X
          (fun _ => hb) hX
        have a1 := mixedBondDerivative_minimalAction hsumF an2 (offsetBonds Y fun _ : Fin 1 => b) X
        have a2 := mixedBondDerivative_minimalAction hsumF' an2' (offsetBonds Y' fun _ : Fin 1 => b) X
        change |mixedBondDerivative (minimalAction a (finiteCells F) F.top) V (offsetBonds Y fun _ : Fin 1 => b) X -
          mixedBondDerivative (minimalAction a (finiteCells F') F'.top) V' (offsetBonds Y' fun _ : Fin 1 => b) X| ≤ _
        rw [a1, a2]
        refine r1.trans ?_
        have hcf : derivativeScale s (0 + 1) = s := by simp [derivativeScale]
        rw [hcf]
        have a3 := hN 1
        have hx := hdist b.1 hb.1
        have hc0 : 4 * M * (s * N (0 + 1)) ≤ K * s := by
          have e0 : N (0 + 1) = N 1 := rfl
          rw [e0]
          calc 4 * M * (s * N 1) = (4 * M * N 1) * s := by ring
            _ ≤ K * s := mul_le_mul_of_nonneg_right hK1 hs.le
        exact mul_exp_neg_le_mul_exp_neg' (by
          have : 0 ≤ N (0 + 1) := (hN _).le
          positivity) hc0 hx (by linarith)
      · intro h o i k e X hb hk1 hk3 hbox hX
        obtain ⟨ho, hch, hin, hd1, hd2⟩ := id hb
        have r1 := (hlocC h o i ho hch hin hd2).2 k e X hk1 hbox hX
        have eN : ‖bondDeriv (torusCoordinate a ρA (fineBondAt Y h o i)) V (bondsAt Y e) X -
            bondDeriv (torusCoordinate a ρA (fineBondAt Y' h o i)) V' (bondsAt Y' e) X‖ =
            ‖((mixedBondDerivative (minimizingBondCoordinate a ρA (finiteCells F) (fineBondAt Y h o i)) V
                (offsetBonds Y e) X : imaginaryQuaternions) : ℍ[ℝ]) -
              ((mixedBondDerivative (minimizingBondCoordinate a ρA (finiteCells F') (fineBondAt Y' h o i)) V'
                (offsetBonds Y' e) X : imaginaryQuaternions) : ℍ[ℝ])‖ := rfl
        rw [eN]
        exact r1.trans (mul_exp_neg_le_mul_exp_neg (hN k).le (hNK3 k hk3) (hcoord h o i hb) (by linarith))
      · intro _ k e X hk hbox hX
        have r1 := (hloc Y Y' r hag).1 k e X hbox hX
        refine r1.trans ?_
        have hcN : derivativeScale s k * N k ≤ Kk 3 :=
          (mul_le_of_le_one_left (hN k).le (hcf1 s hs.le hs1 k)).trans (hNK3 k hk)
        exact mul_exp_neg_le_mul_exp_neg (mul_nonneg (derivativeScale_nonneg hs.le k) (hN k).le) hcN
          (Nat.cast_nonneg _) (by linarith)
      · intro k e X hbox hX
        have r1 := abs_sum_sub_sum_le (j := k) hδ hs.le hN hM hcmp' hF hF' c3 e3 hlocS hag e X hbox hX
        have a1 := mixedBondDerivative_minimalAction hsumF an2 (offsetBonds Y e) X
        have a2 := mixedBondDerivative_minimalAction hsumF' an2' (offsetBonds Y' e) X
        change |mixedBondDerivative (minimalAction a (finiteCells F) F.top) V (offsetBonds Y e) X -
          mixedBondDerivative (minimalAction a (finiteCells F') F'.top) V' (offsetBonds Y' e) X| ≤ _
        rw [a1, a2]
        refine r1.trans ?_
        have hx := hdist (e 0).1 (hbox 0).1
        have hcN : derivativeScale s (k + 1) * N (k + 1) ≤ N (k + 1) :=
          mul_le_of_le_one_left (hN _).le (hcf1 s hs.le hs1 _)
        have hc0 : 0 ≤ derivativeScale s (k + 1) * N (k + 1) :=
          mul_nonneg (derivativeScale_nonneg hs.le _) (hN _).le
        have hc1 : 4 * M * (derivativeScale s (k + 1) * N (k + 1)) ≤ Kk (k + 1) := hKk4 _ _ hcN
        exact mul_exp_neg_le_mul_exp_neg' (by positivity) hc1 hx (by linarith)
end ColdStepAtMirrorFrames
end YangMills.Construction
end
