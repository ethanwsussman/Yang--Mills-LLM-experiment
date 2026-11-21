import YangMills.Construction.ColdChainAtEveryLevel.DifferencesAreNearlyFlatProof
import YangMills.Construction.ColdChainAtEveryLevel.FormOfTheSliceAgainstItsCurl
import YangMills.Construction.ColdChainAtEveryLevel.SliceNormWithTheRadius
import YangMills.Construction.HoleBesideASecondHole.CoordinatesOfAFieldNearATopProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
namespace SliceNorm
variable {F : BlockFrame}
theorem natAbs_valMinAbs_intCast_le (n : ℕ) (d : ℤ) : ((d : ZMod n).valMinAbs).natAbs ≤ d.natAbs := by apply _root_.YangMills.Construction.BlockWeights.natAbs_valMinAbs_intCast_le <;> assumption
theorem siteOfCoords_add {j : ℕ} (a b : Fin 4 → ℤ) :
    siteOfCoords (F := F) j a + siteOfCoords j b = siteOfCoords j fun i => a i + b i := by apply _root_.YangMills.Construction.BlockLines.siteOfCoords_add_fun <;> assumption
theorem siteCoords_siteOfCoords {j : ℕ} (a : Fin 4 → ℤ) (i : Fin 4) :
    siteCoords (siteOfCoords (F := F) j a) i = a i % (F.period j i : ℤ) := by apply _root_.YangMills.Construction.BlockLines.siteCoords_siteOfCoords <;> assumption
theorem period_eq {j : ℕ} (i : Fin 4) :
    (F.period j i : ℤ) = (F.extent i : ℤ) * (F.blockSide : ℤ) ^ (F.top - j) := by
  simp [BlockFrame.period]
theorem blockSide_pow_sub_succ {j : ℕ} (hj : j < F.top) :
    (F.blockSide : ℤ) ^ (F.top - j) = F.blockSide * (F.blockSide : ℤ) ^ (F.top - (j + 1)) := by apply _root_.YangMills.Construction.BlockLines.blockSide_pow_sub_eq <;> assumption
theorem mem_centredCube (M : ℕ) (h : Fin 4 → ℤ) :
    h ∈ centredCube M ↔ ∀ i, -(((M : ℤ) - 1) / 2) ≤ h i ∧ h i ≤ ((M : ℤ) - 1) / 2 := by apply _root_.YangMills.Construction.LumpContours.CutAction.mem_centredCube <;> assumption
theorem odd_pow_half (hodd : Odd F.blockSide) (e : ℕ) : ∃ k : ℕ, F.blockSide ^ e = 2 * k + 1 ∧
    (((F.blockSide ^ e : ℕ) : ℤ) - 1) / 2 = k ∧ (F.blockSide : ℤ) ^ e = 2 * (k : ℤ) + 1 := by apply _root_.YangMills.Construction.BlockLines.odd_pow_eq_two_mul_add_one <;> assumption
def halfSide (F : BlockFrame) : ℤ := ((F.blockSide : ℤ) - 1) / 2
theorem refineSite_add_smul_unitStep {j : ℕ} (y : F.Site (j + 1)) (i : Fin 4) (h : Fin 4 → ℤ) (r : ℕ) :
    refineSite y + siteOfCoords j h + (r : ℤ) • unitStep j i =
      refineSite y + siteOfCoords j (fun l => h l + if l = i then (r : ℤ) else 0) := by apply _root_.YangMills.Construction.NearlyFlatDifferences.refineSite_add_smul_unitStep <;> assumption
theorem mem_innerBonds_of_path {S : Finset F.Cell} {j : ℕ} (hj : j < F.top) (hodd : Odd F.blockSide)
    (c : F.Site (j + 1) × Fin 4) (hc : c ∈ innerBonds S (j + 1)) (h : Fin 4 → ℤ)
    (hh : h ∈ centredCube F.blockSide) (r : ℕ) (hr : r < F.blockSide) :
    (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2, c.2) ∈ innerBonds S j := by apply _root_.YangMills.Construction.NearlyFlatDifferences.mem_innerBonds_of_line <;> assumption
theorem enclosingCell_siteOfCoords {j : ℕ} (hL : 0 < F.blockSide) (t : Fin 4 → ℤ) :
    enclosingCell (siteOfCoords (F := F) j t) =
      siteOfCoords F.top (fun i => (t i + ((F.blockSide : ℤ) ^ (F.top - j) - 1) / 2) /
        (F.blockSide : ℤ) ^ (F.top - j)) := by
  funext i
  change (((siteCoords (siteOfCoords (F := F) j t) i + ((F.blockSide : ℤ) ^ (F.top - j) - 1) / 2) /
      (F.blockSide : ℤ) ^ (F.top - j) : ℤ) : ZMod (F.period F.top i)) =
    (((t i + ((F.blockSide : ℤ) ^ (F.top - j) - 1) / 2) / (F.blockSide : ℤ) ^ (F.top - j) : ℤ) :
      ZMod (F.period F.top i))
  rw [siteCoords_siteOfCoords, period_eq]
  set M : ℤ := (F.blockSide : ℤ) ^ (F.top - j) with hM
  have hMpos : 0 < M := by
    have : (0 : ℤ) < F.blockSide := by exact_mod_cast hL
    positivity
  set sd : ℤ := (F.extent i : ℤ) with hsd
  set q : ℤ := t i / (sd * M) with hq
  have e : t i + (M - 1) / 2 = (t i % (sd * M) + (M - 1) / 2) + M * (sd * q) := by
    have := Int.emod_add_mul_ediv (t i) (sd * M)
    rw [← hq] at this
    nlinarith
  rw [e, Int.add_mul_ediv_left _ _ hMpos.ne']
  refine (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2 ?_
  rw [period_eq]
  simp only [Nat.sub_self, pow_zero, mul_one]
  exact ⟨q, by ring⟩
theorem ediv_succ_bounds (x M : ℤ) (hM : 0 < M) : x / M ≤ (x + 1) / M ∧ (x + 1) / M ≤ x / M + 1 := by
  constructor
  · exact Int.ediv_le_ediv hM (by omega)
  · calc (x + 1) / M ≤ (x + M * 1) / M := Int.ediv_le_ediv hM (by omega)
      _ = x / M + 1 := Int.add_mul_ediv_left _ _ hM.ne'
theorem abs_ediv_sub_ediv_le_one (k k' a g : ℤ) (hk : 0 ≤ k) (hk' : 0 ≤ k') (h1 : -k ≤ g)
    (h2 : g ≤ k + (2 * k + 1)) :
    |(a + k') / (2 * k' + 1) -
      ((2 * k + 1) * a + g + ((2 * k + 1) * k' + k)) / ((2 * k + 1) * (2 * k' + 1))| ≤ 1 := by
  have hL : 0 < 2 * k + 1 := by omega
  have hM : 0 < 2 * k' + 1 := by omega
  rw [← Int.ediv_ediv_of_nonneg hL.le]
  have e : (2 * k + 1) * a + g + ((2 * k + 1) * k' + k) = (g + k) + (2 * k + 1) * (a + k') := by ring
  rw [e, Int.add_mul_ediv_left _ _ hL.ne']
  set E := (g + k) / (2 * k + 1) with hE
  have hE0 : 0 ≤ E := Int.ediv_nonneg (by omega) hL.le
  have hE1 : E < 2 := Int.ediv_lt_of_lt_mul hL (by omega)
  obtain ⟨hb1, hb2⟩ := ediv_succ_bounds (a + k') (2 * k' + 1) hM
  have hcase : E = 0 ∨ E = 1 := by omega
  rcases hcase with h | h
  · rw [h, zero_add]; simp
  · rw [h, add_comm 1]
    rw [abs_le]
    constructor <;> omega
theorem cellSupDist_refineSite_le_one {j : ℕ} (hj : j < F.top) (hodd : Odd F.blockSide)
    (y : F.Site (j + 1)) (g : Fin 4 → ℤ)
    (h1 : ∀ l, -halfSide F ≤ g l) (h2 : ∀ l, g l ≤ halfSide F + F.blockSide) :
    cellSupDist (enclosingCell y) (enclosingCell (refineSite y + siteOfCoords j g)) ≤ 1 := by
  have hL : 0 < F.blockSide := hodd.pos
  have e : refineSite y + siteOfCoords j g =
      siteOfCoords j (fun l => (F.blockSide : ℤ) * siteCoords y l + g l) := by
    simp only [refineSite]
    rw [siteOfCoords_add]
  rw [e, enclosingCell_siteOfCoords hL]
  simp only [cellSupDist]
  apply Finset.sup_le
  intro l _
  obtain ⟨k, hk1, hk2, hk3⟩ := odd_pow_half hodd 1
  obtain ⟨k', hk1', hk2', hk3'⟩ := odd_pow_half hodd (F.top - (j + 1))
  rw [pow_one] at hk1 hk2 hk3
  have hh : halfSide F = k := hk2
  have hLk : (F.blockSide : ℤ) = 2 * (k : ℤ) + 1 := hk3
  have hs : (F.blockSide : ℤ) ^ (F.top - j) = (2 * (k : ℤ) + 1) * (2 * (k' : ℤ) + 1) := by
    rw [blockSide_pow_sub_succ hj, hk3', hLk]
  have hhalf : ((F.blockSide : ℤ) ^ (F.top - j) - 1) / 2 = (2 * (k : ℤ) + 1) * k' + k := by
    rw [hs]
    have : (2 * (k : ℤ) + 1) * (2 * (k' : ℤ) + 1) - 1 = 2 * ((2 * (k : ℤ) + 1) * k' + k) := by ring
    rw [this]
    simp
  have hhalf' : ((F.blockSide : ℤ) ^ (F.top - (j + 1)) - 1) / 2 = k' := by
    rw [hk3']
    omega
  set a := siteCoords y l with ha
  have hc : (enclosingCell y - siteOfCoords F.top (fun i => ((F.blockSide : ℤ) * siteCoords y i + g i +
      ((F.blockSide : ℤ) ^ (F.top - j) - 1) / 2) / (F.blockSide : ℤ) ^ (F.top - j)) : F.Cell) l =
      (((a + k') / (2 * (k' : ℤ) + 1) -
        ((2 * (k : ℤ) + 1) * a + g l + ((2 * (k : ℤ) + 1) * k' + k)) /
        ((2 * (k : ℤ) + 1) * (2 * (k' : ℤ) + 1)) : ℤ) : ZMod (F.period F.top l)) := by
    simp only [Pi.sub_apply, enclosingCell, siteOfCoords]
    rw [hhalf, hhalf', hs, hk3', hLk, Int.cast_sub]
  have hb := abs_ediv_sub_ediv_le_one k k' a (g l) (by positivity) (by positivity)
    (by rw [← hh]; exact h1 l) (by have := h2 l; rw [hh, hLk] at this; exact this)
  rw [Pi.sub_apply] at hc
  rw [hc]
  refine le_trans (natAbs_valMinAbs_intCast_le _ _) ?_
  have := Int.abs_eq_natAbs (((a + k') / (2 * (k' : ℤ) + 1) -
    ((2 * (k : ℤ) + 1) * a + g l + ((2 * (k : ℤ) + 1) * k' + k)) /
        ((2 * (k : ℤ) + 1) * (2 * (k' : ℤ) + 1))))
  omega
theorem baseDistance_refineSite_add {j : ℕ} (hj : j < F.top) (y : F.Site (j + 1)) (g : Fin 4 → ℤ)
    (G : ℕ) (hG : ∀ i, (g i).natAbs ≤ G) (p : F.Site 0) :
    baseDistance (refineSite y + siteOfCoords j g) p ≤ baseDistance y p + F.blockSide ^ j * G ∧
      baseDistance y p ≤ baseDistance (refineSite y + siteOfCoords j g) p + F.blockSide ^ j * G := by apply _root_.YangMills.Construction.WeightedAverages.Chains.baseDistance_refineSite_add <;> assumption
theorem min_max_ratio_le (N A L d d' : ℝ) (hN : 0 ≤ N) (hA : 0 < A) (hL : 1 ≤ L) (hd : 0 ≤ d)
    (hd' : 0 ≤ d') (h1 : d' ≤ d + 2 * L * A) (h2 : d ≤ d' + 2 * L * A) :
    min N (max (L * A) d') ≤ 4 * L * min N (max A d) ∧
      min N (max A d) ≤ 4 * L * min N (max (L * A) d') := by
  have h4 : 0 ≤ 4 * L := by linarith
  constructor
  · rw [mul_min_of_nonneg _ _ h4]
    apply le_min
    · exact le_trans (min_le_left _ _) (by nlinarith)
    · refine le_trans (min_le_right _ _) (max_le ?_ ?_)
      · have : A ≤ max A d := le_max_left _ _
        nlinarith
      · have ha : A ≤ max A d := le_max_left _ _
        have hb : d ≤ max A d := le_max_right _ _
        nlinarith
  · rw [mul_min_of_nonneg _ _ h4]
    apply le_min
    · exact le_trans (min_le_left _ _) (by nlinarith)
    · refine le_trans (min_le_right _ _) (max_le ?_ ?_)
      · have : L * A ≤ max (L * A) d' := le_max_left _ _
        nlinarith
      · have ha : L * A ≤ max (L * A) d' := le_max_left _ _
        have hb : d' ≤ max (L * A) d' := le_max_right _ _
        nlinarith
theorem rpow_neg_le_of_ratio (t B θ : ℝ) (hB : 1 ≤ B) (ht : 0 < t) (ht1 : t ≤ B) (ht2 : 1 ≤ B * t)
    (hθ : |θ| ≤ 1 / 8) : t ^ (-θ) ≤ B ^ (1 / 8 : ℝ) := by
  have hB0 : 0 < B := by linarith
  have hθ' := abs_le.1 hθ
  rcases le_total 0 θ with h | h
  · have hinv : t⁻¹ ≤ B := by
      rw [inv_le_comm₀ ht hB0]
      rw [inv_eq_one_div, div_le_iff₀ hB0]
      linarith
    rw [Real.rpow_neg ht.le, ← Real.inv_rpow ht.le]
    calc t⁻¹ ^ θ ≤ B ^ θ := Real.rpow_le_rpow (inv_nonneg.2 ht.le) hinv h
      _ ≤ B ^ (1 / 8 : ℝ) := Real.rpow_le_rpow_of_exponent_le hB hθ'.2
  · calc t ^ (-θ) ≤ B ^ (-θ) := Real.rpow_le_rpow ht.le ht1 (by linarith)
      _ ≤ B ^ (1 / 8 : ℝ) := Real.rpow_le_rpow_of_exponent_le hB (by linarith)
theorem scaleRadius_pos (hL : 0 < F.blockSide) (j : ℕ) (p : F.Site 0) (x : F.Site j) :
    0 < scaleRadius F j p x := by apply _root_.YangMills.Construction.CoordinateSeminorms.scaleRadius_pos <;> assumption
theorem classWeight_succ_le {j : ℕ} (hj : j < F.top) (hodd : Odd F.blockSide) (φ : F.Cell → ℝ)
    (θ del : ℝ) (p : F.Site 0) (hθ : |θ| ≤ 1 / 8) (hdel : |del| ≤ 1 / 8)
    (hφ : ∀ y y', |φ y - φ y'| ≤ |del| * cellSupDist y y') (y : F.Site (j + 1)) (g : Fin 4 → ℤ)
    (h1 : ∀ l, -halfSide F ≤ g l) (h2 : ∀ l, g l ≤ halfSide F + F.blockSide) :
    classWeight F φ θ p (j + 1) y ≤ Real.exp (1 / 8) * (4 * (F.blockSide : ℝ)) ^ (1 / 8 : ℝ) *
      classWeight F φ θ p j (refineSite y + siteOfCoords j g) := by
  have hLn : 0 < F.blockSide := hodd.pos
  have hL1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hLn
  set x := refineSite y + siteOfCoords j g with hx
  have hcell := cellSupDist_refineSite_le_one hj hodd y g h1 h2
  have hexp : Real.exp (φ (enclosingCell y)) ≤ Real.exp (1 / 8) * Real.exp (φ (enclosingCell x)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have hc1 : (cellSupDist (enclosingCell y) (enclosingCell x) : ℝ) ≤ 1 := by exact_mod_cast hcell
    have hb := hφ (enclosingCell y) (enclosingCell x)
    have h3 : |del| * (cellSupDist (enclosingCell y) (enclosingCell x) : ℝ) ≤ 1 / 8 * 1 :=
      mul_le_mul hdel hc1 (by positivity) (by norm_num)
    have h4 := le_abs_self (φ (enclosingCell y) - φ (enclosingCell x))
    linarith
  obtain ⟨k, hk1, hk2, hk3⟩ := odd_pow_half hodd 1
  rw [pow_one] at hk1 hk2 hk3
  have hh : halfSide F = k := hk2
  have hG : ∀ i, (g i).natAbs ≤ 2 * F.blockSide := by
    intro i
    have a1 := h1 i
    have a2 := h2 i
    rw [hh] at a1 a2
    omega
  obtain ⟨hd1, hd2⟩ := baseDistance_refineSite_add hj y g (2 * F.blockSide) hG p
  set ρ := scaleRadius F j p x with hρ
  set ρ' := scaleRadius F (j + 1) p y with hρ'
  have hρpos : 0 < ρ := scaleRadius_pos hLn _ _ _
  have hρ'pos : 0 < ρ' := scaleRadius_pos hLn _ _ _
  have hAj : (0 : ℝ) < (F.blockSide : ℝ) ^ j := by positivity
  have hrat := min_max_ratio_le ((F.blockSide : ℝ) ^ F.top) ((F.blockSide : ℝ) ^ j) F.blockSide
    (baseDistance x p) (baseDistance y p)
    (by positivity) hAj hL1 (by positivity) (by positivity)
    (by
      have : ((baseDistance y p : ℕ) : ℝ) ≤
          ((baseDistance x p + F.blockSide ^ j * (2 * F.blockSide) : ℕ) : ℝ) := by
        exact_mod_cast hd2
      push_cast at this
      linarith)
    (by
      have : ((baseDistance x p : ℕ) : ℝ) ≤
          ((baseDistance y p + F.blockSide ^ j * (2 * F.blockSide) : ℕ) : ℝ) := by
        exact_mod_cast hd1
      push_cast at this
      linarith)
  have hrw : (F.blockSide : ℝ) * (F.blockSide : ℝ) ^ j = (F.blockSide : ℝ) ^ (j + 1) := by
    rw [pow_succ]; ring
  rw [hrw] at hrat
  have hr1 : ρ' ≤ 4 * (F.blockSide : ℝ) * ρ := hrat.1
  have hr2 : ρ ≤ 4 * (F.blockSide : ℝ) * ρ' := hrat.2
  have hB : (1 : ℝ) ≤ 4 * (F.blockSide : ℝ) := by linarith
  have hpow : (ρ' / ρ) ^ (-θ) ≤ (4 * (F.blockSide : ℝ)) ^ (1 / 8 : ℝ) := by
    apply rpow_neg_le_of_ratio _ _ _ hB (by positivity) ?_ ?_ hθ
    · rw [div_le_iff₀ hρpos]; exact hr1
    · rw [← mul_div_assoc, le_div_iff₀ hρpos]; linarith
  have hsplit : (ρ' / (F.blockSide : ℝ) ^ F.top) ^ (-θ) =
      (ρ' / ρ) ^ (-θ) * (ρ / (F.blockSide : ℝ) ^ F.top) ^ (-θ) := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    field_simp
  simp only [classWeight]
  rw [← hρ, ← hρ', hsplit]
  have hP : 0 ≤ (ρ / (F.blockSide : ℝ) ^ F.top) ^ (-θ) := by positivity
  calc Real.exp (φ (enclosingCell y)) * ((ρ' / ρ) ^ (-θ) * (ρ / (F.blockSide : ℝ) ^ F.top) ^ (-θ))
      ≤ (Real.exp (1 / 8) * Real.exp (φ (enclosingCell x))) *
          ((4 * (F.blockSide : ℝ)) ^ (1 / 8 : ℝ) * (ρ / (F.blockSide : ℝ) ^ F.top) ^ (-θ)) := by
        apply mul_le_mul hexp _ (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_right hpow hP
    _ = _ := by ring
theorem norm_adjointAction (g : UnitQuaternion) (w : ℍ[ℝ]) : ‖adjointAction g w‖ = ‖w‖ := by apply _root_.YangMills.Construction.BlockLines.norm_adjointAction <;> assumption
theorem card_centredCube (hodd : Odd F.blockSide) : (centredCube F.blockSide).card = F.blockSide ^ 4 := by apply _root_.YangMills.Construction.NearTopCoordinates.card_centredCube <;> assumption
theorem refineSite_add_injective {j : ℕ} (hj : j < F.top) (hodd : Odd F.blockSide)
    (y y' : F.Site (j + 1)) (h h' : Fin 4 → ℤ)
    (hh : h ∈ centredCube F.blockSide) (hh' : h' ∈ centredCube F.blockSide)
    (e : refineSite y + siteOfCoords j h = refineSite y' + siteOfCoords j h') :
    y = y' ∧ h = h' := by apply _root_.YangMills.Construction.BlockLines.refineSite_add_injective <;> assumption
theorem exp_mul_rpow_le_half (hL5 : 5 ≤ F.blockSide) :
    Real.exp (1 / 8) * (4 * (F.blockSide : ℝ)) ^ (1 / 8 : ℝ) ≤ (F.blockSide : ℝ) / 2 := by
  have hL : (5 : ℝ) ≤ F.blockSide := by exact_mod_cast hL5
  have hE : Real.exp 1 ≤ 3 := by
    have := Real.exp_one_lt_d9
    linarith
  have h1 : Real.exp (1 / 8) = Real.exp 1 ^ (1 / 8 : ℝ) := (Real.exp_one_rpow _).symm
  have h2 : (F.blockSide : ℝ) / 2 = (((F.blockSide : ℝ) / 2) ^ (8 : ℕ)) ^ (1 / 8 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  rw [h1, ← Real.mul_rpow (by positivity) (by positivity)]
  conv_rhs => rw [h2]
  apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
  have h3 : (5 / 2 : ℝ) ^ 7 * ((F.blockSide : ℝ) / 2) ≤ ((F.blockSide : ℝ) / 2) ^ 8 := by
    have h4 : (5 / 2 : ℝ) ≤ (F.blockSide : ℝ) / 2 := by linarith
    have h5 : (5 / 2 : ℝ) ^ 7 ≤ ((F.blockSide : ℝ) / 2) ^ 7 := pow_le_pow_left₀ (by norm_num) h4 7
    calc (5 / 2 : ℝ) ^ 7 * ((F.blockSide : ℝ) / 2) ≤ ((F.blockSide : ℝ) / 2) ^ 7 * ((F.blockSide : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right h5 (by positivity)
      _ = _ := by ring
  have h6 : Real.exp 1 * (4 * (F.blockSide : ℝ)) ≤ 3 * (4 * (F.blockSide : ℝ)) :=
    mul_le_mul_of_nonneg_right hE (by positivity)
  norm_num at h3
  nlinarith
variable {S : Finset F.Cell}
theorem parallelAverage_weighted_sq_le (hL5 : 5 ≤ F.blockSide) (hodd : Odd F.blockSide) {j : ℕ}
    (hj : j < F.top) (R : F.GaugeField j)
    (f : F.Site j → Fin 4 → ℍ[ℝ]) (φ : F.Cell → ℝ) (θ del : ℝ) (p : F.Site 0)
    (hθ : |θ| ≤ 1 / 8) (hdel : |del| ≤ 1 / 8)
    (hφ : ∀ y y', |φ y - φ y'| ≤ |del| * cellSupDist y y') :
    ∑ c ∈ innerBonds S (j + 1), (classWeight F φ θ p (j + 1) c.1 * ‖parallelAverage R f c‖) ^ 2 ≤
      1 / 4 * ∑ b ∈ innerBonds S j, (classWeight F φ θ p j b.1 * ‖f b.1 b.2‖) ^ 2 := by
  classical
  have hLn : 0 < F.blockSide := hodd.pos
  set W := classWeight F φ θ p with hW
  have hWpos : ∀ (i : ℕ) (x : F.Site i), 0 < W i x := by
    intro i x
    simp only [hW, classWeight]
    have := scaleRadius_pos hLn i p x
    positivity
  set A := Real.exp (1 / 8) * (4 * (F.blockSide : ℝ)) ^ (1 / 8 : ℝ) with hA
  have hApos : 0 < A := by positivity
  have hAL : A ≤ (F.blockSide : ℝ) / 2 := exp_mul_rpow_le_half hL5
  set X : F.Site (j + 1) × Fin 4 → (Fin 4 → ℤ) → ℕ → F.Site j :=
    fun c h r => refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2 with hX
  set G : F.Site j × Fin 4 → ℝ := fun b => (W j b.1 * ‖f b.1 b.2‖) ^ 2 with hG
  have hGnn : ∀ b, 0 ≤ G b := fun b => by positivity
  set Q : Finset ((Fin 4 → ℤ) × ℕ) := centredCube F.blockSide ×ˢ Finset.range F.blockSide with hQ
  have hQcard : (Q.card : ℝ) = (F.blockSide : ℝ) ^ 5 := by
    rw [hQ, Finset.card_product, card_centredCube hodd, Finset.card_range]
    push_cast
    ring
  have hnorm : ∀ c : F.Site (j + 1) × Fin 4, ‖parallelAverage R f c‖ ≤
      (1 / (F.blockSide : ℝ) ^ 4) * ∑ q ∈ Q, ‖f (X c q.1 q.2) c.2‖ := by
    intro c
    simp only [parallelAverage, norm_smul]
    have h1 : ‖∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), ∑ r ∈ Finset.range F.blockSide,
        adjointAction (pathHolonomy R (refineSite c.1) (axisPath h π ++ List.replicate r (c.2, true)))
          (f (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2)‖ ≤
        24 * ∑ q ∈ Q, ‖f (X c q.1 q.2) c.2‖ := by
      refine le_trans (norm_sum_le _ _) ?_
      rw [hQ, Finset.sum_product, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro h _
      refine le_trans (norm_sum_le _ _) ?_
      have h2 : ∀ π : Equiv.Perm (Fin 4), ‖∑ r ∈ Finset.range F.blockSide,
          adjointAction (pathHolonomy R (refineSite c.1) (axisPath h π ++ List.replicate r (c.2, true)))
            (f (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2)‖ ≤
          ∑ r ∈ Finset.range F.blockSide, ‖f (X c h r) c.2‖ := by
        intro π
        refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
        apply Finset.sum_congr rfl
        intro r _
        rw [norm_adjointAction]
      refine le_trans (Finset.sum_le_sum fun π _ => h2 π) (le_of_eq ?_)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
      simp [Nat.factorial]
    have h3 : ‖(1 / (24 * (F.blockSide : ℝ) ^ 4))‖ = 1 / (24 * (F.blockSide : ℝ) ^ 4) := by
      rw [Real.norm_of_nonneg (by positivity)]
    rw [h3]
    calc 1 / (24 * (F.blockSide : ℝ) ^ 4) * _ ≤
          1 / (24 * (F.blockSide : ℝ) ^ 4) * (24 * ∑ q ∈ Q, ‖f (X c q.1 q.2) c.2‖) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by field_simp
  have hwt : ∀ (c : F.Site (j + 1) × Fin 4) (q : (Fin 4 → ℤ) × ℕ), q ∈ Q →
      W (j + 1) c.1 ≤ A * W j (X c q.1 q.2) := by
    intro c q hq
    obtain ⟨hq1, hq2⟩ := Finset.mem_product.1 hq
    have hr : q.2 < F.blockSide := Finset.mem_range.1 hq2
    have hc := (mem_centredCube _ _).1 hq1
    have hc' : ∀ l, -halfSide F ≤ q.1 l ∧ q.1 l ≤ halfSide F := hc
    have hXe : X c q.1 q.2 =
        refineSite c.1 + siteOfCoords j (fun l => q.1 l + if l = c.2 then (q.2 : ℤ) else 0) :=
      refineSite_add_smul_unitStep c.1 c.2 q.1 q.2
    rw [hXe]
    refine classWeight_succ_le hj hodd φ θ del p hθ hdel hφ c.1 _ (fun l => ?_) (fun l => ?_)
    · by_cases hl : l = c.2
      · simp only [hl, if_true]; linarith [(hc' c.2).1]
      · simp only [if_neg hl, add_zero]; exact (hc' l).1
    · by_cases hl : l = c.2
      · simp only [hl, if_true]; linarith [(hc' c.2).2]
      · simp only [if_neg hl, add_zero]; linarith [(hc' l).2]
  have hterm : ∀ c : F.Site (j + 1) × Fin 4, (W (j + 1) c.1 * ‖parallelAverage R f c‖) ^ 2 ≤
      A ^ 2 * (1 / (F.blockSide : ℝ) ^ 3) * ∑ q ∈ Q, G (X c q.1 q.2, c.2) := by
    intro c
    have h1 : W (j + 1) c.1 * ‖parallelAverage R f c‖ ≤
        A * (1 / (F.blockSide : ℝ) ^ 4) * ∑ q ∈ Q, W j (X c q.1 q.2) * ‖f (X c q.1 q.2) c.2‖ := by
      calc W (j + 1) c.1 * ‖parallelAverage R f c‖
          ≤ W (j + 1) c.1 * ((1 / (F.blockSide : ℝ) ^ 4) * ∑ q ∈ Q, ‖f (X c q.1 q.2) c.2‖) :=
            mul_le_mul_of_nonneg_left (hnorm c) (hWpos _ _).le
        _ = (1 / (F.blockSide : ℝ) ^ 4) * ∑ q ∈ Q, W (j + 1) c.1 * ‖f (X c q.1 q.2) c.2‖ := by
            rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro q _
            ring
        _ ≤ (1 / (F.blockSide : ℝ) ^ 4) * ∑ q ∈ Q, (A * W j (X c q.1 q.2)) * ‖f (X c q.1 q.2) c.2‖ := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply Finset.sum_le_sum
            intro q hq
            exact mul_le_mul_of_nonneg_right (hwt c q hq) (norm_nonneg _)
        _ = _ := by
            rw [Finset.mul_sum, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro q _
            ring
    have h0 : 0 ≤ W (j + 1) c.1 * ‖parallelAverage R f c‖ :=
      mul_nonneg (hWpos _ _).le (norm_nonneg _)
    have hcs := sq_sum_le_card_mul_sum_sq (s := Q)
      (f := fun q => W j (X c q.1 q.2) * ‖f (X c q.1 q.2) c.2‖)
    rw [hQcard] at hcs
    calc (W (j + 1) c.1 * ‖parallelAverage R f c‖) ^ 2
        ≤ (A * (1 / (F.blockSide : ℝ) ^ 4) * ∑ q ∈ Q, W j (X c q.1 q.2) * ‖f (X c q.1 q.2) c.2‖) ^ 2 :=
          pow_le_pow_left₀ h0 h1 2
      _ = A ^ 2 * (1 / (F.blockSide : ℝ) ^ 4) ^ 2 *
            (∑ q ∈ Q, W j (X c q.1 q.2) * ‖f (X c q.1 q.2) c.2‖) ^ 2 := by
          ring
      _ ≤ A ^ 2 * (1 / (F.blockSide : ℝ) ^ 4) ^ 2 *
            ((F.blockSide : ℝ) ^ 5 * ∑ q ∈ Q, G (X c q.1 q.2, c.2)) :=
          mul_le_mul_of_nonneg_left hcs (by positivity)
      _ = _ := by
          field_simp
  have hcount : ∑ c ∈ innerBonds S (j + 1), ∑ q ∈ Q, G (X c q.1 q.2, c.2) ≤
      (F.blockSide : ℝ) * ∑ b ∈ innerBonds S j, G b := by
    simp only [hQ, Finset.sum_product]
    have hswap : ∑ c ∈ innerBonds S (j + 1), ∑ h ∈ centredCube F.blockSide,
          ∑ r ∈ Finset.range F.blockSide, G (X c h r, c.2) =
        ∑ r ∈ Finset.range F.blockSide, ∑ c ∈ innerBonds S (j + 1),
          ∑ h ∈ centredCube F.blockSide, G (X c h r, c.2) := by
      calc ∑ c ∈ innerBonds S (j + 1), ∑ h ∈ centredCube F.blockSide,
            ∑ r ∈ Finset.range F.blockSide, G (X c h r, c.2)
          = ∑ c ∈ innerBonds S (j + 1), ∑ r ∈ Finset.range F.blockSide,
              ∑ h ∈ centredCube F.blockSide, G (X c h r, c.2) :=
            Finset.sum_congr rfl fun c _ => Finset.sum_comm
        _ = _ := Finset.sum_comm
    rw [hswap]
    have hr : ∀ r ∈ Finset.range F.blockSide, ∑ c ∈ innerBonds S (j + 1),
        ∑ h ∈ centredCube F.blockSide, G (X c h r, c.2) ≤ ∑ b ∈ innerBonds S j, G b := by
      intro r hr
      have hrl : r < F.blockSide := Finset.mem_range.1 hr
      set τ : (F.Site (j + 1) × Fin 4) × (Fin 4 → ℤ) → F.Site j × Fin 4 :=
        fun z => (X z.1 z.2 r, z.1.2) with hτ
      have hinj : Set.InjOn τ (innerBonds S (j + 1) ×ˢ centredCube F.blockSide : Finset _) := by
        rintro ⟨c, h⟩ hz ⟨c', h'⟩ hz' e
        have hz1 := Finset.mem_product.1 (Finset.mem_coe.1 hz)
        have hz2 := Finset.mem_product.1 (Finset.mem_coe.1 hz')
        have e' := Prod.ext_iff.1 e
        have e1 : X c h r = X c' h' r := e'.1
        have e2 : c.2 = c'.2 := e'.2
        simp only [hX] at e1
        rw [e2] at e1
        have e3 := add_right_cancel e1
        obtain ⟨hy, hh⟩ := refineSite_add_injective hj hodd c.1 c'.1 h h' hz1.2 hz2.2 e3
        exact Prod.ext (Prod.ext hy e2) hh
      calc ∑ c ∈ innerBonds S (j + 1), ∑ h ∈ centredCube F.blockSide, G (X c h r, c.2)
          = ∑ z ∈ innerBonds S (j + 1) ×ˢ centredCube F.blockSide, G (τ z) := by
            rw [Finset.sum_product]
        _ = ∑ b ∈ (innerBonds S (j + 1) ×ˢ centredCube F.blockSide).image τ, G b :=
            (Finset.sum_image hinj).symm
        _ ≤ ∑ b ∈ innerBonds S j, G b := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro b hb
              obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hb
              obtain ⟨hz1, hz2⟩ := Finset.mem_product.1 hz
              exact mem_innerBonds_of_path hj hodd z.1 hz1 z.2 hz2 r hrl
            · intro b _ _
              exact hGnn b
    calc ∑ r ∈ Finset.range F.blockSide, ∑ c ∈ innerBonds S (j + 1),
          ∑ h ∈ centredCube F.blockSide, G (X c h r, c.2)
        ≤ ∑ _r ∈ Finset.range F.blockSide, ∑ b ∈ innerBonds S j, G b := Finset.sum_le_sum hr
      _ = _ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hfinal : A ^ 2 * (1 / (F.blockSide : ℝ) ^ 3) * (F.blockSide : ℝ) ≤ 1 / 4 := by
    have h1 : A ^ 2 ≤ ((F.blockSide : ℝ) / 2) ^ 2 := pow_le_pow_left₀ hApos.le hAL 2
    have e : A ^ 2 * (1 / (F.blockSide : ℝ) ^ 3) * (F.blockSide : ℝ) = A ^ 2 / (F.blockSide : ℝ) ^ 2 := by
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    nlinarith
  have hsumG : 0 ≤ ∑ b ∈ innerBonds S j, G b := Finset.sum_nonneg fun b _ => hGnn b
  calc ∑ c ∈ innerBonds S (j + 1), (W (j + 1) c.1 * ‖parallelAverage R f c‖) ^ 2
      ≤ ∑ c ∈ innerBonds S (j + 1),
          A ^ 2 * (1 / (F.blockSide : ℝ) ^ 3) * ∑ q ∈ Q, G (X c q.1 q.2, c.2) :=
        Finset.sum_le_sum fun c _ => hterm c
    _ = A ^ 2 * (1 / (F.blockSide : ℝ) ^ 3) *
          ∑ c ∈ innerBonds S (j + 1), ∑ q ∈ Q, G (X c q.1 q.2, c.2) := by
        rw [Finset.mul_sum]
    _ ≤ A ^ 2 * (1 / (F.blockSide : ℝ) ^ 3) * ((F.blockSide : ℝ) * ∑ b ∈ innerBonds S j, G b) :=
        mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = (A ^ 2 * (1 / (F.blockSide : ℝ) ^ 3) * (F.blockSide : ℝ)) * ∑ b ∈ innerBonds S j, G b := by ring
    _ ≤ 1 / 4 * ∑ b ∈ innerBonds S j, G b := mul_le_mul_of_nonneg_right hfinal hsumG
theorem parallelAverage_sub {j : ℕ} (R : F.GaugeField j) (f f' : F.Site j → Fin 4 → ℍ[ℝ])
    (c : F.Site (j + 1) × Fin 4) :
    parallelAverage R (fun x i => f x i - f' x i) c =
      parallelAverage R f c - parallelAverage R f' c := by apply _root_.YangMills.Construction.BlockAverages.ColdBelowTop.parallelAverage_sub <;> assumption
def upperLevelsPart (R : F.FieldChain) (U : ChainChart F) (j : ℕ) : F.Site j → Fin 4 → ℍ[ℝ] :=
  fun y i => linearPart R U j y i - linearPart R (baseOnlyChart U.fine) j y i
theorem upperLevelsPart_zero (R : F.FieldChain) (U : ChainChart F) :
    upperLevelsPart R U 0 = fun _ _ => 0 := by
  funext y i
  simp [upperLevelsPart, linearPart, baseOnlyChart]
theorem upperLevelsPart_succ (R : F.FieldChain) (U : ChainChart F) (j : ℕ) (y : F.Site (j + 1))
    (i : Fin 4) :
    upperLevelsPart R U (j + 1) y i = parallelAverage (R j) (upperLevelsPart R U j) (y, i) +
      if j + 1 < F.top then ((U.coarse j y i : imaginaryQuaternions) : ℍ[ℝ]) else 0 := by
  have hq : parallelAverage (R j) (upperLevelsPart R U j) (y, i) =
      parallelAverage (R j) (linearPart R U j) (y, i) -
        parallelAverage (R j) (linearPart R (baseOnlyChart U.fine) j) (y, i) :=
    parallelAverage_sub _ _ _ _
  rw [hq]
  simp only [upperLevelsPart, linearPart, baseOnlyChart]
  by_cases h : j + 1 < F.top
  · simp only [if_pos h, ZeroMemClass.coe_zero]
    abel
  · simp only [if_neg h]
    abel
theorem add_sq_le_two_mul (x y : ℝ) : (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
  nlinarith [sq_nonneg (x - y)]
theorem upperLevelsPart_weighted_sq_le (hL5 : 5 ≤ F.blockSide) (hodd : Odd F.blockSide) (R : F.FieldChain)
    (U : ChainChart F) (φ : F.Cell → ℝ) (θ del : ℝ) (p : F.Site 0) (hθ : |θ| ≤ 1 / 8)
    (hdel : |del| ≤ 1 / 8) (hφ : ∀ y y', |φ y - φ y'| ≤ |del| * cellSupDist y y') (j : ℕ)
    (hj : j ≤ F.top) :
    ∑ b ∈ innerBonds S j, (classWeight F φ θ p j b.1 * ‖upperLevelsPart R U j b.1 b.2‖) ^ 2 ≤
      2 * ∑ i ∈ Finset.range j, if i + 1 < F.top then
        ∑ c ∈ innerBonds S (i + 1), (classWeight F φ θ p (i + 1) c.1 * ‖U.coarse i c.1 c.2‖) ^ 2
      else 0 := by
  have hLn : 0 < F.blockSide := hodd.pos
  have hWpos : ∀ (i : ℕ) (x : F.Site i), 0 < classWeight F φ θ p i x := by
    intro i x
    simp only [classWeight]
    have := scaleRadius_pos hLn i p x
    positivity
  induction j with
  | zero =>
    simp [upperLevelsPart_zero]
  | succ j ih =>
    have hj' : j < F.top := by omega
    have ih' := ih hj'.le
    have hstep := parallelAverage_weighted_sq_le (S := S) hL5 hodd hj' (R j) (upperLevelsPart R U j)
      φ θ del p hθ hdel hφ
    set W := classWeight F φ θ p with hW
    set M : ℝ := if j + 1 < F.top then
      ∑ c ∈ innerBonds S (j + 1), (W (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 else 0 with hM
    have hterm : ∀ c : F.Site (j + 1) × Fin 4,
        (W (j + 1) c.1 * ‖upperLevelsPart R U (j + 1) c.1 c.2‖) ^ 2 ≤
          2 * (W (j + 1) c.1 * ‖parallelAverage (R j) (upperLevelsPart R U j) c‖) ^ 2 +
            2 * (if j + 1 < F.top then (W (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 else 0) := by
      intro c
      have h1 : ‖upperLevelsPart R U (j + 1) c.1 c.2‖ ≤
          ‖parallelAverage (R j) (upperLevelsPart R U j) c‖ +
            (if j + 1 < F.top then ‖U.coarse j c.1 c.2‖ else 0) := by
        rw [upperLevelsPart_succ]
        refine le_trans (norm_add_le _ _) ?_
        by_cases h : j + 1 < F.top
        · simp only [if_pos h]
          exact le_of_eq rfl
        · simp only [if_neg h, norm_zero]
          exact le_rfl
      have hW0 := (hWpos (j + 1) c.1).le
      have h2 : W (j + 1) c.1 * ‖upperLevelsPart R U (j + 1) c.1 c.2‖ ≤
          W (j + 1) c.1 * ‖parallelAverage (R j) (upperLevelsPart R U j) c‖ +
            W (j + 1) c.1 * (if j + 1 < F.top then ‖U.coarse j c.1 c.2‖ else 0) := by
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left h1 hW0
      have h3 := pow_le_pow_left₀ (mul_nonneg hW0 (norm_nonneg _)) h2 2
      refine le_trans h3 (le_trans (add_sq_le_two_mul _ _) ?_)
      by_cases h : j + 1 < F.top
      · simp only [if_pos h]; exact le_rfl
      · simp [if_neg h]
    have hsum : ∑ c ∈ innerBonds S (j + 1), (W (j + 1) c.1 * ‖upperLevelsPart R U (j + 1) c.1 c.2‖) ^ 2 ≤
        2 * ∑ c ∈ innerBonds S (j + 1),
          (W (j + 1) c.1 * ‖parallelAverage (R j) (upperLevelsPart R U j) c‖) ^ 2 + 2 * M := by
      refine le_trans (Finset.sum_le_sum fun c _ => hterm c) (le_of_eq ?_)
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hM]
      by_cases h : j + 1 < F.top
      · simp only [if_pos h]
      · simp [if_neg h]
    rw [Finset.sum_range_succ, mul_add]
    have hT0 : 0 ≤ ∑ b ∈ innerBonds S j, (W j b.1 * ‖upperLevelsPart R U j b.1 b.2‖) ^ 2 :=
      Finset.sum_nonneg fun b _ => by positivity
    linarith
theorem enclosingCell_mem (hodd : Odd F.blockSide) {j : ℕ} (x : F.Site j) (hx : x ∈ sitesOfCells S j) :
    enclosingCell x ∈ S := by apply _root_.YangMills.Construction.BlockLines.enclosingCell_mem <;> assumption
theorem bondsOver_self (hodd : Odd F.blockSide) (j : ℕ) : bondsOver S S j = innerBonds S j := by
  classical
  simp only [bondsOver]
  apply Finset.filter_true_of_mem
  intro b hb
  simp only [innerBonds, Finset.mem_filter, Finset.mem_product] at hb
  exact enclosingCell_mem hodd _ hb.1.1
theorem sqrt_add_le_add_sqrt (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by apply _root_.YangMills.Construction.CoordinateSeminorms.sqrt_add_le_add_sqrt <;> assumption
theorem sqrt_sum_le_sum_sqrt {ι : Type} (s : Finset ι) (g : ι → ℝ) (hg : ∀ i, 0 ≤ g i) :
    Real.sqrt (∑ i ∈ s, g i) ≤ ∑ i ∈ s, Real.sqrt (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine le_trans (sqrt_add_le_add_sqrt _ _ (hg a) (Finset.sum_nonneg fun i _ => hg i)) ?_
    linarith
theorem card_cellSupDist_le_three (y : F.Cell) : (S.filter fun z => cellSupDist z y ≤ 3).card ≤ 2401 := by
  classical
  set T : Finset (Fin 4 → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-3 : ℤ) 3 with hT
  have hTc : T.card = 2401 := by
    simp [hT, Fintype.card_piFinset]
  rw [← hTc]
  apply Finset.card_le_card_of_injOn (fun z i => ((z - y : F.Cell) i).valMinAbs)
  · intro z hz
    have hz' := (Finset.mem_filter.1 (Finset.mem_coe.1 hz)).2
    refine Finset.mem_coe.2 (Fintype.mem_piFinset.2 fun i => ?_)
    have h1 : (((z - y : F.Cell) i).valMinAbs).natAbs ≤ cellSupDist z y :=
      Finset.le_sup (f := fun i => (((z - y : F.Cell) i).valMinAbs).natAbs) (Finset.mem_univ i)
    rw [Finset.mem_Icc]
    change -3 ≤ ((z - y : F.Cell) i).valMinAbs ∧ ((z - y : F.Cell) i).valMinAbs ≤ 3
    omega
  · intro z _ z' _ e
    funext i
    have := congrFun e i
    have h2 := ZMod.injective_valMinAbs this
    simpa using h2
theorem sum_cellBall_le (g : F.Cell → ℝ) (hg : ∀ y, 0 ≤ g y) :
    ∑ z ∈ S, ∑ y ∈ cellBall S z 3, g y ≤ 2401 * ∑ y ∈ S, g y := by
  classical
  have e : ∑ z ∈ S, ∑ y ∈ cellBall S z 3, g y =
      ∑ y ∈ S, ∑ z ∈ S.filter (fun z => cellSupDist z y ≤ 3), g y := by
    simp only [cellBall]
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
  rw [e, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y _
  rw [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_cellSupDist_le_three y) (hg y)
theorem sum_filter_mem_eq_sum_fiber {ι : Type} (I : Finset ι) (κ : ι → F.Cell) (B : Finset F.Cell)
    (g : ι → ℝ) :
    ∑ i ∈ I.filter (fun i => κ i ∈ B), g i = ∑ y ∈ B, ∑ i ∈ I.filter (fun i => κ i = y), g i := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := I.filter (fun i => κ i ∈ B)) (t := B) (g := κ)
    (fun i hi => (Finset.mem_filter.1 hi).2)]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext i
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩
    exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩
    exact ⟨⟨h1, h3 ▸ hy⟩, h3⟩
theorem sum_filter_cellBall_le {ι : Type} (I : Finset ι) (κ : ι → F.Cell) (g : ι → ℝ)
    (hg : ∀ i, 0 ≤ g i) :
    ∑ z ∈ S, ∑ i ∈ I.filter (fun i => κ i ∈ cellBall S z 3), g i ≤
      2401 * ∑ i ∈ I.filter (fun i => κ i ∈ S), g i := by
  classical
  simp only [sum_filter_mem_eq_sum_fiber]
  exact sum_cellBall_le _ fun y => Finset.sum_nonneg fun i _ => hg i
theorem norm_coe_imaginaryQuaternions (x : imaginaryQuaternions) : ‖(x : ℍ[ℝ])‖ = ‖x‖ := rfl
theorem sum_localNorm_sq_le (R : F.FieldChain) (U : ChainChart F) (W : F.SiteWeights) :
    ∑ z ∈ S, localNorm S R U W z ^ 2 ≤
      2401 * (cellwiseL4Norm S (W 0) (fun x i => U.fine x i) ^ 2 +
        ∑ q ∈ plaquettesOver S S 0, (W 0 q.1 * ‖linearizedCurl (R 0) U.fine q‖) ^ 2 +
        ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S S (j + 1),
          (W (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2) := by
  classical
  have hnear : ∀ z ∈ S, localNorm S R U W z ^ 2 ≤
      (∑ y ∈ cellBall S z 3,
        Real.sqrt (∑ b ∈ bondsOver S {y} 0, (W 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4)) +
      ∑ q ∈ plaquettesOver S (cellBall S z 3) 0, (W 0 q.1 * ‖linearizedCurl (R 0) U.fine q‖) ^ 2 +
      ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
        (W (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 := by
    intro z _
    have hnn : 0 ≤ localNormSq S (cellBall S z 3) R U W := by
      simp only [localNormSq]
      have h1 := Real.sqrt_nonneg
        (∑ b ∈ bondsOver S (cellBall S z 3) 0, (W 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4)
      have h2 : 0 ≤ ∑ p ∈ plaquettesOver S (cellBall S z 3) 0,
          (W 0 p.1 * ‖linearizedCurl (R 0) U.fine p‖) ^ 2 :=
        Finset.sum_nonneg fun q _ => by positivity
      have h3 : 0 ≤ ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
          (W (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 :=
        Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun c _ => by positivity
      linarith
    simp only [localNorm]
    rw [Real.sq_sqrt hnn]
    simp only [localNormSq]
    have hsq : Real.sqrt (∑ b ∈ bondsOver S (cellBall S z 3) 0, (W 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4) ≤
        ∑ y ∈ cellBall S z 3, Real.sqrt (∑ b ∈ bondsOver S {y} 0, (W 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4) := by
      have he : ∑ b ∈ bondsOver S (cellBall S z 3) 0, (W 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4 =
          ∑ y ∈ cellBall S z 3, ∑ b ∈ bondsOver S {y} 0, (W 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4 := by
        simp only [bondsOver, Finset.mem_singleton]
        exact sum_filter_mem_eq_sum_fiber _ _ _ _
      rw [he]
      exact sqrt_sum_le_sum_sqrt _ _ fun y => Finset.sum_nonneg fun b _ => by positivity
    linarith
  have hsum1 : ∑ z ∈ S, ∑ y ∈ cellBall S z 3,
      Real.sqrt (∑ b ∈ bondsOver S {y} 0, (W 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4) ≤
      2401 * cellwiseL4Norm S (W 0) (fun x i => U.fine x i) ^ 2 := by
    have h1 := sum_cellBall_le (S := S)
      (fun y => Real.sqrt (∑ b ∈ bondsOver S {y} 0, (W 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4))
      fun y => Real.sqrt_nonneg _
    have h2 : cellwiseL4Norm S (W 0) (fun x i => U.fine x i) ^ 2 =
        ∑ y ∈ S, Real.sqrt (∑ b ∈ bondsOver S {y} 0, (W 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4) := by
      simp only [cellwiseL4Norm]
      rw [Real.sq_sqrt (Finset.sum_nonneg fun y _ => Real.sqrt_nonneg _)]
      simp only [norm_coe_imaginaryQuaternions]
    rw [h2]
    exact h1
  have hsum2 : ∑ z ∈ S, ∑ q ∈ plaquettesOver S (cellBall S z 3) 0,
      (W 0 q.1 * ‖linearizedCurl (R 0) U.fine q‖) ^ 2 ≤
      2401 * ∑ q ∈ plaquettesOver S S 0, (W 0 q.1 * ‖linearizedCurl (R 0) U.fine q‖) ^ 2 := by
    have h := sum_filter_cellBall_le (S := S) (innerPlaquettes S 0) (fun q => enclosingCell q.1)
      (fun q => (W 0 q.1 * ‖linearizedCurl (R 0) U.fine q‖) ^ 2) (fun q => by positivity)
    simp only [plaquettesOver]
    convert h
  have hsum3 : ∑ z ∈ S, ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
        (W (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 ≤
      2401 * ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S S (j + 1),
        (W (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 := by
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have h := sum_filter_cellBall_le (S := S) (innerBonds S (j + 1)) (fun c => enclosingCell c.1)
      (fun c => (W (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2) (fun c => by positivity)
    simp only [bondsOver]
    convert h
  refine le_trans (Finset.sum_le_sum hnear) ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  linarith
theorem combine_bounds (a C cs P Mm Nu Bq X : ℝ) (ha : 0 < a) (hP0 : 0 ≤ P) (hMm0 : 0 ≤ Mm)
    (hNu0 : 0 ≤ Nu) (hcsle : cs ^ 2 ≤ 2 * C ^ 2 * (P + Bq)) (hBq : Bq ≤ 2 * Nu + 4 * Mm)
    (hX : X ≤ 2401 * (cs ^ 2 + P + Mm)) :
    X ≤ 2401 * (8 * C ^ 2 + 1) * (1 + 1 / a) * (P + a * Mm + a * Nu) := by
  have h1 : cs ^ 2 + P + Mm ≤ (2 * C ^ 2 + 1) * P + 4 * C ^ 2 * Nu + (8 * C ^ 2 + 1) * Mm := by
    have : 2 * C ^ 2 * (P + Bq) ≤ 2 * C ^ 2 * (P + (2 * Nu + 4 * Mm)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  have hC2 : 0 ≤ C ^ 2 := by positivity
  have hia : 0 < 1 / a := by positivity
  have hea : (1 + 1 / a) * a = a + 1 := by field_simp
  have h2 : (2 * C ^ 2 + 1) * P + 4 * C ^ 2 * Nu + (8 * C ^ 2 + 1) * Mm ≤
      (8 * C ^ 2 + 1) * (1 + 1 / a) * (P + a * Mm + a * Nu) := by
    have e : (8 * C ^ 2 + 1) * (1 + 1 / a) * (P + a * Mm + a * Nu) =
        (8 * C ^ 2 + 1) * (1 + 1 / a) * P + (8 * C ^ 2 + 1) * (a + 1) * Mm +
          (8 * C ^ 2 + 1) * (a + 1) * Nu := by
      rw [← hea]
      ring
    rw [e]
    have t1 : (2 * C ^ 2 + 1) * P ≤ (8 * C ^ 2 + 1) * (1 + 1 / a) * P := by
      apply mul_le_mul_of_nonneg_right _ hP0
      nlinarith [mul_nonneg hC2 hia.le]
    have t2 : (8 * C ^ 2 + 1) * Mm ≤ (8 * C ^ 2 + 1) * (a + 1) * Mm := by
      apply mul_le_mul_of_nonneg_right _ hMm0
      nlinarith [mul_nonneg hC2 ha.le]
    have t3 : 4 * C ^ 2 * Nu ≤ (8 * C ^ 2 + 1) * (a + 1) * Nu := by
      apply mul_le_mul_of_nonneg_right _ hNu0
      nlinarith [mul_nonneg hC2 ha.le]
    linarith
  calc X ≤ 2401 * (cs ^ 2 + P + Mm) := hX
    _ ≤ 2401 * ((8 * C ^ 2 + 1) * (1 + 1 / a) * (P + a * Mm + a * Nu)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        linarith
    _ = _ := by ring
theorem baseOnly_top_weighted_sq_le (h5 : 5 ≤ F.blockSide) (hodd : Odd F.blockSide) (R : F.FieldChain)
    (U : ChainChart F) (φ : F.Cell → ℝ) (θ del : ℝ) (p : F.Site 0) (hθ : |θ| ≤ 1 / 8)
    (hdel : |del| ≤ 1 / 8) (hφ : ∀ y y', |φ y - φ y'| ≤ |del| * cellSupDist y y') :
    ∑ b ∈ innerBonds S F.top, (classWeight F φ θ p F.top b.1 *
        ‖linearPart R (baseOnlyChart U.fine) F.top b.1 b.2‖) ^ 2 ≤
      2 * ∑ c ∈ bondsOver S S F.top, (classWeight F φ θ p F.top c.1 * ‖linearPart R U F.top c.1 c.2‖) ^ 2 +
      4 * ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S S (j + 1),
        (classWeight F φ θ p (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 := by
  have hup := upperLevelsPart_weighted_sq_le (S := S) h5 hodd R U φ θ del p hθ hdel hφ F.top le_rfl
  have e1 : (∑ i ∈ Finset.range F.top, if i + 1 < F.top then
      ∑ c ∈ innerBonds S (i + 1), (classWeight F φ θ p (i + 1) c.1 * ‖U.coarse i c.1 c.2‖) ^ 2 else 0) =
      ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S S (j + 1),
        (classWeight F φ θ p (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 := by
    change (∑ i ∈ Finset.range (F.depth + 1), _) = _
    rw [Finset.sum_range_succ, if_neg (lt_irrefl _), add_zero]
    have hn1 : F.top - 1 = F.depth := rfl
    rw [hn1]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j + 1 < F.top := by
      have := Finset.mem_range.1 hj
      simp only [BlockFrame.top]
      omega
    rw [if_pos hj', bondsOver_self hodd]
  rw [e1] at hup
  have hterm : ∀ b : F.Site F.top × Fin 4,
      (classWeight F φ θ p F.top b.1 * ‖linearPart R (baseOnlyChart U.fine) F.top b.1 b.2‖) ^ 2 ≤
        2 * (classWeight F φ θ p F.top b.1 * ‖linearPart R U F.top b.1 b.2‖) ^ 2 +
          2 * (classWeight F φ θ p F.top b.1 * ‖upperLevelsPart R U F.top b.1 b.2‖) ^ 2 := by
    intro b
    have hW0 : 0 ≤ classWeight F φ θ p F.top b.1 := by
      simp only [classWeight]
      have := scaleRadius_pos hodd.pos F.top p b.1
      positivity
    have e : linearPart R (baseOnlyChart U.fine) F.top b.1 b.2 =
        linearPart R U F.top b.1 b.2 - upperLevelsPart R U F.top b.1 b.2 := by
      simp only [upperLevelsPart]
      abel
    have h1 : ‖linearPart R (baseOnlyChart U.fine) F.top b.1 b.2‖ ≤
        ‖linearPart R U F.top b.1 b.2‖ + ‖upperLevelsPart R U F.top b.1 b.2‖ := by
      rw [e]
      exact norm_sub_le _ _
    have h2 := mul_le_mul_of_nonneg_left h1 hW0
    rw [mul_add] at h2
    have h3 := pow_le_pow_left₀ (mul_nonneg hW0 (norm_nonneg _)) h2 2
    exact le_trans h3 (add_sq_le_two_mul _ _)
  have hs := Finset.sum_le_sum (s := innerBonds S F.top) fun b _ => hterm b
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs
  rw [bondsOver_self hodd]
  linarith
end SliceNorm
open SliceNorm in
theorem sliceNormRadiusBound (hF : sliceFormCurlBoundStatement) :
    sliceNormRadiusBoundStatement := by
  obtain ⟨c, C, L1, hc, hC, hF⟩ := hF
  intro a ha
  have hKpos : 0 < 2401 * (8 * C ^ 2 + 1) * (1 + 1 / a) := by positivity
  refine ⟨c, 2 * Real.sqrt (2401 * (8 * C ^ 2 + 1) * (1 + 1 / a)), max L1 5, hc,
    mul_pos two_pos (Real.sqrt_pos.2 hKpos), ?_⟩
  intro F m S hodd hLL hamb hm hreg s V hs hsc hcold φ θ del p hθ hdel hφ U hU
  have h5 : 5 ≤ F.blockSide := le_trans (le_max_right _ _) hLL
  have hB := hF F m S hodd (le_trans (le_max_left _ _) hLL) hamb hm hreg s V hs hsc hcold φ θ del p
    hθ hdel hφ U.fine hU
  have hBq := baseOnly_top_weighted_sq_le (S := S) h5 hodd (referenceFieldChain S V) U φ θ del p hθ hdel hφ
  have hX := sum_localNorm_sq_le (S := S) (referenceFieldChain S V) U (classWeight F φ θ p)
  have hP0 : 0 ≤ ∑ q ∈ plaquettesOver S S 0, (classWeight F φ θ p 0 q.1 *
      ‖linearizedCurl (referenceFieldChain S V 0) U.fine q‖) ^ 2 :=
    Finset.sum_nonneg fun q _ => by positivity
  have hMm0 : 0 ≤ ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S S (j + 1),
      (classWeight F φ θ p (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun c _ => by positivity
  have hNu0 : 0 ≤ ∑ c ∈ bondsOver S S F.top, (classWeight F φ θ p F.top c.1 *
      ‖linearPart (referenceFieldChain S V) U F.top c.1 c.2‖) ^ 2 :=
    Finset.sum_nonneg fun c _ => by positivity
  have hBq0 : 0 ≤ ∑ b ∈ innerBonds S F.top, (classWeight F φ θ p F.top b.1 *
      ‖linearPart (referenceFieldChain S V) (baseOnlyChart U.fine) F.top b.1 b.2‖) ^ 2 :=
    Finset.sum_nonneg fun c _ => by positivity
  have hcs0 : 0 ≤ cellwiseL4Norm S (classWeight F φ θ p 0) (fun x i => U.fine x i) := Real.sqrt_nonneg _
  have hb0 : 0 ≤ weightedBondL2Norm S (fun x => classWeight F φ θ p 0 x / scaleRadius F 0 p x)
      (fun x i => U.fine x i) := Real.sqrt_nonneg _
  have hboth : ∀ t : ℝ, 0 ≤ t → t ≤ C * (Real.sqrt (∑ q ∈ plaquettesOver S S 0,
        (classWeight F φ θ p 0 q.1 * ‖linearizedCurl (referenceFieldChain S V 0) U.fine q‖) ^ 2) +
      Real.sqrt (∑ b ∈ innerBonds S F.top, (classWeight F φ θ p F.top b.1 *
        ‖linearPart (referenceFieldChain S V) (baseOnlyChart U.fine) F.top b.1 b.2‖) ^ 2)) →
      t ^ 2 ≤ 2 * C ^ 2 * (∑ q ∈ plaquettesOver S S 0, (classWeight F φ θ p 0 q.1 *
        ‖linearizedCurl (referenceFieldChain S V 0) U.fine q‖) ^ 2 +
      ∑ b ∈ innerBonds S F.top, (classWeight F φ θ p F.top b.1 *
        ‖linearPart (referenceFieldChain S V) (baseOnlyChart U.fine) F.top b.1 b.2‖) ^ 2) := by
    intro t ht h1
    generalize (∑ q ∈ plaquettesOver S S 0, (classWeight F φ θ p 0 q.1 *
        ‖linearizedCurl (referenceFieldChain S V 0) U.fine q‖) ^ 2) = P at hP0 h1 ⊢
    generalize (∑ b ∈ innerBonds S F.top, (classWeight F φ θ p F.top b.1 *
        ‖linearPart (referenceFieldChain S V) (baseOnlyChart U.fine) F.top b.1 b.2‖) ^ 2) = Bq at hBq0 h1 ⊢
    have h2 : t ^ 2 ≤ (C * (Real.sqrt P + Real.sqrt Bq)) ^ 2 := pow_le_pow_left₀ ht h1 2
    have h3 : (Real.sqrt P + Real.sqrt Bq) ^ 2 ≤ 2 * (Real.sqrt P) ^ 2 + 2 * (Real.sqrt Bq) ^ 2 :=
      add_sq_le_two_mul _ _
    rw [Real.sq_sqrt hP0, Real.sq_sqrt hBq0] at h3
    calc t ^ 2 ≤ C ^ 2 * (Real.sqrt P + Real.sqrt Bq) ^ 2 := by rw [← mul_pow]; exact h2
      _ ≤ C ^ 2 * (2 * P + 2 * Bq) := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = _ := by ring
  have hcsle := hboth _ hcs0 (by linarith)
  have hbsle := hboth _ hb0 (by linarith)
  have hfin := combine_bounds a C _ _ _ _ _ _ ha hP0 hMm0 hNu0 hcsle hBq hX
  have hfin2 := combine_bounds
    (X := weightedBondL2Norm S (fun x => classWeight F φ θ p 0 x / scaleRadius F 0 p x)
      (fun x i => U.fine x i) ^ 2) a C _ _ _ _ _ ha hP0 hMm0 hNu0 hbsle hBq
    (by nlinarith [sq_nonneg (weightedBondL2Norm S (fun x => classWeight F φ θ p 0 x / scaleRadius F 0 p x)
      (fun x i => U.fine x i))])
  have h1 : weightedNorm S (referenceFieldChain S V) U (classWeight F φ θ p) ≤
      Real.sqrt (2401 * (8 * C ^ 2 + 1) * (1 + 1 / a)) *
        Real.sqrt (quadraticFormNormSq a S (referenceFieldChain S V) U (classWeight F φ θ p)) := by
    simp only [weightedNorm]
    rw [← Real.sqrt_mul hKpos.le]
    apply Real.sqrt_le_sqrt
    simp only [quadraticFormNormSq]
    exact hfin
  have h2 : weightedBondL2Norm S (fun x => classWeight F φ θ p 0 x / scaleRadius F 0 p x)
      (fun x i => U.fine x i) ≤ Real.sqrt (2401 * (8 * C ^ 2 + 1) * (1 + 1 / a)) *
        Real.sqrt (quadraticFormNormSq a S (referenceFieldChain S V) U (classWeight F φ θ p)) := by
    rw [← Real.sqrt_mul hKpos.le]
    apply Real.le_sqrt_of_sq_le
    simp only [quadraticFormNormSq]
    exact hfin2
  linarith
end YangMills.Construction.BlockAverages
end
