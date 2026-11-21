import YangMills.Construction.HoleBesideASecondHole.BlocksOfTheLevels
import YangMills.Construction.ColdChainAtEveryLevel.FirstVariationAtTheReferenceProof
import YangMills.Construction.ColdChainAtEveryLevel.SliceNormWithTheRadiusProof
import YangMills.Construction.ColdChainAtEveryLevel.SmoothWeightsThroughTheCurlProof
import YangMills.Construction.ColdChainAtEveryLevel.WeightsThroughTheAverages
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
namespace WeightAverageCommutator
variable {F : BlockFrame}
theorem natAbs_valMinAbs_intCast_le (n : ℕ) (d : ℤ) : ((d : ZMod n).valMinAbs).natAbs ≤ d.natAbs := by apply _root_.YangMills.Construction.BlockWeights.natAbs_valMinAbs_intCast_le <;> assumption
theorem siteOfCoords_siteCoords {j : ℕ} (y : F.Site j) : siteOfCoords j (siteCoords y) = y := by apply _root_.YangMills.Construction.BlockAverages.siteOfCoords_siteCoords <;> assumption
theorem period_eq {j : ℕ} (i : Fin 4) :
    (F.period j i : ℤ) = (F.extent i : ℤ) * (F.blockSide : ℤ) ^ (F.top - j) := by
  simp [BlockFrame.period]
theorem mem_centredCube (M : ℕ) (h : Fin 4 → ℤ) :
    h ∈ centredCube M ↔ ∀ i, -(((M : ℤ) - 1) / 2) ≤ h i ∧ h i ≤ ((M : ℤ) - 1) / 2 := by apply _root_.YangMills.Construction.LumpContours.CutAction.mem_centredCube <;> assumption
theorem odd_pow_half (hodd : Odd F.blockSide) (e : ℕ) : ∃ k : ℕ, F.blockSide ^ e = 2 * k + 1 ∧
    (((F.blockSide ^ e : ℕ) : ℤ) - 1) / 2 = k ∧ (F.blockSide : ℤ) ^ e = 2 * (k : ℤ) + 1 := by apply _root_.YangMills.Construction.BlockLines.odd_pow_eq_two_mul_add_one <;> assumption
theorem refineSite_add_smul_unitStep {j : ℕ} (y : F.Site (j + 1)) (i : Fin 4) (h : Fin 4 → ℤ) (r : ℕ) :
    _root_.YangMills.Construction.BlockAverages.refineSite y + siteOfCoords j h + (r : ℤ) • unitStep j i =
      _root_.YangMills.Construction.BlockAverages.refineSite y + siteOfCoords j (fun l => h l + if l = i then (r : ℤ) else 0) := by apply _root_.YangMills.Construction.NearlyFlatDifferences.refineSite_add_smul_unitStep <;> assumption
theorem mem_innerBonds_of_line {S : Finset F.Cell} {j : ℕ} (hj : j < F.top) (hodd : Odd F.blockSide)
    (c : F.Site (j + 1) × Fin 4) (hc : c ∈ innerBonds S (j + 1)) (h : Fin 4 → ℤ)
    (hh : h ∈ centredCube F.blockSide) (r : ℕ) (hr : r < F.blockSide) :
    (_root_.YangMills.Construction.BlockAverages.refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2, c.2) ∈ innerBonds S j := by apply _root_.YangMills.Construction.NearlyFlatDifferences.mem_innerBonds_of_line <;> assumption
theorem enclosingCell_siteOfCoords {j : ℕ} (hL : 0 < F.blockSide) (t : Fin 4 → ℤ) :
    enclosingCell (siteOfCoords (F := F) j t) =
      siteOfCoords F.top (fun i => (t i + ((F.blockSide : ℤ) ^ (F.top - j) - 1) / 2) /
        (F.blockSide : ℤ) ^ (F.top - j)) := by apply _root_.YangMills.Construction.BlockAverages.SliceNorm.enclosingCell_siteOfCoords <;> assumption
theorem baseDistance_refineSite_add {j : ℕ} (hj : j < F.top) (y : F.Site (j + 1)) (g : Fin 4 → ℤ)
    (G : ℕ) (hG : ∀ i, (g i).natAbs ≤ G) (p : F.Site 0) :
    baseDistance (_root_.YangMills.Construction.BlockAverages.refineSite y + siteOfCoords j g) p ≤ baseDistance y p + F.blockSide ^ j * G ∧
      baseDistance y p ≤ baseDistance (_root_.YangMills.Construction.BlockAverages.refineSite y + siteOfCoords j g) p + F.blockSide ^ j * G := by apply _root_.YangMills.Construction.WeightedAverages.Chains.baseDistance_refineSite_add <;> assumption
theorem scaleRadius_pos (hL : 0 < F.blockSide) (j : ℕ) (p : F.Site 0) (x : F.Site j) :
    0 < scaleRadius F j p x := by apply _root_.YangMills.Construction.CoordinateSeminorms.scaleRadius_pos <;> assumption
theorem norm_adjointAction (g : UnitQuaternion) (w : ℍ[ℝ]) : ‖adjointAction g w‖ = ‖w‖ := by apply _root_.YangMills.Construction.BlockLines.norm_adjointAction <;> assumption
theorem refineSite_add_injective {j : ℕ} (hj : j < F.top) (hodd : Odd F.blockSide) (y y' : F.Site (j + 1))
    (h h' : Fin 4 → ℤ) (hh : h ∈ centredCube F.blockSide) (hh' : h' ∈ centredCube F.blockSide)
    (e : _root_.YangMills.Construction.BlockAverages.refineSite y + siteOfCoords j h = _root_.YangMills.Construction.BlockAverages.refineSite y' + siteOfCoords j h') :
    y = y' ∧ h = h' := by apply _root_.YangMills.Construction.BlockLines.refineSite_add_injective <;> assumption
variable {S : Finset F.Cell}
def lineBond {j : ℕ} (c : F.Site (j + 1) × Fin 4) (h : Fin 4 → ℤ) (r : ℕ) : F.Site j × Fin 4 :=
  (_root_.YangMills.Construction.BlockAverages.refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2, c.2)
def plainAverage {j : ℕ} (g : F.Site j × Fin 4 → ℝ) (c : F.Site (j + 1) × Fin 4) : ℝ :=
  (1 / (F.blockSide : ℝ) ^ 4) * ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
    g (lineBond c h r)
theorem norm_parallelAverage_le (hL : 0 < F.blockSide) {j : ℕ} (R : F.GaugeField j)
    (f : F.Site j → Fin 4 → ℍ[ℝ]) (c : F.Site (j + 1) × Fin 4) :
    ‖parallelAverage R f c‖ ≤ plainAverage (fun b => ‖f b.1 b.2‖) c := by
  simp only [parallelAverage, norm_smul, plainAverage]
  have h1 : ‖∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), ∑ r ∈ Finset.range F.blockSide,
      _root_.YangMills.Construction.BlockAverages.adjointAction (pathHolonomy R (refineSite c.1) (axisPath h π ++ List.replicate r (c.2, true)))
        (f (_root_.YangMills.Construction.BlockAverages.refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2)‖ ≤
      24 * ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
        ‖f (lineBond c h r).1 (lineBond c h r).2‖ := by
    refine le_trans (norm_sum_le _ _) ?_
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro h _
    refine le_trans (norm_sum_le _ _) ?_
    have h2 : ∀ π : Equiv.Perm (Fin 4), ‖∑ r ∈ Finset.range F.blockSide,
        _root_.YangMills.Construction.BlockAverages.adjointAction (pathHolonomy R (refineSite c.1) (axisPath h π ++ List.replicate r (c.2, true)))
          (f (_root_.YangMills.Construction.BlockAverages.refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2)‖ ≤
        ∑ r ∈ Finset.range F.blockSide, ‖f (lineBond c h r).1 (lineBond c h r).2‖ := by
      intro π
      refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
      apply Finset.sum_congr rfl
      intro r _
      rw [norm_adjointAction]
      rfl
    refine le_trans (Finset.sum_le_sum fun π _ => h2 π) (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    simp [Nat.factorial]
  have h3 : ‖(1 / (24 * (F.blockSide : ℝ) ^ 4))‖ = 1 / (24 * (F.blockSide : ℝ) ^ 4) := by
    rw [Real.norm_of_nonneg (by positivity)]
  rw [h3]
  calc 1 / (24 * (F.blockSide : ℝ) ^ 4) * _ ≤ 1 / (24 * (F.blockSide : ℝ) ^ 4) *
        (24 * ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
          ‖f (lineBond c h r).1 (lineBond c h r).2‖) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by field_simp
open Classical in
def readCount {i : ℕ} (c : F.Site (i + 1) × Fin 4) (b : F.Site i × Fin 4) : ℝ :=
  ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
    if lineBond c h r = b then (1 : ℝ) else 0
def averageTranspose (S : Finset F.Cell) {i : ℕ} (κ : F.Site (i + 1) × Fin 4 → ℝ)
    (b : F.Site i × Fin 4) : ℝ :=
  ∑ c ∈ innerBonds S (i + 1), κ c * ((1 / (F.blockSide : ℝ) ^ 4) * readCount c b)
theorem readCount_nonneg {i : ℕ} (c : F.Site (i + 1) × Fin 4) (b : F.Site i × Fin 4) :
    0 ≤ readCount c b := by
  classical
  simp only [readCount]
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
theorem sum_lineBond_eq_sum_readCount {i : ℕ} (hi : i < F.top) (hodd : Odd F.blockSide)
    (c : F.Site (i + 1) × Fin 4) (hc : c ∈ innerBonds S (i + 1)) (g : F.Site i × Fin 4 → ℝ) :
    ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide, g (lineBond c h r) =
      ∑ b ∈ innerBonds S i, readCount c b * g b := by
  classical
  simp only [readCount, Finset.sum_mul]
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  have hm : lineBond c h r ∈ innerBonds S i :=
    mem_innerBonds_of_line hi hodd c hc h hh r (Finset.mem_range.1 hr)
  rw [if_pos hm]
theorem averageTranspose_pairing {i : ℕ} (hi : i < F.top) (hodd : Odd F.blockSide)
    (κ : F.Site (i + 1) × Fin 4 → ℝ) (g : F.Site i × Fin 4 → ℝ) :
    ∑ c ∈ innerBonds S (i + 1), κ c * plainAverage g c =
      ∑ b ∈ innerBonds S i, averageTranspose S κ b * g b := by
  simp only [averageTranspose, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  simp only [plainAverage]
  rw [sum_lineBond_eq_sum_readCount hi hodd c hc, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring
theorem sum_readCount_le {i : ℕ} (hi : i < F.top) (hodd : Odd F.blockSide) (b : F.Site i × Fin 4) :
    ∑ c ∈ innerBonds S (i + 1), readCount c b ≤ F.blockSide := by
  classical
  simp only [readCount]
  have hswap : ∑ c ∈ innerBonds S (i + 1), ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
      (if lineBond c h r = b then (1 : ℝ) else 0) =
      ∑ r ∈ Finset.range F.blockSide, ∑ z ∈ innerBonds S (i + 1) ×ˢ centredCube F.blockSide,
        (if lineBond z.1 z.2 r = b then (1 : ℝ) else 0) := by
    calc _ = ∑ c ∈ innerBonds S (i + 1), ∑ r ∈ Finset.range F.blockSide, ∑ h ∈ centredCube F.blockSide,
          (if lineBond c h r = b then (1 : ℝ) else 0) :=
          Finset.sum_congr rfl fun c _ => Finset.sum_comm
      _ = ∑ r ∈ Finset.range F.blockSide, ∑ c ∈ innerBonds S (i + 1), ∑ h ∈ centredCube F.blockSide,
          (if lineBond c h r = b then (1 : ℝ) else 0) := Finset.sum_comm
      _ = _ := by
          apply Finset.sum_congr rfl
          intro r _
          rw [Finset.sum_product]
  rw [hswap]
  have hone : ∀ r ∈ Finset.range F.blockSide, ∑ z ∈ innerBonds S (i + 1) ×ˢ centredCube F.blockSide,
      (if lineBond z.1 z.2 r = b then (1 : ℝ) else 0) ≤ 1 := by
    intro r _
    rw [Finset.sum_boole]
    have hc : ((innerBonds S (i + 1) ×ˢ centredCube F.blockSide).filter
        fun z => lineBond z.1 z.2 r = b).card ≤ 1 := by
      apply Finset.card_le_one.2
      intro z hz z' hz'
      obtain ⟨hz1, hz2⟩ := Finset.mem_filter.1 hz
      obtain ⟨hz1', hz2'⟩ := Finset.mem_filter.1 hz'
      obtain ⟨h1, h2⟩ := Finset.mem_product.1 hz1
      obtain ⟨h1', h2'⟩ := Finset.mem_product.1 hz1'
      have e := hz2.trans hz2'.symm
      have e' := Prod.ext_iff.1 e
      have e1 : _root_.YangMills.Construction.BlockAverages.refineSite z.1.1 + siteOfCoords i z.2 + (r : ℤ) • unitStep i z.1.2 =
          _root_.YangMills.Construction.BlockAverages.refineSite z'.1.1 + siteOfCoords i z'.2 + (r : ℤ) • unitStep i z'.1.2 := e'.1
      have e2 : z.1.2 = z'.1.2 := e'.2
      rw [e2] at e1
      have e3 := add_right_cancel e1
      obtain ⟨hy, hh⟩ := refineSite_add_injective hi hodd z.1.1 z'.1.1 z.2 z'.2 h2 h2' e3
      exact Prod.ext (Prod.ext hy e2) hh
    exact_mod_cast hc
  calc _ ≤ ∑ _r ∈ Finset.range F.blockSide, (1 : ℝ) := Finset.sum_le_sum hone
    _ = F.blockSide := by simp
structure IsDescentKernel (c₀ : F.Site F.top × Fin 4) (i : ℕ) (κ : F.Site i × Fin 4 → ℝ) : Prop where
  nonneg : ∀ b, 0 ≤ κ b
  bounded : ∀ b, κ b ≤ (1 / (F.blockSide : ℝ) ^ 3) ^ (F.top - i)
  localized : ∀ b, κ b ≠ 0 →
    baseDistance b.1 (baseSite c₀.1) + 3 * F.blockSide ^ i ≤ 3 * F.blockSide ^ F.top
theorem IsDescentKernel.averageTranspose (h5 : 5 ≤ F.blockSide) (hodd : Odd F.blockSide)
    {c₀ : F.Site F.top × Fin 4} {i : ℕ} (hi : i < F.top) {κ : F.Site (i + 1) × Fin 4 → ℝ}
    (hκ : IsDescentKernel c₀ (i + 1) κ) :
    IsDescentKernel c₀ i (WeightAverageCommutator.averageTranspose S κ) := by
  classical
  refine ⟨fun b => ?_, fun b => ?_, fun b hb => ?_⟩
  · simp only [WeightAverageCommutator.averageTranspose]
    exact Finset.sum_nonneg fun c _ => mul_nonneg (hκ.nonneg c)
      (mul_nonneg (by positivity) (readCount_nonneg c b))
  · have hA : (0 : ℝ) ≤ (1 / (F.blockSide : ℝ) ^ 3) ^ (F.top - (i + 1)) := by positivity
    calc WeightAverageCommutator.averageTranspose S κ b ≤
          ∑ c ∈ innerBonds S (i + 1), (1 / (F.blockSide : ℝ) ^ 3) ^ (F.top - (i + 1)) *
            ((1 / (F.blockSide : ℝ) ^ 4) * readCount c b) := by
          apply Finset.sum_le_sum
          intro c _
          exact mul_le_mul_of_nonneg_right (hκ.bounded c)
            (mul_nonneg (by positivity) (readCount_nonneg c b))
      _ = (1 / (F.blockSide : ℝ) ^ 3) ^ (F.top - (i + 1)) * (1 / (F.blockSide : ℝ) ^ 4) *
            ∑ c ∈ innerBonds S (i + 1), readCount c b := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro c _
          ring
      _ ≤ (1 / (F.blockSide : ℝ) ^ 3) ^ (F.top - (i + 1)) * (1 / (F.blockSide : ℝ) ^ 4) * F.blockSide :=
          mul_le_mul_of_nonneg_left (sum_readCount_le hi hodd b) (by positivity)
      _ = (1 / (F.blockSide : ℝ) ^ 3) ^ (F.top - i) := by
          have e : F.top - i = (F.top - (i + 1)) + 1 := by omega
          have e3 : (1 / (F.blockSide : ℝ) ^ 4) * F.blockSide = 1 / (F.blockSide : ℝ) ^ 3 := by field_simp
          rw [e, pow_succ (1 / (F.blockSide : ℝ) ^ 3) (F.top - (i + 1)), mul_assoc, e3]
  · obtain ⟨c, hc, hne⟩ : ∃ c ∈ innerBonds S (i + 1),
        κ c * ((1 / (F.blockSide : ℝ) ^ 4) * readCount c b) ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hb (Finset.sum_eq_zero hall)
    have hκc : κ c ≠ 0 := left_ne_zero_of_mul hne
    have hrc : readCount c b ≠ 0 := right_ne_zero_of_mul (right_ne_zero_of_mul hne)
    obtain ⟨h, hh, hne2⟩ : ∃ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
        (if lineBond c h r = b then (1 : ℝ) else 0) ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hrc (Finset.sum_eq_zero hall)
    obtain ⟨r, hr, hne3⟩ : ∃ r ∈ Finset.range F.blockSide,
        (if lineBond c h r = b then (1 : ℝ) else 0) ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hne2 (Finset.sum_eq_zero hall)
    have hb' : lineBond c h r = b := by
      by_contra hcon
      simp [hcon] at hne3
    subst hb'
    have hrl : r < F.blockSide := Finset.mem_range.1 hr
    have hcube := (mem_centredCube _ _).1 hh
    obtain ⟨k, hk1, hk2, hk3⟩ := odd_pow_half hodd 1
    rw [pow_one] at hk1 hk2 hk3
    have hsite : (lineBond c h r).1 =
        _root_.YangMills.Construction.BlockAverages.refineSite c.1 + siteOfCoords i (fun l => h l + if l = c.2 then (r : ℤ) else 0) :=
      refineSite_add_smul_unitStep c.1 c.2 h r
    have hG : ∀ l, ((fun l => h l + if l = c.2 then (r : ℤ) else 0) l).natAbs ≤ 2 * F.blockSide := by
      intro l
      have h1 := hcube l
      rw [hk2] at h1
      by_cases hl : l = c.2
      · simp only [hl, if_true]
        have h2 := hcube c.2
        rw [hk2] at h2
        omega
      · simp only [if_neg hl, add_zero]
        omega
    obtain ⟨hd1, _⟩ := baseDistance_refineSite_add hi c.1 _ (2 * F.blockSide) hG (baseSite c₀.1)
    rw [hsite]
    have hn := hκ.localized c hκc
    have hpw : F.blockSide ^ (i + 1) = F.blockSide ^ i * F.blockSide := pow_succ _ _
    rw [hpw] at hn
    have hmul : 3 * F.blockSide ^ i ≤ F.blockSide ^ i * F.blockSide := by
      have : F.blockSide ^ i * 3 ≤ F.blockSide ^ i * F.blockSide := Nat.mul_le_mul_left _ (by omega)
      linarith
    nlinarith
theorem telescope_levels (h5 : 5 ≤ F.blockSide) (hodd : Odd F.blockSide) (c₀ : F.Site F.top × Fin 4)
    (hc₀ : c₀ ∈ innerBonds S F.top) (E : (i : ℕ) → F.Site i × Fin 4 → ℝ)
    (m : (i : ℕ) → F.Site (i + 1) × Fin 4 → ℝ) (B : ℕ → ℝ)
    (hE : ∀ i, i < F.top → ∀ b ∈ innerBonds S (i + 1), E (i + 1) b ≤ plainAverage (E i) b + m i b)
    (hB : ∀ i, i < F.top → ∀ κ, IsDescentKernel c₀ (i + 1) κ →
      ∑ b ∈ innerBonds S (i + 1), κ b * m i b ≤ B i) :
    ∃ κ, IsDescentKernel c₀ 0 κ ∧
      E F.top c₀ ≤ ∑ b ∈ innerBonds S 0, κ b * E 0 b + ∑ i ∈ Finset.range F.top, B i := by
  classical
  have key : ∀ d i, i + d = F.top → ∃ κ, IsDescentKernel c₀ i κ ∧
      E F.top c₀ ≤ ∑ b ∈ innerBonds S i, κ b * E i b + ∑ l ∈ Finset.Ico i F.top, B l := by
    intro d
    induction d with
    | zero =>
      intro i hi
      obtain rfl : i = F.top := by omega
      refine ⟨fun b => if b = c₀ then 1 else 0, ⟨fun b => by split_ifs <;> norm_num, fun b => ?_,
        fun b hb => ?_⟩, ?_⟩
      · simp only [Nat.sub_self, pow_zero]
        split_ifs <;> norm_num
      · have : b = c₀ := by
          by_contra hcon
          simp [hcon] at hb
        subst this
        have e : baseSite b.1 - baseSite b.1 = (0 : F.Site 0) := sub_self _
        have hz : baseDistance b.1 (baseSite b.1) = 0 := by
          simp only [baseDistance, e]
          simp
        rw [hz]
        omega
      · simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', if_pos hc₀]
        simp
    | succ d ih =>
      intro i hi
      have hlt : i < F.top := by omega
      obtain ⟨κ, hκ, hle⟩ := ih (i + 1) (by omega)
      refine ⟨averageTranspose S κ, IsDescentKernel.averageTranspose h5 hodd hlt hκ, ?_⟩
      have h1 : ∑ b ∈ innerBonds S (i + 1), κ b * E (i + 1) b ≤
          ∑ b ∈ innerBonds S (i + 1), κ b * (plainAverage (E i) b + m i b) :=
        Finset.sum_le_sum fun b hb => mul_le_mul_of_nonneg_left (hE i hlt b hb) (hκ.nonneg b)
      have h2 : ∑ b ∈ innerBonds S (i + 1), κ b * (plainAverage (E i) b + m i b) =
          ∑ b ∈ innerBonds S i, averageTranspose S κ b * E i b +
            ∑ b ∈ innerBonds S (i + 1), κ b * m i b := by
        simp only [mul_add]
        rw [Finset.sum_add_distrib, averageTranspose_pairing hlt hodd]
      have h3 := hB i hlt κ hκ
      have h4 : ∑ l ∈ Finset.Ico i F.top, B l = B i + ∑ l ∈ Finset.Ico (i + 1) F.top, B l :=
        (Finset.sum_eq_sum_Ico_succ_bot hlt _)
      rw [h4]
      linarith
  obtain ⟨κ, hκ, hle⟩ := key F.top 0 (by omega)
  refine ⟨κ, hκ, ?_⟩
  have : Finset.Ico 0 F.top = Finset.range F.top := by
    ext x
    simp
  rw [this] at hle
  exact hle
theorem natAbs_le_baseDistance {l : ℕ} (x : F.Site l) (p : F.Site 0) (i : Fin 4) :
    (((baseSite x - p : F.Site 0) i).valMinAbs).natAbs ≤ baseDistance x p :=
  Finset.le_sup (f := fun i => (((baseSite x - p : F.Site 0) i).valMinAbs).natAbs) (Finset.mem_univ i)
theorem card_le_of_baseDistance_le {l : ℕ} (hl : l ≤ F.top) (hL : 0 < F.blockSide) (X : Finset (F.Site l))
    (p : F.Site 0) (r : ℕ) (hX : ∀ x ∈ X, baseDistance x p ≤ r) :
    X.card ≤ (2 * r / F.blockSide ^ l + 1) ^ 4 := by apply _root_.YangMills.Construction.WeightedAverages.Chains.card_le_of_baseDistance_le <;> assumption
theorem sum_top_div_scaleRadius_le {l : ℕ} (hl : l ≤ F.top) (hL : 0 < F.blockSide)
    (X : Finset (F.Site l)) (p : F.Site 0) (η : ℝ) (h0 : 0 < η) (h1 : η ≤ 1 / 2) :
    ∑ x ∈ X.filter (fun x => scaleRadius F l p x < η * (F.blockSide : ℝ) ^ F.top),
      (F.blockSide : ℝ) ^ F.top / scaleRadius F l p x ≤
        1600 * η ^ 3 * ((F.blockSide : ℝ) ^ (F.top - l)) ^ 4 := by apply _root_.YangMills.Construction.NearlyFlatDifferences.sum_div_scaleRadius_le <;> assumption
theorem cellSupDist_enclosingCell_le {l : ℕ} (hl : l ≤ F.top) (hodd : Odd F.blockSide) (x : F.Site l)
    (y : F.Cell) (h : baseDistance x (baseSite y) ≤ 3 * F.blockSide ^ F.top) :
    cellSupDist (enclosingCell x) y ≤ 3 := by
  simp only [cellSupDist]
  apply Finset.sup_le
  intro i _
  obtain ⟨K, hK1, hK2, hK3⟩ := odd_pow_half hodd (F.top - l)
  set M : ℤ := 2 * (K : ℤ) + 1 with hM
  have hMpos : 0 < M := by omega
  have hRpos : (0 : ℤ) < (F.blockSide : ℤ) ^ l := by
    have : (0 : ℤ) < F.blockSide := by exact_mod_cast hodd.pos
    positivity
  set R₀ : ℤ := (F.blockSide : ℤ) ^ l with hR₀
  have hN : (F.blockSide : ℤ) ^ F.top = R₀ * M := by
    have e : (F.blockSide : ℤ) ^ F.top = R₀ * (F.blockSide : ℤ) ^ (F.top - l) := by
      rw [hR₀, ← pow_add]
      congr 1
      omega
    rw [e, hK3]
  set d : ℤ := ((baseSite x - baseSite y : F.Site 0) i).valMinAbs with hd
  have hdb : d.natAbs ≤ 3 * F.blockSide ^ F.top := le_trans (natAbs_le_baseDistance x (baseSite y) i) h
  set a : ℤ := siteCoords x i with ha
  set b : ℤ := siteCoords y i with hb
  set sd : ℤ := (F.extent i : ℤ) with hsd
  have hxb : (baseSite x : F.Site 0) i = ((R₀ * a : ℤ) : ZMod (F.period 0 i)) := rfl
  have hyb : (baseSite y : F.Site 0) i =
      (((F.blockSide : ℤ) ^ F.top * b : ℤ) : ZMod (F.period 0 i)) := rfl
  have hcd : ((d : ℤ) : ZMod (F.period 0 i)) =
      ((R₀ * a - (F.blockSide : ℤ) ^ F.top * b : ℤ) : ZMod (F.period 0 i)) := by
    rw [hd, ZMod.coe_valMinAbs, Pi.sub_apply, hxb, hyb, Int.cast_sub]
  obtain ⟨q, hq⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 hcd
  rw [period_eq, Nat.sub_zero, hN] at hq
  set d' : ℤ := a - M * b - sd * M * q with hd'
  have hdd : d = R₀ * d' := by
    rw [hN] at *
    rw [hd']
    linear_combination (-1 : ℤ) * hq
  have hdabs : |d'| ≤ 3 * M := by
    have h1 : |d| ≤ 3 * (R₀ * M) := by
      have h2 : ((d.natAbs : ℕ) : ℤ) ≤ ((3 * F.blockSide ^ F.top : ℕ) : ℤ) := by exact_mod_cast hdb
      rw [Int.natCast_natAbs] at h2
      push_cast at h2
      rw [hN] at h2
      exact h2
    rw [hdd, abs_mul, abs_of_pos hRpos] at h1
    have h3 : R₀ * |d'| ≤ R₀ * (3 * M) := by linarith
    exact le_of_mul_le_mul_left h3 hRpos
  obtain ⟨h4, h5⟩ := abs_le.1 hdabs
  set T : ℤ := (d' + K) / M with hT
  have hTb : -3 ≤ T ∧ T ≤ 3 := by
    constructor
    · have : -3 ≤ (d' + K) / M := by
        rw [Int.le_ediv_iff_mul_le hMpos]
        omega
      exact this
    · have : (d' + K) / M < 4 := Int.ediv_lt_of_lt_mul hMpos (by omega)
      omega
  have hcell : (enclosingCell x - y : F.Cell) i = ((T : ℤ) : ZMod (F.period F.top i)) := by
    have e1 : a + K = (d' + K) + M * (b + sd * q) := by
      rw [hd']
      ring
    have e2 : (a + ((F.blockSide : ℤ) ^ (F.top - l) - 1) / 2) / (F.blockSide : ℤ) ^ (F.top - l) =
        b + sd * q + T := by
      rw [hK3]
      have h2 : (2 * (K : ℤ) + 1 - 1) / 2 = K := by omega
      rw [h2, e1, Int.add_mul_ediv_left _ _ hMpos.ne', hT]
      ring
    have hyc : ((b : ℤ) : ZMod (F.period F.top i)) = y i := ZMod.intCast_zmod_cast (y i)
    have hz0 : ((sd * q : ℤ) : ZMod (F.period F.top i)) = 0 := by
      refine (CharP.intCast_eq_zero_iff (ZMod (F.period F.top i)) (F.period F.top i) _).2 ?_
      rw [period_eq]
      simp only [Nat.sub_self, pow_zero, mul_one]
      exact Dvd.intro _ rfl
    have e3 : (enclosingCell x : F.Cell) i = ((b + sd * q + T : ℤ) : ZMod (F.period F.top i)) := by
      rw [← e2]
      rfl
    rw [Pi.sub_apply, e3, Int.cast_add, Int.cast_add, hz0, hyc]
    ring
  rw [Pi.sub_apply] at hcell
  rw [hcell]
  refine le_trans (natAbs_valMinAbs_intCast_le _ _) ?_
  omega
theorem exp_le_one_add_two_mul (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 1 / 2) : Real.exp u ≤ 1 + 2 * u := by apply _root_.YangMills.Construction.BlockAverages.SmoothWeightCurl.exp_le_one_add_two_mul <;> assumption
theorem weightDeviation_sq_le (δ θ t y d D θ₀ η : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) (hδ : |δ| ≤ d)
    (hy1 : Real.exp (-d) ≤ y) (hy2 : y ≤ Real.exp d) (hθ : |θ| ≤ θ₀) (hθ₀ : θ₀ ≤ 1 / 8)
    (hd : d ≤ D / 2) (hD : D ≤ 1 / 8) (hη : 0 < η) (hη1 : η ≤ 1)
    (hθη : θ₀ * Real.log (1 / η) ≤ D / 2) :
    (|(Real.exp δ * t ^ (-θ)) ^ 2 * y ^ 2 - 1| / (Real.exp δ * t ^ (-θ))) ^ 2 ≤
      (16 * D) ^ 2 + if t < η then 36 / t else 0 := by
  have hd0 : 0 ≤ d := le_trans (abs_nonneg _) hδ
  have hD0 : 0 ≤ D := by linarith
  have hθ0 : 0 ≤ θ₀ := le_trans (abs_nonneg _) hθ
  set Lg := Real.log (1 / t) with hLg
  have hLg0 : 0 ≤ Lg := Real.log_nonneg (by rw [le_div_iff₀ ht0]; linarith)
  have hrp : t ^ (-θ) = Real.exp (θ * Lg) := by
    rw [Real.rpow_def_of_pos ht0, hLg, one_div, Real.log_inv]
    congr 1
    ring
  rw [hrp, ← Real.exp_add]
  set A := δ + θ * Lg with hA
  have hθL : |θ * Lg| ≤ θ₀ * Lg := by
    rw [abs_mul, abs_of_nonneg hLg0]
    exact mul_le_mul_of_nonneg_right hθ hLg0
  have hAb : |A| ≤ d + θ₀ * Lg := le_trans (abs_add_le _ _) (add_le_add hδ hθL)
  obtain ⟨hA1, hA2⟩ := abs_le.1 hAb
  have hxpos : 0 < Real.exp A := Real.exp_pos _
  have hypos : 0 < y := lt_of_lt_of_le (Real.exp_pos _) hy1
  by_cases hc : t < η
  · rw [if_pos hc]
    set s := Real.exp (Lg / 2) with hs
    have hs2 : s ^ 2 = 1 / t := by
      rw [hs, ← Real.exp_nat_mul]
      have : ((2 : ℕ) : ℝ) * (Lg / 2) = Lg := by push_cast; ring
      rw [this, hLg, Real.exp_log (by positivity)]
    have hexpd : Real.exp d ≤ 2 := by
      have := exp_le_one_add_two_mul d hd0 (by linarith)
      linarith
    have hθLg : θ₀ * Lg ≤ Lg / 2 := by nlinarith
    have hx1 : Real.exp A ≤ 2 * s := by
      calc Real.exp A ≤ Real.exp (d + Lg / 2) := Real.exp_le_exp.2 (by linarith)
        _ = Real.exp d * s := by rw [Real.exp_add]
        _ ≤ 2 * s := mul_le_mul_of_nonneg_right hexpd (by positivity)
    have hx2 : (Real.exp A)⁻¹ ≤ 2 * s := by
      rw [← Real.exp_neg]
      calc Real.exp (-A) ≤ Real.exp (d + Lg / 2) := Real.exp_le_exp.2 (by linarith)
        _ = Real.exp d * s := by rw [Real.exp_add]
        _ ≤ 2 * s := mul_le_mul_of_nonneg_right hexpd (by positivity)
    have hy3 : y ^ 2 ≤ 2 := by
      have h1 : y ^ 2 ≤ Real.exp d ^ 2 := pow_le_pow_left₀ hypos.le hy2 2
      have h2 : Real.exp d ^ 2 = Real.exp (2 * d) := by
        rw [← Real.exp_nat_mul]
        norm_num
      have h3 := exp_le_one_add_two_mul (2 * d) (by positivity) (by linarith)
      rw [h2] at h1
      linarith
    have hbound : |Real.exp A ^ 2 * y ^ 2 - 1| / Real.exp A ≤ 6 * s := by
      rw [div_le_iff₀ hxpos]
      have ha0 : 0 ≤ Real.exp A ^ 2 * y ^ 2 := by positivity
      have h1 : |Real.exp A ^ 2 * y ^ 2 - 1| ≤ Real.exp A ^ 2 * y ^ 2 + 1 := by
        rw [abs_le]
        constructor <;> linarith
      have h2 : (1 : ℝ) ≤ 2 * s * Real.exp A := by
        have := mul_le_mul_of_nonneg_right hx2 hxpos.le
        rwa [inv_mul_cancel₀ hxpos.ne'] at this
      have h3 : Real.exp A ^ 2 * y ^ 2 ≤ Real.exp A ^ 2 * 2 :=
        mul_le_mul_of_nonneg_left hy3 (sq_nonneg _)
      have h4 : Real.exp A * Real.exp A ≤ 2 * s * Real.exp A :=
        mul_le_mul_of_nonneg_right hx1 hxpos.le
      have h5 : Real.exp A ^ 2 = Real.exp A * Real.exp A := sq _
      rw [h5] at h3
      linarith
    have hh0 : 0 ≤ |Real.exp A ^ 2 * y ^ 2 - 1| / Real.exp A := by positivity
    calc (|Real.exp A ^ 2 * y ^ 2 - 1| / Real.exp A) ^ 2 ≤ (6 * s) ^ 2 := pow_le_pow_left₀ hh0 hbound 2
      _ = 36 / t := by rw [mul_pow, hs2]; ring
      _ ≤ _ := by linarith [sq_nonneg (16 * D)]
  · rw [if_neg hc, add_zero]
    push Not at hc
    have hLη : Lg ≤ Real.log (1 / η) := by
      apply Real.log_le_log (by positivity)
      exact one_div_le_one_div_of_le hη hc
    have hθL2 : θ₀ * Lg ≤ D / 2 := le_trans (mul_le_mul_of_nonneg_left hLη hθ0) hθη
    have hA3 : |A| ≤ D := by
      rw [abs_le]
      constructor <;> linarith
    obtain ⟨hA4, hA5⟩ := abs_le.1 hA3
    have hprod : Real.exp A ^ 2 * y ^ 2 = (Real.exp A * y) ^ 2 := by ring
    have hup : Real.exp A * y ≤ Real.exp (2 * D) := by
      calc Real.exp A * y ≤ Real.exp D * Real.exp D :=
            mul_le_mul (Real.exp_le_exp.2 hA5) (le_trans hy2 (Real.exp_le_exp.2 (by linarith)))
              hypos.le (Real.exp_pos _).le
        _ = Real.exp (2 * D) := by rw [← Real.exp_add]; ring_nf
    have hlo : Real.exp (-(2 * D)) ≤ Real.exp A * y := by
      calc Real.exp (-(2 * D)) = Real.exp (-D) * Real.exp (-D) := by rw [← Real.exp_add]; ring_nf
        _ ≤ Real.exp A * y :=
            mul_le_mul (Real.exp_le_exp.2 hA4) (le_trans (Real.exp_le_exp.2 (by linarith)) hy1)
              (Real.exp_pos _).le hxpos.le
    have hsq1 : (Real.exp A * y) ^ 2 ≤ Real.exp (4 * D) := by
      calc (Real.exp A * y) ^ 2 ≤ Real.exp (2 * D) ^ 2 :=
            pow_le_pow_left₀ (by positivity) hup 2
        _ = Real.exp (4 * D) := by rw [← Real.exp_nat_mul]; norm_num; ring_nf
    have hsq2 : Real.exp (-(4 * D)) ≤ (Real.exp A * y) ^ 2 := by
      calc Real.exp (-(4 * D)) = Real.exp (-(2 * D)) ^ 2 := by
            rw [← Real.exp_nat_mul]; norm_num; ring_nf
        _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le hlo 2
    have h4a := exp_le_one_add_two_mul (4 * D) (by positivity) (by linarith)
    have h4b := Real.add_one_le_exp (-(4 * D))
    have habs : |Real.exp A ^ 2 * y ^ 2 - 1| ≤ 8 * D := by
      rw [hprod, abs_le]
      constructor <;> linarith
    have hinv : (Real.exp A)⁻¹ ≤ 2 := by
      rw [← Real.exp_neg]
      have := exp_le_one_add_two_mul D hD0 (by linarith)
      have h5 : Real.exp (-A) ≤ Real.exp D := Real.exp_le_exp.2 (by linarith)
      linarith
    have hbound : |Real.exp A ^ 2 * y ^ 2 - 1| / Real.exp A ≤ 16 * D := by
      rw [div_eq_mul_inv]
      calc _ ≤ 8 * D * 2 := mul_le_mul habs hinv (by positivity) (by positivity)
        _ = 16 * D := by ring
    have hh0 : 0 ≤ |Real.exp A ^ 2 * y ^ 2 - 1| / Real.exp A := by positivity
    exact pow_le_pow_left₀ hh0 hbound 2
def nearBonds (S : Finset F.Cell) (l : ℕ) (c₀ : F.Site F.top × Fin 4) : Finset (F.Site l × Fin 4) :=
  (innerBonds S l).filter fun b => baseDistance b.1 (baseSite c₀.1) ≤ 3 * F.blockSide ^ F.top
theorem blockSide_pow_top_eq {l : ℕ} (hl : l ≤ F.top) :
    F.blockSide ^ F.top = F.blockSide ^ l * F.blockSide ^ (F.top - l) := by
  rw [← pow_add]
  congr 1
  omega
theorem card_nearSites_le {l : ℕ} (hl : l ≤ F.top) (hL : 0 < F.blockSide) (c₀ : F.Site F.top × Fin 4) :
    ((((nearBonds S l c₀).image Prod.fst).card : ℕ) : ℝ) ≤
      2401 * ((F.blockSide : ℝ) ^ (F.top - l)) ^ 4 := by
  classical
  have h := card_le_of_baseDistance_le hl hL ((nearBonds S l c₀).image Prod.fst) (baseSite c₀.1)
    (3 * F.blockSide ^ F.top) (by
      intro x hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hx
      exact (Finset.mem_filter.1 hb).2)
  have hpos : 0 < F.blockSide ^ l := by positivity
  have e : 2 * (3 * F.blockSide ^ F.top) / F.blockSide ^ l = 6 * F.blockSide ^ (F.top - l) := by
    rw [blockSide_pow_top_eq hl]
    have : 2 * (3 * (F.blockSide ^ l * F.blockSide ^ (F.top - l))) =
        (6 * F.blockSide ^ (F.top - l)) * F.blockSide ^ l := by ring
    rw [this]
    exact Nat.mul_div_cancel _ hpos
  rw [e] at h
  have hM : 1 ≤ F.blockSide ^ (F.top - l) := Nat.one_le_pow _ _ hL
  have h2 : (6 * F.blockSide ^ (F.top - l) + 1) ^ 4 ≤ 2401 * (F.blockSide ^ (F.top - l)) ^ 4 := by
    calc (6 * F.blockSide ^ (F.top - l) + 1) ^ 4 ≤ (7 * F.blockSide ^ (F.top - l)) ^ 4 :=
          Nat.pow_le_pow_left (by omega) 4
      _ = _ := by rw [mul_pow]; norm_num
  have h3 := le_trans h h2
  exact_mod_cast h3
theorem sum_nearBonds_le {l : ℕ} (c₀ : F.Site F.top × Fin 4) (G : F.Site l → ℝ) (hG : ∀ x, 0 ≤ G x) :
    ∑ b ∈ nearBonds S l c₀, G b.1 ≤ 4 * ∑ x ∈ (nearBonds S l c₀).image Prod.fst, G x := by
  classical
  calc ∑ b ∈ nearBonds S l c₀, G b.1
      ≤ ∑ z ∈ (nearBonds S l c₀).image Prod.fst ×ˢ (Finset.univ : Finset (Fin 4)), G z.1 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro b hb
          exact Finset.mem_product.2 ⟨Finset.mem_image_of_mem _ hb, Finset.mem_univ _⟩
        · intro z _ _
          exact hG _
    _ = 4 * ∑ x ∈ (nearBonds S l c₀).image Prod.fst, G x := by
        rw [Finset.sum_product]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [Finset.mul_sum]
        norm_num
theorem sum_nearBonds_le_of_radial {l : ℕ} (hl : l ≤ F.top) (hL : 0 < F.blockSide)
    (c₀ : F.Site F.top × Fin 4) (p : F.Site 0) (η A B : ℝ) (h0 : 0 < η) (h1 : η ≤ 1 / 2) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (G : F.Site l → ℝ) (hG0 : ∀ x, 0 ≤ G x)
    (hG : ∀ x ∈ (nearBonds S l c₀).image Prod.fst, G x ≤ A +
      if scaleRadius F l p x < η * (F.blockSide : ℝ) ^ F.top then
        B * ((F.blockSide : ℝ) ^ F.top / scaleRadius F l p x) else 0) :
    ∑ b ∈ nearBonds S l c₀, G b.1 ≤ (9604 * A + 6400 * B * η ^ 3) * ((F.blockSide : ℝ) ^ (F.top - l)) ^ 4 := by
  classical
  set X := (nearBonds S l c₀).image Prod.fst with hX
  have hs := sum_top_div_scaleRadius_le hl hL X p η h0 h1
  have hcard := card_nearSites_le (S := S) hl hL c₀
  have h2 : ∑ x ∈ X, G x ≤ ∑ x ∈ X, (A + if scaleRadius F l p x < η * (F.blockSide : ℝ) ^ F.top then
      B * ((F.blockSide : ℝ) ^ F.top / scaleRadius F l p x) else 0) := Finset.sum_le_sum hG
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.sum_filter, ← Finset.mul_sum] at h2
  have h3 := sum_nearBonds_le (S := S) c₀ G hG0
  have h4 : (X.card : ℝ) * A ≤ 2401 * ((F.blockSide : ℝ) ^ (F.top - l)) ^ 4 * A :=
    mul_le_mul_of_nonneg_right hcard hA
  have h5 := mul_le_mul_of_nonneg_left hs hB
  nlinarith
theorem kernel_sum_le_sqrt_mul_sqrt {c₀ : F.Site F.top × Fin 4} {l : ℕ} {κ : F.Site l × Fin 4 → ℝ}
    (hκ : IsDescentKernel c₀ l κ) (hl : l ≤ F.top) (hL : 0 < F.blockSide) (H x : F.Site l × Fin 4 → ℝ)
    (hH : ∀ b, 0 ≤ H b) (hx : ∀ b, 0 ≤ x b) :
    ∑ b ∈ innerBonds S l, κ b * (H b * x b) ≤ (1 / (F.blockSide : ℝ) ^ 3) ^ (F.top - l) *
      (Real.sqrt (∑ b ∈ nearBonds S l c₀, H b ^ 2) * Real.sqrt (∑ b ∈ nearBonds S l c₀, x b ^ 2)) := by
  classical
  have h1 : ∑ b ∈ innerBonds S l, κ b * (H b * x b) = ∑ b ∈ nearBonds S l c₀, κ b * (H b * x b) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro b hb hnb
    have : κ b = 0 := by
      by_contra hcon
      have h2 := hκ.localized b hcon
      exact hnb (Finset.mem_filter.2 ⟨hb, by omega⟩)
    rw [this, zero_mul]
  rw [h1]
  calc ∑ b ∈ nearBonds S l c₀, κ b * (H b * x b)
      ≤ ∑ b ∈ nearBonds S l c₀, (1 / (F.blockSide : ℝ) ^ 3) ^ (F.top - l) * (H b * x b) :=
        Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_right (hκ.bounded b)
          (mul_nonneg (hH b) (hx b))
    _ = (1 / (F.blockSide : ℝ) ^ 3) ^ (F.top - l) * ∑ b ∈ nearBonds S l c₀, H b * x b := by
        rw [Finset.mul_sum]
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _
theorem weightDeviation_identity (Wl Wn w v : ℝ) (h1 : 0 < Wl) (h2 : 0 < Wn) :
    |w ^ 2 - Wn ^ 2| * v = Wn * ((|(Wl / Wn) ^ 2 * (w / Wl) ^ 2 - 1| / (Wl / Wn)) * (Wl * v)) := by
  have e : (Wl / Wn) ^ 2 * (w / Wl) ^ 2 - 1 = (w ^ 2 - Wn ^ 2) / Wn ^ 2 := by
    field_simp
  rw [e, abs_div, abs_of_pos (by positivity : 0 < Wn ^ 2)]
  field_simp
theorem scaleRadius_top (hL : 0 < F.blockSide) (p : F.Site 0) (x : F.Site F.top) :
    scaleRadius F F.top p x = (F.blockSide : ℝ) ^ F.top := by
  simp [scaleRadius]
theorem enclosingCell_top (hL : 0 < F.blockSide) (x : F.Site F.top) : enclosingCell x = x := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.enclosingCell_cell <;> assumption
theorem classWeights_pos (hL : 0 < F.blockSide) (φ : F.Cell → ℝ) (θ : ℝ) (p : F.Site 0) (l : ℕ)
    (x : F.Site l) : 0 < classWeight F φ θ p l x := by apply _root_.YangMills.Construction.NearlyFlatDifferences.classWeight_pos <;> assumption
theorem sum_nearBonds_weightDeviation_sq_le {l : ℕ} (hl : l ≤ F.top) (hodd : Odd F.blockSide)
    (c₀ : F.Site F.top × Fin 4) (φ : F.Cell → ℝ) (θ : ℝ) (p : F.Site 0) (del θ₀ D η e : ℝ) (hη0 : 0 < η)
    (hη1 : η ≤ 1 / 2) (hθ : |θ| ≤ θ₀) (hθ₀ : θ₀ ≤ 1 / 8) (hdel0 : 0 ≤ del) (hd : 3 * del ≤ D / 2)
    (hD : D ≤ 1 / 8) (hθη : θ₀ * Real.log (1 / η) ≤ D / 2)
    (hφ : ∀ y y', |φ y - φ y'| ≤ del * cellSupDist y y')
    (he : 9604 * (16 * D) ^ 2 + 6400 * 36 * η ^ 3 ≤ e ^ 2)
    (y : F.Site l → ℝ)
    (hy : ∀ x ∈ sitesOfCells S l, Real.exp (-(3 * del)) ≤ y x ∧ y x ≤ Real.exp (3 * del)) :
    ∑ b ∈ nearBonds S l c₀,
      (|(classWeight F φ θ p l b.1 / classWeight F φ θ p F.top c₀.1) ^ 2 * y b.1 ^ 2 - 1| /
        (classWeight F φ θ p l b.1 / classWeight F φ θ p F.top c₀.1)) ^ 2 ≤
      e ^ 2 * ((F.blockSide : ℝ) ^ (F.top - l)) ^ 4 := by
  classical
  have hL := hodd.pos
  have hN : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by positivity
  set W := classWeight F φ θ p with hW
  have hmom := sum_nearBonds_le_of_radial (S := S) hl hL c₀ p η ((16 * D) ^ 2) 36 hη0 hη1
    (by positivity) (by norm_num)
    (fun x => (|(W l x / W F.top c₀.1) ^ 2 * y x ^ 2 - 1| / (W l x / W F.top c₀.1)) ^ 2)
    (fun x => by positivity) (by
      intro x hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨hb1, hb2⟩ := Finset.mem_filter.1 hb
      have hbs : b.1 ∈ sitesOfCells S l := by
        simp only [innerBonds, Finset.mem_filter, Finset.mem_product] at hb1
        exact hb1.1.1
      set ρ := scaleRadius F l p b.1 with hρ
      have hρ0 : 0 < ρ := scaleRadius_pos hL l p b.1
      have hρN : ρ ≤ (F.blockSide : ℝ) ^ F.top := min_le_left _ _
      set t := ρ / (F.blockSide : ℝ) ^ F.top with ht
      have ht0 : 0 < t := by positivity
      have ht1 : t ≤ 1 := by
        rw [ht, div_le_one hN]
        exact hρN
      set δ := φ (enclosingCell b.1) - φ c₀.1 with hδ
      have hcd := cellSupDist_enclosingCell_le hl hodd b.1 c₀.1 hb2
      have hδb : |δ| ≤ 3 * del := by
        have h1 := hφ (enclosingCell b.1) c₀.1
        have h2 : (cellSupDist (enclosingCell b.1) c₀.1 : ℝ) ≤ 3 := by exact_mod_cast hcd
        calc |δ| ≤ del * (cellSupDist (enclosingCell b.1) c₀.1 : ℝ) := h1
          _ ≤ del * 3 := mul_le_mul_of_nonneg_left h2 hdel0
          _ = 3 * del := by ring
      have hratio : W l b.1 / W F.top c₀.1 = Real.exp δ * t ^ (-θ) := by
        simp only [hW, classWeight]
        rw [scaleRadius_top hL, enclosingCell_top hL, div_self hN.ne', Real.one_rpow, mul_one, hδ,
          Real.exp_sub]
        field_simp
        rfl
      obtain ⟨hy1, hy2⟩ := hy b.1 hbs
      have hdev := weightDeviation_sq_le δ θ t (y b.1) (3 * del) D θ₀ η ht0 ht1 hδb hy1 hy2 hθ hθ₀ hd hD
        hη0 (by linarith) hθη
      rw [← hratio] at hdev
      refine le_trans hdev ?_
      apply add_le_add le_rfl
      have hiff : t < η ↔ ρ < η * (F.blockSide : ℝ) ^ F.top := by
        rw [ht, div_lt_iff₀ hN]
      by_cases hc : t < η
      · rw [if_pos hc, if_pos (hiff.1 hc)]
        apply le_of_eq
        rw [ht]
        field_simp
      · rw [if_neg hc, if_neg (fun h => hc (hiff.2 h))])
  refine le_trans hmom ?_
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  linarith
theorem parallelAverage_sub_smul {j : ℕ} (R : F.GaugeField j) (f g : F.Site j → Fin 4 → ℍ[ℝ]) (lam : ℝ)
    (c : F.Site (j + 1) × Fin 4) :
    parallelAverage R (fun x i => f x i - lam • g x i) c =
      parallelAverage R f c - lam • parallelAverage R g c := by apply _root_.YangMills.Construction.BlockAverages.FirstVariation.parallelAverage_sub_smul <;> assumption
theorem linearPart_step (R : F.FieldChain) (U U' : ChainChart F) (lam : ℝ) (W : F.SiteWeights) (i : ℕ)
    (hU' : ∀ y k, ((U'.coarse i y k : imaginaryQuaternions) : ℍ[ℝ]) =
      (W (i + 1) y ^ 2) • ((U.coarse i y k : imaginaryQuaternions) : ℍ[ℝ]))
    (y : F.Site (i + 1)) (k : Fin 4) :
    linearPart R U' (i + 1) y k - lam • linearPart R U (i + 1) y k =
      parallelAverage (R i) (fun x l => linearPart R U' i x l - lam • linearPart R U i x l) (y, k) +
        if i + 1 < F.top then
          (W (i + 1) y ^ 2 - lam) • ((U.coarse i y k : imaginaryQuaternions) : ℍ[ℝ]) else 0 := by
  rw [parallelAverage_sub_smul]
  simp only [linearPart]
  by_cases h : i + 1 < F.top
  · simp only [if_pos h, hU']
    module
  · simp only [if_neg h]
    module
theorem inv_cube_pow_mul_sq (L : ℝ) (hL : 0 < L) (k : ℕ) : (1 / L ^ 3) ^ k * (L ^ k) ^ 2 = (1 / L) ^ k := by
  rw [div_pow, div_pow, one_pow]
  have e : (L ^ 3) ^ k = (L ^ k) ^ 3 := by rw [← pow_mul, ← pow_mul, mul_comm]
  rw [e]
  field_simp
theorem upper_level_term_le (hL : 0 < F.blockSide) (W : F.SiteWeights)
    (hWp : ∀ (l : ℕ) (x : F.Site l), 0 < W l x) (Wn e : ℝ) (hWn0 : 0 < Wn) (he0 : 0 ≤ e)
    (c₀ : F.Site F.top × Fin 4) (i : ℕ) (hi : i + 1 ≤ F.top) (κ : F.Site (i + 1) × Fin 4 → ℝ)
    (hκ : IsDescentKernel c₀ (i + 1) κ) (μ : F.Site (i + 1) × Fin 4 → ℝ) (hμ : ∀ b, 0 ≤ μ b)
    (hmo : ∑ b ∈ nearBonds S (i + 1) c₀, (|(W (i + 1) b.1 / Wn) ^ 2 * (1 : ℝ) ^ 2 - 1| /
      (W (i + 1) b.1 / Wn)) ^ 2 ≤ e ^ 2 * ((F.blockSide : ℝ) ^ (F.top - (i + 1))) ^ 4) :
    ∑ b ∈ innerBonds S (i + 1), κ b * (|W (i + 1) b.1 ^ 2 - Wn ^ 2| * μ b) ≤
      Wn * (e * ((1 / (F.blockSide : ℝ)) ^ (F.top - (i + 1)) *
        Real.sqrt (∑ b ∈ nearBonds S (i + 1) c₀, (W (i + 1) b.1 * μ b) ^ 2))) := by
  have hLR : (0 : ℝ) < F.blockSide := by exact_mod_cast hL
  have hid : ∀ b : F.Site (i + 1) × Fin 4, |W (i + 1) b.1 ^ 2 - Wn ^ 2| * μ b =
      Wn * ((|(W (i + 1) b.1 / Wn) ^ 2 * (1 : ℝ) ^ 2 - 1| / (W (i + 1) b.1 / Wn)) *
        (W (i + 1) b.1 * μ b)) := by
    intro b
    have h1 := weightDeviation_identity (W (i + 1) b.1) Wn (W (i + 1) b.1) (μ b) (hWp _ _) hWn0
    rw [div_self (hWp _ _).ne'] at h1
    exact h1
  have hcs := kernel_sum_le_sqrt_mul_sqrt (S := S) hκ hi hL
    (fun b => |(W (i + 1) b.1 / Wn) ^ 2 * (1 : ℝ) ^ 2 - 1| / (W (i + 1) b.1 / Wn))
    (fun b => W (i + 1) b.1 * μ b)
    (fun b => by
      have := hWp (i + 1) b.1
      positivity)
    (fun b => mul_nonneg (hWp _ _).le (hμ b))
  have hsq : Real.sqrt (∑ b ∈ nearBonds S (i + 1) c₀, (|(W (i + 1) b.1 / Wn) ^ 2 * (1 : ℝ) ^ 2 - 1| /
      (W (i + 1) b.1 / Wn)) ^ 2) ≤ e * ((F.blockSide : ℝ) ^ (F.top - (i + 1))) ^ 2 := by
    apply Real.sqrt_le_iff.2
    refine ⟨by positivity, ?_⟩
    refine le_trans hmo (le_of_eq ?_)
    ring
  have hpow := inv_cube_pow_mul_sq (F.blockSide : ℝ) hLR (F.top - (i + 1))
  calc ∑ b ∈ innerBonds S (i + 1), κ b * (|W (i + 1) b.1 ^ 2 - Wn ^ 2| * μ b)
      = Wn * ∑ b ∈ innerBonds S (i + 1), κ b * ((|(W (i + 1) b.1 / Wn) ^ 2 * (1 : ℝ) ^ 2 - 1| /
          (W (i + 1) b.1 / Wn)) * (W (i + 1) b.1 * μ b)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        rw [hid]
        ring
    _ ≤ Wn * ((1 / (F.blockSide : ℝ) ^ 3) ^ (F.top - (i + 1)) *
          (Real.sqrt (∑ b ∈ nearBonds S (i + 1) c₀, (|(W (i + 1) b.1 / Wn) ^ 2 * (1 : ℝ) ^ 2 - 1| /
            (W (i + 1) b.1 / Wn)) ^ 2) *
            Real.sqrt (∑ b ∈ nearBonds S (i + 1) c₀, (W (i + 1) b.1 * μ b) ^ 2))) :=
        mul_le_mul_of_nonneg_left hcs hWn0.le
    _ ≤ Wn * ((1 / (F.blockSide : ℝ) ^ 3) ^ (F.top - (i + 1)) *
          ((e * ((F.blockSide : ℝ) ^ (F.top - (i + 1))) ^ 2) *
            Real.sqrt (∑ b ∈ nearBonds S (i + 1) c₀, (W (i + 1) b.1 * μ b) ^ 2))) := by
        apply mul_le_mul_of_nonneg_left _ hWn0.le
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right hsq (Real.sqrt_nonneg _)
    _ = Wn * (e * (((1 / (F.blockSide : ℝ) ^ 3) ^ (F.top - (i + 1)) *
          ((F.blockSide : ℝ) ^ (F.top - (i + 1))) ^ 2) *
          Real.sqrt (∑ b ∈ nearBonds S (i + 1) c₀, (W (i + 1) b.1 * μ b) ^ 2))) := by
        ring
    _ = _ := by rw [hpow]
theorem sqrt_sum_sq_le_sqrt_sqrt_sum_four (hL : 0 < F.blockSide) (c₀ : F.Site F.top × Fin 4)
    (x : F.Site 0 × Fin 4 → ℝ) (hx : ∀ b, 0 ≤ x b) :
    Real.sqrt (∑ b ∈ nearBonds S 0 c₀, x b ^ 2) ≤
      10 * (F.blockSide : ℝ) ^ F.top * Real.sqrt (Real.sqrt (∑ b ∈ nearBonds S 0 c₀, x b ^ 4)) := by
  classical
  have hNp : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by positivity
  generalize hN : (F.blockSide : ℝ) ^ F.top = N at hNp ⊢
  have hZ0 : 0 ≤ ∑ b ∈ nearBonds S 0 c₀, x b ^ 4 := Finset.sum_nonneg fun b _ => by positivity
  have hQ0 : 0 ≤ ∑ b ∈ nearBonds S 0 c₀, x b ^ 2 := Finset.sum_nonneg fun b _ => by positivity
  have hcardn : ((nearBonds S 0 c₀).card : ℝ) ≤ 9604 * N ^ 4 := by
    have h1 := sum_nearBonds_le (S := S) c₀ (fun _ : F.Site 0 => (1 : ℝ)) (fun _ => by norm_num)
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h1
    have h2 := card_nearSites_le (S := S) (Nat.zero_le F.top) hL c₀
    rw [Nat.sub_zero, hN] at h2
    linarith
  have hcsq := sq_sum_le_card_mul_sum_sq (s := nearBonds S 0 c₀) (f := fun b => x b ^ 2)
  have h4 : ∑ b ∈ nearBonds S 0 c₀, (x b ^ 2) ^ 2 = ∑ b ∈ nearBonds S 0 c₀, x b ^ 4 := by
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [h4] at hcsq
  generalize (∑ b ∈ nearBonds S 0 c₀, x b ^ 4) = Z at hZ0 hcsq ⊢
  generalize (∑ b ∈ nearBonds S 0 c₀, x b ^ 2) = Q at hQ0 hcsq ⊢
  set Y := Real.sqrt (Real.sqrt Z) with hY
  have hY2 : Y ^ 2 = Real.sqrt Z := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hY4 : (Y ^ 2) ^ 2 = Z := by rw [hY2, Real.sq_sqrt hZ0]
  have h5 : Q ^ 2 ≤ (98 * N ^ 2 * Y ^ 2) ^ 2 := by
    calc Q ^ 2 ≤ ((nearBonds S 0 c₀).card : ℝ) * Z := hcsq
      _ ≤ 9604 * N ^ 4 * Z := mul_le_mul_of_nonneg_right hcardn hZ0
      _ = _ := by rw [← hY4]; ring
  have h6 : Q ≤ 98 * N ^ 2 * Y ^ 2 := (abs_le_of_sq_le_sq' h5 (by positivity)).2
  apply Real.sqrt_le_iff.2
  refine ⟨by positivity, ?_⟩
  nlinarith
theorem base_level_term_le (hL : 0 < F.blockSide) (W : F.SiteWeights)
    (hWp : ∀ (l : ℕ) (x : F.Site l), 0 < W l x) (ω : F.Site 0 → ℝ) (Wn e : ℝ) (hWn0 : 0 < Wn)
    (he0 : 0 ≤ e) (c₀ : F.Site F.top × Fin 4) (κ : F.Site 0 × Fin 4 → ℝ) (hκ : IsDescentKernel c₀ 0 κ)
    (μ : F.Site 0 × Fin 4 → ℝ) (hμ : ∀ b, 0 ≤ μ b)
    (hmo : ∑ b ∈ nearBonds S 0 c₀, (|(W 0 b.1 / Wn) ^ 2 * (ω b.1 / W 0 b.1) ^ 2 - 1| /
      (W 0 b.1 / Wn)) ^ 2 ≤ e ^ 2 * ((F.blockSide : ℝ) ^ (F.top - 0)) ^ 4) :
    ∑ b ∈ innerBonds S 0, κ b * (|ω b.1 ^ 2 - Wn ^ 2| * μ b) ≤
      Wn * (e * (10 * Real.sqrt (Real.sqrt (∑ b ∈ nearBonds S 0 c₀, (W 0 b.1 * μ b) ^ 4)))) := by
  have hNp : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by positivity
  rw [Nat.sub_zero] at hmo
  have hcs := kernel_sum_le_sqrt_mul_sqrt (S := S) hκ (Nat.zero_le _) hL
    (fun b => |(W 0 b.1 / Wn) ^ 2 * (ω b.1 / W 0 b.1) ^ 2 - 1| / (W 0 b.1 / Wn))
    (fun b => W 0 b.1 * μ b)
    (fun b => by
      have := hWp 0 b.1
      positivity)
    (fun b => mul_nonneg (hWp _ _).le (hμ b))
  rw [Nat.sub_zero] at hcs
  have hsq : Real.sqrt (∑ b ∈ nearBonds S 0 c₀, (|(W 0 b.1 / Wn) ^ 2 * (ω b.1 / W 0 b.1) ^ 2 - 1| /
      (W 0 b.1 / Wn)) ^ 2) ≤ e * ((F.blockSide : ℝ) ^ F.top) ^ 2 := by
    apply Real.sqrt_le_iff.2
    refine ⟨by positivity, ?_⟩
    refine le_trans hmo (le_of_eq ?_)
    ring
  have h24 := sqrt_sum_sq_le_sqrt_sqrt_sum_four (S := S) hL c₀ (fun b => W 0 b.1 * μ b)
    (fun b => mul_nonneg (hWp _ _).le (hμ b))
  have e1 : (1 / (F.blockSide : ℝ) ^ 3) ^ F.top = 1 / ((F.blockSide : ℝ) ^ F.top) ^ 3 := by
    rw [div_pow, one_pow, ← pow_mul, ← pow_mul, mul_comm]
  rw [e1] at hcs
  generalize (F.blockSide : ℝ) ^ F.top = N at hNp hsq h24 hcs
  generalize Real.sqrt (Real.sqrt (∑ b ∈ nearBonds S 0 c₀, (W 0 b.1 * μ b) ^ 4)) = Y at h24 ⊢
  have hQ0 := Real.sqrt_nonneg (∑ b ∈ nearBonds S 0 c₀, (W 0 b.1 * μ b) ^ 2)
  generalize Real.sqrt (∑ b ∈ nearBonds S 0 c₀, (W 0 b.1 * μ b) ^ 2) = Qs at hcs h24 hQ0
  have hH0 := Real.sqrt_nonneg (∑ b ∈ nearBonds S 0 c₀,
    (|(W 0 b.1 / Wn) ^ 2 * (ω b.1 / W 0 b.1) ^ 2 - 1| / (W 0 b.1 / Wn)) ^ 2)
  generalize Real.sqrt (∑ b ∈ nearBonds S 0 c₀, (|(W 0 b.1 / Wn) ^ 2 * (ω b.1 / W 0 b.1) ^ 2 - 1| /
      (W 0 b.1 / Wn)) ^ 2) = Hs at hcs hsq hH0
  calc ∑ b ∈ innerBonds S 0, κ b * (|ω b.1 ^ 2 - Wn ^ 2| * μ b)
      = Wn * ∑ b ∈ innerBonds S 0, κ b * ((|(W 0 b.1 / Wn) ^ 2 * (ω b.1 / W 0 b.1) ^ 2 - 1| /
          (W 0 b.1 / Wn)) * (W 0 b.1 * μ b)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        rw [weightDeviation_identity (W 0 b.1) Wn (ω b.1) (μ b) (hWp _ _) hWn0]
        ring
    _ ≤ Wn * (1 / N ^ 3 * (Hs * Qs)) := mul_le_mul_of_nonneg_left hcs hWn0.le
    _ ≤ Wn * (1 / N ^ 3 * ((e * N ^ 2) * (10 * N * Y))) := by
        apply mul_le_mul_of_nonneg_left _ hWn0.le
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul hsq h24 hQ0 (by positivity)
    _ = Wn * (e * (10 * Y)) := by
        field_simp
theorem top_bond_bound (h5 : 5 ≤ F.blockSide) (hodd : Odd F.blockSide) (R : F.FieldChain) (U : ChainChart F)
    (W : F.SiteWeights) (hWp : ∀ (l : ℕ) (x : F.Site l), 0 < W l x) (ω : F.Site 0 → ℝ) (e : ℝ)
    (he0 : 0 ≤ e) (c₀ : F.Site F.top × Fin 4) (hc₀ : c₀ ∈ innerBonds S F.top)
    (hmo0 : ∑ b ∈ nearBonds S 0 c₀, (|(W 0 b.1 / W F.top c₀.1) ^ 2 * (ω b.1 / W 0 b.1) ^ 2 - 1| /
      (W 0 b.1 / W F.top c₀.1)) ^ 2 ≤ e ^ 2 * ((F.blockSide : ℝ) ^ (F.top - 0)) ^ 4)
    (hmo : ∀ i, i + 1 < F.top → ∑ b ∈ nearBonds S (i + 1) c₀,
      (|(W (i + 1) b.1 / W F.top c₀.1) ^ 2 * (1 : ℝ) ^ 2 - 1| /
        (W (i + 1) b.1 / W F.top c₀.1)) ^ 2 ≤ e ^ 2 * ((F.blockSide : ℝ) ^ (F.top - (i + 1))) ^ 4) :
    (W F.top c₀.1)⁻¹ * ‖linearPart R (chartWeightSq ω W U) F.top c₀.1 c₀.2 -
          (W F.top c₀.1 ^ 2) • linearPart R U F.top c₀.1 c₀.2‖ ≤
      e * (10 * Real.sqrt (Real.sqrt (∑ b ∈ nearBonds S 0 c₀, (W 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4)) +
        ∑ j ∈ Finset.range (F.top - 1), (1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1)) *
          Real.sqrt (∑ b ∈ nearBonds S (j + 1) c₀, (W (j + 1) b.1 * ‖U.coarse j b.1 b.2‖) ^ 2)) := by
  classical
  have hL := hodd.pos
  have hWn0 : 0 < W F.top c₀.1 := hWp _ _
  generalize hWn : W F.top c₀.1 = Wn at hWn0 hmo0 hmo ⊢
  have hstep : ∀ i, i < F.top → ∀ b ∈ innerBonds S (i + 1),
      (fun (i : ℕ) (b : F.Site i × Fin 4) => ‖linearPart R (chartWeightSq ω W U) i b.1 b.2 -
        (Wn ^ 2) • linearPart R U i b.1 b.2‖) (i + 1) b ≤
      plainAverage ((fun (i : ℕ) (b : F.Site i × Fin 4) => ‖linearPart R (chartWeightSq ω W U) i b.1 b.2 -
        (Wn ^ 2) • linearPart R U i b.1 b.2‖) i) b +
      (fun (i : ℕ) (c : F.Site (i + 1) × Fin 4) => if i + 1 < F.top then
        |W (i + 1) c.1 ^ 2 - Wn ^ 2| * ‖U.coarse i c.1 c.2‖ else 0) i b := by
    intro i _ b _
    have h1 := linearPart_step R U (chartWeightSq ω W U) (Wn ^ 2) W i (fun y k => rfl) b.1 b.2
    simp only []
    rw [h1]
    refine le_trans (norm_add_le _ _) (add_le_add (norm_parallelAverage_le hL _ _ _) ?_)
    by_cases h : i + 1 < F.top
    · simp only [if_pos h, norm_smul, Real.norm_eq_abs]
      exact le_rfl
    · simp only [if_neg h, norm_zero]
      exact le_rfl
  have hBd : ∀ i, i < F.top → ∀ κ, IsDescentKernel c₀ (i + 1) κ →
      ∑ b ∈ innerBonds S (i + 1), κ b * (fun (i : ℕ) (c : F.Site (i + 1) × Fin 4) => if i + 1 < F.top then
        |W (i + 1) c.1 ^ 2 - Wn ^ 2| * ‖U.coarse i c.1 c.2‖ else 0) i b ≤
      (fun i => if i + 1 < F.top then Wn * (e * ((1 / (F.blockSide : ℝ)) ^ (F.top - (i + 1)) *
        Real.sqrt (∑ b ∈ nearBonds S (i + 1) c₀, (W (i + 1) b.1 * ‖U.coarse i b.1 b.2‖) ^ 2))) else 0) i := by
    intro i hi κ hκ
    by_cases h : i + 1 < F.top
    · simp only [if_pos h]
      exact upper_level_term_le hL W hWp Wn e hWn0 he0 c₀ i h.le κ hκ (fun b => ‖U.coarse i b.1 b.2‖)
        (fun b => norm_nonneg _) (hmo i h)
    · simp only [if_neg h]
      simp
  obtain ⟨κ, hκ, htel⟩ := telescope_levels h5 hodd c₀ hc₀
    (fun (i : ℕ) (b : F.Site i × Fin 4) => ‖linearPart R (chartWeightSq ω W U) i b.1 b.2 -
        (Wn ^ 2) • linearPart R U i b.1 b.2‖)
    (fun (i : ℕ) (c : F.Site (i + 1) × Fin 4) => if i + 1 < F.top then
        |W (i + 1) c.1 ^ 2 - Wn ^ 2| * ‖U.coarse i c.1 c.2‖ else 0)
    (fun i => if i + 1 < F.top then Wn * (e * ((1 / (F.blockSide : ℝ)) ^ (F.top - (i + 1)) *
        Real.sqrt (∑ b ∈ nearBonds S (i + 1) c₀, (W (i + 1) b.1 * ‖U.coarse i b.1 b.2‖) ^ 2))) else 0)
    hstep hBd
  have hE0 : ∀ b : F.Site 0 × Fin 4, ‖linearPart R (chartWeightSq ω W U) 0 b.1 b.2 -
      (Wn ^ 2) • linearPart R U 0 b.1 b.2‖ = |ω b.1 ^ 2 - Wn ^ 2| * ‖U.fine b.1 b.2‖ := by
    intro b
    simp only [linearPart]
    have h3 : (((chartWeightSq ω W U).fine b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ]) =
        (ω b.1 ^ 2) • ((U.fine b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ]) := rfl
    rw [h3, ← sub_smul, norm_smul, Real.norm_eq_abs]
    rfl
  have hzero := base_level_term_le (S := S) hL W hWp ω Wn e hWn0 he0 c₀ κ hκ (fun b => ‖U.fine b.1 b.2‖)
    (fun b => norm_nonneg _) hmo0
  simp only [hE0] at htel
  have hsumB : ∑ i ∈ Finset.range F.top, (if i + 1 < F.top then
        Wn * (e * ((1 / (F.blockSide : ℝ)) ^ (F.top - (i + 1)) *
          Real.sqrt (∑ b ∈ nearBonds S (i + 1) c₀, (W (i + 1) b.1 * ‖U.coarse i b.1 b.2‖) ^ 2))) else 0) =
      Wn * (e * ∑ j ∈ Finset.range (F.top - 1), (1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1)) *
        Real.sqrt (∑ b ∈ nearBonds S (j + 1) c₀, (W (j + 1) b.1 * ‖U.coarse j b.1 b.2‖) ^ 2)) := by
    change (∑ i ∈ Finset.range (F.depth + 1), _) = _
    rw [Finset.sum_range_succ, if_neg (lt_irrefl _), add_zero]
    have hn1 : F.top - 1 = F.depth := rfl
    rw [hn1, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j + 1 < F.top := by
      have := Finset.mem_range.1 hj
      simp only [BlockFrame.top]
      omega
    rw [if_pos hj']
  rw [hsumB] at htel
  have hinv : 0 ≤ Wn⁻¹ := by positivity
  have h2 := mul_le_mul_of_nonneg_left (le_trans htel (add_le_add_left hzero _)) hinv
  refine le_trans h2 (le_of_eq ?_)
  field_simp
theorem add_sq_le_two_mul (x y : ℝ) : (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
  nlinarith [sq_nonneg (x - y)]
theorem norm_coe_imaginaryQuaternions (x : imaginaryQuaternions) : ‖(x : ℍ[ℝ])‖ = ‖x‖ := rfl
theorem enclosingCell_mem (hodd : Odd F.blockSide) {j : ℕ} (x : F.Site j) (hx : x ∈ sitesOfCells S j) :
    enclosingCell x ∈ S := by apply _root_.YangMills.Construction.BlockLines.enclosingCell_mem <;> assumption
theorem sqrt_sum_le_sum_sqrt {ι : Type} (s : Finset ι) (g : ι → ℝ) (hg : ∀ i, 0 ≤ g i) :
    Real.sqrt (∑ i ∈ s, g i) ≤ ∑ i ∈ s, Real.sqrt (g i) := by apply _root_.YangMills.Construction.BlockAverages.SliceNorm.sqrt_sum_le_sum_sqrt <;> assumption
theorem card_top_bonds_near_le (y : F.Cell) :
    ((innerBonds S F.top).filter fun c => cellSupDist y c.1 ≤ 3).card ≤ 9604 := by
  classical
  set T : Finset ((Fin 4 → ℤ) × Fin 4) :=
    (Fintype.piFinset fun _ => Finset.Icc (-3 : ℤ) 3) ×ˢ Finset.univ with hT
  have hTc : T.card = 9604 := by
    simp [hT, Fintype.card_piFinset]
  rw [← hTc]
  apply Finset.card_le_card_of_injOn (fun c => (fun i => ((y - c.1 : F.Cell) i).valMinAbs, c.2))
  · intro c hc
    have hc' := (Finset.mem_filter.1 (Finset.mem_coe.1 hc)).2
    rw [Finset.mem_coe, hT, Finset.mem_product]
    refine ⟨Fintype.mem_piFinset.2 fun i => ?_, Finset.mem_univ _⟩
    have h1 : (((y - c.1 : F.Cell) i).valMinAbs).natAbs ≤ cellSupDist y c.1 :=
      Finset.le_sup (f := fun i => (((y - c.1 : F.Cell) i).valMinAbs).natAbs) (Finset.mem_univ i)
    rw [Finset.mem_Icc]
    change -3 ≤ ((y - c.1 : F.Cell) i).valMinAbs ∧ ((y - c.1 : F.Cell) i).valMinAbs ≤ 3
    omega
  · intro c _ c' _ e
    have e' := Prod.ext_iff.1 e
    refine Prod.ext ?_ e'.2
    funext i
    have h1 := congrFun e'.1 i
    have h2 := ZMod.injective_valMinAbs h1
    have h3 : (y - c.1 : F.Cell) i = (y - c'.1 : F.Cell) i := h2
    simpa using h3
theorem sum_top_nearBonds_le (hodd : Odd F.blockSide) {l : ℕ} (hl : l ≤ F.top) (g : F.Site l × Fin 4 → ℝ)
    (hg : ∀ b, 0 ≤ g b) :
    ∑ c ∈ innerBonds S F.top, ∑ b ∈ nearBonds S l c, g b ≤ 9604 * ∑ b ∈ innerBonds S l, g b := by
  classical
  simp only [nearBonds, Finset.sum_filter]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b _
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ (hg b)
  have h1 : ((innerBonds S F.top).filter fun c =>
      baseDistance b.1 (baseSite c.1) ≤ 3 * F.blockSide ^ F.top).card ≤
      ((innerBonds S F.top).filter fun c => cellSupDist (enclosingCell b.1) c.1 ≤ 3).card := by
    apply Finset.card_le_card
    intro c hc
    obtain ⟨h2, h3⟩ := Finset.mem_filter.1 hc
    exact Finset.mem_filter.2 ⟨h2, cellSupDist_enclosingCell_le hl hodd b.1 c.1 h3⟩
  have h4 := le_trans h1 (card_top_bonds_near_le (S := S) (enclosingCell b.1))
  exact_mod_cast h4
theorem sum_top_sqrt_nearBonds_le (hodd : Odd F.blockSide) (g : F.Site 0 × Fin 4 → ℝ) (hg : ∀ b, 0 ≤ g b) :
    ∑ c ∈ innerBonds S F.top, Real.sqrt (∑ b ∈ nearBonds S 0 c, g b) ≤
      9604 * ∑ y ∈ S, Real.sqrt (∑ b ∈ bondsOver S {y} 0, g b) := by
  classical
  have hT : ∀ y : F.Cell, 0 ≤ Real.sqrt (∑ b ∈ bondsOver S {y} 0, g b) := fun y => Real.sqrt_nonneg _
  have hone : ∀ c ∈ innerBonds S F.top, Real.sqrt (∑ b ∈ nearBonds S 0 c, g b) ≤
      ∑ y ∈ S.filter (fun y => cellSupDist y c.1 ≤ 3), Real.sqrt (∑ b ∈ bondsOver S {y} 0, g b) := by
    intro c _
    have hmaps : ∀ b ∈ nearBonds S 0 c,
        enclosingCell b.1 ∈ S.filter (fun y => cellSupDist y c.1 ≤ 3) := by
      intro b hb
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hb
      have h3 : b.1 ∈ sitesOfCells S 0 := by
        simp only [innerBonds, Finset.mem_filter, Finset.mem_product] at h1
        exact h1.1.1
      exact Finset.mem_filter.2 ⟨enclosingCell_mem hodd _ h3,
        cellSupDist_enclosingCell_le (Nat.zero_le _) hodd b.1 c.1 h2⟩
    have h1 : ∑ b ∈ nearBonds S 0 c, g b ≤
        ∑ y ∈ S.filter (fun y => cellSupDist y c.1 ≤ 3), ∑ b ∈ bondsOver S {y} 0, g b := by
      rw [← Finset.sum_fiberwise_of_maps_to hmaps]
      apply Finset.sum_le_sum
      intro y _
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro b hb
        obtain ⟨h2, h3⟩ := Finset.mem_filter.1 hb
        have h4 : b ∈ innerBonds S 0 := (Finset.mem_filter.1 h2).1
        simp only [bondsOver, Finset.mem_filter, Finset.mem_singleton]
        exact ⟨h4, h3⟩
      · intro b _ _
        exact hg b
    refine le_trans (Real.sqrt_le_sqrt h1) ?_
    exact sqrt_sum_le_sum_sqrt _ _ fun y => Finset.sum_nonneg fun b _ => hg b
  refine le_trans (Finset.sum_le_sum hone) ?_
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y _
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ (hT y)
  exact_mod_cast card_top_bonds_near_le (S := S) y
theorem sum_geometric_inv_pow_le (m : ℕ) :
    ∑ j ∈ Finset.range m, (1 / 25 : ℝ) ^ (m + 1 - (j + 1)) ≤ 1 / 24 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have e : ∑ j ∈ Finset.range m, (1 / 25 : ℝ) ^ (m + 1 + 1 - (j + 1)) =
        1 / 25 * ∑ j ∈ Finset.range m, (1 / 25 : ℝ) ^ (m + 1 - (j + 1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.1 hj
      have : m + 1 + 1 - (j + 1) = (m + 1 - (j + 1)) + 1 := by omega
      rw [this, pow_succ]
      ring
    rw [e]
    have e2 : m + 1 + 1 - (m + 1) = 1 := by omega
    rw [e2]
    linarith
theorem sq_sum_levels_le (h5 : 5 ≤ F.blockSide) (X : ℕ → ℝ) :
    (∑ j ∈ Finset.range (F.top - 1), (1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1)) * X j) ^ 2 ≤
      ∑ j ∈ Finset.range (F.top - 1), X j ^ 2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (F.top - 1))
    (fun j => (1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1))) X
  have hL : (5 : ℝ) ≤ F.blockSide := by exact_mod_cast h5
  have hq : ∑ j ∈ Finset.range (F.top - 1), ((1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1))) ^ 2 ≤ 1 := by
    have hn1 : F.top - 1 = F.depth := rfl
    rw [hn1]
    have h1 : ∀ j ∈ Finset.range F.depth, ((1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1))) ^ 2 ≤
        (1 / 25 : ℝ) ^ (F.depth + 1 - (j + 1)) := by
      intro j _
      rw [← pow_mul, mul_comm, pow_mul]
      apply pow_le_pow_left₀ (by positivity)
      rw [div_pow, one_pow]
      apply one_div_le_one_div_of_le (by norm_num)
      nlinarith
    have h2 := sum_geometric_inv_pow_le F.depth
    have h3 := Finset.sum_le_sum h1
    linarith
  have hX : 0 ≤ ∑ j ∈ Finset.range (F.top - 1), X j ^ 2 := Finset.sum_nonneg fun j _ => by positivity
  refine le_trans hcs ?_
  nlinarith
end WeightAverageCommutator
open WeightAverageCommutator in
theorem weightAverageCommutator : weightAverageCommutatorStatement := by
  classical
  intro ε hε
  set e : ℝ := ε / 1500 with he
  have he0 : 0 < e := by positivity
  set η : ℝ := min (1 / 2) (e ^ 2 / 500000) with hη
  have hη0 : 0 < η := lt_min (by norm_num) (by positivity)
  have hη1 : η ≤ 1 / 2 := min_le_left _ _
  have hη2 : η ≤ e ^ 2 / 500000 := min_le_right _ _
  set D : ℝ := min (1 / 8) (e / 2300) with hD
  have hD0 : 0 < D := lt_min (by norm_num) (by positivity)
  have hD1 : D ≤ 1 / 8 := min_le_left _ _
  have hD2 : D ≤ e / 2300 := min_le_right _ _
  set del₀ : ℝ := min (1 / 8) (D / 6) with hdel
  have hdel0 : 0 < del₀ := lt_min (by norm_num) (by positivity)
  have hdel1 : del₀ ≤ 1 / 8 := min_le_left _ _
  have hdel2 : del₀ ≤ D / 6 := min_le_right _ _
  set lg : ℝ := Real.log (1 / η) with hlg
  have hlg0 : 0 ≤ lg := Real.log_nonneg (by
    rw [le_div_iff₀ hη0]
    linarith)
  set θ₀ : ℝ := min (1 / 8) (D / (2 * (1 + lg))) with hθ₀d
  have hθ₀0 : 0 < θ₀ := lt_min (by norm_num) (by positivity)
  have hθ₀1 : θ₀ ≤ 1 / 8 := min_le_left _ _
  have hθ₀2 : θ₀ ≤ D / (2 * (1 + lg)) := min_le_right _ _
  have hθη : θ₀ * lg ≤ D / 2 := by
    have h1 : θ₀ * (2 * (1 + lg)) ≤ D := by
      rw [le_div_iff₀ (by positivity)] at hθ₀2
      exact hθ₀2
    nlinarith
  have hmom : 9604 * (16 * D) ^ 2 + 6400 * 36 * η ^ 3 ≤ e ^ 2 := by
    have h1 : D ^ 2 ≤ (e / 2300) ^ 2 := pow_le_pow_left₀ hD0.le hD2 2
    have h2 : η ^ 3 ≤ η := by
      have h3 : η ^ 2 ≤ 1 := by nlinarith
      nlinarith
    nlinarith [sq_nonneg e]
  refine ⟨θ₀, del₀, hθ₀0, hθ₀1, hdel0, hdel1, ?_⟩
  intro F S R hodd h5 φ θ p ω hθ hφ hω U
  have hL := hodd.pos
  generalize hW : classWeight F φ θ p = W at hω ⊢
  have hWp : ∀ (l : ℕ) (x : F.Site l), 0 < W l x := by
    intro l x
    rw [← hW]
    exact classWeights_pos hL φ θ p l x
  have hd3 : 3 * del₀ ≤ D / 2 := by linarith
  have hper : ∀ c₀ ∈ innerBonds S F.top, (W F.top c₀.1)⁻¹ *
        ‖linearPart R (chartWeightSq ω W U) F.top c₀.1 c₀.2 -
          (W F.top c₀.1 ^ 2) • linearPart R U F.top c₀.1 c₀.2‖ ≤
      e * (10 * Real.sqrt (Real.sqrt (∑ b ∈ nearBonds S 0 c₀, (W 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4)) +
        ∑ j ∈ Finset.range (F.top - 1), (1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1)) *
          Real.sqrt (∑ b ∈ nearBonds S (j + 1) c₀, (W (j + 1) b.1 * ‖U.coarse j b.1 b.2‖) ^ 2)) := by
    intro c₀ hc₀
    refine top_bond_bound h5 hodd R U W hWp ω e he0.le c₀ hc₀ ?_ ?_
    · rw [← hW]
      refine sum_nearBonds_weightDeviation_sq_le (S := S) (Nat.zero_le _) hodd c₀ φ θ p del₀ θ₀ D η e
        hη0 hη1 hθ hθ₀1 hdel0.le hd3 hD1 hθη hφ hmom (fun x => ω x / classWeight F φ θ p 0 x) ?_
      intro x hx
      rw [← hW] at hω
      obtain ⟨h1, h2⟩ := hω x hx
      have hw := classWeights_pos hL φ θ p 0 x
      constructor
      · rw [le_div_iff₀ hw]
        refine le_trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) hw.le) h1
      · rw [div_le_iff₀ hw]
        refine le_trans h2 (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) hw.le)
    · intro i hi
      rw [← hW]
      refine sum_nearBonds_weightDeviation_sq_le (S := S) hi.le hodd c₀ φ θ p del₀ θ₀ D η e hη0 hη1 hθ
        hθ₀1 hdel0.le hd3 hD1 hθη hφ hmom (fun _ => 1) ?_
      intro x _
      exact ⟨by
        rw [Real.exp_le_one_iff]
        linarith, Real.one_le_exp (by linarith)⟩
  set cs := cellwiseL4Norm S (W 0) (fun x i => U.fine x i) with hcs
  set Ms := ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ innerBonds S (j + 1),
    (W (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 with hMs
  have hsq : ∀ c₀ ∈ innerBonds S F.top, ((W F.top c₀.1)⁻¹ *
        ‖linearPart R (chartWeightSq ω W U) F.top c₀.1 c₀.2 -
          (W F.top c₀.1 ^ 2) • linearPart R U F.top c₀.1 c₀.2‖) ^ 2 ≤
      e ^ 2 * (200 * Real.sqrt (∑ b ∈ nearBonds S 0 c₀, (W 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4) +
        2 * ∑ j ∈ Finset.range (F.top - 1), ∑ b ∈ nearBonds S (j + 1) c₀,
          (W (j + 1) b.1 * ‖U.coarse j b.1 b.2‖) ^ 2) := by
    intro c₀ hc₀
    have h1 := hper c₀ hc₀
    have h0 : 0 ≤ (W F.top c₀.1)⁻¹ * ‖linearPart R (chartWeightSq ω W U) F.top c₀.1 c₀.2 -
          (W F.top c₀.1 ^ 2) • linearPart R U F.top c₀.1 c₀.2‖ :=
      mul_nonneg (inv_nonneg.2 (hWp _ _).le) (norm_nonneg _)
    have h2 := pow_le_pow_left₀ h0 h1 2
    refine le_trans h2 ?_
    have h3 := sq_sum_levels_le h5 (fun j => Real.sqrt (∑ b ∈ nearBonds S (j + 1) c₀,
      (W (j + 1) b.1 * ‖U.coarse j b.1 b.2‖) ^ 2))
    have h4 : ∑ j ∈ Finset.range (F.top - 1), Real.sqrt (∑ b ∈ nearBonds S (j + 1) c₀,
        (W (j + 1) b.1 * ‖U.coarse j b.1 b.2‖) ^ 2) ^ 2 =
        ∑ j ∈ Finset.range (F.top - 1), ∑ b ∈ nearBonds S (j + 1) c₀,
          (W (j + 1) b.1 * ‖U.coarse j b.1 b.2‖) ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      exact Real.sq_sqrt (Finset.sum_nonneg fun b _ => by positivity)
    rw [h4] at h3
    have hZ0 : 0 ≤ Real.sqrt (∑ b ∈ nearBonds S 0 c₀, (W 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4) :=
      Real.sqrt_nonneg _
    have hY2 : Real.sqrt (Real.sqrt (∑ b ∈ nearBonds S 0 c₀, (W 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4)) ^ 2 =
        Real.sqrt (∑ b ∈ nearBonds S 0 c₀, (W 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4) := Real.sq_sqrt hZ0
    rw [mul_pow]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine le_trans (add_sq_le_two_mul _ _) ?_
    rw [mul_pow, hY2]
    linarith
  have htop1 := sum_top_sqrt_nearBonds_le (S := S) hodd (fun b => (W 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4)
    (fun b => by positivity)
  have hcs2 : ∑ y ∈ S, Real.sqrt (∑ b ∈ bondsOver S {y} 0, (W 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4) = cs ^ 2 := by
    simp only [hcs, cellwiseL4Norm]
    rw [Real.sq_sqrt (Finset.sum_nonneg fun y _ => Real.sqrt_nonneg _)]
    simp only [norm_coe_imaginaryQuaternions]
  rw [hcs2] at htop1
  have htop2 : ∑ c ∈ innerBonds S F.top, ∑ j ∈ Finset.range (F.top - 1), ∑ b ∈ nearBonds S (j + 1) c,
      (W (j + 1) b.1 * ‖U.coarse j b.1 b.2‖) ^ 2 ≤ 9604 * Ms := by
    rw [Finset.sum_comm, hMs, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hj' : j + 1 ≤ F.top := by
      have := Finset.mem_range.1 hj
      simp only [BlockFrame.top] at this ⊢
      omega
    exact sum_top_nearBonds_le (S := S) hodd hj' (fun b => (W (j + 1) b.1 * ‖U.coarse j b.1 b.2‖) ^ 2)
      (fun b => by positivity)
  have hMs0 : 0 ≤ Ms := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun c _ => by positivity
  have hcs0 : 0 ≤ cs ^ 2 := by positivity
  refine le_trans (Finset.sum_le_sum hsq) ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have he2 : e ^ 2 * 2250000 = ε ^ 2 := by
    rw [he]
    ring
  rw [← he2]
  have hee : 0 ≤ e ^ 2 := by positivity
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hee
  linarith
end YangMills.Construction.BlockAverages
end
