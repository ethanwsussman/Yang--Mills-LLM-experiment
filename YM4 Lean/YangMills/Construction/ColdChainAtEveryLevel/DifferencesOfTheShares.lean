import YangMills.Construction.ColdChainAtEveryLevel.EvaluationsOfTheTerms
import YangMills.Construction.ColdChainAtEveryLevel.SharesAcrossABond
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages.VariationRates
variable {F : BlockFrame} {S : Finset F.Cell}
theorem cutoffProfile_abs (t : ℝ) : cutoffProfile |t| = cutoffProfile t := by
  simp [cutoffProfile]
theorem abs_cutoffProfile_sub_le (s t : ℝ) :
    |cutoffProfile s - cutoffProfile t| ≤ cutoffBound * |s - t| := by apply _root_.YangMills.Construction.CellBumps.cutoffProfile_lipschitz <;> assumption
theorem natAbs_valMinAbs_intCast_le (p : ℕ) (a : ℤ) : ((a : ZMod p).valMinAbs).natAbs ≤ a.natAbs := by apply _root_.YangMills.Construction.BlockWeights.natAbs_valMinAbs_intCast_le <;> assumption
theorem abs_natAbs_valMinAbs_add_sub_le {p : ℕ} (a : ZMod p) (d : ℤ) :
    |(((a + (d : ZMod p)).valMinAbs).natAbs : ℤ) - (a.valMinAbs.natAbs : ℤ)| ≤ |d| := by
  have h1 := (ZMod.natAbs_valMinAbs_add_le a (d : ZMod p)).trans (Int.natAbs_add_le _ _)
  have h2 := (ZMod.natAbs_valMinAbs_add_le (a + (d : ZMod p)) (-(d : ZMod p))).trans (Int.natAbs_add_le _ _)
  rw [add_neg_cancel_right, ZMod.natAbs_valMinAbs_neg] at h2
  have h3 := natAbs_valMinAbs_intCast_le p d
  rw [abs_le]
  rw [Int.abs_eq_natAbs]
  constructor <;> omega
theorem abs_prod_sub_prod_le_sum {a b : Fin 4 → ℝ} (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1)
    (hb : ∀ i, 0 ≤ b i ∧ b i ≤ 1) :
    |∏ i, a i - ∏ i, b i| ≤ ∑ i, |a i - b i| := by apply _root_.YangMills.Construction.BondShares.abs_prod_four_sub_le_sum <;> assumption
theorem cellCutoff_mem_Icc (x : F.Site 0) (z : F.Cell) : 0 ≤ cellCutoff x z ∧ cellCutoff x z ≤ 1 := by
  unfold cellCutoff
  exact ⟨Finset.prod_nonneg fun i _ => cutoffProfile_nonneg _,
    Finset.prod_le_one (fun i _ => cutoffProfile_nonneg _) fun i _ => cutoffProfile_le_one _⟩
theorem abs_cellCutoff_sub_le (hL : 0 < F.blockSide) {r : ℤ} {x x' : F.Site 0} (hw : SupClose r x x')
    (z : F.Cell) :
    |cellCutoff x z - cellCutoff x' z| ≤ 4 * cutoffBound * ((r : ℝ) / (F.blockSide : ℝ) ^ F.top) := by
  obtain ⟨δ, hδ, rfl⟩ := hw
  have hN : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by
    have : (0 : ℝ) < F.blockSide := by exact_mod_cast hL
    positivity
  unfold cellCutoff
  refine (abs_prod_sub_prod_le_sum (fun i => ⟨cutoffProfile_nonneg _, cutoffProfile_le_one _⟩)
    (fun i => ⟨cutoffProfile_nonneg _, cutoffProfile_le_one _⟩)).trans ?_
  have h1 : ∀ i : Fin 4, |cutoffProfile ((((x - cellCentre 0 z : F.Site 0) i).valMinAbs : ℝ) / (F.blockSide : ℝ) ^ F.top) -
      cutoffProfile (((((x + siteOfCoords 0 δ - cellCentre 0 z : F.Site 0)) i).valMinAbs : ℝ) / (F.blockSide : ℝ) ^ F.top)| ≤
      cutoffBound * ((r : ℝ) / (F.blockSide : ℝ) ^ F.top) := by
    intro i
    rw [← cutoffProfile_abs ((((x - cellCentre 0 z : F.Site 0) i).valMinAbs : ℝ) / (F.blockSide : ℝ) ^ F.top),
      ← cutoffProfile_abs (((((x + siteOfCoords 0 δ - cellCentre 0 z : F.Site 0)) i).valMinAbs : ℝ) / (F.blockSide : ℝ) ^ F.top)]
    refine (abs_cutoffProfile_sub_le _ _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (le_trans zero_le_one one_le_cutoffBound)
    rw [abs_div, abs_div, abs_of_pos hN, ← sub_div, abs_div, abs_of_pos hN]
    refine div_le_div_of_nonneg_right ?_ hN.le
    have e : (x + siteOfCoords 0 δ - cellCentre 0 z : F.Site 0) i =
        (x - cellCentre 0 z : F.Site 0) i + ((δ i : ℤ) : ZMod (F.period 0 i)) := by
      simp [siteOfCoords]
      ring
    rw [e]
    have h2 := abs_natAbs_valMinAbs_add_sub_le ((x - cellCentre 0 z : F.Site 0) i) (δ i)
    have h3 : ((|(((x - cellCentre 0 z : F.Site 0) i).valMinAbs : ℤ)| : ℤ) : ℝ) =
        |(((x - cellCentre 0 z : F.Site 0) i).valMinAbs : ℝ)| := by
      push_cast
      rfl
    have h4 := hδ i
    rw [abs_sub_comm]
    have h5 : |((((x - cellCentre 0 z : F.Site 0) i + ((δ i : ℤ) : ZMod (F.period 0 i))).valMinAbs.natAbs : ℤ) : ℤ) -
        ((((x - cellCentre 0 z : F.Site 0) i).valMinAbs.natAbs : ℤ) : ℤ)| ≤ r := h2.trans h4
    have h6 : (|((((x - cellCentre 0 z : F.Site 0) i + ((δ i : ℤ) : ZMod (F.period 0 i))).valMinAbs.natAbs : ℤ) : ℤ) -
        ((((x - cellCentre 0 z : F.Site 0) i).valMinAbs.natAbs : ℤ) : ℤ)| : ℝ) ≤ (r : ℝ) := by exact_mod_cast h5
    refine le_trans (le_of_eq ?_) h6
    congr 1
    simp [Nat.cast_natAbs]
  have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h1 i
  refine this.trans (le_of_eq ?_)
  simp
  ring
theorem one_le_sum_sq_cellCutoff (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {x : F.Site 0}
    (hx : x ∈ sitesOfCells S 0) :
    1 ≤ ∑ y ∈ S, cellCutoff x y ^ 2 := by
  obtain ⟨y, hy, h, hh, rfl⟩ := mem_sitesOfCells.1 hx
  have hb := cellCutoff_self hamb hodd y (h := h) (by simpa using hh)
  refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun y' => cellCutoff (cellCentre 0 y + siteOfCoords 0 h) y' ^ 2)
      (fun _ _ => sq_nonneg _) hy)
  simp [hb]
def partitionBound : ℝ := 2502 * (4 * cutoffBound)
theorem partitionBound_pos : 0 < partitionBound := by
  have := one_le_cutoffBound
  unfold partitionBound
  linarith
theorem abs_cellPartition_sub_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {r : ℤ} (hr : 0 ≤ r)
    {x x' : F.Site 0} (hx : x ∈ sitesOfCells S 0) (hx' : x' ∈ sitesOfCells S 0) (hw : SupClose r x x')
    (z : F.Cell) :
    |cellPartition S x z - cellPartition S x' z| ≤ partitionBound * ((r : ℝ) / (F.blockSide : ℝ) ^ F.top) := by
  classical
  have hL := hodd.pos
  set ε : ℝ := 4 * cutoffBound * ((r : ℝ) / (F.blockSide : ℝ) ^ F.top) with hε
  have hε0 : 0 ≤ ε := by
    have := one_le_cutoffBound
    have h1 : (0 : ℝ) ≤ r := by exact_mod_cast hr
    have h2 : (0 : ℝ) < F.blockSide := by exact_mod_cast hL
    positivity
  have hb : ∀ y, |cellCutoff x y - cellCutoff x' y| ≤ ε := fun y => abs_cellCutoff_sub_le hL hw y
  have hsq : ∀ y, |cellCutoff x y ^ 2 - cellCutoff x' y ^ 2| ≤ 2 * ε := by
    intro y
    have e : cellCutoff x y ^ 2 - cellCutoff x' y ^ 2 =
        (cellCutoff x y - cellCutoff x' y) * (cellCutoff x y + cellCutoff x' y) := by
      ring
    have h1 := cellCutoff_mem_Icc x y
    have h2 := cellCutoff_mem_Icc x' y
    rw [e, abs_mul, abs_of_nonneg (add_nonneg h1.1 h2.1)]
    calc _ ≤ ε * 2 := mul_le_mul (hb y) (by linarith) (by linarith) hε0
      _ = _ := by ring
  set D := ∑ y ∈ S, cellCutoff x y ^ 2 with hD
  set D' := ∑ y ∈ S, cellCutoff x' y ^ 2 with hD'
  have hD1 : 1 ≤ D := one_le_sum_sq_cellCutoff hamb hodd hx
  have hD1' : 1 ≤ D' := one_le_sum_sq_cellCutoff hamb hodd hx'
  obtain ⟨y₀, hy₀, h₀, hh₀, e₀⟩ := mem_sitesOfCells.1 hx
  obtain ⟨y₁, hy₁, h₁, hh₁, e₁⟩ := mem_sitesOfCells.1 hx'
  have hdiff : |D - D'| ≤ 1250 * (2 * ε) := by
    rw [hD, hD', ← Finset.sum_sub_distrib]
    set A := S.filter fun y => cellCutoff x y ≠ 0 with hA
    set B := S.filter fun y => cellCutoff x' y ≠ 0 with hB
    have hcA : A.card ≤ 625 := by
      have := PatchLocality.card_le_of_cellSupDist_le y₀ 2 A fun z hz =>
        PatchLocality.cellSupDist_le_two_of_cellCutoff_ne_zero hamb hodd (Finset.mem_filter.1 hz).2
          (h := h₀) (by simpa using hh₀) e₀
      simpa using this
    have hcB : B.card ≤ 625 := by
      have := PatchLocality.card_le_of_cellSupDist_le y₁ 2 B fun z hz =>
        PatchLocality.cellSupDist_le_two_of_cellCutoff_ne_zero hamb hodd (Finset.mem_filter.1 hz).2
          (h := h₁) (by simpa using hh₁) e₁
      simpa using this
    have hz : ∀ y ∈ S, y ∉ A ∪ B → cellCutoff x y ^ 2 - cellCutoff x' y ^ 2 = 0 := by
      intro y hy hn
      simp only [Finset.mem_union, hA, hB, Finset.mem_filter, not_or, not_and, not_not] at hn
      simp [hn.1 hy, hn.2 hy]
    have hsub : ∑ y ∈ S, (cellCutoff x y ^ 2 - cellCutoff x' y ^ 2) =
        ∑ y ∈ A ∪ B, (cellCutoff x y ^ 2 - cellCutoff x' y ^ 2) := by
      refine (Finset.sum_subset (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)) ?_).symm
      intro y hy hn
      exact hz y hy hn
    rw [hsub]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ (2 * ε) fun y _ => hsq y).trans ?_
    rw [nsmul_eq_mul]
    have hc : ((A ∪ B).card : ℝ) ≤ 1250 := by
      have := Finset.card_union_le A B
      have h2 : (A ∪ B).card ≤ 1250 := by omega
      exact_mod_cast h2
    exact mul_le_mul_of_nonneg_right hc (by linarith)
  have hz1 := cellCutoff_mem_Icc x' z
  have hb1 : cellCutoff x' z ^ 2 ≤ 1 := by nlinarith
  unfold cellPartition
  rw [← hD, ← hD']
  have hDp : 0 < D := by linarith
  have hDp' : 0 < D' := by linarith
  have e : cellCutoff x z ^ 2 / D - cellCutoff x' z ^ 2 / D' =
      (cellCutoff x z ^ 2 - cellCutoff x' z ^ 2) / D + cellCutoff x' z ^ 2 / D' * ((D' - D) / D) := by
    field_simp
    ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_div, abs_mul, abs_div, abs_of_pos hDp, abs_of_pos hDp', abs_of_nonneg (sq_nonneg (cellCutoff x' z))]
  have t1 : |cellCutoff x z ^ 2 - cellCutoff x' z ^ 2| / D ≤ 2 * ε :=
    (div_le_self (abs_nonneg _) hD1).trans (hsq z)
  have t2 : cellCutoff x' z ^ 2 / D' ≤ 1 := (div_le_one hDp').2 (hb1.trans hD1')
  have t3 : |(D' - D) / D| ≤ 1250 * (2 * ε) := by
    rw [abs_div, abs_of_pos hDp, abs_sub_comm]
    exact (div_le_self (abs_nonneg _) hD1).trans hdiff
  have t4 : cellCutoff x' z ^ 2 / D' * |(D' - D) / D| ≤ 1 * (1250 * (2 * ε)) :=
    mul_le_mul t2 t3 (abs_nonneg _) zero_le_one
  have hfin : partitionBound * ((r : ℝ) / (F.blockSide : ℝ) ^ F.top) = 2502 * ε := by
    rw [hε]
    unfold partitionBound
    ring
  rw [hfin]
  linarith
end YangMills.Construction.BlockAverages.VariationRates
end
