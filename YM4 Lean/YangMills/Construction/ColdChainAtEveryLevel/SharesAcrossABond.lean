import YangMills.Construction.ColdChainAtEveryLevel.NormsOfFunctionsOnCells
import YangMills.Construction.ColdChainAtEveryLevel.SharesOfTheCellsAtASite
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BondShares
open BlockAverages GaugeMap PatchPoints LatticeFractionalIntegration FiniteDifferences
variable {F : BlockFrame} {S : Finset F.Cell} {z : F.Cell}
theorem cast_nine_mul_cellSideLength_toNat (hL : 0 < F.blockSide) :
    ((9 * (cellSideLength F).toNat : ℕ) : ℤ) = 9 * cellSideLength F := by
  have := cellSideLength_pos (F := F) hL
  push_cast
  rw [Int.toNat_of_nonneg this.le]
theorem closedOrthant_mul_cellDisplacement_le (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (hL : 0 < F.blockSide) {y : F.Cell} (hd : cellSupDist z y ≤ 10) (i : Fin 4) :
    closedOrthant S z i * cellDisplacement z y i * cellSideLength F ≤ 10 * cellSideLength F := by
  have hN := cellSideLength_pos (F := F) hL
  have h2 := natAbs_valMinAbs_le_cellSupDist y z i
  rw [cellSupDist_symm] at h2
  have h3 : (cellDisplacement z y i).natAbs ≤ 10 := h2.trans hd
  have h4 : |closedOrthant S z i * cellDisplacement z y i| ≤ 10 := by
    rw [abs_mul, abs_closedOrthant he, one_mul, Int.abs_eq_natAbs]
    exact_mod_cast h3
  exact mul_le_mul_of_nonneg_right (abs_le.1 h4).2 hN.le
theorem patchDomain_isFilledToward (hz : z ∈ S) (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (hL : 0 < F.blockSide) :
    IsFilledToward (9 * (cellSideLength F).toNat) (fun _ => 12 * cellSideLength F) (patchDomain S z) := by
  classical
  have hN := cellSideLength_pos (F := F) hL
  have hc9 := cast_nine_mul_cellSideLength_toNat (F := F) hL
  have hself : (fun i => closedOrthant S z i * cellDisplacement z z i * cellSideLength F) ∈ patchCorners S z := by
    refine Finset.mem_image.2 ⟨z, Finset.mem_filter.2 ⟨hz, ?_⟩, rfl⟩
    simp [cellSupDist]
  have hzero : ∀ i, closedOrthant S z i * cellDisplacement z z i * cellSideLength F = 0 := by
    intro i
    simp [cellDisplacement]
  refine ⟨fun q hq => ?_, fun x hx i => ?_, fun x hx q hq y hy => ?_⟩
  · have hqi : ∀ i, 12 * cellSideLength F ≤ q i ∧
        q i < 12 * cellSideLength F + ((9 * (cellSideLength F).toNat : ℕ) : ℤ) :=
      fun i => Finset.mem_Ico.1 (Fintype.mem_piFinset.1 hq i)
    refine Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun i => ?_, ⟨_, hself, fun i => ?_⟩⟩
    · have := hqi i
      rw [hc9] at this
      rw [Finset.mem_Icc]
      constructor <;> omega
    · have := hqi i
      rw [hc9] at this
      rw [hzero]
      omega
  · have h1 := patchDomain_coord_bounds hx i
    rw [hc9, abs_le]
    show -(40 * (9 * cellSideLength F)) ≤ x i - 12 * cellSideLength F ∧
      x i - 12 * cellSideLength F ≤ 40 * (9 * cellSideLength F)
    constructor <;> omega
  · obtain ⟨-, a, ha, hxa⟩ := Finset.mem_filter.1 hx
    obtain ⟨y0, hy0, rfl⟩ := Finset.mem_image.1 ha
    have hy0d := (Finset.mem_filter.1 hy0).2
    have hqi : ∀ i, 12 * cellSideLength F ≤ q i ∧
        q i < 12 * cellSideLength F + ((9 * (cellSideLength F).toNat : ℕ) : ℤ) :=
      fun i => Finset.mem_Ico.1 (Fintype.mem_piFinset.1 hq i)
    refine Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun i => ?_, ⟨_, Finset.mem_image_of_mem _ hy0, fun i => ?_⟩⟩
    · have h1 := patchDomain_coord_bounds hx i
      have h2 := hqi i
      rw [hc9] at h2
      have h3 := hy i
      rw [Finset.mem_Icc]
      have h4 := min_le_iff.1 (le_refl (min (x i) (q i)))
      have h5 := le_max_iff.1 (le_refl (max (x i) (q i)))
      constructor
      · rcases h4 with h4 | h4 <;> omega
      · rcases h5 with h5 | h5 <;> omega
    · have h1 := hxa i
      have h2 := hqi i
      rw [hc9] at h2
      have h3 := hy i
      have h4 := closedOrthant_mul_cellDisplacement_le he hL hy0d i
      have h5 : closedOrthant S z i * cellDisplacement z y0 i * cellSideLength F ≤ min (x i) (q i) :=
        le_min h1 (by omega)
      exact h5.trans h3.1
theorem mem_patchDomain_of_mem_cellOffsets (hz : z ∈ S) (hL : 0 < F.blockSide) {x : Lattice4}
    (hx : x ∈ cellOffsets F) : x ∈ patchDomain S z := by
  classical
  have hN := cellSideLength_pos (F := F) hL
  have hxi := fun i => Finset.mem_Ico.1 (Fintype.mem_piFinset.1 hx i)
  have hself : (fun i => closedOrthant S z i * cellDisplacement z z i * cellSideLength F) ∈ patchCorners S z := by
    refine Finset.mem_image.2 ⟨z, Finset.mem_filter.2 ⟨hz, ?_⟩, rfl⟩
    simp [cellSupDist]
  refine Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun i => ?_, ⟨_, hself, fun i => ?_⟩⟩
  · have := hxi i
    rw [Finset.mem_Icc]
    constructor <;> omega
  · have := hxi i
    simp only [cellDisplacement, sub_self]
    simp
    omega
theorem cutoffProfile_abs_sub_le (u u' : ℝ) :
    |cutoffProfile u - cutoffProfile u'| ≤ cutoffBound * |u - u'| := by apply _root_.YangMills.Construction.CellBumps.cutoffProfile_lipschitz <;> assumption
theorem abs_prod_four_sub_le_sum (a b : Fin 4 → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (hb : ∀ i, 0 ≤ b i ∧ b i ≤ 1) :
    |∏ i, a i - ∏ i, b i| ≤ ∑ i, |a i - b i| := by
  simp only [Fin.prod_univ_four, Fin.sum_univ_four]
  have key : ∀ p q r t : ℝ, 0 ≤ r → r ≤ 1 → 0 ≤ t → t ≤ 1 → |p * r - q * t| ≤ |p - q| * r + |q| * |r - t| := by
    intro p q r t hr0 _ _ _
    have e : p * r - q * t = (p - q) * r + q * (r - t) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hr0]
  obtain ⟨a0, a1⟩ := ha 0
  obtain ⟨b0, b1⟩ := ha 1
  obtain ⟨c0, c1⟩ := ha 2
  obtain ⟨d0, d1⟩ := ha 3
  obtain ⟨e0, e1⟩ := hb 0
  obtain ⟨f0, f1⟩ := hb 1
  obtain ⟨g0, g1⟩ := hb 2
  obtain ⟨h0, h1⟩ := hb 3
  have s1 := key (a 0 * a 1 * a 2) (b 0 * b 1 * b 2) (a 3) (b 3) d0 d1 h0 h1
  have s2 := key (a 0 * a 1) (b 0 * b 1) (a 2) (b 2) c0 c1 g0 g1
  have s3 := key (a 0) (b 0) (a 1) (b 1) b0 b1 f0 f1
  have p1 : |b 0 * b 1 * b 2| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    have h2 : b 0 * b 1 ≤ 1 := mul_le_one₀ e1 f0 f1
    exact mul_le_one₀ h2 g0 g1
  have p2 : |b 0 * b 1| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    exact mul_le_one₀ e1 f0 f1
  have p3 : |b 0| ≤ 1 := by rw [abs_of_nonneg e0]; exact e1
  have n0 := abs_nonneg (a 0 - b 0)
  have n1 := abs_nonneg (a 1 - b 1)
  have n2 := abs_nonneg (a 2 - b 2)
  have n3 := abs_nonneg (a 3 - b 3)
  have n4 := abs_nonneg (a 0 * a 1 - b 0 * b 1)
  have n5 := abs_nonneg (a 0 * a 1 * a 2 - b 0 * b 1 * b 2)
  have t1 : |a 0 * a 1 * a 2 - b 0 * b 1 * b 2| * a 3 ≤ |a 0 * a 1 * a 2 - b 0 * b 1 * b 2| :=
    mul_le_of_le_one_right n5 d1
  have t2 : |b 0 * b 1 * b 2| * |a 3 - b 3| ≤ |a 3 - b 3| := mul_le_of_le_one_left n3 p1
  have t3 : |a 0 * a 1 - b 0 * b 1| * a 2 ≤ |a 0 * a 1 - b 0 * b 1| := mul_le_of_le_one_right n4 c1
  have t4 : |b 0 * b 1| * |a 2 - b 2| ≤ |a 2 - b 2| := mul_le_of_le_one_left n2 p2
  have t5 : |a 0 - b 0| * a 1 ≤ |a 0 - b 0| := mul_le_of_le_one_right n0 b1
  have t6 : |b 0| * |a 1 - b 1| ≤ |a 1 - b 1| := mul_le_of_le_one_left n1 p3
  linarith
theorem cutoffProfile_mem_unitInterval (t : ℝ) : 0 ≤ cutoffProfile t ∧ cutoffProfile t ≤ 1 :=
  ⟨cutoffProfile_nonneg t, cutoffProfile_le_one t⟩
theorem localCutoff_mem_unitInterval (v x : Lattice4) : 0 ≤ localCutoff F v x ∧ localCutoff F v x ≤ 1 :=
  ⟨Finset.prod_nonneg fun _ _ => cutoffProfile_nonneg _, Finset.prod_le_one (fun _ _ => cutoffProfile_nonneg _)
    fun _ _ => cutoffProfile_le_one _⟩
theorem localCutoff_abs_sub_le (hL : 0 < F.blockSide) (v x x' : Lattice4) (hx : ∀ i, |x i - x' i| ≤ 1) :
    |localCutoff F v x - localCutoff F v x'| ≤ 4 * cutoffBound / (F.blockSide : ℝ) ^ F.top := by
  have hN : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by
    have : (0 : ℝ) < F.blockSide := by exact_mod_cast hL
    positivity
  refine (abs_prod_four_sub_le_sum _ _ (fun _ => cutoffProfile_mem_unitInterval _)
    (fun _ => cutoffProfile_mem_unitInterval _)).trans ?_
  have hone : ∀ i : Fin 4,
      |cutoffProfile (((x i - (cellSideLength F - 1) / 2 - cellSideLength F * v i : ℤ) : ℝ) /
          (F.blockSide : ℝ) ^ F.top) -
        cutoffProfile (((x' i - (cellSideLength F - 1) / 2 - cellSideLength F * v i : ℤ) : ℝ) /
          (F.blockSide : ℝ) ^ F.top)| ≤
      cutoffBound / (F.blockSide : ℝ) ^ F.top := by
    intro i
    refine (cutoffProfile_abs_sub_le _ _).trans ?_
    rw [← sub_div, abs_div, abs_of_pos hN, mul_div_assoc']
    refine div_le_div_of_nonneg_right ?_ hN.le
    have h1 : |(((x i - (cellSideLength F - 1) / 2 - cellSideLength F * v i : ℤ) : ℝ) -
        ((x' i - (cellSideLength F - 1) / 2 - cellSideLength F * v i : ℤ) : ℝ))| ≤ 1 := by
      have h2 : (((x i - (cellSideLength F - 1) / 2 - cellSideLength F * v i : ℤ) : ℝ) -
          ((x' i - (cellSideLength F - 1) / 2 - cellSideLength F * v i : ℤ) : ℝ)) = ((x i - x' i : ℤ) : ℝ) := by
        push_cast
        ring
      rw [h2]
      exact_mod_cast hx i
    have hb := one_le_cutoffBound
    nlinarith
  calc _ ≤ ∑ _i : Fin 4, cutoffBound / (F.blockSide : ℝ) ^ F.top := Finset.sum_le_sum fun i _ => hone i
    _ = _ := by simp; ring
def weightConstant : ℝ := 8 * cutoffBound * (1 + 33 ^ 4)
theorem weight_abs_sub_le (hL : 0 < F.blockSide) {x x' : Lattice4}
    (hq : 1 ≤ LocalPartition.sumSqCutoff S z x) (hq' : 1 ≤ LocalPartition.sumSqCutoff S z x')
    (hx : ∀ i, |x i - x' i| ≤ 1) (v : Lattice4) :
    |LocalPartition.weight S z v x - LocalPartition.weight S z v x'| ≤
      weightConstant / (F.blockSide : ℝ) ^ F.top := by
  have hb := one_le_cutoffBound
  set e : ℝ := 4 * cutoffBound / (F.blockSide : ℝ) ^ F.top with he
  have he0 : 0 ≤ e := by positivity
  have hsq : ∀ v : Lattice4, |localCutoff F v x ^ 2 - localCutoff F v x' ^ 2| ≤ 2 * e := by
    intro v
    obtain ⟨a0, a1⟩ := localCutoff_mem_unitInterval (F := F) v x
    obtain ⟨b0, b1⟩ := localCutoff_mem_unitInterval (F := F) v x'
    have h1 := localCutoff_abs_sub_le hL v x x' hx
    have e1 : localCutoff F v x ^ 2 - localCutoff F v x' ^ 2 =
        (localCutoff F v x - localCutoff F v x') * (localCutoff F v x + localCutoff F v x') := by ring
    rw [e1, abs_mul, abs_of_nonneg (by linarith : 0 ≤ localCutoff F v x + localCutoff F v x')]
    calc _ ≤ e * 2 := mul_le_mul h1 (by linarith) (by linarith) he0
      _ = _ := by ring
  have hQ : |LocalPartition.sumSqCutoff S z x - LocalPartition.sumSqCutoff S z x'| ≤ 33 ^ 4 * (2 * e) := by
    unfold LocalPartition.sumSqCutoff
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ _v ∈ localCellIndex S z, 2 * e := Finset.sum_le_sum fun v _ => hsq v
      _ = ((localCellIndex S z).card : ℝ) * (2 * e) := by simp
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact_mod_cast card_localCellIndex_le
  obtain ⟨Q, hQd⟩ : ∃ Q, Q = LocalPartition.sumSqCutoff S z x := ⟨_, rfl⟩
  obtain ⟨Q', hQd'⟩ : ∃ Q', Q' = LocalPartition.sumSqCutoff S z x' := ⟨_, rfl⟩
  simp only [LocalPartition.weight]
  rw [← hQd, ← hQd'] at hQ ⊢
  rw [← hQd] at hq
  rw [← hQd'] at hq'
  have hQ0 : 0 < Q := by linarith
  have hQ0' : 0 < Q' := by linarith
  obtain ⟨b0, b1⟩ := localCutoff_mem_unitInterval (F := F) v x'
  have hb2 : localCutoff F v x' ^ 2 ≤ 1 := by nlinarith
  have hb0 : 0 ≤ localCutoff F v x' ^ 2 := sq_nonneg _
  have e2 : localCutoff F v x ^ 2 / Q - localCutoff F v x' ^ 2 / Q' =
      (localCutoff F v x ^ 2 - localCutoff F v x' ^ 2) / Q + (localCutoff F v x' ^ 2 / Q') * ((Q' - Q) / Q) := by
    field_simp
    ring
  rw [e2]
  refine (abs_add_le _ _).trans ?_
  rw [abs_div, abs_mul, abs_div, abs_div, abs_of_pos hQ0, abs_of_pos hQ0', abs_of_nonneg hb0]
  have t1 : |localCutoff F v x ^ 2 - localCutoff F v x' ^ 2| / Q ≤ 2 * e :=
    (div_le_self (abs_nonneg _) hq).trans (hsq v)
  have t2 : localCutoff F v x' ^ 2 / Q' ≤ 1 := (div_le_self hb0 hq').trans hb2
  have t3 : |Q' - Q| / Q ≤ 33 ^ 4 * (2 * e) := by
    rw [abs_sub_comm]
    exact (div_le_self (abs_nonneg _) hq).trans hQ
  have t4 : localCutoff F v x' ^ 2 / Q' * (|Q' - Q| / Q) ≤ 33 ^ 4 * (2 * e) :=
    (mul_le_of_le_one_left (by positivity) t2).trans t3
  have e3 : weightConstant / (F.blockSide : ℝ) ^ F.top = 2 * e + 33 ^ 4 * (2 * e) := by
    rw [he, weightConstant]
    field_simp
    ring
  rw [e3]
  linarith
theorem cellPartition_abs_sub_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    {x x' : Lattice4} (hx : ∀ i, -(10 * cellSideLength F) ≤ x i ∧ x i < 21 * cellSideLength F)
    (hx' : ∀ i, -(10 * cellSideLength F) ≤ x' i ∧ x' i < 21 * cellSideLength F)
    (hs : patchSite S z x ∈ sitesOfCells S 0) (hs' : patchSite S z x' ∈ sitesOfCells S 0)
    (hd : ∀ i, |x i - x' i| ≤ 1) {y : F.Cell} (hy : y ∈ S) :
    |cellPartition S (patchSite S z x) y - cellPartition S (patchSite S z x') y| ≤
      weightConstant / (F.blockSide : ℝ) ^ F.top := by
  have hL := hodd.pos
  have hc : 0 ≤ weightConstant / (F.blockSide : ℝ) ^ F.top := by
    have hb := one_le_cutoffBound
    have : (0 : ℝ) < F.blockSide := by exact_mod_cast hL
    unfold weightConstant
    positivity
  have hq := LocalPartition.one_le_sumSqCutoff hamb hodd he hx hs
  have hq' := LocalPartition.one_le_sumSqCutoff hamb hodd he hx' hs'
  by_cases h1 : cellCutoff (patchSite S z x) y = 0
  · by_cases h2 : cellCutoff (patchSite S z x') y = 0
    · rw [LocalPartition.cellPartition_eq_zero_of_cellCutoff_eq_zero h1,
        LocalPartition.cellPartition_eq_zero_of_cellCutoff_eq_zero h2]
      simpa using hc
    · obtain ⟨v, hv, rfl⟩ := exists_localCell_of_cellCutoff_ne_zero hamb hodd he hx' h2
      have hm : v ∈ localCellIndex S z := mem_localCellIndex.2 ⟨hv, hy⟩
      rw [LocalPartition.cellPartition_patchSite_eq hamb hodd he hx hm,
        LocalPartition.cellPartition_patchSite_eq hamb hodd he hx' hm]
      exact weight_abs_sub_le hL hq hq' hd v
  · obtain ⟨v, hv, rfl⟩ := exists_localCell_of_cellCutoff_ne_zero hamb hodd he hx h1
    have hm : v ∈ localCellIndex S z := mem_localCellIndex.2 ⟨hv, hy⟩
    rw [LocalPartition.cellPartition_patchSite_eq hamb hodd he hx hm,
      LocalPartition.cellPartition_patchSite_eq hamb hodd he hx' hm]
    exact weight_abs_sub_le hL hq hq' hd v
def stepOffset (st : PathStep) : Lattice4 := if st.2 then basisVector st.1 else - basisVector st.1
theorem stepDisplacement_eq (st : PathStep) :
    (stepDisplacement (F := F) 0 st) = siteOfCoords 0 (stepOffset st) := by
  simp only [stepDisplacement, stepOffset]
  split_ifs
  · rfl
  · rw [siteOfCoords_neg]
    rfl
theorem abs_stepOffset_le (st : PathStep) (k : Fin 4) : |stepOffset st k| ≤ 1 := by
  simp only [stepOffset, basisVector]
  by_cases hk : k = st.1
  · subst hk
    split_ifs <;> simp
  · split_ifs <;> simp [hk]
theorem patchChart_add_stepDisplacement (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    {s : F.Site 0} (st : PathStep) (hr : ∀ i, -(10 * cellSideLength F) ≤ patchChart S z s i ∧
      patchChart S z s i < 21 * cellSideLength F) :
    patchChart S z (s + stepDisplacement 0 st) =
      fun k => patchChart S z s k + closedOrthant S z k * stepOffset st k := by
  have hL := hodd.pos
  obtain ⟨h0, h1⟩ := cellSideLength_half (F := F) hodd
  have hstep : (stepDisplacement (F := F) 0 st) = siteOfCoords 0 (stepOffset st) := stepDisplacement_eq st
  funext k
  set A : ℤ := ((s - cellCentre 0 z) k).valMinAbs with hA
  have hAr : patchChart S z s k = closedOrthant S z k * A + (cellSideLength F - 1) / 2 := rfl
  have hAb : |A| ≤ 22 * cellSideLength F := by
    have h2 := hr k
    rw [hAr] at h2
    rcases he k with hs | hs <;> rw [hs] at h2 <;> rw [abs_le] <;> constructor <;> omega
  have hst : |stepOffset st k| ≤ 1 := abs_stepOffset_le st k
  have e : (s + stepDisplacement 0 st - cellCentre 0 z : F.Site 0) k =
      ((A + stepOffset st k : ℤ) : ZMod (F.period 0 k)) := by
    rw [hstep]
    simp only [Pi.sub_apply, Pi.add_apply, siteOfCoords, hA]
    push_cast
    ring
  have hb : |A + stepOffset st k| < 32 * cellSideLength F := by
    have := abs_add_le A (stepOffset st k)
    omega
  simp only [patchChart]
  rw [e, valMinAbs_of_abs_lt hamb hL k hb, hA]
  ring
theorem interiorBump_patchSite (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    {a : Lattice4} (ha : ∀ i, -(10 * cellSideLength F) ≤ a i ∧ a i < 21 * cellSideLength F) :
    interiorBump (patchSite S z a) z =
      ∏ i, cutoffProfile (5 / 2 * ((a i - (cellSideLength F - 1) / 2 : ℤ) : ℝ) / (cellSideLength F : ℝ)) := by
  have hL := hodd.pos
  obtain ⟨h0, h1⟩ := cellSideLength_half (F := F) hodd
  refine Finset.prod_congr rfl fun i _ => ?_
  have e : (patchSite S z a - cellCentre 0 z) i =
      ((closedOrthant S z i * (a i - (cellSideLength F - 1) / 2) : ℤ) : ZMod (F.period 0 i)) := by
    simp [patchSite, siteOfCoords]
  have hb : |closedOrthant S z i * (a i - (cellSideLength F - 1) / 2)| < 32 * cellSideLength F := by
    rw [abs_mul, abs_closedOrthant he, one_mul, abs_lt]
    have := ha i
    constructor <;> omega
  rw [e, valMinAbs_of_abs_lt hamb hL i hb]
  rcases he i with h | h
  · rw [h]
    simp
  · rw [h, ← cutoffProfile_neg]
    congr 1
    push_cast
    ring
theorem interiorBump_nonneg_at (s : F.Site 0) (y : F.Cell) : 0 ≤ interiorBump s y :=
  Finset.prod_nonneg fun _ _ => cutoffProfile_nonneg _
theorem interiorBump_le_one_at (s : F.Site 0) (y : F.Cell) : interiorBump s y ≤ 1 :=
  Finset.prod_le_one (fun _ _ => cutoffProfile_nonneg _) fun _ _ => cutoffProfile_le_one _
theorem interiorBump_abs_sub_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    {a a' : Lattice4} (ha : ∀ i, -(10 * cellSideLength F) ≤ a i ∧ a i < 21 * cellSideLength F)
    (ha' : ∀ i, -(10 * cellSideLength F) ≤ a' i ∧ a' i < 21 * cellSideLength F) (hd : ∀ i, |a i - a' i| ≤ 1) :
    |interiorBump (patchSite S z a) z - interiorBump (patchSite S z a') z| ≤
      10 * cutoffBound / (cellSideLength F : ℝ) := by
  have hN : (0 : ℝ) < cellSideLength F := by exact_mod_cast cellSideLength_pos (F := F) hodd.pos
  rw [interiorBump_patchSite hamb hodd he ha, interiorBump_patchSite hamb hodd he ha']
  refine (abs_prod_four_sub_le_sum _ _ (fun _ => cutoffProfile_mem_unitInterval _)
    (fun _ => cutoffProfile_mem_unitInterval _)).trans ?_
  have hone : ∀ i : Fin 4,
      |cutoffProfile (5 / 2 * ((a i - (cellSideLength F - 1) / 2 : ℤ) : ℝ) / (cellSideLength F : ℝ)) -
        cutoffProfile (5 / 2 * ((a' i - (cellSideLength F - 1) / 2 : ℤ) : ℝ) / (cellSideLength F : ℝ))| ≤
      (5 / 2 * cutoffBound) / (cellSideLength F : ℝ) := by
    intro i
    refine (cutoffProfile_abs_sub_le _ _).trans ?_
    have e : 5 / 2 * ((a i - (cellSideLength F - 1) / 2 : ℤ) : ℝ) / (cellSideLength F : ℝ) -
        5 / 2 * ((a' i - (cellSideLength F - 1) / 2 : ℤ) : ℝ) / (cellSideLength F : ℝ) =
        (5 / 2 * ((a i - a' i : ℤ) : ℝ)) / (cellSideLength F : ℝ) := by
      push_cast
      ring
    rw [e, abs_div, abs_of_pos hN, mul_div_assoc']
    refine div_le_div_of_nonneg_right ?_ hN.le
    have h1 : |((a i - a' i : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast hd i
    have hb := one_le_cutoffBound
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 5 / 2)]
    nlinarith
  calc _ ≤ ∑ _i : Fin 4, (5 / 2 * cutoffBound) / (cellSideLength F : ℝ) := Finset.sum_le_sum fun i _ => hone i
    _ = _ := by simp; ring
def interiorBumpMean (S : Finset F.Cell) (y : F.Cell) : ℝ :=
  (1 / (cellSideLength F : ℝ) ^ 4) * ∑ x ∈ cellOffsets F, interiorBump (patchSite S y x) y
theorem inv_81_le_interiorBumpMean (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) :
    1 / 81 ≤ interiorBumpMean S z := by
  classical
  have hL := hodd.pos
  have hN := cellSideLength_pos (F := F) hL
  have hNr : (0 : ℝ) < cellSideLength F := by exact_mod_cast hN
  obtain ⟨h0, h1⟩ := cellSideLength_half (F := F) hodd
  set k : ℤ := cellSideLength F / 5 with hk
  set h : ℤ := (cellSideLength F - 1) / 2 with hh
  set T : Finset Lattice4 := Fintype.piFinset fun _ => Finset.Icc (h - k) (h + k) with hT
  have hsub : T ⊆ cellOffsets F := by
    intro x hx
    refine Fintype.mem_piFinset.2 fun i => ?_
    have := Finset.mem_Icc.1 (Fintype.mem_piFinset.1 hx i)
    rw [Finset.mem_Ico]
    omega
  have hone : ∀ x ∈ T, interiorBump (patchSite S z x) z = 1 := by
    intro x hx
    have hr : ∀ i, -(10 * cellSideLength F) ≤ x i ∧ x i < 21 * cellSideLength F := by
      intro i
      have := Finset.mem_Icc.1 (Fintype.mem_piFinset.1 hx i)
      constructor <;> omega
    rw [interiorBump_patchSite hamb hodd he hr]
    refine Finset.prod_eq_one fun i _ => cutoffProfile_eq_one ?_
    have h2 := Finset.mem_Icc.1 (Fintype.mem_piFinset.1 hx i)
    have h3 : |x i - h| ≤ k := by
      rw [abs_le]
      constructor <;> omega
    have h4 : 5 * |x i - h| ≤ cellSideLength F := by omega
    have h5 : 5 * |((x i - h : ℤ) : ℝ)| ≤ (cellSideLength F : ℝ) := by exact_mod_cast h4
    rw [abs_div, abs_mul, abs_of_pos hNr, abs_of_pos (by norm_num : (0 : ℝ) < 5 / 2), div_le_iff₀ hNr]
    nlinarith
  have hcard : (T.card : ℝ) = (2 * (k : ℝ) + 1) ^ 4 := by
    have hk0 : 0 ≤ k := by omega
    have : T.card = (2 * k.toNat + 1) ^ 4 := by
      simp only [hT, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Int.card_Icc]
      congr 1
      omega
    rw [this]
    push_cast
    rw [show ((k.toNat : ℝ)) = (k : ℝ) by exact_mod_cast Int.toNat_of_nonneg hk0]
  have h3k : (cellSideLength F : ℝ) ≤ 3 * (2 * (k : ℝ) + 1) := by
    have : cellSideLength F ≤ 3 * (2 * k + 1) := by omega
    exact_mod_cast this
  have hs : (T.card : ℝ) ≤ ∑ x ∈ cellOffsets F, interiorBump (patchSite S z x) z := by
    calc (T.card : ℝ) = ∑ x ∈ T, interiorBump (patchSite S z x) z := by
          rw [Finset.sum_congr rfl hone]
          simp
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => interiorBump_nonneg_at _ _
  unfold interiorBumpMean
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
  refine le_trans ?_ hs
  rw [hcard]
  have h4 : (cellSideLength F : ℝ) ^ 4 ≤ (3 * (2 * (k : ℝ) + 1)) ^ 4 := pow_le_pow_left₀ hNr.le h3k 4
  have e : (3 * (2 * (k : ℝ) + 1)) ^ 4 = 81 * (2 * (k : ℝ) + 1) ^ 4 := by ring
  rw [e] at h4
  linarith
theorem normalizedBump_eq (S : Finset F.Cell) (s : F.Site 0) (y : F.Cell) :
    normalizedBump S s y = interiorBump s y / interiorBumpMean S y := rfl
theorem normalizedBump_nonneg (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (s : F.Site 0) : 0 ≤ normalizedBump S s z := by
  rw [normalizedBump_eq]
  have := inv_81_le_interiorBumpMean hamb hodd he
  exact div_nonneg (interiorBump_nonneg_at _ _) (by linarith)
theorem normalizedBump_abs_sub_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    {a a' : Lattice4} (ha : ∀ i, -(10 * cellSideLength F) ≤ a i ∧ a i < 21 * cellSideLength F)
    (ha' : ∀ i, -(10 * cellSideLength F) ≤ a' i ∧ a' i < 21 * cellSideLength F) (hd : ∀ i, |a i - a' i| ≤ 1) :
    |normalizedBump S (patchSite S z a) z - normalizedBump S (patchSite S z a') z| ≤
      810 * cutoffBound / (cellSideLength F : ℝ) := by
  have hm := inv_81_le_interiorBumpMean (S := S) hamb hodd he
  have hm0 : 0 < interiorBumpMean S z := by linarith
  rw [normalizedBump_eq, normalizedBump_eq, ← sub_div, abs_div, abs_of_pos hm0, div_le_iff₀ hm0]
  have h1 := interiorBump_abs_sub_le hamb hodd he ha ha' hd
  have hN : (0 : ℝ) < cellSideLength F := by exact_mod_cast cellSideLength_pos (F := F) hodd.pos
  have hb := one_le_cutoffBound
  have h2 : 10 * cutoffBound / (cellSideLength F : ℝ) ≤ 810 * cutoffBound / (cellSideLength F : ℝ) * (1 / 81) := by
    apply le_of_eq
    field_simp
    ring
  have h3 : 810 * cutoffBound / (cellSideLength F : ℝ) * (1 / 81) ≤
      810 * cutoffBound / (cellSideLength F : ℝ) * interiorBumpMean S z :=
    mul_le_mul_of_nonneg_left hm (by positivity)
  linarith
theorem exists_centredCube_of_interiorBump_ne_zero (hodd : Odd F.blockSide) {s : F.Site 0} {y : F.Cell}
    (h : interiorBump s y ≠ 0) :
    ∃ t : Lattice4, t ∈ centredCube (F.blockSide ^ F.top) ∧ s = cellCentre 0 y + siteOfCoords 0 t := by
  have hL := hodd.pos
  have hN := cellSideLength_pos (F := F) hL
  have hNr : (0 : ℝ) < cellSideLength F := by exact_mod_cast hN
  obtain ⟨h0, h1⟩ := cellSideLength_half (F := F) hodd
  refine ⟨fun i => ((s - cellCentre 0 y) i).valMinAbs, ?_, ?_⟩
  · rw [mem_centredCube_iff]
    intro i
    have f1 : cutoffProfile (5 / 2 * (((s - cellCentre 0 y) i).valMinAbs : ℝ) / (cellSideLength F : ℝ)) ≠ 0 :=
      fun h0' => h (Finset.prod_eq_zero (Finset.mem_univ i) h0')
    have g1 := abs_lt_of_cutoffProfile_ne_zero f1
    rw [abs_div, abs_mul, abs_of_pos hNr, abs_of_pos (by norm_num : (0 : ℝ) < 5 / 2), div_lt_iff₀ hNr] at g1
    have g2 : 25 * |((s - cellCentre 0 y) i).valMinAbs| < 9 * cellSideLength F := by
      have : (25 : ℝ) * |(((s - cellCentre 0 y) i).valMinAbs : ℝ)| < 9 * (cellSideLength F : ℝ) := by nlinarith
      exact_mod_cast this
    have g4 : |((s - cellCentre 0 y) i).valMinAbs| ≤ (cellSideLength F - 1) / 2 := by omega
    exact ⟨by linarith [(abs_le.1 g4).1], (abs_le.1 g4).2⟩
  · funext i
    simp only [siteOfCoords, Pi.add_apply, ZMod.coe_valMinAbs, Pi.sub_apply]
    ring
theorem sum_patchSiteSet_eq (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (g : F.Site 0 → ℝ) : ∑ t ∈ patchSiteSet S z, g t = ∑ a ∈ patchDomain S z, g (patchSite S z a) := by
  classical
  exact Finset.sum_image (patchSite_injOn hamb hodd he)
theorem patchCubicKernel_patchSite_eq (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (f : F.Site 0 → ℝ) {a : Lattice4} (ha : a ∈ patchDomain S z) :
    patchCubicKernel S z f (patchSite S z a) =
      ∑ b ∈ patchDomain S z, cubicKernel (a - b) * f (patchSite S z b) := by
  classical
  have hs : patchSite S z a ∈ patchSiteSet S z := Finset.mem_image_of_mem _ ha
  simp only [patchCubicKernel, if_pos hs]
  rw [sum_patchSiteSet_eq hamb hodd he]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [patchChart_patchSite hamb hodd he (patchDomain_coord_bounds ha),
    patchChart_patchSite hamb hodd he (patchDomain_coord_bounds hb)]
end BondShares
end YangMills.Construction
end
