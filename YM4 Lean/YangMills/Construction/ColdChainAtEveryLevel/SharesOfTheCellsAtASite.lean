import YangMills.Construction.ColdChainAtEveryLevel.LinesOfTheBlocksOfABond
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
open YangMills.Construction.LatticeFractionalIntegration
namespace LocalPartition
variable {F : BlockFrame} {S : Finset F.Cell} {z : F.Cell}
def sumSqCutoff (S : Finset F.Cell) (z : F.Cell) (x : Lattice4) : ℝ :=
  ∑ v ∈ localCellIndex S z, localCutoff F v x ^ 2
def weight (S : Finset F.Cell) (z : F.Cell) (v x : Lattice4) : ℝ := localCutoff F v x ^ 2 / sumSqCutoff S z x
theorem weight_nonneg (v x : Lattice4) (hx : 0 ≤ sumSqCutoff S z x) : 0 ≤ weight S z v x :=
  div_nonneg (sq_nonneg _) hx
theorem sum_weight_eq_one {x : Lattice4} (hx : 1 ≤ sumSqCutoff S z x) :
    ∑ v ∈ localCellIndex S z, weight S z v x = 1 := by
  simp only [weight]
  rw [← Finset.sum_div]
  have h0 : sumSqCutoff S z x ≠ 0 := by linarith
  exact div_self h0
theorem localCutoff_ne_zero_of_weight_ne_zero {v x : Lattice4} (h : weight S z v x ≠ 0) : localCutoff F v x ≠ 0 := by
  intro h0
  apply h
  simp [weight, h0]
theorem cellPartition_eq_zero_of_cellCutoff_eq_zero {s : F.Site 0} {y : F.Cell} (h : cellCutoff s y = 0) :
    cellPartition S s y = 0 := by
  simp [cellPartition, h]
theorem abs_sub_lt_two_of_localCutoff_ne_zero (hL : 0 < F.blockSide) {x v v' : Lattice4}
    (h1 : localCutoff F v x ≠ 0) (h2 : localCutoff F v' x ≠ 0) :
    ∀ i, |v' i - v i| < 2 := by
  have hN := cellSideLength_pos (F := F) hL
  have hN' : (0 : ℝ) < GaugeMap.cellSideLength F := by exact_mod_cast hN
  have hcs : (F.blockSide : ℝ) ^ F.top = (GaugeMap.cellSideLength F : ℝ) := by simp [GaugeMap.cellSideLength]
  intro i
  have f1 : cutoffProfile (((x i - (GaugeMap.cellSideLength F - 1) / 2 - GaugeMap.cellSideLength F * v i : ℤ) : ℝ) /
      (F.blockSide : ℝ) ^ F.top) ≠ 0 :=
    fun h0 => h1 (Finset.prod_eq_zero (Finset.mem_univ i) h0)
  have f2 : cutoffProfile (((x i - (GaugeMap.cellSideLength F - 1) / 2 - GaugeMap.cellSideLength F * v' i : ℤ) : ℝ) /
      (F.blockSide : ℝ) ^ F.top) ≠ 0 :=
    fun h0 => h2 (Finset.prod_eq_zero (Finset.mem_univ i) h0)
  have g1 := abs_lt_of_cutoffProfile_ne_zero f1
  have g2 := abs_lt_of_cutoffProfile_ne_zero f2
  rw [hcs, abs_div, abs_of_pos hN', div_lt_iff₀ hN'] at g1 g2
  set A : ℤ := x i - (GaugeMap.cellSideLength F - 1) / 2 - GaugeMap.cellSideLength F * v i with hA
  set A' : ℤ := x i - (GaugeMap.cellSideLength F - 1) / 2 - GaugeMap.cellSideLength F * v' i with hA'
  have e : (GaugeMap.cellSideLength F : ℝ) * ((v' i - v i : ℤ) : ℝ) = (A : ℝ) - A' := by
    have : GaugeMap.cellSideLength F * (v' i - v i) = A - A' := by rw [hA, hA']; ring
    exact_mod_cast this
  have h3 : |(GaugeMap.cellSideLength F : ℝ) * ((v' i - v i : ℤ) : ℝ)| < 2 * GaugeMap.cellSideLength F := by
    rw [e]
    have := abs_sub (A : ℝ) (A' : ℝ)
    nlinarith
  rw [abs_mul, abs_of_pos hN'] at h3
  have h4 : |((v' i - v i : ℤ) : ℝ)| < 2 := by nlinarith
  exact_mod_cast h4
variable (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
  (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
include hamb hodd he in
theorem cellCutoff_patchSite_eq {x v : Lattice4}
    (hx : ∀ i, -(10 * GaugeMap.cellSideLength F) ≤ x i ∧ x i < 21 * GaugeMap.cellSideLength F)
    (hv : v ∈ localCellIndex S z) :
    cellCutoff (GaugeMap.patchSite S z x) (localCell S z v) = localCutoff F v x := by
  have hc := cellSideLength_half (F := F) hodd
  have hN := cellSideLength_pos (F := F) hodd.pos
  exact cellCutoff_eq_localCutoff hamb hodd.pos he hx (mem_localCellIndex.1 hv).1 ⟨hc.1, by omega⟩
include hamb hodd he in
theorem sum_sq_cellCutoff_eq {x : Lattice4}
    (hx : ∀ i, -(10 * GaugeMap.cellSideLength F) ≤ x i ∧ x i < 21 * GaugeMap.cellSideLength F) :
    ∑ y ∈ S, cellCutoff (GaugeMap.patchSite S z x) y ^ 2 = sumSqCutoff S z x := by
  rw [sum_eq_sum_localCellIndex hamb hodd he hx _ (fun y _ h0 => by simp [h0])]
  exact Finset.sum_congr rfl fun v hv => by rw [cellCutoff_patchSite_eq hamb hodd he hx hv]
include hamb hodd he in
theorem cellPartition_patchSite_eq {x v : Lattice4}
    (hx : ∀ i, -(10 * GaugeMap.cellSideLength F) ≤ x i ∧ x i < 21 * GaugeMap.cellSideLength F)
    (hv : v ∈ localCellIndex S z) :
    cellPartition S (GaugeMap.patchSite S z x) (localCell S z v) = weight S z v x := by
  unfold cellPartition weight
  rw [sum_sq_cellCutoff_eq hamb hodd he hx, cellCutoff_patchSite_eq hamb hodd he hx hv]
include hamb hodd he in
theorem one_le_sumSqCutoff {x : Lattice4}
    (hr : ∀ i, -(10 * GaugeMap.cellSideLength F) ≤ x i ∧ x i < 21 * GaugeMap.cellSideLength F)
    (hs : GaugeMap.patchSite S z x ∈ sitesOfCells S 0) : 1 ≤ sumSqCutoff S z x := by
  obtain ⟨y, hy, h, hh, e⟩ := mem_sitesOfCells.1 hs
  have hb : cellCutoff (GaugeMap.patchSite S z x) y = 1 := by
    rw [e]
    have : F.top - 0 = F.top := by omega
    rw [this] at hh
    exact cellCutoff_self hamb hodd y hh
  have hne : cellCutoff (GaugeMap.patchSite S z x) y ≠ 0 := by rw [hb]; norm_num
  obtain ⟨v, hv, rfl⟩ := exists_localCell_of_cellCutoff_ne_zero hamb hodd he hr hne
  have hmem : v ∈ localCellIndex S z := mem_localCellIndex.2 ⟨hv, hy⟩
  have h1 := cellCutoff_patchSite_eq hamb hodd he hr hmem
  rw [hb] at h1
  have h2 : localCutoff F v x ^ 2 ≤ sumSqCutoff S z x :=
    Finset.single_le_sum (f := fun v => localCutoff F v x ^ 2) (fun _ _ => sq_nonneg _) hmem
  rw [← h1] at h2
  simpa using h2
theorem localizationOperator_eq_zero_of_cellCutoff_eq_zero {V : F.GaugeField F.top} {s : F.Site 0} {y : F.Cell}
    (hb : cellCutoff s y = 0) (f : F.Cell → ℍ[ℝ]) : localizationOperator S V s f y = 0 := by
  unfold localizationOperator
  refine Finset.sum_eq_zero fun y' _ => Finset.sum_eq_zero fun y'' _ => ?_
  simp [cellPartition_eq_zero_of_cellCutoff_eq_zero (S := S) hb]
include hamb hodd he in
theorem localizationOperator_patchSite_eq {V : F.GaugeField F.top} {x v : Lattice4}
    (hx : ∀ i, -(10 * GaugeMap.cellSideLength F) ≤ x i ∧ x i < 21 * GaugeMap.cellSideLength F)
    (hv : v ∈ localCellIndex S z) (f : F.Cell → ℍ[ℝ]) :
    localizationOperator S V (GaugeMap.patchSite S z x) f (localCell S z v) =
      ∑ v' ∈ localCellIndex S z, ∑ v'' ∈ localCellIndex S z,
        (weight S z v' x * Real.sqrt (weight S z v x) * Real.sqrt (weight S z v'' x)) •
          (((cellParallelTransport S V (localCell S z v) (localCell S z v') : UnitQuaternion) : ℍ[ℝ]) *
            (((cellParallelTransport S V (localCell S z v'') (localCell S z v'))⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
              f (localCell S z v'')) := by
  classical
  unfold localizationOperator
  rw [sum_eq_sum_localCellIndex hamb hodd he hx _ (fun y' _ h0 => by
    refine Finset.sum_eq_zero fun y'' _ => ?_
    simp [cellPartition_eq_zero_of_cellCutoff_eq_zero (S := S) h0])]
  refine Finset.sum_congr rfl fun v' hv' => ?_
  rw [sum_eq_sum_localCellIndex hamb hodd he hx _ (fun y'' _ h0 => by
    simp [cellPartition_eq_zero_of_cellCutoff_eq_zero (S := S) h0])]
  refine Finset.sum_congr rfl fun v'' hv'' => ?_
  rw [cellPartition_patchSite_eq hamb hodd he hx hv', cellPartition_patchSite_eq hamb hodd he hx hv,
    cellPartition_patchSite_eq hamb hodd he hx hv'']
theorem enclosingCell_cellCentre_add (hL : Odd F.blockSide) {j : ℕ} (z : F.Cell) (h : Fin 4 → ℤ)
    (hh : h ∈ centredCube (F.blockSide ^ (F.top - j))) :
    enclosingCell (cellCentre j z + siteOfCoords j h : F.Site j) = z := by apply _root_.YangMills.Construction.BlockLines.enclosingCell_cellCentre_add <;> assumption
theorem enclosingCell_mem (hL : Odd F.blockSide) {j : ℕ} {x : F.Site j} (hx : x ∈ sitesOfCells S j) :
    enclosingCell x ∈ S := by apply _root_.YangMills.Construction.BlockLines.enclosingCell_mem <;> assumption
end LocalPartition
end YangMills.Construction.BlockAverages
end
