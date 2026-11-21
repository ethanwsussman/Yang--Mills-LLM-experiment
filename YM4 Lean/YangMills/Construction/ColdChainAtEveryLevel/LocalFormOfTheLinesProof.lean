import YangMills.Construction.ColdChainAtEveryLevel.EigenvectorsOfANearlyConstantKernelProofForm
import YangMills.Construction.ColdChainAtEveryLevel.LineOfANearlyConstantKernelProof
import YangMills.Construction.ColdChainAtEveryLevel.LocalFormOfTheLines
import YangMills.Construction.ColdChainAtEveryLevel.SharesOfTheCellsAtASite
import YangMills.Construction.ColdChainAtEveryLevel.TransportsInTheUnitsOfAPatch
import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockAverages
open FiniteDifferences LatticeFractionalIntegration NearlyConstantKernel GaugeMap FlatPairing LatticePaths
section Partition
variable {F : BlockFrame} {S : Finset F.Cell} {z : F.Cell}
def cellScaleNorm (F : BlockFrame) (a : Lattice4) : ℝ := 1 / (cellSideLength F : ℝ) * supNorm a
theorem cellScaleNorm_nonneg (hL : 0 < F.blockSide) (a : Lattice4) : 0 ≤ cellScaleNorm F a := by
  have h := cellSideLength_pos (F := F) hL
  unfold cellScaleNorm
  positivity
theorem abs_coord_le_supNorm (u : Lattice4) (μ : Fin 4) : |(u μ : ℝ)| ≤ supNorm u := by
  have h1 := natAbs_le_supNorm u μ
  have h2 : ((u μ).natAbs : ℝ) = |(u μ : ℝ)| := by simp [Nat.cast_natAbs]
  rw [← h2]
  exact_mod_cast h1
theorem localCutoff_factor_diffBound (hL : 0 < F.blockSide) (D : Set Lattice4) (v : Lattice4) (i : Fin 4) :
    FiniteDiffBound (cellScaleNorm F) 3 D cutoffBound
      (fun x : Lattice4 => cutoffProfile (((x i - (cellSideLength F - 1) / 2 - cellSideLength F * v i : ℤ) : ℝ) /
        (F.blockSide : ℝ) ^ F.top)) := by
  have hN := cellSideLength_pos (F := F) hL
  have hN' : (0 : ℝ) < cellSideLength F := by exact_mod_cast hN
  have hcs : (cellSideLength F : ℝ) = (F.blockSide : ℝ) ^ F.top := by simp [cellSideLength]
  set l : Lattice4 →+ ℝ := AddMonoidHom.mk' (fun x => (x i : ℝ) / (F.blockSide : ℝ) ^ F.top) (fun a b => by
    simp only [Pi.add_apply, Int.cast_add, add_div]) with hl
  have hlen : ∀ a, |l a| ≤ cellScaleNorm F a := by
    intro a
    show |(a i : ℝ) / (F.blockSide : ℝ) ^ F.top| ≤ 1 / (cellSideLength F : ℝ) * supNorm a
    rw [← hcs, abs_div, abs_of_pos hN', div_eq_inv_mul, one_div]
    exact mul_le_mul_of_nonneg_left (abs_coord_le_supNorm a i) (by positivity)
  have := DerivBound.finiteDiffBound (S := D) (cellScaleNorm_nonneg hL) l hlen
    ((-((cellSideLength F - 1) / 2) - cellSideLength F * v i : ℤ) / (F.blockSide : ℝ) ^ F.top)
    cutoffProfile_derivBound
  refine this.congr fun x => ?_
  congr 1
  show (x i : ℝ) / (F.blockSide : ℝ) ^ F.top + _ = _
  rw [← add_div]
  congr 1
  push_cast
  ring
theorem localCutoff_diffBound (hL : 0 < F.blockSide) (D : Set Lattice4) (v : Lattice4) :
    FiniteDiffBound (cellScaleNorm F) 3 D (512 * cutoffBound ^ 4) (localCutoff F v) := by
  have hl := cellScaleNorm_nonneg (F := F) hL
  have hM : 0 ≤ cutoffBound := by linarith [one_le_cutoffBound]
  have f0 := localCutoff_factor_diffBound hL D v 0
  have f1 := localCutoff_factor_diffBound hL D v 1
  have f2 := localCutoff_factor_diffBound hL D v 2
  have f3 := localCutoff_factor_diffBound hL D v 3
  have m1 := FiniteDiffBound.mul hl hM hM f0 f1
  have m2 := FiniteDiffBound.mul hl (by positivity) hM m1 f2
  have m3 := FiniteDiffBound.mul hl (by positivity) hM m2 f3
  have e : (2 : ℝ) ^ 3 * (2 ^ 3 * (2 ^ 3 * cutoffBound * cutoffBound) * cutoffBound) * cutoffBound =
      512 * cutoffBound ^ 4 := by
    ring
  rw [e] at m3
  refine m3.congr fun x => ?_
  simp only [localCutoff, Fin.prod_univ_four]
def cutoffSqBound : ℝ := 8 * (512 * cutoffBound ^ 4) * (512 * cutoffBound ^ 4)
def cutoffSqSumBound : ℝ := 33 ^ 4 * cutoffSqBound
def partitionBound : ℝ := 8 * cutoffSqBound * invDiffBound cutoffSqSumBound 1 3
theorem cutoffSqBound_nonneg : 0 ≤ cutoffSqBound := by
  have : 0 ≤ cutoffBound := by linarith [one_le_cutoffBound]
  unfold cutoffSqBound
  positivity
theorem cutoffSqSumBound_nonneg : 0 ≤ cutoffSqSumBound := by
  have := cutoffSqBound_nonneg
  unfold cutoffSqSumBound
  positivity
theorem partitionBound_nonneg : 0 ≤ partitionBound := by
  have := cutoffSqBound_nonneg
  have h2 := invDiffBound_nonneg cutoffSqSumBound 1 (by norm_num) 3
  unfold partitionBound
  positivity
def localCutoffSqSum (S : Finset F.Cell) (z : F.Cell) (x : Lattice4) : ℝ :=
  ∑ v ∈ localCellIndex S z, localCutoff F v x ^ 2
def localPartition (S : Finset F.Cell) (z : F.Cell) (v x : Lattice4) : ℝ :=
  localCutoff F v x ^ 2 / localCutoffSqSum S z x
theorem localCutoff_nonneg (v x : Lattice4) : 0 ≤ localCutoff F v x :=
  Finset.prod_nonneg fun _ _ => cutoffProfile_nonneg _
theorem localCutoff_sq_diffBound (hL : 0 < F.blockSide) (D : Set Lattice4) (v : Lattice4) :
    FiniteDiffBound (cellScaleNorm F) 3 D cutoffSqBound (fun x => localCutoff F v x ^ 2) := by
  have b := localCutoff_diffBound (F := F) hL D v
  have m := FiniteDiffBound.mul (cellScaleNorm_nonneg hL) (by positivity) (by positivity) b b
  have e : (2 : ℝ) ^ 3 * (512 * cutoffBound ^ 4) * (512 * cutoffBound ^ 4) = cutoffSqBound := by
    unfold cutoffSqBound
    ring
  rw [e] at m
  exact m.congr fun x => by rw [sq]
theorem localCutoffSqSum_diffBound (hL : 0 < F.blockSide) (D : Set Lattice4) :
    FiniteDiffBound (cellScaleNorm F) 3 D cutoffSqSumBound (localCutoffSqSum S z) := by
  have hl := cellScaleNorm_nonneg (F := F) hL
  have h := FiniteDiffBound.sum hl (localCellIndex S z) (fun _ _ => cutoffSqBound_nonneg)
    (fun v _ => localCutoff_sq_diffBound (F := F) hL D v)
  refine (h.bound_mono hl ?_).congr fun x => rfl
  rw [Finset.sum_const, nsmul_eq_mul]
  unfold cutoffSqSumBound
  refine mul_le_mul_of_nonneg_right ?_ cutoffSqBound_nonneg
  exact_mod_cast card_localCellIndex_le
theorem localPartition_diffBound (hL : 0 < F.blockSide) {D : Set Lattice4}
    (hD : ∀ x ∈ D, 1 ≤ localCutoffSqSum S z x) (v : Lattice4) :
    FiniteDiffBound (cellScaleNorm F) 3 D partitionBound (localPartition S z v) := by
  have hl := cellScaleNorm_nonneg (F := F) hL
  have i1 := FiniteDiffBound.inv (r := 1) hl cutoffSqSumBound_nonneg (by norm_num)
    (localCutoffSqSum_diffBound (S := S) (z := z) hL D) (fun x hx => by
      have := hD x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      simpa using this)
  have m := FiniteDiffBound.mul hl cutoffSqBound_nonneg (invDiffBound_nonneg _ _ (by norm_num) _)
    (localCutoff_sq_diffBound (F := F) hL D v) i1
  have e : (2 : ℝ) ^ 3 * cutoffSqBound * invDiffBound cutoffSqSumBound 1 3 = partitionBound := by
    unfold partitionBound
    ring
  rw [e] at m
  exact m.congr fun x => by rw [localPartition, div_eq_mul_inv]
theorem localPartition_nonneg (v x : Lattice4) (hx : 0 ≤ localCutoffSqSum S z x) :
    0 ≤ localPartition S z v x := by apply _root_.YangMills.Construction.BlockAverages.LocalPartition.weight_nonneg <;> assumption
theorem sum_localPartition {x : Lattice4} (hx : 1 ≤ localCutoffSqSum S z x) :
    ∑ v ∈ localCellIndex S z, localPartition S z v x = 1 := by apply _root_.YangMills.Construction.BlockAverages.LocalPartition.sum_weight_eq_one <;> assumption
variable (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
  (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
include hamb hodd he in
theorem cellCutoff_patchSite_eq {x v : Lattice4}
    (hx : ∀ i, -(10 * cellSideLength F) ≤ x i ∧ x i < 21 * cellSideLength F)
    (hv : v ∈ localCellIndex S z) : cellCutoff (patchSite S z x) (localCell S z v) = localCutoff F v x := by apply _root_.YangMills.Construction.BlockAverages.LocalPartition.cellCutoff_patchSite_eq <;> assumption
include hamb hodd he in
theorem sum_cellCutoff_sq_patchSite_eq {x : Lattice4}
    (hx : ∀ i, -(10 * cellSideLength F) ≤ x i ∧ x i < 21 * cellSideLength F) :
    ∑ y ∈ S, cellCutoff (patchSite S z x) y ^ 2 = localCutoffSqSum S z x := by apply _root_.YangMills.Construction.BlockAverages.LocalPartition.sum_sq_cellCutoff_eq <;> assumption
include hamb hodd he in
theorem cellPartition_patchSite_eq {x v : Lattice4}
    (hx : ∀ i, -(10 * cellSideLength F) ≤ x i ∧ x i < 21 * cellSideLength F)
    (hv : v ∈ localCellIndex S z) :
    cellPartition S (patchSite S z x) (localCell S z v) = localPartition S z v x := by apply _root_.YangMills.Construction.BlockAverages.LocalPartition.cellPartition_patchSite_eq <;> assumption
include hamb hodd he in
theorem one_le_localCutoffSqSum {x : Lattice4} (hx : x ∈ patchLocalSites S z) : 1 ≤ localCutoffSqSum S z x := by
  obtain ⟨hr, hs⟩ := hx
  obtain ⟨y, hy, h, hh, e⟩ := mem_sitesOfCells.1 hs
  have hb : cellCutoff (patchSite S z x) y = 1 := by
    rw [e]
    have : F.top - 0 = F.top := by omega
    rw [this] at hh
    exact cellCutoff_self hamb hodd y hh
  have hne : cellCutoff (patchSite S z x) y ≠ 0 := by rw [hb]; norm_num
  obtain ⟨v, hv, rfl⟩ := exists_localCell_of_cellCutoff_ne_zero hamb hodd he hr hne
  have hmem : v ∈ localCellIndex S z := mem_localCellIndex.2 ⟨hv, hy⟩
  have h1 := cellCutoff_patchSite_eq hamb hodd he hr hmem
  rw [hb] at h1
  have h2 : localCutoff F v x ^ 2 ≤ localCutoffSqSum S z x :=
    Finset.single_le_sum (f := fun v => localCutoff F v x ^ 2) (fun _ _ => sq_nonneg _) hmem
  rw [← h1] at h2
  simpa using h2
end Partition
section Kernel
variable {F : BlockFrame} {S : Finset F.Cell} {V : F.GaugeField F.top} {z : F.Cell}
def localHolonomy (S : Finset F.Cell) (V : F.GaugeField F.top) (z : F.Cell) (v v' v'' : Lattice4) : UnitQuaternion :=
  (cellTransport S V z (localCell S z v))⁻¹ * cellParallelTransport S V (localCell S z v) (localCell S z v') *
    (cellParallelTransport S V (localCell S z v'') (localCell S z v'))⁻¹ * cellTransport S V z (localCell S z v'')
open Classical in
def localKernel (S : Finset F.Cell) (V : F.GaugeField F.top) (z : F.Cell) (v v' v'' : Lattice4) : ℍ[ℝ] :=
  if supNorm (v' - v) ≤ 3 ∧ supNorm (v' - v'') ≤ 3 then
    ((localHolonomy S V z v v' v'' : UnitQuaternion) : ℍ[ℝ]) - 1 else 0
theorem localKernel_star (v v' v'' : Lattice4) :
    star (localKernel S V z v v' v'') = localKernel S V z v'' v' v := by
  classical
  unfold localKernel
  by_cases h : supNorm (v' - v) ≤ 3 ∧ supNorm (v' - v'') ≤ 3
  · rw [if_pos h, if_pos h.symm, star_sub, star_one]
    congr 1
    rw [← coe_unitQuaternion_inv]
    congr 1
    simp only [localHolonomy]
    group
  · have h' : ¬ (supNorm (v' - v'') ≤ 3 ∧ supNorm (v' - v) ≤ 3) := fun a => h a.symm
    rw [if_neg h, if_neg h', star_zero]
theorem localKernel_norm_le {C s : ℝ} (hs : 0 ≤ C * s)
    (hT : ∀ v ∈ localCellIndex S z, ∀ v' ∈ localCellIndex S z, supNorm (v' - v) ≤ 3 →
      ‖(((cellTransport S V z (localCell S z v))⁻¹ * cellParallelTransport S V (localCell S z v) (localCell S z v') *
          cellTransport S V z (localCell S z v') : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ C * s)
    {v v' v'' : Lattice4} (hv : v ∈ localCellIndex S z) (hv' : v' ∈ localCellIndex S z)
    (hv'' : v'' ∈ localCellIndex S z) :
    ‖localKernel S V z v v' v''‖ ≤ 2 * (C * s) := by
  classical
  unfold localKernel
  by_cases h : supNorm (v' - v) ≤ 3 ∧ supNorm (v' - v'') ≤ 3
  · rw [if_pos h]
    have h1 := hT v hv v' hv' h.1
    have h2 := hT v'' hv'' v' hv' h.2
    set A := (cellTransport S V z (localCell S z v))⁻¹ *
      cellParallelTransport S V (localCell S z v) (localCell S z v') *
      cellTransport S V z (localCell S z v') with hA
    set B := (cellTransport S V z (localCell S z v''))⁻¹ *
      cellParallelTransport S V (localCell S z v'') (localCell S z v') *
      cellTransport S V z (localCell S z v') with hB
    have e : localHolonomy S V z v v' v'' = A * B⁻¹ := by
      simp only [localHolonomy, hA, hB]
      group
    rw [e]
    refine (norm_coe_mul_sub_one_le _ _).trans ?_
    rw [norm_coe_inv_sub_one]
    linarith
  · rw [if_neg h, norm_zero]
    linarith
theorem supNorm_sub_le_of_localCutoff_ne_zero (hL : 0 < F.blockSide) {x v v' : Lattice4}
    (h1 : localCutoff F v x ≠ 0) (h2 : localCutoff F v' x ≠ 0) :
    supNorm (v' - v) ≤ 3 := by
  have hN := cellSideLength_pos (F := F) hL
  have hN' : (0 : ℝ) < cellSideLength F := by exact_mod_cast hN
  have hcs : (F.blockSide : ℝ) ^ F.top = (cellSideLength F : ℝ) := by simp [cellSideLength]
  rw [supNorm_le_iff]
  intro i
  have f1 : cutoffProfile (((x i - (cellSideLength F - 1) / 2 - cellSideLength F * v i : ℤ) : ℝ) /
      (F.blockSide : ℝ) ^ F.top) ≠ 0 :=
    fun h0 => h1 (Finset.prod_eq_zero (Finset.mem_univ i) h0)
  have f2 : cutoffProfile (((x i - (cellSideLength F - 1) / 2 - cellSideLength F * v' i : ℤ) : ℝ) /
      (F.blockSide : ℝ) ^ F.top) ≠ 0 :=
    fun h0 => h2 (Finset.prod_eq_zero (Finset.mem_univ i) h0)
  have g1 := abs_lt_of_cutoffProfile_ne_zero f1
  have g2 := abs_lt_of_cutoffProfile_ne_zero f2
  rw [hcs, abs_div, abs_of_pos hN', div_lt_iff₀ hN'] at g1 g2
  set A : ℤ := x i - (cellSideLength F - 1) / 2 - cellSideLength F * v i with hA
  set A' : ℤ := x i - (cellSideLength F - 1) / 2 - cellSideLength F * v' i with hA'
  have e : (cellSideLength F : ℝ) * ((v' i - v i : ℤ) : ℝ) = (A : ℝ) - A' := by
    have : cellSideLength F * (v' i - v i) = A - A' := by rw [hA, hA']; ring
    exact_mod_cast this
  have h3 : |(cellSideLength F : ℝ) * ((v' i - v i : ℤ) : ℝ)| < 2 * cellSideLength F := by
    rw [e]
    have := abs_sub (A : ℝ) (A' : ℝ)
    nlinarith
  rw [abs_mul, abs_of_pos hN'] at h3
  have h4 : |((v' i - v i : ℤ) : ℝ)| < 2 := by nlinarith
  have h5 : |v' i - v i| < 2 := by exact_mod_cast h4
  have h6 := abs_lt.1 h5
  simp only [Pi.sub_apply]
  omega
variable (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
  (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
theorem cellPartition_eq_zero_of_cellCutoff {s : F.Site 0} {y : F.Cell} (h : cellCutoff s y = 0) :
    cellPartition S s y = 0 := by
  simp [cellPartition, h]
theorem localCutoff_ne_zero_of_localPartition {v x : Lattice4} (h : localPartition S z v x ≠ 0) :
    localCutoff F v x ≠ 0 := by apply _root_.YangMills.Construction.BlockAverages.LocalPartition.localCutoff_ne_zero_of_weight_ne_zero <;> assumption
include hamb hodd he in
theorem localizationOperator_patchSite {x v : Lattice4}
    (hx : ∀ i, -(10 * cellSideLength F) ≤ x i ∧ x i < 21 * cellSideLength F)
    (hv : v ∈ localCellIndex S z) (f : F.Cell → ℍ[ℝ]) :
    (((cellTransport S V z (localCell S z v))⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
        localizationOperator S V (patchSite S z x) f (localCell S z v) =
      (Real.sqrt (localPartition S z v x) : ℍ[ℝ]) *
        symmetrizedApplyCore (localCellIndex S z) (fun w => localPartition S z w x) (localKernel S V z)
          (fun w => (((cellTransport S V z (localCell S z w))⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
            f (localCell S z w)) v := by
  classical
  unfold localizationOperator
  rw [sum_eq_sum_localCellIndex hamb hodd he hx _ (fun y' _ h0 => by
    refine Finset.sum_eq_zero fun y'' _ => ?_
    simp [cellPartition_eq_zero_of_cellCutoff (S := S) h0])]
  have inner : ∀ v' ∈ localCellIndex S z, ∑ y'' ∈ S,
      (cellPartition S (patchSite S z x) (localCell S z v') *
        Real.sqrt (cellPartition S (patchSite S z x) (localCell S z v)) *
        Real.sqrt (cellPartition S (patchSite S z x) y'')) •
      (((cellParallelTransport S V (localCell S z v) (localCell S z v') : UnitQuaternion) : ℍ[ℝ]) *
        (((cellParallelTransport S V y'' (localCell S z v'))⁻¹ : UnitQuaternion) : ℍ[ℝ]) * f y'') =
      ∑ v'' ∈ localCellIndex S z,
      (localPartition S z v' x * Real.sqrt (localPartition S z v x) * Real.sqrt (localPartition S z v'' x)) •
      (((cellParallelTransport S V (localCell S z v) (localCell S z v') : UnitQuaternion) : ℍ[ℝ]) *
        (((cellParallelTransport S V (localCell S z v'') (localCell S z v'))⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
          f (localCell S z v'')) := by
    intro v' hv'
    rw [sum_eq_sum_localCellIndex hamb hodd he hx _ (fun y'' _ h0 => by
      simp [cellPartition_eq_zero_of_cellCutoff (S := S) h0])]
    refine Finset.sum_congr rfl fun v'' hv'' => ?_
    rw [cellPartition_patchSite_eq hamb hodd he hx hv', cellPartition_patchSite_eq hamb hodd he hx hv,
      cellPartition_patchSite_eq hamb hodd he hx hv'']
  rw [Finset.sum_congr rfl inner]
  unfold symmetrizedApplyCore
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun v' hv' => Finset.sum_congr rfl fun v'' hv'' => ?_
  set u := localPartition S z v x with hu
  set u' := localPartition S z v' x with hu'
  set u'' := localPartition S z v'' x with hu''
  by_cases hz : u = 0 ∨ u' = 0 ∨ u'' = 0
  · rcases hz with h | h | h <;> simp [h]
  · push_neg at hz
    have b1 := localCutoff_ne_zero_of_localPartition hz.1
    have b2 := localCutoff_ne_zero_of_localPartition hz.2.1
    have b3 := localCutoff_ne_zero_of_localPartition hz.2.2
    have n1 := supNorm_sub_le_of_localCutoff_ne_zero hodd.pos b1 b2
    have n2 := supNorm_sub_le_of_localCutoff_ne_zero hodd.pos b3 b2
    have hk : 1 + localKernel S V z v v' v'' = ((localHolonomy S V z v v' v'' : UnitQuaternion) : ℍ[ℝ]) := by
      simp only [localKernel, if_pos (And.intro n1 n2)]
      abel
    rw [hk]
    set Ui := (((cellTransport S V z (localCell S z v))⁻¹ : UnitQuaternion) : ℍ[ℝ]) with hUi
    set X := ((cellParallelTransport S V (localCell S z v) (localCell S z v') : UnitQuaternion) : ℍ[ℝ]) with hX
    set Y := (((cellParallelTransport S V (localCell S z v'') (localCell S z v'))⁻¹ : UnitQuaternion) : ℍ[ℝ])
      with hY
    set fv := f (localCell S z v'') with hfv
    have e1 : ((localHolonomy S V z v v' v'' : UnitQuaternion) : ℍ[ℝ]) *
        ((((cellTransport S V z (localCell S z v''))⁻¹ : UnitQuaternion) : ℍ[ℝ]) * fv) = Ui * X * Y * fv := by
      have h1 : ((cellTransport S V z (localCell S z v'') : UnitQuaternion) : ℍ[ℝ]) *
          (((cellTransport S V z (localCell S z v''))⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := by
        rw [← Submonoid.coe_mul, mul_inv_cancel]
        rfl
      simp only [localHolonomy, Submonoid.coe_mul]
      rw [← mul_assoc, mul_assoc _ ((cellTransport S V z (localCell S z v'') : UnitQuaternion) : ℍ[ℝ]), h1,
        mul_one]
    rw [e1]
    have e3 : Ui * (X * Y * fv) = Ui * X * Y * fv := by simp only [mul_assoc]
    rw [mul_smul_comm, e3]
    simp only [Quaternion.coe_mul_eq_smul, smul_smul]
    congr 1
    ring
end Kernel
section Eigenvectors
variable {F : BlockFrame} {S : Finset F.Cell} {V : F.GaugeField F.top} {z : F.Cell}
theorem coe_unitQuaternion_mul_inv (g : UnitQuaternion) : (g : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := by apply _root_.YangMills.Construction.GaugeFixing.coe_mul_coe_inv <;> assumption
theorem coe_unitQuaternion_inv_mul (g : UnitQuaternion) : ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (g : ℍ[ℝ]) = 1 := by apply _root_.YangMills.Construction.GaugeFixing.coe_inv_mul_coe <;> assumption
theorem localizationOperator_eq_zero {s : F.Site 0} {y : F.Cell} (hb : cellCutoff s y = 0) (f : F.Cell → ℍ[ℝ]) :
    localizationOperator S V s f y = 0 := by apply _root_.YangMills.Construction.BlockAverages.LocalPartition.localizationOperator_eq_zero_of_cellCutoff_eq_zero <;> assumption
variable (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
  (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
  {x : Lattice4} (hx : x ∈ patchLocalSites S z)
  (hEig : UnitEigenvectorsNearOne) {η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 64)
  (hk : ∀ v ∈ localCellIndex S z, ∀ v' ∈ localCellIndex S z, ∀ v'' ∈ localCellIndex S z,
    ‖localKernel S V z v v' v''‖ ≤ η)
  (hh : Lattice4 → ℍ[ℝ])
include hamb hodd he hx hEig hη0 hη hk in
theorem isLeadingEigenvector_form
    (huniq : ∀ h' : Lattice4 → ℍ[ℝ], (∀ i ∈ localCellIndex S z, ‖h' i - 1‖ ≤ 1) →
      ∑ i ∈ localCellIndex S z, (localPartition S z i x : ℍ[ℝ]) * h' i = 1 →
      ∀ l : ℍ[ℝ], (∀ i ∈ localCellIndex S z,
        1 + perturbationApply (localCellIndex S z) (fun i => localPartition S z i x) (localKernel S V z) h' i =
          h' i * l) →
      ∀ i ∈ localCellIndex S z, h' i = hh i)
    {f : F.Cell → ℍ[ℝ]} (hf : IsLeadingEigenvector S V (patchSite S z x) f) :
    (∃ c : ℍ[ℝ], c ≠ 0 ∧ ∀ v ∈ localCellIndex S z, f (localCell S z v) =
      ((cellTransport S V z (localCell S z v) : UnitQuaternion) : ℍ[ℝ]) *
        ((Real.sqrt (localPartition S z v x) : ℍ[ℝ]) * (hh v * c))) ∧
      ∀ y ∈ S, cellCutoff (patchSite S z x) y = 0 → f y = 0 := by
  obtain ⟨hn, l, hl, hop⟩ := hf
  have hr := hx.1
  have hsq := one_le_localCutoffSqSum hamb hodd he hx
  have hu : ∀ v ∈ localCellIndex S z, 0 ≤ localPartition S z v x :=
    fun v _ => localPartition_nonneg v x (by linarith)
  have hs := sum_localPartition hsq
  have l0 : l ≠ 0 := by
    intro h0
    rw [h0] at hl
    norm_num at hl
  have hzero : ∀ y ∈ S, cellCutoff (patchSite S z x) y = 0 → f y = 0 := by
    intro y hy hb
    have h1 := hop y hy
    rw [localizationOperator_eq_zero hb] at h1
    exact (smul_eq_zero.1 h1.symm).resolve_left l0
  set ν : Lattice4 → ℍ[ℝ] := fun w =>
    (((cellTransport S V z (localCell S z w))⁻¹ : UnitQuaternion) : ℍ[ℝ]) * f (localCell S z w) with hν
  have hnorm : ∀ w, ‖ν w‖ = ‖f (localCell S z w)‖ := by
    intro w
    simp only [hν]
    rw [norm_mul, norm_coe_unitQuaternion, one_mul]
  have hsum : ∑ w ∈ localCellIndex S z, ‖ν w‖ ^ 2 = 1 := by
    rw [← hn, sum_eq_sum_localCellIndex hamb hodd he hr (fun y => ‖f y‖ ^ 2)
      (fun y hy h0 => by simp [hzero y hy h0])]
    exact Finset.sum_congr rfl fun w _ => by rw [hnorm]
  have heq : ∀ v ∈ localCellIndex S z, (Real.sqrt (localPartition S z v x) : ℍ[ℝ]) *
      symmetrizedApplyCore (localCellIndex S z) (fun w => localPartition S z w x) (localKernel S V z) ν v =
        (l : ℍ[ℝ]) * ν v := by
    intro v hv
    rw [← localizationOperator_patchSite hamb hodd he hr hv f, hop _ (mem_localCellIndex.1 hv).2, mul_smul_comm,
      Quaternion.coe_mul_eq_smul]
  obtain ⟨h', c, hc, hb, hm, hA, hform⟩ :=
    (hEig Lattice4 (localCellIndex S z) (fun w => localPartition S z w x) (localKernel S V z) η hu hs hη0 hη
      hk).1 ν l hl hsum heq
  have hsame := huniq h' hb hm (l : ℍ[ℝ]) hA
  refine ⟨⟨c, hc, fun v hv => ?_⟩, hzero⟩
  have h1 := hform v hv
  rw [hsame v hv] at h1
  rw [← h1]
  simp only [hν]
  rw [← mul_assoc, coe_unitQuaternion_mul_inv, one_mul]
include hamb hodd he hx hEig hη0 hη hk in
theorem exists_isLeadingEigenvector (hb2 : ∀ v ∈ localCellIndex S z, ‖hh v - 1‖ ≤ 1 / 2)
    (hmean : ∑ i ∈ localCellIndex S z, (localPartition S z i x : ℍ[ℝ]) * hh i = 1)
    (heig : ∀ i ∈ localCellIndex S z,
      1 + perturbationApply (localCellIndex S z) (fun i => localPartition S z i x) (localKernel S V z) hh i =
        hh i * (1 + perturbationMean (localCellIndex S z) (fun i => localPartition S z i x)
          (localKernel S V z) hh)) :
    ∃ f, IsLeadingEigenvector S V (patchSite S z x) f := by
  classical
  have hr := hx.1
  have hsq := one_le_localCutoffSqSum hamb hodd he hx
  have hu : ∀ v ∈ localCellIndex S z, 0 ≤ localPartition S z v x :=
    fun v _ => localPartition_nonneg v x (by linarith)
  have hs := sum_localPartition hsq
  obtain ⟨l, w, hl, hw, hsum, heq⟩ :=
    (hEig Lattice4 (localCellIndex S z) (fun w => localPartition S z w x) (localKernel S V z) η hu hs hη0 hη
      hk).2 hh hb2 hmean heig (fun i _ i' _ i'' _ => localKernel_star i i' i'')
  set ν : Lattice4 → ℍ[ℝ] := fun v => (Real.sqrt (localPartition S z v x) : ℍ[ℝ]) * ((w : ℍ[ℝ]) * hh v) with hν
  set f : F.Cell → ℍ[ℝ] := fun y => ∑ v ∈ localCellIndex S z,
    if localCell S z v = y then ((cellTransport S V z (localCell S z v) : UnitQuaternion) : ℍ[ℝ]) * ν v else 0
    with hf
  have hfv : ∀ v ∈ localCellIndex S z, f (localCell S z v) =
      ((cellTransport S V z (localCell S z v) : UnitQuaternion) : ℍ[ℝ]) * ν v := by
    intro v hv
    simp only [hf]
    rw [Finset.sum_eq_single v]
    · simp
    · intro b hb hbv
      have : localCell S z b ≠ localCell S z v := fun h =>
        hbv (localCell_injective hamb he (mem_localCellIndex.1 hb).1 (mem_localCellIndex.1 hv).1 h)
      simp [this]
    · intro h
      exact absurd hv h
  have hfz : ∀ y, cellCutoff (patchSite S z x) y = 0 → f y = 0 := by
    intro y hb
    simp only [hf]
    refine Finset.sum_eq_zero fun v hv => ?_
    by_cases h : localCell S z v = y
    · rw [if_pos h]
      have h1 : localPartition S z v x = 0 := by
        rw [← cellPartition_patchSite_eq hamb hodd he hr hv, h]
        exact cellPartition_eq_zero_of_cellCutoff hb
      simp [hν, h1]
    · rw [if_neg h]
  refine ⟨f, ?_, l, hl, fun y hy => ?_⟩
  · rw [sum_eq_sum_localCellIndex hamb hodd he hr (fun y => ‖f y‖ ^ 2) (fun y _ h0 => by simp [hfz y h0])]
    rw [← hsum]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [hfv v hv, norm_mul, norm_coe_unitQuaternion, one_mul]
  · by_cases hb : cellCutoff (patchSite S z x) y = 0
    · rw [localizationOperator_eq_zero hb, hfz y hb, smul_zero]
    · obtain ⟨v, hvb, rfl⟩ := exists_localCell_of_cellCutoff_ne_zero hamb hodd he hr hb
      have hv : v ∈ localCellIndex S z := mem_localCellIndex.2 ⟨hvb, hy⟩
      have t := localizationOperator_patchSite (V := V) hamb hodd he hr hv f
      have c1 : symmetrizedApplyCore (localCellIndex S z) (fun w => localPartition S z w x) (localKernel S V z)
          (fun w => (((cellTransport S V z (localCell S z w))⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
            f (localCell S z w)) v =
          symmetrizedApplyCore (localCellIndex S z) (fun w => localPartition S z w x) (localKernel S V z) ν v := by
        unfold symmetrizedApplyCore
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb' => ?_
        have hq : (((cellTransport S V z (localCell S z b))⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
            f (localCell S z b) = ν b := by
          rw [hfv b hb', ← mul_assoc, coe_unitQuaternion_inv_mul, one_mul]
        simp only [hq]
      rw [c1, heq v hv] at t
      have e1 : localizationOperator S V (patchSite S z x) f (localCell S z v) =
          ((cellTransport S V z (localCell S z v) : UnitQuaternion) : ℍ[ℝ]) *
            ((((cellTransport S V z (localCell S z v))⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
              localizationOperator S V (patchSite S z x) f (localCell S z v)) := by
        rw [← mul_assoc, coe_unitQuaternion_mul_inv, one_mul]
      rw [e1, t, hfv v hv]
      set U := ((cellTransport S V z (localCell S z v) : UnitQuaternion) : ℍ[ℝ])
      calc U * ((l : ℍ[ℝ]) * ν v) = (U * (l : ℍ[ℝ])) * ν v := (mul_assoc _ _ _).symm
        _ = ((l : ℍ[ℝ]) * U) * ν v := by rw [Quaternion.coe_commutes]
        _ = (l : ℍ[ℝ]) * (U * ν v) := mul_assoc _ _ _
        _ = l • (U * ν v) := Quaternion.coe_mul_eq_smul _ _
end Eigenvectors
section Centres
theorem isLeadingEigenvector_mul_unit {F : BlockFrame} {S : Finset F.Cell} {V : F.GaugeField F.top}
    {x : F.Site 0} {f : F.Cell → ℍ[ℝ]}
    (hf : IsLeadingEigenvector S V x f) (c : UnitQuaternion) :
    IsLeadingEigenvector S V x (fun y => f y * (c : ℍ[ℝ])) := by
  obtain ⟨hn, l, hl, hop⟩ := hf
  refine ⟨?_, l, hl, fun y hy => ?_⟩
  · simpa [norm_mul, norm_coe_unitQuaternion] using hn
  · have h1 := hop y hy
    have e : localizationOperator S V x (fun y => f y * (c : ℍ[ℝ])) y =
        localizationOperator S V x f y * (c : ℍ[ℝ]) := by
      simp only [localizationOperator, Finset.sum_mul, smul_mul_assoc, mul_assoc]
    rw [e, h1, smul_mul_assoc]
variable {F : BlockFrame} {S : Finset F.Cell} {V : F.GaugeField F.top} {z : F.Cell}
theorem cellParallelTransport_self (y : F.Cell) : cellParallelTransport S V y y = 1 := by
  have h0 : cellDisplacement y y = 0 := by
    funext i
    simp [cellDisplacement]
  unfold cellParallelTransport
  rw [h0]
  have h1 : orthantPart (closedOrthant S y) (0 : Lattice4) = 0 := by
    funext i
    simp [orthantPart]
  have e3 : List.finRange 4 = [0, 1, 2, 3] := by decide
  have e : axisPath (0 : Lattice4) 1 = [] := by
    unfold axisPath
    rw [e3]
    simp
  rw [h1, sub_self, e]
  rfl
variable (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
  (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
include hamb hodd he in
theorem cellCutoff_eq_zero_at_cellCentre {x : Lattice4}
    (hx : ∀ i, -(10 * cellSideLength F) ≤ x i ∧ x i < 21 * cellSideLength F) {y y' : F.Cell}
    (hs : patchSite S z x = cellCentre 0 y) (hy' : y' ≠ y) : cellCutoff (patchSite S z x) y' = 0 := by
  have hL := hodd.pos
  have hN := cellSideLength_pos (F := F) hL
  have hN' : (0 : ℝ) < cellSideLength F := by exact_mod_cast hN
  have hcs : (F.blockSide : ℝ) ^ F.top = (cellSideLength F : ℝ) := by simp [cellSideLength]
  obtain ⟨hc0, hc1⟩ := cellSideLength_half (F := F) hodd
  have hown : cellCutoff (patchSite S z x) y = 1 := by
    have h0 : (0 : Lattice4) ∈ centredCube (F.blockSide ^ F.top) := by
      simp only [centredCube, Fintype.mem_piFinset, Finset.mem_Icc]
      intro i
      have : (1 : ℤ) ≤ ((F.blockSide ^ F.top : ℕ) : ℤ) := by
        have : 1 ≤ F.blockSide ^ F.top := Nat.one_le_pow _ _ hL
        exact_mod_cast this
      simp only [Pi.zero_apply]
      constructor <;> omega
    have := cellCutoff_self hamb hodd y h0
    rw [siteOfCoords_zero, add_zero] at this
    rw [hs]
    exact this
  by_contra hb
  obtain ⟨v', hv', rfl⟩ := exists_localCell_of_cellCutoff_ne_zero hamb hodd he hx hb
  obtain ⟨v, hv, rfl⟩ := exists_localCell_of_cellCutoff_ne_zero hamb hodd he hx
    (by rw [hown]; norm_num : cellCutoff (patchSite S z x) y ≠ 0)
  apply hy'
  have hvv : v' = v := by
    funext i
    have h1 := patchSite_sub_cellCentre S z x v i
    rw [hs, sub_self] at h1
    have h2 := hx i
    have h3 := hv i
    have hA : |closedOrthant S z i * (x i - (cellSideLength F - 1) / 2 - cellSideLength F * v i)| <
        32 * cellSideLength F := by
      rw [abs_mul, abs_closedOrthant he, one_mul, abs_lt]
      have a1 : cellSideLength F * v i ≤ cellSideLength F * 21 := mul_le_mul_of_nonneg_left h3.2 hN.le
      have a2 : cellSideLength F * (-11) ≤ cellSideLength F * v i := mul_le_mul_of_nonneg_left h3.1 hN.le
      constructor <;> omega
    have h4 := valMinAbs_of_abs_lt hamb hL i hA
    rw [← h1] at h4
    have h5 : ((0 : F.Site 0) i).valMinAbs = 0 := by simp
    rw [h5] at h4
    have h6 : x i - (cellSideLength F - 1) / 2 - cellSideLength F * v i = 0 := by
      rcases he i with h | h <;> rw [h] at h4 <;> omega
    have f2 : cutoffProfile ((((patchSite S z x - cellCentre 0 (localCell S z v')) i).valMinAbs : ℝ) /
        (F.blockSide : ℝ) ^ F.top) ≠ 0 :=
      fun h0 => hb (Finset.prod_eq_zero (Finset.mem_univ i) h0)
    have g2 := abs_lt_of_cutoffProfile_ne_zero f2
    have h7 := patchSite_sub_cellCentre S z x v' i
    have h8 := hv' i
    have hA' : |closedOrthant S z i * (x i - (cellSideLength F - 1) / 2 - cellSideLength F * v' i)| <
        32 * cellSideLength F := by
      rw [abs_mul, abs_closedOrthant he, one_mul, abs_lt]
      have a1 : cellSideLength F * v' i ≤ cellSideLength F * 21 := mul_le_mul_of_nonneg_left h8.2 hN.le
      have a2 : cellSideLength F * (-11) ≤ cellSideLength F * v' i := mul_le_mul_of_nonneg_left h8.1 hN.le
      constructor <;> omega
    rw [h7, valMinAbs_of_abs_lt hamb hL i hA', hcs, abs_div, abs_of_pos hN', div_lt_iff₀ hN'] at g2
    have e1 : closedOrthant S z i * (x i - (cellSideLength F - 1) / 2 - cellSideLength F * v' i) =
        closedOrthant S z i * (cellSideLength F * (v i - v' i)) := by
      have : x i - (cellSideLength F - 1) / 2 - cellSideLength F * v' i = cellSideLength F * (v i - v' i) := by
        linear_combination h6
      rw [this]
    rw [e1] at g2
    have g3 : |(closedOrthant S z i : ℝ)| = 1 := by
      rcases he i with h | h <;> rw [h] <;> norm_num
    push_cast at g2
    rw [abs_mul, abs_mul, g3, one_mul, abs_of_pos hN'] at g2
    have g4 : |(v i : ℝ) - v' i| < 1 := by nlinarith
    have g5 : |v i - v' i| < 1 := by exact_mod_cast g4
    have := abs_lt.1 g5
    omega
  rw [hvv]
include hamb hodd he in
theorem cellPartition_eq_one_at_cellCentre {x : Lattice4}
    (hx : ∀ i, -(10 * cellSideLength F) ≤ x i ∧ x i < 21 * cellSideLength F) {y : F.Cell} (hy : y ∈ S)
    (hs : patchSite S z x = cellCentre 0 y) : cellPartition S (patchSite S z x) y = 1 := by
  classical
  have hL := hodd.pos
  have hown : cellCutoff (patchSite S z x) y = 1 := by
    have h0 : (0 : Lattice4) ∈ centredCube (F.blockSide ^ F.top) := by
      simp only [centredCube, Fintype.mem_piFinset, Finset.mem_Icc]
      intro i
      have : (1 : ℤ) ≤ ((F.blockSide ^ F.top : ℕ) : ℤ) := by
        have : 1 ≤ F.blockSide ^ F.top := Nat.one_le_pow _ _ hL
        exact_mod_cast this
      simp only [Pi.zero_apply]
      constructor <;> omega
    have := cellCutoff_self hamb hodd y h0
    rw [siteOfCoords_zero, add_zero] at this
    rw [hs]
    exact this
  have hsum : ∑ y' ∈ S, cellCutoff (patchSite S z x) y' ^ 2 = 1 := by
    rw [Finset.sum_eq_single y]
    · rw [hown]; norm_num
    · intro b _ hb
      rw [cellCutoff_eq_zero_at_cellCentre hamb hodd he hx hs hb]; norm_num
    · intro h
      exact absurd hy h
  simp [cellPartition, hown, hsum]
include hamb hodd he in
theorem isLeadingEigenvector_indicator {x : Lattice4}
    (hx : ∀ i, -(10 * cellSideLength F) ≤ x i ∧ x i < 21 * cellSideLength F) {y : F.Cell} (hy : y ∈ S)
    (hs : patchSite S z x = cellCentre 0 y) {f : F.Cell → ℍ[ℝ]} (hf1 : f y = 1) (hf0 : ∀ y', y' ≠ y → f y' = 0) :
    IsLeadingEigenvector S V (patchSite S z x) f := by
  classical
  set s := patchSite S z x with hsdef
  have hzero : ∀ y', y' ≠ y → cellCutoff s y' = 0 :=
    fun y' h => cellCutoff_eq_zero_at_cellCentre hamb hodd he hx hs h
  have hshare : cellPartition S s y = 1 := cellPartition_eq_one_at_cellCentre hamb hodd he hx hy hs
  have hshare0 : ∀ y', y' ≠ y → cellPartition S s y' = 0 :=
    fun y' h => cellPartition_eq_zero_of_cellCutoff (hzero y' h)
  refine ⟨?_, 1, by norm_num, fun y1 _ => ?_⟩
  · rw [Finset.sum_eq_single y]
    · simp [hf1]
    · intro b _ hb
      simp [hf0 b hb]
    · intro h
      exact absurd hy h
  · unfold localizationOperator
    rw [Finset.sum_eq_single y]
    · rw [Finset.sum_eq_single y]
      · rw [hshare, cellParallelTransport_self, hf1]
        by_cases h1 : y1 = y
        · subst h1
          rw [hshare, cellParallelTransport_self, hf1]
          simp
        · rw [hshare0 y1 h1, hf0 y1 h1]
          simp
      · intro b _ hb
        simp [hf0 b hb]
      · intro h
        exact absurd hy h
    · intro b _ hb
      refine Finset.sum_eq_zero fun y'' _ => ?_
      simp [hshare0 b hb]
    · intro h
      exact absurd hy h
end Centres
section Pairings
variable {F : BlockFrame} {S : Finset F.Cell} {V : F.GaugeField F.top} {z : F.Cell}
def unscaledPairing (S : Finset F.Cell) (z : F.Cell) (h : Lattice4 → Lattice4 → ℍ[ℝ]) (a b : Lattice4) : ℍ[ℝ] :=
  ∑ v ∈ localCellIndex S z, ((localCutoff F v a * localCutoff F v b : ℝ) : ℍ[ℝ]) * (star (h a v) * h b v)
theorem sqrt_localPartition {x : Lattice4} (hsq : 1 ≤ localCutoffSqSum S z x) (v : Lattice4) :
    Real.sqrt (localPartition S z v x) = localCutoff F v x * (Real.sqrt (localCutoffSqSum S z x))⁻¹ := by
  unfold localPartition
  rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (localCutoff_nonneg v x), div_eq_mul_inv]
theorem star_unitQuaternion_mul (g : UnitQuaternion) : star (g : ℍ[ℝ]) * (g : ℍ[ℝ]) = 1 :=
  coe_unitQuaternion_inv_mul g
variable (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
  (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
include hamb hodd he in
theorem quaternionPairing_eq {h : Lattice4 → Lattice4 → ℍ[ℝ]} {a b : Lattice4}
    (ha : a ∈ patchLocalSites S z) (hb : b ∈ patchLocalSites S z)
    {fa fb : F.Cell → ℍ[ℝ]} {ca cb : ℍ[ℝ]}
    (hfa : ∀ v ∈ localCellIndex S z, fa (localCell S z v) =
      ((cellTransport S V z (localCell S z v) : UnitQuaternion) : ℍ[ℝ]) *
        ((Real.sqrt (localPartition S z v a) : ℍ[ℝ]) * (h a v * ca)))
    (hfb : ∀ v ∈ localCellIndex S z, fb (localCell S z v) =
      ((cellTransport S V z (localCell S z v) : UnitQuaternion) : ℍ[ℝ]) *
        ((Real.sqrt (localPartition S z v b) : ℍ[ℝ]) * (h b v * cb)))
    (hza : ∀ y ∈ S, cellCutoff (patchSite S z a) y = 0 → fa y = 0) :
    quaternionPairing S fa fb = star ca * ((((Real.sqrt (localCutoffSqSum S z a))⁻¹ *
      (Real.sqrt (localCutoffSqSum S z b))⁻¹ : ℝ) : ℍ[ℝ]) * unscaledPairing S z h a b) * cb := by
  have hsa := one_le_localCutoffSqSum hamb hodd he ha
  have hsb := one_le_localCutoffSqSum hamb hodd he hb
  unfold quaternionPairing
  rw [sum_eq_sum_localCellIndex hamb hodd he ha.1 _ (fun y hy h0 => by simp [hza y hy h0])]
  unfold unscaledPairing
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [hfa v hv, hfb v hv, sqrt_localPartition hsa, sqrt_localPartition hsb]
  set U := ((cellTransport S V z (localCell S z v) : UnitQuaternion) : ℍ[ℝ]) with hU
  have hUU : star U * U = 1 := star_unitQuaternion_mul _
  set ra := (Real.sqrt (localCutoffSqSum S z a))⁻¹
  set rb := (Real.sqrt (localCutoffSqSum S z b))⁻¹
  set pa := localCutoff F v a
  set pb := localCutoff F v b
  simp only [Quaternion.coe_mul_eq_smul]
  rw [star_mul, quaternion_star_real_smul, star_mul, smul_mul_assoc, mul_smul_comm, mul_smul_comm,
    smul_mul_assoc]
  have e1 : star ca * star (h a v) * star U * (U * (h b v * cb)) = star ca * (star (h a v) * h b v) * cb := by
    calc _ = star ca * star (h a v) * ((star U * U) * (h b v * cb)) := by simp only [mul_assoc]
      _ = _ := by rw [hUU, one_mul]; simp only [mul_assoc]
  rw [e1]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  ring
include hamb hodd he in
theorem quaternionPairing_transportVector {h : Lattice4 → Lattice4 → ℍ[ℝ]} {a : Lattice4}
    (ha : a ∈ patchLocalSites S z) {fa : F.Cell → ℍ[ℝ]} {ca : ℍ[ℝ]}
    (hfa : ∀ v ∈ localCellIndex S z, fa (localCell S z v) =
      ((cellTransport S V z (localCell S z v) : UnitQuaternion) : ℍ[ℝ]) *
        ((Real.sqrt (localPartition S z v a) : ℍ[ℝ]) * (h a v * ca)))
    (hza : ∀ y ∈ S, cellCutoff (patchSite S z a) y = 0 → fa y = 0)
    (hmean : ∑ i ∈ localCellIndex S z, (localPartition S z i a : ℍ[ℝ]) * h a i = 1) :
    quaternionPairing S fa (transportVector S V z (patchSite S z a)) = star ca := by
  have hsa := one_le_localCutoffSqSum hamb hodd he ha
  unfold quaternionPairing
  rw [sum_eq_sum_localCellIndex hamb hodd he ha.1 _ (fun y hy h0 => by simp [hza y hy h0])]
  have hstar : ∑ i ∈ localCellIndex S z, star (h a i) * (localPartition S z i a : ℍ[ℝ]) = 1 := by
    have := congrArg star hmean
    simpa [star_sum, star_mul, Quaternion.star_coe] using this
  have e : ∀ v ∈ localCellIndex S z, star (fa (localCell S z v)) *
      transportVector S V z (patchSite S z a) (localCell S z v) =
      star ca * (star (h a v) * (localPartition S z v a : ℍ[ℝ])) := by
    intro v hv
    have hu : 0 ≤ localPartition S z v a := localPartition_nonneg v a (by linarith)
    rw [hfa v hv]
    unfold transportVector
    rw [cellPartition_patchSite_eq hamb hodd he ha.1 hv]
    set U := ((cellTransport S V z (localCell S z v) : UnitQuaternion) : ℍ[ℝ]) with hU
    have hUU : star U * U = 1 := star_unitQuaternion_mul _
    set r := Real.sqrt (localPartition S z v a) with hr
    have hrr : r * r = localPartition S z v a := Real.mul_self_sqrt hu
    simp only [Quaternion.coe_mul_eq_smul]
    rw [star_mul, quaternion_star_real_smul, star_mul]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [hrr]
    have e1 : star ca * star (h a v) * star U * U = star ca * star (h a v) := by
      rw [mul_assoc _ (star U), hUU, mul_one]
    rw [e1]
    have e2 : star (h a v) * (localPartition S z v a : ℍ[ℝ]) = (localPartition S z v a) • star (h a v) := by
      rw [← Quaternion.coe_commutes, Quaternion.coe_mul_eq_smul]
    rw [e2, mul_smul_comm]
  rw [Finset.sum_congr rfl e, ← Finset.mul_sum, hstar, mul_one]
end Pairings
section Conclusion
theorem finiteDiffBound_coe_quaternion {A : Type} [AddCommGroup A] {len : A → ℝ} {k : ℕ} {D : Set A} {B : ℝ}
    {f : A → ℝ} (h : FiniteDiffBound len k D B f) :
    FiniteDiffBound len k D B (fun x => ((f x : ℝ) : ℍ[ℝ])) := by apply _root_.YangMills.Construction.NearlyConstantKernel.finiteDiffBound_coe <;> assumption
theorem sum_coe_quaternion {ι : Type} (t : Finset ι) (f : ι → ℝ) :
    ∑ i ∈ t, (f i : ℍ[ℝ]) = ((∑ i ∈ t, f i : ℝ) : ℍ[ℝ]) := by apply _root_.YangMills.Construction.NearlyConstantKernel.sum_coe_real <;> assumption
variable {F : BlockFrame}
theorem finiteDiffBound_fst (hL : 0 < F.blockSide) {D : Set Lattice4} {W : Type} [NormedAddCommGroup W] {Bf : ℝ}
    {f : Lattice4 → W} (hB : 0 ≤ Bf) (h : FiniteDiffBound (cellScaleNorm F) 3 D Bf f) :
    FiniteDiffBound (scaledPairNorm (1 / (cellSideLength F : ℝ))) 3 (D ×ˢ D) Bf (fun p => f p.1) := by
  have hN' : (0 : ℝ) < cellSideLength F := by exact_mod_cast cellSideLength_pos (F := F) hL
  refine (h.comp (cellScaleNorm_nonneg hL) (AddMonoidHom.fst Lattice4 Lattice4) (fun a => ?_) hB).mono
    fun p hp => hp.1
  show 1 / (cellSideLength F : ℝ) * supNorm a.1 ≤
    1 / (cellSideLength F : ℝ) * ((supNorm a.1 : ℝ) + supNorm a.2)
  have : (0 : ℝ) ≤ supNorm a.2 := Nat.cast_nonneg _
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
theorem finiteDiffBound_snd (hL : 0 < F.blockSide) {D : Set Lattice4} {W : Type} [NormedAddCommGroup W] {Bf : ℝ}
    {f : Lattice4 → W} (hB : 0 ≤ Bf) (h : FiniteDiffBound (cellScaleNorm F) 3 D Bf f) :
    FiniteDiffBound (scaledPairNorm (1 / (cellSideLength F : ℝ))) 3 (D ×ˢ D) Bf (fun p => f p.2) := by
  have hN' : (0 : ℝ) < cellSideLength F := by exact_mod_cast cellSideLength_pos (F := F) hL
  refine (h.comp (cellScaleNorm_nonneg hL) (AddMonoidHom.snd Lattice4 Lattice4) (fun a => ?_) hB).mono
    fun p hp => hp.2
  show 1 / (cellSideLength F : ℝ) * supNorm a.2 ≤
    1 / (cellSideLength F : ℝ) * ((supNorm a.1 : ℝ) + supNorm a.2)
  have : (0 : ℝ) ≤ supNorm a.1 := Nat.cast_nonneg _
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
theorem polarUnit_coe_unitQuaternion (g : UnitQuaternion) : polarUnit (g : ℍ[ℝ]) = g := by apply _root_.YangMills.Construction.BlockLines.polarUnit_coe <;> assumption
variable {S : Finset F.Cell} {V : F.GaugeField F.top} {z : F.Cell}
theorem leadingFrame_at_cellCentre (hamb : IsAdmissibleAmbient F) (hL : 0 < F.blockSide) {y : F.Cell} (hy : y ∈ S)
    {s : F.Site 0} (hs : s = cellCentre 0 y) :
    leadingFrame S V s y = 1 ∧ ∀ y', y' ≠ y → leadingFrame S V s y' = 0 := by
  classical
  have hc : ∃ y ∈ S, s = cellCentre 0 y := ⟨y, hy, hs⟩
  have e : hc.choose = y := cellCentre_injective hamb hL (hc.choose_spec.2.symm.trans hs)
  unfold leadingFrame
  rw [dif_pos hc, e]
  exact ⟨by simp, fun y' h => by simp [h]⟩
theorem patchPairingLocalForm (hLine : EigenvectorNearOne)
    (hEig : UnitEigenvectorsNearOne) (hTr : patchTransportStatement) :
    patchPairingLocalFormStatement := by
  obtain ⟨C0, hC0, hT⟩ := hTr
  obtain ⟨c1, C1, hc1, hC1, hLn⟩ := hLine (33 ^ 4) partitionBound partitionBound_nonneg
  have hsq0 := cutoffSqBound_nonneg
  set e0 : ℝ := min (min c1 (1 / 64)) (1 / (4 * C1)) with he0
  refine ⟨2 * (33 ^ 4 * cutoffSqBound) + 1, 2 * (33 ^ 4 * (8 * cutoffSqBound * (10 * (C1 * (2 * C0))))) + 1,
    e0 / (2 * C0), by linarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 2 * 33 ^ 4) hsq0], by positivity,
    by positivity, ?_⟩
  intro F m S hodd hamb hm hreg s V hs hsc hcold z hz
  have hL := hodd.pos
  obtain ⟨he, hcl⟩ := closedOrthant_spec hreg (by omega) z
  obtain ⟨hTk, _⟩ := hT F m S hodd hamb hm hreg s V hs.le hcold z hz
  set η : ℝ := 2 * (C0 * s) with hη
  have hηe : η ≤ e0 := by
    rw [le_div_iff₀ (by positivity)] at hsc
    rw [hη]
    linarith
  have hηc : η ≤ c1 := hηe.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hη64 : η ≤ 1 / 64 := hηe.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hη0 : 0 ≤ η := by positivity
  have hρ : C1 * η ≤ 1 / 4 := by
    have h1 : η ≤ 1 / (4 * C1) := hηe.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    linarith
  set D := patchLocalSites S z with hD
  set Ω := localCellIndex S z with hΩ
  have hk : ∀ v ∈ Ω, ∀ v' ∈ Ω, ∀ v'' ∈ Ω, ‖localKernel S V z v v' v''‖ ≤ η :=
    fun v hv v' hv' v'' hv'' => localKernel_norm_le (by positivity) hTk hv hv' hv''
  have hsq : ∀ x ∈ D, 1 ≤ localCutoffSqSum S z x := fun x hx => one_le_localCutoffSqSum hamb hodd he hx
  obtain ⟨h, hbd, hmean, heig, huniq⟩ := hLn Lattice4 Lattice4 (cellScaleNorm F) D Ω
    (fun v x => localPartition S z v x)
    (localKernel S V z) η (cellScaleNorm_nonneg hL) card_localCellIndex_le hη0 hηc hk
    (fun v _ => localPartition_diffBound hL hsq v)
    (fun x hx v _ => localPartition_nonneg v x (by linarith [hsq x hx]))
    (fun x hx => sum_localPartition (hsq x hx))
  have hnear : ∀ x ∈ D, ∀ v ∈ Ω, ‖h x v - 1‖ ≤ 1 / 4 := fun x hx v hv => ((hbd v hv).norm_le x hx).trans hρ
  have hline : ∀ x ∈ D, IsLeadingEigenvector S V (patchSite S z x) (leadingFrame S V (patchSite S z x)) := by
    intro x hx
    by_cases hc : ∃ y ∈ S, patchSite S z x = cellCentre 0 y
    · obtain ⟨y, hy, hs'⟩ := hc
      obtain ⟨l1, l0⟩ := leadingFrame_at_cellCentre (V := V) hamb hL hy hs'
      exact isLeadingEigenvector_indicator hamb hodd he hx.1 hy hs' l1 l0
    · have hex := exists_isLeadingEigenvector hamb hodd he hx hEig hη0 hη64 hk (h x)
        (fun v hv => (hnear x hx v hv).trans (by norm_num)) (hmean x hx) (heig x hx)
      unfold leadingFrame
      rw [dif_neg hc, dif_pos hex]
      exact isLeadingEigenvector_mul_unit hex.choose_spec _
  have hform : ∀ x, ∃ c : ℍ[ℝ], x ∈ D → (c ≠ 0 ∧ ∀ v ∈ Ω, leadingFrame S V (patchSite S z x) (localCell S z v) =
      ((cellTransport S V z (localCell S z v) : UnitQuaternion) : ℍ[ℝ]) *
        ((Real.sqrt (localPartition S z v x) : ℍ[ℝ]) * (h x v * c))) := by
    intro x
    by_cases hx : x ∈ D
    · obtain ⟨⟨c, hc, hf⟩, _⟩ :=
        isLeadingEigenvector_form hamb hodd he hx hEig hη0 hη64 hk (h x) (huniq x hx) (hline x hx)
      exact ⟨c, fun _ => ⟨hc, hf⟩⟩
    · exact ⟨0, fun h' => absurd h' hx⟩
  choose cf hcf using hform
  have hzero : ∀ x ∈ D, ∀ y ∈ S, cellCutoff (patchSite S z x) y = 0 →
      leadingFrame S V (patchSite S z x) y = 0 :=
    fun x hx => (isLeadingEigenvector_form hamb hodd he hx hEig hη0 hη64 hk (h x) (huniq x hx) (hline x hx)).2
  set T : Lattice4 × Lattice4 → ℝ := fun p => ∑ v ∈ Ω, localCutoff F v p.1 * localCutoff F v p.2 with hTdef
  set X : Lattice4 × Lattice4 → ℍ[ℝ] := fun p => ∑ v ∈ Ω,
    ((localCutoff F v p.1 * localCutoff F v p.2 : ℝ) : ℍ[ℝ]) * (star (h p.1 v) * h p.2 v - 1) with hXdef
  have hPV : ∀ a b, pairingValue (fun p => T p + T p) (fun p => X p + X p) a b =
      unscaledPairing S z h a b + unscaledPairing S z h a b := by
    intro a b
    have e1 : ((T (a, b) : ℝ) : ℍ[ℝ]) + X (a, b) = unscaledPairing S z h a b := by
      simp only [hTdef, hXdef, unscaledPairing]
      rw [← sum_coe_quaternion, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [mul_sub, mul_one]
      abel
    simp only [pairingValue, Quaternion.coe_add]
    rw [← e1]
    abel
  have hrawstar : ∀ a b, unscaledPairing S z h b a = star (unscaledPairing S z h a b) := by
    intro a b
    simp only [unscaledPairing, star_sum, star_mul, star_star, Quaternion.star_coe]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [mul_comm (localCutoff F v b), Quaternion.coe_commutes]
  have hN' : (0 : ℝ) < cellSideLength F := by exact_mod_cast cellSideLength_pos (F := F) hL
  have hlen : ∀ a, 0 ≤ scaledPairNorm (1 / (cellSideLength F : ℝ)) a := fun a => by
    unfold scaledPairNorm
    positivity
  have hM : 0 ≤ 512 * cutoffBound ^ 4 := by
    have : 0 ≤ cutoffBound := by linarith [one_le_cutoffBound]
    positivity
  have hT0 : ∀ v ∈ Ω, FiniteDiffBound (scaledPairNorm (1 / (cellSideLength F : ℝ))) 3 (D ×ˢ D) cutoffSqBound
      (fun p => localCutoff F v p.1 * localCutoff F v p.2) := by
    intro v _
    have a := finiteDiffBound_fst hL hM (localCutoff_diffBound (F := F) hL D v)
    have b := finiteDiffBound_snd hL hM (localCutoff_diffBound (F := F) hL D v)
    have m := FiniteDiffBound.mul hlen hM hM a b
    have e : (2 : ℝ) ^ 3 * (512 * cutoffBound ^ 4) * (512 * cutoffBound ^ 4) = cutoffSqBound := by
      unfold cutoffSqBound
      ring
    rw [e] at m
    exact m
  have hcard : ((Ω.card : ℕ) : ℝ) ≤ 33 ^ 4 := by exact_mod_cast card_localCellIndex_le
  have hT1 : FiniteDiffBound (scaledPairNorm (1 / (cellSideLength F : ℝ))) 3 (D ×ˢ D)
      (33 ^ 4 * cutoffSqBound) T := by
    have := FiniteDiffBound.sum hlen Ω (fun _ _ => hsq0) hT0
    refine this.bound_mono hlen ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hcard hsq0
  have bd0 : FiniteDiffBound (scaledPairNorm (1 / (cellSideLength F : ℝ))) 3 (D ×ˢ D)
      (2 * (33 ^ 4 * cutoffSqBound) + 1) (fun p => T p + T p) :=
    (hT1.add hT1).bound_mono hlen (by linarith)
  set ρ0 : ℝ := C1 * η with hρ0
  have hρ00 : 0 ≤ ρ0 := by positivity
  have hterm : ∀ v ∈ Ω, FiniteDiffBound (scaledPairNorm (1 / (cellSideLength F : ℝ))) 3 (D ×ˢ D)
      (8 * cutoffSqBound * (10 * ρ0))
      (fun p => ((localCutoff F v p.1 * localCutoff F v p.2 : ℝ) : ℍ[ℝ]) * (star (h p.1 v) * h p.2 v - 1)) := by
    intro v hv
    have rl := finiteDiffBound_fst hL hρ00 (hbd v hv)
    have rr := finiteDiffBound_snd hL hρ00 (hbd v hv)
    have sl := rl.map (AddMonoidHom.mk' (fun q : ℍ[ℝ] => star q) (fun a b => star_add a b)) (fun w => by simp)
    have y1 := FiniteDiffBound.mul hlen hρ00 hρ00 sl rr
    have y2 := (sl.add rr).add y1
    have y3 := y2.bound_mono hlen (C' := 10 * ρ0) (by nlinarith [mul_nonneg hρ00 (sub_nonneg.2 hρ)])
    have y4 : FiniteDiffBound (scaledPairNorm (1 / (cellSideLength F : ℝ))) 3 (D ×ˢ D) (10 * ρ0)
        (fun p => star (h p.1 v) * h p.2 v - 1) := by
      refine y3.congr fun p => ?_
      simp only [AddMonoidHom.mk'_apply, star_sub, star_one]
      noncomm_ring
    have m := FiniteDiffBound.mul hlen hsq0 (by positivity) (finiteDiffBound_coe_quaternion (hT0 v hv)) y4
    norm_num at m ⊢
    exact m
  have hX1 : FiniteDiffBound (scaledPairNorm (1 / (cellSideLength F : ℝ))) 3 (D ×ˢ D)
      (33 ^ 4 * (8 * cutoffSqBound * (10 * ρ0))) X := by
    have := FiniteDiffBound.sum hlen Ω (fun _ _ => by positivity) hterm
    refine this.bound_mono hlen ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hcard (by positivity)
  have bd1 : FiniteDiffBound (scaledPairNorm (1 / (cellSideLength F : ℝ))) 3 (D ×ˢ D)
      ((2 * (33 ^ 4 * (8 * cutoffSqBound * (10 * (C1 * (2 * C0))))) + 1) * s) (fun p => X p + X p) := by
    refine (hX1.add hX1).bound_mono hlen ?_
    have e : 33 ^ 4 * (8 * cutoffSqBound * (10 * ρ0)) + 33 ^ 4 * (8 * cutoffSqBound * (10 * ρ0)) =
        2 * (33 ^ 4 * (8 * cutoffSqBound * (10 * (C1 * (2 * C0))))) * s := by
      rw [hρ0, hη]
      ring
    rw [e]
    nlinarith
  refine ⟨fun p => T p + T p, fun p => X p + X p, bd0, bd1, ?_, ?_, ?_, ?_⟩
  · intro a b
    rw [hPV, hPV, hrawstar a b, star_add]
  · intro a ha
    rw [hPV]
    have e : unscaledPairing S z h a a =
        ((∑ v ∈ Ω, localCutoff F v a * localCutoff F v a * Quaternion.normSq (h a v) : ℝ) : ℍ[ℝ]) := by
      rw [← sum_coe_quaternion]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [Quaternion.star_mul_self]
      simp only [Quaternion.coe_mul]
    rw [e]
    have hb : ∀ v ∈ Ω, localCutoff F v a ^ 2 * (9 / 16) ≤
        localCutoff F v a * localCutoff F v a * Quaternion.normSq (h a v) := by
      intro v hv
      have h1 := hnear a ha v hv
      have h2 := norm_sub_norm_le (1 : ℍ[ℝ]) (h a v)
      rw [norm_sub_rev, norm_one] at h2
      rw [Quaternion.normSq_eq_norm_mul_self, sq]
      exact mul_le_mul_of_nonneg_left (by nlinarith) (mul_self_nonneg _)
    have h4 := Finset.sum_le_sum hb
    rw [← Finset.sum_mul] at h4
    have h5 : 1 ≤ ∑ v ∈ Ω, localCutoff F v a ^ 2 := hsq a ha
    show 1 ≤ (∑ v ∈ Ω, localCutoff F v a * localCutoff F v a * Quaternion.normSq (h a v)) +
      (∑ v ∈ Ω, localCutoff F v a * localCutoff F v a * Quaternion.normSq (h a v))
    nlinarith
  · intro a ha b hb hne
    obtain ⟨hca, hfa⟩ := hcf a ha
    obtain ⟨hcb, hfb⟩ := hcf b hb
    have p1 := quaternionPairing_eq hamb hodd he ha hb hfa hfb (hzero a ha)
    have fa := quaternionPairing_transportVector hamb hodd he ha hfa (hzero a ha) (hmean a ha)
    have fb := quaternionPairing_transportVector hamb hodd he hb hfb (hzero b hb) (hmean b hb)
    rw [hPV] at hne ⊢
    have hraw : unscaledPairing S z h a b ≠ 0 := by
      intro h0
      apply hne
      rw [h0, add_zero]
    have h2 : unscaledPairing S z h a b + unscaledPairing S z h a b =
        ((2 : ℝ) : ℍ[ℝ]) * unscaledPairing S z h a b := by
      rw [Quaternion.coe_mul_eq_smul, two_smul]
    have two0 : ((2 : ℝ) : ℍ[ℝ]) ≠ 0 := fun h0 => by
      have := congrArg (fun q : ℍ[ℝ] => q.re) h0
      norm_num at this
    set r : ℝ := (Real.sqrt (localCutoffSqSum S z a))⁻¹ * (Real.sqrt (localCutoffSqSum S z b))⁻¹ with hr
    have hrpos : 0 < r := by
      have ha1 := hsq a ha
      have hb1 := hsq b hb
      positivity
    have r0 : (r : ℍ[ℝ]) ≠ 0 := fun h0 => hrpos.ne' (by simpa using congrArg (fun q : ℍ[ℝ] => q.re) h0)
    have sa : star (cf a) ≠ 0 := star_ne_zero.2 hca
    unfold frameChange
    rw [fa, fb, p1, h2, polarUnit_mul two0 hraw, polarUnit_coe (by norm_num), one_mul,
      polarUnit_mul (mul_ne_zero sa (mul_ne_zero r0 hraw)) hcb, polarUnit_mul sa (mul_ne_zero r0 hraw),
      polarUnit_mul r0 hraw, polarUnit_coe hrpos, one_mul, polarUnit_star (cf b), inv_inv]
  · intro y hy a ha hs'
    obtain ⟨l1, l0⟩ := leadingFrame_at_cellCentre (V := V) hamb hL hy hs'
    have hsh := cellPartition_eq_one_at_cellCentre hamb hodd he ha.1 hy hs'
    have e : quaternionPairing S (leadingFrame S V (patchSite S z a)) (transportVector S V z (patchSite S z a)) =
        ((cellTransport S V z y : UnitQuaternion) : ℍ[ℝ]) := by
      unfold quaternionPairing
      rw [Finset.sum_eq_single y]
      · rw [l1, star_one, one_mul]
        unfold transportVector
        rw [hsh]
        simp
      · intro b _ hb
        rw [l0 b hb, star_zero, zero_mul]
      · intro h'
        exact absurd hy h'
    unfold frameChange
    rw [e, polarUnit_coe_unitQuaternion]
end Conclusion
end BlockAverages
end YangMills.Construction
end
