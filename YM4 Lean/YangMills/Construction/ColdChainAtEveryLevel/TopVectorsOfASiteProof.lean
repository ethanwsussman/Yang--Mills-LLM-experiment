import YangMills.Construction.ColdChainAtEveryLevel.LocalFormOfTheLinesProof
import YangMills.Construction.ColdChainAtEveryLevel.TopVectorsOfASite
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
namespace LeadingEigenvector
open LatticeFractionalIntegration (Lattice4 supNorm)
open GaugeMap (patchSite cellSideLength)
open NearlyConstantKernel FiniteDifferences LocalPartition
variable {F : BlockFrame} {S : Finset F.Cell} {V : F.GaugeField F.top} {z : F.Cell}
def localHolonomy (S : Finset F.Cell) (V : F.GaugeField F.top) (z : F.Cell) (v v' v'' : Lattice4) : UnitQuaternion :=
  (GaugeMap.cellTransport S V z (localCell S z v))⁻¹ * cellParallelTransport S V (localCell S z v) (localCell S z v') *
    (cellParallelTransport S V (localCell S z v'') (localCell S z v'))⁻¹ * GaugeMap.cellTransport S V z (localCell S z v'')
open Classical in
def holonomyKernel (S : Finset F.Cell) (V : F.GaugeField F.top) (z : F.Cell) (v v' v'' : Lattice4) : ℍ[ℝ] :=
  if supNorm (v' - v) ≤ 3 ∧ supNorm (v' - v'') ≤ 3 then ((localHolonomy S V z v v' v'' : UnitQuaternion) : ℍ[ℝ]) - 1 else 0
theorem holonomyKernel_star (v v' v'' : Lattice4) :
    star (holonomyKernel S V z v v' v'') = holonomyKernel S V z v'' v' v := by
  classical
  unfold holonomyKernel
  by_cases h : supNorm (v' - v) ≤ 3 ∧ supNorm (v' - v'') ≤ 3
  · rw [if_pos h, if_pos h.symm, star_sub, star_one]
    congr 1
    rw [← coe_unitQuaternion_inv]
    congr 1
    simp only [localHolonomy]
    group
  · have h' : ¬ (supNorm (v' - v'') ≤ 3 ∧ supNorm (v' - v) ≤ 3) := fun a => h a.symm
    rw [if_neg h, if_neg h', star_zero]
theorem holonomyKernel_norm_le {C s : ℝ} (hs : 0 ≤ C * s)
    (hT : ∀ v ∈ localCellIndex S z, ∀ v' ∈ localCellIndex S z, supNorm (v' - v) ≤ 3 →
      ‖(((GaugeMap.cellTransport S V z (localCell S z v))⁻¹ * cellParallelTransport S V (localCell S z v) (localCell S z v') *
          GaugeMap.cellTransport S V z (localCell S z v') : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ C * s)
    {v v' v'' : Lattice4} (hv : v ∈ localCellIndex S z) (hv' : v' ∈ localCellIndex S z) (hv'' : v'' ∈ localCellIndex S z) :
    ‖holonomyKernel S V z v v' v''‖ ≤ 2 * (C * s) := by
  classical
  unfold holonomyKernel
  by_cases h : supNorm (v' - v) ≤ 3 ∧ supNorm (v' - v'') ≤ 3
  · rw [if_pos h]
    have h1 := hT v hv v' hv' h.1
    have h2 := hT v'' hv'' v' hv' h.2
    set A := (GaugeMap.cellTransport S V z (localCell S z v))⁻¹ * cellParallelTransport S V (localCell S z v) (localCell S z v') *
      GaugeMap.cellTransport S V z (localCell S z v') with hA
    set B := (GaugeMap.cellTransport S V z (localCell S z v''))⁻¹ * cellParallelTransport S V (localCell S z v'') (localCell S z v') *
      GaugeMap.cellTransport S V z (localCell S z v') with hB
    have e : localHolonomy S V z v v' v'' = A * B⁻¹ := by
      simp only [localHolonomy, hA, hB]
      group
    rw [e]
    refine (norm_coe_mul_sub_one_le _ _).trans ?_
    rw [norm_coe_inv_sub_one]
    linarith
  · rw [if_neg h, norm_zero]
    linarith
theorem supNorm_sub_le_three (hL : 0 < F.blockSide) {x v v' : Lattice4} (h1 : localCutoff F v x ≠ 0)
    (h2 : localCutoff F v' x ≠ 0) :
    supNorm (v' - v) ≤ 3 := by
  exact _root_.YangMills.Construction.BlockAverages.supNorm_sub_le_of_localCutoff_ne_zero
    (F := F) (x := x) (v := v) (v' := v') hL h1 h2
theorem coe_mul_coe_inv (g : UnitQuaternion) : (g : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := by apply _root_.YangMills.Construction.GaugeFixing.coe_mul_coe_inv <;> assumption
theorem coe_inv_mul_coe (g : UnitQuaternion) : ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (g : ℍ[ℝ]) = 1 := by apply _root_.YangMills.Construction.GaugeFixing.coe_inv_mul_coe <;> assumption
variable (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
  (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
include hamb hodd he in
theorem conj_localizationOperator_eq {x v : Lattice4}
    (hx : ∀ i, -(10 * cellSideLength F) ≤ x i ∧ x i < 21 * cellSideLength F)
    (hv : v ∈ localCellIndex S z) (f : F.Cell → ℍ[ℝ]) :
    (((GaugeMap.cellTransport S V z (localCell S z v))⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
        localizationOperator S V (patchSite S z x) f (localCell S z v) =
      (Real.sqrt (_root_.YangMills.Construction.BlockAverages.LocalPartition.weight S z v x) : ℍ[ℝ]) *
        symmetrizedApplyCore (localCellIndex S z) (fun w => _root_.YangMills.Construction.BlockAverages.LocalPartition.weight S z w x) (holonomyKernel S V z)
          (fun w => (((GaugeMap.cellTransport S V z (localCell S z w))⁻¹ : UnitQuaternion) : ℍ[ℝ]) * f (localCell S z w)) v := by
  classical
  rw [localizationOperator_patchSite_eq hamb hodd he hx hv]
  unfold symmetrizedApplyCore
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun v' hv' => Finset.sum_congr rfl fun v'' hv'' => ?_
  set u := _root_.YangMills.Construction.BlockAverages.LocalPartition.weight S z v x with hu
  set u' := _root_.YangMills.Construction.BlockAverages.LocalPartition.weight S z v' x with hu'
  set u'' := _root_.YangMills.Construction.BlockAverages.LocalPartition.weight S z v'' x with hu''
  by_cases hz : u = 0 ∨ u' = 0 ∨ u'' = 0
  · rcases hz with h | h | h <;> simp [h]
  · push_neg at hz
    have b1 := localCutoff_ne_zero_of_weight_ne_zero hz.1
    have b2 := localCutoff_ne_zero_of_weight_ne_zero hz.2.1
    have b3 := localCutoff_ne_zero_of_weight_ne_zero hz.2.2
    have n1 := supNorm_sub_le_three hodd.pos b1 b2
    have n2 := supNorm_sub_le_three hodd.pos b3 b2
    have hk : 1 + holonomyKernel S V z v v' v'' = ((localHolonomy S V z v v' v'' : UnitQuaternion) : ℍ[ℝ]) := by
      simp only [holonomyKernel, if_pos (And.intro n1 n2)]
      abel
    rw [hk]
    set Ui := (((GaugeMap.cellTransport S V z (localCell S z v))⁻¹ : UnitQuaternion) : ℍ[ℝ]) with hUi
    set X := ((cellParallelTransport S V (localCell S z v) (localCell S z v') : UnitQuaternion) : ℍ[ℝ]) with hX
    set Y := (((cellParallelTransport S V (localCell S z v'') (localCell S z v'))⁻¹ : UnitQuaternion) : ℍ[ℝ]) with hY
    set fv := f (localCell S z v'') with hfv
    have e1 : ((localHolonomy S V z v v' v'' : UnitQuaternion) : ℍ[ℝ]) *
        ((((GaugeMap.cellTransport S V z (localCell S z v''))⁻¹ : UnitQuaternion) : ℍ[ℝ]) * fv) = Ui * X * Y * fv := by
      have h1 : ((GaugeMap.cellTransport S V z (localCell S z v'') : UnitQuaternion) : ℍ[ℝ]) *
          (((GaugeMap.cellTransport S V z (localCell S z v''))⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := by
        rw [← Submonoid.coe_mul, mul_inv_cancel]
        rfl
      simp only [localHolonomy, Submonoid.coe_mul]
      rw [← mul_assoc, mul_assoc _ ((GaugeMap.cellTransport S V z (localCell S z v'') : UnitQuaternion) : ℍ[ℝ]), h1, mul_one]
    rw [e1]
    have e3 : Ui * (X * Y * fv) = Ui * X * Y * fv := by simp only [mul_assoc]
    rw [mul_smul_comm, e3]
    simp only [Quaternion.coe_mul_eq_smul, smul_smul]
    congr 1
    ring
variable {x : Lattice4} (hr : ∀ i, -(10 * cellSideLength F) ≤ x i ∧ x i < 21 * cellSideLength F)
  (hsq : 1 ≤ sumSqCutoff S z x)
  (hEig : UnitEigenvectorsNearOne) {η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 64)
  (hk : ∀ v ∈ localCellIndex S z, ∀ v' ∈ localCellIndex S z, ∀ v'' ∈ localCellIndex S z,
    ‖holonomyKernel S V z v v' v''‖ ≤ η)
  (hh : Lattice4 → ℍ[ℝ])
include hamb hodd he hr hsq hEig hη0 hη hk in
theorem eq_of_isLeadingEigenvector
    (huniq : ∀ h' : Lattice4 → ℍ[ℝ], (∀ i ∈ localCellIndex S z, ‖h' i - 1‖ ≤ 1) →
      ∑ i ∈ localCellIndex S z, (_root_.YangMills.Construction.BlockAverages.LocalPartition.weight S z i x : ℍ[ℝ]) * h' i = 1 →
      ∀ l : ℍ[ℝ], (∀ i ∈ localCellIndex S z,
        1 + perturbationApply (localCellIndex S z) (fun i => _root_.YangMills.Construction.BlockAverages.LocalPartition.weight S z i x) (holonomyKernel S V z) h' i = h' i * l) →
      ∀ i ∈ localCellIndex S z, h' i = hh i)
    {f : F.Cell → ℍ[ℝ]} (hf : IsLeadingEigenvector S V (patchSite S z x) f) :
    (∃ c : ℍ[ℝ], c ≠ 0 ∧ ∀ v ∈ localCellIndex S z, f (localCell S z v) =
      ((GaugeMap.cellTransport S V z (localCell S z v) : UnitQuaternion) : ℍ[ℝ]) *
        ((Real.sqrt (_root_.YangMills.Construction.BlockAverages.LocalPartition.weight S z v x) : ℍ[ℝ]) * (hh v * c))) ∧
      ∀ y ∈ S, cellCutoff (patchSite S z x) y = 0 → f y = 0 := by
  obtain ⟨hn, l, hl, hop⟩ := hf
  have hu : ∀ v ∈ localCellIndex S z, 0 ≤ _root_.YangMills.Construction.BlockAverages.LocalPartition.weight S z v x := fun v _ => weight_nonneg v x (by linarith)
  have hs := sum_weight_eq_one hsq
  have l0 : l ≠ 0 := by
    intro h0
    rw [h0] at hl
    norm_num at hl
  have hzero : ∀ y ∈ S, cellCutoff (patchSite S z x) y = 0 → f y = 0 := by
    intro y hy hb
    have h1 := hop y hy
    rw [localizationOperator_eq_zero_of_cellCutoff_eq_zero hb] at h1
    exact (smul_eq_zero.1 h1.symm).resolve_left l0
  set ν : Lattice4 → ℍ[ℝ] := fun w =>
    (((GaugeMap.cellTransport S V z (localCell S z w))⁻¹ : UnitQuaternion) : ℍ[ℝ]) * f (localCell S z w) with hν
  have hnorm : ∀ w, ‖ν w‖ = ‖f (localCell S z w)‖ := by
    intro w
    simp only [hν]
    rw [norm_mul, _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion, one_mul]
  have hsum : ∑ w ∈ localCellIndex S z, ‖ν w‖ ^ 2 = 1 := by
    rw [← hn, sum_eq_sum_localCellIndex hamb hodd he hr (fun y => ‖f y‖ ^ 2) (fun y hy h0 => by simp [hzero y hy h0])]
    exact Finset.sum_congr rfl fun w _ => by rw [hnorm]
  have heq : ∀ v ∈ localCellIndex S z, (Real.sqrt (_root_.YangMills.Construction.BlockAverages.LocalPartition.weight S z v x) : ℍ[ℝ]) *
      symmetrizedApplyCore (localCellIndex S z) (fun w => _root_.YangMills.Construction.BlockAverages.LocalPartition.weight S z w x) (holonomyKernel S V z) ν v =
        (l : ℍ[ℝ]) * ν v := by
    intro v hv
    rw [← conj_localizationOperator_eq hamb hodd he hr hv f, hop _ (mem_localCellIndex.1 hv).2, mul_smul_comm,
      Quaternion.coe_mul_eq_smul]
  obtain ⟨h', c, hc, hb, hm, hA, hform⟩ :=
    (hEig Lattice4 (localCellIndex S z) (fun w => _root_.YangMills.Construction.BlockAverages.LocalPartition.weight S z w x) (holonomyKernel S V z) η hu hs hη0 hη hk).1
      ν l hl hsum heq
  have hsame := huniq h' hb hm (l : ℍ[ℝ]) hA
  refine ⟨⟨c, hc, fun v hv => ?_⟩, hzero⟩
  have h1 := hform v hv
  rw [hsame v hv] at h1
  rw [← h1]
  simp only [hν]
  rw [← mul_assoc, coe_mul_coe_inv, one_mul]
include hamb hodd he hr hsq hEig hη0 hη hk in
theorem exists_isLeadingEigenvector (hb2 : ∀ v ∈ localCellIndex S z, ‖hh v - 1‖ ≤ 1 / 2)
    (hmean : ∑ i ∈ localCellIndex S z, (_root_.YangMills.Construction.BlockAverages.LocalPartition.weight S z i x : ℍ[ℝ]) * hh i = 1)
    (heig : ∀ i ∈ localCellIndex S z,
      1 + perturbationApply (localCellIndex S z) (fun i => _root_.YangMills.Construction.BlockAverages.LocalPartition.weight S z i x) (holonomyKernel S V z) hh i =
        hh i * (1 + perturbationMean (localCellIndex S z) (fun i => _root_.YangMills.Construction.BlockAverages.LocalPartition.weight S z i x) (holonomyKernel S V z) hh)) :
    ∃ f, IsLeadingEigenvector S V (patchSite S z x) f := by
  classical
  have hu : ∀ v ∈ localCellIndex S z, 0 ≤ _root_.YangMills.Construction.BlockAverages.LocalPartition.weight S z v x := fun v _ => weight_nonneg v x (by linarith)
  have hs := sum_weight_eq_one hsq
  obtain ⟨l, w, hl, hw, hsum, heq⟩ :=
    (hEig Lattice4 (localCellIndex S z) (fun w => _root_.YangMills.Construction.BlockAverages.LocalPartition.weight S z w x) (holonomyKernel S V z) η hu hs hη0 hη hk).2
      hh hb2 hmean heig (fun i _ i' _ i'' _ => holonomyKernel_star i i' i'')
  set ν : Lattice4 → ℍ[ℝ] := fun v => (Real.sqrt (_root_.YangMills.Construction.BlockAverages.LocalPartition.weight S z v x) : ℍ[ℝ]) * ((w : ℍ[ℝ]) * hh v) with hν
  set f : F.Cell → ℍ[ℝ] := fun y => ∑ v ∈ localCellIndex S z,
    if localCell S z v = y then ((GaugeMap.cellTransport S V z (localCell S z v) : UnitQuaternion) : ℍ[ℝ]) * ν v
    else 0 with hf
  have hfv : ∀ v ∈ localCellIndex S z, f (localCell S z v) =
      ((GaugeMap.cellTransport S V z (localCell S z v) : UnitQuaternion) : ℍ[ℝ]) * ν v := by
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
      have h1 : _root_.YangMills.Construction.BlockAverages.LocalPartition.weight S z v x = 0 := by
        rw [← _root_.YangMills.Construction.BlockAverages.LocalPartition.cellPartition_patchSite_eq hamb hodd he hr hv, h]
        exact cellPartition_eq_zero_of_cellCutoff_eq_zero hb
      simp [hν, h1]
    · rw [if_neg h]
  refine ⟨f, ?_, l, hl, fun y hy => ?_⟩
  · rw [sum_eq_sum_localCellIndex hamb hodd he hr (fun y => ‖f y‖ ^ 2) (fun y _ h0 => by simp [hfz y h0])]
    rw [← hsum]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [hfv v hv, norm_mul, _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion, one_mul]
  · by_cases hb : cellCutoff (patchSite S z x) y = 0
    · rw [localizationOperator_eq_zero_of_cellCutoff_eq_zero hb, hfz y hb, smul_zero]
    · obtain ⟨v, hvb, rfl⟩ := exists_localCell_of_cellCutoff_ne_zero hamb hodd he hr hb
      have hv : v ∈ localCellIndex S z := mem_localCellIndex.2 ⟨hvb, hy⟩
      have t := conj_localizationOperator_eq (V := V) hamb hodd he hr hv f
      have c1 : symmetrizedApplyCore (localCellIndex S z) (fun w => _root_.YangMills.Construction.BlockAverages.LocalPartition.weight S z w x) (holonomyKernel S V z)
          (fun w => (((GaugeMap.cellTransport S V z (localCell S z w))⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
            f (localCell S z w)) v =
          symmetrizedApplyCore (localCellIndex S z) (fun w => _root_.YangMills.Construction.BlockAverages.LocalPartition.weight S z w x) (holonomyKernel S V z) ν v := by
        unfold symmetrizedApplyCore
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb' => ?_
        have hq : (((GaugeMap.cellTransport S V z (localCell S z b))⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
            f (localCell S z b) = ν b := by
          rw [hfv b hb', ← mul_assoc, coe_inv_mul_coe, one_mul]
        simp only [hq]
      rw [c1, heq v hv] at t
      have e1 : localizationOperator S V (patchSite S z x) f (localCell S z v) =
          ((GaugeMap.cellTransport S V z (localCell S z v) : UnitQuaternion) : ℍ[ℝ]) *
            ((((GaugeMap.cellTransport S V z (localCell S z v))⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
              localizationOperator S V (patchSite S z x) f (localCell S z v)) := by
        rw [← mul_assoc, coe_mul_coe_inv, one_mul]
      rw [e1, t, hfv v hv]
      set U := ((GaugeMap.cellTransport S V z (localCell S z v) : UnitQuaternion) : ℍ[ℝ])
      calc U * ((l : ℍ[ℝ]) * ν v) = (U * (l : ℍ[ℝ])) * ν v := (mul_assoc _ _ _).symm
        _ = ((l : ℍ[ℝ]) * U) * ν v := by rw [Quaternion.coe_commutes]
        _ = (l : ℍ[ℝ]) * (U * ν v) := mul_assoc _ _ _
        _ = l • (U * ν v) := Quaternion.coe_mul_eq_smul _ _
omit hamb hodd he hr hsq hEig hη0 hη hk hh in
theorem finiteDiffBound_of_subsingleton {W : Type} [NormedAddCommGroup W] (k : ℕ) {D : Set Lattice4}
    (hD : D.Subsingleton) {B : ℝ} (hB : 0 ≤ B) {f : Lattice4 → W} (hf : ∀ x ∈ D, ‖f x‖ ≤ B) :
    FiniteDiffBound (fun _ : Lattice4 => (1 : ℝ)) k D B f := by
  induction k generalizing D B f with
  | zero => exact hf
  | succ k ih =>
    refine ⟨hf, fun b => ih (hD.anti fun x hx => hx.1) (by simpa using hB) ?_⟩
    rintro x ⟨hx, hxb⟩
    have : x + b = x := hD hxb hx
    simp [this, hB]
end LeadingEigenvector
open LatticeFractionalIntegration (Lattice4 supNorm)
open GaugeMap (patchSite cellSideLength)
open NearlyConstantKernel FiniteDifferences LocalPartition LeadingEigenvector
theorem leadingEigenvectorLine_holds (hLine : EigenvectorNearOne)
    (hEig : UnitEigenvectorsNearOne) (hTr : patchTransportStatement) :
    leadingEigenvectorLineStatement := by
  classical
  obtain ⟨C0, hC0, hT⟩ := hTr
  obtain ⟨c1, C1, hc1, hC1, hLn⟩ := hLine (33 ^ 4) 1 zero_le_one
  set e0 : ℝ := min (min c1 (1 / 64)) (1 / (4 * C1)) with he0
  refine ⟨e0 / (2 * C0), by positivity, ?_⟩
  intro F m S hodd hamb hm hreg s V hs hsc hcold x hx
  have hL := hodd.pos
  obtain ⟨z, hz, o, ho, hxo⟩ := mem_sitesOfCells.1 hx
  obtain ⟨he, -⟩ := closedOrthant_spec (S := S) hreg (by omega) z
  obtain ⟨hTk, -⟩ := hT F m S hodd hamb hm hreg s V hs.le hcold z hz
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
  obtain ⟨hc0, hc1'⟩ := cellSideLength_half (F := F) hodd
  have hoi : ∀ i, |o i| ≤ (cellSideLength F - 1) / 2 := by
    intro i
    have := Fintype.mem_piFinset.1 ho i
    have e : (((F.blockSide ^ (F.top - 0) : ℕ) : ℤ)) = cellSideLength F := by
      simp [cellSideLength]
    rw [Finset.mem_Icc, e] at this
    exact abs_le.2 this
  set a : Lattice4 := fun i => closedOrthant S z i * o i + (cellSideLength F - 1) / 2 with ha
  have hxa : patchSite S z a = x := by
    rw [hxo]
    unfold patchSite
    congr 2
    funext i
    simp only [ha, add_sub_cancel_right, ← mul_assoc, closedOrthant_mul_self he i, one_mul]
  have hr : ∀ i, -(10 * cellSideLength F) ≤ a i ∧ a i < 21 * cellSideLength F := by
    intro i
    have h1 := abs_le.1 (hoi i)
    simp only [ha]
    rcases he i with h | h <;> rw [h] <;> constructor <;> omega
  have hxs : patchSite S z a ∈ sitesOfCells S 0 := by rw [hxa]; exact hx
  have hsq : 1 ≤ sumSqCutoff S z a := one_le_sumSqCutoff hamb hodd he hr hxs
  set Ω := localCellIndex S z with hΩ
  have hk : ∀ v ∈ Ω, ∀ v' ∈ Ω, ∀ v'' ∈ Ω, ‖holonomyKernel S V z v v' v''‖ ≤ η :=
    fun v hv v' hv' v'' hv'' => holonomyKernel_norm_le (by positivity) hTk hv hv' hv''
  have hu : ∀ v ∈ Ω, 0 ≤ _root_.YangMills.Construction.BlockAverages.LocalPartition.weight S z v a := fun v _ => weight_nonneg v a (by linarith)
  have hsum := sum_weight_eq_one hsq
  have hle1 : ∀ v ∈ Ω, _root_.YangMills.Construction.BlockAverages.LocalPartition.weight S z v a ≤ 1 := fun v hv => by
    rw [← hsum]
    exact Finset.single_le_sum (f := fun v => _root_.YangMills.Construction.BlockAverages.LocalPartition.weight S z v a) hu hv
  obtain ⟨h, hbd, hmean, heig, huniq⟩ := hLn Lattice4 Lattice4 (fun _ => (1 : ℝ)) {a} Ω
    (fun v x => _root_.YangMills.Construction.BlockAverages.LocalPartition.weight S z v x)
    (holonomyKernel S V z) η (fun _ => zero_le_one) card_localCellIndex_le hη0 hηc hk
    (fun v hv => finiteDiffBound_of_subsingleton 3 Set.subsingleton_singleton zero_le_one (fun x hx => by
      rw [Set.mem_singleton_iff.1 hx, Real.norm_eq_abs, abs_of_nonneg (hu v hv)]
      exact hle1 v hv))
    (fun x hx v hv => by rw [Set.mem_singleton_iff.1 hx]; exact hu v hv)
    (fun x hx => by rw [Set.mem_singleton_iff.1 hx]; exact hsum)
  have hmem : a ∈ ({a} : Set Lattice4) := rfl
  have hnear : ∀ v ∈ Ω, ‖h a v - 1‖ ≤ 1 / 4 := fun v hv => ((hbd v hv).norm_le a hmem).trans hρ
  have hform : ∀ {f}, IsLeadingEigenvector S V x f → _ := fun {f} hf =>
    eq_of_isLeadingEigenvector hamb hodd he hr hsq hEig hη0 hη64 hk (h a) (huniq a hmem) (f := f)
      (by rw [hxa]; exact hf)
  refine ⟨by
    rw [← hxa]
    exact _root_.YangMills.Construction.BlockAverages.LeadingEigenvector.exists_isLeadingEigenvector hamb hodd he hr hsq hEig hη0 hη64 hk (h a)
      (fun v hv => (hnear v hv).trans (by norm_num)) (hmean a hmem) (heig a hmem), ?_⟩
  intro f g hf hg
  obtain ⟨⟨c, hc, hfv⟩, hfz⟩ := hform hf
  obtain ⟨⟨c', hc', hgv⟩, hgz⟩ := hform hg
  have hcell : enclosingCell x = z := by
    rw [hxo]
    exact enclosingCell_cellCentre_add hodd z o ho
  have hlc : localCell S z 0 = z := by
    have e : (fun i => closedOrthant S z i * (0 : Lattice4) i) = 0 := by
      funext i
      simp
    unfold localCell
    rw [e, siteOfCoords_zero, add_zero]
  have h0mem : (0 : Lattice4) ∈ Ω := by
    refine mem_localCellIndex.2 ⟨fun i => by simp, ?_⟩
    rw [hlc]
    exact hz
  have hbump : localCutoff F 0 a = 1 := by
    have h1 := cellCutoff_patchSite_eq hamb hodd he hr h0mem
    rw [hlc, hxa, hxo] at h1
    have e : F.top - 0 = F.top := by omega
    rw [e] at ho
    rw [← h1]
    exact cellCutoff_self hamb hodd z ho
  have hsh : 0 < _root_.YangMills.Construction.BlockAverages.LocalPartition.weight S z 0 a := by
    unfold _root_.YangMills.Construction.BlockAverages.LocalPartition.weight
    rw [hbump]
    have : 0 < sumSqCutoff S z a := by linarith
    positivity
  have hq0 : h a 0 ≠ 0 := by
    intro h0
    have := hnear 0 h0mem
    rw [h0, zero_sub, norm_neg, norm_one] at this
    norm_num at this
  constructor
  · rw [hcell]
    have h1 := hfv 0 h0mem
    rw [hlc] at h1
    rw [h1]
    refine mul_ne_zero (coe_unitQuaternion_ne_zero _) (mul_ne_zero ?_ (mul_ne_zero hq0 hc))
    intro h0
    have := congrArg (fun q : ℍ[ℝ] => q.re) h0
    simp at this
    have h2 : 0 < Real.sqrt (_root_.YangMills.Construction.BlockAverages.LocalPartition.weight S z 0 a) := Real.sqrt_pos.2 hsh
    linarith [this.symm ▸ h2]
  · set p : ℍ[ℝ] := c⁻¹ * c' with hp
    have hrel : ∀ y ∈ S, g y = f y * p := by
      intro y hy
      by_cases hb : cellCutoff (patchSite S z a) y = 0
      · rw [hgz y hy hb, hfz y hy hb, zero_mul]
      · obtain ⟨v, hvb, rfl⟩ := exists_localCell_of_cellCutoff_ne_zero hamb hodd he hr hb
        have hv : v ∈ Ω := mem_localCellIndex.2 ⟨hvb, hy⟩
        rw [hgv v hv, hfv v hv, hp]
        simp only [mul_assoc]
        rw [mul_inv_cancel_left₀ hc]
    have hpn : ‖p‖ = 1 := by
      have e1 : ∑ y ∈ S, ‖g y‖ ^ 2 = ‖p‖ ^ 2 * ∑ y ∈ S, ‖f y‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y hy => ?_
        rw [hrel y hy, norm_mul]
        ring
      rw [hg.1, hf.1] at e1
      have h4 := norm_nonneg p
      nlinarith
    have hp0 : p ≠ 0 := fun h0 => by
      rw [h0, norm_zero] at hpn
      norm_num at hpn
    refine ⟨polarUnit p, fun y hy => ?_⟩
    rw [coe_polarUnit hp0, hpn, inv_one, one_smul]
    exact hrel y hy
end YangMills.Construction.BlockAverages
end
