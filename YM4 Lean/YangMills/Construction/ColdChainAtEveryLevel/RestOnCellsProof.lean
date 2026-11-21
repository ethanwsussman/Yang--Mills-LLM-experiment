import YangMills.Construction.ColdChainAtEveryLevel.PatchOfADifference
import YangMills.Construction.ColdChainAtEveryLevel.PotentialsInAPatch
import YangMills.Construction.ColdChainAtEveryLevel.RestOnCells
import YangMills.Construction.ColdChainAtEveryLevel.SitesOfAPatch
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.GaugeRemainderBounds
open BlockAverages GaugeMap PatchPoints PatchFrames PatchDifferences BondShares LatticeFractionalIntegration
section Basics
variable {F : BlockFrame} {S : Finset F.Cell}
theorem adjointAction_mul (g h : UnitQuaternion) (w : ℍ[ℝ]) :
    adjointAction (g * h) w = adjointAction g (adjointAction h w) := by apply _root_.YangMills.Construction.BlockAverages.adjointAction_mul <;> assumption
theorem adjointAction_one (w : ℍ[ℝ]) : adjointAction (1 : UnitQuaternion) w = w := by
  simp [adjointAction]
theorem adjointAction_add (g : UnitQuaternion) (p q : ℍ[ℝ]) :
    adjointAction g (p + q) = adjointAction g p + adjointAction g q := by apply _root_.YangMills.Construction.BlockAverages.adjointAction_add <;> assumption
theorem adjointAction_sub (g : UnitQuaternion) (p q : ℍ[ℝ]) :
    adjointAction g (p - q) = adjointAction g p - adjointAction g q := by apply _root_.YangMills.Construction.BlockLines.adjointAction_sub <;> assumption
theorem adjointAction_neg (g : UnitQuaternion) (p : ℍ[ℝ]) : adjointAction g (-p) = - adjointAction g p := by
  simp only [adjointAction, mul_neg, neg_mul]
theorem adjointAction_smul (g : UnitQuaternion) (a : ℝ) (p : ℍ[ℝ]) :
    adjointAction g (a • p) = a • adjointAction g p := by apply _root_.YangMills.Construction.BlockAverages.adjointAction_smul <;> assumption
theorem adjointAction_sum (g : UnitQuaternion) {ι : Type} (t : Finset ι) (f : ι → ℍ[ℝ]) :
    adjointAction g (∑ i ∈ t, f i) = ∑ i ∈ t, adjointAction g (f i) := by
  simp only [adjointAction, Finset.mul_sum, Finset.sum_mul]
theorem norm_adjointAction (g : UnitQuaternion) (w : ℍ[ℝ]) : ‖adjointAction g w‖ = ‖w‖ := by apply _root_.YangMills.Construction.BlockLines.norm_adjointAction <;> assumption
theorem norm_adjointAction_sub_self_le (g : UnitQuaternion) (q : ℍ[ℝ]) :
    ‖adjointAction g q - q‖ ≤ 2 * ‖(g : ℍ[ℝ]) - 1‖ * ‖q‖ := by apply _root_.YangMills.Construction.BlockLines.norm_adjointAction_sub_le <;> assumption
theorem cellPartition_nonneg (x : F.Site 0) (y : F.Cell) : 0 ≤ cellPartition S x y :=
  div_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
theorem cellPartition_le_one (x : F.Site 0) {y : F.Cell} (hy : y ∈ S) : cellPartition S x y ≤ 1 := by apply _root_.YangMills.Construction.BlockAverages.PatchLocality.cellPartition_le_one <;> assumption
theorem sum_cellPartition (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {x : F.Site 0}
    (hx : x ∈ sitesOfCells S 0) : ∑ y ∈ S, cellPartition S x y = 1 := by apply _root_.YangMills.Construction.BlockAverages.PatchLocality.sum_cellPartition <;> assumption
theorem cellSupDist_le_one_of_cellPartition_ne_zero (hodd : Odd F.blockSide) {x : F.Site 0} {z : F.Cell}
    (h : cellPartition S x z ≠ 0) : cellSupDist (enclosingCell x) z ≤ 1 := by
  have hL := hodd.pos
  have hb : cellCutoff x z ≠ 0 := fun h0 => h (by simp [cellPartition, h0])
  have hNr : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by
    have : (0 : ℝ) < F.blockSide := by exact_mod_cast hL
    positivity
  refine cellSupDist_enclosingCell_le hodd x z 1 fun i => ?_
  have f1 : cutoffProfile ((((x - cellCentre 0 z) i).valMinAbs : ℝ) / (F.blockSide : ℝ) ^ F.top) ≠ 0 :=
    fun h0 => hb (Finset.prod_eq_zero (Finset.mem_univ i) h0)
  have g1 := abs_lt_of_cutoffProfile_ne_zero f1
  rw [abs_div, abs_of_pos hNr, div_lt_iff₀ hNr] at g1
  have g2 : |(((x - cellCentre 0 z) i).valMinAbs : ℝ)| ≤ (F.blockSide : ℝ) ^ F.top := by nlinarith
  have g3 : ((((x - cellCentre 0 z) i).valMinAbs).natAbs : ℝ) ≤ ((F.blockSide ^ F.top : ℕ) : ℝ) := by
    have : ((((x - cellCentre 0 z) i).valMinAbs).natAbs : ℝ) = |(((x - cellCentre 0 z) i).valMinAbs : ℝ)| := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [this]
    push_cast
    exact g2
  have g4 : (((x - cellCentre 0 z) i).valMinAbs).natAbs ≤ F.blockSide ^ F.top := by exact_mod_cast g3
  simpa using g4
end Basics
section Glue
variable {F : BlockFrame} {S : Finset F.Cell} {V : F.GaugeField F.top}
def gluedRemainder (S : Finset F.Cell) (V : F.GaugeField F.top) (E : F.Cell → Lattice4 → ℍ[ℝ]) (s : F.Site 0) :
    ℍ[ℝ] :=
  ∑ z ∈ S, cellPartition S s z • adjointAction (frameChange S V z s) (E z (patchChart S z s))
theorem patchChart_mem_patchDomain_of_near (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {z : F.Cell}
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) {s : F.Site 0} (hs : s ∈ sitesOfCells S 0)
    (hd : cellSupDist (enclosingCell s) z ≤ 10) : patchChart S z s ∈ patchDomain S z := by
  obtain ⟨y, hy, h, hh, rfl⟩ := mem_sitesOfCells.1 hs
  rw [enclosingCell_cellCentre_add hodd y h hh] at hd
  rw [cellSupDist_symm] at hd
  exact patchChart_mem_patchDomain hamb hodd he hy hd (by simpa using hh)
theorem gluedPotential_eq (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {m : ℕ}
    (hreg : IsOrthantRegular S m) (hm : 32 ≤ m)
    {ξ : F.Site 0 → ℍ[ℝ]} {E : F.Cell → Lattice4 → ℍ[ℝ]} {D : F.Cell → F.Site 0 → ℝ} {C : ℝ}
    (hR : ∀ z ∈ S, PatchRemainder S V z ξ (E z) (D z) C) {s : F.Site 0} (hs : s ∈ sitesOfCells S 0) :
    gluedPotential S V (referenceFieldChain S V 0) (covariantDiff (referenceFieldChain S V 0) ξ) s =
      - ξ s + gluedRemainder S V E s := by
  have hterm : ∀ z ∈ S, cellPartition S s z • adjointAction (frameChange S V z s)
      (localPotential S V (referenceFieldChain S V 0) z (covariantDiff (referenceFieldChain S V 0) ξ)
        (patchChart S z s) -
       localPotentialMean S V (referenceFieldChain S V 0) z (covariantDiff (referenceFieldChain S V 0) ξ)) =
      cellPartition S s z • (- ξ s) +
        cellPartition S s z • adjointAction (frameChange S V z s) (E z (patchChart S z s)) := by
    intro z hz
    by_cases h0 : cellPartition S s z = 0
    · simp [h0]
    · have he := (closedOrthant_spec (S := S) hreg hm z).1
      have hd := cellSupDist_le_one_of_cellPartition_ne_zero hodd h0
      have ha := patchChart_mem_patchDomain_of_near hamb hodd he hs (hd.trans (by norm_num))
      rw [(hR z hz).localPotential_sub_mean _ ha, adjointAction_add, adjointAction_neg, smul_add]
      simp only [localSection, patchSite_patchChart he]
      have e : adjointAction (frameChange S V z s) (adjointAction (frameChange S V z s)⁻¹ (ξ s)) = ξ s := by
        rw [← adjointAction_mul, mul_inv_cancel, adjointAction_one]
      rw [e]
  simp only [gluedPotential, gluedRemainder]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.sum_smul, sum_cellPartition hamb hodd hs,
    one_smul]
theorem frameCellMean_congr (hodd : Odd F.blockSide) {y : F.Cell} (hy : y ∈ S)
    (he : ∀ i, closedOrthant S y i = 1 ∨ closedOrthant S y i = -1)
    {ξ ξ' : F.Site 0 → ℍ[ℝ]} (h : ∀ s ∈ sitesOfCells S 0, ξ s = ξ' s) :
    frameCellMean S V y ξ = frameCellMean S V y ξ' := by
  obtain ⟨h0, h1⟩ := cellSideLength_half (F := F) hodd
  simp only [frameCellMean]
  congr 1
  refine Finset.sum_congr rfl fun x hx => ?_
  have hxi := fun i => Finset.mem_Ico.1 (Fintype.mem_piFinset.1 hx i)
  have hmem : patchSite S y x ∈ sitesOfCells S 0 := by
    refine mem_sitesOfCells.2 ⟨y, hy, fun i => closedOrthant S y i * (x i - (cellSideLength F - 1) / 2), ?_, rfl⟩
    have : (fun i => closedOrthant S y i * (x i - (cellSideLength F - 1) / 2)) ∈
        centredCube (F.blockSide ^ F.top) := by
      rw [mem_centredCube_iff]
      intro i
      have := hxi i
      rcases he i with hs | hs <;> rw [hs] <;> constructor <;> omega
    simpa using this
  rw [h _ hmem]
theorem frameCellMean_neg_add (y : F.Cell) (ξ A : F.Site 0 → ℍ[ℝ]) :
    frameCellMean S V y (fun s => - ξ s + A s) = - frameCellMean S V y ξ + frameCellMean S V y A := by
  simp only [frameCellMean, adjointAction_add, adjointAction_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    smul_add, smul_neg]
theorem gaugeRemainder_eq (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {m : ℕ}
    (hreg : IsOrthantRegular S m) (hm : 32 ≤ m)
    {ξ : F.Site 0 → ℍ[ℝ]} (hξ : CellMeanFree S V ξ) {E : F.Cell → Lattice4 → ℍ[ℝ]} {D : F.Cell → F.Site 0 → ℝ}
    {C : ℝ} (hR : ∀ z ∈ S, PatchRemainder S V z ξ (E z) (D z) C) {s : F.Site 0} (hs : s ∈ sitesOfCells S 0) :
    gaugeRemainder S V ξ s = gluedRemainder S V E s -
      ∑ y ∈ S, normalizedBump S s y • adjointAction (frameChange S V y s)
        (frameCellMean S V y (gluedRemainder S V E)) := by
  have hcm : ∀ y ∈ S, frameCellMean S V y (gluedPotential S V (referenceFieldChain S V 0)
      (covariantDiff (referenceFieldChain S V 0) ξ)) = frameCellMean S V y (gluedRemainder S V E) := by
    intro y hy
    have he := (closedOrthant_spec (S := S) hreg hm y).1
    rw [frameCellMean_congr hodd hy he fun t ht => gluedPotential_eq hamb hodd hreg hm hR ht,
      frameCellMean_neg_add, hξ y hy]
    simp
  simp only [gaugeRemainder, gaugeMap]
  rw [gluedPotential_eq hamb hodd hreg hm hR hs, Finset.sum_congr rfl fun y hy => by rw [hcm y hy]]
  abel
theorem cellMeanFree_gaugeRemainder (hodd : Odd F.blockSide) {m : ℕ} (hreg : IsOrthantRegular S m) (hm : 32 ≤ m)
    (hL : 0 < F.blockSide) {ξ : F.Site 0 → ℍ[ℝ]} (hξ : CellMeanFree S V ξ)
    (hG : CellMeanFree S V (gaugeMap S V (referenceFieldChain S V 0)
      (covariantDiff (referenceFieldChain S V 0) ξ))) : CellMeanFree S V (gaugeRemainder S V ξ) := by
  intro y hy
  have e : frameCellMean S V y (gaugeRemainder S V ξ) = frameCellMean S V y (gaugeMap S V (referenceFieldChain S V 0)
      (covariantDiff (referenceFieldChain S V 0) ξ)) + frameCellMean S V y ξ := by
    simp only [frameCellMean, gaugeRemainder, adjointAction_add, Finset.sum_add_distrib, smul_add]
  rw [e, hG y hy, hξ y hy, add_zero]
end Glue
section Terms
variable {F : BlockFrame} {S : Finset F.Cell} {V : F.GaugeField F.top}
theorem cellSupDist_triangle (x y z : F.Cell) : cellSupDist x z ≤ cellSupDist x y + cellSupDist y z := by apply _root_.YangMills.Construction.BlockAverages.PatchLocality.cellSupDist_triangle <;> assumption
theorem patchChart_add_unitStep (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {z : F.Cell}
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    {s : F.Site 0} (i : Fin 4) (ha : patchChart S z s ∈ patchDomain S z) :
    (closedOrthant S z i = 1 ∧ patchChart S z (s + unitStep 0 i) = patchChart S z s + basisVector i) ∨
      (closedOrthant S z i = -1 ∧ patchChart S z s = patchChart S z (s + unitStep 0 i) + basisVector i) := by
  have h := patchChart_add_stepDisplacement hamb hodd he (s := s) (i, true) (patchDomain_coord_bounds ha)
  have hv : stepDisplacement (F := F) 0 ((i, true) : PathStep) = unitStep 0 i := by simp [stepDisplacement]
  rw [hv] at h
  have hk : ∀ k, closedOrthant S z k * stepOffset ((i, true) : PathStep) k =
      closedOrthant S z i * basisVector i k := by
    intro k
    simp only [stepOffset, basisVector, if_true]
    by_cases hki : k = i
    · subst hki
      rfl
    · simp [hki]
  rcases he i with h1 | h1
  · left
    refine ⟨h1, ?_⟩
    rw [h]
    funext k
    simp only [hk, h1, one_mul, Pi.add_apply]
  · right
    refine ⟨h1, ?_⟩
    rw [h]
    funext k
    simp only [hk, h1, Pi.add_apply]
    ring
theorem supNorm_neg_basisVector (i : Fin 4) : supNorm (- basisVector i) = 1 := by
  have e : supNorm (- basisVector i) = supNorm (basisVector i) := by
    unfold supNorm
    refine Finset.sup_congr rfl fun k _ => ?_
    simp
  rw [e, PatchDifferences.supNorm_basisVector]
def remainderSize (S : Finset F.Cell) (z : F.Cell) (e : Lattice4 → ℍ[ℝ]) : F.Site 0 → ℝ :=
  restrictToPatch S z fun t => ‖e (patchChart S z t)‖
theorem norm_gluedTerm_sub_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {m : ℕ}
    (hreg : IsOrthantRegular S m) (hm : 32 ≤ m)
    {ξ : F.Site 0 → ℍ[ℝ]} {z : F.Cell} {R : Lattice4 → Lattice4 → UnitQuaternion} {Cs r Ck : ℝ}
    {e : Lattice4 → ℍ[ℝ]} {Dl : F.Site 0 → ℝ}
    (hz : z ∈ S) (hF : IsPatchFrame S V z R Cs r) (hr1 : 1 ≤ r * cellSideLength F) (hC : 0 ≤ Cs)
    (hR : PatchRemainder S V z ξ e Dl Ck) {s : F.Site 0} {i : Fin 4} (hs : s ∈ sitesOfCells S 0)
    (hs' : s + unitStep 0 i ∈ sitesOfCells S 0) :
    ‖cellPartition S (s + unitStep 0 i) z • adjointAction (leadingTransport S V s (s + unitStep 0 i))
        (adjointAction (frameChange S V z (s + unitStep 0 i)) (e (patchChart S z (s + unitStep 0 i)))) -
      cellPartition S s z • adjointAction (frameChange S V z s) (e (patchChart S z s))‖ ≤
      2 * Cs / (cellSideLength F : ℝ) * remainderSize S z e (s + unitStep 0 i) +
        weightConstant / (F.blockSide : ℝ) ^ F.top * remainderSize S z e s + (Dl s + Dl (s + unitStep 0 i)) := by
  classical
  have hL := hodd.pos
  have he := (closedOrthant_spec (S := S) hreg hm z).1
  have hN0 : (0 : ℝ) < cellSideLength F := by exact_mod_cast cellSideLength_pos (F := F) hL
  have hE0 : ∀ t, 0 ≤ remainderSize S z e t := restrictToPatch_nonneg fun _ => norm_nonneg _
  have hD0 := hR.stepBound_nonneg
  have hc1 : 0 ≤ 2 * Cs / (cellSideLength F : ℝ) := div_nonneg (mul_nonneg (by norm_num) hC) hN0.le
  have hc2 : 0 ≤ weightConstant / (F.blockSide : ℝ) ^ F.top := by
    have hb := one_le_cutoffBound
    unfold weightConstant
    positivity
  have hrhs : 0 ≤ 2 * Cs / (cellSideLength F : ℝ) * remainderSize S z e (s + unitStep 0 i) +
        weightConstant / (F.blockSide : ℝ) ^ F.top * remainderSize S z e s + (Dl s + Dl (s + unitStep 0 i)) :=
    add_nonneg (add_nonneg (mul_nonneg hc1 (hE0 _)) (mul_nonneg hc2 (hE0 _))) (add_nonneg (hD0 _) (hD0 _))
  by_cases h0 : cellPartition S s z = 0 ∧ cellPartition S (s + unitStep 0 i) z = 0
  · rw [h0.1, h0.2]
    simpa using hrhs
  have hstep : cellSupDist (enclosingCell (s + unitStep 0 i)) (enclosingCell s) ≤ 1 := by
    obtain ⟨y, _, h, hh, rfl⟩ := mem_sitesOfCells.1 hs
    have hst := cellSupDist_enclosingCell_step hodd (y := y) (h := h) (by simpa using hh) (i, true)
    have hv : stepDisplacement (F := F) 0 ((i, true) : PathStep) = unitStep 0 i := by simp [stepDisplacement]
    rw [hv] at hst
    rw [enclosingCell_cellCentre_add hodd y h hh]
    exact hst
  have hnear : cellSupDist (enclosingCell s) z ≤ 2 ∧ cellSupDist (enclosingCell (s + unitStep 0 i)) z ≤ 2 := by
    by_cases h1 : cellPartition S s z = 0
    · have h2 : cellPartition S (s + unitStep 0 i) z ≠ 0 := fun h2 => h0 ⟨h1, h2⟩
      have h3 := cellSupDist_le_one_of_cellPartition_ne_zero hodd h2
      refine ⟨?_, by omega⟩
      have h4 := cellSupDist_triangle (enclosingCell s) (enclosingCell (s + unitStep 0 i)) z
      have h5 : cellSupDist (enclosingCell s) (enclosingCell (s + unitStep 0 i)) =
          cellSupDist (enclosingCell (s + unitStep 0 i)) (enclosingCell s) :=
        cellSupDist_symm _ _
      omega
    · have h3 := cellSupDist_le_one_of_cellPartition_ne_zero hodd h1
      refine ⟨by omega, ?_⟩
      have h4 := cellSupDist_triangle (enclosingCell (s + unitStep 0 i)) (enclosingCell s) z
      omega
  have ha := patchChart_mem_patchDomain_of_near hamb hodd he hs (hnear.1.trans (by norm_num))
  have ha' := patchChart_mem_patchDomain_of_near hamb hodd he hs' (hnear.2.trans (by norm_num))
  obtain ⟨a, hadef⟩ : ∃ a, a = patchChart S z s := ⟨_, rfl⟩
  obtain ⟨a', hadef'⟩ : ∃ a', a' = patchChart S z (s + unitStep 0 i) := ⟨_, rfl⟩
  rw [← hadef] at ha
  rw [← hadef'] at ha'
  have hsa : patchSite S z a = s := by rw [hadef]; exact patchSite_patchChart he s
  have hsa' : patchSite S z a' = s + unitStep 0 i := by rw [hadef']; exact patchSite_patchChart he _
  have hor := patchChart_add_unitStep hamb hodd he (s := s) i (hadef ▸ ha)
  rw [← hadef, ← hadef'] at hor
  have hsup : supNorm (a' - a) = 1 := by
    rcases hor with ⟨_, h⟩ | ⟨_, h⟩
    · rw [h, add_sub_cancel_left]
      exact PatchDifferences.supNorm_basisVector i
    · rw [h, sub_add_cancel_left]
      exact supNorm_neg_basisVector i
  have hdist : (supNorm (a' - a) : ℝ) ≤ r * cellSideLength F := by
    rw [hsup]
    simpa using hr1
  have hlink := hF.leadingTransport_eq a ha a' ha' hdist
  have hnr := hF.norm_sub_one_le a ha a' ha' hdist
  rw [hsup] at hnr
  rw [hsa, hsa'] at hlink
  have hnr' : ‖((R a a' : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ Cs / (cellSideLength F : ℝ) := by
    simpa [div_eq_mul_inv] using hnr
  have hstepE : ‖e a' - e a‖ ≤ Dl s + Dl (s + unitStep 0 i) := by
    rcases hor with ⟨_, h⟩ | ⟨_, h⟩
    · have h1 := hR.norm_step_le a ha i (by rw [← h]; exact ha')
      rw [← h, hsa] at h1
      have := hD0 (s + unitStep 0 i)
      linarith
    · have h1 := hR.norm_step_le a' ha' i (by rw [← h]; exact ha)
      rw [← h, hsa'] at h1
      rw [norm_sub_rev]
      have := hD0 s
      linarith
  have hra : remainderSize S z e s = ‖e a‖ := by
    have hm1 : s ∈ patchSiteSet S z := by
      rw [← hsa]
      exact Finset.mem_image_of_mem _ ha
    simp only [remainderSize]
    rw [restrictToPatch_of_mem hm1, ← hadef]
  have hra' : remainderSize S z e (s + unitStep 0 i) = ‖e a'‖ := by
    have hm1 : s + unitStep 0 i ∈ patchSiteSet S z := by
      rw [← hsa']
      exact Finset.mem_image_of_mem _ ha'
    simp only [remainderSize]
    rw [restrictToPatch_of_mem hm1, ← hadef']
  have hdcoord : ∀ k, |a k - a' k| ≤ 1 := by
    intro k
    have hu : |basisVector i k| ≤ 1 := by
      simp only [basisVector]
      by_cases hk : k = i
      · subst hk
        simp
      · simp [hk]
    rcases hor with ⟨_, h⟩ | ⟨_, h⟩
    · rw [h]
      simpa [abs_neg] using hu
    · rw [h]
      simpa using hu
  have hshare := cellPartition_abs_sub_le hamb hodd he (patchDomain_coord_bounds ha) (patchDomain_coord_bounds ha')
    (by rw [hsa]; exact hs) (by rw [hsa']; exact hs') hdcoord hz
  rw [hsa, hsa'] at hshare
  obtain ⟨χ, hχ⟩ : ∃ χ, χ = cellPartition S s z := ⟨_, rfl⟩
  obtain ⟨χ', hχ'⟩ : ∃ χ', χ' = cellPartition S (s + unitStep 0 i) z := ⟨_, rfl⟩
  rw [← hχ, ← hχ'] at hshare
  have hχ0 : 0 ≤ χ' := hχ' ▸ cellPartition_nonneg _ _
  have hχ1 : χ' ≤ 1 := hχ' ▸ cellPartition_le_one _ hz
  rw [← hχ, ← hχ', ← hadef, ← hadef', hlink, hra, hra']
  obtain ⟨f, hf⟩ : ∃ f, f = frameChange S V z s := ⟨_, rfl⟩
  obtain ⟨f', hf'⟩ : ∃ f', f' = frameChange S V z (s + unitStep 0 i) := ⟨_, rfl⟩
  rw [← hf, ← hf']
  have e1 : adjointAction (f * R a a' * f'⁻¹) (adjointAction f' (e a')) =
      adjointAction f (adjointAction (R a a') (e a')) := by
    rw [← adjointAction_mul, ← adjointAction_mul]
    congr 1
    group
  have e1' : χ' • adjointAction f (adjointAction (R a a') (e a')) - χ • adjointAction f (e a) =
      adjointAction f (χ' • adjointAction (R a a') (e a') - χ • e a) := by
    rw [adjointAction_sub, adjointAction_smul, adjointAction_smul]
  rw [e1, e1', norm_adjointAction]
  have e2 : χ' • adjointAction (R a a') (e a') - χ • e a =
      χ' • (adjointAction (R a a') (e a') - e a') + χ' • (e a' - e a) + (χ' - χ) • e a := by
    simp only [smul_sub, sub_smul]
    abel
  rw [e2]
  have n1 : ‖χ' • (adjointAction (R a a') (e a') - e a')‖ + ‖χ' • (e a' - e a)‖ ≤
      2 * (Cs / (cellSideLength F : ℝ)) * ‖e a'‖ + (Dl s + Dl (s + unitStep 0 i)) := by
    rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hχ0]
    have h1 := norm_adjointAction_sub_self_le (R a a') (e a')
    have h2 : 2 * ‖((R a a' : UnitQuaternion) : ℍ[ℝ]) - 1‖ * ‖e a'‖ ≤
        2 * (Cs / (cellSideLength F : ℝ)) * ‖e a'‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    have h3 : 0 ≤ 2 * (Cs / (cellSideLength F : ℝ)) * ‖e a'‖ :=
      mul_nonneg (mul_nonneg (by norm_num) (div_nonneg hC hN0.le)) (norm_nonneg _)
    have h4 : χ' * ‖adjointAction (R a a') (e a') - e a'‖ ≤ ‖adjointAction (R a a') (e a') - e a'‖ :=
      mul_le_of_le_one_left (norm_nonneg _) hχ1
    have h5 : χ' * ‖e a' - e a‖ ≤ ‖e a' - e a‖ := mul_le_of_le_one_left (norm_nonneg _) hχ1
    linarith
  have n2 : ‖(χ' - χ) • e a‖ ≤ weightConstant / (F.blockSide : ℝ) ^ F.top * ‖e a‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    have h1 : |χ' - χ| ≤ weightConstant / (F.blockSide : ℝ) ^ F.top := by
      rw [abs_sub_comm]
      exact hshare
    exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  have e3 : 2 * Cs / (cellSideLength F : ℝ) = 2 * (Cs / (cellSideLength F : ℝ)) := by ring
  have n3 := norm_add_le (χ' • (adjointAction (R a a') (e a') - e a')) (χ' • (e a' - e a))
  have n4 := norm_add_le (χ' • (adjointAction (R a a') (e a') - e a') + χ' • (e a' - e a)) ((χ' - χ) • e a)
  rw [e3]
  linarith
theorem normalizedBump_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {z : F.Cell}
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) (s : F.Site 0) : normalizedBump S s z ≤ 81 := by
  have hm := inv_81_le_interiorBumpMean (S := S) hamb hodd he
  have hm0 : 0 < interiorBumpMean S z := by linarith
  rw [normalizedBump_eq, div_le_iff₀ hm0]
  have := interiorBump_le_one_at s z
  linarith
theorem enclosingCell_eq_of_normalizedBump_ne_zero (hodd : Odd F.blockSide) {s : F.Site 0} {y : F.Cell}
    (h : normalizedBump S s y ≠ 0) : enclosingCell s = y := by
  have h1 : interiorBump s y ≠ 0 := fun h0 => h (by rw [normalizedBump_eq, h0, zero_div])
  obtain ⟨t, ht, e⟩ := exists_centredCube_of_interiorBump_ne_zero hodd h1
  rw [e]
  exact enclosingCell_cellCentre_add hodd y t (by simpa using ht)
theorem norm_bumpTerm_sub_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {m : ℕ}
    (hreg : IsOrthantRegular S m) (hm : 32 ≤ m)
    {y : F.Cell} {R : Lattice4 → Lattice4 → UnitQuaternion} {Cs r : ℝ} (hF : IsPatchFrame S V y R Cs r)
    (hr1 : 1 ≤ r * cellSideLength F) (hC : 0 ≤ Cs) {s : F.Site 0} {i : Fin 4} (hs : s ∈ sitesOfCells S 0)
    (hs' : s + unitStep 0 i ∈ sitesOfCells S 0) (q : ℍ[ℝ]) :
    ‖normalizedBump S (s + unitStep 0 i) y • adjointAction (leadingTransport S V s (s + unitStep 0 i))
        (adjointAction (frameChange S V y (s + unitStep 0 i)) q) -
        normalizedBump S s y • adjointAction (frameChange S V y s) q‖ ≤
      (162 * Cs + 810 * cutoffBound) / (cellSideLength F : ℝ) * ‖q‖ := by
  classical
  have hL := hodd.pos
  have he := (closedOrthant_spec (S := S) hreg hm y).1
  have hN0 : (0 : ℝ) < cellSideLength F := by exact_mod_cast cellSideLength_pos (F := F) hL
  have hb := one_le_cutoffBound
  have hrhs : 0 ≤ (162 * Cs + 810 * cutoffBound) / (cellSideLength F : ℝ) * ‖q‖ :=
    mul_nonneg (div_nonneg (add_nonneg (mul_nonneg (by norm_num) hC) (by linarith)) hN0.le) (norm_nonneg _)
  by_cases h0 : normalizedBump S s y = 0 ∧ normalizedBump S (s + unitStep 0 i) y = 0
  · rw [h0.1, h0.2]
    simpa using hrhs
  have hstep : cellSupDist (enclosingCell (s + unitStep 0 i)) (enclosingCell s) ≤ 1 := by
    obtain ⟨y', _, h, hh, rfl⟩ := mem_sitesOfCells.1 hs
    have hst := cellSupDist_enclosingCell_step hodd (y := y') (h := h) (by simpa using hh) (i, true)
    have hv : stepDisplacement (F := F) 0 ((i, true) : PathStep) = unitStep 0 i := by simp [stepDisplacement]
    rw [hv] at hst
    rw [enclosingCell_cellCentre_add hodd y' h hh]
    exact hst
  have hnear : cellSupDist (enclosingCell s) y ≤ 1 ∧ cellSupDist (enclosingCell (s + unitStep 0 i)) y ≤ 1 := by
    by_cases h1 : normalizedBump S s y = 0
    · have h2 : normalizedBump S (s + unitStep 0 i) y ≠ 0 := fun h2 => h0 ⟨h1, h2⟩
      have h3 := enclosingCell_eq_of_normalizedBump_ne_zero hodd h2
      rw [h3] at hstep
      rw [cellSupDist_symm] at hstep
      rw [h3]
      exact ⟨hstep, by simp [cellSupDist]⟩
    · have h3 := enclosingCell_eq_of_normalizedBump_ne_zero hodd h1
      rw [h3] at hstep ⊢
      exact ⟨by simp [cellSupDist], hstep⟩
  have ha := patchChart_mem_patchDomain_of_near hamb hodd he hs (hnear.1.trans (by norm_num))
  have ha' := patchChart_mem_patchDomain_of_near hamb hodd he hs' (hnear.2.trans (by norm_num))
  obtain ⟨a, hadef⟩ : ∃ a, a = patchChart S y s := ⟨_, rfl⟩
  obtain ⟨a', hadef'⟩ : ∃ a', a' = patchChart S y (s + unitStep 0 i) := ⟨_, rfl⟩
  rw [← hadef] at ha
  rw [← hadef'] at ha'
  have hsa : patchSite S y a = s := by rw [hadef]; exact patchSite_patchChart he s
  have hsa' : patchSite S y a' = s + unitStep 0 i := by rw [hadef']; exact patchSite_patchChart he _
  have hor := patchChart_add_unitStep hamb hodd he (s := s) i (hadef ▸ ha)
  rw [← hadef, ← hadef'] at hor
  have hsup : supNorm (a' - a) = 1 := by
    rcases hor with ⟨_, h⟩ | ⟨_, h⟩
    · rw [h, add_sub_cancel_left]
      exact PatchDifferences.supNorm_basisVector i
    · rw [h, sub_add_cancel_left]
      exact supNorm_neg_basisVector i
  have hdist : (supNorm (a' - a) : ℝ) ≤ r * cellSideLength F := by
    rw [hsup]
    simpa using hr1
  have hlink := hF.leadingTransport_eq a ha a' ha' hdist
  have hnr := hF.norm_sub_one_le a ha a' ha' hdist
  rw [hsup] at hnr
  rw [hsa, hsa'] at hlink
  have hnr' : ‖((R a a' : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ Cs / (cellSideLength F : ℝ) := by
    simpa [div_eq_mul_inv] using hnr
  have hdcoord : ∀ k, |a k - a' k| ≤ 1 := by
    intro k
    have hu : |basisVector i k| ≤ 1 := by
      simp only [basisVector]
      by_cases hk : k = i
      · subst hk
        simp
      · simp [hk]
    rcases hor with ⟨_, h⟩ | ⟨_, h⟩
    · rw [h]
      simpa [abs_neg] using hu
    · rw [h]
      simpa using hu
  have hbump := normalizedBump_abs_sub_le (S := S) hamb hodd he (patchDomain_coord_bounds ha)
    (patchDomain_coord_bounds ha') hdcoord
  rw [hsa, hsa'] at hbump
  have hψ0 := normalizedBump_nonneg (S := S) hamb hodd he (s + unitStep 0 i)
  have hψ1 := normalizedBump_le (S := S) hamb hodd he (s + unitStep 0 i)
  obtain ⟨ψ, hψ⟩ : ∃ ψ, ψ = normalizedBump S s y := ⟨_, rfl⟩
  obtain ⟨ψ', hψ'⟩ : ∃ ψ', ψ' = normalizedBump S (s + unitStep 0 i) y := ⟨_, rfl⟩
  rw [← hψ, ← hψ'] at hbump
  rw [← hψ'] at hψ0 hψ1
  rw [← hψ, ← hψ', hlink]
  obtain ⟨f, hf⟩ : ∃ f, f = frameChange S V y s := ⟨_, rfl⟩
  obtain ⟨f', hf'⟩ : ∃ f', f' = frameChange S V y (s + unitStep 0 i) := ⟨_, rfl⟩
  rw [← hf, ← hf']
  have e1 : adjointAction (f * R a a' * f'⁻¹) (adjointAction f' q) = adjointAction f (adjointAction (R a a') q) := by
    rw [← adjointAction_mul, ← adjointAction_mul]
    congr 1
    group
  have e1' : ψ' • adjointAction f (adjointAction (R a a') q) - ψ • adjointAction f q =
      adjointAction f (ψ' • adjointAction (R a a') q - ψ • q) := by
    rw [adjointAction_sub, adjointAction_smul, adjointAction_smul]
  rw [e1, e1', norm_adjointAction]
  have e2 : ψ' • adjointAction (R a a') q - ψ • q = ψ' • (adjointAction (R a a') q - q) + (ψ' - ψ) • q := by
    simp only [smul_sub, sub_smul]
    abel
  rw [e2]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hψ0]
  have h1 := norm_adjointAction_sub_self_le (R a a') q
  have h2 : ‖adjointAction (R a a') q - q‖ ≤ 2 * (Cs / (cellSideLength F : ℝ)) * ‖q‖ :=
    h1.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  have h3 : ψ' * ‖adjointAction (R a a') q - q‖ ≤ 81 * (2 * (Cs / (cellSideLength F : ℝ)) * ‖q‖) :=
    mul_le_mul hψ1 h2 (norm_nonneg _) (by norm_num)
  have h4 : |ψ' - ψ| * ‖q‖ ≤ 810 * cutoffBound / (cellSideLength F : ℝ) * ‖q‖ := by
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [abs_sub_comm]
    exact hbump
  have e3 : (162 * Cs + 810 * cutoffBound) / (cellSideLength F : ℝ) * ‖q‖ =
      81 * (2 * (Cs / (cellSideLength F : ℝ)) * ‖q‖) + 810 * cutoffBound / (cellSideLength F : ℝ) * ‖q‖ := by
    ring
  rw [e3]
  linarith
end Terms
section Bond
variable {F : BlockFrame} {S : Finset F.Cell} {V : F.GaugeField F.top}
def bumpCorrection (S : Finset F.Cell) (V : F.GaugeField F.top) (E : F.Cell → Lattice4 → ℍ[ℝ]) (s : F.Site 0) :
    ℍ[ℝ] :=
  ∑ y ∈ S, normalizedBump S s y • adjointAction (frameChange S V y s) (frameCellMean S V y (gluedRemainder S V E))
theorem mem_cellBall_two_of_step (hodd : Odd F.blockSide) {s : F.Site 0} {i : Fin 4} (hs : s ∈ sitesOfCells S 0)
    {z : F.Cell} (hz : z ∈ S)
    (h : cellSupDist (enclosingCell (s + unitStep 0 i)) z ≤ 1 ∨ cellSupDist (enclosingCell s) z ≤ 1) :
    z ∈ cellBall S (enclosingCell s) 2 := by
  have hstep : cellSupDist (enclosingCell (s + unitStep 0 i)) (enclosingCell s) ≤ 1 := by
    obtain ⟨y', _, t, hh, rfl⟩ := mem_sitesOfCells.1 hs
    have hst := cellSupDist_enclosingCell_step hodd (y := y') (h := t) (by simpa using hh) (i, true)
    have hv : stepDisplacement (F := F) 0 ((i, true) : PathStep) = unitStep 0 i := by simp [stepDisplacement]
    rw [hv] at hst
    rw [enclosingCell_cellCentre_add hodd y' t hh]
    exact hst
  refine Finset.mem_filter.2 ⟨hz, ?_⟩
  rcases h with h | h
  · have h4 := cellSupDist_triangle (enclosingCell s) (enclosingCell (s + unitStep 0 i)) z
    have h5 : cellSupDist (enclosingCell s) (enclosingCell (s + unitStep 0 i)) =
        cellSupDist (enclosingCell (s + unitStep 0 i)) (enclosingCell s) :=
      cellSupDist_symm _ _
    omega
  · omega
theorem norm_covariantDiff_gaugeRemainder_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {m : ℕ}
    (hreg : IsOrthantRegular S m) (hm : 32 ≤ m)
    {ξ : F.Site 0 → ℍ[ℝ]} (hξ : CellMeanFree S V ξ) {E : F.Cell → Lattice4 → ℍ[ℝ]} {D : F.Cell → F.Site 0 → ℝ}
    {Rf : F.Cell → Lattice4 → Lattice4 → UnitQuaternion} {Cs r Ck : ℝ}
    (hR : ∀ z ∈ S, PatchRemainder S V z ξ (E z) (D z) Ck) (hF : ∀ z ∈ S, IsPatchFrame S V z (Rf z) Cs r)
    (hr1 : 1 ≤ r * cellSideLength F) (hC : 0 ≤ Cs) {s : F.Site 0} {i : Fin 4} (hs : s ∈ sitesOfCells S 0)
    (hs' : s + unitStep 0 i ∈ sitesOfCells S 0) :
    ‖covariantDiff (referenceFieldChain S V 0) (gaugeRemainder S V ξ) s i‖ ≤
      ∑ z ∈ cellBall S (enclosingCell s) 2, (2 * Cs / (cellSideLength F : ℝ) * remainderSize S z (E z) (s + unitStep 0 i) +
        weightConstant / (F.blockSide : ℝ) ^ F.top * remainderSize S z (E z) s + (D z s + D z (s + unitStep 0 i))) +
      ∑ y ∈ cellBall S (enclosingCell s) 1, (162 * Cs + 810 * cutoffBound) / (cellSideLength F : ℝ) *
        ‖frameCellMean S V y (gluedRemainder S V E)‖ := by
  classical
  obtain ⟨T, hT⟩ : ∃ T, T = leadingTransport S V s (s + unitStep 0 i) := ⟨_, rfl⟩
  have hsplit : covariantDiff (referenceFieldChain S V 0) (gaugeRemainder S V ξ) s i =
      (adjointAction T (gluedRemainder S V E (s + unitStep 0 i)) - gluedRemainder S V E s) -
        (adjointAction T (bumpCorrection S V E (s + unitStep 0 i)) - bumpCorrection S V E s) := by
    simp only [covariantDiff, referenceFieldChain_zero_apply, ← hT]
    rw [gaugeRemainder_eq hamb hodd hreg hm hξ hR hs, gaugeRemainder_eq hamb hodd hreg hm hξ hR hs',
      adjointAction_sub]
    simp only [bumpCorrection]
    abel
  have hA : adjointAction T (gluedRemainder S V E (s + unitStep 0 i)) - gluedRemainder S V E s =
      ∑ z ∈ S, (cellPartition S (s + unitStep 0 i) z • adjointAction T
          (adjointAction (frameChange S V z (s + unitStep 0 i)) (E z (patchChart S z (s + unitStep 0 i)))) -
        cellPartition S s z • adjointAction (frameChange S V z s) (E z (patchChart S z s))) := by
    simp only [gluedRemainder]
    rw [adjointAction_sum, Finset.sum_sub_distrib]
    simp only [adjointAction_smul]
  have hB : adjointAction T (bumpCorrection S V E (s + unitStep 0 i)) - bumpCorrection S V E s =
      ∑ y ∈ S, (normalizedBump S (s + unitStep 0 i) y • adjointAction T
          (adjointAction (frameChange S V y (s + unitStep 0 i)) (frameCellMean S V y (gluedRemainder S V E))) -
        normalizedBump S s y • adjointAction (frameChange S V y s) (frameCellMean S V y (gluedRemainder S V E))) := by
    simp only [bumpCorrection]
    rw [adjointAction_sum, Finset.sum_sub_distrib]
    simp only [adjointAction_smul]
  have hsubB : cellBall S (enclosingCell s) 2 ⊆ S := Finset.filter_subset _ _
  have hA2 : ‖adjointAction T (gluedRemainder S V E (s + unitStep 0 i)) - gluedRemainder S V E s‖ ≤
      ∑ z ∈ cellBall S (enclosingCell s) 2, (2 * Cs / (cellSideLength F : ℝ) * remainderSize S z (E z) (s + unitStep 0 i) +
        weightConstant / (F.blockSide : ℝ) ^ F.top * remainderSize S z (E z) s + (D z s + D z (s + unitStep 0 i))) := by
    rw [hA, ← Finset.sum_subset hsubB]
    · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun z hz => ?_)
      rw [hT]
      exact norm_gluedTerm_sub_le hamb hodd hreg hm (hsubB hz) (hF z (hsubB hz)) hr1 hC (hR z (hsubB hz)) hs hs'
    · intro z hz hn
      have h1 : cellPartition S s z = 0 := by
        by_contra h
        exact hn (mem_cellBall_two_of_step hodd (i := i) hs hz
          (Or.inr (cellSupDist_le_one_of_cellPartition_ne_zero hodd h)))
      have h2 : cellPartition S (s + unitStep 0 i) z = 0 := by
        by_contra h
        exact hn (mem_cellBall_two_of_step hodd hs hz (Or.inl (cellSupDist_le_one_of_cellPartition_ne_zero hodd h)))
      rw [h1, h2]
      simp
  have hsubB1 : cellBall S (enclosingCell s) 1 ⊆ S := Finset.filter_subset _ _
  have hB2 : ‖adjointAction T (bumpCorrection S V E (s + unitStep 0 i)) - bumpCorrection S V E s‖ ≤
      ∑ y ∈ cellBall S (enclosingCell s) 1, (162 * Cs + 810 * cutoffBound) / (cellSideLength F : ℝ) *
        ‖frameCellMean S V y (gluedRemainder S V E)‖ := by
    rw [hB, ← Finset.sum_subset hsubB1]
    · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y hy => ?_)
      rw [hT]
      exact norm_bumpTerm_sub_le hamb hodd hreg hm (hF y (hsubB1 hy)) hr1 hC hs hs' _
    · intro y hy hn
      have h1 : normalizedBump S s y = 0 := by
        by_contra h
        have h3 := enclosingCell_eq_of_normalizedBump_ne_zero hodd h
        exact hn (Finset.mem_filter.2 ⟨hy, by rw [h3]; simp [cellSupDist]⟩)
      have h2 : normalizedBump S (s + unitStep 0 i) y = 0 := by
        by_contra h
        have h3 := enclosingCell_eq_of_normalizedBump_ne_zero hodd h
        refine hn (Finset.mem_filter.2 ⟨hy, ?_⟩)
        have hstep : cellSupDist (enclosingCell (s + unitStep 0 i)) (enclosingCell s) ≤ 1 := by
          obtain ⟨y', _, t, hh, rfl⟩ := mem_sitesOfCells.1 hs
          have hst := cellSupDist_enclosingCell_step hodd (y := y') (h := t) (by simpa using hh) (i, true)
          have hv : stepDisplacement (F := F) 0 ((i, true) : PathStep) = unitStep 0 i := by
            simp [stepDisplacement]
          rw [hv] at hst
          rw [enclosingCell_cellCentre_add hodd y' t hh]
          exact hst
        rw [h3, cellSupDist_symm] at hstep
        exact hstep
      rw [h1, h2]
      simp
  rw [hsplit]
  exact (norm_sub_le _ _).trans (add_le_add hA2 hB2)
end Bond
section Means
variable {F : BlockFrame} {S : Finset F.Cell} {V : F.GaugeField F.top}
theorem cellMeanFree_gaugeMap (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {m : ℕ}
    (hreg : IsOrthantRegular S m) (hm : 32 ≤ m)
    (R : F.GaugeField 0) (u : F.Site 0 → Fin 4 → ℍ[ℝ]) : CellMeanFree S V (gaugeMap S V R u) := by
  classical
  intro y hy
  have he := (closedOrthant_spec (S := S) hreg hm y).1
  have hDm := inv_81_le_interiorBumpMean (S := S) (z := y) hamb hodd he
  have hDpos : 0 < interiorBumpMean S y := by linarith
  obtain ⟨g, hg⟩ : ∃ g, g = gluedPotential S V R u := ⟨_, rfl⟩
  have hpoint : ∀ x ∈ cellOffsets F,
      adjointAction (frameChange S V y (patchSite S y x))⁻¹ (gaugeMap S V R u (patchSite S y x)) =
        adjointAction (frameChange S V y (patchSite S y x))⁻¹ (g (patchSite S y x)) -
          (interiorBump (patchSite S y x) y / interiorBumpMean S y) • frameCellMean S V y g := by
    intro x hx
    have hxi := fun i => Finset.mem_Ico.1 (Fintype.mem_piFinset.1 hx i)
    obtain ⟨h0, h1⟩ := cellSideLength_half (F := F) hodd
    have hcube : (fun i => closedOrthant S y i * (x i - (cellSideLength F - 1) / 2)) ∈
        centredCube (F.blockSide ^ F.top) := by
      rw [mem_centredCube_iff]
      intro i
      have := hxi i
      rcases he i with hs | hs <;> rw [hs] <;> constructor <;> omega
    have hcell : enclosingCell (patchSite S y x) = y := enclosingCell_cellCentre_add hodd y _ (by simpa using hcube)
    have hz : ∀ y' ∈ S, y' ≠ y → normalizedBump S (patchSite S y x) y' •
        adjointAction (frameChange S V y' (patchSite S y x)) (frameCellMean S V y' g) = 0 := by
      intro y' _ hne
      have h2 : normalizedBump S (patchSite S y x) y' = 0 := by
        by_contra h
        exact hne ((enclosingCell_eq_of_normalizedBump_ne_zero hodd h).symm.trans hcell)
      rw [h2, zero_smul]
    simp only [gaugeMap]
    rw [← hg, Finset.sum_eq_single_of_mem y hy hz, adjointAction_sub, adjointAction_smul]
    have e : adjointAction (frameChange S V y (patchSite S y x))⁻¹
        (adjointAction (frameChange S V y (patchSite S y x)) (frameCellMean S V y g)) = frameCellMean S V y g := by
      rw [← adjointAction_mul, inv_mul_cancel, adjointAction_one]
    rw [e]
    rfl
  change (1 / (cellSideLength F : ℝ) ^ 4) • ∑ x ∈ cellOffsets F,
    adjointAction (frameChange S V y (patchSite S y x))⁻¹ (gaugeMap S V R u (patchSite S y x)) = 0
  rw [Finset.sum_congr rfl hpoint, Finset.sum_sub_distrib, smul_sub, ← Finset.sum_smul, smul_smul]
  have hone : (1 / (cellSideLength F : ℝ) ^ 4) *
      ∑ x ∈ cellOffsets F, interiorBump (patchSite S y x) y / interiorBumpMean S y = 1 := by
    rw [← Finset.sum_div, ← mul_div_assoc]
    exact div_self hDpos.ne'
  rw [hone, one_smul]
  have : (1 / (cellSideLength F : ℝ) ^ 4) • ∑ x ∈ cellOffsets F,
      adjointAction (frameChange S V y (patchSite S y x))⁻¹ (g (patchSite S y x)) = frameCellMean S V y g := rfl
  rw [this]
  exact sub_self _
theorem sum_cellOffsets_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {y : F.Cell} (hy : y ∈ S)
    (he : ∀ i, closedOrthant S y i = 1 ∨ closedOrthant S y i = -1) (g : F.Site 0 → ℝ) (hg : ∀ t, 0 ≤ g t) :
    ∑ x ∈ cellOffsets F, g (patchSite S y x) ≤ ∑ t ∈ cellSites S y, g t := by
  classical
  have hL := hodd.pos
  obtain ⟨h0, h1⟩ := cellSideLength_half (F := F) hodd
  have hinj : Set.InjOn (patchSite S y) (cellOffsets F : Set Lattice4) := fun a ha b hb h =>
    patchSite_injOn hamb hodd he (mem_patchDomain_of_mem_cellOffsets hy hL ha)
      (mem_patchDomain_of_mem_cellOffsets hy hL hb) h
  rw [← Finset.sum_image (f := g) hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => hg _
  intro t ht
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ht
  have hxi := fun i => Finset.mem_Ico.1 (Fintype.mem_piFinset.1 hx i)
  have hcube : (fun i => closedOrthant S y i * (x i - (cellSideLength F - 1) / 2)) ∈
      centredCube (F.blockSide ^ F.top) := by
    rw [mem_centredCube_iff]
    intro i
    have := hxi i
    rcases he i with hs | hs <;> rw [hs] <;> constructor <;> omega
  exact Finset.mem_filter.2 ⟨mem_sitesOfCells.2 ⟨y, hy, _, by simpa using hcube, rfl⟩,
    enclosingCell_cellCentre_add hodd y _ (by simpa using hcube)⟩
end Means
section Norms
variable {F : BlockFrame} {S : Finset F.Cell} {V : F.GaugeField F.top}
variable {Md Lf Sr : (F.Site 0 → ℝ) → F.Cell → ℝ} {σ : F.Cell → ℝ} {K : ℝ}
theorem patchCubicKernel_nonneg {z : F.Cell} {f : F.Site 0 → ℝ} (hf : ∀ t, 0 ≤ f t) (t : F.Site 0) :
    0 ≤ patchCubicKernel S z f t := by apply _root_.YangMills.Construction.PatchPotentials.patchCubicKernel_nonneg <;> assumption
theorem remainder_arith {Ck N W a b c sz : ℝ} (hCk : 0 ≤ Ck) (hK : 0 ≤ K) (hN : 0 < N) (hW : 0 ≤ W)
    (hc0 : 0 ≤ c) (hsz : 0 ≤ sz)
    (ha : a ≤ K * (K * N * W)) (hb : b ≤ K * N * (K * sz)) (hm : sz * c ≤ K ^ 3 * W) :
    Ck * a + Ck * c * b ≤ Ck * (K ^ 2 + K ^ 5) * N * W := by
  have h1 : Ck * a ≤ Ck * (K * (K * N * W)) := mul_le_mul_of_nonneg_left ha hCk
  have h2 : Ck * c * b ≤ Ck * c * (K * N * (K * sz)) := mul_le_mul_of_nonneg_left hb (mul_nonneg hCk hc0)
  have h3 : Ck * K ^ 2 * N * (sz * c) ≤ Ck * K ^ 2 * N * (K ^ 3 * W) :=
    mul_le_mul_of_nonneg_left hm (mul_nonneg (mul_nonneg hCk (sq_nonneg K)) hN.le)
  have e2 : Ck * (K ^ 2 + K ^ 5) * N * W = Ck * (K * (K * N * W)) + Ck * K ^ 2 * N * (K ^ 3 * W) := by ring
  rw [e2]
  linarith
theorem remainderSize_bound (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {m : ℕ}
    (hreg : IsOrthantRegular S m) (hm : 32 ≤ m)
    (hN : CellNormFamily S Md Lf Sr σ K) (hK : 0 ≤ K) {ξ : F.Site 0 → ℍ[ℝ]} {z : F.Cell} {e : Lattice4 → ℍ[ℝ]}
    {Dl : F.Site 0 → ℝ} {Ck : ℝ} (hz : z ∈ S) (hCk : 0 ≤ Ck) (hR : PatchRemainder S V z ξ e Dl Ck) {y : F.Cell}
    (hd : cellSupDist y z ≤ 22) :
    Md (remainderSize S z e) y ≤ Ck * (K ^ 2 + K ^ 5) * (cellSideLength F : ℝ) * ∑ x ∈ cellBall S z 20, Md Dl x := by
  classical
  have hL := hodd.pos
  have he := (closedOrthant_spec (S := S) hreg hm z).1
  have hNz : (0 : ℝ) < cellSideLength F := by exact_mod_cast cellSideLength_pos (F := F) hL
  obtain ⟨N, hNd⟩ : ∃ N : ℝ, N = (cellSideLength F : ℝ) := ⟨_, rfl⟩
  have hN0 : 0 < N := hNd ▸ hNz
  obtain ⟨W, hWd⟩ : ∃ W, W = ∑ x ∈ cellBall S z 20, Md Dl x := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := hWd ▸ Finset.sum_nonneg fun _ _ => hN.isSeminorm_base.nonneg _ _
  rw [← hWd, ← hNd]
  obtain ⟨T, hTd⟩ : ∃ T, T = patchCubicKernel S z Dl := ⟨_, rfl⟩
  have hT0 : ∀ t, 0 ≤ T t := fun t => hTd ▸ patchCubicKernel_nonneg hR.stepBound_nonneg t
  have hDon : restrictToPatch S z Dl = Dl := by
    funext t
    by_cases ht : t ∈ patchSiteSet S z
    · exact restrictToPatch_of_mem ht
    · rw [restrictToPatch_of_not_mem ht, hR.stepBound_eq_zero t ht]
  have hMT : ∀ y, Md T y ≤ K * (K * N * W) := by
    intro y
    refine (hN.base_le_target T y).trans ?_
    rw [hTd]
    refine (hN.kernel_le z hz Dl y).trans (mul_le_mul_of_nonneg_left ?_ hK)
    rw [hDon, hWd, Finset.mul_sum, hNd]
    exact Finset.sum_le_sum fun x _ => hN.source_le _ x
  obtain ⟨c, hcd⟩ : ∃ c, c = (1 / N ^ 4) * ∑ x ∈ cellOffsets F, T (patchSite S z x) := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := hcd ▸ mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => hT0 _)
  have hpt : ∀ x ∈ cellSites S y, |remainderSize S z e x| ≤ |Ck * T x + (Ck * c) * 1| := by
    intro x _
    have hr0 : 0 ≤ Ck * T x + (Ck * c) * 1 :=
      add_nonneg (mul_nonneg hCk (hT0 x)) (by simpa using mul_nonneg hCk hc0)
    have hs0 : 0 ≤ remainderSize S z e x := restrictToPatch_nonneg (fun _ => norm_nonneg _) x
    rw [abs_of_nonneg hs0, abs_of_nonneg hr0]
    by_cases hx : x ∈ patchSiteSet S z
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
      simp only [remainderSize]
      rw [restrictToPatch_of_mem hx, patchChart_patchSite hamb hodd he (patchDomain_coord_bounds ha), mul_one, hTd,
        hcd, hTd, hNd]
      exact hR.norm_le a ha
    · simp only [remainderSize]
      rw [restrictToPatch_of_not_mem hx]
      exact hr0
  have hstep : Md (remainderSize S z e) y ≤ Ck * Md T y + Ck * c * Md (fun _ => 1) y := by
    refine (hN.isSeminorm_base.mono_abs _ (fun x => Ck * T x + (Ck * c) * 1) y hpt).trans
      ((hN.isSeminorm_base.add_le _ _ y).trans ?_)
    rw [hN.isSeminorm_base.smul, hN.isSeminorm_base.smul (Ck * c) (fun _ => 1), abs_of_nonneg hCk,
      abs_of_nonneg (mul_nonneg hCk hc0)]
  have hsz : 0 < σ z := hN.scale_pos z
  have hone : Md (fun _ => 1) y ≤ K * N * (K * σ z) := by
    refine (hN.base_le_target _ y).trans ((hN.const_le y).trans ?_)
    rw [← hNd]
    exact mul_le_mul_of_nonneg_left (hN.scale_le_of_near y z hd) (mul_nonneg hK hN0.le)
  have hmean : σ z * c ≤ K ^ 3 * W := by
    have h1 := hN.mean_le T z
    have h2 : ∑ x ∈ cellOffsets F, T (patchSite S z x) ≤ ∑ x ∈ cellSites S z, |T x| := by
      refine (sum_cellOffsets_le hamb hodd hz he T hT0).trans (le_of_eq ?_)
      exact Finset.sum_congr rfl fun x _ => (abs_of_nonneg (hT0 x)).symm
    rw [← hNd] at h1
    have h3 := hMT z
    rw [hcd]
    calc σ z * (1 / N ^ 4 * ∑ x ∈ cellOffsets F, T (patchSite S z x))
        = (1 / N ^ 4) * (σ z * ∑ x ∈ cellOffsets F, T (patchSite S z x)) := by ring
      _ ≤ (1 / N ^ 4) * (K * N ^ 3 * Md T z) :=
          mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left h2 hsz.le).trans h1) (by positivity)
      _ ≤ (1 / N ^ 4) * (K * N ^ 3 * (K * (K * N * W))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (by positivity)) (by positivity)
      _ = _ := by field_simp
  exact hstep.trans (remainder_arith hCk hK hN0 hW0 hc0 hsz.le (hMT y) hone hmean)
theorem stepBound_le_sum_cellBall (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {m : ℕ}
    (hreg : IsOrthantRegular S m) (hm : 32 ≤ m)
    (hN : CellNormFamily S Md Lf Sr σ K) {ξ : F.Site 0 → ℍ[ℝ]} {z : F.Cell} {e : Lattice4 → ℍ[ℝ]}
    {Dl : F.Site 0 → ℝ} {Ck : ℝ} (hR : PatchRemainder S V z ξ e Dl Ck) {y : F.Cell} (hy : y ∈ S) :
    Md Dl y ≤ ∑ x ∈ cellBall S z 20, Md Dl x := by
  classical
  by_cases hb : y ∈ cellBall S z 20
  · exact Finset.single_le_sum (f := fun x => Md Dl x) (fun _ _ => hN.isSeminorm_base.nonneg _ _) hb
  · have h0 : Md Dl y = 0 := cellSeminorm_eq_zero_of_vanish hN.isSeminorm_base fun x hx => by
      refine hR.stepBound_eq_zero x fun hxp => hb ?_
      obtain ⟨b, hb', rfl⟩ := Finset.mem_image.1 hxp
      have h1 := (enclosingCell_patchSite hamb hodd hreg hm hb').2
      rw [(Finset.mem_filter.1 hx).2] at h1
      exact Finset.mem_filter.2 ⟨hy, by rw [cellSupDist_symm]; exact h1⟩
    rw [h0]
    exact Finset.sum_nonneg fun _ _ => hN.isSeminorm_base.nonneg _ _
theorem frameCellMean_gluedRemainder_bound (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {m : ℕ}
    (hreg : IsOrthantRegular S m) (hm : 32 ≤ m)
    (hN : CellNormFamily S Md Lf Sr σ K) (hK : 0 ≤ K) {E : F.Cell → Lattice4 → ℍ[ℝ]} {y : F.Cell} (hy : y ∈ S) :
    σ y * ‖frameCellMean S V y (gluedRemainder S V E)‖ ≤
      K / (cellSideLength F : ℝ) * ∑ z ∈ cellBall S y 1, Md (remainderSize S z (E z)) y := by
  classical
  have hL := hodd.pos
  have hey := (closedOrthant_spec (S := S) hreg hm y).1
  have hNz : (0 : ℝ) < cellSideLength F := by exact_mod_cast cellSideLength_pos (F := F) hL
  have hRs0 : ∀ z t, 0 ≤ remainderSize S z (E z) t := fun z t => restrictToPatch_nonneg (fun _ => norm_nonneg _) t
  obtain ⟨g, hgd⟩ : ∃ g : F.Site 0 → ℝ, g = fun t => ∑ z ∈ cellBall S y 1, remainderSize S z (E z) t :=
    ⟨_, rfl⟩
  have hg0 : ∀ t, 0 ≤ g t := fun t => hgd ▸ Finset.sum_nonneg fun z _ => hRs0 z t
  have hpt : ∀ t ∈ cellSites S y, ‖gluedRemainder S V E t‖ ≤ g t := by
    intro t ht
    obtain ⟨ht1, ht2⟩ := Finset.mem_filter.1 ht
    simp only [gluedRemainder, hgd]
    have hsub : cellBall S y 1 ⊆ S := Finset.filter_subset _ _
    have hzero : ∀ z ∈ S, z ∉ cellBall S y 1 → cellPartition S t z •
        adjointAction (frameChange S V z t) (E z (patchChart S z t)) = 0 := by
      intro z hz hn
      have h0 : cellPartition S t z = 0 := by
        by_contra h
        have h1 := cellSupDist_le_one_of_cellPartition_ne_zero hodd h
        rw [ht2] at h1
        exact hn (Finset.mem_filter.2 ⟨hz, h1⟩)
      rw [h0, zero_smul]
    rw [← Finset.sum_subset hsub hzero]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun z hz => ?_)
    have hzS := hsub hz
    by_cases h0 : cellPartition S t z = 0
    · rw [h0, zero_smul, norm_zero]
      exact hRs0 z t
    · have hez := (closedOrthant_spec (S := S) hreg hm z).1
      have hd := cellSupDist_le_one_of_cellPartition_ne_zero hodd h0
      have ha := patchChart_mem_patchDomain_of_near hamb hodd hez ht1 (hd.trans (by norm_num))
      have htp : t ∈ patchSiteSet S z := by
        have := Finset.mem_image_of_mem (patchSite S z) ha
        rwa [patchSite_patchChart hez] at this
      simp only [remainderSize]
      rw [restrictToPatch_of_mem htp, norm_smul, norm_adjointAction, Real.norm_eq_abs,
        abs_of_nonneg (cellPartition_nonneg _ _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (cellPartition_le_one _ hzS)
  have hcell : ∀ x ∈ cellOffsets F, patchSite S y x ∈ cellSites S y := by
    intro x hx
    have hxi := fun i => Finset.mem_Ico.1 (Fintype.mem_piFinset.1 hx i)
    obtain ⟨h0, h1⟩ := cellSideLength_half (F := F) hodd
    have hcube : (fun i => closedOrthant S y i * (x i - (cellSideLength F - 1) / 2)) ∈
        centredCube (F.blockSide ^ F.top) := by
      rw [mem_centredCube_iff]
      intro i
      have := hxi i
      rcases hey i with hs | hs <;> rw [hs] <;> constructor <;> omega
    exact Finset.mem_filter.2 ⟨mem_sitesOfCells.2 ⟨y, hy, _, by simpa using hcube, rfl⟩,
      enclosingCell_cellCentre_add hodd y _ (by simpa using hcube)⟩
  have h1 : ‖frameCellMean S V y (gluedRemainder S V E)‖ ≤
      (1 / (cellSideLength F : ℝ) ^ 4) * ∑ t ∈ cellSites S y, g t := by
    simp only [frameCellMean]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun x hx => ?_).trans (sum_cellOffsets_le hamb hodd hy hey g hg0)
    rw [norm_adjointAction]
    exact hpt _ (hcell x hx)
  have hsy := hN.scale_pos y
  have h2 : σ y * ∑ t ∈ cellSites S y, g t ≤
      K * (cellSideLength F : ℝ) ^ 3 * ∑ z ∈ cellBall S y 1, Md (remainderSize S z (E z)) y := by
    rw [hgd]
    simp only
    rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun z _ => ?_
    have h3 := hN.mean_le (remainderSize S z (E z)) y
    refine le_trans (le_of_eq ?_) h3
    congr 1
    exact Finset.sum_congr rfl fun t _ => (abs_of_nonneg (hRs0 z t)).symm
  calc σ y * ‖frameCellMean S V y (gluedRemainder S V E)‖
      ≤ σ y * ((1 / (cellSideLength F : ℝ) ^ 4) * ∑ t ∈ cellSites S y, g t) := mul_le_mul_of_nonneg_left h1 hsy.le
    _ = (1 / (cellSideLength F : ℝ) ^ 4) * (σ y * ∑ t ∈ cellSites S y, g t) := by ring
    _ ≤ (1 / (cellSideLength F : ℝ) ^ 4) *
        (K * (cellSideLength F : ℝ) ^ 3 * ∑ z ∈ cellBall S y 1, Md (remainderSize S z (E z)) y) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by field_simp
end Norms
section Form
variable {F : BlockFrame} {S : Finset F.Cell} {V : F.GaugeField F.top}
variable {Md Lf Sr : (F.Site 0 → ℝ) → F.Cell → ℝ} {σ : F.Cell → ℝ} {K : ℝ}
theorem card_cellBall_one (hamb : IsAdmissibleAmbient F) (z : F.Cell) : ((cellBall S z 1).card : ℝ) ≤ 81 := by
  have := card_le_of_cellSupDist_le hamb z 1 (cellBall S z 1) fun y hy => (Finset.mem_filter.1 hy).2
  have h2 : ((cellBall S z 1).card : ℝ) ≤ (((2 * 1 + 1) ^ 4 : ℕ) : ℝ) := by exact_mod_cast this
  norm_num at h2 ⊢
  exact h2
theorem card_cellBall_two (hamb : IsAdmissibleAmbient F) (z : F.Cell) : ((cellBall S z 2).card : ℝ) ≤ 625 := by
  have := card_le_of_cellSupDist_le hamb z 2 (cellBall S z 2) fun y hy => (Finset.mem_filter.1 hy).2
  have h2 : ((cellBall S z 2).card : ℝ) ≤ (((2 * 2 + 1) ^ 4 : ℕ) : ℝ) := by exact_mod_cast this
  norm_num at h2 ⊢
  exact h2
theorem base_shift_unitStep_le (hN : CellNormFamily S Md Lf Sr σ K) (i : Fin 4) {f : F.Site 0 → ℝ}
    (hf : ∀ x, x ∉ sitesOfCells S 0 → f x = 0) (z : F.Cell) :
    Md (fun x => f (x + unitStep 0 i)) z ≤ K * ∑ y ∈ cellBall S z 1, Md f y := by
  have hv : stepDisplacement (F := F) 0 ((i, true) : PathStep) = unitStep 0 i := by simp [stepDisplacement]
  have := hN.base_shift_le (i, true) f z hf
  rwa [hv] at this
theorem sum_cellBall_one_le (hamb : IsAdmissibleAmbient F) {g : F.Cell → ℝ} {B : ℝ} (hB : 0 ≤ B) (z₀ : F.Cell)
    (hg : ∀ y ∈ cellBall S z₀ 1, g y ≤ B) : ∑ y ∈ cellBall S z₀ 1, g y ≤ 81 * B := by
  calc ∑ y ∈ cellBall S z₀ 1, g y ≤ ∑ _y ∈ cellBall S z₀ 1, B := Finset.sum_le_sum hg
    _ = ((cellBall S z₀ 1).card : ℝ) * B := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (card_cellBall_one hamb z₀) hB
theorem term_arith {ca cb e0 e1 d0 d1 Q W : ℝ} (hca : 0 ≤ ca) (hcb : 0 ≤ cb) (hK : 0 ≤ K) (hW : 0 ≤ W)
    (he0 : e0 ≤ Q) (he1 : e1 ≤ K * (81 * Q)) (hd0 : d0 ≤ W) (hd1 : d1 ≤ K * (81 * W)) :
    ca * e1 + cb * e0 + (d0 + d1) ≤ ca * (K * (81 * Q)) + cb * Q + (W + K * (81 * W)) := by
  have h1 := mul_le_mul_of_nonneg_left he1 hca
  have h2 := mul_le_mul_of_nonneg_left he0 hcb
  linarith
theorem formNormOn_gaugeRemainder_bound (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {m : ℕ}
    (hreg : IsOrthantRegular S m) (hm : 32 ≤ m)
    (hN : CellNormFamily S Md Lf Sr σ K) (hK : 0 ≤ K) {ξ : F.Site 0 → ℍ[ℝ]} (hξ : CellMeanFree S V ξ)
    {E : F.Cell → Lattice4 → ℍ[ℝ]} {D : F.Cell → F.Site 0 → ℝ}
    {Rf : F.Cell → Lattice4 → Lattice4 → UnitQuaternion} {Cs r Ck : ℝ}
    (hR : ∀ z ∈ S, PatchRemainder S V z ξ (E z) (D z) Ck) (hF : ∀ z ∈ S, IsPatchFrame S V z (Rf z) Cs r)
    (hr1 : 1 ≤ r * cellSideLength F) (hC : 0 ≤ Cs) (hC1 : Cs ≤ 1) (hCk : 0 ≤ Ck) {z₀ : F.Cell} (hz₀ : z₀ ∈ S) :
    Md (formNormOn S (covariantDiff (referenceFieldChain S V 0) (gaugeRemainder S V ξ))) z₀ ≤
      (4 * (2 * (81 * K) * (Ck * (K ^ 2 + K ^ 5)) + weightConstant * (Ck * (K ^ 2 + K ^ 5)) + (1 + 81 * K) +
          81 * K ^ 3 * (162 + 810 * cutoffBound) * (Ck * (K ^ 2 + K ^ 5)))) *
        ∑ z ∈ cellBall S z₀ 2, ∑ x ∈ cellBall S z 20, Md (D z) x := by
  classical
  have hL := hodd.pos
  have hNz : (0 : ℝ) < cellSideLength F := by exact_mod_cast cellSideLength_pos (F := F) hL
  have hNL : (F.blockSide : ℝ) ^ F.top = (cellSideLength F : ℝ) := by simp [cellSideLength]
  obtain ⟨N, hNd⟩ : ∃ N : ℝ, N = (cellSideLength F : ℝ) := ⟨_, rfl⟩
  have hN0 : 0 < N := hNd ▸ hNz
  have hb := one_le_cutoffBound
  have hCb : 0 ≤ weightConstant := by
    unfold weightConstant
    positivity
  obtain ⟨C2, hC2⟩ : ∃ C2, C2 = Ck * (K ^ 2 + K ^ 5) := ⟨_, rfl⟩
  have hC20 : 0 ≤ C2 := hC2 ▸ mul_nonneg hCk (add_nonneg (sq_nonneg K) (pow_nonneg hK 5))
  obtain ⟨ca, hcad⟩ : ∃ ca, ca = 2 * Cs / N := ⟨_, rfl⟩
  obtain ⟨cb, hcbd⟩ : ∃ cb, cb = weightConstant / N := ⟨_, rfl⟩
  obtain ⟨cc, hccd⟩ : ∃ cc, cc = (162 * Cs + 810 * cutoffBound) / N := ⟨_, rfl⟩
  have hca0 : 0 ≤ ca := hcad ▸ div_nonneg (mul_nonneg (by norm_num) hC) hN0.le
  have hcb0 : 0 ≤ cb := hcbd ▸ div_nonneg hCb hN0.le
  have hcc0 : 0 ≤ cc := hccd ▸ div_nonneg (add_nonneg (mul_nonneg (by norm_num) hC) (by linarith)) hN0.le
  obtain ⟨W, hWd⟩ : ∃ W : F.Cell → ℝ, W = fun z => ∑ x ∈ cellBall S z 20, Md (D z) x := ⟨_, rfl⟩
  have hW0 : ∀ z, 0 ≤ W z := fun z => hWd ▸ Finset.sum_nonneg fun _ _ => hN.isSeminorm_base.nonneg _ _
  obtain ⟨Ez, hEz⟩ : ∃ Ez : F.Cell → F.Site 0 → ℝ, Ez = fun z => remainderSize S z (E z) := ⟨_, rfl⟩
  have hEz0 : ∀ z t, 0 ≤ Ez z t := fun z t => hEz ▸ restrictToPatch_nonneg (fun _ => norm_nonneg _) t
  have hS2 : cellBall S z₀ 2 ⊆ S := Finset.filter_subset _ _
  have hS1 : cellBall S z₀ 1 ⊆ S := Finset.filter_subset _ _
  have hP : ∀ z : F.Cell, patchSiteSet S z ⊆ sitesOfCells S 0 := fun z t ht => by
    obtain ⟨b, hb', rfl⟩ := Finset.mem_image.1 ht
    exact patchSite_mem_sitesOfCells hamb hodd hreg hm hb'
  have hEoff : ∀ z x, x ∉ sitesOfCells S 0 → Ez z x = 0 := fun z x hx => by
    rw [hEz]
    exact restrictToPatch_of_not_mem fun h => hx (hP z h)
  have hDoff : ∀ z ∈ S, ∀ x, x ∉ sitesOfCells S 0 → D z x = 0 := fun z hz x hx =>
    (hR z hz).stepBound_eq_zero x fun h => hx (hP z h)
  obtain ⟨Mc, hMc⟩ : ∃ Mc, Mc = ∑ y ∈ cellBall S z₀ 1, cc * ‖frameCellMean S V y (gluedRemainder S V E)‖ :=
    ⟨_, rfl⟩
  have hMc0 : 0 ≤ Mc := hMc ▸ Finset.sum_nonneg fun _ _ => mul_nonneg hcc0 (norm_nonneg _)
  obtain ⟨Pf, hPf⟩ : ∃ Pf : Fin 4 → F.Site 0 → ℝ, Pf = fun i x =>
      (∑ z ∈ cellBall S z₀ 2, (ca * Ez z (x + unitStep 0 i) + cb * Ez z x + (D z x + D z (x + unitStep 0 i)))) +
        Mc * 1 :=
    ⟨_, rfl⟩
  have hDnn : ∀ z ∈ cellBall S z₀ 2, ∀ t, 0 ≤ D z t := fun z hz t => (hR z (hS2 hz)).stepBound_nonneg t
  have hPf0 : ∀ i x, 0 ≤ Pf i x := by
    intro i x
    rw [hPf]
    refine add_nonneg (Finset.sum_nonneg fun z hz => ?_) (by simpa using hMc0)
    exact add_nonneg (add_nonneg (mul_nonneg hca0 (hEz0 _ _)) (mul_nonneg hcb0 (hEz0 _ _)))
      (add_nonneg (hDnn z hz _) (hDnn z hz _))
  have hpt : ∀ x ∈ cellSites S z₀,
      |formNormOn S (covariantDiff (referenceFieldChain S V 0) (gaugeRemainder S V ξ)) x| ≤ |∑ i, Pf i x| := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
    rw [abs_of_nonneg (formNormOn_nonneg _ _), abs_of_nonneg (Finset.sum_nonneg fun i _ => hPf0 i x)]
    refine Finset.sum_le_sum fun i _ => ?_
    split_ifs with hb'
    · have hs' : x + unitStep 0 i ∈ sitesOfCells S 0 := (Finset.mem_filter.1 hb').2
      have h1 := norm_covariantDiff_gaugeRemainder_le hamb hodd hreg hm hξ hR hF hr1 hC hx1 hs'
      rw [hx2, hNL, ← hNd, ← hcad, ← hcbd, ← hccd, ← hMc] at h1
      rw [hPf, mul_one]
      simpa only [hEz] using h1
    · exact hPf0 i x
  have hQ : ∀ z ∈ cellBall S z₀ 2, ∀ y ∈ cellBall S z₀ 1, Md (Ez z) y ≤ C2 * N * W z := by
    intro z hz y hy
    have hzS := hS2 hz
    have hd1 := (Finset.mem_filter.1 hy).2
    have hd2 := (Finset.mem_filter.1 hz).2
    have hd : cellSupDist y z ≤ 22 := by
      have h4 := cellSupDist_triangle y z₀ z
      rw [cellSupDist_symm y z₀] at h4
      omega
    have := remainderSize_bound hamb hodd hreg hm hN hK hzS hCk (hR z hzS) hd
    rw [hEz, hWd, hC2, hNd]
    exact this
  have hz₀1 : z₀ ∈ cellBall S z₀ 1 := Finset.mem_filter.2 ⟨hz₀, by simp [cellSupDist]⟩
  have hterm : ∀ i, ∀ z ∈ cellBall S z₀ 2,
      Md (fun x => ca * Ez z (x + unitStep 0 i) + cb * Ez z x + (D z x + D z (x + unitStep 0 i))) z₀ ≤
        ca * (K * (81 * (C2 * N * W z))) + cb * (C2 * N * W z) + (W z + K * (81 * W z)) := by
    intro i z hz
    have hzS := hS2 hz
    have hWz := hW0 z
    have hQ0 : 0 ≤ C2 * N * W z := mul_nonneg (mul_nonneg hC20 hN0.le) hWz
    have e0 := hQ z hz z₀ hz₀1
    have e1 : Md (fun x => Ez z (x + unitStep 0 i)) z₀ ≤ K * (81 * (C2 * N * W z)) :=
      (base_shift_unitStep_le hN i (hEoff z) z₀).trans (mul_le_mul_of_nonneg_left
        (sum_cellBall_one_le hamb hQ0 z₀ fun y hy => hQ z hz y hy) hK)
    have hDy : ∀ y ∈ S, Md (D z) y ≤ W z := fun y hy => by
      rw [hWd]
      exact stepBound_le_sum_cellBall hamb hodd hreg hm hN (hR z hzS) hy
    have d0 := hDy z₀ hz₀
    have d1 : Md (fun x => D z (x + unitStep 0 i)) z₀ ≤ K * (81 * W z) :=
      (base_shift_unitStep_le hN i (hDoff z hzS) z₀).trans (mul_le_mul_of_nonneg_left
        (sum_cellBall_one_le hamb hWz z₀ fun y hy => hDy y (hS1 hy)) hK)
    have h1 := hN.isSeminorm_base.add_le (fun x => ca * Ez z (x + unitStep 0 i) + cb * Ez z x)
      (fun x => D z x + D z (x + unitStep 0 i)) z₀
    have h2 := hN.isSeminorm_base.add_le (fun x => ca * Ez z (x + unitStep 0 i)) (fun x => cb * Ez z x) z₀
    have h3 := hN.isSeminorm_base.add_le (fun x => D z x) (fun x => D z (x + unitStep 0 i)) z₀
    have h4 := hN.isSeminorm_base.smul ca (fun x => Ez z (x + unitStep 0 i)) z₀
    have h5 := hN.isSeminorm_base.smul cb (fun x => Ez z x) z₀
    rw [abs_of_nonneg hca0] at h4
    rw [abs_of_nonneg hcb0] at h5
    have h6 := term_arith (K := K) hca0 hcb0 hK hWz e0 e1 d0 d1
    have h7 : Md (fun x => D z x) z₀ = Md (D z) z₀ := rfl
    have h8 : Md (fun x => Ez z x) z₀ = Md (Ez z) z₀ := rfl
    rw [h7] at h3
    rw [h8] at h5
    linarith
  have hone : Md (fun _ => 1) z₀ ≤ K * N * σ z₀ := by
    refine (hN.base_le_target _ z₀).trans ((hN.const_le z₀).trans ?_)
    rw [hNd]
  have hWB : ∀ {A : Finset F.Cell}, A ⊆ cellBall S z₀ 2 → ∑ z ∈ A, W z ≤ ∑ z ∈ cellBall S z₀ 2, W z := fun h =>
    Finset.sum_le_sum_of_subset_of_nonneg h fun _ _ _ => hW0 _
  have hmeanY : ∀ y ∈ cellBall S z₀ 1, σ y * ‖frameCellMean S V y (gluedRemainder S V E)‖ ≤
      K * C2 * ∑ z ∈ cellBall S z₀ 2, W z := by
    intro y hy
    have hyS := hS1 hy
    have hd1 := (Finset.mem_filter.1 hy).2
    have h1 := frameCellMean_gluedRemainder_bound (V := V) (E := E) hamb hodd hreg hm hN hK hyS
    refine h1.trans ?_
    have hsub : cellBall S y 1 ⊆ cellBall S z₀ 2 := by
      intro z hz
      obtain ⟨hz1, hz2⟩ := Finset.mem_filter.1 hz
      refine Finset.mem_filter.2 ⟨hz1, ?_⟩
      have h4 := cellSupDist_triangle z₀ y z
      omega
    have h2 : ∑ z ∈ cellBall S y 1, Md (remainderSize S z (E z)) y ≤ ∑ z ∈ cellBall S y 1, C2 * N * W z := by
      refine Finset.sum_le_sum fun z hz => ?_
      have := hQ z (hsub hz) y hy
      rw [hEz] at this
      exact this
    rw [← Finset.mul_sum] at h2
    rw [← hNd]
    calc K / N * ∑ z ∈ cellBall S y 1, Md (remainderSize S z (E z)) y
        ≤ K / N * (C2 * N * ∑ z ∈ cellBall S y 1, W z) := mul_le_mul_of_nonneg_left h2 (div_nonneg hK hN0.le)
      _ = K * C2 * ∑ z ∈ cellBall S y 1, W z := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (hWB hsub) (mul_nonneg hK hC20)
  obtain ⟨TW, hTW⟩ : ∃ TW, TW = ∑ z ∈ cellBall S z₀ 2, W z := ⟨_, rfl⟩
  have hTW0 : 0 ≤ TW := hTW ▸ Finset.sum_nonneg fun _ _ => hW0 _
  rw [← hTW] at hmeanY
  have hMcOne : Mc * Md (fun _ => 1) z₀ ≤ 81 * K ^ 3 * (162 + 810 * cutoffBound) * C2 * TW := by
    have hs0 := hN.scale_pos z₀
    have hc4 : cc * N ≤ 162 + 810 * cutoffBound := by
      rw [hccd, div_mul_cancel₀ _ hN0.ne']
      linarith
    have hy1 : ∀ y ∈ cellBall S z₀ 1, cc * ‖frameCellMean S V y (gluedRemainder S V E)‖ * (K * N * σ z₀) ≤
        K ^ 3 * (162 + 810 * cutoffBound) * C2 * TW := by
      intro y hy
      have hd := (Finset.mem_filter.1 hy).2
      have hsn : σ z₀ ≤ K * σ y := hN.scale_le_of_near z₀ y (hd.trans (by norm_num))
      have hm0 := norm_nonneg (frameCellMean S V y (gluedRemainder S V E))
      have h1 : σ z₀ * ‖frameCellMean S V y (gluedRemainder S V E)‖ ≤ K * (K * C2 * TW) := by
        calc σ z₀ * ‖frameCellMean S V y (gluedRemainder S V E)‖
            ≤ (K * σ y) * ‖frameCellMean S V y (gluedRemainder S V E)‖ :=
              mul_le_mul_of_nonneg_right hsn hm0
          _ = K * (σ y * ‖frameCellMean S V y (gluedRemainder S V E)‖) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (hmeanY y hy) hK
      have hcN : 0 ≤ cc * N := mul_nonneg hcc0 hN0.le
      calc cc * ‖frameCellMean S V y (gluedRemainder S V E)‖ * (K * N * σ z₀)
          = (cc * N) * K * (σ z₀ * ‖frameCellMean S V y (gluedRemainder S V E)‖) := by ring
        _ ≤ (162 + 810 * cutoffBound) * K * (K * (K * C2 * TW)) := by
            exact mul_le_mul (mul_le_mul_of_nonneg_right hc4 hK) h1 (mul_nonneg hs0.le hm0)
              (mul_nonneg (by linarith) hK)
        _ = _ := by ring
    have hM0 : 0 ≤ Md (fun _ => 1) z₀ := hN.isSeminorm_base.nonneg _ _
    calc Mc * Md (fun _ => 1) z₀ ≤ Mc * (K * N * σ z₀) := mul_le_mul_of_nonneg_left hone hMc0
      _ = ∑ y ∈ cellBall S z₀ 1, cc * ‖frameCellMean S V y (gluedRemainder S V E)‖ * (K * N * σ z₀) := by
          rw [hMc, Finset.sum_mul]
      _ ≤ 81 * (K ^ 3 * (162 + 810 * cutoffBound) * C2 * TW) :=
          sum_cellBall_one_le hamb
            (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hK 3) (by linarith)) hC20) hTW0) z₀ hy1
      _ = _ := by ring
  have hPi : ∀ i, Md (Pf i) z₀ ≤ ((2 * (81 * K) * C2 + weightConstant * C2 + (1 + 81 * K)) * TW) +
      81 * K ^ 3 * (162 + 810 * cutoffBound) * C2 * TW := by
    intro i
    have hfun : Pf i = fun x => (∑ z ∈ cellBall S z₀ 2,
        (ca * Ez z (x + unitStep 0 i) + cb * Ez z x + (D z x + D z (x + unitStep 0 i)))) + Mc * 1 := by
      rw [hPf]
    rw [hfun]
    refine (hN.isSeminorm_base.add_le _ _ z₀).trans ?_
    have h1 := hN.isSeminorm_base.sum_le (cellBall S z₀ 2)
      (fun z x => ca * Ez z (x + unitStep 0 i) + cb * Ez z x + (D z x + D z (x + unitStep 0 i))) z₀
    have h2 : ∑ z ∈ cellBall S z₀ 2,
        Md (fun x => ca * Ez z (x + unitStep 0 i) + cb * Ez z x + (D z x + D z (x + unitStep 0 i))) z₀ ≤
        ∑ z ∈ cellBall S z₀ 2, (2 * (81 * K) * C2 + weightConstant * C2 + (1 + 81 * K)) * W z := by
      refine Finset.sum_le_sum fun z hz => (hterm i z hz).trans ?_
      have hWz := hW0 z
      have e1 : ca * (K * (81 * (C2 * N * W z))) = 2 * Cs * (81 * K) * C2 * W z := by
        rw [hcad]
        field_simp
      have e2 : cb * (C2 * N * W z) = weightConstant * C2 * W z := by
        rw [hcbd]
        field_simp
      have h3 : 2 * Cs * (81 * K) * C2 * W z ≤ 2 * (81 * K) * C2 * W z := by
        have hp : 0 ≤ (81 * K) * C2 * W z := mul_nonneg (mul_nonneg (by positivity) hC20) hWz
        have : 2 * Cs * (81 * K) * C2 * W z = 2 * Cs * ((81 * K) * C2 * W z) := by ring
        rw [this]
        nlinarith
      rw [e1, e2]
      nlinarith
    rw [← Finset.mul_sum, ← hTW] at h2
    have h3 := hN.isSeminorm_base.smul Mc (fun _ => 1) z₀
    rw [abs_of_nonneg hMc0] at h3
    rw [h3]
    linarith
  have hsum : Md (fun x => ∑ i, Pf i x) z₀ ≤
      ∑ _i : Fin 4, (((2 * (81 * K) * C2 + weightConstant * C2 + (1 + 81 * K)) * TW) +
        81 * K ^ 3 * (162 + 810 * cutoffBound) * C2 * TW) :=
    (hN.isSeminorm_base.sum_le Finset.univ Pf z₀).trans (Finset.sum_le_sum fun i _ => hPi i)
  refine (hN.isSeminorm_base.mono_abs _ _ z₀ hpt).trans (hsum.trans (le_of_eq ?_))
  rw [← hC2]
  have e : ∑ z ∈ cellBall S z₀ 2, ∑ x ∈ cellBall S z 20, Md (D z) x = TW := by
    rw [hTW, hWd]
  rw [e]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring
end Form
theorem gaugeRemainderCellBoundStatement_holds (hPD : covariantDiffPatchRemainderStatement)
    (hFr : patchFrameExistenceStatement) : gaugeRemainderCellBoundStatement := by
  classical
  obtain ⟨Cf, r, cf, hCf, hr, hcf, hFrames⟩ := hFr
  intro K hK
  obtain ⟨Cp, cp, L1p, hCp, hcp, hP⟩ := hPD K hK
  obtain ⟨C6, hC6⟩ : ∃ C6, C6 = 4 * (2 * (81 * K) * (Cp * (K ^ 2 + K ^ 5)) +
      weightConstant * (Cp * (K ^ 2 + K ^ 5)) +
      (1 + 81 * K) + 81 * K ^ 3 * (162 + 810 * cutoffBound) * (Cp * (K ^ 2 + K ^ 5))) := ⟨_, rfl⟩
  have hb := one_le_cutoffBound
  have hCb : 0 ≤ weightConstant := by
    unfold weightConstant
    positivity
  have hC60 : 0 ≤ C6 := by
    rw [hC6]
    have h1 : 0 ≤ Cp * (K ^ 2 + K ^ 5) := by positivity
    have h2 : 0 ≤ 162 + 810 * cutoffBound := by linarith
    positivity
  refine ⟨C6 * Cp * 625 + 1, min cp (min cf (1 / Cf)), max L1p (⌈1 / r⌉₊ + 1), by positivity,
    lt_min hcp (lt_min hcf (by positivity)), ?_⟩
  intro F m S hodd hL1 hamb hm hreg s V hs hsc hcold
  have hL := hodd.pos
  have hm32 : 32 ≤ m := by omega
  have hNz : (1 : ℝ) ≤ cellSideLength F := by exact_mod_cast cellSideLength_pos (F := F) hL
  have hN0 : (0 : ℝ) < cellSideLength F := by linarith
  have hLN : (F.blockSide : ℝ) ≤ cellSideLength F := by
    have h1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hL
    have h2 : (F.blockSide : ℝ) ≤ (F.blockSide : ℝ) ^ F.top := le_self_pow₀ h1 (by simp [BlockFrame.top])
    simpa [cellSideLength] using h2
  have hr1 : 1 ≤ r * cellSideLength F := by
    have h1 : 1 / r ≤ (F.blockSide : ℝ) := by
      have h2 : (⌈1 / r⌉₊ : ℝ) ≤ F.blockSide := by
        have : ⌈1 / r⌉₊ ≤ F.blockSide := by
          have := (le_max_right _ _).trans hL1
          omega
        exact_mod_cast this
      exact (Nat.le_ceil _).trans h2
    have h3 : 1 / r ≤ cellSideLength F := h1.trans hLN
    rw [div_le_iff₀ hr] at h3
    linarith
  have hsp : s ≤ cp := hsc.trans (min_le_left _ _)
  have hsf : s ≤ cf := hsc.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hs1 : s ≤ 1 / Cf := hsc.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hC0 : 0 ≤ Cf * s := by positivity
  have hC1 : Cf * s ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hs1 hCf.le
    rwa [mul_one_div_cancel hCf.ne'] at this
  refine ⟨fun u => cellMeanFree_gaugeMap hamb hodd hreg hm32 _ u, fun ξ hξ => ?_⟩
  have hPer := hP F m S hodd ((le_max_left _ _).trans hL1) hamb hm hreg s V hs hsp hcold ξ hξ
  choose! E D hRest hW using hPer
  choose! Rf hRf using fun z (hz : z ∈ S) => hFrames F m S hodd hamb hm hreg s V hs hsf hcold z hz
  refine ⟨cellMeanFree_gaugeRemainder hodd hreg hm32 hL hξ (cellMeanFree_gaugeMap hamb hodd hreg hm32 _ _),
    fun Md Lf Sr σ hN z₀ hz₀ => ?_⟩
  have h1 := formNormOn_gaugeRemainder_bound hamb hodd hreg hm32 hN hK.le hξ hRest hRf hr1 hC0 hC1 hCp.le hz₀
  rw [← hC6] at h1
  refine h1.trans ?_
  obtain ⟨g, hgd⟩ : ∃ g : F.Cell → ℝ, g = fun y => Md (sectionNormOn S ξ) y / (cellSideLength F : ℝ) +
      Md (formNormOn S (covariantDiff (referenceFieldChain S V 0) ξ)) y := ⟨_, rfl⟩
  have hg0 : ∀ y, 0 ≤ g y := fun y =>
    hgd ▸ add_nonneg (div_nonneg (hN.isSeminorm_base.nonneg _ _) hN0.le) (hN.isSeminorm_base.nonneg _ _)
  have hG0 : 0 ≤ ∑ y ∈ cellBall S z₀ 22, g y := Finset.sum_nonneg fun _ _ => hg0 _
  have hz : ∀ z ∈ cellBall S z₀ 2, ∑ x ∈ cellBall S z 20, Md (D z) x ≤ Cp * s * ∑ y ∈ cellBall S z₀ 22, g y := by
    intro z hz2
    obtain ⟨hzS, hzd⟩ := Finset.mem_filter.1 hz2
    refine (hW z hzS Md Lf Sr σ hN).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have hsub : cellBall S z 20 ⊆ cellBall S z₀ 22 := by
      intro y hy
      obtain ⟨hy1, hy2⟩ := Finset.mem_filter.1 hy
      refine Finset.mem_filter.2 ⟨hy1, ?_⟩
      have h4 := cellSupDist_triangle z₀ z y
      omega
    refine le_trans (Finset.sum_le_sum fun y _ => ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => hg0 _)
    rw [hgd]
    have hmono : ∀ (f : F.Site 0 → ℝ), Md (restrictToPatch S z f) y ≤ Md f y := fun f =>
      hN.isSeminorm_base.mono_abs _ _ _ fun x _ => by
        by_cases hx : x ∈ patchSiteSet S z
        · rw [restrictToPatch_of_mem hx]
        · rw [restrictToPatch_of_not_mem hx]
          simp
    exact add_le_add (div_le_div_of_nonneg_right (hmono _) hN0.le) (hmono _)
  have h2 : ∑ z ∈ cellBall S z₀ 2, ∑ x ∈ cellBall S z 20, Md (D z) x ≤
      625 * (Cp * s * ∑ y ∈ cellBall S z₀ 22, g y) := by
    calc _ ≤ ∑ _z ∈ cellBall S z₀ 2, Cp * s * ∑ y ∈ cellBall S z₀ 22, g y := Finset.sum_le_sum hz
      _ = ((cellBall S z₀ 2).card : ℝ) * (Cp * s * ∑ y ∈ cellBall S z₀ 22, g y) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (card_cellBall_two hamb z₀) (mul_nonneg (by positivity) hG0)
  have h3 := mul_le_mul_of_nonneg_left h2 hC60
  refine h3.trans ?_
  have eg : ∑ y ∈ cellBall S z₀ 22, (Md (sectionNormOn S ξ) y / (cellSideLength F : ℝ) +
      Md (formNormOn S (covariantDiff (referenceFieldChain S V 0) ξ)) y) = ∑ y ∈ cellBall S z₀ 22, g y := by
    rw [hgd]
  rw [eg]
  have e : C6 * (625 * (Cp * s * ∑ y ∈ cellBall S z₀ 22, g y)) =
      (C6 * Cp * 625) * s * ∑ y ∈ cellBall S z₀ 22, g y := by ring
  rw [e]
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hs.le) ?_
  exact hG0
end YangMills.Construction.GaugeRemainderBounds
end
