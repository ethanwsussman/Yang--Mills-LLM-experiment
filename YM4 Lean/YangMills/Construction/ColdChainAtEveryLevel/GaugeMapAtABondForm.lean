import YangMills.Construction.ColdChainAtEveryLevel.GapsBetweenPatches
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BondGauge
open BlockAverages GaugeMap PatchPoints PatchForms PatchPotentials PotentialMeans PatchGaps BondShares
  LatticeFractionalIntegration
section Near
variable {F : BlockFrame} {S : Finset F.Cell} {V : F.GaugeField F.top} {Cs r Ch : ℝ}
theorem cellPartition_nonneg (x : F.Site 0) (y : F.Cell) : 0 ≤ cellPartition S x y :=
  div_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
theorem cellPartition_le_one (x : F.Site 0) {y : F.Cell} (hy : y ∈ S) : cellPartition S x y ≤ 1 := by apply _root_.YangMills.Construction.BlockAverages.PatchLocality.cellPartition_le_one <;> assumption
theorem cellSupDist_le_one_of_partition_ne_zero (h : PotentialSetting S V Cs r Ch) {z₀ z : F.Cell} {s : F.Site 0}
    (hs : s ∈ cellSites S z₀) (hne : cellPartition S s z ≠ 0) :
    cellSupDist z z₀ ≤ 1 := by
  classical
  have hL := h.odd_side.pos
  have hNr : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by
    have : (0 : ℝ) < F.blockSide := by exact_mod_cast hL
    positivity
  have hb : cellCutoff s z ≠ 0 := fun hb =>
    hne (BlockAverages.LocalPartition.cellPartition_eq_zero_of_cellCutoff_eq_zero hb)
  have hc : enclosingCell s = z₀ := (Finset.mem_filter.1 hs).2
  have key := cellSupDist_enclosingCell_le h.odd_side s z 1 fun i => by
    have h1 : cutoffProfile ((((s - cellCentre 0 z) i).valMinAbs : ℝ) / (F.blockSide : ℝ) ^ F.top) ≠ 0 :=
      fun h0 => hb (Finset.prod_eq_zero (Finset.mem_univ i) h0)
    have h2 := abs_lt_of_cutoffProfile_ne_zero h1
    rw [abs_div, abs_of_pos hNr, div_lt_iff₀ hNr] at h2
    have h3 : ((|((s - cellCentre 0 z) i).valMinAbs| : ℤ) : ℝ) < (((F.blockSide ^ F.top : ℕ) : ℤ) : ℝ) := by
      push_cast
      nlinarith
    have h4 : |((s - cellCentre 0 z) i).valMinAbs| < ((F.blockSide ^ F.top : ℕ) : ℤ) := by exact_mod_cast h3
    rw [Int.abs_eq_natAbs] at h4
    omega
  rw [hc] at key
  rw [cellSupDist_symm]
  exact key
theorem mem_and_eq_of_mem_cellSites (h : PotentialSetting S V Cs r Ch) {y : F.Cell} {s : F.Site 0}
    (hs : s ∈ cellSites S y) :
    y ∈ S ∧ ∃ g ∈ centredCube (F.blockSide ^ F.top), s = cellCentre 0 y + siteOfCoords 0 g := by
  obtain ⟨y', hy', g, hg, e⟩ := mem_sitesOfCells.1 (Finset.mem_filter.1 hs).1
  have hg' : g ∈ centredCube (F.blockSide ^ F.top) := by simpa using hg
  have hc : enclosingCell s = y' := by
    rw [e]
    exact BlockAverages.LocalPartition.enclosingCell_cellCentre_add h.odd_side y' g hg'
  have hyy : y' = y := by rw [← hc]; exact (Finset.mem_filter.1 hs).2
  subst hyy
  exact ⟨hy', g, hg', e⟩
theorem exists_cellBall_of_step (h : PotentialSetting S V Cs r Ch) {z₀ : F.Cell} {s : F.Site 0} {i : Fin 4}
    (hs : s ∈ cellSites S z₀) (hs' : s + unitStep 0 i ∈ sitesOfCells S 0) :
    ∃ y', y' ∈ cellBall S z₀ 1 ∧ s + unitStep 0 i ∈ cellSites S y' := by
  classical
  obtain ⟨hz₀, g, hg, e⟩ := mem_and_eq_of_mem_cellSites h hs
  have hst : stepDisplacement (F := F) 0 ((i, true) : PathStep) = unitStep 0 i := by simp [stepDisplacement]
  have h1 := cellSupDist_enclosingCell_step h.odd_side (y := z₀) hg (i, true)
  rw [hst, ← e] at h1
  refine ⟨enclosingCell (s + unitStep 0 i),
    Finset.mem_filter.2 ⟨BlockAverages.LocalPartition.enclosingCell_mem h.odd_side hs', ?_⟩,
    Finset.mem_filter.2 ⟨hs', rfl⟩⟩
  rw [cellSupDist_symm]
  exact h1
theorem sum_cellPartition (h : PotentialSetting S V Cs r Ch) {x : F.Site 0} (hx : x ∈ sitesOfCells S 0) :
    ∑ y ∈ S, cellPartition S x y = 1 := by
  obtain ⟨y, hy, g, hg, rfl⟩ := mem_sitesOfCells.1 hx
  have hb := cellCutoff_self h.ambient h.odd_side y (h := g) (by simpa using hg)
  have hpos : 0 < ∑ y' ∈ S, cellCutoff (cellCentre 0 y + siteOfCoords 0 g) y' ^ 2 := by
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum
      (f := fun y' => cellCutoff (cellCentre 0 y + siteOfCoords 0 g) y' ^ 2) (fun _ _ => sq_nonneg _) hy)
    simp [hb]
  unfold cellPartition
  rw [← Finset.sum_div, div_self hpos.ne']
end Near
section Split
variable {F : BlockFrame} {S : Finset F.Cell} {V : F.GaugeField F.top} {Cs r Ch : ℝ}
def formAddGaugeDiff (S : Finset F.Cell) (V : F.GaugeField F.top) (u : F.Site 0 → Fin 4 → imaginaryQuaternions)
    (x : F.Site 0) (i : Fin 4) : ℍ[ℝ] :=
  toQuaternionForm u x i + covariantDiff (referenceFieldChain S V 0)
    (gaugeMap S V (referenceFieldChain S V 0) (toQuaternionForm u)) x i
def gluedOfForm (S : Finset F.Cell) (V : F.GaugeField F.top) (u : F.Site 0 → Fin 4 → imaginaryQuaternions) :
    F.Site 0 → ℍ[ℝ] :=
  gluedPotential S V (referenceFieldChain S V 0) (toQuaternionForm u)
theorem gluedOfForm_apply (u : F.Site 0 → Fin 4 → imaginaryQuaternions) (s : F.Site 0) :
    gluedOfForm S V u s = ∑ z ∈ S, cellPartition S s z • potentialSection S V z u s := rfl
def cutoffPart (S : Finset F.Cell) (V : F.GaugeField F.top) (u : F.Site 0 → Fin 4 → imaginaryQuaternions)
    (s : F.Site 0) : ℍ[ℝ] :=
  ∑ y ∈ S, normalizedBump S s y • adjointAction (frameChange S V y s) (frameCellMean S V y (gluedOfForm S V u))
theorem gaugeMap_eq_sub_cutoffPart (u : F.Site 0 → Fin 4 → imaginaryQuaternions) (s : F.Site 0) :
    gaugeMap S V (referenceFieldChain S V 0) (toQuaternionForm u) s = gluedOfForm S V u s - cutoffPart S V u s := rfl
theorem formAddGaugeDiff_eq (h : PotentialSetting S V Cs r Ch) (u : F.Site 0 → Fin 4 → imaginaryQuaternions)
    (z₀ : F.Cell) {s : F.Site 0} {i : Fin 4}
    (hs : s ∈ sitesOfCells S 0) (hs' : s + unitStep 0 i ∈ sitesOfCells S 0) :
    formAddGaugeDiff S V u s i = ∑ z ∈ S, cellPartition S s z • primitiveDefect S V z u s i +
      ∑ z ∈ S, (cellPartition S (s + unitStep 0 i) z - cellPartition S s z) •
        adjointAction (referenceFieldChain S V 0 s i) (potentialGap S V z z₀ u (s + unitStep 0 i)) -
      covariantDiff (referenceFieldChain S V 0) (cutoffPart S V u) s i := by
  classical
  obtain ⟨R, hR⟩ : ∃ R, R = referenceFieldChain S V 0 s i := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = toQuaternionForm u s i := ⟨_, rfl⟩
  obtain ⟨a₀, ha₀⟩ : ∃ a₀, a₀ = adjointAction R (potentialSection S V z₀ u (s + unitStep 0 i)) := ⟨_, rfl⟩
  have A1 := sum_cellPartition h hs
  have A2 := sum_cellPartition h hs'
  have key : ∀ z ∈ S, cellPartition S s z • primitiveDefect S V z u s i +
      (cellPartition S (s + unitStep 0 i) z - cellPartition S s z) •
      adjointAction R (potentialGap S V z z₀ u (s + unitStep 0 i)) =
      cellPartition S s z • q + cellPartition S (s + unitStep 0 i) z •
          adjointAction R (potentialSection S V z u (s + unitStep 0 i)) -
        cellPartition S s z • potentialSection S V z u s -
        (cellPartition S (s + unitStep 0 i) z • a₀ - cellPartition S s z • a₀) := by
    intro z _
    simp only [primitiveDefect, covariantDiff, potentialGap, adjointAction_apply_sub, ← hR, ← hq, ← ha₀]
    simp only [smul_add, smul_sub, sub_smul]
    abel
  have hbig : ∑ z ∈ S, cellPartition S s z • primitiveDefect S V z u s i +
      ∑ z ∈ S, (cellPartition S (s + unitStep 0 i) z - cellPartition S s z) •
      adjointAction R (potentialGap S V z z₀ u (s + unitStep 0 i)) =
      q + adjointAction R (gluedOfForm S V u (s + unitStep 0 i)) - gluedOfForm S V u s := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl key, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_smul, ← Finset.sum_smul, ← Finset.sum_smul, A1, A2,
      gluedOfForm_apply, gluedOfForm_apply, adjointAction_apply_sum]
    simp only [adjointAction_apply_smul, one_smul, sub_self, sub_zero]
  rw [← hR, hbig]
  simp only [formAddGaugeDiff, covariantDiff]
  rw [gaugeMap_eq_sub_cutoffPart, gaugeMap_eq_sub_cutoffPart, ← hR, ← hq, adjointAction_apply_sub]
  abel
end Split
section Terms
variable {F : BlockFrame} {S : Finset F.Cell} {V : F.GaugeField F.top} {Cs r Ch : ℝ}
theorem patchSite_mem_cellSites_of_offset (h : PotentialSetting S V Cs r Ch) {y : F.Cell} (hy : y ∈ S) {a : Lattice4}
    (ha : a ∈ cellOffsets F) : patchSite S y a ∈ cellSites S y := by
  obtain ⟨h0, h1⟩ := cellSideLength_half (F := F) h.odd_side
  have hcube : (fun k => closedOrthant S y k * (a k - (cellSideLength F - 1) / 2)) ∈
      centredCube (F.blockSide ^ F.top) := by
    rw [mem_centredCube_iff]
    intro i
    have := Finset.mem_Ico.1 (Fintype.mem_piFinset.1 ha i)
    rcases h.closedOrthant_cases y i with hs | hs <;> rw [hs] <;> constructor <;> omega
  exact mem_cellSites_of_centredCube h.odd_side hy hcube
theorem norm_sum_primitiveDefect_le (h : PotentialSetting S V Cs r Ch) (u : F.Site 0 → Fin 4 → imaginaryQuaternions)
    {z₀ : F.Cell} {s : F.Site 0} {i : Fin 4}
    (hs : s ∈ cellSites S z₀) (hs' : s + unitStep 0 i ∈ sitesOfCells S 0) :
    ‖∑ z ∈ S, cellPartition S s z • primitiveDefect S V z u s i‖ ≤ ∑ z ∈ cellBall S z₀ 1,
      (defectBound (Cs / (cellSideLength F : ℝ)) Ch S V z u s +
        defectBound (Cs / (cellSideLength F : ℝ)) Ch S V z u (s + unitStep 0 i)) := by
  classical
  have hsub : cellBall S z₀ 1 ⊆ S := Finset.filter_subset _ _
  have e : ∑ z ∈ S, cellPartition S s z • primitiveDefect S V z u s i =
      ∑ z ∈ cellBall S z₀ 1, cellPartition S s z • primitiveDefect S V z u s i := by
    refine (Finset.sum_subset hsub fun z hz hn => ?_).symm
    have h0 : cellPartition S s z = 0 := by
      by_contra hne
      exact hn (Finset.mem_filter.2 ⟨hz, by
        rw [cellSupDist_symm]; exact cellSupDist_le_one_of_partition_ne_zero h hs hne⟩)
    rw [h0, zero_smul]
  rw [e]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun z hz => ?_)
  obtain ⟨hzS, hzd⟩ := Finset.mem_filter.1 hz
  obtain ⟨y', hy', hsy⟩ := exists_cellBall_of_step h hs hs'
  obtain ⟨hy'S, hy'd⟩ := Finset.mem_filter.1 hy'
  have hz₀ : z₀ ∈ S := (mem_and_eq_of_mem_cellSites h hs).1
  have p0 : s ∈ patchSiteSet S z :=
    h.mem_patchSiteSet_of_cellSupDist_le hz₀ (by rw [cellSupDist_symm]; omega) hs
  have p1 : s + unitStep 0 i ∈ patchSiteSet S z := by
    refine h.mem_patchSiteSet_of_cellSupDist_le hy'S ?_ hsy
    have := cellSupDist_triangle z z₀ y'
    rw [cellSupDist_symm z z₀] at this
    omega
  obtain ⟨R, hF⟩ := h.frames z hzS
  obtain ⟨H, Gk, hk⟩ := exists_homotopyKernels_patchDomain h hzS
  have hd := norm_primitiveDefect_le h hF hk u p0 p1
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (cellPartition_nonneg _ _)]
  refine le_trans ?_ hd
  exact mul_le_of_le_one_left (norm_nonneg _) (cellPartition_le_one _ hzS)
theorem abs_cellPartition_sub_le (h : PotentialSetting S V Cs r Ch) {z₀ z : F.Cell} {s : F.Site 0} {i : Fin 4}
    (hs : s ∈ cellSites S z₀) (hs' : s + unitStep 0 i ∈ sitesOfCells S 0) (hz : z ∈ S) :
    |cellPartition S (s + unitStep 0 i) z - cellPartition S s z| ≤ weightConstant / (cellSideLength F : ℝ) := by
  classical
  obtain ⟨y', hy', hsy⟩ := exists_cellBall_of_step h hs hs'
  obtain ⟨hy'S, hy'd⟩ := Finset.mem_filter.1 hy'
  have hz₀ : z₀ ∈ S := (mem_and_eq_of_mem_cellSites h hs).1
  have he := h.closedOrthant_cases z₀
  have p0 : s ∈ patchSiteSet S z₀ := h.mem_patchSiteSet_of_cellSupDist_le hz₀ (by simp [cellSupDist]) hs
  have p1 : s + unitStep 0 i ∈ patchSiteSet S z₀ := h.mem_patchSiteSet_of_cellSupDist_le hy'S (by omega) hsy
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 p0
  obtain ⟨a', ha', e'⟩ := Finset.mem_image.1 p1
  have hst : stepDisplacement (F := F) 0 ((i, true) : PathStep) = unitStep 0 i := by simp [stepDisplacement]
  have hra := patchDomain_coord_bounds ha
  have cs := patchChart_add_stepDisplacement h.ambient h.odd_side he (s := patchSite S z₀ a) (i, true)
    (by rw [h.patchChart_patchSite ha]; exact hra)
  rw [hst, ← e', h.patchChart_patchSite ha', h.patchChart_patchSite ha] at cs
  have hd : ∀ k, |a k - a' k| ≤ 1 := by
    intro k
    rw [cs]
    have e1 : a k - (a k + closedOrthant S z₀ k * stepOffset ((i, true) : PathStep) k) =
        - (closedOrthant S z₀ k * stepOffset ((i, true) : PathStep) k) := by ring
    simp only []
    rw [e1, abs_neg, abs_mul, abs_closedOrthant he, one_mul]
    exact abs_stepOffset_le _ k
  have key := cellPartition_abs_sub_le h.ambient h.odd_side he hra (patchDomain_coord_bounds ha')
    (Finset.mem_filter.1 hs).1 (e' ▸ hs') hd hz
  rw [← cellSideLength_cast] at key
  rw [← e', abs_sub_comm]
  exact key
theorem norm_sum_potentialGap_le (h : PotentialSetting S V Cs r Ch) (u : F.Site 0 → Fin 4 → imaginaryQuaternions)
    {z₀ : F.Cell} {s : F.Site 0} {i : Fin 4}
    (hs : s ∈ cellSites S z₀) (hs' : s + unitStep 0 i ∈ sitesOfCells S 0) (A : UnitQuaternion) :
    ‖∑ z ∈ S, (cellPartition S (s + unitStep 0 i) z - cellPartition S s z) •
        adjointAction A (potentialGap S V z z₀ u (s + unitStep 0 i))‖ ≤
      ∑ z ∈ cellBall S z₀ 2, weightConstant / (cellSideLength F : ℝ) *
        PatchDifferences.sectionNormOn S (potentialGap S V z z₀ u) (s + unitStep 0 i) := by
  classical
  have hsub : cellBall S z₀ 2 ⊆ S := Finset.filter_subset _ _
  obtain ⟨y', hy', hsy⟩ := exists_cellBall_of_step h hs hs'
  obtain ⟨hy'S, hy'd⟩ := Finset.mem_filter.1 hy'
  have e : ∑ z ∈ S, (cellPartition S (s + unitStep 0 i) z - cellPartition S s z) •
      adjointAction A (potentialGap S V z z₀ u (s + unitStep 0 i)) =
      ∑ z ∈ cellBall S z₀ 2, (cellPartition S (s + unitStep 0 i) z - cellPartition S s z) •
        adjointAction A (potentialGap S V z z₀ u (s + unitStep 0 i)) := by
    refine (Finset.sum_subset hsub fun z hz hn => ?_).symm
    have h0 : cellPartition S s z = 0 := by
      by_contra hne
      have := cellSupDist_le_one_of_partition_ne_zero h hs hne
      exact hn (Finset.mem_filter.2 ⟨hz, by rw [cellSupDist_symm]; omega⟩)
    have h1 : cellPartition S (s + unitStep 0 i) z = 0 := by
      by_contra hne
      have h2 := cellSupDist_le_one_of_partition_ne_zero h hsy hne
      have h3 := cellSupDist_triangle z y' z₀
      rw [cellSupDist_symm y' z₀] at h3
      exact hn (Finset.mem_filter.2 ⟨hz, by rw [cellSupDist_symm]; omega⟩)
    rw [h0, h1, sub_zero, zero_smul]
  rw [e]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun z hz => ?_)
  obtain ⟨hzS, -⟩ := Finset.mem_filter.1 hz
  have hc := abs_cellPartition_sub_le h hs hs' hzS
  rw [norm_smul, Real.norm_eq_abs, norm_adjointAction_apply]
  have e2 : PatchDifferences.sectionNormOn S (potentialGap S V z z₀ u) (s + unitStep 0 i) =
      ‖potentialGap S V z z₀ u (s + unitStep 0 i)‖ := by
    simp [PatchDifferences.sectionNormOn, hs']
  rw [e2]
  exact mul_le_mul_of_nonneg_right hc (norm_nonneg _)
def cutoffConstant : ℝ := 810 * cutoffBound + 162
theorem cutoffConstant_nonneg : 0 ≤ cutoffConstant := by
  have := one_le_cutoffBound
  unfold cutoffConstant
  positivity
theorem norm_cutoff_term_le (h : PotentialSetting S V Cs r Ch) {y : F.Cell} (hy : y ∈ S) {s : F.Site 0} {i : Fin 4}
    (p0 : s ∈ patchSiteSet S y) (p1 : s + unitStep 0 i ∈ patchSiteSet S y) (m : ℍ[ℝ]) :
    ‖adjointAction (referenceFieldChain S V 0 s i) (normalizedBump S (s + unitStep 0 i) y •
        adjointAction (frameChange S V y (s + unitStep 0 i)) m) -
        normalizedBump S s y • adjointAction (frameChange S V y s) m‖ ≤
      cutoffConstant / (cellSideLength F : ℝ) * ‖m‖ := by
  classical
  have he := h.closedOrthant_cases y
  have hNp := h.cellSideLength_pos
  have hc1 := h.coldness_le_one
  obtain ⟨R, hF⟩ := h.frames y hy
  obtain ⟨T, hT, hl⟩ := exists_leadingTransport_near_one hF h.scale h.ambient h.odd_side he p0 p1
  obtain ⟨f, hf⟩ : ∃ f, f = frameChange S V y s := ⟨_, rfl⟩
  obtain ⟨f', hf'⟩ : ∃ f', f' = frameChange S V y (s + unitStep 0 i) := ⟨_, rfl⟩
  obtain ⟨a, ha, ea⟩ := Finset.mem_image.1 p0
  obtain ⟨a', ha', ea'⟩ := Finset.mem_image.1 p1
  have hst : stepDisplacement (F := F) 0 ((i, true) : PathStep) = unitStep 0 i := by simp [stepDisplacement]
  have hra := patchDomain_coord_bounds ha
  have cs := patchChart_add_stepDisplacement h.ambient h.odd_side he (s := patchSite S y a) (i, true)
    (by rw [h.patchChart_patchSite ha]; exact hra)
  rw [ea, hst, ← ea', h.patchChart_patchSite ha', ← ea, h.patchChart_patchSite ha] at cs
  have hd : ∀ k, |a k - a' k| ≤ 1 := by
    intro k
    rw [cs]
    have e1 : a k - (a k + closedOrthant S y k * stepOffset ((i, true) : PathStep) k) =
        - (closedOrthant S y k * stepOffset ((i, true) : PathStep) k) := by ring
    simp only []
    rw [e1, abs_neg, abs_mul, abs_closedOrthant he, one_mul]
    exact abs_stepOffset_le _ k
  have hstep := normalizedBump_abs_sub_le h.ambient h.odd_side he hra (patchDomain_coord_bounds ha') hd
  rw [ea, ea'] at hstep
  have hb0 : 0 ≤ normalizedBump S s y := normalizedBump_nonneg h.ambient h.odd_side he s
  have hb1 : normalizedBump S s y ≤ 81 := by
    have hm := inv_81_le_interiorBumpMean (S := S) (z := y) h.ambient h.odd_side he
    have hm0 : 0 < interiorBumpMean S y := by linarith
    rw [normalizedBump_eq, div_le_iff₀ hm0]
    have := interiorBump_le_one_at s y
    linarith
  have eR : referenceFieldChain S V 0 s i = f * T * f'⁻¹ := by
    rw [referenceFieldChain_zero_eq, hl, hf, hf']
  have e1 : adjointAction (f * T * f'⁻¹) (adjointAction f' m) = adjointAction f (adjointAction T m) := by
    rw [← adjointAction_mul_apply, ← adjointAction_mul_apply]
    congr 1
    group
  rw [eR, ← hf, ← hf', adjointAction_apply_smul, e1]
  obtain ⟨b', hb'⟩ : ∃ b', b' = normalizedBump S (s + unitStep 0 i) y := ⟨_, rfl⟩
  obtain ⟨b0, hb0'⟩ : ∃ b0, b0 = normalizedBump S s y := ⟨_, rfl⟩
  rw [← hb0'] at hb0 hb1
  rw [← hb', ← hb0'] at hstep ⊢
  have e2 : b' • adjointAction f (adjointAction T m) - b0 • adjointAction f m =
      (b' - b0) • adjointAction f (adjointAction T m) + b0 • adjointAction f (adjointAction T m - m) := by
    rw [adjointAction_apply_sub, sub_smul, smul_sub]
    abel
  rw [e2]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, norm_adjointAction_apply, norm_adjointAction_apply,
    norm_adjointAction_apply, abs_of_nonneg hb0]
  have t1 : |b' - b0| ≤ 810 * cutoffBound / (cellSideLength F : ℝ) := by
    rw [abs_sub_comm]
    exact hstep
  have t2 : ‖adjointAction T m - m‖ ≤ 2 * (Cs / (cellSideLength F : ℝ)) * ‖m‖ :=
    (norm_adjointAction_apply_sub_le _ _).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  have t3 : Cs / (cellSideLength F : ℝ) ≤ 1 / (cellSideLength F : ℝ) := div_le_div_of_nonneg_right hc1 hNp.le
  have hm0 := norm_nonneg m
  have t4 : |b' - b0| * ‖m‖ ≤ 810 * cutoffBound / (cellSideLength F : ℝ) * ‖m‖ :=
    mul_le_mul_of_nonneg_right t1 hm0
  have t5 : b0 * ‖adjointAction T m - m‖ ≤ 81 * (2 * (1 / (cellSideLength F : ℝ)) * ‖m‖) := by
    refine mul_le_mul hb1 (t2.trans ?_) (norm_nonneg _) (by norm_num)
    exact mul_le_mul_of_nonneg_right (by linarith) hm0
  have e3 : cutoffConstant / (cellSideLength F : ℝ) * ‖m‖ = 810 * cutoffBound / (cellSideLength F : ℝ) * ‖m‖ +
      81 * (2 * (1 / (cellSideLength F : ℝ)) * ‖m‖) := by
    unfold cutoffConstant
    ring
  rw [e3]
  exact add_le_add t4 t5
theorem normalizedBump_eq_zero_of_enclosingCell_ne {y : F.Cell} {t : F.Site 0} (h : PotentialSetting S V Cs r Ch)
    (ht : t ∈ sitesOfCells S 0) (hc : enclosingCell t ≠ y) :
    normalizedBump S t y = 0 := by
  have : interiorBump t y = 0 := by
    by_contra hne
    obtain ⟨g, hg, e⟩ := exists_centredCube_of_interiorBump_ne_zero h.odd_side hne
    exact hc (by rw [e]; exact BlockAverages.LocalPartition.enclosingCell_cellCentre_add h.odd_side y g hg)
  rw [normalizedBump_eq, this, zero_div]
theorem norm_covariantDiff_cutoffPart_le (h : PotentialSetting S V Cs r Ch)
    (u : F.Site 0 → Fin 4 → imaginaryQuaternions) {z₀ : F.Cell} {s : F.Site 0} {i : Fin 4}
    (hs : s ∈ cellSites S z₀) (hs' : s + unitStep 0 i ∈ sitesOfCells S 0) :
    ‖covariantDiff (referenceFieldChain S V 0) (cutoffPart S V u) s i‖ ≤
      ∑ y ∈ cellBall S z₀ 1, cutoffConstant / (cellSideLength F : ℝ) *
        ‖frameCellMean S V y (gluedOfForm S V u)‖ := by
  classical
  have hsub : cellBall S z₀ 1 ⊆ S := Finset.filter_subset _ _
  obtain ⟨y', hy', hsy⟩ := exists_cellBall_of_step h hs hs'
  obtain ⟨hy'S, hy'd⟩ := Finset.mem_filter.1 hy'
  have hz₀ : z₀ ∈ S := (mem_and_eq_of_mem_cellSites h hs).1
  have hss : s ∈ sitesOfCells S 0 := (Finset.mem_filter.1 hs).1
  have hcs : enclosingCell s = z₀ := (Finset.mem_filter.1 hs).2
  have hcs' : enclosingCell (s + unitStep 0 i) = y' := (Finset.mem_filter.1 hsy).2
  have e0 : covariantDiff (referenceFieldChain S V 0) (cutoffPart S V u) s i = ∑ y ∈ S,
      (adjointAction (referenceFieldChain S V 0 s i) (normalizedBump S (s + unitStep 0 i) y •
        adjointAction (frameChange S V y (s + unitStep 0 i)) (frameCellMean S V y (gluedOfForm S V u))) -
      normalizedBump S s y • adjointAction (frameChange S V y s) (frameCellMean S V y (gluedOfForm S V u))) := by
    simp only [covariantDiff, cutoffPart]
    rw [adjointAction_apply_sum, Finset.sum_sub_distrib]
  have e1 : ∑ y ∈ S, (adjointAction (referenceFieldChain S V 0 s i) (normalizedBump S (s + unitStep 0 i) y •
        adjointAction (frameChange S V y (s + unitStep 0 i)) (frameCellMean S V y (gluedOfForm S V u))) -
      normalizedBump S s y • adjointAction (frameChange S V y s) (frameCellMean S V y (gluedOfForm S V u))) =
      ∑ y ∈ cellBall S z₀ 1, (adjointAction (referenceFieldChain S V 0 s i)
        (normalizedBump S (s + unitStep 0 i) y •
        adjointAction (frameChange S V y (s + unitStep 0 i)) (frameCellMean S V y (gluedOfForm S V u))) -
      normalizedBump S s y • adjointAction (frameChange S V y s) (frameCellMean S V y (gluedOfForm S V u))) := by
    refine (Finset.sum_subset hsub fun y hy hn => ?_).symm
    have h1 : enclosingCell s ≠ y := by
      rw [hcs]
      rintro rfl
      exact hn (Finset.mem_filter.2 ⟨hy, by simp [cellSupDist]⟩)
    have h2 : enclosingCell (s + unitStep 0 i) ≠ y := by
      rw [hcs']
      rintro rfl
      exact hn hy'
    rw [normalizedBump_eq_zero_of_enclosingCell_ne h hss h1, normalizedBump_eq_zero_of_enclosingCell_ne h hs' h2,
      zero_smul, zero_smul, adjointAction_apply_zero, sub_zero]
  rw [e0, e1]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y hy => ?_)
  obtain ⟨hyS, hyd⟩ := Finset.mem_filter.1 hy
  have p0 : s ∈ patchSiteSet S y :=
    h.mem_patchSiteSet_of_cellSupDist_le hz₀ (by rw [cellSupDist_symm]; omega) hs
  have p1 : s + unitStep 0 i ∈ patchSiteSet S y := by
    refine h.mem_patchSiteSet_of_cellSupDist_le hy'S ?_ hsy
    have := cellSupDist_triangle y z₀ y'
    rw [cellSupDist_symm y z₀] at this
    omega
  exact norm_cutoff_term_le h hyS p0 p1 _
theorem norm_frameCellMean_gluedOfForm_le' (h : PotentialSetting S V Cs r Ch)
    (u : F.Site 0 → Fin 4 → imaginaryQuaternions) {y : F.Cell} (hy : y ∈ S) :
    ‖frameCellMean S V y (gluedOfForm S V u)‖ ≤ ∑ z ∈ cellBall S y 1, (1 / (cellSideLength F : ℝ) ^ 4) *
      ∑ c ∈ centredCube (F.blockSide ^ F.top),
        PatchDifferences.sectionNormOn S (potentialGap S V z y u) (cellCentre 0 y + siteOfCoords 0 c) := by
  classical
  have hL := h.odd_side.pos
  have hNp := h.cellSideLength_pos
  have hsub : cellBall S y 1 ⊆ S := Finset.filter_subset _ _
  have hpt : ∀ a ∈ cellOffsets F, adjointAction (frameChange S V y (patchSite S y a))⁻¹
      (gluedOfForm S V u (patchSite S y a)) =
      centredPotential S V y u a + adjointAction (frameChange S V y (patchSite S y a))⁻¹
        (∑ z ∈ S, cellPartition S (patchSite S y a) z • potentialGap S V z y u (patchSite S y a)) := by
    intro a ha
    have ht := patchSite_mem_cellSites_of_offset h hy ha
    have hts := (Finset.mem_filter.1 ht).1
    have e1 : gluedOfForm S V u (patchSite S y a) = potentialSection S V y u (patchSite S y a) +
        ∑ z ∈ S, cellPartition S (patchSite S y a) z • potentialGap S V z y u (patchSite S y a) := by
      rw [gluedOfForm_apply]
      have e2 : ∀ z ∈ S, cellPartition S (patchSite S y a) z • potentialSection S V z u (patchSite S y a) =
          cellPartition S (patchSite S y a) z • potentialSection S V y u (patchSite S y a) +
            cellPartition S (patchSite S y a) z • potentialGap S V z y u (patchSite S y a) := by
        intro z _
        rw [← smul_add, potentialGap]
        congr 1
        abel
      rw [Finset.sum_congr rfl e2, Finset.sum_add_distrib, ← Finset.sum_smul, sum_cellPartition h hts, one_smul]
    rw [e1, adjointAction_apply_add]
    congr 1
    simp only [potentialSection]
    rw [adjointAction_inv_apply_apply, h.patchChart_patchSite (mem_patchDomain_of_mem_cellOffsets hy hL ha)]
  have e0 : frameCellMean S V y (gluedOfForm S V u) = PatchPotentials.cellMean F (centredPotential S V y u) +
      (1 / (cellSideLength F : ℝ) ^ 4) • ∑ a ∈ cellOffsets F, adjointAction (frameChange S V y (patchSite S y a))⁻¹
        (∑ z ∈ S, cellPartition S (patchSite S y a) z • potentialGap S V z y u (patchSite S y a)) := by
    simp only [frameCellMean, PatchPotentials.cellMean]
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, smul_add]
  rw [e0, cellMean_centredPotential h u, zero_add, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hterm : ∀ a ∈ cellOffsets F, ‖adjointAction (frameChange S V y (patchSite S y a))⁻¹
      (∑ z ∈ S, cellPartition S (patchSite S y a) z • potentialGap S V z y u (patchSite S y a))‖ ≤
      ∑ z ∈ cellBall S y 1, PatchDifferences.sectionNormOn S (potentialGap S V z y u) (patchSite S y a) := by
    intro a ha
    have ht := patchSite_mem_cellSites_of_offset h hy ha
    have hts := (Finset.mem_filter.1 ht).1
    rw [norm_adjointAction_apply]
    have e : ∑ z ∈ S, cellPartition S (patchSite S y a) z • potentialGap S V z y u (patchSite S y a) =
        ∑ z ∈ cellBall S y 1, cellPartition S (patchSite S y a) z • potentialGap S V z y u (patchSite S y a) := by
      refine (Finset.sum_subset hsub fun z hz hn => ?_).symm
      have h0 : cellPartition S (patchSite S y a) z = 0 := by
        by_contra hne
        exact hn (Finset.mem_filter.2 ⟨hz, by
          rw [cellSupDist_symm]; exact cellSupDist_le_one_of_partition_ne_zero h ht hne⟩)
      rw [h0, zero_smul]
    rw [e]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun z hz => ?_)
    obtain ⟨hzS, -⟩ := Finset.mem_filter.1 hz
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (cellPartition_nonneg _ _)]
    have e2 : PatchDifferences.sectionNormOn S (potentialGap S V z y u) (patchSite S y a) =
        ‖potentialGap S V z y u (patchSite S y a)‖ := by
      simp [PatchDifferences.sectionNormOn, hts]
    rw [e2]
    exact mul_le_of_le_one_left (norm_nonneg _) (cellPartition_le_one _ hzS)
  have h1 := (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
  refine (mul_le_mul_of_nonneg_left h1 (by positivity)).trans (le_of_eq ?_)
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [sum_cellOffsets_patchSite h.odd_side (h.closedOrthant_cases y)
    (PatchDifferences.sectionNormOn S (potentialGap S V z y u))]
end Terms
section Cell
variable {F : BlockFrame} {S : Finset F.Cell} {V : F.GaugeField F.top} {Cs r Ch : ℝ}
  {Md Lf Sr : (F.Site 0 → ℝ) → F.Cell → ℝ} {σ : F.Cell → ℝ} {K : ℝ}
def localBound (Md Sr : (F.Site 0 → ℝ) → F.Cell → ℝ) (Cs : ℝ) (S : Finset F.Cell) (V : F.GaugeField F.top)
    (u : F.Site 0 → Fin 4 → imaginaryQuaternions) (T : F.Cell → ℝ) (z₀ : F.Cell) : ℝ :=
  ∑ x ∈ cellBall S z₀ 22, (Sr (curlNorm S V u) x + T x +
    Cs * Md (PatchDifferences.formNormOn S (toQuaternionForm u)) x)
theorem cellBall_subset_cellBall {z₀ z : F.Cell} {d a e : ℕ} (hd : cellSupDist z₀ z ≤ d) (he : d + a ≤ e) :
    cellBall S z a ⊆ cellBall S z₀ e := by
  intro x hx
  obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
  refine Finset.mem_filter.2 ⟨h1, ?_⟩
  have := cellSupDist_triangle z₀ z x
  omega
theorem localTerm_nonneg (hc : 0 ≤ Cs) (hN : CellNormFamily S Md Lf Sr σ K)
    (u : F.Site 0 → Fin 4 → imaginaryQuaternions) {T : F.Cell → ℝ} (hT0 : ∀ y, 0 ≤ T y) (x : F.Cell) :
    0 ≤ Sr (curlNorm S V u) x + T x + Cs * Md (PatchDifferences.formNormOn S (toQuaternionForm u)) x :=
  add_nonneg (add_nonneg (hN.isSeminorm_source.nonneg _ _) (hT0 x)) (mul_nonneg hc (hN.isSeminorm_base.nonneg _ _))
theorem localBound_nonneg (hc : 0 ≤ Cs) (hN : CellNormFamily S Md Lf Sr σ K)
    (u : F.Site 0 → Fin 4 → imaginaryQuaternions) {T : F.Cell → ℝ} (hT0 : ∀ y, 0 ≤ T y) (z₀ : F.Cell) :
    0 ≤ localBound Md Sr Cs S V u T z₀ :=
  Finset.sum_nonneg fun x _ => localTerm_nonneg hc hN u hT0 x
theorem nearTotal_le_localBound (hc : 0 ≤ Cs) (hN : CellNormFamily S Md Lf Sr σ K)
    (u : F.Site 0 → Fin 4 → imaginaryQuaternions) {T : F.Cell → ℝ} (hT0 : ∀ y, 0 ≤ T y) {z₀ z : F.Cell}
    (hd : cellSupDist z₀ z ≤ 2) :
    nearTotal Md Sr Cs S V u z ≤ localBound Md Sr Cs S V u T z₀ := by
  have e : nearTotal Md Sr Cs S V u z = ∑ x ∈ cellBall S z 20,
      (Sr (curlNorm S V u) x + Cs * Md (PatchDifferences.formNormOn S (toQuaternionForm u)) x) := by
    simp only [nearTotal, curlTotal, formTotal]
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  rw [e]
  calc _ ≤ ∑ x ∈ cellBall S z 20, (Sr (curlNorm S V u) x + T x +
          Cs * Md (PatchDifferences.formNormOn S (toQuaternionForm u)) x) :=
        Finset.sum_le_sum fun x _ => by linarith [hT0 x]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (cellBall_subset_cellBall hd (by norm_num))
        fun x _ _ => localTerm_nonneg hc hN u hT0 x
theorem sum_top_le_localBound (hc : 0 ≤ Cs) (hN : CellNormFamily S Md Lf Sr σ K)
    (u : F.Site 0 → Fin 4 → imaginaryQuaternions) {T : F.Cell → ℝ} (hT0 : ∀ y, 0 ≤ T y) {z₀ z : F.Cell}
    (hd : cellSupDist z₀ z ≤ 2) :
    ∑ x ∈ cellBall S z 2, T x ≤ localBound Md Sr Cs S V u T z₀ := by
  calc _ ≤ ∑ x ∈ cellBall S z 2, (Sr (curlNorm S V u) x + T x +
          Cs * Md (PatchDifferences.formNormOn S (toQuaternionForm u)) x) :=
        Finset.sum_le_sum fun x _ => by
          have := hN.isSeminorm_source.nonneg (curlNorm S V u) x
          have := mul_nonneg hc (hN.isSeminorm_base.nonneg (PatchDifferences.formNormOn S (toQuaternionForm u)) x)
          linarith
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (cellBall_subset_cellBall hd (by norm_num))
        fun x _ _ => localTerm_nonneg hc hN u hT0 x
theorem sum_cellBall_le (h : PotentialSetting S V Cs r Ch) (z : F.Cell) (d : ℕ) (f : F.Cell → ℝ) {B : ℝ}
    (hB : 0 ≤ B) (hf : ∀ x ∈ cellBall S z d, f x ≤ B) :
    ∑ x ∈ cellBall S z d, f x ≤ ((2 * d + 1) ^ 4 : ℕ) * B := by
  calc _ ≤ ∑ _x ∈ cellBall S z d, B := Finset.sum_le_sum hf
    _ = ((cellBall S z d).card : ℝ) * B := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (card_cellBall_le h.ambient z d) hB
def bondCellConstant (K Ch : ℝ) : ℝ :=
  4 * (81 * ((1 + K * 81) * defectConstant K Ch) + 625 * (weightConstant * (K * (81 * (3 * gapConstant K Ch)))) +
    81 * (cutoffConstant * (K * (K * (81 * (K * (3 * gapConstant K Ch)))))))
theorem zero_le_weightConstant : 0 ≤ weightConstant := by
  have := one_le_cutoffBound
  unfold weightConstant
  positivity
theorem bondCellConstant_nonneg (hK : 0 ≤ K) (hCh : 0 ≤ Ch) : 0 ≤ bondCellConstant K Ch := by
  have h1 := defectConstant_nonneg hK hCh
  have h2 := gapConstant_nonneg hK hCh
  have h3 := zero_le_weightConstant
  have h4 := cutoffConstant_nonneg
  unfold bondCellConstant
  positivity
theorem target_formAddGaugeDiff_le (h : PotentialSetting S V Cs r Ch) (hK : 0 ≤ K)
    (hN : CellNormFamily S Md Lf Sr σ K)
    (hFT : ∀ b ∈ S, ∀ z ∈ cellBall S b 2, ∃ g : UnitQuaternion, ∀ x ∈ cellSites S b,
      ‖((patchFrameTransition S V z b x : UnitQuaternion) : ℍ[ℝ]) - (g : ℍ[ℝ])‖ ≤ Cs)
    (u : F.Site 0 → Fin 4 → imaginaryQuaternions) {T : F.Cell → ℝ} (hT0 : ∀ y, 0 ≤ T y)
    (hT : ∀ c ∈ innerBonds S F.top,
      σ c.1 * ‖linearPart (referenceFieldChain S V) (baseOnlyChart u) F.top c.1 c.2‖ ≤ T c.1)
    (hTop : ∀ z ∈ S, ∀ c ∈ innerBonds S F.top, enclosingCell c.1 ∈ cellBall S z 10 →
      enclosingCell (c.1 + unitStep F.top c.2) ∈ cellBall S z 10 →
      ‖BlockAverages.patchFrameForm S V z (linearPart (referenceFieldChain S V) (baseOnlyChart u) F.top) c.1 c.2 -
        nestedAverage (BlockAverages.patchFrameForm S V z (toQuaternionForm u)) F.top c.1 c.2‖ ≤
      Cs * nestedAverage (fun x k => ‖toQuaternionForm u x k‖) F.top c.1 c.2) {z₀ : F.Cell} (hz₀ : z₀ ∈ S) :
    Lf (PatchDifferences.formNormOn S (formAddGaugeDiff S V u)) z₀ ≤
      bondCellConstant K Ch * localBound Md Sr Cs S V u T z₀ := by
  classical
  have hκ := h.coldnessRatio_nonneg
  have hCh := h.kernelConst_nonneg
  have hc0 := h.coldness_nonneg
  have hNp := h.cellSideLength_pos
  obtain ⟨κ, hκd⟩ : ∃ κ, κ = Cs / (cellSideLength F : ℝ) := ⟨_, rfl⟩
  rw [← hκd] at hκ
  obtain ⟨B, hB⟩ : ∃ B, B = localBound Md Sr Cs S V u T z₀ := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := hB ▸ localBound_nonneg hc0 hN u hT0 z₀
  rw [← hB]
  obtain ⟨cD, hcD⟩ : ∃ cD, cD = defectConstant K Ch := ⟨_, rfl⟩
  obtain ⟨cG, hcG⟩ : ∃ cG, cG = gapConstant K Ch := ⟨_, rfl⟩
  have hcD0 : 0 ≤ cD := hcD ▸ defectConstant_nonneg hK hCh
  have hcG0 : 0 ≤ cG := hcG ▸ gapConstant_nonneg hK hCh
  have hsh := zero_le_weightConstant
  have hbu := cutoffConstant_nonneg
  have gapB : ∀ {b z y : F.Cell}, b ∈ cellBall S z₀ 2 → z ∈ cellBall S z₀ 2 → cellSupDist z b ≤ 2 →
      y ∈ cellBall S b 2 →
      Lf (PatchDifferences.sectionNormOn S (potentialGap S V z b u)) y ≤
        (cellSideLength F : ℝ) * (cG * (3 * B)) := by
    intro b z y hb hz hd hy
    obtain ⟨hbS, hbd⟩ := Finset.mem_filter.1 hb
    obtain ⟨hzS, hzd⟩ := Finset.mem_filter.1 hz
    obtain ⟨g, hg⟩ := hFT b hbS z (Finset.mem_filter.2 ⟨hzS, by rw [cellSupDist_symm]; exact hd⟩)
    have h1 := target_sectionNormOn_potentialGap_le h hK hN hbS hzS hd u hg hT0 hT (hTop z hzS) hy
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hNp.le)
    rw [← hcG]
    refine mul_le_mul_of_nonneg_left ?_ hcG0
    have a1 := sum_top_le_localBound hc0 hN u hT0 (V := V) hzd
    have a2 := nearTotal_le_localBound (V := V) hc0 hN u hT0 hzd
    have a3 := nearTotal_le_localBound (V := V) hc0 hN u hT0 hbd
    rw [← hB] at a1 a2 a3
    linarith
  have hbox12 : ∀ {x : F.Cell}, x ∈ cellBall S z₀ 1 → x ∈ cellBall S z₀ 2 := by
    intro x hx
    obtain ⟨a, b⟩ := Finset.mem_filter.1 hx
    exact Finset.mem_filter.2 ⟨a, by omega⟩
  have hself : z₀ ∈ cellBall S z₀ 2 := Finset.mem_filter.2 ⟨hz₀, by simp [cellSupDist]⟩
  obtain ⟨A, hA⟩ : ∃ A : F.Cell → F.Site 0 → ℝ, A = fun z => defectBound κ Ch S V z u := ⟨_, rfl⟩
  have hA0 : ∀ z t, 0 ≤ A z t := fun z t => by
    rw [hA]
    exact defectBound_nonneg hκ hCh u t
  obtain ⟨G, hG⟩ : ∃ G : F.Cell → F.Site 0 → ℝ,
      G = fun z => PatchDifferences.sectionNormOn S (potentialGap S V z z₀ u) := ⟨_, rfl⟩
  have hG0 : ∀ z t, 0 ≤ G z t := fun z t => by
    rw [hG]
    exact PatchPotentials.sectionNormOn_nonneg _ t
  obtain ⟨m, hm⟩ : ∃ m : F.Cell → ℝ, m = fun y => ‖frameCellMean S V y (gluedOfForm S V u)‖ := ⟨_, rfl⟩
  have hm0 : ∀ y, 0 ≤ m y := fun y => by
    rw [hm]
    exact norm_nonneg _
  obtain ⟨c1, hc1⟩ : ∃ c1, c1 = weightConstant / (cellSideLength F : ℝ) := ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ c2, c2 = cutoffConstant / (cellSideLength F : ℝ) := ⟨_, rfl⟩
  have hc10 : 0 ≤ c1 := hc1 ▸ div_nonneg hsh hNp.le
  have hc20 : 0 ≤ c2 := hc2 ▸ div_nonneg hbu hNp.le
  obtain ⟨P, hP⟩ : ∃ P : Fin 4 → F.Site 0 → ℝ,
      P = fun i t => ∑ z ∈ cellBall S z₀ 1, (A z t + A z (t + unitStep 0 i)) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Fin 4 → F.Site 0 → ℝ,
      Q = fun i t => ∑ z ∈ cellBall S z₀ 2, c1 * G z (t + unitStep 0 i) := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : F.Site 0 → ℝ, W = fun _ => ∑ y ∈ cellBall S z₀ 1, c2 * m y * 1 := ⟨_, rfl⟩
  have hP0 : ∀ i t, 0 ≤ P i t := fun i t => by
    rw [hP]
    exact Finset.sum_nonneg fun z _ => add_nonneg (hA0 z _) (hA0 z _)
  have hQ0 : ∀ i t, 0 ≤ Q i t := fun i t => by
    rw [hQ]
    exact Finset.sum_nonneg fun z _ => mul_nonneg hc10 (hG0 z _)
  have hW0 : ∀ t, 0 ≤ W t := fun t => by
    rw [hW]
    exact Finset.sum_nonneg fun z _ => by
      have := hm0 z
      positivity
  have hpt : ∀ t ∈ cellSites S z₀, |PatchDifferences.formNormOn S (formAddGaugeDiff S V u) t| ≤
      |∑ i, (P i t + Q i t + W t)| := by
    intro t ht
    have hts : t ∈ sitesOfCells S 0 := (Finset.mem_filter.1 ht).1
    rw [abs_of_nonneg (zero_le_formNormOn _ t), abs_of_nonneg (Finset.sum_nonneg fun i _ =>
      add_nonneg (add_nonneg (hP0 i t) (hQ0 i t)) (hW0 t))]
    refine Finset.sum_le_sum fun i _ => ?_
    split_ifs with hb
    · have hs' : t + unitStep 0 i ∈ sitesOfCells S 0 := (Finset.mem_filter.1 hb).2
      rw [formAddGaugeDiff_eq h u z₀ hts hs']
      refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
      · have := norm_sum_primitiveDefect_le h u ht hs'
        rw [← hκd] at this
        rw [hP, hA]
        exact this
      · have := norm_sum_potentialGap_le h u ht hs' (referenceFieldChain S V 0 t i)
        rw [hQ, hG, hc1]
        exact this
      · have := norm_covariantDiff_cutoffPart_le h u ht hs'
        rw [hW, hm, hc2]
        simpa using this
    · exact add_nonneg (add_nonneg (hP0 i t) (hQ0 i t)) (hW0 t)
  have hshift : ∀ (i : Fin 4) (f : F.Site 0 → ℝ), (∀ x, x ∉ sitesOfCells S 0 → f x = 0) →
      Lf (fun t => f (t + unitStep 0 i)) z₀ ≤ K * ∑ y ∈ cellBall S z₀ 1, Lf f y := by
    intro i f hf
    have := hN.target_shift_le (i, true) f z₀ hf
    simpa [stepDisplacement] using this
  have bA : ∀ {z y : F.Cell}, z ∈ cellBall S z₀ 2 → cellSupDist y z ≤ 22 → Lf (A z) y ≤ cD * B := by
    intro z y hz hy
    obtain ⟨hzS, hzd⟩ := Finset.mem_filter.1 hz
    obtain ⟨R, hF⟩ := h.frames z hzS
    obtain ⟨H, Gk, hk⟩ := exists_homotopyKernels_patchDomain h hzS
    have h1 := target_defectBound_le h hF hk hK hN hzS u hy
    rw [← hκd, ← hcD] at h1
    rw [hA]
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hcD0)
    have := nearTotal_le_localBound (V := V) hc0 hN u hT0 hzd
    rw [← hB] at this
    exact this
  have hAoff : ∀ z x, x ∉ sitesOfCells S 0 → A z x = 0 := by
    intro z x hx
    rw [hA]
    exact defectBound_of_not_mem u fun h2 => hx (h.patchSiteSet_subset z h2)
  have bP : ∀ i, Lf (P i) z₀ ≤ 81 * ((1 + K * 81) * (cD * B)) := by
    intro i
    have hone : ∀ z ∈ cellBall S z₀ 1, Lf (fun t => A z t + A z (t + unitStep 0 i)) z₀ ≤
        (1 + K * 81) * (cD * B) := by
      intro z hz
      have hz2 := hbox12 hz
      have hzd := (Finset.mem_filter.1 hz).2
      refine (hN.isSeminorm_target.add_le _ _ z₀).trans ?_
      have a1 : Lf (A z) z₀ ≤ cD * B := bA hz2 (by omega)
      have a2 : Lf (fun t => A z (t + unitStep 0 i)) z₀ ≤ K * (81 * (cD * B)) := by
        refine (hshift i _ (hAoff z)).trans (mul_le_mul_of_nonneg_left ?_ hK)
        have := sum_cellBall_le h z₀ 1 (fun y => Lf (A z) y) (mul_nonneg hcD0 hB0) (fun y hy => by
          have hyd := (Finset.mem_filter.1 hy).2
          have t1 := cellSupDist_triangle y z₀ z
          rw [cellSupDist_symm y z₀] at t1
          exact bA hz2 (by omega))
        norm_num at this ⊢
        exact this
      have e : (1 + K * 81) * (cD * B) = cD * B + K * (81 * (cD * B)) := by ring
      rw [e]
      exact add_le_add a1 a2
    have h1 : Lf (P i) z₀ ≤ ∑ z ∈ cellBall S z₀ 1, Lf (fun t => A z t + A z (t + unitStep 0 i)) z₀ := by
      rw [hP]
      exact hN.isSeminorm_target.sum_le _ _ z₀
    have h2 := sum_cellBall_le h z₀ 1 (fun z => Lf (fun t => A z t + A z (t + unitStep 0 i)) z₀)
      (by positivity : 0 ≤ (1 + K * 81) * (cD * B)) hone
    norm_num at h2 ⊢
    exact h1.trans h2
  have bQ : ∀ i, Lf (Q i) z₀ ≤ 625 * (weightConstant * (K * (81 * (cG * (3 * B))))) := by
    intro i
    have hone : ∀ z ∈ cellBall S z₀ 2, Lf (fun t => c1 * G z (t + unitStep 0 i)) z₀ ≤
        weightConstant * (K * (81 * (cG * (3 * B)))) := by
      intro z hz
      have hzd := (Finset.mem_filter.1 hz).2
      rw [hN.isSeminorm_target.smul, abs_of_nonneg hc10]
      have a1 : Lf (fun t => G z (t + unitStep 0 i)) z₀ ≤
          K * (81 * ((cellSideLength F : ℝ) * (cG * (3 * B)))) := by
        refine (hshift i _ ?_).trans (mul_le_mul_of_nonneg_left ?_ hK)
        · intro x hx
          rw [hG]
          simp [PatchDifferences.sectionNormOn, hx]
        · have := sum_cellBall_le h z₀ 1 (fun y => Lf (G z) y)
            (by positivity : 0 ≤ (cellSideLength F : ℝ) * (cG * (3 * B)))
            (fun y hy => by
              rw [hG]
              exact gapB hself hz (by rw [cellSupDist_symm]; exact hzd) (by
                obtain ⟨p, q⟩ := Finset.mem_filter.1 hy
                exact Finset.mem_filter.2 ⟨p, by omega⟩))
          norm_num at this ⊢
          exact this
      refine (mul_le_mul_of_nonneg_left a1 hc10).trans (le_of_eq ?_)
      rw [hc1]
      field_simp
    have h1 : Lf (Q i) z₀ ≤ ∑ z ∈ cellBall S z₀ 2, Lf (fun t => c1 * G z (t + unitStep 0 i)) z₀ := by
      rw [hQ]
      exact hN.isSeminorm_target.sum_le _ _ z₀
    have h2 := sum_cellBall_le h z₀ 2 (fun z => Lf (fun t => c1 * G z (t + unitStep 0 i)) z₀)
      (by positivity : 0 ≤ weightConstant * (K * (81 * (cG * (3 * B))))) hone
    norm_num at h2 ⊢
    exact h1.trans h2
  have bM : ∀ y ∈ cellBall S z₀ 1, σ y * m y ≤ 81 * (K * (cG * (3 * B))) := by
    intro y hy
    obtain ⟨hyS, hyd⟩ := Finset.mem_filter.1 hy
    have hy2 := hbox12 hy
    have hm1 := norm_frameCellMean_gluedOfForm_le' h u hyS
    have hmy : m y = ‖frameCellMean S V y (gluedOfForm S V u)‖ := by rw [hm]
    rw [← hmy] at hm1
    have hσ := (hN.scale_pos y).le
    refine (mul_le_mul_of_nonneg_left hm1 hσ).trans ?_
    rw [Finset.mul_sum]
    have hone : ∀ z ∈ cellBall S y 1, σ y * ((1 / (cellSideLength F : ℝ) ^ 4) *
        ∑ c ∈ centredCube (F.blockSide ^ F.top),
          PatchDifferences.sectionNormOn S (potentialGap S V z y u) (cellCentre 0 y + siteOfCoords 0 c)) ≤
        K * (cG * (3 * B)) := by
      intro z hz
      obtain ⟨hzS, hzd⟩ := Finset.mem_filter.1 hz
      have hz2 : z ∈ cellBall S z₀ 2 := by
        refine Finset.mem_filter.2 ⟨hzS, ?_⟩
        have := cellSupDist_triangle z₀ y z
        omega
      have a1 := scale_mul_cellMean_le hN h.ambient h.odd_side hyS
        (PatchDifferences.sectionNormOn S (potentialGap S V z y u)) (PatchPotentials.sectionNormOn_nonneg _)
      refine a1.trans ?_
      rw [div_le_iff₀ hNp]
      have a2 := (hN.base_le_target (PatchDifferences.sectionNormOn S (potentialGap S V z y u)) y).trans
        (gapB hy2 hz2 (by rw [cellSupDist_symm]; omega) (Finset.mem_filter.2 ⟨hyS, by simp [cellSupDist]⟩))
      refine (mul_le_mul_of_nonneg_left a2 hK).trans (le_of_eq ?_)
      ring
    have h2 := sum_cellBall_le h y 1 (fun z => σ y * ((1 / (cellSideLength F : ℝ) ^ 4) *
        ∑ c ∈ centredCube (F.blockSide ^ F.top),
          PatchDifferences.sectionNormOn S (potentialGap S V z y u) (cellCentre 0 y + siteOfCoords 0 c)))
      (by positivity : 0 ≤ K * (cG * (3 * B))) hone
    norm_num at h2 ⊢
    exact h2
  have bW : Lf W z₀ ≤ 81 * (cutoffConstant * (K * (K * (81 * (K * (cG * (3 * B))))))) := by
    have hone : ∀ y ∈ cellBall S z₀ 1, Lf (fun _ => c2 * m y * 1) z₀ ≤
        cutoffConstant * (K * (K * (81 * (K * (cG * (3 * B)))))) := by
      intro y hy
      obtain ⟨hyS, hyd⟩ := Finset.mem_filter.1 hy
      have hmy := hm0 y
      rw [hN.isSeminorm_target.smul, abs_of_nonneg (by positivity)]
      have a1 : Lf (fun _ => 1) z₀ ≤ K * (cellSideLength F : ℝ) * σ z₀ := hN.const_le z₀
      have a2 : σ z₀ ≤ K * σ y := hN.scale_le_of_near z₀ y (by omega)
      have a3 := mul_le_mul_of_nonneg_left a2 (by positivity : 0 ≤ K * (cellSideLength F : ℝ))
      have a4 := mul_le_mul_of_nonneg_left (a1.trans a3) (by positivity : 0 ≤ c2 * m y)
      refine a4.trans ?_
      have e : c2 * m y * (K * (cellSideLength F : ℝ) * (K * σ y)) =
          cutoffConstant * (K * (K * (σ y * m y))) := by
        rw [hc2]
        field_simp
      rw [e]
      refine mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (bM y hy) hK) hK) hbu
    have h1 : Lf W z₀ ≤ ∑ y ∈ cellBall S z₀ 1, Lf (fun _ => c2 * m y * 1) z₀ := by
      rw [hW]
      exact hN.isSeminorm_target.sum_le _ _ z₀
    have h2 := sum_cellBall_le h z₀ 1 (fun y => Lf (fun _ => c2 * m y * 1) z₀)
      (by positivity : 0 ≤ cutoffConstant * (K * (K * (81 * (K * (cG * (3 * B))))))) hone
    exact h1.trans (h2.trans (le_of_eq (by norm_num)))
  have hstart : Lf (PatchDifferences.formNormOn S (formAddGaugeDiff S V u)) z₀ ≤
      ∑ i : Fin 4, Lf (fun t => P i t + Q i t + W t) z₀ :=
    (hN.isSeminorm_target.mono_abs _ _ _ hpt).trans (hN.isSeminorm_target.sum_le _ _ z₀)
  have hper : ∀ i : Fin 4, Lf (fun t => P i t + Q i t + W t) z₀ ≤ 81 * ((1 + K * 81) * (cD * B)) +
      625 * (weightConstant * (K * (81 * (cG * (3 * B))))) +
      81 * (cutoffConstant * (K * (K * (81 * (K * (cG * (3 * B))))))) := fun i =>
    (hN.isSeminorm_target.add_le _ _ z₀).trans
      (add_le_add ((hN.isSeminorm_target.add_le _ _ z₀).trans (add_le_add (bP i) (bQ i))) bW)
  refine hstart.trans ((Finset.sum_le_sum fun i _ => hper i).trans (le_of_eq ?_))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold bondCellConstant
  rw [← hcD, ← hcG]
  push_cast
  ring
end Cell
end YangMills.Construction.BondGauge
end
