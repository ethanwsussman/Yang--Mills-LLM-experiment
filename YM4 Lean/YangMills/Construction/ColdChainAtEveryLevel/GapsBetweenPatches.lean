import YangMills.Construction.ColdChainAtEveryLevel.FramesOfTwoPatches
import YangMills.Construction.ColdChainAtEveryLevel.MeansOfAPotential
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.PatchGaps
open BlockAverages GaugeMap PatchPoints LatticeFractionalIntegration PatchPotentials PotentialMeans BondShares PatchFrames
section Near
variable {F : BlockFrame} {S : Finset F.Cell} {z : F.Cell}
def nearCorners (S : Finset F.Cell) (z : F.Cell) : Finset Lattice4 :=
  (cellBall S z 2).image fun y i => closedOrthant S z i * cellDisplacement z y i * cellSideLength F
open Classical in
def nearPatch (S : Finset F.Cell) (z : F.Cell) : Finset Lattice4 :=
  (Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(2 * cellSideLength F)) (6 * cellSideLength F - 1)).filter
    fun x => ∃ a ∈ nearCorners S z, ∀ i, a i ≤ x i
theorem nearPatch_subset_patchDomain (hL : 0 < F.blockSide) : nearPatch S z ⊆ patchDomain S z := by
  classical
  intro x hx
  obtain ⟨h1, a, ha, hax⟩ := Finset.mem_filter.1 hx
  refine Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun i => ?_, a, ?_, hax⟩
  · have := Finset.mem_Icc.1 (Fintype.mem_piFinset.1 h1 i)
    rw [Finset.mem_Icc]
    constructor <;> omega
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨hy1, hy2⟩ := Finset.mem_filter.1 hy
    exact Finset.mem_image.2 ⟨y, Finset.mem_filter.2 ⟨hy1, by omega⟩, rfl⟩
theorem nearCorner_le (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) (hL : 0 < F.blockSide)
    {y : F.Cell} (hd : cellSupDist z y ≤ 2) (i : Fin 4) :
    closedOrthant S z i * cellDisplacement z y i * cellSideLength F ≤ 2 * cellSideLength F := by
  have hN := cellSideLength_pos (F := F) hL
  have h2 := natAbs_valMinAbs_le_cellSupDist y z i
  rw [cellSupDist_symm] at h2
  have h3 : (cellDisplacement z y i).natAbs ≤ 2 := h2.trans hd
  have h4 : |closedOrthant S z i * cellDisplacement z y i| ≤ 2 := by
    rw [abs_mul, abs_closedOrthant he, one_mul, Int.abs_eq_natAbs]
    exact_mod_cast h3
  exact mul_le_mul_of_nonneg_right (abs_le.1 h4).2 hN.le
theorem natCast_three_mul_toNat (hL : 0 < F.blockSide) :
    ((3 * (cellSideLength F).toNat : ℕ) : ℤ) = 3 * cellSideLength F := by
  have := cellSideLength_pos (F := F) hL
  push_cast
  rw [Int.toNat_of_nonneg this.le]
theorem nearPatch_isFilledToward (hz : z ∈ S) (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (hL : 0 < F.blockSide) :
    IsFilledToward (3 * (cellSideLength F).toNat) (fun _ => 3 * cellSideLength F) (nearPatch S z) := by
  classical
  have hN := cellSideLength_pos (F := F) hL
  have hc3 := natCast_three_mul_toNat (F := F) hL
  have hself : (fun i => closedOrthant S z i * cellDisplacement z z i * cellSideLength F) ∈ nearCorners S z := by
    refine Finset.mem_image.2 ⟨z, Finset.mem_filter.2 ⟨hz, ?_⟩, rfl⟩
    simp [cellSupDist]
  have hzero : ∀ i, closedOrthant S z i * cellDisplacement z z i * cellSideLength F = 0 := by
    intro i
    simp [cellDisplacement]
  refine ⟨fun q hq => ?_, fun x hx i => ?_, fun x hx q hq y hy => ?_⟩
  · have hqi : ∀ i, 3 * cellSideLength F ≤ q i ∧
        q i < 3 * cellSideLength F + ((3 * (cellSideLength F).toNat : ℕ) : ℤ) :=
      fun i => Finset.mem_Ico.1 (Fintype.mem_piFinset.1 hq i)
    refine Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun i => ?_, ⟨_, hself, fun i => ?_⟩⟩
    · have := hqi i
      rw [hc3] at this
      rw [Finset.mem_Icc]
      constructor <;> omega
    · have := hqi i
      rw [hc3] at this
      rw [hzero]
      omega
  · have h1 := Finset.mem_Icc.1 (Fintype.mem_piFinset.1 (Finset.mem_filter.1 hx).1 i)
    rw [hc3, abs_le]
    show -(40 * (3 * cellSideLength F)) ≤ x i - 3 * cellSideLength F ∧
      x i - 3 * cellSideLength F ≤ 40 * (3 * cellSideLength F)
    constructor <;> omega
  · obtain ⟨h0, a, ha, hxa⟩ := Finset.mem_filter.1 hx
    obtain ⟨y0, hy0, rfl⟩ := Finset.mem_image.1 ha
    have hy0d := (Finset.mem_filter.1 hy0).2
    have hqi : ∀ i, 3 * cellSideLength F ≤ q i ∧
        q i < 3 * cellSideLength F + ((3 * (cellSideLength F).toNat : ℕ) : ℤ) :=
      fun i => Finset.mem_Ico.1 (Fintype.mem_piFinset.1 hq i)
    refine Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun i => ?_,
      ⟨_, Finset.mem_image_of_mem _ hy0, fun i => ?_⟩⟩
    · have h1 := Finset.mem_Icc.1 (Fintype.mem_piFinset.1 h0 i)
      have h2 := hqi i
      rw [hc3] at h2
      have h3 := hy i
      rw [Finset.mem_Icc]
      have h4 := min_le_iff.1 (le_refl (min (x i) (q i)))
      have h5 := le_max_iff.1 (le_refl (max (x i) (q i)))
      constructor
      · rcases h4 with h4 | h4 <;> omega
      · rcases h5 with h5 | h5 <;> omega
    · have h1 := hxa i
      have h2 := hqi i
      rw [hc3] at h2
      have h3 := hy i
      have h4 := nearCorner_le he hL hy0d i
      have h5 : closedOrthant S z i * cellDisplacement z y0 i * cellSideLength F ≤ min (x i) (q i) :=
        le_min h1 (by omega)
      exact h5.trans h3.1
variable {V : F.GaugeField F.top} {Cs r Ch : ℝ}
theorem exists_cell_of_mem_nearPatch (h : PotentialSetting S V Cs r Ch) {a : Lattice4} (ha : a ∈ nearPatch S z) :
    ∃ y ∈ S, cellSupDist z y ≤ 6 ∧ patchSite S z a ∈ cellSites S y := by
  classical
  obtain ⟨m, hm, hreg⟩ := h.regular
  have hL := h.odd_side.pos
  obtain ⟨hc0, hc1⟩ := cellSideLength_half (F := F) h.odd_side
  have he := h.closedOrthant_cases z
  obtain ⟨y, g, hy, -, hg, e⟩ :=
    exists_cell_of_mem_patchDomain h.ambient h.odd_side hreg hm (nearPatch_subset_patchDomain hL ha)
  have hr : ∀ i, -(2 * cellSideLength F) ≤ a i ∧ a i ≤ 6 * cellSideLength F - 1 := fun i =>
    Finset.mem_Icc.1 (Fintype.mem_piFinset.1 (Finset.mem_filter.1 ha).1 i)
  refine ⟨y, hy, ?_, ?_⟩
  · have hc : enclosingCell (patchSite S z a) = y := by
      rw [e]
      exact LocalPartition.enclosingCell_cellCentre_add h.odd_side y g hg
    rw [cellSupDist_symm, ← hc]
    refine cellSupDist_enclosingCell_le h.odd_side _ z 6 fun i => ?_
    have e1 : (patchSite S z a - cellCentre 0 z) i =
        ((closedOrthant S z i * (a i - (cellSideLength F - 1) / 2) : ℤ) : ZMod (F.period 0 i)) := by
      simp [patchSite, siteOfCoords]
    have h6 : |closedOrthant S z i * (a i - (cellSideLength F - 1) / 2)| ≤ 6 * cellSideLength F := by
      rw [abs_mul, abs_closedOrthant he, one_mul, abs_le]
      have := hr i
      constructor <;> omega
    have hb : |closedOrthant S z i * (a i - (cellSideLength F - 1) / 2)| < 32 * cellSideLength F := by omega
    rw [e1, valMinAbs_of_abs_lt h.ambient hL i hb]
    have hs : cellSideLength F = ((F.blockSide ^ F.top : ℕ) : ℤ) := by simp [cellSideLength]
    rw [hs, Int.abs_eq_natAbs] at h6
    exact_mod_cast h6
  · rw [e]
    exact mem_cellSites_of_centredCube h.odd_side hy hg
theorem patchChart_mem_nearPatch (h : PotentialSetting S V Cs r Ch) {y : F.Cell} (hy : y ∈ cellBall S z 2)
    {t : F.Site 0} (ht : t ∈ cellSites S y) :
    patchChart S z t ∈ nearPatch S z := by
  classical
  have hL := h.odd_side.pos
  have hN := cellSideLength_pos (F := F) hL
  obtain ⟨hc0, hc1⟩ := cellSideLength_half (F := F) h.odd_side
  have he := h.closedOrthant_cases z
  obtain ⟨hyS, hd⟩ := Finset.mem_filter.1 hy
  obtain ⟨y', hy', g, hg, e⟩ := mem_sitesOfCells.1 (Finset.mem_filter.1 ht).1
  have hg' : g ∈ centredCube (F.blockSide ^ F.top) := by simpa using hg
  have hc : enclosingCell t = y' := by
    rw [e]
    exact LocalPartition.enclosingCell_cellCentre_add h.odd_side y' g hg'
  have hyy : y' = y := by rw [← hc]; exact (Finset.mem_filter.1 ht).2
  subst hyy
  have hgb := (mem_centredCube_iff g).1 hg'
  have hoffb : ∀ i, |cellDisplacement z y' i| ≤ 2 := by
    intro i
    have h2 := natAbs_valMinAbs_le_cellSupDist y' z i
    rw [cellSupDist_symm] at h2
    have h3 : (cellDisplacement z y' i).natAbs ≤ 2 := h2.trans hd
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h3
  have hcen : cellCentre (F := F) 0 y' =
      cellCentre 0 z + siteOfCoords 0 (fun i => cellSideLength F * cellDisplacement z y' i) := by
    conv_lhs => rw [eq_add_siteOfCoords_cellDisplacement z y']
    rw [cellCentre_add 0 (Nat.zero_le _)]
    rfl
  have hval : ∀ i, ((t - cellCentre 0 z) i).valMinAbs = cellSideLength F * cellDisplacement z y' i + g i := by
    intro i
    have e1 : (t - cellCentre 0 z) i =
        ((cellSideLength F * cellDisplacement z y' i + g i : ℤ) : ZMod (F.period 0 i)) := by
      rw [e, hcen]
      simp [siteOfCoords]
      ring
    rw [e1]
    refine valMinAbs_of_abs_lt h.ambient hL i ?_
    have h1 := abs_le.1 (hoffb i)
    have h2 := hgb i
    have h3 : cellSideLength F * cellDisplacement z y' i ≤ 2 * cellSideLength F := by nlinarith
    have h4 : -(2 * cellSideLength F) ≤ cellSideLength F * cellDisplacement z y' i := by nlinarith
    rw [abs_lt]
    constructor <;> omega
  have hx : ∀ i, patchChart S z t i =
      closedOrthant S z i * (cellSideLength F * cellDisplacement z y' i + g i) + (cellSideLength F - 1) / 2 := by
    intro i
    simp only [patchChart, hval]
  refine Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun i => ?_, _,
    Finset.mem_image_of_mem _ hy, fun i => ?_⟩
  · rw [hx, Finset.mem_Icc]
    have h1 := abs_le.1 (hoffb i)
    have h2 := hgb i
    have h3 : cellSideLength F * cellDisplacement z y' i ≤ 2 * cellSideLength F := by nlinarith
    have h4 : -(2 * cellSideLength F) ≤ cellSideLength F * cellDisplacement z y' i := by nlinarith
    obtain ⟨w, hw⟩ : ∃ w, w = cellSideLength F * cellDisplacement z y' i := ⟨_, rfl⟩
    rw [← hw] at h3 h4 ⊢
    rcases he i with hs | hs <;> rw [hs] <;> constructor <;> omega
  · show closedOrthant S z i * cellDisplacement z y' i * cellSideLength F ≤ patchChart S z t i
    rw [hx]
    have h2 := hgb i
    have e2 : closedOrthant S z i * cellDisplacement z y' i * cellSideLength F =
        closedOrthant S z i * (cellSideLength F * cellDisplacement z y' i) := by ring
    rw [e2]
    obtain ⟨w, hw⟩ : ∃ w, w = cellSideLength F * cellDisplacement z y' i := ⟨_, rfl⟩
    rw [← hw]
    rcases he i with hs | hs <;> rw [hs] <;> omega
theorem mem_nearPatch_of_mem_cellOffsets (h : PotentialSetting S V Cs r Ch) (hz : z ∈ S) {a : Lattice4}
    (ha : a ∈ cellOffsets F) : a ∈ nearPatch S z := by
  classical
  have hN := cellSideLength_pos (F := F) h.odd_side.pos
  have hxi := fun i => Finset.mem_Ico.1 (Fintype.mem_piFinset.1 ha i)
  have hself : (fun i => closedOrthant S z i * cellDisplacement z z i * cellSideLength F) ∈ nearCorners S z := by
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
end Near
section Gap
variable {F : BlockFrame} {S : Finset F.Cell} {V : F.GaugeField F.top} {z b : F.Cell} {Cs r Ch : ℝ}
  {Md Lf Sr : (F.Site 0 → ℝ) → F.Cell → ℝ} {σ : F.Cell → ℝ} {K : ℝ}
theorem exists_homotopyKernels_patchDomain (h : PotentialSetting S V Cs r Ch) (hz : z ∈ S) :
    ∃ H Gk, HomotopyKernels (9 * (cellSideLength F).toNat) (fun _ => 12 * cellSideLength F)
      (patchDomain S z) H Gk Ch := by
  have hL := h.odd_side.pos
  have hN := cellSideLength_pos (F := F) hL
  refine h.homotopy _ _ _ ?_ (patchDomain_isFilledToward hz (h.closedOrthant_cases z) hL)
  have : 1 ≤ (cellSideLength F).toNat := by omega
  omega
theorem exists_homotopyKernels_nearPatch (h : PotentialSetting S V Cs r Ch) (hz : z ∈ S) :
    ∃ H Gk, HomotopyKernels (3 * (cellSideLength F).toNat) (fun _ => 3 * cellSideLength F)
      (nearPatch S z) H Gk Ch := by
  have hL := h.odd_side.pos
  have hN := cellSideLength_pos (F := F) hL
  refine h.homotopy _ _ _ ?_ (nearPatch_isFilledToward hz (h.closedOrthant_cases z) hL)
  have : 1 ≤ (cellSideLength F).toNat := by omega
  omega
def potentialGap (S : Finset F.Cell) (V : F.GaugeField F.top) (z b : F.Cell)
    (u : F.Site 0 → Fin 4 → imaginaryQuaternions) (t : F.Site 0) : ℍ[ℝ] :=
  potentialSection S V z u t - potentialSection S V b u t
def gapSource (κ Ch : ℝ) (S : Finset F.Cell) (V : F.GaugeField F.top) (z b : F.Cell)
    (u : F.Site 0 → Fin 4 → imaginaryQuaternions) (t : F.Site 0) : ℝ :=
  defectBound κ Ch S V z u t + defectBound κ Ch S V b u t +
    2 * κ * (potentialNorm S V z u t + potentialNorm S V b u t)
theorem gapSource_nonneg {κ : ℝ} (hκ : 0 ≤ κ) (hCh : 0 ≤ Ch) (u : F.Site 0 → Fin 4 → imaginaryQuaternions)
    (t : F.Site 0) : 0 ≤ gapSource κ Ch S V z b u t :=
  add_nonneg (add_nonneg (defectBound_nonneg hκ hCh u t) (defectBound_nonneg hκ hCh u t))
    (mul_nonneg (by positivity) (add_nonneg (potentialNorm_nonneg u t) (potentialNorm_nonneg u t)))
theorem covariantDiff_potentialGap (u : F.Site 0 → Fin 4 → imaginaryQuaternions) (t : F.Site 0) (i : Fin 4) :
    covariantDiff (referenceFieldChain S V 0) (potentialGap S V z b u) t i =
      primitiveDefect S V z u t i - primitiveDefect S V b u t i := by
  simp only [primitiveDefect, covariantDiff, potentialGap, PatchForms.adjointAction_apply_sub]
  abel
theorem patchSite_mem_patchSiteSet_of_nearPatch (h : PotentialSetting S V Cs r Ch) (hd : cellSupDist z b ≤ 2)
    {a : Lattice4} (ha : a ∈ nearPatch S b) :
    patchSite S b a ∈ patchSiteSet S z := by
  obtain ⟨y, hy, h5, ht⟩ := exists_cell_of_mem_nearPatch h ha
  refine h.mem_patchSiteSet_of_cellSupDist_le hy ?_ ht
  have := cellSupDist_triangle z b y
  omega
theorem norm_localSection_potentialGap_step_le {R R' : Lattice4 → Lattice4 → UnitQuaternion}
    (h : PotentialSetting S V Cs r Ch) (hFb : IsPatchFrame S V b R Cs r) (hFz : IsPatchFrame S V z R' Cs r)
    {H H' : Lattice4 × Fin 4 → Lattice4 × Fin 4 × Fin 4 → ℝ} {Gk Gk' : Lattice4 → Lattice4 × Fin 4 → ℝ}
    (hkb : HomotopyKernels (9 * (cellSideLength F).toNat) (fun _ => 12 * cellSideLength F) (patchDomain S b) H Gk Ch)
    (hkz : HomotopyKernels (9 * (cellSideLength F).toNat) (fun _ => 12 * cellSideLength F) (patchDomain S z) H' Gk' Ch)
    (hd : cellSupDist z b ≤ 2) (u : F.Site 0 → Fin 4 → imaginaryQuaternions) {a : Lattice4} {i : Fin 4}
    (ha : a ∈ nearPatch S b) (ha' : a + basisVector i ∈ nearPatch S b) :
    ‖PatchDifferences.localSection S V b (potentialGap S V z b u) (a + basisVector i) -
        PatchDifferences.localSection S V b (potentialGap S V z b u) a‖ ≤
      gapSource (Cs / (cellSideLength F : ℝ)) Ch S V z b u (patchSite S b a) +
        gapSource (Cs / (cellSideLength F : ℝ)) Ch S V z b u (patchSite S b (a + basisVector i)) := by
  classical
  have hL := h.odd_side.pos
  have hκ := h.coldnessRatio_nonneg
  have he := h.closedOrthant_cases b
  have ha0 := nearPatch_subset_patchDomain hL ha
  have ha0' := nearPatch_subset_patchDomain hL ha'
  have tb : patchSite S b a ∈ patchSiteSet S b := Finset.mem_image_of_mem _ ha0
  have tb' : patchSite S b (a + basisVector i) ∈ patchSiteSet S b := Finset.mem_image_of_mem _ ha0'
  have tz := patchSite_mem_patchSiteSet_of_nearPatch h hd ha
  have tz' := patchSite_mem_patchSiteSet_of_nearPatch h hd ha'
  obtain ⟨κ, hκd⟩ : ∃ κ, κ = Cs / (cellSideLength F : ℝ) := ⟨_, rfl⟩
  rw [← hκd] at hκ ⊢
  obtain ⟨t0, ht0⟩ : ∃ t0, t0 = patchSite S b a := ⟨_, rfl⟩
  obtain ⟨t1, ht1⟩ : ∃ t1, t1 = patchSite S b (a + basisVector i) := ⟨_, rfl⟩
  have e := localForm_covariantDiff hFb h.scale he (potentialGap S V z b u) ha0 ha0'
  have e2 : PatchDifferences.localSection S V b (potentialGap S V z b u) (a + basisVector i) -
        PatchDifferences.localSection S V b (potentialGap S V z b u) a =
      localForm S V (referenceFieldChain S V 0) b
          (covariantDiff (referenceFieldChain S V 0) (potentialGap S V z b u)) a i -
        frameRemainder R S V b (potentialGap S V z b u) a i := by
    rw [e]
    simp only [latticeDifference]
    abel
  rw [e2]
  refine (norm_sub_le _ _).trans ?_
  have hr := norm_frameRemainder_le hFb h.scale (potentialGap S V z b u) ha0 ha0'
  have hg : ‖potentialGap S V z b u t1‖ ≤ potentialNorm S V z u t1 + potentialNorm S V b u t1 := by
    rw [ht1, ← norm_potentialSection u tz', ← norm_potentialSection u tb']
    exact norm_sub_le _ _
  have hr2 : ‖frameRemainder R S V b (potentialGap S V z b u) a i‖ ≤
      2 * κ * (potentialNorm S V z u t1 + potentialNorm S V b u t1) := by
    rw [← hκd, ← ht1] at hr
    exact hr.trans (mul_le_mul_of_nonneg_left hg (by positivity))
  have hbond : ‖localForm S V (referenceFieldChain S V 0) b
      (covariantDiff (referenceFieldChain S V 0) (potentialGap S V z b u)) a i‖ ≤
      defectBound κ Ch S V z u t0 + defectBound κ Ch S V z u t1 +
        (defectBound κ Ch S V b u t0 + defectBound κ Ch S V b u t1) := by
    obtain ⟨k1, k2⟩ := PatchForms.patchSite_add_basisVector_cases he a i
    obtain ⟨Hb, Gb, hb2⟩ : ∃ Hb Gb, HomotopyKernels (9 * (cellSideLength F).toNat)
        (fun _ => 12 * cellSideLength F) (patchDomain S b) Hb Gb Ch :=
      ⟨_, _, hkb⟩
    rcases he i with hs | hs
    · rw [norm_localForm_of_sign_pos hs, covariantDiff_potentialGap]
      refine (norm_sub_le _ _).trans ?_
      have e1 := k1 hs
      have d1 := norm_primitiveDefect_le h hFz hkz u tz (e1 ▸ tz')
      have d2 := norm_primitiveDefect_le h hFb hkb u tb (e1 ▸ tb')
      rw [← e1, ← hκd, ← ht0, ← ht1] at d1 d2
      rw [← ht0]
      exact add_le_add d1 d2
    · rw [norm_localForm_of_sign_neg hs, covariantDiff_potentialGap]
      refine (norm_sub_le _ _).trans ?_
      have e1 := k2 hs
      have d1 := norm_primitiveDefect_le h hFz hkz u tz' (e1 ▸ tz)
      have d2 := norm_primitiveDefect_le h hFb hkb u tb' (e1 ▸ tb)
      rw [← e1, ← hκd, ← ht0, ← ht1] at d1 d2
      rw [← ht1]
      linarith
  have p0 := potentialNorm_nonneg (S := S) (V := V) (z := z) u t0
  have p1 := potentialNorm_nonneg (S := S) (V := V) (z := b) u t0
  have q : 0 ≤ 2 * κ * (potentialNorm S V z u t0 + potentialNorm S V b u t0) :=
    mul_nonneg (by positivity) (add_nonneg p0 p1)
  rw [← ht0, ← ht1]
  simp only [gapSource]
  linarith
def framedGap (S : Finset F.Cell) (V : F.GaugeField F.top) (z b : F.Cell)
    (u : F.Site 0 → Fin 4 → imaginaryQuaternions) : Lattice4 → ℍ[ℝ] :=
  PatchDifferences.localSection S V b (potentialGap S V z b u)
theorem stepNorms_framedGap_le {R R' : Lattice4 → Lattice4 → UnitQuaternion} (h : PotentialSetting S V Cs r Ch)
    (hFb : IsPatchFrame S V b R Cs r) (hFz : IsPatchFrame S V z R' Cs r)
    {H H' : Lattice4 × Fin 4 → Lattice4 × Fin 4 × Fin 4 → ℝ} {Gk Gk' : Lattice4 → Lattice4 × Fin 4 → ℝ}
    (hkb : HomotopyKernels (9 * (cellSideLength F).toNat) (fun _ => 12 * cellSideLength F) (patchDomain S b) H Gk Ch)
    (hkz : HomotopyKernels (9 * (cellSideLength F).toNat) (fun _ => 12 * cellSideLength F) (patchDomain S z) H' Gk' Ch)
    (hd : cellSupDist z b ≤ 2) (u : F.Site 0 → Fin 4 → imaginaryQuaternions) (t : F.Site 0) :
    stepNorms (nearPatch S b) S b (framedGap S V z b u) t ≤
      8 * neighbourSum S b (gapSource (Cs / (cellSideLength F : ℝ)) Ch S V z b u) t := by
  classical
  have hL := h.odd_side.pos
  have hκ := h.coldnessRatio_nonneg
  have hCh := h.kernelConst_nonneg
  have hg0 : ∀ t, 0 ≤ gapSource (Cs / (cellSideLength F : ℝ)) Ch S V z b u t := gapSource_nonneg hκ hCh u
  have hnb := neighbourSum_nonneg (S := S) (z := b) hg0 t
  by_cases ht : t ∈ patchSiteSet S b
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 ht
    rw [stepNorms_patchSite h _ _ ha]
    have hone : ∀ i : Fin 4, (if a ∈ nearPatch S b ∧ a + basisVector i ∈ nearPatch S b then
        ‖framedGap S V z b u (a + basisVector i) - framedGap S V z b u a‖ else 0) ≤
        2 * neighbourSum S b (gapSource (Cs / (cellSideLength F : ℝ)) Ch S V z b u) (patchSite S b a) := by
      intro i
      split_ifs with hc
      · have h1 := norm_localSection_potentialGap_step_le h hFb hFz hkb hkz hd u hc.1 hc.2
        have h2 := (le_neighbourSum_of_bond hg0 (h.closedOrthant_cases b) ha
          (nearPatch_subset_patchDomain hL hc.2)).1
        have h3 := le_neighbourSum_self hg0 ht
        simp only [framedGap]
        linarith
      · exact mul_nonneg (by norm_num) hnb
    calc _ ≤ ∑ _i : Fin 4, 2 * neighbourSum S b (gapSource (Cs / (cellSideLength F : ℝ)) Ch S V z b u)
            (patchSite S b a) :=
          Finset.sum_le_sum fun i _ => hone i
      _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  · rw [stepNorms_of_not_mem _ _ ht]
    exact mul_nonneg (by norm_num) hnb
def nearTotal (Md Sr : (F.Site 0 → ℝ) → F.Cell → ℝ) (Cs : ℝ) (S : Finset F.Cell) (V : F.GaugeField F.top)
    (u : F.Site 0 → Fin 4 → imaginaryQuaternions) (z : F.Cell) : ℝ :=
  curlTotal Sr S V u z + Cs * formTotal Md S u z
theorem nearTotal_nonneg (hc : 0 ≤ Cs) (hN : CellNormFamily S Md Lf Sr σ K)
    (u : F.Site 0 → Fin 4 → imaginaryQuaternions) (z : F.Cell) :
    0 ≤ nearTotal Md Sr Cs S V u z :=
  add_nonneg (curlTotal_nonneg hN u z) (mul_nonneg hc (formTotal_nonneg hN u z))
theorem coldness_mul_potentialNorm_le {R : Lattice4 → Lattice4 → UnitQuaternion} (h : PotentialSetting S V Cs r Ch)
    (hF : IsPatchFrame S V z R Cs r)
    {H : Lattice4 × Fin 4 → Lattice4 × Fin 4 × Fin 4 → ℝ} {Gk : Lattice4 → Lattice4 × Fin 4 → ℝ}
    (hk : HomotopyKernels (9 * (cellSideLength F).toNat) (fun _ => 12 * cellSideLength F) (patchDomain S z) H Gk Ch)
    (hK : 0 ≤ K) (hN : CellNormFamily S Md Lf Sr σ K) (hz : z ∈ S) (u : F.Site 0 → Fin 4 → imaginaryQuaternions)
    {y : F.Cell} (hy : cellSupDist y z ≤ 22) :
    Cs / (cellSideLength F : ℝ) * Lf (potentialNorm S V z u) y ≤
      potentialConstant K Ch * nearTotal Md Sr Cs S V u z := by
  have hNp := h.cellSideLength_pos
  have hc0 := h.coldness_nonneg
  have hc1 := h.coldness_le_one
  have hp := potentialConstant_nonneg hK h.kernelConst_nonneg
  have h1 := target_potentialNorm_le h hF hk hK hN hz u hy
  have hM1 := curlTotal_nonneg (V := V) hN u z
  have h2 := mul_le_mul_of_nonneg_left h1 (div_nonneg hc0 hNp.le)
  refine h2.trans ?_
  have e : Cs / (cellSideLength F : ℝ) * ((cellSideLength F : ℝ) *
      (potentialConstant K Ch * (curlTotal Sr S V u z + formTotal Md S u z))) =
      potentialConstant K Ch * (Cs * curlTotal Sr S V u z + Cs * formTotal Md S u z) := by
    field_simp
  rw [e, nearTotal]
  refine mul_le_mul_of_nonneg_left ?_ hp
  have := mul_le_of_le_one_left hM1 hc1
  linarith
def gapSourceConstant (K Ch : ℝ) : ℝ := defectConstant K Ch + 2 * potentialConstant K Ch
theorem gapSourceConstant_nonneg (hK : 0 ≤ K) (hCh : 0 ≤ Ch) : 0 ≤ gapSourceConstant K Ch := by
  have h1 := defectConstant_nonneg hK hCh
  have h2 := potentialConstant_nonneg hK hCh
  unfold gapSourceConstant
  positivity
theorem base_gapSource_le {R R' : Lattice4 → Lattice4 → UnitQuaternion} (h : PotentialSetting S V Cs r Ch)
    (hFb : IsPatchFrame S V b R Cs r) (hFz : IsPatchFrame S V z R' Cs r)
    {H H' : Lattice4 × Fin 4 → Lattice4 × Fin 4 × Fin 4 → ℝ} {Gk Gk' : Lattice4 → Lattice4 × Fin 4 → ℝ}
    (hkb : HomotopyKernels (9 * (cellSideLength F).toNat) (fun _ => 12 * cellSideLength F) (patchDomain S b) H Gk Ch)
    (hkz : HomotopyKernels (9 * (cellSideLength F).toNat) (fun _ => 12 * cellSideLength F) (patchDomain S z) H' Gk' Ch)
    (hK : 0 ≤ K) (hN : CellNormFamily S Md Lf Sr σ K) (hb : b ∈ S) (hz : z ∈ S)
    (u : F.Site 0 → Fin 4 → imaginaryQuaternions) {x : F.Cell}
    (hxb : cellSupDist x b ≤ 22) (hxz : cellSupDist x z ≤ 22) :
    Md (gapSource (Cs / (cellSideLength F : ℝ)) Ch S V z b u) x ≤
      gapSourceConstant K Ch * (nearTotal Md Sr Cs S V u z + nearTotal Md Sr Cs S V u b) := by
  have hκ := h.coldnessRatio_nonneg
  have a1 := (hN.base_le_target _ x).trans (target_defectBound_le h hFz hkz hK hN hz u hxz)
  have a2 := (hN.base_le_target _ x).trans (target_defectBound_le h hFb hkb hK hN hb u hxb)
  have a3 := coldness_mul_potentialNorm_le h hFz hkz hK hN hz u hxz
  have a4 := coldness_mul_potentialNorm_le h hFb hkb hK hN hb u hxb
  have b3 := mul_le_mul_of_nonneg_left (hN.base_le_target (potentialNorm S V z u) x) hκ
  have b4 := mul_le_mul_of_nonneg_left (hN.base_le_target (potentialNorm S V b u) x) hκ
  have c1 : Md (gapSource (Cs / (cellSideLength F : ℝ)) Ch S V z b u) x ≤
      Md (defectBound (Cs / (cellSideLength F : ℝ)) Ch S V z u) x +
          Md (defectBound (Cs / (cellSideLength F : ℝ)) Ch S V b u) x +
        2 * (Cs / (cellSideLength F : ℝ)) * (Md (potentialNorm S V z u) x + Md (potentialNorm S V b u) x) := by
    refine (hN.isSeminorm_base.add_le _ _ x).trans (add_le_add (hN.isSeminorm_base.add_le _ _ x) ?_)
    rw [hN.isSeminorm_base.smul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (hN.isSeminorm_base.add_le _ _ x) (by positivity)
  have e : gapSourceConstant K Ch * (nearTotal Md Sr Cs S V u z + nearTotal Md Sr Cs S V u b) =
      defectConstant K Ch * nearTotal Md Sr Cs S V u z + defectConstant K Ch * nearTotal Md Sr Cs S V u b +
        2 * (potentialConstant K Ch * nearTotal Md Sr Cs S V u z +
          potentialConstant K Ch * nearTotal Md Sr Cs S V u b) := by
    unfold gapSourceConstant
    ring
  rw [e]
  have f1 : curlTotal Sr S V u z + Cs * formTotal Md S u z = nearTotal Md Sr Cs S V u z := rfl
  have f2 : curlTotal Sr S V u b + Cs * formTotal Md S u b = nearTotal Md Sr Cs S V u b := rfl
  rw [f1] at a1
  rw [f2] at a2
  have g : 2 * (Cs / (cellSideLength F : ℝ)) * (Md (potentialNorm S V z u) x + Md (potentialNorm S V b u) x) =
      2 * (Cs / (cellSideLength F : ℝ) * Md (potentialNorm S V z u) x +
        Cs / (cellSideLength F : ℝ) * Md (potentialNorm S V b u) x) := by
    ring
  rw [g] at c1
  linarith
end Gap
section Norm
variable {F : BlockFrame} {S : Finset F.Cell} {V : F.GaugeField F.top} {z b : F.Cell} {Cs r Ch : ℝ}
  {Md Lf Sr : (F.Site 0 → ℝ) → F.Cell → ℝ} {σ : F.Cell → ℝ} {K : ℝ}
def gapStepConstant (K Ch : ℝ) : ℝ := 8 * (1 + 8 * K * 81) * gapSourceConstant K Ch
theorem gapStepConstant_nonneg (hK : 0 ≤ K) (hCh : 0 ≤ Ch) : 0 ≤ gapStepConstant K Ch := by
  have := gapSourceConstant_nonneg hK hCh
  unfold gapStepConstant
  positivity
theorem gapSource_of_not_mem {κ : ℝ} (h : PotentialSetting S V Cs r Ch)
    (u : F.Site 0 → Fin 4 → imaginaryQuaternions) {t : F.Site 0} (ht : t ∉ sitesOfCells S 0) :
    gapSource κ Ch S V z b u t = 0 := by
  have h1 : t ∉ patchSiteSet S z := fun h2 => ht (h.patchSiteSet_subset z h2)
  have h2 : t ∉ patchSiteSet S b := fun h3 => ht (h.patchSiteSet_subset b h3)
  simp only [gapSource, defectBound_of_not_mem u h1, defectBound_of_not_mem u h2, potentialNorm,
    restrictToPatch_of_not_mem h1, restrictToPatch_of_not_mem h2]
  simp
theorem base_stepNorms_framedGap_le {R R' : Lattice4 → Lattice4 → UnitQuaternion} (h : PotentialSetting S V Cs r Ch)
    (hFb : IsPatchFrame S V b R Cs r) (hFz : IsPatchFrame S V z R' Cs r)
    {H H' : Lattice4 × Fin 4 → Lattice4 × Fin 4 × Fin 4 → ℝ} {Gk Gk' : Lattice4 → Lattice4 × Fin 4 → ℝ}
    (hkb : HomotopyKernels (9 * (cellSideLength F).toNat) (fun _ => 12 * cellSideLength F) (patchDomain S b) H Gk Ch)
    (hkz : HomotopyKernels (9 * (cellSideLength F).toNat) (fun _ => 12 * cellSideLength F) (patchDomain S z) H' Gk' Ch)
    (hK : 0 ≤ K) (hN : CellNormFamily S Md Lf Sr σ K) (hb : b ∈ S) (hz : z ∈ S) (hd : cellSupDist z b ≤ 2)
    (u : F.Site 0 → Fin 4 → imaginaryQuaternions) (x : F.Cell) :
    Md (stepNorms (nearPatch S b) S b (framedGap S V z b u)) x ≤
      gapStepConstant K Ch * (nearTotal Md Sr Cs S V u z + nearTotal Md Sr Cs S V u b) := by
  classical
  have hκ := h.coldnessRatio_nonneg
  have hCh := h.kernelConst_nonneg
  have hc0 := h.coldness_nonneg
  obtain ⟨W0, hW0⟩ : ∃ W0, W0 = gapSourceConstant K Ch *
      (nearTotal Md Sr Cs S V u z + nearTotal Md Sr Cs S V u b) := ⟨_, rfl⟩
  have hW00 : 0 ≤ W0 := by
    rw [hW0]
    exact mul_nonneg (gapSourceConstant_nonneg hK hCh)
      (add_nonneg (nearTotal_nonneg hc0 hN u z) (nearTotal_nonneg hc0 hN u b))
  have e : gapStepConstant K Ch * (nearTotal Md Sr Cs S V u z + nearTotal Md Sr Cs S V u b) =
      8 * (1 + 8 * K * 81) * W0 := by
    rw [hW0, gapStepConstant]
    ring
  rw [e]
  have hg0 : ∀ t, 0 ≤ gapSource (Cs / (cellSideLength F : ℝ)) Ch S V z b u t := gapSource_nonneg hκ hCh u
  by_cases hx : x ∈ cellBall S b 6
  · obtain ⟨hxS, hx5⟩ := Finset.mem_filter.1 hx
    have near : ∀ {x1 : F.Cell}, cellSupDist x x1 ≤ 1 →
        Md (gapSource (Cs / (cellSideLength F : ℝ)) Ch S V z b u) x1 ≤ W0 := by
      intro x1 hx1
      have d1 := cellSupDist_triangle x1 x b
      have d2 := cellSupDist_triangle x1 b z
      rw [cellSupDist_symm x1 x, cellSupDist_symm x b] at d1
      rw [cellSupDist_symm b z] at d2
      rw [hW0]
      exact base_gapSource_le h hFb hFz hkb hkz hK hN hb hz u (by omega) (by omega)
    have h1 : Md (stepNorms (nearPatch S b) S b (framedGap S V z b u)) x ≤
        8 * Md (neighbourSum S b (gapSource (Cs / (cellSideLength F : ℝ)) Ch S V z b u)) x := by
      have h2 : Md (stepNorms (nearPatch S b) S b (framedGap S V z b u)) x ≤
          Md (fun t => 8 * neighbourSum S b (gapSource (Cs / (cellSideLength F : ℝ)) Ch S V z b u) t) x := by
        refine hN.isSeminorm_base.mono_abs _ _ _ fun t _ => ?_
        rw [abs_of_nonneg (stepNorms_nonneg _ _ t),
          abs_of_nonneg (mul_nonneg (by norm_num) (neighbourSum_nonneg hg0 t))]
        exact stepNorms_framedGap_le h hFb hFz hkb hkz hd u t
      refine h2.trans (le_of_eq ?_)
      rw [hN.isSeminorm_base.smul, abs_of_nonneg (by norm_num)]
    have h3 := base_neighbourSum_le (z := b) hN hg0 (fun t ht => gapSource_of_not_mem h u ht) x
    have h4 : ∑ y1 ∈ cellBall S x 1, Md (gapSource (Cs / (cellSideLength F : ℝ)) Ch S V z b u) y1 ≤ 81 * W0 := by
      calc _ ≤ ∑ _y1 ∈ cellBall S x 1, W0 := Finset.sum_le_sum fun y1 hy1 => near (Finset.mem_filter.1 hy1).2
        _ = ((cellBall S x 1).card : ℝ) * W0 := by simp
        _ ≤ _ := by
            refine mul_le_mul_of_nonneg_right ?_ hW00
            have := card_cellBall_le (S := S) h.ambient x 1
            norm_num at this ⊢
            exact this
    have h5 := near (x1 := x) (by simp [cellSupDist])
    have h6 := mul_le_mul_of_nonneg_left h4 hK
    have h7 : Md (neighbourSum S b (gapSource (Cs / (cellSideLength F : ℝ)) Ch S V z b u)) x ≤
        (1 + 8 * K * 81) * W0 := by
      have e2 : (1 + 8 * K * 81) * W0 = W0 + 8 * (K * (81 * W0)) := by ring
      rw [e2]
      linarith
    have h8 := mul_le_mul_of_nonneg_left h7 (by norm_num : (0 : ℝ) ≤ 8)
    refine h1.trans (h8.trans (le_of_eq ?_))
    ring
  · have hz0 : Md (stepNorms (nearPatch S b) S b (framedGap S V z b u)) x = 0 := by
      refine cellSeminorm_eq_zero_of_vanish hN.isSeminorm_base fun t ht => ?_
      by_cases htp : t ∈ patchSiteSet S b
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 htp
        rw [stepNorms_patchSite h _ _ ha]
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [if_neg]
        rintro ⟨h1, -⟩
        obtain ⟨y, hy, hy5, hs⟩ := exists_cell_of_mem_nearPatch h h1
        have e1 : enclosingCell (patchSite S b a) = y := (Finset.mem_filter.1 hs).2
        have e2 : enclosingCell (patchSite S b a) = x := (Finset.mem_filter.1 ht).2
        have e3 : x = y := e2.symm.trans e1
        exact hx (Finset.mem_filter.2 ⟨e3 ▸ hy, e3 ▸ hy5⟩)
      · exact stepNorms_of_not_mem _ _ htp
    rw [hz0]
    positivity
def gapKernel (S : Finset F.Cell) (V : F.GaugeField F.top) (z b : F.Cell)
    (u : F.Site 0 → Fin 4 → imaginaryQuaternions) : F.Site 0 → ℝ :=
  patchCubicKernel S b (stepNorms (nearPatch S b) S b (framedGap S V z b u))
theorem gapKernel_nonneg (u : F.Site 0 → Fin 4 → imaginaryQuaternions) (t : F.Site 0) :
    0 ≤ gapKernel S V z b u t :=
  patchCubicKernel_nonneg (stepNorms_nonneg _ _) t
theorem target_gapKernel_le {R R' : Lattice4 → Lattice4 → UnitQuaternion} (h : PotentialSetting S V Cs r Ch)
    (hFb : IsPatchFrame S V b R Cs r) (hFz : IsPatchFrame S V z R' Cs r)
    {H H' : Lattice4 × Fin 4 → Lattice4 × Fin 4 × Fin 4 → ℝ} {Gk Gk' : Lattice4 → Lattice4 × Fin 4 → ℝ}
    (hkb : HomotopyKernels (9 * (cellSideLength F).toNat) (fun _ => 12 * cellSideLength F) (patchDomain S b) H Gk Ch)
    (hkz : HomotopyKernels (9 * (cellSideLength F).toNat) (fun _ => 12 * cellSideLength F) (patchDomain S z) H' Gk' Ch)
    (hK : 0 ≤ K) (hN : CellNormFamily S Md Lf Sr σ K) (hb : b ∈ S) (hz : z ∈ S) (hd : cellSupDist z b ≤ 2)
    (u : F.Site 0 → Fin 4 → imaginaryQuaternions) (y : F.Cell) :
    Lf (gapKernel S V z b u) y ≤ (cellSideLength F : ℝ) * (K ^ 2 * 41 ^ 4 * gapStepConstant K Ch *
      (nearTotal Md Sr Cs S V u z + nearTotal Md Sr Cs S V u b)) := by
  classical
  have hNp := h.cellSideLength_pos
  have hCh := h.kernelConst_nonneg
  have hc0 := h.coldness_nonneg
  obtain ⟨D0, hD0⟩ : ∃ D0, D0 = gapStepConstant K Ch *
      (nearTotal Md Sr Cs S V u z + nearTotal Md Sr Cs S V u b) := ⟨_, rfl⟩
  have hD00 : 0 ≤ D0 := by
    rw [hD0]
    exact mul_nonneg (gapStepConstant_nonneg hK hCh)
      (add_nonneg (nearTotal_nonneg hc0 hN u z) (nearTotal_nonneg hc0 hN u b))
  have hx : ∀ x, Sr (restrictToPatch S b (stepNorms (nearPatch S b) S b (framedGap S V z b u))) x ≤
      K * (cellSideLength F : ℝ) * D0 := by
    intro x
    refine (hN.source_le _ x).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    refine le_trans (hN.isSeminorm_base.mono_abs _ (stepNorms (nearPatch S b) S b (framedGap S V z b u)) x
      fun t _ => ?_) ?_
    · rw [abs_of_nonneg (restrictToPatch_nonneg (stepNorms_nonneg _ _) t), abs_of_nonneg (stepNorms_nonneg _ _ t)]
      exact restrictToPatch_le (stepNorms_nonneg _ _) t
    · rw [hD0]
      exact base_stepNorms_framedGap_le h hFb hFz hkb hkz hK hN hb hz hd u x
  refine (hN.kernel_le b hb _ y).trans ?_
  have h1 : ∑ x ∈ cellBall S b 20, Sr (restrictToPatch S b (stepNorms (nearPatch S b) S b (framedGap S V z b u))) x ≤
      41 ^ 4 * (K * (cellSideLength F : ℝ) * D0) := by
    calc _ ≤ ∑ _x ∈ cellBall S b 20, K * (cellSideLength F : ℝ) * D0 := Finset.sum_le_sum fun x _ => hx x
      _ = ((cellBall S b 20).card : ℝ) * (K * (cellSideLength F : ℝ) * D0) := by simp
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have := card_cellBall_le (S := S) h.ambient b 20
          norm_num at this ⊢
          exact this
  have h2 := mul_le_mul_of_nonneg_left h1 hK
  refine h2.trans (le_of_eq ?_)
  rw [hD0]
  ring
theorem cellMean_centredPotential (h : PotentialSetting S V Cs r Ch) (u : F.Site 0 → Fin 4 → imaginaryQuaternions) :
    cellMean F (centredPotential S V z u) = 0 := by
  have e2 : centredPotential S V z u = fun a =>
      localPotential S V (referenceFieldChain S V 0) z (toQuaternionForm u) a -
        cellMean F (localPotential S V (referenceFieldChain S V 0) z (toQuaternionForm u)) := rfl
  rw [e2, cellMean_sub, cellMean_const h.odd_side.pos, sub_self]
theorem norm_cellMean_framedGap_sub_le (h : PotentialSetting S V Cs r Ch) (hb : b ∈ S) (hd : cellSupDist z b ≤ 2)
    (u : F.Site 0 → Fin 4 → imaginaryQuaternions) {g : UnitQuaternion}
    (hg : ∀ x ∈ cellSites S b, ‖((patchFrameTransition S V z b x : UnitQuaternion) : ℍ[ℝ]) - (g : ℍ[ℝ])‖ ≤ Cs) :
    ‖cellMean F (framedGap S V z b u) - adjointAction g (siteMean (sitePotential S V z u) b)‖ ≤
      2 * Cs * ((1 / (cellSideLength F : ℝ) ^ 4) * ∑ c ∈ centredCube (F.blockSide ^ F.top),
        potentialNorm S V z u (cellCentre 0 b + siteOfCoords 0 c)) := by
  classical
  have hL := h.odd_side.pos
  have hNp := h.cellSideLength_pos
  have hinpatch : ∀ a ∈ cellOffsets F, patchSite S b a ∈ cellSites S b ∧ patchSite S b a ∈ patchSiteSet S z := by
    intro a ha
    have hs := mem_nearPatch_of_mem_cellOffsets h hb ha
    have hcell : patchSite S b a ∈ cellSites S b := by
      obtain ⟨y, hy, -, ht⟩ := exists_cell_of_mem_nearPatch h hs
      refine Finset.mem_filter.2 ⟨(Finset.mem_filter.1 ht).1, ?_⟩
      have hcube : (fun k => closedOrthant S b k * (a k - (cellSideLength F - 1) / 2)) ∈
          centredCube (F.blockSide ^ F.top) := by
        obtain ⟨h0, h1⟩ := cellSideLength_half (F := F) h.odd_side
        rw [mem_centredCube_iff]
        intro i
        have := Finset.mem_Ico.1 (Fintype.mem_piFinset.1 ha i)
        rcases h.closedOrthant_cases b i with hs | hs <;> rw [hs] <;> constructor <;> omega
      exact LocalPartition.enclosingCell_cellCentre_add h.odd_side b _ hcube
    exact ⟨hcell, h.mem_patchSiteSet_of_cellSupDist_le hb (by omega) hcell⟩
  have e1 : cellMean F (framedGap S V z b u) =
      (1 / (cellSideLength F : ℝ) ^ 4) • ∑ a ∈ cellOffsets F,
        adjointAction (patchFrameTransition S V z b (patchSite S b a)) (sitePotential S V z u (patchSite S b a)) := by
    have e0 : cellMean F (framedGap S V z b u) = cellMean F (fun a =>
        adjointAction (patchFrameTransition S V z b (patchSite S b a)) (sitePotential S V z u (patchSite S b a)) -
          centredPotential S V b u a) := by
      refine cellMean_congr fun a ha => ?_
      simp only [framedGap, PatchDifferences.localSection, potentialGap, PatchForms.adjointAction_apply_sub]
      have f1 : adjointAction (frameChange S V b (patchSite S b a))⁻¹ (potentialSection S V z u (patchSite S b a)) =
          adjointAction (patchFrameTransition S V z b (patchSite S b a)) (sitePotential S V z u (patchSite S b a)) := by
        simp only [potentialSection, patchFrameTransition, sitePotential]
        rw [← PatchForms.adjointAction_mul_apply]
      have f2 : adjointAction (frameChange S V b (patchSite S b a))⁻¹ (potentialSection S V b u (patchSite S b a)) =
          centredPotential S V b u a := by
        simp only [potentialSection]
        rw [PatchForms.adjointAction_inv_apply_apply,
          h.patchChart_patchSite (mem_patchDomain_of_mem_cellOffsets hb hL ha)]
      rw [f1, f2]
    rw [e0, cellMean_sub, cellMean_centredPotential h u, sub_zero]
    rfl
  have e2 : adjointAction g (siteMean (sitePotential S V z u) b) =
      (1 / (cellSideLength F : ℝ) ^ 4) • ∑ a ∈ cellOffsets F,
        adjointAction g (sitePotential S V z u (patchSite S b a)) := by
    simp only [siteMean]
    rw [PatchForms.adjointAction_apply_smul, PatchForms.adjointAction_apply_sum,
      sum_cellOffsets_patchSite h.odd_side (h.closedOrthant_cases b)
        (fun t => adjointAction g (sitePotential S V z u t))]
  rw [e1, e2, ← smul_sub, ← Finset.sum_sub_distrib, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity),
    ← sum_cellOffsets_patchSite h.odd_side (h.closedOrthant_cases b) (potentialNorm S V z u)]
  have e3 : ∀ a ∈ cellOffsets F,
      ‖adjointAction (patchFrameTransition S V z b (patchSite S b a)) (sitePotential S V z u (patchSite S b a)) -
        adjointAction g (sitePotential S V z u (patchSite S b a))‖ ≤
        2 * Cs * potentialNorm S V z u (patchSite S b a) := by
    intro a ha
    obtain ⟨h1, h2⟩ := hinpatch a ha
    refine (PatchForms.norm_adjointAction_sub_adjointAction_apply_le _ _ _).trans ?_
    have h3 : potentialNorm S V z u (patchSite S b a) = ‖sitePotential S V z u (patchSite S b a)‖ := by
      rw [potentialNorm, restrictToPatch_of_mem h2]
      rfl
    rw [h3]
    exact mul_le_mul_of_nonneg_right (by linarith [hg _ h1]) (norm_nonneg _)
  have e4 := (norm_sum_le (cellOffsets F) fun a =>
    adjointAction (patchFrameTransition S V z b (patchSite S b a)) (sitePotential S V z u (patchSite S b a)) -
      adjointAction g (sitePotential S V z u (patchSite S b a))).trans (Finset.sum_le_sum e3)
  have e5 := mul_le_mul_of_nonneg_left e4 (by positivity : 0 ≤ 1 / (cellSideLength F : ℝ) ^ 4)
  refine e5.trans (le_of_eq ?_)
  rw [← Finset.mul_sum]
  ring
end Norm
section Bound
variable {F : BlockFrame} {S : Finset F.Cell} {V : F.GaugeField F.top} {z b : F.Cell} {Cs r Ch : ℝ}
  {Md Lf Sr : (F.Site 0 → ℝ) → F.Cell → ℝ} {σ : F.Cell → ℝ} {K : ℝ}
def gapMeanConstant (K Ch : ℝ) : ℝ :=
  Ch * K ^ 3 * 41 ^ 4 * gapStepConstant K Ch + 24 * K * (1 + meanStepConstant K Ch) + 2 * K * potentialConstant K Ch
theorem gapMeanConstant_nonneg (hK : 0 ≤ K) (hCh : 0 ≤ Ch) : 0 ≤ gapMeanConstant K Ch := by
  have h1 := gapStepConstant_nonneg hK hCh
  have h2 := meanStepConstant_nonneg hK hCh
  have h3 := potentialConstant_nonneg hK hCh
  unfold gapMeanConstant
  positivity
def gapConstant (K Ch : ℝ) : ℝ := K ^ 2 * gapMeanConstant K Ch + Ch * (K ^ 2 * 41 ^ 4 * gapStepConstant K Ch)
theorem gapConstant_nonneg (hK : 0 ≤ K) (hCh : 0 ≤ Ch) : 0 ≤ gapConstant K Ch := by
  have h1 := gapStepConstant_nonneg hK hCh
  have h2 := gapMeanConstant_nonneg hK hCh
  unfold gapConstant
  positivity
theorem target_sectionNormOn_potentialGap_le (h : PotentialSetting S V Cs r Ch) (hK : 0 ≤ K)
    (hN : CellNormFamily S Md Lf Sr σ K) (hb : b ∈ S) (hz : z ∈ S)
    (hd : cellSupDist z b ≤ 2) (u : F.Site 0 → Fin 4 → imaginaryQuaternions) {g : UnitQuaternion}
    (hg : ∀ x ∈ cellSites S b, ‖((patchFrameTransition S V z b x : UnitQuaternion) : ℍ[ℝ]) - (g : ℍ[ℝ])‖ ≤ Cs)
    {T : F.Cell → ℝ} (hT0 : ∀ y, 0 ≤ T y)
    (hT : ∀ c ∈ innerBonds S F.top, σ c.1 *
      ‖linearPart (referenceFieldChain S V) (baseOnlyChart u) F.top c.1 c.2‖ ≤ T c.1)
    (hTop : ∀ c ∈ innerBonds S F.top, enclosingCell c.1 ∈ cellBall S z 10 →
      enclosingCell (c.1 + unitStep F.top c.2) ∈ cellBall S z 10 →
      ‖patchFrameForm S V z (linearPart (referenceFieldChain S V) (baseOnlyChart u) F.top) c.1 c.2 -
        nestedAverage (patchFrameForm S V z (toQuaternionForm u)) F.top c.1 c.2‖ ≤
      Cs * nestedAverage (fun x k => ‖toQuaternionForm u x k‖) F.top c.1 c.2) {y : F.Cell}
    (hy : y ∈ cellBall S b 2) :
    Lf (PatchDifferences.sectionNormOn S (potentialGap S V z b u)) y ≤ (cellSideLength F : ℝ) * (gapConstant K Ch *
      (∑ x ∈ cellBall S z 2, T x + nearTotal Md Sr Cs S V u z + nearTotal Md Sr Cs S V u b)) := by
  classical
  have hL := h.odd_side.pos
  have hNp := h.cellSideLength_pos
  have hCh := h.kernelConst_nonneg
  have hc0 := h.coldness_nonneg
  obtain ⟨R, hFb⟩ := h.frames b hb
  obtain ⟨R', hFz⟩ := h.frames z hz
  obtain ⟨H, Gk, hkb⟩ := exists_homotopyKernels_patchDomain h hb
  obtain ⟨H', Gk', hkz⟩ := exists_homotopyKernels_patchDomain h hz
  obtain ⟨Hs, Gs, hks⟩ := exists_homotopyKernels_nearPatch h hb
  have hy2 := (Finset.mem_filter.1 hy).2
  obtain ⟨W, hW⟩ : ∃ W, W = gapKernel S V z b u := ⟨_, rfl⟩
  have hW0 : ∀ t, 0 ≤ W t := fun t => by
    rw [hW]
    exact gapKernel_nonneg u t
  obtain ⟨Uz, hUz⟩ : ∃ Uz, Uz = nearTotal Md Sr Cs S V u z := ⟨_, rfl⟩
  obtain ⟨Ub, hUb⟩ : ∃ Ub, Ub = nearTotal Md Sr Cs S V u b := ⟨_, rfl⟩
  have hUz0 : 0 ≤ Uz := hUz ▸ nearTotal_nonneg hc0 hN u z
  have hUb0 : 0 ≤ Ub := hUb ▸ nearTotal_nonneg hc0 hN u b
  obtain ⟨TT, hTT⟩ : ∃ TT, TT = ∑ x ∈ cellBall S z 2, T x := ⟨_, rfl⟩
  have hTT0 : 0 ≤ TT := hTT ▸ Finset.sum_nonneg fun x _ => hT0 x
  rw [← hUz, ← hUb, ← hTT]
  obtain ⟨cS, hcS⟩ : ∃ cS, cS = K ^ 2 * 41 ^ 4 * gapStepConstant K Ch := ⟨_, rfl⟩
  have hcS0 : 0 ≤ cS := by
    rw [hcS]
    have := gapStepConstant_nonneg hK hCh
    positivity
  have hWn : ∀ y', Lf W y' ≤ (cellSideLength F : ℝ) * (cS * (Uz + Ub)) := by
    intro y'
    rw [hW, hcS, hUz, hUb]
    exact target_gapKernel_le h hFb hFz hkb hkz hK hN hb hz hd u y'
  obtain ⟨φ, hφ⟩ : ∃ φ, φ = framedGap S V z b u := ⟨_, rfl⟩
  obtain ⟨ms, hms⟩ : ∃ ms, ms = endpointMean (3 * (cellSideLength F).toNat) (fun _ => 3 * cellSideLength F) φ :=
    ⟨_, rfl⟩
  have hoff : ∀ {a : Lattice4}, a ∈ nearPatch S b → ‖φ a - ms‖ ≤ Ch * W (patchSite S b a) := by
    intro a ha
    rw [hms, hW, hφ]
    exact norm_sub_endpointMean_le h hks (nearPatch_subset_patchDomain hL) _ ha
  have hca : ‖ms - cellMean F φ‖ ≤ Ch * ((1 / (cellSideLength F : ℝ) ^ 4) *
      ∑ c ∈ centredCube (F.blockSide ^ F.top), W (cellCentre 0 b + siteOfCoords 0 c)) := by
    have e : ms - cellMean F φ = cellMean F (fun a => ms - φ a) := by
      rw [cellMean_sub, cellMean_const hL]
    rw [e, ← sum_cellOffsets_patchSite h.odd_side (h.closedOrthant_cases b) W]
    refine (norm_cellMean_le hL _ (fun a => Ch * W (patchSite S b a)) fun a ha => ?_).trans (le_of_eq ?_)
    · rw [norm_sub_rev]
      exact hoff (mem_nearPatch_of_mem_cellOffsets h hb ha)
    · rw [← Finset.mul_sum]
      ring
  have hcm := norm_cellMean_framedGap_sub_le h hb hd u hg
  rw [← hφ] at hcm
  have hM : σ b * ‖siteMean (sitePotential S V z u) b‖ ≤ 24 * (K * (TT + meanStepConstant K Ch * Uz)) := by
    have := norm_siteMean_near_le h hFz hkz hK hN hz u hb hd hT0 hT hTop
    rw [← hTT] at this
    rw [hUz]
    exact this
  have hσb := hN.scale_pos b
  have hY1 : σ b * ((1 / (cellSideLength F : ℝ) ^ 4) * ∑ c ∈ centredCube (F.blockSide ^ F.top),
      potentialNorm S V z u (cellCentre 0 b + siteOfCoords 0 c)) ≤
      K * Md (potentialNorm S V z u) b / (cellSideLength F : ℝ) :=
    scale_mul_cellMean_le hN h.ambient h.odd_side hb _ (potentialNorm_nonneg u)
  have hY2 : Cs * (K * Md (potentialNorm S V z u) b / (cellSideLength F : ℝ)) ≤
      K * (potentialConstant K Ch * Uz) := by
    have a1 := coldness_mul_potentialNorm_le h hFz hkz hK hN hz u (y := b) (by rw [cellSupDist_symm]; omega)
    rw [← hUz] at a1
    have a2 := mul_le_mul_of_nonneg_left (hN.base_le_target (potentialNorm S V z u) b) (div_nonneg hc0 hNp.le)
    have a3 := mul_le_mul_of_nonneg_left (a2.trans a1) hK
    refine le_trans (le_of_eq ?_) a3
    ring
  have hW1 : σ b * ((1 / (cellSideLength F : ℝ) ^ 4) * ∑ c ∈ centredCube (F.blockSide ^ F.top),
      W (cellCentre 0 b + siteOfCoords 0 c)) ≤
      K * Md W b / (cellSideLength F : ℝ) := scale_mul_cellMean_le hN h.ambient h.odd_side hb W hW0
  have hW2 : K * Md W b / (cellSideLength F : ℝ) ≤ K * (cS * (Uz + Ub)) := by
    have a1 := (hN.base_le_target W b).trans (hWn b)
    rw [div_le_iff₀ hNp]
    have := mul_le_mul_of_nonneg_left a1 hK
    refine this.trans (le_of_eq ?_)
    ring
  have hms1 : ‖ms‖ ≤ Ch * ((1 / (cellSideLength F : ℝ) ^ 4) * ∑ c ∈ centredCube (F.blockSide ^ F.top),
      W (cellCentre 0 b + siteOfCoords 0 c)) +
      (‖siteMean (sitePotential S V z u) b‖ + 2 * Cs * ((1 / (cellSideLength F : ℝ) ^ 4) *
        ∑ c ∈ centredCube (F.blockSide ^ F.top), potentialNorm S V z u (cellCentre 0 b + siteOfCoords 0 c))) := by
    have t1 := norm_sub_le (ms - cellMean F φ) (- cellMean F φ)
    rw [sub_neg_eq_add, sub_add_cancel, norm_neg] at t1
    have t2 := norm_sub_le (cellMean F φ - adjointAction g (siteMean (sitePotential S V z u) b))
      (- adjointAction g (siteMean (sitePotential S V z u) b))
    rw [sub_neg_eq_add, sub_add_cancel, norm_neg, PatchForms.norm_adjointAction_apply] at t2
    linarith
  obtain ⟨A1, hA1⟩ : ∃ A1, A1 = (1 / (cellSideLength F : ℝ) ^ 4) *
      ∑ c ∈ centredCube (F.blockSide ^ F.top), W (cellCentre 0 b + siteOfCoords 0 c) := ⟨_, rfl⟩
  obtain ⟨A2, hA2⟩ : ∃ A2, A2 = (1 / (cellSideLength F : ℝ) ^ 4) * ∑ c ∈ centredCube (F.blockSide ^ F.top),
      potentialNorm S V z u (cellCentre 0 b + siteOfCoords 0 c) := ⟨_, rfl⟩
  rw [← hA1, ← hA2] at hms1
  rw [← hA1] at hW1
  rw [← hA2] at hY1
  have hσms : σ b * ‖ms‖ ≤ gapMeanConstant K Ch * (TT + Uz + Ub) := by
    have b1 := mul_le_mul_of_nonneg_left hms1 hσb.le
    have e : σ b * (Ch * A1 + (‖siteMean (sitePotential S V z u) b‖ + 2 * Cs * A2)) =
        Ch * (σ b * A1) + σ b * ‖siteMean (sitePotential S V z u) b‖ + 2 * (Cs * (σ b * A2)) := by ring
    rw [e] at b1
    have b2 : Ch * (σ b * A1) ≤ Ch * (K * (cS * (Uz + Ub))) := mul_le_mul_of_nonneg_left (hW1.trans hW2) hCh
    have b3 : Cs * (σ b * A2) ≤ K * (potentialConstant K Ch * Uz) :=
      (mul_le_mul_of_nonneg_left hY1 hc0).trans hY2
    have hp := potentialConstant_nonneg hK hCh
    have ht := meanStepConstant_nonneg hK hCh
    have hs := gapStepConstant_nonneg hK hCh
    have e2 : gapMeanConstant K Ch * (TT + Uz + Ub) = Ch * (K * (cS * (Uz + Ub))) +
        24 * (K * (TT + meanStepConstant K Ch * Uz)) +
        2 * (K * (potentialConstant K Ch * Uz)) +
        (Ch * K ^ 3 * 41 ^ 4 * gapStepConstant K Ch * TT + 24 * K * (Uz + Ub) +
          24 * K * meanStepConstant K Ch * (TT + Ub) +
          2 * K * potentialConstant K Ch * (TT + Ub)) := by
      unfold gapMeanConstant
      rw [hcS]
      ring
    rw [e2]
    generalize meanStepConstant K Ch = cT at *
    generalize potentialConstant K Ch = cB at *
    generalize gapStepConstant K Ch = gS at *
    have q : 0 ≤ Ch * K ^ 3 * 41 ^ 4 * gS * TT + 24 * K * (Uz + Ub) + 24 * K * cT * (TT + Ub) +
        2 * K * cB * (TT + Ub) := by
      positivity
    linarith
  have hpt : ∀ t ∈ cellSites S y, |PatchDifferences.sectionNormOn S (potentialGap S V z b u) t| ≤
      |‖ms‖ * 1 + Ch * W t| := by
    intro t ht
    have hts : t ∈ sitesOfCells S 0 := (Finset.mem_filter.1 ht).1
    have h0 := hW0 t
    rw [abs_of_nonneg (sectionNormOn_nonneg _ t), abs_of_nonneg (by positivity)]
    have e1 : PatchDifferences.sectionNormOn S (potentialGap S V z b u) t = ‖potentialGap S V z b u t‖ := by
      simp [PatchDifferences.sectionNormOn, hts]
    have ha := patchChart_mem_nearPatch h hy ht
    have e2 : patchSite S b (patchChart S b t) = t := patchSite_patchChart (h.closedOrthant_cases b) t
    have e3 : ‖potentialGap S V z b u t‖ = ‖φ (patchChart S b t)‖ := by
      rw [hφ, framedGap, norm_localSection, e2]
    have h1 := hoff ha
    rw [e2] at h1
    have h2 := norm_sub_le (φ (patchChart S b t) - ms) (- ms)
    rw [sub_neg_eq_add, sub_add_cancel, norm_neg] at h2
    rw [e1, e3]
    linarith
  have hs1 : Lf (PatchDifferences.sectionNormOn S (potentialGap S V z b u)) y ≤
      ‖ms‖ * Lf (fun _ => 1) y + Ch * Lf W y := by
    refine (hN.isSeminorm_target.mono_abs _ _ _ hpt).trans
      ((hN.isSeminorm_target.add_le _ _ y).trans (add_le_add ?_ ?_))
    · rw [hN.isSeminorm_target.smul, abs_of_nonneg (norm_nonneg _)]
    · rw [hN.isSeminorm_target.smul, abs_of_nonneg hCh]
  have hl1 : Lf (fun _ => 1) y ≤ K * (cellSideLength F : ℝ) * σ y := hN.const_le y
  have hsn : σ y ≤ K * σ b := hN.scale_le_of_near y b (by rw [cellSupDist_symm]; omega)
  have hm0 := norm_nonneg ms
  have hs2 : ‖ms‖ * Lf (fun _ => 1) y ≤ (cellSideLength F : ℝ) * (K ^ 2 * (σ b * ‖ms‖)) := by
    have a1 : ‖ms‖ * Lf (fun _ => 1) y ≤ ‖ms‖ * (K * (cellSideLength F : ℝ) * (K * σ b)) :=
      mul_le_mul_of_nonneg_left (hl1.trans (mul_le_mul_of_nonneg_left hsn (by positivity))) hm0
    refine a1.trans (le_of_eq ?_)
    ring
  have hs3 : (cellSideLength F : ℝ) * (K ^ 2 * (σ b * ‖ms‖)) ≤
      (cellSideLength F : ℝ) * (K ^ 2 * (gapMeanConstant K Ch * (TT + Uz + Ub))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hσms (by positivity)) hNp.le
  have hs4 : Ch * Lf W y ≤ Ch * ((cellSideLength F : ℝ) * (cS * (TT + Uz + Ub))) := by
    refine mul_le_mul_of_nonneg_left ((hWn y).trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (by linarith) hcS0) hNp.le)) hCh
  have e : (cellSideLength F : ℝ) * (gapConstant K Ch * (TT + Uz + Ub)) =
      (cellSideLength F : ℝ) * (K ^ 2 * (gapMeanConstant K Ch * (TT + Uz + Ub))) +
        Ch * ((cellSideLength F : ℝ) * (cS * (TT + Uz + Ub))) := by
    unfold gapConstant
    rw [hcS]
    ring
  rw [e]
  linarith
end Bound
end YangMills.Construction.PatchGaps
end
