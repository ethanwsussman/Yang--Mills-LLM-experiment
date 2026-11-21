import YangMills.Construction.ColdChainAtEveryLevel.EveryFormSplitsAlongTheSlice
import YangMills.Construction.ColdChainAtEveryLevel.GaugeMapOnDifferences
import YangMills.Construction.ColdChainAtEveryLevel.TheGaugeMapAsALinearMap
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages GaugeMap LatticeFractionalIntegration
namespace SliceDecomposition
variable {F : BlockFrame}
theorem adjointAction_add (g : UnitQuaternion) (p q : ℍ[ℝ]) :
    adjointAction g (p + q) = adjointAction g p + adjointAction g q := by apply _root_.YangMills.Construction.BlockAverages.adjointAction_add <;> assumption
theorem adjointAction_sub (g : UnitQuaternion) (p q : ℍ[ℝ]) :
    adjointAction g (p - q) = adjointAction g p - adjointAction g q := by apply _root_.YangMills.Construction.BlockLines.adjointAction_sub <;> assumption
theorem adjointAction_smul (g : UnitQuaternion) (a : ℝ) (p : ℍ[ℝ]) :
    adjointAction g (a • p) = a • adjointAction g p := by apply _root_.YangMills.Construction.BlockAverages.adjointAction_smul <;> assumption
theorem adjointAction_inv_adjointAction (g : UnitQuaternion) (w : ℍ[ℝ]) :
    adjointAction g⁻¹ (adjointAction g w) = w := by apply _root_.YangMills.Construction.CellBumps.adjointAction_inv_adjointAction <;> assumption
theorem re_adjointAction (g : UnitQuaternion) (w : ℍ[ℝ]) : (adjointAction g w).re = w.re := by apply _root_.YangMills.Construction.PlaquetteLinearization.adjointAction_re <;> assumption
variable (S : Finset F.Cell) (V : F.GaugeField F.top) (R : F.GaugeField 0)
theorem frameCellMean_linear (a b : ℝ) (y : F.Cell) (ξ ξ' : F.Site 0 → ℍ[ℝ]) :
    frameCellMean S V y (fun x => a • ξ x + b • ξ' x) = a • frameCellMean S V y ξ + b • frameCellMean S V y ξ' := by apply _root_.YangMills.Construction.GaugeMapLinear.frameCellMean_linComb <;> assumption
theorem gaugeMap_linear (a b : ℝ) (u u' : F.Site 0 → Fin 4 → ℍ[ℝ]) :
    gaugeMap S V R (fun x i => a • u x i + b • u' x i) =
      fun s => a • gaugeMap S V R u s + b • gaugeMap S V R u' s := by apply _root_.YangMills.Construction.GaugeMapLinear.gaugeMap_linComb <;> assumption
theorem re_gaugeMap (u : F.Site 0 → Fin 4 → ℍ[ℝ]) (hu : ∀ x i, (u x i).re = 0) (s : F.Site 0) :
    (gaugeMap S V R u s).re = 0 := by apply _root_.YangMills.Construction.GaugeMapLinear.re_gaugeMap <;> assumption
omit S V R in
theorem enclosingCell_cellCentre_add {j : ℕ} (hodd : Odd F.blockSide) (z : F.Cell) (h : Fin 4 → ℤ)
    (hh : h ∈ centredCube (F.blockSide ^ (F.top - j))) :
    enclosingCell (cellCentre j z + siteOfCoords j h) = z := by apply _root_.YangMills.Construction.CellBumps.enclosingCell_cellCentre_add <;> assumption
omit V R in
theorem orthantOffset_mem_centredCube (hodd : Odd F.blockSide) (z : F.Cell) (x : Lattice4) (hx : x ∈ cellOffsets F) :
    (fun i => closedOrthant S z i * (x i - (cellSideLength F - 1) / 2)) ∈ centredCube (F.blockSide ^ (F.top - 0)) := by apply _root_.YangMills.Construction.CellBumps.signed_offset_mem_centredCube <;> assumption
omit V R in
theorem enclosingCell_mem (hodd : Odd F.blockSide) (x : F.Site 0) (hx : x ∈ sitesOfCells S 0) :
    enclosingCell x ∈ S := by
  simp only [sitesOfCells, Finset.mem_biUnion, Finset.mem_image] at hx
  obtain ⟨z, hz, h, hh, rfl⟩ := hx
  rw [enclosingCell_cellCentre_add hodd z h hh]
  exact hz
omit S V R in
theorem cutoffProfile_nonneg (t : ℝ) : 0 ≤ cutoffProfile t := Real.smoothTransition.nonneg _
omit S V R in
theorem interiorBump_nonneg (s : F.Site 0) (y : F.Cell) : 0 ≤ interiorBump s y :=
  Finset.prod_nonneg fun _ _ => cutoffProfile_nonneg _
omit S V R in
theorem interiorBump_cellCentre (y : F.Cell) : interiorBump (cellCentre 0 y) y = 1 := by
  simp only [interiorBump, sub_self, Pi.zero_apply, ZMod.valMinAbs_zero, Int.cast_zero, mul_zero, zero_div]
  have : cutoffProfile 0 = 1 := by
    apply Real.smoothTransition.one_of_one_le
    norm_num
  simp [this]
omit S V R in
theorem interiorBump_eq_zero_of_ne (hodd : Odd F.blockSide) (y y' : F.Cell) (hne : y ≠ y') (h : Fin 4 → ℤ)
    (hh : h ∈ centredCube (F.blockSide ^ (F.top - 0))) : interiorBump (cellCentre 0 y + siteOfCoords 0 h) y' = 0 := by apply _root_.YangMills.Construction.CellBumps.interiorBump_eq_zero_of_ne <;> assumption
theorem cellMeanFree_gaugeMap (hodd : Odd F.blockSide) (hL : 0 < F.blockSide) (u : F.Site 0 → Fin 4 → ℍ[ℝ]) :
    CellMeanFree S V (gaugeMap S V R u) := by
  classical
  intro y hy
  have hside : (0 : ℝ) < (cellSideLength F : ℝ) := by
    have : (0 : ℤ) < cellSideLength F := by
      simp only [cellSideLength]
      have : (0 : ℤ) < F.blockSide := by exact_mod_cast hL
      positivity
    exact_mod_cast this
  set g := gluedPotential S V R u with hg
  set Dn : ℝ := (1 / (cellSideLength F : ℝ) ^ 4) * ∑ x ∈ cellOffsets F, interiorBump (patchSite S y x) y with hDn
  obtain ⟨k, hk⟩ := (Odd.pow (n := F.top) hodd)
  have hMn : (((F.blockSide ^ F.top : ℕ) : ℤ)) = 2 * (k : ℤ) + 1 := by rw [hk]; push_cast; ring
  have hM : cellSideLength F = 2 * (k : ℤ) + 1 := by
    simp only [cellSideLength]; rw [← hMn]; push_cast; rfl
  set x0 : Lattice4 := fun _ => (k : ℤ) with hx0
  have hx0m : x0 ∈ cellOffsets F := by
    refine Fintype.mem_piFinset.2 fun i => ?_
    rw [Finset.mem_Ico, hM]
    simp only [hx0]
    omega
  have hcentre : patchSite S y x0 = cellCentre 0 y := by
    simp only [patchSite, hM, hx0]
    have h2 : ((2 * (k : ℤ) + 1 - 1) / 2) = k := by omega
    rw [h2]
    have : siteOfCoords (F := F) 0 (fun i => closedOrthant S y i * ((k : ℤ) - k)) = 0 := by
      funext i
      simp [siteOfCoords]
    rw [this, add_zero]
  have hsum : 0 < ∑ x ∈ cellOffsets F, interiorBump (patchSite S y x) y := by
    have h1 : interiorBump (patchSite S y x0) y ≤ ∑ x ∈ cellOffsets F, interiorBump (patchSite S y x) y :=
      Finset.single_le_sum (fun x _ => interiorBump_nonneg _ _) hx0m
    rw [hcentre, interiorBump_cellCentre] at h1
    linarith
  have hDpos : 0 < Dn := by
    rw [hDn]; positivity
  have hpoint : ∀ x ∈ cellOffsets F,
      adjointAction (frameChange S V y (patchSite S y x))⁻¹ (gaugeMap S V R u (patchSite S y x)) =
        adjointAction (frameChange S V y (patchSite S y x))⁻¹ (g (patchSite S y x)) -
          (interiorBump (patchSite S y x) y / Dn) • frameCellMean S V y g := by
    intro x hx
    have hz : ∀ y' ∈ S, y' ≠ y → normalizedBump S (patchSite S y x) y' •
        adjointAction (frameChange S V y' (patchSite S y x)) (frameCellMean S V y' g) = 0 := by
      intro y' _ hne
      have h0 : interiorBump (patchSite S y x) y' = 0 :=
        interiorBump_eq_zero_of_ne hodd y y' hne.symm _ (orthantOffset_mem_centredCube S hodd y x hx)
      simp [normalizedBump, h0]
    simp only [gaugeMap]
    rw [Finset.sum_eq_single_of_mem y hy hz, adjointAction_sub, adjointAction_smul, adjointAction_inv_adjointAction]
    rfl
  change (1 / (cellSideLength F : ℝ) ^ 4) • ∑ x ∈ cellOffsets F,
    adjointAction (frameChange S V y (patchSite S y x))⁻¹ (gaugeMap S V R u (patchSite S y x)) = 0
  rw [Finset.sum_congr rfl hpoint, Finset.sum_sub_distrib, smul_sub, ← Finset.sum_smul, smul_smul]
  have hone : (1 / (cellSideLength F : ℝ) ^ 4) *
      ∑ x ∈ cellOffsets F, interiorBump (patchSite S y x) y / Dn = 1 := by
    rw [← Finset.sum_div, ← mul_div_assoc]
    exact div_self hDpos.ne'
  rw [hone, one_smul]
  exact sub_self _
theorem cellMeanFree_linear (a b : ℝ) (ξ ξ' : F.Site 0 → ℍ[ℝ]) (h : CellMeanFree S V ξ)
    (h' : CellMeanFree S V ξ') : CellMeanFree S V (fun x => a • ξ x + b • ξ' x) := by apply _root_.YangMills.Construction.GaugeMapLinear.cellMeanFree_linComb <;> assumption
theorem cellMeanFree_congr (hodd : Odd F.blockSide) (ξ ξ' : F.Site 0 → ℍ[ℝ])
    (he : ∀ s ∈ sitesOfCells S 0, ξ s = ξ' s) (h : CellMeanFree S V ξ) : CellMeanFree S V ξ' := by apply _root_.YangMills.Construction.GaugeMapLinear.cellMeanFree_congr <;> assumption
omit S V R in
theorem cellSumL2L4Norm_congr (S : Finset F.Cell) (w : F.Site 0 → ℝ) (f f' : F.Site 0 → Fin 4 → ℍ[ℝ])
    (he : ∀ b ∈ innerBonds S 0, f b.1 b.2 = f' b.1 b.2) : cellwiseL4Norm S w f = cellwiseL4Norm S w f' := by
  classical
  simp only [cellwiseL4Norm]
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  apply Finset.sum_congr rfl
  intro b hb
  have hb' : b ∈ innerBonds S 0 := by
    simp only [bondsOver, Finset.mem_filter] at hb
    exact hb.1
  rw [he b hb']
omit V R in
theorem innerBond_endpoints_mem (b : F.Site 0 × Fin 4) (hb : b ∈ innerBonds S 0) :
    b.1 ∈ sitesOfCells S 0 ∧ b.1 + unitStep 0 b.2 ∈ sitesOfCells S 0 := by
  simp only [innerBonds, Finset.mem_filter, Finset.mem_product] at hb
  exact ⟨hb.1.1, hb.2⟩
open Classical in
def extendByZero (A : Finset (F.Site 0)) : (↥A → ℍ[ℝ]) →ₗ[ℝ] (F.Site 0 → ℍ[ℝ]) where
  toFun x y := if h : y ∈ A then x ⟨y, h⟩ else 0
  map_add' x x' := by
    funext y
    by_cases h : y ∈ A <;> simp [h]
  map_smul' c x := by
    funext y
    by_cases h : y ∈ A <;> simp [h]
def restrictTo (A : Finset (F.Site 0)) : (F.Site 0 → ℍ[ℝ]) →ₗ[ℝ] (↥A → ℍ[ℝ]) where
  toFun g a := g a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def gaugeMapLinear : (F.Site 0 → Fin 4 → ℍ[ℝ]) →ₗ[ℝ] (F.Site 0 → ℍ[ℝ]) where
  toFun := gaugeMap S V R
  map_add' u u' := by
    have := gaugeMap_linear S V R 1 1 u u'
    simp only [one_smul] at this
    exact this
  map_smul' c u := by
    have := gaugeMap_linear S V R c 0 u u
    simp only [zero_smul, add_zero] at this
    exact this
def covariantDifferenceLinear : (F.Site 0 → ℍ[ℝ]) →ₗ[ℝ] (F.Site 0 → Fin 4 → ℍ[ℝ]) where
  toFun := covariantDiff R
  map_add' ξ ξ' := by
    funext x i
    simp only [covariantDiff, Pi.add_apply, adjointAction_add]
    abel
  map_smul' c ξ := by
    funext x i
    simp only [covariantDiff, Pi.smul_apply, adjointAction_smul, RingHom.id_apply, smul_sub]
omit V in
theorem extendByZero_apply_mem (A : Finset (F.Site 0)) (x : ↥A → ℍ[ℝ]) (a : ↥A) :
    _root_.YangMills.Construction.SliceDecomposition.extendByZero A x a = x a := by
  simp [_root_.YangMills.Construction.SliceDecomposition.extendByZero]
theorem re_extendByZero (A : Finset (F.Site 0)) (x : ↥A → ℍ[ℝ]) (hx : ∀ a, (x a).re = 0) (y : F.Site 0) :
    (_root_.YangMills.Construction.SliceDecomposition.extendByZero A x y).re = 0 := by
  by_cases h : y ∈ A
  · exact (by simpa using extendByZero_apply_mem (F := F) A x ⟨y, h⟩ ▸ hx ⟨y, h⟩)
  · simp [_root_.YangMills.Construction.SliceDecomposition.extendByZero, h]
def meanFreeSubmodule (hodd : Odd F.blockSide) : Submodule ℝ (↥(sitesOfCells S 0) → ℍ[ℝ]) where
  carrier := {x | CellMeanFree S V (_root_.YangMills.Construction.SliceDecomposition.extendByZero _ x) ∧ ∀ a, (x a).re = 0}
  add_mem' := by
    intro x x' hx hx'
    refine ⟨?_, fun a => ?_⟩
    · have := cellMeanFree_linear S V 1 1 _ _ hx.1 hx'.1
      simp only [one_smul] at this
      rw [map_add]
      exact this
    · have h1 := hx.2 a
      have h2 := hx'.2 a
      simp [h1, h2]
  zero_mem' := by
    refine ⟨?_, fun a => by simp⟩
    intro y _
    rw [map_zero]
    have := frameCellMean_linear S V 0 0 y 0 0
    simp only [zero_smul, add_zero] at this
    exact this
  smul_mem' := by
    intro c x hx
    refine ⟨?_, fun a => ?_⟩
    · have := cellMeanFree_linear S V c 0 _ _ hx.1 hx.1
      simp only [zero_smul, add_zero] at this
      rw [map_smul]
      exact this
    · have h1 := hx.2 a
      simp [h1]
end SliceDecomposition
open SliceDecomposition in
theorem SliceDecomposition.sliceDecomposition_of_gaugeMapOnDifferences
    (hG : gaugeMapOnDifferencesStatement) : sliceDecompositionStatement := by
  classical
  obtain ⟨c₀, C, L1, hc₀, hC, hG⟩ := hG
  refine ⟨min c₀ (1 / (2 * C)), max L1 5, lt_min hc₀ (by positivity), ?_⟩
  intro F m S hodd hLL hamb hm hreg s V hs hsc hcold u
  have h5 : 5 ≤ F.blockSide := le_trans (le_max_right _ _) hLL
  have hL : 0 < F.blockSide := by omega
  have hsC : C * s ≤ 1 / 2 := by
    have h1 : s ≤ 1 / (2 * C) := le_trans hsc (min_le_right _ _)
    calc C * s ≤ C * (1 / (2 * C)) := by gcongr
      _ = 1 / 2 := by field_simp
  set R := referenceFieldChain S V 0 with hR
  set w : F.Site 0 → ℝ := classWeight F (fun _ => 0) 0 0 0 with hw
  have hw1 : ∀ x, w x = 1 := by
    intro x
    simp [hw, classWeight]
  have key : ∀ ξ : F.Site 0 → ℍ[ℝ], CellMeanFree S V ξ →
      CellMeanFree S V (fun x => gaugeMap S V R (covariantDiff R ξ) x + ξ x) ∧
      cellwiseL4Norm S w (covariantDiff R (fun x => gaugeMap S V R (covariantDiff R ξ) x + ξ x)) ≤
        C * s * cellwiseL4Norm S w (covariantDiff R ξ) ∧
      Real.sqrt (∑ z ∈ S, cellSiteNorm 4 S w ξ z ^ 2) ≤
        C * (cellSideLength F : ℝ) * cellwiseL4Norm S w (covariantDiff R ξ) := by
    intro ξ hξ
    obtain ⟨_, hall⟩ := hG F m S hodd (le_trans (le_max_left _ _) hLL) hamb hm hreg s V hs
      (le_trans hsc (min_le_left _ _)) hcold
    obtain ⟨hA, hB, _⟩ := hall ξ hξ
    obtain ⟨hB1, hB2, _⟩ := hB (fun _ => 0) 0 0 0 (by norm_num) (by norm_num) (by simp)
    exact ⟨hA, hB1, hB2⟩
  set A := sitesOfCells S 0 with hA
  set Z := meanFreeSubmodule S V hodd with hZ
  set f : (↥A → ℍ[ℝ]) →ₗ[ℝ] (↥A → ℍ[ℝ]) :=
    restrictTo A ∘ₗ (gaugeMapLinear S V R ∘ₗ covariantDifferenceLinear R + LinearMap.id) ∘ₗ _root_.YangMills.Construction.SliceDecomposition.extendByZero A with hf
  have hfa : ∀ (x : ↥A → ℍ[ℝ]) (a : ↥A), f x a =
      gaugeMap S V R (covariantDiff R (_root_.YangMills.Construction.SliceDecomposition.extendByZero A x)) a + x a := by
    intro x a
    have : _root_.YangMills.Construction.SliceDecomposition.extendByZero A x a = x a := extendByZero_apply_mem A x a
    simp only [hf, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.id_apply]
    change gaugeMap S V R (covariantDiff R (_root_.YangMills.Construction.SliceDecomposition.extendByZero A x)) a + _root_.YangMills.Construction.SliceDecomposition.extendByZero A x a = _
    rw [this]
  have hext : ∀ (x : ↥A → ℍ[ℝ]) (y : F.Site 0) (hy : y ∈ A), _root_.YangMills.Construction.SliceDecomposition.extendByZero A x y = x ⟨y, hy⟩ :=
    fun x y hy => extendByZero_apply_mem A x ⟨y, hy⟩
  have hDre : ∀ ξ : F.Site 0 → ℍ[ℝ], (∀ y, (ξ y).re = 0) → ∀ x i, (covariantDiff R ξ x i).re = 0 := by
    intro ξ hξ x i
    simp only [covariantDiff, Quaternion.re_sub, re_adjointAction, hξ, sub_zero]
  have hmaps : ∀ x ∈ Z, f x ∈ Z := by
    intro x hx
    refine ⟨?_, fun a => ?_⟩
    · refine cellMeanFree_congr S V hodd _ _ ?_ (key _ hx.1).1
      intro y hy
      rw [hext (f x) y hy, hfa, hext x y hy]
    · rw [hfa, Quaternion.re_add, re_gaugeMap S V R _ (hDre _ (re_extendByZero A x hx.2)), hx.2 a, add_zero]
  set T : ↥Z →ₗ[ℝ] ↥Z := f.restrict hmaps with hT
  set G : ↥Z →ₗ[ℝ] ↥Z := LinearMap.id - T with hGd
  have hinj : Function.Injective G := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hxT : ∀ a : ↥A, gaugeMap S V R (covariantDiff R (_root_.YangMills.Construction.SliceDecomposition.extendByZero A x.1)) a = 0 := by
      intro a
      have h1 : (x - T x : ↥Z).1 a = 0 := by
        have : x - T x = 0 := hx
        rw [this]
        rfl
      have h2 : x.1 a - f x a = 0 := h1
      rw [hfa] at h2
      have h3 : x.1 a - (gaugeMap S V R (covariantDiff R (_root_.YangMills.Construction.SliceDecomposition.extendByZero A x.1)) a + x.1 a) =
          - gaugeMap S V R (covariantDiff R (_root_.YangMills.Construction.SliceDecomposition.extendByZero A x.1)) a := by abel
      rw [h3] at h2
      exact neg_eq_zero.1 h2
    set ξ := _root_.YangMills.Construction.SliceDecomposition.extendByZero A x.1 with hξ
    obtain ⟨_, hB, hP⟩ := key ξ x.2.1
    have hsame : cellwiseL4Norm S w
        (covariantDiff R (fun y => gaugeMap S V R (covariantDiff R ξ) y + ξ y)) =
        cellwiseL4Norm S w (covariantDiff R ξ) := by
      apply cellSumL2L4Norm_congr
      intro b hb
      obtain ⟨h1, h2⟩ := innerBond_endpoints_mem S b hb
      simp only [covariantDiff]
      rw [hxT ⟨_, h1⟩, hxT ⟨_, h2⟩]
      simp
    rw [hsame] at hB
    have hN0 : 0 ≤ cellwiseL4Norm S w (covariantDiff R ξ) := Real.sqrt_nonneg _
    have hN : cellwiseL4Norm S w (covariantDiff R ξ) = 0 := by
      nlinarith
    rw [hN, mul_zero] at hP
    have hP0 := le_antisymm hP (Real.sqrt_nonneg _)
    have hP1 := (Real.sqrt_eq_zero (Finset.sum_nonneg fun z _ => by positivity)).1 hP0
    have hP2 := (Finset.sum_eq_zero_iff_of_nonneg (fun z _ => by positivity)).1 hP1
    apply Subtype.ext
    funext a
    have hz := enclosingCell_mem S hodd a.1 a.2
    have h3 := hP2 _ hz
    have h4 : cellSiteNorm 4 S w ξ (enclosingCell a.1) = 0 := by simpa using h3
    simp only [cellSiteNorm] at h4
    have hsum0 : 0 ≤ ∑ x ∈ (sitesOfCells S 0).filter (fun x => enclosingCell x = enclosingCell a.1),
        (w x * ‖ξ x‖) ^ (4 : ℝ) :=
      Finset.sum_nonneg fun y _ => by
        rw [hw1, one_mul]
        positivity
    have h4' := (Real.rpow_eq_zero hsum0 (by norm_num)).1 h4
    have h5 := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => by
      rw [hw1, one_mul]
      positivity)).1 h4' a.1 (Finset.mem_filter.2 ⟨a.2, rfl⟩)
    rw [hw1, one_mul] at h5
    have h6 : ‖ξ a.1‖ = 0 := (Real.rpow_eq_zero (norm_nonneg _) (by norm_num)).1 h5
    have h7 : ξ a.1 = 0 := norm_eq_zero.1 h6
    rw [hξ, extendByZero_apply_mem A _ a] at h7
    exact h7
  have hsurj : Function.Surjective G := LinearMap.injective_iff_surjective.1 hinj
  set uq : F.Site 0 → Fin 4 → ℍ[ℝ] := fun x i => (u x i : ℍ[ℝ]) with huq
  have huqre : ∀ x i, (uq x i).re = 0 := fun x i => (u x i).2
  have hnegre : ∀ x i, ((-uq) x i).re = 0 := by
    intro x i
    simp [huqre]
  have hbmem : restrictTo A (gaugeMapLinear S V R (-uq)) ∈ Z := by
    refine ⟨?_, fun a => re_gaugeMap S V R _ hnegre _⟩
    refine cellMeanFree_congr S V hodd _ _ ?_ (cellMeanFree_gaugeMap S V R hodd hL (-uq))
    intro y hy
    rw [hext _ y hy]
    rfl
  obtain ⟨x, hx⟩ := hsurj ⟨_, hbmem⟩
  set ξ := _root_.YangMills.Construction.SliceDecomposition.extendByZero A x.1 with hξ
  have hxa : ∀ a : ↥A, - gaugeMap S V R (covariantDiff R ξ) a = gaugeMap S V R (-uq) a := by
    intro a
    have h1 : (x - T x : ↥Z).1 a = gaugeMap S V R (-uq) a := by
      have : x - T x = ⟨_, hbmem⟩ := hx
      rw [this]
      rfl
    have h2 : x.1 a - f x a = gaugeMap S V R (-uq) a := h1
    rw [hfa] at h2
    rw [← h2]
    abel
  have hre : ∀ y, (ξ y).re = 0 := re_extendByZero A _ x.2.2
  refine ⟨fun y i => ⟨uq y i - covariantDiff R ξ y i, ?_⟩, ξ, ?_, x.2.1, hre, ?_⟩
  · change (uq y i - covariantDiff R ξ y i).re = 0
    rw [Quaternion.re_sub, huqre, hDre ξ hre]
    simp
  · intro a ha
    have h1 := hxa ⟨a, ha⟩
    have h2 := congrFun (gaugeMap_linear S V R 1 (-1) uq (covariantDiff R ξ)) a
    have h3 := congrFun (gaugeMap_linear S V R (-1) 0 uq uq) a
    simp only [one_smul, neg_smul, zero_smul, add_zero] at h2 h3
    change gaugeMap S V R (fun y i => uq y i - covariantDiff R ξ y i) a = 0
    have e1 : (fun y i => uq y i - covariantDiff R ξ y i) =
        fun y i => uq y i + -covariantDiff R ξ y i := by
      funext y i
      exact sub_eq_add_neg _ _
    have e2 : (fun y i => -uq y i) = -uq := rfl
    rw [e1, h2]
    rw [e2] at h3
    have h1' : - gaugeMap S V R (covariantDiff R ξ) a = - gaugeMap S V R uq a := by
      rw [h1, h3]
    have h1'' := neg_injective h1'
    rw [h1'']
    abel
  · intro x' i
    change uq x' i = (uq x' i - covariantDiff R ξ x' i) + covariantDiff R ξ x' i
    abel
end YangMills.Construction
end
