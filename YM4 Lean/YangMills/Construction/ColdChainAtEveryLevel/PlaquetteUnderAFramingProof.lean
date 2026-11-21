import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
import YangMills.Construction.ColdChainAtEveryLevel.ChartOverAnotherTopProof
import YangMills.Construction.ColdChainAtEveryLevel.PlaquetteUnderAFraming
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
namespace PinnedPlaquette
variable {F : BlockFrame}
def blockSite (y : F.Cell) (h : LatticeFractionalIntegration.Lattice4) : F.Site F.depth :=
  cellCentre F.depth y + siteOfCoords F.depth h
theorem enclosingCell_cellCentre_add (hL : Odd F.blockSide) {j : ℕ} (z : F.Cell) (h : Fin 4 → ℤ)
    (hh : h ∈ centredCube (F.blockSide ^ (F.top - j))) :
    enclosingCell (cellCentre j z + siteOfCoords j h : F.Site j) = z := by apply _root_.YangMills.Construction.BlockLines.enclosingCell_cellCentre_add <;> assumption
theorem enclosingCell_blockSite (hL : Odd F.blockSide) (y : F.Cell) {h : LatticeFractionalIntegration.Lattice4}
    (hh : h ∈ centredCube F.blockSide) : enclosingCell (blockSite y h) = y := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.enclosingCell_blockPoint <;> assumption
theorem blockSite_add_unitStep (y : F.Cell) (h : LatticeFractionalIntegration.Lattice4) (i : Fin 4) :
    blockSite y h + unitStep F.depth i = blockSite y (h + LatticeFractionalIntegration.basisVector i) := by apply _root_.YangMills.Construction.GaugeFixing.cellCentre_add_siteOfCoords_add_unitStep <;> assumption
theorem blockSite_cell_add (y : F.Cell) (h o : LatticeFractionalIntegration.Lattice4) :
    blockSite (y + siteOfCoords F.top o) h = blockSite y (h + (F.blockSide : ℤ) • o) := by
  have e := cellCentre_add F.depth (by simp [BlockFrame.top]) y o
  have e2 : (fun l => (F.blockSide : ℤ) ^ (F.top - F.depth) * o l) = (F.blockSide : ℤ) • o := by
    funext l
    simp
  rw [e2] at e
  simp only [blockSite]
  rw [e, siteOfCoords_add]
  abel
theorem exists_blockSite_of_mem {S : Finset F.Cell} {x : F.Site F.depth} (hx : x ∈ sitesOfCells S F.depth) :
    ∃ y ∈ S, ∃ h ∈ centredCube F.blockSide, x = blockSite y h := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.exists_blockPoint <;> assumption
theorem mem_innerBonds {S : Finset F.Cell} {j : ℕ} {b : F.Site j × Fin 4} :
    b ∈ innerBonds S j ↔ b.1 ∈ sitesOfCells S j ∧ b.1 + unitStep j b.2 ∈ sitesOfCells S j := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.mem_innerBonds <;> assumption
theorem norm_coe_mul_inv_sub_one (a b : UnitQuaternion) :
    ‖((a * b⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ = ‖(a : ℍ[ℝ]) - (b : ℍ[ℝ])‖ := by apply _root_.YangMills.Construction.GaugeFixing.norm_mul_inv_sub_one <;> assumption
theorem norm_coe_mul_sub_coe_mul_le (a a' b b' : UnitQuaternion) :
    ‖((a * b : UnitQuaternion) : ℍ[ℝ]) - ((a' * b' : UnitQuaternion) : ℍ[ℝ])‖ ≤
      ‖(a : ℍ[ℝ]) - a'‖ + ‖(b : ℍ[ℝ]) - b'‖ := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.coe_mul_sub_mul_le <;> assumption
theorem norm_coe_inv_sub_coe_inv (a b : UnitQuaternion) :
    ‖((a⁻¹ : UnitQuaternion) : ℍ[ℝ]) - ((b⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ = ‖(a : ℍ[ℝ]) - b‖ := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.norm_sub_inv_inv <;> assumption
theorem chartChain_depth (R : F.FieldChain) (U : ChainChart F) (V : F.GaugeField F.top) :
    chartChain R U V F.depth = chartField R U F.depth := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.chartChain_depth <;> assumption
theorem baseSite_mem_patch_of_near {S : Finset F.Cell} {z : F.Cell} (hamb : IsAdmissibleAmbient F)
    (hsign : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) (hodd : Odd F.blockSide)
    {o w : LatticeFractionalIntegration.Lattice4}
    (hv : z + siteOfCoords F.top o ∈ S) (ho : ∀ i, o i = 0 ∨ o i = 1)
    (hw0 : ∀ i, o i = 0 → |w i| ≤ ((F.blockSide : ℤ) - 1) / 2)
    (hw1 : ∀ i, o i = 1 → w i = ((F.blockSide : ℤ) - 1) / 2 + 1) :
    baseSite (blockSite z w) ∈ (GaugeMap.patchDomain S z).image (GaugeMap.patchSite S z) := by
  classical
  have hLp : (0 : ℤ) < (F.blockSide : ℤ) := by exact_mod_cast hodd.pos
  set P : ℤ := (F.blockSide : ℤ) ^ F.depth with hP
  have hPpos : 1 ≤ P := one_le_pow₀ (by omega)
  obtain ⟨m, hm⟩ := id hodd
  have hmz : (F.blockSide : ℤ) = 2 * (m : ℤ) + 1 := by exact_mod_cast hm
  have hM : ((F.blockSide : ℤ) - 1) / 2 = m := by omega
  rw [hM] at hw0 hw1
  have hcs : GaugeMap.cellSideLength F = 2 * (P * m) + P := by
    have e : GaugeMap.cellSideLength F = P * (F.blockSide : ℤ) := by
      simp only [GaugeMap.cellSideLength, BlockFrame.top, pow_succ, hP]
    rw [e, hmz]
    ring
  have hq0 : 0 ≤ P * (m : ℤ) := mul_nonneg (by omega) (by omega)
  have hb : ∀ i, (o i = 0 ∧ |P * w i| ≤ P * m) ∨ (o i = 1 ∧ P * w i = P * m + P) := by
    intro i
    rcases ho i with h0 | h1
    · left
      refine ⟨h0, ?_⟩
      rw [abs_mul, abs_of_pos (by omega : (0 : ℤ) < P)]
      exact mul_le_mul_of_nonneg_left (hw0 i h0) (by omega)
    · right
      refine ⟨h1, ?_⟩
      rw [hw1 i h1]
      ring
  set xl : LatticeFractionalIntegration.Lattice4 :=
    fun i => closedOrthant S z i * (P * w i) + (GaugeMap.cellSideLength F - 1) / 2 with hxl
  have hbig : ∀ i, -(10 * GaugeMap.cellSideLength F) ≤ xl i ∧ xl i ≤ 21 * GaugeMap.cellSideLength F - 1 := by
    intro i
    simp only [hxl]
    rw [hcs]
    rcases hb i with ⟨-, h1⟩ | ⟨-, h1⟩
    · have h2 := abs_le.1 h1
      generalize P * w i = u at h2
      generalize P * (m : ℤ) = q at h2 hq0
      rcases hsign i with e | e <;> rw [e] <;> constructor <;> omega
    · generalize P * w i = u at h1
      generalize P * (m : ℤ) = q at h1 hq0
      rcases hsign i with e | e <;> rw [e] <;> constructor <;> omega
  have ho32 : ∀ i, |o i| < 32 := by
    intro i
    rcases ho i with h | h <;> rw [h] <;> norm_num
  refine Finset.mem_image.2 ⟨xl, ?_, ?_⟩
  · unfold GaugeMap.patchDomain
    refine Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun i => Finset.mem_Icc.2 (hbig i),
      ⟨fun i => closedOrthant S z i * o i * GaugeMap.cellSideLength F, ?_, fun i => ?_⟩⟩
    · unfold GaugeMap.patchCorners
      refine Finset.mem_image.2 ⟨z + siteOfCoords F.top o, ?_, ?_⟩
      · unfold cellBall
        refine Finset.mem_filter.2 ⟨hv, ?_⟩
        have := cellSupDist_add_le (F := F) hamb (z + siteOfCoords F.top o) (a := - o) (r := 10) (by norm_num)
          (fun i => by
            rcases ho i with h | h <;> simp [h])
        have e : z + siteOfCoords F.top o + siteOfCoords F.top (- o) = z := by
          rw [siteOfCoords_neg]
          abel
        rw [e] at this
        exact this
      · funext i
        rw [cellDisplacement_add_siteOfCoords hamb z ho32]
    · simp only [hxl]
      rw [hcs]
      rcases hb i with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · have h2 := abs_le.1 h1
        rw [h0]
        generalize P * w i = u at h2
        generalize P * (m : ℤ) = q at h2 hq0
        rcases hsign i with e | e <;> rw [e] <;> simp only [mul_zero, zero_mul] <;> omega
      · rw [h0, h1]
        generalize P * (m : ℤ) = q at hq0
        rcases hsign i with e | e <;> rw [e] <;> omega
  · have e1 : baseSite (blockSite z w) = cellCentre 0 z + siteOfCoords 0 (fun i => P * w i) := by
      simp only [blockSite]
      rw [baseSite_add F.depth (by simp [BlockFrame.top]), baseSite_cellCentre F.depth (by simp [BlockFrame.top])]
    rw [e1]
    unfold GaugeMap.patchSite
    congr 2
    funext i
    simp only [hxl, add_sub_cancel_right]
    rcases hsign i with e | e <;> rw [e] <;> ring
theorem baseSite_corner_mem_patch {S : Finset F.Cell} {z : F.Cell} (hamb : IsAdmissibleAmbient F)
    (hsign : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) (hodd : Odd F.blockSide)
    {h δ : LatticeFractionalIntegration.Lattice4} (hh : h ∈ centredCube F.blockSide)
    (hδ : ∀ i, δ i = 0 ∨ δ i = 1) (hmem : blockSite z (h + δ) ∈ sitesOfCells S F.depth) :
    baseSite (blockSite z (h + δ)) ∈ (GaugeMap.patchDomain S z).image (GaugeMap.patchSite S z) := by
  classical
  obtain ⟨m, hm⟩ := id hodd
  have hM : ((F.blockSide : ℤ) - 1) / 2 = m := by omega
  have hc := (LatticePaths.mem_centredCube_iff F.blockSide h).1 hh
  rw [hM] at hc
  set w := h + δ with hw
  set o : LatticeFractionalIntegration.Lattice4 := fun i => if (m : ℤ) < w i then 1 else 0 with ho
  have hwi : ∀ i, -(m : ℤ) ≤ w i ∧ w i ≤ m + 1 := by
    intro i
    have h1 := hc i
    have h2 : w i = h i + δ i := rfl
    rcases hδ i with e | e <;> rw [h2, e] <;> omega
  have ho01 : ∀ i, o i = 0 ∨ o i = 1 := by
    intro i
    simp only [ho]
    split_ifs <;> simp
  have hu : w - (F.blockSide : ℤ) • o ∈ centredCube F.blockSide := by
    rw [LatticePaths.mem_centredCube_iff, hM]
    intro i
    have h1 := hwi i
    have hz : (F.blockSide : ℤ) = 2 * (m : ℤ) + 1 := by exact_mod_cast hm
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ho]
    split_ifs with hcase
    · rw [hz]
      constructor <;> omega
    · simp only [mul_zero, sub_zero]
      constructor <;> omega
  have hsite : blockSite z w = blockSite (z + siteOfCoords F.top o) (w - (F.blockSide : ℤ) • o) := by
    rw [blockSite_cell_add, sub_add_cancel]
  have hv : z + siteOfCoords F.top o ∈ S := by
    obtain ⟨y', hy', u, hu', e'⟩ := exists_blockSite_of_mem hmem
    have h1 : enclosingCell (blockSite z w) = z + siteOfCoords F.top o := by
      rw [hsite, enclosingCell_blockSite hodd _ hu]
    have h2 : enclosingCell (blockSite z w) = y' := by
      rw [e', enclosingCell_blockSite hodd y' hu']
    rw [← h1, h2]
    exact hy'
  refine baseSite_mem_patch_of_near hamb hsign hodd hv ho01 (fun i h0 => ?_) (fun i h1 => ?_)
  · rw [hM]
    have h1 := hwi i
    have h2 : ¬ (m : ℤ) < w i := by
      intro hlt
      simp only [ho, if_pos hlt] at h0
      omega
    rw [abs_le]
    constructor <;> omega
  · rw [hM]
    have h3 := hwi i
    have h2 : (m : ℤ) < w i := by
      by_contra hlt
      simp only [ho, if_neg hlt] at h1
      omega
    omega
end PinnedPlaquette
theorem pinnedGaugePlaquetteBound : pinnedGaugePlaquetteBoundStatement := by
  classical
  intro a θ del Ca _ _ _ _ _ _
  refine ⟨1, fun L hL _ C₁ C _ hC => ⟨1, 4 * C, one_pos, by positivity, ?_⟩⟩
  intro F m S hFL hamb hm hreg s V _ _ _ U _ X k Γ z _ hz hfr p hp hpz
  have hodd : Odd F.blockSide := hFL ▸ hL
  have hsign := (closedOrthant_spec hreg (by omega) z).1
  set W := chartChain (referenceFieldChain S V) U V with hW
  set E := relativeEnergy a S z W (chartGauge (referenceFieldChain S V) U) X k Γ with hE
  set D := C * Real.sqrt E with hD
  have hD0 : 0 ≤ D := by positivity
  have hcl := hfr.2.2.1 F.depth (by simp [BlockFrame.top])
  set A := gaugedChainFields X Γ F.depth with hA
  set Y := chartField (referenceFieldChain S V) U F.depth with hY
  have hWt : W F.depth = Y := PinnedPlaquette.chartChain_depth _ _ _
  have hbond : ∀ (x : F.Site F.depth) (i : Fin 4), x ∈ sitesOfCells S F.depth →
      x + unitStep F.depth i ∈ sitesOfCells S F.depth →
      baseSite x ∈ patchBaseSites S z → baseSite (x + unitStep F.depth i) ∈ patchBaseSites S z →
      ‖((A x i : UnitQuaternion) : ℍ[ℝ]) - ((Y x i : UnitQuaternion) : ℍ[ℝ])‖ ≤ D := by
    intro x i h1 h2 h3 h4
    have hbm : ((x, i) : F.Site F.depth × Fin 4) ∈ innerBonds S F.depth :=
      PinnedPlaquette.mem_innerBonds.2 ⟨h1, h2⟩
    have t := le_trans (Finset.single_le_sum (s := innerBonds S F.depth)
      (by intro b _; split_ifs <;> positivity) hbm) hcl
    dsimp only at t
    rw [if_pos ⟨h3, h4⟩, hWt, PinnedPlaquette.norm_coe_mul_inv_sub_one] at t
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hD0 (by norm_num)).1 t
  obtain ⟨x, μ, ν⟩ := p
  have hpm := Finset.mem_filter.1 hp
  have hlt : μ < ν := hpm.2.1
  have hcorn := hpm.2.2
  have c0 : x ∈ sitesOfCells S F.depth := hcorn (by simp [plaquetteCorners])
  have c1 : x + unitStep F.depth μ ∈ sitesOfCells S F.depth := hcorn (by simp [plaquetteCorners])
  have c2 : x + unitStep F.depth ν ∈ sitesOfCells S F.depth := hcorn (by simp [plaquetteCorners])
  have c3 : x + unitStep F.depth μ + unitStep F.depth ν ∈ sitesOfCells S F.depth :=
    hcorn (by simp [plaquetteCorners])
  obtain ⟨y, -, h, hh, rfl⟩ := PinnedPlaquette.exists_blockSite_of_mem c0
  have hyz : y = z := by
    rw [← hpz]
    exact (PinnedPlaquette.enclosingCell_blockSite hodd y hh).symm
  subst hyz
  have bareOf : ∀ δ : LatticeFractionalIntegration.Lattice4, (∀ i, δ i = 0 ∨ δ i = 1) →
      PinnedPlaquette.blockSite y (h + δ) ∈ sitesOfCells S F.depth →
      baseSite (PinnedPlaquette.blockSite y (h + δ)) ∈ patchBaseSites S y := by
    intro δ hδ hmem
    have := PinnedPlaquette.baseSite_corner_mem_patch hamb hsign hodd hh hδ hmem
    unfold patchBaseSites
    obtain ⟨l, hl, e⟩ := Finset.mem_image.1 this
    exact Finset.mem_image.2 ⟨l, hl, e⟩
  have unit01 : ∀ (l i : Fin 4), LatticeFractionalIntegration.basisVector l i = 0 ∨
      LatticeFractionalIntegration.basisVector l i = 1 := by
    intro l i
    by_cases hli : i = l
    · subst hli
      simp [LatticeFractionalIntegration.basisVector]
    · simp [LatticeFractionalIntegration.basisVector, hli]
  have e0 : PinnedPlaquette.blockSite y h = PinnedPlaquette.blockSite y (h + 0) := by
    rw [add_zero]
  have e1 := PinnedPlaquette.blockSite_add_unitStep y h μ
  have e2 := PinnedPlaquette.blockSite_add_unitStep y h ν
  have e3 : PinnedPlaquette.blockSite y h + unitStep F.depth μ + unitStep F.depth ν =
      PinnedPlaquette.blockSite y (h + (LatticeFractionalIntegration.basisVector μ +
        LatticeFractionalIntegration.basisVector ν)) := by
    rw [e1, PinnedPlaquette.blockSite_add_unitStep, add_assoc]
  have b0 : baseSite (PinnedPlaquette.blockSite y h) ∈ patchBaseSites S y := by
    have := bareOf 0 (fun i => Or.inl rfl) (by rw [← e0]; exact c0)
    rwa [← e0] at this
  have b1 : baseSite (PinnedPlaquette.blockSite y h + unitStep F.depth μ) ∈ patchBaseSites S y := by
    rw [e1]
    exact bareOf _ (unit01 μ) (by rw [← e1]; exact c1)
  have b2 : baseSite (PinnedPlaquette.blockSite y h + unitStep F.depth ν) ∈ patchBaseSites S y := by
    rw [e2]
    exact bareOf _ (unit01 ν) (by rw [← e2]; exact c2)
  have b3 : baseSite (PinnedPlaquette.blockSite y h + unitStep F.depth μ + unitStep F.depth ν) ∈
      patchBaseSites S y := by
    rw [e3]
    refine bareOf _ (fun i => ?_) (by rw [← e3]; exact c3)
    have hne : μ ≠ ν := ne_of_lt hlt
    by_cases h1 : i = μ
    · subst h1
      right
      simp [LatticeFractionalIntegration.basisVector, hne]
    · by_cases h2 : i = ν
      · subst h2
        right
        simp [LatticeFractionalIntegration.basisVector, h1]
      · left
        simp [LatticeFractionalIntegration.basisVector, h1, h2]
  set x := PinnedPlaquette.blockSite y h with hx
  have s3 : x + unitStep F.depth μ + unitStep F.depth ν - unitStep F.depth μ = x + unitStep F.depth ν := by abel
  have s4 : x + unitStep F.depth μ + unitStep F.depth ν + - unitStep F.depth μ - unitStep F.depth ν = x := by abel
  have expand : ∀ Z : F.GaugeField F.depth, plaquetteHolonomy Z (x, μ, ν) =
      Z x μ * (Z (x + unitStep F.depth μ) ν * ((Z (x + unitStep F.depth ν) μ)⁻¹ * ((Z x ν)⁻¹ * 1))) := by
    intro Z
    simp only [plaquetteHolonomy, pathHolonomy, stepDisplacement, linkValue, if_true, Bool.false_eq_true, if_false]
    rw [s3, s4]
  have d1 := hbond x μ c0 c1 b0 b1
  have d2 := hbond (x + unitStep F.depth μ) ν c1 c3 b1 b3
  have d3 := hbond (x + unitStep F.depth ν) μ c2 (by rw [add_right_comm]; exact c3) b2
    (by rw [add_right_comm]; exact b3)
  have d4 := hbond x ν c0 c2 b0 b2
  show ‖((plaquetteHolonomy A (x, μ, ν) : UnitQuaternion) : ℍ[ℝ]) -
    ((plaquetteHolonomy Y (x, μ, ν) : UnitQuaternion) : ℍ[ℝ])‖ ≤ 4 * C * Real.sqrt E
  rw [expand, expand]
  have t1 := PinnedPlaquette.norm_coe_mul_sub_coe_mul_le (A x μ) (Y x μ)
    (A (x + unitStep F.depth μ) ν * ((A (x + unitStep F.depth ν) μ)⁻¹ * ((A x ν)⁻¹ * 1)))
    (Y (x + unitStep F.depth μ) ν * ((Y (x + unitStep F.depth ν) μ)⁻¹ * ((Y x ν)⁻¹ * 1)))
  have t2 := PinnedPlaquette.norm_coe_mul_sub_coe_mul_le (A (x + unitStep F.depth μ) ν)
    (Y (x + unitStep F.depth μ) ν)
    ((A (x + unitStep F.depth ν) μ)⁻¹ * ((A x ν)⁻¹ * 1)) ((Y (x + unitStep F.depth ν) μ)⁻¹ * ((Y x ν)⁻¹ * 1))
  have t3 := PinnedPlaquette.norm_coe_mul_sub_coe_mul_le (A (x + unitStep F.depth ν) μ)⁻¹
    (Y (x + unitStep F.depth ν) μ)⁻¹ ((A x ν)⁻¹ * 1) ((Y x ν)⁻¹ * 1)
  have t4 : ‖(((A x ν)⁻¹ * 1 : UnitQuaternion) : ℍ[ℝ]) - (((Y x ν)⁻¹ * 1 : UnitQuaternion) : ℍ[ℝ])‖ ≤ D := by
    simp only [mul_one]
    rw [PinnedPlaquette.norm_coe_inv_sub_coe_inv]
    exact d4
  have t5 : ‖(((A (x + unitStep F.depth ν) μ)⁻¹ : UnitQuaternion) : ℍ[ℝ]) -
      (((Y (x + unitStep F.depth ν) μ)⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ ≤ D := by
    rw [PinnedPlaquette.norm_coe_inv_sub_coe_inv]
    exact d3
  have e4 : 4 * C * Real.sqrt E = 4 * D := by
    simp only [hD]
    ring
  rw [e4]
  linarith
end YangMills.Construction.BlockAverages
end
