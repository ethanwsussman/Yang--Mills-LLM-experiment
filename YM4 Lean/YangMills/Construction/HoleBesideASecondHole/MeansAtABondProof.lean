import YangMills.Construction.ColdStepAtMirrorFrames.BlockEnergyAtTheLeastChartProof
import YangMills.Construction.HoleBesideASecondHole.ContoursAgreeWithTheStraightBond
import YangMills.Construction.HoleBesideASecondHole.MeanOfATurnedVariable
import YangMills.Construction.HoleBesideASecondHole.MeansAtABond
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages PathHolonomy LumpContours GroupMeans TurnedMeans BondContours BlockTrees SquareDescent
namespace BondMeans
variable {F : BlockFrame}
theorem top_sub_depth : F.top - F.depth = 1 := by simp [BlockFrame.top]
theorem cellCentre_eq_refineSite (y : F.Cell) : cellCentre F.depth y = refineSite y := by
  funext k
  simp only [cellCentre, refineSite, siteOfCoords, top_sub_depth, pow_one]
theorem period_depth (i : Fin 4) : F.period F.depth i = F.extent i * F.blockSide := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.MinimizingChart.period_depth <;> assumption
theorem siteOfCoords_minimalOffset {j : ℕ} (x x' : F.Site j) :
    siteOfCoords j (minimalOffset x x') = x' - x := by
  funext k
  simp [siteOfCoords, minimalOffset, ZMod.coe_valMinAbs]
theorem minimalOffset_add_siteOfCoords (hL : Odd F.blockSide) (hS : ∀ i, 64 ≤ F.extent i)
    (x : F.Site F.depth) {o o' : Fin 4 → ℤ}
    (ho : o ∈ centredCube F.blockSide) (ho' : o' ∈ centredCube F.blockSide) :
    minimalOffset (x + siteOfCoords F.depth o) (x + siteOfCoords F.depth o') = o' - o := by
  funext i
  have hpos := hL.pos
  have hs := hS i
  have hp : (64 : ℤ) * F.blockSide ≤ (F.period F.depth i : ℤ) := by
    rw [period_depth]
    push_cast
    have : (64 : ℤ) ≤ F.extent i := by exact_mod_cast hs
    nlinarith
  haveI : NeZero (F.period F.depth i) := ⟨by
    intro h0
    rw [h0] at hp
    have : (0 : ℤ) < F.blockSide := by exact_mod_cast hpos
    simp at hp
    omega⟩
  have a1 := abs_le.1 (offsetInBlock_of_mem_centredCube ho i)
  have a2 := abs_le.1 (offsetInBlock_of_mem_centredCube ho' i)
  have e : (x + siteOfCoords F.depth o' - (x + siteOfCoords F.depth o) : F.Site F.depth) i =
      (((o' i - o i : ℤ)) : ZMod (F.period F.depth i)) := by
    simp [siteOfCoords]
  show ((x + siteOfCoords F.depth o' - (x + siteOfCoords F.depth o) : F.Site F.depth) i).valMinAbs = o' i - o i
  rw [e]
  refine (ZMod.valMinAbs_spec _ _).2 ⟨rfl, ?_⟩
  obtain ⟨k, hk⟩ := hL
  have hhalf : ((F.blockSide : ℤ) - 1) / 2 = k := by
    rw [hk]
    push_cast
    omega
  rw [hhalf] at a1 a2
  simp only [Set.mem_Ioc]
  constructor <;> omega
theorem baseLeg_eq_axisPath (hL : Odd F.blockSide) (hS : ∀ i, 64 ≤ F.extent i)
    (b : F.Cell → F.Site F.depth) (y : F.Cell)
    {ob : Fin 4 → ℤ} (hob : ob ∈ centredCube F.blockSide) (hb : b y = refineSite y + siteOfCoords F.depth ob)
    {e : (Fin 4 → ℤ) × Equiv.Perm (Fin 4)} (he : e.1 ∈ centredCube F.blockSide) :
    baseLeg b y e = axisPath (e.1 - ob) e.2 := by
  unfold baseLeg
  rw [hb, cellCentre_eq_refineSite, minimalOffset_add_siteOfCoords hL hS _ hob he]
theorem blockTreeTransport_zero {j : ℕ} (X : F.GaugeField j) (y : F.Site (j + 1)) :
    blockTreeTransport X y 0 = 1 := by
  simp [blockTreeTransport, axisPath_eq_segments, axisPathSegment, pathHolonomy]
theorem zero_mem_centredCube (hL : Odd F.blockSide) : (0 : Fin 4 → ℤ) ∈ centredCube F.blockSide := by apply _root_.YangMills.Construction.GaugeFixing.zero_mem_centredCube <;> assumption
theorem natAbs_lt_period (hL : Odd F.blockSide) (hS : ∀ i, 64 ≤ F.extent i) {o : Fin 4 → ℤ}
    (ho : o ∈ centredCube F.blockSide) (k : Fin 4) :
    (o k).natAbs < F.period F.depth k := by
  have h1 := abs_le.1 (offsetInBlock_of_mem_centredCube ho k)
  have hpos := hL.pos
  have hs := hS k
  rw [period_depth]
  have h2 : 64 * F.blockSide ≤ F.extent k * F.blockSide := Nat.mul_le_mul_right _ hs
  have h3 : (((F.blockSide : ℤ) - 1) / 2) ≤ F.blockSide := by omega
  omega
theorem exists_legRotation_near (hl : LegNearBlockTree) (hL : Odd F.blockSide) (hS : ∀ i, 64 ≤ F.extent i)
    (Wt Wp : F.GaugeField F.depth) (b : F.Cell → F.Site F.depth) (y : F.Cell)
    (Ds Q : Finset (F.Site F.depth)) (κ K : ℝ) (N : ℕ)
    (hK : 0 ≤ K) (hb : b y ∈ sitesBelow F.depth y) (hκ : blockCurvatureNorm Wt y ≤ κ)
    (hnear : LinksClose Wp Wt Ds Q K) (hQ : sitesBelow F.depth y ⊆ Q)
    (hcount : ∀ k, (Ds.image fun z => z k).card ≤ N) :
    ∃ T : UnitQuaternion, ∀ e ∈ allContours F,
      ‖((legRotation Wt Wp b y e : UnitQuaternion) : ℍ[ℝ]) - (T : ℍ[ℝ])‖ ≤
        32 * (F.blockSide : ℝ) * κ + 8 * N * K := by
  obtain ⟨ob, hob, hby⟩ := exists_offset_of_mem_sitesBelow F.depth y hb
  have hA : IsAdmissibleAmbient F := Or.inr hS
  have hj : F.depth < F.top := by simp [BlockFrame.top]
  refine ⟨(blockTreeTransport Wt y ob)⁻¹, ?_⟩
  intro e he
  have hξ : e.1 ∈ centredCube F.blockSide := (Finset.mem_product.1 he).1
  set t := blockTreeTransport Wt y e.1 with ht
  set a := pathHolonomy Wt (b y) (baseLeg b y e) with ha
  set w := pathHolonomy Wp (refineSite y) (axisPath e.1 e.2) with hw
  set wt := pathHolonomy Wt (refineSite y) (axisPath e.1 e.2) with hwt
  have scale : 16 * (F.blockSide : ℝ) * blockCurvatureNorm Wt y ≤ 16 * (F.blockSide : ℝ) * κ :=
    mul_le_mul_of_nonneg_left hκ (by positivity)
  have h1 : ‖(a : ℍ[ℝ]) - (((blockTreeTransport Wt y ob)⁻¹ * t : UnitQuaternion) : ℍ[ℝ])‖ ≤
      16 * (F.blockSide : ℝ) * κ := by
    have h := hl F F.depth hj hL hA Wt y ob e.1 e.2 hob hξ
    rw [← hby, ← baseLeg_eq_axisPath hL hS b y hob hby hξ] at h
    exact h.trans scale
  have h2 : ‖(wt : ℍ[ℝ]) - (t : ℍ[ℝ])‖ ≤ 16 * (F.blockSide : ℝ) * κ := by
    have h := hl F F.depth hj hL hA Wt y 0 e.1 e.2 (zero_mem_centredCube hL) hξ
    simp only [_root_.YangMills.Construction.PathHolonomy.siteOfCoords_zero, add_zero, sub_zero, blockTreeTransport_zero, inv_one, one_mul] at h
    exact h.trans scale
  have h3 : ‖(w : ℍ[ℝ]) - (wt : ℍ[ℝ])‖ ≤ 8 * N * K := by
    have hin : ∀ z ∈ pathSites (refineSite y) (axisPath e.1 e.2), z ∈ Q := by
      intro z hz
      have h := axisPath_sites_mem_sitesBelow F.depth y
        (offsetInBlock_of_mem_centredCube (zero_mem_centredCube hL)) (offsetInBlock_of_mem_centredCube hξ) e.2
      simp only [_root_.YangMills.Construction.PathHolonomy.siteOfCoords_zero, add_zero, sub_zero] at h
      exact hQ (h z hz)
    have p := norm_pathHolonomy_sub_le Wp Wt Ds Q K hK hnear (axisPath e.1 e.2) (refineSite y) hin
    have q := touchCount_axisPath_le Ds (refineSite y) e.1 e.2 N (natAbs_lt_period hL hS hξ) hcount
    have q' : (touchCount Ds (refineSite y) (axisPath e.1 e.2) : ℝ) ≤ 8 * N := by exact_mod_cast q
    calc _ ≤ K * touchCount Ds (refineSite y) (axisPath e.1 e.2) := p
      _ ≤ K * (8 * N) := mul_le_mul_of_nonneg_left q' hK
      _ = 8 * N * K := by ring
  have hturn : legRotation Wt Wp b y e = a * w⁻¹ := by
    unfold legRotation
    rw [cellCentre_eq_refineSite]
  rw [hturn]
  set Tt := (blockTreeTransport Wt y ob)⁻¹ with hTt
  have hww : (w : ℍ[ℝ]) * ((w⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := unitQuaternion_coe_mul_inv w
  have e1 : ((a * w⁻¹ : UnitQuaternion) : ℍ[ℝ]) - (Tt : ℍ[ℝ]) =
      ((a : ℍ[ℝ]) - ((Tt * t : UnitQuaternion) : ℍ[ℝ])) * ((w⁻¹ : UnitQuaternion) : ℍ[ℝ]) +
        (Tt : ℍ[ℝ]) * ((((t : ℍ[ℝ]) - wt) + ((wt : ℍ[ℝ]) - w)) * ((w⁻¹ : UnitQuaternion) : ℍ[ℝ])) := by
    have e2 : ((a : ℍ[ℝ]) - (Tt : ℍ[ℝ]) * (t : ℍ[ℝ])) * ((w⁻¹ : UnitQuaternion) : ℍ[ℝ]) +
        (Tt : ℍ[ℝ]) * ((((t : ℍ[ℝ]) - wt) + ((wt : ℍ[ℝ]) - w)) * ((w⁻¹ : UnitQuaternion) : ℍ[ℝ])) =
        (a : ℍ[ℝ]) * ((w⁻¹ : UnitQuaternion) : ℍ[ℝ]) -
          (Tt : ℍ[ℝ]) * ((w : ℍ[ℝ]) * ((w⁻¹ : UnitQuaternion) : ℍ[ℝ])) := by
      noncomm_ring
    rw [unitQuaternion_coe_mul, unitQuaternion_coe_mul, e2, hww, mul_one]
  rw [e1]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul_unitQuaternion, norm_unitQuaternion_mul, norm_mul_unitQuaternion]
  have n1 := norm_add_le ((t : ℍ[ℝ]) - wt) ((wt : ℍ[ℝ]) - w)
  have n2 : ‖(t : ℍ[ℝ]) - wt‖ ≤ 16 * (F.blockSide : ℝ) * κ := by rwa [norm_sub_rev]
  have n3 : ‖(wt : ℍ[ℝ]) - w‖ ≤ 8 * N * K := by rwa [norm_sub_rev]
  linarith
theorem norm_mul_mul_sub_mul_mul (u v v' w : UnitQuaternion) :
    ‖((u * v * w : UnitQuaternion) : ℍ[ℝ]) - ((u * v' * w : UnitQuaternion) : ℍ[ℝ])‖ = ‖(v : ℍ[ℝ]) - v'‖ := by
  have e : ((u * v * w : UnitQuaternion) : ℍ[ℝ]) - ((u * v' * w : UnitQuaternion) : ℍ[ℝ]) =
      (u : ℍ[ℝ]) * (((v : ℍ[ℝ]) - v') * (w : ℍ[ℝ])) := by
    rw [unitQuaternion_coe_mul, unitQuaternion_coe_mul, unitQuaternion_coe_mul, unitQuaternion_coe_mul]
    noncomm_ring
  rw [e, norm_unitQuaternion_mul, norm_mul_unitQuaternion]
theorem oscillationAtMost_of_near {E : Type} (I : Finset E) (f : E → UnitQuaternion) (T : UnitQuaternion)
    (m η : ℝ) (hm : 2 * m ≤ η)
    (h : ∀ e ∈ I, ‖(f e : ℍ[ℝ]) - (T : ℍ[ℝ])‖ ≤ m) : OscillationAtMost I f η := by
  intro e he e' he'
  have e1 : (f e : ℍ[ℝ]) - f e' = ((f e : ℍ[ℝ]) - T) - ((f e' : ℍ[ℝ]) - T) := by abel
  rw [e1]
  have := norm_sub_le ((f e : ℍ[ℝ]) - T) ((f e' : ℍ[ℝ]) - T)
  have a := h e he
  have b := h e' he'
  linarith
theorem refineSite_add_unitStep (y : F.Cell) (i : Fin 4) :
    refineSite (y + unitStep F.top i) = refineSite y + F.blockSide • unitStep F.depth i := by
  have hj : F.depth < F.top := by simp [BlockFrame.top]
  have h := refineSite_add_stepDisplacement F.depth hj y (i, true)
  simpa [stepDisplacement] using h
theorem pathDisplacement_straight (i : Fin 4) :
    pathDisplacement (F := F) F.depth (List.replicate F.blockSide (i, true)) =
      F.blockSide • unitStep F.depth i := by
  rw [pathDisplacement_replicate]
  simp [stepDisplacement]
theorem contourHolonomy_eq_mul (X : F.GaugeField F.depth) (y : F.Cell) (i : Fin 4)
    (e : (Fin 4 → ℤ) × Equiv.Perm (Fin 4)) :
    contourHolonomy X (y, i) e = pathHolonomy X (refineSite y) (axisPath e.1 e.2) *
      pathHolonomy X (refineSite y + siteOfCoords F.depth e.1) (List.replicate F.blockSide (i, true)) *
        (pathHolonomy X (refineSite (y + unitStep F.top i)) (axisPath e.1 e.2))⁻¹ := by
  show pathHolonomy X (refineSite y) (axisPath e.1 e.2 ++ List.replicate F.blockSide (i, true) ++
    reversePath (axisPath e.1 e.2)) = _
  rw [pathHolonomy_append, pathHolonomy_append, pathDisplacement_axisPath]
  have hend : refineSite y + pathDisplacement F.depth (axisPath e.1 e.2 ++ List.replicate F.blockSide (i, true)) =
      refineSite (y + unitStep F.top i) + pathDisplacement F.depth (axisPath e.1 e.2) := by
    rw [pathDisplacement_append, pathDisplacement_straight, pathDisplacement_axisPath, refineSite_add_unitStep]
    abel
  rw [hend, pathHolonomy_reversePath]
theorem baseContourHolonomy_eq_mul (X : F.GaugeField F.depth) (b : F.Cell → F.Site F.depth) (y : F.Cell)
    (i : Fin 4) (e : (Fin 4 → ℤ) × Equiv.Perm (Fin 4)) :
    baseContourHolonomy X b (y, i) e = pathHolonomy X (b y) (baseLeg b y e) *
      pathHolonomy X (refineSite y + siteOfCoords F.depth e.1) (List.replicate F.blockSide (i, true)) *
        (pathHolonomy X (b (y + unitStep F.top i)) (baseLeg b (y + unitStep F.top i) e))⁻¹ := by
  show pathHolonomy X (b y) (baseLeg b y e ++ List.replicate F.blockSide (i, true) ++
    reversePath (baseLeg b (y + unitStep F.top i) e)) = _
  have h1 : ∀ z : F.Cell, b z + pathDisplacement F.depth (baseLeg b z e) =
      refineSite z + siteOfCoords F.depth e.1 := by
    intro z
    unfold baseLeg
    rw [pathDisplacement_axisPath, siteOfCoords_minimalOffset, cellCentre_eq_refineSite]
    abel
  rw [pathHolonomy_append, pathHolonomy_append, h1]
  have hend : b y + pathDisplacement F.depth (baseLeg b y e ++ List.replicate F.blockSide (i, true)) =
      b (y + unitStep F.top i) + pathDisplacement F.depth (baseLeg b (y + unitStep F.top i) e) := by
    rw [pathDisplacement_append, ← add_assoc, h1, h1, pathDisplacement_straight, refineSite_add_unitStep]
    abel
  rw [hend, pathHolonomy_reversePath]
theorem quatAverage_allContours (X : F.GaugeField F.depth) (c : F.Cell × Fin 4) (hL : Odd F.blockSide) :
    quatAverage (allContours F) (fun e => (contourHolonomy X c e : ℍ[ℝ])) = contourAverage X c := by
  have hc : (allContours F).card = F.blockSide ^ 4 * 24 := by
    simp [allContours, card_centredCube hL, Finset.card_product, Finset.card_univ, Fintype.card_perm,
      Nat.factorial]
  unfold quatAverage contourAverage
  rw [hc]
  have e1 : ∑ e ∈ allContours F, ((contourHolonomy X c e : UnitQuaternion) : ℍ[ℝ]) =
      ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
        ((pathHolonomy X (refineSite c.1) (bondContour F.blockSide h π c.2) : UnitQuaternion) : ℍ[ℝ]) := by
    unfold allContours
    rw [Finset.sum_product]
    rfl
  rw [e1]
  congr 1
  push_cast
  ring_nf
theorem bondMeanEstimate_holds (hl : LegNearBlockTree) (hm : TurnedMeanEstimate)
    (hc : contourStraightBondStatement) : BondMeanEstimate := by
  classical
  intro F Wt Wp W b c G Ds κ K τ N hL hS hκ hK d hη
  obtain ⟨y, i⟩ := c
  have hA : IsAdmissibleAmbient F := Or.inr hS
  have hj : F.depth < F.top := by simp [BlockFrame.top]
  have hLpos : 0 < F.blockSide := hL.pos
  have hLr : (0 : ℝ) < F.blockSide := by exact_mod_cast hLpos
  set y' := y + unitStep F.top i with hy'
  set Q := sitesBelow F.depth y ∪ sitesBelow F.depth y' with hQ
  set η := 72 * (F.blockSide : ℝ) * κ + 16 * N * K with hηd
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hLκ : 0 ≤ (F.blockSide : ℝ) * κ := mul_nonneg hLr.le hκ
  have hNK : 0 ≤ (N : ℝ) * K := mul_nonneg hN0 hK
  have hη0 : 0 ≤ η := by
    rw [hηd]
    nlinarith
  have dnear : LinksClose Wp Wt Ds Q K := d.links_close
  have dbase : b y ∈ sitesBelow F.depth y := d.base_mem
  have dbase' : b y' ∈ sitesBelow F.depth y' := d.base_mem'
  have dcur : blockCurvatureNorm Wt y ≤ κ := d.defect_le
  have dcur' : blockCurvatureNorm Wt y' ≤ κ := d.defect_le'
  have dtop : ∑ p ∈ blockPairPlaquettes (y, i), plaquetteDefect Wp p ^ 2 ≤ κ ^ 2 := d.pairDefect_le
  obtain ⟨T, hT⟩ := exists_legRotation_near hl hL hS Wt Wp b y Ds Q κ K N hK dbase dcur dnear
    Finset.subset_union_left d.coords_card_le
  obtain ⟨T', hT'⟩ := exists_legRotation_near hl hL hS Wt Wp b y' Ds Q κ K N hK dbase' dcur' dnear
    Finset.subset_union_right d.coords_card_le
  have hOA : OscillationAtMost (allContours F) (legRotation Wt Wp b y) η :=
    oscillationAtMost_of_near _ _ T _ η (by rw [hηd]; nlinarith) hT
  have hOB : OscillationAtMost (allContours F) (legRotation Wt Wp b y') η :=
    oscillationAtMost_of_near _ _ T' _ η (by rw [hηd]; nlinarith) hT'
  have hPc : ∀ e ∈ allContours F, ‖((contourHolonomy Wp (y, i) e : UnitQuaternion) : ℍ[ℝ]) -
      (pathHolonomy Wp (refineSite y) (List.replicate F.blockSide (i, true)) : UnitQuaternion)‖ ≤
        4 * ((F.blockSide : ℝ) * κ) := by
    intro e he
    have h := hc F F.depth hj hL hA Wp (y, i) e he
    have h2 : ‖((contourHolonomy Wp (y, i) e : UnitQuaternion) : ℍ[ℝ]) -
        (pathHolonomy Wp (refineSite y) (List.replicate F.blockSide (i, true)) : UnitQuaternion)‖ ^ 2 ≤
          (4 * ((F.blockSide : ℝ) * κ)) ^ 2 := by
      refine h.trans ?_
      have : 16 * (F.blockSide : ℝ) ^ 2 * ∑ p ∈ blockPairPlaquettes (y, i), plaquetteDefect Wp p ^ 2 ≤
          16 * (F.blockSide : ℝ) ^ 2 * κ ^ 2 :=
        mul_le_mul_of_nonneg_left dtop (by positivity)
      nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).1 h2
  have hOP : OscillationAtMost (allContours F) (contourHolonomy Wp (y, i)) η :=
    oscillationAtMost_of_near _ _ _ _ η (by rw [hηd]; nlinarith) hPc
  let σ : List PathStep := List.replicate F.blockSide (i, true)
  let Pk : (Fin 4 → ℤ) × Equiv.Perm (Fin 4) → UnitQuaternion := fun e =>
    pathHolonomy Wp (refineSite y) (axisPath e.1 e.2) *
      pathHolonomy Wt (refineSite y + siteOfCoords F.depth e.1) σ *
        (pathHolonomy Wp (refineSite y') (axisPath e.1 e.2))⁻¹
  have hdist : ∀ e, ‖(Pk e : ℍ[ℝ]) - contourHolonomy Wp (y, i) e‖ =
      ‖((pathHolonomy Wt (refineSite y + siteOfCoords F.depth e.1) σ : UnitQuaternion) : ℍ[ℝ]) -
        (pathHolonomy Wp (refineSite y + siteOfCoords F.depth e.1) σ : UnitQuaternion)‖ := by
    intro e
    rw [contourHolonomy_eq_mul]
    exact norm_mul_mul_sub_mul_mul _ _ _ _
  have hperL : ∀ k, F.blockSide < F.period F.depth k := by
    intro k
    rw [period_depth]
    have := hS k
    nlinarith
  have hstep : ∀ e ∈ allContours F, ‖(Pk e : ℍ[ℝ]) - contourHolonomy Wp (y, i) e‖ ≤
      K * touchCount Ds (refineSite y + siteOfCoords F.depth e.1) σ := by
    intro e he
    rw [hdist, norm_sub_rev]
    refine norm_pathHolonomy_sub_le Wp Wt Ds Q K hK dnear σ _ ?_
    intro z hz
    obtain ⟨r, hr, rfl⟩ := mem_pathSites_replicate _ _ _ _ hz
    have hξ : e.1 ∈ centredCube F.blockSide := (Finset.mem_product.1 he).1
    have hmb := mem_adjacent_blocks F.depth hj hL y i (offsetInBlock_of_mem_centredCube hξ) r hr
    have es : refineSite y + siteOfCoords F.depth e.1 + r • stepDisplacement F.depth (i, true) =
        refineSite y + siteOfCoords F.depth e.1 + r • unitStep F.depth i := by
      simp only [stepDisplacement, if_true]
    rw [es]
    exact hmb
  have htouch : ∀ x : F.Site F.depth, touchCount Ds x σ ≤ 2 * N := fun x =>
    touchCount_straight_le Ds x (i, true) F.blockSide N (hperL i) (d.coords_card_le i)
  have hsup : ∀ e ∈ allContours F, ‖(Pk e : ℍ[ℝ]) - contourHolonomy Wp (y, i) e‖ ≤ 2 * N * K := by
    intro e he
    refine (hstep e he).trans ?_
    have h1 : (touchCount Ds (refineSite y + siteOfCoords F.depth e.1) σ : ℝ) ≤ 2 * N := by
      exact_mod_cast htouch _
    nlinarith
  let Bad : Finset (Fin 4 → ℤ) := (centredCube F.blockSide).filter fun ξ => ∀ k, k ≠ i →
    (refineSite y + siteOfCoords F.depth ξ : F.Site F.depth) k ∈ (fun k => Ds.image fun z => z k) k
  have hBad : Bad.card ≤ F.blockSide * N ^ 3 :=
    card_offsets_le hL F.depth (fun k => (hperL k).le) (refineSite y) i _ N d.coords_card_le
  have hoff : ∀ e ∈ allContours F, e.1 ∉ Bad → ‖(Pk e : ℍ[ℝ]) - contourHolonomy Wp (y, i) e‖ = 0 := by
    intro e he hb
    have h0 : touchCount Ds (refineSite y + siteOfCoords F.depth e.1) σ = 0 := by
      refine touchCount_eq_zero Ds σ _ fun z hz hzD => hb ?_
      obtain ⟨r, _, rfl⟩ := mem_pathSites_replicate _ _ _ _ hz
      refine Finset.mem_filter.2 ⟨(Finset.mem_product.1 he).1, fun k hk => ?_⟩
      refine Finset.mem_image.2 ⟨_, hzD, ?_⟩
      have hz0 : (stepDisplacement F.depth (i, true) : F.Site F.depth) k = 0 := by
        simp [stepDisplacement, unitStep, siteOfCoords, Pi.single_apply, hk]
      simp [hz0]
    have := hstep e he
    rw [h0] at this
    simp only [Nat.cast_zero, mul_zero] at this
    exact le_antisymm this (norm_nonneg _)
  have hcardI : ((allContours F).card : ℝ) = (F.blockSide : ℝ) ^ 4 * 24 := by
    have : (allContours F).card = F.blockSide ^ 4 * 24 := by
      simp [allContours, card_centredCube hL, Finset.card_product, Finset.card_univ, Fintype.card_perm,
        Nat.factorial]
    rw [this]
    push_cast
    ring
  have hmean : average (allContours F) (fun e => ‖(Pk e : ℍ[ℝ]) - contourHolonomy Wp (y, i) e‖) ≤
      2 * (N : ℝ) ^ 4 * K / (F.blockSide : ℝ) ^ 3 := by
    have h1 : ∑ e ∈ allContours F, ‖(Pk e : ℍ[ℝ]) - contourHolonomy Wp (y, i) e‖ ≤
        ∑ e ∈ allContours F, (if e.1 ∈ Bad then 2 * (N : ℝ) * K else 0) := by
      refine Finset.sum_le_sum fun e he => ?_
      by_cases hb : e.1 ∈ Bad
      · simp only [hb, if_true]
        exact hsup e he
      · simp only [hb, if_false]
        exact (hoff e he hb).le
    have h2 : ∑ e ∈ allContours F, (if e.1 ∈ Bad then 2 * (N : ℝ) * K else 0) =
        (Bad.card : ℝ) * 24 * (2 * N * K) := by
      unfold allContours
      rw [Finset.sum_product]
      have e4 : ∀ x ∈ centredCube F.blockSide,
          (∑ _π : Equiv.Perm (Fin 4), (if x ∈ Bad then 2 * (N : ℝ) * K else 0)) =
            24 * (if x ∈ Bad then 2 * (N : ℝ) * K else 0) := by
        intro x _
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
        simp [Nat.factorial]
      refine (Finset.sum_congr rfl e4).trans ?_
      rw [← Finset.mul_sum, ← Finset.sum_filter]
      have e3 : (centredCube F.blockSide).filter (fun ξ => ξ ∈ Bad) = Bad := by
        ext ξ
        simp only [Finset.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨(Finset.mem_filter.1 h).1, h⟩⟩
      rw [e3, Finset.sum_const, nsmul_eq_mul]
      ring
    have h3 : (Bad.card : ℝ) ≤ (F.blockSide : ℝ) * N ^ 3 := by exact_mod_cast hBad
    unfold average
    rw [hcardI]
    have h4 : (1 / ((F.blockSide : ℝ) ^ 4 * 24)) *
        ∑ e ∈ allContours F, ‖(Pk e : ℍ[ℝ]) - contourHolonomy Wp (y, i) e‖ ≤
          (1 / ((F.blockSide : ℝ) ^ 4 * 24)) * ((F.blockSide : ℝ) * N ^ 3 * 24 * (2 * N * K)) := by
      refine mul_le_mul_of_nonneg_left (h1.trans ?_) (by positivity)
      rw [h2]
      have : 0 ≤ 2 * (N : ℝ) * K := by positivity
      exact mul_le_mul_of_nonneg_right (by linarith) this
    refine h4.trans (le_of_eq ?_)
    field_simp
  have hturn : ∀ e, legRotation Wt Wp b y e * Pk e * (legRotation Wt Wp b y' e)⁻¹ =
      baseContourHolonomy Wt b (y, i) e := by
    intro e
    unfold legRotation
    rw [baseContourHolonomy_eq_mul, cellCentre_eq_refineSite, cellCentre_eq_refineSite]
    simp only [Pk, σ]
    generalize pathHolonomy Wt (b y) (baseLeg b y e) = p1
    generalize pathHolonomy Wp (refineSite y) (axisPath e.1 e.2) = p2
    generalize pathHolonomy Wt (refineSite y + siteOfCoords F.depth e.1) (List.replicate F.blockSide (i, true)) = p3
    generalize pathHolonomy Wp (refineSite y') (axisPath e.1 e.2) = p4
    generalize pathHolonomy Wt (b y') (baseLeg b y' e) = p5
    group
  have hsup' : ∀ e ∈ allContours F, ‖(Pk e : ℍ[ℝ]) - contourHolonomy Wp (y, i) e‖ ≤ η := by
    intro e he
    refine (hsup e he).trans ?_
    rw [hηd]
    nlinarith
  obtain ⟨M1, M2⟩ := hm _ (allContours F) G (legRotation Wt Wp b y) (legRotation Wt Wp b y')
    (contourHolonomy Wp (y, i)) Pk η _ τ d.contours_subset d.contours_nonempty hη0 hη hOA hOB hOP hsup' hmean
    (by convert d.missing_le)
  rw [quatAverage_allContours Wp (y, i) hL] at M1 M2
  have hmeanG : quatAverage G (fun e =>
      ((legRotation Wt Wp b y e * Pk e * (legRotation Wt Wp b y' e)⁻¹ : UnitQuaternion) : ℍ[ℝ])) =
        quatAverage G (fun e => (baseContourHolonomy W b (y, i) e : ℍ[ℝ])) := by
    unfold quatAverage
    congr 1
    refine Finset.sum_congr rfl fun e he => ?_
    show (((legRotation Wt Wp b y e * Pk e * (legRotation Wt Wp b y' e)⁻¹ : UnitQuaternion)) : ℍ[ℝ]) =
      (baseContourHolonomy W b (y, i) e : ℍ[ℝ])
    rw [hturn, d.holonomy_eq e he]
  rw [hmeanG] at M1
  exact ⟨M1, M2⟩
end BondMeans
end YangMills.Construction
end
