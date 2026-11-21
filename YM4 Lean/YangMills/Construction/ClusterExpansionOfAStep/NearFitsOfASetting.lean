import YangMills.Construction.ClusterExpansionOfAStep.FitsOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.WideChartOfASetting
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusContours StepSettings TorusFields TorusLumps TorusBlocks
  StepCosts PlainAlignment SettingFits
variable {R : StepSetup} {n : ℕ} [NeZero n] {s : ChartSetting R n} {δ lam σA cg : ℝ} {N : ℕ → ℝ}
def StepSettings.ChartSetting.nearFitSum (s : ChartSetting R n) (W : TorusField (n * R.params.side)) : ℝ :=
  R.params.coupling * ∑ c ∈ s.nearBonds, plainAlignmentDefect R.params.side c.1 c.2 (s.coarse c.1 c.2) W
namespace NearFits
theorem mem_nearBonds {c : TorusBond n} :
    c ∈ s.nearBonds ↔ ∃ b ∈ s.free, _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side b.1) c.1 ≤ 16 := by
  classical
  unfold ChartSetting.nearBonds
  simp
theorem supDist_le_of_near_block (c : s.ChainContext δ lam σA cg N) {b₀ : TorusBond (n * R.params.side)}
    {Y : TorusSite n} (hY : _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side b₀.1) Y ≤ 18) {x : TorusSite (n * R.params.side)}
    (hx : _root_.YangMills.Construction.TorusFields.supDist (blockCentreSite R.params.side Y) x ≤ 5 * R.params.side + 1) :
    _root_.YangMills.Construction.TorusFields.supDist b₀.1 x ≤ 2 * R.range + 2 := by
  have hL := c.params_admissible.L_odd
  have h1 := _root_.YangMills.Construction.TorusBlocks.supDist_le_mul_supDist_parentBlock_add_one hL b₀.1 (blockCentreSite R.params.side Y)
  rw [parentBlock_blockCentreSite hL] at h1
  have h2 := _root_.YangMills.Construction.TorusFields.supDist_triangle b₀.1 (blockCentreSite R.params.side Y) x
  have h3 : R.params.side * (_root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side b₀.1) Y + 1) ≤ R.params.side * 19 :=
    Nat.mul_le_mul_left _ (by omega)
  have h4 := c.large_range.range_large
  omega
theorem supDist_parentBlock_le_of_near (c : s.ChainContext δ lam σA cg N) {Y : TorusSite n}
    {x : TorusSite (n * R.params.side)} (hx : _root_.YangMills.Construction.TorusFields.supDist (blockCentreSite R.params.side Y) x ≤ 10 * R.params.side) :
    _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side x) Y ≤ 11 := by
  have hL := c.params_admissible.L_odd
  have hpos : 0 < R.params.side := hL.pos
  have h1 := mul_supDist_parentBlock_le hL (blockCentreSite R.params.side Y) x
  rw [parentBlock_blockCentreSite hL] at h1
  rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
  have h2 : R.params.side * _root_.YangMills.Construction.TorusFields.supDist Y (parentBlock R.params.side x) ≤ R.params.side * 11 := by omega
  exact Nat.le_of_mul_le_mul_left h2 hpos
theorem supDist_le_of_mem_contourWord (c : s.ChainContext δ lam σA cg N) {Y : TorusSite n} {i : Fin 4}
    {e : (Fin 4 → ℤ) × Equiv.Perm (Fin 4)} (he : e ∈ contourIndex R.params.side)
    {x : TorusBond (n * R.params.side) × Bool} (hx : x ∈ contourWord R.params.side Y i e) :
    _root_.YangMills.Construction.TorusFields.supDist (blockCentreSite R.params.side Y) x.1.1 ≤ 5 * R.params.side := by
  have h1 := _root_.YangMills.Construction.TorusContours.supDist_le_length_of_mem_pathToWord _ _ hx
  exact h1.trans (length_bondContour_le c.params_admissible.L_odd (Finset.mem_product.mp he).1 _ _)
theorem plainAlignmentDefect_congr_near (c : s.ChainContext δ lam σA cg N) {d : TorusBond n}
    (hd : d ∈ s.nearBonds) (v : UnitQuaternion) {W W' : TorusField (n * R.params.side)}
    (h : ∀ x i, s.IsNearFree (x, i) → W x i = W' x i) :
    plainAlignmentDefect R.params.side d.1 d.2 v W = plainAlignmentDefect R.params.side d.1 d.2 v W' := by
  obtain ⟨b₀, hb₀, hbd⟩ := mem_nearBonds.mp hd
  have hm : plainContourAverage R.params.side d.1 d.2 W = plainContourAverage R.params.side d.1 d.2 W' :=
    plainContourAverage_congr fun e he x hx => by
      have h1 := _root_.YangMills.Construction.NearFits.supDist_le_of_mem_contourWord c he hx
      exact h _ _ ⟨b₀, hb₀, _root_.YangMills.Construction.NearFits.supDist_le_of_near_block c (b₀ := b₀) (Y := d.1) (x := x.1.1) (by omega) (by omega)⟩
  unfold plainAlignmentDefect
  rw [hm]
theorem plainAlignmentDefect_congr_far (c : s.ChainContext δ lam σA cg N) {d : TorusBond n}
    (hd : d ∉ s.nearBonds) (v : UnitQuaternion) {W W' : TorusField (n * R.params.side)}
    (h : ∀ x i, (x, i) ∉ s.free → W x i = W' x i) :
    plainAlignmentDefect R.params.side d.1 d.2 v W = plainAlignmentDefect R.params.side d.1 d.2 v W' := by
  have hm : plainContourAverage R.params.side d.1 d.2 W = plainContourAverage R.params.side d.1 d.2 W' :=
    plainContourAverage_congr fun e he x hx => by
      refine h _ _ fun hf => hd (mem_nearBonds.mpr ⟨x.1, hf, ?_⟩)
      have h1 := _root_.YangMills.Construction.NearFits.supDist_le_of_mem_contourWord c he hx
      have h2 := _root_.YangMills.Construction.NearFits.supDist_parentBlock_le_of_near c (x := x.1.1) (Y := d.1) (by nlinarith)
      omega
  unfold plainAlignmentDefect
  rw [hm]
section Bases
theorem usedContours_subset_allContours {F : BlockFrame} (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth)))
    (b : F.Cell → F.Site F.depth) (d : F.Cell × Fin 4) : usedContours J₀ h b d ⊆ allContours F := by
  classical
  unfold usedContours
  split_ifs
  · exact Finset.Subset.refl _
  · exact Finset.filter_subset _ _
theorem length_contourPath_le {F : BlockFrame} [∀ j i, NeZero (F.period j i)] {J₀ : ℕ}
    {h : Finset (Finset (F.Site F.depth))} {b : F.Cell → F.Site F.depth} (hL : 1 ≤ F.blockSide)
    (hb : IsBaseChoice J₀ h b) (d : F.Cell × Fin 4) {ξ : Fin 4 → ℤ} (hξ : ξ ∈ centredCube F.blockSide)
    (π : Equiv.Perm (Fin 4)) : (contourPath b d ξ π).length ≤ 9 * F.blockSide := by
  have key : ∀ y : F.Cell,
      (axisPath (minimalOffset (b y) (cellCentre F.depth y + siteOfCoords F.depth ξ)) π).length ≤ 4 * F.blockSide := by
    intro y
    obtain ⟨z, hz, hy⟩ := exists_centredCube_of_isBaseChoice hL hb y
    refine length_axisPath_le _ π fun k => ?_
    have e : (cellCentre F.depth y + siteOfCoords F.depth ξ - b y : F.Site F.depth) k =
        (((ξ k - z k : ℤ)) : ZMod (F.period F.depth k)) := by
      rw [hy]
      simp [siteAtOffset, siteOfCoords]
    unfold minimalOffset
    rw [e]
    refine (_root_.YangMills.Construction.TorusFields.natAbs_valMinAbs_intCast_le _).trans ?_
    have a1 := TorusContours.mem_centredCube_iff.mp hξ k
    have a2 := TorusContours.mem_centredCube_iff.mp hz k
    omega
  have h1 := key d.1
  have h2 := key (d.1 + BlockAverages.unitStep F.top d.2)
  simp only [contourPath, reversePath, List.length_append, List.length_replicate, List.length_map,
    List.length_reverse]
  omega
end Bases
theorem bondFit_congr_far (c : s.ChainContext δ lam σA cg N) {d : TorusBond n} (hd : d ∉ s.nearBonds)
    {W W' : TorusField (n * R.params.side)} (hh : stepHotLumps R.params W = stepHotLumps R.params W')
    (hag : ∀ x i, (x, i) ∉ s.free → W x i = W' x i) :
    bondFit R.params W s.coarse s.bases d = bondFit R.params W' s.coarse s.bases d := by
  classical
  have hL := c.params_admissible.L_odd
  have hLpos : 1 ≤ R.params.side := hL.pos
  have hP := stepBlockFrame_period_zero R n
  have hn := stepBlockFrame_extent R n
  have hbases : IsBaseChoice R.params.baseDepth (stepHotLumps R.params s.fine) s.bases := c.admissible.isBaseChoice
  obtain ⟨z, hz, h3⟩ := exists_base_eq_blockCentreSite_add (F := stepBlockFrame R.params.side n) hn hLpos hbases d.1
  have h4 : _root_.YangMills.Construction.TorusFields.supDist (blockCentreSite R.params.side d.1)
      (toTorusSite (n * R.params.side)
        (s.bases (torusSiteInFrame (stepBlockFrame R.params.side n) (stepBlockFrame R.params.side n).top d.1))) ≤
      R.params.side := by
    have h5 := _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le (blockCentreSite R.params.side d.1) z R.params.side fun k => by
      have hk := TorusContours.mem_centredCube_iff.mp hz k
      have hLz : (stepBlockFrame R.params.side n).blockSide = R.params.side := rfl
      rw [hLz] at hk
      omega
    have h3' : toTorusSite (n * R.params.side)
        (s.bases (torusSiteInFrame (stepBlockFrame R.params.side n) (stepBlockFrame R.params.side n).top d.1)) =
        blockCentreSite R.params.side d.1 + siteOfInt z := h3
    rw [h3']
    exact h5
  have hmean : contourMean R.params.baseDepth (stepHotLumps R.params W') s.bases
      (readAtLevel (stepBlockFrame R.params.side n) 0 W) (torusSiteInFrame (stepBlockFrame R.params.side n) 1 d.1, d.2) =
      contourMean R.params.baseDepth (stepHotLumps R.params W') s.bases
        (readAtLevel (stepBlockFrame R.params.side n) 0 W') (torusSiteInFrame (stepBlockFrame R.params.side n) 1 d.1, d.2) := by
    unfold contourMean
    congr 1
    refine Finset.sum_congr rfl fun e he => ?_
    have hξ : e.1 ∈ centredCube R.params.side :=
      (Finset.mem_product.mp (usedContours_subset_allContours _ _ _ _ he)).1
    show ((pathHolonomy (readAtLevel (stepBlockFrame R.params.side n) 0 W) _ _ : UnitQuaternion) : ℍ[ℝ]) =
      ((pathHolonomy (readAtLevel (stepBlockFrame R.params.side n) 0 W') _ _ : UnitQuaternion) : ℍ[ℝ])
    rw [pathHolonomy_readAtLevel hP, pathHolonomy_readAtLevel hP, wordHolonomy_congr (W := W) (W' := W')]
    intro x hx
    refine hag _ _ fun hf => hd (mem_nearBonds.mpr ⟨x.1, hf, ?_⟩)
    have h1 := _root_.YangMills.Construction.TorusContours.supDist_le_length_of_mem_pathToWord _ _ hx
    have h2 : (contourPath s.bases (torusSiteInFrame (stepBlockFrame R.params.side n) 1 d.1, d.2) e.1 e.2).length ≤
        9 * R.params.side :=
      length_contourPath_le (F := stepBlockFrame R.params.side n) hLpos hbases
        (torusSiteInFrame (stepBlockFrame R.params.side n) 1 d.1, d.2) hξ e.2
    have h5 := (_root_.YangMills.Construction.TorusFields.supDist_triangle _ _ _).trans (Nat.add_le_add h4 (h1.trans h2))
    have h6 := _root_.YangMills.Construction.NearFits.supDist_parentBlock_le_of_near c (x := x.1.1) (Y := d.1) (by omega)
    omega
  unfold bondFit contourFit
  rw [hh, hmean]
end NearFits
end YangMills.Construction
end
