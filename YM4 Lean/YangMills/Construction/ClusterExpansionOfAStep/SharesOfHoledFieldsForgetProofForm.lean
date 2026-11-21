import YangMills.Construction.ClusterExpansionOfAStep.SharesOfHoledFieldsAtLevelZeroProof
import YangMills.Construction.ClusterExpansionOfAStep.SharesOfHoledFieldsForget
import YangMills.Construction.ColdChainAtEveryLevel.AnalyticSharesOfAColdTopProof
import YangMills.Construction.HoleBesideASecondHole.CellsLeftOffTheSpotsProof
import YangMills.Construction.HoleBesideASecondHole.TorusAtAFrameDefsProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages LumpContours HoleBounds TorusFields TorusLumps StepCosts ColdChain
namespace HoledShares
theorem natAbs_le_of_abs_le_natCast {a : ℤ} {m : ℕ} (h : |a| ≤ (m : ℤ)) : a.natAbs ≤ m := by apply _root_.YangMills.Construction.CongruentBoxes.natAbs_le_of_abs_le_natCast <;> assumption
theorem abs_le_natCast_of_natAbs_le {a : ℤ} {m : ℕ} (h : a.natAbs ≤ m) : |a| ≤ (m : ℤ) := by apply _root_.YangMills.Construction.CongruentBoxes.abs_le_natCast_of_natAbs_le <;> assumption
theorem mem_centredCube_odd_iff (m : ℕ) (h : Fin 4 → ℤ) :
    h ∈ centredCube (2 * m + 1) ↔ ∀ i, |h i| ≤ (m : ℤ) := by apply _root_.YangMills.Construction.HoleSavings.mem_centredCube_odd <;> assumption
section Cells
variable {F : BlockFrame} {n : ℕ} [NeZero n]
theorem period_top_of_extent (hs : ∀ i, F.extent i = n) (i : Fin 4) : F.period F.top i = n := by
  simp [BlockFrame.period, hs]
theorem neZero_period_top (hs : ∀ i, F.extent i = n) (i : Fin 4) : NeZero (F.period F.top i) :=
  ⟨by rw [period_top_of_extent hs]; exact NeZero.ne n⟩
def torusCell (F : BlockFrame) (y : TorusSite n) : F.Cell := torusSiteInFrame F F.top y
theorem toTorusSite_torusCell (hs : ∀ i, F.extent i = n) (y : TorusSite n) :
    toTorusSite n (torusCell F y) = y := by
  funext k
  have := neZero_period_top hs k
  have h := castInt_intCast (period_top_of_extent hs k) (((y k).cast : ℤ))
  simpa [toTorusSite, torusCell, torusSiteInFrame, siteOfCoords, siteCoords] using h
theorem torusCell_toTorusSite (hs : ∀ i, F.extent i = n) (c : F.Cell) :
    torusCell F (toTorusSite n c : TorusSite n) = c := by
  funext k
  have := neZero_period_top hs k
  have h := castInt_intCast (period_top_of_extent hs k).symm (((c k).cast : ℤ))
  simpa [toTorusSite, torusCell, torusSiteInFrame, siteOfCoords, siteCoords] using h
theorem toTorusSite_add (hs : ∀ i, F.extent i = n) (x y : F.Cell) :
    toTorusSite n (x + y) = toTorusSite n x + toTorusSite n y := by
  funext k
  have := neZero_period_top hs k
  exact castInt_add (period_top_of_extent hs k) (x k) (y k)
theorem toTorusSite_siteOfCoords (hs : ∀ i, F.extent i = n) (h : Fin 4 → ℤ) :
    toTorusSite n (siteOfCoords F.top h : F.Cell) = siteOfInt h := by
  funext k
  have := neZero_period_top hs k
  exact castInt_intCast (period_top_of_extent hs k) (h k)
theorem toTorusSite_unitStep (hs : ∀ i, F.extent i = n) (i : Fin 4) :
    toTorusSite n (BlockAverages.unitStep F.top i : F.Cell) = TorusFields.unitStep n i := by
  unfold BlockAverages.unitStep
  rw [toTorusSite_siteOfCoords hs]
  funext k
  by_cases hk : k = i
  · subst hk
    simp [siteOfInt, TorusFields.unitStep]
  · simp [siteOfInt, TorusFields.unitStep, Pi.single_apply, hk]
theorem mem_cellsOfSites_iff (hs : ∀ i, F.extent i = n) (S : Finset (TorusSite n)) (c : F.Cell) :
    c ∈ cellsOfSites F S ↔ (toTorusSite n c : TorusSite n) ∈ S := by apply _root_.YangMills.Construction.TopLevelSites.mem_cellsOfSites_iff <;> assumption
theorem plaquetteDefect_readAtLevel_top (hs : ∀ i, F.extent i = n) (W : TorusField n) (x : F.Cell)
    (μ ν : Fin 4) :
    plaquetteDefect (readAtLevel F F.top W) (x, μ, ν) = curvature W (toTorusSite n x) μ ν := by
  unfold plaquetteDefect TorusFields.curvature TorusFields.holonomy
  have hv : plaquetteHolonomy (readAtLevel F F.top W) (x, μ, ν) =
      W (toTorusSite n x) μ * W (toTorusSite n x + TorusFields.unitStep n μ) ν *
        (W (toTorusSite n x + TorusFields.unitStep n ν) μ)⁻¹ * (W (toTorusSite n x) ν)⁻¹ := by
    have a1 : x + BlockAverages.unitStep F.top μ + BlockAverages.unitStep F.top ν -
        BlockAverages.unitStep F.top μ = x + BlockAverages.unitStep F.top ν := by abel
    have a2 : x + BlockAverages.unitStep F.top μ + BlockAverages.unitStep F.top ν +
        -BlockAverages.unitStep F.top μ - BlockAverages.unitStep F.top ν = x := by abel
    have hr : ∀ (z : F.Cell) (i : Fin 4), readAtLevel F F.top W z i = W (toTorusSite n z) i :=
      fun _ _ => rfl
    simp only [plaquetteHolonomy, pathHolonomy, linkValue, stepDisplacement, if_true,
      Bool.false_eq_true, if_false, mul_one, a1, a2, hr, toTorusSite_add hs, toTorusSite_unitStep hs,
      mul_assoc]
  rw [hv]
theorem mem_torusCells_of_extent (hs : ∀ i, F.extent i = n) (c : F.Cell) : c ∈ torusCells F := by exact _root_.YangMills.Construction.TorusFrames.mem_torusCells_of_extent (n := n) hs c
theorem mem_of_mem_sitesOfCells_top (hs : ∀ i, F.extent i = n) {S : Finset F.Cell} {x : F.Cell}
    (hx : x ∈ sitesOfCells S F.top) : x ∈ S := by
  unfold sitesOfCells at hx
  obtain ⟨z, hz, hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hx
  have h0 : h = 0 := by
    funext i
    have := (Fintype.mem_piFinset.1 hh) i
    simpa using this
  have hc : cellCentre F.top z = z := by
    funext k
    have := neZero_period_top hs k
    simp [cellCentre, siteOfCoords, siteCoords]
  rw [h0, hc]
  have : (siteOfCoords F.top (0 : Fin 4 → ℤ) : F.Cell) = 0 := by
    funext k
    simp [siteOfCoords]
  rw [this, add_zero]
  exact hz
end Cells
section Regions
variable {ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters} {F : BlockFrame} {n : ℕ} [NeZero n]
theorem image_lumpOf_eq_torusLumpOf (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n)
    (hs : ∀ i, F.extent i = n) (x : F.Cell) :
    open Classical in (lumpOf ℓ.grid x).image (toTorusSite n) = torusLumpOf ℓ (toTorusSite n x) := by
  classical
  have hLpos : 0 < ℓ.side := by have := hfit.L_ge; omega
  have hodd := hfit.L_odd
  have hkey : ∀ h : Fin 4 → ℤ, lumpCorner ℓ (siteOfInt h : TorusSite n) =
      fun i => (stripStart ℓ.grid (h i) : ZMod n) := by
    intro h
    funext i
    exact stripStart_cast_intCast ℓ hfit hLn (h i)
  have hx : toTorusSite n x = siteOfInt (siteCoords x) := rfl
  ext z
  simp only [Finset.mem_image, torusLumpOf, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hy
    rw [toTorusSite_siteOfCoords hs, hx, hkey, hkey]
    funext i
    have hi := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hh i)
    rw [stripStart_eq_of_mem hLpos hodd ℓ.grid (siteCoords x i) (h i) hi.1 hi.2]
  · intro hz
    have hz2 : ∀ i, ∃ k : ℤ, stripStart ℓ.grid ((z i).cast : ℤ) =
        stripStart ℓ.grid (siteCoords x i) + n * k := by
      intro i
      have h1 := congrFun hz i
      rw [hx, hkey] at h1
      have h2 : ((stripStart ℓ.grid ((z i).cast : ℤ) : ℤ) : ZMod n) =
          (stripStart ℓ.grid (siteCoords x i) : ZMod n) := h1
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h2
      obtain ⟨k, hk⟩ := h2
      exact ⟨-k, by linarith⟩
    choose k hk using hz2
    have hdv : ∀ i, (ℓ.side : ℤ) ∣ -(n : ℤ) * k i := fun i =>
      Dvd.dvd.mul_right (Dvd.dvd.neg_right (by exact_mod_cast hLn)) _
    have hstrip : ∀ i, stripStart ℓ.grid (((z i).cast : ℤ) + -(n : ℤ) * k i) =
        stripStart ℓ.grid (siteCoords x i) := by
      intro i
      rw [stripStart_add_dvd hLpos hodd _ _ _ (hdv i), hk]
      ring
    refine ⟨siteOfCoords F.top fun i => ((z i).cast : ℤ) + -(n : ℤ) * k i, ?_, ?_⟩
    · refine Finset.mem_image.mpr ⟨_, Fintype.mem_piFinset.mpr fun i => Finset.mem_Icc.mpr ?_, rfl⟩
      exact mem_of_stripStart_eq hLpos hodd ℓ.grid (siteCoords x i) _ (hstrip i)
    · rw [toTorusSite_siteOfCoords hs]
      funext i
      simp [siteOfInt]
open Classical in
def hotLumpCells (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (F : BlockFrame) (V : TorusField n) : Finset (Finset F.Cell) :=
  (torusHotLumps ℓ V).image fun l => l.image (torusCell F)
theorem isLump_of_mem_hotLumpCells (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n)
    (hs : ∀ i, F.extent i = n) (V : TorusField n) :
    ∀ l ∈ hotLumpCells ℓ F V, IsLump ℓ.grid l := by
  classical
  intro l hl
  obtain ⟨l₀, hl₀, rfl⟩ := Finset.mem_image.mp hl
  obtain ⟨x, μ, ν, _, _, z, _, rfl⟩ := (mem_torusHotLumps_iff ℓ hfit hLn V l₀).mp hl₀
  refine ⟨torusCell F z, ?_⟩
  rw [← toTorusSite_torusCell (F := F) hs z, ← image_lumpOf_eq_torusLumpOf hfit hLn hs,
    Finset.image_image]
  rw [toTorusSite_torusCell hs z]
  have hid : (torusCell F ∘ toTorusSite n : F.Cell → F.Cell) = id :=
    funext fun c => torusCell_toTorusSite hs c
  rw [hid, Finset.image_id]
theorem mem_biUnion_thicken_hotLumpCells_iff (hs : ∀ i, F.extent i = n) (V : TorusField n)
    (c : F.Cell) (m : ℕ) :
    c ∈ (hotLumpCells ℓ F V).biUnion (thicken m) ↔
      (toTorusSite n c : TorusSite n) ∈ thickening m (torusHotSites ℓ V) := by
  classical
  unfold thicken thickening
  simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨l', hl', x, hx, h, hh, rfl⟩
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hl'
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    refine ⟨u, Finset.mem_biUnion.mpr ⟨l, hl, hu⟩, ?_⟩
    rw [toTorusSite_add hs, toTorusSite_torusCell hs, toTorusSite_siteOfCoords hs, _root_.YangMills.Construction.TorusFields.supDist_comm]
    exact supDist_add_siteOfInt_le _ _ _ fun i =>
      natAbs_le_of_abs_le_natCast ((mem_centredCube_odd_iff m h).mp hh i)
  · rintro ⟨u, hu, hd⟩
    obtain ⟨l, hl, hul⟩ := Finset.mem_biUnion.mp hu
    obtain ⟨e, he, hb⟩ := exists_offset_of_supDist u (toTorusSite n c)
    refine ⟨l.image (torusCell F), Finset.mem_image.mpr ⟨l, hl, rfl⟩, torusCell F u,
      Finset.mem_image.mpr ⟨u, hul, rfl⟩, e, (mem_centredCube_odd_iff m e).mpr fun i => ?_, ?_⟩
    · have h1 := hb i
      rw [_root_.YangMills.Construction.TorusFields.supDist_comm] at hd
      exact abs_le_natCast_of_natAbs_le (h1.trans hd)
    · have : toTorusSite n (torusCell F u + siteOfCoords F.top e) = toTorusSite n c := by
        rw [toTorusSite_add hs, toTorusSite_torusCell hs, toTorusSite_siteOfCoords hs, he]
      rw [← torusCell_toTorusSite hs c, ← this, torusCell_toTorusSite hs]
theorem mem_lumpsNeighbourhood_hotLumpCells_iff (hs : ∀ i, F.extent i = n) (V : TorusField n)
    (c : F.Cell) :
    c ∈ lumpsNeighbourhood (hotLumpCells ℓ F V) ↔
      (toTorusSite n c : TorusSite n) ∈ thickening lumpRange (torusHotSites ℓ V) :=
  mem_biUnion_thicken_hotLumpCells_iff hs V c lumpRange
theorem isOrthantRegular_coldRegion (hfit : ℓ.Admissible)
    (hreg : ComplementOfThickenedLumpsRegular) (hLn : ℓ.side ∣ n) (hs : ∀ i, F.extent i = n)
    (V : TorusField n) :
    IsOrthantRegular (cellsOfSites F (coldRegion ℓ V)) 2047 := by
  classical
  have hpos : ∀ i, 0 < F.extent i := fun i => by
    rw [hs i]
    exact Nat.pos_of_ne_zero (NeZero.ne n)
  have hdvd : ∀ i, ℓ.side ∣ F.extent i := fun i => by rw [hs i]; exact hLn
  have hr := hreg.2 ℓ.side ℓ.grid F (hotLumpCells ℓ F V) hfit.L_odd hpos hdvd
    (isLump_of_mem_hotLumpCells hfit hLn hs V)
  have he : cellsOfSites F (coldRegion ℓ V) = cellsOffLumps F (hotLumpCells ℓ F V) := by
    ext c
    rw [mem_cellsOfSites_iff hs]
    unfold coldRegion cellsOffLumps
    rw [Finset.mem_sdiff, Finset.mem_sdiff, mem_lumpsNeighbourhood_hotLumpCells_iff hs]
    simp [mem_torusCells_of_extent hs c]
  rw [he]
  exact hr
theorem isCold_coldRegion (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n) (hs : ∀ i, F.extent i = n)
    (V : TorusField n) :
    BlockAverages.IsCold (cellsOfSites F (coldRegion ℓ V)) F.top ℓ.threshold
      (readAtLevel F F.top V) := by
  classical
  rintro ⟨x, μ, ν⟩ hp
  unfold innerPlaquettes at hp
  obtain ⟨h1, h2, _⟩ := Finset.mem_filter.mp hp
  have hx : x ∈ cellsOfSites F (coldRegion ℓ V) :=
    mem_of_mem_sitesOfCells_top hs (Finset.mem_product.mp h1).1
  rw [mem_cellsOfSites_iff hs] at hx
  rw [plaquetteDefect_readAtLevel_top hs]
  by_contra hc
  push Not at hc
  have hl : torusLumpOf ℓ (toTorusSite n x) ∈ torusHotLumps ℓ V :=
    (mem_torusHotLumps_iff ℓ hfit hLn V _).mpr ⟨_, μ, ν, h2, hc, _, by simp [plaquetteVertices], rfl⟩
  have hz : (toTorusSite n x : TorusSite n) ∈ torusHotSites ℓ V :=
    Finset.mem_biUnion.mpr ⟨_, hl, mem_torusLumpOf_self _⟩
  unfold coldRegion at hx
  refine (Finset.mem_sdiff.mp hx).2 ?_
  unfold thickening
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, _, hz, by simp [supDist_self]⟩
theorem isOrthantRegular_univ (hs : ∀ i, F.extent i = n) (m : ℕ) :
    IsOrthantRegular (cellsOfSites F (Finset.univ : Finset (TorusSite n))) m := by
  intro z
  refine ⟨fun _ => 1, fun _ => Or.inl rfl, fun q _ _ h _ _ => ?_⟩
  rw [mem_cellsOfSites_iff hs]
  exact Finset.mem_univ _
theorem isCold_univ {s : ℝ} (hs : ∀ i, F.extent i = n) (V : TorusField n)
    (hV : TorusFields.IsCold s V) :
    BlockAverages.IsCold (cellsOfSites F (Finset.univ : Finset (TorusSite n))) F.top s
      (readAtLevel F F.top V) := by
  classical
  rintro ⟨x, μ, ν⟩ hp
  unfold innerPlaquettes at hp
  obtain ⟨_, h2, _⟩ := Finset.mem_filter.mp hp
  rw [plaquetteDefect_readAtLevel_top hs]
  exact hV _ _ _ h2
end Regions
section Transfer
variable {ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters} {n n' : ℕ} [NeZero n] [NeZero n']
theorem mem_thickening_hotSites_of_sameBlockPosition (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n)
    (hLn' : ℓ.side ∣ n') {V : TorusField n} {V' : TorusField n'}
    {y : TorusSite n} {y' : TorusSite n'} {m : ℕ} (hm : 2 ^ 16 ≤ m) (hn : 2 * m + 2 < n)
    (hag : FieldsAgreeNear V V' y y' m) (hb : SameBlockPosition ℓ y y') (h : Fin 4 → ℤ)
    (hbox : OffsetInBox (m - 2 ^ 16) h)
    (hz : y + siteOfInt h ∈ thickening lumpRange (torusHotSites ℓ V)) :
    y' + siteOfInt h ∈ thickening lumpRange (torusHotSites ℓ V') := by exact _root_.YangMills.Construction.HoledShares.mem_thickening_of_fieldsAgreeNear (n := n) (n' := n') hfit hLn hLn' hm hn hag hb h hbox hz
theorem not_mem_thickening_of_noHotLumpNear {V : TorusField n} {y : TorusSite n} {m : ℕ}
    (hm : 2 ^ 16 ≤ m) (hno : NoHotLumpNear ℓ V y m) (h : Fin 4 → ℤ)
    (hbox : OffsetInBox (m - 2 ^ 16) h) :
    y + siteOfInt h ∉ thickening lumpRange (torusHotSites ℓ V) := by
  classical
  intro hz
  obtain ⟨u, hu, hd⟩ := (Finset.mem_filter.mp hz).2
  have h1 : supDist y (y + siteOfInt h) ≤ m - 2 ^ 16 :=
    supDist_add_siteOfInt_le _ _ _ fun i => natAbs_le_of_abs_le_natCast (hbox i)
  have h2 := supDist_triangle y (y + siteOfInt h) u
  have h3 := hno u hu
  have h4 : lumpRange = 2 ^ 12 := rfl
  omega
end Transfer
theorem mixedBondDerivative_zero {F : BlockFrame} {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (G : F.GaugeField F.top → E) (V : F.GaugeField F.top)
    (c : Fin 0 → F.Site F.top × Fin 4) (X : Fin 0 → imaginaryQuaternions) :
    mixedBondDerivative G V c X = G V := by apply _root_.YangMills.Construction.BlockAverages.AnalyticCellShares.mixedBondDerivative_zero <;> assumption
theorem abs_levelShare_sub_le_of_agree {δ lam ρ σA cg : ℝ} {N : ℕ → ℝ} {ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters}
    (hC : ColdChainConstants ℓ.coupling δ ℓ.side lam ρ σA cg N) (hfit : ℓ.Admissible)
    (hσ : ℓ.threshold ≤ σA)
    {t n n' : ℕ} [NeZero n] [NeZero n'] {V : TorusField n} {V' : TorusField n'}
    {y : TorusSite n} {y' : TorusSite n'} {m : ℕ}
    (hm : 2 ^ 16 ≤ m) (hn : 2 * m + 2 < n) (hn' : 2 * m + 2 < n')
    (hag : FieldsAgreeNear V V' y y' m)
    (S : Finset (TorusSite n)) (S' : Finset (TorusSite n'))
    (hr : IsOrthantRegular (cellsOfSites (torusFrame ℓ.side t n) S) 2047)
    (hr' : IsOrthantRegular (cellsOfSites (torusFrame ℓ.side t n') S') 2047)
    (hc : BlockAverages.IsCold (cellsOfSites (torusFrame ℓ.side t n) S) (torusFrame ℓ.side t n).top
      ℓ.threshold (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V))
    (hc' : BlockAverages.IsCold (cellsOfSites (torusFrame ℓ.side t n') S')
      (torusFrame ℓ.side t n').top ℓ.threshold
      (readAtLevel (torusFrame ℓ.side t n') (torusFrame ℓ.side t n').top V'))
    (hmem : ∀ h, OffsetInBox (m - 2 ^ 16) h → (y + siteOfInt h ∈ S ↔ y' + siteOfInt h ∈ S')) :
    |levelShare ℓ.coupling ℓ.side (t + 1) S y V - levelShare ℓ.coupling ℓ.side (t + 1) S' y' V'| ≤
      ℓ.threshold ^ 2 * N 0 * Real.exp (-δ * ((m - 2 ^ 16 : ℕ) : ℝ)) := by
  obtain ⟨_, _, _, _, _, hσA, _, _, hthm⟩ := hC
  have hs : ∀ i, (torusFrame ℓ.side t n).extent i = n := fun _ => rfl
  have hs' : ∀ i, (torusFrame ℓ.side t n').extent i = n' := fun _ => rfl
  have hσpos := hfit.σ_pos
  have hamb : IsAdmissibleAmbient (torusFrame ℓ.side t n) := Or.inr fun i => by
    change 64 ≤ n
    omega
  have hamb' : IsAdmissibleAmbient (torusFrame ℓ.side t n') := Or.inr fun i => by
    change 64 ≤ n'
    omega
  have hall := hthm (torusFrame ℓ.side t n) 2047 _ rfl hamb (by norm_num) hr ℓ.threshold _ hσpos hσ hc
  have hagree : AgreeOnBall (cellsOfSites (torusFrame ℓ.side t n) S)
      (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V)
      (cellsOfSites (torusFrame ℓ.side t n') S')
      (readAtLevel (torusFrame ℓ.side t n') (torusFrame ℓ.side t n').top V')
      (torusCell (torusFrame ℓ.side t n) y) (torusCell (torusFrame ℓ.side t n') y')
      (m - 2 ^ 16) := by
    refine ⟨fun i => Or.inr ?_, fun i => Or.inr ?_, fun h hh => ?_, fun b hb => ?_⟩
    · change _ < n
      omega
    · change _ < n'
      omega
    · rw [mem_cellsOfSites_iff hs, mem_cellsOfSites_iff hs', toTorusSite_add hs,
        toTorusSite_add hs', toTorusSite_torusCell hs, toTorusSite_torusCell hs',
        toTorusSite_siteOfCoords hs, toTorusSite_siteOfCoords hs']
      exact hmem h hh
    · have e1 : readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V
          (torusCell (torusFrame ℓ.side t n) y + siteOfCoords _ b.1) b.2 =
            V (y + siteOfInt b.1) b.2 := by
        change V (toTorusSite n _) b.2 = _
        rw [toTorusSite_add hs, toTorusSite_torusCell hs, toTorusSite_siteOfCoords hs]
      have e2 : readAtLevel (torusFrame ℓ.side t n') (torusFrame ℓ.side t n').top V'
          (torusCell (torusFrame ℓ.side t n') y' + siteOfCoords _ b.1) b.2 =
            V' (y' + siteOfInt b.1) b.2 := by
        change V' (toTorusSite n' _) b.2 = _
        rw [toTorusSite_add hs', toTorusSite_torusCell hs', toTorusSite_siteOfCoords hs']
      rw [e1, e2]
      refine hag b ⟨fun i => ?_, fun i => ?_⟩
      · have := hb.1 i
        omega
      · have := hb.2 i
        omega
  have hloc := (hall.2.2.2.2.2 (torusFrame ℓ.side t n') _ _ (torusCell _ y) (torusCell _ y')
    (m - 2 ^ 16) rfl rfl hamb' hr' hc' hagree).1
  have h0 := hloc 0 Fin.elim0 Fin.elim0 (fun l => l.elim0) (fun l => l.elim0)
  rw [mixedBondDerivative_zero, mixedBondDerivative_zero] at h0
  have hk : derivativeScale ℓ.threshold 0 = ℓ.threshold ^ 2 := by simp [derivativeScale]
  rw [hk] at h0
  exact h0
theorem sharesOfHoledFieldsForget_of_complementRegular
    (hreg : ComplementOfThickenedLumpsRegular) : SharesOfHoledFieldsForget := by
  intro δ lam ρ σA cg N ℓ hC hfit hσ t n n' _ _ V V' y y' m hLn hm hn hn' hag
  have hs : ∀ i, (torusFrame ℓ.side t n).extent i = n := fun _ => rfl
  have hs' : ∀ i, (torusFrame ℓ.side t n').extent i = n' := fun _ => rfl
  constructor
  · intro hLn' hb
    refine abs_levelShare_sub_le_of_agree hC hfit hσ hm hn hn' hag _ _
      (isOrthantRegular_coldRegion hfit hreg hLn hs V)
      (isOrthantRegular_coldRegion hfit hreg hLn' hs' V') (isCold_coldRegion hfit hLn hs V)
      (isCold_coldRegion hfit hLn' hs' V') ?_
    intro h hh
    unfold coldRegion
    rw [Finset.mem_sdiff, Finset.mem_sdiff]
    simp only [Finset.mem_univ, true_and, not_iff_not]
    rcases hb with hb | ⟨h1, h2⟩
    · constructor
      · exact mem_thickening_hotSites_of_sameBlockPosition hfit hLn hLn' hm hn hag hb h hh
      · refine mem_thickening_hotSites_of_sameBlockPosition hfit hLn' hLn hm hn' ?_ ?_ h hh
        · intro b hbb
          exact (hag b hbb).symm
        · intro i
          have := hb i
          have h2 : (ℓ.side : ℤ) ∣ (((y i).cast : ℤ) - ((y' i).cast : ℤ)) :=
            Int.dvd_of_emod_eq_zero this
          have h3 : (ℓ.side : ℤ) ∣ (((y' i).cast : ℤ) - ((y i).cast : ℤ)) := by
            have := dvd_neg.mpr h2
            simpa using this
          exact Int.emod_eq_zero_of_dvd h3
    · exact iff_of_false (not_mem_thickening_of_noHotLumpNear hm h1 h hh)
        (not_mem_thickening_of_noHotLumpNear hm h2 h hh)
  · intro hcold hno
    refine abs_levelShare_sub_le_of_agree hC hfit hσ hm hn hn' hag _ _
      (isOrthantRegular_coldRegion hfit hreg hLn hs V) (isOrthantRegular_univ hs' 2047)
      (isCold_coldRegion hfit hLn hs V) (isCold_univ hs' V' hcold) ?_
    intro h hh
    unfold coldRegion
    rw [Finset.mem_sdiff]
    simp only [Finset.mem_univ, true_and, iff_true]
    exact not_mem_thickening_of_noHotLumpNear hm hno h hh
end HoledShares
end YangMills.Construction
end
