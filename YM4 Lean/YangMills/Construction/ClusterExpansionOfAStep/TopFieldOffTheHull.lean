import YangMills.Construction.ClusterExpansionOfAStep.MarksOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.MirrorOfABox
import YangMills.Construction.ClusterExpansionOfAStep.SitesOfTheTopOfAStep
import YangMills.Construction.HoleBesideASecondHole.ComplementOfEnlargedLumpsIsRegular
import YangMills.Construction.HoleBesideASecondHole.TopHotPlaquettesPayProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages LumpContours HoleBounds ColdStepAtMirrorFrames TorusFields TorusLumps TorusMirror StepMarks StepCosts
namespace TopLevelSites
section Torus
variable {F : BlockFrame} {n : ℕ} [NeZero n]
theorem period_top_of_extent (hn : ∀ i, F.extent i = n) (i : Fin 4) : F.period F.top i = n := by
  rw [period_top, hn]
theorem period_depth_of_extent (hn : ∀ i, F.extent i = n) (i : Fin 4) :
    F.period F.depth i = n * F.blockSide := by
  rw [period_depth, hn]
theorem enclosingCell_torusSiteInFrame (hn : ∀ i, F.extent i = n) [NeZero (n * F.blockSide)]
    (x : TorusSite (n * F.blockSide)) :
    enclosingCell (torusSiteInFrame F F.depth x) = torusSiteInFrame F F.top (parentBlock F.blockSide x) := by
  funext i
  have := NeZero.mk (n := n) (NeZero.ne n)
  change (((siteCoords (torusSiteInFrame F F.depth x) i + ((F.blockSide : ℤ) ^ (F.top - F.depth) - 1) / 2) /
      (F.blockSide : ℤ) ^ (F.top - F.depth) : ℤ) : ZMod (F.period F.top i)) =
    ((((parentBlock F.blockSide x i).cast : ℤ)) : ZMod (F.period F.top i))
  rw [top_sub_depth, pow_one, siteCoords_torusSiteInFrame (period_depth_of_extent hn) x i]
  have e := castInt_intCast (m := n) (n := F.period F.top i) (period_top_of_extent hn i).symm
    ((((x i).cast : ℤ) + ((F.blockSide : ℤ) - 1) / 2) / (F.blockSide : ℤ))
  exact e.symm
theorem torusSiteInFrame_mem_cellsOfSites_iff (hn : ∀ i, F.extent i = n) {S : Finset (TorusSite n)}
    {y : TorusSite n} : torusSiteInFrame F F.top y ∈ cellsOfSites F S ↔ y ∈ S := by
  classical
  unfold cellsOfSites
  constructor
  · intro h
    obtain ⟨y', hy', e⟩ := Finset.mem_image.mp h
    have e' : torusSiteInFrame F F.top y' = torusSiteInFrame F F.top y := e
    have := congrArg (toTorusSite n) e'
    rw [toTorusSite_torusSiteInFrame (period_top_of_extent hn),
      toTorusSite_torusSiteInFrame (period_top_of_extent hn)] at this
    exact this ▸ hy'
  · intro h
    exact Finset.mem_image.mpr ⟨y, h, rfl⟩
theorem mem_cellsOfSites_iff (hn : ∀ i, F.extent i = n) {S : Finset (TorusSite n)} {c : F.Cell} :
    c ∈ cellsOfSites F S ↔ toTorusSite n c ∈ S := by
  rw [← torusSiteInFrame_mem_cellsOfSites_iff hn, torusSiteInFrame_toTorusSite (period_top_of_extent hn)]
theorem cellsOfSites_univ (hn : ∀ i, F.extent i = n) :
    cellsOfSites F (Finset.univ : Finset (TorusSite n)) = finiteCells F := by
  ext c
  rw [mem_cellsOfSites_iff hn]
  have hs : ∀ i, 0 < F.extent i := fun i => by rw [hn]; exact Nat.pos_of_ne_zero (NeZero.ne n)
  simp [mem_finiteCells hs c]
theorem isOrthantRegular_finiteCells (hs : ∀ i, 0 < F.extent i) (m : ℕ) :
    IsOrthantRegular (finiteCells F) m :=
  fun _ => ⟨fun _ => 1, fun _ => Or.inl rfl, fun _ _ _ _ _ _ => mem_finiteCells hs _⟩
theorem isCold_readAtLevel {S : Finset F.Cell} {s : ℝ} {W : TorusField n} (hn : ∀ i, F.extent i = n)
    (h : TorusFields.IsCold s W) : BlockAverages.IsCold S F.top s (readAtLevel F F.top W) := by
  rintro ⟨c, μ, ν⟩ hp
  have hlt : μ < ν := (Finset.mem_filter.mp hp).2.1
  rw [plaquetteDefect_readAtLevel_eq (period_top_of_extent hn)]
  exact h _ _ _ hlt
theorem valMinAbs_intCast_cast {p N : ℕ} (hp : p = N) (a : ZMod p) :
    ((((ZMod.cast a : ℤ)) : ZMod N)).valMinAbs = a.valMinAbs := by
  subst hp
  rw [ZMod.intCast_zmod_cast]
theorem readAtLevel_torusSiteInFrame_add (hn : ∀ i, F.extent i = n) (V : TorusField n) (y : TorusSite n)
    (e : Fin 4 → ℤ) (i : Fin 4) :
    readAtLevel F F.top V (torusSiteInFrame F F.top y + siteOfCoords F.top e) i = V (y + siteOfInt e) i := by
  have : readAtLevel F F.top V (torusSiteInFrame F F.top y + siteOfCoords F.top e) i =
      V (toTorusSite n (torusSiteInFrame F F.top y + siteOfCoords F.top e)) i := rfl
  rw [this, toTorusSite_add (period_top_of_extent hn), toTorusSite_torusSiteInFrame (period_top_of_extent hn),
    toTorusSite_siteOfCoords (period_top_of_extent hn)]
theorem readAtLevel_torusSiteInFrame_add' (hn : ∀ i, F.extent i = n) (V : TorusField n) (y : TorusSite n)
    (e : Fin 4 → ℤ) (i : Fin 4) :
    readAtLevel F F.top V (torusSiteInFrame F F.top y + siteOfCoords F.top e) i = V (y + siteOfInt e) i := by apply _root_.YangMills.Construction.TopLevelSites.readAtLevel_torusSiteInFrame_add <;> assumption
theorem reflectedField_readAtLevel (hn : ∀ i, F.extent i = n) {m : ℕ} (hm : 0 < m) (y : TorusSite n)
    (V : TorusField n) :
    reflectedField m (torusSiteInFrame F F.top y) (readAtLevel F F.top V) =
      readAtLevel (reflectedFrame F m) (reflectedFrame F m).top (TorusMirror.mirrorField m y V) := by
  haveI : NeZero (4 * m) := ⟨by omega⟩
  have hp' : ∀ i, (reflectedFrame F m).period (reflectedFrame F m).top i = 4 * m := fun i => by
    rw [period_top]
    rfl
  funext z i
  set z' : TorusSite (4 * m) := toTorusSite (4 * m) z with hz'
  have hc : ∀ l, (z l).valMinAbs = (z' l).valMinAbs := fun l => (valMinAbs_intCast_cast (hp' l) (z l)).symm
  have e1 : (fun l => reflectCoord m ((z l).valMinAbs)) = foldSite m z' := by
    funext l
    rw [hc]
    rfl
  have e2 : (fun l => reflectCoord m
      ((z l).valMinAbs + (Pi.single i 1 : Fin 4 → ℤ) l)) = foldSite m (z' + TorusFields.unitStep (4 * m) i) := by
    funext l
    by_cases hl : l = i
    · subst hl
      rw [foldSite_add_unitStep_self hm, hc]
      simp only [Pi.single_eq_same]
      rfl
    · rw [foldSite_add_unitStep_of_ne z' i l hl, hc]
      simp only [Pi.single_eq_of_ne hl, add_zero]
      rfl
  have key : ∀ (e e' : Fin 4 → ℤ), e = foldSite m z' → e' = foldSite m (z' + TorusFields.unitStep (4 * m) i) →
      (if e' i = e i + 1 then readAtLevel F F.top V (torusSiteInFrame F F.top y + siteOfCoords F.top e) i
        else (readAtLevel F F.top V (torusSiteInFrame F F.top y + siteOfCoords F.top e') i)⁻¹) =
        TorusMirror.mirrorField m y V z' i := by
    rintro _ _ rfl rfl
    unfold TorusMirror.mirrorField
    rw [readAtLevel_torusSiteInFrame_add hn, readAtLevel_torusSiteInFrame_add hn]
  exact key _ _ e1 e2
theorem agreeOnBall_reflectedField (hn : ∀ i, F.extent i = n) {m : ℕ} (hm : 2 ≤ m) (hbig : 2 * m + 2 < n)
    {S : Finset (TorusSite n)} (V : TorusField n) (y : TorusSite n)
    (hbox : ∀ h, WithinRadius m h → y + siteOfInt h ∈ S) :
    AgreeOnBall (cellsOfSites F S) (readAtLevel F F.top V) (finiteCells (reflectedFrame F m))
      (reflectedField m (torusSiteInFrame F F.top y) (readAtLevel F F.top V)) (torusSiteInFrame F F.top y) 0 m := by
  haveI : NeZero (4 * m) := ⟨by omega⟩
  have hs' : ∀ i, 0 < (reflectedFrame F m).extent i := fun i => by
    change 0 < 4 * m
    omega
  have hp' : ∀ i, (reflectedFrame F m).period (reflectedFrame F m).top i = 4 * m := fun i => by
    rw [period_top]
    rfl
  refine ⟨fun i => Or.inr (by rw [hn]; exact hbig), fun i => Or.inr ?_, ?_, ?_⟩
  · change 2 * m + 2 < 4 * m
    omega
  · intro h hh
    constructor
    · intro _
      exact mem_finiteCells hs' _
    · intro _
      rw [← torusSiteInFrame_siteOfInt (period_top_of_extent hn), ← torusSiteInFrame_add (period_top_of_extent hn),
        torusSiteInFrame_mem_cellsOfSites_iff hn]
      exact hbox h hh
  · intro b hb
    rw [reflectedField_readAtLevel hn (by omega), readAtLevel_torusSiteInFrame_add' hn]
    have e : readAtLevel (reflectedFrame F m) (reflectedFrame F m).top (TorusMirror.mirrorField m y V)
        (0 + siteOfCoords (reflectedFrame F m).top b.1) b.2 =
        TorusMirror.mirrorField m y V (toTorusSite (4 * m) (0 + siteOfCoords (reflectedFrame F m).top b.1)) b.2 := rfl
    rw [e, zero_add, toTorusSite_siteOfCoords hp']
    exact (mirrorField_siteOfInt hm y V b hb).symm
end Torus
section Situations
variable {ℓ : StepParameters} {n : ℕ} [NeZero n]
theorem image_lumpOf_toTorusSite {F : BlockFrame} {j N : ℕ} [NeZero N] (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ N)
    (hp : ∀ i, F.period j i = N) (x : F.Site j) :
    open Classical in (lumpOf ℓ.grid x).image (toTorusSite N) = torusLumpOf ℓ (toTorusSite N x) := by
  classical
  have hLpos : 0 < ℓ.side := by have := hfit.L_ge; omega
  have hodd := hfit.L_odd
  have hkey : ∀ h : Fin 4 → ℤ, lumpCorner ℓ (siteOfInt h : TorusSite N) =
      fun i => (stripStart ℓ.grid (h i) : ZMod N) := by
    intro h
    funext i
    exact stripStart_cast_intCast ℓ hfit hLn (h i)
  have hx : toTorusSite N x = siteOfInt (siteCoords x) := rfl
  ext z
  simp only [Finset.mem_image, torusLumpOf, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hy
    rw [toTorusSite_siteOfCoords hp, hx, hkey, hkey]
    funext i
    have hi := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hh i)
    rw [stripStart_eq_of_mem hLpos hodd ℓ.grid (siteCoords x i) (h i) hi.1 hi.2]
  · intro hz
    have hz2 : ∀ i, ∃ k : ℤ, stripStart ℓ.grid ((z i).cast : ℤ) =
        stripStart ℓ.grid (siteCoords x i) + N * k := by
      intro i
      have h1 := congrFun hz i
      rw [hx, hkey] at h1
      have h2 : ((stripStart ℓ.grid ((z i).cast : ℤ) : ℤ) : ZMod N) =
          (stripStart ℓ.grid (siteCoords x i) : ZMod N) := h1
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h2
      obtain ⟨k, hk⟩ := h2
      exact ⟨-k, by linarith⟩
    choose k hk using hz2
    have hdv : ∀ i, (ℓ.side : ℤ) ∣ -(N : ℤ) * k i := fun i =>
      Dvd.dvd.mul_right (Dvd.dvd.neg_right (by exact_mod_cast hLn)) _
    have hstrip : ∀ i, stripStart ℓ.grid (((z i).cast : ℤ) + -(N : ℤ) * k i) =
        stripStart ℓ.grid (siteCoords x i) := by
      intro i
      rw [stripStart_add_dvd hLpos hodd _ _ _ (hdv i), hk]
      ring
    refine ⟨siteOfCoords j fun i => ((z i).cast : ℤ) + -(N : ℤ) * k i, ?_, ?_⟩
    · refine Finset.mem_image.mpr ⟨_, Fintype.mem_piFinset.mpr fun i => Finset.mem_Icc.mpr ?_, rfl⟩
      exact mem_of_stripStart_eq hLpos hodd ℓ.grid (siteCoords x i) _ (hstrip i)
    · rw [toTorusSite_siteOfCoords hp]
      funext i
      simp [siteOfInt]
theorem isLump_image_torusLumpOf {F : BlockFrame} (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n)
    (hn : ∀ i, F.extent i = n) (z : TorusSite n) :
    open Classical in IsLump ℓ.grid ((torusLumpOf ℓ z).image (torusSiteInFrame F F.top)) := by
  classical
  refine ⟨torusSiteInFrame F F.top z, ?_⟩
  have e := image_lumpOf_toTorusSite (ℓ := ℓ) hfit hLn (period_top_of_extent hn) (torusSiteInFrame F F.top z)
  rw [toTorusSite_torusSiteInFrame (period_top_of_extent hn)] at e
  rw [← e, Finset.image_image]
  have hid : (torusSiteInFrame F F.top ∘ toTorusSite n : F.Cell → F.Cell) = id :=
    funext fun c => torusSiteInFrame_toTorusSite (period_top_of_extent hn) c
  rw [hid, Finset.image_id]
theorem mem_thicken_iff {F : BlockFrame} {j m : ℕ} {X : Finset (F.Site j)} {c : F.Site j} :
    c ∈ thicken m X ↔ ∃ x ∈ X, ∃ h ∈ centredCube (2 * m + 1), c = x + siteOfCoords j h := by
  simp only [thicken, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, h, hh, rfl⟩
    exact ⟨x, hx, h, hh, rfl⟩
  · rintro ⟨x, hx, h, hh, rfl⟩
    exact ⟨x, hx, h, hh, rfl⟩
theorem halfWidth_two_mul_add_one (R : ℕ) : halfWidth (2 * R + 1) = R := by
  unfold halfWidth
  push_cast
  omega
theorem mem_biUnion_thicken_iff {F : BlockFrame} (hn : ∀ i, F.extent i = n) (R : ℕ)
    (X : Finset (Finset (TorusSite n))) (c : F.Cell) :
    open Classical in c ∈ (X.image fun l => l.image (torusSiteInFrame F F.top)).biUnion (thicken R) ↔
      toTorusSite n c ∈ thickening R (X.biUnion id) := by
  classical
  rw [mem_thickening]
  constructor
  · intro h
    obtain ⟨l, hl, hc2⟩ := Finset.mem_biUnion.mp h
    obtain ⟨l₀, hl₀, rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨x, hx, e, he, rfl⟩ := mem_thicken_iff.mp hc2
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    refine ⟨z, Finset.mem_biUnion.mpr ⟨l₀, hl₀, hz⟩, ?_⟩
    rw [toTorusSite_add (period_top_of_extent hn), toTorusSite_torusSiteInFrame (period_top_of_extent hn),
      toTorusSite_siteOfCoords (period_top_of_extent hn), supDist_comm]
    refine supDist_add_siteOfInt_le z e _ fun i => ?_
    have := (mem_centredCube_iff e).mp he i
    rw [halfWidth_two_mul_add_one] at this
    omega
  · rintro ⟨x, hx, hd⟩
    obtain ⟨l₀, hl₀, hxl⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨e, he, hb⟩ := exists_offset_of_supDist x (toTorusSite n c)
    refine Finset.mem_biUnion.mpr ⟨l₀.image (torusSiteInFrame F F.top), Finset.mem_image.mpr ⟨l₀, hl₀, rfl⟩, ?_⟩
    refine mem_thicken_iff.mpr ⟨torusSiteInFrame F F.top x, Finset.mem_image.mpr ⟨x, hxl, rfl⟩, e, ?_, ?_⟩
    · rw [mem_centredCube_iff, halfWidth_two_mul_add_one]
      intro i
      have h1 := hb i
      rw [supDist_comm] at h1
      have h2 : (e i).natAbs ≤ R := h1.trans hd
      omega
    · apply toTorusSite_injective (period_top_of_extent hn)
      rw [toTorusSite_add (period_top_of_extent hn), toTorusSite_torusSiteInFrame (period_top_of_extent hn),
        toTorusSite_siteOfCoords (period_top_of_extent hn), ← he]
theorem mem_torusCells_of_pos {F : BlockFrame} (hs : ∀ i, 0 < F.extent i) (c : F.Cell) : c ∈ torusCells F := by apply _root_.YangMills.Construction.HoleSavings.TopHotPlaquetteCost.mem_torusCells <;> assumption
theorem isOrthantRegular_cellsOfSites_compl_thickening {F : BlockFrame}
    (hc : ComplementOfThickenedLumpsRegular) (hfit : ℓ.Admissible)
    (hLn : ℓ.side ∣ n) (hn : ∀ i, F.extent i = n) (V : TorusField n) :
    IsOrthantRegular (cellsOfSites F (Finset.univ \ thickening lumpRange (torusHotSites ℓ V))) 2047 := by
  classical
  set H : Finset (Finset F.Cell) := (torusHotLumps ℓ V).image fun l => l.image (torusSiteInFrame F F.top) with hH
  have hs : ∀ i, 0 < F.extent i := fun i => by rw [hn]; exact Nat.pos_of_ne_zero (NeZero.ne n)
  have hlump : ∀ l ∈ H, IsLump ℓ.grid l := by
    intro l hl
    obtain ⟨l₀, hl₀, rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨x, μ, ν, _, _, z, _, rfl⟩ := (mem_torusHotLumps_iff ℓ hfit hLn V l₀).mp hl₀
    convert isLump_image_torusLumpOf hfit hLn hn z
  have hreg := hc.2 ℓ.side ℓ.grid F H hfit.L_odd hs (fun i => by rw [hn]; exact hLn) hlump
  have hnear : ∀ c : F.Cell, c ∈ lumpsNeighbourhood H ↔
      toTorusSite n c ∈ thickening lumpRange (torusHotSites ℓ V) :=
    fun c => mem_biUnion_thicken_iff hn lumpRange (torusHotLumps ℓ V) c
  have e : cellsOffLumps F H = cellsOfSites F (Finset.univ \ thickening lumpRange (torusHotSites ℓ V)) := by
    ext c
    rw [mem_cellsOfSites_iff hn]
    unfold cellsOffLumps
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, mem_torusCells_of_pos hs c, hnear]
  rwa [← e]
theorem isCold_cellsOfSites_compl_thickening {F : BlockFrame} (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n)
    (hn : ∀ i, F.extent i = n) (V : TorusField n) :
    BlockAverages.IsCold (cellsOfSites F (Finset.univ \ thickening lumpRange (torusHotSites ℓ V))) F.top
      ℓ.threshold (readAtLevel F F.top V) := by
  classical
  rintro ⟨c, μ, ν⟩ hp
  have hlt : μ < ν := (Finset.mem_filter.mp hp).2.1
  have hc : c ∈ sitesOfCells (cellsOfSites F (Finset.univ \ thickening lumpRange (torusHotSites ℓ V))) F.top :=
    (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  rw [mem_sitesOfCells_top, mem_cellsOfSites_iff hn] at hc
  rw [plaquetteDefect_readAtLevel_eq (period_top_of_extent hn)]
  by_contra hcon
  have hge : ℓ.threshold ≤ curvature V (toTorusSite n c) μ ν := not_lt.mp hcon
  have hl : torusLumpOf ℓ (toTorusSite n c) ∈ torusHotLumps ℓ V :=
    (mem_torusHotLumps_iff ℓ hfit hLn V _).mpr
      ⟨_, μ, ν, hlt, hge, toTorusSite n c, by simp [plaquetteVertices], rfl⟩
  have hz : toTorusSite n c ∈ torusHotSites ℓ V := Finset.mem_biUnion.mpr ⟨_, hl, mem_torusLumpOf_self _⟩
  have : toTorusSite n c ∈ thickening lumpRange (torusHotSites ℓ V) :=
    (mem_thickening _ _ _).mpr ⟨_, hz, by rw [supDist_self]; exact Nat.zero_le _⟩
  exact (Finset.mem_sdiff.mp hc).2 this
theorem lt_supDist_of_not_mem_minimalHull {r' : ℕ} {V : TorusField n} {y z : TorusSite n}
    (hy : y ∉ minimalHull ℓ r' V) (hz : z ∈ torusHotSites ℓ V) : 2 * r' < supDist y z := by
  by_contra hcon
  exact hy ((mem_thickening _ _ _).mpr ⟨z, hz, not_lt.mp hcon⟩)
theorem stepSituation_regular_and_cold (hc : ComplementOfThickenedLumpsRegular) (hfit : ℓ.Admissible)
    {r' : ℕ} {V : TorusField n} {S C : Finset (TorusSite n)} {s : ℝ} (hsit : IsStepSituation ℓ r' V S C s) :
    0 < s ∧ s ≤ 2 * ℓ.threshold ∧ 4096 ≤ n ∧ ∀ F : BlockFrame, (∀ i, F.extent i = n) →
      IsOrthantRegular (cellsOfSites F S) 2047 ∧
        BlockAverages.IsCold (cellsOfSites F S) F.top s (readAtLevel F F.top V) := by
  have hσ := hfit.σ_pos
  have hn₀ := hfit.n₀_ge
  have hLge := hfit.L_ge
  rcases hsit with ⟨hb, rfl, rfl, rfl⟩ | ⟨hb, hcold, rfl, rfl, rfl⟩
  · refine ⟨hσ, by linarith, ?_, fun F hn =>
      ⟨isOrthantRegular_cellsOfSites_compl_thickening hc hfit hb.1 hn V,
        isCold_cellsOfSites_compl_thickening hfit hb.1 hn V⟩⟩
    have := hb.2
    nlinarith
  · refine ⟨by linarith, by linarith, by omega, fun F hn => ?_⟩
    rw [cellsOfSites_univ hn]
    exact ⟨isOrthantRegular_finiteCells (fun i => by rw [hn]; omega) _, isCold_readAtLevel hn hcold⟩
theorem stepSituation_box_of_not_mem (hfit : ℓ.Admissible) {r r' : ℕ} (hr : RangesAdmissible r r')
    {V : TorusField n} {S C : Finset (TorusSite n)} {s : ℝ} (hsit : IsStepSituation ℓ r' V S C s)
    {y : TorusSite n} (hy : y ∉ C) :
    (∀ h, WithinRadius (r / 2 ^ 11 + 1) h → y + siteOfInt h ∈ S) ∧
    ∀ (a : Fin 4 → ℤ) (μ ν : Fin 4), μ < ν →
      (∀ d ∈ plaquetteOffsets μ ν, OffsetInBox (r / 2 ^ 11) (a + d)) → curvature V (y + siteOfInt a) μ ν < s := by
  have hnear := hr.le_succ
  have hlarge := hr.large
  rcases hsit with ⟨hb, rfl, rfl, rfl⟩ | ⟨hb, hcold, rfl, rfl, rfl⟩
  · constructor
    · intro h hh
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hin => ?_⟩
      obtain ⟨x, hx, hd⟩ := (mem_thickening _ _ _).mp hin
      have h1 := lt_supDist_of_not_mem_minimalHull hy hx
      have h2 : supDist y (y + siteOfInt h) ≤ r / 2 ^ 11 + 1 := supDist_add_siteOfInt_le y h _ fun i => by
        have := abs_le.mp (hh i)
        omega
      have h3 := supDist_triangle y (y + siteOfInt h) x
      unfold lumpRange at hd
      omega
    · intro a μ ν hlt hbox
      by_contra hcon
      have hge : ℓ.threshold ≤ curvature V (y + siteOfInt a) μ ν := not_lt.mp hcon
      have hl : torusLumpOf ℓ (y + siteOfInt a) ∈ torusHotLumps ℓ V :=
        (mem_torusHotLumps_iff ℓ hfit hb.1 V _).mpr ⟨_, μ, ν, hlt, hge, _, by simp [plaquetteVertices], rfl⟩
      have hz : y + siteOfInt a ∈ torusHotSites ℓ V := Finset.mem_biUnion.mpr ⟨_, hl, mem_torusLumpOf_self _⟩
      have h1 := lt_supDist_of_not_mem_minimalHull hy hz
      have h0 : (0 : Fin 4 → ℤ) ∈ plaquetteOffsets μ ν := by simp [plaquetteOffsets]
      have hbx := hbox 0 h0
      have h2 : supDist y (y + siteOfInt a) ≤ r / 2 ^ 11 := supDist_add_siteOfInt_le y a _ fun i => by
        have := abs_le.mp (hbx i)
        simp only [add_zero] at this
        omega
      omega
  · exact ⟨fun _ _ => Finset.mem_univ _, fun a μ ν hlt _ => hcold _ _ _ hlt⟩
theorem stepSituation_eq_univ_of_small (hfit : ℓ.Admissible) {r r' : ℕ} (hr : RangesAdmissible r r')
    {V : TorusField n} {S C : Finset (TorusSite n)} {s : ℝ} (hsit : IsStepSituation ℓ r' V S C s)
    {y : TorusSite n} (hy : y ∉ C) (hsmall : ¬ 4 * (r / 2 ^ 11) + 5 < n) : S = Finset.univ := by
  have hnear := hr.le_succ
  have hlarge := hr.large
  rcases hsit with ⟨hb, rfl, rfl, rfl⟩ | ⟨hb, hcold, rfl, rfl, rfl⟩
  · have hempty : torusHotSites ℓ V = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun z hz => ?_
      have h1 := lt_supDist_of_not_mem_minimalHull hy hz
      have h2 : supDist y z ≤ n / 2 := by
        rw [supDist_le_iff]
        intro i
        exact ZMod.natAbs_valMinAbs_le _
      omega
    rw [hempty]
    simp [thickening]
  · rfl
theorem isCold_reflectedField {F : BlockFrame} (hn : ∀ i, F.extent i = n) {m : ℕ} (hm : 0 < m) {s : ℝ}
    (hs : 0 < s) (V : TorusField n) (y : TorusSite n)
    (hcold : ∀ (a : Fin 4 → ℤ) (μ ν : Fin 4), μ < ν → (∀ d ∈ plaquetteOffsets μ ν, OffsetInBox m (a + d)) →
      curvature V (y + siteOfInt a) μ ν < s) :
    BlockAverages.IsCold (finiteCells (reflectedFrame F m)) (reflectedFrame F m).top s
      (reflectedField m (torusSiteInFrame F F.top y) (readAtLevel F F.top V)) := by
  haveI : NeZero (4 * m) := ⟨by omega⟩
  rw [reflectedField_readAtLevel hn hm]
  exact isCold_readAtLevel (n := 4 * m) (fun _ => rfl) (isCold_mirrorField hm y V hs hcold)
end Situations
section Bonds
variable {F : BlockFrame} {n : ℕ} [NeZero n]
theorem fineBondAt_enclosingCell_cellOffset (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (x : F.Site F.depth) (i : Fin 4) :
    fineBondAt (enclosingCell x) 0 (cellOffset x) i = (x, i) := by
  unfold fineBondAt
  have e : (enclosingCell x : F.Cell) + siteOfCoords F.top 0 = enclosingCell x := by
    rw [siteOfCoords_zero, add_zero]
  rw [e, (centre_cellOffset hL hs x).2]
theorem fineBondAt_zero {F' : BlockFrame} (hne : ∀ i, NeZero (F'.period F'.top i)) (o : Fin 4 → ℤ) (i : Fin 4) :
    fineBondAt (0 : F'.Cell) 0 o i = (siteOfCoords F'.depth o, i) := by
  unfold fineBondAt
  have e : ((0 : F'.Cell) + siteOfCoords F'.top 0 : F'.Cell) = 0 := by
    rw [siteOfCoords_zero, add_zero]
  have e2 : (cellCentre F'.depth (0 : F'.Cell) : F'.Site F'.depth) = 0 := by
    funext l
    have := hne l
    simp [cellCentre, siteOfCoords, siteCoords]
  rw [e, e2, zero_add]
theorem cellSupDist_self (y : F.Cell) : cellSupDist y y = 0 := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_self <;> assumption
theorem cellSupDist_add_unitStep_le (hs : ∀ i, 0 < F.extent i) (c : F.Cell) (i : Fin 4) :
    cellSupDist c (c + BlockAverages.unitStep F.top i) ≤ 1 := by
  unfold cellSupDist
  refine Finset.sup_le fun l _ => ?_
  haveI : NeZero (F.period F.top l) := ⟨by rw [period_top]; exact (hs l).ne'⟩
  have e : c l - (c + BlockAverages.unitStep F.top i : F.Cell) l =
      ((-(Pi.single i 1 : Fin 4 → ℤ) l : ℤ) : ZMod (F.period F.top l)) := by
    simp [BlockAverages.unitStep, siteOfCoords]
  rw [e]
  refine (natAbs_valMinAbs_intCast_le _).trans ?_
  by_cases hl : l = i
  · subst hl
    simp
  · simp [Pi.single_eq_of_ne hl]
theorem cellSupDist_enclosingCell_step_le (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (x : F.Site F.depth) (i : Fin 4) :
    cellSupDist (enclosingCell x) (enclosingCell (x + BlockAverages.unitStep F.depth i)) ≤ 1 := by
  by_cases hc : IsCrossingBond (x, i)
  · rw [enclosingCell_add_unitStep hL hs x i hc]
    exact cellSupDist_add_unitStep_le (fun i => by have := hs i; omega) _ _
  · have e : enclosingCell (x + BlockAverages.unitStep F.depth i) = enclosingCell x := by
      by_contra hne
      exact hc hne
    rw [e, cellSupDist_self]
    exact Nat.zero_le _
theorem cellOffset_torusSiteInFrame (hn : ∀ i, F.extent i = n) (hL : Odd F.blockSide) (h2 : 2 ≤ n)
    [NeZero (n * F.blockSide)] (x : TorusSite (n * F.blockSide)) (l : Fin 4) :
    cellOffset (torusSiteInFrame F F.depth x) l = offsetFromCentre F.blockSide ((x l).cast : ℤ) := by
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by rw [hn]; exact h2
  obtain ⟨hc, he⟩ := centre_cellOffset hL hs (torusSiteInFrame F F.depth x)
  obtain ⟨e, hcoord, _⟩ := siteCoords_centre_add hL hs (enclosingCell (torusSiteInFrame F F.depth x)) _ hc l
  rw [he, siteCoords_torusSiteInFrame (period_depth_of_extent hn)] at hcoord
  have hLpos : 0 < F.blockSide := hL.pos
  have hb := (mem_centredCube_iff _).mp hc l
  rw [hcoord]
  have e3 : (F.blockSide : ℤ) * siteCoords (enclosingCell (torusSiteInFrame F F.depth x)) l +
      cellOffset (torusSiteInFrame F F.depth x) l + (F.extent l : ℤ) * F.blockSide * e =
      ((F.blockSide : ℤ) * siteCoords (enclosingCell (torusSiteInFrame F F.depth x)) l +
        (F.extent l : ℤ) * F.blockSide * e) + cellOffset (torusSiteInFrame F F.depth x) l := by ring
  rw [e3, offsetFromCentre_add_of_dvd hLpos hL _ _
    ⟨siteCoords (enclosingCell (torusSiteInFrame F F.depth x)) l + (F.extent l : ℤ) * e, by ring⟩
    (abs_le.mpr hb)]
theorem isAxialTreeBond_torusSiteInFrame_iff (hn : ∀ i, F.extent i = n) (hL : Odd F.blockSide) (h2 : 2 ≤ n)
    [NeZero (n * F.blockSide)] (x : TorusSite (n * F.blockSide)) (i : Fin 4) :
    IsAxialTreeBond (torusSiteInFrame F F.depth x, i) ↔
      IsTreeOffset F.blockSide ((fun l => offsetFromCentre F.blockSide ((x l).cast : ℤ)), i) := by
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by rw [hn]; exact h2
  obtain ⟨hc, he⟩ := centre_cellOffset hL hs (torusSiteInFrame F F.depth x)
  have e : cellOffset (torusSiteInFrame F F.depth x) = fun l => offsetFromCentre F.blockSide ((x l).cast : ℤ) :=
    funext (cellOffset_torusSiteInFrame hn hL h2 x)
  rw [← e]
  conv_lhs => rw [← he]
  exact isAxialTreeBond_iff hL hs _ _ hc i
theorem isCrossingBond_torusSiteInFrame_iff (hn : ∀ i, F.extent i = n) (hL : Odd F.blockSide) (h2 : 2 ≤ n)
    [NeZero (n * F.blockSide)] (x : TorusSite (n * F.blockSide)) (i : Fin 4) :
    IsCrossingBond (torusSiteInFrame F F.depth x, i) ↔
      offsetFromCentre F.blockSide ((x i).cast : ℤ) = halfWidth F.blockSide := by
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by rw [hn]; exact h2
  obtain ⟨hc, he⟩ := centre_cellOffset hL hs (torusSiteInFrame F F.depth x)
  rw [← cellOffset_torusSiteInFrame hn hL h2 x i]
  conv_lhs => rw [← he]
  exact isCrossingBond_iff hL hs _ _ hc i
theorem parentBlock_add_unitStep (hn : ∀ i, F.extent i = n) (hL : Odd F.blockSide) (h2 : 2 ≤ n)
    [NeZero (n * F.blockSide)] (x : TorusSite (n * F.blockSide)) (i : Fin 4) :
    parentBlock F.blockSide (x + TorusFields.unitStep (n * F.blockSide) i) = parentBlock F.blockSide x ∨
      parentBlock F.blockSide (x + TorusFields.unitStep (n * F.blockSide) i) =
        parentBlock F.blockSide x + TorusFields.unitStep n i := by
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by rw [hn]; exact h2
  have hnext : torusSiteInFrame F F.depth (x + TorusFields.unitStep (n * F.blockSide) i) =
      torusSiteInFrame F F.depth x + BlockAverages.unitStep F.depth i := by
    apply toTorusSite_injective (period_depth_of_extent hn)
    rw [toTorusSite_torusSiteInFrame (period_depth_of_extent hn), toTorusSite_add (period_depth_of_extent hn),
      toTorusSite_torusSiteInFrame (period_depth_of_extent hn), toTorusSite_unitStep (period_depth_of_extent hn)]
  have c1 := enclosingCell_torusSiteInFrame hn (x + TorusFields.unitStep (n * F.blockSide) i)
  have c0 := enclosingCell_torusSiteInFrame hn x
  by_cases hcr : IsCrossingBond (torusSiteInFrame F F.depth x, i)
  · right
    have := enclosingCell_add_unitStep hL hs _ i hcr
    rw [← hnext, c1, c0] at this
    have e := congrArg (toTorusSite n) this
    rw [toTorusSite_torusSiteInFrame (period_top_of_extent hn), toTorusSite_add (period_top_of_extent hn),
      toTorusSite_torusSiteInFrame (period_top_of_extent hn), toTorusSite_unitStep (period_top_of_extent hn)] at e
    exact e
  · left
    have : enclosingCell (torusSiteInFrame F F.depth x + BlockAverages.unitStep F.depth i) =
        enclosingCell (torusSiteInFrame F F.depth x) := by
      by_contra hne
      exact hcr hne
    rw [← hnext, c1, c0] at this
    have e := congrArg (toTorusSite n) this
    rw [toTorusSite_torusSiteInFrame (period_top_of_extent hn),
      toTorusSite_torusSiteInFrame (period_top_of_extent hn)] at e
    exact e
theorem torusSiteInFrame_mem_sitesOfCells (hn : ∀ i, F.extent i = n) (hL : Odd F.blockSide) (h2 : 2 ≤ n)
    [NeZero (n * F.blockSide)] {S : Finset (TorusSite n)} (u : TorusSite (n * F.blockSide))
    (hu : parentBlock F.blockSide u ∈ S) :
    torusSiteInFrame F F.depth u ∈ sitesOfCells (cellsOfSites F S) F.depth := by
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by rw [hn]; exact h2
  rw [mem_sitesOfCells]
  obtain ⟨hc, he⟩ := centre_cellOffset hL hs (torusSiteInFrame F F.depth u)
  refine ⟨enclosingCell (torusSiteInFrame F F.depth u), ?_, cellOffset (torusSiteInFrame F F.depth u), ?_, he.symm⟩
  · rw [enclosingCell_torusSiteInFrame hn, torusSiteInFrame_mem_cellsOfSites_iff hn]
    exact hu
  · rw [top_sub_depth, pow_one]
    exact hc
theorem mem_chordBonds_of_parentBlock (hn : ∀ i, F.extent i = n) (hL : Odd F.blockSide) (h2 : 2 ≤ n)
    [NeZero (n * F.blockSide)] {S : Finset (TorusSite n)} (x : TorusSite (n * F.blockSide)) (i : Fin 4)
    (hnt : ¬ IsAxialTreeBond (torusSiteInFrame F F.depth x, i)) (h1 : parentBlock F.blockSide x ∈ S)
    (h3 : parentBlock F.blockSide (x + TorusFields.unitStep (n * F.blockSide) i) ∈ S) :
    (torusSiteInFrame F F.depth x, i) ∈ chordBonds (cellsOfSites F S) := by
  classical
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by rw [hn]; exact h2
  have hsite : ∀ u : TorusSite (n * F.blockSide), parentBlock F.blockSide u ∈ S →
      torusSiteInFrame F F.depth u ∈ sitesOfCells (cellsOfSites F S) F.depth := by
    intro u hu
    rw [mem_sitesOfCells]
    obtain ⟨hc, he⟩ := centre_cellOffset hL hs (torusSiteInFrame F F.depth u)
    refine ⟨enclosingCell (torusSiteInFrame F F.depth u), ?_, cellOffset (torusSiteInFrame F F.depth u), ?_, he.symm⟩
    · rw [enclosingCell_torusSiteInFrame hn, torusSiteInFrame_mem_cellsOfSites_iff hn]
      exact hu
    · rw [top_sub_depth, pow_one]
      exact hc
  have hnext : torusSiteInFrame F F.depth (x + TorusFields.unitStep (n * F.blockSide) i) =
      torusSiteInFrame F F.depth x + BlockAverages.unitStep F.depth i := by
    apply toTorusSite_injective (period_depth_of_extent hn)
    rw [toTorusSite_torusSiteInFrame (period_depth_of_extent hn), toTorusSite_add (period_depth_of_extent hn),
      toTorusSite_torusSiteInFrame (period_depth_of_extent hn), toTorusSite_unitStep (period_depth_of_extent hn)]
  unfold chordBonds innerBonds
  refine Finset.mem_filter.mpr
    ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hsite x h1, Finset.mem_univ _⟩, ?_⟩, hnt⟩
  change torusSiteInFrame F F.depth x + BlockAverages.unitStep F.depth i ∈ _
  rw [← hnext]
  exact hsite _ h3
end Bonds
end TopLevelSites
end YangMills.Construction
end
