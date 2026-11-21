import YangMills.Construction.HoleBesideASecondHole.CellsPutBackProof
import YangMills.Construction.HoleBesideASecondHole.DistancesBlocksAndLumpsProof
import YangMills.Construction.HoleBesideASecondHole.HotLumpsOfAStepProof
import YangMills.Construction.HoleBesideASecondHole.TorusAtAFrameDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages TorusFields TorusLumps FrameTransfer LumpContours HoleOnTori StepCosts
namespace TorusFrames
variable {F : BlockFrame} {j m : ℕ}
theorem top_sub_depth (G : BlockFrame) : G.top - G.depth = 1 := by apply _root_.YangMills.Construction.GaugeFixing.top_sub_depth <;> assumption
theorem period_top (G : BlockFrame) (k : Fin 4) : G.period G.top k = G.extent k := by apply _root_.YangMills.Construction.GaugeFixing.period_top <;> assumption
theorem period_depth (G : BlockFrame) (k : Fin 4) : G.period G.depth k = G.extent k * G.blockSide := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.MinimizingChart.period_depth <;> assumption
theorem siteCoords_torusToFrame (hm : ∀ k, F.period j k = m) (x : TorusSite m) (k : Fin 4) :
    siteCoords (torusToFrame F j x) k = ((x k).cast : ℤ) :=
  intCast_cast_of_eq (hm k).symm (x k)
theorem torusToFrame_sub (hm : ∀ k, F.period j k = m) (x y : TorusSite m) :
    torusToFrame F j (x - y) = torusToFrame F j x - torusToFrame F j y := by
  funext k
  exact cast_sub_of_eq (hm k).symm (x k) (y k)
theorem valMinAbs_torusToFrame (hm : ∀ k, F.period j k = m) (x : TorusSite m) (k : Fin 4) :
    (torusToFrame F j x k).valMinAbs = (x k).valMinAbs :=
  valMinAbs_cast_of_eq (hm k).symm (x k)
theorem mem_centredCube_iff (M : ℕ) (h : Fin 4 → ℤ) :
    h ∈ centredCube M ↔ ∀ k, -(((M : ℤ) - 1) / 2) ≤ h k ∧ h k ≤ ((M : ℤ) - 1) / 2 := by apply _root_.YangMills.Construction.LumpContours.CutAction.mem_centredCube <;> assumption
theorem sitesOfCells_top (S : Finset F.Cell) : sitesOfCells S F.top = S := by apply _root_.YangMills.Construction.Reinsertion.sitesOfCells_top <;> assumption
theorem enclosingCell_torusToFrame {n : ℕ} (hn : ∀ k, F.period F.top k = n)
    (ht : ∀ k, F.period F.depth k = n * F.blockSide)
    (x : TorusSite (n * F.blockSide)) :
    enclosingCell (torusToFrame F F.depth x) = torusToFrame F F.top (parentBlock F.blockSide x) := by
  funext k
  have hc : siteCoords (torusToFrame F F.depth x) k = ((x k).cast : ℤ) := siteCoords_torusToFrame ht x k
  simp only [enclosingCell, siteOfCoords, top_sub_depth, pow_one]
  rw [hc]
  simp only [parentBlock, torusToFrame, siteOfCoords]
  exact (cast_intCast_of_eq (hn k).symm _).symm
theorem mem_sitesBelow_iff (hL : Odd F.blockSide) (x : F.Site F.depth) (c : F.Cell) :
    x ∈ sitesBelow F.depth c ↔ enclosingCell x = c := by apply _root_.YangMills.Construction.LumpContours.mem_sitesBelow_iff <;> assumption
theorem sitesOfTorus_thickening (hm : ∀ k, F.period j k = m) [NeZero m] (r : ℕ) (X : Finset (TorusSite m)) :
    sitesOfTorus F j (thickening r X) = thicken r (sitesOfTorus F j X) := by
  have hc : ∀ e : Fin 4 → ℤ, e ∈ centredCube (2 * r + 1) ↔ ∀ k, (e k).natAbs ≤ r := by
    intro e
    rw [mem_centredCube_iff]
    have : (((2 * r + 1 : ℕ) : ℤ) - 1) / 2 = r := by
      push_cast
      omega
    rw [this]
    refine forall_congr' fun k => ?_
    omega
  ext y
  rw [mem_sitesOfTorus hm, mem_thickening]
  simp only [thicken, sitesOfTorus_eq_image, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, hd⟩
    obtain ⟨e, he, hb⟩ := exists_offset_of_supDist x (frameToTorus m y)
    refine ⟨torusToFrame F j x, ⟨x, hx, rfl⟩, e, ?_, ?_⟩
    · rw [hc]
      intro k
      have := hb k
      rw [_root_.YangMills.Construction.TorusFields.supDist_comm] at this
      omega
    · rw [← torusToFrame_siteOfInt hm, ← torusToFrame_add hm, ← he, torusToFrame_frameToTorus hm]
  · rintro ⟨_, ⟨x, hx, rfl⟩, e, he, rfl⟩
    refine ⟨x, hx, ?_⟩
    have h1 : frameToTorus m (torusToFrame F j x + siteOfCoords j e) = x + siteOfInt e := by
      rw [← torusToFrame_siteOfInt hm, ← torusToFrame_add hm, frameToTorus_torusToFrame hm]
    rw [h1, _root_.YangMills.Construction.TorusFields.supDist_comm]
    exact supDist_add_siteOfInt_le x e r ((hc e).1 he)
theorem cutBonds_sitesOfTorus (hm : ∀ k, F.period j k = m) [NeZero m] (X : Finset (TorusSite m)) :
    cutBonds (sitesOfTorus F j X) = (bondsWithin X).image fun c => (torusToFrame F j c.1, c.2) := by
  have hb : ∀ x : TorusSite m, ∀ i, torusToFrame F j (x + TorusFields.unitStep m i) =
      torusToFrame F j x + BlockAverages.unitStep j i := by
    intro x i
    rw [torusToFrame_add hm, torusToFrame_unitStep hm]
  ext ⟨y, i⟩
  rw [mem_cutBonds_iff]
  simp only [Finset.mem_image, bondsWithin, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(frameToTorus m y, i), ⟨(mem_sitesOfTorus hm X y).1 h1, ?_⟩, ?_⟩
    · rw [← torusToFrame_mem_sitesOfTorus hm, hb, torusToFrame_frameToTorus hm]
      exact h2
    · simp only [torusToFrame_frameToTorus hm]
  · rintro ⟨⟨x, i'⟩, ⟨h1, h2⟩, e⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
    refine ⟨(torusToFrame_mem_sitesOfTorus hm X x).2 h1, ?_⟩
    rw [← hb, torusToFrame_mem_sitesOfTorus hm]
    exact h2
theorem mem_torusCells_of_extent {n : ℕ} [NeZero n] (hs : ∀ i, F.extent i = n) (y : F.Cell) :
    y ∈ torusCells F := by
  refine Finset.mem_image.2 ⟨siteCoords y, Fintype.mem_piFinset.2 fun k => Finset.mem_Icc.2 ?_, ?_⟩
  · have hp : F.period F.top k = n := by rw [period_top, hs]
    have : NeZero (F.period F.top k) := by rw [hp]; infer_instance
    have h1 : siteCoords y k = ((y k).val : ℤ) := by
      simp [siteCoords, ZMod.natCast_val]
    have h2 : (y k).val < n := lt_of_lt_of_eq (ZMod.val_lt (y k)) hp
    rw [h1]
    simp only [Pi.zero_apply]
    rw [hs]
    omega
  · exact _root_.YangMills.Construction.FrameTransfer.siteOfCoords_siteCoords y
theorem mem_levelSites (hm : ∀ k, F.period j k = m) [NeZero m] (y : F.Site j) : y ∈ levelSites F j := by exact _root_.YangMills.Construction.TorusFrames.HotStepLumps.mem_levelSites (F := F) (j := j) (m := m) hm y
theorem levelSites_eq_sitesOfTorus (hm : ∀ k, F.period j k = m) [NeZero m] :
    levelSites F j = sitesOfTorus F j (Finset.univ : Finset (TorusSite m)) := by apply _root_.YangMills.Construction.TorusFrames.HotStepLumps.levelSites_eq_image <;> assumption
theorem torusAtFrameStatement_holds : torusAtFrameStatement := by
  intro L _ hodd n _ F hFL hside
  subst hFL
  have hn : ∀ k, F.period F.top k = n := fun k => by rw [period_top, hside]
  have ht : ∀ k, F.period F.depth k = n * F.blockSide := fun k => by rw [period_depth, hside]
  have hcell : ∀ y : F.Site F.depth,
      frameToTorus n (enclosingCell y) = parentBlock F.blockSide (frameToTorus (n * F.blockSide) y) := by
    intro y
    have := enclosingCell_torusToFrame hn ht (frameToTorus (n * F.blockSide) y)
    rw [torusToFrame_frameToTorus ht] at this
    rw [this, frameToTorus_torusToFrame hn]
  have hall : cellsOfSites F (Finset.univ : Finset (TorusSite n)) = torusCells F := by
    ext y
    refine ⟨fun _ => mem_torusCells_of_extent hside y, fun _ => ?_⟩
    exact (mem_sitesOfTorus hn Finset.univ y).2 (Finset.mem_univ _)
  refine ⟨?_, ?_, enclosingCell_torusToFrame hn ht, fun r X => sitesOfTorus_thickening hn r X,
    fun r X => sitesOfTorus_thickening ht r X, fun X => cutBonds_sitesOfTorus hn X,
    fun X => cutBonds_sitesOfTorus ht X, hall, levelSites_eq_sitesOfTorus hn,
    levelSites_eq_sitesOfTorus ht, ?_, ?_⟩
  · intro S
    ext y
    rw [mem_sitesOfTorus ht]
    simp only [sitesInBlocks, Finset.mem_filter, Finset.mem_univ, true_and, cutBelow, Finset.mem_biUnion]
    rw [← hcell]
    constructor
    · intro hy
      exact ⟨enclosingCell y, (mem_sitesOfTorus hn S _).2 hy, (mem_sitesBelow_iff hodd y _).2 rfl⟩
    · rintro ⟨c, hc, hy⟩
      rw [(mem_sitesBelow_iff hodd y c).1 hy]
      exact (mem_sitesOfTorus hn S c).1 hc
  · intro y z
    unfold cellSupDist TorusFields.supDist
    congr 1
    funext i
    show (((torusToFrame F F.top y) i - (torusToFrame F F.top z) i).valMinAbs).natAbs = _
    rw [show (torusToFrame F F.top y) i - (torusToFrame F F.top z) i = (torusToFrame F F.top (y - z)) i by
      rw [torusToFrame_sub hn]; rfl, valMinAbs_torusToFrame hn]
    rfl
  · intro s V
    have hcurv : ∀ (x : TorusSite n) (μ ν : Fin 4),
        plaquetteDefect (readAtLevel F F.top V) (torusToFrame F F.top x, μ, ν) = curvature V x μ ν := by
      intro x μ ν
      unfold plaquetteDefect curvature
      rw [plaquetteHolonomy_readAtLevel hn]
    have hpl : ∀ p : F.Site F.top × Fin 4 × Fin 4,
        p ∈ innerPlaquettes (torusCells F) F.top ↔ p.2.1 < p.2.2 := by
      intro p
      simp only [innerPlaquettes, sitesOfCells_top, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
        and_true]
      constructor
      · exact fun h => h.2.1
      · exact fun h => ⟨mem_torusCells_of_extent hside _, h, fun z _ => mem_torusCells_of_extent hside z⟩
    constructor
    · intro hc x μ ν hμν
      rw [← hcurv]
      exact hc _ ((hpl _).2 hμν)
    · rintro hc ⟨y, μ, ν⟩ hp
      have := hc (frameToTorus n y) μ ν ((hpl _).1 hp)
      rwa [← hcurv, torusToFrame_frameToTorus hn] at this
  · intro ℓ hℓ hdvd
    have hE : ∀ k, (stepBlockFrame ℓ.side (n / ℓ.side)).period 0 k = F.period F.top k := by
      intro k
      rw [hn]
      simp only [BlockFrame.period, stepBlockFrame, BlockFrame.top, Nat.sub_zero, zero_add, pow_one]
      rw [hℓ]
      exact Nat.div_mul_cancel hdvd
    have hat : ∀ x' : (stepBlockFrame ℓ.side (n / ℓ.side)).Site 0,
        torusToFrame F F.top (toTorusSite n x') = transferSite F F.top x' := by
      intro x'
      funext k
      exact cast_intCast_of_eq (hn k).symm _
    have hset : ∀ l : Finset ((stepBlockFrame ℓ.side (n / ℓ.side)).Site 0),
        cellsOfSites F (l.image (toTorusSite n)) = transferSet F F.top l := by
      intro l
      have : cellsOfSites F (l.image (toTorusSite n)) =
          (l.image (toTorusSite n)).image (torusToFrame F F.top) := rfl
      rw [this, Finset.image_image]
      exact Finset.image_congr fun x _ => hat x
    have hinj : Function.Injective (cellsOfSites F : Finset (TorusSite n) → Finset F.Cell) :=
      Finset.image_injective (torusToFrame_injective hn)
    refine ⟨fun l => ⟨?_, ?_⟩, fun S₀ V => ?_⟩
    · rintro ⟨x, rfl⟩
      refine ⟨transferSite F F.top x, ?_⟩
      rw [hset, lumpOf_transferSite hE]
    · rintro ⟨y, hy⟩
      refine ⟨transferSite (stepBlockFrame ℓ.side (n / ℓ.side)) 0 y, hinj ?_⟩
      rw [hy, hset, ← lumpOf_transferSite hE, transferSite_symm hE]
    · have hA : cellsOfSites F S₀ = transferSet F F.top
          (S₀.image (torusSiteInFrame (stepBlockFrame ℓ.side (n / ℓ.side)) 0)) := by
        unfold transferSet cellsOfSites
        rw [Finset.image_image]
        refine Finset.image_congr fun x _ => ?_
        exact (transferSite_siteOfCoords hE _).symm
      have hB : readAtLevel F F.top V =
          transferField F F.top (readAtLevel (stepBlockFrame ℓ.side (n / ℓ.side)) 0 V) :=
        (transferField_readAtLevel hE V).symm
      rw [hA, hB, hotLumps_transfer hE]
      unfold topHotLumps transferLumps
      rw [Finset.image_image]
      exact Finset.image_congr fun l _ => (hset l).symm
end TorusFrames
end YangMills.Construction
end
