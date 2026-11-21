import YangMills.Construction.HoleBesideASecondHole.CarriedSitesAndPaths
import YangMills.Construction.HoleBesideASecondHole.HotLumpsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusFrames
open BlockAverages FrameTransfer LumpContours TorusLumps TorusFields
namespace HotStepLumps
variable {F F' : BlockFrame} {j j' m : ℕ}
theorem mem_levelSites (hm : ∀ k, F.period j k = m) [NeZero m] (y : F.Site j) : y ∈ levelSites F j := by
  refine Finset.mem_image.2 ⟨siteCoords y, Fintype.mem_piFinset.2 fun k => Finset.mem_Icc.2 ?_,
    _root_.YangMills.Construction.FrameTransfer.siteOfCoords_siteCoords y⟩
  have : NeZero (F.period j k) := by rw [hm]; infer_instance
  have h1 : siteCoords y k = ((y k).val : ℤ) := by
    simp [siteCoords, ZMod.natCast_val]
  have h2 := ZMod.val_lt (y k)
  rw [h1]
  simp only [Pi.zero_apply]
  omega
theorem levelSites_eq_image (hm : ∀ k, F.period j k = m) [NeZero m] :
    levelSites F j = (Finset.univ : Finset (TorusSite m)).image (torusToFrame F j) := by
  ext y
  refine ⟨fun _ => ?_, fun _ => mem_levelSites hm y⟩
  exact Finset.mem_image.2 ⟨frameToTorus m y, Finset.mem_univ _, torusToFrame_frameToTorus hm y⟩
theorem toTorusSite_transferSite (h : ∀ i, F.period j i = F'.period j' i) (x : F.Site j) :
    toTorusSite m (transferSite F' j' x) = toTorusSite m x := by
  funext k
  unfold toTorusSite
  rw [siteCoords_transferSite h]
theorem toTorusSite_injective (hm : ∀ k, F.period j k = m) :
    Function.Injective (toTorusSite m : F.Site j → TorusSite m) :=
  Function.LeftInverse.injective (g := torusToFrame F j) (torusToFrame_frameToTorus hm)
end HotStepLumps
open HotStepLumps in
theorem hotLumpsOfStepStatement_holds : hotLumpsOfStepStatement := by
  intro ℓ n _
  have hL : 0 < ℓ.side := Nat.pos_of_ne_zero (NeZero.ne ℓ.side)
  have hE : ∀ k, (stepBlockFrame ℓ.side n).period 0 k = n * ℓ.side := by
    intro k
    simp [BlockFrame.period, stepBlockFrame, BlockFrame.top]
  have hper : ∀ k, (stepBlockFrame ℓ.side (n * ℓ.side / ℓ.side)).period 0 k =
      (stepBlockFrame ℓ.side n).period 0 k := by
    intro k
    simp only [BlockFrame.period, stepBlockFrame, BlockFrame.top]
    rw [Nat.mul_div_cancel _ hL]
  have hE' : ∀ k, (stepBlockFrame ℓ.side (n * ℓ.side / ℓ.side)).period 0 k = n * ℓ.side :=
    fun k => (hper k).trans (hE k)
  have hall : levelSites (stepBlockFrame ℓ.side n) 0 =
      transferSet (stepBlockFrame ℓ.side n) 0 (levelSites (stepBlockFrame ℓ.side (n * ℓ.side / ℓ.side)) 0) := by
    ext y
    refine ⟨fun _ => ?_, fun _ => mem_levelSites hE y⟩
    rw [mem_transferSet hper]
    exact mem_levelSites hE' _
  have key : ∀ W : TorusField (n * ℓ.side), StepCosts.stepHotLumps ℓ W = transferLumps (stepBlockFrame ℓ.side n) 0
      (hotLumps ℓ.grid ℓ.threshold (levelSites (stepBlockFrame ℓ.side (n * ℓ.side / ℓ.side)) 0)
        (readAtLevel (stepBlockFrame ℓ.side (n * ℓ.side / ℓ.side)) 0 W)) := by
    intro W
    rw [← hotLumps_transfer hper, ← hall, transferField_readAtLevel hper]
    rfl
  have h1 : ∀ W : TorusField (n * ℓ.side),
      torusHotLumps ℓ W = (StepCosts.stepHotLumps ℓ W).image (fun l => l.image (toTorusSite (n * ℓ.side))) := by
    intro W
    rw [key]
    unfold torusHotLumps transferLumps
    rw [Finset.image_image]
    refine Finset.image_congr fun l _ => ?_
    simp only [Function.comp, transferSet]
    rw [Finset.image_image]
    exact Finset.image_congr fun x _ => (toTorusSite_transferSite hper x).symm
  refine ⟨fun W => ⟨h1 W, ?_, ?_, ?_⟩, fun hd V => ?_⟩
  · unfold torusHotSites HoleOnTori.stepLumpSites
    rw [h1, Finset.image_biUnion]
    rfl
  · rw [h1]
    exact Finset.card_image_of_injective _ (Finset.image_injective (toTorusSite_injective hE))
  · have hb : sitesInBlocks ℓ.side (Finset.univ : Finset (TorusSite n)) = Finset.univ := by
      ext x
      simp [sitesInBlocks]
    unfold StepCosts.stepHotLumps HoleOnTori.stepHotLumps
    rw [hb, levelSites_eq_image hE]
    rfl
  · have hT : ∀ k, (stepBlockFrame ℓ.side (n / ℓ.side)).period 0 k = n := by
      intro k
      simp only [BlockFrame.period, stepBlockFrame, BlockFrame.top, Nat.sub_zero, zero_add, pow_one]
      exact Nat.div_mul_cancel hd
    unfold torusHotLumps HoleOnTori.topHotLumps
    rw [levelSites_eq_image hT]
    rfl
end YangMills.Construction.TorusFrames
end
