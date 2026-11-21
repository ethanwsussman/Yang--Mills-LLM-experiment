import YangMills.Construction.ClusterExpansionOfAStep.OffsetsOfABlock
import YangMills.Construction.ClusterExpansionOfAStep.TopFieldOffTheHull
import YangMills.Construction.HoleBesideASecondHole.HolesOffTheSpotsProof
import YangMills.Construction.HoleBesideASecondHole.OneTorusAtTwoFrames
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.FrameTransfer
open YangMills.Construction.BlockAverages YangMills.Construction.LumpContours
section Casts
variable {m m' : ℕ}
theorem intCast_cast_of_eq (h : m = m') (y : ZMod m) :
    ((((y.cast : ℤ) : ZMod m')).cast : ℤ) = y.cast := by apply _root_.YangMills.Construction.FrameTorusAction.cast_intCast_cast <;> assumption
theorem cast_intCast_of_eq (h : m = m') (z : ℤ) : ((((z : ZMod m)).cast : ℤ) : ZMod m') = (z : ZMod m') := by apply _root_.YangMills.Construction.FrameTorusAction.intCast_cast_intCast <;> assumption
theorem cast_add_of_eq (h : m = m') (a b : ZMod m) :
    (((a + b : ZMod m).cast : ℤ) : ZMod m') = ((a.cast : ℤ) : ZMod m') + ((b.cast : ℤ) : ZMod m') := by apply _root_.YangMills.Construction.FrameTorusAction.intCast_cast_add <;> assumption
theorem cast_neg_of_eq (h : m = m') (a : ZMod m) :
    (((- a : ZMod m).cast : ℤ) : ZMod m') = - ((a.cast : ℤ) : ZMod m') := by apply _root_.YangMills.Construction.FrameTorusAction.intCast_cast_neg <;> assumption
theorem cast_sub_of_eq (h : m = m') (a b : ZMod m) :
    (((a - b : ZMod m).cast : ℤ) : ZMod m') = ((a.cast : ℤ) : ZMod m') - ((b.cast : ℤ) : ZMod m') := by
  subst h
  simp
theorem cast_inj_of_eq (h : m = m') (a b : ZMod m) :
    ((a.cast : ℤ) : ZMod m') = ((b.cast : ℤ) : ZMod m') ↔ a = b := by
  subst h
  simp
theorem valMinAbs_cast_of_eq (h : m = m') (a : ZMod m) :
    (((a.cast : ℤ)) : ZMod m').valMinAbs = a.valMinAbs := by apply _root_.YangMills.Construction.TopLevelSites.valMinAbs_intCast_cast <;> assumption
end Casts
section OneLevel
variable {F F' : BlockFrame} {j j' : ℕ}
theorem siteOfCoords_siteCoords (x : F.Site j) : (siteOfCoords j (siteCoords x) : F.Site j) = x := by apply _root_.YangMills.Construction.BlockAverages.siteOfCoords_siteCoords <;> assumption
theorem siteCoords_transferSite (h : ∀ i, F.period j i = F'.period j' i) (x : F.Site j) :
    siteCoords (transferSite F' j' x) = siteCoords x := by
  funext i
  exact intCast_cast_of_eq (h i) (x i)
theorem transferSite_transferSite (h : ∀ i, F.period j i = F'.period j' i) (x : F.Site j) :
    transferSite F j (transferSite F' j' x) = x := by
  unfold transferSite
  have := siteCoords_transferSite h x
  unfold transferSite at this
  rw [this]
  exact siteOfCoords_siteCoords x
theorem transferSite_symm (h : ∀ i, F.period j i = F'.period j' i) (y : F'.Site j') :
    transferSite F' j' (transferSite F j y) = y :=
  transferSite_transferSite (fun i => (h i).symm) y
theorem transferSite_injective (h : ∀ i, F.period j i = F'.period j' i) :
    Function.Injective (transferSite F' j' : F.Site j → F'.Site j') :=
  Function.LeftInverse.injective (transferSite_transferSite h)
theorem transferSite_siteOfCoords (h : ∀ i, F.period j i = F'.period j' i) (z : Fin 4 → ℤ) :
    transferSite F' j' (siteOfCoords j z : F.Site j) = siteOfCoords j' z := by
  funext i
  exact cast_intCast_of_eq (h i) (z i)
theorem transferSite_add (h : ∀ i, F.period j i = F'.period j' i) (x y : F.Site j) :
    transferSite F' j' (x + y) = transferSite F' j' x + transferSite F' j' y := by
  funext i
  exact cast_add_of_eq (h i) (x i) (y i)
theorem transferSite_neg (h : ∀ i, F.period j i = F'.period j' i) (x : F.Site j) :
    transferSite F' j' (- x) = - transferSite F' j' x := by
  funext i
  exact cast_neg_of_eq (h i) (x i)
theorem transferSite_sub (h : ∀ i, F.period j i = F'.period j' i) (x y : F.Site j) :
    transferSite F' j' (x - y) = transferSite F' j' x - transferSite F' j' y := by
  funext i
  exact cast_sub_of_eq (h i) (x i) (y i)
theorem transferSite_unitStep (h : ∀ i, F.period j i = F'.period j' i) (i : Fin 4) :
    transferSite F' j' (unitStep j i : F.Site j) = unitStep j' i :=
  transferSite_siteOfCoords h _
theorem transferSite_stepDisplacement (h : ∀ i, F.period j i = F'.period j' i) (st : PathStep) :
    transferSite F' j' (stepDisplacement j st : F.Site j) = stepDisplacement j' st := by
  unfold stepDisplacement
  split_ifs
  · exact transferSite_unitStep h _
  · rw [transferSite_neg h, transferSite_unitStep h]
theorem transferSite_apply_inj (h : ∀ i, F.period j i = F'.period j' i) (x y : F.Site j) (i : Fin 4) :
    transferSite F' j' x i = transferSite F' j' y i ↔ x i = y i :=
  cast_inj_of_eq (h i) (x i) (y i)
theorem valMinAbs_transferSite (h : ∀ i, F.period j i = F'.period j' i) (x : F.Site j) (i : Fin 4) :
    (transferSite F' j' x i).valMinAbs = (x i).valMinAbs :=
  valMinAbs_cast_of_eq (h i) (x i)
theorem supDist_transferSite (h : ∀ i, F.period j i = F'.period j' i) (x y : F.Site j) :
    supDist (transferSite F' j' x) (transferSite F' j' y) = supDist x y := by
  unfold supDist
  congr 1
  funext i
  rw [show transferSite F' j' x i - transferSite F' j' y i = (transferSite F' j' x - transferSite F' j' y) i from rfl,
    ← transferSite_sub h, show (x i - y i) = (x - y) i from rfl, valMinAbs_transferSite h]
theorem minimalOffset_transferSite (h : ∀ i, F.period j i = F'.period j' i) (x y : F.Site j) :
    minimalOffset (transferSite F' j' x) (transferSite F' j' y) = minimalOffset x y := by
  funext i
  unfold minimalOffset
  rw [← transferSite_sub h, valMinAbs_transferSite h]
theorem mem_transferSet (h : ∀ i, F.period j i = F'.period j' i) (X : Finset (F.Site j)) (y : F'.Site j') :
    y ∈ transferSet F' j' X ↔ transferSite F j y ∈ X := by
  unfold transferSet
  rw [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rwa [transferSite_transferSite h]
  · intro hy
    exact ⟨_, hy, transferSite_symm h y⟩
theorem transferSite_mem_transferSet (h : ∀ i, F.period j i = F'.period j' i) (X : Finset (F.Site j))
    (x : F.Site j) : transferSite F' j' x ∈ transferSet F' j' X ↔ x ∈ X := by
  rw [mem_transferSet h, transferSite_transferSite h]
theorem transferSet_transferSet (h : ∀ i, F.period j i = F'.period j' i) (X : Finset (F.Site j)) :
    transferSet F j (transferSet F' j' X) = X := by
  ext x
  rw [mem_transferSet (fun i => (h i).symm), transferSite_mem_transferSet h]
theorem transferSet_injective (h : ∀ i, F.period j i = F'.period j' i) :
    Function.Injective (transferSet F' j' : Finset (F.Site j) → Finset (F'.Site j')) :=
  Function.LeftInverse.injective (transferSet_transferSet h)
theorem transferSet_subset_iff (h : ∀ i, F.period j i = F'.period j' i) (X Y : Finset (F.Site j)) :
    transferSet F' j' X ⊆ transferSet F' j' Y ↔ X ⊆ Y := by
  constructor
  · intro hs x hx
    exact (transferSite_mem_transferSet h Y x).1 (hs ((transferSite_mem_transferSet h X x).2 hx))
  · intro hs y hy
    rw [mem_transferSet h] at hy ⊢
    exact hs hy
theorem mem_transferLumps (h : ∀ i, F.period j i = F'.period j' i) (H : Finset (Finset (F.Site j)))
    (l : Finset (F'.Site j')) : l ∈ transferLumps F' j' H ↔ transferSet F j l ∈ H := by
  unfold transferLumps
  rw [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rwa [transferSet_transferSet h]
  · intro hl
    exact ⟨_, hl, transferSet_transferSet (fun i => (h i).symm) l⟩
theorem transferSet_mem_transferLumps (h : ∀ i, F.period j i = F'.period j' i)
    (H : Finset (Finset (F.Site j))) (l : Finset (F.Site j)) :
    transferSet F' j' l ∈ transferLumps F' j' H ↔ l ∈ H := by
  rw [mem_transferLumps h, transferSet_transferSet h]
theorem transferLumps_transferLumps (h : ∀ i, F.period j i = F'.period j' i)
    (H : Finset (Finset (F.Site j))) : transferLumps F j (transferLumps F' j' H) = H := by
  ext l
  rw [mem_transferLumps (fun i => (h i).symm), transferSet_mem_transferLumps h]
theorem card_transferLumps (h : ∀ i, F.period j i = F'.period j' i) (H : Finset (Finset (F.Site j))) :
    (transferLumps F' j' H).card = H.card :=
  Finset.card_image_of_injective _ (transferSet_injective h)
theorem transferField_apply (h : ∀ i, F.period j i = F'.period j' i) (X : F.GaugeField j) (x : F.Site j)
    (i : Fin 4) : transferField F' j' X (transferSite F' j' x) i = X x i := by
  unfold transferField
  rw [transferSite_transferSite h]
theorem transferField_transferField (h : ∀ i, F.period j i = F'.period j' i) (X : F.GaugeField j) :
    transferField F j (transferField F' j' X) = X := by
  funext x i
  unfold transferField
  rw [transferSite_transferSite h]
theorem transferField_readAtLevel (h : ∀ i, F.period j i = F'.period j' i) {m : ℕ}
    (W : TorusFields.TorusField m) :
    transferField F' j' (TorusFields.readAtLevel F j W) = TorusFields.readAtLevel F' j' W := by
  funext x i
  unfold transferField TorusFields.readAtLevel
  rw [siteCoords_transferSite fun i => (h i).symm]
theorem linkValue_transfer (h : ∀ i, F.period j i = F'.period j' i) (X : F.GaugeField j) (x : F.Site j)
    (st : PathStep) : linkValue (transferField F' j' X) (transferSite F' j' x) st = linkValue X x st := by
  unfold linkValue
  split_ifs
  · exact transferField_apply h X x _
  · rw [← transferSite_unitStep h, ← transferSite_sub h, transferField_apply h]
theorem pathHolonomy_transfer (h : ∀ i, F.period j i = F'.period j' i) (X : F.GaugeField j) (x : F.Site j)
    (l : List PathStep) :
    pathHolonomy (transferField F' j' X) (transferSite F' j' x) l = pathHolonomy X x l := by
  induction l generalizing x with
  | nil => rfl
  | cons st r ih =>
    simp only [pathHolonomy]
    rw [linkValue_transfer h, ← transferSite_stepDisplacement h, ← transferSite_add h, ih]
theorem plaquetteHolonomy_transfer (h : ∀ i, F.period j i = F'.period j' i) (X : F.GaugeField j)
    (p : F.Site j × Fin 4 × Fin 4) :
    plaquetteHolonomy (transferField F' j' X) (transferSite F' j' p.1, p.2) = plaquetteHolonomy X p :=
  pathHolonomy_transfer h X p.1 _
theorem plaquetteDefect_transfer (h : ∀ i, F.period j i = F'.period j' i) (X : F.GaugeField j)
    (p : F.Site j × Fin 4 × Fin 4) :
    plaquetteDefect (transferField F' j' X) (transferSite F' j' p.1, p.2) = plaquetteDefect X p := by
  unfold plaquetteDefect
  rw [plaquetteHolonomy_transfer h]
theorem plaquetteCorners_transfer (h : ∀ i, F.period j i = F'.period j' i) (p : F.Site j × Fin 4 × Fin 4) :
    plaquetteCorners ((transferSite F' j' p.1, p.2) : F'.Site j' × Fin 4 × Fin 4) =
      transferSet F' j' (plaquetteCorners p) := by
  simp only [plaquetteCorners, transferSet, Finset.image_insert, Finset.image_singleton, transferSite_add h,
    transferSite_unitStep h]
theorem mem_cutPlaquettes_iff (X : Finset (F.Site j)) (p : F.Site j × Fin 4 × Fin 4) :
    p ∈ cutPlaquettes X ↔ p.1 ∈ X ∧ p.2.1 < p.2.2 ∧ plaquetteCorners p ⊆ X := by apply _root_.YangMills.Construction.HoleFilling.AwayFromBadCells.mem_cutPlaquettes <;> assumption
theorem transfer_mem_cutPlaquettes (h : ∀ i, F.period j i = F'.period j' i) (X : Finset (F.Site j))
    (p : F.Site j × Fin 4 × Fin 4) :
    ((transferSite F' j' p.1, p.2) : F'.Site j' × Fin 4 × Fin 4) ∈ cutPlaquettes (transferSet F' j' X) ↔
      p ∈ cutPlaquettes X := by
  rw [mem_cutPlaquettes_iff, mem_cutPlaquettes_iff, plaquetteCorners_transfer h, transferSet_subset_iff h,
    transferSite_mem_transferSet h]
theorem cutPlaquettes_transferSet (h : ∀ i, F.period j i = F'.period j' i) (X : Finset (F.Site j)) :
    cutPlaquettes (transferSet F' j' X) =
      (cutPlaquettes X).image fun p => (transferSite F' j' p.1, p.2) := by
  ext q
  rw [Finset.mem_image]
  constructor
  · intro hq
    refine ⟨(transferSite F j q.1, q.2), ?_, ?_⟩
    · rw [← transfer_mem_cutPlaquettes h]
      simpa only [transferSite_symm h] using hq
    · simp only [transferSite_symm h]
  · rintro ⟨p, hp, rfl⟩
    exact (transfer_mem_cutPlaquettes h X p).2 hp
theorem mem_cutBonds_iff (X : Finset (F.Site j)) (b : F.Site j × Fin 4) :
    b ∈ cutBonds X ↔ b.1 ∈ X ∧ b.1 + unitStep j b.2 ∈ X := by
  simp [cutBonds]
theorem transferBond_mem_cutBonds (h : ∀ i, F.period j i = F'.period j' i) (X : Finset (F.Site j))
    (b : F.Site j × Fin 4) : transferBond F' j' b ∈ cutBonds (transferSet F' j' X) ↔ b ∈ cutBonds X := by
  rw [mem_cutBonds_iff, mem_cutBonds_iff]
  simp only [transferBond]
  rw [← transferSite_unitStep h, ← transferSite_add h, transferSite_mem_transferSet h,
    transferSite_mem_transferSet h]
theorem transferBond_symm (h : ∀ i, F.period j i = F'.period j' i) (b : F'.Site j' × Fin 4) :
    transferBond F' j' (transferBond F j b) = b := by
  simp only [transferBond, transferSite_symm h]
theorem transferBond_injective (h : ∀ i, F.period j i = F'.period j' i) :
    Function.Injective (transferBond F' j' : F.Site j × Fin 4 → F'.Site j' × Fin 4) :=
  Function.LeftInverse.injective (transferBond_symm fun i => (h i).symm)
theorem cutBonds_transferSet (h : ∀ i, F.period j i = F'.period j' i) (X : Finset (F.Site j)) :
    cutBonds (transferSet F' j' X) = (cutBonds X).image (transferBond F' j') := by
  ext q
  rw [Finset.mem_image]
  constructor
  · intro hq
    refine ⟨transferBond F j q, ?_, transferBond_symm h q⟩
    rw [← transferBond_mem_cutBonds h, transferBond_symm h]
    exact hq
  · rintro ⟨p, hp, rfl⟩
    exact (transferBond_mem_cutBonds h X p).2 hp
theorem boxSites_transfer (h : ∀ i, F.period j i = F'.period j' i) (lo hi : Fin 4 → ℤ) :
    (boxSites j' lo hi : Finset (F'.Site j')) = transferSet F' j' (boxSites (F := F) j lo hi) := by
  unfold boxSites transferSet
  rw [Finset.image_image]
  refine Finset.image_congr fun z _ => ?_
  exact (transferSite_siteOfCoords h z).symm
theorem lumpOf_transferSite (h : ∀ i, F.period j i = F'.period j' i) {L : ℕ} (g : LumpGrid L)
    (x : F.Site j) : lumpOf g (transferSite F' j' x) = transferSet F' j' (lumpOf g x) := by
  unfold lumpOf
  rw [siteCoords_transferSite h]
  exact boxSites_transfer h _ _
theorem thicken_transferSet (h : ∀ i, F.period j i = F'.period j' i) (m : ℕ) (X : Finset (F.Site j)) :
    thicken m (transferSet F' j' X) = transferSet F' j' (thicken m X) := by
  ext y
  simp only [thicken, transferSet, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, e, he, rfl⟩
    refine ⟨x + siteOfCoords j e, ⟨x, hx, e, he, rfl⟩, ?_⟩
    rw [transferSite_add h, transferSite_siteOfCoords h]
  · rintro ⟨_, ⟨x, hx, e, he, rfl⟩, rfl⟩
    refine ⟨_, ⟨x, hx, rfl⟩, e, he, ?_⟩
    rw [transferSite_add h, transferSite_siteOfCoords h]
theorem lumpsNeighbourhood_transferLumps (h : ∀ i, F.period j i = F'.period j' i)
    (H : Finset (Finset (F.Site j))) :
    lumpsNeighbourhood (transferLumps F' j' H) = transferSet F' j' (lumpsNeighbourhood H) := by
  ext y
  simp only [lumpsNeighbourhood, lumpNeighbourhood, transferLumps, Finset.mem_biUnion, Finset.mem_image,
    mem_transferSet h]
  constructor
  · rintro ⟨_, ⟨l, hl, rfl⟩, hy⟩
    refine ⟨l, hl, ?_⟩
    rw [thicken_transferSet h, mem_transferSet h] at hy
    exact hy
  · rintro ⟨l, hl, hy⟩
    refine ⟨_, ⟨l, hl, rfl⟩, ?_⟩
    rw [thicken_transferSet h, mem_transferSet h]
    exact hy
theorem isLump_transferSet (h : ∀ i, F.period j i = F'.period j' i) {L : ℕ} (g : LumpGrid L)
    (l : Finset (F.Site j)) : IsLump g (transferSet F' j' l) ↔ IsLump g l := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨transferSite F j y, transferSet_injective h ?_⟩
    rw [hy, ← lumpOf_transferSite h, transferSite_symm h]
  · rintro ⟨x, rfl⟩
    exact ⟨transferSite F' j' x, (lumpOf_transferSite h g x).symm⟩
open Classical in
theorem hotLumps_transfer (h : ∀ i, F.period j i = F'.period j' i) {L : ℕ} (g : LumpGrid L) (s : ℝ)
    (X : Finset (F.Site j)) (W : F.GaugeField j) :
    hotLumps g s (transferSet F' j' X) (transferField F' j' W) = transferLumps F' j' (hotLumps g s X W) := by
  ext l
  rw [mem_transferLumps h]
  simp only [hotLumps, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨q, ⟨hq, hs⟩, z, hz, rfl⟩
    have e : q = ((transferSite F' j' (transferSite F j q.1), q.2) : F'.Site j' × Fin 4 × Fin 4) := by
      rw [transferSite_symm h]
    refine ⟨(transferSite F j q.1, q.2), ⟨?_, ?_⟩, transferSite F j z, ?_, ?_⟩
    · rw [← transfer_mem_cutPlaquettes h, ← e]
      exact hq
    · rw [← plaquetteDefect_transfer h W, ← e]
      exact hs
    · rw [plaquetteCorners_transfer (fun i => (h i).symm) q, transferSite_mem_transferSet fun i => (h i).symm]
      exact hz
    · rw [← transferSet_transferSet (F' := F') (j' := j') h (lumpOf g (transferSite F j z)),
        ← lumpOf_transferSite h, transferSite_symm h]
  · rintro ⟨p, ⟨hp, hs⟩, z, hz, hl⟩
    refine ⟨(transferSite F' j' p.1, p.2), ⟨(transfer_mem_cutPlaquettes h X p).2 hp, ?_⟩,
      transferSite F' j' z, ?_, ?_⟩
    · rw [plaquetteDefect_transfer h W]
      exact hs
    · rw [plaquetteCorners_transfer h, transferSite_mem_transferSet h]
      exact hz
    · rw [lumpOf_transferSite h, hl, transferSet_transferSet (fun i => (h i).symm)]
end OneLevel
section TwoLevels
variable {F F' : BlockFrame} {i j i' j' : ℕ}
theorem sitesBelow_transferSite (hL : F.blockSide = F'.blockSide) (hi : ∀ k, F.period i k = F'.period i' k)
    (hj : ∀ k, F.period j k = F'.period j' k) (hd : j - i = j' - i') (x : F.Site j) :
    sitesBelow i' (transferSite F' j' x) = transferSet F' i' (sitesBelow i x) := by
  unfold sitesBelow transferSet
  rw [Finset.image_image, siteCoords_transferSite hj, ← hL, ← hd]
  refine Finset.image_congr fun z _ => ?_
  exact (transferSite_siteOfCoords hi _).symm
theorem cutBelow_transferSet (hL : F.blockSide = F'.blockSide) (hi : ∀ k, F.period i k = F'.period i' k)
    (hj : ∀ k, F.period j k = F'.period j' k) (hd : j - i = j' - i') (X : Finset (F.Site j)) :
    cutBelow i' (transferSet F' j' X) = transferSet F' i' (cutBelow i X) := by
  ext y
  simp only [cutBelow, Finset.mem_biUnion, mem_transferSet hi]
  constructor
  · rintro ⟨x', hx', hy⟩
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hx'
    refine ⟨x, hx, ?_⟩
    rw [sitesBelow_transferSite hL hi hj hd, mem_transferSet hi] at hy
    exact hy
  · rintro ⟨x, hx, hy⟩
    refine ⟨transferSite F' j' x, Finset.mem_image_of_mem _ hx, ?_⟩
    rw [sitesBelow_transferSite hL hi hj hd, mem_transferSet hi]
    exact hy
theorem refineSite_transferSite (hL : F.blockSide = F'.blockSide) (hi : ∀ k, F.period i k = F'.period i' k)
    (hj : ∀ k, F.period (i + 1) k = F'.period (i' + 1) k) (y : F.Site (i + 1)) :
    refineSite (transferSite F' (i' + 1) y) = transferSite F' i' (refineSite y) := by
  unfold refineSite
  rw [siteCoords_transferSite hj, transferSite_siteOfCoords hi, ← hL]
theorem contourAverage_transfer (hL : F.blockSide = F'.blockSide) (hi : ∀ k, F.period i k = F'.period i' k)
    (hj : ∀ k, F.period (i + 1) k = F'.period (i' + 1) k) (X : F.GaugeField i)
    (c : F.Site (i + 1) × Fin 4) :
    contourAverage (transferField F' i' X) (transferBond F' (i' + 1) c) = contourAverage X c := by
  unfold contourAverage
  simp only [transferBond]
  rw [refineSite_transferSite hL hi hj, ← hL]
  simp only [pathHolonomy_transfer hi]
theorem blockFit_transfer (hL : F.blockSide = F'.blockSide) (hi : ∀ k, F.period i k = F'.period i' k)
    (hj : ∀ k, F.period (i + 1) k = F'.period (i' + 1) k) (X : F.GaugeField i) (X' : F.GaugeField (i + 1))
    (c : F.Site (i + 1) × Fin 4) :
    blockFit (transferField F' i' X) (transferField F' (i' + 1) X') (transferBond F' (i' + 1) c) =
      blockFit X X' c := by
  unfold blockFit
  rw [contourAverage_transfer hL hi hj]
  simp only [transferBond]
  rw [transferField_apply hj]
end TwoLevels
section Torus
variable {F : BlockFrame} {j m : ℕ}
def torusToFrame (F : BlockFrame) (j : ℕ) {m : ℕ} (x : TorusFields.TorusSite m) : F.Site j :=
  siteOfCoords j fun i => ((x i).cast : ℤ)
def frameToTorus (m : ℕ) (x : F.Site j) : TorusFields.TorusSite m := fun k => ((siteCoords x k : ℤ) : ZMod m)
theorem frameToTorus_torusToFrame (hm : ∀ k, F.period j k = m) (x : TorusFields.TorusSite m) :
    frameToTorus m (torusToFrame F j x) = x := by
  funext k
  have := cast_intCast_of_eq (hm k) ((x k).cast : ℤ)
  simpa [frameToTorus, torusToFrame, siteCoords, siteOfCoords] using this
theorem torusToFrame_frameToTorus (hm : ∀ k, F.period j k = m) (y : F.Site j) :
    torusToFrame F j (frameToTorus m y) = y := by
  funext k
  have := cast_intCast_of_eq (hm k).symm (siteCoords y k)
  simpa [frameToTorus, torusToFrame, siteCoords, siteOfCoords] using this
theorem torusToFrame_injective (hm : ∀ k, F.period j k = m) :
    Function.Injective (torusToFrame F j : TorusFields.TorusSite m → F.Site j) :=
  Function.LeftInverse.injective (frameToTorus_torusToFrame hm)
theorem torusToFrame_add (hm : ∀ k, F.period j k = m) (x y : TorusFields.TorusSite m) :
    torusToFrame F j (x + y) = torusToFrame F j x + torusToFrame F j y := by
  funext k
  exact cast_add_of_eq (hm k).symm (x k) (y k)
theorem torusToFrame_siteOfInt (hm : ∀ k, F.period j k = m) (z : Fin 4 → ℤ) :
    torusToFrame F j (TorusFields.siteOfInt z : TorusFields.TorusSite m) = siteOfCoords j z := by
  funext k
  exact cast_intCast_of_eq (hm k).symm (z k)
theorem torusUnitStep_eq_siteOfInt (i : Fin 4) :
    TorusFields.unitStep m i = TorusFields.siteOfInt (Pi.single i 1) := by apply _root_.YangMills.Construction.BlockOffsets.unitStep_eq_siteOfInt <;> assumption
theorem torusToFrame_unitStep (hm : ∀ k, F.period j k = m) (i : Fin 4) :
    torusToFrame F j (TorusFields.unitStep m i) = unitStep j i := by
  rw [torusUnitStep_eq_siteOfInt, torusToFrame_siteOfInt hm]
  rfl
theorem readAtLevel_torusToFrame (hm : ∀ k, F.period j k = m) (W : TorusFields.TorusField m)
    (x : TorusFields.TorusSite m) (i : Fin 4) :
    TorusFields.readAtLevel F j W (torusToFrame F j x) i = W x i := by
  show W (frameToTorus m (torusToFrame F j x)) i = W x i
  rw [frameToTorus_torusToFrame hm]
theorem sitesOfTorus_eq_image (X : Finset (TorusFields.TorusSite m)) :
    sitesOfTorus F j X = X.image (torusToFrame F j) := rfl
theorem torusToFrame_mem_sitesOfTorus (hm : ∀ k, F.period j k = m) (X : Finset (TorusFields.TorusSite m))
    (x : TorusFields.TorusSite m) : torusToFrame F j x ∈ sitesOfTorus F j X ↔ x ∈ X := by
  rw [sitesOfTorus_eq_image]
  exact (torusToFrame_injective hm).mem_finset_image
theorem mem_sitesOfTorus (hm : ∀ k, F.period j k = m) (X : Finset (TorusFields.TorusSite m)) (y : F.Site j) :
    y ∈ sitesOfTorus F j X ↔ frameToTorus m y ∈ X := by
  rw [← torusToFrame_mem_sitesOfTorus hm, torusToFrame_frameToTorus hm]
theorem plaquetteHolonomy_readAtLevel (hm : ∀ k, F.period j k = m) (W : TorusFields.TorusField m)
    (x : TorusFields.TorusSite m) (μ ν : Fin 4) :
    plaquetteHolonomy (TorusFields.readAtLevel F j W) (torusToFrame F j x, μ, ν) = TorusFields.holonomy W x μ ν := by
  have e2 : torusToFrame F j x + unitStep j μ + unitStep j ν + - unitStep j μ - unitStep j ν =
      torusToFrame F j x := by
    abel
  have e3 : torusToFrame F j x + unitStep j μ + unitStep j ν - unitStep j μ =
      torusToFrame F j (x + TorusFields.unitStep m ν) := by
    rw [torusToFrame_add hm, torusToFrame_unitStep hm]
    abel
  have e4 : torusToFrame F j x + unitStep j μ = torusToFrame F j (x + TorusFields.unitStep m μ) := by
    rw [torusToFrame_add hm, torusToFrame_unitStep hm]
  simp only [plaquetteHolonomy, pathHolonomy, linkValue, stepDisplacement, if_true, Bool.false_eq_true,
    if_false, mul_one]
  rw [e2, e3, e4, readAtLevel_torusToFrame hm, readAtLevel_torusToFrame hm, readAtLevel_torusToFrame hm,
    readAtLevel_torusToFrame hm]
  simp only [TorusFields.holonomy, mul_assoc]
theorem torusToFrame_mem_cutPlaquettes [NeZero m] (hm : ∀ k, F.period j k = m)
    (X : Finset (TorusFields.TorusSite m)) (x : TorusFields.TorusSite m) (μ ν : Fin 4) :
    ((torusToFrame F j x, μ, ν) : F.Site j × Fin 4 × Fin 4) ∈ cutPlaquettes (sitesOfTorus F j X) ↔
      ((x, μ, ν) : TorusFields.TorusPlaquette m) ∈ TorusFields.plaquettesIn X := by
  have e1 : torusToFrame F j x + unitStep j μ = torusToFrame F j (x + TorusFields.unitStep m μ) := by
    rw [torusToFrame_add hm, torusToFrame_unitStep hm]
  have e2 : torusToFrame F j x + unitStep j ν = torusToFrame F j (x + TorusFields.unitStep m ν) := by
    rw [torusToFrame_add hm, torusToFrame_unitStep hm]
  have e3 : torusToFrame F j x + unitStep j μ + unitStep j ν =
      torusToFrame F j (x + TorusFields.unitStep m μ + TorusFields.unitStep m ν) := by
    rw [torusToFrame_add hm, torusToFrame_add hm, torusToFrame_unitStep hm, torusToFrame_unitStep hm]
  rw [mem_cutPlaquettes_iff]
  simp only [plaquetteCorners, Finset.insert_subset_iff, Finset.singleton_subset_iff, TorusFields.plaquettesIn,
    TorusFields.plaquetteVertices, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  rw [e3, e1, e2]
  simp only [torusToFrame_mem_sitesOfTorus hm]
  tauto
end Torus
end YangMills.Construction.FrameTransfer
end
