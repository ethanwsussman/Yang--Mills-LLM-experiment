import YangMills.Construction.HullsInEveryVolume.EachTowerHasARuleOfTheNoisesProof
import YangMills.Construction.ClusterExpansionOfAStep.TranslationsCarryTheKernelAtBasesProof
import YangMills.Construction.HullsInEveryVolume.TranslationsCarryTheBasesAtEverySide
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.HullTrees
open YangMills.Construction.BlockAverages YangMills.Construction.LumpContours
open YangMills.Construction.TorusContours YangMills.Construction.TorusLumps YangMills.Construction.TorusFields
namespace TranslationInvariance
section Cover
variable {F : BlockFrame} {j : ℕ} {e : F.Site j ≃ F.Site j}
theorem mergedBoxes_image (hbox : ∀ B : Finset (F.Site j), IsSmallBox F B → IsSmallBox F (B.image e))
    (hbox' : ∀ B : Finset (F.Site j), IsSmallBox F B → IsSmallBox F (B.image e.symm))
    (hd : ∀ x y : F.Site j, supDist (e x) (e y) = supDist x y) (seeds : Finset (Finset (F.Site j))) :
    mergedBoxes (seeds.image (Finset.image e)) = (mergedBoxes seeds).image (Finset.image e) := by apply _root_.YangMills.Construction.TranslationKernel.mergedBoxes_image <;> assumption
end Cover
section Moves
variable {F : BlockFrame} {j : ℕ}
theorem boxSites_image_addRight (lo hi k : Fin 4 → ℤ) :
    (boxSites j lo hi : Finset (F.Site j)).image (Equiv.addRight (siteOfCoords j k : F.Site j)) =
      boxSites j (lo + k) (hi + k) := by
  ext x
  simp only [boxSites, Finset.mem_image, Fintype.mem_piFinset, Finset.mem_Icc, Equiv.coe_addRight]
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨z + k, fun i => ?_, _root_.YangMills.Construction.TorusContours.siteOfCoords_add z k⟩
    have := hz i
    simp only [Pi.add_apply]
    constructor <;> linarith [this.1, this.2]
  · rintro ⟨z, hz, rfl⟩
    refine ⟨_, ⟨z - k, fun i => ?_, rfl⟩, ?_⟩
    · have := hz i
      simp only [Pi.add_apply, Pi.sub_apply] at this ⊢
      constructor <;> linarith [this.1, this.2]
    · rw [← _root_.YangMills.Construction.TorusContours.siteOfCoords_add]
      simp
theorem isSmallBox_image_addRight (k : Fin 4 → ℤ) {B : Finset (F.Site j)} (h : IsSmallBox F B) :
    IsSmallBox F (B.image (Equiv.addRight (siteOfCoords j k : F.Site j))) := by
  obtain ⟨lo, hi, h1, rfl⟩ := h
  refine ⟨lo + k, hi + k, fun i => ?_, boxSites_image_addRight lo hi k⟩
  have := h1 i
  simp only [Pi.add_apply]
  constructor <;> linarith [this.1, this.2]
theorem addRight_siteOfCoords_symm (k : Fin 4 → ℤ) :
    (Equiv.addRight (siteOfCoords j k : F.Site j)).symm =
      Equiv.addRight (siteOfCoords j (-k) : F.Site j) := by
  ext x : 1
  rw [_root_.YangMills.Construction.TorusContours.siteOfCoords_neg]
  simp
theorem supDist_add_right (u x y : F.Site j) : supDist (x + u) (y + u) = supDist x y := by
  simp [LumpContours.supDist]
theorem mergedBoxes_image_addRight (k : Fin 4 → ℤ) (seeds : Finset (Finset (F.Site j))) :
    mergedBoxes (seeds.image (Finset.image (Equiv.addRight (siteOfCoords j k : F.Site j)))) =
      (mergedBoxes seeds).image (Finset.image (Equiv.addRight (siteOfCoords j k : F.Site j))) := by
  refine mergedBoxes_image (fun B hB => isSmallBox_image_addRight k hB) (fun B hB => ?_)
    (fun x y => supDist_add_right _ x y) seeds
  rw [addRight_siteOfCoords_symm]
  exact isSmallBox_image_addRight (-k) hB
theorem mem_pathSites_add_right (u : F.Site j) (l : List PathStep) (x z : F.Site j) :
    z ∈ pathSites x l ↔ z + u ∈ pathSites (x + u) l := by
  induction l generalizing x with
  | nil => simp [pathSites]
  | cons st r ih =>
    simp only [pathSites, List.mem_cons, add_left_inj]
    rw [add_right_comm x u, ← ih]
theorem linkValue_translate {X X' : F.GaugeField j} {u : F.Site j} (h : ∀ x i, X' x i = X (x + u) i)
    (x : F.Site j) (st : PathStep) : linkValue X' x st = linkValue X (x + u) st := by
  obtain ⟨k, f⟩ := st
  cases f
  · simp only [linkValue, Bool.false_eq_true, if_false, h]
    rw [sub_add_eq_add_sub]
  · simp only [linkValue, if_true, h]
theorem pathHolonomy_translate {X X' : F.GaugeField j} {u : F.Site j} (h : ∀ x i, X' x i = X (x + u) i)
    (l : List PathStep) (x : F.Site j) : pathHolonomy X' x l = pathHolonomy X (x + u) l := by
  induction l generalizing x with
  | nil => rfl
  | cons st r ih =>
    simp only [pathHolonomy]
    rw [linkValue_translate h, ih, add_right_comm]
theorem plaquetteDefect_translate {X X' : F.GaugeField j} {u : F.Site j} (h : ∀ x i, X' x i = X (x + u) i)
    (x : F.Site j) (μ ν : Fin 4) : plaquetteDefect X' (x, μ, ν) = plaquetteDefect X (x + u, μ, ν) := by
  simp only [plaquetteDefect, plaquetteHolonomy]
  rw [pathHolonomy_translate h]
theorem plaquetteCorners_add_right (u x : F.Site j) (μ ν : Fin 4) :
    plaquetteCorners (x + u, μ, ν) = (plaquetteCorners (x, μ, ν)).image (Equiv.addRight u) := by
  ext z
  simp only [plaquetteCorners, Finset.mem_image, Finset.mem_insert, Finset.mem_singleton, Equiv.coe_addRight]
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨x, by simp, rfl⟩
    · exact ⟨x + BlockAverages.unitStep j μ, by simp, add_right_comm _ _ _⟩
    · exact ⟨x + BlockAverages.unitStep j ν, by simp, add_right_comm _ _ _⟩
    · refine ⟨x + BlockAverages.unitStep j μ + BlockAverages.unitStep j ν, by simp, ?_⟩
      abel
  · rintro ⟨a, (rfl | rfl | rfl | rfl), rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (add_right_comm _ _ _))
    · exact Or.inr (Or.inr (Or.inl (add_right_comm _ _ _)))
    · refine Or.inr (Or.inr (Or.inr ?_))
      abel
theorem offsetFromCentre_add_dvd {L : ℕ} (c K : ℤ) (hK : (L : ℤ) ∣ K) :
    offsetFromCentre L (c + K) = offsetFromCentre L c := by
  obtain ⟨t, rfl⟩ := hK
  unfold offsetFromCentre
  have : (c + (L : ℤ) * t + ((L : ℤ) - 1) / 2) = (c + ((L : ℤ) - 1) / 2) + (L : ℤ) * t := by ring
  rw [this, Int.add_mul_emod_self_left]
end Moves
section Lumps
variable {F : BlockFrame} [∀ j i, NeZero (F.period j i)]
theorem lumpOf_add_siteOfCoords {L : ℕ} (g : LumpGrid L) {j : ℕ}
    (hL : ∀ i, (L : ℤ) ∣ (F.period j i : ℤ)) (k : Fin 4 → ℤ)
    (hk : ∀ i, (L : ℤ) ∣ k i) (x : F.Site j) :
    lumpOf g (x + siteOfCoords j k : F.Site j) =
      (lumpOf g x).image (Equiv.addRight (siteOfCoords j k : F.Site j)) := by
  set K : Fin 4 → ℤ := fun i => siteCoords (x + siteOfCoords j k : F.Site j) i - siteCoords x i with hKdef
  have hc : ∀ i, siteCoords (x + siteOfCoords j k : F.Site j) i = siteCoords x i + K i :=
    fun i => by simp [hKdef]
  have hsite : (siteOfCoords j K : F.Site j) = siteOfCoords j k := by
    have h1 : (siteOfCoords j (siteCoords x + K) : F.Site j) = x + siteOfCoords j k := by
      have : siteCoords x + K = siteCoords (x + siteOfCoords j k : F.Site j) := by
        funext i
        simp [hc i]
      rw [this, _root_.YangMills.Construction.TorusContours.siteOfCoords_siteCoords]
    rw [_root_.YangMills.Construction.TorusContours.siteOfCoords_add, _root_.YangMills.Construction.TorusContours.siteOfCoords_siteCoords] at h1
    exact add_left_cancel h1
  have hKL : ∀ i, (L : ℤ) ∣ K i := by
    intro i
    have h1 : ((K i : ℤ) : ZMod (F.period j i)) = (k i : ZMod (F.period j i)) := congrFun hsite i
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
    have h2 := Int.dvd_sub (hk i) ((hL i).trans h1)
    simpa using h2
  have e2 : (lumpOf g x).image (Equiv.addRight (siteOfCoords j k : F.Site j)) = boxSites j
      ((fun i => siteCoords x i - offsetFromCentre L (siteCoords x i) +
        g.lower (offsetFromCentre L (siteCoords x i))) + K)
      ((fun i => siteCoords x i - offsetFromCentre L (siteCoords x i) +
        g.upper (offsetFromCentre L (siteCoords x i))) + K) := by
    rw [← hsite]
    exact boxSites_image_addRight _ _ K
  rw [e2]
  unfold lumpOf
  congr 1
  · funext i
    simp only [Pi.add_apply, hc i, offsetFromCentre_add_dvd _ _ (hKL i)]
    ring
  · funext i
    simp only [Pi.add_apply, hc i, offsetFromCentre_add_dvd _ _ (hKL i)]
    ring
variable (F) in
def fineShift (v : Fin 4 → ℤ) : F.Site F.depth := siteOfCoords F.depth fun i => (F.blockSide : ℤ) * v i
variable (F) in
def cellShift (v : Fin 4 → ℤ) : F.Cell := siteOfCoords F.top v
variable (F) in
abbrev fineShiftEquiv (v : Fin 4 → ℤ) : F.Site F.depth ≃ F.Site F.depth := Equiv.addRight (fineShift F v)
variable (F) in
abbrev cellShiftEquiv (v : Fin 4 → ℤ) : F.Cell ≃ F.Cell := Equiv.addRight (cellShift F v)
variable (v : Fin 4 → ℤ)
theorem cellCentre_add_cellShift (y : F.Cell) :
    (cellCentre F.depth (y + cellShift F v) : F.Site F.depth) = cellCentre F.depth y + fineShift F v := by
  have h : (y + cellShift F v : F.Cell) = siteOfCoords F.top (siteCoords y + v) := by
    rw [_root_.YangMills.Construction.TorusContours.siteOfCoords_add, _root_.YangMills.Construction.TorusContours.siteOfCoords_siteCoords]
    rfl
  rw [h, cellCentre_siteOfCoords, cellCentre_eq, fineShift, ← _root_.YangMills.Construction.TorusContours.siteOfCoords_add]
  congr 1
  funext k
  simp [mul_add]
theorem siteAtOffset_add_cellShift (y : F.Cell) (z : Fin 4 → ℤ) :
    (siteAtOffset (y + cellShift F v) z : F.Site F.depth) = siteAtOffset y z + fineShift F v := by apply _root_.YangMills.Construction.ChainNoise.RuleFromSampler.siteAtOffset_add_siteOfCoords <;> assumption
theorem image_sitesBelow (y : F.Cell) :
    (sitesBelow F.depth y).image (fineShiftEquiv F v) = sitesBelow F.depth (y + cellShift F v) := by
  ext x
  simp only [Finset.mem_image, _root_.YangMills.Construction.TorusContours.mem_sitesBelow_iff]
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, (siteAtOffset_add_cellShift v y z).symm⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨_, ⟨z, hz, rfl⟩, (siteAtOffset_add_cellShift v y z).symm⟩
theorem image_cellBall (y : F.Cell) (r : ℕ) :
    (_root_.YangMills.Construction.LumpContours.cellBall y r).image (cellShiftEquiv F v) = _root_.YangMills.Construction.LumpContours.cellBall (y + cellShift F v) r := by
  ext x
  simp only [_root_.YangMills.Construction.LumpContours.cellBall, Finset.mem_image]
  constructor
  · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨h, hh, add_right_comm _ _ _⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨_, ⟨h, hh, rfl⟩, add_right_comm _ _ _⟩
theorem image_cutBelow (S : Finset F.Cell) :
    (cutBelow F.depth S).image (fineShiftEquiv F v) = cutBelow F.depth (S.image (cellShiftEquiv F v)) := by
  unfold cutBelow
  rw [Finset.image_biUnion, Finset.biUnion_image]
  exact Finset.biUnion_congr rfl fun y _ => image_sitesBelow v y
theorem image_fineShiftEquiv_injective : Function.Injective (Finset.image (fineShiftEquiv F v)) :=
  Finset.image_injective (fineShiftEquiv F v).injective
theorem nearbyLumps_image (h : Finset (Finset (F.Site F.depth))) (y : F.Cell) :
    nearbyLumps (h.image (Finset.image (fineShiftEquiv F v))) (y + cellShift F v) =
      (nearbyLumps h y).image (Finset.image (fineShiftEquiv F v)) := by
  unfold nearbyLumps
  rw [Finset.filter_image]
  congr 1
  refine Finset.filter_congr fun l _ => ?_
  rw [← image_cellBall v y 2, ← image_cutBelow v]
  exact Finset.image_subset_image_iff (fineShiftEquiv F v).injective
theorem isCrowded_image_iff (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth))) (y : F.Cell) :
    IsCrowded J₀ (h.image (Finset.image (fineShiftEquiv F v))) (y + cellShift F v) ↔ IsCrowded J₀ h y := by
  unfold IsCrowded
  rw [nearbyLumps_image v, Finset.card_image_of_injective _ (image_fineShiftEquiv_injective v)]
theorem image_thicken (k : ℕ) (l : Finset (F.Site F.depth)) :
    (thicken k l).image (fineShiftEquiv F v) = thicken k (l.image (fineShiftEquiv F v)) := by
  ext x
  simp only [thicken, Finset.mem_image, Finset.mem_biUnion]
  constructor
  · rintro ⟨_, ⟨w, hw, h, hh, rfl⟩, rfl⟩
    exact ⟨_, ⟨w, hw, rfl⟩, h, hh, add_right_comm _ _ _⟩
  · rintro ⟨_, ⟨w, hw, rfl⟩, h, hh, rfl⟩
    exact ⟨_, ⟨w, hw, h, hh, rfl⟩, add_right_comm _ _ _⟩
theorem excludedBoxes_image (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth))) (y : F.Cell) :
    excludedBoxes J₀ (h.image (Finset.image (fineShiftEquiv F v))) (y + cellShift F v) =
      (excludedBoxes J₀ h y).image (Finset.image (fineShiftEquiv F v)) := by
  unfold excludedBoxes
  by_cases hc : IsCrowded J₀ h y
  · rw [if_pos hc, if_pos ((isCrowded_image_iff v J₀ h y).mpr hc)]
    simp
  · rw [if_neg hc, if_neg (fun e => hc ((isCrowded_image_iff v J₀ h y).mp e))]
    rw [nearbyLumps_image v]
    have e : ((nearbyLumps h y).image (Finset.image (fineShiftEquiv F v))).image lumpCollar =
        ((nearbyLumps h y).image lumpCollar).image (Finset.image (fineShiftEquiv F v)) := by
      rw [Finset.image_image, Finset.image_image]
      refine Finset.image_congr fun l _ => ?_
      simp only [Function.comp, lumpCollar]
      exact (image_thicken v _ l).symm
    rw [e]
    exact mergedBoxes_image_addRight _ _
theorem mem_baseSitesAt_translate_iff (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth))) (y : F.Cell)
    (z : F.Site F.depth) :
    z ∈ baseSitesAt J₀ h y ↔
      z + fineShift F v ∈ baseSitesAt J₀ (h.image (Finset.image (fineShiftEquiv F v))) (y + cellShift F v) := by
  have e1 : nearbyLumps (h.image (Finset.image (fineShiftEquiv F v))) (y + cellShift F v) = ∅ ↔
      nearbyLumps h y = ∅ := by
    rw [nearbyLumps_image v, Finset.image_eq_empty]
  have e2 := isCrowded_image_iff v J₀ h y
  unfold baseSitesAt
  by_cases hc : nearbyLumps h y = ∅ ∨ IsCrowded J₀ h y
  · rw [if_pos hc, if_pos (by rwa [e1, e2])]
    simp only [Finset.mem_singleton, cellCentre_add_cellShift, add_left_inj]
  · rw [if_neg hc, if_neg (by rwa [e1, e2])]
    simp only [Finset.mem_filter]
    rw [excludedBoxes_image v, ← image_sitesBelow v]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨Finset.mem_image_of_mem (fineShiftEquiv F v) h1, ?_⟩
      intro B hB x hx i e
      obtain ⟨B₀, hB₀, rfl⟩ := Finset.mem_image.mp hB
      obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hx
      refine h2 B₀ hB₀ x₀ hx₀ i ?_
      have e' : x₀ i + fineShift F v i = z i + fineShift F v i := e
      exact add_right_cancel e'
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · obtain ⟨z', hz', e⟩ := Finset.mem_image.mp h1
        have e' : z' + fineShift F v = z + fineShift F v := e
        rwa [← add_right_cancel e']
      · intro B hB x hx i e
        refine h2 _ (Finset.mem_image_of_mem _ hB) (x + fineShift F v)
          (Finset.mem_image_of_mem (fineShiftEquiv F v) hx) i ?_
        show x i + fineShift F v i = z i + fineShift F v i
        rw [e]
section Mean
variable {b b' : F.Cell → F.Site F.depth} (hb : ∀ y, b' y + fineShift F v = b (y + cellShift F v))
include hb
theorem minimalOffset_translate (y y' : F.Cell) (hy : y' = y + cellShift F v) (ξ : Fin 4 → ℤ) :
    minimalOffset (b' y) (cellCentre F.depth y + siteOfCoords F.depth ξ) =
      minimalOffset (b y') (cellCentre F.depth y' + siteOfCoords F.depth ξ) := by
  subst hy
  rw [← hb y, cellCentre_add_cellShift]
  have e : cellCentre F.depth y + fineShift F v + siteOfCoords F.depth ξ - (b' y + fineShift F v) =
      cellCentre F.depth y + siteOfCoords F.depth ξ - b' y := by
    abel
  unfold minimalOffset
  rw [e]
theorem contourPath_translate (c : F.Cell × Fin 4) (ξ : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) :
    contourPath b' c ξ π = contourPath b (c.1 + cellShift F v, c.2) ξ π := by
  unfold contourPath
  simp only
  rw [minimalOffset_translate v hb c.1 _ rfl,
    minimalOffset_translate v hb (c.1 + BlockAverages.unitStep F.top c.2)
      (c.1 + cellShift F v + BlockAverages.unitStep F.top c.2)
      (add_right_comm _ _ _)]
theorem isGoodContour_translate_iff (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth))) (c : F.Cell × Fin 4)
    (ξ : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) :
    IsGoodContour J₀ h b' c ξ π ↔
      IsGoodContour J₀ (h.image (Finset.image (fineShiftEquiv F v))) b (c.1 + cellShift F v, c.2) ξ π := by
  have hB : excludedBoxes J₀ (h.image (Finset.image (fineShiftEquiv F v))) (c.1 + cellShift F v) ∪
      excludedBoxes J₀ (h.image (Finset.image (fineShiftEquiv F v))) (c.1 + cellShift F v + BlockAverages.unitStep F.top c.2) =
      (excludedBoxes J₀ h c.1 ∪ excludedBoxes J₀ h (c.1 + BlockAverages.unitStep F.top c.2)).image
        (Finset.image (fineShiftEquiv F v)) := by
    rw [add_right_comm, excludedBoxes_image v, excludedBoxes_image v, Finset.image_union]
  unfold IsGoodContour
  simp only
  rw [hB, ← contourPath_translate v hb, ← hb c.1]
  constructor
  · intro h1 x hx B hB'
    obtain ⟨B₀, hB₀, rfl⟩ := Finset.mem_image.mp hB'
    have hx' : x - fineShift F v ∈ pathSites (b' c.1) (contourPath b' c ξ π) := by
      rw [mem_pathSites_add_right (fineShift F v)]
      simpa using hx
    intro hxB
    obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hxB
    refine h1 _ hx' B₀ hB₀ ?_
    have : (fineShiftEquiv F v) x₀ - fineShift F v = x₀ := by simp
    rwa [this]
  · intro h1 x hx B hB' hxB
    refine h1 (x + fineShift F v) ((mem_pathSites_add_right (fineShift F v) _ _ _).mp hx)
      (B.image (fineShiftEquiv F v)) (Finset.mem_image_of_mem _ hB')
      (Finset.mem_image_of_mem (fineShiftEquiv F v) hxB)
theorem usedContours_translate (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth))) (c : F.Cell × Fin 4) :
    usedContours J₀ h b' c =
      usedContours J₀ (h.image (Finset.image (fineShiftEquiv F v))) b (c.1 + cellShift F v, c.2) := by
  classical
  have hf : ((allContours F).filter fun e => IsGoodContour J₀ h b' c e.1 e.2) =
      (allContours F).filter fun e =>
        IsGoodContour J₀ (h.image (Finset.image (fineShiftEquiv F v))) b (c.1 + cellShift F v, c.2) e.1 e.2 :=
    Finset.filter_congr fun e _ => isGoodContour_translate_iff v hb J₀ h c e.1 e.2
  have c1 := isCrowded_image_iff v J₀ h c.1
  have c2 := isCrowded_image_iff v J₀ h (c.1 + BlockAverages.unitStep F.top c.2)
  rw [add_right_comm] at c2
  unfold usedContours
  simp only [hf, c1, c2]
theorem contourMean_translate (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth))) {X X' : F.GaugeField F.depth}
    (hX : ∀ x i, X' x i = X (x + fineShift F v) i) (c : F.Cell × Fin 4) :
    contourMean J₀ h b' X' c =
      contourMean J₀ (h.image (Finset.image (fineShiftEquiv F v))) b X (c.1 + cellShift F v, c.2) := by
  unfold contourMean
  rw [usedContours_translate v hb]
  congr 1
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [pathHolonomy_translate hX, hb, contourPath_translate v hb]
end Mean
end Lumps
section Hot
variable {L n : ℕ} [NeZero L] [NeZero n]
abbrev stepShift (L n : ℕ) (v : Fin 4 → ℤ) : (stepBlockFrame L n).Site 0 := fineShift (stepBlockFrame L n) v
theorem mem_hotLumps_iff (grid : LumpGrid L) (s : ℝ) (X : (stepBlockFrame L n).GaugeField 0)
    (l : Finset ((stepBlockFrame L n).Site 0)) :
    l ∈ hotLumps grid s (levelSites (stepBlockFrame L n) 0) X ↔
      ∃ (x : (stepBlockFrame L n).Site 0) (μ ν : Fin 4), μ < ν ∧ s ≤ plaquetteDefect X (x, μ, ν) ∧
        ∃ c ∈ plaquetteCorners (x, μ, ν), l = lumpOf grid c := by apply _root_.YangMills.Construction.TranslationKernel.mem_hotLumps_iff <;> assumption
theorem hotLumps_translate (grid : LumpGrid L) (s : ℝ) (v : Fin 4 → ℤ)
    {X X' : (stepBlockFrame L n).GaugeField 0} (hX : ∀ x i, X' x i = X (x + stepShift L n v) i) :
    hotLumps grid s (levelSites (stepBlockFrame L n) 0) X =
      (hotLumps grid s (levelSites (stepBlockFrame L n) 0) X').image
        (Finset.image (Equiv.addRight (stepShift L n v))) := by
  have hdiv : ∀ i, (L : ℤ) ∣ ((stepBlockFrame L n).period 0 i : ℤ) := fun i => by
    rw [stepBlockFrame_period_zero]
    push_cast
    exact Dvd.intro_left _ rfl
  have hlump : ∀ c : (stepBlockFrame L n).Site 0, lumpOf grid (c + stepShift L n v) =
      (lumpOf grid c).image (Equiv.addRight (stepShift L n v)) := fun c =>
    lumpOf_add_siteOfCoords (F := stepBlockFrame L n) (j := 0) grid hdiv (fun i => (L : ℤ) * v i)
      (fun i => Dvd.intro _ rfl) c
  ext l
  rw [Finset.mem_image, mem_hotLumps_iff]
  constructor
  · rintro ⟨x, μ, ν, hlt, hs, c, hc, rfl⟩
    have hx : x = (x - stepShift L n v) + stepShift L n v := by simp
    rw [hx, plaquetteCorners_add_right] at hc
    obtain ⟨c₀, hc₀, rfl⟩ := Finset.mem_image.mp hc
    refine ⟨lumpOf grid c₀, (mem_hotLumps_iff grid s _ _).mpr
      ⟨x - stepShift L n v, μ, ν, hlt, ?_, c₀, hc₀, rfl⟩, (hlump c₀).symm⟩
    rw [plaquetteDefect_translate hX, ← hx]
    exact hs
  · rintro ⟨l₀, hl₀, rfl⟩
    obtain ⟨x, μ, ν, hlt, hs, c, hc, rfl⟩ := (mem_hotLumps_iff grid s _ _).mp hl₀
    refine ⟨x + stepShift L n v, μ, ν, hlt, ?_, c + stepShift L n v, ?_, (hlump c).symm⟩
    · rw [← plaquetteDefect_translate hX]
      exact hs
    · rw [plaquetteCorners_add_right]
      exact Finset.mem_image_of_mem _ hc
end Hot
section Field
variable (ℓ : StepParameters) {n : ℕ} [NeZero n]
theorem fineLevelField_translate (v : Fin 4 → ℤ) (W : TorusField (n * ℓ.side))
    (x : (stepBlockFrame ℓ.side n).Site 0) (i : Fin 4) :
    fineLevelField ℓ n (TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) * v i) W) x i =
      fineLevelField ℓ n W (x + stepShift ℓ.side n v) i := by
  have h1 : (toTorusSite (n * ℓ.side) (x + stepShift ℓ.side n v) : TorusSite (n * ℓ.side)) =
      toTorusSite (n * ℓ.side) x + siteOfInt fun i => (ℓ.side : ℤ) * v i := by
    rw [toTorusSite_add stepBlockFrame_period_zero]
    congr 1
    exact toTorusSite_siteOfCoords stepBlockFrame_period_zero _
  show W (toTorusSite (n * ℓ.side) x + siteOfInt fun i => (ℓ.side : ℤ) * v i) i =
    W (toTorusSite (n * ℓ.side) (x + stepShift ℓ.side n v)) i
  rw [h1]
end Field
end TranslationInvariance
open TranslationInvariance in
theorem translationCarriesBases : translationCarriesBasesStatement := by
  intro ℓ n _ v W
  have hX := fineLevelField_translate ℓ v W
  have hh := hotLumps_translate (n := n) ℓ.grid ℓ.threshold v hX
  refine ⟨fun y z => ?_, fun b b' c hb => ?_⟩
  · have := mem_baseSitesAt_translate_iff (F := stepBlockFrame ℓ.side n) v ℓ.baseDepth
      (fineHotLumps ℓ (fineLevelField ℓ n (TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) * v i) W))) y z
    rw [show fineHotLumps ℓ (fineLevelField ℓ n W) = _ from hh]
    exact this
  · have := contourMean_translate (F := stepBlockFrame ℓ.side n) v hb ℓ.baseDepth
      (fineHotLumps ℓ (fineLevelField ℓ n (TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) * v i) W))) hX c
    rw [show fineHotLumps ℓ (fineLevelField ℓ n W) = _ from hh]
    exact this
end YangMills.Construction.HullTrees
end
