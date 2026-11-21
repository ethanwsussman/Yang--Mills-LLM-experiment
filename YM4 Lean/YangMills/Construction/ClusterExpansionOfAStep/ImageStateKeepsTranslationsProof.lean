import YangMills.Construction.ClusterExpansionOfAStep.AttachedClustersOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.ContoursFromBases
import YangMills.Construction.ClusterExpansionOfAStep.FramesUnderGaugesAndTranslations
import YangMills.Construction.ClusterExpansionOfAStep.ImageStateKeepsTranslations
import YangMills.Construction.ClusterExpansionOfAStep.SitesOfTheTopOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.TranslationsCarryTheKernelAtBases
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusFields TorusLumps StepSettings StepCosts BaseTranslations
namespace TranslationInvariance
section SetTranslations
variable {m : ℕ} [NeZero m]
theorem mem_translateSet {a z : TorusSite m} {Y : Finset (TorusSite m)} : z ∈ translateSet a Y ↔ z + a ∈ Y := by
  classical
  simp [translateSet]
theorem translateSet_neg_translateSet (a : TorusSite m) (Y : Finset (TorusSite m)) :
    translateSet (-a) (translateSet a Y) = Y := by
  ext z
  simp [mem_translateSet]
theorem translateSet_translateSet_neg (a : TorusSite m) (Y : Finset (TorusSite m)) :
    translateSet a (translateSet (-a) Y) = Y := by
  ext z
  simp [mem_translateSet]
theorem supDist_add_right (a x y : TorusSite m) : supDist (x + a) (y + a) = supDist x y := by
  simp [TorusFields.supDist]
theorem mem_thickening_iff {k : ℕ} {X : Finset (TorusSite m)} {z : TorusSite m} :
    z ∈ thickening k X ↔ ∃ x ∈ X, supDist z x ≤ k := by apply _root_.YangMills.Construction.TorusFields.mem_thickening <;> assumption
theorem thickening_translateSet (k : ℕ) (a : TorusSite m) (X : Finset (TorusSite m)) :
    thickening k (translateSet a X) = translateSet a (thickening k X) := by
  ext z
  rw [mem_translateSet, mem_thickening_iff, mem_thickening_iff]
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨x + a, mem_translateSet.mp hx, by rwa [supDist_add_right]⟩
  · rintro ⟨x, hx, h⟩
    refine ⟨x - a, mem_translateSet.mpr (by simpa using hx), ?_⟩
    rw [← supDist_add_right a]
    simpa using h
theorem chainConnected_of_translateSet {r : ℕ} {a : TorusSite m} {Y : Finset (TorusSite m)} {z w : TorusSite m}
    (h : ChainConnected r (translateSet a Y) z w) : ChainConnected r Y (z + a) (w + a) := by
  unfold ChainConnected at h ⊢
  induction h with
  | refl => exact .refl
  | tail _ hs ih =>
    obtain ⟨hu, hv, huv⟩ := hs
    exact ih.tail ⟨mem_translateSet.mp hu, mem_translateSet.mp hv, by rwa [supDist_add_right]⟩
theorem chainConnected_translateSet {r : ℕ} {a : TorusSite m} {Y : Finset (TorusSite m)} {z w : TorusSite m} :
    ChainConnected r (translateSet a Y) z w ↔ ChainConnected r Y (z + a) (w + a) := by
  refine ⟨chainConnected_of_translateSet, fun h => ?_⟩
  have h' : ChainConnected r (translateSet (-a) (translateSet a Y)) (z + a) (w + a) := by
    rw [translateSet_neg_translateSet]
    exact h
  simpa using chainConnected_of_translateSet h'
theorem chainComponents_translateSet (r : ℕ) (a : TorusSite m) (Y : Finset (TorusSite m)) :
    chainComponents r (translateSet a Y) = (chainComponents r Y).image (translateSet a) := by
  classical
  have key : ∀ y, translateSet a (Y.filter (ChainConnected r Y y)) =
      (translateSet a Y).filter (ChainConnected r (translateSet a Y) (y - a)) := by
    intro y
    ext z
    simp only [mem_translateSet, Finset.mem_filter, chainConnected_translateSet, sub_add_cancel]
  ext X
  simp only [chainComponents, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨_, ⟨y + a, mem_translateSet.mp hy, rfl⟩, ?_⟩
    rw [key]
    simp
  · rintro ⟨X₀, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨y - a, mem_translateSet.mpr (by simpa using hy), ?_⟩
    rw [key]
def translateBonds (a : TorusSite m) (B : Finset (TorusBond m)) : Finset (TorusBond m) :=
  open Classical in Finset.univ.filter fun c => (c.1 + a, c.2) ∈ B
theorem mem_translateBonds {a : TorusSite m} {B : Finset (TorusBond m)} {c : TorusBond m} :
    c ∈ translateBonds a B ↔ (c.1 + a, c.2) ∈ B := by
  classical
  simp [translateBonds]
theorem image_fst_translateBonds (a : TorusSite m) (B : Finset (TorusBond m)) :
    (open Classical in (translateBonds a B).image Prod.fst) =
      translateSet a (open Classical in B.image Prod.fst) := by
  classical
  ext z
  simp only [Finset.mem_image, mem_translateSet, mem_translateBonds]
  constructor
  · rintro ⟨⟨x, i⟩, h, rfl⟩
    exact ⟨_, h, rfl⟩
  · rintro ⟨⟨x, i⟩, h, e⟩
    simp only at e
    exact ⟨(z, i), by simpa [← e] using h, rfl⟩
def translateSetEquiv (a : TorusSite m) : Finset (TorusSite m) ≃ Finset (TorusSite m) where
  toFun := translateSet a
  invFun := translateSet (-a)
  left_inv := translateSet_neg_translateSet a
  right_inv := translateSet_translateSet_neg a
theorem translateBonds_neg_translateBonds (a : TorusSite m) (B : Finset (TorusBond m)) :
    translateBonds (-a) (translateBonds a B) = B := by
  ext c
  simp [mem_translateBonds]
theorem translateBonds_translateBonds_neg (a : TorusSite m) (B : Finset (TorusBond m)) :
    translateBonds a (translateBonds (-a) B) = B := by
  ext c
  simp [mem_translateBonds]
end SetTranslations
section ScaledCoordinates
variable {n L : ℕ}
abbrev scaleCoords (L : ℕ) (v : Fin 4 → ℤ) : Fin 4 → ℤ := fun i => (L : ℤ) * v i
theorem exists_cast_add_intCast {m : ℕ} [NeZero m] (x : ZMod m) (z : ℤ) :
    ∃ k : ℤ, (((x + (z : ZMod m) : ZMod m)).cast : ℤ) = (x.cast : ℤ) + z + (m : ℤ) * k := by
  have h : (((((x + (z : ZMod m) : ZMod m)).cast : ℤ) : ℤ) : ZMod m) = (((x.cast : ℤ) + z : ℤ) : ZMod m) := by
    push_cast
    simp
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h
  exact ⟨-k, by linarith⟩
theorem parentBlock_add_scale [NeZero n] [NeZero L] (x : TorusSite (n * L)) (v : Fin 4 → ℤ) :
    parentBlock L (x + siteOfInt (scaleCoords L v)) = parentBlock L x + siteOfInt v := by
  have hne : NeZero (n * L) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
  have hL : (L : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne L
  funext i
  obtain ⟨k, hk⟩ := exists_cast_add_intCast (x i) ((L : ℤ) * v i)
  simp only [parentBlock, Pi.add_apply, siteOfInt]
  rw [hk]
  have e : ((x i).cast : ℤ) + (L : ℤ) * v i + ((n * L : ℕ) : ℤ) * k + ((L : ℤ) - 1) / 2 =
      (((x i).cast : ℤ) + ((L : ℤ) - 1) / 2) + (L : ℤ) * (v i + (n : ℤ) * k) := by
    push_cast
    ring
  rw [e, Int.add_mul_ediv_left _ _ hL]
  push_cast
  simp
theorem siteOffset_add_scale [NeZero n] [NeZero L] (x : TorusSite (n * L)) (v : Fin 4 → ℤ) :
    siteOffset (x + siteOfInt (scaleCoords L v)) = siteOffset x := by
  have hne : NeZero (n * L) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
  funext i
  obtain ⟨k, hk⟩ := exists_cast_add_intCast (x i) ((L : ℤ) * v i)
  simp only [siteOffset, Pi.add_apply, siteOfInt]
  rw [hk]
  have e : ((x i).cast : ℤ) + (L : ℤ) * v i + ((n * L : ℕ) : ℤ) * k + ((L : ℤ) - 1) / 2 =
      (((x i).cast : ℤ) + ((L : ℤ) - 1) / 2) + (L : ℤ) * (v i + (n : ℤ) * k) := by
    push_cast
    ring
  rw [e, Int.add_mul_emod_self_left]
theorem blockSite_add [NeZero n] [NeZero L] (y : TorusSite n) (o : BlockOffset L) (v : Fin 4 → ℤ) :
    (blockSite (y + siteOfInt v) o : TorusSite (n * L)) = blockSite y o + siteOfInt (scaleCoords L v) := by
  funext i
  obtain ⟨k, hk⟩ := exists_cast_add_intCast (y i) (v i)
  simp only [blockSite, siteOfInt, Pi.add_apply]
  rw [hk]
  have e : (L : ℤ) * (((y i).cast : ℤ) + v i + (n : ℤ) * k) + (((o i : ℕ) : ℤ) - ((L : ℤ) - 1) / 2) =
      ((L : ℤ) * ((y i).cast : ℤ) + (((o i : ℕ) : ℤ) - ((L : ℤ) - 1) / 2)) + (L : ℤ) * v i +
        ((n * L : ℕ) : ℤ) * k := by
    push_cast
    ring
  rw [e, Int.cast_add, Int.cast_mul ((n * L : ℕ) : ℤ), Int.cast_natCast, ZMod.natCast_self, zero_mul, add_zero,
    Int.cast_add]
theorem siteOfInt_scaleCoords_neg (v : Fin 4 → ℤ) :
    (siteOfInt (scaleCoords L (-v)) : TorusSite (n * L)) = - siteOfInt (scaleCoords L v) := by
  funext i
  simp [siteOfInt]
theorem siteOfInt_neg {m : ℕ} (v : Fin 4 → ℤ) : (siteOfInt (-v) : TorusSite m) = - siteOfInt v := by
  funext i
  simp [siteOfInt]
end ScaledCoordinates
section Clusters
variable {n L : ℕ} [NeZero n] [NeZero L]
theorem mem_sitesInBlocks {S : Finset (TorusSite n)} {x : TorusSite (n * L)} :
    x ∈ sitesInBlocks L S ↔ parentBlock L x ∈ S := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.mem_sitesInBlocks <;> assumption
theorem sitesInBlocks_translateSet (v : Fin 4 → ℤ) (S : Finset (TorusSite n)) :
    sitesInBlocks L (translateSet (siteOfInt v) S) =
      translateSet (siteOfInt (scaleCoords L v)) (sitesInBlocks L S) := by
  ext x
  rw [mem_translateSet, mem_sitesInBlocks, mem_sitesInBlocks, mem_translateSet, parentBlock_add_scale]
theorem translateSet_inter_nonempty {m : ℕ} [NeZero m] (a : TorusSite m) (X Y : Finset (TorusSite m)) :
    (open Classical in (translateSet a X ∩ translateSet a Y).Nonempty) ↔
      (open Classical in (X ∩ Y).Nonempty) := by
  classical
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hz
    exact ⟨z + a, Finset.mem_inter.mpr ⟨mem_translateSet.mp h1, mem_translateSet.mp h2⟩⟩
  · rintro ⟨z, hz⟩
    obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hz
    exact ⟨z - a, Finset.mem_inter.mpr
      ⟨mem_translateSet.mpr (by simpa using h1), mem_translateSet.mpr (by simpa using h2)⟩⟩
variable (r r' : ℕ) (v : Fin 4 → ℤ) (bad : Finset (TorusBond (n * L))) (Yt : Finset (TorusSite (n * L)))
  (C : Finset (TorusSite n))
theorem clusterComponents_translate :
    clusterComponents L r (translateBonds (siteOfInt (scaleCoords L v)) bad)
        (translateSet (siteOfInt (scaleCoords L v)) Yt) (translateSet (siteOfInt v) C) =
      (clusterComponents L r bad Yt C).image (translateSet (siteOfInt (scaleCoords L v))) := by
  classical
  unfold clusterComponents
  rw [← chainComponents_translateSet]
  congr 1
  rw [image_fst_translateBonds, sitesInBlocks_translateSet]
  ext z
  simp [mem_translateSet]
theorem attachedSites_translate :
    attachedSites L r (translateBonds (siteOfInt (scaleCoords L v)) bad)
        (translateSet (siteOfInt (scaleCoords L v)) Yt) (translateSet (siteOfInt v) C) =
      translateSet (siteOfInt (scaleCoords L v)) (attachedSites L r bad Yt C) := by
  classical
  ext z
  rw [mem_translateSet]
  simp only [attachedSites, Finset.mem_biUnion, Finset.mem_filter, id, clusterComponents_translate,
    Finset.mem_image]
  constructor
  · rintro ⟨X', ⟨⟨X, hX, rfl⟩, hn⟩, hz⟩
    rw [sitesInBlocks_translateSet] at hn
    exact ⟨X, ⟨hX, (translateSet_inter_nonempty _ _ _).mp (by convert hn)⟩, mem_translateSet.mp hz⟩
  · rintro ⟨X, ⟨hX, hn⟩, hz⟩
    refine ⟨_, ⟨⟨X, hX, rfl⟩, ?_⟩, mem_translateSet.mpr hz⟩
    rw [sitesInBlocks_translateSet]
    convert (translateSet_inter_nonempty (siteOfInt (scaleCoords L v)) X (sitesInBlocks L C)).mpr
      (by convert hn)
theorem coreBlocks_translateSet (θ : Finset (TorusSite (n * L))) :
    coreBlocks L r (translateSet (siteOfInt (scaleCoords L v)) θ) =
      translateSet (siteOfInt v) (coreBlocks L r θ) := by
  classical
  ext y
  rw [mem_translateSet]
  simp only [coreBlocks, Finset.mem_filter, Finset.mem_univ, true_and, thickening_translateSet]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hx
    refine ⟨x + siteOfInt (scaleCoords L v), Finset.mem_inter.mpr ⟨?_, mem_translateSet.mp h2⟩⟩
    rw [mem_sitesInBlocks, parentBlock_add_scale, Finset.mem_singleton.mp (mem_sitesInBlocks.mp h1)]
    exact Finset.mem_singleton_self _
  · rintro ⟨x, hx⟩
    obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hx
    have e : parentBlock L (x + siteOfInt (scaleCoords L (-v))) = y := by
      rw [parentBlock_add_scale, Finset.mem_singleton.mp (mem_sitesInBlocks.mp h1), siteOfInt_neg]
      simp
    refine ⟨x + siteOfInt (scaleCoords L (-v)), Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · rw [mem_sitesInBlocks, e]
      exact Finset.mem_singleton_self _
    · rw [mem_translateSet, siteOfInt_scaleCoords_neg]
      simpa using h2
theorem storedBlocks_translate :
    storedBlocks L r (translateBonds (siteOfInt (scaleCoords L v)) bad)
        (translateSet (siteOfInt (scaleCoords L v)) Yt) (translateSet (siteOfInt v) C) =
      translateSet (siteOfInt v) (storedBlocks L r bad Yt C) := by
  classical
  unfold storedBlocks
  rw [attachedSites_translate, coreBlocks_translateSet]
  ext z
  simp [mem_translateSet]
theorem coarseHull_translate :
    coarseHull L r r' (translateBonds (siteOfInt (scaleCoords L v)) bad)
        (translateSet (siteOfInt (scaleCoords L v)) Yt) (translateSet (siteOfInt v) C) =
      translateSet (siteOfInt v) (coarseHull L r r' bad Yt C) := by
  unfold coarseHull
  rw [storedBlocks_translate, thickening_translateSet]
end Clusters
section HotLumps
variable {ℓ : StepParameters} {m : ℕ} [NeZero m]
theorem curvature_translate_eq (a : TorusSite m) (W : TorusField m) (x : TorusSite m) (μ ν : Fin 4) :
    curvature (TorusFields.translate a W) x μ ν = curvature W (x + a) μ ν := by
  simp only [curvature, TorusFields.holonomy, TorusFields.translate, add_right_comm x a]
theorem mem_plaquetteVertices_add (a : TorusSite m) (x z : TorusSite m) (μ ν : Fin 4) :
    z ∈ plaquetteVertices x μ ν ↔ z + a ∈ plaquetteVertices (x + a) μ ν := by
  simp only [plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false, add_right_comm x a, add_left_inj,
    add_right_comm (x + TorusFields.unitStep m μ) a]
theorem translateSet_torusLumpOf (hfit : ℓ.Admissible) (hLm : ℓ.side ∣ m) (w : Fin 4 → ℤ) (z : TorusSite m) :
    translateSet (siteOfInt (scaleCoords ℓ.side w)) (torusLumpOf ℓ (z + siteOfInt (scaleCoords ℓ.side w))) =
      torusLumpOf ℓ z := by
  classical
  ext x
  rw [mem_translateSet]
  simp only [torusLumpOf, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [lumpCorner_add_side_mul hfit hLm, lumpCorner_add_side_mul hfit hLm, add_left_inj]
theorem torusHotLumps_translate (hfit : ℓ.Admissible) (hLm : ℓ.side ∣ m) (w : Fin 4 → ℤ) (W : TorusField m) :
    torusHotLumps ℓ (TorusFields.translate (siteOfInt (scaleCoords ℓ.side w)) W) =
      (torusHotLumps ℓ W).image (translateSet (siteOfInt (scaleCoords ℓ.side w))) := by
  classical
  set a : TorusSite m := siteOfInt (scaleCoords ℓ.side w) with ha
  ext l
  rw [mem_torusHotLumps_iff ℓ hfit hLm, Finset.mem_image]
  constructor
  · rintro ⟨x, μ, ν, hlt, hs, z, hz, rfl⟩
    refine ⟨torusLumpOf ℓ (z + a), (mem_torusHotLumps_iff ℓ hfit hLm W _).mpr ⟨x + a, μ, ν, hlt, ?_, z + a, ?_, rfl⟩,
      translateSet_torusLumpOf hfit hLm w z⟩
    · rwa [← curvature_translate_eq]
    · exact (mem_plaquetteVertices_add a x z μ ν).mp hz
  · rintro ⟨l₀, h, rfl⟩
    obtain ⟨x, μ, ν, hlt, hs, z, hz, rfl⟩ := (mem_torusHotLumps_iff ℓ hfit hLm W _).mp h
    refine ⟨x - a, μ, ν, hlt, ?_, z - a, ?_, ?_⟩
    · rw [curvature_translate_eq, sub_add_cancel]
      exact hs
    · rw [mem_plaquetteVertices_add a, sub_add_cancel, sub_add_cancel]
      exact hz
    · have := translateSet_torusLumpOf hfit hLm w (z - a)
      rw [← ha, sub_add_cancel] at this
      exact this
theorem torusHotSites_translate (hfit : ℓ.Admissible) (hLm : ℓ.side ∣ m) (w : Fin 4 → ℤ) (W : TorusField m) :
    torusHotSites ℓ (TorusFields.translate (siteOfInt (scaleCoords ℓ.side w)) W) =
      translateSet (siteOfInt (scaleCoords ℓ.side w)) (torusHotSites ℓ W) := by
  classical
  ext z
  rw [mem_translateSet]
  simp only [torusHotSites, torusHotLumps_translate hfit hLm, Finset.mem_biUnion, Finset.mem_image, id]
  constructor
  · rintro ⟨_, ⟨l, hl, rfl⟩, hz⟩
    exact ⟨l, hl, mem_translateSet.mp hz⟩
  · rintro ⟨l, hl, hz⟩
    exact ⟨_, ⟨l, hl, rfl⟩, mem_translateSet.mpr hz⟩
theorem isHullState_translate (hfit : ℓ.Admissible) (hLm : ℓ.side ∣ m) (w : Fin 4 → ℤ) (r : ℕ)
    {W : TorusField m} {Y : Finset (TorusSite m)} (h : IsHullState ℓ r W Y) :
    IsHullState ℓ r (TorusFields.translate (siteOfInt (scaleCoords ℓ.side w)) W)
      (translateSet (siteOfInt (scaleCoords ℓ.side w)) Y) := by
  classical
  refine ⟨?_, ?_⟩
  · rw [torusHotSites_translate hfit hLm, thickening_translateSet]
    intro z hz
    exact mem_translateSet.mpr (h.1 (mem_translateSet.mp hz))
  · intro X' hX'
    rw [chainComponents_translateSet, Finset.mem_image] at hX'
    obtain ⟨X, hX, rfl⟩ := hX'
    obtain ⟨l, hl, hn⟩ := h.2 X hX
    refine ⟨translateSet (siteOfInt (scaleCoords ℓ.side w)) l, ?_, ?_⟩
    · rw [torusHotLumps_translate hfit hLm]
      exact Finset.mem_image_of_mem _ hl
    · convert (translateSet_inter_nonempty (siteOfInt (scaleCoords ℓ.side w)) l X).mpr (by convert hn)
theorem translate_neg_translate (a : TorusSite m) (W : TorusField m) :
    TorusFields.translate (-a) (TorusFields.translate a W) = W := by
  funext x i
  simp [TorusFields.translate]
theorem isHullState_translate_iff (hfit : ℓ.Admissible) (hLm : ℓ.side ∣ m) (w : Fin 4 → ℤ) (r : ℕ)
    {W : TorusField m} {Y : Finset (TorusSite m)} :
    IsHullState ℓ r (TorusFields.translate (siteOfInt (scaleCoords ℓ.side w)) W)
        (translateSet (siteOfInt (scaleCoords ℓ.side w)) Y) ↔ IsHullState ℓ r W Y := by
  refine ⟨fun h => ?_, isHullState_translate hfit hLm w r⟩
  have h' := isHullState_translate hfit hLm (-w) r h
  have e : (siteOfInt (scaleCoords ℓ.side (-w)) : TorusSite m) = - siteOfInt (scaleCoords ℓ.side w) := by
    funext i
    simp [siteOfInt]
  rw [e, translate_neg_translate, translateSet_neg_translateSet] at h'
  exact h'
end HotLumps
section CoarseStates
variable {R : StepSetup} {n : ℕ} [NeZero n]
def translateState (q : CoarseState R n) (a : TorusSite n) : CoarseState R n :=
  ⟨translateSet a q.1, translateLabel a q.1 q.2⟩
theorem coarseState_ext (q q' : CoarseState R n) (h1 : q.1 = q'.1) (h2 : ∀ y, q.markAt y = q'.markAt y) :
    q = q' := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.coarseState_ext <;> assumption
theorem markAt_translateState (q : CoarseState R n) (a y : TorusSite n) :
    (translateState q a).markAt y = q.markAt (y + a) := by
  classical
  by_cases h : y + a ∈ q.1
  · have h' : y ∈ (translateState q a).1 := mem_translateSet.mpr h
    simp only [CoarseState.markAt, dif_pos h, dif_pos h']
    rfl
  · have h' : y ∉ (translateState q a).1 := fun e => h (mem_translateSet.mp e)
    rw [markAt_of_not_mem h, markAt_of_not_mem h']
theorem translateState_neg (q : CoarseState R n) (a : TorusSite n) :
    translateState (translateState q a) (-a) = q := by
  refine coarseState_ext _ _ (translateSet_neg_translateSet a q.1) fun y => ?_
  rw [markAt_translateState, markAt_translateState]
  simp
theorem translateState_injective (a : TorusSite n) :
    Function.Injective fun q : CoarseState R n => translateState q a := by
  intro q q' h
  have := congrArg (fun p => translateState p (-a)) h
  simpa [translateState_neg] using this
theorem labelAt_translateState (q : CoarseState R n) (v : Fin 4 → ℤ) (z : TorusSite (n * R.params.side)) :
    (translateState q (siteOfInt v)).labelAt z = q.labelAt (z + siteOfInt (scaleCoords R.params.side v)) := by
  simp only [CoarseState.labelAt]
  rw [markAt_translateState, ← parentBlock_add_scale, siteOffset_add_scale]
theorem fieldWithStoredLinks_translateState (q : CoarseState R n) (v : Fin 4 → ℤ)
    (W : TorusField (n * R.params.side)) :
    (translateState q (siteOfInt v)).fieldWithStoredLinks
        (TorusFields.translate (siteOfInt (scaleCoords R.params.side v)) W) =
      TorusFields.translate (siteOfInt (scaleCoords R.params.side v)) (q.fieldWithStoredLinks W) := by
  funext x i
  simp only [CoarseState.fieldWithStoredLinks, TorusFields.translate]
  rw [markAt_translateState, ← parentBlock_add_scale, siteOffset_add_scale]
theorem mem_unlabelled {q : CoarseState R n} {Yt : Finset (TorusSite (n * R.params.side))}
    {z : TorusSite (n * R.params.side)} :
    z ∈ q.unlabelled Yt ↔ z ∈ Yt ∧ q.labelAt z = Sum.inl () := by
  classical
  simp [CoarseState.unlabelled]
def unlabelledEquiv (q : CoarseState R n) (v : Fin 4 → ℤ) (Yt : Finset (TorusSite (n * R.params.side))) :
    (translateState q (siteOfInt v)).unlabelled (translateSet (siteOfInt (scaleCoords R.params.side v)) Yt) ≃
      q.unlabelled Yt where
  toFun z := ⟨z.1 + siteOfInt (scaleCoords R.params.side v), by
    have h := mem_unlabelled.mp z.2
    exact mem_unlabelled.mpr ⟨mem_translateSet.mp h.1, by rw [← labelAt_translateState]; exact h.2⟩⟩
  invFun z := ⟨z.1 - siteOfInt (scaleCoords R.params.side v), by
    have h := mem_unlabelled.mp z.2
    refine mem_unlabelled.mpr ⟨mem_translateSet.mpr (by simpa using h.1), ?_⟩
    rw [labelAt_translateState, sub_add_cancel]
    exact h.2⟩
  left_inv z := by simp
  right_inv z := by simp
theorem fillLabels_translateState (q : CoarseState R n) (v : Fin 4 → ℤ)
    (Yt : Finset (TorusSite (n * R.params.side))) (ν : q.unlabelled Yt → R.labels.Ω) :
    (translateState q (siteOfInt v)).fillLabels (translateSet (siteOfInt (scaleCoords R.params.side v)) Yt)
        (fun z => ν (unlabelledEquiv q v Yt z)) =
      translateLabel (siteOfInt (scaleCoords R.params.side v)) Yt (q.fillLabels Yt ν) := by
  funext ⟨z, hz⟩
  have hz' : z + siteOfInt (scaleCoords R.params.side v) ∈ Yt := mem_translateSet.mp hz
  show _ = q.fillLabels Yt ν ⟨z + siteOfInt (scaleCoords R.params.side v), hz'⟩
  by_cases h : q.labelAt (z + siteOfInt (scaleCoords R.params.side v)) = Sum.inl ()
  · have h1 : z + siteOfInt (scaleCoords R.params.side v) ∈ q.unlabelled Yt := mem_unlabelled.mpr ⟨hz', h⟩
    have h2 : z ∈ (translateState q (siteOfInt v)).unlabelled
        (translateSet (siteOfInt (scaleCoords R.params.side v)) Yt) :=
      mem_unlabelled.mpr ⟨hz, by rw [labelAt_translateState]; exact h⟩
    rw [fillLabels_of_mem_unlabelled _ _ _ _ hz h2, fillLabels_of_mem_unlabelled _ _ _ _ hz' h1]
    rfl
  · have h1 : z + siteOfInt (scaleCoords R.params.side v) ∈ q.labelSet := mem_labelSet.mpr h
    have h2 : z ∈ (translateState q (siteOfInt v)).labelSet :=
      mem_labelSet.mpr (by rw [labelAt_translateState]; exact h)
    rw [fillLabels_of_mem _ _ _ _ hz h2, fillLabels_of_mem _ _ _ _ hz' h1]
    have e1 := labelAt_eq_inr_labeling (translateState q (siteOfInt v)) ⟨z, h2⟩
    have e2 := labelAt_eq_inr_labeling q ⟨_, h1⟩
    simp only at e1 e2
    rw [labelAt_translateState, e2] at e1
    exact (Sum.inr_injective e1).symm
end CoarseStates
section Charts
variable {F : BlockFrame} (u : Fin 4 → ℤ)
def cellTranslationSite : F.Site F.depth := siteOfCoords F.depth fun i => (F.blockSide : ℤ) * u i
def translateFine (X : F.GaugeField F.depth) : F.GaugeField F.depth := fun x i => X (x + cellTranslationSite u) i
def translateCoarse (U : F.GaugeField F.top) : F.GaugeField F.top := fun y i => U (y + siteOfCoords F.top u) i
theorem pathHolonomy_translateFine (X : F.GaugeField F.depth) (x : F.Site F.depth) (l : List PathStep) :
    pathHolonomy (translateFine u X) x l = pathHolonomy X (x + cellTranslationSite u) l := by
  induction l generalizing x with
  | nil => rfl
  | cons st r ih =>
    have e : BlockAverages.linkValue (translateFine u X) x st =
        BlockAverages.linkValue X (x + cellTranslationSite u) st := by
      unfold BlockAverages.linkValue translateFine
      split_ifs
      · rfl
      · have e1 : x - BlockAverages.unitStep F.depth st.1 + cellTranslationSite u =
            x + cellTranslationSite u - BlockAverages.unitStep F.depth st.1 := by abel
        rw [e1]
    have e2 : x + stepDisplacement F.depth st + cellTranslationSite u =
        x + cellTranslationSite u + stepDisplacement F.depth st := by abel
    simp only [pathHolonomy, e, ih, e2]
theorem cellCentre_add_siteOfCoords (z : F.Cell) :
    cellCentre F.depth (z + siteOfCoords F.top u) = cellCentre F.depth z + cellTranslationSite u := by
  rw [cellCentre_add F.depth (by simp [BlockFrame.top])]
  unfold cellTranslationSite
  congr 2
  funext i
  simp [BlockFrame.top]
theorem cellCentre_add_add_translation (z : F.Cell) (h : Fin 4 → ℤ) :
    cellCentre F.depth z + siteOfCoords F.depth h + cellTranslationSite u =
      cellCentre F.depth (z + siteOfCoords F.top u) + siteOfCoords F.depth h := by
  rw [cellCentre_add_siteOfCoords]
  abel
theorem enclosingCell_add_translation (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    [∀ j i, NeZero (F.period j i)] (x : F.Site F.depth) :
    enclosingCell (x + cellTranslationSite u) = enclosingCell x + siteOfCoords F.top u := by
  obtain ⟨z, h, hh, rfl⟩ := TopLevelSites.exists_centre_add hL hs x
  rw [cellCentre_add_add_translation, TopLevelSites.enclosingCell_centre_add hL hs _ _ hh,
    TopLevelSites.enclosingCell_centre_add hL hs _ _ hh]
theorem cellOffset_add_translation (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    [∀ j i, NeZero (F.period j i)] (x : F.Site F.depth) :
    cellOffset (x + cellTranslationSite u) = cellOffset x := by
  obtain ⟨z, h, hh, rfl⟩ := TopLevelSites.exists_centre_add hL hs x
  rw [cellCentre_add_add_translation, TopLevelSites.cellOffset_centre_add hL hs _ _ hh,
    TopLevelSites.cellOffset_centre_add hL hs _ _ hh]
theorem isCrossingBond_add_translation (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    [∀ j i, NeZero (F.period j i)] (x : F.Site F.depth) (i : Fin 4) :
    IsCrossingBond (x + cellTranslationSite u, i) ↔ IsCrossingBond (x, i) := by
  obtain ⟨z, h, hh, rfl⟩ := TopLevelSites.exists_centre_add hL hs x
  rw [cellCentre_add_add_translation, TopLevelSites.isCrossingBond_iff hL hs _ _ hh,
    TopLevelSites.isCrossingBond_iff hL hs _ _ hh]
theorem isAxialTreeBond_add_translation (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    [∀ j i, NeZero (F.period j i)] (x : F.Site F.depth) (i : Fin 4) :
    IsAxialTreeBond (x + cellTranslationSite u, i) ↔ IsAxialTreeBond (x, i) := by
  obtain ⟨z, h, hh, rfl⟩ := TopLevelSites.exists_centre_add hL hs x
  rw [cellCentre_add_add_translation, TopLevelSites.isAxialTreeBond_iff hL hs _ _ hh,
    TopLevelSites.isAxialTreeBond_iff hL hs _ _ hh]
theorem axialGauge_translateFine (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    [∀ j i, NeZero (F.period j i)] (π : Equiv.Perm (Fin 4)) (X : F.GaugeField F.depth) (x : F.Site F.depth) :
    axialGauge π (translateFine u X) x = axialGauge π X (x + cellTranslationSite u) := by
  unfold axialGauge
  rw [pathHolonomy_translateFine, cellOffset_add_translation u hL hs, enclosingCell_add_translation u hL hs,
    cellCentre_add_siteOfCoords]
theorem bondCoordinate_translate (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    [∀ j i, NeZero (F.period j i)] (π : Equiv.Perm (Fin 4)) (U : F.GaugeField F.top) (X : F.GaugeField F.depth)
    (x : F.Site F.depth) (i : Fin 4) :
    bondCoordinate π (translateCoarse u U) (translateFine u X) (x, i) =
      bondCoordinate π U X (x + cellTranslationSite u, i) := by
  classical
  have e : gaugeTransform (axialGauge π (translateFine u X)) (translateFine u X) x i =
      gaugeTransform (axialGauge π X) X (x + cellTranslationSite u) i := by
    unfold BlockAverages.gaugeTransform
    rw [axialGauge_translateFine u hL hs, axialGauge_translateFine u hL hs]
    have e2 : x + BlockAverages.unitStep F.depth i + cellTranslationSite u =
        x + cellTranslationSite u + BlockAverages.unitStep F.depth i := by abel
    simp only [translateFine, e2]
  unfold bondCoordinate
  by_cases h : IsCrossingBond (x, i)
  · have h' : IsCrossingBond (x + cellTranslationSite u, i) := (isCrossingBond_add_translation u hL hs x i).mpr h
    rw [if_pos h, if_pos h']
    simp only [e, translateCoarse, enclosingCell_add_translation u hL hs]
  · have h' : ¬ IsCrossingBond (x + cellTranslationSite u, i) :=
      fun c => h ((isCrossingBond_add_translation u hL hs x i).mp c)
    rw [if_neg h, if_neg h']
    simp only [e]
end Charts
section StepFrame
variable {ℓ : StepParameters} {n : ℕ} [NeZero n]
theorem cellTranslationSite_stepBlockFrame (v : Fin 4 → ℤ) :
    (cellTranslationSite (F := stepBlockFrame ℓ.side n) v :
        (stepBlockFrame ℓ.side n).Site (stepBlockFrame ℓ.side n).depth) =
      torusSiteInFrame (stepBlockFrame ℓ.side n) (stepBlockFrame ℓ.side n).depth
        (siteOfInt (scaleCoords ℓ.side v) : TorusSite (n * ℓ.side)) :=
  (TopLevelSites.torusSiteInFrame_siteOfInt (F := stepBlockFrame ℓ.side n) (j := (stepBlockFrame ℓ.side n).depth)
    (N := n * ℓ.side) TorusContours.stepBlockFrame_period_zero (scaleCoords ℓ.side v)).symm
theorem torusSiteInFrame_add_scale (v : Fin 4 → ℤ) (x : TorusSite (n * ℓ.side)) :
    torusSiteInFrame (stepBlockFrame ℓ.side n) (stepBlockFrame ℓ.side n).depth
        (x + siteOfInt (scaleCoords ℓ.side v)) =
      torusSiteInFrame (stepBlockFrame ℓ.side n) (stepBlockFrame ℓ.side n).depth x +
        cellTranslationSite (F := stepBlockFrame ℓ.side n) v := by
  rw [cellTranslationSite_stepBlockFrame]
  exact TopLevelSites.torusSiteInFrame_add (F := stepBlockFrame ℓ.side n) (j := (stepBlockFrame ℓ.side n).depth)
    (N := n * ℓ.side) TorusContours.stepBlockFrame_period_zero _ _
theorem toTorusSite_add_fine (v : Fin 4 → ℤ) (x : (stepBlockFrame ℓ.side n).Site (stepBlockFrame ℓ.side n).depth) :
    toTorusSite (n * ℓ.side) (x + cellTranslationSite (F := stepBlockFrame ℓ.side n) v) =
      toTorusSite (n * ℓ.side) x + siteOfInt (scaleCoords ℓ.side v) := by
  rw [TopLevelSites.toTorusSite_add (F := stepBlockFrame ℓ.side n) (j := (stepBlockFrame ℓ.side n).depth)
    (N := n * ℓ.side) TorusContours.stepBlockFrame_period_zero]
  congr 1
  exact TopLevelSites.toTorusSite_siteOfCoords (F := stepBlockFrame ℓ.side n) (j := (stepBlockFrame ℓ.side n).depth)
    (N := n * ℓ.side) TorusContours.stepBlockFrame_period_zero _
theorem toTorusSite_add_coarse (v : Fin 4 → ℤ) (y : (stepBlockFrame ℓ.side n).Cell) :
    toTorusSite n (y + siteOfCoords (stepBlockFrame ℓ.side n).top v) = toTorusSite n y + siteOfInt v := by
  rw [TopLevelSites.toTorusSite_add (F := stepBlockFrame ℓ.side n) (j := (stepBlockFrame ℓ.side n).top) (N := n)
    TorusContours.stepBlockFrame_period_one]
  congr 1
  exact TopLevelSites.toTorusSite_siteOfCoords (F := stepBlockFrame ℓ.side n) (j := (stepBlockFrame ℓ.side n).top)
    (N := n) TorusContours.stepBlockFrame_period_one _
theorem readAtLevel_translate_fine (v : Fin 4 → ℤ) (W : TorusField (n * ℓ.side)) :
    readAtLevel (stepBlockFrame ℓ.side n) 0 (TorusFields.translate (siteOfInt (scaleCoords ℓ.side v)) W) =
      translateFine (F := stepBlockFrame ℓ.side n) v (readAtLevel (stepBlockFrame ℓ.side n) 0 W) := by
  funext x i
  exact congrArg (fun z => W z i) (toTorusSite_add_fine v x).symm
theorem readAtLevel_translate_coarse (v : Fin 4 → ℤ) (V : TorusField n) :
    readAtLevel (stepBlockFrame ℓ.side n) 1 (TorusFields.translate (siteOfInt v) V) =
      translateCoarse (F := stepBlockFrame ℓ.side n) v (readAtLevel (stepBlockFrame ℓ.side n) 1 V) := by
  funext y i
  exact congrArg (fun z => V z i) (toTorusSite_add_coarse v y).symm
theorem stepBlockFrame_extent_ge (hn : 2 ≤ n) : ∀ i, 2 ≤ (stepBlockFrame ℓ.side n).extent i := fun _ => hn
theorem chartCoord_translate (hL : Odd ℓ.side) (hn : 2 ≤ n) (v : Fin 4 → ℤ) (V : TorusField n)
    (W : TorusField (n * ℓ.side)) (x : TorusSite (n * ℓ.side)) (i : Fin 4) :
    chartCoord ℓ (TorusFields.translate (siteOfInt v) V)
        (TorusFields.translate (siteOfInt (scaleCoords ℓ.side v)) W) (x, i) =
      chartCoord ℓ V W (x + siteOfInt (scaleCoords ℓ.side v), i) := by
  unfold chartCoord
  rw [readAtLevel_translate_fine, readAtLevel_translate_coarse]
  refine (bondCoordinate_translate (F := stepBlockFrame ℓ.side n) v hL (stepBlockFrame_extent_ge hn) _ _ _ _ i).trans ?_
  exact congrArg (fun s : (stepBlockFrame ℓ.side n).Site (stepBlockFrame ℓ.side n).depth =>
    bondCoordinate (F := stepBlockFrame ℓ.side n) 1
      (readAtLevel (stepBlockFrame ℓ.side n) 1 V) (readAtLevel (stepBlockFrame ℓ.side n) 0 W) (s, i))
    (torusSiteInFrame_add_scale v x).symm
theorem add_mem_chartBonds_iff (hL : Odd ℓ.side) (hn : 2 ≤ n) (v : Fin 4 → ℤ) (x : TorusSite (n * ℓ.side))
    (i : Fin 4) :
    (x + siteOfInt (scaleCoords ℓ.side v), i) ∈ chartBonds ℓ.side n ↔ (x, i) ∈ chartBonds ℓ.side n := by
  classical
  simp only [chartBonds, Finset.mem_filter, Finset.mem_univ, true_and]
  show ¬ IsAxialTreeBond (F := stepBlockFrame ℓ.side n)
      (torusSiteInFrame (stepBlockFrame ℓ.side n) (stepBlockFrame ℓ.side n).depth
        (x + siteOfInt (scaleCoords ℓ.side v)), i) ↔
    ¬ IsAxialTreeBond (F := stepBlockFrame ℓ.side n)
      (torusSiteInFrame (stepBlockFrame ℓ.side n) (stepBlockFrame ℓ.side n).depth x, i)
  rw [torusSiteInFrame_add_scale]
  exact not_congr (isAxialTreeBond_add_translation (F := stepBlockFrame ℓ.side n) v hL
    (stepBlockFrame_extent_ge hn) _ i)
end StepFrame
section Weights
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem markedBonds_translateSet (hL : Odd R.params.side) (hn : 2 ≤ n) (v : Fin 4 → ℤ) (C : Finset (TorusSite n)) :
    markedBonds R (translateSet (siteOfInt v) C) =
      translateBonds (siteOfInt (scaleCoords R.params.side v)) (markedBonds R C) := by
  classical
  ext ⟨x, i⟩
  rw [mem_translateBonds]
  simp only [markedBonds, Finset.mem_filter, mem_translateSet]
  rw [add_mem_chartBonds_iff hL hn, parentBlock_add_scale]
theorem bondMark_translate (hL : Odd R.params.side) (hn : 2 ≤ n) (v : Fin 4 → ℤ) (V : TorusField n)
    (W : TorusField (n * R.params.side)) (x : TorusSite (n * R.params.side)) (i : Fin 4)
    (h : frameCoord R.params R.anchorRadius R.depth R.frameReach (TorusFields.translate (siteOfInt v) V) (x, i) =
      frameCoord R.params R.anchorRadius R.depth R.frameReach V
        (x + siteOfInt (scaleCoords R.params.side v), i)) :
    bondMark R (TorusFields.translate (siteOfInt v) V)
        (TorusFields.translate (siteOfInt (scaleCoords R.params.side v)) W) (x, i) =
      bondMark R V W (x + siteOfInt (scaleCoords R.params.side v), i) := by
  unfold bondMark
  rw [chartCoord_translate hL hn, h]
theorem markProduct_translate (hL : Odd R.params.side) (hn : 2 ≤ n) (v : Fin 4 → ℤ) (C : Finset (TorusSite n))
    (V : TorusField n) (W : TorusField (n * R.params.side)) (bad : Finset (TorusBond (n * R.params.side)))
    (hfr : ∀ c ∈ markedBonds R C, frameCoord R.params R.anchorRadius R.depth R.frameReach
      (TorusFields.translate (siteOfInt v) V) (c.1 - siteOfInt (scaleCoords R.params.side v), c.2) =
        frameCoord R.params R.anchorRadius R.depth R.frameReach V c) :
    markProduct R (translateSet (siteOfInt v) C) (TorusFields.translate (siteOfInt v) V)
        (TorusFields.translate (siteOfInt (scaleCoords R.params.side v)) W)
        (translateBonds (siteOfInt (scaleCoords R.params.side v)) bad) = markProduct R C V W bad := by
  classical
  unfold markProduct
  rw [markedBonds_translateSet hL hn]
  refine Finset.prod_nbij' (fun c => (c.1 + siteOfInt (scaleCoords R.params.side v), c.2))
    (fun c => (c.1 - siteOfInt (scaleCoords R.params.side v), c.2))
    (fun c hc => mem_translateBonds.mp hc) (fun c hc => mem_translateBonds.mpr (by simpa using hc))
    (fun c _ => by simp) (fun c _ => by simp) ?_
  rintro ⟨x, i⟩ hc
  have hc' : (x + siteOfInt (scaleCoords R.params.side v), i) ∈ markedBonds R C := mem_translateBonds.mp hc
  have h := hfr _ hc'
  simp only [add_sub_cancel_right] at h
  have hm := bondMark_translate (R := R) hL hn v V W x i h
  simp only [mem_translateBonds]
  rw [hm]
theorem stepWeight_translate (hR : R.IsWellPosed) (hK : BaseTranslations.TranslationPreservesBaseKernel)
    (hn : R.params.n₀ ≤ n) (v : Fin 4 → ℤ) (C : Finset (TorusSite n)) (V : TorusField n)
    (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
    (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n)
    (hull : IsHullState R.params R.range W Yt)
    (hfr : ∀ c ∈ markedBonds R C, frameCoord R.params R.anchorRadius R.depth R.frameReach
      (TorusFields.translate (siteOfInt v) V) (c.1 - siteOfInt (scaleCoords R.params.side v), c.2) =
        frameCoord R.params R.anchorRadius R.depth R.frameReach V c) :
    stepWeight R (translateSet (siteOfInt v) C) (TorusFields.translate (siteOfInt v) V)
        (TorusFields.translate (siteOfInt (scaleCoords R.params.side v)) W)
        (translateSet (siteOfInt (scaleCoords R.params.side v)) Yt)
        (translateLabel (siteOfInt (scaleCoords R.params.side v)) Yt ωt)
        (translateBonds (siteOfInt (scaleCoords R.params.side v)) bad) (translateBases v b) =
      stepWeight R C V W Yt ωt bad b := by
  classical
  have hfit := hR.admissible
  have hn2 : 2 ≤ n := by
    have := hfit.n₀_ge
    omega
  obtain ⟨h1, h2, h3⟩ := hK R.params hfit R.coupling n hn v W V b
  have hside : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Dvd.intro_left _ rfl, by rw [mul_comm]; exact Nat.mul_le_mul_right _ hn⟩
  have hD := hR.hasExpansions.2.translation (n * R.params.side) hside W Yt ωt
    (siteOfInt (scaleCoords R.params.side v)) ⟨v, rfl⟩ hull
  unfold stepWeight
  rw [markProduct_translate hfit.L_odd hn2 v C V W bad hfr, hD]
  by_cases hb : b ∈ baseChoices R.params (fineLevelField R.params n W)
  · have e3 := h3 hb
    have e : baseLaw (R := R) (TorusFields.translate (siteOfInt (scaleCoords R.params.side v)) W)
        (translateBases v b) = baseLaw (R := R) W b := by
      unfold baseLaw
      rw [if_pos (h1.mpr hb), if_pos hb, h2]
    rw [e]
    congr 2
  · have e : baseLaw (R := R) (TorusFields.translate (siteOfInt (scaleCoords R.params.side v)) W)
        (translateBases v b) = baseLaw (R := R) W b := by
      unfold baseLaw
      rw [if_neg (fun h => hb (h1.mp h)), if_neg hb]
    have e0 : baseLaw (R := R) W b = 0 := by
      unfold baseLaw
      rw [if_neg hb]
    rw [e, e0]
    simp
end Weights
section BaseTranslation
variable {L n : ℕ} [NeZero L] [NeZero n]
theorem siteOfCoords_scaleCoords_neg (v : Fin 4 → ℤ) :
    (siteOfCoords (F := stepBlockFrame L n) 0 (scaleCoords L (-v))) =
      - siteOfCoords (F := stepBlockFrame L n) 0 (scaleCoords L v) := by
  funext i
  simp [siteOfCoords]
theorem sub_sub_eq_of_eq_neg {A : Type} [AddCommGroup A] (p X Y : A) (h : Y = -X) : p - X - Y = p := by
  rw [h]
  abel
theorem translateBases_neg_translateBases (v : Fin 4 → ℤ) (b : BaseChoice L n) :
    translateBases (-v) (translateBases v b) = b := by
  funext y
  have e : (y + siteOfCoords (stepBlockFrame L n).top (-v) + siteOfCoords (stepBlockFrame L n).top v :
      (stepBlockFrame L n).Cell) = y := by
    funext i
    simp [siteOfCoords]
  have e' := siteOfCoords_scaleCoords_neg (L := L) (n := n) v
  show b (y + siteOfCoords (stepBlockFrame L n).top (-v) + siteOfCoords (stepBlockFrame L n).top v) -
    siteOfCoords (F := stepBlockFrame L n) 0 (scaleCoords L v) -
    siteOfCoords (F := stepBlockFrame L n) 0 (scaleCoords L (-v)) = b y
  rw [e]
  exact sub_sub_eq_of_eq_neg _ _ _ e'
def translateBasesEquiv (v : Fin 4 → ℤ) : BaseChoice L n ≃ BaseChoice L n where
  toFun := translateBases v
  invFun := translateBases (-v)
  left_inv := translateBases_neg_translateBases v
  right_inv b := by simpa using translateBases_neg_translateBases (-v) b
end BaseTranslation
section StatesOfCases
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem baseOffset_translateBases (v : Fin 4 → ℤ) (b : BaseChoice R.params.side n) (y : TorusSite n) :
    baseOffset R (translateBases v b) y = baseOffset R b (y + siteOfInt v) := by
  have e1 : torusSiteInFrame (stepBlockFrame R.params.side n) (stepBlockFrame R.params.side n).top y +
        siteOfCoords (stepBlockFrame R.params.side n).top v =
      torusSiteInFrame (stepBlockFrame R.params.side n) (stepBlockFrame R.params.side n).top (y + siteOfInt v) := by
    rw [TopLevelSites.torusSiteInFrame_add (F := stepBlockFrame R.params.side n)
        (j := (stepBlockFrame R.params.side n).top) (N := n) TorusContours.stepBlockFrame_period_one,
      TopLevelSites.torusSiteInFrame_siteOfInt (F := stepBlockFrame R.params.side n)
        (j := (stepBlockFrame R.params.side n).top) (N := n) TorusContours.stepBlockFrame_period_one]
  have hb : translateBases v b
        (torusSiteInFrame (stepBlockFrame R.params.side n) (stepBlockFrame R.params.side n).top y) =
      b (torusSiteInFrame (stepBlockFrame R.params.side n) (stepBlockFrame R.params.side n).top (y + siteOfInt v)) -
        siteOfCoords (F := stepBlockFrame R.params.side n) 0 (scaleCoords R.params.side v) :=
    congrArg (fun c => b c - siteOfCoords (F := stepBlockFrame R.params.side n) 0 (scaleCoords R.params.side v)) e1
  have e2 : ∀ p : (stepBlockFrame R.params.side n).Site 0,
      toTorusSite (n * R.params.side)
          (p - siteOfCoords (F := stepBlockFrame R.params.side n) 0 (scaleCoords R.params.side v)) =
        toTorusSite (n * R.params.side) p + siteOfInt (scaleCoords R.params.side (-v)) := by
    intro p
    rw [sub_eq_add_neg, ← siteOfCoords_scaleCoords_neg]
    exact toTorusSite_add_fine (-v) p
  show siteOffset (toTorusSite (n * R.params.side) (translateBases v b
      (torusSiteInFrame (stepBlockFrame R.params.side n) (stepBlockFrame R.params.side n).top y))) =
    siteOffset (toTorusSite (n * R.params.side)
      (b (torusSiteInFrame (stepBlockFrame R.params.side n) (stepBlockFrame R.params.side n).top (y + siteOfInt v))))
  rw [hb, e2]
  exact siteOffset_add_scale _ (-v)
theorem blockConfigAt_translate (v : Fin 4 → ℤ) (C Z : Finset (TorusSite n)) (F : TorusField (n * R.params.side))
    (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
    (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n) (y : TorusSite n) :
    blockConfigAt R (translateSet (siteOfInt v) C) (translateSet (siteOfInt v) Z)
        (TorusFields.translate (siteOfInt (scaleCoords R.params.side v)) F)
        (translateSet (siteOfInt (scaleCoords R.params.side v)) Yt)
        (translateLabel (siteOfInt (scaleCoords R.params.side v)) Yt ωt)
        (translateBonds (siteOfInt (scaleCoords R.params.side v)) bad) (translateBases v b) y =
      blockConfigAt R C Z F Yt ωt bad b (y + siteOfInt v) := by
  classical
  refine blockConfig_ext ?_ ?_ ?_ ?_ ?_
  · simp only [blockConfigAt, mem_translateSet]
  · funext c
    simp only [blockConfigAt, mem_translateBonds, blockSite_add]
  · funext o
    simp only [blockConfigAt]
    by_cases h : blockSite (y + siteOfInt v) o ∈ Yt
    · have h' : blockSite y o ∈ translateSet (siteOfInt (scaleCoords R.params.side v)) Yt := by
        rw [mem_translateSet, ← blockSite_add]
        exact h
      rw [dif_pos h, dif_pos h']
      simp only [translateLabel, Sum.inr.injEq]
      congr 2
      exact (blockSite_add y o v).symm
    · have h' : blockSite y o ∉ translateSet (siteOfInt (scaleCoords R.params.side v)) Yt := by
        rw [mem_translateSet, ← blockSite_add]
        exact h
      rw [dif_neg h, dif_neg h']
  · exact baseOffset_translateBases v b y
  · funext c
    have e : parentBlock R.params.side (blockSite (L := R.params.side) y c.1 +
          TorusFields.unitStep (n * R.params.side) c.2) + siteOfInt v =
        parentBlock R.params.side (blockSite (L := R.params.side) (y + siteOfInt v) c.1 +
          TorusFields.unitStep (n * R.params.side) c.2) := by
      rw [blockSite_add, add_right_comm, parentBlock_add_scale]
    simp only [blockConfigAt, mem_translateSet, e, TorusFields.translate, blockSite_add]
theorem markAt_coarseStateOf (C : Finset (TorusSite n)) (F : TorusField (n * R.params.side))
    (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
    (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n) (y : TorusSite n) :
    (coarseStateOf R C F Yt ωt bad b).markAt y = open Classical in
      if y ∈ storedBlocks R.params.side R.range bad Yt C then
        some (blockConfigAt R C (storedBlocks R.params.side R.range bad Yt C) F Yt ωt bad b y) else none := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.markAt_coarseStateOf <;> assumption
theorem coarseStateOf_translate (v : Fin 4 → ℤ) (C : Finset (TorusSite n)) (F : TorusField (n * R.params.side))
    (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
    (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n) :
    coarseStateOf R (translateSet (siteOfInt v) C) (TorusFields.translate (siteOfInt (scaleCoords R.params.side v)) F)
        (translateSet (siteOfInt (scaleCoords R.params.side v)) Yt)
        (translateLabel (siteOfInt (scaleCoords R.params.side v)) Yt ωt)
        (translateBonds (siteOfInt (scaleCoords R.params.side v)) bad) (translateBases v b) =
      translateState (coarseStateOf R C F Yt ωt bad b) (siteOfInt v) := by
  classical
  refine coarseState_ext _ _ (coarseHull_translate R.range R.nextRange v bad Yt C) fun y => ?_
  rw [markAt_translateState, markAt_coarseStateOf, markAt_coarseStateOf, storedBlocks_translate]
  by_cases hy : y + siteOfInt v ∈ storedBlocks R.params.side R.range bad Yt C
  · have hy' : y ∈ translateSet (siteOfInt v) (storedBlocks R.params.side R.range bad Yt C) :=
      mem_translateSet.mpr hy
    rw [if_pos hy, if_pos hy', blockConfigAt_translate]
  · have hy' : y ∉ translateSet (siteOfInt v) (storedBlocks R.params.side R.range bad Yt C) :=
      fun h => hy (mem_translateSet.mp h)
    rw [if_neg hy, if_neg hy']
end StatesOfCases
section Integrals
theorem lintegral_pi_comp_equiv {ι κ X : Type} [Fintype ι] [Fintype κ] [MeasurableSpace X] (μ : Measure X)
    [SigmaFinite μ] (e : ι ≃ κ) (f : (ι → X) → ENNReal) :
    ∫⁻ a, f (fun i => a (e i)) ∂(Measure.pi fun _ : κ => μ) = ∫⁻ b, f b ∂(Measure.pi fun _ : ι => μ) := by
  let E : (κ → X) ≃ᵐ (ι → X) :=
    { toFun := fun a i => a (e i)
      invFun := fun b k => b (e.symm k)
      left_inv := fun a => by funext k; simp
      right_inv := fun b => by funext i; simp
      measurable_toFun := measurable_pi_lambda _ fun i => measurable_pi_apply _
      measurable_invFun := measurable_pi_lambda _ fun i => measurable_pi_apply _ }
  exact (measurePreserving_comp_equiv μ e).lintegral_comp_emb E.measurableEmbedding f
theorem lintegral_translate {m : ℕ} [NeZero m] (a : TorusSite m) (f : TorusField m → ENNReal) :
    ∫⁻ W, f (TorusFields.translate a W) ∂(fieldHaar m) = ∫⁻ W, f W ∂(fieldHaar m) := by
  unfold fieldHaar
  exact lintegral_pi_comp_equiv (Measure.pi fun _ : Fin 4 => haarUnit) (Equiv.addRight a) f
end Integrals
section Mass
variable {R : StepSetup} {n : ℕ} [NeZero n]
open Classical in
theorem lintegral_term_translate (hR : R.IsWellPosed) (hK : BaseTranslations.TranslationPreservesBaseKernel)
    (hn : R.params.n₀ ≤ n) (v : Fin 4 → ℤ) (C : Finset (TorusSite n)) (V : TorusField n) (q : CoarseState R n)
    (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n)
    (hfr : ∀ c ∈ markedBonds R C, frameCoord R.params R.anchorRadius R.depth R.frameReach
      (TorusFields.translate (siteOfInt v) V) (c.1 - siteOfInt (scaleCoords R.params.side v), c.2) =
        frameCoord R.params R.anchorRadius R.depth R.frameReach V c) :
    (∫⁻ W, ∫⁻ ν : q.unlabelled Yt → R.labels.Ω,
      (if IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt ∧
          coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q then
        ENNReal.ofReal (stepWeight R C V (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b) else 0)
      ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side))) =
    ∫⁻ W, ∫⁻ ν : (translateState q (siteOfInt v)).unlabelled
        (translateSet (siteOfInt (scaleCoords R.params.side v)) Yt) → R.labels.Ω,
      (if IsHullState R.params R.range ((translateState q (siteOfInt v)).fieldWithStoredLinks W)
            (translateSet (siteOfInt (scaleCoords R.params.side v)) Yt) ∧
          coarseStateOf R (translateSet (siteOfInt v) C) ((translateState q (siteOfInt v)).fieldWithStoredLinks W)
            (translateSet (siteOfInt (scaleCoords R.params.side v)) Yt)
            ((translateState q (siteOfInt v)).fillLabels (translateSet (siteOfInt (scaleCoords R.params.side v)) Yt) ν)
            (translateBonds (siteOfInt (scaleCoords R.params.side v)) bad) (translateBases v b) =
            translateState q (siteOfInt v) then
        ENNReal.ofReal (stepWeight R (translateSet (siteOfInt v) C) (TorusFields.translate (siteOfInt v) V)
          ((translateState q (siteOfInt v)).fieldWithStoredLinks W)
          (translateSet (siteOfInt (scaleCoords R.params.side v)) Yt)
          ((translateState q (siteOfInt v)).fillLabels (translateSet (siteOfInt (scaleCoords R.params.side v)) Yt) ν)
          (translateBonds (siteOfInt (scaleCoords R.params.side v)) bad) (translateBases v b)) else 0)
      ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) := by
  symm
  rw [← lintegral_translate (siteOfInt (scaleCoords R.params.side v))]
  refine lintegral_congr fun W => ?_
  rw [← lintegral_pi_comp_equiv R.labels.μ (unlabelledEquiv q v Yt)]
  refine lintegral_congr fun ν => ?_
  have hLm : R.params.side ∣ n * R.params.side := Dvd.intro_left _ rfl
  rw [fieldWithStoredLinks_translateState, fillLabels_translateState, coarseStateOf_translate,
    isHullState_translate_iff hR.admissible hLm]
  by_cases h : IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt ∧
      coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q
  · have h' : IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt ∧
        translateState (coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b) (siteOfInt v) =
          translateState q (siteOfInt v) :=
      ⟨h.1, by rw [h.2]⟩
    rw [if_pos h, if_pos h', stepWeight_translate hR hK hn v C V _ Yt _ bad b h.1 hfr]
  · have h' : ¬ (IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt ∧
        translateState (coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b) (siteOfInt v) =
          translateState q (siteOfInt v)) :=
      fun c => h ⟨c.1, translateState_injective _ c.2⟩
    rw [if_neg h, if_neg h']
theorem coarseStateMass_translate (hR : R.IsWellPosed) (hK : BaseTranslations.TranslationPreservesBaseKernel)
    (hn : R.params.n₀ ≤ n) (v : Fin 4 → ℤ) (C : Finset (TorusSite n)) (V : TorusField n) (q : CoarseState R n)
    (hfr : ∀ c ∈ markedBonds R C, frameCoord R.params R.anchorRadius R.depth R.frameReach
      (TorusFields.translate (siteOfInt v) V) (c.1 - siteOfInt (scaleCoords R.params.side v), c.2) =
        frameCoord R.params R.anchorRadius R.depth R.frameReach V c) :
    coarseStateMass R (translateSet (siteOfInt v) C) (TorusFields.translate (siteOfInt v) V)
        (translateState q (siteOfInt v)) =
      coarseStateMass R C V q := by
  classical
  have hfit := hR.admissible
  have hn2 : 2 ≤ n := by
    have := hfit.n₀_ge
    omega
  symm
  unfold coarseStateMass
  rw [markedBonds_translateSet hfit.L_odd hn2]
  refine Finset.sum_nbij' (translateBonds (siteOfInt (scaleCoords R.params.side v)))
    (translateBonds (-siteOfInt (scaleCoords R.params.side v))) ?_ ?_ ?_ ?_ ?_
  · intro B hB
    refine Finset.mem_powerset.mpr fun c hc => ?_
    exact mem_translateBonds.mpr (Finset.mem_powerset.mp hB (mem_translateBonds.mp hc))
  · intro B hB
    refine Finset.mem_powerset.mpr fun c hc => ?_
    have := mem_translateBonds.mp (Finset.mem_powerset.mp hB (mem_translateBonds.mp hc))
    simpa using this
  · exact fun B _ => translateBonds_neg_translateBonds _ B
  · exact fun B _ => translateBonds_translateBonds_neg _ B
  · intro bad _
    refine Fintype.sum_equiv (translateSetEquiv (siteOfInt (scaleCoords R.params.side v))) _ _ fun Yt => ?_
    refine Fintype.sum_equiv (translateBasesEquiv v) _ _ fun b => ?_
    exact lintegral_term_translate hR hK hn v C V q bad Yt b hfr
end Mass
end TranslationInvariance
theorem coarseWeightExpansion_translationInvariant (hK : BaseTranslations.TranslationPreservesBaseKernel)
    (hF : StepFrames.FrameCovariance) : CoarseWeightExpansionTranslationInvariant := by
  intro R hR hFit n _ hB V Y ω u hu hY
  obtain ⟨w, rfl⟩ := hu
  obtain ⟨δ, lam, σA, cg, N, hC, h2, -⟩ := hFit
  have hfits := hR.admissible
  have hLpos : 1 ≤ R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hn : R.params.n₀ ≤ n := by
    have h1 := hB.2
    exact le_trans (Nat.le_mul_of_pos_left _ hLpos) h1
  have hhull : hotCoreSites R
        (TorusFields.translate (siteOfInt (TranslationInvariance.scaleCoords R.params.side w)) V) =
      translateSet (siteOfInt (TranslationInvariance.scaleCoords R.params.side w))
        (hotCoreSites R V) := by
    unfold hotCoreSites
    rw [TranslationInvariance.torusHotSites_translate hfits hB.1, TranslationInvariance.thickening_translateSet]
  have hfit2 : StepMarks.RangesAdmissible R.range R.nextRange := by
    refine ⟨hR.range_le, hR.nextRange_ge, ?_⟩
    have h3 := hR.range_ge_side
    have h4 := hfits.L_ge
    refine (Nat.le_div_iff_mul_le (by norm_num)).mpr ?_
    calc 16 * 2 ^ 11 ≤ 2 ^ 40 * R.params.side := by nlinarith
      _ ≤ R.range := h3
  have hfr : ∀ c ∈ markedBonds R (hotCoreSites R V),
      frameCoord R.params R.anchorRadius R.depth R.frameReach
        (TorusFields.translate (siteOfInt (TranslationInvariance.scaleCoords R.params.side w)) V)
        (c.1 - siteOfInt (TranslationInvariance.scaleCoords R.params.side
          (TranslationInvariance.scaleCoords R.params.side w)), c.2) =
        frameCoord R.params R.anchorRadius R.depth R.frameReach V c := by
    intro c hc
    classical
    obtain ⟨hc1, hc2⟩ := Finset.mem_filter.mp hc
    exact (hF R.params δ lam R.anchorRadius σA cg N hfits hC h2 R.depth R.range R.nextRange n V _ _ _ hfit2
      (Or.inl ⟨hB, rfl, rfl, rfl⟩) c hc1 hc2).2 _
  have hne : n ≠ 0 := NeZero.ne n
  have key := TranslationInvariance.coarseStateMass_translate hR hK hn
    (TranslationInvariance.scaleCoords R.params.side w) (hotCoreSites R V) V ⟨Y, ω⟩ hfr
  rw [← hhull] at key
  unfold coarseWeightExpansion
  rw [dif_neg hne, dif_neg hne]
  unfold coarseStateWeight
  exact congrArg ENNReal.toReal key
end YangMills.Construction.ClusterExpansionOfAStep
end
