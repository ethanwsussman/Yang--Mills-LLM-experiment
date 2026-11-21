import YangMills.Construction.ClusterExpansionOfAStep.TranslationsCarryTheKernelAtBasesProof
import YangMills.Construction.ClusterExpansionOfAStep.IsometriesCarryTheKernelProof
import YangMills.Construction.ResponseInTheExpansion.IsometriesCarryTheScores
import YangMills.Construction.ResponseInTheExpansion.TheScoreOfABond
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace TorusSymmetry
open TorusFields TorusLumps StepSettings StepCosts TorusContours BlockAverages LumpContours
def linearPart (g : TorusIsometry) (z : Fin 4 → ℤ) : Fin 4 → ℤ := fun i => g.axisSign i * z (g.axisPerm i)
theorem axisSign_mul_self (g : TorusIsometry) (i : Fin 4) : g.axisSign i * g.axisSign i = 1 := by
  rcases g.axisSign_unit i with h | h <;> simp [h]
theorem linearPart_add (g : TorusIsometry) (a b : Fin 4 → ℤ) :
    linearPart g (a + b) = linearPart g a + linearPart g b := by apply _root_.YangMills.Construction.TranslationKernel.linearPart_add <;> assumption
theorem linearPart_neg (g : TorusIsometry) (a : Fin 4 → ℤ) : linearPart g (-a) = - linearPart g a := by apply _root_.YangMills.Construction.TranslationKernel.linearPart_neg <;> assumption
theorem linearPart_single (g : TorusIsometry) (k : Fin 4) (c : ℤ) :
    linearPart g (Pi.single k c) = Pi.single (g.imageAxis k) (g.axisSign (g.imageAxis k) * c) := by apply _root_.YangMills.Construction.TranslationKernel.linearPart_single <;> assumption
def linearPartInv (g : TorusIsometry) (z : Fin 4 → ℤ) : Fin 4 → ℤ :=
  fun q => g.axisSign (g.imageAxis q) * z (g.imageAxis q)
theorem linearPart_linearPartInv (g : TorusIsometry) (z : Fin 4 → ℤ) : linearPart g (linearPartInv g z) = z := by apply _root_.YangMills.Construction.TranslationKernel.linearPart_linearPartInv <;> assumption
theorem linearPartInv_linearPart (g : TorusIsometry) (z : Fin 4 → ℤ) : linearPartInv g (linearPart g z) = z := by apply _root_.YangMills.Construction.TranslationKernel.linearPartInv_linearPart <;> assumption
theorem linearPart_mem_centredCube (g : TorusIsometry) {M : ℕ} {z : Fin 4 → ℤ} (hz : z ∈ centredCube M) :
    linearPart g z ∈ centredCube M := by apply _root_.YangMills.Construction.TranslationKernel.linearPart_mem_centredCube <;> assumption
theorem linearPartInv_mem_centredCube (g : TorusIsometry) {M : ℕ} {z : Fin 4 → ℤ} (hz : z ∈ centredCube M) :
    linearPartInv g z ∈ centredCube M := by apply _root_.YangMills.Construction.TranslationKernel.linearPartInv_mem_centredCube <;> assumption
variable {F : BlockFrame} {j m : ℕ}
def siteMap (g : TorusIsometry) (u : Fin 4 → ℤ) (x : F.Site j) : F.Site j :=
  siteOfCoords j (linearPart g (siteCoords x) + u)
variable [∀ j i, NeZero (F.period j i)]
theorem intCast_siteCoords_siteOfCoords (hp : ∀ i, F.period j i = m) (z : Fin 4 → ℤ) (k : Fin 4) :
    ((siteCoords (siteOfCoords j z : F.Site j) k : ℤ) : ZMod m) = (z k : ZMod m) := by apply _root_.YangMills.Construction.TranslationKernel.intCast_siteCoords_siteOfCoords <;> assumption
theorem siteOfCoords_congr (hp : ∀ i, F.period j i = m) {a b : Fin 4 → ℤ}
    (h : ∀ i, (a i : ZMod m) = (b i : ZMod m)) :
    (siteOfCoords j a : F.Site j) = siteOfCoords j b := by apply _root_.YangMills.Construction.TranslationKernel.siteOfCoords_congr <;> assumption
theorem siteOfCoords_eq_iff (hp : ∀ i, F.period j i = m) {a b : Fin 4 → ℤ} :
    (siteOfCoords j a : F.Site j) = siteOfCoords j b ↔ ∀ i, (a i : ZMod m) = (b i : ZMod m) := by apply _root_.YangMills.Construction.TranslationKernel.siteOfCoords_eq_iff <;> assumption
theorem siteMap_siteOfCoords (hp : ∀ i, F.period j i = m) (g : TorusIsometry) (u z : Fin 4 → ℤ) :
    (siteMap g u (siteOfCoords j z : F.Site j) : F.Site j) = siteOfCoords j (linearPart g z + u) := by apply _root_.YangMills.Construction.TranslationKernel.siteMap_siteOfCoords <;> assumption
theorem siteMap_add (hp : ∀ i, F.period j i = m) (g : TorusIsometry) (u d : Fin 4 → ℤ) (x : F.Site j) :
    (siteMap g u (x + siteOfCoords j d) : F.Site j) = siteMap g u x + siteOfCoords j (linearPart g d) := by apply _root_.YangMills.Construction.TranslationKernel.siteMap_add <;> assumption
theorem siteMap_injective (hp : ∀ i, F.period j i = m) (g : TorusIsometry) (u : Fin 4 → ℤ) :
    Function.Injective (siteMap g u : F.Site j → F.Site j) := by apply _root_.YangMills.Construction.TranslationKernel.siteMap_injective <;> assumption
def siteMapEquiv (hp : ∀ i, F.period j i = m) (g : TorusIsometry) (u : Fin 4 → ℤ) : F.Site j ≃ F.Site j :=
  Equiv.ofBijective (siteMap g u) (Finite.injective_iff_bijective.mp (siteMap_injective hp g u))
theorem siteMapEquiv_apply (hp : ∀ i, F.period j i = m) (g : TorusIsometry) (u : Fin 4 → ℤ) (x : F.Site j) :
    siteMapEquiv hp g u x = siteMap g u x := rfl
theorem toTorusSite_siteMap (g : TorusIsometry) (u : Fin 4 → ℤ) (hp : ∀ i, F.period j i = m) (x : F.Site j) :
    (toTorusSite m (siteMap g u x : F.Site j) : TorusSite m) =
      TorusIsometry.mapSite ⟨g.axisPerm, g.axisSign, u, g.axisSign_unit⟩ (toTorusSite m x) := by apply _root_.YangMills.Construction.TranslationKernel.toTorusSite_siteMap <;> assumption
def mapPathStep (g : TorusIsometry) (st : PathStep) : PathStep :=
  (g.imageAxis st.1, if g.axisSign (g.imageAxis st.1) = 1 then st.2 else !st.2)
theorem stepDisplacement_eq (st : PathStep) :
    (stepDisplacement j st : F.Site j) = siteOfCoords j (Pi.single st.1 (if st.2 then 1 else -1)) := by apply _root_.YangMills.Construction.TranslationKernel.stepDisplacement_eq <;> assumption
theorem siteMap_add_stepDisplacement (hp : ∀ i, F.period j i = m) (g : TorusIsometry) (u : Fin 4 → ℤ)
    (x : F.Site j) (st : PathStep) :
    (siteMap g u (x + stepDisplacement j st) : F.Site j) = siteMap g u x + stepDisplacement j (mapPathStep g st) := by apply _root_.YangMills.Construction.TranslationKernel.siteMap_add_stepDisplacement <;> assumption
def LevelFieldsTransported (g : TorusIsometry) (u : Fin 4 → ℤ) (X X' : F.GaugeField j) : Prop :=
  ∀ x k, if g.axisSign (g.imageAxis k) = 1 then X' (siteMap g u x) (g.imageAxis k) = X x k
    else (X' (siteMap g u x - BlockAverages.unitStep j (g.imageAxis k)) (g.imageAxis k))⁻¹ = X x k
theorem linkValue_mapPathStep (hp : ∀ i, F.period j i = m) {g : TorusIsometry} {u : Fin 4 → ℤ}
    {X X' : F.GaugeField j} (h : LevelFieldsTransported g u X X') (x : F.Site j) (st : PathStep) :
    linkValue X' (siteMap g u x) (mapPathStep g st) = linkValue X x st := by
  obtain ⟨k, f⟩ := st
  rcases g.axisSign_unit (g.imageAxis k) with hs | hs
  · cases f
    · have h1 := h (x - BlockAverages.unitStep j k) k
      rw [if_pos hs] at h1
      have h2 := siteMap_add_stepDisplacement hp g u (x - BlockAverages.unitStep j k) (k, true)
      have e : x - BlockAverages.unitStep j k + stepDisplacement j (k, true) = x := by simp [stepDisplacement]
      rw [e] at h2
      simp only [mapPathStep, hs, if_true, stepDisplacement] at h2
      simp only [mapPathStep, hs, if_true, linkValue, Bool.false_eq_true, if_false]
      rw [h2] at *
      simp only [Bool.true_eq_false, if_true, add_sub_cancel_right]
      rw [h1]
    · have h1 := h x k
      rw [if_pos hs] at h1
      simp [mapPathStep, hs, linkValue, h1]
  · have hne : g.axisSign (g.imageAxis k) ≠ 1 := by rw [hs]; omega
    cases f
    · have h1 := h (x - BlockAverages.unitStep j k) k
      rw [if_neg hne] at h1
      have h2 := siteMap_add_stepDisplacement hp g u (x - BlockAverages.unitStep j k) (k, true)
      have e : x - BlockAverages.unitStep j k + stepDisplacement j (k, true) = x := by simp [stepDisplacement]
      rw [e] at h2
      simp only [mapPathStep, hne, if_false, stepDisplacement, Bool.not_true, Bool.false_eq_true] at h2
      have e2 : siteMap g u (x - BlockAverages.unitStep j k) - BlockAverages.unitStep j (g.imageAxis k) =
          siteMap g u x := by
        rw [h2]
        abel
      rw [e2] at h1
      simp only [mapPathStep, hne, if_false, linkValue, Bool.not_false, if_true, Bool.false_eq_true]
      rw [← h1, inv_inv]
    · have h1 := h x k
      rw [if_neg hne] at h1
      simp only [mapPathStep, hne, if_false, linkValue, Bool.not_true, Bool.false_eq_true, if_true]
      exact h1
theorem pathHolonomy_map (hp : ∀ i, F.period j i = m) {g : TorusIsometry} {u : Fin 4 → ℤ}
    {X X' : F.GaugeField j} (h : LevelFieldsTransported g u X X') (x : F.Site j) (l : List PathStep) :
    pathHolonomy X' (siteMap g u x) (l.map (mapPathStep g)) = pathHolonomy X x l := by
  induction l generalizing x with
  | nil => rfl
  | cons st r ih =>
    simp only [List.map_cons, pathHolonomy]
    rw [linkValue_mapPathStep hp h, ← siteMap_add_stepDisplacement hp, ih]
theorem pathSites_map_siteMap (hp : ∀ i, F.period j i = m) (g : TorusIsometry) (u : Fin 4 → ℤ) (x : F.Site j)
    (l : List PathStep) :
    pathSites (siteMap g u x) (l.map (mapPathStep g)) = (pathSites x l).map (siteMap g u) := by apply _root_.YangMills.Construction.TranslationKernel.pathSites_map <;> assumption
theorem axisPath_map (g : TorusIsometry) (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) :
    (axisPath h π).map (mapPathStep g) = axisPath (linearPart g h) (π.trans g.axisPerm.symm) := by apply _root_.YangMills.Construction.TranslationKernel.axisPath_map <;> assumption
section Geometry
theorem supDist_eq (hp : ∀ i, F.period j i = m) (x y : F.Site j) :
    supDist x y = Finset.univ.sup fun i =>
      ((((siteCoords x i - siteCoords y i : ℤ) : ZMod m)).valMinAbs).natAbs := by apply _root_.YangMills.Construction.TranslationKernel.supDist_eq <;> assumption
theorem supDist_siteMap (hp : ∀ i, F.period j i = m) (g : TorusIsometry) (u : Fin 4 → ℤ) (x y : F.Site j) :
    supDist (siteMap g u x : F.Site j) (siteMap g u y) = supDist x y := by apply _root_.YangMills.Construction.TranslationKernel.supDist_siteMap <;> assumption
def imageBoxLower (g : TorusIsometry) (u lo hi : Fin 4 → ℤ) : Fin 4 → ℤ :=
  fun i => if g.axisSign i = 1 then lo (g.axisPerm i) + u i else - hi (g.axisPerm i) + u i
def imageBoxUpper (g : TorusIsometry) (u lo hi : Fin 4 → ℤ) : Fin 4 → ℤ :=
  fun i => if g.axisSign i = 1 then hi (g.axisPerm i) + u i else - lo (g.axisPerm i) + u i
theorem image_siteMap_boxSites (hp : ∀ i, F.period j i = m) (g : TorusIsometry) (u lo hi : Fin 4 → ℤ) :
    (boxSites j lo hi : Finset (F.Site j)).image (siteMap g u) =
      boxSites j (imageBoxLower g u lo hi) (imageBoxUpper g u lo hi) := by apply _root_.YangMills.Construction.TranslationKernel.image_boxSites <;> assumption
theorem isSmallBox_image (hp : ∀ i, F.period j i = m) (g : TorusIsometry) (u : Fin 4 → ℤ)
    {B : Finset (F.Site j)} (hB : IsSmallBox F B) : IsSmallBox F (B.image (siteMap g u)) := by apply _root_.YangMills.Construction.TranslationKernel.isSmallBox_image <;> assumption
theorem isSmallBox_image_symm (hp : ∀ i, F.period j i = m) (g : TorusIsometry) (u : Fin 4 → ℤ)
    {B : Finset (F.Site j)} (hB : IsSmallBox F B) : IsSmallBox F (B.image (siteMapEquiv hp g u).symm) := by
  obtain ⟨lo, hi, h, rfl⟩ := hB
  let lo₂ : Fin 4 → ℤ := fun q => if g.axisSign (g.imageAxis q) = 1 then lo (g.imageAxis q) - u (g.imageAxis q)
    else -(hi (g.imageAxis q) - u (g.imageAxis q))
  let hi₂ : Fin 4 → ℤ := fun q => if g.axisSign (g.imageAxis q) = 1 then hi (g.imageAxis q) - u (g.imageAxis q)
    else -(lo (g.imageAxis q) - u (g.imageAxis q))
  have hdp : ∀ i, g.imageAxis (g.axisPerm i) = i := fun i => by simp [TorusIsometry.imageAxis]
  have e1 : imageBoxLower g u lo₂ hi₂ = lo := by
    funext i
    rcases g.axisSign_unit i with hs | hs
    · simp [imageBoxLower, lo₂, hdp, hs]
    · have hne : (-1 : ℤ) ≠ 1 := by omega
      simp [imageBoxLower, hi₂, hdp, hs]
  have e2 : imageBoxUpper g u lo₂ hi₂ = hi := by
    funext i
    rcases g.axisSign_unit i with hs | hs
    · simp [imageBoxUpper, hi₂, hdp, hs]
    · have hne : (-1 : ℤ) ≠ 1 := by omega
      simp [imageBoxUpper, lo₂, hdp, hs]
  have e3 := image_siteMap_boxSites (F := F) hp g u lo₂ hi₂
  rw [e1, e2] at e3
  refine ⟨lo₂, hi₂, fun q => ?_, ?_⟩
  · have := h (g.imageAxis q)
    rcases g.axisSign_unit (g.imageAxis q) with hs | hs
    · simp only [lo₂, hi₂, hs, if_true]
      omega
    · have hne : (-1 : ℤ) ≠ 1 := by omega
      simp only [lo₂, hi₂, hs, hne, if_false]
      omega
  · rw [← e3]
    ext x
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      have : (siteMapEquiv hp g u).symm (siteMap g u y) = y := (siteMapEquiv hp g u).symm_apply_apply y
      rwa [this]
    · intro hx
      exact ⟨siteMap g u x, ⟨x, hx, rfl⟩, (siteMapEquiv hp g u).symm_apply_apply x⟩
end Geometry
section Cover
variable {e : F.Site j ≃ F.Site j}
omit [∀ j i, NeZero (F.period j i)] in
theorem mergedBoxes_image (hbox : ∀ B : Finset (F.Site j), IsSmallBox F B → IsSmallBox F (B.image e))
    (hbox' : ∀ B : Finset (F.Site j), IsSmallBox F B → IsSmallBox F (B.image e.symm))
    (hd : ∀ x y : F.Site j, supDist (e x) (e y) = supDist x y) (seeds : Finset (Finset (F.Site j))) :
    mergedBoxes (seeds.image (Finset.image e)) = (mergedBoxes seeds).image (Finset.image e) := by apply _root_.YangMills.Construction.TranslationKernel.mergedBoxes_image <;> assumption
end Cover
section Lumps
variable {L : ℕ}
theorem offsetFromCentre_neg (hL : 0 < L) (hodd : Odd L) (c : ℤ) :
    offsetFromCentre L (-c) = - offsetFromCentre L c := by apply _root_.YangMills.Construction.TranslationKernel.offsetFromCentre_neg <;> assumption
def stripEnd (g : LumpGrid L) (c : ℤ) : ℤ := c - offsetFromCentre L c + g.upper (offsetFromCentre L c)
theorem stripEnd_add_dvd (hL : 0 < L) (hodd : Odd L) (g : LumpGrid L) (c b : ℤ) (hb : (L : ℤ) ∣ b) :
    stripEnd g (c + b) = stripEnd g c + b := by apply _root_.YangMills.Construction.TranslationKernel.stripEnd_add_dvd <;> assumption
theorem stripStart_neg (hL : 0 < L) (hodd : Odd L) (g : LumpGrid L) (c : ℤ) :
    stripStart g (-c) = - stripEnd g c := by apply _root_.YangMills.Construction.TranslationKernel.stripStart_neg <;> assumption
theorem stripEnd_neg (hL : 0 < L) (hodd : Odd L) (g : LumpGrid L) (c : ℤ) :
    stripEnd g (-c) = - stripStart g c := by apply _root_.YangMills.Construction.TranslationKernel.stripEnd_neg <;> assumption
theorem boxSites_add_period (hp : ∀ i, F.period j i = m) (lo hi k : Fin 4 → ℤ) :
    (boxSites j (fun i => lo i + m * k i) (fun i => hi i + m * k i) : Finset (F.Site j)) = boxSites j lo hi := by apply _root_.YangMills.Construction.TranslationKernel.boxSites_add_period <;> assumption
theorem lumpOf_eq (g : LumpGrid L) (x : F.Site j) :
    lumpOf g x = boxSites j (fun i => stripStart g (siteCoords x i)) (fun i => stripEnd g (siteCoords x i)) := rfl
theorem lumpOf_siteMap (hL : 0 < L) (hodd : Odd L) (hp : ∀ i, F.period j i = m) (hm : (L : ℤ) ∣ m)
    (G : TorusIsometry) (u : Fin 4 → ℤ) (hu : ∀ i, (L : ℤ) ∣ u i) (g : LumpGrid L) (x : F.Site j) :
    lumpOf g (siteMap G u x : F.Site j) = (lumpOf g x).image (siteMap G u) := by apply _root_.YangMills.Construction.TranslationKernel.lumpOf_siteMap <;> assumption
end Lumps
section Paths
omit [∀ j i, NeZero (F.period j i)] in
theorem pathHolonomy_append (X : F.GaugeField j) (x : F.Site j) (l l' : List PathStep) :
    pathHolonomy X x (l ++ l') = pathHolonomy X x l * pathHolonomy X (pathEndpoint x l) l' := by
  induction l generalizing x with
  | nil => simp [pathHolonomy, pathEndpoint]
  | cons st r ih => simp [pathHolonomy, pathEndpoint, ih, mul_assoc]
omit [∀ j i, NeZero (F.period j i)] in
theorem linkValue_flip (X : F.GaugeField j) (x : F.Site j) (st : PathStep) :
    linkValue X (x + stepDisplacement j st) (st.1, !st.2) = (linkValue X x st)⁻¹ := by apply _root_.YangMills.Construction.GaugeFixing.linkValue_reverse <;> assumption
omit [∀ j i, NeZero (F.period j i)] in
theorem pathHolonomy_reversePath (X : F.GaugeField j) (x : F.Site j) (l : List PathStep) :
    pathHolonomy X (pathEndpoint x l) (reversePath l) = (pathHolonomy X x l)⁻¹ := by
  induction l generalizing x with
  | nil => simp [pathHolonomy, pathEndpoint, reversePath]
  | cons st r ih =>
    have e : reversePath (st :: r) = reversePath r ++ [(st.1, !st.2)] := by
      simp [reversePath]
    have h2 := pathEndpoint_reversePath (x + stepDisplacement j st) r
    rw [e, pathHolonomy_append, pathEndpoint, ih, h2]
    simp only [pathHolonomy, mul_one, linkValue_flip, mul_inv_rev]
omit [∀ j i, NeZero (F.period j i)] in
theorem reversePath_append (l l' : List PathStep) :
    reversePath (l ++ l') = reversePath l' ++ reversePath l := by
  simp [reversePath]
omit [∀ j i, NeZero (F.period j i)] in
theorem reversePath_reversePath (l : List PathStep) : reversePath (reversePath l) = l := by
  simp [reversePath, List.map_reverse, Function.comp_def]
omit [∀ j i, NeZero (F.period j i)] in
theorem reversePath_replicate (a : ℕ) (st : PathStep) :
    reversePath (List.replicate a st) = List.replicate a (st.1, !st.2) := by
  simp [reversePath]
omit [∀ j i, NeZero (F.period j i)] in
theorem reversePath_map (g : TorusIsometry) (l : List PathStep) :
    (reversePath l).map (mapPathStep g) = reversePath (l.map (mapPathStep g)) := by apply _root_.YangMills.Construction.TranslationKernel.reversePath_map <;> assumption
omit [∀ j i, NeZero (F.period j i)] in
theorem mem_pathSites_reversePath (x : F.Site j) (l : List PathStep) (z : F.Site j) :
    z ∈ pathSites (pathEndpoint x l) (reversePath l) ↔ z ∈ pathSites x l := by apply _root_.YangMills.Construction.TranslationKernel.mem_pathSites_reversePath <;> assumption
end Paths
section Contour
variable {m₀ m₁ : ℕ}
def liftedOffset (L : ℕ) (g : TorusIsometry) : Fin 4 → ℤ := fun i => (L : ℤ) * g.offset i
abbrev fineMap (g : TorusIsometry) (x : F.Site F.depth) : F.Site F.depth := siteMap g (liftedOffset F.blockSide g) x
abbrev cellMap (g : TorusIsometry) (y : F.Cell) : F.Cell := siteMap g g.offset y
theorem fineMap_cellCentre (hp₀ : ∀ i, F.period F.depth i = m₀) (g : TorusIsometry) (y : F.Cell) :
    fineMap g (cellCentre F.depth y : F.Site F.depth) = cellCentre F.depth (cellMap g y) := by apply _root_.YangMills.Construction.TranslationKernel.fineMap_cellCentre <;> assumption
theorem fineMap_siteAtOffset (hp₀ : ∀ i, F.period F.depth i = m₀) (g : TorusIsometry) (y : F.Cell)
    (z : Fin 4 → ℤ) :
    fineMap g (siteAtOffset y z : F.Site F.depth) = siteAtOffset (cellMap g y) (linearPart g z) := by apply _root_.YangMills.Construction.TranslationKernel.fineMap_siteAtOffset <;> assumption
def imageBases (hp₁ : ∀ i, F.period F.top i = m₁) (g : TorusIsometry) (b : F.Cell → F.Site F.depth) :
    F.Cell → F.Site F.depth :=
  fun y => fineMap g (b ((siteMapEquiv hp₁ g g.offset).symm y))
theorem imageBases_cellMap (hp₁ : ∀ i, F.period F.top i = m₁) (g : TorusIsometry)
    (b : F.Cell → F.Site F.depth) (y : F.Cell) :
    imageBases hp₁ g b (cellMap g y) = fineMap g (b y) := by
  have : (siteMapEquiv hp₁ g g.offset).symm (cellMap g y) = y := (siteMapEquiv hp₁ g g.offset).symm_apply_apply y
  rw [imageBases, this]
theorem axisPath_minimalOffset_map (hp₀ : ∀ i, F.period F.depth i = m₀) (g : TorusIsometry)
    {x : F.Site F.depth} {y : F.Cell} {z ξ : Fin 4 → ℤ} (hx : x = siteAtOffset y z)
    (hz : z ∈ centredCube F.blockSide) (hξ : ξ ∈ centredCube F.blockSide)
    (hM : 2 * (F.blockSide : ℤ) ≤ m₀) (π : Equiv.Perm (Fin 4)) :
    (axisPath (minimalOffset x (cellCentre F.depth y + siteOfCoords F.depth ξ)) π).map (mapPathStep g) =
      axisPath (minimalOffset (fineMap g x) (cellCentre F.depth (cellMap g y) + siteOfCoords F.depth (linearPart g ξ)))
        (π.trans g.axisPerm.symm) := by apply _root_.YangMills.Construction.TranslationKernel.axisPath_image <;> assumption
def imageBond (g : TorusIsometry) (c : F.Cell × Fin 4) : F.Cell × Fin 4 :=
  (if g.axisSign (g.imageAxis c.2) = 1 then cellMap g c.1
    else cellMap g c.1 - BlockAverages.unitStep F.top (g.imageAxis c.2), g.imageAxis c.2)
theorem imageBond_of_axisSign_eq_one (hp₁ : ∀ i, F.period F.top i = m₁) (g : TorusIsometry)
    (c : F.Cell × Fin 4) (hs : g.axisSign (g.imageAxis c.2) = 1) :
    (imageBond g c).1 = cellMap g c.1 ∧
      (imageBond g c).1 + BlockAverages.unitStep F.top (imageBond g c).2 =
        cellMap g (c.1 + BlockAverages.unitStep F.top c.2) := by apply _root_.YangMills.Construction.TranslationKernel.imageBond_of_pos <;> assumption
theorem imageBond_of_axisSign_eq_neg_one (hp₁ : ∀ i, F.period F.top i = m₁) (g : TorusIsometry)
    (c : F.Cell × Fin 4) (hs : g.axisSign (g.imageAxis c.2) = -1) :
    (imageBond g c).1 = cellMap g (c.1 + BlockAverages.unitStep F.top c.2) ∧
      (imageBond g c).1 + BlockAverages.unitStep F.top (imageBond g c).2 = cellMap g c.1 := by apply _root_.YangMills.Construction.TranslationKernel.imageBond_of_neg <;> assumption
variable (hp₀ : ∀ i, F.period F.depth i = m₀) (hp₁ : ∀ i, F.period F.top i = m₁)
include hp₀ hp₁ in
theorem contourPath_map_of_pos (g : TorusIsometry) {b : F.Cell → F.Site F.depth}
    (hb : ∀ y, ∃ z ∈ centredCube F.blockSide, b y = siteAtOffset y z)
    (hM : 2 * (F.blockSide : ℤ) ≤ m₀) (c : F.Cell × Fin 4) (hs : g.axisSign (g.imageAxis c.2) = 1)
    {ξ : Fin 4 → ℤ} (hξ : ξ ∈ centredCube F.blockSide) (π : Equiv.Perm (Fin 4)) :
    (contourPath b c ξ π).map (mapPathStep g) =
      contourPath (imageBases hp₁ g b) (imageBond g c) (linearPart g ξ) (π.trans g.axisPerm.symm) := by
  obtain ⟨h1, h2⟩ := imageBond_of_axisSign_eq_one hp₁ g c hs
  obtain ⟨z₁, hz₁, e₁⟩ := hb c.1
  obtain ⟨z₂, hz₂, e₂⟩ := hb (c.1 + BlockAverages.unitStep F.top c.2)
  unfold contourPath
  rw [h2, h1, imageBases_cellMap, imageBases_cellMap, List.map_append, List.map_append, reversePath_map,
    axisPath_minimalOffset_map hp₀ g e₁ hz₁ hξ hM, axisPath_minimalOffset_map hp₀ g e₂ hz₂ hξ hM,
    List.map_replicate]
  have : mapPathStep g (c.2, true) = ((imageBond g c).2, true) := by
    simp [mapPathStep, hs, imageBond]
  rw [this]
include hp₀ hp₁ in
theorem contourPath_map_of_neg (g : TorusIsometry) {b : F.Cell → F.Site F.depth}
    (hb : ∀ y, ∃ z ∈ centredCube F.blockSide, b y = siteAtOffset y z)
    (hM : 2 * (F.blockSide : ℤ) ≤ m₀) (c : F.Cell × Fin 4) (hs : g.axisSign (g.imageAxis c.2) = -1)
    {ξ : Fin 4 → ℤ} (hξ : ξ ∈ centredCube F.blockSide) (π : Equiv.Perm (Fin 4)) :
    (contourPath b c ξ π).map (mapPathStep g) =
      reversePath (contourPath (imageBases hp₁ g b) (imageBond g c) (linearPart g ξ) (π.trans g.axisPerm.symm)) := by
  obtain ⟨h1, h2⟩ := imageBond_of_axisSign_eq_neg_one hp₁ g c hs
  obtain ⟨z₁, hz₁, e₁⟩ := hb c.1
  obtain ⟨z₂, hz₂, e₂⟩ := hb (c.1 + BlockAverages.unitStep F.top c.2)
  have hne : g.axisSign (g.imageAxis c.2) ≠ 1 := by rw [hs]; omega
  unfold contourPath
  rw [h2, h1, imageBases_cellMap, imageBases_cellMap, List.map_append, List.map_append, reversePath_map,
    axisPath_minimalOffset_map hp₀ g e₁ hz₁ hξ hM, axisPath_minimalOffset_map hp₀ g e₂ hz₂ hξ hM,
    List.map_replicate, reversePath_append, reversePath_append, reversePath_reversePath, reversePath_replicate,
    List.append_assoc]
  have : mapPathStep g (c.2, true) = ((imageBond g c).2, !true) := by
    simp [mapPathStep, hne, imageBond]
  rw [this]
end Contour
section Beside
variable {m₀ m₁ : ℕ} (hp₀ : ∀ i, F.period F.depth i = m₀) (hp₁ : ∀ i, F.period F.top i = m₁)
  (g : TorusIsometry)
abbrev fineEquiv : F.Site F.depth ≃ F.Site F.depth := siteMapEquiv hp₀ g (liftedOffset F.blockSide g)
abbrev cellEquiv : F.Cell ≃ F.Cell := siteMapEquiv hp₁ g g.offset
include hp₀ in
theorem image_sitesBelow (y : F.Cell) :
    (sitesBelow F.depth y).image (fineEquiv hp₀ g) = sitesBelow F.depth (cellMap g y) := by
  ext x
  simp only [Finset.mem_image, mem_sitesBelow_iff]
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨linearPart g z, linearPart_mem_centredCube g hz, fineMap_siteAtOffset hp₀ g y z⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨_, ⟨linearPartInv g z, linearPartInv_mem_centredCube g hz, rfl⟩, ?_⟩
    rw [siteMapEquiv_apply, ← fineMap, fineMap_siteAtOffset hp₀, linearPart_linearPartInv]
include hp₁ in
theorem image_cellEquiv_cellBall (y : F.Cell) (r : ℕ) :
    (_root_.YangMills.Construction.LumpContours.cellBall y r).image (cellEquiv hp₁ g) = _root_.YangMills.Construction.LumpContours.cellBall (cellMap g y) r := by
  ext x
  simp only [_root_.YangMills.Construction.LumpContours.cellBall, Finset.mem_image]
  constructor
  · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨linearPart g h, linearPart_mem_centredCube g hh, (siteMap_add hp₁ g _ h y).symm⟩
  · rintro ⟨h, hh, rfl⟩
    refine ⟨_, ⟨linearPartInv g h, linearPartInv_mem_centredCube g hh, rfl⟩, ?_⟩
    rw [siteMapEquiv_apply, siteMap_add hp₁, linearPart_linearPartInv]
include hp₀ in
theorem image_cutBelow (S : Finset F.Cell) :
    (cutBelow F.depth S).image (fineEquiv hp₀ g) = cutBelow F.depth (S.image (cellEquiv hp₁ g)) := by
  unfold cutBelow
  rw [Finset.image_biUnion, Finset.biUnion_image]
  exact Finset.biUnion_congr rfl fun y _ => image_sitesBelow hp₀ g y
theorem image_fineEquiv_injective : Function.Injective (Finset.image (fineEquiv hp₀ g)) :=
  Finset.image_injective (fineEquiv hp₀ g).injective
include hp₁ in
theorem nearbyLumps_image (h : Finset (Finset (F.Site F.depth))) (y : F.Cell) :
    nearbyLumps (h.image (Finset.image (fineEquiv hp₀ g))) (cellMap g y) =
      (nearbyLumps h y).image (Finset.image (fineEquiv hp₀ g)) := by
  unfold nearbyLumps
  rw [Finset.filter_image]
  congr 1
  refine Finset.filter_congr fun l _ => ?_
  rw [← image_cellEquiv_cellBall hp₁ g y 2, ← image_cutBelow hp₀ hp₁ g]
  exact Finset.image_subset_image_iff (fineEquiv hp₀ g).injective
include hp₁ in
theorem isCrowded_image_iff (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth))) (y : F.Cell) :
    IsCrowded J₀ (h.image (Finset.image (fineEquiv hp₀ g))) (cellMap g y) ↔ IsCrowded J₀ h y := by
  unfold IsCrowded
  rw [nearbyLumps_image hp₀ hp₁, Finset.card_image_of_injective _ (image_fineEquiv_injective hp₀ g)]
include hp₀ in
theorem image_thicken (k : ℕ) (l : Finset (F.Site F.depth)) :
    (thicken k l).image (fineEquiv hp₀ g) = thicken k (l.image (fineEquiv hp₀ g)) := by
  ext x
  simp only [thicken, Finset.mem_image, Finset.mem_biUnion]
  constructor
  · rintro ⟨_, ⟨w, hw, h, hh, rfl⟩, rfl⟩
    exact ⟨_, ⟨w, hw, rfl⟩, linearPart g h, linearPart_mem_centredCube g hh, (siteMap_add hp₀ g _ h w).symm⟩
  · rintro ⟨_, ⟨w, hw, rfl⟩, h, hh, rfl⟩
    refine ⟨_, ⟨w, hw, linearPartInv g h, linearPartInv_mem_centredCube g hh, rfl⟩, ?_⟩
    rw [siteMapEquiv_apply, siteMap_add hp₀, linearPart_linearPartInv]
    rfl
include hp₁ in
theorem excludedBoxes_image (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth))) (y : F.Cell) :
    excludedBoxes J₀ (h.image (Finset.image (fineEquiv hp₀ g))) (cellMap g y) =
      (excludedBoxes J₀ h y).image (Finset.image (fineEquiv hp₀ g)) := by
  unfold excludedBoxes
  by_cases hc : IsCrowded J₀ h y
  · rw [if_pos hc, if_pos ((isCrowded_image_iff hp₀ hp₁ g J₀ h y).mpr hc)]
    simp
  · rw [if_neg hc, if_neg (fun e => hc ((isCrowded_image_iff hp₀ hp₁ g J₀ h y).mp e))]
    rw [nearbyLumps_image hp₀ hp₁]
    have e : ((nearbyLumps h y).image (Finset.image (fineEquiv hp₀ g))).image lumpCollar =
        ((nearbyLumps h y).image lumpCollar).image (Finset.image (fineEquiv hp₀ g)) := by
      rw [Finset.image_image, Finset.image_image]
      refine Finset.image_congr fun l _ => ?_
      simp only [Function.comp, lumpCollar]
      exact (image_thicken hp₀ g _ l).symm
    rw [e]
    exact mergedBoxes_image (fun B hB => isSmallBox_image hp₀ g _ hB) (fun B hB => isSmallBox_image_symm hp₀ g _ hB)
      (fun x y => supDist_siteMap hp₀ g _ x y) _
theorem siteMap_ne_iff (hp : ∀ i, F.period j i = m) (u : Fin 4 → ℤ) (x b : F.Site j) :
    (∀ i, (siteMap g u x : F.Site j) i ≠ (siteMap g u b : F.Site j) i) ↔ ∀ q, x q ≠ b q := by apply _root_.YangMills.Construction.TranslationKernel.siteMap_ne_iff <;> assumption
include hp₀ hp₁ in
theorem isBaseChoice_image_iff (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth))) (b : F.Cell → F.Site F.depth) :
    IsBaseChoice J₀ (h.image (Finset.image (fineEquiv hp₀ g))) (imageBases hp₁ g b) ↔ IsBaseChoice J₀ h b := by
  have hcond : ∀ y, (nearbyLumps (h.image (Finset.image (fineEquiv hp₀ g))) (cellMap g y) = ∅ ∨
      IsCrowded J₀ (h.image (Finset.image (fineEquiv hp₀ g))) (cellMap g y)) ↔
        (nearbyLumps h y = ∅ ∨ IsCrowded J₀ h y) := by
    intro y
    rw [nearbyLumps_image hp₀ hp₁, isCrowded_image_iff hp₀ hp₁, Finset.image_eq_empty]
  have hcentre : ∀ y, imageBases hp₁ g b (cellMap g y) = cellCentre F.depth (cellMap g y) ↔
      b y = cellCentre F.depth y := by
    intro y
    rw [imageBases_cellMap, ← fineMap_cellCentre hp₀]
    exact (siteMap_injective hp₀ g _).eq_iff
  have hunder : ∀ y, imageBases hp₁ g b (cellMap g y) ∈ sitesBelow F.depth (cellMap g y) ↔
      b y ∈ sitesBelow F.depth y := by
    intro y
    rw [imageBases_cellMap, ← image_sitesBelow hp₀ g y]
    constructor
    · intro hx
      obtain ⟨w, hw, e⟩ := Finset.mem_image.mp hx
      have : w = b y := (fineEquiv hp₀ g).injective e
      rwa [← this]
    · intro hx
      exact Finset.mem_image_of_mem _ hx
  constructor
  · intro hB y
    have h1 := hB (cellMap g y)
    refine ⟨fun c => (hcentre y).mp (h1.1 ((hcond y).mpr c)), fun c => ?_⟩
    have h2 := h1.2 (fun e => c ((hcond y).mp e))
    refine ⟨(hunder y).mp h2.1, fun B hB' x hx i => ?_⟩
    have h3 := h2.2
    rw [excludedBoxes_image hp₀ hp₁, imageBases_cellMap] at h3
    exact (siteMap_ne_iff g hp₀ _ x (b y)).mp
      (h3 (B.image (fineEquiv hp₀ g)) (Finset.mem_image_of_mem _ hB') (fineEquiv hp₀ g x)
        (Finset.mem_image_of_mem _ hx)) i
  · intro hB y'
    obtain ⟨y, rfl⟩ := (cellEquiv hp₁ g).surjective y'
    have h1 := hB y
    refine ⟨fun c => (hcentre y).mpr (h1.1 ((hcond y).mp c)), fun c => ?_⟩
    have h2 := h1.2 (fun e => c ((hcond y).mpr e))
    refine ⟨(hunder y).mpr h2.1, fun B' hB' x' hx' => ?_⟩
    have hB'' : B' ∈ excludedBoxes J₀ (h.image (Finset.image (fineEquiv hp₀ g))) (cellMap g y) := hB'
    rw [excludedBoxes_image hp₀ hp₁] at hB''
    obtain ⟨B, hB₀, rfl⟩ := Finset.mem_image.mp hB''
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hx'
    exact show ∀ i, (fineEquiv hp₀ g x) i ≠ (imageBases hp₁ g b (cellMap g y)) i from by
      rw [imageBases_cellMap]
      exact (siteMap_ne_iff g hp₀ _ x (b y)).mpr (h2.2 B hB₀ x hx)
end Beside
section Means
variable {m₀ m₁ : ℕ} (hp₀ : ∀ i, F.period F.depth i = m₀) (hp₁ : ∀ i, F.period F.top i = m₁)
  (g : TorusIsometry)
def contourMap (g : TorusIsometry) (e : (Fin 4 → ℤ) × Equiv.Perm (Fin 4)) : (Fin 4 → ℤ) × Equiv.Perm (Fin 4) :=
  (linearPart g e.1, e.2.trans g.axisPerm.symm)
theorem contourMap_injective : Function.Injective (contourMap g) := by apply _root_.YangMills.Construction.TranslationKernel.contourImage_injective <;> assumption
theorem exists_contourMap_eq (e : (Fin 4 → ℤ) × Equiv.Perm (Fin 4)) (he : e ∈ allContours F) :
    ∃ e₀ ∈ allContours F, contourMap g e₀ = e := by apply _root_.YangMills.Construction.TranslationKernel.exists_contourImage_eq <;> assumption
theorem contourMap_mem {e : (Fin 4 → ℤ) × Equiv.Perm (Fin 4)} (he : e ∈ allContours F) :
    contourMap g e ∈ allContours F := by apply _root_.YangMills.Construction.TranslationKernel.contourImage_mem <;> assumption
include hp₀ hp₁ in
theorem mem_pathSites_image_iff {b : F.Cell → F.Site F.depth}
    (hb : ∀ y, ∃ z ∈ centredCube F.blockSide, b y = siteAtOffset y z)
    (hM : 2 * (F.blockSide : ℤ) ≤ m₀) (c : F.Cell × Fin 4) {ξ : Fin 4 → ℤ} (hξ : ξ ∈ centredCube F.blockSide)
    (π : Equiv.Perm (Fin 4)) (z : F.Site F.depth) :
    z ∈ pathSites (imageBases hp₁ g b (imageBond g c).1)
        (contourPath (imageBases hp₁ g b) (imageBond g c) (linearPart g ξ) (π.trans g.axisPerm.symm)) ↔
      ∃ x ∈ pathSites (b c.1) (contourPath b c ξ π), z = fineMap g x := by
  rcases g.axisSign_unit (g.imageAxis c.2) with hs | hs
  · rw [← contourPath_map_of_pos hp₀ hp₁ g hb hM c hs hξ π, (imageBond_of_axisSign_eq_one hp₁ g c hs).1,
      imageBases_cellMap, pathSites_map_siteMap hp₀]
    simp only [List.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
  · have hend := pathEndpoint_contourPath (imageBases hp₁ g b) (imageBond g c) (linearPart g ξ)
      (π.trans g.axisPerm.symm)
    rw [(imageBond_of_axisSign_eq_neg_one hp₁ g c hs).2, imageBases_cellMap] at hend
    have h1 := pathSites_map_siteMap hp₀ g (liftedOffset F.blockSide g) (b c.1) (contourPath b c ξ π)
    rw [contourPath_map_of_neg hp₀ hp₁ g hb hM c hs hξ π] at h1
    change pathSites (fineMap g (b c.1)) _ = _ at h1
    rw [← hend] at h1
    rw [← mem_pathSites_reversePath, h1]
    simp only [List.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
include hp₀ hp₁ in
theorem excludedBoxes_union_image (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth))) (c : F.Cell × Fin 4) :
    excludedBoxes J₀ (h.image (Finset.image (fineEquiv hp₀ g))) (imageBond g c).1 ∪
        excludedBoxes J₀ (h.image (Finset.image (fineEquiv hp₀ g)))
          ((imageBond g c).1 + BlockAverages.unitStep F.top (imageBond g c).2) =
      (excludedBoxes J₀ h c.1 ∪ excludedBoxes J₀ h (c.1 + BlockAverages.unitStep F.top c.2)).image
        (Finset.image (fineEquiv hp₀ g)) := by
  rcases g.axisSign_unit (g.imageAxis c.2) with hs | hs
  · obtain ⟨h1, h2⟩ := imageBond_of_axisSign_eq_one hp₁ g c hs
    rw [h2, h1, excludedBoxes_image hp₀ hp₁, excludedBoxes_image hp₀ hp₁, Finset.image_union]
  · obtain ⟨h1, h2⟩ := imageBond_of_axisSign_eq_neg_one hp₁ g c hs
    rw [h2, h1, excludedBoxes_image hp₀ hp₁, excludedBoxes_image hp₀ hp₁, Finset.image_union, Finset.union_comm]
include hp₀ hp₁ in
theorem isGoodContour_image_iff (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth))) {b : F.Cell → F.Site F.depth}
    (hb : ∀ y, ∃ z ∈ centredCube F.blockSide, b y = siteAtOffset y z) (hM : 2 * (F.blockSide : ℤ) ≤ m₀)
    (c : F.Cell × Fin 4) {ξ : Fin 4 → ℤ} (hξ : ξ ∈ centredCube F.blockSide) (π : Equiv.Perm (Fin 4)) :
    IsGoodContour J₀ (h.image (Finset.image (fineEquiv hp₀ g))) (imageBases hp₁ g b) (imageBond g c)
        (linearPart g ξ) (π.trans g.axisPerm.symm) ↔ IsGoodContour J₀ h b c ξ π := by
  unfold IsGoodContour
  rw [excludedBoxes_union_image hp₀ hp₁]
  constructor
  · intro H x hx B hB hxB
    refine H (fineMap g x) ((mem_pathSites_image_iff hp₀ hp₁ g hb hM c hξ π _).mpr ⟨x, hx, rfl⟩)
      (B.image (fineEquiv hp₀ g)) (Finset.mem_image_of_mem _ hB) (Finset.mem_image_of_mem (fineEquiv hp₀ g) hxB)
  · intro H z hz B' hB' hzB
    obtain ⟨x, hx, rfl⟩ := (mem_pathSites_image_iff hp₀ hp₁ g hb hM c hξ π _).mp hz
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hB'
    obtain ⟨w, hw, e⟩ := Finset.mem_image.mp hzB
    have : w = x := (fineEquiv hp₀ g).injective e
    exact H x hx B hB (this ▸ hw)
theorem usedContours_subset (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth))) (b : F.Cell → F.Site F.depth)
    (c : F.Cell × Fin 4) : usedContours J₀ h b c ⊆ allContours F := by apply _root_.YangMills.Construction.TranslationKernel.usedContours_subset <;> assumption
include hp₀ hp₁ in
theorem isCrowded_ends_image_iff (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth))) (c : F.Cell × Fin 4) :
    (IsCrowded J₀ (h.image (Finset.image (fineEquiv hp₀ g))) (imageBond g c).1 ∨
      IsCrowded J₀ (h.image (Finset.image (fineEquiv hp₀ g)))
        ((imageBond g c).1 + BlockAverages.unitStep F.top (imageBond g c).2)) ↔
    (IsCrowded J₀ h c.1 ∨ IsCrowded J₀ h (c.1 + BlockAverages.unitStep F.top c.2)) := by
  rcases g.axisSign_unit (g.imageAxis c.2) with hs | hs
  · obtain ⟨h1, h2⟩ := imageBond_of_axisSign_eq_one hp₁ g c hs
    rw [h2, h1, isCrowded_image_iff hp₀ hp₁, isCrowded_image_iff hp₀ hp₁]
  · obtain ⟨h1, h2⟩ := imageBond_of_axisSign_eq_neg_one hp₁ g c hs
    rw [h2, h1, isCrowded_image_iff hp₀ hp₁, isCrowded_image_iff hp₀ hp₁, or_comm]
include hp₀ hp₁ in
theorem usedContours_image (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth))) {b : F.Cell → F.Site F.depth}
    (hb : ∀ y, ∃ z ∈ centredCube F.blockSide, b y = siteAtOffset y z) (hM : 2 * (F.blockSide : ℤ) ≤ m₀)
    (c : F.Cell × Fin 4) :
    usedContours J₀ (h.image (Finset.image (fineEquiv hp₀ g))) (imageBases hp₁ g b) (imageBond g c) =
      (usedContours J₀ h b c).image (contourMap g) := by
  classical
  have hall : (allContours F).image (contourMap g) = allContours F := by
    ext e
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨e₀, he₀, rfl⟩
      exact contourMap_mem g he₀
    · intro he
      exact exists_contourMap_eq g e he
  have hf : ((allContours F).filter fun e => IsGoodContour J₀ (h.image (Finset.image (fineEquiv hp₀ g)))
        (imageBases hp₁ g b) (imageBond g c) e.1 e.2) =
      ((allContours F).filter fun e => IsGoodContour J₀ h b c e.1 e.2).image (contourMap g) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨he, hg⟩
      obtain ⟨⟨ξ, π⟩, he₀, rfl⟩ := exists_contourMap_eq g e he
      have hξ : ξ ∈ centredCube F.blockSide := (Finset.mem_product.mp he₀).1
      exact ⟨(ξ, π), ⟨he₀, (isGoodContour_image_iff hp₀ hp₁ g J₀ h hb hM c hξ π).mp hg⟩, rfl⟩
    · rintro ⟨⟨ξ, π⟩, ⟨he₀, hg⟩, rfl⟩
      have hξ : ξ ∈ centredCube F.blockSide := (Finset.mem_product.mp he₀).1
      exact ⟨contourMap_mem g he₀, (isGoodContour_image_iff hp₀ hp₁ g J₀ h hb hM c hξ π).mpr hg⟩
  have hc := isCrowded_ends_image_iff hp₀ hp₁ g J₀ h c
  have hempty : ((allContours F).filter fun e => IsGoodContour J₀ (h.image (Finset.image (fineEquiv hp₀ g)))
        (imageBases hp₁ g b) (imageBond g c) e.1 e.2) = ∅ ↔
      ((allContours F).filter fun e => IsGoodContour J₀ h b c e.1 e.2) = ∅ := by
    rw [hf, Finset.image_eq_empty]
  unfold usedContours
  by_cases h1 : IsCrowded J₀ h c.1 ∨ IsCrowded J₀ h (c.1 + BlockAverages.unitStep F.top c.2) ∨
      ((allContours F).filter fun e => IsGoodContour J₀ h b c e.1 e.2) = ∅
  · have h2 : IsCrowded J₀ (h.image (Finset.image (fineEquiv hp₀ g))) (imageBond g c).1 ∨
        IsCrowded J₀ (h.image (Finset.image (fineEquiv hp₀ g)))
          ((imageBond g c).1 + BlockAverages.unitStep F.top (imageBond g c).2) ∨
        ((allContours F).filter fun e => IsGoodContour J₀ (h.image (Finset.image (fineEquiv hp₀ g)))
          (imageBases hp₁ g b) (imageBond g c) e.1 e.2) = ∅ := by
      rw [← or_assoc, hc, hempty, or_assoc]
      exact h1
    rw [if_pos h1, if_pos h2, hall]
  · have h2 : ¬ (IsCrowded J₀ (h.image (Finset.image (fineEquiv hp₀ g))) (imageBond g c).1 ∨
        IsCrowded J₀ (h.image (Finset.image (fineEquiv hp₀ g)))
          ((imageBond g c).1 + BlockAverages.unitStep F.top (imageBond g c).2) ∨
        ((allContours F).filter fun e => IsGoodContour J₀ (h.image (Finset.image (fineEquiv hp₀ g)))
          (imageBases hp₁ g b) (imageBond g c) e.1 e.2) = ∅) := by
      rw [← or_assoc, hc, hempty, or_assoc]
      exact h1
    rw [if_neg h1, if_neg h2, hf]
include hp₀ hp₁ in
theorem pathHolonomy_contourPath_of_pos {X X' : F.GaugeField F.depth}
    (hX : LevelFieldsTransported g (liftedOffset F.blockSide g) X X')
    {b : F.Cell → F.Site F.depth} (hb : ∀ y, ∃ z ∈ centredCube F.blockSide, b y = siteAtOffset y z)
    (hM : 2 * (F.blockSide : ℤ) ≤ m₀) (c : F.Cell × Fin 4) (hs : g.axisSign (g.imageAxis c.2) = 1)
    {ξ : Fin 4 → ℤ} (hξ : ξ ∈ centredCube F.blockSide) (π : Equiv.Perm (Fin 4)) :
    pathHolonomy X' (imageBases hp₁ g b (imageBond g c).1)
        (contourPath (imageBases hp₁ g b) (imageBond g c) (linearPart g ξ) (π.trans g.axisPerm.symm)) =
      pathHolonomy X (b c.1) (contourPath b c ξ π) := by
  rw [← contourPath_map_of_pos hp₀ hp₁ g hb hM c hs hξ π, (imageBond_of_axisSign_eq_one hp₁ g c hs).1,
    imageBases_cellMap]
  exact pathHolonomy_map hp₀ hX _ _
include hp₀ hp₁ in
theorem pathHolonomy_contourPath_of_neg {X X' : F.GaugeField F.depth}
    (hX : LevelFieldsTransported g (liftedOffset F.blockSide g) X X')
    {b : F.Cell → F.Site F.depth} (hb : ∀ y, ∃ z ∈ centredCube F.blockSide, b y = siteAtOffset y z)
    (hM : 2 * (F.blockSide : ℤ) ≤ m₀) (c : F.Cell × Fin 4) (hs : g.axisSign (g.imageAxis c.2) = -1)
    {ξ : Fin 4 → ℤ} (hξ : ξ ∈ centredCube F.blockSide) (π : Equiv.Perm (Fin 4)) :
    pathHolonomy X' (imageBases hp₁ g b (imageBond g c).1)
        (contourPath (imageBases hp₁ g b) (imageBond g c) (linearPart g ξ) (π.trans g.axisPerm.symm)) =
      (pathHolonomy X (b c.1) (contourPath b c ξ π))⁻¹ := by
  have hend := pathEndpoint_contourPath (imageBases hp₁ g b) (imageBond g c) (linearPart g ξ)
    (π.trans g.axisPerm.symm)
  rw [(imageBond_of_axisSign_eq_neg_one hp₁ g c hs).2, imageBases_cellMap] at hend
  have h1 := pathHolonomy_map hp₀ hX (b c.1) (contourPath b c ξ π)
  rw [contourPath_map_of_neg hp₀ hp₁ g hb hM c hs hξ π] at h1
  change pathHolonomy X' (fineMap g (b c.1)) _ = _ at h1
  rw [← hend, pathHolonomy_reversePath] at h1
  rw [← h1, inv_inv]
include hp₀ hp₁ in
theorem contourMean_image_of_pos (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth))) {X X' : F.GaugeField F.depth}
    (hX : LevelFieldsTransported g (liftedOffset F.blockSide g) X X')
    {b : F.Cell → F.Site F.depth} (hb : ∀ y, ∃ z ∈ centredCube F.blockSide, b y = siteAtOffset y z)
    (hM : 2 * (F.blockSide : ℤ) ≤ m₀) (c : F.Cell × Fin 4) (hs : g.axisSign (g.imageAxis c.2) = 1) :
    contourMean J₀ (h.image (Finset.image (fineEquiv hp₀ g))) (imageBases hp₁ g b) X' (imageBond g c) =
      contourMean J₀ h b X c := by
  unfold contourMean
  rw [usedContours_image hp₀ hp₁ g J₀ h hb hM c, Finset.card_image_of_injective _ (contourMap_injective g),
    Finset.sum_image fun _ _ _ _ e => contourMap_injective g e]
  congr 1
  refine Finset.sum_congr rfl fun e he => ?_
  have hξ : e.1 ∈ centredCube F.blockSide := (Finset.mem_product.mp (usedContours_subset J₀ h b c he)).1
  exact congrArg _ (pathHolonomy_contourPath_of_pos hp₀ hp₁ g hX hb hM c hs hξ e.2)
theorem star_real_smul_quaternion (c : ℝ) (q : ℍ[ℝ]) : star (c • q) = c • star q := by
  ext <;> simp
include hp₀ hp₁ in
theorem contourMean_image_of_neg (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth))) {X X' : F.GaugeField F.depth}
    (hX : LevelFieldsTransported g (liftedOffset F.blockSide g) X X')
    {b : F.Cell → F.Site F.depth} (hb : ∀ y, ∃ z ∈ centredCube F.blockSide, b y = siteAtOffset y z)
    (hM : 2 * (F.blockSide : ℤ) ≤ m₀) (c : F.Cell × Fin 4) (hs : g.axisSign (g.imageAxis c.2) = -1) :
    contourMean J₀ (h.image (Finset.image (fineEquiv hp₀ g))) (imageBases hp₁ g b) X' (imageBond g c) =
      star (contourMean J₀ h b X c) := by
  unfold contourMean
  rw [usedContours_image hp₀ hp₁ g J₀ h hb hM c, Finset.card_image_of_injective _ (contourMap_injective g),
    Finset.sum_image fun _ _ _ _ e => contourMap_injective g e, star_real_smul_quaternion, star_sum]
  congr 1
  refine Finset.sum_congr rfl fun e he => ?_
  have hξ : e.1 ∈ centredCube F.blockSide := (Finset.mem_product.mp (usedContours_subset J₀ h b c he)).1
  have := pathHolonomy_contourPath_of_neg hp₀ hp₁ g hX hb hM c hs hξ e.2
  show ((pathHolonomy X' _ (contourPath _ _ (linearPart g e.1) (e.2.trans g.axisPerm.symm)) : UnitQuaternion) :
    ℍ[ℝ]) = _
  rw [this, coe_inv_unitQuaternion]
end Means
section EvaluationMaps
theorem toTorusSite_sub_unitStep (hp : ∀ i, F.period j i = m) (a : F.Site j) (d : Fin 4) :
    (toTorusSite m (a - BlockAverages.unitStep j d : F.Site j) : TorusSite m) =
      toTorusSite m a - TorusFields.unitStep m d := by apply _root_.YangMills.Construction.TranslationKernel.toTorusSite_sub_unitStep <;> assumption
theorem levelFieldsTransported_of_transports (hp : ∀ i, F.period j i = m) (g : TorusIsometry) (u : Fin 4 → ℤ)
    {W W' : TorusField m} (h : TorusIsometry.Transports ⟨g.axisPerm, g.axisSign, u, g.axisSign_unit⟩ W W') :
    LevelFieldsTransported g u (readAtLevel F j W) (readAtLevel F j W') := by
  intro x k
  have h1 := h (toTorusSite m x) k
  by_cases hs : g.axisSign (g.imageAxis k) = 1
  · have hs' : g.axisSign (g.axisPerm.symm k) = 1 := hs
    rw [if_pos hs]
    simp only [if_pos hs'] at h1
    show W' (toTorusSite m (siteMap g u x : F.Site j)) (g.imageAxis k) = W (toTorusSite m x) k
    rw [toTorusSite_siteMap g u hp]
    exact h1
  · have hs' : ¬ g.axisSign (g.axisPerm.symm k) = 1 := hs
    rw [if_neg hs]
    simp only [if_neg hs'] at h1
    show (W' (toTorusSite m (siteMap g u x - BlockAverages.unitStep j (g.imageAxis k) : F.Site j))
      (g.imageAxis k))⁻¹ = W (toTorusSite m x) k
    rw [toTorusSite_sub_unitStep hp, toTorusSite_siteMap g u hp]
    exact h1
theorem plaquetteDefect_readAtLevel (hp : ∀ i, F.period j i = m) (W : TorusField m) (x : F.Site j) (μ ν : Fin 4) :
    plaquetteDefect (readAtLevel F j W) (x, μ, ν) = TorusFields.curvature W (toTorusSite m x) μ ν := by apply _root_.YangMills.Construction.TranslationKernel.plaquetteDefect_eq_curvature <;> assumption
def imagePlaquetteCorner (g : TorusIsometry) (u : Fin 4 → ℤ) (x : F.Site j) (μ ν : Fin 4) : F.Site j :=
  siteMap g u x - (if g.axisSign (g.imageAxis μ) = 1 then 0 else BlockAverages.unitStep j (g.imageAxis μ)) -
    (if g.axisSign (g.imageAxis ν) = 1 then 0 else BlockAverages.unitStep j (g.imageAxis ν))
theorem toTorusSite_imagePlaquetteCorner (hp : ∀ i, F.period j i = m) (g : TorusIsometry) (u : Fin 4 → ℤ)
    (x : F.Site j) (μ ν : Fin 4) :
    (toTorusSite m (imagePlaquetteCorner g u x μ ν : F.Site j) : TorusSite m) =
      TorusIsometry.imageCorner ⟨g.axisPerm, g.axisSign, u, g.axisSign_unit⟩ (toTorusSite m x) μ ν := by
  have hdir : ∀ k, TorusIsometry.imageAxis ⟨g.axisPerm, g.axisSign, u, g.axisSign_unit⟩ k = g.imageAxis k :=
    fun _ => rfl
  unfold imagePlaquetteCorner TorusIsometry.imageCorner
  rw [hdir, hdir]
  have hsign : ∀ i, (TorusIsometry.mk g.axisPerm g.axisSign u g.axisSign_unit).axisSign i = g.axisSign i :=
    fun _ => rfl
  rw [hsign, hsign]
  by_cases h1 : g.axisSign (g.imageAxis μ) = 1 <;> by_cases h2 : g.axisSign (g.imageAxis ν) = 1 <;>
    simp only [h1, h2, if_true, if_false, sub_zero, toTorusSite_sub_unitStep hp, toTorusSite_siteMap g u hp]
theorem plaquetteDefect_image (hp : ∀ i, F.period j i = m) (g : TorusIsometry) (u : Fin 4 → ℤ)
    {W W' : TorusField m} (h : TorusIsometry.Transports ⟨g.axisPerm, g.axisSign, u, g.axisSign_unit⟩ W W')
    (x : F.Site j) (μ ν : Fin 4) :
    plaquetteDefect (readAtLevel F j W') (imagePlaquetteCorner g u x μ ν, g.imageAxis μ, g.imageAxis ν) =
      plaquetteDefect (readAtLevel F j W) (x, μ, ν) := by
  rw [plaquetteDefect_readAtLevel hp, plaquetteDefect_readAtLevel hp, toTorusSite_imagePlaquetteCorner hp]
  have h1 := plaquetteEnergy_of_transports h (toTorusSite m x) μ ν
  rw [plaquetteEnergy_eq_curvature_sq, plaquetteEnergy_eq_curvature_sq] at h1
  have h2 : TorusFields.curvature W (toTorusSite m x) μ ν ^ 2 =
      TorusFields.curvature W'
        (TorusIsometry.imageCorner ⟨g.axisPerm, g.axisSign, u, g.axisSign_unit⟩ (toTorusSite m x) μ ν)
        (g.imageAxis μ) (g.imageAxis ν) ^ 2 := by
    have h3 := h1
    have e : ∀ a b : ℝ, a / 2 = b / 2 → a = b := fun a b hab => by linarith
    exact e _ _ h3
  exact ((sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2).symm
theorem plaquetteDefect_swap (hp : ∀ i, F.period j i = m) (W : TorusField m) (x : F.Site j) (μ ν : Fin 4) :
    plaquetteDefect (readAtLevel F j W) (x, ν, μ) = plaquetteDefect (readAtLevel F j W) (x, μ, ν) := by apply _root_.YangMills.Construction.TranslationKernel.plaquetteDefect_swap <;> assumption
omit [∀ j i, NeZero (F.period j i)] in
theorem plaquetteCorners_swap (x : F.Site j) (μ ν : Fin 4) :
    plaquetteCorners (x, ν, μ) = plaquetteCorners (x, μ, ν) := by apply _root_.YangMills.Construction.TranslationKernel.plaquetteCorners_swap <;> assumption
theorem shifted_square_eq {A : Type*} [AddCommGroup A] [DecidableEq A] (P e₁ e₂ : A) (a b : Prop) [Decidable a]
    [Decidable b] :
    ({P - (if a then 0 else e₁) - (if b then 0 else e₂), P - (if a then 0 else e₁) - (if b then 0 else e₂) + e₁,
      P - (if a then 0 else e₁) - (if b then 0 else e₂) + e₂,
      P - (if a then 0 else e₁) - (if b then 0 else e₂) + e₁ + e₂} : Finset A) =
    {P, P + (if a then e₁ else -e₁), P + (if b then e₂ else -e₂),
      P + (if a then e₁ else -e₁) + (if b then e₂ else -e₂)} := by apply _root_.YangMills.Construction.TranslationKernel.shifted_corners_eq <;> assumption
theorem siteMap_add_unitStep (hp : ∀ i, F.period j i = m) (g : TorusIsometry) (u : Fin 4 → ℤ) (x : F.Site j)
    (k : Fin 4) :
    (siteMap g u (x + BlockAverages.unitStep j k) : F.Site j) = siteMap g u x +
      (if g.axisSign (g.imageAxis k) = 1 then BlockAverages.unitStep j (g.imageAxis k)
        else - BlockAverages.unitStep j (g.imageAxis k)) := by apply _root_.YangMills.Construction.TranslationKernel.siteMap_add_unitStep <;> assumption
theorem plaquetteCorners_image (hp : ∀ i, F.period j i = m) (g : TorusIsometry) (u : Fin 4 → ℤ) (x : F.Site j)
    (μ ν : Fin 4) :
    plaquetteCorners (imagePlaquetteCorner g u x μ ν, g.imageAxis μ, g.imageAxis ν) =
      (plaquetteCorners (x, μ, ν)).image (siteMap g u) := by
  unfold plaquetteCorners imagePlaquetteCorner
  simp only [Finset.image_insert, Finset.image_singleton, siteMap_add_unitStep hp]
  exact shifted_square_eq _ _ _ _ _
end EvaluationMaps
section Hot
variable {L n : ℕ} [NeZero L] [NeZero n]
theorem mem_hotLumps_iff (grid : LumpGrid L) (s : ℝ) (X : (stepBlockFrame L n).GaugeField 0)
    (l : Finset ((stepBlockFrame L n).Site 0)) :
    l ∈ hotLumps grid s (levelSites (stepBlockFrame L n) 0) X ↔
      ∃ (x : (stepBlockFrame L n).Site 0) (μ ν : Fin 4), μ < ν ∧ s ≤ plaquetteDefect X (x, μ, ν) ∧
        ∃ c ∈ plaquetteCorners (x, μ, ν), l = lumpOf grid c := by apply _root_.YangMills.Construction.TranslationKernel.mem_hotLumps_iff <;> assumption
theorem hotLumps_image (hLodd : Odd L) (grid : LumpGrid L) (s : ℝ) (g : TorusIsometry)
    {W W' : TorusField (n * L)} (h : (g.scaledLift L).Transports W W') :
    hotLumps grid s (levelSites (stepBlockFrame L n) 0) (readAtLevel (stepBlockFrame L n) 0 W') =
      (hotLumps grid s (levelSites (stepBlockFrame L n) 0) (readAtLevel (stepBlockFrame L n) 0 W)).image
        (Finset.image (fineEquiv (F := stepBlockFrame L n) (m₀ := n * L) stepBlockFrame_period_zero g)) := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hp : ∀ i, (stepBlockFrame L n).period 0 i = n * L := stepBlockFrame_period_zero
  have hm : (L : ℤ) ∣ ((n * L : ℕ) : ℤ) := by
    push_cast
    exact Dvd.intro_left _ rfl
  have hu : ∀ i, (L : ℤ) ∣ liftedOffset (stepBlockFrame L n).blockSide g i := fun i => Dvd.intro _ rfl
  have hlump : ∀ c : (stepBlockFrame L n).Site 0,
      lumpOf grid (siteMap g (liftedOffset (stepBlockFrame L n).blockSide g) c : (stepBlockFrame L n).Site 0) =
        (lumpOf grid c).image (fineEquiv (F := stepBlockFrame L n) (m₀ := n * L) stepBlockFrame_period_zero g) :=
    fun c => lumpOf_siteMap hL hLodd hp hm g _ hu grid c
  have hcarry : TorusIsometry.Transports
      ⟨g.axisPerm, g.axisSign, liftedOffset (stepBlockFrame L n).blockSide g, g.axisSign_unit⟩ W W' := h
  ext l
  rw [mem_hotLumps_iff]
  constructor
  · rintro ⟨x', μ', ν', hlt, hs, c', hc', rfl⟩
    set μ₀ := g.axisPerm μ' with hμ₀
    set ν₀ := g.axisPerm ν' with hν₀
    have hdμ : g.imageAxis μ₀ = μ' := by simp [TorusIsometry.imageAxis, hμ₀]
    have hdν : g.imageAxis ν₀ = ν' := by simp [TorusIsometry.imageAxis, hν₀]
    let e := fineEquiv (F := stepBlockFrame L n) (m₀ := n * L) stepBlockFrame_period_zero g
    let x₀ : (stepBlockFrame L n).Site 0 :=
      e.symm (x' + (if g.axisSign μ' = 1 then 0 else BlockAverages.unitStep 0 μ') +
        (if g.axisSign ν' = 1 then 0 else BlockAverages.unitStep 0 ν'))
    have hbase : imagePlaquetteCorner g (liftedOffset (stepBlockFrame L n).blockSide g) x₀ μ₀ ν₀ = x' := by
      unfold imagePlaquetteCorner
      have : siteMap g (liftedOffset (stepBlockFrame L n).blockSide g) x₀ =
          x' + (if g.axisSign μ' = 1 then 0 else BlockAverages.unitStep 0 μ') +
            (if g.axisSign ν' = 1 then 0 else BlockAverages.unitStep 0 ν') := e.apply_symm_apply _
      rw [this, hdμ, hdν]
      abel
    have hcurv := plaquetteDefect_image (F := stepBlockFrame L n) (j := 0) hp g _ hcarry x₀ μ₀ ν₀
    rw [hbase, hdμ, hdν] at hcurv
    have hcorn := plaquetteCorners_image (F := stepBlockFrame L n) (j := 0) hp g
      (liftedOffset (stepBlockFrame L n).blockSide g) x₀ μ₀ ν₀
    rw [hbase, hdμ, hdν] at hcorn
    rw [hcorn] at hc'
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hc'
    have hne : μ₀ ≠ ν₀ := fun e' => (ne_of_lt hlt) (g.axisPerm.injective e')
    refine Finset.mem_image.mpr ⟨lumpOf grid c, (mem_hotLumps_iff grid s _ _).mpr ?_, (hlump c).symm⟩
    rcases lt_or_gt_of_ne hne with hlt₀ | hlt₀
    · exact ⟨x₀, μ₀, ν₀, hlt₀, by rw [← hcurv]; exact hs, c, hc, rfl⟩
    · exact ⟨x₀, ν₀, μ₀, hlt₀, by rw [plaquetteDefect_swap hp, ← hcurv]; exact hs, c,
        by rw [plaquetteCorners_swap]; exact hc, rfl⟩
  · intro hl
    obtain ⟨l₀, hl₀, rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨x, μ, ν, hlt, hs, c, hc, rfl⟩ := (mem_hotLumps_iff grid s _ _).mp hl₀
    have hne : g.imageAxis μ ≠ g.imageAxis ν := fun e' => (ne_of_lt hlt) (g.axisPerm.symm.injective e')
    have hcurv := plaquetteDefect_image (F := stepBlockFrame L n) (j := 0) hp g _ hcarry x μ ν
    have hcorn := plaquetteCorners_image (F := stepBlockFrame L n) (j := 0) hp g
      (liftedOffset (stepBlockFrame L n).blockSide g) x μ ν
    have hmem : siteMap g (liftedOffset (stepBlockFrame L n).blockSide g) c ∈
        plaquetteCorners (imagePlaquetteCorner g (liftedOffset (stepBlockFrame L n).blockSide g) x μ ν,
          g.imageAxis μ, g.imageAxis ν) := by
      rw [hcorn]
      exact Finset.mem_image_of_mem _ hc
    rcases lt_or_gt_of_ne hne with hlt₀ | hlt₀
    · exact ⟨_, g.imageAxis μ, g.imageAxis ν, hlt₀, by rw [hcurv]; exact hs, _, hmem, (hlump c).symm⟩
    · exact ⟨imagePlaquetteCorner g (liftedOffset (stepBlockFrame L n).blockSide g) x μ ν, g.imageAxis ν,
        g.imageAxis μ, hlt₀, by rw [plaquetteDefect_swap hp, hcurv]; exact hs, _,
        by rw [plaquetteCorners_swap]; exact hmem, (hlump c).symm⟩
end Hot
section Bonds
variable {m₀ m₁ : ℕ} (hp₁ : ∀ i, F.period F.top i = m₁) (g : TorusIsometry)
include hp₁ in
theorem imageBond_injective : Function.Injective (imageBond g : F.Cell × Fin 4 → F.Cell × Fin 4) := by apply _root_.YangMills.Construction.TranslationKernel.imageBond_injective <;> assumption
end Bonds
section Main
theorem meanKernel_star_inv (s : ℝ) (q : ℍ[ℝ]) (v : UnitQuaternion) :
    TorusContours.meanKernel s (star q) v⁻¹ = TorusContours.meanKernel s q v := by apply _root_.YangMills.Construction.IsometryInvariance.meanKernel_star_inv <;> assumption
theorem mem_baseChoices (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) {n : ℕ} [NeZero n] (W : (stepBlockFrame ℓ.side n).GaugeField 0)
    (b : (stepBlockFrame ℓ.side n).Cell → (stepBlockFrame ℓ.side n).Site 0) :
    b ∈ baseChoices ℓ W ↔ IsBaseChoice ℓ.baseDepth (fineHotLumps ℓ W) b := by apply _root_.YangMills.Construction.TranslationKernel.mem_baseChoices_iff <;> assumption
end Main
section Scores
open WeightedResponses
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem stepBlockFrame_period_depth (L n : ℕ) [NeZero L] [NeZero n] :
    ∀ i, (stepBlockFrame L n).period (stepBlockFrame L n).depth i = n * L := stepBlockFrame_period_zero
theorem stepBlockFrame_period_top (L n : ℕ) [NeZero L] [NeZero n] :
    ∀ i, (stepBlockFrame L n).period (stepBlockFrame L n).top i = n := TorusContours.stepBlockFrame_period_one
def imageBaseChoice (R : StepSetup) (n : ℕ) [NeZero n] (g : TorusIsometry) (b : BaseChoice R.params.side n) :
    BaseChoice R.params.side n :=
  imageBases (stepBlockFrame_period_top R.params.side n) g b
theorem imageBaseChoice_cellMap (R : StepSetup) (n : ℕ) [NeZero n] (g : TorusIsometry)
    (b : BaseChoice R.params.side n) (y : (stepBlockFrame R.params.side n).Cell) :
    imageBaseChoice R n g b (cellMap g y) = fineMap g (b y) :=
  imageBases_cellMap (stepBlockFrame_period_top R.params.side n) g b y
def baseChoiceEquiv (R : StepSetup) (n : ℕ) [NeZero n] (g : TorusIsometry) :
    BaseChoice R.params.side n ≃ BaseChoice R.params.side n where
  toFun := imageBaseChoice R n g
  invFun := fun b' y => (fineEquiv (stepBlockFrame_period_depth R.params.side n) g).symm (b' (cellMap g y))
  left_inv := fun b => by
    funext y
    exact (congrArg (fineEquiv (stepBlockFrame_period_depth R.params.side n) g).symm
      (imageBaseChoice_cellMap R n g b y)).trans
      ((fineEquiv (stepBlockFrame_period_depth R.params.side n) g).symm_apply_apply _)
  right_inv := fun b' => by
    funext y'
    obtain ⟨y, rfl⟩ := (cellEquiv (stepBlockFrame_period_top R.params.side n) g).surjective y'
    exact (imageBaseChoice_cellMap R n g _ y).trans
      ((fineEquiv (stepBlockFrame_period_depth R.params.side n) g).apply_symm_apply _)
def imageTorusBond (g : TorusIsometry) (c : TorusBond n) : TorusBond n :=
  (if g.axisSign (g.imageAxis c.2) = 1 then g.mapSite c.1
    else g.mapSite c.1 - TorusFields.unitStep n (g.imageAxis c.2), g.imageAxis c.2)
theorem cellMap_torusSiteInFrame (L : ℕ) [NeZero L] (g : TorusIsometry) (x : TorusSite n) :
    cellMap g (torusSiteInFrame (stepBlockFrame L n) 1 x) = torusSiteInFrame (stepBlockFrame L n) 1 (g.mapSite x) := by
  show siteMap g g.offset (siteOfCoords 1 fun i => ((x i).cast : ℤ) : (stepBlockFrame L n).Site 1) =
    siteOfCoords 1 fun i => ((g.mapSite x i).cast : ℤ)
  rw [siteMap_siteOfCoords TorusContours.stepBlockFrame_period_one]
  refine siteOfCoords_congr TorusContours.stepBlockFrame_period_one fun i => ?_
  simp [linearPart, TorusIsometry.mapSite, ZMod.intCast_zmod_cast]
theorem torusSiteInFrame_sub (L : ℕ) [NeZero L] (a : TorusSite n) (d : Fin 4) :
    torusSiteInFrame (stepBlockFrame L n) 1 (a - TorusFields.unitStep n d) =
      torusSiteInFrame (stepBlockFrame L n) 1 a - BlockAverages.unitStep (stepBlockFrame L n).top d := by
  show (siteOfCoords 1 fun i => (((a - TorusFields.unitStep n d) i).cast : ℤ) : (stepBlockFrame L n).Site 1) =
    (siteOfCoords 1 fun i => ((a i).cast : ℤ)) - siteOfCoords 1 (Pi.single d 1)
  rw [show ∀ u v : (stepBlockFrame L n).Site 1, u - v = u + -v from fun _ _ => sub_eq_add_neg _ _,
    ← TorusContours.siteOfCoords_neg, ← TorusContours.siteOfCoords_add]
  refine siteOfCoords_congr TorusContours.stepBlockFrame_period_one fun i => ?_
  by_cases h : i = d
  · subst h
    simp [TorusFields.unitStep, ZMod.intCast_zmod_cast, sub_eq_add_neg]
  · simp [TorusFields.unitStep, h, ZMod.intCast_zmod_cast]
theorem imageBond_torusSiteInFrame (L : ℕ) [NeZero L] (g : TorusIsometry) (c : TorusBond n) :
    imageBond (F := stepBlockFrame L n) g (torusSiteInFrame (stepBlockFrame L n) 1 c.1, c.2) =
      (torusSiteInFrame (stepBlockFrame L n) 1 (imageTorusBond g c).1, (imageTorusBond g c).2) := by
  obtain ⟨x, k⟩ := c
  simp only [imageBond, imageTorusBond]
  refine Prod.ext ?_ rfl
  by_cases hs : g.axisSign (g.imageAxis k) = 1
  · simp only [hs, if_true]
    exact cellMap_torusSiteInFrame L g x
  · simp only [hs, if_false]
    show cellMap g (torusSiteInFrame (stepBlockFrame L n) 1 x) -
      BlockAverages.unitStep (stepBlockFrame L n).top (g.imageAxis k) = _
    rw [cellMap_torusSiteInFrame, torusSiteInFrame_sub]
    rfl
theorem re_star_mul_inv_inv (q : ℍ[ℝ]) (v : UnitQuaternion) :
    (star q * (((v⁻¹)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re = (q * ((v⁻¹ : UnitQuaternion) : ℍ[ℝ])).re := by
  rw [inv_inv, coe_inv_unitQuaternion]
  simp only [Quaternion.re_mul, Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star,
    Quaternion.imK_star]
  ring
theorem mapSite_sub_unitStep_of_pos (g : TorusIsometry) (x : TorusSite n) (k : Fin 4)
    (hs : g.axisSign (g.imageAxis k) = 1) :
    g.mapSite (x - TorusFields.unitStep n k) = g.mapSite x - TorusFields.unitStep n (g.imageAxis k) := by
  funext i
  by_cases h : i = g.imageAxis k
  · subst h
    have e : g.axisPerm (g.imageAxis k) = k := by simp [TorusIsometry.imageAxis]
    simp [TorusIsometry.mapSite, TorusFields.unitStep, e, hs]
    ring
  · have hk : g.axisPerm i ≠ k := fun e => h (by simp [TorusIsometry.imageAxis, ← e])
    simp [TorusIsometry.mapSite, TorusFields.unitStep, h, hk]
theorem mapSite_sub_unitStep_of_neg (g : TorusIsometry) (x : TorusSite n) (k : Fin 4)
    (hs : g.axisSign (g.imageAxis k) = -1) :
    g.mapSite (x - TorusFields.unitStep n k) = g.mapSite x + TorusFields.unitStep n (g.imageAxis k) := by
  funext i
  by_cases h : i = g.imageAxis k
  · subst h
    have e : g.axisPerm (g.imageAxis k) = k := by simp [TorusIsometry.imageAxis]
    simp [TorusIsometry.mapSite, TorusFields.unitStep, e, hs]
    ring
  · have hk : g.axisPerm i ≠ k := fun e => h (by simp [TorusIsometry.imageAxis, ← e])
    simp [TorusIsometry.mapSite, TorusFields.unitStep, h, hk]
theorem parentBlock_intCast (L : ℕ) [NeZero L] (z : ℤ) :
    (((((z : ZMod (n * L)).cast : ℤ) + ((L : ℤ) - 1) / 2) / (L : ℤ) : ℤ) : ZMod n) =
      (((z + ((L : ℤ) - 1) / 2) / (L : ℤ) : ℤ) : ZMod n) := by
  have hL : (L : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne L
  have h := ZMod.intCast_zmod_cast (z : ZMod (n * L))
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  obtain ⟨k, hk⟩ := h
  have e : ((z : ZMod (n * L)).cast : ℤ) = z - ((n * L : ℕ) : ℤ) * k := by linarith
  rw [e]
  have e2 : z - ((n * L : ℕ) : ℤ) * k + ((L : ℤ) - 1) / 2 =
      z + ((L : ℤ) - 1) / 2 + (L : ℤ) * (-(n : ℤ) * k) := by
    push_cast
    ring
  rw [e2, Int.add_mul_ediv_left _ _ hL]
  push_cast
  simp
theorem blockIndex_neg (L : ℕ) (hodd : Odd L) (a : ℤ) :
    (-a + ((L : ℤ) - 1) / 2) / (L : ℤ) = -((a + ((L : ℤ) - 1) / 2) / (L : ℤ)) := by
  obtain ⟨h, hh⟩ := hodd
  have hhalf : ((L : ℤ) - 1) / 2 = h := by omega
  have hpos : (0 : ℤ) < L := by omega
  rw [hhalf]
  set q := (a + h) / (L : ℤ) with hq
  set r := (a + h) % (L : ℤ) with hr
  have h1 : (L : ℤ) * q + r = a + h := Int.mul_ediv_add_emod _ _
  have h2 : 0 ≤ r := Int.emod_nonneg _ (by omega)
  have h3 : r < L := Int.emod_lt_of_pos _ hpos
  have e : -a + h = (2 * h - r) + (L : ℤ) * (-q) := by linarith
  rw [e, Int.add_mul_ediv_left _ _ (by omega), Int.ediv_eq_zero_of_lt (by omega) (by omega)]
  ring
theorem parentBlock_mapSite_scaledLift (L : ℕ) [NeZero L] (hodd : Odd L) (g : TorusIsometry)
    (z : TorusSite (n * L)) :
    parentBlock L ((g.scaledLift L).mapSite z) = g.mapSite (parentBlock L z) := by
  have hL : (L : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne L
  funext i
  set a : ℤ := ((z (g.axisPerm i)).cast : ℤ) with ha
  have e1 : ((g.scaledLift L).mapSite z) i =
      ((g.axisSign i * a + (L : ℤ) * g.offset i : ℤ) : ZMod (n * L)) := by
    have : ((a : ℤ) : ZMod (n * L)) = z (g.axisPerm i) := ZMod.intCast_zmod_cast _
    simp only [TorusIsometry.mapSite, TorusIsometry.scaledLift]
    push_cast
    rw [this]
  simp only [parentBlock]
  rw [e1, parentBlock_intCast]
  have e2 : g.axisSign i * a + (L : ℤ) * g.offset i + ((L : ℤ) - 1) / 2 =
      (g.axisSign i * a + ((L : ℤ) - 1) / 2) + (L : ℤ) * g.offset i := by ring
  rw [e2, Int.add_mul_ediv_left _ _ hL]
  simp only [TorusIsometry.mapSite, parentBlock]
  rw [← ha]
  rcases g.axisSign_unit i with hs | hs
  · rw [hs]
    simp
  · rw [hs]
    have := blockIndex_neg L hodd a
    simp only [neg_mul, one_mul]
    rw [this]
    push_cast
    ring
theorem baseLaw_of_mem {W : TorusField (n * R.params.side)} {b : BaseChoice R.params.side n}
    (h : b ∈ baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W)) :
    baseLaw (R := R) W b =
      1 / ((baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W)).card : ℝ) := if_pos h
theorem baseLaw_of_not_mem {W : TorusField (n * R.params.side)} {b : BaseChoice R.params.side n}
    (h : b ∉ baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W)) :
    baseLaw (R := R) W b = 0 := if_neg h
theorem bondScore_eq_of (hS : BondScoreProperties) (hfit : R.params.Admissible)
    {W W' : TorusField (n * R.params.side)} {V V' : TorusField n}
    {b b' : BaseChoice R.params.side n} {c c' : TorusBond n}
    (hsize : ‖bondMean R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W') b' c'‖ =
      ‖bondMean R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W) b c‖)
    (hre : (bondMean R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W') b' c' *
        (((V' c'.1 c'.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re =
      (bondMean R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W) b c *
        (((V c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re) :
    bondScore R.params R.coupling W' V' b' c' = bondScore R.params R.coupling W V b c := by
  have e' : meanNorm R.params W' b' c' = ‖bondMean R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W') b' c'‖ :=
    rfl
  have e : meanNorm R.params W b c = ‖bondMean R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W) b c‖ := rfl
  rw [(hS R.params hfit R.coupling n b' c').2.1 W' V', (hS R.params hfit R.coupling n b c).2.1 W V, e', e, hsize, hre]
set_option maxHeartbeats 1000000 in
theorem weight_and_scores_transport (hS : BondScoreProperties) (hfit : R.params.Admissible) (hn : R.params.n₀ ≤ n)
    (g : TorusIsometry) (W W' : TorusField (n * R.params.side)) (V V' : TorusField n)
    (hW : (g.scaledLift R.params.side).Transports W W') (hV : g.Transports V V')
    (b : BaseChoice R.params.side n) :
    baseLaw (R := R) W' (baseChoiceEquiv R n g b) * (∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
        bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W')
          (readAtLevel (stepBlockFrame R.params.side n) 1 V') (baseChoiceEquiv R n g b) c) =
      baseLaw (R := R) W b * (∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
        bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
          (readAtLevel (stepBlockFrame R.params.side n) 1 V) b c) ∧
    (baseLaw (R := R) W b ≠ 0 → ∀ Y : TorusSite n,
      blockBondScores (R := R) W' V' (baseChoiceEquiv R n g b) (g.mapSite Y) =
        blockBondScores (R := R) W V b Y) := by
  classical
  have hp₀ : ∀ i, (stepBlockFrame R.params.side n).period (stepBlockFrame R.params.side n).depth i =
      n * R.params.side := stepBlockFrame_period_zero
  have hp₁ : ∀ i, (stepBlockFrame R.params.side n).period (stepBlockFrame R.params.side n).top i = n :=
    TorusContours.stepBlockFrame_period_one
  have hL1 : 1 ≤ (stepBlockFrame R.params.side n).blockSide := Nat.pos_of_ne_zero (NeZero.ne R.params.side)
  have hn2 : 2 ≤ n := by
    have := hfit.n₀_ge
    omega
  have hM : 2 * ((stepBlockFrame R.params.side n).blockSide : ℤ) ≤ ((n * R.params.side : ℕ) : ℤ) := by
    show 2 * (R.params.side : ℤ) ≤ _
    push_cast
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn2) (by positivity)
  set X := fineLevelField R.params n W with hXd
  set X' := fineLevelField R.params n W' with hXd'
  set U := coarseLevelField R.params n V with hUd
  set U' := coarseLevelField R.params n V' with hUd'
  have hX : LevelFieldsTransported g (liftedOffset (stepBlockFrame R.params.side n).blockSide g) X X' :=
    levelFieldsTransported_of_transports stepBlockFrame_period_zero g _ hW
  have hU : LevelFieldsTransported g g.offset U U' := levelFieldsTransported_of_transports TorusContours.stepBlockFrame_period_one g _ hV
  have hH : fineHotLumps R.params X' = (fineHotLumps R.params X).image (Finset.image (fineEquiv hp₀ g)) :=
    hotLumps_image hfit.L_odd R.params.grid R.params.threshold g hW
  have hiff : ∀ b : BaseChoice R.params.side n,
      imageBases hp₁ g b ∈ baseChoices R.params X' ↔ b ∈ baseChoices R.params X := by
    intro b
    constructor
    · intro h
      have h0 : IsBaseChoice R.params.baseDepth (fineHotLumps R.params X') (imageBases hp₁ g b) :=
        (mem_baseChoices R.params X' _).mp h
      have h1 : IsBaseChoice R.params.baseDepth ((fineHotLumps R.params X).image (Finset.image (fineEquiv hp₀ g)))
          (imageBases hp₁ g b) := hH ▸ h0
      exact (mem_baseChoices R.params X b).mpr
        ((isBaseChoice_image_iff hp₀ hp₁ g R.params.baseDepth (fineHotLumps R.params X) b).mp h1)
    · intro h
      have h1 := (isBaseChoice_image_iff hp₀ hp₁ g R.params.baseDepth (fineHotLumps R.params X) b).mpr
        ((mem_baseChoices R.params X b).mp h)
      exact (mem_baseChoices R.params X' _).mpr (hH ▸ h1)
  have hcard : (baseChoices R.params X').card = (baseChoices R.params X).card := by
    refine (Finset.card_bij (fun b _ => imageBases hp₁ g b) (fun b hb => (hiff b).mpr hb)
      (fun b _ b' _ e => (baseChoiceEquiv R n g).injective e) ?_).symm
    intro b' hb'
    obtain ⟨b, rfl⟩ := (baseChoiceEquiv R n g).surjective b'
    exact ⟨b, (hiff b).mp hb', rfl⟩
  have hmeans : ∀ b ∈ baseChoices R.params X, ∀ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
      (g.axisSign (g.imageAxis c.2) = 1 →
        contourMean R.params.baseDepth (fineHotLumps R.params X') (imageBases hp₁ g b) X' (imageBond g c) =
          contourMean R.params.baseDepth (fineHotLumps R.params X) b X c) ∧
      (g.axisSign (g.imageAxis c.2) = -1 →
        contourMean R.params.baseDepth (fineHotLumps R.params X') (imageBases hp₁ g b) X' (imageBond g c) =
          star (contourMean R.params.baseDepth (fineHotLumps R.params X) b X c)) := by
    intro b hb c
    have hb' : IsBaseChoice R.params.baseDepth (fineHotLumps R.params X) b := (mem_baseChoices R.params X b).mp hb
    have hrep : ∀ y, ∃ z ∈ centredCube (stepBlockFrame R.params.side n).blockSide, b y = siteAtOffset y z :=
      fun y => exists_centredCube_of_isBaseChoice hL1 hb' y
    exact ⟨fun hs => (congrArg (fun h => contourMean R.params.baseDepth h (imageBases hp₁ g b) X' (imageBond g c)) hH).trans
        (contourMean_image_of_pos hp₀ hp₁ g R.params.baseDepth _ hX hrep hM c hs),
      fun hs => (congrArg (fun h => contourMean R.params.baseDepth h (imageBases hp₁ g b) X' (imageBond g c)) hH).trans
        (contourMean_image_of_neg hp₀ hp₁ g R.params.baseDepth _ hX hrep hM c hs)⟩
  have hbond : ∀ b ∈ baseChoices R.params X, ∀ c,
      bondKernel R.params R.coupling X' U' (imageBases hp₁ g b) (imageBond g c) =
        bondKernel R.params R.coupling X U b c := by
    intro b hb c
    refine (bondKernel_eq_meanKernel R.params R.coupling X' U' _ _).trans
      (Eq.trans ?_ (bondKernel_eq_meanKernel R.params R.coupling X U b c).symm)
    rcases g.axisSign_unit (g.imageAxis c.2) with hs | hs
    · have h1 := hU c.1 c.2
      rw [if_pos hs] at h1
      have e : U' (imageBond g c).1 (imageBond g c).2 = U c.1 c.2 := by
        simp only [imageBond, hs, if_true]
        exact h1
      exact congrArg₂ (TorusContours.meanKernel (R.params.coupling * R.coupling)) ((hmeans b hb c).1 hs) e
    · have hne : g.axisSign (g.imageAxis c.2) ≠ 1 := by rw [hs]; omega
      have h1 := hU c.1 c.2
      rw [if_neg hne] at h1
      have e : U' (imageBond g c).1 (imageBond g c).2 = (U c.1 c.2)⁻¹ := by
        simp only [imageBond, hne, if_false]
        rw [← h1, inv_inv]
        rfl
      exact (congrArg₂ (TorusContours.meanKernel (R.params.coupling * R.coupling)) ((hmeans b hb c).2 hs) e).trans
        (meanKernel_star_inv _ _ _)
  refine ⟨?_, ?_⟩
  · by_cases hb : b ∈ baseChoices R.params X
    · have e1 : baseLaw (R := R) W' (baseChoiceEquiv R n g b) = baseLaw (R := R) W b :=
        (baseLaw_of_mem (R := R) (W := W') (b := baseChoiceEquiv R n g b) ((hiff b).mpr hb)).trans
          ((congrArg (fun k : ℕ => 1 / (k : ℝ)) hcard).trans (baseLaw_of_mem (R := R) (W := W) (b := b) hb).symm)
      have hprod : (∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
            bondKernel R.params R.coupling X' U' (imageBases hp₁ g b) c) =
          ∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4, bondKernel R.params R.coupling X U b c := by
        let eB : ((stepBlockFrame R.params.side n).Cell × Fin 4) ≃ ((stepBlockFrame R.params.side n).Cell × Fin 4) :=
          Equiv.ofBijective (imageBond g) (Finite.injective_iff_bijective.mp (imageBond_injective hp₁ g))
        exact (Fintype.prod_equiv eB _ _ fun c => (hbond b hb c).symm).symm
      exact congrArg₂ (· * ·) e1 hprod
    · have e1 : baseLaw (R := R) W' (baseChoiceEquiv R n g b) = 0 :=
        baseLaw_of_not_mem (R := R) (W := W') (b := baseChoiceEquiv R n g b) fun h => hb ((hiff b).mp h)
      have e2 : baseLaw (R := R) W b = 0 := baseLaw_of_not_mem (R := R) (W := W) (b := b) hb
      refine (congrArg (· * _) e1).trans ((zero_mul _).trans ?_)
      exact ((congrArg (· * _) e2).trans (zero_mul _)).symm
  · intro hb₀ Y
    have hb : b ∈ baseChoices R.params X := by
      by_contra hc
      exact hb₀ (baseLaw_of_not_mem (R := R) (W := W) (b := b) hc)
    have himg : ∀ c : TorusBond n,
        bondScore R.params R.coupling W' V' (imageBases hp₁ g b) (imageTorusBond g c) =
          bondScore R.params R.coupling W V b c := by
      intro c
      have hfr := imageBond_torusSiteInFrame (n := n) R.params.side g c
      have hm : bondMean R.params X' (imageBases hp₁ g b) (imageTorusBond g c) =
          contourMean R.params.baseDepth (fineHotLumps R.params X') (imageBases hp₁ g b) X'
            (imageBond g (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c.1, c.2)) := by
        rw [hfr]
        rfl
      have hm₀ : bondMean R.params X b c = contourMean R.params.baseDepth (fineHotLumps R.params X) b X
          (torusSiteInFrame (stepBlockFrame R.params.side n) 1 c.1, c.2) := rfl
      rcases g.axisSign_unit (g.imageAxis c.2) with hs | hs
      · have e1 : bondMean R.params X' (imageBases hp₁ g b) (imageTorusBond g c) = bondMean R.params X b c :=
          hm.trans (((hmeans b hb _).1 hs).trans hm₀.symm)
        have e2 : V' (imageTorusBond g c).1 (imageTorusBond g c).2 = V c.1 c.2 := by
          have h1 := hV c.1 c.2
          have hs' : g.axisSign (g.axisPerm.symm c.2) = 1 := hs
          rw [if_pos hs'] at h1
          simp only [imageTorusBond, hs, if_true]
          exact h1
        exact bondScore_eq_of hS hfit (congrArg norm e1)
          (congrArg₂ (fun (q : ℍ[ℝ]) (v : UnitQuaternion) => (q * ((v⁻¹ : UnitQuaternion) : ℍ[ℝ])).re) e1 e2)
      · have hne : g.axisSign (g.imageAxis c.2) ≠ 1 := by rw [hs]; omega
        have e1 : bondMean R.params X' (imageBases hp₁ g b) (imageTorusBond g c) = star (bondMean R.params X b c) :=
          hm.trans (((hmeans b hb _).2 hs).trans (congrArg star hm₀.symm))
        have e2 : V' (imageTorusBond g c).1 (imageTorusBond g c).2 = (V c.1 c.2)⁻¹ := by
          have h1 := hV c.1 c.2
          have hs' : ¬ g.axisSign (g.axisPerm.symm c.2) = 1 := hne
          rw [if_neg hs'] at h1
          simp only [imageTorusBond, hne, if_false]
          rw [← h1, inv_inv]
          rfl
        exact bondScore_eq_of hS hfit ((congrArg norm e1).trans (norm_star _))
          ((congrArg₂ (fun (q : ℍ[ℝ]) (v : UnitQuaternion) => (q * ((v⁻¹ : UnitQuaternion) : ℍ[ℝ])).re) e1 e2).trans
            (re_star_mul_inv_inv _ _))
    unfold blockBondScores
    refine (Fintype.sum_equiv g.axisPerm.symm _ _ fun k => ?_).symm
    show bondScore R.params R.coupling W V b (Y, k) +
        bondScore R.params R.coupling W V b (Y - TorusFields.unitStep n k, k) =
      bondScore R.params R.coupling W' V' (imageBases hp₁ g b) (g.mapSite Y, g.imageAxis k) +
        bondScore R.params R.coupling W' V' (imageBases hp₁ g b)
          (g.mapSite Y - TorusFields.unitStep n (g.imageAxis k), g.imageAxis k)
    rw [← himg (Y, k), ← himg (Y - TorusFields.unitStep n k, k)]
    rcases g.axisSign_unit (g.imageAxis k) with hs | hs
    · have e1 : imageTorusBond g (Y, k) = (g.mapSite Y, g.imageAxis k) := by simp [imageTorusBond, hs]
      have e2 : imageTorusBond g (Y - TorusFields.unitStep n k, k) =
          (g.mapSite Y - TorusFields.unitStep n (g.imageAxis k), g.imageAxis k) := by
        simp [imageTorusBond, hs, mapSite_sub_unitStep_of_pos g Y k hs]
      rw [e1, e2]
    · have hne : g.axisSign (g.imageAxis k) ≠ 1 := by rw [hs]; omega
      have e1 : imageTorusBond g (Y, k) = (g.mapSite Y - TorusFields.unitStep n (g.imageAxis k), g.imageAxis k) := by
        simp [imageTorusBond, hne]
      have e2 : imageTorusBond g (Y - TorusFields.unitStep n k, k) = (g.mapSite Y, g.imageAxis k) := by
        simp [imageTorusBond, hne, mapSite_sub_unitStep_of_neg g Y k hs]
      rw [e1, e2, add_comm]
end Scores
end TorusSymmetry
namespace WeightedResponses
open TorusFields TorusLumps StepSettings StepCosts TorusSymmetry
theorem isometriesPreserveScores (hS : BondScoreProperties) : isometriesPreserveScoresStatement := by
  intro R hfit n _ hn g
  exact ⟨parentBlock_mapSite_scaledLift R.params.side hfit.L_odd g, baseChoiceEquiv R n g, fun W W' V V' hW hV b =>
    weight_and_scores_transport hS hfit hn g W W' V V' hW hV b⟩
end WeightedResponses
end YangMills.Construction
end
