import YangMills.Construction.ClusterExpansionOfAStep.BlocksReadTheirBoxesProof
import YangMills.Construction.ClusterExpansionOfAStep.IsometriesCarryTheKernel
import YangMills.Construction.ClusterExpansionOfAStep.IsometriesOfTheEnergy
import YangMills.Construction.ClusterExpansionOfAStep.TranslationsCarryTheKernelAtBases
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.TranslationKernel
open BlockAverages LumpContours TorusContours TorusFields TorusLumps StepCosts BaseTranslations
def linearPart (g : TorusIsometry) (z : Fin 4 → ℤ) : Fin 4 → ℤ := fun i => g.axisSign i * z (g.axisPerm i)
theorem axisSign_mul_self (g : TorusIsometry) (i : Fin 4) : g.axisSign i * g.axisSign i = 1 := by
  rcases g.axisSign_unit i with h | h <;> simp [h]
theorem linearPart_add (g : TorusIsometry) (a b : Fin 4 → ℤ) :
    linearPart g (a + b) = linearPart g a + linearPart g b := by
  funext i
  simp [linearPart, mul_add]
theorem linearPart_neg (g : TorusIsometry) (a : Fin 4 → ℤ) : linearPart g (-a) = - linearPart g a := by
  funext i
  simp [linearPart]
theorem linearPart_single (g : TorusIsometry) (k : Fin 4) (c : ℤ) :
    linearPart g (Pi.single k c) = Pi.single (g.imageAxis k) (g.axisSign (g.imageAxis k) * c) := by
  funext i
  by_cases h : i = g.imageAxis k
  · subst h
    simp [linearPart, TorusIsometry.imageAxis]
  · have hk : g.axisPerm i ≠ k := fun e => h (by simp [TorusIsometry.imageAxis, ← e])
    simp [linearPart, h, hk]
def linearPartInv (g : TorusIsometry) (z : Fin 4 → ℤ) : Fin 4 → ℤ :=
  fun q => g.axisSign (g.imageAxis q) * z (g.imageAxis q)
theorem linearPart_linearPartInv (g : TorusIsometry) (z : Fin 4 → ℤ) : linearPart g (linearPartInv g z) = z := by
  funext i
  have h : g.imageAxis (g.axisPerm i) = i := by simp [TorusIsometry.imageAxis]
  simp only [linearPart, linearPartInv, h, ← mul_assoc, axisSign_mul_self, one_mul]
theorem linearPartInv_linearPart (g : TorusIsometry) (z : Fin 4 → ℤ) : linearPartInv g (linearPart g z) = z := by
  funext q
  have h : g.axisPerm (g.imageAxis q) = q := by simp [TorusIsometry.imageAxis]
  simp only [linearPart, linearPartInv, h, ← mul_assoc, axisSign_mul_self, one_mul]
theorem linearPart_mem_centredCube (g : TorusIsometry) {M : ℕ} {z : Fin 4 → ℤ} (hz : z ∈ centredCube M) :
    linearPart g z ∈ centredCube M := by
  rw [mem_centredCube_iff] at hz ⊢
  intro i
  have := hz (g.axisPerm i)
  rcases g.axisSign_unit i with h | h <;> simp only [linearPart, h, one_mul, neg_mul] <;> omega
theorem linearPartInv_mem_centredCube (g : TorusIsometry) {M : ℕ} {z : Fin 4 → ℤ} (hz : z ∈ centredCube M) :
    linearPartInv g z ∈ centredCube M := by
  rw [mem_centredCube_iff] at hz ⊢
  intro q
  have := hz (g.imageAxis q)
  rcases g.axisSign_unit (g.imageAxis q) with h | h <;> simp only [linearPartInv, h, one_mul, neg_mul] <;> omega
variable {F : BlockFrame} {j m : ℕ}
def siteMap (g : TorusIsometry) (u : Fin 4 → ℤ) (x : F.Site j) : F.Site j :=
  siteOfCoords j (linearPart g (siteCoords x) + u)
variable [∀ j i, NeZero (F.period j i)]
theorem intCast_siteCoords_siteOfCoords (hp : ∀ i, F.period j i = m) (z : Fin 4 → ℤ) (k : Fin 4) :
    ((siteCoords (siteOfCoords j z : F.Site j) k : ℤ) : ZMod m) = (z k : ZMod m) := by
  have h := intCast_cast_intCast_of_eq (hp k) (z k)
  exact h
theorem siteOfCoords_congr (hp : ∀ i, F.period j i = m) {a b : Fin 4 → ℤ}
    (h : ∀ i, (a i : ZMod m) = (b i : ZMod m)) :
    (siteOfCoords j a : F.Site j) = siteOfCoords j b := by
  funext i
  simp only [siteOfCoords]
  have := h i
  rw [← hp i] at this
  exact this
theorem siteOfCoords_eq_iff (hp : ∀ i, F.period j i = m) {a b : Fin 4 → ℤ} :
    (siteOfCoords j a : F.Site j) = siteOfCoords j b ↔ ∀ i, (a i : ZMod m) = (b i : ZMod m) := by
  refine ⟨fun h i => ?_, siteOfCoords_congr hp⟩
  have := congrFun h i
  simp only [siteOfCoords] at this
  rw [hp i] at this
  exact this
theorem siteMap_siteOfCoords (hp : ∀ i, F.period j i = m) (g : TorusIsometry) (u z : Fin 4 → ℤ) :
    (siteMap g u (siteOfCoords j z : F.Site j) : F.Site j) = siteOfCoords j (linearPart g z + u) := by
  refine siteOfCoords_congr hp fun i => ?_
  simp only [linearPart, Pi.add_apply]
  push_cast
  rw [intCast_siteCoords_siteOfCoords hp]
theorem siteMap_add (hp : ∀ i, F.period j i = m) (g : TorusIsometry) (u d : Fin 4 → ℤ) (x : F.Site j) :
    (siteMap g u (x + siteOfCoords j d) : F.Site j) = siteMap g u x + siteOfCoords j (linearPart g d) := by
  conv_lhs => rw [← TorusContours.siteOfCoords_siteCoords x, ← TorusContours.siteOfCoords_add, siteMap_siteOfCoords hp,
    linearPart_add]
  rw [siteMap, ← TorusContours.siteOfCoords_add]
  congr 1
  abel
theorem siteMap_injective (hp : ∀ i, F.period j i = m) (g : TorusIsometry) (u : Fin 4 → ℤ) :
    Function.Injective (siteMap g u : F.Site j → F.Site j) := by
  intro x x' h
  rw [siteMap, siteMap, siteOfCoords_eq_iff hp] at h
  have hc : ∀ i, ((siteCoords x (g.axisPerm i) : ℤ) : ZMod m) = (siteCoords x' (g.axisPerm i) : ℤ) := by
    intro i
    have h1 := h i
    simp only [linearPart, Pi.add_apply] at h1
    push_cast at h1
    have h2 := add_right_cancel h1
    rcases g.axisSign_unit i with hs | hs
    · simpa [hs] using h2
    · simpa [hs] using h2
  have : (siteOfCoords j (siteCoords x) : F.Site j) = siteOfCoords j (siteCoords x') := by
    refine siteOfCoords_congr hp fun q => ?_
    have := hc (g.imageAxis q)
    simpa [TorusIsometry.imageAxis] using this
  rwa [TorusContours.siteOfCoords_siteCoords, TorusContours.siteOfCoords_siteCoords] at this
def siteMapEquiv (hp : ∀ i, F.period j i = m) (g : TorusIsometry) (u : Fin 4 → ℤ) : F.Site j ≃ F.Site j :=
  Equiv.ofBijective (siteMap g u) (Finite.injective_iff_bijective.mp (siteMap_injective hp g u))
theorem siteMapEquiv_apply (hp : ∀ i, F.period j i = m) (g : TorusIsometry) (u : Fin 4 → ℤ) (x : F.Site j) :
    siteMapEquiv hp g u x = siteMap g u x := rfl
theorem toTorusSite_siteMap (g : TorusIsometry) (u : Fin 4 → ℤ) (hp : ∀ i, F.period j i = m) (x : F.Site j) :
    (toTorusSite m (siteMap g u x : F.Site j) : TorusSite m) =
      TorusIsometry.mapSite ⟨g.axisPerm, g.axisSign, u, g.axisSign_unit⟩ (toTorusSite m x) := by
  rw [siteMap, toTorusSite_siteOfCoords hp]
  funext k
  simp [siteOfInt, linearPart, TorusIsometry.mapSite, toTorusSite]
def mapPathStep (g : TorusIsometry) (st : PathStep) : PathStep :=
  (g.imageAxis st.1, if g.axisSign (g.imageAxis st.1) = 1 then st.2 else !st.2)
theorem stepDisplacement_eq (st : PathStep) :
    (stepDisplacement j st : F.Site j) = siteOfCoords j (Pi.single st.1 (if st.2 then 1 else -1)) := by
  obtain ⟨k, f⟩ := st
  cases f
  · simp only [stepDisplacement, Bool.false_eq_true, if_false, BlockAverages.unitStep]
    rw [← TorusContours.siteOfCoords_neg]
    congr 1
    funext i
    by_cases h : i = k
    · subst h
      simp
    · simp [h]
  · simp [stepDisplacement, BlockAverages.unitStep]
theorem siteMap_add_stepDisplacement (hp : ∀ i, F.period j i = m) (g : TorusIsometry) (u : Fin 4 → ℤ)
    (x : F.Site j) (st : PathStep) :
    (siteMap g u (x + stepDisplacement j st) : F.Site j) = siteMap g u x + stepDisplacement j (mapPathStep g st) := by
  rw [stepDisplacement_eq, siteMap_add hp, linearPart_single, stepDisplacement_eq]
  congr 2
  obtain ⟨k, f⟩ := st
  rcases g.axisSign_unit (g.imageAxis k) with h | h <;> cases f <;> simp [mapPathStep, h]
def FieldTransported (g : TorusIsometry) (u : Fin 4 → ℤ) (X X' : F.GaugeField j) : Prop :=
  ∀ x k, if g.axisSign (g.imageAxis k) = 1 then X' (siteMap g u x) (g.imageAxis k) = X x k
    else (X' (siteMap g u x - BlockAverages.unitStep j (g.imageAxis k)) (g.imageAxis k))⁻¹ = X x k
theorem linkValue_mapPathStep (hp : ∀ i, F.period j i = m) {g : TorusIsometry} {u : Fin 4 → ℤ}
    {X X' : F.GaugeField j} (h : FieldTransported g u X X') (x : F.Site j) (st : PathStep) :
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
    {X X' : F.GaugeField j} (h : FieldTransported g u X X') (x : F.Site j) (l : List PathStep) :
    pathHolonomy X' (siteMap g u x) (l.map (mapPathStep g)) = pathHolonomy X x l := by
  induction l generalizing x with
  | nil => rfl
  | cons st r ih =>
    simp only [List.map_cons, pathHolonomy]
    rw [linkValue_mapPathStep hp h, ← siteMap_add_stepDisplacement hp, ih]
theorem pathSites_map (hp : ∀ i, F.period j i = m) (g : TorusIsometry) (u : Fin 4 → ℤ) (x : F.Site j)
    (l : List PathStep) :
    pathSites (siteMap g u x) (l.map (mapPathStep g)) = (pathSites x l).map (siteMap g u) := by
  induction l generalizing x with
  | nil => rfl
  | cons st r ih =>
    simp only [List.map_cons, pathSites]
    rw [← siteMap_add_stepDisplacement hp, ih]
theorem axisPath_map (g : TorusIsometry) (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) :
    (axisPath h π).map (mapPathStep g) = axisPath (linearPart g h) (π.trans g.axisPerm.symm) := by
  unfold axisPath
  rw [List.map_flatMap]
  congr 1
  funext k
  rw [List.map_replicate]
  have hq : (π.trans g.axisPerm.symm) k = g.imageAxis (π k) := rfl
  have hl : linearPart g h (g.imageAxis (π k)) = g.axisSign (g.imageAxis (π k)) * h (π k) := by
    simp [linearPart, TorusIsometry.imageAxis]
  rw [hq, hl]
  by_cases h0 : h (π k) = 0
  · simp [h0]
  · rcases g.axisSign_unit (g.imageAxis (π k)) with hs | hs
    · simp [hs, mapPathStep]
    · have hne : g.axisSign (g.imageAxis (π k)) ≠ 1 := by rw [hs]; omega
      have hd : (!decide (0 ≤ h (π k))) = decide (0 ≤ -h (π k)) := by
        by_cases hh : 0 ≤ h (π k)
        · have : ¬ 0 ≤ -h (π k) := by omega
          simp [hh, this]
          omega
        · have : 0 ≤ -h (π k) := by omega
          simp [hh, this]
          omega
      simp [hs, mapPathStep, hd]
section Geometry
theorem natAbs_valMinAbs_congr {p q : ℕ} (h : p = q) (z : ℤ) :
    (((z : ZMod p)).valMinAbs).natAbs = (((z : ZMod q)).valMinAbs).natAbs := by
  subst h
  rfl
theorem supDist_eq (hp : ∀ i, F.period j i = m) (x y : F.Site j) :
    supDist x y = Finset.univ.sup fun i =>
      ((((siteCoords x i - siteCoords y i : ℤ) : ZMod m)).valMinAbs).natAbs := by
  unfold LumpContours.supDist
  refine Finset.sup_congr rfl fun i _ => ?_
  have e : x i - y i = ((siteCoords x i - siteCoords y i : ℤ) : ZMod (F.period j i)) := by
    push_cast
    rw [intCast_siteCoords, intCast_siteCoords]
  rw [e]
  exact natAbs_valMinAbs_congr (hp i) _
theorem supDist_siteMap (hp : ∀ i, F.period j i = m) (g : TorusIsometry) (u : Fin 4 → ℤ) (x y : F.Site j) :
    supDist (siteMap g u x : F.Site j) (siteMap g u y) = supDist x y := by
  rw [supDist_eq hp, supDist_eq hp]
  have key : ∀ i, ((((siteCoords (siteMap g u x : F.Site j) i - siteCoords (siteMap g u y : F.Site j) i : ℤ) :
      ZMod m)).valMinAbs).natAbs =
      ((((siteCoords x (g.axisPerm i) - siteCoords y (g.axisPerm i) : ℤ) : ZMod m)).valMinAbs).natAbs := by
    intro i
    have e : (((siteCoords (siteMap g u x : F.Site j) i - siteCoords (siteMap g u y : F.Site j) i : ℤ)) : ZMod m) =
        ((g.axisSign i * (siteCoords x (g.axisPerm i) - siteCoords y (g.axisPerm i)) : ℤ) : ZMod m) := by
      push_cast
      rw [siteMap, siteMap, intCast_siteCoords_siteOfCoords hp, intCast_siteCoords_siteOfCoords hp]
      simp only [linearPart, Pi.add_apply]
      push_cast
      ring
    rw [e]
    rcases g.axisSign_unit i with hs | hs
    · simp [hs]
    · simp only [hs, neg_mul, one_mul, Int.cast_neg, ZMod.natAbs_valMinAbs_neg]
  simp only [key]
  apply le_antisymm
  · refine Finset.sup_le fun i _ => ?_
    exact Finset.le_sup (f := fun i => ((((siteCoords x i - siteCoords y i : ℤ) : ZMod m)).valMinAbs).natAbs)
      (Finset.mem_univ (g.axisPerm i))
  · refine Finset.sup_le fun q _ => ?_
    have := Finset.le_sup (f := fun i =>
      ((((siteCoords x (g.axisPerm i) - siteCoords y (g.axisPerm i) : ℤ) : ZMod m)).valMinAbs).natAbs)
      (Finset.mem_univ (g.imageAxis q))
    simpa [TorusIsometry.imageAxis] using this
def imageBoxLower (g : TorusIsometry) (u lo hi : Fin 4 → ℤ) : Fin 4 → ℤ :=
  fun i => if g.axisSign i = 1 then lo (g.axisPerm i) + u i else - hi (g.axisPerm i) + u i
def imageBoxUpper (g : TorusIsometry) (u lo hi : Fin 4 → ℤ) : Fin 4 → ℤ :=
  fun i => if g.axisSign i = 1 then hi (g.axisPerm i) + u i else - lo (g.axisPerm i) + u i
theorem image_boxSites (hp : ∀ i, F.period j i = m) (g : TorusIsometry) (u lo hi : Fin 4 → ℤ) :
    (boxSites j lo hi : Finset (F.Site j)).image (siteMap g u) =
      boxSites j (imageBoxLower g u lo hi) (imageBoxUpper g u lo hi) := by
  ext x
  simp only [boxSites, Finset.mem_image, Fintype.mem_piFinset, Finset.mem_Icc]
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨linearPart g z + u, fun i => ?_, (siteMap_siteOfCoords hp g u z).symm⟩
    have := hz (g.axisPerm i)
    rcases g.axisSign_unit i with hs | hs
    · simp only [imageBoxLower, imageBoxUpper, linearPart, Pi.add_apply, hs, if_true, one_mul]
      omega
    · have hne : (-1 : ℤ) ≠ 1 := by omega
      simp only [imageBoxLower, imageBoxUpper, linearPart, Pi.add_apply, hs, hne, if_false, neg_mul, one_mul]
      omega
  · rintro ⟨w, hw, rfl⟩
    refine ⟨siteOfCoords j (linearPartInv g (w - u)), ⟨linearPartInv g (w - u), fun q => ?_, rfl⟩, ?_⟩
    · have := hw (g.imageAxis q)
      have hpq : g.axisPerm (g.imageAxis q) = q := by simp [TorusIsometry.imageAxis]
      rcases g.axisSign_unit (g.imageAxis q) with hs | hs
      · simp only [imageBoxLower, imageBoxUpper, hs, if_true, hpq] at this
        simp only [linearPartInv, hs, Pi.sub_apply, one_mul]
        omega
      · have hne : (-1 : ℤ) ≠ 1 := by omega
        simp only [imageBoxLower, imageBoxUpper, hs, hne, if_false, hpq] at this
        simp only [linearPartInv, hs, Pi.sub_apply, neg_mul, one_mul]
        omega
    · rw [siteMap_siteOfCoords hp, linearPart_linearPartInv]
      simp
theorem isSmallBox_image (hp : ∀ i, F.period j i = m) (g : TorusIsometry) (u : Fin 4 → ℤ)
    {B : Finset (F.Site j)} (hB : IsSmallBox F B) : IsSmallBox F (B.image (siteMap g u)) := by
  obtain ⟨lo, hi, h, rfl⟩ := hB
  refine ⟨imageBoxLower g u lo hi, imageBoxUpper g u lo hi, fun i => ?_, image_boxSites hp g u lo hi⟩
  have := h (g.axisPerm i)
  rcases g.axisSign_unit i with hs | hs
  · simp only [imageBoxLower, imageBoxUpper, hs, if_true]
    omega
  · have hne : (-1 : ℤ) ≠ 1 := by omega
    simp only [imageBoxLower, imageBoxUpper, hs, hne, if_false]
    omega
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
  have e3 := image_boxSites (F := F) hp g u lo₂ hi₂
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
theorem image_image_symm (S : Finset (F.Site j)) : (S.image e).image e.symm = S := by
  ext x
  simp
omit [∀ j i, NeZero (F.period j i)] in
theorem image_symm_image (S : Finset (F.Site j)) : (S.image e.symm).image e = S := by
  ext x
  simp
omit [∀ j i, NeZero (F.period j i)] in
theorem isSeparatedCover_image (hbox : ∀ B : Finset (F.Site j), IsSmallBox F B → IsSmallBox F (B.image e))
    (hd : ∀ x y : F.Site j, supDist (e x) (e y) = supDist x y)
    {seeds Z : Finset (Finset (F.Site j))} (h : IsSeparatedCover seeds Z) :
    IsSeparatedCover (seeds.image (Finset.image e)) (Z.image (Finset.image e)) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro B hB
    obtain ⟨B₀, hB₀, rfl⟩ := Finset.mem_image.mp hB
    exact hbox _ (h1 _ hB₀)
  · intro l hl
    obtain ⟨l₀, hl₀, rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨B, hB, hs⟩ := h2 _ hl₀
    exact ⟨_, Finset.mem_image_of_mem _ hB, Finset.image_subset_image hs⟩
  · intro B hB B' hB' hne hw
    obtain ⟨B₀, hB₀, rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨B₁, hB₁, rfl⟩ := Finset.mem_image.mp hB'
    have hne' : B₀ ≠ B₁ := fun e' => hne (by rw [e'])
    obtain ⟨x, hx, y, hy, hxy⟩ := hw
    obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y₀, hy₀, rfl⟩ := Finset.mem_image.mp hy
    rw [hd] at hxy
    exact h3 _ hB₀ _ hB₁ hne' ⟨x₀, hx₀, y₀, hy₀, hxy⟩
omit [∀ j i, NeZero (F.period j i)] in
theorem image_image_symm_family (S : Finset (Finset (F.Site j))) :
    (S.image (Finset.image e)).image (Finset.image e.symm) = S := by
  ext B
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨_, ⟨B₀, hB₀, rfl⟩, rfl⟩
    rwa [image_image_symm]
  · intro hB
    exact ⟨_, ⟨B, hB, rfl⟩, image_image_symm B⟩
omit [∀ j i, NeZero (F.period j i)] in
theorem isLeastSeparatedCover_image
    (hbox : ∀ B : Finset (F.Site j), IsSmallBox F B → IsSmallBox F (B.image e))
    (hbox' : ∀ B : Finset (F.Site j), IsSmallBox F B → IsSmallBox F (B.image e.symm))
    (hd : ∀ x y : F.Site j, supDist (e x) (e y) = supDist x y)
    {seeds Z : Finset (Finset (F.Site j))} (h : IsLeastSeparatedCover seeds Z) :
    IsLeastSeparatedCover (seeds.image (Finset.image e)) (Z.image (Finset.image e)) := by
  have hd' : ∀ x y : F.Site j, supDist (e.symm x) (e.symm y) = supDist x y := by
    intro x y
    have := hd (e.symm x) (e.symm y)
    simpa using this.symm
  refine ⟨isSeparatedCover_image hbox hd h.1, fun Z' hZ' B hB => ?_⟩
  obtain ⟨B₀, hB₀, rfl⟩ := Finset.mem_image.mp hB
  have hc := isSeparatedCover_image (e := e.symm) hbox' hd' hZ'
  rw [image_image_symm_family] at hc
  obtain ⟨B₁, hB₁, hs⟩ := h.2 _ hc B₀ hB₀
  obtain ⟨B₂, hB₂, rfl⟩ := Finset.mem_image.mp hB₁
  refine ⟨B₂, hB₂, ?_⟩
  have := Finset.image_subset_image (f := e) hs
  rwa [image_symm_image] at this
omit [∀ j i, NeZero (F.period j i)] in
theorem isLeastSeparatedCover_subset {seeds Z Z' : Finset (Finset (F.Site j))}
    (h : IsLeastSeparatedCover seeds Z) (h' : IsLeastSeparatedCover seeds Z') : Z ⊆ Z' := by apply _root_.YangMills.Construction.BlockLocality.leastCover_subset <;> assumption
omit [∀ j i, NeZero (F.period j i)] in
theorem mergedBoxes_image (hbox : ∀ B : Finset (F.Site j), IsSmallBox F B → IsSmallBox F (B.image e))
    (hbox' : ∀ B : Finset (F.Site j), IsSmallBox F B → IsSmallBox F (B.image e.symm))
    (hd : ∀ x y : F.Site j, supDist (e x) (e y) = supDist x y) (seeds : Finset (Finset (F.Site j))) :
    mergedBoxes (seeds.image (Finset.image e)) = (mergedBoxes seeds).image (Finset.image e) := by
  have hd' : ∀ x y : F.Site j, supDist (e.symm x) (e.symm y) = supDist x y := by
    intro x y
    have := hd (e.symm x) (e.symm y)
    simpa using this.symm
  classical
  unfold mergedBoxes
  by_cases h : ∃ Z, IsLeastSeparatedCover seeds Z
  · have h2 : ∃ Z, IsLeastSeparatedCover (seeds.image (Finset.image e)) Z :=
      ⟨_, isLeastSeparatedCover_image hbox hbox' hd h.choose_spec⟩
    rw [dif_pos h, dif_pos h2]
    exact Finset.Subset.antisymm
      (isLeastSeparatedCover_subset h2.choose_spec (isLeastSeparatedCover_image hbox hbox' hd h.choose_spec))
      (isLeastSeparatedCover_subset (isLeastSeparatedCover_image hbox hbox' hd h.choose_spec) h2.choose_spec)
  · have h2 : ¬ ∃ Z, IsLeastSeparatedCover (seeds.image (Finset.image e)) Z := by
      rintro ⟨Z, hZ⟩
      have := isLeastSeparatedCover_image (e := e.symm) hbox' (by simpa using hbox) hd' hZ
      rw [image_image_symm_family] at this
      exact h ⟨_, this⟩
    rw [dif_neg h, dif_neg h2]
    simp
end Cover
section Lumps
variable {L : ℕ}
theorem offsetFromCentre_neg (hL : 0 < L) (hodd : Odd L) (c : ℤ) :
    offsetFromCentre L (-c) = - offsetFromCentre L c := by
  obtain ⟨h1, h2⟩ := offsetFromCentre_spec hL hodd c
  have e : -c = -(c - offsetFromCentre L c) + -offsetFromCentre L c := by ring
  rw [e]
  exact offsetFromCentre_add_of_dvd hL hodd _ _ ((dvd_neg).mpr h1) (by rwa [abs_neg])
def stripEnd (g : LumpGrid L) (c : ℤ) : ℤ := c - offsetFromCentre L c + g.upper (offsetFromCentre L c)
theorem stripEnd_add_dvd (hL : 0 < L) (hodd : Odd L) (g : LumpGrid L) (c b : ℤ) (hb : (L : ℤ) ∣ b) :
    stripEnd g (c + b) = stripEnd g c + b := by
  unfold stripEnd
  rw [offsetFromCentre_add_dvd hL hodd c b hb]
  ring
theorem stripStart_neg (hL : 0 < L) (hodd : Odd L) (g : LumpGrid L) (c : ℤ) :
    stripStart g (-c) = - stripEnd g c := by
  unfold stripStart stripEnd
  obtain ⟨_, h2⟩ := offsetFromCentre_spec hL hodd c
  rw [offsetFromCentre_neg hL hodd, g.lower_neg _ h2]
  ring
theorem stripEnd_neg (hL : 0 < L) (hodd : Odd L) (g : LumpGrid L) (c : ℤ) :
    stripEnd g (-c) = - stripStart g c := by
  unfold stripStart stripEnd
  obtain ⟨_, h2⟩ := offsetFromCentre_spec hL hodd c
  have h3 : |(-offsetFromCentre L c)| ≤ ((L : ℤ) - 1) / 2 := by rwa [abs_neg]
  have h4 := g.lower_neg _ h3
  rw [neg_neg] at h4
  rw [offsetFromCentre_neg hL hodd, h4]
  ring
theorem boxSites_add_period (hp : ∀ i, F.period j i = m) (lo hi k : Fin 4 → ℤ) :
    (boxSites j (fun i => lo i + m * k i) (fun i => hi i + m * k i) : Finset (F.Site j)) = boxSites j lo hi := by
  ext x
  simp only [boxSites, Finset.mem_image, Fintype.mem_piFinset, Finset.mem_Icc]
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨fun i => z i - m * k i, fun i => ?_, ?_⟩
    · have := hz i
      constructor <;> linarith [this.1, this.2]
    · refine siteOfCoords_congr hp fun i => ?_
      simp
  · rintro ⟨z, hz, rfl⟩
    refine ⟨fun i => z i + m * k i, fun i => ?_, ?_⟩
    · have := hz i
      constructor <;> linarith [this.1, this.2]
    · refine siteOfCoords_congr hp fun i => ?_
      simp
theorem lumpOf_eq (g : LumpGrid L) (x : F.Site j) :
    lumpOf g x = boxSites j (fun i => stripStart g (siteCoords x i)) (fun i => stripEnd g (siteCoords x i)) := rfl
theorem siteCoords_siteMap (hp : ∀ i, F.period j i = m) (G : TorusIsometry) (u : Fin 4 → ℤ) (x : F.Site j) :
    ∃ k : Fin 4 → ℤ, ∀ i, siteCoords (siteMap G u x : F.Site j) i = (linearPart G (siteCoords x) + u) i + m * k i := by
  have h : ∀ i, ∃ c : ℤ, siteCoords (siteMap G u x : F.Site j) i = (linearPart G (siteCoords x) + u) i + m * c := by
    intro i
    have h1 := intCast_siteCoords_siteOfCoords (F := F) (j := j) hp (linearPart G (siteCoords x) + u) i
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
    obtain ⟨c, hc⟩ := h1
    refine ⟨-c, ?_⟩
    simp only [siteMap]
    linear_combination -hc
  choose k hk using h
  exact ⟨k, hk⟩
theorem lumpOf_siteMap (hL : 0 < L) (hodd : Odd L) (hp : ∀ i, F.period j i = m) (hm : (L : ℤ) ∣ m)
    (G : TorusIsometry) (u : Fin 4 → ℤ) (hu : ∀ i, (L : ℤ) ∣ u i) (g : LumpGrid L) (x : F.Site j) :
    lumpOf g (siteMap G u x : F.Site j) = (lumpOf g x).image (siteMap G u) := by
  obtain ⟨k, hk⟩ := siteCoords_siteMap hp G u x
  rw [lumpOf_eq, lumpOf_eq, image_boxSites hp,
    ← boxSites_add_period hp (imageBoxLower G u _ _) (imageBoxUpper G u _ _) k]
  have hb : ∀ i, (L : ℤ) ∣ u i + m * k i := fun i => dvd_add (hu i) (Dvd.dvd.mul_right hm _)
  congr 1
  · funext i
    rw [hk i]
    simp only [linearPart, Pi.add_apply, imageBoxLower]
    rcases G.axisSign_unit i with hs | hs
    · have : G.axisSign i * siteCoords x (G.axisPerm i) + u i + m * k i =
          siteCoords x (G.axisPerm i) + (u i + m * k i) := by
        rw [hs]
        ring
      rw [this, stripStart_add_dvd hL hodd g _ _ (hb i), if_pos hs]
      ring
    · have : G.axisSign i * siteCoords x (G.axisPerm i) + u i + m * k i =
          - siteCoords x (G.axisPerm i) + (u i + m * k i) := by
        rw [hs]
        ring
      have hne : G.axisSign i ≠ 1 := by rw [hs]; omega
      rw [this, stripStart_add_dvd hL hodd g _ _ (hb i), if_neg hne, stripStart_neg hL hodd]
      ring
  · funext i
    rw [hk i]
    simp only [linearPart, Pi.add_apply, imageBoxUpper]
    rcases G.axisSign_unit i with hs | hs
    · have : G.axisSign i * siteCoords x (G.axisPerm i) + u i + m * k i =
          siteCoords x (G.axisPerm i) + (u i + m * k i) := by
        rw [hs]
        ring
      rw [this, stripEnd_add_dvd hL hodd g _ _ (hb i), if_pos hs]
      ring
    · have : G.axisSign i * siteCoords x (G.axisPerm i) + u i + m * k i =
          - siteCoords x (G.axisPerm i) + (u i + m * k i) := by
        rw [hs]
        ring
      have hne : G.axisSign i ≠ 1 := by rw [hs]; omega
      rw [this, stripEnd_add_dvd hL hodd g _ _ (hb i), if_neg hne, stripEnd_neg hL hodd]
      ring
end Lumps
section Paths
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
    (reversePath l).map (mapPathStep g) = reversePath (l.map (mapPathStep g)) := by
  simp only [reversePath, List.map_map, List.map_reverse]
  congr 2
  funext st
  obtain ⟨k, f⟩ := st
  by_cases h : g.axisSign (g.imageAxis k) = 1 <;> simp [mapPathStep, h]
omit [∀ j i, NeZero (F.period j i)] in
theorem mem_pathSites_append (x : F.Site j) (l l' : List PathStep) (z : F.Site j) :
    z ∈ pathSites x (l ++ l') ↔ z ∈ pathSites x l ∨ z ∈ pathSites (pathEndpoint x l) l' := by
  induction l generalizing x with
  | nil =>
    simp only [List.nil_append, pathSites, pathEndpoint, List.mem_singleton]
    constructor
    · exact Or.inr
    · rintro (rfl | h)
      · cases l' <;> simp [pathSites]
      · exact h
  | cons st r ih =>
    simp only [List.cons_append, pathSites, List.mem_cons, pathEndpoint, ih]
    tauto
omit [∀ j i, NeZero (F.period j i)] in
theorem start_mem_pathSites (x : F.Site j) (l : List PathStep) : x ∈ pathSites x l := by
  cases l <;> simp [pathSites]
omit [∀ j i, NeZero (F.period j i)] in
theorem mem_pathSites_reversePath (x : F.Site j) (l : List PathStep) (z : F.Site j) :
    z ∈ pathSites (pathEndpoint x l) (reversePath l) ↔ z ∈ pathSites x l := by
  induction l generalizing x with
  | nil => simp [pathEndpoint, reversePath, pathSites]
  | cons st r ih =>
    have e : reversePath (st :: r) = reversePath r ++ [(st.1, !st.2)] := by
      simp [reversePath]
    have h2 := pathEndpoint_reversePath (x + stepDisplacement j st) r
    have h3 : x + stepDisplacement j st + stepDisplacement j (st.1, !st.2) = x := by
      rw [stepDisplacement_flip]
      abel
    rw [e, mem_pathSites_append, pathEndpoint, ih, h2]
    simp only [pathSites, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, h3]
    have h4 := start_mem_pathSites (x + stepDisplacement j st) r
    constructor
    · rintro (h | rfl | rfl)
      · exact Or.inr h
      · exact Or.inr h4
      · exact Or.inl rfl
    · rintro (rfl | h)
      · exact Or.inr (Or.inr rfl)
      · exact Or.inl h
end Paths
section Contour
variable {m₀ m₁ : ℕ}
def fineOffset (L : ℕ) (g : TorusIsometry) : Fin 4 → ℤ := fun i => (L : ℤ) * g.offset i
abbrev fineMap (g : TorusIsometry) (x : F.Site F.depth) : F.Site F.depth := siteMap g (fineOffset F.blockSide g) x
abbrev coarseMap (g : TorusIsometry) (y : F.Cell) : F.Cell := siteMap g g.offset y
theorem fineMap_cellCentre (hp₀ : ∀ i, F.period F.depth i = m₀) (g : TorusIsometry) (y : F.Cell) :
    fineMap g (cellCentre F.depth y : F.Site F.depth) = cellCentre F.depth (coarseMap g y) := by
  rw [cellCentre_eq, fineMap, siteMap_siteOfCoords hp₀, coarseMap, siteMap, cellCentre_siteOfCoords]
  congr 1
  funext i
  simp only [linearPart, fineOffset, Pi.add_apply]
  ring
theorem fineMap_siteAtOffset (hp₀ : ∀ i, F.period F.depth i = m₀) (g : TorusIsometry) (y : F.Cell)
    (z : Fin 4 → ℤ) :
    fineMap g (siteAtOffset y z : F.Site F.depth) = siteAtOffset (coarseMap g y) (linearPart g z) := by
  unfold siteAtOffset
  rw [fineMap, siteMap_add hp₀, ← fineMap, fineMap_cellCentre hp₀]
theorem minimalOffset_add (hp : ∀ i, F.period j i = m) (x : F.Site j) {d : Fin 4 → ℤ}
    (hd : ∀ i, 2 * |d i| < m) :
    minimalOffset x (x + siteOfCoords j d) = d := by
  funext i
  simp only [minimalOffset, Pi.add_apply, Pi.sub_apply, add_sub_cancel_left, siteOfCoords]
  have hi := hd i
  refine (ZMod.valMinAbs_spec _ _).mpr ⟨rfl, ?_⟩
  rw [hp i, Set.mem_Ioc]
  rcases abs_cases (d i) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] at hi <;> constructor <;> omega
def imageBases (hp₁ : ∀ i, F.period F.top i = m₁) (g : TorusIsometry) (b : F.Cell → F.Site F.depth) :
    F.Cell → F.Site F.depth :=
  fun y => fineMap g (b ((siteMapEquiv hp₁ g g.offset).symm y))
theorem imageBases_coarseMap (hp₁ : ∀ i, F.period F.top i = m₁) (g : TorusIsometry)
    (b : F.Cell → F.Site F.depth) (y : F.Cell) :
    imageBases hp₁ g b (coarseMap g y) = fineMap g (b y) := by
  have : (siteMapEquiv hp₁ g g.offset).symm (coarseMap g y) = y := (siteMapEquiv hp₁ g g.offset).symm_apply_apply y
  rw [imageBases, this]
theorem two_mul_abs_sub_lt {M : ℕ} {a b : Fin 4 → ℤ} (ha : a ∈ centredCube M) (hb : b ∈ centredCube M)
    (hM : 2 * (M : ℤ) ≤ m) (i : Fin 4) : 2 * |(a - b) i| < m := by
  have h1 := mem_centredCube_iff.mp ha i
  have h2 := mem_centredCube_iff.mp hb i
  simp only [Pi.sub_apply]
  rcases abs_cases (a i - b i) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> omega
theorem minimalOffset_eq (hp₀ : ∀ i, F.period F.depth i = m₀) {x : F.Site F.depth} {y : F.Cell}
    {z ξ : Fin 4 → ℤ} (hx : x = siteAtOffset y z) (hz : z ∈ centredCube F.blockSide)
    (hξ : ξ ∈ centredCube F.blockSide) (hM : 2 * (F.blockSide : ℤ) ≤ m₀) :
    minimalOffset x (cellCentre F.depth y + siteOfCoords F.depth ξ) = ξ - z := by
  have e : (cellCentre F.depth y + siteOfCoords F.depth ξ : F.Site F.depth) =
      x + siteOfCoords F.depth (ξ - z) := by
    rw [hx, siteAtOffset, sub_eq_add_neg, TorusContours.siteOfCoords_add, TorusContours.siteOfCoords_neg]
    abel
  rw [e]
  exact minimalOffset_add hp₀ x (two_mul_abs_sub_lt hξ hz hM)
theorem axisPath_image (hp₀ : ∀ i, F.period F.depth i = m₀) (g : TorusIsometry) {x : F.Site F.depth}
    {y : F.Cell} {z ξ : Fin 4 → ℤ} (hx : x = siteAtOffset y z) (hz : z ∈ centredCube F.blockSide)
    (hξ : ξ ∈ centredCube F.blockSide) (hM : 2 * (F.blockSide : ℤ) ≤ m₀) (π : Equiv.Perm (Fin 4)) :
    (axisPath (minimalOffset x (cellCentre F.depth y + siteOfCoords F.depth ξ)) π).map (mapPathStep g) =
      axisPath (minimalOffset (fineMap g x) (cellCentre F.depth (coarseMap g y) +
        siteOfCoords F.depth (linearPart g ξ))) (π.trans g.axisPerm.symm) := by
  have h1 := minimalOffset_eq hp₀ hx hz hξ hM
  have hx' : fineMap g x = siteAtOffset (coarseMap g y) (linearPart g z) := by rw [hx, fineMap_siteAtOffset hp₀]
  have h2 := minimalOffset_eq hp₀ hx' (linearPart_mem_centredCube g hz) (linearPart_mem_centredCube g hξ) hM
  rw [h1, h2, axisPath_map, sub_eq_add_neg, linearPart_add, linearPart_neg, ← sub_eq_add_neg]
def imageBond (g : TorusIsometry) (c : F.Cell × Fin 4) : F.Cell × Fin 4 :=
  (if g.axisSign (g.imageAxis c.2) = 1 then coarseMap g c.1
    else coarseMap g c.1 - BlockAverages.unitStep F.top (g.imageAxis c.2), g.imageAxis c.2)
theorem coarseMap_add_unitStep (hp₁ : ∀ i, F.period F.top i = m₁) (g : TorusIsometry) (y : F.Cell) (k : Fin 4) :
    coarseMap g (y + BlockAverages.unitStep F.top k) =
      coarseMap g y + siteOfCoords F.top (Pi.single (g.imageAxis k) (g.axisSign (g.imageAxis k))) := by
  rw [BlockAverages.unitStep, coarseMap, siteMap_add hp₁, linearPart_single]
  simp
theorem imageBond_of_pos (hp₁ : ∀ i, F.period F.top i = m₁) (g : TorusIsometry) (c : F.Cell × Fin 4)
    (hs : g.axisSign (g.imageAxis c.2) = 1) :
    (imageBond g c).1 = coarseMap g c.1 ∧
      (imageBond g c).1 + BlockAverages.unitStep F.top (imageBond g c).2 =
        coarseMap g (c.1 + BlockAverages.unitStep F.top c.2) := by
  refine ⟨by simp [imageBond, hs], ?_⟩
  rw [coarseMap_add_unitStep hp₁, hs]
  simp [imageBond, hs, BlockAverages.unitStep]
theorem imageBond_of_neg (hp₁ : ∀ i, F.period F.top i = m₁) (g : TorusIsometry) (c : F.Cell × Fin 4)
    (hs : g.axisSign (g.imageAxis c.2) = -1) :
    (imageBond g c).1 = coarseMap g (c.1 + BlockAverages.unitStep F.top c.2) ∧
      (imageBond g c).1 + BlockAverages.unitStep F.top (imageBond g c).2 = coarseMap g c.1 := by
  have hne : g.axisSign (g.imageAxis c.2) ≠ 1 := by rw [hs]; omega
  have e : (siteOfCoords F.top (Pi.single (g.imageAxis c.2) (-1 : ℤ)) : F.Cell) =
      - BlockAverages.unitStep F.top (g.imageAxis c.2) := by
    rw [BlockAverages.unitStep, ← TorusContours.siteOfCoords_neg]
    congr 1
    funext i
    by_cases h : i = g.imageAxis c.2
    · subst h
      simp
    · simp [h]
  refine ⟨?_, ?_⟩
  · rw [coarseMap_add_unitStep hp₁, hs, e]
    simp [imageBond, hne, sub_eq_add_neg]
  · simp [imageBond, hne]
variable (hp₀ : ∀ i, F.period F.depth i = m₀) (hp₁ : ∀ i, F.period F.top i = m₁)
include hp₀ hp₁ in
theorem contourPath_map_of_pos (g : TorusIsometry) {b : F.Cell → F.Site F.depth}
    (hb : ∀ y, ∃ z ∈ centredCube F.blockSide, b y = siteAtOffset y z)
    (hM : 2 * (F.blockSide : ℤ) ≤ m₀) (c : F.Cell × Fin 4) (hs : g.axisSign (g.imageAxis c.2) = 1)
    {ξ : Fin 4 → ℤ} (hξ : ξ ∈ centredCube F.blockSide) (π : Equiv.Perm (Fin 4)) :
    (contourPath b c ξ π).map (mapPathStep g) =
      contourPath (imageBases hp₁ g b) (imageBond g c) (linearPart g ξ) (π.trans g.axisPerm.symm) := by
  obtain ⟨h1, h2⟩ := imageBond_of_pos hp₁ g c hs
  obtain ⟨z₁, hz₁, e₁⟩ := hb c.1
  obtain ⟨z₂, hz₂, e₂⟩ := hb (c.1 + BlockAverages.unitStep F.top c.2)
  unfold contourPath
  rw [h2, h1, imageBases_coarseMap, imageBases_coarseMap, List.map_append, List.map_append, reversePath_map,
    axisPath_image hp₀ g e₁ hz₁ hξ hM, axisPath_image hp₀ g e₂ hz₂ hξ hM, List.map_replicate]
  have : mapPathStep g (c.2, true) = ((imageBond g c).2, true) := by
    simp [mapPathStep, hs, imageBond]
  rw [this]
include hp₀ hp₁ in
theorem contourPath_map_of_neg (g : TorusIsometry) {b : F.Cell → F.Site F.depth}
    (hb : ∀ y, ∃ z ∈ centredCube F.blockSide, b y = siteAtOffset y z)
    (hM : 2 * (F.blockSide : ℤ) ≤ m₀) (c : F.Cell × Fin 4) (hs : g.axisSign (g.imageAxis c.2) = -1)
    {ξ : Fin 4 → ℤ} (hξ : ξ ∈ centredCube F.blockSide) (π : Equiv.Perm (Fin 4)) :
    (contourPath b c ξ π).map (mapPathStep g) =
      reversePath (contourPath (imageBases hp₁ g b) (imageBond g c) (linearPart g ξ)
        (π.trans g.axisPerm.symm)) := by
  obtain ⟨h1, h2⟩ := imageBond_of_neg hp₁ g c hs
  obtain ⟨z₁, hz₁, e₁⟩ := hb c.1
  obtain ⟨z₂, hz₂, e₂⟩ := hb (c.1 + BlockAverages.unitStep F.top c.2)
  have hne : g.axisSign (g.imageAxis c.2) ≠ 1 := by rw [hs]; omega
  unfold contourPath
  rw [h2, h1, imageBases_coarseMap, imageBases_coarseMap, List.map_append, List.map_append, reversePath_map,
    axisPath_image hp₀ g e₁ hz₁ hξ hM, axisPath_image hp₀ g e₂ hz₂ hξ hM, List.map_replicate,
    reversePath_append, reversePath_append, reversePath_reversePath, reversePath_replicate, List.append_assoc]
  have : mapPathStep g (c.2, true) = ((imageBond g c).2, !true) := by
    simp [mapPathStep, hne, imageBond]
  rw [this]
end Contour
section Beside
variable {m₀ m₁ : ℕ} (hp₀ : ∀ i, F.period F.depth i = m₀) (hp₁ : ∀ i, F.period F.top i = m₁)
  (g : TorusIsometry)
abbrev fineEquiv : F.Site F.depth ≃ F.Site F.depth := siteMapEquiv hp₀ g (fineOffset F.blockSide g)
abbrev coarseEquiv : F.Cell ≃ F.Cell := siteMapEquiv hp₁ g g.offset
include hp₀ in
theorem image_sitesBelow (y : F.Cell) :
    (sitesBelow F.depth y).image (fineEquiv hp₀ g) = sitesBelow F.depth (coarseMap g y) := by
  ext x
  simp only [Finset.mem_image, mem_sitesBelow_iff]
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨linearPart g z, linearPart_mem_centredCube g hz, fineMap_siteAtOffset hp₀ g y z⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨_, ⟨linearPartInv g z, linearPartInv_mem_centredCube g hz, rfl⟩, ?_⟩
    rw [siteMapEquiv_apply, ← fineMap, fineMap_siteAtOffset hp₀, linearPart_linearPartInv]
include hp₁ in
theorem image_cellBall (y : F.Cell) (r : ℕ) :
    (LumpContours.cellBall y r).image (coarseEquiv hp₁ g) = LumpContours.cellBall (coarseMap g y) r := by
  ext x
  simp only [LumpContours.cellBall, Finset.mem_image]
  constructor
  · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨linearPart g h, linearPart_mem_centredCube g hh, (siteMap_add hp₁ g _ h y).symm⟩
  · rintro ⟨h, hh, rfl⟩
    refine ⟨_, ⟨linearPartInv g h, linearPartInv_mem_centredCube g hh, rfl⟩, ?_⟩
    rw [siteMapEquiv_apply, siteMap_add hp₁, linearPart_linearPartInv]
include hp₀ in
theorem image_cutBelow (S : Finset F.Cell) :
    (cutBelow F.depth S).image (fineEquiv hp₀ g) = cutBelow F.depth (S.image (coarseEquiv hp₁ g)) := by
  unfold cutBelow
  rw [Finset.image_biUnion, Finset.biUnion_image]
  exact Finset.biUnion_congr rfl fun y _ => image_sitesBelow hp₀ g y
theorem fineEquiv_image_injective : Function.Injective (Finset.image (fineEquiv hp₀ g)) :=
  Finset.image_injective (fineEquiv hp₀ g).injective
include hp₁ in
theorem nearbyLumps_image (h : Finset (Finset (F.Site F.depth))) (y : F.Cell) :
    nearbyLumps (h.image (Finset.image (fineEquiv hp₀ g))) (coarseMap g y) =
      (nearbyLumps h y).image (Finset.image (fineEquiv hp₀ g)) := by
  unfold nearbyLumps
  rw [Finset.filter_image]
  congr 1
  refine Finset.filter_congr fun l _ => ?_
  rw [← image_cellBall hp₁ g y 2, ← image_cutBelow hp₀ hp₁ g]
  exact Finset.image_subset_image_iff (fineEquiv hp₀ g).injective
include hp₁ in
theorem isCrowded_image_iff (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth))) (y : F.Cell) :
    IsCrowded J₀ (h.image (Finset.image (fineEquiv hp₀ g))) (coarseMap g y) ↔ IsCrowded J₀ h y := by
  unfold IsCrowded
  rw [nearbyLumps_image hp₀ hp₁, Finset.card_image_of_injective _ (fineEquiv_image_injective hp₀ g)]
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
    excludedBoxes J₀ (h.image (Finset.image (fineEquiv hp₀ g))) (coarseMap g y) =
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
    (∀ i, (siteMap g u x : F.Site j) i ≠ (siteMap g u b : F.Site j) i) ↔ ∀ q, x q ≠ b q := by
  have key : ∀ i, (siteMap g u x : F.Site j) i = (siteMap g u b : F.Site j) i ↔
      x (g.axisPerm i) = b (g.axisPerm i) := by
    intro i
    have h1 : (siteMap g u x : F.Site j) i = (siteMap g u b : F.Site j) i ↔
        (((linearPart g (siteCoords x) + u) i : ℤ) : ZMod m) =
          (((linearPart g (siteCoords b) + u) i : ℤ) : ZMod m) := by
      simp only [siteMap, siteOfCoords]
      rw [hp i]
    have h2 : x (g.axisPerm i) = b (g.axisPerm i) ↔
        ((siteCoords x (g.axisPerm i) : ℤ) : ZMod m) = ((siteCoords b (g.axisPerm i) : ℤ) : ZMod m) := by
      rw [← intCast_siteCoords x (g.axisPerm i), ← intCast_siteCoords b (g.axisPerm i)]
      have e : ∀ z z' : ℤ, ((z : ZMod (F.period j (g.axisPerm i))) = (z' : ZMod (F.period j (g.axisPerm i)))) ↔
          ((z : ZMod m) = (z' : ZMod m)) := by
        intro z z'
        rw [hp]
      simpa [siteCoords, ZMod.intCast_zmod_cast] using e (siteCoords x (g.axisPerm i)) (siteCoords b (g.axisPerm i))
    rw [h1, h2]
    simp only [linearPart, Pi.add_apply]
    push_cast
    constructor
    · intro h
      have h3 := add_right_cancel h
      rcases g.axisSign_unit i with hs | hs
      · simpa [hs] using h3
      · simpa [hs] using h3
    · intro h
      rw [h]
  constructor
  · intro h
    exact g.axisPerm.surjective.forall.mpr fun i e => h i ((key i).mpr e)
  · intro h i e
    exact h _ ((key i).mp e)
include hp₀ hp₁ in
theorem isBaseChoice_image_iff (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth))) (b : F.Cell → F.Site F.depth) :
    IsBaseChoice J₀ (h.image (Finset.image (fineEquiv hp₀ g))) (imageBases hp₁ g b) ↔ IsBaseChoice J₀ h b := by
  have hcond : ∀ y, (nearbyLumps (h.image (Finset.image (fineEquiv hp₀ g))) (coarseMap g y) = ∅ ∨
      IsCrowded J₀ (h.image (Finset.image (fineEquiv hp₀ g))) (coarseMap g y)) ↔
        (nearbyLumps h y = ∅ ∨ IsCrowded J₀ h y) := by
    intro y
    rw [nearbyLumps_image hp₀ hp₁, isCrowded_image_iff hp₀ hp₁, Finset.image_eq_empty]
  have hcentre : ∀ y, imageBases hp₁ g b (coarseMap g y) = cellCentre F.depth (coarseMap g y) ↔
      b y = cellCentre F.depth y := by
    intro y
    rw [imageBases_coarseMap, ← fineMap_cellCentre hp₀]
    exact (siteMap_injective hp₀ g _).eq_iff
  have hbelow : ∀ y, imageBases hp₁ g b (coarseMap g y) ∈ sitesBelow F.depth (coarseMap g y) ↔
      b y ∈ sitesBelow F.depth y := by
    intro y
    rw [imageBases_coarseMap, ← image_sitesBelow hp₀ g y]
    constructor
    · intro hx
      obtain ⟨w, hw, e⟩ := Finset.mem_image.mp hx
      have : w = b y := (fineEquiv hp₀ g).injective e
      rwa [← this]
    · intro hx
      exact Finset.mem_image_of_mem _ hx
  constructor
  · intro hB y
    have h1 := hB (coarseMap g y)
    refine ⟨fun c => (hcentre y).mp (h1.1 ((hcond y).mpr c)), fun c => ?_⟩
    have h2 := h1.2 (fun e => c ((hcond y).mp e))
    refine ⟨(hbelow y).mp h2.1, fun B hB' x hx i => ?_⟩
    have h3 := h2.2
    rw [excludedBoxes_image hp₀ hp₁, imageBases_coarseMap] at h3
    exact (siteMap_ne_iff g hp₀ _ x (b y)).mp
      (h3 (B.image (fineEquiv hp₀ g)) (Finset.mem_image_of_mem _ hB') (fineEquiv hp₀ g x)
        (Finset.mem_image_of_mem _ hx)) i
  · intro hB y'
    obtain ⟨y, rfl⟩ := (coarseEquiv hp₁ g).surjective y'
    have h1 := hB y
    refine ⟨fun c => (hcentre y).mpr (h1.1 ((hcond y).mp c)), fun c => ?_⟩
    have h2 := h1.2 (fun e => c ((hcond y).mpr e))
    refine ⟨(hbelow y).mpr h2.1, fun B' hB' x' hx' => ?_⟩
    have hB'' : B' ∈ excludedBoxes J₀ (h.image (Finset.image (fineEquiv hp₀ g))) (coarseMap g y) := hB'
    rw [excludedBoxes_image hp₀ hp₁] at hB''
    obtain ⟨B, hB₀, rfl⟩ := Finset.mem_image.mp hB''
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hx'
    exact show ∀ i, (fineEquiv hp₀ g x) i ≠ (imageBases hp₁ g b (coarseMap g y)) i from by
      rw [imageBases_coarseMap]
      exact (siteMap_ne_iff g hp₀ _ x (b y)).mpr (h2.2 B hB₀ x hx)
end Beside
section Means
variable {m₀ m₁ : ℕ} (hp₀ : ∀ i, F.period F.depth i = m₀) (hp₁ : ∀ i, F.period F.top i = m₁)
  (g : TorusIsometry)
def contourImage (g : TorusIsometry) (e : (Fin 4 → ℤ) × Equiv.Perm (Fin 4)) :
    (Fin 4 → ℤ) × Equiv.Perm (Fin 4) :=
  (linearPart g e.1, e.2.trans g.axisPerm.symm)
theorem contourImage_injective : Function.Injective (contourImage g) := by
  rintro ⟨a, π⟩ ⟨a', π'⟩ h
  simp only [contourImage, Prod.mk.injEq] at h
  have h1 : a = a' := by
    have := congrArg (linearPartInv g) h.1
    simpa [linearPartInv_linearPart] using this
  have h2 : π = π' := by
    ext k
    have := congrArg (fun p : Equiv.Perm (Fin 4) => p k) h.2
    simp only [Equiv.trans_apply, EmbeddingLike.apply_eq_iff_eq] at this
    rw [this]
  rw [h1, h2]
theorem exists_contourImage_eq (e : (Fin 4 → ℤ) × Equiv.Perm (Fin 4)) (he : e ∈ allContours F) :
    ∃ e₀ ∈ allContours F, contourImage g e₀ = e := by
  obtain ⟨a, π⟩ := e
  simp only [allContours, Finset.mem_product, Finset.mem_univ, and_true] at he ⊢
  refine ⟨(linearPartInv g a, π.trans g.axisPerm), linearPartInv_mem_centredCube g he, ?_⟩
  simp only [contourImage, linearPart_linearPartInv, Prod.mk.injEq, true_and]
  ext k
  simp
theorem contourImage_mem {e : (Fin 4 → ℤ) × Equiv.Perm (Fin 4)} (he : e ∈ allContours F) :
    contourImage g e ∈ allContours F := by
  simp only [allContours, Finset.mem_product, Finset.mem_univ, and_true, contourImage] at he ⊢
  exact linearPart_mem_centredCube g he
include hp₀ hp₁ in
theorem mem_pathSites_image_iff {b : F.Cell → F.Site F.depth}
    (hb : ∀ y, ∃ z ∈ centredCube F.blockSide, b y = siteAtOffset y z)
    (hM : 2 * (F.blockSide : ℤ) ≤ m₀) (c : F.Cell × Fin 4) {ξ : Fin 4 → ℤ} (hξ : ξ ∈ centredCube F.blockSide)
    (π : Equiv.Perm (Fin 4)) (z : F.Site F.depth) :
    z ∈ pathSites (imageBases hp₁ g b (imageBond g c).1)
        (contourPath (imageBases hp₁ g b) (imageBond g c) (linearPart g ξ) (π.trans g.axisPerm.symm)) ↔
      ∃ x ∈ pathSites (b c.1) (contourPath b c ξ π), z = fineMap g x := by
  rcases g.axisSign_unit (g.imageAxis c.2) with hs | hs
  · rw [← contourPath_map_of_pos hp₀ hp₁ g hb hM c hs hξ π, (imageBond_of_pos hp₁ g c hs).1,
      imageBases_coarseMap, pathSites_map hp₀]
    simp only [List.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
  · have hend := pathEndpoint_contourPath (imageBases hp₁ g b) (imageBond g c) (linearPart g ξ)
      (π.trans g.axisPerm.symm)
    rw [(imageBond_of_neg hp₁ g c hs).2, imageBases_coarseMap] at hend
    have h1 := pathSites_map hp₀ g (fineOffset F.blockSide g) (b c.1) (contourPath b c ξ π)
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
  · obtain ⟨h1, h2⟩ := imageBond_of_pos hp₁ g c hs
    rw [h2, h1, excludedBoxes_image hp₀ hp₁, excludedBoxes_image hp₀ hp₁, Finset.image_union]
  · obtain ⟨h1, h2⟩ := imageBond_of_neg hp₁ g c hs
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
    (c : F.Cell × Fin 4) : usedContours J₀ h b c ⊆ allContours F := by
  classical
  unfold usedContours
  split_ifs
  · exact subset_rfl
  · exact Finset.filter_subset _ _
include hp₀ hp₁ in
theorem isCrowded_ends_image_iff (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth))) (c : F.Cell × Fin 4) :
    (IsCrowded J₀ (h.image (Finset.image (fineEquiv hp₀ g))) (imageBond g c).1 ∨
      IsCrowded J₀ (h.image (Finset.image (fineEquiv hp₀ g)))
        ((imageBond g c).1 + BlockAverages.unitStep F.top (imageBond g c).2)) ↔
    (IsCrowded J₀ h c.1 ∨ IsCrowded J₀ h (c.1 + BlockAverages.unitStep F.top c.2)) := by
  rcases g.axisSign_unit (g.imageAxis c.2) with hs | hs
  · obtain ⟨h1, h2⟩ := imageBond_of_pos hp₁ g c hs
    rw [h2, h1, isCrowded_image_iff hp₀ hp₁, isCrowded_image_iff hp₀ hp₁]
  · obtain ⟨h1, h2⟩ := imageBond_of_neg hp₁ g c hs
    rw [h2, h1, isCrowded_image_iff hp₀ hp₁, isCrowded_image_iff hp₀ hp₁, or_comm]
include hp₀ hp₁ in
theorem usedContours_image (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth))) {b : F.Cell → F.Site F.depth}
    (hb : ∀ y, ∃ z ∈ centredCube F.blockSide, b y = siteAtOffset y z) (hM : 2 * (F.blockSide : ℤ) ≤ m₀)
    (c : F.Cell × Fin 4) :
    usedContours J₀ (h.image (Finset.image (fineEquiv hp₀ g))) (imageBases hp₁ g b) (imageBond g c) =
      (usedContours J₀ h b c).image (contourImage g) := by
  classical
  have hall : (allContours F).image (contourImage g) = allContours F := by
    ext e
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨e₀, he₀, rfl⟩
      exact contourImage_mem g he₀
    · intro he
      exact exists_contourImage_eq g e he
  have hf : ((allContours F).filter fun e => IsGoodContour J₀ (h.image (Finset.image (fineEquiv hp₀ g)))
        (imageBases hp₁ g b) (imageBond g c) e.1 e.2) =
      ((allContours F).filter fun e => IsGoodContour J₀ h b c e.1 e.2).image (contourImage g) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨he, hg⟩
      obtain ⟨⟨ξ, π⟩, he₀, rfl⟩ := exists_contourImage_eq g e he
      have hξ : ξ ∈ centredCube F.blockSide := (Finset.mem_product.mp he₀).1
      exact ⟨(ξ, π), ⟨he₀, (isGoodContour_image_iff hp₀ hp₁ g J₀ h hb hM c hξ π).mp hg⟩, rfl⟩
    · rintro ⟨⟨ξ, π⟩, ⟨he₀, hg⟩, rfl⟩
      have hξ : ξ ∈ centredCube F.blockSide := (Finset.mem_product.mp he₀).1
      exact ⟨contourImage_mem g he₀, (isGoodContour_image_iff hp₀ hp₁ g J₀ h hb hM c hξ π).mpr hg⟩
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
theorem pathHolonomy_image_of_pos {X X' : F.GaugeField F.depth}
    (hX : FieldTransported g (fineOffset F.blockSide g) X X')
    {b : F.Cell → F.Site F.depth} (hb : ∀ y, ∃ z ∈ centredCube F.blockSide, b y = siteAtOffset y z)
    (hM : 2 * (F.blockSide : ℤ) ≤ m₀) (c : F.Cell × Fin 4) (hs : g.axisSign (g.imageAxis c.2) = 1)
    {ξ : Fin 4 → ℤ} (hξ : ξ ∈ centredCube F.blockSide) (π : Equiv.Perm (Fin 4)) :
    pathHolonomy X' (imageBases hp₁ g b (imageBond g c).1)
        (contourPath (imageBases hp₁ g b) (imageBond g c) (linearPart g ξ) (π.trans g.axisPerm.symm)) =
      pathHolonomy X (b c.1) (contourPath b c ξ π) := by
  rw [← contourPath_map_of_pos hp₀ hp₁ g hb hM c hs hξ π, (imageBond_of_pos hp₁ g c hs).1, imageBases_coarseMap]
  exact pathHolonomy_map hp₀ hX _ _
include hp₀ hp₁ in
theorem contourMean_image_of_pos (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth))) {X X' : F.GaugeField F.depth}
    (hX : FieldTransported g (fineOffset F.blockSide g) X X')
    {b : F.Cell → F.Site F.depth} (hb : ∀ y, ∃ z ∈ centredCube F.blockSide, b y = siteAtOffset y z)
    (hM : 2 * (F.blockSide : ℤ) ≤ m₀) (c : F.Cell × Fin 4) (hs : g.axisSign (g.imageAxis c.2) = 1) :
    contourMean J₀ (h.image (Finset.image (fineEquiv hp₀ g))) (imageBases hp₁ g b) X' (imageBond g c) =
      contourMean J₀ h b X c := by
  unfold contourMean
  rw [usedContours_image hp₀ hp₁ g J₀ h hb hM c, Finset.card_image_of_injective _ (contourImage_injective g),
    Finset.sum_image fun _ _ _ _ e => contourImage_injective g e]
  congr 1
  refine Finset.sum_congr rfl fun e he => ?_
  have hξ : e.1 ∈ centredCube F.blockSide := (Finset.mem_product.mp (usedContours_subset J₀ h b c he)).1
  exact congrArg _ (pathHolonomy_image_of_pos hp₀ hp₁ g hX hb hM c hs hξ e.2)
end Means
section EvaluationMaps
theorem toTorusSite_sub_unitStep (hp : ∀ i, F.period j i = m) (a : F.Site j) (d : Fin 4) :
    (toTorusSite m (a - BlockAverages.unitStep j d : F.Site j) : TorusSite m) =
      toTorusSite m a - TorusFields.unitStep m d := by
  have h := toTorusSite_add (F := F) (j := j) hp (a - BlockAverages.unitStep j d) (BlockAverages.unitStep j d)
  rw [sub_add_cancel, toTorusSite_unitStep hp] at h
  rw [h]
  abel
theorem fieldTransported_of_transports (hp : ∀ i, F.period j i = m) (g : TorusIsometry) (u : Fin 4 → ℤ)
    {W W' : TorusField m}
    (h : TorusIsometry.Transports ⟨g.axisPerm, g.axisSign, u, g.axisSign_unit⟩ W W') :
    FieldTransported g u (readAtLevel F j W) (readAtLevel F j W') := by
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
theorem plaquetteDefect_eq_curvature (hp : ∀ i, F.period j i = m) (W : TorusField m) (x : F.Site j)
    (μ ν : Fin 4) :
    plaquetteDefect (readAtLevel F j W) (x, μ, ν) = curvature W (toTorusSite m x) μ ν := by
  unfold plaquetteDefect curvature holonomy
  have hv : plaquetteHolonomy (readAtLevel F j W) (x, μ, ν) =
      W (toTorusSite m x) μ * W (toTorusSite m x + TorusFields.unitStep m μ) ν *
        (W (toTorusSite m x + TorusFields.unitStep m ν) μ)⁻¹ * (W (toTorusSite m x) ν)⁻¹ := by
    have a1 : x + BlockAverages.unitStep j μ + BlockAverages.unitStep j ν - BlockAverages.unitStep j μ =
        x + BlockAverages.unitStep j ν := by abel
    have a2 : x + BlockAverages.unitStep j μ + BlockAverages.unitStep j ν + -BlockAverages.unitStep j μ -
        BlockAverages.unitStep j ν = x := by abel
    have hr : ∀ (z : F.Site j) (i : Fin 4), readAtLevel F j W z i = W (toTorusSite m z) i := fun _ _ => rfl
    simp only [plaquetteHolonomy, pathHolonomy, linkValue, stepDisplacement, if_true, Bool.false_eq_true,
      if_false, mul_one, a1, a2, hr, toTorusSite_add hp, toTorusSite_unitStep hp, mul_assoc]
  rw [hv]
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
    {W W' : TorusField m}
    (h : TorusIsometry.Transports ⟨g.axisPerm, g.axisSign, u, g.axisSign_unit⟩ W W') (x : F.Site j)
    (μ ν : Fin 4) :
    plaquetteDefect (readAtLevel F j W') (imagePlaquetteCorner g u x μ ν, g.imageAxis μ, g.imageAxis ν) =
      plaquetteDefect (readAtLevel F j W) (x, μ, ν) := by
  rw [plaquetteDefect_eq_curvature hp, plaquetteDefect_eq_curvature hp, toTorusSite_imagePlaquetteCorner hp]
  have h1 := plaquetteEnergy_of_transports h (toTorusSite m x) μ ν
  rw [plaquetteEnergy_eq_curvature_sq, plaquetteEnergy_eq_curvature_sq] at h1
  have h2 : curvature W (toTorusSite m x) μ ν ^ 2 =
      curvature W' (TorusIsometry.imageCorner ⟨g.axisPerm, g.axisSign, u, g.axisSign_unit⟩ (toTorusSite m x) μ ν)
        (g.imageAxis μ) (g.imageAxis ν) ^ 2 := by
    have h3 := h1
    have e : ∀ a b : ℝ, a / 2 = b / 2 → a = b := fun a b hab => by linarith
    exact e _ _ h3
  exact ((sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2).symm
theorem plaquetteDefect_swap (hp : ∀ i, F.period j i = m) (W : TorusField m) (x : F.Site j) (μ ν : Fin 4) :
    plaquetteDefect (readAtLevel F j W) (x, ν, μ) = plaquetteDefect (readAtLevel F j W) (x, μ, ν) := by
  rw [plaquetteDefect_eq_curvature hp, plaquetteDefect_eq_curvature hp]
  have h1 := plaquetteEnergy_symm W (toTorusSite m x) μ ν
  rw [plaquetteEnergy_eq_curvature_sq, plaquetteEnergy_eq_curvature_sq] at h1
  have e : ∀ a b : ℝ, a / 2 = b / 2 → a = b := fun a b hab => by linarith
  exact ((sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (e _ _ h1)).symm
omit [∀ j i, NeZero (F.period j i)] in
theorem plaquetteCorners_swap (x : F.Site j) (μ ν : Fin 4) :
    plaquetteCorners (x, ν, μ) = plaquetteCorners (x, μ, ν) := by
  ext z
  simp only [plaquetteCorners, Finset.mem_insert, Finset.mem_singleton]
  have e : x + BlockAverages.unitStep j ν + BlockAverages.unitStep j μ =
      x + BlockAverages.unitStep j μ + BlockAverages.unitStep j ν := by abel
  rw [e]
  tauto
theorem shifted_corners_eq {A : Type*} [AddCommGroup A] [DecidableEq A] (P e₁ e₂ : A) (a b : Prop)
    [Decidable a] [Decidable b] :
    ({P - (if a then 0 else e₁) - (if b then 0 else e₂), P - (if a then 0 else e₁) - (if b then 0 else e₂) + e₁,
      P - (if a then 0 else e₁) - (if b then 0 else e₂) + e₂,
      P - (if a then 0 else e₁) - (if b then 0 else e₂) + e₁ + e₂} : Finset A) =
    {P, P + (if a then e₁ else -e₁), P + (if b then e₂ else -e₂),
      P + (if a then e₁ else -e₁) + (if b then e₂ else -e₂)} := by
  ext z
  by_cases ha : a <;> by_cases hb : b <;>
    simp only [ha, hb, if_true, if_false, Finset.mem_insert, Finset.mem_singleton]
  · simp only [sub_zero]
  · have e1 : P - 0 - e₂ = P + -e₂ := by abel
    have e2 : P - 0 - e₂ + e₁ = P + e₁ + -e₂ := by abel
    have e3 : P - 0 - e₂ + e₂ = P := by abel
    have e4 : P - 0 - e₂ + e₁ + e₂ = P + e₁ := by abel
    rw [e4, e3, e2, e1]
    tauto
  · have e1 : P - e₁ - 0 = P + -e₁ := by abel
    have e2 : P - e₁ - 0 + e₁ = P := by abel
    have e3 : P - e₁ - 0 + e₂ = P + -e₁ + e₂ := by abel
    have e4 : P - e₁ - 0 + e₁ + e₂ = P + e₂ := by abel
    rw [e4, e3, e2, e1]
    tauto
  · have e1 : P - e₁ - e₂ = P + -e₁ + -e₂ := by abel
    have e2 : P - e₁ - e₂ + e₁ = P + -e₂ := by abel
    have e3 : P - e₁ - e₂ + e₂ = P + -e₁ := by abel
    have e4 : P - e₁ - e₂ + e₁ + e₂ = P := by abel
    rw [e4, e3, e2, e1]
    tauto
theorem siteOfCoords_signed_single (g : TorusIsometry) (k : Fin 4) :
    (siteOfCoords j (Pi.single (g.imageAxis k) (g.axisSign (g.imageAxis k))) : F.Site j) =
      if g.axisSign (g.imageAxis k) = 1 then BlockAverages.unitStep j (g.imageAxis k)
        else - BlockAverages.unitStep j (g.imageAxis k) := by
  rcases g.axisSign_unit (g.imageAxis k) with hs | hs
  · simp [hs, BlockAverages.unitStep]
  · have hne : (-1 : ℤ) ≠ 1 := by omega
    rw [hs, if_neg hne, BlockAverages.unitStep, ← TorusContours.siteOfCoords_neg]
    congr 1
    funext i
    by_cases h : i = g.imageAxis k
    · subst h
      simp
    · simp [h]
theorem siteMap_add_unitStep (hp : ∀ i, F.period j i = m) (g : TorusIsometry) (u : Fin 4 → ℤ) (x : F.Site j)
    (k : Fin 4) :
    (siteMap g u (x + BlockAverages.unitStep j k) : F.Site j) = siteMap g u x +
      (if g.axisSign (g.imageAxis k) = 1 then BlockAverages.unitStep j (g.imageAxis k)
        else - BlockAverages.unitStep j (g.imageAxis k)) := by
  have e : (BlockAverages.unitStep j k : F.Site j) = siteOfCoords j (Pi.single k 1) := rfl
  rw [e, siteMap_add hp, linearPart_single, mul_one, siteOfCoords_signed_single]
theorem plaquetteCorners_image (hp : ∀ i, F.period j i = m) (g : TorusIsometry) (u : Fin 4 → ℤ) (x : F.Site j)
    (μ ν : Fin 4) :
    plaquetteCorners (imagePlaquetteCorner g u x μ ν, g.imageAxis μ, g.imageAxis ν) =
      (plaquetteCorners (x, μ, ν)).image (siteMap g u) := by
  unfold plaquetteCorners imagePlaquetteCorner
  simp only [Finset.image_insert, Finset.image_singleton, siteMap_add_unitStep hp]
  exact shifted_corners_eq _ _ _ _ _
end EvaluationMaps
section Hot
variable {L n : ℕ} [NeZero L] [NeZero n]
theorem mem_levelSites (x : (stepBlockFrame L n).Site 0) : x ∈ levelSites (stepBlockFrame L n) 0 := by
  unfold levelSites boxSites
  refine Finset.mem_image.mpr ⟨siteCoords x, ?_, TorusContours.siteOfCoords_siteCoords x⟩
  refine Fintype.mem_piFinset.mpr fun i => Finset.mem_Icc.mpr ?_
  have h1 : siteCoords x i = (((x i).val : ℕ) : ℤ) := ZMod.cast_eq_val _
  have h2 := ZMod.val_lt (x i)
  rw [h1]
  simp only [Pi.zero_apply]
  omega
theorem mem_hotLumps_iff (grid : LumpGrid L) (s : ℝ) (X : (stepBlockFrame L n).GaugeField 0)
    (l : Finset ((stepBlockFrame L n).Site 0)) :
    l ∈ hotLumps grid s (levelSites (stepBlockFrame L n) 0) X ↔
      ∃ (x : (stepBlockFrame L n).Site 0) (μ ν : Fin 4), μ < ν ∧ s ≤ plaquetteDefect X (x, μ, ν) ∧
        ∃ c ∈ plaquetteCorners (x, μ, ν), l = lumpOf grid c := by
  classical
  unfold hotLumps cutPlaquettes
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true,
    Finset.mem_image]
  constructor
  · rintro ⟨⟨x, μ, ν⟩, ⟨⟨_, hμ, _⟩, hs⟩, c, hc, rfl⟩
    exact ⟨x, μ, ν, hμ, hs, c, hc, rfl⟩
  · rintro ⟨x, μ, ν, hμ, hs, c, hc, rfl⟩
    exact ⟨(x, μ, ν), ⟨⟨mem_levelSites x, hμ, fun z _ => mem_levelSites z⟩, hs⟩, c, hc, rfl⟩
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
  have hu : ∀ i, (L : ℤ) ∣ fineOffset (stepBlockFrame L n).blockSide g i := fun i => Dvd.intro _ rfl
  have hlump : ∀ c : (stepBlockFrame L n).Site 0, lumpOf grid (siteMap g (fineOffset (stepBlockFrame L n).blockSide g) c :
      (stepBlockFrame L n).Site 0) =
        (lumpOf grid c).image (fineEquiv (F := stepBlockFrame L n) (m₀ := n * L) stepBlockFrame_period_zero g) :=
    fun c => lumpOf_siteMap hL hLodd hp hm g _ hu grid c
  have hcarry : TorusIsometry.Transports
      ⟨g.axisPerm, g.axisSign, fineOffset (stepBlockFrame L n).blockSide g, g.axisSign_unit⟩ W W' := h
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
    have hbase : imagePlaquetteCorner g (fineOffset (stepBlockFrame L n).blockSide g) x₀ μ₀ ν₀ = x' := by
      unfold imagePlaquetteCorner
      have : siteMap g (fineOffset (stepBlockFrame L n).blockSide g) x₀ =
          x' + (if g.axisSign μ' = 1 then 0 else BlockAverages.unitStep 0 μ') +
            (if g.axisSign ν' = 1 then 0 else BlockAverages.unitStep 0 ν') := e.apply_symm_apply _
      rw [this, hdμ, hdν]
      abel
    have hcurv := plaquetteDefect_image (F := stepBlockFrame L n) (j := 0) hp g _ hcarry x₀ μ₀ ν₀
    rw [hbase, hdμ, hdν] at hcurv
    have hcorn := plaquetteCorners_image (F := stepBlockFrame L n) (j := 0) hp g
      (fineOffset (stepBlockFrame L n).blockSide g) x₀ μ₀ ν₀
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
      (fineOffset (stepBlockFrame L n).blockSide g) x μ ν
    have hmem : siteMap g (fineOffset (stepBlockFrame L n).blockSide g) c ∈
        plaquetteCorners (imagePlaquetteCorner g (fineOffset (stepBlockFrame L n).blockSide g) x μ ν,
          g.imageAxis μ, g.imageAxis ν) := by
      rw [hcorn]
      exact Finset.mem_image_of_mem _ hc
    rcases lt_or_gt_of_ne hne with hlt₀ | hlt₀
    · exact ⟨_, g.imageAxis μ, g.imageAxis ν, hlt₀, by rw [hcurv]; exact hs, _, hmem, (hlump c).symm⟩
    · exact ⟨imagePlaquetteCorner g (fineOffset (stepBlockFrame L n).blockSide g) x μ ν, g.imageAxis ν,
        g.imageAxis μ, hlt₀, by rw [plaquetteDefect_swap hp, hcurv]; exact hs, _,
        by rw [plaquetteCorners_swap]; exact hmem, (hlump c).symm⟩
end Hot
section Bonds
variable {m₀ m₁ : ℕ} (hp₁ : ∀ i, F.period F.top i = m₁) (g : TorusIsometry)
include hp₁ in
theorem imageBond_injective : Function.Injective (imageBond g : F.Cell × Fin 4 → F.Cell × Fin 4) := by
  rintro ⟨y, k⟩ ⟨y', k'⟩ h
  simp only [imageBond, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hk : k = k' := g.axisPerm.symm.injective h2
  subst hk
  have hy : coarseMap g y = coarseMap g y' := by
    by_cases hs : g.axisSign (g.imageAxis k) = 1
    · simpa [hs] using h1
    · simpa [hs] using h1
  rw [siteMap_injective hp₁ g g.offset hy]
end Bonds
section Main
theorem mem_baseChoices_iff (ℓ : StepParameters) {n : ℕ} [NeZero n] (W : (stepBlockFrame ℓ.side n).GaugeField 0)
    (b : (stepBlockFrame ℓ.side n).Cell → (stepBlockFrame ℓ.side n).Site 0) :
    b ∈ baseChoices ℓ W ↔ IsBaseChoice ℓ.baseDepth (fineHotLumps ℓ W) b := by
  classical
  unfold baseChoices
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact Iff.rfl
def translation (v : Fin 4 → ℤ) : TorusIsometry :=
  ⟨1, fun _ => 1, fun i => - v i, fun _ => Or.inl rfl⟩
theorem translation_transports {m : ℕ} (v : Fin 4 → ℤ) (W : TorusField m) :
    (translation v).Transports W (TorusFields.translate (siteOfInt v) W) := by
  intro x k
  have e : (translation v).mapSite x + siteOfInt v = x := by
    funext i
    simp [TorusIsometry.mapSite, translation, siteOfInt]
  simp only [translation, if_true, Equiv.Perm.one_symm, Equiv.Perm.one_apply]
  show W ((translation v).mapSite x + siteOfInt v) k = W x k
  rw [e]
theorem scaledLift_translation (L : ℕ) (v : Fin 4 → ℤ) :
    (translation v).scaledLift L = translation fun i => (L : ℤ) * v i := by
  simp [TorusIsometry.scaledLift, translation]
theorem linearPart_translation (v z : Fin 4 → ℤ) : linearPart (translation v) z = z := by
  funext i
  simp [linearPart, translation]
theorem translation_preserves_baseKernel (ℓ : StepParameters) (hfit : ℓ.Admissible) (x : ℝ) (n : ℕ) [NeZero n]
    (hn : ℓ.n₀ ≤ n) (v : Fin 4 → ℤ) (W : TorusField (n * ℓ.side)) (V : TorusField n) (b : BaseChoice ℓ.side n) :
    (translateBases v b ∈ baseChoices ℓ (fineLevelField ℓ n (TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) * v i) W)) ↔
        b ∈ baseChoices ℓ (fineLevelField ℓ n W)) ∧
      (baseChoices ℓ (fineLevelField ℓ n (TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) * v i) W))).card =
        (baseChoices ℓ (fineLevelField ℓ n W)).card ∧
      (b ∈ baseChoices ℓ (fineLevelField ℓ n W) →
        ∏ c : (stepBlockFrame ℓ.side n).Cell × Fin 4,
            bondKernel ℓ x (fineLevelField ℓ n (TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) * v i) W))
              (coarseLevelField ℓ n (TorusFields.translate (siteOfInt v) V)) (translateBases v b) c =
          ∏ c : (stepBlockFrame ℓ.side n).Cell × Fin 4,
            bondKernel ℓ x (fineLevelField ℓ n W) (coarseLevelField ℓ n V) b c) := by
  have hp₀ : ∀ i, (stepBlockFrame ℓ.side n).period (stepBlockFrame ℓ.side n).depth i = n * ℓ.side :=
    stepBlockFrame_period_zero
  have hp₁ : ∀ i, (stepBlockFrame ℓ.side n).period (stepBlockFrame ℓ.side n).top i = n :=
    stepBlockFrame_period_one
  have hL1 : 1 ≤ (stepBlockFrame ℓ.side n).blockSide := Nat.pos_of_ne_zero (NeZero.ne ℓ.side)
  have hn2 : 2 ≤ n := by
    have := hfit.n₀_ge
    omega
  have hM : 2 * ((stepBlockFrame ℓ.side n).blockSide : ℤ) ≤ ((n * ℓ.side : ℕ) : ℤ) := by
    show 2 * (ℓ.side : ℤ) ≤ _
    push_cast
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn2) (by positivity)
  set g := translation v with hg
  have hW : (g.scaledLift ℓ.side).Transports W (TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) * v i) W) := by
    rw [hg, scaledLift_translation]
    exact translation_transports _ W
  have hV : g.Transports V (TorusFields.translate (siteOfInt v) V) := translation_transports v V
  set W' := TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) * v i) W with hW'
  set V' := TorusFields.translate (siteOfInt v) V with hV'
  set X := fineLevelField ℓ n W with hXd
  set X' := fineLevelField ℓ n W' with hXd'
  set U := coarseLevelField ℓ n V with hUd
  set U' := coarseLevelField ℓ n V' with hUd'
  have hX : FieldTransported g (fineOffset (stepBlockFrame ℓ.side n).blockSide g) X X' :=
    fieldTransported_of_transports stepBlockFrame_period_zero g _ hW
  have hU : FieldTransported g g.offset U U' := fieldTransported_of_transports stepBlockFrame_period_one g _ hV
  have hH : fineHotLumps ℓ X' = (fineHotLumps ℓ X).image (Finset.image (fineEquiv hp₀ g)) :=
    hotLumps_image hfit.L_odd ℓ.grid ℓ.threshold g hW
  have himg : ∀ b' : BaseChoice ℓ.side n, imageBases hp₁ g b' = translateBases v b' := by
    intro b'
    funext y
    have hy : coarseMap g (y + siteOfCoords (stepBlockFrame ℓ.side n).top v) = y := by
      show siteOfCoords _ (linearPart g (siteCoords (y + siteOfCoords (stepBlockFrame ℓ.side n).top v)) +
        g.offset) = y
      rw [hg, linearPart_translation, TorusContours.siteOfCoords_add, TorusContours.siteOfCoords_siteCoords]
      funext i
      simp [siteOfCoords, translation]
    have := imageBases_coarseMap hp₁ g b' (y + siteOfCoords (stepBlockFrame ℓ.side n).top v)
    rw [hy] at this
    rw [this]
    have e0 : (siteOfCoords (stepBlockFrame ℓ.side n).depth
        (siteCoords (b' (y + siteOfCoords (stepBlockFrame ℓ.side n).top v))) :
        (stepBlockFrame ℓ.side n).Site (stepBlockFrame ℓ.side n).depth) =
          b' (y + siteOfCoords (stepBlockFrame ℓ.side n).top v) :=
      TorusContours.siteOfCoords_siteCoords _
    have e1 : (siteOfCoords (stepBlockFrame ℓ.side n).depth
        (fineOffset (stepBlockFrame ℓ.side n).blockSide (translation v)) :
        (stepBlockFrame ℓ.side n).Site (stepBlockFrame ℓ.side n).depth) =
        - siteOfCoords (stepBlockFrame ℓ.side n).depth fun i => (ℓ.side : ℤ) * v i := by
      have e : fineOffset (stepBlockFrame ℓ.side n).blockSide (translation v) = - fun i => (ℓ.side : ℤ) * v i := by
        funext i
        show (ℓ.side : ℤ) * (- v i) = - ((ℓ.side : ℤ) * v i)
        ring
      rw [e]
      exact TorusContours.siteOfCoords_neg _
    show siteOfCoords _ (linearPart g (siteCoords (b' (y + siteOfCoords (stepBlockFrame ℓ.side n).top v))) +
      fineOffset (stepBlockFrame ℓ.side n).blockSide g) = _
    rw [hg, linearPart_translation, TorusContours.siteOfCoords_add]
    exact (congrArg₂ (· + ·) e0 e1).trans (sub_eq_add_neg _ _).symm
  have hiff : ∀ b' : BaseChoice ℓ.side n, translateBases v b' ∈ baseChoices ℓ X' ↔ b' ∈ baseChoices ℓ X := by
    intro b'
    rw [mem_baseChoices_iff ℓ X', mem_baseChoices_iff ℓ X, ← himg, hH]
    exact isBaseChoice_image_iff hp₀ hp₁ g ℓ.baseDepth (fineHotLumps ℓ X) b'
  have hinj : Function.Injective (imageBases hp₁ g :
      _ → (stepBlockFrame ℓ.side n).Cell → (stepBlockFrame ℓ.side n).Site (stepBlockFrame ℓ.side n).depth) := by
    intro b b' h
    funext y
    have := congrFun h (coarseMap g y)
    rw [imageBases_coarseMap, imageBases_coarseMap] at this
    exact siteMap_injective hp₀ g _ this
  have hmaps : ∀ b, b ∈ baseChoices ℓ X → imageBases hp₁ g b ∈ baseChoices ℓ X' := fun b hb => by
    rw [himg]
    exact (hiff b).mpr hb
  have hsurj : ∀ b', b' ∈ baseChoices ℓ X' → ∃ b, ∃ _ : b ∈ baseChoices ℓ X, imageBases hp₁ g b = b' := by
    intro b' hb'
    have h0 : IsBaseChoice ℓ.baseDepth (fineHotLumps ℓ X') b' := (mem_baseChoices_iff ℓ X' b').mp hb'
    let b : (stepBlockFrame ℓ.side n).Cell → (stepBlockFrame ℓ.side n).Site (stepBlockFrame ℓ.side n).depth :=
      fun y => (fineEquiv hp₀ g).symm (b' (coarseMap g y))
    have e : imageBases hp₁ g b = b' := by
      funext y'
      obtain ⟨y, rfl⟩ := (coarseEquiv hp₁ g).surjective y'
      show imageBases hp₁ g b (coarseMap g y) = _
      rw [imageBases_coarseMap]
      exact (fineEquiv hp₀ g).apply_symm_apply _
    refine ⟨b, (mem_baseChoices_iff ℓ X b).mpr
      ((isBaseChoice_image_iff hp₀ hp₁ g ℓ.baseDepth (fineHotLumps ℓ X) b).mp ?_), e⟩
    have h1 : IsBaseChoice ℓ.baseDepth ((fineHotLumps ℓ X).image (Finset.image (fineEquiv hp₀ g))) b' := hH ▸ h0
    rw [e]
    exact h1
  have hcard : (baseChoices ℓ X').card = (baseChoices ℓ X).card :=
    (Finset.card_bij (fun b _ => imageBases hp₁ g b) hmaps (fun _ _ _ _ e => hinj e) hsurj).symm
  refine ⟨hiff b, hcard, fun hb => ?_⟩
  have hs : ∀ k, g.axisSign k = 1 := fun _ => rfl
  have hbond : ∀ c, bondKernel ℓ x X' U' (imageBases hp₁ g b) (imageBond g c) = bondKernel ℓ x X U b c := by
    intro c
    have hb' : IsBaseChoice ℓ.baseDepth (fineHotLumps ℓ X) b := (mem_baseChoices_iff ℓ X b).mp hb
    have hrep : ∀ y, ∃ z ∈ centredCube (stepBlockFrame ℓ.side n).blockSide, b y = siteAtOffset y z :=
      fun y => exists_centredCube_of_isBaseChoice hL1 hb' y
    refine (bondKernel_eq_meanKernel ℓ x X' U' _ _).trans
      (Eq.trans ?_ (bondKernel_eq_meanKernel ℓ x X U b c).symm)
    have hs' := hs (g.imageAxis c.2)
    have e' : contourMean ℓ.baseDepth (fineHotLumps ℓ X') (imageBases hp₁ g b) X' (imageBond g c) =
        contourMean ℓ.baseDepth (fineHotLumps ℓ X) b X c :=
      (congrArg (fun h => contourMean ℓ.baseDepth h (imageBases hp₁ g b) X' (imageBond g c)) hH).trans
        (contourMean_image_of_pos hp₀ hp₁ g ℓ.baseDepth _ hX hrep hM c hs')
    have h1 := hU c.1 c.2
    rw [if_pos hs'] at h1
    have e : U' (imageBond g c).1 (imageBond g c).2 = U c.1 c.2 := by
      simp only [imageBond, hs', if_true]
      exact h1
    exact congrArg₂ (meanKernel (ℓ.coupling * x)) e' e
  let eB : ((stepBlockFrame ℓ.side n).Cell × Fin 4) ≃ ((stepBlockFrame ℓ.side n).Cell × Fin 4) :=
    Equiv.ofBijective (imageBond g) (Finite.injective_iff_bijective.mp (imageBond_injective hp₁ g))
  rw [← himg]
  exact (Fintype.prod_equiv eB _ _ fun c => (hbond c).symm).symm
end Main
theorem translationPreservesBaseKernel : TranslationPreservesBaseKernel :=
  fun ℓ hfit x n _ hn v W V b => translation_preserves_baseKernel ℓ hfit x n hn v W V b
end YangMills.Construction.TranslationKernel
end
