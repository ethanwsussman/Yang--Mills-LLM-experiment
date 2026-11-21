import YangMills.Construction.ForwardTube.ShiftedTubesInLightConeCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ForwardTube.ShiftedTubeCoords
theorem re_lightConePlus (v : ℂ × ℂ) : (lightConePlus v).re = v.1.re - v.2.im := by
  simp [lightConePlus, sub_eq_add_neg]
theorem re_lightConeMinus (v : ℂ × ℂ) : (lightConeMinus v).re = v.1.re + v.2.im := by
  simp [lightConeMinus]
theorem re_lightConePlus_sub_timeTranslate (u : ℂ × ℂ) (s : ℝ) :
    (lightConePlus (u - timeTranslate s)).re = (lightConePlus u).re - s := by
  simp only [re_lightConePlus, timeTranslate, Prod.fst_sub, Prod.snd_sub, Complex.sub_re,
    Complex.ofReal_re, sub_zero]
  ring
theorem re_lightConeMinus_sub_timeTranslate (u : ℂ × ℂ) (s : ℝ) :
    (lightConeMinus (u - timeTranslate s)).re = (lightConeMinus u).re - s := by
  simp only [re_lightConeMinus, timeTranslate, Prod.fst_sub, Prod.snd_sub, Complex.sub_re,
    Complex.ofReal_re, sub_zero]
  ring
theorem sub_timeTranslate_mem_forwardTube_iff (u : ℂ × ℂ) (s : ℝ) :
    u - timeTranslate s ∈ forwardTube ↔ (lightConePlus u).re > s ∧ (lightConeMinus u).re > s := by
  show (lightConePlus (u - timeTranslate s)).re > 0 ∧
    (lightConeMinus (u - timeTranslate s)).re > 0 ↔ _
  rw [re_lightConePlus_sub_timeTranslate, re_lightConeMinus_sub_timeTranslate]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
theorem mem_translate_image_iff (u : ℂ × ℂ) (s : ℝ) :
    u ∈ (fun w => timeTranslate s + w) '' forwardTube ↔
      (lightConePlus u).re > s ∧ (lightConeMinus u).re > s := by
  rw [← sub_timeTranslate_mem_forwardTube_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩
    have e : timeTranslate s + w - timeTranslate s = w := by abel
    rw [e]
    exact hw
  · intro h
    exact ⟨u - timeTranslate s, h, add_sub_cancel _ _⟩
theorem shiftedForwardTubePow_eq (q : ℕ) (η : ℝ) :
    shiftedForwardTubePow q η =
      {v | ∀ i, (lightConePlus (v i)).re > η / 2 ∧ (lightConeMinus (v i)).re > η / 2} := by
  ext v
  unfold shiftedForwardTubePow translatedPower
  rw [Set.mem_univ_pi]
  exact forall_congr' fun i => mem_translate_image_iff (v i) (η / 2)
theorem forwardTubePow_eq (q : ℕ) :
    forwardTubePow q = {v | ∀ i, (lightConePlus (v i)).re > 0 ∧ (lightConeMinus (v i)).re > 0} := by
  ext v
  unfold forwardTubePow
  rw [Set.mem_univ_pi]
  exact Iff.rfl
theorem halfSpaces_eq_iInter (q : ℕ) (s : ℝ) :
    {v : Fin q → ℂ × ℂ | ∀ i, (lightConePlus (v i)).re > s ∧ (lightConeMinus (v i)).re > s} =
      ⋂ i, ({v | s < (lightConePlus (v i)).re} ∩ {v | s < (lightConeMinus (v i)).re}) := by
  ext v
  simp [Set.mem_iInter]
theorem isOpen_halfSpaces (q : ℕ) (s : ℝ) :
    IsOpen {v : Fin q → ℂ × ℂ | ∀ i, (lightConePlus (v i)).re > s ∧
      (lightConeMinus (v i)).re > s} := by
  rw [halfSpaces_eq_iInter]
  refine isOpen_iInter_of_finite fun i => IsOpen.inter ?_ ?_
  · refine isOpen_lt continuous_const ?_
    unfold lightConePlus
    fun_prop
  · refine isOpen_lt continuous_const ?_
    unfold lightConeMinus
    fun_prop
theorem convex_halfSpaces (q : ℕ) (s : ℝ) :
    Convex ℝ {v : Fin q → ℂ × ℂ | ∀ i, (lightConePlus (v i)).re > s ∧
      (lightConeMinus (v i)).re > s} := by
  rw [halfSpaces_eq_iInter]
  refine convex_iInter fun i => Convex.inter ?_ ?_
  · refine convex_halfSpace_gt ⟨fun x y => ?_, fun c x => ?_⟩ s
    · simp only [re_lightConePlus, Pi.add_apply, Prod.fst_add, Prod.snd_add, Complex.add_re,
        Complex.add_im]
      ring
    · simp only [re_lightConePlus, Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, Complex.real_smul,
        Complex.re_ofReal_mul, Complex.im_ofReal_mul, smul_eq_mul]
      ring
  · refine convex_halfSpace_gt ⟨fun x y => ?_, fun c x => ?_⟩ s
    · simp only [re_lightConeMinus, Pi.add_apply, Prod.fst_add, Prod.snd_add, Complex.add_re,
        Complex.add_im]
      ring
    · simp only [re_lightConeMinus, Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, Complex.real_smul,
        Complex.re_ofReal_mul, Complex.im_ofReal_mul, smul_eq_mul]
      ring
theorem powOpenConvex (q : ℕ) (η : ℝ) : PowOpenConvex q η := by
  refine ⟨shiftedForwardTubePow_eq q η, ?_, ?_, ?_, ?_⟩
  · rw [shiftedForwardTubePow_eq]
    exact isOpen_halfSpaces q _
  · rw [shiftedForwardTubePow_eq]
    exact convex_halfSpaces q _
  · rw [forwardTubePow_eq]
    exact isOpen_halfSpaces q _
  · rw [forwardTubePow_eq]
    exact convex_halfSpaces q _
theorem powNested (q : ℕ) (hq : 1 ≤ q) (η : ℝ) : PowNested q η := by
  refine ⟨fun η' hη' hle => ⟨?_, ?_⟩, fun v hv => ?_⟩
  · rw [shiftedForwardTubePow_eq, shiftedForwardTubePow_eq]
    intro v hv i
    have := hv i
    constructor <;> linarith [this.1, this.2]
  · rw [shiftedForwardTubePow_eq, forwardTubePow_eq]
    intro v hv i
    have := hv i
    constructor <;> linarith [this.1, this.2]
  · rw [forwardTubePow_eq] at hv
    have : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
    obtain ⟨j, hj⟩ := exists_eq_ciInf_of_finite
      (f := fun i : Fin q => min (lightConePlus (v i)).re (lightConeMinus (v i)).re)
    have hinf : 0 < ⨅ i, min (lightConePlus (v i)).re (lightConeMinus (v i)).re := by
      rw [← hj]
      exact lt_min (hv j).1 (hv j).2
    have hpos : 0 < tubeMargin v := lt_min one_pos hinf
    have hle : ∀ i, tubeMargin v ≤ min (lightConePlus (v i)).re (lightConeMinus (v i)).re :=
      fun i => (min_le_right _ _).trans (ciInf_le (Set.finite_range _).bddBelow i)
    refine ⟨⟨hpos, min_le_left _ _⟩, ?_⟩
    rw [shiftedForwardTubePow_eq]
    intro i
    have h₁ := (hle i).trans (min_le_left _ _)
    have h₂ := (hle i).trans (min_le_right _ _)
    constructor <;> linarith
theorem re_lightConePlus_embedPlane (y : RealPlane) : (lightConePlus (embedPlane y)).re = y 0 := by
  simp [re_lightConePlus, embedPlane]
theorem re_lightConeMinus_embedPlane (y : RealPlane) :
    (lightConeMinus (embedPlane y)).re = y 0 := by
  simp [re_lightConeMinus, embedPlane]
theorem realLocus_halfSpaces (q : ℕ) (s : ℝ) :
    realLocus {v : Fin q → ℂ × ℂ | ∀ i, (lightConePlus (v i)).re > s ∧
      (lightConeMinus (v i)).re > s} = embedPlaneTuple '' {y | ∀ i, y i 0 > s} := by
  ext v
  constructor
  · rintro ⟨hv, y, hy⟩
    obtain rfl : v = embedPlaneTuple y := funext hy
    refine ⟨y, fun i => ?_, rfl⟩
    have h := (hv i).1
    rwa [show embedPlaneTuple y i = embedPlane (y i) from rfl, re_lightConePlus_embedPlane] at h
  · rintro ⟨y, hy, rfl⟩
    refine ⟨fun i => ?_, y, fun _ => rfl⟩
    rw [show embedPlaneTuple y i = embedPlane (y i) from rfl, re_lightConePlus_embedPlane,
      re_lightConeMinus_embedPlane]
    exact ⟨hy i, hy i⟩
theorem powRealLocus (q : ℕ) (η : ℝ) : PowRealLocus q η := by
  refine ⟨?_, ?_, ?_⟩
  · rw [shiftedForwardTubePow_eq]
    exact realLocus_halfSpaces q _
  · rw [forwardTubePow_eq]
    exact realLocus_halfSpaces q _
  · ext v
    constructor
    · rintro ⟨hv, y, rfl⟩
      refine ⟨y, Set.mem_univ_pi.2 fun i => ?_, rfl⟩
      have h := (Set.mem_univ_pi.1 hv i).1
      rwa [show embedPlaneTuple y i = embedPlane (y i) from rfl, re_lightConePlus_embedPlane] at h
    · rintro ⟨y, hy, rfl⟩
      refine ⟨Set.mem_univ_pi.2 fun i => ?_, y, rfl⟩
      have h : 0 < y i 0 := Set.mem_univ_pi.1 hy i
      show (lightConePlus (embedPlane (y i))).re > 0 ∧ (lightConeMinus (embedPlane (y i))).re > 0
      rw [re_lightConePlus_embedPlane, re_lightConeMinus_embedPlane]
      exact ⟨h, h⟩
theorem mem_shiftedForwardTube_iff (p : ℕ) (η : ℝ) (x : Fin p → ℂ × ℂ) :
    x ∈ shiftedForwardTube p η ↔
      (∀ h : 0 < p, (lightConePlus (x ⟨0, h⟩)).re > η / 4 ∧
        (lightConeMinus (x ⟨0, h⟩)).re > η / 4) ∧
      ∀ (i : ℕ) (h : i + 1 < p),
        (lightConePlus (x ⟨i + 1, h⟩ - x ⟨i, by omega⟩)).re > η / 2 ∧
        (lightConeMinus (x ⟨i + 1, h⟩ - x ⟨i, by omega⟩)).re > η / 2 := by
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨fun h => (sub_timeTranslate_mem_forwardTube_iff _ _).1 (h₁ h),
      fun i h => (sub_timeTranslate_mem_forwardTube_iff _ _).1 (h₂ i h)⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨fun h => (sub_timeTranslate_mem_forwardTube_iff _ _).2 (h₁ h),
      fun i h => (sub_timeTranslate_mem_forwardTube_iff _ _).2 (h₂ i h)⟩
theorem re_lightConePlus_conjPair (v : ℂ × ℂ) :
    (lightConePlus (conjPair v)).re = (lightConeMinus v).re := by
  simp [re_lightConePlus, re_lightConeMinus, conjPair]
theorem re_lightConeMinus_conjPair (v : ℂ × ℂ) :
    (lightConeMinus (conjPair v)).re = (lightConePlus v).re := by
  simp [re_lightConePlus, re_lightConeMinus, conjPair, sub_eq_add_neg]
theorem conjPair_sub (a b : ℂ × ℂ) : conjPair (a - b) = conjPair a - conjPair b := by
  simp [conjPair]
theorem conjTuple_conjTuple {p : ℕ} (x : Fin p → ℂ × ℂ) : conjTuple (conjTuple x) = x := by
  funext i
  simp [conjTuple, conjPair]
theorem conjTuple_mem_shiftedForwardTube {p : ℕ} {η : ℝ} {x : Fin p → ℂ × ℂ}
    (hx : x ∈ shiftedForwardTube p η) : conjTuple x ∈ shiftedForwardTube p η := by
  obtain ⟨h₁, h₂⟩ := (mem_shiftedForwardTube_iff p η x).1 hx
  refine (mem_shiftedForwardTube_iff p η _).2 ⟨fun h => ?_, fun i h => ?_⟩
  · simp only [conjTuple, re_lightConePlus_conjPair, re_lightConeMinus_conjPair]
    exact ⟨(h₁ h).2, (h₁ h).1⟩
  · simp only [conjTuple, ← conjPair_sub, re_lightConePlus_conjPair, re_lightConeMinus_conjPair]
    exact ⟨(h₂ i h).2, (h₂ i h).1⟩
theorem re_lightConePlus_embedPlane_sub (a b : RealPlane) :
    (lightConePlus (embedPlane a - embedPlane b)).re = a 0 - b 0 := by
  simp [re_lightConePlus, embedPlane]
theorem re_lightConeMinus_embedPlane_sub (a b : RealPlane) :
    (lightConeMinus (embedPlane a - embedPlane b)).re = a 0 - b 0 := by
  simp [re_lightConeMinus, embedPlane]
theorem embedPlaneTuple_mem_iff (p : ℕ) (η : ℝ) (y : Fin p → RealPlane) :
    embedPlaneTuple y ∈ shiftedForwardTube p η ↔ y ∈ orderedTimeTuples p η := by
  rw [mem_shiftedForwardTube_iff]
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun h => ?_, fun i h => ?_⟩
    · have e := (h₁ h).1
      rwa [show embedPlaneTuple y ⟨0, h⟩ = embedPlane (y ⟨0, h⟩) from rfl,
        re_lightConePlus_embedPlane] at e
    · have e := (h₂ i h).1
      rwa [show embedPlaneTuple y ⟨i + 1, h⟩ - embedPlaneTuple y ⟨i, by omega⟩ =
        embedPlane (y ⟨i + 1, h⟩) - embedPlane (y ⟨i, by omega⟩) from rfl,
        re_lightConePlus_embedPlane_sub] at e
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun h => ?_, fun i h => ?_⟩
    · rw [show embedPlaneTuple y ⟨0, h⟩ = embedPlane (y ⟨0, h⟩) from rfl,
        re_lightConePlus_embedPlane, re_lightConeMinus_embedPlane]
      exact ⟨h₁ h, h₁ h⟩
    · rw [show embedPlaneTuple y ⟨i + 1, h⟩ - embedPlaneTuple y ⟨i, by omega⟩ =
        embedPlane (y ⟨i + 1, h⟩) - embedPlane (y ⟨i, by omega⟩) from rfl,
        re_lightConePlus_embedPlane_sub, re_lightConeMinus_embedPlane_sub]
      exact ⟨h₂ i h, h₂ i h⟩
theorem orderedTimeTuples_nonempty (p : ℕ) {η : ℝ} (hη : 0 < η) :
    (orderedTimeTuples p η).Nonempty := by
  refine ⟨fun i => !₂[((i : ℕ) + 1 : ℝ) * η, 0], fun h => ?_, fun i h => ?_⟩
  · simp
    linarith
  · simp
    linarith
theorem isOpen_orderedTimeTuples (p : ℕ) (η : ℝ) : IsOpen (orderedTimeTuples p η) := by
  have e : orderedTimeTuples p η =
      (⋂ h : 0 < p, {y : Fin p → RealPlane | η / 4 < y ⟨0, h⟩ 0}) ∩
        ⋂ j : Fin p, ⋂ h : (j : ℕ) + 1 < p,
          {y : Fin p → RealPlane | η / 2 < y ⟨j + 1, h⟩ 0 - y j 0} := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨h₁, fun j h => h₂ j h⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨h₁, fun i h => h₂ ⟨i, by omega⟩ h⟩
  rw [e]
  refine IsOpen.inter (isOpen_iInter_of_finite fun h => ?_)
    (isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun h => ?_)
  · exact isOpen_lt continuous_const (by fun_prop)
  · exact isOpen_lt continuous_const (by fun_prop)
theorem shiftedTubeRealLocus (p : ℕ) {η : ℝ} (hη : 0 < η) : ShiftedTubeRealLocus p η := by
  refine ⟨Set.ext fun x => mem_shiftedForwardTube_iff p η x, ?_, ?_,
    orderedTimeTuples_nonempty p hη, isOpen_orderedTimeTuples p η⟩
  · apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact conjTuple_mem_shiftedForwardTube hx
    · intro x hx
      exact ⟨conjTuple x, conjTuple_mem_shiftedForwardTube hx, conjTuple_conjTuple x⟩
  · ext v
    constructor
    · rintro ⟨hv, y, hy⟩
      obtain rfl : v = embedPlaneTuple y := funext hy
      exact ⟨y, (embedPlaneTuple_mem_iff p η y).1 hv, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(embedPlaneTuple_mem_iff p η y).2 hy, y, fun _ => rfl⟩
theorem holds : Holds := fun q hq η hη _ =>
  ⟨powOpenConvex q η, powNested q hq η, powRealLocus q η,
    fun p _ => shiftedTubeRealLocus p hη⟩
end YangMills.Construction.ForwardTube.ShiftedTubeCoords
