import YangMills.Construction.ForwardTube.ElementaryFactsOfTheTubeFramesStripSectorAndPencils
import YangMills.Construction.RotationInvariance.GramKernelStaysPositiveAtImaginaryAngles
import YangMills.Construction.RotationInvariance.MotionsOfPlatesAndQuarterRotationsProof
import YangMills.Construction.RotationInvariance.SectorPencilCutAtTheMirrorAndDoubledPencils
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Complex (I)
open RealPlane ForwardTube
noncomputable section
namespace EuclideanFunctionals.MirrorCut
theorem reflectFirst_sub (a b : RealPlane) :
    reflectFirst (a - b) = reflectFirst a - reflectFirst b := by
  ext i
  fin_cases i <;> simp [reflectFirst]
  ring
theorem reflectFirst_neg (a : RealPlane) : reflectFirst (-a) = -reflectFirst a := by
  ext i
  fin_cases i <;> simp [reflectFirst]
theorem reflectFirst_reflectFirst (a : RealPlane) : reflectFirst (reflectFirst a) = a := by apply _root_.YangMills.Construction.EuclideanFunctionals.ProductMotions.reflectFirst_reflectFirst <;> assumption
theorem embedPlane_sub (a b : RealPlane) : embedPlane (a - b) = embedPlane a - embedPlane b := by
  simp [embedPlane]
theorem embedPlane_mem_forwardTube {v : RealPlane} (h : v ∈ openRightHalf) :
    embedPlane v ∈ forwardTube := by
  have h0 : 0 < v 0 := h
  refine ⟨?_, ?_⟩ <;> simpa [lightConePlus, lightConeMinus, embedPlane] using h0
theorem realTuple_mem_successiveDomain {n : ℕ} (a : Fin n → RealPlane)
    (h0 : ∀ h : 0 < n, a ⟨0, h⟩ ∈ openRightHalf)
    (hd : ∀ (i : ℕ) (h : i + 1 < n), a ⟨i + 1, h⟩ - a ⟨i, by omega⟩ ∈ openRightHalf) :
    realTuple a ∈ successiveDomain n := by
  refine ⟨fun h => embedPlane_mem_forwardTube (h0 h), fun i h => ?_⟩
  have := embedPlane_mem_forwardTube (hd i h)
  rw [embedPlane_sub] at this
  exact this
theorem append_apply_of_lt {α : Type*} {n n' : ℕ} (u : Fin n → α) (v : Fin n' → α) {m : ℕ}
    {h : m < n + n'} (hm : m < n) : Fin.append u v ⟨m, h⟩ = u ⟨m, hm⟩ := by
  have e : (⟨m, h⟩ : Fin (n + n')) = Fin.castAdd n' ⟨m, hm⟩ := rfl
  rw [e, Fin.append_left]
theorem append_apply_of_ge {α : Type*} {n n' : ℕ} (u : Fin n → α) (v : Fin n' → α) {m : ℕ}
    {h : m < n + n'} (hm : n ≤ m) {p : ℕ} {hp : p < n'} (e : p = m - n) :
    Fin.append u v ⟨m, h⟩ = v ⟨p, hp⟩ := by
  have e' : (⟨m, h⟩ : Fin (n + n')) = Fin.natAdd n ⟨p, hp⟩ := by
    ext
    simp only [Fin.val_natAdd]
    omega
  rw [e', Fin.append_right]
theorem rev_mk_eq {n m p : ℕ} {hm : m < n} {hp : p < n} (e : p = n - 1 - m) :
    Fin.rev (⟨m, hm⟩ : Fin n) = ⟨p, hp⟩ := by
  ext
  simp only [Fin.val_rev]
  omega
theorem reflectAppend_apply_of_lt {n n' : ℕ} (a : Fin n → RealPlane) (b : Fin n' → RealPlane)
    {m : ℕ} {h : m < n + n'} (hm : m < n) {p : ℕ} {hp : p < n} (e : p = n - 1 - m) :
    reflectAppend a b ⟨m, h⟩ = reflectFirst (a ⟨p, hp⟩) := by
  unfold reflectAppend
  rw [append_apply_of_lt _ _ hm, rev_mk_eq e]
theorem reflectAppend_apply_of_ge {n n' : ℕ} (a : Fin n → RealPlane) (b : Fin n' → RealPlane)
    {m : ℕ} {h : m < n + n'} (hm : n ≤ m) {p : ℕ} {hp : p < n'} (e : p = m - n) :
    reflectAppend a b ⟨m, h⟩ = b ⟨p, hp⟩ := by
  unfold reflectAppend
  exact append_apply_of_ge _ _ hm e
theorem cutLowerPoints_apply {k l : ℕ} (y : Fin (k + l) → RealPlane) {i : ℕ} {h : i < k}
    {p : ℕ} {hp : p < k + l} (e : p = k - 1 - i) :
    cutLowerPoints y ⟨i, h⟩ = reflectFirst (y ⟨p, hp⟩) := by
  have hp' : p < k := by omega
  unfold cutLowerPoints
  rw [rev_mk_eq (hp := hp') e]
  rfl
theorem cutUpperPoints_apply {k l : ℕ} (y : Fin (k + l) → RealPlane) {j : ℕ} {h : j < l}
    {p : ℕ} {hp : p < k + l} (e : p = k + j) : cutUpperPoints y ⟨j, h⟩ = y ⟨p, hp⟩ := by
  subst e
  rfl
theorem sectorProperties_holds (hE : ForwardTube.TubeFrameStripSectorPencilFacts)
    (φ₀ : openingAngles) : SectorProperties φ₀ := by
  obtain ⟨-, -, -, -, -, -, -, h8⟩ := hE
  obtain ⟨hs, -, hconv, hsm, hsub, hneg, hco, -, -, -⟩ := h8 φ₀
  refine ⟨hconv, hsub, hneg, hco, fun c hc v hv => hsm v hv c hc, fun c hc => ?_⟩
  have hφ : 0 < (φ₀ : ℝ) ∧ (φ₀ : ℝ) < Real.pi / 4 := φ₀.2
  have ht : 0 < Real.tan (φ₀ : ℝ) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two hφ.1 (by linarith [hφ.2, Real.pi_pos])
  rw [hs]
  show |(!₂[c, 0] : RealPlane) 1| < (!₂[c, 0] : RealPlane) 0 * Real.tan (φ₀ : ℝ)
  simpa using mul_pos hc ht
theorem cutDisplay_of_sum_eq_zero {k l : ℕ} (y : Fin (k + 1 + (l + 1)) → RealPlane)
    (hs : y (Fin.castAdd (l + 1) (Fin.last k)) + y (Fin.natAdd (k + 1) 0) = 0) :
    CutDisplay y := by
  have hAB : y ⟨k, by omega⟩ + y ⟨k + 1, by omega⟩ = 0 := hs
  have hA : y ⟨k, by omega⟩ = -y ⟨k + 1, by omega⟩ := eq_neg_of_add_eq_zero_left hAB
  have hv : successiveDifferences y ⟨k, by omega⟩ = y ⟨k + 1, by omega⟩ - y ⟨k, by omega⟩ := rfl
  have hh : (1 / 2 : ℝ) • successiveDifferences y ⟨k, by omega⟩ = y ⟨k + 1, by omega⟩ := by
    rw [hv, hA, sub_neg_eq_add, smul_add, ← add_smul]
    norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hh]
    rfl
  · rw [hh, ← reflectFirst_neg, ← hA]
    exact show cutLowerPoints y ⟨0, by omega⟩ = reflectFirst (y ⟨k, by omega⟩) from
      cutLowerPoints_apply y (by omega)
  · intro j h
    have e1 : cutUpperPoints y ⟨j + 1, h⟩ = y ⟨k + 1 + j + 1, by omega⟩ :=
      cutUpperPoints_apply y (by omega)
    have e2 : cutUpperPoints y ⟨j, by omega⟩ = y ⟨k + 1 + j, by omega⟩ :=
      cutUpperPoints_apply y (by omega)
    rw [e1, e2]
    rfl
  · intro i h
    have e1 : cutLowerPoints y ⟨i + 1, h⟩ = reflectFirst (y ⟨k - 1 - i, by omega⟩) :=
      cutLowerPoints_apply y (by omega)
    have e2 : cutLowerPoints y ⟨i, by omega⟩ = reflectFirst (y ⟨k - 1 - i + 1, by omega⟩) :=
      cutLowerPoints_apply y (by omega)
    have hv' : successiveDifferences y ⟨k - 1 - i, by omega⟩ =
        y ⟨k - 1 - i + 1, by omega⟩ - y ⟨k - 1 - i, by omega⟩ := rfl
    rw [e1, e2, hv', reflectFirst_sub]
    abel
theorem cutVectorsInSector_of_display {φ₀ : openingAngles} (hA : SectorProperties φ₀) {k l : ℕ}
    {y : Fin (k + 1 + (l + 1)) → RealPlane} (hy : y ∈ pencilSet φ₀ (k + 1 + (l + 1)))
    (hd : CutDisplay y) : CutVectorsInSector φ₀ y := by
  obtain ⟨-, -, hneg, -, hsm, -⟩ := hA
  obtain ⟨h1, h2, h3, h4⟩ := hd
  have hk : (1 / 2 : ℝ) • successiveDifferences y ⟨k, by omega⟩ ∈ coneSector φ₀ :=
    hsm _ (by norm_num) _ (hy _)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h1]
    exact hk
  · rw [h2]
    exact hneg _ hk
  · intro j h
    rw [h3 j h]
    exact hy _
  · intro i h
    rw [h4 i h]
    exact hneg _ (hy _)
theorem successiveDifferences_reflectAppend_upper {p : ℕ} (a : Fin (p + 1) → RealPlane) (i : ℕ)
    (h : i + 1 < p + 1) :
    successiveDifferences (reflectAppend a a) ⟨p + 1 + i, by omega⟩ =
      a ⟨i + 1, h⟩ - a ⟨i, by omega⟩ := by
  have e1 : reflectAppend a a ⟨p + 1 + i + 1, by omega⟩ = a ⟨i + 1, h⟩ :=
    reflectAppend_apply_of_ge a a (by omega) (by omega)
  have e2 : reflectAppend a a ⟨p + 1 + i, by omega⟩ = a ⟨i, by omega⟩ :=
    reflectAppend_apply_of_ge a a (by omega) (by omega)
  show reflectAppend a a ⟨p + 1 + i + 1, by omega⟩ -
    reflectAppend a a ⟨p + 1 + i, by omega⟩ = _
  rw [e1, e2]
theorem successiveDifferences_reflectAppend_lower {p : ℕ} (a : Fin (p + 1) → RealPlane) (i : ℕ)
    (h : i + 1 < p + 1) :
    successiveDifferences (reflectAppend a a) ⟨p - 1 - i, by omega⟩ =
      -reflectFirst (a ⟨i + 1, h⟩ - a ⟨i, by omega⟩) := by
  have e1 : reflectAppend a a ⟨p - 1 - i + 1, by omega⟩ = reflectFirst (a ⟨i, by omega⟩) :=
    reflectAppend_apply_of_lt a a (by omega) (by omega)
  have e2 : reflectAppend a a ⟨p - 1 - i, by omega⟩ = reflectFirst (a ⟨i + 1, h⟩) :=
    reflectAppend_apply_of_lt a a (by omega) (by omega)
  show reflectAppend a a ⟨p - 1 - i + 1, by omega⟩ -
    reflectAppend a a ⟨p - 1 - i, by omega⟩ = _
  rw [e1, e2, reflectFirst_sub]
  abel
theorem successiveDifferences_reflectAppend_middle {p : ℕ} (a : Fin (p + 1) → RealPlane) :
    successiveDifferences (reflectAppend a a) ⟨p, by omega⟩ = a 0 - reflectFirst (a 0) := by
  have e1 : reflectAppend a a ⟨p + 1, by omega⟩ = a ⟨0, by omega⟩ :=
    reflectAppend_apply_of_ge a a (by omega) (by omega)
  have e2 : reflectAppend a a ⟨p, by omega⟩ = reflectFirst (a ⟨0, by omega⟩) :=
    reflectAppend_apply_of_lt a a (by omega) (by omega)
  show reflectAppend a a ⟨p + 1, by omega⟩ - reflectAppend a a ⟨p, by omega⟩ = _
  rw [e1, e2]
  rfl
theorem sub_reflectFirst_eq (v : RealPlane) : v - reflectFirst v = !₂[2 * v 0, 0] := by
  ext i
  fin_cases i <;> simp [reflectFirst]
  ring
theorem doubledIsPencil_of_sector {φ₀ : openingAngles} (hA : SectorProperties φ₀) {p : ℕ}
    (a : Fin (p + 1) → RealPlane) (h0 : a 0 ∈ openRightHalf)
    (hd : ∀ (i : ℕ) (h : i + 1 < p + 1), a ⟨i + 1, h⟩ - a ⟨i, by omega⟩ ∈ coneSector φ₀) :
    DoubledIsPencil φ₀ a := by
  refine ⟨?_, successiveDifferences_reflectAppend_upper a,
    successiveDifferences_reflectAppend_lower a, successiveDifferences_reflectAppend_middle a,
    sub_reflectFirst_eq _⟩
  obtain ⟨-, -, hneg, -, -, hc⟩ := hA
  rintro ⟨m, hm⟩
  have hm' : m < p + 1 + (p + 1) - 1 := hm
  rcases lt_trichotomy m p with h | h | h
  · have e : (⟨m, hm⟩ : Fin (p + 1 + (p + 1) - 1)) = ⟨p - 1 - (p - 1 - m), by omega⟩ :=
      Fin.ext (by show m = p - 1 - (p - 1 - m); omega)
    rw [e, successiveDifferences_reflectAppend_lower a (p - 1 - m) (by omega)]
    exact hneg _ (hd _ _)
  · subst h
    rw [successiveDifferences_reflectAppend_middle, sub_reflectFirst_eq]
    have h0' : 0 < a 0 0 := h0
    exact hc _ (by linarith)
  · have e : (⟨m, hm⟩ : Fin (p + 1 + (p + 1) - 1)) = ⟨p + 1 + (m - p - 1), by omega⟩ :=
      Fin.ext (by show m = p + 1 + (m - p - 1); omega)
    rw [e, successiveDifferences_reflectAppend_upper a (m - p - 1) (by omega)]
    exact hd _ _
theorem planeKernel_congr_of_eq {S : ConnFamily} {q q' : ℕ} (h : q = q')
    {φ : Fin (q + 1) → realLabels} {φ' : Fin (q' + 1) → realLabels} {v : Fin q → ℂ × ℂ}
    {v' : Fin q' → ℂ × ℂ}
    (hφ : ∀ i : Fin (q' + 1), φ (Fin.cast (by omega) i) = φ' i)
    (hv : ∀ i : Fin q', v (Fin.cast h.symm i) = v' i) :
    planeKernel S φ v = planeKernel S φ' v' := by
  subst h
  have e1 : φ = φ' := funext hφ
  have e2 : v = v' := funext hv
  rw [e1, e2]
theorem gramKernelImag_ofRealPoints (hArgs : ForwardTube.GramKernelArgsFacts)
    (hGram : GramKernelImagPosSemidef.Holds)
    {m : SharpScale} {S : ConnFamily} (d : PlaneDataWithAperture m S) (s : ℝ) {n n' q : ℕ}
    (hq : n + n' = q + 1) (h2 : 2 ≤ n + n')
    (a : Fin n → RealPlane) (b : Fin n' → RealPlane)
    (ha : realTuple a ∈ successiveDomain n) (hb : realTuple b ∈ successiveDomain n')
    (φa : Fin n → realLabels) (φb : Fin n' → realLabels)
    (w : Fin (q + 1) → RealPlane) (ψ : Fin (q + 1) → realLabels)
    (hw : ∀ i : Fin (q + 1), w i = reflectAppend a b (Fin.cast hq.symm i))
    (hψ : ∀ i : Fin (q + 1), ψ i = gramLabelOrder φa φb (Fin.cast hq.symm i)) :
    gramKernelImag S s (ofRealPoints a ha φa) (ofRealPoints b hb φb) =
      planeKernel S ψ (complexBoostTuple (I * (s : ℂ)) (planeTupleDiffs w)) := by
  have hg := ((hGram m S d).2 s).2.1 (ofRealPoints a ha φa) (ofRealPoints b hb φb) h2
  refine hg.trans (planeKernel_congr_of_eq (by show n + n' - 1 = q; omega) ?_ ?_)
  · intro i
    rw [hψ]
    rfl
  · intro i
    have hc := (hArgs.2.2.1 n n' h2 a b ha hb).1 (Fin.cast (by omega) i)
    have hdiff : successiveDifferences (reflectAppend a b) (Fin.cast (by omega) i) =
        w ⟨(i : ℕ) + 1, by omega⟩ - w ⟨i, by omega⟩ := by
      rw [hw, hw]
      rfl
    show imagBoost s (gramKernelArgs (realTuple a) (realTuple b)
        (Fin.cast (by omega) i)) = complexBoost (I * (s : ℂ)) (embedPlane
          (w ⟨(i : ℕ) + 1, by omega⟩ - w ⟨i, by omega⟩))
    rw [hc, hdiff]
    rfl
theorem planeKernel_eq_angleFunction (hAngle : AngleFunctionOnPencil.Holds)
    {m : SharpScale} {S : ConnFamily} (d : PlaneDataWithAperture m S) {q : ℕ} (hq : 1 ≤ q)
    {y : Fin (q + 1) → RealPlane} (hy : y ∈ pencilSet d.angle (q + 1))
    (φ : Fin (q + 1) → realLabels) (s : ℝ) :
    planeKernel S φ (complexBoostTuple (I * (s : ℂ)) (planeTupleDiffs y)) =
      angleFunction S d.angle y φ (I * (s : ℂ)) := by
  obtain ⟨-, -, -, hv, -⟩ := hAngle m S d q hq y hy φ
  obtain ⟨-, h2, -⟩ := hv
  exact (h2 s).symm
theorem reflectAppend_cut {k l : ℕ} (y : Fin (k + 1 + (l + 1)) → RealPlane) :
    reflectAppend (cutLowerPoints y) (cutUpperPoints y) = y := by
  funext ⟨m, hm⟩
  rcases Nat.lt_or_ge m (k + 1) with h | h
  · have e1 : cutLowerPoints y ⟨k - m, by omega⟩ = reflectFirst (y ⟨m, hm⟩) :=
      cutLowerPoints_apply y (by omega)
    have e0 : reflectAppend (cutLowerPoints y) (cutUpperPoints y) ⟨m, hm⟩ =
        reflectFirst (cutLowerPoints y ⟨k - m, by omega⟩) :=
      reflectAppend_apply_of_lt _ _ h (by omega)
    rw [e0, e1, reflectFirst_reflectFirst]
  · have e1 : cutUpperPoints y ⟨m - (k + 1), by omega⟩ = y ⟨m, hm⟩ :=
      cutUpperPoints_apply y (by omega)
    have e0 : reflectAppend (cutLowerPoints y) (cutUpperPoints y) ⟨m, hm⟩ =
        cutUpperPoints y ⟨m - (k + 1), by omega⟩ := reflectAppend_apply_of_ge _ _ h (by omega)
    rw [e0, e1]
theorem gramLabelOrder_cut {k l : ℕ} (φ : Fin (k + 1 + (l + 1)) → realLabels) :
    gramLabelOrder (cutLowerLabels φ) (cutUpperLabels φ) = φ := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · simp [gramLabelOrder, cutLowerLabels, Fin.append_left]
  · simp [gramLabelOrder, cutUpperLabels, Fin.append_right]
theorem doubledLowerLabels_eq {k l : ℕ} (φ : Fin (k + 1 + (l + 1)) → realLabels) :
    doubledLowerLabels φ = gramLabelOrder (cutLowerLabels φ) (cutLowerLabels φ) := by
  simp [doubledLowerLabels, gramLabelOrder, cutLowerLabels]
  rfl
theorem gramKernelThreeValues_holds (hArgs : ForwardTube.GramKernelArgsFacts)
    (hGram : GramKernelImagPosSemidef.Holds) (hAngle : AngleFunctionOnPencil.Holds)
    {m : SharpScale} {S : ConnFamily} (d : PlaneDataWithAperture m S) {k l : ℕ}
    {y : Fin (k + 1 + (l + 1)) → RealPlane} (hy : y ∈ pencilSet d.angle (k + 1 + (l + 1)))
    (φ : Fin (k + 1 + (l + 1)) → realLabels)
    (hx' : DoubledIsPencil d.angle (cutLowerPoints y))
    (hz' : DoubledIsPencil d.angle (cutUpperPoints y))
    (hx : realTuple (cutLowerPoints y) ∈ successiveDomain (k + 1))
    (hz : realTuple (cutUpperPoints y) ∈ successiveDomain (l + 1)) :
    GramKernelThreeValues S d.angle y φ hx hz := by
  intro s
  have hxz := gramKernelImag_ofRealPoints hArgs hGram d s (n := k + 1) (n' := l + 1)
    (q := k + 1 + l) (by omega) (by omega) (cutLowerPoints y) (cutUpperPoints y) hx hz
    (cutLowerLabels φ) (cutUpperLabels φ) y φ
    (fun i => by rw [reflectAppend_cut]; rfl) (fun i => by rw [gramLabelOrder_cut]; rfl)
  have hxx := gramKernelImag_ofRealPoints hArgs hGram d s (n := k + 1) (n' := k + 1)
    (q := k + 1 + k) (by omega) (by omega) (cutLowerPoints y) (cutLowerPoints y) hx hx
    (cutLowerLabels φ) (cutLowerLabels φ)
    (reflectAppend (n := k + 1) (n' := k + 1) (cutLowerPoints y) (cutLowerPoints y))
    (doubledLowerLabels φ) (fun i => rfl) (fun i => by rw [doubledLowerLabels_eq]; rfl)
  have hzz := gramKernelImag_ofRealPoints hArgs hGram d s (n := l + 1) (n' := l + 1)
    (q := l + 1 + l) (by omega) (by omega) (cutUpperPoints y) (cutUpperPoints y) hz hz
    (cutUpperLabels φ) (cutUpperLabels φ)
    (reflectAppend (n := l + 1) (n' := l + 1) (cutUpperPoints y) (cutUpperPoints y))
    (doubledUpperLabels φ) (fun i => rfl) (fun i => rfl)
  refine ⟨hxz, ?_, ?_, ?_⟩
  · exact planeKernel_eq_angleFunction hAngle d (q := k + 1 + l) (by omega) hy φ s
  · exact hxx.trans (planeKernel_eq_angleFunction hAngle d (q := k + 1 + k) (by omega) hx'.1 _ s)
  · exact hzz.trans (planeKernel_eq_angleFunction hAngle d (q := l + 1 + l) (by omega) hz'.1 _ s)
theorem oneSideEmpty_holds (hArgs : ForwardTube.GramKernelArgsFacts)
    (hGram : GramKernelImagPosSemidef.Holds) (hAngle : AngleFunctionOnPencil.Holds)
    {m : SharpScale} {S : ConnFamily} (d : PlaneDataWithAperture m S)
    (hA : SectorProperties d.angle) {q : ℕ} (hq : 1 ≤ q)
    {y : Fin (q + 1) → RealPlane} (hy : y ∈ pencilSet d.angle (q + 1))
    (h0 : y 0 ∈ coneSector d.angle) (φ : Fin (q + 1) → realLabels) :
    OneSideEmpty S d.angle y φ := by
  have hsub : coneSector d.angle ⊆ openRightHalf := hA.2.1
  have hd : ∀ (i : ℕ) (h : i + 1 < q + 1), y ⟨i + 1, h⟩ - y ⟨i, by omega⟩ ∈ coneSector d.angle :=
    fun i h => hy ⟨i, by omega⟩
  have hdouble := doubledIsPencil_of_sector hA y (hsub h0) hd
  have hmem : realTuple y ∈ successiveDomain (q + 1) :=
    realTuple_mem_successiveDomain y (fun _ => hsub h0) (fun i h => hsub (hd i h))
  refine ⟨hmem, hdouble.1, fun hz s => ⟨?_, ?_, ?_⟩⟩
  · exact ((hGram m S d).2 s).2.2.1 _ _ rfl rfl
  · have hE : realTuple (Fin.elim0 : Fin 0 → RealPlane) ∈ successiveDomain 0 :=
      realTuple_mem_successiveDomain _ (fun h => absurd h (lt_irrefl 0))
        (fun i h => absurd h (by omega))
    have he : ofRealPoints (Fin.elim0 : Fin 0 → RealPlane) hE Fin.elim0 =
        LabelledTuple.nil := LabelledTuple.eq_nil_of_length_eq_zero rfl
    have h := gramKernelImag_ofRealPoints hArgs hGram d s (n := 0) (n' := q + 1) (q := q)
      (by omega) (by omega) Fin.elim0 y hE hz Fin.elim0 φ y φ
      (fun ⟨i, hi⟩ => (reflectAppend_apply_of_ge _ _ (Nat.zero_le _) (by simp)).symm)
      (fun ⟨i, hi⟩ => (append_apply_of_ge _ _ (Nat.zero_le _) (by simp)).symm)
    rw [he] at h
    exact h.trans (planeKernel_eq_angleFunction hAngle d hq hy φ s)
  · have h := gramKernelImag_ofRealPoints hArgs hGram d s (n := q + 1) (n' := q + 1)
      (q := q + 1 + q) (by omega) (by omega) y y hz hz φ φ
      (reflectAppend (n := q + 1) (n' := q + 1) y y) (doubledLabels φ)
      (fun i => rfl) (fun i => rfl)
    exact h.trans (planeKernel_eq_angleFunction hAngle d (q := q + 1 + q) (by omega) hdouble.1 _ s)
theorem holds (hE : ForwardTube.TubeFrameStripSectorPencilFacts)
    (hArgs : ForwardTube.GramKernelArgsFacts)
    (hGram : GramKernelImagPosSemidef.Holds)
    (hAngle : AngleFunctionOnPencil.Holds) : Holds := by
  intro m S d
  have hA := sectorProperties_holds hE d.angle
  refine ⟨hA, ?_, ?_⟩
  · intro k l y hy hs φ
    have hdisp := cutDisplay_of_sum_eq_zero y hs
    have hvec := cutVectorsInSector_of_display hA hy hdisp
    have hsub : coneSector d.angle ⊆ openRightHalf := hA.2.1
    obtain ⟨v1, v2, v3, v4⟩ := id hvec
    have hx : realTuple (cutLowerPoints y) ∈ successiveDomain (k + 1) :=
      realTuple_mem_successiveDomain _ (fun _ => hsub v2) (fun i h => hsub (v4 i h))
    have hz : realTuple (cutUpperPoints y) ∈ successiveDomain (l + 1) :=
      realTuple_mem_successiveDomain _ (fun _ => hsub v1) (fun i h => hsub (v3 i h))
    have hx' := doubledIsPencil_of_sector hA (cutLowerPoints y) (hsub v2) v4
    have hz' := doubledIsPencil_of_sector hA (cutUpperPoints y) (hsub v1) v3
    exact ⟨hdisp, hvec, hx, hz, reflectAppend_cut y, gramLabelOrder_cut φ, hx', hz',
      fun hx₁ hz₁ => gramKernelThreeValues_holds hArgs hGram hAngle d hy φ hx' hz' hx₁ hz₁⟩
  · intro q hq y hy h0 φ
    exact oneSideEmpty_holds hArgs hGram hAngle d hA hq hy h0 φ
end EuclideanFunctionals.MirrorCut
end
end YangMills.Construction
