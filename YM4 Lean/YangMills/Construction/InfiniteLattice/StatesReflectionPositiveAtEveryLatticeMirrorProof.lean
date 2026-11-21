import YangMills.Construction.InfiniteLattice.AllLatticeIsometriesAndTheMeanOfThePlaquetteFunction
import YangMills.Construction.InfiniteLattice.ExpansionsMeetTheConditionsOfTheReconstruction
import YangMills.Construction.InfiniteLattice.GibbsStatesByWindowsAndPeriodGroups
import YangMills.Construction.InfiniteLattice.StatesReflectionPositiveAtEveryLatticeMirror
import Mathlib
set_option autoImplicit false
open MeasureTheory
open YangMills.Construction.OneLoopNotation YangMills.Construction.ComplexHilbert YangMills.Construction.ContractionUnitary
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction.LatticeConventions.ReflectionPositiveStates
open NormalHyperplane
open YangMills.Construction.InfiniteLattice (GaugeField IsShiftInvariant LatticePoint
  localRegionObservables axisStep shift)
open SiteFrame
section Contraction
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
theorem norm_apply_le_of_nonneg_of_le_one {T : BddOp H} (hT : IsSymmetricOp T)
    (hnn : OpGE T 0) (hle1 : OpLE T (idOp H)) (v : H) : ‖T v‖ ≤ ‖v‖ := by
  have hsq : ∀ u : H, (⟪u, u⟫_ℂ).re = ‖u‖ ^ 2 := fun u => by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have hnonneg : ∀ u : H, 0 ≤ (⟪u, T u⟫_ℂ).re := fun u => by
    have h := (Complex.le_def.mp (hnn.le u)).1
    simpa using h
  have hupper : ∀ u : H, (⟪u, T u⟫_ℂ).re ≤ ‖u‖ ^ 2 := fun u => by
    have h := (Complex.le_def.mp (hle1.le u)).1
    have e : (⟪u, (idOp H) u⟫_ℂ).re = ‖u‖ ^ 2 := hsq u
    rwa [e] at h
  have hq := hnonneg (v - T v)
  have e : (⟪v - T v, T (v - T v)⟫_ℂ).re =
      (⟪v, T v⟫_ℂ).re - 2 * ‖T v‖ ^ 2 + (⟪T v, T (T v)⟫_ℂ).re := by
    rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right, hT v (T v)]
    simp only [Complex.sub_re, hsq]
    ring
  rw [e] at hq
  have h₂ := hupper v
  have h₃ := hupper (T v)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp (by linarith)
theorem norm_pow_apply_le_of_nonneg_of_le_one {T : BddOp H} (hT : IsSymmetricOp T)
    (hnn : OpGE T 0) (hle1 : OpLE T (idOp H)) (m : ℕ) (v : H) :
    ‖(T ^ m) v‖ ≤ ‖v‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ']
    exact (norm_apply_le_of_nonneg_of_le_one hT hnn hle1 ((T ^ m) v)).trans ih
theorem inner_pow_two_mul_eq_inner_pow [CompleteSpace H] {T : BddOp H} (hT : IsSymmetricOp T)
    (m : ℕ) (v : H) :
    ⟪v, (T ^ (2 * m)) v⟫_ℂ = ⟪(T ^ m) v, (T ^ m) v⟫_ℂ := by
  have hs : IsSymmetricOp (T ^ m) :=
    (isSymmetricOp_iff _).2 (((isSymmetricOp_iff _).1 hT).pow m)
  rw [two_mul, pow_add]
  exact hs v ((T ^ m) v)
end Contraction
theorem list_ofFn_three {α : Type*} (f : Fin 3 → α) : List.ofFn f = [f 0, f 1, f 2] := by
  simp [List.ofFn_succ]
variable {a : Spacing} {ν : Measure (GaugeField (a : ℝ))} [IsProbabilityMeasure ν]
theorem siteFrameMatrixElements_of_admissible (hRec : MirrorReconstruction)
    (hRows : MirrorExpansions.Statement)
    (hst : LinkFrame.IsAdmissibleState a timeAxis ν) :
    SiteFrameMatrixElements a ν := by
  have row := (hRows.2.1 a timeAxis (SpatialDirection.toDirection 0)
    (timeAxis_ne_toDirection 0) 0 ⟨0, by simp⟩).2.1
  have hmid := row.midPlane_isMid
  rw [sitePicture_normalStep] at hmid
  let w : Fin 3 → LatticePoint (a : ℝ) := fun j => axisStep (a : ℝ) (SpatialDirection.toDirection j)
  have hw : ∀ i, euclidDot (vertexPlane timeAxis).normal (w i : Point) = 0 := fun j => by
    have hd := row.euclidDot_tangentStep
      ⟨SpatialDirection.toDirection j, (timeAxis_ne_toDirection j).symm⟩
    rw [sitePicture_tangentStep] at hd
    exact hd
  have hc : MirrorReconstructionHyps (a : ℝ) (vertexPlane timeAxis)
      (axisStep (a : ℝ) timeAxis : Point) (sitePicture a timeAxis).midPlane
      (fun i => (w i : Point)) :=
    ⟨hmid, row.midPlane_isLatticeMirror, by simp, fun i => (w i).2, hw⟩
  obtain ⟨-, hb, hu, hd⟩ := hRec a _ _ (vertexPlane_isLatticeMirror a timeAxis)
    row.midPlane_isLatticeMirror (axisStep (a : ℝ) timeAxis) 3 w ν hc
    (hst.shiftInvariant _) (fun i => hst.shiftInvariant (w i))
    (reflectionPositive_vertexPlane hst)
    (reflectionPositive_midPlane hst row.midPlane_isLatticeMirror)
  refine ⟨hst, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2, fun j => (hu j).2.1, fun j => hd.1 j,
    fun i j => hd.2.1 i j, ?_⟩
  intro F F' m y
  have hm := hd.2.2 F F' m y
  simp only [list_ofFn_three, List.prod_cons, List.prod_nil, mul_one] at hm
  simp only [mul_assoc]
  exact hm
theorem actOn_shift_zero (F : GaugeField (a : ℝ) → ℂ) :
    (shift (0 : LatticePoint (a : ℝ))).actOn F = F :=
  funext fun U => congrArg F (InfiniteLattice.shift_zero_pullbackField U)
theorem evenCorrelationBounds (hb : SiteFrameMatrixElements a ν) :
    EvenCorrelationBounds a ν := by
  obtain ⟨-, hT, hnn, hle1, -, -, -, hm⟩ := hb
  intro F m
  have hpow : ∀ k : ℕ, reflectedCorrelation a timeAxis ν F.1 (k • axisStep (a : ℝ) timeAxis) =
      ⟪timeClass a ν F, (timeTransferOperator a ν ^ k) (timeClass a ν F)⟫_ℂ := by
    intro k
    have h := hm F F k (fun _ => 0)
    simp only [zpowOp_zero, mul_one, zero_zsmul, Finset.sum_const_zero, add_zero] at h
    exact h.symm
  have hform : siteForm a timeAxis ν F F =
      ⟪timeClass a ν F, timeClass a ν F⟫_ℂ := by
    have h := hpow 0
    rw [zero_nsmul] at h
    have h' : reflectedCorrelation a timeAxis ν F.1 0 = siteForm a timeAxis ν F F := by
      simp only [reflectedCorrelation, reflectedCorrelationFun, actOn_shift_zero]
      rfl
    rw [← h', h]
    simp
  have e₁ : reflectedCorrelation a timeAxis ν F.1 ((2 * m) • axisStep (a : ℝ) timeAxis) =
      ((‖(timeTransferOperator a ν ^ m) (timeClass a ν F)‖ ^ 2 : ℝ) : ℂ) := by
    rw [hpow, inner_pow_two_mul_eq_inner_pow hT, inner_self_eq_norm_sq_to_K]
    norm_cast
  have e₂ : siteForm a timeAxis ν F F = ((‖timeClass a ν F‖ ^ 2 : ℝ) : ℂ) := by
    rw [hform, inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [e₁, e₂]
  simp only [Complex.ofReal_im, Complex.ofReal_re]
  exact ⟨trivial, trivial, by positivity,
    pow_le_pow_left₀ (norm_nonneg _) (norm_pow_apply_le_of_nonneg_of_le_one hT hnn hle1 m _) 2⟩
theorem statement_holds (hIso : LatticeSymmetryInvarianceAndEqualFaceMeans)
    (hRec : MirrorReconstruction)
    (hRows : MirrorExpansions.Statement)
    (hCoarse : CoarseStepFivePointBound) :
    Statement := by
  intro a ν _ hinv hrp
  have hst : LinkFrame.IsAdmissibleState a timeAxis ν := ⟨hinv, fun q => hrp _ _⟩
  have hb := siteFrameMatrixElements_of_admissible hRec hRows hst
  refine ⟨hIso a ν hinv hrp, hb, evenCorrelationBounds hb, ?_⟩
  intro i F k hk
  have hF : F.1 ∈ localRegionObservables (a : ℝ) {x : Point | 0 ≤ x timeAxis} := by
    rw [← coe_upperSpace a timeAxis]
    exact F.2
  exact (hCoarse a timeAxis (SpatialDirection.toDirection i) (timeAxis_ne_toDirection i) ν
    ⟨hinv, fun q => hrp _ _, fun q => hrp _ _⟩).2.1 F.1 hF k hk
end YangMills.Construction.LatticeConventions.ReflectionPositiveStates
end
