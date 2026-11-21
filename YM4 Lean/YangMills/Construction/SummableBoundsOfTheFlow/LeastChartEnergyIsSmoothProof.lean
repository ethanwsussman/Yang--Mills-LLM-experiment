import YangMills.Construction.RunningCouplingSlope.TotalOfAStepReadsNoBoundProof
import YangMills.Construction.RunningCouplingSlope.ContoursAtTheLeastFieldHaveKernelsProof
import YangMills.Construction.RunningCouplingSlope.DensityOfTheStepIsAnalyticAtParametersProof
import YangMills.Construction.SummableBoundsOfTheFlow.LeastChartEnergyIsSmooth
import YangMills.Construction.SummableBoundsOfTheFlow.TheFramesBetween
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ChartedEnergyRegularity
section
open Set Filter Topology
open BlockAverages hiding bondSpread
open ColdStepAtMirrorFrames Interpolation ReferenceDensity
variable {F : BlockFrame}
def gaugeRotated {Zp : Type} (G : Zp → F.GaugeField F.top → ℝ) (V : F.GaugeField F.top) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (p : Zp × (Fin k → ℝ)) : ℝ :=
  G p.1 (leftTranslate (bondSpread c X p.2) V)
abbrev BondComponent (F : BlockFrame) : Type := ↥(chordBonds (finiteCells F)) × Fin 3
def bondBasis (α : BondComponent F) : StepVariable (finiteCells F) :=
  bondVariation α.1 (EuclideanSpace.single α.2 1)
def bondCoord (α : BondComponent F) : StepVariable (finiteCells F) →L[ℝ] ℝ :=
  (EuclideanSpace.proj α.2).comp (ContinuousLinearMap.proj α.1)
theorem bondCoord_apply (α : BondComponent F) (ζ : StepVariable (finiteCells F)) :
    bondCoord α ζ = ζ α.1 α.2 := rfl
theorem eq_sum_bondCoord_smul (ζ : StepVariable (finiteCells F)) :
    ζ = ∑ α : BondComponent F, bondCoord α ζ • bondBasis α := by
  funext b
  ext a
  have h1 : ∀ (b' : ↥(chordBonds (finiteCells F))) (a' : Fin 3),
      ((bondCoord (b', a') ζ • bondBasis (b', a') : StepVariable (finiteCells F)) b) a =
        if b' = b then (if a' = a then ζ b' a' else 0) else 0 := by
    intro b' a'
    simp only [bondCoord_apply, bondBasis, bondVariation, Pi.smul_apply, Pi.single_apply]
    by_cases hb : b = b'
    · subst hb
      by_cases ha : a' = a
      · subst ha; simp
      · simp [ha, Ne.symm ha]
    · simp [hb, Ne.symm hb]
  have h2 : (∑ α : BondComponent F, bondCoord α ζ • bondBasis α) b a =
      ∑ α : BondComponent F, ((bondCoord α ζ • bondBasis α : StepVariable (finiteCells F)) b) a := by
    simp [Finset.sum_apply]
  rw [h2, Fintype.sum_prod_type]
  simp only [h1]
  simp
def imaginaryUnit : imaginaryQuaternions := ⟨⟨0, 1, 0, 0⟩, rfl⟩
theorem norm_coe_imaginaryUnit : ‖(imaginaryUnit : Quaternion ℝ)‖ = 1 := by
  have h1 : Quaternion.normSq (imaginaryUnit : Quaternion ℝ) = 1 := by
    rw [Quaternion.normSq_def']
    show (0 : ℝ) ^ 2 + 1 ^ 2 + 0 ^ 2 + 0 ^ 2 = 1
    norm_num
  have h2 := Quaternion.normSq_eq_norm_mul_self (imaginaryUnit : Quaternion ℝ)
  have h3 := norm_nonneg (imaginaryUnit : Quaternion ℝ)
  nlinarith
theorem norm_imaginaryUnit : ‖imaginaryUnit‖ = 1 := norm_coe_imaginaryUnit
def doubledIndex (F : BlockFrame) (i : Fin (Fintype.card (BondComponent F) + Fintype.card (BondComponent F))) :
    BondComponent F :=
  (Fintype.equivFin (BondComponent F)).symm
    (Fin.addCases (motive := fun _ => Fin (Fintype.card (BondComponent F))) (fun j => j) (fun j => j) i)
def doubledBond (F : BlockFrame) (i : Fin (Fintype.card (BondComponent F) + Fintype.card (BondComponent F))) :
    ↥(chordBonds (finiteCells F)) := (doubledIndex F i).1
def doubledUnit (F : BlockFrame) (i : Fin (Fintype.card (BondComponent F) + Fintype.card (BondComponent F))) :
    EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single (doubledIndex F i).2 1
theorem norm_doubledUnit (F : BlockFrame) (i) : ‖doubledUnit F i‖ = 1 := by
  simp [doubledUnit]
def doubledParams (F : BlockFrame) (η : StepVariable (finiteCells F)) {k : ℕ} (s : Fin k → ℝ) (n : ℕ)
    (p : StepVariable (finiteCells F) × (Fin k → ℝ)) :
    Fin ((Fintype.card (BondComponent F) + Fintype.card (BondComponent F)) + (k + n)) → ℝ :=
  Fin.addCases
    (fun a => Fin.addCases (motive := fun _ => ℝ)
      (fun a₁ => bondCoord ((Fintype.equivFin (BondComponent F)).symm a₁) (p.1 - η)) (fun _ => 0) a)
    (fun d => Fin.addCases (motive := fun _ => ℝ) (fun j => s j * p.2 j) (fun _ => 0) d)
theorem doubledParams_left (F : BlockFrame) (η : StepVariable (finiteCells F)) {k : ℕ} (s : Fin k → ℝ) (n : ℕ)
    (p : StepVariable (finiteCells F) × (Fin k → ℝ)) (a : Fin (Fintype.card (BondComponent F))) :
    doubledParams F η s n p (Fin.castAdd (k + n) (Fin.castAdd _ a)) =
      bondCoord ((Fintype.equivFin (BondComponent F)).symm a) (p.1 - η) := by
  simp only [doubledParams, Fin.addCases_left]
theorem doubledParams_mid (F : BlockFrame) (η : StepVariable (finiteCells F)) {k : ℕ} (s : Fin k → ℝ) (n : ℕ)
    (p : StepVariable (finiteCells F) × (Fin k → ℝ)) (a : Fin (Fintype.card (BondComponent F))) :
    doubledParams F η s n p (Fin.castAdd (k + n) (Fin.natAdd _ a)) = 0 := by
  simp only [doubledParams, Fin.addCases_left, Fin.addCases_right]
theorem doubledParams_top (F : BlockFrame) (η : StepVariable (finiteCells F)) {k : ℕ} (s : Fin k → ℝ) (n : ℕ)
    (p : StepVariable (finiteCells F) × (Fin k → ℝ)) (j : Fin k) :
    doubledParams F η s n p (Fin.natAdd _ (Fin.castAdd n j)) = s j * p.2 j := by
  simp only [doubledParams, Fin.addCases_left, Fin.addCases_right]
theorem doubledParams_pad (F : BlockFrame) (η : StepVariable (finiteCells F)) {k : ℕ} (s : Fin k → ℝ) (n : ℕ)
    (p : StepVariable (finiteCells F) × (Fin k → ℝ)) (j : Fin n) :
    doubledParams F η s n p (Fin.natAdd _ (Fin.natAdd k j)) = 0 := by
  simp only [doubledParams, Fin.addCases_right]
theorem doubledParams_contDiff (F : BlockFrame) (η : StepVariable (finiteCells F)) {k : ℕ} (s : Fin k → ℝ) (n : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (doubledParams F η s n) := by
  refine contDiff_pi.2 fun i => ?_
  refine Fin.addCases (fun a => ?_) (fun d => ?_) i
  · refine Fin.addCases (fun a₁ => ?_) (fun a₂ => ?_) a
    · simp only [doubledParams_left]
      exact (bondCoord _).contDiff.comp (contDiff_fst.sub contDiff_const)
    · simp only [doubledParams_mid]
      exact contDiff_const
  · refine Fin.addCases (fun j => ?_) (fun a₂ => ?_) d
    · simp only [doubledParams_top]
      exact contDiff_const.mul ((contDiff_apply ℝ ℝ j).comp contDiff_snd)
    · simp only [doubledParams_pad]
      exact contDiff_const
theorem doubledParams_base (F : BlockFrame) (η : StepVariable (finiteCells F)) {k : ℕ} (s : Fin k → ℝ) (n : ℕ) :
    doubledParams F η s n (η, 0) = 0 := by
  funext i
  refine Fin.addCases (fun a => ?_) (fun d => ?_) i
  · refine Fin.addCases (fun a₁ => ?_) (fun a₂ => ?_) a
    · rw [doubledParams_left]; simp
    · rw [doubledParams_mid]; rfl
  · refine Fin.addCases (fun j => ?_) (fun a₂ => ?_) d
    · rw [doubledParams_top]; simp
    · rw [doubledParams_pad]; rfl
theorem displacedPoint_doubledParams (F : BlockFrame) (η : StepVariable (finiteCells F)) {k : ℕ} (s : Fin k → ℝ)
    (n : ℕ) (p : StepVariable (finiteCells F) × (Fin k → ℝ)) :
    displacedPoint η (doubledBond F) (doubledUnit F)
      (fun i => doubledParams F η s n p (Fin.castAdd (k + n) i)) = p.1 := by
  simp only [displacedPoint]
  rw [Fin.sum_univ_add]
  have h2 : ∑ i, (Pi.single (doubledBond F (Fin.natAdd _ i))
      (doubledParams F η s n p (Fin.castAdd (k + n) (Fin.natAdd _ i)) • doubledUnit F (Fin.natAdd _ i)) :
        StepVariable (finiteCells F)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [doubledParams_mid]
    simp
  rw [h2, add_zero]
  have h1 : ∀ a : Fin (Fintype.card (BondComponent F)),
      (Pi.single (doubledBond F (Fin.castAdd _ a))
        (doubledParams F η s n p (Fin.castAdd (k + n) (Fin.castAdd _ a)) • doubledUnit F (Fin.castAdd _ a)) :
          StepVariable (finiteCells F)) =
      bondCoord ((Fintype.equivFin (BondComponent F)).symm a) (p.1 - η) •
        bondBasis ((Fintype.equivFin (BondComponent F)).symm a) := by
    intro a
    rw [doubledParams_left]
    simp only [doubledBond, doubledUnit, doubledIndex, Fin.addCases_left, bondBasis, bondVariation]
    rw [Pi.single_smul]
  simp only [h1]
  rw [Equiv.sum_comp (Fintype.equivFin (BondComponent F)).symm
    (fun α => bondCoord α (p.1 - η) • bondBasis α), ← eq_sum_bondCoord_smul]
  abel
theorem bondSpread_doubledParams (F : BlockFrame) (η : StepVariable (finiteCells F)) {k : ℕ} (s : Fin k → ℝ)
    (n : ℕ) (p : StepVariable (finiteCells F) × (Fin k → ℝ)) (c : Fin k → F.Site F.top × Fin 4)
    (X X' : Fin k → imaginaryQuaternions)
    (hX : ∀ j, s j • X' j = X j) (c₀ : F.Site F.top × Fin 4) (X₀ : imaginaryQuaternions) :
    bondSpread (Fin.addCases (motive := fun _ => F.Site F.top × Fin 4) c fun _ : Fin n => c₀)
      (Fin.addCases (motive := fun _ => imaginaryQuaternions) X' fun _ : Fin n => X₀)
      (fun i => doubledParams F η s n p (Fin.natAdd _ i)) = bondSpread c X p.2 := by
  funext y i
  simp only [bondSpread]
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_right, doubledParams_pad, zero_smul, ite_self, Finset.sum_const_zero, add_zero,
    Fin.addCases_left, doubledParams_top]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hX j, smul_smul, mul_comm]
theorem contDiffAt_gaugeRotated {n : ℕ} (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
    (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions)
    (hG : ∀ (p : ℕ) (c' : Fin p → F.Site F.top × Fin 4) (X' : Fin p → imaginaryQuaternions),
      AreUnitVectors X' → n ≤ p →
      ContDiffAt ℝ n (jointDisplacement G η V (doubledBond F) (doubledUnit F) c' X') 0) :
    ContDiffAt ℝ n (gaugeRotated G V c X) (η, 0) := by
  classical
  set X' : Fin k → imaginaryQuaternions :=
    fun j => if X j = 0 then imaginaryUnit else (‖X j‖⁻¹ : ℝ) • X j with hX'
  set s : Fin k → ℝ := fun j => ‖X j‖ with hs
  have hsX : ∀ j, s j • X' j = X j := by
    intro j
    by_cases h : X j = 0
    · simp [hs, hX', h]
    · have h0 : ‖X j‖ ≠ 0 := norm_ne_zero_iff.2 h
      simp only [hs, hX', h, if_false, smul_smul, mul_inv_cancel₀ h0, one_smul]
  have hunit : ∀ j, ‖X' j‖ = 1 := by
    intro j
    by_cases h : X j = 0
    · simp only [hX', h, if_true, norm_imaginaryUnit]
    · have h0 : ‖X j‖ ≠ 0 := norm_ne_zero_iff.2 h
      simp only [hX', h, if_false, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ h0]
  set c₀ : F.Site F.top × Fin 4 := (0, 0)
  set cc := Fin.addCases (motive := fun _ => F.Site F.top × Fin 4) c fun _ : Fin n => c₀ with hcc
  set XX := Fin.addCases (motive := fun _ => imaginaryQuaternions) X' fun _ : Fin n => imaginaryUnit with hXX
  have hu : AreUnitVectors XX := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [hXX, Fin.addCases_left, hunit]
    · simp only [hXX, Fin.addCases_right, norm_imaginaryUnit]
  have h1 := hG (k + n) cc XX hu (by omega)
  have h2 : ContDiffAt ℝ n (doubledParams F η s n) (η, 0) :=
    ((doubledParams_contDiff F η s n).of_le (by exact_mod_cast le_top)).contDiffAt
  have h3 : ContDiffAt ℝ n (jointDisplacement G η V (doubledBond F) (doubledUnit F) cc XX)
      (doubledParams F η s n (η, 0)) := by
    rw [doubledParams_base]; exact h1
  have h4 := ContDiffAt.comp (η, (0 : Fin k → ℝ)) h3 h2
  refine h4.congr_of_eventuallyEq (Eventually.of_forall fun p => ?_)
  simp only [Function.comp, jointDisplacement, gaugeRotated]
  rw [displacedPoint_doubledParams, bondSpread_doubledParams F η s n p c X X' hsX c₀ imaginaryUnit]
end
section
open Set Filter Topology MeasureTheory
open scoped Quaternion
open BlockAverages hiding bondSpread
open ColdStepAtMirrorFrames Interpolation ReferenceDensity
variable {F : BlockFrame} {V : F.GaugeField F.top}
theorem bondSpread_zero {k j : ℕ} (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions) :
    bondSpread c X 0 = 0 := by
  funext y i
  simp [bondSpread]
theorem leftTranslate_zero {j : ℕ} (W : F.GaugeField j) :
    leftTranslate (0 : F.Site j → Fin 4 → imaginaryQuaternions) W = W := by
  funext y i
  have : expUnit (0 : imaginaryQuaternions) = 1 := by
    apply Subtype.ext
    simp [expUnit]
  simp [leftTranslate, this]
def bondBall (F : BlockFrame) (ρ : ℝ) : Set (StepVariable (finiteCells F)) := {η | ∀ b, ‖η b‖ ≤ ρ}
def logContourAverage (a ρ : ℝ) (c₀ : F.Site F.top × Fin 4) :
    StepVariable (finiteCells F) → F.GaugeField F.top → ℝ :=
  fun η V' => Real.log ‖_root_.YangMills.Construction.BlockAverages.contourAverage (fieldAboveFrame true a ρ 0 V' η) c₀‖
theorem interpolatedCoords_zero (a ρ : ℝ) (m : ℕ) (V' : F.GaugeField F.top) (η : StepVariable (finiteCells F)) :
    interpolatedCoords 0 a ρ m V' η = coordsAboveFrame true a ρ 0 V' η := by apply _root_.YangMills.SharedProofs.p718 <;> assumption
theorem logContourNorm_zero (a ρ : ℝ) (m : ℕ) (c₀ : F.Site F.top × Fin 4) :
    (logContourNorm 0 a ρ m c₀ : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) =
      logContourAverage a ρ c₀ := by
  funext η V'
  simp only [logContourNorm, logContourAverage, interpolatedField, fieldAboveFrame, interpolatedCoords_zero]
theorem norm_toImaginary (v : EuclideanSpace ℝ (Fin 3)) : ‖toImaginary v‖ = ‖v‖ := by apply _root_.YangMills.Construction.Interpolation.ExponentBoundSteps.norm_toImaginary <;> assumption
theorem fieldAboveFrame_zero (a ρ : ℝ) (V' : F.GaugeField F.top) :
    fieldAboveFrame true a ρ 0 V' (0 : StepVariable (finiteCells F)) = torusMinimizingField a ρ V' := by apply _root_.YangMills.DeltaSharedProofs.p501148 <;> assumption
theorem continuous_pathHolonomy {j : ℕ} {W : ℝ → F.GaugeField j}
    (hW : ∀ y i, Continuous fun q => ((W q y i : UnitQuaternion) : ℍ[ℝ])) :
    ∀ (l : List PathStep) (x : F.Site j),
      Continuous fun q => ((pathHolonomy (W q) x l : UnitQuaternion) : ℍ[ℝ]) := by
  intro l
  induction l with
  | nil =>
    intro x
    simp only [pathHolonomy]
    exact continuous_const
  | cons st r ih =>
    intro x
    simp only [pathHolonomy, linkValue, Submonoid.coe_mul]
    refine Continuous.mul ?_ (ih _)
    by_cases h : st.2 = true
    · simp only [h, if_true]
      exact hW _ _
    · simp only [h]
      have e : ∀ q, (((W q (x - unitStep j st.1) st.1)⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
          star ((W q (x - unitStep j st.1) st.1 : UnitQuaternion) : ℍ[ℝ]) := by
        intro q
        rw [← Unitary.star_eq_inv, Unitary.coe_star]
      simp only [Bool.false_eq_true, if_false, e]
      exact continuous_star.comp (hW _ _)
theorem stepCoordinates_add_smul (η u : StepVariable (finiteCells F)) (s : ℝ) (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (η + s • u) x i = stepCoordinates η x i + s • stepCoordinates u x i := by apply _root_.YangMills.SharedProofs.p44921 <;> assumption
theorem stepCoordinates_of_not_mem {η : StepVariable (finiteCells F)} {b : F.Site F.depth × Fin 4}
    (h : b ∉ chordBonds (finiteCells F)) : stepCoordinates η b.1 b.2 = 0 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.HessianConvexity.stepCoordinates_of_not_mem <;> assumption
theorem stepCoordinates_bond (η : StepVariable (finiteCells F)) (b : ↥(chordBonds (finiteCells F))) :
    stepCoordinates η b.1.1 b.1.2 = toImaginary (η b) := by apply _root_.YangMills.Construction.Interpolation.ExponentBoundSteps.stepCoordinates_of_chordBond <;> assumption
theorem continuous_fieldAboveFrame_smul (a ρ : ℝ) (η : StepVariable (finiteCells F)) (y : F.Site F.depth)
    (i : Fin 4) :
    Continuous fun s : ℝ => ((fieldAboveFrame true a ρ 0 V (s • η) y i : UnitQuaternion) : ℍ[ℝ]) := by
  let +nondep : NormedAlgebra ℚ ℍ[ℝ] := .restrictScalars ℚ ℝ ℍ[ℝ]
  have hw : Continuous fun s : ℝ =>
      ((coordsAboveFrame true a ρ 0 V (s • η) y i : imaginaryQuaternions) : ℍ[ℝ]) := by
    have e : ∀ s : ℝ, ((coordsAboveFrame true a ρ 0 V (s • η) y i : imaginaryQuaternions) : ℍ[ℝ]) =
        ((ColdStepAtMirrorFrames.stepFrame true a ρ 0 (y, i) V : imaginaryQuaternions) : ℍ[ℝ]) +
          s • ((stepCoordinates η y i : imaginaryQuaternions) : ℍ[ℝ]) := by
      intro s
      have h1 := stepCoordinates_add_smul (0 : StepVariable (finiteCells F)) η s y i
      have h0 : stepCoordinates (0 : StepVariable (finiteCells F)) y i = 0 := by
        simp only [stepCoordinates]
        split_ifs
        · apply Subtype.ext
          ext <;> simp [toImaginary]
        · rfl
      rw [h0, zero_add, zero_add] at h1
      simp only [coordsAboveFrame, h1]
      rfl
    simp only [e]
    fun_prop
  have hexp : Continuous fun s : ℝ =>
      (NormedSpace.exp ((coordsAboveFrame true a ρ 0 V (s • η) y i : imaginaryQuaternions) : ℍ[ℝ]) : ℍ[ℝ]) :=
    NormedSpace.exp_continuous.comp hw
  simp only [fieldAboveFrame, chartedField]
  split_ifs
  · simp only [Submonoid.coe_mul]
    exact hexp.mul continuous_const
  · exact continuous_const
  · exact hexp
theorem continuous_norm_contourAverage_smul (a ρ : ℝ) (η : StepVariable (finiteCells F))
    (c : F.Site F.top × Fin 4) :
    Continuous fun s : ℝ => ‖_root_.YangMills.Construction.BlockAverages.contourAverage (fieldAboveFrame true a ρ 0 V (s • η)) c‖ := by
  simp only [_root_.YangMills.Construction.BlockAverages.contourAverage]
  have h1 : Continuous fun s : ℝ => ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
      ((pathHolonomy (fieldAboveFrame true a ρ 0 V (s • η)) (refineSite c.1)
        (bondContour F.blockSide h π c.2) : UnitQuaternion) : ℍ[ℝ]) := by
    refine continuous_finsetSum _ fun h _ => continuous_finsetSum _ fun π _ => ?_
    exact continuous_pathHolonomy (W := fun s => fieldAboveFrame true a ρ 0 V (s • η))
      (fun y i => continuous_fieldAboveFrame_smul a ρ η y i) _ _
  exact (h1.const_smul (1 / (24 * (F.blockSide : ℝ) ^ 4))).norm
theorem pos_of_continuousOn_log {r : ℝ → ℝ} (hr : Continuous r) (hr0 : 0 ≤ r 0 ∧ r 0 ≠ 0)
    (hn : ∀ s, 0 ≤ r s) (hl : ContinuousOn (fun s => Real.log (r s)) (Icc 0 1)) :
    ∀ s ∈ Icc (0 : ℝ) 1, 0 < r s := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨s₁, hs₁, hs₁0⟩ := hcon
  set A := Icc (0 : ℝ) 1 ∩ r ⁻¹' {0} with hA
  have hAc : IsCompact A := isCompact_Icc.inter_right (isClosed_singleton.preimage hr)
  have hAn : A.Nonempty := ⟨s₁, hs₁, le_antisymm hs₁0 (hn s₁)⟩
  obtain ⟨t₀, ht₀, hmin⟩ := hAc.exists_isLeast hAn
  have hrt : r t₀ = 0 := ht₀.2
  have ht0 : 0 < t₀ := by
    rcases ht₀.1.1.eq_or_lt with h | h
    · rw [← h] at hrt
      exact absurd hrt hr0.2
    · exact h
  have hpos : ∀ s ∈ Ico (0 : ℝ) t₀, 0 < r s := by
    intro s hs
    refine lt_of_le_of_ne (hn s) fun h => ?_
    have : t₀ ≤ s := hmin ⟨⟨hs.1, hs.2.le.trans ht₀.1.2⟩, h.symm⟩
    exact absurd hs.2 (not_lt.2 this)
  have hfil : Ico (0 : ℝ) t₀ ∈ 𝓝[<] t₀ := Ico_mem_nhdsLT ht0
  have h1 : Tendsto r (𝓝[<] t₀) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := (hr.tendsto t₀).mono_left (nhdsWithin_le_nhds (s := Iio t₀))
      rwa [hrt] at this
    · filter_upwards [hfil] with s hs
      exact hpos s hs
  have h2 : Tendsto (fun s => Real.log (r s)) (𝓝[<] t₀) atBot := Real.tendsto_log_nhdsGT_zero.comp h1
  have h3 : Tendsto (fun s => Real.log (r s)) (𝓝[<] t₀) (𝓝 (Real.log (r t₀))) := by
    have h4 := (hl t₀ ht₀.1).tendsto
    have h5 : 𝓝[<] t₀ ≤ 𝓝[Icc 0 1] t₀ := by
      refine nhdsWithin_le_iff.2 ?_
      filter_upwards [hfil] with s hs
      exact ⟨hs.1, hs.2.le.trans ht₀.1.2⟩
    exact h4.mono_left h5
  exact not_tendsto_atBot_of_tendsto_nhds h3 h2
def chartedEnergyOf (a ρ : ℝ) : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ :=
  fun η V' => chartedEnergyAtMinimizer a ρ V' η
theorem interpolatedEnergy_zero (a ρ : ℝ) (m : ℕ) :
    (interpolatedEnergy 0 a ρ m : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) = chartedEnergyOf a ρ := by
  funext η V'
  simp only [interpolatedEnergy, chartedEnergyOf, chartedEnergyAtMinimizer, interpolatedCoords_zero]
theorem contDiffAt_chartedEnergy {a ρA κ κ₂ δ₂ x ρ : ℝ} {m : ℕ} {K : ℕ → ℝ} {D : ℕ → ℕ → ℝ}
    (hK : ∀ η ∈ bondBall F ρ, HasInterpolationKernels 0 a ρA κ κ₂ δ₂ x m K D V η)
    {η : StepVariable (finiteCells F)} (hη : η ∈ bondBall F ρ) :
    ContDiffAt ℝ (2 : ℕ) (chartedEnergyAtMinimizer a ρA V) η := by
  by_cases hne : Nonempty (BondComponent F)
  · have hc : 0 < Fintype.card (BondComponent F) := Fintype.card_pos
    have h1 : ContDiffAt ℝ (2 : ℕ) (gaugeRotated (chartedEnergyOf a ρA) V
        (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions)) (η, 0) := by
      refine contDiffAt_gaugeRotated _ η V _ _ fun p c' X' hX' hp => ?_
      have h2 := ((hK η hη).energy _ p (doubledBond F) (doubledUnit F) c' X' (by omega)
        (norm_doubledUnit F) hX').1
      rw [interpolatedEnergy_zero] at h2
      exact h2.of_le (by exact_mod_cast
        (by omega : 2 ≤ Fintype.card (BondComponent F) + Fintype.card (BondComponent F) + p))
    have hRe : chartedEnergyAtMinimizer a ρA V = fun y => gaugeRotated (chartedEnergyOf a ρA) V
        (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions) (y, 0) := by
      funext y
      show chartedEnergyAtMinimizer a ρA V y = chartedEnergyAtMinimizer a ρA (leftTranslate (bondSpread _ _ 0) V) y
      rw [bondSpread_zero, leftTranslate_zero]
    rw [hRe]
    exact ContDiffAt.comp η (g := gaugeRotated (chartedEnergyOf a ρA) V
      (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions)) h1 (by fun_prop)
  · have hem : IsEmpty ↥(chordBonds (finiteCells F)) := ⟨fun b => hne ⟨(b, 0)⟩⟩
    have hsub : Subsingleton (StepVariable (finiteCells F)) := inferInstance
    have : chartedEnergyAtMinimizer a ρA V = fun _ => chartedEnergyAtMinimizer a ρA V η := by
      funext y
      rw [Subsingleton.elim y η]
    rw [this]
    exact contDiffAt_const
theorem continuousAt_logContourAverage {a ρA κ κ₂ δ₂ x ρ : ℝ} {m : ℕ} {K : ℕ → ℝ} {D : ℕ → ℕ → ℝ}
    (hK : ∀ η ∈ bondBall F ρ, HasInterpolationKernels 0 a ρA κ κ₂ δ₂ x m K D V η) (c₀ : F.Site F.top × Fin 4)
    {y : StepVariable (finiteCells F)} (hy : y ∈ bondBall F ρ) :
    ContinuousAt (fun η => logContourAverage a ρA c₀ η V) y := by
  have h1 : ContDiffAt ℝ (1 : ℕ) (gaugeRotated (logContourAverage a ρA c₀) V
      (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions)) (y, 0) := by
    refine contDiffAt_gaugeRotated _ y V _ _ fun p c' X' hX' hp => ?_
    have h2 := ((hK y hy).logContour c₀ _ p (doubledBond F) (doubledUnit F) c' X' (by omega)
      (norm_doubledUnit F) hX').1
    rw [logContourNorm_zero] at h2
    exact h2.of_le (by exact_mod_cast
      (by omega : 1 ≤ Fintype.card (BondComponent F) + Fintype.card (BondComponent F) + p))
  have hRe : (fun η => logContourAverage a ρA c₀ η V) = fun y => gaugeRotated (logContourAverage a ρA c₀) V
      (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions) (y, 0) := by
    funext y
    show logContourAverage a ρA c₀ y V = logContourAverage a ρA c₀ y (leftTranslate (bondSpread _ _ 0) V)
    rw [bondSpread_zero, leftTranslate_zero]
  rw [hRe]
  exact (ContDiffAt.comp y (g := gaugeRotated (logContourAverage a ρA c₀) V
    (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions)) h1
      (by fun_prop)).continuousAt
theorem deriv_deriv_line {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ψ : E → ℝ} {η : E} (u : E)
    (h : ContDiffAt ℝ (2 : ℕ) Ψ η) :
    deriv (deriv fun τ : ℝ => Ψ (η + τ • u)) 0 = fderiv ℝ (fun y => fderiv ℝ Ψ y u) η u := by apply _root_.YangMills.SharedProofs.p27006 <;> assumption
theorem eventually_parameter_floors :
    EventuallyInParameters fun T => 64 ≤ T.n₀ ∧ 5 / 4 * T.σ ≤ T.chainParams.s₀ := by
  intro a _
  refine ⟨0, fun L _ _ c hc => ⟨0, fun Ct _ => ⟨1, one_pos, fun κ _ _ => ⟨1, one_pos, fun η₃ _ _ _ =>
    ⟨0, fun nss _ => ?_⟩⟩⟩⟩⟩
  have hs : 0 < c.s₀ := hc.classical.1.2.2.1
  refine ⟨4 / 5 * c.s₀, by positivity, fun σ _ hσ p _ => ⟨0, fun Cs _ E _ => ⟨64, fun n₀ hn =>
    ⟨0, fun CE _ => ⟨0, fun y₁ _ => ?_⟩⟩⟩⟩⟩
  refine ⟨hn, ?_⟩
  show 5 / 4 * σ ≤ c.s₀
  linarith
theorem chartedEnergy_regular_of_parameters (T : StepParameters) (hT : T.IsOrdered) (h64 : 64 ≤ T.n₀)
    (hσs : 5 / 4 * T.σ ≤ T.chainParams.s₀)
    {Cq Cz : ℕ → ℝ} {Cr : ℕ → ℕ → ℕ → ℝ}
    (hFB : ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x → InterpolatedFrameBoundsAt T Cq Cz Cr t x)
    {Kf : ℕ → ℝ} {D : ℕ → ℕ → ℝ} (hKe : interpolationKernelBoundsAt T Kf D)
    (t : ℕ) (F : BlockFrame) (V : F.GaugeField F.top) (hF : IsCubicTopTorus T.L t T.n₀ F)
    (hV : IsSmallCurvature (5 / 4 * T.σ) V) :
    ContDiffOn ℝ 2 (chartedEnergyAtMinimizer T.a T.ρA V) {η | ∀ b, ‖η b‖ < T.ballRadius} ∧
      fderiv ℝ (chartedEnergyAtMinimizer T.a T.ρA V) 0 = 0 ∧
      (∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.ballRadius) → ∀ c ∈ innerBonds (finiteCells F) F.top,
        0 < ‖_root_.YangMills.Construction.BlockAverages.contourAverage (fieldAboveFrame true T.a T.ρA 0 V η) c‖) ∧
      0 < T.lam ∧ ∀ η u : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.ballRadius) →
        T.lam * ∑ b, ‖u b‖ ^ 2 ≤ secondDerivAlong (chartedEnergyAtMinimizer T.a T.ρA V) η u u := by
  classical
  have hσ : 0 < T.σ := hT.σ_pos
  obtain ⟨hFL, hFt, n, hside, hnn⟩ := id hF
  have hsm := ((hFB t T.coupling le_rfl).one_torus F V 0 hF hV le_rfl zero_le_one).small
  have hc := hT.chain_admissible
  obtain ⟨⟨hρ0, hρ1, hs₀, hδ, -, -, hC1, -⟩, hcl⟩ := hc.classical
  have hL := hc.inequalities
  have hs0 : 0 < 5 / 4 * T.σ := by positivity
  have hCT : IsBlockTorus T.L F := ⟨hFL, n, by omega, hside⟩
  obtain ⟨hleast, hsc, -, -⟩ := hcl F (5 / 4 * T.σ) V hCT hs0 hσs hV
  have hKst : ∀ η ∈ bondBall F T.ballRadius, HasInterpolationKernels 0 T.a T.ρA T.κ T.chainParams.κ₂
      T.chainParams.δ₂ T.coupling (frameRadius T.coupling) Kf D V η :=
    fun η hη => hKe T.coupling t F V 0 η le_rfl hF hV le_rfl zero_le_one hη
  have hclosed : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.ballRadius) → η ∈ bondBall F T.ballRadius :=
    fun η h b => (h b).le
  refine ⟨fun η hη => ?_, ?_, fun η hη c hc' => ?_, hc.positivity.2.2.1, fun η u hη => ?_⟩
  · have h2 := contDiffAt_chartedEnergy hKst (hclosed η hη)
    exact (by exact_mod_cast h2 : ContDiffAt ℝ 2 (chartedEnergyAtMinimizer T.a T.ρA V) η).contDiffWithinAt
  · have hmin : IsLocalMin (chartedEnergyAtMinimizer T.a T.ρA V) 0 := Eventually.of_forall fun η => by
      have e0 : chartedEnergyAtMinimizer T.a T.ρA V (0 : StepVariable (finiteCells F)) =
          blockEnergy T.a (finiteCells F) F.depth (torusMinimizingField T.a T.ρA V) V := by
        rw [← fieldAboveFrame_zero]
        rfl
      rw [e0]
      exact hleast.2.2 _
    exact hmin.fderiv_eq_zero
  · have hLp : 1 ≤ (F.blockSide : ℤ) := by
      have := hT.odd_L.pos
      rw [hFL]
      exact_mod_cast this
    have h0c : (0 : Fin 4 → ℤ) ∈ centredCube F.blockSide := by
      simp only [centredCube, Fintype.mem_piFinset, Pi.zero_apply, Finset.mem_Icc]
      intro _
      constructor <;> omega
    have h2' := (hsc.2 c 0 1 h0c).2
    rw [← fieldAboveFrame_zero] at h2'
    have h2 : 1 - T.chainParams.C * (5 / 4 * T.σ) ≤ ‖_root_.YangMills.Construction.BlockAverages.contourAverage (fieldAboveFrame true T.a T.ρA 0 V 0) c‖ := h2'
    have hCs : T.chainParams.C * (5 / 4 * T.σ) ≤ 1 / 2 := by
      have h3 : T.chainParams.C * (5 / 4 * T.σ) ≤ T.chainParams.C * T.chainParams.s₀ :=
        mul_le_mul_of_nonneg_left hσs (by linarith)
      have h4 := hL.2.2.2.2.1
      linarith
    have hr := continuous_norm_contourAverage_smul (V := V) T.a T.ρA η c
    have hz : ‖_root_.YangMills.Construction.BlockAverages.contourAverage (fieldAboveFrame true T.a T.ρA 0 V ((0 : ℝ) • η)) c‖ ≠ 0 := by
      rw [zero_smul]
      intro h0
      rw [h0] at h2
      linarith
    have hl : ContinuousOn (fun s : ℝ => Real.log ‖_root_.YangMills.Construction.BlockAverages.contourAverage (fieldAboveFrame true T.a T.ρA 0 V (s • η)) c‖)
        (Icc 0 1) := by
      intro s hs
      have hsS : s • η ∈ bondBall F T.ballRadius := fun b => by
        have h3 : ‖(s • η) b‖ = |s| * ‖η b‖ := by rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs]
        rw [h3, abs_of_nonneg hs.1]
        calc s * ‖η b‖ ≤ 1 * ‖η b‖ := mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)
          _ ≤ T.ballRadius := by simpa using (hη b).le
      have h4 := continuousAt_logContourAverage hKst c hsS
      have h5 : ContinuousAt (fun s' : ℝ => s' • η) s := by fun_prop
      exact (ContinuousAt.comp (f := fun s' : ℝ => s' • η)
        (g := fun η => logContourAverage T.a T.ρA c η V) h4 h5).continuousWithinAt
    have h6 := pos_of_continuousOn_log hr ⟨norm_nonneg _, hz⟩ (fun _ => norm_nonneg _) hl 1
      ⟨zero_le_one, le_rfl⟩
    simpa using h6
  · have hηS := hclosed η hη
    have hS2 := contDiffAt_chartedEnergy hKst hηS
    have hfloor := (hc.estimates F (5 / 4 * T.σ) V hCT hs0 (by linarith) hV).hessian
    have hcold := hsm.small_curvature_nearby η hηS
    have ec : interpolatedField 0 T.a T.chainParams.ρA (frameRadius T.coupling) V η =
        fieldAboveFrame true T.a T.ρA 0 V η := by
      simp only [interpolatedField, fieldAboveFrame, interpolatedCoords_zero]
      rfl
    rw [ec] at hcold
    have hnot : ∀ b : F.Site F.depth × Fin 4, b ∉ chordBonds (finiteCells F) →
        coordsAboveFrame true T.a T.ρA 0 V η b.1 b.2 = 0 := by
      intro b hb
      have h1 : minimizingCoordinates T.a (finiteCells F) V T.chainParams.ρA b.1 b.2 = 0 := hleast.1 b hb
      simp only [coordsAboveFrame, stepCoordinates_of_not_mem hb, add_zero]
      simp only [ColdStepAtMirrorFrames.stepFrame, minimizingBondCoordinate, if_true]
      exact h1
    have hroom : ∀ b ∈ chordBonds (finiteCells F),
        ‖coordsAboveFrame true T.a T.ρA 0 V η b.1 b.2‖ ≤ T.chainParams.ρA := by
      intro b hb
      have h1 := hsm.norm_add_le b hb
      have e1 : interpolatedFrame 0 T.a T.chainParams.ρA (frameRadius T.coupling) b V =
          ColdStepAtMirrorFrames.stepFrame true T.a T.ρA 0 b V := by
        simp [interpolatedFrame, ColdStepAtMirrorFrames.stepFrame]
        rfl
      rw [e1] at h1
      have e2 := stepCoordinates_bond η (⟨b, hb⟩ : ↥(chordBonds (finiteCells F)))
      have e3 : coordsAboveFrame true T.a T.ρA 0 V η b.1 b.2 =
          ColdStepAtMirrorFrames.stepFrame true T.a T.ρA 0 b V + toImaginary (η ⟨b, hb⟩) := by
        simp only [coordsAboveFrame]
        rw [← e2]
      rw [e3]
      have h2 : ‖toImaginary (η ⟨b, hb⟩)‖ ≤ T.σ / 64 := by
        rw [norm_toImaginary]
        exact (hη _).le
      have h3 := norm_add_le (ColdStepAtMirrorFrames.stepFrame true T.a T.ρA 0 b V) (toImaginary (η ⟨b, hb⟩))
      linarith
    have hfl := hfloor (coordsAboveFrame true T.a T.ρA 0 V η) (stepCoordinates u) hnot
      (fun b hb => stepCoordinates_of_not_mem hb) hroom (fun p hp => by
        have h1 := hcold p (Finset.mem_filter.1 hp).2.1
        have h2 : 3 / 4 * T.σ ≤ T.chainParams.σA := by nlinarith
        exact lt_of_lt_of_le h1 h2)
    have hfun : (fun τ : ℝ => blockEnergy T.a (finiteCells F) F.depth
        (chartedField (fun x i => coordsAboveFrame true T.a T.ρA 0 V η x i + τ • stepCoordinates u x i) V) V) =
        fun τ : ℝ => chartedEnergyAtMinimizer T.a T.ρA V (η + τ • u) := by
      funext τ
      have : (fun x i => coordsAboveFrame true T.a T.ρA 0 V η x i + τ • stepCoordinates u x i) =
          coordsAboveFrame true T.a T.ρA 0 V (η + τ • u) := by
        funext x i
        simp only [coordsAboveFrame, stepCoordinates_add_smul, add_assoc]
      rw [this]
      rfl
    rw [hfun, deriv_deriv_line u hS2] at hfl
    have hsum : ∑ b ∈ chordBonds (finiteCells F), ‖stepCoordinates u b.1 b.2‖ ^ 2 = ∑ b, ‖u b‖ ^ 2 := by
      rw [← Finset.sum_coe_sort]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [stepCoordinates_bond, norm_toImaginary]
    rw [hsum] at hfl
    exact hfl
theorem chartedEnergyAtMinimizerRegular_holds (hFB : interpolatedFramesStatement)
    (hKe : interpolationKernelBoundsStatement) :
    chartedEnergyAtMinimizerRegular := by
  obtain ⟨Cq, Cz, Cr, h1⟩ := hFB
  obtain ⟨Kf, D, -, -, h2⟩ := hKe
  have A := EventuallyInParameters.and (EventuallyInParameters.and h1 h2) eventually_parameter_floors
  have Bt : EventuallyOrdered _ := EventuallyInParameters.mono A fun T g _ _ => g
  refine EventuallyOrdered.mono Bt fun T hT hn g => ?_
  obtain ⟨⟨g1, g2⟩, g3, g4⟩ := g
  exact fun t F V hF hV => chartedEnergy_regular_of_parameters T hT g3 g4 g1 g2 t F V hF hV
end
end YangMills.Construction.ChartedEnergyRegularity
end
