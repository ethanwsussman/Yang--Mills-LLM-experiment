import YangMills.Construction.RunningCouplingSlope.LeastPointsOverAFieldAreOneOrbitProof
import YangMills.Construction.RunningCouplingSlope.ActionOfAPointIsTheExcessesOfItsSteps
import YangMills.Construction.RunningCouplingSlope.FibreDirectionsAtALeastPointProof
import YangMills.Construction.RunningCouplingSlope.FibreFormIsTheSumOfTheExcessForms
import YangMills.Construction.RunningCouplingSlope.LeastFieldNearTheFlatField
import YangMills.Construction.RunningCouplingSlope.LevelOfAChainReadsTheFieldOfItsStep
import YangMills.Construction.RunningCouplingSlope.MapsOfTheChainAtALeastPoint
import YangMills.Construction.RunningCouplingSlope.SecondDerivativeOfTheExcessReadsTheVelocities
import YangMills.Construction.RunningCouplingSlope.TheChainNearARealPoint
import YangMills.Construction.Matrices.UnitQuaternionsAsMatrices
import YangMills.Construction.SummableBoundsOfTheFlow.LeastActionOfAFrameOnItsTorus
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
open Filter
open scoped Topology Quaternion Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Matrices (ComplexMatrix2)
namespace FibreHessianSum
section Smoothness
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {y₀ : Y}
private theorem contDiffAt_smul {f : Y → ℂ} {g : Y → ComplexMatrix2} (hf : ContDiffAt ℝ 2 f y₀)
    (hg : ContDiffAt ℝ 2 g y₀) : ContDiffAt ℝ 2 (fun y => f y • g y) y₀ := by apply _root_.YangMills.SharedProofs.p3257 <;> assumption
end Smoothness
section QuaternionMatrices
private def quaternionSubmodule : Submodule ℝ ComplexMatrix2 where
  carrier := {M | M 1 1 = star (M 0 0) ∧ M 1 0 = -star (M 0 1)}
  add_mem' := by
    rintro A B ⟨h1, h2⟩ ⟨h3, h4⟩
    refine ⟨?_, ?_⟩
    · simp [Matrix.add_apply, h1, h3]
    · simp only [Matrix.add_apply, h2, h4, star_add]; ring
  zero_mem' := by simp
  smul_mem' := by
    rintro c A ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · simp [Matrix.smul_apply, h1]
    · simp [Matrix.smul_apply, h2]
private theorem compact_mul_mem {g h : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup)
    (hh : h ∈ PeriodicLattice.compactGaugeGroup) : g * h ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.mul_mem_of_mem <;> assumption
private theorem compact_inv_mem {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    g⁻¹ ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
private theorem compact_isUnit_det {g : ComplexMatrix2}
    (hg : g ∈ PeriodicLattice.compactGaugeGroup) : IsUnit g.det := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.det_isUnit_of_mem <;> assumption
end QuaternionMatrices
section LevelRecursion
variable {L n k : ℕ}
private theorem levelField_succ_pos (X : ChainPoint L n k) {j : ℕ} (h : j < k)
    {b : Tower.Edge L n k (j + 1)} (hb : b.IsPositivelyOriented) :
    levelField X (j + 1) b = X.noise ⟨j, h⟩ ⟨b, hb⟩ * normalizedMean (levelField X j) b := by apply _root_.YangMills.SharedProofs.p325 <;> assumption
private theorem levelField_succ_neg (X : ChainPoint L n k) {j : ℕ} (h : j < k)
    {b : Tower.Edge L n k (j + 1)} (hb : ¬b.IsPositivelyOriented) :
    levelField X (j + 1) b = (levelField X (j + 1) b.opposite)⁻¹ := by apply _root_.YangMills.SharedProofs.p5483 <;> assumption
end LevelRecursion
section SmoothFamilies
variable {L n k : ℕ} [NeZero L] {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {y₀ : Y}
  {Z : Y → ChainPoint L n k}
private theorem isUnit_det_of_mem_fieldSpace {j : ℕ} {V : Tower.Edge L n k j → ComplexMatrix2}
    (hV : V ∈ Tower.fieldSpace L n k j) (b : Tower.Edge L n k j) :
    IsUnit (V b).det := compact_isUnit_det (hV.1 b (Set.mem_univ b))
private theorem contDiffAt_levelField (hb : ∀ b, ContDiffAt ℝ 2 (fun y => (Z y).fine b) y₀)
    (hn : ∀ i c, ContDiffAt ℝ 2 (fun y => (Z y).noise i c) y₀) (hX : IsCompactValued (Z y₀)) :
    ∀ j, j ≤ k → ∀ b, ContDiffAt ℝ 2 (fun y => levelField (Z y) j b) y₀ := by apply _root_.YangMills.SharedProofs.p4722 <;> assumption
end SmoothFamilies
section ExponentialMoves
variable {L n k : ℕ} [NeZero L] {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {y₀ : Y}
private theorem contDiffAt_matExp {f : Y → ComplexMatrix2} (hf : ContDiffAt ℝ 2 f y₀) :
    ContDiffAt ℝ 2 (fun y => Matrices.ComplexMatrix2.matExp (f y)) y₀ :=
  ((NormedSpace.exp_analytic (𝕂 := ℝ) (f y₀)).contDiffAt (n := 2)).comp y₀ hf
private theorem matExp_I_smul_zero :
    Matrices.ComplexMatrix2.matExp (Complex.I • (0 : ComplexMatrix2)) = 1 := by
  rw [smul_zero, Matrices.ComplexMatrix2.matExp]
  exact NormedSpace.exp_zero
private theorem contDiffAt_noise_form [FiniteDimensional ℝ Y] (l : Y →ₗ[ℝ] LevelForms L n k)
    (i : Fin k) (c : Tower.Edge L n k (i + 1)) :
    ContDiffAt ℝ 2 (fun y => ((l y).2 i : Tower.Edge L n k (i + 1) → ComplexMatrix2) c) y₀ := by apply _root_.YangMills.SharedProofs.p38354 <;> assumption
private theorem contDiffAt_expMove_fine [FiniteDimensional ℝ Y] (l : Y →ₗ[ℝ] LevelForms L n k)
    {Z : Y → ChainPoint L n k} (hb : ∀ b, ContDiffAt ℝ 2 (fun y => (Z y).fine b) y₀)
    (hu : ∀ b, IsUnit ((Z y₀).fine b).det) (b : Tower.Edge L n k 0) :
    ContDiffAt ℝ 2 (fun y => (expMove (l y) (Z y)).fine b) y₀ := by apply _root_.YangMills.SharedProofs.p2871 <;> assumption
private theorem contDiffAt_expMove_noise [FiniteDimensional ℝ Y] (l : Y →ₗ[ℝ] LevelForms L n k)
    {Z : Y → ChainPoint L n k} (hn : ∀ i c, ContDiffAt ℝ 2 (fun y => (Z y).noise i c) y₀)
    (i : Fin k) (c : Tower.PositiveEdge L n k (i + 1)) :
    ContDiffAt ℝ 2 (fun y => (expMove (l y) (Z y)).noise i c) y₀ := by
  simp only [expMove]
  exact (contDiffAt_matExp (contDiffAt_smul contDiffAt_const
    (contDiffAt_noise_form l i c.1))).mul (hn i c)
end ExponentialMoves
section QuaternionOfMatrix
private abbrev toMat (q : ℍ[ℝ]) : ComplexMatrix2 := SoftAverages.quaternionToMatrix q
private def firstRow : ComplexMatrix2 →ₗ[ℝ] ℍ[ℝ] where
  toFun M := ⟨(M 0 0).re, (M 0 0).im, (M 0 1).re, (M 0 1).im⟩
  map_add' A B := by ext <;> simp <;> rfl
  map_smul' r A := by ext <;> simp <;> rfl
private theorem firstRow_apply (M : ComplexMatrix2) :
    firstRow M = ⟨(M 0 0).re, (M 0 0).im, (M 0 1).re, (M 0 1).im⟩ := rfl
private def firstRowCLM : ComplexMatrix2 →L[ℝ] ℍ[ℝ] := LinearMap.toContinuousLinearMap firstRow
private theorem firstRow_toMat (q : ℍ[ℝ]) : firstRow (toMat q) = q := by
  rw [firstRow_apply]
  ext <;> simp [SoftAverages.quaternionToMatrix]
private theorem toMat_smul (r : ℝ) (q : ℍ[ℝ]) : toMat (r • q) = r • toMat q := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [SoftAverages.quaternionToMatrix] <;> ring
private def toMatCLM : ℍ[ℝ] →L[ℝ] ComplexMatrix2 where
  toFun := toMat
  map_add' := SoftAverages.quaternionToMatrix_add
  map_smul' := toMat_smul
  cont := SoftAverages.continuous_quaternionToMatrix
private theorem quatMatrix_eq_toMat (q : ℍ[ℝ]) : UnitQuaternions.quatMatrix q = toMat q := by apply _root_.YangMills.DeltaSharedProofs.p500685 <;> assumption
private theorem exists_toMat_of_mem {A : ComplexMatrix2} (hA : A ∈ PeriodicLattice.compactGaugeGroup) :
    ∃ g : BlockAverages.UnitQuaternion, A = toMat (g : ℍ[ℝ]) := by
  obtain ⟨g, hg⟩ := UnitQuaternions.toSpecialUnitaryHom_surjective ⟨A, hA⟩
  refine ⟨g, ?_⟩
  have := congrArg Subtype.val hg
  rw [← quatMatrix_eq_toMat]
  exact this.symm
open Classical in
private def unitOfMatrix (M : ComplexMatrix2) : BlockAverages.UnitQuaternion :=
  if h : ∃ g : BlockAverages.UnitQuaternion, M = toMat (g : ℍ[ℝ]) then h.choose else 1
private theorem toMat_unitOfMatrix {M : ComplexMatrix2}
    (h : ∃ g : BlockAverages.UnitQuaternion, M = toMat (g : ℍ[ℝ])) :
    toMat (unitOfMatrix M : ℍ[ℝ]) = M := by
  rw [unitOfMatrix, dif_pos h]
  exact h.choose_spec.symm
private theorem coe_unitOfMatrix {M : ComplexMatrix2}
    (h : ∃ g : BlockAverages.UnitQuaternion, M = toMat (g : ℍ[ℝ])) :
    ((unitOfMatrix M : BlockAverages.UnitQuaternion) : ℍ[ℝ]) = firstRow M := by
  conv_rhs => rw [← toMat_unitOfMatrix h]
  exact (firstRow_toMat _).symm
private theorem unitOfMatrix_toMat (g : BlockAverages.UnitQuaternion) :
    unitOfMatrix (toMat (g : ℍ[ℝ])) = g :=
  Subtype.ext ((coe_unitOfMatrix ⟨g, rfl⟩).trans (firstRow_toMat _))
private def pureQuat (c : Fin 3 → ℝ) : ℍ[ℝ] := ⟨0, c 0, c 1, c 2⟩
private theorem suTwoComponents_inv_I_smul (w : ℍ[ℝ]) :
    suTwoComponents (Complex.I⁻¹ • toMat w) = imaginaryComponents w := by
  funext i
  fin_cases i <;> simp [suTwoComponents, imaginaryComponents, SoftAverages.quaternionToMatrix]
private theorem hasDerivAt_firstRow_of_curve {f : ℝ → ComplexMatrix2}
    {W : BlockAverages.UnitQuaternion} {m : ComplexMatrix2}
    (hf : HasDerivAt f ((Complex.I • m) * toMat (W : ℍ[ℝ])) 0) (h0 : f 0 = toMat (W : ℍ[ℝ]))
    (hr : ∀ᶠ r in 𝓝 (0 : ℝ), ∃ g : BlockAverages.UnitQuaternion, f r = toMat (g : ℍ[ℝ])) :
    HasDerivAt (fun r => firstRowCLM (f r)) (pureQuat (suTwoComponents m) * (W : ℍ[ℝ])) 0 := by
  have hu : HasDerivAt (fun r => firstRowCLM (f r))
      (firstRowCLM ((Complex.I • m) * toMat (W : ℍ[ℝ]))) 0 :=
    firstRowCLM.hasFDerivAt.comp_hasDerivAt 0 hf
  obtain ⟨d, hd⟩ : ∃ d, d = firstRowCLM ((Complex.I • m) * toMat (W : ℍ[ℝ])) := ⟨_, rfl⟩
  rw [← hd] at hu
  obtain ⟨u, hudef⟩ : ∃ u : ℝ → ℍ[ℝ], u = fun r => firstRowCLM (f r) := ⟨_, rfl⟩
  rw [← hudef] at hu ⊢
  have hu0 : u 0 = (W : ℍ[ℝ]) := by
    rw [hudef]
    show firstRow (f 0) = _
    rw [h0, firstRow_toMat]
  have hq : HasDerivAt (fun r => toMatCLM (u r)) (toMatCLM d) 0 :=
    toMatCLM.hasFDerivAt.comp_hasDerivAt 0 hu
  have hqf : (fun r => toMatCLM (u r)) =ᶠ[𝓝 0] f := by
    filter_upwards [hr] with r hg
    obtain ⟨g, hg⟩ := hg
    rw [hudef]
    show toMat (firstRow (f r)) = f r
    rw [hg, firstRow_toMat]
  have hDd : toMat d = (Complex.I • m) * toMat (W : ℍ[ℝ]) :=
    (hq.congr_of_eventuallyEq hqf.symm).unique hf
  have hone : (fun r => u r * star (u r)) =ᶠ[𝓝 0] fun _ => (1 : ℍ[ℝ]) := by
    filter_upwards [hr] with r hg
    obtain ⟨g, hg⟩ := hg
    have e : u r = (g : ℍ[ℝ]) := by
      rw [hudef]
      show firstRow (f r) = _
      rw [hg, firstRow_toMat]
    rw [e]
    exact Unitary.coe_mul_star_self g
  haveI : StarModule ℝ ℍ[ℝ] := ⟨fun r q => by rw [star_trivial r]; exact Quaternion.star_smul r q⟩
  have hmul : HasDerivAt (fun r => u r * star (u r)) (d * star (u 0) + u 0 * star d) 0 :=
    hu.mul hu.star
  have hz : d * star (W : ℍ[ℝ]) + (W : ℍ[ℝ]) * star d = 0 := by
    have := (hmul.congr_of_eventuallyEq hone.symm).unique (hasDerivAt_const (0 : ℝ) (1 : ℍ[ℝ]))
    rwa [hu0] at this
  obtain ⟨w, hw⟩ : ∃ w, w = d * star (W : ℍ[ℝ]) := ⟨_, rfl⟩
  have hwre : w.re = 0 := by
    have e : (W : ℍ[ℝ]) * star d = star w := by simp [hw, star_mul]
    rw [e, ← hw] at hz
    have h := congrArg (fun p : ℍ[ℝ] => p.re) hz
    simp at h
    linarith
  have hWs : star (W : ℍ[ℝ]) * (W : ℍ[ℝ]) = 1 := Unitary.coe_star_mul_self W
  have hWs' : (W : ℍ[ℝ]) * star (W : ℍ[ℝ]) = 1 := Unitary.coe_mul_star_self W
  have hdw : w * (W : ℍ[ℝ]) = d := by rw [hw, mul_assoc, hWs, mul_one]
  have hqw : toMat w = Complex.I • m := by
    rw [hw]
    show SoftAverages.quaternionToMatrix _ = _
    rw [SoftAverages.quaternionToMatrix_mul]
    show toMat d * toMat _ = _
    rw [hDd, mul_assoc]
    show _ * (SoftAverages.quaternionToMatrix _ * SoftAverages.quaternionToMatrix _) = _
    rw [← SoftAverages.quaternionToMatrix_mul, hWs', SoftAverages.quaternionToMatrix_one, mul_one]
  have hl : suTwoComponents m = imaginaryComponents w := by
    rw [← suTwoComponents_inv_I_smul, hqw, smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
  have hqv : pureQuat (suTwoComponents m) = w := by
    rw [hl]
    ext <;> simp [pureQuat, imaginaryComponents, hwre]
  rw [hqv, hdw]
  exact hu
end QuaternionOfMatrix
section FibreLine
variable {L n k : ℕ} [NeZero L]
private theorem levelField_fibreMove (X : ChainPoint L n (k + 1)) (ξ : LevelForms L n (k + 1)) :
    ∀ j, j ≤ k → levelField (fibreMove X ξ) j = levelField (expMove ξ X) j := by apply _root_.YangMills.Construction.RunningCouplingSlope.MinimizerHessian.levelField_fibreMove_of_le <;> assumption
private theorem normalizedMean_mem {k : ℕ} {P : ChainPoint L n k} (hP : IsCompactValued P)
    (i : Fin k) (c : Tower.PositiveEdge L n k (i + 1)) :
    normalizedMean (levelField P i) c.1 ∈ PeriodicLattice.compactGaugeGroup := by
  have h1 := hP.1 i c
  have h2 := (hP.2 (i + 1) i.2).1 c.1 (Set.mem_univ _)
  rw [levelField_succ_pos P i.2 c.2] at h2
  have h2' : P.noise i c * normalizedMean (levelField P i) c.1 ∈
      PeriodicLattice.compactGaugeGroup := h2
  have e : normalizedMean (levelField P i) c.1 =
      (P.noise i c)⁻¹ * (P.noise i c * normalizedMean (levelField P i) c.1) := by
    rw [← mul_assoc, Matrix.nonsing_inv_mul _ (compact_isUnit_det h1), one_mul]
  rw [e]
  exact compact_mul_mem (compact_inv_mem h1) h2'
private theorem levelField_fibreMove_top (X : ChainPoint L n (k + 1)) (ξ : LevelForms L n (k + 1))
    (hP : IsCompactValued (expMove ξ X)) :
    levelField (fibreMove X ξ) (k + 1) = levelField X (k + 1) := by
  have hk : k < k + 1 := by omega
  have hpos : ∀ b : Tower.Edge L n (k + 1) (k + 1), b.IsPositivelyOriented →
      levelField (fibreMove X ξ) (k + 1) b = levelField X (k + 1) b := by
    intro b hb
    rw [levelField_succ_pos _ hk hb, levelField_fibreMove X ξ k le_rfl]
    have hif : (⟨k, hk⟩ : Fin (k + 1)).val + 1 = k + 1 := rfl
    have e : (fibreMove X ξ).noise ⟨k, hk⟩ ⟨b, hb⟩ =
        levelField X (k + 1) b * (normalizedMean (levelField (expMove ξ X) k) b)⁻¹ := by
      simp only [fibreMove, if_pos hif]
      exact if_pos trivial
    have hu := compact_isUnit_det (normalizedMean_mem hP ⟨k, hk⟩ ⟨b, hb⟩)
    rw [e, mul_assoc]
    have hu' : IsUnit (normalizedMean (levelField (expMove ξ X) k) b).det := hu
    rw [Matrix.nonsing_inv_mul _ hu', mul_one]
  funext b
  by_cases hb : b.IsPositivelyOriented
  · exact hpos b hb
  · rw [levelField_succ_neg _ hk hb, levelField_succ_neg _ hk hb,
      hpos _ (PeriodicLattice.Bond.opposite_isPositivelyOriented hb)]
private theorem fibreMove_isCompactValued {X : ChainPoint L n (k + 1)} {ξ : LevelForms L n (k + 1)}
    (hX : IsCompactValued X) (hP : IsCompactValued (expMove ξ X)) :
    IsCompactValued (fibreMove X ξ) := by
  refine ⟨fun i c => ?_, fun j hj => ?_⟩
  · by_cases h : i.val + 1 = k + 1
    · simp only [fibreMove, if_pos h]
      exact compact_mul_mem ((hX.2 (i + 1) i.2).1 c.1 (Set.mem_univ _))
        (compact_inv_mem (normalizedMean_mem hP i c))
    · simp only [fibreMove, if_neg h]
      exact hP.1 i c
  · rcases Nat.lt_or_ge k j with h | h
    · obtain rfl : j = k + 1 := by omega
      rw [levelField_fibreMove_top X ξ hP]
      exact hX.2 _ le_rfl
    · rw [levelField_fibreMove X ξ j h]
      exact hP.2 j hj
private theorem expMove_zero {k : ℕ} {X : ChainPoint L n k} (hX : IsCompactValued X) :
    expMove (0 : LevelForms L n k) X = X := by
  have hc : X.fine ∈ Tower.fieldSpace L n k 0 := hX.2 0 (Nat.zero_le _)
  have hb : PeriodicLattice.expTwist ((0 : LevelForms L n k).1) X.fine = X.fine := by
    funext b
    by_cases h : b.IsPositivelyOriented
    · simp [PeriodicLattice.expTwist, h, matExp_I_smul_zero]
    · simp [PeriodicLattice.expTwist, h, matExp_I_smul_zero]
      exact (hc.2 b.opposite (Set.mem_univ _)).symm
  have hn : (fun i c => Matrices.ComplexMatrix2.matExp (Complex.I • ((0 : LevelForms L n k).2 i :
      Tower.Edge L n k (i + 1) → ComplexMatrix2) c) * X.noise i c) = X.noise := by
    funext i c
    simp [matExp_I_smul_zero]
  show ChainPoint.mk _ _ = X
  rw [hb, hn]
private theorem contDiffAt_levelField_expMove {X : ChainPoint L n (k + 1)}
    {ξ : LevelForms L n (k + 1)}
    (hX : IsCompactValued X) (hP : IsCompactValued (expMove ((0 : ℝ) • ξ) X)) :
    ∀ j, j ≤ k + 1 → ∀ b, ContDiffAt ℝ 2 (fun r : ℝ => levelField (expMove (r • ξ) X) j b) 0 := by
  have hunit : ∀ b : Tower.Edge L n (k + 1) 0, IsUnit (X.fine b).det := fun b =>
    isUnit_det_of_mem_fieldSpace (hX.2 0 (Nat.zero_le _)) b
  refine contDiffAt_levelField (Z := fun r : ℝ => expMove (r • ξ) X) (y₀ := (0 : ℝ))
    (fun b => ?_) (fun i c => ?_) hP
  · exact contDiffAt_expMove_fine (Y := ℝ) (y₀ := 0) (LinearMap.toSpanSingleton ℝ _ ξ)
      (Z := fun _ => X) (fun _ => contDiffAt_const) hunit b
  · exact contDiffAt_expMove_noise (Y := ℝ) (y₀ := 0) (LinearMap.toSpanSingleton ℝ _ ξ)
      (Z := fun _ => X) (fun _ _ => contDiffAt_const) i c
private theorem levelField_fibreMove_zero_smul {X : ChainPoint L n (k + 1)}
    {ξ : LevelForms L n (k + 1)}
    (hX : IsCompactValued X) (hP : IsCompactValued (expMove ((0 : ℝ) • ξ) X)) (l : ℕ)
    (hl : l ≤ k + 1) :
    levelField (fibreMove X ((0 : ℝ) • ξ)) l = levelField X l := by
  rcases Nat.lt_or_ge k l with h | h
  · obtain rfl : l = k + 1 := by omega
    exact levelField_fibreMove_top X _ hP
  · rw [levelField_fibreMove X _ l h, zero_smul, expMove_zero hX]
private theorem contDiffAt_levelField_fibreMove {X : ChainPoint L n (k + 1)}
    {ξ : LevelForms L n (k + 1)}
    (hX : IsCompactValued X) (hP : ∀ᶠ r in 𝓝 (0 : ℝ), IsCompactValued (expMove (r • ξ) X))
    {l : ℕ} (hl : l ≤ k + 1) (b : Tower.Edge L n (k + 1) l) :
    ContDiffAt ℝ 2 (fun r : ℝ => levelField (fibreMove X (r • ξ)) l b) 0 := by
  rcases Nat.lt_or_ge k l with h | h
  · obtain rfl : l = k + 1 := by omega
    refine (contDiffAt_const (c := levelField X (k + 1) b)).congr_of_eventuallyEq ?_
    filter_upwards [hP] with r hr
    rw [levelField_fibreMove_top X _ hr]
  · have e : (fun r : ℝ => levelField (fibreMove X (r • ξ)) l b) =
        fun r : ℝ => levelField (expMove (r • ξ) X) l b :=
      funext fun r => by rw [levelField_fibreMove X _ l h]
    rw [e]
    exact contDiffAt_levelField_expMove hX hP.self_of_nhds l hl b
private theorem hasDerivAt_levelField_fibreMove {X : ChainPoint L n (k + 1)}
    {ξ : LevelForms L n (k + 1)}
    (hP : ∀ᶠ r in 𝓝 (0 : ℝ), IsCompactValued (expMove (r • ξ) X))
    (hv : ∀ j, j ≤ k + 1 → ∀ b : Tower.Edge L n (k + 1) j, b.IsPositivelyOriented →
      HasDerivAt (fun r : ℝ => levelField (expMove (r • ξ) X) j b)
        ((Complex.I • tangentTransport X ξ j b) * levelField X j b) 0)
    (hm : tangentTransport X ξ (k + 1) = 0)
    {l : ℕ} (hl : l ≤ k + 1) {b : Tower.Edge L n (k + 1) l} (hb : b.IsPositivelyOriented) :
    HasDerivAt (fun r : ℝ => levelField (fibreMove X (r • ξ)) l b)
      ((Complex.I • tangentTransport X ξ l b) * levelField X l b) 0 := by
  rcases Nat.lt_or_ge k l with h | h
  · obtain rfl : l = k + 1 := by omega
    have e : (fun r : ℝ => levelField (fibreMove X (r • ξ)) (k + 1) b) =ᶠ[𝓝 0]
        fun _ => levelField X (k + 1) b := by
      filter_upwards [hP] with r hr
      rw [levelField_fibreMove_top X _ hr]
    rw [hm]
    simp only [Pi.zero_apply, smul_zero, zero_mul]
    exact (hasDerivAt_const _ _).congr_of_eventuallyEq e
  · have e : (fun r : ℝ => levelField (fibreMove X (r • ξ)) l b) =
        fun r : ℝ => levelField (expMove (r • ξ) X) l b :=
      funext fun r => by rw [levelField_fibreMove X _ l h]
    rw [e]
    exact hv l hl b hb
private def levelOnFrame {K : ℕ} (P : ChainPoint L n K) (l : ℕ) {F : BlockAverages.BlockFrame}
    {i : ℕ} : F.GaugeField i :=
  fun x μ => unitOfMatrix (levelField P l (edgeOfCoords l (x, μ)))
private theorem exists_toMat_levelField {K : ℕ} {P : ChainPoint L n K} (hP : IsCompactValued P)
    {l : ℕ} (hl : l ≤ K) (b : Tower.Edge L n K l) :
    ∃ g : BlockAverages.UnitQuaternion, levelField P l b = toMat (g : ℍ[ℝ]) :=
  exists_toMat_of_mem ((hP.2 l hl).1 b (Set.mem_univ _))
private theorem levelField_edgeOfCoords {K : ℕ} {P : ChainPoint L n K} (hP : IsCompactValued P)
    {l : ℕ} (hl : l ≤ K) {F : BlockAverages.BlockFrame} {i : ℕ} (b : F.Site i × Fin 4) :
    levelField P l (edgeOfCoords l b) =
      SoftAverages.quaternionToMatrix
        ((levelOnFrame P l b.1 b.2 : BlockAverages.UnitQuaternion) : ℍ[ℝ]) :=
  (toMat_unitOfMatrix (exists_toMat_levelField hP hl _)).symm
private theorem contDiffAt_levelOnFrame {X : ChainPoint L n (k + 1)} {ξ : LevelForms L n (k + 1)}
    (hX : IsCompactValued X) (hP : ∀ᶠ r in 𝓝 (0 : ℝ), IsCompactValued (expMove (r • ξ) X))
    {l : ℕ} (hl : l ≤ k + 1) {F : BlockAverages.BlockFrame} {i : ℕ} (x : F.Site i) (μ : Fin 4) :
    ContDiffAt ℝ 2 (fun r : ℝ =>
      ((levelOnFrame (fibreMove X (r • ξ)) l x μ : BlockAverages.UnitQuaternion) : ℍ[ℝ])) 0 := by
  have h := firstRowCLM.contDiff.contDiffAt.comp (0 : ℝ)
    (contDiffAt_levelField_fibreMove hX hP hl (edgeOfCoords l (x, μ)))
  refine ContDiffAt.congr_of_eventuallyEq h ?_
  filter_upwards [hP] with r hr
  exact coe_unitOfMatrix (exists_toMat_levelField (fibreMove_isCompactValued hX hr) hl _)
private theorem hasDerivAt_levelOnFrame {X : ChainPoint L n (k + 1)} {ξ : LevelForms L n (k + 1)}
    (hX : IsCompactValued X) (hP : ∀ᶠ r in 𝓝 (0 : ℝ), IsCompactValued (expMove (r • ξ) X))
    (hv : ∀ j, j ≤ k + 1 → ∀ b : Tower.Edge L n (k + 1) j, b.IsPositivelyOriented →
      HasDerivAt (fun r : ℝ => levelField (expMove (r • ξ) X) j b)
        ((Complex.I • tangentTransport X ξ j b) * levelField X j b) 0)
    (hm : tangentTransport X ξ (k + 1) = 0)
    {l : ℕ} (hl : l ≤ k + 1) {F : BlockAverages.BlockFrame} {i : ℕ} (x : F.Site i) (μ : Fin 4) :
    HasDerivAt (fun r : ℝ =>
        ((levelOnFrame (fibreMove X (r • ξ)) l x μ : BlockAverages.UnitQuaternion) : ℍ[ℝ]))
      ((frameVelocityOfForm l (tangentTransport X ξ l) x μ : ℍ[ℝ]) *
        ((levelOnFrame (fibreMove X ((0 : ℝ) • ξ)) l x μ : BlockAverages.UnitQuaternion) :
          ℍ[ℝ])) 0 := by
  have hpos : (edgeOfCoords (L := L) (n := n) (k := k + 1) l (x, μ)).IsPositivelyOriented :=
    ⟨μ, by simp [edgeOfCoords, PeriodicLattice.Bond.forwardFrom]⟩
  have hr0 : IsCompactValued (fibreMove X ((0 : ℝ) • ξ)) :=
    fibreMove_isCompactValued hX hP.self_of_nhds
  have h0 := levelField_edgeOfCoords hr0 hl (x, μ)
  have hz := congrFun (levelField_fibreMove_zero_smul hX hP.self_of_nhds l hl)
    (edgeOfCoords l (x, μ))
  have hf := hasDerivAt_levelField_fibreMove hP hv hm hl hpos
  rw [← hz, h0] at hf
  have hc := hasDerivAt_firstRow_of_curve hf h0 (by
    filter_upwards [hP] with r hr
    exact exists_toMat_levelField (fibreMove_isCompactValued hX hr) hl _)
  refine HasDerivAt.congr_of_eventuallyEq hc ?_
  filter_upwards [hP] with r hr
  exact coe_unitOfMatrix (exists_toMat_levelField (fibreMove_isCompactValued hX hr) hl _)
end FibreLine
private theorem differentiableAt_deriv_of_contDiffAt {f : ℝ → ℝ} (hf : ContDiffAt ℝ 2 f 0) :
    DifferentiableAt ℝ (deriv f) 0 := by
  have h : ContDiffAt ℝ 1 (fun r => fderiv ℝ f r 1) 0 :=
    (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
  exact h.differentiableAt (by norm_num)
private theorem deriv_comp_add_zero (g : ℝ → ℝ) (s : ℝ) :
    deriv (fun t => g (s + t)) 0 = deriv g s := by
  rw [deriv_comp_const_add, add_zero]
private theorem deriv_deriv_const_add_sum {ι : Type*} (s : Finset ι) (e : ι → ℝ → ℝ) (c : ℝ)
    (h : ∀ j ∈ s, ContDiffAt ℝ 2 (e j) 0) :
    deriv (deriv fun r => c + ∑ j ∈ s, e j r) 0 = ∑ j ∈ s, deriv (deriv (e j)) 0 := by
  have hd : ∀ j ∈ s, ∀ᶠ r in 𝓝 (0 : ℝ), DifferentiableAt ℝ (e j) r := fun j hj => by
    have h1 : ∀ᶠ r in 𝓝 (0 : ℝ), ContDiffAt ℝ 2 (e j) r := (h j hj).eventually (by simp)
    filter_upwards [h1] with r hr
    exact hr.differentiableAt (by norm_num)
  have E : deriv (fun r => c + ∑ j ∈ s, e j r) =ᶠ[𝓝 0] fun r => ∑ j ∈ s, deriv (e j) r := by
    filter_upwards [(Filter.eventually_all_finset s).2 hd] with r hr
    rw [deriv_const_add, deriv_fun_sum hr]
  rw [E.deriv_eq, deriv_fun_sum fun j hj => differentiableAt_deriv_of_contDiffAt (h j hj)]
private theorem le_torusSideBelow {L : ℕ} (hL : 1 ≤ L) : ∀ s N : ℕ, N ≤ torusSideBelow L s N
  | 0, _ => le_rfl
  | s + 1, N => (Nat.le_mul_of_pos_right N hL).trans (le_torusSideBelow hL s (N * L))
private theorem tendsto_minimizerBelow (hN : MinimizerNearTrivialField) {a ρ : ℝ} (ha : 0 < a)
    {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (h0 : 0 < ρ) (h1 : ρ ≤ 1) :
    ∀ (s k N : ℕ), 2 * L ≤ N →
    Tendsto (minimizerBelow a ρ L k s N) (𝓝 (TorusFields.trivialField N))
      (𝓝 (TorusFields.trivialField (torusSideBelow L s N)))
  | 0, _, _, _ => tendsto_id
  | s + 1, k, N, hm => by
    have h := (hN a ha L hL (k - 1) N ρ hm h0 h1).1
    have hL1 : 1 ≤ L := by have := hL.2; omega
    exact (tendsto_minimizerBelow hN ha hL h0 h1 s (k - 1) (N * L)
      (hm.trans (Nat.le_mul_of_pos_right N hL1))).comp h
private theorem zmod_cast_cast {P m : ℕ} (h : P = m) (x : ZMod P) :
    ((((x.cast : ℤ) : ZMod m)).cast : ℤ) = x.cast := by apply _root_.YangMills.Construction.FrameTorusAction.cast_intCast_cast <;> assumption
private theorem levelField_succ_edgeOfCoords {a ρ : ℝ} {L n K : ℕ}
    {V : TorusFields.TorusField (2 * L ^ n)} {X : ChainPoint L n K}
    (hR : RepresentsMinimizerChain a ρ V X) {j : ℕ} (hj : j < K)
    (x : (frameAtStep L n K j).Site (frameAtStep L n K j).top) (μ : Fin 4) :
    levelField X (j + 1) (edgeOfCoords (j + 1) (x, μ)) = SoftAverages.quaternionToMatrix
      ((topFieldAtStep a ρ L n K j V x μ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) := by
  have hper : ∀ i, (frameAtStep L n K j).period (frameAtStep L n K j).top i =
      torusSideBelow L (K - (j + 1)) (2 * L ^ n) := by
    intro i
    simp [BlockAverages.BlockFrame.period, frameAtStep, TorusFields.torusFrame, sideAtStep,
      BlockAverages.BlockFrame.top]
  have h₁ := (hR (j + 1) hj).2
    (fun i => ((BlockAverages.siteCoords x i : ℤ) :
      ZMod (torusSideBelow L (K - (j + 1)) (2 * L ^ n)))) μ
  have h₂ : levelVertexOfTorusSite (L := L) (n := n) (k := K) (j + 1)
      (fun i => ((BlockAverages.siteCoords x i : ℤ) :
        ZMod (torusSideBelow L (K - (j + 1)) (2 * L ^ n)))) =
      PeriodicLattice.offsetSite 0 (BlockAverages.siteCoords x) := by
    unfold levelVertexOfTorusSite
    congr 1
    funext i
    exact zmod_cast_cast (hper i) (x i)
  rw [h₂] at h₁
  exact h₁
private def ExcessSecondDerivAt (a ρ : ℝ) (L n K j : ℕ) (V : TorusFields.TorusField (2 * L ^ n)) :
    Prop :=
  ∀ (Z : ℝ → (frameAtStep L n K j).GaugeField (frameAtStep L n K j).depth)
    (Z' : ℝ → (frameAtStep L n K j).GaugeField (frameAtStep L n K j).top)
    (A : (frameAtStep L n K j).Site (frameAtStep L n K j).depth → Fin 4 →
      BlockAverages.imaginaryQuaternions)
    (v : (frameAtStep L n K j).Site (frameAtStep L n K j).top → Fin 4 →
      BlockAverages.imaginaryQuaternions),
    Z 0 = stepMinimizer a ρ (topFieldAtStep a ρ L n K j V) →
    Z' 0 = topFieldAtStep a ρ L n K j V →
    (∀ x i, ContDiffAt ℝ 2 (fun r => ((Z r x i : BlockAverages.UnitQuaternion) : ℍ[ℝ])) 0) →
    (∀ x i, ContDiffAt ℝ 2 (fun r => ((Z' r x i : BlockAverages.UnitQuaternion) : ℍ[ℝ])) 0) →
    (∀ x i, HasDerivAt (fun r => ((Z r x i : BlockAverages.UnitQuaternion) : ℍ[ℝ]))
      ((A x i : ℍ[ℝ]) * ((Z 0 x i : BlockAverages.UnitQuaternion) : ℍ[ℝ])) 0) →
    (∀ x i, HasDerivAt (fun r => ((Z' r x i : BlockAverages.UnitQuaternion) : ℍ[ℝ]))
      ((v x i : ℍ[ℝ]) * ((Z' 0 x i : BlockAverages.UnitQuaternion) : ℍ[ℝ])) 0) →
    ContDiffAt ℝ 2 (fun r => excessEnergy a (Z r) (Z' r)) 0 ∧
      deriv (deriv fun r => excessEnergy a (Z r) (Z' r)) 0 =
        excessHessian a (Z 0) (Z' 0) A v
end FibreHessianSum
open FibreHessianSum in
theorem fibreHessian_eq_sum_excessHessian
    (hS : SecondDerivExcessEnergyEqExcessHessian)
    (hA : ChainActionIsSumOfExcesses)
    (hN : MinimizerNearTrivialField)
    (hC : ChainLevelIsStepMinimizer)
    (hM : ChainMapsAtMinimizers)
    (hT : ExpMoveNearCompactPoint) :
    FibreHessianEqSumExcessHessians := by
  classical
  intro a ha L hL k n hn ρ h0 h1
  have hL1 : 1 ≤ L := by have := hL.2; omega
  have hL0 : 0 < L := hL1
  haveI : NeZero L := ⟨hL0.ne'⟩
  have hbase : 2 * L ≤ 2 * L ^ n := by
    have h : L ^ 1 ≤ L ^ n := Nat.pow_le_pow_right hL1 hn
    rw [pow_one] at h
    omega
  have hstep : ∀ j, j ∈ Finset.range (k + 1) →
      ∀ᶠ V in 𝓝 (TorusFields.trivialField (2 * L ^ n)), ExcessSecondDerivAt a ρ L n (k + 1) j V := by
    intro j _
    have hs : 2 * L ≤ torusSideBelow L (k + 1 - (j + 1)) (2 * L ^ n) :=
      hbase.trans (le_torusSideBelow hL1 _ _)
    exact (tendsto_minimizerBelow hN ha hL h0 h1 (k + 1 - (j + 1)) (k + 1) (2 * L ^ n)
      hbase).eventually (hS a ha L hL j _ ρ hs h0 h1)
  filter_upwards [hM a ha L hL (k + 1) n (by omega) hn,
    (Filter.eventually_all_finset (Finset.range (k + 1))).2 hstep] with V eM eS W hW X hX hR ξ
  have hmaps := eM W hW X hX
  have hXr : IsCompactValued X := hX.compact
  obtain ⟨hform, hline⟩ := hT a L hL (k + 1) n (by omega) hn X hXr
  obtain ⟨ζ, hζ⟩ : ∃ ζ : LevelForms L n (k + 1), ζ = (ξ : LevelForms L n (k + 1)) := ⟨_, rfl⟩
  obtain ⟨hP, hv⟩ := hline ζ
  have hm : tangentTransport X ζ (k + 1) = 0 := by
    have h₁ := hmaps.topDeriv_spec ζ
    rw [hζ, LinearMap.mem_ker.1 ξ.2] at h₁
    rw [hζ]
    exact h₁.symm
  have hQ : ∀ᶠ r in 𝓝 (0 : ℝ), IsCompactValued (fibreMove X (r • ζ)) := by
    filter_upwards [hP] with r hr using fibreMove_isCompactValued hXr hr
  have hQ0 : IsCompactValued (fibreMove X ((0 : ℝ) • ζ)) := hQ.self_of_nhds
  let Z : ℝ → (j : Fin (k + 1)) →
      (frameAtStep L n (k + 1) j).GaugeField (frameAtStep L n (k + 1) j).depth :=
    fun r j => levelOnFrame (fibreMove X (r • ζ)) j
  let Z' : ℝ → (j : Fin (k + 1)) →
      (frameAtStep L n (k + 1) j).GaugeField (frameAtStep L n (k + 1) j).top :=
    fun r j => levelOnFrame (fibreMove X (r • ζ)) (j + 1)
  have hZ0 : ∀ j : Fin (k + 1),
      Z 0 j = stepMinimizer a ρ (topFieldAtStep a ρ L n (k + 1) j V) := by
    intro j
    funext x μ
    show unitOfMatrix (levelField (fibreMove X ((0 : ℝ) • ζ)) j (edgeOfCoords j (x, μ))) = _
    rw [levelField_fibreMove_zero_smul hXr hP.self_of_nhds j (by omega),
      hC a ρ L hL (k + 1) n hn V X hR j j.2 (x, μ)]
    exact unitOfMatrix_toMat _
  have hZ'0 : ∀ j : Fin (k + 1), Z' 0 j = topFieldAtStep a ρ L n (k + 1) j V := by
    intro j
    funext x μ
    show unitOfMatrix (levelField (fibreMove X ((0 : ℝ) • ζ)) (j + 1)
      (edgeOfCoords (j + 1) (x, μ))) = _
    rw [levelField_fibreMove_zero_smul hXr hP.self_of_nhds (j + 1) (by omega),
      levelField_succ_edgeOfCoords hR j.2 x μ]
    exact unitOfMatrix_toMat _
  have hj : ∀ j : Fin (k + 1),
      ContDiffAt ℝ 2 (fun r => excessEnergy a (Z r j) (Z' r j)) 0 ∧
      deriv (deriv fun r => excessEnergy a (Z r j) (Z' r j)) 0 =
        excessHessian a (stepMinimizer a ρ (topFieldAtStep a ρ L n (k + 1) j V))
          (topFieldAtStep a ρ L n (k + 1) j V)
          (frameVelocityOfForm j (tangentTransport X ζ j))
          (frameVelocityOfForm (j + 1) (tangentTransport X ζ (j + 1))) := by
    intro j
    have h := eS j (Finset.mem_range.2 j.2) (fun r => Z r j) (fun r => Z' r j)
      (frameVelocityOfForm j (tangentTransport X ζ j))
      (frameVelocityOfForm (j + 1) (tangentTransport X ζ (j + 1))) (hZ0 j) (hZ'0 j)
      (fun x i => contDiffAt_levelOnFrame hXr hP (by omega) x i)
      (fun x i => contDiffAt_levelOnFrame hXr hP (by omega) x i)
      (fun x i => hasDerivAt_levelOnFrame hXr hP hv hm (by omega) x i)
      (fun x i => hasDerivAt_levelOnFrame hXr hP hv hm (by omega) x i)
    have e₁ : excessHessian a (Z 0 j) (Z' 0 j) (frameVelocityOfForm j (tangentTransport X ζ j))
        (frameVelocityOfForm (j + 1) (tangentTransport X ζ (j + 1))) =
        excessHessian a (stepMinimizer a ρ (topFieldAtStep a ρ L n (k + 1) j V))
          (topFieldAtStep a ρ L n (k + 1) j V)
          (frameVelocityOfForm j (tangentTransport X ζ j))
          (frameVelocityOfForm (j + 1) (tangentTransport X ζ (j + 1))) := by
      rw [hZ0 j, hZ'0 j]
    exact ⟨h.1, h.2.trans e₁⟩
  have hsum : (fun r : ℝ => chainAction a (fibreMove X (r • ζ))) =ᶠ[𝓝 0] fun r =>
      BlockAverages.minimalAction a
        (ColdStepAtMirrorFrames.finiteCells (frameAtStep L n (k + 1) (Fin.last k)))
        (frameAtStep L n (k + 1) (Fin.last k)).top (Z' 0 (Fin.last k)) +
      ∑ j : Fin (k + 1), (fun j r => excessEnergy a (Z r j) (Z' r j)) j r := by
    filter_upwards [hQ, hP] with r hr hpr
    have h := hA a ha L hL k n hn (fibreMove X (r • ζ)) hr (Z r) (Z' r)
      (fun j b => levelField_edgeOfCoords hr (by omega) b)
      (fun j b => levelField_edgeOfCoords hr (by omega) b)
    have e : Z' r (Fin.last k) = Z' 0 (Fin.last k) := by
      funext x μ
      have e₂ : levelField (fibreMove X (r • ζ)) (((Fin.last k : Fin (k + 1)) : ℕ) + 1) =
          levelField (fibreMove X ((0 : ℝ) • ζ)) (((Fin.last k : Fin (k + 1)) : ℕ) + 1) :=
        (levelField_fibreMove_top X _ hpr).trans
          (levelField_fibreMove_top X _ hP.self_of_nhds).symm
      show unitOfMatrix (levelField (fibreMove X (r • ζ))
          (((Fin.last k : Fin (k + 1)) : ℕ) + 1) _) =
        unitOfMatrix (levelField (fibreMove X ((0 : ℝ) • ζ))
          (((Fin.last k : Fin (k + 1)) : ℕ) + 1) _)
      rw [e₂]
    rw [h, e]
  have e₁ : fibreSecondDeriv a X ζ ζ =
      deriv (deriv fun r : ℝ => chainAction a (fibreMove X (r • ζ))) 0 := by
    have e₃ : (fun s : ℝ =>
        deriv (fun t : ℝ => chainAction a (fibreMove X (s • ζ + t • ζ))) 0) =
        deriv fun r : ℝ => chainAction a (fibreMove X (r • ζ)) := by
      funext s
      have e₂ : (fun t : ℝ => chainAction a (fibreMove X (s • ζ + t • ζ))) =
          fun t => (fun r : ℝ => chainAction a (fibreMove X (r • ζ))) (s + t) := by
        funext t
        simp only [add_smul]
      rw [e₂]
      exact deriv_comp_add_zero (fun r : ℝ => chainAction a (fibreMove X (r • ζ))) s
    unfold fibreSecondDeriv
    rw [e₃]
  have hfin : fibreHessian a X ξ = fibreSecondDeriv a X ζ ζ := by
    rw [hζ]
    exact hform ξ
  have e₄ := deriv_deriv_const_add_sum Finset.univ
    (fun (j : Fin (k + 1)) r => excessEnergy a (Z r j) (Z' r j))
    (BlockAverages.minimalAction a
      (ColdStepAtMirrorFrames.finiteCells (frameAtStep L n (k + 1) (Fin.last k)))
      (frameAtStep L n (k + 1) (Fin.last k)).top (Z' 0 (Fin.last k))) fun j _ => (hj j).1
  rw [hfin, e₁, (Filter.EventuallyEq.deriv hsum).deriv_eq, ← hζ]
  exact e₄.trans (Finset.sum_congr rfl fun j _ => (hj j).2)
end YangMills.Construction.RunningCouplingSlope
end
