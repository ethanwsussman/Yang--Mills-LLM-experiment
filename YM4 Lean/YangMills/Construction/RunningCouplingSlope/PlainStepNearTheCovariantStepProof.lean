import YangMills.Construction.ColdChainAtEveryLevel.ComplexContours
import YangMills.Construction.Lattice.GaugeCovarianceOfHolonomyProof
import YangMills.Construction.Towers.GaugeTransformationsInTheLeftChartProof
import YangMills.Construction.RunningCouplingSlope.DerivativeOfThePlainAverageAtOne
import YangMills.Construction.RunningCouplingSlope.PlainAverageAlongComplexCurves
import YangMills.Construction.RunningCouplingSlope.PlainAverageNearOne
import YangMills.Construction.RunningCouplingSlope.PlainAverageReadsTheDoubleBlock
import YangMills.Construction.RunningCouplingSlope.PlainDifferentialAtOneOnComplexForms
import YangMills.Construction.RunningCouplingSlope.PlainStepNearTheCovariantStep
import YangMills.Construction.Towers.CovariantAveragesAsDifferentialsProof
import YangMills.Construction.Towers.StepsAtTheTrivialConfigurationOfTheScaledPictureOnASide
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open Set Filter Metric
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.MeanStepNearCovariantDeriv
open Tower Matrices
open Tower.LeftChartFields (CurveLogDerivative)
section MatrixFacts
private theorem norm_mul_sub_one_le_mul (X Y : ComplexMatrix2) :
    ‖X * Y - 1‖ ≤ (1 + ‖X - 1‖) * (1 + ‖Y - 1‖) - 1 := by apply _root_.YangMills.Construction.ComplexContours.norm_mul_sub_one_le_complexQuat <;> assumption
abbrev _root_.YangMills.SharedProofs.p30838 := @norm_mul_sub_one_le_mul
private theorem expI_mul_mem_unitDet (hEL : ComplexMatrix2.ExpLogEstimates)
    {X g : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (hg : g ∈ ComplexMatrix2.unitDeterminant) :
    ComplexMatrix2.matExp (Complex.I • X) * g ∈ ComplexMatrix2.unitDeterminant := by apply _root_.YangMills.Construction.Tower.AsDifferentials.expChart_mem_unitDeterminant <;> assumption
private theorem inv_mem_unitDet {g : ComplexMatrix2} (hg : g ∈ ComplexMatrix2.unitDeterminant) :
    g⁻¹ ∈ ComplexMatrix2.unitDeterminant := by apply _root_.YangMills.SharedProofs.p413 <;> assumption
private theorem inv_inv_of_unitDet {g : ComplexMatrix2}
    (hg : g ∈ ComplexMatrix2.unitDeterminant) : (g⁻¹)⁻¹ = g := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.inv_inv_of_mem_unitDeterminant <;> assumption
private theorem mul_inv_of_unitDet {g : ComplexMatrix2}
    (hg : g ∈ ComplexMatrix2.unitDeterminant) : g * g⁻¹ = 1 := by apply _root_.YangMills.DeltaSharedProofs.p2618 <;> assumption
private theorem inv_mul_of_unitDet {g : ComplexMatrix2}
    (hg : g ∈ ComplexMatrix2.unitDeterminant) : g⁻¹ * g = 1 := by apply _root_.YangMills.DeltaSharedProofs.p40097 <;> assumption
private theorem mul_mem_unitDet {g h : ComplexMatrix2} (hg : g ∈ ComplexMatrix2.unitDeterminant)
    (hh : h ∈ ComplexMatrix2.unitDeterminant) : g * h ∈ ComplexMatrix2.unitDeterminant := by apply _root_.YangMills.SharedProofs.p36859 <;> assumption
private theorem norm_le_of_near_one (hEL : ComplexMatrix2.ExpLogEstimates) {g : ComplexMatrix2}
    (hg : ‖g - 1‖ < 1 / 2) : ‖g‖ ≤ 3 / 2 ∧ ‖g⁻¹‖ ≤ 2 := by
  have h := hEL.2.2.2.1 (g - 1) (by show ‖g - 1‖ < 1; linarith)
  have e : 1 + (g - 1) = g := by abel
  rw [e] at h
  obtain ⟨-, -, hu, hi, -⟩ := h
  have h1 : ‖(1 : ComplexMatrix2)‖ = 1 := norm_one
  refine ⟨?_, ?_⟩
  · have : g = (g - 1) + 1 := by abel
    calc ‖g‖ = ‖(g - 1) + 1‖ := by rw [← this]
      _ ≤ ‖g - 1‖ + ‖(1 : ComplexMatrix2)‖ := norm_add_le _ _
      _ ≤ 3 / 2 := by rw [h1]; linarith
  · have hi' : ‖g⁻¹ - 1‖ ≤ ‖g - 1‖ / (1 - ‖g - 1‖) := hi
    have hb : ‖g - 1‖ / (1 - ‖g - 1‖) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    have : g⁻¹ = (g⁻¹ - 1) + 1 := by abel
    calc ‖g⁻¹‖ = ‖(g⁻¹ - 1) + 1‖ := by rw [← this]
      _ ≤ ‖g⁻¹ - 1‖ + ‖(1 : ComplexMatrix2)‖ := norm_add_le _ _
      _ ≤ 2 := by rw [h1]; linarith
private theorem norm_conjugateBy_le {g : ComplexMatrix2} (h₁ : ‖g‖ ≤ 3 / 2) (h₂ : ‖g⁻¹‖ ≤ 2)
    (X : ComplexMatrix2) : ‖ComplexMatrix2.conjugateBy g X‖ ≤ 3 * ‖X‖ := by
  calc ‖ComplexMatrix2.conjugateBy g X‖ = ‖g * X * g⁻¹‖ := rfl
    _ ≤ ‖g * X‖ * ‖g⁻¹‖ := norm_mul_le _ _
    _ ≤ (‖g‖ * ‖X‖) * ‖g⁻¹‖ := by gcongr; exact norm_mul_le _ _
    _ ≤ (3 / 2 * ‖X‖) * 2 := by gcongr
    _ = 3 * ‖X‖ := by ring
abbrev _root_.YangMills.SharedProofs.p70374 := @norm_conjugateBy_le
private theorem norm_matExp_sub_one_le (hEL : ComplexMatrix2.ExpLogEstimates)
    {Z : ComplexMatrix2} (hZ : ‖Z‖ ≤ 1) : ‖ComplexMatrix2.matExp Z - 1‖ ≤ 2 * ‖Z‖ := by
  have h := (hEL.1 Z).2
  have h' : ‖ComplexMatrix2.matExp Z - 1‖ ≤ Real.exp ‖Z‖ - 1 := h
  have h₂ := Real.abs_exp_sub_one_le (x := ‖Z‖) (by rwa [abs_of_nonneg (norm_nonneg Z)])
  rw [abs_of_nonneg (norm_nonneg Z)] at h₂
  exact h'.trans ((le_abs_self _).trans h₂)
abbrev _root_.YangMills.SharedProofs.p10567 := @norm_matExp_sub_one_le
private theorem norm_conjugateBy_sub_le {g : ComplexMatrix2}
    (hg : g ∈ ComplexMatrix2.unitDeterminant) (Z : ComplexMatrix2) :
    ‖ComplexMatrix2.conjugateBy g Z - Z‖ ≤ 2 * ‖g - 1‖ * ‖Z‖ * ‖g⁻¹‖ := by
  have e : ComplexMatrix2.conjugateBy g Z - Z = ((g - 1) * Z - Z * (g - 1)) * g⁻¹ := by
    have h₁ : Z = Z * g * g⁻¹ := by rw [mul_assoc, mul_inv_of_unitDet hg, mul_one]
    calc ComplexMatrix2.conjugateBy g Z - Z = g * Z * g⁻¹ - Z * g * g⁻¹ := by rw [← h₁]; rfl
      _ = _ := by noncomm_ring
  rw [e]
  have h₂ : ‖(g - 1) * Z - Z * (g - 1)‖ ≤ 2 * ‖g - 1‖ * ‖Z‖ := by
    have a := norm_mul_le (g - 1) Z
    have b := norm_mul_le Z (g - 1)
    have c := norm_sub_le ((g - 1) * Z) (Z * (g - 1))
    nlinarith
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right h₂ (norm_nonneg _))
private theorem differentiableAt_inv_of_unitDet {f : ℂ → ComplexMatrix2} {t : ℂ}
    (hf : DifferentiableAt ℂ f t)
    (hu : ∀ᶠ s in 𝓝 t, f s ∈ ComplexMatrix2.unitDeterminant) :
    DifferentiableAt ℂ (fun s => (f s)⁻¹) t := by
  have hadj : DifferentiableAt ℂ (fun s => Matrix.adjugate (f s)) t := by
    let A : ComplexMatrix2 →ₗ[ℂ] ComplexMatrix2 :=
      { toFun := fun X => Matrix.adjugate X
        map_add' := fun X Y => by
          ext a b
          fin_cases a <;> fin_cases b <;> simp [Matrix.adjugate_fin_two] <;> ring
        map_smul' := fun z X => by
          ext a b
          fin_cases a <;> fin_cases b <;> simp [Matrix.adjugate_fin_two] }
    exact (LinearMap.toContinuousLinearMap A).differentiableAt.comp t hf
  refine hadj.congr_of_eventuallyEq ?_
  filter_upwards [hu] with s hs
  have hs' : (f s).det = 1 := hs
  rw [Matrix.inv_def, hs']
  simp
private theorem norm_one_le_of_vanishing_order_two {f : ℂ → ComplexMatrix2} {R M : ℝ}
    (hR : 4 ≤ R) (hd : DifferentiableOn ℂ f (ball 0 R)) (hb : ∀ z ∈ ball (0 : ℂ) R, ‖f z‖ ≤ M)
    (h0 : f 0 = 0) (h1 : deriv f 0 = 0) : ‖f 1‖ ≤ 4 * M / R ^ 2 := by
  have hR0 : 0 < R := by linarith
  have hM : 0 ≤ M := (norm_nonneg _).trans (hb 0 (mem_ball_self hR0))
  have hd' : DifferentiableOn ℂ (deriv f) (ball 0 R) := hd.deriv isOpen_ball
  have hc : ∀ z ∈ ball (0 : ℂ) (R / 2), ‖deriv f z‖ ≤ M / (R / 2) := by
    intro z hz
    have hz' : ‖z‖ < R / 2 := by simpa using hz
    have hsub : closedBall z (R / 2) ⊆ ball (0 : ℂ) R := by
      intro w hw
      have hw' : ‖w - z‖ ≤ R / 2 := by simpa [dist_eq_norm] using hw
      have : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
        have := norm_add_le (w - z) z
        simpa using this
      simp only [mem_ball, dist_zero_right]
      linarith
    have hcl : DiffContOnCl ℂ f (ball z (R / 2)) :=
      (hd.mono hsub).diffContOnCl_ball subset_rfl
    exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by linarith) hcl
      fun w hw => hb w (hsub (sphere_subset_closedBall hw))
  have hmaps : MapsTo (deriv f) (ball 0 (R / 2)) (closedBall (deriv f 0) (M / (R / 2))) := by
    intro z hz
    rw [h1, mem_closedBall, dist_zero_right]
    exact hc z hz
  have hsch : ∀ z ∈ ball (0 : ℂ) (R / 2), ‖deriv f z‖ ≤ M / (R / 2) / (R / 2) * ‖z‖ := by
    intro z hz
    have h := Complex.dist_le_div_mul_dist_of_mapsTo_ball
      (hd'.mono (ball_subset_ball (by linarith))) hmaps hz
    simpa [h1, dist_eq_norm] using h
  have hsub₁ : closedBall (0 : ℂ) 1 ⊆ ball 0 (R / 2) := closedBall_subset_ball (by linarith)
  have hb₁ : ∀ z ∈ closedBall (0 : ℂ) 1, ‖deriv f z‖ ≤ 4 * M / R ^ 2 := by
    intro z hz
    have hz' : ‖z‖ ≤ 1 := by simpa using hz
    refine (hsch z (hsub₁ hz)).trans ?_
    have e : M / (R / 2) / (R / 2) = 4 * M / R ^ 2 := by field_simp; ring
    rw [e]
    exact mul_le_of_le_one_right (by positivity) hz'
  have hdiff : ∀ z ∈ closedBall (0 : ℂ) 1, DifferentiableAt ℂ f z := fun z hz =>
    hd.differentiableAt (isOpen_ball.mem_nhds
      ((ball_subset_ball (by linarith)) (hsub₁ hz)))
  have hmv := (convex_closedBall (0 : ℂ) 1).norm_image_sub_le_of_norm_deriv_le hdiff hb₁
    (mem_closedBall_self zero_le_one) (by simp : (1 : ℂ) ∈ closedBall (0 : ℂ) 1)
  simpa [h0] using hmv
end MatrixFacts
section Lines
variable {L n k j : ℕ} {c : Edge L n k (j + 1)}
private abbrev cubeEdges (c : Edge L n k (j + 1)) : Set (Edge L n k j) :=
  DoubleBlockPolydisc.doubleBlockBonds c
private structure EdgeData (c : Edge L n k (j + 1)) : Prop where
  expLog : ComplexMatrix2.ExpLogEstimates
  logDeriv : ∀ r : ℝ, 0 < r →
    CurveLogDerivative ℂ (Metric.ball 0 r) PeriodicLattice.complexGaugeGroup
      PeriodicLattice.complexLieAlgebra
  xor_orient : ∀ b : Edge L n k j,
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented
  opposite_opposite : ∀ b : Edge L n k j, b.opposite.opposite = b
  finite : (cubeEdges c).Finite
  opposite_mem : ∀ b ∈ cubeEdges c, b.opposite ∈ cubeEdges c
private theorem EdgeData.opposite_pos (F : EdgeData c) {b : Edge L n k j}
    (hb : ¬ b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by
  rcases F.xor_orient b with h | h
  exacts [absurd h.1 hb, h.1]
private theorem EdgeData.not_opposite_pos (F : EdgeData c) {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by
  rcases F.xor_orient b with h | h
  exacts [h.2, absurd hb h.2]
private theorem expTwist_of_pos {A U : Edge L n k j → ComplexMatrix2} {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) :
    PeriodicLattice.expTwist A U b = ComplexMatrix2.matExp (Complex.I • A b) * U b := by apply _root_.YangMills.Construction.Tower.LeftChartGauge.expTwist_of_positive <;> assumption
private theorem expTwist_of_not_pos {A U : Edge L n k j → ComplexMatrix2} {b : Edge L n k j}
    (hb : ¬ b.IsPositivelyOriented) :
    PeriodicLattice.expTwist A U b =
      (ComplexMatrix2.matExp (Complex.I • A b.opposite) * U b.opposite)⁻¹ := by apply _root_.YangMills.Construction.Tower.LeftChartGauge.expTwist_of_not_positive <;> assumption
private theorem EdgeData.expTwist_mem (F : EdgeData c) {V C : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (hC : C ∈ complexEdgeForms L n k j) :
    PeriodicLattice.expTwist C V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup := by
  have hval : ∀ b : Edge L n k j, b.IsPositivelyOriented →
      ComplexMatrix2.matExp (Complex.I • C b) * V b ∈ ComplexMatrix2.unitDeterminant :=
    fun b hb => expI_mul_mem_unitDet F.expLog (hC.1 b hb) (hV.1 b (mem_univ b))
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · rw [expTwist_of_pos hb]
      exact hval b hb
    · rw [expTwist_of_not_pos hb]
      exact inv_mem_unitDet (hval _ (F.opposite_pos hb))
  · by_cases hb : b.IsPositivelyOriented
    · have hr := F.not_opposite_pos hb
      rw [expTwist_of_not_pos hr, expTwist_of_pos hb, F.opposite_opposite b]
    · have hr := F.opposite_pos hb
      rw [expTwist_of_pos hr, expTwist_of_not_pos hb]
      exact (inv_inv_of_unitDet (hval _ hr)).symm
private theorem EdgeData.expTwist_zero (F : EdgeData c) {V B : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup) :
    PeriodicLattice.expTwist ((0 : ℂ) • B) V = V := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · rw [expTwist_of_pos hb]
    simp [ComplexMatrix2.matExp]
  · rw [expTwist_of_not_pos hb]
    have h₁ := hV.2 b.opposite (mem_univ _)
    rw [F.opposite_opposite b] at h₁
    simp only [Pi.smul_apply, zero_smul, smul_zero, ComplexMatrix2.matExp, NormedSpace.exp_zero,
      one_mul]
    exact h₁.symm
private theorem I_smul_smul_apply (t : ℂ) (B : Edge L n k j → ComplexMatrix2) (b : Edge L n k j) :
    Complex.I • (t • B) b = t • (Complex.I • B b) := by
  simp only [Pi.smul_apply]
  exact smul_comm _ _ _
private theorem EdgeData.differentiableAt_expTwist (F : EdgeData c)
    {V B : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (hB : B ∈ complexEdgeForms L n k j) (b : Edge L n k j) (t₀ : ℂ) :
    DifferentiableAt ℂ (fun t : ℂ => PeriodicLattice.expTwist (t • B) V b) t₀ := by
  have hpos : ∀ b' : Edge L n k j, ∀ t₀ : ℂ,
      DifferentiableAt ℂ
        (fun t : ℂ => ComplexMatrix2.matExp (Complex.I • (t • B) b') * V b') t₀ := by
    intro b' t₀
    simp only [I_smul_smul_apply]
    exact ((hasDerivAt_exp_smul_const (𝕂 := ℂ) (Complex.I • B b') t₀).mul_const
      (V b')).differentiableAt
  by_cases hb : b.IsPositivelyOriented
  · simp only [expTwist_of_pos hb]
    exact hpos b t₀
  · simp only [expTwist_of_not_pos hb]
    have hr := F.opposite_pos hb
    refine differentiableAt_inv_of_unitDet (hpos _ t₀) (Eventually.of_forall fun t => ?_)
    exact expI_mul_mem_unitDet F.expLog (((complexEdgeForms L n k j).smul_mem t hB).1 _ hr)
      (hV.1 _ (mem_univ _))
private theorem EdgeData.norm_expTwist_sub_one_le (F : EdgeData c)
    {V B : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup) {a s : ℝ} {t : ℂ}
    (ha : a ≤ 1) (hs : ∀ b ∈ cubeEdges c, ‖V b - 1‖ ≤ s)
    (ht : ∀ b ∈ cubeEdges c, ‖t‖ * ‖B b‖ ≤ a) {b : Edge L n k j} (hb : b ∈ cubeEdges c) :
    ‖PeriodicLattice.expTwist (t • B) V b - 1‖ ≤ (1 + 2 * a) * (1 + s) - 1 := by
  have hnZ : ∀ b' ∈ cubeEdges c, ‖Complex.I • (t • B) b'‖ ≤ a := fun b' hb' => by
    have : ‖Complex.I • (t • B) b'‖ = ‖t‖ * ‖B b'‖ := by
      simp [norm_smul]
    rw [this]
    exact ht b' hb'
  have hexp : ∀ Z : ComplexMatrix2, ‖Z‖ ≤ a → ‖ComplexMatrix2.matExp Z - 1‖ ≤ 2 * a :=
    fun Z hZ => by
      have := norm_matExp_sub_one_le F.expLog (Z := Z) (hZ.trans ha)
      linarith
  have hs0 : 0 ≤ s := (norm_nonneg _).trans (hs b hb)
  have ha0 : 0 ≤ a := (mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans (ht b hb)
  by_cases hp : b.IsPositivelyOriented
  · rw [expTwist_of_pos hp]
    refine (norm_mul_sub_one_le_mul _ _).trans ?_
    have h₁ := hexp _ (hnZ b hb)
    have h₂ := hs b hb
    have : (1 + ‖ComplexMatrix2.matExp (Complex.I • (t • B) b) - 1‖) * (1 + ‖V b - 1‖) ≤
        (1 + 2 * a) * (1 + s) :=
      mul_le_mul (by linarith) (by linarith) (by linarith [norm_nonneg (V b - 1)]) (by linarith)
    linarith
  · rw [expTwist_of_not_pos hp, Matrix.mul_inv_rev]
    have h₁ := hV.2 b.opposite (mem_univ _)
    rw [F.opposite_opposite b] at h₁
    rw [← h₁, ← Matrix.exp_neg]
    refine (norm_mul_sub_one_le_mul _ _).trans ?_
    have h₂ : ‖ComplexMatrix2.matExp (-(Complex.I • (t • B) b.opposite)) - 1‖ ≤ 2 * a :=
      hexp _ (by rw [norm_neg]; exact hnZ _ (F.opposite_mem b hb))
    have h₃ := hs b hb
    have : (1 + ‖V b - 1‖) *
        (1 + ‖ComplexMatrix2.matExp (-(Complex.I • (t • B) b.opposite)) - 1‖) ≤
        (1 + s) * (1 + 2 * a) :=
      mul_le_mul (by linarith) (by linarith) (by positivity) (by linarith)
    linarith
private structure Admissible (ρ : ℝ) (c : Edge L n k (j + 1))
    (Φ : (Edge L n k j → ComplexMatrix2) → ComplexMatrix2) : Prop where
  local_eq : ∀ W ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
    (∀ b ∈ cubeEdges c, ‖W b - 1‖ < ρ) → ∀ W' : Edge L n k j → ComplexMatrix2,
      (∀ b ∈ cubeEdges c, W' b = W b) → Φ W' = Φ W
  near_one : ∀ W ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
    (∀ b ∈ cubeEdges c, ‖W b - 1‖ < ρ) → ‖Φ W - 1‖ < 1 / 2
  mem_unitDet : ∀ W ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
    (∀ b ∈ cubeEdges c, ‖W b - 1‖ < ρ) → Φ W ∈ ComplexMatrix2.unitDeterminant
  differentiableAt_line : ∀ V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
    ∀ B ∈ complexEdgeForms L n k j,
    ∀ t₀ : ℂ, (∀ b ∈ cubeEdges c, ‖PeriodicLattice.expTwist (t₀ • B) V b - 1‖ < ρ) →
      DifferentiableAt ℂ (fun t : ℂ => Φ (PeriodicLattice.expTwist (t • B) V)) t₀
private def lineValues (c : Edge L n k (j + 1)) (V B : Edge L n k j → ComplexMatrix2) (t : ℂ) :
    PeriodicLattice.PositiveBondOf (cubeEdges c) → ComplexMatrix2 :=
  PeriodicLattice.restrictToPositive _ (PeriodicLattice.expTwist (t • B) V)
private theorem EdgeData.extend_restrict_eq (F : EdgeData c) {W : Edge L n k j → ComplexMatrix2}
    (hW : W ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup) :
    ∀ b ∈ cubeEdges c,
      PeriodicLattice.extendFromPositive (cubeEdges c)
        (PeriodicLattice.restrictToPositive _ W) b = W b := by
  classical
  intro b hb
  by_cases hp : b.IsPositivelyOriented
  · simp [PeriodicLattice.extendFromPositive, PeriodicLattice.restrictToPositive, hb, hp]
  · have hr := F.opposite_pos hp
    have h₁ := hW.2 b.opposite (mem_univ _)
    rw [F.opposite_opposite b] at h₁
    have hrb := F.opposite_mem b hb
    simp [PeriodicLattice.extendFromPositive, PeriodicLattice.restrictToPositive, hb, hp, hr,
      hrb, h₁]
private theorem EdgeData.differentiableAt_of_holomorphic (F : EdgeData c) {ρ : ℝ}
    {V B : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    {Φ : (Edge L n k j → ComplexMatrix2) → ComplexMatrix2}
    (hΦ : PeriodicLattice.IsHolomorphicOnFields
      (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)) (nearIdentityPolydisc ρ c) Φ)
    (hB : B ∈ complexEdgeForms L n k j) {t₀ : ℂ}
    (ht₀ : PeriodicLattice.expTwist (t₀ • B) V ∈ nearIdentityPolydisc ρ c) :
    DifferentiableAt ℂ (fun t => Φ (PeriodicLattice.extendFromPositive
        (cubeEdges c) (lineValues c V B t))) t₀ ∧
      Φ (PeriodicLattice.extendFromPositive (cubeEdges c) (lineValues c V B t₀)) ∈
        PeriodicLattice.complexGaugeGroup := by
  obtain ⟨⟨inst, ⟨O', hO', hD⟩, hmaps, hloc⟩, -⟩ := hΦ
  have hx : lineValues c V B t₀ ∈
      PeriodicLattice.restrictToPositive (cubeEdges c) '' nearIdentityPolydisc ρ c :=
    ⟨_, ht₀, rfl⟩
  have hxO : lineValues c V B t₀ ∈ O' := by
    have h := hx
    rw [hD] at h
    exact h.1
  have hprod : ∀ t, lineValues c V B t ∈
      ComplexMatrix2.complexifiedProduct fun _ : PeriodicLattice.PositiveBondOf (cubeEdges c) =>
        ComplexMatrix2.FactorKind.group := fun t b =>
    (F.expTwist_mem hV ((complexEdgeForms L n k j).smul_mem t hB)).1 b.1 (mem_univ _)
  have hv : DifferentiableAt ℂ (lineValues c V B) t₀ :=
    differentiableAt_pi.2 fun b => F.differentiableAt_expTwist hV hB b.1 t₀
  have hmem : ∀ᶠ t in 𝓝 t₀, lineValues c V B t ∈
      PeriodicLattice.restrictToPositive (cubeEdges c) '' nearIdentityPolydisc ρ c := by
    filter_upwards [hv.continuousAt.eventually (hO'.mem_nhds hxO)] with t ht
    rw [hD]
    exact ⟨ht, hprod t⟩
  obtain ⟨G, hG, hev⟩ := hloc _ hx
  have h2 := (tendsto_nhdsWithin_iff.2 ⟨hv.continuousAt, hmem⟩).eventually hev
  have h3 : DifferentiableAt ℂ (fun t => G (lineValues c V B t)) t₀ :=
    hG.differentiableAt.comp t₀ hv
  have h4 : DifferentiableAt ℂ (fun t => G (lineValues c V B t) ()) t₀ :=
    differentiableAt_pi.1 h3 ()
  refine ⟨h4.congr_of_eventuallyEq ?_, hmaps hx ()⟩
  filter_upwards [h2] with t ht
  exact congrFun ht ()
private theorem mem_polydisc_of_close {ρ : ℝ} {W : Edge L n k j → ComplexMatrix2}
    (hW : W ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (h : ∀ b ∈ cubeEdges c, ‖W b - 1‖ < ρ) : W ∈ nearIdentityPolydisc ρ c :=
  ⟨⟨fun b _ => hW.1 b (mem_univ b), fun b _ => hW.2 b (mem_univ b)⟩, h⟩
private theorem EdgeData.eventually_close (F : EdgeData c) {ρ : ℝ}
    {V B : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (hB : B ∈ complexEdgeForms L n k j) {t₀ : ℂ}
    (h : ∀ b ∈ cubeEdges c, ‖PeriodicLattice.expTwist (t₀ • B) V b - 1‖ < ρ) :
    ∀ᶠ t : ℂ in 𝓝 t₀, ∀ b ∈ cubeEdges c, ‖PeriodicLattice.expTwist (t • B) V b - 1‖ < ρ := by
  refine (Filter.eventually_all_finite F.finite).2 fun b hb => ?_
  have hc : ContinuousAt (fun t : ℂ => ‖PeriodicLattice.expTwist (t • B) V b - 1‖) t₀ :=
    ((F.differentiableAt_expTwist hV hB b t₀).continuousAt.sub continuousAt_const).norm
  exact hc.eventually_lt continuousAt_const (h b hb)
private theorem EdgeData.admissible_of_holomorphic (F : EdgeData c) {ρ ρ' : ℝ} (hρ : ρ ≤ ρ')
    {Φ : (Edge L n k j → ComplexMatrix2) → ComplexMatrix2}
    (hΦ : PeriodicLattice.IsHolomorphicOnFields
      (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)) (nearIdentityPolydisc ρ' c) Φ)
    (hsmall : ∀ W ∈ nearIdentityPolydisc ρ' c, ‖Φ W - 1‖ < 1 / 2)
    (hread : ∀ W ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
      W ∈ nearIdentityPolydisc ρ' c →
      ∀ W' : Edge L n k j → ComplexMatrix2, (∀ b ∈ cubeEdges c, W' b = W b) → Φ W' = Φ W) :
    Admissible ρ c Φ := by
  have hmem : ∀ W ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
      (∀ b ∈ cubeEdges c, ‖W b - 1‖ < ρ) → W ∈ nearIdentityPolydisc ρ' c := fun W hW h =>
    mem_polydisc_of_close hW fun b hb => (h b hb).trans_le hρ
  refine ⟨fun W hW h W' he => hread W hW (hmem W hW h) W' he,
    fun W hW h => hsmall W (hmem W hW h), fun W hW h => ?_, fun V hV B hB t₀ h => ?_⟩
  · have hp : PeriodicLattice.expTwist ((0 : ℂ) • (0 : Edge L n k j → ComplexMatrix2)) W ∈
        nearIdentityPolydisc ρ' c := by
      rw [F.expTwist_zero hW]
      exact hmem W hW h
    have h₁ :=
      (F.differentiableAt_of_holomorphic hW hΦ (complexEdgeForms L n k j).zero_mem hp).2
    have e : lineValues c W (0 : Edge L n k j → ComplexMatrix2) 0 =
        PeriodicLattice.restrictToPositive _ W := by
      simp only [lineValues]
      rw [F.expTwist_zero hW]
    rw [e, hread W hW (hmem W hW h) _ (F.extend_restrict_eq hW)] at h₁
    exact h₁
  · have ht₀ := hmem _ (F.expTwist_mem hV ((complexEdgeForms L n k j).smul_mem t₀ hB)) h
    refine (F.differentiableAt_of_holomorphic hV hΦ hB ht₀).1.congr_of_eventuallyEq ?_
    filter_upwards [F.eventually_close hV hB h] with t ht
    have hW := F.expTwist_mem hV ((complexEdgeForms L n k j).smul_mem t hB)
    exact (hread _ hW (hmem _ hW ht) _ (F.extend_restrict_eq hW)).symm
private theorem EdgeData.admissible_normalizedMean (F : EdgeData c) {ρ : ℝ} (hρ : 0 < ρ)
    (hR : ∀ W W' : Edge L n k j → ComplexMatrix2, (∀ b ∈ cubeEdges c, W b = W' b) →
      normalizedMean W c = normalizedMean W' c)
    (hN : ∀ V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
      (∀ b, ComplexMatrix2.operatorNorm (V b - 1) < ρ) →
        ComplexMatrix2.operatorNorm (normalizedMean V c - 1) < 1 / 2 ∧
          normalizedMean V c ∈ PeriodicLattice.complexGaugeGroup)
    (hA : ∀ V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
      (∀ b, ComplexMatrix2.operatorNorm (V b - 1) < ρ) →
        ∃ D : (Edge L n k j → ComplexMatrix2) →ₗ[ℂ] ComplexMatrix2,
        ∀ (g : Edge L n k j → ComplexMatrix2) (γ : ℂ → Edge L n k j → ComplexMatrix2), γ 0 = V →
          (∀ b, HasDerivAt (fun t => γ t b) (g b) 0) →
            HasDerivAt (fun t => normalizedMean (γ t) c) (D g) 0) :
    Admissible ρ c fun W => normalizedMean W c := by
  classical
  let cut : (Edge L n k j → ComplexMatrix2) → Edge L n k j → ComplexMatrix2 :=
    fun W b => if b ∈ cubeEdges c then W b else 1
  have hcut_eq : ∀ W : Edge L n k j → ComplexMatrix2, ∀ b ∈ cubeEdges c, cut W b = W b :=
    fun W b hb => if_pos hb
  have hcut_out : ∀ W : Edge L n k j → ComplexMatrix2, ∀ b, b ∉ cubeEdges c → cut W b = 1 :=
    fun W b hb => if_neg hb
  have hrev : ∀ b, b ∉ cubeEdges c → b.opposite ∉ cubeEdges c := fun b hb h => by
    have := F.opposite_mem _ h
    rw [F.opposite_opposite b] at this
    exact hb this
  have hcut_mem : ∀ W ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
      cut W ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup := by
    intro W hW
    refine ⟨fun b _ => ?_, fun b _ => ?_⟩
    · by_cases hb : b ∈ cubeEdges c
      · rw [hcut_eq W b hb]
        exact hW.1 b (mem_univ b)
      · rw [hcut_out W b hb]
        exact Matrix.det_one
    · by_cases hb : b ∈ cubeEdges c
      · rw [hcut_eq W b hb, hcut_eq W _ (F.opposite_mem b hb)]
        exact hW.2 b (mem_univ b)
      · rw [hcut_out W b hb, hcut_out W _ (hrev b hb), inv_one]
  have hcut_close : ∀ W : Edge L n k j → ComplexMatrix2, (∀ b ∈ cubeEdges c, ‖W b - 1‖ < ρ) →
      ∀ b, ComplexMatrix2.operatorNorm (cut W b - 1) < ρ := by
    intro W h b
    by_cases hb : b ∈ cubeEdges c
    · rw [hcut_eq W b hb]
      exact h b hb
    · rw [hcut_out W b hb]
      simpa [ComplexMatrix2.operatorNorm] using hρ
  have hcut_read : ∀ W : Edge L n k j → ComplexMatrix2,
      normalizedMean W c = normalizedMean (cut W) c :=
    fun W => hR _ _ fun b hb => (hcut_eq W b hb).symm
  refine ⟨fun W _ _ W' he => hR _ _ he, fun W hW h => ?_, fun W hW h => ?_,
    fun V hV B hB t₀ h => ?_⟩
  · rw [hcut_read W]
    exact (hN _ (hcut_mem W hW) (hcut_close W h)).1
  · rw [hcut_read W]
    exact (hN _ (hcut_mem W hW) (hcut_close W h)).2
  · let γ : ℂ → Edge L n k j → ComplexMatrix2 :=
      fun t => cut (PeriodicLattice.expTwist ((t₀ + t) • B) V)
    have hγ : ∀ b, DifferentiableAt ℂ (fun t => γ t b) 0 := by
      intro b
      by_cases hb : b ∈ cubeEdges c
      · have e : (fun t => γ t b) =
            fun t => PeriodicLattice.expTwist ((t₀ + t) • B) V b := by
          funext t
          exact hcut_eq _ b hb
        rw [e]
        have h₁ := F.differentiableAt_expTwist hV hB b (t₀ + 0)
        exact DifferentiableAt.comp (f := fun t : ℂ => t₀ + t) (0 : ℂ) h₁ (by fun_prop)
      · have e : (fun t => γ t b) = fun _ => 1 := by
          funext t
          exact hcut_out _ b hb
        rw [e]
        exact differentiableAt_const _
    have h0 : γ 0 = cut (PeriodicLattice.expTwist (t₀ • B) V) := by
      simp only [γ, add_zero]
    have hW := F.expTwist_mem hV ((complexEdgeForms L n k j).smul_mem t₀ hB)
    obtain ⟨D, hD⟩ := hA _ (hcut_mem _ hW) (hcut_close _ h)
    have h₁ := (hD (fun b => deriv (fun t => γ t b) 0) γ h0
      fun b => (hγ b).hasDerivAt).differentiableAt
    have h₂ : DifferentiableAt ℂ
        (fun t : ℂ => normalizedMean (γ (t - t₀)) c) t₀ := by
      have h₃ : DifferentiableAt ℂ (fun t => normalizedMean (γ t) c) (t₀ - t₀) := by
        rwa [sub_self]
      exact DifferentiableAt.comp (f := fun t : ℂ => t - t₀) t₀ h₃ (by fun_prop)
    refine h₂.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    show normalizedMean _ c = normalizedMean _ c
    rw [hcut_read (PeriodicLattice.expTwist (t • B) V)]
    simp only [γ, add_sub_cancel]
end Lines
section CauchyEstimates
variable {L n k j : ℕ} {c : Edge L n k (j + 1)} {ρ : ℝ}
  {Φ Φ₁ Φ₂ : (Edge L n k j → ComplexMatrix2) → ComplexMatrix2}
private theorem Admissible.logDeriv_eq (F : EdgeData c) (G : Admissible ρ c Φ)
    {V B : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (hB : B ∈ complexEdgeForms L n k j)
    (hclose : ∀ b ∈ cubeEdges c, ‖V b - 1‖ < ρ) :
    logDirectionalDeriv ℂ (fun X => Φ (PeriodicLattice.expTwist X V)) (Φ V) B =
      Complex.I⁻¹ •
        (deriv (fun t : ℂ => Φ (PeriodicLattice.expTwist (t • B) V)) 0 * (Φ V)⁻¹) := by
  have h0 : ∀ b ∈ cubeEdges c, ‖PeriodicLattice.expTwist ((0 : ℂ) • B) V b - 1‖ < ρ := by
    rw [F.expTwist_zero hV]
    exact hclose
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 (F.eventually_close hV hB h0)
  let w : ℂ → ComplexMatrix2 := fun t => Φ (PeriodicLattice.expTwist (t • B) V)
  have hgroup : MapsTo w (ball 0 r) PeriodicLattice.complexGaugeGroup := fun t ht =>
    G.mem_unitDet _ (F.expTwist_mem hV ((complexEdgeForms L n k j).smul_mem t hB)) (hball t ht)
  have hw0 : DifferentiableAt ℂ w 0 := G.differentiableAt_line V hV B hB 0 h0
  obtain ⟨-, -, heq, -⟩ := F.logDeriv r hr w hgroup hw0
  have hwV : w 0 = Φ V := by
    simp only [w]
    rw [F.expTwist_zero hV]
  rw [hwV] at heq
  simp only [logDirectionalDeriv, Algebra.algebraMap_self, RingHom.id_apply]
  exact heq
private theorem Admissible.norm_logDeriv_le (F : EdgeData c) (G : Admissible ρ c Φ)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {V B : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (hB : B ∈ complexEdgeForms L n k j)
    (hclose : ∀ b ∈ cubeEdges c, ‖V b - 1‖ ≤ 3 / 4 * ρ) {β : ℝ} (hβ : 0 < β)
    (hB1 : ∀ b ∈ cubeEdges c, ‖B b‖ ≤ β) :
    ‖logDirectionalDeriv ℂ (fun X => Φ (PeriodicLattice.expTwist X V)) (Φ V) B‖ ≤
      16 * ρ⁻¹ * β := by
  have hr0 : 0 < ρ / (16 * β) := by positivity
  have hin : ∀ t ∈ closedBall (0 : ℂ) (ρ / (16 * β)), ∀ b ∈ cubeEdges c,
      ‖PeriodicLattice.expTwist (t • B) V b - 1‖ < ρ := by
    intro t ht b hb
    have h1 : ‖t‖ ≤ ρ / (16 * β) := by simpa using ht
    have h2 : ∀ b' ∈ cubeEdges c, ‖t‖ * ‖B b'‖ ≤ ρ / 16 := fun b' hb' => by
      calc ‖t‖ * ‖B b'‖ ≤ ρ / (16 * β) * β :=
            mul_le_mul h1 (hB1 b' hb') (norm_nonneg _) hr0.le
        _ = ρ / 16 := by field_simp
    have h3 := F.norm_expTwist_sub_one_le hV (a := ρ / 16) (by linarith) hclose h2 hb
    refine h3.trans_lt ?_
    nlinarith
  have hclose' : ∀ b ∈ cubeEdges c, ‖V b - 1‖ < ρ := fun b hb =>
    (hclose b hb).trans_lt (by linarith)
  let w : ℂ → ComplexMatrix2 := fun t => Φ (PeriodicLattice.expTwist (t • B) V)
  have hdiff : DifferentiableOn ℂ w (closedBall 0 (ρ / (16 * β))) := fun t ht =>
    (G.differentiableAt_line V hV B hB t (hin t ht)).differentiableWithinAt
  have hsmall : ∀ t ∈ closedBall (0 : ℂ) (ρ / (16 * β)), ‖w t - 1‖ < 1 / 2 := fun t ht =>
    G.near_one _ (F.expTwist_mem hV ((complexEdgeForms L n k j).smul_mem t hB)) (hin t ht)
  have hcauchy : ‖deriv w 0‖ ≤ 1 / 2 / (ρ / (16 * β)) := by
    have hf : DifferentiableOn ℂ (fun t => w t - 1) (closedBall 0 (ρ / (16 * β))) :=
      hdiff.sub_const 1
    have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr0
      (hf.diffContOnCl_ball subset_rfl) (C := 1 / 2)
      fun z hz => (hsmall _ (sphere_subset_closedBall hz)).le
    rwa [deriv_sub_const] at h
  obtain ⟨-, hinv⟩ := norm_le_of_near_one F.expLog (G.near_one V hV hclose')
  rw [G.logDeriv_eq F hV hB hclose', norm_smul]
  have hI : ‖(Complex.I⁻¹ : ℂ)‖ = 1 := by simp
  rw [hI, one_mul]
  calc ‖deriv w 0 * (Φ V)⁻¹‖ ≤ ‖deriv w 0‖ * ‖(Φ V)⁻¹‖ := norm_mul_le _ _
    _ ≤ (1 / 2 / (ρ / (16 * β))) * 2 := by gcongr
    _ = 16 * ρ⁻¹ * β := by field_simp
private theorem norm_contourLogDrift_le (F : EdgeData c) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hLpos : 0 < L) {y : Vertex L n k (j + 1)}
    (hG : ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
      Admissible ρ c fun W => PeriodicLattice.complexMeanContourHolonomy W y x)
    (hfin : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y :
      Set (Vertex L n k j)).Finite)
    (hcard : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y :
      Set (Vertex L n k j)).ncard ≤ L ^ 4)
    {V B : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (hB : B ∈ complexEdgeForms L n k j)
    (hclose : ∀ b ∈ cubeEdges c, ‖V b - 1‖ ≤ 3 / 4 * ρ) {β : ℝ} (hβ : 0 < β)
    (hB1 : ∀ b ∈ cubeEdges c, ‖B b‖ ≤ β) :
    ‖contourLogDrift V B y‖ ≤ 16 * ρ⁻¹ * β := by
  have hterm : ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
      ‖logDirectionalDeriv ℂ
        (fun X => PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.expTwist X V) y x)
        (PeriodicLattice.complexMeanContourHolonomy V y x) B‖ ≤ 16 * ρ⁻¹ * β := fun x hx =>
    (hG x hx).norm_logDeriv_le F hρ hρ1 hV hB hclose hβ hB1
  have hw : ‖PeriodicLattice.inverseFourthPowerWeight L‖ = ((L : ℝ) ^ 4)⁻¹ := by
    have e : (L : ℝ) ^ (-4 : ℤ) = ((L : ℝ) ^ 4)⁻¹ := by
      rw [zpow_neg]
      norm_cast
    simp only [PeriodicLattice.inverseFourthPowerWeight, e, Complex.norm_real,
      Real.norm_eq_abs]
    exact abs_of_pos (by positivity)
  have hcard' : (hfin.toFinset.card : ℝ) ≤ (L : ℝ) ^ 4 := by
    rw [← Set.ncard_eq_toFinset_card _ hfin]
    exact_mod_cast hcard
  simp only [contourLogDrift]
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, norm_smul, hw]
  have hsum := norm_sum_le hfin.toFinset (fun x => logDirectionalDeriv ℂ
    (fun X => PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.expTwist X V) y x)
    (PeriodicLattice.complexMeanContourHolonomy V y x) B)
  have hle : ∑ x ∈ hfin.toFinset, ‖logDirectionalDeriv ℂ
      (fun X => PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.expTwist X V) y x)
      (PeriodicLattice.complexMeanContourHolonomy V y x) B‖ ≤
      (hfin.toFinset.card : ℝ) * (16 * ρ⁻¹ * β) := by
    have := Finset.sum_le_card_nsmul hfin.toFinset _ (16 * ρ⁻¹ * β)
      fun x hx => hterm x (hfin.mem_toFinset.1 hx)
    simpa [nsmul_eq_mul] using this
  have hb : (0 : ℝ) ≤ 16 * ρ⁻¹ * β := by positivity
  calc ((L : ℝ) ^ 4)⁻¹ * _ ≤ ((L : ℝ) ^ 4)⁻¹ * ((L : ℝ) ^ 4 * (16 * ρ⁻¹ * β)) := by
        refine mul_le_mul_of_nonneg_left (hsum.trans (hle.trans ?_)) (by positivity)
        exact mul_le_mul_of_nonneg_right hcard' hb
    _ = 16 * ρ⁻¹ * β := by field_simp
private structure FirstOrderAgree (c : Edge L n k (j + 1))
    (Φ₁ Φ₂ : (Edge L n k j → ComplexMatrix2) → ComplexMatrix2) : Prop where
  one_mem : (fun _ => 1 : Edge L n k j → ComplexMatrix2) ∈
    fieldsIn L n k j PeriodicLattice.complexGaugeGroup
  left_one : Φ₁ (fun _ => 1) = 1
  right_one : Φ₂ (fun _ => 1) = 1
  logDeriv_eq : ∀ B ∈ complexEdgeForms L n k j,
    logDirectionalDeriv ℂ (fun X => Φ₁ (PeriodicLattice.expTwist X fun _ => 1))
        (Φ₁ fun _ => 1) B =
      logDirectionalDeriv ℂ (fun X => Φ₂ (PeriodicLattice.expTwist X fun _ => 1))
        (Φ₂ fun _ => 1) B
private theorem norm_quotient_sub_one_le (F : EdgeData c) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (G₁ : Admissible ρ c Φ₁) (G₂ : Admissible ρ c Φ₂) (A : FirstOrderAgree c Φ₁ Φ₂)
    {W : Edge L n k j → ComplexMatrix2}
    (hW : W ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup) {s : ℝ} (hs : 0 < s)
    (hs' : s ≤ ρ / 128) (hclose : ∀ b ∈ cubeEdges c, ‖W b - 1‖ ≤ s) :
    ‖Φ₁ W * (Φ₂ W)⁻¹ - 1‖ ≤ 16384 * ρ⁻¹ ^ 2 * s ^ 2 := by
  classical
  have hEL := F.expLog
  have hhalf : s ≤ 1 / 128 := hs'.trans (by linarith)
  have hlog : ∀ b ∈ cubeEdges c, ComplexMatrix2.logSeries (W b) ∈ ComplexMatrix2.traceless ∧
      ‖ComplexMatrix2.logSeries (W b)‖ ≤ 2 * s ∧
      ComplexMatrix2.matExp (ComplexMatrix2.logSeries (W b)) = W b := by
    intro b hb
    have hb₁ := hclose b hb
    have h := hEL.2.2.2.1 (W b - 1) (by show ‖W b - 1‖ < 1; linarith)
    have e : 1 + (W b - 1) = W b := by abel
    rw [e] at h
    obtain ⟨h₁, h₂, -, -, h₅⟩ := h
    have h₇ := hEL.2.2.2.2.2.2.1 (W b) (hW.1 b (mem_univ b))
      (by show ‖W b - 1‖ ≤ 9 / 10; linarith)
    refine ⟨h₇.2, ?_, h₅⟩
    have h₃ : ‖W b - 1‖ / (1 - ‖W b - 1‖) ≤ 2 * ‖W b - 1‖ := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [norm_nonneg (W b - 1)]
    linarith
  obtain ⟨f, hf⟩ : ∃ f : Edge L n k j → ComplexMatrix2,
      f = fun b => if b ∈ cubeEdges c then Complex.I⁻¹ • ComplexMatrix2.logSeries (W b)
        else 0 := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : Edge L n k j → ComplexMatrix2, B = extendOddly f := ⟨_, rfl⟩
  have hBpos : ∀ b : Edge L n k j, b.IsPositivelyOriented → B b = f b := fun b hb => by
    rw [hBdef]
    exact if_pos hb
  have hBneg : ∀ b : Edge L n k j, ¬ b.IsPositivelyOriented → B b = -f b.opposite :=
    fun b hb => by
      rw [hBdef]
      exact if_neg hb
  have hfP : ∀ b ∈ cubeEdges c, f b = Complex.I⁻¹ • ComplexMatrix2.logSeries (W b) :=
    fun b hb => by
      rw [hf]
      exact if_pos hb
  have hB : B ∈ complexEdgeForms L n k j := by
    refine (⟨fun b hb => ?_, fun b => ?_⟩ :
      PeriodicLattice.IsBondForm PeriodicLattice.complexLieAlgebra _)
    · show B b ∈ ComplexMatrix2.traceless
      rw [hBpos b hb]
      by_cases hbc : b ∈ cubeEdges c
      · rw [hfP b hbc]
        exact ComplexMatrix2.traceless.smul_mem _ (hlog b hbc).1
      · have : f b = 0 := by
          rw [hf]
          exact if_neg hbc
        rw [this]
        exact ComplexMatrix2.traceless.zero_mem
    · rcases F.xor_orient b with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · rw [hBneg _ h₂, hBpos b h₁, F.opposite_opposite b]
      · rw [hBpos _ h₁, hBneg b h₂, neg_neg]
  have hnorm : ∀ b ∈ cubeEdges c, ‖B b‖ ≤ 2 * s := by
    intro b hb
    have hI : ‖(Complex.I⁻¹ : ℂ)‖ = 1 := by simp
    by_cases hp : b.IsPositivelyOriented
    · rw [hBpos b hp, hfP b hb, norm_smul, hI, one_mul]
      exact (hlog b hb).2.1
    · rw [hBneg b hp, norm_neg, hfP _ (F.opposite_mem b hb), norm_smul, hI, one_mul]
      exact (hlog _ (F.opposite_mem b hb)).2.1
  have hone := A.one_mem
  have hzero : ∀ b ∈ cubeEdges c, ‖(fun _ => 1 : Edge L n k j → ComplexMatrix2) b - 1‖ ≤ 0 :=
    fun b _ => by
      simp
  have hR : (4 : ℝ) ≤ ρ / (32 * s) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hR0 : 0 < ρ / (32 * s) := by linarith
  let C : ℂ → Edge L n k j → ComplexMatrix2 :=
    fun z => PeriodicLattice.expTwist (z • B) fun _ => 1
  have hCmem : ∀ z, C z ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup := fun z =>
    F.expTwist_mem hone ((complexEdgeForms L n k j).smul_mem z hB)
  have hin : ∀ z ∈ ball (0 : ℂ) (ρ / (32 * s)), ∀ b ∈ cubeEdges c, ‖C z b - 1‖ < ρ := by
    intro z hz b hb
    have h1 : ‖z‖ ≤ ρ / (32 * s) := by
      have : ‖z‖ < ρ / (32 * s) := by simpa using hz
      exact this.le
    have h2 : ∀ b' ∈ cubeEdges c, ‖z‖ * ‖B b'‖ ≤ ρ / 16 := fun b' hb' => by
      calc ‖z‖ * ‖B b'‖ ≤ ρ / (32 * s) * (2 * s) :=
            mul_le_mul h1 (hnorm b' hb') (norm_nonneg _) hR0.le
        _ = ρ / 16 := by field_simp; ring
    have h3 := F.norm_expTwist_sub_one_le hone (a := ρ / 16) (by linarith) hzero h2 hb
    refine h3.trans_lt ?_
    nlinarith
  have hC0 : C 0 = fun _ => 1 := F.expTwist_zero hone
  have h0ball : (0 : ℂ) ∈ ball (0 : ℂ) (ρ / (32 * s)) := mem_ball_self hR0
  have hC1 : ∀ b ∈ cubeEdges c, C 1 b = W b := by
    intro b hb
    have hexp : ∀ b' ∈ cubeEdges c, b'.IsPositivelyOriented →
        ComplexMatrix2.matExp (Complex.I • ((1 : ℂ) • B) b') * 1 = W b' := by
      intro b' hb' hp
      have e : Complex.I • ((1 : ℂ) • B) b' = ComplexMatrix2.logSeries (W b') := by
        rw [one_smul, hBpos b' hp, hfP b' hb', smul_smul,
          mul_inv_cancel₀ Complex.I_ne_zero, one_smul]
      rw [e, mul_one]
      exact (hlog b' hb').2.2
    by_cases hp : b.IsPositivelyOriented
    · show PeriodicLattice.expTwist ((1 : ℂ) • B) (fun _ => 1) b = W b
      rw [expTwist_of_pos hp]
      exact hexp b hb hp
    · show PeriodicLattice.expTwist ((1 : ℂ) • B) (fun _ => 1) b = W b
      rw [expTwist_of_not_pos hp]
      have h₁ := hW.2 b.opposite (mem_univ _)
      rw [F.opposite_opposite b] at h₁
      rw [hexp _ (F.opposite_mem b hb) (F.opposite_pos hp), h₁]
  have hWclose : ∀ b ∈ cubeEdges c, ‖W b - 1‖ < ρ := fun b hb =>
    (hclose b hb).trans_lt (by linarith)
  have hv₁ : Φ₁ (C 1) = Φ₁ W := G₁.local_eq W hW hWclose _ hC1
  have hv₂ : Φ₂ (C 1) = Φ₂ W := G₂.local_eq W hW hWclose _ hC1
  let w₁ : ℂ → ComplexMatrix2 := fun z => Φ₁ (C z)
  let w₂ : ℂ → ComplexMatrix2 := fun z => Φ₂ (C z)
  have hd₁ : ∀ z ∈ ball (0 : ℂ) (ρ / (32 * s)), DifferentiableAt ℂ w₁ z := fun z hz =>
    G₁.differentiableAt_line _ hone B hB z (hin z hz)
  have hd₂ : ∀ z ∈ ball (0 : ℂ) (ρ / (32 * s)), DifferentiableAt ℂ w₂ z := fun z hz =>
    G₂.differentiableAt_line _ hone B hB z (hin z hz)
  have hg₂ : ∀ z ∈ ball (0 : ℂ) (ρ / (32 * s)), w₂ z ∈ ComplexMatrix2.unitDeterminant :=
    fun z hz => G₂.mem_unitDet _ (hCmem z) (hin z hz)
  have hdi : ∀ z ∈ ball (0 : ℂ) (ρ / (32 * s)),
      DifferentiableAt ℂ (fun t => (w₂ t)⁻¹) z := fun z hz =>
    differentiableAt_inv_of_unitDet (hd₂ z hz) (by
      filter_upwards [isOpen_ball.mem_nhds hz] with t ht
      exact hg₂ t ht)
  let h : ℂ → ComplexMatrix2 := fun z => w₁ z * (w₂ z)⁻¹
  have hdh : ∀ z ∈ ball (0 : ℂ) (ρ / (32 * s)), DifferentiableAt ℂ h z := fun z hz =>
    (hd₁ z hz).mul (hdi z hz)
  have hone₁ : w₁ 0 = 1 := by
    simp only [w₁]
    rw [hC0]
    exact A.left_one
  have hone₂ : w₂ 0 = 1 := by
    simp only [w₂]
    rw [hC0]
    exact A.right_one
  have hinv1 : (1 : ComplexMatrix2)⁻¹ = 1 := Matrix.inv_eq_right_inv (mul_one 1)
  have hh0 : h 0 = 1 := by
    simp only [h, hone₁, hone₂, hinv1, mul_one]
  have hdeq : deriv w₁ 0 = deriv w₂ 0 := by
    have e₁ := G₁.logDeriv_eq F hone hB fun b _ => by simpa using hρ
    have e₂ := G₂.logDeriv_eq F hone hB fun b _ => by simpa using hρ
    have e₃ := A.logDeriv_eq B hB
    rw [e₁, e₂, A.left_one, A.right_one, hinv1, mul_one, mul_one] at e₃
    exact smul_right_injective _ (inv_ne_zero Complex.I_ne_zero) e₃
  have hdh0 : deriv h 0 = 0 := by
    have hm : HasDerivAt (fun z => h z * w₂ z) (deriv h 0 * w₂ 0 + h 0 * deriv w₂ 0) 0 :=
      (hdh 0 h0ball).hasDerivAt.mul (hd₂ 0 h0ball).hasDerivAt
    have he : (fun z => h z * w₂ z) =ᶠ[𝓝 0] w₁ := by
      filter_upwards [isOpen_ball.mem_nhds h0ball] with z hz
      simp only [h]
      rw [mul_assoc, inv_mul_of_unitDet (hg₂ z hz), mul_one]
    have h₃ : HasDerivAt w₁ (deriv h 0 * w₂ 0 + h 0 * deriv w₂ 0) 0 :=
      hm.congr_of_eventuallyEq he.symm
    have h₄ := h₃.deriv
    rw [hone₂, hh0, mul_one, one_mul, hdeq] at h₄
    have h₅ : deriv h 0 + deriv w₂ 0 = 0 + deriv w₂ 0 := by
      rw [zero_add]
      exact h₄.symm
    exact add_right_cancel h₅
  let g : ℂ → ComplexMatrix2 := fun z => h z - 1
  have hgd : DifferentiableOn ℂ g (ball 0 (ρ / (32 * s))) := fun z hz =>
    ((hdh z hz).sub_const 1).differentiableWithinAt
  have hgb : ∀ z ∈ ball (0 : ℂ) (ρ / (32 * s)), ‖g z‖ ≤ 4 := by
    intro z hz
    obtain ⟨a₁, -⟩ := norm_le_of_near_one hEL (G₁.near_one _ (hCmem z) (hin z hz))
    obtain ⟨-, a₂⟩ := norm_le_of_near_one hEL (G₂.near_one _ (hCmem z) (hin z hz))
    have h₁ : ‖h z‖ ≤ 3 / 2 * 2 := by
      refine (norm_mul_le _ _).trans ?_
      exact mul_le_mul a₁ a₂ (norm_nonneg _) (by norm_num)
    have h₂ := norm_sub_le (h z) 1
    have h₃ : ‖(1 : ComplexMatrix2)‖ = 1 := norm_one
    simp only [g]
    linarith
  have hg0 : g 0 = 0 := by
    simp only [g, hh0, sub_self]
  have hgd0 : deriv g 0 = 0 := by
    simp only [g]
    rw [deriv_sub_const]
    exact hdh0
  have hfin := norm_one_le_of_vanishing_order_two hR hgd hgb hg0 hgd0
  have e : g 1 = Φ₁ W * (Φ₂ W)⁻¹ - 1 := by
    simp only [g, h, w₁, w₂, hv₁, hv₂]
  rw [e] at hfin
  refine hfin.trans (le_of_eq ?_)
  field_simp
  ring
end CauchyEstimates
section StepDifference
variable {L n k j : ℕ} {c : Edge L n k (j + 1)} {ρ : ℝ}
  {Φ₁ Φ₂ : (Edge L n k j → ComplexMatrix2) → ComplexMatrix2}
private theorem step_difference_eq {u m g U A Gd nH nT : ComplexMatrix2}
    (hm : m ∈ ComplexMatrix2.unitDeterminant)
    (hu : u = g * m) (hU : U = Gd * m + g * A) :
    (Complex.I⁻¹ • (U * u⁻¹) + (ComplexMatrix2.conjugateBy u nH - nT)) -
        (Complex.I⁻¹ • (A * m⁻¹) + (ComplexMatrix2.conjugateBy m nH - nT)) =
      Complex.I⁻¹ • (Gd * g⁻¹) +
        (ComplexMatrix2.conjugateBy g
            (Complex.I⁻¹ • (A * m⁻¹) + ComplexMatrix2.conjugateBy m nH) -
          (Complex.I⁻¹ • (A * m⁻¹) + ComplexMatrix2.conjugateBy m nH)) := by
  have hinv : u⁻¹ = m⁻¹ * g⁻¹ := by rw [hu, Matrix.mul_inv_rev]
  have hmm : m * m⁻¹ = 1 := mul_inv_of_unitDet hm
  have e₁ : U * u⁻¹ = Gd * g⁻¹ + g * (A * m⁻¹) * g⁻¹ := by
    rw [hinv, hU, add_mul]
    congr 1
    · calc Gd * m * (m⁻¹ * g⁻¹) = Gd * (m * m⁻¹) * g⁻¹ := by noncomm_ring
        _ = _ := by rw [hmm, mul_one]
    · noncomm_ring
  have e₂ : ComplexMatrix2.conjugateBy u nH = g * (m * nH * m⁻¹) * g⁻¹ := by
    simp only [ComplexMatrix2.conjugateBy]
    rw [hinv, hu]
    noncomm_ring
  have e₃ : ComplexMatrix2.conjugateBy g
      (Complex.I⁻¹ • (A * m⁻¹) + ComplexMatrix2.conjugateBy m nH) =
      Complex.I⁻¹ • (g * (A * m⁻¹) * g⁻¹) + g * (m * nH * m⁻¹) * g⁻¹ := by
    simp only [ComplexMatrix2.conjugateBy, mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
  rw [e₁, e₂, e₃, smul_add]
  simp only [ComplexMatrix2.conjugateBy]
  abel
private theorem norm_step_difference_le (F : EdgeData c) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (G₁ : Admissible ρ c Φ₁) (G₂ : Admissible ρ c Φ₂) (A : FirstOrderAgree c Φ₁ Φ₂)
    {V B : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (hB : B ∈ complexEdgeForms L n k j)
    {s β : ℝ} (hs : 0 < s) (hs' : s ≤ ρ / 512) (hclose : ∀ b ∈ cubeEdges c, ‖V b - 1‖ ≤ s)
    (hβ : 0 < β) (hB1 : ∀ b ∈ cubeEdges c, ‖B b‖ ≤ β) {nH nT : ComplexMatrix2}
    (hnH : ‖nH‖ ≤ 16 * ρ⁻¹ * β) :
    ‖(logDirectionalDeriv ℂ (fun X => Φ₁ (PeriodicLattice.expTwist X V)) (Φ₁ V) B +
          (ComplexMatrix2.conjugateBy (Φ₁ V) nH - nT)) -
        (logDirectionalDeriv ℂ (fun X => Φ₂ (PeriodicLattice.expTwist X V)) (Φ₂ V) B +
          (ComplexMatrix2.conjugateBy (Φ₂ V) nH - nT))‖ ≤
      33 * (16384 * ρ⁻¹ ^ 2) * s * β := by
  classical
  have hEL := F.expLog
  have hρi : 0 < ρ⁻¹ := inv_pos.2 hρ
  have hone : ρ⁻¹ * ρ = 1 := inv_mul_cancel₀ hρ.ne'
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 16384 * ρ⁻¹ ^ 2 := ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hK]; positivity
  have hr0 : 0 < s / β := by positivity
  have hnear : ∀ t ∈ closedBall (0 : ℂ) (s / β), ∀ b ∈ cubeEdges c,
      ‖PeriodicLattice.expTwist (t • B) V b - 1‖ ≤ 4 * s := by
    intro t ht b hb
    have h1 : ‖t‖ ≤ s / β := by simpa using ht
    have h2 : ∀ b' ∈ cubeEdges c, ‖t‖ * ‖B b'‖ ≤ s := fun b' hb' => by
      calc ‖t‖ * ‖B b'‖ ≤ s / β * β := mul_le_mul h1 (hB1 b' hb') (norm_nonneg _) hr0.le
        _ = s := by field_simp
    have h3 := F.norm_expTwist_sub_one_le hV (a := s) (by linarith) hclose h2 hb
    refine h3.trans ?_
    nlinarith
  have hin : ∀ t ∈ closedBall (0 : ℂ) (s / β), ∀ b ∈ cubeEdges c,
      ‖PeriodicLattice.expTwist (t • B) V b - 1‖ < ρ := fun t ht b hb =>
    (hnear t ht b hb).trans_lt (by linarith)
  have hWmem : ∀ t : ℂ, PeriodicLattice.expTwist (t • B) V ∈
      fieldsIn L n k j PeriodicLattice.complexGaugeGroup := fun t =>
    F.expTwist_mem hV ((complexEdgeForms L n k j).smul_mem t hB)
  have h0mem : (0 : ℂ) ∈ closedBall (0 : ℂ) (s / β) := mem_closedBall_self hr0.le
  have hcloseV : ∀ b ∈ cubeEdges c, ‖V b - 1‖ < ρ := fun b hb =>
    (hclose b hb).trans_lt (by linarith)
  let w₁ : ℂ → ComplexMatrix2 := fun t => Φ₁ (PeriodicLattice.expTwist (t • B) V)
  let w₂ : ℂ → ComplexMatrix2 := fun t => Φ₂ (PeriodicLattice.expTwist (t • B) V)
  have hd₁ : ∀ t ∈ closedBall (0 : ℂ) (s / β), DifferentiableAt ℂ w₁ t := fun t ht =>
    G₁.differentiableAt_line V hV B hB t (hin t ht)
  have hd₂ : ∀ t ∈ closedBall (0 : ℂ) (s / β), DifferentiableAt ℂ w₂ t := fun t ht =>
    G₂.differentiableAt_line V hV B hB t (hin t ht)
  have hdi : ∀ t ∈ closedBall (0 : ℂ) (s / β),
      DifferentiableAt ℂ (fun t => (w₂ t)⁻¹) t := fun t ht =>
    differentiableAt_inv_of_unitDet (hd₂ t ht) (by
      filter_upwards [F.eventually_close hV hB (hin t ht)] with t' ht'
      exact G₂.mem_unitDet _ (hWmem t') ht')
  let wg : ℂ → ComplexMatrix2 := fun t => w₁ t * (w₂ t)⁻¹
  have hdg : ∀ t ∈ closedBall (0 : ℂ) (s / β), DifferentiableAt ℂ wg t := fun t ht =>
    (hd₁ t ht).mul (hdi t ht)
  have hsq : ∀ t ∈ closedBall (0 : ℂ) (s / β), ‖wg t - 1‖ ≤ K * (4 * s) ^ 2 := fun t ht => by
    rw [hK]
    exact norm_quotient_sub_one_le F hρ hρ1 G₁ G₂ A (hWmem t) (by positivity) (by linarith)
      (hnear t ht)
  have hcauchy : ‖deriv wg 0‖ ≤ K * (4 * s) ^ 2 / (s / β) := by
    have hf : DifferentiableOn ℂ (fun t => wg t - 1) (closedBall 0 (s / β)) := fun t ht =>
      ((hdg t ht).sub_const 1).differentiableWithinAt
    have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr0
      (hf.diffContOnCl_ball subset_rfl) (C := K * (4 * s) ^ 2)
      fun z hz => hsq z (sphere_subset_closedBall hz)
    rwa [deriv_sub_const] at h
  have hw₁ : w₁ 0 = Φ₁ V := by
    simp only [w₁]
    rw [F.expTwist_zero hV]
  have hw₂ : w₂ 0 = Φ₂ V := by
    simp only [w₂]
    rw [F.expTwist_zero hV]
  have hgr₁ := G₁.mem_unitDet V hV hcloseV
  have hgr₂ := G₂.mem_unitDet V hV hcloseV
  obtain ⟨g, hg⟩ : ∃ g : ComplexMatrix2, g = Φ₁ V * (Φ₂ V)⁻¹ := ⟨_, rfl⟩
  have hwg0 : wg 0 = g := by
    simp only [wg, hw₁, hw₂, hg]
  have hggr : g ∈ ComplexMatrix2.unitDeterminant := by
    rw [hg]
    exact mul_mem_unitDet hgr₁ (inv_mem_unitDet hgr₂)
  have hgclose : ‖g - 1‖ ≤ K * s ^ 2 := by
    rw [hg, hK]
    exact norm_quotient_sub_one_le F hρ hρ1 G₁ G₂ A hV hs (by linarith) hclose
  have hKs : K * s ^ 2 ≤ 1 / 16 := by
    have h₁ : ρ⁻¹ * s ≤ 1 / 512 := by
      calc ρ⁻¹ * s ≤ ρ⁻¹ * (ρ / 512) := mul_le_mul_of_nonneg_left hs' hρi.le
        _ = 1 / 512 := by
          rw [show ρ⁻¹ * (ρ / 512) = (ρ⁻¹ * ρ) / 512 by ring, hone]
    have h₂ : 0 ≤ ρ⁻¹ * s := by positivity
    rw [hK, show 16384 * ρ⁻¹ ^ 2 * s ^ 2 = 16384 * (ρ⁻¹ * s) ^ 2 by ring]
    nlinarith
  have hgsmall : ‖g - 1‖ < 1 / 2 := by linarith
  obtain ⟨-, hginv⟩ := norm_le_of_near_one hEL hgsmall
  have hU : deriv w₁ 0 = deriv wg 0 * Φ₂ V + g * deriv w₂ 0 := by
    have hm : HasDerivAt (fun t => wg t * w₂ t) (deriv wg 0 * w₂ 0 + wg 0 * deriv w₂ 0) 0 :=
      (hdg 0 h0mem).hasDerivAt.mul (hd₂ 0 h0mem).hasDerivAt
    have he : (fun t => wg t * w₂ t) =ᶠ[𝓝 0] w₁ := by
      filter_upwards [Metric.closedBall_mem_nhds (0 : ℂ) hr0] with t ht
      simp only [wg]
      rw [mul_assoc, inv_mul_of_unitDet (G₂.mem_unitDet _ (hWmem t) (hin t ht)), mul_one]
    have h₃ : HasDerivAt w₁ (deriv wg 0 * w₂ 0 + wg 0 * deriv w₂ 0) 0 :=
      hm.congr_of_eventuallyEq he.symm
    rw [h₃.deriv, hw₂, hwg0]
  have hu : Φ₁ V = g * Φ₂ V := by
    rw [hg, mul_assoc, inv_mul_of_unitDet hgr₂, mul_one]
  rw [G₁.logDeriv_eq F hV hB hcloseV, G₂.logDeriv_eq F hV hB hcloseV]
  change ‖(Complex.I⁻¹ • (deriv w₁ 0 * (Φ₁ V)⁻¹) + (ComplexMatrix2.conjugateBy (Φ₁ V) nH - nT)) -
    (Complex.I⁻¹ • (deriv w₂ 0 * (Φ₂ V)⁻¹) + (ComplexMatrix2.conjugateBy (Φ₂ V) nH - nT))‖ ≤ _
  rw [step_difference_eq hgr₂ hu hU]
  have hcl34 : ∀ b ∈ cubeEdges c, ‖V b - 1‖ ≤ 3 / 4 * ρ := fun b hb =>
    (hclose b hb).trans (by linarith)
  have hl₂ := G₂.norm_logDeriv_le F hρ hρ1 hV hB hcl34 hβ hB1
  rw [G₂.logDeriv_eq F hV hB hcloseV] at hl₂
  obtain ⟨a₁, a₂⟩ := norm_le_of_near_one hEL (G₂.near_one V hV hcloseV)
  have hAd := norm_conjugateBy_le a₁ a₂ nH
  obtain ⟨Z, hZ⟩ : ∃ Z : ComplexMatrix2,
      Z = Complex.I⁻¹ • (deriv w₂ 0 * (Φ₂ V)⁻¹) + ComplexMatrix2.conjugateBy (Φ₂ V) nH :=
    ⟨_, rfl⟩
  have hZn : ‖Z‖ ≤ 64 * ρ⁻¹ * β := by
    rw [hZ]
    refine (norm_add_le _ _).trans ?_
    have h₁ : ‖Complex.I⁻¹ • (deriv w₂ 0 * (Φ₂ V)⁻¹)‖ ≤ 16 * ρ⁻¹ * β := hl₂
    nlinarith
  rw [← hZ]
  have hI : ‖(Complex.I⁻¹ : ℂ)‖ = 1 := by simp
  have hterm₁ : ‖Complex.I⁻¹ • (deriv wg 0 * g⁻¹)‖ ≤ 32 * K * s * β := by
    rw [norm_smul, hI, one_mul]
    have e : K * (4 * s) ^ 2 / (s / β) = 16 * K * s * β := by field_simp; ring
    rw [e] at hcauchy
    calc ‖deriv wg 0 * g⁻¹‖ ≤ ‖deriv wg 0‖ * ‖g⁻¹‖ := norm_mul_le _ _
      _ ≤ (16 * K * s * β) * 2 := by gcongr
      _ = _ := by ring
  have hterm₂ : ‖ComplexMatrix2.conjugateBy g Z - Z‖ ≤ K * s * β := by
    have h₁ := norm_conjugateBy_sub_le hggr Z
    have h₂ : 2 * ‖g - 1‖ * ‖Z‖ * ‖g⁻¹‖ ≤ 2 * (K * s ^ 2) * (64 * ρ⁻¹ * β) * 2 := by
      gcongr
    have h₃ : ρ⁻¹ * s ≤ 1 / 512 := by
      calc ρ⁻¹ * s ≤ ρ⁻¹ * (ρ / 512) := mul_le_mul_of_nonneg_left hs' hρi.le
        _ = 1 / 512 := by
          rw [show ρ⁻¹ * (ρ / 512) = (ρ⁻¹ * ρ) / 512 by ring, hone]
    have h₅ : 0 ≤ K * s * β := by positivity
    nlinarith
  refine (norm_add_le _ _).trans ?_
  rw [← hK]
  nlinarith
end StepDifference
section AtEdge
variable {L n k j : ℕ}
private structure EdgeSetup (ρ : ℝ) (c : Edge L n k (j + 1)) : Prop where
  data : EdgeData c
  mean : Admissible ρ c fun W => normalizedMean W c
  smoothing : Admissible ρ c fun W => PeriodicLattice.complexBlockAverage W c
  contour : ∀ y ∈ ({c.source, c.target} : Set (Vertex L n k (j + 1))),
    ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
      Admissible ρ c fun W => PeriodicLattice.complexMeanContourHolonomy W y x
  agree : FirstOrderAgree c (fun W => normalizedMean W c)
    (fun W => PeriodicLattice.complexBlockAverage W c)
  cube_finite : ∀ y : Vertex L n k (j + 1),
    (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y :
      Set (Vertex L n k j)).Finite
  cube_ncard_le : ∀ y : Vertex L n k (j + 1),
    (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y :
      Set (Vertex L n k j)).ncard ≤ L ^ 4
private theorem meanCovariantStep_apply {c : Edge L n k (j + 1)}
    (hc : c.IsPositivelyOriented) (V B : Edge L n k j → ComplexMatrix2) :
    meanCovariantStep V B c = logDirectionalDeriv ℂ
        (fun X => normalizedMean (PeriodicLattice.expTwist X V) c) (normalizedMean V c) B +
      (ComplexMatrix2.conjugateBy (normalizedMean V c) (contourLogDrift V B c.target) -
        contourLogDrift V B c.source) := by
  simp only [meanCovariantStep, Pi.add_apply, covDiff, holLeftDifferential,
    extendOddly, if_pos hc]
private theorem covariantSmoothingDeriv_apply {c : Edge L n k (j + 1)}
    (hc : c.IsPositivelyOriented) (V B : Edge L n k j → ComplexMatrix2) :
    covariantSmoothingDeriv V B c = logDirectionalDeriv ℂ
        (fun X => PeriodicLattice.complexBlockAverage (PeriodicLattice.expTwist X V) c)
        (PeriodicLattice.complexBlockAverage V c) B +
      (ComplexMatrix2.conjugateBy (PeriodicLattice.complexBlockAverage V c)
          (contourLogDrift V B c.target) -
        contourLogDrift V B c.source) := by
  simp only [covariantSmoothingDeriv, complexSmoothingDeriv,
    holLeftDifferential, Pi.add_apply, covDiff, extendOddly, if_pos hc]
  rfl
private theorem EdgeSetup.norm_sub_le {ρ : ℝ} {c : Edge L n k (j + 1)} (S : EdgeSetup ρ c)
    (hc : c.IsPositivelyOriented) (hLpos : 0 < L) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {V B : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (hB : B ∈ complexEdgeForms L n k j)
    {s β : ℝ} (hs : 0 < s) (hs' : s ≤ ρ / 512) (hclose : ∀ b ∈ cubeEdges c, ‖V b - 1‖ ≤ s)
    (hβ : 0 < β) (hB1 : ∀ b ∈ cubeEdges c, ‖B b‖ ≤ β) :
    ‖meanCovariantStep V B c - covariantSmoothingDeriv V B c‖ ≤
      33 * (16384 * ρ⁻¹ ^ 2) * s * β := by
  have hcl : ∀ b ∈ cubeEdges c, ‖V b - 1‖ ≤ 3 / 4 * ρ := fun b hb =>
    (hclose b hb).trans (by linarith)
  have hn := norm_contourLogDrift_le S.data hρ hρ1 hLpos (y := c.target)
    (S.contour c.target (Or.inr rfl)) (S.cube_finite c.target) (S.cube_ncard_le c.target)
    hV hB hcl hβ hB1
  rw [meanCovariantStep_apply hc, covariantSmoothingDeriv_apply hc]
  exact norm_step_difference_le S.data hρ hρ1 S.mean S.smoothing S.agree hV hB hs hs' hclose
    hβ hB1 hn
private theorem EdgeSetup.norm_sub_le_of_nonneg {ρ : ℝ} {c : Edge L n k (j + 1)}
    (S : EdgeSetup ρ c)
    (hc : c.IsPositivelyOriented) (hLpos : 0 < L) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {V B : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (hB : B ∈ complexEdgeForms L n k j)
    {s β : ℝ} (hs : 0 ≤ s) (hs' : s ≤ ρ / 1024) (hclose : ∀ b ∈ cubeEdges c, ‖V b - 1‖ ≤ s)
    (hβ : 0 ≤ β) (hB1 : ∀ b ∈ cubeEdges c, ‖B b‖ ≤ β) :
    ‖meanCovariantStep V B c - covariantSmoothingDeriv V B c‖ ≤
      33 * (16384 * ρ⁻¹ ^ 2) * s * β := by
  have hcont : Tendsto (fun ε : ℝ => 33 * (16384 * ρ⁻¹ ^ 2) * (s + ε) * (β + ε)) (𝓝[>] 0)
      (𝓝 (33 * (16384 * ρ⁻¹ ^ 2) * s * β)) := by
    have h : Continuous fun ε : ℝ => 33 * (16384 * ρ⁻¹ ^ 2) * (s + ε) * (β + ε) := by fun_prop
    have h' := h.tendsto 0
    simp only [add_zero] at h'
    exact h'.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hcont ?_
  have hev : Ioo (0 : ℝ) (ρ / 1024) ∈ 𝓝[>] (0 : ℝ) :=
    Ioo_mem_nhdsGT (by positivity)
  filter_upwards [hev] with ε hε
  exact S.norm_sub_le hc hLpos hρ hρ1 hV hB (by linarith [hε.1]) (by linarith [hε.2])
    (fun b hb => (hclose b hb).trans (by linarith [hε.1])) (by linarith [hε.1])
    (fun b hb => (hB1 b hb).trans (by linarith [hε.1]))
end AtEdge
private structure Inputs : Prop where
  steps : RescaledTrivialSteps
  orientation : PeriodicLattice.BondEndpointsOrientation.Statement
  expLog : ComplexMatrix2.ExpLogEstimates
  chart : LeftChartFields.Claim
  smoothing : SmoothingNearIdentity
  polydiscs : DoubleBlockPolydisc.PolydiscsHold
  averageLocal : PeriodicLattice.ComplexAverageIsLocal
  contours : PairContourIndependence.Statement
  blocks : BlockStructure
  meanNear : NormalizedMeanNearOne
  meanCurves : ContourMeanComplexDerivative
  meanLocal : NormalizedMeanLocal
  meanDiff : HolDifferentialAtOneEqSmoothing
  meanAtOne : NormalizedMeanAtOne
section Setup
variable {L n k j : ℕ}
private theorem Inputs.edgeSetup (R : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j < k)
    {c : Edge L n k (j + 1)} (hc : c.IsPositivelyOriented) {ρ ρN ρA : ℝ} (hρ : 0 < ρ)
    (hρL : ρ ≤ polydiscRadius L) (hρN : ρ ≤ ρN) (hρA : ρ ≤ ρA)
    (hN : ∀ V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
      (∀ b, ComplexMatrix2.operatorNorm (V b - 1) < ρN) → ∀ c : Edge L n k (j + 1),
        c.IsPositivelyOriented →
        meanRadius V c ≠ 0 ∧ ‖meanRadius V c - 1‖ < 1 / 2 ∧
        ComplexMatrix2.operatorNorm (normalizedMean V c - 1) < 1 / 2 ∧
        normalizedMean V c ∈ PeriodicLattice.complexGaugeGroup ∧
        ∃ D : (Edge L n k j → ComplexMatrix2) →ₗ[ℝ] ComplexMatrix2,
          ∀ (g : Edge L n k j → ComplexMatrix2)
          (γ : ℝ → Edge L n k j → ComplexMatrix2), γ 0 = V →
          (∀ b, HasDerivAt (fun t => γ t b) (g b) 0) →
            HasDerivAt (fun t => normalizedMean (γ t) c) (D g) 0)
    (hA : ∀ V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
      (∀ b, ComplexMatrix2.operatorNorm (V b - 1) < ρA) → ∀ c : Edge L n k (j + 1),
        c.IsPositivelyOriented →
        ∃ D : (Edge L n k j → ComplexMatrix2) →ₗ[ℂ] ComplexMatrix2,
          ∀ (g : Edge L n k j → ComplexMatrix2)
          (γ : ℂ → Edge L n k j → ComplexMatrix2), γ 0 = V →
          (∀ b, HasDerivAt (fun t => γ t b) (g b) 0) →
            HasDerivAt (fun t => normalizedMean (γ t) c) (D g) 0) :
    EdgeSetup ρ c := by
  have hk : 1 ≤ k := by omega
  have hrad := (R.smoothing.1 L hL).2.2
  have hd := (R.polydiscs L hL k j hj).1 n hn c hc
  have hfo := hd.finite_open
  have serves := hrad.periodic n k j hn hj c hc
  have F : EdgeData c :=
    { expLog := R.expLog
      logDeriv := R.chart.2.1
      xor_orient := fun b =>
        ((R.orientation ⟨L, hL, ⟨k, hk⟩, ⟨n, hn⟩⟩ j hj.le).2.2.2 b).2.2.2.2.2
      opposite_opposite := fun b =>
        ((R.orientation ⟨L, hL, ⟨k, hk⟩, ⟨n, hn⟩⟩ j hj.le).2.2.2 b).2.2.2.1
      finite := hfo.finite
      opposite_mem := hfo.opposite_mem }
  have hblock : ∀ y : Vertex L n k (j + 1),
      (PeriodicLattice.unitBlock y).ncard = L ^ 4 ∧ (PeriodicLattice.unitBlock y).Finite :=
    fun y => by
      have hb := ((R.blocks L k (j + 1) hL hk (by omega) (by omega)).1 n hn).1 y
      have hcard : (PeriodicLattice.unitBlock y).ncard = L ^ 4 := hb.2.2.1
      have hLpos : 0 < L := by have := hL.2; omega
      exact ⟨hcard, Set.finite_of_ncard_pos (by rw [hcard]; positivity)⟩
  have hone : (fun _ => 1 : Edge L n k j → ComplexMatrix2) ∈
      fieldsIn L n k j PeriodicLattice.complexGaugeGroup := by
    refine ⟨fun _ _ => ?_, fun _ _ => ?_⟩
    · show Matrix.det (1 : ComplexMatrix2) = 1
      simp
    · simp
  have hstep := (R.steps L hL k hk n hn).2 j hj
  have hval := R.meanAtOne L hL n k j hn hj 0 (edgeFormSpace L n k j).zero_mem c hc
  refine ⟨F, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine F.admissible_normalizedMean hρ
      (fun W W' h => (R.meanLocal L hL n k j hn hj c hc W W' h).2.2)
      (fun V hV h => ?_) (fun V hV h => hA V hV (fun b => (h b).trans_le hρA) c hc)
    obtain ⟨-, -, h₁, h₂, -⟩ := hN V hV (fun b => (h b).trans_le hρN) c hc
    exact ⟨h₁, h₂⟩
  · exact F.admissible_of_holomorphic hρL serves.holomorphic_smoothing
      serves.smoothing_near_one
      fun W _ _ W' he => by
        unfold PeriodicLattice.complexBlockAverage
        simp only [if_pos hc]
        exact (R.averageLocal L n k j hL.1 hL.2 hn hj c hc).average_eq _ _ he
  · intro y hy x hx
    exact F.admissible_of_holomorphic hρL (serves.holomorphic_contourMean y hy x hx)
      (fun W hW => serves.contourMean_near_one W hW y hy x hx)
      fun W hW hWp W' hr =>
        ((R.contours L hL k j hj).1 n hn y x hx c c hc hc hy hy W hW hWp.2 hWp.2 W' W hr
          (fun _ _ => rfl)).2.2
  · refine ⟨hone, hval.2.2.1, ?_, fun B hB => ?_⟩
    · exact congrFun hstep.1 c
    · have h₁ := R.meanDiff L hL n k j hn hj B hB c hc
      have h₂ := congrFun ((hstep.2.2.2.2.1 B hB).1) c
      simp only [complexSmoothingDeriv, holLeftDifferential, extendOddly,
        if_pos hc] at h₁ h₂
      exact h₁.trans h₂.symm
  · exact fun y =>
      Set.Finite.preimage (f := Subtype.val) Subtype.val_injective.injOn (hblock y).2
  · exact fun y => by
      rw [← (hblock y).1]
      exact Set.ncard_le_ncard_of_injOn Subtype.val (fun x hx => hx)
        Subtype.val_injective.injOn (hblock y).2
end Setup
theorem meanStep_near_covariantDeriv (steps : RescaledTrivialSteps)
    (orientation : PeriodicLattice.BondEndpointsOrientation.Statement)
    (expLog : ComplexMatrix2.ExpLogEstimates)
    (chart : LeftChartFields.Claim)
    (smoothing : SmoothingNearIdentity)
    (polydiscs : DoubleBlockPolydisc.PolydiscsHold)
    (averageLocal : PeriodicLattice.ComplexAverageIsLocal)
    (contours : PairContourIndependence.Statement)
    (blocks : BlockStructure)
    (meanNear : NormalizedMeanNearOne)
    (meanCurves : ContourMeanComplexDerivative)
    (meanLocal : NormalizedMeanLocal)
    (meanDiff : HolDifferentialAtOneEqSmoothing)
    (meanAtOne : NormalizedMeanAtOne) :
    MeanStepNearCovariantDeriv.Claim := by
  intro L hL
  have R : Inputs := ⟨steps, orientation, expLog, chart, smoothing, polydiscs, averageLocal,
    contours, blocks, meanNear, meanCurves, meanLocal, meanDiff, meanAtOne⟩
  obtain ⟨ρN, hρN, hN⟩ := meanNear L hL
  obtain ⟨ρA, hρA, hA⟩ := meanCurves L hL
  have hrad := (smoothing.1 L hL).2.2
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = min (polydiscRadius L) (min ρN ρA) := ⟨_, rfl⟩
  have hρ : 0 < ρ := by
    rw [hρdef]
    exact lt_min hrad.pos (lt_min hρN hρA)
  have hρL : ρ ≤ polydiscRadius L := by
    rw [hρdef]
    exact min_le_left _ _
  have hρ₁ : ρ ≤ ρN := by
    rw [hρdef]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hρ₂ : ρ ≤ ρA := by
    rw [hρdef]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hρ1 : ρ ≤ 1 := hρL.trans hrad.le_one
  have hLpos : 0 < L := by have := hL.2; omega
  refine ⟨ρ / 1024, 33 * (16384 * ρ⁻¹ ^ 2), by positivity, by positivity, ?_⟩
  intro n k j hn hj V hV hs c hc B hB s β hs0 hβ0 hclose hB1
  have S := R.edgeSetup hL hn hj hc hρ hρL hρ₁ hρ₂ (hN n k j hn hj) (hA n k j hn hj)
  have h := S.norm_sub_le_of_nonneg hc hLpos hρ hρ1 hV hB (s := min s (ρ / 1024)) (β := β)
    (le_min hs0 (by positivity)) (min_le_right _ _)
    (fun b hb => le_min (hclose b hb) (hs b).le) hβ0 hB1
  refine h.trans ?_
  have h₀ : 0 ≤ 33 * (16384 * ρ⁻¹ ^ 2) := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (min_le_left _ _) h₀) hβ0
end YangMills.Construction.RunningCouplingSlope.MeanStepNearCovariantDeriv
end
