import YangMills.Construction.Coordinates.HolomorphicIffDifferentiable
import YangMills.Construction.Lattice.MatricesBlocksAndGaugeTransformations
import YangMills.Construction.Matrices.ExpLogEstimates
import YangMills.Construction.Matrices.NormExpLogBasics
import YangMills.Construction.Matrices.TripleExponentialExpansion
import YangMills.Construction.Towers.ExpansionOfThreeExponentialsInTheLeftChart
import YangMills.Construction.Towers.ThirdOrderVanishingAsACubicBound
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace YangMills.Construction.Tower.TripleExpExpansion
theorem lie_mem_traceless (A B : Matrices.ComplexMatrix2) :
    ⁅A, B⁆ ∈ Matrices.ComplexMatrix2.traceless := by
  show Matrix.trace ⁅A, B⁆ = 0
  rw [lie_eq_mul_sub_mul, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
theorem principalPart_mem_traceless {X Y Z : Matrices.ComplexMatrix2}
    (hX : X ∈ Matrices.ComplexMatrix2.traceless) (hY : Y ∈ Matrices.ComplexMatrix2.traceless)
    (hZ : Z ∈ Matrices.ComplexMatrix2.traceless) (s t : ℂ) :
    principalPart X Y Z s t ∈ Matrices.ComplexMatrix2.traceless :=
  Matrices.ComplexMatrix2.traceless.sub_mem
    (Matrices.ComplexMatrix2.traceless.add_mem
      (Matrices.ComplexMatrix2.traceless.sub_mem (Matrices.ComplexMatrix2.traceless.smul_mem s hY)
        (Matrices.ComplexMatrix2.traceless.smul_mem t
          (Matrices.ComplexMatrix2.traceless.sub_mem hZ hX)))
      (Matrices.ComplexMatrix2.traceless.smul_mem _
        (Matrices.ComplexMatrix2.traceless.smul_mem _ (lie_mem_traceless _ _))))
    (Matrices.ComplexMatrix2.traceless.smul_mem _
      (Matrices.ComplexMatrix2.traceless.smul_mem _ (lie_mem_traceless _ _)))
theorem principalPart_eq_smul_bch (X Y Z : Matrices.ComplexMatrix2) (s t : ℂ) :
    principalPart X Y Z s t = Complex.I⁻¹ •
      ((Complex.I • t • X + Complex.I • s • Y + -(Complex.I • t • Z)) + (1 / 2 : ℂ) •
        (⁅Complex.I • t • X, Complex.I • s • Y⁆ + ⁅Complex.I • t • X, -(Complex.I • t • Z)⁆ +
          ⁅Complex.I • s • Y, -(Complex.I • t • Z)⁆)) := by
  simp only [principalPart, lie_eq_mul_sub_mul, Complex.inv_I, smul_mul_assoc, mul_smul_comm,
    mul_neg, neg_mul, add_mul, mul_add, smul_smul]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  match_scalars <;> grind
theorem logRemainder_eq_smul_bch_error {V : Matrices.ComplexMatrix2} (hV : IsUnit V)
    (X Y Z : Matrices.ComplexMatrix2) (s t : ℂ) :
    logRemainder (tripleProduct X Y Z V) V (principalPart X Y Z) s t = Complex.I⁻¹ •
      (Matrices.ComplexMatrix2.logSeries (Matrices.ComplexMatrix2.matExp (Complex.I • t • X) *
          Matrices.ComplexMatrix2.matExp (Complex.I • s • Y) *
          Matrices.ComplexMatrix2.matExp (-(Complex.I • t • Z))) -
        (Complex.I • t • X + Complex.I • s • Y + -(Complex.I • t • Z)) - (1 / 2 : ℂ) •
        (⁅Complex.I • t • X, Complex.I • s • Y⁆ + ⁅Complex.I • t • X, -(Complex.I • t • Z)⁆ +
          ⁅Complex.I • s • Y, -(Complex.I • t • Z)⁆)) := by
  have hdet : IsUnit V.det := (Matrix.isUnit_iff_isUnit_det V).1 hV
  rw [logRemainder, principalPart_eq_smul_bch, tripleProduct,
    Matrix.mul_nonsing_inv_cancel_right _ _ hdet, smul_sub, smul_sub, smul_add]
  abel
theorem tripleProduct_mul_inv {V : Matrices.ComplexMatrix2} (hV : IsUnit V)
    (X Y Z : Matrices.ComplexMatrix2) (s t : ℂ) :
    tripleProduct X Y Z V s t * V⁻¹ =
      Matrices.ComplexMatrix2.matExp (Complex.I • t • X) *
        Matrices.ComplexMatrix2.matExp (Complex.I • s • Y) *
        Matrices.ComplexMatrix2.matExp (-(Complex.I • t • Z)) := by
  rw [tripleProduct,
    Matrix.mul_nonsing_inv_cancel_right _ _ ((Matrix.isUnit_iff_isUnit_det V).1 hV)]
theorem norm_I_smul_smul (c : ℂ) (A : Matrices.ComplexMatrix2) :
    ‖Complex.I • c • A‖ = ‖c‖ * ‖A‖ := by
  rw [norm_smul, norm_smul, Complex.norm_I, one_mul]
theorem exponent_norms_le {X Y Z : Matrices.ComplexMatrix2}
    {w : Coordinates.ComplexCoordinates 2}
    (hw : ‖w‖ * (‖X‖ + ‖Y‖ + ‖Z‖ + 1) < 1 / 12) :
    ‖Complex.I • w 1 • X‖ ≤ Matrices.ComplexMatrix2.tripleExpRadius ∧
      ‖Complex.I • w 0 • Y‖ ≤ Matrices.ComplexMatrix2.tripleExpRadius ∧
      ‖-(Complex.I • w 1 • Z)‖ ≤ Matrices.ComplexMatrix2.tripleExpRadius ∧
      ‖Complex.I • w 1 • X‖ + ‖Complex.I • w 0 • Y‖ + ‖-(Complex.I • w 1 • Z)‖ ≤
        ‖w‖ * (‖X‖ + ‖Y‖ + ‖Z‖ + 1) := by
  have hr : Matrices.ComplexMatrix2.tripleExpRadius = 1 / 12 := rfl
  have h0 : ‖w 0‖ ≤ ‖w‖ := norm_le_pi_norm w 0
  have h1 : ‖w 1‖ ≤ ‖w‖ := norm_le_pi_norm w 1
  have a := norm_nonneg X
  have b := norm_nonneg Y
  have c := norm_nonneg Z
  have n := norm_nonneg w
  have m1 : ‖w 1‖ * ‖X‖ ≤ ‖w‖ * ‖X‖ := mul_le_mul_of_nonneg_right h1 a
  have m2 : ‖w 0‖ * ‖Y‖ ≤ ‖w‖ * ‖Y‖ := mul_le_mul_of_nonneg_right h0 b
  have m3 : ‖w 1‖ * ‖Z‖ ≤ ‖w‖ * ‖Z‖ := mul_le_mul_of_nonneg_right h1 c
  rw [norm_neg, norm_I_smul_smul, norm_I_smul_smul, norm_I_smul_smul, hr]
  have p1 : 0 ≤ ‖w‖ * ‖X‖ := mul_nonneg n a
  have p2 : 0 ≤ ‖w‖ * ‖Y‖ := mul_nonneg n b
  have p3 : 0 ≤ ‖w‖ * ‖Z‖ := mul_nonneg n c
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
open Matrices Coordinates
theorem claim_holds (hThree : ComplexMatrix2.TripleExpExpansionStatement)
    (hThird : VanishingOrderThreeIffCubicBound)
    (hExpLog : ComplexMatrix2.ExpLogEstimates)
    (hElem : ComplexMatrix2.NormExpLogBasics)
    (hGauge : PeriodicLattice.ElementaryStepFacts)
    (hHol : ComplexCoordinates.HolomorphicDifferentiable.HolomorphicIffDifferentiableStatement) :
    Claim := by
  intro X Y Z V hX hY hZ hV
  obtain ⟨hBound, -⟩ := hThree
  obtain ⟨-, -, -, -, -, hDet, hLogDet, -⟩ := hExpLog
  obtain ⟨⟨-, -, -, -, hEntry, -⟩, -⟩ := hElem
  obtain ⟨-, -, hSeries, -, -⟩ := hGauge 13 1 1 0 ⟨⟨6, rfl⟩, le_rfl⟩ one_pos zero_lt_one
  obtain ⟨hAnalytic, -, -, hExpOfLog⟩ := hSeries
  set K : ℝ := ‖X‖ + ‖Y‖ + ‖Z‖ + 1 with hKdef
  have hK : 0 < K := by positivity
  set δ : ℝ := 1 / (12 * K) with hδdef
  have hδ : 0 < δ := by positivity
  have small : ∀ w : ComplexCoordinates 2, ‖w‖ < δ → ‖w‖ * K < 1 / 12 := fun w hw => by
    have := mul_lt_mul_of_pos_right hw hK
    have e : δ * K = 1 / 12 := by rw [hδdef]; field_simp
    linarith
  set U : Set (ComplexCoordinates 2) := Metric.ball 0 δ with hUdef
  have hOpen : IsOpen U := Metric.isOpen_ball
  have h0 : (0 : ComplexCoordinates 2) ∈ U := Metric.mem_ball_self hδ
  have inU : ∀ w ∈ U, ‖w‖ < δ := fun w hw => mem_ball_zero_iff.1 hw
  have nearOne : ∀ w ∈ U, ComplexMatrix2.operatorNorm (ComplexMatrix2.matExp (Complex.I • w 1 • X) *
      ComplexMatrix2.matExp (Complex.I • w 0 • Y) *
      ComplexMatrix2.matExp (-(Complex.I • w 1 • Z)) - 1) ≤ 1 / 2 :=
    fun w hw => by
      obtain ⟨a, b, c, -⟩ := exponent_norms_le (small w (inU w hw))
      exact (hBound _ _ _ a b c).1
  have inBall : ∀ w ∈ U, ComplexMatrix2.matExp (Complex.I • w 1 • X) *
      ComplexMatrix2.matExp (Complex.I • w 0 • Y) *
      ComplexMatrix2.matExp (-(Complex.I • w 1 • Z)) ∈ ComplexMatrix2.logBall := fun w hw =>
    lt_of_le_of_lt (nearOne w hw) (by norm_num)
  have hDiff : ∀ w ∈ U, DifferentiableAt ℂ (fun w : ComplexCoordinates 2 =>
      logRemainder (tripleProduct X Y Z V) V (principalPart X Y Z) (w 0) (w 1)) w := by
    intro w hw
    have expd : ∀ g : ComplexCoordinates 2 → ComplexMatrix2, DifferentiableAt ℂ g w →
        DifferentiableAt ℂ (fun w => ComplexMatrix2.matExp (g w)) w := fun g hg =>
      ((NormedSpace.exp_analytic (𝕂 := ℂ) (g w)).differentiableAt).comp w hg
    have d0 : DifferentiableAt ℂ (fun w : ComplexCoordinates 2 => w 0) w :=
      differentiableAt_apply 0 w
    have d1 : DifferentiableAt ℂ (fun w : ComplexCoordinates 2 => w 1) w :=
      differentiableAt_apply 1 w
    have dM : DifferentiableAt ℂ (fun w : ComplexCoordinates 2 =>
        ComplexMatrix2.matExp (Complex.I • w 1 • X) * ComplexMatrix2.matExp (Complex.I • w 0 • Y) *
          ComplexMatrix2.matExp (-(Complex.I • w 1 • Z))) w :=
      ((expd _ ((d1.smul_const X).const_smul Complex.I)).mul
        (expd _ ((d0.smul_const Y).const_smul Complex.I))).mul
        (expd _ ((d1.smul_const Z).const_smul Complex.I).neg)
    have dL : DifferentiableAt ℂ (fun w : ComplexCoordinates 2 => ComplexMatrix2.logSeries
        (ComplexMatrix2.matExp (Complex.I • w 1 • X) * ComplexMatrix2.matExp (Complex.I • w 0 • Y) *
          ComplexMatrix2.matExp (-(Complex.I • w 1 • Z)))) w :=
      DifferentiableAt.comp (g := ComplexMatrix2.logSeries) w
        (hAnalytic _ (inBall w hw)).differentiableAt dM
    have dP : DifferentiableAt ℂ (fun w : ComplexCoordinates 2 =>
        principalPart X Y Z (w 0) (w 1)) w := by
      unfold principalPart
      exact (((d0.smul_const Y).sub (d1.smul_const (Z - X))).add
        ((d0.mul d1).smul_const _)).sub ((d1.pow 2).smul_const _)
    have e : (fun w : ComplexCoordinates 2 =>
        logRemainder (tripleProduct X Y Z V) V (principalPart X Y Z) (w 0) (w 1)) =
        fun w => Complex.I⁻¹ • ComplexMatrix2.logSeries (ComplexMatrix2.matExp (Complex.I • w 1 • X) *
          ComplexMatrix2.matExp (Complex.I • w 0 • Y) *
          ComplexMatrix2.matExp (-(Complex.I • w 1 • Z))) -
          principalPart X Y Z (w 0) (w 1) := by
      funext w
      rw [logRemainder, tripleProduct_mul_inv hV]
    rw [e]
    exact (dL.const_smul Complex.I⁻¹).sub dP
  let Lc : ComplexMatrix2 →ₗ[ℂ] ComplexCoordinates 4 :=
    { toFun := ComplexCoordinates.matrixEquiv
      map_add' := fun A B => by funext k; rfl
      map_smul' := fun c A => by funext k; rfl }
  have hHolo : ComplexCoordinates.IsHolomorphicIn U (fun w => ComplexCoordinates.matrixEquiv
      (logRemainder (tripleProduct X Y Z V) V (principalPart X Y Z) (w 0) (w 1))) := by
    refine (hHol 2 4 U _ hOpen).2 fun w hw => DifferentiableAt.differentiableWithinAt ?_
    have d₂ : DifferentiableAt ℂ ComplexCoordinates.matrixEquiv
        (logRemainder (tripleProduct X Y Z V) V (principalPart X Y Z) (w 0) (w 1)) :=
      (LinearMap.toContinuousLinearMap Lc).differentiableAt
    exact d₂.comp w (hDiff w hw)
  refine ⟨U, hOpen, h0, fun w hw => ⟨?_, ?_, ?_⟩, hHolo, (hThird U _ h0 hHolo).2
    ⟨9 * K ^ 3, δ, by positivity, hδ, fun w hw => ?_⟩⟩
  · rw [tripleProduct_mul_inv hV]
    exact inBall w hw
  · have e : principalPart X Y Z (w 0) (w 1) +
        logRemainder (tripleProduct X Y Z V) V (principalPart X Y Z) (w 0) (w 1) =
        Complex.I⁻¹ • ComplexMatrix2.logSeries (tripleProduct X Y Z V (w 0) (w 1) * V⁻¹) := by
      rw [logRemainder]
      abel
    rw [e, smul_smul, mul_inv_cancel₀ Complex.I_ne_zero, one_smul, tripleProduct_mul_inv hV,
      hExpOfLog _ (inBall w hw)]
    rfl
  · have tr0 : ∀ A ∈ ComplexMatrix2.traceless, ComplexMatrix2.fullTrace A = 0 := fun A h => h
    have hdet : (ComplexMatrix2.matExp (Complex.I • w 1 • X) *
        ComplexMatrix2.matExp (Complex.I • w 0 • Y) *
        ComplexMatrix2.matExp (-(Complex.I • w 1 • Z))).det = 1 := by
      rw [Matrix.det_mul, Matrix.det_mul, hDet, hDet, hDet,
        tr0 _ (ComplexMatrix2.traceless.smul_mem _ (ComplexMatrix2.traceless.smul_mem _ hX)),
        tr0 _ (ComplexMatrix2.traceless.smul_mem _ (ComplexMatrix2.traceless.smul_mem _ hY)),
        tr0 _ (ComplexMatrix2.traceless.neg_mem
          (ComplexMatrix2.traceless.smul_mem _ (ComplexMatrix2.traceless.smul_mem _ hZ)))]
      simp
    have hlog := (hLogDet _ hdet ((nearOne w hw).trans (by norm_num))).2
    rw [logRemainder, tripleProduct_mul_inv hV]
    exact ComplexMatrix2.traceless.sub_mem (ComplexMatrix2.traceless.smul_mem _ hlog)
      (principalPart_mem_traceless hX hY hZ _ _)
  · obtain ⟨a, b, c, d⟩ := exponent_norms_le (small w hw)
    have hb := (hBound _ _ _ a b c).2.1
    have hR : ‖logRemainder (tripleProduct X Y Z V) V (principalPart X Y Z) (w 0) (w 1)‖ ≤
        9 * (‖w‖ * K) ^ 3 := by
      rw [logRemainder_eq_smul_bch_error hV, norm_smul, norm_inv, Complex.norm_I, inv_one, one_mul]
      refine hb.trans ?_
      have s0 : 0 ≤ ‖Complex.I • w 1 • X‖ + ‖Complex.I • w 0 • Y‖ +
          ‖-(Complex.I • w 1 • Z)‖ := by positivity
      have := pow_le_pow_left₀ s0 d 3
      linarith
    have hC : ∀ A : ComplexMatrix2, ‖ComplexCoordinates.matrixEquiv A‖ ≤ ‖A‖ := fun A =>
      (pi_norm_le_iff_of_nonneg (norm_nonneg A)).2 fun _ => hEntry A _ _
    calc _ ≤ _ := hC _
      _ ≤ _ := hR
      _ = 9 * K ^ 3 * ‖w‖ ^ 3 := by ring
end YangMills.Construction.Tower.TripleExpExpansion
end
