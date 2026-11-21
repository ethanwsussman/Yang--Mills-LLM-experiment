import YangMills.Construction.ClusterExpansionOfAStep.LocalLogarithmOfTheGroup
import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BondCoordinates
open BlockAverages ColdStepAtMirrorFrames QuaternionLog TorusFields
section Calculus
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
theorem secondDeriv_comp {f : F → G} {g : E → F} {x : E} (hf : ContDiffAt ℝ 2 f (g x))
    (hg : ContDiffAt ℝ 2 g x) (u v : E) :
    fderiv ℝ (fderiv ℝ (f ∘ g)) x u v =
      fderiv ℝ (fderiv ℝ f) (g x) (fderiv ℝ g x u) (fderiv ℝ g x v) +
        fderiv ℝ f (g x) (fderiv ℝ (fderiv ℝ g) x u v) := by
  have hfNear : ∀ᶠ z in nhds (g x), ContDiffAt ℝ 2 f z := hf.eventually (by norm_num)
  have hgNear : ∀ᶠ y in nhds x, ContDiffAt ℝ 2 g y := hg.eventually (by norm_num)
  have hfgNear : ∀ᶠ y in nhds x, ContDiffAt ℝ 2 f (g y) := hg.continuousAt.eventually hfNear
  have hEq : fderiv ℝ (f ∘ g) =ᶠ[nhds x] fun y => (fderiv ℝ f (g y)).comp (fderiv ℝ g y) := by
    filter_upwards [hfgNear, hgNear] with y hy₁ hy₂
    exact fderiv_comp y (hy₁.differentiableAt (by norm_num)) (hy₂.differentiableAt (by norm_num))
  rw [hEq.fderiv_eq]
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) (g x) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdg : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hc : HasFDerivAt (fun y => fderiv ℝ f (g y)) ((fderiv ℝ (fderiv ℝ f) (g x)).comp (fderiv ℝ g x)) x :=
    hdf.hasFDerivAt.comp x (hg.differentiableAt (by norm_num)).hasFDerivAt
  have hcomp := hc.clm_comp hdg.hasFDerivAt
  rw [hcomp.fderiv]
  simp [add_comm]
end Calculus
def toImaginaryCLM : EuclideanSpace ℝ (Fin 3) →L[ℝ] imaginaryQuaternions :=
  LinearMap.toContinuousLinearMap
    { toFun := toImaginary
      map_add' := by
        intro a b
        apply Subtype.ext
        refine Quaternion.ext _ _ ?_ ?_ ?_ ?_
        · show (0 : ℝ) = 0 + 0
          simp
        · show (a + b) 0 = a 0 + b 0
          simp
        · show (a + b) 1 = a 1 + b 1
          simp
        · show (a + b) 2 = a 2 + b 2
          simp
      map_smul' := by
        intro c a
        apply Subtype.ext
        refine Quaternion.ext _ _ ?_ ?_ ?_ ?_
        · show (0 : ℝ) = c * 0
          simp
        · show (c • a) 0 = c * a 0
          simp
        · show (c • a) 1 = c * a 1
          simp
        · show (c • a) 2 = c * a 2
          simp }
theorem toImaginaryCLM_apply (u : EuclideanSpace ℝ (Fin 3)) : toImaginaryCLM u = toImaginary u := rfl
theorem toImaginary_zero : toImaginary 0 = 0 := by
  have h := toImaginaryCLM.map_zero
  rwa [toImaginaryCLM_apply] at h
def bondMove (w : imaginaryQuaternions) (t : UnitQuaternion) (u : EuclideanSpace ℝ (Fin 3)) :
    UnitQuaternion :=
  t⁻¹ * expUnit (w + toImaginary u) * (expUnit w)⁻¹ * t
def bondLogMove (w : imaginaryQuaternions) (t : UnitQuaternion) (u : EuclideanSpace ℝ (Fin 3)) :
    imaginaryQuaternions :=
  logNearOne ((bondMove w t u : UnitQuaternion) : ℍ[ℝ])
def twoSidedMul (a b : ℍ[ℝ]) : ℍ[ℝ] →L[ℝ] ℍ[ℝ] :=
  (ContinuousLinearMap.mul ℝ ℍ[ℝ] a).comp ((ContinuousLinearMap.mul ℝ ℍ[ℝ]).flip b)
theorem twoSidedMul_apply (a b p : ℍ[ℝ]) : twoSidedMul a b p = a * (p * b) := rfl
def shiftedPoint (w : imaginaryQuaternions) (u : EuclideanSpace ℝ (Fin 3)) : ℍ[ℝ] :=
  ((w + toImaginary u : imaginaryQuaternions) : ℍ[ℝ])
theorem coe_bondMove (w : imaginaryQuaternions) (t : UnitQuaternion) :
    (fun u => ((bondMove w t u : UnitQuaternion) : ℍ[ℝ])) =
      (twoSidedMul ((t⁻¹ : UnitQuaternion) : ℍ[ℝ]) ((((expUnit w)⁻¹ * t : UnitQuaternion)) : ℍ[ℝ])) ∘
        (NormedSpace.exp ∘ shiftedPoint w) := by
  funext u
  simp only [bondMove, Function.comp, twoSidedMul_apply, shiftedPoint, Submonoid.coe_mul, expUnit, mul_assoc]
theorem contDiff_shiftedPoint (w : imaginaryQuaternions) {k : WithTop ℕ∞} : ContDiff ℝ k (shiftedPoint w) := by
  have e : shiftedPoint w = fun u => (w : ℍ[ℝ]) + imaginaryQuaternions.subtypeL (toImaginaryCLM u) := by
    funext u
    simp [shiftedPoint, toImaginaryCLM_apply]
  rw [e]
  exact contDiff_const.add (imaginaryQuaternions.subtypeL.contDiff.comp toImaginaryCLM.contDiff)
theorem fderiv_shiftedPoint (w : imaginaryQuaternions) (u : EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ (shiftedPoint w) u = imaginaryQuaternions.subtypeL.comp toImaginaryCLM := by
  have e : shiftedPoint w = fun u => (w : ℍ[ℝ]) + (imaginaryQuaternions.subtypeL.comp toImaginaryCLM) u := by
    funext u
    simp [shiftedPoint, toImaginaryCLM_apply]
  rw [e]
  rw [fderiv_const_add]
  exact (imaginaryQuaternions.subtypeL.comp toImaginaryCLM).fderiv
theorem fderiv_fderiv_shiftedPoint (w : imaginaryQuaternions) (u : EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ (fderiv ℝ (shiftedPoint w)) u = 0 := by
  have h : fderiv ℝ (shiftedPoint w) = fun _ => imaginaryQuaternions.subtypeL.comp toImaginaryCLM :=
    funext (fderiv_shiftedPoint w)
  rw [h]
  simp
theorem shiftedPoint_zero (w : imaginaryQuaternions) : shiftedPoint w 0 = w := by
  simp [shiftedPoint, toImaginary_zero]
theorem bondMove_zero (w : imaginaryQuaternions) (t : UnitQuaternion) : bondMove w t 0 = 1 := by
  simp [bondMove, toImaginary_zero]
theorem exists_bound_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (l : E →L[ℝ] F) : ∃ a : ℝ, 0 ≤ a ∧ ∀ u, ‖l u‖ ≤ a * ‖u‖ :=
  ⟨‖l‖, norm_nonneg _, l.le_opNorm⟩
theorem exists_bound_bilinear {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] (B : E →L[ℝ] F →L[ℝ] G) :
    ∃ a : ℝ, 0 ≤ a ∧ ∀ u v, ‖B u v‖ ≤ a * ‖u‖ * ‖v‖ :=
  ⟨‖B‖, B.opNorm_nonneg, B.le_opNorm₂⟩
theorem exists_deriv_bounds_closedBall {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [FiniteDimensional ℝ A] {f : A → A} (hf : ContDiff ℝ 3 f) : ∃ C : ℝ, 0 ≤ C ∧ ∀ p : A, ‖p‖ ≤ 3 →
      (∀ u, ‖fderiv ℝ f p u‖ ≤ C * ‖u‖) ∧ ∀ u v, ‖fderiv ℝ (fderiv ℝ f) p u v‖ ≤ C * ‖u‖ * ‖v‖ := by
  have c1 : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have c2 : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    (hf.fderiv_right (m := 2) (by norm_num)).continuous_fderiv (by norm_num)
  haveI : ProperSpace A := FiniteDimensional.proper_real A
  obtain ⟨C₁, h₁⟩ := (isCompact_closedBall (0 : A) 3).exists_bound_of_continuousOn c1.continuousOn
  obtain ⟨C₂, h₂⟩ := (isCompact_closedBall (0 : A) 3).exists_bound_of_continuousOn c2.continuousOn
  have h0 : (0 : A) ∈ Metric.closedBall (0 : A) 3 := by simp
  refine ⟨max C₁ C₂, le_max_of_le_left ((norm_nonneg _).trans (h₁ 0 h0)), fun p hp => ?_⟩
  have hp' : p ∈ Metric.closedBall (0 : A) 3 := by simpa using hp
  refine ⟨fun u => ?_, fun u v => ?_⟩
  · refine ((fderiv ℝ f p).le_opNorm u).trans ?_
    exact mul_le_mul_of_nonneg_right ((h₁ p hp').trans (le_max_left _ _)) (norm_nonneg _)
  · refine ((fderiv ℝ (fderiv ℝ f) p).le_opNorm₂ u v).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    exact mul_le_mul_of_nonneg_right ((h₂ p hp').trans (le_max_right _ _)) (norm_nonneg _)
theorem exists_deriv_bounds_exp : ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℍ[ℝ], ‖p‖ ≤ 3 →
    (∀ u, ‖fderiv ℝ (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) p u‖ ≤ C * ‖u‖) ∧
      ∀ u v, ‖fderiv ℝ (fderiv ℝ (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ])) p u v‖ ≤ C * ‖u‖ * ‖v‖ :=
  exists_deriv_bounds_closedBall contDiff_quaternionExp
theorem contDiffAt_bondLogMove (w : imaginaryQuaternions) (t : UnitQuaternion) :
    ContDiffAt ℝ 3 (bondLogMove w t) 0 := by
  have hQ : ContDiff ℝ 3 (fun u => ((bondMove w t u : UnitQuaternion) : ℍ[ℝ])) := by
    rw [coe_bondMove]
    exact (twoSidedMul _ _).contDiff.comp (contDiff_quaternionExp.comp (contDiff_shiftedPoint w))
  have h1 : ContDiffAt ℝ 3 logNearOne ((bondMove w t 0 : UnitQuaternion) : ℍ[ℝ]) := by
    rw [bondMove_zero]
    exact contDiffAt_logNearOne
  exact h1.comp (0 : EuclideanSpace ℝ (Fin 3)) hQ.contDiffAt
theorem bondLogMove_zero (w : imaginaryQuaternions) (t : UnitQuaternion) : bondLogMove w t 0 = 0 := by
  unfold bondLogMove
  rw [bondMove_zero]
  exact logNearOne_one
theorem expUnit_bondLogMove (w : imaginaryQuaternions) (t : UnitQuaternion) :
    ∀ᶠ u in nhds (0 : EuclideanSpace ℝ (Fin 3)), expUnit (bondLogMove w t u) = bondMove w t u := by
  have hQ : Continuous (fun u => ((bondMove w t u : UnitQuaternion) : ℍ[ℝ])) := by
    rw [coe_bondMove]
    exact (twoSidedMul _ _).continuous.comp ((contDiff_quaternionExp (k := 0)).continuous.comp
      (contDiff_shiftedPoint w (k := 0)).continuous)
  have h1 : Filter.Tendsto (fun u => ((bondMove w t u : UnitQuaternion) : ℍ[ℝ])) (nhds 0) (nhds 1) := by
    have h := hQ.tendsto (0 : EuclideanSpace ℝ (Fin 3))
    simpa [bondMove_zero] using h
  filter_upwards [h1.eventually exp_logNearOne] with u hu
  apply Subtype.ext
  exact hu (norm_unitQuaternion _)
theorem exists_bound_deriv_bondLogMove : ∃ C : ℝ, 0 < C ∧ ∀ (w : imaginaryQuaternions) (t : UnitQuaternion),
    ‖w‖ ≤ 3 →
    (∀ u, ‖fderiv ℝ (bondLogMove w t) 0 u‖ ≤ C * ‖u‖) ∧
      ∀ u v, ‖fderiv ℝ (fderiv ℝ (bondLogMove w t)) 0 u v‖ ≤ C * ‖u‖ * ‖v‖ := by
  obtain ⟨C₁, hC₁, hb⟩ := exists_deriv_bounds_exp
  set l : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℍ[ℝ] := imaginaryQuaternions.subtypeL.comp toImaginaryCLM with hl
  obtain ⟨a, ha0, hla⟩ := exists_bound_clm l
  obtain ⟨nD, hnD0, hnD⟩ := exists_bound_clm (fderiv ℝ logNearOne 1)
  obtain ⟨n2, hn20, hn2⟩ := exists_bound_bilinear (fderiv ℝ (fderiv ℝ logNearOne) 1)
  refine ⟨nD * (C₁ * a) + n2 * (C₁ * a) ^ 2 + nD * (C₁ * a ^ 2) + 1, by positivity, fun w t hw => ?_⟩
  set P := twoSidedMul ((t⁻¹ : UnitQuaternion) : ℍ[ℝ]) ((((expUnit w)⁻¹ * t : UnitQuaternion)) : ℍ[ℝ]) with hP
  have hPn : ∀ p, ‖P p‖ = ‖p‖ := by
    intro p
    rw [hP, twoSidedMul_apply, norm_mul, norm_mul, norm_unitQuaternion, norm_unitQuaternion, one_mul, mul_one]
  set G₀ : EuclideanSpace ℝ (Fin 3) → ℍ[ℝ] := NormedSpace.exp ∘ shiftedPoint w with hG₀
  have hline2 : ContDiffAt ℝ 2 (shiftedPoint w) (0 : EuclideanSpace ℝ (Fin 3)) :=
    (contDiff_shiftedPoint w).contDiffAt
  have hexp2 : ContDiffAt ℝ 2 (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) (shiftedPoint w 0) :=
    contDiff_quaternionExp.contDiffAt
  have hG2 : ContDiffAt ℝ 2 G₀ 0 := (contDiff_quaternionExp.comp (contDiff_shiftedPoint w)).contDiffAt
  have d1 : ∀ u, fderiv ℝ G₀ 0 u = fderiv ℝ (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) (w : ℍ[ℝ]) (l u) := by
    intro u
    rw [hG₀, fderiv_comp (0 : EuclideanSpace ℝ (Fin 3)) (hexp2.differentiableAt (by norm_num))
      (hline2.differentiableAt (by norm_num)), shiftedPoint_zero, fderiv_shiftedPoint]
    rfl
  have d2 : ∀ u v, fderiv ℝ (fderiv ℝ G₀) 0 u v =
      fderiv ℝ (fderiv ℝ (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ])) (w : ℍ[ℝ]) (l u) (l v) := by
    intro u v
    rw [hG₀, secondDeriv_comp hexp2 hline2, shiftedPoint_zero, fderiv_shiftedPoint,
      fderiv_fderiv_shiftedPoint]
    simp [hl]
  have hQe : (fun u => ((bondMove w t u : UnitQuaternion) : ℍ[ℝ])) = P ∘ G₀ := coe_bondMove w t
  have hQ2 : ContDiffAt ℝ 2 (P ∘ G₀) 0 := P.contDiff.contDiffAt.comp _ hG2
  have q1 : ∀ u, fderiv ℝ (P ∘ G₀) 0 u = P (fderiv ℝ G₀ 0 u) := by
    intro u
    rw [fderiv_comp (0 : EuclideanSpace ℝ (Fin 3)) P.differentiableAt (hG2.differentiableAt (by norm_num))]
    simp
  have q2 : ∀ u v, fderiv ℝ (fderiv ℝ (P ∘ G₀)) 0 u v = P (fderiv ℝ (fderiv ℝ G₀) 0 u v) := by
    intro u v
    have hfP : fderiv ℝ (P : ℍ[ℝ] → ℍ[ℝ]) = fun _ => P := funext fun p => P.fderiv
    rw [secondDeriv_comp P.contDiff.contDiffAt hG2, hfP]
    simp
  have hone : (P ∘ G₀) 0 = 1 := by
    have h1 : ((bondMove w t 0 : UnitQuaternion) : ℍ[ℝ]) = (P ∘ G₀) 0 := congrFun hQe 0
    rw [← h1, bondMove_zero]
    rfl
  have hlog2 : ContDiffAt ℝ 2 logNearOne ((P ∘ G₀) 0) := by
    rw [hone]
    exact contDiffAt_logNearOne.of_le (by norm_num)
  have hXi : bondLogMove w t = logNearOne ∘ (P ∘ G₀) := by
    funext u
    have h1 : ((bondMove w t u : UnitQuaternion) : ℍ[ℝ]) = (P ∘ G₀) u := congrFun hQe u
    show logNearOne ((bondMove w t u : UnitQuaternion) : ℍ[ℝ]) = logNearOne ((P ∘ G₀) u)
    rw [h1]
  have x1 : ∀ u, fderiv ℝ (bondLogMove w t) 0 u = fderiv ℝ logNearOne 1 (fderiv ℝ (P ∘ G₀) 0 u) := by
    intro u
    rw [hXi, fderiv_comp (0 : EuclideanSpace ℝ (Fin 3)) (hlog2.differentiableAt (by norm_num))
      (hQ2.differentiableAt (by norm_num)), hone]
    rfl
  have x2 : ∀ u v, fderiv ℝ (fderiv ℝ (bondLogMove w t)) 0 u v =
      fderiv ℝ (fderiv ℝ logNearOne) 1 (fderiv ℝ (P ∘ G₀) 0 u) (fderiv ℝ (P ∘ G₀) 0 v) +
        fderiv ℝ logNearOne 1 (fderiv ℝ (fderiv ℝ (P ∘ G₀)) 0 u v) := by
    intro u v
    rw [hXi, secondDeriv_comp hlog2 hQ2, hone]
  have hwb := hb (w : ℍ[ℝ]) hw
  have n1 : ∀ u, ‖fderiv ℝ (P ∘ G₀) 0 u‖ ≤ C₁ * a * ‖u‖ := by
    intro u
    rw [q1, hPn, d1]
    calc _ ≤ C₁ * ‖l u‖ := hwb.1 _
      _ ≤ C₁ * (a * ‖u‖) := mul_le_mul_of_nonneg_left (hla u) hC₁
      _ = _ := by ring
  have n2' : ∀ u v, ‖fderiv ℝ (fderiv ℝ (P ∘ G₀)) 0 u v‖ ≤ C₁ * a ^ 2 * ‖u‖ * ‖v‖ := by
    intro u v
    rw [q2, hPn, d2]
    calc _ ≤ C₁ * ‖l u‖ * ‖l v‖ := hwb.2 _ _
      _ ≤ C₁ * (a * ‖u‖) * (a * ‖v‖) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hla u) hC₁) (hla v) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  constructor
  · intro u
    rw [x1]
    have hu0 := norm_nonneg u
    calc _ ≤ nD * ‖fderiv ℝ (P ∘ G₀) 0 u‖ := hnD _
      _ ≤ nD * (C₁ * a * ‖u‖) := mul_le_mul_of_nonneg_left (n1 u) hnD0
      _ ≤ _ := by
        have e1 : 0 ≤ n2 * (C₁ * a) ^ 2 * ‖u‖ := by positivity
        have e2 : 0 ≤ nD * (C₁ * a ^ 2) * ‖u‖ := by positivity
        nlinarith
  · intro u v
    rw [x2]
    have hu0 := norm_nonneg u
    have hv0 := norm_nonneg v
    have t1 : ‖fderiv ℝ (fderiv ℝ logNearOne) 1 (fderiv ℝ (P ∘ G₀) 0 u) (fderiv ℝ (P ∘ G₀) 0 v)‖ ≤
        n2 * (C₁ * a) ^ 2 * ‖u‖ * ‖v‖ := by
      calc _ ≤ n2 * ‖fderiv ℝ (P ∘ G₀) 0 u‖ * ‖fderiv ℝ (P ∘ G₀) 0 v‖ := hn2 _ _
        _ ≤ n2 * (C₁ * a * ‖u‖) * (C₁ * a * ‖v‖) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (n1 u) hn20) (n1 v) (norm_nonneg _) (by positivity)
        _ = _ := by ring
    have t2 : ‖fderiv ℝ logNearOne 1 (fderiv ℝ (fderiv ℝ (P ∘ G₀)) 0 u v)‖ ≤
        nD * (C₁ * a ^ 2) * ‖u‖ * ‖v‖ := by
      calc _ ≤ nD * ‖fderiv ℝ (fderiv ℝ (P ∘ G₀)) 0 u v‖ := hnD _
        _ ≤ nD * (C₁ * a ^ 2 * ‖u‖ * ‖v‖) := mul_le_mul_of_nonneg_left (n2' u v) hnD0
        _ = _ := by ring
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ n2 * (C₁ * a) ^ 2 * ‖u‖ * ‖v‖ + nD * (C₁ * a ^ 2) * ‖u‖ * ‖v‖ := add_le_add t1 t2
      _ ≤ _ := by
        have e1 : 0 ≤ nD * (C₁ * a) * ‖u‖ * ‖v‖ := by positivity
        have e2 : 0 ≤ ‖u‖ * ‖v‖ := by positivity
        nlinarith
end BondCoordinates
end YangMills.Construction
end
