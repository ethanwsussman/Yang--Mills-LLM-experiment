import YangMills.Construction.ColdChainAtEveryLevel.OneStepOfTheCoordinatesProof
import YangMills.Construction.HoleBesideASecondHole.MeanOfAProductOfGroupVariables
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace GroupMeans
open YangMills.Construction.BlockAverages
theorem unitQuat_norm (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
theorem unitQuat_inv_mul (g : UnitQuaternion) :
    ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (g : ℍ[ℝ]) = 1 := (Unitary.mem_iff.1 g.2).1
theorem unitQuat_mul_inv (g : UnitQuaternion) :
    (g : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := (Unitary.mem_iff.1 g.2).2
theorem unitQuat_coe_inv (g : UnitQuaternion) :
    ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = star (g : ℍ[ℝ]) := rfl
theorem unitQuat_coe_mul (g g' : UnitQuaternion) :
    ((g * g' : UnitQuaternion) : ℍ[ℝ]) = (g : ℍ[ℝ]) * (g' : ℍ[ℝ]) := rfl
theorem norm_unitQuat_mul (g : UnitQuaternion) (q : ℍ[ℝ]) : ‖(g : ℍ[ℝ]) * q‖ = ‖q‖ := by
  rw [norm_mul, unitQuat_norm, one_mul]
theorem norm_mul_unitQuat (g : UnitQuaternion) (q : ℍ[ℝ]) : ‖q * (g : ℍ[ℝ])‖ = ‖q‖ := by
  rw [norm_mul, unitQuat_norm, mul_one]
theorem unitQuat_dist_one_sq (z : UnitQuaternion) :
    ‖(z : ℍ[ℝ]) - 1‖ ^ 2 = 2 - 2 * (z : ℍ[ℝ]).re := by apply _root_.YangMills.Construction.GaugeFixing.norm_coe_sub_one_sq <;> assumption
theorem quat_re_le_norm (q : ℍ[ℝ]) : q.re ≤ ‖q‖ := by apply _root_.YangMills.Construction.BlockAverages.quaternion_re_le_norm <;> assumption
theorem norm_smul_polarPart (q : ℍ[ℝ]) :
    (‖q‖ : ℝ) • ((polarPart q : UnitQuaternion) : ℍ[ℝ]) = q := by
  by_cases h : q = 0
  · simp [h]
  · have hn : ‖q‖ ≠ 0 := norm_ne_zero_iff.2 h
    simp only [polarPart, dif_neg h]
    rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
theorem inv_polarPart_mul (q : ℍ[ℝ]) :
    ((polarPart q)⁻¹ : UnitQuaternion).1 * q = ((‖q‖ : ℝ) : ℍ[ℝ]) := by
  calc ((polarPart q)⁻¹ : UnitQuaternion).1 * q
      = ((polarPart q)⁻¹ : UnitQuaternion).1 *
          ((‖q‖ : ℝ) • ((polarPart q : UnitQuaternion) : ℍ[ℝ])) := by
        rw [norm_smul_polarPart]
    _ = (‖q‖ : ℝ) • (((polarPart q)⁻¹ : UnitQuaternion).1 *
          ((polarPart q : UnitQuaternion) : ℍ[ℝ])) := by
        rw [mul_smul_comm]
    _ = ((‖q‖ : ℝ) : ℍ[ℝ]) := by
        rw [show ((polarPart q)⁻¹ : UnitQuaternion).1 * ((polarPart q : UnitQuaternion) : ℍ[ℝ]) = 1
          from unitQuat_inv_mul _]
        ext <;> simp
variable {E : Type} (I : Finset E)
theorem finset_card_pos_real (hI : I.Nonempty) : (0 : ℝ) < I.card := by
  exact_mod_cast hI.card_pos
theorem average_const (hI : I.Nonempty) (c : ℝ) : average I (fun _ => c) = c := by
  have := finset_card_pos_real I hI
  simp only [average, Finset.sum_const, nsmul_eq_mul]
  field_simp
theorem average_add (f g : E → ℝ) :
    average I (fun e => f e + g e) = average I f + average I g := by
  simp only [average, Finset.sum_add_distrib, mul_add]
theorem average_const_mul (c : ℝ) (f : E → ℝ) :
    average I (fun e => c * f e) = c * average I f := by
  simp only [average, ← Finset.mul_sum]
  ring
theorem average_mono (hI : I.Nonempty) {f g : E → ℝ} (h : ∀ e, f e ≤ g e) :
    average I f ≤ average I g := by
  have := finset_card_pos_real I hI
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun e _ => h e) (by positivity)
theorem quatAverage_add (f g : E → ℍ[ℝ]) :
    quatAverage I (fun e => f e + g e) = quatAverage I f + quatAverage I g := by
  simp only [quatAverage, Finset.sum_add_distrib, smul_add]
theorem quatAverage_mul_left (a : ℍ[ℝ]) (f : E → ℍ[ℝ]) :
    quatAverage I (fun e => a * f e) = a * quatAverage I f := by
  simp only [quatAverage, ← Finset.mul_sum, mul_smul_comm]
theorem quatAverage_mul_right (a : ℍ[ℝ]) (f : E → ℍ[ℝ]) :
    quatAverage I (fun e => f e * a) = quatAverage I f * a := by
  simp only [quatAverage, ← Finset.sum_mul, smul_mul_assoc]
theorem quatAverage_const (hI : I.Nonempty) (c : ℍ[ℝ]) : quatAverage I (fun _ => c) = c := by
  have := finset_card_pos_real I hI
  simp only [quatAverage, Finset.sum_const]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  have : (1 / (I.card : ℝ)) * (I.card : ℝ) = 1 := by field_simp
  rw [this, one_smul]
theorem norm_quatAverage_le (hI : I.Nonempty) (f : E → ℍ[ℝ]) :
    ‖quatAverage I f‖ ≤ average I fun e => ‖f e‖ := by
  have := finset_card_pos_real I hI
  simp only [quatAverage, average]
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
theorem quat_re_finset_sum (f : E → ℍ[ℝ]) : (∑ e ∈ I, f e).re = ∑ e ∈ I, (f e).re := by apply _root_.YangMills.Construction.BlockAverages.CoordinateStep.re_finset_sum <;> assumption
theorem re_quatAverage (f : E → ℍ[ℝ]) : (quatAverage I f).re = average I fun e => (f e).re := by
  simp only [quatAverage, average, Quaternion.re_smul, smul_eq_mul, quat_re_finset_sum]
theorem quatAverage_rotated (g : E → UnitQuaternion) :
    quatAverage I (fun e => (((meanDirection I g)⁻¹ * g e : UnitQuaternion) : ℍ[ℝ])) =
      ((‖quatAverage I fun e => (g e : ℍ[ℝ])‖ : ℝ) : ℍ[ℝ]) := by
  have := quatAverage_mul_left I (((meanDirection I g)⁻¹ : UnitQuaternion) : ℍ[ℝ])
    fun e => (g e : ℍ[ℝ])
  simp only [unitQuat_coe_mul]
  rw [this]
  exact inv_polarPart_mul _
theorem variance_eq (hI : I.Nonempty) (g : E → UnitQuaternion) :
    variance I g = 2 - 2 * ‖quatAverage I fun e => (g e : ℍ[ℝ])‖ := by
  unfold variance
  simp only [unitQuat_dist_one_sq]
  have e1 : (fun e => 2 - 2 * (((meanDirection I g)⁻¹ * g e : UnitQuaternion) : ℍ[ℝ]).re) =
      fun e => (2 : ℝ) + (-2) * (((meanDirection I g)⁻¹ * g e : UnitQuaternion) : ℍ[ℝ]).re := by
    funext e
    ring
  rw [e1, average_add, average_const I hI, average_const_mul, ← re_quatAverage,
    quatAverage_rotated]
  simp
  ring
theorem norm_quatAverage_unit_le_one (hI : I.Nonempty) (g : E → UnitQuaternion) :
    ‖quatAverage I fun e => (g e : ℍ[ℝ])‖ ≤ 1 := by
  refine (norm_quatAverage_le I hI _).trans ?_
  simp only [unitQuat_norm]
  rw [average_const I hI]
theorem variance_nonneg (hI : I.Nonempty) (g : E → UnitQuaternion) : 0 ≤ variance I g := by
  rw [variance_eq I hI]
  linarith [norm_quatAverage_unit_le_one I hI g]
def rotatedDeviation (g : E → UnitQuaternion) (e : E) : ℝ :=
  ‖(((meanDirection I g)⁻¹ * g e : UnitQuaternion) : ℍ[ℝ]) - 1‖
theorem norm_pointwiseProd_sub_le (l : List (E → UnitQuaternion)) (e : E) :
    ‖((pointwiseProd l e : UnitQuaternion) : ℍ[ℝ]) - (prodMeanDirections I l : UnitQuaternion)‖ ≤
      (l.map fun g => rotatedDeviation I g e).sum := by
  induction l with
  | nil => simp [pointwiseProd, prodMeanDirections]
  | cons g r ih =>
    have hA : pointwiseProd (g :: r) e = g e * pointwiseProd r e := by simp [pointwiseProd]
    have hB : prodMeanDirections I (g :: r) = meanDirection I g * prodMeanDirections I r := by
      simp [prodMeanDirections]
    rw [hA, hB]
    simp only [List.map_cons, List.sum_cons]
    set u := meanDirection I g
    set A := pointwiseProd r e
    set B := prodMeanDirections I r
    have e1 : ((g e * A : UnitQuaternion) : ℍ[ℝ]) - ((u * B : UnitQuaternion) : ℍ[ℝ]) =
        (u : ℍ[ℝ]) * (((((u⁻¹ * g e : UnitQuaternion) : ℍ[ℝ]) - 1) * (A : ℍ[ℝ])) +
          ((A : ℍ[ℝ]) - B)) := by
      simp only [unitQuat_coe_mul]
      rw [sub_mul, one_mul, sub_add_sub_cancel, mul_sub, ← mul_assoc, ← mul_assoc,
        unitQuat_mul_inv, one_mul]
    rw [e1, norm_unitQuat_mul]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul_unitQuat]
    exact add_le_add le_rfl ih
theorem average_deviation_cross_le (hI : I.Nonempty) (g : E → UnitQuaternion)
    (l : List (E → UnitQuaternion)) :
    average I (fun e => rotatedDeviation I g e * (l.map fun g' => rotatedDeviation I g' e).sum) ≤
      ((l.length : ℝ) * variance I g + (l.map (variance I)).sum) / 2 := by
  induction l with
  | nil => simp [average, variance_nonneg I hI g]
  | cons g' r ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have e1 : (fun e => rotatedDeviation I g e *
          (rotatedDeviation I g' e + (r.map fun g' => rotatedDeviation I g' e).sum)) =
        fun e => rotatedDeviation I g e * rotatedDeviation I g' e +
          rotatedDeviation I g e * (r.map fun g' => rotatedDeviation I g' e).sum := by
      funext e
      ring
    rw [e1, average_add]
    have e2 : average I (fun e => rotatedDeviation I g e * rotatedDeviation I g' e) ≤
        (variance I g + variance I g') / 2 := by
      have : average I (fun e => rotatedDeviation I g e * rotatedDeviation I g' e) ≤
          average I (fun e => (1 / 2 : ℝ) *
            (rotatedDeviation I g e ^ 2 + rotatedDeviation I g' e ^ 2)) :=
        average_mono I hI fun e => by
          nlinarith [sq_nonneg (rotatedDeviation I g e - rotatedDeviation I g' e)]
      refine this.trans (le_of_eq ?_)
      rw [average_const_mul, average_add]
      simp only [variance, rotatedDeviation]
      ring
    push_cast
    linarith
theorem norm_quatAverage_pointwiseProd_sub_le (hI : I.Nonempty) (l : List (E → UnitQuaternion)) :
    ‖quatAverage I (fun e => ((pointwiseProd l e : UnitQuaternion) : ℍ[ℝ])) -
        (prodMeanDirections I l : UnitQuaternion)‖ ≤
      (l.length / 2 : ℝ) * (l.map (variance I)).sum := by
  induction l with
  | nil =>
    simp only [pointwiseProd, prodMeanDirections, List.map_nil, List.prod_nil]
    rw [quatAverage_const I hI]
    simp
  | cons g r ih =>
    set u := meanDirection I g with hu
    set B := prodMeanDirections I r with hBdef
    set m := variance I g with hm
    set Ms := (r.map (variance I)).sum with hMs
    have hA : ∀ e, ((pointwiseProd (g :: r) e : UnitQuaternion) : ℍ[ℝ]) =
        (u : ℍ[ℝ]) * (((((u⁻¹ * g e : UnitQuaternion) : ℍ[ℝ]) - 1) *
          (((pointwiseProd r e : UnitQuaternion) : ℍ[ℝ]) - B)) +
          ((((u⁻¹ * g e : UnitQuaternion) : ℍ[ℝ]) - 1) * B +
            ((pointwiseProd r e : UnitQuaternion) : ℍ[ℝ]))) := by
      intro e
      have : pointwiseProd (g :: r) e = g e * pointwiseProd r e := by simp [pointwiseProd]
      rw [this]
      have e0 : ∀ z A B' : ℍ[ℝ], (z - 1) * (A - B') + ((z - 1) * B' + A) = z * A := by
        intro z A B'
        noncomm_ring
      rw [e0, unitQuat_coe_mul, unitQuat_coe_mul, ← mul_assoc, ← mul_assoc, unitQuat_mul_inv,
        one_mul]
    have hB : prodMeanDirections I (g :: r) = u * B := by simp [prodMeanDirections, hu, hBdef]
    simp only [hA]
    rw [quatAverage_mul_left, hB, unitQuat_coe_mul, ← mul_sub, norm_unitQuat_mul, quatAverage_add,
      quatAverage_add, quatAverage_mul_right]
    have hz : quatAverage I (fun e => (((u⁻¹ * g e : UnitQuaternion) : ℍ[ℝ]) - 1)) =
        ((‖quatAverage I fun e => (g e : ℍ[ℝ])‖ : ℝ) : ℍ[ℝ]) - 1 := by
      have : (fun e => (((u⁻¹ * g e : UnitQuaternion) : ℍ[ℝ]) - 1)) =
          fun e => (((u⁻¹ * g e : UnitQuaternion) : ℍ[ℝ]) + (-1)) := by
        funext e
        exact sub_eq_add_neg _ _
      rw [this, quatAverage_add, quatAverage_rotated, quatAverage_const I hI]
      exact (sub_eq_add_neg _ _).symm
    rw [hz]
    have hn : ‖(((‖quatAverage I fun e => (g e : ℍ[ℝ])‖ : ℝ) : ℍ[ℝ]) - 1) * (B : ℍ[ℝ])‖ =
        m / 2 := by
      rw [norm_mul_unitQuat, hm, variance_eq I hI]
      have : ((‖quatAverage I fun e => (g e : ℍ[ℝ])‖ : ℝ) : ℍ[ℝ]) - 1 =
          ((‖quatAverage I fun e => (g e : ℍ[ℝ])‖ - 1 : ℝ) : ℍ[ℝ]) := by
        push_cast
        rfl
      rw [this, Quaternion.norm_coe, Real.norm_eq_abs,
        abs_of_nonpos (by linarith [norm_quatAverage_unit_le_one I hI g])]
      ring
    have hc : ‖quatAverage I (fun e => (((u⁻¹ * g e : UnitQuaternion) : ℍ[ℝ]) - 1) *
        (((pointwiseProd r e : UnitQuaternion) : ℍ[ℝ]) - B))‖ ≤ ((r.length : ℝ) * m + Ms) / 2 := by
      refine (norm_quatAverage_le I hI _).trans ?_
      refine le_trans (average_mono I hI fun e => ?_) (average_deviation_cross_le I hI g r)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_pointwiseProd_sub_le I r e) (norm_nonneg _)
    have e3 : quatAverage I (fun e => (((u⁻¹ * g e : UnitQuaternion) : ℍ[ℝ]) - 1) *
          (((pointwiseProd r e : UnitQuaternion) : ℍ[ℝ]) - B)) +
        ((((‖quatAverage I fun e => (g e : ℍ[ℝ])‖ : ℝ) : ℍ[ℝ]) - 1) * (B : ℍ[ℝ]) +
          quatAverage I (fun e => ((pointwiseProd r e : UnitQuaternion) : ℍ[ℝ]))) - (B : ℍ[ℝ]) =
        quatAverage I (fun e => (((u⁻¹ * g e : UnitQuaternion) : ℍ[ℝ]) - 1) *
          (((pointwiseProd r e : UnitQuaternion) : ℍ[ℝ]) - B)) +
        ((((‖quatAverage I fun e => (g e : ℍ[ℝ])‖ : ℝ) : ℍ[ℝ]) - 1) * (B : ℍ[ℝ])) +
          (quatAverage I (fun e => ((pointwiseProd r e : UnitQuaternion) : ℍ[ℝ])) -
            (B : ℍ[ℝ])) := by
      abel
    rw [e3]
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (norm_add_le _ _) ih).trans ?_
    rw [hn]
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [Nat.cast_add, Nat.cast_one, ← hm, ← hMs]
    have e5 : ((r.length : ℝ) + 1) / 2 * (m + Ms) =
        ((r.length : ℝ) * m + Ms) / 2 + m / 2 + (r.length : ℝ) / 2 * Ms := by ring
    rw [e5]
    linarith
theorem norm_prodMeanDirections_sub_one_le (hI : I.Nonempty) (l : List (E → UnitQuaternion)) :
    ‖((prodMeanDirections I l : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
      average I (fun e => ‖((pointwiseProd l e : UnitQuaternion) : ℍ[ℝ]) - 1‖) +
        (l.length / 2 : ℝ) * (l.map (variance I)).sum := by
  have h1 := norm_quatAverage_pointwiseProd_sub_le I hI l
  have h2 : ‖quatAverage I (fun e => ((pointwiseProd l e : UnitQuaternion) : ℍ[ℝ])) - 1‖ ≤
      average I (fun e => ‖((pointwiseProd l e : UnitQuaternion) : ℍ[ℝ]) - 1‖) := by
    have : quatAverage I (fun e => ((pointwiseProd l e : UnitQuaternion) : ℍ[ℝ])) - 1 =
        quatAverage I (fun e => ((pointwiseProd l e : UnitQuaternion) : ℍ[ℝ]) - 1) := by
      have e : (fun e => ((pointwiseProd l e : UnitQuaternion) : ℍ[ℝ]) - 1) =
          fun e => ((pointwiseProd l e : UnitQuaternion) : ℍ[ℝ]) + (-1) := by
        funext e
        exact sub_eq_add_neg _ _
      rw [e, quatAverage_add, quatAverage_const I hI]
      exact sub_eq_add_neg _ _
    rw [this]
    exact norm_quatAverage_le I hI _
  have h3 : ((prodMeanDirections I l : UnitQuaternion) : ℍ[ℝ]) - 1 =
      (quatAverage I (fun e => ((pointwiseProd l e : UnitQuaternion) : ℍ[ℝ])) - 1) -
        (quatAverage I (fun e => ((pointwiseProd l e : UnitQuaternion) : ℍ[ℝ])) -
          (prodMeanDirections I l : UnitQuaternion)) := by
    abel
  rw [h3]
  refine (norm_sub_le _ _).trans ?_
  linarith
theorem variance_le_average_sq_dist (hI : I.Nonempty) (g : E → UnitQuaternion) (T : UnitQuaternion) :
    variance I g ≤ average I fun e => ‖(g e : ℍ[ℝ]) - T‖ ^ 2 := by
  rw [variance_eq I hI]
  have e1 : ∀ e, ‖(g e : ℍ[ℝ]) - T‖ ^ 2 =
      2 + (-2) * (((T⁻¹ * g e : UnitQuaternion) : ℍ[ℝ])).re := by
    intro e
    have : ‖(g e : ℍ[ℝ]) - T‖ = ‖((T⁻¹ * g e : UnitQuaternion) : ℍ[ℝ]) - 1‖ := by
      rw [← norm_unitQuat_mul T⁻¹]
      congr 1
      rw [mul_sub, unitQuat_inv_mul, unitQuat_coe_mul]
    rw [this, unitQuat_dist_one_sq]
    ring
  simp only [e1]
  rw [average_add, average_const I hI, average_const_mul, ← re_quatAverage]
  have e2 : quatAverage I (fun e => ((T⁻¹ * g e : UnitQuaternion) : ℍ[ℝ])) =
      ((T⁻¹ : UnitQuaternion) : ℍ[ℝ]) * quatAverage I fun e => (g e : ℍ[ℝ]) := by
    simp only [unitQuat_coe_mul]
    exact quatAverage_mul_left I _ _
  rw [e2]
  have := quat_re_le_norm (((T⁻¹ : UnitQuaternion) : ℍ[ℝ]) * quatAverage I fun e => (g e : ℍ[ℝ]))
  rw [norm_unitQuat_mul] at this
  linarith
theorem polarPart_star (q : ℍ[ℝ]) : polarPart (star q) = (polarPart q)⁻¹ := by
  by_cases h : q = 0
  · simp [h, polarPart]
  · have h' : star q ≠ 0 := by simpa using h
    apply Subtype.ext
    simp only [polarPart, dif_neg h, dif_neg h']
    show ‖star q‖⁻¹ • star q = star (‖q‖⁻¹ • q)
    rw [Quaternion.star_smul, norm_star]
theorem quatAverage_inv_eq_star (g : E → UnitQuaternion) :
    quatAverage I (fun e => (((g e)⁻¹ : UnitQuaternion) : ℍ[ℝ])) =
      star (quatAverage I fun e => (g e : ℍ[ℝ])) := by
  simp only [quatAverage, unitQuat_coe_inv]
  rw [Quaternion.star_smul, star_sum]
theorem meanDirection_variance_inv (hI : I.Nonempty) (g : E → UnitQuaternion) :
    meanDirection I (fun e => (g e)⁻¹) = (meanDirection I g)⁻¹ ∧
      variance I (fun e => (g e)⁻¹) = variance I g := by
  constructor
  · simp only [meanDirection]
    rw [quatAverage_inv_eq_star I, polarPart_star]
  · rw [variance_eq I hI, variance_eq I hI, quatAverage_inv_eq_star I, norm_star]
theorem norm_sub_meanDirection_le (hI : I.Nonempty) (g : E → UnitQuaternion) (V : UnitQuaternion) :
    ‖(V : ℍ[ℝ]) - meanDirection I g‖ ≤
      2 * Real.sqrt (‖quatAverage I fun e => (g e : ℍ[ℝ])‖ -
        ((quatAverage I fun e => (g e : ℍ[ℝ])) * ((V⁻¹ : UnitQuaternion) : ℍ[ℝ])).re) +
        2 * variance I g := by
  set M := quatAverage I fun e => (g e : ℍ[ℝ]) with hM
  set u := meanDirection I g with hu
  set r := ‖M‖ with hr
  have hr1 : r ≤ 1 := norm_quatAverage_unit_le_one I hI g
  have hMu : M = r • (u : ℍ[ℝ]) := (norm_smul_polarPart M).symm
  have hfit : r - (M * ((V⁻¹ : UnitQuaternion) : ℍ[ℝ])).re = r * (‖(V : ℍ[ℝ]) - u‖ ^ 2 / 2) := by
    have e1 : ‖(V : ℍ[ℝ]) - u‖ = ‖((u * V⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ := by
      rw [← norm_mul_unitQuat V⁻¹, sub_mul, unitQuat_mul_inv, unitQuat_coe_mul, norm_sub_rev]
    rw [e1, unitQuat_dist_one_sq, hMu, smul_mul_assoc, Quaternion.re_smul, unitQuat_coe_mul]
    simp only [smul_eq_mul]
    ring
  rw [hfit]
  have hs : variance I g = 2 - 2 * r := variance_eq I hI g
  have hd : ‖(V : ℍ[ℝ]) - u‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [unitQuat_norm, unitQuat_norm]
    norm_num
  set d := ‖(V : ℍ[ℝ]) - u‖
  rw [hs]
  by_cases hh : 1 / 2 ≤ r
  · have : d ≤ 2 * Real.sqrt (r * (d ^ 2 / 2)) := by
      have h4 : (d / 2) ^ 2 ≤ r * (d ^ 2 / 2) := by nlinarith [sq_nonneg d]
      have := Real.le_sqrt_of_sq_le h4
      linarith
    linarith
  · rw [not_le] at hh
    have := Real.sqrt_nonneg (r * (d ^ 2 / 2))
    nlinarith
theorem meanProductEstimate_holds : MeanProductEstimate := by
  intro E I hI
  exact ⟨norm_prodMeanDirections_sub_one_le I hI, variance_le_average_sq_dist I hI,
    meanDirection_variance_inv I hI, norm_sub_meanDirection_le I hI⟩
end GroupMeans
end YangMills.Construction
end
