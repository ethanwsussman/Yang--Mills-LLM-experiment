import YangMills.Construction.ColdChainAtEveryLevel.LeastQuarticGaugeProof
import YangMills.Construction.ColdStepAtMirrorFrames.PlaquetteOfACutField
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace FourPlaquette
theorem expUnit_inv_eq_expUnit_neg (x : imaginaryQuaternions) : (expUnit x)⁻¹ = expUnit (-x) := by apply _root_.YangMills.Construction.LeastQuarticGauge.expUnit_inv <;> assumption
open BlockOffsets
theorem norm_expUnit_sub_one_sub_le_sq (w : imaginaryQuaternions) (h : ‖w‖ ≤ 1) :
    ‖((expUnit w : UnitQuaternion) : ℍ[ℝ]) - 1 - (w : ℍ[ℝ])‖ ≤ ‖w‖ ^ 2 := by
  have hn : ‖w‖ = ‖(w : ℍ[ℝ])‖ := rfl
  by_cases h0 : ‖w‖ = 0
  · have hw : w = 0 := norm_eq_zero.mp h0
    subst hw
    have : expUnit 0 = 1 := by
      apply Subtype.ext
      show NormedSpace.exp (((0 : imaginaryQuaternions)) : ℍ[ℝ]) = 1
      simp
    simp [this]
  have ht : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
  have e : ((expUnit w : UnitQuaternion) : ℍ[ℝ]) - 1 - (w : ℍ[ℝ]) =
      ((Real.cos ‖w‖ - 1 : ℝ) : ℍ[ℝ]) + (Real.sin ‖w‖ / ‖w‖ - 1) • (w : ℍ[ℝ]) := by
    show NormedSpace.exp (w : ℍ[ℝ]) - 1 - (w : ℍ[ℝ]) = _
    rw [exp_imaginary_eq w, ← hn, sub_smul, one_smul]
    push_cast
    abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Quaternion.norm_coe, Real.norm_eq_abs, Real.norm_eq_abs, ← hn]
  set t := ‖w‖ with htdef
  have c1 : |Real.cos t - 1| ≤ t ^ 2 / 2 := by
    have a1 := Real.one_sub_sq_div_two_le_cos (x := t)
    have a2 := Real.cos_le_one t
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg t]
  have c2 : |Real.sin t / t - 1| * t ≤ t ^ 2 / 2 := by
    have a1 := Real.sin_le ht.le
    have a2 := Real.sin_gt_sub_cube ht
    have e2 : |Real.sin t / t - 1| * t = |Real.sin t - t| := by
      rw [← abs_of_pos ht, ← abs_mul, abs_of_pos ht]
      congr 1
      field_simp
    rw [e2, abs_le]
    constructor <;> nlinarith [pow_pos ht 2, pow_pos ht 3, mul_le_mul_of_nonneg_left h (pow_pos ht 2).le]
  linarith
theorem norm_expUnit_four_mul_sub_linear_le (b : Fin 4 → imaginaryQuaternions) (hb : ∀ i, ‖b i‖ ≤ 1) :
    ‖((expUnit (b 0) * expUnit (b 1) * expUnit (b 2) * expUnit (b 3) : UnitQuaternion) : ℍ[ℝ]) - 1 -
        ((b 0 : ℍ[ℝ]) + (b 1 : ℍ[ℝ]) + (b 2 : ℍ[ℝ]) + (b 3 : ℍ[ℝ]))‖ ≤ 2 * (∑ i, ‖b i‖) ^ 2 := by
  have s0 := norm_expUnit_sub_one_sub_le_sq (b 0) (hb 0)
  have s1 := norm_expUnit_sub_one_sub_le_sq (b 1) (hb 1)
  have s2 := norm_expUnit_sub_one_sub_le_sq (b 2) (hb 2)
  have s3 := norm_expUnit_sub_one_sub_le_sq (b 3) (hb 3)
  have g0 := _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne_expUnit_le (b 0)
  have g1 := _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne_expUnit_le (b 1)
  have g2 := _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne_expUnit_le (b 2)
  have g3 := _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne_expUnit_le (b 3)
  have r2 : _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (expUnit (b 2) * expUnit (b 3)) ≤ ‖b 2‖ + ‖b 3‖ :=
    (_root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne_mul _ _).trans (add_le_add g2 g3)
  have r1 : _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (expUnit (b 1) * (expUnit (b 2) * expUnit (b 3))) ≤ ‖b 1‖ + (‖b 2‖ + ‖b 3‖) :=
    (_root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne_mul _ _).trans (add_le_add g1 r2)
  set q0 : ℍ[ℝ] := ((expUnit (b 0) : UnitQuaternion) : ℍ[ℝ]) with hq0
  set q1 : ℍ[ℝ] := ((expUnit (b 1) : UnitQuaternion) : ℍ[ℝ]) with hq1
  set q2 : ℍ[ℝ] := ((expUnit (b 2) : UnitQuaternion) : ℍ[ℝ]) with hq2
  set q3 : ℍ[ℝ] := ((expUnit (b 3) : UnitQuaternion) : ℍ[ℝ]) with hq3
  have hP : ((expUnit (b 0) * expUnit (b 1) * expUnit (b 2) * expUnit (b 3) : UnitQuaternion) : ℍ[ℝ]) =
      q0 * q1 * q2 * q3 := rfl
  have e : q0 * q1 * q2 * q3 - 1 - ((b 0 : ℍ[ℝ]) + (b 1 : ℍ[ℝ]) + (b 2 : ℍ[ℝ]) + (b 3 : ℍ[ℝ])) =
      (q0 - 1 - (b 0 : ℍ[ℝ])) + (q1 - 1 - (b 1 : ℍ[ℝ])) + (q2 - 1 - (b 2 : ℍ[ℝ])) + (q3 - 1 - (b 3 : ℍ[ℝ])) +
        (q0 - 1) * (q1 * (q2 * q3) - 1) + (q1 - 1) * (q2 * q3 - 1) + (q2 - 1) * (q3 - 1) := by
    noncomm_ring
  rw [hP, e]
  have n1 : ‖(q0 - 1) * (q1 * (q2 * q3) - 1)‖ ≤ ‖b 0‖ * (‖b 1‖ + (‖b 2‖ + ‖b 3‖)) := by
    rw [norm_mul]
    exact mul_le_mul g0 r1 (norm_nonneg _) (norm_nonneg _)
  have n2 : ‖(q1 - 1) * (q2 * q3 - 1)‖ ≤ ‖b 1‖ * (‖b 2‖ + ‖b 3‖) := by
    rw [norm_mul]
    exact mul_le_mul g1 r2 (norm_nonneg _) (norm_nonneg _)
  have n3 : ‖(q2 - 1) * (q3 - 1)‖ ≤ ‖b 2‖ * ‖b 3‖ := by
    rw [norm_mul]
    exact mul_le_mul g2 g3 (norm_nonneg _) (norm_nonneg _)
  have p0 := norm_nonneg (b 0)
  have p1 := norm_nonneg (b 1)
  have p2 := norm_nonneg (b 2)
  have p3 := norm_nonneg (b 3)
  rw [Fin.sum_univ_four]
  refine (norm_add_le _ _).trans ((add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add s0 s1)) s2)) s3)) n1)) n2)) n3).trans ?_)
  nlinarith [mul_nonneg p0 p1, mul_nonneg p0 p2, mul_nonneg p0 p3, mul_nonneg p1 p2, mul_nonneg p1 p3,
    mul_nonneg p2 p3, sq_nonneg (‖b 0‖), sq_nonneg (‖b 1‖), sq_nonneg (‖b 2‖), sq_nonneg (‖b 3‖)]
end FourPlaquette
open FourPlaquette
open BlockOffsets
theorem scaledPlaquetteBound_holds : ScaledPlaquetteBound := by
  intro a c hc hs
  have hs' : ∀ i, ‖a i‖ ≤ 1 := fun i =>
    (Finset.single_le_sum (f := fun i => ‖a i‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)).trans hs
  have hci : ∀ i, ‖c i • a i‖ ≤ ‖a i‖ := fun i => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hc i).1]
    nlinarith [(hc i).2, norm_nonneg (a i)]
  let b : Fin 4 → imaginaryQuaternions := ![c 0 • a 0, c 1 • a 1, -(c 2 • a 2), -(c 3 • a 3)]
  let b' : Fin 4 → imaginaryQuaternions := ![a 0, a 1, -a 2, -a 3]
  have hb : ∀ i, ‖b i‖ ≤ ‖a i‖ := fun i => by
    fin_cases i
    · exact hci 0
    · exact hci 1
    · show ‖-(c 2 • a 2)‖ ≤ _
      rw [norm_neg]; exact hci 2
    · show ‖-(c 3 • a 3)‖ ≤ _
      rw [norm_neg]; exact hci 3
  have hb' : ∀ i, ‖b' i‖ = ‖a i‖ := fun i => by
    fin_cases i
    · rfl
    · rfl
    · show ‖-a 2‖ = _
      rw [norm_neg]; rfl
    · show ‖-a 3‖ = _
      rw [norm_neg]; rfl
  have h1 := norm_expUnit_four_mul_sub_linear_le b fun i => (hb i).trans (hs' i)
  have h2 := norm_expUnit_four_mul_sub_linear_le b' fun i => (hb' i).le.trans (hs' i)
  set s := ∑ i, ‖a i‖ with hsdef
  have sb : ∑ i, ‖b i‖ ≤ s := Finset.sum_le_sum fun i _ => hb i
  have sb' : ∑ i, ‖b' i‖ = s := Finset.sum_congr rfl fun i _ => hb' i
  have sb0 : 0 ≤ ∑ i, ‖b i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have sq : (∑ i, ‖b i‖) ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ sb0 sb 2
  rw [sb'] at h2
  have hP : fourPlaquette (fun i => c i • a i) = expUnit (b 0) * expUnit (b 1) * expUnit (b 2) * expUnit (b 3) := by
    simp only [fourPlaquette, expUnit_inv_eq_expUnit_neg]
    rfl
  have hP' : fourPlaquette a = expUnit (b' 0) * expUnit (b' 1) * expUnit (b' 2) * expUnit (b' 3) := by
    simp only [fourPlaquette, expUnit_inv_eq_expUnit_neg]
    rfl
  set Lc : ℍ[ℝ] := (b 0 : ℍ[ℝ]) + (b 1 : ℍ[ℝ]) + (b 2 : ℍ[ℝ]) + (b 3 : ℍ[ℝ]) with hLc
  set L1 : ℍ[ℝ] := (b' 0 : ℍ[ℝ]) + (b' 1 : ℍ[ℝ]) + (b' 2 : ℍ[ℝ]) + (b' 3 : ℍ[ℝ]) with hL1
  have hrel : Lc = c 0 • L1 + ((c 1 - c 0) • (a 1 : ℍ[ℝ]) - (c 2 - c 0) • (a 2 : ℍ[ℝ]) -
      (c 3 - c 0) • (a 3 : ℍ[ℝ])) := by
    have q0 : (b 0 : ℍ[ℝ]) = c 0 • (a 0 : ℍ[ℝ]) := rfl
    have q1 : (b 1 : ℍ[ℝ]) = c 1 • (a 1 : ℍ[ℝ]) := rfl
    have q2 : (b 2 : ℍ[ℝ]) = -(c 2 • (a 2 : ℍ[ℝ])) := rfl
    have q3 : (b 3 : ℍ[ℝ]) = -(c 3 • (a 3 : ℍ[ℝ])) := rfl
    have r0 : (b' 0 : ℍ[ℝ]) = (a 0 : ℍ[ℝ]) := rfl
    have r1 : (b' 1 : ℍ[ℝ]) = (a 1 : ℍ[ℝ]) := rfl
    have r2 : (b' 2 : ℍ[ℝ]) = -(a 2 : ℍ[ℝ]) := rfl
    have r3 : (b' 3 : ℍ[ℝ]) = -(a 3 : ℍ[ℝ]) := rfl
    rw [hLc, hL1, q0, q1, q2, q3, r0, r1, r2, r3]
    module
  have nL : ‖Lc‖ ≤ c 0 * ‖L1‖ + (|c 1 - c 0| * ‖a 1‖ + |c 2 - c 0| * ‖a 2‖ + |c 3 - c 0| * ‖a 3‖) := by
    rw [hrel]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hc 0).1]
    · refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) ?_)
      · rw [norm_smul, Real.norm_eq_abs]; rfl
      · rw [norm_smul, Real.norm_eq_abs]; rfl
      · rw [norm_smul, Real.norm_eq_abs]; rfl
  have g1 : _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (fourPlaquette fun i => c i • a i) ≤ 2 * (∑ i, ‖b i‖) ^ 2 + ‖Lc‖ := by
    rw [hP]
    unfold _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne
    have := norm_add_le (((expUnit (b 0) * expUnit (b 1) * expUnit (b 2) * expUnit (b 3) : UnitQuaternion) : ℍ[ℝ]) - 1 - Lc) Lc
    rw [sub_add_cancel] at this
    exact this.trans (add_le_add_left h1 _)
  have g2 : ‖L1‖ ≤ _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (fourPlaquette a) + 2 * s ^ 2 := by
    rw [hP']
    unfold _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne
    have := norm_sub_le (((expUnit (b' 0) * expUnit (b' 1) * expUnit (b' 2) * expUnit (b' 3) : UnitQuaternion) : ℍ[ℝ]) - 1)
      (((expUnit (b' 0) * expUnit (b' 1) * expUnit (b' 2) * expUnit (b' 3) : UnitQuaternion) : ℍ[ℝ]) - 1 - L1)
    rw [sub_sub_cancel] at this
    exact this.trans (add_le_add_right h2 _)
  have c0 := hc 0
  rw [Fin.sum_univ_four (f := fun i => |c i - c 0| * ‖a i‖)]
  simp only [sub_self, abs_zero, zero_mul, zero_add]
  have h3 := mul_le_mul_of_nonneg_left g2 c0.1
  have h4 : c 0 * (2 * s ^ 2) ≤ 2 * s ^ 2 := by nlinarith [sq_nonneg s, c0.2]
  nlinarith
end YangMills.Construction.ColdStepAtMirrorFrames
end
