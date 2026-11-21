import YangMills.Construction.ColdChainAtEveryLevel.SharesUnderAnIsometryProof
import YangMills.Construction.ClusterExpansionOfAStep.CumulantsOfTheKernelsAtMovedBondsProof
import YangMills.Construction.ClusterExpansionOfAStep.EnergyNearAClassProof
import YangMills.Construction.ColdChainAtEveryLevel.ComplexChartElements
import YangMills.Construction.ColdStepAtMirrorFrames.ChartIsReadOffItsFieldProof
import YangMills.Construction.ColdStepAtMirrorFrames.GaugeOfTheLeastChartForm
import YangMills.Construction.Matrices.UnitaryLogarithmClosedFormProof
import YangMills.Construction.RunningCouplingSlope.AmplitudeOfAMinimumInTwoCharts
import YangMills.Construction.RunningCouplingSlope.AmplitudeUnderAnIsometry
import YangMills.Construction.RunningCouplingSlope.DeterminantOfTheLeftFrame
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology Matrix
namespace YangMills.Construction.RunningCouplingSlope.StepAmplitudeSymmetry
open Filter BlockAverages ColdStepAtMirrorFrames
private theorem imBasis_zero_re : ((imaginaryBasis 0 : imaginaryQuaternions) : ℍ[ℝ]).re = 0 := rfl
private theorem imBasis_one_re : ((imaginaryBasis 1 : imaginaryQuaternions) : ℍ[ℝ]).re = 0 := rfl
private theorem imBasis_two_re : ((imaginaryBasis 2 : imaginaryQuaternions) : ℍ[ℝ]).re = 0 := rfl
private theorem imBasis_zero_imI : ((imaginaryBasis 0 : imaginaryQuaternions) : ℍ[ℝ]).imI = 1 := by simp [imaginaryBasis, toImaginary]
private theorem imBasis_zero_imJ : ((imaginaryBasis 0 : imaginaryQuaternions) : ℍ[ℝ]).imJ = 0 := by simp [imaginaryBasis, toImaginary]
private theorem imBasis_zero_imK : ((imaginaryBasis 0 : imaginaryQuaternions) : ℍ[ℝ]).imK = 0 := by simp [imaginaryBasis, toImaginary]
private theorem imBasis_one_imI : ((imaginaryBasis 1 : imaginaryQuaternions) : ℍ[ℝ]).imI = 0 := by simp [imaginaryBasis, toImaginary]
private theorem imBasis_one_imJ : ((imaginaryBasis 1 : imaginaryQuaternions) : ℍ[ℝ]).imJ = 1 := by simp [imaginaryBasis, toImaginary]
private theorem imBasis_one_imK : ((imaginaryBasis 1 : imaginaryQuaternions) : ℍ[ℝ]).imK = 0 := by simp [imaginaryBasis, toImaginary]
private theorem imBasis_two_imI : ((imaginaryBasis 2 : imaginaryQuaternions) : ℍ[ℝ]).imI = 0 := by simp [imaginaryBasis, toImaginary]
private theorem imBasis_two_imJ : ((imaginaryBasis 2 : imaginaryQuaternions) : ℍ[ℝ]).imJ = 0 := by simp [imaginaryBasis, toImaginary]
private theorem imBasis_two_imK : ((imaginaryBasis 2 : imaginaryQuaternions) : ℍ[ℝ]).imK = 1 := by simp [imaginaryBasis, toImaginary]
private theorem imaginaryCoord_eq_re_mul_star (m : Fin 3) (q : ℍ[ℝ]) :
    imaginaryCoord m q = (((imaginaryBasis m : imaginaryQuaternions) : ℍ[ℝ]) * star q).re := Quaternion.inner_def _ _
private theorem imaginaryCoord_zero_eq_imI (q : ℍ[ℝ]) : imaginaryCoord 0 q = q.imI := by
  rw [imaginaryCoord_eq_re_mul_star]
  simp [Quaternion.re_mul, imBasis_zero_re, imBasis_zero_imI, imBasis_zero_imJ, imBasis_zero_imK]
private theorem imaginaryCoord_one_eq_imJ (q : ℍ[ℝ]) : imaginaryCoord 1 q = q.imJ := by
  rw [imaginaryCoord_eq_re_mul_star]
  simp [Quaternion.re_mul, imBasis_one_re, imBasis_one_imI, imBasis_one_imJ, imBasis_one_imK]
private theorem imaginaryCoord_two_eq_imK (q : ℍ[ℝ]) : imaginaryCoord 2 q = q.imK := by
  rw [imaginaryCoord_eq_re_mul_star]
  simp [Quaternion.re_mul, imBasis_two_re, imBasis_two_imI, imBasis_two_imJ, imBasis_two_imK]
private def imaginaryCoordL (m : Fin 3) : ℍ[ℝ] →L[ℝ] ℝ := innerSL ℝ ((imaginaryBasis m : imaginaryQuaternions) : ℍ[ℝ])
private theorem imaginaryCoordL_apply (m : Fin 3) (q : ℍ[ℝ]) : imaginaryCoordL m q = imaginaryCoord m q := rfl
private theorem imaginaryCoord_coe_real (m : Fin 3) (r : ℝ) : imaginaryCoord m (r : ℍ[ℝ]) = 0 := by
  fin_cases m
  · exact (imaginaryCoord_zero_eq_imI _).trans (by simp)
  · exact (imaginaryCoord_one_eq_imJ _).trans (by simp)
  · exact (imaginaryCoord_two_eq_imK _).trans (by simp)
private theorem eq_re_add_sum_imaginaryCoord (q : ℍ[ℝ]) :
    q = (q.re : ℍ[ℝ]) + ∑ m, imaginaryCoord m q • ((imaginaryBasis m : imaginaryQuaternions) : ℍ[ℝ]) := by
  rw [Fin.sum_univ_three, imaginaryCoord_zero_eq_imI, imaginaryCoord_one_eq_imJ, imaginaryCoord_two_eq_imK]
  ext <;> simp [imBasis_zero_re, imBasis_zero_imI, imBasis_zero_imJ, imBasis_zero_imK, imBasis_one_re, imBasis_one_imI,
    imBasis_one_imJ, imBasis_one_imK, imBasis_two_re, imBasis_two_imI, imBasis_two_imJ, imBasis_two_imK]
private theorem imaginaryCoord_imaginaryBasis (m m' : Fin 3) :
    imaginaryCoord m ((imaginaryBasis m' : imaginaryQuaternions) : ℍ[ℝ]) = (1 : Matrix (Fin 3) (Fin 3) ℝ) m m' := by
  fin_cases m <;> fin_cases m' <;>
    simp [imaginaryCoord_zero_eq_imI, imaginaryCoord_one_eq_imJ, imaginaryCoord_two_eq_imK, imBasis_zero_imI,
      imBasis_zero_imJ, imBasis_zero_imK, imBasis_one_imI, imBasis_one_imJ, imBasis_one_imK, imBasis_two_imI,
      imBasis_two_imJ, imBasis_two_imK]
private theorem unit_mul_coe_mul_inv (g : UnitQuaternion) (r : ℝ) :
    (g : ℍ[ℝ]) * (r : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = (r : ℍ[ℝ]) := by
  have h : (g : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := (Unitary.mem_iff.1 g.2).2
  rw [(Quaternion.coe_commutes r (g : ℍ[ℝ])).symm, mul_assoc, h, mul_one]
private theorem imaginaryCoord_conj (g : UnitQuaternion) (q : ℍ[ℝ]) (m : Fin 3) :
    imaginaryCoord m ((g : ℍ[ℝ]) * q * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])) =
      ∑ m', adjointMatrix g m m' * imaginaryCoord m' q := by
  conv_lhs => rw [eq_re_add_sum_imaginaryCoord q]
  rw [mul_add, add_mul, unit_mul_coe_mul_inv, Finset.mul_sum, Finset.sum_mul, ← imaginaryCoordL_apply, map_add, map_sum,
    imaginaryCoordL_apply, imaginaryCoord_coe_real, zero_add]
  refine Finset.sum_congr rfl fun m' _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, map_smul, imaginaryCoordL_apply, smul_eq_mul, mul_comm]
  rfl
private theorem adjointMatrix_mul (g h : UnitQuaternion) : adjointMatrix (g * h) = adjointMatrix g * adjointMatrix h := by
  ext m m'
  rw [Matrix.mul_apply]
  show imaginaryCoord m (((g * h : UnitQuaternion) : ℍ[ℝ]) * ((imaginaryBasis m' : imaginaryQuaternions) : ℍ[ℝ]) *
    (((g * h)⁻¹ : UnitQuaternion) : ℍ[ℝ])) = _
  have e : ((g * h : UnitQuaternion) : ℍ[ℝ]) * ((imaginaryBasis m' : imaginaryQuaternions) : ℍ[ℝ]) *
      (((g * h)⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
      (g : ℍ[ℝ]) * ((h : ℍ[ℝ]) * ((imaginaryBasis m' : imaginaryQuaternions) : ℍ[ℝ]) * ((h⁻¹ : UnitQuaternion) : ℍ[ℝ])) *
        ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
    rw [mul_inv_rev]
    simp only [Submonoid.coe_mul, mul_assoc]
  rw [e, imaginaryCoord_conj]
  rfl
private theorem adjointMatrix_one : adjointMatrix (1 : UnitQuaternion) = 1 := by
  ext m m'
  show imaginaryCoord m (((1 : UnitQuaternion) : ℍ[ℝ]) * ((imaginaryBasis m' : imaginaryQuaternions) : ℍ[ℝ]) *
    (((1 : UnitQuaternion)⁻¹ : UnitQuaternion) : ℍ[ℝ])) = _
  simp [imaginaryCoord_imaginaryBasis]
private theorem imaginaryCoord_eq_neg_re_mul (m : Fin 3) (q : ℍ[ℝ]) :
    imaginaryCoord m q = - (((imaginaryBasis m : imaginaryQuaternions) : ℍ[ℝ]) * q).re := by
  fin_cases m
  · show imaginaryCoord 0 q = - (((imaginaryBasis 0 : imaginaryQuaternions) : ℍ[ℝ]) * q).re
    rw [imaginaryCoord_zero_eq_imI]
    simp [Quaternion.re_mul, imBasis_zero_re, imBasis_zero_imI, imBasis_zero_imJ, imBasis_zero_imK]
  · show imaginaryCoord 1 q = - (((imaginaryBasis 1 : imaginaryQuaternions) : ℍ[ℝ]) * q).re
    rw [imaginaryCoord_one_eq_imJ]
    simp [Quaternion.re_mul, imBasis_one_re, imBasis_one_imI, imBasis_one_imJ, imBasis_one_imK]
  · show imaginaryCoord 2 q = - (((imaginaryBasis 2 : imaginaryQuaternions) : ℍ[ℝ]) * q).re
    rw [imaginaryCoord_two_eq_imK]
    simp [Quaternion.re_mul, imBasis_two_re, imBasis_two_imI, imBasis_two_imJ, imBasis_two_imK]
private theorem quaternion_re_mul_comm (p q : ℍ[ℝ]) : (p * q).re = (q * p).re := by apply _root_.YangMills.Construction.BlockAverages.GaugedChains.quaternion_re_mul_comm <;> assumption
private theorem adjointMatrix_transpose (g : UnitQuaternion) : (adjointMatrix g)ᵀ = adjointMatrix g⁻¹ := by
  ext m m'
  rw [Matrix.transpose_apply]
  show imaginaryCoord m' ((g : ℍ[ℝ]) * ((imaginaryBasis m : imaginaryQuaternions) : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])) =
    imaginaryCoord m (((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) * ((imaginaryBasis m' : imaginaryQuaternions) : ℍ[ℝ]) *
      ((g⁻¹⁻¹ : UnitQuaternion) : ℍ[ℝ]))
  rw [imaginaryCoord_eq_neg_re_mul, imaginaryCoord_eq_neg_re_mul, inv_inv, neg_inj]
  set u := ((imaginaryBasis m : imaginaryQuaternions) : ℍ[ℝ])
  set v := ((imaginaryBasis m' : imaginaryQuaternions) : ℍ[ℝ])
  set a := (g : ℍ[ℝ])
  set b := ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])
  calc (v * (a * u * b)).re = (v * (a * u) * b).re := by rw [mul_assoc v]
    _ = (b * (v * (a * u))).re := quaternion_re_mul_comm _ _
    _ = ((b * v * a) * u).re := by simp only [mul_assoc]
    _ = (u * (b * v * a)).re := quaternion_re_mul_comm _ _
private theorem adjointMatrix_orthogonal (g : UnitQuaternion) : (adjointMatrix g)ᵀ * adjointMatrix g = 1 := by
  rw [adjointMatrix_transpose, ← adjointMatrix_mul, inv_mul_cancel, adjointMatrix_one]
private theorem imaginaryCoord_unit_inv (g : UnitQuaternion) (m : Fin 3) :
    imaginaryCoord m ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = - imaginaryCoord m (g : ℍ[ℝ]) := by
  have e : ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = star (g : ℍ[ℝ]) := rfl
  rw [e]
  fin_cases m
  · exact (imaginaryCoord_zero_eq_imI _).trans (by simp [imaginaryCoord_zero_eq_imI])
  · exact (imaginaryCoord_one_eq_imJ _).trans (by simp [imaginaryCoord_one_eq_imJ])
  · exact (imaginaryCoord_two_eq_imK _).trans (by simp [imaginaryCoord_two_eq_imK])
private theorem unit_eq_of_imaginaryCoord_eq {p q : UnitQuaternion}
    (h : ∀ m, imaginaryCoord m (p : ℍ[ℝ]) = imaginaryCoord m (q : ℍ[ℝ]))
    (hp : 0 < (p : ℍ[ℝ]).re) (hq : 0 < (q : ℍ[ℝ]).re) : p = q := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  rw [imaginaryCoord_zero_eq_imI, imaginaryCoord_zero_eq_imI] at h0
  rw [imaginaryCoord_one_eq_imJ, imaginaryCoord_one_eq_imJ] at h1
  rw [imaginaryCoord_two_eq_imK, imaginaryCoord_two_eq_imK] at h2
  have e : (p : ℍ[ℝ]) = q := by
    refine QuaternionLogarithm.eq_of_imPart_eq_of_re_pos p.2 q.2 ?_ hp hq
    ext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  exact Subtype.ext e
private theorem blockPermMatrix_orthogonal_aux {B : Type} [Fintype B] [DecidableEq B] (β : B ≃ B)
    (O : B → Matrix (Fin 3) (Fin 3) ℝ) (hO : ∀ b, (O b)ᵀ * O b = 1) :
    (Matrix.of fun (p q : B × Fin 3) => if p.1 = β q.1 then O q.1 p.2 q.2 else (0 : ℝ))ᵀ *
      (Matrix.of fun (p q : B × Fin 3) => if p.1 = β q.1 then O q.1 p.2 q.2 else (0 : ℝ)) = 1 := by
  ext ⟨b, m₁⟩ ⟨b', m₂⟩
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [Matrix.transpose_apply, Matrix.of_apply]
  rw [Finset.sum_eq_single (β b)]
  · by_cases h : b = b'
    · subst h
      have e := congrFun (congrFun (hO b) m₁) m₂
      rw [Matrix.mul_apply] at e
      simp only [Matrix.transpose_apply] at e
      simp only [if_true, e, Matrix.one_apply, Prod.mk.injEq, true_and]
    · have hne : β b ≠ β b' := fun e => h (β.injective e)
      simp [hne, h]
  · intro c _ hc
    simp [hc]
  · simp
private theorem exp_mul_exp_neg_self (w : ℍ[ℝ]) : NormedSpace.exp w * NormedSpace.exp (-w) = 1 := by apply _root_.YangMills.Construction.QuaternionLogarithm.exp_mul_exp_neg <;> assumption
private def linkVariation (w T : ℍ[ℝ]) (u : ℍ[ℝ] × ℍ[ℝ] × ℍ[ℝ]) : ℍ[ℝ] :=
  NormedSpace.exp u.1 * NormedSpace.exp (w + u.2.1) * T * NormedSpace.exp (-u.2.2) * star T * NormedSpace.exp (-w)
private theorem contDiff_linkVariation (w T : ℍ[ℝ]) : ContDiff ℝ 2 (linkVariation w T) := by
  have e : ContDiff ℝ 2 (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) := QuaternionLog.contDiff_quaternionExp
  have h1 : ContDiff ℝ 2 fun u : ℍ[ℝ] × ℍ[ℝ] × ℍ[ℝ] => NormedSpace.exp u.1 := e.comp contDiff_fst
  have h2 : ContDiff ℝ 2 fun u : ℍ[ℝ] × ℍ[ℝ] × ℍ[ℝ] => NormedSpace.exp (w + u.2.1) :=
    e.comp (contDiff_const.add (contDiff_fst.comp contDiff_snd))
  have h3 : ContDiff ℝ 2 fun u : ℍ[ℝ] × ℍ[ℝ] × ℍ[ℝ] => NormedSpace.exp (-u.2.2) :=
    e.comp (contDiff_snd.comp contDiff_snd).neg
  exact ((((h1.mul h2).mul contDiff_const).mul h3).mul contDiff_const).mul contDiff_const
private theorem linkVariation_zero {w T : ℍ[ℝ]} (hT : T * star T = 1) : linkVariation w T 0 = 1 := by
  have e0 : (0 : ℍ[ℝ] × ℍ[ℝ] × ℍ[ℝ]).2.1 = 0 := rfl
  have e1 : (0 : ℍ[ℝ] × ℍ[ℝ] × ℍ[ℝ]).2.2 = 0 := rfl
  have e2 : (0 : ℍ[ℝ] × ℍ[ℝ] × ℍ[ℝ]).1 = 0 := rfl
  unfold linkVariation
  rw [e0, e1, e2, neg_zero, NormedSpace.exp_zero, add_zero, one_mul, mul_one, mul_assoc _ T, hT, mul_one,
    exp_mul_exp_neg_self]
private theorem fderiv_linkVariation {w T : ℍ[ℝ]} (hT : T * star T = 1) (u : ℍ[ℝ] × ℍ[ℝ] × ℍ[ℝ]) :
    fderiv ℝ (linkVariation w T) 0 u = u.1 + fderiv ℝ NormedSpace.exp w u.2.1 * NormedSpace.exp (-w) -
      (NormedSpace.exp w * T) * u.2.2 * (star T * NormedSpace.exp (-w)) := by
  have hd : DifferentiableAt ℝ (linkVariation w T) 0 := (contDiff_linkVariation w T).differentiable (by norm_num) 0
  have hexp : ∀ q : ℍ[ℝ], DifferentiableAt ℝ (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) q := fun q =>
    (QuaternionLog.contDiff_quaternionExp (k := 1)).differentiable (by norm_num) q
  have h0 : HasFDerivAt (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) (1 : ℍ[ℝ] →L[ℝ] ℍ[ℝ]) 0 := hasFDerivAt_exp_zero
  have line : ∀ (q : ℍ[ℝ]), HasDerivAt (fun s : ℝ => s • q) q 0 := fun q => by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const q
  have h1 : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • u.1)) u.1 0 := by
    have := HasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) (f := fun s : ℝ => s • u.1)
      (by simpa using h0) (line u.1)
    exact this
  have h2 : HasDerivAt (fun s : ℝ => NormedSpace.exp (w + s • u.2.1)) (fderiv ℝ NormedSpace.exp w u.2.1) 0 := by
    have l : HasDerivAt (fun s : ℝ => w + s • u.2.1) u.2.1 0 := (line u.2.1).const_add w
    have := HasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) (f := fun s : ℝ => w + s • u.2.1)
      (by simpa using (hexp w).hasFDerivAt) l
    exact this
  have h3 : HasDerivAt (fun s : ℝ => NormedSpace.exp (-(s • u.2.2))) (-u.2.2) 0 := by
    have l : HasDerivAt (fun s : ℝ => -(s • u.2.2)) (-u.2.2) 0 := (line u.2.2).neg
    have := HasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) (f := fun s : ℝ => -(s • u.2.2))
      (by simpa using h0) l
    exact this
  have hp := ((((h1.mul h2).mul_const T).mul h3).mul_const (star T)).mul_const (NormedSpace.exp (-w))
  have hl : HasDerivAt (fun s : ℝ => s • u) u 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const u
  have hc := HasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) (f := fun s : ℝ => s • u)
    (by simpa using hd.hasFDerivAt) hl
  have := hc.unique hp
  rw [this]
  simp only [zero_smul, add_zero, neg_zero, NormedSpace.exp_zero, one_mul, mul_one, Pi.mul_apply]
  have hw := exp_mul_exp_neg_self w
  set E := NormedSpace.exp w
  set E' := NormedSpace.exp (-w)
  set D := fderiv ℝ NormedSpace.exp w u.2.1
  have hTE : T * (star T * E') = E' := by rw [← mul_assoc, hT, one_mul]
  simp only [add_mul, mul_neg, neg_mul, mul_assoc, hTE, hw, mul_one, sub_eq_add_neg]
private def linkCoords {E B : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (w T : B → ℍ[ℝ])
    (L : B → E →L[ℝ] ℍ[ℝ] × ℍ[ℝ] × ℍ[ℝ]) (e : E) : B × Fin 3 → ℝ :=
  fun p => imaginaryCoord p.2 (linkVariation (w p.1) (T p.1) (L p.1 e))
section LinkCoords
variable {E B : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype B]
  {w T : B → ℍ[ℝ]} {L : B → E →L[ℝ] ℍ[ℝ] × ℍ[ℝ] × ℍ[ℝ]}
private theorem contDiff_linkCoords : ContDiff ℝ 2 (linkCoords w T L) :=
  contDiff_pi.2 fun p =>
    (imaginaryCoordL p.2).contDiff.comp ((contDiff_linkVariation (w p.1) (T p.1)).comp (L p.1).contDiff)
omit [Fintype B] in
private theorem linkCoords_zero (hT : ∀ b, T b * star (T b) = 1) : linkCoords w T L 0 = 0 := by
  funext p
  simp only [linkCoords, map_zero, linkVariation_zero (hT p.1), Pi.zero_apply]
  exact imaginaryCoord_coe_real p.2 1
private theorem fderiv_linkCoords (e : E) (p : B × Fin 3) :
    fderiv ℝ (linkCoords w T L) 0 e p =
      imaginaryCoord p.2 (fderiv ℝ (linkVariation (w p.1) (T p.1)) 0 (L p.1 e)) := by
  have hd : DifferentiableAt ℝ (linkCoords w T L) 0 := (contDiff_linkCoords).differentiable (by norm_num) 0
  have h1 := hasFDerivAt_pi'.1 hd.hasFDerivAt p
  have hb : HasFDerivAt (linkVariation (w p.1) (T p.1)) (fderiv ℝ (linkVariation (w p.1) (T p.1)) 0) (L p.1 0) := by
    rw [map_zero]
    exact ((contDiff_linkVariation _ _).differentiable (by norm_num) 0).hasFDerivAt
  have h2 := (imaginaryCoordL p.2).hasFDerivAt.comp (0 : E) (hb.comp (0 : E) (L p.1).hasFDerivAt)
  have := h1.unique h2
  have e2 := congrArg (fun l => l e) this
  simpa [imaginaryCoordL_apply] using e2
end LinkCoords
section Coordinates
variable {F : BlockFrame}
open Classical
private theorem expUnit_zero_eq_one : expUnit 0 = 1 := Subtype.ext (by simp [expUnit])
private theorem unit_mul_star_self (g : UnitQuaternion) : (g : ℍ[ℝ]) * star (g : ℍ[ℝ]) = 1 := (Unitary.mem_iff.1 g.2).2
private theorem coe_unit_inv (g : UnitQuaternion) : ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = star (g : ℍ[ℝ]) := rfl
private theorem coe_expUnit_inv (w : imaginaryQuaternions) :
    (((expUnit w)⁻¹ : UnitQuaternion) : ℍ[ℝ]) = NormedSpace.exp (-(w : ℍ[ℝ])) := by apply _root_.YangMills.Construction.KernelCumulants.coe_inv_expUnit <;> assumption
open Classical in
private def crossingTop (V : F.GaugeField F.top) (x : F.Site F.depth) (i : Fin 4) : UnitQuaternion :=
  if IsCrossingBond (x, i) then V (enclosingCell x) i else 1
private theorem chartedField_eq_expUnit_mul {w : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (hw : ∀ b, IsAxialTreeBond b → w b.1 b.2 = 0)
    (V : F.GaugeField F.top) (x : F.Site F.depth) (i : Fin 4) :
    chartedField w V x i = expUnit (w x i) * crossingTop V x i := by
  unfold chartedField crossingTop
  by_cases h : IsCrossingBond (x, i)
  · simp [h]
  · by_cases ht : IsAxialTreeBond (x, i)
    · have := hw (x, i) ht
      simp only at this
      simp [h, ht, this, expUnit_zero_eq_one]
    · simp [h, ht]
private theorem not_mem_chordBonds_of_tree {S : Finset F.Cell} {b : F.Site F.depth × Fin 4} (h : IsAxialTreeBond b) :
    b ∉ chordBonds S := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood.not_mem_chordBonds_of_tree <;> assumption
private theorem stepCoordinates_of_tree (η : StepVariable (finiteCells F)) {b : F.Site F.depth × Fin 4}
    (h : IsAxialTreeBond b) : stepCoordinates η b.1 b.2 = 0 := by
  unfold stepCoordinates
  rw [dif_neg (not_mem_chordBonds_of_tree h)]
private theorem stepCoordinates_zero_var (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (0 : StepVariable (finiteCells F)) x i = 0 := by
  unfold stepCoordinates
  split_ifs
  · exact BondCoordinates.toImaginary_zero
  · rfl
private theorem coordsAboveFrame_eq_add (a ρ : ℝ) (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)) :
    coordsAboveFrame true a ρ 0 V η = fun x i => coordsAboveFrame true a ρ 0 V 0 x i + stepCoordinates η x i := by
  funext x i
  simp only [coordsAboveFrame, stepCoordinates_zero_var, add_zero]
private def bondCoordL (b : F.Site F.depth × Fin 4) : StepVariable (finiteCells F) →L[ℝ] ℍ[ℝ] :=
  open Classical in
  if h : b ∈ chordBonds (finiteCells F) then
    QuaternionLogarithm.imaginaryCLM.comp (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : ↥(chordBonds (finiteCells F)) => EuclideanSpace ℝ (Fin 3)) ⟨b, h⟩)
  else 0
private theorem bondCoordL_apply (b : F.Site F.depth × Fin 4) (η : StepVariable (finiteCells F)) :
    bondCoordL b η = ((stepCoordinates η b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ]) := by
  obtain ⟨x, i⟩ := b
  unfold bondCoordL stepCoordinates
  by_cases h : (x, i) ∈ chordBonds (finiteCells F)
  · simp only [dif_pos h]
    rfl
  · simp only [dif_neg h]
    rfl
private def extendByZeroAtCentres (z : OffCentreComponent F F.depth F.top → ℝ) (s : SiteComponent F F.depth) : ℝ :=
  open Classical in
  if h : ¬ IsBlockCentre F.top s.1.1 then z ⟨s, h⟩ else 0
private def gaugeGenerator (z : OffCentreComponent F F.depth F.top → ℝ) (y : F.Site F.depth) : imaginaryQuaternions :=
  ∑ m, siteTangent (extendByZeroAtCentres z) y m • imaginaryBasis m
private theorem coe_gaugeGenerator (z : OffCentreComponent F F.depth F.top → ℝ) (y : F.Site F.depth) :
    ((gaugeGenerator z y : imaginaryQuaternions) : ℍ[ℝ]) =
      ∑ m, siteTangent (extendByZeroAtCentres z) y m • ((imaginaryBasis m : imaginaryQuaternions) : ℍ[ℝ]) := by
  simp [gaugeGenerator]
open Classical in
private theorem siteTangent_extend_add (z z' : OffCentreComponent F F.depth F.top → ℝ) (y : F.Site F.depth) (m : Fin 3) :
    siteTangent (extendByZeroAtCentres (z + z')) y m =
      siteTangent (extendByZeroAtCentres z) y m + siteTangent (extendByZeroAtCentres z') y m := by
  unfold siteTangent extendByZeroAtCentres
  split_ifs <;> simp
open Classical in
private theorem siteTangent_extend_smul (r : ℝ) (z : OffCentreComponent F F.depth F.top → ℝ) (y : F.Site F.depth)
    (m : Fin 3) :
    siteTangent (extendByZeroAtCentres (r • z)) y m = r * siteTangent (extendByZeroAtCentres z) y m := by
  unfold siteTangent extendByZeroAtCentres
  split_ifs <;> simp
private def gaugeGeneratorL (y : F.Site F.depth) : (OffCentreComponent F F.depth F.top → ℝ) →L[ℝ] ℍ[ℝ] :=
  open Classical in
  LinearMap.toContinuousLinearMap
    { toFun := fun z => ((gaugeGenerator z y : imaginaryQuaternions) : ℍ[ℝ])
      map_add' := fun z z' => by
        simp only [coe_gaugeGenerator, siteTangent_extend_add, add_smul, Finset.sum_add_distrib]
      map_smul' := fun r z => by
        simp only [coe_gaugeGenerator, siteTangent_extend_smul, mul_smul, RingHom.id_apply, Finset.smul_sum] }
private theorem gaugeGeneratorL_apply (y : F.Site F.depth) (z : OffCentreComponent F F.depth F.top → ℝ) :
    gaugeGeneratorL y z = ((gaugeGenerator z y : imaginaryQuaternions) : ℍ[ℝ]) := rfl
private def linkMoveL (b : F.Site F.depth × Fin 4) :
    StepVariable (finiteCells F) × (OffCentreComponent F F.depth F.top → ℝ) →L[ℝ] ℍ[ℝ] × ℍ[ℝ] × ℍ[ℝ] :=
  ((gaugeGeneratorL b.1).comp (ContinuousLinearMap.snd ℝ _ _)).prod
    (((bondCoordL b).comp (ContinuousLinearMap.fst ℝ _ _)).prod
      ((gaugeGeneratorL (b.1 + unitStep F.depth b.2)).comp (ContinuousLinearMap.snd ℝ _ _)))
private def chartMoveL (b : F.Site F.depth × Fin 4) : StepVariable (finiteCells F) →L[ℝ] ℍ[ℝ] × ℍ[ℝ] × ℍ[ℝ] :=
  (0 : StepVariable (finiteCells F) →L[ℝ] ℍ[ℝ]).prod ((bondCoordL b).prod 0)
private def linkCoordQuat (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (b : ↥(innerBonds (finiteCells F) F.depth)) : ℍ[ℝ] :=
  ((w b.1.1 b.1.2 : imaginaryQuaternions) : ℍ[ℝ])
private def linkTopQuat (V : F.GaugeField F.top) (b : ↥(innerBonds (finiteCells F) F.depth)) : ℍ[ℝ] :=
  ((crossingTop V b.1.1 b.1.2 : UnitQuaternion) : ℍ[ℝ])
private theorem coe_linkMove_eq (l₁ l₂ u w : imaginaryQuaternions) (T : UnitQuaternion) :
    ((expUnit l₁ * (expUnit (w + u) * T) * (expUnit l₂)⁻¹ * (expUnit w * T)⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
      linkVariation (w : ℍ[ℝ]) (T : ℍ[ℝ]) ((l₁ : ℍ[ℝ]), (u : ℍ[ℝ]), (l₂ : ℍ[ℝ])) := by
  unfold linkVariation
  simp only [mul_inv_rev, Submonoid.coe_mul, coe_expUnit_inv, coe_unit_inv T]
  simp only [mul_assoc]
  rfl
private theorem coe_chartMove_eq (u w : imaginaryQuaternions) (T : UnitQuaternion) :
    ((expUnit (w + u) * T * (expUnit w * T)⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
      linkVariation (w : ℍ[ℝ]) 1 (0, (u : ℍ[ℝ]), 0) := by
  have e : expUnit (w + u) * T * (expUnit w * T)⁻¹ = expUnit (w + u) * (expUnit w)⁻¹ := by group
  rw [e]
  unfold linkVariation
  simp only [Submonoid.coe_mul, coe_expUnit_inv, neg_zero, NormedSpace.exp_zero, one_mul, mul_one, star_one]
  rfl
private theorem gaugeTransform_axialTree {w : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (hw : ∀ b, IsAxialTreeBond b → w b.1 b.2 = 0) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) (z : OffCentreComponent F F.depth F.top → ℝ)
    (b : ↥(innerBonds (finiteCells F) F.depth)) :
    ((_root_.YangMills.Construction.BlockAverages.gaugeTransform (fun y => expUnit (gaugeGenerator z y))
        (chartedField (fun x i => w x i + stepCoordinates η x i) V) b.1.1 b.1.2 *
        (chartedField w V b.1.1 b.1.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
      linkVariation (linkCoordQuat w b) (linkTopQuat V b) (linkMoveL b.1 (η, z)) := by
  have hw' : ∀ c, IsAxialTreeBond c → (fun x i => w x i + stepCoordinates η x i) c.1 c.2 = 0 := fun c hc => by
    show w c.1 c.2 + stepCoordinates η c.1 c.2 = 0
    rw [hw c hc, stepCoordinates_of_tree η hc, add_zero]
  have e : linkMoveL b.1 (η, z) = (((gaugeGenerator z b.1.1 : imaginaryQuaternions) : ℍ[ℝ]),
      ((stepCoordinates η b.1.1 b.1.2 : imaginaryQuaternions) : ℍ[ℝ]),
      ((gaugeGenerator z (b.1.1 + unitStep F.depth b.1.2) : imaginaryQuaternions) : ℍ[ℝ])) := by
    simp [linkMoveL, bondCoordL_apply, gaugeGeneratorL_apply]
  rw [e]
  show ((expUnit (gaugeGenerator z b.1.1) * chartedField (fun x i => w x i + stepCoordinates η x i) V b.1.1 b.1.2 *
    (expUnit (gaugeGenerator z (b.1.1 + unitStep F.depth b.1.2)))⁻¹ * (chartedField w V b.1.1 b.1.2)⁻¹ :
      UnitQuaternion) : ℍ[ℝ]) = _
  rw [chartedField_eq_expUnit_mul hw', chartedField_eq_expUnit_mul hw]
  exact coe_linkMove_eq _ _ _ _ _
private theorem charted_representation {w : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (hw : ∀ b, IsAxialTreeBond b → w b.1 b.2 = 0) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) (b : ↥(innerBonds (finiteCells F) F.depth)) :
    ((chartedField (fun x i => w x i + stepCoordinates η x i) V b.1.1 b.1.2 * (chartedField w V b.1.1 b.1.2)⁻¹ :
        UnitQuaternion) : ℍ[ℝ]) =
      linkVariation (linkCoordQuat w b) 1 (chartMoveL b.1 η) := by
  have hw' : ∀ c, IsAxialTreeBond c → (fun x i => w x i + stepCoordinates η x i) c.1 c.2 = 0 := fun c hc => by
    show w c.1 c.2 + stepCoordinates η c.1 c.2 = 0
    rw [hw c hc, stepCoordinates_of_tree η hc, add_zero]
  have e : chartMoveL b.1 η = (0, ((stepCoordinates η b.1.1 b.1.2 : imaginaryQuaternions) : ℍ[ℝ]), 0) := by
    simp [chartMoveL, bondCoordL_apply]
  rw [e, chartedField_eq_expUnit_mul hw', chartedField_eq_expUnit_mul hw]
  exact coe_chartMove_eq _ _ _
private def stepComponents : StepVariable (finiteCells F) ≃ₗ[ℝ] (ReferenceDensity.ChartCoord F → ℝ) where
  toFun x p := x p.1 p.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun v b := WithLp.toLp 2 fun m => v (b, m)
  left_inv x := by
    funext b
    ext m
    rfl
  right_inv v := by
    funext p
    rfl
private theorem stepComponents_symm_single (i : ReferenceDensity.ChartCoord F) :
    stepComponents.symm (Pi.single i 1) =
      (bondVariation i.1 (EuclideanSpace.single i.2 1) : StepVariable (finiteCells F)) := by
  obtain ⟨c, n⟩ := i
  funext b
  ext m
  show (Pi.single (c, n) (1 : ℝ) : ReferenceDensity.ChartCoord F → ℝ) (b, m) =
    (Pi.single c (EuclideanSpace.single n (1 : ℝ)) : StepVariable (finiteCells F)) b m
  by_cases hb : b = c
  · subst hb
    by_cases hm : m = n
    · subst hm
      simp
    · have : (b, m) ≠ (b, n) := fun h => hm (Prod.ext_iff.1 h).2
      simp [Pi.single_eq_of_ne this, hm]
  · have : (b, m) ≠ (c, n) := fun h => hb (Prod.ext_iff.1 h).1
    simp [Pi.single_eq_of_ne this, Pi.single_eq_of_ne hb]
private theorem imaginaryCoord_toImaginary (v : EuclideanSpace ℝ (Fin 3)) (m : Fin 3) :
    imaginaryCoord m ((toImaginary v : imaginaryQuaternions) : ℍ[ℝ]) = v m := by
  rw [QuaternionLogarithm.coe_toImaginary, QuaternionLogarithm.imaginaryCLM_apply]
  fin_cases m
  · exact imaginaryCoord_zero_eq_imI _
  · exact imaginaryCoord_one_eq_imJ _
  · exact imaginaryCoord_two_eq_imK _
private theorem imaginary_eq_sum (q : imaginaryQuaternions) :
    (q : ℍ[ℝ]) = ∑ m, imaginaryCoord m (q : ℍ[ℝ]) • ((imaginaryBasis m : imaginaryQuaternions) : ℍ[ℝ]) := by
  have h : ((q : ℍ[ℝ]).re : ℍ[ℝ]) = 0 := by
    have : (q : ℍ[ℝ]).re = 0 := q.2
    rw [this]
    rfl
  conv_lhs => rw [eq_re_add_sum_imaginaryCoord (q : ℍ[ℝ]), h, zero_add]
private theorem imaginaryCoord_sum_smul (c : Fin 3 → ℝ) (m : Fin 3) :
    imaginaryCoord m (∑ n, c n • ((imaginaryBasis n : imaginaryQuaternions) : ℍ[ℝ])) = c m := by
  rw [← imaginaryCoordL_apply, map_sum]
  simp only [map_smul, imaginaryCoordL_apply, imaginaryCoord_imaginaryBasis, smul_eq_mul, Matrix.one_apply, mul_ite,
    mul_one, mul_zero]
  simp
private theorem imaginaryCoord_leftExpDifferential (w u : imaginaryQuaternions) (m : Fin 3) :
    imaginaryCoord m (fderiv ℝ NormedSpace.exp (w : ℍ[ℝ]) (u : ℍ[ℝ]) * NormedSpace.exp (-(w : ℍ[ℝ]))) =
      ∑ n, leftExpDifferential w m n * imaginaryCoord n (u : ℍ[ℝ]) := by
  conv_lhs => rw [imaginary_eq_sum u]
  rw [map_sum, Finset.sum_mul, ← imaginaryCoordL_apply, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_smul, smul_mul_assoc, map_smul, imaginaryCoordL_apply, smul_eq_mul, mul_comm]
  rfl
private theorem chartDifferential_mulVec (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (x : StepVariable (finiteCells F)) (p : LinkComponent F F.depth) :
    (chartDifferential w *ᵥ stepComponents x) p =
      ∑ n, leftExpDifferential (w p.1.1.1 p.1.1.2) p.2 n *
        imaginaryCoord n ((stepCoordinates x p.1.1.1 p.1.1.2 : imaginaryQuaternions) : ℍ[ℝ]) := by
  rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  by_cases h : p.1.1 ∈ chordBonds (finiteCells F)
  · rw [Finset.sum_eq_single (⟨p.1.1, h⟩ : ↥(chordBonds (finiteCells F)))]
    · have e : stepCoordinates x p.1.1.1 p.1.1.2 = toImaginary (x ⟨p.1.1, h⟩) := by
        unfold stepCoordinates
        rw [dif_pos h]
      simp only [e, imaginaryCoord_toImaginary]
      refine Finset.sum_congr rfl fun n _ => ?_
      show (if p.1.1 = p.1.1 then leftExpDifferential (w p.1.1.1 p.1.1.2) p.2 n else 0) * x ⟨p.1.1, h⟩ n = _
      rw [if_pos rfl]
    · intro b _ hb
      have : p.1.1 ≠ b.1 := fun e => hb (Subtype.ext e.symm)
      simp [chartDifferential, this]
    · simp
  · have e : stepCoordinates x p.1.1.1 p.1.1.2 = 0 := by
      unfold stepCoordinates
      rw [dif_neg h]
    have e0 : ∀ n : Fin 3, imaginaryCoord n (((0 : imaginaryQuaternions) : ℍ[ℝ])) = 0 := fun n =>
      imaginaryCoord_coe_real n 0
    rw [e]
    simp only [e0, mul_zero, Finset.sum_const_zero]
    refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun n _ => ?_
    have : p.1.1 ≠ b.1 := fun e => h (e ▸ b.2)
    simp [chartDifferential, this]
private theorem gaugeDifferential_mulVec (hsite : ∀ y : F.Site F.depth, y ∈ sitesOfCells (finiteCells F) F.depth)
    (W : F.GaugeField F.depth) (v : SiteComponent F F.depth → ℝ) (p : LinkComponent F F.depth) :
    (gaugeDifferential W *ᵥ v) p = siteTangent v p.1.1.1 p.2 -
      ∑ n, adjointMatrix (W p.1.1.1 p.1.1.2) p.2 n * siteTangent v (p.1.1.1 + unitStep F.depth p.1.1.2) n := by
  have hg : ∀ (y : F.Site F.depth) (n : Fin 3), siteTangent v y n = v (⟨y, hsite y⟩, n) := fun y n => by
    unfold siteTangent
    rw [dif_pos (hsite y)]
  rw [Matrix.mulVec, dotProduct]
  simp only [gaugeDifferential, sub_mul, Finset.sum_sub_distrib]
  congr 1
  · rw [Fintype.sum_prod_type, Finset.sum_eq_single (⟨p.1.1.1, hsite _⟩ : ↥(sitesOfCells (finiteCells F) F.depth))]
    · rw [Finset.sum_eq_single p.2]
      · simp [hg]
      · intro n _ hn
        simp [hn.symm, hn]
      · simp
    · intro y _ hy
      have : y.1 ≠ p.1.1.1 := fun e => hy (Subtype.ext e)
      simp [this]
    · simp
  · rw [Fintype.sum_prod_type, Finset.sum_eq_single
      (⟨p.1.1.1 + unitStep F.depth p.1.1.2, hsite _⟩ : ↥(sitesOfCells (finiteCells F) F.depth))]
    · simp [hg]
    · intro y _ hy
      have : y.1 ≠ p.1.1.1 + unitStep F.depth p.1.1.2 := fun e => hy (Subtype.ext e)
      simp [this]
    · simp
private theorem sum_offCentre (f : SiteComponent F F.depth → ℝ) (hf : ∀ s, IsBlockCentre F.top s.1.1 → f s = 0) :
    ∑ s : OffCentreComponent F F.depth F.top, f s.1 = ∑ s, f s := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun s : SiteComponent F F.depth => ¬ IsBlockCentre F.top s.1.1)
    (by simp) f]
  refine Finset.sum_filter_of_ne fun s _ hs h => hs (hf s h)
private theorem extendByZeroAtCentres_off (z : OffCentreComponent F F.depth F.top → ℝ)
    (s : OffCentreComponent F F.depth F.top) : extendByZeroAtCentres z s.1 = z s := by
  unfold extendByZeroAtCentres
  rw [dif_pos s.2]
private theorem extendByZeroAtCentres_centre (z : OffCentreComponent F F.depth F.top → ℝ) {s : SiteComponent F F.depth}
    (h : IsBlockCentre F.top s.1.1) : extendByZeroAtCentres z s = 0 := by
  unfold extendByZeroAtCentres
  rw [dif_neg (not_not.2 h)]
private theorem offCentreGaugeDifferential_mulVec (W : F.GaugeField F.depth) (z : OffCentreComponent F F.depth F.top → ℝ) :
    offCentreGaugeDifferential W *ᵥ z = gaugeDifferential W *ᵥ extendByZeroAtCentres z := by
  funext p
  rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct,
    ← sum_offCentre (fun s => gaugeDifferential W p s * extendByZeroAtCentres z s) fun s h => by
      simp [extendByZeroAtCentres_centre z h]]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [extendByZeroAtCentres_off]
  rfl
private theorem imaginaryCoord_gaugeGenerator (z : OffCentreComponent F F.depth F.top → ℝ) (y : F.Site F.depth) (m : Fin 3) :
    imaginaryCoord m ((gaugeGenerator z y : imaginaryQuaternions) : ℍ[ℝ]) = siteTangent (extendByZeroAtCentres z) y m := by
  rw [coe_gaugeGenerator, imaginaryCoord_sum_smul]
private theorem linkMoveL_apply (b : F.Site F.depth × Fin 4) (x : StepVariable (finiteCells F))
    (z : OffCentreComponent F F.depth F.top → ℝ) :
    linkMoveL b (x, z) = (((gaugeGenerator z b.1 : imaginaryQuaternions) : ℍ[ℝ]),
      ((stepCoordinates x b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ]),
      ((gaugeGenerator z (b.1 + unitStep F.depth b.2) : imaginaryQuaternions) : ℍ[ℝ])) := by
  simp [linkMoveL, bondCoordL_apply, gaugeGeneratorL_apply]
private theorem chartMoveL_apply (b : F.Site F.depth × Fin 4) (x : StepVariable (finiteCells F)) :
    chartMoveL b x = (0, ((stepCoordinates x b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ]), 0) := by
  simp [chartMoveL, bondCoordL_apply]
private theorem fderiv_gaugeTransform_comp
    (hsite : ∀ y : F.Site F.depth, y ∈ sitesOfCells (finiteCells F) F.depth)
    {w : F.Site F.depth → Fin 4 → imaginaryQuaternions} (hw : ∀ b, IsAxialTreeBond b → w b.1 b.2 = 0)
    (V : F.GaugeField F.top) (x : StepVariable (finiteCells F)) (z : OffCentreComponent F F.depth F.top → ℝ) :
    fderiv ℝ (linkCoords (linkCoordQuat w) (linkTopQuat V) fun b => linkMoveL b.1) 0 (x, z) =
      chartDifferential w *ᵥ stepComponents x + offCentreGaugeDifferential (chartedField w V) *ᵥ z := by
  funext p
  have hT : linkTopQuat V p.1 * star (linkTopQuat V p.1) = 1 := unit_mul_star_self _
  rw [fderiv_linkCoords, fderiv_linkVariation hT, Pi.add_apply, chartDifferential_mulVec,
    offCentreGaugeDifferential_mulVec, gaugeDifferential_mulVec hsite, linkMoveL_apply]
  have hW : (((chartedField w V p.1.1.1 p.1.1.2 : UnitQuaternion) : ℍ[ℝ])) =
      NormedSpace.exp (linkCoordQuat w p.1) * linkTopQuat V p.1 := by
    rw [chartedField_eq_expUnit_mul hw]
    rfl
  have hW' : ((((chartedField w V p.1.1.1 p.1.1.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])) =
      star (linkTopQuat V p.1) * NormedSpace.exp (-(linkCoordQuat w p.1)) := by
    rw [chartedField_eq_expUnit_mul hw, mul_inv_rev, Submonoid.coe_mul, coe_expUnit_inv]
    rfl
  simp only [← hW, ← hW']
  rw [← imaginaryCoordL_apply, map_sub, map_add]
  simp only [imaginaryCoordL_apply]
  rw [imaginaryCoord_gaugeGenerator, imaginaryCoord_conj]
  simp only [imaginaryCoord_gaugeGenerator]
  have e := imaginaryCoord_leftExpDifferential (w p.1.1.1 p.1.1.2) (stepCoordinates x p.1.1.1 p.1.1.2) p.2
  rw [show linkCoordQuat w p.1 = ((w p.1.1.1 p.1.1.2 : imaginaryQuaternions) : ℍ[ℝ]) from rfl, e]
  ring
private theorem fderiv_charted_comp {w : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (x : StepVariable (finiteCells F)) :
    fderiv ℝ (linkCoords (linkCoordQuat w) (fun _ => 1) fun b => chartMoveL b.1) 0 x =
      chartDifferential w *ᵥ stepComponents x := by
  funext p
  have hT : (1 : ℍ[ℝ]) * star (1 : ℍ[ℝ]) = 1 := by simp
  rw [fderiv_linkCoords, fderiv_linkVariation hT, chartDifferential_mulVec, chartMoveL_apply]
  simp only [mul_zero, zero_mul, sub_zero, zero_add]
  exact imaginaryCoord_leftExpDifferential _ _ _
end Coordinates
section Symmetry
variable {F : BlockFrame}
private theorem siteCoords_cast_self {j : ℕ} (x : F.Site j) (i : Fin 4) :
    ((siteCoords x i : ℤ) : ZMod (F.period j i)) = x i := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.siteCoords_cast <;> assumption
private theorem sign_mul_self {g : CubicSymmetry} (hg : g.IsSymmetry F) (i : Fin 4) : g.sign i * g.sign i = 1 := by
  rcases hg.1 i with h | h <;> rw [h] <;> norm_num
private theorem inverse_actSite {g : CubicSymmetry} (hg : g.IsSymmetry F) (j : ℕ) (x : F.Site j) :
    (EnergySymmetry.symmetryInverse g).actSite j (g.actSite j x) = x := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.symmInv_actSite <;> assumption
private theorem symmetryInverse_isSymmetry {g : CubicSymmetry} (hg : g.IsSymmetry F) :
    (EnergySymmetry.symmetryInverse g).IsSymmetry F := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.symmInv_isSymmetry <;> assumption
private theorem actSite_injective {g : CubicSymmetry} (hg : g.IsSymmetry F) (j : ℕ) :
    Function.Injective (g.actSite (F := F) j) :=
  Function.LeftInverse.injective (inverse_actSite hg j)
private theorem actSite_cellCentre {g : CubicSymmetry} (hg : g.IsSymmetry F) {j : ℕ} (hj : j ≤ F.top) (z : F.Cell) :
    g.actSite j (cellCentre j z) = cellCentre j (g.actSite F.top z) := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.actSite_cellCentre <;> assumption
private theorem actSite_add_unitStep_of_pos {g : CubicSymmetry} (hg : g.IsSymmetry F) {j : ℕ} (y : F.Site j) {i : Fin 4}
    (hs : g.sign (g.perm.symm i) = 1) :
    g.actSite j (y + unitStep j i) = g.actSite j y + unitStep j (g.perm.symm i) := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.actSite_add_unitStep_of_pos <;> assumption
private theorem actSite_add_unitStep_of_neg {g : CubicSymmetry} (hg : g.IsSymmetry F) {j : ℕ} (y : F.Site j) {i : Fin 4}
    (hs : g.sign (g.perm.symm i) = -1) :
    g.actSite j (y + unitStep j i) = g.actSite j y - unitStep j (g.perm.symm i) := by apply _root_.YangMills.Construction.BlockAverages.SymmetryTransport.actSite_add_unitStep_of_neg <;> assumption
open Classical
private theorem isBlockCentre_actSite_iff {g : CubicSymmetry} (hg : g.IsSymmetry F) (y : F.Site F.depth) :
    IsBlockCentre F.top (g.actSite F.depth y) ↔ IsBlockCentre F.top y := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨(EnergySymmetry.symmetryInverse g).actSite F.top z, ?_⟩
    have h1 := actSite_cellCentre (symmetryInverse_isSymmetry hg) (Nat.le_succ F.depth) z
    have h2 : g.actSite F.depth y = cellCentre F.depth z := hz
    have h3 := inverse_actSite hg F.depth y
    rw [h2, h1] at h3
    exact h3.symm
  · rintro ⟨z, hz⟩
    refine ⟨g.actSite F.top z, ?_⟩
    have h2 : y = cellCentre F.depth z := hz
    rw [h2]
    exact actSite_cellCentre hg (Nat.le_succ F.depth) z
private def bondImage (g : CubicSymmetry) (c : F.Site F.depth × Fin 4) : F.Site F.depth × Fin 4 :=
  if g.sign (g.perm.symm c.2) = 1 then (g.actSite F.depth c.1, g.perm.symm c.2)
  else (g.actSite F.depth c.1 - unitStep F.depth (g.perm.symm c.2), g.perm.symm c.2)
private theorem bondImage_of_pos {g : CubicSymmetry} {c : F.Site F.depth × Fin 4} (hs : g.sign (g.perm.symm c.2) = 1) :
    bondImage g c = (g.actSite F.depth c.1, g.perm.symm c.2) := by
  unfold bondImage
  rw [if_pos hs]
private theorem bondImage_of_neg {g : CubicSymmetry} (hg : g.IsSymmetry F) {c : F.Site F.depth × Fin 4}
    (hs : g.sign (g.perm.symm c.2) = -1) :
    bondImage g c = (g.actSite F.depth (c.1 + unitStep F.depth c.2), g.perm.symm c.2) := by
  have hne : ¬ g.sign (g.perm.symm c.2) = 1 := by
    rw [hs]
    norm_num
  unfold bondImage
  rw [if_neg hne, actSite_add_unitStep_of_neg hg _ hs]
private theorem bondImage_injective {g : CubicSymmetry} (hg : g.IsSymmetry F) :
    Function.Injective (bondImage (F := F) g) := by
  rintro ⟨y, k⟩ ⟨y', k'⟩ h
  have h2 : (bondImage g (y, k)).2 = (bondImage g (y', k')).2 := congrArg Prod.snd h
  have e2 : ∀ c : F.Site F.depth × Fin 4, (bondImage g c).2 = g.perm.symm c.2 := fun c => by
    unfold bondImage
    split_ifs <;> rfl
  rw [e2, e2] at h2
  have hk : k = k' := g.perm.symm.injective h2
  subst hk
  have h1 : (bondImage g (y, k)).1 = (bondImage g (y', k)).1 := congrArg Prod.fst h
  have hy : y = y' := by
    refine actSite_injective hg F.depth ?_
    unfold bondImage at h1
    simp only at h1
    split_ifs at h1
    · exact h1
    · exact sub_left_injective h1
  rw [hy]
private def blockPermMatrix {B : Type} [DecidableEq B] (β : B ≃ B) (O : B → Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix (B × Fin 3) (B × Fin 3) ℝ :=
  Matrix.of fun p q => if p.1 = β q.1 then O q.1 p.2 q.2 else (0 : ℝ)
private theorem blockPermMatrix_orthogonal {B : Type} [Fintype B] [DecidableEq B] (β : B ≃ B)
    (O : B → Matrix (Fin 3) (Fin 3) ℝ) (hO : ∀ b, (O b)ᵀ * O b = 1) :
    (blockPermMatrix β O)ᵀ * blockPermMatrix β O = 1 :=
  blockPermMatrix_orthogonal_aux β O hO
private theorem blockPermMatrix_mulVec {B : Type} [Fintype B] [DecidableEq B] (β : B ≃ B)
    (O : B → Matrix (Fin 3) (Fin 3) ℝ) (v : B × Fin 3 → ℝ) (b : B) (m : Fin 3) :
    (blockPermMatrix β O *ᵥ v) (β b, m) = ∑ n, O b m n * v (b, n) := by
  rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Finset.sum_eq_single b]
  · simp [blockPermMatrix]
  · intro c _ hc
    have : β b ≠ β c := fun e => hc (β.injective e).symm
    simp [blockPermMatrix, this]
  · simp
private def bondRotation (g : CubicSymmetry) (γ : F.Site F.depth → UnitQuaternion) (W : F.GaugeField F.depth)
    (c : F.Site F.depth × Fin 4) : Matrix (Fin 3) (Fin 3) ℝ :=
  if g.sign (g.perm.symm c.2) = 1 then adjointMatrix (γ (bondImage g c).1)⁻¹
  else - adjointMatrix ((γ (bondImage g c).1)⁻¹ * (W c.1 c.2)⁻¹)
private theorem bondRotation_orthogonal (g : CubicSymmetry) (γ : F.Site F.depth → UnitQuaternion)
    (W : F.GaugeField F.depth) (c : F.Site F.depth × Fin 4) :
    (bondRotation g γ W c)ᵀ * bondRotation g γ W c = 1 := by
  unfold bondRotation
  split_ifs
  · exact adjointMatrix_orthogonal _
  · rw [Matrix.transpose_neg, neg_mul_neg]
    exact adjointMatrix_orthogonal _
section Transport
variable {g : CubicSymmetry} (hg : g.IsSymmetry F)
  (h3 : ∀ (W : F.GaugeField F.depth) (x : F.Site F.depth) (k : Fin 4),
    linkValue (EnergySymmetry.transportField g W) (g.actSite F.depth x) (g.actStep k) = W x k)
include h3
private theorem transportField_bondImage_of_pos (C : F.GaugeField F.depth) {c : F.Site F.depth × Fin 4}
    (hs : g.sign (g.perm.symm c.2) = 1) :
    EnergySymmetry.transportField g C (bondImage g c).1 (bondImage g c).2 = C c.1 c.2 := by
  have := h3 C c.1 c.2
  rw [bondImage_of_pos hs]
  simpa [linkValue, CubicSymmetry.actStep, hs] using this
private theorem transportField_bondImage_of_neg (C : F.GaugeField F.depth) {c : F.Site F.depth × Fin 4}
    (hs : g.sign (g.perm.symm c.2) = -1) :
    EnergySymmetry.transportField g C (bondImage g c).1 (bondImage g c).2 = (C c.1 c.2)⁻¹ := by
  have := h3 C c.1 c.2
  have hne : ¬ g.sign (g.perm.symm c.2) = 1 := by
    rw [hs]
    norm_num
  have e : bondImage g c = (g.actSite F.depth c.1 - unitStep F.depth (g.perm.symm c.2), g.perm.symm c.2) := by
    unfold bondImage
    rw [if_neg hne]
  rw [e]
  simp only [linkValue, CubicSymmetry.actStep, hne, decide_false, Bool.false_eq_true, if_false] at this
  rw [← this, inv_inv]
end Transport
private theorem re_unit_conj (κ : UnitQuaternion) (q : ℍ[ℝ]) :
    ((κ : ℍ[ℝ]) * q * ((κ⁻¹ : UnitQuaternion) : ℍ[ℝ])).re = q.re := by apply _root_.YangMills.Construction.GaugedCriticality.re_conj_unit <;> assumption
private theorem transport_coordinates {g : CubicSymmetry} (hg : g.IsSymmetry F)
    (h3 : ∀ (W : F.GaugeField F.depth) (x : F.Site F.depth) (k : Fin 4),
      linkValue (EnergySymmetry.transportField g W) (g.actSite F.depth x) (g.actStep k) = W x k)
    {W W' : F.GaugeField F.depth} {γ : F.Site F.depth → UnitQuaternion}
    (hγ : EnergySymmetry.transportField g W = _root_.YangMills.Construction.BlockAverages.gaugeTransform γ W') (C : F.GaugeField F.depth)
    (c : F.Site F.depth × Fin 4) :
    (∀ m, imaginaryCoord m ((_root_.YangMills.Construction.BlockAverages.gaugeTransform (fun y => (γ y)⁻¹) (EnergySymmetry.transportField g C)
        (bondImage g c).1 (bondImage g c).2 * (W' (bondImage g c).1 (bondImage g c).2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
        ∑ n, bondRotation g γ W c m n * imaginaryCoord n ((C c.1 c.2 * (W c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])) ∧
    ((_root_.YangMills.Construction.BlockAverages.gaugeTransform (fun y => (γ y)⁻¹) (EnergySymmetry.transportField g C) (bondImage g c).1 (bondImage g c).2 *
        (W' (bondImage g c).1 (bondImage g c).2)⁻¹ : UnitQuaternion) : ℍ[ℝ]).re =
      ((C c.1 c.2 * (W c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]).re := by
  set x' := (bondImage g c).1
  set i := (bondImage g c).2
  have hW : W' x' i = (γ x')⁻¹ * EnergySymmetry.transportField g W x' i * γ (x' + unitStep F.depth i) := by
    rw [hγ]
    simp only [gaugeTransform]
    group
  have hB : _root_.YangMills.Construction.BlockAverages.gaugeTransform (fun y => (γ y)⁻¹) (EnergySymmetry.transportField g C) x' i =
      (γ x')⁻¹ * EnergySymmetry.transportField g C x' i * γ (x' + unitStep F.depth i) := by
    simp only [_root_.YangMills.Construction.BlockAverages.gaugeTransform, inv_inv]
  rcases hg.1 (g.perm.symm c.2) with hs | hs
  · have e1 : EnergySymmetry.transportField g C x' i = C c.1 c.2 := transportField_bondImage_of_pos h3 C hs
    have e2 : EnergySymmetry.transportField g W x' i = W c.1 c.2 := transportField_bondImage_of_pos h3 W hs
    have e : gaugeTransform (fun y => (γ y)⁻¹) (EnergySymmetry.transportField g C) x' i * (W' x' i)⁻¹ =
        (γ x')⁻¹ * (C c.1 c.2 * (W c.1 c.2)⁻¹) * ((γ x')⁻¹)⁻¹ := by
      rw [hB, hW, e1, e2]
      group
    rw [e, Submonoid.coe_mul, Submonoid.coe_mul]
    refine ⟨fun m => ?_, re_unit_conj _ _⟩
    rw [imaginaryCoord_conj]
    unfold bondRotation
    rw [if_pos hs]
  · have e1 : EnergySymmetry.transportField g C x' i = (C c.1 c.2)⁻¹ := transportField_bondImage_of_neg h3 C hs
    have e2 : EnergySymmetry.transportField g W x' i = (W c.1 c.2)⁻¹ := transportField_bondImage_of_neg h3 W hs
    have e : gaugeTransform (fun y => (γ y)⁻¹) (EnergySymmetry.transportField g C) x' i * (W' x' i)⁻¹ =
        ((γ x')⁻¹ * (W c.1 c.2)⁻¹) * (C c.1 c.2 * (W c.1 c.2)⁻¹)⁻¹ * ((γ x')⁻¹ * (W c.1 c.2)⁻¹)⁻¹ := by
      rw [hB, hW, e1, e2]
      group
    rw [e, Submonoid.coe_mul, Submonoid.coe_mul]
    refine ⟨fun m => ?_, ?_⟩
    · rw [imaginaryCoord_conj]
      unfold bondRotation
      rw [if_neg (by rw [hs]; norm_num)]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [imaginaryCoord_unit_inv, Matrix.neg_apply]
      ring
    · rw [re_unit_conj, coe_unit_inv]
      simp
      ring
private def sitePermutation (g : CubicSymmetry) (hg : g.IsSymmetry F)
    (hsite : ∀ y : F.Site F.depth, y ∈ sitesOfCells (finiteCells F) F.depth) :
    ↥(sitesOfCells (finiteCells F) F.depth) ≃ ↥(sitesOfCells (finiteCells F) F.depth) :=
  Equiv.ofBijective (fun s => ⟨g.actSite F.depth s.1, hsite _⟩)
    (Finite.injective_iff_bijective.1 fun s s' h => Subtype.ext (actSite_injective hg F.depth (congrArg Subtype.val h)))
private def bondPermutation (g : CubicSymmetry) (hg : g.IsSymmetry F)
    (hall : ∀ c : F.Site F.depth × Fin 4, c ∈ innerBonds (finiteCells F) F.depth) :
    ↥(innerBonds (finiteCells F) F.depth) ≃ ↥(innerBonds (finiteCells F) F.depth) :=
  Equiv.ofBijective (fun b => ⟨bondImage g b.1, hall _⟩)
    (Finite.injective_iff_bijective.1 fun s s' h => Subtype.ext (bondImage_injective hg (congrArg Subtype.val h)))
private theorem matrix_identity_pos (K A P Q : Matrix (Fin 3) (Fin 3) ℝ) (a d : Fin 3 → ℝ) (h : P * Q = K * A)
    (m : Fin 3) :
    ∑ n, K m n * (a n - ∑ l, A n l * d l) = ∑ n, K m n * a n - ∑ n, P m n * ∑ l, Q n l * d l := by
  have : K *ᵥ (a - A *ᵥ d) = K *ᵥ a - P *ᵥ (Q *ᵥ d) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]
  exact congrFun this m
private theorem matrix_identity_neg (K A Q P G : Matrix (Fin 3) (Fin 3) ℝ) (a d : Fin 3 → ℝ) (h1 : K * A = Q)
    (h2 : P * G = K) (m : Fin 3) :
    ∑ n, (-K) m n * (a n - ∑ l, A n l * d l) = ∑ n, Q m n * d n - ∑ n, P m n * ∑ l, G n l * a l := by
  have : (-K) *ᵥ (a - A *ᵥ d) = Q *ᵥ d - P *ᵥ (G *ᵥ a) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h2, Matrix.neg_mul, h1, Matrix.neg_mulVec,
      Matrix.neg_mulVec]
    abel
  exact congrFun this m
section Rotations
variable {g : CubicSymmetry} (hg : g.IsSymmetry F)
  (hsite : ∀ y : F.Site F.depth, y ∈ sitesOfCells (finiteCells F) F.depth)
  (hall : ∀ c : F.Site F.depth × Fin 4, c ∈ innerBonds (finiteCells F) F.depth)
  (γ : F.Site F.depth → UnitQuaternion)
private def gaugeRotation : Matrix (SiteComponent F F.depth) (SiteComponent F F.depth) ℝ :=
  blockPermMatrix (sitePermutation g hg hsite) fun s => adjointMatrix (γ (g.actSite F.depth s.1))⁻¹
private def linkRotation (W : F.GaugeField F.depth) : Matrix (LinkComponent F F.depth) (LinkComponent F F.depth) ℝ :=
  blockPermMatrix (bondPermutation g hg hall) fun b => bondRotation g γ W b.1
private def offCentreRotation :
    Matrix (OffCentreComponent F F.depth F.top) (OffCentreComponent F F.depth F.top) ℝ :=
  (gaugeRotation hg hsite γ).submatrix Subtype.val Subtype.val
private theorem siteTangent_gaugeRotation (v : SiteComponent F F.depth → ℝ) (y : F.Site F.depth) (m : Fin 3) :
    siteTangent (gaugeRotation hg hsite γ *ᵥ v) (g.actSite F.depth y) m =
      ∑ n, adjointMatrix (γ (g.actSite F.depth y))⁻¹ m n * siteTangent v y n := by
  have hg' : ∀ (u : SiteComponent F F.depth → ℝ) (y : F.Site F.depth) (n : Fin 3),
      siteTangent u y n = u (⟨y, hsite y⟩, n) := fun u y n => by
    unfold siteTangent
    rw [dif_pos (hsite y)]
  simp only [hg']
  exact blockPermMatrix_mulVec (sitePermutation g hg hsite) _ v ⟨y, hsite y⟩ m
include hg in
private theorem linkRotation_gaugeDifferential_mulVec
    (h3 : ∀ (W : F.GaugeField F.depth) (x : F.Site F.depth) (k : Fin 4),
      linkValue (EnergySymmetry.transportField g W) (g.actSite F.depth x) (g.actStep k) = W x k)
    {W W' : F.GaugeField F.depth} (hγ : EnergySymmetry.transportField g W = _root_.YangMills.Construction.BlockAverages.gaugeTransform γ W')
    (v : SiteComponent F F.depth → ℝ) :
    linkRotation hg hall γ W *ᵥ (gaugeDifferential W *ᵥ v) =
      gaugeDifferential W' *ᵥ (gaugeRotation hg hsite γ *ᵥ v) := by
  funext ⟨p, m⟩
  obtain ⟨b, rfl⟩ := (bondPermutation g hg hall).surjective p
  rw [linkRotation, blockPermMatrix_mulVec, gaugeDifferential_mulVec hsite]
  simp only [gaugeDifferential_mulVec hsite]
  have hb : ((bondPermutation g hg hall b).1 : F.Site F.depth × Fin 4) = bondImage g b.1 := rfl
  simp only [hb]
  set c := b.1 with hc
  set x' := (bondImage g c).1 with hx
  set i := (bondImage g c).2 with hi
  have hW : W' x' i = (γ x')⁻¹ * EnergySymmetry.transportField g W x' i * γ (x' + unitStep F.depth i) := by
    rw [hγ]
    simp only [gaugeTransform]
    group
  rcases hg.1 (g.perm.symm c.2) with hs | hs
  · have e0 : EnergySymmetry.transportField g W x' i = W c.1 c.2 := transportField_bondImage_of_pos h3 W hs
    have ex : x' = g.actSite F.depth c.1 := by rw [hx, bondImage_of_pos hs]
    have ei : i = g.perm.symm c.2 := by rw [hi, bondImage_of_pos hs]
    have ee : x' + unitStep F.depth i = g.actSite F.depth (c.1 + unitStep F.depth c.2) := by
      rw [ex, ei, actSite_add_unitStep_of_pos hg _ hs]
    rw [ee] at hW ⊢
    rw [ex, siteTangent_gaugeRotation hg hsite]
    simp only [siteTangent_gaugeRotation hg hsite]
    have ht : bondRotation g γ W c = adjointMatrix (γ (g.actSite F.depth c.1))⁻¹ := by
      unfold bondRotation
      rw [if_pos hs, ← hx, ex]
    rw [ht, ← ex, hW, e0, ex]
    refine matrix_identity_pos _ _ _ _ _ _ ?_ m
    rw [← adjointMatrix_mul, ← adjointMatrix_mul]
    congr 1
    group
  · have e0 : EnergySymmetry.transportField g W x' i = (W c.1 c.2)⁻¹ := transportField_bondImage_of_neg h3 W hs
    have ex : x' = g.actSite F.depth (c.1 + unitStep F.depth c.2) := by rw [hx, bondImage_of_neg hg hs]
    have ei : i = g.perm.symm c.2 := by rw [hi, bondImage_of_neg hg hs]
    have ee : x' + unitStep F.depth i = g.actSite F.depth c.1 := by
      rw [ex, ei, actSite_add_unitStep_of_neg hg _ hs, sub_add_cancel]
    rw [ee] at hW ⊢
    rw [ex, siteTangent_gaugeRotation hg hsite]
    simp only [siteTangent_gaugeRotation hg hsite]
    have ht : bondRotation g γ W c =
        - adjointMatrix ((γ (g.actSite F.depth (c.1 + unitStep F.depth c.2)))⁻¹ * (W c.1 c.2)⁻¹) := by
      unfold bondRotation
      rw [if_neg (by rw [hs]; norm_num), ← hx, ex]
    rw [ht, ← ex, hW, e0, ex]
    refine matrix_identity_neg _ _ _ _ _ _ _ ?_ ?_ m
    · rw [← adjointMatrix_mul]
      congr 1
      group
    · rw [← adjointMatrix_mul]
      congr 1
      group
include hg in
private theorem linkRotation_mul_gaugeDifferential
    (h3 : ∀ (W : F.GaugeField F.depth) (x : F.Site F.depth) (k : Fin 4),
      linkValue (EnergySymmetry.transportField g W) (g.actSite F.depth x) (g.actStep k) = W x k)
    {W W' : F.GaugeField F.depth} (hγ : EnergySymmetry.transportField g W = gaugeTransform γ W') :
    linkRotation hg hall γ W * gaugeDifferential W = gaugeDifferential W' * gaugeRotation hg hsite γ := by
  ext p s
  have := linkRotation_gaugeDifferential_mulVec hg hsite hall γ h3 hγ (Pi.single s 1)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at this
  exact congrFun this p
private theorem gaugeRotation_centre {s : SiteComponent F F.depth} (hs : IsBlockCentre F.top s.1.1)
    (t : OffCentreComponent F F.depth F.top) : gaugeRotation hg hsite γ s t.1 = 0 := by
  have hne : s.1 ≠ sitePermutation g hg hsite t.1.1 := fun e => t.2 ((isBlockCentre_actSite_iff hg _).1 (by
    have : s.1.1 = g.actSite F.depth t.1.1.1 := congrArg Subtype.val e
    rwa [this] at hs))
  simp [gaugeRotation, blockPermMatrix, hne]
private theorem linkRotation_mul_offCentre
    (h3 : ∀ (W : F.GaugeField F.depth) (x : F.Site F.depth) (k : Fin 4),
      linkValue (EnergySymmetry.transportField g W) (g.actSite F.depth x) (g.actStep k) = W x k)
    {W W' : F.GaugeField F.depth} (hγ : EnergySymmetry.transportField g W = gaugeTransform γ W') :
    linkRotation hg hall γ W * offCentreGaugeDifferential W =
      offCentreGaugeDifferential W' * offCentreRotation hg hsite γ := by
  ext p t
  have e1 : (linkRotation hg hall γ W * offCentreGaugeDifferential W) p t =
      (linkRotation hg hall γ W * gaugeDifferential W) p t.1 := rfl
  rw [e1, linkRotation_mul_gaugeDifferential hg hsite hall γ h3 hγ, Matrix.mul_apply, Matrix.mul_apply,
    ← sum_offCentre (fun s => gaugeDifferential W' p s * gaugeRotation hg hsite γ s t.1) fun s h => by
      rw [gaugeRotation_centre hg hsite γ h, mul_zero]]
  rfl
private theorem offCentreRotation_orthogonal : (offCentreRotation hg hsite γ)ᵀ * offCentreRotation hg hsite γ = 1 := by
  have h : (gaugeRotation hg hsite γ)ᵀ * gaugeRotation hg hsite γ = 1 := by
    unfold gaugeRotation
    exact blockPermMatrix_orthogonal (sitePermutation g hg hsite) (fun s => adjointMatrix (γ (g.actSite F.depth s.1))⁻¹)
      fun s => adjointMatrix_orthogonal _
  ext t u
  have e := congrFun (congrFun h t.1) u.1
  rw [Matrix.mul_apply] at e
  rw [Matrix.mul_apply]
  rw [← sum_offCentre (fun s => (gaugeRotation hg hsite γ)ᵀ t.1 s * gaugeRotation hg hsite γ s u.1) fun s h => by
    rw [gaugeRotation_centre hg hsite γ h, mul_zero]] at e
  have e1 : ((1 : Matrix _ _ ℝ) t.1 u.1) = (1 : Matrix _ _ ℝ) t u := by
    by_cases htu : t = u
    · subst htu
      simp
    · have : t.1 ≠ u.1 := fun e => htu (Subtype.ext e)
      simp [Matrix.one_apply, this, htu]
  rw [← e1, ← e]
  rfl
private theorem linkRotation_orthogonal (W : F.GaugeField F.depth) :
    (linkRotation hg hall γ W)ᵀ * linkRotation hg hall γ W = 1 := by
  unfold linkRotation
  exact blockPermMatrix_orthogonal (bondPermutation g hg hall) (fun b => bondRotation g γ W b.1)
    fun b => bondRotation_orthogonal g γ W b.1
end Rotations
end Symmetry
section Charts
variable {F : BlockFrame}
open Classical
private theorem eventually_linkVariation_re_pos {E B : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Finite B]
    {w T : B → ℍ[ℝ]} {L : B → E →L[ℝ] ℍ[ℝ] × ℍ[ℝ] × ℍ[ℝ]} (hT : ∀ b, T b * star (T b) = 1) :
    ∀ᶠ e in 𝓝 (0 : E), ∀ b, 0 < (linkVariation (w b) (T b) (L b e)).re := by
  rw [Filter.eventually_all]
  intro b
  have hc : Continuous fun e => (linkVariation (w b) (T b) (L b e)).re :=
    Quaternion.continuous_re.comp ((contDiff_linkVariation (w b) (T b)).continuous.comp (L b).continuous)
  have h0 : 0 < (linkVariation (w b) (T b) (L b 0)).re := by
    rw [map_zero, linkVariation_zero (hT b)]
    simp
  exact hc.continuousAt.eventually (lt_mem_nhds h0)
private theorem blockEnergy_gaugeTransform (hG : MinimalActionIsGaugeInvariant) (hodd : Odd F.blockSide) (a : ℝ)
    (S : Finset F.Cell) (Γ : F.Site F.depth → UnitQuaternion) (hΓ : ∀ z, Γ (cellCentre F.depth z) = 1)
    (W : F.GaugeField F.depth) (V : F.GaugeField F.top) :
    blockEnergy a S F.depth (_root_.YangMills.Construction.BlockAverages.gaugeTransform Γ W) V = blockEnergy a S F.depth W V := by
  unfold blockEnergy
  rw [hG F a S F.depth hodd.pos (Nat.le_succ _) Γ W]
  congr 2
  refine Finset.sum_congr rfl fun c _ => ?_
  have e : _root_.YangMills.Construction.BlockAverages.contourAverage (gaugeTransform Γ W) c = _root_.YangMills.Construction.BlockAverages.contourAverage W c := by
    rw [GaugeMotions.contourAverage_gaugeTransform hodd (le_refl _) Γ W c,
      ComplexChart.BlockGeometry.refineSite_eq_cellCentre, ComplexChart.BlockGeometry.refineSite_eq_cellCentre, hΓ, hΓ]
    simp
  unfold blockFit
  rw [e]
private theorem gaugeGenerator_cellCentre (z : OffCentreComponent F F.depth F.top → ℝ) (c : F.Cell) :
    gaugeGenerator z (cellCentre F.depth c) = 0 := by
  have h : ∀ m, siteTangent (extendByZeroAtCentres z) (cellCentre F.depth c) m = 0 := fun m => by
    unfold siteTangent
    split_ifs with hy
    · exact extendByZeroAtCentres_centre z ⟨c, rfl⟩
    · rfl
  simp [gaugeGenerator, h]
private theorem blockEnergy_charts_agree (hG : MinimalActionIsGaugeInvariant) (hodd : Odd F.blockSide) {a : ℝ}
    {g : CubicSymmetry} (hg : g.IsSymmetry F)
    (hall : ∀ c : F.Site F.depth × Fin 4, c ∈ innerBonds (finiteCells F) F.depth)
    {V V' : F.GaugeField F.top}
    (h1 : ∀ W : F.GaugeField F.depth,
      blockEnergy a (finiteCells F) F.depth (EnergySymmetry.transportField g W) V' =
        blockEnergy a (finiteCells F) F.depth W V)
    (h3 : ∀ (W : F.GaugeField F.depth) (x : F.Site F.depth) (k : Fin 4),
      linkValue (EnergySymmetry.transportField g W) (g.actSite F.depth x) (g.actStep k) = W x k)
    {w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (ht : ∀ b, IsAxialTreeBond b → w b.1 b.2 = 0) (ht' : ∀ b, IsAxialTreeBond b → w' b.1 b.2 = 0)
    {γ : F.Site F.depth → UnitQuaternion} (hγ1 : ∀ z, γ (cellCentre F.depth z) = 1)
    (hγ : EnergySymmetry.transportField g (chartedField w V) = _root_.YangMills.Construction.BlockAverages.gaugeTransform γ (chartedField w' V'))
    (x η : StepVariable (finiteCells F)) (z : OffCentreComponent F F.depth F.top → ℝ)
    (hre : ∀ b : ↥(innerBonds (finiteCells F) F.depth),
      0 < (linkVariation (linkCoordQuat w' b) (linkTopQuat V' b) (linkMoveL b.1 (x, z))).re)
    (hre' : ∀ b : ↥(innerBonds (finiteCells F) F.depth),
      0 < (linkVariation (linkCoordQuat w b) 1 (chartMoveL b.1 η)).re)
    (hΨν : linkCoords (linkCoordQuat w') (linkTopQuat V') (fun b => linkMoveL b.1) (x, z) =
      linkRotation hg hall γ (chartedField w V) *ᵥ
        linkCoords (linkCoordQuat w) (fun _ => 1) (fun b => chartMoveL b.1) η) :
    blockEnergy a (finiteCells F) F.depth (chartedField (fun y i => w' y i + stepCoordinates x y i) V') V' =
      blockEnergy a (finiteCells F) F.depth (chartedField (fun y i => w y i + stepCoordinates η y i) V) V := by
  set C := chartedField (fun y i => w y i + stepCoordinates η y i) V with hCdef
  set Z := chartedField (fun y i => w' y i + stepCoordinates x y i) V' with hZdef
  have hAB : _root_.YangMills.Construction.BlockAverages.gaugeTransform (fun y => expUnit (gaugeGenerator z y)) Z =
      _root_.YangMills.Construction.BlockAverages.gaugeTransform (fun y => (γ y)⁻¹) (EnergySymmetry.transportField g C) := by
    funext y i
    obtain ⟨b, hb⟩ := (bondPermutation g hg hall).surjective ⟨(y, i), hall _⟩
    have hfw : bondImage g b.1 = (y, i) := congrArg Subtype.val hb
    obtain ⟨hm, hr⟩ := transport_coordinates hg h3 hγ C b.1
    rw [hfw] at hm hr
    have hA := gaugeTransform_axialTree ht' V' x z ⟨(y, i), hall _⟩
    have hc := charted_representation ht V η b
    have hcomp : ∀ m, imaginaryCoord m ((_root_.YangMills.Construction.BlockAverages.gaugeTransform (fun y => expUnit (gaugeGenerator z y)) Z y i *
        (chartedField w' V' y i)⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
        imaginaryCoord m ((_root_.YangMills.Construction.BlockAverages.gaugeTransform (fun y => (γ y)⁻¹) (EnergySymmetry.transportField g C) y i *
          (chartedField w' V' y i)⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
      intro m
      have e := congrFun hΨν (⟨(y, i), hall _⟩, m)
      have e2 := blockPermMatrix_mulVec (bondPermutation g hg hall) (fun b => bondRotation g γ (chartedField w V) b.1)
        (linkCoords (linkCoordQuat w) (fun _ => 1) (fun b => chartMoveL b.1) η) b m
      rw [hb] at e2
      have e3 := e.trans e2
      have hm' := hm m
      simp only at hm'
      rw [hm', hc]
      exact (congrArg (imaginaryCoord m) hA).trans e3
    have hq := unit_eq_of_imaginaryCoord_eq hcomp (by
      have := hre ⟨(y, i), hall _⟩
      rw [← hA] at this
      exact this) (by
      simp only at hr
      rw [hr, hc]
      exact hre' b)
    exact mul_right_cancel hq
  calc blockEnergy a (finiteCells F) F.depth Z V'
      = blockEnergy a (finiteCells F) F.depth (_root_.YangMills.Construction.BlockAverages.gaugeTransform (fun y => expUnit (gaugeGenerator z y)) Z) V' :=
        (blockEnergy_gaugeTransform hG hodd a _ _ (fun c => by rw [gaugeGenerator_cellCentre, expUnit_zero_eq_one])
          Z V').symm
    _ = blockEnergy a (finiteCells F) F.depth
          (_root_.YangMills.Construction.BlockAverages.gaugeTransform (fun y => (γ y)⁻¹) (EnergySymmetry.transportField g C)) V' := by rw [hAB]
    _ = blockEnergy a (finiteCells F) F.depth (EnergySymmetry.transportField g C) V' :=
        blockEnergy_gaugeTransform hG hodd a _ _ (fun c => by rw [hγ1, inv_one]) _ V'
    _ = blockEnergy a (finiteCells F) F.depth C V := h1 C
private theorem hessianMatrix_eq_chartedHessian (a ρ : ℝ) (V : F.GaugeField F.top) :
    Slope.hessianMatrix stepComponents (ReferenceDensity.chartedEnergyAtMinimizer a ρ V) =
      ReferenceDensity.chartedHessian a ρ V 0 := by
  ext i j
  show fderiv ℝ (fun ζ => fderiv ℝ (ReferenceDensity.chartedEnergyAtMinimizer a ρ V) ζ
      (stepComponents.symm (Pi.single i 1))) 0 (stepComponents.symm (Pi.single j 1)) = _
  rw [stepComponents_symm_single, stepComponents_symm_single]
  rfl
private theorem sinc_pos_of_lt_pi {u : ℝ} (h0 : 0 ≤ u) (h1 : u < Real.pi) : 0 < Real.sinc u := by apply _root_.YangMills.SharedProofs.p1819 <;> assumption
private theorem haarLogRatio_eq {w : imaginaryQuaternions} (h : ‖w‖ < Real.pi) :
    haarLogRatio w = Real.log (Real.sinc ‖w‖ ^ 2) := by
  unfold haarLogRatio haarRadialDensity
  rw [if_pos h, if_pos Real.pi_pos, Real.sinc_zero]
  congr 1
  have := Real.pi_pos.ne'
  field_simp
private theorem log_det_relation {H H' Q Q' d : ℝ} (hH : 0 < H) (hH' : 0 < H') (hQ : 0 < Q) (hQ' : 0 < Q')
    (hd : d ≠ 0) (h : H * (d * Q') ^ 2 = H' * (d * Q) ^ 2) :
    -(1 / 2) * Real.log H' + Real.log Q' = -(1 / 2) * Real.log H + Real.log Q := by
  have e : H * Q' ^ 2 = H' * Q ^ 2 := mul_left_cancel₀ (pow_ne_zero 2 hd) (by linear_combination h)
  have l := congrArg Real.log e
  rw [Real.log_mul hH.ne' (pow_ne_zero 2 hQ'.ne'), Real.log_mul hH'.ne' (pow_ne_zero 2 hQ.ne'), Real.log_pow,
    Real.log_pow] at l
  push_cast at l
  linarith
private theorem sum_haarLogRatio (hD : LeftExpDifferentialDet) {w : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    {ρ : ℝ} (hρ : ρ ≤ 1) (hw : ∀ b ∈ chordBonds (finiteCells F), ‖w b.1 b.2‖ ≤ ρ) :
    0 < ∏ b : ↥(chordBonds (finiteCells F)), (leftExpDifferential (w b.1.1 b.1.2)).det ∧
      ∑ b : ↥(chordBonds (finiteCells F)), haarLogRatio (w b.1.1 b.1.2) =
        Real.log (∏ b : ↥(chordBonds (finiteCells F)), (leftExpDifferential (w b.1.1 b.1.2)).det) := by
  have hlt : ∀ b : ↥(chordBonds (finiteCells F)), ‖w b.1.1 b.1.2‖ < Real.pi := fun b =>
    lt_of_le_of_lt ((hw b.1 b.2).trans hρ) (by linarith [Real.pi_gt_three])
  have hpos : ∀ b : ↥(chordBonds (finiteCells F)), 0 < (leftExpDifferential (w b.1.1 b.1.2)).det := fun b => by
    rw [hD]
    exact pow_pos (sinc_pos_of_lt_pi (norm_nonneg _) (hlt b)) 2
  refine ⟨Finset.prod_pos fun b _ => hpos b, ?_⟩
  rw [Real.log_prod fun b _ => (hpos b).ne']
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [haarLogRatio_eq (hlt b), hD]
private def matrixCLM {n : Type} [Fintype n] (M : Matrix n n ℝ) : (n → ℝ) →L[ℝ] (n → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.mulVecLin M)
private theorem chartedField_of_tree (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    {b : F.Site F.depth × Fin 4} (h : IsAxialTreeBond b) : chartedField w V b.1 b.2 = 1 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartDeterminedByField.chartedField_eq_one <;> assumption
end Charts
open Classical in
theorem stepAmplitudeSymmetry_holds (hTwo : Slope.HessianDetRatioInvariant) (hTan : ChartAndGaugeDifferentialsBasis)
    (hDet : LeftExpDifferentialDet) (hE : EnergySymmetry.BlockEnergySymmetric)
    (hG : MinimalActionGaugeCovariance) (hCov : BlocksCoverLowerLevel) :
    stepAmplitudeSymmetryStatement := by
  intro F a ρ V V' g γ hodd hs hg h0 h1 hC hl hl' hγ1 hγ hp hp'
  have hsite : ∀ y : F.Site F.depth, y ∈ sitesOfCells (finiteCells F) F.depth := hCov F hodd fun i => by
    have := hs i
    omega
  have hall : ∀ c : F.Site F.depth × Fin 4, c ∈ innerBonds (finiteCells F) F.depth := fun c =>
    Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hsite _, Finset.mem_univ _⟩, hsite _⟩
  obtain ⟨e1, -, h3⟩ := hE F a (finiteCells F) (finiteCells F) V V' g hodd hg
    (fun z => by simp [BlockOffsets.mem_finiteCells hs]) hC
  obtain ⟨e, d, hd, hdet⟩ := hTan F hodd hs
  set w := coordsAboveFrame true a ρ 0 V 0 with hw
  set w' := coordsAboveFrame true a ρ 0 V' 0 with hw'
  have ht : ∀ b, IsAxialTreeBond b → w b.1 b.2 = 0 := fun b h => hl.1 b (not_mem_chordBonds_of_tree h)
  have ht' : ∀ b, IsAxialTreeBond b → w' b.1 b.2 = 0 := fun b h => hl'.1 b (not_mem_chordBonds_of_tree h)
  have hγ' : EnergySymmetry.transportField g (chartedField w V) = _root_.YangMills.Construction.BlockAverages.gaugeTransform γ (chartedField w' V') := hγ
  have hdA := hdet w (chartedField w V) fun b h => chartedField_of_tree w V h
  have hdA' := hdet w' (chartedField w' V') fun b h => chartedField_of_tree w' V' h
  obtain ⟨hQ, hs1⟩ := sum_haarLogRatio hDet (w := w) h1 hl.2.1
  obtain ⟨hQ', hs2⟩ := sum_haarLogRatio hDet (w := w') h1 hl'.2.1
  have hA : ((Matrix.fromCols (chartDifferential w) (offCentreGaugeDifferential (chartedField w V))).submatrix id
      e.symm).det ≠ 0 := by
    rw [hdA]
    exact mul_ne_zero hd hQ.ne'
  have hA' : ((Matrix.fromCols (chartDifferential w') (offCentreGaugeDifferential (chartedField w' V'))).submatrix id
      e.symm).det ≠ 0 := by
    rw [hdA']
    exact mul_ne_zero hd hQ'.ne'
  have hν : (fun η => linkRotation hg hall γ (chartedField w V) *ᵥ
      linkCoords (linkCoordQuat w) (fun _ => 1) (fun b => chartMoveL b.1) η) =
      matrixCLM (linkRotation hg hall γ (chartedField w V)) ∘
        linkCoords (linkCoordQuat w) (fun _ => 1) (fun b => chartMoveL b.1) := rfl
  have hν₀ : ContDiff ℝ 2 (linkCoords (linkCoordQuat w) (fun _ => 1) (fun b => chartMoveL b.1)) := contDiff_linkCoords
  have hev1 := eventually_linkVariation_re_pos
    (E := StepVariable (finiteCells F) × (OffCentreComponent F F.depth F.top → ℝ))
    (w := linkCoordQuat w') (T := linkTopQuat V') (L := fun b => linkMoveL b.1) fun b => unit_mul_star_self _
  have hev2 := eventually_linkVariation_re_pos (E := StepVariable (finiteCells F)) (w := linkCoordQuat w)
    (T := fun _ => (1 : ℍ[ℝ])) (L := fun b => chartMoveL b.1) fun _ => by simp
  have key := hTwo (StepVariable (finiteCells F)) (ReferenceDensity.ChartCoord F) (OffCentreComponent F F.depth F.top)
    (LinkComponent F F.depth) stepComponents e
    (ReferenceDensity.chartedEnergyAtMinimizer a ρ V) (ReferenceDensity.chartedEnergyAtMinimizer a ρ V')
    (linkCoords (linkCoordQuat w') (linkTopQuat V') fun b => linkMoveL b.1)
    (fun η => linkRotation hg hall γ (chartedField w V) *ᵥ
      linkCoords (linkCoordQuat w) (fun _ => 1) (fun b => chartMoveL b.1) η)
    (chartDifferential w) (chartDifferential w') (offCentreGaugeDifferential (chartedField w V))
    (offCentreGaugeDifferential (chartedField w' V'))
    (linkRotation hg hall γ (chartedField w V)) (offCentreRotation hg hsite γ)
    contDiff_linkCoords.contDiffAt (linkCoords_zero fun b => unit_mul_star_self _)
    (fun x z => fderiv_gaugeTransform_comp hsite ht' V' x z)
    (by
      rw [hν]
      exact ((matrixCLM _).contDiff.comp hν₀).contDiffAt)
    (by
      show linkRotation hg hall γ (chartedField w V) *ᵥ
        linkCoords (linkCoordQuat w) (fun _ => 1) (fun b => chartMoveL b.1) 0 = 0
      rw [linkCoords_zero fun _ => by simp, Matrix.mulVec_zero])
    (fun x => by
      rw [hν, fderiv_comp _ (ContinuousLinearMap.differentiableAt _) (hν₀.differentiable (by norm_num) 0)]
      simp only [ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply, fderiv_charted_comp]
      rfl)
    (linkRotation_orthogonal hg hall γ _) (offCentreRotation_orthogonal hg hsite γ)
    (linkRotation_mul_offCentre hg hsite hall γ h3 hγ') hA hA'
    (by
      rw [nhds_prod_eq]
      filter_upwards [hev1.prod_mk hev2] with p hpp hΨν
      obtain ⟨⟨x, z⟩, η⟩ := p
      have := blockEnergy_charts_agree hG.1 hodd hg hall e1 h3 ht ht' hγ1 hγ' x η z hpp.1 hpp.2 hΨν
      simp only [ReferenceDensity.chartedEnergyAtMinimizer, chartedEnergy]
      rw [coordsAboveFrame_eq_add a ρ V' x, coordsAboveFrame_eq_add a ρ V η]
      exact this)
    (Filter.Eventually.of_forall fun η => hl.2.2 _)
    (Filter.Eventually.of_forall fun η => hl'.2.2 _)
    (by
      rw [hessianMatrix_eq_chartedHessian]
      exact hp')
  rw [hessianMatrix_eq_chartedHessian, hessianMatrix_eq_chartedHessian, hdA, hdA'] at key
  rw [hs1, hs2]
  exact log_det_relation hp.det_pos hp'.det_pos hQ hQ' hd key
end YangMills.Construction.RunningCouplingSlope.StepAmplitudeSymmetry
end
