import YangMills.Construction.SoftAverages.LangevinModelOfAStep
import YangMills.Construction.SoftAverages.MovesOfAField
import Mathlib
set_option autoImplicit false
open scoped Quaternion
noncomputable section
namespace YangMills.Construction.SoftAverages.HaarCoordinates
open FiniteLinkFunctions FieldMoves
abbrev Coordinates : Type := Fin 3 → ℝ
def basisVec (i : Fin 3) : Coordinates := Pi.single i 1
def expDeriv (y : Coordinates) : Coordinates →L[ℝ] ℍ[ℝ] := fderiv ℝ expImag y
def rightFrame (y v : Coordinates) : ℍ[ℝ] := expDeriv y v * star (expImag y)
theorem hasFDerivAt_expImag (y : Coordinates) : HasFDerivAt expImag (expDeriv y) y :=
  (contDiff_expImag.differentiable (by simp) y).hasFDerivAt
def imCoord (A : Fin 3) (q : ℍ[ℝ]) : ℝ := ![q.imI, q.imJ, q.imK] A
def frameMat (y : Coordinates) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun A i => imCoord A (rightFrame y (basisVec i))
theorem quat_coe_eq_smul_one (r : ℝ) : (r : ℍ[ℝ]) = r • (1 : ℍ[ℝ]) :=
  Algebra.algebraMap_eq_smul_one r
theorem norm_pureQuaternionCLM (y : Coordinates) :
    ‖pureQuaternionCLM y‖ = Real.sqrt (∑ i, y i ^ 2) := by
  have e : ‖pureQuaternionCLM y‖ ^ 2 = ∑ i, y i ^ 2 := by
    rw [sq, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
    have e0 : (pureQuaternionCLM y).re = 0 := rfl
    have e1 : (pureQuaternionCLM y).imI = y 0 := rfl
    have e2 : (pureQuaternionCLM y).imJ = y 1 := rfl
    have e3 : (pureQuaternionCLM y).imK = y 2 := rfl
    rw [e0, e1, e2, e3, Fin.sum_univ_three]
    ring
  rw [← e, Real.sqrt_sq (norm_nonneg _)]
theorem expImag_eq_cos_add_sin (y : Coordinates) :
    expImag y = (Real.cos (Real.sqrt (∑ i, y i ^ 2)) : ℍ[ℝ]) +
      (Real.sin (Real.sqrt (∑ i, y i ^ 2)) / Real.sqrt (∑ i, y i ^ 2)) • pureQuaternionCLM y := by
  rw [expImag_eq_exp, Quaternion.exp_of_re_eq_zero _ rfl, norm_pureQuaternionCLM]
theorem expDeriv_eq {y : Coordinates} (hy : y ≠ 0) (v : Coordinates) :
    expDeriv y v =
      ((-(Real.sin (Real.sqrt (∑ i, y i ^ 2))) * ((∑ j, y j * v j) / Real.sqrt (∑ i, y i ^ 2)) : ℝ) : ℍ[ℝ]) +
      (((Real.cos (Real.sqrt (∑ i, y i ^ 2)) * Real.sqrt (∑ i, y i ^ 2) - Real.sin (Real.sqrt (∑ i, y i ^ 2))) /
          (Real.sqrt (∑ i, y i ^ 2)) ^ 2) * ((∑ j, y j * v j) / Real.sqrt (∑ i, y i ^ 2))) •
        pureQuaternionCLM y +
      (Real.sin (Real.sqrt (∑ i, y i ^ 2)) / Real.sqrt (∑ i, y i ^ 2)) • pureQuaternionCLM v := by
  have hs0 : 0 < ∑ i, y i ^ 2 := by
    have hne : ∃ i, y i ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hy (funext hc)
    obtain ⟨i, hi⟩ := hne
    exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ _, by positivity⟩
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = Real.sqrt (∑ i, y i ^ 2) := ⟨_, rfl⟩
  have hθ0 : 0 < θ := hθ ▸ Real.sqrt_pos.mpr hs0
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = ∑ j, y j * v j := ⟨_, rfl⟩
  rw [← hθ, ← hD]
  have h₁ : HasDerivAt (fun t : ℝ => ∑ i, (y + t • v) i ^ 2) (2 * D) 0 := by
    have h₂ : ∀ i, HasDerivAt (fun t : ℝ => (y + t • v) i ^ 2) (2 * (y i * v i)) 0 := fun i => by
      have h₃ : HasDerivAt (fun t : ℝ => y i + t * v i) (v i) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v i)).const_add (y i)
      have h₄ := h₃.fun_pow 2
      have e : (fun t : ℝ => (y + t • v) i ^ 2) = fun t => (y i + t * v i) ^ 2 := by
        funext t
        simp
      rw [e]
      refine h₄.congr_deriv ?_
      simp
      ring
    have h₅ := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => h₂ i
    rw [hD, Finset.mul_sum]
    exact h₅
  have hval : (∑ i, (y + (0 : ℝ) • v) i ^ 2) = ∑ i, y i ^ 2 := by simp
  have hθt : HasDerivAt (fun t : ℝ => Real.sqrt (∑ i, (y + t • v) i ^ 2)) (D / θ) 0 := by
    have := h₁.sqrt (by rw [hval]; exact hs0.ne')
    rw [hval, ← hθ] at this
    convert this using 1
    field_simp
  have hval₂ : Real.sqrt (∑ i, (y + (0 : ℝ) • v) i ^ 2) = θ := by rw [hval, hθ]
  have hc : HasDerivAt (fun t : ℝ => Real.cos (Real.sqrt (∑ i, (y + t • v) i ^ 2)))
      (-Real.sin θ * (D / θ)) 0 := by
    have := hθt.cos
    rw [hval₂] at this
    exact this
  have hsn : HasDerivAt (fun t : ℝ => Real.sin (Real.sqrt (∑ i, (y + t • v) i ^ 2)))
      (Real.cos θ * (D / θ)) 0 := by
    have := hθt.sin
    rw [hval₂] at this
    exact this
  have hS : HasDerivAt (fun t : ℝ => Real.sin (Real.sqrt (∑ i, (y + t • v) i ^ 2)) /
      Real.sqrt (∑ i, (y + t • v) i ^ 2))
      (((Real.cos θ * θ - Real.sin θ) / θ ^ 2) * (D / θ)) 0 := by
    have := hsn.div hθt (by rw [hval₂]; exact hθ0.ne')
    rw [hval₂] at this
    refine this.congr_deriv ?_
    ring
  have hp : HasDerivAt (fun t : ℝ => pureQuaternionCLM (y + t • v)) (pureQuaternionCLM v) 0 := by
    have h₂ : HasDerivAt (fun t : ℝ => y + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y
    exact pureQuaternionCLM.hasFDerivAt.comp_hasDerivAt 0 h₂
  have hg := ((hc.smul_const (1 : ℍ[ℝ])).add (hS.smul hp))
  have hE : HasDerivAt (fun t : ℝ => expImag (y + t • v)) (expDeriv y v) 0 := by
    have h₂ : HasDerivAt (fun t : ℝ => y + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y
    have h₃ : HasFDerivAt expImag (expDeriv y) (y + (0 : ℝ) • v) := by
      simpa using hasFDerivAt_expImag y
    exact h₃.comp_hasDerivAt 0 h₂
  have heq : (fun t : ℝ => expImag (y + t • v)) = fun t : ℝ =>
      Real.cos (Real.sqrt (∑ i, (y + t • v) i ^ 2)) • (1 : ℍ[ℝ]) +
        (Real.sin (Real.sqrt (∑ i, (y + t • v) i ^ 2)) / Real.sqrt (∑ i, (y + t • v) i ^ 2)) •
          pureQuaternionCLM (y + t • v) := by
    funext t
    rw [expImag_eq_cos_add_sin, quat_coe_eq_smul_one]
  rw [heq] at hE
  have huniq := hE.unique hg
  rw [huniq]
  simp only [zero_smul, add_zero]
  rw [← hθ, quat_coe_eq_smul_one]
  abel
def cross3 (v y : Coordinates) : Coordinates :=
  ![v 1 * y 2 - v 2 * y 1, v 2 * y 0 - v 0 * y 2, v 0 * y 1 - v 1 * y 0]
theorem imCoord_mul_star (x u S c : ℝ) (y v : Coordinates) (A : Fin 3) :
    imCoord A (((x : ℍ[ℝ]) + u • pureQuaternionCLM y + S • pureQuaternionCLM v) *
        star ((c : ℍ[ℝ]) + S • pureQuaternionCLM y)) =
      S * c * v A + (c * u - x * S) * y A - S ^ 2 * cross3 v y A := by
  have p₀ : ∀ w : Coordinates, (pureQuaternionCLM w).re = 0 := fun _ => rfl
  have p₁ : ∀ w : Coordinates, (pureQuaternionCLM w).imI = w 0 := fun _ => rfl
  have p₂ : ∀ w : Coordinates, (pureQuaternionCLM w).imJ = w 1 := fun _ => rfl
  have p₃ : ∀ w : Coordinates, (pureQuaternionCLM w).imK = w 2 := fun _ => rfl
  fin_cases A <;>
    simp [imCoord, cross3, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
      Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul, Quaternion.imK_smul,
      p₀, p₁, p₂, p₃] <;> ring
theorem imCoord_rightFrame {y : Coordinates} (hy : y ≠ 0) (v : Coordinates) (A : Fin 3) :
    imCoord A (rightFrame y v) =
      (Real.sin (Real.sqrt (∑ i, y i ^ 2)) / Real.sqrt (∑ i, y i ^ 2)) *
          Real.cos (Real.sqrt (∑ i, y i ^ 2)) * v A +
      (Real.cos (Real.sqrt (∑ i, y i ^ 2)) *
          (((Real.cos (Real.sqrt (∑ i, y i ^ 2)) * Real.sqrt (∑ i, y i ^ 2) -
              Real.sin (Real.sqrt (∑ i, y i ^ 2))) /
            (Real.sqrt (∑ i, y i ^ 2)) ^ 2) * ((∑ j, y j * v j) / Real.sqrt (∑ i, y i ^ 2))) -
        (-(Real.sin (Real.sqrt (∑ i, y i ^ 2))) * ((∑ j, y j * v j) / Real.sqrt (∑ i, y i ^ 2))) *
          (Real.sin (Real.sqrt (∑ i, y i ^ 2)) / Real.sqrt (∑ i, y i ^ 2))) * y A -
      (Real.sin (Real.sqrt (∑ i, y i ^ 2)) / Real.sqrt (∑ i, y i ^ 2)) ^ 2 * cross3 v y A := by
  unfold rightFrame
  rw [expDeriv_eq hy, expImag_eq_cos_add_sin]
  exact imCoord_mul_star _ _ _ _ y v A
theorem det_scalar_add_rankOne_sub_cross (a b κ : ℝ) (y : Coordinates) (T : ℝ)
    (hT : T = ∑ i, y i ^ 2) :
    (Matrix.of fun A i : Fin 3 => a * (if A = i then 1 else 0) + b * y i * y A -
      κ * cross3 (basisVec i) y A).det = (a + b * T) * (a ^ 2 + κ ^ 2 * T) := by
  rw [Matrix.det_fin_three, hT, Fin.sum_univ_three]
  simp [cross3, basisVec]
  ring
theorem det_frameMat (y : Coordinates) : (frameMat y).det = haarDensity y := by
  by_cases hy : y = 0
  · subst hy
    have hd : expDeriv 0 = pureQuaternionCLM := by
      have h₁ : HasFDerivAt (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) (1 : ℍ[ℝ] →L[ℝ] ℍ[ℝ])
          (pureQuaternionCLM 0) := by
        rw [map_zero]
        exact hasFDerivAt_exp_zero (𝕂 := ℝ)
      have h₂ := h₁.comp (0 : Coordinates) pureQuaternionCLM.hasFDerivAt
      have h₃ : HasFDerivAt expImag ((1 : ℍ[ℝ] →L[ℝ] ℍ[ℝ]).comp pureQuaternionCLM) 0 := h₂
      have h₄ := (hasFDerivAt_expImag 0).unique h₃
      rw [h₄]
      ext v <;> simp
    have hM : frameMat 0 = 1 := by
      ext A i
      simp only [frameMat, Matrix.of_apply, rightFrame, hd, expImag_zero, star_one, mul_one]
      have p₁ : ∀ w : Coordinates, (pureQuaternionCLM w).imI = w 0 := fun _ => rfl
      have p₂ : ∀ w : Coordinates, (pureQuaternionCLM w).imJ = w 1 := fun _ => rfl
      have p₃ : ∀ w : Coordinates, (pureQuaternionCLM w).imK = w 2 := fun _ => rfl
      fin_cases A <;> fin_cases i <;> simp [imCoord, basisVec, p₁, p₂, p₃]
    rw [hM, Matrix.det_one]
    simp [haarDensity]
  · have hs0 : 0 < ∑ i, y i ^ 2 := by
      have hne : ∃ i, y i ≠ 0 := by
        by_contra hc
        push Not at hc
        exact hy (funext hc)
      obtain ⟨i, hi⟩ := hne
      exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ _, by positivity⟩
    obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = Real.sqrt (∑ i, y i ^ 2) := ⟨_, rfl⟩
    have hθ0 : 0 < θ := hθ ▸ Real.sqrt_pos.mpr hs0
    have hθ2 : θ ^ 2 = ∑ i, y i ^ 2 := by
      rw [hθ, Real.sq_sqrt hs0.le]
    obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sin θ := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c : ℝ, c = Real.cos θ := ⟨_, rfl⟩
    have hsc : s ^ 2 + c ^ 2 = 1 := by rw [hs, hc]; exact Real.sin_sq_add_cos_sq θ
    have hM : frameMat y = Matrix.of fun A i : Fin 3 => (s / θ * c) * (if A = i then 1 else 0) +
        ((c * ((c * θ - s) / θ ^ 2) + s * (s / θ)) / θ) * y i * y A -
        (s / θ) ^ 2 * cross3 (basisVec i) y A := by
      ext A i
      simp only [frameMat, Matrix.of_apply]
      rw [imCoord_rightFrame hy, ← hθ, ← hs, ← hc]
      have hv : basisVec i A = if A = i then 1 else 0 := by
        simp [basisVec, Pi.single_apply]
      have hD : ∑ j, y j * basisVec i j = y i := by
        simp [basisVec, Pi.single_apply]
      rw [hv, hD]
      ring
    rw [hM, det_scalar_add_rankOne_sub_cross _ _ _ y (θ ^ 2) hθ2]
    have e₁ : s / θ * c + (c * ((c * θ - s) / θ ^ 2) + s * (s / θ)) / θ * θ ^ 2 =
        s ^ 2 + c ^ 2 := by
      field_simp
      ring
    have e₂ : (s / θ * c) ^ 2 + ((s / θ) ^ 2) ^ 2 * θ ^ 2 = (s / θ) ^ 2 * (s ^ 2 + c ^ 2) := by
      field_simp
      ring
    rw [e₁, e₂, hsc, one_mul, mul_one]
    unfold haarDensity
    rw [if_neg hy, hs, hθ]
end YangMills.Construction.SoftAverages.HaarCoordinates
end
