import YangMills.Construction.ColdChainAtEveryLevel.LeastQuarticGaugeProof
import YangMills.Construction.ColdStepAtMirrorFrames.MotionsOfTwoNearCurves
import YangMills.Construction.ColdStepAtMirrorFrames.MoveAlongABondProof
import YangMills.Construction.ColdStepAtMirrorFrames.ThreeDerivativesInASpace
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace TwoCurves
def tripleExpProduct (z : ℍ[ℝ] × ℍ[ℝ] × ℍ[ℝ]) : ℍ[ℝ] :=
  NormedSpace.exp z.1 * NormedSpace.exp z.2.1 * NormedSpace.exp (- z.2.2)
theorem contDiff_exp_quaternion (n : ℕ) : ContDiff ℝ n (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) :=
  contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
theorem contDiff_tripleExpProduct (n : ℕ) : ContDiff ℝ n tripleExpProduct := by
  unfold tripleExpProduct
  have h := contDiff_exp_quaternion n
  exact ((h.comp contDiff_fst).mul (h.comp (contDiff_fst.comp contDiff_snd))).mul
    (h.comp (contDiff_snd.comp contDiff_snd).neg)
section bounds
variable {D E : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] [ProperSpace D] [NormedAddCommGroup E]
  [NormedSpace ℝ E]
theorem exists_bound_lipschitz_closedBall {f : D → E} (hf : ContDiff ℝ 1 f) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ x, ‖x‖ ≤ 1 → ‖f x‖ ≤ C) ∧ ∀ x y, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ‖f x - f y‖ ≤ C * ‖x - y‖ := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hc : Continuous (fun v : D => ‖fderiv ℝ f v‖) := (hf.continuous_fderiv (by norm_num)).norm
  have hcomp : IsCompact (Metric.closedBall (0 : D) 1) := isCompact_closedBall 0 1
  obtain ⟨C₁, hC₁⟩ := hcomp.bddAbove_image hc.continuousOn
  obtain ⟨C₂, hC₂⟩ := hcomp.bddAbove_image hf.continuous.norm.continuousOn
  have hconv : Convex ℝ (Metric.closedBall (0 : D) 1) := convex_closedBall 0 1
  refine ⟨max (max C₁ C₂) 0, le_max_right _ _, fun x hx => ?_, fun x y hx hy => ?_⟩
  · have hm : x ∈ Metric.closedBall (0 : D) 1 := by simpa using hx
    exact (hC₂ ⟨x, hm, rfl⟩).trans ((le_max_right _ _).trans (le_max_left _ _))
  · have hxm : x ∈ Metric.closedBall (0 : D) 1 := by simpa using hx
    have hym : y ∈ Metric.closedBall (0 : D) 1 := by simpa using hy
    exact hconv.norm_image_sub_le_of_norm_fderiv_le (f := f) (fun z _ => hd z)
      (fun z hz => (hC₁ ⟨z, hz, rfl⟩).trans ((le_max_left _ _).trans (le_max_left _ _))) hym hxm
end bounds
section multilinear
variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
theorem norm_apply_single_le (M : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => V) W) (x : V) :
    ‖M ![x]‖ ≤ ‖M‖ * ‖x‖ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ExpProductLog.norm_apply_one_le <;> assumption
theorem norm_apply_pair_le (M : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => V) W) (x y : V) :
    ‖M ![x, y]‖ ≤ ‖M‖ * ‖x‖ * ‖y‖ := by
  have h := M.le_opNorm ![x, y]
  simpa [Fin.prod_univ_two, mul_assoc] using h
theorem apply_single_sub (M : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => V) W) (x y : V) :
    M ![x] - M ![y] = M ![x - y] := by
  have e : ∀ z : V, Function.update ![x] (0 : Fin 1) z = ![z] := by
    intro z
    funext i
    fin_cases i
    simp
  have h := M.map_update_sub ![x] (0 : Fin 1) x y
  rw [e, e, e] at h
  exact h.symm
theorem update_pair_zero (x y z : V) : Function.update ![x, y] (0 : Fin 2) z = ![z, y] := by
  funext i
  fin_cases i <;> simp
theorem update_pair_one (x y z : V) : Function.update ![x, y] (1 : Fin 2) z = ![x, z] := by
  funext i
  fin_cases i <;> simp
theorem apply_pair_sub (M : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => V) W) (x y x' y' : V) :
    M ![x, y] - M ![x', y'] = M ![x - x', y] + M ![x', y - y'] := by
  have h1 := M.map_update_sub ![x, y] (0 : Fin 2) x x'
  have h2 := M.map_update_sub ![x', y] (1 : Fin 2) y y'
  rw [update_pair_zero, update_pair_zero, update_pair_zero] at h1
  rw [update_pair_one, update_pair_one, update_pair_one] at h2
  rw [h1, h2]
  abel
end multilinear
def exponentArgs (u v : (Fin 2 → ℝ) → imaginaryQuaternions) (τ : Fin 2 → ℝ) : ℍ[ℝ] × ℍ[ℝ] × ℍ[ℝ] :=
  ((u τ : ℍ[ℝ]), (v τ : ℍ[ℝ]), (u 0 : ℍ[ℝ]))
theorem coe_iteratedFDeriv_imaginary {a : (Fin 2 → ℝ) → imaginaryQuaternions} (ha : ContDiffAt ℝ 3 a 0) {k : ℕ}
    (hk : k ≤ 3) (m : Fin k → Fin 2 → ℝ) :
    ((iteratedFDeriv ℝ k a 0 m : imaginaryQuaternions) : ℍ[ℝ]) =
      iteratedFDeriv ℝ k (fun τ => (a τ : ℍ[ℝ])) 0 m := by
  have h := (imaginaryQuaternions.subtypeL).iteratedFDeriv_comp_left ha (i := k) (by exact_mod_cast hk)
  have e : (fun τ => (a τ : ℍ[ℝ])) = imaginaryQuaternions.subtypeL ∘ a := rfl
  rw [e, h]
  rfl
theorem contDiffAt_exponentArgs {u v : (Fin 2 → ℝ) → imaginaryQuaternions} (hu : ContDiffAt ℝ 3 u 0)
    (hv : ContDiffAt ℝ 3 v 0) : ContDiffAt ℝ 3 (exponentArgs u v) 0 :=
  (imaginaryQuaternions.subtypeL.contDiff.contDiffAt.comp 0 hu).prodMk
    ((imaginaryQuaternions.subtypeL.contDiff.contDiffAt.comp 0 hv).prodMk contDiffAt_const)
theorem iteratedFDeriv_exponentArgs {u v : (Fin 2 → ℝ) → imaginaryQuaternions} (hu : ContDiffAt ℝ 3 u 0)
    (hv : ContDiffAt ℝ 3 v 0) {k : ℕ} (hk0 : k ≠ 0) (hk : k ≤ 3) (m : Fin k → Fin 2 → ℝ) :
    iteratedFDeriv ℝ k (exponentArgs u v) 0 m =
      (((iteratedFDeriv ℝ k u 0 m : imaginaryQuaternions) : ℍ[ℝ]),
        ((iteratedFDeriv ℝ k v 0 m : imaginaryQuaternions) : ℍ[ℝ]), 0) := by
  have hZ := contDiffAt_exponentArgs hu hv
  have h1 := (ContinuousLinearMap.fst ℝ ℍ[ℝ] (ℍ[ℝ] × ℍ[ℝ])).iteratedFDeriv_comp_left hZ (i := k) (by exact_mod_cast hk)
  have h2 := ((ContinuousLinearMap.fst ℝ ℍ[ℝ] ℍ[ℝ]).comp (ContinuousLinearMap.snd ℝ ℍ[ℝ] (ℍ[ℝ] × ℍ[ℝ]))).iteratedFDeriv_comp_left hZ (i := k) (by exact_mod_cast hk)
  have h3 := ((ContinuousLinearMap.snd ℝ ℍ[ℝ] ℍ[ℝ]).comp (ContinuousLinearMap.snd ℝ ℍ[ℝ] (ℍ[ℝ] × ℍ[ℝ]))).iteratedFDeriv_comp_left hZ (i := k) (by exact_mod_cast hk)
  have e1 : (ContinuousLinearMap.fst ℝ ℍ[ℝ] (ℍ[ℝ] × ℍ[ℝ])) ∘ exponentArgs u v = fun τ => (u τ : ℍ[ℝ]) := rfl
  have e2 : ((ContinuousLinearMap.fst ℝ ℍ[ℝ] ℍ[ℝ]).comp (ContinuousLinearMap.snd ℝ ℍ[ℝ] (ℍ[ℝ] × ℍ[ℝ]))) ∘ exponentArgs u v =
      fun τ => (v τ : ℍ[ℝ]) := rfl
  have e3 : ((ContinuousLinearMap.snd ℝ ℍ[ℝ] ℍ[ℝ]).comp (ContinuousLinearMap.snd ℝ ℍ[ℝ] (ℍ[ℝ] × ℍ[ℝ]))) ∘ exponentArgs u v =
      fun _ => (u 0 : ℍ[ℝ]) := rfl
  rw [e1] at h1
  rw [e2] at h2
  rw [e3, iteratedFDeriv_const_of_ne hk0] at h3
  have g1 := congrArg (fun M => M m) h1
  have g2 := congrArg (fun M => M m) h2
  have g3 := congrArg (fun M => M m) h3
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'] at g1 g2 g3
  rw [← coe_iteratedFDeriv_imaginary hu hk] at g1
  rw [← coe_iteratedFDeriv_imaginary hv hk] at g2
  refine Prod.ext g1.symm (Prod.ext g2.symm ?_)
  simpa using g3.symm
theorem inv_expUnit (w : imaginaryQuaternions) : ((expUnit w)⁻¹ : UnitQuaternion) = expUnit (- w) := by apply _root_.YangMills.Construction.LeastQuarticGauge.expUnit_inv <;> assumption
theorem coe_iteratedFDeriv_eq_chainRule (hC : ThirdOrderChainRuleVectorValued)
    {a u v : (Fin 2 → ℝ) → imaginaryQuaternions} (ha0 : a 0 = 0)
    (hv0 : v 0 = 0) (hCa : ContDiffAt ℝ 3 a 0) (hCu : ContDiffAt ℝ 3 u 0) (hCv : ContDiffAt ℝ 3 v 0)
    (hE : ∀ᶠ τ in 𝓝 (0 : Fin 2 → ℝ), expUnit (a τ) = expUnit (u τ) * expUnit (v τ) * (expUnit (u 0))⁻¹)
    (w w' : Fin 2 → ℝ) :
    ((iteratedFDeriv ℝ 1 a 0 ![w] : imaginaryQuaternions) : ℍ[ℝ]) =
        iteratedFDeriv ℝ 1 tripleExpProduct (exponentArgs u v 0)
          ![iteratedFDeriv ℝ 1 (exponentArgs u v) 0 ![w]] ∧
      ((iteratedFDeriv ℝ 2 a 0 ![w, w'] : imaginaryQuaternions) : ℍ[ℝ]) =
        iteratedFDeriv ℝ 2 tripleExpProduct (exponentArgs u v 0)
            ![iteratedFDeriv ℝ 1 (exponentArgs u v) 0 ![w], iteratedFDeriv ℝ 1 (exponentArgs u v) 0 ![w']] +
          iteratedFDeriv ℝ 1 tripleExpProduct (exponentArgs u v 0)
            ![iteratedFDeriv ℝ 2 (exponentArgs u v) 0 ![w, w']] -
          iteratedFDeriv ℝ 2 (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) 0
            ![((iteratedFDeriv ℝ 1 a 0 ![w] : imaginaryQuaternions) : ℍ[ℝ]),
              ((iteratedFDeriv ℝ 1 a 0 ![w'] : imaginaryQuaternions) : ℍ[ℝ])] := by
  set ca : (Fin 2 → ℝ) → ℍ[ℝ] := fun τ => (a τ : ℍ[ℝ]) with hca
  have hcaC : ContDiffAt ℝ 3 ca 0 := imaginaryQuaternions.subtypeL.contDiff.contDiffAt.comp 0 hCa
  have hca0 : ca 0 = 0 := by
    simp [hca, ha0]
  have hexpC : ContDiffAt ℝ 3 (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) (ca 0) := (contDiff_exp_quaternion 3).contDiffAt
  have T := hC NormedSpace.exp ca 0 hexpC hcaC
  have T' := hC tripleExpProduct (exponentArgs u v) 0 (contDiff_tripleExpProduct 3).contDiffAt
    (contDiffAt_exponentArgs hCu hCv)
  have hEv : (NormedSpace.exp ∘ ca) =ᶠ[𝓝 0] tripleExpProduct ∘ exponentArgs u v := by
    filter_upwards [hE] with τ hτ
    have h1 := congrArg (fun g : UnitQuaternion => (g : ℍ[ℝ])) hτ
    rw [inv_expUnit] at h1
    exact h1
  have e1 := (Filter.EventuallyEq.iteratedFDeriv ℝ hEv 1).eq_of_nhds
  have e2 := (Filter.EventuallyEq.iteratedFDeriv ℝ hEv 2).eq_of_nhds
  have hone : ∀ q : ℍ[ℝ], iteratedFDeriv ℝ 1 (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) 0 ![q] = q := by
    intro q
    rw [iteratedFDeriv_one_apply, (hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := ℍ[ℝ])).fderiv]
    simp
  have hfirst : ∀ x : Fin 2 → ℝ, iteratedFDeriv ℝ 1 ca 0 ![x] =
      iteratedFDeriv ℝ 1 tripleExpProduct (exponentArgs u v 0) ![iteratedFDeriv ℝ 1 (exponentArgs u v) 0 ![x]] := by
    intro x
    have h1 := T.2.1 x
    have h2 := T'.2.1 x
    rw [hca0, hone] at h1
    rw [← h1, e1, h2]
  refine ⟨?_, ?_⟩
  · rw [coe_iteratedFDeriv_imaginary hCa (by norm_num)]
    exact hfirst w
  · rw [coe_iteratedFDeriv_imaginary hCa (by norm_num), coe_iteratedFDeriv_imaginary hCa (by norm_num),
      coe_iteratedFDeriv_imaginary hCa (by norm_num)]
    have h1 := T.2.2.1 w w'
    have h2 := T'.2.2.1 w w'
    rw [hca0, hone] at h1
    rw [e2, h2] at h1
    rw [eq_sub_iff_add_eq]
    simpa [add_comm] using h1.symm
theorem chainRule_values_close {D H : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup H]
    [NormedSpace ℝ H]
    (Φ₁ Φ₁' : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => D) H) (Φ₂ Φ₂' : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => D) H)
    (B : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => H) H) (x y x' y' s s' : D) (p₀ p₁ p₀' p₁' q q' : H) (A K ε : ℝ)
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hε : 0 ≤ ε) (h1 : ‖Φ₁'‖ ≤ A) (h2 : ‖Φ₂'‖ ≤ A) (h3 : ‖Φ₁ - Φ₁'‖ ≤ A * ε)
    (h4 : ‖Φ₂ - Φ₂'‖ ≤ A * ε) (h1' : ‖Φ₁‖ ≤ A) (hx : ‖x‖ ≤ K) (hy : ‖y‖ ≤ K) (hx' : ‖x'‖ ≤ K) (hy' : ‖y'‖ ≤ K)
    (hs : ‖s‖ ≤ K)
    (hxx : ‖x - x'‖ ≤ ε) (hyy : ‖y - y'‖ ≤ ε) (hss : ‖s - s'‖ ≤ ε)
    (ep₀ : p₀ = Φ₁ ![x]) (ep₁ : p₁ = Φ₁ ![y]) (ep₀' : p₀' = Φ₁' ![x']) (ep₁' : p₁' = Φ₁' ![y'])
    (eq : q = Φ₂ ![x, y] + Φ₁ ![s] - B ![p₀, p₁]) (eq' : q' = Φ₂' ![x', y'] + Φ₁' ![s'] - B ![p₀', p₁']) :
    ‖p₀ - p₀'‖ ≤ (A * K + A) * ε ∧ ‖p₁ - p₁'‖ ≤ (A * K + A) * ε ∧
      ‖q - q'‖ ≤ (A * K * K + 2 * A * K + A * K + A + ‖B‖ * (2 * (A * K) * (A * K + A))) * ε := by
  have hone : ∀ (u u' : D), ‖u‖ ≤ K → ‖u - u'‖ ≤ ε → ‖Φ₁ ![u] - Φ₁' ![u']‖ ≤ (A * K + A) * ε := by
    intro u u' hu huu
    have e : Φ₁ ![u] - Φ₁' ![u'] = (Φ₁ - Φ₁') ![u] + Φ₁' ![u - u'] := by
      rw [← apply_single_sub]
      simp
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have b1 := (norm_apply_single_le (Φ₁ - Φ₁') u).trans (mul_le_mul h3 hu (norm_nonneg _) (by positivity))
    have b2 := (norm_apply_single_le Φ₁' (u - u')).trans (mul_le_mul h1 huu (norm_nonneg _) hA)
    nlinarith
  have hp₀ : ‖p₀ - p₀'‖ ≤ (A * K + A) * ε := by
    rw [ep₀, ep₀']
    exact hone _ _ hx hxx
  have hp₁ : ‖p₁ - p₁'‖ ≤ (A * K + A) * ε := by
    rw [ep₁, ep₁']
    exact hone _ _ hy hyy
  refine ⟨hp₀, hp₁, ?_⟩
  have hn₀ : ‖p₀‖ ≤ A * K := by
    rw [ep₀]
    exact (norm_apply_single_le _ _).trans (mul_le_mul h1' hx (norm_nonneg _) hA)
  have hn₁' : ‖p₁'‖ ≤ A * K := by
    rw [ep₁']
    exact (norm_apply_single_le _ _).trans (mul_le_mul h1 hy' (norm_nonneg _) hA)
  have hs1 := hone s s' hs hss
  have e2 : Φ₂ ![x, y] - Φ₂' ![x', y'] = (Φ₂ - Φ₂') ![x, y] + (Φ₂' ![x - x', y] + Φ₂' ![x', y - y']) := by
    rw [← apply_pair_sub]
    simp
  have b1 : ‖Φ₂ ![x, y] - Φ₂' ![x', y']‖ ≤ (A * K * K + 2 * A * K) * ε := by
    rw [e2]
    refine (norm_add_le _ _).trans ?_
    have c1 := norm_apply_pair_le (Φ₂ - Φ₂') x y
    have c2 : ‖Φ₂' ![x - x', y]‖ ≤ A * ε * K := (norm_apply_pair_le _ _ _).trans
      (mul_le_mul (mul_le_mul h2 hxx (norm_nonneg _) hA) hy (norm_nonneg _) (by positivity))
    have c3 : ‖Φ₂' ![x', y - y']‖ ≤ A * K * ε := (norm_apply_pair_le _ _ _).trans
      (mul_le_mul (mul_le_mul h2 hx' (norm_nonneg _) hA) hyy (norm_nonneg _) (by positivity))
    have c4 : ‖Φ₂ - Φ₂'‖ * ‖x‖ * ‖y‖ ≤ A * ε * K * K :=
      mul_le_mul (mul_le_mul h4 hx (norm_nonneg _) (by positivity)) hy (norm_nonneg _) (by positivity)
    have c5 := norm_add_le (Φ₂' ![x - x', y]) (Φ₂' ![x', y - y'])
    nlinarith
  have b3 : ‖B ![p₀, p₁] - B ![p₀', p₁']‖ ≤ ‖B‖ * (2 * (A * K) * (A * K + A)) * ε := by
    rw [apply_pair_sub]
    refine (norm_add_le _ _).trans ?_
    have c2 : ‖B ![p₀ - p₀', p₁]‖ ≤ ‖B‖ * ((A * K + A) * ε) * (A * K) := by
      have hn₁ : ‖p₁‖ ≤ A * K := by
        rw [ep₁]
        exact (norm_apply_single_le _ _).trans (mul_le_mul h1' hy (norm_nonneg _) hA)
      exact (norm_apply_pair_le _ _ _).trans (mul_le_mul (mul_le_mul le_rfl hp₀ (norm_nonneg _) (norm_nonneg _)) hn₁
        (norm_nonneg _) (by positivity))
    have c3 : ‖B ![p₀', p₁ - p₁']‖ ≤ ‖B‖ * (A * K) * ((A * K + A) * ε) := by
      have hn₀' : ‖p₀'‖ ≤ A * K := by
        rw [ep₀']
        exact (norm_apply_single_le _ _).trans (mul_le_mul h1 hx' (norm_nonneg _) hA)
      exact (norm_apply_pair_le _ _ _).trans (mul_le_mul (mul_le_mul le_rfl hn₀' (norm_nonneg _) (norm_nonneg _)) hp₁
        (norm_nonneg _) (by positivity))
    nlinarith
  have e3 : q - q' = (Φ₂ ![x, y] - Φ₂' ![x', y']) + (Φ₁ ![s] - Φ₁' ![s']) - (B ![p₀, p₁] - B ![p₀', p₁']) := by
    rw [eq, eq']
    abel
  rw [e3]
  have n1 := norm_sub_le ((Φ₂ ![x, y] - Φ₂' ![x', y']) + (Φ₁ ![s] - Φ₁' ![s'])) (B ![p₀, p₁] - B ![p₀', p₁'])
  have n2 := norm_add_le (Φ₂ ![x, y] - Φ₂' ![x', y']) (Φ₁ ![s] - Φ₁' ![s'])
  nlinarith
theorem norm_exponentArgs_zero_le {u v : (Fin 2 → ℝ) → imaginaryQuaternions} (hv0 : v 0 = 0) (hu : ‖u 0‖ ≤ 1) :
    ‖exponentArgs u v 0‖ ≤ 1 := by
  have e : ‖(v 0 : ℍ[ℝ])‖ = 0 := by simp [hv0]
  have e2 : ‖((u 0 : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ 1 := hu
  simp only [exponentArgs, Prod.norm_def]
  exact max_le e2 (max_le (by rw [e]; norm_num) e2)
theorem mixedPartial_single (p : (Fin 2 → ℝ) → imaginaryQuaternions) (l : Fin 2) :
    mixedPartial p ![l] = iteratedFDeriv ℝ 1 p 0 ![Pi.single l 1] := by
  unfold mixedPartial
  congr 1
  funext m
  fin_cases m
  rfl
theorem mixedPartial_pair (p : (Fin 2 → ℝ) → imaginaryQuaternions) :
    mixedPartial p ![0, 1] = iteratedFDeriv ℝ 2 p 0 ![Pi.single 0 1, Pi.single 1 1] := by
  unfold mixedPartial
  congr 1
  funext m
  fin_cases m <;> rfl
end TwoCurves
open TwoCurves in
theorem conjugatedCurveDerivStability_of_chainRule (hC : ThirdOrderChainRuleVectorValued) :
    ConjugatedCurveDerivStability := by
  intro K hK
  have hc1 : ContDiff ℝ 1 (iteratedFDeriv ℝ 1 tripleExpProduct) :=
    (contDiff_tripleExpProduct 3).iteratedFDeriv_right (by norm_num)
  have hc2 : ContDiff ℝ 1 (iteratedFDeriv ℝ 2 tripleExpProduct) :=
    (contDiff_tripleExpProduct 3).iteratedFDeriv_right (by norm_num)
  obtain ⟨A₁, hA₁, b₁, l₁⟩ := exists_bound_lipschitz_closedBall hc1
  obtain ⟨A₂, hA₂, b₂, l₂⟩ := exists_bound_lipschitz_closedBall hc2
  set A : ℝ := max A₁ A₂ with hAdef
  have hA : 0 ≤ A := le_max_of_le_left hA₁
  set B := iteratedFDeriv ℝ 2 (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) 0 with hB
  set K' : ℝ := 2 * K with hK'
  set c₁ : ℝ := A * K + A with hc₁
  set c₂ : ℝ := A * K * K + 2 * A * K + A * K + A + ‖B‖ * (2 * (A * K) * (A * K + A)) with hc₂
  have hc₁n : 0 ≤ c₁ := by positivity
  have hc₂n : 0 ≤ c₂ := by positivity
  refine ⟨c₁ + c₂, by positivity, ?_⟩
  intro a a' u u' v ε hε ha0 ha'0 hv0 hCa hCa' hCu hCu' hCv hE hE' hu hu' hKu hKu' hKv hKu2 hKu2' hKv2 hd0 hd1 hd2
  set e₀ : Fin 2 → ℝ := Pi.single 0 1 with he₀
  set e₁ : Fin 2 → ℝ := Pi.single 1 1 with he₁
  obtain ⟨f₀, f₂⟩ := coe_iteratedFDeriv_eq_chainRule hC ha0 hv0 hCa hCu hCv hE e₀ e₁
  obtain ⟨f₁, -⟩ := coe_iteratedFDeriv_eq_chainRule hC ha0 hv0 hCa hCu hCv hE e₁ e₀
  obtain ⟨f₀', f₂'⟩ := coe_iteratedFDeriv_eq_chainRule hC ha'0 hv0 hCa' hCu' hCv hE' e₀ e₁
  obtain ⟨f₁', -⟩ := coe_iteratedFDeriv_eq_chainRule hC ha'0 hv0 hCa' hCu' hCv hE' e₁ e₀
  have hz := norm_exponentArgs_zero_le hv0 hu
  have hz' := norm_exponentArgs_zero_le hv0 hu'
  have hzz : ‖exponentArgs u v 0 - exponentArgs u' v 0‖ ≤ ε := by
    have e1 : ‖(u 0 : ℍ[ℝ]) - (u' 0 : ℍ[ℝ])‖ ≤ ε := hd0
    simp only [exponentArgs, Prod.norm_def, Prod.fst_sub, Prod.snd_sub, sub_self, norm_zero]
    exact max_le e1 (max_le hε e1)
  have hnorm : ∀ {k : ℕ} (hk0 : k ≠ 0) (hk : k ≤ 3) (m : Fin k → Fin 2 → ℝ)
      {p : (Fin 2 → ℝ) → imaginaryQuaternions} (hp : ContDiffAt ℝ 3 p 0),
      ‖iteratedFDeriv ℝ k p 0 m‖ ≤ K → ‖iteratedFDeriv ℝ k v 0 m‖ ≤ K →
      ‖iteratedFDeriv ℝ k (exponentArgs p v) 0 m‖ ≤ K := by
    intro k hk0 hk m p hp h1 h2
    rw [iteratedFDeriv_exponentArgs hp hCv hk0 hk]
    simp only [Prod.norm_def, norm_zero]
    exact max_le h1 (max_le h2 hK)
  have hdiff : ∀ {k : ℕ} (hk0 : k ≠ 0) (hk : k ≤ 3) (m : Fin k → Fin 2 → ℝ),
      ‖iteratedFDeriv ℝ k u 0 m - iteratedFDeriv ℝ k u' 0 m‖ ≤ ε →
      ‖iteratedFDeriv ℝ k (exponentArgs u v) 0 m - iteratedFDeriv ℝ k (exponentArgs u' v) 0 m‖ ≤ ε := by
    intro k hk0 hk m h1
    rw [iteratedFDeriv_exponentArgs hCu hCv hk0 hk, iteratedFDeriv_exponentArgs hCu' hCv hk0 hk]
    simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, sub_self, norm_zero]
    exact max_le h1 hε
  have hKu'0 : ∀ l, ‖iteratedFDeriv ℝ 1 u 0 ![Pi.single l 1]‖ ≤ K := fun l => by
    rw [← mixedPartial_single]; exact hKu l
  have hKu'1 : ∀ l, ‖iteratedFDeriv ℝ 1 u' 0 ![Pi.single l 1]‖ ≤ K := fun l => by
    rw [← mixedPartial_single]; exact hKu' l
  have hKv' : ∀ l, ‖iteratedFDeriv ℝ 1 v 0 ![Pi.single l 1]‖ ≤ K := fun l => by
    rw [← mixedPartial_single]; exact hKv l
  have hd1' : ∀ l, ‖iteratedFDeriv ℝ 1 u 0 ![Pi.single l 1] - iteratedFDeriv ℝ 1 u' 0 ![Pi.single l 1]‖ ≤ ε :=
    fun l => by rw [← mixedPartial_single, ← mixedPartial_single]; exact hd1 l
  have hres := chainRule_values_close
    (iteratedFDeriv ℝ 1 tripleExpProduct (exponentArgs u v 0)) (iteratedFDeriv ℝ 1 tripleExpProduct (exponentArgs u' v 0))
    (iteratedFDeriv ℝ 2 tripleExpProduct (exponentArgs u v 0)) (iteratedFDeriv ℝ 2 tripleExpProduct (exponentArgs u' v 0)) B
    (iteratedFDeriv ℝ 1 (exponentArgs u v) 0 ![e₀]) (iteratedFDeriv ℝ 1 (exponentArgs u v) 0 ![e₁])
    (iteratedFDeriv ℝ 1 (exponentArgs u' v) 0 ![e₀]) (iteratedFDeriv ℝ 1 (exponentArgs u' v) 0 ![e₁])
    (iteratedFDeriv ℝ 2 (exponentArgs u v) 0 ![e₀, e₁]) (iteratedFDeriv ℝ 2 (exponentArgs u' v) 0 ![e₀, e₁])
    ((iteratedFDeriv ℝ 1 a 0 ![e₀] : imaginaryQuaternions) : ℍ[ℝ])
    ((iteratedFDeriv ℝ 1 a 0 ![e₁] : imaginaryQuaternions) : ℍ[ℝ])
    ((iteratedFDeriv ℝ 1 a' 0 ![e₀] : imaginaryQuaternions) : ℍ[ℝ])
    ((iteratedFDeriv ℝ 1 a' 0 ![e₁] : imaginaryQuaternions) : ℍ[ℝ])
    ((iteratedFDeriv ℝ 2 a 0 ![e₀, e₁] : imaginaryQuaternions) : ℍ[ℝ])
    ((iteratedFDeriv ℝ 2 a' 0 ![e₀, e₁] : imaginaryQuaternions) : ℍ[ℝ])
    A K ε hA hK hε ((b₁ _ hz').trans (le_max_left _ _)) ((b₂ _ hz').trans (le_max_right _ _))
    ((l₁ _ _ hz hz').trans (mul_le_mul (le_max_left _ _) hzz (norm_nonneg _) hA))
    ((l₂ _ _ hz hz').trans (mul_le_mul (le_max_right _ _) hzz (norm_nonneg _) hA))
    ((b₁ _ hz).trans (le_max_left _ _))
    (hnorm (by norm_num) (by norm_num) _ hCu (hKu'0 0) (hKv' 0))
    (hnorm (by norm_num) (by norm_num) _ hCu (hKu'0 1) (hKv' 1))
    (hnorm (by norm_num) (by norm_num) _ hCu' (hKu'1 0) (hKv' 0))
    (hnorm (by norm_num) (by norm_num) _ hCu' (hKu'1 1) (hKv' 1))
    (hnorm (by norm_num) (by norm_num) _ hCu (by rw [← mixedPartial_pair]; exact hKu2)
      (by rw [← mixedPartial_pair]; exact hKv2))
    (hdiff (by norm_num) (by norm_num) _ (hd1' 0)) (hdiff (by norm_num) (by norm_num) _ (hd1' 1))
    (hdiff (by norm_num) (by norm_num) _ (by rw [← mixedPartial_pair, ← mixedPartial_pair]; exact hd2))
    f₀ f₁ f₀' f₁' f₂ f₂'
  obtain ⟨r₀, r₁, r₂⟩ := hres
  have hsub : ∀ x y : imaginaryQuaternions, ‖x - y‖ = ‖(x : ℍ[ℝ]) - (y : ℍ[ℝ])‖ := fun _ _ => rfl
  refine ⟨fun l => ?_, ?_⟩
  · rw [mixedPartial_single, mixedPartial_single, hsub]
    fin_cases l
    · exact r₀.trans (mul_le_mul_of_nonneg_right (by linarith) hε)
    · exact r₁.trans (mul_le_mul_of_nonneg_right (by linarith) hε)
  · rw [mixedPartial_pair, mixedPartial_pair, hsub]
    exact r₂.trans (mul_le_mul_of_nonneg_right (by linarith) hε)
end YangMills.Construction.ColdStepAtMirrorFrames
end
