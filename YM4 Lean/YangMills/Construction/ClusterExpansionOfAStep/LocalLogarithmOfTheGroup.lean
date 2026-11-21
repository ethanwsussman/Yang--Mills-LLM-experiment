import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace QuaternionLog
open BlockAverages TorusFields
instance : FiniteDimensional ℝ imaginaryQuaternions := inferInstance
instance : CompleteSpace imaginaryQuaternions := FiniteDimensional.complete ℝ imaginaryQuaternions
def imPartLinear : ℍ[ℝ] →ₗ[ℝ] imaginaryQuaternions where
  toFun q := ⟨q.im, Quaternion.re_im q⟩
  map_add' a b := by
    apply Subtype.ext
    simp
  map_smul' c a := by
    apply Subtype.ext
    simp [Quaternion.im_smul]
def imPartL : ℍ[ℝ] →L[ℝ] imaginaryQuaternions := LinearMap.toContinuousLinearMap imPartLinear
theorem coe_imPartL (q : ℍ[ℝ]) : ((imPartL q : imaginaryQuaternions) : ℍ[ℝ]) = q.im := rfl
theorem contDiff_quaternionExp {k : WithTop ℕ∞} : ContDiff ℝ k (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) :=
  AnalyticOnNhd.contDiff fun x _ => NormedSpace.exp_analytic x
def imExp (w : imaginaryQuaternions) : imaginaryQuaternions := imPartL (NormedSpace.exp (w : ℍ[ℝ]))
theorem contDiff_imExp {k : WithTop ℕ∞} : ContDiff ℝ k imExp :=
  imPartL.contDiff.comp (contDiff_quaternionExp.comp imaginaryQuaternions.subtypeL.contDiff)
theorem imExp_zero : imExp 0 = 0 := by
  apply Subtype.ext
  simp [imExp, coe_imPartL]
theorem imPartL_coe (w : imaginaryQuaternions) : imPartL (w : ℍ[ℝ]) = w := by
  apply Subtype.ext
  rw [coe_imPartL]
  have hw : (w : ℍ[ℝ]).re = 0 := w.2
  ext <;> simp [hw]
theorem hasFDerivAt_imExp_zero :
    HasFDerivAt imExp
      ((ContinuousLinearEquiv.refl ℝ imaginaryQuaternions : imaginaryQuaternions ≃L[ℝ] imaginaryQuaternions) :
        imaginaryQuaternions →L[ℝ] imaginaryQuaternions) 0 := by
  have h1 : HasFDerivAt (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) (1 : ℍ[ℝ] →L[ℝ] ℍ[ℝ])
      (imaginaryQuaternions.subtypeL 0) := by
    simpa using (hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := ℍ[ℝ])).hasFDerivAt
  have h2 := imPartL.hasFDerivAt.comp (0 : imaginaryQuaternions)
    (h1.comp (0 : imaginaryQuaternions) imaginaryQuaternions.subtypeL.hasFDerivAt)
  have e : ((ContinuousLinearEquiv.refl ℝ imaginaryQuaternions : imaginaryQuaternions ≃L[ℝ] imaginaryQuaternions) :
        imaginaryQuaternions →L[ℝ] imaginaryQuaternions) =
      imPartL.comp ((1 : ℍ[ℝ] →L[ℝ] ℍ[ℝ]).comp imaginaryQuaternions.subtypeL) := by
    ext1 w
    exact (imPartL_coe w).symm
  rw [e]
  exact h2
theorem exists_logNearOne : ∃ lg : ℍ[ℝ] → imaginaryQuaternions, lg 1 = 0 ∧ ContDiffAt ℝ 3 lg 1 ∧
    ∀ᶠ q in nhds (1 : ℍ[ℝ]), ‖q‖ = 1 → NormedSpace.exp ((lg q : imaginaryQuaternions) : ℍ[ℝ]) = q := by
  have hc : ContDiffAt ℝ 3 imExp 0 := contDiff_imExp.contDiffAt
  have hn : (3 : WithTop ℕ∞) ≠ 0 := by norm_num
  have hf' := hasFDerivAt_imExp_zero
  set g := hc.localInverse hf' hn with hg
  have gC : ContDiffAt ℝ 3 g (imExp 0) := hc.to_localInverse hf' hn
  rw [imExp_zero] at gC
  have g0 : g 0 = 0 := by
    have := hc.localInverse_apply_image hf' hn
    rwa [imExp_zero] at this
  have im1 : imPartL 1 = 0 := by
    apply Subtype.ext
    simp [coe_imPartL]
  have hr : ∀ᶠ y in nhds (0 : imaginaryQuaternions), imExp (g y) = y := by
    have := (hc.hasStrictFDerivAt' hf' hn).eventually_right_inverse
    rwa [imExp_zero] at this
  refine ⟨fun q => g (imPartL q), by simp [im1, g0], ?_, ?_⟩
  · have h1 : ContDiffAt ℝ 3 g (imPartL 1) := by rwa [im1]
    exact h1.comp (1 : ℍ[ℝ]) imPartL.contDiff.contDiffAt
  · have tim : Filter.Tendsto (fun q : ℍ[ℝ] => imPartL q) (nhds 1) (nhds 0) := by
      have := imPartL.continuous.tendsto (1 : ℍ[ℝ])
      rwa [im1] at this
    have ev1 : ∀ᶠ q in nhds (1 : ℍ[ℝ]), imExp (g (imPartL q)) = imPartL q := tim.eventually hr
    have gt : Filter.Tendsto (fun q : ℍ[ℝ] => g (imPartL q)) (nhds 1) (nhds 0) := by
      have := gC.continuousAt.tendsto
      rw [g0] at this
      exact this.comp tim
    have te : Filter.Tendsto (fun w : imaginaryQuaternions => NormedSpace.exp (w : ℍ[ℝ])) (nhds 0) (nhds 1) := by
      have hcont : Continuous fun w : imaginaryQuaternions => NormedSpace.exp (w : ℍ[ℝ]) :=
        (contDiff_quaternionExp (k := 0)).continuous.comp continuous_subtype_val
      have := hcont.tendsto (0 : imaginaryQuaternions)
      simpa using this
    have tE := te.comp gt
    have tre : Filter.Tendsto
        (fun q : ℍ[ℝ] => (NormedSpace.exp ((g (imPartL q) : imaginaryQuaternions) : ℍ[ℝ])).re)
        (nhds 1) (nhds 1) := by
      have := (Quaternion.continuous_re.tendsto (1 : ℍ[ℝ])).comp tE
      simpa [Function.comp_def] using this
    have ev2 : ∀ᶠ q in nhds (1 : ℍ[ℝ]),
        0 < (NormedSpace.exp ((g (imPartL q) : imaginaryQuaternions) : ℍ[ℝ])).re :=
      tre.eventually (lt_mem_nhds one_pos)
    have ev3 : ∀ᶠ q in nhds (1 : ℍ[ℝ]), 0 < q.re := by
      have : Filter.Tendsto (fun q : ℍ[ℝ] => q.re) (nhds 1) (nhds 1) := by
        have := Quaternion.continuous_re.tendsto (1 : ℍ[ℝ])
        simpa using this
      exact this.eventually (lt_mem_nhds one_pos)
    filter_upwards [ev1, ev2, ev3] with q h1 h2 h3 hq
    set E : ℍ[ℝ] := NormedSpace.exp ((g (imPartL q) : imaginaryQuaternions) : ℍ[ℝ]) with hE
    have hEn : ‖E‖ = 1 := norm_unitQuaternion (expUnit (g (imPartL q)))
    have him : E.im = q.im := by
      have := congrArg (fun w : imaginaryQuaternions => (w : ℍ[ℝ])) h1
      simpa [imExp, coe_imPartL] using this
    have c1 : E.imI = q.imI := by simpa using congrArg (fun z : ℍ[ℝ] => z.imI) him
    have c2 : E.imJ = q.imJ := by simpa using congrArg (fun z : ℍ[ℝ] => z.imJ) him
    have c3 : E.imK = q.imK := by simpa using congrArg (fun z : ℍ[ℝ] => z.imK) him
    have n1 : Quaternion.normSq E = 1 := by
      rw [Quaternion.normSq_eq_norm_mul_self, hEn]
      norm_num
    have n2 : Quaternion.normSq q = 1 := by
      rw [Quaternion.normSq_eq_norm_mul_self, hq]
      norm_num
    rw [Quaternion.normSq_def'] at n1 n2
    rw [c1, c2, c3] at n1
    have hre : E.re = q.re := by nlinarith
    ext
    · exact hre
    · exact c1
    · exact c2
    · exact c3
def logNearOne : ℍ[ℝ] → imaginaryQuaternions := exists_logNearOne.choose
theorem logNearOne_one : logNearOne 1 = 0 := exists_logNearOne.choose_spec.1
theorem contDiffAt_logNearOne : ContDiffAt ℝ 3 logNearOne 1 := exists_logNearOne.choose_spec.2.1
theorem exp_logNearOne : ∀ᶠ q in nhds (1 : ℍ[ℝ]), ‖q‖ = 1 →
    NormedSpace.exp ((logNearOne q : imaginaryQuaternions) : ℍ[ℝ]) = q := exists_logNearOne.choose_spec.2.2
end QuaternionLog
end YangMills.Construction
end
