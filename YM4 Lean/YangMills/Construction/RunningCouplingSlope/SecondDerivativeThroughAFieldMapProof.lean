import YangMills.Construction.RunningCouplingSlope.CompositionKeepsTheCoefficientProof
import YangMills.Construction.RunningCouplingSlope.SecondDerivativeThroughAFieldMap
import YangMills.Construction.Matrices.UnitQuaternionsAsMatrices
import YangMills.Construction.SummableBoundsOfTheFlow.CoordinatesAtTheFlatField
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open Filter
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames TorusFields FlatFieldJets
namespace PullbackCalculus
section SecondOrderChainRule
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
private theorem fderiv_fderiv_comp_of_fderiv_eq_zero {Ψ : F → ℝ} {w : E → F} (hΨ : ContDiffAt ℝ 2 Ψ 0)
    (hw : ContDiffAt ℝ 2 w 0) (hw0 : w 0 = 0) (hD : fderiv ℝ Ψ 0 = 0) (u v : E) :
    fderiv ℝ (fderiv ℝ (Ψ ∘ w)) 0 u v = fderiv ℝ (fderiv ℝ Ψ) 0 (fderiv ℝ w 0 u) (fderiv ℝ w 0 v) := by apply _root_.YangMills.Construction.SlopeCoefficient.Pullback.fderiv_fderiv_comp_of_fderiv_eq_zero <;> assumption
end SecondOrderChainRule
section QuaternionLogarithm
private def imPartLinear : ℍ[ℝ] →ₗ[ℝ] imaginaryQuaternions where
  toFun q := ⟨q - ((q.re : ℝ) : ℍ[ℝ]), by
    show (q - ((q.re : ℝ) : ℍ[ℝ])).re = 0
    simp⟩
  map_add' a b := by
    apply Subtype.ext
    simp only [Submodule.coe_add]
    ext <;> simp
  map_smul' r a := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, RingHom.id_apply]
    ext <;> simp
private def imPart : ℍ[ℝ] →L[ℝ] imaginaryQuaternions := LinearMap.toContinuousLinearMap imPartLinear
private theorem imPart_apply (q : ℍ[ℝ]) :
    ((imPart q : imaginaryQuaternions) : ℍ[ℝ]) = q - ((q.re : ℝ) : ℍ[ℝ]) := rfl
private theorem imPart_coe (w : imaginaryQuaternions) : imPart (w : ℍ[ℝ]) = w := by
  apply Subtype.ext
  rw [imPart_apply]
  have : (w : ℍ[ℝ]).re = 0 := w.2
  simp [this]
private def imExp (w : imaginaryQuaternions) : imaginaryQuaternions := imPart (NormedSpace.exp (w : ℍ[ℝ]))
private theorem contDiffAt_quatExp (q : ℍ[ℝ]) : ContDiffAt ℝ 2 (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) q :=
  (NormedSpace.exp_analytic (𝕂 := ℝ) q).contDiffAt
private theorem contDiffAt_imExp : ContDiffAt ℝ 2 imExp 0 := by
  have h1 : ContDiffAt ℝ 2 (fun w : imaginaryQuaternions => (w : ℍ[ℝ])) 0 :=
    imaginaryQuaternions.subtypeL.contDiff.contDiffAt
  exact imPart.contDiff.contDiffAt.comp (0 : imaginaryQuaternions) ((contDiffAt_quatExp _).comp (0 : imaginaryQuaternions) h1)
private theorem hasFDerivAt_imExp : HasFDerivAt imExp
    ((ContinuousLinearEquiv.refl ℝ imaginaryQuaternions : imaginaryQuaternions ≃L[ℝ] imaginaryQuaternions) :
      imaginaryQuaternions →L[ℝ] imaginaryQuaternions) 0 := by
  have h1 : HasFDerivAt (fun w : imaginaryQuaternions => (w : ℍ[ℝ])) imaginaryQuaternions.subtypeL 0 :=
    imaginaryQuaternions.subtypeL.hasFDerivAt
  have h2 : HasFDerivAt (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) (1 : ℍ[ℝ] →L[ℝ] ℍ[ℝ])
      (((0 : imaginaryQuaternions) : ℍ[ℝ])) :=
    (hasStrictFDerivAt_exp_zero (𝕂 := ℝ)).hasFDerivAt
  have h3 := imPart.hasFDerivAt.comp (0 : imaginaryQuaternions) (h2.comp (0 : imaginaryQuaternions) h1)
  refine h3.congr_fderiv ?_
  ext w : 1
  simp [imPart_coe]
private def imLog : imaginaryQuaternions → imaginaryQuaternions :=
  contDiffAt_imExp.localInverse hasFDerivAt_imExp (by norm_num)
private theorem imExp_zero : imExp 0 = 0 := by
  apply Subtype.ext
  simp [imExp, imPart_apply]
private theorem contDiffAt_imLog : ContDiffAt ℝ 2 imLog 0 := by
  have := contDiffAt_imExp.to_localInverse hasFDerivAt_imExp (by norm_num)
  rwa [imExp_zero] at this
private theorem imLog_zero : imLog 0 = 0 := by
  have := contDiffAt_imExp.localInverse_apply_image hasFDerivAt_imExp (by norm_num)
  rwa [imExp_zero] at this
private theorem hasFDerivAt_imLog : HasFDerivAt imLog (ContinuousLinearMap.id ℝ imaginaryQuaternions) 0 := by
  have h := ((contDiffAt_imExp.hasStrictFDerivAt' hasFDerivAt_imExp (by norm_num)).to_localInverse).hasFDerivAt
  rw [imExp_zero] at h
  exact h
private theorem imExp_imLog : ∀ᶠ v in 𝓝 (0 : imaginaryQuaternions), imExp (imLog v) = v := by
  have h := (contDiffAt_imExp.hasStrictFDerivAt' hasFDerivAt_imExp (by norm_num)).eventually_right_inverse
  rw [imExp_zero] at h
  exact h
private def quatLog (q : ℍ[ℝ]) : imaginaryQuaternions := imLog (imPart q)
private theorem imPart_one : imPart (1 : ℍ[ℝ]) = 0 := by
  apply Subtype.ext
  simp [imPart_apply]
private theorem quatLog_one : quatLog 1 = 0 := by
  simp [quatLog, imPart_one, imLog_zero]
private theorem contDiffAt_quatLog : ContDiffAt ℝ 2 quatLog 1 := by
  have h := contDiffAt_imLog
  rw [← imPart_one] at h
  exact h.comp (1 : ℍ[ℝ]) imPart.contDiff.contDiffAt
private theorem hasFDerivAt_quatLog : HasFDerivAt quatLog imPart 1 := by
  have h := hasFDerivAt_imLog
  rw [← imPart_one] at h
  have := h.comp (1 : ℍ[ℝ]) imPart.hasFDerivAt
  rw [ContinuousLinearMap.id_comp] at this
  exact this
private theorem eq_of_imPart_eq {a b : ℍ[ℝ]} (ha : Quaternion.normSq a = 1) (hb : Quaternion.normSq b = 1)
    (h : imPart a = imPart b) (pa : 0 < a.re) (pb : 0 < b.re) : a = b := by
  have h' := congrArg (fun w : imaginaryQuaternions => (w : ℍ[ℝ])) h
  simp only [imPart_apply] at h'
  have e1 := congrArg (fun q : ℍ[ℝ] => q.imI) h'
  have e2 := congrArg (fun q : ℍ[ℝ] => q.imJ) h'
  have e3 := congrArg (fun q : ℍ[ℝ] => q.imK) h'
  simp at e1 e2 e3
  rw [Quaternion.normSq_def'] at ha hb
  have e4 : a.re ^ 2 = b.re ^ 2 := by
    rw [e1, e2, e3] at ha
    linarith
  have e5 : a.re = b.re := by
    nlinarith [sq_nonneg (a.re - b.re)]
  ext <;> assumption
private theorem exp_quatLog : ∀ᶠ q in 𝓝 (1 : ℍ[ℝ]), Quaternion.normSq q = 1 →
    NormedSpace.exp ((quatLog q : imaginaryQuaternions) : ℍ[ℝ]) = q := by
  have h1 : Tendsto (fun q : ℍ[ℝ] => imPart q) (𝓝 1) (𝓝 0) := by
    have := imPart.continuous.tendsto (1 : ℍ[ℝ])
    rwa [imPart_one] at this
  have h2 := h1.eventually imExp_imLog
  have h3 : ∀ᶠ q : ℍ[ℝ] in 𝓝 1, 0 < q.re := by
    have hc : Continuous fun q : ℍ[ℝ] => q.re := Quaternion.continuous_re
    exact hc.continuousAt.eventually (lt_mem_nhds (by simp))
  have h4 : ContinuousAt (fun q : ℍ[ℝ] => NormedSpace.exp ((quatLog q : imaginaryQuaternions) : ℍ[ℝ])) 1 := by
    have hc := contDiffAt_quatLog.continuousAt
    have he : ContinuousAt (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) (((quatLog 1 : imaginaryQuaternions) : ℍ[ℝ])) :=
      (contDiffAt_quatExp _).continuousAt
    exact ContinuousAt.comp (f := fun q => ((quatLog q : imaginaryQuaternions) : ℍ[ℝ])) he
      (continuous_subtype_val.continuousAt.comp hc)
  have h5 : ∀ᶠ q : ℍ[ℝ] in 𝓝 1, 0 < (NormedSpace.exp ((quatLog q : imaginaryQuaternions) : ℍ[ℝ])).re := by
    have hc : ContinuousAt (fun q : ℍ[ℝ] => (NormedSpace.exp ((quatLog q : imaginaryQuaternions) : ℍ[ℝ])).re) 1 :=
      Quaternion.continuous_re.continuousAt.comp h4
    refine hc.eventually (lt_mem_nhds ?_)
    simp [quatLog_one]
  filter_upwards [h2, h3, h5] with q a2 a3 a5 hq
  refine eq_of_imPart_eq ?_ hq a2 a5 a3
  have := (expUnit (quatLog q)).2
  exact show Quaternion.normSq (((expUnit (quatLog q) : UnitQuaternion)) : ℍ[ℝ]) = 1 from by
    have h := (Unitary.mem_iff.mp this).1
    rw [Quaternion.star_mul_self] at h
    have h2 := congrArg (fun q : ℍ[ℝ] => q.re) h
    simpa using h2
end QuaternionLogarithm
section ImaginaryUnits
variable {n : ℕ}
private def quatI : ℍ[ℝ] := ⟨0, 1, 0, 0⟩
private def quatJ : ℍ[ℝ] := ⟨0, 0, 1, 0⟩
private def quatK : ℍ[ℝ] := ⟨0, 0, 0, 1⟩
private def quatHalf : ℍ[ℝ] := ⟨1 / 2, 1 / 2, 1 / 2, 1 / 2⟩
private theorem mem_unitary_of_normSq {q : ℍ[ℝ]} (h : Quaternion.normSq q = 1) : q ∈ unitary ℍ[ℝ] := by apply _root_.YangMills.Construction.UnitQuaternions.mem_unitary_of_normSq_eq_one <;> assumption
private def unitI : UnitQuaternion := ⟨quatI, mem_unitary_of_normSq (by rw [Quaternion.normSq_def']; simp [quatI])⟩
private def unitJ : UnitQuaternion := ⟨quatJ, mem_unitary_of_normSq (by rw [Quaternion.normSq_def']; simp [quatJ])⟩
private def e₀ : imaginaryQuaternions := ⟨quatI, rfl⟩
private def e₁ : imaginaryQuaternions := ⟨quatJ, rfl⟩
private def e₂ : imaginaryQuaternions := ⟨quatK, rfl⟩
private theorem adjointAction_coe (u : UnitQuaternion) (X : imaginaryQuaternions) :
    ((_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction u X : imaginaryQuaternions) : ℍ[ℝ]) = (u : ℍ[ℝ]) * (X : ℍ[ℝ]) * star (u : ℍ[ℝ]) := rfl
private theorem adjointAction_I_e₁ : _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction unitI e₁ = -e₁ := by
  apply Subtype.ext
  rw [adjointAction_coe]
  change quatI * quatJ * star quatI = -quatJ
  apply Quaternion.ext <;> simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
      Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star, Quaternion.re_neg,
      Quaternion.imI_neg, Quaternion.imJ_neg, Quaternion.imK_neg] <;> simp [quatI, quatJ, quatK, quatHalf] <;> norm_num
private theorem adjointAction_I_e₂ : _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction unitI e₂ = -e₂ := by
  apply Subtype.ext
  rw [adjointAction_coe]
  change quatI * quatK * star quatI = -quatK
  apply Quaternion.ext <;> simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
      Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star, Quaternion.re_neg,
      Quaternion.imI_neg, Quaternion.imJ_neg, Quaternion.imK_neg] <;> simp [quatI, quatJ, quatK, quatHalf] <;> norm_num
private theorem adjointAction_J_e₀ : _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction unitJ e₀ = -e₀ := by
  apply Subtype.ext
  rw [adjointAction_coe]
  change quatJ * quatI * star quatJ = -quatI
  apply Quaternion.ext <;> simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
      Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star, Quaternion.re_neg,
      Quaternion.imI_neg, Quaternion.imJ_neg, Quaternion.imK_neg] <;> simp [quatI, quatJ, quatK, quatHalf] <;> norm_num
private theorem imaginary_eq_sum (X : imaginaryQuaternions) :
    X = (X : ℍ[ℝ]).imI • e₀ + (X : ℍ[ℝ]).imJ • e₁ + (X : ℍ[ℝ]).imK • e₂ := by
  have hre : (X : ℍ[ℝ]).re = 0 := X.2
  apply Subtype.ext
  simp only [Submodule.coe_add, Submodule.coe_smul]
  apply Quaternion.ext
  · change (X : ℍ[ℝ]).re = (X : ℍ[ℝ]).imI * 0 + (X : ℍ[ℝ]).imJ * 0 + (X : ℍ[ℝ]).imK * 0
    rw [hre]
    ring
  · change (X : ℍ[ℝ]).imI = (X : ℍ[ℝ]).imI * 1 + (X : ℍ[ℝ]).imJ * 0 + (X : ℍ[ℝ]).imK * 0
    ring
  · change (X : ℍ[ℝ]).imJ = (X : ℍ[ℝ]).imI * 0 + (X : ℍ[ℝ]).imJ * 1 + (X : ℍ[ℝ]).imK * 0
    ring
  · change (X : ℍ[ℝ]).imK = (X : ℍ[ℝ]).imI * 0 + (X : ℍ[ℝ]).imJ * 0 + (X : ℍ[ℝ]).imK * 1
    ring
private theorem single_eq_sum (c : TorusBond n) (X : imaginaryQuaternions) :
    (Pi.single c X : TorusBond n → imaginaryQuaternions) =
      (X : ℍ[ℝ]).imI • (Pi.single c e₀ : TorusBond n → imaginaryQuaternions) +
      (X : ℍ[ℝ]).imJ • (Pi.single c e₁ : TorusBond n → imaginaryQuaternions) +
      (X : ℍ[ℝ]).imK • (Pi.single c e₂ : TorusBond n → imaginaryQuaternions) := by
  conv_lhs => rw [imaginary_eq_sum X]
  rw [Pi.single_add, Pi.single_add, Pi.single_smul, Pi.single_smul, Pi.single_smul]
end ImaginaryUnits
section ExponentialChart
variable {m : ℕ} [NeZero m]
private def expChart (g : TorusField m → ℝ) : (TorusBond m → imaginaryQuaternions) → ℝ := fun A => g (expField A)
private theorem contDiffAt_expChart {g : TorusField m → ℝ}
    (hs : ∀ (k : ℕ) (c : Fin k → TorusBond m) (X : Fin k → imaginaryQuaternions),
      ContDiffAt ℝ 2 (fun σ : Fin k → ℝ => g (perturb c X σ (trivialField m))) 0) :
    ContDiffAt ℝ 2 (expChart g) 0 := by
  classical
  let Bs := Module.finBasis ℝ imaginaryQuaternions
  let e := Fintype.equivFin (TorusBond m × Fin (Module.finrank ℝ imaginaryQuaternions))
  let c : Fin (Fintype.card (TorusBond m × Fin (Module.finrank ℝ imaginaryQuaternions))) → TorusBond m :=
    fun l => (e.symm l).1
  let X : Fin (Fintype.card (TorusBond m × Fin (Module.finrank ℝ imaginaryQuaternions))) → imaginaryQuaternions :=
    fun l => Bs (e.symm l).2
  let π₀ : (TorusBond m → imaginaryQuaternions) →ₗ[ℝ]
      (Fin (Fintype.card (TorusBond m × Fin (Module.finrank ℝ imaginaryQuaternions))) → ℝ) :=
    { toFun := fun w l => Bs.coord (e.symm l).2 (w (e.symm l).1)
      map_add' := by
        intro a b
        funext l
        simp
      map_smul' := by
        intro r a
        funext l
        simp }
  let π : (TorusBond m → imaginaryQuaternions) →L[ℝ]
      (Fin (Fintype.card (TorusBond m × Fin (Module.finrank ℝ imaginaryQuaternions))) → ℝ) :=
    LinearMap.toContinuousLinearMap π₀
  have hid : ∀ (w : TorusBond m → imaginaryQuaternions) (b : TorusBond m),
      (∑ l, if c l = b then π w l • X l else 0) = w b := by
    intro w b
    have h1 := Equiv.sum_comp e.symm (fun q : TorusBond m × Fin (Module.finrank ℝ imaginaryQuaternions) =>
      if q.1 = b then (Bs.coord q.2 (w q.1)) • Bs q.2 else 0)
    have h2 : (∑ l, if c l = b then π w l • X l else 0) =
        ∑ l, (fun q : TorusBond m × Fin (Module.finrank ℝ imaginaryQuaternions) =>
          if q.1 = b then (Bs.coord q.2 (w q.1)) • Bs q.2 else 0) (e.symm l) := rfl
    rw [h2, h1, Fintype.sum_prod_type, Finset.sum_eq_single b]
    · simp only [if_true]
      exact Bs.sum_repr (w b)
    · intro b' _ hb
      simp [hb]
    · simp
  have hcomp : expChart g = (fun σ => g (perturb c X σ (trivialField m))) ∘ π := by
    funext w
    simp only [Function.comp, expChart, perturb_trivialField]
    congr 2
    funext b
    rw [perturbationForm_apply, hid]
  rw [hcomp]
  refine ContDiffAt.comp (0 : TorusBond m → imaginaryQuaternions) ?_ π.contDiff.contDiffAt
  simpa using hs _ c X
abbrev _root_.YangMills.DeltaSharedProofs.p502251 := @contDiffAt_expChart
private theorem fderiv_expChart_adjointForm {g : TorusField m → ℝ} (hC : ContDiffAt ℝ 2 (expChart g) 0)
    (hinv : ∀ u : UnitQuaternion, ∀ᶠ V in 𝓝 (trivialField m), g (gaugeTransform (fun _ => u) V) = g V)
    (u : UnitQuaternion) (v : TorusBond m → imaginaryQuaternions) :
    fderiv ℝ (expChart g) 0 (adjointForm u v) = fderiv ℝ (expChart g) 0 v := by
  have hd : DifferentiableAt ℝ (expChart g) 0 := hC.differentiableAt (by simp)
  have hev : (expChart g ∘ adjointForm u) =ᶠ[𝓝 0] expChart g := by
    filter_upwards [tendsto_expField_nhds_zero.eventually (hinv u)] with A hA
    show g (expField (adjointForm u A)) = g (expField A)
    rw [← gaugeTransform_const_expField]
    exact hA
  have h0 : DifferentiableAt ℝ (expChart g) (adjointForm u 0) := by simpa using hd
  have e1 : fderiv ℝ (expChart g ∘ adjointForm u) 0 = (fderiv ℝ (expChart g) 0).comp (adjointForm u) := by
    rw [fderiv_comp 0 h0 (adjointForm u).differentiableAt, (adjointForm u).fderiv]
    simp
  rw [hev.fderiv_eq] at e1
  exact (DFunLike.congr_fun e1 v).symm
private theorem fderiv_expChart_eq_zero {g : TorusField m → ℝ} (hC : ContDiffAt ℝ 2 (expChart g) 0)
    (hinv : ∀ u : UnitQuaternion, ∀ᶠ V in 𝓝 (trivialField m), g (gaugeTransform (fun _ => u) V) = g V) :
    fderiv ℝ (expChart g) 0 = 0 := by
  have h₀ : ∀ c : TorusBond m, fderiv ℝ (expChart g) 0 (Pi.single c e₀) = 0 := by
    intro c
    have h := fderiv_expChart_adjointForm hC hinv unitJ (Pi.single c e₀)
    rw [adjointForm_single, adjointAction_J_e₀, Pi.single_neg, map_neg] at h
    linarith
  have h₁ : ∀ c : TorusBond m, fderiv ℝ (expChart g) 0 (Pi.single c e₁) = 0 := by
    intro c
    have h := fderiv_expChart_adjointForm hC hinv unitI (Pi.single c e₁)
    rw [adjointForm_single, adjointAction_I_e₁, Pi.single_neg, map_neg] at h
    linarith
  have h₂ : ∀ c : TorusBond m, fderiv ℝ (expChart g) 0 (Pi.single c e₂) = 0 := by
    intro c
    have h := fderiv_expChart_adjointForm hC hinv unitI (Pi.single c e₂)
    rw [adjointForm_single, adjointAction_I_e₂, Pi.single_neg, map_neg] at h
    linarith
  ext w
  have e : w = ∑ b, Pi.single b (w b) := (Finset.univ_sum_single w).symm
  rw [e, map_sum]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [single_eq_sum, map_add, map_add, map_smul, map_smul, map_smul, h₀, h₁, h₂]
  simp
private theorem perturb_at_origin {m k : ℕ} (c : Fin k → TorusBond m) (X : Fin k → imaginaryQuaternions) :
    perturb c X 0 (trivialField m) = trivialField m := by apply _root_.YangMills.Construction.RunningCouplingSlope.StepGaugeTotals.perturb_zero_trivialField <;> assumption
private theorem perturb_along_first {m : ℕ} (c c' : TorusBond m) (X X' : imaginaryQuaternions) (s : ℝ) :
    perturb ![c, c'] ![X, X'] (s • Pi.single 0 1) (trivialField m) = perturb ![c] ![X] ![s] (trivialField m) := by apply _root_.YangMills.Construction.SlopeCoefficient.Pullback.perturb_pair_first <;> assumption
private theorem perturb_along_second {m : ℕ} (c c' : TorusBond m) (X X' : imaginaryQuaternions) (s : ℝ) :
    perturb ![c, c'] ![X, X'] (s • Pi.single 1 1) (trivialField m) = perturb ![c'] ![X'] ![s] (trivialField m) := by apply _root_.YangMills.Construction.SlopeCoefficient.Pullback.perturb_pair_second <;> assumption
private theorem mixedDeriv_comp_eq_sum {n : ℕ} [NeZero n] {g : TorusField m → ℝ}
    (hC : ContDiffAt ℝ 2 (expChart g) 0) (h1 : fderiv ℝ (expChart g) 0 = 0) {p : TorusField n → TorusField m}
    {Z : TorusBond n → imaginaryQuaternions → TorusBond m → imaginaryQuaternions} (hp : HasFlatTangents p Z)
    (c c' : TorusBond n) (X X' : imaginaryQuaternions) :
    mixedDeriv (fun V => g (p V)) (trivialField n) ![c, c'] ![X, X'] =
      ∑ b, ∑ b', fderiv ℝ (fderiv ℝ (expChart g)) 0 (Pi.single b (Z c X b)) (Pi.single b' (Z c' X' b')) := by
  classical
  set u : TorusBond m → (Fin 2 → ℝ) → ℍ[ℝ] := fun b σ =>
    ((p (perturb ![c, c'] ![X, X'] σ (trivialField n)) b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) with hu
  have hCu : ∀ b, ContDiffAt ℝ 2 (u b) 0 := fun b => hp.contDiff 2 _ _ b
  have hu0 : ∀ b, u b 0 = 1 := by
    intro b
    simp only [hu, perturb_at_origin, hp.map_trivial, trivialField]
    rfl
  set w : (Fin 2 → ℝ) → TorusBond m → imaginaryQuaternions := fun σ b => quatLog (u b σ) with hw
  have hlog : ∀ b, ContDiffAt ℝ 2 quatLog (u b 0) := fun b => by
    rw [hu0]
    exact contDiffAt_quatLog
  have hwC : ContDiffAt ℝ 2 w 0 := contDiffAt_pi.mpr fun b => (hlog b).comp 0 (hCu b)
  have hw0 : w 0 = 0 := by
    funext b
    simp only [hw, hu0, quatLog_one]
    rfl
  have hcont : ∀ b, Tendsto (u b) (𝓝 0) (𝓝 1) := by
    intro b
    have := (hCu b).continuousAt.tendsto
    rwa [hu0] at this
  have hexp : ∀ᶠ σ in 𝓝 (0 : Fin 2 → ℝ), ∀ b,
      NormedSpace.exp ((w σ b : imaginaryQuaternions) : ℍ[ℝ]) = u b σ := by
    rw [eventually_all]
    intro b
    filter_upwards [(hcont b).eventually exp_quatLog] with σ hσ
    refine hσ ?_
    have hu1 := (p (perturb ![c, c'] ![X, X'] σ (trivialField n)) b.1 b.2).2
    have h := (Unitary.mem_iff.mp hu1).1
    rw [Quaternion.star_mul_self] at h
    have h2 := congrArg (fun q : ℍ[ℝ] => q.re) h
    simpa using h2
  have hev : (fun σ : Fin 2 → ℝ => g (p (perturb ![c, c'] ![X, X'] σ (trivialField n)))) =ᶠ[𝓝 0]
      expChart g ∘ w := by
    filter_upwards [hexp] with σ hσ
    simp only [Function.comp, expChart]
    congr 1
    funext x i
    apply Subtype.ext
    exact (hσ (x, i)).symm
  have hfu : ∀ b, HasFDerivAt (u b) (fderiv ℝ (u b) 0) 0 := fun b =>
    ((hCu b).differentiableAt (by simp)).hasFDerivAt
  have hfw : ∀ b, HasFDerivAt (fun σ => w σ b) (imPart.comp (fderiv ℝ (u b) 0)) 0 := by
    intro b
    have h1 : HasFDerivAt quatLog imPart (u b 0) := by
      rw [hu0]
      exact hasFDerivAt_quatLog
    exact h1.comp 0 (hfu b)
  have hfW : HasFDerivAt w (ContinuousLinearMap.pi fun b => imPart.comp (fderiv ℝ (u b) 0)) 0 :=
    hasFDerivAt_pi.mpr hfw
  have line : ∀ (l : Fin 2) (b : TorusBond m) (v : ℍ[ℝ]),
      HasDerivAt (fun s : ℝ => u b (s • Pi.single l 1)) v 0 →
      fderiv ℝ (u b) 0 (Pi.single l 1) = v := by
    intro l b v hv
    have h0 : HasDerivAt (fun s : ℝ => s • (Pi.single l 1 : Fin 2 → ℝ)) (Pi.single l 1) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const (Pi.single l 1 : Fin 2 → ℝ)
    have h1 : HasFDerivAt (u b) (fderiv ℝ (u b) 0) ((0 : ℝ) • (Pi.single l 1 : Fin 2 → ℝ)) := by
      simpa using hfu b
    have h2 := h1.comp_hasDerivAt (0 : ℝ) h0
    exact h2.unique hv
  have hA : fderiv ℝ w 0 (Pi.single 0 1) = ∑ b, Pi.single b (Z c X b) := by
    rw [hfW.fderiv]
    funext b
    have e := line 0 b _ (by
      have := hp.hasDerivAt_tangent c X b
      simp only [hu, perturb_along_first]
      exact this)
    simp only [ContinuousLinearMap.coe_pi', ContinuousLinearMap.comp_apply, e, imPart_coe, Finset.sum_apply]
    rw [Finset.sum_eq_single b]
    · simp
    · intro b' _ hb
      simp [Pi.single_apply, hb.symm]
    · simp
  have hB : fderiv ℝ w 0 (Pi.single 1 1) = ∑ b, Pi.single b (Z c' X' b) := by
    rw [hfW.fderiv]
    funext b
    have e := line 1 b _ (by
      have := hp.hasDerivAt_tangent c' X' b
      simp only [hu, perturb_along_second]
      exact this)
    simp only [ContinuousLinearMap.coe_pi', ContinuousLinearMap.comp_apply, e, imPart_coe, Finset.sum_apply]
    rw [Finset.sum_eq_single b]
    · simp
    · intro b' _ hb
      simp [Pi.single_apply, hb.symm]
    · simp
  have hlhs : mixedDeriv (fun V => g (p V)) (trivialField n) ![c, c'] ![X, X'] = fderiv ℝ (fderiv ℝ
      (fun σ : Fin 2 → ℝ => g (p (perturb ![c, c'] ![X, X'] σ (trivialField n))))) 0
      (Pi.single 0 1) (Pi.single 1 1) := by
    unfold mixedDeriv
    rw [iteratedFDeriv_two_apply]
  rw [hlhs, hev.fderiv.fderiv_eq]
  have hcz := fderiv_fderiv_comp_of_fderiv_eq_zero hC hwC hw0 h1 (Pi.single 0 1) (Pi.single 1 1)
  rw [hcz, hA, hB]
  simp only [map_sum, ContinuousLinearMap.sum_apply]
  rw [Finset.sum_comm]
end ExponentialChart
end PullbackCalculus
namespace TorusFields
open PullbackCalculus in
theorem secondDerivativePullback_holds : SecondDerivativePullback := by
  intro m _ g hs
  have hC := contDiffAt_expChart hs
  refine ⟨fderiv ℝ (fderiv ℝ (expChart g)) 0, fun b b' Y Y' => ?_, fun hinv n _ p Z hp c c' X X' => ?_⟩
  · rw [mixedDeriv_trivialField g ![b, b'] ![Y, Y'] (by exact_mod_cast hC)]
    rw [iteratedFDeriv_two_apply]
    rfl
  · exact mixedDeriv_comp_eq_sum hC (fderiv_expChart_eq_zero hC hinv) hp c c' X X'
end TorusFields
end YangMills.Construction
end
