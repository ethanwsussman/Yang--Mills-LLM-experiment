import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionUnderAGaugeOfTheTopProof
import YangMills.Construction.ColdStepAtMirrorFrames.JetOfAFunctionOfAField
import YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderKillsGradientsProof
import YangMills.Construction.ColdStepAtMirrorFrames.SumsAgainstFlatResponsesProof
import YangMills.Construction.ColdStepAtMirrorFrames.ThreeDerivativesOfAComposite
import YangMills.Construction.ResponseInTheExpansion.MainTermOfABlockRemainder
import YangMills.Construction.Matrices.UnitQuaternionsAsMatrices
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open Filter
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Estimates GaugeAlongMotion
namespace WeightedResponses
namespace BlockSecondDerivative
variable {F : BlockFrame}
def restrictToBonds (A : F.Site F.depth → Fin 4 → imaginaryQuaternions) :
    ↥(fineBonds F) → imaginaryQuaternions := fun b => A b.1.1 b.1.2
theorem mem_fineBonds (hcov : ∀ x : F.Site F.depth, x ∈ sitesOfCells (finiteCells F) F.depth)
    (x : F.Site F.depth) (i : Fin 4) : (x, i) ∈ fineBonds F := by
  unfold fineBonds
  exact Finset.mem_product.mpr ⟨hcov x, Finset.mem_univ _⟩
theorem extendByZero_restrictToBonds (hcov : ∀ x : F.Site F.depth, x ∈ sitesOfCells (finiteCells F) F.depth)
    (A : F.Site F.depth → Fin 4 → imaginaryQuaternions) : _root_.YangMills.Construction.ColdStepAtMirrorFrames.extendByZero (restrictToBonds A) = A := by
  funext x i
  simp [_root_.YangMills.Construction.ColdStepAtMirrorFrames.extendByZero, restrictToBonds, mem_fineBonds hcov x i]
def jetAtUniform (G : F.GaugeField F.depth → ℝ) : (↥(fineBonds F) → imaginaryQuaternions) → ℝ :=
  formComposition (fineBonds F) G (ColdStepAtMirrorFrames.uniformField F F.depth)
theorem jetAtUniform_restrictToBonds (hcov : ∀ x : F.Site F.depth, x ∈ sitesOfCells (finiteCells F) F.depth)
    (G : F.GaugeField F.depth → ℝ) (A : F.Site F.depth → Fin 4 → imaginaryQuaternions) :
    jetAtUniform G (restrictToBonds A) = G (leftTranslate A (ColdStepAtMirrorFrames.uniformField F F.depth)) := by
  simp [jetAtUniform, formComposition, extendByZero_restrictToBonds hcov]
def quatI : ℍ[ℝ] := ⟨0, 1, 0, 0⟩
def quatJ : ℍ[ℝ] := ⟨0, 0, 1, 0⟩
def quatK : ℍ[ℝ] := ⟨0, 0, 0, 1⟩
@[simp] theorem quatI_re : quatI.re = 0 := rfl
@[simp] theorem quatI_imI : quatI.imI = 1 := rfl
@[simp] theorem quatI_imJ : quatI.imJ = 0 := rfl
@[simp] theorem quatI_imK : quatI.imK = 0 := rfl
@[simp] theorem quatJ_re : quatJ.re = 0 := rfl
@[simp] theorem quatJ_imI : quatJ.imI = 0 := rfl
@[simp] theorem quatJ_imJ : quatJ.imJ = 1 := rfl
@[simp] theorem quatJ_imK : quatJ.imK = 0 := rfl
@[simp] theorem quatK_re : quatK.re = 0 := rfl
@[simp] theorem quatK_imI : quatK.imI = 0 := rfl
@[simp] theorem quatK_imJ : quatK.imJ = 0 := rfl
@[simp] theorem quatK_imK : quatK.imK = 1 := rfl
theorem mem_unitary_of_normSq {q : ℍ[ℝ]} (h : Quaternion.normSq q = 1) : q ∈ unitary ℍ[ℝ] := by apply _root_.YangMills.Construction.UnitQuaternions.mem_unitary_of_normSq_eq_one <;> assumption
theorem quatI_mem : quatI ∈ unitary ℍ[ℝ] := mem_unitary_of_normSq (by simp [Quaternion.normSq_def'])
theorem quatJ_mem : quatJ ∈ unitary ℍ[ℝ] := mem_unitary_of_normSq (by simp [Quaternion.normSq_def'])
theorem quatK_mem : quatK ∈ unitary ℍ[ℝ] := mem_unitary_of_normSq (by simp [Quaternion.normSq_def'])
def unitI : UnitQuaternion := ⟨quatI, quatI_mem⟩
def unitJ : UnitQuaternion := ⟨quatJ, quatJ_mem⟩
def unitK : UnitQuaternion := ⟨quatK, quatK_mem⟩
theorem adjointAction_sum_units (X : imaginaryQuaternions) :
    X + _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction unitI X + _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction unitJ X + _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction unitK X = 0 := by
  apply Subtype.ext
  have hX : (X : ℍ[ℝ]).re = 0 := X.2
  have e1 : ((unitI⁻¹ : UnitQuaternion) : ℍ[ℝ]) = star (unitI : ℍ[ℝ]) := rfl
  have e2 : ((unitJ⁻¹ : UnitQuaternion) : ℍ[ℝ]) = star (unitJ : ℍ[ℝ]) := rfl
  have e3 : ((unitK⁻¹ : UnitQuaternion) : ℍ[ℝ]) = star (unitK : ℍ[ℝ]) := rfl
  show (X : ℍ[ℝ]) + (unitI : ℍ[ℝ]) * X * ((unitI⁻¹ : UnitQuaternion) : ℍ[ℝ]) +
    (unitJ : ℍ[ℝ]) * X * ((unitJ⁻¹ : UnitQuaternion) : ℍ[ℝ]) +
    (unitK : ℍ[ℝ]) * X * ((unitK⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 0
  rw [e1, e2, e3]
  show (X : ℍ[ℝ]) + quatI * X * star quatI + quatJ * X * star quatJ + quatK * X * star quatK = 0
  apply Quaternion.ext <;> simp [hX]
theorem expUnit_adjointAction (g : UnitQuaternion) (v : imaginaryQuaternions) :
    expUnit (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g v) = g * expUnit v * g⁻¹ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.expUnit_adjointAction <;> assumption
theorem adjointAction_one (v : imaginaryQuaternions) : _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (1 : UnitQuaternion) v = v := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GradientInvariance.adjointAction_one <;> assumption
theorem adjointAction_zero (g : UnitQuaternion) : _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g 0 = 0 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.adjointAction_zero <;> assumption
def adjointLinear (g : UnitQuaternion) : imaginaryQuaternions →ₗ[ℝ] imaginaryQuaternions where
  toFun := _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g
  map_add' u v := by
    apply Subtype.ext
    show (g : ℍ[ℝ]) * ((u + v : imaginaryQuaternions) : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
      (g : ℍ[ℝ]) * (u : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) +
        (g : ℍ[ℝ]) * (v : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])
    simp [mul_add, add_mul]
  map_smul' c u := by
    apply Subtype.ext
    show (g : ℍ[ℝ]) * ((c • u : imaginaryQuaternions) : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
      c • ((g : ℍ[ℝ]) * (u : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]))
    simp
def adjointOnForms (g : UnitQuaternion) :
    (↥(fineBonds F) → imaginaryQuaternions) →L[ℝ] (↥(fineBonds F) → imaginaryQuaternions) :=
  ContinuousLinearMap.pi fun b =>
    (LinearMap.toContinuousLinearMap (adjointLinear g)).comp (ContinuousLinearMap.proj b)
theorem adjointOnForms_apply (g : UnitQuaternion) (Z : ↥(fineBonds F) → imaginaryQuaternions)
    (b : ↥(fineBonds F)) : adjointOnForms g Z b = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g (Z b) := rfl
theorem continuous_expUnit : Continuous expUnit := by apply _root_.YangMills.Construction.TorusFields.continuous_expUnit <;> assumption
theorem continuous_pathHolonomy {Z : Type} [TopologicalSpace Z] (T : Z → F.GaugeField F.depth)
    (hT : ∀ x i, Continuous fun z => T z x i) (l : List PathStep) (x : F.Site F.depth) :
    Continuous fun z => pathHolonomy (T z) x l := by
  induction l generalizing x with
  | nil => exact continuous_const
  | cons st r ih =>
    simp only [pathHolonomy]
    refine Continuous.mul ?_ (ih _)
    unfold linkValue
    split_ifs
    · exact hT _ _
    · exact (hT _ _).inv
theorem continuous_leftTranslate (x : F.Site F.depth) (i : Fin 4) :
    Continuous fun Z : ↥(fineBonds F) → imaginaryQuaternions =>
      leftTranslate (_root_.YangMills.Construction.ColdStepAtMirrorFrames.extendByZero Z) (ColdStepAtMirrorFrames.uniformField F F.depth) x i := by
  unfold leftTranslate
  refine Continuous.mul (continuous_expUnit.comp ?_) continuous_const
  unfold _root_.YangMills.Construction.ColdStepAtMirrorFrames.extendByZero
  split_ifs with h
  · exact continuous_apply _
  · exact continuous_const
theorem eventually_smallCurvature (hper : ∀ i, F.period F.depth i ≠ 0) {σ : ℝ} (hσ : 0 < σ) :
    ∀ᶠ Z in 𝓝 (0 : ↥(fineBonds F) → imaginaryQuaternions),
      IsSmallCurvature σ (leftTranslate (_root_.YangMills.Construction.ColdStepAtMirrorFrames.extendByZero Z) (ColdStepAtMirrorFrames.uniformField F F.depth)) := by
  have : ∀ i, NeZero (F.period F.depth i) := fun i => ⟨hper i⟩
  have : Finite (F.Site F.depth) := Pi.finite
  have key : ∀ p : F.Site F.depth × Fin 4 × Fin 4, ∀ᶠ Z in 𝓝 (0 : ↥(fineBonds F) → imaginaryQuaternions),
      p.2.1 < p.2.2 → plaquetteDefect (leftTranslate (_root_.YangMills.Construction.ColdStepAtMirrorFrames.extendByZero Z)
        (ColdStepAtMirrorFrames.uniformField F F.depth)) p < σ := by
    intro p
    have hc : Continuous fun Z : ↥(fineBonds F) → imaginaryQuaternions =>
        plaquetteDefect (leftTranslate (_root_.YangMills.Construction.ColdStepAtMirrorFrames.extendByZero Z) (ColdStepAtMirrorFrames.uniformField F F.depth)) p := by
      unfold plaquetteDefect plaquetteHolonomy
      have := continuous_pathHolonomy (fun Z : ↥(fineBonds F) → imaginaryQuaternions =>
        leftTranslate (_root_.YangMills.Construction.ColdStepAtMirrorFrames.extendByZero Z) (ColdStepAtMirrorFrames.uniformField F F.depth))
        (fun x i => continuous_leftTranslate x i) [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] p.1
      exact ((continuous_subtype_val.comp this).sub continuous_const).norm
    have h0 : plaquetteDefect (leftTranslate (_root_.YangMills.Construction.ColdStepAtMirrorFrames.extendByZero (0 : ↥(fineBonds F) → imaginaryQuaternions))
        (ColdStepAtMirrorFrames.uniformField F F.depth)) p = 0 := by
      have e : leftTranslate (_root_.YangMills.Construction.ColdStepAtMirrorFrames.extendByZero (0 : ↥(fineBonds F) → imaginaryQuaternions))
          (ColdStepAtMirrorFrames.uniformField F F.depth) = ColdStepAtMirrorFrames.uniformField F F.depth := by
        funext x i
        apply Subtype.ext
        simp [leftTranslate, ColdStepAtMirrorFrames.uniformField, expUnit, _root_.YangMills.Construction.ColdStepAtMirrorFrames.extendByZero]
      rw [e]
      simp [plaquetteDefect, plaquetteHolonomy, pathHolonomy, linkValue, ColdStepAtMirrorFrames.uniformField]
    have := hc.continuousAt.eventually (gt_mem_nhds (show plaquetteDefect (leftTranslate
        (_root_.YangMills.Construction.ColdStepAtMirrorFrames.extendByZero (0 : ↥(fineBonds F) → imaginaryQuaternions))
        (ColdStepAtMirrorFrames.uniformField F F.depth)) p < σ by rw [h0]; exact hσ))
    exact this.mono fun Z hZ _ => hZ
  have hall := (Filter.eventually_all (ι := F.Site F.depth × Fin 4 × Fin 4)).2 key
  exact hall.mono fun Z hZ p hp => hZ p hp
theorem gaugeTransform_const_leftTranslate (hcov : ∀ x : F.Site F.depth, x ∈ sitesOfCells (finiteCells F) F.depth)
    (g : UnitQuaternion) (Z : ↥(fineBonds F) → imaginaryQuaternions) :
    gaugeTransform (fun _ => g) (leftTranslate (_root_.YangMills.Construction.ColdStepAtMirrorFrames.extendByZero Z) (ColdStepAtMirrorFrames.uniformField F F.depth)) =
      leftTranslate (_root_.YangMills.Construction.ColdStepAtMirrorFrames.extendByZero (adjointOnForms g Z)) (ColdStepAtMirrorFrames.uniformField F F.depth) := by
  funext x i
  have hb := mem_fineBonds hcov x i
  simp only [gaugeTransform, leftTranslate, ColdStepAtMirrorFrames.uniformField, mul_one, _root_.YangMills.Construction.ColdStepAtMirrorFrames.extendByZero, dif_pos hb,
    adjointOnForms_apply]
  rw [expUnit_adjointAction]
theorem fderiv_jetAtUniform_eq_zero (hcov : ∀ x : F.Site F.depth, x ∈ sitesOfCells (finiteCells F) F.depth)
    (hper : ∀ i, F.period F.depth i ≠ 0) {σ : ℝ} (hσ : 0 < σ) (G : F.GaugeField F.depth → ℝ)
    (hinv : ∀ (W : F.GaugeField F.depth) (γ : F.Site F.depth → UnitQuaternion), IsSmallCurvature σ W →
      G (gaugeTransform γ W) = G W)
    (hJ : ContDiffAt ℝ 3 (jetAtUniform G) 0) : fderiv ℝ (jetAtUniform G) 0 = 0 := by
  have hd : DifferentiableAt ℝ (jetAtUniform G) 0 := hJ.differentiableAt (by norm_num)
  have key : ∀ (g : UnitQuaternion) (Z : ↥(fineBonds F) → imaginaryQuaternions),
      fderiv ℝ (jetAtUniform G) 0 (adjointOnForms g Z) = fderiv ℝ (jetAtUniform G) 0 Z := by
    intro g Z
    have he : jetAtUniform G ∘ adjointOnForms g =ᶠ[𝓝 0] jetAtUniform G := by
      filter_upwards [eventually_smallCurvature hper hσ] with Z' hZ'
      simp only [Function.comp, jetAtUniform, formComposition]
      rw [← _root_.YangMills.Construction.WeightedResponses.BlockSecondDerivative.gaugeTransform_const_leftTranslate hcov g Z', hinv _ _ hZ']
    have h0 : adjointOnForms g (0 : ↥(fineBonds F) → imaginaryQuaternions) = 0 := map_zero _
    have hc : HasFDerivAt (jetAtUniform G ∘ adjointOnForms g)
        ((fderiv ℝ (jetAtUniform G) 0).comp (adjointOnForms g)) 0 := by
      have h1 : HasFDerivAt (jetAtUniform G) (fderiv ℝ (jetAtUniform G) 0) (adjointOnForms g 0) := by
        rw [h0]; exact hd.hasFDerivAt
      exact h1.comp 0 (adjointOnForms g).hasFDerivAt
    have := (hc.congr_of_eventuallyEq he.symm).fderiv
    exact (DFunLike.congr_fun this Z).symm
  ext Z
  have hs : Z + adjointOnForms unitI Z + adjointOnForms unitJ Z + adjointOnForms unitK Z = 0 := by
    funext b
    simpa [adjointOnForms_apply] using _root_.YangMills.Construction.WeightedResponses.BlockSecondDerivative.adjointAction_sum_units (Z b)
  have h4 := congrArg (fderiv ℝ (jetAtUniform G) 0) hs
  simp only [map_add, map_zero, key] at h4
  have : (4 : ℝ) * fderiv ℝ (jetAtUniform G) 0 Z = 0 := by linarith
  have : fderiv ℝ (jetAtUniform G) 0 Z = 0 := by linarith
  simpa using this
def gradientForm (φ : F.Site F.depth → ℝ) (X : imaginaryQuaternions) :
    F.Site F.depth → Fin 4 → imaginaryQuaternions :=
  fun x i => (φ (x + unitStep F.depth i) - φ x) • X
theorem iteratedFDeriv_one_smul_coord (A : imaginaryQuaternions) (l : Fin 2) :
    iteratedFDeriv ℝ 1 (fun τ : Fin 2 → ℝ => τ 1 • A) 0 (fun _ : Fin 1 => (Pi.single l 1 : Fin 2 → ℝ)) =
      (Pi.single l 1 : Fin 2 → ℝ) 1 • A := by
  have h : HasFDerivAt (fun τ : Fin 2 → ℝ => τ 1 • A)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).smulRight A) 0 :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).smulRight A).hasFDerivAt
  rw [iteratedFDeriv_one_apply, h.fderiv]
  simp
theorem second_deriv_gradientForm_eq_zero (h₃ : GaugeAlongMotion.gaugeAlongMotionStatement)
    (h₄ : ColdStepAtMirrorFrames.ThirdOrderChainRule)
    (hcov : ∀ x : F.Site F.depth, x ∈ sitesOfCells (finiteCells F) F.depth)
    (hper : ∀ i, F.period F.depth i ≠ 0) {σ : ℝ} (hσ : 0 < σ) (G : F.GaugeField F.depth → ℝ)
    (hinv : ∀ (W : F.GaugeField F.depth) (γ : F.Site F.depth → UnitQuaternion), IsSmallCurvature σ W →
      G (gaugeTransform γ W) = G W)
    (hJ : ContDiffAt ℝ 3 (jetAtUniform G) 0) (φ : F.Site F.depth → ℝ) (X : imaginaryQuaternions)
    (A : F.Site F.depth → Fin 4 → imaginaryQuaternions) :
    iteratedFDeriv ℝ 2 (jetAtUniform G) 0 ![restrictToBonds (gradientForm φ X), restrictToBonds A] = 0 ∧
      iteratedFDeriv ℝ 2 (jetAtUniform G) 0 ![restrictToBonds A, restrictToBonds (gradientForm φ X)] = 0 := by
  classical
  have : ∀ i, NeZero (F.period F.depth i) := fun i => ⟨hper i⟩
  let : Fintype (F.Site F.depth) := Fintype.ofFinite _
  have hD := fderiv_jetAtUniform_eq_zero hcov hper hσ G hinv hJ
  let α : (Fin 2 → ℝ) → F.Site F.depth → Fin 4 → imaginaryQuaternions := fun τ x i => τ 1 • A x i
  let ψ : Fin 2 → F.Site F.depth → imaginaryQuaternions := ![fun z => φ z • X, fun _ => 0]
  let Aq : ℕ → ℝ := fun q => ∑ x : F.Site F.depth, ∑ i : Fin 4, ‖iteratedFDeriv ℝ q (fun τ => α τ x i) 0‖
  let Bq : ℝ := ∑ l : Fin 2, ∑ z : F.Site F.depth, ‖ψ l z‖
  have hAq : ∀ q, 0 ≤ Aq q := fun q => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hBq : 0 ≤ Bq := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  obtain ⟨M, -, hM⟩ := h₃ 3 Aq Bq hAq hBq
  have hα0 : ∀ x i, α 0 x i = 0 := fun x i => by simp [α]
  have hαs : ∀ x i, ContDiffAt ℝ 3 (fun τ => α τ x i) 0 := fun x i => by
    have : ContDiff ℝ 3 (fun τ : Fin 2 → ℝ => τ 1 • A x i) := by fun_prop
    exact this.contDiffAt
  have hparts : ∀ (q : ℕ) (e : Fin q → Fin 2) (x : F.Site F.depth) (i : Fin 4) (l : Fin q), q ≤ 3 →
      ‖motionComponent α e x i‖ ≤ Aq q * (fun _ _ _ => (1 : ℝ)) x i (e l) := by
    intro q e x i l _
    have h1 : ‖motionComponent α e x i‖ ≤ ‖iteratedFDeriv ℝ q (fun τ => α τ x i) 0‖ := by
      unfold motionComponent
      refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
      have : ∏ m, ‖(Pi.single (e m) 1 : Fin 2 → ℝ)‖ = 1 := by
        refine Finset.prod_eq_one fun m _ => ?_
        simp [Pi.norm_single]
      rw [this, mul_one]
    have h2 : ‖iteratedFDeriv ℝ q (fun τ => α τ x i) 0‖ ≤ Aq q := by
      refine le_trans ?_ (Finset.single_le_sum
        (f := fun x => ∑ i : Fin 4, ‖iteratedFDeriv ℝ q (fun τ => α τ x i) 0‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ x))
      exact Finset.single_le_sum (f := fun i => ‖iteratedFDeriv ℝ q (fun τ => α τ x i) 0‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
    simpa using h1.trans h2
  have hψ : ∀ (x : F.Site F.depth) (i : Fin 4) (l : Fin 2), ‖ψ l x‖ ≤ Bq * (fun _ _ _ => (1 : ℝ)) x i l ∧
      ‖ψ l (x + unitStep F.depth i)‖ ≤ Bq * (fun _ _ _ => (1 : ℝ)) x i l := by
    intro x i l
    have hz : ∀ z, ‖ψ l z‖ ≤ Bq := fun z => by
      refine le_trans ?_ (Finset.single_le_sum (f := fun l => ∑ z : F.Site F.depth, ‖ψ l z‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ l))
      exact Finset.single_le_sum (f := fun z => ‖ψ l z‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ z)
    simpa using ⟨hz x, hz _⟩
  obtain ⟨α', hα'0, hα's, hgauge, hfirst, -⟩ := hM F F.depth 2 (ColdStepAtMirrorFrames.uniformField F F.depth) α ψ
    (fun _ _ _ => 1) hper hα0 hαs (fun _ _ _ => zero_le_one) (fun _ _ _ => le_rfl) hparts hψ
  let β : (Fin 2 → ℝ) → ↥(fineBonds F) → imaginaryQuaternions := fun τ b => α' τ b.1.1 b.1.2
  let Λ : (Fin 2 → ℝ) →L[ℝ] (↥(fineBonds F) → imaginaryQuaternions) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).smulRight (restrictToBonds A)
  have hβ0 : β 0 = 0 := by
    funext b; exact hα'0 _ _
  have hβs : ContDiffAt ℝ 3 β 0 := contDiffAt_pi.2 fun b => hα's _ _
  have hΛ0 : Λ 0 = 0 := map_zero _
  have hJβ : ContDiffAt ℝ 3 (jetAtUniform G) (β 0) := by rw [hβ0]; exact hJ
  have hJΛ : ContDiffAt ℝ 3 (jetAtUniform G) (Λ 0) := by rw [hΛ0]; exact hJ
  obtain ⟨-, -, hβ2, -⟩ := h₄ (jetAtUniform G) β 0 hJβ hβs
  obtain ⟨-, -, hΛ2, -⟩ := h₄ (jetAtUniform G) Λ 0 hJΛ Λ.contDiff.contDiffAt
  have hext : ∀ τ, leftTranslate (α τ) (ColdStepAtMirrorFrames.uniformField F F.depth) =
      leftTranslate (_root_.YangMills.Construction.ColdStepAtMirrorFrames.extendByZero (Λ τ)) (ColdStepAtMirrorFrames.uniformField F F.depth) := by
    intro τ
    have : Λ τ = restrictToBonds (α τ) := by
      funext b
      simp [Λ, restrictToBonds, α]
    rw [this, extendByZero_restrictToBonds hcov]
  have hcomp : jetAtUniform G ∘ β =ᶠ[𝓝 0] jetAtUniform G ∘ Λ := by
    have hcold : ∀ᶠ τ in 𝓝 (0 : Fin 2 → ℝ), IsSmallCurvature σ
        (leftTranslate (_root_.YangMills.Construction.ColdStepAtMirrorFrames.extendByZero (Λ τ)) (ColdStepAtMirrorFrames.uniformField F F.depth)) := by
      have ht : Tendsto Λ (𝓝 0) (𝓝 0) := by simpa [hΛ0] using Λ.continuous.tendsto 0
      exact ht.eventually (eventually_smallCurvature hper hσ)
    filter_upwards [hcold, hgauge] with τ hc hg
    have e1 : jetAtUniform G (β τ) = G (leftTranslate (α' τ) (ColdStepAtMirrorFrames.uniformField F F.depth)) :=
      jetAtUniform_restrictToBonds hcov G (α' τ)
    show jetAtUniform G (β τ) = jetAtUniform G (Λ τ)
    rw [e1, ← hg, hext τ, hinv _ _ hc]
    rfl
  have hparts' : ∀ (u v : Fin 2 → ℝ), iteratedFDeriv ℝ 2 (jetAtUniform G) 0
      ![iteratedFDeriv ℝ 1 β 0 ![u], iteratedFDeriv ℝ 1 β 0 ![v]] =
      iteratedFDeriv ℝ 2 (jetAtUniform G) 0 ![iteratedFDeriv ℝ 1 Λ 0 ![u], iteratedFDeriv ℝ 1 Λ 0 ![v]] := by
    intro u v
    have e1 := hβ2 u v
    have e2 := hΛ2 u v
    have e3 : iteratedFDeriv ℝ 2 (jetAtUniform G ∘ β) 0 = iteratedFDeriv ℝ 2 (jetAtUniform G ∘ Λ) 0 :=
      (Filter.EventuallyEq.iteratedFDeriv ℝ
        (show jetAtUniform G ∘ β =ᶠ[𝓝 0] jetAtUniform G ∘ Λ from hcomp) 2).eq_of_nhds
    have z : ∀ w, iteratedFDeriv ℝ 1 (jetAtUniform G) 0 ![w] = 0 := by
      intro w
      rw [iteratedFDeriv_one_apply, hD]
      rfl
    rw [hβ0, z] at e1
    rw [hΛ0, z] at e2
    rw [e3] at e1
    rw [← add_zero (iteratedFDeriv ℝ 2 (jetAtUniform G) 0 _), ← e1, e2, add_zero]
  have dβ : ∀ l : Fin 2, iteratedFDeriv ℝ 1 β 0 ![(Pi.single l 1 : Fin 2 → ℝ)] =
      fun b => motionComponent α' (fun _ : Fin 1 => l) b.1.1 b.1.2 := by
    intro l
    funext b
    rw [iteratedFDeriv_one_apply]
    simp only [motionComponent]
    rw [iteratedFDeriv_one_apply]
    have hd : DifferentiableAt ℝ β 0 := hβs.differentiableAt (by norm_num)
    have := (hasFDerivAt_pi'.1 hd.hasFDerivAt) b
    have e := this.fderiv
    simp only [Matrix.cons_val_zero]
    have e' : fderiv ℝ (fun τ => α' τ b.1.1 b.1.2) 0 = (ContinuousLinearMap.proj b).comp (fderiv ℝ β 0) := e
    rw [e']
    rfl
  have dΛ : ∀ u : Fin 2 → ℝ, iteratedFDeriv ℝ 1 Λ 0 ![u] = Λ u := by
    intro u
    rw [iteratedFDeriv_one_apply, Λ.fderiv]
    rfl
  have hcollect : ∀ (u v : ↥(fineBonds F) → imaginaryQuaternions), u = 0 ∨ v = 0 →
      iteratedFDeriv ℝ 2 (jetAtUniform G) 0 ![u, v] = 0 := by
    intro u v h
    rcases h with h | h
    · subst h
      exact (iteratedFDeriv ℝ 2 (jetAtUniform G) 0).map_coord_zero 0 rfl
    · subst h
      exact (iteratedFDeriv ℝ 2 (jetAtUniform G) 0).map_coord_zero 1 rfl
  have p0 : (fun b : ↥(fineBonds F) => motionComponent α' (fun _ : Fin 1 => (0 : Fin 2)) b.1.1 b.1.2) =
      - restrictToBonds (gradientForm φ X) := by
    funext b
    rw [hfirst (by norm_num) 0 b.1.1 b.1.2]
    have e0 : motionComponent α (fun _ : Fin 1 => (0 : Fin 2)) b.1.1 b.1.2 = 0 := by
      simp only [motionComponent, α]
      rw [iteratedFDeriv_one_smul_coord]
      simp
    rw [e0]
    simp only [ColdStepAtMirrorFrames.uniformField, _root_.YangMills.Construction.WeightedResponses.BlockSecondDerivative.adjointAction_one, ψ, restrictToBonds, gradientForm,
      Pi.neg_apply]
    simp
    module
  have p1 : (fun b : ↥(fineBonds F) => motionComponent α' (fun _ : Fin 1 => (1 : Fin 2)) b.1.1 b.1.2) =
      restrictToBonds A := by
    funext b
    rw [hfirst (by norm_num) 1 b.1.1 b.1.2]
    have e0 : motionComponent α (fun _ : Fin 1 => (1 : Fin 2)) b.1.1 b.1.2 = A b.1.1 b.1.2 := by
      simp only [motionComponent, α]
      rw [iteratedFDeriv_one_smul_coord]
      simp
    rw [e0]
    simp [ψ, restrictToBonds, ColdStepAtMirrorFrames.uniformField, _root_.YangMills.Construction.WeightedResponses.BlockSecondDerivative.adjointAction_zero]
  have l0 : Λ (Pi.single 0 1) = 0 := by
    simp [Λ]
  have neg2 : ∀ (u v : ↥(fineBonds F) → imaginaryQuaternions), iteratedFDeriv ℝ 2 (jetAtUniform G) 0 ![-u, v] =
      - iteratedFDeriv ℝ 2 (jetAtUniform G) 0 ![u, v] := by
    intro u v
    have := (iteratedFDeriv ℝ 2 (jetAtUniform G) 0).map_update_sub ![u, v] 0 0 u
    have e1 : Function.update ![u, v] 0 (0 - u) = ![-u, v] := by
      rw [zero_sub]
      funext j; fin_cases j <;> simp
    have e2 : Function.update ![u, v] 0 0 = ![0, v] := by
      funext j; fin_cases j <;> simp
    have e3 : Function.update ![u, v] 0 u = ![u, v] := by
      funext j; fin_cases j <;> simp
    rw [e1, e2, e3, hcollect 0 v (Or.inl rfl)] at this
    simpa using this
  have neg2' : ∀ (u v : ↥(fineBonds F) → imaginaryQuaternions), iteratedFDeriv ℝ 2 (jetAtUniform G) 0 ![u, -v] =
      - iteratedFDeriv ℝ 2 (jetAtUniform G) 0 ![u, v] := by
    intro u v
    have := (iteratedFDeriv ℝ 2 (jetAtUniform G) 0).map_update_sub ![u, v] 1 0 v
    have e1 : Function.update ![u, v] 1 (0 - v) = ![u, -v] := by
      rw [zero_sub]
      funext j; fin_cases j <;> simp
    have e2 : Function.update ![u, v] 1 0 = ![u, 0] := by
      funext j; fin_cases j <;> simp
    have e3 : Function.update ![u, v] 1 v = ![u, v] := by
      funext j; fin_cases j <;> simp
    rw [e1, e2, e3, hcollect u 0 (Or.inr rfl)] at this
    simpa using this
  constructor
  · have := hparts' (Pi.single 0 1) (Pi.single 1 1)
    rw [dβ 0, dβ 1, dΛ, dΛ, l0, p0, p1, hcollect 0 _ (Or.inl rfl), neg2] at this
    linarith
  · have := hparts' (Pi.single 1 1) (Pi.single 0 1)
    rw [dβ 0, dβ 1, dΛ, dΛ, l0, p0, p1, hcollect _ 0 (Or.inr rfl), neg2'] at this
    linarith
theorem sum_piFinset_fin_two {ι : Type} [DecidableEq ι] (S : Finset ι) (f : ι → ι → ℝ) :
    ∑ β ∈ Fintype.piFinset (fun _ : Fin 2 => S), f (β 0) (β 1) = ∑ b ∈ S, ∑ b' ∈ S, f b b' := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlatResponseSums.sum_piFinset_two <;> assumption
theorem mixedDerivAlong_uniform_eq (hcov : ∀ x : F.Site F.depth, x ∈ sitesOfCells (finiteCells F) F.depth)
    (G : F.GaugeField F.depth → ℝ) (hJ : ContDiffAt ℝ 3 (jetAtUniform G) 0)
    (A₀ A₁ : F.Site F.depth → Fin 4 → imaginaryQuaternions) :
    mixedDerivAlong G (ColdStepAtMirrorFrames.uniformField F F.depth) ![A₀, A₁] =
      iteratedFDeriv ℝ 2 (jetAtUniform G) 0 ![restrictToBonds A₀, restrictToBonds A₁] := by
  let Λ : (Fin 2 → ℝ) →L[ℝ] (↥(fineBonds F) → imaginaryQuaternions) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).smulRight (restrictToBonds A₀) +
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).smulRight (restrictToBonds A₁)
  have e : (fun τ : Fin 2 → ℝ => G (leftTranslate (fun x b => ∑ l, τ l • (![A₀, A₁] : Fin 2 → _) l x b)
      (ColdStepAtMirrorFrames.uniformField F F.depth))) = jetAtUniform G ∘ Λ := by
    funext τ
    have : Λ τ = restrictToBonds (fun x b => ∑ l, τ l • (![A₀, A₁] : Fin 2 → _) l x b) := by
      funext b
      simp [Λ, restrictToBonds, Fin.sum_univ_two]
    simp only [Function.comp, this]
    rw [jetAtUniform_restrictToBonds hcov]
  have hΛ0 : Λ 0 = 0 := map_zero _
  have hJΛ : ContDiffAt ℝ 2 (jetAtUniform G) (Λ 0) := by
    rw [hΛ0]; exact hJ.of_le (by norm_num)
  unfold mixedDerivAlong
  rw [e]
  obtain ⟨U, hU, hxU, hfU⟩ : ∃ U : Set (↥(fineBonds F) → imaginaryQuaternions),
      IsOpen U ∧ Λ 0 ∈ U ∧ ContDiffOn ℝ 2 (jetAtUniform G) U := by
    obtain ⟨u, hu, h⟩ := hJΛ.contDiffOn (m := 2) le_rfl (by simp)
    obtain ⟨U, hUu, hU, hxU⟩ := mem_nhds_iff.1 hu
    exact ⟨U, hU, hxU, h.mono hUu⟩
  have hΛU : IsOpen (Λ ⁻¹' U) := hU.preimage Λ.continuous
  have h := Λ.iteratedFDerivWithin_comp_right hfU hU.uniqueDiffOn hΛU.uniqueDiffOn
    (x := 0) hxU (i := 2) le_rfl
  rw [iteratedFDerivWithin_of_isOpen 2 hΛU (show (0 : Fin 2 → ℝ) ∈ Λ ⁻¹' U from hxU),
    iteratedFDerivWithin_of_isOpen 2 hU hxU] at h
  rw [h, hΛ0]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext l
  fin_cases l <;> simp [Λ]
theorem bondSpan_fin_two (y : F.Site F.depth) (b : Fin 2 → F.Site F.depth × Fin 4) :
    bondSpan y b = bondSpan y ![b 0, b 1] := by
  congr 1
  funext l
  fin_cases l <;> rfl
end BlockSecondDerivative
open BlockSecondDerivative in
theorem blockSecondDerivativeBound_holds (h₁ : TwoGaugedResponseSumBound)
    (h₂ : ColdStepAtMirrorFrames.FormCompositionJet) (h₃ : GaugeAlongMotion.gaugeAlongMotionStatement)
    (h₄ : ColdStepAtMirrorFrames.ThirdOrderChainRule) (h₅ : Estimates.expansionAlongMotionStatement)
    (h₆ : ColdStepAtMirrorFrames.BlocksCoverLowerLevel) : BlockSecondDerivativeBound := by
  classical
  intro a ha
  obtain ⟨del, Ca, hdel, hCa, L₀, hS⟩ := h₁ a ha
  refine ⟨del, Ca, hdel, hCa, L₀, ?_⟩
  intro F δ σ e e₃ Y c B W X r hodd hL hcub hδ hδd hσ he hf ht hX hr
  obtain ⟨n, hn, hside⟩ := hcub
  have hsides : ∀ i, 0 < F.extent i := fun i => by rw [hside i]; omega
  have hcov : ∀ x : F.Site F.depth, x ∈ sitesOfCells (finiteCells F) F.depth := h₆ F hodd hsides
  have hper : ∀ i, F.period F.depth i ≠ 0 := fun i => by
    have := hsides i
    have hLp : 0 < F.blockSide := hodd.pos
    unfold BlockFrame.period
    positivity
  have hflat : IsSmallCurvature σ (ColdStepAtMirrorFrames.uniformField F F.depth) := by
    intro p _
    simp [plaquetteDefect, plaquetteHolonomy, pathHolonomy, linkValue, ColdStepAtMirrorFrames.uniformField, hσ]
  have hS' := hS F δ Y c B W hodd hL ⟨n, hn, hside⟩ hδ hδd hf ht
  have hjet : ∀ y, ContDiffAt ℝ 3 (jetAtUniform (r y)) 0 := fun y =>
    (h₂ ℝ F F.depth (fineBonds F) (r y) _ (hr.smooth y _ hflat)).1
  have hinv : ∀ y (W' : F.GaugeField F.depth) (γ : F.Site F.depth → UnitQuaternion), IsSmallCurvature σ W' →
      r y (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ W') = r y W' := fun y W' γ h => hr.gauge_invariant y W' γ h
  have hsl := h₅.2
  have site : ∀ y ∈ blockFineSites Y, |mixedDerivAlong (r y) (ColdStepAtMirrorFrames.uniformField F F.depth)
      ![unitForm (W 0) (X 0), unitForm (W 1) (X 1)]| ≤
      e * ∑ b₁ ∈ fineBonds F, ∑ b₂ ∈ fineBonds F, (torusDecayFactor F.blockSide δ (bondSpan y ![b₁, b₂]))⁻¹ *
        |localAxialGauge (Real.sqrt F.blockSide) y (W 0) b₁.1 b₁.2| *
        |localAxialGauge (Real.sqrt F.blockSide) y (W 1) b₂.1 b₂.2| := by
    intro y _
    obtain ⟨φ₀, hφ₀⟩ : ∃ φ : F.Site F.depth → ℝ, ∀ x i, localAxialGauge (Real.sqrt F.blockSide) y (W 0) x i =
        W 0 x i + (φ (x + unitStep F.depth i) - φ x) :=
      ⟨fun z => smoothCutoff (Real.sqrt F.blockSide) y z * (- pathSum (W 0) y (axisPath (siteOffset y z) 1)),
        fun x i => rfl⟩
    obtain ⟨φ₁, hφ₁⟩ : ∃ φ : F.Site F.depth → ℝ, ∀ x i, localAxialGauge (Real.sqrt F.blockSide) y (W 1) x i =
        W 1 x i + (φ (x + unitStep F.depth i) - φ x) :=
      ⟨fun z => smoothCutoff (Real.sqrt F.blockSide) y z * (- pathSum (W 1) y (axisPath (siteOffset y z) 1)),
        fun x i => rfl⟩
    set g₀ := localAxialGauge (Real.sqrt F.blockSide) y (W 0) with hg₀
    set g₁ := localAxialGauge (Real.sqrt F.blockSide) y (W 1) with hg₁
    have k₀ := second_deriv_gradientForm_eq_zero h₃ h₄ hcov hper hσ (r y) (hinv y) (hjet y) φ₀ (X 0)
    have k₁ := second_deriv_gradientForm_eq_zero h₃ h₄ hcov hper hσ (r y) (hinv y) (hjet y) φ₁ (X 1)
    have d₀ : restrictToBonds (unitForm (W 0) (X 0)) =
        restrictToBonds (unitForm g₀ (X 0)) - restrictToBonds (gradientForm φ₀ (X 0)) := by
      funext b
      simp only [restrictToBonds, unitForm, gradientForm, Pi.sub_apply, hφ₀]
      module
    have d₁ : restrictToBonds (unitForm (W 1) (X 1)) =
        restrictToBonds (unitForm g₁ (X 1)) - restrictToBonds (gradientForm φ₁ (X 1)) := by
      funext b
      simp only [restrictToBonds, unitForm, gradientForm, Pi.sub_apply, hφ₁]
      module
    have sub0 : ∀ u v w : ↥(fineBonds F) → imaginaryQuaternions,
        iteratedFDeriv ℝ 2 (jetAtUniform (r y)) 0 ![u - v, w] =
        iteratedFDeriv ℝ 2 (jetAtUniform (r y)) 0 ![u, w] - iteratedFDeriv ℝ 2 (jetAtUniform (r y)) 0 ![v, w] := by
      intro u v w
      have := (iteratedFDeriv ℝ 2 (jetAtUniform (r y)) 0).map_update_sub ![u, w] 0 u v
      have e1 : Function.update ![u, w] 0 (u - v) = ![u - v, w] := by
        funext j; fin_cases j <;> simp
      have e2 : Function.update ![u, w] 0 u = ![u, w] := by
        funext j; fin_cases j <;> simp
      have e3 : Function.update ![u, w] 0 v = ![v, w] := by
        funext j; fin_cases j <;> simp
      rwa [e1, e2, e3] at this
    have sub1 : ∀ u v w : ↥(fineBonds F) → imaginaryQuaternions,
        iteratedFDeriv ℝ 2 (jetAtUniform (r y)) 0 ![w, u - v] =
        iteratedFDeriv ℝ 2 (jetAtUniform (r y)) 0 ![w, u] - iteratedFDeriv ℝ 2 (jetAtUniform (r y)) 0 ![w, v] := by
      intro u v w
      have := (iteratedFDeriv ℝ 2 (jetAtUniform (r y)) 0).map_update_sub ![w, u] 1 u v
      have e1 : Function.update ![w, u] 1 (u - v) = ![w, u - v] := by
        funext j; fin_cases j <;> simp
      have e2 : Function.update ![w, u] 1 u = ![w, u] := by
        funext j; fin_cases j <;> simp
      have e3 : Function.update ![w, u] 1 v = ![w, v] := by
        funext j; fin_cases j <;> simp
      rwa [e1, e2, e3] at this
    have same : mixedDerivAlong (r y) (ColdStepAtMirrorFrames.uniformField F F.depth)
        ![unitForm (W 0) (X 0), unitForm (W 1) (X 1)] =
        mixedDerivAlong (r y) (ColdStepAtMirrorFrames.uniformField F F.depth)
          ![unitForm g₀ (X 0), unitForm g₁ (X 1)] := by
      rw [mixedDerivAlong_uniform_eq hcov _ (hjet y), mixedDerivAlong_uniform_eq hcov _ (hjet y), d₀, d₁,
        sub0, sub1, sub1, (k₀ (unitForm g₁ (X 1))).1, (k₀ (gradientForm φ₁ (X 1))).1,
        (k₁ (unitForm g₀ (X 0))).2]
      simp
    rw [same]
    have hbnd := hsl F F.depth 2 (r y) (ColdStepAtMirrorFrames.uniformField F F.depth)
      ![unitForm g₀ (X 0), unitForm g₁ (X 1)] (fineBonds F)
      (fun b => e / torusDecayFactor F.blockSide δ (bondSpan y b)) hper (fun b => mem_fineBonds hcov b.1 b.2)
      (fun q c' X' => (hr.smooth y _ hflat q c' X').of_le (by norm_num))
      (fun b X' hX' => by
        have := hr.decay y _ 2 b X' hflat (by norm_num) (by norm_num) hX'
        simpa using this)
    refine hbnd.trans (le_of_eq ?_)
    have := sum_piFinset_fin_two (fineBonds F) (fun b₁ b₂ => e / torusDecayFactor F.blockSide δ (bondSpan y ![b₁, b₂]) *
      (‖unitForm g₀ (X 0) b₁.1 b₁.2‖ * ‖unitForm g₁ (X 1) b₂.1 b₂.2‖))
    have hpi : ∀ b : Fin 2 → F.Site F.depth × Fin 4, e / torusDecayFactor F.blockSide δ (bondSpan y b) *
        ∏ l, ‖(![unitForm g₀ (X 0), unitForm g₁ (X 1)] : Fin 2 → _) l (b l).1 (b l).2‖ =
        e / torusDecayFactor F.blockSide δ (bondSpan y ![b 0, b 1]) *
          (‖unitForm g₀ (X 0) (b 0).1 (b 0).2‖ * ‖unitForm g₁ (X 1) (b 1).1 (b 1).2‖) := by
      intro b
      rw [Fin.prod_univ_two, bondSpan_fin_two y b]
      rfl
    simp_rw [hpi]
    rw [this, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b₁ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b₂ _ => ?_
    simp only [unitForm, norm_smul, hX 0, hX 1, mul_one, Real.norm_eq_abs]
    rw [div_eq_mul_inv]
    ring
  calc |∑ y ∈ blockFineSites Y, mixedDerivAlong (r y) (ColdStepAtMirrorFrames.uniformField F F.depth)
        ![unitForm (W 0) (X 0), unitForm (W 1) (X 1)]|
      ≤ ∑ y ∈ blockFineSites Y, |mixedDerivAlong (r y) (ColdStepAtMirrorFrames.uniformField F F.depth)
        ![unitForm (W 0) (X 0), unitForm (W 1) (X 1)]| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y ∈ blockFineSites Y, e * ∑ b₁ ∈ fineBonds F, ∑ b₂ ∈ fineBonds F,
        (torusDecayFactor F.blockSide δ (bondSpan y ![b₁, b₂]))⁻¹ *
        |localAxialGauge (Real.sqrt F.blockSide) y (W 0) b₁.1 b₁.2| *
        |localAxialGauge (Real.sqrt F.blockSide) y (W 1) b₂.1 b₂.2| := Finset.sum_le_sum site
    _ = e * ∑ y ∈ blockFineSites Y, ∑ b₁ ∈ fineBonds F, ∑ b₂ ∈ fineBonds F,
        (torusDecayFactor F.blockSide δ (bondSpan y ![b₁, b₂]))⁻¹ *
        |localAxialGauge (Real.sqrt F.blockSide) y (W 0) b₁.1 b₁.2| *
        |localAxialGauge (Real.sqrt F.blockSide) y (W 1) b₂.1 b₂.2| := by rw [Finset.mul_sum]
    _ ≤ e * (Ca * (F.blockSide : ℝ) ^ (50 / 640 : ℝ) / torusDecayFactor F.blockSide δ (bondSpan Y c)) :=
        mul_le_mul_of_nonneg_left hS' he
    _ = Ca * (F.blockSide : ℝ) ^ (50 / 640 : ℝ) * e / torusDecayFactor F.blockSide δ (bondSpan Y c) := by ring
end WeightedResponses
end YangMills.Construction
end
