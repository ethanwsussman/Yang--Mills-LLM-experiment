import YangMills.Construction.RunningCouplingSlope.CoefficientOfALocalDensityProof
import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
import YangMills.Construction.SummableBoundsOfTheFlow.GaugeOfAMotionProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames TorusFields
namespace FlatFieldJets
section Calculus
variable {E₁ E₂ E₃ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂]
  [NormedSpace ℝ E₂] [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]
theorem exists_isOpen_contDiffOn_of_contDiffAt {f : E₁ → E₂} {x : E₁} {n : ℕ}
    (hf : ContDiffAt ℝ n f x) :
    ∃ U : Set E₁, IsOpen U ∧ x ∈ U ∧ ContDiffOn ℝ n f U := by apply _root_.YangMills.Construction.GaugeAlongMotion.exists_isOpen_contDiffOn_of_contDiffAt <;> assumption
theorem iteratedFDeriv_comp_continuousLinearMap (Λ : E₁ →L[ℝ] E₂) {f : E₂ → E₃} {x : E₁} {n : ℕ}
    (hf : ContDiffAt ℝ n f (Λ x)) (v : Fin n → E₁) :
    iteratedFDeriv ℝ n (f ∘ Λ) x v = iteratedFDeriv ℝ n f (Λ x) fun l => Λ (v l) := by
  obtain ⟨U, hU, hxU, hfU⟩ := exists_isOpen_contDiffOn_of_contDiffAt hf
  have hΛ : IsOpen (Λ ⁻¹' U) := hU.preimage Λ.continuous
  have h := Λ.iteratedFDerivWithin_comp_right hfU hU.uniqueDiffOn hΛ.uniqueDiffOn
    (x := x) hxU (i := n) le_rfl
  rw [iteratedFDerivWithin_of_isOpen n hΛ (show x ∈ Λ ⁻¹' U from hxU),
    iteratedFDerivWithin_of_isOpen n hU hxU] at h
  rw [h]
  rfl
end Calculus
section Group
theorem expUnit_zero : expUnit 0 = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
theorem continuous_expUnit : Continuous expUnit := by apply _root_.YangMills.Construction.TorusFields.continuous_expUnit <;> assumption
theorem expUnit_adjointAction (g : UnitQuaternion) (v : imaginaryQuaternions) :
    expUnit (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g v) = g * expUnit v * g⁻¹ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.expUnit_adjointAction <;> assumption
theorem adjointAction_add (g : UnitQuaternion) (X X' : imaginaryQuaternions) :
    _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g (X + X') = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g X + _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g X' := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.adjointAction_add <;> assumption
theorem adjointAction_smul (g : UnitQuaternion) (r : ℝ) (X : imaginaryQuaternions) :
    _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g (r • X) = r • _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g X := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.adjointAction_smul <;> assumption
end Group
section Fields
variable {n : ℕ} [NeZero n]
def expField (A : TorusBond n → imaginaryQuaternions) : TorusField n := fun x i => expUnit (A (x, i))
theorem expField_zero : expField (0 : TorusBond n → imaginaryQuaternions) = trivialField n := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.expOfCoords_zero <;> assumption
theorem tendsto_expField_nhds_zero :
    Filter.Tendsto (expField : (TorusBond n → imaginaryQuaternions) → TorusField n) (𝓝 0)
      (𝓝 (trivialField n)) := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.tendsto_expOfCoords <;> assumption
def perturbationForm {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) :
    (Fin k → ℝ) →L[ℝ] (TorusBond n → imaginaryQuaternions) :=
  ∑ l, (ContinuousLinearMap.proj l : (Fin k → ℝ) →L[ℝ] ℝ).smulRight
    (Pi.single (c l) (X l) : TorusBond n → imaginaryQuaternions)
theorem perturbationForm_apply {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (t : Fin k → ℝ) (b : TorusBond n) :
    perturbationForm c X t b = ∑ l, if c l = b then t l • X l else 0 := by
  simp only [perturbationForm, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply, Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases h : c l = b
  · simp [h]
  · simp [h, Ne.symm h]
theorem perturb_trivialField {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (t : Fin k → ℝ) :
    perturb c X t (trivialField n) = expField (perturbationForm c X t) := by
  funext x i
  simp only [perturb, expField, perturbationForm_apply, trivialField, mul_one]
theorem perturbationForm_single {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (l : Fin k) :
    perturbationForm c X (Pi.single l 1) = Pi.single (c l) (X l) := by
  simp only [perturbationForm, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply, Pi.single_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
theorem mixedDeriv_trivialField {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}
    (G : TorusField n → E) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (h : ContDiffAt ℝ k (fun A => G (expField A)) 0) :
    mixedDeriv G (trivialField n) c X = iteratedFDeriv ℝ k (fun A => G (expField A)) 0
      fun l => Pi.single (c l) (X l) := by
  unfold mixedDeriv
  have h1 : (fun t : Fin k → ℝ => G (perturb c X t (trivialField n))) =
      (fun A => G (expField A)) ∘ (perturbationForm c X) := by
    funext t
    simp only [perturb_trivialField, Function.comp_apply]
  rw [h1, iteratedFDeriv_comp_continuousLinearMap (perturbationForm c X) (by simpa using h)]
  simp only [map_zero, perturbationForm_single]
def adjointForm (g : UnitQuaternion) :
    (TorusBond n → imaginaryQuaternions) →L[ℝ] (TorusBond n → imaginaryQuaternions) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A b => _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g (A b)
      map_add' := fun A A' => funext fun b => _root_.YangMills.Construction.FlatFieldJets.adjointAction_add g _ _
      map_smul' := fun r A => funext fun b => _root_.YangMills.Construction.FlatFieldJets.adjointAction_smul g r _ }
theorem adjointForm_apply (g : UnitQuaternion) (A : TorusBond n → imaginaryQuaternions) (b : TorusBond n) :
    adjointForm g A b = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g (A b) := rfl
theorem adjointForm_single (g : UnitQuaternion) (b : TorusBond n) (X : imaginaryQuaternions) :
    adjointForm g (Pi.single b X) = Pi.single b (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g X) := by
  funext b'
  rw [adjointForm_apply]
  by_cases h : b' = b
  · subst h
    simp
  · simp only [Pi.single_apply, h, if_false]
    apply Subtype.ext
    show (g : ℍ[ℝ]) * ((0 : imaginaryQuaternions) : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 0
    simp
theorem gaugeTransform_const_expField (g : UnitQuaternion) (A : TorusBond n → imaginaryQuaternions) :
    gaugeTransform (fun _ => g) (expField A) = expField (adjointForm g A) := by
  funext x i
  simp only [TorusFields.gaugeTransform, expField, adjointForm_apply, expUnit_adjointAction]
end Fields
end FlatFieldJets
end YangMills.Construction
end
