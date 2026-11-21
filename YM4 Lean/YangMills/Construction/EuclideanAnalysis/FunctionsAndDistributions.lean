import YangMills.Construction.Lattice.ObservablesAndTestNorms
import Mathlib
open MeasureTheory Set TopologicalSpace
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanAnalysis
abbrev RealSpace (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)
section Points
variable {n : ℕ}
def stdBasisVector (μ : Fin n) : RealSpace n := EuclideanSpace.single μ 1
end Points
section Functions
variable {n : ℕ} {F : Type*}
def IsContDiffOne (f : RealSpace n → ℂ) : Prop := ContDiff ℝ 1 f
abbrev CompactSupportClass (k : ℕ∞) (O : Opens (RealSpace n)) (F : Type*) [NormedAddCommGroup F]
    [NormedSpace ℝ F] : Type _ :=
  TestFunction O F k
def IsRadial (f : RealSpace n → F) : Prop := ∀ x y : RealSpace n, ‖x‖ = ‖y‖ → f x = f y
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
def partialDeriv (μ : Fin n) (f : RealSpace n → F) (x : RealSpace n) : F :=
  lineDeriv ℝ f x (stdBasisVector μ)
def gradNorm (f : RealSpace n → F) (x : RealSpace n) : ℝ :=
  Real.sqrt (∑ μ, ‖partialDeriv μ f x‖ ^ 2)
def gradUniformNorm (f : RealSpace n → F) : ℝ := TestFunctions.uniformNorm (gradNorm f)
end Functions
def measureCharFun (m : Measure ℝ) (s : ℝ) : ℂ :=
  ∫ q, Complex.exp (Complex.I * s * q) ∂m
abbrev SmoothTestFunction : Type := TestFunction (⊤ : Opens (RealSpace 4)) ℂ (⊤ : ℕ∞)
abbrev Distribution : Type := SmoothTestFunction →ₗ[ℂ] ℂ
def ofFunction (f : RealSpace 4 → ℂ) : Distribution :=
  (TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul ℂ ℂ) volume f).toLinearMap
theorem ofFunction_apply {f : RealSpace 4 → ℂ} (hf : LocallyIntegrable f volume)
    (φ : SmoothTestFunction) : ofFunction f φ = ∫ x, f x * φ x := by
  have h : LocallyIntegrableOn f ((⊤ : Opens (RealSpace 4)) : Set (RealSpace 4)) volume := by
    simpa using hf.locallyIntegrableOn univ
  simp only [ofFunction, ContinuousLinearMap.coe_coe,
    TestFunction.integralAgainstBilinCLM_eq_integral h, ContinuousLinearMap.mul_apply']
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
def dirac : Distribution where
  toFun φ := φ 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def laplacian {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : RealSpace 4 → F)
    (x : RealSpace 4) : F :=
  ∑ μ, partialDeriv μ (partialDeriv μ f) x
def testLaplacian : SmoothTestFunction →ₗ[ℂ] SmoothTestFunction :=
  ∑ μ : Fin 4, ((TestFunction.lineDerivCLM ℂ (stdBasisVector μ) :
      SmoothTestFunction →L[ℂ] SmoothTestFunction).comp
    (TestFunction.lineDerivCLM ℂ (stdBasisVector μ))).toLinearMap
theorem testLaplacian_apply (φ : SmoothTestFunction) (x : RealSpace 4) :
    testLaplacian φ x = laplacian φ x := by
  have hpart : ∀ (μ : Fin 4) (ψ : SmoothTestFunction),
      ((TestFunction.lineDerivCLM ℂ (stdBasisVector μ) ψ : SmoothTestFunction) :
        RealSpace 4 → ℂ) = partialDeriv μ ψ := fun μ ψ => funext fun y =>
    TestFunction.lineDerivCLM_apply_of_le (by simp)
  have hsum : ∀ (s : Finset (Fin 4)) (g : Fin 4 → SmoothTestFunction),
      (∑ μ ∈ s, g μ) x = ∑ μ ∈ s, g μ x := fun s g => by
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => simp [Finset.sum_insert ha, ih]
  simp only [testLaplacian, LinearMap.sum_apply, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.comp_apply, hsum, laplacian]
  exact Finset.sum_congr rfl fun μ _ => by rw [hpart, hpart]
def distribLaplacian (u : Distribution) : Distribution :=
  u ∘ₗ testLaplacian
def convolution {X R : Type*} [MeasureSpace X] [Sub X] [NormedRing R] [NormedSpace ℝ R]
    (f g : X → R) (x : X) : R :=
  ∫ y, f (x - y) * g y
end YangMills.Construction.EuclideanAnalysis
