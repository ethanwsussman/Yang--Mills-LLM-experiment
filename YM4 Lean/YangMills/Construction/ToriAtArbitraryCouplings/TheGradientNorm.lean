import YangMills.Construction.ReflectionPositivity.SharpNormAndModulusOfAFunctionOfClassC1
import YangMills.Construction.SourcesAndGluing.StandingDataAndSigns
import YangMills.Construction.ToriAtArbitraryCouplings.TheSpaceAndTheCubeSize
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings
open ReflectionPositivity.AxisMirror (Ambient)
namespace TorusSide
variable (s : TorusSide)
def toGluingSetup : SourcesAndGluing.GluingSetup :=
  ⟨⟨s.L, s.admissible, 1, s.m⟩, 1, one_pos, 0⟩
abbrev IsC1Fun (E : Ambient) (f : s.Point E → ℝ) : Prop :=
  Ambient.IsC1 s.asMirrorData E f
def c1Set (E : Ambient) : Set (s.Point E → ℝ) := {f | s.IsC1Fun E f}
def partialD (μ : Fin 4) : (E : Ambient) → (s.Point E → ℝ) → s.Point E → ℝ
  | .torus, f => s.toGluingSetup.partialDeriv μ f
  | .euclidean, f => TestFunctions.partialDerivR4 μ f
theorem pullback_partialD (μ : Fin 4) (E : Ambient) (f : s.Point E → ℝ) :
    s.pullback (s.partialD μ E f) = TestFunctions.partialDerivR4 μ (s.pullback f) := by
  cases E
  · exact s.toGluingSetup.partialDeriv_comp_proj μ f
  · rfl
theorem eq_partialD_of_pullback (μ : Fin 4) (E : Ambient) (f g : s.Point E → ℝ)
    (h : s.pullback g = TestFunctions.partialDerivR4 μ (s.pullback f)) :
    g = s.partialD μ E f := by
  cases E
  · exact s.toGluingSetup.eq_partialDeriv_of_comp μ f g h
  · exact h
def c1CompactSet (E : Ambient) : Set (s.Point E → ℝ) :=
  {f | f ∈ s.c1Set E ∧ s.IsCompactWrt E (s.closedSupport E f)}
abbrev gradVec (E : Ambient) (f : s.Point E → ℝ) : s.Point E → Fin 4 → ℝ :=
  Ambient.grad s.asMirrorData E f
theorem gradVec_apply (E : Ambient) (f : s.Point E → ℝ) (x : s.Point E) (μ : Fin 4) :
    s.gradVec E f x μ = s.partialD μ E f x := by
  cases E
  · have hlift : s.ambientProj .torus (s.asMirrorData.liftChoice x) = x :=
      Classical.epsilon_spec (p := fun y => s.asMirrorData.projection y = x)
        (TestFunctions.torusProj_surjective _ x)
    have h := congrFun (s.pullback_partialD μ .torus f) (s.asMirrorData.liftChoice x)
    simp only [pullback, Function.comp_apply, hlift] at h
    exact h.symm
  · rfl
def gradNorm (E : Ambient) (f : s.Point E → ℝ) (x : s.Point E) : ℝ :=
  Ambient.vecLength (s.gradVec E f x)
theorem gradNorm_eq (E : Ambient) (f : s.Point E → ℝ) (x : s.Point E) :
    s.gradNorm E f x = TorusMetric.euclidNormVec (s.gradVec E f x) := by
  simp [gradNorm, Ambient.vecLength, TorusMetric.euclidNormVec]
def gradSupNorm (E : Ambient) (f : s.Point E → ℝ) : ℝ≥0∞ :=
  ⨆ x : s.Point E, ENNReal.ofReal (s.gradNorm E f x)
def c1GradNorm (E : Ambient) (f : s.Point E → ℝ) : ℝ :=
  max (TestFunctions.uniformNorm f) (s.gradSupNorm E f).toReal
section Norms
variable {𝕜 : Type*} [RCLike 𝕜]
def lipConst : (E : Ambient) → (s.Point E → 𝕜) → ℝ
  | .torus, f => TestFunctions.lipConstTorus f
  | .euclidean, f => TestFunctions.lipConstR4 f
def cubeScale (m' : ℕ) : Ambient.ScaleParam :=
  ⟨(cubeEdge s.L m' : ℝ),
    Set.mem_Ici.2 (by exact_mod_cast one_le_cubeEdge s.admissible m')⟩
def sharpNormAt (m' : ℕ) (E : Ambient) (f : s.Point E → 𝕜) : ℝ :=
  Ambient.normSharp s.asMirrorData (s.cubeScale m') E f
theorem sharpNormAt_eq (m' : ℕ) (E : Ambient) (f : s.Point E → 𝕜) :
    s.sharpNormAt m' E f =
      max (TestFunctions.uniformNorm f) (40 * (cubeEdge s.L m' : ℝ) * s.lipConst E f) := by
  cases E <;> rfl
end Norms
end TorusSide
end YangMills.Construction.ToriAtArbitraryCouplings
end
