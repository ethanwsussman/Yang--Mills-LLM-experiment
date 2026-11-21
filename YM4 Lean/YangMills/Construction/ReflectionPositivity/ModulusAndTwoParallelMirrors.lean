import YangMills.Construction.ReflectionPositivity.ModulusOfAFunctionOfClassC1OnOneTorus
import YangMills.Construction.ReflectionPositivity.ReflectionOfAMirrorOfOneTorus
import Mathlib
set_option autoImplicit false
open Filter Set Topology
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.TorusCutoffs
namespace ParallelMirrors
variable (D : TorusData)
def ModulusMonotoneTendsto (f : D.Torus → ℝ) : Prop :=
  MonotoneOn (D.c1Modulus f) (Ici 0) ∧ Tendsto (D.c1Modulus f) (𝓝[Ici 0] 0) (𝓝 0)
def SharpNormShiftLe (f : D.Torus → ℝ) : Prop :=
  ∀ u u' : D.Torus,
    D.sharpNorm (TorusTuples.transport (TorusTuples.shiftBy u) f -
        TorusTuples.transport (TorusTuples.shiftBy u') f) ≤
      D.c1Modulus f (torusDist u u')
abbrev axisReflectPerm (μ : Fin 4) (c : ℝ) : D.Torus ≃ D.Torus :=
  (TorusMirrors.AxisLevel.mk μ c).reflectPerm D.toStandingParameters
def mirrorShift (μ : Fin 4) (c c' : ℝ) : Fin 4 → ℝ :=
  (2 * (c' - c)) • PeriodicLattice.coordVec μ
def ParallelMirrorShift (μ : Fin 4) (c c' : ℝ) : Prop :=
  (∀ (E : Type) (g : D.Torus → E),
    TorusTuples.transport (axisReflectPerm D μ c') g =
      TorusTuples.transport
        (TorusTuples.shiftByVector D.toStandingParameters (mirrorShift μ c c'))
        (TorusTuples.transport (axisReflectPerm D μ c) g)) ∧
  ∀ (E : Type) [Zero E] (g : D.Torus → E),
    TorusTuples.supp (s := D.toStandingParameters)
        (TorusTuples.transport (axisReflectPerm D μ c') g) =
      translateVec (axisReflectPerm D μ c '' TorusTuples.supp (s := D.toStandingParameters) g)
        (mirrorShift μ c c')
def SharpNormParallelLe (h : D.Torus → ℝ) (μ : Fin 4) (c c' : ℝ) : Prop :=
  D.sharpNorm (TorusTuples.transport (axisReflectPerm D μ c') h -
      TorusTuples.transport (axisReflectPerm D μ c) h) ≤
    D.c1Modulus h (2 * |c' - c|)
def ModulusIsometryInvariant (f : D.Torus → ℝ) : Prop :=
  ∀ r : D.Torus ≃ D.Torus, TorusTuples.IsTorusIsometry D.toStandingParameters r →
    EqOn (D.c1Modulus (TorusTuples.transport r f)) (D.c1Modulus f) (Ici 0)
end ParallelMirrors
open ParallelMirrors
def ParallelMirrors.ModulusProperties : Prop :=
  ∀ D : TorusData,
    (∀ f : D.Torus → ℝ, IsC1 (s := D.toStandingParameters) f →
      ModulusMonotoneTendsto D f ∧ SharpNormShiftLe D f ∧ ModulusIsometryInvariant D f) ∧
    (∀ (μ : Fin 4) (c c' : ℝ), ParallelMirrorShift D μ c c') ∧
    ∀ h : D.Torus → ℝ, IsC1 (s := D.toStandingParameters) h →
      ∀ (μ : Fin 4) (c c' : ℝ), SharpNormParallelLe D h μ c c'
end YangMills.Construction.ReflectionPositivity.TorusCutoffs
end
