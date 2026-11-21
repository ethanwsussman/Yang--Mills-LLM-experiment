import YangMills.Construction.InfiniteLattice.HypercubicMotionsOfTheLattice
import YangMills.Construction.InfiniteLattice.OneLatticeItsConfigurationsAndMeasuresOnCompactSpaces
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter YangMills.Construction.InfiniteLattice
open scoped Topology ENNReal
noncomputable section
namespace YangMills.Construction.LatticePhases.MotionInvariance
variable {a : ℝ}
def PushforwardExistsUnique (r : latticeMotions a) (ρ : ProbMeasure (GaugeField a)) : Prop :=
  ∃! σ : ProbMeasure (GaugeField a), ∀ F : GaugeField a → ℂ, IsBoundedObservable F →
    σ.eval F = ρ.eval (latticeMotionAct r F)
def InvarianceCheckedOnDense (r : latticeMotions a) (ρ : ProbMeasure (GaugeField a)) : Prop :=
  ∀ T : Set C(GaugeField a, ℂ),
    (∀ G : C(GaugeField a, ℂ), ∀ ε : ℝ, 0 < ε → ∃ F ∈ T, uniformSup (⇑G - ⇑F) < ε) →
      (IsSymmetricUnder ρ.toMeasure (latticeMotionSymmetry r) ↔
        ∀ F ∈ T, ρ.eval (latticeMotionAct r ⇑F) = ρ.eval ⇑F)
def InvarianceExtendsToBorel (r : latticeMotions a) (ρ : ProbMeasure (GaugeField a)) : Prop :=
  IsSymmetricUnder ρ.toMeasure (latticeMotionSymmetry r) →
    (∀ X : GaugeField a → ℝ≥0∞, Measurable X →
      ∫⁻ U, latticeMotionAct r X U ∂ρ.toMeasure = ∫⁻ U, X U ∂ρ.toMeasure) ∧
    (∀ X : GaugeField a → ℂ, Measurable X → HasFiniteIntegral X ρ.toMeasure →
      ρ.eval (latticeMotionAct r X) = ρ.eval X) ∧
    (∀ X Y : GaugeField a → ℂ, Measurable X → Measurable Y →
      ρ.HoldsAS (fun U => X U = Y U) →
        ρ.HoldsAS (fun U => latticeMotionAct r X U = latticeMotionAct r Y U))
def InvarianceClosedUnderLimits (r : latticeMotions a) (ρ : ProbMeasure (GaugeField a)) : Prop :=
  ∀ ρs : ℕ+ → ProbMeasure (GaugeField a),
    (∀ i, IsSymmetricUnder (ρs i).toMeasure (latticeMotionSymmetry r)) →
      Tendsto ρs atTop (𝓝 ρ) → IsSymmetricUnder ρ.toMeasure (latticeMotionSymmetry r)
def Holds : Prop :=
  ∀ (D : Setup) (r : latticeMotions D.mesh) (ρ : ProbMeasure (GaugeField D.mesh)),
    PushforwardExistsUnique r ρ ∧ InvarianceCheckedOnDense r ρ ∧
      InvarianceExtendsToBorel r ρ ∧ InvarianceClosedUnderLimits r ρ
end YangMills.Construction.LatticePhases.MotionInvariance
end
