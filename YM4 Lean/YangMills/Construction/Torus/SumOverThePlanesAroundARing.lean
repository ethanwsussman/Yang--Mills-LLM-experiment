import YangMills.Construction.Lattice.LatticeBoxKernel
import YangMills.Construction.Torus.FreeKernelsOnATorus
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
open Tuples FreeRingKernels PeriodicLattice Exterior TestFunctions TorusMetric Conventions
namespace RingPlaneSums
def cyclicEntryProduct (σ : Fin 4 → Fin 4) (y : Fin 4 → Fin 4 → ℝ) (P : Fin 4 → AxisPlane) : ℝ :=
  ∏ k : Fin 4,
    bivectorMatrixEntry (freeCurvaturePropagator (y (σ k) - y (σ (finRotate 4 k))))
      (P (σ k)) (P (σ (finRotate 4 k)))
def PropagatorEntriesSymmetric : Prop :=
  (∀ w : Fin 4 → ℝ, w ≠ 0 →
    (∀ P Q : AxisPlane,
      bivectorMatrixEntry (freeCurvaturePropagator w) P Q =
        bivectorMatrixEntry (freeCurvaturePropagator w) Q P) ∧
    freeCurvaturePropagator (-w) = freeCurvaturePropagator w) ∧
  ∀ x y : Fin 4 → ℝ, x ≠ y → ∀ P Q : AxisPlane,
    bivectorMatrixEntry (freeCurvaturePropagator (x - y)) P Q =
      bivectorMatrixEntry (freeCurvaturePropagator (y - x)) Q P
def PlaneSumEqCyclicTrace : Prop :=
  (∀ σ : Fin 4 → Fin 4, IsBijectiveTuple σ → ∀ y : Fin 4 → Fin 4 → ℝ, Function.Injective y →
    ∑ P : Fin 4 → AxisPlane, cyclicEntryProduct σ y P = cyclicTrace σ y) ∧
  ∀ y : Fin 4 → Fin 4 → ℝ, Function.Injective y →
    freeBoxDensity y = ∑ r : Fin 3, ∑ P : Fin 4 → AxisPlane,
      cyclicEntryProduct (standardFourTuple r) y P
def TracesDependOnDifferences : Prop :=
  ∀ y y' : Fin 4 → Fin 4 → ℝ, Function.Injective y → (∀ i j, y i - y j = y' i - y' j) →
    (∀ σ : Fin 4 → Fin 4, IsBijectiveTuple σ → cyclicTrace σ y = cyclicTrace σ y') ∧
      freeBoxDensity y = freeBoxDensity y'
def LipschitzQuadBoxKernel (p : StandingParameters) : Prop :=
  ∀ f : Fin 4 → p.Torus → ℝ, (∀ i, IsLipschitzFor (euclidDistTorus (ℓ := torusSide p.L p.m)) (f i)) →
    (Pairwise fun i j => Disjoint (metricSupport (f i)) (metricSupport (f j))) →
    ∀ (z : p.Torus) (ρ : ℝ) (c : Fin 4 → ℝ), SupportsInBall z ρ f → c ∈ liftsOf z →
      (∀ i, Integrable (ballIndicatorLift c ρ (f i))) ∧
      (∀ i, HasCompactSupport (ballIndicatorLift c ρ (f i))) ∧
      (Pairwise fun i j =>
        Disjoint (tsupport (ballIndicatorLift c ρ (f i))) (tsupport (ballIndicatorLift c ρ (f j)))) ∧
      freeBoxKernelTorus (L := p.L) (m := p.m) f = freeBoxKernel fun i => ballIndicatorLift c ρ (f i)
def BoxKernelRingExpansion (S : StandingParameters) : Prop :=
  ∀ n : ℕ, n ≤ (S.K : ℕ) →
    (∀ φ : Fin 4 → Plaquette S.L S.m ((S.K : ℕ) : ℤ) → ℝ,
      boxKernel S n φ =
        ∑ r : Fin 3, ∑ᶠ q : Fin 4 → Plaquette S.L S.m ((S.K : ℕ) : ℤ),
          (∏ i, φ i (q i)) *
            ∏ k : Fin 4,
              backgroundCurvatureCovariance S n (q (standardFourTuple r k))
                (q (standardFourTuple r (finRotate 4 k)))) ∧
    ∀ (φ : Fin 4 → Plaquette S.L S.m ((S.K : ℕ) : ℤ) → ℝ) (i : Fin 4),
      IsLinearMap ℝ fun ψ : Plaquette S.L S.m ((S.K : ℕ) : ℤ) → ℝ =>
        boxKernel S n (Function.update φ i ψ)
def RingPlaneSumStatement : Prop :=
  PropagatorEntriesSymmetric ∧ PlaneSumEqCyclicTrace ∧
    TracesDependOnDifferences ∧ (∀ p : StandingParameters, LipschitzQuadBoxKernel p) ∧
      ∀ S : StandingParameters, BoxKernelRingExpansion S
end RingPlaneSums
end YangMills.Construction
end
