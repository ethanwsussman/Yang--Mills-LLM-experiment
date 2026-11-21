import YangMills.Construction.SummableBoundsOfTheFlow.AdmittedObservables
import YangMills.Construction.SummableBoundsOfTheFlow.PropertiesOfIntermediateFrames
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace Interpolation
variable {F : BlockFrame}
def bondDistToTopBond (b : ↥(chordBonds (finiteCells F))) (e : F.Site F.top × Fin 4) : ℝ :=
  cellSupDist (enclosingCell b.1.1) e.1
def topFieldPartial (Th : imaginaryQuaternions → imaginaryQuaternions → imaginaryQuaternions)
    (s a ρA : ℝ) (m : ℕ) (e : F.Site F.top × Fin 4) (X : imaginaryQuaternions)
    (V : F.GaugeField F.top) (b : ↥(chordBonds (finiteCells F)))
    (A : StepVariable (finiteCells F) → ℝ) (η : StepVariable (finiteCells F)) : ℝ :=
  bondPartialDeriv A b η
    (imaginaryCoords (topVariationField Th s a ρA m e X b.1 (toImaginary (η b)) V))
structure ThirdOrderHypotheses
    (Th : imaginaryQuaternions → imaginaryQuaternions → imaginaryQuaternions)
    (s a ρA r x κ α β : ℝ) (m : ℕ) (p : ℝ → ℝ) (Cq : ℕ → ℝ) (V : F.GaugeField F.top)
    (Y : F.Cell) (e : Fin 3 → F.Site F.top × Fin 4) (X : Fin 3 → imaginaryQuaternions)
    (Ψ A : StepVariable (finiteCells F) → ℝ) : Prop where
  smooth : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < r) → ContDiffAt ℝ 2 A η
  hasLocalSize : HasLocalSize r (cutoffFactor r p) Ψ Cq x κ α (TorusComparison.bondDistToCell Y) A
  hasLocalSize_topFieldPartial : ∀ (b : ↥(chordBonds (finiteCells F))) (l : Fin 3),
    HasLocalSize r (cutoffFactor r p) Ψ Cq x κ
      (β * Real.exp (-(2 ^ 4 * κ * TorusComparison.bondDistToCell Y b) -
        2 ^ 6 * κ * bondDistToTopBond b (e l)))
      (TorusComparison.bondDistToCell Y) (topFieldPartial Th s a ρA m (e l) (X l) V b A)
def thirdOrderCovarianceBoundAt (T : StepParameters) (Cq : ℕ → ℝ) : Prop :=
  ∀ (t : ℕ) (x s α β : ℝ) (φ h : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top)
    (Y : F.Cell) (e : Fin 3 → F.Site F.top × Fin 4) (X : Fin 3 → imaginaryQuaternions)
    (Th : imaginaryQuaternions → imaginaryQuaternions → imaginaryQuaternions)
    (A : StepVariable (finiteCells F) → ℝ),
    T.coupling ≤ x → 0 ≤ s → s ≤ 1 → 0 < α → 0 ≤ β →
    FamilyNorms.IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio φ →
    FamilyNorms.IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio h →
    IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V → AreUnitVectors X →
    (∀ w X' : imaginaryQuaternions, ‖w‖ < Real.pi → IsRightTranslationDeriv w X' (Th w X')) →
    ThirdOrderHypotheses Th s T.a T.chainParams.ρA T.ballRadius x T.κ α β (frameRadius x) T.p Cq
      V Y e X (familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ V) A →
    ∑ y' ∈ sitesOfCells (finiteCells F) F.depth,
      |ballCovariance (cutoffFactor T.ballRadius T.p)
        (familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ V) A
        (fun η => bondDeriv (interpolatedExpansion s T.a T.chainParams.ρA (frameRadius x) h y' η) V e X)| ≤
      T.Cs * (1 + ∑ q ∈ Finset.range 7, Cq q) * T.energyRatio * (α + x ^ (-(1 / 2 : ℝ)) * β) *
        Real.exp (-(T.κ / 2 ^ 5 * bondSpan Y e))
def thirdOrderCovarianceBound : Prop :=
  EventuallyInParameters fun T => ∀ Cq : ℕ → ℝ, (∀ q, 0 ≤ Cq q) → thirdOrderCovarianceBoundAt T Cq
end Interpolation
end YangMills.Construction
end
