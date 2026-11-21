import YangMills.Construction.ResponseInTheExpansion.ColdPartAtTheParameters
import YangMills.Construction.ResponseInTheExpansion.TailOfAScore
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.FamilyNorms
namespace YangMills.Construction
namespace WeightedResponses
abbrev FramedFamily : Type := (F : BlockFrame) → F.Cell → AboveFrames F
def ExpectationDecays (T : StepParameters) (t : ℕ) (x : ℝ) (f : LocalFamily) (h : ℝ) (K : FramedFamily) : Prop :=
  ∀ (F : BlockFrame) (Y : F.Cell) (V : F.GaugeField F.top), IsCubicTopTorus T.L t T.n₀ F →
    IsSmallCurvature (5 / 4 * T.σ) V →
    ContDiffThreeAlongBonds ((coldHalfLawAt T x f).expectationOf (K F Y)) V ∧
    ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 →
      AreUnitVectors X →
      |bondDeriv ((coldHalfLawAt T x f).expectationOf (K F Y)) V c X| ≤
        T.CE * h * Real.exp (-(T.κ / 2 ^ 5 * bondSpan Y c))
def ExpectationIsLocal (T : StepParameters) (t : ℕ) (x : ℝ) (f : LocalFamily) (h : ℝ) (K : FramedFamily) : Prop :=
  ∀ (F F' : BlockFrame) (Y : F.Cell) (Y' : F'.Cell) (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (q k : ℕ)
    (b : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions),
    IsCubicTopTorus T.L t T.n₀ F → IsCubicTopTorus T.L t T.n₀ F' →
    IsSmallCurvature (9 / 8 * T.σ) V → IsSmallCurvature (9 / 8 * T.σ) V' →
    AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' q → k ≤ 2 → (∀ l, BondWithinRadius q (b l)) →
    AreUnitVectors X →
    |bondDeriv ((coldHalfLawAt T x f).expectationOf (K F Y)) V (bondsAt Y b) X -
        bondDeriv ((coldHalfLawAt T x f).expectationOf (K F' Y')) V' (bondsAt Y' b) X| ≤
      T.CE * h * Real.exp (-(2 * T.decayRate * q))
def ExpectationIsLocalOnTorus (T : StepParameters) (x : ℝ) (f : LocalFamily) (h : ℝ) {F : BlockFrame}
    (Y : F.Cell) (K : AboveFrames F) : Prop :=
  ∀ (V V' : F.GaugeField F.top) (q k : ℕ) (b : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions),
    IsSmallCurvature (9 / 8 * T.σ) V → IsSmallCurvature (9 / 8 * T.σ) V' →
    AgreeOnBall (finiteCells F) V (finiteCells F) V' Y Y q → k ≤ 2 → (∀ l, BondWithinRadius q (b l)) →
    AreUnitVectors X →
    |bondDeriv ((coldHalfLawAt T x f).expectationOf K) V (bondsAt Y b) X -
        bondDeriv ((coldHalfLawAt T x f).expectationOf K) V' (bondsAt Y b) X| ≤
      T.CE * h * Real.exp (-(2 * T.decayRate * q))
def cellBond {F : BlockFrame} (Y : F.Cell) (i : Fin 4) (backward : Bool) : F.Site F.top × Fin 4 :=
  (if backward then Y - unitStep F.top i else Y, i)
def SmoothIncrementExpectationsAt (T : StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily), T.coupling ≤ x →
    IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f →
    (ExpectationDecays T t x f (x ^ (-(1 / 2) : ℝ)) fun _ Y => (coldHalfLawAt T x f).blockIncrement Y) ∧
    (ExpectationIsLocal T t x f (x ^ (-(1 / 2) : ℝ)) fun _ Y => (coldHalfLawAt T x f).blockIncrement Y) ∧
    (ExpectationDecays T t x f 1 fun _ Y => (coldHalfLawAt T x f).linearBlockPart Y) ∧
    (ExpectationIsLocal T t x f 1 fun _ Y => (coldHalfLawAt T x f).linearBlockPart Y) ∧
    (∀ (i : Fin 4) (backward : Bool),
      (ExpectationDecays T t x f (x ^ (-(1 / 2) : ℝ)) fun _ Y =>
        (coldHalfLawAt T x f).scoreRemainderIncrement (cellBond Y i backward)) ∧
      ExpectationIsLocal T t x f (x ^ (-(1 / 2) : ℝ)) fun _ Y =>
        (coldHalfLawAt T x f).scoreRemainderIncrement (cellBond Y i backward)) ∧
    ∀ (F : BlockFrame) (Y : F.Cell) (w : F.Site F.depth → ℝ) (B : ℝ), 0 ≤ B → (∀ y, |w y| ≤ B) →
      IsCubicTopTorus T.L t T.n₀ F →
      (∀ V : F.GaugeField F.top, IsSmallCurvature (5 / 4 * T.σ) V →
        ContDiffThreeAlongBonds
          ((coldHalfLawAt T x f).expectationOf ((coldHalfLawAt T x f).weightedShareIncrement w Y)) V ∧
        ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 →
          AreUnitVectors X →
          |bondDeriv ((coldHalfLawAt T x f).expectationOf ((coldHalfLawAt T x f).weightedShareIncrement w Y))
              V c X| ≤
            T.CE * (B * x ^ (-(1 / 2) : ℝ)) * Real.exp (-(T.κ / 2 ^ 5 * bondSpan Y c))) ∧
      ExpectationIsLocalOnTorus T x f (B * x ^ (-(1 / 2) : ℝ)) Y
        ((coldHalfLawAt T x f).weightedShareIncrement w Y)
def SmoothIncrementExpectations : Prop := EventuallyInParameters SmoothIncrementExpectationsAt
end WeightedResponses
end YangMills.Construction
end
