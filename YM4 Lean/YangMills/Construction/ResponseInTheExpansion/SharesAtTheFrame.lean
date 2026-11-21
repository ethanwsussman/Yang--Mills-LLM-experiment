import YangMills.Construction.ResponseInTheExpansion.ColdPartAtTheParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation
namespace WeightedResponses
variable {F : BlockFrame}
open Classical in
def ColdHalfLaw.weightedFrameShares (Q : ColdHalfLaw) (w : F.Site F.depth → ℝ) (Y : F.Cell)
    (V : F.GaugeField F.top) : ℝ :=
  ∑ y ∈ (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y),
    w y * minimalSiteShare Q.a y (interpolatedField 1 Q.a Q.chartRadius Q.mirrorRadius V 0)
def weightedFrameSharesStatementAt (T : StepParameters) : Prop :=
  ∀ (t : ℕ) (x B : ℝ) (f : LocalFamily) (F : BlockFrame) (Y : F.Cell) (w : F.Site F.depth → ℝ), T.coupling ≤ x →
    IsCubicTopTorus T.L t T.n₀ F → 0 ≤ B → (∀ y, |w y| ≤ B) →
    (∀ V : F.GaugeField F.top, IsSmallCurvature (5 / 4 * T.σ) V →
      ContDiffThreeAlongBonds ((coldHalfLawAt T x f).weightedFrameShares w Y) V ∧
      ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 →
        AreUnitVectors X →
        |bondDeriv ((coldHalfLawAt T x f).weightedFrameShares w Y) V c X| ≤
          T.Cs * B / torusDecayFactor T.L T.decayRate (bondSpan Y c)) ∧
    ∀ (V V' : F.GaugeField F.top) (q k : ℕ) (b : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions),
      IsSmallCurvature (9 / 8 * T.σ) V → IsSmallCurvature (9 / 8 * T.σ) V' →
      AgreeOnBall (finiteCells F) V (finiteCells F) V' Y Y q → k ≤ 2 → (∀ l, BondWithinRadius q (b l)) →
      AreUnitVectors X →
      |bondDeriv ((coldHalfLawAt T x f).weightedFrameShares w Y) V (bondsAt Y b) X -
          bondDeriv ((coldHalfLawAt T x f).weightedFrameShares w Y) V' (bondsAt Y b) X| ≤
        T.Cs * B / torusDecayFactor T.L T.decayRate q
def weightedFrameSharesStatement : Prop := EventuallyInParameters weightedFrameSharesStatementAt
end WeightedResponses
end YangMills.Construction
end
