import YangMills.Construction.ResponseInTheExpansion.BlockRemainderAboveTheFrame
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WeightedResponses
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
def meanRemainderBound (P : YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) : Prop :=
  ∀ (t : ℕ) (x e : ℝ) (f : LocalFamily) (F : BlockFrame) (r : F.Site F.depth → F.GaugeField F.depth → ℝ) (Y : F.Cell),
    P.coupling ≤ x →
    IsRegularFamily P.L t P.n₀ P.σ P.decayRate P.E P.energyRatio f → IsCubicTopTorus P.L t P.n₀ F → 0 ≤ e →
    IsTorusRemainder P.L P.σ P.decayRate e (e / P.η₃) r →
    (∀ V : F.GaugeField F.top, IsSmallCurvature (5 / 4 * P.σ) V →
      ContDiffThreeAlongBonds ((coldHalfLawAt P x f).expectationOf ((coldHalfLawAt P x f).blockSum r Y)) V ∧
      ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 → AreUnitVectors X →
        |bondDeriv ((coldHalfLawAt P x f).expectationOf ((coldHalfLawAt P x f).blockSum r Y)) V c X| ≤
          P.CE * (e / P.η₃) / torusDecayFactor P.L P.decayRate (bondSpan Y c)) ∧
    ∀ (V V' : F.GaugeField F.top) (q k : ℕ) (b : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions),
      IsSmallCurvature (9 / 8 * P.σ) V → IsSmallCurvature (9 / 8 * P.σ) V' →
      AgreeOnBall (finiteCells F) V (finiteCells F) V' Y Y q → k ≤ 2 → (∀ l, BondWithinRadius q (b l)) → AreUnitVectors X →
      |bondDeriv ((coldHalfLawAt P x f).expectationOf ((coldHalfLawAt P x f).blockSum r Y)) V (bondsAt Y b) X -
          bondDeriv ((coldHalfLawAt P x f).expectationOf ((coldHalfLawAt P x f).blockSum r Y)) V' (bondsAt Y b) X| ≤
        P.CE * (e / P.η₃) / torusDecayFactor P.L P.decayRate q
def meanRemainderStatement : Prop := EventuallyInParameters meanRemainderBound
end YangMills.Construction.WeightedResponses
end
