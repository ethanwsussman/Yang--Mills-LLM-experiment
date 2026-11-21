import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.WeightedResponses
variable {R : StepSettings.StepSetup} {n : ℕ} [NeZero n]
def gasTermAtBlock (A : ResponseSetup R) (G : StepGas.GasGround R n) (Y : TorusFields.TorusSite n)
    (h : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) : ℝ :=
  ∑ y ∈ TorusLumps.sitesInBlocks R.params.side {Y}, gasResponseShift A G y h +
    R.params.coupling / 2 * A.coeff * blockMean R.params.side (R.depth + 1) n Y h *
      ∑ i : Fin 4, (gasBondScoreShift G (Y, i) + gasBondScoreShift G (Y - TorusFields.unitStep n i, i))
def GasTermAtColdFields : Prop :=
  HoldsAtEveryStep fun T R A => R.IsSymmetricWeight →
    (∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n → ∀ (Y : TorusFields.TorusSite n) (V : TorusFields.TorusField n),
      TorusFields.IsCold R.params.threshold V →
      ∀ h : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n),
        |gasTermAtBlock A (StepGas.coldCaseGround R V) Y h| ≤
            Real.exp (-(5 * T.gasRate * R.coupling)) * weightNorm R.params.side R.depth h ∧
        TorusFields.ContDiffThreeAt
            (fun V' : TorusFields.TorusField n => gasTermAtBlock A (StepGas.coldCaseGround R V') Y h) V ∧
        ∀ (k : ℕ) (c : Fin k → TorusFields.TorusBond n) (X : Fin k → BlockAverages.imaginaryQuaternions),
          1 ≤ k → k ≤ 3 → BlockAverages.AreUnitVectors X →
          |TorusFields.mixedDeriv
              (fun V' : TorusFields.TorusField n => gasTermAtBlock A (StepGas.coldCaseGround R V') Y h) V c X| ≤
            Real.exp (-(T.gasRate * R.coupling / 2)) * weightNorm R.params.side R.depth h /
              R.params.weight (TorusFields.supportDiam Y c)) ∧
    ∀ (n n' : ℕ) [NeZero n] [NeZero n'], R.params.n₀ ≤ n → R.params.n₀ ≤ n' →
      ∀ (Y : TorusFields.TorusSite n) (Y' : TorusFields.TorusSite n') (V : TorusFields.TorusField n)
        (V' : TorusFields.TorusField n') (m : ℕ), 2 * m + 2 < n → 2 * m + 2 < n' →
        TorusFields.IsCold R.params.threshold V → TorusFields.IsCold R.params.threshold V' →
        TorusLumps.FieldsAgreeNear V V' Y Y' m →
        ∀ (h : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
          (h' : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n')),
          WeightsAgreeAt R.params.side (R.depth + 1) Y Y' h h' →
          ∀ (k : ℕ) (b : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → BlockAverages.imaginaryQuaternions), k ≤ 2 →
            (∀ l, TorusFields.BondOffsetInBox m (b l)) → BlockAverages.AreUnitVectors X →
            |TorusFields.mixedDeriv (fun U : TorusFields.TorusField n => gasTermAtBlock A (StepGas.coldCaseGround R U) Y h)
                  V (fun l => TorusLumps.bondFrom Y (b l)) X -
                TorusFields.mixedDeriv
                  (fun U : TorusFields.TorusField n' => gasTermAtBlock A (StepGas.coldCaseGround R U) Y' h')
                  V' (fun l => TorusLumps.bondFrom Y' (b l)) X| ≤
              Real.exp (-(T.gasRate * R.coupling / 2)) * weightNorm R.params.side R.depth h / R.params.weight m
end YangMills.Construction.WeightedResponses
end
