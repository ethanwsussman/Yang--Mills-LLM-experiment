import YangMills.Construction.ResponseInTheExpansion.CurvatureOfALevelOnTheDraws
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.AxialGauge
open TorusFields ResponseInTheExpansion BlockAverages
def axialGaugeCurlBoundStatement : Prop :=
  ∀ (n : ℕ) [NeZero n] (R : ℕ), 1 ≤ R → 16 * R < n → ∀ o y : TorusSite n, y ∈ supBall o (2 * R) →
    ∀ v : TorusBond n → imaginaryQuaternions,
    ∃ A : TorusBond n → imaginaryQuaternions,
      (∀ (x : TorusSite n) (i : Fin 4),
          ¬ (x ∈ supBall o (2 * R) ∧ x + TorusFields.unitStep n i ∈ supBall o (2 * R)) → A (x, i) = 0) ∧
      (∀ p ∈ plaquettesIn (supBall o (2 * R)), lieFormCurl (v - A) p = 0) ∧
      ∀ (x : TorusSite n) (i : Fin 4) (M : ℝ), 0 ≤ M → x ∈ supBall o (2 * R) →
        x + TorusFields.unitStep n i ∈ supBall o (2 * R) →
        (∀ p ∈ plaquettesIn (supBall o (2 * R)), supDist p.1 y ≤ supDist x y → ‖lieFormCurl v p‖ ≤ M) →
        ‖A (x, i)‖ ≤ 3 * ((supDist x y : ℝ) * M)
end YangMills.Construction.AxialGauge
end
