import YangMills.Construction.TorusOrFourSpace.BoundFunctionsAndEffectiveConstants
import YangMills.Construction.TorusOrFourSpace.MultilinearFunctionalsAndSetsAtPositiveDistance
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace
open Kind
namespace TorusEffectiveBound
def Claim : Prop :=
  ∀ (D : Params) (θ : RadiusRatio) (P : TorusPartitionChoice D θ) (C : BoundFamily) (n : ℕ),
    2 ≤ n → ∀ d : ℝ, 0 < d →
    ∀ Ψ : sepC1Tuples D torus n → ℝ,
      IsMultilinearOn D torus (sepC1Tuples D torus n) Ψ →
      (∀ g : sepC1Tuples D torus n,
        g.1 ∈ lipTuplesSpacedInBalls D torus n d (ballRadius D θ torus) →
        ENNReal.ofReal |Ψ g| ≤
          ENNReal.ofReal (C.val n d (ballRadius D θ torus)) *
            ∏ i, sharpNormQ D torus (g.1 i)) →
      (∀ R : ℝ, R ∈ Set.Ici (D.side / 4) ↔ 0 < R ∧ R ∉ allowedRadii D torus) ∧
      ∀ R ∈ Set.Ici (D.side / 4),
        effConst P torus C n d R =
          thetaNumber P torus ^ n * C.val n d (ballRadius D θ torus) ∧
        ∀ h : sepC1Tuples D torus n, ENNReal.ofReal d ≤ supportGap D torus h.1 →
          ENNReal.ofReal |Ψ h| ≤
            ENNReal.ofReal (effConst P torus C n d R) *
              ∏ i, sharpNormQ D torus (h.1 i)
end TorusEffectiveBound
end YangMills.Construction.PeriodicSpace
