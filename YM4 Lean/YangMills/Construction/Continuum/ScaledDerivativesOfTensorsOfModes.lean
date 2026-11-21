import YangMills.Construction.Continuum.LocalFunctionalsOfAForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigSpace
def ScaledModeTensorDerivBound : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (Q : PointSystem n) (ν : ℕ), ∃ K : ℝ, 0 ≤ K ∧ ∀ ξ ∈ Q.freqLattice,
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (tensorProd (Q.modeFamily ξ)) ∧
      ∀ α : MultiIndex n, α.order ≤ ν → ∀ x : Config n,
        Q.scale ^ α.order * ‖iteratedPartial α (tensorProd (Q.modeFamily ξ)) x‖ ≤
          K * (1 + Q.scale * coordSupNorm ξ) ^ ν
end YangMills.Construction.ConfigSpace
