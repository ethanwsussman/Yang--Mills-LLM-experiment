import YangMills.Construction.TestFunctions.SeparatedBumpPairs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace LinearResponse
def FreeKernelPositiveOnSeparatedPairs : Prop :=
  ∀ (L m : ℕ) (n vt : ℝ), 0 < n → 0 < vt → vt ≤ 1 → 40 * n ≤ PeriodicLattice.torusSide L m →
    ∀ f h : PeriodicLattice.FourTorus L m → ℝ, (f, h) ∈ TestFunctions.separatedPairsFourTorus L m n vt →
      TestFunctions.uniformNorm f = 1 → TestFunctions.uniformNorm h = 1 →
      1 / 10 ^ 8 * vt ^ 2 ≤ TestFunctions.inverseEighthKernelTorus f h
end LinearResponse
end YangMills.Construction
end
