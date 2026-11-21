import YangMills.Construction.InfiniteLattice.PeriodicExtensionsAndTheirWeakLimitPoints
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.InfiniteLattice.PeriodicExtensions
def EveryStateSequenceHasWeaklyConvergentSubsequence.Statement : Prop :=
  ∀ (s : YangMills.Construction.Conventions.StandingParameters)
    (μ : ℕ+ → RealWeakState (YangMills.Construction.PeriodicLattice.meshSize s.L ((s.K : ℕ) : ℤ))),
    ∃ (n : ℕ+ → ℕ+) (ν : RealWeakState (YangMills.Construction.PeriodicLattice.meshSize s.L ((s.K : ℕ) : ℤ))),
      StrictMono n ∧
        ∀ F : C(YangMills.Construction.InfiniteLattice.GaugeField
            (YangMills.Construction.PeriodicLattice.meshSize s.L ((s.K : ℕ) : ℤ)), ℝ),
          Tendsto (fun k : ℕ+ => (μ (n k)).value F) atTop (𝓝 (ν.value F))
end YangMills.Construction.InfiniteLattice.PeriodicExtensions
