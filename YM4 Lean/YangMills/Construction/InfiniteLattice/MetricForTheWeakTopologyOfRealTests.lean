import YangMills.Construction.InfiniteLattice.PeriodicExtensionsAndTheirWeakLimitPoints
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.InfiniteLattice.PeriodicExtensions
namespace RealWeakState
variable {a : ℝ}
def IsSupNormDenseSeq (F : ℕ+ → C(GaugeField a, ℝ)) : Prop :=
  ∀ (H : C(GaugeField a, ℝ)) (ε : ℝ), 0 < ε →
    ∃ k, CutoffLattice.supNorm (H - F k) < ε
def weakMetricTerm (F : ℕ+ → C(GaugeField a, ℝ)) (μ μ' : RealWeakState a) (k : ℕ+) : ℝ :=
  (2 : ℝ) ^ (-((k : ℕ) : ℤ)) * min 1 |μ.value (F k) - μ'.value (F k)|
def weakMetric (F : ℕ+ → C(GaugeField a, ℝ)) (μ μ' : RealWeakState a) : ℝ :=
  ∑' k, weakMetricTerm F μ μ' k
end RealWeakState
open RealWeakState in
def WeakMetricStatement : Prop :=
  ∀ L K : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < K →
    ∀ F : ℕ+ → C(GaugeField (PeriodicLattice.meshSize L (K : ℤ)), ℝ), IsSupNormDenseSeq F →
      (∀ μ μ' : RealWeakState (PeriodicLattice.meshSize L (K : ℤ)),
        Summable (weakMetricTerm F μ μ') ∧ 0 ≤ weakMetric F μ μ' ∧ weakMetric F μ μ' ≤ 1) ∧
      (∀ μ' : RealWeakState (PeriodicLattice.meshSize L (K : ℤ)),
        Continuous fun μ => weakMetric F μ μ') ∧
      (∀ (μ : ℕ → RealWeakState (PeriodicLattice.meshSize L (K : ℤ)))
        (ν : RealWeakState (PeriodicLattice.meshSize L (K : ℤ))),
        Tendsto (fun i => weakMetric F (μ i) ν) atTop (𝓝 0) ↔
          RealWeakState.TendstoWeakly μ ν) ∧
      (∃ M : MetricSpace (RealWeakState (PeriodicLattice.meshSize L (K : ℤ))),
        (∀ μ μ', M.dist μ μ' = weakMetric F μ μ') ∧
          M.toUniformSpace.toTopologicalSpace = RealWeakState.weakTopology) ∧
      CompactSpace (RealWeakState (PeriodicLattice.meshSize L (K : ℤ))) ∧
      TopologicalSpace.MetrizableSpace (RealWeakState (PeriodicLattice.meshSize L (K : ℤ)))
end YangMills.Construction.InfiniteLattice.PeriodicExtensions
