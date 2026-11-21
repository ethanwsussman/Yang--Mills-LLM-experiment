import YangMills.Construction.InfiniteLattice.VolumeFirstLimits
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
open Filter MeasureTheory
open scoped Topology
structure WindowedApproximants (L : ℕ) (W : ℕ+ → Set ℝ) where
  K : ℕ+ → ℕ+
  tendsto_K : Tendsto (fun j => (K j : ℕ)) atTop atTop
  β : ℕ+ → ℝ
  β_mem_window : ∀ j, β j ∈ W (K j)
  ν : ∀ j, Measure (GaugeField (PeriodicLattice.meshSize L (((K j : ℕ)) : ℤ)))
  isInfiniteVolumeLimit : ∀ j, IsInfiniteVolumeLimit L (K j) (β j) (ν j)
def WindowedApproximants.ConvergesTo {L : ℕ} {W : ℕ+ → Set ℝ} (Q : WindowedApproximants L W)
    (S : (n : ℕ) → (Fin n → AmbientSpace → ℝ) → ℂ) : Prop :=
  ∀ n, 2 ≤ n → ∀ f : Fin n → AmbientSpace → ℝ, IsSeparatedC1cTuple f →
    Tendsto (fun j => smearedEnergyCumulant (Q.ν j) f) atTop (𝓝 (S n f))
def IsWindowedVolumeLimit (L : ℕ) (W : ℕ+ → Set ℝ)
    (S : (n : ℕ) → (Fin n → AmbientSpace → ℝ) → ℂ) : Prop :=
  SchwingerFunctions.IsContinuumSchwingerFamily S ∧ ∃ Q : WindowedApproximants L W, Q.ConvergesTo S
end InfiniteLattice
end YangMills.Construction
end
