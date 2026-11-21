import YangMills.Construction.InfiniteLattice.OneLatticeItsConfigurationsAndMeasuresOnCompactSpaces
import Mathlib
noncomputable section
namespace YangMills.Construction
open InfiniteLattice
namespace LatticePhases
def IsCountableDenseLocal (a : ℝ) (𝒟 : Set (GaugeField a → ℂ)) : Prop :=
  𝒟 ⊆ continuousLocalFunctions a ∧ 𝒟.Countable ∧
    ∀ F ∈ continuousLocalFunctions a, ∀ ε : ℝ, 0 < ε → ∃ H ∈ 𝒟, uniformSup (F - H) < ε
def denseLocalSet (L : ℕ) (K : ℕ+) : Set (GaugeField (refinedSpacing L (K : ℕ)) → ℂ) :=
  Classical.epsilon (IsCountableDenseLocal (refinedSpacing L (K : ℕ)))
theorem denseLocalSet_spec (L : ℕ) (K : ℕ+)
    (h : ∃ 𝒟, IsCountableDenseLocal (refinedSpacing L (K : ℕ)) 𝒟) :
    IsCountableDenseLocal (refinedSpacing L (K : ℕ)) (denseLocalSet L K) :=
  Classical.epsilon_spec h
namespace Setup
variable (D : Setup)
def denseLocalSet : Set (GaugeField D.mesh → ℂ) :=
  LatticePhases.denseLocalSet D.L D.K
end Setup
end LatticePhases
end YangMills.Construction
