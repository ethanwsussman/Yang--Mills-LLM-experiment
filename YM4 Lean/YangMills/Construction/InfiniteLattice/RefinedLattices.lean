import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import Mathlib
noncomputable section
namespace YangMills.Construction.InfiniteLattice
abbrev refinedSpacing (L K : ℕ) : ℝ := PeriodicLattice.meshSize L (K : ℤ)
abbrev refinedLattice (L K : ℕ) : AddSubgroup AmbientSpace := latticeSubgroup (refinedSpacing L K)
abbrev RefinedGaugeField (L K : ℕ) : Type := GaugeField (refinedSpacing L K)
end YangMills.Construction.InfiniteLattice
