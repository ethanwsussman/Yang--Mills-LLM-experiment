import YangMills.Construction.InfiniteLattice.PlaquettesAndTheDensityAtACutoff
import YangMills.Construction.InfiniteLattice.RefinedLattices
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def basePlaquette (L K : ℕ) : LatticeCutoffPlaquette L K := ⟨0, 0, 1, by decide⟩
def meanFaceEnergy {L K : ℕ} (ν : Measure (RefinedGaugeField L K)) : ℝ :=
  ∫ U, faceEnergy U (basePlaquette L K) ∂ν
def refinedRiemannSum (L K : ℕ) (f : AmbientSpace → ℂ) : ℂ :=
  1 / 6 * ∑ μ : Fin 4, ∑ κ ∈ Finset.Ioi μ, (refinedSpacing L K : ℂ) ^ 4 *
    ∑ᶠ x : LatticePoint (refinedSpacing L K),
      f ((x : AmbientSpace) + (refinedSpacing L K / 2) • (Pi.single μ 1 + Pi.single κ 1 : AmbientSpace))
end YangMills.Construction.InfiniteLattice
end
