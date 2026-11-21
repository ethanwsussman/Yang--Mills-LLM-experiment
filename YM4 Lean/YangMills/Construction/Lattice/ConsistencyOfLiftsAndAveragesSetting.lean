import YangMills.Construction.Averaging.SmoothingRadius
import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.BlockAveraging
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Conventions.StandingParameters
def pointClass (s : StandingParameters) (v : Fin 4 → ℝ) : s.Torus :=
  fun μ => (v μ : AddCircle (PeriodicLattice.torusSide s.L s.m))
abbrev BondAt (s : StandingParameters) (j : ℕ) : Type :=
  PeriodicLattice.BondAtLevel s.L s.m s.K j
end Conventions.StandingParameters
namespace PeriodicLattice
variable {L m : ℕ} {j j' : ℤ}
abbrev IsComplexGaugeField (ℬ : Set (Bond L m j)) (U : Bond L m j → Matrices.ComplexMatrix2) : Prop :=
  IsGaugeField complexGaugeGroup ℬ U
def smallFieldsAtSmoothingRadius (c : Bond L m j) : Set (Bond L m j' → Matrices.ComplexMatrix2) :=
  smallPlaquetteFields (Averaging.smoothingRadius L) c
def blockAverageAtSmoothingRadius (U : Bond L m j' → Matrices.ComplexMatrix2) :
    Bond L m j → Matrices.ComplexMatrix2 :=
  blockAverage (Averaging.smoothingRadius L) U
def pathSites (z z' : Site L m j) (Γ : List (Bond L m j)) : Set (Site L m j) :=
  {x | x = z ∨ x = z' ∨ ∃ b ∈ Γ, x = b.source ∨ x = b.target}
def Bond.IsNegativelyOriented (b : Bond L m j) : Prop := ¬ b.IsPositivelyOriented
end PeriodicLattice
end YangMills.Construction
end
