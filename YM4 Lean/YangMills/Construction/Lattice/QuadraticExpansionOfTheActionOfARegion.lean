import YangMills.Construction.Lattice.BareLatticeSpacesAndOperators
import YangMills.Construction.Lattice.WeightedWilsonActions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice.Bare
variable {L m : ℕ} {j : ℤ}
def twistedRegionEnergy (X : Set (FourTorus L m)) (ξ : ℝ)
    (U A : Bond L m j → Matrices.ComplexMatrix2) : ℂ :=
  interiorEnergy X (expTwist (fun e => (ξ : ℂ) • A e) U)
structure IsSecondOrderExpansion (X : Set (FourTorus L m)) (ξ : ℝ)
    (U J : Bond L m j → Matrices.ComplexMatrix2)
    (T : (Bond L m j → Matrices.ComplexMatrix2) → Bond L m j → Matrices.ComplexMatrix2) : Prop where
  current_mem : J ∈ bondFormSpace X
  map_mem : ∀ A ∈ bondFormSpace X, T A ∈ bondFormSpace X
  map_linear : ∀ A ∈ bondFormSpace X, ∀ B ∈ bondFormSpace X, ∀ c : ℂ,
    T (A + c • B) = T A + c • T B
  symmetric : ∀ A ∈ bondFormSpace X, ∀ B ∈ bondFormSpace X,
    bondFormInnerOn X ξ A (T B) = bondFormInnerOn X ξ (T A) B
  remainder : ∃ C r : ℝ, 0 < r ∧ ∀ A ∈ bondFormSpace X, ∀ s : ℝ, s ≤ r →
    (∀ e, Matrices.ComplexMatrix2.operatorNorm (A e) ≤ s) →
      ‖twistedRegionEnergy X ξ U A - twistedRegionEnergy X ξ U 0 -
          bondFormInnerOn X ξ A J -
          (1 / 2 : ℂ) * bondFormInnerOn X ξ A (T A)‖ ≤ C * s ^ 3
def secondOrderPair (X : Set (FourTorus L m)) (ξ : ℝ) (U : Bond L m j → Matrices.ComplexMatrix2) :
    (Bond L m j → Matrices.ComplexMatrix2) ×
      ((Bond L m j → Matrices.ComplexMatrix2) → Bond L m j → Matrices.ComplexMatrix2) :=
  Classical.epsilon fun P => IsSecondOrderExpansion X ξ U P.1 P.2
def regionHessianOp (X : Set (FourTorus L m)) (ξ : ℝ) (U : Bond L m j → Matrices.ComplexMatrix2) :
    (Bond L m j → Matrices.ComplexMatrix2) → Bond L m j → Matrices.ComplexMatrix2 :=
  (secondOrderPair X ξ U).2
end YangMills.Construction.PeriodicLattice.Bare
