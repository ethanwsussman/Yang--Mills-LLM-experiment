import YangMills.Construction.InfiniteLattice.HyperoctahedralMotionsAndCubes
import YangMills.Construction.InfiniteLattice.StatesAtOneSpacing
import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import Mathlib
set_option autoImplicit false

section
open Set
open scoped ComplexConjugate Matrix
noncomputable section
namespace YangMills.Construction.SingleMeshMirrors
abbrev MeshMirror (L K : ℕ) : Type :=
  InfiniteLattice.LatticeMirror (PeriodicLattice.meshSize L (K : ℤ))
variable {L K : ℕ}
abbrev meshMirrorSymmetry (Q : MeshMirror L K) :
    InfiniteLattice.LatticeSymmetry (PeriodicLattice.meshSize L (K : ℤ)) :=
  InfiniteLattice.LatticeMirror.symmetry Q
def halfSpaces (Q : MeshMirror L K) : Set (Set (Fin 4 → ℝ)) :=
  {H | InfiniteLattice.LatticeMirror.IsHalfSpace Q H}
end YangMills.Construction.SingleMeshMirrors
end
end

open MeasureTheory
open scoped NNReal ComplexOrder
noncomputable section
namespace YangMills.Construction.InfiniteLattice.PeriodicStatesAllScales
open SingleMeshMirrors
variable {L K : ℕ}
def reflectionPairing (μ : GaugeFieldProbability (PeriodicLattice.meshSize L (K : ℤ)))
    (M : MeshMirror L K) (G : GaugeField (PeriodicLattice.meshSize L (K : ℤ)) → ℂ) : ℂ :=
  μ.expect fun V => LatticeMirror.conjReflect M G V * G V
def IsReflectionPositiveAt
    (μ : GaugeFieldProbability (PeriodicLattice.meshSize L (K : ℤ))) (M : MeshMirror L K) : Prop :=
  IsSymmetricUnder μ.1 (meshMirrorSymmetry M) ∧
    ∀ S ∈ halfSpaces M, ∀ G : GaugeField (PeriodicLattice.meshSize L (K : ℤ)) → ℂ,
      IsBoundedObservable G → IsRegionMeasurable S G → 0 ≤ reflectionPairing μ M G
def HasSymmetriesAndPositivity
    (μ : GaugeFieldProbability (PeriodicLattice.meshSize L (K : ℤ))) : Prop :=
  (∀ v : LatticePoint (PeriodicLattice.meshSize L (K : ℤ)), IsSymmetricUnder μ.1 (shift v)) ∧
    (∀ g : LatticeSymmetry (PeriodicLattice.meshSize L (K : ℤ)), ∀ w ∈ hyperoctahedralLinearGroup,
      (∀ x, g.toFun x = w x) → IsSymmetricUnder μ.1 g) ∧
    ∀ M : MeshMirror L K, IsReflectionPositiveAt μ M
def IsShiftInvariantGibbs (β : ℝ)
    (μ : GaugeFieldProbability (PeriodicLattice.meshSize L (K : ℤ))) : Prop :=
  IsGibbs β μ.1 ∧ ∀ v : LatticePoint (PeriodicLattice.meshSize L (K : ℤ)),
    IsSymmetricUnder μ.1 (shift v)
def PeriodicStatesCharacterizedAndCompact (L K : ℕ) (β : ℝ) : Prop :=
  periodicGibbsStates L K β = {μ | IsShiftInvariantGibbs β μ} ∧
    (periodicGibbsStates L K β).Nonempty ∧
    Convex ℝ≥0 ((fun μ : GaugeFieldProbability (PeriodicLattice.meshSize L (K : ℤ)) => μ.1) ''
      periodicGibbsStates L K β) ∧
    IsCompact (periodicGibbsStates L K β)
def ClusterPointsAreShiftInvariantGibbs (L K : ℕ) (β : ℝ) : Prop :=
  (∀ μ ∈ weakClusterPointsOfLifts L K β, IsShiftInvariantGibbs β μ) ∧
    weakClusterPointsOfLifts L K β ⊆ periodicGibbsStates L K β
def AllScalesAllCouplings : Prop :=
  ∀ L K : ℕ, Odd L → 13 ≤ L → 0 < K → ∀ β : ℝ, 0 < β →
    (∀ μ ∈ periodicGibbsStates L K β, HasSymmetriesAndPositivity μ) ∧
      PeriodicStatesCharacterizedAndCompact L K β ∧
      ClusterPointsAreShiftInvariantGibbs L K β
end YangMills.Construction.InfiniteLattice.PeriodicStatesAllScales
end
