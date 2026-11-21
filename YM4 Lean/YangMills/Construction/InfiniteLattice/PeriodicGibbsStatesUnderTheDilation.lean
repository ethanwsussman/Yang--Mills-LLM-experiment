import YangMills.Construction.InfiniteLattice.ConfigurationsFunctionsAndMeasures
import YangMills.Construction.InfiniteLattice.DictionaryBetweenSpacings
import YangMills.Construction.InfiniteLattice.ErgodicPhases
import YangMills.Construction.InfiniteLattice.InvariantEventsErgodicStatesAndExtremePoints
import YangMills.Construction.InfiniteLattice.LatticeMirrorsGivenWithANormal
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.GibbsAtFixedSpacing
open MeasureTheory YangMills.Construction.InfiniteLattice
open YangMills.Construction.LatticeConventions (NormalHyperplane Point euclidDot)
def periodicGibbsAtMesh (a β : ℝ) : Set (Measure (GaugeField a)) :=
  {ν | IsPeriodicGibbs β ν}
def periodicGibbsAtMeshProb (a β : ℝ) : Set (BorelProb a) :=
  {ν | ν.1 ∈ periodicGibbsAtMesh a β}
def IsConvexStateSet {a : ℝ} (𝒢 : Set (Measure (GaugeField a))) : Prop :=
  ∀ ν₁ ∈ 𝒢, ∀ ν₂ ∈ 𝒢, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    ENNReal.ofReal t • ν₁ + ENNReal.ofReal (1 - t) • ν₂ ∈ 𝒢
def PushToUnitAffineOn {a : ℝ} (𝒢 : Set (Measure (GaugeField a))) : Prop :=
  ∀ ν₁ ∈ 𝒢, ∀ ν₂ ∈ 𝒢, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    pushToUnit (ENNReal.ofReal t • ν₁ + ENNReal.ofReal (1 - t) • ν₂) =
      ENNReal.ofReal t • pushToUnit ν₁ + ENNReal.ofReal (1 - t) • pushToUnit ν₂
namespace PeriodicGibbsUnderRescaling
def PushToUnitIsAffineHomeomorph (a β : ℝ) : Prop :=
  Set.BijOn pushToUnit (periodicGibbsAtMesh a β) (periodicGibbsAtMesh 1 β) ∧
    PushToUnitAffineOn (periodicGibbsAtMesh a β) ∧
    ∃ e : periodicGibbsAtMeshProb a β ≃ₜ periodicGibbsAtMeshProb 1 β,
      ∀ ν, (e ν : BorelProb 1).1 = pushToUnit (ν : BorelProb a).1
def PushToUnitPreservesErgodicAndExtreme (a β : ℝ) : Prop :=
  IsConvexStateSet (periodicGibbsAtMesh a β) ∧
    IsConvexStateSet (periodicGibbsAtMesh 1 β) ∧
    (∀ ν ∈ periodicGibbsAtMesh a β,
      (IsShiftInvariant ν ∧ IsShiftErgodic ν) ↔
        (IsShiftInvariant (pushToUnit ν) ∧ IsShiftErgodic (pushToUnit ν))) ∧
    ∀ ν ∈ periodicGibbsAtMesh a β,
      IsExtremeState (periodicGibbsAtMesh a β) ν ↔
        IsExtremeState (periodicGibbsAtMesh 1 β) (pushToUnit ν)
def MirrorReflectionsAreMotions (a : ℝ) : Prop :=
  ∀ Q : NormalHyperplane, Q.IsLatticeMirror a → Q.reflect ∈ affineHyperoctahedralMaps a
def LatticePreservingHyperplanesAreMirrors (a : ℝ) : Prop :=
  ∀ (u : Point) (s : ℝ), u ≠ 0 →
    hyperplaneReflect u s '' (latticeSubgroup a : Set AmbientSpace) = latticeSubgroup a →
    ∃ Q : NormalHyperplane, Q.IsLatticeMirror a ∧ Q.carrier = {x | euclidDot u x = s}
def Statement : Prop :=
  ∀ a β : ℝ, 0 < a → 0 < β →
    PushToUnitIsAffineHomeomorph a β ∧
      (∀ L K : ℕ, periodicGibbsAtMesh (YangMills.Construction.PeriodicLattice.meshSize L (K : ℤ)) β =
        periodicGibbsSet L K β) ∧
      PushToUnitPreservesErgodicAndExtreme a β ∧
      MirrorReflectionsAreMotions a ∧
      LatticePreservingHyperplanesAreMirrors a
end PeriodicGibbsUnderRescaling
end YangMills.Construction.GibbsAtFixedSpacing
