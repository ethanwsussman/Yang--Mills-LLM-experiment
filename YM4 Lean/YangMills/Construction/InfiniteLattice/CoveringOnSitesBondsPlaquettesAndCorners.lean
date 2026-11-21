import YangMills.Construction.InfiniteLattice.BondsAndCutPlaquettesAtAMirror
import YangMills.Construction.InfiniteLattice.CoveringPeriodicExtensionsAndTheTwoSetsOfStates
import YangMills.Construction.InfiniteLattice.WindowDensitiesAndStandardWindows
import YangMills.Construction.Lattice.BondsOfTheTorusLatticeAndThePeriodicExtension
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.InfiniteLattice.LatticeCovering
open CutoffLattice
variable (L m K : ℕ)
def SitesCover : Prop :=
  latticeSubgroup 1 ≤ latticeAt L K ∧ latticeSubgroup (PeriodicLattice.torusSide L m) ≤ latticeAt L K ∧
    (∀ x y : AmbientSpace,
      torusCover L m x = torusCover L m y ↔ y - x ∈ latticeSubgroup (PeriodicLattice.torusSide L m)) ∧
    (∀ x y : AmbientSpace, torusCover L m (x + y) = torusCover L m x + torusCover L m y) ∧
    torusCover L m '' (latticeAt L K : Set AmbientSpace) =
      (PeriodicLattice.sublattice L m (K : ℤ) : Set (PeriodicLattice.FourTorus L m))
def LinksCover : Prop :=
  (∀ e ∈ positiveLinksAt L K, ∀ e' ∈ positiveLinksAt L K,
    projectLink L m (K : ℤ) e = projectLink L m (K : ℤ) e' ↔
      ∃ v : LatticePoint (spacingAt L K),
        (v : AmbientSpace) ∈ latticeSubgroup (PeriodicLattice.torusSide L m) ∧ e' = translateLink e v) ∧
    ∀ (U : PeriodicLattice.CompactGaugeField L m (K : ℤ)) (e : Link (spacingAt L K))
      (v : LatticePoint (spacingAt L K)),
      (v : AmbientSpace) ∈ latticeSubgroup (PeriodicLattice.torusSide L m) →
      liftCompactField U (translateLink e v) = liftCompactField U e
def PlaquettesCover : Prop :=
  ∀ p : ElementaryPlaquette (spacingAt L K),
    (∀ U : PeriodicLattice.CompactGaugeField L m (K : ℤ),
      ((faceHolonomy (liftCompactField U) p : Matrices.ComplexMatrix2.specialUnitary) :
          Matrices.ComplexMatrix2) =
          PeriodicLattice.plaquetteHolonomy U.1 (projectFace L m K p) ∧
        faceEnergy (liftCompactField U) p =
          PeriodicLattice.plaquetteCost U.1 (projectFace L m K p)) ∧
      (projectFace L m K p).barycenter = torusCover L m p.center
def WindowCorners (L K : ℕ) : Prop :=
  (∀ p : ElementaryPlaquette (spacingAt L K), ∀ y ∈ NormalFamilies.plaquetteCorners p,
    ∀ y' ∈ NormalFamilies.plaquetteCorners p, ∀ μ : Fin 4,
      |(y : AmbientSpace) μ - (y' : AmbientSpace) μ| ≤ spacingAt L K) ∧
    (∀ p ∈ (cutoffWindow L K).faces, ∀ y ∈ NormalFamilies.plaquetteCorners p,
      TorusMetric.supNormVec (y : AmbientSpace) ≤ (K : ℝ) + spacingAt L K) ∧
    ∀ e ∈ ((cutoffWindow L K).links : Set (Link (spacingAt L K))) ∪ (cutoffWindow L K).rim,
      ∀ x ∈ endpoints e, ∃ p ∈ (cutoffWindow L K).faces,
        x ∈ NormalFamilies.plaquetteCorners p
def CoveringStatement : Prop :=
  ∀ s : Conventions.StandingParameters,
    SitesCover s.L s.m s.K ∧ LinksCover s.L s.m s.K ∧ PlaquettesCover s.L s.m s.K ∧
      WindowCorners s.L s.K
end YangMills.Construction.InfiniteLattice.LatticeCovering
end
