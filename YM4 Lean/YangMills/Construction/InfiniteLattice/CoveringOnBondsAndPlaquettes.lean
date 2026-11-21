import YangMills.Construction.InfiniteLattice.WindowsKernelOperatorAndDensitiesAtOneSpacing
import YangMills.Construction.Lattice.BondsOfTheTorusLatticeAndThePeriodicExtension
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.InfiniteLattice.Covering
def ProjectsPlaquetteEdges (L m K : ℕ) : Prop :=
  ∀ p : ElementaryPlaquette (CutoffLattice.spacingAt L K),
    projectLink L m (K : ℤ) (PeriodicExtensions.firstEdge p) =
        PeriodicExtensions.torusFirstEdge (CutoffLattice.projectFace L m K p) ∧
      projectLink L m (K : ℤ) (PeriodicExtensions.secondEdge p) =
        PeriodicExtensions.torusSecondEdge (CutoffLattice.projectFace L m K p) ∧
      projectLink L m (K : ℤ) (PeriodicExtensions.thirdEdge p) =
        PeriodicExtensions.torusThirdEdge (CutoffLattice.projectFace L m K p) ∧
      projectLink L m (K : ℤ) (PeriodicExtensions.fourthEdge p) =
        PeriodicExtensions.torusFourthEdge (CutoffLattice.projectFace L m K p)
def FaceEnergyOfLift (L m K : ℕ) : Prop :=
  ∀ (p : ElementaryPlaquette (CutoffLattice.spacingAt L K))
    (U : PeriodicLattice.CompactGaugeField L m (K : ℤ)),
    faceEnergy (liftCompactField U) p =
      PeriodicLattice.plaquetteCost U.1 (CutoffLattice.projectFace L m K p)
def PeriodLattice_le (L m K : ℕ) : Prop :=
  latticeSubgroup (PeriodicLattice.torusSide L m) ≤ CutoffLattice.latticeAt L K
def ProjectInvariantUnderPeriods (L m K : ℕ) : Prop :=
  ∀ (b : Link (CutoffLattice.spacingAt L K)) (v : LatticePoint (CutoffLattice.spacingAt L K)),
    (v : AmbientSpace) ∈ latticeSubgroup (PeriodicLattice.torusSide L m) →
    projectLink L m (K : ℤ) (CutoffLattice.translateLink b v) = projectLink L m (K : ℤ) b ∧
      ∀ U : PeriodicLattice.CompactGaugeField L m (K : ℤ),
        liftCompactField U (CutoffLattice.translateLink b v) = liftCompactField U b
def SameProjectionDifferByPeriod (L m K : ℕ) : Prop :=
  ∀ b ∈ CutoffLattice.positiveLinksAt L K, ∀ b' ∈ CutoffLattice.positiveLinksAt L K,
    projectLink L m (K : ℤ) b = projectLink L m (K : ℤ) b' →
    ∃ v : LatticePoint (CutoffLattice.spacingAt L K),
      (v : AmbientSpace) ∈ latticeSubgroup (PeriodicLattice.torusSide L m) ∧
        b' = CutoffLattice.translateLink b v
def WindowProjectsFaithfully (L m K : ℕ) (W : LinkWindow (PeriodicLattice.meshSize L (K : ℤ))) :
    Prop :=
  W.InjectsIntoTorus m →
    BijOn (CutoffLattice.projectFace L m K) W.faces
        {P | PeriodicExtensions.TorusPlaquetteHasEdgeIn P
          (projectLink L m (K : ℤ) '' (W.links : Set _))} ∧
      projectLink L m (K : ℤ) '' (W.links : Set _) ∩ projectLink L m (K : ℤ) '' W.rim = ∅
def injectiveSides (L K : ℕ) (S : Set (Link (CutoffLattice.spacingAt L K))) : Set ℝ :=
  {t | ∃ n : ℕ, 0 < n ∧ PeriodicLattice.torusSide L n = t ∧ InjOn (projectLink L n (K : ℤ)) S}
def EventuallyInjective (L K : ℕ) : Prop :=
  ∀ S : Set (Link (CutoffLattice.spacingAt L K)), S ⊆ CutoffLattice.positiveLinksAt L K →
    S.Finite →
    (injectiveSides L K S).Nonempty ∧
      ∀ t ∈ injectiveSides L K S, ∀ t' ∈ PeriodicLattice.torusSides L, t ≤ t' →
        t' ∈ injectiveSides L K S
def LeastTorusSideIsAttained {L K : ℕ} (W : LinkWindow (PeriodicLattice.meshSize L (K : ℤ))) :
    Prop :=
  (∃ t₀ ∈ PeriodicLattice.torusSides L, W.leastTorusSide = ((t₀ : ℝ) : EReal)) ∧
    W.torusSidesOfInjection =
      {t | t ∈ PeriodicLattice.torusSides L ∧ W.leastTorusSide ≤ ((t : ℝ) : EReal)}
def IsAxialTranslate {a : ℝ} (ℓ : ℝ) (k : ℤ) (b b' : Link a) : Prop :=
  ∃ v : LatticePoint a, (v : AmbientSpace) = ((k : ℝ) * ℓ) • (Pi.single 0 1 : AmbientSpace) ∧
    b' = CutoffLattice.translateLink b v
def AxialTranslatesExit (L m K : ℕ) (W : LinkWindow (PeriodicLattice.meshSize L (K : ℤ))) :
    Prop :=
  ∀ b ∈ W.links,
    {k : ℤ | ∃ b' ∈ W.links, IsAxialTranslate (PeriodicLattice.torusSide L m) k b b'}.Finite ∧
      (W.leastTorusSide ≤ ((PeriodicLattice.torusSide L m : ℝ) : EReal) →
        ∀ b', IsAxialTranslate (PeriodicLattice.torusSide L m) 1 b b' → b' ∉ W.links)
def CoveringProperties : Prop :=
  ∀ s : Conventions.StandingParameters,
    ProjectsPlaquetteEdges s.L s.m s.K ∧ FaceEnergyOfLift s.L s.m s.K ∧
    PeriodLattice_le s.L s.m s.K ∧ ProjectInvariantUnderPeriods s.L s.m s.K ∧
    SameProjectionDifferByPeriod s.L s.m s.K ∧
    EventuallyInjective s.L s.K ∧
    ∀ W : LinkWindow (PeriodicLattice.meshSize s.L ((s.K : ℕ) : ℤ)),
      WindowProjectsFaithfully s.L s.m s.K W ∧
      LeastTorusSideIsAttained W ∧
      AxialTranslatesExit s.L s.m s.K W
end YangMills.Construction.InfiniteLattice.Covering
end
