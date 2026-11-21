import YangMills.Construction.InfiniteLattice.ConfigurationsFunctionsAndMeasures
import YangMills.Construction.InfiniteLattice.HypercubicMotionsOfTheLattice
import YangMills.Construction.InfiniteLattice.SidesOfAPlaquetteAndTheDensityOfBoundedSupport
import YangMills.Construction.InfiniteLattice.TransportOfAFunctionThroughABall
import YangMills.Construction.InfiniteLattice.UnitSpacingLatticeData
import YangMills.Construction.Lattice.ActionOfLatticeIsometries
import YangMills.Construction.Lattice.BondsOfTheTorusLatticeAndThePeriodicExtension
import YangMills.Construction.Lattice.ParallelBondsAndSidesOfAPlaquette
import YangMills.Construction.Torus.LiftsAndInducedMaps
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Function
noncomputable section
namespace YangMills.Construction
namespace LatticeCovering
variable (D : FixedSpacing.Params)
abbrev spacingIndex : ℤ := ((D.K : ℕ) : ℤ)
abbrev mesh : ℝ := PeriodicLattice.meshSize D.L (spacingIndex D)
abbrev period : ℝ := PeriodicLattice.torusSide D.L D.m
abbrev proj : InfiniteLattice.AmbientSpace → PeriodicLattice.FourTorus D.L D.m :=
  TorusMetric.torusProj (period D)
abbrev descend (r : InfiniteLattice.AmbientSpace → InfiniteLattice.AmbientSpace) :
    PeriodicLattice.FourTorus D.L D.m → PeriodicLattice.FourTorus D.L D.m :=
  TorusLifts.descendedMap (period D) (period D) r
def FibersOfProjection : Prop :=
  (∀ x y : InfiniteLattice.AmbientSpace, proj D x = proj D y ↔
      ∃ k : Fin 4 → ℤ, x - y = TestFunctions.latticeTranslate (period D) k) ∧
    (∀ S : Set InfiniteLattice.AmbientSpace,
      (∀ x ∈ S, ∀ y ∈ S, GibbsAtFixedSpacing.linfNorm (x - y) < period D) →
      InjOn (proj D) S) ∧
    proj D ⁻¹' (PeriodicLattice.sublattice D.L D.m (spacingIndex D) :
        Set (PeriodicLattice.FourTorus D.L D.m)) =
      (InfiniteLattice.latticeSubgroup (mesh D) : Set InfiniteLattice.AmbientSpace)
def LinksAndPlaquettesUnderProjection : Prop :=
  BijOn (fun q : PeriodicLattice.Site D.L D.m (spacingIndex D) × Fin 4 =>
        PeriodicLattice.Bond.forwardFrom q.1 q.2)
      univ (PeriodicLattice.forwardBonds D.L D.m (spacingIndex D)) ∧
    (∀ (x : InfiniteLattice.LatticePoint (mesh D)) (κ : Fin 4),
      InfiniteLattice.projectLink D.L D.m (spacingIndex D) (InfiniteLattice.Link.forwardFrom x κ) =
        PeriodicLattice.Bond.forwardFrom (InfiniteLattice.projectPoint D.L D.m (spacingIndex D) x) κ) ∧
    (∀ p : InfiniteLattice.ElementaryPlaquette (mesh D),
      (TorusLifts.projectPlaquette D.L D.m (spacingIndex D) p).origin =
          InfiniteLattice.projectPoint D.L D.m (spacingIndex D) p.corner ∧
        (TorusLifts.projectPlaquette D.L D.m (spacingIndex D) p).firstAxis = p.lowAxis ∧
        (TorusLifts.projectPlaquette D.L D.m (spacingIndex D) p).secondAxis = p.highAxis) ∧
    InfiniteLattice.projectLink D.L D.m (spacingIndex D) ''
        InfiniteLattice.positiveLinkSet (mesh D) =
      PeriodicLattice.forwardBonds D.L D.m (spacingIndex D) ∧
    Surjective (TorusLifts.projectPlaquette D.L D.m (spacingIndex D)) ∧
    (∀ p : InfiniteLattice.ElementaryPlaquette (mesh D),
      PeriodicLattice.Plaquette.edges (TorusLifts.projectPlaquette D.L D.m (spacingIndex D) p) =
        InfiniteLattice.projectLink D.L D.m (spacingIndex D) '' {b | b ∈ p.sideLinks}) ∧
    ∀ p : InfiniteLattice.ElementaryPlaquette (mesh D),
      (TorusLifts.projectPlaquette D.L D.m (spacingIndex D) p).barycenter = proj D p.center
def LiftAndLiftedMeasure : Prop :=
  Continuous (InfiniteLattice.liftCompactField :
      PeriodicLattice.CompactGaugeField D.L D.m (spacingIndex D) → _) ∧
    (∀ (U : PeriodicLattice.CompactGaugeField D.L D.m (spacingIndex D))
      (b : InfiniteLattice.Link (mesh D)), b ∈ InfiniteLattice.positiveLinkSet (mesh D) →
        InfiniteLattice.liftCompactField U b =
          U.linkValue (InfiniteLattice.projectLink D.L D.m (spacingIndex D) b)) ∧
    (∀ (U : PeriodicLattice.CompactGaugeField D.L D.m (spacingIndex D))
      (p : InfiniteLattice.ElementaryPlaquette (mesh D)),
        InfiniteLattice.faceEnergy (InfiniteLattice.liftCompactField U) p =
          PeriodicLattice.plaquetteCost U.1
            (TorusLifts.projectPlaquette D.L D.m (spacingIndex D) p)) ∧
    (∀ F : InfiniteLattice.GaugeField (mesh D) → ℂ, InfiniteLattice.IsBoundedObservable F →
      ∫ V, F V ∂InfiniteLattice.liftedWilsonMeasure D.L D.m (D.K : ℕ) D.β =
        PeriodicLattice.gibbsExpectation D.L D.m (D.K : ℕ) D.β
          (F ∘ InfiniteLattice.liftField D.L D.m (spacingIndex D))) ∧
    (∀ E : Set (InfiniteLattice.GaugeField (mesh D)), MeasurableSet E →
      MeasurableSet ((InfiniteLattice.liftCompactField :
        PeriodicLattice.CompactGaugeField D.L D.m (spacingIndex D) → _) ⁻¹' E)) ∧
    IsProbabilityMeasure (InfiniteLattice.liftedWilsonMeasure D.L D.m (D.K : ℕ) D.β)
def DescentOfMotion (r : InfiniteLattice.latticeMotions (mesh D)) : Prop :=
  TorusLifts.Descends (period D) (period D) r.1 (descend D r.1) ∧
    (∀ σ : PeriodicLattice.FourTorus D.L D.m → PeriodicLattice.FourTorus D.L D.m,
      TorusLifts.Descends (period D) (period D) r.1 σ → σ = descend D r.1) ∧
    PeriodicLattice.IsTorusIsometry (descend D r.1) ∧
    descend D r.1 '' (PeriodicLattice.sublattice D.L D.m (spacingIndex D) :
        Set (PeriodicLattice.FourTorus D.L D.m)) =
      PeriodicLattice.sublattice D.L D.m (spacingIndex D) ∧
    (∀ t ∈ InfiniteLattice.latticeMotions (mesh D),
      descend D (InfiniteLattice.latticeMotionMul r.1 t) =
        descend D r.1 ∘ descend D t) ∧
    (∃ t ∈ InfiniteLattice.latticeMotions (mesh D), LeftInverse t r.1 ∧ RightInverse t r.1 ∧
      LeftInverse (descend D t) (descend D r.1) ∧
      RightInverse (descend D t) (descend D r.1)) ∧
    (∀ w ∈ InfiniteLattice.hypercubicGroup, ∀ v ∈ InfiniteLattice.latticeSubgroup (mesh D),
      (∀ x, r.1 x = w x + v) → ∀ (z : PeriodicLattice.FourTorus D.L D.m) (κ : Fin 4),
        descend D r.1 (PeriodicLattice.translateByVector z
            (mesh D • InfiniteLattice.basisVector κ)) =
          PeriodicLattice.translateByVector (descend D r.1 z)
            (mesh D • w (InfiniteLattice.basisVector κ))) ∧
    ∀ s : PeriodicLattice.TorusLatticeSymmetry D.L D.m (D.K : ℕ),
      s.toFun = descend D r.1 →
        ∀ U : PeriodicLattice.CompactGaugeField D.L D.m (spacingIndex D),
          InfiniteLattice.latticeMotionField r (InfiniteLattice.liftCompactField U) =
            InfiniteLattice.liftCompactField (s.pullback U)
def DescentOfBasicMotions : Prop :=
  (∀ v : InfiniteLattice.LatticePoint (mesh D),
    descend D (fun x => x + (v : InfiniteLattice.AmbientSpace)) = fun z => z + proj D v) ∧
    (∀ w ∈ InfiniteLattice.hypercubicGroup, ∀ (π : Equiv.Perm (Fin 4)) (ε : Fin 4 → ℤˣ),
      (∀ (x : InfiniteLattice.AmbientSpace) (μ : Fin 4),
        w x μ = (((ε μ : ℤˣ) : ℤ) : ℝ) * x (π μ)) →
        descend D w = PeriodicLattice.signedCoordinatePerm D.L D.m π ε) ∧
    ∀ P : InfiniteLattice.PeriodicMirror D.L D.m (spacingIndex D),
      descend D (InfiniteLattice.coordinateReflection P.axis P.level) = P.reflectEquiv
def IsPeriodizationOn (ρ : ℝ) (f : InfiniteLattice.AmbientSpace → ℂ)
    (g : PeriodicLattice.FourTorus D.L D.m → ℂ) : Prop :=
  (∀ x ∈ TestFunctions.closedBallR4 0 ρ, g (proj D x) = f x) ∧
    ∀ u, u ∉ proj D '' TestFunctions.closedBallR4 0 ρ → g u = 0
def PeriodizationProperties (ρ : ℝ) (f : InfiniteLattice.AmbientSpace → ℂ) : Prop :=
  (∀ x : InfiniteLattice.AmbientSpace,
      {k : Fin 4 → ℤ | f (x + TestFunctions.latticeTranslate (period D) k) ≠ 0}.Subsingleton) ∧
    IsPeriodizationOn D ρ f (InfiniteLattice.torusPeriodize D.toStandingParameters f) ∧
    (∀ g, IsPeriodizationOn D ρ f g →
      g = InfiniteLattice.torusPeriodize D.toStandingParameters f) ∧
    (∀ ρ', InfiniteLattice.IsPeriodizableInBall D.toStandingParameters ρ' f →
      IsPeriodizationOn D ρ' f (InfiniteLattice.torusPeriodize D.toStandingParameters f)) ∧
    ((∀ x, (f x).im = 0) →
      ∀ u, (InfiniteLattice.torusPeriodize D.toStandingParameters f u).im = 0) ∧
    (TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 f →
      TestFunctions.IsLipschitzFor TestFunctions.euclidDistTorus
          (InfiniteLattice.torusPeriodize D.toStandingParameters f) ∧
        TestFunctions.lipConstTorus (InfiniteLattice.torusPeriodize D.toStandingParameters f) ≤
          TestFunctions.lipConstR4 f) ∧
    ∀ U : PeriodicLattice.CompactGaugeField D.L D.m (spacingIndex D),
      InfiniteLattice.boundedSupportObservable f (InfiniteLattice.liftCompactField U) =
        PeriodicLattice.smearedObservable
          (InfiniteLattice.torusPeriodize D.toStandingParameters f) U.1
def CoveringStatement : Prop :=
  ∀ D : FixedSpacing.Params,
    FibersOfProjection D ∧
      LinksAndPlaquettesUnderProjection D ∧
      LiftAndLiftedMeasure D ∧
      (∀ r, DescentOfMotion D r) ∧
      DescentOfBasicMotions D ∧
      (∀ ρ : ℝ, ρ ≤ InfiniteLattice.periodizationRadius D.toStandingParameters ↔
        4 * ρ + 4 ≤ D.toStandingParameters.side) ∧
      ∀ (ρ : ℝ) (f : InfiniteLattice.AmbientSpace → ℂ),
        InfiniteLattice.IsPeriodizableInBall D.toStandingParameters ρ f →
          PeriodizationProperties D ρ f
end LatticeCovering
end YangMills.Construction
end
