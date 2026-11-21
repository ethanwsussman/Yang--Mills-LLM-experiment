import YangMills.Construction.Continuum.SchwingerFunctions
import YangMills.Construction.InfiniteLattice.ConnectedCorrelations
import YangMills.Construction.InfiniteLattice.ObservablesAndIsometriesAtOneSpacing
import YangMills.Construction.InfiniteLattice.PeriodicExtensionsStatesAndTorusFunctionalsAtOneSpacing
import YangMills.Construction.InfiniteLattice.SpecificationDensitiesAndTheDensityDistanceAtOneSpacing
import YangMills.Construction.InfiniteLattice.TuplesCombinationsNormalsAndMirrorsOfFourSpace
import YangMills.Construction.Lattice.ActionOfLatticeIsometries
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open InfiniteLattice
namespace FixedSpacing
namespace CurvatureObservable
variable (D : Setup)
abbrev curvatureObs (f : AmbientSpace → ℝ) : D.Fields → ℝ := smearedEnergy f
def curvatureObsComplex (f : AmbientSpace → ℝ) (U : D.Fields) : ℂ := (curvatureObs D f U : ℝ)
def curvatureBound : ℝ := 192
def closedHalfSpace (n : EuclideanMirrors.ReflNormal) : Set AmbientSpace :=
  {x | 0 ≤ LatticeConventions.euclidDot n.1 x}
def CovariantUnderSymmetry (f : AmbientSpace → ℝ) (r : LatticeSymmetry D.mesh) : Prop :=
  Function.Bijective r.plaquetteMap ∧
    (∀ p : ElementaryPlaquette D.mesh,
      r.actOn (fun U : D.Fields => faceEnergy U p) =
        fun U : D.Fields => faceEnergy U (r.plaquetteMap p)) ∧
    (∀ p : ElementaryPlaquette D.mesh, (r.plaquetteMap p).center = r.toFun p.center) ∧
    r.pushforwardFun f ∈ compactTestFunctions ∧
    r.actOn (curvatureObs D f) = curvatureObs D (r.pushforwardFun f)
def CovariantUnderShiftsRotationsReflections (f : AmbientSpace → ℝ) : Prop :=
  (∀ v : LatticePoint D.mesh, (shift v).actOn (curvatureObs D f) =
    curvatureObs D fun x => f (x - (v : AmbientSpace))) ∧
    (∀ w ∈ hyperoctahedralLinearGroup, ∃ r : LatticeSymmetry D.mesh, r.toFun = ⇑w ∧
      r.actOn (curvatureObs D f) = curvatureObs D (f ∘ ⇑w.symm)) ∧
    ∀ (n : EuclideanMirrors.ReflNormal) (c : ℝ),
      (EuclideanMirrors.AffineMirror.mk n c).IsLatticeAligned D.mesh →
      ∃ r : LatticeSymmetry D.mesh, r.toFun = EuclideanMirrors.hyperplaneReflection n c ∧
        r.actOn (curvatureObs D f) =
          curvatureObs D (f ∘ EuclideanMirrors.hyperplaneReflection n c)
def MeasurableOnClosedHalfSpace (f : AmbientSpace → ℝ) (n : EuclideanMirrors.ReflNormal) : Prop :=
  (∀ x, ¬ 0 < LatticeConventions.euclidDot n.1 x → f x = 0) →
    curvatureObsComplex D f ∈ observableAlgebra D.mesh (closedHalfSpace n) ∧
      DependsOnlyOnLinks (positiveLinksWithin D.mesh (closedHalfSpace n)) (curvatureObs D f)
def LocalAndBounded (f : AmbientSpace → ℝ) (R : ℝ) : Prop :=
  0 ≤ R → tsupport f ⊆ closedCube R →
    FactorsThroughFinite ((D.cubeWindow (R + D.mesh / 2)).links : Set (Link D.mesh))
        (curvatureObsComplex D f) ∧
      (D.cubeWindow (R + D.mesh / 2)).links ⊆ (D.cubeWindow (R + 1)).links ∧
      ∀ U : D.Fields,
        |curvatureObs D f U| ≤
          curvatureBound * TestFunctions.uniformNorm f * (R / D.mesh + 1) ^ 4
def LiftCompatible (f : AmbientSpace → ℝ) : Prop :=
  ∀ U : D.TorusFields,
    curvatureObs D f (D.lift U) = D.smeared (D.periodization f) U
def TorusConnectedEqCumulant {n : ℕ} (f : Fin n → AmbientSpace → ℝ) : Prop :=
  D.torusConnected f =
      Cumulants.mixedCumulant D.liftedGibbs (fun i => curvatureObs D (f i)) ∧
    Cumulants.mixedCumulant D.liftedGibbs (fun i => curvatureObs D (f i)) =
      ursellFunction D.liftedGibbs n f
def TorusConnectedEqSchwinger {n : ℕ} (f : Fin n → AmbientSpace → ℝ) : Prop :=
  0 < D.level → (∃ d : ℝ, TestFunctions.HasSeparatedSupportsR4 f d) →
    (∃ A : Set AmbientSpace, TestFunctions.HasDiameterLE A (D.side / 2) ∧
      ∀ i, tsupport (f i) ⊆ A) →
    D.torusConnected f = SchwingerFunctions.connectedSchwingerR4 D.L D.m D.level D.β f
def CurvatureConditions : Prop :=
  ∀ D : Setup,
    (∀ f ∈ compactTestFunctions,
      (∀ r : LatticeSymmetry D.mesh, CovariantUnderSymmetry D f r) ∧
      CovariantUnderShiftsRotationsReflections D f ∧
      (∀ n : EuclideanMirrors.ReflNormal, MeasurableOnClosedHalfSpace D f n) ∧
      (∀ R : ℝ, LocalAndBounded D f R) ∧
      LiftCompatible D f) ∧
    ∀ (n : ℕ) (f : Fin n → AmbientSpace → ℝ), 2 ≤ n → (∀ i, f i ∈ compactTestFunctions) →
      TorusConnectedEqCumulant D f ∧ TorusConnectedEqSchwinger D f
end CurvatureObservable
end FixedSpacing
end YangMills.Construction
end
