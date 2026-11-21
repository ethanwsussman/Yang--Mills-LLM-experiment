import YangMills.Construction.Lattice.PlaquetteFunctionsAndTwoNotionsOfSupport
import YangMills.Construction.Torus.DistanceBallsIntegralAndVolumeInPhysicalUnits
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric TestFunctions PlaquetteSupports
namespace TorusMeasure
namespace BallProjection
variable (P : Conventions.StandingParameters)
def torusBallOver (x : Fin 4 → ℝ) (r : ℝ) : Set P.Torus :=
  closedBallTorus (ℓ := PeriodicLattice.torusSide P.L P.m) (proj P x) r
def IsPushdown (x : Fin 4 → ℝ) (r : ℝ) (f : (Fin 4 → ℝ) → ℝ) (F : P.Torus → ℝ) : Prop :=
  (∀ y, y ∉ closedBallR4 x r → f y = 0) ∧
    (∀ y ∈ closedBallR4 x r, F (proj P y) = f y) ∧
    ∀ z, z ∉ torusBallOver P x r → F z = 0
def ShortVectorNormPreserved : Prop :=
  ∀ y : Fin 4 → ℝ, euclidNormVec y ≤ PeriodicLattice.torusSide P.L P.m / 2 →
    pointNorm (proj P y) = euclidNormVec y
def BallMapsIsometricallyOnto (x : Fin 4 → ℝ) (r : ℝ) : Prop :=
  BijOn (proj P) (closedBallR4 x r) (torusBallOver P x r) ∧
    ∀ y ∈ closedBallR4 x r, ∀ y' ∈ closedBallR4 x r,
      pointDist (proj P y) (proj P y') = euclidDistR4 y y'
def PushdownBijective (x : Fin 4 → ℝ) (r : ℝ) : Prop :=
  (∀ f : (Fin 4 → ℝ) → ℝ, (∀ y, y ∉ closedBallR4 x r → f y = 0) →
    ∃! F : P.Torus → ℝ, IsPushdown P x r f F) ∧
  ∀ F : P.Torus → ℝ, (∀ z, z ∉ torusBallOver P x r → F z = 0) →
    (∃! f : (Fin 4 → ℝ) → ℝ, IsPushdown P x r f F) ∧
      IsPushdown P x r ((closedBallR4 x r).indicator (F ∘ proj P)) F
def IsPeriodizationOf (x : Fin 4 → ℝ) (r : ℝ) (f : (Fin 4 → ℝ) → ℝ) (F : P.Torus → ℝ) : Prop :=
  (∀ y, F (proj P y) = ∑' k : Fin 4 → ℤ, f (y + latticeTranslate (PeriodicLattice.torusSide P.L P.m) k)) ∧
    (∀ (y : Fin 4 → ℝ) (k k' : Fin 4 → ℤ),
      f (y + latticeTranslate (PeriodicLattice.torusSide P.L P.m) k) ≠ 0 →
      f (y + latticeTranslate (PeriodicLattice.torusSide P.L P.m) k') ≠ 0 → k = k') ∧
    IsPeriodizable (PeriodicLattice.torusSide P.L P.m) (closedBallR4 x r) f ∧
    F = periodize (PeriodicLattice.torusSide P.L P.m) f
def SameValues (x : Fin 4 → ℝ) (r : ℝ) (f : (Fin 4 → ℝ) → ℝ) (F : P.Torus → ℝ) : Prop :=
  F '' torusBallOver P x r = f '' closedBallR4 x r ∧
    torusESup (fun z => |F z|) = ⨆ y, ((|f y| : ℝ) : EReal) ∧
    (TorusFunNonneg F ↔ ∀ y, 0 ≤ f y)
def SameLipschitzConstant (f : (Fin 4 → ℝ) → ℝ) (F : P.Torus → ℝ) : Prop :=
  (IsLipschitzFor (euclidDistTorus (ℓ := PeriodicLattice.torusSide P.L P.m)) F ↔
      IsLipschitzFor euclidDistR4 f) ∧
    (IsLipschitzFor euclidDistR4 f →
      lipConstTorus (ℓ := PeriodicLattice.torusSide P.L P.m) F = lipConstR4 f)
def SupportsCorrespond (x : Fin 4 → ℝ) (r : ℝ) (f : (Fin 4 → ℝ) → ℝ) (F : P.Torus → ℝ) : Prop :=
  euclideanTSupport f ⊆ closedBallR4 x r ∧ torusTSupport F ⊆ torusBallOver P x r ∧
    torusTSupport F = proj P '' euclideanTSupport f
def SameIntegral (f : (Fin 4 → ℝ) → ℝ) (F : P.Torus → ℝ) : Prop :=
  IsBoundedFun f → IsNullMeasurableFunR4 f →
    IsBoundedFun F ∧ IsMeasurableFun F ∧ torusIntegral F = integralR4 f
def BallProjectionStatement : Prop :=
  ∀ (P : Conventions.StandingParameters) (r : ℝ) (x : Fin 4 → ℝ), 0 < r →
    r ≤ PeriodicLattice.torusSide P.L P.m / 4 →
    ShortVectorNormPreserved P ∧ BallMapsIsometricallyOnto P x r ∧
      PushdownBijective P x r ∧
      ∀ (f : (Fin 4 → ℝ) → ℝ) (F : P.Torus → ℝ), IsPushdown P x r f F →
        IsPeriodizationOf P x r f F ∧ SameValues P x r f F ∧ SameLipschitzConstant P f F ∧
          SupportsCorrespond P x r f F ∧ SameIntegral P f F
end BallProjection
end TorusMeasure
end YangMills.Construction
