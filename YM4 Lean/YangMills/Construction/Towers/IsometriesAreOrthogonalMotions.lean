import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.TowersOfLattices
import Mathlib
set_option autoImplicit false
open Matrix
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace OrthogonalMotions
open InfiniteLattice (AmbientSpace)
open TorusMetric (euclidNormVec torusProj)
def openBall (r : ℝ≥0∞) : Set AmbientSpace := {h | ENNReal.ofReal (euclidNormVec h) < r}
def liftNorms (s : ℝ) (a b : AmbientSpace) : Set ℝ :=
  Set.range fun n : Fin 4 → ℤ => euclidNormVec (a - b + s • fun μ => (n μ : ℝ))
def minLiftNorm (s : ℝ) (a b : AmbientSpace) : ℝ := sInf (liftNorms s a b)
def IsIntegerMatrix (R : Matrix (Fin 4) (Fin 4) ℝ) : Prop := ∀ μ ν, ∃ m : ℤ, R μ ν = m
def BallIsometryFixingOriginIsLinear : Prop :=
  ∀ r : ℝ≥0∞, 0 < r → ∀ g : AmbientSpace → AmbientSpace, g 0 = 0 →
    (∀ h ∈ openBall r, ∀ h' ∈ openBall r, euclidNormVec (g h - g h') = euclidNormVec (h - h')) →
    ∃ R ∈ Matrix.orthogonalGroup (Fin 4) ℝ, ∀ h ∈ openBall r, g h = R *ᵥ h
def IsometryOfSpaceIsAffine : Prop :=
  ∀ f : AmbientSpace → AmbientSpace, FullSpace.IsDistancePreserving f →
    ∃ R ∈ Matrix.orthogonalGroup (Fin 4) ℝ, ∃ v : AmbientSpace, ∀ x, f x = R *ᵥ x + v
def IntegerAffineIsIsometry : Prop :=
  ∀ R ∈ Matrix.orthogonalGroup (Fin 4) ℝ, IsIntegerMatrix R → ∀ v : AmbientSpace,
    FullSpace.IsDistancePreserving fun x => R *ᵥ x + v
def MinLiftNormAttained (L n : ℕ) : Prop :=
  ∀ a b : AmbientSpace, IsLeast (liftNorms (PeriodicLattice.torusSide L n) a b)
    (minLiftNorm (PeriodicLattice.torusSide L n) a b)
def MinLiftNormWellDefined (L n : ℕ) : Prop :=
  ∀ a b a' b' : AmbientSpace,
    torusProj (PeriodicLattice.torusSide L n) a' = torusProj (PeriodicLattice.torusSide L n) a →
    torusProj (PeriodicLattice.torusSide L n) b' = torusProj (PeriodicLattice.torusSide L n) b →
    minLiftNorm (PeriodicLattice.torusSide L n) a' b' =
      minLiftNorm (PeriodicLattice.torusSide L n) a b
def TorusIsometryLifts (L n : ℕ) : Prop :=
  ∀ f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n, IsDistancePreserving f →
    ∃ R ∈ Matrix.orthogonalGroup (Fin 4) ℝ,
      (fun x : AmbientSpace => R *ᵥ x) ''
          (InfiniteLattice.latticeSubgroup (PeriodicLattice.torusSide L n) : Set AmbientSpace) =
        InfiniteLattice.latticeSubgroup (PeriodicLattice.torusSide L n) ∧
      ∃ v : AmbientSpace, ∀ x : AmbientSpace,
        f (torusProj (PeriodicLattice.torusSide L n) x) =
          torusProj (PeriodicLattice.torusSide L n) (R *ᵥ x + v)
def IntegerAffineDescends (L n : ℕ) : Prop :=
  ∀ R ∈ Matrix.orthogonalGroup (Fin 4) ℝ, IsIntegerMatrix R → ∀ v : AmbientSpace,
    ∃ f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n,
      (∀ x : AmbientSpace,
        f (torusProj (PeriodicLattice.torusSide L n) x) =
          torusProj (PeriodicLattice.torusSide L n) (R *ᵥ x + v)) ∧
      IsDistancePreserving f
def Classification : Prop :=
  BallIsometryFixingOriginIsLinear ∧ IsometryOfSpaceIsAffine ∧ IntegerAffineIsIsometry ∧
    ∀ L n : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n →
      MinLiftNormAttained L n ∧ MinLiftNormWellDefined L n ∧ TorusIsometryLifts L n ∧
        IntegerAffineDescends L n
end OrthogonalMotions
end Tower
end YangMills.Construction
end
