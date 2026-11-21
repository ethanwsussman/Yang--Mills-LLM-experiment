import YangMills.Construction.Continuum.SchwartzTestsAndMollifiers
import Reconstruction.MinkowskiSpace.WightmanTheoriesOfOneHermitianScalarField
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.TubeBoundary
def futureConeTuples (b : ℕ) : Set (TestSpaces.PointTuple b) :=
  Set.univ.pi fun _ => MinkowskiSpace.futureCone
def closedFutureConeTuples (b : ℕ) : Set (TestSpaces.PointTuple b) :=
  Set.univ.pi fun _ => MinkowskiSpace.closedFutureCone
variable {b : ℕ}
def tubePoint (x y : TestSpaces.PointTuple b) : Fin b → MinkowskiSpace.ComplexVec4 :=
  fun k => MinkowskiSpace.toComplex (x k) + Complex.I • MinkowskiSpace.toComplex (y k)
def shiftedIntegrand (u : (Fin b → MinkowskiSpace.ComplexVec4) → ℂ) (y : TestSpaces.PointTuple b)
    (f : TestSpaces.PointTuple b → ℂ) : TestSpaces.PointTuple b → ℂ :=
  fun x => u (tubePoint x y) * f x
def pairing (u : (Fin b → MinkowskiSpace.ComplexVec4) → ℂ) (y : TestSpaces.PointTuple b)
    (f : TestSpaces.PointTuple b → ℂ) : ℂ :=
  ∫ x, shiftedIntegrand u y f x
def translateBy (a : TestSpaces.PointTuple b) (f : TestSpaces.PointTuple b → ℂ) :
    TestSpaces.PointTuple b → ℂ :=
  fun x => f (x - a)
def totalTimeDeriv (f : TestSpaces.PointTuple b → ℂ) : TestSpaces.PointTuple b → ℂ :=
  fun x => ∑ k, TestSpaces.coordDeriv k 0 f x
def maxTimeDerivNorm (n : ℕ) (f : TestSpaces.PointTuple b → ℂ) : ℝ :=
  (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
    fun j => WightmanReconstruction.lOneNorm (totalTimeDeriv^[j] f)
def IsBoundaryExtension (u : (Fin b → MinkowskiSpace.ComplexVec4) → ℂ)
    (J : TestSpaces.PointTuple b → (TestSpaces.PointTuple b → ℂ) → ℂ) : Prop :=
  (∀ y ∈ futureConeTuples b, ∀ f ∈ TestSpaces.schwartzSet b,
    J y f = pairing u y f) ∧
  (∀ f ∈ TestSpaces.schwartzSet b,
    ContinuousOn (fun p : TestSpaces.PointTuple b × TestSpaces.PointTuple b => J p.1 (translateBy p.2 f))
      (closedFutureConeTuples b ×ˢ Set.univ)) ∧
  ∀ y ∈ closedFutureConeTuples b, ∀ f ∈ TestSpaces.schwartzSet b,
    ∀ g ∈ TestSpaces.schwartzSet b, ∀ w w' : ℂ,
      J y (w • f + w' • g) = w * J y f + w' * J y g
def boundaryValue (u : (Fin b → MinkowskiSpace.ComplexVec4) → ℂ) :
    TestSpaces.PointTuple b → (TestSpaces.PointTuple b → ℂ) → ℂ :=
  Classical.epsilon (IsBoundaryExtension u)
def BoundaryValueBound : Prop :=
  ∀ (b q : ℕ) (c : ℝ) (u : (Fin b → MinkowskiSpace.ComplexVec4) → ℂ), 0 < b →
    WightmanTheory.IsHolomorphicOnTube u →
    (∀ ζ ∈ WightmanTheory.tubeTuples b,
      ‖u ζ‖ ≤ c * ∏ k, (min 1 (MinkowskiSpace.tubeGap (ζ k)))⁻¹ ^ q) →
    (∀ y ∈ futureConeTuples b, ∀ f ∈ TestSpaces.schwartzSet b,
      Integrable (shiftedIntegrand u y f)) ∧
    (∀ f ∈ TestSpaces.schwartzSet b, ∀ j : ℕ, Integrable (totalTimeDeriv^[j] f)) ∧
    (∀ f ∈ TestSpaces.schwartzSet b, ∀ a : TestSpaces.PointTuple b,
      translateBy a f ∈ TestSpaces.schwartzSet b) ∧
    IsBoundaryExtension u (boundaryValue u) ∧
    ∀ y ∈ closedFutureConeTuples b, ∀ f ∈ TestSpaces.schwartzSet b,
      ‖boundaryValue u y f‖ ≤ 4 * c * maxTimeDerivNorm (b * q + 1) f
end YangMills.Construction.TubeBoundary
