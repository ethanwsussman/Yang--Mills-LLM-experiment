import YangMills.Construction.InfiniteLattice.ActionOfTheLatticeIsometriesOnObservables
import YangMills.Construction.InfiniteLattice.ReflectionInALatticeMirrorGivenWithANormal
import YangMills.Construction.Lattice.EuclideanIsometries
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
def LatticeSymmetry.refl (a : ℝ) : LatticeSymmetry a where
  toFun := id
  preservesDist _ _ := rfl
  image_eq := Set.image_id _
end InfiniteLattice
namespace LatticeConventions
namespace ObservableRules
open InfiniteLattice (GaugeField IsSymmetricUnder IsSpaceIsometry IsBoundedObservable
  IsStarAlgebraOfFunctions LatticeSymmetry LatticePoint localRegionObservables
  observableSupNorm boundedRegionObservables AmbientSpace shift)
open NormalHyperplane (reflectSymmetry)
def IsOrthogonalMap (R : Point →ₗ[ℝ] Point) : Prop :=
  ∀ x y : Point, euclidDot (R x) (R y) = euclidDot x y
def RegionObservablesMonotoneStarAlgebras (a : ℝ) : Prop :=
  ∀ A B : Set Point, A ⊆ B →
    boundedRegionObservables a A ⊆ boundedRegionObservables a B ∧
    localRegionObservables a A ⊆ localRegionObservables a B ∧
    IsStarAlgebraOfFunctions (boundedRegionObservables a A) ∧
    IsStarAlgebraOfFunctions (localRegionObservables a A)
def ActionLinearUnitalIsometric (a : ℝ) : Prop :=
  ∀ g : LatticeSymmetry a,
    (∀ f f' : GaugeField a → ℂ, IsBoundedObservable f → IsBoundedObservable f' →
      g.actOn (f + f') = g.actOn f + g.actOn f') ∧
    (∀ (c : ℂ) (f : GaugeField a → ℂ), IsBoundedObservable f →
      g.actOn (c • f) = c • g.actOn f) ∧
    g.actOn (constOne : GaugeField a → ℂ) = constOne ∧
    ∀ f : GaugeField a → ℂ, IsBoundedObservable f →
      observableSupNorm (g.actOn f) = observableSupNorm f
def IdentityActsTrivially (a : ℝ) : Prop :=
  ∀ f : GaugeField a → ℂ, IsBoundedObservable f → (LatticeSymmetry.refl a).actOn f = f
def InverseActsInversely (a : ℝ) : Prop :=
  ∀ g : LatticeSymmetry a,
    (∃ h : LatticeSymmetry a, h.IsInverse g) ∧
    ∀ h : LatticeSymmetry a, h.IsInverse g → ∀ f : GaugeField a → ℂ, IsBoundedObservable f →
      g.actOn (h.actOn f) = f ∧ f = h.actOn (g.actOn f)
def ActionMapsLocalObservables (a : ℝ) : Prop :=
  ∀ (g : LatticeSymmetry a) (A : Set Point),
    (fun f : GaugeField a → ℂ => g.actOn f) '' localRegionObservables a A =
      localRegionObservables a (g.setImage A)
def ShiftsComposeOnObservables (a : ℝ) : Prop :=
  ∀ (x y : LatticePoint a) (f : GaugeField a → ℂ), IsBoundedObservable f →
    (shift x).actOn ((shift y).actOn f) = (shift (x + y)).actOn f
def SymmetryClosedUnderCompAndInverse (a : ℝ) : Prop :=
  ∀ μ : Measure (GaugeField a), IsProbabilityMeasure μ →
    ∀ g g' : LatticeSymmetry a, IsSymmetricUnder μ g → IsSymmetricUnder μ g' →
      IsSymmetricUnder μ (g.comp g') ∧
      ∀ h : LatticeSymmetry a, h.IsInverse g → IsSymmetricUnder μ h
def ReflectionIsIsometricInvolution (a : ℝ) : Prop :=
  ∀ P : NormalHyperplane,
    IsOrthogonalMap P.reflectionLinear ∧
    (∀ x w : Point, P.reflect (x + w) = P.reflect x + P.reflectionLinear w) ∧
    IsSpaceIsometry P.reflect ∧
    P.reflect ∘ P.reflect = id ∧
    (P.IsLatticeMirror a → ∃ g : LatticeSymmetry a, g.toFun = P.reflect)
def MapsHyperplane {a : ℝ} (g : LatticeSymmetry a) (R : Point →ₗ[ℝ] Point) (v : LatticePoint a)
    (ε : ℝ) (P P' : NormalHyperplane) : Prop :=
  (∀ x : Point, g.toFun x = R x + (v : AmbientSpace)) ∧
  IsOrthogonalMap R ∧
  (ε = 1 ∨ ε = -1) ∧
  P'.normal = ε • R P.normal ∧
  P'.level = ε * (P.level + euclidDot (R P.normal) (v : AmbientSpace))
def SymmetryMapsMirrorsAndHalfSpaces (a : ℝ) : Prop :=
  ∀ (g : LatticeSymmetry a) (R : Point →ₗ[ℝ] Point) (v : LatticePoint a) (ε : ℝ)
    (P P' : NormalHyperplane),
    P.IsLatticeMirror a → P'.IsLatticeMirror a → MapsHyperplane g R v ε P P' →
      g.setImage P.carrier = P'.carrier ∧
      (ε = 1 → g.setImage P.upperHalfSpace = P'.upperHalfSpace ∧
        g.setImage P.lowerHalfSpace = P'.lowerHalfSpace) ∧
      (ε = -1 → g.setImage P.upperHalfSpace = P'.lowerHalfSpace ∧
        g.setImage P.lowerHalfSpace = P'.upperHalfSpace) ∧
      ∀ h : LatticeSymmetry a, h.IsInverse g →
        P'.reflect = g.toFun ∘ P.reflect ∘ h.toFun
def SymmetricStateTransportsPositivity (a : ℝ) : Prop :=
  ∀ (g : LatticeSymmetry a) (R : Point →ₗ[ℝ] Point) (v : LatticePoint a) (ε : ℝ)
    (P P' : NormalHyperplane) (hP : P.IsLatticeMirror a) (hP' : P'.IsLatticeMirror a),
    MapsHyperplane g R v ε P P' →
    ∀ μ : Measure (GaugeField a), IsProbabilityMeasure μ → IsSymmetricUnder μ g →
      ∀ h : LatticeSymmetry a, h.IsInverse g →
        (∀ f : GaugeField a → ℂ,
          f ∈ localRegionObservables a P'.upperHalfSpace ∨
            f ∈ localRegionObservables a P'.lowerHalfSpace →
          (h.actOn f ∈ localRegionObservables a P.upperHalfSpace ∨
            h.actOn f ∈ localRegionObservables a P.lowerHalfSpace) ∧
          ∫ U, (conjFun ((reflectSymmetry hP').actOn f) * f) U ∂μ =
            ∫ U, g.actOn
              (conjFun ((reflectSymmetry hP).actOn (h.actOn f)) * h.actOn f) U ∂μ ∧
          ∫ U, g.actOn
              (conjFun ((reflectSymmetry hP).actOn (h.actOn f)) * h.actOn f) U ∂μ =
            ∫ U, (conjFun ((reflectSymmetry hP).actOn (h.actOn f)) * h.actOn f) U ∂μ) ∧
        ((∀ f' ∈ localRegionObservables a P.upperHalfSpace,
            0 ≤ ∫ U, (conjFun ((reflectSymmetry hP).actOn f') * f') U ∂μ) →
          (∀ f' ∈ localRegionObservables a P.lowerHalfSpace,
            0 ≤ ∫ U, (conjFun ((reflectSymmetry hP).actOn f') * f') U ∂μ) →
          (∀ f ∈ localRegionObservables a P'.upperHalfSpace,
            0 ≤ ∫ U, (conjFun ((reflectSymmetry hP').actOn f) * f) U ∂μ) ∧
          ∀ f ∈ localRegionObservables a P'.lowerHalfSpace,
            0 ≤ ∫ U, (conjFun ((reflectSymmetry hP').actOn f) * f) U ∂μ)
def AllRules : Prop :=
  ∀ a : Spacing,
    RegionObservablesMonotoneStarAlgebras (a : ℝ) ∧
    ActionLinearUnitalIsometric (a : ℝ) ∧
    IdentityActsTrivially (a : ℝ) ∧
    InverseActsInversely (a : ℝ) ∧
    ActionMapsLocalObservables (a : ℝ) ∧
    ShiftsComposeOnObservables (a : ℝ) ∧
    SymmetryClosedUnderCompAndInverse (a : ℝ) ∧
    ReflectionIsIsometricInvolution (a : ℝ) ∧
    SymmetryMapsMirrorsAndHalfSpaces (a : ℝ) ∧
    SymmetricStateTransportsPositivity (a : ℝ)
end ObservableRules
end LatticeConventions
end YangMills.Construction
end
