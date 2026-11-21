import YangMills.Construction.InfiniteLattice.ReflectionInALatticeMirrorGivenWithANormal
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace LatticeConventions
namespace MirrorReflections
open YangMills.Construction.InfiniteLattice (LatticeMirror ReflectionClass latticeSubgroup)
def sumPlane (μ lam : Direction) (h : μ ≠ lam) (c : ℝ) : NormalHyperplane :=
  ⟨basisVector μ + basisVector lam, c, Or.inr ⟨μ, lam, h, Or.inl rfl⟩⟩
def diffPlane (μ lam : Direction) (h : μ ≠ lam) (c : ℝ) : NormalHyperplane :=
  ⟨basisVector μ - basisVector lam, c, Or.inr ⟨μ, lam, h, Or.inr rfl⟩⟩
def normalize (n : Point) : Point := (euclidNorm n)⁻¹ • n
def ReflectFixesAndSwaps (P : NormalHyperplane) : Prop :=
  (∀ x ∈ P.carrier, P.reflect x = x) ∧
    P.reflect '' P.upperHalfSpace = P.lowerHalfSpace ∧
    P.reflect '' P.lowerHalfSpace = P.upperHalfSpace
def LinearNegatesNormal (P : NormalHyperplane) : Prop :=
  P.reflectionLinear P.normal = -P.normal ∧
    ∀ w : Point, euclidDot P.normal w = 0 → P.reflectionLinear w = w
def ActsOnOneAxis (P : NormalHyperplane) (μ : Direction) : Prop :=
  ∀ x : Point, P.reflect x μ = 2 * P.level - x μ ∧
    ∀ ν : Direction, ν ≠ μ → P.reflect x ν = x ν
def ActsOnSumAxes (P : NormalHyperplane) (μ lam : Direction) : Prop :=
  ∀ x : Point, P.reflect x μ = P.level - x lam ∧ P.reflect x lam = P.level - x μ ∧
    ∀ ν : Direction, ν ≠ μ → ν ≠ lam → P.reflect x ν = x ν
def ActsOnDiffAxes (P : NormalHyperplane) (μ lam : Direction) : Prop :=
  ∀ x : Point, P.reflect x μ = P.level + x lam ∧ P.reflect x lam = x μ - P.level ∧
    ∀ ν : Direction, ν ≠ μ → ν ≠ lam → P.reflect x ν = x ν
def AxisAction (P : NormalHyperplane) : Prop :=
  ∀ μ lam : Direction, μ ≠ lam →
    (P.normal = basisVector μ → ActsOnOneAxis P μ) ∧
      (P.normal = basisVector μ + basisVector lam → ActsOnSumAxes P μ lam) ∧
      (P.normal = basisVector μ - basisVector lam → ActsOnDiffAxes P μ lam)
def PreservesLatticeIff (a : Spacing) (P : NormalHyperplane) : Prop :=
  P.reflect '' (latticeSubgroup (a : ℝ) : Set Point) = (latticeSubgroup (a : ℝ) : Set Point) ↔
    P.IsLatticeMirror (a : ℝ)
def MirrorsClassified (a : Spacing) : Prop :=
  Nat.card ReflectionClass = 16 ∧
    {E : Set Point | ∃ P : NormalHyperplane, P.IsLatticeMirror (a : ℝ) ∧ P.carrier = E} =
      ⋃ C : ReflectionClass, LatticeMirror.plane '' C.mirrors (a : ℝ) ∧
    ∀ P : NormalHyperplane, P.IsLatticeMirror (a : ℝ) →
      ∃! C : ReflectionClass, P.carrier ∈ LatticeMirror.plane '' C.mirrors (a : ℝ)
def DiagonalPlanesAreMirrors (a : Spacing) : Prop :=
  ∀ (μ lam : Direction) (h : μ ≠ lam),
    (sumPlane μ lam h 0).IsLatticeMirror (a : ℝ) ∧
      (diffPlane μ lam h 0).IsLatticeMirror (a : ℝ)
def DiagonalPlaneUnitNormal : Prop :=
  ∀ (j : SpatialDirection) (c : ℝ),
    {x : Point | x timeAxis + x j.toDirection = c} =
      {x : Point | euclidDot (normalize (basisVector timeAxis + basisVector j.toDirection)) x =
        c / Real.sqrt 2}
def IsIsometricInvolution (a : Spacing) (P : NormalHyperplane) : Prop :=
  (∀ x y : Point, euclidNorm (P.reflect x - P.reflect y) = euclidNorm (x - y)) ∧
    P.reflect ∘ P.reflect = id ∧
    (∀ x v : Point, P.reflect (x + v) = P.reflect x + P.reflectionLinear v) ∧
    ∀ hP : P.IsLatticeMirror (a : ℝ),
      (NormalHyperplane.reflectSymmetry hP).toFun = P.reflect
def LinearEigenvectors (P : NormalHyperplane) : Prop :=
  ∀ v : Point,
    (P.reflectionLinear v = -v ↔
        v = ((euclidNorm P.normal ^ 2)⁻¹ * euclidDot P.normal v) • P.normal) ∧
      (P.reflectionLinear v = v ↔ euclidDot P.normal v = 0)
def SamePlaneTwoNormals (a : Spacing) (P P' : NormalHyperplane) : Prop :=
  (P'.normal, P'.level) ≠ (P.normal, P.level) →
    (P'.carrier = P.carrier ↔
      ∃ μ lam : Direction, μ ≠ lam ∧ P.normal = basisVector μ - basisVector lam ∧
        P'.normal = basisVector lam - basisVector μ ∧ P'.level = -P.level) ∧
    (P'.carrier = P.carrier →
      P'.reflect = P.reflect ∧ P'.reflectionLinear = P.reflectionLinear ∧
        (P'.IsLatticeMirror (a : ℝ) ↔ P.IsLatticeMirror (a : ℝ)) ∧
        P'.upperHalfSpace = P.lowerHalfSpace ∧ P.upperHalfSpace = P'.lowerHalfSpace)
def MirrorReflectionsStatement : Prop :=
  ∀ a : Spacing,
    (∀ P : NormalHyperplane,
      ReflectFixesAndSwaps P ∧
        LinearNegatesNormal P ∧
        AxisAction P ∧
        PreservesLatticeIff a P) ∧
      MirrorsClassified a ∧
      DiagonalPlanesAreMirrors a ∧
      DiagonalPlaneUnitNormal ∧
      (∀ P : NormalHyperplane,
        IsIsometricInvolution a P ∧
          LinearEigenvectors P) ∧
      ∀ P P' : NormalHyperplane, SamePlaneTwoNormals a P P'
end MirrorReflections
end LatticeConventions
end YangMills.Construction
end
