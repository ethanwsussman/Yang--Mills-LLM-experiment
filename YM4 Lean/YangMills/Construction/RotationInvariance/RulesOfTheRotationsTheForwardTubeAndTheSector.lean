import YangMills.Construction.RotationInvariance.EntireFunctionOfTheAngleOnAPencil
import YangMills.Construction.RotationInvariance.TubesOfTheFramesAndOrderings
import Mathlib
set_option autoImplicit false
open Complex (I)
open ComplexConjugate
noncomputable section
namespace YangMills.Construction.ForwardTube.RotationRules
def LightConeAndComplexRotationRules : Prop :=
  IsLinearMap ℂ (fun v : ℂ × ℂ => (lightConePlus v, lightConeMinus v)) ∧
  Function.Bijective (fun v : ℂ × ℂ => (lightConePlus v, lightConeMinus v)) ∧
  (∀ v : ℂ × ℂ, v.1 = 1 / 2 * (lightConePlus v + lightConeMinus v) ∧
    v.2 = 1 / (2 * I) * (lightConePlus v - lightConeMinus v)) ∧
  complexBoost 0 = id ∧
  (∀ α : ℂ, IsLinearMap ℂ (complexBoost α) ∧ Function.Bijective (complexBoost α) ∧
    Function.LeftInverse (complexBoost (-α)) (complexBoost α) ∧
    Function.RightInverse (complexBoost (-α)) (complexBoost α)) ∧
  (∀ α β : ℂ, complexBoost α ∘ complexBoost β = complexBoost (α + β) ∧
    complexBoost (α + β) = complexBoost β ∘ complexBoost α) ∧
  (∀ α : ℂ, complexBoost (α + 2 * (Real.pi : ℂ)) = complexBoost α) ∧
  (∀ (θ : ℝ) (v : ℂ × ℂ), complexBoost (θ : ℂ) v =
    (v.1 * (Real.cos θ : ℂ) - v.2 * (Real.sin θ : ℂ),
      v.1 * (Real.sin θ : ℂ) + v.2 * (Real.cos θ : ℂ))) ∧
  (∀ θ : ℝ, complexBoost (θ : ℂ) '' realVectors = realVectors) ∧
  (∀ (θ : ℝ) (v : ℂ × ℂ), v ∈ realVectors ↔ complexBoost (θ : ℂ) v ∈ realVectors) ∧
  ∀ (θ : ℝ) (v : ℂ × ℂ),
    vecRe (complexBoost (θ : ℂ) v) = RealPlane.rotate θ (vecRe v)
def TupleRotationPermutationShiftRules : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ (α : ℂ) (z : Fin (m + 1) → ℂ × ℂ) (c : ℂ × ℂ)
    (σ τ : Equiv.Perm (Fin (m + 1))) (f : Fin (m + 1) → RealPlane.realLabels),
    complexBoostTuple α (RealPlane.permuteTuple σ z) =
        RealPlane.permuteTuple σ (complexBoostTuple α z) ∧
    complexDifferences (complexBoostTuple α z) =
        complexBoostTuple α (complexDifferences z) ∧
    complexBoostTuple α (fun i => z i + c) =
        (fun i => complexBoostTuple α z i + complexBoost α c) ∧
    RealPlane.permuteTuple σ (fun i => z i + c) = (fun i => RealPlane.permuteTuple σ z i + c) ∧
    complexDifferences (fun i => z i + c) = complexDifferences z ∧
    tupleRe (RealPlane.permuteTuple σ z) = RealPlane.permuteTuple σ (tupleRe z) ∧
    tupleRe (complexDifferences z) = RealPlane.successiveDifferences (tupleRe z) ∧
    RealPlane.permuteTuple τ (RealPlane.permuteTuple σ z) = RealPlane.permuteTuple (σ * τ) z ∧
    RealPlane.permuteTuple τ (RealPlane.permuteTuple σ f) = RealPlane.permuteTuple (σ * τ) f
def PlaneInnerRotationReflectionRules : Prop :=
  (∀ (θ : ℝ) (x y : RealPlane),
    inner ℝ x y = (conj (lightConePlus (embedPlane x)) * lightConePlus (embedPlane y)).re ∧
    ‖x‖ = ‖lightConePlus (embedPlane x)‖ ∧
    inner ℝ (RealPlane.rotate θ x) (RealPlane.rotate θ y) = inner ℝ x y ∧
    RealPlane.rotate θ RealPlane.unitX = !₂[Real.cos θ, Real.sin θ] ∧
    inner ℝ (RealPlane.rotate θ RealPlane.unitX) x = RealPlane.rotate (-θ) x 0 ∧
    RealPlane.reflectFirst (RealPlane.rotate θ RealPlane.unitX) =
      RealPlane.rotate (Real.pi - θ) RealPlane.unitX ∧
    ∀ ψ : ℝ, lightConePlus (embedPlane x) = (‖x‖ : ℂ) * Complex.exp (I * (ψ : ℂ)) →
      RealPlane.rotate θ x 0 = ‖x‖ * Real.cos (ψ + θ)) ∧
  IsLinearMap ℝ RealPlane.reflectFirst ∧
  Function.Involutive RealPlane.reflectFirst ∧
  RealPlane.reflectFirst '' RealPlane.openRightHalf = RealPlane.openLeftHalf ∧
  RealPlane.reflectFirst '' RealPlane.openLeftHalf = RealPlane.openRightHalf
def AffineAndRotationHolomorphy : Prop :=
  (∀ N M : ℕ, 1 ≤ N → 1 ≤ M →
    (∀ P : Fin M → MvPolynomial (Fin N) ℂ, (∀ j, (P j).totalDegree ≤ 1) →
      Coordinates.ComplexCoordinates.IsHolomorphicIn Set.univ
        (fun (z : Coordinates.ComplexCoordinates N) (j : Fin M) => MvPolynomial.eval z (P j))) ∧
    ∀ L : Coordinates.ComplexCoordinates N →ₗ[ℂ] Coordinates.ComplexCoordinates M,
      Coordinates.ComplexCoordinates.IsHolomorphicIn Set.univ L) ∧
  ∀ m : ℕ, 1 ≤ m →
    IsHolomorphicScalarPairMap (q := m + 1) (q' := m + 1) Set.univ
      (fun p => complexBoostTuple (I * p.1) p.2) ∧
    ∀ z : Fin (m + 1) → ℂ × ℂ,
      Coordinates.ComplexCoordinates.IsHolomorphicVia
        Matrices.GroupLieProduct.Subspaces.AnalyticCalculus.scalarEquiv
        (pairTupleEquiv (m + 1)) Set.univ
        (fun α : ℂ => complexBoostTuple α z)
def TubeAndRotatedTubeRules : Prop :=
  forwardTube = {v : ℂ × ℂ | v.1.re > |v.2.im|} ∧
  forwardTube ∩ realVectors = embedPlane '' RealPlane.openRightHalf ∧
  (∀ k : rightAngleMultiples,
    IsOpen (rotatedForwardTube k) ∧
    Convex ℝ (rotatedForwardTube k) ∧
    (∀ v ∈ rotatedForwardTube k, ∀ r : ℝ, 0 < r → r • v ∈ rotatedForwardTube k) ∧
    (∀ s : ℝ, complexBoost (I * (s : ℂ)) '' rotatedForwardTube k = rotatedForwardTube k) ∧
    (∀ v ∈ rotatedForwardTube k, embedPlane (vecRe v) ∈ rotatedForwardTube k) ∧
    ∀ x : RealPlane, embedPlane x ∈ rotatedForwardTube k ↔ inner ℝ (rotatedDirection k) x > 0) ∧
  rotatedForwardTube rightAngleZero = forwardTube
def SectorAndPencilRules : Prop :=
  ∀ β : RealPlane.openingAngles,
    RealPlane.coneSector β = {x : RealPlane | x 0 > 0 ∧ |x 1| < x 0 * Real.tan β} ∧
    IsOpen (RealPlane.coneSector β) ∧
    RealPlane.coneSector β ⊆ RealPlane.openRightHalf ∧
    RealPlane.unitX ∈ RealPlane.coneSector β ∧
    ∀ m : ℕ, 1 ≤ m →
      IsOpen (RealPlane.pencilSet β (m + 1)) ∧
      (fun l : Fin (m + 1) => (((l : ℕ) : ℝ) + 1) • RealPlane.unitX) ∈ RealPlane.pencilSet β (m + 1)
def Holds : Prop :=
  LightConeAndComplexRotationRules ∧
  TupleRotationPermutationShiftRules ∧
  PlaneInnerRotationReflectionRules ∧
  AffineAndRotationHolomorphy ∧
  TubeAndRotatedTubeRules ∧
  SectorAndPencilRules
end YangMills.Construction.ForwardTube.RotationRules
end
