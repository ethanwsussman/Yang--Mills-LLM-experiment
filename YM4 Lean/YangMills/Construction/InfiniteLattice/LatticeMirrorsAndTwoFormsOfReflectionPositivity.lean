import YangMills.Construction.InfiniteLattice.ReflectionPositivityAtAMirrorGivenWithANormal
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction.LatticeConventions
open YangMills.Construction.InfiniteLattice (GaugeField IsLocalObservable IsRegionMeasurable
  IsBoundedObservable IsReflectionPositiveAt IsReflectionPositiveOn LatticeMirror ReflectionClass
  localRegionObservables)
open NormalHyperplane (IsReflectionPositiveAcrossMirror IsReflectionPositiveAcrossFamily
  reflectSymmetry)
def diagonalClassOfPair (μ ν : Direction) (hne : μ ≠ ν) (s : ℤˣ) : ReflectionClass :=
  if hlt : μ < ν then .diagonal μ ν hlt s
  else .diagonal ν μ (lt_of_le_of_ne (not_lt.1 hlt) hne.symm) s
def MirrorPlanesEqLatticeMirrorCarriers (a : ℝ) : Prop :=
  ∀ P : Set Point, (∃ M : LatticeMirror a, M.plane = P) ↔
    ∃ Q : NormalHyperplane, Q.IsLatticeMirror a ∧ Q.carrier = P
def AxialNormalMirror (a : ℝ) : Prop :=
  ∀ (μ : Direction) (Q : NormalHyperplane), Q.IsLatticeMirror a → Q.normal = basisVector μ →
    Q.carrier = {x | x μ = Q.level} ∧
    ∃ M : LatticeMirror a, M.cls = .axial μ ∧ M.level = Q.level ∧ M.plane = Q.carrier ∧
      (M.ContainsSites ↔ Q.IsVertexMirror a) ∧ (M.BisectsLinks ↔ Q.IsEdgeMirror a)
def AxialNormalClass (a : ℝ) : Prop :=
  ∀ μ : Direction,
    NormalHyperplane.carrier '' NormalHyperplane.mirrorsWithNormal a (basisVector μ) =
      {P | ∃ c : ℝ, (∃ q : ℤ, c = (q : ℝ) * (a / 2)) ∧ P = {x | x μ = c}} ∧
    NormalHyperplane.carrier '' NormalHyperplane.mirrorsWithNormal a (basisVector μ) =
      (fun M : LatticeMirror a => M.plane) '' ReflectionClass.mirrors a (.axial μ)
def DiagonalNormalMirror (a : ℝ) : Prop :=
  ∀ (μ ν : Direction) (hne : μ ≠ ν) (s : ℤˣ) (Q : NormalHyperplane),
    Q.IsLatticeMirror a → Q.normal = basisVector μ + ((s : ℤ) : ℝ) • basisVector ν →
    Q.carrier = {x | x μ + ((s : ℤ) : ℝ) * x ν = Q.level} ∧
    ∃ M : LatticeMirror a, M.cls = diagonalClassOfPair μ ν hne s ∧ M.plane = Q.carrier
def DiagonalNormalClass (a : ℝ) : Prop :=
  ∀ (μ ν : Direction) (hne : μ ≠ ν),
    (∀ s : ℤˣ,
      NormalHyperplane.carrier '' NormalHyperplane.mirrorsWithNormal a
          (basisVector μ + ((s : ℤ) : ℝ) • basisVector ν) =
        {P | ∃ c : ℝ, (∃ q : ℤ, c = (q : ℝ) * a) ∧
          P = {x | x μ + ((s : ℤ) : ℝ) * x ν = c}} ∧
      NormalHyperplane.carrier '' NormalHyperplane.mirrorsWithNormal a
          (basisVector μ + ((s : ℤ) : ℝ) • basisVector ν) =
        (fun M : LatticeMirror a => M.plane) ''
          ReflectionClass.mirrors a (diagonalClassOfPair μ ν hne s)) ∧
    NormalHyperplane.carrier '' NormalHyperplane.mirrorsWithNormal a (basisVector μ - basisVector ν) =
      NormalHyperplane.carrier '' NormalHyperplane.mirrorsWithNormal a (basisVector ν - basisVector μ)
def MirrorReflectionAndHalfSpaces (a : ℝ) : Prop :=
  ∀ (Q : NormalHyperplane) (hQ : Q.IsLatticeMirror a) (M : LatticeMirror a),
    M.plane = Q.carrier →
    M.symmetry.toFun = Q.reflect ∧
    (∀ F : GaugeField a → ℂ, IsBoundedObservable F →
      M.conjReflect F = conjFun ((reflectSymmetry hQ).actOn F)) ∧
    ∀ H : Set Point, M.IsHalfSpace H ↔ H = Q.upperHalfSpace ∨ H = Q.lowerHalfSpace
def LocalRegionObservablesChar (a : ℝ) : Prop :=
  ∀ S : Set Point,
    localRegionObservables a S =
      {F | IsBoundedObservable F ∧ IsLocalObservable F ∧ IsRegionMeasurable S F}
def OneSidedPositivityIffReflectionPositive (a : ℝ) : Prop :=
  ∀ (Q : NormalHyperplane) (hQ : Q.IsLatticeMirror a) (M : LatticeMirror a),
    M.plane = Q.carrier →
    ∀ H : Set Point, H = Q.upperHalfSpace ∨ H = Q.lowerHalfSpace →
    ∀ (μ : Measure (GaugeField a)) [IsProbabilityMeasure μ],
      (∀ F : GaugeField a → ℂ, IsBoundedObservable F → IsLocalObservable F →
        IsRegionMeasurable H F →
        0 ≤ ∫ U, F U * M.conjReflect F U ∂μ) ↔ IsReflectionPositiveAcrossMirror hQ μ
def ReflectionPositivityFormulationsAgree (a : ℝ) : Prop :=
  ∀ (Q : NormalHyperplane) (hQ : Q.IsLatticeMirror a) (M : LatticeMirror a),
    M.plane = Q.carrier →
    ∀ (μ : Measure (GaugeField a)) [IsProbabilityMeasure μ],
      (IsReflectionPositiveAt μ M ↔ IsReflectionPositiveAcrossMirror hQ μ) ∧
      (IsReflectionPositiveOn μ (ReflectionClass.mirrors a M.cls) ↔
        IsReflectionPositiveAcrossFamily (NormalHyperplane.mirrorsWithNormal a Q.normal)
          (fun _ hQ' => hQ'.2) μ)
def LatticeMirrorsAndReflectionPositivity.Statement : Prop :=
  ∀ a : Spacing,
    MirrorPlanesEqLatticeMirrorCarriers (a : ℝ) ∧
    AxialNormalMirror (a : ℝ) ∧
    AxialNormalClass (a : ℝ) ∧
    DiagonalNormalMirror (a : ℝ) ∧
    DiagonalNormalClass (a : ℝ) ∧
    MirrorReflectionAndHalfSpaces (a : ℝ) ∧
    LocalRegionObservablesChar (a : ℝ) ∧
    OneSidedPositivityIffReflectionPositive (a : ℝ) ∧
    ReflectionPositivityFormulationsAgree (a : ℝ)
end YangMills.Construction.LatticeConventions
end
