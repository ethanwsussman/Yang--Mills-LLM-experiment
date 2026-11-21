import YangMills.Construction.InfiniteLattice.HyperoctahedralMotionsAndCubes
import YangMills.Construction.InfiniteLattice.SeparatedTuplesOfFourSpaceAsSymbols
import YangMills.Construction.InfiniteLattice.TuplesCombinationsNormalsAndMirrorsOfFourSpace
import Mathlib
set_option autoImplicit false
open YangMills.Construction.AmbientPoints YangMills.Construction.Continuum.SeparatedFourTuples
open YangMills.Construction.LatticeConventions (euclidDot)
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice.EuclideanMirrors
namespace MirrorReflections
def unitNormalVec (n : ReflNormal) : Fin 4 → ℝ := (Real.sqrt n.sqNorm)⁻¹ • n.1
def IsOrthogonalReflection (n : ReflNormal) (c : ℝ) : Prop :=
  TorusMetric.euclidNormVec (unitNormalVec n) = 1 ∧
    (AffineMirror.mk n c).carrier = {x | euclidDot (unitNormalVec n) x = c / Real.sqrt n.sqNorm} ∧
    (∀ x y, TorusMetric.euclidNormVec (hyperplaneReflection n c x - hyperplaneReflection n c y) =
      TorusMetric.euclidNormVec (x - y)) ∧
    (∀ x ∈ (AffineMirror.mk n c).carrier, hyperplaneReflection n c x = x) ∧
    (∀ x, euclidDot n.1 (hyperplaneReflection n c x) - c = -(euclidDot n.1 x - c)) ∧
    (∀ x, ∃ t : ℝ, hyperplaneReflection n c x - x = t • n.1) ∧
    Function.Involutive (hyperplaneReflection n c) ∧
    hyperplaneReflection n c '' {x | c < euclidDot n.1 x} = {x | euclidDot n.1 x < c} ∧
    hyperplaneReflection n c '' {x | euclidDot n.1 x < c} = {x | c < euclidDot n.1 x}
def LatticeAlignedEqClassMirrors (b : ℝ) : Prop :=
  (∀ M : AffineMirror, M.IsLatticeAligned b →
    M.reflect '' (InfiniteLattice.latticeSubgroup b : Set (Fin 4 → ℝ)) =
      InfiniteLattice.latticeSubgroup b) ∧
    {H : Set (Fin 4 → ℝ) | ∃ M : AffineMirror, M.IsLatticeAligned b ∧ M.IsAxial ∧ M.carrier = H} =
      {H | ∃ (P : InfiniteLattice.LatticeMirror b) (μ : Fin 4),
        P.cls = .axial μ ∧ P.plane = H} ∧
    {H : Set (Fin 4 → ℝ) | ∃ M : AffineMirror, M.IsLatticeAligned b ∧ M.IsDiagonal ∧ M.carrier = H} =
      {H | ∃ (P : InfiniteLattice.LatticeMirror b) (μ ν : Fin 4) (hμν : μ < ν) (ε : ℤˣ),
        P.cls = .diagonal μ ν hμν ε ∧ P.plane = H} ∧
    {H : Set (Fin 4 → ℝ) | ∃ M : AffineMirror, M.IsLatticeAligned b ∧ M.carrier = H} =
      {H | ∃ F : InfiniteLattice.ReflectionClass, ∃ P ∈ F.mirrors b, P.plane = H} ∧
    (∀ M : AffineMirror, M.IsLatticeAligned b → ∀ P : InfiniteLattice.LatticeMirror b,
      P.plane = M.carrier → P.symmetry.toFun = M.reflect) ∧
    ∀ n : ReflNormal, (AffineMirror.mk n 0).IsLatticeAligned b
def OriginReflectionHyperoctahedral (n : ReflNormal) : Prop :=
  ∃ w ∈ InfiniteLattice.hyperoctahedralLinearGroup, ⇑w = hyperplaneReflection n 0
def reflectTuple (s : Conventions.StandingParameters) (n : ReflNormal) (c : ℝ) (X : SepTuple s) :
    SepTuple s :=
  FourSpaceSymbols.transportSymbol (isDistIsometry_hyperplaneReflectionEquiv s n c) X
def OppositeSideTuples (s : Conventions.StandingParameters) (n : ReflNormal) (c : ℝ) : Prop :=
  ∀ X Y : SepTuple s, X ∈ sepTuplesIn (s := s) (AffineMirror.mk n c).positiveSide →
    Y ∈ sepTuplesIn (s := s) (AffineMirror.mk n c).positiveSide →
    (∀ i, tsupport (tupleComponents (reflectTuple s n c X) i) ⊆ {x : Fin 4 → ℝ | euclidDot n.1 x < c}) ∧
      joinTuple (reflectTuple s n c X) Y ∈ allSeparatedTuples s .euclidean
def ReflectionEqShiftOriginReflection (s : Conventions.StandingParameters) (n : ReflNormal)
    (c : ℝ) : Prop :=
  ∀ x : Fin 4 → ℝ, hyperplaneReflection n c x =
    FourSpaceSymbols.translationEquiv s ((2 * c) • n.dual) (hyperplaneReflection n 0 x)
def ReflectionAboutMirrorPoint (s : Conventions.StandingParameters) (n : ReflNormal) (c : ℝ) : Prop :=
  euclidDot n.1 (c • n.dual) = c ∧
    ∀ v : Fin 4 → ℝ, euclidDot n.1 v = c →
      (∀ x, hyperplaneReflection n c x - v = hyperplaneReflection n 0 (x - v)) ∧
      (∀ (Z : Type) (h : EuclideanFour s → Z) (x : Fin 4 → ℝ),
        FourSpaceSymbols.translateFn v h (hyperplaneReflection n c x) =
          FourSpaceSymbols.translateFn (s := s) v
            (fun y : Fin 4 → ℝ => h (hyperplaneReflection n 0 y)) x) ∧
      ∀ Y : SepTuple s,
        reflectTuple s n c (FourSpaceSymbols.translateSymbol v Y) =
          FourSpaceSymbols.translateSymbol v (reflectTuple s n 0 Y)
def Statement : Prop :=
  (∀ (n : ReflNormal) (c : ℝ), IsOrthogonalReflection n c) ∧
    (∀ b : ℝ, 0 < b → LatticeAlignedEqClassMirrors b) ∧
    (∀ n : ReflNormal, OriginReflectionHyperoctahedral n) ∧
    ∀ (s : Conventions.StandingParameters) (n : ReflNormal) (c : ℝ), OppositeSideTuples s n c ∧
      ReflectionEqShiftOriginReflection s n c ∧
      ReflectionAboutMirrorPoint s n c
end MirrorReflections
end InfiniteLattice.EuclideanMirrors
end YangMills.Construction
end
