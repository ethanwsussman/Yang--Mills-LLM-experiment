import YangMills.Construction.InfiniteLattice.OneFamilyOfMirrors
import YangMills.Construction.InfiniteLattice.OrientedBondsLiftsAndPreservedMeasuresOfATorus
import YangMills.Construction.ReflectionPositivity.PeriodLatticesSplitForANormal
import Mathlib
set_option autoImplicit false
open scoped Matrix
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
namespace PeriodSublattice
variable (Λ : PeriodSublattice 1)
structure MapsOrbits (g : LatticeSymmetry 1) : Prop where
  points_orbit : ∀ x : LatticePoint 1, g.pointMap '' {y | Λ.quotientMap y = Λ.quotientMap x} =
    {y | Λ.quotientMap y = Λ.quotientMap (g.pointMap x)}
  links_orbit : ∀ e : Link 1,
    g.linkMap '' Λ.orientedOrbit e = Λ.orientedOrbit (g.linkMap e)
  faces_orbit : ∀ f : ElementaryPlaquette 1,
    g.plaquetteMap '' Λ.plaquetteOrbit f = Λ.plaquetteOrbit (g.plaquetteMap f)
def descendPoint (g : LatticeSymmetry 1) (s : Λ.QuotientTorus) : Λ.QuotientTorus :=
  Λ.quotientMap (g.pointMap s.out)
def descendOrientedLink (g : LatticeSymmetry 1) (c : Λ.OrientedLink) :
    Λ.OrientedLink :=
  Λ.orientedClass (g.linkMap (Λ.orientedRep c))
def descendFace (g : LatticeSymmetry 1) (F : Λ.QuotientPlaquette) : Λ.QuotientPlaquette :=
  Λ.faceClass (g.plaquetteMap (Λ.plaquetteRep F))
structure DescendsToQuotient (g : LatticeSymmetry 1) : Prop where
  descendPoint_quotientMap : ∀ x : LatticePoint 1,
    Λ.descendPoint g (Λ.quotientMap x) = Λ.quotientMap (g.pointMap x)
  descendOrientedLink_orientedClass : ∀ e : Link 1,
    Λ.descendOrientedLink g (Λ.orientedClass e) = Λ.orientedClass (g.linkMap e)
  descendFace_faceClass : ∀ f : ElementaryPlaquette 1,
    Λ.descendFace g (Λ.faceClass f) = Λ.faceClass (g.plaquetteMap f)
  descendPoint_bijective : Function.Bijective (Λ.descendPoint g)
  descendOrientedLink_bijective : Function.Bijective (Λ.descendOrientedLink g)
  descendFace_bijective : Function.Bijective (Λ.descendFace g)
  sourcePoint_descend : ∀ c : Λ.OrientedLink,
    Λ.sourcePoint (Λ.descendOrientedLink g c) = Λ.descendPoint g (Λ.sourcePoint c)
  targetPoint_descend : ∀ c : Λ.OrientedLink,
    Λ.targetPoint (Λ.descendOrientedLink g c) = Λ.descendPoint g (Λ.targetPoint c)
  plaquetteVertices_descend : ∀ F : Λ.QuotientPlaquette,
    Λ.plaquetteVertices (Λ.descendFace g F) = Λ.descendPoint g '' Λ.plaquetteVertices F
structure SameDescent (g g' : LatticeSymmetry 1) : Prop where
  points_eq : Λ.descendPoint g = Λ.descendPoint g'
  links_eq : Λ.descendOrientedLink g = Λ.descendOrientedLink g'
  faces_eq : Λ.descendFace g = Λ.descendFace g'
end PeriodSublattice
open NormalFamilies
def SplitTorusDescent : Prop :=
  ∀ (Λ : PeriodSublattice 1) (n : AmbientSpace) (hn : n ∈ normalSet) (m : ℤ) (c : ℝ)
    (hc : IsAllowedLevel 1 n c) (v : LatticePoint 1), Λ.SplitsAlongWithHalfPeriod n m →
    let Q : NormalLevelPair 1 := ⟨n, hn, c, hc⟩
    (∃ w : LatticePoint 1, (w : AmbientSpace) = (2 * (m : ℝ)) • dualVector n) ∧
    n ⬝ᵥ ((2 * (m : ℝ)) • dualVector n) = 2 * (m : ℝ) ∧
    (∀ γ ∈ Λ.periods, ∃ k : ℤ, n ⬝ᵥ (γ : AmbientSpace) = 2 * (m : ℝ) * (k : ℝ)) ∧
    (∀ x y : LatticePoint 1, Λ.quotientMap x = Λ.quotientMap y →
      ∃ k : ℤ, n ⬝ᵥ (x : AmbientSpace) - n ⬝ᵥ (y : AmbientSpace) = 2 * (m : ℝ) * (k : ℝ)) ∧
    (∀ H : AddSubgroup AmbientSpace, Λ.IsTransverseComplement n m H →
      ∀ x : AmbientSpace, x ∈ H ↔ x ∈ Λ.toAmbient ∧ n ⬝ᵥ x = 0) ∧
    linearReflect n '' (Λ.toAmbient : Set AmbientSpace) = Λ.toAmbient ∧
    Λ.MapsOrbits (shift v) ∧ Λ.DescendsToQuotient (shift v) ∧
    Λ.MapsOrbits Q.reflectSymmetry ∧ Λ.DescendsToQuotient Q.reflectSymmetry ∧
    (∀ e : Λ.OrientedLink,
      Λ.OrientedIsPositive (Λ.descendOrientedLink (shift v) e) ↔
        Λ.OrientedIsPositive e) ∧
    (v ∈ Λ.periods →
      Λ.descendPoint (shift v) = id ∧
      Λ.descendOrientedLink (shift v) = id ∧
      Λ.descendFace (shift v) = id) ∧
    (∀ f : AmbientSpace → AmbientSpace, IsClassIsometry n f → ∃ g : LatticeSymmetry 1, g.toFun = f) ∧
    (∀ g : LatticeSymmetry 1, IsClassIsometry n g.toFun →
      Λ.MapsOrbits g ∧ Λ.DescendsToQuotient g) ∧
    (∀ g g' g'' : LatticeSymmetry 1, IsClassIsometry n g.toFun →
      IsClassIsometry n g'.toFun → g''.toFun = g.toFun ∘ g'.toFun →
      Λ.descendPoint g'' = Λ.descendPoint g ∘ Λ.descendPoint g' ∧
      Λ.descendOrientedLink g'' = Λ.descendOrientedLink g ∘ Λ.descendOrientedLink g' ∧
      Λ.descendFace g'' = Λ.descendFace g ∘ Λ.descendFace g') ∧
    (∃ h : IsAllowedLevel 1 n (c + (m : ℝ)),
      Λ.SameDescent (NormalLevelPair.reflectSymmetry ⟨n, hn, c + (m : ℝ), h⟩)
        Q.reflectSymmetry) ∧
    (∀ x : LatticePoint 1, n ⬝ᵥ (x : AmbientSpace) = c → reflectAcross n c (x : AmbientSpace) = x) ∧
    (∀ x : LatticePoint 1, n ⬝ᵥ (x : AmbientSpace) = c + (m : ℝ) →
      reflectAcross n c (x : AmbientSpace) = (x : AmbientSpace) - (2 * (m : ℝ)) • dualVector n ∧
      Λ.quotientMap (Q.reflectSymmetry.pointMap x) = Λ.quotientMap x)
end InfiniteLattice
end YangMills.Construction
