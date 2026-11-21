import YangMills.Construction.InfiniteLattice.CoordinateMirrorsThroughLinks
import YangMills.Construction.InfiniteLattice.IsometriesOfTheUnitLattice
import YangMills.Construction.InfiniteLattice.LatticeOfACutoffItsIsometriesAndTimeReflections
import YangMills.Construction.InfiniteLattice.ObservablesAndIsometriesAtOneSpacing
import YangMills.Construction.Lattice.TheDataAtOneCutoffAndTheSpaceOfTheConfigurations
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.InfiniteLattice
variable {a : ℝ}
def Link.midpoint (b : Link a) : AmbientSpace :=
  (1 / 2 : ℝ) • ((b.initial : AmbientSpace) + (b.terminal : AmbientSpace))
def LatticeSymmetry.ActionProperties (r r' : LatticeSymmetry a) : Prop :=
  (∀ A : GaugeField a → ℂ, IsBoundedObservable A →
    (r * r').actOn A = r.actOn (r'.actOn A)) ∧
  (∀ p : ElementaryPlaquette a, ∃ q : ElementaryPlaquette a, q.closedSquare = r.mapSquare p ∧
    r.actOn (fun U : GaugeField a => faceEnergy U p) =
      fun U : GaugeField a => faceEnergy U q) ∧
  (∀ f : AmbientSpace → ℝ, IsBoundedBorelCompactlySupported f →
    r.actOn (smearedEnergy f) = smearedEnergy (r.pushforwardFun f)) ∧
  ∀ f : AmbientSpace → ℂ, IsBoundedBorelCompactlySupported f →
    r.actOn (smearedEnergy f) = smearedEnergy (r.pushforwardFun f)
def TimeReflectionLevelSets (a : ℝ) : Prop :=
  (∀ t : ℝ, (∃ r : LatticeSymmetry a, r.toFun = reflectTime t) ↔
    t ∈ halfSpacingTimes a) ∧
  (∀ t : ℝ, (∃ q : ℤ, t = (q : ℝ) * a) →
    (∃ x : LatticePoint a, (x : AmbientSpace) ∈ equalTimePlane t) ∧
    ∀ x : LatticePoint a, (x : AmbientSpace) timeAxis = t →
      (x : AmbientSpace) ∈ equalTimePlane t) ∧
  ∀ t ∈ halfIntegerLevels a,
    (∀ x : LatticePoint a, (x : AmbientSpace) ∉ equalTimePlane t) ∧
    (∃ b : Link a, b.midpoint ∈ equalTimePlane t) ∧
    ∀ x : LatticePoint a, (x : AmbientSpace) timeAxis = t - a / 2 →
      (x : AmbientSpace) + (a / 2) • basisVector timeAxis ∈ equalTimePlane t ∧
      (x : AmbientSpace) + (a / 2) • basisVector timeAxis =
        (Link.forwardFrom x timeAxis).midpoint
def TimeConjProperties (t : halfSpacingTimes a) : Prop :=
  (∀ B : GaugeField a → ℂ, IsBoundedObservable B → IsBoundedObservable (timeConj t B)) ∧
  (∀ (c c' : ℂ) (B B' : GaugeField a → ℂ), IsBoundedObservable B → IsBoundedObservable B' →
    timeConj t (c • B + c' • B') =
      conj c • timeConj t B + conj c' • timeConj t B') ∧
  (∀ B B' : GaugeField a → ℂ, IsBoundedObservable B → IsBoundedObservable B' →
    timeConj t (B * B') = timeConj t B * timeConj t B') ∧
  ∀ B : GaugeField a → ℂ, IsBoundedObservable B → timeConj t (timeConj t B) = B
def CutoffSymmetriesAndTimeReflections : Prop :=
  ∀ s : YangMills.Construction.Conventions.StandingParameters,
    (∀ r r' : LatticeSymmetry s.spacing, LatticeSymmetry.ActionProperties r r') ∧
    TimeReflectionLevelSets s.spacing ∧
    ∀ t : halfSpacingTimes s.spacing, TimeConjProperties t
end YangMills.Construction.InfiniteLattice
