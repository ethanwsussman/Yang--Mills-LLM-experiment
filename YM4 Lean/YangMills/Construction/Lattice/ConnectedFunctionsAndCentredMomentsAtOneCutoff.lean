import YangMills.Construction.Lattice.SignsAtOneCutoffOfTheTorusOfExponentM
import YangMills.Construction.ReflectionPositivity.IsometriesCentringTuplesAndTheTwoFunctionals
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.CutoffNotation
variable (S : Conventions.StandingParameters) (β : ℝ) {n q : ℕ}
def IsRealValued (f : S.Torus → ℂ) : Prop := ∀ x, (f x).im = 0
def cumulantOfReal (f : Fin n → S.Torus → ℝ) : ℂ :=
  PeriodicLattice.gibbsCumulant S.L S.m S.K β fun l U => smearedObs S (f l) U
def markExpansion (f : Fin n → S.Torus → ℂ) : ℂ :=
  ∑ ε : Fin n → Fin 2, Complex.I ^ markSum ε *
    cumulantOfReal S β fun l => reImPart S (f l) (ε l)
open Classical in
def connectedFn (f : Fin n → S.Torus → ℂ) : ℂ :=
  if ∀ l, IsRealValued S (f l) then cumulantOfReal S β fun l x => (f l x).re
  else markExpansion S β f
theorem connectedFn_ofReal (f : Fin n → S.Torus → ℝ) :
    connectedFn S β (fun l x => (f l x : ℂ)) = cumulantOfReal S β f := by
  have hr : ∀ l, IsRealValued S fun x => ((f l x : ℝ) : ℂ) := fun l x => Complex.ofReal_im _
  simp [connectedFn, hr]
def DisjointSupports {E : Type*} [NormedAddCommGroup E] (h : Fin q → S.Torus → E) : Prop :=
  ReflectionPositivity.CutoffMirrors.MirrorData.PairwiseDisjointSupp
    (D := defaultMirrorData S) h
def centredMomentFn (h : Fin q → S.Torus → ℂ) : ℂ :=
  ∑ π ∈ SetPartition.singletonFree q, ∏ B ∈ π.parts,
    connectedFn S β fun k : Fin B.card => h (B.orderEmbOfFin rfl k)
def IsCentredMomentArg (h : Fin q → S.Torus → ℂ) : Prop :=
  (∀ l, HasFiniteLip S (h l)) ∧ DisjointSupports S h
end YangMills.Construction.CutoffNotation
end
