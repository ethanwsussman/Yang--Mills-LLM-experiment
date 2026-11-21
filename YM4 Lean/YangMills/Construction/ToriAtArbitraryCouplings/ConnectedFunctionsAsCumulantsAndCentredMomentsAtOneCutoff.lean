import YangMills.Construction.Lattice.ConnectedFunctionsAndCentredMomentsAtOneCutoff
import YangMills.Construction.Lattice.ConnectedFunctionsAreAFiniteSumOverPlaquettes
import YangMills.Construction.ReflectionPositivity.CentredObservableAndFunctionals
import YangMills.Construction.ToriAtArbitraryCouplings.MultilinearAndSymmetricFunctionalsOnClassesOfTuples
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open ReflectionPositivity.AxisMirror (Ambient)
open ConnectedFunctionExpansion (IsBoundedOnTorus)
namespace ToriAtArbitraryCouplings.OneCutoffCumulants
variable (D : ReflectionPositivity.AxisMirror.MirrorData)
def connectedValue {n : ℕ} (f : Fin n → D.Torus → ℝ) : ℂ :=
  PeriodicLattice.connectedFunction D.L D.m D.K (D.β : ℂ) f
abbrev torusSide : TorusSide := TorusSide.ofStandingParameters D.toStandingParameters
def restrictLip (n : ℕ) (X : (torusSide D).lipDisjointOfLength .torus n) : ℝ :=
  (connectedValue D X.1.get).re
def restrictSep (n : ℕ)
    (f : AmbientPoints.separatedTuples D.toStandingParameters .torus n) : ℝ :=
  (connectedValue D f.1).re
def IsJointCumulant : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ f : Fin n → D.Torus → ℝ, (∀ i, IsBoundedOnTorus (f i)) →
    connectedValue D f =
      PeriodicLattice.gibbsCumulant D.L D.m D.K D.β fun i U => PeriodicLattice.smearedObservable (f i) U
def IsSchwingerFunction : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ f : Fin n → D.Torus → ℝ, SchwingerFunctions.IsTorusTestFamily f →
    connectedValue D f = SchwingerFunctions.connectedSchwinger D.L D.m D.K D.β f
def IsLipschitzNumber : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ f : Fin n → D.Torus → ℝ,
    (∀ i, CutoffNotation.HasFiniteLip D.toStandingParameters (f i)) →
      connectedValue D f =
        CutoffNotation.connectedFn D.toStandingParameters D.β fun i x => (f i x : ℂ)
def IsRealSymmMultilinear : Prop :=
  ∀ (n : ℕ), 1 ≤ n →
    (∀ f : Fin n → D.Torus → ℝ, (∀ i, IsBoundedOnTorus (f i)) → (connectedValue D f).im = 0) ∧
    (∀ (f : Fin n → D.Torus → ℝ) (σ : Equiv.Perm (Fin n)), (∀ i, IsBoundedOnTorus (f i)) →
      connectedValue D (f ∘ σ) = connectedValue D f) ∧
    ∀ (f : Fin n → D.Torus → ℝ) (i : Fin n) (g g' : D.Torus → ℝ) (a a' : ℝ),
      (∀ k, IsBoundedOnTorus (f k)) → IsBoundedOnTorus g → IsBoundedOnTorus g' →
        connectedValue D (Function.update f i (a • g + a' • g')) =
          (a : ℂ) * connectedValue D (Function.update f i g) +
            (a' : ℂ) * connectedValue D (Function.update f i g')
def RestrictionsMultilinearSymm : Prop :=
  ∀ (n : ℕ), 1 ≤ n →
    (torusSide D).IsMultilinearOnLip .torus (restrictLip D n) ∧
      (torusSide D).IsPermInvariant .torus (n := n) (restrictLip D n) ∧
      AmbientPoints.IsTupleMultilinear (restrictSep D n) ∧
      AmbientPoints.IsTupleSymmetric (restrictSep D n)
def MomentEqPartitionSum : Prop :=
  ∀ (q : ℕ) (f : Fin q → D.Torus → ℝ), (∀ l, IsBoundedOnTorus (f l)) →
    (D.latticeMoment (List.ofFn f) : ℂ) =
      ∑ π ∈ SetPartition.singletonFree q, ∏ J ∈ π.parts,
        connectedValue D (AmbientPoints.restrictTuple f J)
def MomentEqCentredMoment : Prop :=
  ∀ (q : ℕ) (f : Fin q → D.Torus → ℝ),
    (∀ l, CutoffNotation.HasFiniteLip D.toStandingParameters (f l)) →
      (D.latticeMoment (List.ofFn f) : ℂ) =
          CutoffNotation.centredMomentFn D.toStandingParameters D.β (fun l x => (f l x : ℂ)) ∧
        (CutoffNotation.DisjointSupports D.toStandingParameters f →
          CutoffNotation.IsCentredMomentArg D.toStandingParameters fun l x => (f l x : ℂ))
def Statement : Prop :=
  ∀ D : ReflectionPositivity.AxisMirror.MirrorData, 8 * 105 ^ 4 ≤ D.L →
    (IsJointCumulant D ∧ IsSchwingerFunction D ∧
        IsLipschitzNumber D ∧
        IsRealSymmMultilinear D ∧
        RestrictionsMultilinearSymm D) ∧
      MomentEqPartitionSum D ∧ MomentEqCentredMoment D
end ToriAtArbitraryCouplings.OneCutoffCumulants
end YangMills.Construction
end
