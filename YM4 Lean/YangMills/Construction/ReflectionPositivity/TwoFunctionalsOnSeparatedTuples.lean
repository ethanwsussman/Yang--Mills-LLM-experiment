import YangMills.Construction.ReflectionPositivity.CentredObservableAndFunctionals
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror
namespace MirrorData
variable (D : MirrorData)
def CenteredObservableLinearMeanZero : Prop :=
  (∀ (f h : D.Torus → ℝ) (t : ℝ),
    D.centeredObservable (f + t • h) = D.centeredObservable f + t • D.centeredObservable h) ∧
  ∀ f : D.Torus → ℝ,
    YangMills.Construction.PeriodicLattice.gibbsExpectation D.L D.m D.K D.β
      (D.centeredObservable f) = 0
def LatticeMomentIsSeparated : Prop :=
  (∀ X : List (D.Torus → ℝ),
    Integrable (fun U => (X.map fun f => D.centeredObservable f U).prod)
      (YangMills.Construction.PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.β)) ∧
  D.latticeMoment [] = 1 ∧
  (∀ f : D.Torus → ℝ, D.latticeMoment [f] = 0) ∧
  (∀ (n : ℕ) (f : Fin n → D.Torus → ℝ) (i : Fin n),
    IsLinearMap ℝ fun g : D.Torus → ℝ => D.latticeMoment (List.ofFn (Function.update f i g))) ∧
  Ambient.IsSeparatedFunctional D Ambient.torus fun X => D.latticeMoment X.1
end MirrorData
namespace Ambient.ConnectedFamily
variable {D : MirrorData} {E : Ambient}
def CenteredFunctionalIsSeparated (S : ConnectedFamily D E) : Prop :=
  IsSeparatedFunctional D E S.centeredFunctional ∧
  S.centeredFunctional (emptyList D E) = 1 ∧
  ∀ X : separatedAll D E, X.1.length = 1 → S.centeredFunctional X = 0
end Ambient.ConnectedFamily
def BothFunctionalsSeparated : Prop :=
  ∀ D : MirrorData, D.CenteredObservableLinearMeanZero ∧ D.LatticeMomentIsSeparated ∧
    ∀ (E : Ambient) (S : Ambient.ConnectedFamily D E), S.CenteredFunctionalIsSeparated
end YangMills.Construction.ReflectionPositivity.AxisMirror
