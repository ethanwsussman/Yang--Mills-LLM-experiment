import YangMills.Construction.InfiniteLattice.IsometriesOfTheUnitLattice
import YangMills.Construction.InfiniteLattice.LatticeOfACutoffItsIsometriesAndTimeReflections
import YangMills.Construction.InfiniteLattice.ObservablesAndIsometriesAtOneSpacing
import YangMills.Construction.InfiniteLattice.StandingConventionsOfMultipleReflections
import YangMills.Construction.InfiniteLattice.TransferOperatorWithAnInsertion
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
variable {a : ℝ}
def spacingMultiples (a : ℝ) : Set ℝ := {w | ∃ n : ℤ, w = (n : ℝ) * a}
def timeAxisPoint (w : spacingMultiples a) : LatticePoint a :=
  ⟨Pi.single timeAxis (w : ℝ), by
    obtain ⟨n, hn⟩ := w.2
    refine ⟨Pi.single timeAxis n, fun μ => ?_⟩
    by_cases h : μ = timeAxis
    · subst h
      simp [hn]
    · simp [Pi.single_eq_of_ne h]⟩
def doubledTimeGap (s s' : halfSpacingTimes a) : spacingMultiples a :=
  ⟨2 * ((s : ℝ) - s'), by
    obtain ⟨q, hq⟩ := s.2
    obtain ⟨q', hq'⟩ := s'.2
    exact ⟨q - q', by rw [hq, hq']; push_cast; ring⟩⟩
def halfTimeAdd (s : halfSpacingTimes a) (w : spacingMultiples a) : halfSpacingTimes a :=
  ⟨(s : ℝ) + w, by
    obtain ⟨q, hq⟩ := s.2
    obtain ⟨n, hn⟩ := w.2
    exact ⟨q + 2 * n, by rw [hq, hn]; push_cast; ring⟩⟩
namespace LatticeSymmetry
def MulIsIdentity (g h : LatticeSymmetry a) : Prop :=
  (g * h).toFun = id ∧
    ∀ A : GaugeField a → ℂ, IsBoundedObservable A → g.actOn (h.actOn A) = A
def MulEq (g h k : LatticeSymmetry a) : Prop :=
  (g * h).toFun = k.toFun ∧
    ∀ A : GaugeField a → ℂ, IsBoundedObservable A →
      g.actOn (h.actOn A) = k.actOn A
def MulEqMul (g h k l : LatticeSymmetry a) : Prop :=
  (g * h).toFun = (k * l).toFun ∧
    ∀ A : GaugeField a → ℂ, IsBoundedObservable A →
      g.actOn (h.actOn A) = k.actOn (l.actOn A)
def MapsSmearedEnergy {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    (g : LatticeSymmetry a) (f : AmbientSpace → E) : Prop :=
  IsBoundedBorelCompactlySupported f → IsBoundedBorelCompactlySupported (g.pushforwardFun f) ∧
    g.actOn (smearedEnergy f) = smearedEnergy (g.pushforwardFun f)
end LatticeSymmetry
end InfiniteLattice
namespace MultipleReflections.SymmetriesOnFacesAndReflectionIdentities
open InfiniteLattice InfiniteLattice.LatticeSymmetry
def Statement : Prop :=
  ∀ D : Setup,
    (∀ g : D.LatticeSymmetry,
      (∀ p : ElementaryPlaquette D.mesh,
        (∃! q : ElementaryPlaquette D.mesh, q.closedSquare = g.mapSquare p) ∧
        ∀ q : ElementaryPlaquette D.mesh, q.closedSquare = g.mapSquare p →
          g.actOn (fun U : D.GaugeField => faceEnergy U p) =
            fun U : D.GaugeField => faceEnergy U q) ∧
      (∀ f : AmbientSpace → ℝ, g.MapsSmearedEnergy f) ∧
      ∀ f : AmbientSpace → ℂ, g.MapsSmearedEnergy f) ∧
    (∀ (t : halfSpacingTimes D.mesh) (u : positiveMultiples D.mesh),
      (t : ℝ) + (u : ℝ) / 2 ∈ halfSpacingTimes D.mesh ∧
      MulEq (timeReflect (midpointTime t u)) (timeReflect t) (shift (timeStep u)) ∧
      MulEq (timeReflect (midpointTime t u)) (shift (timeStep u)) (timeReflect t)) ∧
    ∀ (s s' : halfSpacingTimes D.mesh) (w : spacingMultiples D.mesh),
      MulIsIdentity (timeReflect s) (timeReflect s) ∧
      MulEq (timeReflect s) (timeReflect s')
        (shift (timeAxisPoint (doubledTimeGap s s'))) ∧
      MulEqMul (timeReflect s) (shift (timeAxisPoint w))
        (shift (-timeAxisPoint w)) (timeReflect s) ∧
      MulEqMul (timeReflect (halfTimeAdd s w)) (shift (timeAxisPoint w))
        (shift (timeAxisPoint w)) (timeReflect s)
end MultipleReflections.SymmetriesOnFacesAndReflectionIdentities
end YangMills.Construction
end
