import YangMills.Construction.ClusterExpansionOfAStep.ClassesOfTwoGrounds
import YangMills.Construction.ClusterExpansionOfAStep.ComparisonOfTwoGases
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory Dobrushin TorusFields TorusLumps StepSettings
namespace StepGas
variable {R : StepSetup} {n n' : ℕ} [NeZero n] [NeZero n']
structure GasGround.IsInnerSpin (G : GasGround R n) (Y : TorusSite n) (m : ℕ) (A : Finset (TorusSite n))
    (i : G.GasSpin) : Prop where
  not_touches : ¬ i.1.Touches A
  core_near : ∀ y ∈ i.1.core, ∃ h, OffsetInBox m h ∧ y = Y + siteOfInt h
abbrev GasGround.InnerSpin (G : GasGround R n) (Y : TorusSite n) (m : ℕ) (A : Finset (TorusSite n)) : Type :=
  {i : G.GasSpin // G.IsInnerSpin Y m A i}
def GasGround.occupied (G : GasGround R n) (i : G.GasSpin) (s : G.SpinState i) : G.SpinValue i := Sum.inr s
set_option genSizeOf false in
set_option genInjectivity false in
set_option maxHeartbeats 1000000 in
structure SharedInnerGas (G : GasGround R n) (G' : GasGround R n') (Y : TorusSite n) (Y' : TorusSite n') (N m : ℕ)
    (A : Finset (TorusSite n)) (A' : Finset (TorusSite n')) where
  spinEquiv : G.InnerSpin Y m A ≃ G'.InnerSpin Y' m A'
  valueEquiv : ∀ j : G.InnerSpin Y m A, G.SpinValue j.1 ≃ᵐ G'.SpinValue (spinEquiv j).1
  sameSupport : ∀ j : G.InnerSpin Y m A, SameSupportNear j.1.1 (spinEquiv j).1.1 Y Y' N
  meets_iff : ∀ j : G.InnerSpin Y m A, j.1.1.Meets Y ↔ (spinEquiv j).1.1.Meets Y'
  unitCount_eq : ∀ j : G.InnerSpin Y m A,
    supportUnitCount R.params.side R.range j.1.1 = supportUnitCount R.params.side R.range (spinEquiv j).1.1
  map_vacant : ∀ j : G.InnerSpin Y m A,
    valueEquiv j (Sum.inl () : G.SpinValue j.1) = (Sum.inl () : G'.SpinValue (spinEquiv j).1)
  map_occupied : ∀ (j : G.InnerSpin Y m A) (s : G.SpinState j.1), ∃ s' : G'.SpinState (spinEquiv j).1,
    valueEquiv j (G.occupied j.1 s) = G'.occupied (spinEquiv j).1 s' ∧
      SameStateNear j.1.1 (spinEquiv j).1.1 s.1 s'.1 Y Y' N
  farApart_iff : ∀ j j' : G.InnerSpin Y m A, j ≠ j' →
    (j.1.1.FarApart j'.1.1 ↔ (spinEquiv j).1.1.FarApart (spinEquiv j').1.1)
  measurePreserving : ∀ j : G.InnerSpin Y m A,
    MeasurePreserving (valueEquiv j) (withNoneMeasure (G.spinStateMeasure j.1))
      (withNoneMeasure (G'.spinStateMeasure (spinEquiv j).1))
variable {G : GasGround R n} {G' : GasGround R n'} {Y : TorusSite n} {Y' : TorusSite n'} {N m : ℕ}
  {A : Finset (TorusSite n)} {A' : Finset (TorusSite n')}
abbrev SharedInnerGas.Config (_ : SharedInnerGas G G' Y Y' N m A A') : Type :=
  ∀ j : G.InnerSpin Y m A, G.SpinValue j.1
def SharedInnerGas.extendFirst (g : SharedInnerGas G G' Y Y' N m A A') (τ : g.Config) : G.Config :=
  G.pairConstraint.embedConfig Subtype.val (fun _ s => s) τ
def SharedInnerGas.extendSecond (g : SharedInnerGas G G' Y Y' N m A A') (τ : g.Config) : G'.Config :=
  G'.pairConstraint.embedConfig (fun j => (g.spinEquiv j).1) (fun j => g.valueEquiv j) τ
def GasGround.coreOffsets (G : GasGround R n) (Y : TorusSite n) (m : ℕ) (i : G.GasSpin) : Finset (Fin 4 → ℤ) :=
  open Classical in
  (Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(m : ℤ)) (m : ℤ)).filter fun h => Y + siteOfInt h ∈ i.1.core
end StepGas
end YangMills.Construction
end
