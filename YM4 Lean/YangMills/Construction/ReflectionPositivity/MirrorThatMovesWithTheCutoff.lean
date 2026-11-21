import YangMills.Construction.ReflectionPositivity.InstancesOfTheInequalityAtAMirror
import YangMills.Construction.ReflectionPositivity.SequencesOfLatticeDataAndTheirLimits
import Mathlib
set_option autoImplicit false
open Filter
open scoped ComplexConjugate Topology
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror.MovingMirror
open Ambient
variable {D : MirrorData}
def meshOf {E : Ambient} (S : LatticeDataSeq D E) (j : ℕ+) : ℝ :=
  PeriodicLattice.meshSize D.L (S.K j : ℕ)
def IsNearLinkLevel {E : Ambient} (S : LatticeDataSeq D E) (c : ℝ) (j : ℕ+) (c' : ℝ) : Prop :=
  c' ∈ LimitSpaces.halfShiftedMultiplesOf (meshOf S j) ∧ |c' - c| ≤ 1 / 2 * meshOf S j
def dataAt {E : Ambient} (S : LatticeDataSeq D E) (j : ℕ+) : MirrorData :=
  ⟨S.standingAt j, S.β j, S.β_pos j⟩
def ElementsInOpenSlab :
    {E : Ambient} → LatticeDataSeq D E → ℕ+ → CoordMirror → FnList D E → Prop
  | torus, _, _, _, _ => True
  | euclidean, S, j, P, X =>
    ∀ g ∈ S.listAt j X,
      closedSupport (dataAt S j) torus g ⊆ P.upperSide (dataAt S j) torus
def reflectedGram {E : Ambient} (S : LatticeDataSeq D E) {P₀ : CoordMirror}
    (I : P₀.PositivityInstance D E) (P : CoordMirror) (j : ℕ+) : ℂ :=
  ∑ i, ∑ k, conj (I.coeffs i) * I.coeffs k *
    ((S.centredAt j (P.reflectAppend D E (I.tuples i).1 (I.tuples k).1) : ℝ) : ℂ)
def EventuallyPositive {E : Ambient} (S : LatticeDataSeq D E) (μ : Fin 4) (c : ℝ)
    (cj : ℕ+ → ℝ) : Prop :=
  ∀ I : (CoordMirror.mk μ c).PositivityInstance D E, ∀ᶠ j in atTop,
    I.suppUnion ⊆ (CoordMirror.mk μ (cj j)).upperSide D E ∧
    (∀ i, ElementsInOpenSlab S j (CoordMirror.mk μ (cj j)) (I.tuples i).1) ∧
    (reflectedGram S I (CoordMirror.mk μ (cj j)) j).im = 0 ∧
    0 ≤ (reflectedGram S I (CoordMirror.mk μ (cj j)) j).re
def TendsAlongMovingMirror {E : Ambient} (S : LatticeDataSeq D E)
    (T : FunctionalFamily D E) (μ : Fin 4) (c : ℝ) (cj : ℕ+ → ℝ) : Prop :=
  ∀ X Y : separatedWithin D E ((CoordMirror.mk μ c).upperSide D E),
    (∀ᶠ j in atTop, S.ReadsAt j ((CoordMirror.mk μ (cj j)).reflectAppend D E X.1 Y.1)) ∧
    Tendsto (fun j => S.centredAt j ((CoordMirror.mk μ (cj j)).reflectAppend D E X.1 Y.1))
      atTop (𝓝 (evalOrZero (FunctionalFamily.centeredFunctional T)
        ((CoordMirror.mk μ c).reflectAppend D E X.1 Y.1)))
def MovingMirrorLimit : Prop :=
  ∀ (D : MirrorData) (E : Ambient) (S : LatticeDataSeq D E) (T : FunctionalFamily D E),
    S.TendsToFamily T → ∀ (μ : Fin 4) (c : ℝ),
      (∀ j, ∃ c', IsNearLinkLevel S c j c') ∧
      ∀ cj : ℕ+ → ℝ, (∀ j, IsNearLinkLevel S c j (cj j)) →
        EventuallyPositive S μ c cj ∧
        TendsAlongMovingMirror S T μ c cj ∧
        ∀ I : (CoordMirror.mk μ c).PositivityInstance D E,
          I.HoldsReal (FunctionalFamily.centeredFunctional T)
end YangMills.Construction.ReflectionPositivity.AxisMirror.MovingMirror
end
