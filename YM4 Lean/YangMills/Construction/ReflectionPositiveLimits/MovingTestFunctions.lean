import YangMills.Construction.ReflectionPositiveLimits.MirrorsAndReflectionPositivityOfAFunctional
import Mathlib
set_option autoImplicit false
open Filter Set Topology
noncomputable section
namespace YangMills.Construction.ReflectionPositivity
open TorusMetric (euclidNormVec)
def EuclidIsometry.comp (r s : EuclidIsometry) : EuclidIsometry where
  toFun := r.toFun ∘ s.toFun
  preserves_dist x y := by
    simp only [Function.comp_apply]
    rw [r.preserves_dist, s.preserves_dist]
theorem Concatenable.symm {X Y : Tuple} (hXY : Concatenable X Y) :
    Concatenable Y X :=
  fun g hg f hf => (hXY f hf g hg).symm
def concatOrNil (X Y : Tuple) : Tuple :=
  open Classical in
  if hXY : Concatenable X Y then concat X Y hXY else nilTuple
def NormalMirror.atOffset (M : NormalMirror) (b : ℝ) : NormalMirror :=
  ⟨M.normal, b, M.normal_mem⟩
def NormalMirror.shiftVec (M : NormalMirror) (b : ℝ) : Space :=
  (2 * (b - M.offset) / euclidNormVec M.normal ^ 2) • M.normal
def IsometryActsOnTuples : Prop :=
  ∀ (X Y : Tuple) (r s : EuclidIsometry),
    push (r.comp s) X = push r (push s X) ∧
    (push r X).1.map tsupport = X.1.map (fun f => r.toFun '' tsupport f) ∧
    ∀ hXY : Concatenable X Y, ∃ hrXY : Concatenable (push r X) (push r Y),
      concat (push r X) (push r Y) hrXY = push r (concat X Y hXY)
def TranslateConcatTendsto : Prop :=
  ∀ (X Y : Tuple) (w : ℕ → Space) (v : Space), Tendsto w atTop (𝓝 v) →
    ∀ hYX : Concatenable Y (push (EuclidIsometry.translate v) X),
      ∃ k₀ : ℕ, 1 ≤ k₀ ∧
        (∀ k, k₀ ≤ k → Concatenable Y (push (EuclidIsometry.translate (w k)) X) ∧
          Concatenable (push (EuclidIsometry.translate (w k)) X) Y) ∧
        AdmissiblyTendsto k₀
          (fun k => concatOrNil Y (push (EuclidIsometry.translate (w k.toNat)) X))
          (concat Y (push (EuclidIsometry.translate v) X) hYX) ∧
        AdmissiblyTendsto k₀
          (fun k => concatOrNil (push (EuclidIsometry.translate (w k.toNat)) X) Y)
          (concat (push (EuclidIsometry.translate v) X) Y hYX.symm)
def TranslateTendsto : Prop :=
  ∀ (X : Tuple) (w : ℕ → Space) (v : Space), Tendsto w atTop (𝓝 v) →
    ∃ k₀ : ℕ, 1 ≤ k₀ ∧
      AdmissiblyTendsto k₀ (fun k => push (EuclidIsometry.translate (w k.toNat)) X)
        (push (EuclidIsometry.translate v) X)
def ReflectConcatTendsto : Prop :=
  ∀ (M : NormalMirror) (X₁ X₂ : Tuple) (h₁ : X₁ ∈ tuplesSupportedIn M.posSide)
    (h₂ : X₂ ∈ tuplesSupportedIn M.posSide) (b : ℕ → ℝ),
    (∀ k, 1 ≤ k → b k ≤ M.offset) → Tendsto b atTop (𝓝 M.offset) →
      (∀ k, 1 ≤ k → (M.atOffset (b k)).reflectIso.toFun =
        (EuclidIsometry.translate (M.shiftVec (b k))).toFun ∘ M.reflectIso.toFun) ∧
      Tendsto (fun k => M.shiftVec (b k)) atTop (𝓝 0) ∧
      (∀ k, 1 ≤ k →
        push (M.atOffset (b k)).reflectIso X₁ ∈
          tuplesSupportedIn {x | euclidInner M.normal x < 2 * b k - M.offset} ∧
        {x | euclidInner M.normal x < 2 * b k - M.offset} ⊆
          {x | euclidInner M.normal x < M.offset} ∧
        Concatenable (push (M.atOffset (b k)).reflectIso X₁) X₂) ∧
      ∃ k₀ : ℕ, 1 ≤ k₀ ∧
        AdmissiblyTendsto k₀
          (fun k => concatOrNil (push (M.atOffset (b k.toNat)).reflectIso X₁) X₂)
          (concat (push M.reflectIso X₁) X₂ (NormalMirror.concatenable_reflectIso h₁ h₂))
def MovingTestFunctions.statement : Prop :=
  IsometryActsOnTuples ∧ TranslateConcatTendsto ∧ TranslateTendsto ∧ ReflectConcatTendsto
end YangMills.Construction.ReflectionPositivity
