import YangMills.Construction.Continuum.AdmissibleSequences
import YangMills.Construction.Continuum.SchwingerFunctionsOfAFunctionalOnSeparatedTuples
import Mathlib
set_option autoImplicit false
open Filter Topology
noncomputable section
namespace YangMills.Construction
namespace ConfigSpace
def IsCLMSequence (S : FlatSequence) : Prop :=
  (∀ c : flatOffDiagonalAt 0, S 0 c = c.1) ∧
    ∀ m : ℕ, IsContLinearOnFlat (S.atSucc m)
def IsEuclidInvariant (S : FlatSequence) : Prop :=
  ∀ (m : ℕ) (φ : schwartzFlatOffDiagonal (m + 1)) (r : EuclidMotion)
    (h : motionAct r φ.1 ∈ schwartzFlatOffDiagonal (m + 1)),
    S.atSucc m ⟨_, h⟩ = S.atSucc m φ
def IsPermSymmetric (S : FlatSequence) : Prop :=
  ∀ (m : ℕ) (φ : schwartzFlatOffDiagonal (m + 1)) (ς : Equiv.Perm (Fin (m + 1)))
    (h : permAct ς φ.1 ∈ schwartzFlatOffDiagonal (m + 1)),
    S.atSucc m ⟨_, h⟩ = S.atSucc m φ
open Classical in
def FlatSequence.evalAt (S : FlatSequence) {n : ℕ} (f : FnOrScalar n) : ℂ :=
  if h : f ∈ flatOffDiagonalAt n then S n ⟨f, h⟩ else 0
theorem FlatSequence.evalAt_of_mem (S : FlatSequence) {n : ℕ}
    {f : FnOrScalar n} (h : f ∈ flatOffDiagonalAt n) : S.evalAt f = S n ⟨f, h⟩ :=
  dif_pos h
def FlatSequence.reflectionPairing (S : FlatSequence)
    (φ ψ : (q : ℕ) → FnOrScalar q) : ℂ :=
  ∑ᶠ p : ℕ × ℕ, S.evalAt (tensorAt (flipConjAt (φ p.1)) (ψ p.2))
def IsOSPositive (S : FlatSequence) : Prop :=
  ∀ Φ : PosTimeSeq, PosTimeSeq.IsFinitelySupported Φ →
    (S.reflectionPairing (fun q => (Φ q).1) fun q => (Φ q).1).im = 0 ∧
      0 ≤ (S.reflectionPairing (fun q => (Φ q).1) fun q => (Φ q).1).re
def HasClusterProperty (S : FlatSequence) : Prop :=
  ∀ Φ Ψ : PosTimeSeq, PosTimeSeq.IsFinitelySupported Φ → PosTimeSeq.IsFinitelySupported Ψ →
    ∀ v ∈ zeroTimeHyperplane, v ≠ 0 →
      Tendsto
        (fun t : ℝ =>
          S.reflectionPairing (fun q => (Φ q).1) fun q => shiftActAt (t • v) (Ψ q).1)
        atTop
        (𝓝 ((∑ᶠ q : ℕ, S.evalAt (flipConjAt (Φ q).1)) *
          ∑ᶠ q : ℕ, S.evalAt (Ψ q).1))
end ConfigSpace
end YangMills.Construction
end
