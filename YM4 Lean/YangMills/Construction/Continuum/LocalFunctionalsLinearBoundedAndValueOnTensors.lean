import YangMills.Construction.Continuum.FormsBoundedOnSeparatedBalls
import YangMills.Construction.Continuum.LocalFunctionalsOfAForm
import Mathlib
set_option autoImplicit false
open Filter Topology
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.ConfigSpace.LocalPairingProps
variable {n : ℕ}
def SupportedClassIsSubmodule (Q : PointSystem n) : Prop :=
  ∃ S : Submodule ℂ (Config n → ℂ), (S : Set (Config n → ℂ)) = Q.supportedClass
def PairingIsComplexLinear (T : smoothRealTupleSet n → ℝ) (Q : PointSystem n) : Prop :=
  (∀ F ∈ Q.supportedClass, ∀ H ∈ Q.supportedClass,
    localPairing T Q (F + H) = localPairing T Q F + localPairing T Q H) ∧
  ∀ (w : ℂ), ∀ F ∈ Q.supportedClass, localPairing T Q (w • F) = w * localPairing T Q F
def PairingBoundedByScaledNorm (c : ℝ) (a : ℕ) (G : ℝ) (T : smoothRealTupleSet n → ℝ)
    (Q : PointSystem n) : Prop :=
  ∀ F ∈ Q.supportedClass, ‖localPairing T Q F‖ ≤
    localConst ^ n * max 1 c ^ n * G * max 1 (Q.boxGap.toReal ^ (-(a : ℤ))) *
      Q.scale ^ (-(n : ℤ)) * scaledSupNorm (5 * n + 1) Q.scale F
def PairingContinuousInScaledNorm (T : smoothRealTupleSet n → ℝ) (Q : PointSystem n) : Prop :=
  ∀ (F : Config n → ℂ) (Fs : ℝ → Config n → ℂ), F ∈ Q.supportedClass →
    (∀ t, 0 < t → Fs t ∈ Q.supportedClass) →
    Tendsto (fun t => scaledSupNorm (5 * n + 1) Q.scale (Fs t - F)) atTop (𝓝 0) →
    Tendsto (fun t => localPairing T Q (Fs t)) atTop (𝓝 (localPairing T Q F))
def PairingOnTensors (T : smoothRealTupleSet n → ℝ) (Q : PointSystem n) : Prop :=
  ∀ φ : FnTuple n, (∀ i, ContDiff ℝ ∞ (φ i)) → (∀ i, tsupport (φ i) ⊆ Q.midBox i) →
    ∃ h : φ ∈ smoothComplexTupleSet n,
      tensorProd φ ∈ Q.supportedClass ∧ localPairing T Q (tensorProd φ) = complexify T ⟨φ, h⟩
def LocalPairingProperties : Prop :=
  ∀ (n : ℕ) (c : ℝ) (a : ℕ) (G : ℝ) (T : smoothRealTupleSet n → ℝ) (Q : PointSystem n),
    SeparatedBallBound c a G T → Q.IsSeparated →
      SupportedClassIsSubmodule Q ∧ PairingIsComplexLinear T Q ∧ 1 ≤ localConst ∧
        PairingBoundedByScaledNorm c a G T Q ∧ PairingContinuousInScaledNorm T Q ∧
          PairingOnTensors T Q
end YangMills.Construction.ConfigSpace.LocalPairingProps
