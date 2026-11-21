import YangMills.Construction.Continuum.LocalFunctionalsOfAForm
import Mathlib
set_option autoImplicit false
open Filter
open scoped Matrix Topology
noncomputable section
namespace YangMills.Construction
namespace ConfigSpace
variable {n : ℕ}
namespace PointSystem
variable (Q : PointSystem n)
def freqsWithin (t : ℝ) : Set (Config n) := {ξ | ξ ∈ Q.freqLattice ∧ coordSupNorm ξ ≤ t}
def truncatedSum (Φ : Config n → ℂ) (t : ℝ) : Config n → ℂ := fun x =>
  ∑ᶠ ξ ∈ Q.freqsWithin t, Q.fourierCoeff Φ ξ * tensorProd (Q.modeFamily ξ) x
def sepWeight (a : ℕ) : ℝ := max 1 (Q.boxGap.toReal ^ (-(a : ℤ)))
def CoeffDecay (Φ : Config n → ℂ) : Prop :=
  ∀ (ν : ℕ), ∀ ξ ∈ Q.freqLattice,
    (1 + Q.scale * coordSupNorm ξ) ^ ν * ‖Q.fourierCoeff Φ ξ‖ ≤ 2 ^ ν * scaledSupNorm ν Q.scale Φ
def ModesLocalCharacters : Prop :=
  ∀ (i : Fin n), ∀ ξ ∈ Q.freqLattice,
    Q.modeFun i ξ ∈ SmoothMaps.smoothCompactSet (Fin 4 → ℝ) ∧ tsupport (Q.modeFun i ξ) ⊆ Q.outerBox i ∧
      ∀ y ∈ Q.midBox i,
        Q.modeFun i ξ y = Complex.exp (Complex.I * ((ξ i ⬝ᵥ (y - Q.base i) : ℝ)))
def HasFourierExpansion (Φ : Config n → ℂ) : Prop :=
  ∀ x : Config n,
    Summable (fun ξ : Q.freqLattice => ‖Q.fourierCoeff Φ ξ * ∏ i, Q.modeFun i ξ (x i)‖) ∧
      Φ x = ∑' ξ : Q.freqLattice, Q.fourierCoeff Φ ξ * ∏ i, Q.modeFun i ξ (x i)
def TruncationsConverge (Φ : Config n → ℂ) : Prop :=
  (∀ t : ℝ, 0 < t → (Q.freqsWithin t).Finite ∧
    tsupport (Q.truncatedSum Φ t) ⊆ cylinderSet Q.outerBox) ∧
  ∀ ν : ℕ, Tendsto (fun t : ℝ => scaledSupNorm ν Q.scale (Φ - Q.truncatedSum Φ t)) atTop (𝓝 0)
def ModeBounds (c : ℝ) (a : ℕ) (G : ℝ) (T : smoothRealTupleSet n → ℝ) : Prop :=
  ∀ ξ ∈ Q.freqLattice,
    Q.modeFamily ξ ∈ smoothComplexTupleSet n ∧
    (∀ i, max (TestFunctions.uniformNorm (Q.modeFun i ξ)) (c * gradSupNorm (Q.modeFun i ξ)) ≤
      modeConst * max 1 c * Q.scale⁻¹ * (1 + Q.scale * coordSupNorm ξ)) ∧
    ‖complexifyAtModes T Q ξ‖ ≤
      (2 * modeConst) ^ n * max 1 c ^ n * Q.scale ^ (-(n : ℤ)) *
        (1 + Q.scale * coordSupNorm ξ) ^ n * G * Q.sepWeight a
def CoeffCostSummable (Φ : Config n → ℂ) (c : ℝ) (a : ℕ) (G : ℝ)
    (T : smoothRealTupleSet n → ℝ) : Prop :=
  Summable (fun ξ : Q.freqLattice => ‖Q.fourierCoeff Φ ξ‖ * ‖complexifyAtModes T Q ξ‖) ∧
    ∑' ξ : Q.freqLattice, ‖Q.fourierCoeff Φ ξ‖ * ‖complexifyAtModes T Q ξ‖ ≤
      2 ^ (5 * n + 1) * (1 + 8 * (n : ℝ)) * (2 * modeConst) ^ n * max 1 c ^ n * G *
        Q.sepWeight a * Q.scale ^ (-(n : ℤ)) * scaledSupNorm (5 * n + 1) Q.scale Φ
end PointSystem
def IntegerLatticeSumBound (n : ℕ) : Prop :=
  Summable (fun ζ : Fin n → Fin 4 → ℤ =>
    (1 + Real.pi * coordSupNorm (fun i k => (ζ i k : ℝ))) ^ (-(4 * (n : ℤ)) - 1)) ∧
  ∑' ζ : Fin n → Fin 4 → ℤ,
    (1 + Real.pi * coordSupNorm (fun i k => (ζ i k : ℝ))) ^ (-(4 * (n : ℤ)) - 1) ≤ 1 + 8 * (n : ℝ)
end ConfigSpace
end YangMills.Construction
