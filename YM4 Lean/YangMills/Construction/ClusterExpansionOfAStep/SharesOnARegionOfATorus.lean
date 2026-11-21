import YangMills.Construction.ClusterExpansionOfAStep.ConstantsOfTheColdChain
import YangMills.Construction.ClusterExpansionOfAStep.SharesAndCostsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace TorusShares
open BlockAverages TorusFields TorusLumps StepCosts ColdChain
variable {m : ℕ}
def IsLocallyOrthantClosed (X : Finset (TorusSite m)) (k : ℕ) : Prop :=
  ∀ z : TorusSite m, ∃ eps : Fin 4 → ℤ, (∀ i, eps i = 1 ∨ eps i = -1) ∧
    ∀ q ∈ X, supDist q z ≤ k → ∀ h : Fin 4 → ℤ, (∀ i, 0 ≤ eps i * h i) → (∀ i, |h i| ≤ (k : ℤ)) →
      q + siteOfInt h ∈ X
def IsColdOn (X : Finset (TorusSite m)) (s : ℝ) (W : TorusField m) : Prop :=
  ∀ x μ ν, μ < ν → (∀ z ∈ plaquetteVertices x μ ν, z ∈ X) → curvature W x μ ν < s
def RegionsAgreeNear (X X' : Finset (TorusSite m)) (W W' : TorusField m) (y : TorusSite m) (ρ : ℕ) : Prop :=
  2 * ρ + 2 < m ∧ (∀ h, OffsetInBox ρ h → (y + siteOfInt h ∈ X ↔ y + siteOfInt h ∈ X')) ∧
    FieldsAgreeNear W W' y y ρ
open Classical in
def multiplyAtBond (b : TorusBond m) (v : imaginaryQuaternions) (W : TorusField m) : TorusField m :=
  fun x i => if (x, i) = b then expUnit v * W x i else W x i
structure ShareLocality (a : ℝ) (L : ℕ) (s₀ A δ : ℝ) : Prop where
  decay_of_agreement : ∀ (t m : ℕ) [NeZero m] (X X' : Finset (TorusSite m)) (W W' : TorusField m)
    (y : TorusSite m) (ρ : ℕ) (s : ℝ),
    64 ≤ m → 0 < s → s ≤ s₀ → IsLocallyOrthantClosed X 1024 → IsLocallyOrthantClosed X' 1024 →
    IsColdOn X s W → IsColdOn X' s W' →
    RegionsAgreeNear X X' W W' y ρ → |levelShare a L t X y W - levelShare a L t X' y W'| ≤ A * Real.exp (-(δ * ρ))
  twist_bound : ∀ (t m : ℕ) [NeZero m] (X : Finset (TorusSite m)) (W : TorusField m) (b : TorusBond m)
    (v : imaginaryQuaternions) (y : TorusSite m) (s : ℝ),
    64 ≤ m → 0 < s → s ≤ s₀ → IsLocallyOrthantClosed X 1024 →
    (∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 → IsColdOn X s (multiplyAtBond b (τ • v) W)) →
    |levelShare a L t X y (multiplyAtBond b v W) - levelShare a L t X y W| ≤
      A * ‖(v : ℍ[ℝ])‖ * Real.exp (-(δ * supDist y b.1))
def ShareLocalityExists : Prop :=
  ∀ (a δ : ℝ) (L : ℕ) (lam ρ σA cg : ℝ) (N : ℕ → ℝ), 0 < a → Odd L → ColdChainConstants a δ L lam ρ σA cg N →
    ∃ A : ℝ, 0 < A ∧ ShareLocality a L σA A δ
end TorusShares
end YangMills.Construction
end
