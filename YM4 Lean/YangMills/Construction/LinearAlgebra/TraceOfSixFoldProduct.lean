import YangMills.Construction.Conventions.RealPowerAndLogarithm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate ComplexOrder
namespace YangMills.Construction.TraceBound
open YangMills.Construction.RealPower
section Definitions
variable {E : Type} [AddCommGroup E] [Module ℂ E]
structure IsHermitianForm (h : E → E → ℂ) : Prop where
  linear_right : ∀ v, IsLinearMap ℂ (h v)
  conj_symm : ∀ v w, h w v = conj (h v w)
  pos : ∀ v, v ≠ 0 → 0 < h v v
def formNorm (h : E → E → ℂ) (v : E) : ℝ :=
  sqrtOf (h v v).re
def opNormE (h : E → E → ℂ) (T : Module.End ℂ E) : EReal :=
  sSup ((fun v => ((formNorm h (T v) : ℝ) : EReal)) '' {v | formNorm h v ≤ 1})
def IsOrthonormalFamily {ι : Type} [Finite ι] (h : E → E → ℂ) (x : ι → E) : Prop :=
  (∀ i, h (x i) (x i) = 1) ∧ ∀ i k, i ≠ k → h (x i) (x k) = 0
def IsOrthonormalBasisOf {ι : Type} [Finite ι] (h : E → E → ℂ) (x : ι → E) : Prop :=
  (∃ b : Module.Basis ι ℂ E, ⇑b = x) ∧ IsOrthonormalFamily h x
def IsAdjointOf (h : E → E → ℂ) (T T' : Module.End ℂ E) : Prop :=
  ∀ v w, h (T' v) w = h v (T w)
def HasUniqueAdjoint (h : E → E → ℂ) (T : Module.End ℂ E) : Prop :=
  ∃! T' : Module.End ℂ E, IsAdjointOf h T T'
def adjointOf (h : E → E → ℂ) (T : Module.End ℂ E) : Module.End ℂ E :=
  Classical.epsilon (IsAdjointOf h T)
variable [FiniteDimensional ℂ E]
def adjointMulEigenvalues (h : E → E → ℂ) (T : Module.End ℂ E) : Multiset ℂ :=
  (LinearMap.charpoly (adjointOf h T * T)).roots
def HasSingularValues (h : E → E → ℂ) (T : Module.End ℂ E) : Prop :=
  HasUniqueAdjoint h T ∧ ∀ μ ∈ adjointMulEigenvalues h T, μ.im = 0 ∧ 0 ≤ μ.re
def singularValuesOf (h : E → E → ℂ) (T : Module.End ℂ E) : Multiset ℝ :=
  (adjointMulEigenvalues h T).map fun μ => sqrtOf μ.re
def sumCubesSingularValues (h : E → E → ℂ) (T : Module.End ℂ E) : ℝ :=
  ((singularValuesOf h T).map fun s => rpowPos s 3).sum
def HasSchattenThreeNorm (h : E → E → ℂ) (T : Module.End ℂ E) : Prop :=
  HasSingularValues h T ∧ 0 ≤ sumCubesSingularValues h T
def schattenThreeNorm (h : E → E → ℂ) (T : Module.End ℂ E) : ℝ :=
  cbrtOf (sumCubesSingularValues h T)
end Definitions
def TraceSixFoldProductBound : Prop :=
  ∀ n : ℕ, 1 ≤ n →
  ∀ (E : Type) [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E],
    Module.finrank ℂ E = n →
  ∀ h : E → E → ℂ, IsHermitianForm h →
    (∀ T : Module.End ℂ E,
      HasUniqueAdjoint h T ∧
      (∃ r : ℝ, opNormE h T = r) ∧
      (∀ μ ∈ adjointMulEigenvalues h T, μ.im = 0 ∧ 0 ≤ μ.re) ∧
      HasSingularValues h T ∧
      Multiset.card (singularValuesOf h T) = n ∧
      HasSchattenThreeNorm h T) ∧
    (∀ (T : Module.End ℂ E) (e : Fin n → E) (d : Fin n → ℂ),
      IsOrthonormalBasisOf h e → (∀ i, T (e i) = d i • e i) →
        singularValuesOf h T = Finset.univ.val.map (fun i => ‖d i‖) ∧
        rpowPos (schattenThreeNorm h T) 3 = ∑ i, rpowPos ‖d i‖ 3) ∧
    (∀ A₁ A₂ A₃ B₁ B₂ B₃ : Module.End ℂ E,
      ((‖LinearMap.trace ℂ E (A₁ * B₁ * A₂ * B₂ * A₃ * B₃)‖ : ℝ) : EReal) ≤
          ((schattenThreeNorm h A₁ * schattenThreeNorm h A₂ * schattenThreeNorm h A₃ : ℝ) : EReal) *
            opNormE h B₁ * opNormE h B₂ * opNormE h B₃ ∧
      ((schattenThreeNorm h A₁ * schattenThreeNorm h A₂ * schattenThreeNorm h A₃ : ℝ) : EReal) *
            opNormE h B₁ * opNormE h B₂ * opNormE h B₃ ≤
          ((1 / 3 * (rpowPos (schattenThreeNorm h A₁) 3 + rpowPos (schattenThreeNorm h A₂) 3 +
              rpowPos (schattenThreeNorm h A₃) 3) : ℝ) : EReal) *
            opNormE h B₁ * opNormE h B₂ * opNormE h B₃)
end YangMills.Construction.TraceBound
