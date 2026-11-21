import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.MatrixLog
abbrev SqMat (N : ℕ) : Type := Matrix (Fin N) (Fin N) ℂ
variable {N : ℕ}
def logTerm (X : SqMat N) (n : ℕ) : SqMat N :=
  ((-1 : ℂ) ^ (n + 2) / ((n : ℂ) + 1)) • (X - 1) ^ (n + 1)
def logOfSeries (X : SqMat N) : SqMat N := ∑' n : ℕ, logTerm X n
structure IsOrthoProjFamily {r : ℕ} (P : Fin r → SqMat N) : Prop where
  star_eq : ∀ j, (P j).conjTranspose = P j
  mul_eq : ∀ j k, P j * P k = if j = k then P j else 0
def IsLogBranch (D : Set ℂ) (ℓ : ℂ → ℂ) : Prop :=
  ∀ z ∈ D, Complex.exp (ℓ z) = z
def IsSpectralLog (D : Set ℂ) (ℓ : ℂ → ℂ) (X L : SqMat N) : Prop :=
  ∃ (r : ℕ) (z : Fin r → ℂ) (P : Fin r → SqMat N), IsOrthoProjFamily P ∧ X = ∑ j, z j • P j ∧
    (∀ j, z j ∈ D) ∧ L = ∑ j, ℓ (z j) • P j
def spectralLog (D : Set ℂ) (ℓ : ℂ → ℂ) (X : SqMat N) : SqMat N :=
  Classical.epsilon (IsSpectralLog D ℓ X)
def principalSpectralLog (X : SqMat N) : SqMat N := spectralLog {0}ᶜ Complex.log X
structure IsUnitarySpectralForm {r : ℕ} (U : SqMat N) (l : Fin r → ℝ) (P : Fin r → SqMat N) :
    Prop where
  proj : IsOrthoProjFamily P
  injective : Function.Injective l
  mem_Ioc : ∀ j, l j ∈ Set.Ioc (-Real.pi) Real.pi
  eq_sum : U = ∑ j, Complex.exp (Complex.I * (l j : ℂ)) • P j
def phaseMatrix {r : ℕ} (l : Fin r → ℝ) (P : Fin r → SqMat N) : SqMat N :=
  ∑ j, (l j : ℂ) • P j
def UnitaryFormUniqueNonzero (N : ℕ) : Prop :=
  ∀ U ∈ Matrix.unitaryGroup (Fin N) ℂ, ∀ (r r' : ℕ) (l : Fin r → ℝ) (l' : Fin r' → ℝ)
    (P : Fin r → SqMat N) (P' : Fin r' → SqMat N),
    IsUnitarySpectralForm U l P → IsUnitarySpectralForm U l' P' →
    (∀ j, P j ≠ 0) → (∀ j, P' j ≠ 0) →
    ∃ σ : Fin r ≃ Fin r', ∀ j, l' (σ j) = l j ∧ P' (σ j) = P j
def MatrixLogarithmsSeriesAndSpectral : Prop :=
  ∀ N : ℕ,
    (∀ X : SqMat N, ‖X - 1‖ < 1 →
      Summable (logTerm X) ∧ NormedSpace.exp (logOfSeries X) = X) ∧
    (∀ Y : SqMat N, ‖Y‖ < Real.log 2 →
      ‖NormedSpace.exp Y - 1‖ < 1 ∧ logOfSeries (NormedSpace.exp Y) = Y) ∧
    AnalyticOnNhd ℂ (NormedSpace.exp : SqMat N → SqMat N) Set.univ ∧
    AnalyticOnNhd ℂ (logOfSeries : SqMat N → SqMat N) {X | ‖X - 1‖ < 1} ∧
    (∀ X : SqMat N, IsStarNormal X →
      ∃ (r : ℕ) (z : Fin r → ℂ) (P : Fin r → SqMat N), IsOrthoProjFamily P ∧ X = ∑ j, z j • P j) ∧
    (∀ (D : Set ℂ) (ℓ : ℂ → ℂ), IsLogBranch D ℓ →
      ∀ X : SqMat N, IsStarNormal X → ∀ (r : ℕ) (z : Fin r → ℂ) (P : Fin r → SqMat N),
        IsOrthoProjFamily P → X = ∑ j, z j • P j → (∀ j, z j ∈ D) →
        spectralLog D ℓ X = ∑ j, ℓ (z j) • P j) ∧
    (∀ U ∈ Matrix.unitaryGroup (Fin N) ℂ,
      ∃ (r : ℕ) (l : Fin r → ℝ) (P : Fin r → SqMat N), IsUnitarySpectralForm U l P ∧ ∀ j, P j ≠ 0) ∧
    UnitaryFormUniqueNonzero N ∧
    (∀ U ∈ Matrix.unitaryGroup (Fin N) ℂ, ∀ (r : ℕ) (l : Fin r → ℝ) (P : Fin r → SqMat N),
      IsUnitarySpectralForm U l P →
        principalSpectralLog U = Complex.I • phaseMatrix l P ∧ (phaseMatrix l P).IsHermitian ∧
          ‖phaseMatrix l P‖ ≤ Real.pi)
end YangMills.Construction.MatrixLog
end
