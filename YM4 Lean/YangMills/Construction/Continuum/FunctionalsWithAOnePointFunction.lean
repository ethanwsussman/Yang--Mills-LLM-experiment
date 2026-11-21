import YangMills.Construction.Continuum.FunctionalsOnSeparatedTuples
import YangMills.Construction.Continuum.TensorProductsAndIntegrationOverArguments
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.TestSpaces
open Classical in
def evalOrZero {p : ℕ} (T : flatSchwartzSet p → ℂ) (g : PointTuple p → ℂ) : ℂ :=
  if h : g ∈ flatSchwartzSet p then T ⟨g, h⟩ else 0
def schwingerFromCentred (c : ℝ) (T : (p : ℕ) → flatSchwartzSet p → ℂ) (n : ℕ)
    (φ : flatSchwartzSet n) : ℂ :=
  ∑ A ∈ (Finset.univ : Finset (Fin n)).ssubsets,
      (c : ℂ) ^ A.card * evalOrZero (T (n - A.card)) (integrateOut A φ.1) +
    (c : ℂ) ^ n * ∫ x, φ.1 x
def onePointConst (k : ℕ) (C cBar : ℝ) : ℝ := C + cBar * (weightIntegral k).toReal
def OnePointFunctional.growth : Prop :=
  ∀ (k : ℕ) (κ a C cBar c : ℝ) (σ : SepTuple → ℝ)
    (T : (p : ℕ) → flatSchwartzSet p → ℂ),
    4 < k → 0 ≤ κ → 0 ≤ a → 0 ≤ C → 0 ≤ cBar →
    IsSepFunctional σ →
    (∀ X : SepTupleOfCard 1, cumulant σ X = c * ∫ u, X.1 0 u) →
    |c| ≤ cBar →
    IsSchwingerFamily (centredPart σ) T →
    (∀ p, 1 ≤ p → ∀ φ : flatSchwartzSet p,
      ENNReal.ofReal ‖T p φ‖ ≤
        ENNReal.ofReal (a * C ^ p * (p.factorial : ℝ) ^ κ) * weightedSeminorm (k * p) φ.1) →
    (∀ n, 1 ≤ n →
      (∀ φ : flatSchwartzSet n, Integrable φ.1 ∧
        ∀ A ∈ (Finset.univ : Finset (Fin n)).ssubsets,
          integrableFibers A φ.1 = Set.univ ∧
            integrateOut A φ.1 ∈ flatSchwartzSet (n - A.card)) ∧
      IsCLinearOnFlat (schwingerFromCentred c T n) ∧
      (∀ X : SepTupleOfCard n, HasSmoothComponents Set.univ X.1 →
        ∀ h : tensorProdComplex X.1 ∈ flatSchwartzSet n,
          schwingerFromCentred c T n ⟨_, h⟩ = σ ⟨n, X⟩) ∧
      ∀ φ : flatSchwartzSet n,
        ENNReal.ofReal ‖schwingerFromCentred c T n φ‖ ≤
          ENNReal.ofReal ((1 + a) * onePointConst k C cBar ^ n *
            (n.factorial : ℝ) ^ κ) * weightedSeminorm (k * n) φ.1) ∧
    GrowthBound k (1 + a) (onePointConst k C cBar) κ σ
end YangMills.Construction.TestSpaces
end
