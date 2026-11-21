import YangMills.Construction.Continuum.FunctionalsOnSeparatedTuples
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TestSpaces
def IsSchwingerAtOrder (σ : SepTuple → ℝ) (n : ℕ)
    (T : flatSchwartzSet n → ℂ) : Prop :=
  (1 ≤ n → IsCLinearOnFlat T ∧ IsWeightedBounded T ∧
    ∀ X : SepTupleOfCard n, HasSmoothComponents Set.univ X.1 →
      ∀ h : tensorProdComplex X.1 ∈ flatSchwartzSet n, T ⟨_, h⟩ = σ ⟨n, X⟩) ∧
  (n = 0 → ∀ (φ : flatSchwartzSet n) (x : PointTuple n), T φ = φ.1 x)
theorem isSchwingerFamily_iff_forall_order (σ : SepTuple → ℝ)
    (T : (n : ℕ) → flatSchwartzSet n → ℂ) :
    IsSchwingerFamily σ T ↔ ∀ n, IsSchwingerAtOrder σ n (T n) := by
  constructor
  · rintro ⟨hpos, hzero⟩ n
    refine ⟨hpos n, ?_⟩
    rintro rfl φ x
    rw [hzero φ]
    exact congrArg φ.1 (funext fun i => i.elim0)
  · intro h
    exact ⟨fun n hn => (h n).1 hn, fun φ => (h 0).2 rfl φ _⟩
def SchwingerUniqueAtEachOrder : Prop :=
  ∀ σ : SepTuple → ℝ, IsSepFunctional σ →
    ∀ (n : ℕ) (T₁ T₂ : flatSchwartzSet n → ℂ),
      IsSchwingerAtOrder σ n T₁ → IsSchwingerAtOrder σ n T₂ → T₁ = T₂
end YangMills.Construction.TestSpaces
