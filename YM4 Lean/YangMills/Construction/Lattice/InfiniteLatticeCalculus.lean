import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
def l1Length {d : ℕ} (v : Fin d → ℝ) : ℝ := ∑ μ, |v μ|
def supLength {d : ℕ} (v : Fin d → ℝ) : ℝ := ⨆ μ, |v μ|
def gridSubgroup (d : ℕ) (a : ℝ) : AddSubgroup (Fin d → ℝ) where
  carrier := {x | ∃ n : Fin d → ℤ, ∀ μ, x μ = (n μ : ℝ) * a}
  add_mem' := by
    rintro x y ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, fun μ => ?_⟩
    simp only [Pi.add_apply, hn, hm, Int.cast_add, add_mul]
  zero_mem' := ⟨0, fun μ => by simp⟩
  neg_mem' := by
    rintro x ⟨n, hn⟩
    refine ⟨-n, fun μ => ?_⟩
    simp only [Pi.neg_apply, hn, Int.cast_neg, neg_mul]
abbrev GridSite (d : ℕ) (a : ℝ) : Type := ↥(gridSubgroup d a)
abbrev GridField (d : ℕ) (a : ℝ) : Type := Fin d → GridSite d a → ℝ
variable {d : ℕ} {a : ℝ}
def gridStep (μ : Fin d) : GridSite d a :=
  ⟨Pi.single μ a, Pi.single μ 1, fun ν => by
    by_cases h : ν = μ
    · subst h
      simp
    · simp [Pi.single_eq_of_ne h]⟩
def forwardDiff (μ : Fin d) (f : GridSite d a → ℝ) : GridSite d a → ℝ :=
  fun x => a⁻¹ * (f (x + gridStep μ) - f x)
def backwardDiff (μ : Fin d) (f : GridSite d a → ℝ) : GridSite d a → ℝ :=
  fun x => a⁻¹ * (f (x - gridStep μ) - f x)
def gradient (f : GridSite d a → ℝ) : GridField d a := fun μ => forwardDiff μ f
def gradientAdjoint (F : GridField d a) : GridSite d a → ℝ := fun x => ∑ μ, backwardDiff μ (F μ) x
def laplacian (f : GridSite d a → ℝ) : GridSite d a → ℝ := gradientAdjoint (gradient f)
def l2Norm (f : GridSite d a → ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (a ^ d) * ∑' x, ENNReal.ofReal (f x ^ 2)) ^ (1 / 2 : ℝ)
def restrictedL2Norm (X : Set (GridSite d a)) (f : GridSite d a → ℝ) : ℝ≥0∞ := l2Norm (X.indicator f)
def supOver (X : Set (GridSite d a)) (f : GridSite d a → ℝ) : ℝ≥0∞ := ⨆ x ∈ X, ENNReal.ofReal |f x|
def supNorm (f : GridSite d a → ℝ) : ℝ≥0∞ := supOver Set.univ f
def fieldSupNorm (F : GridField d a) : ℝ≥0∞ := ⨆ μ, supNorm (F μ)
def latticeConv (k g : GridSite d a → ℝ) : GridSite d a → ℝ :=
  fun x => a ^ d * ∑' z, k (x - z) * g z
end InfiniteLattice
end YangMills.Construction
