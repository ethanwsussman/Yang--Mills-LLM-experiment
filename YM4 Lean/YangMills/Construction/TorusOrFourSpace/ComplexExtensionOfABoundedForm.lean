import YangMills.Construction.TorusOrFourSpace.ComplexClassesOfOnePoint
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace
namespace Kind.Tuple
variable (P : Params) (Q : Kind) {n : ℕ+}
def IsBoundedComplexMultiform (U : Fin (n : ℕ) → Set (Q.Pt P)) (c : ℝ)
    (G : (Fin (n : ℕ) → Q.Pt P → ℂ) → ℂ) : Prop :=
  (∀ (h : Fin (n : ℕ) → Q.Pt P → ℂ) (k : Fin (n : ℕ)) (u v : Q.Pt P → ℂ),
    (∀ i, h i ∈ complexC1SupportedIn P Q (U i)) → u ∈ complexC1SupportedIn P Q (U k) →
      v ∈ complexC1SupportedIn P Q (U k) →
      G (Function.update h k (u + v)) = G (Function.update h k u) + G (Function.update h k v)) ∧
  (∀ (h : Fin (n : ℕ) → Q.Pt P → ℂ) (k : Fin (n : ℕ)) (u : Q.Pt P → ℂ) (a : ℂ),
    (∀ i, h i ∈ complexC1SupportedIn P Q (U i)) → u ∈ complexC1SupportedIn P Q (U k) →
      G (Function.update h k (a • u)) = a * G (Function.update h k u)) ∧
  ∀ h : Fin (n : ℕ) → Q.Pt P → ℂ, (∀ i, h i ∈ complexC1SupportedIn P Q (U i)) →
    ENNReal.ofReal ‖G h‖ ≤
      ENNReal.ofReal (2 ^ (n : ℕ) * c) * ∏ i, c1NormSingle P Q (h i)
end Kind.Tuple
def ComplexExtensionClaim : Prop :=
  ∀ (P : Params) (Q : Kind) (n : ℕ+) (c : ℝ), 0 ≤ c →
    ∀ U : Fin (n : ℕ) → Set (Q.Pt P), (∀ i, Kind.IsOpenQ P Q (U i)) →
    ∀ B : (∀ i, Kind.c1SupportedIn P Q (U i)) → ℝ,
      (∀ (g : ∀ i, Kind.c1SupportedIn P Q (U i)) (i : Fin (n : ℕ)) (u v w : Kind.c1SupportedIn P Q (U i))
        (a b : ℝ), w.1 = a • u.1 + b • v.1 →
          B (Function.update g i w) =
            a * B (Function.update g i u) + b * B (Function.update g i v)) →
      (∀ g : ∀ i, Kind.c1SupportedIn P Q (U i), ENNReal.ofReal |B g| ≤
        ENNReal.ofReal c * ∏ i, Kind.Tuple.c1NormSingleReal P Q (g i).1) →
      ∃ G : (Fin (n : ℕ) → Q.Pt P → ℂ) → ℂ,
        Kind.Tuple.IsBoundedComplexMultiform P Q U c G ∧
          ∀ g : ∀ i, Kind.c1SupportedIn P Q (U i), G (fun i x => ((g i).1 x : ℂ)) = (B g : ℂ)
end YangMills.Construction.PeriodicSpace
