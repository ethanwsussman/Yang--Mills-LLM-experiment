import YangMills.Construction.Cumulants.NonSingletonPartitions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Multilinear
variable {q : ℕ}
def restrictOrdered {V : Fin q → Type} (x : ∀ l, V l) (J : Finset (Fin q)) (i : Fin J.card) :
    V (J.orderEmbOfFin rfl i) :=
  x (J.orderEmbOfFin rfl i)
abbrev BlockForms (V : Fin q → Type) [∀ l, AddCommGroup (V l)] [∀ l, Module ℝ (V l)] : Type :=
  ∀ J : Finset (Fin q), 2 ≤ J.card →
    MultilinearMap ℝ (fun i : Fin J.card => V (J.orderEmbOfFin rfl i)) ℝ
def partitionSum {V : Fin q → Type} [∀ l, AddCommGroup (V l)] [∀ l, Module ℝ (V l)]
    (Φ : BlockForms V) (x : ∀ l, V l) : ℝ :=
  ∑ π ∈ (SetPartition.nonSingletonPartitions q).attach, ∏ J ∈ π.1.parts.attach,
    Φ J.1 ((Finset.mem_filter.mp π.2).2 J.1 J.2) (restrictOrdered x J.1)
def partitionBound (q : ℕ) (C : ℕ → ℝ) : ℝ :=
  ∑ π ∈ SetPartition.nonSingletonPartitions q, ∏ J ∈ π.parts, C J.card
def BoundedMultilinearEstimates : Prop :=
  ∀ q : ℕ, 1 ≤ q → ∀ (V : Fin q → Type) [∀ l, AddCommGroup (V l)] [∀ l, Module ℝ (V l)]
    (p : ∀ l, Seminorm ℝ (V l)),
    (∀ (Φ : MultilinearMap ℝ V ℝ) (c : ℝ), 0 ≤ c →
      (∀ x : ∀ l, V l, |Φ x| ≤ c * ∏ l, p l (x l)) →
      ∀ f g : ∀ l, V l,
        |Φ f - Φ g| ≤ c * ∑ l, p l (f l - g l) * (∏ l' ∈ Finset.Iio l, p l' (g l')) *
            ∏ l' ∈ Finset.Ioi l, p l' (f l') ∧
          c * ∑ l, p l (f l - g l) * (∏ l' ∈ Finset.Iio l, p l' (g l')) *
              ∏ l' ∈ Finset.Ioi l, p l' (f l') ≤
            c * ∑ l, p l (f l - g l) *
              ∏ l' ∈ Finset.univ.erase l, (p l' (f l') + p l' (g l'))) ∧
    (∀ Φ : BlockForms V,
      (∃ M : MultilinearMap ℝ V ℝ, ∀ x, M x = partitionSum Φ x) ∧
      ∀ C : ℕ → ℝ, (∀ m, 2 ≤ m → m ≤ q → 0 ≤ C m) →
        (∀ (J : Finset (Fin q)) (hJ : 2 ≤ J.card) (x : ∀ l, V l),
          |Φ J hJ (restrictOrdered x J)| ≤ C J.card * ∏ l ∈ J, p l (x l)) →
        ∀ x : ∀ l, V l, |partitionSum Φ x| ≤ partitionBound q C * ∏ l, p l (x l))
end YangMills.Construction.Multilinear
end
