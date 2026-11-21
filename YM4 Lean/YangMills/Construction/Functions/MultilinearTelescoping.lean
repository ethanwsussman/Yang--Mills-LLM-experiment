import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.MultilinearTelescoping
def TelescopingBound : Prop :=
  ∀ n : ℕ, 1 ≤ n →
  ∀ (E : Fin n → Type) [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    (q : ∀ i, Seminorm ℝ (E i)) (C : ℝ), 0 ≤ C →
  ∀ M : MultilinearMap ℝ E ℝ,
    (∀ x : ∀ i, E i, |M x| ≤ C * ∏ i, q i (x i)) →
  ∀ x y : ∀ i, E i,
    |M x - M y| ≤
        C * ∑ i, q i (x i - y i) * (∏ j ∈ Finset.Iio i, q j (y j)) *
          ∏ j ∈ Finset.Ioi i, q j (x j) ∧
      C * ∑ i, q i (x i - y i) * (∏ j ∈ Finset.Iio i, q j (y j)) *
          ∏ j ∈ Finset.Ioi i, q j (x j) ≤
        C * ∑ i, q i (x i - y i) * ∏ j ∈ Finset.univ.erase i, (q j (x j) + q j (y j))
end YangMills.Construction.MultilinearTelescoping
