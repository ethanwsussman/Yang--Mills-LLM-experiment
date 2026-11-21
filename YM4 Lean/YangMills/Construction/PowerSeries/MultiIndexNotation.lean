import Mathlib
noncomputable section
namespace YangMills.Construction
namespace PowerSeries
abbrev MultiIndex (n : ℕ) : Type := Fin n → ℕ
namespace MultiIndex
variable {n : ℕ}
def order (β : MultiIndex n) : ℕ := ∑ i, β i
def factorial (β : MultiIndex n) : ℕ := ∏ i, (β i).factorial
def monomial {M : Type*} [CommMonoid M] (y : Fin n → M) (β : MultiIndex n) : M := ∏ i, y i ^ β i
end MultiIndex
end PowerSeries
end YangMills.Construction
