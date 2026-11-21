import Mathlib
universe u v w
namespace YangMills.Construction
namespace Conventions
def DependsOnlyThrough {D : Type u} {Q : Type v} {R : Type w} (x : D → R) (q : D → Q) : Prop :=
  ∃ f : Q → R, ∀ d, x d = f (q d)
variable {Q : Type u} {Cfg : Q → ℕ+ → ℕ+ → ℕ → ℕ → Type v}
end Conventions
end YangMills.Construction
