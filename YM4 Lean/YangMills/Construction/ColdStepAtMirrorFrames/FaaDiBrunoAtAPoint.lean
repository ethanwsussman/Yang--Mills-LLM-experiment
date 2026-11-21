import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Calculus
def FaaDiBrunoAt : Prop :=
  ∀ (E G H : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H] (g : G → H) (f : E → G) (n : ℕ) (x : E),
    ContDiffAt ℝ n g (f x) → ContDiffAt ℝ n f x → ∀ v : Fin n → E,
      iteratedFDeriv ℝ n (g ∘ f) x v = ∑ c : OrderedFinpartition n,
        iteratedFDeriv ℝ c.length g (f x) fun i => iteratedFDeriv ℝ (c.partSize i) f x (v ∘ c.emb i)
end YangMills.Construction.Calculus
end
