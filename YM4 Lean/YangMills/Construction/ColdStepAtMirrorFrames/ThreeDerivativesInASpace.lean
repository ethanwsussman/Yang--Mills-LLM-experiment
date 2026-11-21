import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
def ThirdOrderChainRuleVectorValued : Prop :=
  ∀ {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (g : F → G) (f : E → F) (x : E),
    ContDiffAt ℝ 3 g (f x) → ContDiffAt ℝ 3 f x →
    ContDiffAt ℝ 3 (g ∘ f) x ∧
    (∀ u : E, iteratedFDeriv ℝ 1 (g ∘ f) x ![u] =
      iteratedFDeriv ℝ 1 g (f x) ![iteratedFDeriv ℝ 1 f x ![u]]) ∧
    (∀ u v : E, iteratedFDeriv ℝ 2 (g ∘ f) x ![u, v] =
      iteratedFDeriv ℝ 2 g (f x) ![iteratedFDeriv ℝ 1 f x ![u], iteratedFDeriv ℝ 1 f x ![v]] +
      iteratedFDeriv ℝ 1 g (f x) ![iteratedFDeriv ℝ 2 f x ![u, v]]) ∧
    ∀ u v w : E, iteratedFDeriv ℝ 3 (g ∘ f) x ![u, v, w] =
      iteratedFDeriv ℝ 3 g (f x)
        ![iteratedFDeriv ℝ 1 f x ![u], iteratedFDeriv ℝ 1 f x ![v], iteratedFDeriv ℝ 1 f x ![w]] +
      iteratedFDeriv ℝ 2 g (f x) ![iteratedFDeriv ℝ 2 f x ![u, v], iteratedFDeriv ℝ 1 f x ![w]] +
      iteratedFDeriv ℝ 2 g (f x) ![iteratedFDeriv ℝ 2 f x ![u, w], iteratedFDeriv ℝ 1 f x ![v]] +
      iteratedFDeriv ℝ 2 g (f x) ![iteratedFDeriv ℝ 2 f x ![v, w], iteratedFDeriv ℝ 1 f x ![u]] +
      iteratedFDeriv ℝ 1 g (f x) ![iteratedFDeriv ℝ 3 f x ![u, v, w]]
end ColdStepAtMirrorFrames
end YangMills.Construction
end
