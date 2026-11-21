import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Analytic
def FaaDiBrunoAnalyticProperty : Prop :=
  ∀ (k : ℕ) (A B W : Type) [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [CompleteSpace B] [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    (G : B → W) (T : A → B) (x : A), AnalyticAt ℝ T x → AnalyticAt ℝ G (T x) → ∀ v : Fin k → A,
      iteratedFDeriv ℝ k (G ∘ T) x v = ∑ c : OrderedFinpartition k,
        iteratedFDeriv ℝ c.length G (T x)
          (fun m => iteratedFDeriv ℝ (c.partSize m) T x (v ∘ c.emb m))
end Analytic
end YangMills.Construction
end
