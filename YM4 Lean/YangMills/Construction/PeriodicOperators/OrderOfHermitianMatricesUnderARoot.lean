import YangMills.Construction.Towers.CoercivityOfTheFreeOperators
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators
namespace RootConjugationOrder
def ConjugatedOrderBounds : Prop :=
  ∀ P Q : PeriodicData, IsPeriodic P → IsPeriodic Q →
    ∀ (N K X : QuotHom P P) (A : QuotHom P Q) (Astar : QuotHom Q P) (c cA : ℝ),
      0 < c → c ≤ 1 → 0 < cA →
      IsSelfAdjointQuotHom N →
      LoewnerLE (scalarQuotHom P 0) K →
      LoewnerLE ((c : ℂ) • (K + scalarQuotHom P 1)) X →
      LoewnerLE X (K + scalarQuotHom P 1) →
      N.comp ((K + scalarQuotHom P 1).comp N) = LinearMap.id →
      IsAdjointQuotHom A Astar →
      LoewnerLE (scalarQuotHom Q cA) (A.comp ((N.comp N).comp Astar)) →
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ τ ∈ Icc (0 : ℝ) 1,
        LoewnerLE (scalarQuotHom P c)
          (N.comp (((t : ℂ) • X + ((1 - t : ℝ) : ℂ) • K + scalarQuotHom P 1).comp N)) ∧
        LoewnerLE (scalarQuotHom P c) (N.comp ((X + scalarQuotHom P τ).comp N)) ∧
        IsInvertibleQuotHom (N.comp ((X + scalarQuotHom P τ).comp N)) ∧
        LoewnerLE (scalarQuotHom Q (cA / 2))
          (A.comp ((N.comp ((quotHomInverse (N.comp ((X + scalarQuotHom P τ).comp N))).comp
            N)).comp Astar))
end RootConjugationOrder
end YangMills.Construction.PeriodicOperators
end
