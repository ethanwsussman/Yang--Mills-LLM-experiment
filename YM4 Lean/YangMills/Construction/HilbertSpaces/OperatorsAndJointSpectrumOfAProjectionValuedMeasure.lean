import YangMills.Construction.SpectralTheory.RealBorelCalculus
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction.SpectralTheory.SpectralMeasure
variable {m m' : ℕ} [NeZero m] [NeZero m'] {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]
theorem IsRealIntegralOp.unique {μ : SpectralMeasure m H} {f : (Fin m → ℝ) → ℝ}
    {hf : Measurable f} {A B : UnboundedOp H} (hA : μ.IsRealIntegralOp f hf A)
    (hB : μ.IsRealIntegralOp f hf B) : A = B := by
  refine LinearPMap.ext (SetLike.coe_injective (hA.1.trans hB.1.symm)) ?_
  intro v hv hv'
  rw [hA.2 ⟨v, hv⟩, hB.2 ⟨v, hv'⟩]
def realIntegralOp (μ : SpectralMeasure m H) (f : (Fin m → ℝ) → ℝ)
    (hf : Measurable f) : UnboundedOp H :=
  Classical.epsilon (μ.IsRealIntegralOp f hf)
theorem IsRealIntegralOp.eq_realIntegralOp {μ : SpectralMeasure m H}
    {f : (Fin m → ℝ) → ℝ} {hf : Measurable f} {A : UnboundedOp H}
    (hA : μ.IsRealIntegralOp f hf A) : A = μ.realIntegralOp f hf :=
  hA.unique (Classical.epsilon_spec ⟨A, hA⟩)
end YangMills.Construction.SpectralTheory.SpectralMeasure
