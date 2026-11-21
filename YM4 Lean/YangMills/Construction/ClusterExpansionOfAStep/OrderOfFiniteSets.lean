import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.RandomOrder
open Classical in
def IntegrableOfLowerRankSet : Prop :=
  ∀ (K : Type) [Fintype K] (k₀ : K) (p : Finset K → ℝ),
    Integrable (fun v : K → ℝ => p (Finset.univ.filter fun k => v k < v k₀))
      (Measure.pi fun _ : K => volume.restrict (Set.Icc (0 : ℝ) 1))
end YangMills.Construction.RandomOrder
end
