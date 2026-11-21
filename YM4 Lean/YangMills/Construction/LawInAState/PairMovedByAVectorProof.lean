import YangMills.Construction.LawInAState.PairMovedByAVector
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.StateLaws
open TorusMetric TestFunctions
open InfiniteLattice (AmbientSpace)
theorem localizedPair_translate : localizedPairTranslateStatement := by
  intro c s d Λ f h hp
  refine ⟨⟨fun x => hp.abs_f_le _, fun x => hp.abs_h_le _, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x hx i
    have hloc := hp.f_localized _ hx i
    simp only [Pi.sub_apply, Pi.add_apply] at hloc ⊢
    rwa [show x i - (c i + s i) = x i - s i - c i by ring]
  · intro x hx i
    have hloc := hp.h_localized _ hx i
    simp only [Pi.sub_apply, Pi.add_apply] at hloc ⊢
    rwa [show x i - (c i + s i) = x i - s i - c i by ring]
  · intro x x' t ht
    exact hp.f_lipschitz _ _ t fun i => by simpa using ht i
  · intro x x' t ht
    exact hp.h_lipschitz _ _ t fun i => by simpa using ht i
  · intro x x' hx hx'
    have hsep := hp.separated _ _ hx hx'
    rwa [sub_sub_sub_cancel_right] at hsep
  · unfold TestFunctions.inverseEighthKernel
    have hshift := integral_add_left_eq_self (μ := (volume : Measure AmbientSpace).prod (volume : Measure AmbientSpace))
      (fun z : AmbientSpace × AmbientSpace => f z.1 * h z.2 * ((euclidNormVec (z.1 - z.2) ^ (-8 : ℤ) : ℝ) : ℝ)) ((-s, -s) : AmbientSpace × AmbientSpace)
    rw [Measure.volume_eq_prod]
    refine Eq.trans ?_ hshift
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [Prod.fst_add, Prod.snd_add, add_sub_add_left_eq_sub, neg_add_eq_sub, sub_sub_sub_cancel_right]
    rfl
end YangMills.Construction.StateLaws
end
