import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.TorusOrFourSpace.ProductsAndProjectionsOfSeveralPoints
import YangMills.Construction.TorusOrFourSpace.RulesForTensors
import YangMills.Construction.TorusOrFourSpace.SmoothRealFunctionsInTheTwoSenses
import YangMills.Construction.TorusOrFourSpace.SpaceAndItsFunctionsAreWellDefined
import YangMills.Construction.TorusOrFourSpace.TensorOfASeparatedTupleWithSmoothEntries
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Euclid
open YangMills.Construction.PeriodicSpace.Kind.Tuple
theorem supportQ_ofReal (D : Params) (u : Kind.euclidean.Pt D → ℝ) :
    Kind.supportQ D Kind.euclidean (fun y => ((u y : ℝ) : ℂ)) =
      Kind.supportQ D Kind.euclidean u := by
  have hset : {y | ((u y : ℝ) : ℂ) ≠ 0} = {y | u y ≠ 0} := by
    ext y
    simp
  unfold Kind.supportQ
  rw [hset]
theorem abs_apply_le_euclidNormVec (v : Fin 4 → ℝ) (μ : Fin 4) :
    |v μ| ≤ TorusMetric.euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
theorem supportQ_subset_tsupport (hwell : WellPosedness.WellPosed) (D : Params)
    (u : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) (hx : x ∈ Kind.supportQ D Kind.euclidean u) :
    x ∈ tsupport u := by
  have hclose : ∀ y : Fin 4 → ℝ, ∀ ε : ℝ, 0 < ε → Kind.quotDist D Kind.euclidean x y < ε →
      dist x y < ε := by
    intro y ε hε hxy
    have hd : Kind.quotDist D Kind.euclidean x y = TorusMetric.euclidNormVec (x - y) :=
      (hwell D Kind.euclidean).2.2.2.2.2.2.2.1 x y
    refine (dist_pi_lt_iff hε).2 fun μ => ?_
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (abs_apply_le_euclidNormVec (x - y) μ) (hd ▸ hxy)
  refine Metric.mem_closure_iff.2 fun ε hε => ?_
  obtain ⟨y, hy, hxy⟩ := hx ε hε
  exact ⟨y, hy, hclose y ε hε hxy⟩
theorem smoothSepTensorFacts_holds (hrules : TensorRules.AllRules)
    (hprod : TupleProducts.Statement)
    (hsmooth : Kind.SmoothIffSmoothAsTuple)
    (hwell : WellPosedness.WellPosed) : SmoothSepTensorFacts := by
  intro D n O _ f hf hsm hsupp F C
  have hr := hrules D n n
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hr.2.2.2.2.2.2.2.2.1 _ fun i => (hsmooth D Kind.euclidean (f i)).1 (hsm i)
  · have h := hr.2.2.2.2.2.2.1 fun i y => ((f i y : ℝ) : ℂ)
    refine h.trans ?_
    ext y
    simp only [Set.mem_pi, Set.mem_univ, true_implies, supportQ_ofReal]
    rfl
  · exact ((hprod D Kind.euclidean n).1 _).2.2 hf.2.1
  · intro y hy
    have hO : ∀ l, y l ∈ O := fun l =>
      (hsupp l).2 (supportQ_subset_tsupport hwell D (f l) _ (hy l))
    refine ⟨fun l => ⟨y l, hO l⟩, ?_, rfl⟩
    intro l l' hl
    by_contra hne
    have heq : y l = y l' := congrArg Subtype.val hl
    exact Set.disjoint_left.1 (hf.2.2 l l' hne) (hy l) (heq ▸ hy l')
end YangMills.Construction.PeriodicSpace.Euclid
end
