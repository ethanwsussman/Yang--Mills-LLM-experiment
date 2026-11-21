import YangMills.Construction.BoundsOnEverySide.SeparatedLimitsUnderABoundProof
import YangMills.Construction.Continuum.ConnectedFunctionsCentredFunctionalsOnTheSpanAndCumulantsOfAState
import YangMills.Construction.Cumulants.CumulantsMomentsAndCentredMoments
import YangMills.Construction.ReflectionPositivity.ConnectedFunctionsOfTheLimitAreLimitsOfCumulants
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Topology
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.UrsellLimit
open AxisMirror (MirrorData)
open InfiniteLattice
open LimitConventions (ApproxTriple)
open Probability (IsBoundedRealRV)
open TupleLists (ofList toList ofList_toList)
open SetPartition (Partitions blockCount)
open TestSpaces (SepTuple SepTupleOfCard cumulant sepRestrict)
variable {L : ℕ}
theorem sepTuple_apply_mem_compactTestFunctions {n : ℕ} (X : SepTupleOfCard n) (i : Fin n) :
    X.1 i ∈ compactTestFunctions := by apply _root_.YangMills.Construction.BoundsOnEverySide.SubsequentialLimits.tuple_mem_compactTestFunctions <;> assumption
theorem smearedField_eq_smearedEnergy_add (T : ApproxTriple L) (j : ℕ+) (f : AmbientSpace → ℝ)
    (hf : {p : ElementaryPlaquette (refinedSpacing L (T.cutoff j)) | f p.center ≠ 0}.Finite)
    (U : RefinedGaugeField L (T.cutoff j)) :
    T.smearedField j f U = smearedEnergy f U +
      -(T.offset j * ∑ᶠ p : ElementaryPlaquette (refinedSpacing L (T.cutoff j)), f p.center) := by
  have hmem : ∀ p : ElementaryPlaquette (refinedSpacing L (T.cutoff j)), p ∉ hf.toFinset →
      f p.center = 0 := fun p hp => by
    by_contra h
    exact hp (hf.mem_toFinset.2 h)
  have h₁ : Function.support (fun p : ElementaryPlaquette (refinedSpacing L (T.cutoff j)) =>
      f p.center * (faceEnergy U p - T.offset j)) ⊆ hf.toFinset := fun p hp => by
    by_contra h
    exact hp (by simp [hmem p (by simpa using h)])
  have h₂ : Function.support (fun p : ElementaryPlaquette (refinedSpacing L (T.cutoff j)) =>
      faceEnergy U p • f p.center) ⊆ hf.toFinset := fun p hp => by
    by_contra h
    exact hp (by simp [hmem p (by simpa using h)])
  have h₃ : Function.support (fun p : ElementaryPlaquette (refinedSpacing L (T.cutoff j)) =>
      f p.center) ⊆ hf.toFinset := fun p hp => by
    by_contra h
    exact hp (hmem p (by simpa using h))
  have hfield : T.smearedField j f U = ∑ᶠ p : ElementaryPlaquette (refinedSpacing L (T.cutoff j)),
      f p.center * (faceEnergy U p - T.offset j) := rfl
  rw [hfield, smearedEnergy, finsum_eq_sum_of_support_subset _ h₁,
    finsum_eq_sum_of_support_subset _ h₂, finsum_eq_sum_of_support_subset _ h₃, Finset.mul_sum,
    ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [smul_eq_mul]
  ring
theorem tupleRep_sepRestrict (T : ApproxTriple L) (j : ℕ+) {n : ℕ}
    (X : SepTupleOfCard n) (J : Finset (Fin n)) (U : RefinedGaugeField L (T.cutoff j)) :
    T.tupleRep j (toList ⟨J.card, sepRestrict X J⟩) U =
      ∏ l ∈ J, T.smearedField j (X.1 l) U := by
  have h : T.tupleRep j (toList ⟨J.card, sepRestrict X J⟩) U =
      ((List.ofFn fun k : Fin J.card => X.1 (J.orderEmbOfFin rfl k)).map
        fun f => T.smearedField j f U).prod := rfl
  rw [h, List.map_ofFn, List.prod_ofFn, ← Finset.prod_coe_sort J,
    ← Equiv.prod_comp (J.orderIsoOfFin rfl).toEquiv]
  exact Finset.prod_congr rfl fun k _ => by simp
theorem finsetMoment_smearedField (T : ApproxTriple L) (j : ℕ+) {n : ℕ} (X : SepTupleOfCard n)
    (J : Finset (Fin n)) :
    Cumulants.finsetMoment (T.state j) (fun i => T.smearedField j (X.1 i)) J =
      ((∫ U, T.tupleRep j (toList ⟨J.card, sepRestrict X J⟩) U ∂T.state j : ℝ) : ℂ) := by
  simp_rw [tupleRep_sepRestrict]
  rw [Cumulants.finsetMoment]
  split_ifs with h
  · subst h
    simp
  · exact integral_complex_ofReal
theorem ursellFunction_eq_sum_partitions
    (hc : Cumulants.CumulantMomentRelations)
    (hs : CenteredIdentity.Statement) (D : MirrorData) (T : ApproxTriple D.L) (j : ℕ+)
    {n : ℕ} (hn : 2 ≤ n) (X : SepTupleOfCard n) :
    ursellFunction (T.state j) n X.1 =
      ∑ π : Partitions (Finset.univ : Finset (Fin n)),
        (-1 : ℂ) ^ (blockCount π - 1) * ((blockCount π - 1).factorial : ℂ) *
          ∏ J ∈ π.parts, ((∫ U, T.tupleRep j (toList ⟨J.card, sepRestrict X J⟩) U
            ∂T.state j : ℝ) : ℂ) := by
  have hobs : ∀ i, CenteredIdentity.SmearedIsFiniteAndBounded
      (refinedSpacing D.L (T.cutoff j)) (X.1 i) := fun i =>
    (hs ⟨D.L, D.isAdmissible, T.cutoff j, D.m⟩ (T.state j) inferInstance).1.1 _
      (sepTuple_apply_mem_compactTestFunctions X i)
  let c : Fin n → ℝ := fun i =>
    -(T.offset j * ∑ᶠ p : ElementaryPlaquette (refinedSpacing D.L (T.cutoff j)), X.1 i p.center)
  have hy : (fun i => T.smearedField j (X.1 i)) =
      Cumulants.shiftTuple (fun i U => smearedEnergy (X.1 i) U) c := by
    funext i U
    exact smearedField_eq_smearedEnergy_add T j _ (hobs i).1 U
  have hby : ∀ i, IsBoundedRealRV
      (T.smearedField j (X.1 i) : RefinedGaugeField D.L (T.cutoff j) → ℝ) := fun i => by
    have hi : (T.smearedField j (X.1 i) : RefinedGaugeField D.L (T.cutoff j) → ℝ) =
        fun U => smearedEnergy (X.1 i) U + c i := congrFun hy i
    obtain ⟨hm, C, hC⟩ := (hobs i).2
    rw [hi]
    refine ⟨hm.add_const _, C + |c i|, fun U => ?_⟩
    exact (abs_add_le _ _).trans (add_le_add (hC U) le_rfl)
  obtain ⟨-, -, -, -, -, -, hG⟩ := hc _ (T.state j) n (fun i => T.smearedField j (X.1 i)) hby
  obtain ⟨-, -, -, hD, -⟩ := hc _ (T.state j) n (fun i => T.smearedField j (X.1 i)) hby
  have hshift := hD n (fun i U => smearedEnergy (X.1 i) U) c hn fun i => (hobs i).2
  rw [← hy] at hshift
  rw [InfiniteLattice.ursellFunction_eq_mixedCumulant, ← hshift, hG (by omega)]
  simp_rw [finsetMoment_smearedField]
theorem holds (hc : Cumulants.CumulantMomentRelations)
    (hs : CenteredIdentity.Statement) : UrsellOfLimitIsLimitOfCumulants := by
  intro D T s hlim n hn X
  have hrhs : (cumulant s X : ℂ) =
      ∑ π : Partitions (Finset.univ : Finset (Fin n)),
        (-1 : ℂ) ^ (blockCount π - 1) * ((blockCount π - 1).factorial : ℂ) *
          ∏ J ∈ π.parts, ((s ⟨J.card, sepRestrict X J⟩ : ℝ) : ℂ) := by
    rw [TestSpaces.cumulant_eq_sum_partitions]
    push_cast
    rfl
  rw [hrhs]
  simp_rw [ursellFunction_eq_sum_partitions hc hs D T _ hn X]
  refine tendsto_finsetSum _ fun π _ => Tendsto.const_mul _ (tendsto_finsetProd _ fun J _ => ?_)
  have hJ : Tendsto (fun j => ∫ U, T.tupleRep j (toList ⟨J.card, sepRestrict X J⟩) U
      ∂T.state j) atTop (𝓝 (s (ofList (toList ⟨J.card, sepRestrict X J⟩)))) := hlim _
  rw [ofList_toList] at hJ
  exact (Complex.continuous_ofReal.tendsto _).comp hJ
end YangMills.Construction.ReflectionPositivity.UrsellLimit
end
