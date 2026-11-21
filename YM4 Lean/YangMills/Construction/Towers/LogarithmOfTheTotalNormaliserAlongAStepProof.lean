import YangMills.Construction.Towers.DilationNearTheTrivialConfiguration
import YangMills.Construction.Towers.LinearMapsOnTheRealSpacesProof
import YangMills.Construction.Towers.LogarithmOfTheTotalNormaliserAlongAStep
import YangMills.Construction.Towers.NormalisersOfTheCriticalBranch
import YangMills.Construction.Towers.SecondOrderOfACompositeAtOneProof
import YangMills.Construction.Towers.TheChainOfABlockField
import YangMills.Construction.Towers.TheCriticalBranch
import YangMills.Construction.Towers.TotalNormaliserIsAProduct
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace YangMills.Construction.Tower
namespace LogTotalNormaliserStepLemmas
variable {L n k : ℕ}
theorem trivialField_mem_fieldSpace (j : ℕ) :
    trivialField L n k j ∈ fieldSpace L n k j := by apply _root_.YangMills.Construction.Tower.CompositeSecondOrder.trivialField_mem <;> assumption
theorem EventuallyNearIdentity.at_trivialField {j : ℕ}
    {P : (Edge L n k j → Matrices.ComplexMatrix2) → Prop}
    (h : EventuallyNearIdentity (fieldSpace L n k j) P) : P (trivialField L n k j) :=
  Filter.Eventually.self_of_nhdsWithin h (trivialField_mem_fieldSpace j)
theorem descendingChain_eq_chosenProlongIter (W : Edge L n k k → Matrices.ComplexMatrix2) {j : ℕ}
    (hj : j ≤ k) :
    descendingChain W hj = chosenProlongIter L n k hj W := by apply _root_.YangMills.Construction.Tower.RealLinearMaps.descendingChain_eq_chosenProlongIter <;> assumption
theorem eventually_descendingChain (hc : ProlongItersNearIdentity L n k) {j : ℕ} (hj : j ≤ k)
    {P : (Edge L n k j → Matrices.ComplexMatrix2) → Prop}
    (hP : EventuallyNearIdentity (fieldSpace L n k j) P) :
    EventuallyNearIdentity (fieldSpace L n k k) fun W => P (descendingChain W hj) := by
  have h := (hc.tendsto j hj).eventually hP
  refine h.mono fun W hW => ?_
  rw [descendingChain_eq_chosenProlongIter]
  exact hW
theorem eventually_transportTotal_scaleEdge {j i : ℕ} (hL : 0 < L) (hj : j ≤ k)
    (hd : ScalingPreservesFieldsAndForms (m := n) hL hj i)
    (ho : ScalingPreservesOpenSets (m := n) hL hj i)
    {P : (Edge L (scaledExponent n k j) j i → Matrices.ComplexMatrix2) → Prop}
    (hP : EventuallyNearIdentity (fieldSpace L (scaledExponent n k j) j i) P) :
    EventuallyNearIdentity (fieldSpace L n k i)
      fun V => P (transportTotal (scaleEdge hL hj i) V) := by
  have hS := ((ho.1 {V | V ∈ fieldSpace L n k i ∧
      P (transportTotal (scaleEdge hL hj i) V)} (fun V hV => hV.1)).2).2 ?_
  · exact Filter.Eventually.mono hS fun V hV => hV.2
  · refine Filter.Eventually.mp hP ?_
    filter_upwards [eventually_mem_nhdsWithin] with U hU hPU
    obtain ⟨V, hV, rfl⟩ := hd.1.surjOn hU
    exact ⟨V, ⟨hV, hPU⟩, rfl⟩
theorem log_sub_log_of_eq_mul {z z₁ a a₁ b b₁ : ℝ} (ha : 0 < a) (ha₁ : 0 < a₁) (hb : 0 < b)
    (hb₁ : 0 < b₁) (hz : z = a * b) (hz₁ : z₁ = a₁ * b₁) :
    Real.log z - Real.log z₁ =
      (Real.log b - Real.log b₁) + (Real.log a - Real.log a₁) := by
  rw [hz, hz₁, Real.log_mul ha.ne' hb.ne', Real.log_mul ha₁.ne' hb₁.ne']
  ring
noncomputable def lowerNormaliserProduct (L n k : ℕ)
    (W : Edge L n (k + 1) (k + 1) → Matrices.ComplexMatrix2) : ℝ :=
  ∏ i : Fin k, gaussianNormaliser L n (k + 1) i (descendingChain W (Fin.castSucc i).is_lt)
theorem prod_eq_lowerNormaliserProduct_mul (W : Edge L n (k + 1) (k + 1) → Matrices.ComplexMatrix2) :
    ∏ i : Fin (k + 1), gaussianNormaliser L n (k + 1) i (descendingChain W i.is_lt) =
      lowerNormaliserProduct L n k W * gaussianNormaliser L n (k + 1) k W := by
  rw [Fin.prod_univ_castSucc]
  exact congrArg (lowerNormaliserProduct L n k W * ·)
    (congrArg (gaussianNormaliser L n (k + 1) k) (descendingChain_top W))
theorem eventually_factors_pos (hc : ProlongItersNearIdentity L n (k + 1))
    (hpos : ∀ i : Fin (k + 1), EventuallyNearIdentity (fieldSpace L n (k + 1) ((i : ℕ) + 1))
      fun V => 0 < gaussianNormaliser L n (k + 1) i V) :
    EventuallyNearIdentity (fieldSpace L n (k + 1) (k + 1)) fun W =>
      0 < lowerNormaliserProduct L n k W ∧ 0 < gaussianNormaliser L n (k + 1) k W := by
  have h : ∀ i : Fin (k + 1),
      ∀ᶠ W in 𝓝[fieldSpace L n (k + 1) (k + 1)] (fun _ => (1 : Matrices.ComplexMatrix2)),
        0 < gaussianNormaliser L n (k + 1) i (descendingChain W i.is_lt) := fun i =>
    eventually_descendingChain hc i.is_lt (hpos i)
  refine (eventually_all.2 h).mono fun W hW => ⟨?_, ?_⟩
  · exact Finset.prod_pos fun i _ => hW (Fin.castSucc i)
  · have := hW (Fin.last k)
    rwa [show descendingChain W (Fin.last k).is_lt = W from descendingChain_top W] at this
theorem eventually_lowerNormaliserProduct (hL : 0 < L) (hc : ProlongItersNearIdentity L n (k + 2))
    (hd : ∀ i ≤ k + 1, ScalingPreservesFieldsAndForms (m := n) hL (Nat.le_succ (k + 1)) i)
    (ho : ∀ i ≤ k + 1, ScalingPreservesOpenSets (m := n) hL (Nat.le_succ (k + 1)) i)
    (ha : ScalingCompatible (n := n) hL (Nat.le_succ (k + 1)))
    (hchain : EventuallyNearIdentity (fieldSpace L n (k + 2) (k + 2)) fun W =>
      ChainScalingCompatible hL W)
    (hshort : EventuallyNearIdentity
      (fieldSpace L (scaledExponent n (k + 2) (k + 1)) (k + 1) (k + 1))
      fun U => TotalNormaliserWellDefined U ∧
        totalGaussianNormaliser L (scaledExponent n (k + 2) (k + 1)) (k + 1) U =
          ∏ i : Fin (k + 1), gaussianNormaliser L (scaledExponent n (k + 2) (k + 1)) (k + 1) i
            (descendingChain U i.is_lt)) :
    EventuallyNearIdentity (fieldSpace L n (k + 2) (k + 2)) fun W =>
      TotalNormaliserWellDefined
          (scaledTopField hL (Nat.le_succ (k + 1)) (chosenProlong L n (k + 2) (k + 1) W)) ∧
        totalGaussianNormaliser L (scaledExponent n (k + 2) (k + 1)) (k + 1)
            (scaledTopField hL (Nat.le_succ (k + 1)) (chosenProlong L n (k + 2) (k + 1) W)) =
          lowerNormaliserProduct L n (k + 1) W := by
  have hmember : ∀ W : Edge L n (k + 2) (k + 2) → Matrices.ComplexMatrix2,
      descendingChain W (Nat.le_succ (k + 1)) = chosenProlong L n (k + 2) (k + 1) W := fun W => by
    rw [descendingChain_of_lt W (Nat.lt_succ_self (k + 1)), descendingChain_top]
  have hnear := eventually_descendingChain hc (Nat.le_succ (k + 1))
    (eventually_transportTotal_scaleEdge hL (Nat.le_succ (k + 1)) (hd (k + 1) le_rfl)
      (ho (k + 1) le_rfl) hshort)
  have hfactor : ∀ i : Fin (k + 1),
      ∀ᶠ W in 𝓝[fieldSpace L n (k + 2) (k + 2)] (fun _ => (1 : Matrices.ComplexMatrix2)),
        gaussianNormaliser L (scaledExponent n (k + 2) (k + 1)) (k + 1) i
            (transportTotal (scaleEdge hL (Nat.le_succ (k + 1)) ((i : ℕ) + 1))
              (descendingChain W (i.is_lt.trans (Nat.lt_succ_self (k + 1))))) =
          gaussianNormaliser L n (k + 2) i
            (descendingChain W (i.is_lt.trans (Nat.lt_succ_self (k + 1)))) := by
    intro i
    refine (eventually_descendingChain hc (i.is_lt.trans (Nat.lt_succ_self (k + 1)))
      (eventually_transportTotal_scaleEdge hL (Nat.le_succ (k + 1)) (hd _ i.is_lt) (ho _ i.is_lt)
        (ha.normaliser_eq i i.is_lt))).mono fun W hW => ?_
    rw [← hW, transportTotalScalar_transportTotal]
  filter_upwards [hnear, hchain, eventually_all.2 hfactor] with W h₁ h₂ h₃
  have h₄ : scaledTopField hL (Nat.le_succ (k + 1)) (chosenProlong L n (k + 2) (k + 1) W) =
      transportTotal (scaleEdge hL (Nat.le_succ (k + 1)) (k + 1))
        (descendingChain W (Nat.le_succ (k + 1))) := by
    rw [hmember]
    rfl
  rw [h₄]
  refine ⟨h₁.1, h₁.2.trans (Finset.prod_congr rfl fun i _ => ?_)⟩
  have h₅ := h₂ (k + 1) (Nat.le_succ (k + 1)) (Nat.succ_pos k) ((i : ℕ) + 1) i.is_lt
  have h₆ : descendingChain (transportTotal (scaleEdge hL (Nat.le_succ (k + 1)) (k + 1))
        (descendingChain W (Nat.le_succ (k + 1)))) i.is_lt =
      transportTotal (scaleEdge hL (Nat.le_succ (k + 1)) ((i : ℕ) + 1))
        (descendingChain W (i.is_lt.trans (Nat.lt_succ_self (k + 1)))) := h₅
  rw [h₆]
  exact h₃ i
end LogTotalNormaliserStepLemmas
open LogTotalNormaliserStepLemmas in
theorem LogTotalNormaliserStep.holds (hProduct : TotalNormaliserFactorises)
    (hBranch : CriticalBranchExists) (hComposites : ProlongCompositesAndVertexLayers.Statement)
    (hNormalisers : NormalisersHold)
    (hChain : BlockFieldChainProperties)
    (hDilation : ScalingNearTrivialField) :
    LogTotalNormaliserStep.Statement := by
  intro L n k hst hn hL
  have hP := hProduct L n (k + 1) hst hn (Nat.succ_le_succ (Nat.zero_le k))
  obtain ⟨hc, -, -⟩ := hComposites.1 L n (k + 1) hst hn (Nat.succ_le_succ (Nat.zero_le k))
  have hpos := eventually_factors_pos hc fun i =>
    (hNormalisers L n (k + 1) hst hn i i.is_lt).normaliser_pos
  have hP₁ := EventuallyNearIdentity.at_trivialField hP
  have hpos₁ := EventuallyNearIdentity.at_trivialField hpos
  cases k with
  | zero =>
    filter_upwards [hP, hpos] with W hW hW₂
    refine ⟨Or.inr ⟨hW.1, hP₁.1⟩, Or.inl rfl, ?_⟩
    have hlog := log_sub_log_of_eq_mul hW₂.1 hpos₁.1 hW₂.2 hpos₁.2
      (hW.2.trans (prod_eq_lowerNormaliserProduct_mul W))
      (hP₁.2.trans (prod_eq_lowerNormaliserProduct_mul _))
    simpa [logTotalNormaliserRatio, logLevelNormaliserRatio, logNormaliserRatio,
      lowerNormaliserProduct] using hlog
  | succ k =>
    have hb : (chosenCriticalBranch L n (k + 2)).IsCritical :=
      Classical.epsilon_spec (hBranch L n (k + 2) hst hn)
    have hd : ∀ i ≤ k + 1, ScalingPreservesFieldsAndForms (m := n) hL (Nat.le_succ (k + 1)) i :=
      fun i hi => (hDilation L n (k + 2) (k + 1) i i hL (Nat.le_succ (k + 1)) hst hn hi hi).1
    have ho : ∀ i ≤ k + 1, ScalingPreservesOpenSets (m := n) hL (Nat.le_succ (k + 1)) i :=
      fun i hi => (hDilation L n (k + 2) (k + 1) i i hL (Nat.le_succ (k + 1)) hst hn hi hi).2.1
    have hshort := hProduct L (scaledExponent n (k + 2) (k + 1)) (k + 1) hst
      (Nat.add_pos_left hn _) (Nat.succ_le_succ (Nat.zero_le k))
    have hlower := eventually_lowerNormaliserProduct hL hc hd ho
      (hNormalisers L n (k + 2) hst hn k (Nat.le_succ (k + 1))).scaling
      ((hChain L n (k + 2) hst hn (Nat.succ_le_succ (Nat.zero_le _)) hL).1.mono
        fun _ hW => hW.2.2) hshort
    have hlower₁ := EventuallyNearIdentity.at_trivialField hlower
    have hone : scaledTopField hL (Nat.le_succ (k + 1))
        (chosenProlong L n (k + 2) (k + 1) (trivialField L n (k + 2) (k + 2))) =
        trivialField L (scaledExponent n (k + 2) (k + 1)) (k + 1) (k + 1) := by
      rw [show chosenProlong L n (k + 2) (k + 1) (trivialField L n (k + 2) (k + 2)) =
        trivialField L n (k + 2) (k + 1) from hb.prolong_trivial (k + 1) (Nat.lt_succ_self _)]
      exact (hd (k + 1) le_rfl).2.1
    rw [hone] at hlower₁
    filter_upwards [hP, hpos, hlower] with W hW hW₂ hW₃
    refine ⟨Or.inr ⟨hW.1, hP₁.1⟩, Or.inr ⟨hW₃.1, hlower₁.1⟩, ?_⟩
    have hlog := log_sub_log_of_eq_mul hW₂.1 hpos₁.1 hW₂.2 hpos₁.2
      (hW.2.trans (prod_eq_lowerNormaliserProduct_mul W))
      (hP₁.2.trans (prod_eq_lowerNormaliserProduct_mul _))
    have hk : k + 1 + 1 ≠ 0 := Nat.succ_ne_zero _
    have hk' : k + 1 ≠ 0 := Nat.succ_ne_zero _
    simp only [logTotalNormaliserRatio, logLevelNormaliserRatio, logNormaliserRatio, if_neg hk,
      if_neg hk', hW₃.2, hlower₁.2]
    exact hlog
end YangMills.Construction.Tower
