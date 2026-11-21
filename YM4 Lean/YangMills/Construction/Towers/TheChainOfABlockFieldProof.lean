import YangMills.Construction.Towers.LogarithmOfTheTotalNormaliserAlongAStepProof
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace YangMills.Construction.Tower
namespace BlockFieldChain
variable {L m k : ℕ}
theorem descendingChain_eq_chosenProlongIter (W : Edge L m k k → Matrices.ComplexMatrix2) {j : ℕ}
    (hj : j ≤ k) :
    descendingChain W hj = chosenProlongIter L m k hj W := by apply _root_.YangMills.Construction.Tower.RealLinearMaps.descendingChain_eq_chosenProlongIter <;> assumption
theorem eventually_descendingChain (hc : ProlongItersNearIdentity L m k) {j : ℕ} (hj : j ≤ k)
    {P : (Edge L m k j → Matrices.ComplexMatrix2) → Prop}
    (hP : EventuallyNearIdentity (fieldSpace L m k j) P) :
    ∀ᶠ W in 𝓝[fieldSpace L m k k] (fun _ => (1 : Matrices.ComplexMatrix2)),
      P (descendingChain W hj) := by apply _root_.YangMills.Construction.Tower.LogTotalNormaliserStepLemmas.eventually_descendingChain <;> assumption
theorem chainOverBottom_near (hb : (chosenCriticalBranch L m k).IsCritical)
    (hc : ProlongItersNearIdentity L m k) :
    EventuallyNearIdentity (fieldSpace L m k k) ChainOverBottom := by
  have h : ∀ j : Fin (k + 1), ∀ᶠ W in 𝓝[fieldSpace L m k k]
      (fun _ => (1 : Matrices.ComplexMatrix2)),
      descendingChain W (Nat.lt_succ_iff.1 j.2) =
        smoothingIter L m k j (chainBottom W) := by
    intro j
    have hj := Nat.lt_succ_iff.1 j.2
    refine (eventually_descendingChain hc hj (hb.prolongComp_section j hj)).mono fun W hW => ?_
    rw [chainBottom_eq, ← chosenProlongComp_descendingChain W hj]
    exact hW.1.symm
  refine (eventually_all.2 h).mono fun W hW j hj => ⟨?_, hW ⟨j, Nat.lt_succ_of_le hj⟩⟩
  rw [chainBottom_eq, chosenProlongComp_descendingChain]
theorem chainAxialGauge_near (hb : (chosenCriticalBranch L m k).IsCritical)
    (hc : ProlongItersNearIdentity L m k) :
    EventuallyNearIdentity (fieldSpace L m k k) ChainAxialGauge := by
  have h : ∀ i : Fin k, ∀ᶠ W in 𝓝[fieldSpace L m k k] (fun _ => (1 : Matrices.ComplexMatrix2)),
      IsAxialGaugeAt L m k i (descendingChain W i.2.le) := by
    intro i
    refine (eventually_descendingChain hc i.2 (hb.prolong_section i i.2)).mono fun W hW => ?_
    rw [descendingChain_of_lt W i.2]
    exact hW.2.1
  exact (eventually_all.2 h).mono fun W hW i hi => hW ⟨i, hi⟩
variable {j i : ℕ}
theorem eventuallyNearIdentity_scaling (hL : 0 < L) (hj : j ≤ k)
    (hd : ScalingPreservesFieldsAndForms (m := m) hL hj i)
    (ho : ScalingPreservesOpenSets (m := m) hL hj i)
    {P : (Edge L (scaledExponent m k j) j i → Matrices.ComplexMatrix2) → Prop}
    (hP : EventuallyNearIdentity (fieldSpace L (scaledExponent m k j) j i) P) :
    EventuallyNearIdentity (fieldSpace L m k i)
      fun V => P (transportTotal (scaleEdge hL hj i) V) := by apply _root_.YangMills.Construction.Tower.LogTotalNormaliserStepLemmas.eventually_transportTotal_scaleEdge <;> assumption
theorem descendingChain_scaledTopField (hL : 0 < L) (hj : j ≤ k)
    (hc : ProlongItersNearIdentity L m k)
    (ha : ScalingCompatible (n := m) hL hj)
    (hd : ∀ i ≤ j, ScalingPreservesFieldsAndForms (m := m) hL hj i)
    (ho : ∀ i ≤ j, ScalingPreservesOpenSets (m := m) hL hj i) (hi : i ≤ j) :
    ∀ᶠ W in 𝓝[fieldSpace L m k k] (fun _ => (1 : Matrices.ComplexMatrix2)),
      descendingChain (scaledTopField hL hj (descendingChain W hj)) hi =
        transportTotal (scaleEdge hL hj i) (descendingChain W (hi.trans hj)) := by
  refine Nat.decreasingInduction (motive := fun i h =>
    ∀ᶠ W in 𝓝[fieldSpace L m k k] (fun _ => (1 : Matrices.ComplexMatrix2)),
      descendingChain (scaledTopField hL hj (descendingChain W hj)) h =
        transportTotal (scaleEdge hL hj i) (descendingChain W (h.trans hj))) ?_ ?_ hi
  · intro i hij ih
    have hk : i + 1 ≤ k := le_trans hij hj
    have hnear := eventually_descendingChain hc hk
      (eventuallyNearIdentity_scaling hL hj (hd (i + 1) hij) (ho (i + 1) hij) (ha.prolong_eq i hij))
    filter_upwards [ih, hnear] with W h₁ h₂
    rw [descendingChain_of_lt _ hij, h₁, ← h₂, transportTotalFunValued_transportTotal,
      ← descendingChain_of_lt W hk]
  · exact Eventually.of_forall fun W => by rw [descendingChain_top]; rfl
end BlockFieldChain
open BlockFieldChain in
theorem blockFieldChainProperties_holds (hB : CriticalBranchExists)
    (hC : ProlongCompositesAndVertexLayers.Statement)
    (hN : NormalisersHold)
    (hD : ScalingNearTrivialField) : BlockFieldChainProperties := by
  intro L m k hst hm hk hL
  have hb : (chosenCriticalBranch L m k).IsCritical := Classical.epsilon_spec (hB L m k hst hm)
  obtain ⟨hc, -, hl⟩ := hC.1 L m k hst hm hk
  refine ⟨?_, fun x hx => hl.existsUnique_layer x hx⟩
  have key : ∀ j i : ℕ, ∀ᶠ W in 𝓝[fieldSpace L m k k] (fun _ => (1 : Matrices.ComplexMatrix2)),
      ∀ (hj : j ≤ k), 1 ≤ j → ∀ hi : i ≤ j,
        descendingChain (scaledTopField hL hj (descendingChain W hj)) hi =
          transportTotal (scaleEdge hL hj i) (descendingChain W (hi.trans hj)) := by
    intro j i
    by_cases h : j ≤ k ∧ 1 ≤ j ∧ i ≤ j
    · obtain ⟨hj, h1, hi⟩ := h
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hv := descendingChain_scaledTopField (m := m) hL hj hc (hN L m k hst hm j' hj).scaling
        (fun i' hi' => (hD L m k (j' + 1) i' i' hL hj hst hm hi' hi').1)
        (fun i' hi' => (hD L m k (j' + 1) i' i' hL hj hst hm hi' hi').2.1) hi
      exact hv.mono fun W hW _ _ _ => hW
    · exact Eventually.of_forall fun W a b c => absurd ⟨a, b, c⟩ h
  have hall := eventually_all.2 fun p : Fin (k + 1) × Fin (k + 1) => key p.1 p.2
  filter_upwards [chainOverBottom_near hb hc, chainAxialGauge_near hb hc, hall] with W h₁ h₂ h₃
  exact ⟨h₁, h₂, fun j hj h1 i hi =>
    h₃ (⟨j, Nat.lt_succ_of_le hj⟩, ⟨i, Nat.lt_succ_of_le (hi.trans hj)⟩) hj h1 hi⟩
end YangMills.Construction.Tower
