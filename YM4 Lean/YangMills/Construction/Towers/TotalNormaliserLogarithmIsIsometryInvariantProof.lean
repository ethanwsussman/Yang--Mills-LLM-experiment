import YangMills.Construction.Towers.DilationNearTheTrivialConfiguration
import YangMills.Construction.Towers.IsometryCovarianceOfTheLiftProof
import YangMills.Construction.Towers.LogarithmOfTheTotalNormaliserAlongAStep
import YangMills.Construction.Towers.NormalisersOfTheCriticalBranch
import YangMills.Construction.Towers.TotalNormaliserLogarithmIsIsometryInvariant
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.Towers
theorem eventually_forall_comp_of_const_within {ι X : Type*} [Finite ι] [TopologicalSpace X]
    (x : X) {S : Set (ι → X)} {P : (ι → X) → Prop}
    (hP : ∀ᶠ V in 𝓝[S] (fun _ : ι => x), P V) :
    ∀ᶠ V in 𝓝[S] (fun _ : ι => x), ∀ σ : ι → ι, V ∘ σ ∈ S → P (V ∘ σ) := by apply _root_.YangMills.Construction.Tower.LiftSymmetryCovariance.eventually_comp_within <;> assumption
open YangMills.Construction.Tower in
theorem logTotalNormaliserSymmetryInvariant_holds
    (hSub : Tower.SublatticesSymmetriesScalingsAndProjections.Statement)
    (hQuot : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hImg : Tower.GaugeAndSymmetryImages.statement)
    (hScal : ScalingCompatibility.Statement)
    (hNearId : Tower.ScalingNearTrivialField)
    (hProl : ProlongCompositesAndVertexLayers.Statement)
    (hCrit : Tower.CriticalBranchExists)
    (hNorm : Tower.NormalisersHold)
    (hLogStep : Tower.LogTotalNormaliserStep.Statement) :
    Tower.LogTotalNormaliserSymmetryInvariant := by
  intro L m₀ k₀ hS hm₀
  have hL : 0 < L := lt_of_lt_of_le (by norm_num) hS.2
  have key : ∀ k m : ℕ, 0 < m → EventuallyNearIdentity (fieldSpace L m k k) fun U =>
      ∀ φ : PeriodicLattice.FourTorus L m → PeriodicLattice.FourTorus L m,
        IsLevelSymmetry k k φ →
        logTotalNormaliserRatio L m k (pushField φ U) = logTotalNormaliserRatio L m k U := by
    intro k
    induction k with
    | zero =>
      intro m _
      exact Filter.Eventually.of_forall fun U φ _ => by simp [logTotalNormaliserRatio]
    | succ k ih =>
      intro m hm
      have hk : k ≤ k + 1 := Nat.le_succ k
      have hEdgeFin : Finite (Edge L m (k + 1) (k + 1)) := by
        obtain ⟨-, ⟨-, -, -, -, -, -, -, -, -, -, -, hE, -⟩, -⟩ :=
          hQuot L hS m (k + 1) (k + 1) hm le_rfl
        exact hE
      have hc : (chosenCriticalBranch L m (k + 1)).IsCritical :=
        Classical.epsilon_spec (hCrit L m (k + 1) hS hm)
      have hEquiv := hc.prolong_symmetry_equivariant k (Nat.lt_succ_self k)
      have hRatio := (hNorm L m (k + 1) hS hm k le_rfl).logRatio_symmetry_invariant
      have hOneStep := hLogStep L m k hS hm hL
      have hIterOne : chosenProlongIter L m (k + 1) hk = chosenProlong L m (k + 1) k := by
        funext U
        simp only [chosenProlongIter, CriticalBranchData.prolongIter]
        rw [show hk = Nat.le_succ_of_le le_rfl from rfl, Nat.leRec_succ, Nat.leRec_self]
        · rfl
        · exact le_rfl
      have hProlTends : Tendsto (chosenProlong L m (k + 1) k)
          (𝓝[fieldSpace L m (k + 1) (k + 1)] trivialField L m (k + 1) (k + 1))
          (𝓝[fieldSpace L m (k + 1) k] trivialField L m (k + 1) k) := by
        have h := (hProl.1 L m (k + 1) hS hm (Nat.succ_le_succ (Nat.zero_le k))).1.tendsto k hk
        rwa [hIterOne] at h
      have hScaleTends : Tendsto (scaledTopField (m := m) hL hk)
          (𝓝[fieldSpace L m (k + 1) k] trivialField L m (k + 1) k)
          (𝓝[fieldSpace L (scaledExponent m (k + 1) k) k k]
            trivialField L (scaledExponent m (k + 1) k) k k) := by
        obtain ⟨hBij, hTriv, -⟩ := (hNearId L m (k + 1) k k k hL hk hS hm le_rfl le_rfl).1
        have hcont : Continuous (scaledTopField (m := m) hL hk) :=
          continuous_pi fun e => continuous_apply _
        refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
        · have h := hcont.tendsto (trivialField L m (k + 1) k)
          have h1 : scaledTopField (m := m) hL hk (trivialField L m (k + 1) k) =
              trivialField L (scaledExponent m (k + 1) k) k k := hTriv
          rw [h1] at h
          exact h.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with V hV
          exact hBij.mapsTo hV
      have hIH : ∀ᶠ U in
          𝓝[fieldSpace L m (k + 1) (k + 1)] trivialField L m (k + 1) (k + 1),
          ∀ ψ : PeriodicLattice.FourTorus L (scaledExponent m (k + 1) k) →
              PeriodicLattice.FourTorus L (scaledExponent m (k + 1) k), IsLevelSymmetry k k ψ →
            logTotalNormaliserRatio L (scaledExponent m (k + 1) k) k
                (pushField ψ (scaledTopField hL hk (chosenProlong L m (k + 1) k U))) =
              logTotalNormaliserRatio L (scaledExponent m (k + 1) k) k
                (scaledTopField hL hk (chosenProlong L m (k + 1) k U)) :=
        (hScaleTends.comp hProlTends).eventually (ih (scaledExponent m (k + 1) k) (Nat.add_pos_left hm _))
      have hInLevel : ∀ᶠ U in
          𝓝[fieldSpace L m (k + 1) (k + 1)] trivialField L m (k + 1) (k + 1),
          chosenProlong L m (k + 1) k U ∈ fieldSpace L m (k + 1) k :=
        hProlTends.eventually self_mem_nhdsWithin
      have hSplit : ∀ᶠ U in
          𝓝[fieldSpace L m (k + 1) (k + 1)] trivialField L m (k + 1) (k + 1),
          logTotalNormaliserRatio L m (k + 1) U =
            logNormaliserRatio L m (k + 1) k U +
              logLevelNormaliserRatio hL hk (chosenProlong L m (k + 1) k U) :=
        Filter.Eventually.mono hOneStep fun _ h => h.2.2
      filter_upwards [eventually_forall_comp_of_const_within (1 : Matrices.ComplexMatrix2) hSplit,
        hSplit, hRatio, hEquiv, hIH, hInLevel, self_mem_nhdsWithin] with U hAll hU hR hE hH hV hUmem φ hφ
      have hOnto : MapsSublatticeOnto (L := L) (n := m) (k + 1) k φ :=
        (((hSub L hL hS (k + 1)).2.2.2.1 m hm (k + 1) le_rfl φ hφ.1 hφ.2).2 k hk).1
      have hKeep : ScalingPreservesSymmetry (n := m) hL hk k φ :=
        ((hScal L hS hL (k + 1) k k hk le_rfl).1 m hm).2.2 φ hφ.1 hOnto
      have hGauge : PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup univ U :=
        ⟨fun e _ => (Matrix.mem_specialUnitaryGroup_iff.1 (hUmem.1 e trivial)).2, hUmem.2⟩
      have hφU : pushField φ U ∈ fieldSpace L m (k + 1) (k + 1) :=
        ((hImg L (k + 1) (k + 1) hS le_rfl).1 m hm U (fun _ => 1) φ hGauge
          (fun _ => Matrix.det_one) hφ.1 hφ.2).2.2.2 hUmem
      have hConj : scaledTopField hL hk (pushField φ (chosenProlong L m (k + 1) k U)) =
          pushField (conjMap (scaling hL m (k + 1) k).toEquiv φ)
            (scaledTopField hL hk (chosenProlong L m (k + 1) k U)) :=
        hKeep.field_comm _ (Or.inl hV)
      have hSplitφ : logTotalNormaliserRatio L m (k + 1) (pushField φ U) =
          logNormaliserRatio L m (k + 1) k (pushField φ U) +
            logLevelNormaliserRatio hL hk (chosenProlong L m (k + 1) k (pushField φ U)) :=
        hAll (edgePreimage φ) hφU
      have hComm : chosenProlong L m (k + 1) k (pushField φ U) =
          pushField φ (chosenProlong L m (k + 1) k U) := hE φ hφ
      have hLevelEq : logLevelNormaliserRatio hL hk
            (pushField φ (chosenProlong L m (k + 1) k U)) =
          logLevelNormaliserRatio hL hk (chosenProlong L m (k + 1) k U) := by
        unfold logLevelNormaliserRatio
        rw [hConj]
        exact hH _ ⟨hKeep.distancePreserving, hKeep.mapsSublattice⟩
      rw [hSplitφ, hU, hR φ hφ, hComm, hLevelEq]
  exact key (k₀ + 1) m₀ hm₀
end YangMills.Construction.Towers
end
