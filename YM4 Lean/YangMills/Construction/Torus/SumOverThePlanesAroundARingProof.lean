import YangMills.Construction.Lattice.RingsOnThreeAndFourIndicesAndRingKernelsOfOrdersFourAndTwoProof
import YangMills.Construction.LinearAlgebra.PropertiesOfTheFreeCurvaturePropagator
import YangMills.Construction.ResponseInTheExpansion.BoundsOfTheCollinearConnectedLawProof
import YangMills.Construction.Torus.CubesBallsOfTheTorusAndTheirLifts
import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory Tuples FreeRingKernels PeriodicLattice Exterior TestFunctions TorusMetric
namespace RingPlaneSums
theorem propagatorEntriesSymmetric_of_properties
    (hK : Exterior.FreeCurvaturePropagatorProperties) :
    PropagatorEntriesSymmetric := by
  have key : ∀ w : Fin 4 → ℝ, w ≠ 0 → ∀ P Q : AxisPlane,
      bivectorMatrixEntry (freeCurvaturePropagator w) P Q =
        bivectorMatrixEntry (freeCurvaturePropagator w) Q P := by
    intro w hw P Q
    have h := (hK.1 w hw).2.1 (axisBivector P) (axisBivector Q)
    unfold bivectorMatrixEntry
    rw [h]
    exact real_inner_comm _ _
  refine ⟨fun w hw => ⟨key w hw, (hK.1 w hw).1⟩, fun x y hxy P Q => ?_⟩
  have hw : x - y ≠ 0 := sub_ne_zero.mpr hxy
  rw [show y - x = -(x - y) by abel, (hK.1 _ hw).1, key _ hw]
theorem bivectorMatrixEntry_mul (A B : Module.End ℝ Bivector) (P Q : AxisPlane) :
    bivectorMatrixEntry (A * B) P Q = ∑ R, bivectorMatrixEntry A P R * bivectorMatrixEntry B R Q := by
  classical
  simp only [bivectorMatrixEntry_eq_toMatrix]
  rw [Module.End.mul_eq_comp,
    LinearMap.toMatrix_comp axisBivectorBasis.toBasis axisBivectorBasis.toBasis
      axisBivectorBasis.toBasis,
    Matrix.mul_apply]
theorem bivectorTrace_mul_four (S : Fin 4 → Module.End ℝ Bivector) :
    bivectorTrace (S 0 * (S 1 * (S 2 * S 3))) =
      ∑ Q : Fin 4 → AxisPlane, ∏ k : Fin 4,
        bivectorMatrixEntry (S k) (Q k) (Q (finRotate 4 k)) := by
  let e : (Fin 4 → AxisPlane) ≃ AxisPlane × AxisPlane × AxisPlane × AxisPlane :=
    { toFun := fun Q => (Q 0, Q 1, Q 2, Q 3)
      invFun := fun t => ![t.1, t.2.1, t.2.2.1, t.2.2.2]
      left_inv := fun Q => by
        funext i
        fin_cases i <;> rfl
      right_inv := fun _ => rfl }
  have hr0 : finRotate 4 0 = 1 := by decide
  have hr1 : finRotate 4 1 = 2 := by decide
  have hr2 : finRotate 4 2 = 3 := by decide
  have hr3 : finRotate 4 3 = 0 := by decide
  rw [Fintype.sum_equiv e _
    (fun t => bivectorMatrixEntry (S 0) t.1 t.2.1 * (bivectorMatrixEntry (S 1) t.2.1 t.2.2.1 *
      (bivectorMatrixEntry (S 2) t.2.2.1 t.2.2.2 * bivectorMatrixEntry (S 3) t.2.2.2 t.1))) (fun Q => by
        simp only [Fin.prod_univ_four, hr0, hr1, hr2, hr3]
        show _ = bivectorMatrixEntry (S 0) (Q 0) (Q 1) * (bivectorMatrixEntry (S 1) (Q 1) (Q 2) *
          (bivectorMatrixEntry (S 2) (Q 2) (Q 3) * bivectorMatrixEntry (S 3) (Q 3) (Q 0)))
        ring)]
  simp only [Fintype.sum_prod_type]
  unfold bivectorTrace
  simp only [bivectorMatrixEntry_mul, Finset.mul_sum]
def cyclicPropagators (σ : Fin 4 → Fin 4) (y : Fin 4 → Fin 4 → ℝ) (k : Fin 4) :
    Module.End ℝ Bivector :=
  freeCurvaturePropagator (y (σ k) - y (σ (finRotate 4 k)))
theorem cyclicTrace_eq_bivectorTrace (σ : Fin 4 → Fin 4) (y : Fin 4 → Fin 4 → ℝ) :
    cyclicTrace σ y = bivectorTrace
      (cyclicPropagators σ y 0 * (cyclicPropagators σ y 1 *
        (cyclicPropagators σ y 2 * cyclicPropagators σ y 3))) := by
  unfold cyclicTrace cyclicPropagatorProduct
  congr 1
theorem sum_cyclicEntryProduct (σ : Fin 4 → Fin 4) (hσ : IsBijectiveTuple σ)
    (y : Fin 4 → Fin 4 → ℝ) :
    ∑ P : Fin 4 → AxisPlane, cyclicEntryProduct σ y P = cyclicTrace σ y := by
  rw [cyclicTrace_eq_bivectorTrace, bivectorTrace_mul_four (cyclicPropagators σ y)]
  exact Fintype.sum_equiv
    (Equiv.arrowCongr (Equiv.ofBijective σ hσ).symm (Equiv.refl AxisPlane)) _ _
    (fun P => rfl)
theorem planeSumEqCyclicTrace_holds : PlaneSumEqCyclicTrace := by
  refine ⟨fun σ hσ y _ => sum_cyclicEntryProduct σ hσ y, fun y _ => ?_⟩
  unfold freeBoxDensity
  exact Finset.sum_congr rfl fun r _ =>
    (sum_cyclicEntryProduct _ (isBijectiveTuple_standardFourTuple r) y).symm
theorem cyclicTrace_congr {n : ℕ} (σ : Fin n → Fin n) (y y' : Fin n → Fin 4 → ℝ)
    (h : ∀ i j, y i - y j = y' i - y' j) : cyclicTrace σ y = cyclicTrace σ y' := by
  unfold cyclicTrace cyclicPropagatorProduct
  simp only [h]
theorem tracesDependOnDifferences_holds : TracesDependOnDifferences := by
  intro y y' _ h
  refine ⟨fun σ _ => cyclicTrace_congr σ y y' h, ?_⟩
  unfold freeBoxDensity
  exact Finset.sum_congr rfl fun r _ => cyclicTrace_congr _ y y' h
section Lifts
open TorusCubesAndBalls CubesAndBallLifts TorusMeasure
theorem continuous_of_isLipschitzFor {g : (Fin 4 → ℝ) → ℝ} (h : IsLipschitzFor euclidDistR4 g) :
    Continuous g := by apply _root_.YangMills.Construction.TestPairs.continuous_of_isLipschitzFor_r4 <;> assumption
theorem closedBallR4_subset_closedBall (c : Fin 4 → ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    closedBallR4 c ρ ⊆ Metric.closedBall c ρ := by apply _root_.YangMills.SharedProofs.p71595 <;> assumption
variable (s : Conventions.StandingParameters)
theorem isBallLift_closedBallR4 (hG : CubesBallsAndLifts)
    {z : s.Torus} {ρ : ℝ} {c : Fin 4 → ℝ} (hr : IsAdmissibleRadius s.L s.m ρ) (hc : c ∈ liftsOf z) :
    IsBallLift z ρ (closedBallR4 c ρ) :=
  (((hG s).2.2.2.2.2.2.1 z ρ hr.1 hr.2).1 _).2 ⟨c, hc, rfl⟩
theorem liftProperties_closedBallR4 (hG : CubesBallsAndLifts)
    {z : s.Torus} {ρ : ℝ} {c : Fin 4 → ℝ} (hr : IsAdmissibleRadius s.L s.m ρ) (hc : c ∈ liftsOf z) :
    LiftProperties s z ρ (closedBallR4 c ρ) :=
  ((hG s).2.2.2.2.2.2.1 z ρ hr.1 hr.2).2.1 _ (isBallLift_closedBallR4 s hG hr hc)
variable {s}
theorem mem_metricSupport_of_ne {f : s.Torus → ℝ} {u : s.Torus} (h : f u ≠ 0) :
    u ∈ metricSupport f :=
  @subset_closure _ (metricTopology s.L s.m) _ u h
theorem translate_mem_of_ne_zero (hG : CubesBallsAndLifts)
    {z z' : s.Torus} {ρ ρ' : ℝ} {c c' : Fin 4 → ℝ}
    (hr : IsAdmissibleRadius s.L s.m ρ) (hr' : IsAdmissibleRadius s.L s.m ρ')
    (hc : c ∈ liftsOf z) (hc' : c' ∈ liftsOf z') {g : s.Torus → ℝ}
    (hs : metricSupport g ⊆ closedBallTorus z ρ) (hs' : metricSupport g ⊆ closedBallTorus z' ρ')
    {u₀ : s.Torus} {t₀ t₀' : Fin 4 → ℝ} (hu₀ : u₀ ∈ closedBallTorus z ρ)
    (hu₀' : u₀ ∈ closedBallTorus z' ρ')
    (ht₀ : IsLiftWithin (closedBallR4 c ρ) u₀ t₀) (ht₀' : IsLiftWithin (closedBallR4 c' ρ') u₀ t₀')
    {x : Fin 4 → ℝ} (hx : x ∈ closedBallR4 c ρ) (hne : g (proj s x) ≠ 0) :
    x + (t₀' - t₀) ∈ closedBallR4 c' ρ' ∧ proj s (x + (t₀' - t₀)) = proj s x := by
  have F := liftProperties_closedBallR4 s hG hr hc
  have F' := liftProperties_closedBallR4 s hG hr' hc'
  have hu := hs (mem_metricSupport_of_ne hne)
  have hu' := hs' (mem_metricSupport_of_ne hne)
  obtain ⟨w, hw, -⟩ := F'.2.1 _ hu'
  have A := F.2.2 _ hu u₀ hu₀ x t₀ ⟨hx, rfl⟩ ht₀
  have A' := F'.2.2 _ hu' u₀ hu₀' w t₀' hw ht₀'
  have e : x - t₀ = w - t₀' := A'.2.2.2 (x - t₀) A.1 A.2.2.1
  have hw' : x + (t₀' - t₀) = w := by
    calc x + (t₀' - t₀) = (x - t₀) + t₀' := by abel
      _ = (w - t₀') + t₀' := by rw [e]
      _ = w := by abel
  rw [hw']
  exact hw
theorem ballIndicatorLift_eq_zero {c : Fin 4 → ℝ} {ρ : ℝ} {g : s.Torus → ℝ} {x : Fin 4 → ℝ}
    (h : ¬(x ∈ closedBallR4 c ρ ∧ g (proj s x) ≠ 0)) :
    ballIndicatorLift c ρ g x = 0 := by
  unfold ballIndicatorLift
  by_cases hx : x ∈ closedBallR4 c ρ
  · rw [Set.indicator_of_mem hx]
    by_contra hne
    exact h ⟨hx, hne⟩
  · exact Set.indicator_of_notMem hx _
theorem ballIndicatorLift_of_mem {c : Fin 4 → ℝ} {ρ : ℝ} {g : s.Torus → ℝ} {x : Fin 4 → ℝ}
    (hx : x ∈ closedBallR4 c ρ) : ballIndicatorLift c ρ g x = g (proj s x) := by
  unfold ballIndicatorLift
  rw [Set.indicator_of_mem hx]
  rfl
theorem exists_translate_ballIndicatorLift (hG : CubesBallsAndLifts) {n : ℕ}
    {f : Fin n → s.Torus → ℝ} {z z' : s.Torus} {ρ ρ' : ℝ} {c c' : Fin 4 → ℝ}
    (h : SupportsInBall z ρ f) (h' : SupportsInBall z' ρ' f)
    (hc : c ∈ liftsOf z) (hc' : c' ∈ liftsOf z') :
    ∃ b : Fin 4 → ℝ, ∀ i x, ballIndicatorLift c' ρ' (f i) (x + b) = ballIndicatorLift c ρ (f i) x := by
  by_cases hz : ∃ i u, f i u ≠ 0
  · obtain ⟨i₀, u₀, h₀⟩ := hz
    have hu₀ := h.2 i₀ (mem_metricSupport_of_ne h₀)
    have hu₀' := h'.2 i₀ (mem_metricSupport_of_ne h₀)
    obtain ⟨t₀, ht₀, -⟩ := (liftProperties_closedBallR4 s hG h.1 hc).2.1 _ hu₀
    obtain ⟨t₀', ht₀', -⟩ := (liftProperties_closedBallR4 s hG h'.1 hc').2.1 _ hu₀'
    refine ⟨t₀' - t₀, fun i x => ?_⟩
    by_cases hx : x ∈ closedBallR4 c ρ ∧ f i (proj s x) ≠ 0
    · obtain ⟨h1, h2⟩ :=
        translate_mem_of_ne_zero hG h.1 h'.1 hc hc' (h.2 i) (h'.2 i) hu₀ hu₀' ht₀ ht₀' hx.1 hx.2
      rw [ballIndicatorLift_of_mem h1, ballIndicatorLift_of_mem hx.1, h2]
    · rw [ballIndicatorLift_eq_zero hx]
      refine ballIndicatorLift_eq_zero fun hy => hx ?_
      obtain ⟨h1, h2⟩ :=
        translate_mem_of_ne_zero hG h'.1 h.1 hc' hc (h'.2 i) (h.2 i) hu₀' hu₀ ht₀' ht₀ hy.1 hy.2
      have hxb : x + (t₀' - t₀) + (t₀ - t₀') = x := by abel
      rw [hxb] at h1 h2
      exact ⟨h1, by rw [h2]; exact hy.2⟩
  · have hz' : ∀ i u, f i u = 0 := fun i u => by
      by_contra hne
      exact hz ⟨i, u, hne⟩
    refine ⟨0, fun i x => ?_⟩
    rw [ballIndicatorLift_eq_zero (fun hy => hy.2 (hz' i _)),
      ballIndicatorLift_eq_zero (fun hy => hy.2 (hz' i _))]
theorem freeRingKernelAlong_translate {n : ℕ} (σ : Fin n → Fin n)
    {g g' : Fin n → (Fin 4 → ℝ) → ℝ} {b : Fin 4 → ℝ}
    (h : ∀ i x, g' i (x + b) = g i x) :
    freeRingKernelAlong σ g = freeRingKernelAlong σ g' := by
  unfold freeRingKernelAlong
  rw [← integral_add_right_eq_self (μ := volume)
    (fun x : Fin n → Fin 4 → ℝ => (∏ j, g' j (x j)) * cyclicTrace σ x) (fun _ => b)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have ht : cyclicTrace σ (x + fun _ => b) = cyclicTrace σ x :=
    cyclicTrace_congr σ _ _ fun i j => by simp
  simp only [ht, Pi.add_apply, h]
theorem freeBoxKernel_translate {g g' : Fin 4 → (Fin 4 → ℝ) → ℝ} {b : Fin 4 → ℝ}
    (h : ∀ i x, g' i (x + b) = g i x) : freeBoxKernel g = freeBoxKernel g' := by
  unfold freeBoxKernel freeRingKernel
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs with hR
  · exact freeRingKernelAlong_translate _ h
  · rfl
theorem ballIndicatorLift_of_isLipschitzFor (hG : CubesBallsAndLifts)
    {z : s.Torus} {ρ : ℝ} {c : Fin 4 → ℝ} (hr : IsAdmissibleRadius s.L s.m ρ) (hc : c ∈ liftsOf z)
    {g : s.Torus → ℝ} (hg : IsLipschitzFor (euclidDistTorus (ℓ := torusSide s.L s.m)) g)
    (hs : metricSupport g ⊆ closedBallTorus z ρ) :
    Continuous (ballIndicatorLift c ρ g) ∧ HasCompactSupport (ballIndicatorLift c ρ g) ∧
      tsupport (ballIndicatorLift c ρ g) = setLiftWithin (closedBallR4 c ρ) (metricSupport g) := by
  have hB := isBallLift_closedBallR4 s hG hr hc
  have hb : IsBoundedFun g := (hG s).2.2.2.2.2.2.2.1 g hg
  have H := (hG s).2.2.2.2.2.2.2.2 z ρ _ g hB hb hs
  refine ⟨continuous_of_isLipschitzFor (H.2.2.2 hg).1, ?_, H.2.1⟩
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall c ρ) ?_
  intro x hx
  refine closedBallR4_subset_closedBall c hr.1.le ?_
  by_contra hn
  exact hx (ballIndicatorLift_eq_zero fun hy => hn hy.1)
end Lifts
theorem lipschitzQuadBoxKernel_holds (hG : TorusCubesAndBalls.CubesBallsAndLifts)
    (s : Conventions.StandingParameters) : LipschitzQuadBoxKernel s := by
  intro f hf hd z ρ c hS hc
  have hl := fun i => ballIndicatorLift_of_isLipschitzFor hG hS.1 hc (hf i) (hS.2 i)
  refine ⟨fun i => (hl i).1.integrable_of_hasCompactSupport (hl i).2.1, fun i => (hl i).2.1,
    fun i j hij => ?_, ?_⟩
  · show Disjoint _ _
    rw [(hl i).2.2, (hl j).2.2, Set.disjoint_left]
    rintro t ⟨u, hu, -, hut⟩ ⟨w, hw, -, hwt⟩
    have : u = w := hut.symm.trans hwt
    subst this
    exact Set.disjoint_left.mp (hd hij) hu hw
  · obtain ⟨z', ρ', hS', c', hc', hg⟩ :=
      isTupleLift_tupleLift (⟨z, ρ, hS⟩ : SupportsInSomeBall f)
    obtain ⟨b, hb⟩ := exists_translate_ballIndicatorLift hG hS hS' hc hc'
    refine (freeBoxKernel_translate (b := b) fun i x => ?_).symm
    rw [hg i, hb]
section Lattice
variable {L m : ℕ} {j : ℤ}
theorem image_fixFirst :
    (Finset.univ : Finset (Equiv.Perm (TailPosition 4))).image fixFirst =
      {![0, 1, 2, 3], ![0, 3, 2, 1], ![0, 1, 3, 2], ![0, 2, 3, 1], ![0, 2, 1, 3],
        ![0, 3, 1, 2]} := by
  decide +kernel
theorem fixFirst_injective :
    Function.Injective (fixFirst : Equiv.Perm (TailPosition 4) → Fin 4 → Fin 4) := by apply _root_.YangMills.SharedProofs.p29512 <;> assumption
theorem sum_fixFirst {M : Type*} [AddCommMonoid M] (G : (Fin 4 → Fin 4) → M) :
    ∑ τ : Equiv.Perm (TailPosition 4), G (fixFirst τ) =
      G ![0, 1, 2, 3] + (G ![0, 3, 2, 1] + (G ![0, 1, 3, 2] + (G ![0, 2, 3, 1] +
        (G ![0, 2, 1, 3] + G ![0, 3, 1, 2])))) := by
  rw [← Finset.sum_image (f := G) (g := fixFirst)
    (fun _ _ _ _ h => fixFirst_injective h), image_fixFirst]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_pair (by decide)]
theorem cyclicKernel_orderFour (C : Plaquette L m j → Plaquette L m j → ℝ)
    (hC : IsSymmetricKernel C) (φ : Fin 4 → Plaquette L m j → ℝ) :
    cyclicKernel C φ = ∑ r : Fin 3, ∑ᶠ p : Fin 4 → Plaquette L m j,
      (∏ i, φ i (p i)) *
        ∏ k : Fin 4, C (p (standardFourTuple r k)) (p (standardFourTuple r (finRotate 4 k))) := by
  have hr0 : finRotate 4 0 = 1 := by decide
  have hr1 : finRotate 4 1 = 2 := by decide
  have hr2 : finRotate 4 2 = 3 := by decide
  have hr3 : finRotate 4 3 = 0 := by decide
  set G : (Fin 4 → Fin 4) → ℝ := fun σ => ∑ᶠ p : Fin 4 → Plaquette L m j,
    (∏ i, φ i (p i)) * ∏ i, C (p (σ i)) (p (σ (finRotate 4 i))) with hG
  have rev : ∀ a b c d : Fin 4, G ![a, b, c, d] = G ![a, d, c, b] := by
    intro a b c d
    refine finsum_congr fun p => ?_
    congr 1
    simp only [Fin.prod_univ_four, hr0, hr1, hr2, hr3]
    simp only [Matrix.cons_val]
    rw [hC (p b) (p a), hC (p c) (p b), hC (p d) (p c), hC (p a) (p d)]
    ring
  have h0 : G ![0, 3, 2, 1] = G ![0, 1, 2, 3] := (rev 0 3 2 1)
  have h1 : G ![0, 2, 3, 1] = G ![0, 1, 3, 2] := (rev 0 2 3 1)
  have h2 : G ![0, 3, 1, 2] = G ![0, 2, 1, 3] := (rev 0 3 1 2)
  have hs : ∑ τ : Equiv.Perm (TailPosition 4), G (fixFirst τ) =
      2 * (G ![0, 1, 2, 3] + G ![0, 1, 3, 2] + G ![0, 2, 1, 3]) := by
    rw [sum_fixFirst G, h0, h1, h2]
    ring
  have hk : cyclicKernel C φ = 1 / 2 * ∑ τ : Equiv.Perm (TailPosition 4), G (fixFirst τ) := rfl
  rw [hk, hs, Fin.sum_univ_three]
  have e0 : standardFourTuple 0 = ![0, 1, 2, 3] := rfl
  have e1 : standardFourTuple 1 = ![0, 1, 3, 2] := rfl
  have e2 : standardFourTuple 2 = ![0, 2, 1, 3] := rfl
  simp only [e0, e1, e2]
  show _ = G ![0, 1, 2, 3] + G ![0, 1, 3, 2] + G ![0, 2, 1, 3]
  ring
theorem isLinearMap_cyclicKernel [Finite (Plaquette L m j)] {n : ℕ}
    (C : Plaquette L m j → Plaquette L m j → ℝ) (φ : Fin n → Plaquette L m j → ℝ) (i : Fin n) :
    IsLinearMap ℝ fun ψ : Plaquette L m j → ℝ => cyclicKernel C (Function.update φ i ψ) := by
  classical
  have := Fintype.ofFinite (Plaquette L m j)
  set T : Equiv.Perm (TailPosition n) → (Fin n → Plaquette L m j) → ℝ := fun τ p =>
    (∏ k ∈ Finset.univ.erase i, φ k (p k)) *
      ∏ k, C (p (fixFirst τ k)) (p (fixFirst τ (finRotate n k))) with hT
  have key : ∀ ψ : Plaquette L m j → ℝ, cyclicKernel C (Function.update φ i ψ) =
      1 / 2 * ∑ τ, ∑ p, ψ (p i) * T τ p := by
    intro ψ
    unfold cyclicKernel
    congr 1
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), Function.update_self, hT,
      mul_assoc]
    congr 2
    refine Finset.prod_congr rfl fun k hk => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  constructor
  · intro ψ ψ'
    simp only [key, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]
  · intro a ψ
    simp only [key, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun p _ => ?_
    ring
end Lattice
theorem boxKernelRingExpansion_holds (hR : CyclicKernels.CyclicKernelOrderFour)
    (S : Conventions.StandingParameters) : BoxKernelRingExpansion S := by
  intro s _
  have : Finite (Plaquette S.L S.m ((S.K : ℕ) : ℤ)) := (hR.2 S).1
  exact ⟨fun φ => cyclicKernel_orderFour _ (isSymmetricKernel_backgroundCurvatureCovariance S s) φ,
    fun φ i => isLinearMap_cyclicKernel _ φ i⟩
theorem ringPlaneSumStatement_holds (hK : Exterior.FreeCurvaturePropagatorProperties)
    (hG : TorusCubesAndBalls.CubesBallsAndLifts)
    (hR : CyclicKernels.CyclicKernelOrderFour) : RingPlaneSumStatement :=
  ⟨propagatorEntriesSymmetric_of_properties hK, planeSumEqCyclicTrace_holds,
    tracesDependOnDifferences_holds, lipschitzQuadBoxKernel_holds hG,
    boxKernelRingExpansion_holds hR⟩
end RingPlaneSums
end YangMills.Construction
end
