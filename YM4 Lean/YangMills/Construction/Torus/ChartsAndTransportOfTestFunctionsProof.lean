import YangMills.Construction.Torus.ChartsOfSmallOpenSetsAndTransportOfFunctions
import YangMills.Construction.Torus.GradientNormOfAFunctionOfOnePoint
import Mathlib
import YangMills.Construction.Torus.DistancesAndLiftsOfTorusOrFourSpace
import YangMills.Construction.Torus.MultilinearFormBoundedInTheGradientNorms
import YangMills.Construction.Torus.RestrictionsSumsProductsAndTensorsOfTestFunctions
import YangMills.Construction.Torus.SeparationSpacesAndProductsOverDisjointSetsProof
set_option autoImplicit false

section
open Set YangMills.Construction.TorusMetric
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.AmbientPoints
variable {s : Conventions.StandingParameters} {E : Ambient} {n : ℕ}
def IsLinearBijOnWithInv (𝕜 : Type*) {X Y : Type*} [Semiring 𝕜] [AddCommMonoid X]
    [AddCommMonoid Y] [Module 𝕜 X] [Module 𝕜 Y] (f : X → Y) (g : Y → X) (A : Set X) (B : Set Y) :
    Prop :=
  BijOn f A B ∧ InvOn g f A B ∧ (∀ x ∈ A, ∀ x' ∈ A, f (x + x') = f x + f x') ∧
    ∀ (c : 𝕜), ∀ x ∈ A, f (c • x) = c • f x
def boxChartInv (V : Fin n → Set (Pt s E)) (z : Fin n → Fin 4 → ℝ) (y : Tuple s E n) :
    Tuple s .euclidean n :=
  open Classical in
  if h : ∃ u ∈ boxChartDomain V z, boxChart s E z u = y then h.choose
  else fun _ => (0 : Fin 4 → ℝ)
def distribPullback (V : Fin n → Set (Pt s E)) (z : Fin n → Fin 4 → ℝ)
    (T : testFns (boxChartDomain V z) → ℂ) : testFns (boxSet V) → ℂ :=
  fun F =>
    open Classical in
    if h : chartPullback V z F.1 ∈ testFns (boxChartDomain V z) then T ⟨_, h⟩ else 0
def distribPushforward (V : Fin n → Set (Pt s E)) (z : Fin n → Fin 4 → ℝ)
    (T' : testFns (boxSet V) → ℂ) : testFns (boxChartDomain V z) → ℂ :=
  fun H =>
    open Classical in
    if h : chartPushforward V z H.1 ∈ testFns (boxSet V) then T' ⟨_, h⟩ else 0
def coordSetTestFns (V : Fin n → Set (Pt s E)) (i : Fin n) : Set (Tuple s E 1 → ℂ) :=
  testFns (boxSet fun _ : Fin 1 => V i)
def tensorSpan (V : Fin n → Set (Pt s E)) : Set (Tuple s E n → ℂ) :=
  {F | ∃ (m : ℕ) (φ : Fin m → Fin n → Pt s E → ℂ),
    (∀ k i, ofSinglePoint (φ k i) ∈ coordSetTestFns V i) ∧ F = ∑ k, tensorProd (φ k)}
def CoordChartIsometry (V : Fin n → Set (Pt s E)) (z : Fin n → Fin 4 → ℝ) (i : Fin n) :
    Prop :=
  IsOpen (localChartDomain (V i) (z i)) ∧ (0 : Fin 4 → ℝ) ∈ localChartDomain (V i) (z i) ∧
    BijOn (localChart s E (z i)) (localChartDomain (V i) (z i)) (V i) ∧
    (∀ u ∈ localChartDomain (V i) (z i), ∀ u' ∈ localChartDomain (V i) (z i),
      pointDist s E (localChart s E (z i) u) (localChart s E (z i) u') = pointDist s .euclidean u u') ∧
    localChartDomain (V i) (z i) ⊆ {u : Fin 4 → ℝ | euclidNormVec u ≤ (maxDiam V).toReal} ∧
    V i ⊆ closedBall s E (proj s E (z i)) (maxDiam V).toReal
def BoxChartIsometry (V : Fin n → Set (Pt s E)) (z : Fin n → Fin 4 → ℝ) : Prop :=
  IsOpen (boxChartDomain V z) ∧ IsOpen (boxSet V) ∧
    BijOn (boxChart s E z) (boxChartDomain V z) (boxSet V) ∧
    InvOn (boxChartInv V z) (boxChart s E z) (boxChartDomain V z) (boxSet V) ∧
    (∀ u ∈ boxChartDomain V z, ∀ u' ∈ boxChartDomain V z,
      supDist (boxChart s E z u) (boxChart s E z u') = supDist u u') ∧
    ContinuousOn (boxChart s E z) (boxChartDomain V z) ∧
    ContinuousOn (boxChartInv V z) (boxSet V) ∧
    (∀ K, K ⊆ boxChartDomain V z → IsCompact K → IsCompact (boxChart s E z '' K)) ∧
    ∀ K, K ⊆ boxSet V → IsCompact K → IsCompact (boxChartInv V z '' K)
def PullbackPreservesCn (V : Fin n → Set (Pt s E)) (z : Fin n → Fin 4 → ℝ) : Prop :=
  ∀ (ν : ℕ∞) (F : Tuple s E n → ℂ), IsCn ν F → IsCompact (closedSupport F) →
    closedSupport F ⊆ boxSet V →
      IsCn ν (chartPullback V z F) ∧
        closedSupport (chartPullback V z F) = boxChartInv V z '' closedSupport F ∧
        IsCompact (boxChartInv V z '' closedSupport F) ∧
        boxChartInv V z '' closedSupport F ⊆ boxChartDomain V z ∧
        (∀ α : PowerSeries.MultiIndex (4 * n), (α.order : ℕ∞) ≤ ν →
          multiDeriv α (chartPullback V z F) = chartPullback V z (multiDeriv α F)) ∧
        chartPushforward V z (chartPullback V z F) = F
def PushforwardPreservesCn (V : Fin n → Set (Pt s E)) (z : Fin n → Fin 4 → ℝ) : Prop :=
  ∀ (ν : ℕ∞) (H : Tuple s .euclidean n → ℂ), IsCn ν H → IsCompact (closedSupport H) →
    closedSupport H ⊆ boxChartDomain V z →
      IsCn ν (chartPushforward V z H) ∧
        closedSupport (chartPushforward V z H) = boxChart s E z '' closedSupport H ∧
        IsCompact (boxChart s E z '' closedSupport H) ∧
        boxChart s E z '' closedSupport H ⊆ boxSet V ∧
        (∀ α : PowerSeries.MultiIndex (4 * n), (α.order : ℕ∞) ≤ ν →
          multiDeriv α (chartPushforward V z H) = chartPushforward V z (multiDeriv α H)) ∧
        chartPullback V z (chartPushforward V z H) = H
def TransportTestFnsDistribs (V : Fin n → Set (Pt s E))
    (z : Fin n → Fin 4 → ℝ) : Prop :=
  IsLinearBijOnWithInv ℂ (chartPullback V z) (chartPushforward V z)
      (testFns (boxSet V)) (boxTestFns V z) ∧
    (∀ F ∈ testFns (boxSet V),
      (∀ ν : ℕ, cnNorm ν (chartPullback V z F) = cnNorm ν F) ∧
        closedSupport (chartPullback V z F) = boxChartInv V z '' closedSupport F) ∧
    (∀ (Fs : ℕ+ → Tuple s E n → ℂ) (F : Tuple s E n → ℂ),
      (∀ t, Fs t ∈ testFns (boxSet V)) → F ∈ testFns (boxSet V) →
        (TestFnTendsto (boxSet V) Fs F ↔
          TestFnTendsto (boxChartDomain V z) (fun t => chartPullback V z (Fs t))
            (chartPullback V z F))) ∧
    (∀ T ∈ boxDistribs V z,
      distribPullback V z T ∈ distribs (boxSet V) ∧
        ∀ ν₀ : ℕ, HasOrderLE ν₀ T → HasOrderLE ν₀ (distribPullback V z T)) ∧
    ∀ T' ∈ distribs (boxSet V), distribPushforward V z T' ∈ boxDistribs V z
def TransportCoord (V : Fin n → Set (Pt s E)) (z : Fin n → Fin 4 → ℝ) (i : Fin n) : Prop :=
  IsLinearBijOnWithInv ℂ (coordPullback V z i) (coordPushforward V z i)
      (coordSetTestFns V i) (coordTestFns V z i) ∧
    (∀ F ∈ coordSetTestFns V i, (∀ y, (F y).im = 0) →
      ∀ u, (coordPullback V z i F u).im = 0) ∧
    (∀ H ∈ coordTestFns V z i, (∀ u, (H u).im = 0) →
      ∀ y, (coordPushforward V z i H y).im = 0) ∧
    IsLinearBijOnWithInv ℝ (singlePushforward V z i) (singlePullback V z i)
      (coordC1CompactSupport V z i) (c1CompactSupportIn (V i)) ∧
    ∀ g ∈ coordC1CompactSupport V z i,
      c1GradNorm (fun y => ((singlePushforward V z i g y : ℝ) : ℂ)) =
        c1GradNorm (fun u => ((g u : ℝ) : ℂ))
def TransportTensor (V : Fin n → Set (Pt s E)) (z : Fin n → Fin 4 → ℝ) : Prop :=
  (∀ φ : Fin n → Pt s E → ℂ, (∀ i, ofSinglePoint (φ i) ∈ coordSetTestFns V i) →
    chartPullback V z (tensorProd φ) = tensorProd fun i => singlePullback V z i (φ i)) ∧
  ∀ g : Fin n → Pt s .euclidean → ℂ,
    (∀ i, ofSinglePoint (g i) ∈ coordTestFns V z i) →
      chartPushforward V z (tensorProd g) = tensorProd fun i => singlePushforward V z i (g i)
def ChartTransport.statement : Prop :=
  ∀ (s : Conventions.StandingParameters) (E : Ambient) (n : ℕ) (V : Fin n → Set (Pt s E)),
    IsSmallOpenTuple V →
      (∃ z, IsBasePoint V z) ∧
        ∀ z, IsBasePoint V z →
          (0 < maxDiam V ∧ maxDiam V < injRadius s E) ∧
          (∀ i, CoordChartIsometry V z i) ∧
          BoxChartIsometry V z ∧
          PullbackPreservesCn V z ∧
          PushforwardPreservesCn V z ∧
          TransportTestFnsDistribs V z ∧
          (∀ i, TransportCoord V z i) ∧
          TransportTensor V z ∧
          DenseInTestFns (boxSet V) (tensorSpan V)
end YangMills.Construction.AmbientPoints
end
end

open Set Filter YangMills.Construction.TorusMetric
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction.AmbientPoints.ChartTransportProof
section Partials
variable {D : ℕ}
theorem partialDeriv_congr {G G₀ : (Fin D → ℝ) → ℂ} {x : Fin D → ℝ} (h : G =ᶠ[𝓝 x] G₀)
    (j : Fin D) : partialDeriv j G =ᶠ[𝓝 x] partialDeriv j G₀ := by
  filter_upwards [h.eventuallyEq_nhds] with y hy
  exact hy.lineDeriv_eq
theorem iterate_partialDeriv_congr {G G₀ : (Fin D → ℝ) → ℂ} {x : Fin D → ℝ}
    (h : G =ᶠ[𝓝 x] G₀) (j : Fin D) (k : ℕ) :
    (partialDeriv j)^[k] G =ᶠ[𝓝 x] (partialDeriv j)^[k] G₀ := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact partialDeriv_congr ih j
theorem iteratedPartial_congr {G G₀ : (Fin D → ℝ) → ℂ} {x : Fin D → ℝ} (h : G =ᶠ[𝓝 x] G₀)
    (α : PowerSeries.MultiIndex D) : iteratedPartial α G =ᶠ[𝓝 x] iteratedPartial α G₀ := by
  have key : ∀ l : List (Fin D),
      l.foldr (fun j H => (partialDeriv j)^[α j] H) G =ᶠ[𝓝 x]
        l.foldr (fun j H => (partialDeriv j)^[α j] H) G₀ := by
    intro l
    induction l with
    | nil => exact h
    | cons j l ih => exact iterate_partialDeriv_congr ih j (α j)
  exact key _
theorem partialDeriv_comp_add (c : Fin D → ℝ) (G : (Fin D → ℝ) → ℂ) (j : Fin D) :
    partialDeriv j (fun y => G (y + c)) = fun y => partialDeriv j G (y + c) := by
  funext y
  simp only [partialDeriv, lineDeriv]
  congr 1
  funext t
  congr 1
  abel
theorem iterate_partialDeriv_comp_add (c : Fin D → ℝ) (G : (Fin D → ℝ) → ℂ) (j : Fin D)
    (k : ℕ) : (partialDeriv j)^[k] (fun y => G (y + c)) =
      fun y => (partialDeriv j)^[k] G (y + c) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, partialDeriv_comp_add]
theorem iteratedPartial_comp_add (c : Fin D → ℝ) (G : (Fin D → ℝ) → ℂ)
    (α : PowerSeries.MultiIndex D) :
    iteratedPartial α (fun y => G (y + c)) = fun y => iteratedPartial α G (y + c) := by
  have key : ∀ l : List (Fin D),
      l.foldr (fun j H => (partialDeriv j)^[α j] H) (fun y => G (y + c)) =
        fun y => l.foldr (fun j H => (partialDeriv j)^[α j] H) G (y + c) := by
    intro l
    induction l with
    | nil => rfl
    | cons j l ih =>
      simp only [List.foldr_cons]
      rw [ih, iterate_partialDeriv_comp_add]
  exact key _
theorem partialDeriv_const_zero (j : Fin D) :
    partialDeriv j (fun _ : Fin D → ℝ => (0 : ℂ)) = fun _ => 0 := by
  funext y
  simp [partialDeriv, lineDeriv]
theorem iteratedPartial_const_zero (α : PowerSeries.MultiIndex D) :
    iteratedPartial α (fun _ : Fin D → ℝ => (0 : ℂ)) = fun _ => 0 := by
  have hit : ∀ (j : Fin D) (k : ℕ),
      (partialDeriv j)^[k] (fun _ : Fin D → ℝ => (0 : ℂ)) = fun _ => 0 := by
    intro j k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, partialDeriv_const_zero]
  have key : ∀ l : List (Fin D),
      l.foldr (fun j H => (partialDeriv j)^[α j] H) (fun _ : Fin D → ℝ => (0 : ℂ)) =
        fun _ => 0 := by
    intro l
    induction l with
    | nil => rfl
    | cons j l ih =>
      simp only [List.foldr_cons]
      rw [ih, hit]
  exact key _
theorem continuousPartialsUpTo_comp_add (c : Fin D → ℝ) (m : ℕ) {G : (Fin D → ℝ) → ℂ}
    (h : ContinuousPartialsUpTo univ m G) :
    ContinuousPartialsUpTo univ m (fun y => G (y + c)) := by
  induction m generalizing G with
  | zero =>
    exact (h.continuousOn.comp_continuous (continuous_add_const c)
      fun _ => mem_univ _).continuousOn
  | succ m ih =>
    refine ⟨(h.1.comp_continuous (continuous_add_const c) fun _ => mem_univ _).continuousOn,
      fun j => ⟨fun x _ => ?_, ?_⟩⟩
    · have hd : DifferentiableAt ℝ (fun t : ℝ => G (x + c + t • Pi.single j (1 : ℝ))) 0 :=
        (h.2 j).1 (x + c) (mem_univ _)
      have hshift : (fun t : ℝ => G (x + c + t • Pi.single j (1 : ℝ))) =
          fun t : ℝ => G (x + t • Pi.single j (1 : ℝ) + c) := by
        ext t
        rw [add_right_comm]
      show DifferentiableAt ℝ (fun t : ℝ => G (x + t • Pi.single j (1 : ℝ) + c)) 0
      rw [← hshift]
      exact hd
    · simpa only [partialDeriv_comp_add] using ih (h.2 j).2
theorem continuousPartialsUpTo_const_zero (m : ℕ) :
    ContinuousPartialsUpTo univ m (fun _ : Fin D → ℝ => (0 : ℂ)) := by apply _root_.YangMills.Construction.AmbientPoints.SeparationAndProductFacts.contPartials_const_zero <;> assumption
theorem continuousPartialsUpTo_of_locally_eq (m : ℕ) {G : (Fin D → ℝ) → ℂ}
    (h : ∀ x, ∃ G₀, ContinuousPartialsUpTo univ m G₀ ∧ G =ᶠ[𝓝 x] G₀) :
    ContinuousPartialsUpTo univ m G := by
  have cont : ∀ {k : ℕ} {H : (Fin D → ℝ) → ℂ},
      (∀ x, ∃ H₀, ContinuousPartialsUpTo univ k H₀ ∧ H =ᶠ[𝓝 x] H₀) → ContinuousOn H univ := by
    intro k H hH
    rw [continuousOn_univ, continuous_iff_continuousAt]
    intro x
    rcases hH x with ⟨H₀, hk, hx⟩
    exact (hk.continuousOn.continuousAt univ_mem).congr hx.symm
  induction m generalizing G with
  | zero => exact cont h
  | succ m ih =>
    refine ⟨cont h, fun j => ⟨fun x _ => ?_, ih fun x => ?_⟩⟩
    · rcases h x with ⟨G₀, hG₀, hx⟩
      exact hx.lineDifferentiableAt_iff.mpr ((hG₀.2 j).1 x (mem_univ x))
    · rcases h x with ⟨G₀, hG₀, hx⟩
      exact ⟨partialDeriv j G₀, (hG₀.2 j).2, partialDeriv_congr hx j⟩
end Partials
section Transfer
variable {s : Conventions.StandingParameters} {n : ℕ}
theorem isCn_and_multiDeriv_of_locally_translate {X Y : Ambient}
    (hX : TupleDerivProps s X n) (hY : TupleDerivProps s Y n)
    (ν : ℕ∞) (F : Tuple s X n → ℂ) (hF : IsCn ν F) (F' : Tuple s Y n → ℂ)
    (W : (Tuple s X n → ℂ) → Tuple s Y n → ℂ)
    (hloc : ∀ x : Fin (4 * n) → ℝ,
      (∃ c : Fin (4 * n) → ℝ,
        (∀ᶠ x' in 𝓝 x, F' (tupleProj s Y n x') = F (tupleProj s X n (x' + c))) ∧
          ∀ H, W H (tupleProj s Y n x) = H (tupleProj s X n (x + c))) ∨
      ((∀ᶠ x' in 𝓝 x, F' (tupleProj s Y n x') = 0) ∧
        ∀ α : PowerSeries.MultiIndex (4 * n), (α.order : ℕ∞) ≤ ν →
          W (multiDeriv α F) (tupleProj s Y n x) = 0)) :
    IsCn ν F' ∧ ∀ α : PowerSeries.MultiIndex (4 * n), (α.order : ℕ∞) ≤ ν →
      multiDeriv α F' = W (multiDeriv α F) := by
  have hclass : IsCn ν F' := by
    refine ⟨isOpen_univ, fun m hm => continuousPartialsUpTo_of_locally_eq m fun x => ?_⟩
    rcases hloc x with ⟨c, h1, -⟩ | ⟨h1, -⟩
    · exact ⟨fun y => (F ∘ tupleProj s X n) (y + c),
        continuousPartialsUpTo_comp_add c m (hF.2 m hm), h1⟩
    · exact ⟨fun _ => 0, continuousPartialsUpTo_const_zero m, h1⟩
  refine ⟨hclass, fun α hα => ?_⟩
  obtain ⟨H', hH', -⟩ := ((hY ν F' hclass).1 α hα).1
  obtain ⟨H, hH, -⟩ := ((hX ν F hF).1 α hα).1
  have hc' := multiDeriv_comp_tupleProj ⟨H', hH'⟩
  have hc := multiDeriv_comp_tupleProj ⟨H, hH⟩
  funext y
  obtain ⟨x, rfl⟩ := tupleProj_surjective s Y n y
  have h1 : multiDeriv α F' (tupleProj s Y n x) =
      iteratedPartial α (F' ∘ tupleProj s Y n) x := congrFun hc' x
  rw [h1]
  rcases hloc x with ⟨c, he, hW⟩ | ⟨he, hW⟩
  · have h2 := (iteratedPartial_congr (G := F' ∘ tupleProj s Y n)
      (G₀ := fun y => (F ∘ tupleProj s X n) (y + c)) he α).self_of_nhds
    rw [h2, iteratedPartial_comp_add, hW]
    exact (congrFun hc (x + c)).symm
  · have h2 := (iteratedPartial_congr (G := F' ∘ tupleProj s Y n)
      (G₀ := fun _ => 0) he α).self_of_nhds
    rw [h2, iteratedPartial_const_zero, hW α hα]
end Transfer
section Charts
variable {s : Conventions.StandingParameters} {E : Ambient} {n : ℕ} {V : Fin n → Set (Pt s E)}
  {z : Fin n → Fin 4 → ℝ}
theorem continuous_euclidNormVec : Continuous (fun u : Pt s .euclidean => euclidNormVec u) := by
  have key : ∀ o : Pt s .euclidean, Continuous fun u : Pt s .euclidean => dist u o :=
    fun o => continuous_id.dist continuous_const
  have h : ∀ v : Fin 4 → ℝ, euclidNormVec (v - 0) = euclidNormVec v := fun v => by rw [sub_zero]
  exact (key (0 : Fin 4 → ℝ)).congr fun u => h u
theorem continuous_localChart (f : DistanceFacts.MetricFacts s E) (b : Fin 4 → ℝ) :
    Continuous (fun u : Pt s .euclidean => localChart s E b u) := by
  have key : ∀ u u' : Fin 4 → ℝ, pointDist s E (localChart s E b u) (localChart s E b u') ≤
      euclidNormVec (u - u') := by
    intro u u'
    have h := f.pointDist_proj_le (b + u) (b + u')
    rw [add_sub_add_left_eq_sub] at h
    exact h
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun u u' => ?_).continuous
  simp only [NNReal.coe_one, one_mul]
  exact key u u'
theorem pointDist_le_maxDiam {i : Fin n} {a b : Pt s E} (ha : a ∈ V i) (hb : b ∈ V i) :
    ENNReal.ofReal (pointDist s E a b) ≤ maxDiam V :=
  ((le_iSup₂_of_le a ha (le_iSup₂_of_le b hb le_rfl) :
    ENNReal.ofReal (pointDist s E a b) ≤ setDiam s E (V i))).trans
      (le_iSup (fun i => setDiam s E (V i)) i)
theorem maxDiam_lt_injRadius (hV : IsSmallOpenTuple V) :
    maxDiam V < injRadius s E := by
  obtain ⟨⟨i, hi⟩, -⟩ := isGreatest_maxDiam hV.1 V
  have hi' : setDiam s E (V i) = maxDiam V := hi
  rw [← hi']
  exact (hV.2 i).2.2
theorem maxDiam_pos (f : DistanceFacts.MetricFacts s E) (hV : IsSmallOpenTuple V) :
    0 < maxDiam V := by
  have i : Fin n := ⟨0, hV.1⟩
  exact lt_of_lt_of_le (f.setDiam_pos _ (hV.2 i).2.1 (hV.2 i).1)
    (le_iSup (fun i => setDiam s E (V i)) i)
theorem pointDist_le_maxDiam_toReal (hV : IsSmallOpenTuple V) {i : Fin n} {a b : Pt s E}
    (ha : a ∈ V i) (hb : b ∈ V i) : pointDist s E a b ≤ (maxDiam V).toReal :=
  (ENNReal.ofReal_le_iff_le_toReal (maxDiam_lt_injRadius hV).ne_top).mp
    (pointDist_le_maxDiam ha hb)
theorem isOpen_localChartDomain (f : DistanceFacts.MetricFacts s E) {A : Set (Pt s E)}
    (hA : IsOpen A) (b : Fin 4 → ℝ) : IsOpen (localChartDomain A b) := by
  have h : localChartDomain A b =
      {u : Pt s .euclidean | ENNReal.ofReal (euclidNormVec u) < injRadius s E} ∩
        (fun u : Pt s .euclidean => localChart s E b u) ⁻¹' A := rfl
  rw [h]
  exact (isOpen_lt (ENNReal.continuous_ofReal.comp continuous_euclidNormVec)
    continuous_const).inter (hA.preimage (continuous_localChart f b))
theorem pointDist_localChart (f : DistanceFacts.MetricFacts s E) {A : Set (Pt s E)}
    {b : Fin 4 → ℝ} {u u' : Fin 4 → ℝ} (hu : u ∈ localChartDomain A b)
    (hu' : u' ∈ localChartDomain A b) :
    pointDist s E (localChart s E b u) (localChart s E b u') = pointDist s .euclidean u u' := by
  have htri : euclidNormVec (u - u') ≤ euclidNormVec u + euclidNormVec u' := by
    have h := euclidNormVec_sub_le u 0 u'
    rw [sub_zero, euclidNormVec_sub_comm 0 u', sub_zero] at h
    exact h
  have hlt : ENNReal.ofReal (euclidNormVec ((b + u) - (b + u'))) < 2 * injRadius s E := by
    rw [add_sub_add_left_eq_sub, two_mul]
    exact lt_of_le_of_lt ((ENNReal.ofReal_le_ofReal htri).trans ENNReal.ofReal_add_le)
      (ENNReal.add_lt_add hu.1 hu'.1)
  have h := f.pointDist_proj_eq (b + u) (b + u') hlt
  rw [add_sub_add_left_eq_sub] at h
  exact h
theorem coordChartIsometry_of_small (f : DistanceFacts.MetricFacts s E)
    (hV : IsSmallOpenTuple V) (hz : IsBasePoint V z) (i : Fin n) :
    CoordChartIsometry V z i := by
  have hzero : (0 : Fin 4 → ℝ) ∈ localChartDomain (V i) (z i) := by
    refine ⟨?_, ?_⟩
    · have h0 : euclidNormVec (0 : Fin 4 → ℝ) = 0 := by simp [euclidNormVec]
      rw [h0, ENNReal.ofReal_zero]
      exact lt_of_le_of_lt zero_le (maxDiam_lt_injRadius hV)
    · rw [add_zero]
      exact hz i
  have hinj : InjOn (localChart s E (z i)) (localChartDomain (V i) (z i)) := by
    intro u hu u' hu' e
    have h := pointDist_localChart f hu hu'
    rw [e, pointDist_self] at h
    exact eq_of_pointDist_eq_zero .euclidean h.symm
  have hsurj : SurjOn (localChart s E (z i)) (localChartDomain (V i) (z i)) (V i) := by
    intro y hy
    obtain ⟨x, hx, hd⟩ := f.exists_lift_pointDist (z i) y
    have hx' : proj s E x = y := hx
    have hlen : euclidNormVec (x - z i) = pointDist s E (proj s E (z i)) y := by
      rw [euclidNormVec_sub_comm, hd]
    refine ⟨x - z i, ⟨?_, ?_⟩, ?_⟩
    · rw [hlen]
      exact lt_of_le_of_lt (pointDist_le_maxDiam (hz i) hy) (maxDiam_lt_injRadius hV)
    · rw [add_sub_cancel, hx']
      exact hy
    · change proj s E (z i + (x - z i)) = y
      rw [add_sub_cancel, hx']
  refine ⟨isOpen_localChartDomain f (hV.2 i).1 _, hzero, ⟨mapsTo_localChart _ _, hinj, hsurj⟩,
    fun u hu u' hu' => pointDist_localChart f hu hu', ?_, ?_⟩
  · intro u hu
    have h := pointDist_localChart f hu hzero
    have hlen : ∀ v : Fin 4 → ℝ, euclidNormVec (v - 0) = euclidNormVec v :=
      fun v => by rw [sub_zero]
    have h' : pointDist s .euclidean u (0 : Fin 4 → ℝ) = euclidNormVec u := hlen u
    rw [h'] at h
    change euclidNormVec u ≤ _
    rw [← h]
    exact pointDist_le_maxDiam_toReal hV hu.2 hzero.2
  · intro y hy
    exact pointDist_le_maxDiam_toReal hV hy (hz i)
theorem bijOn_boxChart (h : ∀ i, CoordChartIsometry V z i) :
    BijOn (boxChart s E z) (boxChartDomain V z) (boxSet V) := by
  refine ⟨mapsTo_boxChart V z, ?_, ?_⟩
  · intro u hu u' hu' e
    funext i
    exact (h i).2.2.1.injOn (hu i (mem_univ i)) (hu' i (mem_univ i)) (congrFun e i)
  · intro y hy
    have hex : ∀ i, ∃ u ∈ localChartDomain (V i) (z i), localChart s E (z i) u = y i :=
      fun i => (h i).2.2.1.surjOn (hy i (mem_univ i))
    choose u hu hu' using hex
    exact ⟨u, fun i _ => hu i, funext hu'⟩
theorem boxChartInv_of_exists {y : Tuple s E n}
    (h : ∃ u ∈ boxChartDomain V z, boxChart s E z u = y) :
    boxChartInv V z y = h.choose :=
  dif_pos h
theorem invOn_boxChartInv
    (hb : BijOn (boxChart s E z) (boxChartDomain V z) (boxSet V)) :
    InvOn (boxChartInv V z) (boxChart s E z) (boxChartDomain V z) (boxSet V) := by
  constructor
  · intro u hu
    have hex : ∃ v ∈ boxChartDomain V z, boxChart s E z v = boxChart s E z u := ⟨u, hu, rfl⟩
    rw [boxChartInv_of_exists hex]
    exact hb.injOn hex.choose_spec.1 hu hex.choose_spec.2
  · intro y hy
    have hex : ∃ v ∈ boxChartDomain V z, boxChart s E z v = y := hb.surjOn hy
    rw [boxChartInv_of_exists hex]
    exact hex.choose_spec.2
theorem mapsTo_boxChartInv
    (hb : BijOn (boxChart s E z) (boxChartDomain V z) (boxSet V)) :
    MapsTo (boxChartInv V z) (boxSet V) (boxChartDomain V z) := by
  intro y hy
  obtain ⟨u, hu, rfl⟩ := hb.surjOn hy
  rw [(invOn_boxChartInv hb).1 hu]
  exact hu
theorem continuous_boxChart (f : DistanceFacts.MetricFacts s E) :
    Continuous (fun u : Tuple s .euclidean n => boxChart s E z u) :=
  continuous_pi fun i => (continuous_localChart f (z i)).comp (continuous_apply i)
theorem supDist_boxChart (h : ∀ i, CoordChartIsometry V z i)
    {u u' : Tuple s .euclidean n} (hu : u ∈ boxChartDomain V z)
    (hu' : u' ∈ boxChartDomain V z) :
    supDist (boxChart s E z u) (boxChart s E z u') = supDist u u' :=
  iSup_congr fun i => (h i).2.2.2.1 _ (hu i (mem_univ i)) _ (hu' i (mem_univ i))
theorem continuousOn_boxChartInv (h : ∀ i, CoordChartIsometry V z i) :
    ContinuousOn (boxChartInv V z) (boxSet V) := by
  have hb := bijOn_boxChart h
  have hinv := invOn_boxChartInv hb
  refine (LipschitzOnWith.of_dist_le_mul (K := 1) fun y hy y' hy' => ?_).continuousOn
  have hm := supDist_boxChart h (mapsTo_boxChartInv hb hy)
    (mapsTo_boxChartInv hb hy')
  rw [hinv.2 hy, hinv.2 hy'] at hm
  rw [dist_eq_supDist, dist_eq_supDist, ← hm]
  simp
theorem boxChartIsometry_of_coord (f : DistanceFacts.MetricFacts s E)
    (hV : IsSmallOpenTuple V) (h : ∀ i, CoordChartIsometry V z i) :
    BoxChartIsometry V z := by
  have hbij := bijOn_boxChart h
  have hcont := continuous_boxChart (z := z) f
  have hback := continuousOn_boxChartInv h
  refine ⟨isOpen_set_pi finite_univ fun i _ => (h i).1,
    isOpen_set_pi finite_univ fun i _ => (hV.2 i).1, hbij, invOn_boxChartInv hbij,
    fun _ hu _ hu' => supDist_boxChart h hu hu', hcont.continuousOn, hback,
    fun _ _ hcpt => hcpt.image hcont,
    fun _ hsub hcpt => hcpt.image_of_continuousOn (hback.mono hsub)⟩
end Charts
section Transports
theorem closure_image_eq_image_closure_of_isCompact {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space Y] {φ : X → Y} {A S : Set X} (hφ : ContinuousOn φ A)
    (hcpt : IsCompact (closure S)) (hsub : closure S ⊆ A) :
    closure (φ '' S) = φ '' closure S := by
  have hφ' : ContinuousOn φ (closure S) := hφ.mono hsub
  refine Subset.antisymm ?_ hφ'.image_closure
  exact closure_minimal (image_mono subset_closure) (hcpt.image_of_continuousOn hφ').isClosed
variable {s : Conventions.StandingParameters} {E : Ambient} {n : ℕ}
theorem eq_zero_of_notMem_closedSupport {p : ℕ} {E' : Ambient} {F : Tuple s E' p → ℂ}
    {y : Tuple s E' p} (h : y ∉ closedSupport F) : F y = 0 := by
  by_contra hne
  exact h (subset_closure hne)
theorem flattenCoords_add (a b : Fin n → Fin 4 → ℝ) :
    flattenCoords n (a + b) = flattenCoords n a + flattenCoords n b := by
  funext j
  rfl
theorem tupleProj_euclidean (x : Fin (4 * n) → ℝ) :
    tupleProj s .euclidean n x = (flattenCoords n).symm x := rfl
theorem tupleProj_continuous {E' : Ambient} (h : TupleOpenSetProps s E' n) :
    Continuous (tupleProj s E' n) :=
  (h.2.2.2.2.2 (Tuple s E' n) id).mp continuous_id
theorem boxChart_tupleProj (z : Fin n → Fin 4 → ℝ) (x : Fin (4 * n) → ℝ) :
    boxChart s E z (tupleProj s .euclidean n x) =
      tupleProj s E n (x + flattenCoords n z) := by
  have h := boxChart_eq_tupleProj (s := s) (E := E) z ((flattenCoords n).symm x)
  rw [flattenCoords_add, Equiv.apply_symm_apply, add_comm] at h
  exact h
structure ChartSetup (V : Fin n → Set (Pt s E)) (z : Fin n → Fin 4 → ℝ) : Prop where
  metric : DistanceFacts.MetricFacts s E
  small : IsSmallOpenTuple V
  base : IsBasePoint V z
  cover : TupleCoveringProps s E n
  opens : TupleOpenSetProps s E n
  opensFlat : TupleOpenSetProps s .euclidean n
  derivs : TupleDerivProps s E n
  derivsFlat : TupleDerivProps s .euclidean n
  lincomb : ∀ Ω : Set (Tuple s E n), IsOpen Ω → LinearCombFacts Ω
  lincombFlat : ∀ Ω : Set (Tuple s .euclidean n), IsOpen Ω → LinearCombFacts Ω
  tensors : ∀ (O : Fin n → Set (Pt s E)) (φ : Fin n → Pt s E → ℂ), (∀ i, IsOpen (O i)) →
    (∀ i, ofSinglePoint (φ i) ∈ testFns (singletonTupleSet (O i))) →
      TensorProdFacts O φ
variable {V : Fin n → Set (Pt s E)} {z : Fin n → Fin 4 → ℝ}
namespace ChartSetup
variable (S : ChartSetup V z)
include S
theorem coordIso (i : Fin n) : CoordChartIsometry V z i :=
  coordChartIsometry_of_small S.metric S.small S.base i
theorem bijOn : BijOn (boxChart s E z) (boxChartDomain V z) (boxSet V) :=
  bijOn_boxChart S.coordIso
theorem invOn :
    InvOn (boxChartInv V z) (boxChart s E z) (boxChartDomain V z) (boxSet V) :=
  invOn_boxChartInv S.bijOn
theorem boxIso : BoxChartIsometry V z := boxChartIsometry_of_coord S.metric S.small S.coordIso
theorem isOpen_boxChartDomain : IsOpen (boxChartDomain V z) := S.boxIso.1
theorem isOpen_boxSet : IsOpen (boxSet V) := S.boxIso.2.1
theorem image_boxChartDomain : boxChart s E z '' boxChartDomain V z = boxSet V :=
  S.bijOn.image_eq
theorem chartPushforward_boxChart_apply {R : Type*} [Zero R] (H : Tuple s .euclidean n → R)
    {u : Tuple s .euclidean n} (hu : u ∈ boxChartDomain V z) :
    chartPushforward V z H (boxChart s E z u) = H u :=
  chartPushforward_boxChart S.bijOn.injOn H hu
theorem chartPushforward_of_notMem_boxSet {R : Type*} [Zero R] (H : Tuple s .euclidean n → R)
    {y : Tuple s E n} (hy : y ∉ boxSet V) : chartPushforward V z H y = 0 :=
  chartPushforward_of_notMem H (by rwa [S.image_boxChartDomain])
theorem closedSupport_chartPullback {F : Tuple s E n → ℂ} (hK : IsCompact (closedSupport F))
    (hsub : closedSupport F ⊆ boxSet V) :
    closedSupport (chartPullback V z F) = boxChartInv V z '' closedSupport F := by
  have hset : {u | chartPullback V z F u ≠ 0} = boxChartInv V z '' {y | F y ≠ 0} := by
    ext u
    constructor
    · intro hne
      by_cases hu : u ∈ boxChartDomain V z
      · rw [mem_ofPred_eq, chartPullback_of_mem _ hu] at hne
        exact ⟨_, hne, S.invOn.1 hu⟩
      · exact absurd (chartPullback_of_notMem _ hu) hne
    · rintro ⟨y, hy, rfl⟩
      have hyV : y ∈ boxSet V := hsub (subset_closure hy)
      rw [mem_ofPred_eq, chartPullback_of_mem _ (mapsTo_boxChartInv S.bijOn hyV), S.invOn.2 hyV]
      exact hy
  rw [closedSupport, hset]
  exact closure_image_eq_image_closure_of_isCompact S.boxIso.2.2.2.2.2.2.1 hK hsub
theorem closedSupport_chartPushforward {H : Tuple s .euclidean n → ℂ}
    (hK : IsCompact (closedSupport H)) (hsub : closedSupport H ⊆ boxChartDomain V z) :
    closedSupport (chartPushforward V z H) = boxChart s E z '' closedSupport H := by
  have hset : {y | chartPushforward V z H y ≠ 0} = boxChart s E z '' {u | H u ≠ 0} := by
    ext y
    constructor
    · intro hne
      by_cases hy : y ∈ boxChart s E z '' boxChartDomain V z
      · obtain ⟨u, hu, rfl⟩ := hy
        rw [mem_ofPred_eq, S.chartPushforward_boxChart_apply _ hu] at hne
        exact ⟨u, hne, rfl⟩
      · exact absurd (chartPushforward_of_notMem H hy) hne
    · rintro ⟨u, hu, rfl⟩
      rw [mem_ofPred_eq, S.chartPushforward_boxChart_apply _ (hsub (subset_closure hu))]
      exact hu
  rw [closedSupport, hset]
  exact closure_image_eq_image_closure_of_isCompact S.boxIso.2.2.2.2.2.1 hK hsub
theorem chartPushforward_chartPullback {F : Tuple s E n → ℂ} (hsub : closedSupport F ⊆ boxSet V) :
    chartPushforward V z (chartPullback V z F) = F := by
  funext y
  by_cases hy : y ∈ boxSet V
  · obtain ⟨u, hu, rfl⟩ := S.bijOn.surjOn hy
    rw [S.chartPushforward_boxChart_apply _ hu, chartPullback_of_mem _ hu]
  · rw [S.chartPushforward_of_notMem_boxSet _ hy,
      eq_zero_of_notMem_closedSupport fun h => hy (hsub h)]
theorem chartPullback_chartPushforward {H : Tuple s .euclidean n → ℂ}
    (hsub : closedSupport H ⊆ boxChartDomain V z) :
    chartPullback V z (chartPushforward V z H) = H := by
  funext u
  by_cases hu : u ∈ boxChartDomain V z
  · rw [chartPullback_of_mem _ hu, S.chartPushforward_boxChart_apply _ hu]
  · rw [chartPullback_of_notMem _ hu, eq_zero_of_notMem_closedSupport fun h => hu (hsub h)]
theorem pullbackPreservesCn : PullbackPreservesCn V z := by
  intro ν F hF hK hsub
  have hsupp := S.closedSupport_chartPullback hK hsub
  have hK' : IsCompact (boxChartInv V z '' closedSupport F) := S.boxIso.2.2.2.2.2.2.2.2 _ hsub hK
  have hsub' : boxChartInv V z '' closedSupport F ⊆ boxChartDomain V z :=
    image_subset_iff.mpr fun y hy => mapsTo_boxChartInv S.bijOn (hsub hy)
  have hcov := tupleProj_continuous S.opensFlat
  have hmain := isCn_and_multiDeriv_of_locally_translate S.derivs S.derivsFlat ν F hF
    (chartPullback V z F) (chartPullback V z) (by
      intro x
      by_cases hu : tupleProj s .euclidean n x ∈ boxChartDomain V z
      · refine Or.inl ⟨flattenCoords n z, ?_, fun H => ?_⟩
        · filter_upwards [hcov.continuousAt.eventually
            (S.isOpen_boxChartDomain.mem_nhds hu)] with x' hx'
          rw [chartPullback_of_mem _ hx', boxChart_tupleProj]
        · rw [chartPullback_of_mem _ hu, boxChart_tupleProj]
      · refine Or.inr ⟨?_, fun α _ => chartPullback_of_notMem _ hu⟩
        have hnot : tupleProj s .euclidean n x ∉
            boxChartInv V z '' closedSupport F := fun h => hu (hsub' h)
        filter_upwards [hcov.continuousAt.eventually
          (hK'.isClosed.isOpen_compl.mem_nhds hnot)] with x' hx'
        refine eq_zero_of_notMem_closedSupport ?_
        rwa [hsupp])
  exact ⟨hmain.1, hsupp, hK', hsub', hmain.2, S.chartPushforward_chartPullback hsub⟩
theorem pushforwardPreservesCn : PushforwardPreservesCn V z := by
  intro ν H hH hK hsub
  have hsupp := S.closedSupport_chartPushforward hK hsub
  have hK' : IsCompact (boxChart s E z '' closedSupport H) := S.boxIso.2.2.2.2.2.2.2.1 _ hsub hK
  have hsub' : boxChart s E z '' closedSupport H ⊆ boxSet V :=
    image_subset_iff.mpr fun u hu => mapsTo_boxChart V z (hsub hu)
  have hcovE := tupleProj_continuous S.opens
  have hcovR := tupleProj_continuous S.opensFlat
  have hmain := isCn_and_multiDeriv_of_locally_translate S.derivsFlat S.derivs ν H hH
    (chartPushforward V z H) (chartPushforward V z) (by
      intro x
      by_cases hy : tupleProj s E n x ∈ boxSet V
      · obtain ⟨u, hu, huy⟩ := S.bijOn.surjOn hy
        set xu := flattenCoords n u with hxu
        set c := flattenCoords n z with hc
        have hback : tupleProj s .euclidean n xu = u := by
          rw [tupleProj_euclidean, hxu]
          exact (flattenCoords n).symm_apply_apply u
        have hper : IsTuplePeriod s E n (x - (xu + c)) := by
          refine (S.cover.2.1 x (xu + c)).mp ?_
          rw [← boxChart_tupleProj, hback, huy]
        set w := x - (xu + c) with hw
        have hshift : x + (-w - c) = xu := by
          rw [hw]
          abel
        have hsame : ∀ x', tupleProj s E n x' =
            boxChart s E z (tupleProj s .euclidean n (x' + (-w - c))) := by
          intro x'
          rw [boxChart_tupleProj]
          refine (S.cover.2.1 x' _).mpr ?_
          have he : x' - (x' + (-w - c) + c) = w := by abel
          rwa [he]
        refine Or.inl ⟨-w - c, ?_, fun G => ?_⟩
        · have hcont : ContinuousAt
              (fun x' => tupleProj s .euclidean n (x' + (-w - c))) x :=
            (hcovR.comp (continuous_id.add continuous_const)).continuousAt
          have hmem : boxChartDomain V z ∈
              𝓝 ((fun x' => tupleProj s .euclidean n (x' + (-w - c))) x) := by
            refine S.isOpen_boxChartDomain.mem_nhds ?_
            change tupleProj s .euclidean n (x + (-w - c)) ∈ _
            rwa [hshift, hback]
          filter_upwards [hcont.eventually hmem] with x' hx'
          rw [hsame x', S.chartPushforward_boxChart_apply _ hx']
        · rw [hsame x, S.chartPushforward_boxChart_apply]
          rw [hshift, hback]
          exact hu
      · refine Or.inr ⟨?_, fun α _ => S.chartPushforward_of_notMem_boxSet _ hy⟩
        have hnot : tupleProj s E n x ∉ boxChart s E z '' closedSupport H :=
          fun h => hy (hsub' h)
        filter_upwards [hcovE.continuousAt.eventually
          (hK'.isClosed.isOpen_compl.mem_nhds hnot)] with x' hx'
        refine eq_zero_of_notMem_closedSupport ?_
        rwa [hsupp])
  exact ⟨hmain.1, hsupp, hK', hsub', hmain.2, S.chartPullback_chartPushforward hsub⟩
end ChartSetup
end Transports
section TestFunctionsAndDistributions
variable {s : Conventions.StandingParameters} {n : ℕ}
theorem iSup_eq_iSup_of_surjOn {X Y : Type*} {A : Set X} {B : Set Y} {j : X → Y}
    (hj : SurjOn j A B) {ψ : Y → ℝ≥0∞} {ψ' : X → ℝ≥0∞} (hval : ∀ u ∈ A, ψ (j u) = ψ' u)
    (hoff : ∀ y, y ∉ B → ψ y = 0) (hoff' : ∀ u, u ∉ A → ψ' u = 0) :
    ⨆ y, ψ y = ⨆ u, ψ' u := by
  refine le_antisymm (iSup_le fun y => ?_) (iSup_le fun u => ?_)
  · rcases em (y ∈ B) with hy | hy
    · obtain ⟨u, hu, rfl⟩ := hj hy
      exact (hval u hu).le.trans (le_iSup ψ' u)
    · simp [hoff y hy]
  · rcases em (u ∈ A) with hu | hu
    · exact (hval u hu).symm.le.trans (le_iSup ψ (j u))
    · simp [hoff' u hu]
theorem testFnTendsto_map {X Y : Ambient} {p : ℕ} {Ω₁ : Set (Tuple s X p)}
    {Ω₂ : Set (Tuple s Y p)} (W : (Tuple s X p → ℂ) → Tuple s Y p → ℂ)
    (hWmem : ∀ F ∈ testFns Ω₁, W F ∈ testFns Ω₂)
    (hWnorm : ∀ F ∈ testFns Ω₁, ∀ ν, cnNorm ν (W F) = cnNorm ν F)
    (hWsub : ∀ F G, W (F - G) = W F - W G)
    (hsubMem : ∀ F ∈ testFns Ω₁, ∀ G ∈ testFns Ω₁, F - G ∈ testFns Ω₁)
    (hWsupp : ∀ K, IsCompact K → K ⊆ Ω₁ → ∃ K', IsCompact K' ∧ K' ⊆ Ω₂ ∧
      ∀ F ∈ testFns Ω₁, closedSupport F ⊆ K → closedSupport (W F) ⊆ K')
    {Fs : ℕ+ → Tuple s X p → ℂ} {F : Tuple s X p → ℂ} (h : TestFnTendsto Ω₁ Fs F) :
    TestFnTendsto Ω₂ (fun t => W (Fs t)) (W F) := by
  rcases h with ⟨hFs, hF, ⟨K, hKc, hKsub, hFK, hFsK⟩, hlim⟩
  rcases hWsupp K hKc hKsub with ⟨K', hK'c, hK'sub, hK'⟩
  refine ⟨fun t => hWmem _ (hFs t), hWmem _ hF,
    ⟨K', hK'c, hK'sub, hK' _ hF hFK, fun t => hK' _ (hFs t) (hFsK t)⟩, fun ν => ?_⟩
  have hnorms : ∀ t, cnNorm ν (W (Fs t) - W F) = cnNorm ν (Fs t - F) := fun t => by
    rw [← hWsub, hWnorm _ (hsubMem _ (hFs t) _ hF)]
  simpa only [hnorms] using hlim ν
theorem isDistrib_comp_map {X Y : Ambient} {p : ℕ} {Ω₁ : Set (Tuple s X p)}
    {Ω₂ : Set (Tuple s Y p)} (W : (Tuple s X p → ℂ) → Tuple s Y p → ℂ)
    (hWmem : ∀ F ∈ testFns Ω₁, W F ∈ testFns Ω₂)
    (hWnorm : ∀ F ∈ testFns Ω₁, ∀ ν, cnNorm ν (W F) = cnNorm ν F)
    (hWadd : ∀ F G, W (F + G) = W F + W G) (hWsmul : ∀ (c : ℂ) F, W (c • F) = c • W F)
    (hWsupp : ∀ K, IsCompact K → K ⊆ Ω₁ → ∃ K', IsCompact K' ∧ K' ⊆ Ω₂ ∧
      ∀ F ∈ testFns Ω₁, closedSupport F ⊆ K → closedSupport (W F) ⊆ K')
    (T : testFns Ω₂ → ℂ) (hT : IsDistrib T) (G : testFns Ω₁ → ℂ)
    (hG : ∀ (F : testFns Ω₁) (h : W F.1 ∈ testFns Ω₂), G F = T ⟨_, h⟩) :
    IsDistrib G ∧ ∀ ν₀, HasOrderLE ν₀ T → HasOrderLE ν₀ G := by
  have hGW : ∀ F : testFns Ω₁, G F = T ⟨W F.1, hWmem _ F.2⟩ := fun F => hG F _
  have hbound : ∀ {K : Set (Tuple s X p)} {K' : Set (Tuple s Y p)} (ν : ℕ),
      (∀ F ∈ testFns Ω₁, closedSupport F ⊆ K → closedSupport (W F) ⊆ K') →
        OrderBoundsOn T K' ν → OrderBoundsOn G K ν := by
    intro K K' ν hKK' hTK'
    obtain ⟨C, hC⟩ := hTK'
    refine ⟨C, fun F hF => ?_⟩
    rw [hGW, ← hWnorm _ F.2 ν]
    exact hC ⟨W F.1, hWmem _ F.2⟩ (hKK' _ F.2 hF)
  have hlin : IsComplexLinearForm G := by
    refine ⟨fun F₁ F₂ H hH => ?_, fun c F H hH => ?_⟩
    · rw [hGW, hGW, hGW]
      refine hT.1.1 _ _ _ ?_
      exact (congrArg W hH).trans (hWadd _ _)
    · rw [hGW, hGW]
      refine hT.1.2 c _ _ ?_
      exact (congrArg W hH).trans (hWsmul c _)
  have hdist : IsDistrib G := ⟨hlin, fun K hK hKΩ => by
    obtain ⟨K', hK', hK'Ω, hKK'⟩ := hWsupp K hK hKΩ
    obtain ⟨ν, hν⟩ := hT.2 K' hK' hK'Ω
    exact ⟨ν, hbound ν hKK' hν⟩⟩
  refine ⟨hdist, fun ν₀ hν₀ => ⟨hdist, fun K hK hKΩ => ?_⟩⟩
  obtain ⟨K', hK', hK'Ω, hKK'⟩ := hWsupp K hK hKΩ
  exact hbound ν₀ hKK' (hν₀.2 K' hK' hK'Ω)
variable {E : Ambient} {V : Fin n → Set (Pt s E)} {z : Fin n → Fin 4 → ℝ}
section Linearity
variable {𝕜 R : Type*} [Semiring 𝕜] [AddCommMonoid R] [Module 𝕜 R]
theorem chartPullback_add (V : Fin n → Set (Pt s E)) (z : Fin n → Fin 4 → ℝ)
    (F G : Tuple s E n → R) : chartPullback V z (F + G) = chartPullback V z F + chartPullback V z G := by
  funext u
  by_cases hu : u ∈ boxChartDomain V z
  · simp only [Pi.add_apply, chartPullback_of_mem _ hu]
  · simp only [Pi.add_apply, chartPullback_of_notMem _ hu, add_zero]
theorem chartPullback_smul (V : Fin n → Set (Pt s E)) (z : Fin n → Fin 4 → ℝ) (c : 𝕜)
    (F : Tuple s E n → R) : chartPullback V z (c • F) = c • chartPullback V z F := by
  funext u
  by_cases hu : u ∈ boxChartDomain V z
  · simp only [Pi.smul_apply, chartPullback_of_mem _ hu]
  · simp only [Pi.smul_apply, chartPullback_of_notMem _ hu, smul_zero]
theorem chartPushforward_add (V : Fin n → Set (Pt s E)) (z : Fin n → Fin 4 → ℝ)
    (H G : Tuple s .euclidean n → R) :
    chartPushforward V z (H + G) = chartPushforward V z H + chartPushforward V z G := by
  funext y
  by_cases h : ∃ u ∈ boxChartDomain V z, boxChart s E z u = y
  · simp only [chartPushforward, Pi.add_apply, dif_pos h]
  · simp only [chartPushforward, Pi.add_apply, dif_neg h, add_zero]
theorem chartPushforward_smul (V : Fin n → Set (Pt s E)) (z : Fin n → Fin 4 → ℝ) (c : 𝕜)
    (H : Tuple s .euclidean n → R) : chartPushforward V z (c • H) = c • chartPushforward V z H := by
  funext y
  by_cases h : ∃ u ∈ boxChartDomain V z, boxChart s E z u = y
  · simp only [chartPushforward, Pi.smul_apply, dif_pos h]
  · simp only [chartPushforward, Pi.smul_apply, dif_neg h, smul_zero]
theorem chartPushforward_sum (V : Fin n → Set (Pt s E)) (z : Fin n → Fin 4 → ℝ) {m : ℕ}
    (H : Fin m → Tuple s .euclidean n → R) :
    chartPushforward V z (∑ k, H k) = ∑ k, chartPushforward V z (H k) := by
  funext y
  by_cases h : ∃ u ∈ boxChartDomain V z, boxChart s E z u = y
  · simp only [chartPushforward, Finset.sum_apply, dif_pos h]
  · simp only [chartPushforward, Finset.sum_apply, dif_neg h, Finset.sum_const_zero]
end Linearity
theorem chartPullback_sub (V : Fin n → Set (Pt s E)) (z : Fin n → Fin 4 → ℝ)
    (F G : Tuple s E n → ℂ) : chartPullback V z (F - G) = chartPullback V z F - chartPullback V z G := by
  funext u
  by_cases hu : u ∈ boxChartDomain V z
  · simp only [Pi.sub_apply, chartPullback_of_mem _ hu]
  · simp only [Pi.sub_apply, chartPullback_of_notMem _ hu, sub_zero]
theorem chartPushforward_sub (V : Fin n → Set (Pt s E)) (z : Fin n → Fin 4 → ℝ)
    (H G : Tuple s .euclidean n → ℂ) :
    chartPushforward V z (H - G) = chartPushforward V z H - chartPushforward V z G := by
  funext y
  by_cases h : ∃ u ∈ boxChartDomain V z, boxChart s E z u = y
  · simp only [chartPushforward, Pi.sub_apply, dif_pos h]
  · simp only [chartPushforward, Pi.sub_apply, dif_neg h, sub_zero]
theorem sub_mem_testFns {X : Ambient} {p : ℕ} {Ω : Set (Tuple s X p)}
    (h : LinearCombFacts Ω) {F G : Tuple s X p → ℂ} (hF : F ∈ testFns Ω)
    (hG : G ∈ testFns Ω) : F - G ∈ testFns Ω := by
  have he : (1 : ℂ) • F + (-1 : ℂ) • G = F - G := by
    simp [sub_eq_add_neg]
  exact he ▸ (h F hF G hG 1 (-1)).1
namespace ChartSetup
variable (S : ChartSetup V z)
include S
theorem chartPullback_mem_testFns {F : Tuple s E n → ℂ} (hF : F ∈ testFns (boxSet V)) :
    chartPullback V z F ∈ testFns (boxChartDomain V z) := by
  obtain ⟨h1, h2, h3, h4, -, -⟩ := S.pullbackPreservesCn ⊤ F hF.1 hF.2.1 hF.2.2
  exact ⟨h1, h2 ▸ h3, h2 ▸ h4⟩
theorem chartPushforward_mem_testFns {H : Tuple s .euclidean n → ℂ}
    (hH : H ∈ testFns (boxChartDomain V z)) :
    chartPushforward V z H ∈ testFns (boxSet V) := by
  obtain ⟨h1, h2, h3, h4, -, -⟩ := S.pushforwardPreservesCn ⊤ H hH.1 hH.2.1 hH.2.2
  exact ⟨h1, h2 ▸ h3, h2 ▸ h4⟩
theorem cnNorm_chartPullback {F : Tuple s E n → ℂ} (hF : F ∈ testFns (boxSet V))
    (ν : ℕ) : cnNorm ν (chartPullback V z F) = cnNorm ν F := by
  obtain ⟨-, -, -, -, hd, -⟩ := S.pullbackPreservesCn ⊤ F hF.1 hF.2.1 hF.2.2
  refine iSup_congr fun α => iSup_congr fun _ => ?_
  rw [hd α le_top]
  have hsupp : closedSupport (multiDeriv α F) ⊆ closedSupport F :=
    ((S.derivs ⊤ F hF.1).1 α le_top).2.2.1
  refine (iSup_eq_iSup_of_surjOn S.bijOn.surjOn (fun u hu => ?_) (fun y hy => ?_)
    (fun u hu => ?_)).symm
  · rw [chartPullback_of_mem _ hu]
  · rw [eq_zero_of_notMem_closedSupport fun h => hy (hF.2.2 (hsupp h))]
    simp
  · rw [chartPullback_of_notMem _ hu]
    simp
theorem cnNorm_chartPushforward {H : Tuple s .euclidean n → ℂ}
    (hH : H ∈ testFns (boxChartDomain V z)) (ν : ℕ) :
    cnNorm ν (chartPushforward V z H) = cnNorm ν H := by
  rw [← S.cnNorm_chartPullback (S.chartPushforward_mem_testFns hH) ν,
    S.chartPullback_chartPushforward hH.2.2]
theorem exists_isCompact_chartPullback (K : Set (Tuple s E n)) (hK : IsCompact K)
    (hsub : K ⊆ boxSet V) :
    ∃ K', IsCompact K' ∧ K' ⊆ boxChartDomain V z ∧
      ∀ F ∈ testFns (boxSet V), closedSupport F ⊆ K →
        closedSupport (chartPullback V z F) ⊆ K' := by
  refine ⟨boxChartInv V z '' K, S.boxIso.2.2.2.2.2.2.2.2 _ hsub hK,
    image_subset_iff.mpr fun y hy => mapsTo_boxChartInv S.bijOn (hsub hy), fun F hF h => ?_⟩
  rw [S.closedSupport_chartPullback hF.2.1 hF.2.2]
  exact image_mono h
theorem exists_isCompact_chartPushforward (K : Set (Tuple s .euclidean n)) (hK : IsCompact K)
    (hsub : K ⊆ boxChartDomain V z) :
    ∃ K', IsCompact K' ∧ K' ⊆ boxSet V ∧
      ∀ H ∈ testFns (boxChartDomain V z), closedSupport H ⊆ K →
        closedSupport (chartPushforward V z H) ⊆ K' := by
  refine ⟨boxChart s E z '' K, S.boxIso.2.2.2.2.2.2.2.1 _ hsub hK,
    image_subset_iff.mpr fun u hu => mapsTo_boxChart V z (hsub hu), fun H hH h => ?_⟩
  rw [S.closedSupport_chartPushforward hH.2.1 hH.2.2]
  exact image_mono h
theorem transportTestFnsDistribs : TransportTestFnsDistribs V z := by
  have hinv : InvOn (chartPushforward V z) (chartPullback V z) (testFns (boxSet V))
      (boxTestFns V z) :=
    ⟨fun F hF => S.chartPushforward_chartPullback hF.2.2,
      fun H hH => S.chartPullback_chartPushforward hH.2.2⟩
  have hdiff₁ : ∀ F ∈ testFns (boxSet V), ∀ G ∈ testFns (boxSet V),
      F - G ∈ testFns (boxSet V) := fun F hF G hG =>
    sub_mem_testFns (S.lincomb _ S.isOpen_boxSet) hF hG
  have hdiff₂ : ∀ F ∈ testFns (boxChartDomain V z),
      ∀ G ∈ testFns (boxChartDomain V z),
        F - G ∈ testFns (boxChartDomain V z) := fun F hF G hG =>
    sub_mem_testFns (S.lincombFlat _ S.isOpen_boxChartDomain) hF hG
  refine ⟨⟨hinv.bijOn (fun F hF => S.chartPullback_mem_testFns hF)
      (fun H hH => S.chartPushforward_mem_testFns hH), hinv,
      fun F _ G _ => chartPullback_add V z F G, fun c F _ => chartPullback_smul V z c F⟩,
    fun F hF => ⟨S.cnNorm_chartPullback hF, S.closedSupport_chartPullback hF.2.1 hF.2.2⟩,
    fun Fs F hFs hF => ⟨fun h => ?_, fun h => ?_⟩, fun T hT => ?_, fun T' hT' => ?_⟩
  · exact testFnTendsto_map (chartPullback V z) (fun F hF => S.chartPullback_mem_testFns hF)
      (fun F hF ν => S.cnNorm_chartPullback hF ν) (chartPullback_sub V z) hdiff₁
      S.exists_isCompact_chartPullback h
  · have h' := testFnTendsto_map (chartPushforward V z)
      (fun H hH => S.chartPushforward_mem_testFns hH)
      (fun H hH ν => S.cnNorm_chartPushforward hH ν) (chartPushforward_sub V z) hdiff₂
      S.exists_isCompact_chartPushforward h
    have he : (fun t => chartPushforward V z (chartPullback V z (Fs t))) = Fs :=
      funext fun t => S.chartPushforward_chartPullback (hFs t).2.2
    rwa [he, S.chartPushforward_chartPullback hF.2.2] at h'
  · have h := isDistrib_comp_map (chartPullback V z) (fun F hF => S.chartPullback_mem_testFns hF)
      (fun F hF ν => S.cnNorm_chartPullback hF ν) (chartPullback_add V z) (chartPullback_smul V z)
      S.exists_isCompact_chartPullback T hT (distribPullback V z T) (fun F h => dif_pos h)
    exact ⟨h.1, h.2⟩
  · exact (isDistrib_comp_map (chartPushforward V z)
      (fun H hH => S.chartPushforward_mem_testFns hH)
      (fun H hH ν => S.cnNorm_chartPushforward hH ν) (chartPushforward_add V z)
      (chartPushforward_smul V z) S.exists_isCompact_chartPushforward T' hT'
      (distribPushforward V z T') (fun F h => dif_pos h)).1
end ChartSetup
end TestFunctionsAndDistributions
section Entries
variable {s : Conventions.StandingParameters} {E : Ambient} {n : ℕ} {V : Fin n → Set (Pt s E)}
  {z : Fin n → Fin 4 → ℝ}
theorem const_apply_zero_eq {X : Ambient} (y : Tuple s X 1) : (fun _ => y 0) = y := by
  funext j
  rw [Subsingleton.elim j 0]
theorem singletonTuples_eq_boxSet (A : Set (Pt s .euclidean)) :
    singletonTuples A = boxSet fun _ : Fin 1 => A := by
  ext y
  constructor
  · intro h j _
    rw [Subsingleton.elim j 0]
    exact h
  · intro h
    exact h 0 (mem_univ 0)
theorem singletonTupleSet_eq_boxSet {X : Ambient} (A : Set (Pt s X)) :
    singletonTupleSet A = boxSet fun _ : Fin 1 => A := by
  ext y
  constructor
  · intro h j _
    rw [Subsingleton.elim j 0]
    exact h
  · intro h
    exact h 0 (mem_univ 0)
theorem ofSinglePoint_singlePushforward (g : Pt s .euclidean → ℂ) (i : Fin n) :
    ofSinglePoint (singlePushforward V z i g) =
      coordPushforward V z i (ofSinglePoint g) := by
  funext y
  change coordPushforward V z i (fun v => g (v 0)) (fun _ => y 0) = _
  rw [const_apply_zero_eq]
  rfl
theorem asFunctionOnOnePoint_singlePushforward (g : Pt s .euclidean → ℝ) (i : Fin n) :
    asFunctionOnOnePoint (singlePushforward V z i g) =
      coordPushforward V z i (asFunctionOnOnePoint g) := by
  funext y
  have h := congrFun (chartPushforward_ofReal (fun _ : Fin 1 => V i) (fun _ => z i)
    (fun v => g (v 0))) y
  change ((coordPushforward V z i (fun v => g (v 0)) (fun _ => y 0) : ℝ) : ℂ) = _
  rw [const_apply_zero_eq]
  exact h.symm
theorem asFunctionOnOnePoint_singlePullback (φ : Pt s E → ℝ) (i : Fin n) :
    asFunctionOnOnePoint (singlePullback V z i φ) =
      coordPullback V z i (asFunctionOnOnePoint φ) := by
  funext v
  have h := congrFun (chartPullback_ofReal (fun _ : Fin 1 => V i) (fun _ => z i)
    (fun y => φ (y 0))) v
  change ((coordPullback V z i (fun y => φ (y 0)) (fun _ => v 0) : ℝ) : ℂ) = _
  rw [const_apply_zero_eq]
  exact h.symm
theorem asFunctionOnOnePoint_injective {X : Ambient} {f f' : Pt s X → ℝ}
    (h : asFunctionOnOnePoint f = asFunctionOnOnePoint f') : f = f' := by
  funext a
  exact Complex.ofReal_injective (congrFun h fun _ => a)
theorem mem_c1CompactSupportIn_iff {X : Ambient} (A : Set (Pt s X)) (f : Pt s X → ℝ) :
    f ∈ c1CompactSupportIn A ↔ IsCn 1 (asFunctionOnOnePoint f) ∧
      IsCompact (closedSupport (asFunctionOnOnePoint f)) ∧
        closedSupport (asFunctionOnOnePoint f) ⊆ boxSet fun _ : Fin 1 => A := by
  have hc : IsCompact (closedSupport (asFunctionOnOnePoint f)) ↔ IsCompact (tsupport f) := by
    rw [closedSupport_asFunctionOnOnePoint]
    exact (Homeomorph.funUnique (Fin 1) (Pt s X)).isCompact_preimage
  have hs : closedSupport (asFunctionOnOnePoint f) ⊆ (boxSet fun _ : Fin 1 => A) ↔
      tsupport f ⊆ A := by
    rw [closedSupport_asFunctionOnOnePoint]
    constructor
    · intro h a ha
      exact h (a := fun _ => a) ha 0 (mem_univ 0)
    · intro h y hy j _
      rw [Subsingleton.elim j 0]
      exact h hy
  exact and_congr Iff.rfl (and_congr hc.symm hs.symm)
theorem zero_mem_testFns {X : Ambient} {p : ℕ} (Ω : Set (Tuple s X p)) :
    (0 : Tuple s X p → ℂ) ∈ testFns Ω := by
  have hs : closedSupport (0 : Tuple s X p → ℂ) = ∅ := by
    have h0 : {y | (0 : Tuple s X p → ℂ) y ≠ 0} = ∅ := by
      ext y
      simp
    rw [closedSupport, h0, closure_empty]
  refine ⟨⟨isOpen_univ, fun m _ => continuousPartialsUpTo_const_zero m⟩, ?_, ?_⟩
  · rw [hs]
    exact isCompact_empty
  · rw [hs]
    exact empty_subset _
theorem gradNorm_eq_zero_of_partialAt {X : Ambient} {g : Pt s X → ℂ} {x : Pt s X}
    (h : ∀ μ, partialAt μ g x = 0) : gradNorm g x = 0 := by
  simp [gradNorm, gradient, h]
section OneCoordinate
variable {i : Fin n} (S₁ : ChartSetup (fun _ : Fin 1 => V i) (fun _ => z i))
include S₁
theorem singlePushforward_localChart {R : Type*} [Zero R] (g : Pt s .euclidean → R)
    {u : Pt s .euclidean} (hu : u ∈ localChartDomain (V i) (z i)) :
    singlePushforward V z i g (localChart s E (z i) u) = g u :=
  S₁.chartPushforward_boxChart_apply (fun v => g (v 0)) (u := fun _ => u)
    (mem_boxChartDomain_single.mpr hu)
theorem singlePushforward_of_notMem {R : Type*} [Zero R] (g : Pt s .euclidean → R)
    {y : Pt s E} (hy : y ∉ V i) : singlePushforward V z i g y = 0 := by
  have hne : (fun _ : Fin 1 => y) ∉ boxSet fun _ : Fin 1 => V i :=
    fun h => hy (h 0 (mem_univ 0))
  exact S₁.chartPushforward_of_notMem_boxSet (fun v => g (v 0)) hne
theorem transportCoord_of_setup (hentry : CoordChartIsometry V z i) :
    TransportCoord V z i := by
  have hpush : ∀ g ∈ coordC1CompactSupport V z i,
      singlePushforward V z i g ∈ c1CompactSupportIn (V i) := by
    intro g hg
    obtain ⟨h1, h2, h3⟩ := (mem_c1CompactSupportIn_iff _ _).mp hg
    obtain ⟨k1, k2, k3, k4, -, -⟩ := S₁.pushforwardPreservesCn 1 (asFunctionOnOnePoint g) h1 h2 h3
    refine (mem_c1CompactSupportIn_iff _ _).mpr ?_
    rw [asFunctionOnOnePoint_singlePushforward]
    exact ⟨k1, k2 ▸ k3, k2 ▸ k4⟩
  have hpull : ∀ φ ∈ c1CompactSupportIn (V i),
      singlePullback V z i φ ∈ coordC1CompactSupport V z i := by
    intro φ hφ
    obtain ⟨h1, h2, h3⟩ := (mem_c1CompactSupportIn_iff _ _).mp hφ
    obtain ⟨k1, k2, k3, k4, -, -⟩ := S₁.pullbackPreservesCn 1 (asFunctionOnOnePoint φ) h1 h2 h3
    refine (mem_c1CompactSupportIn_iff _ _).mpr ?_
    rw [asFunctionOnOnePoint_singlePullback]
    exact ⟨k1, k2 ▸ k3, k2 ▸ k4⟩
  have hinv : InvOn (singlePullback V z i) (singlePushforward V z i)
      (coordC1CompactSupport V z i) (c1CompactSupportIn (V i)) := by
    constructor
    · intro g hg
      obtain ⟨-, -, h3⟩ := (mem_c1CompactSupportIn_iff _ _).mp hg
      refine asFunctionOnOnePoint_injective ?_
      rw [asFunctionOnOnePoint_singlePullback, asFunctionOnOnePoint_singlePushforward]
      exact S₁.chartPullback_chartPushforward h3
    · intro φ hφ
      obtain ⟨-, -, h3⟩ := (mem_c1CompactSupportIn_iff _ _).mp hφ
      refine asFunctionOnOnePoint_injective ?_
      rw [asFunctionOnOnePoint_singlePushforward, asFunctionOnOnePoint_singlePullback]
      exact S₁.chartPushforward_chartPullback h3
  refine ⟨S₁.transportTestFnsDistribs.1, ?_, ?_,
    ⟨hinv.bijOn hpush hpull, hinv, fun g _ g' _ => ?_, fun c g _ => ?_⟩, ?_⟩
  · intro F _ hre u
    change (chartPullback (fun _ : Fin 1 => V i) (fun _ => z i) F u).im = 0
    by_cases hu : u ∈ boxChartDomain (fun _ : Fin 1 => V i) (fun _ => z i)
    · rw [chartPullback_of_mem _ hu]
      exact hre _
    · rw [chartPullback_of_notMem _ hu]
      rfl
  · intro H _ hre y
    change (chartPushforward (fun _ : Fin 1 => V i) (fun _ => z i) H y).im = 0
    by_cases h : ∃ u ∈ boxChartDomain (fun _ : Fin 1 => V i) (fun _ => z i),
        boxChart s E (fun _ => z i) u = y
    · simp only [chartPushforward, dif_pos h]
      exact hre _
    · simp only [chartPushforward, dif_neg h, Complex.zero_im]
  · funext y
    exact congrFun (chartPushforward_add (fun _ : Fin 1 => V i) (fun _ => z i)
      (fun v => g (v 0)) (fun v => g' (v 0))) fun _ => y
  · funext y
    exact congrFun (chartPushforward_smul (fun _ : Fin 1 => V i) (fun _ => z i) c
      (fun v => g (v 0))) fun _ => y
  · intro g hg
    obtain ⟨h1, h2, h3⟩ := (mem_c1CompactSupportIn_iff _ _).mp hg
    obtain ⟨-, -, -, -, hd, -⟩ := S₁.pushforwardPreservesCn 1 (asFunctionOnOnePoint g) h1 h2 h3
    have hfo : ofSinglePoint (fun y => ((singlePushforward V z i g y : ℝ) : ℂ)) =
        coordPushforward V z i (asFunctionOnOnePoint g) :=
      asFunctionOnOnePoint_singlePushforward g i
    have hpart : ∀ (μ : Fin 4) (x : Pt s E),
        partialAt μ (fun y => ((singlePushforward V z i g y : ℝ) : ℂ)) x =
          chartPushforward (fun _ : Fin 1 => V i) (fun _ => z i)
            (multiDeriv (basisMultiIndex μ) (asFunctionOnOnePoint g)) fun _ => x := by
      intro μ x
      rw [partialAt, hfo]
      exact congrFun (hd _ (by rw [basisMultiIndex_order]; rfl)) _
    have hoff : ∀ (μ : Fin 4) (u : Pt s .euclidean), u ∉ localChartDomain (V i) (z i) →
        partialAt μ (fun u => ((g u : ℝ) : ℂ)) u = 0 := by
      intro μ u hu
      have hsupp : closedSupport (multiDeriv (basisMultiIndex μ) (asFunctionOnOnePoint g)) ⊆
          closedSupport (asFunctionOnOnePoint g) :=
        ((S₁.derivsFlat 1 _ h1).1 _ (by rw [basisMultiIndex_order]; rfl)).2.2.1
      exact eq_zero_of_notMem_closedSupport fun h => hu (h3 (hsupp h) 0 (mem_univ 0))
    refine congrArg₂ max ?_ ?_
    · rw [tupleSupNorm_ofSinglePoint, tupleSupNorm_ofSinglePoint]
      refine iSup_eq_iSup_of_surjOn hentry.2.2.1.surjOn (fun u hu => ?_) (fun y hy => ?_)
        (fun u hu => ?_)
      · rw [singlePushforward_localChart S₁ g hu]
      · rw [singlePushforward_of_notMem S₁ g hy]
        simp
      · rw [image_eq_zero_of_notMem_tsupport fun h => hu (hg.2.2 h)]
        simp
    · refine iSup_eq_iSup_of_surjOn hentry.2.2.1.surjOn (fun u hu => ?_) (fun y hy => ?_)
        (fun u hu => ?_)
      · have he : ∀ μ, partialAt μ (fun y => ((singlePushforward V z i g y : ℝ) : ℂ))
            (localChart s E (z i) u) = partialAt μ (fun u => ((g u : ℝ) : ℂ)) u := by
          intro μ
          rw [hpart]
          exact S₁.chartPushforward_boxChart_apply _ (u := fun _ => u)
            (mem_boxChartDomain_single.mpr hu)
        simp only [gradNorm, gradient, he]
      · rw [gradNorm_eq_zero_of_partialAt]
        · simp
        · intro μ
          rw [hpart]
          have hne : (fun _ : Fin 1 => y) ∉ boxSet fun _ : Fin 1 => V i :=
            fun h => hy (h 0 (mem_univ 0))
          exact S₁.chartPushforward_of_notMem_boxSet _ hne
      · rw [gradNorm_eq_zero_of_partialAt fun μ => hoff μ u hu]
        simp
end OneCoordinate
theorem transportTensor_of_setup (S : ChartSetup V z)
    (S₁ : ∀ i, ChartSetup (fun _ : Fin 1 => V i) (fun _ => z i)) : TransportTensor V z := by
  refine ⟨fun φ _ => ?_, fun g _ => ?_⟩
  · funext u
    by_cases hu : u ∈ boxChartDomain V z
    · rw [chartPullback_of_mem _ hu]
      exact Finset.prod_congr rfl fun i _ =>
        (singlePullback_of_mem _ (hu i (mem_univ i))).symm
    · rw [chartPullback_of_notMem _ hu]
      have hex : ∃ i, u i ∉ localChartDomain (V i) (z i) := by
        by_contra hall
        exact hu fun i _ => not_not.mp (not_exists.mp hall i)
      obtain ⟨i, hi⟩ := hex
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (singlePullback_of_notMem _ hi)).symm
  · funext y
    by_cases hy : y ∈ boxSet V
    · obtain ⟨u, hu, rfl⟩ := S.bijOn.surjOn hy
      rw [S.chartPushforward_boxChart_apply _ hu]
      exact Finset.prod_congr rfl fun i _ =>
        (singlePushforward_localChart (S₁ i) _ (hu i (mem_univ i))).symm
    · rw [S.chartPushforward_of_notMem_boxSet _ hy]
      have hex : ∃ i, y i ∉ V i := by
        by_contra hall
        exact hy fun i _ => not_not.mp (not_exists.mp hall i)
      obtain ⟨i, hi⟩ := hex
      exact (Finset.prod_eq_zero (Finset.mem_univ i)
        (singlePushforward_of_notMem (S₁ i) _ hi)).symm
theorem denseIn_tensorSpan (hB : BoundedMultilinearFormIsDistribution) (S : ChartSetup V z)
    (S₁ : ∀ i, ChartSetup (fun _ : Fin 1 => V i) (fun _ => z i)) :
    DenseInTestFns (boxSet V) (tensorSpan V) := by
  refine ⟨?_, fun F hF => ?_⟩
  · rintro _ ⟨m, φ, hφ, rfl⟩
    refine Finset.sum_induction _ (· ∈ testFns (boxSet V))
      (fun a b ha hb => ?_) (zero_mem_testFns _) (fun k _ => ?_)
    · simpa using ((S.lincomb _ S.isOpen_boxSet) a ha b hb 1 1).1
    · exact (S.tensors V (φ k) (fun i => (S.small.2 i).1) fun i => by
        rw [singletonTupleSet_eq_boxSet]
        exact hφ k i).1
  · have hpull := S.chartPullback_mem_testFns hF
    have hdiam : 0 < (maxDiam V).toReal :=
      ENNReal.toReal_pos (maxDiam_pos S.metric S.small).ne'
        (maxDiam_lt_injRadius S.small).ne_top
    have hinBall : IsOpenTupleInBall (maxDiam V).toReal
        (fun i => localChartDomain (V i) (z i)) :=
      ⟨S.small.1, hdiam, fun i => ⟨(S.coordIso i).1, (S.coordIso i).2.2.2.2.1⟩⟩
    obtain ⟨hcut, ⟨χ, hχ, hone⟩, hseq⟩ :=
      (hB s n (maxDiam V).toReal 0 (fun i => localChartDomain (V i) (z i)) hinBall le_rfl
        (fun _ => 0) (fun _ _ _ _ _ _ _ _ => by simp) (fun _ => by simp)).1 ⟨_, hpull⟩
    obtain ⟨Fs, hFs, hconv⟩ := hseq χ (hcut χ hχ hone)
    have hmem : ∀ t, Fs t ∈ testFns (boxChartDomain V z) := hconv.1
    refine ⟨fun t => chartPushforward V z (Fs t), fun t => ?_, ?_⟩
    · obtain ⟨m, φ, hφ, he⟩ := hFs t
      refine ⟨m, fun l i => singlePushforward V z i (φ l i), fun l i => ?_, ?_⟩
      · rw [ofSinglePoint_singlePushforward]
        refine (S₁ i).chartPushforward_mem_testFns ?_
        have h := (hφ l i).1
        rw [singletonTuples_eq_boxSet] at h
        exact h
      · change chartPushforward V z (Fs t) = _
        rw [he, chartPushforward_sum]
        exact Finset.sum_congr rfl fun l _ =>
          (transportTensor_of_setup S S₁).2 (φ l) fun i => by
            have h := (hφ l i).1
            rw [singletonTuples_eq_boxSet] at h
            exact h
    · have hiff := S.transportTestFnsDistribs.2.2.1
        (fun t => chartPushforward V z (Fs t)) F
        (fun t => S.chartPushforward_mem_testFns (hmem t)) hF
      refine hiff.mpr ?_
      have he : (fun t => chartPullback V z (chartPushforward V z (Fs t))) = Fs :=
        funext fun t => S.chartPullback_chartPushforward (hmem t).2.2
      rw [he]
      exact hconv
end Entries
theorem chartSetup_of (hL : DistanceFacts.MetricFactsClaim) (hT : TupleTopology.Holds)
    (hR : TestFnOperations) {s : Conventions.StandingParameters}
    {E : Ambient} {n : ℕ} {V : Fin n → Set (Pt s E)} {z : Fin n → Fin 4 → ℝ}
    (hV : IsSmallOpenTuple V) (hz : IsBasePoint V z) : ChartSetup V z := by
  have opsE := hR s E n hV.1
  have opsR := hR s .euclidean n hV.1
  have topE := (hT s E).1 n hV.1
  have topR := (hT s .euclidean).1 n hV.1
  exact ⟨hL s E, hV, hz, topE.1, topE.2.1, topR.2.1, topE.2.2.2.2, topR.2.2.2.2,
    fun Ω hΩ => (opsE.2.1 Ω hΩ).2.1, fun Ω hΩ => (opsR.2.1 Ω hΩ).2.1, opsE.2.2.2⟩
theorem chartTransport_holds (hL : DistanceFacts.MetricFactsClaim) (hT : TupleTopology.Holds)
    (hR : TestFnOperations) (hB : BoundedMultilinearFormIsDistribution) :
    ChartTransport.statement := by
  intro s E n V hV
  refine ⟨?_, fun z hz => ?_⟩
  · choose y hy using fun i => (hV.2 i).2.1
    obtain ⟨x, hx⟩ := tupleProj_surjective s E n y
    refine ⟨(flattenCoords n).symm x, fun i => ?_⟩
    rw [show proj s E ((flattenCoords n).symm x i) = y i from congrFun hx i]
    exact hy i
  · have setup : ChartSetup V z := chartSetup_of hL hT hR hV hz
    have setup₁ : ∀ i, ChartSetup (fun _ : Fin 1 => V i) (fun _ => z i) := fun i =>
      chartSetup_of hL hT hR ⟨le_rfl, fun _ => hV.2 i⟩ fun _ => hz i
    exact ⟨⟨maxDiam_pos setup.metric hV, maxDiam_lt_injRadius hV⟩, setup.coordIso,
      setup.boxIso, setup.pullbackPreservesCn, setup.pushforwardPreservesCn,
      setup.transportTestFnsDistribs, fun i => transportCoord_of_setup (setup₁ i) (setup.coordIso i),
      transportTensor_of_setup setup setup₁, denseIn_tensorSpan hB setup setup₁⟩
end YangMills.Construction.AmbientPoints.ChartTransportProof
