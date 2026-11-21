import YangMills.Construction.CellOfTheFlow.LongClassesAtAllLevelsProof
import YangMills.Construction.CellOfTheFlow.TheCellEventReadsItsCellProof
import YangMills.Construction.ClusterExpansionOfAStep.ChartCoordinateIsBorel
import YangMills.Construction.ClusterExpansionOfAStep.FrameIsContinuousWhereItIsRead
import YangMills.Construction.ResponseInTheExpansion.CurvatureOfAStepFallsByHalfProof
import YangMills.Construction.ResponseInTheExpansion.FluctuationsOfAStepAreBorel
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory Filter Topology
namespace YangMills.Construction.ResponseInTheExpansion
open TorusFields TorusLumps StepSettings RenormalizationStepParameters StepMarks StepCosts StepFrames ColdChain BlockAverages
  LumpContours WeightedResponses ClusterExpansionOfAStep
namespace StepDeviationMeasurable
private theorem scale_bounds (B : ℝ) (hB : 0 < B) : ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → ∀ x' : ℝ,
    |x' - x| ≤ 4 * B * Real.log x ^ 2 →
    16 ≤ clusterRange x' / 2 ^ 11 ∧
      ((clusterRange x' / 2 ^ 11 : ℕ) : ℝ) + (⌊x ^ ((1 : ℝ) / 20)⌋₊ : ℝ) / 8 + 4 ≤ (⌊x ^ ((1 : ℝ) / 20)⌋₊ : ℝ) := by
  have h1 : ∀ᶠ x : ℝ in atTop, 4 * B * Real.log x ^ 2 ≤ x / 2 := by
    have h := isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1)
    have h' := h.def (show (0 : ℝ) < 1 / (8 * B) by positivity)
    filter_upwards [h', eventually_gt_atTop 1] with x hx hx1
    have hl : 0 ≤ Real.log x := Real.log_nonneg hx1.le
    have e : Real.log x ^ (2 : ℝ) = Real.log x ^ 2 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [e, Real.rpow_one, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by linarith)] at hx
    have h2 := mul_le_mul_of_nonneg_left hx (show 0 ≤ 8 * B by positivity)
    have e2 : 8 * B * (1 / (8 * B) * x) = x := by field_simp
    linarith
  have h2 : ∀ᶠ x : ℝ in atTop, (2 : ℝ) ^ 20 ≤ x ^ ((1 : ℝ) / 100) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 100)).eventually_ge_atTop _
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp (h1.and (h2.and (eventually_ge_atTop (1 : ℝ))))
  refine ⟨max x₀ 1, le_max_right _ _, fun x hx x' hx' => ?_⟩
  obtain ⟨a1, a2, a3⟩ := hx₀ x ((le_max_left _ _).trans hx)
  have hx0 : 0 < x := by linarith
  obtain ⟨hlo, hhi⟩ := abs_le.mp hx'
  have hx'lo : x / 2 ≤ x' := by linarith
  have hx'hi : x' ≤ 2 * x := by linarith
  have hx'0 : 0 ≤ x' := by linarith
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = x ^ ((1 : ℝ) / 100) := ⟨_, rfl⟩
  rw [← hv] at a2
  have hv0 : 0 ≤ v := by rw [hv]; positivity
  have t1 : (1 : ℝ) ≤ 2 ^ ((1 : ℝ) / 100) := Real.one_le_rpow (by norm_num) (by norm_num)
  have t2 : (2 : ℝ) ^ ((1 : ℝ) / 100) ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (x := 2) (by norm_num) (show (1 : ℝ) / 100 ≤ 1 by norm_num)
  have hrlo : v / 2 ≤ (clusterRange x' : ℝ) := by
    have e1 : (x / 2) ^ ((1 : ℝ) / 100) = v / 2 ^ ((1 : ℝ) / 100) := by
      rw [hv]
      exact Real.div_rpow hx0.le (by norm_num) _
    have e4 : v / 2 ≤ v / 2 ^ ((1 : ℝ) / 100) := div_le_div_of_nonneg_left hv0 (by linarith) t2
    have e5 : (x / 2) ^ ((1 : ℝ) / 100) ≤ x' ^ ((1 : ℝ) / 100) :=
      Real.rpow_le_rpow (by positivity) hx'lo (by norm_num)
    have e6 : x' ^ ((1 : ℝ) / 100) ≤ (clusterRange x' : ℝ) := Nat.le_ceil _
    linarith
  have hrhi : (clusterRange x' : ℝ) ≤ 2 * v + 1 := by
    have e1 : (2 * x) ^ ((1 : ℝ) / 100) = 2 ^ ((1 : ℝ) / 100) * v := by
      rw [hv]
      exact Real.mul_rpow (by norm_num) hx0.le
    have e2 : (2 : ℝ) ^ ((1 : ℝ) / 100) * v ≤ 2 * v := mul_le_mul_of_nonneg_right t2 hv0
    have e5 : x' ^ ((1 : ℝ) / 100) ≤ (2 * x) ^ ((1 : ℝ) / 100) := Real.rpow_le_rpow hx'0 hx'hi (by norm_num)
    have e6 := (Nat.ceil_lt_add_one (Real.rpow_nonneg hx'0 ((1 : ℝ) / 100))).le
    have e : (clusterRange x' : ℝ) = (⌈x' ^ ((1 : ℝ) / 100)⌉₊ : ℝ) := rfl
    rw [e]
    linarith
  have hv1 : (2 : ℝ) ≤ v := by
    have : (2 : ℝ) ≤ 2 ^ 20 := by norm_num
    linarith
  constructor
  · rw [Nat.le_div_iff_mul_le (by norm_num)]
    have h : (32768 : ℝ) ≤ (clusterRange x' : ℝ) := by
      norm_num at a2
      linarith
    have h' : 32768 ≤ clusterRange x' := by exact_mod_cast h
    norm_num
    exact h'
  · have hw : x ^ ((1 : ℝ) / 20) = v ^ 5 := by
      rw [hv, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      norm_num
    have hfl : v ^ 5 - 1 ≤ (⌊x ^ ((1 : ℝ) / 20)⌋₊ : ℝ) := by
      have := (Nat.lt_floor_add_one (x ^ ((1 : ℝ) / 20))).le
      rw [hw] at this ⊢
      linarith
    have hm : ((clusterRange x' / 2 ^ 11 : ℕ) : ℝ) ≤ (clusterRange x' : ℝ) := by
      exact_mod_cast Nat.div_le_self _ _
    have hv4 : (16 : ℝ) ≤ v ^ 4 := by
      have : (2 : ℝ) ^ 4 ≤ v ^ 4 := pow_le_pow_left₀ (by norm_num) hv1 4
      norm_num at this ⊢
      linarith
    have hv5 : 16 * v ≤ v ^ 5 := by
      have : 16 * v ≤ v ^ 4 * v := mul_le_mul_of_nonneg_right hv4 hv0
      have e : v ^ 4 * v = v ^ 5 := by ring
      linarith
    linarith
private theorem mem_supBall {n : ℕ} [NeZero n] {o z : TorusSite n} {R : ℝ} :
    z ∈ supBall o R ↔ (supDist z o : ℝ) ≤ R := by
  simp [supBall]
private theorem coldNearSite_of_ball {n : ℕ} [NeZero n] {V : TorusField n} {o : TorusSite n} {R s : ℝ}
    (hb : IsColdOnBall s V o R) (Y : TorusSite n) (ρ : ℕ)
    (hin : ∀ a, OffsetInBox ρ a → Y + siteOfInt a ∈ supBall o R) : ColdNearSite s ρ Y V := by apply _root_.YangMills.DeltaSharedProofs.p502503 <;> assumption
private theorem add_mem_supBall {n : ℕ} [NeZero n] {o Y : TorusSite n} {D R : ℝ} {ρ : ℕ}
    (hY : (supDist Y o : ℝ) ≤ D) (hDR : D + ρ ≤ R) (a : Fin 4 → ℤ) (ha : OffsetInBox ρ a) :
    Y + siteOfInt a ∈ supBall o R := by apply _root_.YangMills.SharedProofs.p100246 <;> assumption
private theorem measurableSet_isColdOnBall {n : ℕ} [NeZero n] (s : ℝ) (o : TorusSite n) (r : ℝ) :
    MeasurableSet {V : TorusField n | IsColdOnBall s V o r} := by
  have e : {V : TorusField n | IsColdOnBall s V o r} =
      ⋂ p ∈ plaquettesIn (supBall o r), {V : TorusField n | curvature V p.1 p.2.1 p.2.2 < s} := by
    ext V
    simp [IsColdOnBall]
  rw [e]
  exact Finset.measurableSet_biInter _ fun p _ =>
    (isOpen_lt (continuous_curvature _ _ _) continuous_const).measurableSet
private theorem imaginaryComponent_sub (e : Fin 3) (X Y : imaginaryQuaternions) :
    imaginaryComponent e (X - Y) = imaginaryComponent e X - imaginaryComponent e Y := by
  fin_cases e <;> simp [imaginaryComponent]
private theorem continuous_imaginaryCoord (e : Fin 3) :
    Continuous fun q : ℍ[ℝ] => (![q.imI, q.imJ, q.imK] e : ℝ) := by
  fin_cases e
  · exact Quaternion.continuous_imI
  · exact Quaternion.continuous_imJ
  · exact Quaternion.continuous_imK
private theorem measurable_imaginaryComponent {Ξ : Type} [MeasurableSpace Ξ] {g : Ξ → imaginaryQuaternions}
    (hg : MeasurableQuaternion fun p => ((g p : imaginaryQuaternions) : ℍ[ℝ])) (e : Fin 3) :
    Measurable fun p => imaginaryComponent e (g p) := by
  fin_cases e
  · exact hg.2.1
  · exact hg.2.2.1
  · exact hg.2.2.2
abbrev _root_.YangMills.SharedProofs.p32747 := @measurable_imaginaryComponent
private theorem measurable_indicator_sub {n n' : ℕ} [NeZero n] [NeZero n'] {A : Set (TorusField n)}
    (hA : MeasurableSet A) {f : TorusField n → imaginaryQuaternions}
    (hf : ContinuousOn (fun V => ((f V : imaginaryQuaternions) : ℍ[ℝ])) A)
    {g : TorusField n × TorusField n' → imaginaryQuaternions}
    (hg : MeasurableQuaternion fun p => ((g p : imaginaryQuaternions) : ℍ[ℝ])) (e : Fin 3) :
    Measurable (Set.indicator {p : TorusField n × TorusField n' | p.1 ∈ A}
      fun p => imaginaryComponent e (g p - f p.1)) := by
  classical
  have hc : ContinuousOn (fun V => imaginaryComponent e (f V)) A :=
    (continuous_imaginaryCoord e).comp_continuousOn hf
  have hp : Measurable (A.piecewise (fun V => imaginaryComponent e (f V)) fun _ => (0 : ℝ)) :=
    ContinuousOn.measurable_piecewise hc continuousOn_const hA
  have hS : MeasurableSet {p : TorusField n × TorusField n' | p.1 ∈ A} := measurable_fst hA
  have h1 : Measurable (Set.indicator {p : TorusField n × TorusField n' | p.1 ∈ A}
      fun p => imaginaryComponent e (g p)) :=
    (measurable_imaginaryComponent hg e).indicator hS
  have e1 : (Set.indicator {p : TorusField n × TorusField n' | p.1 ∈ A}
      fun p => imaginaryComponent e (g p - f p.1)) =
      fun p => Set.indicator {p : TorusField n × TorusField n' | p.1 ∈ A}
          (fun p => imaginaryComponent e (g p)) p -
        (A.piecewise (fun V => imaginaryComponent e (f V)) fun _ => (0 : ℝ)) p.1 := by
    funext p
    by_cases h : p.1 ∈ A
    · have h' : p ∈ {p : TorusField n × TorusField n' | p.1 ∈ A} := h
      rw [Set.indicator_of_mem h', Set.indicator_of_mem h', Set.piecewise_eq_of_mem _ _ _ h,
        imaginaryComponent_sub]
    · have h' : p ∉ {p : TorusField n × TorusField n' | p.1 ∈ A} := h
      rw [Set.indicator_of_notMem h', Set.indicator_of_notMem h', Set.piecewise_eq_of_notMem _ _ _ h, sub_zero]
  rw [e1]
  exact h1.sub (hp.comp measurable_fst)
private theorem measurableSet_hotCoreSites_eq (R : StepSetup) {n : ℕ} [NeZero n] (C : Finset (TorusSite n)) :
    MeasurableSet {V : TorusField n | hotCoreSites R V = C} := by apply _root_.YangMills.SharedProofs.p5873 <;> assumption
private theorem measurableSet_sigma_fst {A : Type} {β : A → Type} [∀ a, MeasurableSpace (β a)] (a : A) :
    MeasurableSet {z : Sigma β | z.1 = a} := by apply _root_.YangMills.SharedProofs.p1937 <;> assumption
private theorem measurableSet_of_countable_fibres {X D : Type} [MeasurableSpace X] [Countable D] (f : X → D)
    (hf : ∀ d, MeasurableSet {x | f x = d}) (P : D → Prop) : MeasurableSet {x | P (f x)} := by apply _root_.YangMills.SharedProofs.p26374 <;> assumption
variable {ℓ : StepParameters}
private theorem measurableSet_stageState_support (T : StageTower ℓ) (s n : ℕ) [NeZero n]
    (hq : Measurable (stageState T s n)) (a : Finset (TorusSite n)) :
    MeasurableSet {u : MarkedSample ℓ s n | (stageState T s n u).2.1 = a} :=
  hq (measurable_snd (measurableSet_sigma_fst (β := fun Y : Finset (TorusSite n) => Y → (T.stage s).labels.Ω) a))
private theorem measurableSet_stepEvent (T : StageTower ℓ)
    (hs : ∀ (s n : ℕ) [NeZero n], Measurable (stageState T s n)) (t n : ℕ) [NeZero n] (o : TorusSite n) (m : ℝ) :
    MeasurableSet {u : MarkedSample ℓ (t + 1) n |
      Disjoint (stageState T (t + 1) n u).2.1 (supBall o m) ∧ StepAvoids T t m o u} := by
  classical
  have h1 : MeasurableSet {u : MarkedSample ℓ (t + 1) n |
      Disjoint (stageState T (t + 1) n u).2.1 (supBall o m)} :=
    measurableSet_of_countable_fibres (fun u : MarkedSample ℓ (t + 1) n => (stageState T (t + 1) n u).2.1)
      (measurableSet_stageState_support T _ n (hs _ n)) (fun Y => Disjoint Y (supBall o m))
  have hb : Measurable (fun u : MarkedSample ℓ (t + 1) n => (u.1 : MarkedSample ℓ t (n * ℓ.side))) :=
    (measurable_fst : Measurable fun u : MarkedSample ℓ t (n * ℓ.side) × StepOutcome ℓ n => u.1)
  have hc : Measurable (fun u : MarkedSample ℓ (t + 1) n => (u.2.2.2 : BondSet (n * ℓ.side))) :=
    (measurable_snd.comp (measurable_snd.comp measurable_snd) :
      Measurable fun u : MarkedSample ℓ t (n * ℓ.side) × StepOutcome ℓ n => u.2.2.2)
  have hv : Measurable (fun u : MarkedSample ℓ (t + 1) n => (u.2.2.1 : TorusField n)) :=
    (measurable_fst.comp (measurable_snd.comp measurable_snd) :
      Measurable fun u : MarkedSample ℓ t (n * ℓ.side) × StepOutcome ℓ n => u.2.2.1)
  have hf : ∀ d : Finset (TorusSite (n * ℓ.side)) × Finset (TorusBond (n * ℓ.side)) × Finset (TorusSite n),
      MeasurableSet {u : MarkedSample ℓ (t + 1) n |
        (((stageState T t (n * ℓ.side) u.1).2.1, u.2.2.2, hotCoreSites (T.stage t).toStepSetup u.2.2.1) :
          Finset (TorusSite (n * ℓ.side)) × Finset (TorusBond (n * ℓ.side)) × Finset (TorusSite n)) = d} := by
    rintro ⟨d₁, d₂, d₃⟩
    have e : {u : MarkedSample ℓ (t + 1) n |
        (((stageState T t (n * ℓ.side) u.1).2.1, u.2.2.2, hotCoreSites (T.stage t).toStepSetup u.2.2.1) :
          Finset (TorusSite (n * ℓ.side)) × Finset (TorusBond (n * ℓ.side)) × Finset (TorusSite n)) = (d₁, d₂, d₃)} =
        ((fun u : MarkedSample ℓ (t + 1) n => (u.1 : MarkedSample ℓ t (n * ℓ.side))) ⁻¹'
          {w | (stageState T t (n * ℓ.side) w).2.1 = d₁}) ∩
        (((fun u : MarkedSample ℓ (t + 1) n => (u.2.2.2 : BondSet (n * ℓ.side))) ⁻¹' {w | w = d₂}) ∩
          ((fun u : MarkedSample ℓ (t + 1) n => (u.2.2.1 : TorusField n)) ⁻¹'
            {V | hotCoreSites (T.stage t).toStepSetup V = d₃})) := by
      ext u
      constructor
      · intro h
        have g₁ : (stageState T t (n * ℓ.side) u.1).2.1 = d₁ := congrArg
          (fun z : Finset (TorusSite (n * ℓ.side)) × Finset (TorusBond (n * ℓ.side)) × Finset (TorusSite n) =>
            z.1) h
        have g₂ : (u.2.2.2 : Finset (TorusBond (n * ℓ.side))) = d₂ := congrArg
          (fun z : Finset (TorusSite (n * ℓ.side)) × Finset (TorusBond (n * ℓ.side)) × Finset (TorusSite n) =>
            z.2.1) h
        have g₃ : hotCoreSites (T.stage t).toStepSetup u.2.2.1 = d₃ := congrArg
          (fun z : Finset (TorusSite (n * ℓ.side)) × Finset (TorusBond (n * ℓ.side)) × Finset (TorusSite n) =>
            z.2.2) h
        exact ⟨g₁, g₂, g₃⟩
      · rintro ⟨h1, h2, h3⟩
        exact Prod.ext h1 (Prod.ext h2 h3)
    rw [e]
    exact (hb (measurableSet_stageState_support T t _ (hs t _) d₁)).inter
      ((hc (MeasurableSpace.measurableSet_top)).inter (hv (measurableSet_hotCoreSites_eq _ d₃)))
  have h2 : MeasurableSet {u : MarkedSample ℓ (t + 1) n | StepAvoids T t m o u} :=
    measurableSet_of_countable_fibres (fun u : MarkedSample ℓ (t + 1) n =>
      (((stageState T t (n * ℓ.side) u.1).2.1, u.2.2.2, hotCoreSites (T.stage t).toStepSetup u.2.2.1) :
        Finset (TorusSite (n * ℓ.side)) × Finset (TorusBond (n * ℓ.side)) × Finset (TorusSite n))) hf
      (fun d => FreeCoresAvoid (T.stage t).toStepSetup d.1 d.2.1 d.2.2 (supBall o m))
  exact h1.inter h2
end StepDeviationMeasurable
open StepDeviationMeasurable in
theorem stepDeviationMeasurable (hrun : FlowWhereExpansionReturns)
    (hch : ChartCoordMeasurable) (hfr : continuousOn_frameCoord_of_cold)
    (hst : StageStatesMeasurableStatement) : stepDeviationMeasurableStatement := by
  intro a _
  obtain ⟨C₀, hC₀⟩ := hrun
  refine ⟨0, fun _ => 1, C₀, fun _ => one_pos, ?_⟩
  intro L _ _ T _ _ hD _ _ _ hCder
  refine ⟨T.floorMin, fun y hy hret _ => ?_⟩
  have hfit : (T.stepParameters y).Admissible := hD.fits y hy
  have hrun' := (hC₀ (T.stepParameters y) hfit hCder hret).2
  have hσ : 0 < (T.stepParameters y).threshold := hfit.σ_pos
  have hσA : (T.stepParameters y).threshold ≤ T.σA := by
    have h1 := hD.σ_le
    have h2 : (T.stepParameters y).threshold = T.threshold := rfl
    rw [h2] at hσ ⊢
    linarith
  obtain ⟨x₀, hx₀1, hfl⟩ := scale_bounds (T.stepParameters y).B hfit.B_pos
  refine ⟨x₀, ?_⟩
  intro Tw β k n _ nn j o hloc hj
  have hβ : (T.stepParameters y).y₁ ≤ β := hloc.coupling_ge 0 (Nat.zero_le _)
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (couplingFlow (T.stepParameters y) β k).1 := ⟨_, rfl⟩
  have hBpos := hfit.B_pos
  have hrunb : ∀ i, i ≤ 2 * chainDepth x →
      |(couplingFlow (T.stepParameters y) β (k + i)).1 - x| ≤ 2 * (T.stepParameters y).B * i := by
    intro i
    induction i with
    | zero =>
      intro _
      simp [hx]
    | succ i ih =>
      intro hi
      have h1 := ih (by omega)
      have h2 : |(couplingFlow (T.stepParameters y) β (k + i + 1)).1 - (couplingFlow (T.stepParameters y) β (k + i)).1|
          ≤ 2 * (T.stepParameters y).B :=
        ((hrun' β hβ).1 (k + i)).2 (fun l hl => hloc.coupling_ge l (by rw [← hx]; omega))
      have h3 := abs_sub_le (couplingFlow (T.stepParameters y) β (k + i + 1)).1
        (couplingFlow (T.stepParameters y) β (k + i)).1 x
      have e : k + (i + 1) = k + i + 1 := rfl
      rw [e]
      push_cast
      linarith
  have hj' : j < 2 * chainDepth x := by
    rw [hx]
    exact hj
  have hxt : |(couplingFlow (T.stepParameters y) β (k + j)).1 - x| ≤ 4 * (T.stepParameters y).B * Real.log x ^ 2 := by
    have h1 := hrunb j hj'.le
    have h2 : (chainDepth x : ℝ) ≤ Real.log x ^ 2 := Nat.floor_le (sq_nonneg _)
    have h3 : (j : ℝ) ≤ 2 * (chainDepth x : ℝ) := by exact_mod_cast hj'.le
    have h4 : 2 * (T.stepParameters y).B * (j : ℝ) ≤ 2 * (T.stepParameters y).B * (2 * Real.log x ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hxfloor : x₀ ≤ x := by
    rw [hx]
    exact hloc.floor_le
  obtain ⟨h16, hsum⟩ := hfl x hxfloor _ hxt
  have hlev : (Tw.stage (k + j)).coupling = (couplingFlow (T.stepParameters y) β (k + j)).1 :=
    hloc.onFamily.coupling_eq _ (by rw [← hx]; omega)
  have htab := hloc.onFamily.onFamily (k + j) (by rw [← hx]; omega)
  have hρA : (Tw.stage (k + j)).anchorRadius = T.ρA := htab.anchorRadius_eq
  have hm₀ : (Tw.stage (k + j)).toStepSetup.frameReach =
      clusterRange (couplingFlow (T.stepParameters y) β (k + j)).1 / 2 ^ 11 :=
    congrArg (· / 2 ^ 11) (congrArg clusterRange hlev)
  have hside : localBlockSide (T.stepParameters y) β k = ⌊x ^ ((1 : ℝ) / 20)⌋₊ := by
    rw [hx]
    rfl
  have hn₁ : 2 ^ 10 * (⌊x ^ ((1 : ℝ) / 20)⌋₊ : ℝ) ≤ (n : ℝ) := by
    have := hloc.side_ge
    rw [← hx] at this
    exact this
  have hchain : ColdChainConstants (T.stepParameters y).coupling T.δ₁ (T.stepParameters y).side T.lam
      (Tw.stage (k + j)).anchorRadius T.σA T.cg T.N := by
    rw [hρA]
    exact hD.chain
  rw [← hm₀] at h16 hsum
  rw [← hside] at hsum hn₁
  have hst' : ∀ (s n : ℕ) [NeZero n], Measurable (stageState Tw s n) := hst (T.stepParameters y) hfit Tw
  refine ⟨fun b e hb => ?_, measurableSet_stepEvent Tw hst' (k + j) n o _⟩
  unfold stepDeviation frameDeviation
  generalize (Tw.stage (k + j)).toStepSetup.frameReach = m₀ at h16 hsum ⊢
  generalize localBlockSide (T.stepParameters y) β k = m at hsum hn₁ hb ⊢
  have hbm := Finset.mem_filter.mp hb
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have h4 : ((m₀ + 4 : ℕ) : ℝ) ≤ (m : ℝ) := by
    push_cast
    linarith
  have h4' : m₀ + 4 ≤ m := by exact_mod_cast h4
  have hn₂ : 2 ^ 10 * m ≤ n := by exact_mod_cast hn₁
  have hbig : 4 * m₀ + 5 < n := by omega
  have n64 : 64 ≤ n := by omega
  obtain ⟨hc, -⟩ := hfr (T.stepParameters y) T.δ₁ T.lam (Tw.stage (k + j)).anchorRadius T.σA T.cg T.N hfit hchain
    hσA (k + j) m₀ n h16 n64 b hbm.1
  have hY : (supDist (parentBlock (T.stepParameters y).side b.1) o : ℝ) ≤ (m : ℝ) / 8 := mem_supBall.mp hbm.2
  have hcold : ContinuousOn (fun V : TorusField n =>
      ((frameCoord (T.stepParameters y) (Tw.stage (k + j)).anchorRadius (k + j) m₀ V b : imaginaryQuaternions) : ℍ[ℝ]))
      {V : TorusField n | IsColdOnBall (T.stepParameters y).threshold V o (m : ℝ)} :=
    (hc hbig).mono fun V hV => coldNearSite_of_ball hV _ _ (add_mem_supBall hY (by linarith))
  exact measurable_indicator_sub (measurableSet_isColdOnBall _ o _) hcold (hch (T.stepParameters y) n b) e
end YangMills.Construction.ResponseInTheExpansion
end
