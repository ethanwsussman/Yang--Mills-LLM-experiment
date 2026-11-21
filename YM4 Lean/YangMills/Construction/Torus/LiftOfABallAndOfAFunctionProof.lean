import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import YangMills.Construction.Torus.LiftOfABallAndOfAFunction
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric PeriodicLattice ReflectionPositivity Conventions
namespace TestFunctions.BallLift
theorem euclidNormVec_nonneg (v : Fin 4 → ℝ) : 0 ≤ euclidNormVec v := Real.sqrt_nonneg _
theorem euclidNormVec_zero : euclidNormVec (0 : Fin 4 → ℝ) = 0 := by simp [euclidNormVec]
theorem euclidNormVec_neg (v : Fin 4 → ℝ) : euclidNormVec (-v) = euclidNormVec v := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_neg <;> assumption
theorem euclidNormVec_sub_comm (x y : Fin 4 → ℝ) :
    euclidNormVec (x - y) = euclidNormVec (y - x) := by apply _root_.YangMills.Construction.AmbientPoints.euclidNormVec_sub_comm <;> assumption
theorem euclidNormVec_add_le (u v : Fin 4 → ℝ) :
    euclidNormVec (u + v) ≤ euclidNormVec u + euclidNormVec v := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_add_le <;> assumption
theorem abs_apply_le_euclidNormVec (v : Fin 4 → ℝ) (i : Fin 4) : |v i| ≤ euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
theorem eq_of_euclidNormVec_sub_nonpos {x y : Fin 4 → ℝ} (h : euclidNormVec (x - y) ≤ 0) :
    x = y := by
  funext i
  have h1 := abs_apply_le_euclidNormVec (x - y) i
  have h2 : |(x - y) i| ≤ 0 := h1.trans h
  have h3 : (x - y) i = 0 := abs_nonpos_iff.1 h2
  simpa [sub_eq_zero] using h3
theorem intCombination_apply (S : ℝ) (n : Fin 4 → ℤ) (i : Fin 4) :
    AxisMirror.intCombination S n i = S * (n i : ℝ) := by
  simp [AxisMirror.intCombination, Finset.sum_apply, PeriodicLattice.coordVec,
    Pi.single_apply]
theorem le_euclidNormVec_intCombination {S : ℝ} (hS : 0 ≤ S) {n : Fin 4 → ℤ} (hn : n ≠ 0) :
    S ≤ euclidNormVec (AxisMirror.intCombination S n) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hn
  have h1 := abs_apply_le_euclidNormVec (AxisMirror.intCombination S n) i
  have h2 : (1 : ℝ) ≤ |(n i : ℝ)| := by
    have : (1 : ℤ) ≤ |n i| := Int.one_le_abs hi
    exact_mod_cast this
  have h3 : |AxisMirror.intCombination S n i| = S * |(n i : ℝ)| := by
    rw [intCombination_apply, abs_mul, abs_of_nonneg hS]
  rw [h3] at h1
  nlinarith
theorem isClosed_closedBallR4 (c : Fin 4 → ℝ) (ρ : ℝ) : IsClosed (closedBallR4 c ρ) := by apply _root_.YangMills.Construction.TestPairs.isClosed_closedBallR4 <;> assumption
theorem mem_closure_iff_euclidNormVec {E : Set (Fin 4 → ℝ)} {x : Fin 4 → ℝ} :
    x ∈ closure E ↔ ∀ r : ℝ, 0 < r → ∃ a ∈ E, euclidNormVec (a - x) < r := by
  constructor
  · intro hx r hr
    have hcont : Continuous fun a : Fin 4 → ℝ => euclidNormVec (a - x) := by
      unfold euclidNormVec
      fun_prop
    obtain ⟨a, haU, haE⟩ := mem_closure_iff.1 hx {a | euclidNormVec (a - x) < r}
      (isOpen_lt hcont continuous_const) (by simpa [euclidNormVec_zero] using hr)
    exact ⟨a, haE, haU⟩
  · intro h
    refine Metric.mem_closure_iff.2 fun ε hε => ?_
    obtain ⟨a, haE, ha⟩ := h ε hε
    refine ⟨a, haE, (dist_pi_lt_iff hε).2 fun i => ?_⟩
    rw [Real.dist_eq]
    have h1 := abs_apply_le_euclidNormVec (a - x) i
    rw [Pi.sub_apply, abs_sub_comm] at h1
    exact lt_of_le_of_lt h1 ha
variable {P : StandingParameters}
def mirrorDataOf (P : StandingParameters) : AxisMirror.MirrorData := ⟨P, 1, one_pos⟩
theorem torusEuclidNorm_isLeast (H : AxisMirror.ProjectionFacts) (y y' : Fin 4 → ℝ) :
    IsLeast (range fun n : Fin 4 → ℤ =>
        euclidNormVec (y - y' + AxisMirror.intCombination (torusSide P.L P.m) n))
      (torusEuclidNorm (torusProj (torusSide P.L P.m) y - torusProj (torusSide P.L P.m) y')) :=
  (H (mirrorDataOf P)).2.1.1 y y'
theorem torusEuclidNorm_proj_le (H : AxisMirror.ProjectionFacts) (y y' : Fin 4 → ℝ) :
    torusEuclidNorm (torusProj (torusSide P.L P.m) y - torusProj (torusSide P.L P.m) y') ≤
      euclidNormVec (y - y') :=
  (H (mirrorDataOf P)).2.1.2.1 y y'
theorem exists_lift_realizing (H : AxisMirror.ProjectionFacts) (y : Fin 4 → ℝ)
    (w : P.Torus) : ∃ y'', torusProj (torusSide P.L P.m) y'' = w ∧
      euclidNormVec (y - y'') = torusEuclidNorm (torusProj (torusSide P.L P.m) y - w) :=
  (H (mirrorDataOf P)).2.1.2.2.1 y w
theorem torusEuclidNorm_sub_comm (H : AxisMirror.ProjectionFacts) (w w' : P.Torus) :
    torusEuclidNorm (w - w') = torusEuclidNorm (w' - w) :=
  (H (mirrorDataOf P)).2.1.2.2.2.1 w w'
theorem torusEuclidNorm_triangle (H : AxisMirror.ProjectionFacts) (w w' w'' : P.Torus) :
    torusEuclidNorm (w - w'') ≤ torusEuclidNorm (w - w') + torusEuclidNorm (w' - w'') :=
  (H (mirrorDataOf P)).2.1.2.2.2.2.2 w w' w''
theorem torusEuclidNorm_self_nonpos (H : AxisMirror.ProjectionFacts) (w : P.Torus) :
    torusEuclidNorm (w - w) ≤ 0 := by
  obtain ⟨y, rfl, -⟩ := exists_lift_realizing H 0 w
  have h := torusEuclidNorm_proj_le (P := P) H y y
  simpa [euclidNormVec_zero] using h
theorem mem_metricClosure_iff (H : AxisMirror.ProjectionFacts)
    {A : Set P.Torus} {w : P.Torus} :
    w ∈ @closure _ (metricTopology P.L P.m) A ↔
      ∀ r : ℝ, 0 < r → ∃ a ∈ A, torusEuclidNorm (a - w) < r := by
  constructor
  · intro hw r hr
    have hopen : @IsOpen _ (metricTopology P.L P.m)
        {y : P.Torus | torusEuclidNorm (y - w) < r} := by
      intro y hy
      have hy' : torusEuclidNorm (y - w) < r := hy
      refine ⟨r - torusEuclidNorm (y - w), sub_pos.2 hy', fun y' hy'' => ?_⟩
      have h1 : torusEuclidNorm (y' - y) < r - torusEuclidNorm (y - w) := hy''
      have h2 := torusEuclidNorm_triangle H y' y w
      show torusEuclidNorm (y' - w) < r
      linarith
    have hmem : w ∈ {y : P.Torus | torusEuclidNorm (y - w) < r} :=
      lt_of_le_of_lt (torusEuclidNorm_self_nonpos H w) hr
    obtain ⟨a, haU, haA⟩ := (@mem_closure_iff _ (metricTopology P.L P.m) _ _).1 hw _ hopen hmem
    exact ⟨a, haA, haU⟩
  · intro h
    refine (@mem_closure_iff _ (metricTopology P.L P.m) _ _).2 fun O hO hwO => ?_
    obtain ⟨r, hr, hsub⟩ := hO w hwO
    obtain ⟨a, haA, ha⟩ := h r hr
    exact ⟨a, hsub ha, haA⟩
variable {ρ : ℝ} {c : Fin 4 → ℝ}
theorem torusEuclidNorm_proj_eq (H : AxisMirror.ProjectionFacts)
    (hρ : IsAdmissibleRadius P.L P.m ρ) {x y : Fin 4 → ℝ} (hx : x ∈ closedBallR4 c ρ)
    (hy : y ∈ closedBallR4 c ρ) :
    torusEuclidNorm (torusProj (torusSide P.L P.m) x - torusProj (torusSide P.L P.m) y) =
      euclidNormVec (x - y) := by
  have hx' : euclidNormVec (x - c) ≤ ρ := hx
  have hy' : euclidNormVec (y - c) ≤ ρ := hy
  have hxy : euclidNormVec (x - y) ≤ 2 * ρ := by
    have h1 := euclidNormVec_add_le (x - c) (c - y)
    rw [sub_add_sub_cancel, euclidNormVec_sub_comm c y] at h1
    linarith
  obtain ⟨hρ0, hρ1⟩ := hρ
  have hS : 0 ≤ torusSide P.L P.m := by linarith
  obtain ⟨⟨n, hn⟩, -⟩ := torusEuclidNorm_isLeast (P := P) H x y
  have hle := torusEuclidNorm_proj_le (P := P) H x y
  have hn' : euclidNormVec (x - y + AxisMirror.intCombination (torusSide P.L P.m) n) =
      torusEuclidNorm (torusProj (torusSide P.L P.m) x - torusProj (torusSide P.L P.m) y) := hn
  by_cases h0 : n = 0
  · subst h0
    have hz : AxisMirror.intCombination (torusSide P.L P.m) 0 = 0 := by
      funext i
      simp [AxisMirror.intCombination]
    rw [← hn', hz, add_zero]
  · exfalso
    have h1 := le_euclidNormVec_intCombination hS h0
    have h2 := euclidNormVec_add_le
      (x - y + AxisMirror.intCombination (torusSide P.L P.m) n) (-(x - y))
    rw [euclidNormVec_neg, add_comm (x - y), add_neg_cancel_right] at h2
    rw [add_comm (x - y)] at hn'
    linarith
theorem injOn_torusProj (H : AxisMirror.ProjectionFacts)
    (hρ : IsAdmissibleRadius P.L P.m ρ) :
    InjOn (torusProj (torusSide P.L P.m)) (closedBallR4 c ρ) := by
  intro x hx y hy hxy
  have h1 := torusEuclidNorm_proj_eq H hρ hx hy
  rw [hxy] at h1
  refine eq_of_euclidNormVec_sub_nonpos ?_
  rw [← h1]
  exact torusEuclidNorm_self_nonpos H _
theorem projIsometricOnBall_of_facts (H : AxisMirror.ProjectionFacts) (P : StandingParameters)
    (z : P.Torus) (ρ : ℝ) (c : Fin 4 → ℝ) (hρ : IsAdmissibleRadius P.L P.m ρ)
    (hc : c ∈ liftsOf z) : projIsometricOnBall P z ρ c := by
  have hz : torusProj (torusSide P.L P.m) c = z := hc
  subst hz
  refine ⟨fun x hx y hy => torusEuclidNorm_proj_eq H hρ hx hy, ?_, injOn_torusProj H hρ, ?_⟩
  · intro x hx
    exact (torusEuclidNorm_proj_le (P := P) H x c).trans hx
  · intro w hw
    have hw' : torusEuclidNorm (w - torusProj (torusSide P.L P.m) c) ≤ ρ := hw
    obtain ⟨y, hy, hyn⟩ := exists_lift_realizing H c w
    refine ⟨y, ?_, hy⟩
    show euclidNormVec (y - c) ≤ ρ
    rw [euclidNormVec_sub_comm, hyn, torusEuclidNorm_sub_comm H]
    exact hw'
theorem closure_subset_closedBallR4 {E : Set (Fin 4 → ℝ)} (hE : E ⊆ closedBallR4 c ρ) :
    closure E ⊆ closedBallR4 c ρ :=
  closure_minimal hE (isClosed_closedBallR4 c ρ)
theorem bijOn_closure_metricClosure (H : AxisMirror.ProjectionFacts) (z : P.Torus)
    (hρ : IsAdmissibleRadius P.L P.m ρ) (hc : c ∈ liftsOf z) {E : Set (Fin 4 → ℝ)}
    (hE : E ⊆ closedBallR4 c ρ) :
    BijOn (torusProj (torusSide P.L P.m)) (closure E)
      (@closure _ (metricTopology P.L P.m) (torusProj (torusSide P.L P.m) '' E)) := by
  have hball := projIsometricOnBall_of_facts H P z ρ c hρ hc
  have hcl := closure_subset_closedBallR4 hE
  refine ⟨?_, (injOn_torusProj H hρ).mono hcl, ?_⟩
  · intro x hx
    refine (mem_metricClosure_iff H).2 fun r hr => ?_
    obtain ⟨a, haE, ha⟩ := mem_closure_iff_euclidNormVec.1 hx r hr
    refine ⟨torusProj (torusSide P.L P.m) a, mem_image_of_mem _ haE, ?_⟩
    rw [torusEuclidNorm_proj_eq H hρ (hE haE) (hcl hx)]
    exact ha
  · intro w hw
    have hw' := (mem_metricClosure_iff H).1 hw
    have hwball : w ∈ closedBallTorus (ℓ := torusSide P.L P.m) z ρ := by
      show torusEuclidNorm (w - z) ≤ ρ
      refine le_of_forall_pos_le_add fun r hr => ?_
      obtain ⟨_, ⟨a, haE, rfl⟩, ha⟩ := hw' r hr
      have h1 := torusEuclidNorm_triangle H w (torusProj (torusSide P.L P.m) a) z
      have h2 : torusEuclidNorm (torusProj (torusSide P.L P.m) a - z) ≤ ρ := hball.2.1 (hE haE)
      have h3 := torusEuclidNorm_sub_comm H w (torusProj (torusSide P.L P.m) a)
      linarith
    obtain ⟨x, hx, rfl⟩ := hball.2.2.2 hwball
    refine ⟨x, mem_closure_iff_euclidNormVec.2 fun r hr => ?_, rfl⟩
    obtain ⟨_, ⟨a, haE, rfl⟩, ha⟩ := hw' r hr
    refine ⟨a, haE, ?_⟩
    rw [← torusEuclidNorm_proj_eq H hρ (hE haE) hx]
    exact ha
variable {f : P.Torus → ℝ}
theorem ballIndicatorLift_of_mem {x : Fin 4 → ℝ} (hx : x ∈ closedBallR4 c ρ) :
    ballIndicatorLift c ρ f x = f (torusProj (torusSide P.L P.m) x) := by
  simp [ballIndicatorLift, Set.indicator, hx]
theorem ballIndicatorLift_of_not_mem {x : Fin 4 → ℝ} (hx : x ∉ closedBallR4 c ρ) :
    ballIndicatorLift c ρ f x = 0 := by
  simp [ballIndicatorLift, Set.indicator, hx]
theorem nonzero_subset_closedBallR4 :
    {x | ballIndicatorLift c ρ f x ≠ 0} ⊆ closedBallR4 c ρ := by
  intro x hx
  by_contra hxB
  exact hx (ballIndicatorLift_of_not_mem hxB)
theorem nonzero_subset_closedBallTorus {z : P.Torus}
    (hsupp : metricSupport f ⊆ closedBallTorus z ρ) :
    {w | f w ≠ 0} ⊆ closedBallTorus (ℓ := torusSide P.L P.m) z ρ :=
  fun _ hw => hsupp (@subset_closure _ (metricTopology P.L P.m) _ _ hw)
theorem bijOn_nonzero_sets (H : AxisMirror.ProjectionFacts) {z : P.Torus}
    (hρ : IsAdmissibleRadius P.L P.m ρ) (hc : c ∈ liftsOf z)
    (hsupp : metricSupport f ⊆ closedBallTorus z ρ) :
    BijOn (torusProj (torusSide P.L P.m)) {x | ballIndicatorLift c ρ f x ≠ 0} {w | f w ≠ 0} := by
  have hball := projIsometricOnBall_of_facts H P z ρ c hρ hc
  refine ⟨?_, (injOn_torusProj H hρ).mono nonzero_subset_closedBallR4, ?_⟩
  · intro x hx
    have hxB := nonzero_subset_closedBallR4 hx
    have hx' : ballIndicatorLift c ρ f x ≠ 0 := hx
    rw [ballIndicatorLift_of_mem hxB] at hx'
    exact hx'
  · intro w hw
    obtain ⟨x, hx, rfl⟩ := hball.2.2.2 (nonzero_subset_closedBallTorus hsupp hw)
    refine ⟨x, ?_, rfl⟩
    show ballIndicatorLift c ρ f x ≠ 0
    rw [ballIndicatorLift_of_mem hx]
    exact hw
theorem bijOn_supports (H : AxisMirror.ProjectionFacts) {z : P.Torus}
    (hρ : IsAdmissibleRadius P.L P.m ρ) (hc : c ∈ liftsOf z)
    (hsupp : metricSupport f ⊆ closedBallTorus z ρ) :
    BijOn (torusProj (torusSide P.L P.m)) (euclidSupport (ballIndicatorLift c ρ f))
      (metricSupport f) := by
  have h := bijOn_closure_metricClosure H z hρ hc (nonzero_subset_closedBallR4 (f := f))
  rw [(bijOn_nonzero_sets H hρ hc hsupp).image_eq] at h
  exact h
theorem euclidSupport_subset_closedBallR4 :
    euclidSupport (ballIndicatorLift c ρ f) ⊆ closedBallR4 c ρ :=
  closure_subset_closedBallR4 nonzero_subset_closedBallR4
theorem isCompact_euclidSupport : IsCompact (euclidSupport (ballIndicatorLift c ρ f)) := by
  refine IsCompact.of_isClosed_subset (isCompact_closedBall c ρ) isClosed_closure ?_
  intro x hx
  have hx' : euclidNormVec (x - c) ≤ ρ := euclidSupport_subset_closedBallR4 hx
  refine Metric.mem_closedBall.2 ?_
  by_cases hρ : 0 ≤ ρ
  · refine (dist_pi_le_iff hρ).2 fun i => ?_
    rw [Real.dist_eq]
    exact (abs_apply_le_euclidNormVec (x - c) i).trans hx'
  · exact absurd ((euclidNormVec_nonneg _).trans hx') hρ
theorem liftProperties_of_facts (H : AxisMirror.ProjectionFacts) (P : StandingParameters)
    (z : P.Torus) (ρ : ℝ) (c : Fin 4 → ℝ) (f : P.Torus → ℝ) (g : (Fin 4 → ℝ) → ℝ)
    (hf : IsFunctionLift z ρ c f g) : liftProperties P ρ c f g := by
  obtain ⟨hρ, hc, hsupp, rfl⟩ := hf
  have hnz := bijOn_nonzero_sets H hρ hc hsupp
  refine ⟨hnz, bijOn_supports H hρ hc hsupp, isCompact_euclidSupport,
    euclidSupport_subset_closedBallR4, ?_, ?_, ?_⟩
  · refine le_antisymm (iSup_le fun x => ?_) (iSup_le fun w => ?_)
    · by_cases hx : x ∈ closedBallR4 c ρ
      · rw [ballIndicatorLift_of_mem hx]
        exact le_iSup (fun w => ENNReal.ofReal ‖f w‖) (torusProj (torusSide P.L P.m) x)
      · rw [ballIndicatorLift_of_not_mem hx]
        simp
    · by_cases hw : f w = 0
      · simp [hw]
      · obtain ⟨x, hx, rfl⟩ := hnz.2.2 (show w ∈ {w | f w ≠ 0} from hw)
        have hxB := nonzero_subset_closedBallR4 hx
        have h := le_iSup (fun x => ENNReal.ofReal ‖ballIndicatorLift c ρ f x‖) x
        simp only [ballIndicatorLift_of_mem hxB] at h
        exact h
  · intro hpos x
    by_cases hx : x ∈ closedBallR4 c ρ
    · rw [ballIndicatorLift_of_mem hx]
      exact hpos _
    · rw [ballIndicatorLift_of_not_mem hx]
  · intro hm
    have hproj : @Measurable _ _ _ (borelSets P.L P.m) (torusProj (torusSide P.L P.m)) :=
      @measurable_generateFrom _ _ _ _ _ fun O hO =>
        (((@continuous_def _ _ _ (metricTopology P.L P.m) _).1 continuous_torusProj)
          O hO).measurableSet
    have hcomp : Measurable (f ∘ torusProj (torusSide P.L P.m)) :=
      @Measurable.comp _ _ _ _ (borelSets P.L P.m) _ _ _ hm hproj
    exact hcomp.indicator (isClosed_closedBallR4 c ρ).measurableSet
theorem liftPairProperties_of_facts (H : AxisMirror.ProjectionFacts) (P : StandingParameters)
    (z : P.Torus) (ρ : ℝ) (c : Fin 4 → ℝ) (f f' : P.Torus → ℝ) (g g' : (Fin 4 → ℝ) → ℝ)
    (hf : IsFunctionLift z ρ c f g) (hf' : IsFunctionLift z ρ c f' g') :
    liftPairProperties P f f' g g' := by
  obtain ⟨hρ, hc, hsupp, rfl⟩ := hf
  obtain ⟨-, -, hsupp', rfl⟩ := hf'
  have hb := bijOn_supports H hρ hc hsupp
  have hb' := bijOn_supports H hρ hc hsupp'
  have hB := euclidSupport_subset_closedBallR4 (c := c) (ρ := ρ) (f := f)
  have hB' := euclidSupport_subset_closedBallR4 (c := c) (ρ := ρ) (f := f')
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · refine le_iInf₂ fun a ha => le_iInf₂ fun b hb₁ => ?_
    obtain ⟨x, hx, rfl⟩ := hb.2.2 ha
    obtain ⟨y, hy, rfl⟩ := hb'.2.2 hb₁
    rw [torusEuclidNorm_proj_eq H hρ (hB hx) (hB' hy)]
    exact iInf₂_le_of_le x hx (iInf₂_le y hy)
  · refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
    rw [← torusEuclidNorm_proj_eq H hρ (hB hx) (hB' hy)]
    exact iInf₂_le_of_le _ (hb.1 hx) (iInf₂_le _ (hb'.1 hy))
  · intro hdisj
    refine Set.disjoint_left.2 fun x hx hx' => ?_
    exact Set.disjoint_left.1 hdisj (hb.1 hx) (hb'.1 hx')
theorem ballAndFunctionLift_of_facts (H : AxisMirror.ProjectionFacts) : BallAndFunctionLift :=
  fun P z ρ c hρ hc => ⟨projIsometricOnBall_of_facts H P z ρ c hρ hc,
    fun f g hf => liftProperties_of_facts H P z ρ c f g hf,
    fun f f' g g' hf hf' => liftPairProperties_of_facts H P z ρ c f f' g g' hf hf'⟩
end TestFunctions.BallLift
end YangMills.Construction
