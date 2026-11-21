import YangMills.Construction.Lattice.BareLatticeAndBarycentres
import YangMills.Construction.Torus.CollinearQuadruplesProof
import YangMills.Construction.Torus.CubesBallsOfTheTorusAndTheirLifts
import YangMills.Construction.Torus.GeometryOfASeparatedQuadrupleProof
import YangMills.Construction.Torus.ProjectionsOfTheSequenceProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set YangMills.Construction.PeriodicLattice YangMills.Construction.TorusMetric YangMills.Construction.TestFunctions YangMills.Construction.TorusMeasure YangMills.Construction.CubesAndBallLifts
open YangMills.Construction.TorusCovering (ProjectionProperties VolumeProperties periodVec)
open Topology Filter
noncomputable section
namespace YangMills.Construction.TorusCubesAndBalls
variable {s : Conventions.StandingParameters}
theorem euclidNormVec_sub_le (t t' : Fin 4 → ℝ) :
    euclidNormVec (t - t') ≤ euclidNormVec t + euclidNormVec t' := by apply _root_.YangMills.Construction.QuadrupleClasses.Collinear.euclidNormVec_sub_le <;> assumption
theorem euclidNormVec_nonneg (t : Fin 4 → ℝ) : 0 ≤ euclidNormVec t := Real.sqrt_nonneg _
theorem euclidNormVec_zero : euclidNormVec 0 = 0 := by simp [euclidNormVec]
theorem euclidNormVec_smul (r : ℝ) (t : Fin 4 → ℝ) :
    euclidNormVec (r • t) = |r| * euclidNormVec t := by apply _root_.YangMills.SharedProofs.p37834 <;> assumption
theorem abs_apply_le_euclidNormVec (t : Fin 4 → ℝ) (μ : Fin 4) : |t μ| ≤ euclidNormVec t := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
theorem eq_zero_of_euclidNormVec_eq_zero {t : Fin 4 → ℝ} (h : euclidNormVec t = 0) : t = 0 := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.eq_zero_of_euclidNormVec_eq_zero <;> assumption
theorem continuous_euclidNormVec : Continuous euclidNormVec := by apply _root_.YangMills.Construction.SeparatedTuples.continuous_euclidNormVec <;> assumption
theorem proj_add (t t' : Fin 4 → ℝ) :
    proj s (t + t') = proj s t + proj s t' := by apply _root_.YangMills.Construction.TorusMeasure.BallProjection.proj_map_add <;> assumption
theorem proj_sub (t t' : Fin 4 → ℝ) :
    proj s (t - t') = proj s t - proj s t' := by apply _root_.YangMills.Construction.TorusMeasure.BallProjection.proj_map_sub <;> assumption
theorem proj_zero : proj s 0 = 0 := by apply _root_.YangMills.Construction.TorusMeasure.TranslatedLatticeCells.proj_map_zero <;> assumption
theorem torusSide_pos (s : Conventions.StandingParameters) : 0 < PeriodicLattice.torusSide s.L s.m := by apply _root_.YangMills.Construction.TorusMeasure.TranslatedLatticeCells.torusSide_pos <;> assumption
theorem eq_zero_of_latticeTranslate_lt {ℓ : ℝ} (hℓ : 0 < ℓ) {k : Fin 4 → ℤ}
    (hk : euclidNormVec (latticeTranslate ℓ k) < ℓ) : k = 0 := by apply _root_.YangMills.Construction.QuadrupleGeometry.eq_zero_of_latticeTranslate_lt <;> assumption
section Facts
variable (hF : ProjectionProperties s)
include hF
theorem proj_eq_zero_iff (t : Fin 4 → ℝ) :
    proj s t = 0 ↔ ∃ k, t = periodVec s k := by
  obtain ⟨-, -, -, -, -, -, -, hker, -, -⟩ := hF
  exact hker t
theorem proj_surjective : Function.Surjective (proj s) := by
  obtain ⟨-, -, -, -, -, -, hsurj, -, -, -⟩ := hF
  exact hsurj
theorem pointNorm_nonneg (u : s.Torus) : 0 ≤ pointNorm u := by apply _root_.YangMills.Construction.TorusMeasure.TranslatedLatticeCells.pointNorm_nonneg <;> assumption
theorem eq_of_proj_eq_of_short {r t : Fin 4 → ℝ} (hcov : proj s r = proj s t)
    (hr : euclidNormVec r < s.side / 2) (ht : euclidNormVec t < s.side / 2) : r = t := by
  have h0 : proj s (r - t) = 0 := by rw [proj_sub, hcov, sub_self]
  obtain ⟨k, hk⟩ := (proj_eq_zero_iff hF _).1 h0
  have hlt : euclidNormVec (latticeTranslate (PeriodicLattice.torusSide s.L s.m) k) <
      PeriodicLattice.torusSide s.L s.m := by
    have h1 := euclidNormVec_sub_le r t
    have h2 : s.side = PeriodicLattice.torusSide s.L s.m := rfl
    rw [hk] at h1
    have h3 : euclidNormVec (periodVec s k) =
      euclidNormVec (latticeTranslate (PeriodicLattice.torusSide s.L s.m) k) := rfl
    rw [h3] at h1
    rw [h2] at hr ht
    linarith
  have hk0 := eq_zero_of_latticeTranslate_lt (torusSide_pos s) hlt
  have : r - t = 0 := by
    rw [hk, hk0]
    funext μ
    simp [periodVec, latticeTranslate]
  exact sub_eq_zero.1 this
end Facts
section Balls
variable (hB : TorusMeasure.BallProjection.BallProjectionStatement)
include hB
theorem proj_center_eq {z : s.Torus} {ϱ : ℝ} {c : Fin 4 → ℝ} (h0 : 0 < ϱ)
    (h1 : ϱ < s.side / 4) (him : proj s '' closedBallR4 c ϱ = closedBallTorus z ϱ) :
    proj s c = z := by
  obtain ⟨hN, ⟨-, hiso⟩, -⟩ := hB s ϱ c h0 h1.le
  have hz : z ∈ closedBallTorus z ϱ := by
    have h2 := hN 0 (by
      rw [euclidNormVec_zero]
      have := torusSide_pos s
      positivity)
    rw [proj_zero, euclidNormVec_zero] at h2
    show torusEuclidNorm (z - z) ≤ ϱ
    rw [sub_self]
    exact (show pointNorm (0 : s.Torus) = 0 from h2).le.trans h0.le
  rw [← him] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  by_contra hne
  have hd : 0 < euclidNormVec (c - t) := by
    refine lt_of_le_of_ne (euclidNormVec_nonneg _) fun h => hne ?_
    rw [sub_eq_zero.1 (eq_zero_of_euclidNormVec_eq_zero h.symm)]
  set d := euclidNormVec (c - t) with hddef
  set x := c + (ϱ / d) • (c - t) with hx
  have hxc : x - c = (ϱ / d) • (c - t) := by rw [hx]; abel
  have hxt : x - t = (1 + ϱ / d) • (c - t) := by
    rw [hx, add_smul, one_smul]
    abel
  have hxB : x ∈ closedBallR4 c ϱ := by
    show euclidNormVec (x - c) ≤ ϱ
    rw [hxc, euclidNormVec_smul, abs_of_pos (div_pos h0 hd), ← hddef]
    field_simp
    exact le_refl _
  have hdist : pointDist (proj s x) (proj s t) = d + ϱ := by
    rw [hiso x hxB t ht]
    show euclidNormVec (x - t) = d + ϱ
    rw [hxt, euclidNormVec_smul, abs_of_pos (by positivity), ← hddef]
    field_simp
  have hin : proj s x ∈ closedBallTorus (proj s t) ϱ := by
    rw [← him]
    exact ⟨x, hxB, rfl⟩
  have hle : pointDist (proj s x) (proj s t) ≤ ϱ := hin
  rw [hdist] at hle
  linarith
theorem isBallLift_iff {z : s.Torus} {ϱ : ℝ} (h0 : 0 < ϱ) (h1 : ϱ < s.side / 4)
    (B : Set (Fin 4 → ℝ)) :
    IsBallLift z ϱ B ↔ ∃ t : Fin 4 → ℝ, proj s t = z ∧ B = closedBallR4 t ϱ := by
  constructor
  · rintro ⟨-, -, ⟨c, rfl⟩, him⟩
    exact ⟨c, proj_center_eq hB h0 h1 him, rfl⟩
  · rintro ⟨t, rfl, rfl⟩
    obtain ⟨-, ⟨hbij, -⟩, -⟩ := hB s ϱ t h0 h1.le
    exact ⟨h0, h1, ⟨t, rfl⟩, hbij.image_eq⟩
theorem liftProperties (hF : ProjectionProperties s) {z : s.Torus} {ϱ : ℝ} (h0 : 0 < ϱ)
    (h1 : ϱ < s.side / 4) {B : Set (Fin 4 → ℝ)} (hl : IsBallLift z ϱ B) :
    LiftProperties s z ϱ B := by
  obtain ⟨c, rfl, rfl⟩ := (isBallLift_iff hB h0 h1 B).1 hl
  obtain ⟨-, ⟨hbij, hiso⟩, -⟩ := hB s ϱ c h0 h1.le
  refine ⟨fun x hx x' hx' => hiso x hx x' hx', fun u hu => ?_, ?_⟩
  · obtain ⟨t, ht, rfl⟩ := hbij.surjOn hu
    exact ⟨t, ⟨ht, rfl⟩, fun t' ht' => hbij.injOn ht'.1 ht ht'.2⟩
  · intro u hu w hw t t' ht ht'
    have e1 : proj s (t - t') = u - w := by rw [proj_sub, ht.2, ht'.2]
    have e2 : euclidNormVec (t - t') = pointDist u w := by
      rw [← ht.2, ← ht'.2]
      exact (hiso t ht.1 t' ht'.1).symm
    have e3 : euclidNormVec (t - t') < s.side / 2 := by
      have h2 : t - t' = (t - c) - (t' - c) := by abel
      have h3 := euclidNormVec_sub_le (t - c) (t' - c)
      rw [← h2] at h3
      have h4 : euclidNormVec (t - c) ≤ ϱ := ht.1
      have h5 : euclidNormVec (t' - c) ≤ ϱ := ht'.1
      linarith
    exact ⟨e1, e2, e3, fun r hr hr2 => eq_of_proj_eq_of_short hF (hr.trans e1.symm) hr2 e3⟩
theorem liftsDifferByPeriod (hF : ProjectionProperties s) {z : s.Torus} {ϱ : ℝ} (h0 : 0 < ϱ)
    (h1 : ϱ < s.side / 4) {B B' : Set (Fin 4 → ℝ)} (hl : IsBallLift z ϱ B)
    (hl' : IsBallLift z ϱ B') : LiftsDifferByPeriod s z ϱ B B' := by
  obtain ⟨c, hc, rfl⟩ := (isBallLift_iff hB h0 h1 B).1 hl
  obtain ⟨c', hc', rfl⟩ := (isBallLift_iff hB h0 h1 B').1 hl'
  have hz : proj s (c' - c) = 0 := by rw [proj_sub, hc, hc', sub_self]
  obtain ⟨n, hn⟩ := (proj_eq_zero_iff hF _).1 hz
  set p : Fin 4 → ℝ := s.side • (fun μ => (n μ : ℝ)) with hp
  have hpn : p = periodVec s n := by
    funext μ
    simp [hp, periodVec, latticeTranslate, Conventions.StandingParameters.side]
  have hc'c : c' = c + p := by
    rw [hpn, ← hn]
    abel
  have hp0 : proj s p = 0 := (proj_eq_zero_iff hF _).2 ⟨n, hpn⟩
  refine ⟨n, ?_, ?_⟩
  · ext y
    constructor
    · intro hy
      refine ⟨y - p, ?_, sub_add_cancel y p⟩
      have : y - p - c = y - c' := by rw [hc'c]; abel
      show euclidNormVec (y - p - c) ≤ ϱ
      rw [this]
      exact hy
    · rintro ⟨x, hx, rfl⟩
      have : x + p - c' = x - c := by rw [hc'c]; abel
      show euclidNormVec (x + p - c') ≤ ϱ
      rw [this]
      exact hx
  · intro u hu t t' ht ht'
    obtain ⟨-, ⟨hbij, -⟩, -⟩ := hB s ϱ c' h0 h1.le
    have hmem : t + p ∈ closedBallR4 c' ϱ := by
      have : t + p - c' = t - c := by rw [hc'c]; abel
      show euclidNormVec (t + p - c') ≤ ϱ
      rw [this]
      exact ht.1
    exact hbij.injOn ht'.1 hmem (by rw [ht'.2, proj_add, hp0, add_zero, ht.2])
theorem smallBallLifts (hF : ProjectionProperties s) : SmallBallLifts s :=
  fun _ _ h0 h1 => ⟨isBallLift_iff hB h0 h1, fun _ hl => liftProperties hB hF h0 h1 hl,
    fun _ _ hl hl' => liftsDifferByPeriod hB hF h0 h1 hl hl'⟩
end Balls
section Closure
variable (hF : ProjectionProperties s)
  (hD : TorusMeasure.TranslatedLatticeCells.DistanceProperties s)
include hF hD
theorem pointNorm_zero : pointNorm (0 : s.Torus) = 0 := by
  have h := hD.2 0
  rw [proj_zero, euclidNormVec_zero] at h
  exact le_antisymm h (pointNorm_nonneg hF _)
theorem mem_closure_iff_pointDist_lt {A : Set s.Torus} {u : s.Torus} :
    u ∈ @closure _ (metricTopology s.L s.m) A ↔ ∀ r : ℝ, 0 < r → ∃ y ∈ A, pointDist y u < r := by
  rw [@mem_closure_iff _ (metricTopology s.L s.m)]
  constructor
  · intro h r hr
    have hopen : @IsOpen _ (metricTopology s.L s.m) {y : s.Torus | pointDist y u < r} := by
      intro y hy
      have hy' : pointDist y u < r := hy
      refine ⟨r - pointDist y u, sub_pos.2 hy', fun y' hy'' => ?_⟩
      have h1 : pointDist y' y < r - pointDist y u := hy''
      have h2 := (hD.1 y' u y).2
      show pointDist y' u < r
      linarith
    have hu : u ∈ {y : s.Torus | pointDist y u < r} := by
      show pointNorm (u - u) < r
      rw [sub_self, pointNorm_zero hF hD]
      exact hr
    obtain ⟨y, hy1, hy2⟩ := h _ hopen hu
    exact ⟨y, hy2, hy1⟩
  · intro h o ho hu
    obtain ⟨r, hr, hsub⟩ := ho u hu
    obtain ⟨y, hy, hyr⟩ := h r hr
    exact ⟨y, hsub hyr, hy⟩
end Closure
theorem continuous_of_isLipschitzFor {g : (Fin 4 → ℝ) → ℝ} (hg : IsLipschitzFor euclidDistR4 g) :
    Continuous g := by apply _root_.YangMills.Construction.TestPairs.continuous_of_isLipschitzFor_r4 <;> assumption
theorem functionLiftTo_concentric (hB : TorusMeasure.BallProjection.BallProjectionStatement)
    {ϱ ϱ' : ℝ} {c : Fin 4 → ℝ} {f : s.Torus → ℝ} (h0 : 0 < ϱ) (hle : ϱ ≤ ϱ')
    (hlt : ϱ' < s.side / 4) (hoff : ∀ u, u ∉ closedBallTorus (proj s c) ϱ → f u = 0) :
    functionLiftTo (closedBallR4 c ϱ') f = functionLiftTo (closedBallR4 c ϱ) f := by
  obtain ⟨-, ⟨-, hiso⟩, -⟩ := hB s ϱ' c (h0.trans_le hle) hlt.le
  funext x
  unfold functionLiftTo
  by_cases hx : x ∈ closedBallR4 c ϱ
  · have hx' : x ∈ closedBallR4 c ϱ' := le_trans hx hle
    rw [indicator_of_mem hx, indicator_of_mem hx']
  · rw [indicator_of_notMem hx]
    by_cases hx' : x ∈ closedBallR4 c ϱ'
    · rw [indicator_of_mem hx']
      refine hoff _ fun hin => hx ?_
      have hc : c ∈ closedBallR4 c ϱ' := by
        show euclidNormVec (c - c) ≤ ϱ'
        rw [sub_self, euclidNormVec_zero]
        exact (h0.trans_le hle).le
      have h1 := hiso x hx' c hc
      have h2 : pointDist (proj s x) (proj s c) ≤ ϱ := hin
      rw [h1] at h2
      exact h2
    · rw [indicator_of_notMem hx']
theorem functionLiftProperties (hB : TorusMeasure.BallProjection.BallProjectionStatement)
    (hF : ProjectionProperties s)
    (hD : TorusMeasure.TranslatedLatticeCells.DistanceProperties s) : FunctionLiftProperties s := by
  intro z ϱ B f hl hbd hsupp
  have hl' := hl
  obtain ⟨h0, h1, ⟨c, rfl⟩, him⟩ := hl'
  obtain rfl := proj_center_eq hB h0 h1 him
  have hoff : ∀ u, u ∉ closedBallTorus (proj s c) ϱ → f u = 0 := by
    intro u hu
    by_contra hne
    exact hu (hsupp (@subset_closure _ (metricTopology s.L s.m) {y | f y ≠ 0} u hne))
  obtain ⟨-, ⟨hbij, hiso⟩, ⟨-, hcorr⟩, hfun⟩ := hB s ϱ c h0 h1.le
  have hbelow := (hcorr f hoff).2
  obtain ⟨-, -, hLp, ⟨hcl, -, -⟩, hI⟩ := hfun _ f hbelow
  set F := functionLiftTo (closedBallR4 c ϱ) f with hFdef
  have hFeq : F = (closedBallR4 c ϱ).indicator (f ∘ proj s) := rfl
  have hFmem : ∀ t ∈ closedBallR4 c ϱ, F t = f (proj s t) := fun t ht => by
    rw [hFeq, indicator_of_mem ht]
    rfl
  have hFoff : ∀ t, t ∉ closedBallR4 c ϱ → F t = 0 := fun t ht => by
    rw [hFeq, indicator_of_notMem ht]
  have hFne : ∀ t, F t ≠ 0 → t ∈ closedBallR4 c ϱ := fun t ht => by
    by_contra hn
    exact ht (hFoff t hn)
  obtain ⟨C, hC⟩ := hbd
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hFbd : IsBoundedFun F := by
    refine ⟨C, fun t => ?_⟩
    by_cases ht : t ∈ closedBallR4 c ϱ
    · rw [hFmem t ht]
      exact hC _
    · rw [hFoff t ht, norm_zero]
      exact hC0
  have hfb : BddAbove (range fun u => ‖f u‖) := ⟨C, by rintro _ ⟨u, rfl⟩; exact hC u⟩
  have hFb : BddAbove (range fun t => ‖F t‖) := by
    obtain ⟨C', hC'⟩ := hFbd
    exact ⟨C', by rintro _ ⟨t, rfl⟩; exact hC' t⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hs0 : 0 ≤ uniformNorm f := Real.iSup_nonneg fun _ => norm_nonneg _
    have hs1 : 0 ≤ uniformNorm F := Real.iSup_nonneg fun _ => norm_nonneg _
    refine le_antisymm (ciSup_le fun t => ?_) (ciSup_le fun u => ?_)
    · by_cases ht : t ∈ closedBallR4 c ϱ
      · rw [hFmem t ht]
        exact le_ciSup hfb (proj s t)
      · rw [hFoff t ht, norm_zero]
        exact hs0
    · by_cases hu : u ∈ closedBallTorus (proj s c) ϱ
      · obtain ⟨t, ht, rfl⟩ := hbij.surjOn hu
        rw [← hFmem t ht]
        exact le_ciSup hFb t
      · rw [hoff u hu, norm_zero]
        exact hs1
  · ext t
    constructor
    · intro ht
      have htB : t ∈ closedBallR4 c ϱ := hcl ht
      refine ⟨proj s t, ?_, htB, rfl⟩
      refine (mem_closure_iff_pointDist_lt hF hD).2 fun r hr => ?_
      have hopen : IsOpen {x : Fin 4 → ℝ | euclidNormVec (x - t) < r} :=
        isOpen_lt (continuous_euclidNormVec.comp (continuous_id.sub continuous_const))
          continuous_const
      have hmem : t ∈ {x : Fin 4 → ℝ | euclidNormVec (x - t) < r} := by
        show euclidNormVec (t - t) < r
        rw [sub_self, euclidNormVec_zero]
        exact hr
      obtain ⟨t', ht'r, ht'⟩ := mem_closure_iff.1 ht _ hopen hmem
      have ht'B := hFne t' ht'
      refine ⟨proj s t', ?_, ?_⟩
      · have : F t' ≠ 0 := ht'
        rwa [hFmem t' ht'B] at this
      · have h2 := hD.2 (t' - t)
        rw [proj_sub] at h2
        exact h2.trans_lt ht'r
    · rintro ⟨u, hu, htB, rfl⟩
      have hnear := (mem_closure_iff_pointDist_lt hF hD).1 hu
      refine mem_closure_iff.2 fun o ho hto => ?_
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 ho t hto
      obtain ⟨y, hy, hyr⟩ := hnear ε hε
      have hne : f y ≠ 0 := hy
      have hyb : y ∈ closedBallTorus (proj s c) ϱ := by
        by_contra hn
        exact hne (hoff y hn)
      obtain ⟨t', ht'B, rfl⟩ := hbij.surjOn hyb
      have hdist : euclidNormVec (t' - t) < ε := by
        have := hiso t' ht'B t htB
        rw [this] at hyr
        exact hyr
      refine ⟨t', hball ?_, ?_⟩
      · rw [Metric.mem_ball, dist_pi_lt_iff hε]
        intro μ
        rw [Real.dist_eq]
        exact (abs_apply_le_euclidNormVec (t' - t) μ).trans_lt hdist
      · show F t' ≠ 0
        rwa [hFmem t' ht'B]
  · intro c' ϱ' hBc hle hlt
    have hc' : proj s c' = proj s c := by
      refine proj_center_eq hB h0 h1 ?_
      rw [← hBc]
      exact him
    have hcon := functionLiftTo_concentric hB (c := c') h0 hle hlt (by rw [hc']; exact hoff)
    rw [hcon, ← hBc]
  · intro hf
    have hFL : IsLipschitzFor euclidDistR4 F := hLp.1.1 hf
    have hmeas : IsNullMeasurableFunR4 F :=
      (continuous_of_isLipschitzFor hFL).measurable.nullMeasurable
    exact ⟨hFL, (hLp.2 hFL).symm.le, ((hI hFbd hmeas).2.2).symm⟩
def closedCenteredBox (a : ℝ) : Set (Fin 4 → ℝ) := Set.pi univ fun _ => Icc (-(a / 2)) (a / 2)
def halfOpenCenteredBox (a : ℝ) : Set (Fin 4 → ℝ) := Set.pi univ fun _ => Ico (-(a / 2)) (a / 2)
theorem measurableSet_closedCenteredBox (a : ℝ) : MeasurableSet (closedCenteredBox a) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc
theorem measurableSet_halfOpenCenteredBox (a : ℝ) : MeasurableSet (halfOpenCenteredBox a) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico
theorem halfOpenCenteredBox_subset (a : ℝ) : halfOpenCenteredBox a ⊆ closedCenteredBox a :=
  fun _ h μ hμ => Ico_subset_Icc_self (h μ hμ)
theorem volume_closedCenteredBox {a : ℝ} (ha : 0 < a) :
    volume (closedCenteredBox a) = ENNReal.ofReal (a ^ 4) := by
  rw [closedCenteredBox, volume_pi_pi]
  simp only [Real.volume_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (by linarith)]
  congr 2
  ring
theorem volume_halfOpenCenteredBox {a : ℝ} (ha : 0 < a) :
    volume (halfOpenCenteredBox a) = ENNReal.ofReal (a ^ 4) := by
  rw [halfOpenCenteredBox, volume_pi_pi]
  simp only [Real.volume_Ico, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (by linarith)]
  congr 2
  ring
theorem volume_closedCenteredBox_diff {a : ℝ} (ha : 0 < a) :
    volume (closedCenteredBox a \ halfOpenCenteredBox a) = 0 := by
  rw [measure_sdiff (halfOpenCenteredBox_subset a)
    (measurableSet_halfOpenCenteredBox a).nullMeasurableSet
    (by rw [volume_halfOpenCenteredBox ha]; exact ENNReal.ofReal_ne_top),
    volume_closedCenteredBox ha, volume_halfOpenCenteredBox ha, tsub_self]
theorem volume_image_add_left (w : Fin 4 → ℝ) (S : Set (Fin 4 → ℝ)) :
    volume ((fun τ => w + τ) '' S) = volume S := by
  rw [Set.image_add_left]
  exact measure_preimage_add _ _ _
theorem measurableSet_image_add_left (w : Fin 4 → ℝ) {S : Set (Fin 4 → ℝ)}
    (hS : MeasurableSet S) : MeasurableSet ((fun τ => w + τ) '' S) := by
  rw [Set.image_add_left]
  exact (measurable_const_add _) hS
theorem euclidNormVec_le_of_mem_closedCenteredBox {a : ℝ} (ha : 0 < a) {τ : Fin 4 → ℝ}
    (hτ : τ ∈ closedCenteredBox a) : euclidNormVec τ ≤ a := by
  have h : ∑ μ, τ μ ^ 2 ≤ a ^ 2 := by
    have h1 : ∀ μ, τ μ ^ 2 ≤ (a / 2) ^ 2 := fun μ => by
      have := hτ μ (mem_univ μ)
      exact sq_le_sq' this.1 this.2
    calc ∑ μ, τ μ ^ 2 ≤ ∑ _μ : Fin 4, (a / 2) ^ 2 := Finset.sum_le_sum fun μ _ => h1 μ
      _ = a ^ 2 := by simp; ring
  exact Real.sqrt_le_iff.2 ⟨ha.le, h⟩
theorem exists_torusProj_eq_supNormVec_eq {S : ℝ} (x : Torus4 S) :
    ∃ v, torusProj S v = x ∧ TorusMetric.supNormVec v = _root_.YangMills.Construction.TorusMetric.torusSupNorm x := by
  choose b hb hb' using fun μ => exists_coe_eq_abs_eq_norm (x μ)
  have hcov : torusProj S b = x := funext hb
  refine ⟨b, hcov, le_antisymm ?_ ?_⟩
  · refine le_csInf ⟨_, b, hcov, rfl⟩ ?_
    rintro _ ⟨v, hv, rfl⟩
    have hv' : torusProj S v = x := hv
    refine Finset.sup'_le _ _ fun μ _ => ?_
    rw [hb' μ, ← hv']
    exact (addCircle_norm_coe_le_abs _).trans
      (Finset.le_sup' (fun μ => |v μ|) (Finset.mem_univ μ))
  · refine csInf_le ⟨0, ?_⟩ ⟨b, hcov, rfl⟩
    rintro _ ⟨v, -, rfl⟩
    exact (abs_nonneg _).trans (Finset.le_sup' (fun μ => |v μ|) (Finset.mem_univ (0 : Fin 4)))
theorem torusSupNorm_torusProj_le {S : ℝ} (τ : Fin 4 → ℝ) :
    _root_.YangMills.Construction.TorusMetric.torusSupNorm (torusProj S τ) ≤ TorusMetric.supNormVec τ := by apply _root_.YangMills.Construction.Weighted.ProjectionProof.torusSupNorm_proj_le <;> assumption
theorem mem_siteCube_iff (y : Site s.L s.m ((s.K : ℕ) : ℤ)) (x : s.Torus) :
    x ∈ siteCube y ↔ ∃ τ ∈ closedCenteredBox (PlaquetteSupports.latticeSpacing s),
      x = (y : s.Torus) + proj s τ := by
  constructor
  · intro hx
    have hx' : _root_.YangMills.Construction.TorusMetric.torusSupNorm (x - (y : s.Torus)) ≤ PlaquetteSupports.latticeSpacing s / 2 := hx
    obtain ⟨v, hv, hv2⟩ := exists_torusProj_eq_supNormVec_eq (x - (y : s.Torus))
    refine ⟨v, fun μ _ => ?_, ?_⟩
    · have h1 : |v μ| ≤ PlaquetteSupports.latticeSpacing s / 2 :=
        (Finset.le_sup' (fun μ => |v μ|) (Finset.mem_univ μ)).trans (hv2.le.trans hx')
      exact abs_le.1 h1
    · have hv' : proj s v = x - (y : s.Torus) := hv
      rw [hv']
      abel
  · rintro ⟨τ, hτ, rfl⟩
    show _root_.YangMills.Construction.TorusMetric.torusSupNorm ((y : s.Torus) + proj s τ - (y : s.Torus)) ≤
      PlaquetteSupports.latticeSpacing s / 2
    rw [add_sub_cancel_left]
    exact (torusSupNorm_torusProj_le τ).trans
      (Finset.sup'_le _ _ fun μ _ => abs_le.2 (hτ μ (mem_univ μ)))
theorem translatedSiteCube_eq_image (y : Site s.L s.m ((s.K : ℕ) : ℤ)) (v : s.Torus)
    {w : Fin 4 → ℝ} (hw : proj s w = (y : s.Torus) + v) :
    translatedSiteCube y v =
      proj s '' ((fun τ => w + τ) '' closedCenteredBox (PlaquetteSupports.latticeSpacing s)) := by
  ext x
  constructor
  · rintro ⟨x', hx', rfl⟩
    obtain ⟨τ, hτ, rfl⟩ := (mem_siteCube_iff y x').1 hx'
    exact ⟨w + τ, ⟨τ, hτ, rfl⟩, by rw [proj_add, hw]; exact add_right_comm _ _ _⟩
  · rintro ⟨_, ⟨τ, hτ, rfl⟩, rfl⟩
    exact ⟨(y : s.Torus) + proj s τ, (mem_siteCube_iff _ _).2 ⟨τ, hτ, rfl⟩,
      by rw [proj_add, hw]; exact add_right_comm _ _ _⟩
theorem torusCell_eq_image {z : s.Torus} {w : Fin 4 → ℝ} (hw : proj s w = z) (a : ℝ) :
    torusCell a z = proj s '' ((fun τ => w + τ) '' halfOpenCenteredBox a) := by
  ext x
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact ⟨w + τ, ⟨τ, hτ, rfl⟩, by rw [proj_add, hw]⟩
  · rintro ⟨_, ⟨τ, hτ, rfl⟩, rfl⟩
    exact ⟨τ, hτ, by rw [proj_add, hw]⟩
theorem zero_le_torusVolume (E : Set s.Torus) : 0 ≤ torusVolume E := by apply _root_.YangMills.Construction.TorusMeasure.TranslatedLatticeCells.torusVolume_nonneg_of_set <;> assumption
section Cubes
variable (hF : ProjectionProperties s) (hV : VolumeProperties s)
  (hU : TorusProjection.VolumeNonincreasing)
  (ha : 0 < PlaquetteSupports.latticeSpacing s)
  (hC : TorusMeasure.TranslatedLatticeCells.CellProperties s (PlaquetteSupports.latticeSpacing s))
  (hCover : ∀ v : s.Torus, ∀ x : s.Torus, ∃ y : Site s.L s.m ((s.K : ℕ) : ℤ),
    x ∈ cellAround ((y : s.Torus) + v))
  (hDisj : ∀ (v : s.Torus) (y y' : Site s.L s.m ((s.K : ℕ) : ℤ)), y ≠ y' →
    Disjoint (cellAround ((y : s.Torus) + v)) (cellAround ((y' : s.Torus) + v)))
include hF hV hU ha hC hCover hDisj
theorem translatedCubesTileTorus : TranslatedCubesTileTorus s := by
  intro v
  have hsurj := proj_surjective hF
  have hsub : ∀ (y : Site s.L s.m ((s.K : ℕ) : ℤ)),
      cellAround ((y : s.Torus) + v) ⊆ translatedSiteCube y v := by
    intro y
    obtain ⟨w, hw⟩ := hsurj ((y : s.Torus) + v)
    rw [translatedSiteCube_eq_image y v hw]
    show torusCell _ _ ⊆ _
    rw [torusCell_eq_image hw]
    exact image_mono (image_mono (halfOpenCenteredBox_subset _))
  have hcube : ∀ y : Site s.L s.m ((s.K : ℕ) : ℤ),
      IsMeasurableTorusSet (translatedSiteCube y v) ∧
      torusVolume (translatedSiteCube y v) = PlaquetteSupports.latticeSpacing s ^ 4 := by
    intro y
    obtain ⟨w, hw⟩ := hsurj ((y : s.Torus) + v)
    have hS : IsNullMeasurableR4
        ((fun τ => w + τ) '' closedCenteredBox (PlaquetteSupports.latticeSpacing s)) :=
      (measurableSet_image_add_left w (measurableSet_closedCenteredBox _)).nullMeasurableSet
    obtain ⟨hm, hle, -⟩ := hU s _ hS
    rw [← translatedSiteCube_eq_image y v hw] at hm hle
    refine ⟨hm, le_antisymm ?_ ?_⟩
    · have h1 : volumeR4
          ((fun τ => w + τ) '' closedCenteredBox (PlaquetteSupports.latticeSpacing s)) =
          ENNReal.ofReal (PlaquetteSupports.latticeSpacing s ^ 4) := by
        unfold volumeR4
        rw [volume_image_add_left, volume_closedCenteredBox ha]
      rw [h1] at hle
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hle
    · obtain ⟨-, hcm, hcv, -⟩ := hC ((y : s.Torus) + v)
      rw [← hcv]
      exact hV.1 _ _ hcm hm (hsub y)
  refine ⟨fun y => ⟨(hcube y).1, (hcube y).2, hsub y⟩, ?_, ?_⟩
  · refine eq_univ_of_forall fun x => ?_
    obtain ⟨y, hy⟩ := hCover v x
    exact mem_iUnion.2 ⟨y, hsub y hy⟩
  · intro y y' hne
    obtain ⟨w, hw⟩ := hsurj ((y : s.Torus) + v)
    obtain ⟨w', hw'⟩ := hsurj ((y' : s.Torus) + v)
    set N := closedCenteredBox (PlaquetteSupports.latticeSpacing s) \
      halfOpenCenteredBox (PlaquetteSupports.latticeSpacing s) with hN
    have hNm : MeasurableSet N :=
      (measurableSet_closedCenteredBox _).diff (measurableSet_halfOpenCenteredBox _)
    set M := (fun τ => w + τ) '' N ∪ (fun τ => w' + τ) '' N with hM
    have hMm : MeasurableSet M :=
      (measurableSet_image_add_left w hNm).union (measurableSet_image_add_left w' hNm)
    have hM0 : volume M = 0 := by
      refine measure_union_null ?_ ?_
      · rw [volume_image_add_left]
        exact volume_closedCenteredBox_diff ha
      · rw [volume_image_add_left]
        exact volume_closedCenteredBox_diff ha
    obtain ⟨hMi, hMle, -⟩ := hU s M hMm.nullMeasurableSet
    have hsubI : translatedSiteCube y v ∩ translatedSiteCube y' v ⊆ proj s '' M := by
      rintro x ⟨hx, hx'⟩
      have hx1 := hx
      have hx2 := hx'
      rw [translatedSiteCube_eq_image y v hw] at hx1
      rw [translatedSiteCube_eq_image y' v hw'] at hx2
      obtain ⟨_, ⟨τ, hτ, rfl⟩, hxe⟩ := hx1
      obtain ⟨_, ⟨τ', hτ', rfl⟩, hxe'⟩ := hx2
      by_cases h1 : τ ∈ halfOpenCenteredBox (PlaquetteSupports.latticeSpacing s)
      · by_cases h2 : τ' ∈ halfOpenCenteredBox (PlaquetteSupports.latticeSpacing s)
        · exfalso
          have hc : x ∈ cellAround ((y : s.Torus) + v) := by
            show x ∈ torusCell _ _
            rw [torusCell_eq_image hw]
            exact ⟨_, ⟨τ, h1, rfl⟩, hxe⟩
          have hc' : x ∈ cellAround ((y' : s.Torus) + v) := by
            show x ∈ torusCell _ _
            rw [torusCell_eq_image hw']
            exact ⟨_, ⟨τ', h2, rfl⟩, hxe'⟩
          exact Set.disjoint_left.1 (hDisj v y y' hne) hc hc'
        · exact ⟨_, Or.inr ⟨τ', ⟨hτ', h2⟩, rfl⟩, hxe'⟩
      · exact ⟨_, Or.inl ⟨τ, ⟨hτ, h1⟩, rfl⟩, hxe⟩
    have hIm : IsMeasurableTorusSet (translatedSiteCube y v ∩ translatedSiteCube y' v) :=
      NullMeasurableSet.inter (hcube y).1 (hcube y').1
    have hle := hV.1 _ _ hIm hMi hsubI
    have hz : torusVolume (proj s '' M) ≤ 0 := by
      have h1 : volumeR4 M = 0 := hM0
      rw [h1] at hMle
      exact ENNReal.ofReal_eq_zero.1 (le_antisymm hMle bot_le)
    exact le_antisymm (hle.trans hz) (zero_le_torusVolume _)
end Cubes
theorem translatedCubeSpecialCases (hF : ProjectionProperties s) :
    TranslatedCubeSpecialCases s := by
  obtain ⟨-, -, -, -, -, -, -, -, hadd, -⟩ := hF
  refine ⟨fun y => ?_, fun y P => ?_⟩
  · simp [translatedSiteCube]
  · unfold translatedSiteCube
    exact image_congr fun x _ => hadd x _
theorem cubePointsNearCenter
    (hD : TorusMeasure.TranslatedLatticeCells.DistanceProperties s)
    (ha : 0 < PlaquetteSupports.latticeSpacing s) :
    CubePointsNearCenter s := by
  refine ⟨fun y x hx => ?_, ?_⟩
  · obtain ⟨τ, hτ, rfl⟩ := (mem_siteCube_iff y x).1 hx
    show pointNorm ((y : s.Torus) + proj s τ - (y : s.Torus)) ≤
      PlaquetteSupports.latticeSpacing s
    rw [add_sub_cancel_left]
    exact (hD.2 τ).trans (euclidNormVec_le_of_mem_closedCenteredBox ha hτ)
  · rintro y _ ⟨τ, hτ, rfl⟩
    rw [add_sub_cancel_left]
    exact euclidNormVec_le_of_mem_closedCenteredBox ha hτ
theorem halfOpenCubesPartition (ha : 0 < PlaquetteSupports.latticeSpacing s) :
    HalfOpenCubesPartition s := by
  set a := PlaquetteSupports.latticeSpacing s with hadef
  refine ⟨?_, ?_, ?_⟩
  · rintro y ⟨k, hk⟩ y' ⟨k', hk'⟩ hne
    refine Set.disjoint_left.2 ?_
    rintro x ⟨τ, hτ, rfl⟩ ⟨τ', hτ', he⟩
    apply hne
    funext μ
    have h1 := hτ μ (mem_univ μ)
    have h2 := hτ' μ (mem_univ μ)
    have h3 : y' μ + τ' μ = y μ + τ μ := congrFun he μ
    rw [hk μ, hk' μ] at h3 ⊢
    have h4 : a * ((k' μ : ℝ) - k μ) < a * 1 := by nlinarith [h1.1, h1.2, h2.1, h2.2]
    have h5 : a * ((k μ : ℝ) - k' μ) < a * 1 := by nlinarith [h1.1, h1.2, h2.1, h2.2]
    have h6 : (k' μ : ℝ) - k μ < 1 := lt_of_mul_lt_mul_left h4 ha.le
    have h7 : (k μ : ℝ) - k' μ < 1 := lt_of_mul_lt_mul_left h5 ha.le
    have h8 : k' μ - k μ < 1 := by exact_mod_cast h6
    have h9 : k μ - k' μ < 1 := by exact_mod_cast h7
    have h10 : k μ = k' μ := by omega
    rw [h10]
  · refine eq_univ_of_forall fun t => ?_
    refine mem_iUnion₂.2 ⟨fun μ => a * (⌊t μ / a + 1 / 2⌋ : ℝ), ⟨fun μ => ⌊t μ / a + 1 / 2⌋,
      fun _ => rfl⟩, t - fun μ => a * (⌊t μ / a + 1 / 2⌋ : ℝ), fun μ _ => ?_, by simp⟩
    have h1 := Int.floor_le (t μ / a + 1 / 2)
    have h2 := Int.lt_floor_add_one (t μ / a + 1 / 2)
    have h3 : t μ = a * (t μ / a) := by field_simp
    have h4 : a * (⌊t μ / a + 1 / 2⌋ : ℝ) ≤ a * (t μ / a + 1 / 2) :=
      mul_le_mul_of_nonneg_left h1 ha.le
    have h5 : a * (t μ / a + 1 / 2) < a * ((⌊t μ / a + 1 / 2⌋ : ℝ) + 1) :=
      mul_lt_mul_of_pos_left h2 ha
    simp only [Pi.sub_apply]
    constructor <;> nlinarith
  · intro y _
    show volume ((fun τ => y + τ) '' halfOpenCenteredBox a) = _
    rw [volume_image_add_left, volume_halfOpenCenteredBox ha]
theorem offsetNormBounds : OffsetNormBounds := by
  have key : ∀ a b c d : Fin 4, a < b → c < d →
      (∑ μ : Fin 4, ((if μ = a then (1 : ℤ) else 0) + (if μ = b then 1 else 0) -
        (if μ = c then 1 else 0) - (if μ = d then 1 else 0)) ^ 2) ≤ 4 := by
    decide
  have main2 : ∀ a b : Fin 4, a < b →
      (∑ μ : Fin 4, ((if μ = a then (1 : ℤ) else 0) + (if μ = b then 1 else 0)) ^ 2) = 2 := by
    decide
  intro P Q
  have hP := main2 P.lower P.upper P.lower_lt_upper
  have hPQ := key P.lower P.upper Q.lower Q.upper P.lower_lt_upper Q.lower_lt_upper
  have hP' : (∑ μ : Fin 4, ((if μ = P.lower then (1 : ℝ) else 0) +
      (if μ = P.upper then 1 else 0)) ^ 2) = 2 := by exact_mod_cast hP
  have hPQ' : (∑ μ : Fin 4, ((if μ = P.lower then (1 : ℝ) else 0) +
      (if μ = P.upper then 1 else 0) - (if μ = Q.lower then 1 else 0) -
      (if μ = Q.upper then 1 else 0)) ^ 2) ≤ 4 := by exact_mod_cast hPQ
  constructor
  · have h1 : ∑ μ, planeCenterOffset P μ ^ 2 = 1 / 2 := by
      have : ∀ μ, planeCenterOffset P μ ^ 2 =
          (1 / 4 : ℝ) * ((if μ = P.lower then (1 : ℝ) else 0) +
          (if μ = P.upper then 1 else 0)) ^ 2 := fun μ => by
        simp only [planeCenterOffset, Pi.smul_apply, Pi.add_apply, Pi.single_apply, smul_eq_mul]
        ring
      simp only [this, ← Finset.mul_sum, hP']
      norm_num
    unfold euclidNormVec
    rw [h1, Real.sqrt_div zero_le_one, Real.sqrt_one]
  · have h1 : ∑ μ, (planeCenterOffset P - planeCenterOffset Q) μ ^ 2 ≤ 1 := by
      have : ∀ μ, (planeCenterOffset P - planeCenterOffset Q) μ ^ 2 =
          (1 / 4 : ℝ) * ((if μ = P.lower then (1 : ℝ) else 0) +
          (if μ = P.upper then 1 else 0) - (if μ = Q.lower then 1 else 0) -
          (if μ = Q.upper then 1 else 0)) ^ 2 := fun μ => by
        simp only [planeCenterOffset, Pi.sub_apply, Pi.smul_apply, Pi.add_apply,
          Pi.single_apply, smul_eq_mul]
        ring
      simp only [this, ← Finset.mul_sum]
      linarith
    exact Real.sqrt_le_one.2 h1 |> fun h => h
theorem cubesBallsAndLifts_holds
    (hMeasure : TorusCovering.CoveringIntegralVolumeStatement)
    (hCells : TorusMeasure.TranslatedLatticeCells.CellsAndBallsStatement)
    (hLattice : BareLattice.BareLatticeProperties)
    (hUnfold : TorusProjection.VolumeNonincreasing)
    (hBall : TorusMeasure.BallProjection.BallProjectionStatement) : CubesBallsAndLifts := by
  intro s
  obtain ⟨hF, -, hV, -⟩ := hMeasure s
  obtain ⟨hD, hW, hLip, hAll⟩ := hCells s
  obtain ⟨ha, ⟨hside, hpos⟩, ⟨-, hforms⟩, -⟩ := hLattice s
  have hn : PeriodicLattice.torusSide s.L s.m / PlaquetteSupports.latticeSpacing s =
      ((BareLattice.latticePointsPerSide s : ℤ) : ℝ) := by
    rw [Int.cast_natCast]
    exact hside
  obtain ⟨hC, ⟨-, -, -, hLC⟩, -, -⟩ := hAll (PlaquetteSupports.latticeSpacing s) _ ha hn
  have hlat : ∀ x : s.Torus,
      x ∈ TorusMeasure.TranslatedLatticeCells.cellLattice s (PlaquetteSupports.latticeSpacing s) ↔
      x ∈ BareLattice.baseLattice s := by
    intro x
    have h1 : x ∈ BareLattice.baseLattice s ↔ x ∈ BareLattice.projectedLattice s := by
      rw [← hforms]
      rfl
    rw [h1]
    constructor
    · rintro ⟨t, ⟨k, hk⟩, rfl⟩
      exact ⟨t, ⟨k, fun μ => by rw [hk μ, mul_comm]⟩, rfl⟩
    · rintro ⟨t, ⟨k, hk⟩, rfl⟩
      exact ⟨t, ⟨k, fun μ => by rw [hk μ, mul_comm]⟩, rfl⟩
  have hCover : ∀ v x : s.Torus, ∃ y : Site s.L s.m ((s.K : ℕ) : ℤ),
      x ∈ cellAround ((y : s.Torus) + v) := by
    intro v x
    have hx : x ∈ ⋃ y ∈ TorusMeasure.TranslatedLatticeCells.cellLattice s
        (PlaquetteSupports.latticeSpacing s),
        torusCell (PlaquetteSupports.latticeSpacing s) (y + v) := by
      rw [(hLC v).2]
      exact mem_univ x
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 hx
    exact ⟨⟨y, (hlat y).1 hy⟩, hxy⟩
  have hDisj : ∀ (v : s.Torus) (y y' : Site s.L s.m ((s.K : ℕ) : ℤ)), y ≠ y' →
      Disjoint (cellAround ((y : s.Torus) + v)) (cellAround ((y' : s.Torus) + v)) := by
    intro v y y' hne
    exact (hLC v).1 ((hlat _).2 y.2) ((hlat _).2 y'.2) fun h => hne (Subtype.ext h)
  refine ⟨translatedCubesTileTorus hF hV hUnfold ha hC hCover hDisj,
    translatedCubeSpecialCases hF, cubePointsNearCenter hD ha, halfOpenCubesPartition ha,
    offsetNormBounds, ?_, smallBallLifts hBall hF, fun f hf => (hLip f hf).1,
    functionLiftProperties hBall hF hD⟩
  · intro z t ϱ ht h0
    obtain ⟨hset, hl, -, hm, hv, -⟩ := hW z ϱ h0
    obtain ⟨-, -, -, hlift, -⟩ := hF
    rw [← hset]
    exact ⟨(hl t ((hlift z t).2 ht)).1, hm, hv⟩
end YangMills.Construction.TorusCubesAndBalls
end
