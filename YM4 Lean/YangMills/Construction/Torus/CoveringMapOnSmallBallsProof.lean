import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflectionsProof
import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import YangMills.Construction.ReflectionPositivity.TorusAsAMetricSpaceAndClassesOfTestFunctionsProof
import YangMills.Construction.Torus.CoveringMapOnSmallBalls
import YangMills.Construction.Torus.GeometryTransportLiftAndDilationOfTestPairsProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set YangMills.Construction.TorusMetric
open scoped ComplexOrder ENNReal
noncomputable section
namespace YangMills.Construction.TestFunctions.SmallBalls
theorem euclidNormVec_nonneg (v : Fin 4 → ℝ) : 0 ≤ euclidNormVec v := Real.sqrt_nonneg _
theorem euclidNormVec_add_le (a b : Fin 4 → ℝ) :
    euclidNormVec (a + b) ≤ euclidNormVec a + euclidNormVec b := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_add_le <;> assumption
theorem euclidNormVec_neg (v : Fin 4 → ℝ) : euclidNormVec (-v) = euclidNormVec v := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_neg <;> assumption
theorem euclidNormVec_sub_comm (a b : Fin 4 → ℝ) :
    euclidNormVec (a - b) = euclidNormVec (b - a) := by apply _root_.YangMills.Construction.AmbientPoints.euclidNormVec_sub_comm <;> assumption
theorem euclidNormVec_smul (t : ℝ) (v : Fin 4 → ℝ) :
    euclidNormVec (t • v) = |t| * euclidNormVec v := by apply _root_.YangMills.SharedProofs.p37834 <;> assumption
theorem euclidNormVec_zero : euclidNormVec (0 : Fin 4 → ℝ) = 0 := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_zero <;> assumption
theorem abs_apply_le_euclidNormVec (v : Fin 4 → ℝ) (i : Fin 4) : |v i| ≤ euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
theorem continuous_euclidNormVec : Continuous euclidNormVec := by apply _root_.YangMills.Construction.SeparatedTuples.continuous_euclidNormVec <;> assumption
theorem euclidNormVec_single_zero (t : ℝ) : euclidNormVec (Pi.single (0 : Fin 4) t) = |t| := by
  simp [euclidNormVec, Fin.sum_univ_four, Real.sqrt_sq_eq_abs]
theorem latticeTranslate_neg (ℓ : ℝ) (k : Fin 4 → ℤ) :
    latticeTranslate ℓ (-k) = -latticeTranslate ℓ k := by apply _root_.YangMills.Construction.ReflectionPositivity.CutoffMirrors.TorusMetricSpace.latticeTranslate_neg <;> assumption
theorem latticeTranslate_zero (ℓ : ℝ) : latticeTranslate ℓ (0 : Fin 4 → ℤ) = 0 := by apply _root_.YangMills.Construction.LimitSpaces.PeriodizeOnSmallSets.latticeTranslate_zero <;> assumption
theorem latticeTranslate_sub (ℓ : ℝ) (k k' : Fin 4 → ℤ) :
    latticeTranslate ℓ (k - k') = latticeTranslate ℓ k - latticeTranslate ℓ k' := by apply _root_.YangMills.Construction.LatticeCovering.latticeTranslate_sub <;> assumption
theorem le_euclidNormVec_latticeTranslate {ℓ : ℝ} (hℓ : 0 < ℓ) {k : Fin 4 → ℤ} (hk : k ≠ 0) :
    ℓ ≤ euclidNormVec (latticeTranslate ℓ k) := by apply _root_.YangMills.Construction.TestPairs.le_euclidNormVec_latticeTranslate <;> assumption
theorem isClosed_closedBallR4 (c : Fin 4 → ℝ) (r : ℝ) : IsClosed (closedBallR4 c r) := by apply _root_.YangMills.Construction.TestPairs.isClosed_closedBallR4 <;> assumption
theorem isCompact_closedBallR4 (c : Fin 4 → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    IsCompact (closedBallR4 c r) := by apply _root_.YangMills.Construction.TestPairs.isCompact_closedBallR4 <;> assumption
theorem euclidNormVec_sub_le_two_mul_of_mem {c x y : Fin 4 → ℝ} {r : ℝ}
    (hx : x ∈ closedBallR4 c r) (hy : y ∈ closedBallR4 c r) : euclidNormVec (x - y) ≤ 2 * r := by apply _root_.YangMills.Construction.TestPairs.euclidNormVec_sub_le_two_mul_of_mem <;> assumption
variable {ℓ : ℝ}
theorem proj_add (x y : Fin 4 → ℝ) : torusProj ℓ (x + y) = torusProj ℓ x + torusProj ℓ y := by apply _root_.YangMills.Construction.TestPairs.torusProj_map_add <;> assumption
theorem proj_sub (x y : Fin 4 → ℝ) : torusProj ℓ (x - y) = torusProj ℓ x - torusProj ℓ y := by apply _root_.YangMills.Construction.TestPairs.torusProj_map_sub <;> assumption
theorem continuous_proj : Continuous (torusProj ℓ) := by apply _root_.YangMills.Construction.TestPairs.continuous_torusProj <;> assumption
theorem proj_sub_latticeTranslate (x : Fin 4 → ℝ) (k : Fin 4 → ℤ) :
    torusProj ℓ (x - latticeTranslate ℓ k) = torusProj ℓ x := by apply _root_.YangMills.Construction.TestFunctions.PairTransport.torusProj_sub_latticeTranslate <;> assumption
theorem isLeast_torusEuclidNorm (u : Torus4 ℓ) :
    IsLeast (euclidNormVec '' (torusProj ℓ ⁻¹' {u})) (torusEuclidNorm u) := by
  choose b hb hb' using fun i => exists_coe_eq_abs_eq_norm (u i)
  have hproj : torusProj ℓ b = u := funext hb
  have hleast : IsLeast (euclidNormVec '' (torusProj ℓ ⁻¹' {u})) (euclidNormVec b) := by
    refine ⟨⟨b, hproj, rfl⟩, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    have hv' : torusProj ℓ v = u := hv
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
    have h1 : |b i| ≤ |v i| := by
      rw [hb' i, ← hv']
      exact addCircle_norm_coe_le_abs _
    exact sq_le_sq.mpr h1
  have h := hleast.csInf_eq
  rw [show torusEuclidNorm u = sInf (euclidNormVec '' (torusProj ℓ ⁻¹' {u})) from rfl, h]
  exact hleast
theorem exists_lift_norm_eq (u : Torus4 ℓ) :
    ∃ w, torusProj ℓ w = u ∧ euclidNormVec w = torusEuclidNorm u := by apply _root_.YangMills.Construction.AmbientPoints.exists_torusProj_eq_euclidNormVec_eq <;> assumption
theorem torusEuclidNorm_le_of_proj_eq {u : Torus4 ℓ} {w : Fin 4 → ℝ} (h : torusProj ℓ w = u) :
    torusEuclidNorm u ≤ euclidNormVec w :=
  (isLeast_torusEuclidNorm u).2 ⟨w, h, rfl⟩
theorem torusEuclidNorm_proj_le (w : Fin 4 → ℝ) :
    torusEuclidNorm (torusProj ℓ w) ≤ euclidNormVec w := by apply _root_.YangMills.Construction.SourcesAndGluing.torusEuclidNorm_torusProj_le <;> assumption
theorem zero_le_torusEuclidNorm (u : Torus4 ℓ) : 0 ≤ torusEuclidNorm u := by apply _root_.YangMills.Construction.TestPairs.torusEuclidNorm_nonneg <;> assumption
theorem euclidDistTorus_symm (u v : Torus4 ℓ) : euclidDistTorus u v = euclidDistTorus v u := by apply _root_.YangMills.Construction.TestPairs.euclidDistTorus_comm <;> assumption
theorem torusEuclidNorm_proj_of_le_half (hℓ : 0 < ℓ) {v : Fin 4 → ℝ}
    (hv : euclidNormVec v ≤ ℓ / 2) : torusEuclidNorm (torusProj ℓ v) = euclidNormVec v := by apply _root_.YangMills.Construction.TestPairs.torusEuclidNorm_torusProj_of_le_half <;> assumption
theorem projDistFormula (hℓ : 0 < ℓ) : ProjDistFormula ℓ := by
  intro x y
  have hd : euclidDistTorus (torusProj ℓ x) (torusProj ℓ y) =
      torusEuclidNorm (torusProj ℓ (x - y)) := by
    rw [proj_sub]
    rfl
  rw [hd]
  refine ⟨⟨?_, ?_⟩, torusEuclidNorm_proj_le _, torusEuclidNorm_proj_of_le_half hℓ⟩
  · obtain ⟨w, hw, hn⟩ := exists_lift_norm_eq (torusProj ℓ (x - y))
    obtain ⟨k, rfl⟩ := exists_latticeTranslate_of_torusProj_eq hw
    refine ⟨-k, ?_⟩
    show euclidNormVec (x - y - latticeTranslate ℓ (-k)) = _
    rw [latticeTranslate_neg, sub_neg_eq_add]
    exact hn
  · rintro _ ⟨k, rfl⟩
    exact torusEuclidNorm_le_of_proj_eq (proj_sub_latticeTranslate _ k)
theorem existsNearestLift : ExistsNearestLift ℓ := by
  intro u v x hx
  have hx' : torusProj ℓ x = u := hx
  obtain ⟨w, hw, hn⟩ := exists_lift_norm_eq (u - v)
  refine ⟨x - w, ?_, ?_⟩
  · show torusProj ℓ (x - w) = v
    rw [proj_sub, hx', hw]
    abel
  · rw [sub_sub_cancel, hn]
    rfl
theorem distTriangle : DistTriangle ℓ := by
  intro u v w
  obtain ⟨a, ha, hna⟩ := exists_lift_norm_eq (u - v)
  obtain ⟨b, hb, hnb⟩ := exists_lift_norm_eq (v - w)
  show torusEuclidNorm (u - w) ≤ torusEuclidNorm (u - v) + torusEuclidNorm (v - w)
  rw [← hna, ← hnb]
  refine le_trans (torusEuclidNorm_le_of_proj_eq ?_) (euclidNormVec_add_le a b)
  rw [proj_add, ha, hb]
  abel
section Ball
variable {c : Fin 4 → ℝ} {σ : ℝ}
theorem euclidDistTorus_proj_of_mem (hℓ : 0 < ℓ) (hσ : σ ≤ ℓ / 4) {x y : Fin 4 → ℝ}
    (hx : x ∈ closedBallR4 c σ) (hy : y ∈ closedBallR4 c σ) :
    euclidDistTorus (torusProj ℓ x) (torusProj ℓ y) = euclidNormVec (x - y) := by
  have h := euclidNormVec_sub_le_two_mul_of_mem hx hy
  exact ((projDistFormula hℓ x y).2.2) (by linarith)
theorem ballMapsOntoBall (hℓ : 0 < ℓ) (hσ : σ ≤ ℓ / 4) : BallMapsOntoBall ℓ c σ := by
  refine ⟨⟨?_, ?_, ?_⟩, fun x hx y hy => euclidDistTorus_proj_of_mem hℓ hσ hx hy⟩
  · intro x hx
    show torusEuclidNorm (torusProj ℓ x - torusProj ℓ c) ≤ σ
    rw [← proj_sub]
    exact (torusEuclidNorm_proj_le _).trans hx
  · intro x hx y hy h
    have h1 := euclidDistTorus_proj_of_mem hℓ hσ hx hy
    rw [h] at h1
    have h2 : euclidDistTorus (torusProj ℓ y) (torusProj ℓ y) = 0 := by
      have h3 := (projDistFormula hℓ y y).2.2
      rw [sub_self, euclidNormVec_zero] at h3
      exact h3 (by linarith)
    rw [h2] at h1
    have h4 : x - y = 0 := by
      funext i
      have := abs_apply_le_euclidNormVec (x - y) i
      rw [← h1] at this
      simpa using this
    exact sub_eq_zero.mp h4
  · intro u hu
    obtain ⟨w, hw, hn⟩ := exists_lift_norm_eq (u - torusProj ℓ c)
    refine ⟨c + w, ?_, ?_⟩
    · show euclidNormVec (c + w - c) ≤ σ
      rw [add_sub_cancel_left, hn]
      exact hu
    · rw [proj_add, hw]
      abel
theorem proj_image_closedBallR4 (hℓ : 0 < ℓ) (hσ : σ ≤ ℓ / 4) :
    torusProj ℓ '' closedBallR4 c σ = closedBallTorus (torusProj ℓ c) σ :=
  (ballMapsOntoBall hℓ hσ).1.image_eq
theorem proj_notMem_image_of_lt (hℓ : 0 < ℓ) (hσ : σ ≤ ℓ / 4) {y : Fin 4 → ℝ}
    (h1 : σ < euclidNormVec (y - c)) (h2 : euclidNormVec (y - c) ≤ ℓ / 2) :
    torusProj ℓ y ∉ torusProj ℓ '' closedBallR4 c σ := by
  rw [proj_image_closedBallR4 hℓ hσ]
  intro h
  have h3 : torusEuclidNorm (torusProj ℓ y - torusProj ℓ c) ≤ σ := h
  rw [← proj_sub, torusEuclidNorm_proj_of_le_half hℓ h2] at h3
  linarith
theorem exists_notMem_proj_image (hℓ : 0 < ℓ) (hσ : σ ≤ ℓ / 4) :
    ∃ y, y ∉ closedBallR4 c σ ∧ torusProj ℓ y ∉ torusProj ℓ '' closedBallR4 c σ := by
  have hv : euclidNormVec (c + Pi.single (0 : Fin 4) (ℓ / 2) - c) = ℓ / 2 := by
    rw [add_sub_cancel_left, euclidNormVec_single_zero, abs_of_pos (by linarith)]
  refine ⟨c + Pi.single (0 : Fin 4) (ℓ / 2), ?_, ?_⟩
  · intro h
    have h1 : euclidNormVec (c + Pi.single (0 : Fin 4) (ℓ / 2) - c) ≤ σ := h
    linarith
  · exact proj_notMem_image_of_lt hℓ hσ (by rw [hv]; linarith) hv.le
end Ball
section Periodize
variable {c : Fin 4 → ℝ} {σ : ℝ} {f : (Fin 4 → ℝ) → ℂ}
theorem add_latticeTranslate_notMem (hℓ : 0 < ℓ) (hσ : σ ≤ ℓ / 4) {x : Fin 4 → ℝ}
    (hx : x ∈ closedBallR4 c σ) {k : Fin 4 → ℤ} (hk : k ≠ 0) :
    x + latticeTranslate ℓ k ∉ closedBallR4 c σ := by
  intro h
  have h1 := euclidNormVec_sub_le_two_mul_of_mem h hx
  rw [add_sub_cancel_left] at h1
  have h2 := le_euclidNormVec_latticeTranslate hℓ hk
  linarith
theorem periodize_proj_of_mem (hℓ : 0 < ℓ) (hσ : σ ≤ ℓ / 4) (hf : f ∈ vanishOffBall c σ)
    {x : Fin 4 → ℝ} (hx : x ∈ closedBallR4 c σ) : periodize ℓ f (torusProj ℓ x) = f x := by
  rw [periodize_torusProj, periodicSum, tsum_eq_single 0, latticeTranslate_zero, add_zero]
  intro k hk
  exact hf _ (add_latticeTranslate_notMem hℓ hσ hx hk)
theorem periodize_of_notMem_image (hf : f ∈ vanishOffBall c σ) {u : Torus4 ℓ}
    (hu : u ∉ torusProj ℓ '' closedBallR4 c σ) : periodize ℓ f u = 0 := by
  obtain ⟨x, rfl⟩ := torusProj_surjective ℓ u
  rw [periodize_torusProj, periodicSum]
  have : ∀ k : Fin 4 → ℤ, f (x + latticeTranslate ℓ k) = 0 := by
    intro k
    refine hf _ fun h => hu ⟨_, h, torusProj_add_latticeTranslate ℓ x k⟩
  simp [this]
theorem liftToBall_mem_vanishOffBall (F : Torus4 ℓ → ℂ) :
    liftToBall ℓ c σ F ∈ vanishOffBall c σ :=
  fun _ hx => liftToBall_apply_of_notMem F hx
theorem periodize_liftToBall (hℓ : 0 < ℓ) (hσ : σ ≤ ℓ / 4) {F : Torus4 ℓ → ℂ}
    (hF : F ∈ vanishOffImage ℓ c σ) : periodize ℓ (liftToBall ℓ c σ F) = F := by
  funext u
  by_cases hu : u ∈ torusProj ℓ '' closedBallR4 c σ
  · obtain ⟨x, hx, rfl⟩ := hu
    rw [periodize_proj_of_mem hℓ hσ (liftToBall_mem_vanishOffBall F) hx,
      liftToBall_apply_of_mem F hx]
  · rw [periodize_of_notMem_image (liftToBall_mem_vanishOffBall F) hu, hF u hu]
theorem liftToBall_periodize (hℓ : 0 < ℓ) (hσ : σ ≤ ℓ / 4) (hf : f ∈ vanishOffBall c σ) :
    liftToBall ℓ c σ (periodize ℓ f) = f := by
  funext x
  by_cases hx : x ∈ closedBallR4 c σ
  · rw [liftToBall_apply_of_mem _ hx, periodize_proj_of_mem hℓ hσ hf hx]
  · rw [liftToBall_apply_of_notMem _ hx, hf x hx]
theorem periodizeOnBall (hℓ : 0 < ℓ) (hσ : σ ≤ ℓ / 4)
    (hf : f ∈ vanishOffBall c σ) : PeriodizeOnBall ℓ c σ f := by
  refine ⟨⟨?_, ?_⟩, fun x hx => periodize_proj_of_mem hℓ hσ hf hx,
    fun u hu => periodize_of_notMem_image hf hu⟩
  · intro x hx y hy
    have := euclidNormVec_sub_le_two_mul_of_mem hx hy
    linarith
  · intro x hx
    by_contra h
    exact hx (hf x h)
theorem periodizeBijective (hℓ : 0 < ℓ) (hσ : σ ≤ ℓ / 4) : PeriodizeBijective ℓ c σ := by
  refine ⟨⟨fun f hf u hu => periodize_of_notMem_image hf hu, ?_, ?_⟩, ?_, ?_⟩
  · intro f hf g hg h
    rw [← liftToBall_periodize hℓ hσ hf, h, liftToBall_periodize hℓ hσ hg]
  · intro F hF
    exact ⟨liftToBall ℓ c σ F, liftToBall_mem_vanishOffBall F, periodize_liftToBall hℓ hσ hF⟩
  · intro f hf
    exact liftToBall_periodize hℓ hσ hf
  · intro F hF
    exact periodize_liftToBall hℓ hσ hF
theorem range_periodize (hℓ : 0 < ℓ) (hσ : σ ≤ ℓ / 4) (hf : f ∈ vanishOffBall c σ) :
    range (periodize ℓ f) = range f := by
  obtain ⟨y, hy, hy'⟩ := exists_notMem_proj_image (c := c) hℓ hσ
  apply Subset.antisymm
  · rintro _ ⟨u, rfl⟩
    by_cases hu : u ∈ torusProj ℓ '' closedBallR4 c σ
    · obtain ⟨x, hx, rfl⟩ := hu
      exact ⟨x, (periodize_proj_of_mem hℓ hσ hf hx).symm⟩
    · exact ⟨y, by rw [hf y hy, periodize_of_notMem_image hf hu]⟩
  · rintro _ ⟨x, rfl⟩
    by_cases hx : x ∈ closedBallR4 c σ
    · exact ⟨_, periodize_proj_of_mem hℓ hσ hf hx⟩
    · exact ⟨_, by rw [hf x hx, periodize_of_notMem_image hf hy']⟩
theorem periodizeValues (hℓ : 0 < ℓ) (hσ : σ ≤ ℓ / 4) (hf : f ∈ vanishOffBall c σ) :
    PeriodizeValues ℓ f := by
  have hr := range_periodize hℓ hσ hf
  have hmem : ∀ x, ∃ u, periodize ℓ f u = f x := fun x => by
    have : f x ∈ range (periodize ℓ f) := hr ▸ mem_range_self x
    exact this
  have hmem' : ∀ u, ∃ x, f x = periodize ℓ f u := fun u => by
    have : periodize ℓ f u ∈ range f := hr ▸ mem_range_self u
    exact this
  refine ⟨hr, fun _ => ?_, ⟨fun h x => ?_, fun h u => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
  · unfold uniformNorm iSup
    have e1 : range (fun u => ‖periodize ℓ f u‖) = norm '' range (periodize ℓ f) :=
      (range_comp norm (periodize ℓ f))
    have e2 : range (fun x => ‖f x‖) = norm '' range f := (range_comp norm f)
    rw [e1, e2, hr]
  · obtain ⟨u, hu⟩ := hmem x
    rw [← hu]
    exact h u
  · obtain ⟨x, hx⟩ := hmem' u
    rw [← hx]
    exact h x
  · obtain ⟨u, hu⟩ := Function.ne_iff.mp h
    obtain ⟨x, hx⟩ := hmem' u
    exact Function.ne_iff.mpr ⟨x, by rw [hx]; exact hu⟩
  · obtain ⟨x, hx⟩ := Function.ne_iff.mp h
    obtain ⟨u, hu⟩ := hmem x
    exact Function.ne_iff.mpr ⟨u, by rw [hu]; exact hx⟩
theorem tsupport_subset_closedBallR4 (hf : f ∈ vanishOffBall c σ) :
    tsupport f ⊆ closedBallR4 c σ := by
  refine closure_minimal ?_ (isClosed_closedBallR4 c σ)
  intro x hx
  by_contra h
  exact hx (hf x h)
theorem support_periodize (hℓ : 0 < ℓ) (hσ : σ ≤ ℓ / 4) (hf : f ∈ vanishOffBall c σ) :
    Function.support (periodize ℓ f) = torusProj ℓ '' Function.support f := by
  ext u
  constructor
  · intro hu
    by_cases hi : u ∈ torusProj ℓ '' closedBallR4 c σ
    · obtain ⟨x, hx, rfl⟩ := hi
      refine ⟨x, ?_, rfl⟩
      have : periodize ℓ f (torusProj ℓ x) ≠ 0 := hu
      rwa [periodize_proj_of_mem hℓ hσ hf hx] at this
    · exact absurd (periodize_of_notMem_image hf hi) hu
  · rintro ⟨x, hx, rfl⟩
    have hb : x ∈ closedBallR4 c σ := by
      by_contra h
      exact hx (hf x h)
    show periodize ℓ f (torusProj ℓ x) ≠ 0
    rw [periodize_proj_of_mem hℓ hσ hf hb]
    exact hx
theorem tsupport_periodize (hℓ : 0 < ℓ) (hσ : σ ≤ ℓ / 4) (hσ0 : 0 < σ)
    (hf : f ∈ vanishOffBall c σ) :
    tsupport (periodize ℓ f) = torusProj ℓ '' tsupport f := by
  have hcpt : IsCompact (tsupport f) :=
    (isCompact_closedBallR4 c hσ0.le).of_isClosed_subset (isClosed_tsupport f)
      (tsupport_subset_closedBallR4 hf)
  apply Subset.antisymm
  · refine closure_minimal ?_ (hcpt.image continuous_proj).isClosed
    rw [support_periodize hℓ hσ hf]
    exact image_mono subset_closure
  · rw [tsupport, tsupport, support_periodize hℓ hσ hf]
    exact image_closure_subset_closure_image continuous_proj
theorem periodizeSupport (hℓ : 0 < ℓ) (hσ : σ ≤ ℓ / 4) (hσ0 : 0 < σ)
    (hf : f ∈ vanishOffBall c σ) {g : (Fin 4 → ℝ) → ℂ} (hg : g ∈ vanishOffBall c σ) :
    PeriodizeSupport ℓ c σ f g := by
  refine ⟨tsupport_subset_closedBallR4 hf, tsupport_periodize hℓ hσ hσ0 hf, ?_⟩
  rw [tsupport_periodize hℓ hσ hσ0 hf, tsupport_periodize hℓ hσ hσ0 hg]
  unfold setEuclidDist setDistR4
  rw [iInf_image]
  refine iInf_congr fun x => iInf_congr fun hx => ?_
  rw [iInf_image]
  refine iInf_congr fun y => iInf_congr fun hy => ?_
  have := euclidDistTorus_proj_of_mem hℓ hσ (tsupport_subset_closedBallR4 hf hx)
    (tsupport_subset_closedBallR4 hg hy)
  rw [← this]
  rfl
theorem periodize_lipschitz_bound_of_mem (hℓ : 0 < ℓ) (hσ : σ ≤ ℓ / 4)
    (hf : f ∈ vanishOffBall c σ) {C : ℝ} (hb : ∀ x y, ‖f x - f y‖ ≤ C * euclidDistR4 x y)
    {x : Fin 4 → ℝ} (hx : x ∈ closedBallR4 c σ) (v : Torus4 ℓ) :
    ‖periodize ℓ f (torusProj ℓ x) - periodize ℓ f v‖ ≤
      C * euclidDistTorus (torusProj ℓ x) v := by
  by_cases hv : v ∈ torusProj ℓ '' closedBallR4 c σ
  · obtain ⟨y, hy, rfl⟩ := hv
    rw [periodize_proj_of_mem hℓ hσ hf hx, periodize_proj_of_mem hℓ hσ hf hy,
      euclidDistTorus_proj_of_mem hℓ hσ hx hy]
    exact hb x y
  · obtain ⟨y, hy, hd⟩ := existsNearestLift (torusProj ℓ x) v x rfl
    have hy' : torusProj ℓ y = v := hy
    have hyb : y ∉ closedBallR4 c σ := fun h => hv ⟨y, h, hy'⟩
    rw [periodize_proj_of_mem hℓ hσ hf hx, periodize_of_notMem_image hf hv, ← hd, ← hf y hyb]
    exact hb x y
theorem periodize_lipschitz_bound (hℓ : 0 < ℓ) (hσ : σ ≤ ℓ / 4) (hf : f ∈ vanishOffBall c σ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x y, ‖f x - f y‖ ≤ C * euclidDistR4 x y)
    (u v : Torus4 ℓ) :
    ‖periodize ℓ f u - periodize ℓ f v‖ ≤ C * euclidDistTorus u v := by
  by_cases hu : u ∈ torusProj ℓ '' closedBallR4 c σ
  · obtain ⟨x, hx, rfl⟩ := hu
    exact periodize_lipschitz_bound_of_mem hℓ hσ hf hb hx v
  · by_cases hv : v ∈ torusProj ℓ '' closedBallR4 c σ
    · obtain ⟨y, hy, rfl⟩ := hv
      rw [norm_sub_rev, euclidDistTorus_symm]
      exact periodize_lipschitz_bound_of_mem hℓ hσ hf hb hy u
    · rw [periodize_of_notMem_image hf hu, periodize_of_notMem_image hf hv, sub_self, norm_zero]
      exact mul_nonneg hC (zero_le_torusEuclidNorm _)
theorem exists_intermediate_point (hσ : σ ≤ ℓ / 4) (hℓ : 0 < ℓ) {x y : Fin 4 → ℝ}
    (hx : x ∈ closedBallR4 c σ) (hy : y ∉ closedBallR4 c σ) :
    ∃ z, σ < euclidNormVec (z - c) ∧ euclidNormVec (z - c) ≤ ℓ / 2 ∧
      euclidNormVec (x - z) ≤ euclidNormVec (x - y) := by
  have hy1 : σ < euclidNormVec (y - c) := not_le.mp hy
  have hx1 : euclidNormVec (x - c) ≤ σ := hx
  by_cases hc : euclidNormVec (y - c) ≤ ℓ / 2
  · exact ⟨y, hy1, hc, le_rfl⟩
  · rw [not_le] at hc
    have hcont : ContinuousOn (fun t : ℝ => euclidNormVec (x + t • (y - x) - c)) (Icc 0 1) := by
      apply Continuous.continuousOn
      exact continuous_euclidNormVec.comp (by fun_prop)
    have hivt := intermediate_value_Icc (zero_le_one' ℝ) hcont
    have hmem : ℓ / 2 ∈ Icc (euclidNormVec (x + (0 : ℝ) • (y - x) - c))
        (euclidNormVec (x + (1 : ℝ) • (y - x) - c)) := by
      constructor
      · rw [zero_smul, add_zero]
        linarith
      · rw [one_smul, add_sub_cancel]
        exact hc.le
    obtain ⟨t, ⟨ht0, ht1⟩, ht⟩ := hivt hmem
    have ht' : euclidNormVec (x + t • (y - x) - c) = ℓ / 2 := ht
    refine ⟨x + t • (y - x), ?_, ht'.le, ?_⟩
    · rw [ht']
      linarith
    · have e : x - (x + t • (y - x)) = t • (x - y) := by
        funext i
        simp
        ring
      rw [e, euclidNormVec_smul, abs_of_nonneg ht0]
      have := euclidNormVec_nonneg (x - y)
      nlinarith
theorem lipschitz_bound_of_mem_of_notMem (hℓ : 0 < ℓ) (hσ : σ ≤ ℓ / 4)
    (hf : f ∈ vanishOffBall c σ) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ u v : Torus4 ℓ,
      ‖periodize ℓ f u - periodize ℓ f v‖ ≤ C * euclidDistTorus u v)
    {x y : Fin 4 → ℝ} (hx : x ∈ closedBallR4 c σ) (hy : y ∉ closedBallR4 c σ) :
    ‖f x - f y‖ ≤ C * euclidDistR4 x y := by
  obtain ⟨z, hz1, hz2, hz3⟩ := exists_intermediate_point hσ hℓ hx hy
  have hz := proj_notMem_image_of_lt hℓ hσ hz1 hz2
  have h1 := hb (torusProj ℓ x) (torusProj ℓ z)
  rw [periodize_proj_of_mem hℓ hσ hf hx, periodize_of_notMem_image hf hz, sub_zero] at h1
  rw [hf y hy, sub_zero]
  have h2 : euclidDistTorus (torusProj ℓ x) (torusProj ℓ z) ≤ euclidNormVec (x - z) := by
    show torusEuclidNorm (torusProj ℓ x - torusProj ℓ z) ≤ _
    rw [← proj_sub]
    exact torusEuclidNorm_proj_le _
  calc ‖f x‖ ≤ C * euclidDistTorus (torusProj ℓ x) (torusProj ℓ z) := h1
    _ ≤ C * euclidNormVec (x - y) := mul_le_mul_of_nonneg_left (h2.trans hz3) hC
theorem lipschitz_bound_of_periodize (hℓ : 0 < ℓ) (hσ : σ ≤ ℓ / 4)
    (hf : f ∈ vanishOffBall c σ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u v : Torus4 ℓ,
      ‖periodize ℓ f u - periodize ℓ f v‖ ≤ C * euclidDistTorus u v) (x y : Fin 4 → ℝ) :
    ‖f x - f y‖ ≤ C * euclidDistR4 x y := by
  by_cases hx : x ∈ closedBallR4 c σ
  · by_cases hy : y ∈ closedBallR4 c σ
    · have h1 := hb (torusProj ℓ x) (torusProj ℓ y)
      rwa [periodize_proj_of_mem hℓ hσ hf hx, periodize_proj_of_mem hℓ hσ hf hy,
        euclidDistTorus_proj_of_mem hℓ hσ hx hy] at h1
    · exact lipschitz_bound_of_mem_of_notMem hℓ hσ hf hC hb hx hy
  · by_cases hy : y ∈ closedBallR4 c σ
    · have h1 := lipschitz_bound_of_mem_of_notMem hℓ hσ hf hC hb hy hx
      rwa [norm_sub_rev, show euclidDistR4 y x = euclidDistR4 x y from
        euclidNormVec_sub_comm y x] at h1
    · rw [hf x hx, hf y hy, sub_self, norm_zero]
      exact mul_nonneg hC (euclidNormVec_nonneg _)
theorem periodizeLipschitz (hℓ : 0 < ℓ) (hσ : σ ≤ ℓ / 4) (hf : f ∈ vanishOffBall c σ) :
    PeriodizeLipschitz ℓ f := by
  refine ⟨⟨?_, ?_⟩, fun _ => ?_⟩
  · rintro ⟨C, hC, hb⟩
    exact ⟨C, hC, periodize_lipschitz_bound hℓ hσ hf hC hb⟩
  · rintro ⟨C, hC, hb⟩
    exact ⟨C, hC, lipschitz_bound_of_periodize hℓ hσ hf hC hb⟩
  · unfold lipConstTorus lipConstR4 bestLipschitzConstant
    congr 1
    ext C
    constructor
    · rintro ⟨hC, hb⟩
      exact ⟨hC, lipschitz_bound_of_periodize hℓ hσ hf hC hb⟩
    · rintro ⟨hC, hb⟩
      exact ⟨hC, periodize_lipschitz_bound hℓ hσ hf hC hb⟩
end Periodize
section Integral
variable {c : Fin 4 → ℝ} {σ : ℝ} {f : (Fin 4 → ℝ) → ℂ}
def fundamentalCube (ℓ : ℝ) : Set (Fin 4 → ℝ) := Set.pi univ fun _ : Fin 4 => Ico (0 : ℝ) ℓ
def translatedCube (ℓ : ℝ) (k : Fin 4 → ℤ) : Set (Fin 4 → ℝ) :=
  {x | x - latticeTranslate ℓ k ∈ fundamentalCube ℓ}
theorem measurableSet_fundamentalCube : MeasurableSet (fundamentalCube ℓ) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico
theorem measurableSet_translatedCube (k : Fin 4 → ℤ) : MeasurableSet (translatedCube ℓ k) :=
  (measurable_id.sub_const _) measurableSet_fundamentalCube
theorem iUnion_translatedCube (hℓ : 0 < ℓ) : ⋃ k, translatedCube ℓ k = univ := by
  refine eq_univ_of_forall fun x => mem_iUnion.mpr ?_
  choose k hk using fun i => (existsUnique_sub_zsmul_mem_Ico hℓ (x i) 0).exists
  refine ⟨k, fun i _ => ?_⟩
  have := hk i
  simpa [latticeTranslate, zsmul_eq_mul, mul_comm] using this
theorem pairwise_disjoint_translatedCube (hℓ : 0 < ℓ) :
    Pairwise (Function.onFun Disjoint (translatedCube ℓ)) := by
  intro k k' hne
  refine Set.disjoint_left.mpr fun x hx hx' => hne ?_
  funext i
  have h1 := hx i (mem_univ i)
  have h2 := hx' i (mem_univ i)
  refine (existsUnique_sub_zsmul_mem_Ico hℓ (x i) 0).unique ?_ ?_
  · simpa [latticeTranslate, zsmul_eq_mul, mul_comm] using h1
  · simpa [latticeTranslate, zsmul_eq_mul, mul_comm] using h2
theorem integrable_of_vanishOffBall (hσ0 : 0 < σ) (hf : f ∈ vanishOffBall c σ)
    (hb : IsBoundedFun f) (hm : Measurable f) : Integrable f := by
  obtain ⟨C, hC⟩ := hb
  have hon : IntegrableOn f (closedBallR4 c σ) :=
    IntegrableOn.of_bound (isCompact_closedBallR4 c hσ0.le).measure_lt_top
      hm.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  exact hon.integrable_of_forall_notMem_eq_zero fun x hx => hf x hx
theorem summable_translates (hℓ : 0 < ℓ) (hσ : σ ≤ ℓ / 4) (hf : f ∈ vanishOffBall c σ)
    (v : Fin 4 → ℝ) : Summable fun k : Fin 4 → ℤ => f (v + latticeTranslate ℓ k) := by
  by_cases h : ∃ k₀, v + latticeTranslate ℓ k₀ ∈ closedBallR4 c σ
  · obtain ⟨k₀, hk₀⟩ := h
    refine summable_of_ne_finset_zero (s := {k₀}) fun k hk => ?_
    refine hf _ fun hmem => ?_
    have hne : k - k₀ ≠ 0 := sub_ne_zero.mpr (by simpa using hk)
    refine add_latticeTranslate_notMem hℓ hσ hk₀ hne ?_
    have e : v + latticeTranslate ℓ k₀ + latticeTranslate ℓ (k - k₀) =
        v + latticeTranslate ℓ k := by
      rw [latticeTranslate_sub]
      abel
    rwa [e]
  · have : ∀ k : Fin 4 → ℤ, f (v + latticeTranslate ℓ k) = 0 :=
      fun k => hf _ fun hk => h ⟨k, hk⟩
    simp only [this]
    exact summable_zero
theorem measurable_periodicSum (hℓ : 0 < ℓ) (hσ : σ ≤ ℓ / 4) (hf : f ∈ vanishOffBall c σ)
    (hm : Measurable f) : Measurable (periodicSum ℓ f) := by
  refine measurable_of_tendsto_metrizable' (Filter.atTop : Filter (Finset (Fin 4 → ℤ)))
    (f := fun s v => ∑ k ∈ s, f (v + latticeTranslate ℓ k)) ?_ ?_
  · intro s
    exact Finset.measurable_sum _ fun k _ => hm.comp (measurable_id.add_const _)
  · rw [tendsto_pi_nhds]
    intro v
    exact (summable_translates hℓ hσ hf v).hasSum
theorem integral_periodize (hℓ : 0 < ℓ) (hσ0 : 0 < σ)
    (hf : f ∈ vanishOffBall c σ) (hb : IsBoundedFun f) (hm : Measurable f) :
    torusIntegralComplex ℓ (periodize ℓ f) = ∫ x, f x := by
  have hint := integrable_of_vanishOffBall hσ0 hf hb hm
  have hshift : ∀ (g : (Fin 4 → ℝ) → ℂ) (k : Fin 4 → ℤ),
      ∫ x in fundamentalCube ℓ, g (x + latticeTranslate ℓ k) =
        ∫ y in translatedCube ℓ k, g y := by
    intro g k
    have hpre : (fun x => x + latticeTranslate ℓ k) ⁻¹' translatedCube ℓ k =
        fundamentalCube ℓ := by
      ext x
      simp [translatedCube]
    rw [← hpre]
    exact (measurePreserving_add_right volume (latticeTranslate ℓ k)).setIntegral_preimage_emb
      (measurableEmbedding_addRight _) g _
  have hshiftR : ∀ (g : (Fin 4 → ℝ) → ℝ) (k : Fin 4 → ℤ),
      ∫ x in fundamentalCube ℓ, g (x + latticeTranslate ℓ k) =
        ∫ y in translatedCube ℓ k, g y := by
    intro g k
    have hpre : (fun x => x + latticeTranslate ℓ k) ⁻¹' translatedCube ℓ k =
        fundamentalCube ℓ := by
      ext x
      simp [translatedCube]
    rw [← hpre]
    exact (measurePreserving_add_right volume (latticeTranslate ℓ k)).setIntegral_preimage_emb
      (measurableEmbedding_addRight _) g _
  have hnorm : HasSum (fun k => ∫ y in translatedCube ℓ k, ‖f y‖) _ :=
    hasSum_integral_iUnion (fun k => measurableSet_translatedCube k)
      (pairwise_disjoint_translatedCube hℓ) hint.norm.integrableOn
  have hsum1 : HasSum (fun k => ∫ y in translatedCube ℓ k, f y)
      (∫ y in ⋃ k, translatedCube ℓ k, f y) :=
    hasSum_integral_iUnion (fun k => measurableSet_translatedCube k)
      (pairwise_disjoint_translatedCube hℓ) hint.integrableOn
  rw [iUnion_translatedCube hℓ, setIntegral_univ] at hsum1
  have hsum2 : HasSum (fun k : Fin 4 → ℤ => ∫ x in fundamentalCube ℓ, f (x + latticeTranslate ℓ k))
      (∫ x in fundamentalCube ℓ, ∑' k : Fin 4 → ℤ, f (x + latticeTranslate ℓ k)) := by
    refine hasSum_integral_of_summable_integral_norm
      (fun k => (hint.comp_add_right (latticeTranslate ℓ k)).integrableOn) ?_
    have : (fun k : Fin 4 → ℤ => ∫ x in fundamentalCube ℓ, ‖f (x + latticeTranslate ℓ k)‖) =
        fun k => ∫ y in translatedCube ℓ k, ‖f y‖ := by
      funext k
      exact hshiftR (fun y => ‖f y‖) k
    rw [this]
    exact hnorm.summable
  simp only [hshift f] at hsum2
  have e : torusIntegralComplex ℓ (periodize ℓ f) =
      ∫ x in fundamentalCube ℓ, ∑' k : Fin 4 → ℤ, f (x + latticeTranslate ℓ k) := by
    unfold torusIntegralComplex
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact periodize_torusProj ℓ f x
  rw [e]
  exact hsum2.unique hsum1
theorem periodizeIntegral (hℓ : 0 < ℓ) (hσ : σ ≤ ℓ / 4) (hσ0 : 0 < σ)
    (hf : f ∈ vanishOffBall c σ) : PeriodizeIntegral ℓ f := by
  intro hb hm
  refine ⟨?_, ?_, integral_periodize hℓ hσ0 hf hb hm⟩
  · obtain ⟨C, hC⟩ := hb
    refine ⟨C, fun v => ?_⟩
    have : periodize ℓ f (torusProj ℓ v) ∈ range f := by
      rw [← range_periodize hℓ hσ hf]
      exact mem_range_self _
    obtain ⟨x, hx⟩ := this
    show ‖periodize ℓ f (torusProj ℓ v)‖ ≤ C
    rw [← hx]
    exact hC x
  · have : periodize ℓ f ∘ torusProj ℓ = periodicSum ℓ f := funext (periodize_torusProj ℓ f)
    rw [this]
    exact measurable_periodicSum hℓ hσ hf hm
end Integral
section Kernel
variable {F H : Torus4 ℓ → ℂ}
theorem mem_vanishOffImage_of_tsupport {c : Fin 4 → ℝ} {σ : ℝ}
    (h : tsupport F ⊆ torusProj ℓ '' closedBallR4 c σ) : F ∈ vanishOffImage ℓ c σ :=
  fun _ hu => image_eq_zero_of_notMem_tsupport fun hs => hu (h hs)
theorem isBoundedFun_liftToBall {c : Fin 4 → ℝ} {σ : ℝ} (hF : IsBoundedMeasurableOnTorus F) :
    IsBoundedFun (liftToBall ℓ c σ F) := by
  obtain ⟨C, hC⟩ := hF.1
  refine ⟨C, fun x => ?_⟩
  by_cases hx : x ∈ closedBallR4 c σ
  · rw [liftToBall_apply_of_mem F hx]
    exact hC _
  · rw [liftToBall_apply_of_notMem F hx, norm_zero]
    exact (norm_nonneg _).trans (hC 0)
theorem measurable_liftToBall {c : Fin 4 → ℝ} {σ : ℝ} (hF : IsBoundedMeasurableOnTorus F) :
    Measurable (liftToBall ℓ c σ F) :=
  hF.2.indicator (isClosed_closedBallR4 c σ).measurableSet
theorem hasCompactSupport_liftToBall {c : Fin 4 → ℝ} {σ : ℝ} (hσ0 : 0 < σ)
    (F : Torus4 ℓ → ℂ) : HasCompactSupport (liftToBall ℓ c σ F) :=
  (isCompact_closedBallR4 c hσ0.le).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_subset_closedBallR4 (liftToBall_mem_vanishOffBall F))
theorem isKernelPairR4_liftToBall (hℓ : 0 < ℓ) {c : Fin 4 → ℝ} {σ : ℝ}
    (hF : IsBoundedMeasurableOnTorus F) (hH : IsBoundedMeasurableOnTorus H)
    (hd : 0 < setEuclidDist (tsupport F) (tsupport H)) (hball : BallCoversSupports F H c σ) :
    IsKernelPairR4 (liftToBall ℓ c σ F) (liftToBall ℓ c σ H) := by
  obtain ⟨hσ0, hσ, h1, h2⟩ := hball
  refine ⟨isBoundedFun_liftToBall hF, isBoundedFun_liftToBall hH, measurable_liftToBall hF,
    measurable_liftToBall hH, hasCompactSupport_liftToBall hσ0 F,
    hasCompactSupport_liftToBall hσ0 H, ?_⟩
  have h := (periodizeSupport (c := c) hℓ hσ hσ0 (liftToBall_mem_vanishOffBall F)
    (liftToBall_mem_vanishOffBall H)).2.2
  rw [periodize_liftToBall hℓ hσ (mem_vanishOffImage_of_tsupport h1),
    periodize_liftToBall hℓ hσ (mem_vanishOffImage_of_tsupport h2)] at h
  rwa [← h]
theorem exists_common_latticeTranslate (hℓ : 0 < ℓ) {A : Set (Torus4 ℓ)}
    (hA : ∀ u ∈ A, ∀ v ∈ A, euclidDistTorus u v ≤ ℓ / 4) {c₁ c₂ : Fin 4 → ℝ} {σ₁ σ₂ : ℝ}
    (hσ₁ : σ₁ ≤ ℓ / 4) (hσ₂ : σ₂ ≤ ℓ / 4)
    (h₁ : A ⊆ torusProj ℓ '' closedBallR4 c₁ σ₁) (h₂ : A ⊆ torusProj ℓ '' closedBallR4 c₂ σ₂) :
    ∃ k : Fin 4 → ℤ,
      (∀ x ∈ closedBallR4 c₁ σ₁, torusProj ℓ x ∈ A →
        x + latticeTranslate ℓ k ∈ closedBallR4 c₂ σ₂) ∧
      ∀ y ∈ closedBallR4 c₂ σ₂, torusProj ℓ y ∈ A →
        y - latticeTranslate ℓ k ∈ closedBallR4 c₁ σ₁ := by
  rcases A.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · exact ⟨0, fun _ _ h => absurd h (notMem_empty _), fun _ _ h => absurd h (notMem_empty _)⟩
  obtain ⟨x₀, hx₀, hxa⟩ := h₁ ha
  obtain ⟨y₀, hy₀, hya⟩ := h₂ ha
  obtain ⟨k, hk⟩ := exists_latticeTranslate_of_torusProj_eq (hya.trans hxa.symm)
  have key : ∀ x ∈ closedBallR4 c₁ σ₁, ∀ y ∈ closedBallR4 c₂ σ₂, torusProj ℓ x ∈ A →
      torusProj ℓ y = torusProj ℓ x → y = x + latticeTranslate ℓ k := by
    intro x hx y hy hxA hyx
    obtain ⟨k', hk'⟩ := exists_latticeTranslate_of_torusProj_eq hyx
    have d1 : euclidNormVec (x - x₀) ≤ ℓ / 4 := by
      rw [← euclidDistTorus_proj_of_mem hℓ hσ₁ hx hx₀, hxa]
      exact hA _ hxA _ ha
    have d2 : euclidNormVec (y - y₀) ≤ ℓ / 4 := by
      rw [← euclidDistTorus_proj_of_mem hℓ hσ₂ hy hy₀, hya, hyx]
      exact hA _ hxA _ ha
    by_cases hkk : k' - k = 0
    · rw [hk', sub_eq_zero.mp hkk]
    · exfalso
      have h3 := le_euclidNormVec_latticeTranslate hℓ hkk
      have e : latticeTranslate ℓ (k' - k) = (y - y₀) + -(x - x₀) := by
        rw [latticeTranslate_sub, hk', hk]
        abel
      rw [e] at h3
      have h4 := euclidNormVec_add_le (y - y₀) (-(x - x₀))
      rw [euclidNormVec_neg] at h4
      linarith
  refine ⟨k, fun x hx hxA => ?_, fun y hy hyA => ?_⟩
  · obtain ⟨y, hy, hyx⟩ := h₂ hxA
    rw [← key x hx y hy hxA hyx]
    exact hy
  · obtain ⟨x, hx, hxy⟩ := h₁ hyA
    have := key x hx y hy (by rw [hxy]; exact hyA) hxy.symm
    rw [this, add_sub_cancel_right]
    exact hx
theorem liftToBall_eq_translate {A : Set (Torus4 ℓ)} {c₁ c₂ : Fin 4 → ℝ} {σ₁ σ₂ : ℝ}
    {k : Fin 4 → ℤ}
    (h₁ : ∀ x ∈ closedBallR4 c₁ σ₁, torusProj ℓ x ∈ A →
      x + latticeTranslate ℓ k ∈ closedBallR4 c₂ σ₂)
    (h₂ : ∀ y ∈ closedBallR4 c₂ σ₂, torusProj ℓ y ∈ A →
      y - latticeTranslate ℓ k ∈ closedBallR4 c₁ σ₁)
    (hF : tsupport F ⊆ A) :
    liftToBall ℓ c₂ σ₂ F = fun x => liftToBall ℓ c₁ σ₁ F (x - latticeTranslate ℓ k) := by
  funext x
  by_cases h0 : F (torusProj ℓ x) = 0
  · have e1 : liftToBall ℓ c₂ σ₂ F x = 0 := by
      by_cases hx : x ∈ closedBallR4 c₂ σ₂
      · rw [liftToBall_apply_of_mem F hx, h0]
      · rw [liftToBall_apply_of_notMem F hx]
    have e2 : liftToBall ℓ c₁ σ₁ F (x - latticeTranslate ℓ k) = 0 := by
      by_cases hx : x - latticeTranslate ℓ k ∈ closedBallR4 c₁ σ₁
      · rw [liftToBall_apply_of_mem F hx, proj_sub_latticeTranslate, h0]
      · rw [liftToBall_apply_of_notMem F hx]
    rw [e1, e2]
  · have hA : torusProj ℓ x ∈ A := hF (subset_tsupport F h0)
    by_cases hx : x ∈ closedBallR4 c₂ σ₂
    · rw [liftToBall_apply_of_mem F hx, liftToBall_apply_of_mem F (h₂ x hx hA),
        proj_sub_latticeTranslate]
    · have hx' : x - latticeTranslate ℓ k ∉ closedBallR4 c₁ σ₁ := by
        intro h
        refine hx ?_
        have := h₁ _ h (by rw [proj_sub_latticeTranslate]; exact hA)
        rwa [sub_add_cancel] at this
      rw [liftToBall_apply_of_notMem F hx, liftToBall_apply_of_notMem F hx']
theorem inverseEighthKernel_translate (φ ψ : (Fin 4 → ℝ) → ℂ) (p : Fin 4 → ℝ) :
    inverseEighthKernel (fun x => φ (x - p)) (fun x => ψ (x - p)) = inverseEighthKernel φ ψ := by
  unfold inverseEighthKernel
  have : (volume : Measure ((Fin 4 → ℝ) × (Fin 4 → ℝ))).IsAddRightInvariant := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have h := integral_sub_right_eq_self (μ := (volume : Measure ((Fin 4 → ℝ) × (Fin 4 → ℝ))))
    (fun z : (Fin 4 → ℝ) × (Fin 4 → ℝ) =>
      φ z.1 * ψ z.2 * ((euclidNormVec (z.1 - z.2) ^ (-8 : ℤ) : ℝ) : ℂ)) (p, p)
  refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)) h
  simp only [Prod.fst_sub, Prod.snd_sub, sub_sub_sub_cancel_right]
  rfl
theorem liftsAgree (hℓ : 0 < ℓ) (hF : IsBoundedMeasurableOnTorus F)
    (hH : IsBoundedMeasurableOnTorus H) (hs : SupportsInSmallBall F H) {c₁ c₂ : Fin 4 → ℝ}
    {σ₁ σ₂ : ℝ} (hb₁ : BallCoversSupports F H c₁ σ₁) (hb₂ : BallCoversSupports F H c₂ σ₂) :
    LiftsAgree F H c₁ σ₁ c₂ σ₂ := by
  obtain ⟨hd, u, r, hr0, hr, hFu, hHu⟩ := hs
  have hA : ∀ a ∈ tsupport F ∪ tsupport H, ∀ b ∈ tsupport F ∪ tsupport H,
      euclidDistTorus a b ≤ ℓ / 4 := by
    have hin : ∀ a ∈ tsupport F ∪ tsupport H, euclidDistTorus a u ≤ r := by
      rintro a (ha | ha)
      · exact hFu ha
      · exact hHu ha
    intro a ha b hb
    have h1 := distTriangle a u b
    have h2 := hin a ha
    have h3 := hin b hb
    rw [euclidDistTorus_symm u b] at h1
    linarith
  obtain ⟨k, hk₁, hk₂⟩ := exists_common_latticeTranslate hℓ hA hb₁.2.1 hb₂.2.1
    (union_subset hb₁.2.2.1 hb₁.2.2.2) (union_subset hb₂.2.2.1 hb₂.2.2.2)
  have eF := liftToBall_eq_translate (F := F) hk₁ hk₂ subset_union_left
  have eH := liftToBall_eq_translate (F := H) hk₁ hk₂ subset_union_right
  refine ⟨isKernelPairR4_liftToBall hℓ hF hH hd hb₁, isKernelPairR4_liftToBall hℓ hF hH hd hb₂,
    ⟨k, eF, eH⟩, ?_⟩
  rw [eF, eH]
  exact inverseEighthKernel_translate _ _ _
theorem ballCoversSupports_of_isKernelBallTorus (hℓ : 0 < ℓ) {c : Fin 4 → ℝ} {r : ℝ}
    (h : IsKernelBallTorus F H c r) : BallCoversSupports F H c r := by
  obtain ⟨-, hr0, hr, h1, h2⟩ := h
  refine ⟨hr0, hr, ?_, ?_⟩
  · rwa [proj_image_closedBallR4 hℓ hr]
  · rwa [proj_image_closedBallR4 hℓ hr]
theorem kernelIndependentOfBall (hℓ : 0 < ℓ) : KernelIndependentOfBall ℓ := by
  intro F H hF hH hs
  refine ⟨fun c₁ σ₁ c₂ σ₂ h₁ h₂ => liftsAgree hℓ hF hH hs h₁ h₂, fun c r h => ?_⟩
  have hex : ∃ q : (Fin 4 → ℝ) × ℝ, IsKernelBallTorus F H q.1 q.2 := ⟨(c, r), h⟩
  rw [inverseEighthKernelTorus, dif_pos hex]
  exact (liftsAgree hℓ hF hH hs (ballCoversSupports_of_isKernelBallTorus hℓ h)
    (ballCoversSupports_of_isKernelBallTorus hℓ hex.choose_spec)).2.2.2
end Kernel
theorem coveringOnSmallBalls : CoveringOnSmallBalls := by
  intro ℓ hℓ
  refine ⟨projDistFormula hℓ, existsNearestLift, distTriangle, fun c σ hσ0 hσ => ?_,
    kernelIndependentOfBall hℓ⟩
  refine ⟨ballMapsOntoBall hℓ hσ, fun f hf => periodizeOnBall hℓ hσ hf,
    periodizeBijective hℓ hσ, fun f hf g hg => ?_⟩
  exact ⟨periodizeValues hℓ hσ hf, periodizeSupport hℓ hσ hσ0 hf hg,
    periodizeLipschitz hℓ hσ hf, periodizeIntegral hℓ hσ hσ0 hf⟩
end YangMills.Construction.TestFunctions.SmallBalls
