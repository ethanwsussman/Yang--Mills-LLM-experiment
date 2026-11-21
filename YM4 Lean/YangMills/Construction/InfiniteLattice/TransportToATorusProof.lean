import YangMills.Construction.SystemOfAdmissibleConstants.CentredMomentsInTheFineCaseProof
import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import YangMills.Construction.InfiniteLattice.CoveringOfTheTorusLatticeProof
import YangMills.Construction.InfiniteLattice.TransportToATorus
import YangMills.Construction.Torus.CollinearQuadruplesProof
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.PeriodicTransport
open YangMills.Construction.TorusMetric YangMills.Construction.PeriodicLattice
open YangMills.Construction.TestFunctions YangMills.Construction.SeparatedFamilies
theorem euclidNormVec_nonneg (v : Fin 4 → ℝ) : 0 ≤ euclidNormVec v := Real.sqrt_nonneg _
theorem euclidNormVec_zero : euclidNormVec (0 : Fin 4 → ℝ) = 0 := by simp [euclidNormVec]
theorem euclidNormVec_neg (v : Fin 4 → ℝ) : euclidNormVec (-v) = euclidNormVec v := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_neg <;> assumption
theorem euclidNormVec_sub_le (v w : Fin 4 → ℝ) :
    euclidNormVec (v - w) ≤ euclidNormVec v + euclidNormVec w := by apply _root_.YangMills.Construction.QuadrupleClasses.Collinear.euclidNormVec_sub_le <;> assumption
theorem continuous_euclidNormVec : Continuous (euclidNormVec : (Fin 4 → ℝ) → ℝ) := by apply _root_.YangMills.Construction.SeparatedTuples.continuous_euclidNormVec <;> assumption
theorem abs_apply_le_euclidNormVec (v : Fin 4 → ℝ) (μ : Fin 4) : |v μ| ≤ euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
theorem dist_le_euclidNormVec (p q : Fin 4 → ℝ) : dist p q ≤ euclidNormVec (p - q) := by
  refine (dist_pi_le_iff (euclidNormVec_nonneg _)).2 fun μ => ?_
  rw [Real.dist_eq]
  exact abs_apply_le_euclidNormVec (p - q) μ
theorem le_euclidNormVec_latticeTranslate {a : ℝ} {k : Fin 4 → ℤ} (hk : k ≠ 0) :
    a ≤ euclidNormVec (latticeTranslate a k) := by apply _root_.YangMills.Construction.LimitSpaces.PeriodizeOnSmallSets.le_euclidNormVec_latticeTranslate <;> assumption
theorem latticeTranslate_zero (a : ℝ) : latticeTranslate a 0 = 0 := by apply _root_.YangMills.Construction.LimitSpaces.PeriodizeOnSmallSets.latticeTranslate_zero <;> assumption
theorem latticeTranslate_sub (a : ℝ) (k k' : Fin 4 → ℤ) :
    latticeTranslate a (k - k') = latticeTranslate a k - latticeTranslate a k' := by apply _root_.YangMills.Construction.LatticeCovering.latticeTranslate_sub <;> assumption
theorem torusProj_sub (S : ℝ) (v w : Fin 4 → ℝ) :
    torusProj S (v - w) = torusProj S v - torusProj S w := by apply _root_.YangMills.Construction.TestPairs.torusProj_map_sub <;> assumption
theorem torusEuclidNorm_torusProj_le (S : ℝ) (v : Fin 4 → ℝ) :
    torusEuclidNorm (torusProj S v) ≤ euclidNormVec v := by apply _root_.YangMills.Construction.SourcesAndGluing.torusEuclidNorm_torusProj_le <;> assumption
theorem exists_minimal_lift {S : ℝ} (x : Torus4 S) :
    ∃ b, torusProj S b = x ∧ euclidNormVec b = torusEuclidNorm x := by apply _root_.YangMills.Construction.AmbientPoints.exists_torusProj_eq_euclidNormVec_eq <;> assumption
theorem torusEuclidNorm_nonneg {S : ℝ} (x : Torus4 S) : 0 ≤ torusEuclidNorm x := by apply _root_.YangMills.Construction.TestPairs.torusEuclidNorm_nonneg <;> assumption
theorem torusEuclidNorm_neg_le {S : ℝ} (x : Torus4 S) :
    torusEuclidNorm (-x) ≤ torusEuclidNorm x := by
  obtain ⟨b, hc, hb⟩ := exists_minimal_lift x
  have h : torusProj S (-b) = -x := by
    rw [← hc]
    funext μ
    simp [torusProj]
  rw [← h, ← hb, ← euclidNormVec_neg b]
  exact torusEuclidNorm_torusProj_le S (-b)
theorem euclidDistTorus_comm {S : ℝ} (u v : Torus4 S) :
    euclidDistTorus u v = euclidDistTorus v u := by apply _root_.YangMills.Construction.TestPairs.euclidDistTorus_comm <;> assumption
structure RadiusFits (a r : ℝ) : Prop where
  radius_pos : 0 < r
  side_ge : 4 * r + 4 ≤ a
section Ball
variable {a r : ℝ} {x y : Fin 4 → ℝ}
theorem mem_radialBall_iff (hr : 0 < r) : x ∈ radialBall r ↔ euclidNormVec x < r := by
  rw [radialBall, originBall_ofReal hr]
  rfl
theorem euclidNormVec_sub_lt_of_mem (h : RadiusFits a r) (hx : x ∈ radialBall r)
    (hy : y ∈ radialBall r) : euclidNormVec (x - y) < 2 * r := by
  have h1 := (mem_radialBall_iff h.radius_pos).1 hx
  have h2 := (mem_radialBall_iff h.radius_pos).1 hy
  have h3 := euclidNormVec_sub_le x y
  linarith
theorem RadiusFits.side_pos (h : RadiusFits a r) : 0 < a := by
  have := h.radius_pos
  have := h.side_ge
  linarith
theorem euclidDistTorus_torusProj_le (a : ℝ) (x y : Fin 4 → ℝ) :
    euclidDistTorus (torusProj a x) (torusProj a y) ≤ euclidDistR4 x y := by apply _root_.YangMills.DeltaSharedProofs.p50059 <;> assumption
theorem euclidDistTorus_torusProj_eq (h : RadiusFits a r) (hx : x ∈ radialBall r)
    (hy : y ∈ radialBall r) :
    euclidDistTorus (torusProj a x) (torusProj a y) = euclidDistR4 x y := by
  refine le_antisymm (euclidDistTorus_torusProj_le a x y) ?_
  obtain ⟨b, hc, hb⟩ := exists_minimal_lift (torusProj a x - torusProj a y)
  rw [euclidDistTorus, ← hb, euclidDistR4]
  rw [← torusProj_sub] at hc
  obtain ⟨k, hk⟩ := exists_latticeTranslate_of_torusProj_eq hc
  by_cases hk0 : k = 0
  · rw [hk, hk0, latticeTranslate_zero, add_zero]
  · have h1 := euclidNormVec_sub_lt_of_mem h hx hy
    have h2 := le_euclidNormVec_latticeTranslate (a := a) hk0
    have h3 := euclidNormVec_sub_le b (x - y)
    have h4 : b - (x - y) = latticeTranslate a k := by rw [hk]; abel
    rw [h4] at h3
    have := h.side_ge
    linarith
theorem torusProj_injOn (h : RadiusFits a r) : InjOn (torusProj a) (radialBall r) := by
  intro x hx y hy hxy
  obtain ⟨k, hk⟩ := exists_latticeTranslate_of_torusProj_eq hxy
  by_cases hk0 : k = 0
  · rw [hk, hk0, latticeTranslate_zero, add_zero]
  · exfalso
    have h1 := euclidNormVec_sub_lt_of_mem h hx hy
    have h2 := le_euclidNormVec_latticeTranslate (a := a) hk0
    have h4 : x - y = latticeTranslate a k := by rw [hk]; abel
    rw [h4] at h1
    have := h.side_ge
    have := h.radius_pos
    linarith
theorem hasDiameterLE_radialBall (h : RadiusFits a r) : HasDiameterLE (radialBall r) (a / 2) := by
  intro x hx y hy
  have h1 := euclidNormVec_sub_lt_of_mem h hx hy
  have := h.side_ge
  have := h.radius_pos
  linarith
end Ball
section Values
variable {a r : ℝ} {f : (Fin 4 → ℝ) → ℝ}
theorem apply_add_latticeTranslate_eq_zero (h : RadiusFits a r)
    (hf : Function.support f ⊆ radialBall r) {x : Fin 4 → ℝ} (hx : x ∈ radialBall r)
    {k : Fin 4 → ℤ} (hk : k ≠ 0) : f (x + latticeTranslate a k) = 0 := by
  by_contra hne
  have hmem : x + latticeTranslate a k ∈ radialBall r := hf hne
  have heq := torusProj_injOn h hmem hx (torusProj_add_latticeTranslate a x k)
  have h0 : latticeTranslate a k = 0 := by simpa using heq
  have h2 := le_euclidNormVec_latticeTranslate (a := a) hk
  rw [h0, euclidNormVec_zero] at h2
  exact absurd h.side_pos (not_lt.2 h2)
theorem periodicSum_of_mem (h : RadiusFits a r) (hf : Function.support f ⊆ radialBall r)
    {x : Fin 4 → ℝ} (hx : x ∈ radialBall r) : periodicSum a f x = f x := by
  rw [periodicSum, tsum_eq_single 0 fun k hk => apply_add_latticeTranslate_eq_zero h hf hx hk,
    latticeTranslate_zero, add_zero]
theorem agreesWithPeriodization (h : RadiusFits a r) (hf : Function.support f ⊆ radialBall r) :
    AgreesWithPeriodization (radialBall r) f (periodize a f) := by
  refine ⟨fun x hx => ?_, fun u hu => ?_⟩
  · rw [periodize_torusProj, periodicSum_of_mem h hf hx]
  · have hz : ∀ k, f (liftPoint u + latticeTranslate a k) = 0 := by
      intro k
      by_contra hne
      refine hu ⟨_, hf hne, ?_⟩
      rw [torusProj_add_latticeTranslate, torusProj_liftPoint]
    rw [periodize, periodicSum]
    simp only [hz, tsum_zero]
theorem exists_eq_of_periodize_ne_zero (h : RadiusFits a r)
    (hf : Function.support f ⊆ radialBall r) {u : Torus4 a} (hu : periodize a f u ≠ 0) :
    ∃ x ∈ radialBall r, torusProj a x = u ∧ periodize a f u = f x := by
  have hv := agreesWithPeriodization h hf
  by_cases hmem : u ∈ torusProj a '' radialBall r
  · obtain ⟨x, hx, rfl⟩ := hmem
    exact ⟨x, hx, rfl, hv.1 x hx⟩
  · exact absurd (hv.2 u hmem) hu
theorem support_linearCombination_subset {g : (Fin 4 → ℝ) → ℝ}
    (hf : Function.support f ⊆ radialBall r) (hg : Function.support g ⊆ radialBall r)
    (α α' : ℝ) : Function.support (α • f + α' • g) ⊆ radialBall r := by
  intro x hx
  by_contra hn
  have h1 : f x = 0 := by
    by_contra h
    exact hn (hf h)
  have h2 : g x = 0 := by
    by_contra h
    exact hn (hg h)
  exact hx (by simp [h1, h2])
theorem periodize_linearCombination (h : RadiusFits a r) {g : (Fin 4 → ℝ) → ℝ}
    (hf : Function.support f ⊆ radialBall r) (hg : Function.support g ⊆ radialBall r)
    (α α' : ℝ) :
    periodize a (α • f + α' • g) = α • periodize a f + α' • periodize a g := by
  have h1 := agreesWithPeriodization h hf
  have h2 := agreesWithPeriodization h hg
  have h3 := agreesWithPeriodization h (support_linearCombination_subset hf hg α α')
  funext u
  by_cases hmem : u ∈ torusProj a '' radialBall r
  · obtain ⟨x, hx, rfl⟩ := hmem
    simp [h1.1 x hx, h2.1 x hx, h3.1 x hx]
  · simp [h1.2 u hmem, h2.2 u hmem, h3.2 u hmem]
end Values
section Lipschitz
variable {a r : ℝ} {f : (Fin 4 → ℝ) → ℝ}
theorem lipschitz_bound_of_eq_zero (h : RadiusFits a r) (hf : Function.support f ⊆ radialBall r)
    {C : ℝ} (hC : ∀ x y, ‖f x - f y‖ ≤ C * euclidDistR4 x y) {x : Fin 4 → ℝ} {v : Torus4 a}
    (hx : x ∈ radialBall r) (hv : periodize a f v = 0) :
    ‖periodize a f (torusProj a x) - periodize a f v‖ ≤ C * euclidDistTorus (torusProj a x) v := by
  obtain ⟨b, hc, hb⟩ := exists_minimal_lift (torusProj a x - v)
  have hy : torusProj a (x - b) = v := by
    rw [torusProj_sub, hc]
    abel
  have hfy : f (x - b) = 0 := by
    by_contra hne
    have hmem : x - b ∈ radialBall r := hf hne
    have hval := (agreesWithPeriodization h hf).1 _ hmem
    rw [hy, hv] at hval
    exact hne hval.symm
  have hd : euclidDistR4 x (x - b) = euclidDistTorus (torusProj a x) v := by
    rw [euclidDistTorus, ← hb, euclidDistR4]
    congr 1
    abel
  rw [hv, (agreesWithPeriodization h hf).1 x hx, ← hd]
  simpa [hfy] using hC x (x - b)
theorem periodize_lipschitz_bound (h : RadiusFits a r) (hf : Function.support f ⊆ radialBall r)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x y, ‖f x - f y‖ ≤ C * euclidDistR4 x y) (u v : Torus4 a) :
    ‖periodize a f u - periodize a f v‖ ≤ C * euclidDistTorus u v := by
  by_cases hu : periodize a f u = 0
  · by_cases hv : periodize a f v = 0
    · rw [hu, hv, sub_zero, norm_zero]
      exact mul_nonneg hC0 (torusEuclidNorm_nonneg _)
    · obtain ⟨y, hy, rfl, -⟩ := exists_eq_of_periodize_ne_zero h hf hv
      have := lipschitz_bound_of_eq_zero h hf hC hy hu
      rwa [norm_sub_rev, euclidDistTorus_comm] at this
  · by_cases hv : periodize a f v = 0
    · obtain ⟨x, hx, rfl, -⟩ := exists_eq_of_periodize_ne_zero h hf hu
      exact lipschitz_bound_of_eq_zero h hf hC hx hv
    · obtain ⟨x, hx, rfl, hfx⟩ := exists_eq_of_periodize_ne_zero h hf hu
      obtain ⟨y, hy, rfl, hfy⟩ := exists_eq_of_periodize_ne_zero h hf hv
      rw [hfx, hfy, euclidDistTorus_torusProj_eq h hx hy]
      exact hC x y
theorem uniformNorm_periodize (h : RadiusFits a r) (hf : Function.support f ⊆ radialBall r)
    {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) : uniformNorm (periodize a f) = uniformNorm f := by
  have hv := agreesWithPeriodization h hf
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hbf : BddAbove (range fun x => ‖f x‖) := ⟨B, by rintro _ ⟨x, rfl⟩; exact hB x⟩
  have hbt : BddAbove (range fun u => ‖periodize a f u‖) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨u, rfl⟩
    by_cases hmem : u ∈ torusProj a '' radialBall r
    · obtain ⟨x, hx, rfl⟩ := hmem
      simpa [hv.1 x hx] using hB x
    · simpa [hv.2 u hmem] using hB0
  refine le_antisymm (ciSup_le fun u => ?_) (ciSup_le fun x => ?_)
  · by_cases hmem : u ∈ torusProj a '' radialBall r
    · obtain ⟨x, hx, rfl⟩ := hmem
      rw [hv.1 x hx]
      exact le_ciSup hbf x
    · rw [hv.2 u hmem, norm_zero]
      exact (norm_nonneg _).trans (le_ciSup hbf 0)
  · by_cases hx : x ∈ radialBall r
    · rw [← hv.1 x hx]
      exact le_ciSup hbt (torusProj a x)
    · have h0 : f x = 0 := by
        by_contra hne
        exact hx (hf hne)
      rw [h0, norm_zero]
      exact (norm_nonneg _).trans (le_ciSup hbt (torusProj a 0))
theorem lipConstTorus_periodize_le (h : RadiusFits a r) (hf : Function.support f ⊆ radialBall r)
    (hL : IsLipschitzFor euclidDistR4 f) : lipConstTorus (periodize a f) ≤ lipConstR4 f := by
  obtain ⟨C, hC0, hC⟩ := hL
  refine csInf_le_csInf ⟨0, ?_⟩ ⟨C, hC0, hC⟩ ?_
  · rintro D ⟨hD, -⟩
    exact hD
  · rintro D ⟨hD0, hD⟩
    exact ⟨hD0, periodize_lipschitz_bound h hf hD0 hD⟩
end Lipschitz
section Supports
variable {L m : ℕ} {ρ : ℝ} {f : (Fin 4 → ℝ) → ℝ}
theorem continuous_torusProj {a : ℝ} : Continuous (torusProj a) := by apply _root_.YangMills.Construction.TestPairs.continuous_torusProj <;> assumption
theorem torusSupport_periodize (h : RadiusFits (torusSide L m) ρ) (hc : HasCompactSupport f)
    (hf : tsupport f ⊆ radialBall ρ) :
    torusSupport (L := L) (m := m) (periodize (torusSide L m) f) =
      torusProj (torusSide L m) '' tsupport f := by
  have hs : Function.support f ⊆ radialBall ρ := (subset_tsupport f).trans hf
  have : Fact (0 < torusSide L m) := ⟨h.side_pos⟩
  refine Subset.antisymm (fun u hu => ?_) ?_
  · have hcl : IsClosed (torusProj (torusSide L m) ⁻¹' (torusProj (torusSide L m) '' tsupport f)) :=
      ((IsCompact.image hc continuous_torusProj).isClosed).preimage continuous_torusProj
    have ha : liftPoint u ∈
        closure (torusProj (torusSide L m) ⁻¹' (torusProj (torusSide L m) '' tsupport f)) := by
      refine Metric.mem_closure_iff.2 fun ε hε => ?_
      obtain ⟨y, hy, hd⟩ := hu ε hε
      obtain ⟨z, -, rfl, hz⟩ := exists_eq_of_periodize_ne_zero h hs hy
      obtain ⟨w, hw, hwn⟩ := exists_minimal_lift (u - torusProj (torusSide L m) z)
      refine ⟨liftPoint u - w, ?_, ?_⟩
      · have hcov : torusProj (torusSide L m) (liftPoint u - w) = torusProj (torusSide L m) z := by
          rw [torusProj_sub, torusProj_liftPoint, hw]
          abel
        refine ⟨z, subset_tsupport f ?_, hcov.symm⟩
        rw [Function.mem_support, ← hz]
        exact hy
      · have h1 := dist_le_euclidNormVec (liftPoint u) (liftPoint u - w)
        have h2 : liftPoint u - (liftPoint u - w) = w := by abel
        rw [h2, hwn] at h1
        exact h1.trans_lt hd
    have hmem := hcl.closure_subset_iff.2 subset_rfl ha
    rwa [mem_preimage, torusProj_liftPoint] at hmem
  · rintro _ ⟨x, hx, rfl⟩ ε hε
    have hopen : IsOpen {z : Fin 4 → ℝ | euclidNormVec (x - z) < ε} :=
      isOpen_lt (continuous_euclidNormVec.comp (continuous_const.sub continuous_id))
        continuous_const
    have hxW : x ∈ {z : Fin 4 → ℝ | euclidNormVec (x - z) < ε} := by
      simpa [euclidNormVec_zero] using hε
    obtain ⟨z, hzW, hz⟩ := mem_closure_iff.1 hx _ hopen hxW
    refine ⟨torusProj (torusSide L m) z, ?_, ?_⟩
    · rw [(agreesWithPeriodization h hs).1 z (hs hz)]
      exact hz
    · rw [← torusProj_sub]
      exact (torusEuclidNorm_torusProj_le _ _).trans_lt hzW
theorem periodizeSupports (h : RadiusFits (torusSide L m) ρ) {g : (Fin 4 → ℝ) → ℝ}
    (hf : SupportedInBall ρ f) (hg : SupportedInBall ρ g) :
    PeriodizeSupports L m ρ f g := by
  have hsf := torusSupport_periodize h hf.1 hf.2
  have hsg := torusSupport_periodize h hg.1 hg.2
  refine ⟨hsf, ?_, ?_, ?_⟩
  · rw [hsf]
    rintro _ ⟨x, hx, rfl⟩
    have h1 := (mem_radialBall_iff h.radius_pos).1 (hf.2 hx)
    have h2 : torusProj (torusSide L m) x - torusProj (torusSide L m) 0 =
        torusProj (torusSide L m) x := by
      have : torusProj (torusSide L m) (0 : Fin 4 → ℝ) = 0 := by
        funext μ
        simp [torusProj]
      rw [this, sub_zero]
    show torusEuclidNorm (torusProj (torusSide L m) x - torusProj (torusSide L m) 0) ≤ ρ
    rw [h2]
    exact (torusEuclidNorm_torusProj_le _ _).trans h1.le
  · rw [hsf, hsg, setEuclidDist, setDistR4, iInf_image]
    refine iInf_congr fun p => iInf_congr fun hp => ?_
    rw [iInf_image]
    refine iInf_congr fun q => iInf_congr fun hq => ?_
    have := euclidDistTorus_torusProj_eq h (hf.2 hp) (hg.2 hq)
    rw [euclidDistTorus, euclidDistR4] at this
    rw [this]
  · intro hdis
    rw [hsf, hsg]
    refine eq_empty_of_forall_notMem ?_
    rintro _ ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩
    have := torusProj_injOn h (hg.2 hy) (hf.2 hx) hxy
    have hmem : x ∈ tsupport f ∩ tsupport g := ⟨hx, this ▸ hy⟩
    rw [hdis] at hmem
    exact hmem
end Supports
theorem contDiff_periodize_comp {a r : ℝ} {f : (Fin 4 → ℝ) → ℝ} (h : RadiusFits a r)
    (hf : Function.support f ⊆ radialBall r) (hc : ContDiff ℝ 1 f) :
    ContDiff ℝ 1 (periodize a f ∘ torusProj a) := by
  have he : periodize a f ∘ torusProj a = periodicSum a f := funext (periodize_torusProj a f)
  rw [he]
  refine contDiff_iff_contDiffAt.2 fun x₀ => ?_
  have hopen : IsOpen {v : Fin 4 → ℝ | euclidNormVec (v - x₀) < 1} :=
    isOpen_lt (continuous_euclidNormVec.comp (continuous_id.sub continuous_const)) continuous_const
  have hnhds : {v : Fin 4 → ℝ | euclidNormVec (v - x₀) < 1} ∈ 𝓝 x₀ :=
    hopen.mem_nhds (by simp [euclidNormVec_zero])
  have huniq : ∀ v ∈ {v : Fin 4 → ℝ | euclidNormVec (v - x₀) < 1},
      ∀ v' ∈ {v : Fin 4 → ℝ | euclidNormVec (v - x₀) < 1}, ∀ k k' : Fin 4 → ℤ,
      f (v + latticeTranslate a k) ≠ 0 → f (v' + latticeTranslate a k') ≠ 0 → k = k' := by
    intro v hv v' hv' k k' hk hk'
    by_contra hne
    have h1 := euclidNormVec_sub_lt_of_mem h (hf hk) (hf hk')
    have h2 := le_euclidNormVec_latticeTranslate (a := a) (sub_ne_zero.2 hne)
    have h3 := euclidNormVec_sub_le
      ((v + latticeTranslate a k) - (v' + latticeTranslate a k')) (v - v')
    have h4 : (v + latticeTranslate a k) - (v' + latticeTranslate a k') - (v - v') =
        latticeTranslate a (k - k') := by
      rw [latticeTranslate_sub]
      abel
    have h5 := euclidNormVec_sub_le (v - x₀) (v' - x₀)
    have h6 : v - x₀ - (v' - x₀) = v - v' := by abel
    rw [h4] at h3
    rw [h6] at h5
    have hv1 : euclidNormVec (v - x₀) < 1 := hv
    have hv2 : euclidNormVec (v' - x₀) < 1 := hv'
    have := h.side_ge
    have := h.radius_pos
    linarith
  by_cases hex : ∃ v ∈ {v : Fin 4 → ℝ | euclidNormVec (v - x₀) < 1}, ∃ k : Fin 4 → ℤ,
      f (v + latticeTranslate a k) ≠ 0
  · obtain ⟨v₀, hv₀, k₀, hk₀⟩ := hex
    have heq : periodicSum a f =ᶠ[𝓝 x₀] fun v => f (v + latticeTranslate a k₀) := by
      filter_upwards [hnhds] with v hv
      refine tsum_eq_single k₀ fun k hk => ?_
      by_contra hne
      exact hk (huniq v hv v₀ hv₀ k k₀ hne hk₀)
    exact (hc.comp (contDiff_id.add contDiff_const)).contDiffAt.congr_of_eventuallyEq heq
  · have heq : periodicSum a f =ᶠ[𝓝 x₀] fun _ => (0 : ℝ) := by
      filter_upwards [hnhds] with v hv
      have hz : ∀ k, f (v + latticeTranslate a k) = 0 := by
        intro k
        by_contra hne
        exact hex ⟨v, hv, k, hne⟩
      rw [periodicSum]
      simp only [hz, tsum_zero]
    exact contDiffAt_const.congr_of_eventuallyEq heq
theorem radiusFits_of_le {L m : ℕ} {r : ℝ} (hr : 0 < r) (h : 2 * r + 2 ≤ (L : ℝ) ^ m) :
    RadiusFits (torusSide L m) r :=
  ⟨hr, by rw [torusSide]; linarith⟩
theorem mainClaim : MainClaim := by
  intro L m ρ f g hl hf hg
  have h := radiusFits_of_le hl.radius_pos hl.radius_le_side
  have hsf : Function.support f ⊆ radialBall ρ := (subset_tsupport f).trans hf.2
  have hsg : Function.support g ⊆ radialBall ρ := (subset_tsupport g).trans hg.2
  refine ⟨⟨euclidDistTorus_torusProj_le _, fun x hx y hy => euclidDistTorus_torusProj_eq h hx hy,
    torusProj_injOn h⟩, ⟨hasDiameterLE_radialBall h, ⟨hasDiameterLE_radialBall h, hsf⟩, ?_, ?_,
    agreesWithPeriodization h hsf⟩,
    ?_, fun α α' => periodize_linearCombination h hsf hsg α α', ?_, periodizeSupports h hf hg,
    fun hc => contDiff_periodize_comp h hsf hc⟩
  · exact fun x => periodize_torusProj _ f x
  · intro x k hk k' hk'
    have heq := torusProj_injOn h (hsf hk) (hsf hk')
      ((torusProj_add_latticeTranslate _ x k).trans (torusProj_add_latticeTranslate _ x k').symm)
    have hp : latticeTranslate (torusSide L m) k = latticeTranslate (torusSide L m) k' :=
      add_left_cancel heq
    by_contra hne
    have h2 := le_euclidNormVec_latticeTranslate (a := torusSide L m) (sub_ne_zero.2 hne)
    rw [latticeTranslate_sub, hp, sub_self, euclidNormVec_zero] at h2
    exact absurd h.side_pos (not_lt.2 h2)
  · intro r hr hsub hle
    have hr' := radiusFits_of_le hr hle
    have hsr : Function.support f ⊆ radialBall r := (subset_tsupport f).trans hsub
    exact ⟨⟨hasDiameterLE_radialBall hr', hsr⟩, agreesWithPeriodization hr' hsr⟩
  · intro hL
    obtain ⟨C, hC0, hC⟩ := id hL
    have hcont : Continuous f :=
      YangMills.Construction.SeparatedFamilies.IsEuclidLipschitz.continuous ⟨C, fun x y => hC x y⟩
    obtain ⟨B, hB⟩ := hf.1.exists_bound_of_continuous hcont
    have hsup := uniformNorm_periodize h hsf hB
    have hlip := lipConstTorus_periodize_le h hsf hL
    refine ⟨⟨C, hC0, periodize_lipschitz_bound h hsf hC0 hC⟩, hsup, hlip, fun M hM => ?_⟩
    rw [sharpNormTorus, sharpNormR4, hsup]
    exact max_le_max le_rfl (mul_le_mul_of_nonneg_left hlip (by positivity))
end YangMills.Construction.PeriodicTransport
