import YangMills.Construction.InfiniteLattice.TransportToATorusProof
import YangMills.Construction.ResponseInTheExpansion.TheConnectedLawAtAPairIsTheFreeKernel
import YangMills.Construction.ResponseInTheExpansion.TheFreeKernelAtAPairIsPositiveProof
import YangMills.Construction.ResponseInTheExpansion.TheWeightsOfATupleAreLocalProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace YangMills.Construction.ResponseInTheExpansion
open TorusMetric TestFunctions PeriodicLattice LinearResponse
namespace PairCumulant
variable {S : ℝ}
private theorem abs_apply_le_euclidNormVec (v : Fin 4 → ℝ) (μ : Fin 4) : |v μ| ≤ euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
private theorem euclidNormVec_nonneg (v : Fin 4 → ℝ) : 0 ≤ euclidNormVec v := Real.sqrt_nonneg _
private theorem continuous_euclidNormVec : Continuous euclidNormVec := by apply _root_.YangMills.Construction.SeparatedTuples.continuous_euclidNormVec <;> assumption
private theorem torusProj_sub (v w : Fin 4 → ℝ) : torusProj S (v - w) = torusProj S v - torusProj S w := by apply _root_.YangMills.Construction.TestPairs.torusProj_map_sub <;> assumption
private theorem torusEuclidNorm_nonneg (x : Torus4 S) : 0 ≤ torusEuclidNorm x := by apply _root_.YangMills.Construction.TestPairs.torusEuclidNorm_nonneg <;> assumption
private theorem torusEuclidNorm_proj_le (v : Fin 4 → ℝ) : torusEuclidNorm (torusProj S v) ≤ euclidNormVec v := by apply _root_.YangMills.Construction.SourcesAndGluing.torusEuclidNorm_torusProj_le <;> assumption
private theorem exists_minimal_lift (x : Torus4 S) :
    ∃ b : Fin 4 → ℝ, torusProj S b = x ∧ euclidNormVec b = torusEuclidNorm x := by apply _root_.YangMills.Construction.AmbientPoints.exists_torusProj_eq_euclidNormVec_eq <;> assumption
private theorem torusEuclidNorm_add_le (x y : Torus4 S) :
    torusEuclidNorm (x + y) ≤ torusEuclidNorm x + torusEuclidNorm y := by apply _root_.YangMills.Construction.TestPairs.torusEuclidNorm_add_le <;> assumption
private theorem torusEuclidNorm_neg_le (x : Torus4 S) : torusEuclidNorm (-x) ≤ torusEuclidNorm x := by apply _root_.YangMills.Construction.PeriodicTransport.torusEuclidNorm_neg_le <;> assumption
private theorem torusEuclidNorm_sub_comm (x y : Torus4 S) : torusEuclidNorm (x - y) = torusEuclidNorm (y - x) := by apply _root_.YangMills.Construction.AmbientPoints.torusEuclidNorm_sub_comm <;> assumption
private theorem torusEuclidNorm_proj_eq (hS : 0 < S) {v : Fin 4 → ℝ} (hv : ∀ μ, |v μ| ≤ S / 2) :
    torusEuclidNorm (torusProj S v) = euclidNormVec v := by apply _root_.YangMills.SharedProofs.p44320 <;> assumption
private theorem continuous_comp_torusProj {f : Torus4 S → ℝ} (hf : IsLipschitzFor euclidDistTorus f) :
    Continuous (f ∘ torusProj S) := by apply _root_.YangMills.SharedProofs.p54921 <;> assumption
private theorem integral_liftToBall (hS : 0 < S) {c : Fin 4 → ℝ} {r : ℝ} (hr : r ≤ S / 4)
    {f : Torus4 S → ℝ} (hf : tsupport f ⊆ closedBallTorus (torusProj S c) r) :
    ∫ v, liftToBall S c r f v = torusVolumeIntegral S f := by apply _root_.YangMills.SharedProofs.p83706 <;> assumption
private theorem trace_planeKernelMatrix_mul_neg (hT : CurvatureKernelSqTraceFormula) {z : Fin 4 → ℝ}
    (hz : 0 < sqNorm z) :
    Matrix.trace (planeKernelMatrix z * planeKernelMatrix (-z)) = 6 / (Real.pi ^ 4 * sqNorm z ^ 4) := by apply _root_.YangMills.SharedProofs.p793 <;> assumption
private theorem traceAlongCycle_two_swap (u : Fin 2 → Fin 4 → ℝ) :
    traceAlongCycle S u 1 = Matrix.trace (planeKernelMatrix (periodicDisplacement S (u 1) (u 0)) *
      planeKernelMatrix (periodicDisplacement S (u 0) (u 1))) := by
  unfold traceAlongCycle
  have h0 : finRotate 2 0 = 1 := rfl
  have h1 : finRotate 2 1 = 0 := rfl
  simp [List.ofFn_succ, h0, h1]
private theorem torusProj_periodicDisplacement (hS : 0 < S) (v w : Fin 4 → ℝ) :
    torusProj S (periodicDisplacement S w v) = torusProj S v - torusProj S w := by
  rw [← torusProj_sub]
  funext i
  show (((circleSub S (v i) (w i) : ℝ)) : AddCircle S) = (((v i - w i : ℝ)) : AddCircle S)
  unfold circleSub
  rw [AddCircle.coe_sub]
  have : ((S * (round ((v i - w i) / S) : ℝ) : ℝ) : AddCircle S) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨round ((v i - w i) / S), by simp [mul_comm]⟩
  rw [this, sub_zero]
private theorem abs_periodicDisplacement_le (hS : 0 < S) (v w : Fin 4 → ℝ) (i : Fin 4) :
    |periodicDisplacement S w v i| ≤ S / 2 := by
  show |circleSub S (v i) (w i)| ≤ S / 2
  unfold circleSub
  have h1 := abs_sub_round ((v i - w i) / S)
  have e : v i - w i - S * (round ((v i - w i) / S) : ℝ) = S * ((v i - w i) / S - round ((v i - w i) / S)) := by
    field_simp
  rw [e, abs_mul, abs_of_pos hS]
  nlinarith
private theorem periodicDisplacement_antisymm (hS : 0 < S) (v w : Fin 4 → ℝ)
    (hD : torusEuclidNorm (torusProj S v - torusProj S w) ≤ S / 4) :
    periodicDisplacement S v w = -periodicDisplacement S w v ∧
      euclidNormVec (periodicDisplacement S w v) = torusEuclidNorm (torusProj S v - torusProj S w) := by
  have hE : euclidNormVec (periodicDisplacement S w v) = torusEuclidNorm (torusProj S v - torusProj S w) := by
    rw [← torusProj_periodicDisplacement hS, torusEuclidNorm_proj_eq hS (abs_periodicDisplacement_le hS v w)]
  have hE' : euclidNormVec (periodicDisplacement S v w) = torusEuclidNorm (torusProj S w - torusProj S v) := by
    rw [← torusProj_periodicDisplacement hS, torusEuclidNorm_proj_eq hS (abs_periodicDisplacement_le hS w v)]
  refine ⟨?_, hE⟩
  funext i
  have a1 : |periodicDisplacement S w v i| ≤ S / 4 := (abs_apply_le_euclidNormVec _ i).trans (hE.le.trans hD)
  have a2 : |periodicDisplacement S v w i| ≤ S / 4 := by
    refine (abs_apply_le_euclidNormVec _ i).trans (hE'.le.trans ?_)
    rw [torusEuclidNorm_sub_comm]
    exact hD
  show circleSub S (w i) (v i) = -circleSub S (v i) (w i)
  have a1' : |circleSub S (v i) (w i)| ≤ S / 4 := a1
  have a2' : |circleSub S (w i) (v i)| ≤ S / 4 := a2
  set k : ℤ := round ((v i - w i) / S) + round ((w i - v i) / S) with hk
  have e : circleSub S (w i) (v i) + circleSub S (v i) (w i) = -(S * (k : ℝ)) := by
    unfold circleSub
    rw [hk]
    push_cast
    ring
  have hb : |S * (k : ℝ)| < S := by
    have h3 : |S * (k : ℝ)| = |circleSub S (w i) (v i) + circleSub S (v i) (w i)| := by
      rw [e, abs_neg]
    rw [h3]
    have := abs_add_le (circleSub S (w i) (v i)) (circleSub S (v i) (w i))
    linarith
  have hk0 : k = 0 := by
    rw [abs_mul, abs_of_pos hS] at hb
    have h4 : |(k : ℝ)| < 1 := by
      by_contra hc
      push_neg at hc
      nlinarith
    have h5 : |k| < 1 := by exact_mod_cast h4
    exact Int.abs_lt_one_iff.1 h5
  rw [hk0] at e
  simp only [Int.cast_zero, mul_zero, neg_zero] at e
  linarith
private theorem zpow_neg_eight (a : ℝ) : a ^ (-8 : ℤ) = (a ^ 8)⁻¹ := by
  rw [zpow_neg]
  norm_cast
private theorem isCompact_closedBallR4 (c : Fin 4 → ℝ) (r : ℝ) : IsCompact (closedBallR4 c r) := by apply _root_.YangMills.SharedProofs.p20989 <;> assumption
private def invEighthPow (a b : Torus4 S) : ℝ := (torusEuclidNorm (a - b) ^ 8)⁻¹
private theorem continuous_torusEuclidNorm_proj : Continuous fun v : Fin 4 → ℝ => torusEuclidNorm (torusProj S v) := by
  rw [continuous_iff_continuousAt]
  intro v
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h0 : Tendsto (fun w => euclidNormVec (w - v) + euclidNormVec (v - w)) (𝓝 v) (𝓝 0) := by
    have hc : Continuous fun w : Fin 4 → ℝ => euclidNormVec (w - v) + euclidNormVec (v - w) :=
      (continuous_euclidNormVec.comp (continuous_id.sub continuous_const)).add
        (continuous_euclidNormVec.comp (continuous_const.sub continuous_id))
    simpa [euclidNormVec] using hc.tendsto v
  refine squeeze_zero (fun _ => norm_nonneg _) (fun w => ?_) h0
  have a1 : torusEuclidNorm (torusProj S w) ≤ torusEuclidNorm (torusProj S v) + euclidNormVec (w - v) := by
    have e : torusProj S w = torusProj S v + torusProj S (w - v) := by
      rw [torusProj_sub]
      abel
    rw [e]
    exact (torusEuclidNorm_add_le _ _).trans (add_le_add_right (torusEuclidNorm_proj_le _) _)
  have a2 : torusEuclidNorm (torusProj S v) ≤ torusEuclidNorm (torusProj S w) + euclidNormVec (v - w) := by
    have e : torusProj S v = torusProj S w + torusProj S (v - w) := by
      rw [torusProj_sub]
      abel
    rw [e]
    exact (torusEuclidNorm_add_le _ _).trans (add_le_add_right (torusEuclidNorm_proj_le _) _)
  have b1 := euclidNormVec_nonneg (w - v)
  have b2 := euclidNormVec_nonneg (v - w)
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith
private def pairIntegrand (f h : Torus4 S → ℝ) (p : (Fin 4 → ℝ) × (Fin 4 → ℝ)) : ℝ :=
  f (torusProj S p.1) * h (torusProj S p.2) * invEighthPow (torusProj S p.1) (torusProj S p.2)
private theorem measurable_pairIntegrand {f h : Torus4 S → ℝ} (hf : IsLipschitzFor euclidDistTorus f)
    (hh : IsLipschitzFor euclidDistTorus h) :
    Measurable (pairIntegrand f h) := by
  have c1 : Measurable fun p : (Fin 4 → ℝ) × (Fin 4 → ℝ) => f (torusProj S p.1) :=
    ((continuous_comp_torusProj hf).comp continuous_fst).measurable
  have c2 : Measurable fun p : (Fin 4 → ℝ) × (Fin 4 → ℝ) => h (torusProj S p.2) :=
    ((continuous_comp_torusProj hh).comp continuous_snd).measurable
  have c3 : Continuous fun p : (Fin 4 → ℝ) × (Fin 4 → ℝ) => torusEuclidNorm (torusProj S (p.1 - p.2)) :=
    continuous_torusEuclidNorm_proj.comp (continuous_fst.sub continuous_snd)
  have c4 : Measurable fun p : (Fin 4 → ℝ) × (Fin 4 → ℝ) => invEighthPow (torusProj S p.1) (torusProj S p.2) := by
    have e : (fun p : (Fin 4 → ℝ) × (Fin 4 → ℝ) => invEighthPow (torusProj S p.1) (torusProj S p.2)) =
        fun p => (torusEuclidNorm (torusProj S (p.1 - p.2)) ^ 8)⁻¹ := by
      funext p
      simp only [invEighthPow, torusProj_sub]
    rw [e]
    exact (c3.pow 8).measurable.inv
  exact (c1.mul c2).mul c4
private theorem integrableOn_pairIntegrand {f h : Torus4 S → ℝ} (hf : IsLipschitzFor euclidDistTorus f)
    (hh : IsLipschitzFor euclidDistTorus h)
    {n : ℝ} (hn : 0 < n) (h1 : ∀ a, |f a| ≤ 1) (h2 : ∀ a, |h a| ≤ 1)
    (hlow : ∀ a b, f a ≠ 0 → h b ≠ 0 → n ≤ torusEuclidNorm (a - b))
    {A B : Set (Fin 4 → ℝ)} (hA : volume A ≠ ∞) (hB : volume B ≠ ∞) :
    IntegrableOn (pairIntegrand f h) (A ×ˢ B) (volume : Measure ((Fin 4 → ℝ) × (Fin 4 → ℝ))) := by
  have hfin : (volume : Measure ((Fin 4 → ℝ) × (Fin 4 → ℝ))) (A ×ˢ B) ≠ ∞ := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_ne_top hA hB
  refine Measure.integrableOn_of_bounded (M := (n ^ 8)⁻¹) hfin
    (measurable_pairIntegrand hf hh).aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
  by_cases ha : f (torusProj S p.1) = 0
  · simp only [pairIntegrand, ha, zero_mul, norm_zero]
    positivity
  by_cases hb : h (torusProj S p.2) = 0
  · simp only [pairIntegrand, hb, mul_zero, zero_mul, norm_zero]
    positivity
  have hD := hlow _ _ ha hb
  have hp8 : 0 < n ^ 8 := by positivity
  have hle : n ^ 8 ≤ torusEuclidNorm (torusProj S p.1 - torusProj S p.2) ^ 8 := pow_le_pow_left₀ hn.le hD 8
  have hi : invEighthPow (torusProj S p.1) (torusProj S p.2) ≤ (n ^ 8)⁻¹ := inv_anti₀ hp8 hle
  have hi0 : 0 ≤ invEighthPow (torusProj S p.1) (torusProj S p.2) := by
    unfold invEighthPow
    positivity
  simp only [pairIntegrand, Real.norm_eq_abs, abs_mul, abs_of_nonneg hi0]
  calc |f (torusProj S p.1)| * |h (torusProj S p.2)| * invEighthPow (torusProj S p.1) (torusProj S p.2)
        ≤ 1 * 1 * (n ^ 8)⁻¹ := by
        have := h1 (torusProj S p.1)
        have := h2 (torusProj S p.2)
        gcongr
    _ = _ := by ring
private theorem setIntegral_ballProd_eq_cubeProd (hS : 0 < S) {f h : Torus4 S → ℝ}
    (hf : IsLipschitzFor euclidDistTorus f) (hh : IsLipschitzFor euclidDistTorus h)
    {n : ℝ} (hn : 0 < n) (h1 : ∀ a, |f a| ≤ 1) (h2 : ∀ a, |h a| ≤ 1)
    (hlow : ∀ a b, f a ≠ 0 → h b ≠ 0 → n ≤ torusEuclidNorm (a - b))
    {c : Fin 4 → ℝ} {r : ℝ} (hr : r ≤ S / 4) (hfs : tsupport f ⊆ closedBallTorus (torusProj S c) r)
    (hhs : tsupport h ⊆ closedBallTorus (torusProj S c) r) :
    ∫ p in closedBallR4 c r ×ˢ closedBallR4 c r, pairIntegrand f h p =
      ∫ p in (Set.pi Set.univ fun _ : Fin 4 => Ico (0 : ℝ) S) ×ˢ
        (Set.pi Set.univ fun _ : Fin 4 => Ico (0 : ℝ) S), pairIntegrand f h p := by
  have hBfin : volume (closedBallR4 c r) ≠ ∞ := (isCompact_closedBallR4 c r).measure_lt_top.ne
  have hQfin : volume (Set.pi Set.univ fun _ : Fin 4 => Ico (0 : ℝ) S) ≠ ∞ := by
    rw [Real.volume_pi_Ico]
    simp
  have hBm : MeasurableSet (closedBallR4 c r) :=
    (isClosed_le (continuous_euclidNormVec.comp (continuous_id.sub continuous_const))
      continuous_const).measurableSet
  rw [Measure.volume_eq_prod, setIntegral_prod _ (by
      rw [← Measure.volume_eq_prod]
      exact integrableOn_pairIntegrand hf hh hn h1 h2 hlow hBfin hBfin),
    setIntegral_prod _ (by
      rw [← Measure.volume_eq_prod]
      exact integrableOn_pairIntegrand hf hh hn h1 h2 hlow hQfin hQfin)]
  set J : Torus4 S → ℝ := fun a => torusVolumeIntegral S fun b => h b * invEighthPow a b with hJ
  have inner : ∀ v, ∫ w in closedBallR4 c r, pairIntegrand f h (v, w) = f (torusProj S v) * J (torusProj S v) := by
    intro v
    have e : ∀ w, pairIntegrand f h (v, w) =
        f (torusProj S v) * (h (torusProj S w) * invEighthPow (torusProj S v) (torusProj S w)) := fun w => by
      simp only [pairIntegrand]
      ring
    simp only [e]
    rw [integral_const_mul]
    congr 1
    have h3 := integral_liftToBall hS hr (f := fun b => h b * invEighthPow (torusProj S v) b)
      ((tsupport_mul_subset_left).trans hhs)
    unfold liftToBall at h3
    rw [integral_indicator hBm] at h3
    exact h3
  have inner' : ∀ v, ∫ w in Set.pi Set.univ fun _ : Fin 4 => Ico (0 : ℝ) S, pairIntegrand f h (v, w) =
      f (torusProj S v) * J (torusProj S v) := by
    intro v
    have e : ∀ w, pairIntegrand f h (v, w) =
        f (torusProj S v) * (h (torusProj S w) * invEighthPow (torusProj S v) (torusProj S w)) := fun w => by
      simp only [pairIntegrand]
      ring
    simp only [e]
    rw [integral_const_mul]
    rfl
  simp only [inner, inner']
  have h3 := integral_liftToBall hS hr (f := fun a => f a * J a) ((tsupport_mul_subset_left).trans hfs)
  unfold liftToBall at h3
  rw [integral_indicator hBm] at h3
  exact h3
private theorem abs_le_one_of_uniformNorm_eq_one {X : Type} {f : X → ℝ} (h1 : uniformNorm f = 1) (x : X) :
    |f x| ≤ 1 := by apply _root_.YangMills.SharedProofs.p64038 <;> assumption
private theorem exists_ne_zero_of_uniformNorm_eq_one {X : Type} {f : X → ℝ} (h1 : uniformNorm f = 1) :
    ∃ x, f x ≠ 0 := by apply _root_.YangMills.SharedProofs.p97669 <;> assumption
private theorem torusEuclidNorm_sub_le_of_tsupport_ball {g : Torus4 S → ℝ} {c : Torus4 S} {n : ℝ}
    (hs : tsupport g ⊆ closedBallTorus c n) {x z : Torus4 S}
    (hx : x ∈ tsupport g) (hz : z ∈ tsupport g) : torusEuclidNorm (x - z) ≤ 2 * n := by
  have hx' : torusEuclidNorm (x - c) ≤ n := hs hx
  have hz' : torusEuclidNorm (z - c) ≤ n := hs hz
  have e : x - z = (x - c) + -(z - c) := by abel
  have h2 := torusEuclidNorm_add_le (x - c) (-(z - c))
  have h3 := torusEuclidNorm_neg_le (z - c)
  rw [← e] at h2
  linarith
open Classical in
private theorem gaussianCumulantLimit_pair_eq (hT : CurvatureKernelSqTraceFormula) (hS : 0 < S)
    {f h : Torus4 S → ℝ}
    (hf : IsLipschitzFor euclidDistTorus f) (hh : IsLipschitzFor euclidDistTorus h) {n : ℝ} (hn : 0 < n)
    (hlow : ∀ a b, f a ≠ 0 → h b ≠ 0 → n ≤ torusEuclidNorm (a - b))
    (hup : ∀ a b, f a ≠ 0 → h b ≠ 0 → torusEuclidNorm (a - b) ≤ S / 4) :
    gaussianCumulantLimit S (q := 1) ![f, h] = 9 / Real.pi ^ 4 *
      ∫ p in (Set.pi Set.univ fun _ : Fin 4 => Ico (0 : ℝ) S) ×ˢ
        (Set.pi Set.univ fun _ : Fin 4 => Ico (0 : ℝ) S), pairIntegrand f h p := by
  have e : (Finset.univ : Finset (Equiv.Perm (Fin 2))).filter (fun s => s 0 = 0) = {1} := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      ext i
      fin_cases i
      · simpa using congrArg Fin.val h
      · have h1 : s 1 ≠ 0 := fun e => by
          have := s.injective (e.trans h.symm)
          exact absurd this (by decide)
        have h2 : s 1 = 1 := by
          revert h1
          generalize s 1 = t
          fin_cases t <;> simp
        simpa using congrArg Fin.val h2
    · rintro rfl
      rfl
  unfold gaussianCumulantLimit
  rw [e, Finset.sum_singleton]
  have hpt : ∀ u : Fin 2 → Fin 4 → ℝ,
      (∏ i, (![f, h] : Fin 2 → _) i (torusProj S (u i))) * traceAlongCycle S u 1 =
      6 / Real.pi ^ 4 * pairIntegrand f h (u 0, u 1) := by
    intro u
    rw [Fin.prod_univ_two]
    show f (torusProj S (u 0)) * h (torusProj S (u 1)) * traceAlongCycle S u 1 = _
    by_cases ha : f (torusProj S (u 0)) = 0
    · simp [pairIntegrand, ha]
    by_cases hb : h (torusProj S (u 1)) = 0
    · simp [pairIntegrand, hb]
    have hD := hlow _ _ ha hb
    obtain ⟨hopp, hE⟩ := periodicDisplacement_antisymm hS (u 0) (u 1) (hup _ _ ha hb)
    rw [traceAlongCycle_two_swap, hopp]
    have hsq : sqNorm (periodicDisplacement S (u 1) (u 0)) =
        torusEuclidNorm (torusProj S (u 0) - torusProj S (u 1)) ^ 2 := by
      rw [← hE]
      unfold euclidNormVec sqNorm
      rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    have hDp : 0 < torusEuclidNorm (torusProj S (u 0) - torusProj S (u 1)) := by linarith
    rw [trace_planeKernelMatrix_mul_neg hT (by rw [hsq]; positivity), hsq]
    simp only [pairIntegrand, invEighthPow]
    have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
    field_simp
  have hint : ∫ u in Set.pi Set.univ (fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 4 => Ico (0 : ℝ) S),
      pairIntegrand f h (u 0, u 1) =
      ∫ p in (Set.pi Set.univ fun _ : Fin 4 => Ico (0 : ℝ) S) ×ˢ
        (Set.pi Set.univ fun _ : Fin 4 => Ico (0 : ℝ) S), pairIntegrand f h p := by
    have h1 := (volume_preserving_finTwoArrow (Fin 4 → ℝ)).setIntegral_preimage_emb
      (MeasurableEquiv.measurableEmbedding _) (pairIntegrand f h)
      ((Set.pi Set.univ fun _ : Fin 4 => Ico (0 : ℝ) S) ×ˢ (Set.pi Set.univ fun _ : Fin 4 => Ico (0 : ℝ) S))
    have h2 : (MeasurableEquiv.finTwoArrow (α := Fin 4 → ℝ)) ⁻¹'
        ((Set.pi Set.univ fun _ : Fin 4 => Ico (0 : ℝ) S) ×ˢ (Set.pi Set.univ fun _ : Fin 4 => Ico (0 : ℝ) S)) =
        Set.pi Set.univ (fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 4 => Ico (0 : ℝ) S) := by
      ext u
      simp [Set.mem_prod, Fin.forall_fin_two, MeasurableEquiv.finTwoArrow]
    rw [h2] at h1
    exact h1
  simp only [hpt]
  rw [integral_const_mul, hint]
  ring
end PairCumulant
open PairCumulant in
theorem pairCumulant_eq_freeKernel (hT : CurvatureKernelSqTraceFormula) :
    pairCumulantEqFreeKernelStatement := by
  intro ℓ m n vt f h hn hvt hside hp
  obtain ⟨⟨x₁, x₂, hb₁, hb₂, hd₁, hd₂⟩, hf1, hh1⟩ := hp
  have hS : 0 < torusSide ℓ.side m := by linarith
  have h1 := abs_le_one_of_uniformNorm_eq_one hf1
  have h2 := abs_le_one_of_uniformNorm_eq_one hh1
  have hlowT : ∀ a ∈ tsupport f, ∀ b ∈ tsupport h, n ≤ torusEuclidNorm (a - b) := by
    intro a ha b hb
    have a1 : setEuclidDist (tsupport f) (tsupport h) ≤ ENNReal.ofReal (torusEuclidNorm (a - b)) :=
      (iInf₂_le a ha).trans (iInf₂_le b hb)
    have a2 := hd₁.trans a1
    exact (ENNReal.ofReal_le_ofReal_iff (torusEuclidNorm_nonneg _)).1 a2
  have hupT : ∀ a ∈ tsupport f, ∀ b ∈ tsupport h, torusEuclidNorm (a - b) ≤ 10 * n := by
    intro x hx z hz
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hlt : setEuclidDist (tsupport f) (tsupport h) < ENNReal.ofReal (6 * n + ε) :=
      lt_of_le_of_lt hd₂ ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith))
    unfold setEuclidDist at hlt
    simp only [iInf_lt_iff] at hlt
    obtain ⟨a, ha, b, hb, hab⟩ := hlt
    have hab' : torusEuclidNorm (a - b) < 6 * n + ε := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 hab
    have t1 := torusEuclidNorm_sub_le_of_tsupport_ball hb₁.2.2.2.1 hx ha
    have t2 := torusEuclidNorm_sub_le_of_tsupport_ball hb₂.2.2.2.1 hb hz
    have e : x - z = (x - a) + ((a - b) + (b - z)) := by abel
    have t3 := torusEuclidNorm_add_le (x - a) ((a - b) + (b - z))
    have t4 := torusEuclidNorm_add_le (a - b) (b - z)
    rw [← e] at t3
    linarith
  have hlow : ∀ a b, f a ≠ 0 → h b ≠ 0 → n ≤ torusEuclidNorm (a - b) := fun a b ha hb =>
    hlowT a (subset_tsupport _ ha) b (subset_tsupport _ hb)
  have hup : ∀ a b, f a ≠ 0 → h b ≠ 0 → torusEuclidNorm (a - b) ≤ torusSide ℓ.side m / 4 := fun a b ha hb =>
    (hupT a (subset_tsupport _ ha) b (subset_tsupport _ hb)).trans (by linarith)
  rw [gaussianCumulantLimit_pair_eq hT hS hb₁.1 hb₂.1 hn hlow hup]
  congr 1
  obtain ⟨x₀, hx₀⟩ := exists_ne_zero_of_uniformNorm_eq_one hf1
  obtain ⟨c, hc, -⟩ := exists_minimal_lift x₀
  have hx₀s : x₀ ∈ tsupport f := subset_tsupport _ hx₀
  have H : ∃ q : (Fin 4 → ℝ) × ℝ, IsKernelBallTorus f h q.1 q.2 := by
    refine ⟨(c, 10 * n), lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hn) hd₁, by
      show 0 < 10 * n
      positivity, ?_, ?_, ?_⟩
    · show 10 * n ≤ torusSide ℓ.side m / 4
      linarith
    · intro u hu
      show torusEuclidNorm (u - torusProj _ c) ≤ 10 * n
      rw [hc]
      have := torusEuclidNorm_sub_le_of_tsupport_ball hb₁.2.2.2.1 hu hx₀s
      linarith
    · intro w hw
      show torusEuclidNorm (w - torusProj _ c) ≤ 10 * n
      rw [hc, torusEuclidNorm_sub_comm]
      exact hupT x₀ hx₀s w hw
  unfold inverseEighthKernelTorus
  rw [dif_pos H]
  obtain ⟨-, -, hr, hbf, hbh⟩ := H.choose_spec
  rw [← setIntegral_ballProd_eq_cubeProd hS hb₁.1 hb₂.1 hn h1 h2 hlow hr hbf hbh]
  unfold inverseEighthKernel
  set cc := H.choose.1 with hcc
  set rr := H.choose.2 with hrr
  have hBm : MeasurableSet (closedBallR4 cc rr) :=
    (isClosed_le (continuous_euclidNormVec.comp (continuous_id.sub continuous_const))
      continuous_const).measurableSet
  rw [← integral_indicator (hBm.prod hBm)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  show Set.indicator _ _ q = _
  by_cases h₁ : q.1 ∈ closedBallR4 cc rr
  · by_cases h₂ : q.2 ∈ closedBallR4 cc rr
    · rw [Set.indicator_of_mem (show q ∈ _ ×ˢ _ from ⟨h₁, h₂⟩)]
      simp only [liftToBall, Set.indicator_of_mem h₁, Set.indicator_of_mem h₂, Function.comp,
        pairIntegrand, invEighthPow, RCLike.ofReal_real_eq_id, id]
      rw [← torusProj_sub, torusEuclidNorm_proj_eq hS, zpow_neg_eight]
      intro μ
      have a1 : |(q.1 - cc) μ| ≤ rr := (abs_apply_le_euclidNormVec (q.1 - cc) μ).trans h₁
      have a2 : |(q.2 - cc) μ| ≤ rr := (abs_apply_le_euclidNormVec (q.2 - cc) μ).trans h₂
      simp only [Pi.sub_apply] at a1 a2 ⊢
      have e : q.1 μ - q.2 μ = (q.1 μ - cc μ) - (q.2 μ - cc μ) := by ring
      rw [e]
      have := abs_sub (q.1 μ - cc μ) (q.2 μ - cc μ)
      linarith
    · rw [Set.indicator_of_notMem (fun hm => h₂ hm.2)]
      simp [liftToBall, Set.indicator_of_notMem h₂]
  · rw [Set.indicator_of_notMem (fun hm => h₁ hm.1)]
    simp [liftToBall, Set.indicator_of_notMem h₁]
end YangMills.Construction.ResponseInTheExpansion
end
