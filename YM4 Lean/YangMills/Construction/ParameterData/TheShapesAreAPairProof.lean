import YangMills.Construction.ParameterData.TheShapesAreAPair
import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory Set TorusMetric TestFunctions
open scoped ENNReal
namespace TrajectoryData
variable {S : ℝ}
private theorem torusEuclidNorm_eq_sqrt (x : Torus4 S) :
    torusEuclidNorm x = Real.sqrt (∑ μ, ‖x μ‖ ^ 2) := by apply _root_.YangMills.Construction.AmbientPoints.torusEuclidNorm_eq_sqrt <;> assumption
private theorem torusEuclidNorm_add_le (x y : Torus4 S) :
    torusEuclidNorm (x + y) ≤ torusEuclidNorm x + torusEuclidNorm y := by apply _root_.YangMills.Construction.TestPairs.torusEuclidNorm_add_le <;> assumption
private theorem torusEuclidNorm_zero : torusEuclidNorm (0 : Torus4 S) = 0 := by apply _root_.YangMills.Construction.TestPairs.torusEuclidNorm_zero <;> assumption
private theorem torusEuclidNorm_sub_comm (x y : Torus4 S) :
    torusEuclidNorm (x - y) = torusEuclidNorm (y - x) := by apply _root_.YangMills.Construction.AmbientPoints.torusEuclidNorm_sub_comm <;> assumption
private theorem torusEuclidNorm_proj_le (w : Fin 4 → ℝ) :
    torusEuclidNorm (torusProj S w) ≤ euclidNormVec w := by apply _root_.YangMills.Construction.SourcesAndGluing.torusEuclidNorm_torusProj_le <;> assumption
private theorem continuous_torusEuclidNorm : Continuous (torusEuclidNorm : Torus4 S → ℝ) := by apply _root_.YangMills.Construction.TestPairs.continuous_torusEuclidNorm <;> assumption
private theorem torusEuclidNorm_proj_single (hS : 0 < S) {t : ℝ} (ht : |t| ≤ S / 2) :
    torusEuclidNorm (torusProj S (Pi.single 0 t)) = |t| := by
  have h : ‖(t : AddCircle S)‖ = |t| :=
    (AddCircle.norm_coe_eq_abs_iff S hS.ne').2 (by rwa [abs_of_pos hS])
  rw [torusEuclidNorm_eq_sqrt, Fin.sum_univ_four]
  simp [torusProj, h, Real.sqrt_sq_eq_abs]
private theorem torusProj_add (u w : Fin 4 → ℝ) :
    torusProj S (u + w) = torusProj S u + torusProj S w := by apply _root_.YangMills.Construction.TestPairs.torusProj_map_add <;> assumption
private theorem torusProj_sub (u w : Fin 4 → ℝ) :
    torusProj S (u - w) = torusProj S u - torusProj S w := by apply _root_.YangMills.Construction.TestPairs.torusProj_map_sub <;> assumption
private theorem continuous_torusProj : Continuous (torusProj S) := by apply _root_.YangMills.Construction.TestPairs.continuous_torusProj <;> assumption
private theorem abs_apply_le_euclidNormVec (u : Fin 4 → ℝ) (i : Fin 4) :
    |u i| ≤ euclidNormVec u := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
private theorem tentProfile_nonneg (r : ℝ) : 0 ≤ tentProfile r := le_max_right _ _
private theorem tentProfile_le_one (r : ℝ) : tentProfile r ≤ 1 :=
  max_le (min_le_left _ _) zero_le_one
private theorem tentProfile_eq_one {r : ℝ} (hr : r ≤ 1 / 2) : tentProfile r = 1 := by
  unfold tentProfile
  rw [min_eq_left (by linarith)]
  exact max_eq_left zero_le_one
private theorem tentProfile_eq_zero {r : ℝ} (hr : 1 ≤ r) : tentProfile r = 0 := by
  unfold tentProfile
  exact max_eq_right (min_le_of_right_le (by linarith))
private theorem abs_tentProfile_sub_le (r s : ℝ) :
    |tentProfile r - tentProfile s| ≤ 2 * |r - s| := by
  unfold tentProfile
  refine (abs_max_sub_max_le_abs _ _ _).trans ((abs_min_sub_min_le_max _ _ _ _).trans ?_)
  rw [sub_self, abs_zero]
  refine max_le (by positivity) (le_of_eq ?_)
  rw [show 2 * (1 - r) - 2 * (1 - s) = 2 * (s - r) by ring, abs_mul, abs_two, abs_sub_comm]
private theorem continuous_tentProfile : Continuous tentProfile := by
  have h : tentProfile = fun r : ℝ => max (min 1 (2 * (1 - r))) 0 := rfl
  rw [h]
  fun_prop
private def centredTent (S n : ℝ) (c p : Torus4 S) : ℝ :=
  tentProfile (torusEuclidNorm (p - c) / (0.99 * n))
private theorem centredTent_nonneg (n : ℝ) (c p : Torus4 S) : 0 ≤ centredTent S n c p :=
  tentProfile_nonneg _
private theorem centredTent_le_one (n : ℝ) (c p : Torus4 S) : centredTent S n c p ≤ 1 :=
  tentProfile_le_one _
private theorem centredTent_self (n : ℝ) (c : Torus4 S) : centredTent S n c c = 1 := by
  unfold centredTent
  rw [sub_self, torusEuclidNorm_zero, zero_div]
  exact tentProfile_eq_one (by norm_num)
private theorem continuous_centredTent (n : ℝ) (c : Torus4 S) :
    Continuous (centredTent S n c) :=
  continuous_tentProfile.comp
    ((continuous_torusEuclidNorm.comp (continuous_id.sub continuous_const)).div_const _)
private theorem centredTent_lipschitz {n : ℝ} (hn : 0 < n) (c x y : Torus4 S) :
    ‖centredTent S n c x - centredTent S n c y‖ ≤ 2 / (0.99 * n) * euclidDistTorus x y := by
  have hk : 0 < 0.99 * n := by positivity
  have hA : torusEuclidNorm (x - c) ≤ torusEuclidNorm (x - y) + torusEuclidNorm (y - c) := by
    have := torusEuclidNorm_add_le (x - y) (y - c)
    rwa [sub_add_sub_cancel] at this
  have hB : torusEuclidNorm (y - c) ≤ torusEuclidNorm (x - y) + torusEuclidNorm (x - c) := by
    have := torusEuclidNorm_add_le (y - x) (x - c)
    rwa [sub_add_sub_cancel, torusEuclidNorm_sub_comm y x] at this
  have hAB : |torusEuclidNorm (x - c) - torusEuclidNorm (y - c)| ≤ torusEuclidNorm (x - y) :=
    abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  calc ‖centredTent S n c x - centredTent S n c y‖
      ≤ 2 * |torusEuclidNorm (x - c) / (0.99 * n) - torusEuclidNorm (y - c) / (0.99 * n)| :=
        abs_tentProfile_sub_le _ _
    _ = 2 / (0.99 * n) * |torusEuclidNorm (x - c) - torusEuclidNorm (y - c)| := by
        rw [← sub_div, abs_div, abs_of_pos hk]
        ring
    _ ≤ 2 / (0.99 * n) * euclidDistTorus x y :=
        mul_le_mul_of_nonneg_left hAB (by positivity)
private theorem uniformNorm_centredTent (n : ℝ) (c : Torus4 S) :
    uniformNorm (centredTent S n c) = 1 := by
  have hnorm : ∀ x, ‖centredTent S n c x‖ = centredTent S n c x := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (centredTent_nonneg n c x)]
  unfold uniformNorm
  have : Nonempty (Torus4 S) := ⟨c⟩
  apply le_antisymm
  · exact ciSup_le fun x => by rw [hnorm]; exact centredTent_le_one n c x
  · have hb : BddAbove (range fun x => ‖centredTent S n c x‖) := by
      refine ⟨1, ?_⟩
      rintro _ ⟨x, rfl⟩
      simp only [hnorm]
      exact centredTent_le_one n c x
    calc (1 : ℝ) = ‖centredTent S n c c‖ := by rw [hnorm, centredTent_self]
      _ ≤ _ := le_ciSup hb c
private theorem tsupport_centredTent {n : ℝ} (hn : 0 < n) (c : Torus4 S) :
    tsupport (centredTent S n c) ⊆ {p | torusEuclidNorm (p - c) ≤ 0.99 * n} := by
  refine closure_minimal ?_ (isClosed_le (continuous_torusEuclidNorm.comp
    (continuous_id.sub continuous_const)) continuous_const)
  intro p hp
  by_contra h
  apply hp
  have hk : 0 < 0.99 * n := by positivity
  exact tentProfile_eq_zero ((one_le_div hk).2 (not_le.1 h).le)
private theorem integral_periodCube [Fact (0 < S)] {f : Torus4 S → ℝ} (hf : Continuous f)
    (t : Fin 4 → ℝ) :
    ∫ v in Set.pi univ (fun i => Ioc (t i) (t i + S)), f (torusProj S v) =
      ∫ x, f x ∂(Measure.pi fun _ : Fin 4 => (volume : Measure (AddCircle S))) := by
  have hmp := measurePreserving_pi
    (fun i : Fin 4 => (volume : Measure ℝ).restrict (Ioc (t i) (t i + S)))
    (fun _ : Fin 4 => (volume : Measure (AddCircle S)))
    (fun i => AddCircle.measurePreserving_mk S (t i))
  rw [← hmp.map_eq, integral_map hmp.aemeasurable hf.aestronglyMeasurable, volume_pi,
    Measure.restrict_pi_pi]
  rfl
private theorem torusVolumeIntegral_eq_periodCube (hS : 0 < S) {f : Torus4 S → ℝ}
    (hf : Continuous f) (t : Fin 4 → ℝ) :
    torusVolumeIntegral S f =
      ∫ v in Set.pi univ (fun i => Ioc (t i) (t i + S)), f (torusProj S v) := by
  have : Fact (0 < S) := ⟨hS⟩
  rw [integral_periodCube hf t, ← integral_periodCube hf 0]
  unfold torusVolumeIntegral
  refine setIntegral_congr_set ?_
  have h := Measure.ae_eq_set_pi (μ := fun _ : Fin 4 => (volume : Measure ℝ)) (I := univ)
    (s := fun _ => Ico (0 : ℝ) S) (t := fun _ => Ioc (0 : ℝ) S) (fun _ _ => Ico_ae_eq_Ioc)
  simpa [volume_pi] using h
private theorem volume_euclidNormVec_ball (w : Fin 4 → ℝ) {R : ℝ} (hR : 0 < R) :
    volume {u : Fin 4 → ℝ | euclidNormVec (u - w) < R} =
      ENNReal.ofReal (R ^ 4 * (Real.pi ^ 2 / 2)) := by
  have hpre : {u : Fin 4 → ℝ | euclidNormVec (u - w) < R} =
      (fun u => u + (-w)) ⁻¹' {x : Fin 4 → ℝ | (∑ i, |x i| ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) < R} := by
    ext u
    simp only [mem_ofPred_eq, mem_preimage, euclidNormVec, ← sub_eq_add_neg, Real.sqrt_eq_rpow,
      Real.rpow_two, sq_abs]
  have h1 : Real.Gamma (1 / 2 + 1) = Real.sqrt Real.pi / 2 := by
    rw [Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
    ring
  have h2 : Real.Gamma ((4 : ℝ) / 2 + 1) = 2 := by
    rw [show (4 : ℝ) / 2 + 1 = ((2 : ℕ) : ℝ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
    norm_num [Nat.factorial]
  have h3 : Real.sqrt Real.pi ^ 4 = Real.pi ^ 2 := by
    rw [show Real.sqrt Real.pi ^ 4 = (Real.sqrt Real.pi ^ 2) ^ 2 by ring,
      Real.sq_sqrt Real.pi_pos.le]
  rw [hpre, measure_preimage_add_right, volume_sum_rpow_lt (Fin 4) (by norm_num : (1 : ℝ) ≤ 2) R]
  simp only [Fintype.card_fin, Nat.cast_ofNat]
  rw [h1, h2, ← ENNReal.ofReal_pow hR.le, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [show 2 * (Real.sqrt Real.pi / 2) = Real.sqrt Real.pi by ring, h3]
private theorem integral_centredTent_ge (hS₀ : 0 < S) {n : ℝ} (hn : 0 < n) (hS : 40 * n ≤ S)
    (w : Fin 4 → ℝ) :
    1 / 4 * n ^ 4 ≤ torusVolumeIntegral S (centredTent S n (torusProj S w)) := by
  have hF : Continuous fun u => centredTent S n (torusProj S w) (torusProj S u) :=
    (continuous_centredTent n _).comp continuous_torusProj
  set t : Fin 4 → ℝ := fun i => w i - S / 2 with ht
  set R : ℝ := 0.495 * n with hRdef
  have hR : 0 < R := by positivity
  set A : Set (Fin 4 → ℝ) := {u | euclidNormVec (u - w) < R} with hA
  set C : Set (Fin 4 → ℝ) := Set.pi univ fun i => Ioc (t i) (t i + S) with hC
  have hAC : A ⊆ C := by
    intro u hu i _
    have h1 : |(u - w) i| ≤ euclidNormVec (u - w) := abs_apply_le_euclidNormVec _ i
    have h2 := abs_le.1 (h1.trans (le_of_lt hu))
    simp only [Pi.sub_apply] at h2
    have h3 : R ≤ S / 2 := by rw [hRdef]; linarith
    constructor
    · simp only [ht]; linarith [h2.1]
    · simp only [ht]; linarith [h2.2]
  have hone : ∀ u ∈ A, centredTent S n (torusProj S w) (torusProj S u) = 1 := by
    intro u hu
    unfold centredTent
    refine tentProfile_eq_one ?_
    rw [← torusProj_sub]
    have h1 : torusEuclidNorm (torusProj S (u - w)) ≤ R :=
      (torusEuclidNorm_proj_le _).trans (le_of_lt hu)
    rw [div_le_iff₀ (by positivity)]
    rw [hRdef] at h1
    linarith
  have hAmeas : MeasurableSet A := by
    refine measurableSet_lt ?_ measurable_const
    have hc : Continuous fun u : Fin 4 → ℝ => euclidNormVec (u - w) := by
      unfold euclidNormVec
      fun_prop
    exact hc.measurable
  have hint : IntegrableOn (fun u => centredTent S n (torusProj S w) (torusProj S u)) C := by
    have hIcc : IntegrableOn (fun u => centredTent S n (torusProj S w) (torusProj S u))
        (Icc t (fun i => t i + S)) := hF.continuousOn.integrableOn_compact isCompact_Icc
    refine hIcc.mono_set fun u hu => ⟨fun i => ?_, fun i => ?_⟩
    · exact (hu i (mem_univ i)).1.le
    · exact (hu i (mem_univ i)).2
  have hvol : (volume A).toReal = R ^ 4 * (Real.pi ^ 2 / 2) := by
    rw [hA, volume_euclidNormVec_ball w hR, ENNReal.toReal_ofReal (by positivity)]
  have hleft : ∫ u in A, centredTent S n (torusProj S w) (torusProj S u) =
      R ^ 4 * (Real.pi ^ 2 / 2) := by
    rw [setIntegral_congr_fun hAmeas hone, setIntegral_const, smul_eq_mul, mul_one, Measure.real,
      hvol]
  have hmono : ∫ u in A, centredTent S n (torusProj S w) (torusProj S u) ≤
      ∫ u in C, centredTent S n (torusProj S w) (torusProj S u) :=
    setIntegral_mono_set hint (Filter.Eventually.of_forall fun u => centredTent_nonneg n _ _)
      (LE.le.eventuallyLE hAC)
  rw [torusVolumeIntegral_eq_periodCube hS₀ (continuous_centredTent n _) t]
  refine le_trans ?_ hmono
  rw [hleft, hRdef]
  have hpi : (9.8 : ℝ) ≤ Real.pi ^ 2 := by
    have := Real.pi_gt_d2
    nlinarith
  have hn4 : 0 < n ^ 4 := by positivity
  have : (0.495 * n) ^ 4 * (Real.pi ^ 2 / 2) = n ^ 4 * (0.495 ^ 4 * (Real.pi ^ 2 / 2)) := by ring
  rw [this]
  nlinarith
private theorem isShapedBump_centredTent (hS₀ : 0 < S) {n : ℝ} (hn : 0 < n) (hS : 40 * n ≤ S)
    (w : Fin 4 → ℝ) :
    IsShapedBump euclidDistTorus closedBallTorus (torusVolumeIntegral S) n (1 / 4)
      (torusProj S w) (centredTent S n (torusProj S w)) := by
  have hk : 0 < 0.99 * n := by positivity
  refine ⟨⟨2 / (0.99 * n), by positivity, centredTent_lipschitz hn _⟩, centredTent_nonneg n _,
    ⟨torusProj S w, ?_⟩, ?_, ?_, ?_⟩
  · rw [centredTent_self]
    exact one_ne_zero
  · intro p hp
    have h := tsupport_centredTent hn _ hp
    have h' : torusEuclidNorm (p - torusProj S w) ≤ 0.99 * n := h
    show torusEuclidNorm (p - torusProj S w) ≤ n
    linarith
  · rw [uniformNorm_centredTent, mul_one]
    exact integral_centredTent_ge hS₀ hn hS w
  · rw [uniformNorm_centredTent]
    have h : bestLipschitzConstant euclidDistTorus (centredTent S n (torusProj S w)) ≤
        2 / (0.99 * n) :=
      csInf_le ⟨0, fun _ h => h.1⟩ ⟨by positivity, centredTent_lipschitz hn _⟩
    refine h.trans ?_
    rw [div_le_div_iff₀ hk (by positivity)]
    linarith
theorem bumpsFormSeparatedPair : bumpsFormSeparatedPairStatement := by
  intro L m n v hL hn hS
  have hS₀ : 0 < PeriodicLattice.torusSide L m := by linarith
  set S := PeriodicLattice.torusSide L m with hSdef
  set w : Fin 4 → ℝ := fun i => (v i : ℝ) with hw
  set e : Fin 4 → ℝ := Pi.single 0 (3.5 * n) with he
  have e₁ : firstBump L m n v = centredTent S n (torusProj S w) := rfl
  have e₂ : translatedBump L m n v = centredTent S n (torusProj S (w + e)) := by
    funext p
    show tentProfile (torusEuclidNorm ((p - torusProj S e) - torusProj S w) / (0.99 * n)) =
      tentProfile (torusEuclidNorm (p - torusProj S (w + e)) / (0.99 * n))
    rw [torusProj_add, sub_sub, add_comm (torusProj S e)]
  have hdist : torusEuclidNorm (torusProj S (w + e) - torusProj S w) = 3.5 * n := by
    rw [torusProj_add, add_sub_cancel_left, he, torusEuclidNorm_proj_single hS₀,
      abs_of_pos (by positivity)]
    rw [abs_of_pos (by positivity)]
    linarith
  rw [e₁, e₂]
  refine ⟨torusProj S w, torusProj S (w + e), isShapedBump_centredTent hS₀ hn hS w,
    isShapedBump_centredTent hS₀ hn hS (w + e), ?_, ?_⟩
  · refine le_iInf₂ fun a ha => le_iInf₂ fun b hb => ENNReal.ofReal_le_ofReal ?_
    have ha' : torusEuclidNorm (a - torusProj S w) ≤ 0.99 * n := tsupport_centredTent hn _ ha
    have hb' : torusEuclidNorm (b - torusProj S (w + e)) ≤ 0.99 * n :=
      tsupport_centredTent hn _ hb
    have h₁ := torusEuclidNorm_add_le (torusProj S (w + e) - b) (b - torusProj S w)
    have h₂ := torusEuclidNorm_add_le (b - a) (a - torusProj S w)
    rw [sub_add_sub_cancel, hdist, torusEuclidNorm_sub_comm (torusProj S (w + e)) b] at h₁
    rw [sub_add_sub_cancel] at h₂
    rw [torusEuclidNorm_sub_comm b a] at h₂
    linarith
  · have hc : torusProj S w ∈ tsupport (centredTent S n (torusProj S w)) :=
      subset_tsupport _ (by
        show centredTent S n (torusProj S w) (torusProj S w) ≠ 0
        rw [centredTent_self]
        exact one_ne_zero)
    have hc' : torusProj S (w + e) ∈ tsupport (centredTent S n (torusProj S (w + e))) :=
      subset_tsupport _ (by
        show centredTent S n (torusProj S (w + e)) (torusProj S (w + e)) ≠ 0
        rw [centredTent_self]
        exact one_ne_zero)
    refine (iInf₂_le _ hc).trans ((iInf₂_le _ hc').trans (ENNReal.ofReal_le_ofReal ?_))
    rw [torusEuclidNorm_sub_comm, hdist]
    linarith
end TrajectoryData
end YangMills.Construction
end
