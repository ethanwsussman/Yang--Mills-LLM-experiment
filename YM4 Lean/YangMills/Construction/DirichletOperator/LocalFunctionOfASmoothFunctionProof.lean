import YangMills.Construction.DirichletOperator.LocalFunctionOfASmoothFunction
import YangMills.Construction.DirichletOperator.WhereThePartitionFunctionOfACubeLives
import YangMills.Construction.PartitionCubes.DiffBoundsFromDerivsProof
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open scoped ContDiff
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.Torus YangMills.Construction.RegionSequence
open YangMills.Construction.RegionSequence.NestedRegions
namespace PartitionCubes.TransferOfSmooth
theorem torusProj_add (L : ℝ) (a b : Fin 4 → ℝ) :
    torusProj 4 L (a + b) = torusProj 4 L a + torusProj 4 L b := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.torusProj_add <;> assumption
theorem torusProj_surjective (L : ℝ) (y : PeriodicTorus 4 L) :
    ∃ w : Fin 4 → ℝ, torusProj 4 L w = y := by apply _root_.YangMills.Construction.PartitionCubes.FiniteDifference.exists_torusProj_eq <;> assumption
theorem torusProj_sub_eq_zero {L : ℝ} {a b : Fin 4 → ℝ} (hab : torusProj 4 L b = torusProj 4 L a) :
    torusProj 4 L (b - a) = 0 := by
  have e := torusProj_add L (b - a) a
  rw [sub_add_cancel, hab] at e
  exact add_eq_right.mp e.symm
def openCube (z : Fin 4 → ℝ) (ρ : ℝ) : Set (Fin 4 → ℝ) := {y | ∀ i, |y i - z i| < ρ}
theorem isOpen_openCube (z : Fin 4 → ℝ) (ρ : ℝ) : IsOpen (openCube z ρ) := by
  simp only [openCube, Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun i => isOpen_lt (by fun_prop) continuous_const
theorem openCube_subset_closedBall {z : Fin 4 → ℝ} {ρ : ℝ} (hρ : 0 < ρ) :
    openCube z ρ ⊆ Metric.closedBall z ρ := fun _ hy =>
  (dist_pi_le_iff hρ.le).2 fun i => by
    rw [Real.dist_eq]
    exact (hy i).le
structure PeriodicBoxFunction (L : ℝ) (z : Fin 4 → ℝ) (ρ : ℝ) (f : (Fin 4 → ℝ) → ℝ) : Prop where
  congr : ∀ a a', torusProj 4 L a = torusProj 4 L a' → f a = f a'
  vanish : ∀ a, f a ≠ 0 → ∃ a₀ ∈ openCube z (5 / 6 * ρ), torusProj 4 L a₀ = torusProj 4 L a
variable {L ρ : ℝ} {z : Fin 4 → ℝ} {f : (Fin 4 → ℝ) → ℝ}
theorem PeriodicBoxFunction.eq_comp_add (hf : PeriodicBoxFunction L z ρ f) {a b : Fin 4 → ℝ}
    (hab : torusProj 4 L b = torusProj 4 L a) : f = fun y => f ((b - a) + y) := by
  funext y
  apply hf.congr
  rw [torusProj_add, torusProj_sub_eq_zero hab, zero_add]
theorem PeriodicBoxFunction.mem_or_eventuallyEq_zero (hf : PeriodicBoxFunction L z ρ f) (hρ : 0 < ρ)
    (a : Fin 4 → ℝ) :
    (∃ b ∈ openCube z ρ, torusProj 4 L b = torusProj 4 L a) ∨ f =ᶠ[𝓝 a] 0 := by
  by_cases ha : ∃ b ∈ openCube z ρ, torusProj 4 L b = torusProj 4 L a
  · exact Or.inl ha
  right
  have hball : Metric.ball a (ρ / 6) ∈ 𝓝 a := Metric.ball_mem_nhds a (by positivity)
  filter_upwards [hball] with y hy
  by_contra hne
  obtain ⟨y₀, hy₀, hproj⟩ := hf.vanish y hne
  apply ha
  refine ⟨y₀ + (a - y), fun i => ?_, ?_⟩
  · have h₁ := hy₀ i
    have h₂ : |a i - y i| < ρ / 6 := by
      have h₃ : ‖a - y‖ < ρ / 6 := by
        rw [← dist_eq_norm, dist_comm]
        exact hy
      exact lt_of_le_of_lt (norm_le_pi_norm (a - y) i) h₃
    have e : (y₀ + (a - y)) i - z i = (y₀ i - z i) + (a i - y i) := by
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    rw [e]
    have h₄ := abs_add_le (y₀ i - z i) (a i - y i)
    linarith
  · rw [torusProj_add, hproj, ← torusProj_add, add_sub_cancel]
theorem PeriodicBoxFunction.iteratedFDeriv_mem_or_zero (hf : PeriodicBoxFunction L z ρ f) (hρ : 0 < ρ)
    (n : ℕ) (a : Fin 4 → ℝ) :
    (∃ b ∈ openCube z ρ, iteratedFDeriv ℝ n f a = iteratedFDeriv ℝ n f b) ∨
      iteratedFDeriv ℝ n f a = 0 := by
  rcases hf.mem_or_eventuallyEq_zero hρ a with ⟨b, hb, hab⟩ | h0
  · refine Or.inl ⟨b, hb, ?_⟩
    calc iteratedFDeriv ℝ n f a
        = iteratedFDeriv ℝ n (fun y => f ((b - a) + y)) a :=
          congrArg (fun u => iteratedFDeriv ℝ n u a) (hf.eq_comp_add hab)
      _ = iteratedFDeriv ℝ n f ((b - a) + a) := iteratedFDeriv_comp_add_left n _ _
      _ = iteratedFDeriv ℝ n f b := by rw [sub_add_cancel]
  · right
    have e := (Filter.EventuallyEq.iteratedFDeriv ℝ h0 n).eq_of_nhds
    simpa using e
section EqOnCube
variable {L₁ L₂ : ℝ} {u U : (Fin 4 → ℝ) → ℝ}
theorem iteratedFDeriv_eq_of_eqOn_openCube (heq : ∀ y ∈ openCube z ρ, U y = u y) (n : ℕ)
    {y : Fin 4 → ℝ} (hy : y ∈ openCube z ρ) : iteratedFDeriv ℝ n U y = iteratedFDeriv ℝ n u y := by
  have e : U =ᶠ[𝓝 y] u := Filter.eventually_of_mem ((isOpen_openCube z ρ).mem_nhds hy) heq
  exact (Filter.EventuallyEq.iteratedFDeriv ℝ e n).eq_of_nhds
theorem contDiff_of_eqOn (hU : PeriodicBoxFunction L₂ z ρ U) (hρ : 0 < ρ)
    (heq : ∀ y ∈ openCube z ρ, U y = u y) (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ U := by
  refine contDiff_iff_contDiffAt.2 fun a => ?_
  rcases hU.mem_or_eventuallyEq_zero hρ a with ⟨b, hb, hab⟩ | h0
  · have e : U =ᶠ[𝓝 b] u := Filter.eventually_of_mem ((isOpen_openCube z ρ).mem_nhds hb) heq
    have h₁ : ContDiffAt ℝ ∞ U b := hu.contDiffAt.congr_of_eventuallyEq e
    have h₂ : ContDiffAt ℝ ∞ U ((b - a) + a) := by rwa [sub_add_cancel]
    have h₃ : ContDiffAt ℝ ∞ (fun y : Fin 4 → ℝ => (b - a) + y) a :=
      (contDiff_const.add contDiff_id).contDiffAt
    rw [hU.eq_comp_add hab]
    exact ContDiffAt.comp a h₂ h₃
  · exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq h0
theorem bddAbove_iteratedFDeriv_of_contDiff (hu' : PeriodicBoxFunction L₁ z ρ u) (hρ : 0 < ρ)
    (hu : ContDiff ℝ ∞ u) (n : ℕ) (w : Fin n → Fin 4 → ℝ) :
    BddAbove (range fun y => |iteratedFDeriv ℝ n u y w|) := by
  have hcont : Continuous fun y => |iteratedFDeriv ℝ n u y w| := by
    have h₁ : Continuous fun y => iteratedFDeriv ℝ n u y :=
      hu.continuous_iteratedFDeriv (by exact_mod_cast le_top)
    exact ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Fin 4 → ℝ) ℝ w).continuous.comp
      h₁).abs
  obtain ⟨B, hB⟩ := (isCompact_closedBall z ρ).bddAbove_image hcont.continuousOn
  refine ⟨max B 0, ?_⟩
  rintro _ ⟨a, rfl⟩
  rcases hu'.iteratedFDeriv_mem_or_zero hρ n a with ⟨b, hb, hd⟩ | h0
  · show |iteratedFDeriv ℝ n u a w| ≤ _
    rw [hd]
    exact le_max_of_le_left (hB ⟨b, openCube_subset_closedBall hρ hb, rfl⟩)
  · show |iteratedFDeriv ℝ n u a w| ≤ _
    rw [h0]
    simp
theorem bddAbove_iteratedFDeriv_of_eqOn (hU : PeriodicBoxFunction L₂ z ρ U) (hρ : 0 < ρ)
    (heq : ∀ y ∈ openCube z ρ, U y = u y) (hu : ContDiff ℝ ∞ u) (n : ℕ)
    (w : Fin n → Fin 4 → ℝ) : BddAbove (range fun y => |iteratedFDeriv ℝ n U y w|) :=
  bddAbove_iteratedFDeriv_of_contDiff hU hρ (contDiff_of_eqOn hU hρ heq hu) n w
theorem iSup_iteratedFDeriv_eq (hu' : PeriodicBoxFunction L₁ z ρ u) (hU : PeriodicBoxFunction L₂ z ρ U)
    (hρ : 0 < ρ) (heq : ∀ y ∈ openCube z ρ, U y = u y) (hu : ContDiff ℝ ∞ u) (n : ℕ)
    (w : Fin n → Fin 4 → ℝ) :
    ⨆ y, |iteratedFDeriv ℝ n U y w| = ⨆ y, |iteratedFDeriv ℝ n u y w| := by
  have bu := bddAbove_iteratedFDeriv_of_contDiff hu' hρ hu n w
  have bU := bddAbove_iteratedFDeriv_of_eqOn hU hρ heq hu n w
  have nu : 0 ≤ ⨆ y, |iteratedFDeriv ℝ n u y w| := Real.iSup_nonneg fun _ => abs_nonneg _
  have nU : 0 ≤ ⨆ y, |iteratedFDeriv ℝ n U y w| := Real.iSup_nonneg fun _ => abs_nonneg _
  apply le_antisymm
  · refine ciSup_le fun a => ?_
    rcases hU.iteratedFDeriv_mem_or_zero hρ n a with ⟨b, hb, hd⟩ | h0
    · rw [hd, iteratedFDeriv_eq_of_eqOn_openCube heq n hb]
      exact le_ciSup bu b
    · rw [h0]
      simpa using nu
  · refine ciSup_le fun a => ?_
    rcases hu'.iteratedFDeriv_mem_or_zero hρ n a with ⟨b, hb, hd⟩ | h0
    · rw [hd, ← iteratedFDeriv_eq_of_eqOn_openCube heq n hb]
      exact le_ciSup bU b
    · rw [h0]
      simpa using nU
theorem abs_sub_le_lOne (hu' : PeriodicBoxFunction L₁ z ρ u) (hU : PeriodicBoxFunction L₂ z ρ U)
    (hρ : 0 < ρ) (heq : ∀ y ∈ openCube z ρ, U y = u y) (hu : ContDiff ℝ ∞ u) (a w : Fin 4 → ℝ) :
    |U (a + w) - U a| ≤
      (⨆ i : Fin 4, ⨆ y, |iteratedFDeriv ℝ 1 u y fun _ => Pi.single i 1|) * ∑ i, |w i| := by
  set C : ℝ := ⨆ i : Fin 4, ⨆ y, |iteratedFDeriv ℝ 1 u y fun _ => Pi.single i 1| with hC
  have hUs := contDiff_of_eqOn hU hρ heq hu
  have hdiff : Differentiable ℝ U := hUs.differentiable (by simp)
  have hpart : ∀ (y : Fin 4 → ℝ) (i : Fin 4),
      |fderiv ℝ U y (Pi.single i 1)| ≤ C := by
    intro y i
    have h₁ : |iteratedFDeriv ℝ 1 U y fun _ => Pi.single i 1| ≤
        ⨆ b, |iteratedFDeriv ℝ 1 U b fun _ => Pi.single i 1| :=
      le_ciSup (bddAbove_iteratedFDeriv_of_eqOn hU hρ heq hu 1 fun _ => Pi.single i 1) y
    rw [iSup_iteratedFDeriv_eq hu' hU hρ heq hu 1 fun _ => Pi.single i 1,
      iteratedFDeriv_one_apply] at h₁
    refine h₁.trans ?_
    exact le_ciSup (f := fun i : Fin 4 => ⨆ y, |iteratedFDeriv ℝ 1 u y fun _ => Pi.single i 1|)
      (Set.finite_range _).bddAbove i
  have hw : w = ∑ i, w i • (Pi.single i (1 : ℝ) : Fin 4 → ℝ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hbound : ∀ y : Fin 4 → ℝ, |fderiv ℝ U y w| ≤ C * ∑ i, |w i| := by
    intro y
    have e : fderiv ℝ U y w = ∑ i, w i * fderiv ℝ U y (Pi.single i 1) := by
      conv_lhs => rw [hw]
      simp [map_sum]
    rw [e, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hpart y i) (abs_nonneg _)
  have hline : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun s : ℝ => U (a + s • w))
      (fderiv ℝ U (a + s • w) w) (Icc (0 : ℝ) 1) s := by
    intro s _
    have h₁ : HasDerivAt (fun s : ℝ => a + s • w) w s := by
      simpa using ((hasDerivAt_id s).smul_const w).const_add a
    exact ((hdiff (a + s • w)).hasFDerivAt.comp_hasDerivAt s h₁).hasDerivWithinAt
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01' hline
    (fun s _ => by simpa [Real.norm_eq_abs] using hbound (a + s • w))
  simpa [Real.norm_eq_abs] using h
end EqOnCube
variable {R : NestedRegions} {N : ℕ}
theorem torusProj_liftedCentre (Q : LevelCube R N) : torusProj 4 R.side Q.liftedCentre = Q.centre := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.torusProj_liftedCentre <;> assumption
theorem le_mul_lOneNorm {L s C : ℝ} (hC : 0 ≤ C) (y : PeriodicTorus 4 L)
    (h : ∀ w : Fin 4 → ℝ, torusProj 4 L w = y → s ≤ C * ∑ i, |w i|) : s ≤ C * lOneNorm y := by
  obtain ⟨w₀, hw₀⟩ := torusProj_surjective L y
  have hne : {t | ∃ w : Fin 4 → ℝ, torusProj 4 L w = y ∧ t = ∑ i, |w i|}.Nonempty :=
    ⟨_, w₀, hw₀, rfl⟩
  rcases hC.eq_or_lt with h0 | hpos
  · have := h w₀ hw₀
    rw [← h0, zero_mul] at this
    rw [← h0, zero_mul]
    exact this
  · rw [← div_le_iff₀' hpos, lOneNorm]
    refine le_csInf hne ?_
    rintro _ ⟨w, hw, rfl⟩
    rw [div_le_iff₀' hpos]
    exact h w hw
theorem statement_holds (hM : FirstTypeMaps.Statement)
    (hW : PartitionFnSupportStatement) : Statement := by
  intro R K m N R₁ hs Q hQ φ hφ hg
  obtain ⟨⟨hadm, -⟩, hbij, -, hemb, hembij, -⟩ := hM R K m N R₁ hs Q hQ
  have hρ : 0 < cubeSide R N Q.level := by
    have h := hadm.side_pos
    unfold LevelCube.torusSide at h
    linarith
  have hsupp : ∀ x ∈ tsupport φ,
      ∃ a₀ ∈ openCube Q.liftedCentre (5 / 6 * cubeSide R N Q.level), torusProj 4 R.side a₀ = x := by
    intro x hx
    have h₁ : supNorm (x - Q.centre) < 5 / 6 * cubeSide R N Q.level :=
      (hW R K m N R₁ hs Q).2 (5 / 6) (by norm_num) (by norm_num) (hφ hx)
    obtain ⟨w₀, hw₀⟩ := torusProj_surjective R.side (x - Q.centre)
    have hne : {t | ∃ w : Fin 4 → ℝ, torusProj 4 R.side w = x - Q.centre ∧ t = ‖w‖}.Nonempty :=
      ⟨_, w₀, hw₀, rfl⟩
    obtain ⟨_, ⟨w, hw, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hne h₁
    refine ⟨Q.liftedCentre + w, fun i => ?_, ?_⟩
    · have e : (Q.liftedCentre + w) i - Q.liftedCentre i = w i := by simp
      rw [e]
      exact lt_of_le_of_lt (norm_le_pi_norm w i) hlt
    · rw [torusProj_add, torusProj_liftedCentre, hw, add_sub_cancel]
  have hsmall : openCube Q.liftedCentre (5 / 6 * cubeSide R N Q.level) ⊆
      openCube Q.liftedCentre (cubeSide R N Q.level) :=
    fun a ha i => (ha i).trans (by linarith)
  have hstrict : ∀ a ∈ openCube Q.liftedCentre (cubeSide R N Q.level),
      torusProj 4 R.side a ∈ Q.strictPts :=
    fun a ha => hbij.mapsTo ha
  have hsub : ∀ x ∈ tsupport φ, x ∈ Q.strictPts := by
    intro x hx
    obtain ⟨a₀, ha₀, rfl⟩ := hsupp x hx
    exact hstrict a₀ (hsmall ha₀)
  have heq : ∀ a ∈ openCube Q.liftedCentre (cubeSide R N Q.level),
      Q.system.transferFn φ (torusProj 4 Q.system.setting.side a) = φ (torusProj 4 R.side a) := by
    intro a ha
    have hone : ∀ x, x ∈ tsupport φ →
        Q.system.embed x = torusProj 4 Q.system.setting.side a → x = torusProj 4 R.side a := by
      intro x hx hxe
      exact hembij.injOn (hsub x hx) (hstrict a ha) (hxe.trans (hemb a ha).symm)
    unfold CubeSystem.transferFn
    by_cases hin : torusProj 4 R.side a ∈ tsupport φ
    · have e : {x : R.Point | x ∈ tsupport φ ∧
          Q.system.embed x = torusProj 4 Q.system.setting.side a} = {torusProj 4 R.side a} := by
        ext x
        constructor
        · rintro ⟨hx, hxe⟩
          exact hone x hx hxe
        · rintro rfl
          exact ⟨hin, hemb a ha⟩
      rw [e, finsum_mem_singleton]
    · have e : {x : R.Point | x ∈ tsupport φ ∧
          Q.system.embed x = torusProj 4 Q.system.setting.side a} = ∅ := by
        ext x
        constructor
        · rintro ⟨hx, hxe⟩
          exact absurd (hone x hx hxe ▸ hx) hin
        · exact fun h => h.elim
      rw [e, finsum_mem_empty, image_eq_zero_of_notMem_tsupport hin]
  have hu' : PeriodicBoxFunction R.side Q.liftedCentre (cubeSide R N Q.level)
      fun a => φ (torusProj 4 R.side a) :=
    ⟨fun a a' h => by simp only [h], fun a ha => hsupp _ (subset_tsupport φ ha)⟩
  have hU : PeriodicBoxFunction Q.system.setting.side Q.liftedCentre (cubeSide R N Q.level)
      fun a => Q.system.transferFn φ (torusProj 4 Q.system.setting.side a) := by
    refine ⟨fun a a' h => by simp only [h], fun a ha => ?_⟩
    have hne : {x : R.Point | x ∈ tsupport φ ∧
        Q.system.embed x = torusProj 4 Q.system.setting.side a}.Nonempty := by
      by_contra hemp
      apply ha
      unfold CubeSystem.transferFn
      rw [not_nonempty_iff_eq_empty.mp hemp, finsum_mem_empty]
    obtain ⟨x, hx, hxe⟩ := hne
    obtain ⟨a₀, ha₀, rfl⟩ := hsupp x hx
    exact ⟨a₀, ha₀, (hemb a₀ (hsmall ha₀)).symm.trans hxe⟩
  refine ⟨contDiff_of_eqOn hU hρ heq hg, fun n ν => iSup_iteratedFDeriv_eq hu' hU hρ heq hg n _,
    fun x x' => ?_⟩
  have hC : 0 ≤ ⨆ i : Fin 4, ⨆ a, |iteratedFDeriv ℝ 1 (fun a => φ (torusProj 4 R.side a)) a
      fun _ => Pi.single i 1| :=
    Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => abs_nonneg _
  refine le_mul_lOneNorm hC _ fun w hw => ?_
  obtain ⟨a, rfl⟩ := torusProj_surjective Q.system.setting.side x'
  have hx : x = torusProj 4 Q.system.setting.side (a + w) := by
    rw [torusProj_add, hw, add_sub_cancel]
  rw [hx]
  exact abs_sub_le_lOne hu' hU hρ heq hg a w
end PartitionCubes.TransferOfSmooth
end YangMills.Construction
