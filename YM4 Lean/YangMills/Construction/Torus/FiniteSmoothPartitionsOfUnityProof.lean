import YangMills.Construction.Torus.CoveringMapOpenAndCompactSetsAndDerivativesOfTuples
import YangMills.Construction.Torus.DistancesAndLiftsOfTorusOrFourSpace
import YangMills.Construction.Torus.FiniteSmoothPartitionsOfUnity
import YangMills.Construction.Torus.PeriodBoxModesCoefficientsAndPartialSums
import Mathlib
set_option autoImplicit false
open Set Filter Topology YangMills.Construction.TorusMetric
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
open scoped ENNReal ContDiff
noncomputable section
namespace YangMills.Construction.AmbientPoints.SmoothPartition
def bumpProfile (t : ℝ) : ℝ := Real.smoothTransition ((4 - t) / 3)
theorem bumpProfile_contDiff : ContDiff ℝ ∞ bumpProfile :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const 3)
theorem bumpProfile_mem (t : ℝ) : bumpProfile t ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
theorem bumpProfile_eq_one {t : ℝ} (ht : t ≤ 1) : bumpProfile t = 1 :=
  Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ (by norm_num)]; linarith)
theorem bumpProfile_eq_zero {t : ℝ} (ht : 4 ≤ t) : bumpProfile t = 0 :=
  Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (by linarith) (by norm_num))
variable {s : Conventions.StandingParameters} {E : Ambient}
def bump (s : Conventions.StandingParameters) (E : Ambient) (y : Pt s E) (r : ℝ) (y' : Pt s E) : ℝ :=
  bumpProfile (pointDist s E y' y ^ 2 / r ^ 2)
theorem bump_mem (y y' : Pt s E) (r : ℝ) : bump s E y r y' ∈ Icc (0 : ℝ) 1 :=
  bumpProfile_mem _
theorem bump_eq_one_of_le {y y' : Pt s E} {r : ℝ} (hr : 0 < r) (hle : pointDist s E y' y ≤ r) :
    bump s E y r y' = 1 := by
  have h0 : 0 ≤ pointDist s E y' y := dist_nonneg (x := y') (y := y)
  exact bumpProfile_eq_one ((div_le_one (by positivity)).2 (pow_le_pow_left₀ h0 hle 2))
theorem bump_eq_zero_of_le {y y' : Pt s E} {r : ℝ} (hr : 0 < r)
    (hle : 2 * r ≤ pointDist s E y' y) : bump s E y r y' = 0 := by
  refine bumpProfile_eq_zero ?_
  rw [le_div_iff₀ (by positivity)]
  have := pow_le_pow_left₀ (by positivity) hle 2
  nlinarith
theorem continuous_euclidNormVec_sub (x : Fin 4 → ℝ) :
    Continuous fun x' : Fin 4 → ℝ => euclidNormVec (x' - x) := by
  simp only [euclidNormVec, Pi.sub_apply]
  exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun μ _ =>
    ((continuous_apply μ).sub continuous_const).pow 2)
theorem contDiff_euclidNormVec_sub_sq (x : Fin 4 → ℝ) :
    ContDiff ℝ ∞ fun x' : Fin 4 → ℝ => euclidNormVec (x' - x) ^ 2 := by
  have hfun : (fun x' : Fin 4 → ℝ => euclidNormVec (x' - x) ^ 2) =
      fun x' => ∑ μ, (x' μ - x μ) ^ 2 := by
    funext x'
    simp only [euclidNormVec, Pi.sub_apply]
    exact Real.sq_sqrt (Finset.sum_nonneg fun μ _ => sq_nonneg _)
  rw [hfun]
  exact ContDiff.sum fun μ _ => ((contDiff_apply ℝ ℝ μ).sub contDiff_const).pow 2
theorem continuous_proj (H : DistanceFacts.MetricFacts s E) :
    Continuous (proj s E) := by
  refine continuous_iff_continuousAt.2 fun x => tendsto_iff_dist_tendsto_zero.2 ?_
  refine squeeze_zero (fun _ => dist_nonneg) (fun x' => H.pointDist_proj_le x' x) ?_
  have h := (continuous_euclidNormVec_sub x).tendsto x
  simpa [euclidNormVec] using h
theorem bump_comp_proj_contDiff (H : DistanceFacts.MetricFacts s E) (y : Pt s E) {r : ℝ}
    (hr : 0 < r) (hρ : ENNReal.ofReal (2 * r) < 2 * injRadius s E) :
    ContDiff ℝ ∞ (bump s E y r ∘ proj s E) := by
  have hcov := continuous_proj H
  have hc : Continuous fun u => pointDist s E (proj s E u) y :=
    hcov.dist continuous_const
  rw [contDiff_iff_contDiffAt]
  intro u₀
  by_cases hd : 2 * r < pointDist s E (proj s E u₀) y
  · have hev : ∀ᶠ u in 𝓝 u₀, 2 * r < pointDist s E (proj s E u) y :=
      (hc.tendsto u₀).eventually_const_lt hd
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hev] with u hu
    exact bump_eq_zero_of_le hr hu.le
  · obtain ⟨x₀, hx₀, hx⟩ := H.exists_lift_pointDist u₀ y
    have hx₀' : proj s E x₀ = y := hx₀
    have hlt : ENNReal.ofReal (euclidNormVec (u₀ - x₀)) < 2 * injRadius s E := by
      rw [hx]
      exact (ENNReal.ofReal_le_ofReal (not_lt.1 hd)).trans_lt hρ
    have hopen : IsOpen {u : Fin 4 → ℝ |
        ENNReal.ofReal (euclidNormVec (u - x₀)) < 2 * injRadius s E} :=
      isOpen_lt (ENNReal.continuous_ofReal.comp (continuous_euclidNormVec_sub x₀))
        continuous_const
    have hsm : ContDiff ℝ ∞ fun u : Fin 4 → ℝ => bumpProfile (euclidNormVec (u - x₀) ^ 2 / r ^ 2) :=
      bumpProfile_contDiff.comp ((contDiff_euclidNormVec_sub_sq x₀).div_const _)
    refine hsm.contDiffAt.congr_of_eventuallyEq ?_
    filter_upwards [hopen.mem_nhds hlt] with u hu
    have heq := H.pointDist_proj_eq u x₀ hu
    rw [hx₀'] at heq
    simp only [Function.comp_apply, bump, heq]
variable {p : ℕ}
def smoothFns (s : Conventions.StandingParameters) (E : Ambient) (p : ℕ) :
    Subalgebra ℝ (Tuple s E p → ℝ) where
  carrier := {f | ContDiff ℝ ∞ (f ∘ tupleProj s E p)}
  mul_mem' := fun {a b} (ha : ContDiff ℝ ∞ (a ∘ tupleProj s E p))
    (hb : ContDiff ℝ ∞ (b ∘ tupleProj s E p)) => ha.mul hb
  add_mem' := fun {a b} (ha : ContDiff ℝ ∞ (a ∘ tupleProj s E p))
    (hb : ContDiff ℝ ∞ (b ∘ tupleProj s E p)) => ha.add hb
  algebraMap_mem' := fun c =>
    (contDiff_const : ContDiff ℝ ∞ fun _ : Fin (4 * p) → ℝ => c)
theorem contDiff_flattenCoords_symm_apply (i : Fin p) :
    ContDiff ℝ ∞ fun x : Fin (4 * p) → ℝ => (flattenCoords p).symm x i := by
  refine contDiff_pi.2 fun μ => ?_
  exact contDiff_apply ℝ ℝ ((finProdFinEquiv.trans (finCongr (Nat.mul_comm p 4))) (i, μ))
def tupleBump (y : Tuple s E p) (r : ℝ) (y' : Tuple s E p) : ℝ :=
  ∏ i, bump s E (y i) r (y' i)
theorem tupleBump_mem_smoothFns (H : DistanceFacts.MetricFacts s E) (y : Tuple s E p) {r : ℝ}
    (hr : 0 < r) (hρ : ENNReal.ofReal (2 * r) < 2 * injRadius s E) :
    tupleBump y r ∈ smoothFns s E p := by
  change ContDiff ℝ ∞ fun x => ∏ i, bump s E (y i) r (tupleProj s E p x i)
  exact contDiff_prod fun i _ =>
    (bump_comp_proj_contDiff H (y i) hr hρ).comp (contDiff_flattenCoords_symm_apply i)
theorem tupleBump_mem (y y' : Tuple s E p) (r : ℝ) :
    tupleBump y r y' ∈ Icc (0 : ℝ) 1 :=
  ⟨Finset.prod_nonneg fun _ _ => (bump_mem _ _ _).1,
    Finset.prod_le_one (fun _ _ => (bump_mem _ _ _).1) fun _ _ => (bump_mem _ _ _).2⟩
theorem exists_radius_lt_injRadius (s : Conventions.StandingParameters) (E : Ambient) :
    ∃ c : ℝ, 0 < c ∧ ENNReal.ofReal (2 * c) < 2 * injRadius s E := by
  cases E with
  | torus =>
    have hL : 0 < s.L := by
      have := s.isAdmissible.2
      omega
    have hside : 0 < s.side := by
      simp only [Conventions.StandingParameters.side, PeriodicLattice.torusSide]
      positivity
    refine ⟨s.side / 8, by positivity, ?_⟩
    rw [two_mul_injRadius_torus, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    linarith
  | euclidean =>
    refine ⟨1, one_pos, ?_⟩
    rw [two_mul_injRadius_euclidean]
    exact ENNReal.ofReal_lt_top
theorem exists_bump (H : DistanceFacts.MetricFacts s E) (hB : TupleBallProps s E p)
    (y : Tuple s E p) (W : Set (Tuple s E p)) (hW : IsOpen W) (hy : y ∈ W) :
    ∃ ψ ∈ smoothFns s E p, (∀ z, ψ z ∈ Icc (0 : ℝ) 1) ∧
      ∃ U, IsOpen U ∧ y ∈ U ∧ (∀ z ∈ U, ψ z = 1) ∧
        ∃ C, IsCompact C ∧ C ⊆ W ∧ ∀ z, ψ z ≠ 0 → z ∈ C := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hW y hy
  obtain ⟨c, hc, hcρ⟩ := exists_radius_lt_injRadius s E
  set r := min c (ε / 4) with hrdef
  have hr : 0 < r := lt_min hc (by positivity)
  have hrc : r ≤ c := min_le_left _ _
  have hrε : r ≤ ε / 4 := min_le_right _ _
  have hρ : ENNReal.ofReal (2 * r) < 2 * injRadius s E :=
    (ENNReal.ofReal_le_ofReal (by linarith)).trans_lt hcρ
  refine ⟨tupleBump y r, tupleBump_mem_smoothFns H y hr hρ,
    fun z => tupleBump_mem y z r, Metric.ball y r, Metric.isOpen_ball,
    Metric.mem_ball_self hr, ?_, {y' | supDist y' y ≤ 2 * r},
    (hB.2 y (2 * r) (by positivity)).2.1, ?_, ?_⟩
  · intro z hz
    refine Finset.prod_eq_one fun i _ => bump_eq_one_of_le hr ?_
    exact (dist_le_pi_dist z y i).trans (Metric.mem_ball.1 hz).le
  · intro z hz
    refine hball (Metric.mem_ball.2 ?_)
    have hz' : supDist z y ≤ 2 * r := hz
    rw [dist_eq_supDist]
    linarith
  · intro z hz
    have hz' := Finset.prod_ne_zero_iff.1 hz
    change supDist z y ≤ 2 * r
    rw [← dist_eq_supDist]
    refine (dist_pi_le_iff (by positivity)).2 fun i => ?_
    by_contra hlt
    exact hz' i (Finset.mem_univ i) (bump_eq_zero_of_le hr (not_le.1 hlt).le)
theorem exists_telescoping_weights {T ι : Type*} {r : ℕ} (G : Subalgebra ℝ (T → ℝ))
    (a : ι → Fin r) (ψ : ι → T → ℝ) (hG : ∀ b, ψ b ∈ G)
    (h01 : ∀ b z, ψ b z ∈ Icc (0 : ℝ) 1) (t : Finset ι) :
    ∃ φ : Fin r → T → ℝ, (∀ c, φ c ∈ G) ∧ (∀ c z, 0 ≤ φ c z) ∧
      (∀ z, ∑ c, φ c z = 1 - ∏ b ∈ t, (1 - ψ b z)) ∧
      ∀ c z, φ c z ≠ 0 → ∃ b ∈ t, a b = c ∧ ψ b z ≠ 0 := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    exact ⟨0, fun _ => zero_mem _, fun _ _ => le_rfl, fun z => by simp, fun _ _ h => (h rfl).elim⟩
  | insert b t hb ih =>
    obtain ⟨φ, hφG, hφ0, hsum, hsupp⟩ := ih
    set w : T → ℝ := fun z => ψ b z * ∏ c ∈ t, (1 - ψ c z) with hw
    have hwG : w ∈ G := by
      have hweq : w = ψ b * ∏ c ∈ t, (1 - ψ c) := by
        funext z
        simp [hw, Finset.prod_apply]
      rw [hweq]
      exact mul_mem (hG b) (prod_mem fun c _ => sub_mem (one_mem _) (hG c))
    have hw0 : ∀ z, 0 ≤ w z := fun z =>
      mul_nonneg (h01 b z).1 (Finset.prod_nonneg fun c _ => sub_nonneg.2 (h01 c z).2)
    have hval : ∀ c z, (φ c + if c = a b then w else 0) z =
        φ c z + if c = a b then w z else 0 := by
      intro c z
      by_cases hcb : c = a b <;> simp [hcb]
    refine ⟨fun c => φ c + if c = a b then w else 0, ?_, ?_, ?_, ?_⟩
    · intro c
      refine add_mem (hφG c) ?_
      split_ifs
      · exact hwG
      · exact zero_mem _
    · intro c z
      beta_reduce
      rw [hval]
      refine add_nonneg (hφ0 c z) ?_
      split_ifs
      · exact hw0 z
      · exact le_rfl
    · intro z
      simp only [hval]
      rw [Finset.sum_add_distrib, hsum, Finset.sum_ite_eq' Finset.univ (a b) (fun _ => w z),
        if_pos (Finset.mem_univ _), Finset.prod_insert hb]
      simp only [hw]
      ring
    · intro c z hne
      beta_reduce at hne
      rw [hval] at hne
      by_cases h0 : φ c z = 0
      · rw [h0, zero_add] at hne
        split_ifs at hne with hc
        · exact ⟨b, Finset.mem_insert_self _ _, hc.symm, left_ne_zero_of_mul hne⟩
        · exact (hne rfl).elim
      · obtain ⟨b', hb', hab, hψ⟩ := hsupp c z h0
        exact ⟨b', Finset.mem_insert_of_mem hb', hab, hψ⟩
theorem exists_partition_of_bumps {T : Type*} [TopologicalSpace T] {r : ℕ}
    (G : Subalgebra ℝ (T → ℝ))
    (hloc : ∀ (y : T) (W : Set T), IsOpen W → y ∈ W →
      ∃ ψ ∈ G, (∀ z, ψ z ∈ Icc (0 : ℝ) 1) ∧ ∃ U, IsOpen U ∧ y ∈ U ∧ (∀ z ∈ U, ψ z = 1) ∧
        ∃ C, IsCompact C ∧ C ⊆ W ∧ ∀ z, ψ z ≠ 0 → z ∈ C)
    (hr : 1 ≤ r) (K : Set T) (hK : IsCompact K) (W : Fin r → Set T) (hW : ∀ a, IsOpen (W a))
    (hKW : K ⊆ ⋃ a, W a) :
    ∃ φ : Fin r → T → ℝ, (∀ a, φ a ∈ G) ∧ (∀ a z, φ a z ∈ Icc (0 : ℝ) 1) ∧
      (∀ a, ∃ C, IsCompact C ∧ C ⊆ W a ∧ ∀ z, φ a z ≠ 0 → z ∈ C) ∧
      ∃ O, IsOpen O ∧ K ⊆ O ∧ ∀ z ∈ O, ∑ a, φ a z = 1 := by
  classical
  have hpick : ∀ y : T, ∃ (a : Fin r) (ψ : T → ℝ) (U C : Set T), ψ ∈ G ∧
      (∀ z, ψ z ∈ Icc (0 : ℝ) 1) ∧ IsOpen U ∧ (y ∈ K → y ∈ U) ∧ (∀ z ∈ U, ψ z = 1) ∧
      IsCompact C ∧ C ⊆ W a ∧ ∀ z, ψ z ≠ 0 → z ∈ C := by
    intro y
    by_cases hy : y ∈ K
    · obtain ⟨a, ha⟩ := mem_iUnion.1 (hKW hy)
      obtain ⟨ψ, hψ, h01, U, hU, hyU, hU1, C, hC, hCW, hz⟩ := hloc y (W a) (hW a) ha
      exact ⟨a, ψ, U, C, hψ, h01, hU, fun _ => hyU, hU1, hC, hCW, hz⟩
    · refine ⟨⟨0, hr⟩, 0, ∅, ∅, zero_mem _, fun z => by simp, isOpen_empty,
        fun h => (hy h).elim, fun z hz => hz.elim, isCompact_empty, empty_subset _,
        fun z hz => (hz rfl).elim⟩
  choose a ψ U C hG h01 hUo hyU hU1 hCc hCW hC using hpick
  obtain ⟨t, -, hcov⟩ := hK.elim_nhds_subcover U fun y hy => (hUo y).mem_nhds (hyU y hy)
  obtain ⟨φ, hφG, hφ0, hsum, hsupp⟩ := exists_telescoping_weights G a ψ hG h01 t
  have hle : ∀ c z, φ c z ≤ 1 := by
    intro c z
    have h1 : φ c z ≤ ∑ c', φ c' z :=
      Finset.single_le_sum (f := fun c' => φ c' z) (fun c' _ => hφ0 c' z) (Finset.mem_univ c)
    have h2 : 0 ≤ ∏ b ∈ t, (1 - ψ b z) :=
      Finset.prod_nonneg fun b _ => sub_nonneg.2 (h01 b z).2
    rw [hsum] at h1
    linarith
  refine ⟨φ, hφG, fun c z => ⟨hφ0 c z, hle c z⟩, ?_, ⋃ b ∈ t, U b,
    isOpen_biUnion fun b _ => hUo b, hcov, ?_⟩
  · intro c
    refine ⟨⋃ b ∈ t.filter fun b => a b = c, C b,
      (t.filter fun b => a b = c).isCompact_biUnion fun b _ => hCc b, ?_, ?_⟩
    · refine iUnion₂_subset fun b hb => ?_
      have hab := (Finset.mem_filter.1 hb).2
      exact hab ▸ hCW b
    · intro z hz
      obtain ⟨b, hb, hab, hψ⟩ := hsupp c z hz
      exact mem_iUnion₂.2 ⟨b, Finset.mem_filter.2 ⟨hb, hab⟩, hC b z hψ⟩
  · intro z hz
    obtain ⟨b, hb, hzb⟩ := mem_iUnion₂.1 hz
    rw [hsum, Finset.prod_eq_zero hb (by rw [hU1 b z hzb, sub_self]), sub_zero]
theorem continuousPartialsUpTo_of_contDiff {D : ℕ} (n : ℕ) (F : (Fin D → ℝ) → ℂ)
    (hF : ContDiff ℝ ∞ F) : ContinuousPartialsUpTo univ n F := by apply _root_.YangMills.Construction.Torus.FourierBox.continuousPartialsUpTo_of_contDiff <;> assumption
theorem mem_testFns {f : Tuple s E p → ℝ} (hf : f ∈ smoothFns s E p)
    {C W : Set (Tuple s E p)} (hC : IsCompact C) (hCW : C ⊆ W) (hz : ∀ z, f z ≠ 0 → z ∈ C) :
    (fun z => (f z : ℂ)) ∈ testFns W := by
  have hsub : closedSupport (fun z => (f z : ℂ)) ⊆ C := by
    refine closure_minimal (fun z hne => hz z fun h => hne ?_) hC.isClosed
    simp [h]
  refine ⟨⟨isOpen_univ, fun n _ => continuousPartialsUpTo_of_contDiff n _ ?_⟩,
    hC.of_isClosed_subset isClosed_closure hsub, hsub.trans hCW⟩
  exact Complex.ofRealCLM.contDiff.comp hf
theorem smoothPartitionOfUnity_holds (h₁ : DistanceFacts.MetricFactsClaim)
    (h₂ : TupleTopology.Holds) : SmoothPartitionOfUnityStatement := by
  intro s E p hp
  have hloc := fun (y : Tuple s E p) (W : Set (Tuple s E p)) (hW : IsOpen W) (hy : y ∈ W) =>
    exists_bump (h₁ s E) ((h₂ s E).1 p hp).2.2.2.1 y W hW hy
  refine ⟨?_, ?_⟩
  · intro r hr K W hK hW hKW
    obtain ⟨φ, hφG, h01, hC, O, hO, hKO, hsum⟩ :=
      exists_partition_of_bumps (smoothFns s E p) hloc hr K hK W hW hKW
    refine ⟨fun a z => (φ a z : ℂ), fun a => ?_, fun a z => ⟨φ a z, h01 a z, rfl⟩, O,
      ⟨O, hO, hKO, Subset.rfl⟩, fun z hz => ?_⟩
    · obtain ⟨C, hCc, hCW, hz⟩ := hC a
      exact mem_testFns (hφG a) hCc hCW hz
    · rw [← Complex.ofReal_sum, hsum z hz, Complex.ofReal_one]
  · intro K W hK hW hKW
    obtain ⟨φ, hφG, h01, hC, O, hO, hKO, hsum⟩ :=
      exists_partition_of_bumps (r := 1) (smoothFns s E p) hloc le_rfl K hK (fun _ => W)
        (fun _ => hW) (fun z hz => mem_iUnion.2 ⟨0, hKW hz⟩)
    obtain ⟨C, hCc, hCW, hz⟩ := hC 0
    refine ⟨fun z => (φ 0 z : ℂ), mem_testFns (hφG 0) hCc hCW hz,
      fun z => ⟨φ 0 z, h01 0 z, rfl⟩, O, ⟨O, hO, hKO, Subset.rfl⟩, fun z hz' => ?_⟩
    have := hsum z hz'
    simp only [Fin.sum_univ_one] at this
    change ((φ 0 z : ℝ) : ℂ) = 1
    rw [this, Complex.ofReal_one]
end YangMills.Construction.AmbientPoints.SmoothPartition
