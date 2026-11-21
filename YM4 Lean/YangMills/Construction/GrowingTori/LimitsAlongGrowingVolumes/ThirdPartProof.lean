import YangMills.Construction.FamiliesOfLimits.ReflectionPositivityOnTuplesAtEveryCoordinateMirrorProof
import YangMills.Construction.SystemsWithFiveBounds.ListOfTheReconstructionOfALimitProof
import YangMills.Construction.GrowingTori.LimitsAlongGrowingVolumes.FirstPartProofForm
import YangMills.Construction.TotalDensitiesGiveASystem.ReconstructionOfAFamilyWithABoundProof
import Mathlib
set_option autoImplicit false
open Set
open scoped NNReal ENNReal ComplexConjugate
section
set_option autoImplicit false
open Set Filter Topology
open scoped NNReal ENNReal ComplexConjugate
noncomputable section
namespace YangMills.Construction.ToriLimits.GrowingVolumeLimits.ProofSteps.ReflectedLatticeFormula
open PeriodicSpace TorusTransport.TestFunctionOrders
open ReflectionSpaces (finiteUpperSequences)
open BallTuples (FnTuple R4Fun)
open TorusMetric (euclidNormVec)
open SourcesAndGluing (ballR4)
theorem euclidNormVec_add_le (x y : Fin 4 → ℝ) :
    euclidNormVec (x + y) ≤ euclidNormVec x + euclidNormVec y := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_add_le <;> assumption
theorem euclidNormVec_neg (x : Fin 4 → ℝ) : euclidNormVec (-x) = euclidNormVec x := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_neg <;> assumption
abbrev timeMirror (c : ℝ) : Equiv.Perm (Fin 4 → ℝ) := BallPeriodization.hyperplaneReflection 3 c
theorem timeMirror_apply_three (c : ℝ) (x : Fin 4 → ℝ) : timeMirror c x 3 = 2 * c - x 3 := by
  rw [BallPeriodization.hyperplaneReflection_apply]
  simp [PeriodicLattice.coordVec]
  ring
theorem timeMirror_apply_of_ne (c : ℝ) (x : Fin 4 → ℝ) {ν : Fin 4} (h : ν ≠ 3) :
    timeMirror c x ν = x ν := by
  rw [BallPeriodization.hyperplaneReflection_apply]
  simp [PeriodicLattice.coordVec, Pi.single_eq_of_ne h]
theorem timeMirror_timeMirror (c : ℝ) (x : Fin 4 → ℝ) : timeMirror c (timeMirror c x) = x := by
  funext ν
  by_cases h : ν = 3
  · subst h
    rw [timeMirror_apply_three, timeMirror_apply_three]
    ring
  · rw [timeMirror_apply_of_ne _ _ h, timeMirror_apply_of_ne _ _ h]
theorem continuous_timeMirror (c : ℝ) : Continuous (timeMirror c) := by
  have : (timeMirror c : (Fin 4 → ℝ) → Fin 4 → ℝ) =
      fun x => x - (2 * (x 3 - c)) • PeriodicLattice.coordVec 3 :=
    funext fun x => BallPeriodization.hyperplaneReflection_apply 3 c x
  rw [this]
  fun_prop
theorem contDiff_timeMirror (c : ℝ) : ContDiff ℝ 1 (timeMirror c) := by
  have : (timeMirror c : (Fin 4 → ℝ) → Fin 4 → ℝ) =
      fun x => x - (2 * (x 3 - c)) • PeriodicLattice.coordVec 3 :=
    funext fun x => BallPeriodization.hyperplaneReflection_apply 3 c x
  rw [this]
  fun_prop
def timeMirrorHomeomorph (c : ℝ) : (Fin 4 → ℝ) ≃ₜ (Fin 4 → ℝ) where
  toEquiv := timeMirror c
  continuous_toFun := continuous_timeMirror c
  continuous_invFun := by
    have : (timeMirror c).symm = timeMirror c := by
      ext x : 1
      rw [Equiv.symm_apply_eq, timeMirror_timeMirror]
    show Continuous (timeMirror c).symm
    rw [this]
    exact continuous_timeMirror c
theorem euclidNormVec_timeMirror_sub (c c' : ℝ) (x : Fin 4 → ℝ) :
    euclidNormVec (timeMirror c x - timeMirror c' x) = |2 * (c - c')| := by
  have h : timeMirror c x - timeMirror c' x = (2 * (c - c')) • PeriodicLattice.coordVec 3 := by
    funext ν
    by_cases hν : ν = 3
    · subst hν
      simp only [Pi.sub_apply, timeMirror_apply_three, Pi.smul_apply, smul_eq_mul]
      simp [PeriodicLattice.coordVec]
      ring
    · simp [timeMirror_apply_of_ne _ _ hν, PeriodicLattice.coordVec, Pi.single_eq_of_ne hν]
  rw [h]
  simp only [euclidNormVec, Fin.sum_univ_four]
  simp [PeriodicLattice.coordVec, Real.sqrt_sq_eq_abs]
theorem euclidNormVec_timeMirror_zero (x : Fin 4 → ℝ) :
    euclidNormVec (timeMirror 0 x) = euclidNormVec x := by
  simp only [euclidNormVec, Fin.sum_univ_four]
  rw [timeMirror_apply_three, timeMirror_apply_of_ne _ _ (by decide : (0 : Fin 4) ≠ 3),
    timeMirror_apply_of_ne _ _ (by decide : (1 : Fin 4) ≠ 3),
    timeMirror_apply_of_ne _ _ (by decide : (2 : Fin 4) ≠ 3)]
  congr 1
  ring
theorem fnSupport_eq_tsupport (f : R4Fun) : BallTuples.fnSupport f = tsupport f := rfl
theorem fnSupport_comp_timeMirror (c : ℝ) (f : R4Fun) :
    BallTuples.fnSupport (f ∘ timeMirror c) = timeMirror c '' BallTuples.fnSupport f := by
  have h : tsupport (f ∘ timeMirrorHomeomorph c) = timeMirrorHomeomorph c ⁻¹' tsupport f :=
    tsupport_comp_eq_preimage f (timeMirrorHomeomorph c)
  rw [fnSupport_eq_tsupport, fnSupport_eq_tsupport]
  have e : (f ∘ timeMirror c) = f ∘ timeMirrorHomeomorph c := rfl
  rw [e, h]
  ext x
  constructor
  · intro hx
    exact ⟨timeMirror c x, hx, timeMirror_timeMirror c x⟩
  · rintro ⟨y, hy, rfl⟩
    show timeMirror c (timeMirror c y) ∈ tsupport f
    rwa [timeMirror_timeMirror]
def SupportedAbove (c : ℝ) {k : ℕ} (X : FnTuple k) : Prop :=
  ∀ l, BallTuples.fnSupport (X l) ⊆ {x | c < x 3}
def mirrorAppend (c : ℝ) {k k' : ℕ} (X : FnTuple k) (Y : FnTuple k') : FnTuple (k + k') :=
  Fin.append (fun l => X l ∘ timeMirror c) Y
@[simp] theorem mirrorAppend_castAdd (c : ℝ) {k k' : ℕ} (X : FnTuple k) (Y : FnTuple k')
    (l : Fin k) : mirrorAppend c X Y (Fin.castAdd k' l) = X l ∘ timeMirror c :=
  Fin.append_left _ _ _
@[simp] theorem mirrorAppend_natAdd (c : ℝ) {k k' : ℕ} (X : FnTuple k) (Y : FnTuple k')
    (l : Fin k') : mirrorAppend c X Y (Fin.natAdd k l) = Y l :=
  Fin.append_right _ _ _
theorem fnSupport_comp_timeMirror_subset_below {c : ℝ} {f : R4Fun}
    (h : BallTuples.fnSupport f ⊆ {x | c < x 3}) :
    BallTuples.fnSupport (f ∘ timeMirror c) ⊆ {x | x 3 < c} := by
  rw [fnSupport_comp_timeMirror]
  rintro _ ⟨x, hx, rfl⟩
  have h₁ : c < x 3 := h hx
  show timeMirror c x 3 < c
  rw [timeMirror_apply_three]
  linarith
theorem isCompact_fnSupport_comp_timeMirror {c : ℝ} {f : R4Fun}
    (h : IsCompact (BallTuples.fnSupport f)) :
    IsCompact (BallTuples.fnSupport (f ∘ timeMirror c)) := by
  rw [fnSupport_comp_timeMirror]
  exact h.image (continuous_timeMirror c)
theorem disjoint_of_subset_below_above {c : ℝ} {A B : Set (Fin 4 → ℝ)} (hA : A ⊆ {x | x 3 < c})
    (hB : B ⊆ {x | c < x 3}) : Disjoint A B :=
  Set.disjoint_left.2 fun x ha hb => by
    have h₁ : x 3 < c := hA ha
    have h₂ : c < x 3 := hB hb
    exact lt_asymm h₁ h₂
theorem mirrorAppend_mem_sepC1Tuples (E : PeriodicSpace.Params) {c : ℝ} {k k' : ℕ} {X : FnTuple k}
    {Y : FnTuple k'} (hX : X ∈ Kind.sepC1Tuples E .euclidean k)
    (hY : Y ∈ Kind.sepC1Tuples E .euclidean k') (hXc : SupportedAbove c X)
    (hYc : SupportedAbove c Y) :
    mirrorAppend c X Y ∈ Kind.sepC1Tuples E .euclidean (k + k') := by
  obtain ⟨x₁, x₂, x₃⟩ := (BallTuples.mem_sepC1Tuples_euclidean_iff X).1 hX
  obtain ⟨y₁, y₂, y₃⟩ := (BallTuples.mem_sepC1Tuples_euclidean_iff Y).1 hY
  refine (BallTuples.mem_sepC1Tuples_euclidean_iff _).2 ⟨fun l => ?_, fun l => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) l
    · rw [mirrorAppend_castAdd]
      exact (x₁ i).comp (contDiff_timeMirror c)
    · rw [mirrorAppend_natAdd]
      exact y₁ i
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) l
    · rw [mirrorAppend_castAdd]
      exact isCompact_fnSupport_comp_timeMirror (x₂ i)
    · rw [mirrorAppend_natAdd]
      exact y₂ i
  · intro l l'
    refine Fin.addCases (fun i => ?_) (fun i => ?_) l <;>
      refine Fin.addCases (fun i' => ?_) (fun i' => ?_) l'
    · intro hne
      rw [mirrorAppend_castAdd, mirrorAppend_castAdd, fnSupport_comp_timeMirror,
        fnSupport_comp_timeMirror]
      have hi : i ≠ i' := fun e => hne (by rw [e])
      exact (Set.disjoint_image_iff (timeMirror c).injective).2 (x₃ i i' hi)
    · intro _
      rw [mirrorAppend_castAdd, mirrorAppend_natAdd]
      exact disjoint_of_subset_below_above (fnSupport_comp_timeMirror_subset_below (hXc i)) (hYc i')
    · intro _
      rw [mirrorAppend_castAdd, mirrorAppend_natAdd]
      exact (disjoint_of_subset_below_above (fnSupport_comp_timeMirror_subset_below (hXc i'))
        (hYc i)).symm
    · intro hne
      rw [mirrorAppend_natAdd, mirrorAppend_natAdd]
      have hi : i ≠ i' := fun e => hne (by rw [e])
      exact y₃ i i' hi
theorem exists_height_radius_of_isCompact {K : Set (Fin 4 → ℝ)} (hK : IsCompact K)
    (h : K ⊆ {x | 0 < x 3}) :
    ∃ δ R : ℝ, 0 < δ ∧ 0 < R ∧ ∀ x ∈ K, δ ≤ x 3 ∧ euclidNormVec x < R := by
  have hc : Continuous euclidNormVec := by
    unfold euclidNormVec
    fun_prop
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, 1, one_pos, one_pos, by simp⟩
  obtain ⟨y, hy, hmin⟩ := hK.exists_isMinOn hne (continuous_apply (3 : Fin 4)).continuousOn
  refine ⟨y 3, |B| + 1, h hy, by positivity, fun x hx => ⟨hmin hx, ?_⟩⟩
  have := hB x hx
  rw [Real.norm_eq_abs] at this
  have h₂ := le_abs_self (euclidNormVec x)
  have h₃ := le_abs_self B
  linarith
theorem isHalfSpaceEntry_eventually {f : R4Fun} (hK : IsCompact (BallTuples.fnSupport f))
    (h : BallTuples.fnSupport f ⊆ {x | 0 < x 3}) :
    ∃ δ R : ℝ, 0 < δ ∧ 0 < R ∧ ∀ c ρ : ℝ, 0 ≤ c → c < δ → R + 2 * c ≤ ρ →
      CentredTensorMoments.TorusFunctionals.IsHalfSpaceComponent ρ 3 c f := by
  obtain ⟨δ, R, hδ, hR, hx⟩ := exists_height_radius_of_isCompact hK h
  refine ⟨δ, R, hδ, hR, fun c ρ hc hcδ hρ => ⟨fun x hxK => ?_, ?_⟩⟩
  · obtain ⟨h₁, h₂⟩ := hx x hxK
    refine ⟨?_, ?_⟩
    · show SourcesAndGluing.euclidNorm x < ρ
      show euclidNormVec x < ρ
      linarith
    · show c < x 3
      linarith
  · have e : (f ∘ (BallPeriodization.hyperplaneReflection 3 c : Equiv.Perm (Fin 4 → ℝ))) =
        f ∘ timeMirror c := rfl
    rw [e, fnSupport_comp_timeMirror]
    rintro _ ⟨x, hxK, rfl⟩
    show euclidNormVec (timeMirror c x) < ρ
    have e₁ : timeMirror c x = (timeMirror c x - timeMirror 0 x) + timeMirror 0 x := by abel
    have h₁ := euclidNormVec_add_le (timeMirror c x - timeMirror 0 x) (timeMirror 0 x)
    rw [← e₁, euclidNormVec_timeMirror_sub, euclidNormVec_timeMirror_zero, sub_zero,
      abs_of_nonneg (by linarith)] at h₁
    have := (hx x hxK).2
    linarith
theorem sharpNormQ_toReal_le (E : PeriodicSpace.Params) {g : R4Fun}
    (hb : BddAbove (Set.range fun x => ‖g x‖)) :
    (Kind.sharpNormQ E .euclidean g).toReal ≤ TestFunctions.sharpNormR4 E.M g := by
  have hnn : 0 ≤ TestFunctions.sharpNormR4 E.M g := by
    refine le_trans ?_ (le_max_left _ _)
    exact Real.iSup_nonneg fun _ => norm_nonneg _
  refine ENNReal.toReal_le_of_le_ofReal hnn ?_
  refine max_le (iSup_le fun y => ENNReal.ofReal_le_ofReal ?_) (ENNReal.ofReal_le_ofReal ?_)
  · exact (le_ciSup hb y).trans (le_max_left _ _)
  · have e : Kind.lipConstQ E .euclidean g = TestFunctions.lipConstR4 g := by
      unfold Kind.lipConstQ TestFunctions.lipConstR4
      congr 1
      funext x y
      exact BallPeriodization.quotDist_euclidean E x y
    rw [e]
    exact le_max_right _ _
theorem sharpNormR4_zero (M : ℝ) :
    TestFunctions.sharpNormR4 M (0 : R4Fun) = 0 := by apply _root_.YangMills.DeltaSharedProofs.p501833 <;> assumption
def axisMirrorData (E : PeriodicSpace.Params) : ReflectionPositivity.AxisMirror.MirrorData :=
  ⟨BallTuples.cutoffOneParams E, 1, one_pos⟩
theorem mem_compactC1 (E : PeriodicSpace.Params) {f : R4Fun}
    (hf : ContDiff ℝ 1 f) (hc : IsCompact (BallTuples.fnSupport f)) :
    f ∈ ReflectionPositivity.AxisMirror.Ambient.compactC1 (axisMirrorData E) ℝ .euclidean := by
  refine ⟨hf, ?_⟩
  have e : ReflectionPositivity.AxisMirror.Ambient.closedSupport (axisMirrorData E) .euclidean f =
      BallTuples.fnSupport f :=
    (AmbientPoints.closure_eq_closureWrt
      (X := AmbientPoints.Pt (BallTuples.cutoffOneParams E) .euclidean)
      (Function.support f)).symm.trans
      (BallTuples.closure_pt_euclidean (BallTuples.cutoffOneParams E) _)
  rw [e]
  exact (AmbientPoints.isCompact_iff_isCompactWrt
    (X := AmbientPoints.Pt (BallTuples.cutoffOneParams E) .euclidean) _).1
    ((BallTuples.isCompact_pt_euclidean_iff (BallTuples.cutoffOneParams E) _).2 hc)
theorem timeMirror_eq_hyperplaneReflect (c : ℝ) :
    (timeMirror c : (Fin 4 → ℝ) → Fin 4 → ℝ) = TorusTransport.hyperplaneReflect 3 c :=
  funext fun x => by
    rw [BallPeriodization.hyperplaneReflection_apply, GrowingTori.hyperplaneReflect_eq_sub]
theorem sharpNormQ_mirror_sub_small (h : CitedFacts) (E : PeriodicSpace.Params) {f : R4Fun}
    (hf : ContDiff ℝ 1 f) (hc : IsCompact (BallTuples.fnSupport f)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ c : ℝ, 0 < c → c < δ →
      (Kind.sharpNormQ E .euclidean (f ∘ timeMirror c - f ∘ timeMirror 0)).toReal < ε := by
  let M : ReflectionPositivity.AxisMirror.Ambient.ScaleParam := ⟨E.M, E.one_le_M⟩
  let f' : ReflectionPositivity.AxisMirror.Ambient.compactC1 (axisMirrorData E) ℝ .euclidean :=
    ⟨f, mem_compactC1 E hf hc⟩
  obtain ⟨⟨-, hT⟩, -, -, hclose⟩ := (h.translations (axisMirrorData E) M).1 f'
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ≥0),
      ReflectionPositivity.AxisMirror.Ambient.smoothModulus M f' t < ε :=
    hT.eventually (gt_mem_nhds hε)
  obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hev
  have hu' : (0 : ℝ) < u := by exact_mod_cast hu
  refine ⟨(u : ℝ) / 2, half_pos hu', fun c hc₀ hcu => ?_⟩
  have hb : BddAbove (Set.range fun x => ‖(f ∘ timeMirror c - f ∘ timeMirror 0) x‖) := by
    obtain ⟨B, hB⟩ := hf.continuous.bounded_above_of_compact_support hc
    refine ⟨B + B, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (norm_sub_le _ _).trans (add_le_add (hB _) (hB _))
  refine (sharpNormQ_toReal_le E hb).trans_lt ?_
  have h₁ := hclose 3 0 c
  unfold ParallelReflectNormSharpBound at h₁
  have hmem : (2 * |c - 0|).toNNReal ∈ Set.Ioo (0 : ℝ≥0) u := by
    have e : |c - 0| = c := by rw [sub_zero, abs_of_pos hc₀]
    rw [e]
    refine ⟨Real.toNNReal_pos.2 (by positivity), ?_⟩
    rw [Real.toNNReal_lt_iff_lt_coe (by positivity)]
    linarith
  refine lt_of_le_of_lt ?_ (hsub hmem)
  rw [← timeMirror_eq_hyperplaneReflect, ← timeMirror_eq_hyperplaneReflect] at h₁
  exact h₁
def largeIn (J : Sequences.PNatIndexSet) : Filter ℕ+ := atTop ⊓ 𝓟 J.carrier
theorem largeIn_neBot (J : Sequences.PNatIndexSet) : (largeIn J).NeBot := by
  unfold largeIn
  refine Filter.inf_principal_neBot_iff.2 fun U hU => ?_
  obtain ⟨N, hN⟩ := mem_atTop_sets.1 hU
  obtain ⟨j, hj, hlt⟩ := J.infinite.exists_gt N
  exact ⟨j, hN j hlt.le, hj⟩
theorem eventually_largeIn_of_eventuallyAlong {J : Sequences.PNatIndexSet} {P : ℕ+ → Prop}
    (h : DiagonalLimits.EventuallyAlong J P) : ∀ᶠ j in largeIn J, P j := by
  obtain ⟨j', hj'⟩ := h
  unfold largeIn
  rw [eventually_inf_principal]
  filter_upwards [eventually_ge_atTop (⟨j'.toNat + 1, by omega⟩ : ℕ+)] with j hj hjJ
  refine hj' j hjJ ?_
  have h₁ : j'.toNat + 1 ≤ (j : ℕ) := hj
  omega
theorem eventuallyAlong_of_eventually_largeIn {J : Sequences.PNatIndexSet} {P : ℕ+ → Prop}
    (h : ∀ᶠ j in largeIn J, P j) : DiagonalLimits.EventuallyAlong J P := by
  unfold largeIn at h
  rw [eventually_inf_principal] at h
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  refine ⟨((N : ℕ) : ℤ), fun j hj hle => hN j ?_ hj⟩
  have : (N : ℕ) ≤ (j : ℕ) := by exact_mod_cast hle
  exact this
theorem eventually_largeIn_of_atTop {J : Sequences.PNatIndexSet} {P : ℕ+ → Prop}
    (h : ∀ᶠ j in atTop, P j) : ∀ᶠ j in largeIn J, P j :=
  h.filter_mono inf_le_left
theorem tendsto_largeIn_of_tendsToWhereDefined {J : Sequences.PNatIndexSet} {P : ℕ+ → Prop}
    {x : ℕ+ → ℂ} {z : ℂ} (h : DiagonalLimits.TendsToWhereDefined J P (fun j _ => x j) z) :
    Tendsto x (largeIn J) (𝓝 z) := by
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  filter_upwards [eventually_largeIn_of_eventuallyAlong (h ε hε)] with j hj
  obtain ⟨-, hlt⟩ := hj
  rwa [dist_eq_norm]
variable {D : Setup}
theorem spacing_pos (S : ToriSequence D) (j : ℕ+) : 0 < S.spacing j := by
  have hL : (0 : ℝ) < D.L := by
    exact_mod_cast (by have := D.one_lt_L; omega : 0 < D.L)
  unfold ToriSequence.spacing PeriodicLattice.meshSize
  exact zpow_pos hL _
theorem tendsto_spacing_zero (S : ToriSequence D) : Tendsto S.spacing atTop (𝓝 0) := by
  have hL : (1 : ℝ) < D.L := by exact_mod_cast D.one_lt_L
  have h₁ : Tendsto (fun n : ℕ => ((D.L : ℝ)⁻¹) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.2 (by linarith)) (inv_lt_one_of_one_lt₀ hL)
  refine (h₁.comp S.K_tendsto).congr fun j => ?_
  simp [ToriSequence.spacing, PeriodicLattice.meshSize, zpow_neg]
theorem exists_pos_separation {n : ℕ} (K : Fin n → Set (Fin 4 → ℝ)) (hK : ∀ l, IsCompact (K l))
    (hd : ∀ l l', l ≠ l' → Disjoint (K l) (K l')) :
    ∃ d : ℝ, 0 < d ∧ ∀ l l', l ≠ l' → ∀ x ∈ K l, ∀ y ∈ K l', d ≤ euclidNormVec (x - y) := by apply _root_.YangMills.SharedProofs.p33435 <;> assumption
theorem exists_pos_radius {n : ℕ} (K : Fin n → Set (Fin 4 → ℝ)) (hK : ∀ l, IsCompact (K l)) :
    ∃ R : ℝ, 0 < R ∧ ∀ l, ∀ x ∈ K l, euclidNormVec x ≤ R := by apply _root_.YangMills.SharedProofs.p71691 <;> assumption
theorem mem_c1SupportedIn_of (h : CitedFacts) (E : PeriodicSpace.Params) {f : R4Fun}
    {A : Set (Fin 4 → ℝ)} (hf : ContDiff ℝ 1 f) (hc : IsCompact (BallTuples.fnSupport f))
    (hs : BallTuples.fnSupport f ⊆ A) : f ∈ Kind.c1SupportedIn E .euclidean A := by
  obtain ⟨-, -, -, -, hW, -⟩ := h.collars
  refine ⟨((hW E).1.2.2.2.1 f).2 hf, ?_, ?_⟩
  · rw [BallTuples.supportQ_euclidean]
    exact (BallTuples.isCompactQ_euclidean_iff E _).2 hc
  · rw [BallTuples.supportQ_euclidean]
    exact hs
def euclidThickening (K : Set (Fin 4 → ℝ)) (d : ℝ) : Set (Fin 4 → ℝ) :=
  {x | ∃ y ∈ K, euclidNormVec (x - y) ≤ d}
theorem setsInBallsSeparated_euclidThickening (h : CitedFacts) (E : PeriodicSpace.Params) {n : ℕ}
    {K : Fin n → Set (Fin 4 → ℝ)} {d R : ℝ} (hd : 0 < d) (hR : 0 < R)
    (hsep : ∀ l l', l ≠ l' → ∀ x ∈ K l, ∀ y ∈ K l', 3 * d ≤ euclidNormVec (x - y))
    (hrad : ∀ l, ∀ x ∈ K l, euclidNormVec x ≤ R) :
    Kind.SetsInBallsSeparated E .euclidean d (R + d) (fun l => euclidThickening (K l) d) := by
  obtain ⟨-, -, -, -, hW, -⟩ := h.collars
  obtain ⟨hW₁, hW₂, -⟩ := hW E
  have hRd : 0 < R + d := by linarith
  refine ⟨fun l => ⟨Kind.closedBallAbout E .euclidean 0 (R + d), ⟨hRd, 0, rfl⟩, ?_⟩,
    fun l l' hne => ?_⟩
  · have hsub : ∀ x : Fin 4 → ℝ, x ∈ euclidThickening (K l) d →
        euclidNormVec (x - 0) ≤ R + d := by
      rintro x ⟨y, hy, hxy⟩
      have e : x - 0 = (x - y) + y := by abel
      rw [e]
      exact (euclidNormVec_add_le _ _).trans (by linarith [hrad l y hy])
    exact fun x hx => (Set.ext_iff.1 (hW₂.1 0 (R + d) hRd) x).2 (hsub x hx)
  · rw [hW₁.2.1]
    refine le_iInf₂ fun a ha => le_iInf₂ fun b hb => ENNReal.ofReal_le_ofReal ?_
    obtain ⟨y, hy, hay⟩ := ha
    obtain ⟨y', hy', hby⟩ := hb
    have h₁ := hsep l l' hne y hy y' hy'
    have e : y - y' = (-(a - y)) + ((a - b) + (b - y')) := by abel
    have h₂ := euclidNormVec_add_le (-(a - y)) ((a - b) + (b - y'))
    have h₃ := euclidNormVec_add_le (a - b) (b - y')
    rw [← e, euclidNormVec_neg] at h₂
    linarith
theorem tendsto_centredSchwinger_mirrorAppend (h : CitedFacts) (S : ToriSequence D)
    {J : Sequences.PNatIndexSet} {Ξ : D.LimitHierarchy} (hM : CentredMomentsConverge S J Ξ)
    {k k' : ℕ} {X : FnTuple k} {Y : FnTuple k'} (hX : X ∈ D.sepDomain k) (hY : Y ∈ D.sepDomain k')
    (hX₀ : SupportedAbove 0 X) (hY₀ : SupportedAbove 0 Y) :
    Tendsto (fun j => S.centred j (mirrorAppend (S.spacing j / 2) X Y)) (largeIn J)
      (𝓝 ((Ξ.partitionMoment ⟨mirrorAppend 0 X Y,
        mirrorAppend_mem_sepC1Tuples D.euclidParams hX hY hX₀ hY₀⟩ : ℝ) : ℂ)) := by
  have hZ₀ := mirrorAppend_mem_sepC1Tuples D.euclidParams hX hY hX₀ hY₀
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have e : ∀ c : ℝ, mirrorAppend c X Y = mirrorAppend 0 X Y := fun c => by
      funext l
      refine Fin.addCases (fun i => i.elim0) (fun i => ?_) l
      rw [mirrorAppend_natAdd, mirrorAppend_natAdd]
    simp only [e]
    exact tendsto_largeIn_of_tendsToWhereDefined (hM.atFixed _ ⟨_, hZ₀⟩)
  set E := D.euclidParams with hE
  have hq : 1 ≤ k + k' := by omega
  set Z₀ := mirrorAppend 0 X Y with hZ₀def
  obtain ⟨z₁, z₂, z₃⟩ := (BallTuples.mem_sepC1Tuples_euclidean_iff Z₀).1 hZ₀
  obtain ⟨x₁, x₂, -⟩ := (BallTuples.mem_sepC1Tuples_euclidean_iff X).1 hX
  obtain ⟨y₁, y₂, -⟩ := (BallTuples.mem_sepC1Tuples_euclidean_iff Y).1 hY
  obtain ⟨d₀, hd₀, hsep₀⟩ := exists_pos_separation (fun l => BallTuples.fnSupport (Z₀ l)) z₂ z₃
  obtain ⟨R, hR, hrad⟩ := exists_pos_radius (fun l => BallTuples.fnSupport (Z₀ l)) z₂
  set d := d₀ / 3 with hd
  have hdpos : 0 < d := by positivity
  have hsep : ∀ l l', l ≠ l' → ∀ x ∈ BallTuples.fnSupport (Z₀ l),
      ∀ y ∈ BallTuples.fnSupport (Z₀ l'), 3 * d ≤ euclidNormVec (x - y) :=
    fun l l' hne x hx y hy => by
      have := hsep₀ l l' hne x hx y hy
      rw [hd]
      linarith
  have hA := setsInBallsSeparated_euclidThickening h E hdpos hR hsep hrad
  let H : ℕ+ → FnTuple (k + k') := fun j =>
    if S.spacing j ≤ d then mirrorAppend (S.spacing j / 2) X Y else Z₀
  have hZc : ∀ c : ℝ, |2 * c| ≤ d → ∀ l, mirrorAppend c X Y l ∈
      Kind.c1SupportedIn E .euclidean (euclidThickening (BallTuples.fnSupport (Z₀ l)) d) := by
    intro c hc l
    refine Fin.addCases (fun i => ?_) (fun i => ?_) l
    · rw [mirrorAppend_castAdd]
      refine mem_c1SupportedIn_of h E ((x₁ i).comp (contDiff_timeMirror c))
        (isCompact_fnSupport_comp_timeMirror (x₂ i)) ?_
      rw [fnSupport_comp_timeMirror]
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨timeMirror 0 x, ?_, ?_⟩
      · rw [hZ₀def, mirrorAppend_castAdd, fnSupport_comp_timeMirror]
        exact ⟨x, hx, rfl⟩
      · rw [euclidNormVec_timeMirror_sub, sub_zero]
        exact hc
    · rw [mirrorAppend_natAdd]
      refine mem_c1SupportedIn_of h E (y₁ i) (y₂ i) ?_
      intro x hx
      refine ⟨x, ?_, ?_⟩
      · rw [hZ₀def, mirrorAppend_natAdd]
        exact hx
      · rw [sub_self]
        simp [euclidNormVec, hdpos.le]
  have hZ₀c : ∀ l, Z₀ l ∈
      Kind.c1SupportedIn E .euclidean (euclidThickening (BallTuples.fnSupport (Z₀ l)) d) :=
    hZc 0 (by simpa using hdpos.le)
  have hH : ∀ j, H j ∈ Kind.productSet E .euclidean
      (fun l => Kind.c1SupportedIn E .euclidean (euclidThickening (BallTuples.fnSupport (Z₀ l)) d)) := by
    intro j l _
    by_cases hj : S.spacing j ≤ d
    · have : H j = mirrorAppend (S.spacing j / 2) X Y := if_pos hj
      rw [this]
      refine hZc _ ?_ l
      have e : 2 * (S.spacing j / 2) = S.spacing j := by ring
      rw [e, abs_of_pos (spacing_pos S j)]
      exact hj
    · have : H j = Z₀ := if_neg hj
      rw [this]
      exact hZ₀c l
  have hsmall : ∀ᶠ j in atTop, S.spacing j ≤ d :=
    (tendsto_spacing_zero S).eventually (Iic_mem_nhds hdpos)
  have hsharp : ∀ l, ∀ ε : ℝ, 0 < ε → DiagonalLimits.EventuallyAlong J fun j =>
      (Kind.sharpNormQ E .euclidean (H j l - Z₀ l)).toReal < ε := by
    intro l ε hε
    refine eventuallyAlong_of_eventually_largeIn (eventually_largeIn_of_atTop ?_)
    refine Fin.addCases (fun i => ?_) (fun i => ?_) l
    · obtain ⟨δ, hδ, hlt⟩ := sharpNormQ_mirror_sub_small h E (x₁ i) (x₂ i) hε
      have hδ' : ∀ᶠ j in atTop, S.spacing j / 2 < δ := by
        have := (tendsto_spacing_zero S).div_const (2 : ℝ)
        rw [zero_div] at this
        exact this.eventually (gt_mem_nhds hδ)
      filter_upwards [hsmall, hδ'] with j hj₁ hj₂
      have e₁ : H j = mirrorAppend (S.spacing j / 2) X Y := if_pos hj₁
      rw [e₁, hZ₀def, mirrorAppend_castAdd, mirrorAppend_castAdd]
      exact hlt _ (half_pos (spacing_pos S j)) hj₂
    · refine Eventually.of_forall fun j => ?_
      have e₁ : H j (Fin.natAdd k i) = Z₀ (Fin.natAdd k i) := by
        by_cases hj : S.spacing j ≤ d
        · have : H j = mirrorAppend (S.spacing j / 2) X Y := if_pos hj
          rw [this, hZ₀def, mirrorAppend_natAdd, mirrorAppend_natAdd]
        · have : H j = Z₀ := if_neg hj
          rw [this]
      rw [e₁, sub_self]
      refine lt_of_le_of_lt (sharpNormQ_toReal_le E ?_) ?_
      · exact ⟨0, by rintro _ ⟨x, rfl⟩; simp⟩
      · rw [sharpNormR4_zero]
        exact hε
  have hconv := hM.atMoving (k + k') hq d (R + d) hdpos (by linarith)
    (fun l => euclidThickening (BallTuples.fnSupport (Z₀ l)) d) hA ⟨Z₀, hZ₀⟩ H
    (fun l _ => hZ₀c l) hH hsharp
  have hlim := tendsto_largeIn_of_tendsToWhereDefined hconv
  refine hlim.congr' ?_
  filter_upwards [eventually_largeIn_of_atTop hsmall] with j hj
  have : H j = mirrorAppend (S.spacing j / 2) X Y := if_pos hj
  rw [this]
open CentredTensorMoments (realTupleTensor conjReflectTest)
open CentredTensorMoments.TorusFunctionals (linComb)
def IsUpperCombination (E : PeriodicSpace.Params) {q n : ℕ} (F : OrderedTestFun q)
    (a : Fin n → ℂ) (X : Fin n → FnTuple q) : Prop :=
  (∀ b, X b ∈ Kind.sepC1Tuples E .euclidean q) ∧ (∀ b, SupportedAbove 0 (X b)) ∧
    F = linComb a fun b => realTupleTensor (X b)
theorem exists_isUpperCombination (E : PeriodicSpace.Params) {q : ℕ} {F : OrderedTestFun q}
    (hF : F ∈ ReflectionSpaces.sepTensorsUpper E q) :
    ∃ (n : ℕ) (a : Fin n → ℂ) (X : Fin n → FnTuple q), IsUpperCombination E F a X := by
  cases q with
  | zero =>
    refine ⟨1, fun _ => F, fun _ l => l.elim0, fun _ => ?_, fun _ l => l.elim0, ?_⟩
    · exact (BallTuples.mem_sepC1Tuples_euclidean_iff _).2
        ⟨fun l => l.elim0, fun l => l.elim0, fun l => l.elim0⟩
    · show F = ∑ b : Fin 1, F * (1 : ℂ)
      simp
  | succ q =>
    have hF' : (F : (Fin (q + 1) → Kind.euclidean.Pt E) → ℂ) ∈ sepTensorSpanOn E (q + 1)
        (ReflectionSpaces.upperHalfOpen : Set (Fin 4 → ℝ)) := hF
    obtain ⟨n, a, g, hg⟩ := (Submodule.mem_span_set'
      (M := (Fin (q + 1) → Kind.euclidean.Pt E) → ℂ)).1 hF'
    have hch : ∀ i, ∃ f ∈ Kind.sepC1TuplesWithin E Kind.euclidean (q + 1)
        (ReflectionSpaces.upperHalfOpen : Set (Fin 4 → ℝ)),
        (g i).1 = Kind.tensorFn E Kind.euclidean fun i y => ((f i y : ℝ) : ℂ) := fun i => (g i).2
    choose X hX hXg using hch
    refine ⟨n, a, X, fun b => (hX b).1, fun b l => ?_, ?_⟩
    · have h₁ := (hX b).2 l
      have e : Kind.supportQ E .euclidean (X b l) = BallTuples.fnSupport (X b l) :=
        BallTuples.supportQ_euclidean E _
      exact fun x hx => h₁ (by rw [e]; exact hx)
    · funext x
      have hg' : (F : (Fin (q + 1) → Kind.euclidean.Pt E) → ℂ) = ∑ i, a i • (g i).1 := hg.symm
      have h₂ : ∀ x' : Fin (q + 1) → Kind.euclidean.Pt E,
          (F : (Fin (q + 1) → Kind.euclidean.Pt E) → ℂ) x' =
            ∑ i, a i * Kind.tensorFn E Kind.euclidean (fun l y => ((X i l y : ℝ) : ℂ)) x' := by
        intro x'
        rw [hg', Finset.sum_apply]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Pi.smul_apply, hXg, smul_eq_mul]
      exact h₂ x
theorem conjReflectTest_linComb (c : ℝ) {q n : ℕ} (a : Fin n → ℂ) (X : Fin n → FnTuple q) :
    conjReflectTest 3 c (linComb a fun b => realTupleTensor (X b)) =
      linComb (fun b => conj (a b))
        fun b => realTupleTensor (fun l => X b l ∘ timeMirror c) := by
  cases q with
  | zero =>
    show conj (∑ b, a b * (1 : ℂ)) = ∑ b, conj (a b) * (1 : ℂ)
    simp
  | succ q =>
    funext x
    show conj (∑ b, a b * ∏ i, ((X b i (timeMirror c (x i)) : ℝ) : ℂ)) =
      ∑ b, conj (a b) * ∏ i, (((X b i ∘ timeMirror c) (x i) : ℝ) : ℂ)
    simp [map_sum, map_mul, map_prod]
theorem prod_finAppend {k k' : ℕ} (A : FnTuple k) (B : FnTuple k') (x : Configuration (k + k')) :
    ∏ l, ((Fin.append A B l (x l) : ℝ) : ℂ) =
      (∏ i, ((A i (initPoints x i) : ℝ) : ℂ)) * ∏ i, ((B i (tailPoints x i) : ℝ) : ℂ) := by
  rw [Fin.prod_univ_add]
  simp [initPoints, tailPoints]
theorem sum_finProd_mul {n n' : ℕ} (f : Fin n → ℂ) (g : Fin n' → ℂ) :
    ∑ i : Fin (n * n'), f (finProdFinEquiv.symm i).1 * g (finProdFinEquiv.symm i).2 =
      (∑ b, f b) * ∑ b, g b := by
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  exact Equiv.sum_comp finProdFinEquiv.symm fun p : Fin n × Fin n' => f p.1 * g p.2
theorem sigma_succ_ext {n m : ℕ} (h : n = m) (G : OrderedTestFun (n + 1))
    (G' : OrderedTestFun (m + 1))
    (hG : ∀ x : Configuration (m + 1), G' x = G fun i => x (Fin.cast (by omega) i)) :
    (⟨n + 1, G⟩ : GradedTestFun) = ⟨m + 1, G'⟩ := by
  subst h
  congr 1
  funext x
  exact (hG x).symm
theorem gradedTensor_linComb {k k' n n' : ℕ} (a : Fin n → ℂ) (a' : Fin n' → ℂ)
    (A : Fin n → FnTuple k) (B : Fin n' → FnTuple k') :
    gradedTensor ⟨k, linComb a fun b => realTupleTensor (A b)⟩
        ⟨k', linComb a' fun b => realTupleTensor (B b)⟩ =
      ⟨k + k', linComb
        (fun i : Fin (n * n') => a (finProdFinEquiv.symm i).1 * a' (finProdFinEquiv.symm i).2)
        fun i => realTupleTensor
          (Fin.append (A (finProdFinEquiv.symm i).1) (B (finProdFinEquiv.symm i).2))⟩ := by
  cases k with
  | zero =>
    cases k' with
    | zero =>
      show (⟨0, (∑ b, a b * (1 : ℂ)) * ∑ b, a' b * (1 : ℂ)⟩ : GradedTestFun) =
        ⟨0, ∑ i : Fin (n * n'), a (finProdFinEquiv.symm i).1 * a' (finProdFinEquiv.symm i).2 *
          (1 : ℂ)⟩
      congr 1
      simp only [mul_one]
      exact (sum_finProd_mul a a').symm
    | succ r =>
      refine sigma_succ_ext (Nat.zero_add r).symm _ _ fun x => ?_
      show ∑ i : Fin (n * n'), a (finProdFinEquiv.symm i).1 * a' (finProdFinEquiv.symm i).2 *
          ∏ l, ((Fin.append (A (finProdFinEquiv.symm i).1) (B (finProdFinEquiv.symm i).2) l
            (x l) : ℝ) : ℂ) =
        (∑ b, a b * (1 : ℂ)) * ∑ b, a' b * ∏ l, ((B b l (x (Fin.cast (by omega) l)) : ℝ) : ℂ)
      simp only [prod_finAppend (k := 0), Finset.univ_eq_empty, Finset.prod_empty, one_mul,
        mul_one]
      rw [← sum_finProd_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_assoc]
      have e : ∀ l, tailPoints (p := 0) (q := r + 1) x l = x (Fin.cast (by omega) l) :=
        fun l => congrArg x (Fin.ext (by simp))
      simp only [e]
  | succ p =>
    cases k' with
    | zero =>
      show (⟨p + 1, fun x => (∑ b, a' b * (1 : ℂ)) * ∑ b, a b * ∏ l, ((A b l (x l) : ℝ) : ℂ)⟩ :
          GradedTestFun) =
        ⟨p + 1, fun x => ∑ i : Fin (n * n'),
          a (finProdFinEquiv.symm i).1 * a' (finProdFinEquiv.symm i).2 *
          ∏ l, ((Fin.append (A (finProdFinEquiv.symm i).1) (B (finProdFinEquiv.symm i).2) l
            (x l) : ℝ) : ℂ)⟩
      congr 1
      funext x
      simp only [prod_finAppend (k' := 0), Finset.univ_eq_empty, Finset.prod_empty, mul_one]
      rw [mul_comm, ← sum_finProd_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      have e : ∀ l, initPoints (p := p + 1) (q := 0) x l = x l := fun _ => rfl
      simp only [e]
      ring
    | succ r =>
      show (⟨p + 1 + (r + 1), tensor (p := p + 1) (q := r + 1) _ _⟩ :
        GradedTestFun) = ⟨p + 1 + (r + 1), _⟩
      congr 1
      funext x
      show (∑ b, a b * ∏ l, ((A b l (initPoints x l) : ℝ) : ℂ)) *
          ∑ b, a' b * ∏ l, ((B b l (tailPoints x l) : ℝ) : ℂ) =
        ∑ i : Fin (n * n'), a (finProdFinEquiv.symm i).1 * a' (finProdFinEquiv.symm i).2 *
          ∏ l, ((Fin.append (A (finProdFinEquiv.symm i).1) (B (finProdFinEquiv.symm i).2) l
            (x l) : ℝ) : ℂ)
      rw [← sum_finProd_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [prod_finAppend]
      ring
open CentredTensorMoments (realTupleTensor conjReflectTest)
open CentredTensorMoments.TorusFunctionals (linComb IsHalfSpaceComponent IsHalfSpaceCombination)
variable {D : Setup}
theorem realTupleTensor_mem (E : PeriodicSpace.Params) {q : ℕ} {X : FnTuple q}
    (hX : X ∈ Kind.sepC1Tuples E .euclidean q) :
    realTupleTensor X ∈ sepTensorSubmodule E Set.univ q := by apply _root_.YangMills.Construction.FamiliesOfLimits.CoordinateMirrorPositivity.realTupleTensor_mem_univ <;> assumption
theorem linComb_succ {q n : ℕ} (c : Fin (n + 1) → ℂ) (T : Fin (n + 1) → OrderedTestFun q) :
    linComb c T = c 0 • T 0 + (1 : ℂ) • linComb (Fin.tail c) (Fin.tail T) := by
  cases q with
  | zero =>
    show ∑ b, c b * T b = c 0 * T 0 + 1 * ∑ b, Fin.tail c b * Fin.tail T b
    rw [Fin.sum_univ_succ, one_mul]
    rfl
  | succ q =>
    funext x
    show ∑ b, c b * T b x = c 0 * T 0 x + 1 * ∑ b, Fin.tail c b * Fin.tail T b x
    rw [Fin.sum_univ_succ, one_mul]
    rfl
theorem momentExtensionAt_realTupleTensor {Ξ : D.LimitHierarchy} (hE : MomentLinearExtension Ξ)
    {q : ℕ} {X : FnTuple q} (hX : X ∈ D.sepDomain q) :
    momentExtensionAt Ξ ⟨q, realTupleTensor X⟩ = ((Ξ.partitionMoment ⟨X, hX⟩ : ℝ) : ℂ) := by
  cases q with
  | zero =>
    rw [Kind.Hierarchy.partitionMoment_zero]
    exact (hE.at_zero _).trans (by simp [realTupleTensor, CentredTensorMoments.tupleTensor])
  | succ q => exact hE.at_tensor q ⟨X, hX⟩
theorem momentExtensionAt_linComb {Ξ : D.LimitHierarchy} (hE : MomentLinearExtension Ξ) {q : ℕ} :
    ∀ {n : ℕ} (c : Fin n → ℂ) (X : Fin n → FnTuple q) (hX : ∀ b, X b ∈ D.sepDomain q),
      (linComb c fun b => realTupleTensor (X b)) ∈
          sepTensorSubmodule D.euclidParams Set.univ q ∧
        momentExtensionAt Ξ ⟨q, linComb c fun b => realTupleTensor (X b)⟩ =
          ∑ b, c b * ((Ξ.partitionMoment ⟨X b, hX b⟩ : ℝ) : ℂ) := by
  intro n
  induction n with
  | zero =>
    intro c X hX
    have e : (linComb c fun b => realTupleTensor (X b)) = (0 : OrderedTestFun q) := by
      cases q with
      | zero => simp [linComb]
      | succ q =>
        funext x
        show ∑ b, c b * _ = (0 : ℂ)
        simp
    rw [e]
    refine ⟨Submodule.zero_mem _, ?_⟩
    have h₀ := hE.is_linear q 0 0 0 0 (Submodule.zero_mem _) (Submodule.zero_mem _)
    simp only [zero_mul, smul_zero, add_zero] at h₀
    simpa using h₀
  | succ n ih =>
    intro c X hX
    obtain ⟨h₁, h₂⟩ := ih (Fin.tail c) (Fin.tail X) (fun b => hX b.succ)
    have e : (linComb c fun b => realTupleTensor (X b)) =
        c 0 • realTupleTensor (X 0) +
          (1 : ℂ) • linComb (Fin.tail c) fun b => realTupleTensor (Fin.tail X b) :=
      linComb_succ c _
    have hm := realTupleTensor_mem D.euclidParams (hX 0)
    rw [e]
    refine ⟨Submodule.add_mem _ (Submodule.smul_mem _ _ hm) (Submodule.smul_mem _ _ h₁), ?_⟩
    rw [hE.is_linear q _ _ _ _ hm h₁, h₂, momentExtensionAt_realTupleTensor hE (hX 0),
      Fin.sum_univ_succ, one_mul]
    rfl
def pairCoeff {n n' : ℕ} (a : Fin n → ℂ) (a' : Fin n' → ℂ) (i : Fin (n * n')) : ℂ :=
  conj (a (finProdFinEquiv.symm i).1) * a' (finProdFinEquiv.symm i).2
def pairMirrorTuple (c : ℝ) {k k' n n' : ℕ} (X : Fin n → FnTuple k) (Y : Fin n' → FnTuple k')
    (i : Fin (n * n')) : FnTuple (k + k') :=
  mirrorAppend c (X (finProdFinEquiv.symm i).1) (Y (finProdFinEquiv.symm i).2)
theorem gradedTensor_conjReflect_eq (c : ℝ) {k k' n n' : ℕ} {F : OrderedTestFun k}
    {G : OrderedTestFun k'} {a : Fin n → ℂ} {a' : Fin n' → ℂ} {X : Fin n → FnTuple k}
    {Y : Fin n' → FnTuple k'} (hF : F = linComb a fun b => realTupleTensor (X b))
    (hG : G = linComb a' fun b => realTupleTensor (Y b)) :
    gradedTensor ⟨k, conjReflectTest 3 c F⟩ ⟨k', G⟩ =
      ⟨k + k', linComb (pairCoeff a a') fun i => realTupleTensor (pairMirrorTuple c X Y i)⟩ := by
  rw [hF, hG, conjReflectTest_linComb]
  exact gradedTensor_linComb _ _ _ _
theorem pairMirrorTuple_mem {k k' n n' : ℕ} {F : OrderedTestFun k} {G : OrderedTestFun k'}
    {a : Fin n → ℂ} {a' : Fin n' → ℂ} {X : Fin n → FnTuple k} {Y : Fin n' → FnTuple k'}
    (hF : IsUpperCombination D.euclidParams F a X) (hG : IsUpperCombination D.euclidParams G a' Y)
    (i : Fin (n * n')) : pairMirrorTuple 0 X Y i ∈ D.sepDomain (k + k') :=
  mirrorAppend_mem_sepC1Tuples D.euclidParams (hF.1 _) (hG.1 _) (hF.2.1 _) (hG.2.1 _)
theorem momentExtensionAt_gradedTensor {Ξ : D.LimitHierarchy} (hE : MomentLinearExtension Ξ)
    {k k' n n' : ℕ} {F : OrderedTestFun k} {G : OrderedTestFun k'} {a : Fin n → ℂ}
    {a' : Fin n' → ℂ} {X : Fin n → FnTuple k} {Y : Fin n' → FnTuple k'}
    (hF : IsUpperCombination D.euclidParams F a X) (hG : IsUpperCombination D.euclidParams G a' Y) :
    momentExtensionAt Ξ (gradedTensor ⟨k, conjReflectTest 3 0 F⟩ ⟨k', G⟩) =
      ∑ i, pairCoeff a a' i *
        ((Ξ.partitionMoment ⟨pairMirrorTuple 0 X Y i, pairMirrorTuple_mem hF hG i⟩ : ℝ) : ℂ) := by
  rw [gradedTensor_conjReflect_eq 0 hF.2.2 hG.2.2]
  exact (momentExtensionAt_linComb hE _ _ _).2
theorem tendsto_sum_pairs (h : CitedFacts) (S : ToriSequence D) {J : Sequences.PNatIndexSet}
    {Ξ : D.LimitHierarchy} (hM : CentredMomentsConverge S J Ξ) (hE : MomentLinearExtension Ξ)
    {k k' n n' : ℕ} {F : OrderedTestFun k} {G : OrderedTestFun k'} {a : Fin n → ℂ}
    {a' : Fin n' → ℂ} {X : Fin n → FnTuple k} {Y : Fin n' → FnTuple k'}
    (hF : IsUpperCombination D.euclidParams F a X) (hG : IsUpperCombination D.euclidParams G a' Y) :
    Tendsto (fun j => ∑ i, pairCoeff a a' i *
        S.centred j (pairMirrorTuple (S.spacing j / 2) X Y i))
      (largeIn J)
      (𝓝 (momentExtensionAt Ξ (gradedTensor ⟨k, conjReflectTest 3 0 F⟩ ⟨k', G⟩))) := by
  rw [momentExtensionAt_gradedTensor hE hF hG]
  refine tendsto_finsetSum _ fun i _ => Tendsto.const_mul _ ?_
  exact tendsto_centredSchwinger_mirrorAppend h S hM (hF.1 _) (hG.1 _) (hF.2.1 _) (hG.2.1 _)
def AllHalfSpaceComponents (ρ c : ℝ) {k : ℕ} (X : FnTuple k) : Prop :=
  ∀ l, IsHalfSpaceComponent ρ 3 c (X l)
theorem eventually_allHalfSpaceComponents (h : CitedFacts) (S : ToriSequence D) {k : ℕ}
    {X : FnTuple k} (hX : X ∈ D.sepDomain k) (hX₀ : SupportedAbove 0 X) :
    ∀ᶠ j in atTop, AllHalfSpaceComponents (S.radius j) (S.spacing j / 2) X := by
  obtain ⟨-, x₂, -⟩ := (BallTuples.mem_sepC1Tuples_euclidean_iff X).1 hX
  refine eventually_all.2 fun l => ?_
  obtain ⟨δ, R, hδ, hR, hf⟩ := isHalfSpaceEntry_eventually (x₂ l) (hX₀ l)
  have hrad : Tendsto S.radius atTop atTop := ((h.cumulants D S).1).2.1
  have hc : Tendsto (fun j => S.spacing j / 2) atTop (𝓝 0) := by
    have := (tendsto_spacing_zero S).div_const (2 : ℝ)
    rwa [zero_div] at this
  filter_upwards [hc.eventually (gt_mem_nhds hδ), hc.eventually (gt_mem_nhds (one_pos)),
    hrad.eventually_ge_atTop (R + 2)] with j h₁ h₂ h₃
  exact hf _ _ (half_pos (spacing_pos S j)).le h₁ (by linarith)
theorem mirrorAppend_mem_lipTuplesBall (E : PeriodicSpace.Params) {ρ c : ℝ} {k k' : ℕ}
    {X : FnTuple k} {Y : FnTuple k'} (hX : X ∈ Kind.sepC1Tuples E .euclidean k)
    (hY : Y ∈ Kind.sepC1Tuples E .euclidean k')
    (hXo : AllHalfSpaceComponents ρ c X) (hYo : AllHalfSpaceComponents ρ c Y) :
    mirrorAppend c X Y ∈ BallTuples.lipTuplesBall (k + k') ρ := by
  have hXc : SupportedAbove c X := fun l => (hXo l).1.trans Set.inter_subset_right
  have hYc : SupportedAbove c Y := fun l => (hYo l).1.trans Set.inter_subset_right
  have hZ := mirrorAppend_mem_sepC1Tuples E hX hY hXc hYc
  have hZ' := (BallTuples.mem_sepC1Tuples_euclidean_iff _).1 hZ
  refine ⟨BallTuples.isSepLipschitz_of_mem_sepTuplesR4 (D := E)
    ((BallTuples.mem_sepTuplesR4_iff _).2 hZ'), fun l => ⟨hZ'.2.1 l, ?_⟩⟩
  refine Fin.addCases (fun i => ?_) (fun i => ?_) l
  · rw [mirrorAppend_castAdd]
    exact (hXo i).2
  · rw [mirrorAppend_natAdd]
    exact (hYo i).1.trans Set.inter_subset_left
theorem centredTensorMoment_gradedTensor (h : CitedFacts) (S : ToriSequence D) (j : ℕ+)
    {k k' n n' : ℕ} {F : OrderedTestFun k} {G : OrderedTestFun k'} {a : Fin n → ℂ}
    {a' : Fin n' → ℂ} {X : Fin n → FnTuple k} {Y : Fin n' → FnTuple k'}
    (hF : IsUpperCombination D.euclidParams F a X) (hG : IsUpperCombination D.euclidParams G a' Y)
    (hXo : ∀ b, AllHalfSpaceComponents (S.radius j) (S.spacing j / 2) (X b))
    (hYo : ∀ b, AllHalfSpaceComponents (S.radius j) (S.spacing j / 2) (Y b)) :
    (LatticeLevel.momentDataAt S j).centredTensorMoment
        (D.latticeRadius (S.m j))
        (gradedTensor ⟨k, conjReflectTest 3 (S.spacing j / 2) F⟩ ⟨k', G⟩).2 =
      ∑ i, pairCoeff a a' i * S.centred j (pairMirrorTuple (S.spacing j / 2) X Y i) := by
  rw [gradedTensor_conjReflect_eq _ hF.2.2 hG.2.2]
  exact (h.polynomials D (S.K j) (S.m j) (S.β j) (S.β_pos j)).tensorMoment_linComb _ _ _ _
    fun i => mirrorAppend_mem_lipTuplesBall D.euclidParams (hF.1 _) (hG.1 _) (hXo _) (hYo _)
open CentredTensorMoments (realTupleTensor conjReflectTest)
open CentredTensorMoments.TorusFunctionals (linComb IsHalfSpaceCombination seqObservable)
open LatticeLevel (momentDataAt seqPolynomial ReflectionIsSymmetryAt reflectedPairingAt)
variable {D : Setup}
theorem centredPolynomial_of_eq_zero (K m : ℕ+) (β : ℝ) (hβ : 0 < β) {q : ℕ}
    {F : OrderedTestFun q} (hF : F = 0) (U : (D.momentSetup K m β hβ).BondField) :
    D.centredPolynomial K m β hβ F U = 0 := by
  subst hF
  cases q with
  | zero => rfl
  | succ q =>
    rw [Setup.centredPolynomial_succ]
    show ∑ᶠ p : Fin (q + 1) → (D.momentSetup K m β hβ).PlaquetteInBall (D.latticeRadius m),
      (0 : ℂ) * _ = 0
    simp
theorem seqPolynomial_eq_seqObservable (S : ToriSequence D) (j : ℕ+) {F : TestFamily} {q₀ : ℕ}
    (hF : ∀ q, q₀ < q → F q = 0) :
    seqPolynomial S j F =
      seqObservable (momentDataAt S j) (D.latticeRadius (S.m j))
        (q₀ := q₀) fun q => F q := by
  funext U
  unfold seqPolynomial seqObservable
  rw [finsum_eq_sum_of_support_subset (s := Finset.range (q₀ + 1)), Finset.sum_range]
  · rfl
  · intro q hq
    by_contra hn
    refine hq (centredPolynomial_of_eq_zero _ _ _ _ (hF q ?_) U)
    simpa using hn
theorem isLinkLevel_half_spacing (S : ToriSequence D) (j : ℕ+) :
    (momentDataAt S j).atCutoff.IsLinkLevel (S.spacing j / 2) := by
  refine ⟨0, ?_⟩
  have e : (momentDataAt S j).atCutoff.spacing = S.spacing j := rfl
  rw [e]
  simp
  ring
theorem reflectedPairingAt_eq (h : CitedFacts) (S : ToriSequence D) (j : ℕ+) {F G : TestFamily}
    {q₀ : ℕ} (hF₀ : ∀ q, q₀ < q → F q = 0) (hG₀ : ∀ q, q₀ < q → G q = 0)
    (hF : ∀ q : Fin (q₀ + 1), IsHalfSpaceCombination (S.radius j) 3 (S.spacing j / 2) q (F q))
    (hG : ∀ q : Fin (q₀ + 1), IsHalfSpaceCombination (S.radius j) 3 (S.spacing j / 2) q (G q)) :
    ∃ hiso : ReflectionIsSymmetryAt S j,
      reflectedPairingAt S j hiso F G =
        (∑ q : Fin (q₀ + 1), ∑ q' : Fin (q₀ + 1),
          (momentDataAt S j).centredTensorMoment (D.latticeRadius (S.m j))
            (gradedTensor ⟨q, conjReflectTest 3 (S.spacing j / 2) (F q)⟩
              ⟨q', G q'⟩).2) ∧
      (reflectedPairingAt S j hiso F F).im = 0 ∧ 0 ≤ (reflectedPairingAt S j hiso F F).re := by
  have hρ := D.isRadius_latticeRadius (S.K j) (S.m j) (S.β j) (S.β_pos j)
  obtain ⟨hiso, -, hsum, him, hre⟩ := (h.functionals (momentDataAt S j) _ hρ).2.2.2.2 3
    (S.spacing j / 2) (isLinkLevel_half_spacing S j) q₀ (fun q => F q) (fun q => G q) hF hG
  have e : ∀ H K : TestFamily, (∀ q, q₀ < q → H q = 0) → (∀ q, q₀ < q → K q = 0) →
      reflectedPairingAt S j hiso H K =
        CentredTensorMoments.TorusFunctionals.reflectionPairing (momentDataAt S j)
          (D.latticeRadius (S.m j)) hiso (q₀ := q₀)
          (fun q => H q) (fun q => K q) := by
    intro H K hH hK
    unfold reflectedPairingAt
    rw [seqPolynomial_eq_seqObservable S j hH, seqPolynomial_eq_seqObservable S j hK]
    rfl
  refine ⟨hiso, ?_, ?_, ?_⟩
  · rw [e F G hF₀ hG₀]
    exact hsum
  · rw [e F F hF₀ hF₀]
    exact him
  · rw [e F F hF₀ hF₀]
    exact hre
theorem isHalfSpaceCombination_of {ρ c : ℝ} {q n : ℕ} {F : OrderedTestFun q} {a : Fin n → ℂ}
    {X : Fin n → FnTuple q} (E : PeriodicSpace.Params) (hF : IsUpperCombination E F a X)
    (hX : ∀ b, AllHalfSpaceComponents ρ c (X b)) : IsHalfSpaceCombination ρ 3 c q F := by
  cases q with
  | zero => trivial
  | succ q =>
    refine ⟨n, a, X, fun b => ?_, hX, hF.2.2⟩
    exact BallTuples.isSepLipschitz_of_mem_sepTuplesR4 (D := E)
      ((BallTuples.mem_sepTuplesR4_iff _).2
        ((BallTuples.mem_sepC1Tuples_euclidean_iff _).1 (hF.1 b)))
theorem linComb_fin_zero {q : ℕ} (c : Fin 0 → ℂ) (T : Fin 0 → OrderedTestFun q) :
    linComb c T = (0 : OrderedTestFun q) := by
  cases q with
  | zero => simp [linComb]
  | succ q =>
    funext x
    show ∑ b, c b * _ = (0 : ℂ)
    simp
theorem isUpperCombination_of_eq_zero (E : PeriodicSpace.Params) {q : ℕ} {F : OrderedTestFun q}
    (hF : F = 0) :
    IsUpperCombination E F (Fin.elim0 : Fin 0 → ℂ) (Fin.elim0 : Fin 0 → FnTuple q) :=
  ⟨fun b => b.elim0, fun b => b.elim0, hF.trans (linComb_fin_zero _ _).symm⟩
theorem momentExtensionAt_gradedTensor_zero_left {Ξ : D.LimitHierarchy}
    (hE : MomentLinearExtension Ξ) {k k' n' : ℕ} {F : OrderedTestFun k} {G : OrderedTestFun k'}
    {a' : Fin n' → ℂ} {Y : Fin n' → FnTuple k'} (hF : F = 0)
    (hG : IsUpperCombination D.euclidParams G a' Y) :
    momentExtensionAt Ξ (gradedTensor ⟨k, conjReflectTest 3 0 F⟩ ⟨k', G⟩) = 0 := by
  rw [momentExtensionAt_gradedTensor hE (isUpperCombination_of_eq_zero _ hF) hG]
  have : IsEmpty (Fin (0 * n')) := by
    rw [Nat.zero_mul]
    infer_instance
  simp
theorem momentExtensionAt_gradedTensor_zero_right {Ξ : D.LimitHierarchy}
    (hE : MomentLinearExtension Ξ) {k k' n : ℕ} {F : OrderedTestFun k} {G : OrderedTestFun k'}
    {a : Fin n → ℂ} {X : Fin n → FnTuple k} (hF : IsUpperCombination D.euclidParams F a X)
    (hG : G = 0) :
    momentExtensionAt Ξ (gradedTensor ⟨k, conjReflectTest 3 0 F⟩ ⟨k', G⟩) = 0 := by
  rw [momentExtensionAt_gradedTensor hE hF (isUpperCombination_of_eq_zero _ hG)]
  have : IsEmpty (Fin (n * 0)) := by
    rw [Nat.mul_zero]
    infer_instance
  simp
theorem exists_approximating_sequence (h : CitedFacts) (S : ToriSequence D)
    {J : Sequences.PNatIndexSet} {Ξ : D.LimitHierarchy} (hM : CentredMomentsConverge S J Ξ)
    (hE : MomentLinearExtension Ξ) (F F' : finiteUpperSequences D.euclidParams) :
    ∃ G : ℕ+ → ℂ, Tendsto G (largeIn J) (𝓝 (reflectionPairing Ξ F F')) ∧
      ∀ᶠ j in atTop, ∃ hiso : ReflectionIsSymmetryAt S j,
        reflectedPairingAt S j hiso F.1 F'.1 = G j ∧
        (reflectedPairingAt S j hiso F.1 F.1).im = 0 ∧
        0 ≤ (reflectedPairingAt S j hiso F.1 F.1).re := by
  have hrep := fun q => exists_isUpperCombination D.euclidParams (F.2.1 q)
  have hrep' := fun q => exists_isUpperCombination D.euclidParams (F'.2.1 q)
  choose n a X hX using hrep
  choose n' a' Y hY using hrep'
  obtain ⟨N, hN⟩ := F.2.2
  obtain ⟨N', hN'⟩ := F'.2.2
  set q₀ := N + N' with hq₀
  have hF₀ : ∀ q, q₀ < q → F.1 q = 0 := fun q hq => hN q (by omega)
  have hF₀' : ∀ q, q₀ < q → F'.1 q = 0 := fun q hq => hN' q (by omega)
  refine ⟨fun j => ∑ q : Fin (q₀ + 1), ∑ q' : Fin (q₀ + 1),
    ∑ i, pairCoeff (a q) (a' q') i *
      S.centred j (pairMirrorTuple (S.spacing j / 2) (X q) (Y q') i),
    ?_, ?_⟩
  · have hform : reflectionPairing Ξ F F' = ∑ q : Fin (q₀ + 1), ∑ q' : Fin (q₀ + 1),
        momentExtensionAt Ξ (gradedTensor ⟨q, conjReflectTest 3 0 (F.1 q)⟩
          ⟨q', F'.1 q'⟩) := by
      unfold reflectionPairing reflectionForm
      rw [finsum_eq_sum_of_support_subset (s := Finset.range (q₀ + 1) ×ˢ Finset.range (q₀ + 1)),
        Finset.sum_product, Finset.sum_range]
      · refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.sum_range]
        rfl
      · intro p hp
        by_contra hn
        refine hp ?_
        have hmem : ¬ (p.1 ≤ q₀ ∧ p.2 ≤ q₀) := by
          intro hc
          refine hn ?_
          simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio]
          omega
        by_cases h₁ : p.1 ≤ q₀
        · exact momentExtensionAt_gradedTensor_zero_right hE (hX p.1) (hF₀' _ (by omega))
        · exact momentExtensionAt_gradedTensor_zero_left hE (hF₀ _ (by omega)) (hY p.2)
    rw [hform]
    refine tendsto_finsetSum _ fun q _ => tendsto_finsetSum _ fun q' _ => ?_
    exact tendsto_sum_pairs h S hM hE (hX q) (hY q')
  · have hone : ∀ᶠ j in atTop, ∀ q : Fin (q₀ + 1), ∀ b,
        AllHalfSpaceComponents (S.radius j) (S.spacing j / 2) (X q b) :=
      eventually_all.2 fun q => eventually_all.2 fun b =>
        eventually_allHalfSpaceComponents h S ((hX q).1 b) ((hX q).2.1 b)
    have hone' : ∀ᶠ j in atTop, ∀ q : Fin (q₀ + 1), ∀ b,
        AllHalfSpaceComponents (S.radius j) (S.spacing j / 2) (Y q b) :=
      eventually_all.2 fun q => eventually_all.2 fun b =>
        eventually_allHalfSpaceComponents h S ((hY q).1 b) ((hY q).2.1 b)
    filter_upwards [hone, hone'] with j h₁ h₂
    obtain ⟨hiso, e, him, hre⟩ := reflectedPairingAt_eq h S j hF₀ hF₀'
      (fun q => isHalfSpaceCombination_of D.euclidParams (hX q) (h₁ q))
      (fun q => isHalfSpaceCombination_of D.euclidParams (hY q) (h₂ q))
    refine ⟨hiso, e.trans ?_, him, hre⟩
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun q' _ => ?_
    exact centredTensorMoment_gradedTensor h S j (hX q) (hY q') (h₁ q) (h₂ q')
theorem reflectionPairing_eq_limit (h : CitedFacts) (S : ToriSequence D)
    {J : Sequences.PNatIndexSet} {Ξ : D.LimitHierarchy} (hM : CentredMomentsConverge S J Ξ)
    (hE : MomentLinearExtension Ξ) (F F' : finiteUpperSequences D.euclidParams) :
    DiagonalLimits.TendsToWhereDefined J (ReflectionIsSymmetryAt S)
      (fun j hj => reflectedPairingAt S j hj F.1 F'.1) (reflectionPairing Ξ F F') := by
  obtain ⟨G, hG, hev⟩ := exists_approximating_sequence h S hM hE F F'
  intro ε hε
  refine eventuallyAlong_of_eventually_largeIn ?_
  filter_upwards [Metric.tendsto_nhds.1 hG ε hε, eventually_largeIn_of_atTop hev] with j h₁ h₂
  obtain ⟨hiso, e, -⟩ := h₂
  refine ⟨hiso, ?_⟩
  rw [e, ← dist_eq_norm]
  exact h₁
theorem reflectionPositive (h : CitedFacts) (S : ToriSequence D) {J : Sequences.PNatIndexSet}
    {Ξ : D.LimitHierarchy} (hM : CentredMomentsConverge S J Ξ) (hE : MomentLinearExtension Ξ) :
    ReflectionPositive Ξ := by
  intro F
  obtain ⟨G, hG, hev⟩ := exists_approximating_sequence h S hM hE F F
  have := largeIn_neBot J
  have hev' : ∀ᶠ j in largeIn J, (G j).im = 0 ∧ 0 ≤ (G j).re := by
    filter_upwards [eventually_largeIn_of_atTop hev] with j hj
    obtain ⟨hiso, e, him, hre⟩ := hj
    rw [← e]
    exact ⟨him, hre⟩
  have him : (reflectionPairing Ξ F F).im = 0 := by
    have h₁ : Tendsto (fun j => (G j).im) (largeIn J) (𝓝 (reflectionPairing Ξ F F).im) :=
      (Complex.continuous_im.tendsto _).comp hG
    have h₂ : Tendsto (fun j => (G j).im) (largeIn J) (𝓝 0) :=
      tendsto_const_nhds.congr' (hev'.mono fun j hj => hj.1.symm)
    exact tendsto_nhds_unique h₁ h₂
  have hre : 0 ≤ (reflectionPairing Ξ F F).re := by
    have h₁ : Tendsto (fun j => (G j).re) (largeIn J) (𝓝 (reflectionPairing Ξ F F).re) :=
      (Complex.continuous_re.tendsto _).comp hG
    exact ge_of_tendsto h₁ (hev'.mono fun j hj => hj.2)
  exact ⟨(reflectionPairing Ξ F F).re, hre, Complex.ext rfl (by simp [him])⟩
end YangMills.Construction.ToriLimits.GrowingVolumeLimits.ProofSteps.ReflectedLatticeFormula
end
end
