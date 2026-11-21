import YangMills.Construction.SeparatedSequences.ClassExpansionsOnAGeneralTorusProof
import YangMills.Construction.DirichletOperator.FactsOfTheSettingInLevelUnitsProof
import YangMills.Construction.SeparatedSequences.ClassSiteFunctionsInASettingOfTheTorusOfLevelSideProof
import YangMills.Construction.SeparatedSequences.PartitionsCubesExpansionsAndTheTriangleInequality
import Mathlib
set_option autoImplicit false
open Set
open scoped Pointwise
open MeasureTheory
noncomputable section
namespace YangMills.Construction.SeparatedClasses.BlockGeometryOfClass
open SingleSequence SingleSequence.SequenceData
section Rescaling
variable (s : SequenceData)
theorem Lreal_pos : 0 < s.Lreal := by apply _root_.YangMills.Construction.SeparatedClasses.BlockSettingScalarData.Lreal_pos <;> assumption
theorem thirteen_le_Lreal : (13 : ℝ) ≤ s.Lreal := by
  have hL := s.data.isAdmissible.2
  show (13 : ℝ) ≤ (s.data.L : ℝ)
  exact_mod_cast hL
theorem unitScale_pos : 0 < s.unitScale := pow_pos (Lreal_pos s) _
theorem unitScale_eq_zpow :
    s.unitScale = s.Lreal ^ ((s.data.cutoff : ℤ) - (s.data.t : ℤ)) := by apply _root_.YangMills.Construction.SeparatedClasses.GaugeOneFormsProof.TorusComponents.unitScale_eq_zpow <;> assumption
theorem unitTorusSide_eq :
    s.unitTorusSide = s.unitScale * PeriodicLattice.torusSide s.data.L s.data.m := by
  have hne := (Lreal_pos s).ne'
  rw [SequenceData.unitTorusSide, Torus.unitSide, unitScale_eq_zpow, PeriodicLattice.torusSide]
  have e : ((s.data.m : ℕ) : ℤ) + ((s.data.cutoff : ℕ) : ℤ) - (s.data.t : ℤ) =
      ((s.data.cutoff : ℤ) - (s.data.t : ℤ)) + ((s.data.m : ℕ) : ℤ) := by ring
  rw [e, zpow_add₀ hne, zpow_natCast]
  ring
theorem unitTorusSide_ne_zero : s.unitTorusSide ≠ 0 := by apply _root_.YangMills.Construction.SeparatedClasses.BlockSettingScalarData.unitTorusSide_ne_zero <;> assumption
def rescale : s.data.Point ≃ₜ TorusMetric.Torus4 s.unitTorusSide :=
  Homeomorph.piCongrRight fun _ =>
    AddCircle.homeomorphAddCircle _ _ s.torusSide_ne_zero (unitTorusSide_ne_zero s)
theorem toTorus_apply (x : s.data.Point) : s.toTorus s.unitTorusSide x = rescale s x := by
  rw [SequenceData.toTorus, dif_pos (unitTorusSide_ne_zero s)]
  rfl
theorem toTorus_eq_rescale : s.toTorus s.unitTorusSide = rescale s := funext (toTorus_apply s)
theorem rescale_sub (x y : s.data.Point) : rescale s (x - y) = rescale s x - rescale s y := by
  funext μ
  exact map_sub (AddCircle.equivAddCircle _ _ s.torusSide_ne_zero (unitTorusSide_ne_zero s)) _ _
theorem rescale_torusProj (v : Fin 4 → ℝ) :
    rescale s (TorusMetric.torusProj (PeriodicLattice.torusSide s.data.L s.data.m) v) =
      TorusMetric.torusProj s.unitTorusSide (s.unitScale • v) := by
  funext μ
  have hℓ := s.torusSide_ne_zero
  show AddCircle.homeomorphAddCircle _ _ hℓ (unitTorusSide_ne_zero s) ((v μ : ℝ) : AddCircle _) = _
  rw [AddCircle.homeomorphAddCircle_apply_mk]
  show _ = ((s.unitScale * v μ : ℝ) : AddCircle s.unitTorusSide)
  congr 1
  rw [unitTorusSide_eq]
  field_simp
theorem supNormVec_eq_norm (v : Fin 4 → ℝ) : TorusMetric.supNormVec v = ‖v‖ := by apply _root_.YangMills.Construction.LevelUnitFacts.supNormVec_eq_norm <;> assumption
theorem supNorm_rescale (x : s.data.Point) :
    Torus.supNorm (rescale s x) = s.unitScale * TorusMetric.torusSupNorm x := by
  have hc := unitScale_pos s
  have hset : {r | ∃ v : Fin 4 → ℝ, Torus.torusProj 4 s.unitTorusSide v = rescale s x ∧ r = ‖v‖} =
      s.unitScale • (TorusMetric.supNormVec ''
        (TorusMetric.torusProj (PeriodicLattice.torusSide s.data.L s.data.m) ⁻¹' {x})) := by
    ext r
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨TorusMetric.supNormVec (s.unitScale⁻¹ • v), ⟨s.unitScale⁻¹ • v, ?_, rfl⟩, ?_⟩
      · apply (rescale s).injective
        rw [rescale_torusProj, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
        exact hv
      · show s.unitScale * TorusMetric.supNormVec (s.unitScale⁻¹ • v) = ‖v‖
        rw [supNormVec_eq_norm, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hc), ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      refine ⟨s.unitScale • w, ?_, ?_⟩
      · have hw' : TorusMetric.torusProj (PeriodicLattice.torusSide s.data.L s.data.m) w = x := hw
        rw [← hw', rescale_torusProj]
        rfl
      · show s.unitScale * TorusMetric.supNormVec w = _
        rw [supNormVec_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  unfold Torus.supNorm TorusMetric.torusSupNorm
  rw [hset, Real.sInf_smul_of_nonneg hc.le, smul_eq_mul]
theorem rescale_image_cube (z : s.data.Point) (a : ℝ) :
    rescale s '' {x | TorusMetric.torusSupNorm (x - z) ≤ a / 2} =
      Torus.cubeAt (rescale s z) (s.unitScale * a) := by
  have hc := unitScale_pos s
  ext p
  obtain ⟨x, rfl⟩ := (rescale s).surjective p
  rw [(rescale s).injective.mem_set_image]
  show TorusMetric.torusSupNorm (x - z) ≤ a / 2 ↔
    Torus.supNorm (rescale s x - rescale s z) ≤ s.unitScale * a / 2
  rw [← rescale_sub, supNorm_rescale, mul_div_assoc]
  exact (mul_le_mul_iff_right₀ hc).symm
theorem rescale_image_sublattice (j : ℤ) (σ : ℝ)
    (hσ : σ = s.unitScale * PeriodicLattice.meshSize s.data.L j) :
    rescale s '' (PeriodicLattice.sublattice s.data.L s.data.m j : Set s.data.Point) =
      (Torus.spacingLattice 4 s.unitTorusSide σ : Set (Torus.PeriodicTorus 4 s.unitTorusSide)) := by
  ext p
  constructor
  · rintro ⟨x, ⟨n, hn⟩, rfl⟩
    refine ⟨n, ?_⟩
    have hx : x = TorusMetric.torusProj (PeriodicLattice.torusSide s.data.L s.data.m)
        fun μ => (n μ : ℝ) * PeriodicLattice.meshSize s.data.L j := funext hn
    rw [hx, rescale_torusProj]
    funext μ
    show ((s.unitScale * ((n μ : ℝ) * PeriodicLattice.meshSize s.data.L j) : ℝ) :
        AddCircle s.unitTorusSide) = (((n μ : ℝ) * σ : ℝ) : AddCircle s.unitTorusSide)
    rw [hσ]
    congr 1
    ring
  · rintro ⟨k, rfl⟩
    refine ⟨TorusMetric.torusProj (PeriodicLattice.torusSide s.data.L s.data.m)
      fun μ => (k μ : ℝ) * PeriodicLattice.meshSize s.data.L j, ⟨k, fun μ => rfl⟩, ?_⟩
    rw [rescale_torusProj]
    funext μ
    show ((s.unitScale * ((k μ : ℝ) * PeriodicLattice.meshSize s.data.L j) : ℝ) :
        AddCircle s.unitTorusSide) = (((k μ : ℝ) * σ : ℝ) : AddCircle s.unitTorusSide)
    rw [hσ]
    congr 1
    ring
theorem rescale_image_partition (i : ℤ) (σ : ℝ)
    (hσ : σ = s.unitScale * PeriodicLattice.meshSize s.data.L i) :
    (fun Q => rescale s '' Q) '' PeriodicLattice.standardCubePartition s.data.L s.data.m i =
      Torus.cubePartition 4 s.unitTorusSide σ := by
  ext 𝒬
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    refine ⟨rescale s y, ?_, ?_⟩
    · rw [← SetLike.mem_coe, ← rescale_image_sublattice s i σ hσ]
      exact ⟨y, y.2, rfl⟩
    · rw [hσ]
      exact rescale_image_cube s _ _
  · rintro ⟨z, hz, rfl⟩
    rw [← SetLike.mem_coe, ← rescale_image_sublattice s i σ hσ] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    refine ⟨PeriodicLattice.cubeAround (⟨x, hx⟩ : PeriodicLattice.Site s.data.L s.data.m i),
      ⟨_, rfl⟩, ?_⟩
    rw [hσ]
    exact rescale_image_cube s _ _
theorem unitScale_mul_meshSize (i : ℤ) :
    s.unitScale * PeriodicLattice.meshSize s.data.L ((s.data.cutoff : ℤ) - i) =
      s.Lreal ^ (i - (s.data.t : ℤ)) := by
  rw [unitScale_eq_zpow, PeriodicLattice.meshSize, ← zpow_add₀ (Lreal_pos s).ne']
  congr 1
  ring
theorem dirichletParameters :
    Dirichlet.Parameters 4 s.data.L (1 - s.Lreal ^ (-2 : ℤ)) 1 := by
  have h13 := thirteen_le_Lreal s
  have hL := s.data.isAdmissible
  have hlt : s.Lreal ^ (-2 : ℤ) < 1 := by
    rw [zpow_neg, inv_lt_one₀ (zpow_pos (Lreal_pos s) _)]
    have : (1 : ℝ) < s.Lreal ^ (2 : ℤ) := by
      rw [zpow_ofNat]
      nlinarith
    exact this
  have hpos : 0 < s.Lreal ^ (-2 : ℤ) := zpow_pos (Lreal_pos s) _
  exact ⟨by norm_num, by have := hL.2; omega, hL.1, by linarith, by linarith⟩
end Rescaling
section SegmentLists
variable (s : SequenceData)
theorem pointAt_scaleSegmentDir (g : TorusMetric.LiftedSegment) (τ : ℝ) :
    Torus.TorusSegment.pointAt s.unitTorusSide (s.scaleSegmentDir g) τ =
      rescale s (g.pointAt (PeriodicLattice.torusSide s.data.L s.data.m) τ) := by
  rw [TorusMetric.LiftedSegment.pointAt, rescale_torusProj]
  show TorusMetric.torusProj s.unitTorusSide
    (s.unitScale • g.tail + τ • (s.unitScale • g.displacement)) = _
  rw [smul_add, smul_comm τ s.unitScale g.displacement]
theorem scaleSegmentDir_term (g : TorusMetric.LiftedSegment) (X : Set s.data.Point) :
    (s.scaleSegmentDir g).lOneLength *
        (volume {τ ∈ Icc (0 : ℝ) 1 |
          Torus.TorusSegment.pointAt s.unitTorusSide (s.scaleSegmentDir g) τ ∈
            rescale s '' X}).toReal =
      s.unitScale * (TorusMetric.l1NormVec g.displacement * (volume (Icc (0 : ℝ) 1 ∩
        g.pointAt (PeriodicLattice.torusSide s.data.L s.data.m) ⁻¹' X)).toReal) := by
  have hset : {τ ∈ Icc (0 : ℝ) 1 |
      Torus.TorusSegment.pointAt s.unitTorusSide (s.scaleSegmentDir g) τ ∈ rescale s '' X} =
      Icc (0 : ℝ) 1 ∩ g.pointAt (PeriodicLattice.torusSide s.data.L s.data.m) ⁻¹' X := by
    ext τ
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, pointAt_scaleSegmentDir,
      (rescale s).injective.mem_set_image]
  have hlen : (s.scaleSegmentDir g).lOneLength =
      s.unitScale * TorusMetric.l1NormVec g.displacement := by
    show ∑ μ, |s.unitScale * g.displacement μ| = s.unitScale * ∑ μ, |g.displacement μ|
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun μ _ => by rw [abs_mul, abs_of_pos (unitScale_pos s)]
  rw [hset, hlen, mul_assoc]
theorem lengthWithin_rescale_image (Γ : List TorusMetric.LiftedSegment) (X : Set s.data.Point) :
    Torus.lengthWithin (Γ.map s.scaleSegmentDir) (rescale s '' X) =
      s.unitScale * TorusMetric.pathLengthIn (PeriodicLattice.torusSide s.data.L s.data.m) Γ X := by
  induction Γ with
  | nil => simp [Torus.lengthWithin, TorusMetric.pathLengthIn]
  | cons g Γ ih =>
    simp only [Torus.lengthWithin, TorusMetric.pathLengthIn, List.map_cons, List.sum_cons] at ih ⊢
    rw [scaleSegmentDir_term, ih, mul_add]
theorem segmentUnion_map (Γ : List TorusMetric.LiftedSegment) :
    Torus.segmentUnion s.unitTorusSide (Γ.map s.scaleSegmentDir) =
      rescale s '' TorusMetric.segmentsSupport (PeriodicLattice.torusSide s.data.L s.data.m) Γ := by
  ext p
  simp only [Torus.segmentUnion, TorusMetric.segmentsSupport, TorusMetric.LiftedSegment.support,
    mem_ofPred_eq, List.mem_map, mem_image, mem_iUnion, exists_prop]
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, τ, hτ, rfl⟩
    exact ⟨_, ⟨g, hg, τ, hτ, rfl⟩, (pointAt_scaleSegmentDir s g τ).symm⟩
  · rintro ⟨_, ⟨g, hg, τ, hτ, rfl⟩, rfl⟩
    exact ⟨_, ⟨g, hg, rfl⟩, τ, hτ, (pointAt_scaleSegmentDir s g τ).symm⟩
theorem scaleSegmentDir_surjective : Function.Surjective s.scaleSegmentDir := by
  rintro ⟨b, d⟩
  have hc := (unitScale_pos s).ne'
  refine ⟨⟨s.unitScale⁻¹ • b, s.unitScale⁻¹ • (b + d)⟩, ?_⟩
  show (⟨s.unitScale • s.unitScale⁻¹ • b,
    s.unitScale • (s.unitScale⁻¹ • (b + d) - s.unitScale⁻¹ • b)⟩ : Torus.TorusSegment 4) = _
  rw [smul_inv_smul₀ hc, ← smul_sub, add_sub_cancel_left, smul_inv_smul₀ hc]
theorem lengthWithin_nonneg {S : ℝ} (Γ : List (Torus.TorusSegment 4))
    (X : Set (Torus.PeriodicTorus 4 S)) : 0 ≤ Torus.lengthWithin Γ X := by
  refine List.sum_nonneg fun a ha => ?_
  obtain ⟨g, -, rfl⟩ := List.mem_map.1 ha
  exact mul_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) ENNReal.toReal_nonneg
theorem exists_isTreeGraph_mem (x y : s.data.Point) :
    ∃ Γ : List TorusMetric.LiftedSegment,
      TorusMetric.IsTreeGraph (PeriodicLattice.torusSide s.data.L s.data.m) Γ ∧
      x ∈ TorusMetric.segmentsSupport (PeriodicLattice.torusSide s.data.L s.data.m) Γ ∧
      y ∈ TorusMetric.segmentsSupport (PeriodicLattice.torusSide s.data.L s.data.m) Γ := by
  have hlift : ∀ p : s.data.Point, ∃ v : Fin 4 → ℝ,
      TorusMetric.torusProj (PeriodicLattice.torusSide s.data.L s.data.m) v = p := fun p =>
    ⟨fun μ => (TorusMetric.exists_coe_eq_abs_eq_norm (p μ)).choose,
      funext fun μ => (TorusMetric.exists_coe_eq_abs_eq_norm (p μ)).choose_spec.1⟩
  obtain ⟨v, hv⟩ := hlift x
  obtain ⟨w, hw⟩ := hlift y
  have hsupp : TorusMetric.segmentsSupport (PeriodicLattice.torusSide s.data.L s.data.m) [⟨v, w⟩] =
      TorusMetric.LiftedSegment.pointAt (PeriodicLattice.torusSide s.data.L s.data.m) ⟨v, w⟩ ''
        Icc 0 1 := by
    simp [TorusMetric.segmentsSupport, TorusMetric.LiftedSegment.support]
  have hcont : Continuous
      (TorusMetric.LiftedSegment.pointAt (PeriodicLattice.torusSide s.data.L s.data.m) ⟨v, w⟩) := by
    refine continuous_pi fun μ => ?_
    show Continuous fun τ : ℝ =>
      ((((⟨v, w⟩ : TorusMetric.LiftedSegment).tail +
        τ • (⟨v, w⟩ : TorusMetric.LiftedSegment).displacement) μ : ℝ) :
        AddCircle (PeriodicLattice.torusSide s.data.L s.data.m))
    exact (AddCircle.continuous_mk' _).comp (by fun_prop)
  refine ⟨[⟨v, w⟩], ?_, ?_, ?_⟩
  · show IsConnected (TorusMetric.segmentsSupport _ _)
    rw [hsupp]
    exact (isConnected_Icc zero_le_one).image _ hcont.continuousOn
  · rw [hsupp]
    refine ⟨0, left_mem_Icc.2 zero_le_one, ?_⟩
    simp [TorusMetric.LiftedSegment.pointAt, hv]
  · rw [hsupp]
    refine ⟨1, right_mem_Icc.2 zero_le_one, ?_⟩
    simp [TorusMetric.LiftedSegment.pointAt, TorusMetric.LiftedSegment.displacement, hw]
end SegmentLists
section BlockSettingOfSide
variable {s : SequenceData} {𝒮 : s.BlockSettingType} (h : s.IsBlockSetting 𝒮)
include h
theorem Ω_eq_image (n : ℕ) : 𝒮.Ω n = rescale s '' s.Ω n := by
  rw [h.Ω_eq, SequenceData.regionOn, toTorus_eq_rescale]
theorem Ω_eq_empty_of_lt {n : ℕ} (hn : s.data.t < n) : 𝒮.Ω n = ∅ :=
  𝒮.isSeparatedChain.eq_empty_of_lt n (by rw [h.t_eq]; exact hn)
theorem scaleSpacing_eq_zpow (i : ℤ) :
    Torus.scaleSpacing s.data.L 𝒮.ξ i = s.Lreal ^ (i - (s.data.t : ℤ)) := by
  rw [Torus.scaleSpacing, h.ξ_eq, SequenceData.mesh, Torus.unitSpacing,
    sub_eq_add_neg, zpow_add₀ (Lreal_pos s).ne']
theorem scaleSpacing_eq_meshSize (i : ℕ) :
    Torus.scaleSpacing s.data.L 𝒮.ξ (i : ℤ) =
      s.unitScale * PeriodicLattice.meshSize s.data.L
        (PeriodicLattice.levelDepth s.data.cutoff i) := by
  rw [scaleSpacing_eq_zpow h, PeriodicLattice.levelDepth, unitScale_mul_meshSize]
theorem blockScale_eq_meshSize (n : ℕ) :
    (𝒮.M : ℝ) * 𝒮.scaleAt n =
      s.unitScale * PeriodicLattice.meshSize s.data.L (s.data.scales.blockPartitionIndex n) := by
  have e : s.data.scales.blockPartitionIndex n =
      (s.data.cutoff : ℤ) - ((n : ℤ) + (s.data.blockExp : ℤ)) := by
    simp only [SeparatedSequences.ScaleData.blockPartitionIndex,
      PeriodicLattice.scaledCubeIndex, PeriodicLattice.levelDepth]
    ring
  rw [e, unitScale_mul_meshSize, Dirichlet.BlockSetting.scaleAt, scaleSpacing_eq_zpow h,
    h.M_eq, ClassData.blockSize]
  push_cast
  rw [← zpow_natCast, ← zpow_add₀ (Lreal_pos s).ne']
  congr 1
  ring
theorem le_lastNonemptyIndex {n : ℕ} (hn : (𝒮.Ω n).Nonempty) :
    n ≤ Torus.lastNonemptyIndex 𝒮.Ω := by
  refine le_csSup ⟨s.data.t, fun k hk => ?_⟩ hn
  by_contra hlt
  exact (show (𝒮.Ω k).Nonempty from hk).ne_empty (Ω_eq_empty_of_lt h (not_le.mp hlt))
theorem lastNonemptyIndex_le : Torus.lastNonemptyIndex 𝒮.Ω ≤ s.data.t := by
  refine csSup_le ⟨0, 𝒮.isSeparatedChain.zero_nonempty⟩ fun k hk => ?_
  by_contra hlt
  exact (show (𝒮.Ω k).Nonempty from hk).ne_empty (Ω_eq_empty_of_lt h (not_le.mp hlt))
theorem shell_subset_Ω (hT : Torus.PartitionsHold) (n : ℕ) :
    Torus.shell 𝒮.Ω n ⊆ 𝒮.Ω n := by
  by_cases hn : n ≤ Torus.lastNonemptyIndex 𝒮.Ω
  · have hm := ((hT 4 s.data.L _ _ (dirichletParameters s) 𝒮.ξ s.unitTorusSide
      𝒮.isSeparatedChain.scale_pos 𝒮.isSeparatedChain.period_pos).2.2 𝒮.M 𝒮.R₁ 𝒮.t 𝒮.Ω
      𝒮.isSeparatedChain).2.1
    exact (hm.shell_subset n hn).trans inter_subset_left
  · have he : 𝒮.Ω n = ∅ :=
      not_nonempty_iff_eq_empty.mp fun hne => hn (le_lastNonemptyIndex h hne)
    simp [Torus.shell, he]
theorem rescale_image_layerAt (hT : Torus.PartitionsHold) (n : ℕ) :
    rescale s '' s.data.layerAt s.Ω n = Torus.shell 𝒮.Ω n := by
  rcases lt_trichotomy n s.data.t with hn | hn | hn
  · have e : s.data.layerAt s.Ω n = closure (s.Ω n \ s.Ω (n + 1)) := if_pos hn
    rw [e, (rescale s).image_closure, image_sdiff (rescale s).injective, Torus.shell,
      Ω_eq_image h, Ω_eq_image h]
  · subst hn
    have e : s.data.layerAt s.Ω s.data.t = s.Ω s.data.t := by
      show SeparatedSequences.layerSet s.data.scales s.Ω s.data.t = _
      rw [SeparatedSequences.layerSet, if_neg (lt_irrefl _), if_pos rfl]
    rw [e, ← Ω_eq_image h]
    apply Subset.antisymm
    · rw [Torus.shell, Ω_eq_empty_of_lt h (Nat.lt_succ_self _), sdiff_empty]
      exact subset_closure
    · exact shell_subset_Ω h hT _
  · have e : s.data.layerAt s.Ω n = ∅ := by
      show SeparatedSequences.layerSet s.data.scales s.Ω n = _
      rw [SeparatedSequences.layerSet, if_neg (show ¬n < s.data.t by omega),
        if_neg (show ¬n = s.data.t by omega)]
    rw [e, image_empty, Torus.shell, Ω_eq_empty_of_lt h hn]
    simp
theorem rescale_image_layerSitesAt (hT : Torus.PartitionsHold) (n : ℕ) :
    (fun y : s.data.LatticeSite n => rescale s (y : s.data.Point)) '' s.data.layerSitesAt s.Ω n =
      Torus.shellSites s.data.L 𝒮.ξ 𝒮.Ω n := by
  have hlat := rescale_image_sublattice s (PeriodicLattice.levelDepth s.data.cutoff n) _
    (scaleSpacing_eq_meshSize h n)
  ext p
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hl : rescale s (y : s.data.Point) ∈ Torus.shell 𝒮.Ω n := by
      rw [← rescale_image_layerAt h hT]
      exact ⟨_, hy, rfl⟩
    refine ⟨le_lastNonemptyIndex h ⟨_, shell_subset_Ω h hT n hl⟩, ?_, hl⟩
    rw [← SetLike.mem_coe, ← hlat]
    exact ⟨y, y.2, rfl⟩
  · rintro ⟨-, hp, hl⟩
    rw [← SetLike.mem_coe, ← hlat] at hp
    obtain ⟨x, hx, rfl⟩ := hp
    rw [← rescale_image_layerAt h hT, (rescale s).injective.mem_set_image] at hl
    exact ⟨⟨x, hx⟩, hl, rfl⟩
theorem shellIndex_eq (hT : Torus.PartitionsHold) (hC : BlockStructureStatement)
    (y : s.data.Apex s.Ω) :
    Torus.shellIndex s.data.L 𝒮.ξ 𝒮.Ω (rescale s y.point) = y.level := by
  have hdisj := (hC s.data s.Ω s.frame s.Ω_mem).2.2.2.2.2.1.1
  have hset : {n | rescale s y.point ∈ Torus.shellSites s.data.L 𝒮.ξ 𝒮.Ω n} = {y.level} := by
    ext k
    rw [mem_singleton_iff]
    constructor
    · intro hk
      have hk' : rescale s y.point ∈ Torus.shellSites s.data.L 𝒮.ξ 𝒮.Ω k := hk
      have hkt : k ≤ s.data.t := hk'.1.trans (lastNonemptyIndex_le h)
      rw [← rescale_image_layerSitesAt h hT] at hk'
      obtain ⟨z, hz, hzy⟩ := hk'
      have hzy' : (z : s.data.Point) = y.point := (rescale s).injective hzy
      by_contra hne
      exact Set.disjoint_left.1 (hdisj k hkt y.level y.2.1 hne) ⟨z, hz, hzy'⟩
        ⟨y.site, y.2.2, rfl⟩
    · intro hk
      subst hk
      show rescale s y.point ∈ Torus.shellSites s.data.L 𝒮.ξ 𝒮.Ω y.level
      rw [← rescale_image_layerSitesAt h hT]
      exact ⟨y.site, y.2.2, rfl⟩
  rw [Torus.shellIndex, hset, csInf_singleton]
theorem shellSpacing_eq (hT : Torus.PartitionsHold) (hC : BlockStructureStatement)
    (y : s.data.Apex s.Ω) :
    Torus.shellSpacing s.data.L 𝒮.ξ 𝒮.Ω (rescale s y.point) =
      s.unitScale * PeriodicLattice.meshSize s.data.L
        (PeriodicLattice.levelDepth s.data.cutoff y.level) := by
  rw [Torus.shellSpacing, shellIndex_eq h hT hC, scaleSpacing_eq_meshSize h]
omit h in
theorem mesh_eq (y : s.data.Apex s.Ω) :
    y.mesh = s.unitScale * PeriodicLattice.meshSize s.data.L
      (PeriodicLattice.levelDepth s.data.cutoff y.level) := by
  rw [PeriodicLattice.levelDepth, unitScale_mul_meshSize]
  rfl
theorem chainWeightedLength_map (hT : Torus.PartitionsHold)
    (Γ : List TorusMetric.LiftedSegment) :
    Torus.chainWeightedLength s.data.L 𝒮.ξ 𝒮.t 𝒮.Ω (Γ.map s.scaleSegmentDir) =
      s.data.chainLength s.Ω Γ := by
  have hin : ∀ r, s.data.scales.toUnits s.data.L r = s.unitScale * r := by
    intro r
    rw [unitScale_eq_zpow]
    rfl
  have hun : ∀ i : ℕ, s.data.scales.levelMesh s.data.L i =
      Torus.scaleSpacing s.data.L 𝒮.ξ i := fun i => (scaleSpacing_eq_zpow h i).symm
  have hmem : SeparatedSequences.truncatedMember s.data.scales s.Ω 1 = s.Ω 1 := by
    by_cases h1 : 1 ≤ s.data.t
    · exact if_pos h1
    · have he : s.Ω 1 = ∅ := s.Ω_mem.2.2 1 (by omega)
      rw [he]
      exact if_neg h1
  have hone : (𝒮.Ω 1)ᶜ =
      rescale s '' (SeparatedSequences.truncatedMember s.data.scales s.Ω 1)ᶜ := by
    rw [hmem, Ω_eq_image h, image_compl_eq (rescale s).bijective]
  show _ = SeparatedSequences.layerWeightedLength s.data.scales s.Ω Γ
  rw [Torus.chainWeightedLength, SeparatedSequences.layerWeightedLength, h.t_eq, hone,
    lengthWithin_rescale_image, hin, hun 0]
  congr 1
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [← rescale_image_layerAt h hT n, lengthWithin_rescale_image, hin, hun]
theorem chainLength_nonneg (hT : Torus.PartitionsHold) (Γ : List TorusMetric.LiftedSegment) :
    0 ≤ s.data.chainLength s.Ω Γ := by
  have hsp : ∀ i : ℤ, 0 ≤ (Torus.scaleSpacing s.data.L 𝒮.ξ i)⁻¹ := fun i => by
    rw [scaleSpacing_eq_zpow h]
    exact inv_nonneg.mpr (zpow_pos (Lreal_pos s) _).le
  rw [← chainWeightedLength_map h hT, Torus.chainWeightedLength]
  exact add_nonneg (Finset.sum_nonneg fun n _ => mul_nonneg (hsp _) (lengthWithin_nonneg _ _))
    (mul_nonneg (hsp _) (lengthWithin_nonneg _ _))
theorem blockDist_eq (hT : Torus.PartitionsHold) (x y : s.data.Point) :
    ENNReal.ofReal (𝒮.blockDist (rescale s x) (rescale s y)) = s.data.chainDist s.Ω x y := by
  let A : Set (List TorusMetric.LiftedSegment) :=
    {Γ | TorusMetric.IsTreeGraph (PeriodicLattice.torusSide s.data.L s.data.m) Γ ∧
      x ∈ TorusMetric.segmentsSupport (PeriodicLattice.torusSide s.data.L s.data.m) Γ ∧
      y ∈ TorusMetric.segmentsSupport (PeriodicLattice.torusSide s.data.L s.data.m) Γ}
  have hR : {r | ∃ Γ : List (Torus.TorusSegment 4),
      IsConnected (Torus.segmentUnion s.unitTorusSide Γ) ∧
      rescale s x ∈ Torus.segmentUnion s.unitTorusSide Γ ∧
      rescale s y ∈ Torus.segmentUnion s.unitTorusSide Γ ∧
      r = Torus.chainWeightedLength s.data.L 𝒮.ξ 𝒮.t 𝒮.Ω Γ} =
      s.data.chainLength s.Ω '' A := by
    ext r
    constructor
    · rintro ⟨Γ', hc, hx, hy, rfl⟩
      obtain ⟨Γ, rfl⟩ := (List.map_surjective_iff.2 (scaleSegmentDir_surjective s)) Γ'
      rw [segmentUnion_map] at hc hx hy
      rw [(rescale s).injective.mem_set_image] at hx hy
      exact ⟨Γ, ⟨(rescale s).isConnected_image.1 hc, hx, hy⟩,
        (chainWeightedLength_map h hT Γ).symm⟩
    · rintro ⟨Γ, ⟨hc, hx, hy⟩, rfl⟩
      refine ⟨Γ.map s.scaleSegmentDir, ?_, ?_, ?_, (chainWeightedLength_map h hT Γ).symm⟩
      · rw [segmentUnion_map]
        exact (rescale s).isConnected_image.2 hc
      · rw [segmentUnion_map, (rescale s).injective.mem_set_image]
        exact hx
      · rw [segmentUnion_map, (rescale s).injective.mem_set_image]
        exact hy
  have hA : A.Nonempty := exists_isTreeGraph_mem s x y
  have hdist : 𝒮.blockDist (rescale s x) (rescale s y) =
      sInf (s.data.chainLength s.Ω '' A) := by
    rw [← hR]
    rfl
  have hbdd : BddBelow (s.data.chainLength s.Ω '' A) :=
    ⟨0, by rintro _ ⟨Γ, -, rfl⟩; exact chainLength_nonneg h hT Γ⟩
  rw [hdist, Monotone.map_csInf_of_continuousAt ENNReal.continuous_ofReal.continuousAt
    ENNReal.ofReal_mono (hA.image _) hbdd, image_image, sInf_image]
  rfl
end BlockSettingOfSide
theorem statement_holds (hT : Torus.PartitionsHold) (hC : BlockStructureStatement) :
    Statement := by
  intro s 𝒮 h
  have hspace : ∀ n : ℕ, 𝒮.scaleAt n =
      s.unitScale * PeriodicLattice.meshSize s.data.L
        (PeriodicLattice.levelDepth s.data.cutoff n) :=
    scaleSpacing_eq_meshSize h
  refine
    { sublattices := ?_, partitions := ?_, blockPartitions := ?_, layers := ?_,
      layerSites := ?_, allLayerSites := ?_, meshes := ?_, blocks := ?_,
      doubledBlocks := ?_, lengths := ?_, distances := ?_ }
  · intro n _
    rw [toTorus_eq_rescale]
    exact rescale_image_sublattice s _ _ (hspace n)
  · intro n _
    rw [toTorus_eq_rescale]
    exact rescale_image_partition s _ _ (hspace n)
  · intro n _
    rw [toTorus_eq_rescale]
    exact rescale_image_partition s _ _ (blockScale_eq_meshSize h n)
  · intro n
    rw [toTorus_eq_rescale]
    exact rescale_image_layerAt h hT n
  · intro n _
    rw [toTorus_eq_rescale]
    exact rescale_image_layerSitesAt h hT n
  · rw [SequenceData.AllLayerSitesMatch, toTorus_eq_rescale]
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp only [ClassData.layerPts, SeparatedSequences.layerPoints, mem_iUnion,
        exists_prop] at hx
      obtain ⟨n, hn, y, hy, rfl⟩ := hx
      refine ⟨n, by rw [h.t_eq]; exact hn, ?_⟩
      rw [← rescale_image_layerSitesAt h hT]
      exact ⟨y, hy, rfl⟩
    · rintro ⟨n, hn, hp⟩
      rw [← rescale_image_layerSitesAt h hT] at hp
      obtain ⟨y, hy, rfl⟩ := hp
      refine ⟨y, ?_, rfl⟩
      simp only [ClassData.layerPts, SeparatedSequences.layerPoints, mem_iUnion, exists_prop]
      exact ⟨n, by rw [h.t_eq] at hn; exact hn, y, hy, rfl⟩
  · intro y
    rw [toTorus_eq_rescale, mesh_eq]
    exact shellSpacing_eq h hT hC y
  · intro y
    rw [toTorus_eq_rescale]
    show Torus.cubeAt (rescale s y.point)
        (Torus.shellSpacing s.data.L 𝒮.ξ 𝒮.Ω (rescale s y.point)) =
      rescale s '' {x | TorusMetric.torusSupNorm (x - y.point) ≤
        PeriodicLattice.meshSize s.data.L (PeriodicLattice.levelDepth s.data.cutoff y.level) / 2}
    rw [shellSpacing_eq h hT hC y, rescale_image_cube]
  · intro y
    rw [toTorus_eq_rescale]
    show Torus.cubeAt (rescale s y.point)
        (2 * Torus.shellSpacing s.data.L 𝒮.ξ 𝒮.Ω (rescale s y.point)) =
      rescale s '' {x | TorusMetric.torusSupNorm (x - y.point) ≤
        2 * PeriodicLattice.meshSize s.data.L
          (PeriodicLattice.levelDepth s.data.cutoff y.level) / 2}
    rw [shellSpacing_eq h hT hC y, rescale_image_cube, mul_left_comm]
  · intro Γ
    exact chainWeightedLength_map h hT Γ
  · intro x y
    rw [toTorus_eq_rescale]
    exact blockDist_eq h hT x y
end YangMills.Construction.SeparatedClasses.BlockGeometryOfClass
end
