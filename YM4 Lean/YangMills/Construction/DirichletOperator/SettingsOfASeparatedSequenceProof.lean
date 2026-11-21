import YangMills.Construction.SeparatedSequences.NumbersOfThePropagatorServeOnTheToriProof
import YangMills.Construction.DirichletOperator.CornerCubeInALayerOfASequenceProof
import YangMills.Construction.DirichletOperator.SettingsOfASeparatedSequence
import YangMills.Construction.RegionSequence.CellsAndAdjoints
import YangMills.Construction.RegionSequence.WeightedDistTriangleProof
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal Pointwise
open YangMills.Construction.Dirichlet YangMills.Construction.Torus
noncomputable section
namespace YangMills.Construction.RegionSequence
section Geometry
variable {S σ : ℝ}
theorem supNorm_lifts_nonempty {d : ℕ} (p : PeriodicTorus d S) :
    {r | ∃ v : Fin d → ℝ, torusProj d S v = p ∧ r = ‖v‖}.Nonempty := by
  choose v hv _ using fun μ => TorusMetric.exists_coe_eq_abs_eq_norm (p μ)
  exact ⟨_, v, funext hv, rfl⟩
theorem norm_apply_le_supNorm {d : ℕ} (p : PeriodicTorus d S) (μ : Fin d) : ‖p μ‖ ≤ supNorm p := by
  refine le_csInf (supNorm_lifts_nonempty p) ?_
  rintro _ ⟨v, rfl, rfl⟩
  exact (TorusMetric.addCircle_norm_coe_le_abs (v μ)).trans (norm_le_pi_norm v μ)
theorem torusProj_sub {d : ℕ} (v w : Fin d → ℝ) :
    torusProj d S v - torusProj d S w = torusProj d S (v - w) := by
  funext μ
  simp [torusProj]
end Geometry
section Whole
variable {S σ : ℝ}
end Whole
namespace NestedRegions
variable (𝒮 : NestedRegions)
theorem scale_pos (n : ℕ) : 0 < 𝒮.scale n := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.scale_pos <;> assumption
theorem side_eq_of_le_s {M n : ℕ} {k : ℤ} (hk : 𝒮.side = (k : ℝ) * (2 * ((M : ℝ) * 𝒮.scale 𝒮.s)))
    (hn : n ≤ 𝒮.s) :
    𝒮.side = ((k * (𝒮.L : ℤ) ^ (𝒮.s - n) : ℤ) : ℝ) * (2 * ((M : ℝ) * 𝒮.scale n)) := by
  rw [hk, scale_eq_pow_mul, scale_eq_pow_mul]
  have : (𝒮.L : ℝ) ^ 𝒮.s = (𝒮.L : ℝ) ^ (𝒮.s - n) * (𝒮.L : ℝ) ^ n := by
    rw [← pow_add, Nat.sub_add_cancel hn]
  rw [this]
  push_cast
  ring
theorem pos_of_side_eq {M : ℕ} {k : ℤ} (hM : 0 < M)
    (hk : 𝒮.side = (k : ℝ) * (2 * ((M : ℝ) * 𝒮.scale 𝒮.s))) : 0 < k := by
  have h1 : 0 < (M : ℝ) * 𝒮.scale 𝒮.s := mul_pos (by exact_mod_cast hM) (𝒮.scale_pos _)
  have h2 : (0 : ℝ) < k := by
    by_contra h
    have : (k : ℝ) * (2 * ((M : ℝ) * 𝒮.scale 𝒮.s)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (not_lt.mp h) (by positivity)
    have := 𝒮.side_pos
    linarith
  exact_mod_cast h2
end NestedRegions
namespace NestedRegions
variable (𝒮 : NestedRegions)
theorem exists_cube_count {μ n : ℕ} {k : ℤ} (hM0 : 0 < 𝒮.L ^ μ)
    (hk : 𝒮.side = (k : ℝ) * (2 * (((𝒮.L ^ μ : ℕ) : ℝ) * 𝒮.scale 𝒮.s))) (hn : n ≤ 𝒮.s) :
    ∃ a : ℕ, 0 < a ∧ 𝒮.side = ((a : ℤ) : ℝ) * (2 * (((𝒮.L ^ μ : ℕ) : ℝ) * 𝒮.scale n)) := by
  have h13 := 𝒮.thirteen_le_L
  have hkpos := 𝒮.pos_of_side_eq hM0 hk
  have hp : 0 < k * (𝒮.L : ℤ) ^ (𝒮.s - n) := mul_pos hkpos (pow_pos (by omega) _)
  refine ⟨(k * (𝒮.L : ℤ) ^ (𝒮.s - n)).toNat, by omega, ?_⟩
  rw [Int.toNat_of_nonneg hp.le]
  exact 𝒮.side_eq_of_le_s hk hn
end NestedRegions
end YangMills.Construction.RegionSequence
namespace YangMills.Construction.RegionSequence.NestedRegions
variable {𝒮 : NestedRegions}
theorem lastNonemptyIndex_le {d : ℕ} {S : ℝ} {Ω : ℕ → Set (PeriodicTorus d S)} {s : ℕ}
    (h : ∀ n, s < n → Ω n = ∅) : lastNonemptyIndex Ω ≤ s := by
  refine csSup_le' ?_
  intro n hn
  by_contra hlt
  have := h n (not_le.mp hlt)
  rw [Set.mem_ofPred_eq, this] at hn
  exact Set.not_nonempty_empty hn
theorem le_lastNonemptyIndex {d : ℕ} {S : ℝ} {Ω : ℕ → Set (PeriodicTorus d S)} {s n : ℕ}
    (h : ∀ n, s < n → Ω n = ∅) (hn : (Ω n).Nonempty) : n ≤ lastNonemptyIndex Ω := by
  refine le_csSup ⟨s, ?_⟩ hn
  intro k hk
  by_contra hlt
  have := h k (not_le.mp hlt)
  rw [Set.mem_ofPred_eq, this] at hk
  exact Set.not_nonempty_empty hk
theorem lengthWithin_empty {d : ℕ} {S : ℝ} (Γ : List (TorusSegment d)) :
    lengthWithin Γ (∅ : Set (PeriodicTorus d S)) = 0 := by
  simp [lengthWithin]
section End
variable {s' : ℕ} (h : 𝒮.EndsAt s')
theorem EndsAt.allCentres_eq : 𝒮.allCentres = h.truncate.allCentres := by
  have htop : lastNonemptyIndex 𝒮.Ω ≤ s' := lastNonemptyIndex_le h.Ω_eq_empty_of_lt
  have htop' : lastNonemptyIndex 𝒮.Ω ≤ 𝒮.s := lastNonemptyIndex_le 𝒮.Ω_eq_empty
  ext y
  constructor
  · rintro ⟨n, -, hy⟩
    exact ⟨n, hy.1.trans htop, hy⟩
  · rintro ⟨n, -, hy⟩
    exact ⟨n, hy.1.trans htop', hy⟩
theorem EndsAt.mem_allCentres {y : 𝒮.Point} (hy : y ∈ 𝒮.allCentres) : y ∈ h.truncate.allCentres :=
  h.allCentres_eq ▸ hy
theorem EndsAt.coarseInner_eq (ω₁ ω₂ : 𝒮.Coarse) (ω₁' ω₂' : h.truncate.Coarse)
    (h₁ : EqOnCentres h ω₁ ω₁') (h₂ : EqOnCentres h ω₂ ω₂') :
    coarseInner ω₁ ω₂ = coarseInner (𝒮 := h.truncate) ω₁' ω₂' := by
  refine (finsum_congr fun y => ?_).trans (finsum_comp_equiv (Equiv.setCongr h.allCentres_eq)
    (f := fun y : h.truncate.allCentres => h.truncate.levelScale y ^ 4 * ω₁' y * ω₂' y))
  have e₁ := h₁ y.1 y.2 (h.mem_allCentres y.2)
  have e₂ := h₂ y.1 y.2 (h.mem_allCentres y.2)
  show 𝒮.levelScale y.1 ^ 4 * ω₁ y * ω₂ y = 𝒮.levelScale y.1 ^ 4 * ω₁' ⟨y.1, _⟩ * ω₂' ⟨y.1, _⟩
  rw [← e₁, ← e₂]
theorem EndsAt.eqOnCentres_blockAvg (f : 𝒮.FineSite → ℝ) :
    EqOnCentres h (blockAvg f) (blockAvg (𝒮 := h.truncate) f) :=
  fun _ _ _ => rfl
theorem EndsAt.blockAvgAdj_eq (ω : 𝒮.Coarse) (ω' : h.truncate.Coarse)
    (hω : EqOnCentres h ω ω') :
    blockAvgAdj ω = blockAvgAdj (𝒮 := h.truncate) ω' := by
  unfold blockAvgAdj adjointValue
  refine congrArg Classical.epsilon (funext fun v => propext (and_congr_right fun _ => ?_))
  refine forall₂_congr fun u _ => ?_
  rw [h.coarseInner_eq ω (blockAvg u) ω' (blockAvg (𝒮 := h.truncate) u) hω
    (h.eqOnCentres_blockAvg u)]
  exact Iff.rfl
theorem EndsAt.eqOnCentres_weightMul (ω : 𝒮.Coarse) (ω' : h.truncate.Coarse)
    (hω : EqOnCentres h ω ω') :
    EqOnCentres h (weightMul ω) (weightMul (𝒮 := h.truncate) ω') := by
  intro y hy hy'
  have := hω y hy hy'
  show blockWeights 𝒮.L (𝒮.level y) * (𝒮.scale (𝒮.level y) ^ 2)⁻¹ * ω ⟨y, hy⟩ =
    blockWeights 𝒮.L (𝒮.level y) * (𝒮.scale (𝒮.level y) ^ 2)⁻¹ * ω' ⟨y, hy'⟩
  rw [this]
theorem EndsAt.gaugeLap_eq (f : 𝒮.FineSite → ℝ) :
    gaugeLap f = gaugeLap (𝒮 := h.truncate) f :=
  congrArg (fun g : 𝒮.FineSite → ℝ => dirichletLap f + g)
    (h.blockAvgAdj_eq _ _ (h.eqOnCentres_weightMul _ _ (h.eqOnCentres_blockAvg f)))
theorem EndsAt.gaugeGreenOp_eq (f : 𝒮.FineSite → ℝ) :
    gaugeGreenOp f = gaugeGreenOp (𝒮 := h.truncate) f := by
  unfold gaugeGreenOp inverseValue
  refine congrArg Classical.epsilon (funext fun g => propext (and_congr_right fun _ => ?_))
  rw [h.gaugeLap_eq g]
  exact Iff.rfl
theorem EndsAt.avgKernel_eq : 𝒮.avgKernel = h.truncate.avgKernel := by
  ext f
  refine and_congr_right fun _ => ?_
  constructor
  · intro hf
    funext y
    exact (h.eqOnCentres_blockAvg f y.1 (h.allCentres_eq.symm ▸ y.2) y.2).symm.trans (congrFun hf _)
  · intro hf
    funext y
    exact (h.eqOnCentres_blockAvg f y.1 y.2 (h.mem_allCentres y.2)).trans (congrFun hf _)
theorem EndsAt.rangeProj_eq (f : 𝒮.FineSite → ℝ) :
    rangeProj f = rangeProj (𝒮 := h.truncate) f :=
  congrArg (fun K : Set (𝒮.FineSite → ℝ) =>
    orthProjValue (dirichletLap '' K) innerSum f) h.avgKernel_eq
theorem EndsAt.complProj_eq (f : 𝒮.FineSite → ℝ) :
    complProj f = complProj (𝒮 := h.truncate) f :=
  congrArg (fun g : 𝒮.FineSite → ℝ => f - g) (h.rangeProj_eq f)
theorem EndsAt.avgForm_eq (A A' : 𝒮.FineBond → ℝ) :
    avgForm A A' = avgForm (𝒮 := h.truncate) A A' := by
  symm
  refine Finset.sum_subset (Finset.range_subset_range.mpr (by
    have := h.le_s
    show s' + 1 ≤ 𝒮.s + 1
    omega)) ?_
  intro n _ hn
  have hlt : s' < n := by
    have : ¬ n < s' + 1 := fun hh => hn (Finset.mem_range.mpr hh)
    omega
  have hr : h.truncate.coarseBonds n = ∅ := h.truncate.coarseBonds_eq_empty_of_lt hlt
  refine (finsum_congr fun c => ?_).trans finsum_zero
  have hc : c ∉ h.truncate.coarseBonds n := by
    rw [hr]
    exact Set.notMem_empty c
  have : IsEmpty (c ∈ h.truncate.coarseBonds n) := ⟨hc⟩
  exact finsum_of_isEmpty _
theorem EndsAt.avgOp_eq (A : 𝒮.FineBond → ℝ) :
    avgOp A = avgOp (𝒮 := h.truncate) A := by
  unfold avgOp
  refine congrArg Classical.epsilon (funext fun B => propext (and_congr_right fun _ => ?_))
  refine forall₂_congr fun A' _ => ?_
  rw [h.avgForm_eq A A']
  exact Iff.rfl
theorem EndsAt.baseOp_eq (A : 𝒮.FineBond → ℝ) :
    baseOp A = baseOp (𝒮 := h.truncate) A := by
  have e₁ := h.rangeProj_eq (dDirAdj A)
  have e₂ := h.avgOp_eq A
  show curlSqDir A + dDir (rangeProj (dDirAdj A)) + avgOp A = _
  rw [e₁, e₂]
  rfl
theorem EndsAt.baseGreen_eq (A : 𝒮.FineBond → ℝ) :
    baseGreen A = baseGreen (𝒮 := h.truncate) A := by
  unfold baseGreen inverseValue
  refine congrArg Classical.epsilon (funext fun g => propext (and_congr_right fun _ => ?_))
  rw [h.baseOp_eq g]
  exact Iff.rfl
theorem EndsAt.chainWeight_eq (Γ : List (TorusSegment 4)) :
    𝒮.chainWeight Γ = h.truncate.chainWeight Γ := by
  have hsum : ∑ n ∈ Finset.Icc 1 s', (𝒮.scale n)⁻¹ * lengthWithin Γ (𝒮.shellOf n) =
      ∑ n ∈ Finset.Icc 1 𝒮.s, (𝒮.scale n)⁻¹ * lengthWithin Γ (𝒮.shellOf n) := by
    refine Finset.sum_subset (Finset.Icc_subset_Icc_right h.le_s) ?_
    intro n _ hn
    have hlt : s' < n := by
      by_contra hle
      simp only [Finset.mem_Icc, not_and] at hn
      rename_i hn'
      exact hn (Finset.mem_Icc.mp hn').1 (not_lt.mp hle)
    have hl : 𝒮.shellOf n = ∅ := h.truncate.shellOf_eq_empty_of_lt hlt
    rw [hl, lengthWithin_empty, mul_zero]
  show _ = ∑ n ∈ Finset.Icc 1 s', (𝒮.scale n)⁻¹ * lengthWithin Γ (𝒮.shellOf n) +
    𝒮.ξ⁻¹ * lengthWithin Γ (𝒮.Ω 1)ᶜ
  rw [hsum]
  rfl
theorem EndsAt.weightedDist_eq (y y' : 𝒮.Point) :
    𝒮.weightedDist y y' = h.truncate.weightedDist y y' := by
  unfold weightedDist
  refine congrArg sInf (Set.ext fun r => ?_)
  refine exists_congr fun Γ => and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ => ?_
  rw [h.chainWeight_eq Γ]
end End
end YangMills.Construction.RegionSequence.NestedRegions
namespace YangMills.Construction.RegionSequence
section Compare
variable {S : ℝ}
theorem supNormVec_eq_norm (v : Fin 4 → ℝ) : TorusMetric.supNormVec v = ‖v‖ := by apply _root_.YangMills.Construction.LevelUnitFacts.supNormVec_eq_norm <;> assumption
theorem supNorm_eq_torusSupNorm (p : PeriodicTorus 4 S) : supNorm p = TorusMetric.torusSupNorm p := by apply _root_.YangMills.Construction.GeneralTorus.GreenBounds.FromPropagator.supNorm_eq_torusSupNorm <;> assumption
theorem pointAt_segmentToLifted (s : TorusSegment 4) (τ : ℝ) :
    s.pointAt S τ = (segmentToLifted s).pointAt S τ := by
  show torusProj 4 S _ = TorusMetric.torusProj S _
  have : TorusMetric.LiftedSegment.displacement (segmentToLifted s) = s.direction := by
    simp [TorusMetric.LiftedSegment.displacement, segmentToLifted]
  rw [this]
  rfl
end Compare
end YangMills.Construction.RegionSequence
namespace YangMills.Construction.RegionSequence.NestedRegions
variable {𝒮 : NestedRegions} {M R₁ : ℕ}
section Same
variable (hcells : CellStructure.CellStructureClaim) (hs : 𝒮.IsGapSeparated M R₁)
end Same
theorem IsGapSeparated.isSeparatedChain (hs : 𝒮.IsGapSeparated M R₁) (hne : (𝒮.Ω 0).Nonempty) :
    IsSeparatedChain 𝒮.L 𝒮.ξ M R₁ 𝒮.s 𝒮.Ω := by
  have h13 := 𝒮.thirteen_le_L
  have htop : lastNonemptyIndex 𝒮.Ω ≤ 𝒮.s := lastNonemptyIndex_le 𝒮.Ω_eq_empty
  refine ⟨𝒮.ξ_pos, 𝒮.side_pos, hs.isPowerGe_block, hs.isPowerGe_gap, hne, 𝒮.Ω_succ_subset,
    𝒮.Ω_eq_empty, ?_, ?_, hs.gap_lt⟩
  · obtain ⟨-, μ, hμ⟩ := hs.isPowerGe_block
    obtain ⟨k, hk⟩ := hs.side_mem_grid
    have hM0 : 0 < M := by have := hs.isPowerGe_block.1; omega
    have hkpos := 𝒮.pos_of_side_eq hM0 hk
    have he := 𝒮.side_eq_of_le_s hk htop
    have hp : 0 < k * (𝒮.L : ℤ) ^ (𝒮.s - lastNonemptyIndex 𝒮.Ω) :=
      mul_pos hkpos (pow_pos (by omega) _)
    refine ⟨(k * (𝒮.L : ℤ) ^ (𝒮.s - lastNonemptyIndex 𝒮.Ω)).toNat, by omega, ?_⟩
    have e : (((k * (𝒮.L : ℤ) ^ (𝒮.s - lastNonemptyIndex 𝒮.Ω)).toNat : ℕ) : ℝ) =
        ((k * (𝒮.L : ℤ) ^ (𝒮.s - lastNonemptyIndex 𝒮.Ω) : ℤ) : ℝ) := by
      have := Int.toNat_of_nonneg hp.le
      exact_mod_cast this
    rw [e]
    refine he.trans ?_
    show _ * (2 * ((M : ℝ) * 𝒮.scale _)) = 2 * _ * ((M : ℝ) * 𝒮.scale _)
    ring
  · intro n hn
    exact hs.Ω_eq_sUnion n (hn.trans htop)
theorem chainWeight_nonneg (𝒮 : NestedRegions) (Γ : List (TorusSegment 4)) : 0 ≤ 𝒮.chainWeight Γ := by apply _root_.YangMills.Construction.RegionSequence.WeightedDist.chainWeight_nonneg <;> assumption
end YangMills.Construction.RegionSequence.NestedRegions
namespace YangMills.Construction.RegionSequence
section Dilation
variable {p q : ℝ} (hp : p ≠ 0) (hq : q ≠ 0)
def torusDilation (x : Fin 4 → AddCircle p) : PeriodicTorus 4 q :=
  fun μ => AddCircle.equivAddCircle p q hp hq (x μ)
theorem torusDilation_bijective : Function.Bijective (torusDilation hp hq) :=
  ⟨fun _ _ h => funext fun μ => (AddCircle.equivAddCircle p q hp hq).injective (congrFun h μ),
    fun y => ⟨fun μ => (AddCircle.equivAddCircle p q hp hq).symm (y μ),
      funext fun μ => by simp [torusDilation]⟩⟩
theorem torusDilation_sub (x y : Fin 4 → AddCircle p) :
    torusDilation hp hq (x - y) = torusDilation hp hq x - torusDilation hp hq y :=
  funext fun _ => map_sub _ _ _
theorem torusDilation_torusProj (v : Fin 4 → ℝ) :
    torusDilation hp hq (TorusMetric.torusProj p v) = torusProj 4 q fun μ => v μ * (p⁻¹ * q) :=
  funext fun _ => AddCircle.equivAddCircle_apply_mk p q hp hq _
theorem supNorm_torusDilation (hc : 0 < p⁻¹ * q) (x : Fin 4 → AddCircle p) :
    supNorm (torusDilation hp hq x) = (p⁻¹ * q) * TorusMetric.torusSupNorm x := by
  set c := p⁻¹ * q with hcdef
  have hset : {r | ∃ v : Fin 4 → ℝ, torusProj 4 q v = torusDilation hp hq x ∧ r = ‖v‖} =
      c • (TorusMetric.supNormVec '' (TorusMetric.torusProj p ⁻¹' {x})) := by
    ext r
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨_, ⟨fun μ => v μ * c⁻¹, ?_, rfl⟩, ?_⟩
      · apply (torusDilation_bijective hp hq).1
        rw [torusDilation_torusProj, ← hv]
        congr 1
        funext μ
        rw [← hcdef]
        field_simp
      · show c • TorusMetric.supNormVec _ = ‖v‖
        rw [supNormVec_eq_norm]
        have e : v = c • fun μ => v μ * c⁻¹ := by
          funext μ
          simp only [Pi.smul_apply, smul_eq_mul]
          field_simp
        conv_rhs => rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
        rfl
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      refine ⟨fun μ => w μ * c, ?_, ?_⟩
      · have hw' : TorusMetric.torusProj p w = x := hw
        rw [← hw', torusDilation_torusProj]
      · show c • TorusMetric.supNormVec _ = _
        rw [supNormVec_eq_norm]
        have e : (fun μ => w μ * c) = c • w := by
          funext μ
          simp [mul_comm]
        rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
        rfl
  unfold supNorm TorusMetric.torusSupNorm
  rw [hset, Real.sInf_smul_of_nonneg hc.le]
  rfl
theorem torusDilation_image_ball (hc : 0 < p⁻¹ * q) (y : Fin 4 → AddCircle p) (a : ℝ) :
    torusDilation hp hq '' {x | TorusMetric.torusSupNorm (x - y) ≤ a / 2} =
      cubeAt (torusDilation hp hq y) ((p⁻¹ * q) * a) := by
  ext z
  obtain ⟨x, rfl⟩ := (torusDilation_bijective hp hq).2 z
  rw [(torusDilation_bijective hp hq).1.mem_set_image]
  show TorusMetric.torusSupNorm (x - y) ≤ a / 2 ↔ supNorm _ ≤ _
  rw [← torusDilation_sub, supNorm_torusDilation hp hq hc, mul_div_assoc]
  exact (mul_le_mul_iff_right₀ hc).symm
theorem supSetDist_torusDilation (hc : 0 < p⁻¹ * q) (A B : Set (Fin 4 → AddCircle p)) :
    supSetDist (torusDilation hp hq '' A) (torusDilation hp hq '' B) =
      ENNReal.ofReal (p⁻¹ * q) * TorusMetric.setSupDist A B := by
  have h0 : ENNReal.ofReal (p⁻¹ * q) ≠ 0 := by simpa using hc
  have hT : ENNReal.ofReal (p⁻¹ * q) ≠ ⊤ := ENNReal.ofReal_ne_top
  unfold supSetDist TorusMetric.setSupDist
  simp only [iInf_image, ENNReal.mul_iInf_of_ne h0 hT, ← torusDilation_sub,
    supNorm_torusDilation hp hq hc, ENNReal.ofReal_mul hc.le]
def scaleSegment (c : ℝ) (s : TorusMetric.LiftedSegment) : TorusSegment 4 :=
  ⟨fun μ => s.tail μ * c, fun μ => (s.head μ - s.tail μ) * c⟩
theorem pointAt_scaleSegment (s : TorusMetric.LiftedSegment) (τ : ℝ) :
    (scaleSegment (p⁻¹ * q) s).pointAt q τ = torusDilation hp hq (s.pointAt p τ) := by
  show torusProj 4 q _ = torusDilation hp hq (TorusMetric.torusProj p _)
  rw [torusDilation_torusProj]
  congr 1
  funext μ
  simp [scaleSegment, TorusMetric.LiftedSegment.displacement]
  ring
end Dilation
end YangMills.Construction.RegionSequence
namespace YangMills.Construction.RegionSequence
section LatticeDilation
variable {L m : ℕ} {q : ℝ} (hp : PeriodicLattice.torusSide L m ≠ 0) (hq : q ≠ 0)
theorem image_standardCubePartition (hc : 0 < (PeriodicLattice.torusSide L m)⁻¹ * q) (i : ℤ) :
    (fun Q => torusDilation hp hq '' Q) '' PeriodicLattice.standardCubePartition L m i =
      cubePartition 4 q (((PeriodicLattice.torusSide L m)⁻¹ * q) * PeriodicLattice.meshSize L i) := by
  ext Q
  constructor
  · rintro ⟨_, ⟨⟨x, k, hk⟩, rfl⟩, rfl⟩
    refine ⟨torusDilation hp hq x, ⟨k, ?_⟩, torusDilation_image_ball hp hq hc x _⟩
    have hx : x = TorusMetric.torusProj _ fun μ => (k μ : ℝ) * PeriodicLattice.meshSize L i :=
      funext hk
    rw [hx, torusDilation_torusProj]
    congr 1
    funext μ
    ring
  · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
    refine ⟨_, ⟨⟨TorusMetric.torusProj _ fun μ => (k μ : ℝ) * PeriodicLattice.meshSize L i,
      k, fun _ => rfl⟩, rfl⟩, ?_⟩
    refine (torusDilation_image_ball hp hq hc _ _).trans ?_
    rw [torusDilation_torusProj]
    congr 2
    funext μ
    ring
theorem isCubeUnion_image (hc : 0 < (PeriodicLattice.torusSide L m)⁻¹ * q) {i : ℤ}
    {X : Set (PeriodicLattice.FourTorus L m)} (hX : PeriodicLattice.IsPartitionRegion i X) :
    IsCubeUnion (((PeriodicLattice.torusSide L m)⁻¹ * q) * PeriodicLattice.meshSize L i)
      (torusDilation hp hq '' X) := by
  obtain ⟨C, hC, rfl⟩ := hX
  refine ⟨(fun Q => torusDilation hp hq '' Q) '' C, ?_, ?_⟩
  · rw [← image_standardCubePartition hp hq hc]
    exact image_mono hC
  · ext z
    constructor
    · rintro ⟨x, ⟨Q, hQ, hx⟩, rfl⟩
      exact ⟨_, ⟨Q, hQ, rfl⟩, x, hx, rfl⟩
    · rintro ⟨_, ⟨Q, hQ, rfl⟩, x, hx, rfl⟩
      exact ⟨x, ⟨Q, hQ, hx⟩, rfl⟩
theorem image_complementRegion (hc : 0 < (PeriodicLattice.torusSide L m)⁻¹ * q) (i : ℤ)
    (X : Set (PeriodicLattice.FourTorus L m)) :
    torusDilation hp hq '' PeriodicLattice.complementRegion i X =
      cubeComplement (((PeriodicLattice.torusSide L m)⁻¹ * q) * PeriodicLattice.meshSize L i)
        (torusDilation hp hq '' X) := by
  have hinj := (torusDilation_bijective hp hq).1
  ext z
  constructor
  · rintro ⟨x, ⟨Q, ⟨hQ, hn⟩, hx⟩, rfl⟩
    refine ⟨torusDilation hp hq '' Q, ⟨?_, ?_⟩, x, hx, rfl⟩
    · rw [← image_standardCubePartition hp hq hc]
      exact ⟨Q, hQ, rfl⟩
    · intro hsub
      exact hn ⟨hQ, (image_subset_image_iff hinj).mp hsub⟩
  · rintro ⟨Q', ⟨hQ', hn⟩, hz⟩
    rw [← image_standardCubePartition hp hq hc] at hQ'
    obtain ⟨Q, hQ, rfl⟩ := hQ'
    obtain ⟨x, hx, rfl⟩ := hz
    exact ⟨x, ⟨Q, ⟨hQ, fun h => hn (image_mono h.2)⟩, hx⟩, rfl⟩
end LatticeDilation
end YangMills.Construction.RegionSequence
namespace YangMills.Construction.Propagator.SeparatedRegionChain
open YangMills.Construction.RegionSequence
variable (P : SeparatedRegionChain)
abbrev dilationFactor : ℝ := (PeriodicLattice.torusSide P.L P.m)⁻¹ * P.sideInUnits
theorem cast_L_ne_zero : (P.L : ℝ) ≠ 0 := P.L_pos.ne'
theorem dilationFactor_eq :
    P.dilationFactor = (P.L : ℝ) ^ PeriodicLattice.levelDepth P.K P.level := by
  have hL := P.cast_L_ne_zero
  have e : (((P.m : ℕ) : ℤ) + ((P.K : ℕ) : ℤ) - (P.level : ℤ)) =
      ((P.m : ℕ) : ℤ) + PeriodicLattice.levelDepth P.K P.level := by
    simp only [PeriodicLattice.levelDepth]
    ring
  show (2 * (P.L : ℝ) ^ (P.m : ℕ))⁻¹ *
    (2 * (P.L : ℝ) ^ (((P.m : ℕ) : ℤ) + ((P.K : ℕ) : ℤ) - (P.level : ℤ))) = _
  rw [e, zpow_add₀ hL, zpow_natCast]
  field_simp
theorem dilationFactor_pos : 0 < P.dilationFactor := by
  rw [dilationFactor_eq]
  exact zpow_pos P.L_pos _
theorem scaleSpacing_baseMesh (n : ℕ) :
    scaleSpacing P.L P.baseMesh n = (P.L : ℝ) ^ ((n : ℤ) - (P.level : ℤ)) := by
  show (P.L : ℝ) ^ (n : ℤ) * (P.L : ℝ) ^ (-(P.level : ℤ)) = _
  rw [← zpow_add₀ P.cast_L_ne_zero, sub_eq_add_neg]
theorem cast_blockCount : (P.blockCount : ℝ) = (P.L : ℝ) ^ (P.blockExponent : ℤ) := by
  simp [blockCount]
theorem dilationFactor_mul_meshSize (n : ℕ) :
    P.dilationFactor * PeriodicLattice.meshSize P.L (P.scaleData.blockPartitionIndex n) =
      (P.blockCount : ℝ) * scaleSpacing P.L P.baseMesh n := by
  rw [dilationFactor_eq, scaleSpacing_baseMesh, cast_blockCount]
  show (P.L : ℝ) ^ _ * (P.L : ℝ) ^ _ = _
  rw [← zpow_add₀ P.cast_L_ne_zero, ← zpow_add₀ P.cast_L_ne_zero]
  congr 1
  simp only [SeparatedSequences.ScaleData.blockPartitionIndex, PeriodicLattice.scaledCubeIndex,
    PeriodicLattice.levelDepth, scaleData]
  ring
theorem exists_cube_count {n : ℕ} (h : -((P.m : ℕ) : ℤ) ≤ P.scaleData.blockPartitionIndex n) :
    ∃ a : ℕ, 0 < a ∧ P.sideInUnits =
      ((a : ℤ) : ℝ) * (2 * (((P.L ^ P.blockExponent : ℕ) : ℝ) * scaleSpacing P.L P.baseMesh n)) := by
  have h0 : 0 ≤ ((P.m : ℕ) : ℤ) + P.scaleData.blockPartitionIndex n := by omega
  obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le h0
  have hLp : 0 < P.L := by exact_mod_cast P.L_pos
  refine ⟨P.L ^ j, pow_pos hLp _, ?_⟩
  have e₁ : (((P.L ^ j : ℕ) : ℤ) : ℝ) = (P.L : ℝ) ^ (j : ℤ) := by simp
  have e₂ : ((P.L ^ P.blockExponent : ℕ) : ℝ) = (P.L : ℝ) ^ (P.blockExponent : ℤ) := by simp
  rw [e₁, e₂, scaleSpacing_baseMesh]
  show 2 * (P.L : ℝ) ^ (((P.m : ℕ) : ℤ) + ((P.K : ℕ) : ℤ) - (P.level : ℤ)) = _
  have : (P.L : ℝ) ^ (j : ℤ) * (2 * ((P.L : ℝ) ^ (P.blockExponent : ℤ) *
      (P.L : ℝ) ^ ((n : ℤ) - (P.level : ℤ)))) =
      2 * ((P.L : ℝ) ^ (j : ℤ) * ((P.L : ℝ) ^ (P.blockExponent : ℤ) *
      (P.L : ℝ) ^ ((n : ℤ) - (P.level : ℤ)))) := by ring
  rw [this, ← zpow_add₀ P.cast_L_ne_zero, ← zpow_add₀ P.cast_L_ne_zero]
  congr 2
  rw [← hj]
  simp only [SeparatedSequences.ScaleData.blockPartitionIndex, PeriodicLattice.scaledCubeIndex,
    PeriodicLattice.levelDepth, scaleData]
  ring
theorem regionInUnits_eq_empty {n : ℕ} (h : P.Ω n = ∅) : P.regionInUnits n = ∅ := by
  simp [regionInUnits, h]
theorem isCubeUnion_block {n : ℕ} (hn : n ≤ P.level) :
    IsCubeUnion ((P.blockCount : ℝ) * scaleSpacing P.L P.baseMesh n) (P.regionInUnits n) := by
  rcases P.separated.1 n hn with h | ⟨-, h⟩
  · rw [P.regionInUnits_eq_empty h]
    exact ⟨∅, empty_subset _, sUnion_empty.symm⟩
  · rw [← dilationFactor_mul_meshSize]
    exact isCubeUnion_image P.torusSide_ne_zero P.sideInUnits_pos.ne' P.dilationFactor_pos h
end YangMills.Construction.Propagator.SeparatedRegionChain
namespace YangMills.Construction.Propagator.SeparatedRegionChain
open YangMills.Construction.RegionSequence
variable (P : SeparatedRegionChain)
theorem regionInUnits_nonempty_iff (n : ℕ) : (P.regionInUnits n).Nonempty ↔ (P.Ω n).Nonempty := by
  simp [regionInUnits]
theorem regionInUnits_eq_empty_of_lt (n : ℕ) (hn : P.level < n) : P.regionInUnits n = ∅ :=
  P.regionInUnits_eq_empty (P.empty_past n hn)
theorem lastNonemptyIndex_le_level : lastNonemptyIndex P.regionInUnits ≤ P.level :=
  NestedRegions.lastNonemptyIndex_le P.regionInUnits_eq_empty_of_lt
theorem Ω_lastNonemptyIndex_nonempty : (P.Ω (lastNonemptyIndex P.regionInUnits)).Nonempty := by
  rw [← regionInUnits_nonempty_iff]
  have hne : {n | (P.regionInUnits n).Nonempty}.Nonempty :=
    ⟨0, (P.regionInUnits_nonempty_iff 0).mpr P.first_nonempty⟩
  have hb : BddAbove {n | (P.regionInUnits n).Nonempty} := ⟨P.level, fun n hn => by
    by_contra hlt
    have := P.regionInUnits_eq_empty_of_lt n (not_le.mp hlt)
    rw [Set.mem_ofPred_eq, this] at hn
    exact Set.not_nonempty_empty hn⟩
  exact Nat.sSup_mem hne hb
theorem isSeparatedChain (hLM : P.L ≤ P.blockCount) :
    IsSeparatedChain P.L P.baseMesh P.blockCount P.gapSize P.level P.regionInUnits := by
  refine ⟨P.baseMesh_pos, P.sideInUnits_pos, ⟨hLM, _, rfl⟩, ⟨P.le_gapNumber, _, rfl⟩,
    (P.regionInUnits_nonempty_iff 0).mpr P.first_nonempty,
    fun n hn => image_mono (P.separated.2 n hn).1, P.regionInUnits_eq_empty_of_lt, ?_,
    fun n hn => P.isCubeUnion_block (hn.trans P.lastNonemptyIndex_le_level), ?_⟩
  · have htop := P.lastNonemptyIndex_le_level
    rcases P.separated.1 _ htop with h | ⟨h₁, -⟩
    · exact absurd h P.Ω_lastNonemptyIndex_nonempty.ne_empty
    · obtain ⟨a, ha, he⟩ := P.exists_cube_count h₁
      refine ⟨a, ha, he.trans ?_⟩
      show _ = _ * ((P.blockCount : ℝ) * _)
      simp only [blockCount]
      push_cast
      ring
  · intro n hn
    by_cases hne : (P.Ω (n + 1)).Nonempty
    · have hnon : (P.Ω n).Nonempty := hne.mono (P.separated.2 n hn).1
      have hsep := (P.separated.2 n hn).2
      rcases P.separated.1 n hn.le with h | ⟨-, -⟩
      · exact absurd h hnon.ne_empty
      · have e₁ : cubeComplement ((P.blockCount : ℝ) * scaleSpacing P.L P.baseMesh n)
            (P.regionInUnits n) =
            P.toUnits '' PeriodicLattice.complementRegion (P.scaleData.blockPartitionIndex n)
              (P.Ω n) := by
          rw [← dilationFactor_mul_meshSize]
          exact (image_complementRegion P.torusSide_ne_zero P.sideInUnits_pos.ne'
            P.dilationFactor_pos _ _).symm
        rw [e₁]
        have e₂ : supSetDist (P.toUnits '' PeriodicLattice.complementRegion
            (P.scaleData.blockPartitionIndex n) (P.Ω n)) (P.regionInUnits (n + 1)) =
            ENNReal.ofReal ((P.L : ℝ) ^ PeriodicLattice.levelDepth P.K P.level) *
            TorusMetric.setSupDist (PeriodicLattice.complementRegion
              (P.scaleData.blockPartitionIndex n) (P.Ω n)) (P.Ω (n + 1)) := by
          rw [← dilationFactor_eq]
          exact supSetDist_torusDilation P.torusSide_ne_zero P.sideInUnits_pos.ne'
            P.dilationFactor_pos _ _
        rw [e₂]
        have e₃ : ((P.gapSize : ℕ) : ℝ) * (P.blockCount : ℝ) * scaleSpacing P.L P.baseMesh n =
            ((P.L ^ P.gapExponent : ℕ) : ℝ) * (P.L : ℝ) ^ P.blockExponent *
              P.scaleData.levelMesh P.L n := by
          rw [scaleSpacing_baseMesh]
          simp [blockCount, gapSize, SeparatedSequences.ScaleData.levelMesh, scaleData]
        rw [e₃]
        exact hsep
    · have h0 : P.regionInUnits (n + 1) = ∅ :=
        P.regionInUnits_eq_empty (not_nonempty_iff_eq_empty.mp hne)
      rw [h0]
      have : supSetDist (cubeComplement ((P.blockCount : ℝ) * scaleSpacing P.L P.baseMesh n)
          (P.regionInUnits n)) (∅ : Set (PeriodicTorus 4 P.sideInUnits)) = ⊤ := by
        simp [supSetDist]
      rw [this]
      exact ENNReal.ofReal_lt_top
section Distance
variable {P} (hcells : CellStructure.CellStructureClaim) (h : P.IsRegionChain)
  (𝔟 : Set (LatticeBond 4 P.sideInUnits P.baseMesh))
  (inner_subset : ∀ b : LatticeBond 4 P.sideInUnits P.baseMesh,
      (b.source : PeriodicTorus 4 P.sideInUnits) ∈ P.regionInUnits 0 →
      (b.target : PeriodicTorus 4 P.sideInUnits) ∈ P.regionInUnits 0 → b ∈ 𝔟)
  (subset_star : ∀ b ∈ 𝔟, (b.source : PeriodicTorus 4 P.sideInUnits) ∈ P.regionInUnits 0 ∨
      (b.target : PeriodicTorus 4 P.sideInUnits) ∈ P.regionInUnits 0)
end Distance
end YangMills.Construction.Propagator.SeparatedRegionChain
namespace YangMills.Construction.RegionSequence
end YangMills.Construction.RegionSequence
namespace YangMills.Construction.Propagator.SeparatedRegionChain
open YangMills.Construction.RegionSequence
variable {P : SeparatedRegionChain}
end YangMills.Construction.Propagator.SeparatedRegionChain
namespace YangMills.Construction.RegionSequence
end YangMills.Construction.RegionSequence
