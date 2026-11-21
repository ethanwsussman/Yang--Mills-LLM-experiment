import YangMills.Construction.SeparatedSequences.ClassWeightInASettingOfRegionsProof
import YangMills.Construction.RegionSequence.CellsAndAdjoints
import YangMills.Construction.RegionSequence.ShellDecomposition
import YangMills.Construction.SeparatedSequences.ClassExpansionsAndAveragesInASettingOfRegionsProof
import YangMills.Construction.SeparatedSequences.ClassGeometryInASettingOfRegions
import Mathlib
set_option autoImplicit false
open Set
open scoped Pointwise
noncomputable section
namespace YangMills.Construction.SeparatedClasses.NestedGeometryOfClass
open SingleSequence SingleSequence.SequenceData
open RegionSequence.CellStructure
variable (s : SequenceData) (𝒮 : RegionSequence.NestedRegions)
def rescaleHomeomorph : s.data.Point ≃ₜ 𝒮.Point :=
  Homeomorph.piCongrRight fun _ =>
    AddCircle.homeomorphAddCircle _ _ s.torusSide_ne_zero 𝒮.side_pos.ne'
theorem toTorus_apply_eq (x : s.data.Point) : s.toTorus 𝒮.side x = rescaleHomeomorph s 𝒮 x := by
  unfold SequenceData.toTorus
  rw [dif_pos 𝒮.side_pos.ne']
  rfl
theorem toTorus_eq : s.toTorus 𝒮.side = rescaleHomeomorph s 𝒮 := funext (toTorus_apply_eq s 𝒮)
theorem rescale_sub (x y : s.data.Point) :
    rescaleHomeomorph s 𝒮 (x - y) = rescaleHomeomorph s 𝒮 x - rescaleHomeomorph s 𝒮 y :=
  funext fun μ =>
    map_sub (AddCircle.equivAddCircle _ _ s.torusSide_ne_zero 𝒮.side_pos.ne') (x μ) (y μ)
def rescaleFactor : ℝ := (PeriodicLattice.torusSide s.data.L s.data.m)⁻¹ * 𝒮.side
theorem blockFactor_pos : 0 < (s.data.L : ℝ) := by apply _root_.YangMills.Construction.SeparatedClasses.SingleSequence.NestedRescale.blockFactor_pos <;> assumption
theorem rescaleFactor_pos : 0 < rescaleFactor s 𝒮 := by
  have hL := blockFactor_pos s
  have h : 0 < PeriodicLattice.torusSide s.data.L s.data.m := by
    unfold PeriodicLattice.torusSide
    positivity
  exact mul_pos (inv_pos.2 h) 𝒮.side_pos
theorem rescale_torusProj (v : Fin 4 → ℝ) :
    rescaleHomeomorph s 𝒮 (TorusMetric.torusProj (PeriodicLattice.torusSide s.data.L s.data.m) v) =
      Torus.torusProj 4 𝒮.side (rescaleFactor s 𝒮 • v) := by
  funext μ
  show AddCircle.equivAddCircle _ _ s.torusSide_ne_zero 𝒮.side_pos.ne'
    ((v μ : ℝ) : AddCircle (PeriodicLattice.torusSide s.data.L s.data.m)) = _
  rw [AddCircle.equivAddCircle_apply_mk]
  show _ = ((rescaleFactor s 𝒮 * v μ : ℝ) : AddCircle 𝒮.side)
  rw [mul_comm]
  rfl
theorem supNormVec_eq_norm (v : Fin 4 → ℝ) : TorusMetric.supNormVec v = ‖v‖ := by apply _root_.YangMills.Construction.LevelUnitFacts.supNormVec_eq_norm <;> assumption
theorem supNorm_rescale (x : s.data.Point) :
    Torus.supNorm (rescaleHomeomorph s 𝒮 x) = rescaleFactor s 𝒮 * TorusMetric.torusSupNorm x := by
  have hc := rescaleFactor_pos s 𝒮
  have hset : {r | ∃ v : Fin 4 → ℝ, Torus.torusProj 4 𝒮.side v = rescaleHomeomorph s 𝒮 x ∧ r = ‖v‖} =
      rescaleFactor s 𝒮 • (TorusMetric.supNormVec ''
        (TorusMetric.torusProj (PeriodicLattice.torusSide s.data.L s.data.m) ⁻¹' {x})) := by
    ext r
    rw [Set.mem_smul_set]
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨TorusMetric.supNormVec ((rescaleFactor s 𝒮)⁻¹ • v), ⟨_, ?_, rfl⟩, ?_⟩
      · show TorusMetric.torusProj _ _ = x
        apply (rescaleHomeomorph s 𝒮).injective
        rw [rescale_torusProj, smul_smul, mul_inv_cancel₀ hc.ne', one_smul, hv]
      · rw [supNormVec_eq_norm, norm_smul, smul_eq_mul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.2 hc), mul_inv_cancel_left₀ hc.ne']
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      have hw' : TorusMetric.torusProj (PeriodicLattice.torusSide s.data.L s.data.m) w = x := hw
      refine ⟨rescaleFactor s 𝒮 • w, ?_, ?_⟩
      · rw [← rescale_torusProj, hw']
      · rw [supNormVec_eq_norm, norm_smul, smul_eq_mul, Real.norm_eq_abs, abs_of_pos hc]
  unfold Torus.supNorm TorusMetric.torusSupNorm
  rw [hset, Real.sInf_smul_of_nonneg hc.le, smul_eq_mul]
theorem mem_sublattice_iff_rescale {i : ℤ} {σ : ℝ}
    (hσ : σ = rescaleFactor s 𝒮 * PeriodicLattice.meshSize s.data.L i) (x : s.data.Point) :
    x ∈ PeriodicLattice.sublattice s.data.L s.data.m i ↔
      rescaleHomeomorph s 𝒮 x ∈ Torus.spacingLattice 4 𝒮.side σ := by
  have key : ∀ k : Fin 4 → ℤ, rescaleHomeomorph s 𝒮
      (TorusMetric.torusProj (PeriodicLattice.torusSide s.data.L s.data.m)
        fun μ => (k μ : ℝ) * PeriodicLattice.meshSize s.data.L i) =
      Torus.torusProj 4 𝒮.side fun μ => (k μ : ℝ) * σ := by
    intro k
    rw [rescale_torusProj]
    congr 1
    funext μ
    simp only [Pi.smul_apply, smul_eq_mul, hσ]
    ring
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [← key]
    exact congrArg _ (funext hk)
  · rintro ⟨k, hk⟩
    refine ⟨k, fun μ => ?_⟩
    exact congrFun ((rescaleHomeomorph s 𝒮).injective (hk.trans (key k).symm)) μ
theorem rescale_image_cubeAround {i : ℤ} {σ : ℝ}
    (hσ : σ = rescaleFactor s 𝒮 * PeriodicLattice.meshSize s.data.L i)
    (y : PeriodicLattice.Site s.data.L s.data.m i) :
    rescaleHomeomorph s 𝒮 '' PeriodicLattice.cubeAround y =
      Torus.cubeAt (rescaleHomeomorph s 𝒮 (y : s.data.Point)) σ := by
  have hc := rescaleFactor_pos s 𝒮
  have key : ∀ x : s.data.Point, rescaleHomeomorph s 𝒮 x ∈
      Torus.cubeAt (rescaleHomeomorph s 𝒮 (y : s.data.Point)) σ ↔
      x ∈ PeriodicLattice.cubeAround y := by
    intro x
    show Torus.supNorm (rescaleHomeomorph s 𝒮 x - rescaleHomeomorph s 𝒮 (y : s.data.Point)) ≤ σ / 2 ↔
      TorusMetric.torusSupNorm (x - (y : s.data.Point)) ≤ PeriodicLattice.meshSize s.data.L i / 2
    rw [← rescale_sub, supNorm_rescale, hσ, mul_div_assoc]
    exact mul_le_mul_iff_right₀ hc
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (key x).2 hx
  · intro hp
    obtain ⟨x, rfl⟩ := (rescaleHomeomorph s 𝒮).surjective p
    exact ⟨x, (key x).1 hp, rfl⟩
variable {s 𝒮}
theorem scale_eq_coarseMesh (hs : s.IsNestedRegions 𝒮) (n : ℕ) :
    𝒮.scale n = s.data.coarseMesh n := by apply _root_.YangMills.Construction.SeparatedClasses.MassForm.scale_eq_levelMeshRatio <;> assumption
theorem scale_eq_factor_mul_meshSize (hs : s.IsNestedRegions 𝒮) (n : ℕ) :
    𝒮.scale n = rescaleFactor s 𝒮 *
      PeriodicLattice.meshSize s.data.L (PeriodicLattice.levelDepth s.data.cutoff n) := by
  have hL := (blockFactor_pos s).ne'
  rw [scale_eq_coarseMesh hs]
  unfold rescaleFactor PeriodicLattice.meshSize PeriodicLattice.torusSide
    Conventions.LeveledParameters.coarseMesh
  rw [hs.side_eq]
  unfold SequenceData.unitTorusSide Torus.unitSide
  have e : (2 * (s.data.L : ℝ) ^ (s.data.m : ℕ))⁻¹ *
      (2 * (s.data.L : ℝ) ^ (((s.data.m : ℕ) : ℤ) + ((s.data.cutoff : ℕ) : ℤ) - (s.data.t : ℤ))) =
      (s.data.L : ℝ) ^ (((s.data.cutoff : ℕ) : ℤ) - (s.data.t : ℤ)) := by
    rw [show ((s.data.m : ℕ) : ℤ) + ((s.data.cutoff : ℕ) : ℤ) - (s.data.t : ℤ) =
      ((s.data.m : ℕ) : ℤ) + (((s.data.cutoff : ℕ) : ℤ) - (s.data.t : ℤ)) by ring,
      zpow_add₀ hL, zpow_natCast]
    field_simp
  rw [e, ← zpow_add₀ hL]
  congr 1
  simp only [PeriodicLattice.levelDepth]
  ring
theorem isPartitionLevel (hs : s.IsNestedRegions 𝒮) {i : ℕ} (hi : i ≤ s.data.t) :
    𝒮.IsPartitionLevel i := by
  have hL := (blockFactor_pos s).ne'
  have hK := s.data.t_le_cutoff
  have h1 : (1 : ℤ) ≤ (s.data.L : ℤ) := by
    have := s.data.isAdmissible.2
    exact_mod_cast (by omega : 1 ≤ s.data.L)
  refine ⟨2 * (s.data.L : ℤ) ^ ((s.data.m : ℕ) + (s.data.cutoff : ℕ) - i), ?_, ?_⟩
  · have := one_le_pow₀ h1 (n := (s.data.m : ℕ) + (s.data.cutoff : ℕ) - i)
    linarith
  · rw [scale_eq_coarseMesh hs, hs.side_eq]
    unfold SequenceData.unitTorusSide Torus.unitSide Conventions.LeveledParameters.coarseMesh
    rw [div_eq_iff (zpow_ne_zero _ hL)]
    push_cast
    rw [← zpow_natCast, mul_assoc, ← zpow_add₀ hL]
    congr 2
    have : ((((s.data.m : ℕ) + (s.data.cutoff : ℕ) - i : ℕ)) : ℤ) =
        ((s.data.m : ℕ) : ℤ) + ((s.data.cutoff : ℕ) : ℤ) - (i : ℤ) := by
      have : i ≤ (s.data.cutoff : ℕ) := hi.trans hK
      omega
    rw [this]
    ring
theorem Ω_eq_image (hs : s.IsNestedRegions 𝒮) (n : ℕ) :
    𝒮.Ω n = rescaleHomeomorph s 𝒮 '' s.Ω n := by
  rw [hs.Ω_eq n, SequenceData.regionOn, toTorus_eq]
theorem mem_levelSublattice_iff (hs : s.IsNestedRegions 𝒮) (n : ℕ) (x : s.data.Point) :
    x ∈ PeriodicLattice.sublattice s.data.L s.data.m (PeriodicLattice.levelDepth s.data.cutoff n) ↔
      rescaleHomeomorph s 𝒮 x ∈ Torus.spacingLattice 4 𝒮.side (𝒮.scale n) :=
  mem_sublattice_iff_rescale s 𝒮 (scale_eq_factor_mul_meshSize hs n) x
theorem shellOf_last (hc : CellFacts 𝒮) (hs : s.IsNestedRegions 𝒮) :
    𝒮.shellOf s.data.t = 𝒮.Ω s.data.t := by
  have ht : s.data.t ≤ 𝒮.s := hs.s_eq.ge
  have hempty : 𝒮.Ω (s.data.t + 1) = ∅ := 𝒮.Ω_eq_empty _ (by rw [hs.s_eq]; omega)
  rw [hc.shell_eq _ ht]
  obtain ⟨C, hC, hU⟩ := (hc.regions _ ht).1
  apply Subset.antisymm
  · rintro x ⟨Q, hQ, hx⟩
    exact hQ.2.1 hx
  · intro x hx
    have hx' := hx
    rw [hU] at hx'
    obtain ⟨Q, hQ, hxQ⟩ := hx'
    refine ⟨Q, ⟨hC hQ, ?_, ?_⟩, hxQ⟩
    · rw [hU]
      exact subset_sUnion_of_mem hQ
    · rw [hempty]
      exact fun h => h hxQ
theorem image_layerAt (hc : CellFacts 𝒮) (hs : s.IsNestedRegions 𝒮) (n : ℕ) :
    rescaleHomeomorph s 𝒮 '' s.data.layerAt s.Ω n = 𝒮.shellOf n := by
  rcases lt_trichotomy n s.data.t with h | h | h
  · have e : s.data.layerAt s.Ω n = closure (s.Ω n \ s.Ω (n + 1)) := if_pos h
    rw [e, (rescaleHomeomorph s 𝒮).image_closure, image_sdiff (rescaleHomeomorph s 𝒮).injective,
      ← Ω_eq_image hs, ← Ω_eq_image hs]
    rfl
  · have e : s.data.layerAt s.Ω n = s.Ω s.data.t :=
      (if_neg (by show ¬ n < s.data.t; omega)).trans (if_pos h)
    rw [e, h, shellOf_last hc hs, Ω_eq_image hs]
  · have e : s.data.layerAt s.Ω n = ∅ :=
      (if_neg (by show ¬ n < s.data.t; omega)).trans (if_neg (by show ¬ n = s.data.t; omega))
    rw [e, image_empty, 𝒮.shellOf_eq_empty_of_lt (by rw [hs.s_eq]; exact h)]
theorem mem_layerAt_iff (hc : CellFacts 𝒮) (hs : s.IsNestedRegions 𝒮) (n : ℕ)
    (x : s.data.Point) :
    x ∈ s.data.layerAt s.Ω n ↔ rescaleHomeomorph s 𝒮 x ∈ 𝒮.shellOf n := by
  rw [← image_layerAt hc hs n]
  exact (rescaleHomeomorph s 𝒮).injective.mem_set_image.symm
theorem le_lastNonemptyIndex {n : ℕ} (h : (𝒮.shellOf n).Nonempty) :
    n ≤ Torus.lastNonemptyIndex 𝒮.Ω := by
  have h1 : (𝒮.Ω n \ 𝒮.Ω (n + 1)).Nonempty := closure_nonempty_iff.1 h
  refine le_csSup ⟨𝒮.s, ?_⟩ (h1.mono sdiff_subset)
  intro k hk
  by_contra hlt
  have e := 𝒮.Ω_eq_empty k (by omega)
  have hk' : (𝒮.Ω k).Nonempty := hk
  rw [e] at hk'
  exact not_nonempty_empty hk'
theorem mem_centresAt_iff {n : ℕ} {p : 𝒮.Point} :
    p ∈ 𝒮.centresAt n ↔
      p ∈ Torus.spacingLattice 4 𝒮.side (𝒮.scale n) ∧ p ∈ 𝒮.shellOf n :=
  ⟨fun h => h.2, fun h => ⟨le_lastNonemptyIndex ⟨p, h.2⟩, h.1, h.2⟩⟩
theorem rescale_mem_centresAt (hc : CellFacts 𝒮) (hs : s.IsNestedRegions 𝒮) {n : ℕ}
    (y : s.data.LatticeSite n) (hy : y ∈ s.data.layerSitesAt s.Ω n) :
    rescaleHomeomorph s 𝒮 (y : s.data.Point) ∈ 𝒮.centresAt n :=
  mem_centresAt_iff.2 ⟨(mem_levelSublattice_iff hs n _).1 y.2, (mem_layerAt_iff hc hs n _).1 hy⟩
theorem exists_layerSite_of_mem_centresAt (hc : CellFacts 𝒮) (hs : s.IsNestedRegions 𝒮)
    {n : ℕ} {p : 𝒮.Point} (hp : p ∈ 𝒮.centresAt n) :
    ∃ y : s.data.LatticeSite n, y ∈ s.data.layerSitesAt s.Ω n ∧
      rescaleHomeomorph s 𝒮 (y : s.data.Point) = p := by
  obtain ⟨hl, hly⟩ := mem_centresAt_iff.1 hp
  obtain ⟨x, rfl⟩ := (rescaleHomeomorph s 𝒮).surjective p
  exact ⟨⟨x, (mem_levelSublattice_iff hs n x).2 hl⟩, (mem_layerAt_iff hc hs n x).2 hly, rfl⟩
theorem Ω_antitone {a b : ℕ} (hab : a ≤ b) (hb : b ≤ 𝒮.s) : 𝒮.Ω b ⊆ 𝒮.Ω a := by apply _root_.YangMills.Construction.RegionSequence.ShellDecomposition.Ω_antitone <;> assumption
theorem not_mem_centresAt_of_lt (hp : PartitionFacts 𝒮) (hc : CellFacts 𝒮)
    (hs : s.IsNestedRegions 𝒮) {n' n : ℕ} (h : n' < n) (hn : n ≤ 𝒮.s) {p : 𝒮.Point}
    (hpn : p ∈ 𝒮.centresAt n) (hpn' : p ∈ 𝒮.centresAt n') : False := by
  have hnt : n ≤ s.data.t := hs.s_eq ▸ hn
  have hin : p ∈ 𝒮.Ω n := ((hc.cell_subset n hn p hpn).2 hpn.2.2).1
  have hmem : p ∈ 𝒮.Ω (n' + 1) := Ω_antitone h hn hin
  obtain ⟨Q, -, hint, huniq⟩ := hp.site_interior n' (n' + 1) (Nat.le_succ _)
    (isPartitionLevel hs (by omega)) p hpn'.2.1
  obtain ⟨C, hC, hU⟩ := (hc.regions (n' + 1) (by omega)).1
  have hp' := hmem
  rw [hU] at hp'
  obtain ⟨Q', hQ', hpQ'⟩ := hp'
  have hQQ : Q' = Q := huniq Q' (hC hQ') hpQ'
  have hsub : Q ⊆ 𝒮.Ω (n' + 1) := by
    rw [hU]
    exact hQQ ▸ subset_sUnion_of_mem hQ'
  have hcl : p ∈ closure (𝒮.Ω n' \ 𝒮.Ω (n' + 1)) := hpn'.2.2
  obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.1 hcl _ isOpen_interior (interior_mono hsub hint)
  exact hz2.2 (interior_subset hz1)
theorem level_eq_of_mem_centresAt (hp : PartitionFacts 𝒮) (hc : CellFacts 𝒮)
    (hs : s.IsNestedRegions 𝒮) {n : ℕ} (hn : n ≤ 𝒮.s) {p : 𝒮.Point}
    (hpn : p ∈ 𝒮.centresAt n) : 𝒮.level p = n := by
  show sInf {k | p ∈ Torus.shellSites 𝒮.L 𝒮.ξ 𝒮.Ω k} = n
  apply le_antisymm (Nat.sInf_le hpn)
  by_contra hlt
  have hmem : sInf {k | p ∈ Torus.shellSites 𝒮.L 𝒮.ξ 𝒮.Ω k} ∈
      {k | p ∈ Torus.shellSites 𝒮.L 𝒮.ξ 𝒮.Ω k} := Nat.sInf_mem ⟨n, hpn⟩
  exact not_mem_centresAt_of_lt hp hc hs (not_le.1 hlt) hn hpn hmem
theorem levelScale_eq (hp : PartitionFacts 𝒮) (hc : CellFacts 𝒮) (hs : s.IsNestedRegions 𝒮)
    {n : ℕ} (hn : n ≤ 𝒮.s) {p : 𝒮.Point} (hpn : p ∈ 𝒮.centresAt n) :
    𝒮.levelScale p = 𝒮.scale n := by
  show Torus.scaleSpacing 𝒮.L 𝒮.ξ (𝒮.level p : ℤ) = _
  rw [level_eq_of_mem_centresAt hp hc hs hn hpn]
  rfl
theorem levelScale_apex (hp : PartitionFacts 𝒮) (hc : CellFacts 𝒮) (hs : s.IsNestedRegions 𝒮)
    (y : s.data.Apex s.Ω) :
    𝒮.levelScale (rescaleHomeomorph s 𝒮 y.point) = 𝒮.scale y.level :=
  levelScale_eq hp hc hs (hs.s_eq ▸ y.2.1) (rescale_mem_centresAt hc hs y.site y.2.2)
theorem statement_holds (h₁ : CellStructureClaim) : Statement := by
  intro s 𝒮 hs
  obtain ⟨hp, hc, -⟩ := h₁ 𝒮
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n _
    rw [toTorus_eq]
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (mem_levelSublattice_iff hs n x).1 hx
    · intro h
      obtain ⟨x, rfl⟩ := (rescaleHomeomorph s 𝒮).surjective p
      exact ⟨x, (mem_levelSublattice_iff hs n x).2 h, rfl⟩
  · intro n _
    rw [toTorus_eq]
    ext Q
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨rescaleHomeomorph s 𝒮 y, (mem_levelSublattice_iff hs n _).1 y.2,
        rescale_image_cubeAround s 𝒮 (scale_eq_factor_mul_meshSize hs n) y⟩
    · rintro ⟨c, hcm, rfl⟩
      obtain ⟨x, rfl⟩ := (rescaleHomeomorph s 𝒮).surjective c
      exact ⟨PeriodicLattice.cubeAround ⟨x, (mem_levelSublattice_iff hs n x).2 hcm⟩, ⟨_, rfl⟩,
        rescale_image_cubeAround s 𝒮 (scale_eq_factor_mul_meshSize hs n) _⟩
  · intro n
    rw [toTorus_eq]
    exact image_layerAt hc hs n
  · intro n _
    ext p
    simp only [toTorus_apply_eq]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact rescale_mem_centresAt hc hs y hy
    · intro h
      obtain ⟨y, hy, rfl⟩ := exists_layerSite_of_mem_centresAt hc hs h
      exact ⟨y, hy, rfl⟩
  · show s.toTorus 𝒮.side '' s.data.layerPts s.Ω = 𝒮.allCentres
    rw [toTorus_eq]
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨n, hn, y, hy, rfl⟩ : ∃ n ≤ s.data.t, ∃ y ∈ s.data.layerSitesAt s.Ω n,
          (y : s.data.Point) = x := by
        simpa [SeparatedSequences.layerPoints, mem_iUnion] using hx
      exact ⟨n, hs.s_eq ▸ hn, rescale_mem_centresAt hc hs y hy⟩
    · rintro ⟨n, hn, h⟩
      obtain ⟨y, hy, rfl⟩ := exists_layerSite_of_mem_centresAt hc hs h
      refine ⟨(y : s.data.Point), ?_, rfl⟩
      have hn' : n ≤ s.data.t := hs.s_eq ▸ hn
      show _ ∈ SeparatedSequences.layerPoints s.data.scales s.Ω
      unfold SeparatedSequences.layerPoints
      exact mem_iUnion₂.2 ⟨n, hn', y, hy, rfl⟩
  · intro y
    rw [toTorus_apply_eq, levelScale_apex hp hc hs y]
    exact scale_eq_coarseMesh hs y.level
  · intro y
    rw [toTorus_eq]
    show Torus.cubeAt _ (𝒮.levelScale _) = _
    rw [levelScale_apex hp hc hs y]
    exact (rescale_image_cubeAround s 𝒮 (scale_eq_factor_mul_meshSize hs y.level) y.site).symm
end YangMills.Construction.SeparatedClasses.NestedGeometryOfClass
