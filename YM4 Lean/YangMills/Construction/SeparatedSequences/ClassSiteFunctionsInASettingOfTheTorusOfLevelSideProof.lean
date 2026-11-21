import YangMills.Construction.SeparatedSequences.ClassExpansionsAndAveragesInASettingOfRegionsProof
import YangMills.Construction.SeparatedSequences.ClassExpansionsOnAGeneralTorusProof
import YangMills.Construction.DirichletOperator.FactsOfTheSettingInLevelUnits
import YangMills.Construction.Lattice.DifferenceOperatorsOfTheBareLattice
import YangMills.Construction.Lattice.ExistenceOfTheOperatorsOfASeparatedSequence
import YangMills.Construction.SeparatedSequences.ClassGeometryInASettingOfTheTorusOfLevelSide
import YangMills.Construction.SeparatedSequences.ClassSiteFunctionsInASettingOfTheTorusOfLevelSide
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric PeriodicLattice PeriodicLattice.DirichletOperators
namespace SeparatedClasses.BlockSettingScalarData
open SingleSequence SingleSequence.SequenceData
section EvaluationMaps
variable (s : SequenceData)
theorem Lreal_pos : (0 : ℝ) < s.Lreal := by apply _root_.YangMills.Construction.SeparatedClasses.SingleSequence.NestedRescale.blockFactor_pos <;> assumption
theorem one_lt_Lreal : (1 : ℝ) < s.Lreal := by apply _root_.YangMills.Construction.SeparatedClasses.GaugeOneFormsProof.TorusComponents.one_lt_blockFactor <;> assumption
theorem unitTorusSide_ne_zero : s.unitTorusSide ≠ 0 := by
  have hL := (Lreal_pos s).ne'
  simp only [SequenceData.unitTorusSide, YangMills.Construction.Torus.unitSide]
  exact mul_ne_zero two_ne_zero (zpow_ne_zero _ hL)
theorem toTorus_apply (x : s.data.Point) (μ : Fin 4) :
    s.toTorus s.unitTorusSide x μ =
      AddCircle.equivAddCircle _ s.unitTorusSide s.torusSide_ne_zero (unitTorusSide_ne_zero s)
        (x μ) := by
  simp only [SequenceData.toTorus, dif_pos (unitTorusSide_ne_zero s)]
theorem toTorus_injective : Function.Injective (s.toTorus s.unitTorusSide) := by
  intro x y hxy
  funext μ
  have h := congrFun hxy μ
  rw [toTorus_apply, toTorus_apply] at h
  exact (AddCircle.equivAddCircle _ s.unitTorusSide s.torusSide_ne_zero
    (unitTorusSide_ne_zero s)).injective h
theorem toTorus_add (x y : s.data.Point) :
    s.toTorus s.unitTorusSide (x + y) =
      s.toTorus s.unitTorusSide x + s.toTorus s.unitTorusSide y := by
  funext μ
  simp only [Pi.add_apply, toTorus_apply, map_add]
theorem toTorus_sub (x y : s.data.Point) :
    s.toTorus s.unitTorusSide (x - y) =
      s.toTorus s.unitTorusSide x - s.toTorus s.unitTorusSide y := by
  funext μ
  simp only [Pi.sub_apply, toTorus_apply, map_sub]
end EvaluationMaps
section Setting
variable {s : SequenceData} {𝒮 : s.BlockSettingType}
theorem meshSize_mul_scale :
    meshSize s.data.L (levelDepth s.data.cutoff 0) *
      ((PeriodicLattice.torusSide s.data.L s.data.m)⁻¹ * s.unitTorusSide) = s.mesh := by
  have hL := (Lreal_pos s).ne'
  simp only [SequenceData.unitTorusSide, SequenceData.mesh, YangMills.Construction.Torus.unitSide,
    YangMills.Construction.Torus.unitSpacing, PeriodicLattice.torusSide, PeriodicLattice.meshSize,
    levelDepth]
  have hL' : ((s.data.L : ℕ) : ℝ) ≠ 0 := hL
  rw [show ((s.data.m : ℕ) : ℤ) + ((s.data.cutoff : ℕ) : ℤ) - ((s.data.t : ℕ) : ℤ) =
    ((s.data.m : ℕ) : ℤ) + (((s.data.cutoff : ℕ) : ℤ) + (-((s.data.t : ℕ) : ℤ))) by ring,
    zpow_add₀ hL', zpow_add₀ hL', zpow_natCast,
    show -(((s.data.cutoff : ℕ) : ℤ) - ((0 : ℕ) : ℤ)) = -((s.data.cutoff : ℕ) : ℤ) by simp,
    zpow_neg]
  have h1 : ((s.data.L : ℝ) ^ ((s.data.cutoff : ℕ) : ℤ)) ≠ 0 := zpow_ne_zero _ hL'
  have h2 : ((s.data.L : ℝ) ^ (s.data.m : ℕ)) ≠ 0 := pow_ne_zero _ hL'
  field_simp
theorem toTorus_unitStep (h : s.IsBlockSetting 𝒮) (μ : Fin 4) :
    s.toTorus s.unitTorusSide ((unitStep s.data.L s.data.m (levelDepth s.data.cutoff 0) μ :
        PeriodicLattice.Site s.data.L s.data.m (levelDepth s.data.cutoff 0)) : s.data.Point) =
      ((Dirichlet.unitStep 4 s.unitTorusSide 𝒮.ξ μ :
          Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ) : Torus4 s.unitTorusSide) := by
  funext ν
  rw [toTorus_apply]
  by_cases hν : ν = μ
  · subst hν
    simp only [unitStep, pointOnAxis, Dirichlet.unitStep, YangMills.Construction.Torus.torusProj,
      Pi.single_eq_same]
    rw [AddCircle.equivAddCircle_apply_mk, meshSize_mul_scale, h.ξ_eq]
  · simp [unitStep, pointOnAxis, Dirichlet.unitStep, YangMills.Construction.Torus.torusProj,
      Pi.single_eq_of_ne hν]
theorem mem_zeroFormsOn_iff {Ω₀ : Set s.data.Point} {f : s.data.SiteFn} :
    f ∈ zeroFormsOn s.data.cutoff Ω₀ ↔ ∀ x : s.data.BareSite, (x : s.data.Point) ∉ Ω₀ → f x = 0 := by
  constructor
  · rintro ⟨g, rfl⟩ x hx
    exact Set.indicator_of_notMem (s := sitesOfRegion s.data.cutoff Ω₀) hx g
  · intro hf
    refine ⟨f, ?_⟩
    funext x
    by_cases hx : (x : s.data.Point) ∈ Ω₀
    · exact Set.indicator_of_mem (s := sitesOfRegion s.data.cutoff Ω₀) hx f
    · rw [hf x hx]
      exact Set.indicator_of_notMem (s := sitesOfRegion s.data.cutoff Ω₀) hx f
theorem image_sublattice (g : s.BlockSettingGeometry 𝒮) :
    s.toTorus s.unitTorusSide '' (sublattice s.data.L s.data.m (levelDepth s.data.cutoff 0) :
        Set s.data.Point) =
      (YangMills.Construction.Torus.spacingLattice 4 s.unitTorusSide 𝒮.ξ :
        Set (Torus4 s.unitTorusSide)) := by
  have h := g.sublattices 0 (Nat.zero_le _)
  simpa [Dirichlet.BlockSetting.scaleAt, YangMills.Construction.Torus.scaleSpacing] using h
def bareSiteEquiv (g : s.BlockSettingGeometry 𝒮) :
    s.data.BareSite ≃ Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ :=
  Equiv.ofBijective
    (fun x => ⟨s.toTorus s.unitTorusSide (x : s.data.Point), by
      have : s.toTorus s.unitTorusSide (x : s.data.Point) ∈
          (YangMills.Construction.Torus.spacingLattice 4 s.unitTorusSide 𝒮.ξ :
            Set (Torus4 s.unitTorusSide)) := by
        rw [← image_sublattice g]
        exact ⟨x, x.2, rfl⟩
      exact this⟩)
    ⟨fun x y hxy => Subtype.ext (toTorus_injective s (congrArg Subtype.val hxy)), fun x' => by
      have : (x' : Torus4 s.unitTorusSide) ∈
          s.toTorus s.unitTorusSide '' (sublattice s.data.L s.data.m (levelDepth s.data.cutoff 0) :
            Set s.data.Point) := by
        rw [image_sublattice g]
        exact x'.2
      obtain ⟨x, hx, hxx⟩ := this
      exact ⟨⟨x, hx⟩, Subtype.ext hxx⟩⟩
theorem coe_bareSiteEquiv (g : s.BlockSettingGeometry 𝒮) (x : s.data.BareSite) :
    ((bareSiteEquiv g x : Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ) : Torus4 s.unitTorusSide) =
      s.toTorus s.unitTorusSide (x : s.data.Point) := rfl
theorem bareSiteEquiv_mem_iff (h : s.IsBlockSetting 𝒮) (g : s.BlockSettingGeometry 𝒮)
    (x : s.data.BareSite) :
    ((bareSiteEquiv g x : Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ) : Torus4 s.unitTorusSide) ∈
        𝒮.Ω 0 ↔
      (x : s.data.Point) ∈ s.Ω 0 := by
  rw [coe_bareSiteEquiv, h.Ω_eq 0]
  exact (toTorus_injective s).mem_set_image
theorem bareSiteEquiv_add (h : s.IsBlockSetting 𝒮) (g : s.BlockSettingGeometry 𝒮)
    (x : s.data.BareSite) (μ : Fin 4) :
    bareSiteEquiv g (x + unitStep s.data.L s.data.m (levelDepth s.data.cutoff 0) μ) =
      bareSiteEquiv g x + Dirichlet.unitStep 4 s.unitTorusSide 𝒮.ξ μ := by
  apply Subtype.ext
  change s.toTorus s.unitTorusSide ((x : s.data.Point) + _) =
    s.toTorus s.unitTorusSide (x : s.data.Point) + _
  rw [toTorus_add, toTorus_unitStep h]
theorem bareSiteEquiv_sub (h : s.IsBlockSetting 𝒮) (g : s.BlockSettingGeometry 𝒮)
    (x : s.data.BareSite) (μ : Fin 4) :
    bareSiteEquiv g (x - unitStep s.data.L s.data.m (levelDepth s.data.cutoff 0) μ) =
      bareSiteEquiv g x - Dirichlet.unitStep 4 s.unitTorusSide 𝒮.ξ μ := by
  apply Subtype.ext
  change s.toTorus s.unitTorusSide ((x : s.data.Point) - _) =
    s.toTorus s.unitTorusSide (x : s.data.Point) - _
  rw [toTorus_sub, toTorus_unitStep h]
theorem siteRel_iff (g : s.BlockSettingGeometry 𝒮) (x : s.data.BareSite)
    (x' : Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ) :
    s.scalarData.SiteRel (scalarDataOfBlockSetting 𝒮) (s.toTorus s.unitTorusSide) x x' ↔
      x' = bareSiteEquiv g x := by
  constructor
  · intro hx
    exact Subtype.ext hx.symm
  · rintro rfl
    rfl
theorem vanishesOff_iff (h : s.IsBlockSetting 𝒮) (g : s.BlockSettingGeometry 𝒮)
    (f' : Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ → ℝ) :
    Dirichlet.VanishesOff (𝒮.Ω 0) f' ↔
      (f' ∘ bareSiteEquiv g) ∈ zeroFormsOn s.data.cutoff (s.Ω 0) := by
  rw [mem_zeroFormsOn_iff]
  constructor
  · intro hf x hx
    exact hf _ (fun hm => hx ((bareSiteEquiv_mem_iff h g x).1 hm))
  · intro hf x' hx'
    obtain ⟨x, rfl⟩ := (bareSiteEquiv g).surjective x'
    exact hf x (fun hm => hx' ((bareSiteEquiv_mem_iff h g x).2 hm))
def pushField (g : s.BlockSettingGeometry 𝒮) (f : s.data.SiteFn) :
    Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ → ℝ := f ∘ (bareSiteEquiv g).symm
theorem pushField_comp (g : s.BlockSettingGeometry 𝒮) (f : s.data.SiteFn) :
    pushField g f ∘ bareSiteEquiv g = f := by
  funext x
  simp [pushField]
theorem latticeInner_eq (h : s.IsBlockSetting 𝒮) (g : s.BlockSettingGeometry 𝒮)
    {f₁ f₂ : s.data.SiteFn} {f₁' f₂' : Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ → ℝ}
    (h₁ : ∀ x, f₁ x = f₁' (bareSiteEquiv g x)) (h₂ : ∀ x, f₂ x = f₂' (bareSiteEquiv g x)) :
    latticeInner s.data.L s.data.t f₁ f₂ = Dirichlet.innerSum f₁' f₂' := by
  have e₁ : 𝒮.ξ ^ 4 = finestMeshInLevelUnits s.data.L s.data.t ^ 4 := by
    rw [h.ξ_eq]
    rfl
  simp only [latticeInner, Dirichlet.innerSum]
  rw [e₁, ← finsum_comp_equiv (bareSiteEquiv g)]
  simp only [h₁, h₂]
def coarseEquiv (g : s.BlockSettingGeometry 𝒮) :
    ↥(s.params.allLayerPoints s.Ω) ≃ ↥𝒮.centres :=
  Equiv.ofBijective
    (fun y => ⟨s.toTorus s.unitTorusSide y.1, by
      have hall := g.allLayerSites
      have : s.toTorus s.unitTorusSide y.1 ∈ s.toTorus s.unitTorusSide '' s.data.layerPts s.Ω :=
        ⟨y.1, y.2, rfl⟩
      rw [hall] at this
      exact this⟩)
    ⟨fun x y hxy => Subtype.ext (toTorus_injective s (congrArg Subtype.val hxy)), fun y' => by
      have hall := g.allLayerSites
      have : y'.1 ∈ s.toTorus s.unitTorusSide '' s.data.layerPts s.Ω := by
        rw [hall]
        exact y'.2
      obtain ⟨y, hy, hyy⟩ := this
      exact ⟨⟨y, hy⟩, Subtype.ext hyy⟩⟩
theorem coe_coarseEquiv (g : s.BlockSettingGeometry 𝒮)
    (y : ↥(s.params.allLayerPoints s.Ω)) :
    (coarseEquiv g y).1 = s.toTorus s.unitTorusSide y.1 := rfl
theorem centreIndex_apex (h : s.IsBlockSetting 𝒮) (g : s.BlockSettingGeometry 𝒮)
    (z : s.data.Apex s.Ω) : 𝒮.centreIndex (s.toTorus s.unitTorusSide z.point) = z.level := by
  have e : s.Lreal ^ ((𝒮.centreIndex (s.toTorus s.unitTorusSide z.point) : ℕ) : ℤ) * 𝒮.ξ =
      s.Lreal ^ ((z.level : ℤ) - (s.data.t : ℤ)) := g.meshes z
  rw [h.ξ_eq] at e
  have e' : s.Lreal ^ (((𝒮.centreIndex (s.toTorus s.unitTorusSide z.point) : ℕ) : ℤ) +
      (-(s.data.t : ℤ))) = s.Lreal ^ ((z.level : ℤ) - (s.data.t : ℤ)) := by
    rw [zpow_add₀ (Lreal_pos s).ne']
    exact e
  have hinj := zpow_right_injective₀ (Lreal_pos s) (one_lt_Lreal s).ne'
  have := hinj e'
  omega
theorem exists_apex (y : ↥(s.params.allLayerPoints s.Ω)) :
    ∃ z : s.data.Apex s.Ω, z.point = y.1 := by
  obtain ⟨p, hn, hz, hy⟩ := s.params.exists_levelSite s.Ω y
  exact ⟨⟨p, hn, hz⟩, hy⟩
theorem centreSpacing_apex (g : s.BlockSettingGeometry 𝒮) (z : s.data.Apex s.Ω) :
    𝒮.centreSpacing (s.toTorus s.unitTorusSide z.point) = s.params.levelMeshRatio z.level :=
  g.meshes z
theorem coarseZeroInner_eq (h : s.IsBlockSetting 𝒮) (g : s.BlockSettingGeometry 𝒮)
    (ω₁ ω₂ : ↥(s.params.allLayerPoints s.Ω) → ℝ) (ω₁' ω₂' : ↥𝒮.centres → ℝ)
    (h₁ : ∀ y, ω₁ y = ω₁' (coarseEquiv g y)) (h₂ : ∀ y, ω₂ y = ω₂' (coarseEquiv g y)) :
    s.params.coarseZeroInner s.Ω ω₁ ω₂ =
      ∑ᶠ y : ↥𝒮.centres, 𝒮.centreSpacing y.1 ^ 4 * ω₁' y * ω₂' y := by
  classical
  have hR : (∑ᶠ y : ↥𝒮.centres, 𝒮.centreSpacing y.1 ^ 4 * ω₁' y * ω₂' y) =
      ∑ᶠ y : ↥(s.params.allLayerPoints s.Ω),
        𝒮.centreSpacing (s.toTorus s.unitTorusSide y.1) ^ 4 * ω₁ y * ω₂ y := by
    rw [← finsum_comp_equiv (coarseEquiv g)]
    simp only [h₁, h₂, coe_coarseEquiv]
  rw [hR]
  let _ : Fintype ↥(s.params.allLayerPoints s.Ω) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  set lev : ↥(s.params.allLayerPoints s.Ω) → ℕ :=
    fun y => 𝒮.centreIndex (s.toTorus s.unitTorusSide y.1) with hlev
  have hmaps : ∀ y ∈ (Finset.univ : Finset ↥(s.params.allLayerPoints s.Ω)),
      lev y ∈ Finset.range (s.params.t + 1) := by
    intro y _
    obtain ⟨z, hz⟩ := exists_apex y
    have : lev y = z.level := by
      simp only [hlev]
      rw [← hz]
      exact centreIndex_apex h g z
    rw [this, Finset.mem_range]
    exact Nat.lt_succ_of_le z.2.1
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  simp only [SeparatedSequences.BaseParameters.coarseZeroInner]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hnt : n ≤ s.data.t := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  have hmem : ∀ z : ↥(s.params.layerSites s.Ω n),
      ((z.1 : s.data.Point)) ∈ s.params.allLayerPoints s.Ω :=
    fun z => mem_iUnion₂.mpr ⟨n, hnt, z.1, z.2, rfl⟩
  have hlevz : ∀ z : ↥(s.params.layerSites s.Ω n), lev ⟨z.1, hmem z⟩ = n := fun z =>
    centreIndex_apex h g (⟨⟨n, z.1⟩, hnt, z.2⟩ : s.data.Apex s.Ω)
  let E : ↥(s.params.layerSites s.Ω n) ≃
      {y : ↥(s.params.allLayerPoints s.Ω) // lev y = n} :=
    Equiv.ofBijective (fun z => ⟨⟨z.1, hmem z⟩, hlevz z⟩)
      ⟨fun z z' hzz => Subtype.ext (Subtype.ext (congrArg (fun w => w.1.1) hzz)), fun y => by
        obtain ⟨⟨⟨k, w⟩, hk, hw⟩, hz⟩ := exists_apex y.1
        have hkn : k = n := by
          have h1 := centreIndex_apex h g (⟨⟨k, w⟩, hk, hw⟩ : s.data.Apex s.Ω)
          rw [hz] at h1
          exact h1.symm.trans y.2
        subst hkn
        exact ⟨⟨w, hw⟩, Subtype.ext (Subtype.ext hz)⟩⟩
  have : Finite (s.params.LatticeSite n) := s.params.instFiniteLatticeSite n
  have : Finite ↥(s.params.layerSites s.Ω n) := Subtype.finite
  have hterm : ∀ z : ↥(s.params.layerSites s.Ω n),
      𝒮.centreSpacing (s.toTorus s.unitTorusSide (z.1 : s.data.Point)) ^ 4 *
          ω₁ ⟨z.1, hmem z⟩ * ω₂ ⟨z.1, hmem z⟩ =
        s.params.levelMeshRatio n ^ 4 *
          (SeparatedSequences.BaseParameters.pointValue ω₁ (z.1 : s.params.Torus) *
            SeparatedSequences.BaseParameters.pointValue ω₂ (z.1 : s.params.Torus)) := by
    intro z
    have hs := centreSpacing_apex g (⟨⟨n, z.1⟩, hnt, z.2⟩ : s.data.Apex s.Ω)
    have hs' : 𝒮.centreSpacing (s.toTorus s.unitTorusSide (z.1 : s.data.Point)) =
        s.params.levelMeshRatio n := hs
    rw [hs']
    simp only [SeparatedSequences.BaseParameters.pointValue, dif_pos (hmem z)]
    ring
  calc s.params.levelMeshRatio n ^ SeparatedSequences.BaseParameters.dimension *
        ∑ᶠ y : ↥(s.params.layerSites s.Ω n),
          SeparatedSequences.BaseParameters.pointValue ω₁ (y.1 : s.params.Torus) *
            SeparatedSequences.BaseParameters.pointValue ω₂ (y.1 : s.params.Torus)
      = ∑ᶠ z : ↥(s.params.layerSites s.Ω n),
          𝒮.centreSpacing (s.toTorus s.unitTorusSide (z.1 : s.data.Point)) ^ 4 *
            ω₁ ⟨z.1, hmem z⟩ * ω₂ ⟨z.1, hmem z⟩ := by
        rw [← SeparatedSequences.BaseParameters.finsum_const_mul_finite]
        exact finsum_congr fun z => (hterm z).symm
    _ = ∑ᶠ y : {y : ↥(s.params.allLayerPoints s.Ω) // lev y = n},
          𝒮.centreSpacing (s.toTorus s.unitTorusSide y.1.1) ^ 4 * ω₁ y.1 * ω₂ y.1 :=
        finsum_comp_equiv E (f := fun y : {y : ↥(s.params.allLayerPoints s.Ω) // lev y = n} =>
          𝒮.centreSpacing (s.toTorus s.unitTorusSide y.1.1) ^ 4 * ω₁ y.1 * ω₂ y.1)
    _ = ∑ y ∈ Finset.univ with lev y = n,
          𝒮.centreSpacing (s.toTorus s.unitTorusSide y.1) ^ 4 * ω₁ y * ω₂ y := by
        rw [finsum_eq_sum_of_fintype]
        exact (Finset.sum_subtype (Finset.univ.filter fun y => lev y = n) (fun y => by simp)
          (fun y => 𝒮.centreSpacing (s.toTorus s.unitTorusSide y.1) ^ 4 * ω₁ y * ω₂ y)).symm
theorem averageZero_eq (h : s.IsBlockSetting 𝒮) (g : s.BlockSettingGeometry 𝒮)
    {f : s.data.SiteFn} (hf : f ∈ zeroFormsOn s.data.cutoff (s.Ω 0))
    {f' : Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ → ℝ}
    (sv : ∀ x, f x = f' (bareSiteEquiv g x))
    (y : ↥(s.params.allLayerPoints s.Ω)) :
    s.params.averageZero s.Ω ⟨f, hf⟩ y = 𝒮.cellAverage f' (s.toTorus s.unitTorusSide y.1) := by
  have hp := (s.params.exists_levelSite s.Ω y).choose_spec
  set p := s.params.levelSite s.Ω y with hpdef
  have hp' : p.1 ≤ s.params.t ∧ p.2 ∈ s.params.layerSites s.Ω p.1 ∧
      (p.2 : s.params.Torus) = y := hp
  let z : s.data.Apex s.Ω := ⟨p, hp'.1, hp'.2.1⟩
  have hzp : z.point = y.1 := hp'.2.2
  have hc := g.blocks z
  have hs : 𝒮.centreSpacing (s.toTorus s.unitTorusSide y.1) = s.params.levelMeshRatio p.1 := by
    rw [← hzp]
    exact centreSpacing_apex g z
  have hsum : (∑ᶠ x : {x : BareSite s.params.L s.params.m s.params.K //
        (x : s.params.Torus) ∈ SeparatedSequences.BaseParameters.fineBlock (D := s.params) p.2},
          f x.1) =
      ∑ᶠ x' ∈ {x' : Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ |
        (x' : Torus4 s.unitTorusSide) ∈ 𝒮.cell (s.toTorus s.unitTorusSide y.1)}, f' x' := by
    rw [← finsum_set_coe_eq_finsum_mem]
    let E : {x : BareSite s.params.L s.params.m s.params.K //
        (x : s.params.Torus) ∈ SeparatedSequences.BaseParameters.fineBlock (D := s.params) p.2} ≃
        ↥{x' : Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ |
          (x' : Torus4 s.unitTorusSide) ∈ 𝒮.cell (s.toTorus s.unitTorusSide y.1)} :=
      (bareSiteEquiv g).subtypeEquiv fun x => by
        change (x : s.data.Point) ∈ SeparatedSequences.BaseParameters.fineBlock (D := s.params) p.2 ↔
          s.toTorus s.unitTorusSide (x : s.data.Point) ∈ 𝒮.cell (s.toTorus s.unitTorusSide y.1)
        rw [← hzp, hc, (toTorus_injective s).mem_set_image]
        exact ⟨fun hx => hx.1, fun hx => ⟨hx, x.2⟩⟩
    rw [← finsum_comp_equiv E]
    exact finsum_congr fun x => sv x.1
  have hratio : (𝒮.ξ / s.params.levelMeshRatio p.1) ^ 4 = ((s.data.L : ℝ) ^ (p.1 * 4))⁻¹ := by
    have hL := (Lreal_pos s).ne'
    have hL' : (s.data.L : ℝ) ≠ 0 := hL
    have e : 𝒮.ξ / s.params.levelMeshRatio p.1 = ((s.data.L : ℝ) ^ p.1)⁻¹ := by
      rw [h.ξ_eq]
      change (s.data.L : ℝ) ^ (-(s.data.t : ℤ)) / (s.data.L : ℝ) ^ ((p.1 : ℤ) - (s.data.t : ℤ)) = _
      rw [zpow_sub₀ hL', zpow_neg]
      simp only [zpow_natCast]
      have h1 : (s.data.L : ℝ) ^ (s.data.t : ℕ) ≠ 0 := pow_ne_zero _ hL'
      have h2 : (s.data.L : ℝ) ^ p.1 ≠ 0 := pow_ne_zero _ hL'
      field_simp
    rw [e, inv_pow, ← pow_mul]
  change ((s.data.L : ℝ) ^ (p.1 * 4))⁻¹ * _ =
    (𝒮.ξ / 𝒮.centreSpacing (s.toTorus s.unitTorusSide y.1)) ^ 4 * _
  rw [hs, hratio, hsum]
theorem agreeAlong_iff (g : s.BlockSettingGeometry 𝒮) {f : s.data.SiteFn}
    {f' : Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ → ℝ} :
    AgreeAlong (s.scalarData.SiteRel (scalarDataOfBlockSetting 𝒮) (s.toTorus s.unitTorusSide))
        f f' ↔
      ∀ x, f x = f' (bareSiteEquiv g x) := by
  constructor
  · intro hv x
    exact hv x _ ((siteRel_iff g x _).2 rfl)
  · intro hv x x' hx
    rw [(siteRel_iff g x x').1 hx]
    exact hv x
section Operators
variable (h : s.IsBlockSetting 𝒮) (g : s.BlockSettingGeometry 𝒮)
theorem centreOf_eq (huniq : ∀ (x : s.data.BareSite) (p q : Σ n : ℕ, s.params.LatticeSite n),
      s.params.IsBlockCentreOf s.Ω (x : s.params.Torus) p →
      s.params.IsBlockCentreOf s.Ω (x : s.params.Torus) q → p = q)
    (x : s.data.BareSite) (z : s.data.Apex s.Ω)
    (hz : s.params.IsBlockCentreOf s.Ω (x : s.params.Torus) z.1) :
    𝒮.centreOf ((bareSiteEquiv g x : Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ) :
        Torus4 s.unitTorusSide) =
      s.toTorus s.unitTorusSide z.point := by
  have hall := g.allLayerSites
  have hsite : s.toTorus s.unitTorusSide z.point ∈ 𝒮.centres := by
    rw [← hall]
    exact ⟨z.point, mem_iUnion₂.mpr ⟨z.1.1, z.2.1, z.1.2, z.2.2, rfl⟩, rfl⟩
  have hcube : ((bareSiteEquiv g x : Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ) :
      Torus4 s.unitTorusSide) ∈ 𝒮.cell (s.toTorus s.unitTorusSide z.point) := by
    rw [g.blocks z, coe_bareSiteEquiv, (toTorus_injective s).mem_set_image]
    exact hz.2.2.1
  have hspec := Classical.epsilon_spec (p := fun y => y ∈ 𝒮.centres ∧
    ((bareSiteEquiv g x : Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ) :
      Torus4 s.unitTorusSide) ∈ 𝒮.cell y)
    ⟨_, hsite, hcube⟩
  change 𝒮.centreOf _ ∈ 𝒮.centres ∧ _ ∈ 𝒮.cell (𝒮.centreOf _) at hspec
  obtain ⟨hs, hc⟩ := hspec
  rw [← hall] at hs
  obtain ⟨w, hw, hww⟩ := hs
  obtain ⟨z', hz'⟩ := exists_apex (s := s) ⟨w, hw⟩
  have hz'' : z'.point = w := hz'
  rw [← hww, ← hz'', g.blocks z', coe_bareSiteEquiv, (toTorus_injective s).mem_set_image] at hc
  have hcen : s.params.IsBlockCentreOf s.Ω (x : s.params.Torus) z'.1 :=
    ⟨z'.2.1, z'.2.2, hc, x.2⟩
  have hpq := huniq x _ _ hcen hz
  rw [← hww, ← hz'']
  have : z' = z := Subtype.ext hpq
  rw [this]
include h in
theorem massiveZeroOperator_eq
    (hlap : ∀ f' : Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ → ℝ,
      Dirichlet.VanishesOff (𝒮.Ω 0) f' →
      ∀ x' : Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ, (x' : Torus4 s.unitTorusSide) ∈ 𝒮.Ω 0 →
        Dirichlet.latticeLaplacian f' x' = 𝒮.fullOperator f' x' - 𝒮.averagingOp f' x')
    (hform : ∀ (f : ZeroForms s.params.L s.params.m s.params.K)
      (x : BareSite s.params.L s.params.m s.params.K),
      scalarLaplacian s.params.L s.params.m s.params.K s.params.t f x =
        (finestMeshInLevelUnits s.params.L s.params.t ^ 2)⁻¹ * ∑ μ,
          ((f x - f (x + unitStep s.params.L s.params.m (levelDepth s.params.K 0) μ)) +
            (f x - f (x - unitStep s.params.L s.params.m (levelDepth s.params.K 0) μ))))
    (hstar : ∀ (ω : s.params.CoarseZeroForms s.Ω)
      (x : BareSite s.params.L s.params.m s.params.K), x ∈ sitesOfRegion s.params.K (s.Ω 0) →
      (s.params.averageZeroAdjoint s.Ω ω).1 x = SeparatedSequences.BaseParameters.pointValue ω
        ((s.params.blockCentre s.Ω (x : s.params.Torus)).2 : s.params.Torus))
    (hcentre : ∀ x : BareSite s.params.L s.params.m s.params.K,
      x ∈ sitesOfRegion s.params.K (s.Ω 0) →
      s.params.IsBlockCentreOf s.Ω (x : s.params.Torus)
        (s.params.blockCentre s.Ω (x : s.params.Torus)))
    (huniq : ∀ (x : s.data.BareSite) (p q : Σ n : ℕ, s.params.LatticeSite n),
      s.params.IsBlockCentreOf s.Ω (x : s.params.Torus) p →
      s.params.IsBlockCentreOf s.Ω (x : s.params.Torus) q → p = q)
    {f : s.data.SiteFn} (hf : f ∈ zeroFormsOn s.data.cutoff (s.Ω 0))
    {f' : Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ → ℝ}
    (sv : ∀ x, f x = f' (bareSiteEquiv g x))
    (x : s.data.BareSite) :
    (s.params.massiveZeroOperator s.Ω ⟨f, hf⟩).1 x = 𝒮.fullOperator f' (bareSiteEquiv g x) := by
  have hcomp : f' ∘ bareSiteEquiv g = f := funext fun x => (sv x).symm
  have hf' : Dirichlet.VanishesOff (𝒮.Ω 0) f' := (vanishesOff_iff h g f').2 (hcomp ▸ hf)
  by_cases hx : (x : s.data.Point) ∈ s.Ω 0
  · have hx' := (bareSiteEquiv_mem_iff h g x).2 hx
    have e1 := hlap f' hf' _ hx'
    have e2 : (s.params.massiveZeroOperator s.Ω ⟨f, hf⟩).1 x =
        (dirichletLaplacian s.params.K s.params.t (s.Ω 0) ⟨f, hf⟩).1 x +
          (s.params.weightedAverageZero s.Ω ⟨f, hf⟩).1 x := rfl
    have hchi : siteProjection s.params.K (s.Ω 0) f = f := by
      funext w
      by_cases hw : (w : s.data.Point) ∈ s.Ω 0
      · exact Set.indicator_of_mem (s := sitesOfRegion s.data.cutoff (s.Ω 0)) hw f
      · rw [mem_zeroFormsOn_iff.1 hf w hw]
        exact Set.indicator_of_notMem (s := sitesOfRegion s.data.cutoff (s.Ω 0)) hw f
    have e3 : (dirichletLaplacian s.params.K s.params.t (s.Ω 0) ⟨f, hf⟩).1 x =
        scalarLaplacian s.params.L s.params.m s.params.K s.params.t f x := by
      change siteProjection s.params.K (s.Ω 0) (scalarLaplacian s.params.L s.params.m s.params.K
        s.params.t (siteProjection s.params.K (s.Ω 0) f)) x = _
      rw [hchi]
      exact Set.indicator_of_mem (s := sitesOfRegion s.data.cutoff (s.Ω 0)) hx _
    have e5 : scalarLaplacian s.params.L s.params.m s.params.K s.params.t f x =
        Dirichlet.latticeLaplacian f' (bareSiteEquiv g x) := by
      have hξ : finestMeshInLevelUnits s.params.L s.params.t = 𝒮.ξ := by
        rw [h.ξ_eq]
        rfl
      rw [hform, hξ, Finset.mul_sum]
      simp only [Dirichlet.latticeLaplacian, Dirichlet.latticeDiv,
        Dirichlet.grad, Dirichlet.backwardDiff, Dirichlet.forwardDiff]
      refine Finset.sum_congr rfl fun μ _ => ?_
      have hplus := sv (x + unitStep s.data.L s.data.m (levelDepth s.data.cutoff 0) μ)
      have hminus := sv (x - unitStep s.data.L s.data.m (levelDepth s.data.cutoff 0) μ)
      rw [bareSiteEquiv_add h g] at hplus
      rw [bareSiteEquiv_sub h g] at hminus
      change (𝒮.ξ ^ 2)⁻¹ * ((f x - f (x + unitStep s.data.L s.data.m (levelDepth s.data.cutoff 0) μ)) +
        (f x - f (x - unitStep s.data.L s.data.m (levelDepth s.data.cutoff 0) μ))) = _
      rw [hplus, hminus, sv x, sub_add_cancel]
      ring
    have e4 : (s.params.weightedAverageZero s.Ω ⟨f, hf⟩).1 x =
        𝒮.averagingOp f' (bareSiteEquiv g x) := by
      have hcen := hcentre x hx
      change (s.params.averageZeroAdjoint s.Ω (s.params.weightMulZero s.Ω
        (s.params.averageZero s.Ω ⟨f, hf⟩))).1 x = _
      rw [hstar _ x hx]
      set p := s.params.blockCentre s.Ω (x : s.params.Torus) with hp
      let z : s.data.Apex s.Ω := ⟨p, hcen.1, hcen.2.1⟩
      have hy : (p.2 : s.params.Torus) ∈ s.params.allLayerPoints s.Ω :=
        mem_iUnion₂.mpr ⟨p.1, hcen.1, p.2, hcen.2.1, rfl⟩
      have hq := (s.params.exists_levelSite s.Ω ⟨p.2, hy⟩).choose_spec
      set q := s.params.levelSite s.Ω ⟨p.2, hy⟩ with hqdef
      have hq' : q.1 ≤ s.params.t ∧ q.2 ∈ s.params.layerSites s.Ω q.1 ∧
          (q.2 : s.params.Torus) = p.2 := hq
      let z' : s.data.Apex s.Ω := ⟨q, hq'.1, hq'.2.1⟩
      have hzz : z'.point = z.point := hq'.2.2
      have hlevel : q.1 = p.1 := by
        have i1 := centreIndex_apex h g z'
        have i2 := centreIndex_apex h g z
        rw [hzz] at i1
        exact i1.symm.trans i2
      have hterm : SeparatedSequences.BaseParameters.pointValue (s.params.weightMulZero s.Ω
          (s.params.averageZero s.Ω ⟨f, hf⟩)) (p.2 : s.params.Torus) =
          s.params.levelWeight q.1 * (s.params.levelMeshRatio q.1 ^ 2)⁻¹ *
            s.params.averageZero s.Ω ⟨f, hf⟩ ⟨p.2, hy⟩ := by
        simp only [SeparatedSequences.BaseParameters.pointValue, dif_pos hy]
        rfl
      rw [hterm, hlevel, averageZero_eq h g hf sv]
      have hchiP : 𝒮.averagingOp f' (bareSiteEquiv g x) =
          𝒮.a (𝒮.centreIndex (𝒮.centreOf
              (bareSiteEquiv g x : Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ))) *
            (𝒮.centreSpacing (𝒮.centreOf
              (bareSiteEquiv g x : Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ)) ^ 2)⁻¹ *
            𝒮.cellAverage f' (𝒮.centreOf
              (bareSiteEquiv g x : Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ)) :=
        Set.indicator_of_mem (s := {w : Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ |
          (w : Torus4 s.unitTorusSide) ∈ 𝒮.Ω 0}) hx'
          (fun w : Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ =>
            𝒮.a (𝒮.centreIndex (𝒮.centreOf (w : Torus4 s.unitTorusSide))) *
              (𝒮.centreSpacing (𝒮.centreOf (w : Torus4 s.unitTorusSide)) ^ 2)⁻¹ *
              𝒮.cellAverage f' (𝒮.centreOf (w : Torus4 s.unitTorusSide)))
      have hc := centreOf_eq g huniq x z hcen
      rw [hchiP, hc, centreIndex_apex h g z, centreSpacing_apex g z]
      have hw := h.a_eq z.level hcen.1
      rw [hw]
      rfl
    rw [e2, e3, e4, e5, e1]
    ring
  · have hx' : ((bareSiteEquiv g x : Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ) :
        Torus4 s.unitTorusSide) ∉ 𝒮.Ω 0 := fun hm => hx ((bareSiteEquiv_mem_iff h g x).1 hm)
    rw [mem_zeroFormsOn_iff.1 (s.params.massiveZeroOperator s.Ω ⟨f, hf⟩).2 x hx]
    simp only [Dirichlet.BlockSetting.fullOperator, Dirichlet.BlockSetting.blockOperator,
      Pi.add_apply, Dirichlet.dirichletLaplacian, Dirichlet.restrictTo]
    rw [Set.indicator_of_notMem (s := {w : Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ |
        (w : Torus4 s.unitTorusSide) ∈ 𝒮.Ω 0}) hx',
      Set.indicator_of_notMem (s := {w : Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ |
        (w : Torus4 s.unitTorusSide) ∈ 𝒮.Ω 0}) hx']
    simp
include h in
theorem zeroGreen_eq
    (hop : ∀ {f : s.data.SiteFn} (hf : f ∈ zeroFormsOn s.data.cutoff (s.Ω 0))
      {f' : Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ → ℝ},
      (∀ x, f x = f' (bareSiteEquiv g x)) →
      ∀ x : s.data.BareSite,
        (s.params.massiveZeroOperator s.Ω ⟨f, hf⟩).1 x = 𝒮.fullOperator f' (bareSiteEquiv g x))
    (hunit : IsUnit (s.params.massiveZeroOperator s.Ω))
    {f : s.data.SiteFn} (hf : f ∈ zeroFormsOn s.data.cutoff (s.Ω 0))
    {f' : Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ → ℝ}
    (sv : ∀ x, f x = f' (bareSiteEquiv g x))
    (x : s.data.BareSite) :
    (s.params.zeroGreen s.Ω ⟨f, hf⟩).1 x = 𝒮.fullGreen f' (bareSiteEquiv g x) := by
  have hcomp : f' ∘ bareSiteEquiv g = f := funext fun x => (sv x).symm
  have hf' : Dirichlet.VanishesOff (𝒮.Ω 0) f' := (vanishesOff_iff h g f').2 (hcomp ▸ hf)
  have hMG : s.params.massiveZeroOperator s.Ω (s.params.zeroGreen s.Ω ⟨f, hf⟩) = ⟨f, hf⟩ :=
    LinearMap.congr_fun (Ring.mul_inverse_cancel _ hunit) _
  set G := s.params.zeroGreen s.Ω ⟨f, hf⟩ with hG
  have hGf : (G.1 : s.data.SiteFn) ∈ zeroFormsOn s.data.cutoff (s.Ω 0) := G.2
  have svG : ∀ x, G.1 x = pushField g G.1 (bareSiteEquiv g x) := fun x => by simp [pushField]
  have hgmem : Dirichlet.VanishesOff (𝒮.Ω 0) (pushField g G.1) :=
    (vanishesOff_iff h g _).2 (by rw [pushField_comp]; exact hGf)
  have hchi : Dirichlet.restrictTo (𝒮.Ω 0) f' = f' := by
    funext w
    by_cases hw : (w : Torus4 s.unitTorusSide) ∈ 𝒮.Ω 0
    · exact Set.indicator_of_mem (s := {w : Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ |
        (w : Torus4 s.unitTorusSide) ∈ 𝒮.Ω 0}) hw f'
    · rw [hf' w hw]
      exact Set.indicator_of_notMem (s := {w : Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ |
        (w : Torus4 s.unitTorusSide) ∈ 𝒮.Ω 0}) hw f'
  have hA : 𝒮.fullOperator (pushField g G.1) = f' := by
    funext w
    obtain ⟨y, rfl⟩ := (bareSiteEquiv g).surjective w
    rw [← hop hGf svG y, ← sv y]
    exact congrArg (fun F : ↥(zeroFormsOn s.data.cutoff (s.Ω 0)) => F.1 y) hMG
  have hex : ∃ k : Dirichlet.LatticeSite 4 s.unitTorusSide 𝒮.ξ → ℝ,
      Dirichlet.VanishesOff (𝒮.Ω 0) k ∧
        𝒮.blockOperator (𝒮.Ω 0) (Dirichlet.boundaryBonds (𝒮.Ω 0)) k =
          Dirichlet.restrictTo (𝒮.Ω 0) f' :=
    ⟨_, hgmem, by rw [hchi]; exact hA⟩
  have hk := Classical.epsilon_spec hex
  change Dirichlet.VanishesOff (𝒮.Ω 0) (𝒮.fullGreen f') ∧
    𝒮.fullOperator (𝒮.fullGreen f') = Dirichlet.restrictTo (𝒮.Ω 0) f' at hk
  obtain ⟨hk1, hk2⟩ := hk
  rw [hchi] at hk2
  have hHmem := (vanishesOff_iff h g (𝒮.fullGreen f')).1 hk1
  have hMH : s.params.massiveZeroOperator s.Ω ⟨𝒮.fullGreen f' ∘ bareSiteEquiv g, hHmem⟩ =
      ⟨f, hf⟩ := by
    apply Subtype.ext
    funext y
    rw [hop hHmem (fun _ => rfl) y, hk2]
    exact (sv y).symm
  have hinv := LinearMap.congr_fun (Ring.inverse_mul_cancel _ hunit)
    (⟨𝒮.fullGreen f' ∘ bareSiteEquiv g, hHmem⟩ : ↥(zeroFormsOn s.data.cutoff (s.Ω 0)))
  have hHG : (⟨𝒮.fullGreen f' ∘ bareSiteEquiv g, hHmem⟩ :
      ↥(zeroFormsOn s.data.cutoff (s.Ω 0))) = G := by
    have h1 : Ring.inverse (s.params.massiveZeroOperator s.Ω)
        (s.params.massiveZeroOperator s.Ω ⟨𝒮.fullGreen f' ∘ bareSiteEquiv g, hHmem⟩) =
        ⟨𝒮.fullGreen f' ∘ bareSiteEquiv g, hHmem⟩ := hinv
    rw [hMH] at h1
    exact h1.symm
  rw [← hHG]
  rfl
end Operators
theorem coarseRel_iff (g : s.BlockSettingGeometry 𝒮)
    (y : ↥(s.params.allLayerPoints s.Ω)) (y' : ↥𝒮.centres) :
    s.scalarData.CoarseRel (scalarDataOfBlockSetting 𝒮) (s.toTorus s.unitTorusSide) y y' ↔
      y' = coarseEquiv g y := by
  constructor
  · intro hy
    exact Subtype.ext hy.symm
  · rintro rfl
    rfl
end Setting
theorem pairsUniquely_of_equiv {X X' : Type} (e : X ≃ X') (R : X → X' → Prop)
    (hR : ∀ x x', R x x' ↔ x' = e x) : PairsUniquely R :=
  ⟨fun x => ⟨e x, (hR x _).2 rfl, fun x' hx => (hR x x').1 hx⟩,
    fun x' => ⟨e.symm x', (hR _ _).2 (by simp), fun x hx => by
      rw [(hR x x').1 hx]
      simp⟩⟩
end SeparatedClasses.BlockSettingScalarData
end YangMills.Construction
