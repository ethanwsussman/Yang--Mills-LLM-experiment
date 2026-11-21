import YangMills.Construction.Lattice.WeightedFunctionSpacesAndTensors
import YangMills.Construction.RegionSequence.GaugeLaplacianPositivityProof
import YangMills.Construction.SeparatedSequences.ClassGeometryInASettingOfRegions
import YangMills.Construction.SeparatedSequences.ClassProjectionOnAGeneralTorusProof
import YangMills.Construction.SeparatedSequences.ClassSequenceIsSeparatedForItsNumbers
import YangMills.Construction.SeparatedSequences.ClassSiteFunctionsInASettingOfTheTorusOfLevelSideProof
import YangMills.Construction.SeparatedSequences.WeightsOfAClassSequenceAtOne
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric PeriodicLattice.DirichletOperators
namespace SeparatedClasses
namespace ScalarCorrespondence
open SingleSequence SingleSequence.SequenceData
section Read
variable (s : SequenceData) {S : ℝ}
theorem toTorus_apply (hS : S ≠ 0) (x : s.data.Point) (μ : Fin 4) :
    s.toTorus S x μ = AddCircle.equivAddCircle _ S s.torusSide_ne_zero hS (x μ) := by
  rw [SequenceData.toTorus, dif_pos hS]
theorem toTorus_injective (hS : S ≠ 0) : Function.Injective (s.toTorus S) := by
  intro x y h
  funext μ
  have h' := congrFun h μ
  rw [toTorus_apply s hS, toTorus_apply s hS] at h'
  exact (AddCircle.equivAddCircle _ S s.torusSide_ne_zero hS).injective h'
theorem toTorus_add (hS : S ≠ 0) (x y : s.data.Point) :
    s.toTorus S (x + y) = s.toTorus S x + s.toTorus S y := by
  funext μ
  simp only [Pi.add_apply, toTorus_apply s hS, map_add]
theorem toTorus_sub (hS : S ≠ 0) (x y : s.data.Point) :
    s.toTorus S (x - y) = s.toTorus S x - s.toTorus S y := by
  funext μ
  simp only [Pi.sub_apply, toTorus_apply s hS, map_sub]
theorem cast_L_ne_zero : (s.data.L : ℝ) ≠ 0 := by apply _root_.YangMills.Construction.SeparatedClasses.GaugeProjectionOfClass.blockFactor_cast_ne_zero <;> assumption
theorem unitTorusSide_ne_zero : s.unitTorusSide ≠ 0 := by apply _root_.YangMills.Construction.SeparatedClasses.BlockSettingScalarData.unitTorusSide_ne_zero <;> assumption
theorem meshSize_mul_ratio :
    PeriodicLattice.meshSize s.data.L (PeriodicLattice.levelDepth s.data.cutoff 0) *
      ((PeriodicLattice.torusSide s.data.L s.data.m)⁻¹ * s.unitTorusSide) = s.mesh := by apply _root_.YangMills.Construction.SeparatedClasses.BlockSettingScalarData.meshSize_mul_scale <;> assumption
theorem toTorus_unitStep {ξ : ℝ} (hS : S = s.unitTorusSide) (hξ : ξ = s.mesh) (μ : Fin 4) :
    s.toTorus S ((PeriodicLattice.unitStep s.data.L s.data.m
      (PeriodicLattice.levelDepth s.data.cutoff 0) μ : PeriodicLattice.Site _ _ _) : s.data.Point) =
      ((Dirichlet.unitStep 4 S ξ μ : Dirichlet.LatticeSite 4 S ξ) : Torus.PeriodicTorus 4 S) := by
  subst hS hξ
  have hS := unitTorusSide_ne_zero s
  funext ν
  rw [toTorus_apply s hS]
  by_cases h : ν = μ
  · subst h
    have e : ((PeriodicLattice.unitStep s.data.L s.data.m
        (PeriodicLattice.levelDepth s.data.cutoff 0) ν : PeriodicLattice.Site _ _ _) :
          s.data.Point) ν =
        ((PeriodicLattice.meshSize s.data.L (PeriodicLattice.levelDepth s.data.cutoff 0) : ℝ) :
          AddCircle (PeriodicLattice.torusSide s.data.L s.data.m)) := by
      simp [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis]
    rw [e, AddCircle.equivAddCircle_apply_mk, meshSize_mul_ratio]
    simp [Dirichlet.unitStep, Torus.torusProj]
  · have e : ((PeriodicLattice.unitStep s.data.L s.data.m
        (PeriodicLattice.levelDepth s.data.cutoff 0) μ : PeriodicLattice.Site _ _ _) :
          s.data.Point) ν = 0 := by
      simp [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne h]
    rw [e, map_zero]
    simp [Dirichlet.unitStep, Torus.torusProj, Pi.single_eq_of_ne h]
end Read
section General
theorem mem_zeroFormsOn_iff {L m K : ℕ} {Ω₀ : Set (PeriodicLattice.FourTorus L m)}
    {f : ZeroForms L m K} :
    f ∈ zeroFormsOn K Ω₀ ↔ ∀ x : BareSite L m K, (x : PeriodicLattice.FourTorus L m) ∉ Ω₀ →
      f x = 0 := by
  constructor
  · rintro ⟨g, rfl⟩ x hx
    show indicator (sitesOfRegion K Ω₀) g x = 0
    exact indicator_of_notMem (show x ∉ sitesOfRegion K Ω₀ from hx) g
  · intro h
    refine ⟨f, ?_⟩
    funext x
    show indicator (sitesOfRegion K Ω₀) f x = f x
    by_cases hx : (x : PeriodicLattice.FourTorus L m) ∈ Ω₀
    · exact indicator_of_mem (show x ∈ sitesOfRegion K Ω₀ from hx) f
    · rw [h x hx]
      exact indicator_of_notMem (show x ∉ sitesOfRegion K Ω₀ from hx) f
theorem siteProjection_of_mem {L m K : ℕ} {Ω₀ : Set (PeriodicLattice.FourTorus L m)}
    {f : ZeroForms L m K} (hf : f ∈ zeroFormsOn K Ω₀) : siteProjection K Ω₀ f = f := by
  obtain ⟨g, hg⟩ := hf
  rw [← hg]
  funext x
  show indicator (sitesOfRegion K Ω₀) (indicator (sitesOfRegion K Ω₀) g) x =
    indicator (sitesOfRegion K Ω₀) g x
  rw [indicator_indicator, inter_self]
theorem eq_of_weighted_sum_eq {ι : Type} [Finite ι] {ξ : ℝ} (hξ : ξ ≠ 0) {a b : ι → ℝ}
    (h : ξ ^ 4 * ∑ᶠ i, a i * (a i - b i) = ξ ^ 4 * ∑ᶠ i, b i * (a i - b i)) : a = b := by
  have hξ4 : ξ ^ 4 ≠ 0 := pow_ne_zero _ hξ
  have h1 := mul_left_cancel₀ hξ4 h
  have := Fintype.ofFinite ι
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, ← sub_eq_zero,
    ← Finset.sum_sub_distrib] at h1
  have h2 : ∑ i, (a i - b i) ^ 2 = 0 := by
    rw [← h1]
    exact Finset.sum_congr rfl fun i _ => by ring
  funext i
  have h3 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (a i - b i)).1 h2 i
    (Finset.mem_univ i)
  exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h3)
theorem extendByZero_of_mem {X Y : Type} {E : Submodule ℝ (X → ℝ)} (T : ↥E → Y → ℝ) {f : X → ℝ}
    (h : f ∈ E) : _root_.YangMills.Construction.SeparatedClasses.SingleSequence.extendByZero E T f = T ⟨f, h⟩ :=
  dif_pos h
end General
def apexOf (s : SequenceData) (v : ↥(s.params.allLayerPoints s.Ω)) : s.data.Apex s.Ω :=
  ⟨s.params.levelSite s.Ω v, (s.params.exists_levelSite s.Ω v).choose_spec.1,
    (s.params.exists_levelSite s.Ω v).choose_spec.2.1⟩
theorem apexOf_point (s : SequenceData) (v : ↥(s.params.allLayerPoints s.Ω)) :
    (apexOf s v).point = v.1 :=
  (s.params.exists_levelSite s.Ω v).choose_spec.2.2
structure Transfer (s : SequenceData) (𝒮 : RegionSequence.NestedRegions) where
  fineEquiv : s.data.BareSite ≃ 𝒮.FineSite
  fineEquiv_coe : ∀ x, ((fineEquiv x : 𝒮.FineSite) : 𝒮.Point) =
    s.toTorus 𝒮.side (x : s.data.Point)
  centreEquiv : ↥(s.params.allLayerPoints s.Ω) ≃ ↥𝒮.allCentres
  centreEquiv_coe : ∀ y, ((centreEquiv y : ↥𝒮.allCentres) : 𝒮.Point) = s.toTorus 𝒮.side y.1
  nested : s.IsNestedRegions 𝒮
  geom : s.NestedGeometry 𝒮
  unitWeights : s.WeightsAtUnitMass
  lap_apply : ∀ (f : ZeroForms s.data.L s.data.m s.data.cutoff)
    (x : BareSite s.data.L s.data.m s.data.cutoff),
    scalarLaplacian s.data.L s.data.m s.data.cutoff s.data.t f x =
      (PeriodicLattice.finestMeshInLevelUnits s.data.L s.data.t ^ 2)⁻¹ * ∑ μ,
        ((f x - f (x + PeriodicLattice.unitStep s.data.L s.data.m
            (PeriodicLattice.levelDepth s.data.cutoff 0) μ)) +
          (f x - f (x - PeriodicLattice.unitStep s.data.L s.data.m
            (PeriodicLattice.levelDepth s.data.cutoff 0) μ)))
  isUnit_op : IsUnit (s.params.massiveZeroOperator s.Ω)
  isAdjoint : FiniteDimReal.IsAdjointFor (s.params.restrictedZeroInner s.Ω)
    (s.params.coarseZeroInner s.Ω) (s.params.averageZero s.Ω)
    (s.params.averageZeroAdjoint s.Ω)
  coarseInner_eq : ∀ f g, s.params.coarseZeroInner s.Ω f g =
    ∑ᶠ v, s.params.pointMesh s.Ω v ^ 4 * (f v * g v)
namespace Transfer
variable {s : SequenceData} {𝒮 : RegionSequence.NestedRegions} (B : Transfer s 𝒮)
theorem mem_region_zero (x : s.data.BareSite) :
    ((B.fineEquiv x : 𝒮.FineSite) : 𝒮.Point) ∈ 𝒮.Ω 0 ↔ (x : s.data.Point) ∈ s.Ω 0 := by
  rw [B.fineEquiv_coe, B.nested.Ω_eq 0, SequenceData.regionOn]
  exact (toTorus_injective s 𝒮.side_pos.ne').mem_set_image
include B in
theorem finite_fineSite : Finite 𝒮.FineSite := by
  have : Finite s.data.BareSite := s.params.instFiniteLatticeSite 0
  exact Finite.of_equiv _ B.fineEquiv
theorem mem_iff_mem_siteFns {f : ZeroForms s.data.L s.data.m s.data.cutoff}
    {f' : 𝒮.FineSite → ℝ} (hf : ∀ x, f x = f' (B.fineEquiv x)) :
    f ∈ zeroFormsOn s.data.cutoff (s.Ω 0) ↔ f' ∈ 𝒮.siteFns := by
  rw [mem_zeroFormsOn_iff]
  constructor
  · intro h x' hx'
    obtain ⟨x, rfl⟩ := B.fineEquiv.surjective x'
    rw [← hf]
    exact h x fun hx => hx' ((B.mem_region_zero x).2 hx)
  · intro h x hx
    rw [hf]
    exact h _ fun hx' => hx ((B.mem_region_zero x).1 hx')
include B in
theorem finestMesh_eq : PeriodicLattice.finestMeshInLevelUnits s.data.L s.data.t = 𝒮.ξ := by
  rw [B.nested.ξ_eq]
  rfl
theorem latticeInner_eq {f g : ZeroForms s.data.L s.data.m s.data.cutoff}
    {f' g' : 𝒮.FineSite → ℝ}
    (hf : ∀ x, f x = f' (B.fineEquiv x)) (hg : ∀ x, g x = g' (B.fineEquiv x)) :
    latticeInner s.data.L s.data.t f g = Dirichlet.innerSum f' g' := by
  have h : ∑ᶠ x, f x * g x = ∑ᶠ x', f' x' * g' x' := by
    rw [← finsum_comp_equiv B.fineEquiv]
    exact finsum_congr fun x => by rw [hf, hg]
  simp only [latticeInner, Dirichlet.innerSum, h, B.finestMesh_eq]
theorem fineEquiv_add_unitStep (x : s.data.BareSite) (μ : Fin 4) :
    B.fineEquiv (x + PeriodicLattice.unitStep s.data.L s.data.m
      (PeriodicLattice.levelDepth s.data.cutoff 0) μ) =
      B.fineEquiv x + Dirichlet.unitStep 4 𝒮.side 𝒮.ξ μ := by
  apply Subtype.ext
  rw [B.fineEquiv_coe, AddSubgroup.coe_add, AddSubgroup.coe_add, toTorus_add s 𝒮.side_pos.ne',
    toTorus_unitStep s B.nested.side_eq B.nested.ξ_eq, B.fineEquiv_coe]
theorem fineEquiv_sub_unitStep (x : s.data.BareSite) (μ : Fin 4) :
    B.fineEquiv (x - PeriodicLattice.unitStep s.data.L s.data.m
      (PeriodicLattice.levelDepth s.data.cutoff 0) μ) =
      B.fineEquiv x - Dirichlet.unitStep 4 𝒮.side 𝒮.ξ μ := by
  apply Subtype.ext
  rw [B.fineEquiv_coe, AddSubgroup.coe_sub, AddSubgroup.coe_sub, toTorus_sub s 𝒮.side_pos.ne',
    toTorus_unitStep s B.nested.side_eq B.nested.ξ_eq, B.fineEquiv_coe]
theorem scalarLaplacian_eq {f : ZeroForms s.data.L s.data.m s.data.cutoff}
    {f' : 𝒮.FineSite → ℝ} (hf : ∀ x, f x = f' (B.fineEquiv x)) (x : s.data.BareSite) :
    scalarLaplacian s.data.L s.data.m s.data.cutoff s.data.t f x =
      Dirichlet.latticeLaplacian f' (B.fineEquiv x) := by
  rw [B.lap_apply, B.finestMesh_eq]
  simp only [Dirichlet.latticeLaplacian, Dirichlet.latticeDiv, Dirichlet.grad,
    Dirichlet.backwardDiff, Dirichlet.forwardDiff, sub_add_cancel]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [hf, hf, hf, fineEquiv_add_unitStep, fineEquiv_sub_unitStep]
  ring
end Transfer
namespace Transfer
variable {s : SequenceData} {𝒮 : RegionSequence.NestedRegions} (B : Transfer s 𝒮)
include B
theorem levelScale_eq (v : ↥(s.params.allLayerPoints s.Ω)) :
    𝒮.levelScale ((B.centreEquiv v : ↥𝒮.allCentres) : 𝒮.Point) =
      s.data.coarseMesh (s.params.levelSite s.Ω v).1 := by
  have h : 𝒮.levelScale (s.toTorus 𝒮.side (apexOf s v).point) = (apexOf s v).mesh :=
    B.geom.meshes (apexOf s v)
  rw [apexOf_point] at h
  rw [B.centreEquiv_coe]
  exact h
theorem level_eq (v : ↥(s.params.allLayerPoints s.Ω)) :
    𝒮.level ((B.centreEquiv v : ↥𝒮.allCentres) : 𝒮.Point) = (s.params.levelSite s.Ω v).1 := by
  have hL := cast_L_ne_zero s
  have h : (𝒮.L : ℝ) ^ ((𝒮.level ((B.centreEquiv v : ↥𝒮.allCentres) : 𝒮.Point) : ℕ) : ℤ) *
      𝒮.ξ = (s.data.L : ℝ) ^ (((s.params.levelSite s.Ω v).1 : ℤ) - (s.data.t : ℤ)) :=
    B.levelScale_eq v
  rw [B.nested.L_eq, B.nested.ξ_eq] at h
  have hx : s.mesh = (s.data.L : ℝ) ^ (-(s.data.t : ℤ)) := rfl
  rw [hx, sub_eq_add_neg, zpow_add₀ hL] at h
  have h3 := mul_right_cancel₀ (zpow_ne_zero _ hL) h
  rw [zpow_natCast, zpow_natCast] at h3
  have h4 : s.data.L ^ 𝒮.level ((B.centreEquiv v : ↥𝒮.allCentres) : 𝒮.Point) =
      s.data.L ^ (s.params.levelSite s.Ω v).1 := by exact_mod_cast h3
  have h2 : 2 ≤ s.data.L := by
    have := s.data.isAdmissible.2
    omega
  exact Nat.pow_right_injective h2 h4
theorem cellOf_eq (v : ↥(s.params.allLayerPoints s.Ω)) :
    𝒮.cellOf ((B.centreEquiv v : ↥𝒮.allCentres) : 𝒮.Point) =
      s.toTorus 𝒮.side '' (apexOf s v).block := by
  have h : 𝒮.cellOf (s.toTorus 𝒮.side (apexOf s v).point) =
      s.toTorus 𝒮.side '' (apexOf s v).block :=
    B.geom.blocks (apexOf s v)
  rw [apexOf_point] at h
  rw [B.centreEquiv_coe]
  exact h
theorem mem_fineBlock_iff (v : ↥(s.params.allLayerPoints s.Ω)) (x : s.data.BareSite) :
    B.fineEquiv x ∈ 𝒮.fineBlock (s.params.levelSite s.Ω v).1
        ((B.centreEquiv v : ↥𝒮.allCentres) : 𝒮.Point) ↔
      (x : s.data.Point) ∈
        SeparatedSequences.BaseParameters.fineBlock (D := s.params)
          (s.params.levelSite s.Ω v).2 := by
  have hc : 𝒮.fineBlock (𝒮.level ((B.centreEquiv v : ↥𝒮.allCentres) : 𝒮.Point))
      ((B.centreEquiv v : ↥𝒮.allCentres) : 𝒮.Point) =
      {x : 𝒮.FineSite | (x : 𝒮.Point) ∈
        𝒮.cellOf ((B.centreEquiv v : ↥𝒮.allCentres) : 𝒮.Point)} := rfl
  rw [B.level_eq] at hc
  rw [hc, mem_ofPred_eq, B.fineEquiv_coe, B.cellOf_eq,
    (toTorus_injective s 𝒮.side_pos.ne').mem_set_image]
  exact ⟨fun h => ⟨h, x.2⟩, fun h => h.1⟩
theorem averageZero_eq {f : ZeroForms s.data.L s.data.m s.data.cutoff} {f' : 𝒮.FineSite → ℝ}
    (hm : f ∈ zeroFormsOn s.data.cutoff (s.Ω 0)) (hf : ∀ x, f x = f' (B.fineEquiv x))
    (v : ↥(s.params.allLayerPoints s.Ω)) :
    s.params.averageZero s.Ω ⟨f, hm⟩ v =
      RegionSequence.NestedRegions.blockAvg f' (B.centreEquiv v) := by
  have hs : ∑ᶠ x : {x : BareSite s.data.L s.data.m s.data.cutoff // (x : s.data.Point) ∈
        SeparatedSequences.BaseParameters.fineBlock (D := s.params)
          (s.params.levelSite s.Ω v).2}, f x.1 =
      ∑ᶠ x' ∈ 𝒮.fineBlock (s.params.levelSite s.Ω v).1
        ((B.centreEquiv v : ↥𝒮.allCentres) : 𝒮.Point), f' x' := by
    refine (finsum_subtype_eq_finsum_cond (f := f) _).trans ?_
    refine Eq.trans ?_ (finsum_comp_equiv B.fineEquiv)
    exact finsum_congr fun x =>
      finsum_congr_Prop (propext (B.mem_fineBlock_iff v x).symm) fun _ => hf x
  show ((s.data.L : ℝ) ^ ((s.params.levelSite s.Ω v).1 * 4))⁻¹ * _ =
    ((𝒮.L : ℝ) ^ (𝒮.level ((B.centreEquiv v : ↥𝒮.allCentres) : 𝒮.Point) * 4))⁻¹ *
      ∑ᶠ x ∈ 𝒮.fineBlock (𝒮.level ((B.centreEquiv v : ↥𝒮.allCentres) : 𝒮.Point))
        ((B.centreEquiv v : ↥𝒮.allCentres) : 𝒮.Point), f' x
  rw [B.nested.L_eq, B.level_eq, ← hs]
theorem coarseZeroInner_eq {ω₁ ω₂ : s.params.CoarseZeroForms s.Ω} {w₁ w₂ : 𝒮.Coarse}
    (h₁ : ∀ v, ω₁ v = w₁ (B.centreEquiv v)) (h₂ : ∀ v, ω₂ v = w₂ (B.centreEquiv v)) :
    s.params.coarseZeroInner s.Ω ω₁ ω₂ = RegionSequence.NestedRegions.coarseInner w₁ w₂ := by
  rw [B.coarseInner_eq]
  refine Eq.trans ?_ (finsum_comp_equiv B.centreEquiv)
  refine finsum_congr fun v => ?_
  have hs : s.params.pointMesh s.Ω v =
      𝒮.levelScale ((B.centreEquiv v : ↥𝒮.allCentres) : 𝒮.Point) :=
    (B.levelScale_eq v).symm
  rw [h₁, h₂, hs]
  ring
theorem averageZeroAdjoint_eq (ω : s.params.CoarseZeroForms s.Ω) (w : 𝒮.Coarse)
    (hω : ∀ v, ω v = w (B.centreEquiv v)) (x : s.data.BareSite) :
    (s.params.averageZeroAdjoint s.Ω ω).1 x =
      RegionSequence.NestedRegions.blockAvgAdj w (B.fineEquiv x) := by
  have := B.finite_fineSite
  obtain ⟨F, hF⟩ : ∃ F, F = s.params.averageZeroAdjoint s.Ω ω := ⟨_, rfl⟩
  rw [← hF]
  let v₀ : 𝒮.FineSite → ℝ := fun x' => F.1 (B.fineEquiv.symm x')
  have hv₀ : ∀ x, F.1 x = v₀ (B.fineEquiv x) := fun x => by simp [v₀]
  have hmem₀ : v₀ ∈ 𝒮.siteFns := (B.mem_iff_mem_siteFns hv₀).1 F.2
  let P : (𝒮.FineSite → ℝ) → Prop := fun v => v ∈ (𝒮.siteFns : Set (𝒮.FineSite → ℝ)) ∧
    ∀ u ∈ (𝒮.siteFns : Set (𝒮.FineSite → ℝ)), Dirichlet.innerSum v u =
      RegionSequence.NestedRegions.coarseInner w (RegionSequence.NestedRegions.blockAvg u)
  have hP₀ : P v₀ := by
    refine ⟨hmem₀, fun u hu => ?_⟩
    have hu₀ : ∀ x, (fun x => u (B.fineEquiv x)) x = u (B.fineEquiv x) := fun _ => rfl
    have hm := (B.mem_iff_mem_siteFns hu₀).2 hu
    rw [← B.latticeInner_eq hv₀ hu₀]
    have h := B.isAdjoint ⟨fun x => u (B.fineEquiv x), hm⟩ ω
    rw [← hF] at h
    exact h.symm.trans (B.coarseZeroInner_eq hω fun v => B.averageZero_eq hm hu₀ v)
  have hP : P (RegionSequence.NestedRegions.blockAvgAdj w) :=
    Classical.epsilon_spec (⟨v₀, hP₀⟩ : ∃ v, P v)
  have heq : RegionSequence.NestedRegions.blockAvgAdj w = v₀ := by
    have hd : RegionSequence.NestedRegions.blockAvgAdj w - v₀ ∈ 𝒮.siteFns :=
      sub_mem hP.1 hmem₀
    exact eq_of_weighted_sum_eq 𝒮.ξ_pos.ne' ((hP.2 _ hd).trans (hP₀.2 _ hd).symm)
  rw [hv₀, heq]
theorem levelWeight_eq (n : ℕ) : s.params.levelWeight n = Dirichlet.blockWeights 𝒮.L n := by
  rw [B.nested.L_eq]
  have hsucc : ∀ n, s.params.levelWeight (n + 1) =
      Dirichlet.blockWeights s.data.L (n + 1) := by
    intro n
    induction n with
    | zero => exact B.unitWeights.one
    | succ n ih =>
      rw [B.unitWeights.succ (n + 1) (by omega), ih]
      have e : s.Lreal ^ (-2 : ℤ) = ((s.data.L : ℝ) ^ 2)⁻¹ := by
        rw [zpow_neg]
        rfl
      rw [e]
      rfl
  cases n with
  | zero => exact B.unitWeights.zero
  | succ n => exact hsucc n
theorem levelMeshRatio_eq (n : ℕ) : s.params.levelMeshRatio n = 𝒮.scale n := by
  have hL := cast_L_ne_zero s
  show (s.data.L : ℝ) ^ ((n : ℤ) - (s.data.t : ℤ)) = (𝒮.L : ℝ) ^ (n : ℤ) * 𝒮.ξ
  rw [B.nested.L_eq, B.nested.ξ_eq, sub_eq_add_neg, zpow_add₀ hL]
  rfl
theorem weightMulZero_eq {ω : s.params.CoarseZeroForms s.Ω} {w : 𝒮.Coarse}
    (h : ∀ v, ω v = w (B.centreEquiv v)) (v : ↥(s.params.allLayerPoints s.Ω)) :
    s.params.weightMulZero s.Ω ω v =
      RegionSequence.NestedRegions.weightMul w (B.centreEquiv v) := by
  show s.params.levelWeight (s.params.levelSite s.Ω v).1 *
      (s.params.levelMeshRatio (s.params.levelSite s.Ω v).1 ^ 2)⁻¹ * ω v =
    Dirichlet.blockWeights 𝒮.L (𝒮.level ((B.centreEquiv v : ↥𝒮.allCentres) : 𝒮.Point)) *
      (𝒮.scale (𝒮.level ((B.centreEquiv v : ↥𝒮.allCentres) : 𝒮.Point)) ^ 2)⁻¹ *
        w (B.centreEquiv v)
  rw [B.level_eq, B.levelWeight_eq, B.levelMeshRatio_eq, h]
omit B in
theorem projSites_of_mem {f' : 𝒮.FineSite → ℝ} (hm : f' ∈ 𝒮.siteFns) :
    RegionSequence.NestedRegions.projSites f' = f' := by apply _root_.YangMills.Construction.RegionSequence.GaugeLapPositivityProof.projSites_eq_self_of_mem <;> assumption
theorem dirichletLaplacian_eq {f : ZeroForms s.data.L s.data.m s.data.cutoff}
    {f' : 𝒮.FineSite → ℝ} (hm : f ∈ zeroFormsOn s.data.cutoff (s.Ω 0))
    (hf : ∀ x, f x = f' (B.fineEquiv x)) (x : s.data.BareSite) :
    (dirichletLaplacian s.data.cutoff s.data.t (s.Ω 0) ⟨f, hm⟩).1 x =
      RegionSequence.NestedRegions.dirichletLap f' (B.fineEquiv x) := by
  have hm' := (B.mem_iff_mem_siteFns hf).1 hm
  show siteProjection s.data.cutoff (s.Ω 0) (scalarLaplacian s.data.L s.data.m s.data.cutoff
      s.data.t (siteProjection s.data.cutoff (s.Ω 0) f)) x =
    RegionSequence.NestedRegions.projSites
      (Dirichlet.latticeLaplacian (RegionSequence.NestedRegions.projSites f')) (B.fineEquiv x)
  rw [siteProjection_of_mem hm, projSites_of_mem hm']
  show indicator (sitesOfRegion s.data.cutoff (s.Ω 0)) _ x =
    indicator {x : 𝒮.FineSite | (x : 𝒮.Point) ∈ 𝒮.Ω 0} _ (B.fineEquiv x)
  by_cases hx : (x : s.data.Point) ∈ s.Ω 0
  · rw [indicator_of_mem (show x ∈ sitesOfRegion s.data.cutoff (s.Ω 0) from hx),
      indicator_of_mem (show B.fineEquiv x ∈ {x : 𝒮.FineSite | (x : 𝒮.Point) ∈ 𝒮.Ω 0} from
        (B.mem_region_zero x).2 hx)]
    exact B.scalarLaplacian_eq hf x
  · rw [indicator_of_notMem (show x ∉ sitesOfRegion s.data.cutoff (s.Ω 0) from hx),
      indicator_of_notMem (show B.fineEquiv x ∉ {x : 𝒮.FineSite | (x : 𝒮.Point) ∈ 𝒮.Ω 0} from
        fun h => hx ((B.mem_region_zero x).1 h))]
theorem massiveZeroOperator_eq {f : ZeroForms s.data.L s.data.m s.data.cutoff}
    {f' : 𝒮.FineSite → ℝ} (hm : f ∈ zeroFormsOn s.data.cutoff (s.Ω 0))
    (hf : ∀ x, f x = f' (B.fineEquiv x)) (x : s.data.BareSite) :
    (s.params.massiveZeroOperator s.Ω ⟨f, hm⟩).1 x =
      RegionSequence.NestedRegions.gaugeLap f' (B.fineEquiv x) := by
  have h₂ : (s.params.weightedAverageZero s.Ω ⟨f, hm⟩).1 x =
      RegionSequence.NestedRegions.blockAvgAdj (RegionSequence.NestedRegions.weightMul
        (RegionSequence.NestedRegions.blockAvg f')) (B.fineEquiv x) :=
    B.averageZeroAdjoint_eq _ _
      (fun v => B.weightMulZero_eq (fun v => B.averageZero_eq hm hf v) v) x
  show (dirichletLaplacian s.data.cutoff s.data.t (s.Ω 0) ⟨f, hm⟩).1 x +
      (s.params.weightedAverageZero s.Ω ⟨f, hm⟩).1 x =
    RegionSequence.NestedRegions.dirichletLap f' (B.fineEquiv x) +
      RegionSequence.NestedRegions.blockAvgAdj (RegionSequence.NestedRegions.weightMul
        (RegionSequence.NestedRegions.blockAvg f')) (B.fineEquiv x)
  rw [B.dirichletLaplacian_eq hm hf, h₂]
theorem zeroGreen_eq {f : ZeroForms s.data.L s.data.m s.data.cutoff} {f' : 𝒮.FineSite → ℝ}
    (hm : f ∈ zeroFormsOn s.data.cutoff (s.Ω 0)) (hf : ∀ x, f x = f' (B.fineEquiv x))
    (x : s.data.BareSite) :
    (s.params.zeroGreen s.Ω ⟨f, hm⟩).1 x =
      RegionSequence.NestedRegions.gaugeGreenOp f' (B.fineEquiv x) := by
  have hright : s.params.massiveZeroOperator s.Ω * s.params.zeroGreen s.Ω = 1 :=
    Ring.mul_inverse_cancel _ B.isUnit_op
  have hleft : s.params.zeroGreen s.Ω * s.params.massiveZeroOperator s.Ω = 1 :=
    Ring.inverse_mul_cancel _ B.isUnit_op
  obtain ⟨G, hG⟩ : ∃ G, G = s.params.zeroGreen s.Ω ⟨f, hm⟩ := ⟨_, rfl⟩
  rw [← hG]
  have hMG : s.params.massiveZeroOperator s.Ω G = ⟨f, hm⟩ := by
    rw [hG]
    exact LinearMap.congr_fun hright ⟨f, hm⟩
  let g₀ : 𝒮.FineSite → ℝ := fun x' => G.1 (B.fineEquiv.symm x')
  have hg₀ : ∀ x, G.1 x = g₀ (B.fineEquiv x) := fun x => by simp [g₀]
  have hmem₀ : g₀ ∈ 𝒮.siteFns := (B.mem_iff_mem_siteFns hg₀).1 G.2
  let P : (𝒮.FineSite → ℝ) → Prop := fun g => g ∈ (𝒮.siteFns : Set (𝒮.FineSite → ℝ)) ∧
    RegionSequence.NestedRegions.gaugeLap g = f'
  have hP₀ : P g₀ := by
    refine ⟨hmem₀, ?_⟩
    funext x'
    obtain ⟨x, rfl⟩ := B.fineEquiv.surjective x'
    rw [← B.massiveZeroOperator_eq G.2 hg₀ x, ← hf]
    exact congrArg (fun F : ↥(zeroFormsOn s.data.cutoff (s.Ω 0)) => F.1 x) hMG
  have hP : P (RegionSequence.NestedRegions.gaugeGreenOp f') :=
    Classical.epsilon_spec (⟨g₀, hP₀⟩ : ∃ g, P g)
  have hh : ∀ x, (fun x => RegionSequence.NestedRegions.gaugeGreenOp f' (B.fineEquiv x)) x =
      RegionSequence.NestedRegions.gaugeGreenOp f' (B.fineEquiv x) := fun _ => rfl
  have hmh := (B.mem_iff_mem_siteFns hh).2 hP.1
  have hMH : s.params.massiveZeroOperator s.Ω ⟨_, hmh⟩ = ⟨f, hm⟩ := by
    apply Subtype.ext
    funext x
    rw [B.massiveZeroOperator_eq hmh hh x, hP.2]
    exact (hf x).symm
  have hGH : G = ⟨_, hmh⟩ := by
    rw [hG, ← hMH]
    exact LinearMap.congr_fun hleft _
  rw [hGH]
theorem siteRel_iff (x : s.data.BareSite) (x' : 𝒮.FineSite) :
    s.scalarData.SiteRel (scalarDataOfNested 𝒮) (s.toTorus 𝒮.side) x x' ↔
      B.fineEquiv x = x' := by
  constructor
  · intro h
    exact Subtype.ext ((B.fineEquiv_coe x).trans h)
  · rintro rfl
    exact (B.fineEquiv_coe x).symm
theorem coarseRel_iff (y : ↥(s.params.allLayerPoints s.Ω)) (y' : ↥𝒮.allCentres) :
    s.scalarData.CoarseRel (scalarDataOfNested 𝒮) (s.toTorus 𝒮.side) y y' ↔
      B.centreEquiv y = y' := by
  constructor
  · intro h
    exact Subtype.ext ((B.centreEquiv_coe y).trans h)
  · rintro rfl
    exact (B.centreEquiv_coe y).symm
theorem corresponds :
    s.scalarData.Corresponds (scalarDataOfNested 𝒮) (s.toTorus 𝒮.side) := by
  have sv : ∀ {f : s.data.BareSite → ℝ} {f' : 𝒮.FineSite → ℝ},
      AgreeAlong (s.scalarData.SiteRel (scalarDataOfNested 𝒮) (s.toTorus 𝒮.side)) f f' →
        ∀ x, f x = f' (B.fineEquiv x) :=
    fun h x => h x (B.fineEquiv x) ((B.siteRel_iff x _).2 rfl)
  have sv' : ∀ {f : s.data.BareSite → ℝ} {f' : 𝒮.FineSite → ℝ},
      (∀ x, f x = f' (B.fineEquiv x)) →
      AgreeAlong (s.scalarData.SiteRel (scalarDataOfNested 𝒮) (s.toTorus 𝒮.side)) f f' := by
    intro f f' h x x' hx
    rw [← (B.siteRel_iff x x').1 hx]
    exact h x
  have tv : ∀ {ω : ↥(s.params.allLayerPoints s.Ω) → ℝ} {w : ↥𝒮.allCentres → ℝ},
      AgreeAlong (s.scalarData.CoarseRel (scalarDataOfNested 𝒮) (s.toTorus 𝒮.side)) ω w →
        ∀ v, ω v = w (B.centreEquiv v) :=
    fun h v => h v (B.centreEquiv v) ((B.coarseRel_iff v _).2 rfl)
  have tv' : ∀ {ω : ↥(s.params.allLayerPoints s.Ω) → ℝ} {w : ↥𝒮.allCentres → ℝ},
      (∀ v, ω v = w (B.centreEquiv v)) →
      AgreeAlong (s.scalarData.CoarseRel (scalarDataOfNested 𝒮) (s.toTorus 𝒮.side)) ω w := by
    intro ω w h v v' hv
    rw [← (B.coarseRel_iff v v').1 hv]
    exact h v
  refine
    { sites := ⟨fun x => ⟨B.fineEquiv x, (B.siteRel_iff x _).2 rfl,
          fun y hy => ((B.siteRel_iff x y).1 hy).symm⟩,
        fun x' => ⟨B.fineEquiv.symm x', (B.siteRel_iff _ x').2 (B.fineEquiv.apply_symm_apply x'),
          fun y hy => by
            rw [← (B.siteRel_iff y x').1 hy]
            exact (B.fineEquiv.symm_apply_apply y).symm⟩⟩
      coarse := ⟨fun y => ⟨B.centreEquiv y, (B.coarseRel_iff y _).2 rfl,
          fun z hz => ((B.coarseRel_iff y z).1 hz).symm⟩,
        fun y' => ⟨B.centreEquiv.symm y',
          (B.coarseRel_iff _ y').2 (B.centreEquiv.apply_symm_apply y'),
          fun z hz => by
            rw [← (B.coarseRel_iff z y').1 hz]
            exact (B.centreEquiv.symm_apply_apply z).symm⟩⟩
      space := ⟨fun f hf => ⟨fun x' => f (B.fineEquiv.symm x'), ?_, sv' fun x => by simp⟩,
        fun f' hf' => ⟨fun x => f' (B.fineEquiv x), ?_, sv' fun _ => rfl⟩⟩
      inner := fun f _ g _ f' _ g' _ hf hg => B.latticeInner_eq (sv hf) (sv hg)
      coarseInner := fun ω _ ω' _ w _ w' _ h h' => B.coarseZeroInner_eq (tv h) (tv h')
      avg := ?_
      op := ?_
      inv := ?_ }
  · exact (B.mem_iff_mem_siteFns fun x => by simp).1 hf
  · exact (B.mem_iff_mem_siteFns fun _ => rfl).2 hf'
  · intro f hf f' _ h
    have hf₁ : f ∈ zeroFormsOn s.data.cutoff (s.Ω 0) := hf
    refine tv' fun v => ?_
    show extendByZero (zeroFormsOn s.data.cutoff (s.Ω 0))
      (fun f => s.params.averageZero s.Ω f) f v = _
    refine (congrFun (extendByZero_of_mem _ hf₁) v).trans ?_
    exact B.averageZero_eq hf₁ (sv h) v
  · intro f hf f' _ h
    have hf₁ : f ∈ zeroFormsOn s.data.cutoff (s.Ω 0) := hf
    refine sv' fun x => ?_
    show extendByZero (zeroFormsOn s.data.cutoff (s.Ω 0))
      (fun f => (s.params.massiveZeroOperator s.Ω f).1) f x = _
    refine (congrFun (extendByZero_of_mem _ hf₁) x).trans ?_
    exact B.massiveZeroOperator_eq hf₁ (sv h) x
  · intro f hf f' _ h
    have hf₁ : f ∈ zeroFormsOn s.data.cutoff (s.Ω 0) := hf
    refine sv' fun x => ?_
    show extendByZero (zeroFormsOn s.data.cutoff (s.Ω 0))
      (fun f => (s.params.zeroGreen s.Ω f).1) f x = _
    refine (congrFun (extendByZero_of_mem _ hf₁) x).trans ?_
    exact B.zeroGreen_eq hf₁ (sv h) x
end Transfer
end ScalarCorrespondence
end SeparatedClasses
end YangMills.Construction
