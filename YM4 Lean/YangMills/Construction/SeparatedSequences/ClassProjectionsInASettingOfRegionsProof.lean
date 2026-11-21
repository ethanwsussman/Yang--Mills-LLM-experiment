import YangMills.Construction.SeparatedSequences.ClassProjectionsInASettingOfRegions
import YangMills.Construction.SeparatedSequences.ClassProjectionsInWeightedDataProof
import YangMills.Construction.SeparatedSequences.ClassSiteFunctionsInASettingOfRegions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric PeriodicLattice PeriodicLattice.DirichletOperators
namespace SeparatedClasses.NestedProjectionsOfClass
open SingleSequence SingleSequence.SequenceData
section Paired
variable {X X' : Type} {R : X → X' → Prop}
theorem exists_agreeAlong_right (hR : PairsUniquely R) (f : X → ℝ) : ∃ f', AgreeAlong R f f' := by
  have hpick := fun x' => (hR.2 x').exists
  choose g hg using hpick
  exact ⟨fun x' => f (g x'), fun x x' hx => by rw [(hR.2 x').unique hx (hg x')]⟩
theorem exists_agreeAlong_left (hR : PairsUniquely R) (f' : X' → ℝ) : ∃ f, AgreeAlong R f f' := by
  have hpick := fun x => (hR.1 x).exists
  choose g hg using hpick
  exact ⟨fun x => f' (g x), fun x x' hx => by rw [(hR.1 x).unique hx (hg x)]⟩
theorem agreeAlong_right_unique (hR : PairsUniquely R) {f : X → ℝ} {f' g' : X' → ℝ}
    (hf : AgreeAlong R f f') (hg : AgreeAlong R f g') : f' = g' := by
  funext x'
  obtain ⟨x, hx⟩ := (hR.2 x').exists
  rw [← hf x x' hx, hg x x' hx]
theorem agreeAlong_left_unique (hR : PairsUniquely R) {f g : X → ℝ} {f' : X' → ℝ}
    (hf : AgreeAlong R f f') (hg : AgreeAlong R g f') : f = g := by
  funext x
  obtain ⟨x', hx⟩ := (hR.1 x).exists
  rw [hf x x' hx, hg x x' hx]
theorem agreeAlong_zero : AgreeAlong R (0 : X → ℝ) (0 : X' → ℝ) := fun _ _ _ => rfl
end Paired
theorem extendByZero_coe {X Y : Type} (E : Submodule ℝ (X → ℝ)) (T : ↥E → Y → ℝ) (f : ↥E) :
    extendByZero E T f.1 = T f := by apply _root_.YangMills.Construction.SeparatedClasses.WeightedProjectionsOfClass.extendByZero_coe <;> assumption
section Inner
variable (P : SeparatedSequences.BaseParameters) (Ω : ℕ → Set P.Torus)
theorem eq_zero_of_inner_self (f : ↥(zeroFormsOn P.K (Ω 0)))
    (hf : P.restrictedZeroInner Ω f f = 0) : f = 0 := by
  have hfin : Finite (BareSite P.L P.m P.K) := P.instFiniteLatticeSite 0
  have hL : (0 : ℝ) < (P.L : ℝ) := by
    have := P.three_le_L
    exact_mod_cast (by omega : 0 < P.L)
  have hmesh : finestMeshInLevelUnits P.L P.t ≠ 0 := by
    rw [← P.levelMeshRatio_zero]
    simp only [SeparatedSequences.BaseParameters.levelMeshRatio, SeparatedSequences.ScaleData.levelMesh]
    exact (zpow_pos hL _).ne'
  have hsum : ∑ᶠ i, f.1 i * f.1 i = 0 := by
    have hself := hf
    simp only [SeparatedSequences.BaseParameters.restrictedZeroInner, latticeInner] at hself
    exact (mul_eq_zero.mp hself).resolve_left (pow_ne_zero _ hmesh)
  classical
  have := Fintype.ofFinite (BareSite P.L P.m P.K)
  rw [finsum_eq_sum_of_fintype] at hsum
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_self_nonneg (f.1 i)).mp hsum
  apply Subtype.ext
  funext i
  exact mul_self_eq_zero.mp (hz i (Finset.mem_univ i))
theorem inner_sub_left (f g u : ↥(zeroFormsOn P.K (Ω 0))) :
    P.restrictedZeroInner Ω (f - g) u =
      P.restrictedZeroInner Ω f u - P.restrictedZeroInner Ω g u := by
  have hfin : Finite (BareSite P.L P.m P.K) := P.instFiniteLatticeSite 0
  classical
  have := Fintype.ofFinite (BareSite P.L P.m P.K)
  simp only [SeparatedSequences.BaseParameters.restrictedZeroInner, latticeInner]
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, ← mul_sub,
    ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Submodule.coe_sub, Pi.sub_apply]
  ring
theorem eq_of_inner_eq (f g : ↥(zeroFormsOn P.K (Ω 0)))
    (hfg : ∀ u, P.restrictedZeroInner Ω f u = P.restrictedZeroInner Ω g u) : f = g := by
  have := eq_zero_of_inner_self P Ω (f - g)
    (by rw [inner_sub_left, hfg, sub_self])
  exact sub_eq_zero.mp this
end Inner
variable {s : SequenceData} {𝒩 : RegionSequence.NestedRegions}
abbrev FineRel (s : SequenceData) (𝒩 : RegionSequence.NestedRegions) :
    s.data.BareSite → 𝒩.FineSite → Prop :=
  s.scalarData.SiteRel (scalarDataOfNested 𝒩) (s.toTorus 𝒩.side)
abbrev ApexRel (s : SequenceData) (𝒩 : RegionSequence.NestedRegions) :
    ↥(s.params.allLayerPoints s.Ω) → ↥𝒩.allCentres → Prop :=
  s.scalarData.CoarseRel (scalarDataOfNested 𝒩) (s.toTorus 𝒩.side)
abbrev zeroSpace (s : SequenceData) : Submodule ℝ s.data.SiteFn := zeroFormsOn s.data.cutoff (s.Ω 0)
section Carried
variable (h : s.scalarData.Corresponds (scalarDataOfNested 𝒩) (s.toTorus 𝒩.side))
include h
theorem mem_siteFns_of_agree {f : ↥(zeroSpace s)} {f' : 𝒩.FineSite → ℝ}
    (hf : AgreeAlong (FineRel s 𝒩) f.1 f') : f' ∈ 𝒩.siteFns := by
  obtain ⟨g, hg, hfg⟩ := h.space.1 f.1 f.2
  have e := agreeAlong_right_unique h.sites hf hfg
  rw [e]
  exact hg
theorem exists_fine_agree (f : ↥(zeroSpace s)) :
    ∃ f' : 𝒩.FineSite → ℝ, AgreeAlong (FineRel s 𝒩) f.1 f' := by
  obtain ⟨g, _, hfg⟩ := h.space.1 f.1 f.2
  exact ⟨g, hfg⟩
theorem exists_zeroSpace_agree {f' : 𝒩.FineSite → ℝ} (hf : f' ∈ 𝒩.siteFns) :
    ∃ f : ↥(zeroSpace s), AgreeAlong (FineRel s 𝒩) f.1 f' := by
  obtain ⟨g, hg, hfg⟩ := h.space.2 f' hf
  exact ⟨⟨g, hg⟩, hfg⟩
theorem inner_eq_innerSum {f g : ↥(zeroSpace s)} {f' g' : 𝒩.FineSite → ℝ}
    (hf : AgreeAlong (FineRel s 𝒩) f.1 f') (hg : AgreeAlong (FineRel s 𝒩) g.1 g') :
    s.params.restrictedZeroInner s.Ω f g = Dirichlet.innerSum f' g' :=
  h.inner f.1 f.2 g.1 g.2 f' (mem_siteFns_of_agree h hf) g' (mem_siteFns_of_agree h hg) hf hg
theorem coarseInner_eq {ω ν : ↥(s.params.allLayerPoints s.Ω) → ℝ} {ω' ν' : 𝒩.Coarse}
    (hω : AgreeAlong (ApexRel s 𝒩) ω ω') (hν : AgreeAlong (ApexRel s 𝒩) ν ν') :
    s.params.coarseZeroInner s.Ω ω ν = RegionSequence.NestedRegions.coarseInner ω' ν' :=
  h.coarseInner ω trivial ν trivial ω' trivial ν' trivial hω hν
theorem averageZero_agree {f : ↥(zeroSpace s)} {f' : 𝒩.FineSite → ℝ}
    (hf : AgreeAlong (FineRel s 𝒩) f.1 f') :
    AgreeAlong (ApexRel s 𝒩) (s.params.averageZero s.Ω f)
      (RegionSequence.NestedRegions.blockAvg f') := by
  have e := h.avg f.1 f.2 f' (mem_siteFns_of_agree h hf) hf
  have e' : s.scalarData.avg f.1 = s.params.averageZero s.Ω f :=
    extendByZero_coe _ _ f
  rw [e'] at e
  exact e
theorem massiveZeroOperator_agree {f : ↥(zeroSpace s)} {f' : 𝒩.FineSite → ℝ}
    (hf : AgreeAlong (FineRel s 𝒩) f.1 f') :
    AgreeAlong (FineRel s 𝒩) (s.params.massiveZeroOperator s.Ω f).1
      (RegionSequence.NestedRegions.gaugeLap f') := by
  have e := h.op f.1 f.2 f' (mem_siteFns_of_agree h hf) hf
  have e' : s.scalarData.op f.1 = (s.params.massiveZeroOperator s.Ω f).1 :=
    extendByZero_coe (zeroSpace s) (fun f => (s.params.massiveZeroOperator s.Ω f).1) f
  rw [e'] at e
  exact e
theorem zeroGreen_agree {f : ↥(zeroSpace s)} {f' : 𝒩.FineSite → ℝ}
    (hf : AgreeAlong (FineRel s 𝒩) f.1 f') :
    AgreeAlong (FineRel s 𝒩) (s.params.zeroGreen s.Ω f).1
      (RegionSequence.NestedRegions.gaugeGreenOp f') := by
  have e := h.inv f.1 f.2 f' (mem_siteFns_of_agree h hf) hf
  have e' : s.scalarData.inv f.1 = (s.params.zeroGreen s.Ω f).1 :=
    extendByZero_coe (zeroSpace s) (fun f => (s.params.zeroGreen s.Ω f).1) f
  rw [e'] at e
  exact e
theorem averageZeroAdjoint_agree
    (hadj : FiniteDimReal.IsAdjointFor (s.params.restrictedZeroInner s.Ω)
      (s.params.coarseZeroInner s.Ω) (s.params.averageZero s.Ω)
      (s.params.averageZeroAdjoint s.Ω))
    {ω : ↥(s.params.allLayerPoints s.Ω) → ℝ} {ω' : 𝒩.Coarse}
    (hω : AgreeAlong (ApexRel s 𝒩) ω ω') :
    AgreeAlong (FineRel s 𝒩) (s.params.averageZeroAdjoint s.Ω ω).1
      (RegionSequence.NestedRegions.blockAvgAdj ω') := by
  set v := s.params.averageZeroAdjoint s.Ω ω with hv
  obtain ⟨v', hv'⟩ := exists_fine_agree h v
  have hex : ∃ w : 𝒩.FineSite → ℝ, w ∈ (𝒩.siteFns : Set (𝒩.FineSite → ℝ)) ∧
      ∀ u ∈ (𝒩.siteFns : Set (𝒩.FineSite → ℝ)), Dirichlet.innerSum w u =
        RegionSequence.NestedRegions.coarseInner ω' (RegionSequence.NestedRegions.blockAvg u) := by
    refine ⟨v', mem_siteFns_of_agree h hv', fun u hu => ?_⟩
    obtain ⟨uL, huL⟩ := exists_zeroSpace_agree h hu
    rw [← inner_eq_innerSum h hv' huL, ← coarseInner_eq h hω (averageZero_agree h huL), hv]
    exact (hadj uL ω).symm
  obtain ⟨hmem, hspec⟩ := Classical.epsilon_spec hex
  change RegionSequence.NestedRegions.blockAvgAdj ω' ∈ (𝒩.siteFns : Set (𝒩.FineSite → ℝ)) at hmem
  change ∀ u ∈ (𝒩.siteFns : Set (𝒩.FineSite → ℝ)),
    Dirichlet.innerSum (RegionSequence.NestedRegions.blockAvgAdj ω') u =
      RegionSequence.NestedRegions.coarseInner ω' (RegionSequence.NestedRegions.blockAvg u) at hspec
  obtain ⟨vL, hvL⟩ := exists_zeroSpace_agree h hmem
  have e : vL = v := by
    refine eq_of_inner_eq s.params s.Ω vL v fun u => ?_
    obtain ⟨u', hu'⟩ := exists_fine_agree h u
    rw [inner_eq_innerSum h hvL hu', hspec u' (mem_siteFns_of_agree h hu'), hv, ← hadj u ω,
      coarseInner_eq h hω (averageZero_agree h hu')]
  rw [← e]
  exact hvL
theorem blockAvgAdj_zero
    (hadj : FiniteDimReal.IsAdjointFor (s.params.restrictedZeroInner s.Ω)
      (s.params.coarseZeroInner s.Ω) (s.params.averageZero s.Ω)
      (s.params.averageZeroAdjoint s.Ω)) :
    RegionSequence.NestedRegions.blockAvgAdj (0 : 𝒩.Coarse) = 0 := by
  have e := averageZeroAdjoint_agree h hadj (ω := 0) (ω' := 0) agreeAlong_zero
  have e0 : (s.params.averageZeroAdjoint s.Ω (0 : ↥(s.params.allLayerPoints s.Ω) → ℝ)).1 = 0 := by
    rw [show (0 : ↥(s.params.allLayerPoints s.Ω) → ℝ) = (0 : s.params.CoarseZeroForms s.Ω) from rfl,
      map_zero]
    rfl
  rw [e0] at e
  exact agreeAlong_right_unique h.sites e agreeAlong_zero
theorem greenSquare_agree
    (hadj : FiniteDimReal.IsAdjointFor (s.params.restrictedZeroInner s.Ω)
      (s.params.coarseZeroInner s.Ω) (s.params.averageZero s.Ω)
      (s.params.averageZeroAdjoint s.Ω))
    {ω : ↥(s.params.allLayerPoints s.Ω) → ℝ} {ω' : 𝒩.Coarse}
    (hω : AgreeAlong (ApexRel s 𝒩) ω ω') :
    AgreeAlong (ApexRel s 𝒩) (s.greenSquare ω) (greenSquareOfNested 𝒩 ω') := by
  have h1 := averageZeroAdjoint_agree h hadj hω
  have h2 := zeroGreen_agree h h1
  have h3 := zeroGreen_agree h h2
  have h4 := averageZero_agree h h3
  have e : s.greenSquare ω = s.params.averageZero s.Ω (s.params.zeroGreen s.Ω
      (s.params.zeroGreen s.Ω (s.params.averageZeroAdjoint s.Ω ω))) := by
    simp only [greenSquare, SeparatedSequences.BaseParameters.averagedZeroGreenSq,
      LinearMap.comp_apply, pow_two, Module.End.mul_apply]
  rw [e]
  exact h4
theorem greenSquareInv_agree
    (hadj : FiniteDimReal.IsAdjointFor (s.params.restrictedZeroInner s.Ω)
      (s.params.coarseZeroInner s.Ω) (s.params.averageZero s.Ω)
      (s.params.averageZeroAdjoint s.Ω))
    (hunit : IsUnit (s.params.averagedZeroGreenSq s.Ω))
    {ω : ↥(s.params.allLayerPoints s.Ω) → ℝ} {ω' : 𝒩.Coarse}
    (hω : AgreeAlong (ApexRel s 𝒩) ω ω') :
    AgreeAlong (ApexRel s 𝒩) (s.greenSquareInv ω)
      (RegionSequence.inverseValue univ (greenSquareOfNested 𝒩) ω') := by
  set T := s.params.averagedZeroGreenSq s.Ω with hT
  have hright : ∀ ν : ↥(s.params.allLayerPoints s.Ω) → ℝ, T (Ring.inverse T ν) = ν := fun ν => by
    have := Ring.mul_inverse_cancel T hunit
    exact congrArg (fun X : Module.End ℝ _ => X ν) this
  have hleft : ∀ ν : ↥(s.params.allLayerPoints s.Ω) → ℝ, Ring.inverse T (T ν) = ν := fun ν => by
    have := Ring.inverse_mul_cancel T hunit
    exact congrArg (fun X : Module.End ℝ _ => X ν) this
  have hsq : ∀ ν, s.greenSquare ν = T ν := fun _ => rfl
  have hex : ∃ g : 𝒩.Coarse, g ∈ (univ : Set 𝒩.Coarse) ∧ greenSquareOfNested 𝒩 g = ω' := by
    obtain ⟨g', hg'⟩ := exists_agreeAlong_right h.coarse (Ring.inverse T ω)
    refine ⟨g', trivial, ?_⟩
    have e := greenSquare_agree h hadj hg'
    rw [hsq, hright] at e
    exact agreeAlong_right_unique h.coarse e hω
  obtain ⟨-, hspec⟩ := Classical.epsilon_spec hex
  change greenSquareOfNested 𝒩 (RegionSequence.inverseValue univ (greenSquareOfNested 𝒩) ω') = ω' at hspec
  have key : ∀ G : 𝒩.Coarse, greenSquareOfNested 𝒩 G = ω' →
      AgreeAlong (ApexRel s 𝒩) (s.greenSquareInv ω) G := by
    intro G hG
    obtain ⟨gL, hgL⟩ : ∃ gL : ↥(s.params.allLayerPoints s.Ω) → ℝ,
        AgreeAlong (ApexRel s 𝒩) gL G := exists_agreeAlong_left h.coarse G
    have e := greenSquare_agree h hadj hgL
    rw [hG, hsq] at e
    have e2 : T gL = ω := agreeAlong_left_unique h.coarse e hω
    have e3 : s.greenSquareInv ω = gL := by
      change Ring.inverse T ω = gL
      rw [← e2, hleft]
    rw [e3]
    exact hgL
  exact key _ hspec
theorem mem_averageZeroKernel_iff {f : ↥(zeroSpace s)} {f' : 𝒩.FineSite → ℝ}
    (hf : AgreeAlong (FineRel s 𝒩) f.1 f') :
    f ∈ s.params.averageZeroKernel s.Ω ↔ f' ∈ 𝒩.avgKernel := by
  have e := averageZero_agree h hf
  constructor
  · intro hk
    have hk' : s.params.averageZero s.Ω f = 0 := hk
    rw [hk'] at e
    exact ⟨mem_siteFns_of_agree h hf, agreeAlong_right_unique h.coarse e agreeAlong_zero⟩
  · rintro ⟨-, hk⟩
    rw [hk] at e
    exact agreeAlong_left_unique h.coarse e agreeAlong_zero
theorem dirichletLaplacian_agree
    (hadj : FiniteDimReal.IsAdjointFor (s.params.restrictedZeroInner s.Ω)
      (s.params.coarseZeroInner s.Ω) (s.params.averageZero s.Ω)
      (s.params.averageZeroAdjoint s.Ω))
    {k : ↥(zeroSpace s)} {k' : 𝒩.FineSite → ℝ} (hk : k ∈ s.params.averageZeroKernel s.Ω)
    (hkk : AgreeAlong (FineRel s 𝒩) k.1 k') :
    AgreeAlong (FineRel s 𝒩) (dirichletLaplacian s.data.cutoff s.data.t (s.Ω 0) k).1
      (RegionSequence.NestedRegions.dirichletLap k') := by
  have e := massiveZeroOperator_agree h hkk
  have hk0 : s.params.averageZero s.Ω k = 0 := hk
  have eL : s.params.massiveZeroOperator s.Ω k = dirichletLaplacian s.data.cutoff s.data.t (s.Ω 0) k := by
    simp only [SeparatedSequences.BaseParameters.massiveZeroOperator,
      SeparatedSequences.BaseParameters.weightedAverageZero, LinearMap.add_apply, LinearMap.comp_apply,
      hk0, map_zero, add_zero]
  have hk' : RegionSequence.NestedRegions.blockAvg k' = 0 := ((mem_averageZeroKernel_iff h hkk).mp hk).2
  have eR : RegionSequence.NestedRegions.gaugeLap k' =
      RegionSequence.NestedRegions.dirichletLap k' := by
    have hw : RegionSequence.NestedRegions.weightMul (0 : 𝒩.Coarse) = 0 := by
      funext y
      simp [RegionSequence.NestedRegions.weightMul]
    simp only [RegionSequence.NestedRegions.gaugeLap, hk', hw, blockAvgAdj_zero h hadj, add_zero]
  rw [eL, eR] at e
  exact e
theorem gaugeRangeProjection_agree
    (hadj : FiniteDimReal.IsAdjointFor (s.params.restrictedZeroInner s.Ω)
      (s.params.coarseZeroInner s.Ω) (s.params.averageZero s.Ω)
      (s.params.averageZeroAdjoint s.Ω))
    (hproj : RealInnerForms.IsOrthogonalProjectionFor (s.params.restrictedZeroInner s.Ω)
      (s.params.laplacianImageOfAverageZeroKernel s.Ω) (s.params.gaugeRangeProjection s.Ω))
    {f : ↥(zeroSpace s)} {f' : 𝒩.FineSite → ℝ} (hf : AgreeAlong (FineRel s 𝒩) f.1 f') :
    AgreeAlong (FineRel s 𝒩) (s.params.gaugeRangeProjection s.Ω f).1
      (RegionSequence.NestedRegions.rangeProj f') := by
  set r := s.params.gaugeRangeProjection s.Ω f with hr
  have hsub : ∀ {g g' : ↥(zeroSpace s)} {a' b' : 𝒩.FineSite → ℝ},
      AgreeAlong (FineRel s 𝒩) g.1 a' → AgreeAlong (FineRel s 𝒩) g'.1 b' →
      AgreeAlong (FineRel s 𝒩) (g - g').1 (a' - b') := by
    intro g g' a' b' ha hb x x' hx
    simp only [Submodule.coe_sub, Pi.sub_apply]
    rw [show (g : s.data.SiteFn) x = a' x' from ha x x' hx,
      show (g' : s.data.SiteFn) x = b' x' from hb x x' hx]
  have hup : ∀ w ∈ s.params.laplacianImageOfAverageZeroKernel s.Ω, ∃ w' : 𝒩.FineSite → ℝ,
      w' ∈ RegionSequence.NestedRegions.dirichletLap '' 𝒩.avgKernel ∧
        AgreeAlong (FineRel s 𝒩) w.1 w' := by
    rintro w ⟨k, hk, rfl⟩
    obtain ⟨k', hk'⟩ := exists_fine_agree h k
    exact ⟨_, ⟨k', (mem_averageZeroKernel_iff h hk').mp hk, rfl⟩, dirichletLaplacian_agree h hadj hk hk'⟩
  have hdown : ∀ w' ∈ RegionSequence.NestedRegions.dirichletLap '' 𝒩.avgKernel,
      ∃ w ∈ s.params.laplacianImageOfAverageZeroKernel s.Ω, AgreeAlong (FineRel s 𝒩) w.1 w' := by
    rintro w' ⟨k', hk', rfl⟩
    obtain ⟨k, hk⟩ := exists_zeroSpace_agree h hk'.1
    have hkm := (mem_averageZeroKernel_iff h hk).mpr hk'
    exact ⟨_, ⟨k, hkm, rfl⟩, dirichletLaplacian_agree h hadj hkm hk⟩
  have hex : ∃ q : 𝒩.FineSite → ℝ,
      q ∈ RegionSequence.NestedRegions.dirichletLap '' 𝒩.avgKernel ∧
      ∀ w ∈ RegionSequence.NestedRegions.dirichletLap '' 𝒩.avgKernel,
        Dirichlet.innerSum (f' - q) w = 0 := by
    obtain ⟨r', hr'm, hr'⟩ := hup r (hproj f).1
    refine ⟨r', hr'm, fun w' hw' => ?_⟩
    obtain ⟨w, hw, hww⟩ := hdown w' hw'
    rw [← inner_eq_innerSum h (hsub hf hr') hww]
    exact (hproj f).2 w hw
  obtain ⟨hmem, hspec⟩ := Classical.epsilon_spec hex
  change RegionSequence.NestedRegions.rangeProj f' ∈
    RegionSequence.NestedRegions.dirichletLap '' 𝒩.avgKernel at hmem
  change ∀ w ∈ RegionSequence.NestedRegions.dirichletLap '' 𝒩.avgKernel,
    Dirichlet.innerSum (f' - RegionSequence.NestedRegions.rangeProj f') w = 0 at hspec
  obtain ⟨r₂, hr₂m, hr₂⟩ := hdown _ hmem
  have hperp : ∀ w ∈ s.params.laplacianImageOfAverageZeroKernel s.Ω,
      s.params.restrictedZeroInner s.Ω (f - r₂) w = 0 := by
    intro w hw
    obtain ⟨w', hw'm, hww⟩ := hup w hw
    rw [inner_eq_innerSum h (hsub hf hr₂) hww]
    exact hspec w' hw'm
  have e : r₂ = r := by
    have hc : r₂ - r ∈ s.params.laplacianImageOfAverageZeroKernel s.Ω :=
      Submodule.sub_mem _ hr₂m (hproj f).1
    have h0 : s.params.restrictedZeroInner s.Ω (r₂ - r) (r₂ - r) = 0 := by
      have e1 : r₂ - r = (f - r) - (f - r₂) := by abel
      have e2 := (hproj f).2 _ hc
      have e3 := hperp _ hc
      have e4 : s.params.restrictedZeroInner s.Ω (r₂ - r) (r₂ - r) =
          s.params.restrictedZeroInner s.Ω ((f - r) - (f - r₂)) (r₂ - r) := by rw [← e1]
      rw [e4, inner_sub_left, e2, e3, sub_zero]
    exact sub_eq_zero.mp (eq_zero_of_inner_self s.params s.Ω _ h0)
  rw [← e]
  exact hr₂
end Carried
theorem statement_holds (hScalar : ScalarDataOfNestedCorresponds)
    (hExist : SeparatedSequences.OperatorExistenceStatement) : Statement := by
  intro s 𝒩 hset
  have h := hScalar s 𝒩 hset
  let D : SeparatedSequences.SequenceDatum := ⟨s.params, s.Ω, s.Ω_mem.2.1, s.Ω_mem.1⟩
  have hdef : s.params.OperatorsWellDefined s.Ω s.frame := (hExist.1 D s.frame).2.2.2.2
  have hadj := hdef.zero_adjoint
  have hproj := hdef.gauge_projection
  have hunit := hdef.averaged_zero_green_sq_invertible
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ω _ ω' _ hω
    exact greenSquare_agree h hadj hω
  · intro ω _ ω' _ hω
    exact greenSquareInv_agree h hadj hunit hω
  · intro f hf f' _ hff
    have e : s.rangeProj f = (s.params.gaugeRangeProjection s.Ω ⟨f, hf⟩).1 :=
      extendByZero_coe (zeroSpace s) (fun f => (s.params.gaugeRangeProjection s.Ω f).1) ⟨f, hf⟩
    rw [e]
    exact gaugeRangeProjection_agree h hadj hproj (f := ⟨f, hf⟩) hff
  · intro f hf f' _ hff
    have e : s.complProj f = (s.params.gaugeComplementProjection s.Ω ⟨f, hf⟩).1 :=
      extendByZero_coe (zeroSpace s) (fun f => (s.params.gaugeComplementProjection s.Ω f).1) ⟨f, hf⟩
    rw [e]
    have hg := gaugeRangeProjection_agree h hadj hproj (f := ⟨f, hf⟩) hff
    intro x x' hx
    have h1 := hff x x' hx
    have h2 := hg x x' hx
    change f x - (s.params.gaugeRangeProjection s.Ω ⟨f, hf⟩).1 x =
      f' x' - RegionSequence.NestedRegions.rangeProj f' x'
    rw [h1, h2]
end SeparatedClasses.NestedProjectionsOfClass
end YangMills.Construction
