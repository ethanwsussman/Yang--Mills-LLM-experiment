import YangMills.Construction.Dirichlet.RegionSequenceOperators
import YangMills.Construction.Torus.FormsAveragesAndOperatorsOnAGeneralTorus
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.GeneralTorus
namespace RegionObjects
def siteCast {S σ σ' : ℝ} (h : σ = σ') (x : YangMills.Construction.Dirichlet.LatticeSite 4 S σ) :
    LatticeSite S σ' :=
  ⟨x.1, by
    obtain ⟨k, hk⟩ := x.2
    refine ⟨k, ?_⟩
    rw [hk]
    funext μ
    simp only [YangMills.Construction.Torus.torusProj, YangMills.Construction.TorusMetric.torusProj,
      h, mul_comm]⟩
section EvaluationMaps
variable (D : ScaleData)
theorem levelSpacing_zero : D.levelSpacing 0 = D.baseSpacing := by
  simp [ScaleData.levelSpacing]
theorem scaleSpacing_natCast (n : ℕ) :
    YangMills.Construction.Torus.scaleSpacing D.L D.baseSpacing (n : ℤ) = D.levelSpacing n := by
  simp [ScaleData.levelSpacing, YangMills.Construction.Torus.scaleSpacing]
def toBaseSite (x : YangMills.Construction.Dirichlet.LatticeSite 4 D.torusSide D.baseSpacing) :
    D.BaseSite :=
  siteCast (levelSpacing_zero D).symm x
def toBaseBond (b : YangMills.Construction.Dirichlet.LatticeBond 4 D.torusSide D.baseSpacing) :
    D.BaseBond :=
  ScaleData.bondFrom (toBaseSite D b.source) b.dir
def toPosBond (n : ℕ)
    (c : YangMills.Construction.Dirichlet.LatticeBond 4 D.torusSide
      (YangMills.Construction.Torus.scaleSpacing D.L D.baseSpacing (n : ℤ))) :
    D.PosBond n :=
  ScaleData.bondFrom (siteCast (scaleSpacing_natCast D n) c.source) c.dir
def toBasePlaquette
    (p : YangMills.Construction.Dirichlet.LatticeSite 4 D.torusSide D.baseSpacing ×
      {p : Fin 4 × Fin 4 // p.1 < p.2}) :
    D.BasePlaquette :=
  ⟨toBaseSite D p.1, p.2.1.1, p.2.1.2, p.2.2⟩
theorem toBaseBond_src (b : YangMills.Construction.Dirichlet.LatticeBond 4 D.torusSide D.baseSpacing) :
    ((toBaseBond D b).1.src : D.Space) = (b.source : D.Space) := by
  simp [toBaseBond, ScaleData.bondFrom, LatticeBond.plus, toBaseSite, siteCast]
theorem toBaseBond_tgt (b : YangMills.Construction.Dirichlet.LatticeBond 4 D.torusSide D.baseSpacing) :
    ((toBaseBond D b).1.tgt : D.Space) = (b.target : D.Space) := by
  simp only [toBaseBond, ScaleData.bondFrom, LatticeBond.plus, toBaseSite, siteCast,
    YangMills.Construction.Dirichlet.LatticeBond.target, unitStep,
    YangMills.Construction.Dirichlet.unitStep, AddSubgroup.coe_add, coordPoint,
    levelSpacing_zero D]
  rfl
theorem torusSide_pos : 0 < D.torusSide := by
  obtain ⟨k, hk, hS⟩ := D.torusSide_evenMultiple
  have hL : (0 : ℝ) < D.L := by
    have := D.blocking.thirteen_le
    exact_mod_cast (by omega : 0 < D.L)
  rw [hS]
  have := D.baseSpacing_pos
  have : (0 : ℝ) < k := by exact_mod_cast hk
  positivity
end EvaluationMaps
theorem bondSet_cases (W : GaugeSetting) :
    W.bondSet = W.chain.meetingBonds ∨ W.bondSet = W.chain.interiorBonds := by
  unfold GaugeSetting.bondSet
  cases W.choice with
  | meeting => exact Or.inl rfl
  | interior => exact Or.inr rfl
def SetsAreCubeUnions (W : GaugeSetting) : Prop :=
  ∀ n ≤ W.data.lastLevel, YangMills.Construction.Torus.IsCubeUnion
    (YangMills.Construction.Torus.scaleSpacing W.data.L W.data.baseSpacing (n : ℤ)) (W.chain.set n)
def toNestedRegions (W : GaugeSetting) (h : SetsAreCubeUnions W) :
    YangMills.Construction.RegionSequence.NestedRegions where
  L := W.data.L
  odd_L := W.data.blocking.odd_blockingFactor
  thirteen_le_L := W.data.blocking.thirteen_le
  ξ := W.data.baseSpacing
  ξ_pos := W.data.baseSpacing_pos
  side := W.data.torusSide
  side_pos := torusSide_pos W.data
  s := W.data.lastLevel
  side_mem_zmultiples := by
    obtain ⟨k, -, hS⟩ := W.data.torusSide_evenMultiple
    refine ⟨k, ?_⟩
    rw [hS]
    simp only [YangMills.Construction.Torus.scaleSpacing, zpow_natCast, Int.cast_natCast]
    ring
  Ω := W.chain.set
  Ω_succ_subset := W.chain.mono
  isCubeUnion_Ω := h
  Ω_eq_empty := W.chain.eq_empty_of_gt
  bonds := {b | toBaseBond W.data b ∈ W.bondSet}
  mem_bonds_of_mem := by
    intro b ht hh
    change toBaseBond W.data b ∈ W.bondSet
    have ht' : ((toBaseBond W.data b).1.src : W.data.Space) ∈ W.chain.set 0 := by
      rw [toBaseBond_src W.data]
      exact ht
    have hh' : ((toBaseBond W.data b).1.tgt : W.data.Space) ∈ W.chain.set 0 := by
      rw [toBaseBond_tgt W.data]
      exact hh
    rcases bondSet_cases W with hb | hb <;> rw [hb]
    · exact Or.inl ht'
    · exact ⟨ht', hh'⟩
  mem_of_mem_bonds := by
    intro b hb
    change toBaseBond W.data b ∈ W.bondSet at hb
    have hstar : ((toBaseBond W.data b).1.src : W.data.Space) ∈ W.chain.set 0 ∨
        ((toBaseBond W.data b).1.tgt : W.data.Space) ∈ W.chain.set 0 := by
      rcases bondSet_cases W with h' | h' <;> rw [h'] at hb
      · exact hb
      · exact Or.inl hb.1
    rw [toBaseBond_src W.data, toBaseBond_tgt W.data] at hstar
    exact hstar
variable (W : GaugeSetting)
def siteComap (f : W.data.SiteField) :
    YangMills.Construction.Dirichlet.LatticeSite 4 W.data.torusSide W.data.baseSpacing → ℝ :=
  f ∘ toBaseSite W.data
def bondComap (A : W.data.BondField) :
    YangMills.Construction.Dirichlet.LatticeBond 4 W.data.torusSide W.data.baseSpacing → ℝ :=
  A ∘ toBaseBond W.data
def plaquetteComap (F : W.data.PlaquetteField) :
    YangMills.Construction.Dirichlet.LatticeSite 4 W.data.torusSide W.data.baseSpacing ×
      {p : Fin 4 × Fin 4 // p.1 < p.2} → ℝ :=
  F ∘ toBasePlaquette W.data
open YangMills.Construction.RegionSequence.NestedRegions in
structure Agrees (h : SetsAreCubeUnions W) : Prop where
  layers : ∀ n, (toNestedRegions W h).shellOf n = W.chain.shell n
  layer_sites : ∀ n, (toNestedRegions W h).centresAt n = W.chain.shellSites n
  sites : (toNestedRegions W h).allCentres = W.chain.shellSitesUnion
  spacing_of : ∀ y, (toNestedRegions W h).levelScale y = W.chain.localSpacing y
  cell : ∀ y, (toNestedRegions W h).cellOf y = W.chain.localCube y
  base_sites : Function.Bijective (toBaseSite W.data)
  base_bonds : Function.Bijective (toBaseBond W.data)
  site_space : ∀ f, siteComap W f ∈ (toNestedRegions W h).siteFns ↔ f ∈ W.chain.dirichletSites
  form_space : ∀ A, bondComap W A ∈ (toNestedRegions W h).oneForms ↔ A ∈ W.formSubspace
  site_inner : ∀ f g, YangMills.Construction.Dirichlet.innerSum (siteComap W f) (siteComap W g) =
    W.data.siteInner f g
  bond_inner : ∀ A A', bondInner (𝒮 := toNestedRegions W h) (bondComap W A) (bondComap W A') =
    W.data.bondInner A A'
  site_proj : ∀ f, projSites (𝒮 := toNestedRegions W h) (siteComap W f) =
    siteComap W (W.chain.siteProj f : W.data.SiteField)
  form_proj : ∀ A, projBonds (𝒮 := toNestedRegions W h) (bondComap W A) =
    bondComap W (W.formProj A : W.data.BondField)
  anchor : ∀ b : (toNestedRegions W h).FineBond, toBaseBond W.data b ∈ W.bondSet →
    ((toNestedRegions W h).anchor b).1 = (W.chain.anchor (toBaseBond W.data b)).1
  bond_in : ∀ (y : W.data.Space) (b : (toNestedRegions W h).FineBond), toBaseBond W.data b ∈ W.bondSet →
    (AnchoredIn ((toNestedRegions W h).cellOf y) b ↔ W.chain.LiesInCell (toBaseBond W.data b) y)
  supported_in : ∀ (y : W.data.Space), ∀ A ∈ W.formSubspace,
    (AnchorSupported ((toNestedRegions W h).cellOf y) (bondComap W A) ↔ W.SupportedInCell A y)
  site_diff : ∀ (ν : Fin 4) (f : W.data.SiteField) (x : (toNestedRegions W h).FineSite),
    YangMills.Construction.Dirichlet.forwardDiff ν (siteComap W f) x =
      W.data.forwardDiff ν f (toBaseSite W.data x)
  form_diff : ∀ (ν : Fin 4) (A : W.data.BondField) (b : (toNestedRegions W h).FineBond),
    fwdDiff (𝒮 := toNestedRegions W h) ν (bondComap W A) b =
      W.data.forwardDiff ν (W.data.formComponent b.dir A) (toBaseSite W.data b.source)
  grad : ∀ f, dTorus (𝒮 := toNestedRegions W h) (siteComap W f) =
    bondComap W (W.data.grad f)
  curl : ∀ A, curlTorus (𝒮 := toNestedRegions W h) (bondComap W A) =
    plaquetteComap W (W.data.plaquetteCurl A)
  grad_adjoint : ∀ A, dTorusAdj (𝒮 := toNestedRegions W h) (bondComap W A) =
    siteComap W (W.data.gradAdjoint A)
  curl_adjoint : ∀ F, curlTorusAdj (𝒮 := toNestedRegions W h) (plaquetteComap W F) =
    bondComap W (W.data.plaquetteCurlAdjoint F)
  dirichlet_lap : ∀ f : ↥W.chain.dirichletSites,
    dirichletLap (𝒮 := toNestedRegions W h) (siteComap W f) =
      siteComap W (W.chain.dirichletLap f : W.data.SiteField)
  site_mean : ∀ (f : ↥W.chain.dirichletSites) (y : W.data.Space)
    (hy : y ∈ (toNestedRegions W h).allCentres) (hy' : y ∈ W.chain.shellSitesUnion),
    blockAvg (𝒮 := toNestedRegions W h) (siteComap W f) ⟨y, hy⟩ = W.chain.siteMeans f ⟨y, hy'⟩
  mean_kernel : ∀ f : ↥W.chain.dirichletSites,
    siteComap W f ∈ (toNestedRegions W h).avgKernel ↔ f ∈ W.chain.siteMeansKer
  range_proj : ∀ f : ↥W.chain.dirichletSites,
    rangeProj (𝒮 := toNestedRegions W h) (siteComap W f) =
      siteComap W (W.chain.lapImageProj f : W.data.SiteField)
  level_bonds : ∀ n ≤ W.data.lastLevel, Function.Bijective (toPosBond W.data n)
  coarse_bonds : ∀ n ≤ W.data.lastLevel, ∀ c : (toNestedRegions W h).BondAt n,
    c ∈ (toNestedRegions W h).coarseBonds n ↔ toPosBond W.data n c ∈ W.coarseBondsAt n
  means : ∀ n ≤ W.data.lastLevel, ∀ (A : W.data.BondField) (c : (toNestedRegions W h).BondAt n),
    bondAvg (𝒮 := toNestedRegions W h) n (bondComap W A) c =
      W.data.blockBondMean n A (toPosBond W.data n c)
  mass_part : ∀ A : ↥W.formSubspace, avgOp (𝒮 := toNestedRegions W h) (bondComap W A) =
    bondComap W (W.massPart A : W.data.BondField)
  lap : ∀ A : ↥W.formSubspace, baseOp (𝒮 := toNestedRegions W h) (bondComap W A) =
    bondComap W (W.gaugeLap A : W.data.BondField)
  invertible : (toNestedRegions W h).BaseOpInvertible ↔ IsUnit W.gaugeLap
  green : IsUnit W.gaugeLap → ∀ A : ↥W.formSubspace,
    baseGreen (𝒮 := toNestedRegions W h) (bondComap W A) =
      bondComap W (W.greenOp A : W.data.BondField)
end RegionObjects
def RegionObjects.ObjectsAgree : Prop :=
  ∀ W : GaugeSetting, W.mass = 1 → W.data.L ≤ W.data.blockCount →
    (∃ u : ℕ, W.data.baseSpacing = YangMills.Construction.Torus.unitSpacing W.data.L u) →
    ∃ h : RegionObjects.SetsAreCubeUnions W, RegionObjects.Agrees W h
end YangMills.Construction.GeneralTorus
