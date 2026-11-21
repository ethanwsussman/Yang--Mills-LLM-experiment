import YangMills.Construction.SeparatedSequences.ClassExpansionsAndAveragesInASettingOfRegionsProof
import YangMills.Construction.Lattice.ExistenceOfTheOperatorsOfASeparatedSequence
import YangMills.Construction.SeparatedSequences.BasePointIsThatOfTheOperatorsAndTheFoot
import YangMills.Construction.SeparatedSequences.ClassExpansionsInASettingOfRegions
import YangMills.Construction.SeparatedSequences.ClassProjectionsInASettingOfRegions
import YangMills.Construction.SeparatedSequences.ClassSiteFunctionsInASettingOfRegions
import YangMills.Construction.SeparatedSequences.ClassWeightInASettingOfRegions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric PeriodicLattice PeriodicLattice.DirichletOperators
namespace SeparatedClasses.NestedOneForms
open SingleSequence SingleSequence.SequenceData
section PairingOff
variable {X X' : Type} {R : X → X' → Prop}
def equivOfPairs (h : PairsUniquely R) : X ≃ X' :=
  Equiv.ofBijective (fun x => (h.1 x).choose)
    ⟨fun x y hxy => by
        have hx := (h.1 x).choose_spec.1
        have hy := (h.1 y).choose_spec.1
        simp only at hxy
        rw [← hxy] at hy
        exact (h.2 _).unique hx hy,
      fun x' => by
        obtain ⟨x, hx, -⟩ := h.2 x'
        exact ⟨x, ((h.1 x).choose_spec.2 x' hx).symm⟩⟩
theorem rel_equivOfPairs (h : PairsUniquely R) (x : X) : R x (equivOfPairs h x) :=
  (h.1 x).choose_spec.1
theorem equivOfPairs_eq (h : PairsUniquely R) {x : X} {x' : X'} (hx : R x x') :
    equivOfPairs h x = x' :=
  (h.1 x).unique (rel_equivOfPairs h x) hx
theorem funext_of_finsum_mul {Y : Set X} {v w : X → ℝ} (hv : ∀ x, x ∉ Y → v x = 0)
    (hw : ∀ x, x ∉ Y → w x = 0)
    (h : ∀ u : X → ℝ, (∀ x, x ∉ Y → u x = 0) → ∑ᶠ x, v x * u x = ∑ᶠ x, w x * u x) : v = w := by
  classical
  funext x
  by_cases hx : x ∈ Y
  · have hu : ∀ y, y ∉ Y → (Pi.single x 1 : X → ℝ) y = 0 := fun y hy =>
      Pi.single_eq_of_ne (by rintro rfl; exact hy hx) _
    have h1 := h (Pi.single x 1) hu
    have e : ∀ f : X → ℝ, ∑ᶠ y, f y * (Pi.single x 1 : X → ℝ) y = f x := fun f => by
      rw [finsum_eq_single _ x fun y hy => by simp [Pi.single_eq_of_ne hy]]
      simp
    rwa [e, e] at h1
  · rw [hv x hx, hw x hx]
end PairingOff
theorem formalAdjoint_spec {ι κ : Type} {L t : ℕ} [Finite ι] [Finite κ]
    (T : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) (f : ι → ℝ) (g : κ → ℝ) :
    latticeInner L t g (T f) = latticeInner L t (formalAdjoint L t T g) f := by
  classical
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite κ
  have hex : ∃ T' : (κ → ℝ) →ₗ[ℝ] (ι → ℝ),
      ∀ f g, latticeInner L t g (T f) = latticeInner L t (T' g) f := by
    refine ⟨Matrix.toLin' (LinearMap.toMatrix' T).transpose, fun f g => ?_⟩
    simp only [latticeInner, finsum_eq_sum_of_fintype]
    congr 1
    have h1 : T f = (LinearMap.toMatrix' T).mulVec f := (LinearMap.toMatrix'_mulVec T f).symm
    rw [h1, Matrix.toLin'_apply, Matrix.mulVec_transpose]
    exact Matrix.dotProduct_mulVec g _ f
  exact Classical.epsilon_spec
    (p := fun T' : (κ → ℝ) →ₗ[ℝ] (ι → ℝ) =>
      ∀ f g, latticeInner L t g (T f) = latticeInner L t (T' g) f)
    hex f g
section EvaluationMaps
variable (s : SequenceData) (𝒮 : RegionSequence.NestedRegions)
theorem toTorus_eq (x : s.data.Point) : s.toTorus 𝒮.side x = ClassData.regionEquiv s.data 𝒮 x := by
  unfold SequenceData.toTorus
  rw [dif_pos 𝒮.side_pos.ne']
  rfl
theorem unitTorusSide_eq : s.unitTorusSide = s.data.levelUnitTorus.toScaleData.torusSide := by
  have ht := s.data.t_le_cutoff
  show 2 * (s.data.L : ℝ) ^ (((s.data.m : ℕ) : ℤ) + ((s.data.K : ℕ) : ℤ) - (s.data.t : ℤ)) =
    2 * (s.data.L : ℝ) ^ ((s.data.m : ℕ) + (s.data.K : ℕ) - s.data.t)
  rw [← zpow_natCast]
  congr 2
  omega
variable {s 𝒮}
theorem mesh_eq (hS : s.IsNestedRegions 𝒮) : 𝒮.ξ = finestMeshInLevelUnits s.data.L s.data.t :=
  hS.ξ_eq
theorem meshSize_mul_ratio (hS : s.IsNestedRegions 𝒮) :
    PeriodicLattice.meshSize s.data.L (levelDepth s.data.cutoff 0) *
      ((PeriodicLattice.torusSide s.data.L s.data.m)⁻¹ * 𝒮.side) = 𝒮.ξ := by apply _root_.YangMills.Construction.SeparatedClasses.SingleSequence.NestedRescale.meshSize_zero_mul_rescaleFactor <;> assumption
theorem toTorus_apply (x : s.data.Point) (μ : Fin 4) :
    s.toTorus 𝒮.side x μ =
      AddCircle.equivAddCircle _ 𝒮.side s.torusSide_ne_zero 𝒮.side_pos.ne' (x μ) := by
  simp only [SequenceData.toTorus, dif_pos 𝒮.side_pos.ne']
theorem toTorus_unitStep (hS : s.IsNestedRegions 𝒮) (μ : Fin 4) :
    s.toTorus 𝒮.side ((PeriodicLattice.unitStep s.data.L s.data.m (levelDepth s.data.cutoff 0) μ :
        PeriodicLattice.Site s.data.L s.data.m (levelDepth s.data.cutoff 0)) : s.data.Point) =
      ((Dirichlet.unitStep 4 𝒮.side 𝒮.ξ μ : Dirichlet.LatticeSite 4 𝒮.side 𝒮.ξ) :
        𝒮.Point) := by
  funext ν
  rw [toTorus_apply]
  by_cases hν : ν = μ
  · subst hν
    simp only [PeriodicLattice.unitStep, pointOnAxis, Dirichlet.unitStep, Torus.torusProj,
      Pi.single_eq_same]
    rw [AddCircle.equivAddCircle_apply_mk, meshSize_mul_ratio hS]
  · simp [PeriodicLattice.unitStep, pointOnAxis, Dirichlet.unitStep, Torus.torusProj,
      Pi.single_eq_of_ne hν]
end EvaluationMaps
section Members
variable {s : SequenceData} {𝒮 : RegionSequence.NestedRegions}
  (hs : PairsUniquely (s.scalarData.SiteRel (scalarDataOfNested 𝒮) (s.toTorus 𝒮.side)))
  (hb : PairsUniquely (s.oneFormData.BondRel (oneFormDataOfNested 𝒮) (s.toTorus 𝒮.side)))
def siteEquiv : s.data.BareSite ≃ 𝒮.FineSite := equivOfPairs hs
def bondEquiv : s.data.BareBond ≃ 𝒮.FineBond := equivOfPairs hb
def plaquetteEquiv : BarePlaquette s.data.L s.data.m s.data.cutoff ≃ 𝒮.FinePlaquette where
  toFun p := (siteEquiv hs p.origin, ⟨(p.firstAxis, p.secondAxis), p.firstAxis_lt_secondAxis⟩)
  invFun q := ⟨(siteEquiv hs).symm q.1, q.2.1.1, q.2.1.2, q.2.2⟩
  left_inv p := by simp
  right_inv q := by simp
theorem coe_siteEquiv (x : s.data.BareSite) :
    ((siteEquiv hs x : 𝒮.FineSite) : 𝒮.Point) = s.toTorus 𝒮.side (x : s.data.Point) :=
  (rel_equivOfPairs hs x).symm
theorem siteEquiv_add_unitStep (hS : s.IsNestedRegions 𝒮) (x : s.data.BareSite) (μ : Fin 4) :
    siteEquiv hs (x + PeriodicLattice.unitStep s.data.L s.data.m (levelDepth s.data.cutoff 0) μ) =
      siteEquiv hs x + Dirichlet.unitStep 4 𝒮.side 𝒮.ξ μ := by
  apply Subtype.ext
  rw [coe_siteEquiv]
  change s.toTorus 𝒮.side ((x : s.data.Point) + _) =
    ((siteEquiv hs x : 𝒮.FineSite) : 𝒮.Point) + _
  rw [coe_siteEquiv, toTorus_eq, map_add, ← toTorus_eq, ← toTorus_eq, toTorus_unitStep hS]
theorem bondEquiv_bondFrom (hS : s.IsNestedRegions 𝒮) (x : s.data.BareSite) (μ : Fin 4) :
    bondEquiv hb (bondFrom x μ) = ⟨siteEquiv hs x, μ⟩ := by
  refine equivOfPairs_eq hb ?_
  refine Prod.ext ?_ ?_
  · exact (coe_siteEquiv hs x).symm
  · change s.toTorus 𝒮.side
      (((x + PeriodicLattice.unitStep s.data.L s.data.m (levelDepth s.data.cutoff 0) μ :
        PeriodicLattice.Site s.data.L s.data.m (levelDepth s.data.cutoff 0))) : s.data.Point) =
      ((siteEquiv hs x + Dirichlet.unitStep 4 𝒮.side 𝒮.ξ μ : 𝒮.FineSite) : 𝒮.Point)
    rw [← siteEquiv_add_unitStep hs hS, coe_siteEquiv]
variable (hS : s.IsNestedRegions 𝒮)
end Members
section Adjoints
variable {s : SequenceData} {𝒮 : RegionSequence.NestedRegions}
  (hs : PairsUniquely (s.scalarData.SiteRel (scalarDataOfNested 𝒮) (s.toTorus 𝒮.side)))
  (hb : PairsUniquely (s.oneFormData.BondRel (oneFormDataOfNested 𝒮) (s.toTorus 𝒮.side)))
  (hS : s.IsNestedRegions 𝒮)
theorem finite_bareSite (s : SequenceData) : Finite s.data.BareSite :=
  s.params.instFiniteLatticeSite 0
end Adjoints
section Spaces
theorem mem_range_indicatorMul {ι : Type} {X : Set ι} {f : ι → ℝ} :
    f ∈ LinearMap.range (indicatorMul X) ↔ ∀ i, i ∉ X → f i = 0 := by
  constructor
  · rintro ⟨g, rfl⟩ i hi
    exact Set.indicator_of_notMem hi g
  · intro hf
    refine ⟨f, ?_⟩
    funext i
    by_cases hi : i ∈ X
    · exact Set.indicator_of_mem hi f
    · rw [hf i hi]
      exact Set.indicator_of_notMem hi f
theorem indicatorMul_of_mem {ι : Type} {X : Set ι} {f : ι → ℝ}
    (hf : f ∈ LinearMap.range (indicatorMul X)) : indicatorMul X f = f := by
  obtain ⟨g, rfl⟩ := hf
  funext i
  by_cases hi : i ∈ X
  · change X.indicator (X.indicator g) i = X.indicator g i
    simp [hi]
  · change X.indicator (X.indicator g) i = X.indicator g i
    simp [hi]
variable {s : SequenceData} {𝒮 : RegionSequence.NestedRegions}
  (hs : PairsUniquely (s.scalarData.SiteRel (scalarDataOfNested 𝒮) (s.toTorus 𝒮.side)))
  (hb : PairsUniquely (s.oneFormData.BondRel (oneFormDataOfNested 𝒮) (s.toTorus 𝒮.side)))
  (hS : s.IsNestedRegions 𝒮)
end Spaces
section Operators
variable {s : SequenceData} {𝒮 : RegionSequence.NestedRegions}
  (hs : PairsUniquely (s.scalarData.SiteRel (scalarDataOfNested 𝒮) (s.toTorus 𝒮.side)))
  (hb : PairsUniquely (s.oneFormData.BondRel (oneFormDataOfNested 𝒮) (s.toTorus 𝒮.side)))
  (hS : s.IsNestedRegions 𝒮)
end Operators
section Forms
variable {s : SequenceData} {𝒮 : RegionSequence.NestedRegions}
  (hs : PairsUniquely (s.scalarData.SiteRel (scalarDataOfNested 𝒮) (s.toTorus 𝒮.side)))
  (hb : PairsUniquely (s.oneFormData.BondRel (oneFormDataOfNested 𝒮) (s.toTorus 𝒮.side)))
  (hS : s.IsNestedRegions 𝒮)
end Forms
end SeparatedClasses.NestedOneForms
end YangMills.Construction
