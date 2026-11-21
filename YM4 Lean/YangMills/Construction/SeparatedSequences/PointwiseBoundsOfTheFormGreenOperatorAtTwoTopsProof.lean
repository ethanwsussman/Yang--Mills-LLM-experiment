import YangMills.Construction.SeparatedSequences.ClassExpansionsOnAGeneralTorusProof
import YangMills.Construction.DirichletOperator.PropagatorBoundsForDivergenceSourcesProof
import YangMills.Construction.DirichletOperator.SettingsOfASeparatedSequenceProof
import YangMills.Construction.SeparatedSequences.ChosenConstantsOfTheConditions
import YangMills.Construction.SeparatedSequences.FormsInASettingOfRegionsProof
import YangMills.Construction.SeparatedSequences.OneSequenceOneSetOfObjects
import YangMills.Construction.SeparatedSequences.PartitionsCubesExpansionsAndTheTriangleInequality
import YangMills.Construction.SeparatedSequences.SumsRatiosCubesThatMeetAndThePlaceOfAnExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric PeriodicLattice PeriodicLattice.DirichletOperators
namespace SeparatedClasses.ApexPairBounds
open SingleSequence SingleSequence.SequenceData
section PairingOff
variable {X X' : Type} {R : X → X' → Prop}
def pairEquiv (h : PairsUniquely R) : X ≃ X' :=
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
end PairingOff
theorem mem_range_indicatorMul {ι : Type} {X : Set ι} {f : ι → ℝ} :
    f ∈ LinearMap.range (indicatorMul X) ↔ ∀ i, i ∉ X → f i = 0 := by apply _root_.YangMills.Construction.SeparatedClasses.NestedOneForms.mem_range_indicatorMul <;> assumption
theorem indicatorMul_of_mem {ι : Type} {X : Set ι} {f : ι → ℝ}
    (hf : f ∈ LinearMap.range (indicatorMul X)) : indicatorMul X f = f := by apply _root_.YangMills.Construction.SeparatedClasses.NestedOneForms.indicatorMul_of_mem <;> assumption
section EvaluationMaps
variable {s : SequenceData} {𝒮 : RegionSequence.NestedRegions}
theorem toTorus_add (x x' : s.data.Point) :
    s.toTorus 𝒮.side (x + x') = s.toTorus 𝒮.side x + s.toTorus 𝒮.side x' := by apply _root_.YangMills.Construction.SeparatedClasses.FormsMatch.toTorus_add <;> assumption
theorem toTorus_neg (x : s.data.Point) : s.toTorus 𝒮.side (-x) = -s.toTorus 𝒮.side x := by apply _root_.YangMills.Construction.SeparatedClasses.FormsMatch.toTorus_neg <;> assumption
theorem toTorus_unitStep (hS : s.IsNestedRegions 𝒮) (μ : Fin 4) :
    s.toTorus 𝒮.side ((PeriodicLattice.unitStep s.data.L s.data.m
        (PeriodicLattice.levelDepth s.data.cutoff 0) μ :
        PeriodicLattice.Site s.data.L s.data.m (PeriodicLattice.levelDepth s.data.cutoff 0)) :
          s.data.Point) =
      ((Dirichlet.unitStep 4 𝒮.side 𝒮.ξ μ : Dirichlet.LatticeSite 4 𝒮.side 𝒮.ξ) :
        𝒮.Point) := by apply _root_.YangMills.Construction.SeparatedClasses.NestedOneForms.toTorus_unitStep <;> assumption
variable (s 𝒮) in
abbrev BondsCorrespond : s.data.BareBond → 𝒮.FineBond → Prop :=
  s.oneFormData.BondRel (oneFormDataOfNested 𝒮) (s.toTorus 𝒮.side)
end EvaluationMaps
section Bonds
variable {s : SequenceData} {𝒮 : RegionSequence.NestedRegions}
  (hb : PairsUniquely (BondsCorrespond s 𝒮))
def bondEquiv : s.data.BareBond ≃ 𝒮.FineBond := pairEquiv hb
end Bonds
theorem weightedDist_nonneg (𝒮 : RegionSequence.NestedRegions) (p q : 𝒮.Point) :
    0 ≤ 𝒮.weightedDist p q := by apply _root_.YangMills.Construction.DivSourceEstimate.weightedDist_nonneg <;> assumption
section Divergence
variable (s : SequenceData)
def translateEquiv (μ : Fin 4) : s.data.BareBond ≃ s.data.BareBond where
  toFun := translateBond (s.data.fineStep μ)
  invFun := translateBond (-s.data.fineStep μ)
  left_inv b := Subtype.ext (PeriodicLattice.Bond.ext (by simp [translateBond])
    (by simp [translateBond]))
  right_inv b := Subtype.ext (PeriodicLattice.Bond.ext (by simp [translateBond])
    (by simp [translateBond]))
theorem finestMesh_ne_zero : s.data.finestMesh ≠ 0 := by apply _root_.YangMills.Construction.SeparatedClasses.GaugeOneFormsProof.TorusComponents.finestMesh_ne_zero <;> assumption
end Divergence
section LinearMaps
variable (s : SequenceData)
def greenLinear : s.data.BondFn →ₗ[ℝ] s.data.BondFn :=
  (oneFormsOn s.data.cutoff (s.Ω 0) s.frame).subtype ∘ₗ
    s.data.unitSpacingParameters.oneGreen s.Ω s.frame ∘ₗ
      (bondProjection s.data.cutoff (s.Ω 0) s.frame).rangeRestrict
end LinearMaps
section Parts
variable {ι Z : Type}
open Classical in
def restrictTo (p : ι → Z) (z : Z) (A : ι → ℝ) : ι → ℝ := fun b => if p b = z then A b else 0
end Parts
section Cubes
variable {C : ClassData} {Ω : ℕ → Set C.Point}
theorem mesh_pos (y : C.Apex Ω) (hL : 0 < (C.L : ℝ)) : 0 < y.mesh := zpow_pos hL _
end Cubes
end SeparatedClasses.ApexPairBounds
end YangMills.Construction
end
