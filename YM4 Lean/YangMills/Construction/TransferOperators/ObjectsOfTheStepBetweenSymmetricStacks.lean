import YangMills.Construction.TransferOperators.CharacterCoefficientsOfTheOneBondWeightProof
import YangMills.Construction.TransferOperators.ReflectionInALinkMirrorSymmetricStacksAndTheReversal
import YangMills.Construction.TransferOperators.SymmetryBoundsAndInvarianceOfTheBondKernelAndTheLayerEnergy
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open MeasureTheory Set InfiniteLattice SpinHarmonics Matrices.ComplexMatrix2
noncomputable section
namespace TransferOperators
variable {μ : Fin 4}
theorem Block.touchingPlaquettes_finite (B : Block μ) : B.touchingPlaquettes.Finite := by
  refine (B.links.finite_toSet.biUnion fun b _ =>
    SlicePlaquette.finite_setOf_mem_links b).subset ?_
  rintro p ⟨b, hb, hp⟩
  exact mem_iUnion₂.2 ⟨b, hb, hp⟩
theorem continuous_singleBondWeight (β : ℝ) : Continuous (singleBondWeight β) := by apply _root_.YangMills.Construction.SpinHarmonics.BondWeightCoeffs.continuous_singleBondWeight <;> assumption
theorem continuous_linkProductKernel (β : ℝ) {B : Type} [Finite B] :
    Continuous fun p : (B → specialUnitary) × (B → specialUnitary) =>
      linkProductKernel β p.1 p.2 := by
  let _ : Fintype B := Fintype.ofFinite B
  simp only [linkProductKernel, finprod_eq_prod_of_fintype]
  exact continuous_finsetProd _ fun b _ => (continuous_singleBondWeight β).comp
    (((continuous_apply b).comp continuous_fst).mul
      ((continuous_apply b).comp continuous_snd).inv)
theorem Block.continuous_sliceEnergy (B : Block μ) (β : ℝ) :
    Continuous fun p : (B.links → specialUnitary) ×
      (↥(B.thickened \ (B.links : Set (SliceLink μ))) → specialUnitary) =>
        B.sliceEnergy β p.1 p.2 := by
  let _ : Fintype B.touchingPlaquettes := B.touchingPlaquettes_finite.fintype
  simp only [Block.sliceEnergy, finsum_eq_sum_of_fintype]
  refine continuous_const.mul (continuous_finsetSum _ fun q _ => continuous_const.sub
    (continuous_const.mul (Continuous.matrix_trace (continuous_subtype_val.comp ?_))))
  have hg : ∀ b : B.thickened, Continuous fun p : (B.links → specialUnitary) ×
      (↥(B.thickened \ (B.links : Set (SliceLink μ))) → specialUnitary) =>
        B.gluedConfiguration p.1 p.2 b := by
    intro b
    by_cases h : b.1 ∈ B.links
    · simp only [Block.gluedConfiguration, dif_pos h]
      exact (continuous_apply _).comp continuous_fst
    · simp only [Block.gluedConfiguration, dif_neg h]
      exact (continuous_apply _).comp continuous_snd
  unfold plaquetteHolonomy
  exact (((hg _).mul (hg _)).mul (hg _).inv).mul (hg _).inv
variable (μ) in
structure CenteredStackStep where
  center : ℤ
  halfWidth : ℤ
  one_le_halfWidth : 1 ≤ halfWidth
  vertexSet : Set (SliceSite μ)
  vertexSet_finite : Finite vertexSet
  block : Block μ
  thickened_subset : block.thickened ⊆ linksWithin vertexSet
namespace CenteredStackStep
variable (D : CenteredStackStep μ)
instance : Finite D.vertexSet := D.vertexSet_finite
abbrev InnerPairs : Type := ↥(centeredLinkPairs D.center D.halfWidth D.vertexSet)
def enclosingStack : Stack :=
  centeredStack D.center (D.halfWidth + 1) (by have := D.one_le_halfWidth; omega)
def enclosingValues (U : GaugeField 1) : D.InnerPairs → specialUnitary :=
  fun p => D.enclosingStack.transportedLinkVariable μ U p.1.1 p.1.2
def bottom : ℤ := D.center - D.halfWidth + 1
def top : ℤ := D.center + D.halfWidth
def IsInnerLevel (j : ℤ) : Prop := D.bottom ≤ j ∧ j ≤ D.top
theorem isInnerLevel_bottom : D.IsInnerLevel D.bottom := by
  have := D.one_le_halfWidth
  simp only [IsInnerLevel, bottom, top]
  omega
theorem isInnerLevel_top : D.IsInnerLevel D.top := by
  have := D.one_le_halfWidth
  simp only [IsInnerLevel, bottom, top]
  omega
theorem isInnerLevel_bottom_add_one : D.IsInnerLevel (D.bottom + 1) := by
  have := D.one_le_halfWidth
  simp only [IsInnerLevel, bottom, top]
  omega
theorem isInnerLevel_top_sub_one : D.IsInnerLevel (D.top - 1) := by
  have := D.one_le_halfWidth
  simp only [IsInnerLevel, bottom, top]
  omega
def innerPair {j : ℤ} (hj : D.IsInnerLevel j) (b : SliceLink μ) (hb : b ∈ D.block.thickened) :
    D.InnerPairs :=
  ⟨(j, b), hj.1, hj.2, D.thickened_subset hb⟩
def blockRestrict {j : ℤ} (hj : D.IsInnerLevel j) (u : D.InnerPairs → specialUnitary) :
    D.block.links → specialUnitary :=
  fun b => u (D.innerPair hj b.1 (D.block.subset_thickened b.2))
def collarRestrict {j : ℤ} (hj : D.IsInnerLevel j) (u : D.InnerPairs → specialUnitary) :
    ↥(D.block.thickened \ (D.block.links : Set (SliceLink μ))) → specialUnitary :=
  fun b => u (D.innerPair hj b.1 b.2.1)
def sliceEnergyAt (β : ℝ) {j : ℤ} (hj : D.IsInnerLevel j) (u : D.InnerPairs → specialUnitary) :
    ℂ :=
  D.block.sliceEnergy β (D.blockRestrict hj u) (D.collarRestrict hj u)
def bottomKernel (β : ℝ) (u : D.InnerPairs → specialUnitary) : ℂ :=
  linkProductKernel β (D.blockRestrict D.isInnerLevel_bottom u)
    (D.blockRestrict D.isInnerLevel_bottom_add_one u)
def topKernel (β : ℝ) (u : D.InnerPairs → specialUnitary) : ℂ :=
  linkProductKernel β (D.blockRestrict D.isInnerLevel_top u)
    (D.blockRestrict D.isInnerLevel_top_sub_one u)
def boundaryWeight (β : ℝ) (u : D.InnerPairs → specialUnitary) : ℂ :=
  Complex.exp (-D.sliceEnergyAt β D.isInnerLevel_bottom u - D.sliceEnergyAt β D.isInnerLevel_top u) *
    D.bottomKernel β u * if D.halfWidth = 1 then 1 else D.topKernel β u
theorem continuous_blockRestrict {j : ℤ} (hj : D.IsInnerLevel j) :
    Continuous (D.blockRestrict hj) := by
  unfold blockRestrict
  exact continuous_pi fun b => continuous_apply (D.innerPair hj b.1 (D.block.subset_thickened b.2))
theorem continuous_collarRestrict {j : ℤ} (hj : D.IsInnerLevel j) :
    Continuous (D.collarRestrict hj) := by
  unfold collarRestrict
  exact continuous_pi fun b => continuous_apply (D.innerPair hj b.1 b.2.1)
theorem continuous_sliceEnergyAt (β : ℝ) {j : ℤ} (hj : D.IsInnerLevel j) :
    Continuous (D.sliceEnergyAt β hj) := by
  have h := (D.block.continuous_sliceEnergy β).comp
    ((D.continuous_blockRestrict hj).prodMk (D.continuous_collarRestrict hj))
  exact h
theorem continuous_bottomKernel (β : ℝ) : Continuous (D.bottomKernel β) := by
  have h := (continuous_linkProductKernel β (B := D.block.links)).comp
    ((D.continuous_blockRestrict D.isInnerLevel_bottom).prodMk
      (D.continuous_blockRestrict D.isInnerLevel_bottom_add_one))
  exact h
theorem continuous_topKernel (β : ℝ) : Continuous (D.topKernel β) := by
  have h := (continuous_linkProductKernel β (B := D.block.links)).comp
    ((D.continuous_blockRestrict D.isInnerLevel_top).prodMk
      (D.continuous_blockRestrict D.isInnerLevel_top_sub_one))
  exact h
theorem continuous_boundaryWeight (β : ℝ) : Continuous (D.boundaryWeight β) := by
  unfold boundaryWeight
  refine (Complex.continuous_exp.comp (((D.continuous_sliceEnergyAt β _).neg).sub
    (D.continuous_sliceEnergyAt β _))).mul (D.continuous_bottomKernel β) |>.mul ?_
  split_ifs
  · exact continuous_const
  · exact D.continuous_topKernel β
def boundaryWeightMap (β : ℝ) : C(D.InnerPairs → specialUnitary, ℂ) :=
  ⟨D.boundaryWeight β, D.continuous_boundaryWeight β⟩
def levelPart (j : ℤ) : Set D.InnerPairs := {p | p.1.1 = j ∧ p.1.2 ∈ D.block.links}
def levelPartElement {j : ℤ} (hj : D.IsInnerLevel j) (b : D.block.links) : D.levelPart j :=
  ⟨D.innerPair hj b.1 (D.block.subset_thickened b.2), rfl, b.2⟩
def pullToLevel {j : ℤ} (hj : D.IsInnerLevel j) (f : (D.block.links → specialUnitary) → ℂ)
    (u : D.levelPart j → specialUnitary) : ℂ :=
  f fun b => u (D.levelPartElement hj b)
theorem isRealEntryPolynomial_pullToLevel {j : ℤ} (hj : D.IsInnerLevel j)
    {f : (D.block.links → specialUnitary) → ℂ} (hf : IsRealEntryPolynomial f) :
    IsRealEntryPolynomial (D.pullToLevel hj f) := by
  obtain ⟨⟨p, hp⟩, hr⟩ := hf
  refine ⟨⟨MvPolynomial.rename (Sum.map (Prod.map (D.levelPartElement hj) id)
    (Prod.map (D.levelPartElement hj) id)) p, fun u => ?_⟩, fun u => hr _⟩
  have e : entryEval (fun b => u (D.levelPartElement hj b)) = entryEval u ∘
      Sum.map (Prod.map (D.levelPartElement hj) id) (Prod.map (D.levelPartElement hj) id) := by
    funext x
    rcases x with ⟨b, i, j⟩ | ⟨b, i, j⟩ <;> rfl
  rw [MvPolynomial.eval_rename, pullToLevel, hp, e]
def transferStepFunction (β : ℝ) {f h : (D.block.links → specialUnitary) → ℂ}
    (hf : IsRealEntryPolynomial f) (hh : IsRealEntryPolynomial h)
    (Φ : C(D.InnerPairs → specialUnitary, ℂ)) (u : D.InnerPairs → specialUnitary) : ℂ :=
  (D.boundaryWeight β u)⁻¹ *
    hatSum β (D.levelPart D.bottom) (D.pullToLevel D.isInnerLevel_bottom f)
      (D.isRealEntryPolynomial_pullToLevel D.isInnerLevel_bottom hf)
      (hatSum β (D.levelPart D.top) (D.pullToLevel D.isInnerLevel_top h)
        (D.isRealEntryPolynomial_pullToLevel D.isInnerLevel_top hh) (D.boundaryWeightMap β * Φ)) u
end CenteredStackStep
end TransferOperators
end
end YangMills.Construction
