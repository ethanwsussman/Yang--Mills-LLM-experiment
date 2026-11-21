import YangMills.Construction.InfiniteLattice.TorusInequalitiesPassToTheMeasuresOfAnInvariantClass
import YangMills.Construction.TransferOperators.PropertiesOfAnOperatorBetweenTwoSquareRootsOfTheBondKernel
import YangMills.Construction.TransferOperators.TraceInequalityOfContractions
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.InfiniteLattice YangMills.Construction.SpinHarmonics
noncomputable section
namespace YangMills.Construction.TransferOperators
variable {μ : Fin 4}
def SliceLink.translate (b : SliceLink μ) (z : SliceSite μ) : SliceLink μ :=
  ⟨CutoffLattice.translateLink b.1 z,
    by
      obtain ⟨ρ, h⟩ := b.2.1
      refine ⟨ρ, ?_⟩
      change (b.1.terminal + (z : LatticePoint 1)) - (b.1.initial + (z : LatticePoint 1)) = _
      rw [add_sub_add_right_eq_sub]
      exact h,
    (sliceLattice μ).add_mem b.2.2.1 z.2, (sliceLattice μ).add_mem b.2.2.2 z.2⟩
abbrev Block.L2Operator (B : Block μ) : Type :=
  HaarL2 (B.links : Set (SliceLink μ)) →L[ℂ]
    HaarL2 (B.links : Set (SliceLink μ))
namespace Block
variable (B : Block μ)
def insertionLinks (i : ℤ) : Set (Link 1) :=
  {c | ∃ b ∈ B.links, c = (spatialLink μ i b).1 ∨ c = (spatialLink μ (i + 1) b).1} ∪
    {c | ∃ y ∈ B.vertices, c = (temporalLink μ i y).1}
def logKernelRatio (β : ℝ) (Ξ : B.L2Operator) (i : ℤ) (U : GaugeField 1) : ℂ :=
  let S : Stack := ⟨i, i + 1, lt_add_one i⟩
  let u := S.transportedRestriction μ U i (B.links : Set (SliceLink μ))
  let u' := S.transportedRestriction μ U (i + 1) (B.links : Set (SliceLink μ))
  Complex.log (sqrtKernelSandwich β Ξ u u' / linkProductKernel β u u')
def LogKernelRatioIsRealLocalInvariant (β : ℝ) (Ξ : B.L2Operator) (i : ℤ) : Prop :=
  B.logKernelRatio β Ξ i ∈ continuousLocalFunctions 1 ∧
    (∀ U, (B.logKernelRatio β Ξ i U).im = 0) ∧
    IsGaugeInvariantFunction (B.logKernelRatio β Ξ i) ∧
    DependsOnlyOn (B.insertionLinks i) (B.logKernelRatio β Ξ i)
def PairwiseDisjointShifts (i : ℤ) (Q' : AddSubgroup (LatticePoint 1)) : Prop :=
  Pairwise (Function.onFun Disjoint fun v : Q' =>
    shiftedLinks (Subtype.val '' B.atLevel i) (v : LatticePoint 1))
end Block
namespace CubicPeriodSublattice
variable (Γ : CubicPeriodSublattice)
variable (μ) in
def BoltzmannWeightEqProdSlices (β : ℝ) : Prop :=
  ∀ U : Γ.lattice.QuotientField,
    ((Γ.lattice.boltzmannWeight β U : ℝ) : ℂ) =
      ∏ j : ZMod Γ.side,
        Complex.exp (-Γ.sliceEnergy β (Γ.sliceField (μ := μ) U j)) *
          linkProductKernel β (Γ.sliceField (μ := μ) U j)
            (Γ.orbitGaugeAct (Γ.temporalSliceField (μ := μ) U j)
              (Γ.sliceField (μ := μ) U (j + 1)))
variable (μ) in
def PartitionFunctionEqTrace (β : ℝ) : Prop :=
  TraceSummablePW (Γ.transfer μ β ^ Γ.side) ∧
    ((Γ.lattice.partitionFunction β : ℝ) : ℂ) = tracePW (Γ.transfer μ β ^ Γ.side)
variable (B : Block μ)
def blockCopy (v : LatticePoint 1) (b : ↥(B.links : Set (SliceLink μ))) : Γ.LinkOrbits μ :=
  Γ.linkClass (b.1.translate (slicePart μ v))
def blockCopyRange (v : LatticePoint 1) : Set (Γ.LinkOrbits μ) := Set.range (Γ.blockCopy B v)
variable (μ) in
def copyLevel (i : ℤ) (v : LatticePoint 1) : ZMod Γ.side := Γ.levelClass (i + level μ v)
def operatorCopy (Ξ : B.L2Operator) (v : LatticePoint 1) :
    HaarL2 ↥(Γ.blockCopyRange B v) →L[ℂ] HaarL2 ↥(Γ.blockCopyRange B v) :=
  linkRelabelOp (Set.rangeFactorization (Γ.blockCopy B v)) Ξ
def operatorCopyTensor (Ξ : B.L2Operator) (v : LatticePoint 1) : Γ.SliceL2 μ →L[ℂ] Γ.SliceL2 μ :=
  tensorOne (Γ.blockCopyRange B v) (Γ.operatorCopy B Ξ v)
abbrev CosetsMod (Q' : AddSubgroup (LatticePoint 1)) : Type := Q' ⧸ Γ.lattice.periods.addSubgroupOf Q'
def cosetRep {Q' : AddSubgroup (LatticePoint 1)} (c : Γ.CosetsMod Q') : LatticePoint 1 :=
  ((Quotient.out c : Q') : LatticePoint 1)
instance instFiniteCosetsMod (Q' : AddSubgroup (LatticePoint 1)) : Finite (Γ.CosetsMod Q') := by
  refine Finite.of_injective (fun c => Γ.coordResidues (Γ.cosetRep c)) fun c c' h => ?_
  have h₁ := Γ.sub_mem_periods (congrFun h)
  rw [← Quotient.out_eq c, ← Quotient.out_eq c']
  refine (QuotientAddGroup.eq).mpr (AddSubgroup.mem_addSubgroupOf.mpr ?_)
  have e : (((-Quotient.out c + Quotient.out c' : Q') : LatticePoint 1)) =
      Γ.cosetRep c' - Γ.cosetRep c := by
    simp [cosetRep, sub_eq_add_neg, add_comm]
  rw [e]
  exact h₁
variable (μ) in
def cosetsAtLevel (i : ℤ) (Q' : AddSubgroup (LatticePoint 1)) (j : ZMod Γ.side) : Finset (Γ.CosetsMod Q') :=
  (Set.toFinite {c : Γ.CosetsMod Q' | Γ.copyLevel μ i (Γ.cosetRep c) = j}).toFinset
def levelProductOp (Ξ : B.L2Operator) (i : ℤ) (Q' : AddSubgroup (LatticePoint 1)) (j : ZMod Γ.side) :
    Γ.SliceL2 μ →L[ℂ] Γ.SliceL2 μ :=
  (((Γ.cosetsAtLevel μ i Q' j).toList).map fun c =>
    Γ.operatorCopyTensor B Ξ (Γ.cosetRep c)).prod
def levelProductOps (Ξ : B.L2Operator) (i : ℤ) (Q' : AddSubgroup (LatticePoint 1)) (k : Fin Γ.side) :
    Γ.SliceL2 μ →L[ℂ] Γ.SliceL2 μ :=
  Γ.levelProductOp B Ξ i Q' (Γ.levelClass ((k : ℕ) + 1))
def BlockCopiesDisjoint (i : ℤ) (Q' : AddSubgroup (LatticePoint 1)) : Prop :=
  (∀ v ∈ Q', ∀ v' ∈ Q', v - v' ∈ Γ.lattice.periods →
    Γ.blockCopy B v = Γ.blockCopy B v' ∧ Γ.blockCopyRange B v = Γ.blockCopyRange B v' ∧
      Γ.copyLevel μ i v = Γ.copyLevel μ i v') ∧
    (∀ v ∈ Q', Function.Injective (Γ.blockCopy B v)) ∧
    ∀ v ∈ Q', ∀ v' ∈ Q', v - v' ∉ Γ.lattice.periods →
      Γ.copyLevel μ i v = Γ.copyLevel μ i v' →
      Disjoint (Γ.blockCopyRange B v) (Γ.blockCopyRange B v')
def LevelProductOpsContract (Ξ : B.L2Operator) (i : ℤ) (Q' : AddSubgroup (LatticePoint 1)) : Prop :=
  ∀ j : ZMod Γ.side,
    (∀ c ∈ Γ.cosetsAtLevel μ i Q' j, ∀ c' ∈ Γ.cosetsAtLevel μ i Q' j,
      Commute (Γ.operatorCopyTensor B Ξ (Γ.cosetRep c))
        (Γ.operatorCopyTensor B Ξ (Γ.cosetRep c'))) ∧
    ‖Γ.levelProductOp B Ξ i Q' j‖ ≤ 1
def ExpShiftIntegralEqTrace (β : ℝ) (Ξ : B.L2Operator) (i : ℤ)
    (Q' : AddSubgroup (LatticePoint 1)) : Prop :=
  TraceSummablePW (interleavedProd (Γ.levelProductOps B Ξ i Q') (Γ.transfer μ β)) ∧
    ((∫ U, Real.exp (Γ.lattice.cosetSumOfShifts Q' (B.logKernelRatio β Ξ i) U) *
        Γ.lattice.boltzmannWeight β U ∂Γ.lattice.quotientHaar : ℝ) : ℂ) =
      tracePW (interleavedProd (Γ.levelProductOps B Ξ i Q') (Γ.transfer μ β))
def ExpShiftIntegralLePartitionFunction (β : ℝ) (Ξ : B.L2Operator) (i : ℤ)
    (Q' : AddSubgroup (LatticePoint 1)) : Prop :=
  Γ.lattice.ExpShiftSumInequality β Q' (B.logKernelRatio β Ξ i) ∧
    ∫ U, Γ.lattice.boltzmannWeight β U ∂Γ.lattice.quotientHaar = Γ.lattice.partitionFunction β
end CubicPeriodSublattice
end YangMills.Construction.TransferOperators
end
