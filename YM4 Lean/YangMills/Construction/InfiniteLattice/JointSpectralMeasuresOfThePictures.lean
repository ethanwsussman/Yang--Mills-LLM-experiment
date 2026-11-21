import YangMills.Construction.InfiniteLattice.OperatorsAndMatrixElementsOfTheTwoCoordinatePictures
import YangMills.Construction.JointSpectrum.SpectralIntegral
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Set
open YangMills.Construction.OneLoopNotation YangMills.Construction.ComplexHilbert
open YangMills.Construction.JointSpectrum
open scoped InnerProductSpace ComplexOrder
noncomputable section
namespace YangMills.Construction.LatticeConventions
section Families
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {J J' : Type} [Fintype J] [Nonempty J] [Fintype J'] [Nonempty J']
structure IsCommutingFamilyData (T : BddOp H) (U : J → BddOp H) : Prop where
  isSymmetric : IsSymmetricOp T
  nonneg : OpGE T 0
  le_one : OpLE T (idOp H)
  unitary : ∀ i, IsUnitaryMap (U i : H →ₗ[ℂ] H)
  commute_T_U : ∀ i, Commute T (U i)
  commute_U_U : ∀ i j, Commute (U i) (U j)
theorem isSelfAdjoint_of_isSymmetricOp {S : BddOp H}
    (hS : IsSymmetricOp S) : IsSelfAdjoint S :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr fun x y => (hS x y).symm
theorem le_of_opLE {S S' : BddOp H} (hS : OpLE S S') : S ≤ S' := by
  rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_def]
  refine ⟨(isSelfAdjoint_of_isSymmetricOp hS.right).sub
    (isSelfAdjoint_of_isSymmetricOp hS.left)
    |> ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp, fun x => ?_⟩
  have hre := (Complex.le_def.mp (hS.le x)).1
  change 0 ≤ (inner ℂ ((S' - S) x) x).re
  rw [sub_apply, inner_sub_left, ← hS.right x x, ← hS.left x x, Complex.sub_re]
  linarith
theorem mem_unitary_of_isUnitaryMap {V : BddOp H}
    (hV : IsUnitaryMap (V : H →ₗ[ℂ] H)) : V ∈ unitary (H →L[ℂ] H) := by
  have hleft : star V * V = 1 := by
    have := (ContinuousLinearMap.norm_map_iff_adjoint_comp_self V).mp hV.isometric
    simpa [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def] using this
  have hright : V * star V = 1 := by
    ext x
    obtain ⟨y, rfl⟩ := hV.onto x
    have : (star V) (V y) = y := congrArg (fun W : H →L[ℂ] H => W y) hleft
    change V (star V (V y)) = V y
    rw [this]
  exact Unitary.mem_iff.mpr ⟨hleft, hright⟩
def IsCommutingFamilyData.toFamily {T : BddOp H} {U : J → BddOp H}
    (hTU : IsCommutingFamilyData T U) : CommutingFamily H J where
  A := T
  B := fun i => ⟨U i, mem_unitary_of_isUnitaryMap (hTU.unitary i)⟩
  isSelfAdjoint_A := isSelfAdjoint_of_isSymmetricOp hTU.isSymmetric
  zero_le_A := le_of_opLE hTU.nonneg
  A_le_one := le_of_opLE hTU.le_one
  commute_A_B := hTU.commute_T_U
  commute_B_B := hTU.commute_U_U
variable (H J) in
def trivialFamily : CommutingFamily H J where
  A := 0
  B := fun _ => 1
  isSelfAdjoint_A := IsSelfAdjoint.zero _
  zero_le_A := le_rfl
  A_le_one := (ContinuousLinearMap.nonneg_iff_isPositive _).mpr ContinuousLinearMap.isPositive_one
  commute_A_B := fun _ => Commute.zero_left _
  commute_B_B := fun _ _ => Commute.refl _
def familyOf (T : BddOp H) (U : J → BddOp H) : CommutingFamily H J :=
  open Classical in
  if hTU : IsCommutingFamilyData T U then hTU.toFamily else trivialFamily H J
theorem familyOf_A {T : BddOp H} {U : J → BddOp H}
    (hTU : IsCommutingFamilyData T U) : (familyOf T U).A = T := by
  rw [familyOf, dif_pos hTU]
  rfl
theorem familyOf_B {T : BddOp H} {U : J → BddOp H}
    (hTU : IsCommutingFamilyData T U) (i : J) :
    ((familyOf T U).B i : H →L[ℂ] H) = U i := by
  rw [familyOf, dif_pos hTU]
  rfl
theorem IsCommutingFamilyData.comp {T : BddOp H} {U : J → BddOp H}
    (hTU : IsCommutingFamilyData T U) (f : J' → J) :
    IsCommutingFamilyData T (U ∘ f) where
  isSymmetric := hTU.isSymmetric
  nonneg := hTU.nonneg
  le_one := hTU.le_one
  unitary := fun i => hTU.unitary (f i)
  commute_T_U := fun i => hTU.commute_T_U (f i)
  commute_U_U := fun i j => hTU.commute_U_U (f i) (f j)
end Families
abbrev TransverseDirection (μ : Direction) : Type := {d : Direction // d ≠ μ}
instance instNonemptyTransverseDirection (μ : Direction) : Nonempty (TransverseDirection μ) :=
  ⟨⟨μ + 1, by revert μ; decide⟩⟩
abbrev SingleTransverse {μ : Direction} (d : TransverseDirection μ) : Type :=
  ↥({d} : Set (TransverseDirection μ))
namespace LinkFrame
variable (a : Spacing) (μ : Direction)
  (ν : Measure (YangMills.Construction.InfiniteLattice.GaugeField (a : ℝ)))
  [IsProbabilityMeasure ν]
def singleShiftFamily (d : TransverseDirection μ) :
    CommutingFamily (LinkHilbertSpace a μ ν) (SingleTransverse d) :=
  familyOf (transferOperator a μ ν) fun i => transverseShift a μ ν i.1
def allShiftsFamily : CommutingFamily (LinkHilbertSpace a μ ν) (TransverseDirection μ) :=
  familyOf (transferOperator a μ ν) (transverseShift a μ ν)
def singleShiftSpectralMeasure (d : TransverseDirection μ) :
    Set (SpectralDomain (SingleTransverse d)) → LinkHilbertSpace a μ ν → LinkHilbertSpace a μ ν :=
  YangMills.Construction.JointSpectrum.SpectralIntegral.jointSpectralMeasure
    (singleShiftFamily a μ ν d)
def allShiftsSpectralMeasure :
    Set (SpectralDomain (TransverseDirection μ)) → LinkHilbertSpace a μ ν → LinkHilbertSpace a μ ν :=
  YangMills.Construction.JointSpectrum.SpectralIntegral.jointSpectralMeasure
    (allShiftsFamily a μ ν)
variable {a μ ν}
theorem TransferMatrixElements.isCommutingFamilyData (hM : TransferMatrixElements a μ ν) :
    IsCommutingFamilyData (transferOperator a μ ν) (transverseShift a μ ν) :=
  ⟨hM.1, hM.2.1, hM.2.2.1, hM.2.2.2.1, hM.2.2.2.2.1, hM.2.2.2.2.2.1⟩
theorem TransferMatrixElements.allShiftsFamily_ops
    (hM : TransferMatrixElements a μ ν) :
    (allShiftsFamily a μ ν).A = transferOperator a μ ν ∧
      ∀ d, ((allShiftsFamily a μ ν).B d : BddOp (LinkHilbertSpace a μ ν)) =
        transverseShift a μ ν d :=
  ⟨familyOf_A hM.isCommutingFamilyData, familyOf_B hM.isCommutingFamilyData⟩
theorem TransferMatrixElements.singleShiftFamily_ops
    (hM : TransferMatrixElements a μ ν) (d : TransverseDirection μ) :
    (singleShiftFamily a μ ν d).A = transferOperator a μ ν ∧
      ∀ i, ((singleShiftFamily a μ ν d).B i : BddOp (LinkHilbertSpace a μ ν)) =
        transverseShift a μ ν d := by
  have hsub := hM.isCommutingFamilyData.comp (J' := SingleTransverse d) Subtype.val
  refine ⟨familyOf_A hsub, fun i => ?_⟩
  have hi : i.1 = d := i.2
  exact (familyOf_B hsub i).trans (congrArg (transverseShift a μ ν) hi)
end LinkFrame
namespace SiteFrame
variable (a : Spacing) (μ : Direction)
  (ν : Measure (YangMills.Construction.InfiniteLattice.GaugeField (a : ℝ)))
  [IsProbabilityMeasure ν]
def singleShiftFamily (d : TransverseDirection μ) :
    CommutingFamily (SiteHilbertSpace a μ ν) (SingleTransverse d) :=
  familyOf (transferOperator a μ ν) fun i => transverseShift a μ ν i.1
def allShiftsFamily : CommutingFamily (SiteHilbertSpace a μ ν) (TransverseDirection μ) :=
  familyOf (transferOperator a μ ν) (transverseShift a μ ν)
def singleShiftSpectralMeasure (d : TransverseDirection μ) :
    Set (SpectralDomain (SingleTransverse d)) → SiteHilbertSpace a μ ν → SiteHilbertSpace a μ ν :=
  YangMills.Construction.JointSpectrum.SpectralIntegral.jointSpectralMeasure
    (singleShiftFamily a μ ν d)
def allShiftsSpectralMeasure :
    Set (SpectralDomain (TransverseDirection μ)) → SiteHilbertSpace a μ ν → SiteHilbertSpace a μ ν :=
  YangMills.Construction.JointSpectrum.SpectralIntegral.jointSpectralMeasure
    (allShiftsFamily a μ ν)
variable {a μ ν}
theorem TransferMatrixElements.isCommutingFamilyData (hM : TransferMatrixElements a μ ν) :
    IsCommutingFamilyData (transferOperator a μ ν) (transverseShift a μ ν) :=
  ⟨hM.1, hM.2.1, hM.2.2.1, hM.2.2.2.1, hM.2.2.2.2.1, hM.2.2.2.2.2.1⟩
theorem TransferMatrixElements.allShiftsFamily_ops
    (hM : TransferMatrixElements a μ ν) :
    (allShiftsFamily a μ ν).A = transferOperator a μ ν ∧
      ∀ d, ((allShiftsFamily a μ ν).B d : BddOp (SiteHilbertSpace a μ ν)) =
        transverseShift a μ ν d :=
  ⟨familyOf_A hM.isCommutingFamilyData, familyOf_B hM.isCommutingFamilyData⟩
theorem TransferMatrixElements.singleShiftFamily_ops
    (hM : TransferMatrixElements a μ ν) (d : TransverseDirection μ) :
    (singleShiftFamily a μ ν d).A = transferOperator a μ ν ∧
      ∀ i, ((singleShiftFamily a μ ν d).B i : BddOp (SiteHilbertSpace a μ ν)) =
        transverseShift a μ ν d := by
  have hsub := hM.isCommutingFamilyData.comp (J' := SingleTransverse d) Subtype.val
  refine ⟨familyOf_A hsub, fun i => ?_⟩
  have hi : i.1 = d := i.2
  exact (familyOf_B hsub i).trans (congrArg (transverseShift a μ ν) hi)
end SiteFrame
section Support
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {J : Type*} [Fintype J] [Nonempty J]
def SpectralMapSupportedOn (E : Set (SpectralDomain J) → K → K) (C : Set (SpectralDomain J)) :
    Prop :=
  MeasurableSet C ∧ E Cᶜ = 0
end Support
end YangMills.Construction.LatticeConventions
end
