import YangMills.Construction.InfiniteLattice.ConeInequalityInTheLinkPicture
import YangMills.Construction.InfiniteLattice.FunctionsOfTheBondsOfASet
import YangMills.Construction.ReflectionPositivity.EnergyMomentumInequalityAtOneStepLinkForm
import YangMills.Construction.ReflectionPositivity.MatrixElementsAreCorrelations
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures.EnergyMomentumOneStep
open InfiniteLattice (GaugeField axisStep shift halfSpaceLocalObservables regionSigma_mono)
open ReflectionPositivity.MirrorHyperplanes (unitPositiveClass linkReflect)
open LatticeConventions (Spacing NormalHyperplane)
open JointSpectrum (CommutingFamily)
open ContractionUnitary (zpowOp opInv isTwoSidedInverse_opInv)
section Operators
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
theorem one_sub_sq_sub_mul_expand (T U V : H →L[ℂ] H) :
    (1 - T) ^ 2 - T * ((2 : ℂ) • 1 - U - V) =
      T ^ 0 * 1 - (4 : ℂ) • (T ^ 1 * 1) + T ^ 2 * 1 + T ^ 1 * U + T ^ 1 * V := by
  have htwo : (2 : ℂ) • (1 : H →L[ℂ] H) = 1 + 1 := two_smul ℂ 1
  have hfour : (4 : ℂ) • (T ^ 1 * 1) = T + T + T + T := by
    rw [show (4 : ℂ) = 1 + 1 + 1 + 1 by norm_num]
    simp only [add_smul, one_smul, pow_one, mul_one]
  rw [htwo, hfour]
  noncomm_ring
theorem inner_one_sub_sq_sub_mul (T U V : H →L[ℂ] H) (P : ℤ → H →L[ℂ] H) (hP0 : P 0 = 1)
    (hP1 : P 1 = U) (hPm : P (-1) = V) (ψ : H) :
    inner ℂ ψ (((1 - T) ^ 2 - T * ((2 : ℂ) • 1 - U - V) : H →L[ℂ] H) ψ) =
      inner ℂ ψ ((T ^ 0 * P 0) ψ) - 4 * inner ℂ ψ ((T ^ 1 * P 0) ψ) +
        inner ℂ ψ ((T ^ 2 * P 0) ψ) + inner ℂ ψ ((T ^ 1 * P 1) ψ) +
        inner ℂ ψ ((T ^ 1 * P (-1)) ψ) := by
  rw [hP0, hP1, hPm, one_sub_sq_sub_mul_expand]
  simp only [add_apply, sub_apply, smul_apply, inner_add_right, inner_sub_right, inner_smul_right]
theorem adjoint_eq_zpowOp_neg_one [CompleteSpace H] {V : H →L[ℂ] H}
    (hV : ComplexHilbert.IsUnitaryMap (V : H →ₗ[ℂ] H)) :
    ContinuousLinearMap.adjoint V = zpowOp V (-1) := by
  have hleft : ContinuousLinearMap.adjoint V * V = 1 :=
    (ContinuousLinearMap.norm_map_iff_adjoint_comp_self V).mp hV.isometric
  have hright : V * opInv V = 1 := (isTwoSidedInverse_opInv hV).1
  rw [ContractionUnitary.zpowOp_of_neg V (by norm_num), left_inv_eq_right_inv hleft hright]
  simp
end Operators
section Families
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {J : Type*} [Fintype J] [Nonempty J] [DecidableEq J]
theorem unitaryMonomial_eq_of_support (S : CommutingFamily K J) (α : J) (z : J → ℤ)
    (hz : ∀ β, β ≠ α → z β = 0) :
    S.unitaryMonomial z = ((S.B α ^ z α : unitary (K →L[ℂ] K)) : K →L[ℂ] K) := by
  have hprod : Finset.univ.noncommProd (fun β => S.B β ^ z β)
      (fun β _ β' _ _ => S.commute_zpow_unitary z β β') = S.B α ^ z α := by
    refine (Finset.mul_noncommProd_erase Finset.univ (Finset.mem_univ α) _ _).symm.trans ?_
    refine (congrArg (S.B α ^ z α * ·)
      (Finset.noncommProd_eq_pow_card _ _ _ 1 fun β hβ => ?_)).trans ?_
    · rw [hz β (Finset.ne_of_mem_erase hβ), zpow_zero]
    · simp
  exact congrArg Subtype.val hprod
end Families
section Comparison
open LatticeConventions.LinkFrame (upperAlgebra)
abbrev unitSpacing : Spacing := ⟨1, one_pos⟩
theorem reflectSymmetry_eq_reflect {a : ℝ} {Q : NormalHyperplane} (hQ : Q.IsLatticeMirror a) :
    NormalHyperplane.reflectSymmetry hQ = (NormalHyperplane.toMirrorPair hQ).reflect :=
  ReflectionPositivity.MirrorHyperplanes.latticeSymmetry_ext Q.reflect_eq_hyperplaneReflect
theorem isReflectionPositiveAcrossMirror_of_mem {ν : Measure (GaugeField (1 : ℝ))}
    [IsProbabilityMeasure ν] (hν : ν ∈ unitPositiveClass) {Q : NormalHyperplane}
    (hQ : Q.IsLatticeMirror 1) : NormalHyperplane.IsReflectionPositiveAcrossMirror hQ ν := by
  rintro ⟨F, hF⟩
  obtain ⟨B, hB, hO, hM⟩ := Set.mem_iUnion₂.1 hF
  have hpos := (hν.2.2 (NormalHyperplane.toMirrorPair hQ)).2 Q.upperHalfSpace (Or.inl rfl) F hO
    ⟨Q.upperHalfSpace ∩ B,
      Bornology.IsBounded.subset (Set.mem_ofPred.1 hB) Set.inter_subset_right, hM⟩
    (hM.mono (regionSigma_mono Set.inter_subset_left) le_rfl)
  have hform : NormalHyperplane.reflectionForm hQ ν ⟨F, hF⟩ ⟨F, hF⟩ =
      ∫ U, conj ((NormalHyperplane.toMirrorPair hQ).reflect.actOn F U) * F U ∂ν := by
    rw [← reflectSymmetry_eq_reflect]
    rfl
  rw [hform]
  have hle := Complex.le_def.mp hpos
  exact ⟨by simpa using hle.2.symm, by simpa using hle.1⟩
theorem pairConditions_of_mem {ν : Measure (GaugeField (1 : ℝ))}
    [IsProbabilityMeasure ν] (hν : ν ∈ unitPositiveClass) {μ κ : Fin 4}
    (hne : μ ≠ κ) : LatticeConventions.PairConditions (a := 1) hne ν :=
  ⟨hν.2.1, fun _ => isReflectionPositiveAcrossMirror_of_mem hν _,
    fun _ => isReflectionPositiveAcrossMirror_of_mem hν _⟩
theorem mem_upperAlgebra_of_mem (hreads : InfiniteLattice.LinkLocalFunctions.Statement)
    {μ : Fin 4} {F : GaugeField (1 : ℝ) → ℂ} (hF : F ∈ halfSpaceLocalObservables μ) :
    F ∈ upperAlgebra unitSpacing μ := by
  exact show F ∈ (upperAlgebra unitSpacing μ : Set (GaugeField (1 : ℝ) → ℂ)) from by
    rw [LatticeConventions.LinkFrame.coe_upperAlgebra]
    obtain ⟨B, hB, hO, hM⟩ := hreads.2.2.2.2.2.2 μ F hF
    refine Set.mem_iUnion₂.2 ⟨B, Set.mem_ofPred.2 hB, hO, hM.mono
      (regionSigma_mono (Set.inter_subset_inter_left B fun x hx => ?_)) le_rfl⟩
    have hx' : (0 : ℝ) ≤ x μ := hx
    change -((1 : ℝ) / 2) ≤ x μ
    linarith
theorem linkReflection_unitSpacing (μ : Fin 4) :
    LatticeConventions.LinkFrame.linkReflection unitSpacing μ = linkReflect μ :=
  ReflectionPositivity.MirrorHyperplanes.latticeSymmetry_ext (by
    funext x
    rw [LatticeConventions.LinkFrame.linkReflection_toFun,
      ReflectionPositivity.MirrorHyperplanes.linkReflect_apply]
    rfl)
theorem intPoint_single (l : Fin 4) (y : ℤ) : intPoint (Pi.single l y) = y • axisStep 1 l := by
  apply Subtype.ext
  funext i
  by_cases h : i = l
  · subst h
    simp [intPoint, axisStep]
  · simp [intPoint, axisStep, Pi.single_eq_of_ne h]
variable (ν : unitPositiveClass) (μ : Fin 4) (l : TransverseAxis μ)
theorem shiftMonomial_single (y : ℤ) :
    ReflectionPair.link.shiftMonomial ν μ (Pi.single l.1 y) =
      (((ReflectionPair.link.opFamily ν μ).B l ^ y : unitary _) : _ →L[ℂ] _) := by
  unfold ReflectionPair.shiftMonomial
  rw [unitaryMonomial_eq_of_support _ l _ fun β hβ =>
    Pi.single_eq_of_ne (fun e => hβ (Subtype.ext e)) _]
  simp
end Comparison
open LatticeConventions in
theorem oneStepEnergyMomentumLink (hcone : LatticeConventions.LinkConeInequality)
    (hpictures : LatticeConventions.CoordinatePictureOperators)
    (hmatrix : MatrixElementsEqCorrelations)
    (hreads : InfiniteLattice.LinkLocalFunctions.Statement) :
    OneStepEnergyMomentumLink := by
  intro ν μ l
  have : IsProbabilityMeasure (ν : Measure (GaugeField (1 : ℝ))) := ν.2.1
  have hTs : IsSelfAdjoint (ReflectionPair.link.transferOp ν μ) :=
    (ReflectionPair.link.opFamily ν μ).isSelfAdjoint_A
  have hc : Commute (ReflectionPair.link.transferOp ν μ) (ReflectionPair.link.shiftOp ν μ l) :=
    (ReflectionPair.link.opFamily ν μ).commute_A_B l
  generalize hTdef : ReflectionPair.link.transferOp ν μ = T at hTs hc ⊢
  generalize hUdef : ReflectionPair.link.shiftOp ν μ l = U at hc ⊢
  have hcs : Commute T (star U) := by
    have h := congrArg star hc.eq
    simp only [star_mul, hTs.star_eq] at h
    exact h.symm
  have hW : IsSelfAdjoint ((2 : ℂ) • (1 : ReflectionPair.link.Hilb ν μ →L[ℂ]
      ReflectionPair.link.Hilb ν μ) - U - star U) := by
    rw [isSelfAdjoint_iff]
    simp [star_sub, star_smul, sub_right_comm]
  have hWc : Commute T ((2 : ℂ) • (1 : ReflectionPair.link.Hilb ν μ →L[ℂ]
      ReflectionPair.link.Hilb ν μ) - U - star U) :=
    (((Commute.one_right T).smul_right (2 : ℂ)).sub_right hc).sub_right hcs
  have hA : IsSelfAdjoint ((1 - T) ^ 2) := ((IsSelfAdjoint.one _).sub hTs).pow 2
  have hB := (IsSelfAdjoint.commute_iff hTs hW).mp hWc
  refine ⟨hA, hB, (FormHilbert.le_iff_inner_sub_nonneg hA hB).mpr fun ψ => ?_⟩
  have hdense : DenseRange (FormHilbert.formClass (ReflectionPair.link.pairForm ν μ)) :=
    UniformSpace.Completion.denseRange_coe
      (α := FormHilbert.FormSeminormed (ReflectionPair.link.pairForm ν μ))
  refine hdense.induction_on (p := fun ψ => 0 ≤ inner ℂ ψ
    (((1 - T) ^ 2 - T * ((2 : ℂ) • 1 - U - star U) : _ →L[ℂ] _) ψ)) ψ ?_ ?_
  · exact isClosed_le continuous_const (by fun_prop)
  rintro ⟨F, hF⟩
  have hcl : FormHilbert.formClass (ReflectionPair.link.pairForm ν μ) ⟨F, hF⟩ =
      ReflectionPair.link.obsClass ν μ F := by
    rw [ReflectionPair.obsClass, dif_pos hF]
  change 0 ≤ inner ℂ (FormHilbert.formClass (ReflectionPair.link.pairForm ν μ) ⟨F, hF⟩)
    (((1 - T) ^ 2 - T * ((2 : ℂ) • 1 - U - star U) : _ →L[ℂ] _)
      (FormHilbert.formClass (ReflectionPair.link.pairForm ν μ) ⟨F, hF⟩))
  rw [hcl]
  let R : ℕ → ℤ → ℂ := fun n y => ∫ x, conj ((linkReflect μ).actOn F x) *
    (shift (n • axisStep 1 μ + y • axisStep 1 l.1)).actOn F x
      ∂(ν : Measure (GaugeField (1 : ℝ)))
  have hL : ∀ (n : ℕ) (y : ℤ), inner ℂ (ReflectionPair.link.obsClass ν μ F)
      ((T ^ n * ReflectionPair.link.shiftMonomial ν μ (Pi.single l.1 y))
        (ReflectionPair.link.obsClass ν μ F)) = R n y := fun n y => by
    rw [← hTdef]
    have h := (hmatrix ν μ F hF F hF n (Pi.single l.1 y) (Pi.single_eq_of_ne l.2.symm _)).1
    rw [intPoint_single] at h
    exact h
  have hP0 : ReflectionPair.link.shiftMonomial ν μ (Pi.single l.1 0) = 1 := by
    rw [shiftMonomial_single, zpow_zero]
    rfl
  have hP1 : ReflectionPair.link.shiftMonomial ν μ (Pi.single l.1 1) = U := by
    rw [shiftMonomial_single, zpow_one]
    exact hUdef
  have hPm : ReflectionPair.link.shiftMonomial ν μ (Pi.single l.1 (-1)) = star U := by
    rw [shiftMonomial_single, zpow_neg_one, ← hUdef]
    rfl
  have e₁ := inner_one_sub_sq_sub_mul T U (star U)
    (fun y => ReflectionPair.link.shiftMonomial ν μ (Pi.single l.1 y)) hP0 hP1 hPm
    (ReflectionPair.link.obsClass ν μ F)
  have hst : LinkFrame.IsAdmissibleState unitSpacing μ (ν : Measure (GaugeField (1 : ℝ))) :=
    ⟨ν.2.2.1, fun _ => isReflectionPositiveAcrossMirror_of_mem ν.2 _⟩
  obtain ⟨-, -, -, hun, -, -, -, hme⟩ := (hpictures unitSpacing μ ν.1 hst).2.1
  have habove := (hcone unitSpacing μ l.1 l.2.symm _
    (pairConditions_of_mem ν.2 l.2.symm)).1
  let G : LinkFrame.upperAlgebra unitSpacing μ := ⟨F, mem_upperAlgebra_of_mem hreads hF⟩
  have hR : ∀ (n : ℕ) (y : ℤ), inner ℂ (LinkFrame.linkClass unitSpacing μ ν.1 G)
      ((LinkFrame.transferOperator unitSpacing μ ν.1 ^ n *
        zpowOp (LinkFrame.transverseShift unitSpacing μ ν.1 l) y)
        (LinkFrame.linkClass unitSpacing μ ν.1 G)) = R n y := fun n y => by
    have h := hme G G l n y
    rw [linkReflection_unitSpacing μ] at h
    exact h
  have e₂ := inner_one_sub_sq_sub_mul (LinkFrame.transferOperator unitSpacing μ ν.1)
    (LinkFrame.transverseShift unitSpacing μ ν.1 l)
    (ContinuousLinearMap.adjoint (LinkFrame.transverseShift unitSpacing μ ν.1 l))
    (zpowOp (LinkFrame.transverseShift unitSpacing μ ν.1 l))
    (ContractionUnitary.zpowOp_zero _)
    (by simp [zpowOp]) (adjoint_eq_zpowOp_neg_one (hun l)).symm
    (LinkFrame.linkClass unitSpacing μ ν.1 G)
  have h₀ : 0 ≤ inner ℂ (LinkFrame.linkClass unitSpacing μ ν.1 G)
      (((1 - LinkFrame.transferOperator unitSpacing μ ν.1) ^ 2 -
        LinkFrame.transferOperator unitSpacing μ ν.1 *
          ((2 : ℂ) • 1 - LinkFrame.transverseShift unitSpacing μ ν.1 l -
            ContinuousLinearMap.adjoint (LinkFrame.transverseShift unitSpacing μ ν.1 l)) : _ →L[ℂ] _)
        (LinkFrame.linkClass unitSpacing μ ν.1 G)) := by
    rw [sub_apply, inner_sub_right]
    exact sub_nonneg.mpr (habove.le _)
  rw [e₂] at h₀
  simp only [hR] at h₀
  rw [e₁]
  simp only [hL]
  exact h₀
end YangMills.Construction.ReflectionPositivity.DirectionPictures.EnergyMomentumOneStep
