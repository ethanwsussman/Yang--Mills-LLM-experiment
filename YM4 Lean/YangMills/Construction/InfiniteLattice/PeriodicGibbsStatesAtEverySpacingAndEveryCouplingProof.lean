import YangMills.Construction.InfiniteLattice.WhatIsReadOfAPeriodicGibbsStateProof
import YangMills.Construction.InfiniteLattice.PeriodicExtensionInAWindow
import YangMills.Construction.InfiniteLattice.PeriodicGibbsStatesAtASpacing
import YangMills.Construction.InfiniteLattice.PeriodicGibbsStatesAtEverySpacingAndEveryCoupling
import YangMills.Construction.InfiniteLattice.PropertiesOfTheWilsonKernelOnObservables
import YangMills.Construction.InfiniteLattice.StatesDeterminedByContinuousLocalFunctions
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped NNReal ComplexOrder ComplexConjugate Matrix
noncomputable section
namespace YangMills.Construction.InfiniteLattice.PeriodicStatesAllScales
open SingleMeshMirrors LatticeConventions
variable {a : ℝ} {L K : ℕ}
theorem compactSpace_gaugeField : CompactSpace (GaugeField a) := by
  have hc : IsClosed {U : Link a → Matrices.ComplexMatrix2.specialUnitary |
      ∀ e, U e.opposite = (U e)⁻¹} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun e => isClosed_eq (continuous_apply _) (continuous_apply e).inv
  exact isCompact_iff_compactSpace.mp hc.isCompact
theorem isBoundedObservable_of_continuous {F : GaugeField a → ℂ} (hF : Continuous F) :
    IsBoundedObservable F := by
  have := compactSpace_gaugeField (a := a)
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hF.continuousOn
  exact ⟨hF.measurable, C, fun U => hC U (Set.mem_univ U)⟩
theorem continuous_expect {F : GaugeField a → ℂ} (hF : Continuous F) :
    Continuous fun μ : GaugeFieldProbability a => μ.expect F := by
  have := compactSpace_gaugeField (a := a)
  let G : BoundedContinuousFunction (GaugeField a) ℂ :=
    BoundedContinuousFunction.mkOfCompact ⟨F, hF⟩
  exact show Continuous fun μ : GaugeFieldProbability a => μ.expect G from
    continuous_iInf_dom (i := G) continuous_induced_dom
theorem dependsOnlyOnLinks_mono {S T : Set (Link a)} (h : S ⊆ T) {F : GaugeField a → ℂ}
    (hF : DependsOnlyOnLinks S F) : DependsOnlyOnLinks T F :=
  fun U U' e => hF U U' (funext fun l => congrFun e ⟨l.1, h l.2⟩)
theorem isPeriodicMeasure_of_shift_invariant {μ : Measure (GaugeField a)}
    (h : ∀ v : LatticePoint a, IsSymmetricUnder μ (shift v)) : IsPeriodicMeasure μ :=
  ⟨⊤, inferInstance, fun v _ => h v⟩
theorem expect_eq_of_eventually_eq_lifts {β : ℝ}
    {μ : GaugeFieldProbability (PeriodicLattice.meshSize L (K : ℤ))}
    (hμ : μ ∈ weakClusterPointsOfLifts L K β)
    {F₁ F₂ : GaugeField (PeriodicLattice.meshSize L (K : ℤ)) → ℂ}
    (h₁ : Continuous F₁) (h₂ : Continuous F₂) (ℓ₀ : ℝ)
    (h : ∀ m : ℕ, 0 < m → ℓ₀ ≤ PeriodicLattice.torusSide L m →
      ∫ U, F₁ U ∂liftedWilsonMeasure L m K β = ∫ U, F₂ U ∂liftedWilsonMeasure L m K β) :
    μ.expect F₁ = μ.expect F₂ := by
  by_contra hne
  have hO : IsOpen {ρ : GaugeFieldProbability (PeriodicLattice.meshSize L (K : ℤ)) |
      ρ.expect F₁ ≠ ρ.expect F₂} :=
    isOpen_ne_fun (continuous_expect h₁) (continuous_expect h₂)
  obtain ⟨m, hm, hℓ, ρ, hρ, hρ₁⟩ := hμ _ hO hne ℓ₀
  apply hρ
  have e := h m hm hℓ
  rw [← hρ₁] at e
  exact e
abbrev standingParamsOf (hL : Odd L) (h13 : 13 ≤ L) (hK : 0 < K) {m : ℕ} (hm : 0 < m) :
    Conventions.StandingParameters :=
  ⟨L, ⟨hL, h13⟩, ⟨K, hK⟩, ⟨m, hm⟩⟩
theorem isGibbs_of_mem_clusterPoints (hKer : WilsonOperatorProperties)
    (hLift : PeriodicLift.Statement) (hL : Odd L) (h13 : 13 ≤ L) (hK : 0 < K)
    {β : ℝ} (hβ : 0 < β) {μ : GaugeFieldProbability (PeriodicLattice.meshSize L (K : ℤ))}
    (hμ : μ ∈ weakClusterPointsOfLifts L K β) : IsGibbs β μ.1 := by
  classical
  have ha : 0 < PeriodicLattice.meshSize L (K : ℤ) :=
    PeriodicLift.meshSize_pos (standingParamsOf hL h13 hK one_pos)
  have hkern := hKer L K hL h13 hK ha β hβ
  refine (List.TFAE.out (hkern.2.2 μ) 2 0).mp ?_
  intro Λ hΛ F hF
  have hops := hkern.1 Λ hΛ
  have hFc : Continuous F := hF.1
  obtain ⟨W, hWfin, hWpos, hFW⟩ := hF.2
  have hfinE := WilsonOperator.thickenedLinks_finite Λ
  let S : Finset (Link (PeriodicLattice.meshSize L (K : ℤ))) := hWfin.toFinset ∪ hfinE.toFinset
  have hES : WilsonOperator.thickenedLinks Λ ⊆ (S : Set _) := fun l hl => by
    simp only [S, Finset.coe_union, Set.Finite.coe_toFinset]
    exact Or.inr hl
  have hWS : W ⊆ (S : Set _) := fun l hl => by
    simp only [S, Finset.coe_union, Set.Finite.coe_toFinset]
    exact Or.inl hl
  have hΛS : (Λ : Set (Link (PeriodicLattice.meshSize L (K : ℤ)))) ⊆ S :=
    fun l hl => hES (Or.inl hl)
  have hSpos : (S : Set (Link (PeriodicLattice.meshSize L (K : ℤ)))) ⊆
      positiveLinkSet (PeriodicLattice.meshSize L (K : ℤ)) := by
    simp only [S, Finset.coe_union, Set.Finite.coe_toFinset]
    exact Set.union_subset hWpos (WilsonOperator.thickenedLinks_subset hΛ)
  have hγc : Continuous (WilsonOperator.kernelOperator ha β hΛ F) :=
    (hops.2.2.kernel_mem_continuousCylinderFunctions F hF).1
  refine expect_eq_of_eventually_eq_lifts hμ hγc hFc
    (PeriodicLift.endpointDiameter S + 1) fun m hm hℓ => ?_
  exact (hLift (standingParamsOf hL h13 hK hm) β hβ).2.2 Λ S hΛS hSpos hES
    (lt_of_lt_of_le (lt_add_one _) hℓ) F (isBoundedObservable_of_continuous hFc)
    (dependsOnlyOnLinks_mono hWS hFW)
theorem isSymmetricUnder_shift_of_mem_clusterPoints
    (hStates : CylinderFunctionsDetermineStates.Statement)
    (hLift : PeriodicLift.Statement) (hL : Odd L) (h13 : 13 ≤ L) (hK : 0 < K)
    {β : ℝ} (hβ : 0 < β) {μ : GaugeFieldProbability (PeriodicLattice.meshSize L (K : ℤ))}
    (hμ : μ ∈ weakClusterPointsOfLifts L K β)
    (v : LatticePoint (PeriodicLattice.meshSize L (K : ℤ))) : IsSymmetricUnder μ.1 (shift v) := by
  have hs := (hStates L K hL h13 hK).2.1 (shift v)
  refine hs.2.2 μ fun F hF => ?_
  refine expect_eq_of_eventually_eq_lifts hμ (hs.1 F hF.1) hF.1 0 fun m hm _ => ?_
  exact (hLift (standingParamsOf hL h13 hK hm) β hβ).2.1 v F (isBoundedObservable_of_continuous hF.1)
theorem realNormal_axial_or_diagonal (C : ReflectionClass) :
    IsAxialNormal C.realNormal ∨ IsFaceDiagonalNormal C.realNormal := by
  cases C with
  | axial μ =>
    refine Or.inl ⟨μ, ?_⟩
    funext κ
    by_cases h : κ = μ
    · subst h
      simp [ReflectionClass.realNormal, ReflectionClass.intNormal, _root_.YangMills.Construction.LatticeConventions.basisVector]
    · simp [ReflectionClass.realNormal, ReflectionClass.intNormal, _root_.YangMills.Construction.LatticeConventions.basisVector,
        Pi.single_eq_of_ne h]
  | diagonal μ ν lt s =>
    refine Or.inr ⟨μ, ν, lt.ne, ?_⟩
    rcases Int.units_eq_one_or s with rfl | rfl
    · left
      funext κ
      simp only [ReflectionClass.realNormal, ReflectionClass.intNormal, _root_.YangMills.Construction.LatticeConventions.basisVector, Pi.add_apply,
        Pi.smul_apply, Pi.single_apply]
      split_ifs <;> simp <;> norm_num
    · right
      funext κ
      simp only [ReflectionClass.realNormal, ReflectionClass.intNormal, _root_.YangMills.Construction.LatticeConventions.basisVector, Pi.sub_apply,
        Pi.add_apply, Pi.smul_apply, Pi.single_apply]
      split_ifs <;> simp
def toNormalHyperplane (Q : LatticeMirror a) : NormalHyperplane where
  normal := Q.cls.realNormal
  level := Q.level
  normal_valid := realNormal_axial_or_diagonal Q.cls
theorem isLatticeMirror_toNormalHyperplane (Q : LatticeMirror a) :
    (toNormalHyperplane Q).IsLatticeMirror a := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodicGibbsConsequences.normalHyperplane_isLatticeMirror <;> assumption
theorem latticeSymmetry_eq_of_toFun_eq {r s : LatticeSymmetry a} (h : r.toFun = s.toFun) :
    r = s := by
  cases r
  cases s
  cases h
  rfl
theorem reflectSymmetry_toNormalHyperplane (Q : LatticeMirror a) :
    NormalHyperplane.reflectSymmetry (isLatticeMirror_toNormalHyperplane Q) = Q.symmetry :=
  latticeSymmetry_eq_of_toFun_eq
    (NormalHyperplane.reflect_eq_hyperplaneReflect (toNormalHyperplane Q))
theorem hasSymmetriesAndPositivity (hSpacing : PeriodicGibbsAtSpacing.Statement)
    (ha : 0 < PeriodicLattice.meshSize L (K : ℤ)) {β : ℝ} (hβ : 0 < β)
    {μ : GaugeFieldProbability (PeriodicLattice.meshSize L (K : ℤ))}
    (hμ : μ ∈ periodicGibbsStates L K β) : HasSymmetriesAndPositivity μ := by
  have hprob : IsProbabilityMeasure μ.1 := μ.2
  have hp := (hSpacing _ ha β hβ).1 μ.1 hμ
  refine ⟨hp.1, hp.2.1, fun Q => ?_⟩
  have hq := hp.2.2 (toNormalHyperplane Q) (isLatticeMirror_toNormalHyperplane Q)
  have hprod : ∀ F : GaugeField (PeriodicLattice.meshSize L (K : ℤ)) → ℂ,
      PeriodicGibbsAtSpacing.mirrorPairing (isLatticeMirror_toNormalHyperplane Q) F =
        fun U => LatticeMirror.conjReflect Q F U * F U := by
    intro F
    funext U
    change conj ((NormalHyperplane.reflectSymmetry
      (isLatticeMirror_toNormalHyperplane Q)).actOn F U) * F U =
        conj (Q.symmetry.actOn F U) * F U
    rw [reflectSymmetry_toNormalHyperplane]
  refine ⟨?_, ?_⟩
  · have h := hq.1
    rw [reflectSymmetry_toNormalHyperplane] at h
    exact h
  · intro H hH F hF hFH
    rcases (hH : LatticeMirror.IsHalfSpace Q H) with rfl | rfl
    · have h := hq.2.1 F (And.intro hF hFH : IsBoundedObservable F ∧ IsRegionMeasurable _ F)
      rw [hprod] at h
      exact h
    · have h := hq.2.2.1 F (And.intro hF hFH : IsBoundedObservable F ∧ IsRegionMeasurable _ F)
      rw [hprod] at h
      exact h
theorem periodicGibbsStates_eq (hSpacing : PeriodicGibbsAtSpacing.Statement)
    (ha : 0 < PeriodicLattice.meshSize L (K : ℤ)) {β : ℝ} (hβ : 0 < β) :
    periodicGibbsStates L K β = {μ | IsShiftInvariantGibbs β μ} := by
  ext μ
  constructor
  · intro hμ
    exact ⟨hμ.1, (hasSymmetriesAndPositivity hSpacing ha hβ hμ).1⟩
  · intro hμ
    exact ⟨hμ.1, isPeriodicMeasure_of_shift_invariant hμ.2⟩
theorem isClosed_shiftInvariantGibbs (hKer : WilsonOperatorProperties)
    (hStates : CylinderFunctionsDetermineStates.Statement) (hL : Odd L) (h13 : 13 ≤ L)
    (hK : 0 < K) (ha : 0 < PeriodicLattice.meshSize L (K : ℤ)) {β : ℝ} (hβ : 0 < β) :
    IsClosed {μ : GaugeFieldProbability (PeriodicLattice.meshSize L (K : ℤ)) |
      IsShiftInvariantGibbs β μ} := by
  have hkern := hKer L K hL h13 hK ha β hβ
  have hs := (hStates L K hL h13 hK).2.1
  have hset : {μ : GaugeFieldProbability (PeriodicLattice.meshSize L (K : ℤ)) |
      IsShiftInvariantGibbs β μ} =
      (⋂ (Λ : Finset (Link (PeriodicLattice.meshSize L (K : ℤ))))
        (hΛ : (Λ : Set (Link (PeriodicLattice.meshSize L (K : ℤ)))) ⊆
          positiveLinkSet (PeriodicLattice.meshSize L (K : ℤ)))
        (F : GaugeField (PeriodicLattice.meshSize L (K : ℤ)) → ℂ)
        (_ : F ∈ continuousCylinderFunctions (PeriodicLattice.meshSize L (K : ℤ))),
        {μ | μ.expect (WilsonOperator.kernelOperator ha β hΛ F) = μ.expect F}) ∩
      ⋂ (v : LatticePoint (PeriodicLattice.meshSize L (K : ℤ)))
        (F : GaugeField (PeriodicLattice.meshSize L (K : ℤ)) → ℂ)
        (_ : F ∈ continuousCylinderFunctions (PeriodicLattice.meshSize L (K : ℤ))),
        {μ | μ.expect ((shift v).actOn F) = μ.expect F} := by
    ext μ
    simp only [Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · intro hμ
      refine ⟨fun Λ hΛ F hF => ?_, fun v F hF => ?_⟩
      · have hout := List.TFAE.out (hkern.2.2 μ) 0 2
        exact hout.mp hμ.1 Λ hΛ F hF
      · exact hμ.2 v F (isBoundedObservable_of_continuous hF.1)
    · rintro ⟨h₁, h₂⟩
      have hout := List.TFAE.out (hkern.2.2 μ) 2 0
      exact ⟨hout.mp fun Λ hΛ F hF => h₁ Λ hΛ F hF,
        fun v => (hs (shift v)).2.2 μ fun F hF => h₂ v F hF⟩
  rw [hset]
  refine IsClosed.inter ?_ ?_
  · refine isClosed_iInter fun Λ => isClosed_iInter fun hΛ => isClosed_iInter fun F =>
      isClosed_iInter fun hF => ?_
    exact isClosed_eq
      (continuous_expect ((hkern.1 Λ hΛ).2.2.kernel_mem_continuousCylinderFunctions F hF).1)
      (continuous_expect hF.1)
  · refine isClosed_iInter fun v => isClosed_iInter fun F => isClosed_iInter fun hF => ?_
    exact isClosed_eq (continuous_expect ((hs (shift v)).1 F hF.1))
      (continuous_expect hF.1)
theorem allScalesAllCouplings_holds (hSpacing : PeriodicGibbsAtSpacing.Statement)
    (hLift : PeriodicLift.Statement)
    (hKer : WilsonOperatorProperties)
    (hStates : CylinderFunctionsDetermineStates.Statement) : AllScalesAllCouplings := by
  intro L K hL h13 hK β hβ
  have ha : 0 < PeriodicLattice.meshSize L (K : ℤ) :=
    PeriodicLift.meshSize_pos (standingParamsOf hL h13 hK one_pos)
  have hset := (hSpacing _ ha β hβ).2.2.2
  have hlim : ∀ μ ∈ weakClusterPointsOfLifts L K β, IsShiftInvariantGibbs β μ :=
    fun μ hμ => ⟨isGibbs_of_mem_clusterPoints hKer hLift hL h13 hK hβ hμ,
      isSymmetricUnder_shift_of_mem_clusterPoints hStates hLift hL h13 hK hβ hμ⟩
  have himage : (fun μ : GaugeFieldProbability (PeriodicLattice.meshSize L (K : ℤ)) => μ.1) ''
      periodicGibbsStates L K β =
      {μ : Measure (GaugeField (PeriodicLattice.meshSize L (K : ℤ))) |
        IsPeriodicGibbs β μ} := by
    ext ρ
    constructor
    · rintro ⟨μ, hμ, rfl⟩
      exact hμ
    · intro h
      exact ⟨⟨ρ, h.1.1⟩, h, rfl⟩
  have hcompact : CompactSpace (GaugeFieldProbability (PeriodicLattice.meshSize L (K : ℤ))) :=
    (hStates L K hL h13 hK).2.2
  refine ⟨fun μ hμ => hasSymmetriesAndPositivity hSpacing ha hβ hμ,
    ⟨periodicGibbsStates_eq hSpacing ha hβ, ?_, ?_, ?_⟩, hlim, ?_⟩
  · obtain ⟨ρ, hρ⟩ := hset.2.1
    exact ⟨⟨ρ, hρ.1.1⟩, hρ⟩
  · rw [himage]
    exact hset.2.2.1
  · rw [periodicGibbsStates_eq hSpacing ha hβ]
    exact (isClosed_shiftInvariantGibbs hKer hStates hL h13 hK ha hβ).isCompact
  · intro μ hμ
    rw [periodicGibbsStates_eq hSpacing ha hβ]
    exact hlim μ hμ
end YangMills.Construction.InfiniteLattice.PeriodicStatesAllScales
end
