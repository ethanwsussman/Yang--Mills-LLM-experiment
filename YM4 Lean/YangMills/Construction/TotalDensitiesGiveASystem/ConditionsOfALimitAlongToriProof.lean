import YangMills.Construction.Continuum.TheRecursionOfTheConnectedFunctionsIsTriangularProof
import YangMills.Construction.QuaternionicWilsonModel.TheLimitsOfTheTopAreRealAndNotZeroProof
import YangMills.Construction.QuaternionicWilsonModel.WhatTheTopGivesAtEveryCouplingProof
import YangMills.Construction.Continuum.ConnectedFunctionsAndCentredFunctionalOfAFunctional
import YangMills.Construction.LawThroughTheLevels.PairOfTheClassIsOfTestFunctions
import YangMills.Construction.LimitTheorem.RepresentativeAndTheIdentifications
import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPair
import YangMills.Construction.TotalDensitiesGiveASystem.ConditionsOfALimitAlongTori
import YangMills.Construction.TotalDensitiesGiveASystem.GlueAtDrawnParameters
import YangMills.Construction.TotalDensitiesGiveASystem.GrowthOfAFamilyWithAPowerBound
import YangMills.Construction.TotalDensitiesGiveASystem.PerBallBoundOfALimitAlongTori
import YangMills.Construction.TotalDensitiesGiveASystem.TheLawsAtEveryShape
import YangMills.Construction.TotalDensitiesGiveASystem.ThePowerBoundAtTheData
import YangMills.Construction.TotalDensitiesGiveASystem.WeightedNormsGrowWithTheirIndex
import YangMills.Construction.TwoPoints.PartsOfATestPlate
import YangMills.Construction.TwoPoints.ShapeConstantInTheUnitInterval
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.TotalDensities.LimitAlongToriProof
section Auxiliary
open scoped ComplexOrder ENNReal InnerProductSpace NNReal
section PositiveForm
variable (σ : SeparatedTuples.TupleFunctional)
  (hσ : HilbertSpaceBasics.IsPosSemidef (ReflectionPositivity.TupleForm.reflectionForm σ))
private theorem reflectionForm_posTupleVec
    (X Y : SeparatedTuples.supportedIn TimeAxis.upperHalfSpace) :
    ReflectionPositivity.TupleForm.reflectionForm σ (ReflectionPositivity.Reconstruction.posTupleVec X)
        (ReflectionPositivity.Reconstruction.posTupleVec Y) =
      (σ (SeparatedTuples.SepTuple.juxt (SeparatedTuples.push TimeAxis.timeReflection X.1) Y.1) : ℂ) := by
  simp only [ReflectionPositivity.TupleForm.reflectionForm, ReflectionPositivity.TupleForm.reflectConj,
    ReflectionPositivity.Reconstruction.posTupleVec, SeparatedTuples.conjugation_basisVec,
    SeparatedTuples.pushSpan, SeparatedTuples.linearExtend_basisVec, SeparatedTuples.formalMul_basisVec,
    SeparatedTuples.TupleFunctional.spanExtension]
private theorem inner_posClass (F G : ReflectionPositivity.TupleForm.PositiveSpan) :
    ⟪ReflectionPositivity.Reconstruction.posClass σ hσ F, ReflectionPositivity.Reconstruction.posClass σ hσ G⟫_ℂ =
      ReflectionPositivity.TupleForm.reflectionForm σ F G :=
  UniformSpace.Completion.inner_coe (𝕜 := ℂ)
    (E := HilbertSpaceBasics.FormSpace (ReflectionPositivity.TupleForm.reflectionForm σ) hσ) F G
end PositiveForm
private theorem timeReflection_involutive : Function.Involutive TimeAxis.timeReflection := fun x => by
  funext μ
  fin_cases μ <;> simp [TimeAxis.timeReflection]
private theorem invMap_timeReflection :
    SeparatedTuples.invMap TimeAxis.timeReflection = TimeAxis.timeReflection :=
  funext fun x => by
    have hx := Function.leftInverse_invFun timeReflection_involutive.injective (TimeAxis.timeReflection x)
    rwa [timeReflection_involutive x] at hx
private theorem continuous_timeReflection : Continuous TimeAxis.timeReflection := by
  refine continuous_pi fun μ => ?_
  fin_cases μ <;> simp [TimeAxis.timeReflection] <;> fun_prop
private def timeReflectionHomeomorph : (Fin 4 → ℝ) ≃ₜ (Fin 4 → ℝ) where
  toFun := TimeAxis.timeReflection
  invFun := TimeAxis.timeReflection
  left_inv := timeReflection_involutive
  right_inv := timeReflection_involutive
  continuous_toFun := continuous_timeReflection
  continuous_invFun := continuous_timeReflection
private theorem tsupport_comp_timeReflection (f : SeparatedTuples.RealValued) :
    tsupport (f ∘ TimeAxis.timeReflection) = TimeAxis.timeReflection ⁻¹' tsupport f :=
  tsupport_comp_eq_preimage f timeReflectionHomeomorph
private theorem contDiff_timeReflection : ContDiff ℝ 1 TimeAxis.timeReflection := by
  refine contDiff_pi.2 fun μ => ?_
  fin_cases μ <;> simp [TimeAxis.timeReflection] <;> fun_prop
private theorem isDisjointlySupported_pushList_timeReflection (X : SeparatedTuples.SepTuple) :
    SeparatedTuples.IsDisjointlySupported (SeparatedTuples.pushList TimeAxis.timeReflection X.1) := by
  simp only [SeparatedTuples.pushList, invMap_timeReflection]
  refine ⟨fun g hg => ?_, ?_⟩
  · obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
    have hfX := X.2.1 f hf
    exact ⟨ContDiff.comp hfX.1 contDiff_timeReflection, hfX.2.comp_homeomorph timeReflectionHomeomorph⟩
  · refine List.pairwise_map.2 (X.2.2.imp fun {f g} hd => ?_)
    rw [tsupport_comp_timeReflection, tsupport_comp_timeReflection]
    exact hd.preimage _
private theorem push_timeReflection_val (X : SeparatedTuples.SepTuple) :
    (SeparatedTuples.push TimeAxis.timeReflection X).1 = X.1.map fun f => f ∘ TimeAxis.timeReflection := by
  unfold SeparatedTuples.push
  rw [dif_pos (isDisjointlySupported_pushList_timeReflection X)]
  simp [SeparatedTuples.pushList, invMap_timeReflection]
private theorem composable_push_timeReflection {X Y : SeparatedTuples.SepTuple}
    (hX : X ∈ SeparatedTuples.supportedIn TimeAxis.upperHalfSpace)
    (hY : Y ∈ SeparatedTuples.supportedIn TimeAxis.upperHalfSpace) :
    SeparatedTuples.SepTuple.Composable (SeparatedTuples.push TimeAxis.timeReflection X) Y := by
  intro g hg k hk
  rw [push_timeReflection_val] at hg
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
  rw [tsupport_comp_timeReflection]
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  have h₁ : 0 < TimeAxis.timeReflection x 3 := hX f hf hx
  have h₂ : 0 < x 3 := hY k hk hx'
  simp [TimeAxis.timeReflection] at h₁
  linarith
private theorem juxt_timeReflection_val {A B : SeparatedTuples.SepTuple} {k : ℕ}
    (a b : Fin k → SeparatedTuples.RealValued)
    (hA : A.1 = List.ofFn a) (hB : B.1 = List.ofFn b)
    (hA' : A ∈ SeparatedTuples.supportedIn TimeAxis.upperHalfSpace)
    (hB' : B ∈ SeparatedTuples.supportedIn TimeAxis.upperHalfSpace) :
    (SeparatedTuples.SepTuple.juxt (SeparatedTuples.push TimeAxis.timeReflection A) B).1 =
      List.ofFn (Fin.append (fun i => a i ∘ TimeAxis.timeReflection) b) := by
  rw [SeparatedTuples.SepTuple.juxt_val (composable_push_timeReflection hA' hB'), push_timeReflection_val,
    hA, hB, List.ofFn_fin_append, List.map_ofFn]
  rfl
private theorem hasReconstruction_of_properties {σ : SeparatedTuples.TupleFunctional}
    (hl : LimitTheorem.ReconstructionProperties σ)
    (p : HilbertSpaceBasics.IsPosSemidef (ReflectionPositivity.TupleForm.reflectionForm σ)) :
    LimitTheorem.HasReconstruction σ p := by
  obtain ⟨-, -, q, hq, -⟩ := hl
  exact hq
private theorem evalOnMap_centredOf (S : LimitTheorem.CumulantFamily) (X : TestSpaces.SepTuple) :
    LimitTheorem.evalOnMap (LimitTheorem.centredOf S) X = TestSpaces.centredOfCumulants S X := by
  show TestSpaces.centredOfCumulants S (TupleLists.ofList (TupleLists.toList X)) = _
  rw [TupleLists.ofList_toList]
private theorem centredOfCumulants_two (S : LimitTheorem.CumulantFamily) (X : TestSpaces.SepTupleOfCard 2) :
    TestSpaces.centredOfCumulants S ⟨2, X⟩ = S 2 le_rfl X := by apply _root_.YangMills.Construction.TestSpaces.RecursionTriangular.centredOfCumulants_pair <;> assumption
private theorem two_le_rank_physicalSpace {σ : SeparatedTuples.TupleFunctional}
    (p : HilbertSpaceBasics.IsPosSemidef (ReflectionPositivity.TupleForm.reflectionForm σ))
    (hR : LimitTheorem.HasReconstruction σ p)
    (X : SeparatedTuples.supportedIn TimeAxis.upperHalfSpace) (h0 : σ X.1 = 0)
    (hpos : 0 < σ (SeparatedTuples.SepTuple.juxt (SeparatedTuples.push TimeAxis.timeReflection X.1) X.1)) :
    2 ≤ Module.rank ℂ (ReflectionPositivity.Reconstruction.PhysicalSpace σ p) := by
  obtain ⟨⟨-, hn, hX⟩, -⟩ := hR
  set u := ReflectionPositivity.Reconstruction.posClass σ p (ReflectionPositivity.Reconstruction.posTupleVec X)
    with hu
  have huΩ : ⟪u, ReflectionPositivity.Reconstruction.vacuum σ p⟫_ℂ = 0 := by
    rw [hu, (hX X).1, h0]
    simp
  have huu : ⟪u, u⟫_ℂ =
      ((σ (SeparatedTuples.SepTuple.juxt (SeparatedTuples.push TimeAxis.timeReflection X.1) X.1) : ℝ) : ℂ) := by
    rw [hu, inner_posClass, reflectionForm_posTupleVec]
  have hu0 : ⟪u, u⟫_ℂ ≠ 0 := by
    rw [huu]
    exact_mod_cast hpos.ne'
  have hΩ0 : ReflectionPositivity.Reconstruction.vacuum σ p ≠ 0 := fun e => by
    rw [e, norm_zero] at hn
    exact zero_ne_one hn
  have hli : LinearIndependent ℂ ![ReflectionPositivity.Reconstruction.vacuum σ p, u] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have e₁ := congrArg (fun y => ⟪u, y⟫_ℂ) hst
    simp only [inner_add_right, inner_smul_right, huΩ, inner_zero_right, mul_zero, zero_add] at e₁
    have ht : t = 0 := (mul_eq_zero.1 e₁).resolve_right hu0
    subst ht
    simp only [zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.1 hst).resolve_right hΩ0, rfl⟩
  have hcard := hli.cardinal_le_rank
  simpa using hcard
private theorem reflectAcross_coordVec_three :
    TwoPoints.reflectAcross (PeriodicLattice.coordVec 3) = TimeAxis.timeReflection := by
  funext x
  ext μ
  fin_cases μ <;>
    simp [TwoPoints.reflectAcross, TwoPoints.euclidDot, TimeAxis.timeReflection,
      PeriodicLattice.coordVec, Fin.sum_univ_four] <;> ring
private theorem exists_reflected_pair (hPl : TwoPoints.TestPlates.TestPlatePieces.Statement) {ϖ : ℝ}
    (hϖ : 0 < ϖ) (hϖ4 : ϖ ≤ 4) :
    ∃ f : InfiniteLattice.AmbientSpace → ℝ,
      (f ∘ TimeAxis.timeReflection, f) ∈ TestFunctions.separatedPairsR4 (5 / 2 * ϖ) TwoPoints.Shapes.shapeConst ∧
      ContDiff ℝ 1 f ∧ ContDiff ℝ 1 (f ∘ TimeAxis.timeReflection) ∧ tsupport f ⊆ TimeAxis.upperHalfSpace := by
  let b : ContDiffBump (0 : Fin 2 → ℝ) := ⟨1, 2, one_pos, by norm_num⟩
  let φ : (Fin 2 → ℝ) → ℂ := fun ζ => ((b ζ : ℝ) : ℂ)
  have hφs : tsupport φ ⊆ tsupport b := closure_mono fun ζ hζ hb => hζ (by simp [φ, hb])
  have hbt : tsupport b ⊆ Metric.closedBall 0 2 := by
    rw [b.tsupport_eq]
  have hφ : φ ∈ TwoPoints.transProfiles :=
    ⟨⟨Complex.ofRealCLM.contDiff.comp b.contDiff, b.hasCompactSupport.isCompact.of_isClosed_subset
      (isClosed_tsupport _) hφs, Set.subset_univ _⟩, fun ζ => by simp [φ]⟩
  have hset : TwoPoints.TestPlates.PlateHypotheses φ 4 ϖ 1 := by
    refine ⟨hφ, ⟨0, by simp [φ, b.one_of_mem_closedBall (Metric.mem_closedBall_self (by norm_num))]⟩, by norm_num,
      fun ζ hζ => ?_, hϖ, hϖ4, ⟨le_rfl, by norm_num⟩⟩
    have h₁ : ‖ζ‖ ≤ 2 := by simpa using hbt (hφs hζ)
    have hc : ∀ i, ζ i ^ 2 ≤ 4 := fun i => by
      have : |ζ i| ≤ 2 := (norm_le_pi_norm ζ i).trans h₁
      nlinarith [abs_nonneg (ζ i), sq_abs (ζ i)]
    show TwoPoints.euclidNorm ζ ≤ 4
    refine Real.sqrt_le_iff.2 ⟨by norm_num, ?_⟩
    rw [Fin.sum_univ_two]
    nlinarith [hc 0, hc 1]
  obtain ⟨hcover, -, -, hdec, hmirror⟩ := hPl φ 4 ϖ 1 hset
  obtain ⟨ι, hι⟩ : (TwoPoints.TestPlates.supportCells ϖ φ).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have h0 : ∀ ι, TwoPoints.TestPlates.cellBump ϖ ι 0 = 0 := fun ι => by
      have hn : ι ∉ TwoPoints.TestPlates.supportCells ϖ φ := by simp [hne]
      have hz : TwoPoints.TestPlates.localizedProfile ϖ φ ι 0 = 0 := by
        by_contra hcon
        exact hn ⟨0, hcon⟩
      have hb0 : φ 0 = 1 := by simp [φ, b.one_of_mem_closedBall (Metric.mem_closedBall_self (by norm_num))]
      simpa [TwoPoints.TestPlates.localizedProfile, hb0] using hz
    have hs := hcover.1 0
    simp only [h0] at hs
    exact zero_ne_one (hasSum_zero.unique hs)
  obtain ⟨⟨⟨p₁, p₂⟩, hp, h₁, h₂⟩, hm, hh, -⟩ := (hmirror ι hι).1
  have hpart := ((hdec.2.2 ι hι).1)
  simp only at hp h₁ h₂
  set h := TwoPoints.TestPlates.upperCellPlate ϖ 1 φ ι with hdef
  have hreal : ∀ x, p₂ x = (h x).re := fun x => by
    rw [← h₂]
    simp [TwoPoints.ofRealFun]
  have hc₂ : ContDiff ℝ 1 p₂ := by
    have : p₂ = fun x => (h x).re := funext hreal
    rw [this]
    exact Complex.reCLM.contDiff.comp hh.1.1
  have hp₁ : p₁ = p₂ ∘ TimeAxis.timeReflection := by
    funext x
    have e := congrFun h₁ x
    rw [← h₂, TwoPoints.reflectFun, reflectAcross_coordVec_three] at e
    exact Complex.ofReal_injective e
  have hsup : tsupport p₂ ⊆ tsupport h := closure_mono fun x hx hz => hx (by
    rw [hreal, show h x = 0 from hz]
    simp)
  refine ⟨p₂, hp₁ ▸ hp, hc₂, ?_, fun x hx => ?_⟩
  · exact hc₂.comp (by
      refine contDiff_pi.2 fun μ => ?_
      fin_cases μ <;> simp [TimeAxis.timeReflection] <;> fun_prop)
  · have h₃ := hpart.2.2 (hsup hx)
    show TimeAxis.timeComponent x > 0
    have : TimeAxis.timeComponent x = x 3 := rfl
    rw [this]
    linarith [h₃.1]
private theorem disjoint_of_setDistR4 {A B : Set InfiniteLattice.AmbientSpace} {d : ℝ} (hd : 0 < d)
    (h : ENNReal.ofReal d ≤ TestFunctions.setDistR4 A B) : Disjoint A B := by apply _root_.YangMills.Construction.NonGaussianLimits.disjoint_of_le_setDistR4 <;> assumption
private theorem pair_mem_disjointSupportTuples (hP : Scales.SeparatedPairsAreTestFunctionsStatement)
    {d ϑ : ℝ} (hd : 0 < d) {f g : InfiniteLattice.AmbientSpace → ℝ}
    (hp : (f, g) ∈ TestFunctions.separatedPairsR4 d ϑ)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    ![f, g] ∈ TestSpaces.disjointSupportTuples (Set.univ : Set (Fin 4 → ℝ)) 2 := by
  obtain ⟨hf', hg'⟩ := hP d ϑ f g hd.le hp
  have hp' := hp
  simp only [TestFunctions.separatedPairsR4, TestFunctions.separatedPairs, Set.mem_ofPred_eq] at hp'
  obtain ⟨-, -, -, -, s, -⟩ := hp'
  have hdis := disjoint_of_setDistR4 hd s
  refine ⟨fun i => ?_, fun i i' hii => ?_⟩
  · fin_cases i
    · exact ⟨hf, hf'.2, Set.subset_univ _⟩
    · exact ⟨hg, hg'.2, Set.subset_univ _⟩
  · fin_cases i <;> fin_cases i'
    · exact absurd rfl hii
    · exact hdis
    · exact hdis.symm
    · exact absurd rfl hii
end Auxiliary
private theorem holdsAtAdmissibleParameters_side_ge {C : RenormalizationStepParameters.ParameterAssignment → ℝ → Prop}
    (h : HoldsAtAdmissibleParameters C) (N : ℕ) :
    HoldsAtAdmissibleParameters fun T y => C T y ∧ N ≤ T.side := by
  obtain ⟨A, hA, g⟩ := h
  refine ⟨{ A with sideFloor := fun a => max (A.sideFloor a) N },
    ⟨hA.property_eventually, hA.rateCeiling_pos, hA.thresholdCeiling_pos⟩, fun T hT hM => ?_⟩
  have m : A.IsMetBy T := ⟨le_trans (le_max_left _ _) hM.side_ge, hM.derivBound_ge, hM.rt_le, hM.threshold_le,
    hM.n₀_ge, hM.Cs_ge, hM.N_ge, hM.holds⟩
  obtain ⟨y₀, f⟩ := g T hT m
  exact ⟨y₀, fun y hy => ⟨f y hy, le_trans (le_max_right _ _) hM.side_ge⟩⟩
private theorem growthFactor_mono {A A' B B' κ κ' : ℝ} (n : ℕ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hAA : A ≤ A')
    (hBB : B ≤ B') (hκ : κ ≤ κ') :
    A * B ^ n * (n.factorial : ℝ) ^ κ ≤ A' * B' ^ n * (n.factorial : ℝ) ^ κ' := by
  have h1 : (1 : ℝ) ≤ n.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero n)
  have hf : (n.factorial : ℝ) ^ κ ≤ (n.factorial : ℝ) ^ κ' := Real.rpow_le_rpow_of_exponent_le h1 hκ
  have hp : 0 ≤ (n.factorial : ℝ) ^ κ := Real.rpow_nonneg (by linarith) _
  have hBn : B ^ n ≤ B' ^ n := pow_le_pow_left₀ hB hBB n
  have hA' : 0 ≤ A' := le_trans hA hAA
  have hB' : 0 ≤ B' := le_trans hB hBB
  exact mul_le_mul (mul_le_mul hAA hBn (by positivity) hA') hf hp (by positivity)
private theorem satisfiesGrowth_mono (hW : TotalDensitiesGiveASystem.BracketNormMonotone)
    {T : ConfigSpace.FlatSequence} {k k' : ℕ}
    {c c' C C' κ κ' : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C) (hk : k ≤ k') (hcc : c ≤ c') (hCC : C ≤ C') (hκ : κ ≤ κ')
    (h : LimitTheorem.SatisfiesGrowth T k c C κ) :
    SystemsWithFiveBounds.SatisfiesGrowth T k' c' C' κ' := fun m φ => by
  refine le_trans (h m φ) ?_
  have hn : ConfigSpace.bracketNorm (k * (m + 1)) (ConfigSpace.toSchwartzFn φ) ≤
      ConfigSpace.bracketNorm (k' * (m + 1)) (ConfigSpace.toSchwartzFn φ) :=
    hW _ _ _ _ (Nat.mul_le_mul_right _ hk)
  have h0 : 0 ≤ ConfigSpace.bracketNorm (k * (m + 1)) (ConfigSpace.toSchwartzFn φ) :=
    ENNReal.toReal_nonneg
  have hg := growthFactor_mono (m + 1) hc hC hcc hCC hκ
  have hg0 : 0 ≤ c' * C' ^ (m + 1) * ((m + 1).factorial : ℝ) ^ κ' := by
    have hc' : 0 ≤ c' := le_trans hc hcc
    have hC' : 0 ≤ C' := le_trans hC hCC
    positivity
  exact mul_le_mul hg hn h0 hg0
abbrev _root_.YangMills.DeltaSharedProofs.p501308 := @satisfiesGrowth_mono
private theorem reconstructionConditions_of {σ : SeparatedTuples.TupleFunctional}
    (h : LimitTheorem.ReconstructionProperties σ) :
    SystemsWithFiveBounds.ReconstructionConditions σ := by
  obtain ⟨a, b, hp, r, s, c, j, U, hU⟩ := h
  exact ⟨a, b, hp, r, s, c, j, U, ⟨hU.acts, hU.isUnitary, hU.fixes_vacuum, hU.comm_hamiltonian⟩⟩
private theorem twoPointFactor_pos : 0 < LimitTheorem.twoPointFactor := by
  unfold LimitTheorem.twoPointFactor
  have := Real.pi_pos
  positivity
private theorem uniformNorm_pos {f : (Fin 4 → ℝ) → ℝ} (hb : TestFunctions.IsBoundedFun f)
    (hz : ∃ z, f z ≠ 0) : 0 < TestFunctions.uniformNorm f := by
  obtain ⟨z, hz⟩ := hz
  obtain ⟨B, hB⟩ := hb
  exact lt_of_lt_of_le (norm_pos_iff.2 hz)
    (le_ciSup (f := fun x => ‖f x‖) ⟨B, by rintro _ ⟨x, rfl⟩; exact hB x⟩ z)
private theorem inverseEighthKernel_pos (hG : TestPairs.GeometryAndKernelBounds) {d ϑ : ℝ} (hd : 0 < d)
    (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) {f g : (Fin 4 → ℝ) → ℝ} (hp : (f, g) ∈ TestFunctions.separatedPairsR4 d ϑ) :
    0 < TestFunctions.inverseEighthKernel f g := by
  have hp' := hp
  simp only [TestFunctions.separatedPairsR4, TestFunctions.separatedPairs, Set.mem_ofPred_eq] at hp'
  obtain ⟨x₁, x₂, b₁, b₂, s₁, s₂⟩ := hp'
  have hcent : TestFunctions.IsCentrePairR4 d ϑ x₁ x₂ (f, g) :=
    ⟨⟨b₁.2.2.2.1, b₁.2.2.2.2.1, b₁.2.2.2.2.2⟩, ⟨b₂.2.2.2.1, b₂.2.2.2.2.1, b₂.2.2.2.2.2⟩, s₁, s₂⟩
  obtain ⟨-, -, -, hker, hchain⟩ := (hG.1 d ϑ ⟨hd, hϑ, hϑ1⟩ x₁ x₂ f g hp hcent).1
  have hG₁ : 0 < TestFunctions.uniformNorm f := uniformNorm_pos hker.1 b₁.2.2.1
  have hG₂ : 0 < TestFunctions.uniformNorm g := uniformNorm_pos hker.2.1 b₂.2.2.1
  have hKf : (10 : ℝ) ^ (-8 : ℤ) * ϑ ^ 2 * TestFunctions.uniformNorm f * TestFunctions.uniformNorm g ≤
      TestFunctions.inverseEighthKernel f g :=
    hchain.1.trans hchain.2.1
  exact lt_of_lt_of_le (by positivity) hKf
private theorem isSubexpGrowth_succ : RoomFunctions.IsSubexpGrowth fun s => (s : ℝ) + 1 := by apply _root_.YangMills.Construction.QuaternionicWilsonModel.TopLimitsRealNonzero.linearGauge_isSubexpGrowth <;> assumption
private theorem isLawModulus_zero : IsLawModulus (1 / 40) fun _ => 0 :=
  ⟨fun _ _ _ _ _ => le_rfl, fun _ _ => ⟨le_rfl, by norm_num⟩, tendsto_const_nhds⟩
private theorem twoPoint_pos_of_law (hG : TestPairs.GeometryAndKernelBounds) {ϑ d₀ : ℝ} {ηBar εBar : ℝ → ℝ}
    {S : LimitTheorem.CumulantFamily}
    (hϑ : ϑ ∈ Ioc (0 : ℝ) 1) (hd₀ : d₀ ∈ Ioc (0 : ℝ) (1 / 40)) (hη : ∀ d ∈ Ioc 0 d₀, ηBar d ∈ Icc (0 : ℝ) (1 / 3))
    (hε : ∀ d ∈ Ioc 0 d₀, εBar d ∈ Icc (0 : ℝ) (1 / 2))
    (h : ∀ d ∈ Ioc (0 : ℝ) d₀, ∀ X : TestSpaces.SepTupleOfCard 2,
      (X.1 0, X.1 1) ∈ TestFunctions.separatedPairsR4 d ϑ →
      SatisfiesTwoPointLawWithError (SystemsWithFiveBounds.twoPointMainTerm d (X.1 0) (X.1 1)) ηBar εBar d
        (S 2 le_rfl X))
    (d : ℝ) (hd : d ∈ Ioc (0 : ℝ) d₀) (X : TestSpaces.SepTupleOfCard 2)
    (hX : (X.1 0, X.1 1) ∈ TestFunctions.separatedPairsR4 d ϑ) :
    0 < S 2 le_rfl X := by
  obtain ⟨η, e, h₁, -⟩ := h d hd X hX
  rw [e]
  have hK := inverseEighthKernel_pos hG hd.1 hϑ.1 hϑ.2 hX
  have hlog : 0 < Real.log (1 / d) := by
    have h₂ : d < 1 := lt_of_le_of_lt (hd.2.trans hd₀.2) (by norm_num)
    exact Real.log_pos (by rw [one_div]; exact (one_lt_inv₀ hd.1).2 h₂)
  have h₃ := (hη d hd).2
  have h₄ := (hε d hd).2
  have hfac : 0 < 1 + η := by
    have a₁ : 0 < 1 - ηBar d := by linarith
    have a₂ : 0 < 1 - εBar d := by linarith
    exact lt_of_lt_of_le (by positivity) h₁
  exact mul_pos (div_pos (mul_pos twoPointFactor_pos hK) (pow_pos hlog 2)) hfac
theorem growingTorusLimitsSatisfyConditions_holds (hWhat : ToriLimit.Claim) (hPer : BallBoundPassesToLimit)
    (hRec : reconstructionOfBoundedFamily) (hPow : PowerBoundAtData)
    (hGrow : GrowthOfPowerBoundedFamily) (hLaws : LawsAtEveryShape)
    (hW : TotalDensitiesGiveASystem.BracketNormMonotone)
    (hIdent : LimitTheorem.CutoffRepresentatives.IdentificationsHold)
    (hTG : TestPairs.GeometryAndKernelBounds) (hPair : Scales.SeparatedPairsAreTestFunctionsStatement)
    (hPl : TwoPoints.TestPlates.TestPlatePieces.Statement)
    (hShape : TwoPoints.Shapes.ShapeConstMemIoc.Statement) : GrowingTorusLimitsSatisfyConditions := by
  obtain ⟨floor, hWh⟩ := hWhat
  refine HoldsAtAdmissibleParameters.mono
    (holdsAtAdmissibleParameters_side_ge (HoldsAtAdmissibleParameters.and hPow hLaws) floor) fun T y hDr hA => ?_
  obtain ⟨⟨⟨yP, fP⟩, cL, fL⟩, hfl⟩ := hA
  obtain ⟨yS, fS⟩ := fL cL le_rfl
  refine ⟨max yP yS, fun g hg hy => ?_⟩
  obtain ⟨Cp, hCp, hbd⟩ := fP g hg (le_trans (le_max_left _ _) hy)
  have fSg := fS g hg (le_trans (le_max_right _ _) hy)
  have hbase : 0 ≤ SeparatedPowerBound.powerBase 1 5 (Cp * 16) := by
    have hb : (1 : ℝ) ≤ SeparatedBound.extBaseMax := le_max_left _ _
    have hb' : 0 ≤ SeparatedBound.extBaseMax := by linarith
    unfold SeparatedPowerBound.powerBase
    positivity
  refine ⟨15, 2 * SeparatedBound.extFactorAbs, SeparatedPowerBound.powerBase 1 5 (Cp * 16), 26,
    fun C hC hk h₁ h₂ h₃ hB ϑ d₀ ηBar εBar hϑ hLaw hd₀ hη hε S hS => ?_⟩
  have hBF : Conventions.IsAdmissibleBlockingFactor T.side := ⟨hDr.L_odd, le_trans (by norm_num) hDr.L_ge⟩
  obtain ⟨K, m, β, hp, hK, hm, hlim⟩ := id hS
  have hβ : ∀ j, 0 < β j := fun j => by
    have h₄ : SequencePassage.passageThreshold (2 * T.B) g ≤ β j := (hp j).2.1
    have h₅ : 0 < g ^ (-2 : ℤ) := zpow_pos hg _
    have h₆ : 1 ≤ T.B := hDr.B_ge
    unfold SequencePassage.passageThreshold at h₄
    linarith
  let Q : ToriSequence T.side := ⟨K, m, β, hβ, hK, hm⟩
  have hQ : Q.HasCumulantLimit S := hlim
  have pos₀ : ∀ n, 2 ≤ n → ∀ d R : ℝ, 0 < d → 0 < R → 0 ≤ C.localBound n d R :=
    fun n hn d R hd hR => (hC.localBound_pos n hn d R hd hR).le
  have hcl := hWh T.side hDr.L_odd hfl Q C.localBound pos₀ (fun n hn R hR => hC.localBound_antitone n hn R hR)
    (fun j n hn R d hR hd f hf hb hs => (hB.onTori (K j) (β j) (hp j) (m j) n hn R d hR hd f hf hb hs).1) S hQ
  have hP₀ := hPer T.side hBF Q C.localBound pos₀
    (fun j n hn R d hR hd f hf hb hs => (hB.onTori (K j) (β j) (hp j) (m j) n hn R d hR hd f hf hb hs).1) S hQ
  have hP₁ := hPer T.side hBF Q
    (fun n d R => C.globalPrefactor d R * C.globalBase R ^ n * (n.factorial : ℝ) ^ C.globalExp)
    (fun n _ d R hd hR => by
      have a₁ := (hC.globalPrefactor_pos d R hd hR).le
      have a₂ := (hC.globalBase_pos R hR).le
      have a₃ : (0 : ℝ) ≤ n.factorial := Nat.cast_nonneg _
      positivity)
    (fun j n hn R d hR hd f hf hb hs => (hB.onTori (K j) (β j) (hp j) (m j) n hn R d hR hd f hf hb hs).2) S hQ
  have hP₂ := hPer T.side hBF Q
    (fun n d R => (Cp * max 1 (d ^ (-((5 : ℕ) : ℤ))) * (1 + R) ^ 4) ^ n * (n.factorial : ℝ) ^ (6 : ℝ))
    (fun n _ d R hd hR => by
      have a₂ : 0 ≤ max 1 (d ^ (-((5 : ℕ) : ℤ))) := le_trans zero_le_one (le_max_left _ _)
      have a₃ : (0 : ℝ) ≤ n.factorial := Nat.cast_nonneg _
      positivity)
    (fun j n hn R d hR hd f hf hb hs => hbd (K j) (β j) (hp j) (m j) n hn R d hR hd f hf hb hs) S hQ
  have hpow : SeparatedPowerBound.PowerSepBound 1 5 (Cp * 16) 6 S := fun n hn d hd X hX => by
    have h₄ := hP₂ n hn 1 d one_pos hd X hX.1 fun i k hik =>
      hX.2.trans (iInf_le_of_le i (iInf_le_of_le k (iInf_le_of_le hik le_rfl)))
    have e : Cp * max 1 (d ^ (-((5 : ℕ) : ℤ))) * (1 + 1) ^ 4 = Cp * 16 * max 1 (d ^ (-((5 : ℕ) : ℤ))) := by
      ring
    simp only [e] at h₄
    exact h₄
  obtain ⟨hml, hcont, hlist⟩ := hRec C.localBound S pos₀ hcl hP₀
  obtain ⟨⟨Tg, hTs, hTb⟩, hdist⟩ := hGrow (Cp * 16) S (by positivity) hcl hpow
  have ha : 0 < InfiniteLattice.refinedSpacing 13 ((1 : ℕ+) : ℕ) := by
    simp only [InfiniteLattice.refinedSpacing, PeriodicLattice.meshSize]
    positivity
  have hL13 : Conventions.IsAdmissibleBlockingFactor 13 := ⟨by decide, le_rfl⟩
  let U₀ : CutoffLattice.FieldsAt 13 ((1 : ℕ+) : ℕ) :=
    CutoffLattice.fieldOfValues ha fun _ => 1
  have hS3 := (hIdent 13 hL13 (fun _ => 1) (fun _ => MeasureTheory.Measure.dirac U₀)
    (fun _ => inferInstance) S).2.2
  have hconn := hS3.2.2.2
  have hon : ∀ d ∈ Ioc (0 : ℝ) d₀, ∀ X : TestSpaces.SepTupleOfCard 2,
      (X.1 0, X.1 1) ∈ TestFunctions.separatedPairsR4 d ϑ →
      SatisfiesTwoPointLawWithError (SystemsWithFiveBounds.twoPointMainTerm d (X.1 0) (X.1 1)) ηBar εBar d
        (S 2 le_rfl X) :=
    hLaw.on_space S (Or.inl hS)
  have hsh : TwoPoints.Shapes.shapeConst ∈ Ioc (0 : ℝ) 1 := hShape.2.2.2.2.2.2
  obtain ⟨d₀', ηB, εB, ζ, K₀, d₄, -, -, law, lim, -, -, -⟩ := fSg TwoPoints.Shapes.shapeConst hsh
    (fun s => (s : ℝ) + 1) isSubexpGrowth_succ (1 / 40) (fun _ => 0) (by norm_num) isLawModulus_zero
  have hd₀' := law.cutoff_mem
  have hpos' := twoPoint_pos_of_law hTG hsh hd₀' law.sharp_on_tori.ηBar_mem
    (fun d hd => law.sharp_on_tori.εBar_mem 0 d hd) (lim.on_space S (Or.inl hS))
  refine ⟨⟨fun v => hcl.invariant _ ⟨1, fun x => by simp [LimitTheorem.shiftMotion]⟩,
      fun r hr _ => hcl.invariant r hr,
      hcl.symmetric, fun r hr => (hS3.2.1 r).2 (hcl.invariant r hr), hS3.1.2 hcl.symmetric⟩,
    hcl.reflectionPositive, hdist, ?_⟩
  refine ⟨fun n hn R hR d hd X hb hs => ?_, ⟨Tg, hTs, ?_⟩, reconstructionConditions_of hlist,
    fun d hd f h hpr hf hh => ?_, hconn, twoPoint_pos_of_law hTG hϑ hd₀ hη hε hon, ?_⟩
  · rw [hconn n hn X]
    exact ⟨hP₀ n hn R d hR hd X hb hs, hP₁ n hn R d hR hd X hb hs⟩
  · exact satisfiesGrowth_mono hW (mul_nonneg (by norm_num) (abs_nonneg _)) hbase hk h₁ h₂ h₃ hTb
  · have hmem := pair_mem_disjointSupportTuples hPair hd.1 hpr hf hh
    obtain ⟨η, e, a, b⟩ := hon d hd ⟨![f, h], hmem⟩ hpr
    refine ⟨⟨![f, h], hmem⟩, rfl, η, ?_, ?_, ?_⟩
    · rw [hconn 2 le_rfl]
      exact e
    · have h₄ := hε d hd
      have h₅ : 0 ≤ (1 - ηBar d) ^ 4 := by positivity
      nlinarith [h₄.2]
    · have h₄ := hε d hd
      have h₅ : 0 ≤ (1 + ηBar d) ^ 4 := by
        have := (hη d hd).1
        positivity
      nlinarith [h₄.2]
  · intro p
    have hϖ : 0 < 2 / 5 * d₀' := by linarith [hd₀'.1]
    have hϖ4 : 2 / 5 * d₀' ≤ 4 := by linarith [hd₀'.2]
    obtain ⟨f, hpair, hc, hcθ, hsupp⟩ := exists_reflected_pair hPl hϖ hϖ4
    have e : 5 / 2 * (2 / 5 * d₀') = d₀' := by ring
    rw [e] at hpair
    let X₂ : TestSpaces.SepTupleOfCard 2 :=
      ⟨![f ∘ TimeAxis.timeReflection, f], pair_mem_disjointSupportTuples hPair hd₀'.1 hpair hcθ hc⟩
    have h2 := hpos' d₀' ⟨hd₀'.1, le_rfl⟩ X₂ hpair
    have hf : f ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ)) := X₂.2.1 1
    let X₁ : SeparatedTuples.SepTuple := TupleLists.toList ⟨1, TestSpaces.singletonSepTuple f hf⟩
    have hX₁ : X₁.1 = List.ofFn (fun _ : Fin 1 => f) := rfl
    have hmem : X₁ ∈ SeparatedTuples.supportedIn TimeAxis.upperHalfSpace := fun u hu => by
      rw [hX₁] at hu
      simp at hu
      rw [hu]
      exact hsupp
    have h0 : (LimitTheorem.centredOf S) X₁ = 0 := by
      have e₀ : LimitTheorem.connectedFn (LimitTheorem.centredOf S) (TestSpaces.singletonSepTuple f hf) =
          LimitTheorem.evalOnMap (LimitTheorem.centredOf S) ⟨1, TestSpaces.singletonSepTuple f hf⟩ :=
        TestSpaces.cumulant_single _ _
      have h₄ := hS3.2.2.1 (TestSpaces.singletonSepTuple f hf)
      rw [e₀] at h₄
      exact h₄
    have hprod : (LimitTheorem.centredOf S)
        (SeparatedTuples.SepTuple.juxt (SeparatedTuples.push TimeAxis.timeReflection X₁) X₁) = S 2 le_rfl X₂ := by
      have e₁ := juxt_timeReflection_val (fun _ => f) (fun _ => f) hX₁ hX₁ hmem hmem
      have e₂ : SeparatedTuples.SepTuple.juxt (SeparatedTuples.push TimeAxis.timeReflection X₁) X₁ =
          TupleLists.toList ⟨2, X₂⟩ :=
        Subtype.ext (e₁.trans (by
          show _ = List.ofFn ![f ∘ TimeAxis.timeReflection, f]
          simp [List.ofFn_succ, Fin.append, Fin.addCases]))
      rw [e₂]
      show LimitTheorem.evalOnMap (LimitTheorem.centredOf S) ⟨2, X₂⟩ = _
      rw [evalOnMap_centredOf, centredOfCumulants_two]
    exact two_le_rank_physicalSpace p (hasReconstruction_of_properties hlist p) ⟨X₁, hmem⟩ h0 (hprod ▸ h2)
end YangMills.Construction.TotalDensities.LimitAlongToriProof
end
