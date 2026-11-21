import YangMills.Construction.ClusterExpansionOfAStep.ParametersExist
import YangMills.Construction.QuaternionicWilsonModel.TheFlowRepresentsTheMixedMomentProof
import YangMills.Construction.QuaternionicWilsonModel.TheQuaternionModelIsSUTwoWithWilsonsWeightProof
import YangMills.Construction.QuaternionicWilsonModel.TheSeamsOfTheModel
import YangMills.Construction.ResponseInTheExpansion.TheChainIsALaw
import YangMills.Construction.RunningCouplingSlope.CoefficientOfTheLeastAction
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped Topology Quaternion
noncomputable section
namespace YangMills.Construction
open Matrices TorusLumps WeightedResponses TorusFields SlopeCoefficient TotalDensityFlow ModelSeams SoftAverages
  BlockAverages ClusterExpansionOfAStep RenormalizationStepParameters TotalDensitySystem RunningCouplingSlope
namespace ModelSeamsProof
def kernelCompatibleParams (ℓ : TorusLumps.StepParameters) : TorusLumps.StepParameters :=
  { ℓ with κ := 1 / 8, κ₁ := 1, rt := 1, n₁ := 1, E := 1, E₃ := 1, derivBound := 1, n₀ := 4096, y₁ := 2 ^ 1600, B := 1 }
theorem le_clusterRange_two_pow : 2 ^ 16 ≤ clusterRange (2 ^ 1600) := by
  unfold TorusLumps.clusterRange
  have hr : ((2 : ℝ) ^ 1600) ^ ((1 : ℝ) / 100) = 2 ^ 16 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [hr]
  have hc : ⌈((2 : ℝ) ^ 16)⌉₊ = 2 ^ 16 := by
    have h2 : ((2 : ℝ) ^ 16) = ((2 ^ 16 : ℕ) : ℝ) := by norm_num
    rw [h2, Nat.ceil_natCast]
  rw [hc]
theorem kernelCompatibleParams_admissible {ℓ : TorusLumps.StepParameters} (hd : IsUnitMeshStepParameters ℓ) :
    (kernelCompatibleParams ℓ).Admissible where
  a_ge := by
    show 1 ≤ ℓ.coupling
    rw [hd.coupling_eq_one]
  L_odd := hd.side_odd
  L_ge := by
    have h := hd.side_ge
    show 2 ^ 16 ≤ ℓ.side
    omega
  σ_pos := hd.threshold_mem.1
  κ_pos := by norm_num [kernelCompatibleParams]
  κ_le := by norm_num [kernelCompatibleParams]
  κ₁_pos := by norm_num [kernelCompatibleParams]
  rt_pos := by norm_num [kernelCompatibleParams]
  n₁_pos := by norm_num [kernelCompatibleParams]
  E_pos := by norm_num [kernelCompatibleParams]
  E_ge := by norm_num [kernelCompatibleParams]
  depth_lt := hd.side_gt
  E₃_pos := by norm_num [kernelCompatibleParams]
  B_pos := by norm_num [kernelCompatibleParams]
  Cder_ge := by norm_num [kernelCompatibleParams]
  n₀_ge := by norm_num [kernelCompatibleParams]
  y₁_ge := by
    show (1 : ℝ) ≤ 2 ^ 1600
    exact one_le_pow₀ (by norm_num)
  range_ge := le_clusterRange_two_pow
theorem chainFunctional_kernelCompatible (ℓ : TorusLumps.StepParameters) (β : ℝ) (x : ℕ → ℝ) (s : ℕ) :
    chainFunctional (kernelCompatibleParams ℓ) β x s = chainFunctional ℓ β x s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    show kernelImage (kernelCompatibleParams ℓ) (x s) (chainFunctional (kernelCompatibleParams ℓ) β x s) =
      kernelImage ℓ (x s) (chainFunctional ℓ β x s)
    rw [ih]
    rfl
theorem flowData_snd_eq_chainFunctional (ℓ : TorusLumps.StepParameters) (β : ℝ) (t : ℕ) :
    (flowData ℓ β t).2 = chainFunctional ℓ β (TotalDensityFlow.coupling ℓ β) t := by apply _root_.YangMills.SharedProofs.p64958 <;> assumption
theorem isFiniteMeasure_chainReferenceMeasure (ℓ : TorusLumps.StepParameters) :
    (s n : ℕ) → [NeZero n] → IsFiniteMeasure (chainReferenceMeasure ℓ s n)
  | 0, n, _ => inferInstanceAs (IsFiniteMeasure (fieldHaar n))
  | s + 1, n, _ => by
    letI := chainSampleMeasurableSpace ℓ s (n * ℓ.side)
    haveI := isFiniteMeasure_chainReferenceMeasure ℓ s (n * ℓ.side)
    haveI : IsFiniteMeasure (Measure.count : Measure (StepCosts.BaseChoice ℓ.side n)) := inferInstance
    exact inferInstanceAs (IsFiniteMeasure ((chainReferenceMeasure ℓ s (n * ℓ.side)).prod
      ((Measure.count : Measure (StepCosts.BaseChoice ℓ.side n)).prod (fieldHaar n))))
def sampleEquiv (ℓ : TorusLumps.StepParameters) :
    (s n : ℕ) → ChainSample ℓ s n ≃ᵐ ChainSample (kernelCompatibleParams ℓ) s n
  | 0, n => MeasurableEquiv.refl (TorusField n)
  | s + 1, n =>
    letI := chainSampleMeasurableSpace ℓ s (n * ℓ.side)
    letI := chainSampleMeasurableSpace (kernelCompatibleParams ℓ) s (n * ℓ.side)
    MeasurableEquiv.prodCongr (sampleEquiv ℓ s (n * ℓ.side))
      (MeasurableEquiv.refl (StepCosts.BaseChoice ℓ.side n × TorusField n))
theorem finalField_sampleEquiv (ℓ : TorusLumps.StepParameters) : (s n : ℕ) → (u : ChainSample ℓ s n) →
    finalField (kernelCompatibleParams ℓ) s n (sampleEquiv ℓ s n u) = finalField ℓ s n u
  | 0, _, _ => rfl
  | _ + 1, _, _ => rfl
theorem initialField_sampleEquiv (ℓ : TorusLumps.StepParameters) : (s n : ℕ) → (u : ChainSample ℓ s n) →
    initialField (kernelCompatibleParams ℓ) s n (sampleEquiv ℓ s n u) = initialField ℓ s n u
  | 0, _, _ => rfl
  | s + 1, n, u => initialField_sampleEquiv ℓ s (n * ℓ.side) u.1
theorem chainJointDensity_sampleEquiv (ℓ : TorusLumps.StepParameters) (β : ℝ) (x : ℕ → ℝ) :
    (s n : ℕ) → [NeZero n] → (u : ChainSample ℓ s n) →
    chainJointDensity (kernelCompatibleParams ℓ) β x s n (sampleEquiv ℓ s n u) = chainJointDensity ℓ β x s n u
  | 0, _, _, _ => rfl
  | s + 1, n, _, u => by
    show chainJointDensity (kernelCompatibleParams ℓ) β x s (n * ℓ.side) (sampleEquiv ℓ s (n * ℓ.side) u.1) *
        stepTransitionDensity (kernelCompatibleParams ℓ) (x s)
          (finalField (kernelCompatibleParams ℓ) s (n * ℓ.side) (sampleEquiv ℓ s (n * ℓ.side) u.1)) u.2.1 u.2.2 =
      chainJointDensity ℓ β x s (n * ℓ.side) u.1 *
        stepTransitionDensity ℓ (x s) (finalField ℓ s (n * ℓ.side) u.1) u.2.1 u.2.2
    rw [chainJointDensity_sampleEquiv ℓ β x s (n * ℓ.side) u.1, finalField_sampleEquiv ℓ s (n * ℓ.side) u.1]
    rfl
theorem map_chainReferenceMeasure (ℓ : TorusLumps.StepParameters) : (s n : ℕ) → [NeZero n] →
    (chainReferenceMeasure ℓ s n).map (sampleEquiv ℓ s n) = chainReferenceMeasure (kernelCompatibleParams ℓ) s n
  | 0, n, _ => Measure.map_id
  | s + 1, n, _ => by
    letI := chainSampleMeasurableSpace ℓ s (n * ℓ.side)
    letI := chainSampleMeasurableSpace (kernelCompatibleParams ℓ) s (n * ℓ.side)
    haveI := isFiniteMeasure_chainReferenceMeasure ℓ s (n * ℓ.side)
    haveI := isFiniteMeasure_chainReferenceMeasure (kernelCompatibleParams ℓ) s (n * ℓ.side)
    have ih := map_chainReferenceMeasure ℓ s (n * ℓ.side)
    have hp := Measure.map_prod_map (chainReferenceMeasure ℓ s (n * ℓ.side))
      ((Measure.count : Measure (StepCosts.BaseChoice ℓ.side n)).prod (fieldHaar n))
      (sampleEquiv ℓ s (n * ℓ.side)).measurable measurable_id
    rw [Measure.map_id, ih] at hp
    exact hp.symm ▸ rfl
theorem map_chainJointLaw (ℓ : TorusLumps.StepParameters) (β : ℝ) (x : ℕ → ℝ) (s n : ℕ) [NeZero n] :
    (chainJointLaw ℓ β x s n).map (sampleEquiv ℓ s n) = chainJointLaw (kernelCompatibleParams ℓ) β x s n := by
  ext A hA
  rw [(sampleEquiv ℓ s n).map_apply, chainJointLaw, chainJointLaw,
    withDensity_apply _ ((sampleEquiv ℓ s n).measurable hA), withDensity_apply _ hA,
    ← map_chainReferenceMeasure ℓ s n, MeasurableEquiv.restrict_map, lintegral_map_equiv]
  exact lintegral_congr fun u => by rw [chainJointDensity_sampleEquiv]
theorem isChainDensity_kernelCompatible (hC : ChainIsProbabilityLaw) {ℓ : TorusLumps.StepParameters}
    (hd : IsUnitMeshStepParameters ℓ) (β : ℝ) (x : ℕ → ℝ) (t n : ℕ) [NeZero n] :
    IsChainDensity (kernelCompatibleParams ℓ) β x t n (chainFunctional ℓ β x t) := by
  obtain ⟨h1, h2, -, -, -, -, h7, h8, h9⟩ :=
    hC (kernelCompatibleParams ℓ) (kernelCompatibleParams_admissible hd) hd.side_gt β x t n
  rw [chainFunctional_kernelCompatible] at h7 h8
  refine ⟨h1, fun G hG => h9 G hG.1 hG.2, h7, h2, fun F hF => ?_⟩
  rw [h7]
  exact h8 F hF.1 hF.2
theorem isChainDensity_of_unitMesh (hC : ChainIsProbabilityLaw) {ℓ : TorusLumps.StepParameters}
    (hd : IsUnitMeshStepParameters ℓ) (β : ℝ) (x : ℕ → ℝ) (t n : ℕ) [NeZero n] :
    IsChainDensity ℓ β x t n (chainFunctional ℓ β x t) := by
  have hf := isChainDensity_kernelCompatible hC hd β x t n
  have e := map_chainJointLaw ℓ β x t n
  refine ⟨?_, fun G hG => ?_, hf.integral_eq, hf.partition_pos, fun F hF => ?_⟩
  · haveI := hf.isProbability
    refine ⟨?_⟩
    have h := measure_univ (μ := chainJointLaw (kernelCompatibleParams ℓ) β x t n)
    rw [← e, (sampleEquiv ℓ t n).map_apply, Set.preimage_univ] at h
    exact h
  · have h := hf.initial_integral G hG
    rw [← e, integral_map_equiv] at h
    exact (integral_congr_ae (Eventually.of_forall fun u =>
      congrArg G (initialField_sampleEquiv ℓ t n u).symm)).trans h
  · have h := hf.final_integral F hF
    rw [← e, integral_map_equiv] at h
    exact (integral_congr_ae (Eventually.of_forall fun u =>
      congrArg F (finalField_sampleEquiv ℓ t n u).symm)).trans h
theorem arraysAreChainDensities (hC : ChainIsProbabilityLaw) (hB : bottomChainLawIsWilsonGibbsStatement)
    {ℓ : TorusLumps.StepParameters} (hd : IsUnitMeshStepParameters ℓ) : ArraysAreChainDensities ℓ := by
  refine ⟨fun β t n _ => ?_, fun β m K n _ hm hn => ?_⟩
  · rw [flowData_snd_eq_chainFunctional]
    exact isChainDensity_of_unitMesh hC hd β _ t n
  · have hL : 2 ≤ ℓ.side := by
      have := hd.side_ge
      omega
    have e : fineSide ℓ.side K n = 2 * ℓ.side ^ (m + K) := by rw [fineSide_eq, hn, pow_add]; ring
    have h1 : 2 ≤ ℓ.side ^ (m + K) := le_trans hL (Nat.le_self_pow (by omega) ℓ.side)
    exact hB ℓ β (TotalDensityFlow.coupling ℓ β) K n m K (chainFunctional ℓ β (TotalDensityFlow.coupling ℓ β) K) e
      (by rw [e]; omega) (isChainDensity_of_unitMesh hC hd β _ K n)
theorem hermitianOfImaginary_eq (X : imaginaryQuaternions) : hermitianOfImaginary X =
    !![((X : ℍ[ℝ]).imI : ℂ), ((X : ℍ[ℝ]).imK : ℂ) - Complex.I * (X : ℍ[ℝ]).imJ;
      ((X : ℍ[ℝ]).imK : ℂ) + Complex.I * (X : ℍ[ℝ]).imJ, -((X : ℍ[ℝ]).imI : ℂ)] := by
  have h : (X : ℍ[ℝ]).re = 0 := X.2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermitianOfImaginary, quaternionToMatrix, h] <;> ring_nf <;>
    simp [Complex.I_sq]
theorem quaternionToMatrix_eq_I_smul (X : imaginaryQuaternions) :
    quaternionToMatrix (X : ℍ[ℝ]) = Complex.I • hermitianOfImaginary X := by
  simp [hermitianOfImaginary, smul_smul]
theorem hermitianOfImaginary_injective : Function.Injective hermitianOfImaginary := by
  intro X Y h
  exact Subtype.ext (quaternionToMatrix_injective
    (by rw [quaternionToMatrix_eq_I_smul, quaternionToMatrix_eq_I_smul, h]))
theorem hermitianOfImaginary_isHermitian (X : imaginaryQuaternions) : (hermitianOfImaginary X).IsHermitian := by
  rw [hermitianOfImaginary_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply, sub_eq_add_neg]
theorem fullTrace_hermitianOfImaginary (X : imaginaryQuaternions) :
    ComplexMatrix2.fullTrace (hermitianOfImaginary X) = 0 := by
  rw [hermitianOfImaginary_eq]
  simp [ComplexMatrix2.fullTrace, Matrix.trace_fin_two]
theorem existsUnique_hermitianOfImaginary_eq (A : ComplexMatrix2) (hA : A.IsHermitian)
    (ht : ComplexMatrix2.fullTrace A = 0) : ∃! X : imaginaryQuaternions, hermitianOfImaginary X = A := by
  have h00 : star (A 0 0) = A 0 0 := hA.apply 0 0
  have h10 : star (A 0 1) = A 1 0 := hA.apply 1 0
  have him : (A 0 0).im = 0 := by
    have := congrArg Complex.im h00
    simp at this
    linarith
  have hre' : (A 1 0).re = (A 0 1).re := by rw [← h10]; simp
  have him' : (A 1 0).im = -(A 0 1).im := by rw [← h10]; simp
  have h11 : A 1 1 = -A 0 0 := by
    have : A 0 0 + A 1 1 = 0 := by simpa [ComplexMatrix2.fullTrace, Matrix.trace_fin_two] using ht
    linear_combination this
  have hX : hermitianOfImaginary (imagQuaternion (A 0 0).re (-(A 0 1).im) (A 0 1).re) = A := by
    rw [hermitianOfImaginary_eq]
    ext i j
    fin_cases i <;> fin_cases j
    · simp [imagQuaternion, Complex.ext_iff, him]
    · simp [imagQuaternion, Complex.ext_iff]
    · simp [imagQuaternion, Complex.ext_iff, hre', him']
    · simp [imagQuaternion, h11, Complex.ext_iff, him]
  exact ⟨_, hX, fun Y hY => hermitianOfImaginary_injective (hY.trans hX.symm)⟩
theorem inner_eq_half_fullTrace (X X' : imaginaryQuaternions) :
    ((inner ℝ (X : ℍ[ℝ]) (X' : ℍ[ℝ]) : ℝ) : ℂ) =
      (1 / 2) * ComplexMatrix2.fullTrace (hermitianOfImaginary X * hermitianOfImaginary X') := by
  have h : (X : ℍ[ℝ]).re = 0 := X.2
  have h' : (X' : ℍ[ℝ]).re = 0 := X'.2
  rw [hermitianOfImaginary_eq, hermitianOfImaginary_eq, Quaternion.inner_def]
  simp only [ComplexMatrix2.fullTrace, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  simp [h, h']
  ring_nf
  simp [Complex.I_sq]
theorem specialUnitary_expUnit (X : imaginaryQuaternions) :
    ((unitQuaternionEquivSpecialUnitary (expUnit X) : ComplexMatrix2.specialUnitary) : ComplexMatrix2) =
      ComplexMatrix2.matExp (Complex.I • hermitianOfImaginary X) := by
  have hp : pureQuaternion ![(X : ℍ[ℝ]).imI, (X : ℍ[ℝ]).imJ, (X : ℍ[ℝ]).imK] = (X : ℍ[ℝ]) := by
    have h : (X : ℍ[ℝ]).re = 0 := X.2
    ext <;> simp [pureQuaternion, h]
  have he := colorExp_ofReal ![(X : ℍ[ℝ]).imI, (X : ℍ[ℝ]).imJ, (X : ℍ[ℝ]).imK]
  rw [hp] at he
  rw [coe_unitQuaternionEquivSpecialUnitary, ← quaternionToMatrix_eq_I_smul]
  show quaternionToMatrix (NormedSpace.exp (X : ℍ[ℝ])) = _
  rw [← he]
  show ComplexMatrix2.matExp (colorMatrix _) = _
  rw [colorMatrix_ofReal, hp]
def hermitianAddHom : imaginaryQuaternions →+ ComplexMatrix2 where
  toFun := hermitianOfImaginary
  map_zero' := by
    rw [hermitianOfImaginary_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_add' X Y := by
    rw [hermitianOfImaginary_eq, hermitianOfImaginary_eq, hermitianOfImaginary_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
theorem hermitianOfImaginary_smul (r : ℝ) (X : imaginaryQuaternions) :
    hermitianOfImaginary (r • X) = (r : ℂ) • hermitianOfImaginary X := by
  rw [hermitianOfImaginary_eq, hermitianOfImaginary_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring
theorem specialUnitary_perturb {n k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (σ : Fin k → ℝ) (x : TorusSite n) (i : Fin 4) :
    ((unitQuaternionEquivSpecialUnitary (TorusFields.perturb c X σ (trivialField n) x i) :
        ComplexMatrix2.specialUnitary) : ComplexMatrix2) =
      ComplexMatrix2.matExp (Complex.I • ∑ l, if c l = (x, i) then (σ l : ℂ) • hermitianOfImaginary (X l) else 0) := by
  have hm : TorusFields.perturb c X σ (trivialField n) x i =
      expUnit (∑ l, if c l = (x, i) then σ l • X l else 0) := by
    simp [TorusFields.perturb, trivialField]
  rw [hm, specialUnitary_expUnit]
  congr 2
  show hermitianAddHom _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases h : c l = (x, i)
  · simp only [if_pos h]
    exact hermitianOfImaginary_smul _ _
  · simp only [if_neg h]
    exact map_zero hermitianAddHom
theorem pauliAlgebra : ImaginaryQuaternionsArePauliAlgebra where
  matrix_eq := quaternionToMatrix_eq_I_smul
  isHermitian := hermitianOfImaginary_isHermitian
  trace_eq_zero := fullTrace_hermitianOfImaginary
  existsUnique := existsUnique_hermitianOfImaginary_eq
  inner_eq_half_trace := inner_eq_half_fullTrace
  pauli_i := by
    rw [hermitianOfImaginary_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [imagQuaternion]
  pauli_j := by
    rw [hermitianOfImaginary_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [imagQuaternion]
  pauli_k := by
    rw [hermitianOfImaginary_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [imagQuaternion]
  exp_eq := specialUnitary_expUnit
  perturb_eq := specialUnitary_perturb
theorem eventuallyInParameters_of_forall {P : ColdStepAtMirrorFrames.StepParameters → Prop} (h : ∀ T, P T) :
    ColdStepAtMirrorFrames.EventuallyInParameters P := fun _ _ =>
  ⟨0, fun _ _ _ _ _ => ⟨0, fun _ _ => ⟨1, one_pos, fun _ _ _ => ⟨1, one_pos, fun _ _ _ _ => ⟨0, fun _ _ =>
    ⟨1, one_pos, fun _ _ _ _ _ => ⟨0, fun _ _ _ _ => ⟨0, fun _ _ => ⟨0, fun _ _ => ⟨0, fun _ _ => h _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem exists_admissible_parameterAssignment (h : ParametersCanBeChosen) : ∃ T : ParameterAssignment, T.Admissible := by
  obtain ⟨cK, κ, δ₁, J₀, h⟩ := h 1 le_rfl
  obtain ⟨L₀, hL⟩ := h (fun _ => True) (eventuallyInParameters_of_forall fun _ => trivial)
  obtain ⟨T, -, -, -, -, -, -, -, -, -, -, -, -, hT, -⟩ := hL (2 * L₀ + 1) ⟨L₀, rfl⟩ (by omega) 0 (fun _ => 1)
    (fun _ _ => 1) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ => 0) (fun _ => one_pos) (fun _ _ => one_pos)
  exact ⟨T, hT⟩
theorem wilsonAction_trivialField {n : ℕ} [NeZero n] :
    TorusFields.wilsonAction (Finset.univ : Finset (TorusSite n)) (trivialField n) = 0 := by
  unfold TorusFields.wilsonAction TorusFields.plaquetteEnergy
  refine Finset.sum_eq_zero fun p _ => ?_
  simp [TorusFields.holonomy, trivialField]
theorem logRatio_wilsonWeight {β : ℝ} {n : ℕ} (hn : n ≠ 0) (a : ℝ) (L : ℕ) (V : TorusField n) :
    logRatio (wilsonWeight β) n V = -β * minimalActionTotal a L 0 n V := by
  haveI : NeZero n := ⟨hn⟩
  unfold TotalDensityFlow.logRatio TorusLumps.wilsonWeight RunningCouplingSlope.minimalActionTotal
  simp only [dif_neg hn]
  rw [Real.log_exp, Real.log_exp, wilsonAction_trivialField]
  simp [actionAtLevel]
theorem sideFilter_le_atTop {L : ℕ} (hL : 2 ≤ L) : sideFilter L ≤ atTop := by apply _root_.YangMills.SharedProofs.p17016 <;> assumption
theorem sideFilter_eventually_ne_zero {L : ℕ} (hL : 2 ≤ L) : ∀ᶠ n in sideFilter L, n ≠ 0 := by
  unfold TotalDensityFlow.sideFilter
  rw [Filter.eventually_map]
  exact Filter.Eventually.of_forall fun q => by positivity
instance sideFilter_neBot (L : ℕ) : (sideFilter L).NeBot := by
  unfold TotalDensityFlow.sideFilter
  infer_instance
theorem wilsonWeight_hasNextCoupling {a : ℝ} {L L' : ℕ} (hL : 2 ≤ L')
    (h : HasSlopeCoefficient atTop (minimalActionTotal a L 0) 1) (β : ℝ) :
    HasNextCoupling L' (wilsonWeight β) β := by
  obtain ⟨K, hK, hs⟩ := h
  have hle := sideFilter_le_atTop hL
  have hne := sideFilter_eventually_ne_zero hL
  refine ⟨hne.mono fun n hn => Filter.Eventually.of_forall fun V => ?_, ?_⟩
  · simp only [wilsonWeight, dif_neg hn]
    exact Real.exp_pos _
  refine ⟨fun c c' => -β * K c c', ?_, ?_⟩
  · have hsec : ∀ᶠ n in sideFilter L', ∀ (c c' : TorusBond n) (X X' : imaginaryQuaternions),
        hessianAtTrivial (logRatio (wilsonWeight β)) n c c' X X' =
          -β * hessianAtTrivial (minimalActionTotal a L 0) n c c' X X' := by
      filter_upwards [hne, hK.eventually_isGaugeTotalAt.filter_mono hle] with n hn ht c c' X X'
      have hf : (fun σ : Fin 2 → ℝ =>
            logRatio (wilsonWeight β) n (TorusFields.perturb ![c, c'] ![X, X'] σ (trivialField n))) =
          (-β) • fun σ : Fin 2 → ℝ =>
            minimalActionTotal a L 0 n (TorusFields.perturb ![c, c'] ![X, X'] σ (trivialField n)) := by
        funext σ
        simp only [Pi.smul_apply, smul_eq_mul]
        exact logRatio_wilsonWeight hn a L _
      unfold SlopeCoefficient.hessianAtTrivial TorusFields.mixedDeriv
      rw [hf, iteratedFDeriv_const_smul_apply (ht.contDiffAt_perturb 2 _ _)]
      simp
    refine ⟨?_, ?_, ?_⟩
    · filter_upwards [hne, hK.eventually_isGaugeTotalAt.filter_mono hle] with n hn ht
      have hH : logRatio (wilsonWeight β) n = fun V => -β * minimalActionTotal a L 0 n V :=
        funext fun V => logRatio_wilsonWeight hn a L V
      refine ⟨fun k c X => ?_, ?_, fun g => ?_, fun g => ?_⟩
      · have := (ht.contDiffAt_perturb k c X).const_smul (-β)
        refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun σ => ?_)
        simp [hH]
      · filter_upwards [ht.gauge_invariant_near] with p hp
        simp only [hH, hp]
      · filter_upwards [ht.constant_gauge_invariant g] with V hV
        simp only [hH, hV]
      · filter_upwards [ht.isometry_invariant g] with V hV V' hc
        simp only [hH, hV V' hc]
    · obtain ⟨M, θ, hθ, hd⟩ := hK.exp_decay
      refine ⟨|β| * M, θ, hθ, ?_⟩
      filter_upwards [hd.filter_mono hle, hsec] with n h1 h2 c c' X X' hX hX'
      rw [h2, abs_mul, abs_neg, mul_assoc]
      exact mul_le_mul_of_nonneg_left (h1 c c' X X' hX hX') (abs_nonneg _)
    · intro c c' X X'
      have := ((hK.tendsto_kernel c c' X X').mono_left hle).const_mul (-β)
      refine (this.congr' ?_).trans (le_of_eq ?_)
      · filter_upwards [hsec] with n hn
        exact (hn _ _ _ _).symm
      · congr 1
        ring
  · have h1 : HasSum (fun z => -β * secondMomentTerm K z) (-β * 1) := hs.mul_left (-β)
    have h2 : (secondMomentTerm fun c c' => -β * K c c') = fun z => -β * secondMomentTerm K z := by
      funext z
      simp only [secondMomentTerm]
      ring
    show HasSum (secondMomentTerm fun c c' => -β * K c c') (-β)
    rw [h2]
    have h3 : -β * 1 = -β := by ring
    rw [h3] at h1
    exact h1
theorem hasMixedSecondMoment_unique {l : Filter ℕ} [l.NeBot] {H : GaugeTotal} {b b' : ℝ}
    (h : HasMixedSecondMoment l H b) (h' : HasMixedSecondMoment l H b') : b = b' := by
  exact _root_.YangMills.SharedProofs.p57451 (l := l) (H := H) h h'
theorem wilsonWeightMixedMoment (hCL : MinimalActionHasUnitCoefficient) (hLD : ParametersCanBeChosen)
    (hM : SlopeIsMixedMoment) : wilsonWeightMixedMomentEqNegCoupling := by
  intro L β hL
  obtain ⟨T, hT⟩ := exists_admissible_parameterAssignment hLD
  have hr : HasNextCoupling L (wilsonWeight β) β := wilsonWeight_hasNextCoupling hL (hCL T hT 0) β
  have hm := hM (sideFilter L) (sideFilter_le_atTop hL) _ _ hr.2
  exact ⟨hr, fun b => ⟨fun hb => hasMixedSecondMoment_unique hb hm, fun hb => hb ▸ hm⟩⟩
theorem seamsStatement_holds (hC : ChainIsProbabilityLaw) (hB : bottomChainLawIsWilsonGibbsStatement)
    (hCL : MinimalActionHasUnitCoefficient) (hLD : ParametersCanBeChosen)
    (hM : SlopeIsMixedMoment) : seamsStatement :=
  ⟨fun _ hd => arraysAreChainDensities hC hB hd, pauliAlgebra, wilsonWeightMixedMoment hCL hLD hM⟩
end ModelSeamsProof
end YangMills.Construction
end
