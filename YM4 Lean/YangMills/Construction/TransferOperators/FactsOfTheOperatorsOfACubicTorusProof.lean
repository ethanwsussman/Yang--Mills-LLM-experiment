import YangMills.Construction.Matrices.FactsOnFunctionsAndOperatorsOfSeveralVariablesOnG
import YangMills.Construction.TransferOperators.AlgebraOfATransferOperatorOnAPowerOfG
import YangMills.Construction.TransferOperators.AverageOfATwistedActionOnAPowerOfG
import YangMills.Construction.TransferOperators.EnergyOfTheOrbitsOfACubicTorus
import YangMills.Construction.TransferOperators.FactsOfTheOperatorsOfACubicTorus
import YangMills.Construction.TransferOperators.FactsOfTheSquareRootOfTheBondKernel
import YangMills.Construction.TransferOperators.KernelsInvariantUnderATwistedAction
import YangMills.Construction.TransferOperators.MultiplicationByABoundedFunctionOnAPowerOfG
import YangMills.Construction.TransferOperators.OperatorsOfATwistedActionOnAPowerOfG
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
open SpinHarmonics
namespace TransferOperators.CubicTorusOperators
section PeterWeyl
variable (J : Type) [Finite J] [Nonempty J]
theorem one_le_norm_peterWeylFn (hS : SeveralVariables.SeveralVariablesFacts)
    (α : PeterWeylIndex J) : 1 ≤ ‖peterWeylFn α‖ := by
  have hunit : ‖peterWeylVec α‖ = 1 := (hS J (spins α) ⟨0⟩).1.1.1 α
  have hop := (ContinuousMap.toLp (E := ℂ) 2 (Matrices.ComplexMatrix2.haarPi J) ℂ).le_of_opNorm_le
    (ContinuousMap.toLp_norm_le (μ := Matrices.ComplexMatrix2.haarPi J) (p := 2) (𝕜 := ℂ) (E := ℂ)
      (α := J → Matrices.ComplexMatrix2.specialUnitary)) (peterWeylFn α)
  have hle : ‖peterWeylVec α‖ ≤ ‖peterWeylFn α‖ := by
    simpa [measureUnivNNReal, peterWeylVec] using hop
  rwa [hunit] at hle
variable {β : ℝ}
theorem norm_sqrtLinkOperator_peterWeylVec_le (hS : SeveralVariables.SeveralVariablesFacts)
    (hR : SqrtLinkFacts.SqrtLinkKernelFacts) (hβ : 0 < β) (α : PeterWeylIndex J) :
    ‖sqrtLinkOperator β J (peterWeylVec α)‖ ≤ sqrtPeterWeylCoeff β α := by
  obtain ⟨-, -, -, hEig, -⟩ := (hR β hβ).1 J
  have hBasis := (hS J (spins α) ⟨0⟩).1
  have hmem : peterWeylFn α ∈ prodCoeffSpan (spins α) := by
    rw [← hBasis.2.2.1]
    exact Submodule.subset_span ⟨α, rfl, rfl⟩
  have heig : sqrtLinkOperator β J (peterWeylVec α) =
      (sqrtCharCoeffProd β (spins α) : ℂ) • peterWeylVec α :=
    (hEig (spins α) (peterWeylFn α) hmem).1
  have hunit : ‖peterWeylVec α‖ = 1 := hBasis.1.1 α
  rw [heig, norm_smul, hunit, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (show 0 ≤ sqrtCharCoeffProd β (spins α) from Real.sqrt_nonneg _)]
  exact le_refl _
theorem summable_sqrtPeterWeylCoeff (hS : SeveralVariables.SeveralVariablesFacts)
    (hR : SqrtLinkFacts.SqrtLinkKernelFacts) (hβ : 0 < β) :
    Summable (sqrtPeterWeylCoeff β : PeterWeylIndex J → ℝ) := by
  obtain ⟨-, -, hSum, -⟩ := (hR β hβ).1 J
  refine Summable.of_nonneg_of_le (fun α => Real.sqrt_nonneg _) (fun α => ?_)
    (hSum.2 (1 / 2) (by norm_num))
  have hrpow : (peterWeylCoeff β α).re ^ (1 / 2 : ℝ) = sqrtPeterWeylCoeff β α :=
    (Real.sqrt_eq_rpow _).symm
  rw [hrpow]
  have hone := one_le_norm_peterWeylFn J hS α
  exact le_mul_of_one_le_right (Real.sqrt_nonneg _) (one_le_pow₀ hone)
theorem summable_sqrtPeterWeylCoeff_sq (hS : SeveralVariables.SeveralVariablesFacts)
    (hR : SqrtLinkFacts.SqrtLinkKernelFacts) (hβ : 0 < β) :
    Summable fun α : PeterWeylIndex J => sqrtPeterWeylCoeff β α ^ 2 := by
  obtain ⟨-, -, hSum, -⟩ := (hR β hβ).1 J
  refine Summable.of_nonneg_of_le (fun α => sq_nonneg _) (fun α => ?_) (hSum.2 1 one_pos).abs
  have hone := one_le_norm_peterWeylFn J hS α
  have hsq : Real.sqrt (peterWeylCoeff β α).re ^ 2 ≤ |(peterWeylCoeff β α).re| := by
    rcases le_total 0 (peterWeylCoeff β α).re with h | h
    · rw [Real.sq_sqrt h]
      exact le_abs_self _
    · rw [Real.sqrt_eq_zero_of_nonpos h]
      simp
  rw [Real.rpow_one, abs_mul, abs_of_nonneg (sq_nonneg ‖peterWeylFn α‖)]
  exact hsq.trans (le_mul_of_one_le_right (abs_nonneg _) (one_le_pow₀ hone))
end PeterWeyl
section CubicTorus
variable (Γ : CubicPeriodSublattice) (μ : Fin 4)
theorem vertexOrbits_nonempty : Nonempty (Γ.VertexOrbits μ) := ⟨Γ.vertexClass 0⟩
theorem linkOrbits_nonempty : Nonempty (Γ.LinkOrbits μ) := by
  obtain ⟨ρ, hρ⟩ := exists_ne μ
  exact ⟨Γ.linkClass (SliceLink.ofAxis 0 ρ hρ)⟩
theorem gaugeRep_spec (hO : TwistedActionOperators.Statement)
    (g : Γ.VertexOrbits μ → Matrices.ComplexMatrix2.specialUnitary) :
    Γ.IsGaugeRep g (Γ.gaugeRep g) := by
  have := linkOrbits_nonempty Γ μ
  exact Classical.epsilon_spec ((hO _ _ (Γ.orbitSource (μ := μ)) (Γ.orbitTarget (μ := μ))).1 g)
theorem gaugeRepProperties_holds (hO : TwistedActionOperators.Statement)
    (hA : TwistedAverageStatement) : Γ.GaugeRepProperties μ := by
  have := linkOrbits_nonempty Γ μ
  have := vertexOrbits_nonempty Γ μ
  have hf := gaugeRep_spec Γ μ hO
  have hp : Γ.IsGaugeProjection (Γ.gaugeProjection μ) :=
    Classical.epsilon_spec (hA _ _ (Γ.orbitSource (μ := μ)) (Γ.orbitTarget (μ := μ))).1
  obtain ⟨hbij, hiso, hmul, -, hcomm⟩ :=
    (hO _ _ (Γ.orbitSource (μ := μ)) (Γ.orbitTarget (μ := μ))).2 Γ.gaugeRep hf
  obtain ⟨pint, pinner, psymm, pidem, prange, pcomm⟩ :=
    (hA _ _ (Γ.orbitSource (μ := μ)) (Γ.orbitTarget (μ := μ))).2 Γ.gaugeRep
      (Γ.gaugeProjection μ) hf hp
  exact
    { rep_formula := hf
      rep_unitary := fun g => ⟨hbij g, hiso g⟩
      rep_mul := hmul
      proj_formula := hp
      proj_integrable := pint
      proj_inner := pinner
      proj_symm := psymm
      proj_idempotent := pidem
      proj_range := prange
      commute_proj := pcomm
      kernelOp_commute := fun A hAc hAi g => hcomm A hAc hAi g }
variable {β : ℝ}
theorem boltzmann_exp_bounds (hE : SliceEnergyProperties.Statement) (hβ : 0 < β)
    (u : Γ.LinkOrbits μ → Matrices.ComplexMatrix2.specialUnitary) :
    (Complex.exp (-Γ.sliceEnergy β u)).im = 0 ∧ 0 ≤ (Complex.exp (-Γ.sliceEnergy β u)).re ∧
      (Complex.exp (-Γ.sliceEnergy β u)).re ≤ 1 := by
  obtain ⟨him, hre⟩ := (hE β hβ Γ μ).2.1 u
  have hreal : Complex.exp (-Γ.sliceEnergy β u) = ((Real.exp (-(Γ.sliceEnergy β u).re) : ℝ) : ℂ) := by
    have hv : Γ.sliceEnergy β u = (((Γ.sliceEnergy β u).re : ℝ) : ℂ) :=
      Complex.ext rfl (by simpa using him)
    rw [Complex.ofReal_exp, Complex.ofReal_neg, ← hv]
  rw [hreal, Complex.ofReal_im, Complex.ofReal_re]
  exact ⟨rfl, (Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hre)⟩
theorem boltzmannMultiplier_properties (hO : TwistedActionOperators.Statement)
    (hM : BoundedMultiplicationStatement)
    (hE : SliceEnergyProperties.Statement) (hβ : 0 < β) :
    Γ.BoltzmannProperties μ β ∧ ‖Γ.boltzmannMultiplier μ β‖ ≤ 1 := by
  have := linkOrbits_nonempty Γ μ
  obtain ⟨hex, hall⟩ := hM (Γ.LinkOrbits μ) (fun u => Complex.exp (-Γ.sliceEnergy β u))
    (hE β hβ Γ μ).1.neg.cexp (boltzmann_exp_bounds Γ μ hE hβ)
  have hf : Γ.IsBoltzmannMultiplier β (Γ.boltzmannMultiplier μ β) :=
    Classical.epsilon_spec hex
  obtain ⟨h0, h1, hn, hc⟩ := hall _ hf
  refine ⟨⟨hf, h0, h1, fun g => ?_⟩, hn⟩
  refine hc _ (Γ.orbitSource (μ := μ)) (Γ.orbitTarget (μ := μ)) g _ (gaugeRep_spec Γ μ hO g)
    fun u => ?_
  have hinv := (hE β hβ Γ μ).2.2 g⁻¹ u
  change Complex.exp (-Γ.sliceEnergy β (Γ.orbitGaugeAct g⁻¹ u)) = _
  rw [hinv]
theorem linkOperatorProperties_holds (hO : TwistedActionOperators.Statement)
    (hK : TwistInvariantKernelsStatement)
    (hR : SqrtLinkFacts.SqrtLinkKernelFacts) (hβ : 0 < β) :
    Γ.LinkOperatorProperties μ β := by
  have := linkOrbits_nonempty Γ μ
  obtain ⟨hk, -, -, -, -, hr, hb, -, hT, -⟩ := (hR β hβ).1 (Γ.LinkOrbits μ)
  obtain ⟨hinv, hbc, hpc⟩ := hK β hβ (Γ.LinkOrbits μ)
  obtain ⟨-, -, -, -, hc⟩ := (hO _ _ (Γ.orbitSource (μ := μ)) (Γ.orbitTarget (μ := μ))).2
    Γ.gaugeRep (gaugeRep_spec Γ μ hO)
  exact
    { link_traceClass := hT.2
      sqrt_hilbertSchmidt := hT.1
      link_symm := hb.2.1
      sqrt_symm := hr.2.1
      link_nonneg := hb.2.2.1
      sqrt_nonneg := hr.2.2.1
      link_real := hb.1
      sqrt_real := hr.1
      link_continuous := hbc
      sqrt_continuous := hk.2.2
      link_commute := hc (fun p => linkProductKernel β p.1 p.2) hbc fun g u u' =>
        (hinv _ (Γ.orbitSource (μ := μ)) (Γ.orbitTarget (μ := μ)) g u u').1
      sqrt_commute := hc (fun p => sqrtLinkKernel β p.1 p.2) hk.2.2 fun g u u' =>
        (hinv _ (Γ.orbitSource (μ := μ)) (Γ.orbitTarget (μ := μ)) g u u').2.1
      isotypic_commute := fun l => hc (fun p => isotypicKernel l p.1 p.2) (hpc l)
        fun g u u' => (hinv _ (Γ.orbitSource (μ := μ)) (Γ.orbitTarget (μ := μ)) g u u').2.2 l }
theorem transferProperties_holds (hO : TwistedActionOperators.Statement)
    (hA : TwistedAverageStatement)
    (hK : TwistInvariantKernelsStatement)
    (hM : BoundedMultiplicationStatement)
    (hE : SliceEnergyProperties.Statement)
    (hL : TransferAlgebraStatement)
    (hR : SqrtLinkFacts.SqrtLinkKernelFacts)
    (hS : SeveralVariables.SeveralVariablesFacts) (hβ : 0 < β) :
    Γ.TransferProperties μ β := by
  have := linkOrbits_nonempty Γ μ
  have hG := gaugeRepProperties_holds Γ μ hO hA
  obtain ⟨hW, hWn⟩ := boltzmannMultiplier_properties Γ μ hO hM hE hβ
  have hB := linkOperatorProperties_holds Γ μ hO hK hR hβ
  have hRP := hG.commute_proj _ hB.sqrt_symm hB.sqrt_commute
  have hMP := hG.commute_proj _ hW.nonneg.1 hW.commute
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9⟩ :=
    hL (Γ.LinkOrbits μ) (sqrtPeterWeylCoeff β) (sqrtLinkOperator β (Γ.LinkOrbits μ))
      (Γ.gaugeProjection μ) (Γ.boltzmannMultiplier μ β) hB.sqrt_symm hG.proj_symm
      hG.proj_idempotent hRP hW.nonneg hWn hMP
      (norm_sqrtLinkOperator_peterWeylVec_le _ hS hR hβ) (summable_sqrtPeterWeylCoeff_sq _ hS hR hβ)
      (summable_sqrtPeterWeylCoeff _ hS hR hβ)
  exact
    { sqrt_commute_proj := hRP
      half_symm := t1
      half_hilbertSchmidt := t2
      transfer_eq_sandwich := t3
      transfer_eq_factor := t4
      transfer_nonneg := t5
      transfer_symm := t6
      transfer_traceClass := t7
      entry_le := t8
      entry_summable := t9 }
end CubicTorus
section Block
variable {μ : Fin 4} (B : Block μ)
def blockSource (e : B.LinkType) : B.vertices := ⟨e.1.source, (B.links_subset_linksWithin e.2).1⟩
def blockTarget (e : B.LinkType) : B.vertices := ⟨e.1.target, (B.links_subset_linksWithin e.2).2⟩
theorem blockLinks_nonempty : Nonempty B.LinkType := by
  obtain ⟨e, he⟩ := B.links_nonempty
  exact ⟨⟨e, Finset.mem_coe.mpr he⟩⟩
theorem blockOperatorProperties_holds (hO : TwistedActionOperators.Statement)
    (hK : TwistInvariantKernelsStatement)
    (hR : SqrtLinkFacts.SqrtLinkKernelFacts) {β : ℝ} (hβ : 0 < β) :
    B.OperatorProperties β := by
  have := blockLinks_nonempty B
  have hf : ∀ g : B.vertices → Matrices.ComplexMatrix2.specialUnitary,
      IsBlockGaugeRep B g (blockGaugeRep B g) := fun g =>
    Classical.epsilon_spec ((hO _ _ (blockSource B) (blockTarget B)).1 g)
  obtain ⟨hbij, hiso, hmul, -, hc⟩ :=
    (hO _ _ (blockSource B) (blockTarget B)).2 (blockGaugeRep B) hf
  obtain ⟨hk, -, -, -, -, hr, hb, -, hT, -⟩ := (hR β hβ).1 B.LinkType
  obtain ⟨hinv, hbc, hpc⟩ := hK β hβ B.LinkType
  exact
    { rep_formula := hf
      rep_unitary := fun g => ⟨hbij g, hiso g⟩
      rep_mul := hmul
      kernelOp_commute := fun A hAc hAi g => hc A hAc hAi g
      link_continuous := hbc
      sqrt_continuous := hk.2.2
      isotypic_continuous := hpc
      link_invariant := fun g u u' => (hinv _ (blockSource B) (blockTarget B) g u u').1
      sqrt_invariant := fun g u u' => (hinv _ (blockSource B) (blockTarget B) g u u').2.1
      isotypic_invariant := fun l g u u' => (hinv _ (blockSource B) (blockTarget B) g u u').2.2 l
      link_traceClass := hT.2
      sqrt_hilbertSchmidt := hT.1
      link_symm := hb.2.1
      sqrt_symm := hr.2.1
      link_nonneg := hb.2.2.1
      sqrt_nonneg := hr.2.2.1
      link_real := hb.1
      sqrt_real := hr.1 }
end Block
theorem statement_holds (hO : TwistedActionOperators.Statement)
    (hA : TwistedAverageStatement)
    (hK : TwistInvariantKernelsStatement)
    (hM : BoundedMultiplicationStatement)
    (hE : SliceEnergyProperties.Statement)
    (hL : TransferAlgebraStatement)
    (hR : SqrtLinkFacts.SqrtLinkKernelFacts)
    (hS : SeveralVariables.SeveralVariablesFacts) : Statement := fun _ hβ =>
  ⟨fun Γ μ => ⟨gaugeRepProperties_holds Γ μ hO hA, (boltzmannMultiplier_properties Γ μ hO hM hE hβ).1,
      linkOperatorProperties_holds Γ μ hO hK hR hβ,
      transferProperties_holds Γ μ hO hA hK hM hE hL hR hS hβ⟩,
    fun _ B => blockOperatorProperties_holds B hO hK hR hβ⟩
end TransferOperators.CubicTorusOperators
end YangMills.Construction
end
