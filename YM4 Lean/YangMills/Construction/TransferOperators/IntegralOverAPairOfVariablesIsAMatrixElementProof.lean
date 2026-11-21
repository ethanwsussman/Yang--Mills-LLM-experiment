import YangMills.Construction.TransferOperators.CycleOfKernelsIsATraceProof
import YangMills.Construction.TransferOperators.FactsOfTheOperatorsOfACubicTorusProof
import YangMills.Construction.TransferOperators.PeriodicStatesHaarMeasureCubicLatticesAndIntegralOperators
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.SpinHarmonics
open YangMills.Construction.TransferOperators.GibbsHaarKernels
noncomputable section
namespace YangMills.Construction.TransferOperators.PairIntegralMatrixEntry
variable (Γ : CubicPeriodSublattice) {μ : Fin 4}
theorem linkOrbits_nonempty (μ : Fin 4) : Nonempty (Γ.LinkOrbits μ) := by apply _root_.YangMills.Construction.TransferOperators.CubicTorusOperators.linkOrbits_nonempty <;> assumption
theorem orbitGaugeAct_inv_orbitGaugeAct
    (g : Γ.VertexOrbits μ → Matrices.ComplexMatrix2.specialUnitary)
    (u : Γ.LinkOrbits μ → Matrices.ComplexMatrix2.specialUnitary) :
    Γ.orbitGaugeAct g⁻¹ (Γ.orbitGaugeAct g u) = u := by
  funext e
  simp [CubicPeriodSublattice.orbitGaugeAct, mul_assoc]
theorem continuous_pairIntegrand {β : ℝ} (hV : Continuous (Γ.sliceEnergy (μ := μ) β))
    (a' a : PeterWeylIndex (Γ.LinkOrbits μ)) :
    Continuous (Γ.pairIntegrand β a' a) := by apply _root_.YangMills.Construction.TransferOperators.CubicPeriodSublattice.continuous_pairIntegrand <;> assumption
theorem inner_gaugeRep_boltzmann {β : ℝ}
    (hH : HaarPiInvariance (Γ.LinkOrbits μ)) (hG : Γ.GaugeRepProperties μ)
    (hW : Γ.BoltzmannProperties μ β) (a' a : PeterWeylIndex (Γ.LinkOrbits μ))
    (g : Γ.VertexOrbits μ → Matrices.ComplexMatrix2.specialUnitary) :
    inner ℂ (peterWeylVec a') (Γ.gaugeRep g
        (Γ.boltzmannMultiplier μ β (peterWeylVec a))) =
      ∫ u, Γ.pairIntegrand β a' a (g, u) ∂Matrices.ComplexMatrix2.haarPi (Γ.LinkOrbits μ) := by
  set m := Matrices.ComplexMatrix2.haarPi (Γ.LinkOrbits μ) with hm
  have hT : MeasurePreserving (Γ.orbitGaugeAct g) m m :=
    hH.1 (fun e => g (Γ.orbitSource e)) fun e => (g (Γ.orbitTarget e))⁻¹
  set Φ := Γ.boltzmannMultiplier μ β (peterWeylVec a) with hΦ
  set Ψ := Γ.gaugeRep g Φ with hΨ
  have hψ' : (peterWeylVec a' : (Γ.LinkOrbits μ → Matrices.ComplexMatrix2.specialUnitary) → ℂ)
      =ᵐ[m] peterWeylFn a' :=
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) m (peterWeylFn a')
  have hψ : (peterWeylVec a : (Γ.LinkOrbits μ → Matrices.ComplexMatrix2.specialUnitary) → ℂ)
      =ᵐ[m] peterWeylFn a :=
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) m (peterWeylFn a)
  have hMeas : AEStronglyMeasurable
      (fun u => star (peterWeylFn a' u) *
        (Ψ : (Γ.LinkOrbits μ → Matrices.ComplexMatrix2.specialUnitary) → ℂ) u) m :=
    ((continuous_star.comp (peterWeylFn a').continuous).aestronglyMeasurable).mul
      (Lp.aestronglyMeasurable Ψ)
  have e₁ : inner ℂ (peterWeylVec a') Ψ =
      ∫ u, star (peterWeylFn a' u) *
        (Ψ : (Γ.LinkOrbits μ → Matrices.ComplexMatrix2.specialUnitary) → ℂ) u ∂m := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hψ'] with u hu
    rw [hu, RCLike.inner_apply, mul_comm]
    rfl
  rw [e₁, ← hT.map_eq, integral_map hT.aemeasurable (by rw [hT.map_eq]; exact hMeas)]
  refine integral_congr_ae ?_
  have h₁ := hT.quasiMeasurePreserving.ae_eq_comp (hG.rep_formula g Φ)
  have h₂ := hW.formula (peterWeylVec a)
  filter_upwards [h₁, h₂, hψ] with u c₁ c₂ c₃
  have c₁' : (Ψ : (Γ.LinkOrbits μ → Matrices.ComplexMatrix2.specialUnitary) → ℂ)
      (Γ.orbitGaugeAct g u) =
      (Φ : (Γ.LinkOrbits μ → Matrices.ComplexMatrix2.specialUnitary) → ℂ) u := by
    have := c₁
    simp only [Function.comp_apply, orbitGaugeAct_inv_orbitGaugeAct] at this
    exact this
  rw [c₁', hΦ, c₂, c₃]
  simp only [CubicPeriodSublattice.pairIntegrand]
  ring
theorem holds (hFacts : CubicTorusOperators.Statement)
    (hRoot : SqrtLinkFacts.SqrtLinkKernelFacts)
    (hSeveral : SpinHarmonics.SeveralVariables.SeveralVariablesFacts)
    (hEnergy : SliceEnergyProperties.Statement)
    (hStates : GibbsHaarKernels.Statement) :
    Statement := by
  intro β hβ Γ μ a' a
  have := linkOrbits_nonempty Γ μ
  obtain ⟨hG, hW, hB, hL⟩ := (hFacts β hβ).1 Γ μ
  have hV := (hEnergy β hβ Γ μ).1
  have hH : HaarPiInvariance (Γ.LinkOrbits μ) := hStates.2.1 _
  have hcont := continuous_pairIntegrand Γ hV a' a
  have hInt : Integrable (Γ.pairIntegrand β a' a)
      ((Matrices.ComplexMatrix2.haarPi (Γ.VertexOrbits μ)).prod
        (Matrices.ComplexMatrix2.haarPi (Γ.LinkOrbits μ))) :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨hInt, ?_⟩
  obtain ⟨-, -, -, hE, -⟩ := (hRoot β hβ).1 (Γ.LinkOrbits μ)
  have hsqrt : ∀ k : PeterWeylIndex (Γ.LinkOrbits μ),
      sqrtLinkOperator β (Γ.LinkOrbits μ) (peterWeylVec k) =
        (sqrtPeterWeylCoeff β k : ℂ) • peterWeylVec k := fun k => by
    have hB' := (hSeveral (Γ.LinkOrbits μ) (spins k) ⟨0⟩).1
    have hmem : peterWeylFn k ∈ prodCoeffSpan (spins k) := by
      rw [← hB'.2.2.1]
      exact Submodule.subset_span ⟨k, rfl, rfl⟩
    exact (hE (spins k) (peterWeylFn k) hmem).1
  rw [integral_prod _ hInt, peterWeylEntry, hL.transfer_eq_factor]
  simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
  rw [hsqrt a, hB.sqrt_symm, hsqrt a', map_smul, map_smul, inner_smul_left,
    inner_smul_right, hG.proj_inner]
  simp only [inner_gaugeRep_boltzmann Γ hH hG hW a' a, Complex.conj_ofReal]
  ring
end YangMills.Construction.TransferOperators.PairIntegralMatrixEntry
end
