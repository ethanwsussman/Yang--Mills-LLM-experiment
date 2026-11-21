import YangMills.Construction.PeriodicOperators.ProductsOfJetsProof
import YangMills.Construction.PeriodicOperators.NormsAndTracesOfMatricesOnTheClasses
import YangMills.Construction.PeriodicOperators.RiemannSumsAndShiftsProof
import YangMills.Construction.PeriodicOperators.ShiftInTheTraceOfTwoJets
import YangMills.Construction.PeriodicOperators.StripsAndFiniteNormsOfJets
import Mathlib
set_option autoImplicit false
open Set Topology
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators.JetTraceShift
open JetQuad (IsJet)
open RiemannSums (HolomorphicNearStrip PeriodicOnStrip BoundedOnStrip periodLattice)
section Phases
variable {D : PeriodicData}
theorem phaseMul_isUnit (hD : IsPeriodic D) (e : Fin 4 → ℤ) :
    IsUnit (phaseMul D e : Module.End ℂ (D.UnitQuot → ℂ)) := by apply _root_.YangMills.Construction.PeriodicOperators.MatrixFunctionKernel.phaseMul_isUnit <;> assumption
end Phases
section Traces
theorem trace_comp_eq_sum_entries {J J' : Type} [Fintype J] [Fintype J']
    (M : (J' → ℂ) →ₗ[ℂ] (J → ℂ)) (N : (J → ℂ) →ₗ[ℂ] (J' → ℂ)) :
    LinearMap.trace ℂ (J → ℂ) (M.comp N) =
      ∑ c, ∑ c', linearMapEntry M c c' * linearMapEntry N c' c := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ J), LinearMap.toMatrix_eq_toMatrix',
    LinearMap.toMatrix'_comp]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, LinearMap.toMatrix'_apply]
  rfl
theorem trace_phaseMul_conj {D D' : PeriodicData} (hD : IsPeriodic D)
    (hD' : IsPeriodic D') (e : Fin 4 → ℤ) (A : QuotHom D' D) (B : QuotHom D D') :
    LinearMap.trace ℂ (D.UnitQuot → ℂ)
        (((quotHomInverse (phaseMul D e)).comp
            (A.comp (phaseMul D' e))).comp
          ((quotHomInverse (phaseMul D' e)).comp
            (B.comp (phaseMul D e)))) =
      LinearMap.trace ℂ (D.UnitQuot → ℂ) (A.comp B) := by
  have := hD.finite_quot
  have hE : (phaseMul D e : Module.End ℂ (D.UnitQuot → ℂ)) *
      quotHomInverse (phaseMul D e) = 1 :=
    Ring.mul_inverse_cancel _ (phaseMul_isUnit hD e)
  have hE' : (phaseMul D' e : Module.End ℂ (D'.UnitQuot → ℂ)) *
      quotHomInverse (phaseMul D' e) = 1 :=
    Ring.mul_inverse_cancel _ (phaseMul_isUnit hD' e)
  have hE'v : ∀ v, phaseMul D' e (quotHomInverse (phaseMul D' e) v) = v :=
    fun v => LinearMap.congr_fun hE' v
  have hshape : (((quotHomInverse (phaseMul D e)).comp
        (A.comp (phaseMul D' e))).comp
      ((quotHomInverse (phaseMul D' e)).comp (B.comp (phaseMul D e)))) =
      (quotHomInverse (phaseMul D e) : Module.End ℂ (D.UnitQuot → ℂ)) *
        ((A.comp B : Module.End ℂ (D.UnitQuot → ℂ)) * phaseMul D e) := by
    refine LinearMap.ext fun f => ?_
    simp only [LinearMap.comp_apply, Module.End.mul_apply, hE'v]
  rw [hshape, LinearMap.trace_mul_comm, mul_assoc, hE, mul_one]
end Traces
section Holomorphy
variable {U : Set (Fin 4 → ℂ)} {f g : (Fin 4 → ℂ) → ℂ}
theorem isHolomorphicIn_scalar_iff :
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) U (fun z _ => f z) ↔
      IsOpen U ∧ ContinuousOn f U ∧ ∀ a ∈ U, ∀ j : Fin 4, ∀ᶠ ζ in 𝓝 (0 : ℂ),
        DifferentiableAt ℂ
          (fun ζ : ℂ => f (a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j)) ζ := by apply _root_.YangMills.Construction.PeriodicOperators.MatrixFunctionKernel.isHolomorphicIn_scalar_iff <;> assumption
theorem isHolomorphicIn_scalar_mono {U' : Set (Fin 4 → ℂ)} (hU' : IsOpen U') (hsub : U' ⊆ U)
    (h : Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) U (fun z _ => f z)) :
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) U' (fun z _ => f z) := by
  obtain ⟨-, hc, hd⟩ := isHolomorphicIn_scalar_iff.mp h
  exact isHolomorphicIn_scalar_iff.mpr ⟨hU', hc.mono hsub, fun a ha j => hd a (hsub ha) j⟩
theorem isHolomorphicIn_scalar_comp_sub (p : Fin 4 → ℂ)
    (h : Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) U (fun z _ => f z)) :
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) ((fun κ => κ - p) ⁻¹' U)
      (fun z _ => f (z - p)) := by
  obtain ⟨hU, hc, hd⟩ := isHolomorphicIn_scalar_iff.mp h
  have hsubc : Continuous fun κ : Fin 4 → ℂ => κ - p := continuous_id.sub continuous_const
  refine isHolomorphicIn_scalar_iff.mpr ⟨hU.preimage hsubc, hc.comp hsubc.continuousOn fun _ h => h,
    fun a ha j => (hd (a - p) ha j).mono fun ζ hζ => ?_⟩
  have heq : (fun ζ : ℂ => f (a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j - p)) =
      fun ζ : ℂ => f (a - p + ζ • Coordinates.ComplexCoordinates.stdBasisVector j) := by
    funext ζ
    rw [add_sub_right_comm]
  rw [heq]
  exact hζ
theorem isHolomorphicIn_scalar_mul
    (hf : Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) U (fun z _ => f z))
    (hg : Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) U (fun z _ => g z)) :
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) U (fun z _ => f z * g z) := by apply _root_.YangMills.Construction.PeriodicOperators.MatrixFunctionKernel.isHolomorphicIn_scalar_mul <;> assumption
theorem isHolomorphicIn_scalar_sum {ι : Type} (s : Finset ι) (F : ι → (Fin 4 → ℂ) → ℂ)
    (hU : IsOpen U)
    (h : ∀ i ∈ s, Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) U (fun z _ => F i z)) :
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) U (fun z _ => ∑ i ∈ s, F i z) := by apply _root_.YangMills.Construction.PeriodicOperators.JetProducts.ScalarHolomorphicOn.sum <;> assumption
end Holomorphy
section Points
variable {δ : ℝ} {p κ : Fin 4 → ℂ}
theorem sub_mem_imStrip_two_mul (hκ : κ ∈ imStrip δ) (hp : p ∈ imStrip δ) :
    κ - p ∈ imStrip (2 * δ) := fun μ => by
  have h1 := abs_le.mp (hκ μ)
  have h2 := abs_le.mp (hp μ)
  refine abs_le.mpr ?_
  simp only [Pi.sub_apply, Complex.sub_im]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
theorem mem_imStrip_two_mul (hδ : 0 < δ) (hκ : κ ∈ imStrip δ) : κ ∈ imStrip (2 * δ) := fun μ =>
  (hκ μ).trans (by linarith)
theorem sub_mem_stripAddShift (hδ : 0 < δ) (hκ : κ ∈ imStrip δ) (hp : p ∈ imStrip δ) :
    κ - p ∈ stripAddShift δ p :=
  ⟨sub_mem_imStrip_two_mul hκ hp, by rw [sub_add_cancel]; exact mem_imStrip_two_mul hδ hκ⟩
theorem mem_stripSubShift (hδ : 0 < δ) (hκ : κ ∈ imStrip δ) (hp : p ∈ imStrip δ) :
    κ ∈ stripSubShift δ p :=
  ⟨mem_imStrip_two_mul hδ hκ, sub_mem_imStrip_two_mul hκ hp⟩
theorem toComplexVec_mem_imStrip (hδ : 0 < δ) (y : InfiniteLattice.AmbientSpace) :
    toComplexVec y ∈ imStrip δ := fun μ => by
  simpa [toComplexVec] using hδ.le
theorem toComplexVec_add_mem_imStrip (hp : p ∈ imStrip δ) (y : InfiniteLattice.AmbientSpace) :
    toComplexVec y + p ∈ imStrip δ := by apply _root_.YangMills.Construction.PeriodicOperators.RiemannSums.toComplexVec_add_mem_imStrip <;> assumption
theorem continuous_toComplexVec :
    Continuous (toComplexVec : InfiniteLattice.AmbientSpace → Fin 4 → ℂ) := by apply _root_.YangMills.Construction.PeriodicOperators.EntriesDets.continuous_toComplexVec <;> assumption
end Points
variable {D D' : PeriodicData} {δ : ℝ} {p : Fin 4 → ℂ}
  {T : JetQuad D' D} {S : JetQuad D D'}
theorem shiftedTrace_holomorphicNearStrip (hD : IsPeriodic D) (hD' : IsPeriodic D')
    (hδ : 0 < δ) (hp : p ∈ imStrip δ) (hT : IsJet δ p T) (hS : IsJet δ p S) :
    HolomorphicNearStrip δ (shiftedTrace p T S) := by
  obtain ⟨U₁, hU₁, hsub₁, h₁⟩ := hT.holo_f10
  obtain ⟨U₂, hU₂, hsub₂, h₂⟩ := hS.holo_f01
  have := hD.finite_quot
  have := hD'.finite_quot
  have := Fintype.ofFinite D.UnitQuot
  have := Fintype.ofFinite D'.UnitQuot
  have hsubc : Continuous fun κ : Fin 4 → ℂ => κ - p := continuous_id.sub continuous_const
  have hU : IsOpen ((fun κ : Fin 4 → ℂ => κ - p) ⁻¹' U₁ ∩ U₂) :=
    (hU₁.preimage hsubc).inter hU₂
  refine ⟨(fun κ => κ - p) ⁻¹' U₁ ∩ U₂, fun κ hκ =>
    ⟨hsub₁ (sub_mem_stripAddShift hδ hκ hp), hsub₂ (mem_stripSubShift hδ hκ hp)⟩, ?_⟩
  have hshape : (fun (z : Fin 4 → ℂ) (_ : Fin 1) => shiftedTrace p T S z) =
      fun z _ => ∑ c, ∑ c', linearMapEntry (T.f10 (z - p)) c c' * linearMapEntry (S.f01 z) c' c := by
    funext z _
    exact trace_comp_eq_sum_entries _ _
  show Coordinates.ComplexCoordinates.IsHolomorphicIn _
    (fun (z : Fin 4 → ℂ) (_ : Fin 1) => shiftedTrace p T S z)
  rw [hshape]
  refine isHolomorphicIn_scalar_sum _ _ hU fun c _ => isHolomorphicIn_scalar_sum _ _ hU
    fun c' _ => isHolomorphicIn_scalar_mul ?_ ?_
  · exact isHolomorphicIn_scalar_mono hU inter_subset_left
      (isHolomorphicIn_scalar_comp_sub p (h₁ c c'))
  · exact isHolomorphicIn_scalar_mono hU inter_subset_right (h₂ c' c)
theorem shiftedTrace_periodicOnStrip (hD : IsPeriodic D) (hD' : IsPeriodic D')
    (hδ : 0 < δ) (hp : p ∈ imStrip δ) (hT : IsJet δ p T) (hS : IsJet δ p S) :
    PeriodicOnStrip δ (shiftedTrace p T S) := by
  rintro κ hκ q ⟨n, hn⟩
  have hpt : κ + toComplexVec q = addTwoPiInt κ n := by
    funext μ
    have := hn μ
    simp only [Pi.add_apply, toComplexVec, addTwoPiInt, this]
    push_cast
    ring
  have hpt' : κ + toComplexVec q - p = addTwoPiInt (κ - p) n := by
    rw [hpt]
    funext μ
    simp only [Pi.sub_apply, addTwoPiInt]
    ring
  unfold shiftedTrace
  rw [hpt', hpt, hT.quasiPeriodic_f10 n _ (sub_mem_stripAddShift hδ hκ hp),
    hS.quasiPeriodic_f01 n _ (mem_stripSubShift hδ hκ hp)]
  exact trace_phaseMul_conj hD hD' n _ _
theorem shiftedTrace_boundedOnStrip (hN : QuotMatrixNorms.Claim)
    (hF : StripJetNorms.Claim)
    (hD : IsPeriodic D) (hD' : IsPeriodic D')
    (hδ : 0 < δ) (hp : p ∈ imStrip δ) (hT : IsJet δ p T) (hS : IsJet δ p S) :
    BoundedOnStrip δ (shiftedTrace p T S) := by
  obtain ⟨C, hC, htr⟩ := (hN D D D hD hD hD).2.2.2
  have hprod := (hN D' D D hD' hD hD).2.1
  have hfT := ((hF D' D hD' hD δ p hδ hp).2 T hT).2.1
  have hfS := ((hF D D' hD hD' δ p hδ hp).2 S hS).2.2.1
  set A := ⨆ κ ∈ stripAddShift δ p, quotHomNorm (T.f10 κ) with hA
  set B := ⨆ κ ∈ stripSubShift δ p, quotHomNorm (S.f01 κ) with hB
  refine ⟨C * (A * B).toReal, fun κ hκ => (htr _).trans ?_⟩
  refine mul_le_mul_of_nonneg_left ?_ hC
  refine ENNReal.toReal_mono (ENNReal.mul_lt_top hfT hfS).ne ((hprod _ _).trans ?_)
  exact mul_le_mul'
    (le_iSup₂ (f := fun κ (_ : κ ∈ stripAddShift δ p) => quotHomNorm (T.f10 κ)) _
      (sub_mem_stripAddShift hδ hκ hp))
    (le_iSup₂ (f := fun κ (_ : κ ∈ stripSubShift δ p) => quotHomNorm (S.f01 κ)) _
      (mem_stripSubShift hδ hκ hp))
theorem claim_holds (hR : RiemannSums.Claim) (hF : StripJetNorms.Claim)
    (hN : QuotMatrixNorms.Claim) : Claim := by
  intro δ p hδ hp D D' hD hD' T S hT hS
  have hhol := shiftedTrace_holomorphicNearStrip hD hD' hδ hp hT hS
  have hcont : ∃ U, imStrip δ ⊆ U ∧ ContinuousOn (shiftedTrace p T S) U := by
    obtain ⟨U, hsub, hU⟩ := hhol
    exact ⟨U, hsub, (isHolomorphicIn_scalar_iff.mp hU).2.1⟩
  obtain ⟨U, hsub, hc⟩ := hcont
  refine ⟨hc.comp_continuous continuous_toComplexVec fun y => hsub (toComplexVec_mem_imStrip hδ y),
    hc.comp_continuous (continuous_toComplexVec.add continuous_const)
      fun y => hsub (toComplexVec_add_mem_imStrip hp y), ?_⟩
  exact (hR 1 δ (shiftedTrace p T S) one_pos hδ hhol (shiftedTrace_periodicOnStrip hD hD' hδ hp hT hS)
    (shiftedTrace_boundedOnStrip hN hF hD hD' hδ hp hT hS)).2 p hp
end YangMills.Construction.PeriodicOperators.JetTraceShift
end
