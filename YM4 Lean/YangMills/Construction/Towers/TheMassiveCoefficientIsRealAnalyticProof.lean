import YangMills.Construction.Coordinates.HolomorphicIffDifferentiable
import YangMills.Construction.OneLoopLaw.CoefficientOfATemperedFunctional
import YangMills.Construction.PeriodicOperators.FunctionalDeterminesItsPolarisationSymbol
import YangMills.Construction.Towers.TheMassiveCoefficientIsRealAnalytic
import YangMills.Construction.Towers.TheMassiveFamilyIsTempered
import YangMills.Construction.Towers.TheMassiveSymbolsAreHolomorphicInTheNumberAndTheMomentum
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.MassiveStiffnessFunctions.RealAnalyticity
open YangMills.Construction.Coordinates YangMills.Construction.Coordinates.ComplexCoordinates Set Filter
open scoped Topology
open YangMills.Construction.PeriodicOperators YangMills.Construction.PeriodicOperators.Tempered
open YangMills.Construction.Coordinates.ComplexCoordinates.LogDetSecondDeriv (IsHolomorphicScalarIn asLine)
def realSlicePoint (z s t : ℝ) : ComplexCoordinates 5 :=
  ((z : ℂ) • stdBasisVector (0 : Fin 5) + s • stdBasisVector (1 : Fin 5)) + t • stdBasisVector (2 : Fin 5)
theorem realSlicePoint_mem_realLocus (z s t : ℝ) : realSlicePoint z s t ∈ realLocus 5 := by
  intro j
  fin_cases j <;> simp [realSlicePoint, stdBasisVector]
theorem realSlicePoint_apply_zero (z s t : ℝ) : realSlicePoint z s t 0 = (z : ℂ) := by
  simp [realSlicePoint, stdBasisVector]
theorem realSlicePoint_apply_succ (z s t : ℝ) :
    (fun i : Fin 4 => realSlicePoint z s t i.succ) =
      toComplexVec (Pi.single 0 s + Pi.single 1 t) := by
  funext i
  fin_cases i <;> simp [realSlicePoint, stdBasisVector, toComplexVec]
theorem hasDerivAt_apply_add_smul {N N' : ℕ} {f : ComplexCoordinates N → ComplexCoordinates N'}
    {a : ComplexCoordinates N} (v : ComplexCoordinates N) (hf : DifferentiableAt ℝ f a) (j : Fin N') :
    HasDerivAt (fun t : ℝ => f (a + t • v) j) (fderiv ℝ f a v j) 0 :=
  hasDerivAt_pi.1 (hf.hasFDerivAt.hasLineDerivAt v) j
theorem differentiableAt_of_isHolomorphicIn
    (hD : ComplexCoordinates.HolomorphicDifferentiable.HolomorphicIffDifferentiableStatement) {N N' : ℕ}
    {O : Set (ComplexCoordinates N)} {f : ComplexCoordinates N → ComplexCoordinates N'}
    (hf : IsHolomorphicIn O f) {a : ComplexCoordinates N} (ha : a ∈ O) : DifferentiableAt ℂ f a :=
  ((hD N N' O f hf.1).1 hf a ha).differentiableAt (hf.1.mem_nhds ha)
def partialTwo (f : ComplexCoordinates 5 → ComplexCoordinates 1) (w : ComplexCoordinates 5) :
    ComplexCoordinates 1 :=
  fderiv ℝ f w (stdBasisVector (2 : Fin 5))
def partialOneTwo (f : ComplexCoordinates 5 → ComplexCoordinates 1) (w : ComplexCoordinates 5) :
    ComplexCoordinates 1 :=
  fderiv ℝ (partialTwo f) w (stdBasisVector (1 : Fin 5))
theorem secondPartialAtZero_eq_partialOneTwo
    (hD : ComplexCoordinates.HolomorphicDifferentiable.HolomorphicIffDifferentiableStatement)
    (hD' : SeparatedFrame.HolomorphicDerivatives.Claim)
    {O : Set (ComplexCoordinates 5)} {H : ComplexCoordinates 5 → ℂ}
    (hH : IsHolomorphicIn O (asLine H)) (g : (Fin 4 → ℂ) → ℂ) (z : ℝ)
    (hb : (z : ℂ) • stdBasisVector (0 : Fin 5) ∈ O)
    (hg : ∀ s t : ℝ, realSlicePoint z s t ∈ O →
      H (realSlicePoint z s t) = g (toComplexVec (Pi.single 0 s + Pi.single 1 t))) :
    OneLoopLaw.TemperedStiffness.secondPartialAtZero g 0 1 =
      partialOneTwo (asLine H) ((z : ℂ) • stdBasisVector (0 : Fin 5)) 0 := by
  have hf₁ : IsHolomorphicIn O (partialTwo (asLine H)) :=
    (hD' 5 1 O (asLine H) hH).1 (stdBasisVector (2 : Fin 5))
  have hcont : Continuous fun q : ℝ × ℝ => realSlicePoint z q.1 q.2 := by
    unfold realSlicePoint
    fun_prop
  have hzero : realSlicePoint z 0 0 = (z : ℂ) • stdBasisVector (0 : Fin 5) := by
    simp [realSlicePoint]
  have hev : ∀ᶠ q : ℝ × ℝ in 𝓝 ((0 : ℝ), (0 : ℝ)), realSlicePoint z q.1 q.2 ∈ O :=
    hcont.continuousAt.eventually_mem (hH.1.mem_nhds (by simpa [hzero] using hb))
  have key : ∀ᶠ s : ℝ in 𝓝 (0 : ℝ),
      deriv (fun t : ℝ => g (toComplexVec (Pi.single 0 s + Pi.single 1 t))) 0 =
        partialTwo (asLine H)
          ((z : ℂ) • stdBasisVector (0 : Fin 5) + s • stdBasisVector (1 : Fin 5)) 0 := by
    filter_upwards [hev.curry_nhds] with s hs
    have hmem : (z : ℂ) • stdBasisVector (0 : Fin 5) + s • stdBasisVector (1 : Fin 5) ∈ O := by
      simpa [realSlicePoint] using hs.self_of_nhds
    have heq : (fun t : ℝ => g (toComplexVec (Pi.single 0 s + Pi.single 1 t))) =ᶠ[𝓝 0]
        fun t : ℝ => asLine H (((z : ℂ) • stdBasisVector (0 : Fin 5) + s • stdBasisVector (1 : Fin 5)) +
          t • stdBasisVector (2 : Fin 5)) 0 := by
      filter_upwards [hs] with t ht
      exact (hg s t ht).symm
    rw [heq.deriv_eq]
    exact (hasDerivAt_apply_add_smul _
      ((differentiableAt_of_isHolomorphicIn hD hH hmem).restrictScalars ℝ) 0).deriv
  unfold OneLoopLaw.TemperedStiffness.secondPartialAtZero
  have hcancelled' : (fun s : ℝ => deriv (fun t : ℝ =>
      g (toComplexVec (Pi.single 0 s + Pi.single 1 t))) 0) =ᶠ[𝓝 0]
      fun s : ℝ => partialTwo (asLine H)
        ((z : ℂ) • stdBasisVector (0 : Fin 5) + s • stdBasisVector (1 : Fin 5)) 0 := key
  rw [hcancelled'.deriv_eq]
  exact (hasDerivAt_apply_add_smul _
    ((differentiableAt_of_isHolomorphicIn hD hf₁ hb).restrictScalars ℝ) 0).deriv
theorem massiveStiffness_eq_neg_secondPartialAtZero
    (hC : OneLoopLaw.TemperedStiffness.TemperedStiffnessClaim)
    (hU : PeriodicOperators.Tempered.HessianSymbolDetermined.Claim)
    (hT : MassiveOpFunctions.Tempered.MassiveFamilyTempered) {L : ℕ} (hL : 0 < L)
    (hs : Conventions.IsAdmissibleBlockingFactor L)
    {z : ℝ} (hz : 0 < z) :
    ((massiveStiffness hL z : ℝ) : ℂ) =
      -OneLoopLaw.TemperedStiffness.secondPartialAtZero
        (hessianSymbol L (massiveFieldFamily L z) 0 1) 0 1 := by
  obtain ⟨hF, δ, π, e, hc⟩ := (hT L hs z hz).1
  obtain ⟨-, -, -, b, -, -, hform⟩ := hC L hL hs _ δ π e hF hc
  have hmixed := (hform 0 1 (by decide)).neg_secondPartial_mixed
  obtain ⟨P, hP, -⟩ := (hU L hs _ ⟨hF, δ, π, e, hc⟩).2
  have hsymbol : IsHessianSymbol L (massiveFieldFamily L z)
      (hessianSymbol L (massiveFieldFamily L z)) := Classical.epsilon_spec ⟨P, hP⟩
  have hreal : ∀ y : InfiniteLattice.AmbientSpace, π 0 1 (toComplexVec y) =
      hessianSymbol L (massiveFieldFamily L z) 0 1 (toComplexVec y) := fun y =>
    (hsymbol δ π e hc 0 1 (fun μ => by simpa [toComplexVec] using hc.delta_pos.le)).symm
  simp only [OneLoopLaw.TemperedStiffness.secondPartialAtZero, hreal] at hmixed ⊢
  exact hmixed.symm
theorem massiveStiffness_analytic
    (hD : ComplexCoordinates.HolomorphicDifferentiable.HolomorphicIffDifferentiableStatement)
    (hD' : SeparatedFrame.HolomorphicDerivatives.Claim)
    (hC : OneLoopLaw.TemperedStiffness.TemperedStiffnessClaim)
    (hU : PeriodicOperators.Tempered.HessianSymbolDetermined.Claim)
    (hT : MassiveOpFunctions.Tempered.MassiveFamilyTempered) (hS : MassiveLogDet.SymbolHolomorphy) :
    StiffnessAnalytic := by
  intro L hL hs z₀ hz₀
  have hz₀ : 0 < z₀ := hz₀
  obtain ⟨O, ⟨w₀, hw₀, hw₀0, hw₀s⟩, H, hH, hHeq⟩ := hS L hs 0 1 z₀ hz₀ 0
  have hH : IsHolomorphicIn O (asLine H) := hH
  have hbase : (z₀ : ℂ) • stdBasisVector (0 : Fin 5) ∈ O := by
    have : w₀ = (z₀ : ℂ) • stdBasisVector (0 : Fin 5) := by
      funext j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp [hw₀0, stdBasisVector]
      · have := hw₀s i
        simp [this, toComplexVec, stdBasisVector, Fin.succ_ne_zero]
    exact this ▸ hw₀
  have hf₂ : IsHolomorphicIn O (partialOneTwo (asLine H)) :=
    (hD' 5 1 O _ ((hD' 5 1 O (asLine H) hH).1 (stdBasisVector (2 : Fin 5)))).1
      (stdBasisVector (1 : Fin 5))
  have hline : Continuous fun ζ : ℂ => ζ • stdBasisVector (0 : Fin 5) := by fun_prop
  have hline₀ : ∀ ζ : ℂ, DifferentiableAt ℂ (fun ζ : ℂ => ζ • stdBasisVector (0 : Fin 5)) ζ :=
    fun ζ => differentiableAt_id.smul_const _
  have hopen : IsOpen ((fun ζ : ℂ => ζ • stdBasisVector (0 : Fin 5)) ⁻¹' O) := hH.1.preimage hline
  have hG : DifferentiableOn ℂ
      (fun ζ : ℂ => -partialOneTwo (asLine H) (ζ • stdBasisVector (0 : Fin 5)) 0)
      ((fun ζ : ℂ => ζ • stdBasisVector (0 : Fin 5)) ⁻¹' O) := by
    intro ζ hζ
    have h₁ : DifferentiableAt ℂ (partialOneTwo (asLine H)) (ζ • stdBasisVector (0 : Fin 5)) :=
      differentiableAt_of_isHolomorphicIn hD hf₂ hζ
    have h₂ : DifferentiableAt ℂ
        (fun ζ : ℂ => partialOneTwo (asLine H) (ζ • stdBasisVector (0 : Fin 5))) ζ :=
      DifferentiableAt.comp (g := partialOneTwo (asLine H)) ζ h₁ (hline₀ ζ)
    exact ((differentiableAt_pi.1 h₂ 0).neg).differentiableWithinAt
  have hA := hG.analyticAt (hopen.mem_nhds (show (z₀ : ℂ) ∈ _ from hbase))
  have hreal : AnalyticAt ℝ
      (fun x : ℝ => (-partialOneTwo (asLine H) ((x : ℂ) • stdBasisVector (0 : Fin 5)) 0).re) z₀ :=
    Complex.reCLM.analyticAt _ |>.fun_comp
      ((hA.restrictScalars (𝕜 := ℝ)).fun_comp (Complex.ofRealCLM.analyticAt z₀))
  refine hreal.congr ?_
  have hnear : ∀ᶠ x : ℝ in 𝓝 z₀, (x : ℂ) • stdBasisVector (0 : Fin 5) ∈ O :=
    (hline.comp Complex.continuous_ofReal).continuousAt.eventually_mem (hH.1.mem_nhds hbase)
  filter_upwards [hnear, Ioi_mem_nhds hz₀] with x hx hpos
  have hpos : 0 < x := hpos
  have hvalue := massiveStiffness_eq_neg_secondPartialAtZero hC hU hT hL hs hpos
  rw [secondPartialAtZero_eq_partialOneTwo hD hD' hH _ x hx fun s t hst => by
    have := hHeq _ hst (realSlicePoint_mem_realLocus x s t) (by simp [realSlicePoint_apply_zero, hpos])
    simpa [realSlicePoint_apply_zero, realSlicePoint_apply_succ] using this] at hvalue
  rw [← hvalue]
  simp
end YangMills.Construction.Tower.MassiveStiffnessFunctions.RealAnalyticity
end
