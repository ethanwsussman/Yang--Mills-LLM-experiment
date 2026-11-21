import YangMills.Construction.RunningCouplingSlope.PlainAverageAlongComplexCurvesProof
import YangMills.Construction.Towers.GaugeTransformationsInTheLeftChartProof
import YangMills.Construction.Lattice.LatticesOfATorusAndTheProductTopologyOfConfigurations
import YangMills.Construction.Matrices.ExpChartHolomorphyProof
import YangMills.Construction.Matrices.ImplicitFunctionOnTheRealFormProof
import YangMills.Construction.RunningCouplingSlope.PlainAverageNearOne
import YangMills.Construction.RunningCouplingSlope.PlainDifferentialIsLinear
import YangMills.Construction.RunningCouplingSlope.PlainIteratesAreHolomorphicAtARadius
import YangMills.Construction.Towers.AveragedContourOfAPairDoesNotDependOnTheBond
import YangMills.Construction.Towers.CurvesReadInTheChartAtOneProof
import YangMills.Construction.Towers.KernelsOfThreeMapsOfATowerProof
import YangMills.Construction.Towers.LinearMapsOnTheRealSpacesProof
import YangMills.Construction.Towers.LinearityOfTheCovariantMapsOfAStepOnTheSidesProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open Set Filter
open scoped ENNReal Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear
open Tower PeriodicOperators Matrices
open Tower.LeftChartFields (CurveLogDerivative)
section Germs
variable {P X Y : Type} [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup Y] [NormedSpace ℂ Y]
def AnalyticGerm (S : Set P) (p₀ : P) (g : P → X) : Prop :=
  ∃ H : P → X, AnalyticAt ℂ H p₀ ∧ ∀ᶠ p in 𝓝[S] p₀, g p = H p
variable {S : Set P} {p₀ : P} {g g' : P → X}
theorem AnalyticGerm.congr_eventually (h : AnalyticGerm S p₀ g)
    (he : ∀ᶠ p in 𝓝[S] p₀, g p = g' p) : AnalyticGerm S p₀ g' := by
  obtain ⟨H, hH, hev⟩ := h
  refine ⟨H, hH, ?_⟩
  filter_upwards [hev, he] with p h₁ h₂
  rw [← h₂, h₁]
theorem AnalyticGerm.const (x : X) : AnalyticGerm S p₀ fun _ => x :=
  ⟨fun _ => x, analyticAt_const, Eventually.of_forall fun _ => rfl⟩
theorem AnalyticGerm.add (h : AnalyticGerm S p₀ g) (h' : AnalyticGerm S p₀ g') :
    AnalyticGerm S p₀ fun p => g p + g' p := by
  obtain ⟨H, hH, hev⟩ := h
  obtain ⟨H', hH', hev'⟩ := h'
  refine ⟨fun p => H p + H' p, hH.add hH', ?_⟩
  filter_upwards [hev, hev'] with p h₁ h₂
  rw [h₁, h₂]
theorem AnalyticGerm.neg (h : AnalyticGerm S p₀ g) : AnalyticGerm S p₀ fun p => -g p := by
  obtain ⟨H, hH, hev⟩ := h
  refine ⟨fun p => -H p, hH.neg, ?_⟩
  filter_upwards [hev] with p h₁
  rw [h₁]
theorem AnalyticGerm.sub (h : AnalyticGerm S p₀ g) (h' : AnalyticGerm S p₀ g') :
    AnalyticGerm S p₀ fun p => g p - g' p := by
  simpa [sub_eq_add_neg] using h.add h'.neg
theorem AnalyticGerm.map_clm (T : X →L[ℂ] Y) (h : AnalyticGerm S p₀ g) :
    AnalyticGerm S p₀ fun p => T (g p) := by
  obtain ⟨H, hH, hev⟩ := h
  refine ⟨fun p => T (H p), T.analyticAt _ |>.comp hH, ?_⟩
  filter_upwards [hev] with p h₁
  rw [h₁]
theorem AnalyticGerm.sum {α : Type} (s : Finset α) {f : α → P → X}
    (h : ∀ a ∈ s, AnalyticGerm S p₀ (f a)) : AnalyticGerm S p₀ fun p => ∑ a ∈ s, f a p := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using AnalyticGerm.const (S := S) (p₀ := p₀) (0 : X)
  | insert a s ha ih =>
    have h₁ := (h a (Finset.mem_insert_self a s)).add
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))
    exact h₁.congr_eventually (Eventually.of_forall fun p => by rw [Finset.sum_insert ha])
theorem AnalyticGerm.eq_at_point (hp : p₀ ∈ S) {H : P → X}
    (hev : ∀ᶠ p in 𝓝[S] p₀, g p = H p) : g p₀ = H p₀ :=
  hev.self_of_nhdsWithin hp
theorem AnalyticGerm.tendsto_self (hp : p₀ ∈ S) (h : AnalyticGerm S p₀ g) :
    Tendsto g (𝓝[S] p₀) (𝓝 (g p₀)) := by
  obtain ⟨H, hH, hev⟩ := h
  rw [AnalyticGerm.eq_at_point hp hev]
  have h₁ : Tendsto H (𝓝[S] p₀) (𝓝 (H p₀)) :=
    hH.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  exact h₁.congr' (hev.mono fun p hp => hp.symm)
theorem AnalyticGerm.comp_analytic (hp : p₀ ∈ S) (h : AnalyticGerm S p₀ g) {f : X → Y}
    (hf : AnalyticAt ℂ f (g p₀)) : AnalyticGerm S p₀ fun p => f (g p) := by
  obtain ⟨H, hH, hev⟩ := h
  have e := AnalyticGerm.eq_at_point hp hev
  rw [e] at hf
  refine ⟨fun p => f (H p), hf.comp hH, ?_⟩
  filter_upwards [hev] with p h₁
  rw [h₁]
theorem AnalyticGerm.comp_tuple {τ : Type} [Fintype τ] {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (hp : p₀ ∈ S)
    {Ψ : P → τ → E} (hΨ : ∀ i, AnalyticGerm S p₀ fun p => Ψ p i) {D : Set (τ → E)}
    (hD : ∀ᶠ p in 𝓝[S] p₀, Ψ p ∈ D) {φ : (τ → E) → Y} {G : (τ → E) → Y}
    (hG : AnalyticAt ℂ G (Ψ p₀)) (hGev : ∀ᶠ y in 𝓝[D] (Ψ p₀), φ y = G y) :
    AnalyticGerm S p₀ fun p => φ (Ψ p) := by
  choose H hH hev using hΨ
  have hvec : AnalyticAt ℂ (fun p i => H i p) p₀ := AnalyticAt.pi hH
  have hall : ∀ᶠ p in 𝓝[S] p₀, Ψ p = fun i => H i p := by
    filter_upwards [eventually_all.2 hev] with p h
    exact funext h
  have hat : Ψ p₀ = fun i => H i p₀ := hall.self_of_nhdsWithin hp
  have htend : Tendsto Ψ (𝓝[S] p₀) (𝓝[D] (Ψ p₀)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, hD⟩
    have h₁ : Tendsto (fun p i => H i p) (𝓝[S] p₀) (𝓝 (Ψ p₀)) := by
      rw [hat]
      exact hvec.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact h₁.congr' (hall.mono fun p hp => hp.symm)
  rw [hat] at hG
  refine ⟨fun p => G (fun i => H i p), hG.comp hvec, ?_⟩
  filter_upwards [htend.eventually hGev, hall] with p h₁ h₂
  rw [h₁, h₂]
end Germs
section Scalars
variable {P X : Type} [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable {S : Set P} {p₀ : P}
theorem AnalyticGerm.smul {f : P → ℂ} {g : P → X} (hf : AnalyticGerm S p₀ f)
    (hg : AnalyticGerm S p₀ g) : AnalyticGerm S p₀ fun p => f p • g p := by
  obtain ⟨H, hH, hev⟩ := hf
  obtain ⟨H', hH', hev'⟩ := hg
  refine ⟨fun p => H p • H' p, hH.smul hH', ?_⟩
  filter_upwards [hev, hev'] with p h₁ h₂
  rw [h₁, h₂]
theorem AnalyticGerm.mul_complex {f f' : P → ℂ} (hf : AnalyticGerm S p₀ f)
    (hg : AnalyticGerm S p₀ f') : AnalyticGerm S p₀ fun p => f p * f' p := hf.smul hg
theorem AnalyticGerm.inv_complex (hp : p₀ ∈ S) {f : P → ℂ} (hf : AnalyticGerm S p₀ f)
    (h0 : f p₀ ≠ 0) : AnalyticGerm S p₀ fun p => (f p)⁻¹ :=
  hf.comp_analytic hp (analyticAt_id.inv h0)
theorem AnalyticGerm.sqrt (hp : p₀ ∈ S) {f : P → ℂ} (hf : AnalyticGerm S p₀ f)
    (h0 : f p₀ ∈ Complex.slitPlane) : AnalyticGerm S p₀ fun p => (f p) ^ (1 / 2 : ℂ) :=
  hf.comp_analytic hp (analyticAt_id.cpow analyticAt_const h0)
end Scalars
section Matrices
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P]
variable {S : Set P} {p₀ : P} {g g' : P → ComplexMatrix2}
theorem AnalyticGerm.matMul (h : AnalyticGerm S p₀ g) (h' : AnalyticGerm S p₀ g') :
    AnalyticGerm S p₀ fun p => g p * g' p := by
  obtain ⟨H, hH, hev⟩ := h
  obtain ⟨H', hH', hev'⟩ := h'
  refine ⟨fun p => H p * H' p, hH.mul hH', ?_⟩
  filter_upwards [hev, hev'] with p h₁ h₂
  rw [h₁, h₂]
def matrixEntryCLM (r s : Fin 2) : ComplexMatrix2 →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ r s)
theorem AnalyticGerm.matEntry (h : AnalyticGerm S p₀ g) (r s : Fin 2) :
    AnalyticGerm S p₀ fun p => g p r s :=
  h.map_clm (matrixEntryCLM r s)
theorem AnalyticGerm.det (h : AnalyticGerm S p₀ g) : AnalyticGerm S p₀ fun p => (g p).det := by
  refine (((h.matEntry 0 0).mul_complex (h.matEntry 1 1)).sub
    ((h.matEntry 0 1).mul_complex (h.matEntry 1 0))).congr_eventually
      (Eventually.of_forall fun p => ?_)
  exact (Matrix.det_fin_two _).symm
def adjugateCLM : ComplexMatrix2 →L[ℂ] ComplexMatrix2 :=
  LinearMap.toContinuousLinearMap
    { toFun := Matrix.adjugate
      map_add' := fun X Y => by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two] <;> ring
      map_smul' := fun c X => by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two] }
theorem AnalyticGerm.matInv (hp : p₀ ∈ S) (h : AnalyticGerm S p₀ g) (h0 : (g p₀).det ≠ 0) :
    AnalyticGerm S p₀ fun p => (g p)⁻¹ := by
  refine ((h.det.inv_complex hp h0).smul (h.map_clm adjugateCLM)).congr_eventually
    (Eventually.of_forall fun p => ?_)
  rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rfl
theorem AnalyticGerm.listProd {α : Type} (V : P → α → ComplexMatrix2)
    (hV : ∀ a, AnalyticGerm S p₀ fun p => V p a) (l : List α) :
    AnalyticGerm S p₀ fun p => (l.map (V p)).prod := by
  induction l with
  | nil => simpa using AnalyticGerm.const (S := S) (p₀ := p₀) (1 : ComplexMatrix2)
  | cons a l ih => simpa using (hV a).matMul ih
theorem AnalyticGerm.matExp (hp : p₀ ∈ S) (h : AnalyticGerm S p₀ g) :
    AnalyticGerm S p₀ fun p => ComplexMatrix2.matExp (g p) :=
  h.comp_analytic hp (NormedSpace.exp_analytic (𝕂 := ℂ) _)
end Matrices
section Derivative
variable {P X : Type} [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable {S : Set P} {p₀ : P} {g : P × ℂ → X}
theorem eventually_curry_prod_zero {q : P × ℂ → Prop}
    (h : ∀ᶠ z in 𝓝[S ×ˢ univ] ((p₀, 0) : P × ℂ), q z) :
    ∀ᶠ p in 𝓝[S] p₀, ∀ᶠ t in 𝓝 (0 : ℂ), q (p, t) := by
  rw [nhdsWithin_prod_eq, nhdsWithin_univ] at h
  exact h.curry
theorem AnalyticGerm.differentiable_slice (hg : AnalyticGerm (S ×ˢ univ) ((p₀, 0) : P × ℂ) g) :
    ∀ᶠ p in 𝓝[S] p₀, DifferentiableAt ℂ (fun t => g (p, t)) 0 := by
  obtain ⟨H, hH, hev⟩ := hg
  have hin : ContinuousAt (fun p : P => ((p, 0) : P × ℂ)) p₀ := by fun_prop
  have hA : ∀ᶠ p in 𝓝 p₀, AnalyticAt ℂ H (p, 0) :=
    hin.eventually hH.eventually_analyticAt
  filter_upwards [eventually_curry_prod_zero hev, nhdsWithin_le_nhds hA] with p h₁ h₂
  have hd : DifferentiableAt ℂ (fun t : ℂ => H (p, t)) 0 :=
    DifferentiableAt.comp (g := H) (0 : ℂ) h₂.differentiableAt (by fun_prop)
  exact hd.congr_of_eventuallyEq h₁
theorem AnalyticGerm.deriv_slice (hg : AnalyticGerm (S ×ˢ univ) ((p₀, 0) : P × ℂ) g) :
    AnalyticGerm S p₀ fun p => deriv (fun t => g (p, t)) 0 := by
  obtain ⟨H, hH, hev⟩ := hg
  have hin : ContinuousAt (fun p : P => ((p, 0) : P × ℂ)) p₀ := by fun_prop
  have hA : ∀ᶠ p in 𝓝 p₀, AnalyticAt ℂ H (p, 0) :=
    hin.eventually hH.eventually_analyticAt
  have hinc : AnalyticAt ℂ (fun p : P => ((p, 0) : P × ℂ)) p₀ :=
    analyticAt_id.prod analyticAt_const
  have hF : AnalyticAt ℂ (fun p : P => fderiv ℂ H (p, 0)) p₀ :=
    AnalyticAt.comp (g := fderiv ℂ H) hH.fderiv hinc
  have hap : AnalyticAt ℂ (fun p : P => fderiv ℂ H (p, 0) ((0, 1) : P × ℂ)) p₀ :=
    ((ContinuousLinearMap.apply ℂ X ((0, 1) : P × ℂ)).analyticAt _).comp hF
  refine ⟨_, hap, ?_⟩
  filter_upwards [eventually_curry_prod_zero hev, nhdsWithin_le_nhds hA] with p h₁ h₂
  have hd : HasDerivAt (fun t : ℂ => ((p, t) : P × ℂ)) ((0, 1) : P × ℂ) 0 :=
    (hasDerivAt_const (0 : ℂ) p).prodMk (hasDerivAt_id (0 : ℂ))
  have hc : HasDerivAt (fun t : ℂ => H (p, t)) (fderiv ℂ H (p, 0) ((0, 1) : P × ℂ)) 0 :=
    HasFDerivAt.comp_hasDerivAt (f := fun t : ℂ => ((p, t) : P × ℂ)) (0 : ℂ)
      h₂.differentiableAt.hasFDerivAt hd
  have e : (fun t => g (p, t)) =ᶠ[𝓝 0] fun t => H (p, t) := h₁
  rw [e.deriv_eq]
  exact hc.deriv
end Derivative
section Pairs
variable {P X : Type} [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable {S : Set P} {p₀ : P} {g : P → X}
theorem tendsto_fst_prod_zero :
    Tendsto (Prod.fst : P × ℂ → P) (𝓝[S ×ˢ univ] ((p₀, 0) : P × ℂ)) (𝓝[S] p₀) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · exact (continuous_fst.tendsto ((p₀, 0) : P × ℂ)).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with z hz using hz.1
theorem tendsto_pair_zero : Tendsto (fun p : P => ((p, 0) : P × ℂ)) (𝓝[S] p₀)
    (𝓝[S ×ˢ univ] ((p₀, 0) : P × ℂ)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have h : ContinuousAt (fun p : P => ((p, 0) : P × ℂ)) p₀ := by fun_prop
    exact h.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with p hp using ⟨hp, mem_univ _⟩
theorem AnalyticGerm.comp_fst (h : AnalyticGerm S p₀ g) :
    AnalyticGerm (S ×ˢ univ) ((p₀, 0) : P × ℂ) fun z => g z.1 := by
  obtain ⟨H, hH, hev⟩ := h
  have hf : AnalyticAt ℂ (Prod.fst : P × ℂ → P) ((p₀, 0) : P × ℂ) := analyticAt_fst
  exact ⟨fun z => H z.1, AnalyticAt.comp (g := H) (f := Prod.fst) hH hf,
    tendsto_fst_prod_zero.eventually hev⟩
theorem analyticGerm_snd : AnalyticGerm (S ×ˢ univ) ((p₀, 0) : P × ℂ) fun z => z.2 :=
  ⟨Prod.snd, analyticAt_snd, Eventually.of_forall fun _ => rfl⟩
theorem AnalyticGerm.restrict_zero {g : P × ℂ → X}
    (h : AnalyticGerm (S ×ˢ univ) ((p₀, 0) : P × ℂ) g) :
    AnalyticGerm S p₀ fun p => g (p, 0) := by
  obtain ⟨H, hH, hev⟩ := h
  have hinc : AnalyticAt ℂ (fun p : P => ((p, 0) : P × ℂ)) p₀ :=
    analyticAt_id.prod analyticAt_const
  exact ⟨fun p => H (p, 0), AnalyticAt.comp (g := H) hH hinc, tendsto_pair_zero.eventually hev⟩
end Pairs
theorem mem_slitPlane_of_sqrt_near_one {z : ℂ} (h : ‖z ^ (1 / 2 : ℂ) - 1‖ < 1 / 2) :
    z ∈ Complex.slitPlane := by
  by_contra hz
  rw [Complex.mem_slitPlane_iff, not_or, not_lt, not_not] at hz
  obtain ⟨hre, him⟩ := hz
  have hzero : (z ^ (1 / 2 : ℂ)).re = 0 := by
    by_cases h0 : z = 0
    · rw [h0, Complex.zero_cpow (by norm_num)]
      simp
    · have hlt : z.re < 0 := lt_of_le_of_ne hre fun e => h0 (Complex.ext e him)
      have harg : z.arg = Real.pi := Complex.arg_eq_pi_iff.2 ⟨hlt, him⟩
      rw [Complex.cpow_def_of_ne_zero h0, Complex.exp_re]
      have him' : (Complex.log z * (1 / 2 : ℂ)).im = Real.pi / 2 := by
        rw [Complex.mul_im]
        simp [Complex.log_im, harg]
        ring
      rw [him', Real.cos_pi_div_two, mul_zero]
  have h₁ : |(z ^ (1 / 2 : ℂ) - 1).re| ≤ ‖z ^ (1 / 2 : ℂ) - 1‖ := Complex.abs_re_le_norm _
  simp only [Complex.sub_re, Complex.one_re, hzero, zero_sub, abs_neg, abs_one] at h₁
  linarith
section Tower
variable {L n k j : ℕ}
theorem expTwist_of_positive {A U : Edge L n k j → ComplexMatrix2} {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) :
    PeriodicLattice.expTwist A U b = ComplexMatrix2.matExp (Complex.I • A b) * U b := by apply _root_.YangMills.Construction.Tower.LeftChartGauge.expTwist_of_positive <;> assumption
theorem expTwist_of_not_positive {A U : Edge L n k j → ComplexMatrix2} {b : Edge L n k j}
    (hb : ¬ b.IsPositivelyOriented) :
    PeriodicLattice.expTwist A U b =
      (ComplexMatrix2.matExp (Complex.I • A b.opposite) * U b.opposite)⁻¹ := by apply _root_.YangMills.Construction.Tower.LeftChartGauge.expTwist_of_not_positive <;> assumption
theorem inv_mem_unitDeterminant {g : ComplexMatrix2} (hg : g ∈ ComplexMatrix2.unitDeterminant) :
    g⁻¹ ∈ ComplexMatrix2.unitDeterminant := by apply _root_.YangMills.SharedProofs.p413 <;> assumption
theorem inv_inv_of_mem_unitDeterminant {g : ComplexMatrix2}
    (hg : g ∈ ComplexMatrix2.unitDeterminant) : (g⁻¹)⁻¹ = g := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.inv_inv_of_mem_unitDeterminant <;> assumption
theorem mul_mem_unitDeterminant {g g' : ComplexMatrix2} (hg : g ∈ ComplexMatrix2.unitDeterminant)
    (hg' : g' ∈ ComplexMatrix2.unitDeterminant) : g * g' ∈ ComplexMatrix2.unitDeterminant := by apply _root_.YangMills.SharedProofs.p36859 <;> assumption
theorem matExp_mem_unitDeterminant (hE : ComplexMatrix2.ExpLogEstimates) {Z : ComplexMatrix2}
    (hZ : Z ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.matExp Z ∈ ComplexMatrix2.unitDeterminant := by apply _root_.YangMills.SharedProofs.p27134 <;> assumption
theorem expTwist_mem_fieldsIn (hE : ComplexMatrix2.ExpLogEstimates)
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {A U : Edge L n k j → ComplexMatrix2} (hA : A ∈ complexEdgeForms L n k j)
    (hU : U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup) :
    PeriodicLattice.expTwist A U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup := by
  have hU' : PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup univ U := hU
  have hpos : ∀ b : Edge L n k j, b.IsPositivelyOriented →
      ComplexMatrix2.matExp (Complex.I • A b) * U b ∈ ComplexMatrix2.unitDeterminant :=
    fun b hb => mul_mem_unitDeterminant
      (matExp_mem_unitDeterminant hE (ComplexMatrix2.traceless.smul_mem _ (hA.1 b hb)))
      (hU'.1 b (mem_univ b))
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · rcases PeriodicLattice.Bond.positive_or_opposite_positive b with h | h
    · rw [expTwist_of_positive h]
      exact hpos b h
    · rcases hx b with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · rw [expTwist_of_positive h₁]
        exact hpos b h₁
      · rw [expTwist_of_not_positive h₂]
        exact inv_mem_unitDeterminant (hpos _ h)
  · rcases hx b with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [expTwist_of_positive h₁, expTwist_of_not_positive h₂,
        PeriodicLattice.Bond.opposite_opposite]
    · rw [expTwist_of_positive h₁, expTwist_of_not_positive h₂,
        inv_inv_of_mem_unitDeterminant (hpos _ h₁)]
end Tower
section Level
variable {L n k j : ℕ}
theorem expTwist_zero_smul {U : Edge L n k j → ComplexMatrix2}
    (hU : U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup) (A : Edge L n k j → ComplexMatrix2) :
    PeriodicLattice.expTwist ((0 : ℂ) • A) U = U := by apply _root_.YangMills.Construction.Tower.RealLinearMaps.expTwist_zero_smul <;> assumption
structure StepHypotheses (L n k j : ℕ) (r : ℝ) : Prop where
  finite_edges : Finite (Edge L n k j)
  finite_vertices : Finite (Vertex L n k j)
  orientation_xor : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented
  expLog : ComplexMatrix2.ExpLogEstimates
  curve_logs : ∀ s : ℝ, 0 < s → CurveLogDerivative ℂ (Metric.ball 0 s)
    PeriodicLattice.complexGaugeGroup PeriodicLattice.complexLieAlgebra
  mean_near_one : ∀ V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
    (∀ b, ComplexMatrix2.operatorNorm (V b - 1) < r) →
    ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
      ‖meanRadius V c - 1‖ < 1 / 2 ∧ normalizedMean V c ∈ PeriodicLattice.complexGaugeGroup
  le_polydiscRadius : r ≤ polydiscRadius L
  admissible : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
    PolydiscIsAdmissible (polydiscRadius L) c
  contour_local : ∀ (y : Vertex L n k (j + 1)),
    ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
    ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
    y ∈ ({c.source, c.target} : Set (Vertex L n k (j + 1))) →
    ∀ W : Edge L n k j → ComplexMatrix2,
    PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup univ W →
    (∀ b, ComplexMatrix2.operatorNorm (W b - 1) < polydiscRadius L) →
    ∀ W' : Edge L n k j → ComplexMatrix2,
      (∀ b ∈ DoubleBlockPolydisc.doubleBlockBonds c, W' b = W b) →
        PeriodicLattice.complexMeanContourHolonomy W' y x =
          PeriodicLattice.complexMeanContourHolonomy W y x
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] {S : Set P} {p₀ : P} {r : ℝ}
structure IsRegularFamily (r : ℝ) (S : Set P) (p₀ : P) (V : P → Edge L n k j → ComplexMatrix2) :
    Prop where
  base_mem : p₀ ∈ S
  analytic : ∀ b, AnalyticGerm S p₀ fun p => V p b
  eventually_field : ∀ᶠ p in 𝓝[S] p₀, V p ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup
  near_one : ∀ b, ComplexMatrix2.operatorNorm (V p₀ b - 1) < r
variable {V : P → Edge L n k j → ComplexMatrix2}
theorem IsRegularFamily.base_field (hV : IsRegularFamily r S p₀ V) :
    V p₀ ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup :=
  hV.eventually_field.self_of_nhdsWithin hV.base_mem
theorem IsRegularFamily.det_base (hV : IsRegularFamily r S p₀ V) (b : Edge L n k j) :
    (V p₀ b).det = 1 :=
  (show PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup univ (V p₀) from
    hV.base_field).1 b (mem_univ b)
theorem IsRegularFamily.eventually_near_one (T : StepHypotheses L n k j r)
    (hV : IsRegularFamily r S p₀ V) :
    ∀ᶠ p in 𝓝[S] p₀, ∀ b, ComplexMatrix2.operatorNorm (V p b - 1) < r := by
  have := T.finite_edges
  refine eventually_all.2 fun b => ?_
  have h₁ : Tendsto (fun p => ‖V p b - 1‖) (𝓝[S] p₀) (𝓝 ‖V p₀ b - 1‖) :=
    (((hV.analytic b).tendsto_self hV.base_mem).sub_const 1).norm
  exact h₁.eventually_lt_const (hV.near_one b)
theorem det_pathHolonomy {U : Edge L n k j → ComplexMatrix2} (hU : ∀ b, (U b).det = 1)
    (l : List (Edge L n k j)) : (PeriodicLattice.pathHolonomy U l).det = 1 := by apply _root_.YangMills.Construction.RunningCouplingSlope.ContourMeanDerivative.det_list_prod_eq_one <;> assumption
theorem IsRegularFamily.holonomy_analytic (hV : IsRegularFamily r S p₀ V)
    (l : List (Edge L n k j)) :
    AnalyticGerm S p₀ fun p => PeriodicLattice.pathHolonomy (V p) l :=
  AnalyticGerm.listProd V hV.analytic l
theorem IsRegularFamily.contourHolonomy_analytic (hV : IsRegularFamily r S p₀ V)
    (c : Edge L n k (j + 1)) (x : Vertex L n k j) (π : Equiv.Perm (Fin 4)) :
    AnalyticGerm S p₀ fun p => contourHolonomy (V p) c x π := by
  refine ((hV.holonomy_analytic _).matMul (hV.holonomy_analytic _)).matMul
    ((hV.holonomy_analytic _).matInv hV.base_mem ?_)
  rw [det_pathHolonomy hV.det_base]
  exact one_ne_zero
theorem IsRegularFamily.contourMean_analytic (T : StepHypotheses L n k j r)
    (hV : IsRegularFamily r S p₀ V) (c : Edge L n k (j + 1)) :
    AnalyticGerm S p₀ fun p => contourMean (V p) c := by
  have := T.finite_vertices
  have hfin : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
      Set (Vertex L n k j)).Finite := Set.toFinite _
  unfold RunningCouplingSlope.contourMean
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin]
  exact (AnalyticGerm.const _).smul (AnalyticGerm.sum _ fun x _ => AnalyticGerm.sum _ fun π _ =>
    hV.contourHolonomy_analytic c x π)
theorem IsRegularFamily.normalizedMean_analytic (T : StepHypotheses L n k j r)
    (hV : IsRegularFamily r S p₀ V) {c : Edge L n k (j + 1)} (hc : c.IsPositivelyOriented) :
    AnalyticGerm S p₀ (fun p => normalizedMean (V p) c) ∧
      ∀ᶠ p in 𝓝[S] p₀, normalizedMean (V p) c ∈ PeriodicLattice.complexGaugeGroup := by
  have hn := T.mean_near_one _ hV.base_field hV.near_one c hc
  have hm := hV.contourMean_analytic T c
  have hs : (Matrix.det (RunningCouplingSlope.contourMean (V p₀) c)) ∈ Complex.slitPlane :=
    mem_slitPlane_of_sqrt_near_one hn.1
  have hl : AnalyticGerm S p₀ fun p => meanRadius (V p) c := hm.det.sqrt hV.base_mem hs
  have hl0 : meanRadius (V p₀) c ≠ 0 := by
    intro h
    have := hn.1
    rw [h] at this
    norm_num at this
  refine ⟨(hl.inv_complex hV.base_mem hl0).smul hm, ?_⟩
  filter_upwards [hV.eventually_field, hV.eventually_near_one T] with p h₁ h₂
  exact (T.mean_near_one _ h₁ h₂ c hc).2
theorem extendFromPositive_restrict_eq {ℬ : Set (Edge L n k j)}
    (hℬ : ∀ b ∈ ℬ, b.opposite ∈ ℬ) {W : Edge L n k j → ComplexMatrix2}
    (hW : ∀ b : Edge L n k j, W b.opposite = (W b)⁻¹) (b : Edge L n k j) (hb : b ∈ ℬ) :
    PeriodicLattice.extendFromPositive ℬ (PeriodicLattice.restrictToPositive ℬ W) b = W b := by
  unfold PeriodicLattice.extendFromPositive
  by_cases hp : b.IsPositivelyOriented
  · rw [dif_pos ⟨hb, hp⟩]
    rfl
  · have hr := (PeriodicLattice.Bond.positive_or_opposite_positive b).resolve_left hp
    rw [dif_neg (fun h => hp h.2), dif_pos ⟨hℬ b hb, hr⟩]
    have h := hW b.opposite
    rw [PeriodicLattice.Bond.opposite_opposite] at h
    exact h.symm
theorem IsRegularFamily.contourMeanHolonomy_analytic (T : StepHypotheses L n k j r)
    (hV : IsRegularFamily r S p₀ V) (y : Vertex L n k (j + 1)) {x : Vertex L n k j}
    (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y) :
    AnalyticGerm S p₀ (fun p => PeriodicLattice.complexMeanContourHolonomy (V p) y x) ∧
      ∀ᶠ p in 𝓝[S] p₀, PeriodicLattice.complexMeanContourHolonomy (V p) y x ∈
        PeriodicLattice.complexGaugeGroup := by
  classical
  have hc : (PeriodicLattice.Bond.forwardFrom y 0).IsPositivelyOriented :=
    ⟨0, add_sub_cancel_left _ _⟩
  set c := PeriodicLattice.Bond.forwardFrom y 0 with hcdef
  have hy : y ∈ ({c.source, c.target} : Set (Vertex L n k (j + 1))) := Or.inl rfl
  have hadm := T.admissible c hc
  obtain ⟨inst, hol⟩ := (hadm.holomorphic_contourMean y hy x hx).1
  have hclosed : ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)),
      b.opposite ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)) :=
    fun b hb => ⟨hb.2, hb.1⟩
  have hpoly : ∀ W ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
      (∀ b, ComplexMatrix2.operatorNorm (W b - 1) < r) →
        W ∈ nearIdentityPolydisc (polydiscRadius L) c := by
    intro W hW hn
    have hW' : PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup univ W := hW
    exact ⟨⟨fun b _ => hW'.1 b (mem_univ b), fun b _ => hW'.2 b (mem_univ b)⟩,
      fun b _ => (hn b).trans_le T.le_polydiscRadius⟩
  have hD : ∀ᶠ p in 𝓝[S] p₀, PeriodicLattice.restrictToPositive
      (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)) (V p) ∈
      PeriodicLattice.restrictToPositive
        (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)) ''
        nearIdentityPolydisc (polydiscRadius L) c := by
    filter_upwards [hV.eventually_field, hV.eventually_near_one T] with p h₁ h₂
    exact ⟨_, hpoly _ h₁ h₂, rfl⟩
  have h0 := hD.self_of_nhdsWithin hV.base_mem
  obtain ⟨G, hG, hGev⟩ := hol.2.2 _ h0
  have hfam := AnalyticGerm.comp_tuple hV.base_mem
    (Ψ := fun p => PeriodicLattice.restrictToPositive
      (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)) (V p))
    (fun i => hV.analytic i.1) hD hG hGev
  have hone := hfam.map_clm
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Unit => ComplexMatrix2) ())
  have hread : ∀ᶠ p in 𝓝[S] p₀, PeriodicLattice.complexMeanContourHolonomy
      (PeriodicLattice.extendFromPositive
        (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j))
        (PeriodicLattice.restrictToPositive
          (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)) (V p))) y x =
      PeriodicLattice.complexMeanContourHolonomy (V p) y x := by
    filter_upwards [hV.eventually_field, hV.eventually_near_one T] with p h₁ h₂
    have h₁' : PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup univ (V p) := h₁
    exact T.contour_local y x hx c hc hy _ h₁' (fun b => (h₂ b).trans_le T.le_polydiscRadius) _
      fun b hb => extendFromPositive_restrict_eq hclosed (fun b => h₁'.2 b (mem_univ b)) b hb
  refine ⟨hone.congr_eventually hread, ?_⟩
  filter_upwards [hD, hread] with p h₁ h₂
  have h := hol.2.1 h₁ ()
  rw [← h₂]
  exact h
end Level
section Motion
variable {L n k j : ℕ}
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] {S : Set P} {p₀ : P} {r : ℝ}
variable {V : P → Edge L n k j → ComplexMatrix2} {B : P → Edge L n k j → ComplexMatrix2}
theorem IsRegularFamily.expTwist (T : StepHypotheses L n k j r) (hV : IsRegularFamily r S p₀ V)
    (hB : ∀ b, AnalyticGerm S p₀ fun p => B p b)
    (hBf : ∀ᶠ p in 𝓝[S] p₀, B p ∈ complexEdgeForms L n k j) :
    IsRegularFamily r (S ×ˢ univ) ((p₀, 0) : P × ℂ)
      fun z => PeriodicLattice.expTwist (z.2 • B z.1) (V z.1) := by
  have hmem : ((p₀, 0) : P × ℂ) ∈ S ×ˢ (univ : Set ℂ) := ⟨hV.base_mem, mem_univ _⟩
  have hval : ∀ b, AnalyticGerm (S ×ˢ univ) ((p₀, 0) : P × ℂ)
      fun z : P × ℂ => ComplexMatrix2.matExp (Complex.I • (z.2 • B z.1) b) * V z.1 b := fun b =>
    (AnalyticGerm.matExp hmem ((AnalyticGerm.const Complex.I).smul
      (analyticGerm_snd.smul (hB b).comp_fst))).matMul (hV.analytic b).comp_fst
  refine ⟨hmem, fun b => ?_, ?_, fun b => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · exact (hval b).congr_eventually
        (Eventually.of_forall fun z => (expTwist_of_positive hb).symm)
    · refine ((hval b.opposite).matInv hmem ?_).congr_eventually
        (Eventually.of_forall fun z => (expTwist_of_not_positive hb).symm)
      have h0 : ComplexMatrix2.matExp
          (Complex.I • (((p₀, 0) : P × ℂ).2 • B p₀) b.opposite) = 1 := by
        simp [ComplexMatrix2.matExp]
      show (ComplexMatrix2.matExp (Complex.I • (((p₀, 0) : P × ℂ).2 • B p₀) b.opposite) *
        V p₀ b.opposite).det ≠ 0
      rw [h0, one_mul, hV.det_base]
      exact one_ne_zero
  · refine (tendsto_fst_prod_zero.eventually (hV.eventually_field.and hBf)).mono fun z h => ?_
    exact expTwist_mem_fieldsIn T.expLog T.orientation_xor (Submodule.smul_mem _ z.2 h.2) h.1
  · show ComplexMatrix2.operatorNorm
      (PeriodicLattice.expTwist ((0 : ℂ) • B p₀) (V p₀) b - 1) < r
    rw [expTwist_zero_smul hV.base_field]
    exact hV.near_one b
theorem IsRegularFamily.logDirectionalDeriv_analytic (T : StepHypotheses L n k j r)
    (hV : IsRegularFamily r S p₀ V)
    {Φ : (Edge L n k j → ComplexMatrix2) → ComplexMatrix2}
    (hΦ : AnalyticGerm (S ×ˢ univ) ((p₀, 0) : P × ℂ)
        (fun z => Φ (PeriodicLattice.expTwist (z.2 • B z.1) (V z.1))) ∧
      ∀ᶠ z in 𝓝[S ×ˢ univ] ((p₀, 0) : P × ℂ),
        Φ (PeriodicLattice.expTwist (z.2 • B z.1) (V z.1)) ∈ PeriodicLattice.complexGaugeGroup) :
    AnalyticGerm S p₀ (fun p => Tower.logDirectionalDeriv ℂ
        (fun X => Φ (PeriodicLattice.expTwist X (V p))) (Φ (V p)) (B p)) ∧
      ∀ᶠ p in 𝓝[S] p₀, Tower.logDirectionalDeriv ℂ
        (fun X => Φ (PeriodicLattice.expTwist X (V p))) (Φ (V p)) (B p) ∈
          ComplexMatrix2.traceless := by
  obtain ⟨hg, hgrp⟩ := hΦ
  have hmem : ((p₀, 0) : P × ℂ) ∈ S ×ˢ (univ : Set ℂ) := ⟨hV.base_mem, mem_univ _⟩
  have hD := hg.deriv_slice
  have h0 := hg.restrict_zero
  have hdet : (Φ (PeriodicLattice.expTwist (((p₀, 0) : P × ℂ).2 • B ((p₀, 0) : P × ℂ).1)
      (V ((p₀, 0) : P × ℂ).1))).det ≠ 0 := by
    have h : (Φ (PeriodicLattice.expTwist (((p₀, 0) : P × ℂ).2 • B ((p₀, 0) : P × ℂ).1)
      (V ((p₀, 0) : P × ℂ).1))).det = 1 := hgrp.self_of_nhdsWithin hmem
    rw [h]
    exact one_ne_zero
  have hinv := h0.matInv hV.base_mem hdet
  have hmain := (AnalyticGerm.const (S := S) (p₀ := p₀) Complex.I⁻¹).smul (hD.matMul hinv)
  have hall : ∀ᶠ p in 𝓝[S] p₀, Tower.logDirectionalDeriv ℂ
        (fun X => Φ (PeriodicLattice.expTwist X (V p))) (Φ (V p)) (B p) =
      Complex.I⁻¹ • (deriv (fun t : ℂ => Φ (PeriodicLattice.expTwist (t • B p) (V p))) 0 *
        (Φ (PeriodicLattice.expTwist ((0 : ℂ) • B p) (V p)))⁻¹) ∧
      Complex.I⁻¹ • (deriv (fun t : ℂ => Φ (PeriodicLattice.expTwist (t • B p) (V p))) 0 *
        (Φ (PeriodicLattice.expTwist ((0 : ℂ) • B p) (V p)))⁻¹) ∈ ComplexMatrix2.traceless := by
    filter_upwards [eventually_curry_prod_zero hgrp, hg.differentiable_slice,
      hV.eventually_field] with p h₁ h₂ h₃
    obtain ⟨s, hs, hball⟩ := Metric.eventually_nhds_iff_ball.1 h₁
    have hc := T.curve_logs s hs
      (fun t : ℂ => Φ (PeriodicLattice.expTwist (t • B p) (V p))) (fun t ht => hball t ht) h₂
    obtain ⟨-, -, heq, hm⟩ := hc
    refine ⟨?_, hm⟩
    have e : Φ (V p) = Φ (PeriodicLattice.expTwist ((0 : ℂ) • B p) (V p)) := by
      rw [expTwist_zero_smul h₃]
    rw [← heq, e]
    rfl
  refine ⟨hmain.congr_eventually (hall.mono fun p h => h.1.symm), hall.mono fun p h => ?_⟩
  rw [h.1]
  exact h.2
end Motion
section Step
variable {L n k j : ℕ}
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] {S : Set P} {p₀ : P} {r : ℝ}
variable {V : P → Edge L n k j → ComplexMatrix2} {B : P → Edge L n k j → ComplexMatrix2}
theorem AnalyticGerm.extendOddly {f : P → Edge L n k j → ComplexMatrix2}
    (hf : ∀ c : Edge L n k j, c.IsPositivelyOriented → AnalyticGerm S p₀ fun p => f p c)
    (c : Edge L n k j) : AnalyticGerm S p₀ fun p => Tower.extendOddly (f p) c := by
  classical
  by_cases hc : c.IsPositivelyOriented
  · refine (hf c hc).congr_eventually (Eventually.of_forall fun p => ?_)
    simp [Tower.extendOddly, hc]
  · have hr := (PeriodicLattice.Bond.positive_or_opposite_positive c).resolve_left hc
    refine (hf _ hr).neg.congr_eventually (Eventually.of_forall fun p => ?_)
    simp [Tower.extendOddly, hc]
theorem IsRegularFamily.holLeftDifferential_analytic (T : StepHypotheses L n k j r)
    (hV : IsRegularFamily r S p₀ V) (hB : ∀ b, AnalyticGerm S p₀ fun p => B p b)
    (hBf : ∀ᶠ p in 𝓝[S] p₀, B p ∈ complexEdgeForms L n k j) (c : Edge L n k (j + 1)) :
    AnalyticGerm S p₀ fun p => holLeftDifferential normalizedMean (V p) (B p) c := by
  refine AnalyticGerm.extendOddly (fun c hc => ?_) c
  exact (hV.logDirectionalDeriv_analytic T (Φ := fun W => normalizedMean W c)
    ((hV.expTwist T hB hBf).normalizedMean_analytic T hc)).1
theorem IsRegularFamily.contourLogDrift_analytic (T : StepHypotheses L n k j r)
    (hV : IsRegularFamily r S p₀ V) (hB : ∀ b, AnalyticGerm S p₀ fun p => B p b)
    (hBf : ∀ᶠ p in 𝓝[S] p₀, B p ∈ complexEdgeForms L n k j) (y : Vertex L n k (j + 1)) :
    AnalyticGerm S p₀ fun p => contourLogDrift (V p) (B p) y := by
  have := T.finite_vertices
  have hfin : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y :
      Set (Vertex L n k j)).Finite := Set.toFinite _
  unfold Tower.contourLogDrift
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine (AnalyticGerm.const _).smul (AnalyticGerm.sum _ fun x hx => ?_)
  have hx' := hfin.mem_toFinset.1 hx
  exact (hV.logDirectionalDeriv_analytic T
    (Φ := fun W => PeriodicLattice.complexMeanContourHolonomy W y x)
    ((hV.expTwist T hB hBf).contourMeanHolonomy_analytic T y hx')).1
theorem AnalyticGerm.conjugateBy (hp : p₀ ∈ S) {g g' : P → ComplexMatrix2}
    (h : AnalyticGerm S p₀ g) (h' : AnalyticGerm S p₀ g') (h0 : (g p₀).det ≠ 0) :
    AnalyticGerm S p₀ fun p => ComplexMatrix2.conjugateBy (g p) (g' p) :=
  (h.matMul h').matMul (h.matInv hp h0)
theorem IsRegularFamily.meanCovariantStep_analytic (T : StepHypotheses L n k j r)
    (hV : IsRegularFamily r S p₀ V) (hB : ∀ b, AnalyticGerm S p₀ fun p => B p b)
    (hBf : ∀ᶠ p in 𝓝[S] p₀, B p ∈ complexEdgeForms L n k j) (c : Edge L n k (j + 1)) :
    AnalyticGerm S p₀ fun p => meanCovariantStep (V p) (B p) c := by
  refine (hV.holLeftDifferential_analytic T hB hBf c).add
    (AnalyticGerm.extendOddly (fun b hb => ?_) c)
  obtain ⟨h₁, h₂⟩ := hV.normalizedMean_analytic T hb
  have hdet : (normalizedMean (V p₀) b).det ≠ 0 := by
    have h : (normalizedMean (V p₀) b).det = 1 := h₂.self_of_nhdsWithin hV.base_mem
    rw [h]
    exact one_ne_zero
  exact (AnalyticGerm.conjugateBy hV.base_mem h₁ (hV.contourLogDrift_analytic T hB hBf _)
    hdet).sub (hV.contourLogDrift_analytic T hB hBf _)
theorem IsRegularFamily.adjointCubeAverage_analytic (T : StepHypotheses L n k j r)
    (hV : IsRegularFamily r S p₀ V)
    {l : P → Vertex L n k j → ComplexMatrix2} (hl : ∀ x, AnalyticGerm S p₀ fun p => l p x)
    (y : Vertex L n k (j + 1)) :
    AnalyticGerm S p₀ fun p => adjointCubeAverage (V p) (l p) y := by
  have := T.finite_vertices
  have hfin : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y :
      Set (Vertex L n k j)).Finite := Set.toFinite _
  unfold Tower.adjointCubeAverage
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine (AnalyticGerm.const _).smul (AnalyticGerm.sum _ fun x hx => ?_)
  obtain ⟨h₁, h₂⟩ := hV.contourMeanHolonomy_analytic T y (hfin.mem_toFinset.1 hx)
  refine AnalyticGerm.conjugateBy hV.base_mem h₁ (hl x) ?_
  have h : (PeriodicLattice.complexMeanContourHolonomy (V p₀) y x).det = 1 :=
    h₂.self_of_nhdsWithin hV.base_mem
  rw [h]
  exact one_ne_zero
end Step
section Coefficients
theorem exists_clm_pauliCoeff (a : Fin 3) :
    ∃ T : ComplexMatrix2 →L[ℂ] ℂ, ∀ X ∈ ComplexMatrix2.traceless, T X = pauliCoeff a X := by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend ((LinearMap.proj a : (Fin 3 → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
    (OneLoop.pauliCoordinateEquiv : ComplexMatrix2.traceless →ₗ[ℂ] (Fin 3 → ℂ)))
  refine ⟨LinearMap.toContinuousLinearMap g, fun X hX => ?_⟩
  have h := LinearMap.congr_fun hg ⟨X, hX⟩
  unfold Tower.pauliCoeff
  rw [dif_pos hX]
  exact h
theorem ofPauliCoeffs_mem_traceless {σ : Type} (c : Fin 3 × σ → ℂ) (x : σ) :
    ofPauliCoeffs c x ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_mem <;> assumption
theorem ofPauliCoeffs_smul_add {σ : Type} (z : ℂ) (c c' : Fin 3 × σ → ℂ) :
    ofPauliCoeffs (z • c + c') = z • ofPauliCoeffs c + ofPauliCoeffs c' := by
  funext x
  simp only [ofPauliCoeffs, Pi.add_apply, Pi.smul_apply, add_smul, Finset.sum_add_distrib,
    smul_eq_mul, mul_smul, Finset.smul_sum]
end Coefficients
section Kernels
variable {N N' : Type}
theorem applyKernel_single [DecidableEq N] (T : KernelMatrix N N') (ι : N) (ι' : N') :
    applyKernel T (Pi.single ι 1) ι' = T ι' ι := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.applyKernel_single <;> assumption
theorem kernelOfMap_apply [Fintype N] [DecidableEq N] {M : (N → ℂ) → N' → ℂ}
    (hM : ∀ (z : ℂ) (f f' : N → ℂ), M (z • f + f') = z • M f + M f') (ι : N) (ι' : N') :
    kernelOfMap M ι' ι = M (Pi.single ι 1) ι' := by
  have h0 : M 0 = 0 := by
    have h := hM 1 0 0
    simp only [smul_zero, add_zero, one_smul] at h
    simpa using h
  let Lm : (N → ℂ) →ₗ[ℂ] (N' → ℂ) :=
    { toFun := M
      map_add' := fun f f' => by simpa using hM 1 f f'
      map_smul' := fun z f => by simpa [h0] using hM z f 0 }
  have hG : Represents (fun ι' ι => M (Pi.single ι 1) ι') M := by
    intro f
    refine ⟨fun ι' => (hasSum_fintype _).summable, ?_⟩
    funext ι'
    have hf : M f = ∑ i, f i • M (Pi.single i 1) := by
      have h := LinearMap.pi_apply_eq_sum_univ Lm f
      have e : ∀ i : N, (fun j : N => if i = j then (1 : ℂ) else 0) = Pi.single i 1 := fun i => by
        funext j
        by_cases hij : i = j
        · subst hij
          simp
        · simp [hij, Pi.single_eq_of_ne (Ne.symm hij)]
      simp only [e] at h
      exact h
    show ∑' ι, M (Pi.single ι 1) ι' * f ι = M f ι'
    rw [tsum_fintype, hf, Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => by simp [mul_comm]
  have hK : Represents (kernelOfMap M) M :=
    Classical.epsilon_spec (p := fun T => Represents T M) ⟨_, hG⟩
  rw [← applyKernel_single (kernelOfMap M) ι ι', (hK _).2]
end Kernels
section Linear
variable {L n k j : ℕ} {r : ℝ}
theorem conjugateBy_smul_add (g : ComplexMatrix2) (z : ℂ) (X Y : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (z • X + Y) =
      z • ComplexMatrix2.conjugateBy g X + ComplexMatrix2.conjugateBy g Y := by
  simp only [ComplexMatrix2.conjugateBy, mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul]
theorem conjugateBy_traceless_of_det {g X : ComplexMatrix2} (hg : g.det = 1)
    (hX : X ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.conjugateBy g X ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.conjugateBy_mem_traceless_of_det <;> assumption
theorem extendOddly_of_positive {f : Edge L n k j → ComplexMatrix2} {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) : extendOddly f b = f b := by apply _root_.YangMills.Construction.Tower.IdentityChartCurves.extendOddly_of_pos <;> assumption
theorem extendOddly_of_not_positive {f : Edge L n k j → ComplexMatrix2} {b : Edge L n k j}
    (hb : ¬ b.IsPositivelyOriented) : extendOddly f b = -f b.opposite := by apply _root_.YangMills.Construction.Tower.IdentityChartCurves.extendOddly_of_not_pos <;> assumption
theorem extendOddly_mem
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {f : Edge L n k j → ComplexMatrix2}
    (hf : ∀ b : Edge L n k j, b.IsPositivelyOriented → f b ∈ ComplexMatrix2.traceless) :
    extendOddly f ∈ complexEdgeForms L n k j := by apply _root_.YangMills.Construction.Tower.StepMapsComplexLinear.extendOddly_mem <;> assumption
theorem covDiff_smul_add (U : Edge L n k j → ComplexMatrix2) (z : ℂ)
    (l l' : Vertex L n k j → ComplexMatrix2) :
    covDiff U (z • l + l') = z • covDiff U l + covDiff U l' := by apply _root_.YangMills.Construction.Tower.CovDiffStep.covDiff_smul_add <;> assumption
structure LinearStepHypotheses (L n k j : ℕ) (r : ℝ) : Prop where
  le_polydiscRadius : r ≤ polydiscRadius L
  orientation_xor : ∀ b : Edge L n k (j + 1),
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented
  mean_mem : ∀ V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
    (∀ b, ComplexMatrix2.operatorNorm (V b - 1) < r) →
    ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
      normalizedMean V c ∈ PeriodicLattice.complexGaugeGroup
  holDiff : ∀ V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
    (∀ b, ComplexMatrix2.operatorNorm (V b - 1) < r) →
      (∀ (B : Edge L n k j → ComplexMatrix2) (c : Edge L n k (j + 1)), c.IsPositivelyOriented →
        holLeftDifferential normalizedMean V B c ∈ ComplexMatrix2.traceless) ∧
      ∀ (z : ℂ) (B B' : Edge L n k j → ComplexMatrix2),
        holLeftDifferential normalizedMean V (z • B + B') =
          z • holLeftDifferential normalizedMean V B +
            holLeftDifferential normalizedMean V B'
  driftAndAdjoint : ∀ V ∈ smallComplexFields L n k j,
      (∀ B ∈ complexEdgeForms L n k j, ∀ y, contourLogDrift V B y ∈ ComplexMatrix2.traceless) ∧
      (∀ B ∈ complexEdgeForms L n k j, ∀ B' ∈ complexEdgeForms L n k j, ∀ c : ℂ,
        contourLogDrift V (c • B + B') = c • contourLogDrift V B + contourLogDrift V B') ∧
      (∀ l : Vertex L n k j → ComplexMatrix2, (∀ x, l x ∈ ComplexMatrix2.traceless) →
        ∀ y, adjointCubeAverage V l y ∈ ComplexMatrix2.traceless) ∧
      ∀ l l' : Vertex L n k j → ComplexMatrix2, (∀ x, l x ∈ ComplexMatrix2.traceless) →
        (∀ x, l' x ∈ ComplexMatrix2.traceless) → ∀ c : ℂ,
        adjointCubeAverage V (c • l + l') =
          c • adjointCubeAverage V l + adjointCubeAverage V l'
variable {V : Edge L n k j → ComplexMatrix2}
def IsNearOne (r : ℝ) (V : Edge L n k j → ComplexMatrix2) : Prop :=
  V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup ∧
    ∀ b, ComplexMatrix2.operatorNorm (V b - 1) < r
theorem LinearStepHypotheses.mem_small (T : LinearStepHypotheses L n k j r)
    (hV : IsNearOne r V) : V ∈ smallComplexFields L n k j :=
  ⟨hV.1, fun b => (hV.2 b).trans_le T.le_polydiscRadius⟩
theorem meanCovariantStep_mem (T : LinearStepHypotheses L n k j r) (hV : IsNearOne r V)
    {B : Edge L n k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n k j) :
    meanCovariantStep V B ∈ complexEdgeForms L n k (j + 1) := by
  refine Submodule.add_mem _ (extendOddly_mem T.orientation_xor fun b hb => ?_)
    (extendOddly_mem T.orientation_xor fun b hb => ?_)
  · have h := (T.holDiff V hV.1 hV.2).1 B b hb
    unfold Tower.holLeftDifferential at h
    rw [extendOddly_of_positive hb] at h
    exact h
  · have hl := (T.driftAndAdjoint V (T.mem_small hV)).1 B hB
    exact Submodule.sub_mem _
      (conjugateBy_traceless_of_det (T.mean_mem V hV.1 hV.2 b hb) (hl _)) (hl _)
theorem meanCovariantStep_smul_add (T : LinearStepHypotheses L n k j r) (hV : IsNearOne r V)
    {B B' : Edge L n k j → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n k j) (hB' : B' ∈ complexEdgeForms L n k j) (z : ℂ) :
    meanCovariantStep V (z • B + B') =
      z • meanCovariantStep V B + meanCovariantStep V B' := by
  unfold RunningCouplingSlope.meanCovariantStep
  rw [(T.holDiff V hV.1 hV.2).2, (T.driftAndAdjoint V (T.mem_small hV)).2.1 B hB B' hB',
    covDiff_smul_add, smul_add]
  abel
end Linear
section Iterates
variable {L n k : ℕ} {r : ℝ}
theorem meanIterate_succ_of_positive (U : Edge L n k 0 → ComplexMatrix2) {j : ℕ} (hj : j < k)
    {c : Edge L n k (j + 1)} (hc : c.IsPositivelyOriented) :
    meanIterate U (j + 1) c = normalizedMean (meanIterate U j) c := by
  show levelField (quietPoint U) (j + 1) c = _
  simp only [levelField, dif_pos hj, fieldOfPositiveValues, dif_pos hc, quietPoint, one_mul]
  rfl
theorem meanIterate_succ_of_not_positive (U : Edge L n k 0 → ComplexMatrix2) {j : ℕ} (hj : j < k)
    {c : Edge L n k (j + 1)} (hc : ¬ c.IsPositivelyOriented) (hr : c.opposite.IsPositivelyOriented) :
    meanIterate U (j + 1) c = (normalizedMean (meanIterate U j) c.opposite)⁻¹ := by
  show levelField (quietPoint U) (j + 1) c = _
  simp only [levelField, dif_pos hj, fieldOfPositiveValues, dif_neg hc, dif_pos hr, quietPoint,
    one_mul]
  rfl
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] {S : Set P} {p₀ : P}
variable {U : P → Edge L n k 0 → ComplexMatrix2}
theorem isRegularFamily_meanIterate (hp : p₀ ∈ S)
    (hs : ∀ p ∈ S, ∀ j < k, IsNearOne r (meanIterate (U p) j)) {j : ℕ} (hj : j < k)
    (hg : ∀ b, AnalyticGerm S p₀ fun p => meanIterate (U p) j b) :
    IsRegularFamily r S p₀ fun p => meanIterate (U p) j :=
  ⟨hp, hg, by filter_upwards [self_mem_nhdsWithin] with p h using (hs p h j hj).1,
    (hs p₀ hp j hj).2⟩
theorem meanIterate_analytic (F : ∀ j < k, StepHypotheses L n k j r) (hp : p₀ ∈ S)
    (hU : ∀ b, AnalyticGerm S p₀ fun p => U p b)
    (hs : ∀ p ∈ S, ∀ j < k, IsNearOne r (meanIterate (U p) j)) :
    ∀ j ≤ k, ∀ b, AnalyticGerm S p₀ fun p => meanIterate (U p) j b := by
  intro j
  induction j with
  | zero => exact fun _ b => hU b
  | succ j ih =>
    intro hj c
    have hjk : j < k := hj
    have hV := isRegularFamily_meanIterate hp hs hjk (ih hjk.le)
    by_cases hc : c.IsPositivelyOriented
    · exact (hV.normalizedMean_analytic (F j hjk) hc).1.congr_eventually
        (Eventually.of_forall fun p => (meanIterate_succ_of_positive (U p) hjk hc).symm)
    · have hr := (PeriodicLattice.Bond.positive_or_opposite_positive c).resolve_left hc
      obtain ⟨h₁, h₂⟩ := hV.normalizedMean_analytic (F j hjk) hr
      have hdet : (normalizedMean (meanIterate (U p₀) j) c.opposite).det = 1 :=
        h₂.self_of_nhdsWithin hp
      exact (h₁.matInv hp (by rw [hdet]; exact one_ne_zero)).congr_eventually
        (Eventually.of_forall fun p => (meanIterate_succ_of_not_positive (U p) hjk hc hr).symm)
end Iterates
section Products
variable {L n k : ℕ} {r : ℝ}
theorem meanCovariant_mem {U : Edge L n k 0 → ComplexMatrix2}
    (G : ∀ j < k, LinearStepHypotheses L n k j r)
    (hs : ∀ j < k, IsNearOne r (meanIterate U j)) {B : Edge L n k 0 → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n k 0) :
    ∀ j ≤ k, meanCovariant U j B ∈ complexEdgeForms L n k j := by
  intro j
  induction j with
  | zero => exact fun _ => hB
  | succ j ih =>
    intro hj
    have hjk : j < k := hj
    exact meanCovariantStep_mem (G j hjk) (hs j hjk) (ih hjk.le)
theorem meanCovariant_smul_add {U : Edge L n k 0 → ComplexMatrix2}
    (G : ∀ j < k, LinearStepHypotheses L n k j r)
    (hs : ∀ j < k, IsNearOne r (meanIterate U j)) {B B' : Edge L n k 0 → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n k 0) (hB' : B' ∈ complexEdgeForms L n k 0) (z : ℂ) :
    ∀ j ≤ k, meanCovariant U j (z • B + B') =
      z • meanCovariant U j B + meanCovariant U j B' := by
  intro j
  induction j with
  | zero => exact fun _ => rfl
  | succ j ih =>
    intro hj
    have hjk : j < k := hj
    show meanCovariantStep (meanIterate U j) (meanCovariant U j (z • B + B')) =
      z • meanCovariantStep (meanIterate U j) (meanCovariant U j B) +
        meanCovariantStep (meanIterate U j) (meanCovariant U j B')
    rw [ih hjk.le]
    exact meanCovariantStep_smul_add (G j hjk) (hs j hjk) (meanCovariant_mem G hs hB j hjk.le)
      (meanCovariant_mem G hs hB' j hjk.le) z
theorem composedCubeAverage_mem {U : Edge L n k 0 → ComplexMatrix2}
    (G : ∀ j < k, LinearStepHypotheses L n k j r)
    (hs : ∀ j < k, IsNearOne r (meanIterate U j)) {l : Vertex L n k 0 → ComplexMatrix2}
    (hl : ∀ x, l x ∈ ComplexMatrix2.traceless) :
    ∀ j ≤ k, ∀ y, composedCubeAverage (quietPoint U) j l y ∈ ComplexMatrix2.traceless := by
  intro j
  induction j with
  | zero => exact fun _ => hl
  | succ j ih =>
    intro hj y
    have hjk : j < k := hj
    exact ((G j hjk).driftAndAdjoint _ ((G j hjk).mem_small (hs j hjk))).2.2.1 _ (ih hjk.le) y
theorem composedCubeAverage_smul_add {U : Edge L n k 0 → ComplexMatrix2}
    (G : ∀ j < k, LinearStepHypotheses L n k j r)
    (hs : ∀ j < k, IsNearOne r (meanIterate U j)) {l l' : Vertex L n k 0 → ComplexMatrix2}
    (hl : ∀ x, l x ∈ ComplexMatrix2.traceless) (hl' : ∀ x, l' x ∈ ComplexMatrix2.traceless)
    (z : ℂ) :
    ∀ j ≤ k, composedCubeAverage (quietPoint U) j (z • l + l') =
      z • composedCubeAverage (quietPoint U) j l + composedCubeAverage (quietPoint U) j l' := by
  intro j
  induction j with
  | zero => exact fun _ => rfl
  | succ j ih =>
    intro hj
    have hjk : j < k := hj
    show adjointCubeAverage (levelField (quietPoint U) j)
        (composedCubeAverage (quietPoint U) j (z • l + l')) =
      z • adjointCubeAverage (levelField (quietPoint U) j)
          (composedCubeAverage (quietPoint U) j l) +
        adjointCubeAverage (levelField (quietPoint U) j) (composedCubeAverage (quietPoint U) j l')
    rw [ih hjk.le]
    exact ((G j hjk).driftAndAdjoint _ ((G j hjk).mem_small (hs j hjk))).2.2.2 _ _
      (composedCubeAverage_mem G hs hl j hjk.le) (composedCubeAverage_mem G hs hl' j hjk.le) z
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] {S : Set P} {p₀ : P}
variable {U : P → Edge L n k 0 → ComplexMatrix2}
theorem meanCovariant_analytic (F : ∀ j < k, StepHypotheses L n k j r)
    (G : ∀ j < k, LinearStepHypotheses L n k j r)
    (hp : p₀ ∈ S) (hU : ∀ b, AnalyticGerm S p₀ fun p => U p b)
    (hs : ∀ p ∈ S, ∀ j < k, IsNearOne r (meanIterate (U p) j))
    {B : Edge L n k 0 → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n k 0) :
    ∀ j ≤ k, ∀ c, AnalyticGerm S p₀ fun p => meanCovariant (U p) j B c := by
  intro j
  induction j with
  | zero => exact fun _ c => AnalyticGerm.const _
  | succ j ih =>
    intro hj c
    have hjk : j < k := hj
    have hV := isRegularFamily_meanIterate hp hs hjk (meanIterate_analytic F hp hU hs j hjk.le)
    refine hV.meanCovariantStep_analytic (F j hjk) (ih hjk.le) ?_ c
    filter_upwards [self_mem_nhdsWithin] with p h
    exact meanCovariant_mem G (hs p h) hB j hjk.le
theorem composedCubeAverage_analytic (F : ∀ j < k, StepHypotheses L n k j r)
    (hp : p₀ ∈ S) (hU : ∀ b, AnalyticGerm S p₀ fun p => U p b)
    (hs : ∀ p ∈ S, ∀ j < k, IsNearOne r (meanIterate (U p) j))
    (l : Vertex L n k 0 → ComplexMatrix2) :
    ∀ j ≤ k, ∀ y, AnalyticGerm S p₀ fun p => composedCubeAverage (quietPoint (U p)) j l y := by
  intro j
  induction j with
  | zero => exact fun _ c => AnalyticGerm.const _
  | succ j ih =>
    intro hj y
    have hjk : j < k := hj
    have hV := isRegularFamily_meanIterate hp hs hjk (meanIterate_analytic F hp hU hs j hjk.le)
    exact hV.adjointCubeAverage_analytic (F j hjk) (ih hjk.le) y
end Products
section Entries
variable {L n k : ℕ} {r : ℝ}
theorem real_smul_eq_complex_smul (η : ℝ) (X : ComplexMatrix2) : η • X = (η : ℂ) • X := by apply _root_.YangMills.SharedProofs.p9878 <;> assumption
open Classical in
def pauliForm (f : Fin 3 × PositiveEdge L n k 0 → ℂ) : Edge L n k 0 → ComplexMatrix2 :=
  extendOddly fun b => if h : b.IsPositivelyOriented then ofPauliCoeffs f ⟨b, h⟩ else 0
theorem pauliForm_mem
    (hx : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (f : Fin 3 × PositiveEdge L n k 0 → ℂ) : pauliForm f ∈ complexEdgeForms L n k 0 := by
  classical
  refine extendOddly_mem hx fun b hb => ?_
  rw [dif_pos hb]
  exact ofPauliCoeffs_mem_traceless _ _
theorem pauliForm_smul_add (z : ℂ) (f f' : Fin 3 × PositiveEdge L n k 0 → ℂ) :
    pauliForm (z • f + f') = z • pauliForm f + pauliForm f' := by
  classical
  funext b
  unfold pauliForm
  by_cases hb : b.IsPositivelyOriented
  · simp only [Pi.add_apply, Pi.smul_apply, extendOddly_of_positive hb, dif_pos hb,
      ofPauliCoeffs_smul_add]
  · have hr := (PeriodicLattice.Bond.positive_or_opposite_positive b).resolve_left hb
    simp only [Pi.add_apply, Pi.smul_apply, extendOddly_of_not_positive hb, dif_pos hr,
      ofPauliCoeffs_smul_add, smul_neg, neg_add]
def kernelMapQ (L n k : ℕ) (U : Edge L n k 0 → ComplexMatrix2)
    (f : Fin 3 × PositiveEdge L n k 0 → ℂ) : Fin 3 × PositiveEdge L n k k → ℂ :=
  fun κ => pauliCoeff κ.1 ((finestMesh L k • meanCovariant U k (pauliForm f)) κ.2.1)
def kernelMapR (L n k : ℕ) (U : Edge L n k 0 → ComplexMatrix2) (f : Fin 3 × Vertex L n k 0 → ℂ) :
    Fin 3 × Vertex L n k k → ℂ :=
  fun κ => pauliCoeff κ.1 (composedCubeAverage (quietPoint U) k (ofPauliCoeffs f) κ.2)
theorem meanKernelQ_eq (U : Edge L n k 0 → ComplexMatrix2) :
    meanKernelQ L n k U = kernelOfMap (kernelMapQ L n k U) := rfl
theorem meanKernelR_eq (U : Edge L n k 0 → ComplexMatrix2) :
    meanKernelR L n k U = kernelOfMap (kernelMapR L n k U) := rfl
theorem kernelMapQ_smul_add (G : ∀ j < k, LinearStepHypotheses L n k j r)
    (hx : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {U : Edge L n k 0 → ComplexMatrix2} (hs : ∀ j < k, IsNearOne r (meanIterate U j)) (z : ℂ)
    (f f' : Fin 3 × PositiveEdge L n k 0 → ℂ) :
    kernelMapQ L n k U (z • f + f') = z • kernelMapQ L n k U f + kernelMapQ L n k U f' := by
  funext κ
  obtain ⟨T, hT⟩ := exists_clm_pauliCoeff κ.1
  have hmem : ∀ g, meanCovariant U k (pauliForm g) κ.2.1 ∈ ComplexMatrix2.traceless := fun g =>
    (meanCovariant_mem G hs (pauliForm_mem hx g) k le_rfl).1 κ.2.1 κ.2.2
  have hsm : ∀ g, (finestMesh L k • meanCovariant U k (pauliForm g)) κ.2.1 ∈
      ComplexMatrix2.traceless := fun g => by
    rw [Pi.smul_apply, real_smul_eq_complex_smul]
    exact Submodule.smul_mem _ _ (hmem g)
  show pauliCoeff κ.1 ((finestMesh L k • meanCovariant U k (pauliForm (z • f + f'))) κ.2.1) =
    z * pauliCoeff κ.1 ((finestMesh L k • meanCovariant U k (pauliForm f)) κ.2.1) +
    pauliCoeff κ.1 ((finestMesh L k • meanCovariant U k (pauliForm f')) κ.2.1)
  rw [← hT _ (hsm _), ← hT _ (hsm _), ← hT _ (hsm _), pauliForm_smul_add,
    meanCovariant_smul_add G hs (pauliForm_mem hx f) (pauliForm_mem hx f') z k le_rfl]
  simp only [Pi.smul_apply, Pi.add_apply, real_smul_eq_complex_smul, map_add, map_smul,
    smul_eq_mul, smul_add]
  ring
theorem kernelMapR_smul_add (G : ∀ j < k, LinearStepHypotheses L n k j r)
    {U : Edge L n k 0 → ComplexMatrix2} (hs : ∀ j < k, IsNearOne r (meanIterate U j)) (z : ℂ)
    (f f' : Fin 3 × Vertex L n k 0 → ℂ) :
    kernelMapR L n k U (z • f + f') = z • kernelMapR L n k U f + kernelMapR L n k U f' := by
  funext κ
  obtain ⟨T, hT⟩ := exists_clm_pauliCoeff κ.1
  have hmem : ∀ g, composedCubeAverage (quietPoint U) k (ofPauliCoeffs g) κ.2 ∈
      ComplexMatrix2.traceless := fun g =>
    composedCubeAverage_mem G hs (ofPauliCoeffs_mem_traceless g) k le_rfl κ.2
  show pauliCoeff κ.1 (composedCubeAverage (quietPoint U) k (ofPauliCoeffs (z • f + f')) κ.2) =
    z * pauliCoeff κ.1 (composedCubeAverage (quietPoint U) k (ofPauliCoeffs f) κ.2) +
    pauliCoeff κ.1 (composedCubeAverage (quietPoint U) k (ofPauliCoeffs f') κ.2)
  rw [← hT _ (hmem _), ← hT _ (hmem _), ← hT _ (hmem _), ofPauliCoeffs_smul_add,
    composedCubeAverage_smul_add G hs (ofPauliCoeffs_mem_traceless f)
      (ofPauliCoeffs_mem_traceless f') z k le_rfl]
  simp only [Pi.smul_apply, Pi.add_apply, map_add, map_smul, smul_eq_mul]
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] {S : Set P} {p₀ : P}
variable {U : P → Edge L n k 0 → ComplexMatrix2}
theorem meanKernelQ_analytic [Finite (PositiveEdge L n k 0)]
    (F : ∀ j < k, StepHypotheses L n k j r) (G : ∀ j < k, LinearStepHypotheses L n k j r)
    (hx : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (hp : p₀ ∈ S) (hU : ∀ b, AnalyticGerm S p₀ fun p => U p b)
    (hs : ∀ p ∈ S, ∀ j < k, IsNearOne r (meanIterate (U p) j))
    (ι' : Fin 3 × PositiveEdge L n k k) (ι : Fin 3 × PositiveEdge L n k 0) :
    AnalyticGerm S p₀ fun p => meanKernelQ L n k (U p) ι' ι := by
  classical
  let _ := Fintype.ofFinite (PositiveEdge L n k 0)
  obtain ⟨T, hT⟩ := exists_clm_pauliCoeff ι'.1
  have hB : pauliForm (Pi.single ι 1) ∈ complexEdgeForms L n k 0 := pauliForm_mem hx _
  have hg := (((AnalyticGerm.const (S := S) (p₀ := p₀) ((finestMesh L k : ℝ) : ℂ)).smul
    (meanCovariant_analytic F G hp hU hs hB k le_rfl ι'.2.1))).map_clm T
  refine hg.congr_eventually ?_
  filter_upwards [self_mem_nhdsWithin] with p h
  rw [meanKernelQ_eq, kernelOfMap_apply (kernelMapQ_smul_add G hx (hs p h)) ι ι']
  show _ = pauliCoeff ι'.1 ((finestMesh L k • meanCovariant (U p) k
    (pauliForm (Pi.single ι 1))) ι'.2.1)
  rw [Pi.smul_apply, real_smul_eq_complex_smul, hT]
  exact Submodule.smul_mem _ _ ((meanCovariant_mem G (hs p h) hB k le_rfl).1 ι'.2.1 ι'.2.2)
theorem meanKernelR_analytic [Finite (Vertex L n k 0)]
    (F : ∀ j < k, StepHypotheses L n k j r) (G : ∀ j < k, LinearStepHypotheses L n k j r)
    (hp : p₀ ∈ S) (hU : ∀ b, AnalyticGerm S p₀ fun p => U p b)
    (hs : ∀ p ∈ S, ∀ j < k, IsNearOne r (meanIterate (U p) j))
    (ι' : Fin 3 × Vertex L n k k) (ι : Fin 3 × Vertex L n k 0) :
    AnalyticGerm S p₀ fun p => meanKernelR L n k (U p) ι' ι := by
  classical
  let _ := Fintype.ofFinite (Vertex L n k 0)
  obtain ⟨T, hT⟩ := exists_clm_pauliCoeff ι'.1
  have hg := (composedCubeAverage_analytic F hp hU hs (ofPauliCoeffs (Pi.single ι 1)) k le_rfl
    ι'.2).map_clm T
  refine hg.congr_eventually ?_
  filter_upwards [self_mem_nhdsWithin] with p h
  rw [meanKernelR_eq, kernelOfMap_apply (kernelMapR_smul_add G (hs p h)) ι ι']
  show _ = pauliCoeff ι'.1 (composedCubeAverage (quietPoint (U p)) k
    (ofPauliCoeffs (Pi.single ι 1)) ι'.2)
  rw [hT]
  exact composedCubeAverage_mem G (hs p h) (ofPauliCoeffs_mem_traceless _) k le_rfl ι'.2
end Entries
section Generic
variable {σ : Type} [Fintype σ]
theorem operatorNorm_le_supNorm (A : σ → ComplexMatrix2) (i : σ) :
    ComplexMatrix2.operatorNorm (A i) ≤ GroupLieProduct.supNorm A :=
  le_ciSup (f := fun i => ComplexMatrix2.operatorNorm (A i)) (Set.finite_range _).bddAbove i
theorem supNorm_lt_iff {ρ : ℝ} (hρ : 0 < ρ) (A : σ → ComplexMatrix2) :
    GroupLieProduct.supNorm A < ρ ↔ ∀ i, ComplexMatrix2.operatorNorm (A i) < ρ := by apply _root_.YangMills.SharedProofs.p9363 <;> assumption
theorem isOpen_supNorm_lt {ρ : ℝ} (hρ : 0 < ρ) :
    IsOpen {A : σ → ComplexMatrix2 | GroupLieProduct.supNorm A < ρ} := by
  simp_rw [supNorm_lt_iff hρ, Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_lt ((continuous_apply i).norm) continuous_const
theorem isSupOpen_supBall {ρ : ℝ} (hρ : 0 < ρ) :
    GroupLieProduct.IsSupOpen (GroupLieProduct.supBall σ ρ) := by
  refine ⟨fun A hA => hA.1, fun A hA => ⟨ρ - GroupLieProduct.supNorm A, sub_pos.2 hA.2, ?_⟩⟩
  intro B hB hlt
  refine ⟨hB, (supNorm_lt_iff hρ B).2 fun i => ?_⟩
  have h₁ := operatorNorm_le_supNorm (B - A) i
  have h₂ := operatorNorm_le_supNorm A i
  have h₃ : ‖B i‖ ≤ ‖(B - A) i‖ + ‖A i‖ := by
    have := norm_add_le ((B - A) i) (A i)
    simpa using this
  simp only [ComplexMatrix2.operatorNorm] at h₁ h₂ ⊢
  linarith
def tupleOfCoordsLinear (e : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (ν : σ ≃ Fin (Fintype.card σ)) :
    Coordinates.ComplexCoordinates (Fintype.card σ * 3) →ₗ[ℂ] (σ → ComplexMatrix2) where
  toFun := GroupLieProduct.tupleOfCoords e ν
  map_add' w w' := by
    funext i
    simp [GroupLieProduct.tupleOfCoords, Coordinates.ComplexCoordinates.tracelessTuple, add_smul,
      Finset.sum_add_distrib]
  map_smul' c w := by
    funext i
    simp [GroupLieProduct.tupleOfCoords, Coordinates.ComplexCoordinates.tracelessTuple, mul_smul,
      Finset.smul_sum]
theorem tupleOfCoords_mem (e : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (ν : σ ≃ Fin (Fintype.card σ)) (w : Coordinates.ComplexCoordinates (Fintype.card σ * 3)) :
    GroupLieProduct.tupleOfCoords e ν w ∈ GroupLieProduct.tracelessPi σ := by apply _root_.YangMills.Construction.Matrices.GroupLieProduct.Subspaces.RealForm.tupleOfCoords_mem <;> assumption
theorem isHolomorphicOnTraceless_of_analyticGerm {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {l : ℕ}
    (c : E ≃ Coordinates.ComplexCoordinates l) (Tc : E →L[ℂ] Coordinates.ComplexCoordinates l)
    (hTc : ∀ x, Tc x = c x)
    {ρ : ℝ} (hρ : 0 < ρ) (e : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    {f : (σ → ComplexMatrix2) → E}
    (hf : ∀ A₀ ∈ GroupLieProduct.supBall σ ρ,
      AnalyticGerm (GroupLieProduct.supBall σ ρ) A₀ f) :
    GroupLieProduct.IsHolomorphicOnTraceless e c (GroupLieProduct.supBall σ ρ) f := by
  refine ⟨isSupOpen_supBall hρ, fun ν => ?_⟩
  set T := GroupLieProduct.tupleOfCoords e ν with hT
  have hTc' : Continuous T :=
    (LinearMap.toContinuousLinearMap (tupleOfCoordsLinear e ν)).continuous
  have hset : T ⁻¹' GroupLieProduct.supBall σ ρ =
      T ⁻¹' {A | GroupLieProduct.supNorm A < ρ} := by
    ext w
    exact ⟨fun h => h.2, fun h => ⟨tupleOfCoords_mem e ν w, h⟩⟩
  have hS : IsOpen (T ⁻¹' GroupLieProduct.supBall σ ρ) := by
    rw [hset]
    exact (isOpen_supNorm_lt hρ).preimage hTc'
  have hAn : ∀ w ∈ T ⁻¹' GroupLieProduct.supBall σ ρ, AnalyticAt ℂ (c ∘ f ∘ T) w := by
    intro w hw
    obtain ⟨H, hH, hev⟩ := hf (T w) hw
    have htend : Tendsto T (𝓝 w) (𝓝[GroupLieProduct.supBall σ ρ] (T w)) :=
      tendsto_nhdsWithin_iff.2 ⟨hTc'.tendsto w, hS.mem_nhds hw⟩
    have hH' : AnalyticAt ℂ (fun v => Tc
        (H (LinearMap.toContinuousLinearMap (tupleOfCoordsLinear e ν) v))) w :=
      (Tc.analyticAt _).comp
        (AnalyticAt.comp (f := LinearMap.toContinuousLinearMap (tupleOfCoordsLinear e ν)) hH
          (ContinuousLinearMap.analyticAt _ _))
    refine hH'.congr ?_
    filter_upwards [htend.eventually hev] with v hv
    change Tc (H (T v)) = c (f (T v))
    rw [hv, hTc]
  refine ⟨hS, fun w hw => (hAn w hw).continuousAt.continuousWithinAt, fun a ha j => ?_⟩
  have hline : Continuous fun ζ : ℂ =>
      a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j := by fun_prop
  have hnear : ∀ᶠ ζ in 𝓝 (0 : ℂ),
      a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j ∈
        T ⁻¹' GroupLieProduct.supBall σ ρ :=
    (hS.preimage hline).mem_nhds (by simpa using ha)
  filter_upwards [hnear] with ζ hζ
  have hd : DifferentiableAt ℂ
      (fun ζ : ℂ => a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j) ζ := by
    fun_prop
  exact DifferentiableAt.comp (g := c ∘ f ∘ T) ζ (hAn _ hζ).differentiableAt hd
def matrixEquivCLM : ComplexMatrix2 →L[ℂ] Coordinates.ComplexCoordinates 4 :=
  LinearMap.toContinuousLinearMap
    { toFun := Coordinates.ComplexCoordinates.matrixEquiv
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
def scalarCoordsCLM : ℂ →L[ℂ] Coordinates.ComplexCoordinates 1 :=
  LinearMap.toContinuousLinearMap
    { toFun := Tower.LeftChartFields.scalarCoords
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
end Generic
section Family
variable {L n k : ℕ} {F : Finset (Edge L n k 0)}
def antisymmetrize (hF : ∀ b, b ∈ F) (A : F → ComplexMatrix2) : Edge L n k 0 → ComplexMatrix2 :=
  fun b => (1 / 2 : ℂ) • (A ⟨b, hF b⟩ - A ⟨b.opposite, hF _⟩)
theorem antisymmetrize_of_form (hF : ∀ b, b ∈ F) {a : Edge L n k 0 → ComplexMatrix2}
    (ha : a ∈ complexEdgeForms L n k 0) : antisymmetrize hF (fun b => a b) = a := by
  funext b
  have h : a b.opposite = -a b := ha.2 b
  simp only [antisymmetrize, h, sub_neg_eq_add]
  rw [← two_smul ℂ (a b), smul_smul]
  norm_num
theorem antisymmetrize_mem (hF : ∀ b, b ∈ F) {ρ : ℝ} {A : F → ComplexMatrix2}
    (hA : A ∈ GroupLieProduct.supBall F ρ) :
    antisymmetrize hF A ∈ complexEdgeForms L n k 0 := by
  refine ⟨fun b _ => ?_, fun b => ?_⟩
  · exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (hA.1 _) (hA.1 _))
  · simp only [antisymmetrize, PeriodicLattice.Bond.opposite_opposite]
    rw [← smul_neg, neg_sub]
theorem maxOperatorNorm_antisymmetrize_lt (hF : ∀ b, b ∈ F) {ρ : ℝ} (hρ : 0 < ρ)
    {A : F → ComplexMatrix2} (hA : A ∈ GroupLieProduct.supBall F ρ) :
    maxOperatorNorm (antisymmetrize hF A) < ENNReal.ofReal ρ := by
  have hle : maxOperatorNorm (antisymmetrize hF A) ≤
      ENNReal.ofReal (GroupLieProduct.supNorm A) := by
    refine iSup_le fun b => ENNReal.ofReal_le_ofReal ?_
    have h₁ := operatorNorm_le_supNorm A ⟨b, hF b⟩
    have h₂ := operatorNorm_le_supNorm A ⟨b.opposite, hF _⟩
    have h₃ := norm_sub_le (A ⟨b, hF b⟩) (A ⟨b.opposite, hF _⟩)
    simp only [ComplexMatrix2.operatorNorm, antisymmetrize, norm_smul] at h₁ h₂ ⊢
    norm_num
    linarith
  exact hle.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hρ).2 hA.2)
def exponentCLM (hF : ∀ b, b ∈ F) (b : Edge L n k 0) : (F → ComplexMatrix2) →L[ℂ] ComplexMatrix2 :=
  (Complex.I * (finestMesh L k : ℂ) * (1 / 2 : ℂ)) •
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : F => ComplexMatrix2) ⟨b, hF b⟩ -
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : F => ComplexMatrix2) ⟨b.opposite, hF _⟩)
theorem exponentCLM_apply (hF : ∀ b, b ∈ F) (b : Edge L n k 0) (A : F → ComplexMatrix2) :
    exponentCLM hF b A = Complex.I • scaledRemainderForm (antisymmetrize hF A) b := by
  ext r s
  simp [exponentCLM, scaledRemainderForm, antisymmetrize, Matrix.smul_apply]
  ring
theorem remainderGaugeField_antisymmetrize_analytic (hF : ∀ b, b ∈ F) {ρ : ℝ}
    (b : Edge L n k 0) (A₀ : F → ComplexMatrix2) :
    AnalyticGerm (GroupLieProduct.supBall F ρ) A₀
      fun A => remainderGaugeField (antisymmetrize hF A) b := by
  refine ⟨fun A => ComplexMatrix2.matExp (exponentCLM hF b A),
    AnalyticAt.comp (f := exponentCLM hF b)
      (NormedSpace.exp_analytic (𝕂 := ℂ) _) (ContinuousLinearMap.analyticAt _ _), ?_⟩
  filter_upwards [self_mem_nhdsWithin] with A hA
  change IdentityExpChart.expForm (scaledRemainderForm (antisymmetrize hF A)) b = _
  have hrev : scaledRemainderForm (antisymmetrize hF A) b.opposite =
      -scaledRemainderForm (antisymmetrize hF A) b := by
    have h : antisymmetrize hF A b.opposite = -antisymmetrize hF A b :=
      (antisymmetrize_mem hF hA).2 b
    simp only [scaledRemainderForm, Pi.smul_apply, h, smul_neg]
  unfold IdentityExpChart.expForm PeriodicLattice.expTwist
  rw [exponentCLM_apply]
  split_ifs with hb
  · simp
  · rw [Pi.one_apply, mul_one, hrev, smul_neg]
    have h := Matrix.exp_neg (-(Complex.I • scaledRemainderForm (antisymmetrize hF A) b))
    rw [neg_neg] at h
    exact h.symm
end Family
theorem claim_of_components (hNear : NormalizedMeanNearOne)
    (hDiff : HolDifferentialLinear)
    (hAvg : Tower.SmoothingNearIdentity)
    (hCont : Tower.PairContourIndependence.Statement)
    (hLin : Tower.StepMapsComplexLinear.Claim)
    (hE : ComplexMatrix2.ExpLogEstimates)
    (hChart : Tower.LeftChartFields.Claim)
    (hO : PeriodicLattice.BondEndpointsOrientation.Statement) :
    Claim := by
  intro L hL
  obtain ⟨ρ₂, hρ₂, hnear⟩ := hNear L hL
  obtain ⟨ρ₃, hρ₃, hdiff⟩ := hDiff L hL
  have hrad := (hAvg.1 L hL).2.2
  obtain ⟨r, hr, hr₀, hr₂, hr₃⟩ : ∃ r : ℝ, 0 < r ∧ r ≤ polydiscRadius L ∧ r ≤ ρ₂ ∧ r ≤ ρ₃ :=
    ⟨min (polydiscRadius L) (min ρ₂ ρ₃), lt_min hrad.pos (lt_min hρ₂ hρ₃), min_le_left _ _,
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  refine ⟨r, hr, fun ρ hρ n k hn hk hprem => ?_⟩
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL.2
  have hsites : ∀ j, Finite (Vertex L n k j) := fun j =>
    SeparatedSequences.BaseParameters.site_finite hLpos n _
  have hbonds : ∀ j, Finite (Edge L n k j) := fun j =>
    have := hsites j
    Finite.of_injective (fun b : Edge L n k j => (b.source, b.target)) fun b b' hb =>
      PeriodicLattice.Bond.ext (congrArg Prod.fst hb) (congrArg Prod.snd hb)
  have hxor : ∀ j ≤ k, ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := fun j hj b =>
    ((hO ⟨L, hL, ⟨k, hk⟩, ⟨n, hn⟩⟩ j hj).2.2.2 b).2.2.2.2.2
  have hsmallNear : ∀ j < k, ∀ V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
      (∀ b, ComplexMatrix2.operatorNorm (V b - 1) < r) →
      ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
        ‖meanRadius V c - 1‖ < 1 / 2 ∧ normalizedMean V c ∈ PeriodicLattice.complexGaugeGroup := by
    intro j hj V hV hb c hc
    have h := hnear n k j hn hj V hV (fun b => (hb b).trans_le hr₂) c hc
    exact ⟨h.2.1, h.2.2.2.1⟩
  have F : ∀ j < k, StepHypotheses L n k j r := fun j hj =>
    { finite_edges := hbonds j
      finite_vertices := hsites j
      orientation_xor := hxor j hj.le
      expLog := hE
      curve_logs := hChart.2.1
      mean_near_one := hsmallNear j hj
      le_polydiscRadius := hr₀
      admissible := fun c hc => hrad.periodic n k j hn hj c hc
      contour_local := fun y x hx c hc hy W hW hWn W' hr' =>
        ((hCont L hL k j hj).1 n hn y x hx c c hc hc hy hy W hW (fun b _ => hWn b)
          (fun b _ => hWn b) W' W hr' (fun _ _ => rfl)).2.2 }
  have G : ∀ j < k, LinearStepHypotheses L n k j r := fun j hj =>
    { le_polydiscRadius := hr₀
      orientation_xor := hxor (j + 1) hj
      mean_mem := fun V hV hb c hc => (hsmallNear j hj V hV hb c hc).2
      holDiff := fun V hV hb => hdiff n k j hn hj V hV fun b => (hb b).trans_le hr₃
      driftAndAdjoint := fun V hV => by
        have h := hLin L hL n k j hn hj V hV
        exact ⟨fun B hB => (h.1 B hB).2, fun B hB B' hB' c => (h.2.1 B hB B' hB' c).2,
          fun l hl => (h.2.2.1 l hl).2, fun l l' hl hl' c => (h.2.2.2 l l' hl hl' c).2⟩ }
  have := hbonds 0
  have := hsites 0
  have hPfin : Finite (PositiveEdge L n k 0) := Subtype.finite
  let _ := Fintype.ofFinite (Edge L n k 0)
  have hF : ∀ b : Edge L n k 0, b ∈ (Finset.univ : Finset (Edge L n k 0)) := Finset.mem_univ
  have hsm : ∀ A ∈ GroupLieProduct.supBall (Finset.univ : Finset (Edge L n k 0)) ρ, ∀ j < k,
      IsNearOne r (meanIterate (remainderGaugeField (antisymmetrize hF A)) j) :=
    fun A hA j hj => hprem _ (antisymmetrize_mem hF hA)
      (maxOperatorNorm_antisymmetrize_lt hF hρ hA) j hj
  have hvalues : ∀ a ∈ complexEdgeForms L n k 0,
      remainderGaugeField (antisymmetrize hF fun b => a b) = remainderGaugeField a := by
    intro a ha
    rw [antisymmetrize_of_form hF ha]
  refine ⟨fun j hj b => ⟨Finset.univ,
      fun A => meanIterate (remainderGaugeField (antisymmetrize hF A)) j b,
      fun e => isHolomorphicOnTraceless_of_analyticGerm _ matrixEquivCLM (fun _ => rfl) hρ e
        fun A₀ hA₀ => meanIterate_analytic F hA₀
          (fun b => remainderGaugeField_antisymmetrize_analytic hF b A₀) hsm j hj b,
      fun a ha _ => by
        beta_reduce
        rw [hvalues a ha]⟩,
    fun ι' ι => ⟨Finset.univ,
      fun A => meanKernelQ L n k (remainderGaugeField (antisymmetrize hF A)) ι' ι,
      fun e => isHolomorphicOnTraceless_of_analyticGerm _ scalarCoordsCLM (fun _ => rfl) hρ e
        fun A₀ hA₀ => meanKernelQ_analytic F G (hxor 0 (Nat.zero_le k)) hA₀
          (fun b => remainderGaugeField_antisymmetrize_analytic hF b A₀) hsm ι' ι,
      fun a ha _ => by
        beta_reduce
        rw [hvalues a ha]⟩,
    fun ι' ι => ⟨Finset.univ,
      fun A => meanKernelR L n k (remainderGaugeField (antisymmetrize hF A)) ι' ι,
      fun e => isHolomorphicOnTraceless_of_analyticGerm _ scalarCoordsCLM (fun _ => rfl) hρ e
        fun A₀ hA₀ => meanKernelR_analytic F G hA₀
          (fun b => remainderGaugeField_antisymmetrize_analytic hF b A₀) hsm ι' ι,
      fun a ha _ => by
        beta_reduce
        rw [hvalues a ha]⟩⟩
end YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear
end
