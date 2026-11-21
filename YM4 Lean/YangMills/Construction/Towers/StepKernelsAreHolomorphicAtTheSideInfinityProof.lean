import YangMills.Construction.Matrices.CalculusOfHolomorphicMapsProof
import YangMills.Construction.Towers.LinearityOfTheCovariantStepAtTheSideInfinityProof
import YangMills.Construction.Towers.StepKernelsAreHolomorphicAtTheSideInfinity
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.StepKernelHolomorphy
open Matrices Matrices.GroupLieProduct Coordinates
open LeftChartFields (CurveLogDerivative)
instance instCompleteSpaceComplexMatrix2 : CompleteSpace ComplexMatrix2 :=
  FiniteDimensional.complete ℂ ComplexMatrix2
def adjugateLin : ComplexMatrix2 →ₗ[ℂ] ComplexMatrix2 where
  toFun X := Matrix.adjugate X
  map_add' X Y := by
    simp only [Matrix.adjugate_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
  map_smul' c X := by
    simp only [Matrix.adjugate_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
def adjugateCLM : ComplexMatrix2 →L[ℂ] ComplexMatrix2 :=
  LinearMap.toContinuousLinearMap adjugateLin
theorem inv_eq_adjugateCLM {X : ComplexMatrix2} (h : X ∈ PeriodicLattice.complexGaugeGroup) :
    X⁻¹ = adjugateCLM X := by
  have hdet : X.det = 1 := h
  show X⁻¹ = Matrix.adjugate X
  rw [Matrix.inv_def, hdet]
  simp
def pauliCoeffLin (a : Fin 3) : ComplexMatrix2 →ₗ[ℂ] ℂ where
  toFun X := ![(X 0 1 + X 1 0) / 2, (X 1 0 - X 0 1) / (2 * Complex.I), X 0 0] a
  map_add' X Y := by
    fin_cases a <;> simp <;> ring
  map_smul' c X := by
    fin_cases a <;> simp <;> ring
def pauliCoeffCLM (a : Fin 3) : ComplexMatrix2 →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap (pauliCoeffLin a)
theorem pauliCoeff_eq_pauliCoeffCLM (a : Fin 3) {X : ComplexMatrix2}
    (h : X ∈ ComplexMatrix2.traceless) : Tower.pauliCoeff a X = pauliCoeffCLM a X := by
  unfold Tower.pauliCoeff
  rw [dif_pos h]
  rfl
section AnalyticGerms
variable {σ : Type} [Fintype σ] {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
def HasAnalyticGerms (D : Set (σ → ComplexMatrix2)) (g : (σ → ComplexMatrix2) → E) : Prop :=
  ∀ x ∈ D, ∃ G : (σ → ComplexMatrix2) → E, AnalyticAt ℂ G x ∧ ∀ᶠ y in 𝓝[D] x, g y = G y
variable {D D' : Set (σ → ComplexMatrix2)}
theorem HasAnalyticGerms.mono {g : (σ → ComplexMatrix2) → E} (h : HasAnalyticGerms D g)
    (hs : D' ⊆ D) : HasAnalyticGerms D' g :=
  fun x hx => let ⟨G, hG, he⟩ := h x (hs hx); ⟨G, hG, he.filter_mono (nhdsWithin_mono _ hs)⟩
theorem HasAnalyticGerms.congr {g g' : (σ → ComplexMatrix2) → E} (h : HasAnalyticGerms D g)
    (he : ∀ y ∈ D, g' y = g y) : HasAnalyticGerms D g' := fun x hx => by
  obtain ⟨G, hG, hge⟩ := h x hx
  refine ⟨G, hG, ?_⟩
  filter_upwards [hge, self_mem_nhdsWithin] with y h1 h2
  rw [he y h2, h1]
theorem HasAnalyticGerms.const (c : E) : HasAnalyticGerms D fun _ => c :=
  fun _ _ => ⟨fun _ => c, analyticAt_const, Eventually.of_forall fun _ => rfl⟩
theorem HasAnalyticGerms.add {g g' : (σ → ComplexMatrix2) → E} (h : HasAnalyticGerms D g)
    (h' : HasAnalyticGerms D g') : HasAnalyticGerms D fun v => g v + g' v := fun x hx => by
  obtain ⟨G, hG, he⟩ := h x hx
  obtain ⟨G', hG', he'⟩ := h' x hx
  refine ⟨fun v => G v + G' v, hG.add hG', ?_⟩
  filter_upwards [he, he'] with y h1 h2
  rw [h1, h2]
theorem HasAnalyticGerms.sub {g g' : (σ → ComplexMatrix2) → E} (h : HasAnalyticGerms D g)
    (h' : HasAnalyticGerms D g') : HasAnalyticGerms D fun v => g v - g' v := fun x hx => by
  obtain ⟨G, hG, he⟩ := h x hx
  obtain ⟨G', hG', he'⟩ := h' x hx
  refine ⟨fun v => G v - G' v, hG.sub hG', ?_⟩
  filter_upwards [he, he'] with y h1 h2
  rw [h1, h2]
theorem HasAnalyticGerms.mul {g g' : (σ → ComplexMatrix2) → ComplexMatrix2}
    (h : HasAnalyticGerms D g) (h' : HasAnalyticGerms D g') :
    HasAnalyticGerms D fun v => g v * g' v := fun x hx => by
  obtain ⟨G, hG, he⟩ := h x hx
  obtain ⟨G', hG', he'⟩ := h' x hx
  refine ⟨fun v => G v * G' v, hG.mul hG', ?_⟩
  filter_upwards [he, he'] with y h1 h2
  rw [h1, h2]
theorem HasAnalyticGerms.clm {g : (σ → ComplexMatrix2) → E} (h : HasAnalyticGerms D g)
    (T : E →L[ℂ] F) : HasAnalyticGerms D fun v => T (g v) := fun x hx => by
  obtain ⟨G, hG, he⟩ := h x hx
  refine ⟨fun v => T (G v), (T.analyticAt _).comp hG, ?_⟩
  filter_upwards [he] with y h1
  rw [h1]
theorem HasAnalyticGerms.smul {g : (σ → ComplexMatrix2) → E} (h : HasAnalyticGerms D g)
    (c : ℂ) : HasAnalyticGerms D fun v => c • g v :=
  h.clm (c • ContinuousLinearMap.id ℂ E)
theorem HasAnalyticGerms.sum {ι : Type} (s : Finset ι) {g : ι → (σ → ComplexMatrix2) → E}
    (h : ∀ i ∈ s, HasAnalyticGerms D (g i)) : HasAnalyticGerms D fun v => ∑ i ∈ s, g i v := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasAnalyticGerms.const (0 : E)
  | insert i s hi ih =>
    have := (h i (Finset.mem_insert_self _ _)).add
      (ih fun i' hi' => h i' (Finset.mem_insert_of_mem hi'))
    refine this.congr fun _ _ => ?_
    rw [Finset.sum_insert hi]
theorem HasAnalyticGerms.inv {g : (σ → ComplexMatrix2) → ComplexMatrix2}
    (h : HasAnalyticGerms D g) (hm : MapsTo g D PeriodicLattice.complexGaugeGroup) :
    HasAnalyticGerms D fun v => (g v)⁻¹ :=
  (h.clm adjugateCLM).congr fun _ hy => inv_eq_adjugateCLM (hm hy)
end AnalyticGerms
section LogCurves
variable {σ : Type}
def expMoved (v A : σ → ComplexMatrix2) (z : ℂ) : σ → ComplexMatrix2 :=
  fun b => ComplexMatrix2.matExp (Complex.I • (z • A b)) * v b
def logDerivAlong (Φ : (σ → ComplexMatrix2) → ComplexMatrix2) (A v : σ → ComplexMatrix2) :
    ComplexMatrix2 :=
  Complex.I⁻¹ • deriv (fun z => ComplexMatrix2.logSeries (Φ (expMoved v A z) * (Φ v)⁻¹)) 0
def IsTangentDirection (A v : σ → ComplexMatrix2) : Prop :=
  (∀ z b, expMoved v A z b ∈ PeriodicLattice.complexGaugeGroup) ∧
    ∀ b, HasDerivAt (fun z => expMoved v A z b) (Complex.I • A b * v b) 0
variable [Fintype σ]
omit [Fintype σ] in
theorem expMoved_zero (v A : σ → ComplexMatrix2) : expMoved v A 0 = v := by
  funext b
  simp [expMoved]
theorem eventually_expMoved_mem {D : Set (σ → ComplexMatrix2)}
    (hD : ComplexMatrix2.IsRelativelyOpen (unimodularPi σ) D)
    {A v : σ → ComplexMatrix2} (hv : v ∈ D) (hA : IsTangentDirection A v) :
    ∀ᶠ z in 𝓝 (0 : ℂ), expMoved v A z ∈ D := by
  obtain ⟨O, hO, hOe⟩ := hD
  have hd : HasDerivAt (expMoved v A) (fun b => Complex.I • A b * v b) 0 :=
    hasDerivAt_pi.2 hA.2
  have hvO : expMoved v A 0 ∈ O := by
    rw [expMoved_zero]
    rw [hOe] at hv
    exact hv.1
  filter_upwards [hd.continuousAt.eventually (hO.mem_nhds hvO)] with z hz
  rw [hOe]
  exact ⟨hz, fun b => hA.1 z b⟩
theorem logDerivAlong_eq
    (hlog : ∀ ρ : ℝ, 0 < ρ → CurveLogDerivative ℂ (Metric.ball 0 ρ)
      PeriodicLattice.complexGaugeGroup PeriodicLattice.complexLieAlgebra)
    {D : Set (σ → ComplexMatrix2)} (hD : ComplexMatrix2.IsRelativelyOpen (unimodularPi σ) D)
    {Φ G : (σ → ComplexMatrix2) → ComplexMatrix2}
    (hmaps : MapsTo Φ D PeriodicLattice.complexGaugeGroup) {v A : σ → ComplexMatrix2}
    (hv : v ∈ D) (hG : AnalyticAt ℂ G v) (hGe : ∀ᶠ y in 𝓝[D] v, Φ y = G y)
    (hA : IsTangentDirection A v) :
    logDerivAlong Φ A v =
      Complex.I⁻¹ • (fderiv ℂ G v (fun b => Complex.I • A b * v b) * (Φ v)⁻¹) := by
  have hd : HasDerivAt (expMoved v A) (fun b => Complex.I • A b * v b) 0 :=
    hasDerivAt_pi.2 hA.2
  have hv0 := expMoved_zero v A
  have hnear := eventually_expMoved_mem hD hv hA
  have htend : Tendsto (expMoved v A) (𝓝 0) (𝓝[D] v) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, hnear⟩
    have := hd.continuousAt.tendsto
    rwa [hv0] at this
  have hev := htend.eventually hGe
  have hGd : HasFDerivAt G (fderiv ℂ G v) (expMoved v A 0) := by
    rw [hv0]
    exact hG.differentiableAt.hasFDerivAt
  have hψ : HasDerivAt (fun z => Φ (expMoved v A z))
      (fderiv ℂ G v (fun b => Complex.I • A b * v b)) 0 :=
    (hGd.comp_hasDerivAt (0 : ℂ) hd).congr_of_eventuallyEq hev
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hnear
  have hmaps' : MapsTo (fun z => Φ (expMoved v A z)) (Metric.ball 0 r)
      PeriodicLattice.complexGaugeGroup := fun z hz => hmaps (hball z hz)
  obtain ⟨-, -, e, -⟩ := hlog r hr _ hmaps' hψ.differentiableAt
  simp only [hv0, hψ.deriv] at e
  exact e
theorem HasAnalyticGerms.logDeriv
    (hlog : ∀ ρ : ℝ, 0 < ρ → CurveLogDerivative ℂ (Metric.ball 0 ρ)
      PeriodicLattice.complexGaugeGroup PeriodicLattice.complexLieAlgebra)
    {D : Set (σ → ComplexMatrix2)} (hD : ComplexMatrix2.IsRelativelyOpen (unimodularPi σ) D)
    {Φ : (σ → ComplexMatrix2) → ComplexMatrix2} (hΦ : HasAnalyticGerms D Φ)
    (hmaps : MapsTo Φ D PeriodicLattice.complexGaugeGroup) {A : σ → ComplexMatrix2}
    (hA : ∀ v ∈ D, IsTangentDirection A v) : HasAnalyticGerms D (logDerivAlong Φ A) :=
  fun x hx => by
  obtain ⟨G, hG, hGe⟩ := hΦ x hx
  have hw : AnalyticAt ℂ (fun v : σ → ComplexMatrix2 => fun b => Complex.I • A b * v b) x :=
    analyticAt_pi_iff.2 fun b => analyticAt_const.mul
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ComplexMatrix2) b).analyticAt x)
  refine ⟨fun v => Complex.I⁻¹ • (fderiv ℂ G v (fun b => Complex.I • A b * v b) *
    adjugateCLM (G v)), ?_, ?_⟩
  · have hb := (ContinuousLinearMap.id ℂ ((σ → ComplexMatrix2) →L[ℂ] ComplexMatrix2)).analyticAt_bilinear
      (fderiv ℂ G x, fun b => Complex.I • A b * x b)
    have hf : AnalyticAt ℂ (fderiv ℂ G) x := hG.fderiv
    have hp : AnalyticAt ℂ
        (fun v : σ → ComplexMatrix2 => fderiv ℂ G v (fun b => Complex.I • A b * v b)) x :=
      AnalyticAt.comp
        (g := fun q : ((σ → ComplexMatrix2) →L[ℂ] ComplexMatrix2) × (σ → ComplexMatrix2) =>
          q.1 q.2)
        (f := fun v => (fderiv ℂ G v, fun b => Complex.I • A b * v b)) hb (hf.prod hw)
    exact analyticAt_const.fun_smul (hp.fun_mul ((adjugateCLM.analyticAt _).comp hG))
  · have h1 : ∀ᶠ y in 𝓝[D] x, ∀ᶠ y' in 𝓝[D] y, Φ y' = G y' :=
      eventually_eventually_nhdsWithin.2 hGe
    have h2 : ∀ᶠ y in 𝓝[D] x, AnalyticAt ℂ G y :=
      hG.eventually_analyticAt.filter_mono nhdsWithin_le_nhds
    filter_upwards [h1, h2, hGe, self_mem_nhdsWithin] with y e1 e2 e3 e4
    rw [logDerivAlong_eq hlog hD hmaps e4 e2 e1 (hA y e4), inv_eq_adjugateCLM (hmaps e4), e3]
end LogCurves
section ExpCharts
variable {σ : Type} [Fintype σ]
open DoubleBlockPolydisc (leftComponents)
open LeftChartFields (scalarCoords)
omit [Fintype σ] in
theorem scalarCoords_apply (z : ℂ) (i : Fin 1) : scalarCoords z i = z := by apply _root_.YangMills.DeltaSharedProofs.p23888 <;> assumption
theorem isHolomorphicIn_congr {N N' : ℕ} {O : Set (ComplexCoordinates N)}
    {f g : ComplexCoordinates N → ComplexCoordinates N'}
    (h : ComplexCoordinates.IsHolomorphicIn O f) (e : ∀ a ∈ O, g a = f a) :
    ComplexCoordinates.IsHolomorphicIn O g := by apply _root_.YangMills.SharedProofs.p63802 <;> assumption
def matrixPiCLE {τ : Type} [Fintype τ] {k : ℕ} (ν : τ ≃ Fin k) :
    (τ → ComplexMatrix2) ≃L[ℂ] ComplexCoordinates
      (ComplexCoordinates.productDim fun _ : Fin k => ComplexCoordinates.Component.matrix) :=
  LinearEquiv.toContinuousLinearEquiv
    { matrixPiEquiv ν with
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
theorem isHolomorphicToCoords_of_differentiableOn
    (hE : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory) {O : Set (σ → ComplexMatrix2)}
    (hO : IsOpen O) {Φ : (σ → ComplexMatrix2) → ℂ}
    (hΦ : DifferentiableOn ℂ (fun v => scalarCoords (Φ v)) O) :
    ∀ b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless,
      IsHolomorphicToCoords b scalarCoords
        ((leftComponents ⁻¹' O : Set (σ ⊕ Empty → ComplexMatrix2)) ∩ GroupLieProduct σ Empty)
        fun q => Φ (leftComponents q) := by
  let ν : σ ⊕ Empty ≃ Fin (Fintype.card (σ ⊕ Empty)) := Fintype.equivFin _
  have hcont : Continuous (leftComponents : (σ ⊕ Empty → ComplexMatrix2) → σ → ComplexMatrix2) :=
    continuous_pi fun r => continuous_apply _
  have hdiff :
      Differentiable ℂ (leftComponents : (σ ⊕ Empty → ComplexMatrix2) → σ → ComplexMatrix2) :=
    differentiable_pi.2 fun r => differentiable_apply _
  have hO' : IsOpen (leftComponents ⁻¹' O : Set (σ ⊕ Empty → ComplexMatrix2)) :=
    hO.preimage hcont
  refine (((hE.2.2.2.1 σ Empty).2.2) ℂ 1 _ scalarCoords ν _ _ ?_).2
  unfold ComplexCoordinates.IsHolomorphicVia
  have himg : matrixPiEquiv ν '' (leftComponents ⁻¹' O) =
      (matrixPiCLE ν).symm ⁻¹' (leftComponents ⁻¹' O) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : (matrixPiCLE ν).symm (matrixPiEquiv ν x) = x :=
        (matrixPiEquiv ν).symm_apply_apply x
      simpa [this] using hx
    · intro hz
      exact ⟨(matrixPiCLE ν).symm z, hz, (matrixPiEquiv ν).apply_symm_apply z⟩
  have hfun : (scalarCoords ∘ (fun q => Φ (leftComponents q)) ∘ (matrixPiEquiv ν).symm) =
      fun z => scalarCoords (Φ (leftComponents ((matrixPiCLE ν).symm z))) := rfl
  rw [himg, hfun]
  have hopen : IsOpen ((matrixPiCLE ν).symm ⁻¹' (leftComponents ⁻¹' O)) :=
    hO'.preimage (matrixPiCLE ν).symm.continuous
  have hd : DifferentiableOn ℂ
      (fun z => scalarCoords (Φ (leftComponents ((matrixPiCLE ν).symm z))))
      ((matrixPiCLE ν).symm ⁻¹' (leftComponents ⁻¹' O)) := fun z hz => by
    have h₁ : DifferentiableAt ℂ (fun v => scalarCoords (Φ v))
        (leftComponents ((matrixPiCLE ν).symm z)) :=
      hΦ.differentiableAt (hO.mem_nhds hz)
    have h₂ : DifferentiableAt ℂ (fun z => leftComponents ((matrixPiCLE ν).symm z)) z :=
      (hdiff _).comp z (matrixPiCLE ν).symm.differentiableAt
    exact (h₁.comp z h₂).differentiableWithinAt
  refine ⟨hopen, hd.continuousOn, fun a ha j => ?_⟩
  have hline : Continuous fun ζ : ℂ => a + ζ • ComplexCoordinates.stdBasisVector j := by fun_prop
  have hmem : ∀ᶠ ζ in 𝓝 (0 : ℂ), a + ζ • ComplexCoordinates.stdBasisVector j ∈
      (matrixPiCLE ν).symm ⁻¹' (leftComponents ⁻¹' O) :=
    hline.continuousAt.eventually_mem (by simpa using hopen.mem_nhds ha)
  filter_upwards [hmem] with ζ hζ
  have h2 : DifferentiableAt ℂ (fun ζ : ℂ => a + ζ • ComplexCoordinates.stdBasisVector j) ζ := by
    fun_prop
  exact DifferentiableAt.comp (f := fun ζ : ℂ => a + ζ • ComplexCoordinates.stdBasisVector j) ζ
    (hd.differentiableAt (hopen.mem_nhds hζ)) h2
theorem isHolomorphicToCoords_of_germs (hE : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    {D : Set (σ → ComplexMatrix2)} (hD : ComplexMatrix2.IsRelativelyOpen (unimodularPi σ) D)
    {g : (σ → ComplexMatrix2) → ℂ} (hg : HasAnalyticGerms D g)
    (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) :
    IsHolomorphicToCoords β scalarCoords (leftComponents ⁻¹' D)
      fun p => g (leftComponents p) := by
  have hcont : Continuous (leftComponents : (σ ⊕ Empty → ComplexMatrix2) → σ → ComplexMatrix2) :=
    continuous_pi fun _ => continuous_apply _
  have hsc : Continuous (scalarCoords : ℂ → ComplexCoordinates 1) :=
    continuous_pi fun i => by
      simp only [scalarCoords_apply]
      exact continuous_id
  obtain ⟨O₀, hO₀, hDe⟩ := hD
  have hopen : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct σ Empty)
      (leftComponents ⁻¹' D : Set (σ ⊕ Empty → ComplexMatrix2)) := by
    refine ⟨leftComponents ⁻¹' O₀, hO₀.preimage hcont, ?_⟩
    rw [hDe]
    ext q
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun i => by
        rcases i with i | i
        · exact h2 i
        · exact i.elim⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun i => h2 (.inl i)⟩
  refine ⟨hopen, fun p hp => ?_, fun p hp => ?_⟩
  · obtain ⟨G, hG, he⟩ := hg _ hp
    have ht : Tendsto (leftComponents : (σ ⊕ Empty → ComplexMatrix2) → σ → ComplexMatrix2)
        (𝓝[leftComponents ⁻¹' D] p) (𝓝[D] (leftComponents p)) :=
      tendsto_nhdsWithin_iff.2 ⟨hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,
        eventually_mem_nhdsWithin⟩
    have h1 : ContinuousWithinAt (fun q => G (leftComponents q)) (leftComponents ⁻¹' D) p :=
      (ContinuousAt.comp (f := leftComponents) hG.continuousAt
        hcont.continuousAt).continuousWithinAt
    have h2 : ContinuousWithinAt (fun q => g (leftComponents q)) (leftComponents ⁻¹' D) p :=
      h1.congr_of_eventuallyEq (ht.eventually he) (he.self_of_nhdsWithin hp)
    exact hsc.continuousAt.comp_continuousWithinAt h2
  · obtain ⟨G, hG, he⟩ := hg _ hp
    obtain ⟨U₁, hU₁, hxU₁, hfU₁⟩ := mem_nhdsWithin.1 he
    obtain ⟨U₃, hU₃sub, hU₃, hxU₃⟩ := mem_nhds_iff.1 hG.eventually_analyticAt
    have hpD : leftComponents p ∈ O₀ ∩ unimodularPi σ := hDe ▸ hp
    have hN : IsOpen (U₁ ∩ U₃ ∩ O₀) := (hU₁.inter hU₃).inter hO₀
    have hdiff : DifferentiableOn ℂ (fun v => scalarCoords (G v)) (U₁ ∩ U₃ ∩ O₀) :=
      fun y hy => by
        have h1 : DifferentiableAt ℂ G y := (hU₃sub hy.1.2).differentiableAt
        refine (differentiableAt_pi.2 fun i => ?_).differentiableWithinAt
        simp only [scalarCoords_apply]
        exact h1
    have hpp : p ∈ GroupLieProduct σ Empty := fun i => by
      rcases i with i | i
      · exact hpD.2 i
      · exact i.elim
    obtain ⟨O', h0, hO', hhol⟩ := (isHolomorphicToCoords_of_differentiableOn hE hN hdiff β).2.2 p
      ⟨⟨⟨hxU₁, hxU₃⟩, hpD.1⟩, hpp⟩
    have hinD : ∀ A ∈ O', leftComponents (expChartAt p A) ∈ U₁ ∩ D := fun A hA => by
      obtain ⟨h1, h2⟩ := hO' A hA
      refine ⟨h1.1.1, ?_⟩
      rw [hDe]
      exact ⟨h1.2, fun i => h2 (.inl i)⟩
    refine ⟨O', h0, fun A hA => (hinD A hA).2, hhol.1, fun ν => ?_⟩
    refine isHolomorphicIn_congr (hhol.2 ν) fun a ha => ?_
    show scalarCoords (g _) = scalarCoords (G _)
    exact congrArg _ (hfU₁ (hinD _ ha))
end ExpCharts
section OddForms
variable {a : ℝ}
theorem isPositivelyOriented_or_opposite (b : InfiniteLattice.Link a) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.GibbsForms.isPositivelyOriented_or_opposite <;> assumption
theorem not_isPositivelyOriented_opposite (ha : 0 < a) {b : InfiniteLattice.Link a}
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.Link.opposite_not_isPositivelyOriented <;> assumption
theorem extendOddly_of_pos (f : InfiniteLattice.Link a → ComplexMatrix2)
    {b : InfiniteLattice.Link a} (hb : b.IsPositivelyOriented) : extendOddly f b = f b := by apply _root_.YangMills.Construction.Tower.FullSpace.Translations.extendOddly_of_pos <;> assumption
theorem extendOddly_mem (ha : 0 < a) {f : InfiniteLattice.Link a → ComplexMatrix2}
    (h : ∀ b : InfiniteLattice.Link a, b.IsPositivelyOriented → f b ∈ ComplexMatrix2.traceless) :
    extendOddly f ∈ complexEdgeForms a := by apply _root_.YangMills.Construction.Tower.FullSpace.LinearityProof.extendOddly_mem <;> assumption
end OddForms
theorem pauliFamily_mem_traceless (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
theorem conj_mem_traceless (V : ComplexMatrix2) {A : ComplexMatrix2}
    (hA : A ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.conjugateBy V A ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.PeriodicLattice.conjugateBy_mem_traceless <;> assumption
theorem cubeVertices_finite (L : ℕ) {a : ℝ} (a' : ℝ) (y : InfiniteLattice.LatticePoint a) :
    (cubeVertices L a' y : Set (InfiniteLattice.LatticePoint a')).Finite := by apply _root_.YangMills.Construction.Tower.FullSpace.LinearityProof.cubeVertices_finite <;> assumption
theorem inv_inv_of_mem_gauge {X : ComplexMatrix2} (h : X ∈ PeriodicLattice.complexGaugeGroup) :
    X⁻¹⁻¹ = X := by apply _root_.YangMills.SharedProofs.p6288 <;> assumption
theorem inv_mem_gauge {X : ComplexMatrix2} (h : X ∈ PeriodicLattice.complexGaugeGroup) :
    X⁻¹ ∈ PeriodicLattice.complexGaugeGroup := by apply _root_.YangMills.Construction.Averaging.SmallFieldAnalyticity.inv_mem_complexGaugeGroup <;> assumption
section DoubleCube
variable {L k j : ℕ}
theorem meshAt_pos (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ) :
    0 < meshAt L k j := by apply _root_.YangMills.Construction.Tower.BlockPathContourPivotProof.Periodic.meshAt_pos <;> assumption
theorem opposite_mem_doubleCubeLinks {c : Edge L k (j + 1)} {b : Edge L k j}
    (hb : b ∈ doubleCubeLinks L (meshAt L k j) c) :
    b.opposite ∈ doubleCubeLinks L (meshAt L k j) c := ⟨hb.2, hb.1⟩
theorem extendFromPositive_restrictPositive {c : Edge L k (j + 1)} {V : Edge L k j → ComplexMatrix2}
    (hV : IsFieldOn PeriodicLattice.complexGaugeGroup (doubleCubeLinks L (meshAt L k j) c) V)
    {b : Edge L k j} (hb : b ∈ doubleCubeLinks L (meshAt L k j) c) :
    extendFromPositive (doubleCubeLinks L (meshAt L k j) c)
      (restrictPositive (doubleCubeLinks L (meshAt L k j) c) V) b = V b := by apply _root_.YangMills.Construction.Tower.FullSpace.LinearityProof.extendFromPositive_restrictPositive <;> assumption
theorem contourMean_eq_extend (hS : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hQ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) {c : Edge L k (j + 1)}
    (hc : c.IsPositivelyOriented) {y : Vertex L k (j + 1)} (hy : y = c.initial ∨ y = c.terminal)
    {x : Vertex L k j} (hx : x ∈ cubeVertices L (meshAt L k j) y)
    {U U' : Edge L k j → ComplexMatrix2}
    (hU' : U' ∈ nearIdentityPolydisc L k j (polydiscRadius L) c)
    (he : ∀ b ∈ doubleCubeLinks L (meshAt L k j) c, U b = U' b) :
    complexContourMean L U y x =
      complexContourMean L (extendFromPositive (doubleCubeLinks L (meshAt L k j) c)
        (restrictPositive (doubleCubeLinks L (meshAt L k j) c) U')) y x := by apply _root_.YangMills.Construction.Tower.FullSpace.LinearityProof.complexContourMean_eq_extend <;> assumption
theorem expTwist_eqOn {ρ : ℝ} {c : Edge L k (j + 1)} {V B U' : Edge L k j → ComplexMatrix2}
    {z : ℂ} (hU' : U' ∈ nearIdentityPolydisc L k j ρ c)
    (e : restrictPositive (doubleCubeLinks L (meshAt L k j) c) U' =
      expMoved (restrictPositive (doubleCubeLinks L (meshAt L k j) c) V)
        (fun b => B b.1) z) :
    ∀ b ∈ doubleCubeLinks L (meshAt L k j) c, expTwist (z • B) V b = U' b := by apply _root_.YangMills.Construction.Tower.FullSpace.LinearityProof.expTwist_eqOn <;> assumption
def polydiscTuples (r : ℝ) (c : Edge L k (j + 1)) :
    Set (PositiveEdgeOf (doubleCubeLinks L (meshAt L k j) c) → ComplexMatrix2) :=
  restrictPositive (doubleCubeLinks L (meshAt L k j) c) '' nearIdentityPolydisc L k j r c
abbrev extendByOne (c : Edge L k (j + 1))
    (v : PositiveEdgeOf (doubleCubeLinks L (meshAt L k j) c) → ComplexMatrix2) :
    Edge L k j → ComplexMatrix2 :=
  extendFromPositive (doubleCubeLinks L (meshAt L k j) c) v
theorem polydiscTuples_mono {r r' : ℝ} (h : r ≤ r') (c : Edge L k (j + 1)) :
    polydiscTuples r c ⊆ polydiscTuples r' c := by
  rintro _ ⟨U, hU, rfl⟩
  exact ⟨U, ⟨hU.1, fun b hb => (hU.2 b hb).trans_le h⟩, rfl⟩
theorem extendByOne_of_not_mem {c : Edge L k (j + 1)}
    (v : PositiveEdgeOf (doubleCubeLinks L (meshAt L k j) c) → ComplexMatrix2)
    {b : Edge L k j} (hb : b ∉ doubleCubeLinks L (meshAt L k j) c) :
    extendByOne c v b = 1 := by
  unfold extendByOne extendFromPositive
  rw [dif_neg fun h => hb h.1, dif_neg fun h => hb (opposite_mem_doubleCubeLinks h.1)]
theorem extendByOne_pos {c : Edge L k (j + 1)}
    (v : PositiveEdgeOf (doubleCubeLinks L (meshAt L k j) c) → ComplexMatrix2)
    (b : PositiveEdgeOf (doubleCubeLinks L (meshAt L k j) c)) :
    extendByOne c v b.1 = v b := by
  unfold extendByOne extendFromPositive
  rw [dif_pos b.2]
theorem restrictPositive_extendByOne {c : Edge L k (j + 1)}
    (v : PositiveEdgeOf (doubleCubeLinks L (meshAt L k j) c) → ComplexMatrix2) :
    restrictPositive (doubleCubeLinks L (meshAt L k j) c) (extendByOne c v) = v :=
  funext fun b => extendByOne_pos v b
theorem extendByOne_mem_smallComplexFields (hρ : 0 < polydiscRadius L) {r : ℝ}
    (hr : r ≤ polydiscRadius L) {c : Edge L k (j + 1)}
    {v : PositiveEdgeOf (doubleCubeLinks L (meshAt L k j) c) → ComplexMatrix2}
    (hv : v ∈ polydiscTuples r c) : extendByOne c v ∈ smallComplexFields L k j := by
  obtain ⟨U, hU, rfl⟩ := hv
  have hin : ∀ b ∈ doubleCubeLinks L (meshAt L k j) c,
      extendByOne c (restrictPositive (doubleCubeLinks L (meshAt L k j) c) U) b = U b :=
    fun b hb => extendFromPositive_restrictPositive hU.1 hb
  have hrev : ∀ b : Edge L k j, b.opposite ∈ doubleCubeLinks L (meshAt L k j) c →
      b ∈ doubleCubeLinks L (meshAt L k j) c := fun b hb => opposite_mem_doubleCubeLinks hb
  refine ⟨⟨fun b => ?_, fun b => ?_⟩, fun b => ?_⟩
  · by_cases hb : b ∈ doubleCubeLinks L (meshAt L k j) c
    · rw [hin b hb]
      exact hU.1.1 b hb
    · rw [extendByOne_of_not_mem _ hb]
      show Matrix.det (1 : ComplexMatrix2) = 1
      exact Matrix.det_one
  · by_cases hb : b ∈ doubleCubeLinks L (meshAt L k j) c
    · rw [hin b hb, hin _ (opposite_mem_doubleCubeLinks hb)]
      exact hU.1.2 b hb
    · rw [extendByOne_of_not_mem _ hb, extendByOne_of_not_mem _ fun h => hb (hrev b h), inv_one]
  · by_cases hb : b ∈ doubleCubeLinks L (meshAt L k j) c
    · rw [hin b hb]
      exact (hU.2 b hb).trans_le hr
    · rw [extendByOne_of_not_mem _ hb, sub_self]
      simpa using hρ
theorem polydiscTuples_isRelativelyOpen (hL : Conventions.IsAdmissibleBlockingFactor L) (r : ℝ)
    (c : Edge L k (j + 1)) [Fintype (PositiveEdgeOf (doubleCubeLinks L (meshAt L k j) c))] :
    ComplexMatrix2.IsRelativelyOpen
      (unimodularPi (PositiveEdgeOf (doubleCubeLinks L (meshAt L k j) c)))
      (polydiscTuples r c) := by
  have ha := meshAt_pos hL k j
  refine ⟨{v | ∀ b, ComplexMatrix2.operatorNorm (v b - 1) < r ∧
    ComplexMatrix2.operatorNorm (adjugateCLM (v b) - 1) < r}, ?_, ?_⟩
  · simp only [Set.ofPred_forall, Set.ofPred_and]
    refine isOpen_iInter_of_finite fun b => IsOpen.inter ?_ ?_
    · exact isOpen_lt (by fun_prop) continuous_const
    · exact isOpen_lt (by fun_prop) continuous_const
  · ext v
    constructor
    · rintro ⟨U, hU, rfl⟩
      refine ⟨fun b => ⟨hU.2 b.1 b.2.1, ?_⟩, fun b => hU.1.1 _ b.2.1⟩
      show ComplexMatrix2.operatorNorm (adjugateCLM (U b.1) - 1) < r
      rw [← inv_eq_adjugateCLM (hU.1.1 _ b.2.1), ← hU.1.2 _ b.2.1]
      exact hU.2 _ (opposite_mem_doubleCubeLinks b.2.1)
    · rintro ⟨hn, hg⟩
      have hg' : ∀ b, v b ∈ PeriodicLattice.complexGaugeGroup := hg
      have hneg : ∀ b (hb : b ∈ doubleCubeLinks L (meshAt L k j) c)
          (hp : ¬ b.IsPositivelyOriented),
          extendByOne c v b = (v ⟨b.opposite, opposite_mem_doubleCubeLinks hb,
            (isPositivelyOriented_or_opposite b).resolve_left hp⟩)⁻¹ := by
        intro b hb hp
        unfold extendByOne extendFromPositive
        rw [dif_neg fun h => hp h.2, dif_pos]
      have hgroup : ∀ b ∈ doubleCubeLinks L (meshAt L k j) c,
          extendByOne c v b ∈ PeriodicLattice.complexGaugeGroup := by
        intro b hb
        by_cases hp : b.IsPositivelyOriented
        · rw [extendByOne_pos v ⟨b, hb, hp⟩]
          exact hg' _
        · rw [hneg b hb hp]
          exact inv_mem_gauge (hg' _)
      have hnorm : ∀ b ∈ doubleCubeLinks L (meshAt L k j) c,
          ComplexMatrix2.operatorNorm (extendByOne c v b - 1) < r := by
        intro b hb
        by_cases hp : b.IsPositivelyOriented
        · rw [extendByOne_pos v ⟨b, hb, hp⟩]
          exact (hn ⟨b, hb, hp⟩).1
        · rw [hneg b hb hp, inv_eq_adjugateCLM (hg' _)]
          exact (hn _).2
      refine ⟨extendByOne c v, ⟨⟨hgroup, fun b hb => ?_⟩, hnorm⟩, restrictPositive_extendByOne v⟩
      by_cases hp : b.IsPositivelyOriented
      · have hp' : ¬ b.opposite.IsPositivelyOriented := not_isPositivelyOriented_opposite ha hp
        rw [hneg _ (opposite_mem_doubleCubeLinks hb) hp', extendByOne_pos v ⟨b, hb, hp⟩]
        rfl
      · rw [hneg b hb hp, extendByOne_pos v ⟨b.opposite, opposite_mem_doubleCubeLinks hb,
          (isPositivelyOriented_or_opposite b).resolve_left hp⟩, inv_inv_of_mem_gauge (hg' _)]
end DoubleCube
section TupleFormulas
variable {L k j : ℕ}
def meanOfTuple (c : Edge L k (j + 1))
    (v : PositiveEdgeOf (doubleCubeLinks L (meshAt L k j) c) → ComplexMatrix2) : ComplexMatrix2 :=
  complexSmoothing L (extendByOne c v) c
def contourOfTuple (c : Edge L k (j + 1)) (y : Vertex L k (j + 1)) (x : Vertex L k j)
    (v : PositiveEdgeOf (doubleCubeLinks L (meshAt L k j) c) → ComplexMatrix2) : ComplexMatrix2 :=
  complexContourMean L (extendByOne c v) y x
def driftOfTuple (c : Edge L k (j + 1)) (y : Vertex L k (j + 1))
    (B : Edge L k j → ComplexMatrix2)
    (v : PositiveEdgeOf (doubleCubeLinks L (meshAt L k j) c) → ComplexMatrix2) : ComplexMatrix2 :=
  PeriodicLattice.inverseFourthPowerWeight L • ∑ᶠ x ∈ cubeVertices L (meshAt L k j) y,
    logDerivAlong (contourOfTuple c y x) (fun b => B b.1) v
def kernelOfTuple (c : Edge L k (j + 1)) (B : Edge L k j → ComplexMatrix2)
    (v : PositiveEdgeOf (doubleCubeLinks L (meshAt L k j) c) → ComplexMatrix2) : ComplexMatrix2 :=
  logDerivAlong (meanOfTuple c) (fun b => B b.1) v +
    (ComplexMatrix2.conjugateBy (meanOfTuple c v) (driftOfTuple c c.terminal B v) -
      driftOfTuple c c.initial B v)
theorem germs_of_isHolomorphicBetween {σ : Type} [inst : Fintype σ]
    {D : Set (σ → ComplexMatrix2)} {Φ : (σ → ComplexMatrix2) → ComplexMatrix2}
    (h : ∃ _ : Fintype σ, ComplexMatrix2.IsHolomorphicBetween
      (fun _ : σ => ComplexMatrix2.FactorKind.group)
      (fun _ : Unit => ComplexMatrix2.FactorKind.group) D fun v _ => Φ v) :
    ComplexMatrix2.IsRelativelyOpen (unimodularPi σ) D ∧
      MapsTo Φ D PeriodicLattice.complexGaugeGroup ∧ HasAnalyticGerms D Φ := by
  obtain ⟨i, hh⟩ := h
  obtain rfl : i = inst := Subsingleton.elim _ _
  refine ⟨hh.1, fun v hv => hh.2.1 hv (), fun x hx => ?_⟩
  obtain ⟨F, hFa, hFe⟩ := hh.2.2 x hx
  refine ⟨fun v => F v (),
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Unit => ComplexMatrix2) ()).analyticAt
      _).comp hFa, ?_⟩
  filter_upwards [hFe] with y hy
  exact congrFun hy ()
theorem isTangentDirection_restrict (hA : LeftChartFields.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) {V : Edge L k j → ComplexMatrix2}
    (hV : V ∈ smallComplexFields L k j) {B : Edge L k j → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms (meshAt L k j)) (c : Edge L k (j + 1)) :
    IsTangentDirection
      (fun b : PositiveEdgeOf (doubleCubeLinks L (meshAt L k j) c) => B b.1)
      (restrictPositive (doubleCubeLinks L (meshAt L k j) c) V) := by
  have hLeft := ((hA.2.2 L k j hL hj.le).2.1.1).2
  exact ⟨fun z b => (hLeft V hV.1 B hB ⟨b.1, b.2.2⟩).1 z,
    fun b => (hLeft V hV.1 B hB ⟨b.1, b.2.2⟩).2⟩
theorem smoothingMap_eq_meanOfTuple (hW : MeanStableFields.MeanStableFieldsHold)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) {V : Edge L k j → ComplexMatrix2}
    (hV : V ∈ smallComplexFields L k j) {c : Edge L k (j + 1)} (hc : c.IsPositivelyOriented) :
    smoothingMap L k j V c = meanOfTuple c
      (restrictPositive (doubleCubeLinks L (meshAt L k j) c) V) := by
  have hWhole := (hW L hL k (by omega)).2
  have hsmall : V ∈ MeanStableFields.Infinite.fieldsNearOne L k j := hV
  obtain ⟨F₂, hF₂, hpw⟩ := hWhole.polydisc_presentation j hj c hc
  have hw₂ := hpw V hsmall
  exact hw₂.2.2.2 V hsmall hw₂.2.2.1
theorem complexSmoothingDeriv_eq (hO : UniqueValue.PresentationsAgreeAndBallsOpen)
    (hW : MeanStableFields.MeanStableFieldsHold)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) {V : Edge L k j → ComplexMatrix2}
    (hV : V ∈ smallComplexFields L k j) {c : Edge L k (j + 1)}
    (hc : c.IsPositivelyOriented) {B : Edge L k j → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms (meshAt L k j)) :
    complexSmoothingDeriv V B c = logDerivAlong (meanOfTuple c) (fun b => B b.1)
      (restrictPositive (doubleCubeLinks L (meshAt L k j) c) V) := by
  have hWhole := (hW L hL k (by omega)).2
  have hsmall : V ∈ MeanStableFields.Infinite.fieldsNearOne L k j := hV
  obtain ⟨F₂, hF₂, hpw⟩ := hWhole.polydisc_presentation j hj c hc
  have hw₂ := hpw V hsmall
  obtain ⟨F₁, O₁, f₁, hw₁, hk₁⟩ :=
    (hWhole.holomorphic_smoothing j hj c hc OneLoop.pauliBasis).2 V hsmall
  have hex : ∃ w : LocalData L k j ComplexMatrix2,
      IsLocalPresentation PeriodicLattice.complexGaugeGroup (smallComplexFields L k j)
        (fun U' => smoothingMap L k j U' c) V w.support w.region w.fn ∧
      holomorphicPresentations L k j OneLoop.pauliBasis ComplexCoordinates.matrixEquiv
        w.support w.region w.fn := ⟨⟨F₁, O₁, f₁⟩, hw₁, hk₁⟩
  have spec := Classical.epsilon_spec hex
  have hone := (hO L k j hL.1 hL.2 hj.le).1.2.2.2
  have hV0 := smoothingMap_eq_meanOfTuple hW hL hj hV hc
  obtain ⟨ε, hε, h⟩ := hone (smallComplexFields L k j) (hWhole.isFinitelyOpen_nearOne j hj)
    (fun U' => smoothingMap L k j U' c) V hsmall _ _ _ F₂ _ _ spec.1 hw₂ B 0
    (fun b hb => hB.1 b hb) (fun _ _ => ComplexMatrix2.traceless.zero_mem)
  have e : complexSmoothingDeriv V B c = logDirectionalDeriv ℂ
      (valueViaPresentation PeriodicLattice.complexGaugeGroup (smallComplexFields L k j)
        (holomorphicPresentations L k j OneLoop.pauliBasis ComplexCoordinates.matrixEquiv)
        (fun U' => smoothingMap L k j U' c) V) (smoothingMap L k j V c) B := by
    unfold complexSmoothingDeriv holLeftDifferential extendOddly
    exact if_pos hc
  rw [e, hV0]
  unfold logDirectionalDeriv logDerivAlong
  refine congrArg (fun w => Complex.I⁻¹ • w) (Filter.EventuallyEq.deriv_eq ?_)
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hε] with t ht
  have ht' : ‖t‖ < ε := by simpa using ht
  have h3 := (h t 0 ht' (by simpa using hε)).2.2
  have m1 : ∀ F : Finset (Edge L k j),
      UniqueValue.perturbedTuple F B 0 V (algebraMap ℂ ℂ t) (algebraMap ℂ ℂ 0) =
        fun b : F => ComplexMatrix2.matExp (Complex.I • (t • B) b.1) * V b.1 := by
    intro F
    funext b
    simp [UniqueValue.perturbedTuple]
  rw [m1, m1] at h3
  have m2 : MeanStableFields.Infinite.smoothingOnFinset c F₂ hF₂
      (fun b : F₂ => ComplexMatrix2.matExp (Complex.I • (t • B) b.1) * V b.1) =
      meanOfTuple c
        (expMoved (restrictPositive (doubleCubeLinks L (meshAt L k j) c) V)
          (fun b => B b.1) t) := rfl
  show ComplexMatrix2.logSeries ((chosenPresentation PeriodicLattice.complexGaugeGroup
    (smallComplexFields L k j)
    (holomorphicPresentations L k j OneLoop.pauliBasis ComplexCoordinates.matrixEquiv)
    (fun U' => smoothingMap L k j U' c) V).fn
      (fun b => ComplexMatrix2.matExp (Complex.I • (t • B) b.1) * V b.1) * _) = _
  exact congrArg (fun Y => ComplexMatrix2.logSeries (Y * _)) (h3.trans m2)
theorem logDeriv_contourMean_eq (hS : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hQ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hA : LeftChartFields.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) {V : Edge L k j → ComplexMatrix2}
    (hV : V ∈ smallComplexFields L k j) {c : Edge L k (j + 1)}
    (hc : c.IsPositivelyOriented) {y : Vertex L k (j + 1)}
    (hy : y ∈ ({c.initial, c.terminal} : Set (Vertex L k (j + 1))))
    {x : Vertex L k j} (hx : x ∈ cubeVertices L (meshAt L k j) y)
    {B : Edge L k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms (meshAt L k j)) :
    logDirectionalDeriv ℂ (fun X => complexContourMean L (expTwist X V) y x)
        (complexContourMean L V y x) B =
      logDerivAlong (contourOfTuple c y x) (fun b => B b.1)
        (restrictPositive (doubleCubeLinks L (meshAt L k j) c) V) := by
  have hserve := (hS.1 L hL).2.2.fullSpace k j hj c hc
  have hy' : y = c.initial ∨ y = c.terminal := hy
  obtain ⟨inst, hhol⟩ := (hserve.holomorphic_contourMean y hy x hx).1
  have hVp : V ∈ nearIdentityPolydisc L k j (polydiscRadius L) c :=
    ⟨⟨fun b _ => hV.1.1 b, fun b _ => hV.1.2 b⟩, fun b _ => hV.2 b⟩
  have hW := contourMean_eq_extend hS hQ hL hj hc hy' hx hVp fun _ _ => rfl
  have hnear := eventually_expMoved_mem hhol.1 ⟨V, hVp, rfl⟩
    (isTangentDirection_restrict hA hL hj hV hB c)
  unfold logDirectionalDeriv logDerivAlong
  refine congrArg (fun w => Complex.I⁻¹ • w) (Filter.EventuallyEq.deriv_eq ?_)
  filter_upwards [hnear] with z hz
  obtain ⟨U', hU', e⟩ := hz
  have e1 := contourMean_eq_extend hS hQ hL hj hc hy' hx hU' (expTwist_eqOn hU' e)
  rw [e] at e1
  show ComplexMatrix2.logSeries (complexContourMean L (expTwist (z • B) V) y x * _) = _
  rw [e1, hW]
  rfl
theorem covariantSmoothingDeriv_eq (hS : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hQ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hO : UniqueValue.PresentationsAgreeAndBallsOpen)
    (hW : MeanStableFields.MeanStableFieldsHold)
    (hA : LeftChartFields.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) {V : Edge L k j → ComplexMatrix2}
    (hV : V ∈ smallComplexFields L k j) {c : Edge L k (j + 1)}
    (hc : c.IsPositivelyOriented) {B : Edge L k j → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms (meshAt L k j)) :
    covariantSmoothingDeriv V B c = kernelOfTuple c B
      (restrictPositive (doubleCubeLinks L (meshAt L k j) c) V) := by
  have hd : ∀ y ∈ ({c.initial, c.terminal} : Set (Vertex L k (j + 1))),
      contourLogDrift V B y = driftOfTuple c y B
        (restrictPositive (doubleCubeLinks L (meshAt L k j) c) V) := fun y hy => by
    unfold contourLogDrift driftOfTuple
    exact congrArg _ (finsum_mem_congr rfl fun x hx =>
      logDeriv_contourMean_eq hS hQ hA hL hj hV hc hy hx hB)
  have hD : covDiff (smoothingMap L k j V) (contourLogDrift V B) c =
      ComplexMatrix2.conjugateBy (smoothingMap L k j V c) (contourLogDrift V B c.terminal) -
        contourLogDrift V B c.initial :=
    extendOddly_of_pos _ hc
  show complexSmoothingDeriv V B c +
    covDiff (smoothingMap L k j V) (contourLogDrift V B) c = _
  rw [complexSmoothingDeriv_eq hO hW hL hj hV hc hB, hD, smoothingMap_eq_meanOfTuple hW hL hj hV hc,
    hd _ (Or.inr rfl), hd _ (Or.inl rfl)]
  rfl
theorem covariantSmoothingDeriv_mem_traceless (hLin : CovariantStepComplexLinear)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) {V : Edge L k j → ComplexMatrix2}
    (hV : V ∈ smallComplexFields L k j) {c : Edge L k (j + 1)}
    (hc : c.IsPositivelyOriented) {B : Edge L k j → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms (meshAt L k j)) :
    covariantSmoothingDeriv V B c ∈ ComplexMatrix2.traceless := by
  obtain ⟨h1, -, -, -⟩ := hLin L hL k j hj V hV
  have ht := h1 B hB
  have hD : covDiff (smoothingMap L k j V) (contourLogDrift V B) c =
      ComplexMatrix2.conjugateBy (smoothingMap L k j V c) (contourLogDrift V B c.terminal) -
        contourLogDrift V B c.initial :=
    extendOddly_of_pos _ hc
  show complexSmoothingDeriv V B c +
    covDiff (smoothingMap L k j V) (contourLogDrift V B) c ∈ _
  rw [hD]
  exact ComplexMatrix2.traceless.add_mem (ht.1.1 c hc)
    (ComplexMatrix2.traceless.sub_mem (conj_mem_traceless _ (ht.2 _)) (ht.2 _))
theorem basisForm_mem (hL : Conventions.IsAdmissibleBlockingFactor L) (a : Fin 3)
    (b : PositiveEdge (meshAt L k j)) :
    basisForm a b ∈ complexEdgeForms (meshAt L k j) := by
  classical
  unfold basisForm
  refine extendOddly_mem (meshAt_pos hL k j) fun b' _ => ?_
  split_ifs
  · exact pauliFamily_mem_traceless a
  · exact ComplexMatrix2.traceless.zero_mem
end TupleFormulas
section PolydiscGerms
variable {L k j : ℕ} {c : Edge L k (j + 1)}
  [Fintype (PositiveEdgeOf (doubleCubeLinks L (meshAt L k j) c))]
omit [Fintype (PositiveEdgeOf (doubleCubeLinks L (meshAt L k j) c))] in
theorem isTangentDirection_on_polydisc (hS : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hA : LeftChartFields.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) {B : Edge L k j → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms (meshAt L k j)) :
    ∀ v ∈ polydiscTuples (polydiscRadius L) c,
      IsTangentDirection
        (fun b : PositiveEdgeOf (doubleCubeLinks L (meshAt L k j) c) => B b.1) v :=
  fun v hv => by
  have hs := extendByOne_mem_smallComplexFields (hS.1 L hL).2.2.pos le_rfl hv
  have h := isTangentDirection_restrict hA hL hj hs hB c
  rwa [restrictPositive_extendByOne] at h
theorem meanOfTuple_germs (hS : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) (hc : c.IsPositivelyOriented) :
    MapsTo (meanOfTuple c) (polydiscTuples (polydiscRadius L) c)
        PeriodicLattice.complexGaugeGroup ∧
      HasAnalyticGerms (polydiscTuples (polydiscRadius L) c) (meanOfTuple c) :=
  (germs_of_isHolomorphicBetween (Φ := meanOfTuple c)
    ((hS.1 L hL).2.2.fullSpace k j hj c hc).holomorphic_smoothing.1).2
theorem contourOfTuple_germs (hS : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) (hc : c.IsPositivelyOriented)
    {y : Vertex L k (j + 1)} (hy : y ∈ ({c.initial, c.terminal} : Set (Vertex L k (j + 1))))
    {x : Vertex L k j} (hx : x ∈ cubeVertices L (meshAt L k j) y) :
    MapsTo (contourOfTuple c y x) (polydiscTuples (polydiscRadius L) c)
        PeriodicLattice.complexGaugeGroup ∧
      HasAnalyticGerms (polydiscTuples (polydiscRadius L) c) (contourOfTuple c y x) :=
  (germs_of_isHolomorphicBetween (Φ := contourOfTuple c y x)
    (((hS.1 L hL).2.2.fullSpace k j hj c hc).holomorphic_contourMean y hy x hx).1).2
theorem driftOfTuple_germs (hS : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hA : LeftChartFields.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) (hc : c.IsPositivelyOriented)
    {y : Vertex L k (j + 1)} (hy : y ∈ ({c.initial, c.terminal} : Set (Vertex L k (j + 1))))
    {B : Edge L k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms (meshAt L k j)) :
    HasAnalyticGerms (polydiscTuples (polydiscRadius L) c) (driftOfTuple c y B) := by
  have hfin := cubeVertices_finite L (meshAt L k j) y
  have hs : HasAnalyticGerms (polydiscTuples (polydiscRadius L) c) fun v =>
      ∑ x ∈ hfin.toFinset, logDerivAlong (contourOfTuple c y x) (fun b => B b.1) v :=
    HasAnalyticGerms.sum _ fun x hx => by
      have hx' := hfin.mem_toFinset.1 hx
      exact HasAnalyticGerms.logDeriv (fun ρ hρ => hA.2.1 ρ hρ)
        (polydiscTuples_isRelativelyOpen hL _ c)
        (contourOfTuple_germs hS hL hj hc hy hx').2 (contourOfTuple_germs hS hL hj hc hy hx').1
        (isTangentDirection_on_polydisc hS hA hL hj hB)
  refine (hs.smul (PeriodicLattice.inverseFourthPowerWeight L)).congr fun v _ => ?_
  unfold driftOfTuple
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
theorem kernelOfTuple_germs (hS : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hA : LeftChartFields.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) (hc : c.IsPositivelyOriented)
    {B : Edge L k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms (meshAt L k j)) :
    HasAnalyticGerms (polydiscTuples (polydiscRadius L) c) (kernelOfTuple c B) := by
  obtain ⟨hm, hg⟩ := meanOfTuple_germs hS hL hj hc
  have hd := HasAnalyticGerms.logDeriv (fun ρ hρ => hA.2.1 ρ hρ)
    (polydiscTuples_isRelativelyOpen hL _ c) hg hm
    (isTangentDirection_on_polydisc hS hA hL hj hB)
  have hh := driftOfTuple_germs hS hA hL hj hc (y := c.terminal) (Or.inr rfl) hB
  have ht := driftOfTuple_germs hS hA hL hj hc (y := c.initial) (Or.inl rfl) hB
  exact hd.add (((hg.mul hh).mul (hg.inv hm)).sub ht)
end PolydiscGerms
section Conditions
open DoubleBlockPolydisc.Infinite (polydiscPositive)
variable {L k j : ℕ}
theorem polydiscPositive_eq (r : ℝ) (c : Edge L k (j + 1)) :
    polydiscPositive L k j r c = polydiscTuples r c :=
  image_image _ _ _
theorem kernelHolomorphyAt_of_pos (hS : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hQ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hO : UniqueValue.PresentationsAgreeAndBallsOpen)
    (hW : MeanStableFields.MeanStableFieldsHold)
    (hA : LeftChartFields.Claim)
    (hLin : CovariantStepComplexLinear)
    (hE : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) {c : Edge L k (j + 1)}
    (hc : c.IsPositivelyOriented) : KernelHolomorphyAt L k j c := by
  have hρ := (hS.1 L hL).2.2.pos
  have hr : 3 / 4 * polydiscRadius L ≤ polydiscRadius L := by linarith
  obtain ⟨inst, -⟩ := ((hS.1 L hL).2.2.fullSpace k j hj c hc).holomorphic_smoothing.1
  have hsmall : ∀ {V : Edge L k j → ComplexMatrix2}, V ∈ smallComplexFields L k j →
      V ∈ nearIdentityPolydisc L k j (polydiscRadius L) c := fun hV =>
    ⟨⟨fun b _ => hV.1.1 b, fun b _ => hV.1.2 b⟩, fun b _ => hV.2 b⟩
  refine ⟨?_, fun b _ a a' => ?_, fun b _ a a' => ?_, fun y hy x hx a a' => ?_,
    fun y hy x hx a a' => ?_⟩
  · rw [polydiscPositive_eq]
    exact polydiscTuples_isRelativelyOpen hL _ c
  · have hB := basisForm_mem (k := k) (j := j) hL a b
    have hg : HasAnalyticGerms (polydiscTuples (polydiscRadius L) c)
        fun v => kernelCoeff (extendByOne c v) c b a a' :=
      ((kernelOfTuple_germs hS hA hL hj hc hB).clm (pauliCoeffCLM a')).congr fun v hv => by
        have hs := extendByOne_mem_smallComplexFields hρ le_rfl hv
        have h1 := covariantSmoothingDeriv_eq hS hQ hO hW hA hL hj hs hc hB
        rw [restrictPositive_extendByOne] at h1
        unfold kernelCoeff
        rw [pauliCoeff_eq_pauliCoeffCLM a'
          (covariantSmoothingDeriv_mem_traceless hLin hL hj hs hc hB), h1]
    refine ⟨inst, fun β => ?_⟩
    rw [polydiscPositive_eq]
    exact isHolomorphicToCoords_of_germs hE (polydiscTuples_isRelativelyOpen hL _ c)
      (hg.mono (polydiscTuples_mono hr c)) β
  · have hB := basisForm_mem (k := k) (j := j) hL a b
    intro V hV hVr
    have hs := extendByOne_mem_smallComplexFields hρ hr
      (show restrictPositive (doubleCubeLinks L (meshAt L k j) c) V ∈
        polydiscTuples (3 / 4 * polydiscRadius L) c from ⟨V, hVr, rfl⟩)
    have h1 := covariantSmoothingDeriv_eq hS hQ hO hW hA hL hj hV hc hB
    have h2 := covariantSmoothingDeriv_eq hS hQ hO hW hA hL hj hs hc hB
    rw [restrictPositive_extendByOne] at h2
    show Tower.pauliCoeff a' (covariantSmoothingDeriv V (basisForm a b) c) =
      Tower.pauliCoeff a' (covariantSmoothingDeriv (extendByOne c
        (restrictPositive (doubleCubeLinks L (meshAt L k j) c) V))
        (basisForm a b) c)
    rw [h1, h2]
  · obtain ⟨hm, hg⟩ := contourOfTuple_germs hS hL hj hc hy hx
    have hg' : HasAnalyticGerms (polydiscTuples (polydiscRadius L) c)
        fun v => contourConjCoeff (extendByOne c v) y x a a' :=
      (((hg.mul (HasAnalyticGerms.const (ComplexMatrix2.pauliFamily a))).mul (hg.inv hm)).clm
        (pauliCoeffCLM a')).congr fun v hv => by
        unfold contourConjCoeff
        exact pauliCoeff_eq_pauliCoeffCLM a' (conj_mem_traceless _ (pauliFamily_mem_traceless a))
    refine ⟨inst, fun β => ?_⟩
    rw [polydiscPositive_eq]
    exact isHolomorphicToCoords_of_germs hE (polydiscTuples_isRelativelyOpen hL _ c)
      (hg'.mono (polydiscTuples_mono hr c)) β
  · intro V hV _
    have e := contourMean_eq_extend hS hQ hL hj hc hy hx (hsmall hV) fun _ _ => rfl
    show Tower.pauliCoeff a'
        (ComplexMatrix2.conjugateBy (complexContourMean L V y x) (ComplexMatrix2.pauliFamily a)) =
      Tower.pauliCoeff a' (ComplexMatrix2.conjugateBy (complexContourMean L (extendByOne c
        (restrictPositive (doubleCubeLinks L (meshAt L k j) c) V)) y x)
        (ComplexMatrix2.pauliFamily a))
    rw [← e]
end Conditions
theorem kernelsHolomorphic (hS : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hQ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hO : UniqueValue.PresentationsAgreeAndBallsOpen)
    (hW : MeanStableFields.MeanStableFieldsHold)
    (hA : LeftChartFields.Claim)
    (hLin : CovariantStepComplexLinear)
    (hE : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory) : KernelsHolomorphic :=
  fun _ hL _ _ hj _ hc => kernelHolomorphyAt_of_pos hS hQ hO hW hA hLin hE hL hj hc
end YangMills.Construction.Tower.FullSpace.StepKernelHolomorphy
end
