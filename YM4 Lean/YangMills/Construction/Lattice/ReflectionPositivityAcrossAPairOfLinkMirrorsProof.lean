import YangMills.Construction.Lattice.ActionAcrossALinkMirrorOfAGridDatum
import YangMills.Construction.Lattice.ContinuityOfTheActionOfAnIsometryOfAGridDatum
import YangMills.Construction.Lattice.CoordinatesAcrossALinkMirrorOfAGridDatum
import YangMills.Construction.Lattice.LayersOfALinkMirrorOfAGridDatum
import YangMills.Construction.Lattice.ReflectionPositivityAcrossAPairOfLinkMirrors
import YangMills.Construction.Matrices.FunctionsAndOperatorsOfSeveralVariablesOnG
import YangMills.Construction.Matrices.PositivityOfAnIntegralOverTwoSidesAndGaugeVariables
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction
open BoxTorus
namespace MirrorPositivity
open GridMirror TorusDescent
variable {L : ℕ} {κ : ℤ}
theorem edgeVariable_forward {d : CellGrid L κ} (U : d.GaugeConfig) (b : d.ForwardEdge) :
    edgeVariable U b.1 = U b := by
  rw [edgeVariable, dif_pos b.2]
theorem gibbsMean_eq_integral (d : CellGrid L κ) (β : ℝ)
    (hc : Continuous fun U : d.GaugeConfig => Real.exp (-β * d.wilsonAction U))
    (hZ : 0 < d.normalizingIntegral β) (Φ : d.GaugeConfig → ℂ) :
    d.gibbsMean β Φ = (((d.normalizingIntegral β)⁻¹ : ℝ) : ℂ) *
      ∫ U, Φ U * (Real.exp (-β * d.wilsonAction U) : ℂ) ∂haarConfigMeasure L κ d.sideLengths := by
  have hm : Measurable fun U : d.GaugeConfig => ENNReal.ofReal (d.boltzmannFactor β U) :=
    ENNReal.measurable_ofReal.comp hc.measurable
  rw [CellGrid.gibbsMean, CellGrid.gibbsMeasure, integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul hm
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    ENNReal.toReal_inv, ENNReal.toReal_ofReal hZ.le, Complex.real_smul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  have hw : 0 ≤ d.boltzmannFactor β U := (Real.exp_pos _).le
  show (ENNReal.ofReal (d.boltzmannFactor β U)).toReal • Φ U = _
  rw [ENNReal.toReal_ofReal hw, Complex.real_smul, mul_comm]
  rfl
theorem positive_on_posHalf (hLay : MirrorLayers.LayeringTheorem)
    (hCo : GridMirror.MirrorCoordinates)
    (hAc : GridMirror.ActionSplitsAcrossMirror)
    (hPos : Matrices.TwoSidedGaugePositivity.PositivityStatement)
    (hLat : GridLattice.Properties)
    (hPull : GridSymmetries.PullbackContinuity)
    {d : CellGrid L κ} {β : ℝ} (hβ : 0 < β) (θ : d.Space → d.Space) (μ : Fin 4) (c : ℝ)
    (hg : IsMirrorReflection (d.symmetryOfMap θ) μ c) {F F' : d.GaugeConfig → ℂ}
    (hF : IsBoundedBorelOfEdges
      {b : d.DirectedEdge | b.LiesIn (posHalf d μ c)} F)
    (hF' : IsBoundedBorelOfEdges
      {b : d.DirectedEdge | b.LiesIn (posHalf d μ c)} F') :
    0 ≤ reflectedPairing d β θ F F ∧
      ‖reflectedPairing d β θ F' F‖ ^ 2 ≤
        (reflectedPairing d β θ F' F').re * (reflectedPairing d β θ F F).re := by
  classical
  set g := d.symmetryOfMap θ with hgdef
  obtain ⟨h, -, layer, hl⟩ := hLay L κ d g μ c hg
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hup, -⟩ := hl
  obtain ⟨ι, hιm, hιmap, hι⟩ := hCo L κ d g μ c hg
  obtain ⟨hAcont, hA0, hAreads, hAsum⟩ := hAc L κ d g μ c hg
  obtain ⟨-, -, -, -, hDens⟩ := hLat L κ d
  obtain ⟨-, hDens⟩ := hDens
  obtain ⟨hexp, -, -, hZ⟩ := hDens β hβ
  have hZ' : 0 < d.normalizingIntegral β := hZ
  have hres : ∀ G : d.GaugeConfig → ℂ, IsBoundedBorelOfEdges
      {b : d.DirectedEdge | b.LiesIn (posHalf d μ c)} G →
      ∃ f : (HalfEdge d (posHalf d μ c) → Conventions.StandingParameters.gaugeGroup) → ℂ,
        Measurable f ∧ (∃ C : ℝ, ∀ W, ‖f W‖ ≤ C) ∧
          ∀ U : d.GaugeConfig, G U = f fun b => U b.1 := by
    rintro G ⟨f₀, hm, ⟨C, hC⟩, hU⟩
    have hp : ∀ b : ↥(forwardPart
        {b : d.DirectedEdge | b.LiesIn (posHalf d μ c)}),
        b.1.1.LiesIn (posHalf d μ c) := by
      rintro ⟨b, hb | hb⟩
      · exact hb
      · have := (hup b.1.flip).1 hb
        exact (hup b.1).2 ⟨this.2, this.1⟩
    exact ⟨fun W => f₀ fun b => W ⟨b.1, hp b⟩,
      hm.comp (measurable_pi_lambda _ fun b => measurable_pi_apply _), ⟨C, fun W => hC _⟩,
      fun U => hU U⟩
  obtain ⟨f, hfm, hfb, hfU⟩ := hres F hF
  obtain ⟨f', hfm', hfb', hfU'⟩ := hres F' hF'
  letI : Fintype (HalfEdge d (posHalf d μ c)) := Fintype.ofFinite _
  letI : Fintype (MirrorPairedPoint g (posHalf d μ c)) := Fintype.ofFinite _
  letI : Fintype (TransverseEdge g (posHalf d μ c) μ) := Fintype.ofFinite _
  let A : (HalfEdge d (posHalf d μ c) → Conventions.StandingParameters.gaugeGroup) → ℝ :=
    fun W => halfAction d (posHalf d μ c) (ι (W, 1, 1))
  have hAm : Measurable A :=
    hAcont.measurable.comp (hιm.comp (measurable_id.prodMk measurable_const))
  have hagree : ∀ x (b : HalfEdge d (posHalf d μ c)), ι x b.1 = x.1 b := fun x b => by
    exact (edgeVariable_forward (ι x) b.1).symm.trans ((hι x).1 b)
  have hS₁ : ∀ x, halfAction d (posHalf d μ c) (ι x) = A x.1 := fun x =>
    hAreads _ _ fun b => by rw [hagree, hagree]
  have hpull : ∀ x (b : HalfEdge d (posHalf d μ c)),
      g.pullback (ι x) b.1 = x.2.1 b := fun x b => (hι x).2.1 b
  have hS₂ : ∀ x, halfAction d (posHalf d μ c) (g.pullback (ι x)) = A x.2.1 := fun x =>
    hAreads _ _ fun b => by rw [hpull, hagree]
  have haction : ∀ x, d.wilsonAction (ι x) =
      Matrices.TwoSidedGaugePositivity.gaugeExponent
        (fun e : TransverseEdge g (posHalf d μ c) μ => e.1) (fun e => e.start)
        (fun e => e.finish) A x := by
    intro x
    rw [hAsum, hS₁, hS₂, finsum_eq_sum_of_fintype,
      Matrices.TwoSidedGaugePositivity.gaugeExponent]
    refine congrArg (fun t => A x.1 + A x.2.1 + t) (Finset.sum_congr rfl fun e _ => ?_)
    rw [mirrorFaceEnergy, mirrorHolonomy, (hι x).1 e.1, (hι x).2.2, (hι x).2.1, (hι x).2.2]
  have hform : ∀ (G₁ G₂ : d.GaugeConfig → ℂ)
      (f₁ f₂ : (HalfEdge d (posHalf d μ c) → Conventions.StandingParameters.gaugeGroup) → ℂ),
      Measurable f₁ → Measurable f₂ → (∀ U : d.GaugeConfig, G₁ U = f₁ fun b => U b.1) →
      (∀ U : d.GaugeConfig, G₂ U = f₂ fun b => U b.1) →
      reflectedPairing d β θ G₂ G₁ = (((d.normalizingIntegral β)⁻¹ : ℝ) : ℂ) *
        Matrices.TwoSidedGaugePositivity.gaugeForm
          (fun e : TransverseEdge g (posHalf d μ c) μ => e.1) (fun e => e.start)
          (fun e => e.finish) A β f₂ f₁ := by
    intro G₁ G₂ f₁ f₂ hm₁ hm₂ h₁ h₂
    have hrestrict : Measurable fun U : d.GaugeConfig =>
        fun b : HalfEdge d (posHalf d μ c) => U b.1 :=
      measurable_pi_lambda _ fun b => measurable_pi_apply _
    have hG₁ : Measurable G₁ := by
      have : G₁ = f₁ ∘ fun U : d.GaugeConfig =>
          fun b : HalfEdge d (posHalf d μ c) => U b.1 := funext h₁
      rw [this]
      exact hm₁.comp hrestrict
    have hG₂ : Measurable G₂ := by
      have : G₂ = f₂ ∘ fun U : d.GaugeConfig =>
          fun b : HalfEdge d (posHalf d μ c) => U b.1 := funext h₂
      rw [this]
      exact hm₂.comp hrestrict
    have hpullc : Measurable g.pullback := (hPull L κ d g).1.measurable
    have hΨ : Measurable fun U : d.GaugeConfig =>
        starRingEnd ℂ (g.actOnObservables G₂ U) * G₁ U *
          (Real.exp (-β * d.wilsonAction U) : ℂ) := by
      have h₃ : Measurable fun U : d.GaugeConfig => g.actOnObservables G₂ U := hG₂.comp hpullc
      exact ((Complex.continuous_conj.measurable.comp h₃).mul hG₁).mul
        (Complex.measurable_ofReal.comp hexp.measurable)
    rw [reflectedPairing, gibbsMean_eq_integral d β hexp hZ']
    congr 1
    rw [Matrices.TwoSidedGaugePositivity.gaugeForm, ← hιmap,
      integral_map hιm.aemeasurable hΨ.aestronglyMeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have e₁ : G₁ (ι x) = f₁ x.1 := by
      rw [h₁]
      exact congrArg f₁ (funext fun b => hagree x b)
    have e₂ : g.actOnObservables G₂ (ι x) = f₂ x.2.1 := by
      show G₂ (g.pullback (ι x)) = _
      rw [h₂]
      exact congrArg f₂ (funext fun b => hpull x b)
    show starRingEnd ℂ (g.actOnObservables G₂ (ι x)) * G₁ (ι x) *
      (Real.exp (-β * d.wilsonAction (ι x)) : ℂ) = _
    rw [e₁, e₂, haction]
  obtain ⟨hp₁, hp₂⟩ := hPos _ _ _ (fun e : TransverseEdge g (posHalf d μ c) μ => e.1)
    (fun e => e.start) (fun e => e.finish) A β hβ hAm (fun W => hA0 _) f f' hfm hfb hfm' hfb'
  have hz : 0 < (d.normalizingIntegral β)⁻¹ := inv_pos.mpr hZ'
  rw [hform F F f f hfm hfm hfU hfU, hform F F' f f' hfm hfm' hfU hfU',
    hform F' F' f' f' hfm' hfm' hfU' hfU']
  refine ⟨mul_nonneg (Complex.zero_le_real.mpr hz.le) hp₁, ?_⟩
  rw [norm_mul, Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.norm_real,
    Real.norm_of_nonneg hz.le, mul_pow]
  nlinarith [mul_le_mul_of_nonneg_left hp₂ (sq_nonneg (d.normalizingIntegral β)⁻¹)]
theorem isMirrorReflection_of_descend (hInd : TorusDescent.DescentTheorem)
    {d : CellGrid L κ} (μ : Fin 4) (c : ℝ)
    (hz : ∃ z : ℤ, c = PeriodicLattice.meshSize L κ * ((z : ℝ) + 1 / 2))
    {θ : d.Space → d.Space} (hθ : d.IsInducedMap θ (coordReflection μ c)) :
    BoxTorus.IsDistPreserving θ ∧
      θ '' (BoxTorus.gridSubgroup L κ d.sideLengths : Set d.Space) =
        (BoxTorus.gridSubgroup L κ d.sideLengths : Set d.Space) ∧
      IsMirrorReflection (d.symmetryOfMap θ) μ c := by
  obtain ⟨-, -, ⟨hex, hind, -, -, hiso⟩, himg, hrefl⟩ := hInd L κ d
  obtain ⟨hmem, -⟩ := hrefl μ c
  have hθeq : θ = descend d (coordReflection μ c) := (hex _ hmem).unique hθ (hind _ hmem)
  have hsites : coordReflection μ c ''
      (InfiniteLattice.latticeSubgroup (PeriodicLattice.meshSize L κ) :
        Set InfiniteLattice.AmbientSpace) =
      (InfiniteLattice.latticeSubgroup (PeriodicLattice.meshSize L κ) :
        Set InfiniteLattice.AmbientSpace) := by
    obtain ⟨z, hz⟩ := hz
    have hv : (2 * c) • InfiniteLattice.basisVector μ ∈
        InfiniteLattice.latticeSubgroup (PeriodicLattice.meshSize L κ) := by
      refine ⟨Pi.single μ (2 * z + 1), fun ν => ?_⟩
      by_cases h : ν = μ
      · subst h
        simp [InfiniteLattice.basisVector, hz]
        ring
      · simp [InfiniteLattice.basisVector, Pi.single_eq_of_ne h]
    exact InfiniteLattice.LatticeMotion.image_latticeSubgroup
      ⟨_, InfiniteLattice.coordinateSignFlip_mem_hypercubicGroup μ, _, hv,
        InfiniteLattice.coordinateReflection_eq_signFlip_add μ c⟩
  obtain ⟨R, w, hR, e⟩ := hmem
  have hlat : θ '' (BoxTorus.gridSubgroup L κ d.sideLengths : Set d.Space) =
      (BoxTorus.gridSubgroup L κ d.sideLengths : Set d.Space) := by
    rw [hθeq, e]
    exact (himg R w hR).2.2 (e ▸ hsites)
  have hi : BoxTorus.IsDistPreserving θ := by
    rw [hθeq]
    exact (hiso _ ⟨R, w, hR, e⟩).1
  have hto : (d.symmetryOfMap θ).toFun = θ := by
    rw [CellGrid.symmetryOfMap, dif_pos ⟨hi, hlat⟩]
  refine ⟨hi, hlat, hz, ?_⟩
  rw [hto]
  exact hθ
theorem shifted_mirror_position (hInd : TorusDescent.DescentTheorem)
    (hLat : GridLattice.Properties) {d : CellGrid L κ} (μ : Fin 4) (c : ℝ)
    (hz : ∃ z : ℤ, c = PeriodicLattice.meshSize L κ * ((z : ℝ) + 1 / 2))
    {θ : d.Space → d.Space} (hθ : d.IsInducedMap θ (coordReflection μ c)) :
    (∃ z : ℤ, c + 1 / 2 * d.sideLengths μ =
        PeriodicLattice.meshSize L κ * ((z : ℝ) + 1 / 2)) ∧
      d.IsInducedMap θ (coordReflection μ (c + 1 / 2 * d.sideLengths μ)) ∧
      posHalf d μ (c + 1 / 2 * d.sideLengths μ) = negHalf d μ c := by
  obtain ⟨-, -, ⟨hex, hind, -, -, -⟩, -, hrefl⟩ := hInd L κ d
  obtain ⟨hmem, -, -, -, ho₁, ho₂, -⟩ := hrefl μ c
  have hθeq : θ = descend d (coordReflection μ c) := (hex _ hmem).unique hθ (hind _ hmem)
  refine ⟨?_, hθeq ▸ ho₁, ho₂⟩
  obtain ⟨z, hz⟩ := hz
  obtain ⟨⟨hs, -⟩, -⟩ := hLat L κ d
  obtain ⟨-, N, hN, -, ⟨k, hk⟩, h4⟩ := hs μ
  have ha : PeriodicLattice.meshSize L κ ≠ 0 := by
    intro h0
    rw [h0, div_zero] at hN
    have : N = 0 := by exact_mod_cast hN
    omega
  have hside : d.sideLengths μ = ((k : ℝ) + k) * PeriodicLattice.meshSize L κ := by
    have : (N : ℝ) = (k : ℝ) + k := by exact_mod_cast hk
    rw [← this, hN]
    field_simp
  refine ⟨z + k, ?_⟩
  rw [hz, hside]
  push_cast
  ring
theorem positiveOnHalf_posHalf (hLay : MirrorLayers.LayeringTheorem)
    (hCo : GridMirror.MirrorCoordinates)
    (hAc : GridMirror.ActionSplitsAcrossMirror)
    (hPos : Matrices.TwoSidedGaugePositivity.PositivityStatement)
    (hInd : TorusDescent.DescentTheorem)
    (hLat : GridLattice.Properties)
    (hPull : GridSymmetries.PullbackContinuity)
    {d : CellGrid L κ} {β : ℝ} (hβ : 0 < β) (θ : d.Space → d.Space) (μ : Fin 4) (c : ℝ)
    (hg : IsMirrorReflection (d.symmetryOfMap θ) μ c) :
    PositiveOnHalf d β θ (posHalf d μ c) := by
  obtain ⟨h, -, layer, hl⟩ := hLay L κ d _ μ c hg
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hup, -⟩ := hl
  obtain ⟨-, -, -, -, hrefl⟩ := hInd L κ d
  obtain ⟨-, -, -, ⟨-, -, hopen, -⟩, -⟩ := hrefl μ c
  have hE : {b : d.DirectedEdge | b.LiesIn (posHalf d μ c)} =
      d.edgesWithin (posHalf d μ c) := Set.ext fun b => hup b
  refine ⟨hup, hopen, ?_, ?_⟩
  · show {F | IsBoundedBorelOfEdges (d.edgesWithin (posHalf d μ c)) F} = _
    rw [hE]
  · intro F hF F' hF'
    have h₁ : IsBoundedBorelOfEdges
        {b : d.DirectedEdge | b.LiesIn (posHalf d μ c)} F := by
      rw [hE]
      exact hF
    have h₂ : IsBoundedBorelOfEdges
        {b : d.DirectedEdge | b.LiesIn (posHalf d μ c)} F' := by
      rw [hE]
      exact hF'
    exact positive_on_posHalf hLay hCo hAc hPos hLat hPull hβ θ μ c hg h₁ h₂
theorem reflectionPositivityAcrossMirrors_holds (hLay : MirrorLayers.LayeringTheorem)
    (hCo : GridMirror.MirrorCoordinates)
    (hAc : GridMirror.ActionSplitsAcrossMirror)
    (hPos : Matrices.TwoSidedGaugePositivity.PositivityStatement)
    (hInd : TorusDescent.DescentTheorem)
    (hLat : GridLattice.Properties)
    (hGeo : GroupAndCells.AllHold)
    (hPull : GridSymmetries.PullbackContinuity) : ReflectionPositivityAcrossMirrors := by
  intro L κ d β hβ
  refine ⟨fun μ c hz => ?_, ?_⟩
  · obtain ⟨-, -, ⟨hex, hind, -, -, -⟩, -, hrefl⟩ := hInd L κ d
    obtain ⟨hmem, -⟩ := hrefl μ c
    refine ⟨(hex _ hmem), fun θ hθ => ?_⟩
    have hθ' : d.IsInducedMap θ (coordReflection μ c) := hθ
    obtain ⟨hi, hlat, hg⟩ := isMirrorReflection_of_descend hInd μ c hz hθ'
    obtain ⟨hz', hθ'', hu⟩ := shifted_mirror_position hInd hLat μ c hz hθ'
    obtain ⟨-, -, hg'⟩ := isMirrorReflection_of_descend hInd μ _ hz' hθ''
    refine ⟨hi, hlat, positiveOnHalf_posHalf hLay hCo hAc hPos hInd hLat hPull hβ θ μ c hg, ?_⟩
    have := positiveOnHalf_posHalf hLay hCo hAc hPos hInd hLat hPull hβ θ μ _ hg'
    rw [hu] at this
    exact this
  · intro μ a θ hθ H hH F hF
    obtain ⟨-, -, -, -, -, hm, -⟩ := hGeo L κ d
    obtain ⟨⟨hz, -, hfix, -, -, hcomps, -⟩, -⟩ := hm μ a θ hθ
    have hcr : d.faceReflect μ a = coordReflection μ (d.faceLevel μ a) := by
      funext x
      show x - _ = x - _
      congr 2
      simp only [CellGrid.faceLevel]
      ring
    have hθ' : d.IsInducedMap θ (coordReflection μ (d.faceLevel μ a)) := hcr ▸ hθ
    obtain ⟨-, -, hg⟩ := isMirrorReflection_of_descend hInd μ _ hz hθ'
    obtain ⟨hz', hθ'', hu⟩ := shifted_mirror_position hInd hLat μ _ hz hθ'
    obtain ⟨-, -, hg'⟩ := isMirrorReflection_of_descend hInd μ _ hz' hθ''
    have hmemH : H ∈ ({d.upperSlab μ a, d.lowerSlab μ a} : Set (Set d.Space)) := by
      rw [← hcomps]
      obtain ⟨x, hx, rfl⟩ := hH
      exact ⟨x, hfix ▸ hx, by rw [hfix]⟩
    rcases hmemH with rfl | hlow
    · exact (positive_on_posHalf hLay hCo hAc hPos hLat hPull hβ θ μ _ hg hF hF).1
    · have hlow' : H = posHalf d μ (d.faceLevel μ a + 1 / 2 * d.sideLengths μ) := by
        rw [hu]
        exact hlow
      subst hlow'
      exact (positive_on_posHalf hLay hCo hAc hPos hLat hPull hβ θ μ _ hg' hF hF).1
end MirrorPositivity
end YangMills.Construction
end
