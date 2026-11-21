import YangMills.Construction.LawOnABoxOfTheFlow.BorelChartOfABox
import YangMills.Construction.LawOnABoxOfTheFlow.OnePointInAnOrbit
import YangMills.Construction.LawOnABoxOfTheFlow.ToolsOfAChart
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.BoxGaussian
open YangMills.Construction.TorusFields YangMills.Construction.TorusLumps
open YangMills.Construction.ResponseInTheExpansion YangMills.Construction.BlockAverages
variable {n : ℕ} [NeZero n]
set_option synthInstance.maxSize 1024
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
private def chartIncidence (a : ℝ) (L k : ℕ) (o : TorusSite n) (R : ℕ) (c₀ δ : ℝ) :
    Set (ChartPoint o R × ((TorusSite n → UnitQuaternion) × (TorusBond n → imaginaryQuaternions))) :=
  {z | IsAxialSmall o R δ z.1.1 ∧ IsSupportedGauge o R z.2.1 ∧ z.2.2 ∈ sliceEllipsoid a L k o R z.1.1 c₀ ∧
    IsInChart (supBall o (2 * R)) z.1.1 z.2.2
      (TorusFields.gaugeTransform (z.1.2.1 * z.2.1) (glueField z.1.2.2.1 z.1.2.2.2))}
private theorem isClosed_chartIncidence (a : ℝ) (L k : ℕ) (o : TorusSite n) (R : ℕ) (c₀ δ : ℝ)
    (hq : Continuous fun v : TorusBond n → imaginaryQuaternions =>
      hessianForm a L k (supBall o (2 * R)) v v) :
    IsClosed (chartIncidence a L k o R c₀ δ) := by
  have hA : Continuous fun z : ChartPoint o R × ((TorusSite n → UnitQuaternion) ×
      (TorusBond n → imaginaryQuaternions)) => z.1.1 :=
    continuous_fst.comp continuous_fst
  have hζ : Continuous fun z : ChartPoint o R × ((TorusSite n → UnitQuaternion) ×
      (TorusBond n → imaginaryQuaternions)) => z.2.2 :=
    continuous_snd.comp continuous_snd
  have hg : Continuous fun z : ChartPoint o R × ((TorusSite n → UnitQuaternion) ×
      (TorusBond n → imaginaryQuaternions)) => z.1.2.1 :=
    continuous_fst.comp (continuous_snd.comp continuous_fst)
  have hγ : Continuous fun z : ChartPoint o R × ((TorusSite n → UnitQuaternion) ×
      (TorusBond n → imaginaryQuaternions)) => z.2.1 :=
    continuous_fst.comp continuous_snd
  have hu : Continuous fun z : ChartPoint o R × ((TorusSite n → UnitQuaternion) ×
      (TorusBond n → imaginaryQuaternions)) => (z.1.2.2.1, z.1.2.2.2) :=
    (continuous_snd.comp (continuous_snd.comp continuous_fst))
  have hW : Continuous fun z : ChartPoint o R × ((TorusSite n → UnitQuaternion) ×
      (TorusBond n → imaginaryQuaternions)) =>
      TorusFields.gaugeTransform (z.1.2.1 * z.2.1) (glueField z.1.2.2.1 z.1.2.2.2) :=
    Continuous.comp (g := fun p : (TorusSite n → UnitQuaternion) × TorusField n =>
        TorusFields.gaugeTransform p.1 p.2) continuous_gaugeTransform_prod
      (f := fun z : ChartPoint o R × ((TorusSite n → UnitQuaternion) ×
        (TorusBond n → imaginaryQuaternions)) =>
        (z.1.2.1 * z.2.1, glueField z.1.2.2.1 z.1.2.2.2))
      ((hg.mul hγ).prodMk (Continuous.comp
        (g := fun p : OuterField o R × InnerField o R => (glueField p.1 p.2 : TorusField n))
        (continuous_glueField o R) hu))
  have h : chartIncidence a L k o R c₀ δ =
      {z | z.1.1 ∈ {A | IsAxialSmall o R δ A}} ∩
      (⋂ y ∈ {y : TorusSite n | y ∉ supBall o R}, {z | z.2.1 y = 1}) ∩
      {z | (z.1.1, z.2.2) ∈ {p : (TorusBond n → imaginaryQuaternions) × (TorusBond n → imaginaryQuaternions) |
        p.2 ∈ gaugeSlice o R p.1}} ∩
      {z | hessianForm a L k (supBall o (2 * R)) (z.1.1 + z.2.2) (z.1.1 + z.2.2) ≤ c₀} ∩
      (⋂ b ∈ bondsWithin (supBall o (2 * R)),
        {z | ((TorusFields.gaugeTransform (z.1.2.1 * z.2.1) (glueField z.1.2.2.1 z.1.2.2.2) b.1 b.2 :
            UnitQuaternion) : ℍ[ℝ]) = chartPoint (z.1.1 b) (z.2.2 b)}) := by
    ext z
    simp only [chartIncidence, sliceEllipsoid, IsSupportedGauge, IsInChart, Set.mem_setOf_eq,
      Set.mem_inter_iff, Set.mem_iInter]
    tauto
  rw [h]
  refine ((((isClosed_setOf_isAxialSmall o R δ).preimage hA).inter ?_ |>.inter ?_).inter ?_).inter ?_
  · exact isClosed_biInter fun y _ =>
      isClosed_eq ((continuous_apply y).comp hγ) continuous_const
  · exact (isClosed_gaugeSlice_graph o R).preimage (hA.prodMk hζ)
  · exact isClosed_le (hq.comp (hA.add hζ)) continuous_const
  · refine isClosed_biInter fun b _ => isClosed_eq ?_ ?_
    · exact continuous_subtype_val.comp
        ((continuous_apply b.2).comp ((continuous_apply b.1).comp hW))
    · exact continuous_chartPoint ((continuous_apply b).comp hA) ((continuous_apply b).comp hζ)
theorem measurableChart_of_bounds (hB : ellipsoidBoundsStatement) (hO : chartMeetsOrbitOnceStatement)
    (hF : cubeHessianStatement) : measurableChartStatement := by
  intro Tb hTb κ₀ h1 h2 C₀ hC₀
  obtain ⟨K, x₁, hK1, hb⟩ := hB Tb hTb κ₀ h1 h2 C₀ hC₀
  obtain ⟨x₂, ho⟩ := hO Tb hTb κ₀ h1 h2 C₀ hC₀
  obtain ⟨CQ, R₀, -, hf⟩ := hF Tb hTb
  refine ⟨max (max x₁ x₂) (((R₀ : ℝ) + 1) ^ 27), ?_⟩
  intro x R k n _ o hx hR hn
  have hx₁ : x₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx₂ : x₂ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hRR : R₀ ≤ R := by
    rw [hR]
    exact le_boxRadius κ₀ x h1 R₀ (le_trans (le_max_right _ _) hx)
  obtain ⟨-, -, -, -, -, -, hform⟩ := hf k n o R hRR hn
  set c₀ := C₀ * (R : ℝ) ^ 4 * boxScale x ^ 2 with hc₀
  set δ := boxScale x with hδ
  have hq : Continuous fun v : TorusBond n → imaginaryQuaternions =>
      hessianForm Tb.coupling Tb.side k (supBall o (2 * R)) v v := by
    have : (fun v : TorusBond n → imaginaryQuaternions =>
        hessianForm Tb.coupling Tb.side k (supBall o (2 * R)) v v) = fun v =>
        ∑ e : Fin 3, ∑ b : TorusBond n, ∑ b' : TorusBond n,
          mixedDeriv (actionAtLevel Tb.coupling Tb.side k (supBall o (2 * R))) (trivialField n) ![b, b']
              ![imaginaryUnitI, imaginaryUnitI] *
            imaginaryComponent e (v b) * imaginaryComponent e (v b') := funext fun v => hform v v
    rw [this]
    refine continuous_finset_sum _ fun e _ => continuous_finset_sum _ fun b _ =>
      continuous_finset_sum _ fun b' _ => ?_
    exact (continuous_const.mul ((continuous_imaginaryComponent e).comp (continuous_apply b))).mul
      ((continuous_imaginaryComponent e).comp (continuous_apply b'))
  have hZ := isClosed_chartIncidence Tb.coupling Tb.side k o R c₀ δ hq
  set M : ℝ := K * (R : ℝ) ^ 3 * δ with hM
  let Kb : Set (TorusBond n → imaginaryQuaternions) := Set.pi Set.univ fun _ => Metric.closedBall 0 M
  have hKb : IsCompact Kb := isCompact_univ_pi fun _ => isCompact_closedBall 0 M
  have hbd : ∀ (A : TorusBond n → imaginaryQuaternions), IsAxialSmall o R δ A →
      ∀ ζ ∈ sliceEllipsoid Tb.coupling Tb.side k o R A c₀, ζ ∈ Kb := by
    intro A hA ζ hζ b _
    have := (hb x R k n o A hx₁ hR hn hA).2 ζ hζ
    simpa [M, mem_closedBall_zero_iff] using this.2.1 b
  let Kt := {z : (TorusSite n → UnitQuaternion) × Kb // True}
  haveI : CompactSpace Kb := isCompact_iff_compactSpace.mp hKb
  let Z₁ : Set (ChartPoint o R × ((TorusSite n → UnitQuaternion) × Kb)) :=
    {z | (z.1, (z.2.1, (z.2.2 : TorusBond n → imaginaryQuaternions))) ∈
      chartIncidence Tb.coupling Tb.side k o R c₀ δ}
  have hZ₁ : IsClosed Z₁ := hZ.preimage (continuous_fst.prodMk
    ((continuous_fst.comp continuous_snd).prodMk
      (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))))
  have hE : chartPointSet Tb.coupling Tb.side k o R c₀ δ = Prod.fst '' Z₁ := by
    ext p
    constructor
    · rintro ⟨hA, γ, ζ, hγ, hζ, hc⟩
      exact ⟨(p, (γ, ⟨ζ, hbd _ hA ζ hζ⟩)), ⟨hA, hγ, hζ, hc⟩, rfl⟩
    · rintro ⟨z, ⟨hA, hγ, hζ, hc⟩, rfl⟩
      exact ⟨hA, z.2.1, z.2.2, hγ, hζ, hc⟩
  have hEc : IsClosed (chartPointSet Tb.coupling Tb.side k o R c₀ δ) := by
    rw [hE]
    exact isClosedMap_fst_of_compactSpace _ hZ₁
  refine ⟨hEc.measurableSet, ?_⟩
  let Gr : Set (ChartPoint o R × (TorusBond n → imaginaryQuaternions)) :=
    (fun z : (ChartPoint o R × (TorusBond n → imaginaryQuaternions)) × (TorusSite n → UnitQuaternion) => z.1) ''
      {z | (z.1.1, (z.2, z.1.2)) ∈ chartIncidence Tb.coupling Tb.side k o R c₀ δ}
  have hGr : IsClosed Gr := by
    refine isClosedMap_fst_of_compactSpace _ (hZ.preimage ?_)
    exact (continuous_fst.comp continuous_fst).prodMk
      (continuous_snd.prodMk (continuous_snd.comp continuous_fst))
  classical
  let φ : ChartPoint o R → TorusBond n → imaginaryQuaternions := fun p =>
    if h : p ∈ chartPointSet Tb.coupling Tb.side k o R c₀ δ then h.2.choose_spec.choose else 0
  have hφ : ∀ p ∈ chartPointSet Tb.coupling Tb.side k o R c₀ δ,
      ∃ γ, (p, (γ, φ p)) ∈ chartIncidence Tb.coupling Tb.side k o R c₀ δ := by
    intro p hp
    have hs := hp.2.choose_spec.choose_spec
    refine ⟨hp.2.choose, hp.1, hs.1, ?_, ?_⟩
    · simpa only [φ, dif_pos hp] using hs.2.1
    · simpa only [φ, dif_pos hp] using hs.2.2
  have hone : ∀ p ∈ chartPointSet Tb.coupling Tb.side k o R c₀ δ, ∀ v, (p, v) ∈ Gr → v ∈ Kb → v = φ p := by
    rintro p hp v ⟨⟨⟨p', v'⟩, γ'⟩, ⟨hA, hγ', hv, hc'⟩, hpv⟩ -
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpv
    obtain ⟨γ, -, hγ, hv₂, hc⟩ := hφ p' hp
    have hin : IsSupportedGauge o R ((p'.2.1 * γ') * (p'.2.1 * γ)⁻¹) := by
      intro z hz
      have e1 : γ z = 1 := hγ z hz
      have e2 : γ' z = 1 := hγ' z hz
      show (p'.2.1 * γ' * (p'.2.1 * γ)⁻¹) z = 1
      simp [Pi.mul_apply, Pi.inv_apply, e1, e2]
    have hgg : TorusFields.gaugeTransform ((p'.2.1 * γ') * (p'.2.1 * γ)⁻¹)
        (TorusFields.gaugeTransform (p'.2.1 * γ) (glueField p'.2.2.1 p'.2.2.2)) =
        TorusFields.gaugeTransform (p'.2.1 * γ') (glueField p'.2.2.1 p'.2.2.2) := by
      rw [gaugeTransform_gaugeTransform, inv_mul_cancel_right]
    have := ho x R k n o p'.1 hx₂ hR hn hA
      (TorusFields.gaugeTransform (p'.2.1 * γ) (glueField p'.2.2.1 p'.2.2.2))
      ((p'.2.1 * γ') * (p'.2.1 * γ)⁻¹) (φ p') v' hin hv₂ hv hc (by rw [hgg]; exact hc')
    exact this.1
  have hcont : ContinuousOn φ (chartPointSet Tb.coupling Tb.side k o R c₀ δ) := by
    refine continuousOn_of_isClosed_graph_of_isCompact hKb hEc hGr (fun p hp => ?_) hone
    obtain ⟨γ, hz⟩ := hφ p hp
    exact ⟨⟨((p, φ p), γ), hz, rfl⟩, hbd _ hz.1 _ hz.2.2.1⟩
  refine ⟨(chartPointSet Tb.coupling Tb.side k o R c₀ δ).piecewise φ (fun _ => 0), ?_, ?_⟩
  · exact hcont.measurable_piecewise continuousOn_const hEc.measurableSet
  · intro p hp
    obtain ⟨γ, hz⟩ := hφ p hp
    refine ⟨γ, hz.2.1, ?_, ?_⟩
    · rw [Set.piecewise_eq_of_mem _ _ _ hp]
      exact hz.2.2.1
    · rw [Set.piecewise_eq_of_mem _ _ _ hp]
      exact hz.2.2.2
end YangMills.Construction.BoxGaussian
end
