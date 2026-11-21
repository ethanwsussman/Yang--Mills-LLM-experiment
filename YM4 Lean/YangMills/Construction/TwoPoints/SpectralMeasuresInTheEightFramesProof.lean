import YangMills.Construction.TwoPoints.EntireContinuationInTheRotationAngleProof
import YangMills.Construction.TwoPoints.ExistenceOfThePlaneSpectralMeasure
import YangMills.Construction.TwoPoints.NormOfAPlateInTheSpectralVariablesProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace YangMills.Construction
open SpectralCalculus
namespace TwoPoints
open InfiniteLattice (AmbientSpace)
open PeriodicLattice (coordVec)
namespace SpectralMeasuresAtAllNormals
section Measure
variable {B : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ} {f : (Fin 2 → ℝ) → ℂ}
  {n : AmbientSpace} {μ : Measure SpectralPlane}
theorem measurable_energyDecay (s : ℝ) : Measurable (energyDecay s) := by apply _root_.YangMills.Construction.TwoPoints.AxisDecayGrowthAtZero.measurable_energyDecay <;> assumption
theorem energyDecay_nonneg (s : ℝ) (q : SpectralPlane) : 0 ≤ energyDecay s q :=
  (Real.exp_pos _).le
theorem energyDecay_antitone {s s' : ℝ} (hs : s ≤ s') (q : SpectralPlane) :
    energyDecay s' q ≤ energyDecay s q := by apply _root_.YangMills.Construction.TwoPoints.EntireAngleContinuationProof.energyDecay_antitone <;> assumption
theorem energyDecay_le_one {s : ℝ} (hs : 0 ≤ s) (q : SpectralPlane) :
    energyDecay s q ≤ 1 := by
  have := energyDecay_antitone hs q
  simpa [energyDecay] using this
theorem lintegral_energyDecay_lt_top (hμ : IsAveragedKernelSpectralMeasure B f n μ) {s : ℝ}
    (hs : 0 < s) : ∫⁻ q, ENNReal.ofReal (energyDecay s q) ∂μ < ∞ := by
  exact hμ.lintegral_decay_lt_top ⟨s, hs.le⟩ (by exact_mod_cast hs)
theorem integrable_energyDecay (hμ : IsAveragedKernelSpectralMeasure B f n μ) {s : ℝ}
    (hs : 0 < s) : Integrable (energyDecay s) μ := by apply _root_.YangMills.Construction.TwoPoints.PlateNormViaSpectralMeasure.integrable_energyDecay <;> assumption
theorem spectralCharacter_zero (s : ℝ≥0) (q : SpectralPlane) :
    spectralCharacter s 0 q = ((energyDecay s q : ℝ) : ℂ) := by
  simp [spectralCharacter, energyDecay]
theorem transverseAveragedKernel_eq_integral (hμ : IsAveragedKernelSpectralMeasure B f n μ)
    {s : ℝ} (hs : 0 < s) :
    transverseAveragedKernel B f (planeCoords (s • n)) = ((∫ q, energyDecay s q ∂μ : ℝ) : ℂ) := by
  have h := hμ.kernel_eq_integral ⟨s, hs.le⟩ (by exact_mod_cast hs) 0
  rw [zero_smul, add_zero] at h
  change transverseAveragedKernel B f (planeCoords (s • n)) = _ at h
  rw [h, integralWrt, ← integral_complex_ofReal]
  exact integral_congr_ae (Eventually.of_forall fun q => spectralCharacter_zero ⟨s, hs.le⟩ q)
theorem integral_energyDecay_antitoneOn (hμ : IsAveragedKernelSpectralMeasure B f n μ) :
    AntitoneOn (fun s : ℝ => ∫ q, energyDecay s q ∂μ) (Ioi 0) := by
  intro s hs s' hs' hle
  exact integral_mono (integrable_energyDecay hμ hs') (integrable_energyDecay hμ hs)
    (energyDecay_antitone hle)
theorem tendsto_total_mass (hμ : IsAveragedKernelSpectralMeasure B f n μ) :
    Tendsto (fun s : ℝ => ENNReal.ofReal (∫ q, energyDecay s q ∂μ)) (𝓝[>] 0) (𝓝 (μ univ)) := by
  have hval : ∀ s : ℝ, 0 < s → ENNReal.ofReal (∫ q, energyDecay s q ∂μ) =
      ∫⁻ q, ENNReal.ofReal (energyDecay s q) ∂μ := fun s hs =>
    ofReal_integral_eq_lintegral_ofReal (integrable_energyDecay hμ hs)
      (Eventually.of_forall (energyDecay_nonneg s))
  have hseq : Tendsto (fun k : ℕ => ∫⁻ q, ENNReal.ofReal (energyDecay (1 / ((k : ℝ) + 1)) q) ∂μ)
      atTop (𝓝 (∫⁻ _, 1 ∂μ)) := by
    refine lintegral_tendsto_of_tendsto_of_monotone
      (fun k => (measurable_energyDecay _).ennreal_ofReal.aemeasurable) ?_ ?_
    · refine Eventually.of_forall fun q k l hkl => ENNReal.ofReal_le_ofReal ?_
      refine energyDecay_antitone ?_ q
      have : (k : ℝ) ≤ l := by exact_mod_cast hkl
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    · refine Eventually.of_forall fun q => ?_
      have h0 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h1 : Tendsto (fun k : ℕ => energyDecay (1 / ((k : ℝ) + 1)) q) atTop (𝓝 1) := by
        have hc : Continuous fun s : ℝ => energyDecay s q := by
          unfold energyDecay
          fun_prop
        have := (hc.tendsto 0).comp h0
        rw [show energyDecay 0 q = 1 by simp [energyDecay]] at this
        exact this
      have h2 := (ENNReal.continuous_ofReal.tendsto 1).comp h1
      rw [ENNReal.ofReal_one] at h2
      exact h2
  simp only [lintegral_const, one_mul] at hseq
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · obtain ⟨k, hk⟩ := (hseq.eventually (lt_mem_nhds ha)).exists
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    filter_upwards [Ioo_mem_nhdsGT hpos] with s hs
    rw [hval s hs.1]
    refine hk.trans_le (lintegral_mono fun q => ENNReal.ofReal_le_ofReal ?_)
    exact energyDecay_antitone hs.2.le q
  · filter_upwards [self_mem_nhdsWithin] with s hs
    rw [hval s hs]
    refine lt_of_le_of_lt ?_ hb
    calc ∫⁻ q, ENNReal.ofReal (energyDecay s q) ∂μ ≤ ∫⁻ _, 1 ∂μ :=
          lintegral_mono fun q => by
            simpa using ENNReal.ofReal_le_ofReal (energyDecay_le_one (le_of_lt hs) q)
      _ = μ univ := by simp
theorem isFiniteMeasure_weighted (hμ : IsAveragedKernelSpectralMeasure B f n μ) :
    IsFiniteMeasure (μ.withDensity fun q => ENNReal.ofReal (energyDecay 1 q)) :=
  isFiniteMeasure_withDensity (lintegral_energyDecay_lt_top hμ one_pos).ne
theorem sigmaFinite_of_isSpectral (hμ : IsAveragedKernelSpectralMeasure B f n μ) :
    SigmaFinite μ := by apply _root_.YangMills.Construction.TwoPoints.PlateNormViaSpectralMeasure.sigmaFinite_of_isAveragedKernelSpectralMeasure <;> assumption
end Measure
theorem signedPerm_mem_reflectionNormals {L : AmbientSpace →ₗ[ℝ] AmbientSpace}
    (hL : IsSignedPerm L) {v : AmbientSpace} (hv : v ∈ reflectionNormals) :
    L v ∈ reflectionNormals := by
  obtain ⟨σ, e, h⟩ := hL
  have hsign : ∀ (i : Fin 4) (c : ℝ), (c = 1 ∨ c = -1) →
      (c * (((e i : ℤˣ) : ℤ) : ℝ) = 1 ∨ c * (((e i : ℤˣ) : ℤ) : ℝ) = -1) := by
    intro i c hc
    rcases Int.units_eq_one_or (e i) with h1 | h1 <;> rcases hc with rfl | rfl <;> simp [h1]
  rcases hv with ⟨i, c, hc, rfl⟩ | ⟨i, j, c, c', hij, hc, hc', rfl⟩
  · left
    refine ⟨σ i, _, hsign i c hc, ?_⟩
    rw [map_smul, h, smul_smul]
  · right
    have hne : σ i ≠ σ j := fun he => hij.ne (σ.injective he)
    have hval : L ((Real.sqrt 2)⁻¹ • (c • coordVec i + c' • coordVec j)) =
        (Real.sqrt 2)⁻¹ • ((c * (((e i : ℤˣ) : ℤ) : ℝ)) • coordVec (σ i) +
          (c' * (((e j : ℤˣ) : ℤ) : ℝ)) • coordVec (σ j)) := by
      simp only [map_smul, map_add, h, smul_smul]
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact ⟨σ i, σ j, _, _, hlt, hsign i c hc, hsign j c' hc', hval⟩
    · refine ⟨σ j, σ i, _, _, hlt, hsign j c' hc', hsign i c hc, ?_⟩
      rw [hval, add_comm]
theorem dihedral_mem_planeReflectionNormals (hD : DihedralAndRightAngle)
    {g : Equiv.Perm AmbientSpace} (hg : g ∈ dihedralInPlane) {v : AmbientSpace}
    (hv : v ∈ planeReflectionNormals) : g v ∈ planeReflectionNormals := by
  obtain ⟨L, hL, hsp⟩ := exists_isSignedPerm hg.1
  refine ⟨?_, ?_⟩
  · have h := signedPerm_mem_reflectionNormals hsp hv.1
    rwa [hL] at h
  · rw [← (hD.2.2.1 g hg).1]
    exact mem_image_of_mem _ hv.2
theorem embedPlane_planeCoords {x : AmbientSpace} (hx : x ∈ coordPlane) :
    embedPlane (planeCoords x) = x := by
  have h1 : x 1 = 0 := congrFun hx 0
  have h2 : x 2 = 0 := congrFun hx 1
  funext i
  fin_cases i <;>
    simp [embedPlane, planeCoords, coordVec, PeriodicLattice.coordVec, h1, h2]
theorem smul_mem_coordPlane (s : ℝ) {x : AmbientSpace} (hx : x ∈ coordPlane) :
    s • x ∈ coordPlane := by
  have h1 : x 1 = 0 := congrFun hx 0
  have h2 : x 2 = 0 := congrFun hx 1
  funext i
  fin_cases i <;> simp [transCoords, h1, h2]
theorem euclidNorm_eq_one (h : ReflectionNormalsCount) {v : AmbientSpace}
    (hv : v ∈ reflectionNormals) : euclidNorm v = 1 := by
  rcases hv with ⟨i, c, hc, rfl⟩ | ⟨i, j, c, c', hij, hc, hc', rfl⟩
  · exact h.1 i c hc
  · exact h.2.1 i j c c' hij hc hc'
theorem planeCoords_smul_ne_zero (h : ReflectionNormalsCount) {v : AmbientSpace}
    (hv : v ∈ planeReflectionNormals) {s : ℝ} (hs : 0 < s) : planeCoords (s • v) ≠ 0 := by
  intro h0
  have he := embedPlane_planeCoords (smul_mem_coordPlane s hv.2)
  have hz : s • v = 0 := by
    rw [← he, h0]
    simp [embedPlane]
  have hv0 : v = 0 := (smul_eq_zero.mp hz).resolve_left hs.ne'
  have h1 := euclidNorm_eq_one h hv.1
  rw [hv0] at h1
  simp [euclidNorm] at h1
theorem statement_holds (hElem : ReflectionsPlaneFacts.Statement)
    (hKer : AveragedKernelProperties.Statement)
    (hEx : AveragedKernelSpectralMeasureExists.Statement)
    (hNorm : PlateNormViaSpectralMeasure.Statement) : Statement := by
  intro St B f hF hP hf
  have hspec : ∀ v ∈ planeReflectionNormals,
      IsAveragedKernelSpectralMeasure B f v (averagedKernelSpectralMeasure B f v) :=
    fun v hv => Classical.epsilon_spec (hEx St B f hF hP hf v hv)
  obtain ⟨h32, -, -, h8, -, hD, -, -⟩ := hElem
  obtain ⟨hG, -, -⟩ := hKer St B hF hP f hf
  have hker : ∀ v ∈ planeReflectionNormals, ∀ s : ℝ, 0 < s →
      ((decayTransform B f v s : ℝ) : ℂ) = transverseAveragedKernel B f (planeCoords (s • v)) :=
    fun v hv s hs => (transverseAveragedKernel_eq_integral (hspec v hv) hs).symm
  have hsym : ∀ v ∈ planeReflectionNormals, ∀ g ∈ dihedralInPlane, ∀ s : ℝ, 0 < s →
      decayTransform B f (g v) s = decayTransform B f v s := by
    intro v hv g hg s hs
    have hgv := dihedral_mem_planeReflectionNormals hD hg hv
    apply Complex.ofReal_injective
    rw [hker _ hgv s hs, hker v hv s hs]
    have hinv := hG.invariant g hg _ (planeCoords_smul_ne_zero h32 hv hs)
    rw [embedPlane_planeCoords (smul_mem_coordPlane s hv.2)] at hinv
    obtain ⟨L, hL, -⟩ := exists_isSignedPerm hg.1
    have hlin : g (s • v) = s • g v := by
      rw [← hL, map_smul]
    rwa [hlin] at hinv
  have hdata : ∀ v ∈ planeReflectionNormals, NormalSpectralData B f v := fun v hv =>
    { represents := ⟨hspec v hv, fun _ _ => rfl, hker v hv⟩
      transform_nonneg := fun s _ => integral_nonneg (energyDecay_nonneg s)
      transform_antitoneOn := integral_energyDecay_antitoneOn (hspec v hv)
      transform_invariant := hsym v hv
      plateNorm := fun α hα h => hNorm St B f hF hP hf v hv _ (hspec v hv) α hα h
      tendsto_total := tendsto_total_mass (hspec v hv)
      isFinite_weighted := isFiniteMeasure_weighted (hspec v hv)
      sigmaFinite := sigmaFinite_of_isSpectral (hspec v hv) }
  obtain ⟨-, -, -, ⟨g, hg, hgq⟩, -, q1, q2, q3, -, p1, p2, p3⟩ := hD
  have hq : ∀ x, g x = rightAngleRotation x := fun x => congrFun hgq x
  have hq2 : ∀ x, (rightAngleRotation ^ 2) x = g (g x) := fun x => by
    rw [hq, hq, pow_two]
    rfl
  have hq3 : ∀ x, (rightAngleRotation ^ 3) x = g (g (g x)) := fun x => by
    rw [hq, hq, hq, pow_succ, pow_two]
    rfl
  have hq1 : ∀ x, (rightAngleRotation ^ 1) x = g x := fun x => by
    rw [hq, pow_one]
  rw [hq1] at q1 p1
  rw [hq2] at q2 p2
  rw [hq3, q2] at q3
  have hlist := h8.2.1
  have he₄ : coordVec 3 ∈ planeReflectionNormals := by rw [hlist]; simp
  have he₁ : coordVec 0 ∈ planeReflectionNormals := by rw [hlist]; simp
  have hme₄ : -coordVec 3 ∈ planeReflectionNormals := by rw [hlist]; simp
  have hnp : diagNormalPlus ∈ planeReflectionNormals := by rw [hlist]; simp
  have hmnm : -diagNormalMinus ∈ planeReflectionNormals := by rw [hlist]; simp
  have hmnp : -diagNormalPlus ∈ planeReflectionNormals := by rw [hlist]; simp
  refine ⟨hdata, fun s hs => ?_, fun s hs => ?_⟩
  · have a₁ : decayTransform B f (coordVec 0) s = decayTransform B f (coordVec 3) s := by
      rw [← q1]
      exact hsym _ he₄ g hg s hs
    have a₂ : decayTransform B f (-coordVec 3) s = decayTransform B f (coordVec 3) s := by
      rw [← q2, q1, hsym _ he₁ g hg s hs, a₁]
    have a₃ : decayTransform B f (-coordVec 0) s = decayTransform B f (coordVec 3) s := by
      rw [← q3, hsym _ hme₄ g hg s hs, a₂]
    exact ⟨rfl, a₂, a₁, a₃⟩
  · have b₁ : decayTransform B f (-diagNormalMinus) s = decayTransform B f diagNormalPlus s := by
      rw [← p1]
      exact hsym _ hnp g hg s hs
    have b₂ : decayTransform B f (-diagNormalPlus) s = decayTransform B f diagNormalPlus s := by
      rw [← p2, p1, hsym _ hmnm g hg s hs, b₁]
    have b₃ : decayTransform B f diagNormalMinus s = decayTransform B f diagNormalPlus s := by
      rw [hq3, p2] at p3
      rw [← p3, hsym _ hmnp g hg s hs, b₂]
    exact ⟨rfl, b₂, b₃, b₁⟩
end SpectralMeasuresAtAllNormals
end TwoPoints
end YangMills.Construction
end
