import YangMills.Construction.ClusterExpansionOfAStep.TwoSettingsOnABoxProof
import YangMills.Construction.ColdStepAtMirrorFrames.ChartEnergyInCoordinates
import YangMills.Construction.ColdStepAtMirrorFrames.EnergyAboutAChartPoint
import YangMills.Construction.ColdStepAtMirrorFrames.LieCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace ChartedEnergyLocal
section Calculus
variable {ι : Type} [Fintype ι]
theorem fderiv_apply_multilinear {n : ℕ} {Φ : BondField ι → ContinuousMultilinearMap ℝ (fun _ : Fin n => BondField ι) ℝ}
    {p : BondField ι} (hΦ : DifferentiableAt ℝ Φ p) (m : Fin n → BondField ι) (z : BondField ι) :
    fderiv ℝ (fun ζ => Φ ζ m) p z = fderiv ℝ Φ p z m := by
  have h := ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => BondField ι) ℝ m).hasFDerivAt (x := Φ p)).comp p
    hΦ.hasFDerivAt
  have e : (fun ζ => Φ ζ m) = (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => BondField ι) ℝ m) ∘ Φ := rfl
  rw [e, h.fderiv]
  rfl
theorem secondDerivAlong_eq_iteratedFDeriv {f : BondField ι → ℝ} {p : BondField ι} (h : ContDiffAt ℝ 2 f p)
    (u v : BondField ι) : secondDerivAlong f p u v = iteratedFDeriv ℝ 2 f p ![v, u] := by
  have d : DifferentiableAt ℝ (iteratedFDeriv ℝ 1 f) p :=
    (h.iteratedFDeriv_right (m := 1) (i := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [iteratedFDeriv_succ_apply_left]
  have t : (Fin.tail ![v, u] : Fin 1 → BondField ι) = ![u] := by
    funext i
    fin_cases i
    rfl
  have e0 : (![v, u] : Fin 2 → BondField ι) 0 = v := rfl
  rw [e0, t, ← fderiv_apply_multilinear d]
  unfold secondDerivAlong
  congr 2
  funext ζ
  rw [iteratedFDeriv_one_apply]
  rfl
theorem thirdDerivAlong_eq_iteratedFDeriv {f : BondField ι → ℝ} {p : BondField ι} (h : ContDiffAt ℝ 3 f p)
    (u v z : BondField ι) : thirdDerivAlong f p u v z = iteratedFDeriv ℝ 3 f p ![z, v, u] := by
  have d : DifferentiableAt ℝ (iteratedFDeriv ℝ 2 f) p :=
    (h.iteratedFDeriv_right (m := 1) (i := 2) (by norm_num)).differentiableAt (by norm_num)
  rw [iteratedFDeriv_succ_apply_left]
  have t : (Fin.tail ![z, v, u] : Fin 2 → BondField ι) = ![v, u] := by
    funext i
    fin_cases i <;> rfl
  have e0 : (![z, v, u] : Fin 3 → BondField ι) 0 = z := rfl
  rw [e0, t, ← fderiv_apply_multilinear d]
  unfold thirdDerivAlong
  have hev : (fun ζ => secondDerivAlong f ζ u v) =ᶠ[nhds p] fun ζ => iteratedFDeriv ℝ 2 f ζ ![v, u] := by
    filter_upwards [h.eventually (by simp)] with ζ hζ
    exact secondDerivAlong_eq_iteratedFDeriv (hζ.of_le (by norm_num)) u v
  rw [hev.fderiv_eq]
theorem iteratedFDeriv_comp_continuousLinearMap_zero {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (g : A →L[ℝ] BondField ι) (f : BondField ι → ℝ) (k : ℕ) (hf : ContDiffAt ℝ k f 0) (v : Fin k → A) :
    iteratedFDeriv ℝ k (f ∘ g) 0 v = iteratedFDeriv ℝ k f 0 (fun l => g (v l)) := by
  obtain ⟨U, hU, hUo⟩ : ∃ U ∈ nhds (0 : BondField ι), ContDiffOn ℝ k f U := by
    obtain ⟨u, hu, h⟩ := hf.contDiffOn (m := k) le_rfl (by simp)
    exact ⟨u, by simpa using hu, by simpa using h⟩
  obtain ⟨O, hOU, hOo, hO0⟩ := mem_nhds_iff.mp hU
  have hfO : ContDiffOn ℝ k f O := hUo.mono hOU
  have hg0 : g 0 ∈ O := by simpa using hO0
  have hpre : IsOpen (g ⁻¹' O) := hOo.preimage g.continuous
  have h1 := g.iteratedFDerivWithin_comp_right hfO hOo.uniqueDiffOn hpre.uniqueDiffOn hg0
    (i := k) le_rfl
  have e1 : iteratedFDerivWithin ℝ k (f ∘ g) (g ⁻¹' O) 0 = iteratedFDeriv ℝ k (f ∘ g) 0 :=
    iteratedFDerivWithin_of_isOpen k hpre (by simpa using hO0)
  have e2 : iteratedFDerivWithin ℝ k f O (g 0) = iteratedFDeriv ℝ k f 0 := by
    rw [map_zero]
    exact iteratedFDerivWithin_of_isOpen k hOo hO0
  rw [← e1, h1, e2]
  rfl
theorem multilinear_two_smul (T : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => BondField ι) ℝ) (c d : ℝ)
    (u v : BondField ι) : T ![c • u, d • v] = c * d * T ![u, v] := by
  have h := T.map_smul_univ ![c, d] ![u, v]
  have e : (fun i => (![c, d] : Fin 2 → ℝ) i • (![u, v] : Fin 2 → BondField ι) i) = ![c • u, d • v] := by
    funext i
    fin_cases i <;> rfl
  rw [e] at h
  rw [h]
  simp [Fin.prod_univ_two]
theorem multilinear_three_smul (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => BondField ι) ℝ) (c d g : ℝ)
    (u v z : BondField ι) : T ![c • u, d • v, g • z] = c * d * g * T ![u, v, z] := by
  have h := T.map_smul_univ ![c, d, g] ![u, v, z]
  have e : (fun i => (![c, d, g] : Fin 3 → ℝ) i • (![u, v, z] : Fin 3 → BondField ι) i) =
      ![c • u, d • v, g • z] := by
    funext i
    fin_cases i <;> rfl
  rw [e] at h
  rw [h]
  simp [Fin.prod_univ_three]
end Calculus
variable {F : BlockFrame}
def bondDirection (b : ↥(chordBonds (finiteCells F))) (e : BondVector) : ChartDirection F :=
  .inl (b.1.1, b.1.2, toImaginary e)
theorem norm_directionVector_bondDirection {b : ↥(chordBonds (finiteCells F))} {e : BondVector}
    (hLC : ImaginaryCoordinatesIsometric) (he : ‖e‖ = 1) : ‖directionVector (bondDirection b e)‖ = 1 := by
  obtain ⟨_, _, hn, _⟩ := hLC
  show ‖toImaginary e‖ = 1
  rw [hn, he]
theorem stepCoordinates_bondVariation (hLC : ImaginaryCoordinatesIsometric) (b : ↥(chordBonds (finiteCells F)))
    (e : BondVector) (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (bondVariation b e : StepVariable (finiteCells F)) x i =
      directionCoordinate (bondDirection b e) x i := by
  classical
  obtain ⟨_, hsm, _⟩ := hLC
  have z0 : toImaginary (0 : BondVector) = 0 := by
    have := hsm 0 (0 : BondVector)
    simpa using this
  simp only [stepCoordinates, directionCoordinate, bondDirection]
  by_cases h : (x, i) ∈ chordBonds (finiteCells F)
  · rw [dif_pos h]
    by_cases hb : b = ⟨(x, i), h⟩
    · subst hb
      simp [bondVariation]
    · have h1 : ¬ (b.1.1 = x ∧ b.1.2 = i) := fun hh => hb (Subtype.ext (Prod.ext hh.1 hh.2))
      rw [if_neg h1]
      have : (bondVariation b e : StepVariable (finiteCells F)) ⟨(x, i), h⟩ = 0 := by
        simp [bondVariation, Pi.single_apply, Ne.symm hb]
      rw [this, z0]
  · rw [dif_neg h]
    have h1 : ¬ (b.1.1 = x ∧ b.1.2 = i) := fun hh => h (by
      have : (x, i) = b.1 := Prod.ext hh.1.symm hh.2.symm
      rw [this]
      exact b.2)
    rw [if_neg h1]
def stepCoordinatesLinear (hLC : ImaginaryCoordinatesIsometric) (x : F.Site F.depth) (i : Fin 4) :
    StepVariable (finiteCells F) →ₗ[ℝ] imaginaryQuaternions where
  toFun η := stepCoordinates η x i
  map_add' η ζ := by
    classical
    obtain ⟨ha, _⟩ := hLC
    simp only [stepCoordinates]
    split_ifs
    · exact ha _ _
    · simp
  map_smul' c η := by
    classical
    obtain ⟨_, hs, _⟩ := hLC
    simp only [stepCoordinates, RingHom.id_apply]
    split_ifs
    · exact hs _ _
    · simp
theorem chartRestriction_bondDirection (hLC : ImaginaryCoordinatesIsometric) (a : ℝ)
    (p : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    {k : ℕ} (bs : Fin k → ↥(chordBonds (finiteCells F))) (es : Fin k → BondVector) (σ : Fin k → ℝ) :
    chartRestriction a p V (fun l => bondDirection (bs l) (es l)) σ =
      chartedEnergyAt a p V (∑ l, σ l • (bondVariation (bs l) (es l) : StepVariable (finiteCells F))) := by
  have e1 : ∀ x i, ∑ l, σ l • directionCoordinate (bondDirection (bs l) (es l)) x i =
      stepCoordinates (∑ l, σ l • (bondVariation (bs l) (es l) : StepVariable (finiteCells F))) x i :=
      fun x i => by
    have := map_sum (stepCoordinatesLinear hLC x i)
      (fun l => σ l • (bondVariation (bs l) (es l) : StepVariable (finiteCells F))) Finset.univ
    refine Eq.trans ?_ this.symm
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul]
    show _ = σ l • stepCoordinates (bondVariation (bs l) (es l) : StepVariable (finiteCells F)) x i
    rw [stepCoordinates_bondVariation hLC]
  have e2 : leftTranslate (fun y i => ∑ l, σ l • directionMove (bondDirection (bs l) (es l)) y i) V = V := by
    funext y i
    have : ∑ l, σ l • directionMove (bondDirection (bs l) (es l)) y i = 0 :=
      Finset.sum_eq_zero fun l _ => by simp [directionMove, bondDirection]
    simp only [leftTranslate, this]
    have h0 : expUnit 0 = 1 := by
      apply Subtype.ext
      simp [expUnit]
    rw [h0, one_mul]
  unfold chartRestriction chartedEnergyAt
  rw [e2]
  simp only [e1]
def chartCoordinatesLinear (hLC : ImaginaryCoordinatesIsometric) (F : BlockFrame) :
    StepVariable (finiteCells F) →ₗ[ℝ] (Fin (chartDimension F) → ℝ) where
  toFun ζ := chartCoordinates (stepCoordinates ζ) (fun _ _ => 0)
  map_add' η ζ := by
    funext n
    simp only [chartCoordinates, Pi.add_apply]
    rcases (chartCoordinateEquiv F).symm n with p | p
    · show imaginaryCoord p.2 _ = imaginaryCoord p.2 _ + imaginaryCoord p.2 _
      rw [← map_add]
      congr 1
      exact (stepCoordinatesLinear hLC _ _).map_add η ζ
    · show imaginaryCoord p.2 0 = imaginaryCoord p.2 0 + imaginaryCoord p.2 0
      simp
  map_smul' c ζ := by
    funext n
    simp only [chartCoordinates, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    rcases (chartCoordinateEquiv F).symm n with p | p
    · show imaginaryCoord p.2 _ = c * imaginaryCoord p.2 _
      rw [← smul_eq_mul, ← map_smul]
      congr 1
      exact (stepCoordinatesLinear hLC _ _).map_smul c ζ
    · show imaginaryCoord p.2 0 = c * imaginaryCoord p.2 0
      simp
theorem chartedEnergyAt_eq_chartRestriction (hLC : ImaginaryCoordinatesIsometric)
    (hCE : ChartedEnergyInCoordinates) (a : ℝ)
    (p : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top) (hodd : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) (ζ : StepVariable (finiteCells F)) :
    chartedEnergyAt a p V ζ = chartRestriction a p V (chartDirections F) (chartCoordinatesLinear hLC F ζ) := by
  have h := (hCE F a p (stepCoordinates ζ) V (fun _ _ => 0) hodd hs).1
  have e2 : leftTranslate (fun _ _ => (0 : imaginaryQuaternions)) V = V := by
    funext y i
    have h0 : expUnit 0 = 1 := by
      apply Subtype.ext
      simp [expUnit]
    simp only [leftTranslate, h0, one_mul]
  rw [e2] at h
  exact h.symm
theorem contDiffAt_chartedEnergyAt (hLC : ImaginaryCoordinatesIsometric) (hCE : ChartedEnergyInCoordinates)
    (a : ℝ) (p : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (hodd : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (hA : AnalyticAt ℝ (chartRestriction a p V (chartDirections F)) 0) (n : ℕ) :
    ContDiffAt ℝ n (chartedEnergyAt a p V) 0 := by
  have e : chartedEnergyAt a p V =
      chartRestriction a p V (chartDirections F) ∘ (chartCoordinatesLinear hLC F).toContinuousLinearMap := by
    funext ζ
    exact chartedEnergyAt_eq_chartRestriction hLC hCE a p V hodd hs ζ
  rw [e]
  refine ContDiffAt.comp 0 ?_ (ContinuousLinearMap.contDiff _).contDiffAt
  simpa using hA.contDiffAt
def bondVariationSum {k : ℕ} (bs : Fin k → ↥(chordBonds (finiteCells F))) (es : Fin k → BondVector) :
    (Fin k → ℝ) →L[ℝ] StepVariable (finiteCells F) :=
  ∑ l, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) l).smulRight
    (bondVariation (bs l) (es l) : StepVariable (finiteCells F))
theorem bondVariationSum_apply {k : ℕ} (bs : Fin k → ↥(chordBonds (finiteCells F))) (es : Fin k → BondVector)
    (σ : Fin k → ℝ) :
    bondVariationSum bs es σ = ∑ l, σ l • (bondVariation (bs l) (es l) : StepVariable (finiteCells F)) := by
  simp [bondVariationSum]
theorem bondVariationSum_single {k : ℕ} (bs : Fin k → ↥(chordBonds (finiteCells F))) (es : Fin k → BondVector)
    (l : Fin k) : bondVariationSum bs es (Pi.single l 1) = bondVariation (bs l) (es l) := by
  classical
  rw [bondVariationSum_apply, Finset.sum_eq_single l]
  · simp
  · intro j _ hj
    simp [Pi.single_apply, hj]
  · simp
theorem chartMixedDeriv_eq_iteratedFDeriv (hLC : ImaginaryCoordinatesIsometric) (a : ℝ)
    (p : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    {k : ℕ} (bs : Fin k → ↥(chordBonds (finiteCells F))) (es : Fin k → BondVector)
    (hf : ContDiffAt ℝ k (chartedEnergyAt a p V) 0) :
    chartMixedDeriv a p V (fun l => bondDirection (bs l) (es l)) =
      iteratedFDeriv ℝ k (chartedEnergyAt a p V) 0 (fun l => bondVariation (bs l) (es l)) := by
  have e : chartRestriction a p V (fun l => bondDirection (bs l) (es l)) =
      chartedEnergyAt a p V ∘ bondVariationSum bs es := by
    funext σ
    rw [chartRestriction_bondDirection hLC, Function.comp, bondVariationSum_apply]
  unfold chartMixedDeriv
  rw [e, iteratedFDeriv_comp_continuousLinearMap_zero _ _ k hf]
  simp only [bondVariationSum_single]
theorem exists_unit_smul (e : BondVector) : ∃ u : BondVector, ‖u‖ = 1 ∧ e = ‖e‖ • u := by
  by_cases h : e = 0
  · refine ⟨EuclideanSpace.single 0 1, by simp, by simp [h]⟩
  · have hn : ‖e‖ ≠ 0 := norm_ne_zero_iff.2 h
    refine ⟨‖e‖⁻¹ • e, ?_, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm]
      field_simp
    · rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
theorem bondVariation_smul {ι : Type} [DecidableEq ι] (b : ι) (c : ℝ) (u : BondVector) :
    (bondVariation b (c • u) : BondField ι) = c • bondVariation b u := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LocalMeans.bondVariation_smul <;> assumption
theorem secondDerivAlong_shift {ι : Type} [Fintype ι] {A G : BondField ι → ℝ} {η : BondField ι}
    (h : ∀ ζ, A ζ = G (η + ζ)) (ζ u v : BondField ι) :
    secondDerivAlong A ζ u v = secondDerivAlong G (η + ζ) u v := by
  have e : A = fun ζ => G (η + ζ) := funext h
  have hf : ∀ ζ, fderiv ℝ A ζ = fderiv ℝ G (η + ζ) := fun ζ => by
    rw [e]
    exact fderiv_comp_add_left η
  unfold secondDerivAlong
  have e2 : (fun ξ => fderiv ℝ A ξ u) = fun ξ => (fun y => fderiv ℝ G y u) (η + ξ) := by
    funext ξ
    rw [hf]
  rw [e2]
  exact congrArg (fun T => T v) (fderiv_comp_add_left (𝕜 := ℝ) (f := fun y => fderiv ℝ G y u) (x := ζ) η)
theorem thirdDerivAlong_shift {ι : Type} [Fintype ι] {A G : BondField ι → ℝ} {η : BondField ι}
    (h : ∀ ζ, A ζ = G (η + ζ)) (ζ u v z : BondField ι) :
    thirdDerivAlong A ζ u v z = thirdDerivAlong G (η + ζ) u v z := by
  unfold thirdDerivAlong
  have e2 : (fun ξ => secondDerivAlong A ξ u v) = fun ξ => (fun y => secondDerivAlong G y u v) (η + ξ) := by
    funext ξ
    exact secondDerivAlong_shift h ξ u v
  rw [e2]
  exact congrArg (fun T => T z)
    (fderiv_comp_add_left (𝕜 := ℝ) (f := fun y => secondDerivAlong G y u v) (x := ζ) η)
theorem chartedSlope_eq_fderiv (hLC : ImaginaryCoordinatesIsometric) (a : ℝ)
    (p : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (b : ↥(chordBonds (finiteCells F))) (e : BondVector) (hd : DifferentiableAt ℝ (chartedEnergyAt a p V) 0) :
    chartedSlope a p V b.1 (toImaginary e) = fderiv ℝ (chartedEnergyAt a p V) 0 (bondVariation b e) := by
  classical
  have hline : (fun u : ℝ => chartedEnergy a (Function.update p b.1.1 (Function.update (p b.1.1) b.1.2
      (p b.1.1 b.1.2 + u • toImaginary e))) V) =
      fun u : ℝ => chartedEnergyAt a p V (u • (bondVariation b e : StepVariable (finiteCells F))) := by
    funext u
    unfold chartedEnergyAt
    congr 1
    funext x i
    have h1 : stepCoordinates (u • (bondVariation b e : StepVariable (finiteCells F))) x i =
        u • directionCoordinate (bondDirection b e) x i := by
      have := (stepCoordinatesLinear hLC x i).map_smul u (bondVariation b e : StepVariable (finiteCells F))
      refine Eq.trans this ?_
      congr 1
      exact stepCoordinates_bondVariation hLC b e x i
    rw [h1]
    simp only [directionCoordinate, bondDirection]
    by_cases hx : b.1.1 = x
    · subst hx
      by_cases hi : b.1.2 = i
      · subst hi
        simp
      · have : ¬ i = b.1.2 := fun h => hi h.symm
        simp [Function.update_of_ne this, hi]
    · have : ¬ x = b.1.1 := fun h => hx h.symm
      simp [Function.update_of_ne this, hx]
  unfold chartedSlope
  rw [hline]
  have h1 : HasDerivAt (fun u : ℝ => u • (bondVariation b e : StepVariable (finiteCells F)))
      (bondVariation b e) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (bondVariation b e : StepVariable (finiteCells F))
  have h2 : HasFDerivAt (chartedEnergyAt a p V) (fderiv ℝ (chartedEnergyAt a p V) 0)
      ((fun u : ℝ => u • (bondVariation b e : StepVariable (finiteCells F))) 0) := by
    simpa using hd.hasFDerivAt
  exact (h2.comp_hasDerivAt (0 : ℝ) h1).deriv
end ChartedEnergyLocal
open ChartedEnergyLocal in
theorem chartEnergyDerivBounds_of_kernelBound (hK : ChartEnergyKernelBound)
    (hCE : ChartedEnergyInCoordinates) (hLC : ImaginaryCoordinatesIsometric) :
    ChartEnergyDerivBounds := by
  intro a L c ha hodd hL hc
  obtain ⟨Ck, hCk, hker⟩ := hK a L c ha hodd hL hc
  refine ⟨Ck 2 + Ck 3, add_pos (hCk 2) (hCk 3), ?_⟩
  intro F w η V htorus hsm
  obtain ⟨hFL, n, hn, hside⟩ := htorus
  have hoddF : Odd F.blockSide := hFL ▸ hodd
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by rw [hside i]; omega
  have hA := (hker F (shiftCoordinates w η) V ⟨hFL, n, hn, hside⟩ hsm (chartDimension F) (chartDirections F)).1
  have hcd : ∀ n : ℕ, ContDiffAt ℝ n (chartedEnergyAt a (shiftCoordinates w η) V) 0 := fun n =>
    contDiffAt_chartedEnergyAt hLC hCE a _ V hoddF hs hA n
  have hmv := hLC.2.2.2.2.1
  have hshift : ∀ ζ, chartedEnergyAt a (shiftCoordinates w η) V ζ = chartedEnergyAt a w V (η + ζ) := fun ζ => by
    show chartedEnergy a (shiftCoordinates (shiftCoordinates w η) ζ) V =
      chartedEnergy a (shiftCoordinates w (η + ζ)) V
    rw [hmv]
  have h0 : ∀ z : StepVariable (finiteCells F), η + z - η = z := fun z => by abel
  have hfd : fderiv ℝ (chartedEnergyAt a w V) η = fderiv ℝ (chartedEnergyAt a (shiftCoordinates w η) V) 0 := by
    have e : chartedEnergyAt a (shiftCoordinates w η) V = fun ζ => chartedEnergyAt a w V (η + ζ) := funext hshift
    rw [e, fderiv_comp_add_left, add_zero]
  have hdiff : DifferentiableAt ℝ (chartedEnergyAt a (shiftCoordinates w η) V) 0 :=
    (hcd 1).differentiableAt (by norm_num)
  have hS2 : ∀ u v, secondDerivAlong (chartedEnergyAt a w V) η u v =
      secondDerivAlong (chartedEnergyAt a (shiftCoordinates w η) V) 0 u v :=
    fun u v => by
    have := secondDerivAlong_shift hshift 0 u v
    rw [add_zero] at this
    exact this.symm
  have hS3 : ∀ u v z, thirdDerivAlong (chartedEnergyAt a w V) η u v z =
      thirdDerivAlong (chartedEnergyAt a (shiftCoordinates w η) V) 0 u v z :=
    fun u v z => by
    have := thirdDerivAlong_shift hshift 0 u v z
    rw [add_zero] at this
    exact this.symm
  have hδ : 0 ≤ c.δ₁ := hc.positivity.1.le
  refine ⟨?_, fun b e => ?_, fun b b' e e' => ?_, fun b b' b'' e e' e'' => ?_⟩
  · have e : chartedEnergyAt a w V = fun y => chartedEnergyAt a (shiftCoordinates w η) V (y - η) := by
      funext y
      rw [hshift]
      congr 1
      abel
    rw [e]
    refine ContDiffAt.comp η (g := chartedEnergyAt a (shiftCoordinates w η) V) (f := fun y => y - η) ?_
      (by fun_prop)
    simpa using hcd 3
  · rw [hfd]
    exact chartedSlope_eq_fderiv hLC a _ V b e hdiff
  · obtain ⟨u, hu, hue⟩ := exists_unit_smul e
    obtain ⟨u', hu', hue'⟩ := exists_unit_smul e'
    have hk := (hker F (shiftCoordinates w η) V ⟨hFL, n, hn, hside⟩ hsm 2
      (fun l => bondDirection (![b', b] l) (![u', u] l))).2 (le_refl 2) (fun l => by
        fin_cases l
        · exact norm_directionVector_bondDirection hLC hu'
        · exact norm_directionVector_bondDirection hLC hu)
    have hke := chartMixedDeriv_eq_iteratedFDeriv hLC a (shiftCoordinates w η) V ![b', b] ![u', u] (hcd 2)
    have hvec : (fun l => (bondVariation (![b', b] l) (![u', u] l) : StepVariable (finiteCells F))) =
        ![bondVariation b' u', bondVariation b u] := by
      funext l
      fin_cases l <;> rfl
    rw [hvec] at hke
    have hval : secondDerivAlong (chartedEnergyAt a (shiftCoordinates w η) V) 0 (bondVariation b u)
        (bondVariation b' u') =
        chartMixedDeriv a (shiftCoordinates w η) V (fun l => bondDirection (![b', b] l) (![u', u] l)) := by
      rw [hke]
      exact secondDerivAlong_eq_iteratedFDeriv (hcd 2) _ _
    have hdiam : chordBondDist F b b' ≤ directionDiameter (fun l => bondDirection (![b', b] l) (![u', u] l)) := by
      unfold chordBondDist directionDiameter
      have h1 := Finset.le_sup (f := fun l' : Fin 2 => cellSupDist
        (directionCell ((fun l => bondDirection (![b', b] l) (![u', u] l)) 1))
        (directionCell ((fun l => bondDirection (![b', b] l) (![u', u] l)) l'))) (Finset.mem_univ 0)
      have h2 := Finset.le_sup (f := fun l : Fin 2 => Finset.univ.sup fun l' : Fin 2 => cellSupDist
        (directionCell ((fun l => bondDirection (![b', b] l) (![u', u] l)) l))
        (directionCell ((fun l => bondDirection (![b', b] l) (![u', u] l)) l'))) (Finset.mem_univ 1)
      exact_mod_cast h1.trans h2
    have hexp : Real.exp (-(c.δ₁ * directionDiameter (fun l => bondDirection (![b', b] l) (![u', u] l)))) ≤
        Real.exp (-(c.δ₁ * chordBondDist F b b')) :=
      Real.exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonneg_left hdiam hδ])
    have hscale : secondDerivAlong (chartedEnergyAt a (shiftCoordinates w η) V) 0 (bondVariation b e)
        (bondVariation b' e') =
        ‖e‖ * ‖e'‖ * secondDerivAlong (chartedEnergyAt a (shiftCoordinates w η) V) 0 (bondVariation b u)
          (bondVariation b' u') := by
      rw [secondDerivAlong_eq_iteratedFDeriv (hcd 2), secondDerivAlong_eq_iteratedFDeriv (hcd 2)]
      conv_lhs => rw [hue, hue', bondVariation_smul, bondVariation_smul]
      rw [multilinear_two_smul]
      ring
    rw [hS2, hscale, hval, abs_mul, abs_of_nonneg (by positivity)]
    have hb := hk.trans (mul_le_mul_of_nonneg_left hexp (hCk 2).le)
    have h3 : Ck 2 * Real.exp (-(c.δ₁ * chordBondDist F b b')) ≤
        (Ck 2 + Ck 3) * Real.exp (-(c.δ₁ * chordBondDist F b b')) :=
      mul_le_mul_of_nonneg_right (by linarith [hCk 3]) (Real.exp_pos _).le
    have h4 := hb.trans h3
    calc _ ≤ ‖e‖ * ‖e'‖ * ((Ck 2 + Ck 3) * Real.exp (-(c.δ₁ * chordBondDist F b b'))) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = _ := by ring
  · obtain ⟨u, hu, hue⟩ := exists_unit_smul e
    obtain ⟨u', hu', hue'⟩ := exists_unit_smul e'
    obtain ⟨u'', hu'', hue''⟩ := exists_unit_smul e''
    have hk := (hker F (shiftCoordinates w η) V ⟨hFL, n, hn, hside⟩ hsm 3
      (fun l => bondDirection (![b'', b', b] l) (![u'', u', u] l))).2 (by norm_num) (fun l => by
        fin_cases l
        · exact norm_directionVector_bondDirection hLC hu''
        · exact norm_directionVector_bondDirection hLC hu'
        · exact norm_directionVector_bondDirection hLC hu)
    have hke := chartMixedDeriv_eq_iteratedFDeriv hLC a (shiftCoordinates w η) V ![b'', b', b] ![u'', u', u]
      (hcd 3)
    have hvec : (fun l => (bondVariation (![b'', b', b] l) (![u'', u', u] l) : StepVariable (finiteCells F))) =
        ![bondVariation b'' u'', bondVariation b' u', bondVariation b u] := by
      funext l
      fin_cases l <;> rfl
    rw [hvec] at hke
    have hval : thirdDerivAlong (chartedEnergyAt a (shiftCoordinates w η) V) 0 (bondVariation b u)
        (bondVariation b' u') (bondVariation b'' u'') =
        chartMixedDeriv a (shiftCoordinates w η) V
          (fun l => bondDirection (![b'', b', b] l) (![u'', u', u] l)) := by
      rw [hke]
      exact thirdDerivAlong_eq_iteratedFDeriv (hcd 3) _ _ _
    have hexp : Real.exp (-(c.δ₁ * directionDiameter
        (fun l => bondDirection (![b'', b', b] l) (![u'', u', u] l)))) ≤ 1 :=
      Real.exp_le_one_iff.2 (by
        have : 0 ≤ c.δ₁ * directionDiameter (fun l => bondDirection (![b'', b', b] l) (![u'', u', u] l)) := by
          positivity
        linarith)
    have hscale : thirdDerivAlong (chartedEnergyAt a (shiftCoordinates w η) V) 0 (bondVariation b e)
        (bondVariation b' e') (bondVariation b'' e'') =
        ‖e‖ * ‖e'‖ * ‖e''‖ *
          thirdDerivAlong (chartedEnergyAt a (shiftCoordinates w η) V) 0 (bondVariation b u)
            (bondVariation b' u') (bondVariation b'' u'') := by
      rw [thirdDerivAlong_eq_iteratedFDeriv (hcd 3), thirdDerivAlong_eq_iteratedFDeriv (hcd 3)]
      conv_lhs => rw [hue, hue', hue'', bondVariation_smul, bondVariation_smul, bondVariation_smul]
      rw [multilinear_three_smul]
      ring
    rw [hS3, hscale, hval, abs_mul, abs_of_nonneg (by positivity)]
    have hb := hk.trans (mul_le_mul_of_nonneg_left hexp (hCk 3).le)
    rw [mul_one] at hb
    have h4 : |chartMixedDeriv a (shiftCoordinates w η) V
        (fun l => bondDirection (![b'', b', b] l) (![u'', u', u] l))| ≤ Ck 2 + Ck 3 := by
      linarith [hCk 2]
    calc _ ≤ ‖e‖ * ‖e'‖ * ‖e''‖ * (Ck 2 + Ck 3) := mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = _ := by ring
end YangMills.Construction.ColdStepAtMirrorFrames
end
