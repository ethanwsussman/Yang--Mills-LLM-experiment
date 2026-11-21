import YangMills.Construction.ColdChainAtEveryLevel.GaugeCovarianceOfAContourProof
import YangMills.Construction.ColdChainAtEveryLevel.PlaquettesNearAPoint
import YangMills.Construction.ColdStepAtMirrorFrames.BlocksCoverTheLevelBelow
import YangMills.Construction.ColdStepAtMirrorFrames.ExponentialOfTheLieAlgebra
import YangMills.Construction.ColdStepAtMirrorFrames.FramesAreSmall
import YangMills.Construction.ColdStepAtMirrorFrames.GaugeOfTheLeastChartForm
import YangMills.Construction.ColdStepAtMirrorFrames.HolonomyIsLipschitz
import YangMills.Construction.ColdStepAtMirrorFrames.MirrorFieldIsCold
import YangMills.Construction.ColdStepAtMirrorFrames.MirrorReadsItsBox
import YangMills.Construction.ColdStepAtMirrorFrames.OneLeastChart
import YangMills.Construction.ColdStepAtMirrorFrames.SitesOfABlock
import YangMills.Construction.ColdStepAtMirrorFrames.TranslationOfTheLeastChart
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
namespace SmallFrames
theorem norm_coe_unit (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
theorem norm_conj_sub_one (h g : UnitQuaternion) :
    ‖((h * g * h⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ = ‖(g : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_conj_sub_one <;> assumption
theorem plaquetteHolonomy_eq {j : ℕ} (X : F.GaugeField j) (x : F.Site j) (μ ν : Fin 4) :
    plaquetteHolonomy X (x, μ, ν) =
      X x μ * X (x + unitStep j μ) ν * (X (x + unitStep j ν) μ)⁻¹ * (X x ν)⁻¹ := by apply _root_.YangMills.Construction.PlaquetteExpansion.plaquetteHolonomy_eq <;> assumption
theorem plaquetteHolonomy_gaugeTransform {j : ℕ} (γ : F.Site j → UnitQuaternion) (X : F.GaugeField j)
    (p : F.Site j × Fin 4 × Fin 4) :
    plaquetteHolonomy (gaugeTransform γ X) p = γ p.1 * plaquetteHolonomy X p * (γ p.1)⁻¹ := by apply _root_.YangMills.Construction.BlockAverages.GaugeCovariance.plaquetteHolonomy_gaugeTransform <;> assumption
theorem isSmallCurvature_gaugeTransform {j : ℕ} {s : ℝ} (γ : F.Site j → UnitQuaternion) {X : F.GaugeField j}
    (hX : IsSmallCurvature s X) : IsSmallCurvature s (gaugeTransform γ X) := by
  intro p hp
  have := hX p hp
  unfold plaquetteDefect at this ⊢
  rw [plaquetteHolonomy_gaugeTransform, norm_conj_sub_one]
  exact this
theorem isSmallCurvature_translateField {j : ℕ} {s : ℝ} (u : F.Site j) {X : F.GaugeField j}
    (hX : IsSmallCurvature s X) : IsSmallCurvature s (translateField u X) := by
  rintro ⟨x, μ, ν⟩ hp
  have := hX (x - u, μ, ν) hp
  unfold plaquetteDefect at this ⊢
  have e : plaquetteHolonomy (translateField u X) (x, μ, ν) = plaquetteHolonomy X (x - u, μ, ν) := by
    simp only [plaquetteHolonomy_eq, translateField]
    have e1 : ∀ v : F.Site j, x + v - u = x - u + v := fun v => by abel
    simp only [e1]
  rw [e]
  exact this
theorem mem_chordBonds_iff (hcover : BlocksCoverLowerLevel) (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i)
    (b : F.Site F.depth × Fin 4) : b ∈ chordBonds (finiteCells F) ↔ ¬ IsAxialTreeBond b := by
  classical
  unfold chordBonds innerBonds
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
  have h := hcover F hL hs
  exact ⟨fun hb => hb.2, fun hb => ⟨⟨h _, h _⟩, hb⟩⟩
theorem norm_chartedField_sub_le (hcover : BlocksCoverLowerLevel)
    (hexp : QuaternionExp.ExpUnitLipschitzInjective)
    (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) (V : F.GaugeField F.top)
    (w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ b ∈ chordBonds (finiteCells F), ‖w b.1 b.2 - w' b.1 b.2‖ ≤ ε) (x : F.Site F.depth) (i : Fin 4) :
    ‖((chartedField w V x i : UnitQuaternion) : ℍ[ℝ]) - ((chartedField w' V x i : UnitQuaternion) : ℍ[ℝ])‖ ≤ ε := by
  classical
  unfold chartedField
  by_cases hc : IsCrossingBond (x, i)
  · simp only [if_pos hc]
    have hb : (x, i) ∈ chordBonds (finiteCells F) :=
      (mem_chordBonds_iff hcover hL hs _).mpr fun ht => ht.1 hc
    have e : ((expUnit (w x i) * V (enclosingCell x) i : UnitQuaternion) : ℍ[ℝ]) -
        ((expUnit (w' x i) * V (enclosingCell x) i : UnitQuaternion) : ℍ[ℝ]) =
        (((expUnit (w x i) : UnitQuaternion) : ℍ[ℝ]) - ((expUnit (w' x i) : UnitQuaternion) : ℍ[ℝ])) *
          ((V (enclosingCell x) i : UnitQuaternion) : ℍ[ℝ]) := by
      simp only [Submonoid.coe_mul, sub_mul]
    rw [e, norm_mul, norm_coe_unit, mul_one]
    have h1 := hexp.1 (w x i) (w' x i)
    have h2 : ‖w x i - w' x i‖ ≤ ε := h (x, i) hb
    exact h1.trans h2
  · simp only [if_neg hc]
    by_cases ht : IsAxialTreeBond (x, i)
    · simp only [if_pos ht, sub_self, norm_zero]
      exact hε
    · simp only [if_neg ht]
      have hb : (x, i) ∈ chordBonds (finiteCells F) := (mem_chordBonds_iff hcover hL hs _).mpr ht
      have h1 := hexp.1 (w x i) (w' x i)
      have h2 : ‖w x i - w' x i‖ ≤ ε := h (x, i) hb
      exact h1.trans h2
theorem bondContour_length_le (L : ℕ) (hL : Odd L) (h : Fin 4 → ℤ) (hh : h ∈ centredCube L)
    (π : Equiv.Perm (Fin 4)) (i : Fin 4) :
    ((bondContour L h π i).length : ℝ) ≤ 5 * L := by
  obtain ⟨k, hk⟩ := hL
  have hLz : (L : ℤ) = 2 * k + 1 := by exact_mod_cast hk
  have hb : ∀ l, (h l).natAbs ≤ k := by
    intro l
    unfold centredCube at hh
    rw [Fintype.mem_piFinset] at hh
    have h1 := Finset.mem_Icc.mp (hh l)
    rw [hLz] at h1
    omega
  have hleg : (axisPath h π).length ≤ 4 * k := by
    unfold axisPath
    simp only [List.length_flatMap, List.length_replicate]
    have e : (List.finRange 4).map (fun x => (h (π x)).natAbs) =
        [(h (π 0)).natAbs, (h (π 1)).natAbs, (h (π 2)).natAbs, (h (π 3)).natAbs] := rfl
    rw [e]
    simp only [List.sum_cons, List.sum_nil]
    have := hb (π 0)
    have := hb (π 1)
    have := hb (π 2)
    have := hb (π 3)
    omega
  have hlen : (bondContour L h π i).length = 2 * (axisPath h π).length + L := by
    simp [bondContour, reversePath]
    ring
  rw [hlen]
  have : 2 * (axisPath h π).length + L ≤ 5 * L := by omega
  exact_mod_cast this
theorem blockSide_odd_and_extent_ge {L : ℕ} (hL : Odd L) (hF : IsBlockTorus L F) :
    Odd F.blockSide ∧ ∀ i, 2 ≤ F.extent i := by
  obtain ⟨hFL, n, hn, hside⟩ := hF
  exact ⟨hFL ▸ hL, fun i => by rw [hside]; omega⟩
theorem minimizingCoordinates_gaugeTransform {a : ℝ} {L : ℕ} {c : ColdChainParameters} (hc : c.Admissible a L) (hL : Odd L)
    (hOne : MinimizingChartUnique) (hGa : MinimizingChartGaugeCovariant) (hF : IsBlockTorus L F) {s : ℝ}
    (hs0 : 0 < s) (hs : s ≤ c.s₀) (V : F.GaugeField F.top) (hV : IsSmallCurvature s V)
    (γ : F.Cell → UnitQuaternion) :
    minimizingCoordinates a (finiteCells F) (gaugeTransform γ V) c.ρA =
      fun x i => adjointMap (γ (enclosingCell x)) (minimizingCoordinates a (finiteCells F) V c.ρA x i) := by
  obtain ⟨hOdd, hs2⟩ := blockSide_odd_and_extent_ge hL hF
  have hσA : s ≤ c.σA := by
    have h1 := hc.inequalities.2.2.1
    linarith
  have hVg := isSmallCurvature_gaugeTransform γ hV
  have hl := (hc.classical.2 F s V hF hs0 hs hV).1
  have hl' := (hc.classical.2 F s (gaugeTransform γ V) hF hs0 hs hVg).1
  have hch' := hc.estimates F s (gaugeTransform γ V) hF hs0 hσA hVg
  have hg := hGa F a c.ρA V _ γ hOdd hs2 hl
  exact ((hOne F a c.ρA (c.N 0) s (gaugeTransform γ V) _ hOdd hs2 hc.classical.1.2.1 hch'.minimizer hl').1 _ hg).symm
theorem minimizingCoordinates_translateField {a : ℝ} {L : ℕ} {c : ColdChainParameters} (hc : c.Admissible a L) (hL : Odd L)
    (hOne : MinimizingChartUnique) (hTr : MinimizingChartTranslation) (hF : IsBlockTorus L F) {s : ℝ}
    (hs0 : 0 < s) (hs : s ≤ c.s₀) (V : F.GaugeField F.top) (hV : IsSmallCurvature s V) (h : F.Cell) :
    minimizingCoordinates a (finiteCells F) (translateField h V) c.ρA =
      fun x i => minimizingCoordinates a (finiteCells F) V c.ρA (x - cellCentre F.depth h) i := by
  obtain ⟨hOdd, hs2⟩ := blockSide_odd_and_extent_ge hL hF
  have hσA : s ≤ c.σA := by
    have h1 := hc.inequalities.2.2.1
    linarith
  have hVg := isSmallCurvature_translateField h hV
  have hl := (hc.classical.2 F s V hF hs0 hs hV).1
  have hl' := (hc.classical.2 F s (translateField h V) hF hs0 hs hVg).1
  have hch' := hc.estimates F s (translateField h V) hF hs0 hσA hVg
  have hg := hTr F a c.ρA V _ h hOdd hs2 hl
  exact ((hOne F a c.ρA (c.N 0) s (translateField h V) _ hOdd hs2 hc.classical.1.2.1 hch'.minimizer hl').1 _ hg).symm
theorem reflectedGauge_zero (m : ℕ) (y : F.Cell) (γ : F.Cell → UnitQuaternion) :
    reflectedGauge m y γ (0 : (reflectedFrame F m).Cell) = γ y := by
  unfold reflectedGauge
  have e : (fun l => reflectCoord m (((0 : (reflectedFrame F m).Cell) l).valMinAbs)) = 0 := by
    funext l
    simp [reflectCoord]
  rw [e]
  have e2 : (siteOfCoords F.top (0 : Fin 4 → ℤ) : F.Cell) = 0 := by
    funext i
    simp [siteOfCoords]
  rw [e2, add_zero]
theorem cellCentre_zero {j : ℕ} : (cellCentre j (0 : F.Cell) : F.Site j) = 0 := by
  funext i
  simp [cellCentre, siteOfCoords, siteCoords]
end SmallFrames
open SmallFrames in
theorem frames_small (hcover : BlocksCoverLowerLevel) (hS : SiteDecomposition)
    (hMF : ReflectedFrameChainBounds) (hOne : MinimizingChartUnique)
    (hGa' : MinimalActionGaugeCovariance) (hTr' : TranslationOfMinimizingChart)
    (hexp : QuaternionExp.ExpUnitLipschitzInjective) (hhol : PathHolonomyLipschitz)
    (hMR : reflectedFieldReadsBox) (hcoldM : ReflectedFieldSmallCurvature) :
    framesSmallStatement := by
  classical
  have hGa : MinimizingChartGaugeCovariant := hGa'.2
  have hTr : MinimizingChartTranslation := hTr'.2.2
  have hSh : SiteTranslationByCell := hTr'.2.1
  have hMG : ReflectedFieldOfGaugedTop := hMR.2.1
  have hMS : ReflectedFieldOfTranslatedCentre := hMR.2.2
  intro a L c ha hL hc
  obtain ⟨⟨hρ0, hρ1, hs₀, hδ, hκ, hK, hC, hKk⟩, hcl⟩ := hc.classical
  have hδκ : c.δ₂ / 4 ≤ c.κ₂ := by linarith
  have hKs0 : 0 < c.Kk 1 + c.Kk 2 + c.Kk 3 := by
    have a1 := hKk 1
    have a2 := hKk 2
    have a3 := hKk 3
    linarith
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = 2 * c.C + 5 * L + 16 ^ 3 * (c.Kk 1 + c.Kk 2 + c.Kk 3) + 2 := ⟨_, rfl⟩
  have hC2 : 2 ≤ C := by
    rw [hCdef]
    have := mul_pos (by norm_num : (0 : ℝ) < 16 ^ 3) hKs0
    linarith
  have hCpos : 0 < C := by linarith
  refine ⟨C, min (min 1 (4 / 5 * c.s₀)) (c.ρA / (2 * C)), by linarith, ?_, ?_⟩
  · refine lt_min (lt_min one_pos (by positivity)) (by positivity)
  intro σ m F V hσ hσ₁ hm hgap hF hV
  have hσ1 : σ ≤ 1 := hσ₁.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hσs : 5 / 4 * σ ≤ c.s₀ := by
    have : σ ≤ 4 / 5 * c.s₀ := hσ₁.trans ((min_le_left _ _).trans (min_le_right _ _))
    linarith
  have hσρ : σ ≤ c.ρA / (2 * C) := hσ₁.trans (min_le_right _ _)
  have hspos : 0 < 5 / 4 * σ := by positivity
  have hσA : 5 / 4 * σ ≤ c.σA := by
    have h1 := hc.inequalities.2.2.1
    linarith
  obtain ⟨hOdd, hs2⟩ := blockSide_odd_and_extent_ge hL hF
  have hs0 : ∀ i, 0 < F.extent i := fun i => by have := hs2 i; omega
  obtain ⟨hleast, hsm, hdec, _⟩ := hcl F (5 / 4 * σ) V hF hspos hσs hV
  have hclause := hc.estimates F (5 / 4 * σ) V hF hspos hσA hV
  have hmirror : (∀ i, 4 * m + 5 < F.extent i) → ReflectedFrameBounds a σ c m V := fun hbig =>
    hMF a L c ha hL hc F m σ V hF hm hσ hσs hbig hV
  have hOneC := (hOne F a c.ρA (c.N 0) (5 / 4 * σ) V _ hOdd hs2 hρ1 hclause.minimizer hleast).2
  have hwc : ∀ p : F.Site F.depth × Fin 4 × Fin 4, p.2.1 < p.2.2 →
      plaquetteDefect (chartedField (minimizingCoordinates a (finiteCells F) V c.ρA) V) p < 5 / 4 * σ / 8 := by
    intro p hp
    refine hOneC p ?_
    unfold innerPlaquettes
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
    exact ⟨hcover F hOdd hs0 _, hp, fun x _ => hcover F hOdd hs0 x⟩
  have hnearcold : ∀ w : F.Site F.depth → Fin 4 → imaginaryQuaternions, (∀ b ∈ chordBonds (finiteCells F),
      ‖w b.1 b.2 - minimizingCoordinates a (finiteCells F) V c.ρA b.1 b.2‖ ≤ σ / 1024) →
      IsSmallCurvature (41 / 64 * σ) (chartedField w V) := by
    intro w hw p hp
    have hn := norm_chartedField_sub_le hcover hexp hOdd hs0 V w _ (σ / 1024) (by positivity) hw
    have h1 := hhol F F.depth _ _ _ hn p.1 [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)]
    have h2 := hwc p hp
    unfold plaquetteDefect at h2 ⊢
    unfold plaquetteHolonomy at h2 ⊢
    have h3 := norm_sub_le_norm_sub_add_norm_sub
      (((pathHolonomy (chartedField w V) p.1
        [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] : UnitQuaternion)) : ℍ[ℝ])
      (((pathHolonomy (chartedField (minimizingCoordinates a (finiteCells F) V c.ρA) V) p.1
        [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] : UnitQuaternion)) : ℍ[ℝ]) 1
    simp only [List.length_cons, List.length_nil] at h1
    push_cast at h1
    linarith
  refine ⟨fun flag => ?_, hnearcold⟩
  have hcase : (∀ (b : F.Site F.depth × Fin 4) (V' : F.GaugeField F.top),
      stepFrame flag a c.ρA m b V' = torusCoordinate a c.ρA b V') ∨
      (flag = false ∧ ∀ i, 4 * m + 5 < F.extent i) := by
    by_cases hst : flag = true
    · left
      intro b V'
      simp [stepFrame, hst, torusCoordinate]
    · by_cases hbig : ∀ i, 4 * m + 5 < F.extent i
      · exact Or.inr ⟨by simpa using hst, hbig⟩
      · left
        intro b V'
        simp only [stepFrame, bondFrameCoord, if_neg hbig]
        simp [hst, torusCoordinate]
  have hCf0 : 0 < frameBoundConstant c := by
    unfold frameBoundConstant
    have h1 := hKk 3
    have h2 : 0 < (16 ^ 3 + 1) * (c.Kk 1 + c.Kk 2 + c.Kk 3) := by positivity
    linarith
  obtain ⟨ε, hεdef⟩ : ∃ ε, ε = frameDecayBound (frameBoundConstant c) c.δ₂ m * σ := ⟨_, rfl⟩
  have hε0 : 0 ≤ ε := by
    rw [hεdef]
    unfold frameDecayBound
    positivity
  have hεσ : ε ≤ σ / 1024 := by
    rw [hεdef]
    have h1 := mul_le_mul_of_nonneg_right hgap hσ.le
    have h2 : (2 : ℝ)⁻¹ ^ 10 * σ * σ ≤ (2 : ℝ)⁻¹ ^ 10 * σ * 1 := mul_le_mul_of_nonneg_left hσ1 (by positivity)
    have h3 : (2 : ℝ)⁻¹ ^ 10 * σ * 1 = σ / 1024 := by
      norm_num
      ring
    linarith
  have hF0 : ∀ (b : F.Site F.depth × Fin 4) (V' : F.GaugeField F.top),
      stepFrame false a c.ρA m b V' = bondFrameCoord a c.ρA m b V' :=
    fun b V' => by simp [stepFrame]
  have hclose : (∀ i, 4 * m + 5 < F.extent i) → ∀ b ∈ chordBonds (finiteCells F),
      ‖bondFrameCoord a c.ρA m b V - torusCoordinate a c.ρA b V‖ ≤ ε := by
    intro hbig b hb
    have h1 := ((hmirror hbig).near_minimizer b hb).1
    rw [hεdef]
    rw [Submodule.coe_norm, Submodule.coe_sub]
    exact h1
  have hnearX : (∀ i, 4 * m + 5 < F.extent i) → ∀ (x : F.Site F.depth) (i : Fin 4),
      ‖((chartedField (frameCoordField false a c.ρA m V) V x i : UnitQuaternion) : ℍ[ℝ]) -
        ((chartedField (minimizingCoordinates a (finiteCells F) V c.ρA) V x i : UnitQuaternion) : ℍ[ℝ])‖ ≤ ε := by
    intro hbig x i
    refine norm_chartedField_sub_le hcover hexp hOdd hs0 V _ _ ε hε0 (fun b hb => ?_) x i
    have h1 := hclose hbig b hb
    rw [← hF0] at h1
    exact h1
  have hM : IsBlockTorus L (reflectedFrame F m) := ⟨hF.1, 4 * m, by omega, fun _ => rfl⟩
  have hMs2 : ∀ i, 2 ≤ (reflectedFrame F m).extent i := fun i => by
    change 2 ≤ 4 * m
    omega
  have hOddM : Odd (reflectedFrame F m).blockSide := hOdd
  have hcell0 : ∀ b : F.Site F.depth × Fin 4,
      enclosingCell (reflectedBond m b).1 = (0 : (reflectedFrame F m).Cell) := by
    intro b
    have ho := ((hS F hOdd hs2).2.1 b.1).2
    have h1 := ((hS (reflectedFrame F m) hOddM hMs2).1 0 (cellOffset b.1) ho).1
    rw [cellCentre_zero, zero_add] at h1
    exact h1
  have hfc : (∀ i, 4 * m + 5 < F.extent i) → ∀ (b : F.Site F.depth × Fin 4) (V' : F.GaugeField F.top),
      bondFrameCoord a c.ρA m b V' =
        minimizingBondCoordinate a c.ρA (finiteCells (reflectedFrame F m)) (reflectedBond m b)
          (reflectedField m (enclosingCell b.1) V') := by
    intro hbig b V'
    simp only [bondFrameCoord, if_pos hbig, reflectedBondCoord]
  have hsize : ∀ b ∈ chordBonds (finiteCells F), ‖stepFrame flag a c.ρA m b V‖ ≤ C * σ := by
    intro b hb
    have hh := hsm.1 b hb
    have h2 : c.C * (5 / 4 * σ) + σ / 1024 ≤ C * σ := by
      rw [hCdef]
      have h3 : 0 ≤ 5 * (L : ℝ) * σ := by positivity
      have h4 : 0 ≤ 16 ^ 3 * (c.Kk 1 + c.Kk 2 + c.Kk 3) * σ := by positivity
      have h5 : 0 ≤ c.C * σ := by positivity
      nlinarith
    rcases hcase with hW | ⟨hst, hbig⟩
    · rw [hW]
      refine hh.trans ?_
      linarith
    · subst hst
      rw [hF0]
      refine (norm_le_norm_add_norm_sub' _ (torusCoordinate a c.ρA b V)).trans ?_
      have := hclose hbig b hb
      linarith
  have hhigh : ∀ b ∈ chordBonds (finiteCells F), ∀ (k : ℕ) (e : Fin k → F.Site F.top × Fin 4)
      (X : Fin k → imaginaryQuaternions), 1 ≤ k → AreUnitVectors X →
        ‖bondDeriv (stepFrame flag a c.ρA m b) V e X‖ ≤
        16 ^ k * c.Kk k * Real.exp (-(c.κ₂ * bondListDistance (enclosingCell b.1) e)) := by
    intro b hb k e X hk hX
    rcases hcase with hW | ⟨hst, hbig⟩
    · have hfun : stepFrame flag a c.ρA m b = torusCoordinate a c.ρA b := funext (hW b)
      rw [hfun]
      refine (hdec b hb k e X hk hX).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      have h1 : (1 : ℝ) ≤ 16 ^ k := one_le_pow₀ (by norm_num)
      exact le_mul_of_one_le_left (hKk k).le h1
    · subst hst
      have hfun : stepFrame false a c.ρA m b = bondFrameCoord a c.ρA m b := funext (hF0 b)
      rw [hfun]
      exact (hmirror hbig).deriv_bound b hb k e X hk hX
  refine
    { minimizer_exists := fun hbig y => (hmirror hbig).minimizing y
      norm_le := hsize
      norm_add_le := ?_
      holonomy_ratio := ?_
      small_curvature := ?_
      deriv_decay := ?_
      deriv_bound := hhigh
      deriv_eq_zero_off_box := ?_
      analytic := ?_
      gauge_covariant := ?_
      translation_invariant := ?_ }
  · intro b hb
    have h1 := hsize b hb
    have h2 : 2 * C * σ ≤ c.ρA := by
      have h3 := (le_div_iff₀ (by positivity : 0 < 2 * C)).mp hσρ
      linarith
    have h4 : σ / 64 ≤ C * σ := by nlinarith
    linarith
  · intro e h π hh
    have hb0 := (hsm.2 e h π hh).1
    rcases hcase with hW | ⟨hst, hbig⟩
    · have hfun : frameCoordField flag a c.ρA m V = minimizingCoordinates a (finiteCells F) V c.ρA := by
        funext x i
        simp only [frameCoordField, hW]
        rfl
      rw [hfun]
      refine hb0.trans ?_
      have h3 : 0 ≤ 5 * (L : ℝ) * σ := by positivity
      have h4 : 0 ≤ 16 ^ 3 * (c.Kk 1 + c.Kk 2 + c.Kk 3) * σ := by positivity
      have h5 : 0 ≤ c.C * σ := by positivity
      rw [hCdef]
      nlinarith
    · subst hst
      have h1 := hhol F F.depth _ _ ε (hnearX hbig) (refineSite e.1) (bondContour F.blockSide h π e.2)
      have h2 := bondContour_length_le F.blockSide hOdd h hh π e.2
      have h3 : ‖contourHolonomyDefect (chartedField (frameCoordField false a c.ρA m V) V) V e h π -
          contourHolonomyDefect (torusMinimizingField a c.ρA V) V e h π‖ ≤ 5 * F.blockSide * ε := by
        unfold contourHolonomyDefect torusMinimizingField
        simp only [Submonoid.coe_mul]
        rw [← sub_mul, norm_mul, norm_coe_unit, mul_one]
        exact h1.trans (mul_le_mul_of_nonneg_right h2 hε0)
      have h4 := norm_sub_le_norm_sub_add_norm_sub
        (contourHolonomyDefect (chartedField (frameCoordField false a c.ρA m V) V) V e h π)
        (contourHolonomyDefect (torusMinimizingField a c.ρA V) V e h π) 1
      refine h4.trans ?_
      have hFL : (F.blockSide : ℝ) = L := by rw [hF.1]
      rw [hFL] at h3
      have h5 : 5 * (L : ℝ) * ε ≤ 5 * L * σ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have h6 : 0 ≤ 16 ^ 3 * (c.Kk 1 + c.Kk 2 + c.Kk 3) * σ := by positivity
      have h7 : 0 ≤ c.C * σ := by positivity
      rw [hCdef]
      nlinarith
  · rcases hcase with hW | ⟨hst, hbig⟩
    · have hfun : frameCoordField flag a c.ρA m V = minimizingCoordinates a (finiteCells F) V c.ρA := by
        funext x i
        simp only [frameCoordField, hW]
        rfl
      rw [hfun]
      intro p hp
      refine (hwc p hp).trans_le ?_
      split_ifs <;> linarith
    · subst hst
      have hc0 : ((if false = true then (5 / 8 : ℝ) else 41 / 64) * σ) = 41 / 64 * σ := by simp
      rw [hc0]
      refine hnearcold _ fun b hb => ?_
      have h1 := hclose hbig b hb
      rw [← hF0] at h1
      exact h1.trans hεσ
  · intro b hb k e X hk hk3 hX
    refine (hhigh b hb k e X hk hX).trans ?_
    have h1 : (16 : ℝ) ^ k ≤ 16 ^ 3 := pow_le_pow_right₀ (by norm_num) hk3
    have h2 : c.Kk k ≤ c.Kk 1 + c.Kk 2 + c.Kk 3 := by
      have a1 := hKk 1
      have a2 := hKk 2
      have a3 := hKk 3
      interval_cases k <;> linarith
    have h3 : (16 : ℝ) ^ k * c.Kk k ≤ C := by
      calc (16 : ℝ) ^ k * c.Kk k ≤ 16 ^ 3 * (c.Kk 1 + c.Kk 2 + c.Kk 3) :=
            mul_le_mul h1 h2 (hKk k).le (by norm_num)
        _ ≤ C := by
            rw [hCdef]
            have : 0 ≤ c.C := by linarith
            linarith
    have h4 : Real.exp (-(c.κ₂ * bondListDistance (enclosingCell b.1) e)) ≤
        Real.exp (-(c.δ₂ / 4 * bondListDistance (enclosingCell b.1) e)) := by
      apply Real.exp_le_exp.mpr
      have h0 : (0 : ℝ) ≤ bondListDistance (enclosingCell b.1) e := by positivity
      have := mul_le_mul_of_nonneg_right hδκ h0
      linarith
    exact mul_le_mul h3 h4 (Real.exp_pos _).le hCpos.le
  · intro hst hbig b hb k e X hex
    subst hst
    have hfun : stepFrame false a c.ρA m b = bondFrameCoord a c.ρA m b := funext (hF0 b)
    rw [hfun]
    exact (hmirror hbig).deriv_eq_zero_off_box b hb k e X hex
  · intro b hb
    rcases hcase with hW | ⟨hst, hbig⟩
    · have hfun : stepFrame flag a c.ρA m b = torusCoordinate a c.ρA b := funext (hW b)
      rw [hfun]
      exact (hclause.coordinates b hb).1
    · subst hst
      have hfun : stepFrame false a c.ρA m b = bondFrameCoord a c.ρA m b := funext (hF0 b)
      rw [hfun]
      exact (hmirror hbig).analytic b hb
  · intro b hb γ
    rcases hcase with hW | ⟨hst, hbig⟩
    · rw [hW, hW]
      have e := congrFun (congrFun
        (minimizingCoordinates_gaugeTransform hc hL hOne hGa hF hspos hσs V hV γ) b.1) b.2
      unfold torusCoordinate minimizingBondCoordinate
      rw [e]
      rfl
    · subst hst
      rw [hF0, hF0, hfc hbig, hfc hbig, hMG F m _ V γ (by omega)]
      have hcoldM₀ := hcoldM F m (enclosingCell b.1) V (5 / 4 * σ) (by omega) hV
      have e := congrFun (congrFun (minimizingCoordinates_gaugeTransform hc hL hOne hGa hM hspos hσs
        (reflectedField m (enclosingCell b.1) V) hcoldM₀
        (reflectedGauge m (enclosingCell b.1) γ)) (reflectedBond m b).1) (reflectedBond m b).2
      unfold minimizingBondCoordinate
      rw [e, hcell0, reflectedGauge_zero]
      rfl
  · intro b hb h
    rcases hcase with hW | ⟨hst, hbig⟩
    · rw [hW, hW]
      have e := congrFun (congrFun (minimizingCoordinates_translateField hc hL hOne hTr hF hspos hσs V hV h)
        (b.1 + cellCentre F.depth h)) b.2
      unfold torusCoordinate minimizingBondCoordinate
      rw [e]
      simp
    · subst hst
      rw [hF0, hF0, hfc hbig, hfc hbig]
      have e1 := hSh F h b.1 hOdd hs2
      have e2 : reflectedBond m (b.1 + cellCentre F.depth h, b.2) = reflectedBond m b := by
        unfold reflectedBond
        simp only [e1.2]
      simp only [e1.1, e2]
      rw [hMS F m (enclosingCell b.1) h V]
end YangMills.Construction.ColdStepAtMirrorFrames
end
