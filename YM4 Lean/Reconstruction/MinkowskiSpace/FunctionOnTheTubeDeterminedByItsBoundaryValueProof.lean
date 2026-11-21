import Reconstruction.MinkowskiSpace.AcrossTheSpacelikePointsProof
import YangMills.Construction.ComplexAnalysis.HolomorphicFunctionsAreSmooth
import YangMills.Construction.Continuum.BumpsSmoothedIndicatorsAndTensorsOfBumpsProof
import Reconstruction.Coordinates.HolomorphicParametricIntegral
import Reconstruction.MinkowskiSpace.BoundaryValuesOnTheTubeProof
import Reconstruction.MinkowskiSpace.FunctionOnTheTubeDeterminedByItsBoundaryValue
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.TubeUniqueness
open MinkowskiSpace WightmanTheory TubeBoundary
section Points
variable {b : ℕ}
theorem coneGap_smul (y : RealVec4) {t : ℝ} (ht : 0 ≤ t) :
    coneGap (t • y) = t * coneGap y := by
  have h : spaceNorm (spacePart (t • y)) = t * spaceNorm (spacePart y) := by
    unfold spaceNorm spacePart
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
    rw [Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht]
  simp only [coneGap, h, Pi.smul_apply, smul_eq_mul]
  ring
theorem smul_mem_futureConeTuples {Y : TestSpaces.PointTuple b} (hY : Y ∈ futureConeTuples b)
    {t : ℝ} (ht : 0 < t) : t • Y ∈ futureConeTuples b := by
  intro k _
  have hk : coneGap (Y k) > 0 := hY k trivial
  change coneGap (t • Y k) > 0
  rw [coneGap_smul _ ht.le]
  exact mul_pos ht hk
theorem smul_mem_closedFutureConeTuples {Y : TestSpaces.PointTuple b}
    (hY : Y ∈ futureConeTuples b) {t : ℝ} (ht : 0 ≤ t) : t • Y ∈ closedFutureConeTuples b := by
  intro k _
  have hk : coneGap (Y k) > 0 := hY k trivial
  change coneGap (t • Y k) ≥ 0
  rw [coneGap_smul _ ht]
  exact mul_nonneg ht hk.le
theorem exists_pos_le_coneGap {Y : TestSpaces.PointTuple b} (hY : Y ∈ futureConeTuples b) :
    ∃ ε > 0, ∀ k, ε ≤ coneGap (Y k) := by apply _root_.YangMills.Construction.TubeBoundary.exists_uniform_gap <;> assumption
theorem imPart_tubePoint (x Y : TestSpaces.PointTuple b) (k : Fin b) :
    MinkowskiSpace.imPart (tubePoint x Y k) = Y k := by apply _root_.YangMills.Construction.TubeBoundary.imPart_tubePoint <;> assumption
theorem tubePoint_mem_tubeTuples {Y : TestSpaces.PointTuple b} (hY : Y ∈ futureConeTuples b)
    (x : TestSpaces.PointTuple b) : tubePoint x Y ∈ tubeTuples b := by apply _root_.YangMills.Construction.TubeBoundary.tubePoint_mem_tubeTuples <;> assumption
def tupleCoords (ζ : Fin b → ComplexVec4) : Coordinates.ComplexCoordinates (b * 4) :=
  fun j => ζ (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2
theorem coordsToTuple_tupleCoords (ζ : Fin b → ComplexVec4) :
    coordsToTuple (tupleCoords ζ) = ζ := by apply _root_.YangMills.Construction.FieldForms.SpacelikeExtension.coordsToTuple_tupleCoords <;> assumption
theorem continuous_comp_tubePoint_add {u : (Fin b → ComplexVec4) → ℂ}
    (hu : IsHolomorphicOnTube u) {Y : TestSpaces.PointTuple b} (hY : Y ∈ futureConeTuples b)
    (a : TestSpaces.PointTuple b) :
    Continuous fun x : TestSpaces.PointTuple b => u (tubePoint (x + a) Y) := by apply _root_.YangMills.Construction.TubeBoundary.continuous_comp_tubePoint <;> assumption
theorem differentiableAt_comp_coordsToTuple
    (h₃ : SeveralComplexVariables.HolomorphicContDiff.Statement)
    (hb : 0 < b) {u : (Fin b → ComplexVec4) → ℂ} (hu : IsHolomorphicOnTube u)
    {z : Coordinates.ComplexCoordinates (b * 4)} (hz : coordsToTuple z ∈ tubeTuples b) :
    DifferentiableAt ℂ (fun z : Coordinates.ComplexCoordinates (b * 4) => u (coordsToTuple z)) z := by
  have : Nonempty (Fin (b * 4)) := ⟨⟨0, by omega⟩⟩
  have hW : SeveralComplexVariables.IsHolomorphicOnOpen (coordsToTuple ⁻¹' tubeTuples b)
      (fun z : Fin (b * 4) → ℂ => u (coordsToTuple z)) := by
    refine ⟨hu.1, (continuous_apply (0 : Fin 1)).comp_continuousOn hu.2.1, fun c hc q => ?_⟩
    filter_upwards [hu.2.2 c hc q] with ζ hζ
    have e : SeveralComplexVariables.basisVector q =
        Coordinates.ComplexCoordinates.stdBasisVector q := by
      funext i
      simp [SeveralComplexVariables.basisVector, Coordinates.ComplexCoordinates.stdBasisVector,
        Pi.single_apply]
    rw [e]
    exact differentiableAt_pi.1 hζ 0
  have hC := h₃ (Fin (b * 4)) _ _ hW
  exact (hC.contDiffAt (hu.1.mem_nhds hz)).differentiableAt (by simp)
def complexLine (x a Y : TestSpaces.PointTuple b) (z : ℂ) : Fin b → ComplexVec4 :=
  tubePoint (x + (a + z.re • Y)) (z.im • Y)
theorem complexLine_apply (x a Y : TestSpaces.PointTuple b) (w : ℂ) (k : Fin b) (μ : Fin 4) :
    complexLine x a Y w k μ = ((x k μ + a k μ : ℝ) : ℂ) + w * (Y k μ : ℂ) := by
  simp only [complexLine, tubePoint, toComplex, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  apply Complex.ext <;> simp
  ring
theorem complexLine_mem_tubeTuples {Y : TestSpaces.PointTuple b} (hY : Y ∈ futureConeTuples b)
    (x a : TestSpaces.PointTuple b) {w : ℂ} (hw : 0 < w.im) : complexLine x a Y w ∈ tubeTuples b :=
  tubePoint_mem_tubeTuples (smul_mem_futureConeTuples hY hw) _
theorem tubeGap_complexLine (x a Y : TestSpaces.PointTuple b) {w : ℂ} (hw : 0 ≤ w.im)
    (k : Fin b) : tubeGap (complexLine x a Y w k) = w.im * coneGap (Y k) := by
  rw [tubeGap, complexLine, imPart_tubePoint]
  exact coneGap_smul _ hw
theorem differentiableAt_comp_complexLine
    (h₃ : SeveralComplexVariables.HolomorphicContDiff.Statement)
    (hb : 0 < b) {u : (Fin b → ComplexVec4) → ℂ} (hu : IsHolomorphicOnTube u)
    {Y : TestSpaces.PointTuple b} (hY : Y ∈ futureConeTuples b) (x a : TestSpaces.PointTuple b)
    {w : ℂ} (hw : 0 < w.im) : DifferentiableAt ℂ (fun w : ℂ => u (complexLine x a Y w)) w := by
  have hz := differentiableAt_comp_coordsToTuple h₃ hb hu (z := tupleCoords (complexLine x a Y w))
    (by rw [coordsToTuple_tupleCoords]; exact complexLine_mem_tubeTuples hY x a hw)
  have hc : DifferentiableAt ℂ (fun w : ℂ => tupleCoords (complexLine x a Y w)) w := by
    refine differentiableAt_pi.2 fun i => ?_
    simp only [tupleCoords, complexLine_apply]
    fun_prop
  have h := DifferentiableAt.comp w hz hc
  simpa [Function.comp_def, coordsToTuple_tupleCoords] using h
theorem norm_le_of_le_tubeGap {q : ℕ} {c : ℝ} {u : (Fin b → ComplexVec4) → ℂ}
    (hB : ∀ ζ ∈ tubeTuples b, ‖u ζ‖ ≤ c * ∏ k, (min 1 (tubeGap (ζ k)))⁻¹ ^ q)
    {δ : ℝ} (hδ : 0 < δ) {ζ : Fin b → ComplexVec4} (hζ : ζ ∈ tubeTuples b)
    (hm : ∀ k, δ ≤ tubeGap (ζ k)) : ‖u ζ‖ ≤ |c| * ((min 1 δ)⁻¹ ^ q) ^ b := by
  have hpos : ∀ k, 0 < min 1 (tubeGap (ζ k)) := fun k =>
    lt_min one_pos (lt_of_lt_of_le hδ (hm k))
  have h0 : ∀ k, 0 ≤ (min 1 (tubeGap (ζ k)))⁻¹ ^ q := fun k =>
    pow_nonneg (inv_nonneg.2 (hpos k).le) q
  have hp : ∏ k, (min 1 (tubeGap (ζ k)))⁻¹ ^ q ≤ ((min 1 δ)⁻¹ ^ q) ^ b := by
    calc ∏ k, (min 1 (tubeGap (ζ k)))⁻¹ ^ q ≤ ∏ _k : Fin b, (min 1 δ)⁻¹ ^ q :=
          Finset.prod_le_prod (fun k _ => h0 k) fun k _ =>
            pow_le_pow_left₀ (inv_nonneg.2 (hpos k).le)
              (inv_anti₀ (lt_min one_pos hδ) (min_le_min_left 1 (hm k))) q
      _ = ((min 1 δ)⁻¹ ^ q) ^ b := by simp
  have hP : 0 ≤ ∏ k, (min 1 (tubeGap (ζ k)))⁻¹ ^ q := Finset.prod_nonneg fun k _ => h0 k
  exact (hB ζ hζ).trans ((mul_le_mul_of_nonneg_right (le_abs_self c) hP).trans
    (mul_le_mul_of_nonneg_left hp (abs_nonneg c)))
theorem pairing_translateBy {u : (Fin b → ComplexVec4) → ℂ}
    (Y a : TestSpaces.PointTuple b) (ψ : TestSpaces.PointTuple b → ℂ) :
    pairing u Y (TubeBoundary.translateBy a ψ) = ∫ x, u (tubePoint (x + a) Y) * ψ x := by apply _root_.YangMills.Construction.TubeBoundary.pairing_translateBy <;> assumption
theorem norm_le_tupleNorm (x : TestSpaces.PointTuple b) : ‖x‖ ≤ TestSpaces.tupleNorm x := by apply _root_.YangMills.SharedProofs.p25561 <;> assumption
theorem isHolomorphicIn_congr {m : ℕ} {O : Set (Coordinates.ComplexCoordinates m)}
    {f g : Coordinates.ComplexCoordinates m → ℂ}
    (h : Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => f z)
    (hfg : ∀ z ∈ O, f z = g z) :
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => g z := by
  refine ⟨h.1, h.2.1.congr fun z hz => ?_, fun a ha j => ?_⟩
  · funext i
    exact (hfg z hz).symm
  · have hcont : Continuous fun ζ : ℂ =>
        a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j := by fun_prop
    have hO : ∀ᶠ ζ in 𝓝 (0 : ℂ), a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j ∈ O :=
      hcont.continuousAt.eventually (h.1.mem_nhds (by simpa using ha))
    filter_upwards [h.2.2 a ha j, hO.eventually_nhds] with ζ hζ hζO
    refine hζ.congr_of_eventuallyEq ?_
    filter_upwards [hζO] with s hs
    funext i
    exact (hfg _ hs).symm
end Points
section Main
open ComplexAnalysis (upperHalfPlaneCoords)
variable {b q : ℕ} {c : ℝ} {u : (Fin b → ComplexVec4) → ℂ}
theorem integral_mul_bump_eq_zero (h₁ : TubeBoundary.BoundaryValueBound)
    (h₂ : ComplexAnalysis.IdentityTheoremsProdAndUpperHalfPlane)
    (h₃ : SeveralComplexVariables.HolomorphicContDiff.Statement)
    (h₄ : Coordinates.ComplexCoordinates.HolomorphicParametricIntegral)
    (hb : 0 < b) (hu : IsHolomorphicOnTube u)
    (hB : ∀ ζ ∈ tubeTuples b, ‖u ζ‖ ≤ c * ∏ k, (min 1 (tubeGap (ζ k)))⁻¹ ^ q)
    {Υ : TestSpaces.PointTuple b → ℝ} (hc : Continuous Υ) (hi : Integrable Υ) (h0 : ∀ x, 0 ≤ Υ x)
    (hφ : (fun x => (Υ x : ℂ)) ∈ TestSpaces.schwartzSet b)
    (hz : ∀ a : TestSpaces.PointTuple b,
      boundaryValue u 0 (TubeBoundary.translateBy a fun x => (Υ x : ℂ)) = 0)
    {Y : TestSpaces.PointTuple b} (hY : Y ∈ futureConeTuples b) (a : TestSpaces.PointTuple b) :
    ∫ x, u (tubePoint (x + a) Y) * (Υ x : ℂ) = 0 := by
  obtain ⟨-, -, htr, ⟨he1, he2, -⟩, -⟩ := h₁ b q c u hb hu hB
  let v : ℂ → ℂ := fun z => boundaryValue u (z.im • Y)
    (TubeBoundary.translateBy (a + z.re • Y) fun x => (Υ x : ℂ))
  have hvc : ContinuousOn v {z | 0 ≤ z.im} := by
    have hm : Continuous fun z : ℂ => (z.im • Y, a + z.re • Y) := by fun_prop
    exact (he2 _ hφ).comp hm.continuousOn fun z hw => ⟨smul_mem_closedFutureConeTuples hY hw, trivial⟩
  have hvr : ∀ z : ℂ, z.im = 0 → v z = 0 := by
    intro z hz0
    change boundaryValue u (z.im • Y) _ = 0
    rw [hz0, zero_smul]
    exact hz _
  have hint : ∀ z : ℂ, 0 < z.im → v z = ∫ x, u (complexLine x a Y z) * (Υ x : ℂ) := by
    intro z hw
    change boundaryValue u (z.im • Y)
      (TubeBoundary.translateBy (a + z.re • Y) fun x => (Υ x : ℂ)) = _
    rw [he1 _ (smul_mem_futureConeTuples hY hw) _ (htr _ hφ _), pairing_translateBy]
    rfl
  let ν : Measure (TestSpaces.PointTuple b) := volume.withDensity fun x => ENNReal.ofReal (Υ x)
  have hfin : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hi.2
  have hν : ∀ g : TestSpaces.PointTuple b → ℂ, ∫ x, g x ∂ν = ∫ x, g x * (Υ x : ℂ) := by
    intro g
    rw [integral_withDensity_eq_integral_toReal_smul hc.measurable.ennreal_ofReal
      (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [ENNReal.toReal_ofReal (h0 x), Complex.real_smul]
    ring
  have hO : IsOpen upperHalfPlaneCoords := isOpen_lt continuous_const (by fun_prop)
  obtain ⟨ε, hε, hm⟩ := exists_pos_le_coneGap hY
  have hmeas : ∀ ζ ∈ upperHalfPlaneCoords,
      Measurable fun ξ : TestSpaces.PointTuple b => u (complexLine ξ a Y (ζ 0)) := by
    intro ζ hζ
    have hζ' : 0 < (ζ 0).im := hζ
    exact (continuous_comp_tubePoint_add hu (smul_mem_futureConeTuples hY hζ')
      (a + (ζ 0).re • Y)).measurable
  have hhol : ∀ ξ : TestSpaces.PointTuple b, Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1)
      upperHalfPlaneCoords fun ζ _ => u (complexLine ξ a Y (ζ 0)) := by
    intro ξ
    have hd : ∀ w : ℂ, 0 < w.im → DifferentiableAt ℂ (fun w : ℂ => u (complexLine ξ a Y w)) w :=
      fun w hw => differentiableAt_comp_complexLine h₃ hb hu hY ξ a hw
    refine ⟨hO, continuousOn_pi.2 fun _ z hw => ?_, fun a₀ ha₀ j => ?_⟩
    · have h1 : ContinuousAt (fun w : ℂ => u (complexLine ξ a Y w)) (z 0) :=
        (hd (z 0) hw).continuousAt
      have h2 : ContinuousAt (fun z : Coordinates.ComplexCoordinates 1 => z 0) z :=
        (continuous_apply 0).continuousAt
      exact (ContinuousAt.comp (f := fun z : Coordinates.ComplexCoordinates 1 => z 0) h1 h2).continuousWithinAt
    · have hp : Differentiable ℂ fun s : ℂ =>
          (a₀ + s • Coordinates.ComplexCoordinates.stdBasisVector j) 0 := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        fun_prop
      have h0' : 0 < ((a₀ + (0 : ℂ) • Coordinates.ComplexCoordinates.stdBasisVector j) 0).im := by
        simp only [zero_smul, add_zero]
        exact ha₀
      have hev : ∀ᶠ s in 𝓝 (0 : ℂ),
          0 < ((a₀ + s • Coordinates.ComplexCoordinates.stdBasisVector j) 0).im :=
        (Complex.continuous_im.comp hp.continuous).continuousAt.eventually (lt_mem_nhds h0')
      filter_upwards [hev] with s hs
      exact differentiableAt_pi.2 fun _ => DifferentiableAt.comp
        (f := fun s : ℂ => (a₀ + s • Coordinates.ComplexCoordinates.stdBasisVector j) 0) s
        (hd _ hs) (hp s)
  have hbd : ∀ a₀ ∈ upperHalfPlaneCoords, ∃ O' ∈ 𝓝 a₀, O' ⊆ upperHalfPlaneCoords ∧ ∃ C : ℝ,
      ∀ ξ : TestSpaces.PointTuple b, ∀ ζ ∈ O', ‖u (complexLine ξ a Y (ζ 0))‖ ≤ C := by
    intro a₀ ha₀
    have ht : 0 < (a₀ 0).im := ha₀
    have hδ : 0 < (a₀ 0).im / 2 * ε := mul_pos (half_pos ht) hε
    have hO' : IsOpen {z : Coordinates.ComplexCoordinates 1 | (a₀ 0).im / 2 < (z 0).im} :=
      isOpen_lt continuous_const (by fun_prop)
    refine ⟨_, hO'.mem_nhds (half_lt_self ht), fun z hw => lt_trans (half_pos ht) hw,
      |c| * ((min 1 ((a₀ 0).im / 2 * ε))⁻¹ ^ q) ^ b, fun ξ z hw => ?_⟩
    have hw' : (a₀ 0).im / 2 < (z 0).im := hw
    have hpos : 0 < (z 0).im := lt_trans (half_pos ht) hw'
    refine norm_le_of_le_tubeGap hB hδ (complexLine_mem_tubeTuples hY ξ a hpos) fun k => ?_
    rw [tubeGap_complexLine ξ a Y hpos.le]
    exact mul_le_mul hw'.le (hm k) hε.le hpos.le
  have hI := (h₄ (TestSpaces.PointTuple b) ν 1 le_rfl _ hO
    (fun p => u (complexLine p.1 a Y (p.2 0))) hmeas hhol hbd).2
  have hvh : Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) upperHalfPlaneCoords
      fun z _ => v (z 0) :=
    isHolomorphicIn_congr (f := fun ζ => ∫ ξ, u (complexLine ξ a Y (ζ 0)) ∂ν) hI fun z hw => by
      have hw' : 0 < (z 0).im := hw
      rw [hν (fun ξ => u (complexLine ξ a Y (z 0))), hint (z 0) hw']
  have h := h₂.2 v hvc hvh hvr Complex.I (by simp)
  rw [hint Complex.I (by simp)] at h
  simpa [complexLine] using h
end Main
theorem boundaryValueDetermines (h₁ : TubeBoundary.BoundaryValueBound)
    (h₂ : ComplexAnalysis.IdentityTheoremsProdAndUpperHalfPlane)
    (h₃ : SeveralComplexVariables.HolomorphicContDiff.Statement)
    (h₄ : Coordinates.ComplexCoordinates.HolomorphicParametricIntegral)
    (h₅ : TestSpaces.Elementary.BasicProperties) : BoundaryValueDetermines := by
  intro b q c u Υ hb hu hB hs h0 h1 hsupp hz ζ hζ
  have hcont : ∀ j, 0 < j → Continuous (Υ j) := fun j hj => (hs j hj).1.continuous
  have hint : ∀ j, 0 < j → Integrable (Υ j) := fun j hj =>
    (hcont j hj).integrable_of_hasCompactSupport (hs j hj).2.1
  have hcs : ∀ j, 0 < j → HasCompactSupport fun x => (Υ j x : ℂ) := fun j hj =>
    (hs j hj).2.1.comp_left Complex.ofReal_zero
  have hφ : ∀ j, 0 < j → (fun x => (Υ j x : ℂ)) ∈ TestSpaces.schwartzSet b := by
    intro j hj
    have hm : (fun x => (Υ j x : ℂ)) ∈
        (TestSpaces.smoothCompactSupp Set.univ : Set (TestSpaces.PointTuple b → ℂ)) :=
      ⟨Complex.ofRealCLM.contDiff.comp (hs j hj).1, hcs j hj, Set.subset_univ _⟩
    exact ((h₅ b hb).2.2.1 Set.univ isOpen_univ _ hm).1
  let a : TestSpaces.PointTuple b := fun k => MinkowskiSpace.rePart (ζ k)
  let Y : TestSpaces.PointTuple b := fun k => MinkowskiSpace.imPart (ζ k)
  have hY : Y ∈ futureConeTuples b := fun k _ => hζ k trivial
  have hf : Continuous fun x => u (tubePoint (x + a) Y) := continuous_comp_tubePoint_add hu hY a
  have hf0 : u (tubePoint (0 + a) Y) = u ζ := by
    congr 1
    funext k
    simp only [tubePoint, zero_add]
    exact (eq_rePart_add_I_smul_imPart (ζ k)).symm
  refine norm_le_zero_iff.1 (le_of_forall_pos_le_add fun ε hε => ?_)
  rw [zero_add]
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.1 (hf.continuousAt (x := 0)) ε hε
  obtain ⟨m, hn⟩ := exists_nat_one_div_lt hδ
  have hj : 0 < m + 1 := Nat.succ_pos m
  have hjd : 1 / ((m + 1 : ℕ) : ℝ) < δ := by simpa using hn
  have hzero := integral_mul_bump_eq_zero h₁ h₂ h₃ h₄ hb hu hB (hcont _ hj) (hint _ hj) (h0 _ hj)
    (hφ _ hj) (hz _ hj) hY a
  have hi1 : Integrable fun x => u (tubePoint (x + a) Y) * (Υ (m + 1) x : ℂ) :=
    (hf.mul (Complex.continuous_ofReal.comp (hcont _ hj))).integrable_of_hasCompactSupport
      (hcs _ hj).mul_left
  have hi2 : Integrable fun x => u ζ * (Υ (m + 1) x : ℂ) := (hint _ hj).ofReal.const_mul _
  have hone : ∫ x, (Υ (m + 1) x : ℂ) = 1 := by
    rw [integral_complex_ofReal, h1 _ hj, Complex.ofReal_one]
  have hrepr : u ζ = ∫ x, (u ζ - u (tubePoint (x + a) Y)) * (Υ (m + 1) x : ℂ) := by
    have e : (fun x => (u ζ - u (tubePoint (x + a) Y)) * (Υ (m + 1) x : ℂ)) =
        fun x => u ζ * (Υ (m + 1) x : ℂ) - u (tubePoint (x + a) Y) * (Υ (m + 1) x : ℂ) := by
      funext x
      ring
    rw [e, integral_sub hi2 hi1, hzero, integral_const_mul, hone]
    simp
  have hle : ∀ x, ‖(u ζ - u (tubePoint (x + a) Y)) * (Υ (m + 1) x : ℂ)‖ ≤
      ε * Υ (m + 1) x := by
    intro x
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (h0 _ hj x)]
    by_cases hx : Υ (m + 1) x = 0
    · simp [hx]
    · have hlt : TestSpaces.tupleNorm x < 1 / ((m + 1 : ℕ) : ℝ) := by
        by_contra hge
        exact hx (hsupp _ hj x (not_lt.1 hge))
      have hd : dist x 0 < δ := by
        rw [dist_zero_right]
        exact ((norm_le_tupleNorm x).trans_lt hlt).trans hjd
      have h3 : dist (u (tubePoint (x + a) Y)) (u (tubePoint (0 + a) Y)) < ε :=
        hclose hd
      rw [hf0, dist_comm, dist_eq_norm] at h3
      exact mul_le_mul_of_nonneg_right h3.le (h0 _ hj x)
  have hfinal := norm_integral_le_of_norm_le ((hint _ hj).const_mul ε) (ae_of_all _ hle)
  rw [integral_const_mul, h1 _ hj, mul_one, ← hrepr] at hfinal
  exact hfinal
end YangMills.Construction.TubeUniqueness
