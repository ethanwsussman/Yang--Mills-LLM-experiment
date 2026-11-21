import YangMills.Construction.ColdStepAtMirrorFrames.BlockEnergyOnTwoTori
import YangMills.Construction.ColdStepAtMirrorFrames.BlockEnergyUnderGaugesAndShifts
import YangMills.Construction.ColdStepAtMirrorFrames.CellGeometryOfATorus
import YangMills.Construction.ColdStepAtMirrorFrames.ComparisonOfTwoTops
import YangMills.Construction.ColdStepAtMirrorFrames.DensityOfAFrameOnOneTorusForm
import YangMills.Construction.ColdStepAtMirrorFrames.DensityOfTheFrames
import YangMills.Construction.ColdStepAtMirrorFrames.ExponentialOfTheLieAlgebra
import YangMills.Construction.ColdStepAtMirrorFrames.HolonomyIsLipschitz
import YangMills.Construction.ColdStepAtMirrorFrames.KernelsOfTheBlockEnergyProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheDensitiesAreNearTheirLimitsProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open YangMills.Construction.BlockAverages YangMills.Construction.Interpolation
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
namespace FrameDensity
theorem norm_coe_unitQuaternion (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
theorem pow_le_factorial_mul_exp (N : ℕ) (ε : ℝ) (hε : 0 < ε) (y : ℝ) (hy : 0 ≤ y) :
    y ^ N ≤ ((N.factorial : ℝ) / ε ^ N) * Real.exp (ε * y) := by
  have h := Real.pow_div_factorial_le_exp (ε * y) (by positivity) N
  have hf : (0 : ℝ) < N.factorial := by exact_mod_cast N.factorial_pos
  rw [div_le_iff₀ hf, mul_pow] at h
  have hp : 0 < ε ^ N := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hp]
  nlinarith
theorem max_one_pow_le_exp (N : ℕ) (ε : ℝ) (hε : 0 < ε) : ∃ A : ℝ, 0 ≤ A ∧ ∀ q y : ℝ, 0 ≤ q → q ≤ y →
    max 1 (q ^ N) ≤ (1 + A) * Real.exp (ε * y) := by
  refine ⟨(N.factorial : ℝ) / ε ^ N, by positivity, fun q y hq hqy => ?_⟩
  have hy : 0 ≤ y := hq.trans hqy
  have he : (1 : ℝ) ≤ Real.exp (ε * y) := Real.one_le_exp (by positivity)
  have hA0 : 0 ≤ (N.factorial : ℝ) / ε ^ N := by positivity
  have h1 : q ^ N ≤ (N.factorial : ℝ) / ε ^ N * Real.exp (ε * y) :=
    (pow_le_pow_left₀ hq hqy N).trans (pow_le_factorial_mul_exp N ε hε y hy)
  refine max_le ?_ ?_
  · nlinarith
  · nlinarith [Real.exp_pos (ε * y)]
theorem torusDecayFactor_le_exp (δ₂ : ℝ) (hδ₂ : 0 < δ₂) (L : ℕ) (hL : 1 ≤ L) : ∃ Cw : ℝ, 1 ≤ Cw ∧ ∀ δ : ℝ, δ ≤ δ₂ / 64 → ∀ n : ℕ,
    torusDecayFactor L δ n ≤ Cw * Real.exp (δ₂ / 32 * n) := by
  obtain ⟨A, hA0, hA⟩ := max_one_pow_le_exp 16000 (δ₂ / 64) (by positivity)
  refine ⟨1 + A, by linarith, fun δ hδ n => ?_⟩
  unfold torusDecayFactor
  have hn : (0 : ℝ) ≤ n := by positivity
  have hroot : (1 : ℝ) ≤ (L : ℝ) ^ (1 / 640 : ℝ) := Real.one_le_rpow (by exact_mod_cast hL) (by norm_num)
  have hq : (n : ℝ) / (L : ℝ) ^ (1 / 640 : ℝ) ≤ n := div_le_self hn hroot
  have hq0 : 0 ≤ (n : ℝ) / (L : ℝ) ^ (1 / 640 : ℝ) := by positivity
  have h2 := hA _ _ hq0 hq
  have h3 : Real.exp (δ * n) ≤ Real.exp (δ₂ / 64 * n) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hδ hn)
  refine (mul_le_mul h2 h3 (Real.exp_pos _).le (by positivity)).trans (le_of_eq ?_)
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring
theorem plaquetteDefect_chartedField_le (hexp : QuaternionExp.ExpUnitLipschitzInjective) (hhol : PathHolonomyLipschitz)
    (hcover : BlocksCoverLowerLevel) (hL : Odd F.blockSide) (hs0 : ∀ i, 0 < F.extent i) (V : F.GaugeField F.top)
    (w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ b ∈ chordBonds (finiteCells F), ‖w b.1 b.2 - w' b.1 b.2‖ ≤ ε) (p : F.Site F.depth × Fin 4 × Fin 4) :
    plaquetteDefect (chartedField w V) p ≤ plaquetteDefect (chartedField w' V) p + 4 * ε := by
  classical
  have hmem : ∀ x i, ¬ IsAxialTreeBond (x, i) → (x, i) ∈ chordBonds (finiteCells F) := by
    intro x i ht
    unfold chordBonds innerBonds
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
    exact ⟨⟨hcover F hL hs0 _, hcover F hL hs0 _⟩, ht⟩
  have hbond : ∀ x i, ‖((chartedField w V x i : UnitQuaternion) : ℍ[ℝ]) - ((chartedField w' V x i : UnitQuaternion) : ℍ[ℝ])‖ ≤ ε := by
    intro x i
    unfold chartedField
    by_cases hcr : IsCrossingBond (x, i)
    · simp only [if_pos hcr]
      have e : (((expUnit (w x i) * V (enclosingCell x) i : UnitQuaternion)) : ℍ[ℝ]) - ((expUnit (w' x i) * V (enclosingCell x) i : UnitQuaternion) : ℍ[ℝ]) =
          (((expUnit (w x i) : UnitQuaternion) : ℍ[ℝ]) - ((expUnit (w' x i) : UnitQuaternion) : ℍ[ℝ])) * ((V (enclosingCell x) i : UnitQuaternion) : ℍ[ℝ]) := by
        simp only [Submonoid.coe_mul, sub_mul]
      rw [e, norm_mul, norm_coe_unitQuaternion, mul_one]
      exact (hexp.1 _ _).trans (h (x, i) (hmem x i fun ht => ht.1 hcr))
    · simp only [if_neg hcr]
      by_cases ht : IsAxialTreeBond (x, i)
      · simp only [if_pos ht, sub_self, norm_zero]
        exact hε
      · simp only [if_neg ht]
        exact (hexp.1 _ _).trans (h (x, i) (hmem x i ht))
  have h2 := hhol F F.depth _ _ _ hbond p.1 [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)]
  simp only [List.length_cons, List.length_nil] at h2
  unfold plaquetteDefect plaquetteHolonomy
  obtain ⟨A, hAd⟩ : ∃ A, A = (((pathHolonomy (chartedField w V) p.1
    [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] : UnitQuaternion) : ℍ[ℝ])) := ⟨_, rfl⟩
  obtain ⟨B, hBd⟩ : ∃ B, B = ((pathHolonomy (chartedField w' V) p.1
    [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] : UnitQuaternion) : ℍ[ℝ]) := ⟨_, rfl⟩
  rw [← hAd, ← hBd] at h2 ⊢
  have h3 : ‖A - 1‖ ≤ ‖A - B‖ + ‖B - 1‖ := by
    have := norm_add_le (A - B) (B - 1)
    simpa using this
  norm_num at h2
  linarith
theorem stepFrame_eq_of_not_large {a ρ : ℝ} {m : ℕ} (hbig : ¬ ∀ i, 4 * m + 5 < F.extent i) (b : F.Site F.depth × Fin 4) (V : F.GaugeField F.top) :
    stepFrame false a ρ m b V = stepFrame true a ρ m b V := by
  simp [stepFrame, bondFrameCoord, if_neg hbig]
theorem norm_frameGap_le {a ρ δ₂ Cf σ : ℝ} {m : ℕ} {V : F.GaugeField F.top} (hCf : 0 < Cf) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hN : (∀ i, 4 * m + 5 < F.extent i) → FrameNearMinimizer a ρ δ₂ Cf σ m V) (b : F.Site F.depth × Fin 4)
    (hb : b ∈ chordBonds (finiteCells F)) : ‖frameGap a ρ m b V‖ ≤ frameDecayBound Cf δ₂ m := by
  have hg0 : 0 ≤ frameDecayBound Cf δ₂ m := by
    unfold frameDecayBound
    positivity
  by_cases hbig : ∀ i, 4 * m + 5 < F.extent i
  · have h1 := (hN hbig b hb).1
    have e : ‖frameGap a ρ m b V‖ = ‖frameDeviation a ρ m b V‖ := by
      unfold frameGap frameDeviation
      simp only [stepFrame, torusCoordinate]
      rfl
    rw [e]
    exact h1.trans (mul_le_of_le_one_right hg0 hσ1)
  · unfold frameGap
    rw [stepFrame_eq_of_not_large hbig, sub_self, norm_zero]
    exact hg0
theorem norm_bondDeriv_frameGap_le {a ρ δ₂ Cf σ : ℝ} {m : ℕ} {V : F.GaugeField F.top} (hCf : 0 < Cf) (hδ₂ : 0 ≤ δ₂)
    (hN : (∀ i, 4 * m + 5 < F.extent i) → FrameNearMinimizer a ρ δ₂ Cf σ m V) (b : F.Site F.depth × Fin 4)
    (hb : b ∈ chordBonds (finiteCells F)) (hA1 : IsBondAnalyticAt (stepFrame true a ρ m b) V)
    (hA0 : IsBondAnalyticAt (stepFrame false a ρ m b) V) (k : ℕ) (e : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (hk : 1 ≤ k) (hk3 : k ≤ 3) (hX : AreUnitVectors X) :
    ‖bondDeriv (frameGap a ρ m b) V e X‖ ≤
      frameDecayBound Cf δ₂ m * Real.exp (-(δ₂ / 4 * bondListDistance (enclosingCell b.1) e)) := by
  by_cases hbig : ∀ i, 4 * m + 5 < F.extent i
  · have h1 := (hN hbig b hb).2 k e X hk hk3 hX
    have hf : ContDiffAt ℝ k (fun τ : Fin k → ℝ => frameGap a ρ m b (leftTranslate (ColdStepAtMirrorFrames.bondSpread e X τ) V)) 0 :=
      ((hA0 k e X).sub (hA1 k e X)).contDiffAt
    have hcomp := ContinuousLinearMap.iteratedFDeriv_comp_left (imaginaryQuaternions.subtypeL) hf (i := k) le_rfl
    have hfun : frameDeviation a ρ m b = fun V' => ((frameGap a ρ m b V' : imaginaryQuaternions) : ℍ[ℝ]) := by
      funext V'
      unfold frameGap frameDeviation
      simp only [stepFrame, torusCoordinate]
      rfl
    have e2 : ‖bondDeriv (frameGap a ρ m b) V e X‖ = ‖bondDeriv (frameDeviation a ρ m b) V e X‖ := by
      rw [hfun]
      unfold bondDeriv
      have h3 := congrArg (fun T => T (fun l : Fin k => (Pi.single l 1 : Fin k → ℝ))) hcomp
      simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp] at h3
      change _ = ‖iteratedFDeriv ℝ k (⇑(imaginaryQuaternions.subtypeL) ∘ fun τ : Fin k → ℝ =>
        frameGap a ρ m b (leftTranslate (ColdStepAtMirrorFrames.bondSpread e X τ) V)) 0 (fun l => Pi.single l 1)‖
      rw [h3]
      rfl
    rw [e2]
    refine h1.trans ?_
    unfold frameDecayBound
    rw [mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hCf.le
    have h4 : (bondListDistance (enclosingCell b.1) e : ℝ) ≤ ((max m (bondListDistance (enclosingCell b.1) e) : ℕ) : ℝ) := by
      exact_mod_cast le_max_right _ _
    nlinarith
  · have hz : (fun τ : Fin k → ℝ => frameGap a ρ m b (leftTranslate (ColdStepAtMirrorFrames.bondSpread e X τ) V)) = fun _ => 0 := by
      funext τ
      unfold frameGap
      rw [stepFrame_eq_of_not_large hbig, sub_self]
    unfold bondDeriv
    rw [hz, iteratedFDeriv_const_of_ne (by omega)]
    simp only [Pi.zero_apply, ContinuousMultilinearMap.zero_apply, norm_zero]
    unfold frameDecayBound
    positivity
theorem framesNearAtTop_of_bounds (hexp : QuaternionExp.ExpUnitLipschitzInjective) (hhol : PathHolonomyLipschitz)
    (hcover : BlocksCoverLowerLevel) {L : ℕ} {a σ C ω : ℝ} {c : ColdChainParameters} {m : ℕ} {V : F.GaugeField F.top}
    (hodd : Odd F.blockSide) (hs0 : ∀ i, 0 < F.extent i) (hS : ∀ star, FrameSmallness star a c.ρA c.δ₂ c.κ₂ C σ c.Kk m V)
    (hgap : ∀ b ∈ chordBonds (finiteCells F), ‖frameGap a c.ρA m b V‖ ≤ ω)
    (hdec : ∀ b ∈ chordBonds (finiteCells F), ∀ (k : ℕ) (e : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
      1 ≤ k → k ≤ 3 → AreUnitVectors X →
      ‖bondDeriv (frameGap a c.ρA m b) V e X‖ ≤ ω * Real.exp (-(c.δ₂ / 4 * bondListDistance (enclosingCell b.1) e)))
    (hsize : C * σ ≤ 1 / (64 * (L : ℝ))) (hcold : 5 / 8 * σ + 4 * ω ≤ c.σA) (hω0 : 0 ≤ ω) :
    FramesNearAtTop L a σ C ω c m V := by
  refine ⟨hS, hgap, hdec, fun θ hθ => ⟨fun b hb => ?_, fun p hp => ?_⟩⟩
  · have h1 := (hS true).norm_le b hb
    have h2 := (hS false).norm_le b hb
    obtain ⟨h0, h3⟩ := hθ
    simp only [interpolatedFrame]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith), abs_of_nonneg h0]
    have h4 : (1 - θ) * ‖stepFrame true a c.ρA m (b.1, b.2) V‖ ≤ (1 - θ) * (C * σ) :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    have h5 : θ * ‖stepFrame false a c.ρA m (b.1, b.2) V‖ ≤ θ * (C * σ) := mul_le_mul_of_nonneg_left h2 h0
    nlinarith
  · have h1 := plaquetteDefect_chartedField_le hexp hhol hcover hodd hs0 V (fun z i => interpolatedFrame θ a c.ρA m (z, i) V)
      (frameCoordField true a c.ρA m V) ω hω0 (fun b hb => by
        have e : interpolatedFrame θ a c.ρA m (b.1, b.2) V - frameCoordField true a c.ρA m V b.1 b.2 =
            θ • frameGap a c.ρA m (b.1, b.2) V := by
          simp only [interpolatedFrame, frameCoordField, frameGap]
          module
        change ‖interpolatedFrame θ a c.ρA m (b.1, b.2) V - frameCoordField true a c.ρA m V b.1 b.2‖ ≤ ω
        rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ.1]
        have h2 := hgap b hb
        have h3 := norm_nonneg (frameGap a c.ρA m (b.1, b.2) V)
        have h4 := hθ.2
        have h5 := hθ.1
        calc θ * ‖frameGap a c.ρA m (b.1, b.2) V‖ ≤ 1 * ‖frameGap a c.ρA m (b.1, b.2) V‖ :=
              mul_le_mul_of_nonneg_right h4 h3
          _ ≤ ω := by rw [one_mul]; exact h2) p
    have h2 := (hS true).small_curvature p hp
    simp only [if_true] at h2
    linarith
theorem mem_finiteCells (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell) : z ∈ finiteCells F := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CellShares.mem_finiteCells <;> assumption
theorem minimalCellShare_translate (hs : ∀ i, 2 ≤ F.extent i) {a : ℝ} (hcub : ∀ i j, F.extent i = F.extent j) {s δ : ℝ} {N : ℕ → ℝ}
    {V : F.GaugeField F.top} (hsh : HasRegularCellShares a δ s N (finiteCells F) V) (Y h : F.Cell) :
    minimalCellShare a (finiteCells F) (Y + h) (translateField h V) = minimalCellShare a (finiteCells F) Y V := by
  have hper : ∀ i, F.period F.top i = F.extent i := fun i => by simp [BlockFrame.period]
  have hne : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by
    rw [hper]
    have := hs i
    omega⟩
  have honsite : ∀ x : F.Cell, CubicSymmetry.actSite ⟨1, fun _ => 1, siteCoords h⟩ F.top x = x + h := by
    intro x
    funext i
    have := hne i
    simp only [CubicSymmetry.actSite, siteOfCoords, Equiv.Perm.coe_one, id_eq, one_mul, Nat.sub_self, pow_zero, Pi.add_apply]
    rw [Int.cast_add]
    unfold siteCoords
    rw [ZMod.intCast_zmod_cast, ZMod.intCast_zmod_cast]
  have hcar : CubicSymmetry.TransportsField ⟨1, fun _ => 1, siteCoords h⟩ V (translateField h V) := by
    intro x k
    rw [honsite]
    simp [CubicSymmetry.actStep, linkValue, translateField]
    rfl
  have hiso := hsh.2.2.2.2.1 ⟨1, fun _ => 1, siteCoords h⟩ (finiteCells F) (translateField h V)
    ⟨fun _ => Or.inl rfl, hcub⟩ (fun z => ⟨fun _ => mem_finiteCells hs _, fun _ => mem_finiteCells hs _⟩) hcar Y
  rw [honsite] at hiso
  exact hiso
theorem bondSpan_le_two_mul (hsym : ∀ x y : F.Cell, cellSupDist x y = cellSupDist y x)
    (htri : ∀ x y z : F.Cell, cellSupDist x z ≤ cellSupDist x y + cellSupDist y z) (Y : F.Cell) {k : ℕ}
    (e : Fin k → F.Site F.top × Fin 4) : bondSpan Y e ≤ 2 * bondListDistance Y e := by
  have h1 : ∀ l, cellSupDist Y (e l).1 ≤ bondListDistance Y e := fun l =>
    Finset.le_sup (f := fun l => cellSupDist Y (e l).1) (Finset.mem_univ l)
  refine max_le ?_ ?_
  · refine Finset.sup_le fun l _ => ?_
    have := h1 l
    change cellSupDist Y (e l).1 ≤ _
    omega
  · refine Finset.sup_le fun l _ => Finset.sup_le fun l' _ => ?_
    change cellSupDist (e l).1 (e l').1 ≤ _
    have h2 := htri (e l).1 Y (e l').1
    rw [hsym (e l).1 Y] at h2
    have h3 := h1 l
    have h4 := h1 l'
    omega
theorem bondDeriv_zero {G : F.GaugeField F.top → ℝ} (W : F.GaugeField F.top) (c : Fin 0 → F.Site F.top × Fin 4) (X : Fin 0 → imaginaryQuaternions) :
    bondDeriv G W c X = G W := by apply _root_.YangMills.SharedProofs.p1654 <;> assumption
theorem natAbs_valMinAbs_intCast_le {n : ℕ} [NeZero n] (e : ℤ) : ((e : ZMod n)).valMinAbs.natAbs ≤ e.natAbs := by apply _root_.YangMills.Construction.TorusFields.natAbs_valMinAbs_intCast_le <;> assumption
theorem period_neZero (hs : ∀ i, 2 ≤ F.extent i) (i : Fin 4) : NeZero (F.period F.top i) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CellEnergyKernels.neZero_period_top <;> assumption
theorem cellSupDist_add_unitStep_le (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell) (i : Fin 4) : cellSupDist z (z + unitStep F.top i) ≤ 1 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CellEnergyKernels.cellSupDist_add_unitStep_le <;> assumption
theorem cellSupDist_add_siteOfCoords_le (hs : ∀ i, 2 ≤ F.extent i) {r : ℕ} (Y : F.Cell) (u : Fin 4 → ℤ) (hu : WithinRadius r u) :
    cellSupDist Y (Y + siteOfCoords F.top u) ≤ r := by
  unfold cellSupDist
  refine Finset.sup_le fun l _ => ?_
  haveI := period_neZero hs l
  have e : Y l - (Y + siteOfCoords F.top u : F.Cell) l = (((-(u l) : ℤ)) : ZMod (F.period F.top l)) := by
    simp [siteOfCoords]
  rw [e]
  refine (natAbs_valMinAbs_intCast_le _).trans ?_
  have h1 := hu l
  rw [Int.natAbs_neg]
  have h2 : ((u l).natAbs : ℤ) ≤ r := by
    rw [Int.natCast_natAbs]
    exact h1
  exact_mod_cast h2
theorem cellSupDist_fineBondAt_le (hS : SiteDecomposition) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (htri : ∀ x y z : F.Cell, cellSupDist x z ≤ cellSupDist x y + cellSupDist y z) {r : ℕ} (Y : F.Cell) (u o : Fin 4 → ℤ) (i : Fin 4)
    (hu : WithinRadius r u) (ho : o ∈ centredCube F.blockSide) :
    cellSupDist Y (enclosingCell (fineBondAt Y u o i).1) ≤ r ∧
      cellSupDist Y (enclosingCell ((fineBondAt Y u o i).1 + unitStep F.depth i)) ≤ r + 1 := by
  have h1 : enclosingCell (fineBondAt Y u o i).1 = Y + siteOfCoords F.top u := ((hS F hL hs).1 (Y + siteOfCoords F.top u) o ho).1
  have hd := cellSupDist_add_siteOfCoords_le hs Y u hu
  refine ⟨by rw [h1]; exact hd, ?_⟩
  rcases (hS F hL hs).2.2.2 (fineBondAt Y u o i).1 i with h | h
  · rw [h, h1]
    omega
  · rw [h, h1]
    have h2 := htri Y (Y + siteOfCoords F.top u) (Y + siteOfCoords F.top u + unitStep F.top i)
    have h3 := cellSupDist_add_unitStep_le hs (Y + siteOfCoords F.top u) i
    omega
theorem decay_term_le {x B ω Cf Cw E₈ Ct W e d : ℝ} (hx : 0 ≤ x) (hB : 0 ≤ B) (hω0 : 0 ≤ ω) (hω : ω ≤ Cf * E₈)
    (hCw : 0 ≤ Cw) (hW : 0 < W) (he : 0 ≤ e) (hWd : W ≤ Cw * d) (hed : e * d ≤ 1) (hCt : B * Cf * Cw ≤ Ct) (hE : 0 ≤ E₈) :
    x * B * ω * e ≤ Ct * x * E₈ / W := by
  rw [le_div_iff₀ hW]
  have h0 : 0 ≤ x * B * ω := by positivity
  have h1 : e * W ≤ Cw := by
    calc e * W ≤ e * (Cw * d) := mul_le_mul_of_nonneg_left hWd he
      _ = Cw * (e * d) := by ring
      _ ≤ Cw * 1 := mul_le_mul_of_nonneg_left hed hCw
      _ = Cw := mul_one _
  calc x * B * ω * e * W = (x * B * ω) * (e * W) := by ring
    _ ≤ (x * B * ω) * Cw := mul_le_mul_of_nonneg_left h1 h0
    _ ≤ (x * B * (Cf * E₈)) * Cw := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hω (by positivity)) hCw
    _ = (B * Cf * Cw) * (x * E₈) := by ring
    _ ≤ Ct * (x * E₈) := mul_le_mul_of_nonneg_right hCt (by positivity)
    _ = Ct * x * E₈ := by ring
theorem near_term_le {x B ω Cf Cw E₈ Ct W g d : ℝ} (hx : 0 ≤ x) (hB : 0 ≤ B) (hω0 : 0 ≤ ω) (hω : ω * g = Cf * E₈)
    (hCw : 0 ≤ Cw) (hW : 0 < W) (hWd : W ≤ Cw * d) (hdg : d ≤ g) (hCt : 2 * B * Cf * Cw ≤ Ct) (hE : 0 ≤ E₈) :
    2 * (x * B * ω) ≤ Ct * x * E₈ / W := by
  rw [le_div_iff₀ hW]
  have h0 : 0 ≤ 2 * (x * B * ω) := by positivity
  calc 2 * (x * B * ω) * W ≤ 2 * (x * B * ω) * (Cw * g) :=
        mul_le_mul_of_nonneg_left (hWd.trans (mul_le_mul_of_nonneg_left hdg hCw)) h0
    _ = 2 * x * B * Cw * (ω * g) := by ring
    _ = (2 * B * Cf * Cw) * (x * E₈) := by rw [hω]; ring
    _ ≤ Ct * (x * E₈) := mul_le_mul_of_nonneg_right hCt (by positivity)
    _ = Ct * x * E₈ := by ring
theorem far_term_le {δ₁ δ₂ x σ Cf C₃ Bb Cc Cw Ct W m r : ℝ} (hδ₂ : 0 < δ₂) (hlet : 2 ^ 6 * δ₂ ≤ δ₁) (hx : 0 < x) (hσ : 0 < σ)
    (hCf : 0 < Cf) (hC₃ : 0 < C₃) (hBb : 0 < Bb) (hCc : 0 < Cc) (hCw : 0 < Cw)
    (hgap : Cf * Real.exp (-(δ₂ / 4 * m)) ≤ σ) (hm0 : 0 ≤ m) (hmr : 4 * m < r) (hW : 0 < W)
    (hWb : W ≤ Cw * Real.exp (δ₂ / 32 * r))
    (hCt : Cc * (41 * C₃ / Cf ^ 2 + C₃ ^ (2 / 3 : ℝ) * Bb ^ (1 / 3 : ℝ)) * Cw ≤ Ct) :
    Cc * ((x * (C₃ * Real.exp (-(δ₁ * (r / 2))))) / (5 / 32 * σ) ^ 2 +
      (x * (C₃ * Real.exp (-(δ₁ * (r / 2))))) ^ (2 / 3 : ℝ) * (x * Bb) ^ (1 / 3 : ℝ)) ≤
      Ct * x * Real.exp (-(δ₂ / 8 * m)) / W := by
  obtain ⟨E, hE⟩ : ∃ E, E = Real.exp (-(δ₁ * (r / 2))) := ⟨_, rfl⟩
  have hE0 : 0 < E := by
    rw [hE]
    exact Real.exp_pos _
  rw [← hE]
  obtain ⟨e₁₆, he⟩ : ∃ e₁₆, e₁₆ = Real.exp (-(δ₂ / 16 * r)) := ⟨_, rfl⟩
  have he0 : 0 < e₁₆ := by
    rw [he]
    exact Real.exp_pos _
  have hs0 : 0 < Cf * Real.exp (-(δ₂ / 4 * m)) := by positivity
  have hT1 : (x * (C₃ * E)) / (5 / 32 * σ) ^ 2 ≤ x * (41 * C₃ / Cf ^ 2) * e₁₆ := by
    have h1 : (Cf * Real.exp (-(δ₂ / 4 * m))) ^ 2 ≤ σ ^ 2 := pow_le_pow_left₀ hs0.le hgap 2
    have h2 : E * Real.exp (δ₂ / 2 * m) ≤ e₁₆ := by
      rw [hE, he, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith
    have h3 : (Real.exp (-(δ₂ / 4 * m))) ^ 2 * Real.exp (δ₂ / 2 * m) = 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      have : ((2 : ℕ) : ℝ) * (-(δ₂ / 4 * m)) + δ₂ / 2 * m = 0 := by
        push_cast
        ring
      rw [this, Real.exp_zero]
    rw [div_le_iff₀ (by positivity)]
    have h4 : (5 / 32 * σ) ^ 2 = 25 / 1024 * σ ^ 2 := by ring
    rw [h4]
    have h5 : x * (41 * C₃ / Cf ^ 2) * (E * Real.exp (δ₂ / 2 * m)) * (25 / 1024 * (Cf * Real.exp (-(δ₂ / 4 * m))) ^ 2) =
        x * C₃ * E * (41 * 25 / 1024) * ((Real.exp (-(δ₂ / 4 * m))) ^ 2 * Real.exp (δ₂ / 2 * m)) := by
      field_simp
    rw [h3] at h5
    have h6 : x * (41 * C₃ / Cf ^ 2) * (E * Real.exp (δ₂ / 2 * m)) * (25 / 1024 * (Cf * Real.exp (-(δ₂ / 4 * m))) ^ 2) ≤
        x * (41 * C₃ / Cf ^ 2) * e₁₆ * (25 / 1024 * σ ^ 2) := by
      refine mul_le_mul (mul_le_mul_of_nonneg_left h2 (by positivity)) ?_ (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left h1 (by norm_num)
    have h7 : x * (C₃ * E) ≤ x * C₃ * E * (41 * 25 / 1024) * 1 := by
      have : 0 ≤ x * C₃ * E := by positivity
      nlinarith
    calc x * (C₃ * E) ≤ x * C₃ * E * (41 * 25 / 1024) * 1 := h7
      _ = _ := h5.symm
      _ ≤ _ := h6
  have hT2 : (x * (C₃ * E)) ^ (2 / 3 : ℝ) * (x * Bb) ^ (1 / 3 : ℝ) ≤ x * (C₃ ^ (2 / 3 : ℝ) * Bb ^ (1 / 3 : ℝ)) * e₁₆ := by
    rw [Real.mul_rpow hx.le (by positivity), Real.mul_rpow hC₃.le hE0.le, Real.mul_rpow hx.le hBb.le]
    have h1 : x ^ (2 / 3 : ℝ) * x ^ (1 / 3 : ℝ) = x := by
      rw [← Real.rpow_add hx]
      norm_num
    have h2 : E ^ (2 / 3 : ℝ) ≤ e₁₆ := by
      rw [hE, he, ← Real.exp_mul]
      apply Real.exp_le_exp.mpr
      nlinarith
    calc x ^ (2 / 3 : ℝ) * (C₃ ^ (2 / 3 : ℝ) * E ^ (2 / 3 : ℝ)) * (x ^ (1 / 3 : ℝ) * Bb ^ (1 / 3 : ℝ))
        = (x ^ (2 / 3 : ℝ) * x ^ (1 / 3 : ℝ)) * (C₃ ^ (2 / 3 : ℝ) * Bb ^ (1 / 3 : ℝ)) * E ^ (2 / 3 : ℝ) := by ring
      _ = x * (C₃ ^ (2 / 3 : ℝ) * Bb ^ (1 / 3 : ℝ)) * E ^ (2 / 3 : ℝ) := by rw [h1]
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)
  obtain ⟨A, hA⟩ : ∃ A, A = 41 * C₃ / Cf ^ 2 + C₃ ^ (2 / 3 : ℝ) * Bb ^ (1 / 3 : ℝ) := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by
    rw [hA]
    positivity
  have hsum : Cc * ((x * (C₃ * E)) / (5 / 32 * σ) ^ 2 + (x * (C₃ * E)) ^ (2 / 3 : ℝ) * (x * Bb) ^ (1 / 3 : ℝ)) ≤
      Cc * (x * A * e₁₆) := by
    refine mul_le_mul_of_nonneg_left ((add_le_add hT1 hT2).trans (le_of_eq ?_)) hCc.le
    rw [hA]
    ring
  refine hsum.trans ?_
  rw [le_div_iff₀ hW]
  have h8 : e₁₆ * W ≤ Cw * Real.exp (-(δ₂ / 8 * m)) := by
    calc e₁₆ * W ≤ e₁₆ * (Cw * Real.exp (δ₂ / 32 * r)) := mul_le_mul_of_nonneg_left hWb he0.le
      _ = Cw * (e₁₆ * Real.exp (δ₂ / 32 * r)) := by ring
      _ ≤ Cw * Real.exp (-(δ₂ / 8 * m)) := by
          refine mul_le_mul_of_nonneg_left ?_ hCw.le
          rw [he, ← Real.exp_add]
          apply Real.exp_le_exp.mpr
          nlinarith
  have hC0 : 0 ≤ Cc * x * A := by positivity
  calc Cc * (x * A * e₁₆) * W = (Cc * x * A) * (e₁₆ * W) := by ring
    _ ≤ (Cc * x * A) * (Cw * Real.exp (-(δ₂ / 8 * m))) := mul_le_mul_of_nonneg_left h8 hC0
    _ = (Cc * A * Cw) * (x * Real.exp (-(δ₂ / 8 * m))) := by ring
    _ ≤ Ct * (x * Real.exp (-(δ₂ / 8 * m))) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [hA]
        exact hCt
    _ = _ := by ring
theorem mixedBondDerivative_zero {G : F.GaugeField F.top → ℝ} (W : F.GaugeField F.top) (c : Fin 0 → F.Site F.top × Fin 4) (X : Fin 0 → imaginaryQuaternions) :
    mixedBondDerivative G W c X = G W := by
  unfold mixedBondDerivative
  rw [iteratedFDeriv_zero_apply]
  congr 1
  funext y i
  have h0 : expUnit 0 = 1 := by
    apply Subtype.ext
    simp [expUnit]
  simp [rotatedField, BlockAverages.bondSpread, h0]
theorem agreeOnBall_mono {F' : BlockFrame} {S : Finset F.Cell} {V : F.GaugeField F.top} {S' : Finset F'.Cell} {V' : F'.GaugeField F'.top}
    {Y : F.Cell} {Y' : F'.Cell} {r r' : ℕ} (h : r' ≤ r) (hA : AgreeOnBall S V S' V' Y Y' r) : AgreeOnBall S V S' V' Y Y' r' := by
  obtain ⟨h1, h2, h3, h4⟩ := hA
  have hbox : ∀ u, WithinRadius r' u → WithinRadius r u := fun u hu i => (hu i).trans (by exact_mod_cast h)
  refine ⟨fun i => (h1 i).imp_right fun e => by omega, fun i => (h2 i).imp_right fun e => by omega,
    fun u hu => h3 u (hbox u hu), fun b hb => h4 b ⟨hbox _ hb.1, hbox _ hb.2⟩⟩
end FrameDensity
open FrameDensity in
theorem frameDensityBoundsStatement_holds (hOne : FrameDensityOnTorus) (hTwo : CellEnergyShareLocal)
    (hGS : CellEnergyShareInvariant) (hLC : CellEnergyShareAtMinimizingChart)
    (hCmp : DerivativesCloseOfValuesClose) (hexp : QuaternionExp.ExpUnitLipschitzInjective)
    (hhol : PathHolonomyLipschitz) (hcover : BlocksCoverLowerLevel)
    (hCG : CubicTorusCellGeometry) (hSB : SiteDecomposition) : frameDensityBoundsStatement := by
  classical
  intro a L c Cf C σ₀ ha hL hL40 hc hF
  obtain ⟨hCf, hC, hσ₀, hFH⟩ := hF
  obtain ⟨Bk, hBk, hone⟩ := hOne a L c ha hL hL40 hc C hC
  obtain ⟨C₂, hC₂, htwo⟩ := hTwo a L c ha hL hL40 hc
  obtain ⟨Cc, hCc, hcmp⟩ := hCmp
  have hδ₁ : 0 < c.δ₁ := hc.positivity.1
  have hδ₂ : 0 < c.δ₂ := hc.classical.1.2.2.2.1
  have hs₀ : 0 < c.s₀ := hc.classical.1.2.2.1
  have hlet : 2 ^ 6 * c.δ₂ ≤ c.δ₁ := hc.inequalities.2.1
  have hσA : 16 * c.s₀ ≤ c.σA := hc.inequalities.2.2.1
  have hLpos : 1 ≤ L := hL.pos
  have hLr : (0 : ℝ) < L := by exact_mod_cast hLpos
  obtain ⟨Cw, hCw, hwt⟩ := torusDecayFactor_le_exp c.δ₂ hδ₂ L hLpos
  obtain ⟨C₃, hC₃⟩ : ∃ C₃, C₃ = C₂ + c.N 0 := ⟨_, rfl⟩
  have hN0 : 0 < c.N 0 := hc.positivity.2.2.2.2.2.1 0
  have hC₃0 : 0 < C₃ := by rw [hC₃]; linarith
  obtain ⟨Bb, hBb⟩ : ∃ Bb, Bb = Bk 6 + C₃ := ⟨_, rfl⟩
  have hBb0 : 0 < Bb := by
    rw [hBb]
    have := hBk 6
    linarith
  obtain ⟨A₁, hA₁⟩ : ∃ A₁, A₁ = 41 * C₃ / Cf ^ 2 := ⟨_, rfl⟩
  obtain ⟨A₂, hA₂⟩ : ∃ A₂, A₂ = C₃ ^ (2 / 3 : ℝ) * Bb ^ (1 / 3 : ℝ) := ⟨_, rfl⟩
  have hA₁0 : 0 ≤ A₁ := by
    rw [hA₁]
    positivity
  have hA₂0 : 0 ≤ A₂ := by
    rw [hA₂]
    positivity
  obtain ⟨Ct, hCt⟩ : ∃ Ct, Ct = 2 * Bk 0 * Cf * Cw + Cc * (A₁ + A₂) * Cw + 1 := ⟨_, rfl⟩
  have hCw0 : 0 < Cw := by linarith
  have hBk0 := hBk 0
  have hCt0 : 0 < Ct := by
    rw [hCt]
    positivity
  obtain ⟨σ₁, hσ₁d⟩ : ∃ σ₁, σ₁ = min (σ₀ / 2) (min (2 / 5 * c.s₀) (min (2 / 5) (1 / (128 * (L : ℝ) * C)))) := ⟨_, rfl⟩
  have hCpos : 0 < C := by linarith
  have hσ₁0 : 0 < σ₁ := by
    rw [hσ₁d]
    refine lt_min (by positivity) (lt_min (by positivity) (lt_min (by norm_num) (by positivity)))
  refine ⟨Ct, σ₁, hCt0, hσ₁0, ?_, ?_⟩
  · rw [hσ₁d]
    exact (min_le_left _ _).trans (by linarith)
  intro κ δ σ x m t n₀ hκ hκ' hδ hσ hσσ hx hm hn hgap hx1 hx2
  have hσa : σ ≤ σ₀ / 2 := by
    rw [hσ₁d] at hσσ
    exact hσσ.trans (min_le_left _ _)
  have hσb : σ ≤ 2 / 5 * c.s₀ := by
    rw [hσ₁d] at hσσ
    exact hσσ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hσc : σ ≤ 2 / 5 := by
    rw [hσ₁d] at hσσ
    exact hσσ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hσd : σ ≤ 1 / (128 * (L : ℝ) * C) := by
    rw [hσ₁d] at hσσ
    exact hσσ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨ω, hωd⟩ : ∃ ω, ω = frameDecayBound Cf c.δ₂ m := ⟨_, rfl⟩
  have hω0 : 0 < ω := by
    rw [hωd]
    unfold frameDecayBound
    positivity
  rw [← hωd] at hgap hx1
  have hωσ : ω ≤ σ := by
    have h1 : (2 : ℝ)⁻¹ ^ 10 ≤ 1 := by norm_num
    exact hgap.trans (mul_le_of_le_one_left hσ.le h1)
  have hω1 : ω ≤ 1 := by linarith only [hωσ, hσc]
  have hδle : δ ≤ c.δ₂ / 64 := by
    rw [hδ]
    have : (0 : ℝ) ≤ c.δ₂ := hδ₂.le
    norm_num at hκ' ⊢
    linarith
  have hmr : (0 : ℝ) ≤ m := by positivity
  obtain ⟨E₈, hE₈⟩ : ∃ E₈, E₈ = Real.exp (-(c.δ₂ / 8 * m)) := ⟨_, rfl⟩
  have hE₈0 : 0 < E₈ := by
    rw [hE₈]
    exact Real.exp_pos _
  have hωE : ω ≤ Cf * E₈ := by
    rw [hωd, hE₈]
    unfold frameDecayBound
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hCf.le
    nlinarith
  have hωE2 : ω * Real.exp (c.δ₂ / 8 * m) = Cf * E₈ := by
    rw [hωd, hE₈]
    unfold frameDecayBound
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hTop : ∀ F : BlockFrame, IsCubicTopTorus L t n₀ F → IsBlockTorus L F ∧ Odd F.blockSide ∧ (∀ i, 2 ≤ F.extent i) ∧
      (∀ i j, F.extent i = F.extent j) ∧ F.depth = t := by
    rintro F ⟨h1, h2, n, h3, h4⟩
    refine ⟨⟨h1, n, by omega, h3⟩, by rw [h1]; exact hL, fun i => ?_, fun i j => ?_, h2⟩
    · rw [h3]
      omega
    · rw [h3, h3]
  have hAt : ∀ σ' : ℝ, σ ≤ σ' → σ' ≤ 2 * σ → ∀ F : BlockFrame, IsCubicTopTorus L t n₀ F → ∀ V : F.GaugeField F.top,
      IsSmallCurvature (5 / 4 * σ') V →
      FrameBoundsAt a L c Cf C σ' κ x m t n₀ F V ∧ FramesNearAtTop L a σ' C ω c m V := by
    intro σ' h1 h2 F hF V hV
    obtain ⟨hch, hodd, hs2, hcub, htt⟩ := hTop F hF
    have hgap' : frameDecayBound Cf c.δ₂ m ≤ 2⁻¹ ^ 10 * σ' := by
      rw [← hωd]
      exact hgap.trans (mul_le_mul_of_nonneg_left h1 (by positivity))
    have hH := hFH κ σ' x m t n₀ hκ hκ' (lt_of_lt_of_le hσ h1) (by linarith only [h2, hσa]) hx hm hn hgap'
      (by rw [← hωd]; exact hx1) hx2 F V hF hV
    refine ⟨hH, ?_⟩
    have hσ'1 : σ' ≤ 1 := by linarith only [h2, hσc]
    have hσ'0 : 0 ≤ σ' := by linarith only [h1, hσ]
    refine framesNearAtTop_of_bounds hexp hhol hcover hodd (fun i => by have := hs2 i; omega) hH.2.1
      (fun b hb => by
        rw [hωd]
        exact norm_frameGap_le hCf hσ'0 hσ'1 hH.1 b hb)
      (fun b hb k e X hk hk3 hX => by
        rw [hωd]
        exact norm_bondDeriv_frameGap_le hCf hδ₂.le hH.1 b hb ((hH.2.1 true).analytic b hb) ((hH.2.1 false).analytic b hb) k e X hk hk3 hX)
      ?_ ?_ hω0.le
    · have h3 : σ' ≤ 1 / (64 * (L : ℝ) * C) := by
        have e : 1 / (64 * (L : ℝ) * C) = 2 * (1 / (128 * (L : ℝ) * C)) := by
          field_simp
          ring
        rw [e]
        linarith only [h2, hσd]
      calc C * σ' ≤ C * (1 / (64 * (L : ℝ) * C)) := mul_le_mul_of_nonneg_left h3 hCpos.le
        _ = 1 / (64 * (L : ℝ)) := by
          field_simp
    · linarith only [h2, hσb, hσA, hωσ, hσ, hs₀]
  have hOneAt : ∀ σ' : ℝ, σ ≤ σ' → σ' ≤ 2 * σ → ∀ F : BlockFrame, IsCubicTopTorus L t n₀ F → ∀ V : F.GaugeField F.top,
      IsSmallCurvature (5 / 4 * σ') V → ∀ Y : F.Cell,
      IsBondAnalyticAt (frameDensity false a c.ρA x m Y) V ∧
      (∀ (k : ℕ) (e : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 3 → AreUnitVectors X →
        |bondDeriv (frameDensity false a c.ρA x m Y) V e X| ≤
          x * Bk 0 * ω * Real.exp (-(c.δ₂ / 4 * bondListDistance Y e))) ∧
      ∀ (k : ℕ) (e : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k → AreUnitVectors X →
        |bondDeriv (frameDensity false a c.ρA x m Y) V e X| ≤ x * Bk k := by
    intro σ' h1 h2 F hF V hV Y
    exact hone x σ' ω (5 / 4 * σ') m F V (by linarith only [hx]) (by linarith only [h1, hσ]) (by linarith only [h2, hσb]) hω0.le hω1 (hTop F hF).1 hV
      (hAt σ' h1 h2 F hF V hV).2 Y
  have hsmall : ∀ σ' : ℝ, σ ≤ σ' → σ' ≤ 2 * σ → ∀ F : BlockFrame, IsCubicTopTorus L t n₀ F → ∀ V : F.GaugeField F.top,
      IsSmallCurvature (5 / 4 * σ') V → IsAdmissibleChartPoint L c.σA (fun z i => stepFrame false a c.ρA m (z, i) V) V := by
    intro σ' h1 h2 F hF V hV
    have h3 := (hAt σ' h1 h2 F hF V hV).2.between 1 ⟨zero_le_one, le_rfl⟩
    have e1 : (fun z i => interpolatedFrame 1 a c.ρA m (z, i) V) = fun z i => stepFrame false a c.ρA m (z, i) V := by
      funext z i
      simp [interpolatedFrame]
    rw [e1] at h3
    exact h3
  have hchain : ∀ (s : ℝ) (F : BlockFrame) (V : F.GaugeField F.top), IsBlockTorus L F → 0 < s → s ≤ c.s₀ →
      IsSmallCurvature s V → c.EstimatesAt a s V := fun s F V hch h0 h1 hV =>
    hc.estimates F s V hch h0 (by linarith only [h1, hσA, hs₀]) hV
  have hσs : 5 / 4 * σ ≤ c.s₀ := by linarith only [hσb, hs₀]
  have hσ2 : σ ≤ 2 * σ := by linarith only [hσ]
  have hσ54 : 0 < 5 / 4 * σ := by linarith only [hσ]
  have hW0 : ∀ n : ℕ, 0 < torusDecayFactor L δ n := fun n =>
    mul_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) (Real.exp_pos _)
  have hA12 : 0 ≤ Cc * (A₁ + A₂) * Cw := by positivity
  have hCt2 : 2 * Bk 0 * Cf * Cw ≤ Ct := by
    rw [hCt]
    linarith only [hA12]
  have hBCC : 0 ≤ Bk 0 * Cf * Cw := by positivity
  have hCt1 : Bk 0 * Cf * Cw ≤ Ct := by
    linarith only [hCt2, hBCC]
  have hCt3 : Cc * (41 * C₃ / Cf ^ 2 + C₃ ^ (2 / 3 : ℝ) * Bb ^ (1 / 3 : ℝ)) * Cw ≤ Ct := by
    rw [← hA₁, ← hA₂, hCt]
    have : 0 ≤ 2 * Bk 0 * Cf * Cw := by positivity
    linarith only [this]
  refine ⟨⟨fun F hF Y V hV k e X => ?_, fun F hF Y V γ hV => ?_, fun F hF Y h V hV => ?_⟩,
    fun F hF Y V hV => ?_, fun F hF Y V k e X hV hk1 hk3 hX => ?_, ?_, fun F hF Y V hV => ?_,
    fun F hF star hstar Y V hV => ?_⟩
  · exact ((hOneAt σ le_rfl hσ2 F hF V hV Y).1 k e X).contDiffAt
  · obtain ⟨hch, hodd, hs2, hcub, htt⟩ := hTop F hF
    have hH := hAt σ le_rfl hσ2 F hF V hV
    have hS := hH.1.2.1 false
    change frameDensity false a c.ρA x m Y (gaugeTransform γ V) = frameDensity false a c.ρA x m Y V
    unfold frameDensity
    rw [(hGS a L c ha hL hL40 hc F _ _ V hch (hsmall σ le_rfl hσ2 F hF V hV) Y).1 γ
      (fun b hb => hS.gauge_covariant b hb γ), (hchain _ F V hch hσ54 hσs hV).cellShares.2.2.2.1 Y γ]
  · obtain ⟨hch, hodd, hs2, hcub, htt⟩ := hTop F hF
    have hH := hAt σ le_rfl hσ2 F hF V hV
    have hS := hH.1.2.1 false
    change frameDensity false a c.ρA x m (Y + h) (translateField h V) = frameDensity false a c.ρA x m Y V
    unfold frameDensity
    rw [(hGS a L c ha hL hL40 hc F _ _ V hch (hsmall σ le_rfl hσ2 F hF V hV) Y).2 h
      (fun b hb => hS.translation_invariant b hb h), minimalCellShare_translate hs2 hcub (hchain _ F V hch hσ54 hσs hV).cellShares Y h]
  · exact (hOneAt σ le_rfl hσ2 F hF V hV Y).1
  · obtain ⟨hch, hodd, hs2, hcub, htt⟩ := hTop F hF
    obtain ⟨-, -, hcsym, hctri, -⟩ := hCG.1 F hodd hch.2
    have h1 := (hOneAt σ le_rfl hσ2 F hF V hV Y).2.1 k e X hk3 hX
    have hW := hwt δ hδle (bondSpan Y e)
    refine h1.trans ?_
    rw [← hE₈]
    refine decay_term_le (e := Real.exp (-(c.δ₂ / 4 * bondListDistance Y e))) (d := Real.exp (c.δ₂ / 32 * (bondSpan Y e : ℕ)))
      (by linarith only [hx]) hBk0.le hω0.le hωE hCw0.le (hW0 _) (Real.exp_pos _).le hW ?_ ?_ hE₈0.le
    · rw [← Real.exp_add]
      refine Real.exp_le_one_iff.mpr ?_
      have h2 : (bondSpan Y e : ℝ) ≤ 2 * bondListDistance Y e := by exact_mod_cast bondSpan_le_two_mul hcsym hctri Y e
      have h3 : (0 : ℝ) ≤ bondListDistance Y e := by positivity
      nlinarith only [h2, h3, hδ₂]
    · exact hCt1
  · intro F F' hF hF' Y Y' V V' r k h X hV hV' hA hk hb hX
    obtain ⟨hch, hodd, hs2, hcub, htt⟩ := hTop F hF
    obtain ⟨hch', hodd', hs2', hcub', htt'⟩ := hTop F' hF'
    by_cases hr : r ≤ 4 * m
    · have h1 := (hOneAt σ le_rfl hσ2 F hF V hV Y).2.1 k (bondsAt Y h) X (by omega) hX
      have h2 := (hOneAt σ le_rfl hσ2 F' hF' V' hV' Y').2.1 k (bondsAt Y' h) X (by omega) hX
      have hxB : 0 ≤ x * Bk 0 * ω := by
        have : 0 ≤ x := by linarith only [hx]
        positivity
      have e1 : Real.exp (-(c.δ₂ / 4 * bondListDistance Y (bondsAt Y h))) ≤ 1 := Real.exp_le_one_iff.mpr (by
        have : (0 : ℝ) ≤ bondListDistance Y (bondsAt Y h) := by positivity
        nlinarith only [this, hδ₂])
      have e2 : Real.exp (-(c.δ₂ / 4 * bondListDistance Y' (bondsAt Y' h))) ≤ 1 := Real.exp_le_one_iff.mpr (by
        have : (0 : ℝ) ≤ bondListDistance Y' (bondsAt Y' h) := by positivity
        nlinarith only [this, hδ₂])
      have h3 := h1.trans (mul_le_of_le_one_right hxB e1)
      have h4 := h2.trans (mul_le_of_le_one_right hxB e2)
      have h5 := abs_sub (bondDeriv (frameDensity false a c.ρA x m Y) V (bondsAt Y h) X)
        (bondDeriv (frameDensity false a c.ρA x m Y') V' (bondsAt Y' h) X)
      refine (h5.trans (add_le_add h3 h4)).trans ?_
      rw [← two_mul]
      have hrr : (r : ℝ) ≤ 4 * m := by exact_mod_cast hr
      rw [← hE₈]
      exact near_term_le (by linarith only [hx]) hBk0.le hω0.le hωE2 hCw0.le (hW0 _) (hwt δ hδle r)
        (Real.exp_le_exp.mpr (by nlinarith only [hrr, hδ₂])) hCt2 hE₈0.le
    · have hr4 : 4 * m < r := by omega
      have hrr : 4 * (m : ℝ) < r := by exact_mod_cast hr4
      have hside : ∀ {G : BlockFrame}, (∀ i, 2 ≤ G.extent i) → (∀ i, G.extent i = 0 ∨ 2 * r + 2 < G.extent i) →
          ∀ i, 4 * m + 5 < G.extent i := by
        intro G h1 h2 i
        have h3 := (h2 i).resolve_left (by have := h1 i; omega)
        omega
      have hbig := hside hs2 hA.1
      have hbig' := hside hs2' hA.2.1
      obtain ⟨r', hr'⟩ : ∃ r', r' = r - m - 2 := ⟨_, rfl⟩
      have hr'r : r' ≤ r := by omega
      have hr'1 : 1 ≤ r' := by omega
      have hr'm : r' + m + 2 = r := by omega
      have hr'c : (r' : ℝ) = r - m - 2 := by
        have : ((r' + m + 2 : ℕ) : ℝ) = r := by exact_mod_cast hr'm
        push_cast at this
        linarith only [this]
      have hr'2 : (r : ℝ) / 2 ≤ r' := by
        have hm16 : (16 : ℝ) ≤ m := by exact_mod_cast hm
        rw [hr'c]
        linarith only [hrr, hm16]
      have hrpos : (0 : ℝ) ≤ r := by positivity
      obtain ⟨E, hE⟩ : ∃ E, E = Real.exp (-(c.δ₁ * ((r : ℝ) / 2))) := ⟨_, rfl⟩
      have hE0 : 0 < E := by
        rw [hE]
        exact Real.exp_pos _
      have hx0 : 0 < x := by linarith only [hx]
      have hs2σ : 0 < 5 / 4 * (2 * σ) := by linarith only [hσ]
      have hs2σ' : 5 / 4 * (2 * σ) ≤ c.s₀ := by linarith only [hσb]
      have hval : ∀ (W : F.GaugeField F.top) (W' : F'.GaugeField F'.top), IsSmallCurvature (5 / 4 * (2 * σ)) W →
          IsSmallCurvature (5 / 4 * (2 * σ)) W' → AgreeOnBall (finiteCells F) W (finiteCells F') W' Y Y' r →
          |frameDensity false a c.ρA x m Y W - frameDensity false a c.ρA x m Y' W'| ≤ x * (C₃ * E) := by
        intro W W' hW hW' hAg
        have hH := (hAt (2 * σ) hσ2 le_rfl F hF W hW).1
        have hloc := (hH.2.2.2 F' W' Y Y' r hF' hW' hAg).1 false
        have hsame := hloc.eq_of_far rfl hbig hbig'
        have hchart : ∀ (h o : Fin 4 → ℤ) (i : Fin 4), WithinRadius r' h → o ∈ centredCube L → fineBondAt Y h o i ∈ chordBonds (finiteCells F) →
            (fun z i => stepFrame false a c.ρA m (z, i) W) (fineBondAt Y h o i).1 i =
              (fun z i => stepFrame false a c.ρA m (z, i) W') (fineBondAt Y' h o i).1 i := by
          intro u o i b3 b1 b2
          have b1' : o ∈ centredCube F.blockSide := by rw [hch.1]; exact b1
          obtain ⟨b4, b5⟩ := cellSupDist_fineBondAt_le hSB hodd hs2 (hCG.1 F hodd hch.2).2.2.2.1 Y u o i b3 b1'
          have hb2 : IsFineBondWithinRadius Y r u o i := ⟨b1', b2, fun l => (b3 l).trans (by exact_mod_cast hr'r), by omega, by omega⟩
          have hm' : (m : ℝ) < (r : ℝ) - cellSupDist Y (enclosingCell (fineBondAt Y u o i).1) := by
            have : (cellSupDist Y (enclosingCell (fineBondAt Y u o i).1) : ℝ) ≤ r' := by exact_mod_cast b4
            rw [hr'c] at this
            linarith only [this]
          exact (hsame u o i hb2 hm').1
        have hS := htwo F F' _ _ W W' Y Y' r' hr'1 hch hch' (by rw [htt, htt']) (hsmall (2 * σ) hσ2 le_rfl F hF W hW)
          (hsmall (2 * σ) hσ2 le_rfl F' hF' W' hW') (agreeOnBall_mono hr'r hAg) hchart
        have hloc2 := ((hchain _ F W hch hs2σ hs2σ' hW).locality F' W' Y Y' r (by rw [hch.1, hch'.1]) (by rw [htt, htt'])
          hch'.2 hW' hAg).1 0 Fin.elim0 Fin.elim0 (fun l => l.elim0) (fun l => l.elim0)
        rw [mixedBondDerivative_zero, mixedBondDerivative_zero] at hloc2
        have hfac : derivativeScale (5 / 4 * (2 * σ)) 0 * c.N 0 * Real.exp (-c.δ₁ * r) ≤ c.N 0 * E := by
          have h1 : derivativeScale (5 / 4 * (2 * σ)) 0 ≤ 1 := by
            simp only [derivativeScale, if_true]
            nlinarith only [hσc, hσ]
          have h4 : Real.exp (-c.δ₁ * r) ≤ E := by
            rw [hE]
            apply Real.exp_le_exp.mpr
            nlinarith only [hrpos, hδ₁]
          have h5 : 0 ≤ derivativeScale (5 / 4 * (2 * σ)) 0 := by
            simp only [derivativeScale, if_true]
            positivity
          calc derivativeScale (5 / 4 * (2 * σ)) 0 * c.N 0 * Real.exp (-c.δ₁ * r)
              ≤ 1 * c.N 0 * E := mul_le_mul (mul_le_mul_of_nonneg_right h1 hN0.le) h4 (Real.exp_pos _).le (by positivity)
            _ = c.N 0 * E := by ring
        have hS2 : C₂ * Real.exp (-(c.δ₁ * r')) ≤ C₂ * E := by
          refine mul_le_mul_of_nonneg_left ?_ hC₂.le
          rw [hE]
          apply Real.exp_le_exp.mpr
          nlinarith only [hr'2, hδ₁]
        unfold frameDensity
        have e1 : -x * (cellEnergyShare a Y (fun z i => stepFrame false a c.ρA m (z, i) W) W - minimalCellShare a (finiteCells F) Y W) -
            -x * (cellEnergyShare a Y' (fun z i => stepFrame false a c.ρA m (z, i) W') W' - minimalCellShare a (finiteCells F') Y' W') =
            x * (-((cellEnergyShare a Y (fun z i => stepFrame false a c.ρA m (z, i) W) W -
              cellEnergyShare a Y' (fun z i => stepFrame false a c.ρA m (z, i) W') W') -
              (minimalCellShare a (finiteCells F) Y W - minimalCellShare a (finiteCells F') Y' W'))) := by ring
        rw [e1, abs_mul, abs_of_pos hx0, abs_neg]
        refine mul_le_mul_of_nonneg_left ?_ hx0.le
        have h6 := abs_sub (cellEnergyShare a Y (fun z i => stepFrame false a c.ρA m (z, i) W) W -
              cellEnergyShare a Y' (fun z i => stepFrame false a c.ρA m (z, i) W') W')
              (minimalCellShare a (finiteCells F) Y W - minimalCellShare a (finiteCells F') Y' W')
        refine h6.trans ?_
        rw [hC₃, add_mul]
        exact add_le_add (hS.trans hS2) (hloc2.trans hfac)
      have hres := hcmp F F' (frameDensity false a c.ρA x m Y) (frameDensity false a c.ρA x m Y') (5 / 4 * σ) (5 / 4 * (2 * σ))
        (5 / 32 * σ) (x * (C₃ * E)) (x * Bb) V V' Y Y' r hs2 hs2' (by linarith only [hσ]) (by linarith only [hσc])
        (by linarith only [hσ]) (by positivity) ?_ ?_ ?_ hval hV hV' hA k h X hk hb hX
      · refine hres.trans ?_
        rw [hE]
        have hgapσ : Cf * Real.exp (-(c.δ₂ / 4 * m)) ≤ σ := by
          have e : Cf * Real.exp (-(c.δ₂ / 4 * m)) = ω := by
            rw [hωd]
            rfl
          rw [e]
          exact hωσ
        exact far_term_le hδ₂ hlet hx0 hσ hCf hC₃0 hBb0 hCc hCw0 hgapσ hmr hrr (hW0 _) (hwt δ hδle r) hCt3
      · refine mul_le_mul_of_nonneg_left ?_ hx0.le
        have hE1 : E ≤ 1 := by
          rw [hE]
          refine Real.exp_le_one_iff.mpr ?_
          nlinarith only [hrpos, hδ₁]
        have h1 : C₃ * E ≤ C₃ := mul_le_of_le_one_right hC₃0.le hE1
        have := hBk 6
        rw [hBb]
        linarith only [h1, this]
      · intro W hW
        refine ⟨(hOneAt (2 * σ) hσ2 le_rfl F hF W hW Y).1, fun e X' hX' => ?_⟩
        refine ((hOneAt (2 * σ) hσ2 le_rfl F hF W hW Y).2.2 6 e X' (by norm_num) hX').trans ?_
        refine mul_le_mul_of_nonneg_left ?_ hx0.le
        rw [hBb]
        linarith only [hC₃0]
      · intro W hW
        refine ⟨(hOneAt (2 * σ) hσ2 le_rfl F' hF' W hW Y').1, fun e X' hX' => ?_⟩
        refine ((hOneAt (2 * σ) hσ2 le_rfl F' hF' W hW Y').2.2 6 e X' (by norm_num) hX').trans ?_
        refine mul_le_mul_of_nonneg_left ?_ hx0.le
        rw [hBb]
        linarith only [hC₃0]
  · have h1 := (hOneAt σ le_rfl hσ2 F hF V hV Y).2.1 0 Fin.elim0 Fin.elim0 (by omega) (fun l => l.elim0)
    rw [bondDeriv_zero] at h1
    have hl : bondListDistance Y (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) = 0 := by simp [bondListDistance]
    rw [hl] at h1
    simp only [Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, mul_one] at h1
    refine h1.trans ?_
    rw [← hE₈]
    have h2 := decay_term_le (x := x) (B := Bk 0) (ω := ω) (Cf := Cf) (Cw := Cw) (E₈ := E₈) (Ct := Ct) (W := 1) (e := 1) (d := 1)
      (by linarith only [hx]) hBk0.le hω0.le hωE hCw0.le one_pos zero_le_one (by linarith only [hCw]) (by norm_num) hCt1 hE₈0.le
    simpa using h2
  · obtain ⟨hch, hodd, hs2, hcub, htt⟩ := hTop F hF
    have hsame : (fun z i => stepFrame star a c.ρA m (z, i) V) = fun z i => stepFrame true a c.ρA m (z, i) V := by
      funext z i
      rcases hstar with rfl | hb
      · rfl
      · cases star
        · exact stepFrame_eq_of_not_large hb _ V
        · rfl
    have h1 := (hc.classical.2 F _ V hch hσ54 hσs hV).1
    have h2 := (hchain _ F V hch hσ54 hσs hV).cellShares.2.2.1
    have h3 := hLC F a c.ρA _ V (by linarith only [ha]) hodd hs2 h1 h2 Y
    have h4 : cellEnergyShare a Y (fun z i => stepFrame true a c.ρA m (z, i) V) V = minimalCellShare a (finiteCells F) Y V := h3
    change frameDensity star a c.ρA x m Y V = 0
    unfold frameDensity
    rw [hsame, h4, sub_self, mul_zero]
end YangMills.Construction.ColdStepAtMirrorFrames
end
