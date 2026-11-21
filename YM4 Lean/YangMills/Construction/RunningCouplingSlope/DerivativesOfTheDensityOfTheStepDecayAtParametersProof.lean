import YangMills.Construction.ColdStepAtMirrorFrames.ClassicalChainAtGivenNumbers
import YangMills.Construction.RunningCouplingSlope.ContoursAtTheLeastFieldHaveKernels
import YangMills.Construction.RunningCouplingSlope.DerivativesOfTheDensityOfTheStepDecayAtParameters
import YangMills.Construction.RunningCouplingSlope.HaarDensityAtTheLeastFieldHasKernels
import YangMills.Construction.RunningCouplingSlope.TraceAtTheLeastFieldHasKernels
import YangMills.Construction.SummableBoundsOfTheFlow.BondsOfACellAreFew
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesOfATopFamilyOnTori
import YangMills.Construction.SummableBoundsOfTheFlow.ObservablesInTheLawsBetweenProof
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
noncomputable section
open scoped Topology
open BlockAverages ColdStepAtMirrorFrames Interpolation IteratedDerivative Estimates TorusFields TorusLumps
  ReferenceDensity RenormalizationStepParameters ColdChain
namespace RunningCouplingSlope
variable {F : BlockFrame}
private theorem cellSupDist_le_cellSetDiameter {P : Finset F.Cell} {x y : F.Cell} (hx : x ∈ P) (hy : y ∈ P) :
    cellSupDist x y ≤ cellSetDiameter P := by apply _root_.YangMills.Construction.Interpolation.ObservableSizes.cellSupDist_le_cellSetDiameter <;> assumption
private theorem bondSpan_le_cellSetDiameter {k : ℕ} (Y : F.Cell) (c : Fin k → F.Site F.top × Fin 4) :
    bondSpan Y c ≤ cellSetDiameter ({Y} ∪ topBondCells c) := by
  have hY : Y ∈ ({Y} ∪ topBondCells c : Finset F.Cell) := by simp
  have hc : ∀ l, (c l).1 ∈ ({Y} ∪ topBondCells c : Finset F.Cell) := fun l =>
    Finset.mem_union_right _ (Finset.mem_image.2 ⟨l, Finset.mem_univ _, rfl⟩)
  unfold bondSpan
  refine max_le (Finset.sup_le fun l _ => ?_) (Finset.sup_le fun l _ => Finset.sup_le fun l' _ => ?_)
  · exact cellSupDist_le_cellSetDiameter hY (hc l)
  · exact cellSupDist_le_cellSetDiameter (hc l) (hc l')
abbrev _root_.YangMills.SharedProofs.p63056 := @bondSpan_le_cellSetDiameter
private theorem card_innerBonds_at_cell_le_four (Y : F.Cell)
    [DecidablePred fun c : F.Site F.top × Fin 4 => c.1 = Y] :
    ((innerBonds (finiteCells F) F.top).filter fun c => c.1 = Y).card ≤ 4 := by
  have h := Finset.card_le_card_of_injOn (s := (innerBonds (finiteCells F) F.top).filter fun c => c.1 = Y)
    (t := (Finset.univ : Finset (Fin 4))) (fun c => c.2) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) (by
      intro p hp q hq e
      have h1 := (Finset.mem_filter.1 (Finset.mem_coe.1 hp)).2
      have h2 := (Finset.mem_filter.1 (Finset.mem_coe.1 hq)).2
      exact Prod.ext (h1.trans h2.symm) e)
  simpa using h
abbrev _root_.YangMills.SharedProofs.p2730 := @card_innerBonds_at_cell_le_four
private theorem exists_decay_at_admissible_parameters (hTr : TraceKernelBounds)
    (hC : contourLogDerivBoundStatement) (hJ : haarLogRatioDerivBoundStatement)
    (hP : BondDerivSumProductRules) (hO : TopFamilyDerivBoundsOnTori)
    (hB : cellBondsCardStatement) (a : ℝ) (L : ℕ) (c : ColdChainParameters) (ha : 1 ≤ a) (hL : Odd L)
    (hL40 : 2 ^ 40 ≤ L) (hc : c.Admissible a L) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧ ∀ s : ℝ, IsReachableColdness c L s → ∀ (t n : ℕ) [NeZero n], 64 ≤ n →
      ∀ (y : TorusSite n) (W : TorusField n), IsCold s W →
        ∀ (k : ℕ) (b : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
        1 ≤ k → k ≤ 3 → AreUnitVectors X →
        |mixedDeriv (stepDensityFamily a c.ρA c.lam L t n y) W b X| ≤ C * Real.exp (-(r * supportDiam y b)) := by
  obtain ⟨rT, CT, hrT, hCT, gT⟩ := hTr a L c ha hL hL40 hc
  obtain ⟨Dc, hDc, gC⟩ := hC a L c ha hL hL40 hc
  obtain ⟨Dh, hDh, gJ⟩ := hJ a L c ha hL hL40 hc
  have hδ : 0 < c.δ₁ := hc.positivity.1
  set DC : ℝ := ∑ m ∈ Finset.range 4, Dc m with hDC
  set DH : ℝ := ∑ m ∈ Finset.range 4, Dh m with hDH
  have hDCa : ∀ m, m ≤ 3 → Dc m ≤ DC := fun m hm =>
    Finset.single_le_sum (f := Dc) (fun b _ => (hDc b).le) (Finset.mem_range.2 (by omega))
  have hDHa : ∀ m, m ≤ 3 → Dh m ≤ DH := fun m hm =>
    Finset.single_le_sum (f := Dh) (fun b _ => (hDh b).le) (Finset.mem_range.2 (by omega))
  have hDC0 : 0 ≤ DC := Finset.sum_nonneg fun b _ => (hDc b).le
  have hDH0 : 0 ≤ DH := Finset.sum_nonneg fun b _ => (hDh b).le
  set r : ℝ := min rT (c.δ₁ / 2) with hr
  have hr0 : 0 < r := lt_min hrT (by positivity)
  have hr1 : r ≤ rT := min_le_left _ _
  have hr2 : r ≤ c.δ₁ / 2 := min_le_right _ _
  have hC0 : 0 < CT + 6 * DC + 4 * (L : ℝ) ^ 4 * DH := by positivity
  refine ⟨r, CT + 6 * DC + 4 * (L : ℝ) ^ 4 * DH, hr0, hC0, fun s hs t n _ hn y W hW k b X h1 h3 hX => ?_⟩
  refine hO L t 64 3 s (fun _ Y V => stepDensity a c.ρA c.lam Y V)
    (fun _ m => (CT + 6 * DC + 4 * (L : ℝ) ^ 4 * DH) * Real.exp (-(r * m))) ?_ n hn y W hW k b X h1 h3 hX
  clear hW h1 h3 hX b X k W y hn
  intro F hF Y V k e X hV h1 h3 hX
  classical
  obtain ⟨hFL, -, m, hside, hm⟩ := hF
  have hchain : IsBlockTorus L F := ⟨hFL, m, hm, hside⟩
  have hside2 : ∀ i, 2 ≤ F.extent i := by
    intro i
    rw [hside i]
    omega
  have hodd : Odd F.blockSide := hFL ▸ hL
  obtain ⟨hsum, hsmul, -⟩ := hP F V k e X
  set S : ℕ := cellSetDiameter ({Y} ∪ topBondCells e) with hSdef
  let Gc : (F.Site F.top × Fin 4) → F.GaugeField F.top → ℝ := fun c₀ V' =>
    Real.log ‖contourAverage (fieldAboveFrame true a c.ρA 0 V' 0) c₀‖
  have hGc : ∀ c₀ : F.Site F.top × Fin 4, c₀.1 = Y → ContDiffAlongBonds k (Gc c₀) V e X ∧
      |bondDeriv (Gc c₀) V e X| ≤ DC * Real.exp (-(c.δ₁ / 2 * S)) := by
    intro c₀ hc₀
    obtain ⟨p, q⟩ := gC F s V c₀ k e X hchain hs hV h1 hX
    rw [hc₀] at q
    exact ⟨p, q.trans (mul_le_mul_of_nonneg_right (hDCa _ h3) (Real.exp_pos _).le)⟩
  let Gh : ↥(chordBonds (finiteCells F)) → F.GaugeField F.top → ℝ := fun b₀ V' =>
    haarLogRatio (coordsAboveFrame true a c.ρA 0 V' 0 b₀.1.1 b₀.1.2)
  have hGh : ∀ b₀ : ↥(chordBonds (finiteCells F)), enclosingCell b₀.1.1 = Y → ContDiffAlongBonds k (Gh b₀) V e X ∧
      |bondDeriv (Gh b₀) V e X| ≤ DH * Real.exp (-(c.δ₁ / 2 * S)) := by
    intro b₀ hb₀
    obtain ⟨p, q⟩ := gJ F s V b₀ k e X hchain hs hV h1 hX
    rw [hb₀] at q
    exact ⟨p, q.trans (mul_le_mul_of_nonneg_right (hDHa _ h3) (Real.exp_pos _).le)⟩
  obtain ⟨sI, bI⟩ := gT F s V Y k e X hchain hs hV (by omega) hX
  let Bs := (innerBonds (finiteCells F) F.top).filter fun c => c.1 = Y
  let Cb := Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1 = Y
  let Iy : F.GaugeField F.top → ℝ := fun V' => ∫ τ in (0 : ℝ)..1, hessianCellShare a c.ρA c.lam Y V' τ
  have hfun : (fun V' => stepDensity a c.ρA c.lam Y V') = fun V' =>
      ((-(1 / 2 : ℝ)) * Iy V' + (3 / 2 : ℝ) * ∑ c₀ ∈ Bs, Gc c₀ V') + ∑ b ∈ Cb, Gh b V' := by
    funext V'
    unfold stepDensity
    simp only [Cb, Bs, Finset.sum_filter]
    rfl
  have sC : ∀ c₀ ∈ Bs, ContDiffAlongBonds k (Gc c₀) V e X := fun c₀ h => (hGc c₀ (Finset.mem_filter.1 h).2).1
  have sH : ∀ b ∈ Cb, ContDiffAlongBonds k (Gh b) V e X := fun b h => (hGh b (Finset.mem_filter.1 h).2).1
  have sCs : ContDiffAlongBonds k (fun V' => ∑ c₀ ∈ Bs, Gc c₀ V') V e X := ContDiffAt.sum sC
  have sHs : ContDiffAlongBonds k (fun V' => ∑ b ∈ Cb, Gh b V') V e X := ContDiffAt.sum sH
  have sI' : ContDiffAlongBonds k Iy V e X := sI
  have a1 : ContDiffAlongBonds k (fun V' => (-(1 / 2 : ℝ)) * Iy V') V e X := contDiffAt_const.mul sI'
  have a2 : ContDiffAlongBonds k (fun V' => (3 / 2 : ℝ) * ∑ c₀ ∈ Bs, Gc c₀ V') V e X :=
    contDiffAt_const.mul sCs
  have a3 : ContDiffAlongBonds k
      (fun V' => (-(1 / 2 : ℝ)) * Iy V' + (3 / 2 : ℝ) * ∑ c₀ ∈ Bs, Gc c₀ V') V e X :=
    ContDiffAt.add a1 a2
  have add2 : ∀ G H : F.GaugeField F.top → ℝ, ContDiffAlongBonds k G V e X → ContDiffAlongBonds k H V e X →
      bondDeriv (fun V' => G V' + H V') V e X = bondDeriv G V e X + bondDeriv H V e X := by
    intro G H hG hH
    have h := hsum Bool Finset.univ (fun b => if b then G else H) (by
      intro b _
      cases b
      · simpa using hH
      · simpa using hG)
    simpa [Fintype.sum_bool] using h
  show |bondDeriv (fun V' => stepDensity a c.ρA c.lam Y V') V e X| ≤ _
  rw [hfun, add2 _ _ a3 sHs, add2 _ _ a1 a2, hsmul _ _ sI', hsmul _ _ sCs, hsum _ _ _ sC, hsum _ _ _ sH]
  set E : ℝ := Real.exp (-(r * S)) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg _
  have e7 : Real.exp (-(rT * S)) ≤ E := Real.exp_le_exp.2 (by nlinarith)
  have e8 : Real.exp (-(c.δ₁ / 2 * S)) ≤ E := Real.exp_le_exp.2 (by nlinarith)
  have t1 : |(-(1 / 2 : ℝ)) * bondDeriv Iy V e X| ≤ CT * E := by
    rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have h1 : |bondDeriv Iy V e X| ≤ CT * E :=
      bI.trans (mul_le_mul_of_nonneg_left e7 hCT.le)
    have h2 : 0 ≤ |bondDeriv Iy V e X| := abs_nonneg _
    linarith
  have hcB : ((Bs.card : ℕ) : ℝ) ≤ 4 := by exact_mod_cast card_innerBonds_at_cell_le_four Y
  have hcC : ((Cb.card : ℕ) : ℝ) ≤ 4 * (L : ℝ) ^ 4 := by
    have h := hB F hodd hside2 Y
    rw [hFL] at h
    exact_mod_cast h
  have t2 : |(3 / 2 : ℝ) * ∑ c₀ ∈ Bs, bondDeriv (Gc c₀) V e X| ≤ 6 * DC * E := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
    have h1 : |∑ c₀ ∈ Bs, bondDeriv (Gc c₀) V e X| ≤ (Bs.card : ℝ) * (DC * E) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [← nsmul_eq_mul]
      refine Finset.sum_le_card_nsmul _ _ _ fun c₀ h => ?_
      exact (hGc c₀ (Finset.mem_filter.1 h).2).2.trans (mul_le_mul_of_nonneg_left e8 hDC0)
    have h2 : (Bs.card : ℝ) * (DC * E) ≤ 4 * (DC * E) :=
      mul_le_mul_of_nonneg_right hcB (mul_nonneg hDC0 hE0)
    linarith
  have t3 : |∑ b ∈ Cb, bondDeriv (Gh b) V e X| ≤ 4 * (L : ℝ) ^ 4 * DH * E := by
    have h1 : |∑ b ∈ Cb, bondDeriv (Gh b) V e X| ≤ (Cb.card : ℝ) * (DH * E) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [← nsmul_eq_mul]
      refine Finset.sum_le_card_nsmul _ _ _ fun b h => ?_
      exact (hGh b (Finset.mem_filter.1 h).2).2.trans (mul_le_mul_of_nonneg_left e8 hDH0)
    have h2 : (Cb.card : ℝ) * (DH * E) ≤ 4 * (L : ℝ) ^ 4 * (DH * E) :=
      mul_le_mul_of_nonneg_right hcC (mul_nonneg hDH0 hE0)
    linarith
  have hspan : (bondSpan Y e : ℝ) ≤ S := by exact_mod_cast bondSpan_le_cellSetDiameter Y e
  have hfin : E ≤ Real.exp (-(r * (bondSpan Y e : ℝ))) := by
    refine Real.exp_le_exp.2 ?_
    have := mul_le_mul_of_nonneg_left hspan hr0.le
    linarith
  calc _ ≤ |(-(1 / 2 : ℝ)) * bondDeriv Iy V e X + (3 / 2 : ℝ) * ∑ c₀ ∈ Bs, bondDeriv (Gc c₀) V e X| +
        |∑ b ∈ Cb, bondDeriv (Gh b) V e X| := abs_add_le _ _
    _ ≤ |(-(1 / 2 : ℝ)) * bondDeriv Iy V e X| + |(3 / 2 : ℝ) * ∑ c₀ ∈ Bs, bondDeriv (Gc c₀) V e X| +
        |∑ b ∈ Cb, bondDeriv (Gh b) V e X| := by
      gcongr
      exact abs_add_le _ _
    _ ≤ CT * E + 6 * DC * E + 4 * (L : ℝ) ^ 4 * DH * E := add_le_add (add_le_add t1 t2) t3
    _ = (CT + 6 * DC + 4 * (L : ℝ) ^ 4 * DH) * E := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hfin hC0.le
theorem densityDerivativesDecay_of_kernel_bounds (hG : AdmissibleParametersExist)
    (hTr : TraceKernelBounds) (hC : contourLogDerivBoundStatement)
    (hJ : haarLogRatioDerivBoundStatement) (hP : BondDerivSumProductRules)
    (hO : TopFamilyDerivBoundsOnTori) (hB : cellBondsCardStatement) :
    DensityDerivativesDecay := by
  have key : ∀ l : ChainParameters, ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
      (1 ≤ l.coupling → Odd l.side → 2 ^ 40 ≤ l.side →
        ColdChainConstants l.coupling l.δ₁ l.side l.lam l.ρA l.σA l.cg l.N →
        ∀ s : ℝ, 0 < s → s ≤ l.σA → 2 ^ 10 * (l.side : ℝ) * (l.N 0 + 1) * s ≤ 9 / 8 →
        ∀ (t n : ℕ) [NeZero n], 64 ≤ n → ∀ (y : TorusSite n) (W : TorusField n), IsCold s W →
          ∀ (k : ℕ) (b : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 →
            AreUnitVectors X →
            |mixedDeriv (stepDensityFamily l.coupling l.ρA l.lam l.side t n y) W b X| ≤
              C * Real.exp (-(r * supportDiam y b))) := by
    intro l
    by_cases hg : 1 ≤ l.coupling ∧ Odd l.side ∧ 2 ^ 40 ≤ l.side ∧
        ColdChainConstants l.coupling l.δ₁ l.side l.lam l.ρA l.σA l.cg l.N
    · obtain ⟨ha, hL, hL40, hch⟩ := hg
      obtain ⟨c, -, -, hlam, hρ, hσ, -, hN, hc⟩ :=
        hG l.coupling l.δ₁ l.side l.lam l.ρA l.σA l.cg l.N ha hL hch
      obtain ⟨r, C, hr, hC0, h⟩ :=
        exists_decay_at_admissible_parameters hTr hC hJ hP hO hB l.coupling l.side c ha hL hL40 hc
      refine ⟨r, C, hr, hC0, fun _ _ _ _ s h0 h1 h2 t n _ hn y W hW k b X hk1 hk3 hX => ?_⟩
      have hs : IsReachableColdness c l.side s := ⟨h0, by rw [hσ]; exact h1, by rw [hN]; exact h2⟩
      have h3 := h s hs t n hn y W hW k b X hk1 hk3 hX
      rwa [hρ, hlam] at h3
    · exact ⟨1, 1, one_pos, one_pos, fun h1 h2 h3 h4 => absurd ⟨h1, h2, h3, h4⟩ hg⟩
  choose r C hr hC0 hkey using key
  refine ⟨r, C, hr, hC0, fun T hT t n _ hn y W hW k b X h1 h3 hX => ?_⟩
  have hσ0 := hT.σ_pos
  have hσA : 9 / 8 * T.threshold ≤ T.σA := by
    have := hT.σ_le
    linarith
  have hsmall : 2 ^ 10 * (T.side : ℝ) * (T.N 0 + 1) * (9 / 8 * T.threshold) ≤ 9 / 8 := by
    have := hT.σ_L
    linarith
  exact hkey T.toChainParameters hT.a_ge hT.L_odd hT.L_ge hT.chain (9 / 8 * T.threshold) (by positivity) hσA
    hsmall t n hn y W hW k b X h1 h3 hX
end RunningCouplingSlope
end
end YangMills.Construction
