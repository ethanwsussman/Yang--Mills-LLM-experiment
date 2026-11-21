import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
import YangMills.Construction.ColdStepAtMirrorFrames.BlockEnergyOnTwoTori
import YangMills.Construction.ColdStepAtMirrorFrames.KernelsOfTheBlockEnergy
import YangMills.Construction.ColdStepAtMirrorFrames.SumsOverCellsAndBonds
import YangMills.Construction.ColdStepAtMirrorFrames.SumsThatAgreeNearAPoint
import YangMills.Construction.ResponseInTheExpansion.EntriesOnTwoTori
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames DirectionalDerivatives
namespace ChartResponse
variable {F : BlockFrame}
private theorem expUnit_zero_aux : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
private theorem shiftField_inl (p : F.Site F.depth × Fin 4 × imaginaryQuaternions) (θ : ℝ) (V : F.GaugeField F.top) :
    shiftField (Sum.inl p : ChartDirection F) θ V = V := by
  funext y i
  simp [shiftField, leftTranslate, directionMove, expUnit_zero_aux]
private theorem shiftCoordinates_zero (r : ChartDirection F) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) :
    shiftCoordinates r 0 w = w := by
  funext x i
  simp [shiftCoordinates]
private theorem evalAlong_base (Φ : (F.Site F.depth → Fin 4 → imaginaryQuaternions) → F.GaugeField F.top → ℝ)
    (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (p q : F.Site F.depth × Fin 4 × imaginaryQuaternions) (s u : ℝ) :
    evalAlong Φ w V ![Sum.inl p, Sum.inl q] ![s, u] = Φ (shiftTwice p q s u w) V := by
  unfold evalAlong shiftTwice shiftCoordinates
  have e : (fun y i => ∑ l, (![s, u] : Fin 2 → ℝ) l • directionMove ((![Sum.inl p, Sum.inl q] : Fin 2 → ChartDirection F) l) y i) =
      fun _ _ => (0 : imaginaryQuaternions) := by
    funext y i
    simp [Fin.sum_univ_two, directionMove]
  have e' : leftTranslate (fun _ _ => (0 : imaginaryQuaternions)) V = V := by
    funext y i
    simp [leftTranslate, expUnit_zero_aux]
  rw [e, e']
  congr 1
  funext x i
  simp [Fin.sum_univ_two, add_assoc]
private theorem evalAlong_shiftTwice (Φ : (F.Site F.depth → Fin 4 → imaginaryQuaternions) → F.GaugeField F.top → ℝ)
    (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (p q : F.Site F.depth × Fin 4 × imaginaryQuaternions) (s u : ℝ) (σ : Fin 2 → ℝ) :
    evalAlong Φ (shiftTwice p q s u w) V ![Sum.inl p, Sum.inl q] σ =
      evalAlong Φ w V ![Sum.inl p, Sum.inl q] (σ + ![s, u]) := by
  unfold evalAlong shiftTwice shiftCoordinates
  congr 1
  · funext x i
    simp only [Fin.sum_univ_two, Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    module
  · congr 1
    funext y i
    simp [Fin.sum_univ_two, directionMove]
private theorem secondDifference_near_entry (hM : MixedDerivLipschitzAndSecondDifference)
    (Φ : (F.Site F.depth → Fin 4 → imaginaryQuaternions) → F.GaugeField F.top → ℝ)
    (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (p q : F.Site F.depth × Fin 4 × imaginaryQuaternions) (h B : ℝ) (hh : 0 ≤ h)
    (hk : ∀ s u, 0 ≤ s → s ≤ h → 0 ≤ u → u ≤ h →
      AnalyticAt ℝ (evalAlong Φ (shiftTwice p q s u w) V ![Sum.inl p, Sum.inl q]) 0 ∧
      (∀ r : F.Site F.depth × Fin 4 × imaginaryQuaternions, r = p ∨ r = q →
        AnalyticAt ℝ (evalAlong Φ (shiftTwice p q s u w) V ![Sum.inl r, Sum.inl p, Sum.inl q]) 0 ∧
        |mixedDerivAlong Φ (shiftTwice p q s u w) V ![Sum.inl r, Sum.inl p, Sum.inl q]| ≤ B)) :
    |Φ (shiftTwice p q h h w) V - Φ (shiftTwice p q h 0 w) V - Φ (shiftTwice p q 0 h w) V + Φ (shiftTwice p q 0 0 w) V -
      h ^ 2 * mixedDerivAlong Φ w V ![Sum.inl p, Sum.inl q]| ≤ 2 * B * h * h ^ 2 := by
  set f := evalAlong Φ w V ![Sum.inl p, Sum.inl q] with hf
  have hB : 0 ≤ B := (abs_nonneg _).trans ((hk 0 0 le_rfl hh le_rfl hh).2 p (Or.inl rfl)).2
  have hsec : ∀ s u, 0 ≤ s → s ≤ h → 0 ≤ u → u ≤ h → AnalyticAt ℝ f ![s, u] ∧
      fderiv ℝ (fderiv ℝ f) ![s, u] (Pi.single 0 1) (Pi.single 1 1) =
        mixedDerivAlong Φ (shiftTwice p q s u w) V ![Sum.inl p, Sum.inl q] := by
    intro s u h0 h1 h2 h3
    have e : evalAlong Φ (shiftTwice p q s u w) V ![Sum.inl p, Sum.inl q] = fun σ => f (σ + ![s, u]) :=
      funext fun σ => evalAlong_shiftTwice Φ w V p q s u σ
    constructor
    · have h := (hk s u h0 h1 h2 h3).1
      rw [e] at h
      have e2 : f = fun σ => (fun σ => f (σ + ![s, u])) (σ - ![s, u]) := by
        funext σ
        show f σ = f (σ - ![s, u] + ![s, u])
        rw [sub_add_cancel]
      rw [e2]
      have h4 : AnalyticAt ℝ (fun σ : Fin 2 → ℝ => σ - ![s, u]) ![s, u] := analyticAt_id.sub analyticAt_const
      have h5 : AnalyticAt ℝ (fun σ => f (σ + ![s, u])) ((fun σ : Fin 2 → ℝ => σ - ![s, u]) ![s, u]) := by
        simpa using h
      exact AnalyticAt.comp (g := fun σ => f (σ + ![s, u])) (f := fun σ : Fin 2 → ℝ => σ - ![s, u]) h5 h4
    · unfold mixedDerivAlong
      rw [e, iteratedFDeriv_comp_add_right, iteratedFDeriv_two_apply]
      simp
  have hmove : ∀ s u, 0 ≤ s → s ≤ h → 0 ≤ u → u ≤ h →
      |mixedDerivAlong Φ (shiftTwice p q s u w) V ![Sum.inl p, Sum.inl q] -
        mixedDerivAlong Φ w V ![Sum.inl p, Sum.inl q]| ≤ 2 * B * h := by
    intro s u h0 h1 h2 h3
    have e1 : ∀ θ, shiftCoordinates (Sum.inl p : ChartDirection F) θ w = shiftTwice p q θ 0 w := by
      intro θ
      simp [shiftTwice, shiftCoordinates_zero]
    have s1 := hM.1 F Φ w V p q (Sum.inl p) B s h0 (fun θ a b => by
      rw [shiftField_inl, e1]
      have := (hk θ 0 a (b.trans h1) le_rfl hh).2 p (Or.inl rfl)
      exact this)
    have e2 : ∀ θ, shiftCoordinates (Sum.inl q : ChartDirection F) θ (shiftTwice p q s 0 w) = shiftTwice p q s θ w := by
      intro θ
      simp [shiftTwice, shiftCoordinates_zero]
    have s2 := hM.1 F Φ (shiftTwice p q s 0 w) V p q (Sum.inl q) B u h2 (fun θ a b => by
      rw [shiftField_inl, e2]
      have := (hk s θ h0 h1 a (b.trans h3)).2 q (Or.inr rfl)
      exact this)
    rw [shiftField_inl, e1] at s1
    rw [shiftField_inl, e2] at s2
    have h4 := abs_sub_le (mixedDerivAlong Φ (shiftTwice p q s u w) V ![Sum.inl p, Sum.inl q])
      (mixedDerivAlong Φ (shiftTwice p q s 0 w) V ![Sum.inl p, Sum.inl q]) (mixedDerivAlong Φ w V ![Sum.inl p, Sum.inl q])
    have h5 : B * s ≤ B * h := by gcongr
    have h6 : B * u ≤ B * h := by gcongr
    linarith
  have := hM.2 f h (2 * B * h) (mixedDerivAlong Φ w V ![Sum.inl p, Sum.inl q]) hh fun s u a b c d => by
    obtain ⟨h1, h2⟩ := hsec s u a b c d
    exact ⟨h1, by rw [h2]; exact hmove s u a b c d⟩
  simp only [hf, evalAlong_base] at this
  exact this
private theorem iteratedFDeriv_finset_sum_at_zero {ι : Type} (S : Finset ι) (g : ι → (Fin 2 → ℝ) → ℝ) (k : ℕ)
    (hg : ∀ Y ∈ S, AnalyticAt ℝ (g Y) 0) :
    iteratedFDeriv ℝ k (fun σ => ∑ Y ∈ S, g Y σ) 0 = ∑ Y ∈ S, iteratedFDeriv ℝ k (g Y) 0 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact congrFun (iteratedFDeriv_zero_fun (𝕜 := ℝ) (E := Fin 2 → ℝ) (F := ℝ)) 0
  | insert a S ha ih =>
    have e : (fun σ => ∑ Y ∈ insert a S, g Y σ) = g a + fun σ => ∑ Y ∈ S, g Y σ := by
      funext σ
      simp [Finset.sum_insert ha]
    have h1 : ContDiffAt ℝ k (g a) 0 := (hg a (Finset.mem_insert_self _ _)).contDiffAt.of_le (by exact_mod_cast le_top)
    have h2 : ContDiffAt ℝ k (fun σ => ∑ Y ∈ S, g Y σ) 0 :=
      ContDiffAt.sum fun Y hY => (hg Y (Finset.mem_insert_of_mem hY)).contDiffAt.of_le (by exact_mod_cast le_top)
    rw [e, iteratedFDeriv_add_apply h1 h2, Finset.sum_insert ha, ih fun Y hY => hg Y (Finset.mem_insert_of_mem hY)]
private theorem chartMixedDeriv_eq_sum (hS : sumCellSharesEqAction) (a : ℝ) (ha : 0 ≤ a) (hodd : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i)
    (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top) (q : Fin 2 → ChartDirection F)
    (han : ∀ Y ∈ finiteCells F, AnalyticAt ℝ (cellEnergyAlong a Y w V q) 0) :
    chartMixedDeriv a w V q = ∑ Y ∈ finiteCells F, cellEnergyKernel a Y w V q := by
  have e : chartRestriction a w V q = fun σ => ∑ Y ∈ finiteCells F, cellEnergyAlong a Y w V q σ := by
    funext σ
    exact ((hS F a _ _ ha hodd hs).2).symm
  unfold chartMixedDeriv cellEnergyKernel
  rw [e, iteratedFDeriv_finset_sum_at_zero _ _ _ han]
  simp
private theorem siteOfCoords_add (j : ℕ) (g h : Fin 4 → ℤ) :
    siteOfCoords (F := F) j g + siteOfCoords j h = siteOfCoords j (g + h) := by
  funext i
  simp [siteOfCoords]
private theorem fineBondAt_translate (Y : F.Cell) (g h o : Fin 4 → ℤ) (i : Fin 4) :
    fineBondAt (Y + siteOfCoords F.top g) h o i = fineBondAt Y (g + h) o i := by
  unfold fineBondAt
  rw [add_assoc, siteOfCoords_add]
private theorem cellSupDist_translate_le (hs : ∀ i, 2 ≤ F.extent i) (Y : F.Cell) (g : Fin 4 → ℤ) (R : ℕ)
    (hg : ∀ i, |g i| ≤ (R : ℤ)) :
    cellSupDist (Y + siteOfCoords F.top g) Y ≤ R := by
  unfold cellSupDist
  refine Finset.sup_le fun i _ => ?_
  have hne : NeZero (F.period F.top i) := ⟨by
    rw [BlockOffsets.period_top]
    have := hs i
    omega⟩
  have h1 := CellSums.residueNorm_le_natAbs_of_cast ((Y + siteOfCoords F.top g : F.Cell) i - Y i) (g i)
    (by simp [siteOfCoords])
  unfold CellSums.residueNorm at h1
  refine h1.trans ?_
  have h2 := hg i
  rw [Int.abs_eq_natAbs] at h2
  exact_mod_cast h2
abbrev _root_.YangMills.SharedProofs.p92070 := @cellSupDist_translate_le
set_option maxHeartbeats 2000000 in
theorem hessianEntryAgreeOnTwoTori (hM : MixedDerivLipschitzAndSecondDifference) (hKb : CellEnergyKernelBound)
    (hB : CellEnergyShareLocal) (hS : sumCellSharesEqAction) (hN : DecayingSumsClose) :
    HessianEntryAgreeOnTwoTori := by
  intro a L c ha hL hL0 hc ϱ hϱ
  obtain ⟨Ck, hCk, hker⟩ := hKb a L c ha hL hL0 hc
  obtain ⟨Cb, hCb, hbl⟩ := hB a L c ha hL hL0 hc
  have hδ : 0 < c.δ₁ := hc.positivity.1
  obtain ⟨M, hM0, -, hsum⟩ := hN (c.δ₁ / 8) (by positivity)
  set ϱ₁ := min ϱ 1 with hϱ₁
  have hϱ₁0 : 0 < ϱ₁ := lt_min hϱ one_pos
  have hϱ₁1 : ϱ₁ ≤ 1 := min_le_right _ _
  set T₀ := 4 * Cb / ϱ₁ ^ 2 + 4 * Ck 3 with hT₀
  have hT₀0 : 0 < T₀ := by
    have := hCk 3
    positivity
  have hC2 := hCk 2
  have hC3 := hCk 3
  refine ⟨(T₀ + 2 * Ck 2) * M, by positivity, ?_⟩
  intro F F' w w' V V' Y Y' r p q p' q' hr hF hF' ht hp hq hp' hq' hpts hag hw hd hd'
  classical
  have hFL : F.blockSide = L := hF.1
  have hFL' : F'.blockSide = L := hF'.1
  have hodd : Odd F.blockSide := hFL ▸ hL
  have hodd' : Odd F'.blockSide := hFL' ▸ hL
  obtain ⟨a1, a2, a3, a4⟩ := id hag
  obtain ⟨n, hn64, hside⟩ := hF.2
  obtain ⟨n', hn64', hside'⟩ := hF'.2
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by rw [hside i]; omega
  have hs' : ∀ i, 2 ≤ F'.extent i := fun i => by rw [hside' i]; omega
  have hsr : ∀ i, 2 * r + 2 < F.extent i := fun i => by
    rcases a1 i with h | h
    · have := hs i
      omega
    · exact h
  have hsr' : ∀ i, 2 * r + 2 < F'.extent i := fun i => by
    rcases a2 i with h | h
    · have := hs' i
      omega
    · exact h
  set R := r / 2 with hR
  set r₁ := r - R with hr₁
  have hr₁1 : 1 ≤ r₁ := by omega
  have hr₁r : (r : ℝ) ≤ 2 * r₁ := by
    have : r ≤ 2 * r₁ := by omega
    exact_mod_cast this
  set E := Real.exp (-(c.δ₁ / 8 * r)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : E ≤ 1 := Real.exp_le_one_iff.2 (by
    have : (0 : ℝ) ≤ r := by positivity
    have : 0 ≤ c.δ₁ / 8 * r := by positivity
    linarith)
  set h := ϱ₁ * E with hh
  have hh0 : 0 < h := by positivity
  have hhϱ : h ≤ ϱ := by
    have : h ≤ ϱ₁ * 1 := mul_le_mul_of_nonneg_left hE1 hϱ₁0.le
    have h2 : ϱ₁ ≤ ϱ := min_le_left _ _
    linarith
  have hsm : ∀ s u, 0 ≤ s → s ≤ h → 0 ≤ u → u ≤ h → IsAdmissibleChartPoint L c.σA (shiftTwice p q s u w) V ∧
      IsAdmissibleChartPoint L c.σA (shiftTwice p' q' s u w') V' := fun s u a b c' d =>
    hpts s u a (b.trans hhϱ) c' (d.trans hhϱ)
  have hbase : IsAdmissibleChartPoint L c.σA w V ∧ IsAdmissibleChartPoint L c.σA w' V' := by
    have := hpts 0 0 le_rfl hϱ.le le_rfl hϱ.le
    have e1 : shiftTwice p q 0 0 w = w := by
      funext x i
      simp [shiftTwice, shiftCoordinates]
    have e2 : shiftTwice p' q' 0 0 w' = w' := by
      funext x i
      simp [shiftTwice, shiftCoordinates]
    rwa [e1, e2] at this
  have third : ∀ {G : BlockFrame} (hG : IsBlockTorus L G) (w₁ : G.Site G.depth → Fin 4 → imaginaryQuaternions)
      (V₁ : G.GaugeField G.top) (Z : G.Cell)
      (p₁ q₁ : G.Site G.depth × Fin 4 × imaginaryQuaternions), ‖p₁.2.2‖ = 1 → ‖q₁.2.2‖ = 1 →
      (∀ s u, 0 ≤ s → s ≤ h → 0 ≤ u → u ≤ h → IsAdmissibleChartPoint L c.σA (shiftTwice p₁ q₁ s u w₁) V₁) →
      ∀ s u, 0 ≤ s → s ≤ h → 0 ≤ u → u ≤ h →
        AnalyticAt ℝ (evalAlong (cellEnergyShare a Z) (shiftTwice p₁ q₁ s u w₁) V₁ ![Sum.inl p₁, Sum.inl q₁]) 0 ∧
        (∀ r' : G.Site G.depth × Fin 4 × imaginaryQuaternions, r' = p₁ ∨ r' = q₁ →
          AnalyticAt ℝ (evalAlong (cellEnergyShare a Z) (shiftTwice p₁ q₁ s u w₁) V₁
            ![Sum.inl r', Sum.inl p₁, Sum.inl q₁]) 0 ∧
          |mixedDerivAlong (cellEnergyShare a Z) (shiftTwice p₁ q₁ s u w₁) V₁
            ![Sum.inl r', Sum.inl p₁, Sum.inl q₁]| ≤ Ck 3) := by
    intro G hG w₁ V₁ Z p₁ q₁ hp₁ hq₁ hsm₁ s u h0 h1 h2 h3
    have hpt := hsm₁ s u h0 h1 h2 h3
    refine ⟨(hker G _ V₁ hG hpt Z 2 ![Sum.inl p₁, Sum.inl q₁]).1, fun r' hr' => ?_⟩
    obtain ⟨h4, h5⟩ := hker G _ V₁ hG hpt Z 3 ![Sum.inl r', Sum.inl p₁, Sum.inl q₁]
    refine ⟨h4, ?_⟩
    have hu : ∀ l, ‖directionVector ((![Sum.inl r', Sum.inl p₁, Sum.inl q₁] : Fin 3 → ChartDirection G) l)‖ = 1 := by
      intro l
      fin_cases l
      · rcases hr' with e | e <;> subst e <;> simpa [directionVector]
      · simpa [directionVector] using hp₁
      · simpa [directionVector] using hq₁
    refine (h5 (by norm_num) hu).trans ?_
    have : Real.exp (-(c.δ₁ * directionReach Z
        (![Sum.inl r', Sum.inl p₁, Sum.inl q₁] : Fin 3 → ChartDirection G))) ≤ 1 :=
      Real.exp_le_one_iff.2 (by
        have : 0 ≤ c.δ₁ * (directionReach Z
          (![Sum.inl r', Sum.inl p₁, Sum.inl q₁] : Fin 3 → ChartDirection G) : ℝ) := by positivity
        linarith)
    nlinarith
  have near : ∀ g : Fin 4 → ℤ, (∀ i, |g i| ≤ (R : ℤ)) →
      |cellEnergyKernel a (Y + siteOfCoords F.top g) w V ![Sum.inl p, Sum.inl q] -
        cellEnergyKernel a (Y' + siteOfCoords F'.top g) w' V' ![Sum.inl p', Sum.inl q']| ≤ T₀ * E := by
    intro g hg
    set Y₁ := Y + siteOfCoords F.top g with hY₁
    set Y₁' := Y' + siteOfCoords F'.top g with hY₁'
    have hin : ∀ h' : Fin 4 → ℤ, WithinRadius r₁ h' → WithinRadius r (g + h') := by
      intro h' hh' i
      have h1 := hg i
      have h2 := hh' i
      have h3 : |(g + h') i| ≤ |g i| + |h' i| := abs_add_le _ _
      have h4 : (r₁ : ℤ) + (R : ℤ) = r := by omega
      simp only [Pi.add_apply] at h3 ⊢
      linarith
    have hag₁ : AgreeOnBall (finiteCells F) V (finiteCells F') V' Y₁ Y₁' r₁ := by
      refine ⟨fun i => Or.inr ?_, fun i => Or.inr ?_, fun h' hh' => ?_, fun b hb => ?_⟩
      · have := hsr i
        omega
      · have := hsr' i
        omega
      · rw [hY₁, hY₁', add_assoc, add_assoc, siteOfCoords_add, siteOfCoords_add]
        exact a3 _ (hin h' hh')
      · have e1 : Y₁ + siteOfCoords F.top b.1 = Y + siteOfCoords F.top (g + b.1) := by
          rw [hY₁, add_assoc, siteOfCoords_add]
        have e2 : Y₁' + siteOfCoords F'.top b.1 = Y' + siteOfCoords F'.top (g + b.1) := by
          rw [hY₁', add_assoc, siteOfCoords_add]
        rw [e1, e2]
        have hb' : BondWithinRadius r ((g + b.1), b.2) := by
          refine ⟨hin _ hb.1, ?_⟩
          have := hin _ hb.2
          rwa [← add_assoc] at this
        exact a4 _ hb'
    have hval : ∀ s u, 0 ≤ s → s ≤ h → 0 ≤ u → u ≤ h →
        |cellEnergyShare a Y₁ (shiftTwice p q s u w) V - cellEnergyShare a Y₁' (shiftTwice p' q' s u w') V'| ≤
          Cb * (E ^ 4) := by
      intro s u h0 h1 h2 h3
      obtain ⟨hsm1, hsm2⟩ := hsm s u h0 h1 h2 h3
      have := hbl F F' _ _ V V' Y₁ Y₁' r₁ hr₁1 hF hF' ht hsm1 hsm2 hag₁ (fun h' o i hh' ho hmem => by
        have hmem' : fineBondAt Y (g + h') o i ∈ chordBonds (finiteCells F) := by
          rw [← fineBondAt_translate]
          exact hmem
        obtain ⟨e1, e2, e3⟩ := hw (g + h') o i (hin h' hh') ho hmem'
        rw [hY₁, hY₁', fineBondAt_translate, fineBondAt_translate]
        simp only [shiftTwice, shiftCoordinates]
        rw [e1, e2, e3])
      refine this.trans ?_
      have e : E ^ 4 = Real.exp (-(c.δ₁ / 2 * r)) := by
        rw [hE, ← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      rw [e]
      have h5 : -(c.δ₁ * (r₁ : ℝ)) ≤ -(c.δ₁ / 2 * r) := by nlinarith
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h5) hCb.le
    have D := secondDifference_near_entry hM (cellEnergyShare a Y₁) w V p q h (Ck 3) hh0.le
      (third hF w V Y₁ p q hp hq (fun s u a' b c' d => (hsm s u a' b c' d).1))
    have D' := secondDifference_near_entry hM (cellEnergyShare a Y₁') w' V' p' q' h (Ck 3) hh0.le
      (third hF' w' V' Y₁' p' q' hp' hq' (fun s u a' b c' d => (hsm s u a' b c' d).2))
    have v1 := abs_le.1 (hval h h hh0.le le_rfl hh0.le le_rfl)
    have v2 := abs_le.1 (hval h 0 hh0.le le_rfl le_rfl hh0.le)
    have v3 := abs_le.1 (hval 0 h le_rfl hh0.le hh0.le le_rfl)
    have v4 := abs_le.1 (hval 0 0 le_rfl hh0.le le_rfl hh0.le)
    have d1 := abs_le.1 D
    have d2 := abs_le.1 D'
    set x := cellEnergyKernel a Y₁ w V ![Sum.inl p, Sum.inl q] -
      cellEnergyKernel a Y₁' w' V' ![Sum.inl p', Sum.inl q'] with hx
    have ex : mixedDerivAlong (cellEnergyShare a Y₁) w V ![Sum.inl p, Sum.inl q] =
        cellEnergyKernel a Y₁ w V ![Sum.inl p, Sum.inl q] := rfl
    have ex' : mixedDerivAlong (cellEnergyShare a Y₁') w' V' ![Sum.inl p', Sum.inl q'] =
        cellEnergyKernel a Y₁' w' V' ![Sum.inl p', Sum.inl q'] := rfl
    rw [ex] at d1
    rw [ex'] at d2
    have hbound : h ^ 2 * |x| ≤ 4 * (Cb * E ^ 4) + 4 * Ck 3 * h * h ^ 2 := by
      have e : h ^ 2 * |x| = |h ^ 2 * x| := by rw [abs_mul, abs_of_nonneg (sq_nonneg h)]
      rw [e, hx, mul_sub]
      exact abs_le.2 ⟨by linarith [d1.1, d1.2, d2.1, d2.2], by linarith [d1.1, d1.2, d2.1, d2.2]⟩
    have hgoal : h ^ 2 * |x| ≤ h ^ 2 * (T₀ * E) := by
      refine hbound.trans ?_
      have e1 : h ^ 2 * (T₀ * E) = 4 * Cb * E ^ 3 + 4 * Ck 3 * ϱ₁ ^ 2 * E ^ 3 := by
        rw [hh, hT₀]
        field_simp
      rw [e1, hh]
      have e2 : Cb * E ^ 4 ≤ Cb * E ^ 3 := by
        have : E ^ 4 ≤ E ^ 3 := pow_le_pow_of_le_one hE0.le hE1 (by norm_num)
        gcongr
      have e3 : Ck 3 * (ϱ₁ * E) * (ϱ₁ * E) ^ 2 ≤ Ck 3 * ϱ₁ ^ 2 * E ^ 3 := by
        have : ϱ₁ ^ 3 ≤ ϱ₁ ^ 2 := pow_le_pow_of_le_one hϱ₁0.le hϱ₁1 (by norm_num)
        have e4 : Ck 3 * (ϱ₁ * E) * (ϱ₁ * E) ^ 2 = Ck 3 * ϱ₁ ^ 3 * E ^ 3 := by ring
        rw [e4]
        gcongr
      nlinarith
    exact le_of_mul_le_mul_left hgoal (by positivity)
  have far : ∀ {G : BlockFrame} (hG : IsBlockTorus L G) (w₁ : G.Site G.depth → Fin 4 → imaginaryQuaternions)
      (V₁ : G.GaugeField G.top) (Z : G.Cell)
      (p₁ q₁ : G.Site G.depth × Fin 4 × imaginaryQuaternions), ‖p₁.2.2‖ = 1 → ‖q₁.2.2‖ = 1 →
      IsAdmissibleChartPoint L c.σA w₁ V₁ →
      8 * cellSupDist (enclosingCell p₁.1) Z ≤ r → (∀ i, 2 ≤ G.extent i) →
      ∀ Y₁, R < cellSupDist Y₁ Z → |cellEnergyKernel a Y₁ w₁ V₁ ![Sum.inl p₁, Sum.inl q₁]| ≤
        (Ck 2 * Real.exp (-(c.δ₁ / 16 * r))) * Real.exp (-(c.δ₁ / 8 * cellSupDist Y₁ Z)) := by
    intro G hG w₁ V₁ Z p₁ q₁ hp₁ hq₁ hpt hd₁ hsG Y₁ hY
    obtain ⟨-, h5⟩ := hker G _ V₁ hG hpt Y₁ 2 ![Sum.inl p₁, Sum.inl q₁]
    have hu : ∀ l, ‖directionVector ((![Sum.inl p₁, Sum.inl q₁] : Fin 2 → ChartDirection G) l)‖ = 1 := by
      intro l
      fin_cases l
      · simpa [directionVector] using hp₁
      · simpa [directionVector] using hq₁
    refine (h5 (by norm_num) hu).trans ?_
    have hre : cellSupDist Y₁ (enclosingCell p₁.1) ≤
        directionReach Y₁ (![Sum.inl p₁, Sum.inl q₁] : Fin 2 → ChartDirection G) := by
      have := Finset.le_sup (f := fun l : Fin 2 =>
          cellSupDist Y₁ (directionCell ((![Sum.inl p₁, Sum.inl q₁] : Fin 2 → ChartDirection G) l)))
        (Finset.mem_univ 0)
      simpa [directionReach, directionCell] using this
    have htri := CellSums.cellSupDist_triangle (F := G) (fun i => by have := hsG i; omega) Y₁ (enclosingCell p₁.1) Z
    have h1 : (cellSupDist Y₁ Z : ℝ) ≤ directionReach Y₁ (![Sum.inl p₁, Sum.inl q₁] : Fin 2 → ChartDirection G) +
        cellSupDist (enclosingCell p₁.1) Z := by
      have : cellSupDist Y₁ Z ≤ directionReach Y₁ (![Sum.inl p₁, Sum.inl q₁] : Fin 2 → ChartDirection G) +
          cellSupDist (enclosingCell p₁.1) Z := by omega
      exact_mod_cast this
    have h2 : 8 * (cellSupDist (enclosingCell p₁.1) Z : ℝ) ≤ r := by exact_mod_cast hd₁
    have h3 : (r : ℝ) ≤ 2 * cellSupDist Y₁ Z := by
      have : r ≤ 2 * cellSupDist Y₁ Z := by omega
      exact_mod_cast this
    rw [mul_assoc, ← Real.exp_add]
    gcongr
    nlinarith
  have hsumG := chartMixedDeriv_eq_sum hS a (by linarith) hodd hs w V ![Sum.inl p, Sum.inl q]
    (fun Y₁ _ => (hker F w V hF hbase.1 Y₁ 2 _).1)
  have hsumG' := chartMixedDeriv_eq_sum hS a (by linarith) hodd' hs' w' V' ![Sum.inl p', Sum.inl q']
    (fun Y₁ _ => (hker F' w' V' hF' hbase.2 Y₁ 2 _).1)
  rw [hsumG, hsumG']
  have hfin := hsum F F' (fun Y₁ => cellEnergyKernel a Y₁ w V ![Sum.inl p, Sum.inl q])
    (fun Y₁ => cellEnergyKernel a Y₁ w' V' ![Sum.inl p', Sum.inl q']) Y Y' R (T₀ * Real.exp (-(c.δ₁ / 16 * r)))
    (Ck 2 * Real.exp (-(c.δ₁ / 16 * r))) hs hs'
    (fun i => by have := hsr i; omega) (fun i => by have := hsr' i; omega) (by positivity) (by positivity)
    (fun g hg => by
      refine (near g hg).trans ?_
      rw [mul_assoc, ← Real.exp_add]
      refine mul_le_mul_of_nonneg_left ?_ hT₀0.le
      rw [hE]
      apply Real.exp_le_exp.2
      have h1 : (cellSupDist (Y + siteOfCoords F.top g) Y : ℝ) ≤ R := by
        exact_mod_cast cellSupDist_translate_le hs Y g R hg
      have h2 : (R : ℝ) * 2 ≤ r := by
        have : R * 2 ≤ r := by omega
        exact_mod_cast this
      have h3 := mul_le_mul_of_nonneg_left h1 hδ.le
      have h4 := mul_le_mul_of_nonneg_left h2 hδ.le
      linarith)
    (far hF w V Y p q hp hq hbase.1 hd hs) (far hF' w' V' Y' p' q' hp' hq' hbase.2 hd' hs')
  refine hfin.trans (le_of_eq ?_)
  ring
end ChartResponse
end YangMills.Construction
end
