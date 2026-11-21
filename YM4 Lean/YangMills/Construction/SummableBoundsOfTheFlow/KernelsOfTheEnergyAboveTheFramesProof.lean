import YangMills.Construction.HoleBesideASecondHole.EnergyInTheChart
import YangMills.Construction.ResponseInTheExpansion.CalculusOfTwoMoves
import YangMills.Construction.RunningCouplingSlope.EnergyAtTheLeastFieldHasKernelsProof
import YangMills.Construction.SummableBoundsOfTheFlow.DecayOfTheFramesBetween
import YangMills.Construction.SummableBoundsOfTheFlow.KernelsOfTheEnergyAboveTheFrames
import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceAtParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction.Interpolation
section spread
variable {F : BlockFrame}
private theorem chartedField_congr {w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (V : F.GaugeField F.top) (h : ∀ x i, ¬ IsAxialTreeBond (x, i) → w x i = w' x i) :
    chartedField w V = chartedField w' V := by apply _root_.YangMills.SharedProofs.p16263 <;> assumption
end spread
section core
variable {F : BlockFrame} {l j : ℕ}
private theorem abs_jointMixedDeriv_le_of_frames (a : ℝ)
    (fr : F.Site F.depth × Fin 4 → F.GaugeField F.top → imaginaryQuaternions) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) (b : Fin l → ↥(chordBonds (finiteCells F)))
    (u : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin j → F.Site F.top × Fin 4)
    (X : Fin j → imaginaryQuaternions)
    (hchart : ∀ d, ¬ IsAxialTreeBond d → d ∈ chordBonds (finiteCells F))
    (hana : ∀ d ∈ chordBonds (finiteCells F), IsBondAnalyticAt (fr d) V)
    {K Ck : ℕ → ℝ} {κ₂ δ₁ r₀ Cb : ℝ} (hK : ∀ k, 0 ≤ K k) (hκ : 0 ≤ κ₂)
    (hdec : ∀ d ∈ chordBonds (finiteCells F), ∀ (k : ℕ) (c' : Fin k → F.Site F.top × Fin 4)
      (X' : Fin k → imaginaryQuaternions), 1 ≤ k → AreUnitVectors X' →
      ‖bondDeriv (fr d) V c' X'‖ ≤ K k * Real.exp (-(κ₂ * bondListDistance (enclosingCell d.1) c')))
    (hu : ∀ i, ‖u i‖ = 1) (hX : AreUnitVectors X) (hCk : ∀ k, 0 ≤ Ck k)
    (hker : ∀ (k : ℕ) (q : Fin k → ChartDirection F),
      AnalyticAt ℝ (chartRestriction a (fun z i => fr (z, i) V + stepCoordinates η z i) V q) 0 ∧
      (2 ≤ k → (∀ m, ‖directionVector (q m)‖ = 1) →
        |chartMixedDeriv a (fun z i => fr (z, i) V + stepCoordinates η z i) V q| ≤
          Ck k * Real.exp (-(δ₁ * directionDiameter q))))
    (hz : ∀ y : F.Cell, cellSupDist y y = 0) (hsym : ∀ x y : F.Cell, cellSupDist x y = cellSupDist y x)
    (htri : ∀ x y z : F.Cell, cellSupDist x z ≤ cellSupDist x y + cellSupDist y z) (hCb : 0 ≤ Cb)
    (hsum : ∀ z : F.Cell, ∑ β : ↥(chordBonds (finiteCells F)),
      Real.exp (-(κ₂ / 2 * cellSupDist (enclosingCell β.1.1) z)) ≤ Cb)
    (hl : 2 ≤ l) (hr₀ : 0 ≤ r₀) (h1 : r₀ ≤ δ₁) (h2 : 4 * r₀ ≤ κ₂) :
    ContDiffAt ℝ (l + j : ℕ) (jointDisplacement (fun ζ V' => chartedEnergy a
      (fun z i => fr (z, i) V' + stepCoordinates ζ z i) V') η V b u c X) 0 ∧
    |jointMixedDeriv (fun ζ V' => chartedEnergy a (fun z i => fr (z, i) V' + stepCoordinates ζ z i) V')
        η V b u c X| ≤
      (∑ c' : OrderedFinpartition (l + j), Ck c'.length * (∏ m, (K (c'.partSize m) + 1)) *
        (3 * Cb + j) ^ c'.length) *
        Real.exp (-(r₀ * cellSetDiameter (chordBondCells b ∪ topBondCells c))) := by apply _root_.YangMills.SharedProofs.p59928 (κ₂ := κ₂) <;> assumption
end core
section table
private theorem eventually_parameter_bounds (g : ℝ → ℕ → ColdChainParameters → ℝ)
    (hg : ∀ a L c, 1 ≤ a → Odd L → ColdChainParameters.Admissible c a L → 0 < g a L c) :
    EventuallyInParameters fun T => 1 ≤ T.a ∧ Odd T.L ∧ 2 ^ 40 ≤ T.L ∧
      T.chainParams.Admissible T.a T.L ∧ 0 < T.σ ∧ T.σ ≤ g T.a T.L T.chainParams ∧ 64 ≤ T.n₀ := by
  intro a ha
  refine ⟨2 ^ 40, fun L hL hL₀ c hc => ⟨0, fun Ct _ => ⟨1, one_pos, fun κ _ _ => ⟨1, one_pos,
    fun η₃ _ _ _ => ⟨0, fun nss _ => ⟨g a L c, hg a L c ha hL hc, fun σ h0 hσ p hp => ⟨0,
      fun Cs _ E _ => ⟨64, fun n₀ hn => ⟨0, fun CE _ => ⟨0, fun y₁ _ => ?_⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  exact ⟨ha, hL, hL₀, hc, h0, hσ, hn⟩
private theorem norm_stepCoordinates_le {F : BlockFrame} (η : StepVariable (finiteCells F)) {r : ℝ}
    (h0 : 0 ≤ r) (hη : ∀ b, ‖η b‖ ≤ r) (x : F.Site F.depth) (i : Fin 4) :
    ‖stepCoordinates η x i‖ ≤ r := by apply _root_.YangMills.Construction.SecondOrderMoves.norm_stepCoordinates_le <;> assumption
private theorem exists_kernel_constant (hK : ChartEnergyKernelBound)
    (hgeo : CubicTorusCellGeometry) (hcov : BlocksCoverLowerLevel)
    (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) :
    ∃ D₀ : ℕ → ℕ → ℝ, (∀ l j, 0 < D₀ l j) ∧
      (1 ≤ T.a → Odd T.L → 2 ^ 40 ≤ T.L → T.chainParams.Admissible T.a T.L →
        ∀ (F : BlockFrame) (fr : F.Site F.depth × Fin 4 → F.GaugeField F.top → imaginaryQuaternions)
          (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)), IsBlockTorus T.L F →
          IsAdmissibleChartPoint T.L T.chainParams.σA
            (fun z i => fr (z, i) V + stepCoordinates η z i) V →
          (∀ d ∈ chordBonds (finiteCells F), IsBondAnalyticAt (fr d) V) →
          (∀ d ∈ chordBonds (finiteCells F), ∀ (k : ℕ) (c' : Fin k → F.Site F.top × Fin 4)
            (X' : Fin k → imaginaryQuaternions), 1 ≤ k → AreUnitVectors X' →
            ‖bondDeriv (fr d) V c' X'‖ ≤
              16 ^ k * T.chainParams.Kk k *
                Real.exp (-(T.chainParams.κ₂ * bondListDistance (enclosingCell d.1) c'))) →
          ∀ (l j : ℕ) (b : Fin l → ↥(chordBonds (finiteCells F)))
            (u : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin j → F.Site F.top × Fin 4)
            (X : Fin j → imaginaryQuaternions),
            2 ≤ l → (∀ i, ‖u i‖ = 1) → AreUnitVectors X →
            ContDiffAt ℝ (l + j : ℕ) (jointDisplacement (fun ζ V' => chartedEnergy T.a
              (fun z i => fr (z, i) V' + stepCoordinates ζ z i) V') η V b u c X) 0 ∧
            |jointMixedDeriv (fun ζ V' => chartedEnergy T.a
                (fun z i => fr (z, i) V' + stepCoordinates ζ z i) V') η V b u c X| ≤
              D₀ l j * Real.exp (-(T.chainParams.δ₂ *
                cellSetDiameter (chordBondCells b ∪ topBondCells c)))) := by
  by_cases hgood : 1 ≤ T.a ∧ Odd T.L ∧ 2 ^ 40 ≤ T.L ∧ T.chainParams.Admissible T.a T.L
  · obtain ⟨ha, hL, hL40, hc⟩ := hgood
    obtain ⟨Ck, hCk, hker⟩ := hK T.a T.L T.chainParams ha hL hL40 hc
    obtain ⟨-, -, -, hδ₂, hκδ, -, -, hKk⟩ := hc.classical.1
    have hκ₂ : 0 < T.chainParams.κ₂ := by nlinarith
    obtain ⟨Cg, hCg, hsum⟩ := hgeo.2 (T.chainParams.κ₂ / 2) (by linarith)
    have hL0 : 0 < T.L := by omega
    let Cb : ℝ := Cg * (T.L : ℝ) ^ 4
    have hCb : 0 ≤ Cb := by positivity
    let K : ℕ → ℝ := fun k => 16 ^ k * T.chainParams.Kk k
    have hK0 : ∀ k, 0 ≤ K k := fun k => mul_nonneg (by positivity) (hKk k).le
    let B : ℕ → ℕ → ℝ := fun l j => ∑ c' : OrderedFinpartition (l + j), Ck c'.length *
      (∏ m, (K (c'.partSize m) + 1)) * (3 * Cb + j) ^ c'.length
    have hB : ∀ l j, 0 ≤ B l j := fun l j => Finset.sum_nonneg fun c' _ =>
      mul_nonneg (mul_nonneg (hCk _).le (Finset.prod_nonneg fun m _ => by
        have := hK0 (c'.partSize m); linarith)) (by positivity)
    refine ⟨fun l j => B l j + 1, fun l j => by have := hB l j; linarith, ?_⟩
    intro _ _ _ _ F fr V η hF hsmall hana hdec l j b u c X hl hu hX
    have hodd : Odd F.blockSide := hF.1 ▸ hL
    have hcub := hF.2
    obtain ⟨n, hn64, hside⟩ := id hcub
    have hpos : ∀ i, 0 < F.extent i := fun i => by rw [hside i]; omega
    have hall := hcov F hodd hpos
    have hbond : ∀ d : F.Site F.depth × Fin 4, d ∈ fineBonds F := fun d => by
      simp [fineBonds, hall]
    have hchart : ∀ d, ¬ IsAxialTreeBond d → d ∈ chordBonds (finiteCells F) := fun d hd => by
      have : d.1 + unitStep F.depth d.2 ∈ sitesOfCells (finiteCells F) F.depth := hall _
      simp [chordBonds, innerBonds, hall, hd]
    have hg1 := hgeo.1 F hodd hcub
    have hsum' : ∀ z : F.Cell, ∑ β : ↥(chordBonds (finiteCells F)),
        Real.exp (-(T.chainParams.κ₂ / 2 * cellSupDist (enclosingCell β.1.1) z)) ≤ Cb := by
      intro z
      have h1 := hsum F hodd hcub z
      rw [hF.1] at h1
      rw [Finset.sum_coe_sort (chordBonds (finiteCells F))
        (fun d => Real.exp (-(T.chainParams.κ₂ / 2 * cellSupDist (enclosingCell d.1) z)))]
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (fun d _ => hbond d)
        fun _ _ _ => (Real.exp_pos _).le) h1
    have hcore := abs_jointMixedDeriv_le_of_frames T.a fr V η b u c X hchart hana (K := K) (Ck := Ck)
      (κ₂ := T.chainParams.κ₂) (δ₁ := T.chainParams.δ₁) (r₀ := T.chainParams.δ₂) (Cb := Cb) hK0
      hκ₂.le hdec hu hX (fun k => (hCk k).le)
      (fun k q => by
        have := hker F _ V hF hsmall k q
        exact ⟨this.1, fun h2 hq => this.2 h2 hq⟩)
      (fun z => by simp [cellSupDist]) hg1.2.2.1 hg1.2.2.2.1 hCb hsum' hl hδ₂.le
      (by have := hc.inequalities.2.1; nlinarith) (by nlinarith)
    refine ⟨hcore.1, hcore.2.trans ?_⟩
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    show B l j ≤ B l j + 1
    linarith
  · refine ⟨fun _ _ => 1, fun _ _ => one_pos, ?_⟩
    intro h1 h2 h3 h4
    exact absurd ⟨h1, h2, h3, h4⟩ hgood
end table
theorem energyKernelBounds_holds (hD : SummableBounds.interpolatedFrameDecayStatement)
    (hK : ChartEnergyKernelBound) (hgeo : CubicTorusCellGeometry)
    (hcov : BlocksCoverLowerLevel) : EnergyKernelBounds := by
  obtain ⟨Cz, hCz, hD⟩ := hD
  choose D₀ hpos hprop using exists_kernel_constant hK hgeo hcov
  refine ⟨D₀, hpos, ?_⟩
  let g : ℝ → ℕ → ColdChainParameters → ℝ := fun a L c =>
    min (1 / (64 * (L : ℝ) * (Cz a L c + 1))) (c.σA / (16 * (Cz a L c + 2)))
  have hg : ∀ a L c, 1 ≤ a → Odd L → ColdChainParameters.Admissible c a L → 0 < g a L c := by
    intro a L c _ hL hc
    have hL0 : (0 : ℝ) < L := by
      have : 0 < L := hL.pos
      exact_mod_cast this
    have h1 := hCz a L c
    have h2 := hc.positivity.2.2.2.1
    exact lt_min (by positivity) (by positivity)
  refine EventuallyInParameters.mono
    (EventuallyInParameters.and hD (eventually_parameter_bounds g hg)) ?_
  rintro T ⟨gD, ha, hL, hL40, hc, hσ0, hσ, hn⟩ x t F V s η hx hF hV hs hs' hη l j b u c X hl hu hX
  obtain ⟨hFL, hFt, n, hside, hn₀⟩ := hF
  have hF' : IsCubicTopTorus T.L t T.n₀ F := ⟨hFL, hFt, n, hside, hn₀⟩
  have hodd : Odd F.blockSide := hFL ▸ hL
  have hchain : IsBlockTorus T.L F := ⟨hFL, n, hn.trans hn₀, hside⟩
  have hsides : ∀ i, 2 ≤ F.extent i := fun i => by rw [hside i]; omega
  have hall := hcov F hodd fun i => by have := hsides i; omega
  have hchart : ∀ d, ¬ IsAxialTreeBond d → d ∈ chordBonds (finiteCells F) := fun d hd => by
    have : d.1 + unitStep F.depth d.2 ∈ sitesOfCells (finiteCells F) F.depth := hall _
    simp [chordBonds, innerBonds, hall, hd]
  set fr : F.Site F.depth × Fin 4 → F.GaugeField F.top → imaginaryQuaternions :=
    fun d => interpolatedFrame s T.a T.chainParams.ρA (frameRadius x) d with hfr
  have hframe := fun d hd => gD x t F V s hx hF' hV hs hs' d hd
  set Cn := Cz T.a T.L T.chainParams with hCn
  have hCn0 : 0 < Cn := hCz _ _ _
  have hLr : (0 : ℝ) < T.L := by
    have : 0 < T.L := hL.pos
    exact_mod_cast this
  have hσ₁ : T.σ ≤ 1 / (64 * (T.L : ℝ) * (Cn + 1)) := hσ.trans (min_le_left _ _)
  have hσ₂ : T.σ ≤ T.chainParams.σA / (16 * (Cn + 2)) := hσ.trans (min_le_right _ _)
  have hρ : T.ballRadius ≤ T.σ := by
    simp only [StepParameters.ballRadius]
    linarith
  have hcoord : ∀ x' i, ‖stepCoordinates η x' i‖ ≤ T.σ :=
    norm_stepCoordinates_le η hσ0.le fun b' => (hη b').trans hρ
  have he₁ : (Cn + 1) * T.σ ≤ 1 / (64 * (T.L : ℝ)) := by
    rw [le_div_iff₀ (by positivity)] at hσ₁ ⊢
    nlinarith
  have hsize : ∀ d ∈ chordBonds (finiteCells F),
      ‖fr d V + stepCoordinates η d.1 d.2‖ ≤ (Cn + 1) * T.σ := by
    intro d hd
    refine (norm_add_le _ _).trans ?_
    have h1 := (hframe d hd).1
    have h2 := hcoord d.1 d.2
    linarith
  have hsmall : IsAdmissibleChartPoint T.L T.chainParams.σA
      (fun z i => fr (z, i) V + stepCoordinates η z i) V := by
    refine ⟨fun d hd => (hsize d hd).trans he₁, ?_⟩
    set w' : F.Site F.depth → Fin 4 → imaginaryQuaternions := fun z i =>
      open Classical in if IsAxialTreeBond (z, i) then 0 else fr (z, i) V + stepCoordinates η z i
      with hw'
    have hcf : chartedField (fun z i => fr (z, i) V + stepCoordinates η z i) V = chartedField w' V :=
      chartedField_congr V fun z i ht => by simp [hw', ht]
    rw [hcf]
    have hL64 : (1 : ℝ) ≤ 64 * T.L := by
      have : (1 : ℝ) ≤ T.L := by exact_mod_cast hL.pos
      linarith
    have he₂ : (Cn + 1) * T.σ ≤ 1 / 4 := by
      refine he₁.trans ?_
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : (1 : ℝ) ≤ T.L := by exact_mod_cast hL.pos
      linarith
    have hcold : IsCold (finiteCells F) F.top (5 / 4 * T.σ) V := fun p hp => by
      simp only [innerPlaquettes, Finset.mem_filter] at hp
      exact hV p hp.2.1
    intro p hp
    have hmem : p ∈ innerPlaquettes (finiteCells F) F.depth := by
      simp only [innerPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
      refine ⟨hall _, hp, fun y _ => hall y⟩
    have hcur := GaugeFixing.plaquetteDefect_chartedField_le hsides hodd (finiteCells F) V
      (5 / 4 * T.σ) ((Cn + 1) * T.σ) (by positivity) hcold w' he₂ (fun d _ => by
        by_cases ht : IsAxialTreeBond (d.1, d.2)
        · have : w' d.1 d.2 = 0 := by simp [hw', ht]
          rw [this]
          simp only [ZeroMemClass.coe_zero, norm_zero]
          positivity
        · have : w' d.1 d.2 = fr (d.1, d.2) V + stepCoordinates η d.1 d.2 := by simp [hw', ht]
          rw [this]
          exact hsize (d.1, d.2) (hchart _ ht)) p hmem
    have hlt : 5 / 4 * T.σ + 8 * ((Cn + 1) * T.σ) < T.chainParams.σA := by
      have h2 := hc.positivity.2.2.2.1
      rw [le_div_iff₀ (by positivity)] at hσ₂
      nlinarith
    linarith
  have hgo := hprop (rateParameters T) ha hL hL40 hc F fr V η hchain hsmall
    (fun d hd => (hframe d hd).2.1)
    (fun d hd k c' X' hk hX' => (hframe d hd).2.2 k c' X' hk hX') l j b u c X hl hu hX
  exact hgo
end YangMills.Construction.Interpolation
end
