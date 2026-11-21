import YangMills.Construction.CellOfTheFlow.HullsThatMeetCellsAreRare
import YangMills.Construction.ClusterExpansionOfAStep.MovesOfAField
import YangMills.Construction.ClusterExpansionOfAStep.ThreeFactsOfAnExpansionProof
import YangMills.Construction.ClusterExpansionOfAStep.ZetaOfAGroundIsBorelProof
import YangMills.Construction.FreeEnergiesOfTheFlow.ActionOfAColdField
import YangMills.Construction.FreeEnergiesOfTheFlow.HaarMassOfASmallBall
import YangMills.Construction.FreeEnergiesOfTheFlow.StateOfAStepIsBorelProof
import YangMills.Construction.HullsInEveryVolume.TheArrayPaysItsLumpsProof
import YangMills.Construction.LawOnABoxOfTheFlow.DensityOfTheStateAlongTheFlow
import YangMills.Construction.ResponseInTheExpansion.StatesAlongTheChainAreBorel
import YangMills.Construction.ResponseInTheExpansion.TheDrawBelowHasItsLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.CellWindows
open TorusFields TorusLumps StepSettings RenormalizationStepParameters WeightedResponses ResponseInTheExpansion BlockAverages LumpContours HaarBalls FieldMoves
section Action
private theorem blockFit_nonneg {F : BlockFrame} {j : ℕ} (X : F.GaugeField j) (X' : F.GaugeField (j + 1))
    (c : F.Site (j + 1) × Fin 4) : 0 ≤ blockFit X X' c := by apply _root_.YangMills.Construction.BlockAverages.MinimalChain.blockFit_nonneg <;> assumption
private theorem wilsonAction_nonneg {F : BlockFrame} (S : Finset F.Cell) (U : F.GaugeField 0) :
    0 ≤ wilsonAction S U := by apply _root_.YangMills.Construction.TorusLumps.wilsonAction_nonneg <;> assumption
private theorem minimalAction_nonneg {F : BlockFrame} {a : ℝ} (ha : 0 ≤ a) (S : Finset F.Cell) :
    ∀ (j : ℕ) (X : F.GaugeField j), 0 ≤ minimalAction a S j X
  | 0, U => wilsonAction_nonneg S U
  | j + 1, V => by
    refine Real.iInf_nonneg fun W => ?_
    exact add_nonneg (minimalAction_nonneg ha S j W)
      (mul_nonneg ha (Finset.sum_nonneg fun c _ => blockFit_nonneg _ _ _))
private theorem actionAtLevel_nonneg {n : ℕ} [NeZero n] {a : ℝ} (ha : 0 ≤ a) (L : ℕ) :
    ∀ (t : ℕ) (S : Finset (TorusSite n)) (W : TorusField n), 0 ≤ actionAtLevel a L t S W
  | 0, S, W => Finset.sum_nonneg fun p _ => plaquetteEnergy_nonneg W _ _ _
  | t + 1, S, W => minimalAction_nonneg ha _ _ _
end Action
section Count
private theorem le_natAbs_valMinAbs_of_far {n : ℕ} [NeZero n] (d s : ℤ) (h1 : s ≤ |d|) (h2 : |d| ≤ n - s) :
    s ≤ (((d : ZMod n)).valMinAbs.natAbs : ℤ) := by
  set w := ((d : ZMod n)).valMinAbs with hw
  have hcast : ((w : ℤ) : ZMod n) = (d : ZMod n) := ZMod.coe_valMinAbs _
  have hdvd : (n : ℤ) ∣ d - w := (ZMod.intCast_eq_intCast_iff_dvd_sub w d n).mp hcast
  obtain ⟨q, hq⟩ := hdvd
  by_contra hlt
  push_neg at hlt
  have hwa : |w| < s := by rwa [Int.abs_eq_natAbs]
  obtain ⟨hw1, hw2⟩ := abs_lt.mp hwa
  obtain ⟨hd1, hd2⟩ := abs_le.mp h2
  rcases lt_trichotomy q 0 with h | h | h
  · have : (n : ℤ) * q ≤ -n := by nlinarith
    omega
  · subst h
    have hdw : d = w := by omega
    rw [hdw] at h1
    omega
  · have : (n : ℤ) ≤ n * q := by nlinarith
    omega
private theorem side_le_supDist_of_sameParity {n : ℕ} [NeZero n] (G : CellGrid) (Q : ℕ) (hs : 0 < G.side)
    (hn : n = G.side * (2 * Q))
    {κ κ₁ κ₂ : Fin 4 → ℤ} (h₁ : κ₁ ∈ G.sameParityIndices n κ) (h₂ : κ₂ ∈ G.sameParityIndices n κ)
    (hne : κ₁ ≠ κ₂) {v₁ v₂ : TorusSite n}
    (hv₁ : v₁ ∈ G.cell n κ₁) (hv₂ : v₂ ∈ G.cell n κ₂) : G.side ≤ _root_.YangMills.Construction.TorusFields.supDist v₁ v₂ := by
  classical
  obtain ⟨hi₁, hp₁⟩ := Finset.mem_filter.mp h₁
  obtain ⟨hi₂, hp₂⟩ := Finset.mem_filter.mp h₂
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  simp only [CellGrid.cell, Finset.mem_filter] at hv₁ hv₂
  obtain ⟨g₁, hg₁, e₁⟩ := hv₁.2
  obtain ⟨g₂, hg₂, e₂⟩ := hv₂.2
  have hdiv : n / G.side = 2 * Q := by
    rw [hn]
    exact Nat.mul_div_cancel_left _ hs
  have hb₁ := Finset.mem_Ico.mp (Fintype.mem_piFinset.mp hi₁ i)
  have hb₂ := Finset.mem_Ico.mp (Fintype.mem_piFinset.mp hi₂ i)
  rw [hdiv] at hb₁ hb₂
  push_cast at hb₁ hb₂
  obtain ⟨b, hb⟩ : (2 : ℤ) ∣ κ₁ i - κ₂ i := by
    have := dvd_sub (hp₁ i) (hp₂ i)
    simpa using this
  set sd : ℤ := (G.side : ℤ) with hsd
  have hnz : (n : ℤ) = 2 * (sd * Q) := by
    rw [hn]
    push_cast
    ring
  set d : ℤ := (G.offset i + sd * κ₁ i + g₁ i) - (G.offset i + sd * κ₂ i + g₂ i) with hd
  have hdz : d = 2 * (sd * b) + (g₁ i - g₂ i) := by
    have : sd * (κ₁ i - κ₂ i) = sd * (2 * b) := by rw [hb]
    rw [hd]
    linarith
  have hg1 := hg₁ i
  have hg2 := hg₂ i
  have hb0 : b ≠ 0 := by
    rintro rfl
    apply hi
    omega
  have hbQ : |b| ≤ (Q : ℤ) - 1 := by
    rw [abs_le]
    omega
  obtain ⟨hbl, hbu⟩ := abs_le.mp hbQ
  have habs : sd ≤ |d| ∧ |d| ≤ n - sd := by
    rcases lt_or_gt_of_ne hb0 with h | h
    · have t1 : sd * b ≤ -sd := by nlinarith
      have t2 : -(sd * Q - sd) ≤ sd * b := by nlinarith
      constructor
      · rw [le_abs]
        right
        omega
      · rw [abs_le]
        omega
    · have t1 : sd ≤ sd * b := by nlinarith
      have t2 : sd * b ≤ sd * Q - sd := by nlinarith
      constructor
      · rw [le_abs]
        left
        omega
      · rw [abs_le]
        omega
  have hz := le_natAbs_valMinAbs_of_far (n := n) d sd habs.1 habs.2
  have hval : v₁ i - v₂ i = (d : ZMod n) := by
    rw [e₁, e₂, hd]
    simp only [siteOfInt]
    push_cast
    rfl
  have hle : ((v₁ i - v₂ i).valMinAbs).natAbs ≤ _root_.YangMills.Construction.TorusFields.supDist v₁ v₂ :=
    Finset.le_sup (f := fun i => ((v₁ i - v₂ i).valMinAbs).natAbs) (Finset.mem_univ i)
  rw [hval] at hle
  have : (G.side : ℤ) ≤ ((d : ZMod n).valMinAbs.natAbs : ℤ) := hz
  omega
open Classical in
private theorem card_le_hotLumps_add_excessLength {n : ℕ} [NeZero n] (ℓ : StepParameters) (r : ℕ)
    (W : TorusField n) (Y : Finset (TorusSite n))
    (S : Finset (Fin 4 → ℤ)) (v : (Fin 4 → ℤ) → TorusSite n) (hv : ∀ κ ∈ S, v κ ∈ Y)
    (hfar : ∀ κ ∈ S, ∀ κ' ∈ S, κ ≠ κ' → 8 * r < _root_.YangMills.Construction.TorusFields.supDist (v κ) (v κ')) :
    S.card ≤ ((torusHotLumps ℓ W).filter (· ⊆ Y)).card + excessLength ℓ r Y W := by
  set H := (torusHotLumps ℓ W).filter (· ⊆ Y) with hH
  set M := H.image lumpCenter with hM
  set X := Y \ thickening (4 * r) M with hX
  have hne : {k | ∃ C : Finset (TorusSite n), C.card = k ∧ X ⊆ thickening (4 * r) C}.Nonempty :=
    ⟨X.card, X, rfl, fun z hz => (mem_thickening _ _ _).mpr ⟨z, hz, by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega⟩⟩
  obtain ⟨C, hC, hXC⟩ := Nat.sInf_mem hne
  have hlen : excessLength ℓ r Y W = C.card := by
    rw [hC]
    rfl
  have hcen : ∀ κ ∈ S, ∃ z ∈ C ∪ M, _root_.YangMills.Construction.TorusFields.supDist (v κ) z ≤ 4 * r := by
    intro κ hκ
    by_cases h : v κ ∈ thickening (4 * r) M
    · obtain ⟨z, hz, hd⟩ := (mem_thickening _ _ _).mp h
      exact ⟨z, Finset.mem_union_right _ hz, hd⟩
    · obtain ⟨z, hz, hd⟩ := (mem_thickening _ _ _).mp (hXC (Finset.mem_sdiff.mpr ⟨hv κ hκ, h⟩))
      exact ⟨z, Finset.mem_union_left _ hz, hd⟩
  choose! c hc hd using hcen
  have hinj : Set.InjOn c S := by
    intro κ hκ κ' hκ' he
    by_contra hne'
    have h1 := hfar κ hκ κ' hκ' hne'
    have h2 := _root_.YangMills.Construction.TorusFields.supDist_triangle (v κ) (c κ) (v κ')
    have h3 := hd κ hκ
    have h4 := hd κ' hκ'
    rw [← he, _root_.YangMills.Construction.TorusFields.supDist_comm] at h4
    omega
  have h1 : S.card ≤ (C ∪ M).card := Finset.card_le_card_of_injOn c hc hinj
  have h2 := Finset.card_union_le C M
  have h3 : M.card ≤ H.card := Finset.card_image_le
  omega
end Count
section Hull
variable {ℓ : StepParameters} {t : ℕ} {x : ℝ} {D : TorusFunctional} {f : LocalDensity} {n : ℕ} [NeZero n]
  {Λ : LabelSpace} {Dq : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ}
  {Φ : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → Finset (TorusSite n) → ℝ}
  {φ : (n : ℕ) → TorusSite n → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ}
private theorem lintegral_glueLabel_self {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]
    {Y Y' : Finset (TorusSite n)} (h : Y' = Y) (G : (Y → Ω) → ENNReal) (ω₀ : Y → Ω) :
    ∫⁻ ν, G (glueLabel Y Y' ω₀ ν) ∂(Measure.pi fun _ : Y' => μ) = ∫⁻ ω, G ω ∂(Measure.pi fun _ : Y => μ) := by apply _root_.YangMills.SharedProofs.p29218 <;> assumption
open Classical in
private theorem lintegral_labelWeight_le (h3 : ExpansionBasicBounds) (hfit : ℓ.Admissible) (hE : 1 ≤ ℓ.E)
    (hx : 0 < x)
    (hfl : 4 * ℓ.n₀ + 2 ^ 16 ≤ clusterRange x) (hc : ColdExpansion ℓ t x D f)
    (hh : HullExpansion ℓ t x D f Λ Dq Φ φ)
    (hs : IsBlockTorusSide ℓ n) (W : TorusField n) (Y : Finset (TorusSite n))
    (hY : IsHullState ℓ (clusterRange x) W Y) (q : ℝ)
    (hq : q ≤ x * ℓ.κ * ℓ.threshold ^ 2 * (((torusHotLumps ℓ W).filter (· ⊆ Y)).card : ℝ) +
      ℓ.κ₁ * x * ℓ.threshold ^ 2 * (excessLength ℓ (clusterRange x) Y W : ℝ)) :
    ∫⁻ ω, ENNReal.ofReal (Dq n W Y ω) ∂(Measure.pi fun _ : Y => Λ.μ) ≤
      ENNReal.ofReal (D n (trivialField n) * Real.exp (2 * ℓ.E * Fintype.card (TorusSite n) - q)) := by
  have hfacts := h3 ℓ t x D f Λ Dq Φ φ hfit hE hx hfl hc hh
  have hflat : IsCold ℓ.threshold (trivialField n) := fun z μ ν _ => by
    simp only [curvature, holonomy_trivialField]
    simpa using hfit.σ_pos
  have hn₀ : ℓ.n₀ ≤ n := by
    have h1 := hs.2
    have h2 : 1 * ℓ.n₀ ≤ ℓ.side * ℓ.n₀ := Nat.mul_le_mul_right _ (by have := hfit.L_ge; omega)
    omega
  have hD1 : 0 < D n (trivialField n) := hc.positive n hn₀ _ hflat
  set c : ℝ := D n (trivialField n) * Real.exp (2 * ℓ.E * Fintype.card (TorusSite n)) with hcdef
  have hc0 : 0 ≤ c := by positivity
  by_cases hne : Nonempty (Y → Λ.Ω)
  · obtain ⟨ω₀⟩ := hne
    set P := chainComponents (clusterRange x) Y with hP
    have hU : P.biUnion id = Y := biUnion_chainComponents
    have hp := hh.price n hs W Y ω₀ P hY subset_rfl
      (fun X hX => absurd (Finset.mem_sdiff.mp hX).1 (Finset.mem_sdiff.mp hX).2)
    let G : (Y → Λ.Ω) → ENNReal := fun ω =>
      if ∃ X ∈ P, Φ n W Y ω X = 0 then 0 else
        ENNReal.ofReal ((∏ X ∈ P, Φ n W Y ω X) *
          Real.exp (∑ y ∈ Finset.univ.filter (fun y : TorusSite n =>
              ∃ z ∈ P.biUnion id, (_root_.YangMills.Construction.TorusFields.supDist y z : ℝ) < (clusterRange x : ℝ) / 4),
            φ n y W Y ω))
    have hG : ∫⁻ ω, G ω ∂(Measure.pi fun _ : Y => Λ.μ) ≤ ENNReal.ofReal (Real.exp (-q)) := by
      rw [← lintegral_glueLabel_self Λ.μ hU G ω₀]
      refine hp.trans ?_
      apply ENNReal.ofReal_le_ofReal
      rw [hU]
      apply Real.exp_le_exp.mpr
      linarith
    have hpt : ∀ ω, ENNReal.ofReal (Dq n W Y ω) ≤ ENNReal.ofReal c * G ω := by
      intro ω
      by_cases hz : ∃ X ∈ P, Φ n W Y ω X = 0
      · obtain ⟨X, hX, h0⟩ := hz
        rw [hh.form n hs W Y ω hY, Finset.prod_eq_zero hX h0, mul_zero]
        simp
      · have hGω : G ω = ENNReal.ofReal ((∏ X ∈ P, Φ n W Y ω X) *
            Real.exp (∑ y ∈ Finset.univ.filter (fun y : TorusSite n =>
                ∃ z ∈ P.biUnion id, (_root_.YangMills.Construction.TorusFields.supDist y z : ℝ) < (clusterRange x : ℝ) / 4), φ n y W Y ω)) := by
          simp only [G]
          rw [if_neg hz]
        push_neg at hz
        rw [hGω, ← ENNReal.ofReal_mul hc0]
        apply ENNReal.ofReal_le_ofReal
        rw [hh.form n hs W Y ω hY]
        set near := Finset.univ.filter (fun y : TorusSite n =>
                ∃ z ∈ P.biUnion id, (_root_.YangMills.Construction.TorusFields.supDist y z : ℝ) < (clusterRange x : ℝ) / 4) with hnear
        have hsplit : ∑ y, φ n y W Y ω = ∑ y ∈ near, φ n y W Y ω +
            ∑ y ∈ Finset.univ.filter (fun y : TorusSite n =>
              ¬ ∃ z ∈ P.biUnion id, (_root_.YangMills.Construction.TorusFields.supDist y z : ℝ) < (clusterRange x : ℝ) / 4), φ n y W Y ω :=
          (Finset.sum_filter_add_sum_filter_not _ _ _).symm
        have hfarsum : ∑ y ∈ Finset.univ.filter (fun y : TorusSite n =>
              ¬ ∃ z ∈ P.biUnion id, (_root_.YangMills.Construction.TorusFields.supDist y z : ℝ) < (clusterRange x : ℝ) / 4), φ n y W Y ω ≤
            2 * ℓ.E * Fintype.card (TorusSite n) := by
          have h1 : ∀ y ∈ Finset.univ.filter (fun y : TorusSite n =>
              ¬ ∃ z ∈ P.biUnion id, (_root_.YangMills.Construction.TorusFields.supDist y z : ℝ) < (clusterRange x : ℝ) / 4),
              φ n y W Y ω ≤ 2 * ℓ.E := by
            intro y hy
            have hy2 := (Finset.mem_filter.mp hy).2
            push_neg at hy2
            rw [hU] at hy2
            exact (le_abs_self _).trans (hfacts.2.1 n hs W Y ω y hY hz hy2)
          have h2 := Finset.sum_le_card_nsmul _ _ _ h1
          rw [nsmul_eq_mul] at h2
          have h3 : ((Finset.univ.filter (fun y : TorusSite n =>
              ¬ ∃ z ∈ P.biUnion id, (_root_.YangMills.Construction.TorusFields.supDist y z : ℝ) < (clusterRange x : ℝ) / 4)).card : ℝ) ≤
              Fintype.card (TorusSite n) := by
            exact_mod_cast Finset.card_le_univ _
          nlinarith
        have hA : 0 ≤ x * actionAtLevel ℓ.coupling ℓ.side t
            (Finset.univ \ thickening lumpRange (torusHotSites ℓ W)) W :=
          mul_nonneg hx.le (actionAtLevel_nonneg (by linarith [hfit.a_ge]) _ _ _ _)
        have hprod : 0 ≤ ∏ X ∈ P, Φ n W Y ω X :=
          Finset.prod_nonneg fun X _ => hh.factor_nonneg n hs W Y ω X
        have hexp : Real.exp (-x * actionAtLevel ℓ.coupling ℓ.side t
            (Finset.univ \ thickening lumpRange (torusHotSites ℓ W)) W + ∑ y, φ n y W Y ω) ≤
            Real.exp (2 * ℓ.E * Fintype.card (TorusSite n)) * Real.exp (∑ y ∈ near, φ n y W Y ω) := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          rw [hsplit]
          linarith
        calc D n (trivialField n) * _ * _ ≤ D n (trivialField n) *
              (Real.exp (2 * ℓ.E * Fintype.card (TorusSite n)) *
              Real.exp (∑ y ∈ near, φ n y W Y ω)) * ∏ X ∈ P, Φ n W Y ω X := by gcongr
          _ = c * ((∏ X ∈ P, Φ n W Y ω X) * Real.exp (∑ y ∈ near, φ n y W Y ω)) := by
            rw [hcdef]
            ring
    calc ∫⁻ ω, ENNReal.ofReal (Dq n W Y ω) ∂(Measure.pi fun _ : Y => Λ.μ)
        ≤ ∫⁻ ω, ENNReal.ofReal c * G ω ∂(Measure.pi fun _ : Y => Λ.μ) := lintegral_mono hpt
      _ = ENNReal.ofReal c * ∫⁻ ω, G ω ∂(Measure.pi fun _ : Y => Λ.μ) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal c * ENNReal.ofReal (Real.exp (-q)) := by gcongr
      _ = ENNReal.ofReal (c * Real.exp (-q)) := (ENNReal.ofReal_mul hc0).symm
      _ = _ := by
        congr 1
        rw [hcdef, mul_assoc, ← Real.exp_add]
        congr 2
  · haveI : IsEmpty (Y → Λ.Ω) := not_nonempty_iff.mp hne
    simp
end Hull
section Main
private theorem measurable_sigma_of_forall {A : Type} {β : A → Type} [∀ a, MeasurableSpace (β a)] {γ : Type}
    [MeasurableSpace γ] {f : Sigma β → γ} (h : ∀ a, Measurable fun y : β a => f ⟨a, y⟩) : Measurable f := by apply _root_.YangMills.SharedProofs.p3239 <;> assumption
private theorem card_torusSite (n : ℕ) [NeZero n] : (Fintype.card (TorusSite n) : ℝ) = (n : ℝ) ^ 4 := by
  simp [ZMod.card]
private theorem fieldHaar_pi_closedBall_ge (n : ℕ) [NeZero n] {e q : ℝ} (hq : 0 ≤ q)
    (hb : q ≤ (haarUnit (closedBallAtOne e)).toReal) :
    ENNReal.ofReal ((q ^ 4) ^ Fintype.card (TorusSite n)) ≤
      fieldHaar n (Set.pi Set.univ fun _ : TorusSite n => Set.pi Set.univ fun _ : Fin 4 => closedBallAtOne e) := by
  have hb' : ENNReal.ofReal q ≤ haarUnit (closedBallAtOne e) := by
    rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
    exact hb
  unfold fieldHaar
  rw [Measure.pi_pi]
  simp only [Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_pow hq]
  gcongr
abbrev _root_.YangMills.SharedProofs.p69150 := @fieldHaar_pi_closedBall_ge
private theorem measurableSet_pi_closedBall (n : ℕ) [NeZero n] (e : ℝ) :
    MeasurableSet (Set.pi Set.univ fun _ : TorusSite n => Set.pi Set.univ fun _ : Fin 4 => closedBallAtOne e) := by
  have h1 : MeasurableSet (closedBallAtOne e) := by
    have : IsClosed (closedBallAtOne e) :=
      isClosed_le (continuous_norm.comp (continuous_subtype_val.sub continuous_const)) continuous_const
    exact this.measurableSet
  exact MeasurableSet.univ_pi fun _ => MeasurableSet.univ_pi fun _ => h1
abbrev _root_.YangMills.SharedProofs.p68411 := @measurableSet_pi_closedBall
private theorem functional_ge_near_one {Tb : ParameterAssignment} {y : ℝ} {t : ℕ} {x : ℝ} {D : TorusFunctional}
    {f : LocalDensity}
    (hfacts : ∀ (n : ℕ) [NeZero n], (Tb.stepParameters y).n₀ ≤ n → ∀ (z : TorusSite n) (W : TorusField n),
      IsCold (Tb.stepParameters y).threshold W → |centered f n z W| ≤ (Tb.stepParameters y).E)
    (hσ : 0 < Tb.threshold) {Nc : ℝ} (hNc0 : 0 ≤ Nc)
    (hNc : ∀ (t n : ℕ) [NeZero n], Tb.n₀ ≤ n → ∀ (s : ℝ) (W : TorusField n), 0 < s → s ≤ Tb.threshold →
      IsCold s W → actionAtLevel Tb.coupling Tb.side t Finset.univ W ≤ Nc * s ^ 2 * (n : ℝ) ^ 4)
    (hc : ColdExpansion (Tb.stepParameters y) t x D f) (hx : 1 ≤ x) (n : ℕ) [NeZero n] (hn : Tb.n₀ ≤ n)
    (W : TorusField n)
    (hW : ∀ z i, ((W z i : UnitQuaternion) : ℍ[ℝ]) - 1 ∈
      Metric.closedBall (0 : ℍ[ℝ]) (Tb.threshold / (8 * Real.sqrt x))) :
    D n (trivialField n) * Real.exp (-((Nc * Tb.threshold ^ 2 + Tb.E) * (n : ℝ) ^ 4)) ≤ D n W := by
  have hsq : 1 ≤ Real.sqrt x := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hx
  set s : ℝ := Tb.threshold / Real.sqrt x with hs
  have hs0 : 0 < s := by positivity
  have hsσ : s ≤ Tb.threshold := div_le_self hσ.le hsq
  have hcold : IsCold s W := by
    intro z μ ν _
    have h1 := curvature_le_add_of_close (W := trivialField n) (W' := W)
      (ε := Tb.threshold / (8 * Real.sqrt x)) (fun z i => by
      have := hW z i
      simpa [trivialField, dist_zero_right] using this) z μ ν
    have h2 : curvature (trivialField n) z μ ν = 0 := by simp [curvature, holonomy_trivialField]
    rw [h2, zero_add] at h1
    have h3 : 4 * (Tb.threshold / (8 * Real.sqrt x)) = s / 2 := by
      rw [hs]
      field_simp
      ring
    linarith
  have hcoldσ : IsCold (Tb.stepParameters y).threshold W := fun z μ ν h => (hcold z μ ν h).trans_le hsσ
  have hflat : IsCold (Tb.stepParameters y).threshold (trivialField n) := fun z μ ν _ => by
    have h2 : curvature (trivialField n) z μ ν = 0 := by simp [curvature, holonomy_trivialField]
    rw [h2]
    exact hσ
  have hpos := hc.positive n hn W hcoldσ
  have hpos1 := hc.positive n hn _ hflat
  have hform := hc.form n hn W hcoldσ
  have hD : D n W = D n (trivialField n) * Real.exp (-x * actionAtLevel (Tb.stepParameters y).coupling
      (Tb.stepParameters y).side t Finset.univ W + ∑ z, centered f n z W) := by
    rw [← hform, Real.exp_sub, Real.exp_log hpos, Real.exp_log hpos1]
    field_simp
  rw [hD]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hpos1.le
  have hA := hNc t n hn s W hs0 hsσ hcold
  have hxs : x * s ^ 2 = Tb.threshold ^ 2 := by
    rw [hs, div_pow, Real.sq_sqrt (by linarith)]
    field_simp
  have hA' : x * actionAtLevel Tb.coupling Tb.side t Finset.univ W ≤ Nc * Tb.threshold ^ 2 * (n : ℝ) ^ 4 := by
    have h0 : (0 : ℝ) ≤ x := by linarith
    calc x * actionAtLevel Tb.coupling Tb.side t Finset.univ W ≤ x * (Nc * s ^ 2 * (n : ℝ) ^ 4) :=
          mul_le_mul_of_nonneg_left hA h0
      _ = Nc * (x * s ^ 2) * (n : ℝ) ^ 4 := by ring
      _ = _ := by rw [hxs]
  have hsum : -(Tb.E * (n : ℝ) ^ 4) ≤ ∑ z, centered f n z W := by
    have h1 : ∀ z ∈ (Finset.univ : Finset (TorusSite n)), -Tb.E ≤ centered f n z W := fun z _ =>
      (abs_le.mp (hfacts n hn z W hcoldσ)).1
    have h2 := Finset.card_nsmul_le_sum _ _ _ h1
    rw [nsmul_eq_mul, Finset.card_univ, card_torusSite] at h2
    linarith
  have ea : actionAtLevel (Tb.stepParameters y).coupling (Tb.stepParameters y).side t Finset.univ W =
      actionAtLevel Tb.coupling Tb.side t Finset.univ W := rfl
  rw [ea]
  nlinarith
abbrev _root_.YangMills.SharedProofs.p2065 := @functional_ge_near_one
private def haarBallExponent (cH σ : ℝ) : ℝ := -(Real.log cH + 3 * Real.log (σ / 8))
private theorem exponent_inequality (C l2 E Nq b ab lx K : ℝ) (h : 0 ≤ C * (ab - b)) :
    C * l2 + (2 * E * C - K) ≤ -((Nq + E) * C) + C * (4 * (-b - 3 / 2 * lx)) +
      ((l2 + 3 * E + Nq + 4 * ab + 6 * lx) * C - K) := by
  linarith
open Classical in
private theorem markedSampleLaw_hullMeetsCells_le {Tb : ParameterAssignment} {y : ℝ} (hD : Tb.Admissible)
    (hfit : (Tb.stepParameters y).Admissible)
    (h3 : ExpansionBasicBounds) {Nc cH : ℝ} (hNc0 : 0 ≤ Nc)
    (hNc : ∀ (t n : ℕ) [NeZero n], Tb.n₀ ≤ n → ∀ (s : ℝ) (W : TorusField n), 0 < s → s ≤ Tb.threshold →
      IsCold s W → actionAtLevel Tb.coupling Tb.side t Finset.univ W ≤ Nc * s ^ 2 * (n : ℝ) ^ 4)
    (hcH : 0 < cH)
    (hHb : ∀ e : ℝ, 0 < e → e ≤ 1 → cH * e ^ 3 ≤ (haarUnit (closedBallAtOne e)).toReal)
    (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k n : ℕ) [NeZero n] (hS : IsTowerAtParameters Tb y T β k)
    (hden : ∀ G : StageState T k n → ENNReal, Measurable G →
      ENNReal.ofReal (∫ W, wilsonWeight β (fineSide (Tb.stepParameters y).side k n) W
          ∂(fieldHaar (fineSide (Tb.stepParameters y).side k n))) *
        ∫⁻ u, G (stageState T k n u) ∂(markedSampleLaw T β k n) =
      ∫⁻ W, (open Classical in
        ∑ Y ∈ Finset.univ.filter (IsHullState (Tb.stepParameters y) (clusterRange (T.stage k).coupling) W),
          ∫⁻ ω, G (W, ⟨Y, ω⟩) * ENNReal.ofReal ((T.stage k).labelWeight n W Y ω)
            ∂(Measure.pi fun _ : Y => (T.stage k).labels.μ)) ∂(fieldHaar n))
    (hP : IsProbabilityMeasure (markedSampleLaw T β k n)) (hB : Measurable (stageState T k n))
    (hs : IsBlockTorusSide (Tb.stepParameters y) n) (hx1 : 1 ≤ (T.stage k).coupling)
    (hrange : 4 * (Tb.stepParameters y).n₀ + 2 ^ 16 ≤ clusterRange (T.stage k).coupling)
    (G : CellGrid) (Q : ℕ) (hside : 0 < G.side) (hQ : n = G.side * (2 * Q)) (h8 : 8 * stageRange T k < G.side)
    (κ : Fin 4 → ℤ) (S : Finset (Fin 4 → ℤ)) (hSS : S ⊆ G.sameParityIndices n κ) :
    markedSampleLaw T β k n
        {u | ∀ κ' ∈ S, (stageHull T k n u ∩ interiorAtDepth (8 * stageRange T k) (G.cell n κ')).Nonempty} ≤
      ENNReal.ofReal (Real.exp ((Real.log 2 + 3 * Tb.E + Nc * Tb.threshold ^ 2 +
          4 * |haarBallExponent cH Tb.threshold| +
          6 * Real.log (T.stage k).coupling) * (n : ℝ) ^ 4 -
          (T.stage k).coupling * Tb.κ₁ * Tb.threshold ^ 2 * S.card)) := by
  have hσ : 0 < Tb.threshold := hD.σ_pos
  have hE : 1 ≤ Tb.E := hfit.E_ge
  set x := (T.stage k).coupling with hxdef
  have hrow : (T.stage k).toStepSetup.HasExpansions := (hS.onFamily k le_rfl).isStep.1
  have hC : ColdExpansion (Tb.stepParameters y) (T.stage k).depth x (T.stage k).functional
      (T.stage k).density := hrow.1
  have hH : HullExpansion (Tb.stepParameters y) (T.stage k).depth x (T.stage k).functional
      (T.stage k).density (T.stage k).labels (T.stage k).labelWeight
      (T.stage k).clusterFactor (T.stage k).siteDensity := hrow.2
  have hx0 : 0 < x := by linarith
  have hfacts := h3 _ _ _ _ _ _ _ _ _ hfit hE hx0 hrange hC hH
  have hLpos' : 0 < Tb.side := Nat.pos_of_ne_zero (NeZero.ne Tb.side)
  have hbig : Tb.n₀ ≤ n := by
    have h1 : Tb.side * Tb.n₀ ≤ n := hs.2
    nlinarith
  set Ev : Set (Finset (TorusSite n)) :=
    {Y | ∀ κ' ∈ S, (Y ∩ interiorAtDepth (8 * stageRange T k) (G.cell n κ')).Nonempty} with hEv
  have hE0 : MeasurableSet {z : Σ Y : Finset (TorusSite n), (Y → (T.stage k).labels.Ω) | z.1 ∈ Ev} :=
    measurableSet_setOf.2 (measurable_sigma_of_forall
      (f := fun z : Σ Y : Finset (TorusSite n), (Y → (T.stage k).labels.Ω) => z.1 ∈ Ev)
      fun a => by
        show Measurable fun _ => a ∈ Ev
        exact measurable_const)
  have hEm : MeasurableSet {q : StageState T k n | q.2.1 ∈ Ev} := measurable_snd hE0
  let G' : StageState T k n → ENNReal := Set.indicator {q | q.2.1 ∈ Ev} 1
  have hG' : Measurable G' := measurable_one.indicator hEm
  have hd1 := hden G' hG'
  have hd2 := hden (fun _ => 1) measurable_const
  set zr : ℝ := ∫ W, wilsonWeight β (fineSide (Tb.stepParameters y).side k n) W
    ∂(fieldHaar (fineSide (Tb.stepParameters y).side k n)) with hzr
  set Sset : Set (MarkedSample (Tb.stepParameters y) k n) :=
    {u | ∀ κ' ∈ S, (stageHull T k n u ∩ interiorAtDepth (8 * stageRange T k) (G.cell n κ')).Nonempty}
    with hSdef
  have hSm : MeasurableSet Sset := hB hEm
  have hl1 : ∫⁻ u, G' (stageState T k n u) ∂(markedSampleLaw T β k n) = markedSampleLaw T β k n Sset := by
    have e : (fun u => G' (stageState T k n u)) = Sset.indicator 1 := rfl
    rw [e]
    exact lintegral_indicator_one hSm
  rw [hl1] at hd1
  simp only [lintegral_const, one_mul, measure_univ, mul_one] at hd2
  set C' : ℝ := (Fintype.card (TorusSite n) : ℝ) with hC'
  set K' : ℝ := x * Tb.κ₁ * Tb.threshold ^ 2 * S.card with hK'
  set D1 : ℝ := (T.stage k).functional n (trivialField n) with hD1def
  have hflat : IsCold (Tb.stepParameters y).threshold (trivialField n) := fun z μ ν _ => by
    have h2 : curvature (trivialField n) z μ ν = 0 := by simp [curvature, holonomy_trivialField]
    rw [h2]
    exact hσ
  have hD1 : 0 < D1 := hC.positive _ hbig _ hflat
  set cU : ℝ := D1 * Real.exp (2 * Tb.E * C' - K') with hcU
  have hκ₁ : Tb.κ₁ ≤ Tb.κ := by
    have h1 : Tb.κ₁ ≤ Tb.κ / 16 := min_le_left _ _
    have h2 := hD.κ_pos
    linarith
  have hκ₁0 : 0 < Tb.κ₁ := hfit.κ₁_pos
  have hkey : ∀ W, ∀ Y ∈ Finset.univ.filter (IsHullState (Tb.stepParameters y) (clusterRange x) W),
      ∫⁻ ω, G' (W, ⟨Y, ω⟩) * ENNReal.ofReal ((T.stage k).labelWeight n W Y ω)
        ∂(Measure.pi fun _ : Y => (T.stage k).labels.μ) ≤ ENNReal.ofReal cU := by
    intro W Y hYm
    have hY : IsHullState (Tb.stepParameters y) (clusterRange x) W Y := (Finset.mem_filter.mp hYm).2
    by_cases hYE : Y ∈ Ev
    · have hG1 : ∀ ω : Y → (T.stage k).labels.Ω, G' (W, ⟨Y, ω⟩) = 1 := fun ω =>
        Set.indicator_of_mem (s := {q : StageState T k n | q.2.1 ∈ Ev}) (a := (W, ⟨Y, ω⟩)) hYE 1
      simp only [hG1, one_mul]
      have hch : ∀ κ' ∈ S, ∃ v, v ∈ Y ∧ v ∈ G.cell n κ' := fun κ' hκ' => by
        obtain ⟨v, hv⟩ := hYE κ' hκ'
        obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hv
        exact ⟨v, h1, (Finset.mem_filter.mp h2).1⟩
      choose! v hv1 hv2 using hch
      have hcard := card_le_hotLumps_add_excessLength (Tb.stepParameters y) (clusterRange x) W Y S v hv1
        (fun a ha b hb hne => by
        have h1 := side_le_supDist_of_sameParity G Q hside hQ (hSS ha) (hSS hb) hne (hv2 a ha) (hv2 b hb)
        have h2 : 8 * clusterRange x < G.side := h8
        omega)
      have hcR : (S.card : ℝ) ≤ (((torusHotLumps (Tb.stepParameters y) W).filter (· ⊆ Y)).card : ℝ) +
          (excessLength (Tb.stepParameters y) (clusterRange x) Y W : ℝ) := by exact_mod_cast hcard
      have hq : K' ≤ x * (Tb.stepParameters y).κ * (Tb.stepParameters y).threshold ^ 2 *
            (((torusHotLumps (Tb.stepParameters y) W).filter (· ⊆ Y)).card : ℝ) +
          (Tb.stepParameters y).κ₁ * x * (Tb.stepParameters y).threshold ^ 2 *
            (excessLength (Tb.stepParameters y) (clusterRange x) Y W : ℝ) := by
        show x * Tb.κ₁ * Tb.threshold ^ 2 * S.card ≤ x * Tb.κ * Tb.threshold ^ 2 *
            (((torusHotLumps (Tb.stepParameters y) W).filter (· ⊆ Y)).card : ℝ) +
          Tb.κ₁ * x * Tb.threshold ^ 2 * (excessLength (Tb.stepParameters y) (clusterRange x) Y W : ℝ)
        have ha : 0 ≤ x * Tb.κ₁ * Tb.threshold ^ 2 := by positivity
        have h1 := mul_le_mul_of_nonneg_left hcR ha
        have h2 : x * Tb.κ₁ * Tb.threshold ^ 2 *
            (((torusHotLumps (Tb.stepParameters y) W).filter (· ⊆ Y)).card : ℝ) ≤
            x * Tb.κ * Tb.threshold ^ 2 *
            (((torusHotLumps (Tb.stepParameters y) W).filter (· ⊆ Y)).card : ℝ) := by
          gcongr
        linarith
      exact lintegral_labelWeight_le h3 hfit hE hx0 hrange hC hH hs W Y hY K' hq
    · have hG0 : ∀ ω : Y → (T.stage k).labels.Ω, G' (W, ⟨Y, ω⟩) = 0 := fun ω =>
        Set.indicator_of_notMem (s := {q : StageState T k n | q.2.1 ∈ Ev}) (a := (W, ⟨Y, ω⟩)) hYE 1
      simp only [hG0, zero_mul, lintegral_zero]
      exact zero_le
  have hupper : ∀ W, (∑ Y ∈ Finset.univ.filter (IsHullState (Tb.stepParameters y) (clusterRange x) W),
      ∫⁻ ω, G' (W, ⟨Y, ω⟩) * ENNReal.ofReal ((T.stage k).labelWeight n W Y ω)
        ∂(Measure.pi fun _ : Y => (T.stage k).labels.μ)) ≤
      ENNReal.ofReal ((2 : ℝ) ^ Fintype.card (TorusSite n)) * ENNReal.ofReal cU := by
    intro W
    refine (Finset.sum_le_card_nsmul _ _ _ (hkey W)).trans ?_
    rw [nsmul_eq_mul]
    have hcard : (Finset.univ.filter (IsHullState (Tb.stepParameters y) (clusterRange x) W)).card ≤
        2 ^ Fintype.card (TorusSite n) := by
      refine (Finset.card_le_univ _).trans ?_
      rw [Fintype.card_finset]
    have h1 : ((Finset.univ.filter (IsHullState (Tb.stepParameters y) (clusterRange x) W)).card : ENNReal) ≤
        ((2 ^ Fintype.card (TorusSite n) : ℕ) : ENNReal) := by exact_mod_cast hcard
    have h2e : ((2 ^ Fintype.card (TorusSite n) : ℕ) : ENNReal) =
        ENNReal.ofReal ((2 : ℝ) ^ Fintype.card (TorusSite n)) := by
      rw [show ((2 : ℝ) ^ Fintype.card (TorusSite n)) = ((2 ^ Fintype.card (TorusSite n) : ℕ) : ℝ) by
        push_cast; rfl, ENNReal.ofReal_natCast]
    rw [h2e] at h1
    exact mul_le_mul' h1 (le_refl _)
  have hnum : ENNReal.ofReal zr * markedSampleLaw T β k n Sset ≤
      ENNReal.ofReal ((2 : ℝ) ^ Fintype.card (TorusSite n)) * ENNReal.ofReal cU := by
    rw [hd1]
    refine (lintegral_mono hupper).trans ?_
    rw [lintegral_const, measure_univ, mul_one]
  have hsq : 1 ≤ Real.sqrt x := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hx1
  have hsq0 : 0 < Real.sqrt x := by linarith
  set e : ℝ := Tb.threshold / (8 * Real.sqrt x) with he
  have he0 : 0 < e := by positivity
  have he1 : e ≤ 1 := by
    rw [he, div_le_one (by positivity)]
    have := hD.σ_one
    linarith
  set q : ℝ := cH * e ^ 3 with hq
  have hq0 : 0 < q := by positivity
  have hqb : q ≤ (haarUnit (closedBallAtOne e)).toReal := hHb e he0 he1
  set c0 : ℝ := D1 * Real.exp (-((Nc * Tb.threshold ^ 2 + Tb.E) * (n : ℝ) ^ 4)) with hc0
  have hc00 : 0 ≤ c0 := by positivity
  have hlow : ENNReal.ofReal c0 * ENNReal.ofReal ((q ^ 4) ^ Fintype.card (TorusSite n)) ≤ ENNReal.ofReal zr := by
    rw [hd2]
    have hsum : ∀ W, (∑ Y ∈ Finset.univ.filter (IsHullState (Tb.stepParameters y) (clusterRange x) W),
        ∫⁻ ω, ENNReal.ofReal ((T.stage k).labelWeight n W Y ω)
          ∂(Measure.pi fun _ : Y => (T.stage k).labels.μ)) =
        ENNReal.ofReal ((T.stage k).functional n W) := fun W => hH.sum _ hs W
    simp only [hsum]
    set B : Set (TorusField n) := Set.pi Set.univ fun _ : TorusSite n =>
      Set.pi Set.univ fun _ : Fin 4 => closedBallAtOne e with hBdef
    have hBm : MeasurableSet B := measurableSet_pi_closedBall _ e
    calc ENNReal.ofReal c0 * ENNReal.ofReal ((q ^ 4) ^ Fintype.card (TorusSite n))
        ≤ ENNReal.ofReal c0 * fieldHaar n B := by
          gcongr
          exact fieldHaar_pi_closedBall_ge _ hq0.le hqb
      _ = ∫⁻ _ in B, ENNReal.ofReal c0 ∂(fieldHaar n) := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ W in B, ENNReal.ofReal ((T.stage k).functional n W) ∂(fieldHaar n) := by
          refine setLIntegral_mono' hBm fun W hW => ENNReal.ofReal_le_ofReal ?_
          refine functional_ge_near_one (y := y) (hfacts.1) hσ hNc0 hNc hC hx1 _ hbig W fun z i => ?_
          have h1 : W z i ∈ closedBallAtOne e := hW z (Set.mem_univ _) i (Set.mem_univ _)
          simpa [closedBallAtOne, dist_zero_right] using h1
      _ ≤ _ := setLIntegral_le_lintegral _ _
  set a : ℝ := (markedSampleLaw T β k n).real Sset with ha
  have ha0 : 0 ≤ a := measureReal_nonneg
  have hLw : 0 < c0 * (q ^ 4) ^ Fintype.card (TorusSite n) := by positivity
  have hzLw : c0 * (q ^ 4) ^ Fintype.card (TorusSite n) ≤ zr := by
    rw [← ENNReal.ofReal_mul hc00] at hlow
    rcases (ENNReal.ofReal_le_ofReal_iff').mp hlow with h | h
    · exact h
    · exact absurd h (not_le.mpr hLw)
  have hzr0 : 0 ≤ zr := hLw.le.trans hzLw
  have e1 : markedSampleLaw T β k n Sset = ENNReal.ofReal a := (ofReal_measureReal (measure_ne_top _ _)).symm
  have hza : zr * a ≤ (2 : ℝ) ^ Fintype.card (TorusSite n) * cU := by
    rw [e1, ← ENNReal.ofReal_mul hzr0, ← ENNReal.ofReal_mul (by positivity)] at hnum
    rcases (ENNReal.ofReal_le_ofReal_iff').mp hnum with h | h
    · exact h
    · exact h.trans (by positivity)
  have hC'n : C' = (n : ℝ) ^ 4 := card_torusSite _
  have hC'0 : 0 ≤ C' := by positivity
  set b : ℝ := haarBallExponent cH Tb.threshold with hb
  have hlogq : Real.log q = -b - 3 / 2 * Real.log x := by
    rw [hq, Real.log_mul hcH.ne' (by positivity), Real.log_pow, he,
      show Tb.threshold / (8 * Real.sqrt x) = (Tb.threshold / 8) / Real.sqrt x by field_simp,
      Real.log_div (by positivity) hsq0.ne',
      Real.log_sqrt (by linarith), hb, haarBallExponent]
    push_cast
    ring
  have hpow2 : (2 : ℝ) ^ Fintype.card (TorusSite n) = Real.exp (C' * Real.log 2) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num), mul_comm]
  have hpowq : (q ^ 4) ^ Fintype.card (TorusSite n) = Real.exp (C' * (4 * Real.log q)) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by positivity), Real.log_pow]
    congr 1
    push_cast
    ring
  set Ex : ℝ := (Real.log 2 + 3 * Tb.E + Nc * Tb.threshold ^ 2 + 4 * |b| + 6 * Real.log x) * (n : ℝ) ^ 4 - K'
    with hEx
  have hU : (2 : ℝ) ^ Fintype.card (TorusSite n) * cU ≤
      c0 * (q ^ 4) ^ Fintype.card (TorusSite n) * Real.exp Ex := by
    rw [hpow2, hpowq, hcU, hc0, ← hC'n]
    have e1 : Real.exp (C' * Real.log 2) * (D1 * Real.exp (2 * Tb.E * C' - K')) =
        D1 * Real.exp (C' * Real.log 2 + (2 * Tb.E * C' - K')) := by
      rw [Real.exp_add]
      ring
    have e2 : D1 * Real.exp (-((Nc * Tb.threshold ^ 2 + Tb.E) * C')) * Real.exp (C' * (4 * Real.log q)) *
        Real.exp Ex =
        D1 * Real.exp (-((Nc * Tb.threshold ^ 2 + Tb.E) * C') + C' * (4 * Real.log q) + Ex) := by
      rw [Real.exp_add, Real.exp_add]
      ring
    rw [e1, e2]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hD1.le
    rw [hEx, ← hC'n, hlogq]
    have hb' := le_abs_self b
    exact exponent_inequality _ _ _ _ _ _ _ _ (mul_nonneg hC'0 (sub_nonneg.mpr hb'))
  have hfin : c0 * (q ^ 4) ^ Fintype.card (TorusSite n) * a ≤
      c0 * (q ^ 4) ^ Fintype.card (TorusSite n) * Real.exp Ex :=
    (mul_le_mul_of_nonneg_right hzLw ha0).trans (hza.trans hU)
  have hfinal : a ≤ Real.exp Ex := le_of_mul_le_mul_left hfin hLw
  rw [e1]
  exact ENNReal.ofReal_le_ofReal hfinal
private theorem le_clusterRange_of_pow_le {k : ℕ} {y : ℝ} (hy : (k : ℝ) ^ 100 ≤ y) : k ≤ clusterRange y := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.le_clusterRange <;> assumption
theorem hullMeetsCellsBound_holds (hDen : StageDensity.stageStateDensityStatement)
    (hLaw : WeightedResponses.forgetLastStepStatement)
    (hBor : ResponseInTheExpansion.StageStatesMeasurableStatement)
    (h3 : TorusLumps.ExpansionBasicBounds) (hAct : ColdFieldAction.ColdActionBound)
    (hHaar : HaarBalls.HaarMassCubicLowerBound) : hullMeetsCellsBoundStatement := by
  classical
  obtain ⟨cH, hcH, hHb⟩ := hHaar
  have hA' : ∀ Tb : ParameterAssignment, ∃ N : ℝ, Tb.Admissible → (0 ≤ N ∧ ∀ (t n : ℕ) [NeZero n], Tb.n₀ ≤ n →
      ∀ (s : ℝ) (W : TorusField n), 0 < s → s ≤ Tb.threshold → IsCold s W →
        actionAtLevel Tb.coupling Tb.side t Finset.univ W ≤ N * s ^ 2 * (n : ℝ) ^ 4) := fun Tb => by
    by_cases h : Tb.Admissible
    · obtain ⟨N, h1⟩ := hAct Tb h
      exact ⟨N, fun _ => h1⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose Nc hNc using hA'
  refine ⟨fun Tb => Real.log 2 + 3 * Tb.E + Nc Tb * Tb.threshold ^ 2 +
    4 * |haarBallExponent cH Tb.threshold|, fun _ => 6, ?_⟩
  intro a ha
  obtain ⟨L₁, r₁, hr₁, H₁⟩ := hDen a ha
  refine ⟨L₁, r₁, hr₁, ?_⟩
  intro L hodd hLe Tb hTa hTL hD hrt
  obtain ⟨y₁, Y₁⟩ := H₁ L hodd hLe Tb hTa hTL hD hrt
  refine ⟨max (max y₁ Tb.floorMin) (max 1 (((4 * Tb.n₀ + 2 ^ 16 + Tb.side * Tb.n₀ : ℕ) : ℝ) ^ 100)),
    fun y hy hR hW => ?_⟩
  have hy1 : y₁ ≤ y := ((le_max_left _ _).trans (le_max_left _ _)).trans hy
  have hy2 : Tb.floorMin ≤ y := ((le_max_right _ _).trans (le_max_left _ _)).trans hy
  have hy3 : (1 : ℝ) ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have hy4 : (((4 * Tb.n₀ + 2 ^ 16 + Tb.side * Tb.n₀ : ℕ) : ℝ)) ^ 100 ≤ y :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hy
  have A₁ := Y₁ y hy1 hR hW
  have hfit := hD.fits y hy2
  have hLam : 11 * 2 ^ 12 * (Tb.stepParameters y).baseDepth < (Tb.stepParameters y).side := hD.L_gt
  intro T β k hOn e G κ S hside hle hSS
  have hSt := hOn.onFamily
  have hCo := hOn.measurable
  have hx : y ≤ (T.stage k).coupling := (hSt.onFamily k le_rfl).le_coupling
  have hx1 : 1 ≤ (T.stage k).coupling := hy3.trans hx
  have hr : 4 * Tb.n₀ + 2 ^ 16 + Tb.side * Tb.n₀ ≤ stageRange T k := le_clusterRange_of_pow_le (hy4.trans hx)
  have hL1 : 1 < Tb.side := lt_of_lt_of_le (by norm_num) hD.L_ge
  set a' := Nat.clog Tb.side (2 ^ 7 * stageRange T k) with ha'
  have hsd : G.side = Tb.side ^ a' := hside
  have h2r : 2 ^ 7 * stageRange T k ≤ G.side := by
    rw [hsd]
    exact Nat.le_pow_clog hL1 _
  have hle' : 2 * G.side ≤ 2 * Tb.side ^ e := hle
  have hae : a' ≤ e := by
    refine (Nat.pow_le_pow_iff_right hL1).mp ?_
    rw [← hsd]
    omega
  have he1 : e ≠ 0 := by
    rintro rfl
    have : a' = 0 := by omega
    rw [this, pow_zero] at hsd
    omega
  have hQ : 2 * (Tb.stepParameters y).side ^ e = G.side * (2 * Tb.side ^ (e - a')) := by
    have h1 : Tb.side ^ e = Tb.side ^ a' * Tb.side ^ (e - a') := by
      rw [← pow_add]
      congr 1
      omega
    show 2 * Tb.side ^ e = G.side * (2 * Tb.side ^ (e - a'))
    rw [h1, hsd]
    ring
  have hs : IsBlockTorusSide (Tb.stepParameters y) (2 * (Tb.stepParameters y).side ^ e) := by
    refine ⟨Dvd.dvd.mul_left (dvd_pow_self _ he1) 2, ?_⟩
    show Tb.side * Tb.n₀ ≤ 2 * Tb.side ^ e
    omega
  have hcut : ColdStepAtMirrorFrames.IsCutoff ((Tb.stepParameters y).threshold / 64) T.base.barrierFn := by
    have h0 : T.base.barrierFn = Tb.cutoff := (hSt.onFamily 0 (Nat.zero_le _)).barrierFn_eq
    rw [h0]
    exact hD.cut
  have main := markedSampleLaw_hullMeetsCells_le hD hfit h3 (hNc Tb hD).1 (hNc Tb hD).2 hcH hHb T β k
    (2 * (Tb.stepParameters y).side ^ e) hSt
    (A₁ T β k _ hSt hCo hs) (hLaw _ hfit hLam T hcut hCo β k _).1 (hBor _ hfit T k _) hs hx1
    (by
      have : 4 * Tb.n₀ + 2 ^ 16 ≤ stageRange T k := by omega
      exact this)
    G (Tb.side ^ (e - a')) (by omega) hQ (by omega) κ S hSS
  have ecast : (((2 * (Tb.stepParameters y).side ^ e : ℕ)) : ℝ) = 2 * ((Tb.stepParameters y).side : ℝ) ^ e := by
    push_cast
    rfl
  rw [ecast] at main
  exact main
end Main
end YangMills.Construction.CellWindows
end
