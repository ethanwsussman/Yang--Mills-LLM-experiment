import YangMills.Construction.ResponseInTheExpansion.MeansOfTheMovesAreCarriedProof
import YangMills.Construction.ResponseInTheExpansion.CalculusOfTheParts
import YangMills.Construction.ResponseInTheExpansion.ImageOfOneAtABlockProof
import YangMills.Construction.ResponseInTheExpansion.NumberOfTheResponseProof
import YangMills.Construction.ResponseInTheExpansion.TotalOfTheParts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory
open ColdStepAtMirrorFrames Interpolation BlockAverages TorusFields TorusLumps StepSettings StepCosts RenormalizationStepParameters
open ShareFamilies WeightedResponses Dilation FreeBonds
namespace ResponseInTheExpansion
open TermCalculus
namespace SumOfTerms
section Law
variable {F : BlockFrame}
theorem mem_finiteCells_of_nonempty (Y : F.Cell) (h : (finiteCells F).Nonempty) : Y ∈ finiteCells F := by
  unfold finiteCells at h ⊢
  by_cases hf : Finite F.Cell
  · rw [dif_pos hf]
    exact @Finset.mem_univ _ (Fintype.ofFinite _) _
  · rw [dif_neg hf] at h
    simp at h
theorem mem_finiteCells_of_mem_sites {j : ℕ} {y : F.Site j} (h : y ∈ sitesOfCells (finiteCells F) j) (Y : F.Cell) :
    Y ∈ finiteCells F := by
  obtain ⟨z, hz, -⟩ := Finset.mem_biUnion.1 h
  exact _root_.YangMills.Construction.ResponseInTheExpansion.SumOfTerms.mem_finiteCells_of_nonempty Y ⟨z, hz⟩
theorem mem_finiteCells_of_mem_bonds {j : ℕ} {b : F.Site j × Fin 4} (h : b ∈ innerBonds (finiteCells F) j) (Y : F.Cell) :
    Y ∈ finiteCells F := mem_finiteCells_of_mem_sites (Finset.mem_product.1 (Finset.filter_subset _ _ h)).1 Y
theorem mem_finiteCells_of_mem_chord {b : F.Site F.depth × Fin 4} (h : b ∈ chordBonds (finiteCells F)) (Y : F.Cell) :
    Y ∈ finiteCells F := by
  classical
  unfold chordBonds at h
  exact _root_.YangMills.Construction.ResponseInTheExpansion.SumOfTerms.mem_finiteCells_of_mem_bonds (Finset.filter_subset _ _ h) Y
theorem sum_cells_chord_indicator (u : ↥(chordBonds (finiteCells F)) → ℝ) :
    (open Classical in ∑ Y ∈ finiteCells F, ∑ b : ↥(chordBonds (finiteCells F)), if enclosingCell b.1.1 = Y then u b else 0) = ∑ b, u b := by
  classical
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_ite_eq, if_pos (_root_.YangMills.Construction.ResponseInTheExpansion.SumOfTerms.mem_finiteCells_of_mem_chord b.2 _)]
theorem segmentEnd_false : segmentEnd false = 1 := by simp [segmentEnd]
theorem sum_linearBlockPart (hE : interpolationAtEndpoints) (Q : ColdHalfLaw) (V : F.GaugeField F.top) (η : StepVariable (finiteCells F))
    (hsum : stepExponent false Q.a Q.chartRadius Q.coupling Q.mirrorRadius Q.family 0 V η = ∑ Y ∈ finiteCells F, cellExponent false Q.a Q.chartRadius Q.coupling Q.mirrorRadius Y V η) :
    ∑ Y ∈ finiteCells F, Q.linearBlockPart Y η V = Q.coupling * (Q.totalCost η V - Q.totalCost 0 V) := by
  classical
  have hab : ∀ ζ, interpolatedCoords 1 Q.a Q.chartRadius Q.mirrorRadius V ζ = coordsAboveFrame false Q.a Q.chartRadius Q.mirrorRadius V ζ := fun ζ => by
    have := (hE F false Q.a Q.chartRadius 0 Q.coupling 0 Q.mirrorRadius V).2.1 ζ
    rwa [segmentEnd_false] at this
  have hY : ∀ Y, Q.linearBlockPart Y η V = cellExponent false Q.a Q.chartRadius Q.coupling Q.mirrorRadius Y V η +
      (∑ c ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y), haarGapExcess Q.a Q.coupling (fieldAboveFrame false Q.a Q.chartRadius Q.mirrorRadius V η) c) +
      ∑ b : ↥(chordBonds (finiteCells F)), if enclosingCell b.1.1 = Y then
        haarLogRatio (coordsAboveFrame false Q.a Q.chartRadius Q.mirrorRadius V η b.1.1 b.1.2) else 0 := fun Y => by
    unfold ColdHalfLaw.linearBlockPart cellExponent
    simp only [hab]
    ring
  have e₁ : ∑ Y ∈ finiteCells F, ∑ c ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y),
      haarGapExcess Q.a Q.coupling (fieldAboveFrame false Q.a Q.chartRadius Q.mirrorRadius V η) c =
      ∑ c ∈ innerBonds (finiteCells F) F.top, haarGapExcess Q.a Q.coupling (fieldAboveFrame false Q.a Q.chartRadius Q.mirrorRadius V η) c :=
    Finset.sum_fiberwise_of_maps_to (fun c hc => _root_.YangMills.Construction.ResponseInTheExpansion.SumOfTerms.mem_finiteCells_of_mem_bonds hc _) _
  have e₂ := sum_cells_chord_indicator (F := F) fun b => haarLogRatio (coordsAboveFrame false Q.a Q.chartRadius Q.mirrorRadius V η b.1.1 b.1.2)
  simp only [hY, Finset.sum_add_distrib]
  rw [← hsum, e₁, e₂]
  unfold stepExponent ColdHalfLaw.totalCost
  rw [hab, hab]
  ring
theorem ballExpectation_finset_sum {ι : Type} [Fintype ι] {ρ : ℝ} {r : ℝ → ℝ} {Ψ : BondField ι → ℝ} (hL : IsBallLaw ρ r Ψ) {J : Type} (s : Finset J)
    {H : J → BondField ι → ℝ} (h : ∀ j ∈ s, Integrable fun η => H j η * ballDensity r Ψ η) :
    ballExpectation r Ψ (fun η => ∑ j ∈ s, H j η) = ∑ j ∈ s, ballExpectation r Ψ (H j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using ballExpectation_const hL 0
  | insert a s ha ih =>
    have i₁ : Integrable fun η => (∑ j ∈ s, H j η) * ballDensity r Ψ η := by
      refine (integrable_finsetSum s fun j hj => h j (Finset.mem_insert_of_mem hj)).congr
        (Filter.Eventually.of_forall fun η => ?_)
      simp only [Finset.sum_mul]
    simp only [Finset.sum_insert ha]
    rw [ballExpectation_add hL (h a (Finset.mem_insert_self _ _)) i₁, ih fun j hj => h j (Finset.mem_insert_of_mem hj)]
theorem ballExpectation_congr_ball {ι : Type} [Fintype ι] {ρ : ℝ} {r : ℝ → ℝ} {Ψ : BondField ι → ℝ} (hL : IsBallLaw ρ r Ψ)
    {H H' : BondField ι → ℝ} (h : ∀ k, (∀ b, ‖k b‖ < ρ) → H k = H' k) : ballExpectation r Ψ H = ballExpectation r Ψ H' := by
  unfold ballExpectation
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  by_cases hk : ∀ b, ‖k b‖ < ρ
  · show H k * _ = H' k * _
    rw [h k hk]
  · show H k * _ = H' k * _
    rw [hL.eq_zero_outside k hk]
    simp
theorem expectation_eq_cutoffMean (hE : interpolationAtEndpoints) (Q : ColdHalfLaw) (V : F.GaugeField F.top) (H : StepVariable (finiteCells F) → ℝ) :
    Q.expectation V H = cutoffMean Q.ballRadius Q.cutoff (stepExponent false Q.a Q.chartRadius Q.coupling Q.mirrorRadius Q.family 1 V) H := by apply _root_.YangMills.Construction.ResponseInTheExpansion.ExpectationsEquivariant.expectation_eq_cutoffMean <;> assumption
theorem integrable_move_mul_density {ρ' x κ g₀ g₁ : ℝ} {Y : F.Cell} {A : StepVariable (finiteCells F) → ℝ} {r : ℝ → ℝ}
    {Ψ : StepVariable (finiteCells F) → ℝ} (hL : IsBallLaw ρ' r Ψ) (hM : IsVanishingMoveWithGradient ρ' x κ g₀ g₁ Y A) :
    Integrable fun η => A η * ballDensity r Ψ η := by
  obtain ⟨M, hb⟩ := hM.bounded
  exact integrable_mul_density_of_bounded hL hM.smooth.continuousOn hb
theorem integrable_increment_linear {T' : ColdStepAtMirrorFrames.StepParameters} {x C : ℝ} {f : LocalFamily} {t : ℕ} {V : F.GaugeField F.top} {Q : ColdHalfLaw} (hQ : coldHalfLawAt T' x f = Q)
    (hb : smoothIncrementBoundsAt T' C) (hS : IsAdmissibleAt T' t x f F V) (hr : IsRegularFamily T'.L t T'.n₀ T'.σ T'.decayRate T'.E T'.energyRatio f)
    (hL : IsBallLaw T'.ballRadius Q.radialWeight (Q.exponent V)) (Z : F.Cell) :
    (Integrable fun η => Q.blockIncrement Z η V * ballDensity Q.radialWeight (Q.exponent V) η) ∧
      Integrable fun η => Q.linearBlockPart Z η V * ballDensity Q.radialWeight (Q.exponent V) η := by
  subst hQ
  obtain ⟨m, s, -, -⟩ := hb t x f F V Z hS hr
  exact ⟨integrable_move_mul_density hL m, integrable_move_mul_density hL s⟩
theorem sum_expectation_increment_linear (Q : ColdHalfLaw) (V : F.GaugeField F.top) (hL : IsBallLaw Q.ballRadius Q.radialWeight (Q.exponent V))
    (hi : ∀ Z : F.Cell, (Integrable fun η => Q.blockIncrement Z η V * ballDensity Q.radialWeight (Q.exponent V) η) ∧
      Integrable fun η => Q.linearBlockPart Z η V * ballDensity Q.radialWeight (Q.exponent V) η)
    (hm : ∀ η : StepVariable (finiteCells F), ∑ Z ∈ finiteCells F, Q.blockCost Z η V = Q.totalCost η V)
    (hs : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < Q.ballRadius) →
      ∑ Z ∈ finiteCells F, Q.linearBlockPart Z η V = Q.coupling * (Q.totalCost η V - Q.totalCost 0 V)) :
    (∑ Z ∈ finiteCells F, Q.expectationOf (Q.blockIncrement Z) V = Q.expectation V fun η => Q.totalCost η V - Q.totalCost 0 V) ∧
    ∑ Z ∈ finiteCells F, Q.expectationOf (Q.linearBlockPart Z) V = Q.coupling * Q.expectation V fun η => Q.totalCost η V - Q.totalCost 0 V := by
  refine ⟨?_, ?_⟩
  · have e := ballExpectation_finset_sum hL (finiteCells F) (H := fun Z η => Q.blockIncrement Z η V) fun Z _ => (hi Z).1
    have e' : (fun η => ∑ Z ∈ finiteCells F, Q.blockIncrement Z η V) = fun η => Q.totalCost η V - Q.totalCost 0 V := by
      funext η
      simp only [ColdHalfLaw.blockIncrement, Finset.sum_sub_distrib, hm]
    rw [e'] at e
    exact e.symm
  · have e := ballExpectation_finset_sum hL (finiteCells F) (H := fun Z η => Q.linearBlockPart Z η V) fun Z _ => (hi Z).2
    have e' := ballExpectation_congr_ball hL (H := fun η => ∑ Z ∈ finiteCells F, Q.linearBlockPart Z η V)
      (H' := fun η => Q.coupling * (Q.totalCost η V - Q.totalCost 0 V)) hs
    rw [e'] at e
    rw [ballExpectation_const_mul] at e
    exact e.symm
end Law
section Ties
variable {H : BlockFrame} {m : ℕ}
theorem plaquetteDefect_readAtLevel_eq_curvature {H : BlockFrame} {j m : ℕ} (hm : ∀ i, H.period j i = m) (W : TorusField m)
    (p : H.Site j × Fin 4 × Fin 4) :
    plaquetteDefect (readAtLevel H j W) p = TorusFields.curvature W (toTorusSite m p.1) p.2.1 p.2.2 := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.plaquetteDefect_readAtLevel_torus <;> assumption
theorem period_top_of_extent {n : ℕ} (hs : ∀ i, H.extent i = n) (i : Fin 4) : H.period H.top i = n := by
  simp [BlockFrame.period, hs]
theorem isSmallCurvature_readAtLevel {H : BlockFrame} {j m : ℕ} (hm : ∀ i, H.period j i = m) {s s' : ℝ} (hs : s ≤ s') {W : TorusField m}
    (hW : IsCold s W) : IsSmallCurvature s' (readAtLevel H j W) := by
  intro p hp
  rw [plaquetteDefect_readAtLevel_eq_curvature hm]
  exact (hW _ _ _ hp).trans_le hs
theorem sum_torus_eq_sum_finiteCells {L t n : ℕ} [NeZero n] (g : (torusFrame L t n).Cell → ℝ) :
    ∑ Y : TorusSite n, g (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top Y) =
      ∑ Y ∈ finiteCells (torusFrame L t n), g Y := by apply _root_.YangMills.SharedProofs.p4810 <;> assumption
end Ties
section Top
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem sum_densityOfTopFamily_conditionalMean (hE : interpolationAtEndpoints) {V : TorusField n}
    (hL : IsBallLaw R.ballRadius (coldHalfLawOf R).radialWeight ((coldHalfLawOf R).exponent (coldTopField R V))) (h : LocalDensity)
    (hrow : ∀ (k : StepVariable (finiteCells (torusFrame R.params.side R.depth n))) (Y : TorusSite n),
      cellCentredExpansion false R.params.coupling R.anchorRadius R.frameReach (localFamilyOfDensity h)
          (torusSiteInFrame (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top Y) k (coldTopField R V) =
        ∑ y ∈ sitesInBlocks R.params.side {Y}, centered h (n * R.params.side) y (coldFieldAboveFrames R V k))
    (hint : ∀ y : TorusSite (n * R.params.side), Integrable fun k => centered h (n * R.params.side) y (coldFieldAboveFrames R V k) * coldHalfDensity R V k) :
    ∑ Y, densityOfTopFamily R.params.side R.depth (blockConditionalMean R h) n Y V =
      (coldHalfLawOf R).expectation (coldTopField R V) fun k => ∑ y, centered h (n * R.params.side) y (coldFieldAboveFrames R V k) := by
  classical
  have e : ∀ Y : TorusSite n, densityOfTopFamily R.params.side R.depth (blockConditionalMean R h) n Y V =
      ballExpectation (coldHalfLawOf R).radialWeight ((coldHalfLawOf R).exponent (coldTopField R V))
        (fun k => ∑ y ∈ sitesInBlocks R.params.side {Y}, centered h (n * R.params.side) y (coldFieldAboveFrames R V k)) := fun Y => by
    have h1 := expectation_eq_cutoffMean hE (coldHalfLawOf R) (coldTopField R V) (fun η => cellCentredExpansion false R.params.coupling R.anchorRadius R.frameReach (localFamilyOfDensity h)
      (torusSiteInFrame (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top Y) η (coldTopField R V))
    refine h1.symm.trans ?_
    show ballExpectation _ _ _ = _
    congr 1
    funext k
    exact hrow k Y
  simp only [e]
  have hi : ∀ Y ∈ (Finset.univ : Finset (TorusSite n)), Integrable fun k =>
      (∑ y ∈ sitesInBlocks R.params.side {Y}, centered h (n * R.params.side) y (coldFieldAboveFrames R V k)) *
        ballDensity (coldHalfLawOf R).radialWeight ((coldHalfLawOf R).exponent (coldTopField R V)) k := fun Y _ => by
    refine (integrable_finsetSum (sitesInBlocks R.params.side {Y}) fun y _ => hint y).congr
      (Filter.Eventually.of_forall fun k => ?_)
    simp only [Finset.sum_mul]
    rfl
  rw [← ballExpectation_finset_sum hL _ hi]
  show ballExpectation _ _ _ = ballExpectation _ _ _
  congr 1
  funext k
  simp only [sitesInBlocks, Finset.mem_singleton]
  exact Finset.sum_fiberwise _ _ _
theorem levelShare_sub_action_eq_trivial (hSh : LevelSharesFormCurvatureFamily) {T : ParameterAssignment} (hD : T.Admissible) {y : ℝ} (hy : T.floorMin ≤ y)
    (t : ℕ) {m : ℕ} [NeZero m] (hm : T.n₀ ≤ m) {W : TorusField m} (hW : IsCold T.threshold W) :
    ∑ z, levelShare T.coupling T.side t Finset.univ z W - actionAtLevel T.coupling T.side t Finset.univ W =
      ∑ z, levelShare T.coupling T.side t Finset.univ z (trivialField m) - actionAtLevel T.coupling T.side t Finset.univ (trivialField m) := by
  cases t with
  | zero =>
    rw [sum_levelShare_zero, sum_levelShare_zero]
    simp
  | succ t =>
    obtain ⟨-, -, h₃⟩ := hSh T hD y hy t
    have b₁ := h₃ m hm W hW
    have b₂ := h₃ m hm (trivialField m) (isCold_trivialField hD.σ_pos m)
    have ne : m ≠ 0 := NeZero.ne m
    simp only [centered, levelShareFamily, dif_neg ne, Finset.sum_sub_distrib] at b₁ b₂
    simp only [sub_self] at b₂
    linarith
theorem abs_centered_le {ℓ : TorusLumps.StepParameters} {E E₃ : ℝ} {h : LocalDensity} (hf : ColdDensityBounds ℓ E E₃ h) (hσ : 0 < ℓ.threshold) {m : ℕ} [NeZero m]
    (hm : ℓ.n₀ ≤ m) (hm2 : 2 < m) (y : TorusSite m) {W : TorusField m} (hW : IsCold ℓ.threshold W) :
    |centered h m y W| ≤ E / ℓ.weight 0 := by apply _root_.YangMills.Construction.ResponseInTheExpansion.BlockImageOfOne.abs_centered_le_of_isCold <;> assumption
end Top
end SumOfTerms
open SumOfTerms in
set_option maxHeartbeats 1600000 in
theorem sumOfTermsStatement_holds (hOne : imageOfOneAtBlockStatement) (hLw : coldHalfLawIsLawStatement)
    (hSc : scoresAboveFramesStatement) (hCS : ColdChartSettingIsCold) (hSh : LevelSharesFormCurvatureFamily)
    (hSum : sumCellSharesEqAction) (hE : interpolationAtEndpoints) (hRB : ColdExpansionRegular) :
    sumOfTermsStatement := by
  obtain ⟨r₂, hr₂, g₂⟩ := hOne
  refine ⟨r₂, hr₂, fun T hD hCd hOn hrt K => ?_⟩
  obtain ⟨y₂, g₂⟩ := g₂ T hD hrt K
  obtain ⟨y₃, g₃⟩ := hLw T hD hCd
  obtain ⟨y₄, g₄⟩ := hSc T hD hCd
  obtain ⟨y₅, g₅⟩ := hCS T hD
  obtain ⟨c, nss, hTies, hAll⟩ := hOn
  have hCd₁ := hCd
  obtain ⟨c', nss', hTies', hAll'⟩ := hCd₁
  refine ⟨max (max y₂ y₃) (max (max y₄ y₅) (max T.floorMin T.yC)), fun y hy R A hK hA => ?_⟩
  have f₁ := (le_max_left _ _).trans hy
  have f₂ := (le_max_right _ _).trans hy
  have e₂ : y₂ ≤ y := (le_max_left _ _).trans f₁
  have e₃ : y₃ ≤ y := (le_max_right _ _).trans f₁
  have f₃ := (le_max_left _ _).trans f₂
  have f₄ := (le_max_right _ _).trans f₂
  have e₄ : y₄ ≤ y := (le_max_left _ _).trans f₃
  have e₅ : y₅ ≤ y := (le_max_right _ _).trans f₃
  have hy0 : T.floorMin ≤ y := (le_max_left _ _).trans f₄
  have hyC : T.yC ≤ y := (le_max_right _ _).trans f₄
  have hon := hA.onFamily
  have hℓ : R.params = T.stepParameters y := hon.params_eq
  have hxy : y ≤ R.coupling := hon.le_coupling
  have hresp := hA.admissible
  have hfit : R.params.Admissible := by
    rw [hℓ]
    exact hD.fits y hy0
  have hσ : 0 < R.params.threshold := hfit.σ_pos
  have hn₁ : R.params.n₁ = (R.params.side : ℝ) ^ (1 / 640 : ℝ) := by rw [hℓ]; rfl
  have expansionF := hRB R.params R.depth R.coupling R.functional R.density hfit hn₁ hon.isStep.1.1
  rw [hℓ] at expansionF
  have ha : R.params.coupling = T.coupling := by rw [hℓ]; rfl
  have hLe : R.params.side = T.side := by rw [hℓ]; rfl
  have hn₀ : R.params.n₀ = T.n₀ := by rw [hℓ]; rfl
  have hσe : R.params.threshold = T.threshold := by rw [hℓ]; rfl
  have hρe : R.ballRadius = T.threshold / 64 := by
    show R.params.threshold / 64 = _
    rw [hσe]
  have hρA : c.ρA = T.ρA := hTies.2.2.1
  have hρA' : c'.ρA = T.ρA := hTies'.2.2.1
  have hQ : coldHalfLawAt (T.stepParamsAt c nss y) R.coupling (localFamilyOfDensity R.density) = coldHalfLawOf R := by
    have h3 : R.params.rt = T.rt := by rw [hℓ]; rfl
    unfold coldHalfLawOf
    rw [ha, hρe, h3, hon.anchorRadius_eq, hon.barrierFn_eq, ← hρA]
    rfl
  have H := hAll y hyC
  obtain ⟨Cb, hb⟩ := H.incrementBounds
  have Dn := hAll' y hyC R.depth R.coupling hxy (localFamilyOfDensity R.density) expansionF
  have one := g₂ y e₂ R A hK hA hCd
  have hodd : Odd R.params.side := hfit.L_odd
  have hσT : 0 < T.threshold := hD.σ_pos
  have hL0 : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hn4 : 4096 ≤ T.n₀ := hD.n₀_ge
  have hsl : ∀ (m : ℕ) [NeZero m], R.params.n₀ ≤ m → ∀ W : TorusField m, IsCold R.params.threshold W →
      ∑ z, levelShare R.params.coupling R.params.side R.depth Finset.univ z W - actionAtLevel R.params.coupling R.params.side R.depth Finset.univ W =
        ∑ z, levelShare R.params.coupling R.params.side R.depth Finset.univ z (trivialField m) - actionAtLevel R.params.coupling R.params.side R.depth Finset.univ (trivialField m) := by
    intro m _ hm W hW
    have := levelShare_sub_action_eq_trivial hSh hD hy0 R.depth (m := m) (by omega) (W := W) (hσe ▸ hW)
    rw [← ha, ← hLe] at this
    exact this
  have top : ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n → ∀ V : TorusField n, IsCold R.params.threshold V →
      (∑ Y, linearTerm A n Y V = A.coeff * (coldHalfLawOf R).expectation (coldTopField R V)
        (fun η => (coldHalfLawOf R).totalCost η (coldTopField R V) - (coldHalfLawOf R).totalCost 0 (coldTopField R V))) ∧
      (∑ Y, incrementTerm A n Y V = A.coeff * (coldHalfLawOf R).expectation (coldTopField R V)
        (fun η => (coldHalfLawOf R).totalCost η (coldTopField R V) - (coldHalfLawOf R).totalCost 0 (coldTopField R V))) := by
    intro n _ hn V hV
    have hn' : T.n₀ ≤ n := hn₀ ▸ hn
    have hV' : IsCold (9 / 8 * T.threshold) V := fun x μ ν hμ => by
      have := hV x μ ν hμ
      rw [hσe] at this
      linarith
    obtain ⟨hL, -, -, -, -⟩ := g₃ y e₃ R hon n hn' V hV'
    have hm : ∀ i, (torusFrame R.params.side R.depth n).period (torusFrame R.params.side R.depth n).top i = n := fun i =>
      period_top_of_extent (H := torusFrame R.params.side R.depth n) (fun _ => rfl) i
    have hc54 : IsSmallCurvature (5 / 4 * T.threshold) (coldTopField R V) := isSmallCurvature_readAtLevel hm (s := R.params.threshold) (by rw [hσe]; linarith) hV
    have hc98 : IsSmallCurvature (9 / 8 * T.threshold) (coldTopField R V) := isSmallCurvature_readAtLevel hm (s := R.params.threshold) (by rw [hσe]; linarith) hV
    have htopT : IsCubicTopTorus T.side R.depth T.n₀ (torusFrame R.params.side R.depth n) := ⟨hLe, rfl, n, fun _ => rfl, hn'⟩
    obtain ⟨-, M, hreg⟩ := Dn.regular (torusFrame R.params.side R.depth n) htopT (coldTopField R V) hc98
    have hs2 : ∀ i, 2 ≤ (torusFrame R.params.side R.depth n).extent i := fun _ => by
      show 2 ≤ n
      omega
    have hsum0 : ∀ η : StepVariable (finiteCells (torusFrame R.params.side R.depth n)), (∀ b, ‖η b‖ < (coldHalfLawOf R).ballRadius) →
        stepExponent false (coldHalfLawOf R).a (coldHalfLawOf R).chartRadius (coldHalfLawOf R).coupling (coldHalfLawOf R).mirrorRadius (coldHalfLawOf R).family 0 (coldTopField R V) η =
          ∑ Y ∈ finiteCells (torusFrame R.params.side R.depth n),
            cellExponent false (coldHalfLawOf R).a (coldHalfLawOf R).chartRadius (coldHalfLawOf R).coupling (coldHalfLawOf R).mirrorRadius Y (coldTopField R V) η := fun η hη => by
      have h1 := hreg.stepExponent_eq_sum η (fun b => by
        have := hη b
        show ‖η b‖ < T.threshold / 64
        rw [← hρe]
        exact this)
      show stepExponent false R.params.coupling R.anchorRadius R.coupling R.frameReach (localFamilyOfDensity R.density) 0 _ η =
        ∑ Y ∈ finiteCells _, cellExponent false R.params.coupling R.anchorRadius R.coupling R.frameReach Y _ η
      rw [ha, hon.anchorRadius_eq, ← hρA']
      exact h1
    have hs := fun η hη => sum_linearBlockPart hE (coldHalfLawOf R) (coldTopField R V) η (hsum0 η hη)
    have hcost : ∀ η : StepVariable (finiteCells (torusFrame R.params.side R.depth n)),
        ∑ Z ∈ finiteCells (torusFrame R.params.side R.depth n), (coldHalfLawOf R).blockCost Z η (coldTopField R V) = (coldHalfLawOf R).totalCost η (coldTopField R V) :=
      fun η => (hSum (torusFrame R.params.side R.depth n) (coldHalfLawOf R).a _ (coldTopField R V)
        (by show 0 ≤ R.params.coupling; rw [ha]; linarith [hD.a_ge]) hodd hs2).2
    have hStand : IsAdmissibleAt (T.stepParamsAt c nss y) R.depth R.coupling (localFamilyOfDensity R.density) (torusFrame R.params.side R.depth n) (coldTopField R V) :=
      ⟨hxy, ⟨expansionF.smooth, expansionF.gauge_invariant, expansionF.translation_invariant, expansionF.decay, expansionF.locality⟩, htopT, hc54⟩
    have hLρ : IsBallLaw (T.stepParamsAt c nss y).ballRadius (coldHalfLawOf R).radialWeight ((coldHalfLawOf R).exponent (coldTopField R V)) := by
      have : (T.stepParamsAt c nss y).ballRadius = (coldHalfLawOf R).ballRadius := hρe.symm
      rw [this]
      exact hL
    have hi := integrable_increment_linear hQ hb hStand expansionF hLρ
    obtain ⟨mv, sl⟩ := sum_expectation_increment_linear (coldHalfLawOf R) (coldTopField R V) hL hi hcost hs
    have hx0 : R.coupling ≠ 0 := (lt_of_lt_of_le (lt_of_lt_of_le one_pos hD.yC_ge) (hyC.trans hxy)).ne'
    refine ⟨?_, ?_⟩
    · show ∑ Y : TorusSite n, A.coeff / R.coupling * (coldHalfLawOf R).expectationOf ((coldHalfLawOf R).linearBlockPart
        (torusSiteInFrame (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top Y)) (coldTopField R V) = _
      rw [← Finset.mul_sum, sum_torus_eq_sum_finiteCells fun Z => (coldHalfLawOf R).expectationOf ((coldHalfLawOf R).linearBlockPart Z) (coldTopField R V), sl]
      show A.coeff / R.coupling * (R.coupling * _) = _
      field_simp
    · show ∑ Y : TorusSite n, A.coeff * (coldHalfLawOf R).expectationOf ((coldHalfLawOf R).blockIncrement
        (torusSiteInFrame (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top Y)) (coldTopField R V) = _
      rw [← Finset.mul_sum, sum_torus_eq_sum_finiteCells fun Z => (coldHalfLawOf R).expectationOf ((coldHalfLawOf R).blockIncrement Z) (coldTopField R V), mv]
  have fam : ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n → ∀ V : TorusField n, IsCold R.params.threshold V →
      ∑ Y, densityOfTopFamily R.params.side R.depth (blockConditionalMean R A.siteRemainder) n Y V = ∑ Y, densityOfTopFamily R.params.side R.depth (blockConditionalMean R A.totalRemainder) n Y V -
        A.coeff * (∑ z, @levelShare (n * R.params.side) ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne _)⟩ R.params.coupling R.params.side R.depth Finset.univ z (trivialField _) -
          @actionAtLevel (n * R.params.side) ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne _)⟩ R.params.coupling R.params.side R.depth Finset.univ (trivialField _)) := by
    intro n _ hn V hV
    have hNZ : NeZero (n * R.params.side) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne _)⟩
    have hn' : T.n₀ ≤ n := hn₀ ▸ hn
    have hnL : n ≤ n * R.params.side := Nat.le_mul_of_pos_right n hL0
    have hmL : R.params.n₀ ≤ n * R.params.side := hn.trans hnL
    have hV' : IsCold (9 / 8 * T.threshold) V := fun x μ ν hμ => by
      have := hV x μ ν hμ
      rw [hσe] at this
      linarith
    obtain ⟨hL, -, hpt, hG, -⟩ := g₃ y e₃ R hon n hn' V hV'
    obtain ⟨-, hrow, -, -, -⟩ := g₄ y e₄ R hon n hn' V hV'
    have hcold : ∀ k : StepVariable (finiteCells (torusFrame R.params.side R.depth n)), (∀ b, ‖k b‖ < R.ballRadius) →
        IsCold R.params.threshold (coldFieldAboveFrames R V k) := by
      intro k hk x μ ν hμ
      obtain ⟨η, hη, e⟩ := hpt k hk
      have := g₅ y e₅ R hon n hn' V hV' η (fun b => (hη b).le) x μ ν hμ
      rw [← e, hσe]
      linarith
    have h2 : 2 < n * R.params.side := by omega
    have intH : ∀ {h : LocalDensity} {E E₃ : ℝ}, ColdDensityBounds R.params E E₃ h → ∀ y' : TorusSite (n * R.params.side),
        Integrable fun k => centered h (n * R.params.side) y' (coldFieldAboveFrames R V k) * coldHalfDensity R V k := fun {h E E₃} hf y' =>
      integrable_mul_density_of_bounded hL (R := E / R.params.weight 0)
        (hG (centered h (n * R.params.side) y') fun W hW k c X => (hf.smooth _ hmL y' W hW k c X).sub contDiffAt_const)
        fun k hk => abs_centered_le hf hσ hmL h2 y' (hcold k hk)
    have row := hresp.bounds
    rw [sum_densityOfTopFamily_conditionalMean hE hL A.siteRemainder (hrow A.siteRemainder) (intH row.site_family),
      sum_densityOfTopFamily_conditionalMean hE hL A.totalRemainder (hrow A.totalRemainder) (intH row.total_family)]
    set c₀ : ℝ := ∑ z, levelShare R.params.coupling R.params.side R.depth Finset.univ z (trivialField (n * R.params.side)) -
      actionAtLevel R.params.coupling R.params.side R.depth Finset.univ (trivialField (n * R.params.side)) with hc₀
    have hpoint : ∀ k : StepVariable (finiteCells (torusFrame R.params.side R.depth n)), (∀ b, ‖k b‖ < R.ballRadius) →
        ∑ y', centered A.siteRemainder (n * R.params.side) y' (coldFieldAboveFrames R V k) =
          ∑ y', centered A.totalRemainder (n * R.params.side) y' (coldFieldAboveFrames R V k) + -(A.coeff * c₀) := fun k hk => by
      have hW := hcold k hk
      have e₁ : ∑ z, centeredResponse A.cold (n * R.params.side) z (coldFieldAboveFrames R V k) (constOneWeight _) =
          A.coeff * ∑ z, levelShare R.params.coupling R.params.side R.depth Finset.univ z (coldFieldAboveFrames R V k) + ∑ z, centered A.siteRemainder (n * R.params.side) z (coldFieldAboveFrames R V k) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun z _ => row.share_site _ hmL z _ hW
      have e₂ := row.share_total _ hmL _ hW
      have e₃ := hsl _ hmL _ hW
      linear_combination (e₂ - e₁) - A.coeff * e₃
    show ballExpectation _ _ _ = ballExpectation _ _ _ - _
    rw [ballExpectation_congr_ball hL hpoint]
    have iRb : Integrable fun k => (∑ y', centered A.totalRemainder (n * R.params.side) y' (coldFieldAboveFrames R V k)) *
        ballDensity (coldHalfLawOf R).radialWeight ((coldHalfLawOf R).exponent (coldTopField R V)) k := by
      refine (integrable_finsetSum Finset.univ fun y' _ => intH row.total_family y').congr
        (Filter.Eventually.of_forall fun k => ?_)
      simp only [Finset.sum_mul]
      rfl
    rw [ballExpectation_add hL iRb (hL.integrable.const_mul _), ballExpectation_const hL]
    ring
  refine ⟨fun n _ hn V hV => (top n hn V hV).1, ⟨fun n _ hn W hW => ?_⟩⟩
  have hFl := isCold_trivialField hσ n
  have hn' : T.n₀ ≤ n := hn₀ ▸ hn
  have ne : n ≠ 0 := NeZero.ne n
  obtain ⟨-, -, h₃⟩ := hSh T hD y hy0 R.depth
  have act := h₃ n hn' W (hσe ▸ hW)
  simp only [centered, levelShareFamily, dif_neg ne, Finset.sum_sub_distrib] at act
  rw [← ha, ← hLe] at act
  have osum : ∀ V : TorusField n, IsCold R.params.threshold V → ∑ Y, A.coldStep n Y V (constOneWeight _) =
      A.coeff * ∑ Y, levelShare R.params.coupling R.params.side (R.depth + 1) Finset.univ Y V + ∑ Y, frameTerm A n Y V + ∑ Y, incrementTerm A n Y V +
        ∑ Y, densityOfTopFamily R.params.side R.depth (blockConditionalMean R A.siteRemainder) n Y V + ∑ Y, scoreTailTerm A n Y V + ∑ Y, gasTerm A n Y V +
        ∑ Y, blockConstantTerm A n Y := fun V hV => by
    rw [Finset.sum_congr rfl fun Y _ => one n hn Y V hV]
    simp only [Finset.sum_add_distrib, Finset.mul_sum]
  obtain ⟨s₁, m₁⟩ := top n hn W hW
  obtain ⟨s₂, m₂⟩ := top n hn (trivialField n) hFl
  have r₁ := fam n hn W hW
  have r₂ := fam n hn (trivialField n) hFl
  simp only [centeredResponse, centered, totalRemainderOfTerms, remainderTerm, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [osum W hW, osum (trivialField n) hFl, m₁, m₂, s₁, s₂, r₁, r₂, ← act]
  ring
end ResponseInTheExpansion
end YangMills.Construction
end
