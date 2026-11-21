import YangMills.Construction.FormsOnATorus.ChainMeansAreCarried
import YangMills.Construction.FormsOnATorus.ChainMeansOfFarFunctionsSplit
import YangMills.Construction.FormsOnATorus.ChanceOfAPlaquetteAgainstItsMirrors
import YangMills.Construction.FormsOnATorus.ChessboardOnTheFieldsOfATorus
import YangMills.Construction.FormsOnATorus.CornersOfTheImagesOfAPlaquette
import YangMills.Construction.FormsOnATorus.LawOfTheTopIsTheChainMean
import YangMills.Construction.LawInAState.ProductsOfMarksAtOneLevelProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.WeightedResponses YangMills.Construction.TorusFields
open YangMills.Construction.TorusLumps YangMills.Construction.RenormalizationStepParameters
section RadiusBounds
private theorem descendedRadius_add_five_le {L : ℕ} (hL : 5 ≤ L) (s r : ℕ) :
    descendedRadius L s r + 5 ≤ L ^ s * (r + 5) := by
  induction s generalizing r with
  | zero => simp [descendedRadius]
  | succ s ih =>
    have h1 := ih (L * r + 4 * L)
    have h2 : L * r + 4 * L + 5 ≤ L * (r + 5) := by nlinarith
    have h3 : L ^ s * (L * r + 4 * L + 5) ≤ L ^ s * (L * (r + 5)) := Nat.mul_le_mul_left _ h2
    have h4 : L ^ (s + 1) * (r + 5) = L ^ s * (L * (r + 5)) := by ring
    show descendedRadius L s (L * r + 4 * L) + 5 ≤ _
    omega
private theorem iteratedScaledLift_eq (L : ℕ) (s : ℕ) (g : TorusIsometry) :
    iteratedScaledLift L s g = ⟨g.axisPerm, g.axisSign, fun i => (L : ℤ) ^ s * g.offset i, g.axisSign_unit⟩ := by
  induction s generalizing g with
  | zero => simp [iteratedScaledLift]
  | succ s ih =>
    show iteratedScaledLift L s (g.scaledLift L) = _
    rw [ih]
    simp only [TorusIsometry.scaledLift]
    congr 1
    funext i
    ring
private theorem iteratedScaledLift_cellReflection (L s : ℕ) (u k : Fin 4 → ℤ) :
    iteratedScaledLift L s (cellReflection L u k) =
      cellReflection (L ^ (s + 1)) (fun i => (L : ℤ) ^ s * u i) k := by
  rw [iteratedScaledLift_eq]
  simp only [cellReflection]
  congr 1
  funext i
  push_cast
  ring
end RadiusBounds
section MarkedToChain
variable {ℓ : StepParameters}
private theorem finalField_forgetMarks (s n : ℕ) (u : MarkedSample ℓ s n) :
    finalField ℓ s n (forgetMarks ℓ s n u) = topField ℓ s n u := by apply _root_.YangMills.SharedProofs.p8091 <;> assumption
private theorem measurable_forgetMarks : (s n : ℕ) → Measurable (forgetMarks ℓ s n)
  | 0, _ => measurable_id
  | s + 1, n => by
    letI := markedSampleMeasurableSpace ℓ s (n * ℓ.side)
    letI := chainSampleMeasurableSpace ℓ s (n * ℓ.side)
    exact ((measurable_forgetMarks s (n * ℓ.side)).comp measurable_fst).prodMk
      ((measurable_fst.comp measurable_snd).prodMk (measurable_fst.comp (measurable_snd.comp measurable_snd)))
private theorem measurable_finalField (ℓ : StepParameters) : (s n : ℕ) → Measurable (finalField ℓ s n)
  | 0, _ => measurable_id
  | s + 1, n => by
    letI := chainSampleMeasurableSpace ℓ s (n * ℓ.side)
    exact measurable_snd.comp measurable_snd
private theorem measureReal_topField_mem_eq_integral (hTop : FinalFieldLawIsChainExpectation) (hfit : ℓ.Admissible)
    (hLam : 11 * 2 ^ 12 * ℓ.baseDepth < ℓ.side)
    (T : StageTower ℓ) (β : ℝ) (j n : ℕ) [NeZero n]
    (hmap : Measure.map (forgetMarks ℓ j n) (markedSampleLaw T β j n) =
      chainJointLaw ℓ β (fun i => (T.stage i).coupling) j n)
    (hprob : IsProbabilityMeasure (chainJointLaw ℓ β (fun i => (T.stage i).coupling) j n))
    {A : Set (TorusField n)} (hA : MeasurableSet A) :
    (markedSampleLaw T β j n).real {u | topField ℓ j n u ∈ A} =
      ∫ U, (chainExpectation ℓ (fun i => (T.stage i).coupling) j n (A.indicator 1) U).toReal
        ∂(wilsonLaw β (fineSide ℓ.side j n)) := by
  have hF : Measurable (A.indicator (1 : TorusField n → ENNReal)) := measurable_one.indicator hA
  have h1 : ∀ V, A.indicator (1 : TorusField n → ENNReal) V ≤ 1 := fun V => by
    by_cases h : V ∈ A <;> simp [h]
  obtain ⟨_, _, h3⟩ := hTop ℓ hfit hLam β (fun i => (T.stage i).coupling) j n _ hF h1
  rw [← h3]
  have hB : MeasurableSet (finalField ℓ j n ⁻¹' A) := measurable_finalField ℓ j n hA
  have e1 : {u | topField ℓ j n u ∈ A} = forgetMarks ℓ j n ⁻¹' (finalField ℓ j n ⁻¹' A) := by
    ext u
    simp [finalField_forgetMarks]
  have hm1 : (markedSampleLaw T β j n) {u | topField ℓ j n u ∈ A} =
      chainJointLaw ℓ β (fun i => (T.stage i).coupling) j n (finalField ℓ j n ⁻¹' A) := by
    rw [e1, ← hmap, Measure.map_apply (measurable_forgetMarks j n) hB]
  have e2 : (fun u => (A.indicator (1 : TorusField n → ENNReal) (finalField ℓ j n u)).toReal) =
      (finalField ℓ j n ⁻¹' A).indicator (fun _ => (1 : ℝ)) := by
    funext u
    by_cases h : finalField ℓ j n u ∈ A
    · simp [h]
    · simp [h]
  rw [e2, integral_indicator_const _ hB, Measure.real, hm1]
  simp [Measure.real]
end MarkedToChain
section Chessboard
private theorem plaquetteEnergy_congr {n : ℕ} {W W' : TorusField n} {x : TorusSite n} {μ ν : Fin 4}
    (h : ∀ z ∈ plaquetteVertices x μ ν, ∀ i, W z i = W' z i) :
    plaquetteEnergy W x μ ν = plaquetteEnergy W' x μ ν := by
  have h0 : ∀ i, W x i = W' x i := h x (by simp [plaquetteVertices])
  have h1 : ∀ i, W (x + unitStep n μ) i = W' (x + unitStep n μ) i := h _ (by simp [plaquetteVertices])
  have h2 : ∀ i, W (x + unitStep n ν) i = W' (x + unitStep n ν) i := h _ (by simp [plaquetteVertices])
  unfold plaquetteEnergy holonomy
  rw [h0 μ, h0 ν, h1 ν, h2 μ]
private theorem hotImage_dependsOnlyNear {n : ℕ} [NeZero n] (c M : ℕ) (x₀ : TorusSite n) {μ ν : Fin 4}
    (hμν : μ < ν) (t : ℝ) (k : Fin 4 → Fin M) :
    DependsOnlyNear (siteOfInt fun i => integerCoords x₀ i + c * ((k i : ℕ) : ℤ)) 2
      (({V | t < plaquetteEnergy V (plaquetteCellImage c M (x₀, μ, ν) k).1
        (plaquetteCellImage c M (x₀, μ, ν) k).2.1
        (plaquetteCellImage c M (x₀, μ, ν) k).2.2} : Set (TorusField n)).indicator
          (1 : TorusField n → ENNReal)) := by
  intro V V' h
  have he : plaquetteEnergy V (plaquetteCellImage c M (x₀, μ, ν) k).1 (plaquetteCellImage c M (x₀, μ, ν) k).2.1
      (plaquetteCellImage c M (x₀, μ, ν) k).2.2 = plaquetteEnergy V' (plaquetteCellImage c M (x₀, μ, ν) k).1
      (plaquetteCellImage c M (x₀, μ, ν) k).2.1 (plaquetteCellImage c M (x₀, μ, ν) k).2.2 := by
    refine plaquetteEnergy_congr fun z hz i => h z ?_ i
    obtain ⟨d, hd, rfl⟩ := reflectedPlaquette_vertex_near_centre c x₀ μ ν hμν _ hz
    have e : (siteOfInt fun i => integerCoords x₀ i + c * ((k i : ℕ) : ℤ) + d i : TorusSite n) =
        (siteOfInt fun i => integerCoords x₀ i + c * ((k i : ℕ) : ℤ)) + siteOfInt d := by
      funext i
      simp [siteOfInt]
    rw [e, supDist_comm]
    refine supDist_add_siteOfInt_le _ _ _ fun i => ?_
    have := abs_le.mp (hd i)
    omega
  simp only [Set.indicator, Set.mem_setOf_eq, he, Pi.one_apply]
private theorem plaquetteCellImage_zero {n : ℕ} [NeZero n] (c M : ℕ) (x₀ : TorusSite n) {μ ν : Fin 4}
    (hμν : μ < ν) (k₀ : Fin 4 → Fin M) (h0 : ∀ i, ((k₀ i : ℕ)) = 0) :
    plaquetteCellImage c M (x₀, μ, ν) k₀ = (x₀, μ, ν) := by
  unfold plaquetteCellImage
  simp only
  rw [cellReflection_mapPlaquette _ _ _ _ hμν]
  have hs : ∀ i, (cellReflection c (integerCoords x₀) fun i => ((k₀ i : ℕ) : ℤ)).axisSign i = 1 := fun i => by
    simp [cellReflection, h0 i]
  have hb : (cellReflection c (integerCoords x₀) fun i => ((k₀ i : ℕ) : ℤ)).imageCorner x₀ μ ν = x₀ := by
    unfold TorusIsometry.imageCorner
    rw [if_pos (hs _), if_pos (hs _), cellReflection_mapSite]
    funext i
    simp [siteOfInt, h0 i, integerCoords]
  rw [hb]
private theorem plaquetteChessboard_bound (hChess : ChessboardEstimate) (hTop : FinalFieldLawIsChainExpectation)
    (hCarry : ChainExpectationsTransported) (hSplit : ChainExpectationsFactorizeForSeparatedCells)
    (hTP : TwoPointByTotalCovarianceStatement) {Tb : ParameterAssignment} {y : ℝ} (hD : Tb.Admissible) (hy0 : 0 < y)
    (hfit : (Tb.stepParameters y).Admissible) (T : StageTower (Tb.stepParameters y)) (β : ℝ) (j M : ℕ)
    [NeZero (Tb.side * M)] (hS : IsTowerAtParameters Tb y T β j) (hC : T.MarksMeasurable) (hEven : Even M)
    (hMn : (Tb.stepParameters y).n₀ ≤ M) (x₀ : TorusSite (Tb.side * M)) (μ ν : Fin 4) (hμν : μ < ν) (t : ℝ) :
    ((markedSampleLaw T β j (Tb.side * M)).real
        {u | t < plaquetteEnergy (topField (Tb.stepParameters y) j (Tb.side * M) u) x₀ μ ν}) ^ (M ^ 4) ≤
      (markedSampleLaw T β j (Tb.side * M)).real {u | ∀ k : Fin 4 → Fin M,
        t < plaquetteEnergy (topField (Tb.stepParameters y) j (Tb.side * M) u)
          (plaquetteCellImage Tb.side M (x₀, μ, ν) k).1
          (plaquetteCellImage Tb.side M (x₀, μ, ν) k).2.1 (plaquetteCellImage Tb.side M (x₀, μ, ν) k).2.2} := by
  classical
  have hLam : 11 * 2 ^ 12 * (Tb.stepParameters y).baseDepth < (Tb.stepParameters y).side := hD.L_gt
  have hLbig : 2 ^ 40 ≤ Tb.side := hD.L_ge
  have hn₀ : 4096 ≤ Tb.n₀ := hD.n₀_ge
  have hMn' : Tb.n₀ ≤ M := hMn
  have hM0 : 0 < M := by omega
  have hn16 : 16 ≤ Tb.side * M := by nlinarith
  have hnn : (Tb.stepParameters y).n₀ ≤ Tb.side * M := hMn.trans (Nat.le_mul_of_pos_left _ (by omega))
  have hcut : ColdStepAtMirrorFrames.IsCutoff ((Tb.stepParameters y).threshold / 64) T.base.barrierFn := by
    have h0 : T.base.barrierFn = Tb.cutoff := (hS.onFamily 0 (Nat.zero_le _)).barrierFn_eq
    rw [h0]
    exact hD.cut
  obtain ⟨_, _, _, hmap, _, _⟩ := hTP (Tb.stepParameters y) hfit hLam T hcut hC β (fun _ => 0) j (Tb.side * M)
  have hprob : IsProbabilityMeasure
      (chainJointLaw (Tb.stepParameters y) β (fun i => (T.stage i).coupling) j (Tb.side * M)) := by
    rw [← hmap]
    exact Measure.isProbabilityMeasure_map (measurable_forgetMarks j _).aemeasurable
  set xs : ℕ → ℝ := fun i => (T.stage i).coupling with hxs
  set u : Fin 4 → ℤ := integerCoords x₀ with hu
  let Hk : (Fin 4 → Fin M) → Set (TorusField (Tb.side * M)) := fun k =>
    {V | t < plaquetteEnergy V (plaquetteCellImage Tb.side M (x₀, μ, ν) k).1
      (plaquetteCellImage Tb.side M (x₀, μ, ν) k).2.1 (plaquetteCellImage Tb.side M (x₀, μ, ν) k).2.2}
  let H₀ : Set (TorusField (Tb.side * M)) := {V | t < plaquetteEnergy V x₀ μ ν}
  have hHk : ∀ k, MeasurableSet (Hk k) := fun k =>
    measurableSet_lt measurable_const (continuous_plaquetteEnergy _ _ _).measurable
  have hH₀ : MeasurableSet H₀ := measurableSet_lt measurable_const (continuous_plaquetteEnergy _ _ _).measurable
  let F : (Fin 4 → Fin M) → TorusField (Tb.side * M) → ENNReal := fun k => (Hk k).indicator 1
  let F₀ : TorusField (Tb.side * M) → ENNReal := H₀.indicator 1
  have hFm : ∀ k, Measurable (F k) := fun k => measurable_one.indicator (hHk k)
  have hF₀m : Measurable F₀ := measurable_one.indicator hH₀
  have hF1 : ∀ k V, F k V ≤ 1 := fun k V => by
    by_cases h : V ∈ Hk k <;> simp [F, h]
  have hF₀1 : ∀ V, F₀ V ≤ 1 := fun V => by
    by_cases h : V ∈ H₀ <;> simp [F₀, h]
  obtain ⟨i1, i2⟩ := hSplit (Tb.stepParameters y) hfit hLam xs j (Tb.side * M) Tb.side M 2 rfl hn16
    (by have : (2 : ℕ) ^ 40 ≥ 13 := by norm_num
        omega) u F hFm fun k => hotImage_dependsOnlyNear Tb.side M x₀ hμν t k
  let k₀ : Fin 4 → Fin M := fun _ => ⟨0, hM0⟩
  have hk₀ : plaquetteCellImage Tb.side M (x₀, μ, ν) k₀ = (x₀, μ, ν) :=
    plaquetteCellImage_zero Tb.side M x₀ hμν k₀ fun _ => rfl
  have hF₀ : F₀ = F k₀ := by
    have : H₀ = Hk k₀ := by
      show {V | t < plaquetteEnergy V x₀ μ ν} = {V | t < plaquetteEnergy V
        (plaquetteCellImage Tb.side M (x₀, μ, ν) k₀).1 (plaquetteCellImage Tb.side M (x₀, μ, ν) k₀).2.1
        (plaquetteCellImage Tb.side M (x₀, μ, ν) k₀).2.2}
      rw [hk₀]
    show H₀.indicator 1 = (Hk k₀).indicator 1
    rw [this]
  have hP1 := measureReal_topField_mem_eq_integral hTop hfit hLam T β j (Tb.side * M) hmap hprob hH₀
  let HU : Set (TorusField (Tb.side * M)) := ⋂ k, Hk k
  have hHU : MeasurableSet HU := MeasurableSet.iInter hHk
  have hQ1 := measureReal_topField_mem_eq_integral hTop hfit hLam T β j (Tb.side * M) hmap hprob hHU
  have eset2 : {u | ∀ k : Fin 4 → Fin M,
      t < plaquetteEnergy (topField (Tb.stepParameters y) j (Tb.side * M) u)
        (plaquetteCellImage Tb.side M (x₀, μ, ν) k).1
        (plaquetteCellImage Tb.side M (x₀, μ, ν) k).2.1 (plaquetteCellImage Tb.side M (x₀, μ, ν) k).2.2} =
      {u | topField (Tb.stepParameters y) j (Tb.side * M) u ∈ HU} := by
    ext u
    simp only [Set.mem_setOf_eq, HU, Set.mem_iInter, Hk]
  have hind : HU.indicator (1 : TorusField (Tb.side * M) → ENNReal) = fun V => ∏ k, F k V := by
    funext V
    by_cases h : V ∈ HU
    · rw [Set.indicator_of_mem h]
      exact (Finset.prod_eq_one fun k _ => Set.indicator_of_mem (Set.mem_iInter.mp h k) _).symm
    · rw [Set.indicator_of_notMem h]
      obtain ⟨k, hk⟩ : ∃ k, V ∉ Hk k := by
        by_contra hcon
        push_neg at hcon
        exact h (Set.mem_iInter.mpr hcon)
      exact (Finset.prod_eq_zero (Finset.mem_univ k) (Set.indicator_of_notMem hk _)).symm
  rw [eset2, hQ1, hind]
  have hP2 : (markedSampleLaw T β j (Tb.side * M)).real
      {u | t < plaquetteEnergy (topField (Tb.stepParameters y) j (Tb.side * M) u) x₀ μ ν} = _ := hP1
  rw [hP2]
  obtain ⟨g1, g2, _⟩ := hTop (Tb.stepParameters y) hfit hLam β xs j (Tb.side * M) F₀ hF₀m hF₀1
  have hside : fineSide (Tb.stepParameters y).side j (Tb.side * M) = Tb.side ^ (j + 1) * M := by
    rw [fineSide_eq]
    show Tb.side * M * Tb.side ^ j = _
    ring
  have hβ : 0 < β := by
    have h1 : y ≤ (T.stage 0).coupling := (hS.onFamily 0 (Nat.zero_le _)).le_coupling
    have h2 : (T.stage 0).coupling = (couplingFlow (Tb.stepParameters y) β 0).1 := hS.coupling_eq 0 (by omega)
    have h3 : (couplingFlow (Tb.stepParameters y) β 0).1 = β := rfl
    linarith
  have hm4 : 4 ≤ fineSide (Tb.stepParameters y).side j (Tb.side * M) := by
    rw [hside]
    have h1 : 1 ≤ Tb.side ^ j := Nat.one_le_pow _ _ (by omega)
    have h2 : Tb.side ^ (j + 1) = Tb.side ^ j * Tb.side := pow_succ _ _
    have h3 : Tb.side ≤ Tb.side ^ (j + 1) := by
      rw [h2]
      exact Nat.le_mul_of_pos_left _ (by omega)
    nlinarith
  let G : TorusField (fineSide (Tb.stepParameters y).side j (Tb.side * M)) → ℝ :=
    fun U => (chainExpectation (Tb.stepParameters y) xs j (Tb.side * M) F₀ U).toReal
  let Hc : (Fin 4 → Fin M) → TorusField (fineSide (Tb.stepParameters y).side j (Tb.side * M)) → ℝ :=
    fun k U => (chainExpectation (Tb.stepParameters y) xs j (Tb.side * M) (F k) U).toReal
  have hreads : DependsOnlyOnBox (fun i => (Tb.side : ℤ) ^ j * u i) ((Tb.side ^ (j + 1) - 1) / 2) G := by
    intro W W' hag
    have hR := descendedRadius_add_five_le (L := Tb.side) (by omega) j 2
    have hbig : 16 * Tb.side ^ j ≤ Tb.side ^ (j + 1) := by
      rw [pow_succ, mul_comm]
      exact Nat.mul_le_mul_left _ (by omega)
    have hr := i2 k₀ W W' ?_
    · show (chainExpectation (Tb.stepParameters y) xs j (Tb.side * M) F₀ W).toReal =
        (chainExpectation (Tb.stepParameters y) xs j (Tb.side * M) F₀ W').toReal
      rw [hF₀, hr]
    · intro z hz i
      have ec : (siteOfInt fun i => ((Tb.stepParameters y).side : ℤ) ^ j * (u i + (Tb.side : ℤ) * ((k₀ i : ℕ) : ℤ)) :
          TorusSite (fineSide (Tb.stepParameters y).side j (Tb.side * M))) =
            siteOfInt fun i => (Tb.side : ℤ) ^ j * u i := by
        funext i
        simp [siteOfInt, k₀]
        rfl
      rw [ec] at hz
      rw [supDist_comm] at hz
      obtain ⟨e, he, hb⟩ := exists_offset_of_supDist (siteOfInt fun i => (Tb.side : ℤ) ^ j * u i :
        TorusSite (fineSide (Tb.stepParameters y).side j (Tb.side * M))) z
      have hbox : ∀ l, (e l).natAbs ≤ descendedRadius Tb.side j 2 := fun l => (hb l).trans hz
      have hgoal := hag (e, i) ⟨fun l => ?_, fun l => ?_⟩
      · have e2 : bondFrom (siteOfInt fun i => (Tb.side : ℤ) ^ j * u i :
            TorusSite (fineSide (Tb.stepParameters y).side j (Tb.side * M))) (e, i) = (z, i) := by
          simp only [bondFrom]
          rw [← he]
        rw [e2] at hgoal
        exact hgoal
      · have h1 := hbox l
        show |e l| ≤ _
        rw [Int.abs_eq_natAbs]
        have : (e l).natAbs ≤ (Tb.side ^ (j + 1) - 1) / 2 := by omega
        exact_mod_cast this
      · have h1 := hbox l
        have h2 : |((e + Pi.single i 1 : Fin 4 → ℤ)) l| ≤ (e l).natAbs + 1 := by
          by_cases hl : l = i
          · subst hl
            simp only [Pi.add_apply, Pi.single_eq_same]
            rw [Int.abs_eq_natAbs]
            omega
          · simp only [Pi.add_apply, Pi.single_eq_of_ne hl, add_zero]
            rw [Int.abs_eq_natAbs]
            omega
        refine h2.trans ?_
        have : (e l).natAbs + 1 ≤ (Tb.side ^ (j + 1) - 1) / 2 := by omega
        exact_mod_cast this
  have hcopy : IsCellCopy (Tb.side ^ (j + 1)) (fun i => (Tb.side : ℤ) ^ j * u i) G Hc := by
    intro k W W' hc
    set k' : Fin 4 → ℤ := fun i => ((k i : ℕ) : ℤ) with hk'
    have hg : (iteratedScaledLift (Tb.stepParameters y).side j (cellReflection Tb.side u k')).Transports W W' := by
      have e := iteratedScaledLift_cellReflection Tb.side j u k'
      show (iteratedScaledLift Tb.side j (cellReflection Tb.side u k')).Transports W W'
      rw [e]
      exact hc
    have hFF : ∀ V V', (cellReflection Tb.side u k').Transports V V' → F k V' = F₀ V := by
      intro V V' h
      have he := plaquetteEnergy_of_transports h x₀ μ ν
      have hp : plaquetteCellImage Tb.side M (x₀, μ, ν) k =
          ((cellReflection Tb.side u k').imageCorner x₀ μ ν, μ, ν) :=
        cellReflection_mapPlaquette _ _ _ _ hμν
      have he' : plaquetteEnergy V' (plaquetteCellImage Tb.side M (x₀, μ, ν) k).1
          (plaquetteCellImage Tb.side M (x₀, μ, ν) k).2.1
          (plaquetteCellImage Tb.side M (x₀, μ, ν) k).2.2 = plaquetteEnergy V x₀ μ ν := by
        rw [hp]
        exact he.symm
      simp only [F, F₀, Hk, H₀, Set.indicator, Set.mem_setOf_eq, Pi.one_apply, he']
    have hc' := hCarry (Tb.stepParameters y) hfit xs j (Tb.side * M) hnn (cellReflection Tb.side u k') F₀ (F k)
      hF₀m (hFm k) hFF W W' hg
    show (chainExpectation (Tb.stepParameters y) xs j (Tb.side * M) (F k) W').toReal =
      (chainExpectation (Tb.stepParameters y) xs j (Tb.side * M) F₀ W).toReal
    rw [hc']
  have hch := hChess (Tb.side ^ (j + 1)) M _ hside hD.L_odd.pow hEven hM0 hm4 β hβ
    (fun i => (Tb.side : ℤ) ^ j * u i) G Hc
    g1.ennreal_toReal (fun W => ENNReal.toReal_nonneg) (fun W => by
      have := ENNReal.toReal_mono ENNReal.one_ne_top (g2 W)
      simpa using this) hreads hcopy
  refine hch.trans (le_of_eq ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  show ∏ k, (chainExpectation (Tb.stepParameters y) xs j (Tb.side * M) (F k) U).toReal =
    (chainExpectation (Tb.stepParameters y) xs j (Tb.side * M) (fun V => ∏ k, F k V) U).toReal
  rw [i1 U, ENNReal.toReal_prod]
theorem plaquetteChessboard_holds (hChess : ChessboardEstimate)
    (hTop : FinalFieldLawIsChainExpectation) (hCarry : ChainExpectationsTransported)
    (hSplit : ChainExpectationsFactorizeForSeparatedCells) (hTP : TwoPointByTotalCovarianceStatement) :
    plaquetteChessboardStatement := by
  intro a ha
  refine ⟨0, fun _ => 1, fun _ => one_pos, ?_⟩
  intro L hodd hLe Tb hTa hTL hD hrt
  refine ⟨Tb.floorMin, fun y hy hR hW => ?_⟩
  have hfit := hD.fits y hy
  have hy1 : 1 ≤ Tb.floorMin := le_trans hD.yC_ge (le_max_left _ _)
  intro T β j M _ hS hC hEven hMn p hp t
  obtain ⟨x₀, μ, ν⟩ := p
  have hμν : μ < ν := by
    simp [plaquettesIn] at hp
    exact hp
  exact plaquetteChessboard_bound hChess hTop hCarry hSplit hTP hD (by linarith) hfit T β j M hS hC hEven hMn
    x₀ μ ν hμν t
end Chessboard
end YangMills.Construction.ResponseInTheExpansion
end
