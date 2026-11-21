import YangMills.Construction.ClusterExpansionOfAStep.BondInCoordinates
import YangMills.Construction.ClusterExpansionOfAStep.TreesOfABlock
import YangMills.Construction.ColdStepAtMirrorFrames.GapTermsOfTheExponentProof
import YangMills.Construction.ColdStepAtMirrorFrames.LeastActionIsGaugeInvariant
import YangMills.Construction.RunningCouplingSlope.CurvesOfFieldsAtOne
import YangMills.Construction.RunningCouplingSlope.LeastActionIsWellAtTheTop
import YangMills.Construction.RunningCouplingSlope.LeastPointNearAStrictMinimum
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology Quaternion
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open BlockAverages ColdStepAtMirrorFrames LumpContours
section Basics
variable {F : BlockFrame}
private theorem mem_innerBonds_finiteCells (hs : ∀ i, 2 ≤ F.extent i) (hL : Odd F.blockSide) {j : ℕ} (hj : j ≤ F.top)
    (b : F.Site j × Fin 4) : b ∈ innerBonds (finiteCells F) j := by
  unfold innerBonds
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
  exact ⟨(BlockLevels.mem_sitesOfCells_iff hj hL).2 (BlockOffsets.mem_finiteCells hs _),
    (BlockLevels.mem_sitesOfCells_iff hj hL).2 (BlockOffsets.mem_finiteCells hs _)⟩
private theorem mem_chordBonds_iff (hs : ∀ i, 2 ≤ F.extent i) (hL : Odd F.blockSide) (b : F.Site F.depth × Fin 4) :
    b ∈ chordBonds (finiteCells F) ↔ ¬ IsAxialTreeBond b := by
  unfold chordBonds
  simp only [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_innerBonds_finiteCells hs hL (by simp [BlockFrame.top]) b, h⟩⟩
abbrev _root_.YangMills.SharedProofs.p21924 := @mem_chordBonds_iff
variable {S : Finset F.Cell}
private theorem stepCoordinates_smul (τ : ℝ) (ξ : StepVariable S) (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (τ • ξ) x i = τ • stepCoordinates ξ x i := by
  unfold stepCoordinates
  split_ifs with h
  · exact map_smul BondCoordinates.toImaginaryCLM _ _
  · simp
abbrev _root_.YangMills.SharedProofs.p61127 := @stepCoordinates_smul
private theorem stepCoordinates_zero (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (0 : StepVariable S) x i = 0 := by
  have := stepCoordinates_smul (0 : ℝ) (0 : StepVariable S) x i
  simpa using this
abbrev _root_.YangMills.SharedProofs.p7539 := @stepCoordinates_zero
private def imaginaryCLM : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℍ[ℝ] :=
  imaginaryQuaternions.subtypeL.comp BondCoordinates.toImaginaryCLM
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
private theorem analyticAt_stepCoordinates {η : X → StepVariable S} {e : X} (h : AnalyticAt ℝ η e)
    (x : F.Site F.depth) (i : Fin 4) :
    AnalyticAt ℝ (fun y => ((stepCoordinates (η y) x i : imaginaryQuaternions) : ℍ[ℝ])) e := by
  unfold stepCoordinates
  by_cases hb : (x, i) ∈ chordBonds S
  · simp only [hb, dif_pos]
    have h1 : AnalyticAt ℝ (fun y => η y ⟨(x, i), hb⟩) e :=
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ↥(chordBonds S) => EuclideanSpace ℝ (Fin 3))
        ⟨(x, i), hb⟩).analyticAt _).comp h
    exact (imaginaryCLM.analyticAt _).comp h1
  · simp only [hb, dif_neg, not_false_eq_true]
    simpa using analyticAt_const
private theorem analyticAt_expUnit {w : X → imaginaryQuaternions} {e : X}
    (h : AnalyticAt ℝ (fun y => (w y : ℍ[ℝ])) e) :
    AnalyticAt ℝ (fun y => ((expUnit (w y) : UnitQuaternion) : ℍ[ℝ])) e :=
  AnalyticAt.comp (g := NormedSpace.exp) (f := fun y => (w y : ℍ[ℝ])) (NormedSpace.exp_analytic (𝕂 := ℝ) _) h
private theorem isAnalytic_chartedField {w : X → F.Site F.depth → Fin 4 → imaginaryQuaternions}
    {V : X → F.GaugeField F.top} {e : X}
    (hw : ∀ x i, AnalyticAt ℝ (fun y => (w y x i : ℍ[ℝ])) e) (hV : IsAnalyticFieldFamily V e) :
    IsAnalyticFieldFamily (fun y => chartedField (w y) (V y)) e := by
  intro x i
  by_cases h1 : IsCrossingBond (x, i)
  · simp only [chartedField, h1, if_true]
    exact (analyticAt_expUnit (hw x i)).mul (hV _ _)
  · by_cases h2 : IsAxialTreeBond (x, i)
    · simp only [chartedField, h1, h2, if_true, if_false]
      simpa using analyticAt_const
    · simp only [chartedField, h1, h2, if_false]
      exact analyticAt_expUnit (hw x i)
abbrev _root_.YangMills.SharedProofs.p38066 := @isAnalytic_chartedField
private theorem isAnalytic_fieldOfQuaternions {k : ℕ} {q : X → F.Site k → Fin 4 → ℍ[ℝ]} {e : X}
    (hq : ∀ x i, AnalyticAt ℝ (fun y => q y x i) e) (h0 : ∀ x i, q e x i ≠ 0) :
    IsAnalyticFieldFamily (fun y => fieldOfQuaternions (q y)) e :=
  fun x i => analyticAt_normalize (hq x i) (h0 x i)
theorem fieldOfQuaternions_trivial {k : ℕ} :
    fieldOfQuaternions (quaternionsOfField (trivialBlockField F k)) = trivialBlockField F k :=
  fieldOfQuaternions_quaternionsOfField _
private theorem chartedField_zero_trivial :
    chartedField (fun _ _ => 0) (trivialBlockField F F.top) = trivialBlockField F F.depth := by
  funext x i
  have h0 : expUnit (0 : imaginaryQuaternions) = 1 := by
    apply Subtype.ext
    simp [expUnit]
  unfold chartedField trivialBlockField
  split_ifs <;> simp [h0]
abbrev _root_.YangMills.DeltaSharedProofs.p501102 := @chartedField_zero_trivial
abbrev _root_.YangMills.SharedProofs.p20491 := @chartedField_zero_trivial
end Basics
section Energy
variable {F : BlockFrame} {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
private theorem analyticAt_action {k : ℕ} [Fintype (F.Site k)] {A : F.GaugeField k → ℝ}
    (hA : IsNondegenerateAtTrivial A) {φ : X → F.GaugeField k} {e : X} (h : IsAnalyticFieldFamily φ e)
    (h0 : φ e = trivialBlockField F k) : AnalyticAt ℝ (fun y => A (φ y)) e := by
  have hq : AnalyticAt ℝ (fun y => quaternionsOfField (φ y)) e :=
    AnalyticAt.pi fun x => AnalyticAt.pi fun i => h x i
  have hc : AnalyticAt ℝ (fun y => A (fieldOfQuaternions (quaternionsOfField (φ y)))) e :=
    AnalyticAt.comp (g := fun Y => A (fieldOfQuaternions Y)) (f := fun y => quaternionsOfField (φ y))
      (by rw [h0]; exact hA.analyticAt_trivial) hq
  simpa only [fieldOfQuaternions_quaternionsOfField] using hc
private theorem analyticAt_blockEnergy [Fintype (F.Site F.depth)] {a : ℝ} (hL : Odd F.blockSide)
    (hA : IsNondegenerateAtTrivial (F := F) (k := F.depth) (minimalAction a (finiteCells F) F.depth))
    {φ : X → F.GaugeField F.depth} {φ' : X → F.GaugeField F.top} {e : X} (h : IsAnalyticFieldFamily φ e)
    (h' : IsAnalyticFieldFamily φ' e) (h0 : φ e = trivialBlockField F F.depth) :
    AnalyticAt ℝ (fun y => blockEnergy a (finiteCells F) F.depth (φ y) (φ' y)) e := by
  unfold blockEnergy
  refine (analyticAt_action hA h h0).add
    (analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun c _ => h.analyticAt_blockFit h' c ?_))
  rw [h0, contourAverage_trivial hL]
  exact one_ne_zero
abbrev _root_.YangMills.SharedProofs.p73682 := @analyticAt_blockEnergy
private theorem secondDerivZero_eq_of_velocity {k : ℕ} [Fintype (F.Site k)] {A : F.GaugeField k → ℝ}
    (hA : IsNondegenerateAtTrivial A) {c c' : ℝ → F.GaugeField k} {β : F.Site k → Fin 4 → imaginaryQuaternions}
    (hc : IsCurveThroughTrivial c β) (hc' : IsCurveThroughTrivial c' β)
    (ha : IsAnalyticFieldFamily c 0) (ha' : IsAnalyticFieldFamily c' 0) :
    secondDerivZero (fun τ => A (c τ)) = secondDerivZero (fun τ => A (c' τ)) := by
  set g : (F.Site k → Fin 4 → ℍ[ℝ]) → ℝ := fun Y => A (fieldOfQuaternions Y) with hg
  have hmin : fderiv ℝ g (quaternionsOfField (trivialBlockField F k)) = 0 := by
    have h1 : g (quaternionsOfField (trivialBlockField F k)) = 0 := by
      simp only [hg, fieldOfQuaternions_quaternionsOfField, hA.trivial_eq_zero]
    have : IsLocalMin g (quaternionsOfField (trivialBlockField F k)) := by
      refine Eventually.of_forall fun Y => ?_
      rw [h1]
      exact hA.nonneg _
    exact this.fderiv_eq_zero
  have key : ∀ c : ℝ → F.GaugeField k, IsCurveThroughTrivial c β → IsAnalyticFieldFamily c 0 →
      secondDerivZero (fun τ => A (c τ)) = fderiv ℝ (fderiv ℝ g) (quaternionsOfField (trivialBlockField F k))
        (fun x i => (β x i : ℍ[ℝ])) (fun x i => (β x i : ℍ[ℝ])) := by
    intro c hc ha
    have hγ : AnalyticAt ℝ (fun τ => quaternionsOfField (c τ)) 0 :=
      AnalyticAt.pi fun x => AnalyticAt.pi fun i => ha x i
    have h0 : quaternionsOfField (c 0) = quaternionsOfField (trivialBlockField F k) := by rw [hc.at_zero]
    have h2 := secondDerivZero_comp hA.analyticAt_trivial hmin hγ h0
    have hd : deriv (fun τ => quaternionsOfField (c τ)) 0 = fun x i => (β x i : ℍ[ℝ]) := by
      apply HasDerivAt.deriv
      rw [hasDerivAt_pi]
      intro x
      rw [hasDerivAt_pi]
      intro i
      exact hc.hasDerivAt x i
    rw [hd] at h2
    simpa only [fieldOfQuaternions_quaternionsOfField] using h2
  rw [key c hc ha, key c' hc' ha']
private theorem hasDerivAt_expUnit_smul (w : imaginaryQuaternions) :
    HasDerivAt (fun τ : ℝ => ((expUnit (τ • w) : UnitQuaternion) : ℍ[ℝ])) (w : ℍ[ℝ]) 0 := by apply _root_.YangMills.Construction.GaugedCriticality.hasDerivAt_expUnit_smul <;> assumption
open Classical in
private def chartVelocity (ξ : StepVariable (finiteCells F)) (B : F.Site F.top → Fin 4 → imaginaryQuaternions) :
    F.Site F.depth → Fin 4 → imaginaryQuaternions :=
  fun x i => stepCoordinates ξ x i + if IsCrossingBond (x, i) then B (enclosingCell x) i else 0
private def chartLine (ξ : StepVariable (finiteCells F)) (B : F.Site F.top → Fin 4 → imaginaryQuaternions) (τ : ℝ) :
    F.GaugeField F.depth :=
  chartedField (stepCoordinates (τ • ξ)) (fieldAlongLine B τ)
private theorem isCurveThroughTrivial_chartLine (hs : ∀ i, 2 ≤ F.extent i) (hL : Odd F.blockSide)
    (ξ : StepVariable (finiteCells F)) (B : F.Site F.top → Fin 4 → imaginaryQuaternions) :
    IsCurveThroughTrivial (chartLine ξ B) (chartVelocity ξ B) where
  at_zero := by
    unfold chartLine
    have e1 : stepCoordinates ((0 : ℝ) • ξ) = fun (_ : F.Site F.depth) (_ : Fin 4) => (0 : imaginaryQuaternions) := by
      funext x i
      rw [stepCoordinates_smul]
      simp
    rw [e1, (isCurveThroughTrivial_fieldAlongLine B).at_zero]
    exact chartedField_zero_trivial
  hasDerivAt := by
    intro x i
    have he : (fun τ : ℝ => ((expUnit (stepCoordinates (τ • ξ) x i) : UnitQuaternion) : ℍ[ℝ])) =
        fun τ : ℝ => ((expUnit (τ • stepCoordinates ξ x i) : UnitQuaternion) : ℍ[ℝ]) := by
      funext τ
      rw [stepCoordinates_smul]
    unfold chartLine chartedField chartVelocity
    by_cases h1 : IsCrossingBond (x, i)
    · simp only [h1, if_true]
      have d := (hasDerivAt_expUnit_smul (stepCoordinates ξ x i)).fun_mul
        ((isCurveThroughTrivial_fieldAlongLine B).hasDerivAt (enclosingCell x) i)
      have e0 : ((fieldAlongLine B 0 (enclosingCell x) i : UnitQuaternion) : ℍ[ℝ]) = 1 := by
        rw [(isCurveThroughTrivial_fieldAlongLine B).at_zero]
        rfl
      have e1 : ((expUnit ((0 : ℝ) • stepCoordinates ξ x i) : UnitQuaternion) : ℍ[ℝ]) = 1 := by
        simp [expUnit]
      simp only [e0, e1, mul_one, one_mul] at d
      have hg : (fun τ : ℝ => ((expUnit (stepCoordinates (τ • ξ) x i) * fieldAlongLine B τ (enclosingCell x) i :
            UnitQuaternion) : ℍ[ℝ])) =
          fun τ : ℝ => ((expUnit (τ • stepCoordinates ξ x i) : UnitQuaternion) : ℍ[ℝ]) *
            ((fieldAlongLine B τ (enclosingCell x) i : UnitQuaternion) : ℍ[ℝ]) := by
        funext τ
        rw [stepCoordinates_smul]
        rfl
      rw [hg]
      simpa using d
    · by_cases h2 : IsAxialTreeBond (x, i)
      · have hz : stepCoordinates ξ x i = 0 := by
          unfold stepCoordinates
          rw [dif_neg]
          intro hb
          exact (mem_chordBonds_iff hs hL _).1 hb h2
        simp only [h1, h2, if_true, if_false, hz]
        simpa using hasDerivAt_const (0 : ℝ) (1 : ℍ[ℝ])
      · simp only [h1, h2, if_false, add_zero]
        rw [he]
        exact hasDerivAt_expUnit_smul _
private theorem isAnalytic_fieldAlongLine {k : ℕ} (B : F.Site k → Fin 4 → imaginaryQuaternions) :
    IsAnalyticFieldFamily (fieldAlongLine (F := F) B) 0 := by
  refine isAnalytic_fieldOfQuaternions (q := fun τ x i => 1 + τ • (B x i : ℍ[ℝ])) (fun x i => ?_) (fun x i => ?_)
  · exact analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  · simp
private theorem isAnalytic_chartLine (ξ : StepVariable (finiteCells F))
    (B : F.Site F.top → Fin 4 → imaginaryQuaternions) :
    IsAnalyticFieldFamily (chartLine ξ B) 0 := by
  have hη : AnalyticAt ℝ (fun τ : ℝ => τ • ξ) 0 := analyticAt_id.smul analyticAt_const
  exact isAnalytic_chartedField (fun x i => analyticAt_stepCoordinates hη x i) (isAnalytic_fieldAlongLine B)
private theorem im_coe_imaginary (b : imaginaryQuaternions) : (b : ℍ[ℝ]).im = (b : ℍ[ℝ]) := by
  have h : (b : ℍ[ℝ]).re = 0 := b.2
  ext <;> simp [h]
private theorem blockFit_trivial (hL : Odd F.blockSide) (c : F.Site F.top × Fin 4) :
    blockFit (trivialBlockField F F.depth) (trivialBlockField F F.top) c = 0 := by
  rw [blockFit_eq_reDefect, contourAverage_trivial hL]
  simp [reDefect, trivialBlockField]
private theorem exists_potential_of_secondDerivZero_eq_zero [Fintype (F.Site F.depth)] {a : ℝ} (ha : 0 < a)
    (hs : ∀ i, 2 ≤ F.extent i) (hL : Odd F.blockSide)
    (hA : IsNondegenerateAtTrivial (F := F) (k := F.depth) (minimalAction a (finiteCells F) F.depth))
    (ξ : StepVariable (finiteCells F)) (B : F.Site F.top → Fin 4 → imaginaryQuaternions)
    (h : secondDerivZero (fun τ => blockEnergy a (finiteCells F) F.depth (chartLine ξ B τ) (fieldAlongLine B τ)) = 0) :
    ∃ l : (Fin 4 → ℤ) → imaginaryQuaternions,
      (∀ z i, chartVelocity ξ B (siteOfCoords F.depth z) i = l z - l (z + Pi.single i 1)) ∧
      ∀ y i, B (siteOfCoords F.top y) i =
        l (blockCoords F.blockSide y) - l (blockCoords F.blockSide (y + Pi.single i 1)) := by
  have hcu := isCurveThroughTrivial_chartLine hs hL ξ B
  have hli := isCurveThroughTrivial_fieldAlongLine (F := F) (k := F.top) B
  have hac := isAnalytic_chartLine ξ B
  have hal := isAnalytic_fieldAlongLine (F := F) (k := F.top) B
  have a0 : AnalyticAt ℝ (fun τ => minimalAction a (finiteCells F) F.depth (chartLine ξ B τ)) 0 :=
    analyticAt_action hA hac hcu.at_zero
  have ac : ∀ c ∈ innerBonds (finiteCells F) (F.depth + 1),
      AnalyticAt ℝ (fun τ => blockFit (chartLine ξ B τ) (fieldAlongLine B τ) c) 0 := by
    intro c _
    refine hac.analyticAt_blockFit hal c ?_
    rw [hcu.at_zero, contourAverage_trivial hL]
    exact one_ne_zero
  have hfit0 : ∀ c, 0 ≤ secondDerivZero (fun τ => blockFit (chartLine ξ B τ) (fieldAlongLine B τ) c) ∨
      c ∉ innerBonds (finiteCells F) (F.depth + 1) := by
    intro c
    by_cases hc : c ∈ innerBonds (finiteCells F) (F.depth + 1)
    · left
      refine secondDerivZero_nonneg (ac c hc) (Eventually.of_forall fun τ => ?_) ?_
      · rw [blockFit_eq_reDefect]
        exact reDefect_nonneg _
      · rw [hcu.at_zero, hli.at_zero]
        exact blockFit_trivial hL c
    · exact Or.inr hc
  have hsum : secondDerivZero (fun τ => blockEnergy a (finiteCells F) F.depth (chartLine ξ B τ) (fieldAlongLine B τ)) =
      secondDerivZero (fun τ => minimalAction a (finiteCells F) F.depth (chartLine ξ B τ)) +
        a * ∑ c ∈ innerBonds (finiteCells F) (F.depth + 1),
          secondDerivZero (fun τ => blockFit (chartLine ξ B τ) (fieldAlongLine B τ) c) := by
    have aSum : AnalyticAt ℝ (fun τ => ∑ c ∈ innerBonds (finiteCells F) (F.depth + 1),
        blockFit (chartLine ξ B τ) (fieldAlongLine B τ) c) 0 :=
      Finset.analyticAt_fun_sum _ ac
    have aS : AnalyticAt ℝ (fun τ => a * ∑ c ∈ innerBonds (finiteCells F) (F.depth + 1),
        blockFit (chartLine ξ B τ) (fieldAlongLine B τ) c) 0 :=
      analyticAt_const.mul aSum
    have h1 := secondDerivZero_add a0 aS
    have h2 := secondDerivZero_const_mul a aSum
    have h3 := secondDerivZero_sum _ _ ac
    exact h1.trans (congrArg _ (h2.trans (congrArg _ h3)))
  have n0 : 0 ≤ secondDerivZero (fun τ => minimalAction a (finiteCells F) F.depth (chartLine ξ B τ)) := by
    refine secondDerivZero_nonneg a0 (Eventually.of_forall fun τ => hA.nonneg _) ?_
    rw [hcu.at_zero]
    exact hA.trivial_eq_zero
  have ns : 0 ≤ ∑ c ∈ innerBonds (finiteCells F) (F.depth + 1),
      secondDerivZero (fun τ => blockFit (chartLine ξ B τ) (fieldAlongLine B τ) c) :=
    Finset.sum_nonneg fun c hc => (hfit0 c).resolve_right (not_not.2 hc)
  rw [hsum] at h
  have ns' := mul_nonneg ha.le ns
  have e0 : secondDerivZero (fun τ => minimalAction a (finiteCells F) F.depth (chartLine ξ B τ)) = 0 := by linarith
  have es : ∑ c ∈ innerBonds (finiteCells F) (F.depth + 1),
      secondDerivZero (fun τ => blockFit (chartLine ξ B τ) (fieldAlongLine B τ) c) = 0 := by
    have : a * ∑ c ∈ innerBonds (finiteCells F) (F.depth + 1),
        secondDerivZero (fun τ => blockFit (chartLine ξ B τ) (fieldAlongLine B τ) c) = 0 := by
      linarith
    exact (mul_eq_zero.1 this).resolve_left ha.ne'
  have ec := (Finset.sum_eq_zero_iff_of_nonneg fun c hc => (hfit0 c).resolve_right (not_not.2 hc)).1 es
  have hform : secondDerivZero
      (fun τ => minimalAction a (finiteCells F) F.depth (fieldAlongLine (chartVelocity ξ B) τ)) = 0 := by
    rw [← secondDerivZero_eq_of_velocity hA hcu (isCurveThroughTrivial_fieldAlongLine _) hac
      (isAnalytic_fieldAlongLine _), e0]
  obtain ⟨l, hl⟩ := hA.isExactForm_of_deriv _ hform
  refine ⟨l, hl, fun y i => ?_⟩
  have hn : F.depth < F.top := by simp [BlockFrame.top]
  have hM := hcu.hasDerivAt_contourAverage_of_exact hn hL hl y i
  set c : F.Site (F.depth + 1) × Fin 4 := (siteOfCoords (F.depth + 1) y, i) with hcdef
  have hV : HasDerivAt (fun τ => (((fieldAlongLine B τ c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]))
      ((-(B c.1 c.2) : imaginaryQuaternions) : ℍ[ℝ]) 0 := by
    have h1 := quatStarCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hli.hasDerivAt c.1 c.2)
    have e : quatStarCLM ((B c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]) =
        ((- B c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]) := by
      simp [star_coe_imaginary]
    rw [e] at h1
    exact h1
  have hZ := hM.fun_mul hV
  have z0 : contourAverage (chartLine ξ B 0) c = 1 := by
    rw [hcu.at_zero, contourAverage_trivial hL]
  have z1 : (((fieldAlongLine B 0 c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := by
    rw [hli.at_zero]
    simp [trivialBlockField]
  rw [z0, z1, mul_one, one_mul] at hZ
  have hZ1 : (fun τ => contourAverage (chartLine ξ B τ) c *
      (((fieldAlongLine B τ c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])) 0 = 1 := by
    simp only [z0, z1, mul_one]
  have hval := secondDerivZero_reDefect hZ hZ1 (by
    have := ac c (mem_innerBonds_finiteCells hs hL le_rfl c)
    simpa only [blockFit_eq_reDefect] using this)
  have hz := ec c (mem_innerBonds_finiteCells hs hL le_rfl c)
  simp only [blockFit_eq_reDefect] at hz
  rw [hz] at hval
  have hd : ((l (blockCoords F.blockSide y) - l (blockCoords F.blockSide (y + Pi.single i 1)) :
        imaginaryQuaternions) : ℍ[ℝ]) + ((- B c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]) =
      ((l (blockCoords F.blockSide y) - l (blockCoords F.blockSide (y + Pi.single i 1)) - B c.1 c.2 :
        imaginaryQuaternions) : ℍ[ℝ]) := by
    simp [sub_eq_add_neg]
  rw [hd, im_coe_imaginary] at hval
  have h3 : ‖((l (blockCoords F.blockSide y) - l (blockCoords F.blockSide (y + Pi.single i 1)) - B c.1 c.2 :
      imaginaryQuaternions) : ℍ[ℝ])‖ = 0 := by
    have := hval.symm
    simpa using this
  have h4 : l (blockCoords F.blockSide y) - l (blockCoords F.blockSide (y + Pi.single i 1)) - B c.1 c.2 = 0 := by
    apply Subtype.ext
    simpa using h3
  exact (sub_eq_zero.1 h4).symm
end Energy
section Main
variable {F : BlockFrame}
private theorem norm_toImaginary (v : EuclideanSpace ℝ (Fin 3)) :
    ‖((toImaginary v : imaginaryQuaternions) : ℍ[ℝ])‖ = ‖v‖ := by apply _root_.YangMills.Construction.BlockTrees.norm_toImaginary <;> assumption
private def imaginaryCoords (w : imaginaryQuaternions) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![(w : ℍ[ℝ]).imI, (w : ℍ[ℝ]).imJ, (w : ℍ[ℝ]).imK]
private theorem toImaginary_imaginaryCoords (w : imaginaryQuaternions) : toImaginary (imaginaryCoords w) = w := by
  have h : (w : ℍ[ℝ]).re = 0 := w.2
  apply Subtype.ext
  ext <;> simp [toImaginary, imaginaryCoords, h]
private theorem eq_one_of_reDefect_eq_zero {g : UnitQuaternion} (h : reDefect (g : ℍ[ℝ]) = 0) : g = 1 := by
  have h1 := GaugeFixing.norm_coe_sub_one_sq g
  rw [← one_sub_re_eq_reDefect] at h
  have h2 : ‖(g : ℍ[ℝ]) - 1‖ ^ 2 = 0 := by rw [h1]; linarith
  apply Subtype.ext
  have h3 : (g : ℍ[ℝ]) - 1 = 0 := by simpa using h2
  simpa [sub_eq_zero] using h3
abbrev _root_.YangMills.SharedProofs.p24246 := @eq_one_of_reDefect_eq_zero
private theorem blockEnergy_eq_zero_parts [Fintype (F.Site F.depth)] {a : ℝ} (ha : 0 < a)
    (hA : IsNondegenerateAtTrivial (F := F) (k := F.depth) (minimalAction a (finiteCells F) F.depth))
    {W : F.GaugeField F.depth} {V : F.GaugeField F.top} (h : blockEnergy a (finiteCells F) F.depth W V = 0) :
    minimalAction a (finiteCells F) F.depth W = 0 ∧
      ∀ c ∈ innerBonds (finiteCells F) (F.depth + 1), blockFit W V c = 0 := by
  unfold blockEnergy at h
  have hn : ∀ c ∈ innerBonds (finiteCells F) (F.depth + 1), 0 ≤ blockFit W V c := fun c _ => by
    rw [blockFit_eq_reDefect]
    exact reDefect_nonneg _
  have h0 := hA.nonneg W
  have hs := Finset.sum_nonneg hn
  have hs' := mul_nonneg ha.le hs
  refine ⟨by linarith, ?_⟩
  have : ∑ c ∈ innerBonds (finiteCells F) (F.depth + 1), blockFit W V c = 0 := by
    have : a * ∑ c ∈ innerBonds (finiteCells F) (F.depth + 1), blockFit W V c = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left ha.ne'
  exact (Finset.sum_eq_zero_iff_of_nonneg hn).1 this
private theorem blockEnergy_nonneg [Fintype (F.Site F.depth)] {a : ℝ} (ha : 0 < a)
    (hA : IsNondegenerateAtTrivial (F := F) (k := F.depth) (minimalAction a (finiteCells F) F.depth))
    (W : F.GaugeField F.depth) (V : F.GaugeField F.top) :
    0 ≤ blockEnergy a (finiteCells F) F.depth W V := by
  unfold blockEnergy
  have hn : ∀ c ∈ innerBonds (finiteCells F) (F.depth + 1), 0 ≤ blockFit W V c := fun c _ => by
    rw [blockFit_eq_reDefect]
    exact reDefect_nonneg _
  have := mul_nonneg ha.le (Finset.sum_nonneg hn)
  have := hA.nonneg W
  linarith
private theorem blockEnergy_trivial [Fintype (F.Site F.depth)] {a : ℝ} (hL : Odd F.blockSide)
    (hA : IsNondegenerateAtTrivial (F := F) (k := F.depth) (minimalAction a (finiteCells F) F.depth)) :
    blockEnergy a (finiteCells F) F.depth (trivialBlockField F F.depth) (trivialBlockField F F.top) = 0 := by
  unfold blockEnergy
  rw [hA.trivial_eq_zero, Finset.sum_eq_zero fun c _ => blockFit_trivial hL c]
  simp
private theorem top_eq_of_pure (hL : Odd F.blockSide) {W : F.GaugeField F.depth} {V : F.GaugeField F.top}
    {g : (Fin 4 → ℤ) → UnitQuaternion}
    (hg : ∀ z i, W (siteOfCoords F.depth z) i = g z * (g (z + Pi.single i 1))⁻¹) (y : Fin 4 → ℤ) (i : Fin 4)
    (h : blockFit W V (siteOfCoords (F.depth + 1) y, i) = 0) :
    V (siteOfCoords F.top y) i =
      g (blockCoords F.blockSide y) * (g (blockCoords F.blockSide (y + Pi.single i 1)))⁻¹ := by
  rw [blockFit_eq_reDefect, contourAverage_of_pure (by simp [BlockFrame.top]) hL hg] at h
  have h1 := eq_one_of_reDefect_eq_zero (g := g (blockCoords F.blockSide y) *
    (g (blockCoords F.blockSide (y + Pi.single i 1)))⁻¹ * (V (siteOfCoords F.top y) i)⁻¹) h
  exact (mul_inv_eq_one.1 h1).symm
private theorem eq_trivial_of_blockEnergy_eq_zero [Fintype (F.Site F.depth)] {a : ℝ} (ha : 0 < a)
    (hs : ∀ i, 2 ≤ F.extent i) (hL : Odd F.blockSide)
    (hA : IsNondegenerateAtTrivial (F := F) (k := F.depth) (minimalAction a (finiteCells F) F.depth))
    {W : F.GaugeField F.depth}
    (hz : blockEnergy a (finiteCells F) F.depth W (trivialBlockField F F.top) = 0)
    (htree : ∀ b, IsAxialTreeBond b → W b.1 b.2 = 1) : W = trivialBlockField F F.depth := by
  obtain ⟨h0, hf⟩ := blockEnergy_eq_zero_parts ha hA hz
  obtain ⟨g, hg⟩ := hA.isPureGauge_of_eq_zero W h0
  have hs' : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  have hc := apply_eq_apply_zero_of_tree_and_block_moves hs' hL g (fun z i hb => by
      have h1 := htree _ hb
      simp only [hg] at h1
      exact mul_inv_eq_one.1 h1)
    (fun y i => by
      have h1 := top_eq_of_pure hL hg y i (hf _ (mem_innerBonds_finiteCells hs hL le_rfl _))
      exact mul_inv_eq_one.1 h1.symm)
  funext x i
  have e : W (siteOfCoords F.depth (siteCoords x)) i = 1 := by
    rw [hg, hc (siteCoords x), hc (siteCoords x + Pi.single i 1)]
    simp
  rw [siteOfCoords_siteCoords] at e
  exact e
private theorem continuous_blockEnergy [Fintype (F.Site F.depth)] {a : ℝ}
    (hA : IsNondegenerateAtTrivial (F := F) (k := F.depth) (minimalAction a (finiteCells F) F.depth)) :
    Continuous fun p : F.GaugeField F.depth × F.GaugeField F.top => blockEnergy a (finiteCells F) F.depth p.1 p.2 := by
  unfold blockEnergy
  exact (hA.continuous.comp continuous_fst).add (continuous_const.mul
    (continuous_finsetSum _ fun c _ => continuous_blockFit continuous_fst continuous_snd c))
private theorem minimisers_eventually_mem [Fintype (F.Site F.depth)] {a : ℝ} (ha : 0 < a) (hs : ∀ i, 2 ≤ F.extent i)
    (hL : Odd F.blockSide)
    (hA : IsNondegenerateAtTrivial (F := F) (k := F.depth) (minimalAction a (finiteCells F) F.depth))
    {U : Set (F.GaugeField F.depth)} (hU : U ∈ 𝓝 (trivialBlockField F F.depth)) :
    ∀ᶠ V in 𝓝 (trivialBlockField F F.top), ∀ W : F.GaugeField F.depth, (∀ b, IsAxialTreeBond b → W b.1 b.2 = 1) →
      (∀ W', blockEnergy a (finiteCells F) F.depth W V ≤ blockEnergy a (finiteCells F) F.depth W' V) → W ∈ U := by
  have hcont := continuous_blockEnergy (a := a) hA
  set T : Set (F.GaugeField F.depth) := {W | ∀ b, IsAxialTreeBond b → W b.1 b.2 = 1} with hT
  have hTc : IsClosed T := by
    simp only [hT, Set.ofPred_forall]
    exact isClosed_iInter fun b => isClosed_iInter fun _ =>
      isClosed_eq ((continuous_apply b.2).comp (continuous_apply b.1)) continuous_const
  set K : Set (F.GaugeField F.depth) := T ∩ (interior U)ᶜ with hKd
  have hK : IsCompact K := (hTc.inter isOpen_interior.isClosed_compl).isCompact
  have hpos : ∀ W ∈ K, 0 < blockEnergy a (finiteCells F) F.depth W (trivialBlockField F F.top) := by
    intro W hW
    refine (blockEnergy_nonneg ha hA W _).lt_of_ne' fun h0 => ?_
    have h1 := eq_trivial_of_blockEnergy_eq_zero ha hs hL hA h0 hW.1
    exact hW.2 (h1 ▸ mem_interior_iff_mem_nhds.2 hU)
  have hsub : ∀ W ∈ T, W ∉ K → W ∈ U := fun W hW hK' => by
    by_contra hn
    exact hK' ⟨hW, fun hi => hn (interior_subset hi)⟩
  rcases K.eq_empty_or_nonempty with he | hne
  · refine Eventually.of_forall fun V W hW _ => hsub W hW (by simp [he])
  obtain ⟨W₀, hW₀, hmin⟩ := hK.exists_isMinOn hne
    (hcont.comp (continuous_id.prodMk continuous_const)).continuousOn
  set m := blockEnergy a (finiteCells F) F.depth W₀ (trivialBlockField F F.top) with hm
  have hm0 : 0 < m := hpos W₀ hW₀
  have e1 : ∀ᶠ V in 𝓝 (trivialBlockField F F.top), ∀ W ∈ K,
      m / 2 < blockEnergy a (finiteCells F) F.depth W V := by
    refine hK.eventually_forall_of_forall_eventually
      (P := fun V W => m / 2 < blockEnergy a (finiteCells F) F.depth W V) fun W hW => ?_
    have hc : ContinuousAt (fun z : F.GaugeField F.top × F.GaugeField F.depth =>
        blockEnergy a (finiteCells F) F.depth z.2 z.1) (trivialBlockField F F.top, W) :=
      (hcont.comp continuous_swap).continuousAt
    have hv : m / 2 < blockEnergy a (finiteCells F) F.depth W (trivialBlockField F F.top) := by
      have : m ≤ blockEnergy a (finiteCells F) F.depth W (trivialBlockField F F.top) := hmin hW
      linarith
    exact hc.eventually (lt_mem_nhds hv)
  have e2 : ∀ᶠ V in 𝓝 (trivialBlockField F F.top),
      blockEnergy a (finiteCells F) F.depth (trivialBlockField F F.depth) V < m / 2 := by
    have hc : ContinuousAt (fun V : F.GaugeField F.top =>
        blockEnergy a (finiteCells F) F.depth (trivialBlockField F F.depth) V) (trivialBlockField F F.top) :=
      (hcont.comp (continuous_const.prodMk continuous_id)).continuousAt
    have hv : blockEnergy a (finiteCells F) F.depth (trivialBlockField F F.depth) (trivialBlockField F F.top) < m / 2 := by
      rw [blockEnergy_trivial hL hA]
      linarith
    exact hc.eventually (gt_mem_nhds hv)
  filter_upwards [e1, e2] with V h1 h2 W hW hmn
  refine hsub W hW fun hWK => ?_
  have := h1 W hWK
  have := hmn (trivialBlockField F F.depth)
  linarith
open Classical in
private def coordsOver (W : F.GaugeField F.depth) (V : F.GaugeField F.top) (b : F.Site F.depth × Fin 4) :
    imaginaryQuaternions :=
  if IsCrossingBond b then minimalLog (W b.1 b.2 * (V (enclosingCell b.1) b.2)⁻¹) else minimalLog (W b.1 b.2)
private theorem exists_chartedField (hs : ∀ i, 2 ≤ F.extent i) (hL : Odd F.blockSide) {r : ℝ} (hr : 0 < r)
    {W : F.GaugeField F.depth} {V : F.GaugeField F.top}
    (htree : ∀ b, IsAxialTreeBond b → W b.1 b.2 = 1)
    (hW : ∀ x i, ‖((W x i : UnitQuaternion) : ℍ[ℝ]) - 1‖ < r / 4)
    (hV : ∀ x i, ‖((V x i : UnitQuaternion) : ℍ[ℝ]) - 1‖ < r / 4) :
    ∃ η : StepVariable (finiteCells F), ‖η‖ < r ∧ chartedField (stepCoordinates η) V = W := by
  set η : StepVariable (finiteCells F) := fun b => imaginaryCoords (coordsOver W V b.1) with hη
  have hco : ∀ x i, ¬ IsAxialTreeBond (x, i) → stepCoordinates η x i = coordsOver W V (x, i) := by
    intro x i hb
    unfold stepCoordinates
    rw [dif_pos ((mem_chordBonds_iff hs hL _).2 hb)]
    exact toImaginary_imaginaryCoords _
  refine ⟨η, (pi_norm_lt_iff hr).2 fun b => ?_, ?_⟩
  · rw [← norm_toImaginary, hη]
    simp only [toImaginary_imaginaryCoords]
    unfold coordsOver
    split_ifs with h1
    · refine (GaugeFixing.norm_minimalLog_le _).trans_lt ?_
      rw [GaugeFixing.norm_mul_inv_sub_one]
      have e : ((W b.1.1 b.1.2 : UnitQuaternion) : ℍ[ℝ]) - (V (enclosingCell b.1.1) b.1.2 : UnitQuaternion) =
          (((W b.1.1 b.1.2 : UnitQuaternion) : ℍ[ℝ]) - 1) -
            (((V (enclosingCell b.1.1) b.1.2 : UnitQuaternion) : ℍ[ℝ]) - 1) := by abel
      rw [e]
      have := norm_sub_le (((W b.1.1 b.1.2 : UnitQuaternion) : ℍ[ℝ]) - 1)
        (((V (enclosingCell b.1.1) b.1.2 : UnitQuaternion) : ℍ[ℝ]) - 1)
      have := hW b.1.1 b.1.2
      have := hV (enclosingCell b.1.1) b.1.2
      linarith
    · refine (GaugeFixing.norm_minimalLog_le _).trans_lt ?_
      have := hW b.1.1 b.1.2
      linarith
  · funext x i
    unfold chartedField
    split_ifs with h1 h2
    · have hb : ¬ IsAxialTreeBond (x, i) := fun h => h.1 h1
      rw [hco x i hb]
      unfold coordsOver
      simp only [h1, if_true, GaugeFixing.expUnit_minimalLog, inv_mul_cancel_right]
    · exact (htree _ h2).symm
    · rw [hco x i h2]
      unfold coordsOver
      simp only [h1, if_false, GaugeFixing.expUnit_minimalLog]
private theorem blockEnergy_gaugeTransform [Fintype (F.Site F.depth)] {a : ℝ} (hL : Odd F.blockSide)
    (hinv : MinimalActionGaugeInvariant) (hcov : gaugeCovarianceStatement) (γ : F.Site F.depth → UnitQuaternion)
    (hγ : ∀ z, γ (cellCentre F.depth z) = 1) (W : F.GaugeField F.depth) (V : F.GaugeField F.top) :
    blockEnergy a (finiteCells F) F.depth (gaugeTransform γ W) V = blockEnergy a (finiteCells F) F.depth W V := by
  have hLp : 0 < F.blockSide := hL.pos
  have hn : F.depth < F.top := by simp [BlockFrame.top]
  unfold blockEnergy
  rw [hinv F a _ F.depth hn.le hLp γ W]
  congr 2
  refine Finset.sum_congr rfl fun c _ => ?_
  have h := (hcov F F.depth hn hLp).2.2.2 γ (fun _ => 1) W V c
    (by rw [GaugeFixing.refineSite_eq_cellCentre, hγ]) (by rw [GaugeFixing.refineSite_eq_cellCentre, hγ])
  have e : gaugeTransform (fun _ => (1 : UnitQuaternion)) V = V := by
    funext x i
    simp [gaugeTransform]
  rwa [e] at h
private def quaternionLine {k : ℕ} (B : F.Site k → Fin 4 → imaginaryQuaternions) (τ : ℝ) :
    F.Site k → Fin 4 → ℍ[ℝ] :=
  fun x i => 1 + τ • (B x i : ℍ[ℝ])
private theorem analyticAt_component {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {k : ℕ}
    [Fintype (F.Site k)] {q : X → F.Site k → Fin 4 → ℍ[ℝ]} {e : X} (h : AnalyticAt ℝ q e) (x : F.Site k) (i : Fin 4) :
    AnalyticAt ℝ (fun y => q y x i) e :=
  analyticAt_pi_iff.1 (analyticAt_pi_iff.1 h x) i
private theorem eventually_near_one {k : ℕ} [Fintype (F.Site k)] {r : ℝ} (hr : 0 < r) :
    ∀ᶠ W in 𝓝 (trivialBlockField F k), ∀ x i, ‖((W x i : UnitQuaternion) : ℍ[ℝ]) - 1‖ < r := by
  refine eventually_all.2 fun x => eventually_all.2 fun i => ?_
  have hc : Continuous fun W : F.GaugeField k => ‖((W x i : UnitQuaternion) : ℍ[ℝ]) - 1‖ :=
    ((continuous_subtype_val.comp ((continuous_apply i).comp (continuous_apply x))).sub continuous_const).norm
  have h0 : ‖((trivialBlockField F k x i : UnitQuaternion) : ℍ[ℝ]) - 1‖ < r := by
    simpa [trivialBlockField] using hr
  exact hc.continuousAt.eventually (gt_mem_nhds h0)
private theorem tendsto_fieldOfQuaternions {k : ℕ} [Fintype (F.Site k)] :
    Tendsto (fieldOfQuaternions (F := F) (k := k)) (𝓝 (quaternionsOfField (trivialBlockField F k)))
      (𝓝 (trivialBlockField F k)) := by
  have hc : ContinuousAt (fieldOfQuaternions (F := F) (k := k)) (quaternionsOfField (trivialBlockField F k)) := by
    refine continuousAt_pi.2 fun x => continuousAt_pi.2 fun i => ?_
    refine (Topology.IsInducing.subtypeVal.continuousAt_iff).2 ?_
    have : AnalyticAt ℝ (fun Y : F.Site k → Fin 4 → ℍ[ℝ] => ((normalize (Y x i) : UnitQuaternion) : ℍ[ℝ]))
        (quaternionsOfField (trivialBlockField F k)) :=
      analyticAt_normalize (analyticAt_component analyticAt_id x i) (by simp [quaternionsOfField, trivialBlockField])
    exact this.continuousAt
  have := hc.tendsto
  rwa [fieldOfQuaternions_trivial] at this
private def chartEnergyIn (a : ℝ) (F : BlockFrame)
    (p : StepVariable (finiteCells F) × (F.Site F.top → Fin 4 → ℍ[ℝ])) : ℝ :=
  chartedEnergy a (stepCoordinates p.1) (fieldOfQuaternions p.2)
private theorem stepCoordinates_zero_fun : stepCoordinates (0 : StepVariable (finiteCells F)) =
    fun (_ : F.Site F.depth) (_ : Fin 4) => (0 : imaginaryQuaternions) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GapTerms.stepCoordinates_zero <;> assumption
private theorem chartEnergyIn_origin [Fintype (F.Site F.depth)] {a : ℝ} (hL : Odd F.blockSide)
    (hA : IsNondegenerateAtTrivial (F := F) (k := F.depth) (minimalAction a (finiteCells F) F.depth)) :
    chartEnergyIn a F (0, quaternionsOfField (trivialBlockField F F.top)) = 0 := by
  unfold chartEnergyIn chartedEnergy
  simp only [stepCoordinates_zero_fun, fieldOfQuaternions_trivial, chartedField_zero_trivial]
  exact blockEnergy_trivial hL hA
private theorem analyticAt_chartEnergyIn [Fintype (F.Site F.depth)] [Fintype (F.Site F.top)] {a : ℝ}
    (hL : Odd F.blockSide)
    (hA : IsNondegenerateAtTrivial (F := F) (k := F.depth) (minimalAction a (finiteCells F) F.depth)) :
    AnalyticAt ℝ (chartEnergyIn a F) (0, quaternionsOfField (trivialBlockField F F.top)) := by
  set p₀ : StepVariable (finiteCells F) × (F.Site F.top → Fin 4 → ℍ[ℝ]) :=
    (0, quaternionsOfField (trivialBlockField F F.top)) with hp₀
  have hV : IsAnalyticFieldFamily
      (fun p : StepVariable (finiteCells F) × (F.Site F.top → Fin 4 → ℍ[ℝ]) => fieldOfQuaternions p.2) p₀ :=
    isAnalytic_fieldOfQuaternions (q := fun p : StepVariable (finiteCells F) × (F.Site F.top → Fin 4 → ℍ[ℝ]) => p.2)
      (fun x i => analyticAt_component analyticAt_snd x i)
      (fun x i => by simp [hp₀, quaternionsOfField, trivialBlockField])
  have hW := isAnalytic_chartedField
    (w := fun p : StepVariable (finiteCells F) × (F.Site F.top → Fin 4 → ℍ[ℝ]) => stepCoordinates p.1)
    (fun x i => analyticAt_stepCoordinates analyticAt_fst x i) hV
  refine analyticAt_blockEnergy hL hA hW hV ?_
  simp only [hp₀, stepCoordinates_zero_fun, fieldOfQuaternions_trivial]
  exact chartedField_zero_trivial
private theorem chartEnergyIn_nonneg [Fintype (F.Site F.depth)] {a : ℝ} (ha : 0 < a)
    (hA : IsNondegenerateAtTrivial (F := F) (k := F.depth) (minimalAction a (finiteCells F) F.depth)) (p) :
    0 ≤ chartEnergyIn a F p :=
  blockEnergy_nonneg ha hA _ _
private theorem fderiv_chartEnergyIn [Fintype (F.Site F.depth)] [Fintype (F.Site F.top)] {a : ℝ} (ha : 0 < a)
    (hL : Odd F.blockSide)
    (hA : IsNondegenerateAtTrivial (F := F) (k := F.depth) (minimalAction a (finiteCells F) F.depth)) :
    fderiv ℝ (chartEnergyIn a F) (0, quaternionsOfField (trivialBlockField F F.top)) = 0 := by
  have : IsLocalMin (chartEnergyIn a F) (0, quaternionsOfField (trivialBlockField F F.top)) := by
    refine Eventually.of_forall fun p => ?_
    rw [chartEnergyIn_origin hL hA]
    exact chartEnergyIn_nonneg ha hA p
  exact this.fderiv_eq_zero
private theorem secondDerivZero_chartEnergyIn_eq [Fintype (F.Site F.depth)] [Fintype (F.Site F.top)] {a : ℝ}
    (ha : 0 < a) (hL : Odd F.blockSide)
    (hA : IsNondegenerateAtTrivial (F := F) (k := F.depth) (minimalAction a (finiteCells F) F.depth))
    {γ : ℝ → StepVariable (finiteCells F) × (F.Site F.top → Fin 4 → ℍ[ℝ])} (hγ : AnalyticAt ℝ γ 0)
    (h0 : γ 0 = (0, quaternionsOfField (trivialBlockField F F.top)))
    {γ' : ℝ → StepVariable (finiteCells F) × (F.Site F.top → Fin 4 → ℍ[ℝ])}
    (hγ' : AnalyticAt ℝ γ' 0) (h0' : γ' 0 = (0, quaternionsOfField (trivialBlockField F F.top)))
    (hv : deriv γ 0 = deriv γ' 0) :
    secondDerivZero (fun τ => chartEnergyIn a F (γ τ)) = secondDerivZero (fun τ => chartEnergyIn a F (γ' τ)) := by
  rw [secondDerivZero_comp (analyticAt_chartEnergyIn hL hA) (fderiv_chartEnergyIn ha hL hA) hγ h0,
    secondDerivZero_comp (analyticAt_chartEnergyIn hL hA) (fderiv_chartEnergyIn ha hL hA) hγ' h0', hv]
private theorem analyticAt_quaternionLine {k : ℕ} [Fintype (F.Site k)] (B : F.Site k → Fin 4 → imaginaryQuaternions) :
    AnalyticAt ℝ (quaternionLine (F := F) B) 0 :=
  AnalyticAt.pi fun x => AnalyticAt.pi fun i => analyticAt_const.add (analyticAt_id.smul analyticAt_const)
private theorem quaternionLine_zero {k : ℕ} (B : F.Site k → Fin 4 → imaginaryQuaternions) :
    quaternionLine (F := F) B 0 = quaternionsOfField (trivialBlockField F k) := by
  funext x i
  simp [quaternionLine, quaternionsOfField, trivialBlockField]
private theorem hasDerivAt_quaternionLine {k : ℕ} [Fintype (F.Site k)] (B : F.Site k → Fin 4 → imaginaryQuaternions) :
    HasDerivAt (quaternionLine (F := F) B) (fun x i => (B x i : ℍ[ℝ])) 0 := by
  rw [hasDerivAt_pi]
  intro x
  rw [hasDerivAt_pi]
  intro i
  have h2 : HasDerivAt (fun τ : ℝ => τ • (B x i : ℍ[ℝ])) ((1 : ℝ) • (B x i : ℍ[ℝ])) 0 :=
    (hasDerivAt_id (0 : ℝ)).smul_const (B x i : ℍ[ℝ])
  rw [one_smul] at h2
  exact h2.const_add (1 : ℍ[ℝ])
private theorem chartEnergyIn_line (a : ℝ) (ξ : StepVariable (finiteCells F))
    (B : F.Site F.top → Fin 4 → imaginaryQuaternions) (τ : ℝ) :
    chartEnergyIn a F (τ • ξ, quaternionLine B τ) =
      blockEnergy a (finiteCells F) F.depth (chartLine ξ B τ) (fieldAlongLine B τ) := rfl
private theorem analyticAt_pairLine [Fintype (F.Site F.top)] (ξ : StepVariable (finiteCells F))
    (B : F.Site F.top → Fin 4 → imaginaryQuaternions) :
    AnalyticAt ℝ (fun τ : ℝ => (τ • ξ, quaternionLine (F := F) B τ)) 0 :=
  (analyticAt_id.smul analyticAt_const).prod (analyticAt_quaternionLine B)
private theorem hasDerivAt_pairLine [Fintype (F.Site F.top)] (ξ : StepVariable (finiteCells F))
    (B : F.Site F.top → Fin 4 → imaginaryQuaternions) :
    HasDerivAt (fun τ : ℝ => (τ • ξ, quaternionLine (F := F) B τ)) (ξ, fun x i => (B x i : ℍ[ℝ])) 0 := by
  have h2 : HasDerivAt (fun τ : ℝ => τ • ξ) ((1 : ℝ) • ξ) 0 := (hasDerivAt_id (0 : ℝ)).smul_const ξ
  rw [one_smul] at h2
  exact h2.prodMk (hasDerivAt_quaternionLine B)
private theorem hessian_pos [Fintype (F.Site F.depth)] [Fintype (F.Site F.top)] {a : ℝ} (ha : 0 < a)
    (hs : ∀ i, 2 ≤ F.extent i) (hL : Odd F.blockSide)
    (hA : IsNondegenerateAtTrivial (F := F) (k := F.depth) (minimalAction a (finiteCells F) F.depth))
    (v : StepVariable (finiteCells F)) (hv : v ≠ 0) :
    0 < fderiv ℝ (fderiv ℝ fun e => chartEnergyIn a F (e, quaternionsOfField (trivialBlockField F F.top))) 0 v v := by
  have hs' : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  set g : StepVariable (finiteCells F) → ℝ :=
    fun e => chartEnergyIn a F (e, quaternionsOfField (trivialBlockField F F.top)) with hg
  have hga : AnalyticAt ℝ g 0 := AnalyticAt.comp (g := chartEnergyIn a F)
    (f := fun e => (e, quaternionsOfField (trivialBlockField F F.top))) (analyticAt_chartEnergyIn hL hA)
    (analyticAt_id.prod analyticAt_const)
  have hcrit : fderiv ℝ g 0 = 0 := by
    have : IsLocalMin g 0 := by
      refine Eventually.of_forall fun e => ?_
      show chartEnergyIn a F _ ≤ chartEnergyIn a F _
      rw [chartEnergyIn_origin hL hA]
      exact chartEnergyIn_nonneg ha hA _
    exact this.fderiv_eq_zero
  have hl : AnalyticAt ℝ (fun τ : ℝ => τ • v) 0 := analyticAt_id.smul analyticAt_const
  have h1 := secondDerivZero_comp hga hcrit hl (by simp)
  have hd : deriv (fun τ : ℝ => τ • v) 0 = v := by
    have h2 : HasDerivAt (fun τ : ℝ => τ • v) ((1 : ℝ) • v) 0 := (hasDerivAt_id (0 : ℝ)).smul_const v
    rw [one_smul] at h2
    exact h2.deriv
  rw [hd] at h1
  rw [← h1]
  have e0 : (fun τ : ℝ => g (τ • v)) =
      fun τ => blockEnergy a (finiteCells F) F.depth (chartLine v 0 τ) (fieldAlongLine 0 τ) := by
    funext τ
    rw [← chartEnergyIn_line]
    simp only [hg]
    congr 2
    funext x i
    simp [quaternionLine, quaternionsOfField, trivialBlockField]
  have hnn : 0 ≤ secondDerivZero (fun τ : ℝ => g (τ • v)) := by
    refine secondDerivZero_nonneg (AnalyticAt.comp (g := g) (f := fun τ : ℝ => τ • v) (by simpa using hga) hl)
      (Eventually.of_forall fun τ => chartEnergyIn_nonneg ha hA _) ?_
    simp only [zero_smul]
    exact chartEnergyIn_origin hL hA
  refine hnn.lt_of_ne' fun hz => hv ?_
  rw [e0] at hz
  obtain ⟨l, hl1, hl2⟩ := exists_potential_of_secondDerivZero_eq_zero ha hs hL hA v 0 hz
  have hβ : ∀ x i, chartVelocity v (0 : F.Site F.top → Fin 4 → imaginaryQuaternions) x i =
      stepCoordinates v x i := by
    intro x i
    unfold chartVelocity
    split_ifs <;> simp
  have hconst := apply_eq_apply_zero_of_tree_and_block_moves hs' hL l (fun z i hb => by
      have h2 := hl1 z i
      rw [hβ] at h2
      have h3 : stepCoordinates v (siteOfCoords F.depth z) i = 0 := by
        unfold stepCoordinates
        rw [dif_neg]
        intro hm
        exact (mem_chordBonds_iff hs hL _).1 hm hb
      rw [h3] at h2
      exact sub_eq_zero.1 h2.symm)
    (fun y i => by
      have h2 := hl2 y i
      exact sub_eq_zero.1 (by simpa using h2.symm))
  funext b
  have h2 := hl1 (siteCoords b.1.1) b.1.2
  rw [hconst (siteCoords b.1.1), hconst (siteCoords b.1.1 + Pi.single b.1.2 1), sub_self, hβ,
    siteOfCoords_siteCoords] at h2
  have h3 : stepCoordinates v b.1.1 b.1.2 = toImaginary (v b) := by
    unfold stepCoordinates
    rw [dif_pos b.2]
  rw [h3] at h2
  have h4 : ‖v b‖ = 0 := by
    rw [← norm_toImaginary, h2]
    simp
  simpa using h4
private theorem minimiser_eq_chartedField [Fintype (F.Site F.depth)] {a : ℝ} (hs : ∀ i, 2 ≤ F.extent i)
    (hL : Odd F.blockSide) (hinv : MinimalActionGaugeInvariant) (hcov : gaugeCovarianceStatement) {r : ℝ}
    (hr : 0 < r) {Y : F.Site F.top → Fin 4 → ℍ[ℝ]} {η₀ : StepVariable (finiteCells F)}
    (hstrict : ∀ e : StepVariable (finiteCells F), ‖e‖ < r → e ≠ η₀ →
      chartEnergyIn a F (η₀, Y) < chartEnergyIn a F (e, Y))
    (hnear : ∀ W : F.GaugeField F.depth, (∀ b, IsAxialTreeBond b → W b.1 b.2 = 1) →
      (∀ W', blockEnergy a (finiteCells F) F.depth W (fieldOfQuaternions Y) ≤
        blockEnergy a (finiteCells F) F.depth W' (fieldOfQuaternions Y)) →
      ∀ x i, ‖((W x i : UnitQuaternion) : ℍ[ℝ]) - 1‖ < r / 4)
    (hV : ∀ x i, ‖((fieldOfQuaternions Y x i : UnitQuaternion) : ℍ[ℝ]) - 1‖ < r / 4) (W' : F.GaugeField F.depth)
    (hW' : ∀ W'', blockEnergy a (finiteCells F) F.depth W' (fieldOfQuaternions Y) ≤
      blockEnergy a (finiteCells F) F.depth W'' (fieldOfQuaternions Y)) :
    gaugeTransform (axialGauge 1 W') W' = chartedField (stepCoordinates η₀) (fieldOfQuaternions Y) := by
  have hs' : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  set W₂ := gaugeTransform (axialGauge 1 W') W' with hW₂
  have hen : blockEnergy a (finiteCells F) F.depth W₂ (fieldOfQuaternions Y) =
      blockEnergy a (finiteCells F) F.depth W' (fieldOfQuaternions Y) :=
    blockEnergy_gaugeTransform hL hinv hcov _ (fun z => GaugeFixing.axialGauge_cellCentre hs' hL 1 W' z) W' _
  have htree : ∀ b, IsAxialTreeBond b → W₂ b.1 b.2 = 1 := fun b hb =>
    GaugeFixing.gaugeTransform_axialGauge_of_isAxialTreeBond hs hL W' b.1 b.2 hb
  have hmin : ∀ W'', blockEnergy a (finiteCells F) F.depth W₂ (fieldOfQuaternions Y) ≤
      blockEnergy a (finiteCells F) F.depth W'' (fieldOfQuaternions Y) := by
    intro W''
    rw [hen]
    exact hW' W''
  obtain ⟨η, hη, he⟩ := exists_chartedField hs hL hr htree (hnear W₂ htree hmin) hV
  have hη₀ : η = η₀ := by
    by_contra hne
    have h1 := hstrict η hη hne
    have h2 : chartEnergyIn a F (η, Y) = blockEnergy a (finiteCells F) F.depth W₂ (fieldOfQuaternions Y) := by
      show blockEnergy a (finiteCells F) F.depth (chartedField (stepCoordinates η) (fieldOfQuaternions Y))
        (fieldOfQuaternions Y) = _
      rw [he]
    have h3 := hmin (chartedField (stepCoordinates η₀) (fieldOfQuaternions Y))
    have h4 : chartEnergyIn a F (η₀, Y) = blockEnergy a (finiteCells F) F.depth
        (chartedField (stepCoordinates η₀) (fieldOfQuaternions Y)) (fieldOfQuaternions Y) := rfl
    linarith
  rw [← he, hη₀]
private theorem gaugeTransform_inv_gaugeTransform {k : ℕ} (γ : F.Site k → UnitQuaternion) (W : F.GaugeField k) :
    gaugeTransform (fun x => (γ x)⁻¹) (gaugeTransform γ W) = W := by
  funext x i
  simp [gaugeTransform, mul_assoc]
private theorem fderiv_chartEnergyIn_fst [Fintype (F.Site F.depth)] {a : ℝ} (ha : 0 < a) (hL : Odd F.blockSide)
    (hA : IsNondegenerateAtTrivial (F := F) (k := F.depth) (minimalAction a (finiteCells F) F.depth)) :
    fderiv ℝ (fun e => chartEnergyIn a F (e, quaternionsOfField (trivialBlockField F F.top))) 0 = 0 := by
  have : IsLocalMin (fun e => chartEnergyIn a F (e, quaternionsOfField (trivialBlockField F F.top))) 0 := by
    refine Eventually.of_forall fun e => ?_
    show chartEnergyIn a F _ ≤ chartEnergyIn a F _
    rw [chartEnergyIn_origin hL hA]
    exact chartEnergyIn_nonneg ha hA _
  exact this.fderiv_eq_zero
end Main
theorem minimalActionNondegeneratePropagates (hmin : ParametricMinima.StrictMinimumPersistsAnalytically)
    (hval : minimalChainExistenceStatement) (hinv : MinimalActionGaugeInvariant)
    (hcov : gaugeCovarianceStatement) : minimalActionNondegeneratePropagatesStatement := by
  intro F _ _ a ha hL hs hA
  have hs' : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  have hval' := hval F a (finiteCells F) ha.le
  set q₁ := quaternionsOfField (trivialBlockField F F.top) with hq₁
  obtain ⟨x, r, hr, hxa, hx0, hev⟩ := hmin (StepVariable (finiteCells F)) (F.Site F.top → Fin 4 → ℍ[ℝ])
    (chartEnergyIn a F) q₁ (analyticAt_chartEnergyIn hL hA) (fderiv_chartEnergyIn_fst ha hL hA)
    (hessian_pos ha hs hL hA)
  have hr4 : 0 < r / 4 := by positivity
  have hU := minimisers_eventually_mem ha hs hL hA
    (U := {W | ∀ x i, ‖((W x i : UnitQuaternion) : ℍ[ℝ]) - 1‖ < r / 4}) (eventually_near_one hr4)
  have hU' := tendsto_fieldOfQuaternions.eventually hU
  have hV' := tendsto_fieldOfQuaternions.eventually (eventually_near_one (F := F) (k := F.top) hr4)
  have hgood : ∀ᶠ Y in 𝓝 q₁,
      (∀ W', (∀ W'', blockEnergy a (finiteCells F) F.depth W' (fieldOfQuaternions Y) ≤
          blockEnergy a (finiteCells F) F.depth W'' (fieldOfQuaternions Y)) →
        gaugeTransform (axialGauge 1 W') W' = chartedField (stepCoordinates (x Y)) (fieldOfQuaternions Y)) ∧
      ∀ v : StepVariable (finiteCells F), v ≠ 0 →
        0 < fderiv ℝ (fderiv ℝ fun e => chartEnergyIn a F (e, Y)) (x Y) v v := by
    filter_upwards [hev, hU', hV'] with Y h1 h2 h3
    exact ⟨fun W' hW' => minimiser_eq_chartedField hs hL hinv hcov hr h1.2.1 h2 h3 W' hW', h1.2.2⟩
  have hleast : ∀ Y, (∀ W', (∀ W'', blockEnergy a (finiteCells F) F.depth W' (fieldOfQuaternions Y) ≤
          blockEnergy a (finiteCells F) F.depth W'' (fieldOfQuaternions Y)) →
        gaugeTransform (axialGauge 1 W') W' = chartedField (stepCoordinates (x Y)) (fieldOfQuaternions Y)) →
      (∀ W', blockEnergy a (finiteCells F) F.depth (chartedField (stepCoordinates (x Y)) (fieldOfQuaternions Y))
          (fieldOfQuaternions Y) ≤ blockEnergy a (finiteCells F) F.depth W' (fieldOfQuaternions Y)) ∧
      minimalAction a (finiteCells F) F.top (fieldOfQuaternions Y) = chartEnergyIn a F (x Y, Y) := by
    intro Y hY
    obtain ⟨W, e, hm⟩ := hval'.2.2.1 F.depth (fieldOfQuaternions Y)
    have hc := hY W hm
    have hen : blockEnergy a (finiteCells F) F.depth (chartedField (stepCoordinates (x Y)) (fieldOfQuaternions Y))
        (fieldOfQuaternions Y) = blockEnergy a (finiteCells F) F.depth W (fieldOfQuaternions Y) := by
      rw [← hc]
      exact blockEnergy_gaugeTransform hL hinv hcov _
        (fun z => GaugeFixing.axialGauge_cellCentre hs' hL 1 W z) W _
    exact ⟨fun W' => by rw [hen]; exact hm W', e.symm.trans hen.symm⟩
  refine ⟨⟨hval'.2.1 F.top, ?_, ?_, ?_, ?_, ?_⟩, x, hxa, hx0, ?_⟩
  · obtain ⟨W, e, hm⟩ := hval'.2.2.1 F.depth (trivialBlockField F F.top)
    refine le_antisymm ?_ (hval'.2.1 _ _)
    rw [← blockEnergy_trivial hL hA (a := a)]
    exact e.symm.le.trans (hm _)
  · have hc := isCompact_univ.continuous_sInf (f := fun (V : F.GaugeField F.top) (W : F.GaugeField F.depth) =>
      blockEnergy a (finiteCells F) F.depth W V) (K := Set.univ) ((continuous_blockEnergy hA).comp continuous_swap)
    refine hc.congr fun V => ?_
    rw [Set.image_univ]
    rfl
  · intro V hV
    obtain ⟨W, e, _⟩ := hval'.2.2.1 F.depth V
    have e' : blockEnergy a (finiteCells F) F.depth W V = 0 := e.trans hV
    obtain ⟨h0, hf⟩ := blockEnergy_eq_zero_parts ha hA e'
    obtain ⟨g, hg⟩ := hA.isPureGauge_of_eq_zero W h0
    exact ⟨fun y => g (blockCoords F.blockSide y), fun y i =>
      top_eq_of_pure hL hg y i (hf _ (mem_innerBonds_finiteCells hs hL le_rfl _))⟩
  · have h1 : AnalyticAt ℝ (fun Y => chartEnergyIn a F (x Y, Y)) q₁ :=
      AnalyticAt.comp (g := chartEnergyIn a F) (f := fun Y => (x Y, Y))
        (by rw [hx0]; exact analyticAt_chartEnergyIn hL hA) (hxa.prod analyticAt_id)
    refine h1.congr ?_
    filter_upwards [hgood] with Y hY
    exact (hleast Y hY.1).2.symm
  · intro B hB
    have hql : Tendsto (quaternionLine (F := F) B) (𝓝 0) (𝓝 q₁) := by
      have := (analyticAt_quaternionLine (F := F) B).continuousAt.tendsto
      rwa [quaternionLine_zero] at this
    set γ : ℝ → StepVariable (finiteCells F) × (F.Site F.top → Fin 4 → ℍ[ℝ]) :=
      fun τ => (x (quaternionLine B τ), quaternionLine B τ) with hγd
    have e1 : (fun τ => minimalAction a (finiteCells F) F.top (fieldAlongLine B τ)) =ᶠ[𝓝 0]
        fun τ => chartEnergyIn a F (γ τ) := by
      filter_upwards [hql.eventually hgood] with τ hτ
      exact (hleast _ hτ.1).2
    have hxq : AnalyticAt ℝ (fun τ => x (quaternionLine (F := F) B τ)) 0 :=
      AnalyticAt.comp (g := x) (f := quaternionLine B) (by rw [quaternionLine_zero]; exact hxa)
        (analyticAt_quaternionLine B)
    have hγ : AnalyticAt ℝ γ 0 := hxq.prod (analyticAt_quaternionLine B)
    have h0 : γ 0 = (0, q₁) := by
      show (x (quaternionLine B 0), quaternionLine B 0) = (0, q₁)
      rw [quaternionLine_zero]
      exact Prod.ext hx0 rfl
    set ξ := deriv (fun τ => x (quaternionLine (F := F) B τ)) 0 with hξ
    have hγd' : HasDerivAt γ (ξ, fun x i => (B x i : ℍ[ℝ])) 0 :=
      hxq.differentiableAt.hasDerivAt.prodMk (hasDerivAt_quaternionLine B)
    have hl0 : (fun τ : ℝ => (τ • ξ, quaternionLine (F := F) B τ)) 0 = (0, q₁) := by
      simp [quaternionLine_zero, hq₁]
    have h2 := secondDerivZero_chartEnergyIn_eq ha hL hA hγ h0 (analyticAt_pairLine ξ B) hl0
      (hγd'.deriv.trans (hasDerivAt_pairLine ξ B).deriv.symm)
    have h3 : secondDerivZero (fun τ => chartEnergyIn a F (γ τ)) = 0 := by
      rw [← secondDerivZero_congr e1]
      exact hB
    rw [h3] at h2
    obtain ⟨l, _, hl⟩ := exists_potential_of_secondDerivZero_eq_zero ha hs hL hA ξ B h2.symm
    exact ⟨fun y => l (blockCoords F.blockSide y), hl⟩
  · have hp : Tendsto (fun Y => (x Y, Y)) (𝓝 q₁) (𝓝 ((0 : StepVariable (finiteCells F)), q₁)) := by
      have h1 : ContinuousAt (fun Y => (x Y, Y)) q₁ := hxa.continuousAt.prodMk continuousAt_id
      have h2 := h1.tendsto
      simpa only [hx0] using h2
    have hAn := hp.eventually (analyticAt_chartEnergyIn hL hA).eventually_analyticAt
    filter_upwards [hgood, hAn] with Y hY hY'
    refine ⟨(hleast Y hY.1).1, fun W' hW' => ?_, ?_, hY.2⟩
    · refine ⟨fun y => (axialGauge 1 W' y)⁻¹, fun z => ?_, ?_⟩
      · show (axialGauge 1 W' (cellCentre F.depth z))⁻¹ = 1
        rw [GaugeFixing.axialGauge_cellCentre hs' hL 1 W' z]
        simp
      · rw [← hY.1 W' hW', gaugeTransform_inv_gaugeTransform]
    · exact AnalyticAt.comp (g := chartEnergyIn a F) (f := fun η => (η, Y)) hY'
        (analyticAt_id.prod analyticAt_const)
end YangMills.Construction.RunningCouplingSlope
end
