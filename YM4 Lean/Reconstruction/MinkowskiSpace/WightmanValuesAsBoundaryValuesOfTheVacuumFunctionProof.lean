import Reconstruction.MinkowskiSpace.BoundaryValuesOnTheTubeProof
import Reconstruction.MinkowskiSpace.BoundaryVectorsOfTheSmearedVectorsProof
import Reconstruction.MinkowskiSpace.SchwartzFunctionsInTheVariablesOfTheDifferences
import Reconstruction.MinkowskiSpace.WightmanValuesAsBoundaryValuesOfTheVacuumFunction
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped ComplexConjugate InnerProductSpace Topology
noncomputable section
namespace YangMills.Construction.WightmanBoundaryValues
open MinkowskiSpace FieldForms TestSpaces WightmanReconstruction OneLoopNotation
  ComplexHilbert ProjectionMeasures RealPointVectors TubeBoundary
open WightmanTheory (tubeTuples)
theorem continuous_cumulativeSums {n : ℕ} :
    Continuous (cumulativeSums : PointTuple (n + 1) → PointTuple (n + 1)) := by apply _root_.YangMills.Construction.SmearedBoundaryVectors.continuous_cumulativeSums <;> assumption
theorem cumulativeSums_injective (hs : DifferenceVariables.SchwartzInDifferences)
    {n : ℕ} : Function.Injective (cumulativeSums : PointTuple (n + 1) → PointTuple (n + 1)) := by
  intro x y h
  have hx := (hs n).2.1 x 0
  have hy := (hs n).2.1 y 0
  rw [h] at hx
  have h' : tubePoint x 0 = tubePoint y 0 := hx.symm.trans hy
  funext i μ
  have := congrFun (congrFun h' i) μ
  simpa [tubePoint, toComplex] using this
theorem measurableEmbedding_cumulativeSums
    (hs : DifferenceVariables.SchwartzInDifferences) {n : ℕ} :
    MeasurableEmbedding (cumulativeSums : PointTuple (n + 1) → PointTuple (n + 1)) :=
  continuous_cumulativeSums.measurableEmbedding (cumulativeSums_injective hs)
theorem cumulativeSums_succ_sub {n : ℕ} (Y : PointTuple (n + 1)) (i : Fin n) :
    cumulativeSums Y i.succ - cumulativeSums Y i.castSucc = Y i.succ := by
  have h : Finset.Iic i.succ = insert i.succ (Finset.Iic i.castSucc) := by
    ext j
    simp only [Finset.mem_Iic, Finset.mem_insert, Fin.le_def, Fin.ext_iff, Fin.val_succ,
      Fin.val_castSucc]
    omega
  have hn : i.succ ∉ Finset.Iic i.castSucc := by
    simp [Fin.le_def]
  simp only [cumulativeSums]
  rw [h, Finset.sum_insert hn]
  simp
theorem successiveDiffs_tupleToComplex_cumulativeSums {n : ℕ} (Y : PointTuple (n + 1)) :
    successiveDiffs (tupleToComplex (cumulativeSums Y)) = tupleToComplex fun i : Fin n => Y i.succ := by
  funext i μ
  have h := congrFun (cumulativeSums_succ_sub Y i) μ
  simp only [successiveDiffs, tupleToComplex, toComplex, Pi.sub_apply] at h ⊢
  rw [← h]
  push_cast
  rfl
theorem successiveDiffs_add_I_smul {n : ℕ} (x Y : PointTuple (n + 1)) :
    successiveDiffs (tupleToComplex x + Complex.I • tupleToComplex Y) =
      successiveDiffs (tupleToComplex x) + Complex.I • successiveDiffs (tupleToComplex Y) := by
  funext i μ
  simp only [successiveDiffs, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring
def consFirst {n : ℕ} (Y₁ : Fin 4 → ℝ) (Y' : PointTuple n) : PointTuple (n + 1) :=
  Fin.cons (α := fun _ => Fin 4 → ℝ) Y₁ Y'
theorem consFirst_succ {n : ℕ} (Y₁ : Fin 4 → ℝ) (Y' : PointTuple n) (i : Fin n) :
    consFirst Y₁ Y' i.succ = Y' i := by
  simp [consFirst]
theorem consFirst_zero {n : ℕ} (Y₁ : Fin 4 → ℝ) (Y' : PointTuple n) : consFirst Y₁ Y' 0 = Y₁ := by
  simp [consFirst]
theorem continuous_consFirst {n : ℕ} {X : Type*} [TopologicalSpace X] {f : X → Fin 4 → ℝ}
    {g : X → PointTuple n} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun p => consFirst (f p) (g p) := by
  refine continuous_pi fun k => ?_
  refine Fin.cases ?_ (fun i => ?_) k
  · simpa only [consFirst_zero] using hf
  · simp only [consFirst_succ]
    exact (continuous_apply i).comp hg
theorem coneGap_smul_timeUnit (t : ℝ) : coneGap (t • timeUnit) = t := by
  simp [coneGap, spacePart, spaceNorm, timeUnit, mkTimeSpace]
theorem consFirst_mem_futureConeTuples {n : ℕ} {t : ℝ} (ht : 0 < t) {Y' : PointTuple n}
    (hY : Y' ∈ RealPointVectors.futureConeTuples n) :
    consFirst (t • timeUnit) Y' ∈ TubeBoundary.futureConeTuples (n + 1) := by
  intro k _
  refine Fin.cases ?_ (fun i => ?_) k
  · rw [consFirst_zero]
    show coneGap (t • timeUnit) > 0
    rw [coneGap_smul_timeUnit]
    exact ht
  · rw [consFirst_succ]
    exact hY i
theorem consFirst_mem_closedFutureConeTuples {n : ℕ} {t : ℝ} (ht : 0 ≤ t) {Y' : PointTuple n}
    (hY : Y' ∈ RealPointVectors.closedFutureConeTuples n) :
    consFirst (t • timeUnit) Y' ∈ TubeBoundary.closedFutureConeTuples (n + 1) := by
  intro k _
  refine Fin.cases ?_ (fun i => ?_) k
  · rw [consFirst_zero]
    show coneGap (t • timeUnit) ≥ 0
    rw [coneGap_smul_timeUnit]
    exact ht
  · rw [consFirst_succ]
    exact hY i
theorem futureConeTuples_subset_closed (n : ℕ) :
    RealPointVectors.futureConeTuples n ⊆ RealPointVectors.closedFutureConeTuples n := by
  intro Y h i
  have h1 : coneGap (Y i) > 0 := h i
  show coneGap (Y i) ≥ 0
  exact h1.le
theorem tubePoint_mem_tubeTuples {b : ℕ} (x : PointTuple b) {Y : PointTuple b}
    (hY : Y ∈ TubeBoundary.futureConeTuples b) : tubePoint x Y ∈ tubeTuples b := by
  intro k hk
  have h : MinkowskiSpace.imPart (tubePoint x Y k) = Y k := by
    funext μ
    simp [MinkowskiSpace.imPart, tubePoint, toComplex]
  show MinkowskiSpace.imPart _ ∈ futureCone
  rw [h]
  exact hY k hk
section Vectors
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {E : FourBorelSet → BddOp K} {Ω : K} {A : ℝ → BddOp K} {℘ C : ℝ}
theorem tubeMatrixElement_vacuum_eq (hm : TubeMatrixElements.Statement)
    (hs : DifferenceVariables.SchwartzInDifferences)
    (hp : FieldProductProperties) (hf : IsBoundedFieldForm E Ω A ℘ C) {n : ℕ}
    (x : PointTuple (n + 1)) (Y₁ : Fin 4 → ℝ) (Y' : PointTuple n)
    (hY : consFirst Y₁ Y' ∈ TubeBoundary.futureConeTuples (n + 1)) :
    tubeMatrixElement E Ω A Ω (tubePoint x (consFirst Y₁ Y')) =
      vacuumExpectation E Ω A (n + 1)
        (successiveDiffs (tupleToComplex (cumulativeSums x)) + Complex.I • tupleToComplex Y') := by
  set Y := consFirst Y₁ Y' with hYdef
  set z : Fin (n + 1) → ComplexVec4 :=
    tupleToComplex (cumulativeSums x) + Complex.I • tupleToComplex (cumulativeSums Y) with hzdef
  have hflat : MinkowskiSpace.diffCoords z = tubePoint x Y := (hs n).2.1 x Y
  have hz : z ∈ diffCoordsInTube (n + 1) := by
    show MinkowskiSpace.diffCoords z ∈ tubeTuples (n + 1)
    rw [hflat]
    exact tubePoint_mem_tubeTuples x hY
  have h1 := (hm E Ω A ℘ C hf n Ω).2.2.1 z
  rw [hflat] at h1
  obtain ⟨-, -, -, -, -, -, -, -, -, hvec, -⟩ := hp K E Ω A ℘ C hf
  have hw : (fun i : Fin 0 => i.elim0 : Fin 0 → ComplexVec4) ∈ diffCoordsInTube 0 := by
    intro k
    exact k.elim0
  have h0 : MinkowskiSpace.imPart (0 : ComplexVec4) ∈ closedFutureCone := by
    have : MinkowskiSpace.imPart (0 : ComplexVec4) = 0 := by
      funext μ
      simp [MinkowskiSpace.imPart]
    rw [this]
    show coneGap 0 ≥ 0
    simp [coneGap, spacePart, spaceNorm]
  have h2 := (hvec (n + 1) 0 z _ 0 hz hw h0).2.1
  have hd : successiveDiffs z =
      successiveDiffs (tupleToComplex (cumulativeSums x)) + Complex.I • tupleToComplex Y' := by
    rw [hzdef, successiveDiffs_add_I_smul, successiveDiffs_tupleToComplex_cumulativeSums Y]
    have : (fun i : Fin n => Y i.succ) = Y' := by
      funext i
      exact consFirst_succ Y₁ Y' i
    rw [this]
  rw [← h1, h2]
  exact congrArg (vacuumExpectation E Ω A (n + 1)) hd
theorem shiftedIntegrand_vacuum_eq (hm : TubeMatrixElements.Statement)
    (hs : DifferenceVariables.SchwartzInDifferences)
    (hp : FieldProductProperties) (hf : IsBoundedFieldForm E Ω A ℘ C) {n : ℕ}
    (φ : PointTuple (n + 1) → ℂ) (Y₁ : Fin 4 → ℝ) (Y' : PointTuple n)
    (hY : consFirst Y₁ Y' ∈ TubeBoundary.futureConeTuples (n + 1)) :
    shiftedIntegrand (tubeMatrixElement E Ω A Ω (m := n)) (consFirst Y₁ Y')
        (RealPointVectors.diffCoords φ) =
      vacuumIntegrand E Ω A φ Y' ∘ cumulativeSums := by
  funext y
  simp only [shiftedIntegrand, Function.comp_apply, vacuumIntegrand, RealPointVectors.diffCoords]
  rw [tubeMatrixElement_vacuum_eq hm hs hp hf y Y₁ Y' hY]
theorem vacuum_boundaryData (hm : TubeMatrixElements.Statement)
    (hv : TubeBoundary.BoundaryValueBound) (hf : IsBoundedFieldForm E Ω A ℘ C) (n : ℕ) :
    (∀ Y ∈ TubeBoundary.futureConeTuples (n + 1), ∀ φ ∈ schwartzSet (n + 1),
      Integrable (shiftedIntegrand (tubeMatrixElement E Ω A Ω (m := n)) Y φ)) ∧
    IsBoundaryExtension (tubeMatrixElement E Ω A Ω (m := n))
      (boundaryValue (tubeMatrixElement E Ω A Ω (m := n))) := by
  obtain ⟨hol, bd, -, -⟩ := hm E Ω A ℘ C hf n Ω
  obtain ⟨h1, -, -, hext, -⟩ := hv (n + 1) _ _ _ (Nat.succ_pos n) hol bd
  exact ⟨h1, hext⟩
theorem integrable_and_boundaryValue_eq (hm : TubeMatrixElements.Statement)
    (hv : TubeBoundary.BoundaryValueBound)
    (hs : DifferenceVariables.SchwartzInDifferences)
    (hp : FieldProductProperties) (hf : IsBoundedFieldForm E Ω A ℘ C) {n : ℕ}
    (φ : PointTuple (n + 1) → ℂ) (hφ : φ ∈ schwartzSet (n + 1)) {t : ℝ} (ht : 0 < t)
    {Y' : PointTuple n} (hY' : Y' ∈ RealPointVectors.futureConeTuples n) :
    Integrable (vacuumIntegrand E Ω A φ Y') ∧
      boundaryValue (tubeMatrixElement E Ω A Ω (m := n)) (consFirst (t • timeUnit) Y')
        (RealPointVectors.diffCoords φ) = ∫ x, vacuumIntegrand E Ω A φ Y' x := by
  have hφ' := ((hs n).2.2 φ hφ).1
  have hY := consFirst_mem_futureConeTuples ht hY'
  obtain ⟨hint, hext⟩ := vacuum_boundaryData (E := E) (Ω := Ω) (A := A) hm hv hf n
  have mp := (hs n).1
  have emb := measurableEmbedding_cumulativeSums hs (n := n)
  have heq := shiftedIntegrand_vacuum_eq hm hs hp hf φ (t • timeUnit) Y' hY
  constructor
  · have h := hint _ hY _ hφ'
    rw [heq] at h
    exact (mp.integrable_comp_emb emb).1 h
  · rw [hext.1 _ hY _ hφ', pairing, heq]
    exact mp.integral_comp emb _
theorem translateBy_zero {b : ℕ} (φ : PointTuple b → ℂ) :
    TubeBoundary.translateBy (0 : PointTuple b) φ = φ := by apply _root_.YangMills.Construction.TubeBoundary.translateBy_zero <;> assumption
theorem boundaryValue_at_zero (hm : TubeMatrixElements.Statement)
    (hv : TubeBoundary.BoundaryValueBound)
    (hs : DifferenceVariables.SchwartzInDifferences)
    (hp : FieldProductProperties) (hf : IsBoundedFieldForm E Ω A ℘ C) {n : ℕ}
    (φ : PointTuple (n + 1) → ℂ) (hφ : φ ∈ schwartzSet (n + 1))
    {Y' : PointTuple n} (hY' : Y' ∈ RealPointVectors.futureConeTuples n) :
    boundaryValue (tubeMatrixElement E Ω A Ω (m := n)) (consFirst 0 Y')
      (RealPointVectors.diffCoords φ) = ∫ x, vacuumIntegrand E Ω A φ Y' x := by
  have hφ' := ((hs n).2.2 φ hφ).1
  obtain ⟨-, hext⟩ := vacuum_boundaryData (E := E) (Ω := Ω) (A := A) hm hv hf n
  have hc := hext.2.1 _ hφ'
  have hclosed := futureConeTuples_subset_closed n hY'
  set J := boundaryValue (tubeMatrixElement E Ω A Ω (m := n)) with hJ
  let γ : ℝ → PointTuple (n + 1) × PointTuple (n + 1) := fun t => (consFirst (t • timeUnit) Y', 0)
  have hγc : Continuous γ :=
    (continuous_consFirst (continuous_id.smul continuous_const) continuous_const).prodMk
      continuous_const
  have hγ0 : γ 0 = (consFirst 0 Y', 0) := by
    simp [γ]
  have hin : ∀ t : ℝ, 0 ≤ t →
      γ t ∈ TubeBoundary.closedFutureConeTuples (n + 1) ×ˢ (Set.univ : Set (PointTuple (n + 1))) :=
    fun t ht => ⟨consFirst_mem_closedFutureConeTuples ht hclosed, Set.mem_univ _⟩
  have h0 := hc (γ 0) (hin 0 le_rfl)
  have hmap : Tendsto γ (𝓝[>] (0 : ℝ))
      (𝓝[TubeBoundary.closedFutureConeTuples (n + 1) ×ˢ Set.univ] (γ 0)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨(hγc.tendsto 0).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    exact hin t ht.le
  have hlim := Tendsto.comp h0 hmap
  have hconst : Tendsto (fun _ : ℝ => ∫ x, vacuumIntegrand E Ω A φ Y' x) (𝓝[>] (0 : ℝ))
      (𝓝 (J (consFirst 0 Y') (RealPointVectors.diffCoords φ))) := by
    simp only [hγ0, translateBy_zero] at hlim
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    simp only [Function.comp_apply, γ, translateBy_zero]
    exact (integrable_and_boundaryValue_eq hm hv hs hp hf φ hφ ht hY').2
  exact (tendsto_nhds_unique hconst tendsto_const_nhds)
end Vectors
theorem boundaryValueTheorem_holds (hb : SmearedBoundaryVectors.Statement)
    (hm : TubeMatrixElements.Statement)
    (hv : TubeBoundary.BoundaryValueBound)
    (hs : DifferenceVariables.SchwartzInDifferences)
    (hp : FieldProductProperties) : BoundaryValueTheorem := by
  intro K _ _ _ E Ω A ℘ C hf
  have hB := hb E Ω A ℘ C hf
  have hΩ : ‖Ω‖ = 1 := hf.norm_vacuum
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c
    show ⟪Ω, scalarOfOrderZero c • Ω⟫_ℂ = c
    rw [inner_smul_right, inner_self_eq_norm_sq_to_K, hΩ]
    simp [scalarOfOrderZero]
  · intro n φ hφ Y' hY'
    exact (integrable_and_boundaryValue_eq hm hv hs hp hf φ hφ one_pos hY').1
  · intro n φ hφ
    have hφ' := ((hs n).2.2 φ hφ).1
    obtain ⟨-, hext⟩ := vacuum_boundaryData (E := E) (Ω := Ω) (A := A) hm hv hf n
    have hc := hext.2.1 _ hφ'
    refine ⟨fun Y' => boundaryValue (tubeMatrixElement E Ω A Ω (m := n))
      (consFirst 0 Y') (RealPointVectors.diffCoords φ), ?_, ?_, ?_⟩
    · have hmaps : Set.MapsTo (fun Y' : PointTuple n => (consFirst 0 Y', (0 : PointTuple (n + 1))))
          (RealPointVectors.closedFutureConeTuples n)
          (TubeBoundary.closedFutureConeTuples (n + 1) ×ˢ Set.univ) := by
        intro Y' hY'
        refine ⟨?_, Set.mem_univ _⟩
        have := consFirst_mem_closedFutureConeTuples (t := 0) le_rfl hY'
        simpa using this
      have hcf : Continuous fun Y' : PointTuple n => (consFirst 0 Y', (0 : PointTuple (n + 1))) :=
        (continuous_consFirst continuous_const continuous_id).prodMk continuous_const
      have := hc.comp hcf.continuousOn hmaps
      simpa only [Function.comp_def, translateBy_zero] using this
    · intro Y' hY'
      exact boundaryValue_at_zero hm hv hs hp hf φ hφ hY'
    · have h0 : consFirst (0 : Fin 4 → ℝ) (0 : PointTuple n) = 0 := by
        funext k
        refine Fin.cases ?_ (fun i => ?_) k
        · rw [consFirst_zero]
          rfl
        · rw [consFirst_succ]
          rfl
      show boundaryValue _ (consFirst 0 0) _ = ⟪Ω, testState E Ω A (n + 1) φ⟫_ℂ
      rw [h0, hB.inner_testState_eq_boundaryValue n φ hφ Ω]
  · intro n φ hφ
    have h1 : ‖wightmanFunctional E Ω A (n + 1) φ‖ ≤ ‖Ω‖ * ‖testState E Ω A (n + 1) φ‖ :=
      norm_inner_le_norm _ _
    rw [hΩ, one_mul] at h1
    exact h1.trans (hB.norm_testState_le n φ hφ)
end YangMills.Construction.WightmanBoundaryValues
