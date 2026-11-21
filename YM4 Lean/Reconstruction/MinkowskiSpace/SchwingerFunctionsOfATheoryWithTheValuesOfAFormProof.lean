import Reconstruction.MinkowskiSpace.SchwingerFunctionsOfAEuclideanFieldFormProof
import Reconstruction.MinkowskiSpace.ProductsOfABoundedFieldForm
import Reconstruction.MinkowskiSpace.SchwingerFunctionsOfATheoryWithTheValuesOfAForm
import Reconstruction.MinkowskiSpace.VectorsAtRealPointsOfABoundedFieldForm
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Topology
noncomputable section
namespace YangMills.Construction.TheorySchwinger
open MinkowskiSpace FieldForms RealPointVectors WightmanTheory ProjectionMeasures OneLoopNotation
  ComplexHilbert
theorem zpow_neg_le_inv_pow_toNat {x : ℝ} (hpos : 0 < x) (hle : x ≤ 1) (q : ℤ) :
    x ^ (-q) ≤ x⁻¹ ^ q.toNat := by
  rcases le_total 0 q with hq | hq
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    simp [zpow_neg, inv_pow]
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.mpr hq)
    have ht : q.toNat = 0 := Int.toNat_of_nonpos hq
    rw [hn, ht, zpow_natCast, pow_zero]
    exact pow_le_one₀ hpos.le hle
theorem continuous_rotatePermute {q : ℕ} (R : Matrix.orthogonalGroup (Fin 4) ℝ)
    (σ : Equiv.Perm (Fin q)) : Continuous (TestSpaces.rotatePermute R σ) := by apply _root_.YangMills.Construction.FieldForms.EuclideanSchwinger.continuous_rotatePermute <;> assumption
def wickDiffCoords {m : ℕ} (x : TestSpaces.PointTuple (m + 1)) :
    Coordinates.ComplexCoordinates (m * 4) :=
  fun j => FieldForms.wickDiffs x (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2
theorem coordsToTuple_wickDiffCoords {m : ℕ} (x : TestSpaces.PointTuple (m + 1)) :
    coordsToTuple (wickDiffCoords x) = FieldForms.wickDiffs x := by
  funext k μ
  simp [coordsToTuple, wickDiffCoords]
theorem continuous_wickDiffs_apply {m : ℕ} (k : Fin m) (μ : Fin 4) :
    Continuous fun x : TestSpaces.PointTuple (m + 1) => FieldForms.wickDiffs x k μ := by
  have hc : ∀ i : Fin (m + 1), Continuous fun x : TestSpaces.PointTuple (m + 1) =>
      wickMap (toComplex (x i)) μ := by
    intro i
    have hlin : Continuous fun z : ComplexVec4 => wickMap z μ :=
      (continuous_apply μ).comp wickMap.toLinearMap.continuous_of_finiteDimensional
    refine hlin.comp (continuous_pi fun ν => ?_)
    simp only [toComplex]
    fun_prop
  exact ((hc k.succ).sub (hc k.castSucc)).congr fun x => rfl
theorem continuous_wickDiffCoords {m : ℕ} :
    Continuous (wickDiffCoords (m := m)) :=
  continuous_pi fun _ => continuous_wickDiffs_apply _ _
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem continuousOn_schwinger (E : FourBorelSet → BddOp H) (v : H)
    (A : ℝ → BddOp H) (m : ℕ) (hw : SchwingerWellDefined E v A m)
    (hol : IsHolomorphicOnTube (m := m) (vacuumExpectation E v A (m + 1))) :
    ContinuousOn (schwinger E v A m)
      (TestSpaces.distinctLocus (m + 1)) := by
  have hopen : IsOpen (TestSpaces.distinctLocus (m + 1)) :=
    ConfigSpace.isOpen_distinctArgs
  intro x hx
  refine ContinuousAt.continuousWithinAt ?_
  obtain ⟨⟨R, σ, -, hRσ⟩, -⟩ := hw x hx
  have hg := continuous_rotatePermute R σ
  have hU : TestSpaces.rotatePermute R σ ⁻¹' TestSpaces.increasingTimes (m + 1) ∈ 𝓝 x :=
    (TestSpaces.isOpen_increasingTimes (m + 1)).preimage hg |>.mem_nhds hRσ
  have heq : (fun y => vacuumExpectation E v A (m + 1)
        (coordsToTuple (wickDiffCoords (TestSpaces.rotatePermute R σ y))))
      =ᶠ[𝓝 x] schwinger E v A m := by
    filter_upwards [hU, hopen.mem_nhds hx] with y hy hyd
    rw [coordsToTuple_wickDiffCoords]
    exact (((hw y hyd).2 R σ hy)).symm
  refine ContinuousAt.congr ?_ heq
  have hmem : wickDiffCoords (TestSpaces.rotatePermute R σ x) ∈
      (coordsToTuple ⁻¹' tubeTuples m : Set (Coordinates.ComplexCoordinates (m * 4))) := by
    rw [Set.mem_preimage, coordsToTuple_wickDiffCoords]
    exact fun k _ => wickDiffs_mem_futureTube hRσ k
  have hcont := (hol.2.1.continuousAt (hol.1.mem_nhds hmem))
  have hcomp : ContinuousAt (fun y => (fun _ : Fin 1 => vacuumExpectation E v A (m + 1)
      (coordsToTuple (wickDiffCoords (TestSpaces.rotatePermute R σ y))))) x :=
    ContinuousAt.comp (f := fun y => wickDiffCoords (TestSpaces.rotatePermute R σ y))
      hcont (continuous_wickDiffCoords.comp hg).continuousAt
  exact (continuous_apply (0 : Fin 1)).continuousAt.comp hcomp
theorem claim_of_fieldForm (hS : EuclideanSchwingerProperties)
    (hP : FieldProductProperties)
    (hV : BoundaryVectorsStatement) : Claim := by
  intro H _ _ _ E v A p C hF hEu L _ _ _ T hW S hSeq hInt
  have hVec := hV E v A p C hF
  have hSch := hS H E v A p C hF hEu
  obtain ⟨-, -, -, -, -, -, -, hHol, hBd, -, -⟩ := hP H E v A p C hF
  have key : ∀ m : ℕ, ∃ (q : ℕ) (c : ℝ),
      IsAnalyticContinuationData T S m (vacuumExpectation E v A (m + 1)) q c
        (schwinger E v A m) := by
    intro m
    have hcont := continuousOn_schwinger E v A m (hSch m).1 (hHol m).1
    refine ⟨(ceilExponent p (m + 1)).toNat, |((2 : ℝ) ^ p * C) ^ (m + 1)|,
      (hHol m).1, hcont, ?_, ?_, ?_, ?_⟩
    · intro z hz
      have hb := (hBd (m + 1)).1 z hz
      have hpos : ∀ k, 0 < min 1 (tubeGap (z k)) := fun k =>
        lt_min one_pos (hz k (Set.mem_univ k))
      have hprod : ∏ k, min 1 (tubeGap (z k)) ^ (-ceilExponent p (m + 1)) ≤
          ∏ k, (min 1 (tubeGap (z k)))⁻¹ ^ (ceilExponent p (m + 1)).toNat :=
        Finset.prod_le_prod (fun k _ => (zpow_pos (hpos k) _).le)
          fun k _ => zpow_neg_le_inv_pow_toNat (hpos k) (min_le_left _ _) _
      have hnn : 0 ≤ ∏ k, min 1 (tubeGap (z k)) ^ (-ceilExponent p (m + 1)) :=
        Finset.prod_nonneg fun k _ => (zpow_pos (hpos k) _).le
      calc ‖vacuumExpectation E v A (m + 1) z‖ ≤ _ := hb
        _ ≤ |((2 : ℝ) ^ p * C) ^ (m + 1)| *
            ∏ k, min 1 (tubeGap (z k)) ^ (-ceilExponent p (m + 1)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hnn
        _ ≤ _ := mul_le_mul_of_nonneg_left hprod (abs_nonneg _)
    · intro f
      have hφ : TestSpaces.tensorProd (fun i => (f i).1) ∈ TestSpaces.schwartzSet (m + 1) :=
        hVec.tensorVal_mem (m + 1) (fun i => (f i).1) fun i => (f i).2
      set φ : TestSpaces.PointTuple (m + 1) → ℂ := TestSpaces.tensorProd (fun i => (f i).1)
        with hφdef
      let Y : ℝ → TestSpaces.PointTuple m := fun ε _ => ε • timeUnit
      have hY : ∀ ε : ℝ, 0 < ε → Y ε ∈ futureConeTuples m := by
        intro ε hε i
        change coneGap (ε • timeUnit) > 0
        simpa [coneGap, spacePart, timeUnit, mkTimeSpace, spaceNorm] using hε
      have hYc : ∀ ε : ℝ, 0 ≤ ε → Y ε ∈ closedFutureConeTuples m := by
        intro ε hε i
        change coneGap (ε • timeUnit) ≥ 0
        simpa [coneGap, spacePart, timeUnit, mkTimeSpace, spaceNorm] using hε
      have hpt : ∀ (ε : ℝ) (x : TestSpaces.PointTuple (m + 1)), boundaryApproach x ε =
          successiveDiffs (tupleToComplex x) + Complex.I • tupleToComplex (Y ε) := by
        intro ε x
        funext k μ
        simp [boundaryApproach, tupleToComplex, toComplex, Y, mul_comm]
        ring
      have hint : ∀ (ε : ℝ) (x : TestSpaces.PointTuple (m + 1)),
          vacuumExpectation E v A (m + 1) (boundaryApproach x ε) * ∏ i, (f i).1 (x i) =
            vacuumIntegrand E v A φ (Y ε) x := by
        intro ε x
        rw [hpt]
        rfl
      obtain ⟨G, hGc, hGeq, hG0⟩ := hVec.exists_continuousOn_extension m φ hφ
      refine ⟨fun ε hε => ?_, ?_⟩
      · simp only [hint]
        exact hVec.integrable_vacuumIntegrand m φ hφ (Y ε) (hY ε hε)
      · have hlim : Tendsto (fun ε => G (Y ε)) (𝓝[>] 0) (𝓝 (G 0)) := by
          have hY0 : Y 0 = 0 := by
            funext k
            simp [Y]
          have hYt : Tendsto Y (𝓝[>] 0) (𝓝[closedFutureConeTuples m] 0) := by
            refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
            · have hYcont : Continuous Y := by
                refine continuous_pi fun _ => ?_
                fun_prop
              have := hYcont.tendsto' 0 (0 : TestSpaces.PointTuple m) hY0
              exact this.mono_left nhdsWithin_le_nhds
            · filter_upwards [self_mem_nhdsWithin] with ε hε
              exact hYc ε (le_of_lt hε)
          exact (hGc 0 (by simpa [hY0] using hYc 0 le_rfl)).tendsto.comp hYt
        rw [hG0] at hlim
        rw [hW m f]
        refine hlim.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with ε hε
        rw [hGeq (Y ε) (hY ε hε)]
        simp only [hint]
    · intro σ x hx
      have hxd : x ∈ TestSpaces.distinctLocus (m + 1) := by
        intro i j hij
        have hinj := TestSpaces.increasingTimes_subset_distinctLocus (m + 1) hx
        have h3 := hinj (a₁ := σ.symm i) (a₂ := σ.symm j) (by
          simp [TestSpaces.rotatePermute, hij])
        simpa using congrArg σ h3
      exact ((hSch m).1 x hxd).2 1 σ hx
    · intro φ hφ
      have hφc : Continuous φ.1 := hφ.1.continuous
      have hsupp : tsupport φ.1 ⊆ TestSpaces.distinctLocus (m + 1) := hφ.2.2
      have hopen : IsOpen (TestSpaces.distinctLocus (m + 1)) :=
        ConfigSpace.isOpen_distinctArgs
      have hc : Continuous fun x => schwinger E v A m x * φ.1 x := by
        refine continuous_of_tsupport fun x hx => ?_
        have hx' : x ∈ tsupport φ.1 := tsupport_mul_subset_right hx
        exact ((hcont x (hsupp hx')).continuousAt (hopen.mem_nhds (hsupp hx'))).mul
          hφc.continuousAt
      refine ⟨hc.integrable_of_hasCompactSupport hφ.2.1.mul_left, ?_⟩
      have h := hInt m φ.1 hφ φ.2
      refine h.trans ?_
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      by_cases hx : x ∈ TestSpaces.distinctLocus (m + 1)
      · simp [Set.indicator_of_mem hx, mul_comm]
      · have h0 : φ.1 x = 0 := image_eq_zero_of_notMem_tsupport fun hx' => hx (hsupp hx')
        simp [Set.indicator_of_notMem hx, h0]
  refine ⟨⟨hSeq, fun m => ?_⟩, key⟩
  obtain ⟨q, c, h⟩ := key m
  exact ⟨_, q, c, _, h⟩
end YangMills.Construction.TheorySchwinger
