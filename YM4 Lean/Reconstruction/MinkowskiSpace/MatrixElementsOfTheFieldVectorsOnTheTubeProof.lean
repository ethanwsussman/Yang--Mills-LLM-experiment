import YangMills.Construction.HilbertSpaces.CompletionsAdjointsAndWeakIntegralsAreWellDefined
import Reconstruction.MinkowskiSpace.BoundaryVectorsOfTheSmearedVectorsProof
import Reconstruction.MinkowskiSpace.EuclideanFormOfAnInvariantRepresentedSequenceProof
import Reconstruction.MinkowskiSpace.SchwartzFunctionsInTheVariablesOfTheDifferences
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped ComplexConjugate InnerProductSpace Topology
noncomputable section
namespace YangMills.Construction.TubeMatrixElements
open MinkowskiSpace FieldForms TubeBoundary ProjectionMeasures RealPointVectors WightmanTheory
  OneLoopNotation
theorem tubeGap_imagTimeShift_one : tubeGap (imagTimeShift 1) = 1 := by
  have him : MinkowskiSpace.imPart (imagTimeShift 1) = timeUnit := by
    funext μ
    simp [MinkowskiSpace.imPart, imagTimeShift, MinkowskiSpace.toComplex]
  have hs : spacePart timeUnit = 0 := by
    funext i
    simp [spacePart, timeUnit, mkTimeSpace]
  unfold tubeGap coneGap
  rw [him, hs]
  simp [spaceNorm, timeUnit, mkTimeSpace]
theorem imagTimeShift_one_mem_futureTube : imagTimeShift 1 ∈ futureTube := by apply _root_.YangMills.Construction.MinkowskiSpace.InvariantEuclideanProof.imagTimeShift_one_mem_futureTube <;> assumption
theorem snocPoint_mem_tubeTuples {n : ℕ} {ζ : Fin n → ComplexVec4}
    (hζ : ζ ∈ tubeTuples n) {c : ComplexVec4} (hc : c ∈ futureTube) :
    snocPoint ζ c ∈ tubeTuples (n + 1) := by
  intro k _
  induction k using Fin.lastCases with
  | last => simpa [snocPoint] using hc
  | cast i => simpa [snocPoint] using hζ i (Set.mem_univ i)
def snocCoords {n : ℕ} (ω : ComplexVec4) (z : Coordinates.ComplexCoordinates ((n + 1) * 4)) :
    Coordinates.ComplexCoordinates ((n + 2) * 4) :=
  fun p => snocPoint (coordsToTuple z) ω
    (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2
theorem coordsToTuple_snocCoords {n : ℕ} (ω : ComplexVec4)
    (z : Coordinates.ComplexCoordinates ((n + 1) * 4)) :
    coordsToTuple (snocCoords ω z) = snocPoint (coordsToTuple z) ω := by
  funext k μ
  change snocPoint _ ω (finProdFinEquiv.symm (finProdFinEquiv (k, μ))).1
    (finProdFinEquiv.symm (finProdFinEquiv (k, μ))).2 = _
  rw [Equiv.symm_apply_apply]
theorem snocCoords_apply {n : ℕ} (ω : ComplexVec4)
    (z : Coordinates.ComplexCoordinates ((n + 1) * 4)) (k : Fin (n + 2)) (μ : Fin 4) :
    snocCoords ω z (finProdFinEquiv (k, μ)) = snocPoint (coordsToTuple z) ω k μ :=
  congrFun (congrFun (coordsToTuple_snocCoords ω z) k) μ
theorem continuous_snocCoords {n : ℕ} (ω : ComplexVec4) :
    Continuous (snocCoords (n := n) ω) := by
  refine continuous_pi fun p => ?_
  obtain ⟨⟨k, μ⟩, rfl⟩ := finProdFinEquiv.surjective p
  simp only [snocCoords_apply]
  induction k using Fin.lastCases with
  | last => simpa [snocPoint] using continuous_const
  | cast i =>
    simp only [snocPoint, Fin.snoc_castSucc, coordsToTuple]
    exact continuous_apply _
theorem snocCoords_add_smul {n : ℕ} (ω : ComplexVec4)
    (a : Coordinates.ComplexCoordinates ((n + 1) * 4)) (t : ℂ) (k₀ : Fin (n + 1)) (μ₀ : Fin 4) :
    snocCoords ω (a + t • Coordinates.ComplexCoordinates.stdBasisVector (finProdFinEquiv (k₀, μ₀))) =
      snocCoords ω a +
        t • Coordinates.ComplexCoordinates.stdBasisVector (finProdFinEquiv (k₀.castSucc, μ₀)) := by
  funext p
  obtain ⟨⟨k, μ⟩, rfl⟩ := finProdFinEquiv.surjective p
  simp only [Pi.add_apply, Pi.smul_apply, snocCoords_apply]
  induction k using Fin.lastCases with
  | last =>
    have hne : (Fin.last (n + 1), μ) ≠ (k₀.castSucc, μ₀) := by
      intro h
      exact (Fin.castSucc_lt_last k₀).ne' (congrArg Prod.fst h)
    simp [snocPoint, Coordinates.ComplexCoordinates.stdBasisVector,
      finProdFinEquiv.injective.eq_iff, hne]
  | cast i =>
    simp [snocPoint, coordsToTuple, Coordinates.ComplexCoordinates.stdBasisVector,
      Pi.single_apply, finProdFinEquiv.injective.eq_iff]
theorem isHolomorphicOnTube_comp_snocPoint {n : ℕ} (w : (Fin (n + 2) → ComplexVec4) → ℂ)
    (hw : IsHolomorphicOnTube w) {ω : ComplexVec4} (hω : ω ∈ futureTube) :
    IsHolomorphicOnTube (m := n + 1) fun ζ => w (snocPoint ζ ω) := by
  obtain ⟨ho, hc, hd⟩ := hw
  have hι := continuous_snocCoords (n := n) ω
  have hmem : ∀ z, z ∈ coordsToTuple ⁻¹' tubeTuples (n + 1) →
      snocCoords ω z ∈ coordsToTuple ⁻¹' tubeTuples (n + 2) := by
    intro z hz
    change coordsToTuple (snocCoords ω z) ∈ tubeTuples (n + 2)
    rw [coordsToTuple_snocCoords]
    exact snocPoint_mem_tubeTuples hz hω
  refine ⟨?_, ?_, ?_⟩
  · have he : coordsToTuple ⁻¹' tubeTuples (n + 1) =
        snocCoords ω ⁻¹' (coordsToTuple ⁻¹' tubeTuples (n + 2)) := by
      ext z
      refine ⟨hmem z, fun hz i _ => ?_⟩
      have h₁ : coordsToTuple (snocCoords ω z) ∈ tubeTuples (n + 2) := hz
      rw [coordsToTuple_snocCoords] at h₁
      simpa [snocPoint] using h₁ i.castSucc (Set.mem_univ _)
    rw [he]
    exact ho.preimage hι
  · have he : (fun (z : Coordinates.ComplexCoordinates ((n + 1) * 4)) (_ : Fin 1) =>
        w (snocPoint (coordsToTuple z) ω)) =
        (fun (z : Coordinates.ComplexCoordinates ((n + 2) * 4)) (_ : Fin 1) =>
          w (coordsToTuple z)) ∘ snocCoords ω := by
      funext z _
      simp only [Function.comp_apply, coordsToTuple_snocCoords]
    rw [he]
    exact hc.comp hι.continuousOn hmem
  · intro a ha j
    obtain ⟨⟨k₀, μ₀⟩, rfl⟩ := finProdFinEquiv.surjective j
    filter_upwards [hd _ (hmem a ha) (finProdFinEquiv (k₀.castSucc, μ₀))] with t ht
    have he : (fun (s : ℂ) (_ : Fin 1) => w (snocPoint (coordsToTuple
          (a + s • Coordinates.ComplexCoordinates.stdBasisVector (finProdFinEquiv (k₀, μ₀)))) ω)) =
        fun (s : ℂ) (_ : Fin 1) => w (coordsToTuple
          (snocCoords ω a +
            s • Coordinates.ComplexCoordinates.stdBasisVector
              (finProdFinEquiv (k₀.castSucc, μ₀)))) := by
      funext s _
      rw [← snocCoords_add_smul, coordsToTuple_snocCoords]
    change DifferentiableAt ℂ (fun (s : ℂ) (_ : Fin 1) => w (snocPoint
      (coordsToTuple
        (a + s • Coordinates.ComplexCoordinates.stdBasisVector (finProdFinEquiv (k₀, μ₀)))) ω)) t
    rw [he]
    exact ht
theorem cumulativeSums_succ {n : ℕ} (Y : TestSpaces.PointTuple (n + 1)) (i : Fin n) :
    cumulativeSums Y i.succ = cumulativeSums Y i.castSucc + Y i.succ := by
  have hI : Finset.Iic i.succ = insert i.succ (Finset.Iic i.castSucc) := by
    ext j
    simp only [Finset.mem_Iic, Finset.mem_insert, Fin.le_def, Fin.ext_iff, Fin.val_succ,
      Fin.val_castSucc]
    omega
  have hn : i.succ ∉ Finset.Iic i.castSucc := by
    rw [Finset.mem_Iic, Fin.le_def, Fin.val_succ, Fin.val_castSucc]
    omega
  unfold cumulativeSums
  rw [hI, Finset.sum_insert hn, add_comm]
theorem cumulativeSums_zero {n : ℕ} (Y : TestSpaces.PointTuple (n + 1)) :
    cumulativeSums Y 0 = Y 0 := by apply _root_.YangMills.Construction.SmearedBoundaryVectors.cumulativeSums_zero <;> assumption
theorem imPart_diffCoords {n : ℕ} (x Y : TestSpaces.PointTuple (n + 1)) (k : Fin (n + 1)) :
    MinkowskiSpace.imPart
      (MinkowskiSpace.diffCoords
        (tupleToComplex x + Complex.I • tupleToComplex (cumulativeSums Y)) k) = Y k := by
  induction k using Fin.cases with
  | zero =>
    funext μ
    simp [MinkowskiSpace.diffCoords, MinkowskiSpace.imPart, tupleToComplex,
      MinkowskiSpace.toComplex, cumulativeSums_zero]
  | succ i =>
    funext μ
    simp [MinkowskiSpace.diffCoords, successiveDiffs, MinkowskiSpace.imPart, tupleToComplex,
      MinkowskiSpace.toComplex, cumulativeSums_succ]
theorem continuous_tupleToComplex {n : ℕ} :
    Continuous fun x : TestSpaces.PointTuple n => tupleToComplex x :=
  continuous_pi fun i => continuous_pi fun μ =>
    Complex.continuous_ofReal.comp ((continuous_apply μ).comp (continuous_apply i))
theorem statement_holds (hP : FieldProductProperties)
    (hW : HilbertWellDefined.WellDefinedStatement)
    (hB : BoundaryValueBound)
    (hS : DifferenceVariables.SchwartzInDifferences) : Statement := by
  intro K _ _ _ E Ω A ℘ C hE n χ
  obtain ⟨-, -, -, -, -, hbd, hhol, hfh, hfb, -, -⟩ := hP K E Ω A ℘ C hE
  obtain ⟨hmp, hflat, -⟩ := hS n
  have hΩ : ‖Ω‖ = 1 := hE.norm_vacuum
  have hq : 0 ≤ ceilExponent ℘ (n + 1) :=
    Int.ceil_nonneg (mul_nonneg (Nat.cast_nonneg _) hE.exponent_nonneg)
  have hH : IsHolomorphicOnTube
      (fun ζ : Fin (n + 1) → ComplexVec4 => tubeMatrixElement E Ω A χ ζ) :=
    isHolomorphicOnTube_comp_snocPoint _ ((hhol (n + 1)).2 χ Ω) imagTimeShift_one_mem_futureTube
  have hbound : ∀ ζ ∈ tubeTuples (n + 1),
      ‖tubeMatrixElement E Ω A χ ζ‖ ≤ ‖χ‖ * ((2 : ℝ) ^ ℘ * C) ^ (n + 1) *
        ∏ k, (min 1 (tubeGap (ζ k)))⁻¹ ^ (ceilExponent ℘ (n + 1)).toNat := by
    intro ζ hζ
    have hb := hbd (n + 1) (snocPoint ζ (imagTimeShift 1))
      (snocPoint_mem_tubeTuples hζ imagTimeShift_one_mem_futureTube)
    have hprod : ∏ k, min 1 (tubeGap (snocPoint ζ (imagTimeShift 1) k)) ^
          (-ceilExponent ℘ (n + 1)) =
        ∏ k, (min 1 (tubeGap (ζ k)))⁻¹ ^ (ceilExponent ℘ (n + 1)).toNat := by
      rw [Fin.prod_univ_castSucc]
      have hl : snocPoint ζ (imagTimeShift 1) (Fin.last (n + 1)) = imagTimeShift 1 := by
        simp [snocPoint]
      rw [hl, tubeGap_imagTimeShift_one]
      simp only [min_self, one_zpow, mul_one]
      refine Finset.prod_congr rfl fun k _ => ?_
      have hk : snocPoint ζ (imagTimeShift 1) k.castSucc = ζ k := by
        simp [snocPoint]
      rw [hk, zpow_neg, ← inv_zpow]
      conv_lhs => rw [← Int.toNat_of_nonneg hq]
      rw [zpow_natCast]
    rw [hprod] at hb
    rw [mul_assoc]
    refine (norm_inner_le_norm _ _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg χ)
    refine le_trans ?_ hb
    have := (fieldProduct E A (n + 1) (snocPoint ζ (imagTimeShift 1))).le_opNorm Ω
    rw [hΩ, mul_one] at this
    simpa [opNormOf] using this
  refine ⟨hH, hbound, fun z => rfl, ?_⟩
  intro Y hY φ hφ
  have hzmem : ∀ x : TestSpaces.PointTuple (n + 1),
      tupleToComplex x + Complex.I • tupleToComplex (cumulativeSums Y) ∈
        diffCoordsInTube (n + 1) := by
    intro x k _
    change coneGap (MinkowskiSpace.imPart _) > 0
    have := imPart_diffCoords x Y k
    change coneGap (MinkowskiSpace.imPart (MinkowskiSpace.diffCoords _ k)) > 0
    rw [this]
    exact hY k
  have hzcont : Continuous fun x : TestSpaces.PointTuple (n + 1) =>
      tupleToComplex x + Complex.I • tupleToComplex (cumulativeSums Y) :=
    continuous_tupleToComplex.add continuous_const
  have hΞ : Continuous (shiftedStateVector E Ω A Y) :=
    (hfh n).2.2.2.2.comp_continuous hzcont hzmem
  have hφi : Integrable φ := by
    have h₁ := (hB (n + 1) (ceilExponent ℘ (n + 1)).toNat
      (‖χ‖ * ((2 : ℝ) ^ ℘ * C) ^ (n + 1)) (tubeMatrixElement E Ω A χ) (Nat.succ_pos n)
      hH hbound).2.1 φ hφ 0
    simpa using h₁
  have hWI : HasWeakIntegrandData Set.univ (shiftedStateVector E Ω A Y) φ := by
    refine ⟨MeasurableSet.univ, ⟨((2 : ℝ) ^ ℘ * C) ^ (n + 1) *
      ∏ k, min 1 (coneGap (Y k)) ^ (-ceilExponent ℘ (n + 1)), fun x _ => ?_⟩,
      fun χ' => (continuous_const.inner hΞ).continuousOn, hφi.integrableOn⟩
    have h₁ := (hfb (n + 1)).2 _ (hzmem x)
    have he : ∀ k, tubeGap (diffCoordsOfLength (n + 1)
        (tupleToComplex x + Complex.I • tupleToComplex (cumulativeSums Y)) k) = coneGap (Y k) := by
      intro k
      change coneGap (MinkowskiSpace.imPart (MinkowskiSpace.diffCoords _ k)) = _
      rw [imPart_diffCoords]
    exact show ‖stateVector E Ω A (n + 1)
        (tupleToComplex x + Complex.I • tupleToComplex (cumulativeSums Y))‖ ≤
        ((2 : ℝ) ^ ℘ * C) ^ (n + 1) *
          ∏ k, min 1 (coneGap (Y k)) ^ (-ceilExponent ℘ (n + 1)) from by
      simpa only [he] using h₁
  refine ⟨hWI, ?_⟩
  have hv := (hW.2.2.2 K (TestSpaces.PointTuple (n + 1)) Set.univ
    (shiftedStateVector E Ω A Y) φ hWI).1 χ
  change ⟪χ, weakInt Set.univ (shiftedStateVector E Ω A Y) φ⟫_ℂ = _
  rw [hv, setIntegral_univ]
  have hg : Continuous fun x => φ x * ⟪χ, shiftedStateVector E Ω A Y x⟫_ℂ :=
    hφ.1.continuous.mul (continuous_const.inner hΞ)
  have hm := integral_map hmp.measurable.aemeasurable
    (f := fun x => φ x * ⟪χ, shiftedStateVector E Ω A Y x⟫_ℂ)
    (by rw [hmp.map_eq]; exact hg.aestronglyMeasurable)
  rw [hmp.map_eq] at hm
  rw [hm]
  unfold TubeBoundary.pairing TubeBoundary.shiftedIntegrand
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have hu : ⟪χ, shiftedStateVector E Ω A Y (cumulativeSums x)⟫_ℂ =
      tubeMatrixElement E Ω A χ (tubePoint x Y) := by
    rw [← hflat x Y]
    rfl
  change φ (cumulativeSums x) * ⟪χ, shiftedStateVector E Ω A Y (cumulativeSums x)⟫_ℂ =
    tubeMatrixElement E Ω A χ (tubePoint x Y) * φ (cumulativeSums x)
  rw [hu, mul_comm]
end YangMills.Construction.TubeMatrixElements
