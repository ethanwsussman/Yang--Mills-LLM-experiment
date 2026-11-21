import YangMills.Construction.Matrices.SecondDifferentialOfTheLogarithmOfADeterminantProof
import Reconstruction.ComplexAnalysis.ProductAndHalfPlaneIdentity
import YangMills.Construction.Continuum.BumpsSmoothedIndicatorsAndTensorsOfBumpsProof
import YangMills.Construction.Continuum.ChosenSmoothFunctionsPartitionsOfUnityRotationsAndIntegrability
import YangMills.Construction.Continuum.FirstFactsOnTheTestSpaces
import YangMills.Construction.Coordinates.PowerSeriesHolomorphy
import Reconstruction.MinkowskiSpace.BoundaryVectorsOfTheSmearedVectors
import Reconstruction.MinkowskiSpace.ClosureOfTheTensorVectorsAndTheEuclideanVectors
import Reconstruction.MinkowskiSpace.ConeTubeAndLorentzGroup
import Reconstruction.MinkowskiSpace.FunctionOnTheTubeDeterminedByItsBoundaryValue
import Reconstruction.MinkowskiSpace.MatrixElementsOfTheFieldVectorsOnTheTube
import Reconstruction.MinkowskiSpace.SchwartzFunctionsInTheVariablesOfTheDifferences
import Reconstruction.MinkowskiSpace.SchwartzFunctionsThatStandInTheVectorsAtRealPoints
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set
open scoped ComplexConjugate InnerProductSpace Topology ContDiff
noncomputable section
namespace YangMills.Construction
open MinkowskiSpace FieldForms TestSpaces WightmanReconstruction OneLoopNotation ComplexHilbert
  ProjectionMeasures RealPointVectors TubeBoundary
open WightmanTheory (tubeTuples coordsToTuple IsHolomorphicOnTube)
namespace RealPointVectors.TensorClosure
def tupleCoordsEquiv (b : ℕ) :
    (Fin b → ComplexVec4) ≃ₗ[ℂ] Coordinates.ComplexCoordinates (b * 4) where
  toFun ζ j := ζ (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2
  invFun := coordsToTuple
  map_add' a c := rfl
  map_smul' t a := rfl
  left_inv ζ := by
    funext k μ
    simp [WightmanTheory.coordsToTuple]
  right_inv z := by
    funext j
    change z (finProdFinEquiv ((finProdFinEquiv.symm j).1, (finProdFinEquiv.symm j).2)) = z j
    rw [Prod.mk.eta, Equiv.apply_symm_apply]
def tupleCoordsCLE (b : ℕ) : (Fin b → ComplexVec4) ≃L[ℂ] Coordinates.ComplexCoordinates (b * 4) :=
  (tupleCoordsEquiv b).toContinuousLinearEquiv
theorem coordsToTuple_tupleCoordsCLE {b : ℕ} (ζ : Fin b → ComplexVec4) :
    coordsToTuple (tupleCoordsCLE b ζ) = ζ :=
  (tupleCoordsEquiv b).left_inv ζ
theorem isHolomorphicIn_of_differentiableAt {N : ℕ} {O : Set (Coordinates.ComplexCoordinates N)}
    {g : Coordinates.ComplexCoordinates N → ℂ} (hO : IsOpen O)
    (hg : ∀ z ∈ O, DifferentiableAt ℂ g z) :
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => g z := by apply _root_.YangMills.DeltaSharedProofs.p502090 <;> assumption
theorem isOpen_tube_and_differentiableAt
    (hmx : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties) {b : ℕ}
    {w : (Fin b → ComplexVec4) → ℂ} (hw : IsHolomorphicOnTube (m := b) w) :
    IsOpen (tubeTuples b) ∧ ∀ ζ ∈ tubeTuples b, DifferentiableAt ℂ w ζ := by
  obtain ⟨-, -, hL, -, -⟩ := (hmx.1 (b * 4) _ hw.1).1 1 _ hw
  have hO : IsOpen (tubeTuples b) := by
    have : tubeTuples b = tupleCoordsCLE b ⁻¹' (coordsToTuple ⁻¹' tubeTuples b) := by
      ext ζ
      simp [coordsToTuple_tupleCoordsCLE]
    rw [this]
    exact hw.1.preimage (tupleCoordsCLE b).continuous
  have hw' : w = (fun z : Coordinates.ComplexCoordinates (b * 4) => w (coordsToTuple z)) ∘
      tupleCoordsCLE b := by
    funext ζ
    simp [coordsToTuple_tupleCoordsCLE]
  refine ⟨hO, ?_⟩
  intro ζ hζ
  have hmem : tupleCoordsCLE b ζ ∈ coordsToTuple ⁻¹' tubeTuples b := by
    simpa [coordsToTuple_tupleCoordsCLE] using hζ
  obtain ⟨L, hLz⟩ := hL _ hmem
  have h1 := (hasFDerivAt_of_restrictScalars ℝ hLz rfl).differentiableAt
  have h2 := differentiableAt_pi.1 h1 0
  rw [hw']
  exact DifferentiableAt.comp ζ h2 (tupleCoordsCLE b).differentiableAt
def wickTupleCLE (b : ℕ) : (Fin b → ComplexVec4) ≃L[ℂ] (Fin b → ComplexVec4) :=
  (LinearEquiv.piCongrRight fun _ : Fin b => wickMap).toContinuousLinearEquiv
theorem eq_zero_on_tube_of_eq_zero_at_wick
    (hid : ComplexAnalysis.IdentityTheoremsProdAndUpperHalfPlane)
    (hconv : ConeTubeLorentz.ConesTubeConvex)
    (hι : ∀ x : RealVec4, wickMap (toComplex x) ∈ futureTube ↔ x 3 > 0)
    {b : ℕ} (hb : 1 ≤ b) (hO : IsOpen (tubeTuples b)) {F : (Fin b → ComplexVec4) → ℂ}
    (hF : ∀ ζ ∈ tubeTuples b, DifferentiableAt ℂ F ζ)
    (h0 : ∀ y : Fin b → RealVec4, (∀ k, 0 < y k 3) →
      F (fun k => wickMap (toComplex (y k))) = 0) :
    ∀ ζ ∈ tubeTuples b, F ζ = 0 := by
  classical
  let J : Coordinates.ComplexCoordinates (b * 4) ≃L[ℂ] (Fin b → ComplexVec4) :=
    (tupleCoordsCLE b).symm.trans (wickTupleCLE b)
  let 𝔘 : Set (Coordinates.ComplexCoordinates (b * 4) × Coordinates.ComplexCoordinates 0) :=
    {p | J p.1 ∈ tubeTuples b}
  let u : Coordinates.ComplexCoordinates (b * 4) × Coordinates.ComplexCoordinates 0 → ℂ :=
    fun p => F (J p.1)
  let y₀ : Fin b → RealVec4 := fun _ => ![0, 0, 0, 1]
  let ζ₀ : Fin b → ComplexVec4 := fun k => wickMap (toComplex (y₀ k))
  have hy₀ : ∀ k, 0 < y₀ k 3 := by
    intro k
    simp [y₀]
  have hζ₀ : ζ₀ ∈ tubeTuples b := fun k _ => (hι _).2 (hy₀ k)
  have h𝔘o : IsOpen 𝔘 := hO.preimage (J.continuous.comp continuous_fst)
  have h𝔘c : IsConnected 𝔘 := by
    have himg : 𝔘 = (fun ζ => (J.symm ζ, (0 : Coordinates.ComplexCoordinates 0))) ''
        tubeTuples b := by
      ext p
      constructor
      · intro hp
        refine ⟨J p.1, hp, ?_⟩
        refine Prod.ext (by simp) (Subsingleton.elim _ _)
      · rintro ⟨ζ, hζ, rfl⟩
        simpa [𝔘] using hζ
    rw [himg]
    have hcv : Convex ℝ (tubeTuples b) := hconv.2.2.2.2.2.2 b
    have hcont : Continuous fun ζ : Fin b → ComplexVec4 =>
        (J.symm ζ, (0 : Coordinates.ComplexCoordinates 0)) :=
      J.symm.continuous.prodMk continuous_const
    exact IsConnected.image ⟨⟨ζ₀, hζ₀⟩, hcv.isPreconnected⟩ _ hcont.continuousOn
  let S : Coordinates.ComplexCoordinates (b * 4 + 0) →L[ℂ] Coordinates.ComplexCoordinates (b * 4) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Fin.castAdd 0 i)
  have hP : ∀ z : Coordinates.ComplexCoordinates (b * 4 + 0),
      ((ComplexManifolds.coordinatesProdHomeomorph (b * 4) 0).symm z).1 = S z := by
    intro z
    rfl
  have hu : ComplexAnalysis.HolomorphicOnCoordinatesProd 𝔘 u := by
    refine isHolomorphicIn_of_differentiableAt
      (g := fun z => u ((ComplexManifolds.coordinatesProdHomeomorph (b * 4) 0).symm z))
      ((ComplexManifolds.coordinatesProdHomeomorph (b * 4) 0).isOpen_image.2 h𝔘o) ?_
    rintro z ⟨p, hp, rfl⟩
    have hfun : (fun z => u ((ComplexManifolds.coordinatesProdHomeomorph (b * 4) 0).symm z)) =
        fun z => F (J (S z)) := by
      funext z
      simp only [u, hP]
    rw [hfun]
    have hSp : S (ComplexManifolds.coordinatesProdHomeomorph (b * 4) 0 p) = p.1 := by
      rw [← hP]
      simp
    have h1 : DifferentiableAt ℂ F
        (J (S (ComplexManifolds.coordinatesProdHomeomorph (b * 4) 0 p))) := by
      rw [hSp]
      exact hF _ hp
    have h2 : DifferentiableAt ℂ (fun z => J (S z))
        (ComplexManifolds.coordinatesProdHomeomorph (b * 4) 0 p) :=
      J.differentiableAt.comp _ S.differentiableAt
    exact DifferentiableAt.comp _ h1 h2
  let 𝔵₀ : Coordinates.ComplexCoordinates (b * 4) := tupleCoordsCLE b fun k => toComplex (y₀ k)
  have hJ₀ : J 𝔵₀ = ζ₀ := by
    funext k
    change wickMap (coordsToTuple (tupleCoordsCLE b _) k) = _
    rw [coordsToTuple_tupleCoordsCLE]
  have hmem₀ : (𝔵₀, (0 : Coordinates.ComplexCoordinates 0)) ∈ 𝔘 := by
    change J 𝔵₀ ∈ tubeTuples b
    rw [hJ₀]
    exact hζ₀
  have hreal₀ : 𝔵₀ ∈ Coordinates.ComplexCoordinates.realLocus (b * 4) := by
    intro j
    change (toComplex _ _).im = 0
    simp [toComplex]
  have hev : ∀ᶠ p : Coordinates.ComplexCoordinates (b * 4) × Coordinates.ComplexCoordinates 0 in
      𝓝 (𝔵₀, (0 : Coordinates.ComplexCoordinates 0)), ∀ k, 0 < (coordsToTuple p.1 k 3).re := by
    refine Filter.eventually_all.2 fun k => ?_
    have hc : Continuous fun p : Coordinates.ComplexCoordinates (b * 4) ×
        Coordinates.ComplexCoordinates 0 => (coordsToTuple p.1 k 3).re := by
      unfold WightmanTheory.coordsToTuple
      fun_prop
    have hpos : 0 < (coordsToTuple (𝔵₀, (0 : Coordinates.ComplexCoordinates 0)).1 k 3).re := by
      change 0 < (coordsToTuple (tupleCoordsCLE b _) k 3).re
      rw [coordsToTuple_tupleCoordsCLE]
      simpa [toComplex] using hy₀ k
    exact (hc.tendsto _).eventually (lt_mem_nhds hpos)
  have hnear : ∀ᶠ p in 𝓝 (𝔵₀, (0 : Coordinates.ComplexCoordinates 0)),
      p.1 ∈ Coordinates.ComplexCoordinates.realLocus (b * 4) → u p = 0 := by
    filter_upwards [hev] with p hp hreal
    let y : Fin b → RealVec4 := fun k μ => (coordsToTuple p.1 k μ).re
    have hty : coordsToTuple p.1 = fun k => toComplex (y k) := by
      funext k μ
      refine Complex.ext ?_ ?_
      · simp [y, toComplex]
      · simpa [toComplex, WightmanTheory.coordsToTuple] using hreal (finProdFinEquiv (k, μ))
    have hJp : J p.1 = fun k => wickMap (toComplex (y k)) := by
      funext k
      change wickMap (coordsToTuple p.1 k) = _
      rw [hty]
    change F (J p.1) = 0
    rw [hJp]
    exact h0 y hp
  intro ζ hζ
  have := hid.1 (b * 4) 0 (by omega) 𝔘 u 𝔵₀ 0 h𝔘o h𝔘c hu hmem₀ hreal₀ hnear
    (J.symm ζ, 0) (by simpa [𝔘] using hζ)
  simpa [u] using this
theorem diffCoords_wickMapTuple {n : ℕ} (z : Fin (n + 1) → ComplexVec4) :
    MinkowskiSpace.diffCoords (wickMapTuple z) = wickMapTuple (MinkowskiSpace.diffCoords z) := by
  funext k
  refine Fin.cases ?_ (fun i => ?_) k
  · simp [MinkowskiSpace.diffCoords, wickMapTuple]
  · simp [MinkowskiSpace.diffCoords, successiveDiffs, wickMapTuple, map_sub]
theorem diffCoords_wick_mem_tube
    (hι : ∀ x : RealVec4, wickMap (toComplex x) ∈ futureTube ↔ x 3 > 0)
    {n : ℕ} {x : PointTuple (n + 1)} (hx : x ∈ increasingPositiveTimes (n + 1)) :
    MinkowskiSpace.diffCoords (wickMapTuple (tupleToComplex x)) ∈ tubeTuples (n + 1) := by
  intro k _
  rw [diffCoords_wickMapTuple]
  refine Fin.cases ?_ (fun i => ?_) k
  · have h0 : 0 < x 0 3 := hx.2 (Nat.succ_pos n)
    exact (hι (x 0)).2 h0
  · have hlt : x i.castSucc 3 < x i.succ 3 := hx.1 (Fin.castSucc_lt_succ)
    have he : wickMapTuple (MinkowskiSpace.diffCoords (tupleToComplex x)) i.succ =
        wickMap (toComplex (x i.succ - x i.castSucc)) := by
      have : toComplex (x i.succ - x i.castSucc) =
          toComplex (x i.succ) - toComplex (x i.castSucc) := by
        funext μ
        simp [toComplex]
      rw [this]
      simp [wickMapTuple, MinkowskiSpace.diffCoords, successiveDiffs, tupleToComplex]
    rw [he]
    refine (hι _).2 ?_
    simpa using hlt
theorem cumulativeSums_mem_increasingPositiveTimes {n : ℕ} {y : PointTuple (n + 1)}
    (hy : ∀ k, 0 < y k 3) : cumulativeSums y ∈ increasingPositiveTimes (n + 1) := by
  have hval : ∀ k, cumulativeSums y k 3 = ∑ j ∈ Finset.Iic k, y j 3 := by
    intro k
    simp [cumulativeSums, Finset.sum_apply]
  refine ⟨?_, ?_⟩
  · intro i j hij
    change cumulativeSums y i 3 < cumulativeSums y j 3
    rw [hval, hval]
    refine Finset.sum_lt_sum_of_subset (i := j) ?_ (by simp) (by simpa using hij) (hy j)
      (fun l _ _ => (hy l).le)
    exact Finset.Iic_subset_Iic.2 hij.le
  · intro h
    change 0 < cumulativeSums y ⟨0, h⟩ 3
    rw [hval]
    exact Finset.sum_pos (fun l _ => hy l) ⟨⟨0, h⟩, by simp⟩
theorem closedLinSpan_subset_of_subset {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] {S T : Set K} (h : S ⊆ SesquilinearForms.closedLinSpan T) :
    SesquilinearForms.closedLinSpan S ⊆ SesquilinearForms.closedLinSpan T := by
  have hT : SesquilinearForms.closedLinSpan T =
      ((Submodule.span ℂ T).topologicalClosure : Set K) := by
    unfold SesquilinearForms.closedLinSpan
    rw [seqClosureOf_eq_closure, Submodule.topologicalClosure_coe]
  have hs : Submodule.span ℂ S ≤ (Submodule.span ℂ T).topologicalClosure :=
    Submodule.span_le.2 (by rw [← hT]; exact h)
  unfold SesquilinearForms.closedLinSpan at hT ⊢
  rw [hT, seqClosureOf_eq_closure]
  exact closure_minimal hs (Submodule.isClosed_topologicalClosure _)
theorem abs_apply_le_euclidNormVec (v : Fin 4 → ℝ) (μ : Fin 4) :
    |v μ| ≤ TorusMetric.euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
theorem scaledMollifier_nonneg (hj : IsStandardMollifier stdMollifier) {ε : ℝ} (hε : 0 < ε)
    (x : Fin 4 → ℝ) : 0 ≤ scaledMollifier ε x := by
  unfold scaledMollifier
  exact mul_nonneg (by positivity) (hj.2.1 _)
theorem contDiff_scaledMollifier (hj : IsStandardMollifier stdMollifier) (ε : ℝ) :
    ContDiff ℝ ∞ (scaledMollifier ε) := by
  have h : ContDiff ℝ ∞ stdMollifier := hj.1.1
  change ContDiff ℝ ∞ fun x => ε ^ (-4 : ℤ) * stdMollifier (ε⁻¹ • x)
  have hs : ContDiff ℝ ∞ fun x : Fin 4 → ℝ => ε⁻¹ • x := contDiff_id.const_smul ε⁻¹
  exact contDiff_const.mul (h.comp hs)
theorem integral_scaledMollifier (hj : IsStandardMollifier stdMollifier) {ε : ℝ} (hε : 0 < ε) :
    ∫ x, scaledMollifier ε x = 1 := by
  have h1 : ∫ x, stdMollifier x = 1 := hj.2.2.1
  change ∫ x, ε ^ (-4 : ℤ) * stdMollifier (ε⁻¹ • x) = 1
  rw [integral_const_mul, Measure.integral_comp_inv_smul, h1]
  have hf : Module.finrank ℝ (Fin 4 → ℝ) = 4 := by simp
  rw [hf, abs_of_pos (by positivity)]
  simp only [smul_eq_mul, mul_one]
  rw [zpow_neg]
  have : ε ^ (4 : ℤ) = ε ^ 4 := by norm_cast
  rw [this]
  exact inv_mul_cancel₀ (by positivity)
theorem abs_apply_lt_of_scaledMollifier_ne_zero (hj : IsStandardMollifier stdMollifier) {ε : ℝ}
    (hε : 0 < ε) {v : Fin 4 → ℝ} (h : scaledMollifier ε v ≠ 0) (μ : Fin 4) : |v μ| < ε := by
  have h1 : stdMollifier (ε⁻¹ • v) ≠ 0 := fun h0 => h (by simp [scaledMollifier, h0])
  have h2 : TorusMetric.euclidNormVec (ε⁻¹ • v) < 1 := by
    by_contra hc
    exact h1 (hj.2.2.2.1 _ (not_lt.1 hc))
  have h3 := (abs_apply_le_euclidNormVec (ε⁻¹ • v) μ).trans_lt h2
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hε] at h3
  rwa [inv_mul_lt_iff₀ hε, mul_one] at h3
def diffMollifier (n : ℕ) (ε : ℝ) (x : PointTuple (n + 1)) : ℝ :=
  tensorMollifier ε (n + 1) (cumulativeSums x)
theorem abs_apply_lt_two_mul_of_cumulativeSums {n : ℕ} {x : PointTuple (n + 1)} {ε : ℝ}
    (h : ∀ k μ, |cumulativeSums x k μ| < ε) (k : Fin (n + 1)) (μ : Fin 4) : |x k μ| < 2 * ε := by
  have hfl := congrFun (congrFun (diffCoords_cumulativeSums x) k) μ
  revert hfl
  refine Fin.cases ?_ (fun i => ?_) k
  · intro hfl
    have e : cumulativeSums x 0 μ = x 0 μ := by
      simpa [MinkowskiSpace.diffCoords, tupleToComplex, toComplex] using hfl
    rw [← e]
    have h1 := h 0 μ
    have h2 := abs_nonneg (cumulativeSums x 0 μ)
    linarith
  · intro hfl
    have e : cumulativeSums x i.succ μ - cumulativeSums x i.castSucc μ = x i.succ μ := by
      have e' : ((cumulativeSums x i.succ μ : ℝ) : ℂ) - (cumulativeSums x i.castSucc μ : ℝ) =
          (x i.succ μ : ℝ) := by
        simpa [MinkowskiSpace.diffCoords, successiveDiffs, tupleToComplex, toComplex] using hfl
      exact_mod_cast e'
    rw [← e]
    have h1 := abs_lt.1 (h i.succ μ)
    have h2 := abs_lt.1 (h i.castSucc μ)
    exact abs_lt.2 ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩
theorem tupleNorm_sq_lt {n : ℕ} {x : PointTuple (n + 1)} {δ : ℝ}
    (h : ∀ k μ, |x k μ| < δ) : tupleNorm x ^ 2 < ((n : ℝ) + 1) * 4 * δ ^ 2 := by
  have e : tupleNorm x ^ 2 = ∑ i, ∑ μ, x i μ ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
  rw [e]
  calc ∑ i, ∑ μ, x i μ ^ 2 < ∑ _i : Fin (n + 1), ∑ _μ : Fin 4, δ ^ 2 :=
        Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_univ _⟩ fun i _ =>
          Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_univ _⟩ fun μ _ =>
            sq_lt_sq' (abs_lt.1 (h i μ)).1 (abs_lt.1 (h i μ)).2
    _ = ((n : ℝ) + 1) * 4 * δ ^ 2 := by
        simp
        ring
theorem norm_le_tupleNorm {m : ℕ} (x : PointTuple m) : ‖x‖ ≤ tupleNorm x := by apply _root_.YangMills.SharedProofs.p25561 <;> assumption
def mollifierScale (n j : ℕ) : ℝ := 1 / (4 * ((n : ℝ) + 1) * (j : ℝ))
theorem mollifierScale_pos (n : ℕ) {j : ℕ} (hj : 0 < j) : 0 < mollifierScale n j := by
  unfold mollifierScale
  have : (0 : ℝ) < j := by exact_mod_cast hj
  positivity
theorem diffMollifier_eq_zero (hm : IsStandardMollifier stdMollifier) {n j : ℕ} (hj : 0 < j)
    {x : PointTuple (n + 1)} (hx : 1 / (j : ℝ) ≤ tupleNorm x) :
    diffMollifier n (mollifierScale n j) x = 0 := by
  by_contra hne
  have hne' : ∏ i, scaledMollifier (mollifierScale n j) (cumulativeSums x i) ≠ 0 := hne
  have hε := mollifierScale_pos n hj
  have hf : ∀ k, scaledMollifier (mollifierScale n j) (cumulativeSums x k) ≠ 0 := fun k =>
    Finset.prod_ne_zero_iff.1 hne' k (Finset.mem_univ k)
  have hc : ∀ k μ, |cumulativeSums x k μ| < mollifierScale n j := fun k μ =>
    abs_apply_lt_of_scaledMollifier_ne_zero hm hε (hf k) μ
  have hn := tupleNorm_sq_lt (abs_apply_lt_two_mul_of_cumulativeSums hc)
  have hsq : (1 / (j : ℝ)) ^ 2 ≤ tupleNorm x ^ 2 :=
    pow_le_pow_left₀ (by positivity) hx 2
  have hm1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have he : ((n : ℝ) + 1) * 4 * (2 * mollifierScale n j) ^ 2 =
      (1 / (j : ℝ)) ^ 2 * (1 / ((n : ℝ) + 1)) := by
    unfold mollifierScale
    field_simp
    ring
  have hle : (1 / ((n : ℝ) + 1)) ≤ 1 := by
    rw [div_le_one (by linarith)]
    exact hm1
  have : (1 / (j : ℝ)) ^ 2 * (1 / ((n : ℝ) + 1)) ≤ (1 / (j : ℝ)) ^ 2 :=
    mul_le_of_le_one_right (by positivity) hle
  linarith
theorem contDiff_diffMollifier (hm : IsStandardMollifier stdMollifier) (n : ℕ) (ε : ℝ) :
    ContDiff ℝ ∞ (diffMollifier n ε) := by
  have hps : ∀ i, ContDiff ℝ ∞ (fun x : PointTuple (n + 1) => cumulativeSums x i) := by
    intro i
    unfold cumulativeSums
    exact ContDiff.sum fun l _ =>
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => Fin 4 → ℝ) l).contDiff
  change ContDiff ℝ ∞ fun x => ∏ i, scaledMollifier ε (cumulativeSums x i)
  exact contDiff_prod fun i _ => (contDiff_scaledMollifier hm ε).comp (hps i)
theorem integral_diffMollifier (hm : IsStandardMollifier stdMollifier) {n : ℕ}
    (hmp : MeasurePreserving (cumulativeSums : PointTuple (n + 1) → PointTuple (n + 1))
      volume volume)
    {ε : ℝ} (hε : 0 < ε) : ∫ x, diffMollifier n ε x = 1 := by
  have hc : Continuous (tensorMollifier ε (n + 1)) := by
    change Continuous fun x : PointTuple (n + 1) => ∏ i, scaledMollifier ε (x i)
    exact continuous_finsetProd _ fun i _ =>
      (contDiff_scaledMollifier hm ε).continuous.comp (continuous_apply i)
  have h := integral_map (μ := volume) hmp.aemeasurable hc.aestronglyMeasurable
  rw [hmp.map_eq] at h
  change ∫ x, tensorMollifier ε (n + 1) (cumulativeSums x) = 1
  rw [← h]
  change ∫ x : Fin (n + 1) → Fin 4 → ℝ, ∏ i, scaledMollifier ε (x i) = 1
  rw [integral_fintype_prod_volume_eq_pow, integral_scaledMollifier hm hε, one_pow]
def shiftedMollifier (ε : ℝ) (c v : Fin 4 → ℝ) : ℂ := ((scaledMollifier ε (v - c) : ℝ) : ℂ)
theorem shiftedMollifier_mem_schwartzR4 (hm : IsStandardMollifier stdMollifier)
    (hff : TestSpaces.Elementary.BasicProperties) {ε : ℝ} (hε : 0 < ε) (c : Fin 4 → ℝ) :
    shiftedMollifier ε c ∈ WightmanTheory.schwartzR4 := by
  have hsm : ContDiff ℝ ∞ (shiftedMollifier ε c) :=
    Complex.ofRealCLM.contDiff.comp
      ((contDiff_scaledMollifier hm ε).comp (contDiff_id.sub contDiff_const))
  have hcs₀ : HasCompactSupport stdMollifier := hm.1.2.1
  let hh : (Fin 4 → ℝ) ≃ₜ (Fin 4 → ℝ) :=
    (Homeomorph.subRight c).trans (Homeomorph.smulOfNeZero ε⁻¹ (inv_ne_zero hε.ne'))
  have h1 : HasCompactSupport (stdMollifier ∘ hh) :=
    hcs₀.comp_isClosedEmbedding hh.isClosedEmbedding
  have h2 : HasCompactSupport ((fun _ : Fin 4 → ℝ => ε ^ (-4 : ℤ)) * (stdMollifier ∘ hh)) :=
    h1.mul_left
  have h3 := h2.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have hcs : HasCompactSupport (shiftedMollifier ε c) := h3
  have hmem : WightmanTheory.asOnePointFn (shiftedMollifier ε c) ∈
      (smoothCompactSupp univ : Set (PointTuple 1 → ℂ)) := by
    change ContDiff ℝ ∞ _ ∧ HasCompactSupport _ ∧ tsupport _ ⊆ _
    refine ⟨hsm.comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => Fin 4 → ℝ) 0).contDiff,
      hcs.comp_isClosedEmbedding (Homeomorph.funUnique (Fin 1) (Fin 4 → ℝ)).isClosedEmbedding,
      subset_univ _⟩
  exact ((hff 1 one_pos).2.2.1 univ isOpen_univ _ hmem).1
theorem translateBy_diffMollifier {n : ℕ} (ε : ℝ) (a : PointTuple (n + 1)) :
    translateBy a (fun x => ((diffMollifier n ε x : ℝ) : ℂ)) =
      RealPointVectors.diffCoords
        (tensorVal fun α => shiftedMollifier ε (cumulativeSums a α)) := by
  funext x
  have hps : ∀ k, cumulativeSums (x - a) k = cumulativeSums x k - cumulativeSums a k := by
    intro k
    simp [cumulativeSums, Finset.sum_sub_distrib]
  change ((∏ k, scaledMollifier ε (cumulativeSums (x - a) k) : ℝ) : ℂ) =
    ∏ k, shiftedMollifier ε (cumulativeSums a k) (cumulativeSums x k)
  simp only [hps, shiftedMollifier]
  push_cast
  rfl
section Vectors
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (E : FourBorelSet → BddOp K) (Ω : K) (A : ℝ → BddOp K) (℘ C : ℝ)
theorem tubeMatrixElement_eq_zero_of_orthogonal_euclideanStates
    (hmat : TubeMatrixElements.Statement)
    (hid : ComplexAnalysis.IdentityTheoremsProdAndUpperHalfPlane)
    (hmx : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hconv : ConeTubeLorentz.ConesTubeConvex)
    (hι : ∀ x : RealVec4, wickMap (toComplex x) ∈ futureTube ↔ x 3 > 0)
    (hb : IsBoundedFieldForm E Ω A ℘ C) (χ : K)
    (hχ : ∀ v ∈ euclideanStates E Ω A, ⟪χ, v⟫_ℂ = 0) (n : ℕ) :
    ∀ ζ ∈ tubeTuples (n + 1), tubeMatrixElement E Ω A χ ζ = 0 := by
  obtain ⟨hhol, -, hval, -⟩ := hmat E Ω A ℘ C hb n χ
  obtain ⟨hO, hd⟩ := isOpen_tube_and_differentiableAt hmx hhol
  refine eq_zero_on_tube_of_eq_zero_at_wick hid hconv hι (Nat.succ_le_succ (Nat.zero_le n)) hO hd ?_
  intro y hy
  have hx := cumulativeSums_mem_increasingPositiveTimes (y := y) hy
  have h1 := hχ _ ⟨n + 1, cumulativeSums y, hx, rfl⟩
  rw [hval, diffCoords_wickMapTuple, diffCoords_cumulativeSums] at h1
  exact h1
theorem tubeMatrixElement_eq_zero_of_orthogonal_tensorStates
    (hmat : TubeMatrixElements.Statement)
    (hbdy : SmearedBoundaryVectors.Statement)
    (hun : TubeUniqueness.BoundaryValueDetermines)
    (hdiff : DifferenceVariables.SchwartzInDifferences)
    (hsch : RealPointVectors.SchwartzClosure)
    (hff : TestSpaces.Elementary.BasicProperties) (hm : IsStandardMollifier stdMollifier)
    (hb : IsBoundedFieldForm E Ω A ℘ C) (χ : K)
    (hχ : ∀ v ∈ tensorStates E Ω A, ⟪χ, v⟫_ℂ = 0) (n : ℕ) :
    ∀ ζ ∈ tubeTuples (n + 1), tubeMatrixElement E Ω A χ ζ = 0 := by
  obtain ⟨hhol, hbd, -, -⟩ := hmat E Ω A ℘ C hb n χ
  refine hun (n + 1) (ceilExponent ℘ (n + 1)).toNat
    (‖χ‖ * ((2 : ℝ) ^ ℘ * C) ^ (n + 1)) (tubeMatrixElement E Ω A χ)
    (fun j => diffMollifier n (mollifierScale n j)) (Nat.succ_pos n) hhol hbd ?_ ?_ ?_ ?_ ?_
  · intro j hj
    change ContDiff ℝ ∞ _ ∧ HasCompactSupport _ ∧ tsupport _ ⊆ _
    refine ⟨contDiff_diffMollifier hm n _, ?_, subset_univ _⟩
    refine HasCompactSupport.intro (isCompact_closedBall (0 : PointTuple (n + 1)) (1 / (j : ℝ))) ?_
    intro x hx
    refine diffMollifier_eq_zero hm hj ?_
    have h1 : 1 / (j : ℝ) < ‖x‖ := by simpa using hx
    exact h1.le.trans (norm_le_tupleNorm x)
  · intro j hj x
    change 0 ≤ ∏ i, scaledMollifier (mollifierScale n j) (cumulativeSums x i)
    exact Finset.prod_nonneg fun i _ => scaledMollifier_nonneg hm (mollifierScale_pos n hj) _
  · intro j hj
    exact integral_diffMollifier hm (hdiff n).1 (mollifierScale_pos n hj)
  · intro j hj x hx
    exact diffMollifier_eq_zero hm hj hx
  · intro j hj a
    rw [translateBy_diffMollifier]
    have hfS : ∀ α, shiftedMollifier (mollifierScale n j) (cumulativeSums a α) ∈
        WightmanTheory.schwartzR4 := fun α =>
      shiftedMollifier_mem_schwartzR4 hm hff (mollifierScale_pos n hj) _
    have hφ := hsch.2.2.2 (n + 1) _ hfS
    have h1 := (hbdy E Ω A ℘ C hb).inner_testState_eq_boundaryValue n _ hφ χ
    rw [← h1]
    exact hχ _ ⟨n + 1, _, hfS, rfl⟩
theorem nhdsWithin_futureConeTuples_neBot
    (hconv : ConeTubeLorentz.ConesTubeConvex) (n : ℕ) :
    (𝓝[futureConeTuples (n + 1)] (0 : PointTuple (n + 1))).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot]
  let e : PointTuple (n + 1) := fun _ => timeUnit
  have he : timeUnit ∈ futureCone := by
    change coneGap timeUnit > 0
    simp [coneGap, timeUnit, mkTimeSpace, spacePart, spaceNorm]
  have hmem : ∀ t : ℝ, 0 < t → t • e ∈ futureConeTuples (n + 1) := fun t ht _ =>
    hconv.2.1 t ht _ he
  have hlim : Tendsto (fun k : ℕ => (1 / ((k : ℝ) + 1)) • e) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const e
    simpa using this
  exact mem_closure_of_tendsto hlim (Eventually.of_forall fun k => hmem _ (by positivity))
theorem inner_testState_eq_zero_of_tube
    (hmat : TubeMatrixElements.Statement)
    (hbdy : SmearedBoundaryVectors.Statement)
    (hconv : ConeTubeLorentz.ConesTubeConvex)
    (hb : IsBoundedFieldForm E Ω A ℘ C) (χ : K) (n : ℕ)
    (hu : ∀ ζ ∈ tubeTuples (n + 1), tubeMatrixElement E Ω A χ ζ = 0)
    (φ : PointTuple (n + 1) → ℂ) (hφ : φ ∈ schwartzSet (n + 1)) :
    ⟪χ, testState E Ω A (n + 1) φ⟫_ℂ = 0 := by
  have hlim := (hbdy E Ω A ℘ C hb).isBoundaryLimit_testState n φ hφ χ
  have h0 : ∀ Y ∈ futureConeTuples (n + 1), ⟪χ, smearedState E Ω A Y φ⟫_ℂ = 0 := by
    intro Y hY
    rw [((hmat E Ω A ℘ C hb n χ).2.2.2 Y hY φ hφ).2]
    unfold pairing
    have hz : shiftedIntegrand (tubeMatrixElement E Ω A χ) Y (RealPointVectors.diffCoords φ) = 0 := by
      funext x
      have ht : tubePoint x Y ∈ tubeTuples (n + 1) := by
        intro k _
        change MinkowskiSpace.imPart (tubePoint x Y k) ∈ futureCone
        have e : MinkowskiSpace.imPart (tubePoint x Y k) = Y k := by
          funext μ
          simp [MinkowskiSpace.imPart, tubePoint, toComplex]
        rw [e]
        exact hY k
      simp only [shiftedIntegrand, Pi.zero_apply]
      rw [hu _ ht, zero_mul]
    rw [hz]
    simp
  have := nhdsWithin_futureConeTuples_neBot hconv n
  have hev : (fun Y => ⟪χ, smearedState E Ω A Y φ⟫_ℂ) =ᶠ[𝓝[futureConeTuples (n + 1)] 0]
      fun _ => (0 : ℂ) :=
    Filter.eventually_of_mem self_mem_nhdsWithin h0
  exact tendsto_nhds_unique (hlim.congr' hev) tendsto_const_nhds
end Vectors
theorem statement_holds
    (hmat : TubeMatrixElements.Statement)
    (hbdy : SmearedBoundaryVectors.Statement)
    (hid : ComplexAnalysis.IdentityTheoremsProdAndUpperHalfPlane)
    (hmx : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hcone : MinkowskiSpace.ConeTubeLorentz.Statement)
    (hdec : HilbertToolkit.HilbertCompletionExtensionRiesz)
    (hun : TubeUniqueness.BoundaryValueDetermines)
    (hdiff : DifferenceVariables.SchwartzInDifferences)
    (hsch : RealPointVectors.SchwartzClosure)
    (hff : TestSpaces.Elementary.BasicProperties)
    (hsm : WightmanReconstruction.SmoothToolkit.Toolkit) :
    RealPointVectors.TensorClosure.Statement := by
  intro K _ _ _ E Ω A ℘ C hb
  have hconv := hcone.2.1
  have hι := hcone.2.2.2.1.2.2.2.2.2.1
  have hm : IsStandardMollifier stdMollifier := isStandardMollifier_stdMollifier hsm.1
  have hspan : ∀ (Z : Set K) (v : K), (∀ χ : K, (∀ ψ ∈ Z, ⟪χ, ψ⟫_ℂ = 0) → ⟪χ, v⟫_ℂ = 0) →
      v ∈ SesquilinearForms.closedLinSpan Z := by
    intro Z v hv
    refine ((hdec.2.2.1 K).2 Z).1 v fun χ' hχ' => ?_
    change ⟪v, χ'⟫_ℂ = 0
    rw [← inner_conj_symm, hv χ' hχ', map_zero]
  let V := euclideanStates E Ω A
  have hHE : tensorDomainClosure E Ω A =
      SesquilinearForms.closedLinSpan (tensorStates E Ω A) := rfl
  have hΩ : Ω ∈ V := by
    refine ⟨0, fun i => i.elim0, ⟨fun i => i.elim0, fun h => absurd h (lt_irrefl 0)⟩, rfl⟩
  have hvec : ∀ (n : ℕ) (φ : Motions.TensorVal ℂ n), φ ∈ schwartzOfOrder n →
      testState E Ω A n φ ∈ SesquilinearForms.closedLinSpan V := by
    intro n φ hφ
    refine hspan V _ fun χ hχ => ?_
    cases n with
    | zero =>
      change ⟪χ, scalarOfOrderZero φ • Ω⟫_ℂ = 0
      rw [inner_smul_right, hχ Ω hΩ, mul_zero]
    | succ n =>
      exact inner_testState_eq_zero_of_tube E Ω A ℘ C hmat hbdy hconv hb χ n
        (tubeMatrixElement_eq_zero_of_orthogonal_euclideanStates E Ω A ℘ C hmat hid hmx hconv hι
          hb χ hχ n) φ hφ
  have hT : tensorStates E Ω A ⊆ SesquilinearForms.closedLinSpan V := by
    rintro v ⟨n, f, hf, rfl⟩
    exact hvec n _ (hsch.2.2.2 n f hf)
  have hV : V ⊆ SesquilinearForms.closedLinSpan (tensorStates E Ω A) := by
    rintro v ⟨m, x, hx, rfl⟩
    refine hspan _ _ fun χ hχ => ?_
    cases m with
    | zero =>
      let f₀ : Fin 0 → (Fin 4 → ℝ) → ℂ := fun i => i.elim0
      have h1 : testState E Ω A 0 (tensorVal f₀) = Ω := by
        change scalarOfOrderZero (tensorVal f₀) • Ω = Ω
        have : scalarOfOrderZero (tensorVal f₀) = 1 := by
          change ∏ i : Fin 0, f₀ i ((default : PointTuple 0) i) = 1
          simp
        rw [this, one_smul]
      have h2 := hχ _ ⟨0, f₀, (fun i => i.elim0), rfl⟩
      rw [h1] at h2
      exact h2
    | succ n =>
      rw [((hmat E Ω A ℘ C hb n χ).2.2.1)]
      exact tubeMatrixElement_eq_zero_of_orthogonal_tensorStates E Ω A ℘ C hmat hbdy hun hdiff hsch
        hff hm hb χ hχ n _ (diffCoords_wick_mem_tube hι hx)
  have heq : tensorDomainClosure E Ω A = SesquilinearForms.closedLinSpan V := by
    rw [hHE]
    exact Subset.antisymm (closedLinSpan_subset_of_subset hT) (closedLinSpan_subset_of_subset hV)
  refine ⟨heq, ?_, ?_⟩
  · intro n φ hφ
    rw [heq]
    exact hvec n φ hφ
  · intro n z hz
    rw [heq]
    refine hspan V _ fun χ hχ => ?_
    rw [((hmat E Ω A ℘ C hb n χ).2.2.1)]
    exact tubeMatrixElement_eq_zero_of_orthogonal_euclideanStates E Ω A ℘ C hmat hid hmx hconv hι
      hb χ hχ n _ fun k _ => hz k
end RealPointVectors.TensorClosure
end YangMills.Construction
