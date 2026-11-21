import Reconstruction.MinkowskiSpace.AcrossTheSpacelikePointsProof
import Reconstruction.MinkowskiSpace.ConeTubeAndLorentzGroupProof
import Reconstruction.MinkowskiSpace.EuclideanFormOfAnInvariantRepresentedSequenceProof
import Reconstruction.MinkowskiSpace.FormRepresentsItsFunctionalAndIsEuclideanProof
import Reconstruction.MinkowskiSpace.TranslationOperatorsOfABoundedFieldFormProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open TestSpaces Motions MinkowskiSpace Coordinates Filter Topology MeasureTheory Matrix
open scoped ContDiff ComplexConjugate
namespace FieldForms.EuclideanSchwinger
open ProjectionMeasures OneLoopNotation WightmanTheory WightmanReconstruction.SmoothToolkit
abbrev O4 : Type := Matrix.orthogonalGroup (Fin 4) ℝ
theorem rotatePermute_rotatePermute {q : ℕ} (R R' : O4) (s s' : Equiv.Perm (Fin q))
    (x : PointTuple q) :
    rotatePermute R' s' (rotatePermute R s x) =
      rotatePermute (R' * R) (s * s') x := by
  funext i
  simp [rotatePermute, Matrix.mulVec_mulVec]
theorem rotatePermute_one {q : ℕ} (x : PointTuple q) :
    rotatePermute (1 : O4) 1 x = x := by
  funext i
  simp [rotatePermute]
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {E : FourBorelSet → BddOp K} {Ω : K} {A : ℝ → BddOp K}
theorem orderedSchwinger_eq_of_mem (hE : IsEuclidean E Ω A) {m : ℕ} {x : PointTuple (m + 1)}
    {R R' : O4} {s s' : Equiv.Perm (Fin (m + 1))}
    (h : rotatePermute R s x ∈ increasingTimes (m + 1))
    (h' : rotatePermute R' s' x ∈ increasingTimes (m + 1)) :
    orderedSchwinger E Ω A m (rotatePermute R' s' x) =
      orderedSchwinger E Ω A m (rotatePermute R s x) := by
  have e : rotatePermute R' s' x =
      rotatePermute (R' * R⁻¹) (s⁻¹ * s') (rotatePermute R s x) := by
    rw [rotatePermute_rotatePermute]
    simp
  rw [e] at h' ⊢
  exact hE m _ h _ _ h'
theorem schwinger_eq_orderedSchwinger (hE : IsEuclidean E Ω A) {m : ℕ} {x : PointTuple (m + 1)}
    {R : O4} {s : Equiv.Perm (Fin (m + 1))}
    (h : rotatePermute R s x ∈ increasingTimes (m + 1)) :
    schwinger E Ω A m x =
      orderedSchwinger E Ω A m (rotatePermute R s x) := by
  have hex : ∃ p : O4 × Equiv.Perm (Fin (m + 1)),
      rotatePermute p.1 p.2 x ∈ increasingTimes (m + 1) := ⟨(R, s), h⟩
  rw [schwinger, dif_pos hex]
  exact orderedSchwinger_eq_of_mem hE h hex.choose_spec
theorem schwinger_eq_orderedSchwinger_of_mem (hE : IsEuclidean E Ω A) {m : ℕ}
    {x : PointTuple (m + 1)} (h : x ∈ increasingTimes (m + 1)) :
    schwinger E Ω A m x = orderedSchwinger E Ω A m x := by
  have h' : rotatePermute (1 : O4) 1 x ∈ increasingTimes (m + 1) := by
    rwa [rotatePermute_one]
  rw [schwinger_eq_orderedSchwinger hE h', rotatePermute_one]
theorem orthogonal_dotProduct_mulVec (R : O4) (u v : Fin 4 → ℝ) :
    ((R : Matrix (Fin 4) (Fin 4) ℝ) *ᵥ u) ⬝ᵥ ((R : Matrix (Fin 4) (Fin 4) ℝ) *ᵥ v) = u ⬝ᵥ v := by
  have h : (R : Matrix (Fin 4) (Fin 4) ℝ)ᵀ * (R : Matrix (Fin 4) (Fin 4) ℝ) = 1 :=
    mul_eq_one_comm.1 ((Matrix.mem_orthogonalGroup_iff (Fin 4) ℝ).1 R.2)
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, h,
    Matrix.one_mulVec]
theorem exists_rotatePermute_mem (ht : WightmanReconstruction.SmoothToolkit.Toolkit) {q : ℕ}
    {x : PointTuple q} (hx : x ∈ distinctLocus q) :
    ∃ (R : O4) (s : Equiv.Perm (Fin q)),
      (R : Matrix (Fin 4) (Fin 4) ℝ) ∈ Matrix.specialOrthogonalGroup (Fin 4) ℝ ∧
        rotatePermute R s x ∈ increasingTimes q := by
  classical
  have hinj : Function.Injective x := hx
  let I := {p : Fin q × Fin q // p.1 ≠ p.2}
  let eq := Fintype.equivFin I
  obtain ⟨e, he, hne⟩ := ht.2.2.2.2.2.2.1 (Fintype.card I)
    (fun l => x (eq.symm l).1.1 - x (eq.symm l).1.2)
    (fun l => sub_ne_zero.2 fun h => (eq.symm l).2 (hinj h))
  have he4 : IsUnitVec (Pi.single 3 1 : Fin 4 → ℝ) := by
    simp [IsUnitVec, vecLength]
  obtain ⟨R, hR, hRe⟩ := (ht.2.2.2.2.2.1 4 (Or.inr rfl)).2 e _ he he4
  have hRO : R ∈ Matrix.orthogonalGroup (Fin 4) ℝ :=
    (Matrix.mem_specialOrthogonalGroup_iff.1 hR).1
  let t : Fin q → ℝ := fun i => e ⬝ᵥ x i
  have htime : ∀ u : Fin 4 → ℝ, (R *ᵥ u) 3 = e ⬝ᵥ u := by
    intro u
    have h1 := orthogonal_dotProduct_mulVec ⟨R, hRO⟩ e u
    simp only at h1
    rw [hRe] at h1
    simpa using h1
  have htinj : Function.Injective t := by
    intro i k hik
    by_contra hne'
    have := hne (eq ⟨(i, k), hne'⟩)
    simp only [Equiv.symm_apply_apply] at this
    apply this
    rw [dotProduct_sub]
    exact sub_eq_zero.2 hik
  refine ⟨⟨R, hRO⟩, Tuple.sort t, hR, ?_⟩
  have hmono : StrictMono (t ∘ Tuple.sort t) :=
    (Tuple.monotone_sort t).strictMono_of_injective (htinj.comp (Tuple.sort t).injective)
  intro i k hik
  have := hmono hik
  simpa [timeCoord, rotatePermute, htime] using this
theorem wickDiffs_add_const {m : ℕ} (y : PointTuple (m + 1)) (w : Fin 4 → ℝ) :
    wickDiffs (fun i => y i + w) = wickDiffs y := by
  funext i μ
  fin_cases μ <;>
    simp [wickDiffs, successiveDiffs, wickMapTuple, tupleToComplex,
      wickMap, MinkowskiSpace.toComplex, mul_add]
theorem orderedSchwinger_add_const {m : ℕ} (y : PointTuple (m + 1)) (w : Fin 4 → ℝ) :
    orderedSchwinger E Ω A m (fun i => y i + w) = orderedSchwinger E Ω A m y := congrArg (vacuumExpectation E Ω A (m + 1)) (wickDiffs_add_const y w)
theorem schwinger_motion_perm (ht : WightmanReconstruction.SmoothToolkit.Toolkit)
    (hE : IsEuclidean E Ω A) {m : ℕ}
    (r : RigidMotion) (s : Equiv.Perm (Fin (m + 1))) {x : PointTuple (m + 1)}
    (hx : x ∈ distinctLocus (m + 1)) :
    schwinger E Ω A m (fun i => r.toFun (x (s i))) =
      schwinger E Ω A m x := by
  set x' : PointTuple (m + 1) := fun i => r.toFun (x (s i)) with hx'
  have hmapinj : Function.Injective r.toFun := fun u v h => by
    have := congrArg r.invFun h
    rwa [r.invFun_toFun, r.invFun_toFun] at this
  have hx'd : x' ∈ distinctLocus (m + 1) := fun i k h =>
    s.injective ((show Function.Injective x from hx) (hmapinj h))
  obtain ⟨R₀, s₀, -, h₀⟩ := exists_rotatePermute_mem ht hx'd
  let Rr : O4 := ⟨r.mat, r.mat_mem⟩
  let w : Fin 4 → ℝ := (R₀ : Matrix (Fin 4) (Fin 4) ℝ) *ᵥ r.shift
  have hy : rotatePermute R₀ s₀ x' =
      fun i => rotatePermute (R₀ * Rr) (s * s₀) x i + w := by
    funext i
    simp [rotatePermute, hx', RigidMotion.toFun, Matrix.mulVec_add, Matrix.mulVec_mulVec, w, Rr]
  have hord : rotatePermute (R₀ * Rr) (s * s₀) x ∈ increasingTimes (m + 1) := by
    intro i k hik
    have := h₀ hik
    rw [hy] at this
    simpa [timeCoord] using this
  rw [schwinger_eq_orderedSchwinger hE h₀, schwinger_eq_orderedSchwinger hE hord, hy,
    orderedSchwinger_add_const]
theorem conjPoint_apply (ζ : ComplexVec4) (μ : Fin 4) : conjPoint ζ μ = conj (ζ μ) := by apply _root_.YangMills.Construction.FieldFormTranslations.conjPoint_coord <;> assumption
theorem conjPoint_wickMap (u : Fin 4 → ℝ) :
    conjPoint (wickMap (MinkowskiSpace.toComplex u)) =
      wickMap (MinkowskiSpace.toComplex (timeReflect u)) := by apply _root_.YangMills.Construction.MinkowskiSpace.ConeTubeLorentz.conjPoint_wickMap_toComplex <;> assumption
def timeReflectO4 : O4 :=
  ⟨RigidMotion.timeReflection.mat, RigidMotion.timeReflection.mat_mem⟩
theorem timeReflectO4_mulVec (u : Fin 4 → ℝ) :
    (timeReflectO4 : Matrix (Fin 4) (Fin 4) ℝ) *ᵥ u = timeReflect u := by
  have := congrFun RigidMotion.timeReflection_toFun u
  change RigidMotion.timeReflection.mat *ᵥ u = _
  simpa [RigidMotion.toFun, (show RigidMotion.timeReflection.shift = 0 from rfl)] using this
theorem conj_orderedSchwinger (hc : ExpectationConj E Ω A) (hE : IsEuclidean E Ω A)
    {m : ℕ} {y : PointTuple (m + 1)} (hy : y ∈ increasingTimes (m + 1)) :
    conj (orderedSchwinger E Ω A m y) = orderedSchwinger E Ω A m y := by
  have hrev : rotatePermute timeReflectO4 Fin.revPerm y ∈ increasingTimes (m + 1) := by
    intro i k hik
    have : y (Fin.rev k) 3 < y (Fin.rev i) 3 := hy (Fin.rev_lt_rev.2 hik)
    simpa [timeCoord, rotatePermute, timeReflectO4_mulVec, timeReflect] using this
  have hd : reflectTuple (wickDiffs y) =
      wickDiffs (rotatePermute timeReflectO4 Fin.revPerm y) := by
    funext k
    have h₁ : wickDiffs (rotatePermute timeReflectO4 Fin.revPerm y) k =
        wickMap (MinkowskiSpace.toComplex (timeReflect (y (Fin.rev k).castSucc))) -
          wickMap (MinkowskiSpace.toComplex (timeReflect (y (Fin.rev k).succ))) := by
      simp [wickDiffs, successiveDiffs, wickMapTuple, tupleToComplex,
        rotatePermute, timeReflectO4_mulVec, Fin.rev_succ, Fin.rev_castSucc]
    rw [h₁, ← conjPoint_wickMap, ← conjPoint_wickMap]
    funext μ
    simp only [reflectTuple, wickDiffs, successiveDiffs, wickMapTuple,
      tupleToComplex, conjPoint_apply, Pi.neg_apply, Pi.sub_apply, map_sub]
    ring
  have hmem : wickDiffs y ∈ tubeTuples m := fun i _ =>
    wickDiffs_mem_futureTube hy i
  have h₂ := hc (m + 1) (wickDiffs y) hmem
  have h₃ := hE m y hy timeReflectO4 Fin.revPerm hrev
  rw [orderedSchwinger] at h₃ ⊢
  rw [orderedSchwinger] at h₃
  rw [h₂, ← h₃]
  exact congrArg _ hd
def tupleCoords {k : ℕ} (t : Fin k → ComplexVec4) : ComplexCoordinates (k * 4) :=
  fun j => t (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2
theorem coordsToTuple_tupleCoords {k : ℕ} (t : Fin k → ComplexVec4) :
    coordsToTuple (tupleCoords t) = t := by apply _root_.YangMills.Construction.FieldForms.SpacelikeExtension.coordsToTuple_tupleCoords <;> assumption
def rotDiffs {m : ℕ} (R : O4) (s : Equiv.Perm (Fin (m + 1)))
    (t : Fin (m + 1) → ComplexVec4) : Fin m → ComplexVec4 :=
  successiveDiffs (wickMapTuple
    fun i => toComplexMatrix (R : Matrix (Fin 4) (Fin 4) ℝ) *ᵥ t (s i))
theorem rotDiffs_tupleToComplex {m : ℕ} (R : O4)
    (s : Equiv.Perm (Fin (m + 1))) (x : PointTuple (m + 1)) :
    rotDiffs R s (tupleToComplex x) = wickDiffs (rotatePermute R s x) := by
  have h : ∀ i, toComplexMatrix (R : Matrix (Fin 4) (Fin 4) ℝ) *ᵥ tupleToComplex x (s i) =
      tupleToComplex (rotatePermute R s x) i := by
    intro i
    funext μ
    simp [toComplexMatrix, tupleToComplex, MinkowskiSpace.toComplex, rotatePermute,
      Matrix.mulVec, dotProduct]
  simp only [rotDiffs, wickDiffs, h]
def rotDiffsLinear {m : ℕ} (R : O4) (s : Equiv.Perm (Fin (m + 1))) :
    ComplexCoordinates ((m + 1) * 4) →ₗ[ℂ] ComplexCoordinates (m * 4) where
  toFun z := tupleCoords (rotDiffs R s (coordsToTuple z))
  map_add' z z' := by
    have h : ∀ i, coordsToTuple (z + z') i =
        coordsToTuple z i + coordsToTuple z' i := fun i => rfl
    funext j
    simp [tupleCoords, rotDiffs, successiveDiffs, wickMapTuple, h,
      Matrix.mulVec_add]
    ring
  map_smul' c z := by
    have h : ∀ i, coordsToTuple (c • z) i = c • coordsToTuple z i := fun i => rfl
    funext j
    simp [tupleCoords, rotDiffs, successiveDiffs, wickMapTuple, h,
      Matrix.mulVec_smul, mul_sub]
def continuation (E : FourBorelSet → BddOp K) (Ω : K) (A : ℝ → BddOp K)
    {m : ℕ} (R : O4) (s : Equiv.Perm (Fin (m + 1))) :
    ComplexCoordinates ((m + 1) * 4) → ComplexCoordinates 1 :=
  (fun z _ => vacuumExpectation E Ω A (m + 1) (coordsToTuple z)) ∘ rotDiffsLinear R s
def continuationDomain {m : ℕ} (R : O4) (s : Equiv.Perm (Fin (m + 1))) :
    Set (ComplexCoordinates ((m + 1) * 4)) :=
  rotDiffsLinear R s ⁻¹' (coordsToTuple ⁻¹' tubeTuples m)
theorem continuation_isHolomorphicIn
    (hmx : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {m : ℕ} (hw : IsHolomorphicOnTube (m := m) (vacuumExpectation E Ω A (m + 1)))
    (R : O4) (s : Equiv.Perm (Fin (m + 1))) :
    ComplexCoordinates.IsHolomorphicIn (continuationDomain R s) (continuation E Ω A R s) := by
  have hO := hw.1
  let L : ComplexCoordinates ((m + 1) * 4) →L[ℂ] ComplexCoordinates (m * 4) :=
    LinearMap.toContinuousLinearMap (rotDiffsLinear R s)
  have hg : ComplexCoordinates.IsHolomorphicIn (continuationDomain R s) (rotDiffsLinear R s) := by
    refine ⟨hO.preimage L.continuous, L.continuous.continuousOn, fun a _ j => ?_⟩
    refine Eventually.of_forall fun ζ => ?_
    have : DifferentiableAt ℂ
        (fun ζ : ℂ => L (a + ζ • ComplexCoordinates.stdBasisVector j)) ζ := by
      fun_prop
    exact this
  exact ((hmx.1 _ _ hO).1 1 _ hw).2.2.2.1 _ _ _ hg fun z hz => hz
def pointCoords {m : ℕ} (x : PointTuple (m + 1)) : ComplexCoordinates ((m + 1) * 4) :=
  tupleCoords (tupleToComplex x)
theorem continuous_pointCoords {m : ℕ} : Continuous (pointCoords (m := m)) := by
  refine continuous_pi fun j => ?_
  exact Complex.continuous_ofReal.comp ((continuous_apply _).comp (continuous_apply _))
theorem continuous_realPartPoint {m : ℕ} : Continuous (realPartPoint m) :=
  continuous_pi fun _ => continuous_pi fun _ => Complex.continuous_re.comp (continuous_apply _)
theorem continuous_rotatePermute {q : ℕ} (R : O4) (s : Equiv.Perm (Fin q)) :
    Continuous (rotatePermute R s) := by
  refine continuous_pi fun i => ?_
  exact (Continuous.matrix_mulVec continuous_const (continuous_apply (s i)))
theorem coordsToTuple_of_mem_realLocus {m : ℕ} {z : ComplexCoordinates ((m + 1) * 4)}
    (hz : z ∈ ComplexCoordinates.realLocus ((m + 1) * 4)) :
    coordsToTuple z = tupleToComplex (realPartPoint m z) := by
  funext i μ
  apply Complex.ext
  · simp [coordsToTuple, tupleToComplex, MinkowskiSpace.toComplex, realPartPoint]
  · simpa [coordsToTuple, tupleToComplex, MinkowskiSpace.toComplex] using hz _
theorem continuation_of_mem_realLocus {m : ℕ} (R : O4) (s : Equiv.Perm (Fin (m + 1)))
    {z : ComplexCoordinates ((m + 1) * 4)}
    (hz : z ∈ ComplexCoordinates.realLocus ((m + 1) * 4)) (k : Fin 1) :
    continuation E Ω A R s z k =
      orderedSchwinger E Ω A m (rotatePermute R s (realPartPoint m z)) := by
  simp only [continuation, Function.comp, orderedSchwinger]
  have : coordsToTuple (rotDiffsLinear R s z) =
      wickDiffs (rotatePermute R s (realPartPoint m z)) := by
    change coordsToTuple (tupleCoords (rotDiffs R s (coordsToTuple z))) = _
    rw [coordsToTuple_tupleCoords, coordsToTuple_of_mem_realLocus hz,
      rotDiffs_tupleToComplex]
  rw [this]
theorem pointCoords_mem_realLocus {m : ℕ} (x : PointTuple (m + 1)) :
    pointCoords x ∈ ComplexCoordinates.realLocus ((m + 1) * 4) := fun j => by
  simp [pointCoords, tupleCoords, tupleToComplex, MinkowskiSpace.toComplex]
theorem realPartPoint_pointCoords {m : ℕ} (x : PointTuple (m + 1)) :
    realPartPoint m (pointCoords x) = x := by
  funext i μ
  simp [realPartPoint, pointCoords, tupleCoords, tupleToComplex,
    MinkowskiSpace.toComplex]
theorem mem_continuationDomain {m : ℕ} {R : O4} {s : Equiv.Perm (Fin (m + 1))}
    {z : ComplexCoordinates ((m + 1) * 4)}
    (hz : z ∈ ComplexCoordinates.realLocus ((m + 1) * 4))
    (h : rotatePermute R s (realPartPoint m z) ∈ increasingTimes (m + 1)) :
    z ∈ continuationDomain R s := by
  change coordsToTuple (tupleCoords (rotDiffs R s (coordsToTuple z))) ∈ tubeTuples m
  rw [coordsToTuple_tupleCoords, coordsToTuple_of_mem_realLocus hz,
    rotDiffs_tupleToComplex]
  exact fun i _ => wickDiffs_mem_futureTube h i
theorem schwinger_isRealAnalyticIn (ht : WightmanReconstruction.SmoothToolkit.Toolkit)
    (hmx : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hE : IsEuclidean E Ω A) {m : ℕ}
    (hw : IsHolomorphicOnTube (m := m) (vacuumExpectation E Ω A (m + 1))) :
    ComplexCoordinates.IsRealAnalyticIn (N' := 1)
      {z | z ∈ ComplexCoordinates.realLocus ((m + 1) * 4) ∧
        realPartPoint m z ∈ distinctLocus (m + 1)}
      (fun z _ => schwinger E Ω A m (realPartPoint m z)) := by
  have hopen : IsOpen (distinctLocus (m + 1)) := ConfigSpace.isOpen_distinctArgs
  refine ⟨⟨realPartPoint m ⁻¹' distinctLocus (m + 1),
    hopen.preimage continuous_realPartPoint, ?_⟩, ?_⟩
  · ext z
    simp [and_comm]
  · rintro a ⟨har, had⟩
    obtain ⟨R, s, -, hRs⟩ := exists_rotatePermute_mem ht had
    have hG := continuation_isHolomorphicIn hmx hw R s
    obtain ⟨c, hc⟩ := ((hmx.1 _ _ hG.1).1 1 _ hG).2.2.2.2.2 a
      ⟨mem_continuationDomain har hRs, har⟩
    refine ⟨c, ?_⟩
    have hU : ∀ᶠ z in 𝓝 a,
        rotatePermute R s (realPartPoint m z) ∈ increasingTimes (m + 1) :=
      ((continuous_rotatePermute R s).comp continuous_realPartPoint).continuousAt.eventually
        ((isOpen_increasingTimes (m + 1)).mem_nhds hRs)
    filter_upwards [hc, nhdsWithin_le_nhds hU, self_mem_nhdsWithin] with z h₁ h₂ h₃
    convert h₁ using 1
    funext k
    rw [continuation_of_mem_realLocus R s h₃ k, schwinger_eq_orderedSchwinger hE h₂]
theorem schwinger_continuousOn (ht : WightmanReconstruction.SmoothToolkit.Toolkit)
    (hmx : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hE : IsEuclidean E Ω A) {m : ℕ}
    (hw : IsHolomorphicOnTube (m := m) (vacuumExpectation E Ω A (m + 1))) :
    ContinuousOn (schwinger E Ω A m) (distinctLocus (m + 1)) := by
  intro x hx
  obtain ⟨R, s, -, hRs⟩ := exists_rotatePermute_mem ht hx
  have hG := continuation_isHolomorphicIn hmx hw R s
  have hmem : pointCoords x ∈ continuationDomain R s :=
    mem_continuationDomain (pointCoords_mem_realLocus x)
      (by rwa [realPartPoint_pointCoords])
  have hc : ContinuousAt (continuation E Ω A R s) (pointCoords x) :=
    hG.2.1.continuousAt (hG.1.mem_nhds hmem)
  have hc' : ContinuousAt (fun y : PointTuple (m + 1) => continuation E Ω A R s
      (pointCoords y) 0) x :=
    ((continuous_apply (0 : Fin 1)).continuousAt).comp
      (ContinuousAt.comp (f := pointCoords) hc continuous_pointCoords.continuousAt)
  refine ContinuousAt.continuousWithinAt (hc'.congr ?_)
  have hU : ∀ᶠ y in 𝓝 x, rotatePermute R s y ∈ increasingTimes (m + 1) :=
    (continuous_rotatePermute R s).continuousAt.eventually
      ((isOpen_increasingTimes (m + 1)).mem_nhds hRs)
  filter_upwards [hU] with y hy
  rw [continuation_of_mem_realLocus R s (pointCoords_mem_realLocus y), realPartPoint_pointCoords,
    schwinger_eq_orderedSchwinger hE hy]
def rotatePermuteHomeomorph {q : ℕ} (R : O4) (s : Equiv.Perm (Fin q)) :
    PointTuple q ≃ₜ PointTuple q where
  toFun := rotatePermute R s
  invFun := rotatePermute R⁻¹ s⁻¹
  left_inv x := by
    rw [rotatePermute_rotatePermute]
    simpa using rotatePermute_one x
  right_inv x := by
    rw [rotatePermute_rotatePermute]
    simpa using rotatePermute_one x
  continuous_toFun := continuous_rotatePermute R s
  continuous_invFun := continuous_rotatePermute _ _
theorem rotatePermuteHomeomorph_apply {q : ℕ} (R : O4) (s : Equiv.Perm (Fin q))
    (x : PointTuple q) : rotatePermuteHomeomorph R s x = rotatePermute R s x := rfl
theorem measurePreserving_rotatePermute {q : ℕ} (R : O4) (s : Equiv.Perm (Fin q)) :
    MeasurePreserving (rotatePermute R s) (volume : Measure (PointTuple q)) volume := by apply _root_.YangMills.Construction.MinkowskiSpace.InvariantEuclideanProof.measurePreserving_rotatePermute <;> assumption
theorem mem_distinctLocus_of_rotatePermute {q : ℕ} {R : O4} {s : Equiv.Perm (Fin q)}
    {x : PointTuple q} (h : rotatePermute R s x ∈ distinctLocus q) : x ∈ distinctLocus q := by
  intro a b hab
  have hinj : Function.Injective (rotatePermute R s x) := h
  have : rotatePermute R s x (s.symm a) = rotatePermute R s x (s.symm b) := by
    simp [rotatePermute, hab]
  exact s.symm.injective (hinj this)
theorem integrable_indicator_mul_schwinger {m' : ℕ}
    (hs : ContinuousOn (schwinger E Ω A m') (distinctLocus (m' + 1)))
    {g : PointTuple (m' + 1) → ℂ} (hg : Continuous g)
    (hc : HasCompactSupport g) (hsub : tsupport g ⊆ distinctLocus (m' + 1)) :
    Integrable ((distinctLocus (m' + 1)).indicator
      fun y => g y * schwinger E Ω A m' y) := by
  have hopen : IsOpen (distinctLocus (m' + 1)) := ConfigSpace.isOpen_distinctArgs
  have hind : (distinctLocus (m' + 1)).indicator
      (fun y => g y * schwinger E Ω A m' y) =
        fun y => g y * schwinger E Ω A m' y := by
    funext y
    by_cases hy : y ∈ distinctLocus (m' + 1)
    · simp [hy]
    · have : g y = 0 := image_eq_zero_of_notMem_tsupport fun h => hy (hsub h)
      simp [hy, this]
  rw [hind]
  have hts : tsupport (fun y => g y * schwinger E Ω A m' y) ⊆ tsupport g :=
    tsupport_mul_subset_left
  refine Continuous.integrable_of_hasCompactSupport ?_ (hc.mul_right)
  refine continuous_of_tsupport fun x hx => ?_
  have hxd : x ∈ distinctLocus (m' + 1) := hsub (hts hx)
  exact hg.continuousAt.mul ((hs x hxd).continuousAt (hopen.mem_nhds hxd))
theorem orderedIntegral_eq_integralSchwinger (hE : IsEuclidean E Ω A) {m : ℕ}
    {g ψ : PointTuple (m + 1) → ℂ}
    (R : O4) (s : Equiv.Perm (Fin (m + 1)))
    (hsub : tsupport g ⊆ rotatePermute R s ⁻¹' increasingTimes (m + 1))
    (hψ : ∀ x, ψ (rotatePermute R s x) = g x) :
    orderedIntegral E Ω A m ψ = integralSchwinger E Ω A m g := by
  let Q := rotatePermuteHomeomorph R s
  have hf : ∀ y, (increasingTimes (m + 1)).indicator
      (fun y => ψ y * orderedSchwinger E Ω A m y) y =
      (distinctLocus (m + 1)).indicator
        (fun y => g y * schwinger E Ω A m y) (Q.symm y) := by
    intro y
    have hy : rotatePermute R s (Q.symm y) = y := Q.apply_symm_apply y
    by_cases h : y ∈ increasingTimes (m + 1)
    · have h' : rotatePermute R s (Q.symm y) ∈ increasingTimes (m + 1) := by rwa [hy]
      have hd : Q.symm y ∈ distinctLocus (m + 1) :=
        mem_distinctLocus_of_rotatePermute (increasingTimes_subset_distinctLocus _ h')
      rw [Set.indicator_of_mem h, Set.indicator_of_mem hd, schwinger_eq_orderedSchwinger hE h',
        hy, ← hψ, hy]
    · have hgx : g (Q.symm y) = 0 := image_eq_zero_of_notMem_tsupport fun hh => h (by
        have := hsub hh
        simpa [Set.mem_preimage, hy] using this)
      rw [Set.indicator_of_notMem h]
      by_cases hd : Q.symm y ∈ distinctLocus (m + 1)
      · rw [Set.indicator_of_mem hd, hgx, zero_mul]
      · rw [Set.indicator_of_notMem hd]
  rw [orderedIntegral, integralSchwinger]
  simp_rw [hf]
  exact (measurePreserving_rotatePermute R⁻¹ s⁻¹).integral_comp
    Q.symm.measurableEmbedding _
theorem contDiff_rotatePermute {q : ℕ} (R : O4) (s : Equiv.Perm (Fin q)) :
    ContDiff ℝ ∞ (rotatePermute R s) := by apply _root_.YangMills.Construction.MinkowskiSpace.InvariantEuclideanProof.contDiff_rotatePermute <;> assumption
theorem comp_mem_smoothCompactSupp {q : ℕ} {f : PointTuple q → ℂ} {V : Set (PointTuple q)}
    (hf : f ∈ (smoothCompactSupp V : Set (PointTuple q → ℂ))) (R : O4)
    (s : Equiv.Perm (Fin q)) :
    f ∘ rotatePermuteHomeomorph R s ∈
      (smoothCompactSupp (rotatePermuteHomeomorph R s ⁻¹' V) : Set (PointTuple q → ℂ)) := by
  obtain ⟨h₁, h₂, h₃⟩ := hf
  refine ⟨h₁.comp (contDiff_rotatePermute R s), h₂.comp_homeomorph _, ?_⟩
  exact (tsupport_comp_subset_preimage f (rotatePermuteHomeomorph R s).continuous).trans
    (Set.preimage_mono h₃)
theorem smoothCompactSupp_mono {q : ℕ} {f : PointTuple q → ℂ} {V V' : Set (PointTuple q)}
    (hf : f ∈ (smoothCompactSupp V : Set (PointTuple q → ℂ))) (h : V ⊆ V') :
    f ∈ (smoothCompactSupp V' : Set (PointTuple q → ℂ)) :=
  ⟨hf.1, hf.2.1, hf.2.2.trans h⟩
theorem mem_schwartzFlatOffDiagonal (hff : TestSpaces.Elementary.BasicProperties) {m : ℕ}
    {f : PointTuple (m + 1) → ℂ}
    (hf : f ∈ (smoothCompactSupp (distinctLocus (m + 1)) :
      Set (PointTuple (m + 1) → ℂ))) : f ∈ ConfigSpace.schwartzFlatOffDiagonal (m + 1) := by
  obtain ⟨hs, hfl, -⟩ := (hff (m + 1) (Nat.succ_pos m)).2.2.1 _
    ConfigSpace.isOpen_distinctArgs f hf
  exact ⟨hs, SchwartzAxioms.vanishesToInfiniteOrderOff_iff_flatOff.1 hfl⟩
theorem tsupport_fun_add_subset {X : Type*} [TopologicalSpace X] (f g : X → ℂ) :
    tsupport (fun x => f x + g x) ⊆ tsupport f ∪ tsupport g :=
  (closure_mono (Function.support_add f g)).trans closure_union.subset
theorem add_mem_smoothCompactSupp {q : ℕ} {f g : PointTuple q → ℂ} {V : Set (PointTuple q)}
    (hf : f ∈ (smoothCompactSupp V : Set (PointTuple q → ℂ)))
    (hg : g ∈ (smoothCompactSupp V : Set (PointTuple q → ℂ))) :
    (fun x => f x + g x) ∈ (smoothCompactSupp V : Set (PointTuple q → ℂ)) :=
  ⟨hf.1.add hg.1, hf.2.1.add hg.2.1,
    (tsupport_fun_add_subset f g).trans (Set.union_subset hf.2.2 hg.2.2)⟩
theorem zero_mem_smoothCompactSupp {q : ℕ} (V : Set (PointTuple q)) :
    (fun _ => 0 : PointTuple q → ℂ) ∈ (smoothCompactSupp V : Set (PointTuple q → ℂ)) := by
  refine ⟨contDiff_const, HasCompactSupport.zero, ?_⟩
  rw [show (fun _ : PointTuple q => (0 : ℂ)) = 0 from rfl, tsupport_zero]
  exact Set.empty_subset _
theorem isOpen_preimage_increasingTimes {q : ℕ} (R : O4) (s : Equiv.Perm (Fin q)) :
    IsOpen (rotatePermute R s ⁻¹' increasingTimes q) :=
  (isOpen_increasingTimes q).preimage (continuous_rotatePermute R s)
theorem integralSchwinger_linear_comb {m : ℕ}
    (hs : ContinuousOn (schwinger E Ω A m) (distinctLocus (m + 1)))
    {f g : PointTuple (m + 1) → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hfs : tsupport f ⊆ distinctLocus (m + 1))
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgs : tsupport g ⊆ distinctLocus (m + 1))
    (a b : ℂ) :
    integralSchwinger E Ω A m (fun x => a * f x + b * g x) =
      a * integralSchwinger E Ω A m f +
        b * integralSchwinger E Ω A m g := by
  have h : (distinctLocus (m + 1)).indicator
      (fun y => (a * f y + b * g y) * schwinger E Ω A m y) =
      fun x => a * (distinctLocus (m + 1)).indicator
          (fun y => f y * schwinger E Ω A m y) x +
        b * (distinctLocus (m + 1)).indicator
          (fun y => g y * schwinger E Ω A m y) x := by
    funext x
    by_cases hx : x ∈ distinctLocus (m + 1)
    · simp only [Set.indicator_of_mem hx]
      ring
    · simp [Set.indicator_of_notMem hx]
  rw [integralSchwinger, h,
    integral_add ((integrable_indicator_mul_schwinger hs hf hfc hfs).const_mul a)
      ((integrable_indicator_mul_schwinger hs hg hgc hgs).const_mul b),
    integral_const_mul, integral_const_mul]
  rfl
theorem actOnFun_permuteArgs_rotatePermute {n : ℕ} {F : Type*} (R : O4)
    (s : Equiv.Perm (Fin n)) (f : PointTuple n → F) (x : PointTuple n) :
    actOnFun (⟨R.1, R.2, 0⟩ : RigidMotion) (permuteArgs s⁻¹ f)
      (rotatePermute R s x) = f x := by
  simp only [actOnFun, permuteArgs]
  congr 1
  funext i
  have h := (⟨R.1, R.2, 0⟩ : RigidMotion).invFun_toFun (x i)
  simpa [RigidMotion.toFun, rotatePermute] using h
theorem atSucc_congr {m : ℕ} (S : ConfigSpace.FlatSequence)
    {f f' : PointTuple (m + 1) → ℂ} (e : f = f')
    (h : f ∈ ConfigSpace.schwartzFlatOffDiagonal (m + 1))
    (h' : f' ∈ ConfigSpace.schwartzFlatOffDiagonal (m + 1))
    (hv : S.atSucc m ⟨f, h⟩ = integralSchwinger E Ω A m f) :
    S.atSucc m ⟨f', h'⟩ = integralSchwinger E Ω A m f' := by
  subst e
  exact hv
theorem sequenceEqIntegralSchwinger
    (ht : WightmanReconstruction.SmoothToolkit.Toolkit)
    (hff : TestSpaces.Elementary.BasicProperties) (hE : IsEuclidean E Ω A) {m : ℕ}
    (hs : ContinuousOn (schwinger E Ω A m) (distinctLocus (m + 1))) :
    SequenceEqIntegralSchwinger E Ω A m := by
  classical
  intro S hS hR hperm φ hφ hflat
  have hlin := hS.1.2 m
  have hcomp : IsCompact (tsupport φ) := hφ.2.1
  let U : O4 × Equiv.Perm (Fin (m + 1)) → Set (PointTuple (m + 1)) :=
    fun p => rotatePermute p.1 p.2 ⁻¹' increasingTimes (m + 1)
  have hUo : ∀ p, IsOpen (U p) := fun p => isOpen_preimage_increasingTimes p.1 p.2
  have hcov : tsupport φ ⊆ ⋃ p, U p := fun x hx => by
    obtain ⟨R, s, -, h⟩ := exists_rotatePermute_mem ht (hφ.2.2 hx)
    exact Set.mem_iUnion.2 ⟨(R, s), h⟩
  obtain ⟨t, hcover⟩ := hcomp.elim_finite_subcover U hUo hcov
  let t' := insert ((1 : O4), (1 : Equiv.Perm (Fin (m + 1)))) t
  let e := t'.equivFin
  have hr : 1 ≤ t'.card := Finset.card_pos.2 ⟨_, Finset.mem_insert_self _ _⟩
  obtain ⟨χ, hχ, N, -, hCN, hsum⟩ := ht.2.2.2.1 (m + 1) t'.card (Nat.succ_pos m) hr (tsupport φ)
    (fun α => U (e.symm α).1) hcomp (fun α => hUo _) (by
      intro x hx
      obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.1 (hcover hx)
      exact Set.mem_iUnion.2 ⟨e ⟨p, Finset.mem_insert_of_mem hp⟩, by simpa using hxp⟩)
  let piece : Fin t'.card → PointTuple (m + 1) → ℂ := fun α x => (χ α x : ℂ) * φ x
  have hpiece : ∀ α, piece α ∈ (smoothCompactSupp (U (e.symm α).1) :
      Set (PointTuple (m + 1) → ℂ)) := fun α => by
    refine ⟨(Complex.ofRealCLM.contDiff.comp (hχ α).1).mul hφ.1, hφ.2.1.mul_left, ?_⟩
    refine (tsupport_mul_subset_left (f := fun x => (χ α x : ℂ))).trans ?_
    refine Set.Subset.trans (closure_mono ?_) (hχ α).2.2
    intro x hx h0
    exact hx (by simp [h0])
  have hdist : ∀ p, U p ⊆ distinctLocus (m + 1) := fun p x hx =>
    mem_distinctLocus_of_rotatePermute (increasingTimes_subset_distinctLocus _ hx)
  have hsm : ∀ α, piece α ∈ (smoothCompactSupp (distinctLocus (m + 1)) :
      Set (PointTuple (m + 1) → ℂ)) := fun α => smoothCompactSupp_mono (hpiece α) (hdist _)
  have hlocal : ∀ α (h : piece α ∈ ConfigSpace.schwartzFlatOffDiagonal (m + 1)),
      S.atSucc m ⟨piece α, h⟩ = integralSchwinger E Ω A m (piece α) := by
    intro α h
    let R := (e.symm α).1.1
    let s := (e.symm α).1.2
    have hp : piece α ∈ (smoothCompactSupp
        (rotatePermute R s ⁻¹' increasingTimes (m + 1)) : Set (PointTuple (m + 1) → ℂ)) :=
      hpiece α
    have h₁ : permuteArgs s⁻¹ (piece α) ∈
        (smoothCompactSupp (distinctLocus (m + 1)) : Set (PointTuple (m + 1) → ℂ)) := by
      have h' := smoothCompactSupp_mono (comp_mem_smoothCompactSupp (hsm α) 1 s⁻¹)
        (V' := distinctLocus (m + 1)) (fun x hx => mem_distinctLocus_of_rotatePermute hx)
      convert h' using 1
      funext x
      change piece α (fun i => x (s⁻¹ i)) = piece α (rotatePermute 1 s⁻¹ x)
      congr 1
      funext i
      simp [rotatePermute]
    have hmot : actOnFun (⟨R.1, R.2, 0⟩ : RigidMotion)
        (permuteArgs s⁻¹ (piece α)) = piece α ∘ rotatePermuteHomeomorph R⁻¹ s⁻¹ := by
      funext y
      obtain ⟨x, rfl⟩ := (rotatePermuteHomeomorph R s).surjective y
      rw [rotatePermuteHomeomorph_apply, actOnFun_permuteArgs_rotatePermute]
      have hx : rotatePermuteHomeomorph R⁻¹ s⁻¹ (rotatePermute R s x) = x :=
        (rotatePermuteHomeomorph R s).left_inv x
      simp only [Function.comp, hx]
    have h₂o : actOnFun (⟨R.1, R.2, 0⟩ : RigidMotion)
        (permuteArgs s⁻¹ (piece α)) ∈
        (smoothCompactSupp (increasingTimes (m + 1)) : Set (PointTuple (m + 1) → ℂ)) := by
      rw [hmot]
      refine smoothCompactSupp_mono (comp_mem_smoothCompactSupp hp R⁻¹ s⁻¹) fun y hy => ?_
      have hy' : rotatePermute R s (rotatePermuteHomeomorph R⁻¹ s⁻¹ y) = y :=
        (rotatePermuteHomeomorph R s).right_inv y
      have hy'' : rotatePermute R s (rotatePermuteHomeomorph R⁻¹ s⁻¹ y) ∈
          increasingTimes (m + 1) := hy
      rwa [hy'] at hy''
    have h₂ := smoothCompactSupp_mono h₂o (increasingTimes_subset_distinctLocus (m + 1))
    rw [← hperm ⟨piece α, h⟩ s⁻¹ (mem_schwartzFlatOffDiagonal hff h₁),
      ← hR ⟨_, mem_schwartzFlatOffDiagonal hff h₁⟩ R (mem_schwartzFlatOffDiagonal hff h₂),
      hS.2 m _ h₂o (mem_schwartzFlatOffDiagonal hff h₂)]
    exact orderedIntegral_eq_integralSchwinger hE R s hp.2.2
      (actOnFun_permuteArgs_rotatePermute R s _)
  have hall : ∀ T : Finset (Fin t'.card),
      (fun x => ∑ α ∈ T, piece α x) ∈ (smoothCompactSupp (distinctLocus (m + 1)) :
        Set (PointTuple (m + 1) → ℂ)) ∧
      ∀ h, S.atSucc m ⟨fun x => ∑ α ∈ T, piece α x, h⟩ =
        integralSchwinger E Ω A m (fun x => ∑ α ∈ T, piece α x) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      refine ⟨zero_mem_smoothCompactSupp _, fun h => ?_⟩
      have h0 := hlin 0 0 ⟨_, h⟩ ⟨_, h⟩ ⟨_, h⟩ (by funext x; simp)
      simp only [zero_mul, add_zero] at h0
      rw [h0]
      simp [integralSchwinger]
    | insert a T ha ih =>
      obtain ⟨ih₁, ih₂⟩ := ih
      have hfun : (fun x => ∑ α ∈ insert a T, piece α x) =
          fun x => piece a x + ∑ α ∈ T, piece α x := by
        funext x
        rw [Finset.sum_insert ha]
      rw [hfun]
      refine ⟨add_mem_smoothCompactSupp (hsm a) ih₁, fun h => ?_⟩
      have hl := hlin 1 1 ⟨piece a, mem_schwartzFlatOffDiagonal hff (hsm a)⟩
        ⟨_, mem_schwartzFlatOffDiagonal hff ih₁⟩ ⟨_, h⟩ (by funext x; simp)
      rw [hl, one_mul, one_mul, hlocal, ih₂]
      have := integralSchwinger_linear_comb hs (hsm a).1.continuous (hsm a).2.1 (hsm a).2.2
        ih₁.1.continuous ih₁.2.1 ih₁.2.2 1 1
      simpa using this.symm
  have hφsum : (fun x => ∑ α, piece α x) = φ := by
    funext x
    by_cases hx : x ∈ N
    · simp only [piece]
      rw [← Finset.sum_mul, ← Complex.ofReal_sum, hsum x hx]
      simp
    · have : φ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hCN h)
      simp [piece, this]
  have hflat' := mem_schwartzFlatOffDiagonal hff (hall Finset.univ).1
  exact atSucc_congr S hφsum hflat' hflat ((hall Finset.univ).2 hflat')
theorem tsupport_tensorProdComplex_subset_pi {n : ℕ} (f : Fin n → (Fin 4 → ℝ) → ℝ) :
    tsupport (tensorProdComplex f) ⊆ Set.univ.pi fun i => tsupport (f i) := by apply _root_.YangMills.Construction.RepresentsEuclideanProof.tsupport_tensorProdComplex_subset_pi <;> assumption
theorem continuous_tensorProdComplex {n : ℕ} (X : SepTupleOfCard n) :
    Continuous (tensorProdComplex X.1) :=
  Complex.continuous_ofReal.comp (continuous_finsetProd _ fun i _ =>
    (X.2.1 i).1.continuous.comp (continuous_apply i))
theorem isCompact_pi_tsupport {n : ℕ} (X : SepTupleOfCard n) :
    IsCompact (Set.univ.pi fun i => tsupport (X.1 i)) :=
  isCompact_univ_pi fun i => (X.2.1 i).2.1
theorem hasCompactSupport_tensorProdComplex {n : ℕ} (X : SepTupleOfCard n) :
    HasCompactSupport (tensorProdComplex X.1) :=
  (isCompact_pi_tsupport X).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_tensorProdComplex_subset_pi X.1)
theorem pi_tsupport_subset_distinctLocus {n : ℕ} (X : SepTupleOfCard n) :
    (Set.univ.pi fun i => tsupport (X.1 i)) ⊆ distinctLocus n := by
  intro x hx i k hik
  by_contra hne
  exact Set.disjoint_left.1 (X.2.2 hne) (hx i (Set.mem_univ i)) (hik ▸ hx k (Set.mem_univ k))
theorem tsupport_tensorProdComplex_subset_distinctLocus {n : ℕ} (X : SepTupleOfCard n) :
    tsupport (tensorProdComplex X.1) ⊆ distinctLocus n :=
  (tsupport_tensorProdComplex_subset_pi X.1).trans (pi_tsupport_subset_distinctLocus X)
def residual (E : FourBorelSet → BddOp K) (Ω : K) (A : ℝ → BddOp K)
    (sigma : SepTuple → ℝ) (m : ℕ) (X : SepTupleOfCard (m + 1)) : ℂ :=
  ((sigma ⟨m + 1, X⟩ : ℝ) : ℂ) - integralSchwinger E Ω A m (tensorProdComplex X.1)
theorem residual_multilinear {sigma : SepTuple → ℝ} (hsig : IsSepFunctional sigma) {m : ℕ}
    (hs : ContinuousOn (schwinger E Ω A m) (distinctLocus (m + 1)))
    (i : Fin (m + 1)) (b b' : ℝ) (X X' X'' : SepTupleOfCard (m + 1))
    (h₁ : ∀ j, j ≠ i → X.1 j = X'.1 j) (h₂ : X''.1 i = b • X.1 i + b' • X'.1 i)
    (h₃ : ∀ j, j ≠ i → X''.1 j = X.1 j) :
    residual E Ω A sigma m X'' = b * residual E Ω A sigma m X + b' * residual E Ω A sigma m X' := by
  have hv := hsig.2 (m + 1) (Nat.succ_pos m) i b b' X X' X'' h₁ h₂ h₃
  have hv' : ((sigma ⟨m + 1, X''⟩ : ℝ) : ℂ) = b * sigma ⟨m + 1, X⟩ + b' * sigma ⟨m + 1, X'⟩ := by
    exact_mod_cast congrArg (fun t : ℝ => (t : ℂ)) hv
  have ht : tensorProdComplex X''.1 =
      fun x => (b : ℂ) * tensorProdComplex X.1 x + (b' : ℂ) * tensorProdComplex X'.1 x := by
    funext x
    have hp : ∀ Y : SepTupleOfCard (m + 1), tensorProd Y.1 x =
        Y.1 i (x i) * ∏ j ∈ Finset.univ.erase i, Y.1 j (x j) := fun Y =>
      (Finset.mul_prod_erase _ (fun j => Y.1 j (x j)) (Finset.mem_univ i)).symm
    have he : ∏ j ∈ Finset.univ.erase i, X''.1 j (x j) =
        ∏ j ∈ Finset.univ.erase i, X.1 j (x j) :=
      Finset.prod_congr rfl fun j hj => by rw [h₃ j (Finset.ne_of_mem_erase hj)]
    have he' : ∏ j ∈ Finset.univ.erase i, X'.1 j (x j) =
        ∏ j ∈ Finset.univ.erase i, X.1 j (x j) :=
      Finset.prod_congr rfl fun j hj => by rw [h₁ j (Finset.ne_of_mem_erase hj)]
    simp only [tensorProdComplex]
    rw [hp X'', hp X, hp X', he, he', h₂]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [residual, residual, residual, hv', ht,
    integralSchwinger_linear_comb hs (continuous_tensorProdComplex X)
      (hasCompactSupport_tensorProdComplex X) (tsupport_tensorProdComplex_subset_distinctLocus X)
      (continuous_tensorProdComplex X') (hasCompactSupport_tensorProdComplex X')
      (tsupport_tensorProdComplex_subset_distinctLocus X')]
  ring
theorem residual_of_entry_eq_zero {sigma : SepTuple → ℝ} (hsig : IsSepFunctional sigma)
    {m : ℕ} (hs : ContinuousOn (schwinger E Ω A m) (distinctLocus (m + 1)))
    (Y : SepTupleOfCard (m + 1)) (i : Fin (m + 1)) (h : Y.1 i = 0) :
    residual E Ω A sigma m Y = 0 := by
  have := residual_multilinear (E := E) (Ω := Ω) (A := A) hsig hs i 0 0 Y Y Y (fun _ _ => rfl)
    (by simp [h]) (fun _ _ => rfl)
  simpa using this
theorem tsupport_mul_real_right (g f : (Fin 4 → ℝ) → ℝ) :
    tsupport (fun u => g u * f u) ⊆ tsupport f :=
  tsupport_mul_subset_right (f := g) (g := f)
theorem tsupport_mul_real_left (g f : (Fin 4 → ℝ) → ℝ) :
    tsupport (fun u => g u * f u) ⊆ tsupport g :=
  tsupport_mul_subset_left (f := g) (g := f)
theorem update_mul_mem_disjointSupportTuples {n : ℕ} (Y : SepTupleOfCard n) (a : Fin n)
    {g : (Fin 4 → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g) :
    Function.update Y.1 a (fun u => g u * Y.1 a u) ∈ disjointSupportTuples Set.univ n := by
  have hsub : ∀ j, tsupport (Function.update Y.1 a (fun u => g u * Y.1 a u) j) ⊆
      tsupport (Y.1 j) := by
    intro j
    by_cases hj : j = a
    · subst hj
      simpa using tsupport_mul_real_right g (Y.1 j)
    · simp [Function.update_of_ne hj]
  refine ⟨fun j => ?_, fun j k hjk => (Y.2.2 hjk).mono (hsub j) (hsub k)⟩
  by_cases hj : j = a
  · subst hj
    rw [Function.update_self]
    exact ⟨(hg.of_le (mod_cast le_top)).mul (Y.2.1 j).1,
      (Y.2.1 j).2.1.mul_left, Set.subset_univ _⟩
  · rw [Function.update_of_ne hj]
    exact Y.2.1 j
theorem residual_update_sum {sigma : SepTuple → ℝ} (hsig : IsSepFunctional sigma) {m : ℕ}
    (hs : ContinuousOn (schwinger E Ω A m) (distinctLocus (m + 1)))
    (Y : SepTupleOfCard (m + 1)) (a : Fin (m + 1)) {ι : Type} [DecidableEq ι]
    (ρ : ι → (Fin 4 → ℝ) → ℝ) (hρ : ∀ β, ContDiff ℝ ∞ (ρ β))
    (hterm : ∀ β, residual E Ω A sigma m ⟨_, update_mul_mem_disjointSupportTuples Y a (hρ β)⟩ = 0)
    (T : Finset ι) :
    residual E Ω A sigma m
      ⟨_, update_mul_mem_disjointSupportTuples Y a (ContDiff.sum (s := T) fun β _ => hρ β)⟩ = 0 := by
  induction T using Finset.induction_on with
  | empty =>
    refine residual_of_entry_eq_zero hsig hs _ a ?_
    funext u
    simp
  | insert b T hb ih =>
    have h := residual_multilinear (E := E) (Ω := Ω) (A := A) hsig hs a 1 1
      ⟨_, update_mul_mem_disjointSupportTuples Y a (hρ b)⟩
      ⟨_, update_mul_mem_disjointSupportTuples Y a (ContDiff.sum (s := T) fun β _ => hρ β)⟩
      ⟨_, update_mul_mem_disjointSupportTuples Y a
        (ContDiff.sum (s := insert b T) fun β _ => hρ β)⟩
      (fun j hj => by simp [Function.update_of_ne hj])
      (by
        funext u
        simp [Finset.sum_insert hb, add_mul])
      (fun j hj => by simp [Function.update_of_ne hj])
    rw [h, hterm b, ih]
    simp
theorem exists_separating_times {m : ℕ} (a b : Fin (m + 1) → ℝ)
    (h : ∀ i j, i < j → b i < a j) :
    ∃ c : Fin (m + 2) → ℝ, ∀ i : Fin (m + 1), c i.castSucc < a i ∧ b i < c i.succ := by
  refine ⟨Fin.cases (a 0 - 1) (fun i : Fin (m + 1) =>
    if hi : (i : ℕ) + 1 < m + 1 then (b i + a ⟨i + 1, hi⟩) / 2 else b i + 1),
    fun i => ⟨?_, ?_⟩⟩
  · induction i using Fin.cases with
    | zero => simp
    | succ i =>
      rw [← Fin.succ_castSucc]
      simp only [Fin.cases_succ]
      have hi : ((Fin.castSucc i : Fin (m + 1)) : ℕ) + 1 < m + 1 := by
        simp
      rw [dif_pos hi]
      have := h i.castSucc i.succ Fin.castSucc_lt_succ
      have e : (⟨((Fin.castSucc i : Fin (m + 1)) : ℕ) + 1, hi⟩ : Fin (m + 1)) = i.succ := by
        ext
        simp
      rw [e]
      linarith
  · simp only [Fin.cases_succ]
    split_ifs with hi
    · have := h i ⟨i + 1, hi⟩ (by simp [Fin.lt_def])
      linarith
    · linarith
theorem residual_eq_zero_of_local (hE : IsEuclidean E Ω A) {sigma : SepTuple → ℝ} {m : ℕ}
    (hrep : RepresentsFunctional E Ω A sigma)
    (hsym : WightmanReconstruction.IsPermutationInvariant sigma)
    (hinv : ∀ R : O4, WightmanReconstruction.IsMotionInvariant sigma ⟨R.1, R.2, 0⟩)
    (Y : SepTupleOfCard (m + 1)) (R : O4) (s : Equiv.Perm (Fin (m + 1)))
    (hne : ∀ i, (tsupport (Y.1 i)).Nonempty)
    (hprod : ∀ z : PointTuple (m + 1), (∀ i, z i ∈ tsupport (Y.1 i)) →
      rotatePermute R s z ∈ increasingTimes (m + 1)) :
    residual E Ω A sigma m Y = 0 := by
  classical
  let r : RigidMotion := ⟨R.1, R.2, 0⟩
  let Yp : SepTupleOfCard (m + 1) := WightmanReconstruction.permuteComponents Y s
  let Z : SepTupleOfCard (m + 1) := (UpperHalfTensors.actOnSTuple r ⟨m + 1, Yp⟩).2
  have hZ : ∀ i, Z.1 i = (Y.1 (s i)) ∘ r.invFun := fun i => rfl
  have h₁ : sigma ⟨m + 1, Yp⟩ = sigma ⟨m + 1, Y⟩ := hsym (m + 1) (Nat.succ_pos m) Y s
  have h₂ : sigma ⟨m + 1, Z⟩ = sigma ⟨m + 1, Yp⟩ := hinv R ⟨m + 1, Yp⟩
  let Tm : Fin (m + 1) → Set ℝ := fun i =>
    (fun u => ((R : Matrix (Fin 4) (Fin 4) ℝ) *ᵥ u) 3) '' tsupport (Y.1 (s i))
  have hTc : ∀ i, IsCompact (Tm i) := fun i =>
    ((Y.2.1 (s i)).2.1 : IsCompact _).image
      ((continuous_apply 3).comp (Continuous.matrix_mulVec continuous_const continuous_id))
  have hTn : ∀ i, (Tm i).Nonempty := fun i => (hne (s i)).image _
  choose a ha using fun i => (hTc i).exists_isLeast (hTn i)
  choose b hb using fun i => (hTc i).exists_isGreatest (hTn i)
  choose y hy using hne
  have hgap : ∀ i j, i < j → b i < a j := by
    intro i j hij
    obtain ⟨u, hu, hub⟩ := (hb i).1
    obtain ⟨v, hv, hva⟩ := (ha j).1
    have hsij : s i ≠ s j := fun h => hij.ne (s.injective h)
    let z : PointTuple (m + 1) := Function.update (Function.update y (s i) u) (s j) v
    have hz : ∀ k, z k ∈ tsupport (Y.1 k) := by
      intro k
      by_cases hkj : k = s j
      · subst hkj
        simpa [z] using hv
      · by_cases hki : k = s i
        · subst hki
          simpa [z, Function.update_of_ne hkj] using hu
        · simpa [z, Function.update_of_ne hkj, Function.update_of_ne hki] using hy k
    have h := hprod z hz hij
    have hzi : z (s i) = u := by simp [z, Function.update_of_ne hsij]
    have hzj : z (s j) = v := by simp [z]
    simp only [timeCoord, rotatePermute, hzi, hzj] at h
    rw [← hub, ← hva]
    exact h
  obtain ⟨c, hc⟩ := exists_separating_times a b hgap
  have hinvc : Continuous r.invFun :=
    Continuous.matrix_mulVec continuous_const (continuous_id.sub continuous_const)
  have hZord : WightmanReconstruction.IsTimeOrdered Z.1 := by
    refine ⟨Z.2, c, Fin.strictMono_iff_lt_succ.2 fun i => ?_, fun i u hu => ?_⟩
    · have hab : a i ≤ b i := (ha i).2 (hb i).1
      linarith [(hc i).1, (hc i).2]
    · rw [hZ] at hu
      have hu' := tsupport_comp_subset_preimage (Y.1 (s i)) hinvc hu
      have hmem : u 3 ∈ Tm i := by
        refine ⟨_, hu', ?_⟩
        have := r.toFun_invFun u
        simp only [RigidMotion.toFun] at this
        simp only [add_zero, r] at this
        simp only [r]
        rw [this]
      exact ⟨(hc i).1.trans_le ((ha i).2 hmem), ((hb i).2 hmem).trans_lt (hc i).2⟩
  have h₃ := hrep.2 m Z hZord
  have h₄ : orderedIntegral E Ω A m (tensorProdComplex Z.1) =
      integralSchwinger E Ω A m (tensorProdComplex Y.1) := by
    refine orderedIntegral_eq_integralSchwinger hE R s ?_ ?_
    · exact fun x hx => hprod x fun i =>
        tsupport_tensorProdComplex_subset_pi Y.1 hx i (Set.mem_univ i)
    · intro x
      simp only [tensorProdComplex, tensorProd]
      congr 1
      rw [← Equiv.prod_comp s (fun j => Y.1 j (x j))]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hZ]
      have h := r.invFun_toFun (x (s i))
      have h' : r.invFun (rotatePermute R s x i) = x (s i) := by
        simpa [RigidMotion.toFun, rotatePermute, r] using h
      simp only [Function.comp, h']
  rw [residual, ← h₁, ← h₂, h₃, h₄, sub_self]
def pointTupleOneHomeomorph : PointTuple 1 ≃ₜ (Fin 4 → ℝ) where
  toFun x := x 0
  invFun u := fun _ => u
  left_inv x := by
    funext i
    rw [Subsingleton.elim i 0]
  right_inv _ := rfl
  continuous_toFun := continuous_apply 0
  continuous_invFun := continuous_pi fun _ => continuous_id
theorem functionalEqIntegralSchwinger
    (ht : WightmanReconstruction.SmoothToolkit.Toolkit)
    (hE : IsEuclidean E Ω A) {m : ℕ}
    (hs : ContinuousOn (schwinger E Ω A m) (distinctLocus (m + 1))) :
    FunctionalEqIntegralSchwinger E Ω A m := by
  classical
  intro sigma hrep hsym hinv X
  have hsig := hrep.1
  suffices hd : residual E Ω A sigma m X = 0 from sub_eq_zero.1 hd
  let C : Set (PointTuple (m + 1)) := Set.univ.pi fun i => tsupport (X.1 i)
  have hCc : IsCompact C := isCompact_pi_tsupport X
  let U : O4 × Equiv.Perm (Fin (m + 1)) → Set (PointTuple (m + 1)) :=
    fun p => rotatePermute p.1 p.2 ⁻¹' increasingTimes (m + 1)
  have hUo : ∀ p, IsOpen (U p) := fun p => isOpen_preimage_increasingTimes p.1 p.2
  have hcov : C ⊆ ⋃ p, U p := fun x hx => by
    obtain ⟨R, s, -, h⟩ := exists_rotatePermute_mem ht (pi_tsupport_subset_distinctLocus X hx)
    exact Set.mem_iUnion.2 ⟨(R, s), h⟩
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric hCc hUo hcov
  let W : Set (Fin 4 → ℝ) := ⋃ i, tsupport (X.1 i)
  have hWc : IsCompact W := isCompact_iUnion fun i => (X.2.1 i).2.1
  obtain ⟨t, -, htf, hWt⟩ := hWc.finite_cover_balls (show 0 < δ / 3 by positivity)
  let t' : Finset (Fin 4 → ℝ) := insert 0 htf.toFinset
  let e := t'.equivFin
  have hr : 1 ≤ t'.card := Finset.card_pos.2 ⟨_, Finset.mem_insert_self _ _⟩
  let B : Fin t'.card → Set (Fin 4 → ℝ) := fun β => Metric.ball (e.symm β).1 (δ / 3)
  let e₁ := pointTupleOneHomeomorph
  obtain ⟨χ, hχ, N, -, hCN, hsum⟩ := ht.2.2.2.1 1 t'.card le_rfl hr (e₁ ⁻¹' W)
    (fun β => e₁ ⁻¹' B β) (e₁.isCompact_preimage.2 hWc)
    (fun β => Metric.isOpen_ball.preimage e₁.continuous) (by
      intro x hx
      obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.1 (hWt hx)
      exact Set.mem_iUnion.2
        ⟨e ⟨c, Finset.mem_insert_of_mem (htf.mem_toFinset.2 hc)⟩, by simpa [B] using hxc⟩)
  let ρ : Fin t'.card → (Fin 4 → ℝ) → ℝ := fun β u => χ β (e₁.symm u)
  have hρ : ∀ β, ContDiff ℝ ∞ (ρ β) := fun β =>
    (hχ β).1.comp (contDiff_pi.2 fun _ => contDiff_id)
  have hρs : ∀ β, tsupport (ρ β) ⊆ B β := fun β =>
    (tsupport_comp_subset_preimage (χ β) e₁.symm.continuous).trans fun u hu => by
      have h := (hχ β).2.2 hu
      simpa using h
  have hρ1 : ∀ u ∈ W, ∑ β, ρ β u = 1 := fun u hu => hsum _ (hCN (by simpa using hu))
  have hlocal : ∀ Y : SepTupleOfCard (m + 1), (∀ i, tsupport (Y.1 i) ⊆ tsupport (X.1 i)) →
      (∀ i, ∃ β, tsupport (Y.1 i) ⊆ B β) → residual E Ω A sigma m Y = 0 := by
    intro Y hsupp hsmall
    by_cases hz : ∃ i, Y.1 i = 0
    · obtain ⟨i, hi⟩ := hz
      exact residual_of_entry_eq_zero hsig hs Y i hi
    · have hne : ∀ i, (tsupport (Y.1 i)).Nonempty := fun i => by
        obtain ⟨u, hu⟩ := Function.support_nonempty_iff.2 (not_exists.1 hz i)
        exact ⟨u, subset_tsupport _ hu⟩
      have hne' := hne
      choose y hy using hne'
      have hyC : y ∈ C := fun i _ => hsupp i (hy i)
      obtain ⟨p, hp⟩ := hleb y hyC
      choose β hβ using hsmall
      refine residual_eq_zero_of_local hE hrep hsym hinv Y p.1 p.2 hne fun z hz' => hp ?_
      refine (dist_pi_lt_iff hδ).2 fun i => ?_
      have h₁ : dist (z i) (e.symm (β i)).1 < δ / 3 := hβ i (hz' i)
      have h₂ : dist (y i) (e.symm (β i)).1 < δ / 3 := hβ i (hy i)
      have h₃ := dist_triangle_right (z i) (y i) (e.symm (β i)).1
      linarith
  have hmain : ∀ As : Finset (Fin (m + 1)), ∀ Y : SepTupleOfCard (m + 1),
      (∀ i, tsupport (Y.1 i) ⊆ tsupport (X.1 i)) →
      (∀ i, i ∉ As → ∃ β, tsupport (Y.1 i) ⊆ B β) → residual E Ω A sigma m Y = 0 := by
    intro As
    induction As using Finset.induction_on with
    | empty => exact fun Y h₁ h₂ => hlocal Y h₁ fun i => h₂ i (Finset.notMem_empty i)
    | insert a As ha ih =>
      intro Y h₁ h₂
      have hterm : ∀ β, residual E Ω A sigma m
          ⟨_, update_mul_mem_disjointSupportTuples Y a (hρ β)⟩ = 0 := by
        intro β
        refine ih _ (fun i => ?_) (fun i hi => ?_)
        · by_cases hia : i = a
          · subst hia
            simp only [Function.update_self]
            exact (tsupport_mul_real_right _ _).trans (h₁ i)
          · simp only [Function.update_of_ne hia]
            exact h₁ i
        · by_cases hia : i = a
          · subst hia
            refine ⟨β, ?_⟩
            simp only [Function.update_self]
            exact (tsupport_mul_real_left _ _).trans (hρs β)
          · simp only [Function.update_of_ne hia]
            exact h₂ i (by simp [hia, hi])
      have hS := residual_update_sum hsig hs Y a ρ hρ hterm Finset.univ
      have hf : (fun u => (∑ β, ρ β u) * Y.1 a u) = Y.1 a := by
        funext u
        by_cases hu : u ∈ W
        · rw [hρ1 u hu, one_mul]
        · have h0 : Y.1 a u = 0 := image_eq_zero_of_notMem_tsupport fun h =>
            hu (Set.mem_iUnion.2 ⟨a, h₁ a h⟩)
          simp [h0]
      have hY : Function.update Y.1 a (fun u => (∑ β, ρ β u) * Y.1 a u) = Y.1 := by
        rw [hf, Function.update_eq_self]
      have hYe : (⟨_, update_mul_mem_disjointSupportTuples Y a
          (ContDiff.sum (s := Finset.univ) fun β _ => hρ β)⟩ :
          SepTupleOfCard (m + 1)) = Y := Subtype.ext hY
      rwa [hYe] at hS
  exact hmain Finset.univ X (fun _ => subset_rfl) fun i hi => absurd (Finset.mem_univ i) hi
theorem euclideanSchwingerProperties_holds
    (hmx : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hff : TestSpaces.Elementary.BasicProperties)
    (ht : WightmanReconstruction.SmoothToolkit.Toolkit)
    (hp : FieldProductProperties) :
    EuclideanSchwingerProperties := by
  intro K _ _ _ E Ω A P C hF hE m
  have hprod := hp K E Ω A P C hF
  have hw : IsHolomorphicOnTube (m := m) (vacuumExpectation E Ω A (m + 1)) :=
    (hprod.2.2.2.2.2.2.2.1 m).1
  have hc : ExpectationConj E Ω A := hprod.2.2.2.2.2.2.2.2.2.2
  have hs := schwinger_continuousOn ht hmx hE hw
  refine ⟨fun x hx => ⟨exists_rotatePermute_mem ht hx,
      fun R s h => schwinger_eq_orderedSchwinger hE h⟩,
    ⟨schwinger_isRealAnalyticIn ht hmx hE hw, fun x hx => schwinger_eq_orderedSchwinger_of_mem hE hx,
      fun r s x hx => schwinger_motion_perm ht hE r s hx⟩, fun x hx => ?_,
    sequenceEqIntegralSchwinger ht hff hE hs, functionalEqIntegralSchwinger ht hE hs⟩
  obtain ⟨R, s, -, h⟩ := exists_rotatePermute_mem ht hx
  rw [schwinger_eq_orderedSchwinger hE h]
  exact conj_orderedSchwinger hc hE h
end FieldForms.EuclideanSchwinger
end YangMills.Construction
