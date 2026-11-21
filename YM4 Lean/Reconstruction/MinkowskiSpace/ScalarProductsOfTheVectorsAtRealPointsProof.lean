import Reconstruction.MinkowskiSpace.LocalityOfTheWightmanValuesProof
import Reconstruction.MinkowskiSpace.MatrixElementsOfTheFieldVectorsOnTheTubeProof
import Reconstruction.MinkowskiSpace.ScalarProductsOfTheVectorsAtRealPoints
import Reconstruction.MinkowskiSpace.SchwartzFunctionsThatStandInTheVectorsAtRealPoints
import Reconstruction.MinkowskiSpace.WightmanValuesAsBoundaryValuesOfTheVacuumFunction
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped ComplexConjugate InnerProductSpace Topology
noncomputable section
namespace YangMills.Construction.RealPointInnerProducts
open MinkowskiSpace FieldForms TestSpaces WightmanReconstruction OneLoopNotation
  ComplexHilbert ProjectionMeasures HyperplaneReflection RealPointVectors
def revTuple {q : ℕ} (y : PointTuple q) : PointTuple q := fun i => y (Fin.rev i)
theorem revTuple_revTuple {q : ℕ} (y : PointTuple q) :
    revTuple (revTuple y) = y := by
  funext i
  simp [revTuple]
theorem measurePreserving_revTuple (q : ℕ) :
    MeasurePreserving (revTuple : PointTuple q → PointTuple q) volume volume := by
  have h := volume_measurePreserving_piCongrLeft (fun _ : Fin q => Fin 4 → ℝ)
    (Fin.revPerm (n := q))
  have he : (MeasurableEquiv.piCongrLeft (fun _ : Fin q => Fin 4 → ℝ) (Fin.revPerm (n := q)) :
      PointTuple q → PointTuple q) = revTuple := by
    funext y i
    have := MeasurableEquiv.piCongrLeft_apply_apply (Fin.revPerm (n := q))
      (β := fun _ : Fin q => Fin 4 → ℝ) y (Fin.rev i)
    simpa [revTuple] using this
  rwa [he] at h
theorem measurableEmbedding_revTuple (q : ℕ) :
    MeasurableEmbedding (revTuple : PointTuple q → PointTuple q) := by
  have he : (MeasurableEquiv.piCongrLeft (fun _ : Fin q => Fin 4 → ℝ) (Fin.revPerm (n := q)) :
      PointTuple q → PointTuple q) = revTuple := by
    funext y i
    have := MeasurableEquiv.piCongrLeft_apply_apply (Fin.revPerm (n := q))
      (β := fun _ : Fin q => Fin 4 → ℝ) y (Fin.rev i)
    simpa [revTuple] using this
  rw [← he]
  exact MeasurableEquiv.measurableEmbedding _
theorem appendTuples_eq_comp (q q' : ℕ) :
    (fun p : PointTuple q × PointTuple q' => appendTuples p.1 p.2) =
      (MeasurableEquiv.piCongrLeft (fun _ : Fin (q + q') => Fin 4 → ℝ) finSumFinEquiv) ∘
        (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin q ⊕ Fin q' => Fin 4 → ℝ)).symm := by
  funext p i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · have := MeasurableEquiv.piCongrLeft_apply_apply (finSumFinEquiv (m := q) (n := q'))
      (β := fun _ : Fin (q + q') => Fin 4 → ℝ) ((MeasurableEquiv.sumPiEquivProdPi
        (fun _ : Fin q ⊕ Fin q' => Fin 4 → ℝ)).symm p) (Sum.inl a)
    simp only [finSumFinEquiv_apply_left] at this
    simp only [Function.comp, this, appendTuples, Fin.append_left]
    rfl
  · have := MeasurableEquiv.piCongrLeft_apply_apply (finSumFinEquiv (m := q) (n := q'))
      (β := fun _ : Fin (q + q') => Fin 4 → ℝ) ((MeasurableEquiv.sumPiEquivProdPi
        (fun _ : Fin q ⊕ Fin q' => Fin 4 → ℝ)).symm p) (Sum.inr b)
    simp only [finSumFinEquiv_apply_right] at this
    simp only [Function.comp, this, appendTuples, Fin.append_right]
    rfl
def concatPair {n' n : ℕ} (y : PointTuple (n' + 1)) (x : PointTuple (n + 1)) :
    PointTuple (n' + 1 + n + 1) :=
  appendTuples (q := n' + 1) (q' := n + 1) y x
theorem measurePreserving_appendTuples (q q' : ℕ) :
    MeasurePreserving (fun p : PointTuple q × PointTuple q' => appendTuples p.1 p.2)
      (volume.prod volume) volume := by
  rw [appendTuples_eq_comp q q']
  exact (volume_measurePreserving_piCongrLeft (fun _ : Fin (q + q') => Fin 4 → ℝ)
    finSumFinEquiv).comp (volume_measurePreserving_sumPiEquivProdPi_symm
      (fun _ : Fin q ⊕ Fin q' => Fin 4 → ℝ))
theorem measurableEmbedding_appendTuples (q q' : ℕ) :
    MeasurableEmbedding (fun p : PointTuple q × PointTuple q' => appendTuples p.1 p.2) := by
  rw [appendTuples_eq_comp q q']
  exact (MeasurableEquiv.measurableEmbedding _).comp (MeasurableEquiv.measurableEmbedding _)
theorem measurePreserving_concatPair (n' n : ℕ) :
    MeasurePreserving (fun p : PointTuple (n' + 1) × PointTuple (n + 1) => concatPair p.1 p.2)
      (volume.prod volume) volume :=
  measurePreserving_appendTuples (n' + 1) (n + 1)
theorem measurableEmbedding_concatPair (n' n : ℕ) :
    MeasurableEmbedding (fun p : PointTuple (n' + 1) × PointTuple (n + 1) => concatPair p.1 p.2) :=
  measurableEmbedding_appendTuples (n' + 1) (n + 1)
theorem cumulativeSums_succ_eq {n : ℕ} (Y : PointTuple (n + 1)) (i : Fin n) :
    cumulativeSums Y i.succ = cumulativeSums Y i.castSucc + Y i.succ := by apply _root_.YangMills.Construction.TubeMatrixElements.cumulativeSums_succ <;> assumption
theorem cumulativeSums_zero_eq {n : ℕ} (Y : PointTuple (n + 1)) : cumulativeSums Y 0 = Y 0 := by apply _root_.YangMills.Construction.SmearedBoundaryVectors.cumulativeSums_zero <;> assumption
def mirroredSums {n' n : ℕ} (Y' : PointTuple (n' + 1)) (Y : PointTuple (n + 1)) :
    PointTuple (n' + 1 + (n + 1)) :=
  appendTuples (-revTuple (cumulativeSums Y')) (cumulativeSums Y)
def realSuccDiffs {m : ℕ} (T : PointTuple (m + 1)) : PointTuple m :=
  fun k => T k.succ - T k.castSucc
def combinedImPart {n' n : ℕ} (Y' : PointTuple (n' + 1)) (Y : PointTuple (n + 1)) :
    PointTuple (n' + 1 + n) :=
  realSuccDiffs (m := n' + 1 + n) (mirroredSums Y' Y)
theorem mirroredSums_castAdd {n' n : ℕ} (Y' : PointTuple (n' + 1)) (Y : PointTuple (n + 1))
    (a : Fin (n' + 1)) :
    mirroredSums Y' Y (Fin.castAdd (n + 1) a) = -cumulativeSums Y' (Fin.rev a) := by
  simp [mirroredSums, appendTuples, revTuple]
theorem mirroredSums_natAdd {n' n : ℕ} (Y' : PointTuple (n' + 1)) (Y : PointTuple (n + 1))
    (b : Fin (n + 1)) :
    mirroredSums Y' Y (Fin.natAdd (n' + 1) b) = cumulativeSums Y b := by
  simp [mirroredSums, appendTuples]
theorem combinedImPart_apply {n' n : ℕ} (Y' : PointTuple (n' + 1)) (Y : PointTuple (n + 1))
    (k : Fin (n' + 1 + n)) :
    combinedImPart Y' Y k =
      mirroredSums Y' Y (k.succ : Fin (n' + 1 + (n + 1))) -
        mirroredSums Y' Y (k.castSucc : Fin (n' + 1 + (n + 1))) :=
  rfl
theorem combinedImPart_mem {n' n : ℕ} (S : Set (Fin 4 → ℝ))
    (hS : ∀ a ∈ S, ∀ b ∈ S, a + b ∈ S) (Y' : PointTuple (n' + 1)) (Y : PointTuple (n + 1))
    (hY' : ∀ i, Y' i ∈ S) (hY : ∀ i, Y i ∈ S) (k : Fin (n' + 1 + n)) :
    combinedImPart Y' Y k ∈ S := by
  have hk := k.isLt
  rcases lt_trichotomy k.val n' with h | h | h
  · let a : Fin n' := ⟨k.val, h⟩
    have h1 : (k.castSucc : Fin (n' + 1 + (n + 1))) = Fin.castAdd (n + 1) a.castSucc := by
      apply Fin.ext; simp [a]
    have h2 : (k.succ : Fin (n' + 1 + (n + 1))) = Fin.castAdd (n + 1) a.succ := by
      apply Fin.ext; simp [a]
    have e : combinedImPart Y' Y k = Y' (Fin.rev a).succ := by
      rw [combinedImPart_apply, h1, h2, mirroredSums_castAdd, mirroredSums_castAdd, Fin.rev_succ,
        Fin.rev_castSucc, cumulativeSums_succ_eq]
      abel
    rw [e]
    exact hY' _
  · have h1 : (k.castSucc : Fin (n' + 1 + (n + 1))) = Fin.castAdd (n + 1) (Fin.last n') := by
      apply Fin.ext; simp [h]
    have h2 : (k.succ : Fin (n' + 1 + (n + 1))) = Fin.natAdd (n' + 1) (0 : Fin (n + 1)) := by
      apply Fin.ext; simp [h]
    have e : combinedImPart Y' Y k = Y 0 + Y' 0 := by
      rw [combinedImPart_apply, h1, h2, mirroredSums_castAdd, mirroredSums_natAdd]
      simp [cumulativeSums_zero_eq]
    rw [e]
    exact hS _ (hY _) _ (hY' _)
  · have hlt : k.val - (n' + 1) < n := by omega
    let a : Fin n := ⟨k.val - (n' + 1), hlt⟩
    have h1 : (k.castSucc : Fin (n' + 1 + (n + 1))) = Fin.natAdd (n' + 1) a.castSucc := by
      apply Fin.ext; simp [a]; omega
    have h2 : (k.succ : Fin (n' + 1 + (n + 1))) = Fin.natAdd (n' + 1) a.succ := by
      apply Fin.ext; simp [a]; omega
    have e : combinedImPart Y' Y k = Y a.succ := by
      rw [combinedImPart_apply, h1, h2, mirroredSums_natAdd, mirroredSums_natAdd,
        cumulativeSums_succ_eq]
      abel
    rw [e]
    exact hY _
theorem continuous_cumulativeSums_tuple {n : ℕ} :
    Continuous (cumulativeSums : PointTuple (n + 1) → PointTuple (n + 1)) := by apply _root_.YangMills.Construction.SmearedBoundaryVectors.continuous_cumulativeSums <;> assumption
theorem continuous_combinedImPart {n' n : ℕ} :
    Continuous fun p : PointTuple (n' + 1) × PointTuple (n + 1) => combinedImPart p.1 p.2 := by
  have hT : Continuous fun p : PointTuple (n' + 1) × PointTuple (n + 1) => mirroredSums p.1 p.2 := by
    refine continuous_pi fun i => ?_
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · simp only [mirroredSums_castAdd]
      exact (continuous_pi_iff.1 (continuous_cumulativeSums_tuple.comp continuous_fst)
        (Fin.rev a)).neg
    · simp only [mirroredSums_natAdd]
      exact continuous_pi_iff.1 (continuous_cumulativeSums_tuple.comp continuous_snd) b
  exact continuous_pi fun k => (continuous_pi_iff.1 hT _).sub (continuous_pi_iff.1 hT _)
theorem combinedImPart_zero {n' n : ℕ} :
    combinedImPart (0 : PointTuple (n' + 1)) (0 : PointTuple (n + 1)) = 0 := by
  have h0 : ∀ {m : ℕ}, cumulativeSums (0 : PointTuple (m + 1)) = 0 := by
    intro m
    funext k
    simp [cumulativeSums]
  have hT : mirroredSums (0 : PointTuple (n' + 1)) (0 : PointTuple (n + 1)) = 0 := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · simp [mirroredSums, appendTuples, h0, revTuple]
    · simp [mirroredSums, appendTuples, h0]
  funext k
  simp only [combinedImPart, realSuccDiffs, hT]
  simp
theorem imPart_diffCoords_shift {n : ℕ} (x V : PointTuple (n + 1)) (k : Fin (n + 1)) :
    MinkowskiSpace.imPart
        (MinkowskiSpace.diffCoords (tupleToComplex x + Complex.I • tupleToComplex V) k) =
      MinkowskiSpace.rePart (MinkowskiSpace.diffCoords (tupleToComplex V) k) := by
  refine Fin.cases ?_ (fun i => ?_) k
  · funext μ
    simp [MinkowskiSpace.diffCoords, MinkowskiSpace.imPart, MinkowskiSpace.rePart,
      tupleToComplex, toComplex]
  · funext μ
    simp [MinkowskiSpace.diffCoords, successiveDiffs, MinkowskiSpace.imPart,
      MinkowskiSpace.rePart, tupleToComplex, toComplex]
theorem shift_mem_diffCoordsInTube {n : ℕ} (x Y : PointTuple (n + 1))
    (hY : Y ∈ futureConeTuples (n + 1)) :
    tupleToComplex x + Complex.I • tupleToComplex (cumulativeSums Y) ∈ diffCoordsInTube (n + 1) := by
  change MinkowskiSpace.diffCoords _ ∈ WightmanTheory.tubeTuples (n + 1)
  intro k _
  change MinkowskiSpace.imPart _ ∈ futureCone
  rw [imPart_diffCoords_shift, MinkowskiSpace.diffCoords_cumulativeSums]
  have : MinkowskiSpace.rePart (tupleToComplex Y k) = Y k := by
    funext μ
    simp [MinkowskiSpace.rePart, tupleToComplex, toComplex]
  rw [this]
  exact hY k
theorem conjPoint_shift (a b : RealVec4) :
    conjPoint (toComplex a + Complex.I • toComplex b) = toComplex a + Complex.I • toComplex (-b) := by
  funext μ
  simp [conjPoint, MinkowskiSpace.rePart, MinkowskiSpace.imPart, toComplex]
  ring
theorem append_conjPoint_shift {n' n : ℕ} (y : PointTuple (n' + 1)) (x : PointTuple (n + 1))
    (Y' : PointTuple (n' + 1)) (Y : PointTuple (n + 1)) :
    Fin.append (fun k => conjPoint ((tupleToComplex y + Complex.I • tupleToComplex (cumulativeSums Y'))
        (Fin.rev k))) (tupleToComplex x + Complex.I • tupleToComplex (cumulativeSums Y)) =
      tupleToComplex (concatPair (revTuple y) x) +
        Complex.I • tupleToComplex (mirroredSums Y' Y) := by
  funext i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · have h := conjPoint_shift (y (Fin.rev a)) (cumulativeSums Y' (Fin.rev a))
    simp only [Fin.append_left, Pi.add_apply, Pi.smul_apply, tupleToComplex, mirroredSums_castAdd,
      concatPair, appendTuples]
    simp only [revTuple]
    exact h
  · simp only [Fin.append_right, Pi.add_apply, Pi.smul_apply, tupleToComplex, mirroredSums_natAdd,
      concatPair, appendTuples]
theorem successiveDiffs_shift {m : ℕ} (u T : PointTuple (m + 1)) :
    successiveDiffs (tupleToComplex u + Complex.I • tupleToComplex T) =
      successiveDiffs (tupleToComplex u) + Complex.I • tupleToComplex (realSuccDiffs T) := by
  funext k μ
  simp [successiveDiffs, tupleToComplex, toComplex, realSuccDiffs]
  ring
section Vectors
set_option linter.unusedSectionVars false
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (E : FourBorelSet → BddOp K) (Ω : K) (A : ℝ → BddOp K)
theorem inner_shiftedStateVector (hV : StatesTranslateInner E Ω A) {n' n : ℕ}
    (Y' : PointTuple (n' + 1)) (Y : PointTuple (n + 1)) (hY' : Y' ∈ futureConeTuples (n' + 1))
    (hY : Y ∈ futureConeTuples (n + 1)) (y : PointTuple (n' + 1)) (x : PointTuple (n + 1)) :
    ⟪shiftedStateVector E Ω A Y' y, shiftedStateVector E Ω A Y x⟫_ℂ =
      vacuumExpectation E Ω A (n' + 1 + n + 1)
        (successiveDiffs (tupleToComplex (concatPair (revTuple y) x)) +
          Complex.I • tupleToComplex (combinedImPart Y' Y)) := by
  have h0 : MinkowskiSpace.imPart (0 : ComplexVec4) ∈ closedFutureCone := by
    have : MinkowskiSpace.imPart (0 : ComplexVec4) = 0 := by
      funext μ
      simp [MinkowskiSpace.imPart]
    rw [this]
    simp [closedFutureCone, coneGap, spacePart, spaceNorm]
  have h := (hV (n + 1) (n' + 1) _ _ 0 (shift_mem_diffCoordsInTube x Y hY)
    (shift_mem_diffCoordsInTube y Y' hY') h0).2.2
  rw [append_conjPoint_shift] at h
  have hd := successiveDiffs_shift (m := n' + 1 + n) (concatPair (revTuple y) x)
    (mirroredSums Y' Y)
  exact h.trans (congrArg _ hd)
theorem inner_smearedState (hw : HilbertWellDefined.WeakIntegralUnique)
    {n' n : ℕ} (Y' : PointTuple (n' + 1)) (Y : PointTuple (n + 1)) (ψ : PointTuple (n' + 1) → ℂ)
    (φ : PointTuple (n + 1) → ℂ)
    (hP : HasWeakIntegrandData Set.univ (shiftedStateVector E Ω A Y') ψ)
    (hQ : HasWeakIntegrandData Set.univ (shiftedStateVector E Ω A Y) φ)
    (hin : ∀ y x, ⟪shiftedStateVector E Ω A Y' y, shiftedStateVector E Ω A Y x⟫_ℂ =
      vacuumExpectation E Ω A (n' + 1 + n + 1)
        (successiveDiffs (tupleToComplex (concatPair (revTuple y) x)) +
          Complex.I • tupleToComplex (combinedImPart Y' Y)))
    (Φ : PointTuple (n' + 1 + n + 1) → ℂ)
    (hΦ : ∀ y x, Φ (concatPair y x) = conj (ψ (revTuple y)) * φ x)
    (hint : Integrable (vacuumIntegrand E Ω A Φ (combinedImPart Y' Y))) :
    ⟪smearedState E Ω A Y' ψ, smearedState E Ω A Y φ⟫_ℂ =
      ∫ u, vacuumIntegrand E Ω A Φ (combinedImPart Y' Y) u := by
  have wP := (hw K (PointTuple (n' + 1)) Set.univ _ ψ hP).1
  have wQ := (hw K (PointTuple (n + 1)) Set.univ _ φ hQ).1
  have h1 := wQ (smearedState E Ω A Y' ψ)
  rw [Measure.restrict_univ] at h1
  have h2 : ∀ x, ⟪smearedState E Ω A Y' ψ, shiftedStateVector E Ω A Y x⟫_ℂ =
      ∫ y, conj (ψ y) * ⟪shiftedStateVector E Ω A Y' y, shiftedStateVector E Ω A Y x⟫_ℂ := by
    intro x
    have h := wP (shiftedStateVector E Ω A Y x)
    rw [Measure.restrict_univ] at h
    rw [← inner_conj_symm]
    change conj ⟪shiftedStateVector E Ω A Y x, weakInt Set.univ _ ψ⟫_ℂ = _
    rw [h, ← integral_conj]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp [inner_conj_symm]
  have mp := measurePreserving_concatPair n' n
  have me := measurableEmbedding_concatPair n' n
  set f := vacuumIntegrand E Ω A Φ (combinedImPart Y' Y) with hf
  have h3 : ∫ u, f u = ∫ p : PointTuple (n' + 1) × PointTuple (n + 1), f (concatPair p.1 p.2) :=
    (mp.integral_comp me f).symm
  have hi : Integrable (fun p : PointTuple (n' + 1) × PointTuple (n + 1) => f (concatPair p.1 p.2))
      (volume.prod volume) := (mp.integrable_comp_emb me).2 hint
  have h3' : ∫ u, f u = ∫ x, ∫ y, f (concatPair y x) :=
    h3.trans (integral_prod_symm _ hi)
  rw [h3']
  change ⟪smearedState E Ω A Y' ψ, weakInt Set.univ _ φ⟫_ℂ = _
  rw [h1]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  change φ x * _ = _
  rw [h2 x, ← integral_const_mul,
    ← (measurePreserving_revTuple (n' + 1)).integral_comp
      (measurableEmbedding_revTuple (n' + 1))]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  have hv := hin (revTuple y) x
  rw [revTuple_revTuple] at hv
  rw [hf]
  simp only [vacuumIntegrand]
  rw [hv, hΦ y x]
  ring
end Vectors
section Cones
variable (hm : MinkowskiSpace.ConeTubeLorentz.ConeGapBounds)
include hm
theorem futureCone_add : ∀ a ∈ futureCone, ∀ b ∈ futureCone, a + b ∈ futureCone := by
  intro a ha b hb
  have := hm.2.1 a b
  have ha' : coneGap a > 0 := ha
  have hb' : coneGap b > 0 := hb
  change coneGap (a + b) > 0
  linarith
theorem closedFutureCone_add :
    ∀ a ∈ closedFutureCone, ∀ b ∈ closedFutureCone, a + b ∈ closedFutureCone := by
  intro a ha b hb
  have := hm.2.1 a b
  have ha' : coneGap a ≥ 0 := ha
  have hb' : coneGap b ≥ 0 := hb
  change coneGap (a + b) ≥ 0
  linarith
omit hm in
theorem mem_closedFutureCone_of_mem {a : RealVec4} (ha : a ∈ futureCone) :
    a ∈ closedFutureCone := by apply _root_.YangMills.Construction.WightmanLocality.closedFutureCone_of_futureCone <;> assumption
omit hm in
theorem zero_mem_closedFutureCone : (0 : RealVec4) ∈ closedFutureCone := by apply _root_.YangMills.Construction.WightmanLocality.origin_mem_closedFutureCone <;> assumption
theorem nhdsWithin_futureConeTuples_neBot (m : ℕ) :
    (𝓝[futureConeTuples m] (0 : PointTuple m)).NeBot := by
  have he : coneGap timeUnit > 0 := by
    simp [coneGap, timeUnit, mkTimeSpace, spacePart, spaceNorm]
  let f : ℝ → PointTuple m := fun t => t • (fun _ => timeUnit)
  have hf : Tendsto f (𝓝[>] 0) (𝓝 0) := by
    have : Continuous f := by fun_prop
    have h := (this.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa [f] using h
  have hmem : ∀ᶠ t in 𝓝[>] (0 : ℝ), f t ∈ futureConeTuples m := by
    filter_upwards [self_mem_nhdsWithin] with t ht i
    change coneGap (t • timeUnit) > 0
    rw [hm.1 t timeUnit (le_of_lt ht)]
    exact mul_pos ht he
  exact mem_closure_iff_nhdsWithin_neBot.1 (mem_closure_of_tendsto hf hmem)
end Cones
section Limits
set_option linter.unusedSectionVars false
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (E : FourBorelSet → BddOp K) (Ω : K) (A : ℝ → BddOp K)
set_option maxHeartbeats 1600000 in
theorem inner_testState_succ_succ (hm : MinkowskiSpace.ConeTubeLorentz.ConeGapBounds)
    (hw : HilbertWellDefined.WeakIntegralUnique)
    (hV : StatesTranslateInner E Ω A) {℘ C : ℝ}
    (hB : SmearedBoundaryVectors.Properties E Ω A ℘ C)
    (hW : WightmanBoundaryValues.BoundaryValueProperties E Ω A ℘ C)
    (hI : ∀ (n : ℕ) (Y : PointTuple (n + 1)) (φ : PointTuple (n + 1) → ℂ),
      Y ∈ futureConeTuples (n + 1) → φ ∈ schwartzSet (n + 1) →
        HasWeakIntegrandData Set.univ (shiftedStateVector E Ω A Y) φ)
    {n' n : ℕ} (ψ : PointTuple (n' + 1) → ℂ) (φ : PointTuple (n + 1) → ℂ)
    (hψ : ψ ∈ schwartzSet (n' + 1)) (hφ : φ ∈ schwartzSet (n + 1))
    (Φ : PointTuple (n' + 1 + n + 1) → ℂ) (hΦs : Φ ∈ schwartzSet (n' + 1 + n + 1))
    (hΦ : ∀ y x, Φ (concatPair y x) = conj (ψ (revTuple y)) * φ x) :
    ⟪testState E Ω A (n' + 1) ψ, testState E Ω A (n + 1) φ⟫_ℂ =
      wightmanFunctional E Ω A (n' + 1 + n + 1) Φ := by
  obtain ⟨F, hFc, hFeq, hF0⟩ := hW.exists_continuousOn_extension (n' + 1 + n) Φ hΦs
  have hopen : ∀ Y' ∈ futureConeTuples (n' + 1), ∀ Y ∈ futureConeTuples (n + 1),
      combinedImPart Y' Y ∈ futureConeTuples (n' + 1 + n) := fun Y' hY' Y hY k =>
    combinedImPart_mem _ (futureCone_add hm) Y' Y hY' hY k
  have hclosed : ∀ Y' ∈ closedFutureConeTuples (n' + 1), ∀ Y ∈ closedFutureConeTuples (n + 1),
      combinedImPart Y' Y ∈ closedFutureConeTuples (n' + 1 + n) := fun Y' hY' Y hY k =>
    combinedImPart_mem _ (closedFutureCone_add hm) Y' Y hY' hY k
  have hoc : ∀ {m : ℕ} {Y : PointTuple m}, Y ∈ futureConeTuples m → Y ∈ closedFutureConeTuples m :=
    fun hY i => mem_closedFutureCone_of_mem (hY i)
  have h0c : ∀ {m : ℕ}, (0 : PointTuple m) ∈ closedFutureConeTuples m :=
    fun _ => zero_mem_closedFutureCone
  have hcont := continuous_combinedImPart (n' := n') (n := n)
  have := nhdsWithin_futureConeTuples_neBot hm (n + 1)
  have := nhdsWithin_futureConeTuples_neBot hm (n' + 1)
  have step1 : ∀ Y' ∈ futureConeTuples (n' + 1),
      ⟪smearedState E Ω A Y' ψ, testState E Ω A (n + 1) φ⟫_ℂ =
        F (combinedImPart Y' 0) := by
    intro Y' hY'
    have t1 := hB.isBoundaryLimit_testState n φ hφ (smearedState E Ω A Y' ψ)
    have hc1 : Continuous fun Y : PointTuple (n + 1) => combinedImPart Y' Y :=
      hcont.comp (Continuous.prodMk_right Y')
    have t2 : Tendsto (fun Y => F (combinedImPart Y' Y))
        (𝓝[futureConeTuples (n + 1)] 0) (𝓝 (F (combinedImPart Y' 0))) := by
      refine ((hFc _ (hclosed _ (hoc hY') _ h0c)).tendsto).comp ?_
      refine tendsto_nhdsWithin_iff.2 ⟨(hc1.tendsto 0).mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with Y hY
      exact hclosed _ (hoc hY') _ (hoc hY)
    have e : (fun Y => ⟪smearedState E Ω A Y' ψ, smearedState E Ω A Y φ⟫_ℂ)
        =ᶠ[𝓝[futureConeTuples (n + 1)] 0] fun Y => F (combinedImPart Y' Y) := by
      filter_upwards [self_mem_nhdsWithin] with Y hY
      have hint := hW.integrable_vacuumIntegrand (n' + 1 + n) Φ hΦs _ (hopen Y' hY' Y hY)
      rw [hFeq _ (hopen Y' hY' Y hY)]
      exact inner_smearedState E Ω A hw Y' Y ψ φ (hI n' Y' ψ hY' hψ) (hI n Y φ hY hφ)
        (inner_shiftedStateVector E Ω A hV Y' Y hY' hY) Φ hΦ hint
    exact tendsto_nhds_unique (t1.congr' e) t2
  have t3 : Tendsto (fun Y' => ⟪smearedState E Ω A Y' ψ, testState E Ω A (n + 1) φ⟫_ℂ)
      (𝓝[futureConeTuples (n' + 1)] 0)
      (𝓝 ⟪testState E Ω A (n' + 1) ψ, testState E Ω A (n + 1) φ⟫_ℂ) := by
    have h := hB.isBoundaryLimit_testState n' ψ hψ (testState E Ω A (n + 1) φ)
    have h' := (Complex.continuous_conj.tendsto _).comp h
    simpa [Function.comp_def, inner_conj_symm] using h'
  have hc2 : Continuous fun Y' : PointTuple (n' + 1) => combinedImPart Y' 0 :=
    hcont.comp (Continuous.prodMk_left 0)
  have t4 : Tendsto (fun Y' => F (combinedImPart Y' 0))
      (𝓝[futureConeTuples (n' + 1)] 0) (𝓝 (F (combinedImPart 0 0))) := by
    refine ((hFc _ (hclosed _ h0c _ h0c)).tendsto).comp ?_
    refine tendsto_nhdsWithin_iff.2 ⟨(hc2.tendsto 0).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with Y hY
    exact hclosed _ (hoc hY) _ h0c
  have e2 : (fun Y' => ⟪smearedState E Ω A Y' ψ, testState E Ω A (n + 1) φ⟫_ℂ)
      =ᶠ[𝓝[futureConeTuples (n' + 1)] 0] fun Y' => F (combinedImPart Y' 0) := by
    filter_upwards [self_mem_nhdsWithin] with Y' hY'
    exact step1 Y' hY'
  have := tendsto_nhds_unique (t3.congr' e2) t4
  rw [this, combinedImPart_zero]
  exact hF0
theorem reflectTuple_successiveDiffs {m : ℕ} (x : PointTuple (m + 1)) (Y : PointTuple m) :
    reflectTuple (successiveDiffs (tupleToComplex x) + Complex.I • tupleToComplex Y) =
      successiveDiffs (tupleToComplex (revTuple x)) + Complex.I • tupleToComplex (revTuple Y) := by
  funext k μ
  have hs : (Fin.rev k).succ = Fin.rev k.castSucc := (Fin.rev_castSucc k).symm
  have hc : (Fin.rev k).castSucc = Fin.rev k.succ := (Fin.rev_succ k).symm
  simp only [reflectTuple, conjPoint, successiveDiffs, tupleToComplex, Pi.add_apply, Pi.smul_apply,
    Pi.sub_apply, Pi.neg_apply, MinkowskiSpace.rePart, MinkowskiSpace.imPart, toComplex,
    revTuple, hs, hc]
  simp
  ring
theorem conj_wightmanFunctional (hm : MinkowskiSpace.ConeTubeLorentz.ConeGapBounds)
    (hc : ExpectationConj E Ω A) {℘ C : ℝ}
    (hW : WightmanBoundaryValues.BoundaryValueProperties E Ω A ℘ C)
    {n : ℕ} (ψ : PointTuple (n + 1) → ℂ) (hψ : ψ ∈ schwartzSet (n + 1))
    (hψ' : starFun ψ ∈ schwartzSet (n + 1)) :
    conj (wightmanFunctional E Ω A (n + 1) ψ) = wightmanFunctional E Ω A (n + 1) (starFun ψ) := by
  obtain ⟨F, hFc, hFeq, hF0⟩ := hW.exists_continuousOn_extension n ψ hψ
  obtain ⟨F', hFc', hFeq', hF0'⟩ := hW.exists_continuousOn_extension n _ hψ'
  have hrev : ∀ Y ∈ futureConeTuples n, revTuple Y ∈ futureConeTuples n :=
    fun Y hY i => hY _
  have hoc : ∀ {Y : PointTuple n}, Y ∈ futureConeTuples n → Y ∈ closedFutureConeTuples n :=
    fun hY i => mem_closedFutureCone_of_mem (hY i)
  have h0c : (0 : PointTuple n) ∈ closedFutureConeTuples n := fun _ => zero_mem_closedFutureCone
  have := nhdsWithin_futureConeTuples_neBot hm n
  have e : ∀ Y ∈ futureConeTuples n, conj (F Y) = F' (revTuple Y) := by
    intro Y hY
    have hsub := (measurePreserving_revTuple (n + 1)).integral_comp
      (measurableEmbedding_revTuple (n + 1))
      (vacuumIntegrand E Ω A (starFun ψ) (revTuple Y))
    rw [hFeq Y hY, hFeq' _ (hrev Y hY), ← integral_conj, ← hsub]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [vacuumIntegrand, map_mul]
    have htube : successiveDiffs (tupleToComplex x) + Complex.I • tupleToComplex Y ∈
        WightmanTheory.tubeTuples n := by
      intro k _
      have : MinkowskiSpace.imPart
          ((successiveDiffs (tupleToComplex x) + Complex.I • tupleToComplex Y) k) = Y k := by
        funext μ
        simp [MinkowskiSpace.imPart, successiveDiffs, tupleToComplex, toComplex]
      change MinkowskiSpace.imPart _ ∈ futureCone
      rw [this]
      exact hY k
    have h1 := hc (n + 1) _ htube
    have h2 : starFun ψ (revTuple x) = conj (ψ x) := by
      simp only [starFun]
      congr 2
      funext i
      simp [revTuple]
    rw [h2]
    have h3 := reflectTuple_successiveDiffs x Y
    rw [h1, h3]
  have t1 : Tendsto (fun Y => conj (F Y)) (𝓝[futureConeTuples n] 0)
      (𝓝 (conj (F 0))) := by
    refine (Complex.continuous_conj.tendsto _).comp ?_
    refine ((hFc _ h0c).tendsto).mono_left (nhdsWithin_mono _ fun Y hY => hoc hY)
  have hcr : Continuous (revTuple : PointTuple n → PointTuple n) :=
    continuous_pi fun i => continuous_apply _
  have t2 : Tendsto (fun Y => F' (revTuple Y)) (𝓝[futureConeTuples n] 0) (𝓝 (F' 0)) := by
    have hr0 : revTuple (0 : PointTuple n) = 0 := rfl
    refine ((hFc' _ h0c).tendsto).comp ?_
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := (hcr.tendsto 0).mono_left (nhdsWithin_le_nhds (s := futureConeTuples n))
      rwa [hr0] at this
    · filter_upwards [self_mem_nhdsWithin] with Y hY
      exact hoc (hrev Y hY)
  have e' : (fun Y => conj (F Y)) =ᶠ[𝓝[futureConeTuples n] 0] fun Y => F' (revTuple Y) := by
    filter_upwards [self_mem_nhdsWithin] with Y hY
    exact e Y hY
  have := tendsto_nhds_unique (t1.congr' e') t2
  rw [← hF0, ← hF0', this]
end Limits
section Ends
set_option linter.unusedSectionVars false
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (E : FourBorelSet → BddOp K) (Ω : K) (A : ℝ → BddOp K)
theorem wightmanFunctional_of_eq_smul {℘ C : ℝ}
    (hB : SmearedBoundaryVectors.Properties E Ω A ℘ C) {n : ℕ}
    (φ : PointTuple (n + 1) → ℂ) (hφ : φ ∈ schwartzSet (n + 1)) (c : ℂ)
    (G : PointTuple (n + 1) → ℂ) (hG : G = fun x => c * φ x) :
    wightmanFunctional E Ω A (n + 1) G = c * wightmanFunctional E Ω A (n + 1) φ := by
  have h := hB.testState_linearCombination n φ φ hφ hφ c 0
  have he : c • φ + (0 : ℂ) • φ = G := by
    rw [hG]
    funext x
    simp
  rw [he] at h
  simp only [wightmanFunctional]
  rw [h]
  simp
theorem wightmanFunctional_tensorVal_scalar_left {℘ C : ℝ}
    (hB : SmearedBoundaryVectors.Properties E Ω A ℘ C) (c : ℂ) {n : ℕ}
    (φ : PointTuple (n + 1) → ℂ) (hφ : φ ∈ schwartzSet (n + 1)) :
    wightmanFunctional E Ω A (0 + (n + 1)) (tensorVal (q := 0) (q' := n + 1) c φ) =
      c * wightmanFunctional E Ω A (n + 1) φ := by
  have key : ∀ (N : ℕ) (h : N = n + 1) (G : Motions.TensorVal ℂ N),
      (∀ x : PointTuple N, valToFun G x = c * φ fun i => x (Fin.cast h.symm i)) →
        wightmanFunctional E Ω A N G = c * wightmanFunctional E Ω A (n + 1) φ := by
    intro N h G hG
    subst h
    exact wightmanFunctional_of_eq_smul E Ω A hB φ hφ c G (funext hG)
  refine key _ (Nat.zero_add _) _ fun x => ?_
  have h := valToFun_tensorVal (q := 0) (q' := n + 1) c φ
    (leftPart x) (rightPart x)
  rw [appendTuples_leftPart_rightPart] at h
  rw [h]
  have hl : rightPart (q := 0) (q' := n + 1) x =
      fun i => x (Fin.cast (Nat.zero_add _).symm i) := by
    funext j
    simp only [rightPart]
    congr 1
    apply Fin.ext
    simp
  rw [hl]
  rfl
theorem wightmanFunctional_tensorVal_scalar_right {℘ C : ℝ}
    (hB : SmearedBoundaryVectors.Properties E Ω A ℘ C) (c : ℂ) {n : ℕ}
    (F : PointTuple (n + 1) → ℂ) (hF : F ∈ schwartzSet (n + 1)) :
    wightmanFunctional E Ω A (n + 1 + 0) (tensorVal (q := n + 1) (q' := 0) F c) =
      c * wightmanFunctional E Ω A (n + 1) F := by
  refine wightmanFunctional_of_eq_smul E Ω A hB F hF c _ ?_
  funext x
  have h := valToFun_tensorVal (q := n + 1) (q' := 0) F c x default
  have hx : appendTuples (q := n + 1) (q' := 0) x default = x :=
    funext fun i => Fin.append_left x default i
  rw [hx] at h
  refine h.trans ?_
  exact mul_comm _ _
end Ends
theorem statement_holds (hB : SmearedBoundaryVectors.Statement)
    (hM : TubeMatrixElements.Statement)
    (hW : WightmanBoundaryValues.BoundaryValueTheorem)
    (hP : FieldForms.FieldProductProperties)
    (hS : RealPointVectors.SchwartzClosure)
    (hC : MinkowskiSpace.ConeTubeLorentz.Statement)
    (hI : HilbertWellDefined.WellDefinedStatement) : Statement := by
  intro K _ _ _ E Ω A ℘ C hform n' n ψ φ hψ hφ
  have hb := hB E Ω A ℘ C hform
  have hw := hW E Ω A ℘ C hform
  have hp := hP K E Ω A ℘ C hform
  have hm := hC.1
  have hwe := hI.2.2.2
  have hVS := hp.2.2.2.2.2.2.2.2.2.1
  have hCj := hp.2.2.2.2.2.2.2.2.2.2
  have hOne : ⟪Ω, Ω⟫_ℂ = 1 := by
    have h := hw.wightmanFunctional_zero 1
    simp only [wightmanFunctional, testState, scalarOfOrderZero] at h
    simpa using h
  rcases n' with _ | n' <;> rcases n with _ | n
  · have e : wightmanFunctional E Ω A (0 + 0) (tensorVal (q := 0) (q' := 0) (starVal ψ) φ) =
        conj (scalarOfOrderZero ψ) * scalarOfOrderZero φ := hw.wightmanFunctional_zero _
    rw [e]
    change ⟪scalarOfOrderZero ψ • Ω, scalarOfOrderZero φ • Ω⟫_ℂ = _
    rw [inner_smul_left, inner_smul_right, hOne, mul_one]
  · change ⟪scalarOfOrderZero ψ • Ω, testState E Ω A (n + 1) φ⟫_ℂ = _
    rw [inner_smul_left]
    exact (wightmanFunctional_tensorVal_scalar_left E Ω A hb (conj (scalarOfOrderZero ψ)) φ hφ).symm
  · change ⟪testState E Ω A (n' + 1) ψ, scalarOfOrderZero φ • Ω⟫_ℂ = _
    rw [inner_smul_right]
    have hd : starFun ψ ∈ schwartzSet (n' + 1) := hS.1 (n' + 1) ψ hψ
    have h1 := wightmanFunctional_tensorVal_scalar_right E Ω A hb (scalarOfOrderZero φ) _ hd
    have h2 := conj_wightmanFunctional E Ω A hm hCj hw ψ hψ hd
    refine Eq.trans ?_ h1.symm
    rw [← h2]
    simp [wightmanFunctional, inner_conj_symm]
  · refine inner_testState_succ_succ E Ω A hm hwe hVS hb hw
      (fun m Y f hY hf => ((hM E Ω A ℘ C hform m 0).2.2.2 Y hY f hf).1) ψ φ hψ hφ
      (tensorVal (q := n' + 1) (q' := n + 1) (starVal ψ) φ)
      (hS.2.1 (n' + 1) (n + 1) ψ φ hψ hφ) ?_
    intro y x
    exact valToFun_tensorVal (q := n' + 1) (q' := n + 1) (starVal ψ) φ y x
end YangMills.Construction.RealPointInnerProducts
