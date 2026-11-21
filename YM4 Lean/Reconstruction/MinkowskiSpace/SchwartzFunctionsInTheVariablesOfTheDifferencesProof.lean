import Reconstruction.MinkowskiSpace.BoundaryVectorsOfTheSmearedVectorsProof
import Reconstruction.MinkowskiSpace.MatrixElementsOfTheFieldVectorsOnTheTubeProof
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.DifferenceVariables
open MinkowskiSpace TestSpaces TubeBoundary RealPointVectors MotionsTranslations
variable {n : ℕ}
def cumSumMatrix (n : ℕ) : CoordMatrix (n + 1) :=
  fun a b => if b.1 ≤ a.1 ∧ b.2 = a.2 then 1 else 0
theorem affineApply_cumSumMatrix (x : PointTuple (n + 1)) :
    affineApply (cumSumMatrix n) 0 x = cumulativeSums x := by
  funext i μ
  have h : ∀ j : Fin (n + 1),
      ∑ ν : Fin 4, (if j ≤ i ∧ ν = μ then (1 : ℝ) else 0) * x j ν =
        if j ≤ i then x j μ else 0 := by
    intro j
    by_cases hj : j ≤ i <;> simp [hj]
  simp only [affineApply, cumSumMatrix, cumulativeSums, Pi.zero_apply, add_zero, Finset.sum_apply,
    Fintype.sum_prod_type, h]
  rw [← Finset.sum_filter]
  exact Finset.sum_congr (by ext j; simp) fun _ _ => rfl
theorem det_cumSumMatrix : (cumSumMatrix n).det = 1 := by
  have hb : (cumSumMatrix n).BlockTriangular (fun a => OrderDual.toDual a.1) := by
    intro a b h
    have hlt : a.1 < b.1 := h
    simp [cumSumMatrix, not_le.2 hlt]
  rw [Matrix.BlockTriangular.det hb]
  refine Finset.prod_eq_one fun k _ => ?_
  have e : (cumSumMatrix n).toSquareBlock (fun a => OrderDual.toDual a.1) k = 1 := by
    ext ⟨a, ha⟩ ⟨b, hb'⟩
    have hab : b.1 = a.1 := by
      have := ha.trans hb'.symm
      exact (OrderDual.toDual.injective this).symm
    simp only [Matrix.toSquareBlock, Matrix.toSquareBlockProp, Matrix.one_apply, Subtype.mk.injEq]
    by_cases h2 : b.2 = a.2
    · have : a = b := Prod.ext hab.symm h2.symm
      simp [this, cumSumMatrix]
    · have : a ≠ b := fun h => h2 (by rw [h])
      simp [cumSumMatrix, h2, this]
  rw [e, Matrix.det_one]
theorem isUnit_cumSumMatrix : IsUnit (cumSumMatrix n) := by apply _root_.YangMills.Construction.SmearedBoundaryVectors.isUnit_cumulativeSumsMatrix <;> assumption
theorem entryBound_cumSumMatrix : EntryBound (cumSumMatrix n) 1 := by
  refine ⟨le_rfl, fun a b => ?_⟩
  simp only [cumSumMatrix]
  split_ifs <;> simp
def cumSumLinearMap (n : ℕ) : PointTuple (n + 1) →ₗ[ℝ] PointTuple (n + 1) :=
  (LinearEquiv.curry ℝ ℝ (Fin (n + 1)) (Fin 4)).toLinearMap ∘ₗ Matrix.toLin' (cumSumMatrix n) ∘ₗ
    (LinearEquiv.curry ℝ ℝ (Fin (n + 1)) (Fin 4)).symm.toLinearMap
theorem cumSumLinearMap_apply (x : PointTuple (n + 1)) : cumSumLinearMap n x = cumulativeSums x := by
  rw [← affineApply_cumSumMatrix]
  funext i μ
  simp [cumSumLinearMap, affineApply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  rfl
theorem det_cumSumLinearMap : LinearMap.det (cumSumLinearMap n) = 1 := by
  have h := LinearMap.det_conj (Matrix.toLin' (cumSumMatrix n))
    (LinearEquiv.curry ℝ ℝ (Fin (n + 1)) (Fin 4))
  rw [LinearMap.det_toLin', det_cumSumMatrix] at h
  simpa [cumSumLinearMap, LinearMap.comp_assoc] using h
theorem continuous_cumulativeSums :
    Continuous (cumulativeSums : PointTuple (n + 1) → PointTuple (n + 1)) := by apply _root_.YangMills.Construction.SmearedBoundaryVectors.continuous_cumulativeSums <;> assumption
theorem measurePreserving_cumulativeSums :
    MeasurePreserving (cumulativeSums : PointTuple (n + 1) → PointTuple (n + 1)) volume volume := by
  refine ⟨continuous_cumulativeSums.measurable, ?_⟩
  have h : (cumulativeSums : PointTuple (n + 1) → PointTuple (n + 1)) = cumSumLinearMap n :=
    funext fun x => (cumSumLinearMap_apply x).symm
  rw [h, Measure.map_linearMap_addHaar_eq_smul_addHaar volume
    (by rw [det_cumSumLinearMap]; exact one_ne_zero), det_cumSumLinearMap]
  simp
theorem cumulativeSums_zero (x : PointTuple (n + 1)) : cumulativeSums x 0 = x 0 := by apply _root_.YangMills.Construction.SmearedBoundaryVectors.cumulativeSums_zero <;> assumption
theorem cumulativeSums_succ (x : PointTuple (n + 1)) (i : Fin n) :
    cumulativeSums x i.succ = cumulativeSums x i.castSucc + x i.succ := by apply _root_.YangMills.Construction.TubeMatrixElements.cumulativeSums_succ <;> assumption
theorem diffCoords_cumulativeSums (x Y : PointTuple (n + 1)) :
    MinkowskiSpace.diffCoords (tupleToComplex (cumulativeSums x) +
      Complex.I • tupleToComplex (cumulativeSums Y)) = tubePoint x Y := by
  funext k
  refine Fin.cases ?_ (fun i => ?_) k
  · funext μ
    simp [MinkowskiSpace.diffCoords, tubePoint, tupleToComplex, cumulativeSums_zero]
  · funext μ
    simp only [MinkowskiSpace.diffCoords, Fin.cons_succ, successiveDiffs, tubePoint, tupleToComplex,
      MinkowskiSpace.toComplex, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      cumulativeSums_succ]
    push_cast
    ring
theorem diffCoords_eq_affineComp (φ : PointTuple (n + 1) → ℂ) :
    RealPointVectors.diffCoords φ = affineComp (cumSumMatrix n) 0 φ := by
  funext x
  simp only [RealPointVectors.diffCoords, affineComp, affineApply_cumSumMatrix]
theorem diffCoords_mem_schwartzSet (h₁ : MotionsTranslations.Statement)
    {φ : PointTuple (n + 1) → ℂ} (hφ : φ ∈ schwartzSet (n + 1)) :
    RealPointVectors.diffCoords φ ∈ schwartzSet (n + 1) := by
  rw [diffCoords_eq_affineComp]
  exact (h₁.2.2.2.1 (n + 1) n.succ_pos φ hφ (cumSumMatrix n) 0 1 isUnit_cumSumMatrix
    entryBound_cumSumMatrix).2.1
theorem multiDeriv_single (k : Fin (n + 1)) (g : PointTuple (n + 1) → ℂ) :
    multiDeriv (Pi.single k (Pi.single 0 1) : MultiIdx4 (n + 1)) g =
      coordDeriv k 0 g := by
  let α : MultiIdx4 (n + 1) := Pi.single k (Pi.single 0 1)
  have inner : ∀ (i : Fin (n + 1)) (h : PointTuple (n + 1) → ℂ),
      (List.finRange 4).foldr (fun μ h' => (coordDeriv i μ)^[α i μ] h') h =
        if i = k then coordDeriv k 0 h else h := by
    intro i h
    have e : List.finRange 4 = [0, 1, 2, 3] := by decide
    rw [e]
    by_cases hik : i = k
    · subst hik
      simp [α]
    · simp [α, hik]
  have outer : ∀ L : List (Fin (n + 1)), L.Nodup →
      L.foldr (fun i h => (List.finRange 4).foldr
        (fun μ h' => (coordDeriv i μ)^[α i μ] h') h) g =
        if k ∈ L then coordDeriv k 0 g else g := by
    intro L
    induction L with
    | nil => simp
    | cons i L ih =>
      intro hL
      have hL' := List.nodup_cons.1 hL
      rw [List.foldr_cons, ih hL'.2, inner]
      simp only [List.mem_cons]
      by_cases hik : i = k
      · subst hik
        simp [hL'.1]
      · have : k ≠ i := fun h => hik h.symm
        simp [hik, this]
  simpa [multiDeriv, List.mem_finRange] using outer _ (List.nodup_finRange (n + 1))
theorem sum_smul_coordDeriv_mem (h₁ : MotionsTranslations.Statement)
    (h₂ : TestSpaces.Elementary.BasicProperties) {φ : PointTuple (n + 1) → ℂ}
    (hφ : φ ∈ schwartzSet (n + 1)) (c : Fin (n + 1) → ℂ) (S : Finset (Fin (n + 1))) :
    (fun x => ∑ i ∈ S, c i * coordDeriv i 0 φ x) ∈ schwartzSet (n + 1) := by
  classical
  have hadd := fun (f g : PointTuple (n + 1) → ℂ) (hf : f ∈ schwartzSet (n + 1))
      (hg : g ∈ schwartzSet (n + 1)) (z z' : ℂ) =>
    ((h₂ (n + 1) n.succ_pos).1.1 f hf g hg z z').1.1
  induction S using Finset.induction_on with
  | empty =>
    have h := hadd φ φ hφ hφ 0 0
    have e : TestSpaces.Elementary.linComb 0 φ 0 φ = fun _ => 0 := by
      funext x
      simp [TestSpaces.Elementary.linComb]
    rw [e] at h
    simpa using h
  | insert m S hm ih =>
    have hp : coordDeriv m 0 φ ∈ schwartzSet (n + 1) := by
      have h := (h₁.2.2.2.2 (n + 1) n.succ_pos φ hφ (Pi.single m (Pi.single 0 1))).1
      rwa [multiDeriv_single] at h
    have h := hadd _ _ hp ih (c m) 1
    have e : TestSpaces.Elementary.linComb (c m) (coordDeriv m 0 φ) 1
        (fun x => ∑ i ∈ S, c i * coordDeriv i 0 φ x) =
        fun x => ∑ i ∈ insert m S, c i * coordDeriv i 0 φ x := by
      funext x
      simp [TestSpaces.Elementary.linComb, Finset.sum_insert hm]
    rwa [e] at h
theorem timeWeightedDeriv_mem (h₁ : MotionsTranslations.Statement)
    (h₂ : TestSpaces.Elementary.BasicProperties) {φ : PointTuple (n + 1) → ℂ}
    (hφ : φ ∈ schwartzSet (n + 1)) :
    timeWeightedDeriv φ ∈ schwartzSet (n + 1) :=
  sum_smul_coordDeriv_mem h₁ h₂ hφ _ Finset.univ
theorem iterate_timeWeightedDeriv_mem (h₁ : MotionsTranslations.Statement)
    (h₂ : TestSpaces.Elementary.BasicProperties) {φ : PointTuple (n + 1) → ℂ}
    (hφ : φ ∈ schwartzSet (n + 1)) (j : ℕ) :
    timeWeightedDeriv^[j] φ ∈ schwartzSet (n + 1) := by
  induction j with
  | zero => exact hφ
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact timeWeightedDeriv_mem h₁ h₂ ih
def timeBasis (k : Fin (n + 1)) : PointTuple (n + 1) := Pi.single k (Pi.single 0 1)
theorem sum_cumulativeSums_timeBasis :
    ∑ k : Fin (n + 1), cumulativeSums (timeBasis k) =
      ∑ i : Fin (n + 1), (((i : ℕ) + 1 : ℕ) : ℝ) • timeBasis i := by
  funext i μ
  have hl : ∀ k : Fin (n + 1), cumulativeSums (timeBasis k) i μ =
      if k ≤ i then (Pi.single 0 1 : Fin 4 → ℝ) μ else 0 := by
    intro k
    simp only [cumulativeSums, timeBasis, Finset.sum_apply]
    by_cases hk : k ≤ i
    · rw [if_pos hk, Finset.sum_eq_single k]
      · simp
      · intro j _ hj
        simp [Pi.single_eq_of_ne hj]
      · intro h
        exact absurd (Finset.mem_Iic.2 hk) h
    · rw [if_neg hk]
      refine Finset.sum_eq_zero fun j hj => ?_
      have : j ≠ k := fun h => hk (h ▸ Finset.mem_Iic.1 hj)
      simp [Pi.single_eq_of_ne this]
  have hr : ∀ a : Fin (n + 1), ((((a : ℕ) + 1 : ℕ) : ℝ) • timeBasis a) i μ =
      if a = i then (((i : ℕ) + 1 : ℕ) : ℝ) * (Pi.single 0 1 : Fin 4 → ℝ) μ else 0 := by
    intro a
    by_cases ha : a = i
    · subst ha
      simp [timeBasis]
    · have : i ≠ a := fun h => ha h.symm
      simp [timeBasis, ha]
  simp only [Finset.sum_apply, hl, hr]
  rw [Finset.sum_ite_eq' Finset.univ i, if_pos (Finset.mem_univ i), ← Finset.sum_filter,
    Finset.sum_const, nsmul_eq_mul]
  have hc : (Finset.univ.filter fun k : Fin (n + 1) => k ≤ i).card = (i : ℕ) + 1 := by
    have e : (Finset.univ.filter fun k : Fin (n + 1) => k ≤ i) = Finset.Iic i := by
      ext j
      simp
    rw [e, Fin.card_Iic]
  rw [hc]
theorem totalTimeDeriv_diffCoords {φ : PointTuple (n + 1) → ℂ}
    (hφ : Differentiable ℝ φ) :
    totalTimeDeriv (RealPointVectors.diffCoords φ) =
      RealPointVectors.diffCoords (timeWeightedDeriv φ) := by
  funext x
  let L : PointTuple (n + 1) →L[ℝ] PointTuple (n + 1) := (cumSumLinearMap n).toContinuousLinearMap
  have hL : ∀ y, L y = cumulativeSums y := fun y => cumSumLinearMap_apply y
  have hd : ∀ v, lineDeriv ℝ (RealPointVectors.diffCoords φ) x v =
      fderiv ℝ φ (cumulativeSums x) (cumulativeSums v) := by
    intro v
    have hf : HasFDerivAt (RealPointVectors.diffCoords φ)
        ((fderiv ℝ φ (cumulativeSums x)).comp L) x := by
      have h0 : HasFDerivAt φ (fderiv ℝ φ (L x)) (L x) := (hφ (L x)).hasFDerivAt
      have h1 := h0.comp x L.hasFDerivAt
      have e : RealPointVectors.diffCoords φ = φ ∘ L := by
        funext y
        simp [RealPointVectors.diffCoords, hL]
      rw [e, ← hL x]
      exact h1
    rw [hf.differentiableAt.lineDeriv_eq_fderiv, hf.fderiv]
    simp [hL]
  have hp : ∀ i, coordDeriv i 0 φ (cumulativeSums x) =
      fderiv ℝ φ (cumulativeSums x) (timeBasis i) := fun i =>
    (hφ _).lineDeriv_eq_fderiv
  have hl : ∀ k, coordDeriv k 0 (RealPointVectors.diffCoords φ) x =
      fderiv ℝ φ (cumulativeSums x) (cumulativeSums (timeBasis k)) := fun k => hd _
  simp only [totalTimeDeriv, hl]
  simp only [RealPointVectors.diffCoords]
  rw [← map_sum, sum_cumulativeSums_timeBasis, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Complex.real_smul, hp]
  push_cast
  rfl
theorem iterate_totalTimeDeriv_diffCoords (h₁ : MotionsTranslations.Statement)
    (h₂ : TestSpaces.Elementary.BasicProperties) (j : ℕ) :
    ∀ φ ∈ schwartzSet (n + 1),
      totalTimeDeriv^[j] (RealPointVectors.diffCoords φ) =
        RealPointVectors.diffCoords (timeWeightedDeriv^[j] φ) := by
  induction j with
  | zero => exact fun _ _ => rfl
  | succ j ih =>
    intro φ hφ
    have hdiff : Differentiable ℝ φ := hφ.1.differentiable (by simp)
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      totalTimeDeriv_diffCoords hdiff,
      ih _ (timeWeightedDeriv_mem h₁ h₂ hφ)]
theorem lOneNorm_diffCoords {g : PointTuple (n + 1) → ℂ} (hg : Continuous g) :
    WightmanReconstruction.lOneNorm (RealPointVectors.diffCoords g) =
      WightmanReconstruction.lOneNorm g := by apply _root_.YangMills.Construction.SmearedBoundaryVectors.lOneNorm_comp_cumulativeSums <;> assumption
theorem schwartzInDifferences (h₁ : MotionsTranslations.Statement)
    (h₂ : TestSpaces.Elementary.BasicProperties) : SchwartzInDifferences := by
  intro n
  refine ⟨measurePreserving_cumulativeSums, diffCoords_cumulativeSums, fun φ hφ =>
    ⟨diffCoords_mem_schwartzSet h₁ hφ, iterate_timeWeightedDeriv_mem h₁ h₂ hφ,
      fun j => iterate_totalTimeDeriv_diffCoords h₁ h₂ j φ hφ, fun k => ?_⟩⟩
  refine Finset.sup'_congr _ rfl fun j _ => ?_
  rw [iterate_totalTimeDeriv_diffCoords h₁ h₂ j φ hφ]
  exact lOneNorm_diffCoords (iterate_timeWeightedDeriv_mem h₁ h₂ hφ j).1.continuous
end YangMills.Construction.DifferenceVariables
