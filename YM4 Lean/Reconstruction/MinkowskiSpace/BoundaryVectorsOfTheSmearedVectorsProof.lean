import YangMills.Construction.Continuum.FirstFactsOnTheTestSpaces
import YangMills.Construction.Continuum.MotionsTensorProductsTranslationsAndTheReflection
import Reconstruction.MinkowskiSpace.BoundaryVectorsOfTheSmearedVectors
import Reconstruction.MinkowskiSpace.MatrixElementsOfTheFieldVectorsOnTheTube
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped ComplexConjugate InnerProductSpace Topology ContDiff
noncomputable section
namespace YangMills.Construction.SmearedBoundaryVectors
open MinkowskiSpace FieldForms TestSpaces WightmanReconstruction OneLoopNotation
  ComplexHilbert ProjectionMeasures RealPointVectors TubeBoundary MotionsTranslations
theorem sum_Iic_eq_sum_ite {X : Type*} [AddCommMonoid X] {m : ℕ} (f : Fin m → X) (i : Fin m) :
    ∑ j ∈ Finset.Iic i, f j = ∑ j, if j ≤ i then f j else 0 := by
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext j
  simp
theorem cumulativeSums_zero {n : ℕ} (x : PointTuple (n + 1)) : cumulativeSums x 0 = x 0 := by
  rw [cumulativeSums, sum_Iic_eq_sum_ite, Fin.sum_univ_succ]
  simp
theorem cumulativeSums_succ {n : ℕ} (x : PointTuple (n + 2)) (k : Fin (n + 1)) :
    cumulativeSums x k.succ = x 0 + cumulativeSums (fun j => x j.succ) k := by
  simp only [cumulativeSums, sum_Iic_eq_sum_ite]
  rw [Fin.sum_univ_succ]
  simp [Fin.succ_le_succ_iff]
theorem cumulativeSums_add_smul {n : ℕ} (x v : PointTuple (n + 1)) (t : ℝ) :
    cumulativeSums (x + t • v) = cumulativeSums x + t • cumulativeSums v := by
  funext k
  simp [cumulativeSums, Finset.sum_add_distrib, Finset.smul_sum]
theorem continuous_cumulativeSums {n : ℕ} :
    Continuous (cumulativeSums : PointTuple (n + 1) → PointTuple (n + 1)) :=
  continuous_pi fun _ => continuous_finsetSum _ fun j _ => continuous_apply j
theorem cumulativeSums_injective {n : ℕ} :
    Function.Injective (cumulativeSums : PointTuple (n + 1) → PointTuple (n + 1)) := by
  intro x y h
  have h' : tupleToComplex x = tupleToComplex y := by
    rw [← diffCoords_cumulativeSums x, ← diffCoords_cumulativeSums y, h]
  funext i μ
  have := congrFun (congrFun h' i) μ
  simpa [tupleToComplex, toComplex] using this
theorem measurePreserving_cumulativeSums : ∀ n : ℕ,
    MeasurePreserving (cumulativeSums : PointTuple (n + 1) → PointTuple (n + 1)) volume volume
  | 0 => by
    have h : (cumulativeSums : PointTuple 1 → PointTuple 1) = id := by
      funext x k
      rw [Fin.fin_one_eq_zero k, cumulativeSums_zero]
      rfl
    rw [h]
    exact MeasurePreserving.id _
  | n + 1 => by
    have ih := measurePreserving_cumulativeSums n
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 2) => Fin 4 → ℝ) 0
    have he : MeasurePreserving e volume volume :=
      volume_preserving_piFinSuccAbove (fun _ : Fin (n + 2) => Fin 4 → ℝ) 0
    let g : (Fin 4 → ℝ) → PointTuple (n + 1) → PointTuple (n + 1) :=
      fun y Y k => y + cumulativeSums Y k
    have hgm : Measurable (Function.uncurry g) := by
      apply Continuous.measurable
      refine continuous_pi fun k => continuous_fst.add ?_
      exact (continuous_apply k).comp (continuous_cumulativeSums.comp continuous_snd)
    have hgv : ∀ y, Measure.map (g y) volume = (volume : Measure (PointTuple (n + 1))) := fun y =>
      ((measurePreserving_add_left (volume : Measure (PointTuple (n + 1))) (fun _ => y)).comp
        ih).map_eq
    have hG := MeasurePreserving.skew_product
      (MeasurePreserving.id (volume : Measure (Fin 4 → ℝ))) hgm (ae_of_all _ hgv)
      (μc := (volume : Measure (PointTuple (n + 1))))
      (μd := (volume : Measure (PointTuple (n + 1))))
    have hall := (he.symm e).comp (hG.comp he)
    have hfun : (cumulativeSums : PointTuple (n + 2) → PointTuple (n + 2)) =
        e.symm ∘ (fun p => (id p.1, g p.1 p.2)) ∘ e := by
      funext x
      apply e.injective
      simp only [Function.comp_apply, MeasurableEquiv.apply_symm_apply]
      refine Prod.ext ?_ ?_
      · exact cumulativeSums_zero x
      · funext k
        exact cumulativeSums_succ x k
    rw [hfun]
    exact hall
theorem lineDeriv_comp_cumulativeSums {n : ℕ} (g : PointTuple (n + 1) → ℂ)
    (x v : PointTuple (n + 1)) :
    lineDeriv ℝ (fun y => g (cumulativeSums y)) x v =
      lineDeriv ℝ g (cumulativeSums x) (cumulativeSums v) := by
  simp only [lineDeriv, cumulativeSums_add_smul]
theorem sum_cumulativeSums_single (n : ℕ) :
    ∑ k : Fin (n + 1), cumulativeSums (Pi.single k (Pi.single 0 1) : PointTuple (n + 1)) =
      ∑ i : Fin (n + 1), (((i : ℕ) + 1 : ℕ) : ℝ) •
        (Pi.single i (Pi.single 0 1) : PointTuple (n + 1)) := by
  funext i
  have h1 : ∀ k : Fin (n + 1),
      cumulativeSums (Pi.single k (Pi.single 0 1) : PointTuple (n + 1)) i =
        if k ≤ i then (Pi.single 0 1 : Fin 4 → ℝ) else 0 := by
    intro k
    simp only [cumulativeSums, sum_Iic_eq_sum_ite]
    rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hj
      simp [hj]
    · simp
  rw [Finset.sum_apply, Finset.sum_apply]
  simp only [h1, Pi.smul_apply, Pi.single_apply]
  rw [← Finset.sum_filter]
  simp only [smul_ite, smul_zero]
  rw [Finset.sum_ite_eq]
  have hc : (Finset.univ.filter fun k : Fin (n + 1) => k ≤ i).card = (i : ℕ) + 1 := by
    have : (Finset.univ.filter fun k : Fin (n + 1) => k ≤ i) = Finset.Iic i := by
      ext j
      simp
    rw [this, Fin.card_Iic]
  rw [Finset.sum_const, hc]
  simp only [Finset.mem_univ, if_true]
  rw [Nat.cast_smul_eq_nsmul]
theorem totalTimeDeriv_comp_cumulativeSums {n : ℕ} (g : PointTuple (n + 1) → ℂ)
    (hg : ContDiff ℝ ∞ g) :
    totalTimeDeriv (fun y => g (cumulativeSums y)) =
      fun y => timeWeightedDeriv g (cumulativeSums y) := by
  funext x
  have hd : DifferentiableAt ℝ g (cumulativeSums x) := (hg.differentiable (by simp)) _
  simp only [totalTimeDeriv, timeWeightedDeriv, coordDeriv,
    lineDeriv_comp_cumulativeSums, hd.lineDeriv_eq_fderiv]
  rw [← map_sum, sum_cumulativeSums_single, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Complex.real_smul]
  push_cast
  rfl
theorem contDiff_timeWeightedDeriv {n : ℕ} (g : PointTuple (n + 1) → ℂ) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (timeWeightedDeriv g) := by
  unfold timeWeightedDeriv
  refine ContDiff.sum fun i _ => contDiff_const.mul ?_
  have h : coordDeriv i 0 g =
      fun x => fderiv ℝ g x (Pi.single i (Pi.single 0 1)) := by
    funext x
    exact ((hg.differentiable (by simp)) x).lineDeriv_eq_fderiv
  rw [h]
  exact (hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
theorem contDiff_iterate_timeWeightedDeriv {n : ℕ} (j : ℕ) :
    ∀ g : PointTuple (n + 1) → ℂ, ContDiff ℝ ∞ g →
      ContDiff ℝ ∞ (timeWeightedDeriv^[j] g) := by
  induction j with
  | zero => exact fun _ hg => hg
  | succ j ih =>
    intro g hg
    rw [Function.iterate_succ_apply]
    exact ih _ (contDiff_timeWeightedDeriv g hg)
theorem iterate_totalTimeDeriv_comp {n : ℕ} (j : ℕ) :
    ∀ g : PointTuple (n + 1) → ℂ, ContDiff ℝ ∞ g →
      totalTimeDeriv^[j] (fun y => g (cumulativeSums y)) =
        fun y => timeWeightedDeriv^[j] g (cumulativeSums y) := by
  induction j with
  | zero => exact fun _ _ => rfl
  | succ j ih =>
    intro g hg
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      totalTimeDeriv_comp_cumulativeSums g hg]
    exact ih _ (contDiff_timeWeightedDeriv g hg)
theorem lOneNorm_comp_cumulativeSums {n : ℕ} (g : PointTuple (n + 1) → ℂ) (hg : Continuous g) :
    lOneNorm (fun y => g (cumulativeSums y)) = lOneNorm g := by
  have mp := measurePreserving_cumulativeSums n
  unfold lOneNorm
  calc ∫ x, ‖g (cumulativeSums x)‖ = ∫ y, ‖g y‖ ∂(Measure.map cumulativeSums volume) :=
        (integral_map mp.aemeasurable hg.norm.aestronglyMeasurable).symm
    _ = ∫ y, ‖g y‖ := by rw [mp.map_eq]
theorem maxTimeDerivNorm_diffCoords {n : ℕ} (k : ℕ) (φ : PointTuple (n + 1) → ℂ)
    (hφ : ContDiff ℝ ∞ φ) :
    maxTimeDerivNorm k (diffCoords φ) = maxTimeDerivL1 k φ := by
  unfold maxTimeDerivNorm maxTimeDerivL1
  refine Finset.sup'_congr _ rfl fun j _ => ?_
  have h : diffCoords φ = fun y => φ (cumulativeSums y) := rfl
  rw [h, iterate_totalTimeDeriv_comp j φ hφ]
  exact lOneNorm_comp_cumulativeSums _ (contDiff_iterate_timeWeightedDeriv j φ hφ).continuous
theorem boundOrder_toNat {℘ : ℝ} (h℘ : 0 ≤ ℘) (m : ℕ) :
    (boundOrder ℘ m).toNat = m * (ceilExponent ℘ m).toNat + 1 := by
  have hL : 0 ≤ ceilExponent ℘ m := Int.ceil_nonneg (by positivity)
  obtain ⟨q, hq⟩ := Int.eq_ofNat_of_zero_le hL
  simp only [boundOrder, hq]
  have : ((m : ℤ) * (q : ℤ) + 1) = ((m * q + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [this, Int.toNat_natCast, Int.toNat_natCast]
theorem fieldFormNorm_nonneg {n : ℕ} (℘ : ℝ) (φ : PointTuple (n + 1) → ℂ) :
    0 ≤ fieldFormNorm ℘ φ := by
  unfold fieldFormNorm maxTimeDerivL1
  refine Finset.le_sup'_of_le _ (b := 0) (by simp) ?_
  exact integral_nonneg fun _ => norm_nonneg _
def cumulativeSumsMatrix (n : ℕ) : CoordMatrix (n + 1) :=
  fun a b => if b.1 ≤ a.1 ∧ b.2 = a.2 then 1 else 0
theorem sum_cumulativeSumsMatrix_mul {n : ℕ} (x : PointTuple (n + 1)) (i : Fin (n + 1))
    (μ : Fin 4) :
    ∑ c : CoordIdx (n + 1), cumulativeSumsMatrix n (i, μ) c * x c.1 c.2 =
      cumulativeSums x i μ := by
  rw [Fintype.sum_prod_type]
  simp only [cumulativeSums, sum_Iic_eq_sum_ite, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : j ≤ i <;> simp [cumulativeSumsMatrix, h]
theorem isUnit_cumulativeSumsMatrix (n : ℕ) : IsUnit (cumulativeSumsMatrix n) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro v w h
  have hS : cumulativeSums (fun i μ => v (i, μ)) = cumulativeSums (fun i μ => w (i, μ)) := by
    funext i μ
    rw [← sum_cumulativeSumsMatrix_mul, ← sum_cumulativeSumsMatrix_mul]
    exact congrFun h (i, μ)
  have h' := cumulativeSums_injective hS
  funext c
  exact congrFun (congrFun h' c.1) c.2
theorem diffCoords_mem_schwartzSet (h : AffineCompBounds) {n : ℕ}
    (φ : PointTuple (n + 1) → ℂ) (hφ : φ ∈ schwartzSet (n + 1)) :
    diffCoords φ ∈ schwartzSet (n + 1) := by
  have hb : EntryBound (cumulativeSumsMatrix n) 1 := by
    refine ⟨le_rfl, fun a b => ?_⟩
    unfold cumulativeSumsMatrix
    split_ifs <;> simp
  have h1 := (h (n + 1) (Nat.succ_pos n) φ hφ (cumulativeSumsMatrix n) 0 1
    (isUnit_cumulativeSumsMatrix n) hb).2.1
  have he : affineComp (cumulativeSumsMatrix n) 0 φ = diffCoords φ := by
    funext x
    have : affineApply (cumulativeSumsMatrix n) 0 x = cumulativeSums x := by
      funext i μ
      simp only [affineApply, Pi.zero_apply, add_zero]
      exact sum_cumulativeSumsMatrix_mul x i μ
    simp only [affineComp, this]
    rfl
  rwa [he] at h1
theorem zero_mem_closedFutureConeTuples (b : ℕ) :
    (0 : PointTuple b) ∈ TubeBoundary.closedFutureConeTuples b := by
  intro k _
  show coneGap 0 ≥ 0
  simp [coneGap, spacePart, spaceNorm]
theorem futureConeTuples_subset_closed (b : ℕ) :
    TubeBoundary.futureConeTuples b ⊆ TubeBoundary.closedFutureConeTuples b := by
  intro Y h k hk
  have h1 : coneGap (Y k) > 0 := h k hk
  show coneGap (Y k) ≥ 0
  exact h1.le
theorem realPoint_futureConeTuples_eq (b : ℕ) :
    RealPointVectors.futureConeTuples b = TubeBoundary.futureConeTuples b := by
  ext Y
  simp [RealPointVectors.futureConeTuples, TubeBoundary.futureConeTuples, Set.mem_pi]
theorem coneGap_smul_timeUnit (t : ℝ) : coneGap (t • timeUnit) = t := by
  simp [coneGap, spacePart, spaceNorm, timeUnit, mkTimeSpace]
theorem nhdsWithin_futureConeTuples_neBot (b : ℕ) :
    (𝓝[RealPointVectors.futureConeTuples b] (0 : PointTuple b)).NeBot := by
  apply mem_closure_iff_nhdsWithin_neBot.1
  let Y : ℝ → PointTuple b := fun t _ => t • timeUnit
  have hc : Continuous Y := continuous_pi fun _ => continuous_id.smul continuous_const
  have h0 : Y 0 = 0 := by
    funext k
    simp [Y]
  have ht : Tendsto Y (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := hc.tendsto 0
    rw [h0] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto ht ?_
  filter_upwards [self_mem_nhdsWithin] with t (htp : 0 < t) k
  show coneGap (t • timeUnit) > 0
  rw [coneGap_smul_timeUnit]
  exact htp
section Limits
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {E : FourBorelSet → BddOp K} {Ω : K} {A : ℝ → BddOp K} {℘ C : ℝ}
theorem tubeMatrixElement_boundary_data (hm : TubeMatrixElements.Statement)
    (hv : BoundaryValueBound) (hf : IsBoundedFieldForm E Ω A ℘ C)
    (n : ℕ) (χ : K) :
    IsBoundaryExtension (tubeMatrixElement E Ω A χ (m := n))
        (boundaryValue (tubeMatrixElement E Ω A χ (m := n))) ∧
      ∀ Y ∈ TubeBoundary.closedFutureConeTuples (n + 1), ∀ φ ∈ schwartzSet (n + 1),
        ‖boundaryValue (tubeMatrixElement E Ω A χ (m := n)) Y φ‖ ≤
          4 * (‖χ‖ * ((2 : ℝ) ^ ℘ * C) ^ (n + 1)) *
            maxTimeDerivNorm ((n + 1) * (ceilExponent ℘ (n + 1)).toNat + 1) φ := by
  obtain ⟨hol, bd, -, -⟩ := hm E Ω A ℘ C hf n χ
  obtain ⟨-, -, -, hext, hbd⟩ := hv (n + 1) _ _ _ (Nat.succ_pos n) hol bd
  exact ⟨hext, hbd⟩
theorem tendsto_inner_smearedState (hm : TubeMatrixElements.Statement)
    (hv : BoundaryValueBound) (ha : AffineCompBounds)
    (hf : IsBoundedFieldForm E Ω A ℘ C) (n : ℕ)
    (φ : PointTuple (n + 1) → ℂ) (hφ : φ ∈ schwartzSet (n + 1)) (χ : K) :
    Tendsto (fun Y => ⟪χ, smearedState E Ω A Y φ⟫_ℂ)
      (𝓝[RealPointVectors.futureConeTuples (n + 1)] 0)
      (𝓝 (boundaryValue (tubeMatrixElement E Ω A χ (m := n)) 0 (diffCoords φ))) := by
  have hφ' := diffCoords_mem_schwartzSet ha φ hφ
  obtain ⟨hext, -⟩ := tubeMatrixElement_boundary_data hm hv hf n χ
  set J := boundaryValue (tubeMatrixElement E Ω A χ (m := n)) with hJ
  have hc := hext.2.1 _ hφ'
  have hz : translateBy (0 : PointTuple (n + 1)) (diffCoords φ) = diffCoords φ := by
    funext x
    simp [translateBy]
  have h0 := hc ((0 : PointTuple (n + 1)), (0 : PointTuple (n + 1)))
    ⟨zero_mem_closedFutureConeTuples _, Set.mem_univ _⟩
  have hmap : Tendsto (fun Y : PointTuple (n + 1) => (Y, (0 : PointTuple (n + 1))))
      (𝓝[RealPointVectors.futureConeTuples (n + 1)] 0)
      (𝓝[TubeBoundary.closedFutureConeTuples (n + 1) ×ˢ Set.univ]
        ((0 : PointTuple (n + 1)), (0 : PointTuple (n + 1)))) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact ((continuous_id.prodMk continuous_const).tendsto' _ _ rfl).mono_left
        nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with Y hY
      rw [realPoint_futureConeTuples_eq] at hY
      exact ⟨futureConeTuples_subset_closed _ hY, Set.mem_univ _⟩
  have hlim := Tendsto.comp h0 hmap
  simp only [hz] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with Y hY
  have hY' := hY
  rw [realPoint_futureConeTuples_eq] at hY'
  simp only [Function.comp_apply, hz]
  rw [hext.1 Y hY' _ hφ']
  exact ((hm E Ω A ℘ C hf n χ).2.2.2 Y hY φ hφ).2.symm
theorem exists_boundaryLimit (hm : TubeMatrixElements.Statement)
    (hv : BoundaryValueBound) (ha : AffineCompBounds)
    (hd : HilbertToolkit.FunctionalPart)
    (hf : IsBoundedFieldForm E Ω A ℘ C) (n : ℕ)
    (φ : PointTuple (n + 1) → ℂ) (hφ : φ ∈ schwartzSet (n + 1)) :
    ∃ v : K, (∀ χ : K, boundaryValue (tubeMatrixElement E Ω A χ (m := n)) 0
        (diffCoords φ) = ⟪χ, v⟫_ℂ) ∧
      ‖v‖ ≤ 4 * ((2 : ℝ) ^ ℘ * C) ^ (n + 1) * fieldFormNorm ℘ φ := by
  have hne := nhdsWithin_futureConeTuples_neBot (n + 1)
  have ht := tendsto_inner_smearedState (E := E) (Ω := Ω) (A := A) hm hv ha hf n φ hφ
  have hφ' := diffCoords_mem_schwartzSet ha φ hφ
  let l : K →ₛₗ[starRingEnd ℂ] ℂ :=
    { toFun := fun χ => boundaryValue (tubeMatrixElement E Ω A χ (m := n)) 0
        (diffCoords φ)
      map_add' := fun χ χ' => by
        refine tendsto_nhds_unique (ht (χ + χ')) ?_
        simp only [inner_add_left]
        exact (ht χ).add (ht χ')
      map_smul' := fun c χ => by
        refine tendsto_nhds_unique (ht (c • χ)) ?_
        simp only [inner_smul_left, smul_eq_mul]
        exact (ht χ).const_mul _ }
  have hP : 0 ≤ (2 : ℝ) ^ ℘ * C :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (by linarith [hf.one_le_const])
  have hc : 0 ≤ 4 * ((2 : ℝ) ^ ℘ * C) ^ (n + 1) * fieldFormNorm ℘ φ :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hP _)) (fieldFormNorm_nonneg _ _)
  have hb : ∀ χ, ‖l χ‖ ≤ 4 * ((2 : ℝ) ^ ℘ * C) ^ (n + 1) * fieldFormNorm ℘ φ * ‖χ‖ := by
    intro χ
    have h1 := (tubeMatrixElement_boundary_data hm hv hf n χ).2 0
      (zero_mem_closedFutureConeTuples _) _ hφ'
    rw [maxTimeDerivNorm_diffCoords _ φ hφ.1] at h1
    have h2 : fieldFormNorm ℘ φ = maxTimeDerivL1
        ((n + 1) * (ceilExponent ℘ (n + 1)).toNat + 1) φ := by
      unfold fieldFormNorm
      rw [boundOrder_toNat hf.exponent_nonneg]
    rw [h2]
    refine h1.trans (le_of_eq ?_)
    ring
  obtain ⟨⟨v, hv1, -⟩, hv2⟩ := hd K l _ hc hb
  exact ⟨v, hv1, hv2 v hv1⟩
end Limits
theorem statement_holds (hm : TubeMatrixElements.Statement)
    (hv : BoundaryValueBound)
    (hh : HilbertToolkit.HilbertCompletionExtensionRiesz)
    (hs : TestSpaces.Elementary.BasicProperties)
    (ht : MotionsTranslations.Statement) : SmearedBoundaryVectors.Statement := by
  intro K _ _ _ E Ω A ℘ C hf
  have ha : AffineCompBounds := ht.2.2.2.1
  have hd : HilbertToolkit.FunctionalPart := hh.2.2.2.1
  have hne := fun n => nhdsWithin_futureConeTuples_neBot (n + 1)
  have hlim := fun n φ hφ χ =>
    tendsto_inner_smearedState (E := E) (Ω := Ω) (A := A) hm hv ha hf n φ hφ χ
  have hinner : ∀ (n : ℕ) (φ : PointTuple (n + 1) → ℂ), φ ∈ schwartzSet (n + 1) →
      ∀ v : K, IsBoundaryLimit E Ω A φ v → ∀ χ : K,
        ⟪χ, v⟫_ℂ = boundaryValue (tubeMatrixElement E Ω A χ (m := n)) 0
          (diffCoords φ) := by
    intro n φ hφ v hb χ
    have := hne n
    exact tendsto_nhds_unique (hb χ) (hlim n φ hφ χ)
  have hex : ∀ (n : ℕ) (φ : PointTuple (n + 1) → ℂ), φ ∈ schwartzSet (n + 1) →
      ∃ v : K, IsBoundaryLimit E Ω A φ v ∧
        ‖v‖ ≤ 4 * ((2 : ℝ) ^ ℘ * C) ^ (n + 1) * fieldFormNorm ℘ φ := by
    intro n φ hφ
    obtain ⟨v, h1, h2⟩ := exists_boundaryLimit hm hv ha hd hf n φ hφ
    refine ⟨v, fun χ => ?_, h2⟩
    rw [← h1 χ]
    exact hlim n φ hφ χ
  have hspec : ∀ (n : ℕ) (φ : PointTuple (n + 1) → ℂ), φ ∈ schwartzSet (n + 1) →
      IsBoundaryLimit E Ω A φ (testState E Ω A (n + 1) φ) := by
    intro n φ hφ
    obtain ⟨v, h1, -⟩ := hex n φ hφ
    exact Classical.epsilon_spec (p := IsBoundaryLimit E Ω A φ) ⟨v, h1⟩
  have huniq : ∀ (n : ℕ) (φ : PointTuple (n + 1) → ℂ), φ ∈ schwartzSet (n + 1) →
      ∀ v : K, IsBoundaryLimit E Ω A φ v → v = testState E Ω A (n + 1) φ := by
    intro n φ hφ v hb
    refine ext_inner_left ℂ fun χ => ?_
    rw [hinner n φ hφ v hb χ, hinner n φ hφ _ (hspec n φ hφ) χ]
  refine ⟨hspec, huniq, ?_, ?_, ?_⟩
  · intro n φ φ' hφ hφ' c c'
    have hcomb : c • φ + c' • φ' ∈ schwartzSet (n + 1) := by
      have h0 := (hs (n + 1) (Nat.succ_pos n)).1
      unfold TestSpaces.Elementary.SchwartzClosedUnderOps at h0
      have h := (h0.1 φ hφ φ' hφ' c c').1.1
      have he : TestSpaces.Elementary.linComb c φ c' φ' = c • φ + c' • φ' := by
        funext x
        simp [TestSpaces.Elementary.linComb]
      rwa [he] at h
    refine ext_inner_left ℂ fun χ => ?_
    rw [hinner n _ hcomb _ (hspec n _ hcomb) χ, inner_add_right, inner_smul_right,
      inner_smul_right, hinner n φ hφ _ (hspec n φ hφ) χ, hinner n φ' hφ' _ (hspec n φ' hφ') χ]
    obtain ⟨hext, -⟩ := tubeMatrixElement_boundary_data (E := E) (Ω := Ω) (A := A) hm hv hf n χ
    exact hext.2.2 0 (zero_mem_closedFutureConeTuples _) _ (diffCoords_mem_schwartzSet ha φ hφ) _
      (diffCoords_mem_schwartzSet ha φ' hφ') c c'
  · intro n φ hφ
    obtain ⟨v, h1, h2⟩ := hex n φ hφ
    rwa [huniq n φ hφ v h1] at h2
  · intro n φ hφ χ
    exact hinner n φ hφ _ (hspec n φ hφ) χ
end YangMills.Construction.SmearedBoundaryVectors
