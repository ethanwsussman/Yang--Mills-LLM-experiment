import YangMills.Construction.Continuum.MotionsTensorProductsTranslationsAndTheReflection
import Reconstruction.MinkowskiSpace.ConeTubeAndLorentzGroupProof
import Reconstruction.MinkowskiSpace.LorentzInvarianceOfTheVacuumFunctions
import Reconstruction.MinkowskiSpace.PoincareInvarianceOfTheWightmanValues
import Reconstruction.MinkowskiSpace.VectorsAtRealPointsOfABoundedFieldForm
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Matrix
open scoped Topology
noncomputable section
namespace YangMills.Construction.WightmanPoincare
open YangMills.Construction.MinkowskiSpace YangMills.Construction.RealPointVectors
theorem toComplexMatrix_mulVec_toComplex (M : RealMat4) (v : RealVec4) :
    toComplexMatrix M *ᵥ toComplex v = toComplex (M *ᵥ v) := by apply _root_.YangMills.Construction.MinkowskiSpace.ConeTubeLorentz.toComplexMatrix_mulVec <;> assumption
def invMulVecTuple {m : ℕ} (M : RealMat4) (Y : TestSpaces.PointTuple m) :
    TestSpaces.PointTuple m :=
  fun k => M⁻¹ *ᵥ Y k
def poincareTuple {m : ℕ} (g : RealVec4 × RealMat4) (x : TestSpaces.PointTuple m) :
    TestSpaces.PointTuple m :=
  fun i => g.2 *ᵥ x i + g.1
theorem measurePreserving_mulVec_add (M : RealMat4) (hdet : M.det = 1) (a : RealVec4) :
    MeasurePreserving (fun v : RealVec4 => M *ᵥ v + a) := by
  have hlin : MeasurePreserving (fun v : RealVec4 => M *ᵥ v) := by
    refine ⟨(Matrix.toLin' M).continuous_of_finiteDimensional.measurable, ?_⟩
    have h := Real.map_matrix_volume_pi_eq_smul_volume_pi (M := M) (by simp [hdet])
    have hfun : (fun v : RealVec4 => M *ᵥ v) = ⇑(Matrix.toLin' M) := by
      funext v
      simp
    rw [hfun]
    simpa [hdet] using h
  exact (measurePreserving_add_right volume a).comp hlin
def poincareTupleHomeomorph {m : ℕ} (g : RealVec4 × RealMat4) (h₁ : g.2 * g.2⁻¹ = 1)
    (h₂ : g.2⁻¹ * g.2 = 1) : TestSpaces.PointTuple m ≃ₜ TestSpaces.PointTuple m where
  toFun := poincareTuple g
  invFun := fun x i => g.2⁻¹ *ᵥ (x i - g.1)
  left_inv x := by
    funext i
    simp [poincareTuple, Matrix.mulVec_mulVec, h₂]
  right_inv x := by
    funext i
    simp [poincareTuple, Matrix.mulVec_mulVec, h₁]
  continuous_toFun := by
    unfold poincareTuple
    fun_prop
  continuous_invFun := by
    fun_prop
theorem poincarePullback_mem_schwartzSet
    (haff : MotionsTranslations.AffineCompBounds)
    (g : RealVec4 × RealMat4) (h₂ : g.2⁻¹ * g.2 = 1) (m : ℕ)
    {φ : TestSpaces.PointTuple (m + 1) → ℂ} (hφ : φ ∈ TestSpaces.schwartzSet (m + 1)) :
    poincarePullback g φ ∈ TestSpaces.schwartzSet (m + 1) := by
  classical
  let M : MotionsTranslations.CoordMatrix (m + 1) :=
    Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) g.2⁻¹
  let N : MotionsTranslations.CoordMatrix (m + 1) :=
    Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) g.2
  let w : TestSpaces.PointTuple (m + 1) := fun _ => -(g.2⁻¹ *ᵥ g.1)
  have hMN : M * N = 1 := by
    have h := Matrix.mul_kronecker_mul (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) g.2⁻¹ g.2
    rw [Matrix.mul_one, h₂, Matrix.one_kronecker_one] at h
    exact h.symm
  have hunit : IsUnit M := by
    have hdet : IsUnit M.det := by
      have h := congrArg Matrix.det hMN
      rw [Matrix.det_mul, Matrix.det_one] at h
      exact IsUnit.of_mul_eq_one _ h
    exact (Matrix.isUnit_iff_isUnit_det M).mpr hdet
  have hbound : MotionsTranslations.EntryBound M
      (1 + ∑ μ, ∑ ν, |g.2⁻¹ μ ν|) := by
    have hnn : 0 ≤ ∑ μ, ∑ ν, |g.2⁻¹ μ ν| :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    refine ⟨by linarith, ?_⟩
    rintro ⟨i, μ⟩ ⟨j, ν⟩
    have hle : |g.2⁻¹ μ ν| ≤ ∑ μ, ∑ ν, |g.2⁻¹ μ ν| := by
      calc |g.2⁻¹ μ ν| ≤ ∑ ν, |g.2⁻¹ μ ν| :=
            Finset.single_le_sum (f := fun ν => |g.2⁻¹ μ ν|)
              (fun _ _ => abs_nonneg _) (Finset.mem_univ ν)
        _ ≤ ∑ μ, ∑ ν, |g.2⁻¹ μ ν| :=
            Finset.single_le_sum (f := fun μ => ∑ ν, |g.2⁻¹ μ ν|)
              (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ μ)
    by_cases hij : i = j
    · subst hij
      simp only [M, Matrix.kroneckerMap_apply, Matrix.one_apply_eq, one_mul]
      linarith
    · simp only [M, Matrix.kroneckerMap_apply, Matrix.one_apply_ne hij, zero_mul, abs_zero]
      linarith
  have hsub := (haff (m + 1) (Nat.succ_pos m) φ hφ M w _ hunit hbound).2.1
  have heq : poincarePullback g φ = MotionsTranslations.affineComp M w φ := by
    funext x
    unfold poincarePullback MotionsTranslations.affineComp
    congr 1
    funext i μ
    simp only [MotionsTranslations.affineApply, M, w,
      Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply, ite_mul, one_mul,
      zero_mul, Matrix.mulVec_sub, Pi.sub_apply, Pi.neg_apply]
    simp [Matrix.mulVec, dotProduct, sub_eq_add_neg]
  rw [heq]
  exact hsub
theorem successiveDiffs_poincareTuple {m : ℕ} (g : RealVec4 × RealMat4) (h₁ : g.2 * g.2⁻¹ = 1)
    (Y : TestSpaces.PointTuple m) (x : TestSpaces.PointTuple (m + 1)) :
    successiveDiffs (tupleToComplex (poincareTuple g x)) + Complex.I • tupleToComplex Y =
      mulVecTuple (toComplexMatrix g.2)
        (successiveDiffs (tupleToComplex x) + Complex.I • tupleToComplex (invMulVecTuple g.2 Y)) := by
  funext k
  have hY : g.2 *ᵥ (g.2⁻¹ *ᵥ Y k) = Y k := by
    rw [Matrix.mulVec_mulVec, h₁, Matrix.one_mulVec]
  have hadd : ∀ u v : RealVec4, toComplex (u + v) = toComplex u + toComplex v := fun u v => by
    funext μ
    simp [toComplex]
  simp only [mulVecTuple, successiveDiffs, tupleToComplex, Pi.add_apply, Pi.smul_apply,
    poincareTuple, invMulVecTuple]
  rw [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, toComplexMatrix_mulVec_toComplex,
    toComplexMatrix_mulVec_toComplex, toComplexMatrix_mulVec_toComplex, hY, hadd, hadd]
  abel
theorem successiveDiffs_add_mem_tubeTuples {m : ℕ} {Y : TestSpaces.PointTuple m}
    (hY : Y ∈ futureConeTuples m) (x : TestSpaces.PointTuple (m + 1)) :
    successiveDiffs (tupleToComplex x) + Complex.I • tupleToComplex Y ∈
      WightmanTheory.tubeTuples m := by
  intro k _
  have him : imPart ((successiveDiffs (tupleToComplex x) + Complex.I • tupleToComplex Y) k) =
      Y k := by
    funext μ
    simp [imPart, successiveDiffs, tupleToComplex, toComplex]
  change coneGap (imPart _) > 0
  rw [him]
  exact hY k
theorem timeUnit_mem_futureCone : timeUnit ∈ futureCone := by apply _root_.YangMills.Construction.MinkowskiSpace.ConeTubeLorentz.timeUnit_mem_futureCone <;> assumption
theorem wightmanPoincareInvariance_holds (hvec : BoundaryVectorsStatement)
    (hlor : VacuumLorentzInvariance.Statement)
    (hcone : ConeTubeLorentz.Statement)
    (hmot : MotionsTranslations.Statement) : WightmanPoincareInvariance := by
  intro K _ _ _ E Ω A ℘ C hform heuc g m φ hφ
  obtain ⟨⟨a, Λ⟩, hg⟩ := g
  have hΛ : Λ ∈ restrictedLorentz := hg.2
  have hgrp := hcone.2.2.2.2.2.2.2.2.1
  have hinvmem : Λ⁻¹ ∈ restrictedLorentz := (hgrp.1.2.2 Λ hΛ).2
  have hdetu : IsUnit Λ.det := (hgrp.1.2.2 Λ hΛ).1
  have h₁ : Λ * Λ⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdetu
  have h₂ : Λ⁻¹ * Λ = 1 := Matrix.nonsing_inv_mul _ hdetu
  have hψ : poincarePullback (a, Λ) φ ∈ TestSpaces.schwartzSet (m + 1) :=
    poincarePullback_mem_schwartzSet hmot.2.2.2.1 (a, Λ) h₂ m hφ
  refine ⟨hψ, ?_⟩
  have hV := hvec E Ω A ℘ C hform
  obtain ⟨F, hFc, hFe, hF0⟩ := hV.exists_continuousOn_extension m φ hφ
  obtain ⟨G, hGc, hGe, hG0⟩ := hV.exists_continuousOn_extension m _ hψ
  have hkeep : ∀ y ∈ futureCone, Λ⁻¹ *ᵥ y ∈ futureCone := by
    intro y hy
    have himg : (fun y => Λ⁻¹ *ᵥ y) '' futureCone = futureCone :=
      (hgrp.2 Λ⁻¹ hinvmem).1
    have hmem : Λ⁻¹ *ᵥ y ∈ (fun y => Λ⁻¹ *ᵥ y) '' futureCone := ⟨y, hy, rfl⟩
    rwa [himg] at hmem
  have hkeepT : ∀ Y ∈ futureConeTuples m, invMulVecTuple Λ Y ∈ futureConeTuples m :=
    fun Y hY k => hkeep _ (hY k)
  have hint : ∀ Y ∈ futureConeTuples m,
      ∫ x, vacuumIntegrand E Ω A (poincarePullback (a, Λ) φ) Y x =
        ∫ x, vacuumIntegrand E Ω A φ (invMulVecTuple Λ Y) x := by
    intro Y hY
    have hmp : MeasurePreserving (poincareTuple (m := m + 1) (a, Λ)) :=
      volume_preserving_pi fun _ => measurePreserving_mulVec_add Λ hΛ.2.1 a
    have hemb : MeasurableEmbedding (poincareTuple (m := m + 1) (a, Λ)) :=
      (poincareTupleHomeomorph (m := m + 1) (a, Λ) h₁ h₂).measurableEmbedding
    rw [← hmp.integral_comp hemb]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have hφx : poincarePullback (a, Λ) φ (poincareTuple (a, Λ) x) = φ x := by
      unfold poincarePullback
      congr 1
      funext i
      simp [poincareTuple, Matrix.mulVec_mulVec, h₂]
    have hw : FieldForms.vacuumExpectation E Ω A (m + 1)
        (successiveDiffs (tupleToComplex (poincareTuple (a, Λ) x)) +
          Complex.I • tupleToComplex Y) =
        FieldForms.vacuumExpectation E Ω A (m + 1)
          (successiveDiffs (tupleToComplex x) +
            Complex.I • tupleToComplex (invMulVecTuple Λ Y)) := by
      rw [successiveDiffs_poincareTuple (a, Λ) h₁ Y x]
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · exact congrArg _ (Subsingleton.elim _ _)
      · exact (hlor K E Ω A ℘ C hform heuc m hm).2.2 Λ hΛ _
          (successiveDiffs_add_mem_tubeTuples (hkeepT Y hY) x)
    simp only [vacuumIntegrand, hφx, hw]
  let ray : ℝ → TestSpaces.PointTuple m := fun t _ => t • timeUnit
  have hray : ∀ t : ℝ, 0 < t → ray t ∈ futureConeTuples m := fun t ht _ =>
    (hcone.2.1.2.1 t ht timeUnit timeUnit_mem_futureCone)
  have hclosed : ∀ Y ∈ futureConeTuples m, Y ∈ closedFutureConeTuples m := fun Y hY k => by
    have h : coneGap (Y k) > 0 := hY k
    exact (show coneGap (Y k) ≥ 0 from h.le)
  have hzero : (0 : TestSpaces.PointTuple m) ∈ closedFutureConeTuples m := by
    intro k
    have h : spacePart (0 : RealVec4) = 0 := rfl
    change coneGap 0 ≥ 0
    simp [coneGap, h, spaceNorm]
  have hcray : Tendsto ray (𝓝[>] 0) (𝓝 0) := by
    have : Continuous ray := by
      unfold ray
      fun_prop
    have h0 : ray 0 = 0 := by
      funext k
      simp [ray]
    simpa [h0] using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hcinv : Tendsto (fun t => invMulVecTuple Λ (ray t)) (𝓝[>] 0) (𝓝 0) := by
    have : Continuous (invMulVecTuple (m := m) Λ) := by
      unfold invMulVecTuple
      fun_prop
    have h0 : invMulVecTuple (m := m) Λ 0 = 0 := by
      funext k
      simp [invMulVecTuple]
    have h := (this.tendsto 0).comp hcray
    rw [h0] at h
    exact h
  have hself : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := eventually_mem_nhdsWithin
  have hlimG : Tendsto (fun t => G (ray t)) (𝓝[>] 0) (𝓝 (G 0)) :=
    ((hGc 0 hzero).tendsto).comp (tendsto_nhdsWithin_iff.mpr
      ⟨hcray, hself.mono fun t ht => hclosed _ (hray t ht)⟩)
  have hlimF : Tendsto (fun t => F (invMulVecTuple Λ (ray t))) (𝓝[>] 0) (𝓝 (F 0)) :=
    ((hFc 0 hzero).tendsto).comp (tendsto_nhdsWithin_iff.mpr
      ⟨hcinv, hself.mono fun t ht => hclosed _ (hkeepT _ (hray t ht))⟩)
  have heq : (fun t => G (ray t)) =ᶠ[𝓝[>] 0] fun t => F (invMulVecTuple Λ (ray t)) := by
    filter_upwards [hself] with t ht
    rw [hGe _ (hray t ht), hFe _ (hkeepT _ (hray t ht)), hint _ (hray t ht)]
  have hfin : G 0 = F 0 := tendsto_nhds_unique (hlimG.congr' heq) hlimF
  rw [← hG0, ← hF0, hfin]
end YangMills.Construction.WightmanPoincare
