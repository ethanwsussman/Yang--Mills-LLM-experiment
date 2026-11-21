import YangMills.Construction.Towers.RelationAndBoundsOfTheIteratesOfTheLinearMapsProof
import YangMills.Construction.Towers.AveragesAreBoundedBelowTheRadius
import YangMills.Construction.Towers.AveragesOfTheScaledPictureAreLocalProof
import YangMills.Construction.Towers.LinearMapsBetweenTwoLevelsOfATowerProof
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator ENNReal
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.SubRadiusMeanBounds
open YangMills.Construction.Matrices
open YangMills.Construction.Coordinates
open YangMills.Construction.PeriodicOperators (IsSupBelow)
open YangMills.Construction.PeriodicOperators.CauchyTaylorBounds (IsFieldNorm)
open YangMills.Construction.Tower.LeftChartFields (scalarCoords)
open YangMills.Construction.Tower.IteratedSmallFieldMeans (HolomorphicInEntries)
theorem pauliFamily_mem_traceless (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
theorem real_smul_eq_ofReal_smul (x : ℝ) (X : ComplexMatrix2) : x • X = (x : ℂ) • X := by apply _root_.YangMills.SharedProofs.p9878 <;> assumption
theorem norm_pauliFamily (a : Fin 3) : ‖ComplexMatrix2.pauliFamily a‖ = 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.norm_pauliFamily <;> assumption
theorem pauliCoeff_sum_smul (c : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ a', c a' • ComplexMatrix2.pauliFamily a') = c a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
theorem exists_pauliCoord_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (a : Fin 3) (X : ComplexMatrix2.traceless),
      ‖OneLoop.pauliCoordinateEquiv X a‖ ≤ K * ‖(X : ComplexMatrix2)‖ := by
  let l : Fin 3 → ComplexMatrix2.traceless →L[ℂ] ℂ := fun a => LinearMap.toContinuousLinearMap
    ((LinearMap.proj a) ∘ₗ
      (OneLoop.pauliCoordinateEquiv : ComplexMatrix2.traceless →ₗ[ℂ] (Fin 3 → ℂ)))
  refine ⟨∑ a, ‖l a‖, Finset.sum_nonneg fun _ _ => ContinuousLinearMap.opNorm_nonneg _, fun a X => ?_⟩
  have h1 : ‖OneLoop.pauliCoordinateEquiv X a‖ ≤ ‖l a‖ * ‖X‖ := (l a).le_opNorm X
  have h2 : ‖l a‖ ≤ ∑ a, ‖l a‖ :=
    Finset.single_le_sum (f := fun a => ‖l a‖) (fun _ _ => ContinuousLinearMap.opNorm_nonneg _)
      (Finset.mem_univ a)
  exact h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
section Suprema
variable {ι : Type*}
theorem maxOperatorNorm_le_ofReal {f : ι → ComplexMatrix2} {s : ℝ} (h : ∀ i, ‖f i‖ ≤ s) :
    maxOperatorNorm f ≤ ENNReal.ofReal s := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.maxOperatorNorm_le_ofReal <;> assumption
theorem ofReal_norm_le_maxOperatorNorm (f : ι → ComplexMatrix2) (i : ι) :
    ENNReal.ofReal ‖f i‖ ≤ maxOperatorNorm f := by apply _root_.YangMills.Construction.Tower.IterateBounds.ofReal_norm_le_maxOperatorNorm <;> assumption
theorem maxOperatorNorm_smul (c : ℂ) (f : ι → ComplexMatrix2) :
    maxOperatorNorm (c • f) = ENNReal.ofReal ‖c‖ * maxOperatorNorm f := by
  unfold maxOperatorNorm
  rw [ENNReal.mul_iSup]
  refine iSup_congr fun i => ?_
  rw [← ENNReal.ofReal_mul (norm_nonneg c), Pi.smul_apply, ComplexMatrix2.operatorNorm,
    ComplexMatrix2.operatorNorm, norm_smul]
theorem maxOperatorNorm_add_le (f g : ι → ComplexMatrix2) :
    maxOperatorNorm (f + g) ≤ maxOperatorNorm f + maxOperatorNorm g := by apply _root_.YangMills.Construction.Tower.TwoLevelMaps.maxOperatorNorm_add_le <;> assumption
end Suprema
section Links
variable {a : ℝ}
theorem isPositivelyOriented_or_opposite (b : InfiniteLattice.Link a) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.GibbsForms.isPositivelyOriented_or_opposite <;> assumption
theorem not_isPositivelyOriented_opposite (ha : 0 < a) {b : InfiniteLattice.Link a}
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.Link.opposite_not_isPositivelyOriented <;> assumption
end Links
section Forms
variable {L k : ℕ}
theorem finestMesh_pos (hL : 0 < L) : 0 < finestMesh L k := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.finestMesh_pos <;> assumption
def coeffForm (ζ : (remainderIndex L k).Carrier → ℂ) : Edge L k 0 → ComplexMatrix2 :=
  (edgePauliCoordinates L k 0).ofCoeffs ζ
theorem coeffForm_of_pos (ζ : (remainderIndex L k).Carrier → ℂ) {b : Edge L k 0}
    (h : b.IsPositivelyOriented) :
    coeffForm ζ b = ∑ a, ζ (a, ⟨b, h⟩) • ComplexMatrix2.pauliFamily a := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.pauliForm_of_pos <;> assumption
theorem coeffForm_mem (hη : 0 < finestMesh L k) (ζ : (remainderIndex L k).Carrier → ℂ) :
    coeffForm ζ ∈ complexEdgeForms (meshAt L k 0) := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.pauliForm_mem <;> assumption
theorem coeffForm_add (ζ ξ : (remainderIndex L k).Carrier → ℂ) :
    coeffForm (ζ + ξ) = coeffForm ζ + coeffForm ξ := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.pauliForm_add <;> assumption
theorem coeffForm_smul (c : ℂ) (ζ : (remainderIndex L k).Carrier → ℂ) :
    coeffForm (c • ζ) = c • coeffForm ζ := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.pauliForm_smul <;> assumption
theorem norm_coeffForm_le (ζ : (remainderIndex L k).Carrier → ℂ) {r : ℝ} (h : ∀ κ, ‖ζ κ‖ ≤ r)
    (b : Edge L k 0) : ‖coeffForm ζ b‖ ≤ 3 * r := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.norm_pauliForm_le <;> assumption
theorem coeffForm_apply_mem (ζ : (remainderIndex L k).Carrier → ℂ) (b : Edge L k 0) :
    coeffForm ζ b ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.pauliForm_apply_mem <;> assumption
theorem remainderGaugeField_scaledForm (hη : 0 < finestMesh L k)
    (ζ : (remainderIndex L k).Carrier → ℂ) :
    remainderGaugeField (scaledForm L k ζ) = BackgroundJets.gaugeFieldOfForm L k ζ := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.remainderGaugeField_rescaledForm <;> assumption
theorem scaledForm_eq_smul (ζ : (remainderIndex L k).Carrier → ℂ) :
    scaledForm L k ζ = (((finestMesh L k)⁻¹ : ℝ) : ℂ) • coeffForm ζ := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.rescaledForm_eq_smul <;> assumption
theorem scaledForm_mem (hη : 0 < finestMesh L k) (ζ : (remainderIndex L k).Carrier → ℂ) :
    scaledForm L k ζ ∈ complexEdgeForms (meshAt L k 0) := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.rescaledForm_mem <;> assumption
theorem scaledForm_apply_mem (ζ : (remainderIndex L k).Carrier → ℂ) (b : Edge L k 0) :
    scaledForm L k ζ b ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.rescaledForm_apply_mem <;> assumption
theorem scaledForm_smul (c : ℂ) (ζ : (remainderIndex L k).Carrier → ℂ) :
    scaledForm L k (c • ζ) = c • scaledForm L k ζ := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.rescaledForm_smul <;> assumption
theorem fineFieldNorm_eq (hη : 0 < finestMesh L k) (ζ : (remainderIndex L k).Carrier → ℂ) :
    fineFieldNorm L k ζ = maxOperatorNorm (scaledForm L k ζ) := by
  have hi : 0 < (finestMesh L k)⁻¹ := inv_pos.2 hη
  change ENNReal.ofReal (finestMesh L k)⁻¹ * maxOperatorNorm (coeffForm ζ) = _
  rw [scaledForm_eq_smul]
  have h := maxOperatorNorm_smul (((finestMesh L k)⁻¹ : ℝ) : ℂ) (coeffForm ζ)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hi] at h
  exact h.symm
theorem exists_bound_of_isSupBelow (hη : 0 < finestMesh L k) {ρ : ℝ}
    {ζ : (remainderIndex L k).Carrier → ℂ}
    (h : IsSupBelow (remainderIndex L k) ζ (finestMesh L k * ρ / 3)) :
    ∃ s : ℝ, s < ρ ∧ ∀ b, ‖scaledForm L k ζ b‖ ≤ s := by
  obtain ⟨r, hr, hb⟩ := h
  have hi : 0 < (finestMesh L k)⁻¹ := inv_pos.2 hη
  refine ⟨(finestMesh L k)⁻¹ * (3 * r), ?_, fun b => ?_⟩
  · have h3 : 3 * r < finestMesh L k * ρ := by linarith
    calc (finestMesh L k)⁻¹ * (3 * r) < (finestMesh L k)⁻¹ * (finestMesh L k * ρ) :=
          mul_lt_mul_of_pos_left h3 hi
      _ = ρ := by field_simp
  · rw [scaledForm_eq_smul, Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hi]
    exact mul_le_mul_of_nonneg_left (norm_coeffForm_le ζ hb b) hi.le
theorem isFieldNorm_fineFieldNorm (hη : 0 < finestMesh L k) :
    IsFieldNorm (remainderIndex L k) (fineFieldNorm L k) := by
  refine ⟨fun c ζ => ?_, fun ζ ξ => ?_, fun ζ hζ => ?_⟩
  · change ENNReal.ofReal (finestMesh L k)⁻¹ * maxOperatorNorm (coeffForm (c • ζ)) =
      ENNReal.ofReal ‖c‖ * (ENNReal.ofReal (finestMesh L k)⁻¹ * maxOperatorNorm (coeffForm ζ))
    rw [coeffForm_smul, maxOperatorNorm_smul, mul_left_comm]
  · change ENNReal.ofReal (finestMesh L k)⁻¹ * maxOperatorNorm (coeffForm (ζ + ξ)) ≤
      ENNReal.ofReal (finestMesh L k)⁻¹ * maxOperatorNorm (coeffForm ζ) +
        ENNReal.ofReal (finestMesh L k)⁻¹ * maxOperatorNorm (coeffForm ξ)
    rw [coeffForm_add, ← mul_add]
    gcongr
    exact maxOperatorNorm_add_le _ _
  · have hi : 0 < (finestMesh L k)⁻¹ := inv_pos.2 hη
    have htop : maxOperatorNorm (coeffForm ζ) ≠ ∞ := by
      intro he
      have h0 : ENNReal.ofReal (finestMesh L k)⁻¹ ≠ 0 := by
        simpa using hi
      have : fineFieldNorm L k ζ = ∞ := by
        change ENNReal.ofReal (finestMesh L k)⁻¹ * maxOperatorNorm (coeffForm ζ) = ∞
        rw [he, ENNReal.mul_top h0]
      exact hζ.ne this
    obtain ⟨K, hK0, hK⟩ := exists_pauliCoord_le
    refine ⟨K * (maxOperatorNorm (coeffForm ζ)).toReal, fun κ => ?_⟩
    obtain ⟨a, b, hb⟩ := κ
    have hc : pauliCoeff a (coeffForm ζ b) = ζ (a, ⟨b, hb⟩) := by
      rw [coeffForm_of_pos ζ hb]
      exact pauliCoeff_sum_smul (fun a' => ζ (a', ⟨b, hb⟩)) a
    have h1 : ‖coeffForm ζ b‖ ≤ (maxOperatorNorm (coeffForm ζ)).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal htop).1 (ofReal_norm_le_maxOperatorNorm _ b)
    have h2 := hK a ⟨coeffForm ζ b, coeffForm_apply_mem ζ b⟩
    rw [← hc]
    simp only [pauliCoeff, dif_pos (coeffForm_apply_mem ζ b)]
    exact h2.trans (mul_le_mul_of_nonneg_left h1 hK0)
end Forms
section Holomorphy
theorem isHolomorphicIn_of_linearMap {N M : ℕ}
    (g : ComplexCoordinates N →ₗ[ℂ] ComplexCoordinates M)
    {O : Set (ComplexCoordinates N)} (hO : IsOpen O) : ComplexCoordinates.IsHolomorphicIn O g := by apply _root_.YangMills.Construction.Averaging.SmallRadiusProof.isHolomorphicIn_of_linearMap <;> assumption
theorem differentiableAt_of_translate {G : ℂ → ℂ} {w : ℂ}
    (h : DifferentiableAt ℂ (fun t : ℂ => G (w + t)) 0) : DifferentiableAt ℂ G w := by
  have h' : DifferentiableAt ℂ (fun t : ℂ => G (w + t)) ((fun σ : ℂ => σ - w) w) := by
    simpa using h
  have h3 := DifferentiableAt.comp (g := fun t : ℂ => G (w + t)) (f := fun σ : ℂ => σ - w) w h'
    (by fun_prop)
  have e : ((fun t : ℂ => G (w + t)) ∘ fun σ : ℂ => σ - w) = G := by
    funext σ
    simp
  rwa [e] at h3
variable {L k : ℕ}
theorem differentiableOn_ray
    (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hη : 0 < finestMesh L k) {ρ : ℝ} {v : (Edge L k 0 → ComplexMatrix2) → ℂ}
    (hv : HolomorphicInEntries scalarCoords
      (complexEdgeForms (meshAt L k 0) : Set (Edge L k 0 → ComplexMatrix2)) ρ v)
    (ζ : (remainderIndex L k).Carrier → ℂ) :
    DifferentiableOn ℂ (fun σ : ℂ => v (scaledForm L k (σ • ζ)))
      {σ | fineFieldNorm L k (σ • ζ) < ENNReal.ofReal ρ} := by
  classical
  obtain ⟨F₀, f, hf, hfv⟩ := hv
  let A : F₀ → ComplexMatrix2.traceless := fun i => ⟨scaledForm L k ζ i, scaledForm_apply_mem _ _⟩
  let Ψ : ComplexCoordinates 1 →ₗ[ℂ] (F₀ → ComplexMatrix2.traceless) :=
    { toFun := fun z => z 0 • A
      map_add' := fun z z' => by simp [add_smul]
      map_smul' := fun c z => by simp [mul_smul] }
  let B := OneLoop.pauliBasis
  let ν : F₀ ≃ Fin (Fintype.card F₀) := Fintype.equivFin _
  let g : ComplexCoordinates 1 →ₗ[ℂ] ComplexCoordinates (Fintype.card F₀ * 3) :=
    LinearMap.pi fun idx => (B.coord (finProdFinEquiv.symm idx).2) ∘ₗ
      (LinearMap.proj (ν.symm (finProdFinEquiv.symm idx).1)) ∘ₗ Ψ
  have htuple : ∀ z, GroupLieProduct.tupleOfCoords B ν (g z) =
      fun i : F₀ => scaledForm L k (z 0 • ζ) i := by
    intro z
    funext i
    have h1 : ∀ c : Fin 3, g z (finProdFinEquiv (ν i, c)) = B.repr (Ψ z i) c := by
      intro c
      change (B.coord (finProdFinEquiv.symm (finProdFinEquiv (ν i, c))).2)
        (Ψ z (ν.symm (finProdFinEquiv.symm (finProdFinEquiv (ν i, c))).1)) = _
      rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, Module.Basis.coord_apply]
    have h2 : ∑ x, (B.repr (Ψ z i)) x • ((B x : ComplexMatrix2.traceless) : ComplexMatrix2) =
        ((Ψ z i : ComplexMatrix2.traceless) : ComplexMatrix2) := by
      have h3 := congrArg Subtype.val (B.sum_repr (Ψ z i))
      rw [Submodule.coe_sum] at h3
      exact h3
    have h4 : ((Ψ z i : ComplexMatrix2.traceless) : ComplexMatrix2) =
        scaledForm L k (z 0 • ζ) i := by
      rw [scaledForm_smul]
      rfl
    simp only [GroupLieProduct.tupleOfCoords, ComplexCoordinates.tracelessTuple, h1]
    exact h2.trans h4
  have h0 := (hf B).2 ν
  let O' : Set (ComplexCoordinates 1) :=
    g ⁻¹' (GroupLieProduct.tupleOfCoords B ν ⁻¹' GroupLieProduct.supBall F₀ ρ)
  have hO' : IsOpen O' := h0.1.preimage (LinearMap.continuous_of_finiteDimensional g)
  have h1 := ((hH.1 _ _ h0.1).1 1 _ h0).2.2.2.1 _ _ g (isHolomorphicIn_of_linearMap g hO')
    (fun z hz => hz)
  have hsup : ∀ σ : ℂ, fineFieldNorm L k (σ • ζ) < ENNReal.ofReal ρ →
      maxOperatorNorm (scaledForm L k (σ • ζ)) < ENNReal.ofReal ρ := by
    intro σ hσ
    rwa [← fineFieldNorm_eq hη]
  have hball : ∀ z : ComplexCoordinates 1,
      fineFieldNorm L k (z 0 • ζ) < ENNReal.ofReal ρ → z ∈ O' := by
    intro z hz
    change GroupLieProduct.tupleOfCoords B ν (g z) ∈ GroupLieProduct.supBall F₀ ρ
    rw [htuple]
    have hs := hsup _ hz
    have hne : maxOperatorNorm (scaledForm L k (z 0 • ζ)) ≠ ∞ :=
      (hs.trans ENNReal.ofReal_lt_top).ne
    have hlt : (maxOperatorNorm (scaledForm L k (z 0 • ζ))).toReal < ρ :=
      (ENNReal.toReal_lt_of_lt_ofReal hs)
    refine ⟨?_, (Real.iSup_le (fun i => ?_) ENNReal.toReal_nonneg).trans_lt hlt⟩
    · rw [← GroupLieProduct.coe_tracelessFunctions]
      exact fun i _ => scaledForm_apply_mem _ _
    · exact (ENNReal.ofReal_le_iff_le_toReal hne).1 (ofReal_norm_le_maxOperatorNorm _ _)
  let G : ℂ → ℂ := fun σ => f fun i : F₀ => scaledForm L k (σ • ζ) i
  intro w hw
  let p : ComplexCoordinates 1 := fun _ => w
  have hpO : p ∈ O' := hball p hw
  have hd := (h1.2.2 p hpO 0).self_of_nhds
  have hG : DifferentiableAt ℂ G w := by
    have hcomp : ∀ t : ℂ,
        G (w + t) = ((scalarCoords ∘ f ∘ GroupLieProduct.tupleOfCoords B ν) ∘ g)
          (p + t • ComplexCoordinates.stdBasisVector 0) 0 := by
      intro t
      have hz : (p + t • ComplexCoordinates.stdBasisVector (0 : Fin 1)) 0 = w + t := by
        simp [p, ComplexCoordinates.stdBasisVector]
      simp only [Function.comp_apply, htuple, hz]
      rfl
    have hd' : DifferentiableAt ℂ (fun t : ℂ => G (w + t)) 0 := by
      have h2 := (differentiableAt_pi.1 hd) 0
      simpa only [hcomp] using h2
    exact differentiableAt_of_translate hd'
  refine hG.differentiableWithinAt.congr (fun σ hσ => ?_) ?_
  · exact (hfv _ (scaledForm_mem hη _) (hsup σ hσ)).symm
  · exact (hfv _ (scaledForm_mem hη _) (hsup w hw)).symm
end Holomorphy
theorem meanBoundsBelowRadius_of_powerSeriesHolomorphy
    (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties) : MeanBoundsBelowRadius := by
  intro L hL k hk ρ C hN
  have hS := (hN.2.2.2 k hk).2
  have hη : 0 < finestMesh L k := finestMesh_pos (by have := hL.2; omega)
  have hform : ∀ ζ, fineFieldNorm L k ζ ≤ ENNReal.ofReal ρ →
      scaledForm L k ζ ∈ IteratedSmallFieldMeans.smallFormBall L k ρ := fun ζ h =>
    ⟨scaledForm_mem hη ζ, by rwa [← fineFieldNorm_eq hη]⟩
  refine ⟨isFieldNorm_fineFieldNorm hη, fun ζ h => ?_,
    fun ζ h => ⟨hform ζ h, remainderGaugeField_scaledForm hη ζ⟩,
    ⟨fun ζ h => ?_, fun ζ _ ι' ι => ?_⟩, ⟨fun ζ h => ?_, fun ζ _ ι' ι => ?_⟩⟩
  · obtain ⟨s, hs, hb⟩ := exists_bound_of_isSupBelow hη h
    rw [fineFieldNorm_eq hη]
    exact (maxOperatorNorm_le_ofReal hb).trans (ENNReal.ofReal_le_ofReal hs.le)
  · have h1 := (hS.pointwise _ (hform ζ h.le)).opNorm_Q
    rwa [remainderGaugeField_scaledForm hη] at h1
  · have h1 := differentiableOn_ray hH hη (hS.holomorphic.kernel_Q ι' ι) ζ
    simp only [remainderGaugeField_scaledForm hη] at h1
    exact h1
  · have h1 := (hS.pointwise _ (hform ζ h.le)).opNorm_R
    rwa [remainderGaugeField_scaledForm hη] at h1
  · have h1 := differentiableOn_ray hH hη (hS.holomorphic.kernel_R ι' ι) ζ
    simp only [remainderGaugeField_scaledForm hη] at h1
    exact h1
end YangMills.Construction.Tower.FullSpace.SubRadiusMeanBounds
end
