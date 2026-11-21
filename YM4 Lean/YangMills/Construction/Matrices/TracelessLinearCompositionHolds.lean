import YangMills.Construction.Averaging.EverySmallRadiusServesProof
import YangMills.Construction.Matrices.ImplicitFunctionOnTheRealFormProof
import YangMills.Construction.Matrices.TracelessLinearComposition
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
open YangMills.Construction.Coordinates YangMills.Construction.Matrices
noncomputable section
namespace YangMills.Construction.Matrices.GroupLieProduct.LinearComposition
variable {ι : Type}
def matrixPiLinearEquiv {k : ℕ} (e : ι ≃ Fin k) :
    (ι → ComplexMatrix2) ≃ₗ[ℂ] ComplexCoordinates
      (ComplexCoordinates.productDim fun _ : Fin k => ComplexCoordinates.Component.matrix) :=
  { matrixPiEquiv e with
    map_add' := fun x y => by funext j; rfl
    map_smul' := fun c x => by funext j; rfl }
def tupleOfCoordsLinear [Fintype ι] (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (e : ι ≃ Fin (Fintype.card ι)) :
    ComplexCoordinates (Fintype.card ι * 3) →ₗ[ℂ] (ι → ComplexMatrix2) where
  toFun := tupleOfCoords b e
  map_add' v v' := by
    funext i
    simp [tupleOfCoords, ComplexCoordinates.tracelessTuple, add_smul, Finset.sum_add_distrib]
  map_smul' c v := by
    funext i
    simp [tupleOfCoords, ComplexCoordinates.tracelessTuple, Finset.smul_sum, mul_smul]
theorem tupleOfCoords_mem_tracelessPi [Fintype ι]
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (e : ι ≃ Fin (Fintype.card ι)) (v : ComplexCoordinates (Fintype.card ι * 3)) :
    tupleOfCoords b e v ∈ tracelessPi ι := by apply _root_.YangMills.Construction.Matrices.GroupLieProduct.Subspaces.RealForm.tupleOfCoords_mem <;> assumption
theorem exists_linear_coords [Fintype ι] (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (e : ι ≃ Fin (Fintype.card ι)) :
    ∃ S : (ι → ComplexMatrix2) →ₗ[ℂ] ComplexCoordinates (Fintype.card ι * 3),
      ∀ x ∈ tracelessPi ι, tupleOfCoords b e (S x) = x := by apply _root_.YangMills.Construction.Matrices.GroupLieProduct.Subspaces.RealForm.exists_linear_coords <;> assumption
theorem isHolomorphicIn_of_linearMap {m n : ℕ}
    (L : ComplexCoordinates m →ₗ[ℂ] ComplexCoordinates n)
    {U : Set (ComplexCoordinates m)} (hU : IsOpen U) : ComplexCoordinates.IsHolomorphicIn U L := by apply _root_.YangMills.Construction.Averaging.SmallRadiusProof.isHolomorphicIn_of_linearMap <;> assumption
theorem isOpen_preimage_tupleOfCoords [Fintype ι]
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (e : ι ≃ Fin (Fintype.card ι)) {U : Set (ι → ComplexMatrix2)} (hU : IsSupOpen U) :
    IsOpen (tupleOfCoords b e ⁻¹' U) := by
  rw [isOpen_iff_mem_nhds]
  intro v hv
  obtain ⟨r, hr, hB⟩ := hU.2 _ hv
  have hcont : Continuous (tupleOfCoords b e) :=
    (tupleOfCoordsLinear b e).continuous_of_finiteDimensional
  have hev : ∀ᶠ v' in 𝓝 v,
      ∀ i, ‖tupleOfCoords b e v' i - tupleOfCoords b e v i‖ < r / 2 := by
    rw [eventually_all]
    intro i
    have h1 : Continuous fun v' =>
        ‖tupleOfCoords b e v' i - tupleOfCoords b e v i‖ :=
      (((continuous_apply i).comp hcont).sub continuous_const).norm
    have h2 := h1.tendsto v
    simp only [sub_self, norm_zero] at h2
    exact h2.eventually (gt_mem_nhds (half_pos hr))
  filter_upwards [hev] with v' hv'
  refine hB _ (tupleOfCoords_mem_tracelessPi b e v') ?_
  have hle : supNorm (tupleOfCoords b e v' - tupleOfCoords b e v) ≤ r / 2 :=
    Real.iSup_le (fun i => (hv' i).le) (half_pos hr).le
  linarith
theorem holomorphicLinearComp_of_powerSeries
    (h : ComplexCoordinates.PowerSeriesHolomorphy.Properties) :
    GroupLieProduct.HolomorphicLinearComp := by
  intro α τ _ _ b N D hD
  let e := Fintype.equivFin τ
  let μ := Fintype.equivFin α
  obtain ⟨hN, hf⟩ := hD e
  have hfμ := hf μ
  obtain ⟨S, hS⟩ := exists_linear_coords b μ
  have hSc : Continuous S := S.continuous_of_finiteDimensional
  let eL := matrixPiLinearEquiv e
  have heL : Continuous eL.symm := eL.symm.toLinearMap.continuous_of_finiteDimensional
  have hcont : ContinuousOn D N := by
    have h1 : ContinuousOn
        (fun x => eL.symm ((matrixPiEquiv e ∘ D ∘ tupleOfCoords b μ) (S x))) N := by
      refine heL.comp_continuousOn (hfμ.2.1.comp hSc.continuousOn fun x hx => ?_)
      show tupleOfCoords b μ (S x) ∈ N
      rwa [hS x (hN.1 hx)]
    refine h1.congr fun x hx => ?_
    simp only [Function.comp_apply, hS x (hN.1 hx)]
    exact (eL.symm_apply_apply (D x)).symm
  refine ⟨hcont, ?_⟩
  intro α' τ' _ _ P Q N' hN' hPa hPN e'
  refine ⟨hN', fun μ' => ?_⟩
  let eL' := matrixPiLinearEquiv e'
  let g : ComplexCoordinates (Fintype.card α' * 3) →ₗ[ℂ]
      ComplexCoordinates (Fintype.card α * 3) :=
    S ∘ₗ P ∘ₗ tupleOfCoordsLinear b μ'
  let R := eL'.toLinearMap ∘ₗ Q ∘ₗ eL.symm.toLinearMap
  have hU' : IsOpen (tupleOfCoords b μ' ⁻¹' N') := isOpen_preimage_tupleOfCoords b μ' hN'
  have hTg : ∀ v, tupleOfCoords b μ (g v) = P (tupleOfCoords b μ' v) := fun v =>
    hS _ (hPa (tupleOfCoords_mem_tracelessPi b μ' v))
  have hmaps : MapsTo g (tupleOfCoords b μ' ⁻¹' N') (tupleOfCoords b μ ⁻¹' N) := by
    intro v hv
    show tupleOfCoords b μ (g v) ∈ N
    rw [hTg]
    exact hPN hv
  have c1 := ((h.1 _ _ hfμ.1).1 _ _ hfμ).2.2.2.1 _ _ g (isHolomorphicIn_of_linearMap g hU') hmaps
  have c2 := ((h.1 _ univ isOpen_univ).1 _ R (isHolomorphicIn_of_linearMap R isOpen_univ)).2.2.2.1
    _ _ _ c1 (mapsTo_univ _ _)
  convert c2 using 1
  funext v
  show eL' (Q (D (P (tupleOfCoords b μ' v)))) =
    eL' (Q (eL.symm (eL (D (tupleOfCoords b μ (g v))))))
  rw [eL.symm_apply_apply, hTg]
end YangMills.Construction.Matrices.GroupLieProduct.LinearComposition
