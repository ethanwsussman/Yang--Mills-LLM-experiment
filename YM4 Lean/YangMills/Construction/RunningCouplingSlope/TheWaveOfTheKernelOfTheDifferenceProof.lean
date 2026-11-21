import YangMills.Construction.Towers.SecondDifferentialOfTheFunctionalAndItsComplexExtensionProof
import YangMills.Construction.Lattice.LevelBondOrientationDichotomy
import YangMills.Construction.Matrices.RepresentationsFieldsAndSmoothFunctionsOnG
import YangMills.Construction.RunningCouplingSlope.ColourCoordinatesOfATower
import YangMills.Construction.RunningCouplingSlope.FunctionOfTheWholeChain
import YangMills.Construction.RunningCouplingSlope.TheDifferenceKernelIsCarriedByTranslations
import YangMills.Construction.RunningCouplingSlope.TheWaveOfTheKernelOfTheDifference
import YangMills.Construction.Towers.ConfigurationsOnFiniteBondSets
import YangMills.Construction.Towers.FunctionalInTheBackgroundGaugeInTheExponentialChart
import YangMills.Construction.Towers.ImagesUnderTheResponseReadAtTheSideInfinity
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology ContDiff
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.CosineSumProof
open Tower Tower.CriticalBranchResponse TorusFields Matrices
section Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
private theorem hasDerivAt_planeDeriv (g : E → ℝ) (hg : ContDiffAt ℝ 2 g 0) (x y : E) :
    (∀ᶠ s : ℝ in 𝓝 0, DifferentiableAt ℝ (fun u : ℝ => g (s • x + u • y)) 0) ∧
      HasDerivAt (fun s : ℝ => deriv (fun u : ℝ => g (s • x + u • y)) 0)
        (fderiv ℝ (fderiv ℝ g) 0 x y) 0 := by
  have hd : ∀ᶠ w in 𝓝 (0 : E), DifferentiableAt ℝ g w :=
    (hg.eventually (by simp)).mono fun w hw => hw.differentiableAt (by simp)
  have hs0 : Tendsto (fun s : ℝ => s • x) (𝓝 0) (𝓝 (0 : E)) := by
    have h : Continuous fun s : ℝ => s • x := by fun_prop
    simpa using h.tendsto 0
  have hline : ∀ s : ℝ, HasDerivAt (fun u : ℝ => s • x + u • y) y 0 := by
    intro s
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const y).const_add (s • x)
  have hev : (fun s : ℝ => deriv (fun u : ℝ => g (s • x + u • y)) 0) =ᶠ[𝓝 0]
      fun s => fderiv ℝ g (s • x) y := by
    filter_upwards [hs0.eventually hd] with s hs
    have h2 : HasFDerivAt g (fderiv ℝ g (s • x)) (s • x + (0 : ℝ) • y) := by
      simpa using hs.hasFDerivAt
    exact (h2.comp_hasDerivAt (0 : ℝ) (hline s)).deriv
  refine ⟨?_, ?_⟩
  · filter_upwards [hs0.eventually hd] with s hs
    have h2 : HasFDerivAt g (fderiv ℝ g (s • x)) (s • x + (0 : ℝ) • y) := by
      simpa using hs.hasFDerivAt
    exact (h2.comp_hasDerivAt (0 : ℝ) (hline s)).differentiableAt
  · have h2 : DifferentiableAt ℝ (fderiv ℝ g) 0 :=
      (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
    have h3 : HasDerivAt (fun s : ℝ => s • x) x 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const x
    have h4 : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) 0) ((0 : ℝ) • x) := by
      simpa using h2.hasFDerivAt
    have h5 := h4.comp_hasDerivAt (0 : ℝ) h3
    have h6 := h5.clm_apply (hasDerivAt_const (0 : ℝ) y)
    have h7 : HasDerivAt (fun s : ℝ => fderiv ℝ g (s • x) y) (fderiv ℝ (fderiv ℝ g) 0 x y) 0 := by
      simpa using h6
    exact h7.congr_of_eventuallyEq hev
variable {E₂ V : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [AddCommGroup V] [Module ℝ V]
private theorem hasDerivAt_planeDeriv_linearMap (f : E → ℝ) (hf : ContDiffAt ℝ 2 f 0)
    (T : V →ₗ[ℝ] E) (v v' : V) :
    (∀ᶠ s : ℝ in 𝓝 0, DifferentiableAt ℝ (fun u : ℝ => f (T (s • v + u • v'))) 0) ∧
      HasDerivAt (fun s : ℝ => deriv (fun u : ℝ => f (T (s • v + u • v'))) 0)
        (fderiv ℝ (fderiv ℝ f) 0 (T v) (T v')) 0 := by
  simpa only [map_add, map_smul] using hasDerivAt_planeDeriv f hf (T v) (T v')
private theorem planeDeriv_sub (f : E → ℝ) (f₂ : E₂ → ℝ) (hf : ContDiffAt ℝ 2 f 0)
    (hf₂ : ContDiffAt ℝ 2 f₂ 0) (T : V →ₗ[ℝ] E) (T₂ : V →ₗ[ℝ] E₂) (v v' : V) :
    deriv (fun s : ℝ => deriv (fun u : ℝ =>
        f (T (s • v + u • v')) - f₂ (T₂ (s • v + u • v'))) 0) 0 =
      fderiv ℝ (fderiv ℝ f) 0 (T v) (T v') - fderiv ℝ (fderiv ℝ f₂) 0 (T₂ v) (T₂ v') := by
  obtain ⟨h₁, d₁⟩ := hasDerivAt_planeDeriv_linearMap f hf T v v'
  obtain ⟨h₂, d₂⟩ := hasDerivAt_planeDeriv_linearMap f₂ hf₂ T₂ v v'
  have hev : (fun s : ℝ => deriv (fun u : ℝ =>
        f (T (s • v + u • v')) - f₂ (T₂ (s • v + u • v'))) 0) =ᶠ[𝓝 0]
      fun s => deriv (fun u : ℝ => f (T (s • v + u • v'))) 0 -
        deriv (fun u : ℝ => f₂ (T₂ (s • v + u • v'))) 0 := by
    filter_upwards [h₁, h₂] with s a₁ a₂
    exact (a₁.hasDerivAt.sub a₂.hasDerivAt).deriv
  exact ((d₁.sub d₂).congr_of_eventuallyEq hev).deriv
end Calculus
variable {L n k : ℕ}
private theorem matExp_mul_matExp_neg (Z : ComplexMatrix2) :
    ComplexMatrix2.matExp Z * ComplexMatrix2.matExp (-Z) = 1 := by apply _root_.YangMills.Construction.SpinHarmonics.matExp_mul_matExp_neg <;> assumption
private theorem expTwist_one_eq (Y : edgeFormSpace L n k 0) :
    PeriodicLattice.expTwist (Y : Edge L n k 0 → ComplexMatrix2) 1 =
      PeriodicLattice.expGaugeField (Y : Edge L n k 0 → ComplexMatrix2) := by apply _root_.YangMills.Construction.Tower.HessianExtension.expForm_eq_expGaugeField <;> assumption
private theorem exists_pauliCoordEquiv (hc : PauliCoordsOrthonormal)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    [Fintype (PositiveEdge L n k 0)] [Fintype (PositiveEdge L n k k)] :
    ∃ tc : FieldTriple L n k ≃ₗ[ℝ] (FieldTripleIndex L n k → ℝ),
      ∀ x, tc x = fieldTripleCoords x := by
  obtain ⟨Ψ₀, h₀, -⟩ := (hc L n k 0 hL hn (Nat.zero_le k)).1
  obtain ⟨Ψₖ, hₖ, -⟩ := (hc L n k k hL hn le_rfl).1
  refine ⟨((Ψ₀.prodCongr (Ψ₀.prodCongr Ψₖ)).trans ((LinearEquiv.refl ℝ _).prodCongr
    (LinearEquiv.sumArrowLequivProdArrow _ _ ℝ ℝ).symm)).trans
      (LinearEquiv.sumArrowLequivProdArrow _ _ ℝ ℝ).symm, fun x => ?_⟩
  funext i
  rcases i with i | i | i
  · simp [fieldTripleCoords, h₀]
  · simp [fieldTripleCoords, h₀]
  · simp [fieldTripleCoords, hₖ]
private theorem expChartFunctionalInCoords_apply
    (tc : FieldTriple L n k ≃ₗ[ℝ] (FieldTripleIndex L n k → ℝ))
    (htc : ∀ x, tc x = fieldTripleCoords x) (r : FieldTriple L n k) :
    expChartFunctionalInCoords L n k (tc r) = expChartFunctional r := by
  have hinj : Function.Injective (fieldTripleCoords (L := L) (m := n) (k := k)) := by
    intro x x' h
    apply tc.injective
    rw [htc, htc, h]
  rw [htc]
  exact congrArg expChartFunctional (Function.leftInverse_invFun hinj r)
private theorem contDiffAt_expChartFunctionalInCoords
    [Fintype (PositiveEdge L n k 0)] [Fintype (PositiveEdge L n k k)]
    (tc : FieldTriple L n k ≃ₗ[ℝ] (FieldTripleIndex L n k → ℝ))
    (htc : ∀ x, tc x = fieldTripleCoords x)
    (hnear : ExpChartFunctionalExpansion L n k) :
    ContDiffAt ℝ 2 (expChartFunctionalInCoords L n k) 0 := by
  obtain ⟨W, hW⟩ := hnear.exists_nhd
  have hback : Continuous tc.symm := tc.symm.toLinearMap.continuous_of_finiteDimensional
  have himage : IsOpen (fieldTripleCoords '' W) := by
    have e : fieldTripleCoords '' W = tc.symm ⁻¹' W := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa [← htc x] using hx
      · intro hy
        refine ⟨_, hy, ?_⟩
        rw [← htc]
        simp
    rw [e]
    exact hW.1.preimage hback
  have hz : (0 : FieldTripleIndex L n k → ℝ) ∈ fieldTripleCoords '' W :=
    ⟨0, hW.2.1, by rw [← htc, map_zero]⟩
  exact (hW.2.2.2.2.contDiffAt (himage.mem_nhds hz)).of_le ENat.LEInfty.out
private theorem pauliUnitForm_mem (hdich : PeriodicLattice.LevelBondOrientationDichotomy)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 0 < k) (z : Fin 4 → ℤ) :
    pauliUnitForm L n k z ∈ edgeFormSpace L n k k := by
  classical
  have hpauli : ComplexMatrix2.pauliFamily 2 ∈ ComplexMatrix2.hermitianTraceless :=
    PowerExpCharts.pauliFamily_mem_hermitianTraceless 2
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · simp only [pauliUnitForm, extendOddly, if_pos hb]
    split_ifs
    · exact hpauli
    · exact ComplexMatrix2.hermitianTraceless.zero_mem
  · simp only [pauliUnitForm, extendOddly]
    rcases hdich L n k hL hn hk k le_rfl b with ⟨hb, hr⟩ | ⟨hr, hb⟩
    · rw [if_neg hr, if_pos hb]
      rfl
    · rw [if_pos hr, if_neg hb, neg_neg]
private theorem edgeForm_ext (hdich : PeriodicLattice.LevelBondOrientationDichotomy)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 0 < k)
    {X Y : edgeFormSpace L n k 0}
    (h : restrictToPositiveEdges (X : Edge L n k 0 → ComplexMatrix2) =
      restrictToPositiveEdges (Y : Edge L n k 0 → ComplexMatrix2)) :
    X = Y := by
  apply Subtype.ext
  funext b
  rcases hdich L n k hL hn hk 0 (Nat.zero_le k) b with ⟨hb, -⟩ | ⟨hr, -⟩
  · exact congrFun h ⟨b, hb⟩
  · have e : (X : Edge L n k 0 → ComplexMatrix2) b.opposite =
        (Y : Edge L n k 0 → ComplexMatrix2) b.opposite :=
      congrFun h ⟨b.opposite, hr⟩
    have hX : (X : Edge L n k 0 → ComplexMatrix2) b.opposite =
        -(X : Edge L n k 0 → ComplexMatrix2) b := X.2.2 b
    have hY : (Y : Edge L n k 0 → ComplexMatrix2) b.opposite =
        -(Y : Edge L n k 0 → ComplexMatrix2) b := Y.2.2 b
    rw [hX, hY] at e
    exact neg_injective e
private theorem restrict_mem_tracelessFunctions (X : edgeFormSpace L n k 0) :
    restrictToPositiveEdges (X : Edge L n k 0 → ComplexMatrix2) ∈
      GroupLieProduct.tracelessFunctions (PositiveEdge L n k 0) := by
  simp only [GroupLieProduct.tracelessFunctions]
  rw [Submodule.mem_pi]
  intro b _
  exact (X.2.1 b.1 b.2).2
private theorem coeffsOnEdges_sum {j : ℕ} {ι : Type*} [Fintype ι]
    (Ψ : edgeFormSpace L n k j ≃ₗ[ℝ] (Fin 3 × PositiveEdge L n k j → ℝ))
    (hΨ : ∀ (f : edgeFormSpace L n k j) i,
      toPauliCoeffs (restrictToPositiveEdges (f : Edge L n k j → ComplexMatrix2)) i = ((Ψ f i : ℝ) : ℂ))
    (c : ι → ℝ) (B : ι → edgeFormSpace L n k j) (idx) :
    PeriodicForm.coeffsOnEdges L n k j
        ((∑ i, c i • B i : edgeFormSpace L n k j) : Edge L n k j → ComplexMatrix2) idx =
      ∑ i, (c i : ℂ) * PeriodicForm.coeffsOnEdges L n k j (B i : Edge L n k j → ComplexMatrix2) idx := by
  simp only [PeriodicForm.coeffsOnEdges, hΨ, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  push_cast
  rfl
private theorem periodicResponse_sum (hc : PauliCoordsOrthonormal)
    (hI : ResponseImagesFullSide.ResponseImagesHold)
    (hR : ResponseOperators.Claim) (hf : BondSetFields.ProductStructureHolds)
    (hdich : PeriodicLattice.LevelBondOrientationDichotomy)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (hn : 0 < n)
    {ι : Type*} [Fintype ι] (c : ι → ℝ) (B : ι → edgeFormSpace L n k k) :
    periodicResponse L n k ((∑ i, c i • B i : edgeFormSpace L n k k) : Edge L n k k → ComplexMatrix2) =
      ∑ i, c i • periodicResponse L n k (B i : Edge L n k k → ComplexMatrix2) := by
  classical
  have hb₀ : Finite (Edge L n k 0) :=
    Set.finite_univ_iff.1 ((hf L hL k 0 (Nat.zero_le k)).1 n hn).2.1
  have hbₖ : Finite (Edge L n k k) := Set.finite_univ_iff.1 ((hf L hL k k le_rfl).1 n hn).2.1
  have : Finite (PositiveEdge L n k 0) := Subtype.finite
  have : Finite (PositiveEdge L n k k) := Subtype.finite
  letI : Fintype (Fin 3 × PositiveEdge L n k 0) := Fintype.ofFinite _
  letI : Fintype (Fin 3 × PositiveEdge L n k k) := Fintype.ofFinite _
  obtain ⟨Ψ₀, h₀, -⟩ := (hc L n k 0 hL hn (Nat.zero_le k)).1
  obtain ⟨Ψₖ, hₖ, -⟩ := (hc L n k k hL hn le_rfl).1
  set D : edgeFormSpace L n k k := ∑ i, c i • B i with hD
  set Y : edgeFormSpace L n k 0 :=
    ∑ i, c i • periodicResponse L n k (B i : Edge L n k k → ComplexMatrix2) with hY
  have atD := hI L hL k hk n hn D
  have atB := fun i => hI L hL k hk n hn (B i)
  have hsum : ∀ (idx) (i : ι), Summable fun j => BackgroundFieldResponse.responseKernel L k idx j *
      ((c i : ℂ) * PeriodicForm.coeffsOnEdges L n k k (B i : Edge L n k k → ComplexMatrix2) j) := by
    intro idx i
    have h := (Summable.of_norm ((atB i).resp_summable idx)).mul_left (c i : ℂ)
    refine h.congr fun j => ?_
    ring
  have hread : PeriodicForm.coeffsOnEdges L n k 0 (Y : Edge L n k 0 → ComplexMatrix2) =
      PeriodicForm.coeffsOnEdges L n k 0 (periodicResponse L n k (D : Edge L n k k → ComplexMatrix2)) := by
    funext idx
    have e₁ : PeriodicForm.coeffsOnEdges L n k k (D : Edge L n k k → ComplexMatrix2) = fun j =>
        ∑ i, (c i : ℂ) * PeriodicForm.coeffsOnEdges L n k k (B i : Edge L n k k → ComplexMatrix2) j :=
      funext fun j => coeffsOnEdges_sum Ψₖ hₖ c B j
    rw [hY, coeffsOnEdges_sum Ψ₀ h₀, atD.resp_coeffs, e₁]
    show _ = ∑' j, BackgroundFieldResponse.responseKernel L k idx j * ∑ i, (c i : ℂ) * _
    simp only [Finset.mul_sum]
    rw [Summable.tsum_finsetSum fun i _ => hsum idx i]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(atB i).resp_coeffs]
    show (c i : ℂ) * ∑' j, BackgroundFieldResponse.responseKernel L k idx j * _ = _
    rw [← tsum_mul_left]
    refine tsum_congr fun j => ?_
    ring
  obtain ⟨g, -, hg⟩ := atD.resp_isImage
  have hYc : ResponseOperators.ClassFnEqForm L n k 0
      (restrictToPositiveEdges (Y : Edge L n k 0 → ComplexMatrix2)) _ :=
    fun idx => (hg idx).trans (congrFun hread idx).symm
  obtain ⟨δ₀, -, hδ⟩ := hR
  obtain ⟨f, -, hu⟩ := ((hδ L hL k hk).torus_sides n hn).forms_bottom _
  have e := (hu _ ⟨restrict_mem_tracelessFunctions Y, hYc⟩).trans
    (hu _ ⟨restrict_mem_tracelessFunctions _, hg⟩).symm
  exact (edgeForm_ext hdich hL hn (by omega) e).symm
private theorem meshScaledResponse_sum (hc : PauliCoordsOrthonormal)
    (hI : ResponseImagesFullSide.ResponseImagesHold)
    (hR : ResponseOperators.Claim) (hf : BondSetFields.ProductStructureHolds)
    (hdich : PeriodicLattice.LevelBondOrientationDichotomy)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (hn : 0 < n)
    {ι : Type*} [Fintype ι] (c : ι → ℝ) (B : ι → edgeFormSpace L n k k) :
    meshScaledResponse L n k
        ((∑ i, c i • B i : edgeFormSpace L n k k) : Edge L n k k → ComplexMatrix2) =
      ∑ i, c i • meshScaledResponse L n k (B i : Edge L n k k → ComplexMatrix2) := by
  unfold meshScaledResponse
  rw [periodicResponse_sum hc hI hR hf hdich hL hk hn, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
section Abstract
variable {E₁ E₂ V : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂]
  [NormedSpace ℝ E₂] [AddCommGroup V] [Module ℝ V]
private theorem exists_bilinear_planeDeriv_sub (f₁ : E₁ → ℝ) (f₂ : E₂ → ℝ)
    (h₁ : ContDiffAt ℝ 2 f₁ 0) (h₂ : ContDiffAt ℝ 2 f₂ 0) (T₁ : V →ₗ[ℝ] E₁) (T₂ : V →ₗ[ℝ] E₂) :
    ∃ β : LinearMap.BilinForm ℝ V,
      (∀ v v' : V, deriv (fun s : ℝ => deriv (fun u : ℝ =>
        f₁ (T₁ (s • v + u • v')) - f₂ (T₂ (s • v + u • v'))) 0) 0 = β v v') ∧
      ∀ v : V, deriv (fun s : ℝ => deriv (fun u : ℝ => f₁ (T₁ (s • v + u • v))) 0) 0 -
        deriv (fun s : ℝ => deriv (fun u : ℝ => f₂ (T₂ (s • v + u • v))) 0) 0 = β v v := by
  refine ⟨LinearMap.mk₂ ℝ (fun v v' =>
      fderiv ℝ (fderiv ℝ f₁) 0 (T₁ v) (T₁ v') - fderiv ℝ (fderiv ℝ f₂) 0 (T₂ v) (T₂ v'))
      (fun v v' w => by simp only [map_add, add_apply]; ring)
      (fun r v w => by
        simp only [map_smul, smul_apply, smul_eq_mul]; ring)
      (fun v v' w => by simp only [map_add]; ring)
      (fun r v w => by simp only [map_smul, smul_eq_mul]; ring), fun v v' => ?_, fun v => ?_⟩
  · exact planeDeriv_sub f₁ f₂ h₁ h₂ T₁ T₂ v v'
  · rw [(hasDerivAt_planeDeriv_linearMap f₁ h₁ T₁ v v).2.deriv,
      (hasDerivAt_planeDeriv_linearMap f₂ h₂ T₂ v v).2.deriv]
    rfl
end Abstract
private def backgroundOnlyLinear (L n k : ℕ) : edgeFormSpace L n k 0 →ₗ[ℝ] LevelTriple L n k where
  toFun := backgroundOnlyTriple
  map_add' _ _ := Prod.ext (Prod.ext rfl (add_zero _).symm)
    (Prod.ext (add_zero _).symm (add_zero _).symm)
  map_smul' r _ := Prod.ext (Prod.ext rfl (smul_zero r).symm)
    (Prod.ext (smul_zero r).symm (smul_zero r).symm)
private theorem matExp_zero : ComplexMatrix2.matExp 0 = 1 := by
  simp [ComplexMatrix2.matExp]
private theorem expMove_background (X : edgeFormSpace L n k 0) :
    expMove ((X, 0) : LevelForms L n k) (unitPoint L n k) =
      quietPoint (PeriodicLattice.expTwist (X : Edge L n k 0 → ComplexMatrix2) 1) := by
  unfold expMove quietPoint
  congr 1
  funext i c
  have h : (((0 : (i : Fin k) → edgeFormSpace L n k (i + 1)) i : edgeFormSpace L n k (i + 1)) :
      Edge L n k (i + 1) → ComplexMatrix2) c = 0 := rfl
  show ComplexMatrix2.matExp (Complex.I • (((0 : (i : Fin k) → edgeFormSpace L n k (i + 1)) i :
      edgeFormSpace L n k (i + 1)) : Edge L n k (i + 1) → ComplexMatrix2) c) * 1 = 1
  rw [h, smul_zero, matExp_zero, mul_one]
private theorem tripleFreeEnergy_background (a : ℝ) (X : edgeFormSpace L n k 0) :
    tripleFreeEnergy a (backgroundOnlyTriple X) =
      chainFreeEnergy a
        (quietPoint (PeriodicLattice.expTwist (X : Edge L n k 0 → ComplexMatrix2) 1)) 0 0 := by
  rw [← expMove_background]
  rfl
private theorem exists_levelTriple_equiv (hc : PauliCoordsOrthonormal)
    (hf : BondSetFields.ProductStructureHolds) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) : ∃ N : ℕ, Nonempty ((Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k) := by
  classical
  have fin : ∀ j, j ≤ k → Module.Finite ℝ (edgeFormSpace L n k j) := by
    intro j hj
    have hb : Finite (Edge L n k j) := Set.finite_univ_iff.1 ((hf L hL k j hj).1 n hn).2.1
    have : Finite (PositiveEdge L n k j) := Subtype.finite
    letI : Fintype (Fin 3 × PositiveEdge L n k j) := Fintype.ofFinite _
    obtain ⟨Ψ, -, -⟩ := (hc L n k j hL hn hj).1
    exact Module.Finite.equiv Ψ.symm
  have f₀ : Module.Finite ℝ (edgeFormSpace L n k 0) := fin 0 (Nat.zero_le k)
  have fₖ : Module.Finite ℝ (edgeFormSpace L n k k) := fin k le_rfl
  have fᵢ : ∀ i : Fin k, Module.Finite ℝ (edgeFormSpace L n k (i + 1)) := fun i => fin _ i.2
  have f₁ : Module.Finite ℝ ((i : Fin k) → edgeFormSpace L n k (i + 1)) := Module.Finite.pi
  have f₂ : Module.Finite ℝ (LevelForms L n k) := Module.Finite.prod
  have f₃ : Module.Finite ℝ (LevelForms L n k × edgeFormSpace L n k k) := Module.Finite.prod
  have f₄ : Module.Finite ℝ (LevelTriple L n k) := Module.Finite.prod
  exact ⟨_, ⟨(Module.finBasis ℝ (LevelTriple L n k)).equivFun.symm⟩⟩
private theorem exists_bilinear_hessian (hchain : ChainFreeEnergyAnalytic.Claim)
    (hbg : ExpChartFunctionalClaim)
    (hc : PauliCoordsOrthonormal) (hf : BondSetFields.ProductStructureHolds)
    {a : ℝ} (ha : 0 < a) (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    (hn : 0 < n) :
    ∃ β : LinearMap.BilinForm ℝ (edgeFormSpace L n k 0),
      (∀ A A' : edgeFormSpace L n k 0,
        Tower.leftSecondDeriv (chainMinusBackground a) (Tower.trivialField L n k 0)
          (A : Edge L n k 0 → ComplexMatrix2) (A' : Edge L n k 0 → ComplexMatrix2) = β A A') ∧
      ∀ A : edgeFormSpace L n k 0,
        hessianOfFreeEnergy a (backgroundOnlyTriple A) (backgroundOnlyTriple A) -
          fieldFunctionalSecondDeriv L n k (A, 0, 0) (A, 0, 0) = β A A := by
  classical
  have hb₀ : Finite (Edge L n k 0) :=
    Set.finite_univ_iff.1 ((hf L hL k 0 (Nat.zero_le k)).1 n hn).2.1
  have hbₖ : Finite (Edge L n k k) := Set.finite_univ_iff.1 ((hf L hL k k le_rfl).1 n hn).2.1
  have : Finite (PositiveEdge L n k 0) := Subtype.finite
  have : Finite (PositiveEdge L n k k) := Subtype.finite
  letI : Fintype (PositiveEdge L n k 0) := Fintype.ofFinite _
  letI : Fintype (PositiveEdge L n k k) := Fintype.ofFinite _
  obtain ⟨tc, htc⟩ := exists_pauliCoordEquiv (k := k) hc hL hn
  have h₂ := contDiffAt_expChartFunctionalInCoords tc htc ((hbg L n k hL hn hk).2)
  obtain ⟨N, ⟨e⟩⟩ := exists_levelTriple_equiv (k := k) hc hf hL hn
  have h₁ : ContDiffAt ℝ 2 (fun w => tripleFreeEnergy a (e w)) 0 :=
    ((hchain a ha L hL k n hk hn).1 N e).1.contDiffAt
  obtain ⟨T₁, hT₁⟩ : ∃ T : edgeFormSpace L n k 0 →ₗ[ℝ] (Fin N → ℝ),
      ∀ X, T X = e.symm (backgroundOnlyTriple X) :=
    ⟨e.symm.toLinearMap ∘ₗ backgroundOnlyLinear L n k, fun _ => rfl⟩
  obtain ⟨T₂, hT₂⟩ : ∃ T : edgeFormSpace L n k 0 →ₗ[ℝ] (FieldTripleIndex L n k → ℝ),
      ∀ X, T X = tc (X, 0, 0) :=
    ⟨tc.toLinearMap ∘ₗ LinearMap.inl ℝ _ _, fun _ => rfl⟩
  have hF₁ : ∀ X, tripleFreeEnergy a (e (T₁ X)) = tripleFreeEnergy a (backgroundOnlyTriple X) := by
    intro X
    rw [hT₁, LinearEquiv.apply_symm_apply]
  have hF₂ : ∀ X : edgeFormSpace L n k 0, expChartFunctionalInCoords L n k (T₂ X) =
      backgroundFunctional (PeriodicLattice.expTwist (X : Edge L n k 0 → ComplexMatrix2) 1) 0 0 := by
    intro X
    rw [hT₂, expChartFunctionalInCoords_apply tc htc, expTwist_one_eq]
    rfl
  obtain ⟨β, hβ₁, hβ₂⟩ := exists_bilinear_planeDeriv_sub _ _ h₁ h₂ T₁ T₂
  refine ⟨β, fun A A' => ?_, fun A => ?_⟩
  · have hline : ∀ s t : ℝ, algebraMap ℝ ℂ s • (A : Edge L n k 0 → ComplexMatrix2) +
        algebraMap ℝ ℂ t • (A' : Edge L n k 0 → ComplexMatrix2) =
        ((s • A + t • A' : edgeFormSpace L n k 0) : Edge L n k 0 → ComplexMatrix2) := by
      intro s t
      funext b
      show algebraMap ℝ ℂ s • (A : Edge L n k 0 → ComplexMatrix2) b +
        algebraMap ℝ ℂ t • (A' : Edge L n k 0 → ComplexMatrix2) b =
        s • (A : Edge L n k 0 → ComplexMatrix2) b + t • (A' : Edge L n k 0 → ComplexMatrix2) b
      rw [algebraMap_smul, algebraMap_smul]
    have hs : ∀ s t : ℝ, chainMinusBackground a (PeriodicLattice.expTwist
        (algebraMap ℝ ℂ s • (A : Edge L n k 0 → ComplexMatrix2) +
          algebraMap ℝ ℂ t • (A' : Edge L n k 0 → ComplexMatrix2)) 1) =
        tripleFreeEnergy a (e (T₁ (s • A + t • A'))) -
          expChartFunctionalInCoords L n k (T₂ (s • A + t • A')) := by
      intro s t
      rw [hline, hF₁, hF₂, tripleFreeEnergy_background]
      rfl
    have hgoal := hβ₁ A A'
    rw [← hgoal]
    show deriv (fun s : ℝ => deriv (fun t : ℝ => chainMinusBackground a (PeriodicLattice.expTwist
      (algebraMap ℝ ℂ s • (A : Edge L n k 0 → ComplexMatrix2) +
        algebraMap ℝ ℂ t • (A' : Edge L n k 0 → ComplexMatrix2)) 1)) 0) 0 = _
    simp only [hs]
  · have c₁ : hessianOfFreeEnergy a (backgroundOnlyTriple A) (backgroundOnlyTriple A) =
        deriv (fun s : ℝ => deriv (fun u : ℝ =>
          tripleFreeEnergy a (e (T₁ (s • A + u • A)))) 0) 0 := by
      have hl : ∀ s u : ℝ,
          tripleFreeEnergy a (s • backgroundOnlyTriple A + u • backgroundOnlyTriple A) =
          tripleFreeEnergy a (e (T₁ (s • A + u • A))) := by
        intro s u
        rw [hF₁]
        have h := map_add (backgroundOnlyLinear L n k) (s • A) (u • A)
        rw [map_smul, map_smul] at h
        exact congrArg (tripleFreeEnergy a) h.symm
      unfold hessianOfFreeEnergy
      simp only [hl]
    have c₂ : fieldFunctionalSecondDeriv L n k (A, 0, 0) (A, 0, 0) =
        deriv (fun s : ℝ => deriv (fun u : ℝ =>
          expChartFunctionalInCoords L n k (T₂ (s • A + u • A))) 0) 0 := by
      have hl : ∀ s u : ℝ, fieldFunctional (s • ((A, 0, 0) : RealPeriodicField L n k) +
          u • ((A, 0, 0) : RealPeriodicField L n k)) =
          expChartFunctionalInCoords L n k (T₂ (s • A + u • A)) := by
        intro s u
        rw [hF₂]
        have hr : s • ((A, 0, 0) : RealPeriodicField L n k) +
            u • ((A, 0, 0) : RealPeriodicField L n k) =
            ((s • A + u • A, 0, 0) : RealPeriodicField L n k) :=
          Prod.ext rfl (Prod.ext (by simp) (by simp))
        rw [hr]
        rfl
      unfold fieldFunctionalSecondDeriv
      simp only [hl]
    rw [c₁, c₂]
    exact hβ₂ A
private theorem cosinePhase_sub {s : ℕ} [NeZero s] {t : ℝ} {j : ℤ}
    (ht : t * s = 2 * Real.pi * j) (x y : TorusSite s) :
    cosinePhase t x * cosinePhase t y + sinePhase t x * sinePhase t y = cosinePhase t (x - y) := by
  simp only [cosinePhase, sinePhase]
  rw [← Real.cos_sub, ← mul_sub]
  have hz : (((centredCoords (x - y) 0 : ℤ) : ZMod s)) =
      ((centredCoords x 0 - centredCoords y 0 : ℤ) : ZMod s) := by
    simp [centredCoords]
  obtain ⟨d, hd⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ s).mp hz
  have e : t * ((centredCoords (x - y) 0 : ℤ) : ℝ) =
      t * ((centredCoords x 0 : ℝ) - (centredCoords y 0 : ℝ)) -
        ((j * d : ℤ) : ℝ) * (2 * Real.pi) := by
    have h : (centredCoords x 0 : ℝ) - (centredCoords y 0 : ℝ) -
        ((centredCoords (x - y) 0 : ℤ) : ℝ) = (s : ℝ) * (d : ℝ) := by
      exact_mod_cast hd
    push_cast
    linear_combination (-t) * h - (d : ℝ) * ht
  rw [e, Real.cos_sub_int_mul_two_pi]
abbrev _root_.YangMills.SharedProofs.p72641 := @cosinePhase_sub
theorem differenceKernelCosineSum_holds (hT : DifferenceKernelTranslationInvariant)
    (hchain : ChainFreeEnergyAnalytic.Claim)
    (hbg : ExpChartFunctionalClaim)
    (hc : PauliCoordsOrthonormal) (hf : BondSetFields.ProductStructureHolds)
    (hI : ResponseImagesFullSide.ResponseImagesHold)
    (hR : ResponseOperators.Claim)
    (hdich : PeriodicLattice.LevelBondOrientationDichotomy) :
    DifferenceKernelCosineSum := by
  intro a ha L _ hLs k hk n₀ m t ht
  filter_upwards [hT a ha L hLs k hk, eventually_ge_atTop n₀, eventually_gt_atTop 0]
    with n hcar hn₀ hn C S hCS
  obtain ⟨hC, hS⟩ := hCS
  obtain ⟨β, hβ, hβ'⟩ := exists_bilinear_hessian hchain hbg hc hf ha hLs hk hn
  have hj : t * ((2 * L ^ n : ℕ) : ℝ) = 2 * Real.pi * ((m * (L : ℤ) ^ (n - n₀) : ℤ) : ℝ) := by
    have hp : (L : ℝ) ^ n = (L : ℝ) ^ n₀ * (L : ℝ) ^ (n - n₀) := by
      rw [← pow_add, Nat.add_sub_cancel' hn₀]
    have hL0 : (L : ℝ) ≠ 0 := by
      have : (0 : ℝ) < L := by
        have := hLs.2
        exact_mod_cast (by omega : 0 < L)
      exact this.ne'
    rw [ht]
    push_cast
    rw [hp]
    field_simp
  let u : TorusSite (2 * L ^ n) → edgeFormSpace L n k k := fun x =>
    ⟨pauliUnitForm L n k (centredCoords x), pauliUnitForm_mem hdich hLs hn (by omega) _⟩
  let A : TorusSite (2 * L ^ n) → edgeFormSpace L n k 0 := fun x =>
    meshScaledResponse L n k (u x : Tower.Edge L n k k → ComplexMatrix2)
  have hA : ∀ y x, β (A y) (A x) =
      differenceKernelFinite a L n k (centredCoords (x - y)) :=
    fun y x => (hβ _ _).symm.trans (hcar y x)
  have hform : ∀ (f : TorusSite (2 * L ^ n) → ℝ) (D : edgeFormSpace L n k k),
      (D : Tower.Edge L n k k → ComplexMatrix2) = planeWaveValues L n k f →
      freeEnergyHessianAtResponse a D - normaliserHessianAtResponse L n k D =
        ∑ y, ∑ x, f y * f x * β (A y) (A x) := by
    intro f D hD
    have hDs : D = ∑ x, f x • u x := by
      apply Subtype.ext
      rw [hD, AddSubmonoidClass.coe_finsetSum]
      exact Finset.sum_congr rfl fun _ _ => rfl
    have hsum : meshScaledResponse L n k (D : Tower.Edge L n k k → ComplexMatrix2) =
        ∑ x, f x • A x := by
      rw [hDs]
      exact meshScaledResponse_sum hc hI hR hf hdich hLs hk hn f u
    unfold freeEnergyHessianAtResponse normaliserHessianAtResponse
    rw [hβ', hsum]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
    ring
  have hrow : ∀ y : TorusSite (2 * L ^ n),
      (∑ x, cosinePhase t y * cosinePhase t x * β (A y) (A x)) +
        (∑ x, sinePhase t y * sinePhase t x * β (A y) (A x)) =
          differenceCosineSum a L n k t := by
    intro y
    rw [← Finset.sum_add_distrib]
    unfold differenceCosineSum
    refine (Finset.sum_congr rfl fun x _ => ?_).trans
      (Fintype.sum_equiv (Equiv.subRight y) _ _ fun _ => rfl)
    have ex : (Equiv.subRight y) x = x - y := rfl
    rw [hA, ← add_mul, ex, ← cosinePhase_sub hj x y]
    ring
  rw [hform _ C hC, hform _ S hS, ← Finset.sum_add_distrib]
  simp only [hrow]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : ((Fintype.card (TorusSite (2 * L ^ n)) : ℕ) : ℝ) = (2 * (L : ℝ) ^ n) ^ 4 := by
    simp [ZMod.card]
  rw [hcard]
end YangMills.Construction.RunningCouplingSlope.CosineSumProof
end
