import YangMills.Construction.RotationInvariance.DensityOfThePlateFunctionsAtDistinctPointsProof
import YangMills.Construction.RotationInvariance.HarmonicsAtDistinctPointsProof
import Mathlib
set_option autoImplicit false
open Complex (I)
open YangMills.Construction.RealPlane YangMills.Construction.ForwardTube
open YangMills.Construction.Matrices.GroupLieProduct.Subspaces.AnalyticCalculus (scalarEquiv)
open Filter Topology
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.TubeUnionHarmonicsProof
def IsSampleInversion (F : Finset ℤ) {p : ℕ} (W : ℤ → Fin p → ℂ) : Prop :=
  ∀ b : ℤ → ℂ, ∀ h ∈ F,
    ∑ j : Fin p, W h j * ∑ k ∈ F, b k * Complex.exp (-(4 * (k : ℂ) * (((j : ℕ) : ℝ) : ℂ))) = b h
theorem exists_sampleInversion (F : Finset ℤ) :
    ∃ W : ℤ → Fin F.card → ℂ, IsSampleInversion F W := by
  classical
  let e := F.equivFin
  let v : Fin F.card → ℂ := fun i => Complex.exp (-(4 * (((e.symm i : F) : ℤ) : ℂ)))
  have hreal : ∀ k : ℤ, Complex.exp (-(4 * (k : ℂ))) = ((Real.exp (-(4 * (k : ℝ))) : ℝ) : ℂ) := by
    intro k
    push_cast
    rfl
  have hv : Function.Injective v := by
    intro i i' hii
    simp only [v, hreal] at hii
    have h1 := Real.exp_injective (Complex.ofReal_injective hii)
    have h2 : (((e.symm i : F) : ℤ) : ℝ) = (((e.symm i' : F) : ℤ) : ℝ) := by linarith
    have h3 : ((e.symm i : F) : ℤ) = ((e.symm i' : F) : ℤ) := by exact_mod_cast h2
    exact e.symm.injective (Subtype.ext h3)
  let A := Matrix.vandermonde v
  have hdet : A.det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hv
  have hAinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hdet)
  refine ⟨fun h j => if hh : h ∈ F then A⁻¹ j (e ⟨h, hh⟩) else 0, ?_⟩
  intro b h hh
  have hsum : ∀ j : Fin F.card,
      ∑ k ∈ F, b k * Complex.exp (-(4 * (k : ℂ) * (((j : ℕ) : ℝ) : ℂ))) =
        ∑ i, b (e.symm i) * A i j := by
    intro j
    rw [← Finset.sum_coe_sort F, ← e.symm.sum_comp]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    simp only [A, v, Matrix.vandermonde_apply]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp only [dif_pos hh, hsum]
  calc ∑ j, A⁻¹ j (e ⟨h, hh⟩) * ∑ i, b (e.symm i) * A i j
      = ∑ i, b (e.symm i) * (A * A⁻¹) i (e ⟨h, hh⟩) := by
        simp only [Matrix.mul_apply, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    _ = b h := by
        rw [hAinv]
        simp [Matrix.one_apply]
theorem forall_pairCoord {p : ℕ} {C : Fin (p * 2) → Prop}
    (h0 : ∀ i, C (finProdFinEquiv (i, 0))) (h1 : ∀ i, C (finProdFinEquiv (i, 1))) : ∀ k, C k := by
  intro k
  obtain ⟨⟨i, c⟩, rfl⟩ := finProdFinEquiv.surjective k
  exact (Fin.forall_fin_two (p := fun c => C (finProdFinEquiv (i, c)))).mpr ⟨h0 i, h1 i⟩ c
def pairTupleCLE (p : ℕ) : (Fin p → ℂ × ℂ) ≃L[ℂ] Coordinates.ComplexCoordinates (p * 2) :=
  LinearEquiv.toContinuousLinearEquiv
    { pairTupleEquiv p with
      map_add' := fun v w => by
        funext k
        revert k
        refine forall_pairCoord (fun i => ?_) (fun i => ?_) <;>
          simp [pairTupleEquiv_apply_fst, pairTupleEquiv_apply_snd]
      map_smul' := fun c v => by
        funext k
        revert k
        refine forall_pairCoord (fun i => ?_) (fun i => ?_) <;>
          simp [pairTupleEquiv_apply_fst, pairTupleEquiv_apply_snd] }
theorem pairTupleCLE_apply {p : ℕ} (v : Fin p → ℂ × ℂ) :
    pairTupleCLE p v = pairTupleEquiv p v := rfl
theorem pairTupleCLE_symm_apply {p : ℕ} (w : Coordinates.ComplexCoordinates (p * 2)) :
    (pairTupleCLE p).symm w = (pairTupleEquiv p).symm w := rfl
theorem isHolomorphicIn_of_differentiableOn {N N' : ℕ} {O : Set (Coordinates.ComplexCoordinates N)}
    (hO : IsOpen O) {f : Coordinates.ComplexCoordinates N → Coordinates.ComplexCoordinates N'}
    (hf : DifferentiableOn ℂ f O) : Coordinates.ComplexCoordinates.IsHolomorphicIn O f := by
  refine ⟨hO, hf.continuousOn, fun a ha j => ?_⟩
  have hc : ContinuousAt (fun ζ : ℂ => a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j) 0 := by
    fun_prop
  have hnear : ∀ᶠ ζ in 𝓝 (0 : ℂ), a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j ∈ O :=
    hc.eventually_mem (hO.mem_nhds (by simpa using ha))
  filter_upwards [hnear] with ζ hζ
  have hd : DifferentiableAt ℂ f (a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j) :=
    hf.differentiableAt (hO.mem_nhds hζ)
  exact DifferentiableAt.comp ζ hd (by fun_prop)
theorem isOpen_image_pairTupleEquiv {p : ℕ} {O : Set (Fin p → ℂ × ℂ)} (hO : IsOpen O) :
    IsOpen (pairTupleEquiv p '' O) :=
  (pairTupleCLE p).toHomeomorph.isOpenMap O hO
theorem differentiableOn_comp_pairTupleEquiv_symm {p : ℕ} {O : Set (Fin p → ℂ × ℂ)}
    {f : (Fin p → ℂ × ℂ) → ℂ} (hf : DifferentiableOn ℂ f O) :
    DifferentiableOn ℂ (fun w => f ((pairTupleEquiv p).symm w)) (pairTupleEquiv p '' O) := by
  have h := hf.comp (pairTupleCLE p).symm.differentiable.differentiableOn
    (s := pairTupleEquiv p '' O) (by
      rintro _ ⟨z, hz, rfl⟩
      simpa [pairTupleCLE_symm_apply] using hz)
  exact h
theorem holomorphicOnTuples_of_differentiableOn {p : ℕ} {O : Set (Fin p → ℂ × ℂ)}
    (hO : IsOpen O) {f : (Fin p → ℂ × ℂ) → ℂ} (hf : DifferentiableOn ℂ f O) :
    HolomorphicOnTuples O f := by
  refine isHolomorphicIn_of_differentiableOn (isOpen_image_pairTupleEquiv hO) ?_
  rw [differentiableOn_pi]
  intro i
  exact differentiableOn_comp_pairTupleEquiv_symm hf
theorem differentiableOn_of_holomorphicOnTuples
    (hP : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties) {p : ℕ}
    {O : Set (Fin p → ℂ × ℂ)} {f : (Fin p → ℂ × ℂ) → ℂ} (hf : HolomorphicOnTuples O f) :
    DifferentiableOn ℂ f O := by
  intro z hz
  have hf' : Coordinates.ComplexCoordinates.IsHolomorphicIn (pairTupleEquiv p '' O)
      (scalarEquiv ∘ f ∘ (pairTupleEquiv p).symm) := hf
  obtain ⟨L, hL⟩ := ((hP.1 _ _ hf'.1).1 1 _ hf').2.2.1 (pairTupleEquiv p z) ⟨z, hz, rfl⟩
  have hC : HasFDerivAt (scalarEquiv ∘ f ∘ (pairTupleEquiv p).symm) L
      (pairTupleEquiv p z) := hasFDerivAt_of_restrictScalars ℝ hL rfl
  have h3 : DifferentiableAt ℂ
      ((scalarEquiv ∘ f ∘ (pairTupleEquiv p).symm) ∘ pairTupleCLE p) z :=
    DifferentiableAt.comp z hC.differentiableAt (pairTupleCLE p).differentiableAt
  have h4 := (differentiableAt_pi.mp h3) 0
  have heq : (fun w => ((scalarEquiv ∘ f ∘ (pairTupleEquiv p).symm) ∘
      pairTupleCLE p) w 0) = f := by
    funext w
    simp [pairTupleCLE_apply, scalarEquiv]
  rw [heq] at h4
  exact h4.differentiableWithinAt
theorem continuous_vecRe : Continuous vecRe := by apply _root_.YangMills.Construction.EuclideanFunctionals.DistinctHarmonics.continuous_vecRe <;> assumption
theorem continuous_tupleRe {p : ℕ} :
    Continuous (tupleRe : (Fin p → ℂ × ℂ) → Fin p → RealPlane) :=
  continuous_pi fun i => continuous_vecRe.comp (continuous_apply i)
theorem tupleRe_embedPlaneTuple {p : ℕ} (y : Fin p → RealPlane) :
    tupleRe (embedPlaneTuple y) = y := by apply _root_.YangMills.Construction.EuclideanFunctionals.DistinctHarmonics.tupleRe_embedPlaneTuple <;> assumption
theorem pairTupleEquiv_embed_tupleRe {p : ℕ} (t : Fin p → ℂ × ℂ) :
    pairTupleEquiv p (embedPlaneTuple (tupleRe t)) =
      fun j => ((pairTupleEquiv p t j).re : ℂ) := by
  funext k
  revert k
  refine forall_pairCoord (fun i => ?_) (fun i => ?_) <;>
    simp [pairTupleEquiv_apply_fst, pairTupleEquiv_apply_snd, embedPlaneTuple, embedPlane, tupleRe,
      vecRe]
theorem pairTupleEquiv_embedPlaneTuple_mem_realLocus {p : ℕ} (y : Fin p → RealPlane) :
    pairTupleEquiv p (embedPlaneTuple y) ∈ Coordinates.ComplexCoordinates.realLocus (p * 2) := by apply _root_.YangMills.Construction.EuclideanFunctionals.HarmonicDensity.realCoords_mem_realLocus <;> assumption
theorem embedPlaneTuple_tupleRe_of_mem_realLocus {p : ℕ} {t : Fin p → ℂ × ℂ}
    (ht : pairTupleEquiv p t ∈ Coordinates.ComplexCoordinates.realLocus (p * 2)) :
    embedPlaneTuple (tupleRe t) = t := by
  apply (pairTupleEquiv p).injective
  rw [pairTupleEquiv_embed_tupleRe]
  funext k
  exact Complex.ext (by simp) (by simpa using (ht k).symm)
theorem eqOn_zero_of_eqOn_zero_real
    (hZ : Analysis.ZerosOfAnalyticMapsAndThinSets) {p : ℕ} (hp : 1 ≤ p)
    {T : Set (Fin p → ℂ × ℂ)} (hT : IsOpen T) (hc : Convex ℝ T)
    (hre : ∀ z ∈ T, embedPlaneTuple (tupleRe z) ∈ T)
    {g : (Fin p → ℂ × ℂ) → ℂ} (hg : DifferentiableOn ℂ g T)
    {A : Set (Fin p → RealPlane)} (hA : IsOpen A) (hne : A.Nonempty)
    (hAT : ∀ y ∈ A, embedPlaneTuple y ∈ T) (h0 : ∀ y ∈ A, g (embedPlaneTuple y) = 0) :
    ∀ z ∈ T, g z = 0 := by
  have hlin : IsLinearMap ℝ (pairTupleEquiv p) :=
    ((pairTupleCLE p).toLinearMap.restrictScalars ℝ).isLinear
  have hmain := (hZ (p * 2) (by omega)).1 (pairTupleEquiv p '' T)
    (isOpen_image_pairTupleEquiv hT) (hc.is_linear_image hlin)
    (by
      rintro _ ⟨t, ht, rfl⟩
      exact ⟨_, hre t ht, pairTupleEquiv_embed_tupleRe t⟩)
    (fun w => g ((pairTupleEquiv p).symm w))
    (by
      refine isHolomorphicIn_of_differentiableOn (isOpen_image_pairTupleEquiv hT) ?_
      rw [differentiableOn_pi]
      intro i
      exact differentiableOn_comp_pairTupleEquiv_symm hg)
    (pairTupleEquiv p '' (embedPlaneTuple '' A))
    (by
      obtain ⟨y, hy⟩ := hne
      exact ⟨_, _, ⟨y, hy, rfl⟩, rfl⟩)
    (by
      rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨⟨_, hAT y hy, rfl⟩, pairTupleEquiv_embedPlaneTuple_mem_realLocus y⟩)
    ⟨pairTupleEquiv p '' (tupleRe ⁻¹' A),
      isOpen_image_pairTupleEquiv (hA.preimage continuous_tupleRe), by
        ext w
        constructor
        · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
          refine ⟨⟨_, ?_, rfl⟩, pairTupleEquiv_embedPlaneTuple_mem_realLocus y⟩
          simpa [tupleRe_embedPlaneTuple] using hy
        · rintro ⟨⟨t, ht, rfl⟩, hw⟩
          exact ⟨_, ⟨_, ht, embedPlaneTuple_tupleRe_of_mem_realLocus hw⟩, rfl⟩⟩
    (by
      rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      simpa using h0 y hy)
  intro z hz
  simpa using hmain (pairTupleEquiv p z) ⟨z, hz, rfl⟩
theorem differentiable_imagBoostTuple {n : ℕ} (s : ℝ) :
    Differentiable ℂ (imagBoostTuple (n := n) s) := by
  rw [differentiable_pi]
  intro i
  unfold imagBoostTuple imagBoost complexBoost ofLightConeCoords lightConePlus lightConeMinus
  fun_prop
theorem complexBoost_embedPlane (hR : RotationRules.Holds)
    (t : ℝ) (a : RealPlane) :
    complexBoost (t : ℂ) (embedPlane a) = embedPlane (RealPlane.rotate t a) := by
  obtain ⟨-, -, -, -, -, -, -, hform, -, -, -⟩ := hR.1
  rw [hform]
  simp [embedPlane, RealPlane.rotate]
theorem rotate_neg_rotate (t : ℝ) (a : RealPlane) :
    RealPlane.rotate (-t) (RealPlane.rotate t a) = a := by apply _root_.YangMills.Construction.EuclideanFunctionals.TwoPointTopFrequency.rotate_neg_rotate <;> assumption
theorem continuous_rotate (t : ℝ) : Continuous (RealPlane.rotate t) := by apply _root_.YangMills.Construction.EuclideanFunctionals.TwoPointTopFrequency.continuous_rotate <;> assumption
def unturnPermute (υ : rightAngleMultiples) {n : ℕ} (ς : Equiv.Perm (Fin n))
    (y : Fin n → RealPlane) : Fin n → RealPlane :=
  fun i => RealPlane.rotate (-(υ : ℝ)) (y (ς i))
theorem continuous_unturnPermute (υ : rightAngleMultiples) {n : ℕ} (ς : Equiv.Perm (Fin n)) :
    Continuous (unturnPermute υ ς) :=
  continuous_pi fun _ => (continuous_rotate _).comp (continuous_apply _)
theorem embedPlaneTuple_unturnPermute
    (hR : RotationRules.Holds)
    (υ : rightAngleMultiples) {n : ℕ} (ς : Equiv.Perm (Fin n)) (y : Fin n → RealPlane) :
    embedPlaneTuple (unturnPermute υ ς y) =
      complexBoostTuple ((-(υ : ℝ) : ℝ) : ℂ) (permuteTuple ς (embedPlaneTuple y)) := by
  funext i
  exact (complexBoost_embedPlane hR _ _).symm
theorem expansion_on_turned_pencil
    (hOne : UnionKernel.Holds)
    (hAngle : AngleFunctionOnPencil.Holds)
    (hTop : MaxFrequencyFacts.Holds)
    (hR : RotationRules.Holds)
    {m : SharpScale} {S : ConnFamily} (d : PlaneDataWithAperture m S) {q : ℕ} (hq : 1 ≤ q)
    (φ : Fin (q + 1) → realLabels) (υ : rightAngleMultiples) (ς : Equiv.Perm (Fin (q + 1)))
    {y : Fin (q + 1) → RealPlane}
    (hy : unturnPermute υ ς y ∈ pencilSet d.angle (q + 1)) :
    embedPlaneTuple y ∈ orderedTube υ ς ∧
    ∀ s : ℝ, tubeUnionFunction S φ (imagBoostTuple s (embedPlaneTuple y)) =
      ∑ h ∈ Finset.Icc (-(maxFrequency S d.angle (q + 1) : ℤ))
          (maxFrequency S d.angle (q + 1) : ℤ),
        angleHarmonic S d.angle (unturnPermute υ ς y) (permuteTuple ς φ) h *
          Complex.exp (-(4 * (h : ℂ) * (s : ℂ))) := by
  obtain ⟨-, -, -, -, hlin, hgrp, -, -, -, -, -⟩ := hR.1
  have hRb := hR.2.1 q hq
  set y' := unturnPermute υ ς y with hy'
  set z := embedPlaneTuple y with hz
  have hdiff : planeTupleDiffs y' = complexBoostTuple ((-(υ : ℝ) : ℝ) : ℂ)
      (complexDifferences (permuteTuple ς z)) := by
    have h1 : planeTupleDiffs y' = complexDifferences (embedPlaneTuple y') :=
      (complexDifferences_embedPlaneTuple y').symm
    rw [h1, hy', embedPlaneTuple_unturnPermute hR]
    exact (hRb _ _ 0 1 1 φ).2.1
  have htube : ∀ i, planeTupleDiffs y' i ∈ forwardTube := by
    intro i
    have hsec : successiveDifferences y' i ∈ coneSector d.angle := hy i
    have hhalf := (hR.2.2.2.2.2 d.angle).2.2.1 hsec
    have hmem : embedPlane (successiveDifferences y' i) ∈ embedPlane '' openRightHalf := ⟨_, hhalf, rfl⟩
    rw [← hR.2.2.2.2.1.2.1] at hmem
    exact hmem.1
  have hzT : z ∈ orderedTube υ ς := by
    intro i
    refine ⟨planeTupleDiffs y' i, htube i, ?_⟩
    rw [hdiff]
    have hc : (((-(υ : ℝ) : ℝ)) : ℂ) = -(((υ : ℝ)) : ℂ) := by push_cast; rfl
    rw [hc]
    exact (hlin ((υ : ℝ) : ℂ)).2.2.2 (complexDifferences (permuteTuple ς z) i)
  refine ⟨hzT, fun s => ?_⟩
  have hone := hOne m S d q hq φ υ υ ς ς
  have hzs : imagBoostTuple s z ∈ orderedTube υ ς :=
    (hone.2.1.2.2.2 z hzT).2.1 s
  have hK := hone.2.2.2.2.2.1.1 υ ς _ hzs
  have hcomm : unrotate υ
      (complexDifferences (permuteTuple ς (imagBoostTuple s z))) =
      complexBoostTuple (I * (s : ℂ)) (planeTupleDiffs y') := by
    have h2 : permuteTuple ς (imagBoostTuple s z) =
        complexBoostTuple (I * (s : ℂ)) (permuteTuple ς z) := rfl
    rw [h2, (hRb _ _ 0 1 1 φ).2.1, hdiff]
    funext i
    exact congr_fun ((hgrp _ _).1.trans (hgrp _ _).2)
      (complexDifferences (permuteTuple ς z) i)
  have hA := (hAngle m S d q hq y' hy (permuteTuple ς φ)).2.2.2.1.2.1 s
  have hsum := ((hTop m S d).2.1 q hq y' hy (permuteTuple ς φ)).1.2.2 s
  calc tubeUnionFunction S φ (imagBoostTuple s z)
      = orderedFrameKernel S υ ς (imagBoostTuple s z) φ := hK
    _ = planeKernel S (permuteTuple ς φ) (unrotate υ
          (complexDifferences (permuteTuple ς (imagBoostTuple s z)))) :=
        orderedFrameKernel_eq _ _ _ _ _
    _ = planeKernel S (permuteTuple ς φ)
          (complexBoostTuple (I * (s : ℂ)) (planeTupleDiffs y')) := by
        rw [hcomm]
    _ = angleFunction S d.angle y' (permuteTuple ς φ) (I * (s : ℂ)) := hA.symm
    _ = _ := hsum
def sampleCombination {p : ℕ} (W : ℤ → Fin p → ℂ) (S : ConnFamily) {q : ℕ}
    (φ : Fin (q + 1) → realLabels) (h : ℤ) (z : Fin (q + 1) → ℂ × ℂ) : ℂ :=
  ∑ j : Fin p, W h j * tubeUnionFunction S φ (imagBoostTuple ((j : ℕ) : ℝ) z)
theorem sampleCombination_eq_of_expansion {F : Finset ℤ} {p : ℕ} {W : ℤ → Fin p → ℂ}
    (hW : IsSampleInversion F W) (S : ConnFamily) {q : ℕ} (φ : Fin (q + 1) → realLabels)
    (z : Fin (q + 1) → ℂ × ℂ) (b : ℤ → ℂ)
    (hb : ∀ s : ℝ, tubeUnionFunction S φ (imagBoostTuple s z) =
      ∑ k ∈ F, b k * Complex.exp (-(4 * (k : ℂ) * (s : ℂ)))) {h : ℤ} (hh : h ∈ F) :
    sampleCombination W S φ h z = b h := by
  unfold sampleCombination
  rw [← hW b h hh]
  exact Finset.sum_congr rfl fun j _ => by rw [hb]
theorem differentiableOn_boostedFunction
    (hOne : UnionKernel.Holds)
    (hP : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {m : SharpScale} {S : ConnFamily} (d : PlaneDataWithAperture m S) {q : ℕ} (hq : 1 ≤ q)
    (φ : Fin (q + 1) → realLabels) (s : ℝ) :
    DifferentiableOn ℂ (fun z => tubeUnionFunction S φ (imagBoostTuple s z))
      (orderedTubeUnion q) := by
  have hone := hOne m S d q hq φ rightAngleZero rightAngleZero 1 1
  have hKd : DifferentiableOn ℂ (tubeUnionFunction S φ)
      (orderedTubeUnion q) :=
    differentiableOn_of_holomorphicOnTuples hP hone.2.2.2.2.2.1.2.2.2.1
  have himg := hone.2.2.2.2.2.2.1.2.2.1 s
  refine hKd.comp (differentiable_imagBoostTuple s).differentiableOn ?_
  intro z hz
  rw [← himg]
  exact Set.mem_image_of_mem _ hz
theorem differentiableOn_sampleCombination
    (hOne : UnionKernel.Holds)
    (hP : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {m : SharpScale} {S : ConnFamily} (d : PlaneDataWithAperture m S) {q : ℕ} (hq : 1 ≤ q)
    {p : ℕ} (W : ℤ → Fin p → ℂ) (φ : Fin (q + 1) → realLabels) (h : ℤ) :
    DifferentiableOn ℂ (sampleCombination W S φ h) (orderedTubeUnion q) := by
  unfold sampleCombination
  refine DifferentiableOn.fun_sum fun j _ => ?_
  exact (differentiableOn_boostedFunction hOne hP d hq φ _).const_mul _
theorem hasHarmonicExpansion_sampleCombination
    (hOne : UnionKernel.Holds)
    (hAngle : AngleFunctionOnPencil.Holds)
    (hTop : MaxFrequencyFacts.Holds)
    (hR : RotationRules.Holds)
    (hZ : Analysis.ZerosOfAnalyticMapsAndThinSets)
    (hP : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {m : SharpScale} {S : ConnFamily} (d : PlaneDataWithAperture m S) {q : ℕ} (hq : 1 ≤ q)
    {p : ℕ} {W : ℤ → Fin p → ℂ}
    (hW : IsSampleInversion (Finset.Icc (-(maxFrequency S d.angle (q + 1) : ℤ))
      (maxFrequency S d.angle (q + 1) : ℤ)) W)
    (φ : Fin (q + 1) → realLabels) :
    HasHarmonicExpansion S d.angle φ (sampleCombination W S φ) := by
  intro z hz s
  obtain ⟨υ, hz⟩ := Set.mem_iUnion.mp hz
  obtain ⟨ς, hz⟩ := Set.mem_iUnion.mp hz
  have hone := hOne m S d q hq φ υ υ ς ς
  obtain ⟨hopen, hconv, -, hstab⟩ := hone.2.1
  have hsub : orderedTube υ ς ⊆ orderedTubeUnion q :=
    fun w hw => Set.mem_iUnion.mpr ⟨υ, Set.mem_iUnion.mpr ⟨ς, hw⟩⟩
  have hg : DifferentiableOn ℂ (fun w => tubeUnionFunction S φ
      (imagBoostTuple s w) -
      ∑ h ∈ Finset.Icc (-(maxFrequency S d.angle (q + 1) : ℤ))
          (maxFrequency S d.angle (q + 1) : ℤ),
        sampleCombination W S φ h w * Complex.exp (-(4 * (h : ℂ) * (s : ℂ))))
      (orderedTube υ ς) := by
    refine ((differentiableOn_boostedFunction hOne hP d hq φ s).mono hsub).sub ?_
    refine DifferentiableOn.fun_sum fun h _ => ?_
    exact ((differentiableOn_sampleCombination hOne hP d hq W φ h).mono hsub).mul_const _
  have hpen := (hR.2.2.2.2.2 d.angle).2.2.2.2 q hq
  have hvan := eqOn_zero_of_eqOn_zero_real hZ (by omega) hopen hconv
    (fun w hw => (hstab w hw).2.2) hg
    (A := unturnPermute υ ς ⁻¹' pencilSet d.angle (q + 1))
    (hpen.1.preimage (continuous_unturnPermute υ ς))
    ⟨fun i => RealPlane.rotate (υ : ℝ) ((fun l : Fin (q + 1) => (((l : ℕ) : ℝ) + 1) • unitX)
        (ς⁻¹ i)), by
      have heq : unturnPermute υ ς (fun i => RealPlane.rotate (υ : ℝ)
          ((fun l : Fin (q + 1) => (((l : ℕ) : ℝ) + 1) • unitX) (ς⁻¹ i))) =
          fun l : Fin (q + 1) => (((l : ℕ) : ℝ) + 1) • unitX := by
        funext i
        simp [unturnPermute, rotate_neg_rotate]
      rw [Set.mem_preimage, heq]
      exact hpen.2⟩
    (fun y hy => (expansion_on_turned_pencil hOne hAngle hTop hR d hq φ υ ς hy).1)
    (fun y hy => by
      have hexp := (expansion_on_turned_pencil hOne hAngle hTop hR d hq φ υ ς hy).2
      rw [hexp s, sub_eq_zero]
      refine Finset.sum_congr rfl fun h hh => ?_
      rw [sampleCombination_eq_of_expansion hW S φ _ _ hexp hh])
    z hz
  exact sub_eq_zero.mp hvan
theorem imagBoostTuple_add
    (hR : RotationRules.Holds) {n : ℕ} (s s' : ℝ)
    (z : Fin n → ℂ × ℂ) :
    imagBoostTuple s' (imagBoostTuple s z) =
      imagBoostTuple (s + s') z := by
  obtain ⟨-, -, -, -, -, hgrp, -, -, -, -, -⟩ := hR.1
  funext i
  have h := congr_fun (hgrp (I * (s' : ℂ)) (I * (s : ℂ))).1 (z i)
  have hc : I * (s' : ℂ) + I * (s : ℂ) = I * ((s + s' : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hc] at h
  exact h
theorem imagBoostTuple_zero
    (hR : RotationRules.Holds) {n : ℕ}
    (z : Fin n → ℂ × ℂ) : imagBoostTuple 0 z = z := by
  obtain ⟨-, -, -, h0, -, -, -, -, -, -, -⟩ := hR.1
  funext i
  have hc : I * ((0 : ℝ) : ℂ) = 0 := by simp
  simp only [imagBoostTuple, imagBoost, hc, h0, id]
theorem imagBoostTuple_addConstTuple
    (hR : RotationRules.Holds) {n : ℕ} (s : ℝ)
    (z : Fin n → ℂ × ℂ) (u : ℂ × ℂ) :
    imagBoostTuple s (addConstTuple z u) =
      addConstTuple (imagBoostTuple s z) (imagBoost s u) := by
  obtain ⟨-, -, -, -, hlin, -, -, -, -, -, -⟩ := hR.1
  funext i
  exact (hlin (I * (s : ℂ))).1.map_add (z i) u
theorem unturnPermute_zero_one {n : ℕ} (y : Fin n → RealPlane) :
    unturnPermute rightAngleZero 1 y = y := by
  funext i
  show RealPlane.rotate (-(0 : ℝ)) (y i) = y i
  ext j
  fin_cases j <;> simp [RealPlane.rotate]
theorem holds
    (hOne : UnionKernel.Holds)
    (hAngle : AngleFunctionOnPencil.Holds)
    (hTop : MaxFrequencyFacts.Holds)
    (hR : RotationRules.Holds)
    (hZ : Analysis.ZerosOfAnalyticMapsAndThinSets)
    (hP : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties) :
    TubeUnionHarmonics.Holds := by
  intro m S d q hq φ
  set N := maxFrequency S d.angle (q + 1) with hN
  set F := Finset.Icc (-(N : ℤ)) (N : ℤ) with hF
  obtain ⟨W, hW⟩ := exists_sampleInversion F
  have hmemF : ∀ h : ℤ, |h| ≤ (N : ℤ) ↔ h ∈ F := fun h => by
    rw [hF, Finset.mem_Icc, abs_le]
  have hExp : ∀ ψ : Fin (q + 1) → realLabels,
      HasHarmonicExpansion S d.angle ψ (sampleCombination W S ψ) :=
    fun ψ => hasHarmonicExpansion_sampleCombination hOne hAngle hTop hR hZ hP d hq hW ψ
  have hFam : ∀ ψ : Fin (q + 1) → realLabels,
      HasHarmonicExpansion S d.angle ψ (harmonicFamily S d.angle ψ) :=
    fun ψ => Classical.epsilon_spec ⟨_, hExp ψ⟩
  have huniq : ∀ (ψ : Fin (q + 1) → realLabels) (c : ℤ → (Fin (q + 1) → ℂ × ℂ) → ℂ),
      HasHarmonicExpansion S d.angle ψ c → ∀ h ∈ F,
      ∀ z ∈ orderedTubeUnion q, c h z = sampleCombination W S ψ h z :=
    fun ψ c hc h hh z hz =>
      (sampleCombination_eq_of_expansion hW S ψ z (fun k => c k z) (hc z hz) hh).symm
  have hlow : ∀ (ψ : Fin (q + 1) → realLabels) (h : ℤ) (z : Fin (q + 1) → ℂ × ℂ), h ∈ F →
      z ∈ orderedTubeUnion q →
      tubeUnionHarmonic S d.angle ψ h z = sampleCombination W S ψ h z := by
    intro ψ h z hh hz
    unfold tubeUnionHarmonic
    rw [if_pos ((hmemF h).mpr hh)]
    exact huniq ψ _ (hFam ψ) h hh z hz
  have hhigh : ∀ (ψ : Fin (q + 1) → realLabels) (h : ℤ) (z : Fin (q + 1) → ℂ × ℂ), h ∉ F →
      tubeUnionHarmonic S d.angle ψ h z = 0 := by
    intro ψ h z hh
    unfold tubeUnionHarmonic
    rw [if_neg (mt (hmemF h).mp hh)]
  have hone := hOne m S d q hq φ rightAngleZero rightAngleZero 1 1
  have hDopen := hone.2.2.2.2.2.1.2.2.1
  have hinv : ∀ (ς : Equiv.Perm (Fin (q + 1))) (ψ : Fin (q + 1) → realLabels),
      UnionKernel.Invariance S ς ψ :=
    fun ς ψ => (hOne m S d q hq ψ rightAngleZero rightAngleZero ς 1).2.2.2.2.2.2.1
  have hDrot : ∀ (s : ℝ) (z : Fin (q + 1) → ℂ × ℂ), z ∈ orderedTubeUnion q →
      imagBoostTuple s z ∈ orderedTubeUnion q := by
    intro s z hz
    rw [← (hinv 1 φ).2.2.1 s]
    exact Set.mem_image_of_mem _ hz
  refine ⟨⟨hFam φ, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro c hc h hh z hz
    have hh' := (hmemF h).mp hh
    rw [huniq φ c hc h hh' z hz, huniq φ _ (hFam φ) h hh' z hz]
  · intro h hh
    exact holomorphicOnTuples_of_differentiableOn hDopen
      ((differentiableOn_sampleCombination hOne hP d hq W φ h).congr
        fun z hz => huniq φ _ (hFam φ) h ((hmemF h).mp hh) z hz)
  · intro y hy h
    by_cases hh : h ∈ F
    · obtain ⟨hmem, hexp⟩ := expansion_on_turned_pencil hOne hAngle hTop hR d hq φ rightAngleZero 1
        (y := y) (by rw [unturnPermute_zero_one]; exact hy)
      rw [unturnPermute_zero_one] at hexp
      have hz : embedPlaneTuple y ∈ orderedTubeUnion q :=
        Set.mem_iUnion.mpr ⟨rightAngleZero, Set.mem_iUnion.mpr ⟨1, hmem⟩⟩
      rw [hlow φ h _ hh hz]
      exact sampleCombination_eq_of_expansion hW S φ _ (angleHarmonic S d.angle y φ) hexp hh
    · rw [hhigh φ h _ hh]
      symm
      refine ((hTop m S d).2.1 q hq y hy φ).1.1 h ?_
      rw [hF, Finset.mem_Icc] at hh
      omega
  · intro h z hz
    refine ⟨fun ς => ?_, fun u => ?_, fun s => ?_, ?_⟩
    · by_cases hh : h ∈ F
      · have hzς : permuteTuple ς z ∈ orderedTubeUnion q := by
          rw [← (hinv ς φ).1]
          exact Set.mem_image_of_mem _ hz
        rw [hlow _ h _ hh hzς, hlow φ h z hh hz]
        unfold sampleCombination
        refine Finset.sum_congr rfl fun j _ => ?_
        congr 1
        exact ((hinv ς φ).2.2.2 _ (hDrot _ z hz)).1
      · rw [hhigh _ h _ hh, hhigh _ h _ hh]
    · by_cases hh : h ∈ F
      · have hzu : addConstTuple z u ∈ orderedTubeUnion q := by
          rw [← (hinv 1 φ).2.1 u]
          exact Set.mem_image_of_mem _ hz
        rw [hlow _ h _ hh hzu, hlow φ h z hh hz]
        unfold sampleCombination
        refine Finset.sum_congr rfl fun j _ => ?_
        congr 1
        rw [imagBoostTuple_addConstTuple hR]
        exact ((hinv 1 φ).2.2.2 _ (hDrot _ z hz)).2 _
      · rw [hhigh _ h _ hh, hhigh _ h _ hh]
    · by_cases hh : h ∈ F
      · rw [hlow φ h _ hh (hDrot s z hz), hlow φ h z hh hz]
        have hc := sampleCombination_eq_of_expansion hW S φ (imagBoostTuple s z)
          (fun k => sampleCombination W S φ k z * Complex.exp (-(4 * (k : ℂ) * (s : ℂ))))
          (fun s' => by
            rw [imagBoostTuple_add hR, hExp φ z hz (s + s')]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [mul_assoc (sampleCombination W S φ k z), ← Complex.exp_add]
            congr 2
            push_cast
            ring) hh
        rw [hc, mul_comm]
      · rw [hhigh _ h _ hh, hhigh _ h _ hh, mul_zero]
    · intro ψ j a a' χ χ'
      beta_reduce
      by_cases hh : h ∈ F
      · rw [hlow _ h z hh hz, hlow _ h z hh hz, hlow _ h z hh hz]
        unfold sampleCombination
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun l _ => ?_
        have hm := (hOne m S d q hq ψ rightAngleZero rightAngleZero 1 1).2.2.2.2.2.1.2.2.2.2 _
          (hDrot ((l : ℕ) : ℝ) z hz) ψ j a a' χ χ'
        beta_reduce at hm
        show W h l * unionKernel S _ _ =
          a * (W h l * unionKernel S _ _) +
            a' * (W h l * unionKernel S _ _)
        rw [hm]
        ring
      · rw [hhigh _ h _ hh, hhigh _ h _ hh, hhigh _ h _ hh]
        simp
  · intro z hz
    have h0 := hExp φ z hz 0
    rw [imagBoostTuple_zero hR] at h0
    rw [h0]
    refine Finset.sum_congr rfl fun h hh => ?_
    rw [hlow φ h z hh hz]
    simp
end YangMills.Construction.EuclideanFunctionals.TubeUnionHarmonicsProof
end
