import YangMills.Construction.InfiniteLattice.PeriodLatticesToriAndTheirWilsonMeasures
import YangMills.Construction.Towers.ChainOfTheComplexIteratesAtTheSideInfinity
import YangMills.Construction.Towers.ChainRuleAtTheSideInfinityInTheLeftChart
import YangMills.Construction.Towers.ConfigurationsFormedLevelByLevelOnThePolydiscs
import YangMills.Construction.Towers.ConfigurationsUnderTheLeftChart
import YangMills.Construction.Towers.LinearityOfTheCovariantStepAtTheSideInfinity
import YangMills.Construction.Towers.OneValueForEveryWriting
import YangMills.Construction.Towers.SumOverFinitelyManyPlaquettesProof
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace
namespace IterChain
open YangMills.Construction.Tower.MeanStableFields.Infinite (meanStableFields levelwiseMeanAt)
theorem opposite_isPositivelyOriented_of_not {a : ℝ} {b : InfiniteLattice.Link a}
    (hb : ¬ b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodSublattice.isPositivelyOriented_opposite_of_not <;> assumption
section Evaluation
open YangMills.Construction.Matrices.GroupLieProduct
def coordIndexEquiv {ρ : Type} {n : ℕ} (ν : ρ ≃ Fin n) :
    Fin (Coordinates.ComplexCoordinates.productDim
      fun _ : Fin n => Coordinates.ComplexCoordinates.Component.matrix) ≃ ρ × Fin 4 :=
  (finSigmaFinEquiv (m := n) (n := fun _ => 4)).symm.trans
    ((Equiv.sigmaEquivProd (Fin n) (Fin 4)).trans (Equiv.prodCongr ν.symm (Equiv.refl _)))
theorem matrixPiEquiv_apply_eq {ρ : Type} {n : ℕ} (ν : ρ ≃ Fin n)
    (X : ρ → Matrices.ComplexMatrix2)
    (i : Fin (Coordinates.ComplexCoordinates.productDim
      fun _ : Fin n => Coordinates.ComplexCoordinates.Component.matrix)) :
    matrixPiEquiv ν X i =
      Coordinates.ComplexCoordinates.matrixEquiv (X (coordIndexEquiv ν i).1)
        (coordIndexEquiv ν i).2 :=
  rfl
theorem eval_isHolomorphicVia {ρ : Type} {n : ℕ} (ν : ρ ≃ Fin n) (s : ρ) :
    Coordinates.ComplexCoordinates.IsHolomorphicVia (matrixPiEquiv ν)
      Coordinates.ComplexCoordinates.matrixEquiv univ fun p => p s := by
  let J : Fin 4 →
      Fin (Coordinates.ComplexCoordinates.productDim
        fun _ : Fin n => Coordinates.ComplexCoordinates.Component.matrix) :=
    fun i => (coordIndexEquiv ν).symm (s, i)
  have hJ : ∀ (x : ρ → Matrices.ComplexMatrix2) i,
      Coordinates.ComplexCoordinates.matrixEquiv (x s) i = matrixPiEquiv ν x (J i) := by
    intro x i
    rw [matrixPiEquiv_apply_eq]
    simp only [J, Equiv.apply_symm_apply]
  have hf : (Coordinates.ComplexCoordinates.matrixEquiv ∘
      (fun p : ρ → Matrices.ComplexMatrix2 => p s) ∘
      (matrixPiEquiv ν).symm) = fun z i => z (J i) := by
    funext z i
    simp only [Function.comp]
    rw [hJ, Equiv.apply_symm_apply]
  unfold Coordinates.ComplexCoordinates.IsHolomorphicVia
  rw [hf]
  refine ⟨?_, (continuous_pi fun i => continuous_apply _).continuousOn, fun a _ i =>
    Eventually.of_forall fun ζ => differentiableAt_pi.2 fun i' => ?_⟩
  · rw [image_univ, Equiv.range_eq_univ]
    exact isOpen_univ
  · show DifferentiableAt ℂ
      (fun ζ : ℂ => a (J i') + ζ * Coordinates.ComplexCoordinates.stdBasisVector i (J i')) ζ
    fun_prop
theorem image_asGroupFactors_unimodularPi {σ : Type} :
    asGroupFactors '' unimodularPi σ = Matrices.GroupLieProduct σ Empty := by apply _root_.YangMills.Construction.Tower.FaceSum.image_unimodularPi <;> assumption
theorem eval_isHolomorphicToCoords
    (hX : Matrices.GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless) {σ : Type} [Fintype σ]
    (s : σ) :
    IsHolomorphicToCoords β Coordinates.ComplexCoordinates.matrixEquiv
      (asGroupFactors '' unimodularPi σ) fun p => p (.inl s) := by
  have hT : Coordinates.ComplexCoordinates.IsHolomorphicVia
      (matrixPiEquiv (Fintype.equivFin (σ ⊕ Empty)))
      Coordinates.ComplexCoordinates.matrixEquiv univ
      fun p : σ ⊕ Empty → Matrices.ComplexMatrix2 => p (Sum.inl s) :=
    eval_isHolomorphicVia (Fintype.equivFin (σ ⊕ Empty)) (Sum.inl s)
  have hR : Matrices.GroupLieProduct.ExpChartHolomorphy.ProductRestrictionHolomorphy σ Empty :=
    (hX.2.2.2.1 σ Empty).2.2
  have h' := (hR Matrices.ComplexMatrix2 4 (Fintype.card (σ ⊕ Empty))
    Coordinates.ComplexCoordinates.matrixEquiv
    (Fintype.equivFin (σ ⊕ Empty)) univ (fun p => p (Sum.inl s)) hT).2 β
  rwa [univ_inter, ← image_asGroupFactors_unimodularPi] at h'
end Evaluation
variable {L k : ℕ}
theorem isMeanSequence_of_mem_smallIterateFields
    (hO : IteratedMeans.Unbounded.SpaceConditions L k)
    {U : Edge L k 0 → Matrices.ComplexMatrix2} (hU : U ∈ smallIterateFields L k) :
    LevelwiseMeans.Unbounded.IsMeanSequence k (fun i => complexIter L k i U) where
  mem_fields := by
    intro i hi
    cases i with
    | zero => exact hU.1
    | succ i => exact hO.meanStep_mem i hi _ (hU.2 i hi)
  norm_sub_one_lt := fun i hi b => (hU.2 i hi).2 b
  eq_mean := fun _ _ _ _ => rfl
theorem smallIterateFields_subset_meanStableFields
    (hO : IteratedMeans.Unbounded.SpaceConditions L k) :
    smallIterateFields L k ⊆ meanStableFields L k k :=
  fun U hU => ⟨fun i => complexIter L k i U, isMeanSequence_of_mem_smallIterateFields hO hU, rfl⟩
theorem eq_complexIter_of_isMeanSequence {W : Edge L k 0 → Matrices.ComplexMatrix2}
    {V : ∀ i : ℕ, Edge L k i → Matrices.ComplexMatrix2} {l : ℕ}
    (hV : LevelwiseMeans.Unbounded.IsMeanSequence l V) (h0 : V 0 = W) :
    ∀ i ≤ l, V i = complexIter L k i W
  | 0, _ => h0
  | i + 1, hi => by
    have ih := eq_complexIter_of_isMeanSequence hV h0 i (by omega)
    funext c
    show V (i + 1) c = complexSmoothing L (complexIter L k i W) c
    rw [← ih]
    by_cases hc : c.IsPositivelyOriented
    · exact hV.eq_mean i hi c hc
    · have hr := opposite_isPositivelyOriented_of_not hc
      have h1 : V (i + 1) c = (V (i + 1) c.opposite)⁻¹ := (hV.mem_fields (i + 1) hi).2 c.opposite
      rw [h1, hV.eq_mean i hi c.opposite hr]
      simp [complexSmoothing, hc, hr]
theorem meanStableFields_subset_smallIterateFields :
    meanStableFields L k k ⊆ smallIterateFields L k := by
  rintro W ⟨V, hV, h0⟩
  refine ⟨h0 ▸ hV.mem_fields 0 (Nat.zero_le _), fun j hj => ?_⟩
  rw [← eq_complexIter_of_isMeanSequence hV h0 j hj.le]
  exact ⟨hV.mem_fields j hj.le, hV.norm_sub_one_lt j hj⟩
theorem levelwiseMeanAt_eq_complexIter
    (hP : MeanStableFields.Infinite.MeanStableConditions L k)
    (hO : IteratedMeans.Unbounded.SpaceConditions L k)
    {U : Edge L k 0 → Matrices.ComplexMatrix2} (hU : U ∈ smallIterateFields L k) {i : ℕ}
    (hi : i ≤ k) (c : Edge L k i) : levelwiseMeanAt i c U = complexIter L k i U c := by
  have h := hP.eq_levelwiseMean k le_rfl U _
    ⟨isMeanSequence_of_mem_smallIterateFields hO hU, rfl⟩ i hi c
  unfold levelwiseMeanAt LevelwiseMeans.valuesOrOne
  rw [h]
  rfl
theorem isFinitelyHolomorphic_congr {j : ℕ}
    {β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless}
    {𝔇 : Set (Edge L k j → Matrices.ComplexMatrix2)}
    {h h' : (Edge L k j → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2}
    (hh : ∀ U ∈ 𝔇, h U = h' U)
    (H : IsFinitelyHolomorphic β Coordinates.ComplexCoordinates.matrixEquiv 𝔇 h) :
    IsFinitelyHolomorphic β Coordinates.ComplexCoordinates.matrixEquiv 𝔇 h' := by
  refine ⟨H.1, fun U hU => ?_⟩
  obtain ⟨F, O, f, hw, hf⟩ := H.2 U hU
  exact ⟨F, O, f, ⟨hw.1, hw.2.1, hw.2.2.1, fun U' hU' ho =>
    (hh U' hU').symm.trans (hw.2.2.2 U' hU' ho)⟩, hf⟩
theorem isHolomorphicFieldMap_complexIter
    (hP : MeanStableFields.Infinite.MeanStableConditions L k)
    (hO : IteratedMeans.Unbounded.SpaceConditions L k)
    (β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless) {j : ℕ}
    (hj : j ≤ k) : IsHolomorphicFieldMap β (smallIterateFields L k) (complexIter L k j) := by
  have hs : smallIterateFields L k = meanStableFields L k k :=
    (smallIterateFields_subset_meanStableFields hO).antisymm
      meanStableFields_subset_smallIterateFields
  refine ⟨hs ▸ hP.isFinitelyOpen,
    fun U hU => (isMeanSequence_of_mem_smallIterateFields hO hU).mem_fields j hj,
    fun c hc => ?_⟩
  have H := hP.holomorphic_mean j hj c hc β
  rw [← hs] at H
  exact isFinitelyHolomorphic_congr (fun U hU => levelwiseMeanAt_eq_complexIter hP hO hU hj c) H
theorem isHolomorphicFieldMap_smoothingMap
    (hP : MeanStableFields.Infinite.MeanStableConditions L k)
    (hO : IteratedMeans.Unbounded.SpaceConditions L k)
    (β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless) {j : ℕ} (hj : j < k) :
    IsHolomorphicFieldMap β (smallComplexFields L k j) (smoothingMap L k j) :=
  ⟨hP.isFinitelyOpen_nearOne j hj, fun V hV => hO.meanStep_mem j hj V hV,
    fun c hc => hP.holomorphic_smoothing j hj c hc β⟩
theorem complexIterDeriv_succ (hC : FullSpaceChainRule.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hP : MeanStableFields.Infinite.MeanStableConditions L k)
    (hO : IteratedMeans.Unbounded.SpaceConditions L k)
    {U B : Edge L k 0 → Matrices.ComplexMatrix2}
    (hU : U ∈ smallIterateFields L k) (hB : B ∈ complexEdgeForms (meshAt L k 0))
    {j : ℕ} (hj : j < k) :
    complexIterDeriv L k (j + 1) U B =
      complexSmoothingDeriv (complexIter L k j U) (complexIterDeriv L k j U B) := by
  have hdom : compositeDomain (smallIterateFields L k)
      (smallComplexFields L k j) (complexIter L k j) = smallIterateFields L k := by
    ext W
    exact ⟨fun h => h.1, fun h => ⟨h, h.2 j hj⟩⟩
  have hF := isHolomorphicFieldMap_complexIter hP hO OneLoop.pauliBasis hj.le
  have hM := isHolomorphicFieldMap_smoothingMap hP hO OneLoop.pauliBasis hj
  have h := (hC L k 0 j (j + 1) hL (Nat.zero_le _) hj.le hj).2 OneLoop.pauliBasis _ _ _ _
    hF hM (by rw [hdom]; exact hF.1)
  have h2 := h.2 U (by rw [hdom]; exact hU) B hB
  rw [hdom] at h2
  exact h2
theorem complexIterDeriv_zero
    (hX : Matrices.GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (hA : LeftChartFields.Claim) (hV : UniqueValue.PresentationsAgreeAndBallsOpen)
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hopen : IsFinitelyOpen PeriodicLattice.complexGaugeGroup (smallIterateFields L k))
    {U B : Edge L k 0 → Matrices.ComplexMatrix2} (hU : U ∈ smallIterateFields L k)
    (hB : B ∈ complexEdgeForms (meshAt L k 0)) :
    complexIterDeriv L k 0 U B = B := by
  have key : ∀ c : Edge L k 0, c.IsPositivelyOriented → logDirectionalDeriv ℂ
      (valueViaPresentation PeriodicLattice.complexGaugeGroup (smallIterateFields L k)
        (holomorphicPresentations L k 0 OneLoop.pauliBasis
          Coordinates.ComplexCoordinates.matrixEquiv)
        (fun U' => complexIter L k 0 U' c) U) (complexIter L k 0 U c) B = B c := by
    intro c hc
    classical
    let F₂ : Finset (Edge L k 0) := {c}
    let s : F₂ := ⟨c, Finset.mem_singleton_self c⟩
    let O₂ : Set (F₂ → Matrices.ComplexMatrix2) := edgeProduct PeriodicLattice.complexGaugeGroup F₂
    let f₂ : (F₂ → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2 := fun w => w s
    have hw₂ : IsLocalPresentation PeriodicLattice.complexGaugeGroup (smallIterateFields L k)
        (fun U' => complexIter L k 0 U' c) U F₂ O₂ f₂ := by
      refine ⟨⟨Finset.singleton_nonempty c, ?_⟩, ⟨univ, isOpen_univ, (univ_inter _).symm⟩,
        fun b => hU.1.1 b.1, ?_⟩
      · intro b hb
        rw [Finset.mem_singleton.1 hb]
        exact hc
      · intro U' _ _
        rfl
    have hk₂ : holomorphicPresentations L k 0 OneLoop.pauliBasis
        Coordinates.ComplexCoordinates.matrixEquiv F₂ O₂ f₂ :=
      eval_isHolomorphicToCoords hX OneLoop.pauliBasis s
    have hch := Classical.epsilon_spec
      (p := fun w : LocalData L k 0 Matrices.ComplexMatrix2 =>
        IsLocalPresentation PeriodicLattice.complexGaugeGroup (smallIterateFields L k)
          (fun U' => complexIter L k 0 U' c) U w.support w.region w.fn ∧
        holomorphicPresentations L k 0 OneLoop.pauliBasis
          Coordinates.ComplexCoordinates.matrixEquiv w.support w.region w.fn)
      ⟨⟨F₂, O₂, f₂⟩, hw₂, hk₂⟩
    obtain ⟨ε, hε, hval⟩ := (hV L k 0 hL.1 hL.2 (Nat.zero_le k)).1.2.2.2 _ hopen
      (fun U' => complexIter L k 0 U' c) U hU _ _ _ F₂ O₂ f₂ hch.1 hw₂ B 0
      (fun b hb => hB.1 b hb) (fun _ _ => (Matrices.ComplexMatrix2.traceless).zero_mem)
    have hmove : ∀ (F : Finset (Edge L k 0)) (t : ℂ),
        UniqueValue.perturbedTuple F B 0 U (algebraMap ℂ ℂ t) (algebraMap ℂ ℂ 0) =
          fun b : F => Matrices.ComplexMatrix2.matExp
            (Complex.I • (algebraMap ℂ ℂ t • B) b) * U b := by
      intro F t
      funext b
      simp [UniqueValue.perturbedTuple]
    have hev : ∀ᶠ t in 𝓝 (0 : ℂ), valueViaPresentation PeriodicLattice.complexGaugeGroup
        (smallIterateFields L k)
        (holomorphicPresentations L k 0 OneLoop.pauliBasis
          Coordinates.ComplexCoordinates.matrixEquiv)
        (fun U' => complexIter L k 0 U' c) U (algebraMap ℂ ℂ t • B) =
        Matrices.ComplexMatrix2.matExp (Complex.I • (t • B c)) * U c := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hε] with t ht
      have h := (hval t 0 (by simpa using ht) (by simpa using hε)).2.2
      rw [hmove, hmove] at h
      exact h
    have hclause := (hA.2.2 L k 0 hL (Nat.zero_le k)).2.1.1.2 U hU.1 B hB ⟨c, hc⟩
    have hlog := (hA.2.1 1 one_pos)
      (fun t : ℂ => LeftChartFields.leftExpMul (t • B c) (U c))
      (fun t _ => hclause.1 t) hclause.2.differentiableAt
    have hW0 : LeftChartFields.leftExpMul ((0 : ℂ) • B c) (U c) = U c := by
      simp [LeftChartFields.leftExpMul, Matrices.ComplexMatrix2.matExp]
    have hcongr : (fun t : ℂ => Matrices.ComplexMatrix2.logSeries
        (valueViaPresentation PeriodicLattice.complexGaugeGroup
        (smallIterateFields L k)
        (holomorphicPresentations L k 0 OneLoop.pauliBasis
          Coordinates.ComplexCoordinates.matrixEquiv)
        (fun U' => complexIter L k 0 U' c) U (algebraMap ℂ ℂ t • B) * (U c)⁻¹)) =ᶠ[𝓝 0]
        fun t => Matrices.ComplexMatrix2.logSeries (LeftChartFields.leftExpMul (t • B c) (U c) *
          (LeftChartFields.leftExpMul ((0 : ℂ) • B c) (U c))⁻¹) := by
      filter_upwards [hev] with t ht
      rw [ht, hW0]
      rfl
    have hdet : IsUnit (U c).det := by
      have h1 : (U c).det = 1 := hU.1.1 c
      rw [h1]
      exact isUnit_one
    have hd : HasDerivAt (fun t : ℂ => LeftChartFields.leftExpMul (t • B c) (U c))
        (Complex.I • B c * U c) 0 := hclause.2
    have hlog3 := hlog.2.2.1
    rw [hd.deriv] at hlog3
    show Complex.I⁻¹ • deriv (fun t : ℂ => Matrices.ComplexMatrix2.logSeries
        (valueViaPresentation PeriodicLattice.complexGaugeGroup
        (smallIterateFields L k)
        (holomorphicPresentations L k 0 OneLoop.pauliBasis
          Coordinates.ComplexCoordinates.matrixEquiv)
        (fun U' => complexIter L k 0 U' c) U (algebraMap ℂ ℂ t • B) * (U c)⁻¹)) 0 = B c
    rw [hcongr.deriv_eq, hlog3, hW0]
    show Complex.I⁻¹ • ((Complex.I • B c * U c) * (U c)⁻¹) = B c
    rw [mul_assoc, Matrix.mul_nonsing_inv _ hdet, mul_one, smul_smul,
      inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
  funext b
  unfold complexIterDeriv holLeftDifferential
  by_cases hb : b.IsPositivelyOriented
  · simp only [extendOddly, hb, if_true]
    exact key b hb
  · have hr := opposite_isPositivelyOriented_of_not hb
    simp only [extendOddly, hb, if_false]
    rw [key _ hr, hB.2 b, neg_neg]
end IterChain
open IterChain in
theorem complexIterChain_holds
    (hC : FullSpaceChainRule.Statement)
    (hPP : MeanStableFields.MeanStableFieldsHold)
    (hOO : IteratedMeans.IteratedMeansHold)
    (hV : UniqueValue.PresentationsAgreeAndBallsOpen)
    (hA : LeftChartFields.Claim)
    (hX : Matrices.GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (hS : CovariantStepComplexLinear) :
    ComplexIterChain := by
  intro L hL k U hU B hB
  have hopen : IsFinitelyOpen PeriodicLattice.complexGaugeGroup
      (smallIterateFields L k) := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have h := ((hV L 0 0 hL.1 hL.2 le_rfl).2.2 1 one_pos).1
      have e : smallIterateFields L 0 =
          fieldsValuedIn L 0 0 PeriodicLattice.complexGaugeGroup := by
        ext W
        simp [smallIterateFields]
      rw [e]
      exact h
    · exact (isHolomorphicFieldMap_complexIter (hPP L hL k hk).2 (hOO L hL k hk).2
        OneLoop.pauliBasis (Nat.zero_le k)).1
  have h0 := complexIterDeriv_zero hX hA hV hL hopen hU hB
  have hstep : ∀ j < k, complexIterDeriv L k (j + 1) U B =
      complexSmoothingDeriv (complexIter L k j U)
        (complexIterDeriv L k j U B) := fun j hj =>
    complexIterDeriv_succ hC hL (hPP L hL k (by omega)).2 (hOO L hL k (by omega)).2 hU hB hj
  refine ⟨h0, hstep, ?_⟩
  intro j
  induction j with
  | zero =>
    intro _
    rw [h0]
    exact hB
  | succ j ih =>
    intro hj
    rw [hstep j hj]
    exact ((hS L hL k j hj _ (hU.2 j hj)).1 _ (ih (by omega))).1
end YangMills.Construction.Tower.FullSpace
end
