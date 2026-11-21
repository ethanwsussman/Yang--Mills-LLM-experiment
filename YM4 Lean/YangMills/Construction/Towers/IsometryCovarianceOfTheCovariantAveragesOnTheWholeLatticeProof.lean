import YangMills.Construction.Towers.AveragingCommutesWithIsometriesAtTheSideInfinityProof
import YangMills.Construction.Towers.ChainRuleAtTheSideInfinityInTheLeftChart
import YangMills.Construction.Towers.ComplexAveragesCommuteWithIsometriesOnThePolydiscs
import YangMills.Construction.Towers.GaugeCovarianceOfTheCovariantAveragesAtTheSideInfinityProof
import YangMills.Construction.Towers.IsometriesInTheLeftChart
import YangMills.Construction.Towers.IsometriesOfATowerAreHypercubicMotions
import YangMills.Construction.Towers.IsometryCovarianceOfTheCovariantAveragesOnTheWholeLattice
import YangMills.Construction.Towers.LinearityOfTheCovariantStepAtTheSideInfinity
import YangMills.Construction.Towers.OneValueForEveryWriting
import YangMills.Construction.Towers.SumOverFinitelyManyPlaquettesProof
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace
namespace IsometryEquivariance
open YangMills.Construction.Matrices YangMills.Construction.Coordinates
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.Tower.LeftChartFields (leftExpMul)
section Space
variable {a : ℝ} {f : AmbientSpace → AmbientSpace}
theorem coe_vertexImage (hM : MapsSublatticeOnto a f) (x : InfiniteLattice.LatticePoint a) :
    ((vertexImage f x : InfiniteLattice.LatticePoint a) : AmbientSpace) = f x := by apply _root_.YangMills.Construction.Tower.BlockStructureProof.coe_space_vertexImage <;> assumption
theorem apply_vertexPreimage (hM : MapsSublatticeOnto a f) (x : InfiniteLattice.LatticePoint a) :
    f (vertexPreimage f x : InfiniteLattice.LatticePoint a) = x := by apply _root_.YangMills.Construction.Tower.FullSpace.ScalingInvariance.vertexPreimage_spec <;> assumption
theorem vertexImage_vertexPreimage (hM : MapsSublatticeOnto a f)
    (x : InfiniteLattice.LatticePoint a) : vertexImage f (vertexPreimage f x) = x :=
  Subtype.ext ((coe_vertexImage hM _).trans (apply_vertexPreimage hM x))
theorem vertexPreimage_vertexImage (hM : MapsSublatticeOnto a f) (hi : Function.Injective f)
    (x : InfiniteLattice.LatticePoint a) : vertexPreimage f (vertexImage f x) = x :=
  Subtype.ext (hi ((apply_vertexPreimage hM _).trans (coe_vertexImage hM x)))
theorem vertexImage_injective (hM : MapsSublatticeOnto a f) (hi : Function.Injective f) :
    Function.Injective
      (vertexImage f : InfiniteLattice.LatticePoint a → InfiniteLattice.LatticePoint a) := by
  intro x y h
  apply Subtype.ext
  apply hi
  rw [← coe_vertexImage hM x, ← coe_vertexImage hM y, h]
theorem edgeImage_edgePreimage (hM : MapsSublatticeOnto a f) (hB : MapsLinksOnto a f)
    (hi : Function.Injective f) (b : InfiniteLattice.Link a) :
    edgeImage f (edgePreimage f b) = b := by apply _root_.YangMills.Construction.Tower.FullSpace.EquivariantSmoothing.edgeImage_edgePreimage <;> assumption
theorem edgeImage_opposite (hM : MapsSublatticeOnto a f) (hB : MapsLinksOnto a f)
    (b : InfiniteLattice.Link a) : edgeImage f b.opposite = (edgeImage f b).opposite := by apply _root_.YangMills.Construction.Tower.FullSpace.EquivariantSmoothing.edgeImage_opposite <;> assumption
theorem not_positive_opposite (ha : a ≠ 0) {b : InfiniteLattice.Link a}
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.FullSpace.PolydiscSmoothing.not_opposite_isPositivelyOriented <;> assumption
theorem positive_opposite {b : InfiniteLattice.Link a} (hb : ¬ b.IsPositivelyOriented) :
    b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodSublattice.isPositivelyOriented_opposite_of_not <;> assumption
end Space
section Forms
variable {a : ℝ} {f : AmbientSpace → AmbientSpace}
theorem extendOddly_of_positive (g : InfiniteLattice.Link a → ComplexMatrix2)
    {b : InfiniteLattice.Link a} (hb : b.IsPositivelyOriented) : extendOddly g b = g b := by apply _root_.YangMills.Construction.Tower.FullSpace.Translations.extendOddly_of_pos <;> assumption
theorem extendOddly_of_not_positive (g : InfiniteLattice.Link a → ComplexMatrix2)
    {b : InfiniteLattice.Link a} (hb : ¬ b.IsPositivelyOriented) :
    extendOddly g b = -g b.opposite := by apply _root_.YangMills.Construction.Tower.FullSpace.CovarianceProof.extendOddly_of_not_pos <;> assumption
theorem extendOddly_opposite (ha : a ≠ 0) (g : InfiniteLattice.Link a → ComplexMatrix2)
    (b : InfiniteLattice.Link a) : extendOddly g b.opposite = -extendOddly g b := by
  by_cases hb : b.IsPositivelyOriented
  · rw [extendOddly_of_not_positive g (not_positive_opposite ha hb),
      extendOddly_of_positive g hb]
    rfl
  · rw [extendOddly_of_positive g (positive_opposite hb), extendOddly_of_not_positive g hb,
      neg_neg]
theorem tangentEdgeValue_add (U B B' : InfiniteLattice.Link a → ComplexMatrix2)
    (b : InfiniteLattice.Link a) :
    tangentEdgeValue U (B + B') b = tangentEdgeValue U B b + tangentEdgeValue U B' b := by
  by_cases hb : b.IsPositivelyOriented
  · simp [tangentEdgeValue, hb]
  · simp only [tangentEdgeValue, hb, if_false, ComplexMatrix2.conjugateBy, Pi.add_apply,
      mul_add, add_mul, neg_add]
theorem tangentEdgeValue_smul (U B : InfiniteLattice.Link a → ComplexMatrix2) (t : ℂ)
    (b : InfiniteLattice.Link a) :
    tangentEdgeValue U (t • B) b = t • tangentEdgeValue U B b := by
  by_cases hb : b.IsPositivelyOriented
  · simp [tangentEdgeValue, hb]
  · simp only [tangentEdgeValue, hb, if_false, ComplexMatrix2.conjugateBy, Pi.smul_apply,
      mul_smul_comm, smul_mul_assoc, smul_neg]
theorem isometryOnTangent_add (U B B' : InfiniteLattice.Link a → ComplexMatrix2) :
    isometryOnTangent f U (B + B') = isometryOnTangent f U B + isometryOnTangent f U B' := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp only [isometryOnTangent, Pi.add_apply, extendOddly_of_positive _ hb,
      tangentEdgeValue_add]
  · simp only [isometryOnTangent, Pi.add_apply, extendOddly_of_not_positive _ hb,
      tangentEdgeValue_add, neg_add]
theorem isometryOnTangent_smul (U B : InfiniteLattice.Link a → ComplexMatrix2) (t : ℂ) :
    isometryOnTangent f U (t • B) = t • isometryOnTangent f U B := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp only [isometryOnTangent, Pi.smul_apply, extendOddly_of_positive _ hb,
      tangentEdgeValue_smul]
  · simp only [isometryOnTangent, Pi.smul_apply, extendOddly_of_not_positive _ hb,
      tangentEdgeValue_smul, smul_neg]
theorem conjugateBy_mem_traceless_of_isUnit {V A : ComplexMatrix2} (hV : IsUnit V.det)
    (hA : A ∈ ComplexMatrix2.traceless) : ComplexMatrix2.conjugateBy V A ∈ ComplexMatrix2.traceless := by
  show ComplexMatrix2.fullTrace (V * A * V⁻¹) = 0
  have hA' : ComplexMatrix2.fullTrace A = 0 := hA
  unfold ComplexMatrix2.fullTrace at hA' ⊢
  rw [Matrix.trace_mul_comm, ← mul_assoc, Matrix.nonsing_inv_mul _ hV, one_mul, hA']
theorem isometryOnTangent_mem (ha : a ≠ 0) {U B : InfiniteLattice.Link a → ComplexMatrix2}
    (hU : IsFieldIn PeriodicLattice.complexGaugeGroup U) (hB : B ∈ complexEdgeForms a) :
    isometryOnTangent f U B ∈ complexEdgeForms a := by
  refine ⟨fun b hb => ?_, fun b => extendOddly_opposite ha _ b⟩
  show isometryOnTangent f U B b ∈ ComplexMatrix2.traceless
  unfold isometryOnTangent
  rw [extendOddly_of_positive _ hb]
  unfold tangentEdgeValue
  by_cases hd : (edgePreimage f b).IsPositivelyOriented
  · simp only [hd, if_true]
    exact hB.1 _ hd
  · simp only [hd, if_false]
    have hd' := positive_opposite hd
    have hdet : ((U (edgePreimage f b).opposite)⁻¹).det = 1 := by
      have h1 : (U (edgePreimage f b).opposite).det = 1 := hU.1 _
      rw [Matrix.det_nonsing_inv, h1]
      simp
    refine ComplexMatrix2.traceless.neg_mem (conjugateBy_mem_traceless_of_isUnit ?_ (hB.1 _ hd'))
    rw [hdet]
    exact isUnit_one
end Forms
section EvaluationMaps
open YangMills.Construction.Matrices.GroupLieProduct
def piEntryEquiv {ρ : Type} {n : ℕ} (ν : ρ ≃ Fin n) :
    Fin (ComplexCoordinates.productDim fun _ : Fin n => ComplexCoordinates.Component.matrix) ≃
      ρ × Fin 4 :=
  (finSigmaFinEquiv (m := n) (n := fun _ => 4)).symm.trans
    ((Equiv.sigmaEquivProd (Fin n) (Fin 4)).trans (Equiv.prodCongr ν.symm (Equiv.refl _)))
theorem matrixPiEquiv_apply {ρ : Type} {n : ℕ} (ν : ρ ≃ Fin n) (X : ρ → ComplexMatrix2)
    (i : Fin (ComplexCoordinates.productDim fun _ : Fin n =>
      ComplexCoordinates.Component.matrix)) :
    matrixPiEquiv ν X i =
      ComplexCoordinates.matrixEquiv (X (piEntryEquiv ν i).1) (piEntryEquiv ν i).2 :=
  rfl
theorem entrywise_isHolomorphicVia {ρ : Type} {n : ℕ} (ν : ρ ≃ Fin n) (s : ρ)
    {T : ComplexMatrix2 → ComplexMatrix2} {e : Fin 4 → ℂ} {τ : Fin 4 → Fin 4}
    (hT : ∀ (X : ComplexMatrix2) (i : Fin 4), ComplexCoordinates.matrixEquiv (T X) i =
      e i * ComplexCoordinates.matrixEquiv X (τ i)) :
    ComplexCoordinates.IsHolomorphicVia (matrixPiEquiv ν)
      ComplexCoordinates.matrixEquiv univ fun p => T (p s) := by
  let J : Fin 4 →
      Fin (ComplexCoordinates.productDim fun _ : Fin n => ComplexCoordinates.Component.matrix) :=
    fun i => (piEntryEquiv ν).symm (s, i)
  have hJ : ∀ (x : ρ → ComplexMatrix2) i, ComplexCoordinates.matrixEquiv (x s) i =
      matrixPiEquiv ν x (J i) := by
    intro x i
    rw [matrixPiEquiv_apply]
    simp only [J, Equiv.apply_symm_apply]
  have hf : (ComplexCoordinates.matrixEquiv ∘ (fun p : ρ → ComplexMatrix2 => T (p s)) ∘
      (matrixPiEquiv ν).symm) = fun z i => e i * z (J (τ i)) := by
    funext z i
    simp only [Function.comp]
    rw [hT, hJ, Equiv.apply_symm_apply]
  unfold ComplexCoordinates.IsHolomorphicVia
  rw [hf]
  refine ⟨?_, (continuous_pi fun i => continuous_const.mul (continuous_apply _)).continuousOn,
    fun a _ i => Eventually.of_forall fun ζ => differentiableAt_pi.2 fun i' => ?_⟩
  · rw [image_univ, Equiv.range_eq_univ]
    exact isOpen_univ
  · show DifferentiableAt ℂ
      (fun ζ : ℂ => e i' * (a (J (τ i')) + ζ * ComplexCoordinates.stdBasisVector i (J (τ i')))) ζ
    fun_prop
theorem asGroupFactors_image_unimodularPi {σ : Type} :
    asGroupFactors '' unimodularPi σ = Matrices.GroupLieProduct σ Empty := by apply _root_.YangMills.Construction.Tower.FaceSum.image_unimodularPi <;> assumption
theorem entrywise_isHolomorphicToCoords (hX : ExpChartHolomorphy.ExpChartTheory)
    (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) {σ : Type} [Fintype σ] (s : σ)
    {T : ComplexMatrix2 → ComplexMatrix2} {e : Fin 4 → ℂ} {τ : Fin 4 → Fin 4}
    (hT : ∀ (X : ComplexMatrix2) (i : Fin 4), ComplexCoordinates.matrixEquiv (T X) i =
      e i * ComplexCoordinates.matrixEquiv X (τ i)) :
    IsHolomorphicToCoords β ComplexCoordinates.matrixEquiv
      (asGroupFactors '' unimodularPi σ) fun p => T (p (.inl s)) := by
  have hTh : ComplexCoordinates.IsHolomorphicVia
      (matrixPiEquiv (Fintype.equivFin (σ ⊕ Empty)))
      ComplexCoordinates.matrixEquiv univ
        fun p : σ ⊕ Empty → ComplexMatrix2 => T (p (Sum.inl s)) :=
    entrywise_isHolomorphicVia (Fintype.equivFin (σ ⊕ Empty)) (Sum.inl s) hT
  have hR : ExpChartHolomorphy.ProductRestrictionHolomorphy σ Empty :=
    (hX.2.2.2.1 σ Empty).2.2
  have h' := (hR ComplexMatrix2 4 (Fintype.card (σ ⊕ Empty)) ComplexCoordinates.matrixEquiv
    (Fintype.equivFin (σ ⊕ Empty)) univ (fun p => T (p (Sum.inl s))) hTh).2 β
  rwa [univ_inter, ← asGroupFactors_image_unimodularPi] at h'
theorem adjugate_coords_entrywise :
    ∃ (e : Fin 4 → ℂ) (τ : Fin 4 → Fin 4), ∀ (X : ComplexMatrix2) (i : Fin 4),
      ComplexCoordinates.matrixEquiv (Matrix.adjugate X) i =
        e i * ComplexCoordinates.matrixEquiv X (τ i) := by
  let E := ComplexCoordinates.entryIndex
  refine ⟨fun i => if (E.symm i).1 = (E.symm i).2 then 1 else -1,
    fun i => if (E.symm i).1 = (E.symm i).2 then E ((E.symm i).1.rev, (E.symm i).2.rev) else i,
    fun X i => ?_⟩
  show Matrix.adjugate X (E.symm i).1 (E.symm i).2 = _ * ComplexCoordinates.matrixEquiv X _
  generalize hp : E.symm i = p
  have hi : i = E p := by rw [← hp, Equiv.apply_symm_apply]
  obtain ⟨r, s⟩ := p
  have hcoord : ∀ r' s', ComplexCoordinates.matrixEquiv X (E (r', s')) = X r' s' := by
    intro r' s'
    show X (E.symm (E (r', s'))).1 (E.symm (E (r', s'))).2 = X r' s'
    rw [Equiv.symm_apply_apply]
  subst hi
  fin_cases r <;> fin_cases s <;>
    simp [Matrix.adjugate_fin_two, hcoord, Fin.rev]
theorem adjugate_eq_inv_of_det_eq_one {X : ComplexMatrix2} (h : X.det = 1) :
    Matrix.adjugate X = X⁻¹ := by
  rw [Matrix.inv_def, h]
  simp
end EvaluationMaps
section ImageMap
variable {L k l : ℕ} {f : AmbientSpace → AmbientSpace}
theorem exists_presentation_eval
    (hX : Matrices.GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (hA : LeftChartFields.Claim) (hL : Conventions.IsAdmissibleBlockingFactor L) (hl : l ≤ k)
    (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) {𝔇 : Set (Edge L k l → ComplexMatrix2)}
    (h𝔇 : 𝔇 ⊆ fieldsValuedIn L k l PeriodicLattice.complexGaugeGroup)
    {U : Edge L k l → ComplexMatrix2} (hU : U ∈ 𝔇) (d : Edge L k l) :
    ∃ (F : Finset (Edge L k l)) (O : Set (F → ComplexMatrix2)) (g : (F → ComplexMatrix2) → ComplexMatrix2),
      IsLocalPresentation PeriodicLattice.complexGaugeGroup 𝔇 (fun U' => U' d) U F O g ∧
      holomorphicPresentations L k l β ComplexCoordinates.matrixEquiv F O g ∧
      ∀ X ∈ complexEdgeForms (meshAt L k l),
        g (fun b : F => ComplexMatrix2.matExp (Complex.I • X b) * U b) = expTwist X U d := by
  classical
  have hUc := h𝔇 hU
  by_cases hd : d.IsPositivelyOriented
  · let F : Finset (Edge L k l) := {d}
    let s : F := ⟨d, Finset.mem_singleton_self d⟩
    refine ⟨F, edgeProduct PeriodicLattice.complexGaugeGroup F, fun w => w s,
      ⟨⟨Finset.singleton_nonempty d, ?_⟩,
      ⟨univ, isOpen_univ, (univ_inter _).symm⟩, fun b => hUc.1 b.1, ?_⟩, ?_, ?_⟩
    · intro b hb
      rw [Finset.mem_singleton.1 hb]
      exact hd
    · intro U' _ _
      rfl
    · exact entrywise_isHolomorphicToCoords hX β s (T := id) (e := fun _ => 1) (τ := id)
        (fun _ _ => by simp)
    · intro X _
      simp [expTwist, hd, s]
  · have hd' := positive_opposite hd
    let F : Finset (Edge L k l) := {d.opposite}
    let s : F := ⟨d.opposite, Finset.mem_singleton_self _⟩
    obtain ⟨e, τ, hT⟩ := adjugate_coords_entrywise
    refine ⟨F, edgeProduct PeriodicLattice.complexGaugeGroup F, fun w => Matrix.adjugate (w s),
      ⟨⟨Finset.singleton_nonempty _, ?_⟩,
      ⟨univ, isOpen_univ, (univ_inter _).symm⟩, fun b => hUc.1 b.1, ?_⟩, ?_, ?_⟩
    · intro b hb
      rw [Finset.mem_singleton.1 hb]
      exact hd'
    · intro U' hU' _
      have h1 : U' d = (U' d.opposite)⁻¹ := (h𝔇 hU').2 d.opposite
      have h2 : (U' d.opposite).det = 1 := (h𝔇 hU').1 d.opposite
      show U' d = Matrix.adjugate (U' d.opposite)
      rw [adjugate_eq_inv_of_det_eq_one h2, h1]
    · exact entrywise_isHolomorphicToCoords hX β s hT
    · intro X hXm
      have hcl := (hA.2.2 L k l hL hl).2.1.1.2 U hUc X hXm ⟨d.opposite, hd'⟩
      have hdet : (ComplexMatrix2.matExp (Complex.I • X d.opposite) * U d.opposite).det = 1 := by
        have h1 : leftExpMul ((1 : ℂ) • X d.opposite) (U d.opposite) ∈
            PeriodicLattice.complexGaugeGroup :=
          hcl.1 1
        rw [one_smul] at h1
        exact h1
      show Matrix.adjugate (ComplexMatrix2.matExp (Complex.I • X d.opposite) * U d.opposite) = _
      rw [adjugate_eq_inv_of_det_eq_one hdet]
      simp [expTwist, hd]
end ImageMap
section Differential
variable {L k l : ℕ} {f : AmbientSpace → AmbientSpace}
theorem pushField_isHolomorphic
    (hX : Matrices.GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (hA : LeftChartFields.Claim) (hL : Conventions.IsAdmissibleBlockingFactor L) (hl : l ≤ k)
    (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) {𝔇 : Set (Edge L k l → ComplexMatrix2)}
    (ho : IsFinitelyOpen PeriodicLattice.complexGaugeGroup 𝔇)
    (hT : ∀ U ∈ 𝔇, pushField f U ∈ fieldsValuedIn L k l PeriodicLattice.complexGaugeGroup) :
    IsHolomorphicFieldMap β 𝔇 (pushField f) := by
  refine ⟨ho, hT, fun c _ => ⟨ho.1, fun U hU => ?_⟩⟩
  obtain ⟨F, O, g, hw, hk, -⟩ := exists_presentation_eval hX hA hL hl β ho.1 hU (edgePreimage f c)
  exact ⟨F, O, g, hw, hk⟩
theorem holLeftDifferential_pushField
    (hX : Matrices.GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (hA : LeftChartFields.Claim) (hV : UniqueValue.PresentationsAgreeAndBallsOpen)
    (hI : LeftChartIsometryEquivariance) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hl : l ≤ k) (hs : meshAt L k l ≠ 0) (hf : IsDistancePreserving f)
    (hM : MapsSublatticeOnto (meshAt L k l) f) {𝔇 : Set (Edge L k l → ComplexMatrix2)}
    (ho : IsFinitelyOpen PeriodicLattice.complexGaugeGroup 𝔇)
    (hT : ∀ U ∈ fieldsValuedIn L k l PeriodicLattice.complexGaugeGroup,
      pushField f U ∈ fieldsValuedIn L k l PeriodicLattice.complexGaugeGroup)
    {U B : Edge L k l → ComplexMatrix2} (hU : U ∈ 𝔇)
    (hB : B ∈ complexEdgeForms (meshAt L k l)) :
    holLeftDifferential OneLoop.pauliBasis 𝔇 (pushField f) U B =
      isometryOnTangent f U B := by
  have hUc := ho.1 hU
  have hsU := hT U hUc
  have hBm : isometryOnTangent f U B ∈ complexEdgeForms (meshAt L k l) :=
    isometryOnTangent_mem hs hUc hB
  have key : ∀ c : Edge L k l, c.IsPositivelyOriented → logDirectionalDeriv ℂ
      (valueViaPresentation PeriodicLattice.complexGaugeGroup 𝔇
        (holomorphicPresentations L k l OneLoop.pauliBasis ComplexCoordinates.matrixEquiv)
        (fun U' => pushField f U' c) U) (pushField f U c) B =
      isometryOnTangent f U B c := by
    intro c hc
    classical
    obtain ⟨F₂, O₂, f₂, hw₂, hk₂, hv₂⟩ := exists_presentation_eval hX hA hL hl
      OneLoop.pauliBasis ho.1 hU (edgePreimage f c)
    have hw₂' : IsLocalPresentation PeriodicLattice.complexGaugeGroup 𝔇
      (fun U' => pushField f U' c) U F₂ O₂ f₂ := hw₂
    have hch := Classical.epsilon_spec
      (p := fun w : LocalData L k l ComplexMatrix2 =>
        IsLocalPresentation PeriodicLattice.complexGaugeGroup 𝔇 (fun U' => pushField f U' c) U
          w.support w.region w.fn ∧
        holomorphicPresentations L k l OneLoop.pauliBasis ComplexCoordinates.matrixEquiv
          w.support w.region w.fn) ⟨⟨F₂, O₂, f₂⟩, hw₂', hk₂⟩
    obtain ⟨ε, hε, hval⟩ := (hV L k l hL.1 hL.2 hl).1.2.2.2 _ ho
      (fun U' => pushField f U' c) U hU _ _ _ F₂ O₂ f₂ hch.1 hw₂' B 0
      (fun b hb => hB.1 b hb) (fun _ _ => ComplexMatrix2.traceless.zero_mem)
    have hmove : ∀ (F : Finset (Edge L k l)) (t : ℂ),
        UniqueValue.perturbedTuple F B 0 U (algebraMap ℂ ℂ t) (algebraMap ℂ ℂ 0) =
          fun b : F => ComplexMatrix2.matExp (Complex.I • (algebraMap ℂ ℂ t • B) b) * U b := by
      intro F t
      funext b
      simp [UniqueValue.perturbedTuple]
    have hev : ∀ᶠ t in 𝓝 (0 : ℂ), valueViaPresentation PeriodicLattice.complexGaugeGroup 𝔇
        (holomorphicPresentations L k l OneLoop.pauliBasis ComplexCoordinates.matrixEquiv)
        (fun U' => pushField f U' c) U (algebraMap ℂ ℂ t • B) =
        leftExpMul (t • isometryOnTangent f U B c) (pushField f U c) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hε] with t ht
      have h := (hval t 0 (by simpa using ht) (by simpa using hε)).2.2
      rw [hmove, hmove] at h
      have hXm : algebraMap ℂ ℂ t • B ∈ complexEdgeForms (meshAt L k l) :=
        (complexEdgeForms _).smul_mem _ hB
      refine Eq.trans h ((hv₂ _ hXm).trans ?_)
      have e₂ := congrFun ((hI L k l hL hl).2 f hf hM U hUc _ hXm) c
      rw [isometryOnTangent_smul] at e₂
      have e₃ : expTwist (algebraMap ℂ ℂ t • isometryOnTangent f U B) (pushField f U) c =
          leftExpMul (t • isometryOnTangent f U B c) (pushField f U c) := by
        simp [expTwist, hc, leftExpMul]
      exact e₂.symm.trans e₃
    have hclause := (hA.2.2 L k l hL hl).2.1.1.2 _ hsU _ hBm ⟨c, hc⟩
    have hlog := (hA.2.1 1 one_pos)
      (fun t : ℂ => leftExpMul (t • isometryOnTangent f U B c) (pushField f U c))
      (fun t _ => hclause.1 t) hclause.2.differentiableAt
    have hW0 : leftExpMul ((0 : ℂ) • isometryOnTangent f U B c) (pushField f U c) =
        pushField f U c := by
      simp [leftExpMul, ComplexMatrix2.matExp]
    have hcongr : (fun t : ℂ => ComplexMatrix2.logSeries
        (valueViaPresentation PeriodicLattice.complexGaugeGroup 𝔇
          (holomorphicPresentations L k l OneLoop.pauliBasis ComplexCoordinates.matrixEquiv)
          (fun U' => pushField f U' c) U (algebraMap ℂ ℂ t • B) *
            (pushField f U c)⁻¹)) =ᶠ[𝓝 0]
        fun t => ComplexMatrix2.logSeries
          (leftExpMul (t • isometryOnTangent f U B c) (pushField f U c) *
            (leftExpMul ((0 : ℂ) • isometryOnTangent f U B c) (pushField f U c))⁻¹) := by
      filter_upwards [hev] with t ht
      rw [ht, hW0]
    have hdet : IsUnit (pushField f U c).det := by
      have h1 : (pushField f U c).det = 1 := hsU.1 c
      rw [h1]
      exact isUnit_one
    have hd : HasDerivAt
        (fun t : ℂ => leftExpMul (t • isometryOnTangent f U B c) (pushField f U c))
        (Complex.I • isometryOnTangent f U B c * pushField f U c) 0 := hclause.2
    have hlog3 := hlog.2.2.1
    rw [hd.deriv] at hlog3
    show Complex.I⁻¹ • deriv (fun t : ℂ => ComplexMatrix2.logSeries
        (valueViaPresentation PeriodicLattice.complexGaugeGroup 𝔇
          (holomorphicPresentations L k l OneLoop.pauliBasis ComplexCoordinates.matrixEquiv)
          (fun U' => pushField f U' c) U (algebraMap ℂ ℂ t • B) *
            (pushField f U c)⁻¹)) 0 = isometryOnTangent f U B c
    rw [hcongr.deriv_eq, hlog3, hW0]
    show Complex.I⁻¹ • ((Complex.I • isometryOnTangent f U B c * pushField f U c) *
      (pushField f U c)⁻¹) = isometryOnTangent f U B c
    rw [mul_assoc, Matrix.mul_nonsing_inv _ hdet, mul_one, smul_smul,
      inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
  funext b
  unfold holLeftDifferential
  by_cases hb : b.IsPositivelyOriented
  · rw [extendOddly_of_positive _ hb]
    exact key b hb
  · have hr := positive_opposite hb
    rw [extendOddly_of_not_positive _ hb, key _ hr, hBm.2 b, neg_neg]
theorem holLeftDifferential_congr {i i' : ℕ} (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    {𝔇 : Set (Edge L k i → ComplexMatrix2)}
    {m m' : (Edge L k i → ComplexMatrix2) → Edge L k i' → ComplexMatrix2}
    (h : ∀ U ∈ 𝔇, m U = m' U) {U : Edge L k i → ComplexMatrix2} (hU : U ∈ 𝔇)
    (B : Edge L k i → ComplexMatrix2) :
    holLeftDifferential β 𝔇 m U B = holLeftDifferential β 𝔇 m' U B := by
  unfold holLeftDifferential
  congr 1
  funext c
  have hp : (fun w : LocalData L k i ComplexMatrix2 =>
      IsLocalPresentation PeriodicLattice.complexGaugeGroup 𝔇 (fun U' => m U' c) U
          w.support w.region w.fn ∧
        holomorphicPresentations L k i β ComplexCoordinates.matrixEquiv
          w.support w.region w.fn) =
      fun w => IsLocalPresentation PeriodicLattice.complexGaugeGroup 𝔇 (fun U' => m' U' c) U
          w.support w.region w.fn ∧
        holomorphicPresentations L k i β ComplexCoordinates.matrixEquiv
          w.support w.region w.fn := by
    funext w
    refine propext (and_congr_left fun _ => ?_)
    constructor
    · rintro ⟨h₁, h₂, h₃, h₄⟩
      exact ⟨h₁, h₂, h₃, fun U' hU' ho => by
        have := h₄ U' hU' ho
        simpa [h U' hU'] using this⟩
    · rintro ⟨h₁, h₂, h₃, h₄⟩
      exact ⟨h₁, h₂, h₃, fun U' hU' ho => by
        have := h₄ U' hU' ho
        simpa [h U' hU'] using this⟩
  have hv : valueViaPresentation PeriodicLattice.complexGaugeGroup 𝔇
      (holomorphicPresentations L k i β ComplexCoordinates.matrixEquiv) (fun U' => m U' c) U =
      valueViaPresentation PeriodicLattice.complexGaugeGroup 𝔇
      (holomorphicPresentations L k i β ComplexCoordinates.matrixEquiv) (fun U' => m' U' c) U := by
    funext X
    unfold valueViaPresentation chosenPresentation
    rw [hp]
  rw [hv, h U hU]
theorem holLeftDifferential_equivariant (hC : FullSpaceChainRule.Statement)
    (hX : Matrices.GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (hA : LeftChartFields.Claim) (hV : UniqueValue.PresentationsAgreeAndBallsOpen)
    (hI : LeftChartIsometryEquivariance) (hL : Conventions.IsAdmissibleBlockingFactor L)
    {i i' : ℕ} (hi : i ≤ k) (hi' : i' ≤ k)
    (hs : meshAt L k i ≠ 0) (hs' : meshAt L k i' ≠ 0) (hf : IsDistancePreserving f)
    (hM : MapsSublatticeOnto (meshAt L k i) f) (hM' : MapsSublatticeOnto (meshAt L k i') f)
    (hT : ∀ U ∈ fieldsValuedIn L k i PeriodicLattice.complexGaugeGroup,
      pushField f U ∈ fieldsValuedIn L k i PeriodicLattice.complexGaugeGroup)
    (hT' : ∀ U ∈ fieldsValuedIn L k i' PeriodicLattice.complexGaugeGroup,
      pushField f U ∈ fieldsValuedIn L k i' PeriodicLattice.complexGaugeGroup)
    {𝔇 : Set (Edge L k i → ComplexMatrix2)}
    {m : (Edge L k i → ComplexMatrix2) → Edge L k i' → ComplexMatrix2}
    (hm : IsHolomorphicFieldMap OneLoop.pauliBasis 𝔇 m)
    (hkeep : ∀ U ∈ 𝔇, pushField f U ∈ 𝔇)
    (hcomm : ∀ U ∈ 𝔇, m (pushField f U) = pushField f (m U))
    {U B : Edge L k i → ComplexMatrix2} (hU : U ∈ 𝔇) (hB : B ∈ complexEdgeForms (meshAt L k i))
    (hmB : holLeftDifferential OneLoop.pauliBasis 𝔇 m U B ∈
      complexEdgeForms (meshAt L k i')) :
    holLeftDifferential OneLoop.pauliBasis 𝔇 m (pushField f U)
        (isometryOnTangent f U B) =
      isometryOnTangent f (m U) (holLeftDifferential OneLoop.pauliBasis 𝔇 m U B) := by
  have hopen' : IsFinitelyOpen PeriodicLattice.complexGaugeGroup
      (fieldsValuedIn L k i' PeriodicLattice.complexGaugeGroup) :=
    ((hV L k i' hL.1 hL.2 hi').2.2 1 one_pos).1
  have hSi : IsHolomorphicFieldMap OneLoop.pauliBasis 𝔇
      (pushField f : (Edge L k i → ComplexMatrix2) → Edge L k i → ComplexMatrix2) :=
    pushField_isHolomorphic hX hA hL hi _ hm.1 fun U hU => hT U (hm.1.1 hU)
  have hSi' : IsHolomorphicFieldMap OneLoop.pauliBasis
      (fieldsValuedIn L k i' PeriodicLattice.complexGaugeGroup)
      (pushField f : (Edge L k i' → ComplexMatrix2) → Edge L k i' → ComplexMatrix2) :=
    pushField_isHolomorphic hX hA hL hi' _ hopen' hT'
  have hd₁ : compositeDomain 𝔇 𝔇
      (pushField f : (Edge L k i → ComplexMatrix2) → Edge L k i → ComplexMatrix2) = 𝔇 := by
    ext W
    exact ⟨fun h => h.1, fun h => ⟨h, hkeep W h⟩⟩
  have hd₂ : compositeDomain 𝔇
      (fieldsValuedIn L k i' PeriodicLattice.complexGaugeGroup) m = 𝔇 := by
    ext W
    exact ⟨fun h => h.1, fun h => ⟨h, hm.2.1 h⟩⟩
  have c₁ := (hC L k i i i' hL hi hi hi').2 OneLoop.pauliBasis 𝔇 𝔇 _ m hSi hm
    (by rw [hd₁]; exact hm.1)
  have c₂ := (hC L k i i' i' hL hi hi' hi').2 OneLoop.pauliBasis 𝔇
    (fieldsValuedIn L k i' PeriodicLattice.complexGaugeGroup) m _ hm hSi'
    (by rw [hd₂]; exact hm.1)
  have e₁ := c₁.2 U (by rw [hd₁]; exact hU) B hB
  have e₂ := c₂.2 U (by rw [hd₂]; exact hU) B hB
  rw [hd₁] at e₁
  rw [hd₂] at e₂
  rw [holLeftDifferential_pushField hX hA hV hI hL hi hs hf hM hm.1 hT hU hB] at e₁
  rw [holLeftDifferential_pushField hX hA hV hI hL hi' hs' hf hM' hopen' hT' (hm.2.1 hU) hmB] at e₂
  rw [← e₁, ← e₂]
  exact holLeftDifferential_congr _ (fun W hW => hcomm W hW) hU B
end Differential
section Step
variable {L k j : ℕ} {f : AmbientSpace → AmbientSpace}
theorem covDiff_mem {a : ℝ} (ha : a ≠ 0) {W : InfiniteLattice.Link a → ComplexMatrix2}
    (hW : IsFieldIn PeriodicLattice.complexGaugeGroup W)
    {l : InfiniteLattice.LatticePoint a → ComplexMatrix2}
    (hl : ∀ x, l x ∈ ComplexMatrix2.traceless) : covDiff W l ∈ complexEdgeForms a := by
  refine ⟨fun b hb => ?_, fun b => extendOddly_opposite ha _ b⟩
  show covDiff W l b ∈ ComplexMatrix2.traceless
  unfold covDiff
  rw [extendOddly_of_positive _ hb]
  have h1 : (W b).det = 1 := hW.1 b
  refine ComplexMatrix2.traceless.sub_mem (conjugateBy_mem_traceless_of_isUnit ?_ (hl _)) (hl _)
  rw [h1]
  exact isUnit_one
theorem pushField_mem_small
    (hT : ∀ U ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup,
      pushField f U ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    {V : Edge L k j → ComplexMatrix2} (hV : V ∈ smallComplexFields L k j) :
    pushField f V ∈ smallComplexFields L k j :=
  ⟨hT V hV.1, fun _ => hV.2 _⟩
theorem smoothingMap_pushField (hH : ComplexSmoothingEquivariance.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) (hf : IsDistancePreserving f)
    (hM : MapsSublatticeOnto (meshAt L k (j + 1)) f)
    (hB : MapsLinksOnto (meshAt L k (j + 1)) f) (hi : Function.Injective f)
    (hO : IteratedMeans.Unbounded.SpaceConditions L k)
    (hP : MeanStableFields.Infinite.MeanStableConditions L k)
    (hT : ∀ U ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup,
      pushField f U ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    {V : Edge L k j → ComplexMatrix2} (hV : V ∈ smallComplexFields L k j) :
    smoothingMap L k j (pushField f V) = pushField f (smoothingMap L k j V) := by
  have hcV : smoothingMap L k j V ∈ fieldsValuedIn L k (j + 1) PeriodicLattice.complexGaugeGroup :=
    hO.meanStep_mem j hj V hV
  have hcsV : smoothingMap L k j (pushField f V) ∈
      fieldsValuedIn L k (j + 1) PeriodicLattice.complexGaugeGroup :=
    hO.meanStep_mem j hj _ (pushField_mem_small hT hV)
  funext b
  show smoothingMap L k j (pushField f V) b = smoothingMap L k j V (edgePreimage f b)
  by_cases hc : (edgePreimage f b).IsPositivelyOriented
  · have h := (hH L hL k j hj f hf hM _ hc V (hP.mem_polydisc j hj _ hc V hV)).2
    rw [edgeImage_edgePreimage hM hB hi] at h
    exact h
  · have hr := positive_opposite hc
    have h := (hH L hL k j hj f hf hM _ hr V (hP.mem_polydisc j hj _ hr V hV)).2
    rw [edgeImage_opposite hM hB, edgeImage_edgePreimage hM hB hi] at h
    have e₁ : smoothingMap L k j (pushField f V) b =
        (smoothingMap L k j (pushField f V) b.opposite)⁻¹ := hcsV.2 b.opposite
    have e₂ : smoothingMap L k j V (edgePreimage f b) =
        (smoothingMap L k j V (edgePreimage f b).opposite)⁻¹ := hcV.2 (edgePreimage f b).opposite
    have h' : smoothingMap L k j (pushField f V) b.opposite =
        smoothingMap L k j V (edgePreimage f b).opposite := h
    rw [e₁, h', ← e₂]
theorem cubeVertices_bijOn (hM : MapsSublatticeOnto (meshAt L k j) f) (hi : Function.Injective f)
    (hZ : ∀ y : Vertex L k (j + 1), f '' cube L (meshAt L k j) y =
      cube L (meshAt L k j) (vertexImage f y)) (y : Vertex L k (j + 1)) :
    BijOn (vertexImage f : Vertex L k j → Vertex L k j)
      (cubeVertices L (meshAt L k j) y)
      (cubeVertices L (meshAt L k j) (vertexImage f y)) := by
  refine ⟨fun x hx => ?_, (vertexImage_injective hM hi).injOn, fun x' hx' => ?_⟩
  · show ((vertexImage f x : Vertex L k j) : AmbientSpace) ∈
      cube L (meshAt L k j) (vertexImage f y)
    rw [coe_vertexImage hM, ← hZ]
    exact ⟨_, hx, rfl⟩
  · have h : (x' : AmbientSpace) ∈ f '' cube L (meshAt L k j) y := by
      rw [hZ]
      exact hx'
    obtain ⟨z, hz, e⟩ := h
    refine ⟨vertexPreimage f x', ?_, vertexImage_vertexPreimage hM x'⟩
    have e' : ((vertexPreimage f x' : Vertex L k j) : AmbientSpace) = z :=
      hi ((apply_vertexPreimage hM x').trans e.symm)
    show ((vertexPreimage f x' : Vertex L k j) : AmbientSpace) ∈ cube L (meshAt L k j) y
    rw [e']
    exact hz
theorem forwardFrom_positive (y : Vertex L k (j + 1)) :
    (InfiniteLattice.Link.forwardFrom y 0 : Edge L k (j + 1)).IsPositivelyOriented :=
  ⟨0, by simp [InfiniteLattice.Link.forwardFrom]⟩
theorem adjointCubeAverage_pushField (hH : ComplexSmoothingEquivariance.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) (hf : IsDistancePreserving f)
    (hMj : MapsSublatticeOnto (meshAt L k j) f)
    (hM : MapsSublatticeOnto (meshAt L k (j + 1)) f) (hi : Function.Injective f)
    (hZ : ∀ y : Vertex L k (j + 1), f '' cube L (meshAt L k j) y =
      cube L (meshAt L k j) (vertexImage f y))
    (hP : MeanStableFields.Infinite.MeanStableConditions L k)
    {V : Edge L k j → ComplexMatrix2} (hV : V ∈ smallComplexFields L k j)
    (l : Vertex L k j → ComplexMatrix2) :
    adjointCubeAverage (pushField f V) (pushSiteFunction f l) =
      pushSiteFunction f (adjointCubeAverage V l) := by
  have key : ∀ y : Vertex L k (j + 1),
      adjointCubeAverage (pushField f V) (pushSiteFunction f l) (vertexImage f y) =
        adjointCubeAverage V l y := by
    intro y
    unfold adjointCubeAverage
    congr 1
    symm
    refine finsum_mem_eq_of_bijOn _ (cubeVertices_bijOn hMj hi hZ y) fun x hx => ?_
    have hc := forwardFrom_positive (k := k) (j := j) y
    have h := (hH L hL k j hj f hf hM _ hc V (hP.mem_polydisc j hj _ hc V hV)).1 y
      (Or.inl rfl) x hx
    rw [h]
    show _ = ComplexMatrix2.conjugateBy _ (l (vertexPreimage f (vertexImage f x)))
    rw [vertexPreimage_vertexImage hMj hi]
  funext y'
  show _ = adjointCubeAverage V l (vertexPreimage f y')
  rw [← key, vertexImage_vertexPreimage hM]
theorem eventually_mem_polydisc (hW : UniqueValue.PresentationsAgreeAndBallsOpen)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k)
    (hP : MeanStableFields.Infinite.MeanStableConditions L k)
    {c : Edge L k (j + 1)} (hc : c.IsPositivelyOriented) {V B : Edge L k j → ComplexMatrix2}
    (hV : V ∈ smallComplexFields L k j) (hB : B ∈ complexEdgeForms (meshAt L k j)) :
    ∀ᶠ t in 𝓝 (0 : ℂ), expTwist (algebraMap ℂ ℂ t • B) V ∈
      nearIdentityPolydisc L k j (polydiscRadius L) c := by
  obtain ⟨F, hF, hwr⟩ := hP.polydisc_presentation j hj c hc
  have w := hwr V hV
  obtain ⟨ε, hε, hval⟩ := (hW L k j hL.1 hL.2 hj.le).1.2.2.2 _
    (hP.isFinitelyOpen_nearOne j hj) _ V hV
    _ _ _ _ _ _ w w B 0 (fun b hb => hB.1 b hb) (fun _ _ => ComplexMatrix2.traceless.zero_mem)
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hε] with t ht
  have hm := (hval t 0 (by simpa using ht) (by simpa using hε)).1
  have hm' : MeanStableFields.Infinite.pointOfFinset c F hF
      (UniqueValue.perturbedTuple F B 0 V (algebraMap ℂ ℂ t) (algebraMap ℂ ℂ 0)) ∈
      DoubleBlockPolydisc.positiveImage InfiniteLattice.Link.IsPositivelyOriented
        (doubleCubeLinks L (meshAt L k j) c)
        (nearIdentityPolydisc L k j (polydiscRadius L) c) := hm
  unfold DoubleBlockPolydisc.positiveImage at hm'
  obtain ⟨_, ⟨W, hWp, rfl⟩, he⟩ := hm'
  have hpos : ∀ b (hb : b ∈ doubleCubeLinks L (meshAt L k j) c), b.IsPositivelyOriented →
      W b = expTwist (algebraMap ℂ ℂ t • B) V b := by
    intro b hb hp
    have h := congrFun he ⟨b, hb, hp⟩
    have h' : W b = ComplexMatrix2.matExp
        (Complex.I • (algebraMap ℂ ℂ t • B b + algebraMap ℂ ℂ 0 • (0 : ComplexMatrix2))) *
        V b := by
      simpa [BondSetFields.readPositive, BondSetFields.restrictTo,
        MeanStableFields.Infinite.pointOfFinset, UniqueValue.perturbedTuple] using h
    rw [h']
    simp [expTwist, hp]
  have hrev : ∀ b, b ∈ doubleCubeLinks L (meshAt L k j) c →
      b.opposite ∈ doubleCubeLinks L (meshAt L k j) c := fun b hb => ⟨hb.2, hb.1⟩
  have hall : ∀ b ∈ doubleCubeLinks L (meshAt L k j) c,
      W b = expTwist (algebraMap ℂ ℂ t • B) V b := by
    intro b hb
    by_cases hp : b.IsPositivelyOriented
    · exact hpos b hb hp
    · have hr := positive_opposite hp
      have h1 : W b = (W b.opposite)⁻¹ := hWp.1.2 b.opposite (hrev b hb)
      rw [h1, hpos _ (hrev b hb) hr]
      simp [expTwist, hp, hr]
  refine ⟨⟨fun b hb => ?_, fun b hb => ?_⟩, fun b hb => ?_⟩
  · rw [← hall b hb]
    exact hWp.1.1 b hb
  · rw [← hall b hb, ← hall _ (hrev b hb)]
    exact hWp.1.2 b hb
  · rw [← hall b hb]
    exact hWp.2 b hb
theorem logDirectionalDeriv_congr {α : Type} {φ₁ φ₂ : (α → ComplexMatrix2) → ComplexMatrix2}
    {W₁ W₂ : ComplexMatrix2} {B₁ B₂ : α → ComplexMatrix2} (hW₀ : W₁ = W₂)
    (h : ∀ᶠ t in 𝓝 (0 : ℂ), φ₁ (algebraMap ℂ ℂ t • B₁) = φ₂ (algebraMap ℂ ℂ t • B₂)) :
    logDirectionalDeriv ℂ φ₁ W₁ B₁ = logDirectionalDeriv ℂ φ₂ W₂ B₂ := by
  subst hW₀
  have e : (fun t : ℂ => ComplexMatrix2.logSeries (φ₁ (algebraMap ℂ ℂ t • B₁) * W₁⁻¹)) =ᶠ[𝓝 0]
      fun t => ComplexMatrix2.logSeries (φ₂ (algebraMap ℂ ℂ t • B₂) * W₁⁻¹) := by
    filter_upwards [h] with t ht
    rw [ht]
  unfold logDirectionalDeriv
  rw [e.deriv_eq]
theorem contourLogDrift_pushField (hH : ComplexSmoothingEquivariance.Statement)
    (hW : UniqueValue.PresentationsAgreeAndBallsOpen) (hI : LeftChartIsometryEquivariance)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) (hf : IsDistancePreserving f)
    (hMj : MapsSublatticeOnto (meshAt L k j) f)
    (hM : MapsSublatticeOnto (meshAt L k (j + 1)) f) (hi : Function.Injective f)
    (hZ : ∀ y : Vertex L k (j + 1), f '' cube L (meshAt L k j) y =
      cube L (meshAt L k j) (vertexImage f y))
    (hP : MeanStableFields.Infinite.MeanStableConditions L k)
    {V B : Edge L k j → ComplexMatrix2} (hV : V ∈ smallComplexFields L k j)
    (hB : B ∈ complexEdgeForms (meshAt L k j)) :
    contourLogDrift (pushField f V) (isometryOnTangent f V B) =
      pushSiteFunction f (contourLogDrift V B) := by
  have key : ∀ y : Vertex L k (j + 1),
      contourLogDrift (pushField f V) (isometryOnTangent f V B) (vertexImage f y) =
        contourLogDrift V B y := by
    intro y
    unfold contourLogDrift
    congr 1
    symm
    refine finsum_mem_eq_of_bijOn _ (cubeVertices_bijOn hMj hi hZ y) fun x hx => ?_
    have hc := forwardFrom_positive (k := k) (j := j) y
    have h0 := (hH L hL k j hj f hf hM _ hc V (hP.mem_polydisc j hj _ hc V hV)).1 y
      (Or.inl rfl) x hx
    refine logDirectionalDeriv_congr h0.symm ?_
    filter_upwards [eventually_mem_polydisc hW hL hj hP hc hV hB] with t ht
    have hXm : algebraMap ℂ ℂ t • B ∈ complexEdgeForms (meshAt L k j) :=
      (complexEdgeForms _).smul_mem _ hB
    have e := (hI L k j hL hj.le).2 f hf hMj V hV.1 _ hXm
    rw [isometryOnTangent_smul] at e
    show _ = complexContourMean L (expTwist (algebraMap ℂ ℂ t • isometryOnTangent f V B)
      (pushField f V)) (vertexImage f y) (vertexImage f x)
    rw [e, (hH L hL k j hj f hf hM _ hc _ ht).1 y (Or.inl rfl) x hx]
  funext y'
  show _ = contourLogDrift V B (vertexPreimage f y')
  rw [← key, vertexImage_vertexPreimage hM]
theorem complexSmoothingDeriv_pushField (hC : FullSpaceChainRule.Statement)
    (hX : Matrices.GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (hA : LeftChartFields.Claim) (hW : UniqueValue.PresentationsAgreeAndBallsOpen)
    (hI : LeftChartIsometryEquivariance)
    (hS : CovariantStepComplexLinear)
    (hH : ComplexSmoothingEquivariance.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) (hs : meshAt L k j ≠ 0)
    (hs' : meshAt L k (j + 1) ≠ 0) (hf : IsDistancePreserving f)
    (hMj : MapsSublatticeOnto (meshAt L k j) f)
    (hM : MapsSublatticeOnto (meshAt L k (j + 1)) f)
    (hBd : MapsLinksOnto (meshAt L k (j + 1)) f) (hi : Function.Injective f)
    (hO : IteratedMeans.Unbounded.SpaceConditions L k)
    (hP : MeanStableFields.Infinite.MeanStableConditions L k)
    (hT : ∀ U ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup,
      pushField f U ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    (hT' : ∀ U ∈ fieldsValuedIn L k (j + 1) PeriodicLattice.complexGaugeGroup,
      pushField f U ∈ fieldsValuedIn L k (j + 1) PeriodicLattice.complexGaugeGroup)
    {V B : Edge L k j → ComplexMatrix2} (hV : V ∈ smallComplexFields L k j)
    (hB : B ∈ complexEdgeForms (meshAt L k j)) :
    complexSmoothingDeriv (pushField f V) (isometryOnTangent f V B) =
      isometryOnTangent f (smoothingMap L k j V) (complexSmoothingDeriv V B) := by
  have hm : IsHolomorphicFieldMap OneLoop.pauliBasis (smallComplexFields L k j)
      (smoothingMap L k j) :=
    ⟨hP.isFinitelyOpen_nearOne j hj, fun V hV => hO.meanStep_mem j hj V hV,
      fun c hc => hP.holomorphic_smoothing j hj c hc _⟩
  exact holLeftDifferential_equivariant hC hX hA hW hI hL hj.le hj hs hs' hf hMj hM hT hT' hm
    (fun _ h => pushField_mem_small hT h)
    (fun _ h => smoothingMap_pushField hH hL hj hf hM hBd hi hO hP hT h) hV hB
    ((hS L hL k j hj V hV).1 B hB).1
end Step
section Iterates
variable {L k : ℕ} {f : AmbientSpace → AmbientSpace}
theorem equivariance_at (hC : FullSpaceChainRule.Statement)
    (hCh : ComplexIterChain)
    (hH : ComplexSmoothingEquivariance.Statement)
    (hPP : MeanStableFields.MeanStableFieldsHold)
    (hOO : IteratedMeans.IteratedMeansHold)
    (hW : UniqueValue.PresentationsAgreeAndBallsOpen)
    (hA : LeftChartFields.Claim)
    (hX : Matrices.GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (hS : CovariantStepComplexLinear)
    (hI : LeftChartIsometryEquivariance)
    (hTr : Translations.TranslationProperties)
    (hF : SymmetriesAreHypercubicMotions)
    (hZ : BlockStructure)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {j : ℕ} (hjk : j ≤ k)
    (hf : IsDistancePreserving f)
    (hMk : MapsSublatticeOnto (meshAt L k k) f) {U : Edge L k 0 → ComplexMatrix2}
    (hU : U ∈ smallIterateFields L k) :
    (∀ l : Vertex L k 0 → ComplexMatrix2, (∀ x, l x ∈ ComplexMatrix2.traceless) →
      covDiff (pushField f U) (pushSiteFunction f l) =
        isometryOnTangent f U (covDiff U l) ∧
      iterAdjointCubeAverage L k (pushField f U) j (pushSiteFunction f l) =
        pushSiteFunction f (iterAdjointCubeAverage L k U j l)) ∧
    ∀ B ∈ complexEdgeForms (meshAt L k 0),
      complexIterDeriv L k j (pushField f U) (isometryOnTangent f U B) =
        isometryOnTangent f (complexIter L k j U) (complexIterDeriv L k j U B) ∧
      iterCovariantDeriv L k (pushField f U) j (isometryOnTangent f U B) =
        isometryOnTangent f (complexIter L k j U) (iterCovariantDeriv L k U j B) ∧
      iterContourLogDrift L k (pushField f U) j (isometryOnTangent f U B) =
        pushSiteFunction f (iterContourLogDrift L k U j B) := by
  have hL0 : 0 < L := by have := hL.2; omega
  have hsp : ∀ i, meshAt L k i ≠ 0 := fun i =>
    zpow_ne_zero _ (by exact_mod_cast hL0.ne')
  obtain ⟨⟨w, -, v, -, hwv⟩, hiso, -⟩ := (hF L hL0 hL k).2 k le_rfl f hf hMk
  have hM : ∀ i ≤ k, MapsSublatticeOnto (meshAt L k i) f := fun i h => (hiso i h).1
  have hBd : ∀ i ≤ k, MapsLinksOnto (meshAt L k i) f := fun i h => (hiso i h).2.1
  have hfi : Function.Injective f := by
    intro x y h
    rw [hwv x, hwv y] at h
    exact w.injective (add_right_cancel h)
  have hcov := fun (i : ℕ) (h : i ≤ k) => (hTr L hL k i h).2.2.2.2.1.2.2.1 f hf (hM i h)
  have hT : ∀ i ≤ k, ∀ V ∈ fieldsValuedIn L k i PeriodicLattice.complexGaugeGroup,
      pushField f V ∈ fieldsValuedIn L k i PeriodicLattice.complexGaugeGroup :=
    fun i h V hV => (hcov i h V hV).1
  have hD : ∀ i ≤ k, ∀ V ∈ fieldsValuedIn L k i PeriodicLattice.complexGaugeGroup,
      ∀ l : Vertex L k i → ComplexMatrix2, (∀ x, l x ∈ ComplexMatrix2.traceless) →
        covDiff (pushField f V) (pushSiteFunction f l) =
          isometryOnTangent f V (covDiff V l) :=
    fun i h V hV => (hcov i h V hV).2
  have hZ' : ∀ i < k, ∀ y : Vertex L k (i + 1), f '' cube L (meshAt L k i) y =
      cube L (meshAt L k i) (vertexImage f y) := fun i hi =>
    (hZ L k (i + 1) hL (by omega) (by omega) (by omega)).2.2.2.2 f hf (hM (i + 1) hi)
  have hPk := fun (i : ℕ) (hi : i < k) => (hPP L hL k (by omega)).2
  have hOk := fun (i : ℕ) (hi : i < k) => (hOO L hL k (by omega)).2
  have hAvg : ∀ i < k, ∀ V ∈ smallComplexFields L k i,
      smoothingMap L k i (pushField f V) = pushField f (smoothingMap L k i V) :=
    fun i hi V hV => smoothingMap_pushField hH hL hi hf (hM (i + 1) hi) (hBd (i + 1) hi) hfi
      (hOk i hi) (hPk i hi) (hT i hi.le) hV
  have hAd : ∀ i < k, ∀ V ∈ smallComplexFields L k i, ∀ l : Vertex L k i → ComplexMatrix2,
      adjointCubeAverage (pushField f V) (pushSiteFunction f l) =
        pushSiteFunction f (adjointCubeAverage V l) :=
    fun i hi V hV l => adjointCubeAverage_pushField hH hL hi hf (hM i hi.le) (hM (i + 1) hi) hfi
      (hZ' i hi) (hPk i hi) hV l
  have hDr : ∀ i < k, ∀ V ∈ smallComplexFields L k i,
      ∀ B ∈ complexEdgeForms (meshAt L k i),
      contourLogDrift (pushField f V) (isometryOnTangent f V B) =
        pushSiteFunction f (contourLogDrift V B) :=
    fun i hi V hV B hB => contourLogDrift_pushField hH hW hI hL hi hf (hM i hi.le) (hM (i + 1) hi)
      hfi (hZ' i hi) (hPk i hi) hV hB
  have hQ₁ : ∀ i < k, ∀ V ∈ smallComplexFields L k i,
      ∀ B ∈ complexEdgeForms (meshAt L k i),
      complexSmoothingDeriv (pushField f V) (isometryOnTangent f V B) =
        isometryOnTangent f (smoothingMap L k i V) (complexSmoothingDeriv V B) :=
    fun i hi V hV B hB => complexSmoothingDeriv_pushField hC hX hA hW hI hS hH hL hi (hsp i)
      (hsp (i + 1)) hf (hM i hi.le) (hM (i + 1) hi) (hBd (i + 1) hi) hfi (hOk i hi) (hPk i hi)
      (hT i hi.le) (hT (i + 1) hi) hV hB
  have hCo : ∀ i < k, ∀ V ∈ smallComplexFields L k i,
      ∀ B ∈ complexEdgeForms (meshAt L k i),
      covariantSmoothingDeriv (pushField f V) (isometryOnTangent f V B) =
        isometryOnTangent f (smoothingMap L k i V) (covariantSmoothingDeriv V B) := by
    intro i hi V hV B hB
    have hc : smoothingMap L k i V ∈ fieldsValuedIn L k (i + 1) PeriodicLattice.complexGaugeGroup :=
      (hOk i hi).meanStep_mem i hi V hV
    unfold covariantSmoothingDeriv
    rw [hQ₁ i hi V hV B hB, hAvg i hi V hV, hDr i hi V hV B hB,
      hD (i + 1) hi _ hc _ ((hS L hL k i hi V hV).1 B hB).2, ← isometryOnTangent_add]
  have hCm : ∀ i < k, ∀ V ∈ smallComplexFields L k i,
      ∀ B ∈ complexEdgeForms (meshAt L k i),
      covariantSmoothingDeriv V B ∈ complexEdgeForms (meshAt L k (i + 1)) := by
    intro i hi V hV B hB
    have hc : smoothingMap L k i V ∈ fieldsValuedIn L k (i + 1) PeriodicLattice.complexGaugeGroup :=
      (hOk i hi).meanStep_mem i hi V hV
    exact (complexEdgeForms _).add_mem ((hS L hL k i hi V hV).1 B hB).1
      (covDiff_mem (hsp (i + 1)) hc ((hS L hL k i hi V hV).1 B hB).2)
  have hfield : ∀ i, i ≤ k → complexIter L k i (pushField f U) =
      pushField f (complexIter L k i U) := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      show smoothingMap L k i (complexIter L k i (pushField f U)) =
        pushField f (smoothingMap L k i (complexIter L k i U))
      rw [ih (by omega)]
      exact hAvg i hi _ (hU.2 i hi)
  have hsU : pushField f U ∈ smallIterateFields L k :=
    ⟨hT 0 (Nat.zero_le k) U hU.1, fun i hi => by
      rw [hfield i hi.le]
      exact pushField_mem_small (hT i hi.le) (hU.2 i hi)⟩
  have hQ : ∀ B ∈ complexEdgeForms (meshAt L k 0), ∀ i, i ≤ k →
      complexIterDeriv L k i (pushField f U) (isometryOnTangent f U B) =
        isometryOnTangent f (complexIter L k i U) (complexIterDeriv L k i U B) := by
    intro B hB i
    have hsB := isometryOnTangent_mem (f := f) (hsp 0) hU.1 hB
    have c₁ := hCh L hL k _ hsU _ hsB
    have c₂ := hCh L hL k U hU B hB
    induction i with
    | zero =>
      intro _
      rw [c₁.1, c₂.1]
      rfl
    | succ i ih =>
      intro hi
      have hi' : i < k := hi
      rw [c₁.2.1 i hi', c₂.2.1 i hi', hfield i hi'.le, ih hi'.le]
      exact hQ₁ i hi' _ (hU.2 i hi') _ (c₂.2.2 i hi'.le)
  have hCv : ∀ B ∈ complexEdgeForms (meshAt L k 0), ∀ i, i ≤ k →
      iterCovariantDeriv L k (pushField f U) i (isometryOnTangent f U B) =
        isometryOnTangent f (complexIter L k i U) (iterCovariantDeriv L k U i B) ∧
      iterCovariantDeriv L k U i B ∈ complexEdgeForms (meshAt L k i) := by
    intro B hB i
    induction i with
    | zero => intro _; exact ⟨rfl, hB⟩
    | succ i ih =>
      intro hi
      have hi' : i < k := hi
      obtain ⟨ih₁, ih₂⟩ := ih hi'.le
      refine ⟨?_, hCm i hi' _ (hU.2 i hi') _ ih₂⟩
      show covariantSmoothingDeriv (complexIter L k i (pushField f U))
          (iterCovariantDeriv L k (pushField f U) i (isometryOnTangent f U B)) = _
      rw [hfield i hi'.le, ih₁]
      exact hCo i hi' _ (hU.2 i hi') _ ih₂
  have hAi : ∀ (l : Vertex L k 0 → ComplexMatrix2) (i : ℕ), i ≤ k →
      iterAdjointCubeAverage L k (pushField f U) i (pushSiteFunction f l) =
        pushSiteFunction f (iterAdjointCubeAverage L k U i l) := by
    intro l i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      have hi' : i < k := hi
      show adjointCubeAverage (complexIter L k i (pushField f U))
          (iterAdjointCubeAverage L k (pushField f U) i (pushSiteFunction f l)) = _
      rw [hfield i hi'.le, ih hi'.le]
      exact hAd i hi' _ (hU.2 i hi') _
  have hN : ∀ B ∈ complexEdgeForms (meshAt L k 0), ∀ i, i ≤ k →
      iterContourLogDrift L k (pushField f U) i (isometryOnTangent f U B) =
        pushSiteFunction f (iterContourLogDrift L k U i B) := by
    intro B hB i
    have c₂ := hCh L hL k U hU B hB
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      have hi' : i < k := hi
      show adjointCubeAverage (complexIter L k i (pushField f U))
          (iterContourLogDrift L k (pushField f U) i (isometryOnTangent f U B)) +
        contourLogDrift (complexIter L k i (pushField f U))
          (complexIterDeriv L k i (pushField f U) (isometryOnTangent f U B)) = _
      rw [hfield i hi'.le, ih hi'.le, hQ B hB i hi'.le, hAd i hi' _ (hU.2 i hi'),
        hDr i hi' _ (hU.2 i hi') _ (c₂.2.2 i hi'.le)]
      rfl
  exact ⟨fun l hl => ⟨hD 0 (Nat.zero_le k) U hU.1 l hl, hAi l j hjk⟩,
    fun B hB => ⟨hQ B hB j hjk, (hCv B hB j hjk).1, hN B hB j hjk⟩⟩
end Iterates
end IsometryEquivariance
theorem IsometryEquivariance.holds
    (hC : FullSpaceChainRule.Statement)
    (hCh : ComplexIterChain)
    (hH : ComplexSmoothingEquivariance.Statement)
    (hPP : MeanStableFields.MeanStableFieldsHold)
    (hOO : IteratedMeans.IteratedMeansHold)
    (hW : UniqueValue.PresentationsAgreeAndBallsOpen)
    (hA : LeftChartFields.Claim)
    (hX : Matrices.GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (hS : CovariantStepComplexLinear)
    (hI : LeftChartIsometryEquivariance)
    (hTr : Translations.TranslationProperties)
    (hF : SymmetriesAreHypercubicMotions)
    (hZ : BlockStructure) :
    CovariantSmoothingIsometryEquivariance := by
  intro L hL k j hjk f hf hMk U hU
  exact IsometryEquivariance.equivariance_at hC hCh hH hPP hOO hW hA hX hS hI hTr hF hZ hL
    hjk hf hMk hU
end YangMills.Construction.Tower.FullSpace
end
