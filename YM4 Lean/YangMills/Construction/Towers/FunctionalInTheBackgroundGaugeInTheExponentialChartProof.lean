import YangMills.Construction.Matrices.RestrictionsSumsAndCoordinatesOfRealAnalyticMaps
import YangMills.Construction.Towers.FibresOfARealAnalyticSubmersionProof
import YangMills.Construction.Towers.FunctionalInTheBackgroundGaugeInTheExponentialChart
import YangMills.Construction.Towers.RealAnalyticMapsAreReadInTheChartAtOneProof
import YangMills.Construction.Towers.RepresentationOfTheLogarithmOfTheTotalNormaliser
import YangMills.Construction.Towers.TheTorusMatricesOfTheMassiveOperatorFunctionsProof
import Mathlib
set_option autoImplicit false
open Filter Set Asymptotics
open scoped Topology ContDiff
noncomputable section
namespace YangMills.Construction.Tower
namespace ExpChartFunctionalProof
open Matrices (ComplexMatrix2)
section TaylorTwo
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem taylor_two_remainder_isLittleO {f : E → ℝ} (hf : ContDiffAt ℝ ∞ f 0) :
    (fun x => f x - (f 0 + fderiv ℝ f 0 x + 1 / 2 * fderiv ℝ (fderiv ℝ f) 0 x x)) =o[𝓝 0]
      fun x => ‖x‖ ^ 2 := by
  set D := fderiv ℝ f with hDdef
  set B := fderiv ℝ D 0 with hBdef
  have h2inf : (2 : WithTop ℕ∞) ≤ ∞ := ENat.LEInfty.out
  have hsymm : ∀ x y, B x y = B y x := by
    have h := hf.isSymmSndFDerivAt (by simpa using h2inf)
    intro x y
    exact h x y
  have hD : HasFDerivAt D B 0 := by
    have h1 : ContDiffAt ℝ 1 D 0 := hf.fderiv_right (m := 1) (by rw [one_add_one_eq_two]; exact h2inf)
    exact (h1.differentiableAt (by simp)).hasFDerivAt
  have hdiff : ∀ᶠ x in 𝓝 (0 : E), DifferentiableAt ℝ f x := by
    have h2 : ContDiffAt ℝ 2 f 0 := hf.of_le h2inf
    filter_upwards [h2.eventually (by simp)] with x hx
    exact hx.differentiableAt (by simp)
  have hsmall := (hasFDerivAt_iff_isLittleO_nhds_zero.1 hD)
  rw [isLittleO_iff]
  intro ε hε
  have hsmall' := (isLittleO_iff.1 hsmall) hε
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hdiff.and hsmall')
  have hg : ∀ y ∈ Metric.ball (0 : E) δ, HasFDerivAt
      (fun x => f x - (f 0 + D 0 x + 1 / 2 * B x x)) (D y - D 0 - B y) y := by
    intro y hy
    have h1 : HasFDerivAt f (D y) y := (hball y hy).1.hasFDerivAt
    have h2 : HasFDerivAt (fun x => B x x) (B y + B.flip y) y := by
      have h := B.hasFDerivAt_of_bilinear (hasFDerivAt_id y) (hasFDerivAt_id y)
      refine h.congr_fderiv ?_
      ext v
      simp
    have h3 : HasFDerivAt (fun x => D 0 x) (D 0) y := (D 0).hasFDerivAt
    have h4 := h1.sub (((hasFDerivAt_const (f 0) y).add h3).add (h2.const_mul (1 / 2)))
    refine h4.congr_fderiv ?_
    ext v
    simp only [sub_apply, add_apply, smul_apply, ContinuousLinearMap.flip_apply, zero_add,
      smul_eq_mul, hsymm v y]
    ring
  have hbound : ∀ y ∈ Metric.ball (0 : E) δ, ‖D y - D 0 - B y‖ ≤ ε * ‖y‖ := by
    intro y hy
    have h := (hball y hy).2
    simpa using h
  refine Metric.eventually_nhds_iff_ball.2 ⟨δ, hδ, fun x hx => ?_⟩
  have hxn : ‖x‖ < δ := by simpa using hx
  have hsub : Metric.closedBall (0 : E) ‖x‖ ⊆ Metric.ball (0 : E) δ :=
    Metric.closedBall_subset_ball hxn
  have hmv := (convex_closedBall (0 : E) ‖x‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun x => f x - (f 0 + D 0 x + 1 / 2 * B x x)) (f' := fun y => D y - D 0 - B y)
    (C := ε * ‖x‖) (x := 0) (y := x)
    (fun y hy => (hg y (hsub hy)).hasFDerivWithinAt)
    (fun y hy => (hbound y (hsub hy)).trans (mul_le_mul_of_nonneg_left (by simpa using hy) hε.le))
    (by simp) (by simp)
  simp only [map_zero, mul_zero, add_zero, sub_self, sub_zero] at hmv
  calc _ ≤ ε * ‖x‖ * ‖x‖ := hmv
    _ = ε * ‖‖x‖ ^ 2‖ := by simp [pow_two, mul_assoc]
theorem taylor_two_along_curve {f : E → ℝ} (hf : ContDiffAt ℝ ∞ f 0) {c : ℝ → E} {c₁ : E}
    (h0 : c 0 = 0) (hc : HasDerivAt c c₁ 0) :
    (fun t : ℝ => f (c t) - (f 0 + fderiv ℝ f 0 (c t) +
        t ^ 2 / 2 * fderiv ℝ (fderiv ℝ f) 0 c₁ c₁)) =o[𝓝 0] fun t : ℝ => t ^ 2 := by
  set B := fderiv ℝ (fderiv ℝ f) 0 with hBdef
  have hcont : Tendsto c (𝓝 0) (𝓝 0) := by
    have h := hc.continuousAt.tendsto
    rwa [h0] at h
  have hO : c =O[𝓝 0] fun t : ℝ => t := by
    have h := hc.isBigO_sub
    simpa [h0] using h
  set ϱ : ℝ → E := fun t => c t - t • c₁ with hϱdef
  have hϱ : ϱ =o[𝓝 0] fun t : ℝ => t := by
    have h := hasDerivAt_iff_isLittleO.1 hc
    simpa [h0, hϱdef] using h
  have h1 := (taylor_two_remainder_isLittleO hf).comp_tendsto hcont
  have hnorm : (fun t : ℝ => ‖c t‖ ^ 2) =O[𝓝 0] fun t : ℝ => t ^ 2 := by
    have h := hO.norm_left.pow 2
    exact h
  have h2 := h1.trans_isBigO hnorm
  have hb₁ : (fun t : ℝ => B (ϱ t) (c t)) =o[𝓝 0] fun t : ℝ => t ^ 2 := by
    have hprod : (fun t : ℝ => ‖ϱ t‖ * ‖c t‖) =o[𝓝 0] fun t : ℝ => t * t :=
      hϱ.norm_left.mul_isBigO hO.norm_left
    have hB : (fun t : ℝ => B (ϱ t) (c t)) =O[𝓝 0] fun t : ℝ => ‖ϱ t‖ * ‖c t‖ := by
      refine IsBigO.of_bound ‖B‖ (Eventually.of_forall fun t => ?_)
      have := B.le_opNorm₂ (ϱ t) (c t)
      simpa [abs_mul, mul_assoc] using this
    simpa [pow_two] using hB.trans_isLittleO hprod
  have hb₂ : (fun t : ℝ => t * B c₁ (ϱ t)) =o[𝓝 0] fun t : ℝ => t ^ 2 := by
    have hϱ' : (fun t : ℝ => B c₁ (ϱ t)) =o[𝓝 0] fun t : ℝ => t :=
      ((B c₁).isBigO_comp ϱ (𝓝 0)).trans_isLittleO hϱ
    simpa [pow_two] using (isBigO_refl (fun t : ℝ => t) (𝓝 0)).mul_isLittleO hϱ'
  have hb := (hb₁.add hb₂).const_mul_left (1 / 2 : ℝ)
  refine (h2.add hb).congr_left fun t => ?_
  have hct : c t = ϱ t + t • c₁ := by simp [hϱdef]
  have e₁ : B (c t) = B (ϱ t) + t • B c₁ := by
    rw [hct, map_add, map_smul]
  have e₂ : B c₁ (c t) = B c₁ (ϱ t) + t * B c₁ c₁ := by
    rw [hct, map_add, map_smul, smul_eq_mul]
  have hexp : B (c t) (c t) = B (ϱ t) (c t) + t * B c₁ (ϱ t) + t ^ 2 * B c₁ c₁ := by
    rw [e₁, add_apply, smul_apply, smul_eq_mul, e₂]
    ring
  have hB' : fderiv ℝ (fderiv ℝ f) 0 = B := rfl
  simp only [Function.comp, hB', hexp]
  ring
end TaylorTwo
section Reindexing
open Coordinates (ComplexCoordinates)
open Coordinates.ComplexCoordinates
variable {N M l : ℕ}
theorem isRealAnalyticIn_congr {D : Set (ComplexCoordinates N)}
    {g g' : ComplexCoordinates N → ComplexCoordinates l} (hg : IsRealAnalyticIn D g) (h : EqOn g g' D) :
    IsRealAnalyticIn D g' := by apply _root_.YangMills.Construction.IdentityExpChart.CoordinatesInChart.isRealAnalyticIn_congr <;> assumption
theorem isRealAnalyticIn_reindex (σ : Fin N ≃ Fin M) {T : Set (ComplexCoordinates M)}
    {g : ComplexCoordinates M → ComplexCoordinates l} (hg : IsRealAnalyticIn T g) :
    IsRealAnalyticIn ((fun z : ComplexCoordinates N => z ∘ σ.symm) ⁻¹' T)
      fun z => g (z ∘ σ.symm) := by
  have hcont : Continuous fun z : ComplexCoordinates N => z ∘ σ.symm :=
    continuous_pi fun j => continuous_apply _
  have hreal : ∀ z : ComplexCoordinates N, z ∈ realLocus N ↔ z ∘ σ.symm ∈ realLocus M := by
    intro z
    constructor
    · intro h j
      exact h _
    · intro h i
      simpa using h (σ i)
  refine ⟨?_, fun a ha => ?_⟩
  · obtain ⟨O, hO, hT⟩ := hg.1
    refine ⟨_, hO.preimage hcont, ?_⟩
    ext z
    simp only [mem_preimage, hT, mem_inter_iff, hreal z]
  · obtain ⟨c, hc⟩ := hg.2 _ ha
    let e : (Fin N → ℕ) ≃ (Fin M → ℕ) := Equiv.arrowCongr σ (Equiv.refl ℕ)
    refine ⟨fun m => c (e m), ?_⟩
    have ht : Tendsto (fun z : ComplexCoordinates N => z ∘ σ.symm) (𝓝[realLocus N] a)
        (𝓝[realLocus M] (a ∘ σ.symm)) :=
      tendsto_nhdsWithin_iff.2 ⟨(hcont.tendsto a).mono_left nhdsWithin_le_nhds,
        eventually_nhdsWithin_of_forall fun z hz => (hreal z).1 hz⟩
    filter_upwards [ht.eventually hc] with z hz
    have h := (e.hasSum_iff).2 hz
    have key : ∀ m : Fin N → ℕ, (∏ j, (z j - a j) ^ m j) =
        ∏ j, ((z ∘ σ.symm) j - (a ∘ σ.symm) j) ^ (e m j) :=
      fun m => (Equiv.prod_comp σ.symm fun i => (z i - a i) ^ m i).symm
    convert h using 1
    funext m
    simp only [Function.comp_apply]
    rw [key m]
    rfl
end Reindexing
section PauliCoordinates
open OneLoop (pauliCoordinateEquiv)
theorem pauliCoeff_pauliCombo (x : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ b, x b • ComplexMatrix2.pauliFamily b) = x a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
theorem pauliCombo_pauliCoeff {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
theorem realPauliCombo_mem_hermitianTraceless (r : Fin 3 → ℝ) :
    ∑ a, (r a : ℂ) • ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.PeriodicMatrices.real_pauli_sum_mem_hermitianTraceless <;> assumption
theorem pauliCoeff_im_eq_zero {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.hermitianTraceless)
    (a : Fin 3) : (pauliCoeff a X).im = 0 := by apply _root_.YangMills.SharedProofs.p23717 <;> assumption
theorem realPauliCombo_re_pauliCoeff {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    ∑ a, (((pauliCoeff a X).re : ℝ) : ℂ) • ComplexMatrix2.pauliFamily a = X := by
  conv_rhs => rw [← pauliCombo_pauliCoeff (show X ∈ ComplexMatrix2.traceless from hX.2)]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  exact Complex.ext (by simp) (by simp [pauliCoeff_im_eq_zero hX a])
def pauliCoordEquiv (σ : Type) :
    (Fin 3 × σ → ℝ) ≃ₗ[ℝ] Matrices.GroupLieProduct.hermitianTracelessFunctions σ where
  toFun r := ⟨fun s => ∑ a, (r (a, s) : ℂ) • ComplexMatrix2.pauliFamily a,
    fun s _ => realPauliCombo_mem_hermitianTraceless fun a => r (a, s)⟩
  map_add' r r' := by
    apply Subtype.ext
    funext s
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' t r := by
    apply Subtype.ext
    funext s
    ext i j
    simp [Finset.sum_apply, Matrix.sum_apply, Finset.mul_sum, mul_assoc]
  invFun X ι := (pauliCoeff ι.1 ((X : σ → ComplexMatrix2) ι.2)).re
  left_inv r := by
    funext ι
    have h := pauliCoeff_pauliCombo (fun a => (r (a, ι.2) : ℂ)) ι.1
    simp only [h, Complex.ofReal_re]
  right_inv X := by
    apply Subtype.ext
    funext s
    exact realPauliCombo_re_pauliCoeff (X.2 s (mem_univ s))
end PauliCoordinates
section EdgeForms
variable {L n k j : ℕ}
private theorem isPos_or_opposite_isPos (b : Edge L n k j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
private theorem opposite_not_isPos (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hj : j ≤ k) (b : Edge L n k j) (h : b.IsPositivelyOriented) :
    ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.SharedProofs.p24505 <;> assumption
private theorem edgeForm_apply_pos (w : PositiveEdge L n k j → ComplexMatrix2) {b : Edge L n k j}
    (h : b.IsPositivelyOriented) : edgeFormOfPositiveValues w b = w ⟨b, h⟩ := by
  simp [edgeFormOfPositiveValues, h]
private theorem edgeForm_apply_neg (w : PositiveEdge L n k j → ComplexMatrix2) {b : Edge L n k j}
    (h : ¬ b.IsPositivelyOriented) :
    edgeFormOfPositiveValues w b = -w ⟨b.opposite, (isPos_or_opposite_isPos b).resolve_left h⟩ := by
  simp [edgeFormOfPositiveValues, h, (isPos_or_opposite_isPos b).resolve_left h]
theorem edgeFormOfPositiveValues_restrict (B : edgeFormSpace L n k j) :
    edgeFormOfPositiveValues (restrictToPositiveEdges (B : Edge L n k j → ComplexMatrix2)) = B := by
  funext b
  by_cases h : b.IsPositivelyOriented
  · rw [edgeForm_apply_pos _ h]
    rfl
  · rw [edgeForm_apply_neg _ h]
    have hr : (B : Edge L n k j → ComplexMatrix2) b.opposite = -(B : Edge L n k j → ComplexMatrix2) b :=
      B.2.2 b
    show -(B : Edge L n k j → ComplexMatrix2) b.opposite = _
    rw [hr, neg_neg]
def edgeFormEquivPositive (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hj : j ≤ k) :
    edgeFormSpace L n k j ≃ₗ[ℝ]
      Matrices.GroupLieProduct.hermitianTracelessFunctions (PositiveEdge L n k j) where
  toFun B := ⟨restrictToPositiveEdges (B : Edge L n k j → ComplexMatrix2), fun b _ => B.2.1 b.1 b.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun w := ⟨edgeFormOfPositiveValues (w : PositiveEdge L n k j → ComplexMatrix2), by
    refine ⟨fun b hb => ?_, fun b => ?_⟩
    · rw [edgeForm_apply_pos _ hb]
      exact w.2 _ (mem_univ _)
    · by_cases h : b.IsPositivelyOriented
      · rw [edgeForm_apply_neg _ (opposite_not_isPos hL hn hj b h), edgeForm_apply_pos _ h]
        rfl
      · rw [edgeForm_apply_pos _ ((isPos_or_opposite_isPos b).resolve_left h), edgeForm_apply_neg _ h,
          neg_neg]⟩
  left_inv B := Subtype.ext (edgeFormOfPositiveValues_restrict B)
  right_inv w := by
    apply Subtype.ext
    funext p
    exact edgeForm_apply_pos _ p.2
def edgeFormPauliCoords (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) :
    edgeFormSpace L n k j ≃ₗ[ℝ] (Fin 3 × PositiveEdge L n k j → ℝ) :=
  (edgeFormEquivPositive hL hn hj).trans (pauliCoordEquiv _).symm
def fieldTripleEquiv (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) :
    FieldTriple L n k ≃ₗ[ℝ] (FieldTripleIndex L n k → ℝ) :=
  (((edgeFormPauliCoords hL hn (Nat.zero_le k)).prodCongr
      ((edgeFormPauliCoords hL hn (Nat.zero_le k)).prodCongr (edgeFormPauliCoords hL hn le_rfl))).trans
    ((LinearEquiv.refl ℝ _).prodCongr (LinearEquiv.sumArrowLequivProdArrow _ _ ℝ ℝ).symm)).trans
  (LinearEquiv.sumArrowLequivProdArrow _ _ ℝ ℝ).symm
theorem fieldTripleEquiv_apply (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (x : FieldTriple L n k) : fieldTripleEquiv hL hn x = fieldTripleCoords x := by
  funext i
  rcases i with i | i | i <;> rfl
end EdgeForms
section ChartAtIdentity
open Coordinates (ComplexCoordinates)
open Coordinates.ComplexCoordinates Matrices.GroupLieProduct Matrices.GroupLieProduct.Subspaces
open Matrices.GroupLieProduct.Subspaces.AnalyticCalculus
def pauliBasis (S : Type) [Fintype S] :
    Module.Basis (Fin (Fintype.card (Fin 3 × S))) ℝ (hermitianTracelessFunctions S) :=
  Module.Basis.ofEquivFun ((pauliCoordEquiv S).symm.trans
    (LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin (Fin 3 × S)).symm))
theorem sum_pauliBasis {S : Type} [Fintype S] (r : Fin (Fintype.card (Fin 3 × S)) → ℝ) :
    ∑ i, (r i : ℂ) • ((pauliBasis S i : hermitianTracelessFunctions S) : S → ComplexMatrix2) =
      (pauliCoordEquiv S (r ∘ Fintype.equivFin (Fin 3 × S)) : S → ComplexMatrix2) := by
  have h : ∑ i, r i • pauliBasis S i = pauliCoordEquiv S (r ∘ Fintype.equivFin (Fin 3 × S)) := by
    rw [← (pauliBasis S).equivFun_symm_apply r, pauliBasis,
      Module.Basis.equivFun_ofEquivFun]
    show pauliCoordEquiv S _ = _
    congr 1
  rw [← h]
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  funext s
  ext p q
  simp
def indexEnum (A : Type) [Fintype A] : IndexEnum A :=
  Fintype.equivFinOfCardEq (by simp [mul_comm])
variable {A B : Type}
abbrev TripleSlot (A B : Type) : Type := (Fin 3 × A) ⊕ (Fin 3 × A) ⊕ (Fin 3 × B)
def slotEquiv (A B : Type) : (Fin 3 × (A ⊕ B)) ⊕ (A × Fin 3) ≃ TripleSlot A B where
  toFun
    | .inl (a, .inl b) => .inr (.inl (a, b))
    | .inl (a, .inr c) => .inr (.inr (a, c))
    | .inr (b, a) => .inl (a, b)
  invFun
    | .inl (a, b) => .inr (b, a)
    | .inr (.inl (a, b)) => .inl (a, .inl b)
    | .inr (.inr (a, c)) => .inl (a, .inr c)
  left_inv := by rintro ((⟨a, b | c⟩) | ⟨b, a⟩) <;> rfl
  right_inv := by rintro (⟨a, b⟩ | ⟨a, b⟩ | ⟨a, c⟩) <;> rfl
variable [Fintype A] [Fintype B]
def slotEnum (A B : Type) [Fintype A] [Fintype B] :
    TripleSlot A B ≃ Fin (Fintype.card (Fin 3 × (A ⊕ B)) + 3 * Fintype.card A) :=
  (slotEquiv A B).symm.trans
    ((Equiv.sumCongr (Fintype.equivFin _) (indexEnum A)).trans finSumFinEquiv)
def paramOfSlots (y : TripleSlot A B → ℝ) : ParamSpace (Fintype.card (Fin 3 × (A ⊕ B))) A :=
  ofRealVector (y ∘ (slotEnum A B).symm)
theorem linearPart_paramOfSlots (y : TripleSlot A B → ℝ)
    (i : Fin (Fintype.card (Fin 3 × (A ⊕ B)))) :
    linearPart (paramOfSlots y) i =
      (y (slotEquiv A B (.inl ((Fintype.equivFin _).symm i))) : ℂ) := by
  simp [linearPart, paramOfSlots, ofRealVector, slotEnum]
theorem angularPart_paramOfSlots (y : TripleSlot A B → ℝ) (ρ : A) (a : Fin 3) :
    angularPart (indexEnum A) (paramOfSlots y) ρ a = (y (.inl (a, ρ)) : ℂ) := by
  simp [angularPart, paramOfSlots, ofRealVector, slotEnum, slotEquiv]
def expChartAtIdentity (A B : Type) [Fintype A] [Fintype B] :
    ParamSpace (Fintype.card (Fin 3 × (A ⊕ B))) A → A ⊕ (A ⊕ B) → ComplexMatrix2 :=
  basisExpChart (pauliBasis (A ⊕ B)) (indexEnum A) (ofParts (fun _ => 1) 0)
theorem groupComponent_expChartAtIdentity (y : TripleSlot A B → ℝ) (ρ : A) :
    groupComponent (expChartAtIdentity A B (paramOfSlots y)) ρ =
      ComplexMatrix2.matExp (Complex.I • ∑ a, (y (.inl (a, ρ)) : ℂ) • ComplexMatrix2.pauliFamily a) := by
  simp only [expChartAtIdentity, basisExpChart, groupComponent, ofParts, Sum.elim_inl, mul_one,
    pauliSum]
  simp only [angularPart_paramOfSlots]
  rfl
theorem algebraComponent_expChartAtIdentity (y : TripleSlot A B → ℝ) :
    algebraComponent (expChartAtIdentity A B (paramOfSlots y)) =
      (pauliCoordEquiv (A ⊕ B) (y ∘ slotEquiv A B ∘ Sum.inl) : A ⊕ B → ComplexMatrix2) := by
  have h := sum_pauliBasis (S := A ⊕ B)
    fun i => y (slotEquiv A B (.inl ((Fintype.equivFin _).symm i)))
  have e : (fun i => y (slotEquiv A B (.inl ((Fintype.equivFin (Fin 3 × (A ⊕ B))).symm i)))) ∘
      Fintype.equivFin (Fin 3 × (A ⊕ B)) = y ∘ slotEquiv A B ∘ Sum.inl := by
    funext ι
    simp
  rw [e] at h
  rw [← h]
  have h₂ : algebraComponent (expChartAtIdentity A B (paramOfSlots y)) =
      algebraComponent (ofParts (fun _ => 1) (0 : A ⊕ B → ComplexMatrix2) : A ⊕ (A ⊕ B) → ComplexMatrix2) +
        ∑ i, linearPart (paramOfSlots y) i •
          ((pauliBasis (A ⊕ B) i : hermitianTracelessFunctions (A ⊕ B)) : A ⊕ B → ComplexMatrix2) := rfl
  have h₃ : algebraComponent
      (ofParts (fun _ => 1) (0 : A ⊕ B → ComplexMatrix2) : A ⊕ (A ⊕ B) → ComplexMatrix2) = 0 :=
    rfl
  rw [h₂, h₃, zero_add]
  simp only [linearPart_paramOfSlots]
end ChartAtIdentity
section ChartReadsTriple
open Coordinates (ComplexCoordinates)
open Coordinates.ComplexCoordinates Matrices.GroupLieProduct Matrices.GroupLieProduct.Subspaces
open Matrices.GroupLieProduct.Subspaces.AnalyticCalculus
variable {L n k : ℕ}
private theorem matExp_mul_matExp_neg (Z : ComplexMatrix2) :
    ComplexMatrix2.matExp Z * ComplexMatrix2.matExp (-Z) = 1 := by apply _root_.YangMills.Construction.SpinHarmonics.matExp_mul_matExp_neg <;> assumption
section ProductPoints
variable [Fintype (PositiveEdge L n k 0)] [Fintype (PositiveEdge L n k k)]
def productPointOfTriple (x : FieldTriple L n k) : ProductPoint L n k :=
  expChartAtIdentity (PositiveEdge L n k 0) (PositiveEdge L n k k) (paramOfSlots (fieldTripleCoords x))
theorem fieldOfProductPoint_productPointOfTriple (x : FieldTriple L n k) :
    fieldOfProductPoint (productPointOfTriple x) =
      PeriodicLattice.expGaugeField (x.1 : Edge L n k 0 → ComplexMatrix2) := by
  have hg : ∀ ρ : PositiveEdge L n k 0, groupComponent (productPointOfTriple x) ρ =
      ComplexMatrix2.matExp (Complex.I • (x.1 : Edge L n k 0 → ComplexMatrix2) ρ.1) := by
    intro ρ
    have h := groupComponent_expChartAtIdentity (fieldTripleCoords x) ρ
    have e : ∑ a, ((fieldTripleCoords x (.inl (a, ρ)) : ℝ) : ℂ) • ComplexMatrix2.pauliFamily a =
        (x.1 : Edge L n k 0 → ComplexMatrix2) ρ.1 :=
      realPauliCombo_re_pauliCoeff (X := (x.1 : Edge L n k 0 → ComplexMatrix2) ρ.1) (x.1.2.1 ρ.1 ρ.2)
    rw [e] at h
    exact h
  funext b
  unfold fieldOfProductPoint fieldOfPositiveValues
  by_cases h : b.IsPositivelyOriented
  · rw [dif_pos h]
    exact hg ⟨b, h⟩
  · have h' := (isPos_or_opposite_isPos b).resolve_left h
    rw [dif_neg h, dif_pos h', hg ⟨b.opposite, h'⟩]
    show _ = ComplexMatrix2.matExp (Complex.I • (x.1 : Edge L n k 0 → ComplexMatrix2) b)
    have hr : (x.1 : Edge L n k 0 → ComplexMatrix2) b.opposite =
        -(x.1 : Edge L n k 0 → ComplexMatrix2) b := x.1.2.2 b
    rw [hr, smul_neg]
    exact Matrix.inv_eq_left_inv (matExp_mul_matExp_neg _)
theorem source_productPointOfTriple (x : FieldTriple L n k) :
    sourceOfProductPoint (productPointOfTriple x) = x.2.1 := by
  have h := algebraComponent_expChartAtIdentity (fieldTripleCoords x)
  have e : (fun b => algebraComponent (productPointOfTriple x) (.inl b)) =
      restrictToPositiveEdges (x.2.1 : Edge L n k 0 → ComplexMatrix2) := by
    funext b
    exact (congrFun h (.inl b)).trans (realPauliCombo_re_pauliCoeff (x.2.1.2.1 b.1 b.2))
  unfold sourceOfProductPoint
  rw [e]
  exact edgeFormOfPositiveValues_restrict x.2.1
theorem multiplier_productPointOfTriple (x : FieldTriple L n k) :
    multiplierOfProductPoint (productPointOfTriple x) = x.2.2 := by
  have h := algebraComponent_expChartAtIdentity (fieldTripleCoords x)
  have e : (fun c => algebraComponent (productPointOfTriple x) (.inr c)) =
      restrictToPositiveEdges (x.2.2 : Edge L n k k → ComplexMatrix2) := by
    funext c
    exact (congrFun h (.inr c)).trans (realPauliCombo_re_pauliCoeff (x.2.2.2.1 c.1 c.2))
  unfold multiplierOfProductPoint
  rw [e]
  exact edgeFormOfPositiveValues_restrict x.2.2
theorem backgroundFunctionalAt_productPointOfTriple (x : FieldTriple L n k) :
    backgroundFunctionalAt (productPointOfTriple x) = expChartFunctional x := by
  have hJ := source_productPointOfTriple x
  have hμ := multiplier_productPointOfTriple x
  have h : sourceOfProductPoint (productPointOfTriple x) ∈ edgeFormSpace L n k 0 ∧
      multiplierOfProductPoint (productPointOfTriple x) ∈ edgeFormSpace L n k k := by
    rw [hJ, hμ]
    exact ⟨x.2.1.2, x.2.2.2⟩
  unfold backgroundFunctionalAt expChartFunctional
  rw [dif_pos h, fieldOfProductPoint_productPointOfTriple]
  have e₁ : (⟨_, h.1⟩ : edgeFormSpace L n k 0) = x.2.1 := Subtype.ext hJ
  have e₂ : (⟨_, h.2⟩ : edgeFormSpace L n k k) = x.2.2 := Subtype.ext hμ
  rw [e₁, e₂]
theorem expChartFunctionalDefined_of_productPoint {x : FieldTriple L n k}
    (h : BackgroundFunctionalDefinedAt (productPointOfTriple x)) :
    ExpChartFunctionalDefined x := by
  obtain ⟨J, μ, hJ, hμ, hf⟩ := h
  have e₁ : J = x.2.1 := Subtype.ext (hJ.trans (source_productPointOfTriple x))
  have e₂ : μ = x.2.2 := Subtype.ext (hμ.trans (multiplier_productPointOfTriple x))
  rw [e₁, e₂, fieldOfProductPoint_productPointOfTriple] at hf
  exact hf
end ProductPoints
theorem expChartFunctionalInCoords_apply (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (x : FieldTriple L n k) :
    expChartFunctionalInCoords L n k (fieldTripleCoords x) = expChartFunctional x := by
  have hinj : Function.Injective
      (fieldTripleCoords : FieldTriple L n k → FieldTripleIndex L n k → ℝ) := by
    intro x x' h
    apply (fieldTripleEquiv hL hn).injective
    simpa [fieldTripleEquiv_apply] using h
  exact congrArg expChartFunctional (Function.leftInverse_invFun hinj x)
theorem fieldTripleCoords_symm (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (y : FieldTripleIndex L n k → ℝ) :
    fieldTripleCoords ((fieldTripleEquiv hL hn).symm y) = y := by
  rw [← fieldTripleEquiv_apply hL hn]
  simp
end ChartReadsTriple
section Expansion
open Coordinates (ComplexCoordinates)
open Coordinates.ComplexCoordinates Matrices.GroupLieProduct Matrices.GroupLieProduct.Subspaces
open Matrices.GroupLieProduct.Subspaces.AnalyticCalculus
variable {L n k : ℕ} [i₀ : Fintype (PositiveEdge L n k 0)] [i₁ : Fintype (PositiveEdge L n k k)]
theorem continuous_paramOfSlots {A B : Type} [Fintype A] [Fintype B] :
    Continuous (paramOfSlots : (TripleSlot A B → ℝ) → _) :=
  continuous_pi fun _ => Complex.continuous_ofReal.comp (continuous_apply _)
theorem continuous_fieldTripleCoords (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hfin : FiniteDimensional ℝ (FieldTriple L n k)) :
    Continuous (fieldTripleCoords : FieldTriple L n k → FieldTripleIndex L n k → ℝ) := by
  have h := (fieldTripleEquiv (k := k) hL hn).toLinearMap.continuous_of_finiteDimensional
  have e : ((fieldTripleEquiv hL hn).toLinearMap : FieldTriple L n k → _) =
      fieldTripleCoords := funext (fieldTripleEquiv_apply hL hn)
  rwa [e] at h
theorem fieldTripleCoords_zero (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) :
    fieldTripleCoords (0 : FieldTriple L n k) = 0 := by
  rw [← fieldTripleEquiv_apply hL hn, map_zero]
theorem exists_expChartNhd (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hfin : FiniteDimensional ℝ (FieldTriple L n k))
    (hrep : LogNormaliserRepresentation L n k)
    (hK : AnalyticCalculusStatement)
    (hR : LocalAnalyticity.LocalAnalyticityStatement) :
    ∃ 𝒲 : Set (FieldTriple L n k), IsExpChartNhd 𝒲 := by
  obtain ⟨f₀, f₁, 𝒲, hone, hformed, hra⟩ := hrep.analytic_near_identity
  obtain rfl : f₀ = i₀ := Subsingleton.elim _ _
  obtain rfl : f₁ = i₁ := Subsingleton.elim _ _
  have hw₀ : identityProductPoint L n k ∈
      subspaceTimesGroup (hermitianTracelessFunctions (SourceEdge L n k)) (PositiveEdge L n k 0) := by
    obtain ⟨O, -, hW⟩ := hra.1.2
    rw [hW] at hone
    exact hone.2
  obtain ⟨-, -, -, hν⟩ := hR (SourceEdge L n k) (PositiveEdge L n k 0) Empty Empty
    (hermitianTracelessFunctions _) (hermitianTracelessFunctions Empty) le_rfl le_rfl 𝒲 hra.1
  obtain ⟨hpt, -⟩ := hν (indexEnum _)
  obtain ⟨hcarry, hread⟩ := hpt _ (pauliBasis _) (identityProductPoint L n k) hw₀
  obtain ⟨-, T, hT, h0T, hsub⟩ := hcarry.2.2.2.2 hone
  obtain ⟨-, -, hreadf, -⟩ := hread hone T hT h0T hsub
  obtain ⟨-, -, hsmooth, hanal⟩ := hreadf 1 _ hra
  have hdom := (((hK (SourceEdge L n k) (PositiveEdge L n k 0) Empty Empty).2.2.2
    (hermitianTracelessFunctions _) (hermitianTracelessFunctions Empty) le_rfl le_rfl).2.2.2 _
      (pauliBasis _) (indexEnum _) (identityProductPoint L n k) hw₀).1.2.2.1
  obtain ⟨O₁, hO₁, hTeq⟩ := hT
  obtain ⟨O₂, hO₂, hDeq⟩ := hdom
  have hTmem : ∀ z, z ∈ T ↔ z ∈ O₁ ∩ O₂ ∧ z ∈ realLocus _ := by
    intro z
    rw [hTeq, hDeq]
    simp only [mem_inter_iff]
    tauto
  have hreal : ∀ y : FieldTripleIndex L n k → ℝ, paramOfSlots y ∈ realLocus _ :=
    fun y j => Complex.ofReal_im _
  have hVT : ∀ y : FieldTripleIndex L n k → ℝ, paramOfSlots y ∈ T ↔ paramOfSlots y ∈ O₁ ∩ O₂ :=
    fun y => by rw [hTmem]; simp [hreal y]
  have hVopen : IsOpen (paramOfSlots ⁻¹' T : Set (FieldTripleIndex L n k → ℝ)) := by
    have : (paramOfSlots ⁻¹' T : Set (FieldTripleIndex L n k → ℝ)) =
        paramOfSlots ⁻¹' (O₁ ∩ O₂) := by
      ext y
      exact hVT y
    rw [this]
    exact (hO₁.inter hO₂).preimage continuous_paramOfSlots
  have hcoords := continuous_fieldTripleCoords (k := k) hL hn hfin
  have hsurj : Function.Surjective
      (fieldTripleCoords : FieldTriple L n k → FieldTripleIndex L n k → ℝ) :=
    fun y => ⟨_, fieldTripleCoords_symm hL hn y⟩
  have hzero := fieldTripleCoords_zero (k := k) hL hn
  have hchart0 : (0 : ParamSpace (Fintype.card (Fin 3 × SourceEdge L n k)) (PositiveEdge L n k 0)) =
      paramOfSlots (0 : FieldTripleIndex L n k → ℝ) := by
    funext j
    simp [paramOfSlots, ofRealVector]
  have hinW : ∀ x : FieldTriple L n k, paramOfSlots (fieldTripleCoords x) ∈ T →
      productPointOfTriple x ∈ 𝒲 := fun x hx => hsub ⟨_, hx, rfl⟩
  refine ⟨fieldTripleCoords ⁻¹' (paramOfSlots ⁻¹' T), hVopen.preimage hcoords, ?_, ?_, ?_, ?_⟩
  · show paramOfSlots (fieldTripleCoords (0 : FieldTriple L n k)) ∈ T
    rw [hzero, ← hchart0]
    exact h0T
  · intro x hx
    exact expChartFunctionalDefined_of_productPoint (hformed _ (hinW x hx))
  · intro N e
    let σ : Fin N ≃ Fin _ :=
      e.symm.trans (slotEnum (PositiveEdge L n k 0) (PositiveEdge L n k k))
    have hσ : ∀ j, σ.symm j = e ((slotEnum _ _).symm j) := fun j => rfl
    have h := isRealAnalyticIn_reindex σ hanal
    have hpoint : ∀ z : ComplexCoordinates N, z ∘ σ.symm ∈ T →
        z ∘ σ.symm = paramOfSlots fun ι => (z (e ι)).re := by
      intro z hz
      funext j
      have hj := ((hTmem _).1 hz).2 j
      simp only [paramOfSlots, ofRealVector, Function.comp_apply]
      rw [← hσ]
      exact Complex.ext (by simp [hσ]) (by simpa using hj)
    have hset : coordImage e (fieldTripleCoords ⁻¹' (paramOfSlots ⁻¹' T)) =
        (fun z : ComplexCoordinates N => z ∘ σ.symm) ⁻¹' T := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        have : (fun i => (fieldTripleCoords x (e.symm i) : ℂ)) ∘ σ.symm =
            paramOfSlots (fieldTripleCoords x) := by
          funext j
          simp [hσ, paramOfSlots, ofRealVector]
        show _ ∘ σ.symm ∈ T
        rw [this]
        exact hx
      · intro hz
        have hz' : z ∘ σ.symm ∈ T := hz
        refine ⟨(fieldTripleEquiv hL hn).symm fun ι => (z (e ι)).re, ?_, ?_⟩
        · show paramOfSlots (fieldTripleCoords _) ∈ T
          rw [fieldTripleCoords_symm, ← hpoint z hz']
          exact hz'
        · funext i
          show ((fieldTripleCoords ((fieldTripleEquiv hL hn).symm fun ι => (z (e ι)).re)
            (e.symm i) : ℝ) : ℂ) = z i
          rw [fieldTripleCoords_symm]
          have hi : (z i).im = 0 := by simpa using ((hTmem _).1 hz').2 (σ i)
          exact Complex.ext (by simp) (by simp [hi])
    rw [hset]
    refine isRealAnalyticIn_congr h fun z hz => ?_
    have hz' : z ∘ σ.symm ∈ T := hz
    funext i
    have hx := fieldTripleCoords_symm hL hn fun ι => (z (e ι)).re
    set x := (fieldTripleEquiv hL hn).symm fun ι => (z (e ι)).re with hxdef
    show ((backgroundFunctionalAt (expChartAtIdentity _ _ (z ∘ σ.symm)) : ℝ) : ℂ) =
      ((expChartFunctionalInCoords L n k fun ι => (z (e ι)).re : ℝ) : ℂ)
    rw [hpoint z hz', ← hx, expChartFunctionalInCoords_apply hL hn]
    exact congrArg _ (backgroundFunctionalAt_productPointOfTriple x)
  · rw [image_preimage_eq _ hsurj]
    have hu : ContDiff ℝ ∞ fun y : FieldTripleIndex L n k → ℝ =>
        y ∘ (slotEnum (PositiveEdge L n k 0) (PositiveEdge L n k k)).symm :=
      contDiff_pi.2 fun j => contDiff_apply ℝ ℝ _
    have h₁ := hsmooth.comp hu.contDiffOn (s := paramOfSlots ⁻¹' T) fun y hy => hy
    have h₂ := Complex.reCLM.contDiff.comp_contDiffOn
      ((contDiff_apply ℝ ℂ (0 : Fin 1)).comp_contDiffOn h₁)
    refine h₂.congr fun y hy => ?_
    have hx := fieldTripleCoords_symm hL hn y
    set x := (fieldTripleEquiv hL hn).symm y with hxdef
    rw [← hx, expChartFunctionalInCoords_apply hL hn, ← backgroundFunctionalAt_productPointOfTriple]
    simp [productPointOfTriple, paramOfSlots]
    rfl
theorem expChartFunctionalInCoords_zero (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) :
    expChartFunctionalInCoords L n k 0 = backgroundFunctional (trivialField L n k 0) 0 0 := by
  rw [← fieldTripleCoords_zero (k := k) hL hn, expChartFunctionalInCoords_apply hL hn]
  have h : PeriodicLattice.expGaugeField ((0 : FieldTriple L n k).1 : Edge L n k 0 → ComplexMatrix2) =
      trivialField L n k 0 := by
    funext b
    simp [PeriodicLattice.expGaugeField, ComplexMatrix2.matExp]
  unfold expChartFunctional
  rw [h]
  rfl
theorem expChartFunctionalExpansion_holds (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hfin : FiniteDimensional ℝ (FieldTriple L n k))
    (hrep : LogNormaliserRepresentation L n k)
    (hK : AnalyticCalculusStatement)
    (hR : LocalAnalyticity.LocalAnalyticityStatement) :
    ExpChartFunctionalExpansion L n k := by
  obtain ⟨𝒲, h𝒲⟩ := exists_expChartNhd hL hn hfin hrep hK hR
  have hback : Continuous (fieldTripleEquiv (k := k) hL hn).symm :=
    (fieldTripleEquiv (k := k) hL hn).symm.toLinearMap.continuous_of_finiteDimensional
  have hzero := fieldTripleCoords_zero (k := k) hL hn
  have hleft : ∀ x : FieldTriple L n k,
      (fieldTripleEquiv hL hn).symm (fieldTripleCoords x) = x := by
    intro x
    rw [← fieldTripleEquiv_apply hL hn]
    simp
  have himage : IsOpen (fieldTripleCoords '' 𝒲) := by
    have e : fieldTripleCoords '' 𝒲 = (fieldTripleEquiv hL hn).symm ⁻¹' 𝒲 := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa [hleft x] using hx
      · intro hy
        exact ⟨_, hy, fieldTripleCoords_symm hL hn y⟩
    rw [e]
    exact h𝒲.1.preimage hback
  have hf : ContDiffAt ℝ ∞ (expChartFunctionalInCoords L n k) 0 :=
    h𝒲.2.2.2.2.contDiffAt (himage.mem_nhds ⟨0, h𝒲.2.1, hzero⟩)
  have hadd : ∀ x x' : FieldTriple L n k, fieldTripleCoords (x + x') =
      fieldTripleCoords x + fieldTripleCoords x' := by
    intro x x'
    simp only [← fieldTripleEquiv_apply hL hn, map_add]
  have hsmul : ∀ (t : ℝ) (x : FieldTriple L n k), fieldTripleCoords (t • x) =
      t • fieldTripleCoords x := by
    intro t x
    simp only [← fieldTripleEquiv_apply hL hn, map_smul]
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := ENat.LEInfty.out
  refine ⟨⟨𝒲, h𝒲⟩, ?_, ?_, ?_⟩
  · refine ⟨LinearMap.mk₂ ℝ expChartSecondDeriv ?_ ?_ ?_ ?_,
      fun x x' => rfl, fun x x' => ?_⟩
    · intro x x' x''
      simp [expChartSecondDeriv, hadd]
    · intro t x x'
      simp [expChartSecondDeriv, hsmul]
    · intro x x' x''
      simp [expChartSecondDeriv, hadd]
    · intro t x x'
      simp [expChartSecondDeriv, hsmul]
    · exact hf.isSymmSndFDerivAt (by simpa using h2) _ _
  · rintro 𝒲₁ h₁ γ γ₁ ⟨hγ₀, hγ⟩
    have hc : Tendsto (fun t => fieldTripleCoords (γ t)) (𝓝 0)
        (𝓝 (fieldTripleCoords (γ 0))) := hγ.continuousAt.tendsto
    have hγc := (hback.tendsto _).comp hc
    simp only [Function.comp_def, hleft] at hγc
    rw [hγ₀] at hγc
    exact hγc (h₁.1.mem_nhds h₁.2.1)
  · rintro γ γ₁ ⟨hγ₀, hγ⟩
    have h := taylor_two_along_curve hf (c := fun t => fieldTripleCoords (γ t))
      (c₁ := fieldTripleCoords γ₁) (by simp only [hγ₀, hzero]) hγ
    refine h.congr_left fun t => ?_
    rw [expChartFunctionalInCoords_apply hL hn, expChartFunctionalInCoords_zero hL hn]
    rfl
end Expansion
end ExpChartFunctionalProof
theorem expChartFunctionalClaim_holds
    (hrep : LogNormaliserRepresentationHolds)
    (hG : FiniteSideFormSpaces)
    (hK : Matrices.GroupLieProduct.Subspaces.AnalyticCalculus.AnalyticCalculusStatement)
    (hR : Matrices.GroupLieProduct.Subspaces.LocalAnalyticity.LocalAnalyticityStatement) :
    ExpChartFunctionalClaim := by
  intro L n k hL hn hk
  haveI h₀ := (hG L n k 0 hL hn (Nat.zero_le k)).2.1
  haveI h₁ := (hG L n k k hL hn le_rfl).2.1
  have hfin : FiniteDimensional ℝ (FieldTriple L n k) := inferInstance
  refine ⟨hfin, ?_⟩
  intro _ _
  exact ExpChartFunctionalProof.expChartFunctionalExpansion_holds hL hn hfin (hrep L n k hL hn hk)
    hK hR
end YangMills.Construction.Tower
end
