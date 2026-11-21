import YangMills.Construction.Lattice.BondEndpointsAndFiniteness
import YangMills.Construction.Lattice.BondOrientationDichotomy
import YangMills.Construction.Lattice.CovarianceOfTheRegionHessianAtComplexConfigurations
import YangMills.Construction.Lattice.TwistedMapsAndHessiansUnderIsometries
import YangMills.Construction.Matrices.RepresentationsFieldsAndSmoothFunctionsOnG
import YangMills.Construction.Towers.ConfigurationsOnFiniteBondSetsProof
import YangMills.Construction.Towers.TheRemainderOfTheFreePolarisationProof
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice
namespace HessianHolomorphy
open ComplexTransport Matrices Coordinates SpinHarmonics
private theorem deriv_ofReal_of_hasDerivAt {f : ℂ → ℂ} {c : ℂ} (hf : HasDerivAt f c 0) :
    deriv (fun t : ℝ => f t) 0 = c := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundJets.FreePolarizationRemainder.deriv_ofReal_of_hasDerivAt <;> assumption
private theorem exists_contDiff_mixedDeriv {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P]
    (F : ℂ × ℂ × P → ℂ) (hF : ContDiff ℂ 3 F) :
    ∃ G : P → ℂ, ContDiff ℂ 1 G ∧ ∀ x,
      deriv (fun t : ℝ => deriv (fun t' : ℝ => F ((t : ℂ), (t' : ℂ), x)) 0) 0 = G x := by
  let D₁ : ℂ × ℂ × P → ℂ := fun y => fderiv ℂ F y ((0 : ℂ), (1 : ℂ), (0 : P))
  have hD₁ : ContDiff ℂ 2 D₁ :=
    (hF.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const
  let D₂ : ℂ × ℂ × P → ℂ := fun y => fderiv ℂ D₁ y ((1 : ℂ), (0 : ℂ), (0 : P))
  have hD₂ : ContDiff ℂ 1 D₂ :=
    (hD₁.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  refine ⟨fun x => D₂ (0, 0, x),
    hD₂.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)), fun x => ?_⟩
  have hin : ∀ t : ℝ, deriv (fun t' : ℝ => F ((t : ℂ), (t' : ℂ), x)) 0 = D₁ ((t : ℂ), 0, x) := by
    intro t
    have hc : HasDerivAt (fun z : ℂ => ((t : ℂ), z, x)) ((0 : ℂ), (1 : ℂ), (0 : P)) 0 :=
      (hasDerivAt_const _ _).prodMk ((hasDerivAt_id _).prodMk (hasDerivAt_const _ _))
    have hd := ((hF.differentiable (by norm_num)) ((t : ℂ), (0 : ℂ), x)).hasFDerivAt
    exact deriv_ofReal_of_hasDerivAt (f := fun z : ℂ => F ((t : ℂ), z, x))
      (hd.comp_hasDerivAt (0 : ℂ) hc)
  simp only [hin]
  have hc : HasDerivAt (fun z : ℂ => (z, (0 : ℂ), x)) ((1 : ℂ), (0 : ℂ), (0 : P)) 0 :=
    (hasDerivAt_id _).prodMk ((hasDerivAt_const _ _).prodMk (hasDerivAt_const _ _))
  have hd := ((hD₁.differentiable (by norm_num)) ((0 : ℂ), (0 : ℂ), x)).hasFDerivAt
  have hcomp := hd.comp_hasDerivAt (0 : ℂ) hc
  exact deriv_ofReal_of_hasDerivAt (f := fun z : ℂ => D₁ (z, 0, x)) hcomp
section Smooth
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {n : WithTop ℕ∞}
private theorem contDiff_matExp {f : E → ComplexMatrix2} (hf : ContDiff ℂ n f) :
    ContDiff ℂ n fun x => ComplexMatrix2.matExp (f x) := by
  have hexp : ContDiff ℂ n (NormedSpace.exp : ComplexMatrix2 → ComplexMatrix2) :=
    contDiff_iff_contDiffAt.2 fun y => (NormedSpace.exp_analytic (𝕂 := ℂ) y).contDiffAt
  exact hexp.comp hf
private def adjugateₗ : ComplexMatrix2 →ₗ[ℂ] ComplexMatrix2 where
  toFun := Matrix.adjugate
  map_add' M N := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two] <;> ring
  map_smul' c M := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two]
private theorem contDiff_adjugate {f : E → ComplexMatrix2} (hf : ContDiff ℂ n f) :
    ContDiff ℂ n fun x => Matrix.adjugate (f x) :=
  (LinearMap.toContinuousLinearMap adjugateₗ).contDiff.comp hf
private theorem contDiff_fullTrace {f : E → ComplexMatrix2} (hf : ContDiff ℂ n f) :
    ContDiff ℂ n fun x => ComplexMatrix2.fullTrace (f x) :=
  (LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin 2) ℂ ℂ)).contDiff.comp hf
end Smooth
section Values
variable {L m : ℕ} {j : ℤ}
private def adjugateField (S : Set (Bond L m j)) (v : PositiveBondOf S → ComplexMatrix2) :
    Bond L m j → ComplexMatrix2 :=
  open Classical in
  fun b => if h : b ∈ S ∧ b.IsPositivelyOriented then v ⟨b, h⟩
    else if h' : b.opposite ∈ S ∧ b.opposite.IsPositivelyOriented then
      Matrix.adjugate (v ⟨b.opposite, h'⟩)
    else 1
private theorem gaugeField_apply_pos {S : Set (Bond L m j)} (v : PositiveBondOf S → ComplexMatrix2)
    {b : Bond L m j} (h : b ∈ S ∧ b.IsPositivelyOriented) :
    gaugeFieldOfPositiveValues S v b = v ⟨b, h⟩ := by
  simp only [gaugeFieldOfPositiveValues, dif_pos h]
private theorem gaugeField_apply_opposite {S : Set (Bond L m j)}
    (v : PositiveBondOf S → ComplexMatrix2) {b : Bond L m j} (h : ¬(b ∈ S ∧ b.IsPositivelyOriented))
    (h' : b.opposite ∈ S ∧ b.opposite.IsPositivelyOriented) :
    gaugeFieldOfPositiveValues S v b = (v ⟨b.opposite, h'⟩)⁻¹ := by
  simp only [gaugeFieldOfPositiveValues, dif_neg h, dif_pos h']
private theorem bondForm_apply_pos {S : Set (Bond L m j)} (a : PositiveBondOf S → ComplexMatrix2)
    {b : Bond L m j} (h : b ∈ S ∧ b.IsPositivelyOriented) :
    bondFormOfPositiveValues S a b = a ⟨b, h⟩ := by
  simp only [bondFormOfPositiveValues, dif_pos h]
private theorem bondForm_apply_opposite {S : Set (Bond L m j)}
    (a : PositiveBondOf S → ComplexMatrix2) {b : Bond L m j} (h : ¬(b ∈ S ∧ b.IsPositivelyOriented))
    (h' : b.opposite ∈ S ∧ b.opposite.IsPositivelyOriented) :
    bondFormOfPositiveValues S a b = -a ⟨b.opposite, h'⟩ := by
  simp only [bondFormOfPositiveValues, dif_neg h, dif_pos h']
private theorem bondForm_apply_of_not_mem {S : Set (Bond L m j)}
    (a : PositiveBondOf S → ComplexMatrix2) (hS : IsReversalClosed S) {b : Bond L m j}
    (hb : b ∉ S) : bondFormOfPositiveValues S a b = 0 := by
  have h : ¬(b ∈ S ∧ b.IsPositivelyOriented) := fun x => hb x.1
  have h' : ¬(b.opposite ∈ S ∧ b.opposite.IsPositivelyOriented) := fun x => hb (hS _ x.1)
  simp only [bondFormOfPositiveValues, dif_neg h, dif_neg h']
private theorem det_gaugeField (S : Set (Bond L m j)) {v : PositiveBondOf S → ComplexMatrix2}
    (hv : ∀ i, (v i).det = 1) (b : Bond L m j) : (gaugeFieldOfPositiveValues S v b).det = 1 := by
  simp only [gaugeFieldOfPositiveValues]
  split_ifs with h h'
  · exact hv _
  · rw [Matrix.det_nonsing_inv, hv]
    simp
  · simp
private theorem inv_eq_adjugate_of_det_eq_one {M : ComplexMatrix2} (hM : M.det = 1) :
    M⁻¹ = Matrix.adjugate M := by apply _root_.YangMills.SharedProofs.p104891 <;> assumption
private theorem gaugeField_eq_adjugateField (S : Set (Bond L m j))
    {v : PositiveBondOf S → ComplexMatrix2} (hv : ∀ i, (v i).det = 1) :
    gaugeFieldOfPositiveValues S v = adjugateField S v := by
  funext b
  simp only [gaugeFieldOfPositiveValues, adjugateField]
  split_ifs with h h'
  · rfl
  · exact inv_eq_adjugate_of_det_eq_one (hv _)
  · rfl
private theorem isGaugeField_of_values {S : Set (Bond L m j)}
    (hX : ∀ b : Bond L m j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (hS : IsReversalClosed S) {v : PositiveBondOf S → ComplexMatrix2} (hv : ∀ i, (v i).det = 1) :
    IsGaugeField complexGaugeGroup S (gaugeFieldOfPositiveValues S v) := by
  refine ⟨fun b _ => det_gaugeField S hv b, fun b hb => ?_⟩
  have hob := hS b hb
  rcases hX b with ⟨hp, hn⟩ | ⟨hp, hn⟩
  · have e₁ := gaugeField_apply_pos v (b := b) ⟨hb, hp⟩
    have e₂ := gaugeField_apply_opposite v (b := b.opposite) (fun h => hn h.2) ⟨hb, hp⟩
    exact e₂.trans (congrArg (fun M : ComplexMatrix2 => M⁻¹) e₁.symm)
  · rw [gaugeField_apply_pos v (b := b.opposite) ⟨hob, hp⟩,
      gaugeField_apply_opposite v (b := b) (fun h => hn h.2) ⟨hob, hp⟩,
      Matrix.nonsing_inv_nonsing_inv _ (by rw [hv]; exact isUnit_one)]
private theorem bondForm_mem_traceless (S : Set (Bond L m j)) {a : PositiveBondOf S → ComplexMatrix2}
    (ha : ∀ i, a i ∈ ComplexMatrix2.traceless) (b : Bond L m j) :
    bondFormOfPositiveValues S a b ∈ ComplexMatrix2.traceless := by
  simp only [bondFormOfPositiveValues]
  split_ifs with h h'
  · exact ha _
  · exact ComplexMatrix2.traceless.neg_mem (ha _)
  · exact ComplexMatrix2.traceless.zero_mem
private theorem isSupportedOn_of_values {S : Set (Bond L m j)}
    (hX : ∀ b : Bond L m j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (hS : IsReversalClosed S) {a : PositiveBondOf S → ComplexMatrix2}
    (ha : ∀ i, a i ∈ ComplexMatrix2.traceless) :
    IsComplexBondFormSupportedOn S (bondFormOfPositiveValues S a) := by
  refine ⟨⟨fun b _ => bondForm_mem_traceless S ha b, fun b => ?_⟩, ?_⟩
  · by_cases hb : b ∈ S
    · have hob := hS b hb
      rcases hX b with ⟨hp, hn⟩ | ⟨hp, hn⟩
      · have e₁ := bondForm_apply_pos a (b := b) ⟨hb, hp⟩
        have e₂ := bondForm_apply_opposite a (b := b.opposite) (fun h => hn h.2) ⟨hb, hp⟩
        exact e₂.trans (congrArg (fun M : ComplexMatrix2 => -M) e₁.symm)
      · rw [bondForm_apply_pos a (b := b.opposite) ⟨hob, hp⟩,
          bondForm_apply_opposite a (b := b) (fun h => hn h.2) ⟨hob, hp⟩, neg_neg]
    · have hob : b.opposite ∉ S := fun x => hb (hS _ x)
      rw [bondForm_apply_of_not_mem a hS hb, bondForm_apply_of_not_mem a hS hob, neg_zero]
  · funext b
    by_cases hb : b ∈ S
    · exact Set.indicator_of_mem hb _
    · rw [Set.indicator_of_notMem hb, bondForm_apply_of_not_mem a hS hb]
section Smooth
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {n : WithTop ℕ∞}
private theorem contDiff_adjugateField (S : Set (Bond L m j))
    {v : E → PositiveBondOf S → ComplexMatrix2} (hv : ∀ i, ContDiff ℂ n fun x => v x i)
    (b : Bond L m j) : ContDiff ℂ n fun x => adjugateField S (v x) b := by
  simp only [adjugateField]
  split_ifs with h h'
  · exact hv _
  · exact contDiff_adjugate (hv _)
  · exact contDiff_const
private theorem contDiff_bondForm (S : Set (Bond L m j))
    {a : E → PositiveBondOf S → ComplexMatrix2} (ha : ∀ i, ContDiff ℂ n fun x => a x i)
    (b : Bond L m j) : ContDiff ℂ n fun x => bondFormOfPositiveValues S (a x) b := by
  simp only [bondFormOfPositiveValues]
  split_ifs with h h'
  · exact ha _
  · exact (ha _).neg
  · exact contDiff_const
end Smooth
private def twistedFactor (η : ℂ) (U A B : Bond L m j → ComplexMatrix2) (t t' : ℂ)
    (b : Bond L m j) : ComplexMatrix2 :=
  ComplexMatrix2.matExp (Complex.I • (η • (t • A b + t' • B b))) * U b
private def adjugateTwist (η : ℂ) (U A B : Bond L m j → ComplexMatrix2) (t t' : ℂ) :
    Bond L m j → ComplexMatrix2 :=
  open Classical in
  fun b => if b.IsPositivelyOriented then twistedFactor η U A B t t' b
    else Matrix.adjugate (twistedFactor η U A B t t' b.opposite)
private theorem det_twistedFactor (η : ℂ) {U A B : Bond L m j → ComplexMatrix2}
    (hU : ∀ b, (U b).det = 1) (hA : ∀ b, A b ∈ ComplexMatrix2.traceless)
    (hB : ∀ b, B b ∈ ComplexMatrix2.traceless) (t t' : ℂ) (b : Bond L m j) :
    (twistedFactor η U A B t t' b).det = 1 := by
  have hz : Complex.I • (η • (t • A b + t' • B b)) ∈ ComplexMatrix2.traceless :=
    ComplexMatrix2.traceless.smul_mem _ (ComplexMatrix2.traceless.smul_mem _
      (ComplexMatrix2.traceless.add_mem (ComplexMatrix2.traceless.smul_mem _ (hA b))
        (ComplexMatrix2.traceless.smul_mem _ (hB b))))
  rw [twistedFactor, Matrix.det_mul, det_matExp_of_trace_eq_zero hz, hU, one_mul]
private theorem bareTwist_eq_adjugateTwist {K : ℕ} (k : ℕ) {U A B : BondAtLevel L m K 0 → ComplexMatrix2}
    (hU : ∀ b, (U b).det = 1) (hA : ∀ b, A b ∈ ComplexMatrix2.traceless)
    (hB : ∀ b, B b ∈ ComplexMatrix2.traceless) (t t' : ℂ) :
    bareTwist k (t • A + t' • B) U =
      adjugateTwist ((finestMeshInLevelUnits L k : ℝ) : ℂ) U A B t t' := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp only [bareTwist, expTwist, adjugateTwist, twistedFactor, if_pos hb, Pi.add_apply,
      Pi.smul_apply]
  · have hd := det_twistedFactor ((finestMeshInLevelUnits L k : ℝ) : ℂ) hU hA hB t t' b.opposite
    simp only [adjugateTwist, if_neg hb]
    rw [← inv_eq_adjugate_of_det_eq_one hd]
    simp only [bareTwist, expTwist, twistedFactor, if_neg hb, Pi.add_apply, Pi.smul_apply]
section Smooth
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {n : WithTop ℕ∞}
private theorem contDiff_adjugateTwist (η : ℂ) {U A B : E → Bond L m j → ComplexMatrix2}
    {t t' : E → ℂ} (hU : ∀ b, ContDiff ℂ n fun x => U x b) (hA : ∀ b, ContDiff ℂ n fun x => A x b)
    (hB : ∀ b, ContDiff ℂ n fun x => B x b) (ht : ContDiff ℂ n t) (ht' : ContDiff ℂ n t')
    (b : Bond L m j) :
    ContDiff ℂ n fun x => adjugateTwist η (U x) (A x) (B x) (t x) (t' x) b := by
  have hf : ∀ b, ContDiff ℂ n fun x => twistedFactor η (U x) (A x) (B x) (t x) (t' x) b :=
    fun b => (contDiff_matExp (((((ht.smul (hA b)).add (ht'.smul (hB b)))).const_smul η).const_smul
      Complex.I)).mul (hU b)
  by_cases hb : b.IsPositivelyOriented
  · simp only [adjugateTwist, if_pos hb]
    exact hf b
  · simp only [adjugateTwist, if_neg hb]
    exact contDiff_adjugate (hf _)
private theorem contDiff_pathHolonomy {V : E → Bond L m j → ComplexMatrix2}
    (hV : ∀ b, ContDiff ℂ n fun x => V x b) (γ : List (Bond L m j)) :
    ContDiff ℂ n fun x => pathHolonomy (V x) γ := by
  induction γ with
  | nil => simpa [pathHolonomy] using contDiff_const
  | cons b γ ih =>
    simp only [pathHolonomy, List.map_cons, List.prod_cons]
    exact (hV b).mul ih
private theorem contDiff_interiorEnergy [Finite (Plaquette L m j)] (Ω : Set (FourTorus L m))
    {V : E → Bond L m j → ComplexMatrix2} (hV : ∀ b, ContDiff ℂ n fun x => V x b) :
    ContDiff ℂ n fun x => interiorEnergy Ω (V x) := by
  simp only [interiorEnergy]
  simp only [finsum_mem_eq_finite_toFinset_sum _
    (Set.toFinite (plaquettesInside Ω : Set (Plaquette L m j)))]
  refine ContDiff.sum fun P _ => ?_
  simp only [plaquetteEnergy, plaquetteHolonomy]
  exact contDiff_const.sub (contDiff_const.mul (contDiff_fullTrace (contDiff_pathHolonomy hV _)))
end Smooth
end Values
section Chart
variable {ι κ : Type}
private theorem expChartAt_mem {x A : ι ⊕ κ → ComplexMatrix2} (hx : x ∈ GroupLieProduct ι κ)
    (hA : A ∈ GroupLieProduct.tracelessPi (ι ⊕ κ)) :
    GroupLieProduct.expChartAt x A ∈ GroupLieProduct ι κ := by
  rintro (i | k)
  · have e₁ : (x (.inl i)).det = 1 := hx (.inl i)
    have e₂ : ComplexMatrix2.fullTrace (A (.inl i)) = 0 := hA (.inl i)
    change (ComplexMatrix2.matExp (A (.inl i)) * x (.inl i)).det = 1
    rw [Matrix.det_mul, det_matExp_of_trace_eq_zero e₂, e₁, one_mul]
  · have e₁ : x (.inr k) ∈ ComplexMatrix2.traceless := hx (.inr k)
    have e₂ : A (.inr k) ∈ ComplexMatrix2.traceless := hA (.inr k)
    exact ComplexMatrix2.traceless.add_mem e₁ e₂
variable [Fintype ι] [Fintype κ]
private theorem contDiff_expChartAt (x : ι ⊕ κ → ComplexMatrix2) {N : ℕ}
    {f : ComplexCoordinates N → ι ⊕ κ → ComplexMatrix2} (hf : ContDiff ℂ 1 f) :
    ContDiff ℂ 1 fun w => GroupLieProduct.expChartAt x (f w) := by
  refine contDiff_pi.2 ?_
  rintro (i | k)
  · exact (contDiff_matExp ((contDiff_pi.1 hf) (.inl i))).mul contDiff_const
  · exact contDiff_const.add ((contDiff_pi.1 hf) (.inr k))
private theorem contDiff_tupleOfCoords (e : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (τ : Type) [Fintype τ] (ν : τ ≃ Fin (Fintype.card τ)) :
    ContDiff ℂ 1 (GroupLieProduct.tupleOfCoords e ν) := by
  refine contDiff_pi.2 fun i => ?_
  simp only [GroupLieProduct.tupleOfCoords, ComplexCoordinates.tracelessTuple]
  exact ContDiff.sum fun c _ => (contDiff_apply ℂ ℂ _).smul contDiff_const
private theorem isHolomorphicToCoords_of_eqOn (e : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (g G : (ι ⊕ κ → ComplexMatrix2) → ℂ) (hG : ContDiff ℂ 1 G)
    (hgG : ∀ x ∈ GroupLieProduct ι κ, g x = G x) :
    GroupLieProduct.IsHolomorphicToCoords e (Equiv.funUnique (Fin 1) ℂ).symm
      (GroupLieProduct ι κ) g := by
  have hu : ∀ (z : ℂ) (i : Fin 1), (Equiv.funUnique (Fin 1) ℂ).symm z i = z := fun z i => by
    rw [Subsingleton.elim i default]
    exact (Equiv.funUnique (Fin 1) ℂ).apply_symm_apply z
  refine ⟨⟨univ, isOpen_univ, by simp⟩, ?_, fun x hx =>
    ⟨GroupLieProduct.tracelessPi _, fun _ => ComplexMatrix2.traceless.zero_mem,
      fun A hA => expChartAt_mem hx hA,
      ⟨subset_rfl, fun A _ => ⟨1, one_pos, fun B hB _ => hB⟩⟩, fun ν => ?_⟩⟩
  · have hc : Continuous fun x => (Equiv.funUnique (Fin 1) ℂ).symm (G x) :=
      continuous_pi fun i => by simpa only [hu] using hG.continuous
    exact hc.continuousOn.congr fun x hx => by
      simp only [Function.comp, hgG x hx]
  · have htup : ∀ w, GroupLieProduct.tupleOfCoords e ν w ∈
        GroupLieProduct.tracelessPi (ι ⊕ κ) := fun w i =>
      Submodule.sum_mem _ fun c _ => ComplexMatrix2.traceless.smul_mem _ (e c).2
    have hF : ContDiff ℂ 1 fun w => G (GroupLieProduct.expChartAt x
        (GroupLieProduct.tupleOfCoords e ν w)) :=
      hG.comp (contDiff_expChartAt x (contDiff_tupleOfCoords e _ ν))
    have heq : ∀ w, ((Equiv.funUnique (Fin 1) ℂ).symm ∘
        (g ∘ GroupLieProduct.expChartAt x) ∘ GroupLieProduct.tupleOfCoords e ν) w =
        (Equiv.funUnique (Fin 1) ℂ).symm (G (GroupLieProduct.expChartAt x
          (GroupLieProduct.tupleOfCoords e ν w))) := fun w => by
      simp only [Function.comp, hgG _ (expChartAt_mem hx (htup w))]
    refine ⟨?_, ?_, ?_⟩
    · rw [show GroupLieProduct.tupleOfCoords e ν ⁻¹'
        GroupLieProduct.tracelessPi (ι ⊕ κ) = univ from eq_univ_of_forall htup]
      exact isOpen_univ
    · have hc : Continuous fun w => (Equiv.funUnique (Fin 1) ℂ).symm
          (G (GroupLieProduct.expChartAt x (GroupLieProduct.tupleOfCoords e ν w))) :=
        continuous_pi fun i => by simpa only [hu] using hF.continuous
      exact hc.continuousOn.congr fun w _ => heq w
    · intro a _ l
      refine Filter.Eventually.of_forall fun ζ => ?_
      simp only [heq]
      refine differentiableAt_pi.2 fun i => ?_
      simp only [hu]
      exact ((hF.differentiable (by norm_num)).comp
        ((differentiable_const a).add
          (differentiable_id.smul_const (ComplexCoordinates.stdBasisVector l)))).differentiableAt
end Chart
section Form
variable {L m K : ℕ}
private theorem exists_contDiff_eqOn_hessian {S : Set (BondAtLevel L m K 0)}
    [Fintype (PositiveBondOf S)] [Finite (Plaquette L m (levelDepth K 0))]
    (k : ℕ) (Ω : Set (FourTorus L m)) :
    ∃ G : (PositiveBondOf S ⊕ (PositiveBondOf S ⊕ PositiveBondOf S) → ComplexMatrix2) → ℂ,
      ContDiff ℂ 1 G ∧
      ∀ x ∈ GroupLieProduct (PositiveBondOf S) (PositiveBondOf S ⊕ PositiveBondOf S),
        regionEnergyHessian k Ω (gaugeFieldOfPoint S x)
          (bondFormOfPositiveValues S (firstAlgebraPart x))
          (bondFormOfPositiveValues S (secondAlgebraPart x)) = G x := by
  let F : ℂ × ℂ × (PositiveBondOf S ⊕ (PositiveBondOf S ⊕ PositiveBondOf S) → ComplexMatrix2) → ℂ :=
    fun y => interiorEnergy Ω (adjugateTwist ((finestMeshInLevelUnits L k : ℝ) : ℂ)
      (adjugateField S fun b => y.2.2 (.inl b))
      (bondFormOfPositiveValues S (firstAlgebraPart y.2.2))
      (bondFormOfPositiveValues S (secondAlgebraPart y.2.2)) y.1 y.2.1)
  have hpt : ContDiff ℂ 3 fun y : ℂ × ℂ ×
      (PositiveBondOf S ⊕ (PositiveBondOf S ⊕ PositiveBondOf S) → ComplexMatrix2) => y.2.2 :=
    contDiff_snd.comp contDiff_snd
  have hco : ∀ i, ContDiff ℂ 3 fun y : ℂ × ℂ ×
      (PositiveBondOf S ⊕ (PositiveBondOf S ⊕ PositiveBondOf S) → ComplexMatrix2) => y.2.2 i :=
    contDiff_pi.1 hpt
  have hF : ContDiff ℂ 3 F :=
    contDiff_interiorEnergy Ω (contDiff_adjugateTwist _
      (contDiff_adjugateField S fun _ => hco _)
      (contDiff_bondForm S fun _ => hco _) (contDiff_bondForm S fun _ => hco _)
      contDiff_fst (contDiff_fst.comp contDiff_snd))
  obtain ⟨G, hG, hmix⟩ := exists_contDiff_mixedDeriv F hF
  refine ⟨G, hG, fun x hx => ?_⟩
  have hv : ∀ i : PositiveBondOf S, (x (.inl i)).det = 1 := fun i => hx (.inl i)
  have ha : ∀ i : PositiveBondOf S, firstAlgebraPart x i ∈ ComplexMatrix2.traceless :=
    fun i => hx (.inr (.inl i))
  have hb : ∀ i : PositiveBondOf S, secondAlgebraPart x i ∈ ComplexMatrix2.traceless :=
    fun i => hx (.inr (.inr i))
  have hkey : ∀ t t' : ℝ, interiorEnergy Ω (bareTwist k
      ((t : ℂ) • bondFormOfPositiveValues S (firstAlgebraPart x) +
        (t' : ℂ) • bondFormOfPositiveValues S (secondAlgebraPart x)) (gaugeFieldOfPoint S x)) =
      F ((t : ℂ), (t' : ℂ), x) := by
    intro t t'
    rw [bareTwist_eq_adjugateTwist k (U := gaugeFieldOfPoint S x) (det_gaugeField S hv)
      (bondForm_mem_traceless S ha) (bondForm_mem_traceless S hb)]
    simp only [F, gaugeFieldOfPoint, gaugeField_eq_adjugateField S hv]
  rw [← hmix x]
  simp only [regionEnergyHessian, hkey]
end Form
end HessianHolomorphy
open ComplexTransport HessianHolomorphy Matrices in
theorem regionHessianCovariance_holds
    (hTwist : TwistedTransportIsometryInvariance)
    (hOrient : BondOrientationDichotomy)
    (hFin : BondEndpointsAndFiniteness) :
    RegionHessianCovariance := by
  intro L m i σ hL hm hi hσ K k hK hiK i' hii' hi' Ω hΩ S hS hin
  have hInv : HessiansInvariant σ K Ω S :=
    (hTwist L m i σ hL hm hi hσ).2.2.2 K hK hiK i' hii' hi' Ω hΩ S hS hin
  have hX : ∀ b : BondAtLevel L m K 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    hOrient L m hL hm (levelDepth K 0) hK
  have hfin := (hFin ⟨L, hL, 1, ⟨m, hm⟩⟩).1 (levelDepth K 0)
    (show -(m : ℤ) ≤ levelDepth K 0 from hK.le)
  have hSite : Finite (Site L m (levelDepth K 0)) := hfin.2.2.1
  have hBond : Finite (Bond L m (levelDepth K 0)) := hfin.2.2.2
  have hPlaq : Finite (Plaquette L m (levelDepth K 0)) := by
    refine Finite.of_injective
      (fun P : Plaquette L m (levelDepth K 0) => (P.origin, P.firstAxis, P.secondAxis))
      fun P P' hP => ?_
    simp only [Prod.mk.injEq] at hP
    exact Plaquette.ext hP.1 hP.2.1 hP.2.2
  let inst : Fintype (PositiveBondOf S) := Fintype.ofFinite _
  obtain ⟨G, hG, hgG⟩ := exists_contDiff_eqOn_hessian (S := S) k Ω
  refine ⟨fun U hU A hA B hB => hInv.regionEnergy k U hU A hA B hB,
    inst, inferInstance, fun e => ⟨isHolomorphicToCoords_of_eqOn e _ G hG fun x hx => ?_,
      isHolomorphicToCoords_of_eqOn e _ G hG hgG⟩⟩
  have hv : ∀ i : PositiveBondOf S, (x (.inl i)).det = 1 := fun i => hx (.inl i)
  have ha : ∀ i : PositiveBondOf S, firstAlgebraPart x i ∈ ComplexMatrix2.traceless :=
    fun i => hx (.inr (.inl i))
  have hb : ∀ i : PositiveBondOf S, secondAlgebraPart x i ∈ ComplexMatrix2.traceless :=
    fun i => hx (.inr (.inr i))
  rw [hInv.regionEnergy k (gaugeFieldOfPoint S x) (isGaugeField_of_values hX hS hv) _
    (isSupportedOn_of_values hX hS ha) _ (isSupportedOn_of_values hX hS hb)]
  exact hgG x hx
end YangMills.Construction.PeriodicLattice
