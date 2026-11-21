import YangMills.Construction.EuclideanFunctionals.FiniteMeasureAtNonnegativeEnergiesDeterminedByItsTransform
import YangMills.Construction.EuclideanFunctionals.FirstFactsOnAReconstruction
import YangMills.Construction.EuclideanFunctionals.FirstValuesOfTheCentredFunctional
import YangMills.Construction.EuclideanFunctionals.TuplesSpansAndActions
import YangMills.Construction.FreeKernel.LineIntegrationByPartsProof
import YangMills.Construction.SpectralTheory.EverySelfAdjointOperatorIsResolved
import YangMills.Construction.SpectralTheory.MeasuresIntegralsProductsImagesAndTransportOfAProjectionValuedMeasure
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace ComplexConjugate
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.ReconstructionFactsProof
open YangMills.Construction.HilbertSpaceBasics (UnboundedOp)
open YangMills.Construction.BorelSpectral
open YangMills.Construction.BorelSpectral.SpectralMeasure
open YangMills.Construction.OperatorTransport (IsBoundedAdjoint IsUnitaryMap)
open YangMills.Construction.SpectralTheorem
  (IsSpectralIntegralOf spectralIntegralOp pushforwardToLine coordVar IntegralsAgree
    spectralMeasure negHalfLine RealLineSet)
open YangMills.Construction.SelfAdjointFunctions (fnCalc expI)
open YangMills.Construction.ResolvedOps (IsDiagonalized expComplex)
open YangMills.Construction.BorelCalculus (IsBoundedFn conjFn)
open YangMills.Construction.EuclideanFunctionals.SpectralPoint
open YangMills.Construction.EuclideanFunctionals.EuclidFunctionalWithRecon
structure Inputs : Prop where
  calculus : SpectralMeasureCalculus.CalculusTheorem
  joint : JointSpectralGenerators.JointMeasureGeneratorsCommutation
  diagFacts : ResolvedFacts.DiagonalizedFacts
  diagAll : SelfAdjointResolution.SelfAdjointDiagonalizationTheorem
  uniqueness : FiniteMeasureUniqueness.TransformDeterminesMeasure
  initValues : CenteredInitialValues.InitialValues
  listRules : TupleRules.TupleSpanActionRules
section Integrals
variable (h : Inputs) {𝒦 : Type} [NormedAddCommGroup 𝒦] [InnerProductSpace ℂ 𝒦] [CompleteSpace 𝒦]
  {n n' : ℕ} {Y : Set (Fin n → ℝ)} {Y' : Set (Fin n' → ℝ)}
include h
theorem spectralIntegralOp_apply_of_bounded (E : SpectralMeasure Y 𝒦) {g : Y → ℂ}
    (hg : Measurable g) (hb : IsBoundedFn g) (ψ : 𝒦) :
    ∃ hψ : ψ ∈ (spectralIntegralOp E g).domain,
      spectralIntegralOp E g ⟨ψ, hψ⟩ = E.integralOp g ψ := by
  have hA := (h.calculus 𝒦 n Y E).2.2.1
  have hI := hA.isIntegralOf g hg
  have hB := hA.of_bounded g hg hb
  have hm : ψ ∈ (spectralIntegralOp E g).domain := (hI.1 ψ).2 (by rw [hB.1]; exact mem_univ _)
  exact ⟨hm, (hI.2 ⟨ψ, hm⟩).trans (hB.2 ψ)⟩
theorem integralOp_eq_of_spectralIntegralOp_eq (E : SpectralMeasure Y 𝒦)
    (E' : SpectralMeasure Y' 𝒦) {g : Y → ℂ} {g' : Y' → ℂ} (hg : Measurable g)
    (hb : IsBoundedFn g) (hg' : Measurable g') (hb' : IsBoundedFn g')
    (he : spectralIntegralOp E g = spectralIntegralOp E' g') :
    E.integralOp g = E'.integralOp g' := by
  ext ψ
  obtain ⟨m, hm⟩ := spectralIntegralOp_apply_of_bounded h E hg hb ψ
  obtain ⟨m', hm'⟩ := spectralIntegralOp_apply_of_bounded h E' hg' hb' ψ
  rw [← hm, ← hm']
  exact (LinearPMap.ext_iff.1 he).2 (x := ψ) (hf := m) (hg := m')
theorem spectralIntegralOp_eq_of_integralsAgree (E : SpectralMeasure Y 𝒦)
    (E' : SpectralMeasure Y' 𝒦) {g : Y → ℂ} {g' : Y' → ℂ} (hg : Measurable g)
    (hg' : Measurable g') (hs : IntegralsAgree E g E' g') :
    spectralIntegralOp E g = spectralIntegralOp E' g' := by
  have hI := (h.calculus 𝒦 n Y E).2.2.1.isIntegralOf g hg
  have hI' := (h.calculus 𝒦 n' Y' E').2.2.1.isIntegralOf g' hg'
  refine LinearPMap.ext ?_ ?_
  · ext ψ
    rw [hI.1 ψ, hI'.1 ψ, hs.1]
  · intro x hx hy
    rw [hI.2 ⟨x, hx⟩, hI'.2 ⟨x, hy⟩]
    exact hs.2 _ ((hI.1 _).1 hx)
theorem inner_integralOp_self (E : SpectralMeasure Y 𝒦) {g : Y → ℂ} (hg : Measurable g)
    (hb : IsBoundedFn g) (ψ : 𝒦) :
    ⟪ψ, E.integralOp g ψ⟫_ℂ = ∫ y, g y ∂E.diagMeasure ψ := by
  have hA := (h.calculus 𝒦 n Y E).2.2.1
  have hB := hA.of_bounded g hg hb
  rw [← hB.2 ψ]
  exact hA.inner_self g hg ψ (by rw [hB.1]; exact mem_univ _)
end Integrals
theorem diagMeasure_eq_zero_of_apply_eq_zero {𝒦 : Type} [NormedAddCommGroup 𝒦]
    [InnerProductSpace ℂ 𝒦] [CompleteSpace 𝒦] {n : ℕ} {Y : Set (Fin n → ℝ)}
    (E : SpectralMeasure Y 𝒦) (Δ : BorelSubsets Y) (hΔ : E Δ = 0) (ψ : 𝒦) :
    E.diagMeasure ψ Δ.1 = 0 := by
  rw [diagMeasure_apply, hΔ]
  simp
theorem isUnitaryMap_of_two_sided_inverse {𝒦 : Type} [NormedAddCommGroup 𝒦]
    [InnerProductSpace ℂ 𝒦] {B B' : 𝒦 →L[ℂ] 𝒦} (h₁ : B' * B = 1) (h₂ : B * B' = 1)
    (hB : IsBoundedAdjoint B' B) : IsUnitaryMap (B : 𝒦 →ₗ[ℂ] 𝒦) where
  bijective := by
    refine ⟨fun x y hxy => ?_, fun y => ⟨B' y, ?_⟩⟩
    · have := congrArg B' hxy
      have e₁ : ∀ z, B' (B z) = z := fun z => congrArg (fun T : 𝒦 →L[ℂ] 𝒦 => T z) h₁
      simpa [e₁] using this
    · exact congrArg (fun T : 𝒦 →L[ℂ] 𝒦 => T y) h₂
  inner_map_map φ ψ := by
    have e₁ : B' (B φ) = φ := congrArg (fun T : 𝒦 →L[ℂ] 𝒦 => T φ) h₁
    have e₂ := hB (B φ) ψ
    rw [e₁] at e₂
    exact e₂
section OneFunctional
variable {c : SharpScale} {S : ConnFamily}
abbrev hmFamily (σ : EuclidFunctionalWithRecon c S) : Fin 4 → UnboundedOp σ.space :=
  hamMomFamily σ.recon.ham σ.recon.mom
def planeWave (v : R4) (p : EMPoints) : ℂ :=
  Complex.exp (Complex.I * ((∑ j : Fin 3, v j.castSucc * p.1 j.succ : ℝ) : ℂ))
def heatDamping (t : ℝ) (p : EMPoints) : ℂ :=
  (Ici (0 : ℝ)).indicator (fun x : ℝ => Complex.exp (-(t : ℂ) * (x : ℂ))) (p.1 0)
theorem measurable_emCoord (k : Fin 4) : Measurable fun p : EMPoints => p.1 k :=
  (measurable_pi_apply k).comp measurable_subtype_coe
theorem measurable_planeWave (v : R4) : Measurable (planeWave v) := by
  unfold planeWave
  have h₁ : Measurable fun p : EMPoints => ∑ j : Fin 3, v j.castSucc * p.1 j.succ :=
    Finset.measurable_fun_sum _ fun j _ => (measurable_emCoord j.succ).const_mul _
  exact Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp h₁))
theorem norm_planeWave (v : R4) (p : EMPoints) : ‖planeWave v p‖ = 1 := by
  unfold planeWave
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _
theorem isBoundedFn_planeWave (v : R4) : IsBoundedFn (planeWave v) :=
  ⟨1, fun p => (norm_planeWave v p).le⟩
theorem measurable_heatDamping_real (t : ℝ) :
    Measurable ((Ici (0 : ℝ)).indicator fun x : ℝ => Complex.exp (-(t : ℂ) * (x : ℂ))) :=
  Measurable.indicator (Complex.measurable_exp.comp
    (measurable_const.mul Complex.measurable_ofReal)) measurableSet_Ici
theorem norm_heatDamping_real_le {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    ‖(Ici (0 : ℝ)).indicator (fun x : ℝ => Complex.exp (-(t : ℂ) * (x : ℂ))) x‖ ≤ 1 := by
  by_cases hx : x ∈ Ici (0 : ℝ)
  · rw [indicator_of_mem hx, Complex.norm_exp]
    have hx' : (0 : ℝ) ≤ x := hx
    have : (-(t : ℂ) * (x : ℂ)).re = -t * x := by simp
    rw [this, Real.exp_le_one_iff]
    nlinarith
  · rw [indicator_of_notMem hx]
    simp
theorem measurable_heatDamping (t : ℝ) : Measurable (heatDamping t) :=
  (measurable_heatDamping_real t).comp (measurable_emCoord 0)
theorem isBoundedFn_heatDamping {t : ℝ} (ht : 0 ≤ t) : IsBoundedFn (heatDamping t) :=
  ⟨1, fun _ => norm_heatDamping_real_le ht _⟩
variable (h : Inputs) (σ : EuclidFunctionalWithRecon c S)
include h
theorem isDiagonalized_of_selfAdjoint {A : UnboundedOp σ.space}
    (hA : OperatorTransport.IsSelfAdjointUnbounded A) : IsDiagonalized A :=
  (h.diagAll.1 σ.space).2.2.2.1 A hA
theorem isDiagonalized_hmFamily (k : Fin 4) : IsDiagonalized (hmFamily σ k) := by
  induction k using Fin.cases with
  | zero => exact isDiagonalized_of_selfAdjoint h σ σ.recon.ham_selfAdjoint
  | succ j => exact isDiagonalized_of_selfAdjoint h σ (σ.recon.mom_selfAdjoint j)
omit h in
theorem stronglyCommute_hmFamily (j k : Fin 4) (hjk : j ≠ k) :
    ResolvedOps.StronglyCommute (hmFamily σ j) (hmFamily σ k) := by
  induction j using Fin.cases with
  | zero =>
    induction k using Fin.cases with
    | zero => exact absurd rfl hjk
    | succ k =>
      intro Δ Δ'
      exact (σ.recon.mom_commute_ham k Δ' Δ).symm
  | succ j =>
    induction k using Fin.cases with
    | zero => exact σ.recon.mom_commute_ham j
    | succ k =>
      exact σ.recon.mom_commute j k fun e => hjk (congrArg Fin.succ e)
theorem coordMarginal_jointMeasure (k : Fin 4) :
    σ.jointMeasure.coordMarginal k = spectralMeasure (hmFamily σ k) :=
  ((h.joint σ.space).1 4 (by norm_num) (hmFamily σ) (isDiagonalized_hmFamily h σ)
    (stronglyCommute_hmFamily σ)).2.2.1 k
theorem fnCalc_hmFamily (k : Fin 4) (u : ℝ → ℂ) (hu : Measurable u) :
    fnCalc (hmFamily σ k) u =
      spectralIntegralOp σ.jointMeasure fun y => u (y.1 k) :=
  ((h.joint σ.space).1 4 (by norm_num) (hmFamily σ) (isDiagonalized_hmFamily h σ)
    (stronglyCommute_hmFamily σ)).2.2.2.1 k u hu
theorem hmFamily_eq_spectralIntegralOp (k : Fin 4) :
    hmFamily σ k = spectralIntegralOp σ.jointMeasure fun y => ((y.1 k : ℝ) : ℂ) :=
  ((h.joint σ.space).1 4 (by norm_num) (hmFamily σ) (isDiagonalized_hmFamily h σ)
    (stronglyCommute_hmFamily σ)).2.2.2.2.1 k
theorem integralOp_spectralMeasure_eq_jointMeasure (k : Fin 4) {u : ℝ → ℂ} (hu : Measurable u)
    {b : ℝ} (hb : ∀ x, ‖u x‖ ≤ b) :
    (spectralMeasure (hmFamily σ k)).integralOp (fun y => u (y.1 0)) =
      σ.jointMeasure.integralOp fun y => u (y.1 k) :=
  integralOp_eq_of_spectralIntegralOp_eq h _ _
    (hu.comp ((measurable_pi_apply 0).comp measurable_subtype_coe)) ⟨b, fun _ => hb _⟩
    (hu.comp (measurable_emCoord k)) ⟨b, fun _ => hb _⟩ (fnCalc_hmFamily h σ k u hu)
theorem ham_eq_spectralIntegralOp : σ.recon.ham =
    spectralIntegralOp σ.jointMeasure fun p => ((energyOf p : ℝ) : ℂ) :=
  hmFamily_eq_spectralIntegralOp h σ 0
theorem mom_eq_spectralIntegralOp (j : Fin 3) : σ.recon.mom j =
    spectralIntegralOp σ.jointMeasure fun p => ((momentumOf p j : ℝ) : ℂ) :=
  hmFamily_eq_spectralIntegralOp h σ j.succ
omit h in
theorem translOp_eq_integralOp (v : R4) :
    σ.translOp v = σ.jointMeasure.integralOp (planeWave v) := rfl
theorem heatSemigroup_eq_integralOp {t : ℝ} (ht : 0 ≤ t) :
    σ.heatSemigroup t = σ.jointMeasure.integralOp (heatDamping t) :=
  integralOp_spectralMeasure_eq_jointMeasure h σ 0 (measurable_heatDamping_real t)
    (norm_heatDamping_real_le ht)
theorem jointMeasure_isCarriedBy_nonnegEnergy :
    σ.jointMeasure.IsCarriedBy nonnegEnergy := by
  have h₀ := ((h.diagFacts σ.space).2.1 _ (isDiagonalized_hmFamily h σ 0)).1
    σ.recon.ham_nonneg
  have h₁ := σ.jointMeasure.coordMarginal_realLineSet 0 negHalfLine
  rw [coordMarginal_jointMeasure h σ 0] at h₁
  have hs : (⟨nonnegEnergy.1ᶜ, nonnegEnergy.2.compl⟩ : BorelSubsets EMPoints) =
      ⟨{y | y.1 0 ∈ negHalfLine.1}, ((measurable_pi_apply 0).comp measurable_subtype_coe)
        negHalfLine.2⟩ :=
    Subtype.ext (by
      ext p
      simp [nonnegEnergy, negHalfLine, energyOf])
  unfold IsCarriedBy
  rw [hs]
  exact h₁.symm.trans h₀
theorem boundedLaws : SpectralMeasureCalculus.BoundedCalculusLaws σ.jointMeasure :=
  (h.calculus σ.space 4 EMPoints σ.jointMeasure).2.1
omit h in
theorem heatDamping_mul_planeWave (t : ℝ) (v : R4) : heatDamping t * planeWave v =
    zeroExtend nonnegEnergy.1 (laplaceFourierKernel t v) := by
  funext p
  by_cases hp : p ∈ nonnegEnergy.1
  · have hp' : p.1 0 ∈ Ici (0 : ℝ) := hp
    simp only [Pi.mul_apply, heatDamping, planeWave, zeroExtend, dif_pos hp, indicator_of_mem hp',
      laplaceFourierKernel, ← Complex.exp_add]
    rfl
  · have hp' : p.1 0 ∉ Ici (0 : ℝ) := hp
    simp only [Pi.mul_apply, heatDamping, zeroExtend, dif_neg hp, indicator_of_notMem hp',
      zero_mul]
theorem heatSemigroup_mul_translOp {t : ℝ} (ht : 0 ≤ t) (v : R4) :
    σ.heatSemigroup t * σ.translOp v =
      σ.jointMeasure.integralOpOn nonnegEnergy (laplaceFourierKernel t v) := by
  rw [heatSemigroup_eq_integralOp h σ ht, translOp_eq_integralOp, ← (boundedLaws h σ).mul _ _
    (measurable_heatDamping t) (isBoundedFn_heatDamping ht) (measurable_planeWave v)
    (isBoundedFn_planeWave v), heatDamping_mul_planeWave]
  rfl
theorem translOp_mul_heatSemigroup {t : ℝ} (ht : 0 ≤ t) (v : R4) :
    σ.translOp v * σ.heatSemigroup t = σ.heatSemigroup t * σ.translOp v := by
  rw [heatSemigroup_eq_integralOp h σ ht, translOp_eq_integralOp, ← (boundedLaws h σ).mul _ _
    (measurable_heatDamping t) (isBoundedFn_heatDamping ht) (measurable_planeWave v)
    (isBoundedFn_planeWave v), ← (boundedLaws h σ).mul _ _ (measurable_planeWave v)
    (isBoundedFn_planeWave v) (measurable_heatDamping t) (isBoundedFn_heatDamping ht), mul_comm]
omit h in
theorem planeWave_mul (v v' : R4) : planeWave v * planeWave v' = planeWave (v + v') := by
  funext p
  simp only [Pi.mul_apply, planeWave, ← Complex.exp_add, Pi.add_apply, add_mul,
    Finset.sum_add_distrib]
  push_cast
  ring_nf
theorem translOp_mul (v v' : R4) :
    σ.translOp v * σ.translOp v' = σ.translOp (v + v') := by
  rw [translOp_eq_integralOp, translOp_eq_integralOp, translOp_eq_integralOp, ← planeWave_mul]
  exact ((boundedLaws h σ).mul _ _ (measurable_planeWave v) (isBoundedFn_planeWave v)
    (measurable_planeWave v') (isBoundedFn_planeWave v')).symm
theorem translOp_zero : σ.translOp 0 = 1 := by
  have hf : planeWave 0 = (univ : Set EMPoints).indicator 1 := by
    funext p
    simp [planeWave]
  rw [translOp_eq_integralOp, hf]
  exact ((boundedLaws h σ).indicator ⟨univ, MeasurableSet.univ⟩).trans σ.jointMeasure.map_univ
omit h in
theorem conjFn_planeWave (v : R4) : conjFn (planeWave v) = planeWave (-v) := by
  funext p
  simp only [conjFn, planeWave, ← Complex.exp_conj, map_mul, Complex.conj_I,
    Complex.conj_ofReal, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, Complex.ofReal_neg,
    mul_neg]
theorem star_translOp (v : R4) :
    star (σ.translOp v) = σ.translOp (-v) := by
  rw [translOp_eq_integralOp, translOp_eq_integralOp, ← conjFn_planeWave]
  exact ((boundedLaws h σ).conjugate _ (measurable_planeWave v) (isBoundedFn_planeWave v)).symm
theorem translOp_isBoundedAdjoint (v : R4) :
    IsBoundedAdjoint (σ.translOp (-v)) (σ.translOp v) := by
  intro φ ψ
  rw [← star_translOp h σ v, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left]
theorem translOp_isUnitaryMap (v : R4) :
    IsUnitaryMap (σ.translOp v : σ.space →ₗ[ℂ] σ.space) :=
  isUnitaryMap_of_two_sided_inverse
    (by rw [translOp_mul h σ, neg_add_cancel, translOp_zero h σ])
    (by rw [translOp_mul h σ, add_neg_cancel, translOp_zero h σ])
    (translOp_isBoundedAdjoint h σ v)
omit h in
theorem jointMeasure_isCarriedBy_univ :
    σ.jointMeasure.IsCarriedBy ⟨univ, MeasurableSet.univ⟩ := by
  unfold IsCarriedBy
  have hs : (⟨(univ : Set EMPoints)ᶜ, MeasurableSet.univ.compl⟩ : BorelSubsets EMPoints) =
      ⟨∅, MeasurableSet.empty⟩ := Subtype.ext compl_univ
  rw [hs]
  exact σ.jointMeasure.apply_empty
theorem continuous_translOp_apply (ψ : σ.space) :
    Continuous fun v : spatialVecs => σ.translOp v ψ := by
  rw [continuous_iff_seqContinuous]
  intro x a hx
  refine (boundedLaws h σ).tendsto (fun k => planeWave (x k)) (planeWave a) 1
    ⟨univ, MeasurableSet.univ⟩ (fun k => measurable_planeWave _) (measurable_planeWave _)
    (fun k p => (norm_planeWave _ p).le) (fun p => (norm_planeWave _ p).le)
    (jointMeasure_isCarriedBy_univ σ) (fun y _ => ?_) ψ
  have hc : Continuous fun v : spatialVecs => planeWave v.1 y := by
    unfold planeWave
    refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp ?_))
    exact continuous_finsetSum _ fun j _ =>
      ((continuous_apply _).comp continuous_subtype_val).mul continuous_const
  exact (hc.tendsto a).comp hx
omit h in
theorem norm_exp_I_mul_mul (s x : ℝ) : ‖Complex.exp (Complex.I * s * (x : ℂ))‖ = 1 := by apply _root_.YangMills.Construction.FreeKernel.LineIntegration.norm_character <;> assumption
omit h in
theorem measurable_exp_I_mul_mul (s : ℝ) :
    Measurable fun x : ℝ => Complex.exp (Complex.I * s * (x : ℂ)) :=
  Complex.measurable_exp.comp (measurable_const.mul Complex.measurable_ofReal)
theorem expI_mom (j : Fin 3) (s : ℝ) :
    expI (σ.recon.mom j) s =
      σ.jointMeasure.integralOp fun y =>
        Complex.exp (Complex.I * s * ((y.1 j.succ : ℝ) : ℂ)) :=
  integralOp_spectralMeasure_eq_jointMeasure h σ j.succ (measurable_exp_I_mul_mul s) (b := 1)
    fun x => (norm_exp_I_mul_mul s x).le
theorem translOp_eq_prod_expI (v : R4) :
    σ.translOp v =
      expI (σ.recon.mom 0) (v 0) * expI (σ.recon.mom 1) (v 1) * expI (σ.recon.mom 2) (v 2) := by
  have hm : ∀ (s : ℝ) (k : Fin 4), Measurable fun y : EMPoints =>
      Complex.exp (Complex.I * s * ((y.1 k : ℝ) : ℂ)) := fun s k =>
    (measurable_exp_I_mul_mul s).comp (measurable_emCoord k)
  have hb : ∀ (s : ℝ) (k : Fin 4), IsBoundedFn fun y : EMPoints =>
      Complex.exp (Complex.I * s * ((y.1 k : ℝ) : ℂ)) := fun s k =>
    ⟨1, fun y => (norm_exp_I_mul_mul s _).le⟩
  have hprod : IsBoundedFn ((fun y : EMPoints =>
      Complex.exp (Complex.I * (v 0 : ℝ) * ((y.1 (Fin.succ 0) : ℝ) : ℂ))) * fun y : EMPoints =>
      Complex.exp (Complex.I * (v 1 : ℝ) * ((y.1 (Fin.succ 1) : ℝ) : ℂ))) :=
    ⟨1, fun y => by
      simp only [Pi.mul_apply, norm_mul, norm_exp_I_mul_mul, mul_one, le_refl]⟩
  rw [expI_mom h σ, expI_mom h σ, expI_mom h σ,
    ← (boundedLaws h σ).mul _ _ (hm _ _) (hb _ _) (hm _ _) (hb _ _),
    ← (boundedLaws h σ).mul _ _ ((hm _ _).mul (hm _ _)) hprod (hm _ _) (hb _ _),
    translOp_eq_integralOp]
  congr 1
  funext p
  simp only [Pi.mul_apply, planeWave, ← Complex.exp_add, Fin.sum_univ_three]
  congr 1
  have e₀ : (0 : Fin 3).castSucc = (0 : Fin 4) := rfl
  have e₁ : (1 : Fin 3).castSucc = (1 : Fin 4) := rfl
  have e₂ : (2 : Fin 3).castSucc = (2 : Fin 4) := rfl
  rw [e₀, e₁, e₂]
  push_cast
  ring
theorem dirMomentum_props (n : Fin 3 → ℝ) :
    ResolvedOps.IsDiagonalized (σ.dirMomentum n) ∧
      OperatorTransport.IsSelfAdjointUnbounded (σ.dirMomentum n) ∧
      ∀ s : ℝ, σ.translOp (spatialEmbed (s • n)) = expI (σ.dirMomentum n) s := by
  have hg := measurable_dot3_momentumOf n
  have hR := ((h.diagFacts σ.space).2.2.2.2.2.1 4 EMPoints σ.jointMeasure
    univ_nonempty).1 _ hg
  have hreal := (h.calculus σ.space 4 EMPoints σ.jointMeasure).2.2.2.2.2.2.1
  refine ⟨hR.1, hreal.isSelfAdjoint _ (Complex.measurable_ofReal.comp hg)
    (fun y => Complex.ofReal_im _), fun s => ?_⟩
  have e := hR.2.2 _ (measurable_exp_I_mul_mul s)
  have e' := integralOp_eq_of_spectralIntegralOp_eq h _ _
    ((measurable_exp_I_mul_mul s).comp ((measurable_pi_apply 0).comp measurable_subtype_coe))
    ⟨1, fun y => (norm_exp_I_mul_mul s _).le⟩ ((measurable_exp_I_mul_mul s).comp hg)
    ⟨1, fun y => (norm_exp_I_mul_mul s _).le⟩ e
  refine Eq.trans ?_ e'.symm
  rw [translOp_eq_integralOp]
  congr 1
  funext p
  simp only [planeWave, Function.comp, spatialEmbed, Fin.snoc_castSucc, dot3]
  congr 1
  push_cast
  rw [mul_assoc, Finset.mul_sum]
  simp [mul_assoc, Finset.mul_sum, momentumOf]
theorem spectralGeneratorsAndKernel : σ.SpectralGeneratorsAndKernel := by
  have hA := (h.calculus σ.space 4 EMPoints σ.jointMeasure).2.2.1
  refine ⟨?_, fun j => ?_, jointMeasure_isCarriedBy_nonnegEnergy h σ, fun t ht v _ =>
    ⟨(translOp_mul_heatSemigroup h σ ht v).symm, heatSemigroup_mul_translOp h σ ht v⟩⟩
  · have k := hA.isIntegralOf (fun p => ((energyOf p : ℝ) : ℂ))
      (Complex.measurable_ofReal.comp measurable_energyOf)
    rwa [← ham_eq_spectralIntegralOp h σ] at k
  · have k := hA.isIntegralOf (fun p => ((momentumOf p j : ℝ) : ℂ))
      (Complex.measurable_ofReal.comp (measurable_momentumOf_apply j))
    rwa [← mom_eq_spectralIntegralOp h σ j] at k
theorem translUnitaryGroup : σ.TranslUnitaryGroup :=
  ⟨fun v _ => translOp_isUnitaryMap h σ v, translOp_zero h σ,
    fun v _ v' _ => translOp_mul h σ v v', fun v _ => translOp_isBoundedAdjoint h σ v,
    continuous_translOp_apply h σ, fun v _ => translOp_eq_prod_expI h σ v,
    fun n _ => dirMomentum_props h σ n⟩
omit h in
theorem measurable_zeroExtend_kernel (t : ℝ) (v : R4) :
    Measurable (zeroExtend nonnegEnergy.1 (laplaceFourierKernel t v)) := by
  rw [← heatDamping_mul_planeWave]
  exact (measurable_heatDamping t).mul (measurable_planeWave v)
omit h in
theorem isBoundedFn_zeroExtend_kernel {t : ℝ} (ht : 0 ≤ t) (v : R4) :
    IsBoundedFn (zeroExtend nonnegEnergy.1 (laplaceFourierKernel t v)) := by
  rw [← heatDamping_mul_planeWave]
  refine ⟨1, fun p => ?_⟩
  rw [Pi.mul_apply, norm_mul, norm_planeWave, mul_one]
  exact norm_heatDamping_real_le ht _
end OneFunctional
def emPointsEquiv : EMPoints ≃ᵐ EuclideanSpace ℝ (Fin 4) :=
  (MeasurableEquiv.Set.univ (Fin 4 → ℝ)).trans (MeasurableEquiv.toLp 2 (Fin 4 → ℝ))
theorem setIntegral_map_emPointsEquiv (μ : Measure EMPoints) (t : ℕ)
    (u : EuclideanSpace ℝ (Fin 3)) :
    ∫ p in nonnegEnergySet.1, FiniteMeasureUniqueness.laplaceFourierKernel t u p
        ∂(μ.map emPointsEquiv) =
      ∫ p, zeroExtend nonnegEnergy.1
        (laplaceFourierKernel (t : ℝ) (spatialEmbed fun j => u j)) p ∂μ := by
  rw [← integral_indicator nonnegEnergySet.2, integral_map_equiv emPointsEquiv]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  by_cases hp : p ∈ nonnegEnergy.1
  · have hp' : emPointsEquiv p ∈ nonnegEnergySet.1 := hp
    simp only [indicator_of_mem hp', zeroExtend, dif_pos hp, laplaceFourierKernel,
      FiniteMeasureUniqueness.laplaceFourierKernel]
    congr 1
  · have hp' : emPointsEquiv p ∉ nonnegEnergySet.1 := hp
    simp only [indicator_of_notMem hp', zeroExtend, dif_neg hp]
theorem measure_eq_of_kernel_integrals_eq (h : Inputs) (m m' : Measure EMPoints)
    [IsFiniteMeasure m] [IsFiniteMeasure m']
    (h₀ : m nonnegEnergy.1ᶜ = 0) (h₀' : m' nonnegEnergy.1ᶜ = 0)
    (hI : ∀ (k : ℕ) (v : R4), v ∈ spatialVecs →
      ∫ p, zeroExtend nonnegEnergy.1 (laplaceFourierKernel (k : ℝ) v) p ∂m =
        ∫ p, zeroExtend nonnegEnergy.1 (laplaceFourierKernel (k : ℝ) v) p ∂m') :
    m = m' := by
  have hneg : ∀ μ : Measure EMPoints, μ nonnegEnergy.1ᶜ = 0 →
      (μ.map emPointsEquiv) negEnergySet.1 = 0 := by
    intro μ hμ
    rw [emPointsEquiv.map_apply]
    refine measure_mono_null (fun p hp => ?_) hμ
    exact fun hq : (0 : ℝ) ≤ p.1 0 => absurd (show p.1 0 < 0 from hp) (not_lt.2 hq)
  have hmap := h.uniqueness (m.map emPointsEquiv) (m'.map emPointsEquiv) (hneg m h₀)
    (hneg m' h₀')
    (fun t u => by
      rw [setIntegral_map_emPointsEquiv, setIntegral_map_emPointsEquiv]
      exact hI t _ (by simp [spatialVecs, spatialEmbed]; rfl))
  exact emPointsEquiv.map_measurableEquiv_injective hmap
section OneFunctional
variable {c : SharpScale} {S : ConnFamily} (h : Inputs) (σ : EuclidFunctionalWithRecon c S)
include h
theorem inner_heatSemigroup_translOp {t : ℝ} (ht : 0 ≤ t) (v : R4) (ψ : σ.space) :
    ⟪ψ, σ.heatSemigroup t (σ.translOp v ψ)⟫_ℂ =
      ∫ p, zeroExtend nonnegEnergy.1 (laplaceFourierKernel t v) p
        ∂σ.jointMeasure.diagMeasure ψ := by
  rw [← inner_integralOp_self h _ (measurable_zeroExtend_kernel t v)
    (isBoundedFn_zeroExtend_kernel ht v)]
  exact congrArg (fun T : σ.space →L[ℂ] σ.space => ⟪ψ, T ψ⟫_ℂ)
    (heatSemigroup_mul_translOp h σ ht v)
theorem spectralMeasureUniqueness : σ.SpectralMeasureUniqueness := by
  intro 𝒦 _ _ _ V hV E' hC hI Δ
  have hVs : ∀ ψ : 𝒦, V (hV.inv ψ) = ψ := fun ψ => hV.toLinearEquiv.apply_symm_apply ψ
  have hin : ∀ (ψ : 𝒦) (x : σ.space), ⟪ψ, V x⟫_ℂ = ⟪hV.inv ψ, x⟫_ℂ := by
    intro ψ x
    conv_lhs => rw [← hVs ψ]
    exact hV.inner_map_map _ _
  have hs : ∀ ψ : 𝒦, E'.diagMeasure ψ = σ.jointMeasure.diagMeasure (hV.inv ψ) := by
    intro ψ
    refine measure_eq_of_kernel_integrals_eq h _ _
      (diagMeasure_eq_zero_of_apply_eq_zero E' ⟨_, _⟩ hC ψ)
      (diagMeasure_eq_zero_of_apply_eq_zero _ ⟨_, _⟩ (jointMeasure_isCarriedBy_nonnegEnergy h σ) _)
      fun k v hv => ?_
    rw [← inner_heatSemigroup_translOp h σ (Nat.cast_nonneg k) v,
      ← inner_integralOp_self h E' (measurable_zeroExtend_kernel _ v)
        (isBoundedFn_zeroExtend_kernel (Nat.cast_nonneg k) v), ← hin]
    congr 1
    exact congrArg (fun T : 𝒦 →ₗ[ℂ] 𝒦 => T ψ) (hI k v hv)
  refine (ext_inner_map _ _).1 fun ψ => ?_
  rw [← inner_conj_symm, ← inner_conj_symm _ ψ]
  congr 1
  change ⟪ψ, E' Δ ψ⟫_ℂ = ⟪ψ, V (σ.jointMeasure Δ (hV.inv ψ))⟫_ℂ
  rw [inner_apply_self_eq_diagMeasure, hs, hin, ← inner_apply_self_eq_diagMeasure]
omit h in
theorem nil_mem_sepAll : ([] : FnList) ∈ sepAll :=
  (ReflectionPositivity.AxisMirror.Ambient.nil_mem_separatedWithin defaultMirrorData
    ReflectionPositivity.AxisMirror.Ambient.euclidean upperHalf).1
omit h in
theorem actFree_toFree_nil (r : EuclidMotion) : r.actFree (toFree []) = toFree [] :=
  liftLin_toFree (fun X : sepAll => toFree (r.actList X.1)) ⟨[], nil_mem_sepAll⟩
omit h in
theorem freeConj_toFree_nil : freeConj (toFree []) = toFree [] := by
  rw [toFree_of_mem nil_mem_sepAll]
  simp [freeConj]
omit h in
theorem freeMul_toFree_nil : freeMul (toFree []) (toFree []) = toFree [] := by
  have h₁ := liftLin_toFree (fun X : sepAll => liftLin fun Y : sepAll =>
    toFree (listAppend X.1 Y.1)) ⟨[], nil_mem_sepAll⟩
  have h₂ := liftLin_toFree (fun Y : sepAll => toFree (listAppend [] Y.1))
    ⟨[], nil_mem_sepAll⟩
  exact (LinearMap.congr_fun h₁ (toFree [])).trans h₂
theorem osForm_toFree_nil (S : ConnFamily) :
    osForm S (toFree []) (toFree []) = 1 := by
  unfold osForm
  rw [freeConj_toFree_nil, actFree_toFree_nil, freeMul_toFree_nil]
  have e := liftLin_toFree (fun X : sepAll => ((centeredFn S X : ℝ) : ℂ))
    ⟨[], nil_mem_sepAll⟩
  have e₁ : centeredFn S ⟨[], nil_mem_sepAll⟩ = 1 := (h.initValues S).1
  rw [e₁] at e
  exact e.trans Complex.ofReal_one
theorem inner_vac_self : ⟪σ.recon.vac, σ.recon.vac⟫_ℂ = 1 :=
  (σ.recon.inner_cls _ _).trans (osForm_toFree_nil h S)
theorem norm_vac : ‖σ.recon.vac‖ = 1 := by
  have e := inner_self_eq_norm_sq (𝕜 := ℂ) σ.recon.vac
  rw [inner_vac_self h σ] at e
  have e' : ‖σ.recon.vac‖ ^ 2 = 1 := by simpa using e.symm
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 e'
omit h in
theorem classOrZero_actFree_nil (r : EuclidMotion) :
    readClass σ.recon.cls (r.actFree (toFree [])) = σ.recon.vac := by
  rw [actFree_toFree_nil]
  exact dif_pos emptyComb.2
omit h in
theorem heatSemigroup_vac {t : ℝ} (ht : 0 ≤ t) :
    σ.heatSemigroup t σ.recon.vac = σ.recon.vac :=
  (σ.recon.expHam_cls t ht emptyComb).trans (classOrZero_actFree_nil σ _)
omit h in
theorem translOp_vac {v : R4} (hv : v ∈ spatialVecs) :
    σ.translOp v σ.recon.vac = σ.recon.vac :=
  (σ.recon.transl_cls v hv emptyComb).trans (classOrZero_actFree_nil σ _)
omit h in
theorem rotOp_vac (w : timeStabilizer) :
    σ.recon.rotOp w σ.recon.vac = σ.recon.vac :=
  (σ.recon.rotOp_cls w emptyComb).trans (classOrZero_actFree_nil σ _)
theorem diagMeasure_vac :
    σ.jointMeasure.diagMeasure σ.recon.vac = Measure.dirac ⟨0, mem_univ _⟩ := by
  have hz : (⟨0, mem_univ _⟩ : EMPoints) ∈ nonnegEnergy.1 := le_refl (0 : ℝ)
  refine measure_eq_of_kernel_integrals_eq h _ _ (diagMeasure_eq_zero_of_apply_eq_zero _ ⟨_, _⟩
    (jointMeasure_isCarriedBy_nonnegEnergy h σ) _) ?_ fun k v hv => ?_
  · rw [Measure.dirac_apply' _ nonnegEnergy.2.compl]
    simp [hz]
  · rw [← inner_heatSemigroup_translOp h σ (Nat.cast_nonneg k) v, translOp_vac σ hv,
      heatSemigroup_vac σ (Nat.cast_nonneg k), inner_vac_self h σ, integral_dirac,
      zeroExtend, dif_pos hz]
    simp [laplaceFourierKernel, energyOf, momentumOf, dotR4, dot3]
theorem vac_mem_integralDom (g : EMPoints → ℂ) (hg : Measurable g)
    (h₀ : g ⟨0, mem_univ _⟩ = 0) :
    σ.recon.vac ∈ σ.jointMeasure.integralDom g ∧
      σ.jointMeasure.integralApply g σ.recon.vac = 0 := by
  have hA := (h.calculus σ.space 4 EMPoints σ.jointMeasure).2.2.1
  have hd : σ.recon.vac ∈ σ.jointMeasure.integralDom g := by
    change ∫⁻ y, ‖g y‖ₑ ^ 2 ∂σ.jointMeasure.diagMeasure σ.recon.vac < ⊤
    rw [diagMeasure_vac h σ, lintegral_dirac' _ (hg.enorm.pow_const 2), h₀]
    simp
  refine ⟨hd, ?_⟩
  have e := hA.norm_sq g hg _ hd
  rw [diagMeasure_vac h σ, integral_dirac, h₀] at e
  simpa using e
theorem vacuumInvariance : σ.VacuumInvariance := by
  have hG := spectralGeneratorsAndKernel h σ
  refine ⟨norm_vac h σ, fun t ht => heatSemigroup_vac σ ht, fun v hv => translOp_vac σ hv,
    rotOp_vac σ, diagMeasure_vac h σ, ?_, fun j => ?_⟩
  · have hD := vac_mem_integralDom h σ _ (Complex.measurable_ofReal.comp measurable_energyOf)
      (by simp [energyOf])
    have hm := (hG.1.1 _).2 hD.1
    exact ⟨hm, (hG.1.2 ⟨_, hm⟩).trans hD.2⟩
  · have hD := vac_mem_integralDom h σ _
      (Complex.measurable_ofReal.comp (measurable_momentumOf_apply j)) (by simp [momentumOf])
    have hm := (hG.2.1 j |>.1 _).2 hD.1
    exact ⟨hm, ((hG.2.1 j).2 ⟨_, hm⟩).trans hD.2⟩
end OneFunctional
section Group
theorem offset_eq_zero (w : timeStabilizer) : (w : EuclidMotion).offset = 0 := by
  obtain ⟨f, hf⟩ := w.2.1
  rw [← hf]
  rfl
theorem stab_map_add (w : timeStabilizer) (x y : R4) :
    (w : EuclidMotion) (x + y) = (w : EuclidMotion) x + (w : EuclidMotion) y := by
  simp only [offset_eq_zero, add_zero, map_add]
theorem stab_map_smul (w : timeStabilizer) (a : ℝ) (x : R4) :
    (w : EuclidMotion) (a • x) = a • (w : EuclidMotion) x := by
  simp only [offset_eq_zero, add_zero, map_smul]
theorem signedFrame_fix_time {f : PeriodicLattice.SignedFrame}
    (he : ofSignedFrame f timeVec = timeVec) :
    f.1 3 = 3 ∧ ((f.2 3 : ℤ) : ℝ) = 1 := by
  have h₃ := congrFun he 3
  rw [ofSignedFrame_apply] at h₃
  change ((f.2 3 : ℤ) : ℝ) * timeVec (f.1 3) = timeVec 3 at h₃
  have hone : timeVec 3 = 1 := by simp [PeriodicLattice.coordVec]
  by_cases hf : f.1 3 = 3
  · rw [hf, hone, mul_one] at h₃
    exact ⟨hf, h₃⟩
  · exfalso
    have hz : timeVec (f.1 3) = 0 := by simp [PeriodicLattice.coordVec, hf]
    rw [hz, hone, mul_zero] at h₃
    exact zero_ne_one h₃
theorem stab_apply_three (w : timeStabilizer) (x : R4) : (w : EuclidMotion) x 3 = x 3 := by
  obtain ⟨f, hf⟩ := w.2.1
  have he : ofSignedFrame f timeVec = timeVec := by
    rw [hf]
    exact w.2.2
  obtain ⟨h₁, h₂⟩ := signedFrame_fix_time he
  rw [← hf, ofSignedFrame_apply]
  change ((f.2 3 : ℤ) : ℝ) * x (f.1 3) = x 3
  rw [h₁, h₂, one_mul]
theorem stab_sum_mul (w : timeStabilizer) (a b : R4) :
    ∑ μ, (w : EuclidMotion) a μ * (w : EuclidMotion) b μ = ∑ μ, a μ * b μ := by
  obtain ⟨f, hf⟩ := w.2.1
  rw [← hf]
  have e : ∀ μ, ofSignedFrame f a μ * ofSignedFrame f b μ = a (f.1 μ) * b (f.1 μ) := by
    intro μ
    rw [ofSignedFrame_apply, ofSignedFrame_apply]
    change ((f.2 μ : ℤ) : ℝ) * a (f.1 μ) * (((f.2 μ : ℤ) : ℝ) * b (f.1 μ)) = _
    have hs := intUnit_mul_self (f.2 μ)
    linear_combination (a (f.1 μ) * b (f.1 μ)) * hs
  simp only [e]
  exact Equiv.sum_comp f.1 fun μ => a μ * b μ
theorem spatialEmbed_castSucc (u : Fin 3 → ℝ) (j : Fin 3) : spatialEmbed u j.castSucc = u j :=
  Fin.snoc_castSucc (α := fun _ => ℝ) _ _ _
theorem spatialEmbed_three (u : Fin 3 → ℝ) : spatialEmbed u 3 = 0 :=
  Fin.snoc_last (α := fun _ => ℝ) _ _
theorem spatialEmbed_restrict {v : R4} (hv : v ∈ spatialVecs) :
    spatialEmbed (fun j => v j.castSucc) = v := by
  funext μ
  refine Fin.lastCases ?_ (fun j => ?_) μ
  · exact (spatialEmbed_three _).trans hv.symm
  · exact spatialEmbed_castSucc _ j
theorem spatialEmbed_rotSpatial (w : timeStabilizer) (u : Fin 3 → ℝ) :
    spatialEmbed (rotSpatial w u) = (w : EuclidMotion) (spatialEmbed u) := by
  funext μ
  refine Fin.lastCases ?_ (fun j => ?_) μ
  · change spatialEmbed _ 3 = (w : EuclidMotion) _ 3
    rw [spatialEmbed_three, stab_apply_three, spatialEmbed_three]
  · rw [spatialEmbed_castSucc]
    rfl
theorem dot3_eq_sum (u u' : Fin 3 → ℝ) :
    dot3 u u' = ∑ μ, spatialEmbed u μ * spatialEmbed u' μ := by
  rw [Fin.sum_univ_castSucc]
  have e : spatialEmbed u (Fin.last 3) = 0 := spatialEmbed_three u
  simp only [spatialEmbed_castSucc, e, zero_mul, add_zero]
  rfl
theorem dot3_rotSpatial (w : timeStabilizer) (u q : Fin 3 → ℝ) :
    dot3 (rotSpatial w u) q = dot3 u (rotSpatial w⁻¹ q) := by
  rw [dot3_eq_sum, dot3_eq_sum, spatialEmbed_rotSpatial, spatialEmbed_rotSpatial]
  have e := stab_sum_mul w (spatialEmbed u) (((w⁻¹ : timeStabilizer) : EuclidMotion)
    (spatialEmbed q))
  have e' : (w : EuclidMotion) (((w⁻¹ : timeStabilizer) : EuclidMotion) (spatialEmbed q)) =
      spatialEmbed q := EuclidMotion.apply_inv_apply _ _
  rw [e'] at e
  exact e
theorem rotSpatial_inv_rotSpatial (w : timeStabilizer) (u : Fin 3 → ℝ) :
    rotSpatial w⁻¹ (rotSpatial w u) = u := by
  funext j
  have e : spatialEmbed (rotSpatial w⁻¹ (rotSpatial w u)) = spatialEmbed u := by
    rw [spatialEmbed_rotSpatial, spatialEmbed_rotSpatial]
    exact EuclidMotion.inv_apply_apply _ _
  have e' := congrFun e j.castSucc
  rwa [spatialEmbed_castSucc, spatialEmbed_castSucc] at e'
theorem rotPoint_inv_rotPoint (w : timeStabilizer) (p : EMPoints) :
    rotPoint w⁻¹ (rotPoint w p) = p := by
  apply Subtype.ext
  funext μ
  refine Fin.cases rfl (fun j => ?_) μ
  exact congrFun (rotSpatial_inv_rotSpatial w (momentumOf p)) j
theorem measurable_spatialEmbed_momentumOf :
    Measurable fun p : EMPoints => spatialEmbed (momentumOf p) := by
  refine measurable_pi_iff.2 fun μ => ?_
  refine Fin.lastCases ?_ (fun j => ?_) μ
  · have e : (fun p : EMPoints => spatialEmbed (momentumOf p) (Fin.last 3)) = fun _ => 0 :=
      funext fun p => spatialEmbed_three _
    rw [e]
    exact measurable_const
  · simp only [spatialEmbed_castSucc]
    exact measurable_momentumOf_apply j
theorem measurable_rotPoint (w : timeStabilizer) : Measurable (rotPoint w) := by
  refine Measurable.subtype_mk (measurable_pi_iff.2 fun μ => ?_)
  refine Fin.cases measurable_energyOf (fun j => ?_) μ
  have hc : Continuous fun x : R4 => (w : EuclidMotion) x :=
    (w : EuclidMotion).lin.continuous_of_finiteDimensional.add continuous_const
  exact (measurable_pi_apply j.castSucc).comp
    (hc.measurable.comp measurable_spatialEmbed_momentumOf)
theorem image_rotPoint (w : timeStabilizer) (Δ : Set EMPoints) :
    rotPoint w '' Δ = rotPoint w⁻¹ ⁻¹' Δ := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    rwa [mem_preimage, rotPoint_inv_rotPoint]
  · intro hp
    refine ⟨_, hp, ?_⟩
    have e := rotPoint_inv_rotPoint w⁻¹ p
    rwa [inv_inv] at e
theorem dotR4_stab (w : timeStabilizer) {v : R4} (hv : v ∈ spatialVecs)
    (q : Fin 3 → ℝ) : dotR4 ((w : EuclidMotion) v) q = dotR4 v (rotSpatial w⁻¹ q) := by
  have e : (fun j : Fin 3 => (w : EuclidMotion) v j.castSucc) =
      rotSpatial w fun j => v j.castSucc := by
    funext j
    change _ = (w : EuclidMotion) (spatialEmbed _) j.castSucc
    rw [spatialEmbed_restrict hv]
  unfold dotR4
  rw [e, dot3_rotSpatial]
theorem zeroExtend_kernel_comp_rotPoint (w : timeStabilizer) {v : R4} (hv : v ∈ spatialVecs)
    (t : ℝ) : zeroExtend nonnegEnergy.1 (laplaceFourierKernel t v) ∘ rotPoint w⁻¹ =
      zeroExtend nonnegEnergy.1 (laplaceFourierKernel t ((w : EuclidMotion) v)) := by
  funext p
  by_cases hp : p ∈ nonnegEnergy.1
  · have hq : rotPoint w⁻¹ p ∈ nonnegEnergy.1 := hp
    simp only [Function.comp, zeroExtend, dif_pos hp, dif_pos hq, laplaceFourierKernel]
    rw [dotR4_stab w hv]
    rfl
  · have hq : rotPoint w⁻¹ p ∉ nonnegEnergy.1 := hp
    simp only [Function.comp, zeroExtend, dif_neg hp, dif_neg hq]
theorem stab_smul_timeVec (w : timeStabilizer) (t : ℝ) :
    (w : EuclidMotion) (t • timeVec) = t • timeVec := by
  rw [stab_map_smul, w.2.2]
theorem stab_mul_transl (w : timeStabilizer) (v : R4) :
    (w : EuclidMotion) * EuclidMotion.transl v =
      EuclidMotion.transl ((w : EuclidMotion) v) * (w : EuclidMotion) :=
  EuclidMotion.ext_of_apply fun x => by
    rw [EuclidMotion.mul_apply, EuclidMotion.mul_apply, EuclidMotion.transl_apply,
      EuclidMotion.transl_apply, stab_map_add]
theorem stab_mem_spatialVecs (w : timeStabilizer) {v : R4} (hv : v ∈ spatialVecs) :
    (w : EuclidMotion) v ∈ spatialVecs :=
  (stab_apply_three w v).trans hv
theorem transl_image_upperHalf {v : R4} (hv : 0 ≤ v 3) :
    EuclidMotion.transl v '' upperHalf ⊆ upperHalf := by
  rintro _ ⟨x, hx, rfl⟩
  exact add_pos_of_pos_of_nonneg hx hv
theorem stab_image_upperHalf (w : timeStabilizer) :
    (w : EuclidMotion) '' upperHalf ⊆ upperHalf := by
  rintro _ ⟨x, hx, rfl⟩
  change 0 < (w : EuclidMotion) x 3
  rw [stab_apply_three]
  exact hx
end Group
section OneFunctional
variable {c : SharpScale} {S : ConnFamily} (h : Inputs) (σ : EuclidFunctionalWithRecon c S)
theorem norm_isUnitaryMap_apply {𝒦 : Type} [NormedAddCommGroup 𝒦] [InnerProductSpace ℂ 𝒦]
    {V : 𝒦 →ₗ[ℂ] 𝒦} (hV : IsUnitaryMap V) (x : 𝒦) : ‖V x‖ = ‖x‖ := by
  have e₁ := inner_self_eq_norm_sq (𝕜 := ℂ) (V x)
  have e₂ := inner_self_eq_norm_sq (𝕜 := ℂ) x
  rw [hV.inner_map_map] at e₁
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (e₁.symm.trans e₂)
def rotCLM (w : timeStabilizer) : σ.space →L[ℂ] σ.space :=
  (σ.recon.rotOp w).mkContinuous 1 fun x => by
    rw [one_mul, norm_isUnitaryMap_apply (σ.recon.rotOp_unitary w)]
theorem clm_ext_cls {A B : σ.space →L[ℂ] σ.space}
    (hAB : ∀ F, A (σ.recon.cls F) = B (σ.recon.cls F)) : A = B :=
  DFunLike.coe_injective
    (σ.recon.denseRange_cls.equalizer A.continuous B.continuous (funext hAB))
theorem classOrZero_eq_cls {G : FreeSep} (hG : G ∈ finCombIn upperHalf) :
    readClass σ.recon.cls G = σ.recon.cls ⟨G, hG⟩ :=
  dif_pos hG
theorem heatSemigroup_classOrZero {t : ℝ} (ht : 0 ≤ t) {G : FreeSep}
    (hG : G ∈ finCombIn upperHalf) :
    σ.heatSemigroup t (readClass σ.recon.cls G) =
      readClass σ.recon.cls ((EuclidMotion.transl (t • timeVec)).actFree G) := by
  rw [classOrZero_eq_cls σ hG]
  exact σ.recon.expHam_cls t ht ⟨G, hG⟩
theorem translOp_classOrZero {v : R4} (hv : v ∈ spatialVecs) {G : FreeSep}
    (hG : G ∈ finCombIn upperHalf) :
    σ.translOp v (readClass σ.recon.cls G) =
      readClass σ.recon.cls ((EuclidMotion.transl v).actFree G) := by
  rw [classOrZero_eq_cls σ hG]
  exact σ.recon.transl_cls v hv ⟨G, hG⟩
theorem rotCLM_classOrZero (w : timeStabilizer) {G : FreeSep}
    (hG : G ∈ finCombIn upperHalf) :
    rotCLM σ w (readClass σ.recon.cls G) =
      readClass σ.recon.cls ((w : EuclidMotion).actFree G) := by
  rw [classOrZero_eq_cls σ hG]
  exact σ.recon.rotOp_cls w ⟨G, hG⟩
include h
omit σ in
theorem actFree_mem_finCombIn (r : EuclidMotion) (hr : r '' upperHalf ⊆ upperHalf)
    {F : FreeSep} (hF : F ∈ finCombIn upperHalf) :
    r.actFree F ∈ finCombIn upperHalf := by
  have hO : IsOpen upperHalf := isOpen_lt continuous_const (continuous_apply 3)
  have hb := ((h.listRules.2.1 r _ hO).2.2).mapsTo hF
  have hs : {X : sepAll | X.1 ∈ sepIn (r '' upperHalf)} ⊆
      {X : sepAll | X.1 ∈ sepIn upperHalf} :=
    fun X hX => ⟨hX.1, fun f hf => (hX.2 f hf).trans hr⟩
  exact Finsupp.supported_mono hs hb
omit σ in
theorem actFree_actFree (r r' : EuclidMotion) (F : FreeSep) :
    r.actFree (r'.actFree F) = (r * r').actFree F :=
  (h.listRules.2.2.1 r r' F).1
omit h σ in
theorem timeVec_smul_three_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ (t • timeVec) 3 := by
  simpa [PeriodicLattice.coordVec] using ht
theorem rotCLM_mul_heatSemigroup {t : ℝ} (ht : 0 ≤ t) (w : timeStabilizer) :
    rotCLM σ w * σ.heatSemigroup t = σ.heatSemigroup t * rotCLM σ w :=
  clm_ext_cls σ fun F => by
    have e₀ := (classOrZero_eq_cls σ F.2).symm
    change rotCLM σ w (σ.heatSemigroup t (σ.recon.cls F)) =
      σ.heatSemigroup t (rotCLM σ w (σ.recon.cls F))
    have hT := actFree_mem_finCombIn h _ (transl_image_upperHalf (timeVec_smul_three_nonneg ht))
      F.2
    have hW := actFree_mem_finCombIn h _ (stab_image_upperHalf w) F.2
    rw [e₀, heatSemigroup_classOrZero σ ht F.2, rotCLM_classOrZero σ w hT,
      rotCLM_classOrZero σ w F.2, heatSemigroup_classOrZero σ ht hW,
      actFree_actFree h, actFree_actFree h, stab_mul_transl, stab_smul_timeVec]
theorem rotCLM_mul_translOp {v : R4} (hv : v ∈ spatialVecs) (w : timeStabilizer) :
    rotCLM σ w * σ.translOp v = σ.translOp ((w : EuclidMotion) v) * rotCLM σ w :=
  clm_ext_cls σ fun F => by
    have e₀ := (classOrZero_eq_cls σ F.2).symm
    change rotCLM σ w (σ.translOp v (σ.recon.cls F)) =
      σ.translOp ((w : EuclidMotion) v) (rotCLM σ w (σ.recon.cls F))
    have hT := actFree_mem_finCombIn h _ (transl_image_upperHalf (le_of_eq (Eq.symm hv))) F.2
    have hW := actFree_mem_finCombIn h _ (stab_image_upperHalf w) F.2
    rw [e₀, translOp_classOrZero σ hv F.2, rotCLM_classOrZero σ w hT,
      rotCLM_classOrZero σ w F.2, translOp_classOrZero σ (stab_mem_spatialVecs w hv) hW,
      actFree_actFree h, actFree_actFree h, stab_mul_transl]
theorem rotCLM_mul_rotCLM (w w' : timeStabilizer) :
    rotCLM σ w * rotCLM σ w' = rotCLM σ (w * w') :=
  clm_ext_cls σ fun F => by
    have e₀ := (classOrZero_eq_cls σ F.2).symm
    change rotCLM σ w (rotCLM σ w' (σ.recon.cls F)) = rotCLM σ (w * w') (σ.recon.cls F)
    have hW := actFree_mem_finCombIn h _ (stab_image_upperHalf w') F.2
    rw [e₀, rotCLM_classOrZero σ w' F.2, rotCLM_classOrZero σ w hW,
      rotCLM_classOrZero σ (w * w') F.2, actFree_actFree h]
    rfl
def rotatedJointMeasure (σ : EuclidFunctionalWithRecon c S)
    (w : timeStabilizer) : SpectralMeasure EMPoints σ.space :=
  σ.jointMeasure.pushforward (by norm_num) MeasurableSet.univ (rotPoint w⁻¹)
    (measurable_rotPoint w⁻¹)
theorem spectralIntegralOp_rotatedJointMeasure (w : timeStabilizer) {g : EMPoints → ℂ}
    (hg : Measurable g) :
    spectralIntegralOp (rotatedJointMeasure σ w) g =
      spectralIntegralOp σ.jointMeasure (g ∘ rotPoint w⁻¹) :=
  spectralIntegralOp_eq_of_integralsAgree h _ _ hg (hg.comp (measurable_rotPoint w⁻¹))
    ((h.calculus σ.space 4 EMPoints σ.jointMeasure).2.2.2.2.1.integral_image
      (by norm_num) MeasurableSet.univ _ _ g hg)
theorem integralOpOn_rotatedJointMeasure (w : timeStabilizer) {t : ℝ} (ht : 0 ≤ t) {v : R4}
    (hv : v ∈ spatialVecs) :
    (rotatedJointMeasure σ w).integralOpOn nonnegEnergy (laplaceFourierKernel t v) =
      σ.heatSemigroup t * σ.translOp ((w : EuclidMotion) v) := by
  rw [heatSemigroup_mul_translOp h σ ht]
  have e := spectralIntegralOp_rotatedJointMeasure h σ w (measurable_zeroExtend_kernel t v)
  rw [zeroExtend_kernel_comp_rotPoint w hv] at e
  exact integralOp_eq_of_spectralIntegralOp_eq h _ _ (measurable_zeroExtend_kernel t v)
    (isBoundedFn_zeroExtend_kernel ht v) (measurable_zeroExtend_kernel t _)
    (isBoundedFn_zeroExtend_kernel ht _) e
theorem rotatedJointMeasure_eq_unitaryPushforward (w : timeStabilizer)
    (Δ : BorelSubsets EMPoints) :
    (rotatedJointMeasure σ w Δ : σ.space →ₗ[ℂ] σ.space) =
      σ.jointMeasure.unitaryPushforward (σ.recon.rotOp_unitary w) Δ := by
  have hV := σ.recon.rotOp_unitary w
  refine spectralMeasureUniqueness h σ σ.space _ hV (rotatedJointMeasure σ w) ?_ ?_ Δ
  · exact jointMeasure_isCarriedBy_nonnegEnergy h σ
  · intro k v hv
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    rw [integralOpOn_rotatedJointMeasure h σ w hk hv]
    refine LinearMap.ext fun x => ?_
    have hx : rotCLM σ w (hV.inv x) = x := hV.toLinearEquiv.apply_symm_apply x
    have e₁ : rotCLM σ w (σ.translOp v (hV.inv x)) =
        σ.translOp ((w : EuclidMotion) v) (rotCLM σ w (hV.inv x)) :=
      congrArg (fun T : σ.space →L[ℂ] σ.space => T (hV.inv x))
        (rotCLM_mul_translOp h σ hv w)
    have e₂ : rotCLM σ w (σ.heatSemigroup k (σ.translOp v (hV.inv x))) =
        σ.heatSemigroup k (rotCLM σ w (σ.translOp v (hV.inv x))) :=
      congrArg (fun T : σ.space →L[ℂ] σ.space =>
        T (σ.translOp v (hV.inv x))) (rotCLM_mul_heatSemigroup h σ hk w)
    change σ.heatSemigroup k (σ.translOp ((w : EuclidMotion) v) x) =
      rotCLM σ w (σ.heatSemigroup k (σ.translOp v (hV.inv x)))
    rw [e₂, e₁, hx]
theorem conjOp_spectralIntegralOp (w : timeStabilizer) {g : EMPoints → ℂ} (hg : Measurable g) :
    OperatorTransport.conjOp (σ.recon.rotOp_unitary w)
        (spectralIntegralOp σ.jointMeasure g) =
      spectralIntegralOp σ.jointMeasure (g ∘ rotPoint w⁻¹) := by
  obtain ⟨E', h₁, -, h₃⟩ := (h.calculus σ.space 4 EMPoints σ.jointMeasure).2.2.2.2.2.1
    σ.space _ (σ.recon.rotOp_unitary w)
  have hE : E' = rotatedJointMeasure σ w := ext_apply fun Δ =>
    ContinuousLinearMap.coe_injective
      ((h₁ Δ).trans (rotatedJointMeasure_eq_unitaryPushforward h σ w Δ).symm)
  rw [← h₃ g hg, hE]
  exact spectralIntegralOp_rotatedJointMeasure h σ w hg
theorem rotationCovariance : σ.RotationCovariance := by
  refine ⟨fun t ht w => ?_, fun w v hv => ?_, fun w w' => ?_, fun w Δ => ?_, fun w => ?_,
    fun w n _ => ?_⟩
  · exact LinearMap.ext fun x => congrArg
      (fun T : σ.space →L[ℂ] σ.space => T x) (rotCLM_mul_heatSemigroup h σ ht w)
  · refine LinearMap.ext fun x => ?_
    have hV := σ.recon.rotOp_unitary w
    have hx : rotCLM σ w (hV.inv x) = x := hV.toLinearEquiv.apply_symm_apply x
    have e₁ : rotCLM σ w (σ.translOp v (hV.inv x)) =
        σ.translOp ((w : EuclidMotion) v) (rotCLM σ w (hV.inv x)) :=
      congrArg (fun T : σ.space →L[ℂ] σ.space => T (hV.inv x))
        (rotCLM_mul_translOp h σ hv w)
    rw [hx] at e₁
    exact e₁
  · exact LinearMap.ext fun x => congrArg
      (fun T : σ.space →L[ℂ] σ.space => T x) (rotCLM_mul_rotCLM h σ w w')
  · have hm : MeasurableSet (rotPoint w '' Δ.1) := by
      rw [image_rotPoint]
      exact measurable_rotPoint w⁻¹ Δ.2
    refine ⟨hm, (rotatedJointMeasure_eq_unitaryPushforward h σ w Δ).symm.trans ?_⟩
    exact congrArg (fun D : BorelSubsets EMPoints =>
      (σ.jointMeasure D : σ.space →ₗ[ℂ] σ.space))
      (Subtype.ext (image_rotPoint w Δ.1).symm)
  · have e := ham_eq_spectralIntegralOp h σ
    have hg : Measurable fun p : EMPoints => ((energyOf p : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp measurable_energyOf
    have e₁ := conjOp_spectralIntegralOp h σ w hg
    rw [← e] at e₁
    exact e₁.trans e.symm
  · have hg : Measurable fun p : EMPoints => ((dot3 n (momentumOf p) : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp (measurable_dot3_momentumOf n)
    have e₁ := conjOp_spectralIntegralOp h σ w hg
    have e₂ : ((fun p : EMPoints => ((dot3 n (momentumOf p) : ℝ) : ℂ)) ∘ rotPoint w⁻¹) =
        fun p => ((dot3 (rotSpatial w n) (momentumOf p) : ℝ) : ℂ) := by
      funext p
      rw [dot3_rotSpatial]
      rfl
    rw [e₂] at e₁
    exact e₁
end OneFunctional
theorem reconstructionBasicFacts (hCalculus : SpectralMeasureCalculus.CalculusTheorem)
    (hJoint : JointSpectralGenerators.JointMeasureGeneratorsCommutation)
    (hResolved : ResolvedFacts.DiagonalizedFacts)
    (hAll : SelfAdjointResolution.SelfAdjointDiagonalizationTheorem)
    (hTransform : FiniteMeasureUniqueness.TransformDeterminesMeasure)
    (hValues : CenteredInitialValues.InitialValues)
    (hTuples : TupleRules.TupleSpanActionRules) : ReconstructionBasicFacts := by
  intro c S σ ℋ _ _ _ R
  have h : Inputs := ⟨hCalculus, hJoint, hResolved, hAll, hTransform, hValues, hTuples⟩
  exact ⟨spectralGeneratorsAndKernel h _, translUnitaryGroup h _,
    spectralMeasureUniqueness h _, vacuumInvariance h _, rotationCovariance h _⟩
end YangMills.Construction.EuclideanFunctionals.ReconstructionFactsProof
