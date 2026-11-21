import YangMills.Construction.Lattice.FormOnTheLieAlgebraAndTransposesProof
import YangMills.Construction.Towers.KernelsOfThreeMapsOfATowerProof
import YangMills.Construction.Towers.PlaquettesOfABond
import YangMills.Construction.Towers.SecondDifferentialOfTheActionAsAKernel
import YangMills.Construction.Towers.SumOverFinitelyManyPlaquettes
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.HessianKernel
open PeriodicOperators (KernelMatrix ApplySummableAt applyKernel)
open Matrices
section OneFace
def wilsonTerm (V Y : Fin 4 → ComplexMatrix2) : ℂ :=
  1 - (1 / 2) * ComplexMatrix2.fullTrace (ComplexMatrix2.matExp (Complex.I • Y 0) * V 0 *
    (ComplexMatrix2.matExp (Complex.I • Y 1) * V 1) *
    (ComplexMatrix2.matExp (Complex.I • Y 2) * V 2)⁻¹ *
    (ComplexMatrix2.matExp (Complex.I • Y 3) * V 3)⁻¹)
theorem contDiff_matExp : ContDiff ℂ 2 (fun Z : ComplexMatrix2 => ComplexMatrix2.matExp Z) :=
  contDiff_iff_contDiffAt.2 fun Z => (NormedSpace.exp_analytic (𝕂 := ℂ) Z).contDiffAt
theorem inv_matExp_smul_mul (Y V : ComplexMatrix2) :
    (ComplexMatrix2.matExp (Complex.I • Y) * V)⁻¹ =
      V⁻¹ * ComplexMatrix2.matExp (-(Complex.I • Y)) := by
  have hneg : ComplexMatrix2.matExp (-(Complex.I • Y)) =
      (ComplexMatrix2.matExp (Complex.I • Y))⁻¹ :=
    Matrix.exp_neg (Complex.I • Y)
  rw [Matrix.mul_inv_rev, hneg]
theorem wilsonTerm_contDiff (V : Fin 4 → ComplexMatrix2) : ContDiff ℂ 2 (wilsonTerm V) := by
  have hY : ∀ i : Fin 4,
      ContDiff ℂ 2 (fun Y : Fin 4 → ComplexMatrix2 => ComplexMatrix2.matExp (Complex.I • Y i)) :=
    fun i => contDiff_matExp.comp ((contDiff_apply ℂ ComplexMatrix2 i).const_smul Complex.I)
  have hY' : ∀ i : Fin 4,
      ContDiff ℂ 2 (fun Y : Fin 4 → ComplexMatrix2 =>
        ComplexMatrix2.matExp (-(Complex.I • Y i))) :=
    fun i => contDiff_matExp.comp ((contDiff_apply ℂ ComplexMatrix2 i).const_smul Complex.I).neg
  have htr : ContDiff ℂ 2 (fun X : ComplexMatrix2 => ComplexMatrix2.fullTrace X) :=
    (LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin 2) ℂ ℂ)).contDiff
  have hprod : ContDiff ℂ 2 (fun Y : Fin 4 → ComplexMatrix2 =>
      ComplexMatrix2.matExp (Complex.I • Y 0) * V 0 *
        (ComplexMatrix2.matExp (Complex.I • Y 1) * V 1) *
        ((V 2)⁻¹ * ComplexMatrix2.matExp (-(Complex.I • Y 2))) *
        ((V 3)⁻¹ * ComplexMatrix2.matExp (-(Complex.I • Y 3)))) :=
    ((((hY 0).mul contDiff_const).mul ((hY 1).mul contDiff_const)).mul
      (contDiff_const.mul (hY' 2))).mul (contDiff_const.mul (hY' 3))
  have hfun : ContDiff ℂ 2 (fun Y : Fin 4 → ComplexMatrix2 =>
      (1 : ℂ) - (1 / 2 : ℂ) * ComplexMatrix2.fullTrace
        (ComplexMatrix2.matExp (Complex.I • Y 0) * V 0 *
          (ComplexMatrix2.matExp (Complex.I • Y 1) * V 1) *
          ((V 2)⁻¹ * ComplexMatrix2.matExp (-(Complex.I • Y 2))) *
          ((V 3)⁻¹ * ComplexMatrix2.matExp (-(Complex.I • Y 3))))) :=
    contDiff_const.sub (contDiff_const.mul (htr.comp hprod))
  have heq : wilsonTerm V = fun Y : Fin 4 → ComplexMatrix2 =>
      (1 : ℂ) - (1 / 2 : ℂ) * ComplexMatrix2.fullTrace
        (ComplexMatrix2.matExp (Complex.I • Y 0) * V 0 *
          (ComplexMatrix2.matExp (Complex.I • Y 1) * V 1) *
          ((V 2)⁻¹ * ComplexMatrix2.matExp (-(Complex.I • Y 2))) *
          ((V 3)⁻¹ * ComplexMatrix2.matExp (-(Complex.I • Y 3)))) := by
    funext Y
    simp only [wilsonTerm, inv_matExp_smul_mul]
  rw [heq]
  exact hfun
def wilsonHessian (V : Fin 4 → ComplexMatrix2) :
    (Fin 4 → ComplexMatrix2) →L[ℂ] (Fin 4 → ComplexMatrix2) →L[ℂ] ℂ :=
  fderiv ℂ (fderiv ℂ (wilsonTerm V)) 0
theorem wilsonHessian_symm (V v w : Fin 4 → ComplexMatrix2) :
    wilsonHessian V v w = wilsonHessian V w v :=
  ((wilsonTerm_contDiff V).contDiffAt.isSymmSndFDerivAt (by simp)) v w
section AffineLines
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
theorem hasDerivAt_affine_line {g : E → ℂ} (hg : ContDiff ℂ 2 g) (s : ℂ) (v w : E) :
    HasDerivAt (fun t : ℂ => g (s • v + t • w)) (fderiv ℂ g (s • v) w) 0 := by
  have hg1 : HasFDerivAt g (fderiv ℂ g (s • v)) (s • v) :=
    ((hg.differentiable (by norm_num)) _).hasFDerivAt
  have hline : HasDerivAt (fun t : ℂ => s • v + t • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const w).const_add (s • v)
  exact hg1.comp_hasDerivAt_of_eq (0 : ℂ) hline (by simp)
theorem hasDerivAt_fderiv_ray {g : E → ℂ} (hg : ContDiff ℂ 2 g) (v w : E) :
    HasDerivAt (fun s : ℂ => fderiv ℂ g (s • v) w) (fderiv ℂ (fderiv ℂ g) 0 v w) 0 := by
  have hd : Differentiable ℂ (fderiv ℂ g) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hg1 : HasFDerivAt (fderiv ℂ g) (fderiv ℂ (fderiv ℂ g) 0) 0 := (hd _).hasFDerivAt
  have hray : HasDerivAt (fun s : ℂ => s • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).smul_const v
  have hcomp := hg1.comp_hasDerivAt_of_eq (0 : ℂ) hray (by simp)
  exact ((ContinuousLinearMap.apply ℂ ℂ w).hasFDerivAt).comp_hasDerivAt (0 : ℂ) hcomp
end AffineLines
theorem mixedDeriv_finset_sum {P : Type} (Ω : Finset P) (V v w : P → Fin 4 → ComplexMatrix2) :
    deriv (fun s : ℂ => deriv (fun t : ℂ =>
        ∑ p ∈ Ω, wilsonTerm (V p) (s • v p + t • w p)) 0) 0 =
      ∑ p ∈ Ω, wilsonHessian (V p) (v p) (w p) := by
  have hinner : ∀ s : ℂ, deriv (fun t : ℂ =>
      ∑ p ∈ Ω, wilsonTerm (V p) (s • v p + t • w p)) 0 =
      ∑ p ∈ Ω, fderiv ℂ (wilsonTerm (V p)) (s • v p) (w p) := fun s =>
    (HasDerivAt.fun_sum fun p _ =>
      hasDerivAt_affine_line (wilsonTerm_contDiff (V p)) s (v p) (w p)).deriv
  simp only [hinner]
  exact (HasDerivAt.fun_sum fun p _ =>
    hasDerivAt_fderiv_ray (wilsonTerm_contDiff (V p)) (v p) (w p)).deriv
theorem mixedDeriv_congr_nhds {φ ψ : ℂ × ℂ → ℂ}
    (h : ∀ᶠ q in 𝓝 ((0 : ℂ), (0 : ℂ)), φ q = ψ q) :
    deriv (fun s : ℂ => deriv (fun t : ℂ => φ (s, t)) 0) 0 =
      deriv (fun s : ℂ => deriv (fun t : ℂ => ψ (s, t)) 0) 0 := by
  have hcurry := h.curry_nhds
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [hcurry] with s hs
  exact Filter.EventuallyEq.deriv_eq hs
end OneFace
section GeneralIndex
variable {σ P : Type} (c : P → Fin 4 → σ) (u : σ → ComplexMatrix2)
def cornerValues (p : P) (f : σ → ComplexMatrix2) : Fin 4 → ComplexMatrix2 := fun i => f (c p i)
def faceHessianTerm (p : P) (f f' : σ → ComplexMatrix2) : ℂ :=
  wilsonHessian (cornerValues c p u) (cornerValues c p f) (cornerValues c p f')
def hessianFinsum (f f' : σ → ComplexMatrix2) : ℂ := ∑ᶠ p, faceHessianTerm c u p f f'
variable {c u}
theorem cornerValues_smul_add (p : P) (z : ℂ) (f g : σ → ComplexMatrix2) :
    cornerValues c p (z • f + g) = z • cornerValues c p f + cornerValues c p g := rfl
theorem faceHessianTerm_eq_zero_left {p : P} {f : σ → ComplexMatrix2} (f' : σ → ComplexMatrix2)
    (h : ∀ i, f (c p i) = 0) : faceHessianTerm c u p f f' = 0 := by
  have hz : cornerValues c p f = 0 := funext h
  simp [faceHessianTerm, hz]
theorem faceHessianTerm_eq_zero_right {p : P} {f' : σ → ComplexMatrix2} (f : σ → ComplexMatrix2)
    (h : ∀ i, f' (c p i) = 0) : faceHessianTerm c u p f f' = 0 := by
  have hz : cornerValues c p f' = 0 := funext h
  simp [faceHessianTerm, hz]
theorem faceHessianTerm_comm (p : P) (f f' : σ → ComplexMatrix2) :
    faceHessianTerm c u p f f' = faceHessianTerm c u p f' f :=
  wilsonHessian_symm _ _ _
theorem faceHessianTerm_smul_add (p : P) (z : ℂ) (f g h : σ → ComplexMatrix2) :
    faceHessianTerm c u p (z • f + g) h = z * faceHessianTerm c u p f h + faceHessianTerm c u p g h := by
  simp [faceHessianTerm, cornerValues_smul_add]
theorem hessianFinsum_comm (f f' : σ → ComplexMatrix2) :
    hessianFinsum c u f f' = hessianFinsum c u f' f :=
  finsum_congr fun p => faceHessianTerm_comm p f f'
def facesMeetingSet (c : P → Fin 4 → σ) (F : Set σ) : Set P := {p | ∃ i, c p i ∈ F}
theorem hessianFinsum_eq_sum {f f' : σ → ComplexMatrix2} (Ω : Finset P)
    (hΩ : ∀ p, (∃ i, f (c p i) ≠ 0) → (∃ i, f' (c p i) ≠ 0) → p ∈ Ω) :
    hessianFinsum c u f f' = ∑ p ∈ Ω, faceHessianTerm c u p f f' := by
  refine finsum_eq_sum_of_support_subset _ fun p hp => ?_
  have hp' : faceHessianTerm c u p f f' ≠ 0 := hp
  refine Finset.mem_coe.2 (hΩ p ?_ ?_)
  · by_contra h
    push Not at h
    exact hp' (faceHessianTerm_eq_zero_left f' h)
  · by_contra h
    push Not at h
    exact hp' (faceHessianTerm_eq_zero_right f h)
def HasFiniteSupport (f : σ → ComplexMatrix2) : Prop := (Function.support f).Finite
theorem HasFiniteSupport.smul_add {f g : σ → ComplexMatrix2} (hf : HasFiniteSupport f)
    (hg : HasFiniteSupport g) (z : ℂ) : HasFiniteSupport (z • f + g) := by
  refine (hf.union hg).subset fun b hb => ?_
  by_contra h
  simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h
  exact hb (by simp [h.1, h.2])
theorem hessianFinsum_smul_add (hfin : ∀ F : Set σ, F.Finite → (facesMeetingSet c F).Finite)
    {f g h : σ → ComplexMatrix2} (hf : HasFiniteSupport f) (hg : HasFiniteSupport g) (z : ℂ) :
    hessianFinsum c u (z • f + g) h = z * hessianFinsum c u f h + hessianFinsum c u g h := by
  classical
  have hF := hfin _ (hf.union hg)
  have hΩ : ∀ p, (∃ i, f (c p i) ≠ 0) ∨ (∃ i, g (c p i) ≠ 0) → p ∈ hF.toFinset := by
    rintro p (⟨i, hi⟩ | ⟨i, hi⟩)
    · exact hF.mem_toFinset.2 ⟨i, Or.inl hi⟩
    · exact hF.mem_toFinset.2 ⟨i, Or.inr hi⟩
  rw [hessianFinsum_eq_sum hF.toFinset (f := z • f + g), hessianFinsum_eq_sum hF.toFinset (f := f),
    hessianFinsum_eq_sum hF.toFinset (f := g)]
  · simp only [faceHessianTerm_smul_add, Finset.sum_add_distrib, Finset.mul_sum]
  · exact fun p hp _ => hΩ p (Or.inr hp)
  · exact fun p hp _ => hΩ p (Or.inl hp)
  · rintro p ⟨i, hi⟩ _
    by_contra hp
    refine hi ?_
    have hf0 : f (c p i) = 0 := by
      by_contra hf0
      exact hp (hΩ p (Or.inl ⟨i, hf0⟩))
    have hg0 : g (c p i) = 0 := by
      by_contra hg0
      exact hp (hΩ p (Or.inr ⟨i, hg0⟩))
    simp [hf0, hg0]
theorem hessianFinsum_smul_add_right (hfin : ∀ F : Set σ, F.Finite → (facesMeetingSet c F).Finite)
    {f g h : σ → ComplexMatrix2} (hf : HasFiniteSupport f) (hg : HasFiniteSupport g) (z : ℂ) :
    hessianFinsum c u h (z • f + g) = z * hessianFinsum c u h f + hessianFinsum c u h g := by
  rw [hessianFinsum_comm, hessianFinsum_smul_add hfin hf hg, hessianFinsum_comm f,
    hessianFinsum_comm g]
def pauliDelta (ι : Fin 3 × σ) : σ → ComplexMatrix2 :=
  open Classical in fun b => if b = ι.2 then ComplexMatrix2.pauliFamily ι.1 else 0
def hessianKernelOf (c : P → Fin 4 → σ) (u : σ → ComplexMatrix2) :
    KernelMatrix (Fin 3 × σ) (Fin 3 × σ) :=
  fun ι' ι => hessianFinsum c u (pauliDelta ι') (pauliDelta ι)
theorem pauliDelta_hasFiniteSupport (ι : Fin 3 × σ) : HasFiniteSupport (pauliDelta ι) := by
  refine (Set.finite_singleton ι.2).subset fun b hb => ?_
  by_contra h
  have h' : b ≠ ι.2 := h
  exact hb (by simp [pauliDelta, h'])
theorem pauliFamily_mem_traceless (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
theorem hessianKernelOf_eq_zero (ι ι' : Fin 3 × σ)
    (h : ¬ ∃ p, (∃ i, c p i = ι.2) ∧ ∃ i, c p i = ι'.2) : hessianKernelOf c u ι ι' = 0 := by
  refine finsum_eq_zero_of_forall_eq_zero fun p => ?_
  by_cases h1 : ∃ i, c p i = ι.2
  · have h2 : ∀ i, c p i ≠ ι'.2 := fun i hi => h ⟨p, h1, i, hi⟩
    exact faceHessianTerm_eq_zero_right _ fun i => by simp [pauliDelta, h2 i]
  · have h2 : ∀ i, c p i ≠ ι.2 := fun i hi => h1 ⟨i, hi⟩
    exact faceHessianTerm_eq_zero_left _ fun i => by simp [pauliDelta, h2 i]
theorem hessianKernelOf_row_finite (hfin : ∀ F : Set σ, F.Finite → (facesMeetingSet c F).Finite)
    (ι : Fin 3 × σ) : {ι' : Fin 3 × σ | hessianKernelOf c u ι ι' ≠ 0}.Finite := by
  have hT := hfin {ι.2} (Set.finite_singleton _)
  have hB : (⋃ p ∈ facesMeetingSet c {ι.2}, Set.range (c p)).Finite :=
    hT.biUnion fun p _ => Set.finite_range _
  refine ((Set.finite_univ (α := Fin 3)).prod hB).subset fun ι' hι' => ?_
  by_contra hn
  refine hι' (hessianKernelOf_eq_zero ι ι' ?_)
  rintro ⟨p, ⟨i, hi⟩, i', hi'⟩
  exact hn ⟨Set.mem_univ _,
    Set.mem_biUnion (show p ∈ facesMeetingSet c {ι.2} from ⟨i, hi⟩) ⟨i', hi'⟩⟩
theorem hessianKernelOf_applySummable
    (hfin : ∀ F : Set σ, F.Finite → (facesMeetingSet c F).Finite)
    (g : Fin 3 × σ → ℂ) (ι : Fin 3 × σ) : ApplySummableAt (hessianKernelOf c u) g ι := by
  refine summable_of_finite_support
    ((hessianKernelOf_row_finite (u := u) hfin ι).subset fun ι' hι' => ?_)
  intro h
  exact hι' (by simp [show hessianKernelOf c u ι ι' = 0 from h])
theorem hessianKernelOf_symm (ι ι' : Fin 3 × σ) :
    hessianKernelOf c u ι ι' = hessianKernelOf c u ι' ι :=
  hessianFinsum_comm _ _
theorem pauliCoeff_values {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    pauliCoeff 0 X = (X 0 1 + X 1 0) / 2 ∧
      pauliCoeff 1 X = (X 1 0 - X 0 1) / (2 * Complex.I) ∧
      pauliCoeff 2 X = X 0 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [pauliCoeff, hX, OneLoop.pauliCoordinateEquiv]
theorem entry_one_one_eq_neg {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    X 1 1 = -X 0 0 := by apply _root_.YangMills.Construction.LieInnerProductProof.entry_one_one_of_mem_traceless <;> assumption
theorem sum_pauliCoeff_smul {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
theorem halfTrace_mul_pauliFamily {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (a : Fin 3) :
    ComplexMatrix2.halfTrace (X * ComplexMatrix2.pauliFamily a) = pauliCoeff a X := by
  obtain ⟨h0, h1, h2⟩ := pauliCoeff_values hX
  have h3 := entry_one_one_eq_neg hX
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hI0 : (2 * Complex.I) ≠ 0 := by simp
  have ht : ∀ Y : ComplexMatrix2, ComplexMatrix2.halfTrace (X * Y) =
      (1 / 2) * (X 0 0 * Y 0 0 + X 0 1 * Y 1 0 + X 1 0 * Y 0 1 + X 1 1 * Y 1 1) := by
    intro Y
    simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have e0 : ComplexMatrix2.pauliFamily 0 0 0 = 0 ∧ ComplexMatrix2.pauliFamily 0 0 1 = 1 ∧
      ComplexMatrix2.pauliFamily 0 1 0 = 1 ∧ ComplexMatrix2.pauliFamily 0 1 1 = 0 := by
    simp [ComplexMatrix2.pauliFamily, OneLoop.pauliX]
  have e1 : ComplexMatrix2.pauliFamily 1 0 0 = 0 ∧
      ComplexMatrix2.pauliFamily 1 0 1 = -Complex.I ∧
      ComplexMatrix2.pauliFamily 1 1 0 = Complex.I ∧ ComplexMatrix2.pauliFamily 1 1 1 = 0 := by
    simp [ComplexMatrix2.pauliFamily, OneLoop.pauliY]
  have e2 : ComplexMatrix2.pauliFamily 2 0 0 = 1 ∧ ComplexMatrix2.pauliFamily 2 0 1 = 0 ∧
      ComplexMatrix2.pauliFamily 2 1 0 = 0 ∧ ComplexMatrix2.pauliFamily 2 1 1 = -1 := by
    simp [ComplexMatrix2.pauliFamily, OneLoop.pauliZ]
  fin_cases a
  · change ComplexMatrix2.halfTrace (X * ComplexMatrix2.pauliFamily 0) = pauliCoeff 0 X
    rw [ht, h0, e0.1, e0.2.1, e0.2.2.1, e0.2.2.2]
    ring
  · change ComplexMatrix2.halfTrace (X * ComplexMatrix2.pauliFamily 1) = pauliCoeff 1 X
    rw [ht, h1, e1.1, e1.2.1, e1.2.2.1, e1.2.2.2, eq_div_iff hI0]
    linear_combination (X 0 1 - X 1 0) * hI
  · change ComplexMatrix2.halfTrace (X * ComplexMatrix2.pauliFamily 2) = pauliCoeff 2 X
    rw [ht, h2, e2.1, e2.2.1, e2.2.2.1, e2.2.2.2, h3]
    ring
theorem pauliCoeff_zero (a : Fin 3) : pauliCoeff a 0 = 0 := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_zero <;> assumption
theorem sum_toPauliCoeffs_smul_pauliDelta {f : σ → ComplexMatrix2} (hf : HasFiniteSupport f)
    (hs : ∀ b, f b ∈ ComplexMatrix2.traceless) :
    ∑ ι ∈ Finset.univ ×ˢ hf.toFinset, toPauliCoeffs f ι • pauliDelta ι = f := by
  classical
  funext b
  simp only [Finset.sum_apply, Pi.smul_apply, Finset.sum_product]
  by_cases hb : b ∈ hf.toFinset
  · have h : ∀ a : Fin 3, ∑ b' ∈ hf.toFinset, toPauliCoeffs f (a, b') • pauliDelta (a, b') b =
        pauliCoeff a (f b) • ComplexMatrix2.pauliFamily a := fun a => by
      rw [Finset.sum_eq_single_of_mem b hb]
      · simp [pauliDelta, toPauliCoeffs]
      · intro b' _ hne
        simp [pauliDelta, hne.symm]
    simp only [h]
    exact sum_pauliCoeff_smul (hs b)
  · have hz : f b = 0 := by
      by_contra h
      exact hb (hf.mem_toFinset.2 h)
    rw [hz]
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b' hb' => ?_
    have hne : b ≠ b' := fun h => hb (h ▸ hb')
    simp [pauliDelta, hne]
theorem hessianFinsum_zero_right (f : σ → ComplexMatrix2) : hessianFinsum c u f 0 = 0 :=
  finsum_eq_zero_of_forall_eq_zero fun _ => faceHessianTerm_eq_zero_right _ fun _ => rfl
theorem hessianFinsum_sum_right (hfin : ∀ F : Set σ, F.Finite → (facesMeetingSet c F).Finite)
    {I : Type} (h : σ → ComplexMatrix2) (s : Finset I) (a : I → ℂ) (g : I → σ → ComplexMatrix2)
    (hg : ∀ i, HasFiniteSupport (g i)) :
    HasFiniteSupport (∑ i ∈ s, a i • g i) ∧
      hessianFinsum c u h (∑ i ∈ s, a i • g i) = ∑ i ∈ s, a i * hessianFinsum c u h (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨?_, ?_⟩
    · simp [HasFiniteSupport]
    · simp [hessianFinsum_zero_right]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    refine ⟨(hg i).smul_add ih.1 (a i), ?_⟩
    rw [hessianFinsum_smul_add_right hfin (hg i) ih.1, ih.2]
theorem applyKernel_hessianKernelOf (hfin : ∀ F : Set σ, F.Finite → (facesMeetingSet c F).Finite)
    {f : σ → ComplexMatrix2} (hf : HasFiniteSupport f) (hs : ∀ b, f b ∈ ComplexMatrix2.traceless)
    (ι : Fin 3 × σ) :
    applyKernel (hessianKernelOf c u) (toPauliCoeffs f) ι = hessianFinsum c u (pauliDelta ι) f := by
  classical
  have h1 : applyKernel (hessianKernelOf c u) (toPauliCoeffs f) ι =
      ∑ ι' ∈ Finset.univ ×ˢ hf.toFinset, hessianKernelOf c u ι ι' * toPauliCoeffs f ι' := by
    refine tsum_eq_sum fun ι' hι' => ?_
    have hz : f ι'.2 = 0 := by
      by_contra h
      exact hι' (Finset.mem_product.2 ⟨Finset.mem_univ _, hf.mem_toFinset.2 h⟩)
    simp [toPauliCoeffs, hz, pauliCoeff_zero]
  have h2 := (hessianFinsum_sum_right (c := c) (u := u) hfin (pauliDelta ι)
    (Finset.univ ×ˢ hf.toFinset) (toPauliCoeffs f) pauliDelta pauliDelta_hasFiniteSupport).2
  rw [sum_toPauliCoeffs_smul_pauliDelta hf hs] at h2
  rw [h1, h2]
  exact Finset.sum_congr rfl fun ι' _ => mul_comm _ _
theorem halfTrace_mul_sum_smul (X : ComplexMatrix2) (x : Fin 3 → ℂ) :
    ComplexMatrix2.halfTrace (X * ∑ a, x a • ComplexMatrix2.pauliFamily a) =
      ∑ a, x a * ComplexMatrix2.halfTrace (X * ComplexMatrix2.pauliFamily a) := by
  simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Finset.mul_sum,
    Matrix.trace_sum, mul_smul_comm, Matrix.trace_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun a _ => by ring
theorem traceFinsumPairing_applyKernel
    (hfin : ∀ F : Set σ, F.Finite → (facesMeetingSet c F).Finite)
    {f f' : σ → ComplexMatrix2} (hf : HasFiniteSupport f)
    (hs : ∀ b, f b ∈ ComplexMatrix2.traceless) (hf' : HasFiniteSupport f')
    (hs' : ∀ b, f' b ∈ ComplexMatrix2.traceless) :
    traceFinsumPairing f (ofPauliCoeffs (applyKernel (hessianKernelOf c u) (toPauliCoeffs f'))) =
      hessianFinsum c u f f' := by
  classical
  have h1 : traceFinsumPairing f
      (ofPauliCoeffs (applyKernel (hessianKernelOf c u) (toPauliCoeffs f'))) =
      ∑ b ∈ hf.toFinset, ComplexMatrix2.halfTrace
        (f b * ofPauliCoeffs (applyKernel (hessianKernelOf c u) (toPauliCoeffs f')) b) := by
    refine finsum_eq_sum_of_support_subset _ fun b hb => ?_
    refine Finset.mem_coe.2 (hf.mem_toFinset.2 fun hz => hb ?_)
    simp [hz]
  have h2 := (hessianFinsum_sum_right (c := c) (u := u) hfin f' (Finset.univ ×ˢ hf.toFinset)
    (toPauliCoeffs f) pauliDelta pauliDelta_hasFiniteSupport).2
  rw [sum_toPauliCoeffs_smul_pauliDelta hf hs] at h2
  rw [h1, hessianFinsum_comm, h2, Finset.sum_product_right]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [ofPauliCoeffs, halfTrace_mul_sum_smul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [applyKernel_hessianKernelOf hfin hf' hs', halfTrace_mul_pauliFamily (hs b),
    hessianFinsum_comm]
  exact mul_comm _ _
theorem isSymmBilinearOn_of_hessianFinsum {α : Type} {𝒮 : Set (α → ComplexMatrix2)}
    {Q : (α → ComplexMatrix2) → (α → ComplexMatrix2) → ℂ}
    (hfin : ∀ F : Set σ, F.Finite → (facesMeetingSet c F).Finite)
    (rd : (α → ComplexMatrix2) → σ → ComplexMatrix2)
    (hrd : ∀ (z : ℂ) (E₁ E₂ : α → ComplexMatrix2), rd (z • E₁ + E₂) = z • rd E₁ + rd E₂)
    (hadd : ∀ (z : ℂ), ∀ E₁ ∈ 𝒮, ∀ E₂ ∈ 𝒮, z • E₁ + E₂ ∈ 𝒮)
    (hfs : ∀ E ∈ 𝒮, HasFiniteSupport (rd E))
    (hQ : ∀ B ∈ 𝒮, ∀ B' ∈ 𝒮, Q B B' = hessianFinsum c u (rd B) (rd B')) :
    IsSymmBilinearOn 𝒮 Q := by
  intro z E₁ h₁ E₂ h₂ E₃ h₃
  have hc := hadd z E₁ h₁ E₂ h₂
  refine ⟨?_, ?_, ?_⟩
  · rw [hQ _ hc _ h₃, hQ _ h₁ _ h₃, hQ _ h₂ _ h₃, hrd]
    exact hessianFinsum_smul_add hfin (hfs _ h₁) (hfs _ h₂) z
  · rw [hQ _ h₃ _ hc, hQ _ h₃ _ h₁, hQ _ h₃ _ h₂, hrd]
    exact hessianFinsum_smul_add_right hfin (hfs _ h₁) (hfs _ h₂) z
  · rw [hQ _ h₁ _ h₃, hQ _ h₃ _ h₁]
    exact hessianFinsum_comm _ _
end GeneralIndex
section Torus
variable {L n k j : ℕ}
theorem torus_forwardFrom_positive (x : Vertex L n k j) (μ : Fin 4) :
    (PeriodicLattice.Bond.forwardFrom x μ).IsPositivelyOriented :=
  ⟨μ, by simp [PeriodicLattice.Bond.forwardFrom]⟩
def torusFaceCorners (p : Face L n k j) : Fin 4 → PositiveEdge L n k j :=
  ![⟨PeriodicLattice.Bond.forwardFrom p.origin p.firstAxis, torus_forwardFrom_positive _ _⟩,
    ⟨PeriodicLattice.Bond.forwardFrom (p.origin + PeriodicLattice.unitStep L n _ p.firstAxis)
      p.secondAxis, torus_forwardFrom_positive _ _⟩,
    ⟨PeriodicLattice.Bond.forwardFrom (p.origin + PeriodicLattice.unitStep L n _ p.secondAxis)
      p.firstAxis, torus_forwardFrom_positive _ _⟩,
    ⟨PeriodicLattice.Bond.forwardFrom p.origin p.secondAxis, torus_forwardFrom_positive _ _⟩]
theorem torusFaceCorners_mem (p : Face L n k j) (i : Fin 4) :
    (torusFaceCorners p i : Edge L n k j) ∈ faceEdges p := by
  fin_cases i <;> simp [torusFaceCorners, faceEdges]
theorem torus_positive_or_opposite (b : Edge L n k j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
theorem torus_not_positive_opposite (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) (b : Edge L n k j)
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_not_both_positive <;> assumption
theorem torus_complexFaceTerm_eq
    (hrev : ∀ b : Edge L n k j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    (X U : Edge L n k j → ComplexMatrix2) (p : Face L n k j) :
    complexFaceTerm (PeriodicLattice.expTwist X U) p =
      wilsonTerm (cornerValues torusFaceCorners p (restrictToPositiveEdges U))
        (cornerValues torusFaceCorners p (restrictToPositiveEdges X)) := by
  have e : ∀ b : Edge L n k j, b.IsPositivelyOriented →
      PeriodicLattice.expTwist X U b = ComplexMatrix2.matExp (Complex.I • X b) * U b :=
    fun b hb => if_pos hb
  have r : ∀ b : Edge L n k j, b.IsPositivelyOriented →
      PeriodicLattice.expTwist X U b.opposite =
        (ComplexMatrix2.matExp (Complex.I • X b) * U b)⁻¹ :=
    fun b hb => if_neg (hrev b hb)
  simp only [complexFaceTerm, PeriodicLattice.plaquetteEnergy,
    PeriodicLattice.plaquetteHolonomy, PeriodicLattice.pathHolonomy,
    PeriodicLattice.Plaquette.boundaryBonds, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]
  rw [e _ (torus_forwardFrom_positive _ _), e _ (torus_forwardFrom_positive _ _),
    r _ (torus_forwardFrom_positive _ _), r _ (torus_forwardFrom_positive _ _)]
  simp [wilsonTerm, cornerValues, torusFaceCorners, restrictToPositiveEdges, mul_assoc]
theorem torus_complexActionHessian_eq [Finite (Face L n k j)]
    (hrev : ∀ b : Edge L n k j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    (U B B' : Edge L n k j → ComplexMatrix2) :
    complexActionHessian U B B' =
      hessianFinsum torusFaceCorners (restrictToPositiveEdges U) (restrictToPositiveEdges B)
        (restrictToPositiveEdges B') := by
  classical
  letI := Fintype.ofFinite (Face L n k j)
  have hφ : ∀ X : Edge L n k j → ComplexMatrix2,
      complexAction (PeriodicLattice.expTwist X U) =
        ∑ p, wilsonTerm (cornerValues torusFaceCorners p (restrictToPositiveEdges U))
          (cornerValues torusFaceCorners p (restrictToPositiveEdges X)) := fun X => by
    rw [complexAction, finsum_eq_sum_of_fintype]
    exact Finset.sum_congr rfl fun p _ => torus_complexFaceTerm_eq hrev X U p
  rw [hessianFinsum, finsum_eq_sum_of_fintype]
  simp only [complexActionHessian, holLeftSecondDeriv, mixedDirectionalDeriv, hφ]
  exact mixedDeriv_finset_sum Finset.univ
    (fun p => cornerValues torusFaceCorners p (restrictToPositiveEdges U))
    (fun p => cornerValues torusFaceCorners p (restrictToPositiveEdges B))
    (fun p => cornerValues torusFaceCorners p (restrictToPositiveEdges B'))
theorem torus_extendOddly_pos (f : Edge L n k j → ComplexMatrix2) (b : Edge L n k j)
    (hb : b.IsPositivelyOriented) : extendOddly f b = f b := if_pos hb
theorem torus_restrict_basisForm (a : Fin 3) (b : PositiveEdge L n k j) :
    restrictToPositiveEdges (basisForm a b) = pauliDelta (a, b) := by
  classical
  funext b'
  have e : restrictToPositiveEdges (basisForm a b) b' =
      if b'.1 = b.1 then ComplexMatrix2.pauliFamily a else 0 :=
    if_pos b'.2
  rw [e]
  simp [pauliDelta, Subtype.ext_iff]
theorem holdsOnTorus (hN : FaceEdgeFinsets.HoldsOnTorus L n k j)
    (hS : FacesContainingEdge.Periodic L n k j)
    (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) :
    HoldsOnTorus L n k j := by
  intro U _
  have hiff : ∀ b : Edge L n k j, b.opposite.IsPositivelyOriented ↔ ¬ b.IsPositivelyOriented :=
    fun b => ⟨fun h h' => torus_not_positive_opposite hA hL hn hj b h' h,
      fun h => (torus_positive_or_opposite b).resolve_left h⟩
  have hrev : ∀ b : Edge L n k j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented :=
    fun b hb h => (hiff b).1 h hb
  haveI hpl : Finite (Face L n k j) := Set.finite_univ_iff.1 hN.2.2.2.1
  haveI hbo : Finite (Edge L n k j) := (hA L hL n j k hn hj).2.1.2.2.2.2.2.2.2.2.2.2.2.1
  have hfin : ∀ F : Set (PositiveEdge L n k j), F.Finite →
      (facesMeetingSet torusFaceCorners F).Finite :=
    fun F hF => (hS.2.2 F hF).subset fun p ⟨i, hi⟩ => ⟨_, hi, torusFaceCorners_mem p i⟩
  have hfs : ∀ f : PositiveEdge L n k j → ComplexMatrix2, HasFiniteSupport f :=
    fun f => Set.toFinite _
  have hsl : ∀ E ∈ complexEdgeForms L n k j, ∀ b,
      restrictToPositiveEdges E b ∈ ComplexMatrix2.traceless :=
    fun E hE b => hE.1 b.1 b.2
  have hK : complexHessianKernel U =
      hessianKernelOf torusFaceCorners (restrictToPositiveEdges U) := by
    funext ι' ι
    change complexActionHessian U _ _ = _
    rw [torus_complexActionHessian_eq hrev, torus_restrict_basisForm, torus_restrict_basisForm]
    rfl
  have hop : ∀ B : Edge L n k j → ComplexMatrix2,
      restrictToPositiveEdges (complexHessianOperator U B) =
        ofPauliCoeffs (applyKernel (hessianKernelOf torusFaceCorners (restrictToPositiveEdges U))
          (toPauliCoeffs (restrictToPositiveEdges B))) := fun B => by
    funext b
    have e : restrictToPositiveEdges (complexHessianOperator U B) b =
        ofPauliCoeffs (applyKernel (complexHessianKernel U)
          (toPauliCoeffs (restrictToPositiveEdges B))) b := by
      change complexHessianOperator U B b.1 = _
      rw [complexHessianOperator, torus_extendOddly_pos _ _ b.2]
      exact dif_pos b.2
    rw [e, hK]
  refine ⟨isSymmBilinearOn_of_hessianFinsum hfin restrictToPositiveEdges (fun _ _ _ => rfl)
      (fun z E₁ h₁ E₂ h₂ => (complexEdgeForms L n k j).add_mem
        ((complexEdgeForms L n k j).smul_mem z h₁) h₂) (fun _ _ => hfs _)
      (fun B _ B' _ => torus_complexActionHessian_eq hrev U B B'), ?_, ?_, ?_, ?_, ?_⟩
  · intro ι ι' h
    rw [hK]
    refine hessianKernelOf_eq_zero ι ι' ?_
    rintro ⟨p, ⟨i, hi⟩, i', hi'⟩
    exact h ⟨p, hi ▸ torusFaceCorners_mem p i, hi' ▸ torusFaceCorners_mem p i'⟩
  · rw [hK]
    exact hessianKernelOf_row_finite hfin
  · intro B _ ι
    rw [hK]
    exact hessianKernelOf_applySummable hfin _ ι
  · intro B hB B' hB'
    rw [edgeFormPairing, hop,
      traceFinsumPairing_applyKernel hfin (hfs _) (hsl B hB) (hfs _) (hsl B' hB'),
      torus_complexActionHessian_eq hrev]
  · rw [hK]
    exact fun ι ι' => hessianKernelOf_symm ι ι'
end Torus
section FullSpaceCase
open FaceEdgeFinsets.Unbounded (facesMeeting)
open FaceSum (faceSum faceTerm faceSumOfFamily)
variable {L k j : ℕ}
theorem full_forwardFrom_positive {a : ℝ} (x : InfiniteLattice.LatticePoint a) (μ : Fin 4) :
    (InfiniteLattice.Link.forwardFrom x μ).IsPositivelyOriented :=
  ⟨μ, by simp [InfiniteLattice.Link.forwardFrom]⟩
def fullFaceCorners (p : FullSpace.Face L k j) :
    Fin 4 → FullSpace.PositiveEdge (meshAt L k j) :=
  ![⟨InfiniteLattice.Link.forwardFrom p.corner p.lowAxis, full_forwardFrom_positive _ _⟩,
    ⟨InfiniteLattice.Link.forwardFrom (p.corner + InfiniteLattice.axisStep _ p.lowAxis)
      p.highAxis, full_forwardFrom_positive _ _⟩,
    ⟨InfiniteLattice.Link.forwardFrom (p.corner + InfiniteLattice.axisStep _ p.highAxis)
      p.lowAxis, full_forwardFrom_positive _ _⟩,
    ⟨InfiniteLattice.Link.forwardFrom p.corner p.highAxis, full_forwardFrom_positive _ _⟩]
theorem fullFaceCorners_mem (p : FullSpace.Face L k j) (i : Fin 4) :
    (fullFaceCorners p i : FullSpace.Edge L k j) ∈ FullSpace.faceEdges p := by
  fin_cases i <;> simp [fullFaceCorners, FullSpace.faceEdges]
theorem meshAt_pos (hL : Conventions.IsAdmissibleBlockingFactor L) : 0 < meshAt L k j := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.meshAt_pos <;> assumption
theorem full_opposite_positive_iff {a : ℝ} (ha : 0 < a) (b : InfiniteLattice.Link a) :
    b.opposite.IsPositivelyOriented ↔ ¬ b.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.link_opposite_positive_iff <;> assumption
theorem full_complexFaceTerm_eq
    (hrev : ∀ b : FullSpace.Edge L k j, b.IsPositivelyOriented →
      ¬ b.opposite.IsPositivelyOriented)
    (X U : FullSpace.Edge L k j → ComplexMatrix2) (p : FullSpace.Face L k j) :
    FullSpace.complexFaceTerm (FullSpace.expTwist X U) p =
      wilsonTerm (cornerValues fullFaceCorners p (FullSpace.restrictToPositiveEdges U))
        (cornerValues fullFaceCorners p (FullSpace.restrictToPositiveEdges X)) := by
  have e : ∀ b : FullSpace.Edge L k j, b.IsPositivelyOriented →
      FullSpace.expTwist X U b = ComplexMatrix2.matExp (Complex.I • X b) * U b :=
    fun b hb => if_pos hb
  have r : ∀ b : FullSpace.Edge L k j, b.IsPositivelyOriented →
      FullSpace.expTwist X U b.opposite = (ComplexMatrix2.matExp (Complex.I • X b) * U b)⁻¹ :=
    fun b hb => if_neg (hrev b hb)
  simp only [FullSpace.complexFaceTerm, FullSpace.faceVariable, FullSpace.linkHolonomy,
    FullSpace.faceBoundary, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [e _ (full_forwardFrom_positive _ _), e _ (full_forwardFrom_positive _ _),
    r _ (full_forwardFrom_positive _ _), r _ (full_forwardFrom_positive _ _)]
  simp [wilsonTerm, cornerValues, fullFaceCorners, FullSpace.restrictToPositiveEdges, mul_assoc]
def LeftExpMulInGroup (L k j : ℕ) : Prop :=
  ∀ U ∈ FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup,
    ∀ X ∈ FullSpace.complexEdgeForms (meshAt L k j), ∀ b : FullSpace.Edge L k j,
      b.IsPositivelyOriented →
        ComplexMatrix2.matExp (Complex.I • X b) * U b ∈ PeriodicLattice.complexGaugeGroup
theorem full_expTwist_mem (hl : LeftExpMulInGroup L k j)
    (hiff : ∀ b : FullSpace.Edge L k j, b.opposite.IsPositivelyOriented ↔
      ¬ b.IsPositivelyOriented)
    {U X : FullSpace.Edge L k j → ComplexMatrix2}
    (hU : U ∈ FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    (hX : X ∈ FullSpace.complexEdgeForms (meshAt L k j)) :
    FullSpace.expTwist X U ∈ FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup := by
  have hdet : ∀ b : FullSpace.Edge L k j, b.IsPositivelyOriented →
      (ComplexMatrix2.matExp (Complex.I • X b) * U b).det = 1 := fun b hb => hl U hU X hX b hb
  refine ⟨fun b => ?_, fun b => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · have e : FullSpace.expTwist X U b = ComplexMatrix2.matExp (Complex.I • X b) * U b :=
        if_pos hb
      rw [e]
      exact hdet b hb
    · have e : FullSpace.expTwist X U b =
          (ComplexMatrix2.matExp (Complex.I • X b.opposite) * U b.opposite)⁻¹ := if_neg hb
      rw [e]
      change Matrix.det _ = 1
      rw [Matrix.det_nonsing_inv, hdet _ ((hiff b).2 hb)]
      simp
  · by_cases hb : b.IsPositivelyOriented
    · have h' : ¬ b.opposite.IsPositivelyOriented := fun h => (hiff b).1 h hb
      have e : FullSpace.expTwist X U b = ComplexMatrix2.matExp (Complex.I • X b) * U b :=
        if_pos hb
      have e' : FullSpace.expTwist X U b.opposite =
          (ComplexMatrix2.matExp (Complex.I • X b) * U b)⁻¹ := if_neg h'
      rw [e, e']
    · have h' : b.opposite.IsPositivelyOriented := (hiff b).2 hb
      have e : FullSpace.expTwist X U b =
          (ComplexMatrix2.matExp (Complex.I • X b.opposite) * U b.opposite)⁻¹ := if_neg hb
      have e' : FullSpace.expTwist X U b.opposite =
          ComplexMatrix2.matExp (Complex.I • X b.opposite) * U b.opposite := if_pos h'
      rw [e, e', Matrix.nonsing_inv_nonsing_inv]
      simp [hdet _ h']
theorem faceTermSum_eq_faceSum {Ω : Set (FullSpace.Face L k j)} (hΩ : Ω.Finite)
    {U : FullSpace.Edge L k j → ComplexMatrix2}
    (hU : U ∈ FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup) :
    FullSpace.faceTermSum Ω U = faceSum FullSpace.faceEdges hΩ.toFinset U := by
  rw [FullSpace.faceTermSum, finsum_mem_eq_finite_toFinset_sum _ hΩ, faceSum]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [FullSpace.complexFaceTerm, FullSpace.faceVariable_eq_edge_product hU,
    FullSpace.faceEdges, faceTerm]
theorem exists_local_presentation (hN : FaceEdgeFinsets.Unbounded.HoldsOnFullSpace L k j)
    (hW : FaceSum.HoldsOnFullSpace L k j) {S : Set (FullSpace.Edge L k j)}
    (hS : S.Finite) (hpos : ∀ b ∈ S, b.IsPositivelyOriented)
    {U : FullSpace.Edge L k j → ComplexMatrix2}
    (hU : U ∈ FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup) :
    ∃ w : FullSpace.LocalData L k j ℂ,
      FullSpace.IsLocalPresentation PeriodicLattice.complexGaugeGroup
          (FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
          (FullSpace.faceTermSum (facesMeeting S)) U w.support w.region w.fn ∧
        FullSpace.holomorphicPresentations L k j OneLoop.pauliBasis
          (Equiv.funUnique (Fin 1) ℂ).symm w.support w.region w.fn := by
  classical
  have hΩ := (hN.2.1 S hS hpos).1
  obtain ⟨hF, hne, hFpos⟩ := hN.2.2 S hS hpos
  have hFb : FullSpace.IsFinitePositiveEdgeSet hF.toFinset :=
    ⟨by simpa using hne, fun b hb => hFpos b (hF.mem_toFinset.1 hb)⟩
  have hΩF : ∀ p ∈ hΩ.toFinset, ∀ b ∈ FullSpace.faceEdges p, b ∈ hF.toFinset :=
    fun p hp b hb => hF.mem_toFinset.2 (Or.inr ⟨p, hΩ.mem_toFinset.1 hp, hb⟩)
  obtain ⟨hH, -, -, hWr, -⟩ := hW hF.toFinset hFb hΩ.toFinset hΩF
  have hw := hWr U hU
  refine ⟨⟨hF.toFinset, FullSpace.edgeProduct PeriodicLattice.complexGaugeGroup hF.toFinset,
    faceSumOfFamily FullSpace.faceEdges hF.toFinset hΩ.toFinset⟩,
    ⟨hw.1, hw.2.1, hw.2.2.1, fun U' hU' hO => ?_⟩, hH.2.2 OneLoop.pauliBasis⟩
  rw [faceTermSum_eq_faceSum hΩ hU']
  exact hw.2.2.2 U' hU' hO
theorem presentation_eventually_eq {h : (FullSpace.Edge L k j → ComplexMatrix2) → ℂ}
    {U B B' : FullSpace.Edge L k j → ComplexMatrix2} (hl : LeftExpMulInGroup L k j)
    (hiff : ∀ b : FullSpace.Edge L k j, b.opposite.IsPositivelyOriented ↔
      ¬ b.IsPositivelyOriented)
    (hU : U ∈ FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    (hB : B ∈ FullSpace.complexEdgeForms (meshAt L k j))
    (hB' : B' ∈ FullSpace.complexEdgeForms (meshAt L k j))
    (F : Finset (FullSpace.Edge L k j)) (O : Set (F → ComplexMatrix2))
    (f : (F → ComplexMatrix2) → ℂ)
    (hw : FullSpace.IsLocalPresentation PeriodicLattice.complexGaugeGroup
      (FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup) h U F O f) :
    ∀ᶠ q : ℂ × ℂ in 𝓝 ((0 : ℂ), (0 : ℂ)),
      f (fun b => ComplexMatrix2.matExp (Complex.I • (q.1 • B + q.2 • B') b) * U b) =
        h (FullSpace.expTwist (q.1 • B + q.2 • B') U) := by
  obtain ⟨hFb, ⟨O', hO', hdom⟩, h0, hval⟩ := hw
  have hcont : Continuous (fun q : ℂ × ℂ => fun b : F =>
      ComplexMatrix2.matExp (Complex.I • (q.1 • B + q.2 • B') b) * U b) := by
    refine continuous_pi fun b => ?_
    refine Continuous.mul (contDiff_matExp.continuous.comp ?_) continuous_const
    change Continuous fun q : ℂ × ℂ => Complex.I • (q.1 • B b + q.2 • B' b)
    fun_prop
  have h00 : (fun b : F => ComplexMatrix2.matExp (Complex.I •
      (((0 : ℂ), (0 : ℂ)).1 • B + ((0 : ℂ), (0 : ℂ)).2 • B') b) * U b) ∈ O' := by
    have hz : (fun b : F => ComplexMatrix2.matExp (Complex.I •
        (((0 : ℂ), (0 : ℂ)).1 • B + ((0 : ℂ), (0 : ℂ)).2 • B') b) * U b) =
        FullSpace.restrictToEdges F U := by
      funext b
      simp [FullSpace.restrictToEdges, NormedSpace.exp_zero]
    rw [hz]
    rw [hdom] at h0
    exact h0.1
  filter_upwards [hcont.continuousAt.eventually (hO'.mem_nhds h00)] with q hq
  have hX : q.1 • B + q.2 • B' ∈ FullSpace.complexEdgeForms (meshAt L k j) :=
    (FullSpace.complexEdgeForms _).add_mem ((FullSpace.complexEdgeForms _).smul_mem _ hB)
      ((FullSpace.complexEdgeForms _).smul_mem _ hB')
  have hU' := full_expTwist_mem hl hiff hU hX
  have hbv : FullSpace.restrictToEdges F (FullSpace.expTwist (q.1 • B + q.2 • B') U) =
      fun b : F => ComplexMatrix2.matExp (Complex.I • (q.1 • B + q.2 • B') b) * U b :=
    funext fun b => if_pos (hFb.2 b b.2)
  have hd : FullSpace.restrictToEdges F (FullSpace.expTwist (q.1 • B + q.2 • B') U) ∈ O := by
    rw [hdom]
    exact ⟨hbv ▸ hq, fun b => hU'.1 b⟩
  rw [hval _ hU' hd, hbv]
theorem full_complexActionHessian_eq (hN : FaceEdgeFinsets.Unbounded.HoldsOnFullSpace L k j)
    (hW : FaceSum.HoldsOnFullSpace L k j) (hl : LeftExpMulInGroup L k j)
    (hiff : ∀ b : FullSpace.Edge L k j, b.opposite.IsPositivelyOriented ↔
      ¬ b.IsPositivelyOriented)
    {U B B' : FullSpace.Edge L k j → ComplexMatrix2}
    (hU : U ∈ FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    (hB : B ∈ finiteSupportComplexForms L k j) (hB' : B' ∈ finiteSupportComplexForms L k j) :
    FullSpace.complexActionHessian U B B' =
      hessianFinsum fullFaceCorners (FullSpace.restrictToPositiveEdges U)
        (FullSpace.restrictToPositiveEdges B) (FullSpace.restrictToPositiveEdges B') := by
  classical
  have hrev : ∀ b : FullSpace.Edge L k j, b.IsPositivelyOriented →
      ¬ b.opposite.IsPositivelyOriented :=
    fun b hb h => (hiff b).1 h hb
  have hS : (FullSpace.edgeSupport B ∪ FullSpace.edgeSupport B').Finite := hB.2.union hB'.2
  have hpos : ∀ b ∈ FullSpace.edgeSupport B ∪ FullSpace.edgeSupport B',
      b.IsPositivelyOriented := by
    rintro b (h | h)
    · exact h.1
    · exact h.1
  have hΩ := (hN.2.1 _ hS hpos).1
  have hspec := Classical.epsilon_spec (exists_local_presentation hN hW hS hpos hU)
  have hnear := presentation_eventually_eq hl hiff hU hB.1 hB'.1 _ _ _ hspec.1
  have hgerm : ∀ᶠ q : ℂ × ℂ in 𝓝 ((0 : ℂ), (0 : ℂ)),
      FullSpace.valueViaPresentation PeriodicLattice.complexGaugeGroup
          (FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
          (FullSpace.holomorphicPresentations L k j OneLoop.pauliBasis
            (Equiv.funUnique (Fin 1) ℂ).symm)
          (FullSpace.faceTermSum
            (facesMeeting (FullSpace.edgeSupport B ∪ FullSpace.edgeSupport B'))) U
          (q.1 • B + q.2 • B') =
        ∑ p ∈ hΩ.toFinset,
          wilsonTerm (cornerValues fullFaceCorners p (FullSpace.restrictToPositiveEdges U))
            (q.1 • cornerValues fullFaceCorners p (FullSpace.restrictToPositiveEdges B) +
              q.2 • cornerValues fullFaceCorners p (FullSpace.restrictToPositiveEdges B')) := by
    filter_upwards [hnear] with q hq
    refine Eq.trans hq ?_
    rw [FullSpace.faceTermSum, finsum_mem_eq_finite_toFinset_sum _ hΩ]
    exact Finset.sum_congr rfl fun p _ => full_complexFaceTerm_eq hrev _ U p
  have h1 := mixedDeriv_congr_nhds hgerm
  have h2 := mixedDeriv_finset_sum hΩ.toFinset
    (fun p => cornerValues fullFaceCorners p (FullSpace.restrictToPositiveEdges U))
    (fun p => cornerValues fullFaceCorners p (FullSpace.restrictToPositiveEdges B))
    (fun p => cornerValues fullFaceCorners p (FullSpace.restrictToPositiveEdges B'))
  have h3 : hessianFinsum fullFaceCorners (FullSpace.restrictToPositiveEdges U)
      (FullSpace.restrictToPositiveEdges B) (FullSpace.restrictToPositiveEdges B') =
      ∑ p ∈ hΩ.toFinset,
        faceHessianTerm fullFaceCorners (FullSpace.restrictToPositiveEdges U) p
          (FullSpace.restrictToPositiveEdges B) (FullSpace.restrictToPositiveEdges B') := by
    refine hessianFinsum_eq_sum _ fun p hp _ => ?_
    obtain ⟨i, hi⟩ := hp
    exact hΩ.mem_toFinset.2 ⟨_, Or.inl ⟨(fullFaceCorners p i).2, hi⟩, fullFaceCorners_mem p i⟩
  rw [h3]
  exact h1.trans h2
theorem full_extendOddly_pos (f : FullSpace.Edge L k j → ComplexMatrix2)
    (b : FullSpace.Edge L k j) (hb : b.IsPositivelyOriented) :
    FullSpace.extendOddly f b = f b := if_pos hb
theorem full_extendOddly_opposite
    (hiff : ∀ b : FullSpace.Edge L k j, b.opposite.IsPositivelyOriented ↔
      ¬ b.IsPositivelyOriented)
    (f : FullSpace.Edge L k j → ComplexMatrix2) (b : FullSpace.Edge L k j) :
    FullSpace.extendOddly f b.opposite = -FullSpace.extendOddly f b := by
  by_cases hb : b.IsPositivelyOriented
  · have h' : ¬ b.opposite.IsPositivelyOriented := fun h => (hiff b).1 h hb
    have e1 : FullSpace.extendOddly f b.opposite = -f b := if_neg h'
    have e2 : FullSpace.extendOddly f b = f b := if_pos hb
    rw [e1, e2]
  · have h' : b.opposite.IsPositivelyOriented := (hiff b).2 hb
    have e1 : FullSpace.extendOddly f b.opposite = f b.opposite := if_pos h'
    have e2 : FullSpace.extendOddly f b = -f b.opposite := if_neg hb
    rw [e1, e2, neg_neg]
theorem full_restrict_basisForm (a : Fin 3) (b : FullSpace.PositiveEdge (meshAt L k j)) :
    FullSpace.restrictToPositiveEdges (FullSpace.basisForm (L := L) (k := k) (j := j) a b) =
      pauliDelta (a, b) := by
  classical
  funext b'
  have e : FullSpace.restrictToPositiveEdges
      (FullSpace.basisForm (L := L) (k := k) (j := j) a b) b' =
      if b'.1 = b.1 then ComplexMatrix2.pauliFamily a else 0 := if_pos b'.2
  rw [e]
  simp [pauliDelta, Subtype.ext_iff]
theorem full_hasFiniteSupport_restrict {B : FullSpace.Edge L k j → ComplexMatrix2}
    (hB : FullSpace.HasFiniteEdgeSupport B) :
    HasFiniteSupport (FullSpace.restrictToPositiveEdges B) := by
  refine (Set.Finite.preimage Subtype.val_injective.injOn hB).subset fun b hb => ?_
  exact ⟨b.2, hb⟩
theorem full_basisForm_mem
    (hiff : ∀ b : FullSpace.Edge L k j, b.opposite.IsPositivelyOriented ↔
      ¬ b.IsPositivelyOriented)
    (a : Fin 3) (b : FullSpace.PositiveEdge (meshAt L k j)) :
    FullSpace.basisForm (L := L) (k := k) (j := j) a b ∈ finiteSupportComplexForms L k j := by
  classical
  refine ⟨⟨fun b' hb' => ?_, fun b' => full_extendOddly_opposite hiff _ b'⟩, ?_⟩
  · have e : FullSpace.basisForm (L := L) (k := k) (j := j) a b b' =
        if b' = b.1 then ComplexMatrix2.pauliFamily a else 0 := if_pos hb'
    rw [e]
    split_ifs
    · exact pauliFamily_mem_traceless a
    · exact ComplexMatrix2.traceless.zero_mem
  · refine (Set.finite_singleton b.1).subset ?_
    rintro b' ⟨hb', hne⟩
    by_contra h
    have h' : b' ≠ b.1 := h
    have e : FullSpace.basisForm (L := L) (k := k) (j := j) a b b' =
        if b' = b.1 then ComplexMatrix2.pauliFamily a else 0 := if_pos hb'
    rw [e, if_neg h'] at hne
    exact hne rfl
theorem holdsOnFullSpace (hN : FaceEdgeFinsets.Unbounded.HoldsOnFullSpace L k j)
    (hS : FacesContainingEdge.OnFullSpace L k j) (hW : FaceSum.HoldsOnFullSpace L k j)
    (hl : LeftExpMulInGroup L k j) (hL : Conventions.IsAdmissibleBlockingFactor L) :
    HoldsOnFullSpace L k j := by
  intro U hU
  have hiff : ∀ b : FullSpace.Edge L k j, b.opposite.IsPositivelyOriented ↔
      ¬ b.IsPositivelyOriented :=
    full_opposite_positive_iff (meshAt_pos hL)
  have hfin : ∀ F : Set (FullSpace.PositiveEdge (meshAt L k j)), F.Finite →
      (facesMeetingSet fullFaceCorners F).Finite :=
    fun F hF => (hS.2.2 F hF).subset fun p ⟨i, hi⟩ => ⟨_, hi, fullFaceCorners_mem p i⟩
  have hsl : ∀ E ∈ finiteSupportComplexForms L k j, ∀ b,
      FullSpace.restrictToPositiveEdges E b ∈ ComplexMatrix2.traceless :=
    fun E hE b => hE.1.1 b.1 b.2
  have hK : FullSpace.complexHessianKernel U =
      hessianKernelOf fullFaceCorners (FullSpace.restrictToPositiveEdges U) := by
    funext ι' ι
    change FullSpace.complexActionHessian U _ _ = _
    rw [full_complexActionHessian_eq hN hW hl hiff hU (full_basisForm_mem hiff _ _)
      (full_basisForm_mem hiff _ _), full_restrict_basisForm, full_restrict_basisForm]
    rfl
  have hop : ∀ B : FullSpace.Edge L k j → ComplexMatrix2,
      FullSpace.restrictToPositiveEdges (FullSpace.complexHessianOperator U B) =
        ofPauliCoeffs (applyKernel
          (hessianKernelOf fullFaceCorners (FullSpace.restrictToPositiveEdges U))
          (toPauliCoeffs (FullSpace.restrictToPositiveEdges B))) := fun B => by
    funext b
    have e : FullSpace.restrictToPositiveEdges (FullSpace.complexHessianOperator U B) b =
        ofPauliCoeffs (applyKernel (FullSpace.complexHessianKernel U)
          (toPauliCoeffs (FullSpace.restrictToPositiveEdges B))) b := by
      change FullSpace.complexHessianOperator U B b.1 = _
      rw [FullSpace.complexHessianOperator, full_extendOddly_pos _ _ b.2]
      exact dif_pos b.2
    rw [e, hK]
  have hadd : ∀ (z : ℂ), ∀ E₁ ∈ finiteSupportComplexForms L k j,
      ∀ E₂ ∈ finiteSupportComplexForms L k j,
        z • E₁ + E₂ ∈ finiteSupportComplexForms L k j := by
    intro z E₁ h₁ E₂ h₂
    refine ⟨(FullSpace.complexEdgeForms _).add_mem
      ((FullSpace.complexEdgeForms _).smul_mem z h₁.1) h₂.1, ?_⟩
    refine (Set.Finite.union h₁.2 h₂.2).subset ?_
    rintro b ⟨hb, hne⟩
    by_contra h
    simp only [Set.mem_union, not_or] at h
    have h1 : E₁ b = 0 := by
      by_contra h1
      exact h.1 ⟨hb, h1⟩
    have h2 : E₂ b = 0 := by
      by_contra h2
      exact h.2 ⟨hb, h2⟩
    exact hne (by simp [h1, h2])
  refine ⟨isSymmBilinearOn_of_hessianFinsum hfin FullSpace.restrictToPositiveEdges
      (fun _ _ _ => rfl) hadd
      (fun _ hE => full_hasFiniteSupport_restrict hE.2)
      (fun B hB B' hB' => full_complexActionHessian_eq hN hW hl hiff hU hB hB'),
      ?_, ?_, ?_, ?_, ?_⟩
  · intro ι ι' h
    rw [hK]
    refine hessianKernelOf_eq_zero ι ι' ?_
    rintro ⟨p, ⟨i, hi⟩, i', hi'⟩
    exact h ⟨p, hi ▸ fullFaceCorners_mem p i, hi' ▸ fullFaceCorners_mem p i'⟩
  · rw [hK]
    exact hessianKernelOf_row_finite hfin
  · intro B _ ι
    rw [hK]
    exact hessianKernelOf_applySummable hfin _ ι
  · intro B hB B' hB'
    rw [FullSpace.finiteEdgePairing, hop,
      traceFinsumPairing_applyKernel hfin (full_hasFiniteSupport_restrict hB.2) (hsl B hB)
        (full_hasFiniteSupport_restrict hB'.2) (hsl B' hB'),
      full_complexActionHessian_eq hN hW hl hiff hU hB hB']
  · rw [hK]
    exact fun ι ι' => hessianKernelOf_symm ι ι'
end FullSpaceCase
theorem kernelProperties_holds (hN : FaceEdgeFinsets.FacesAndEdgesFinite)
    (hS : FacesContainingEdge.Holds) (hW : FaceSum.holomorphy_statement)
    (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hC : LeftChartFields.Claim) : KernelProperties := by
  intro L hL k j hj
  refine ⟨fun n hn => holdsOnTorus ((hN L hL k j hj).1 n hn) ((hS L hL k j hj).1 n hn) hA hL hn hj,
    holdsOnFullSpace (hN L hL k j hj).2 (hS L hL k j hj).2 (hW L hL k j hj).2 ?_ hL⟩
  intro U hU X hX b hb
  have h := (((hC.2.2 L k j hL hj).2.1).1.2 U hU X hX ⟨b, hb⟩).1 1
  simpa [LeftChartFields.leftExpMul, LeftChartFields.LatticeData.onPositive,
    LeftChartFields.fullData] using h
end YangMills.Construction.Tower.HessianKernel
end
