import YangMills.Construction.Towers.QuadraticFormsAndTransposesOnTheRealSpacesProof
import YangMills.Construction.Towers.SecondDerivativeOfTheActionInGaugeDirections
import YangMills.Construction.Towers.TheActionOnATowerProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open scoped Matrix.Norms.L2Operator Topology ContDiff
noncomputable section
namespace YangMills.Construction
open Matrices Tower
namespace Tower.GaugeHessian
section Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem hasDerivAt_deriv_comp_two_param {f : E → ℝ} (hf : ContDiff ℝ 2 f) {γ : ℝ → ℝ → E}
    {τ : ℝ → E} {v w : E}
    (hτ : ∀ s, HasDerivAt (γ s) (τ s) 0) (hv : HasDerivAt (fun s => γ s 0) v 0)
    (hw : HasDerivAt τ w 0) :
    HasDerivAt (fun s => deriv (fun t => f (γ s t)) 0)
      (fderiv ℝ (fderiv ℝ f) (γ 0 0) v (τ 0) + fderiv ℝ f (γ 0 0) w) 0 := by
  have hf1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hf2 : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have key : (fun s => deriv (fun t => f (γ s t)) 0) = fun s => fderiv ℝ f (γ s 0) (τ s) := by
    funext s
    exact ((hf1 (γ s 0)).hasFDerivAt.comp_hasDerivAt 0 (hτ s)).deriv
  rw [key]
  have hlin : HasDerivAt (fun s => fderiv ℝ f (γ s 0)) (fderiv ℝ (fderiv ℝ f) (γ 0 0) v) 0 :=
    HasFDerivAt.comp_hasDerivAt (f := fun s => γ s 0) (0 : ℝ) (hf2 (γ 0 0)).hasFDerivAt hv
  exact hlin.clm_apply hw
theorem contDiff_mvPolynomial_eval {σ : Type*} (p : MvPolynomial σ ℝ) {g : E → σ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 fun x => g x i) :
    ContDiff ℝ 2 fun x => MvPolynomial.eval (g x) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp => simpa using hp.mul (hg i)
end Calculus
section Exponential
theorem matExp_contDiff : ContDiff ℝ 2 (ComplexMatrix2.matExp) :=
  contDiff_iff_contDiffAt.mpr fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
theorem matExp_differentiable : Differentiable ℝ ComplexMatrix2.matExp :=
  matExp_contDiff.differentiable (by norm_num)
theorem matExp_fderiv_differentiable : Differentiable ℝ (fderiv ℝ ComplexMatrix2.matExp) :=
  (matExp_contDiff.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
theorem matExp_smul_hasDerivAt (A : ComplexMatrix2) (u : ℝ) :
    HasDerivAt (fun u : ℝ => ComplexMatrix2.matExp (u • A)) (ComplexMatrix2.matExp (u • A) * A) u :=
  hasDerivAt_exp_smul_const A u
theorem matExp_fderiv_smul_self (A : ComplexMatrix2) (u : ℝ) :
    fderiv ℝ ComplexMatrix2.matExp (u • A) A = ComplexMatrix2.matExp (u • A) * A := by
  have hline : HasDerivAt (fun u : ℝ => u • A) A u := by
    simpa using (hasDerivAt_id u).smul_const A
  exact ((matExp_differentiable _).hasFDerivAt.comp_hasDerivAt u hline).unique
    (matExp_smul_hasDerivAt A u)
theorem matExp_fderiv_zero (A : ComplexMatrix2) : fderiv ℝ ComplexMatrix2.matExp 0 A = A := by
  simpa using matExp_fderiv_smul_self A 0
theorem matExp_fderiv_ray_hasDerivAt (A B : ComplexMatrix2) :
    HasDerivAt (fun s : ℝ => fderiv ℝ ComplexMatrix2.matExp (s • A) B)
      (fderiv ℝ (fderiv ℝ ComplexMatrix2.matExp) 0 A B) 0 := by
  have hline : HasDerivAt (fun u : ℝ => u • A) A 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const A
  have hD : HasFDerivAt (fderiv ℝ ComplexMatrix2.matExp)
      (fderiv ℝ (fderiv ℝ ComplexMatrix2.matExp) 0) (0 : ComplexMatrix2) :=
    (matExp_fderiv_differentiable 0).hasFDerivAt
  have happ : HasFDerivAt (fun x : ComplexMatrix2 => fderiv ℝ ComplexMatrix2.matExp x B)
      ((ContinuousLinearMap.apply ℝ ComplexMatrix2 B).comp
        (fderiv ℝ (fderiv ℝ ComplexMatrix2.matExp) 0)) (0 : ComplexMatrix2) :=
    (ContinuousLinearMap.apply ℝ ComplexMatrix2 B).hasFDerivAt.comp (0 : ComplexMatrix2) hD
  have happ' : HasFDerivAt (fun x : ComplexMatrix2 => fderiv ℝ ComplexMatrix2.matExp x B)
      ((ContinuousLinearMap.apply ℝ ComplexMatrix2 B).comp
        (fderiv ℝ (fderiv ℝ ComplexMatrix2.matExp) 0))
      ((0 : ℝ) • A) := by
    rw [zero_smul]
    exact happ
  exact happ'.comp_hasDerivAt (0 : ℝ) hline
theorem matExp_secondDeriv_diag (A : ComplexMatrix2) :
    fderiv ℝ (fderiv ℝ ComplexMatrix2.matExp) 0 A A = A * A := by
  have hray := matExp_fderiv_ray_hasDerivAt A A
  have hfun : (fun s : ℝ => fderiv ℝ ComplexMatrix2.matExp (s • A) A) =
      fun s : ℝ => ComplexMatrix2.matExp (s • A) * A :=
    funext fun s => matExp_fderiv_smul_self A s
  rw [hfun] at hray
  have hprod := (matExp_smul_hasDerivAt A 0).mul_const A
  have huniq := hray.unique hprod
  simpa using huniq
theorem matExp_secondDeriv_zero (A B : ComplexMatrix2) :
    fderiv ℝ (fderiv ℝ ComplexMatrix2.matExp) 0 A B = (1 / 2 : ℂ) • (A * B + B * A) := by
  have hsymm : IsSymmSndFDerivAt ℝ ComplexMatrix2.matExp 0 :=
    (matExp_contDiff.contDiffAt).isSymmSndFDerivAt (by simp)
  have hdiag := matExp_secondDeriv_diag (A + B)
  simp only [map_add, add_apply, matExp_secondDeriv_diag, hsymm.eq B A] at hdiag
  have htwo : (2 : ℂ) • fderiv ℝ (fderiv ℝ ComplexMatrix2.matExp) 0 A B = A * B + B * A := by
    have hexpand : (A + B) * (A + B) = A * A + A * B + B * A + B * B := by noncomm_ring
    rw [hexpand] at hdiag
    have hdouble : fderiv ℝ (fderiv ℝ ComplexMatrix2.matExp) 0 A B +
        fderiv ℝ (fderiv ℝ ComplexMatrix2.matExp) 0 A B = A * B + B * A := by
      have h3 : A * A + fderiv ℝ (fderiv ℝ ComplexMatrix2.matExp) 0 A B +
          (fderiv ℝ (fderiv ℝ ComplexMatrix2.matExp) 0 A B + B * B) =
          A * A + A * B + B * A + B * B := hdiag
      have h4 : A * A + (fderiv ℝ (fderiv ℝ ComplexMatrix2.matExp) 0 A B +
          fderiv ℝ (fderiv ℝ ComplexMatrix2.matExp) 0 A B) + B * B =
          A * A + (A * B + B * A) + B * B := by
        rw [← add_assoc (A * A), ← add_assoc (A * A)]
        rw [← h3.trans (by abel : _ = A * A + A * B + B * A + B * B)]
        abel
      exact add_left_cancel (add_right_cancel h4)
    rw [two_smul, hdouble]
  rw [← htwo, smul_smul]
  norm_num
end Exponential
section Families
variable (P Q R S W M : ComplexMatrix2)
theorem linkTwist_hasDerivAt_inner (s : ℝ) :
    HasDerivAt (fun t : ℝ => ComplexMatrix2.matExp (s • P + t • Q) * W)
      (fderiv ℝ ComplexMatrix2.matExp (s • P) Q * W) 0 := by
  have hline : HasDerivAt (fun t : ℝ => s • P + t • Q) Q 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const Q).const_add (s • P)
  have hexp : HasFDerivAt ComplexMatrix2.matExp (fderiv ℝ ComplexMatrix2.matExp (s • P))
      (s • P + (0 : ℝ) • Q) := by
    rw [zero_smul, add_zero]
    exact (matExp_differentiable _).hasFDerivAt
  exact (hexp.comp_hasDerivAt (0 : ℝ) hline).mul_const W
theorem linkTwist_hasDerivAt_outer :
    HasDerivAt (fun s : ℝ => ComplexMatrix2.matExp (s • P + (0 : ℝ) • Q) * W) (P * W) 0 := by
  simpa using (matExp_smul_hasDerivAt P 0).mul_const W
theorem linkTwist_hasDerivAt_mixed :
    HasDerivAt (fun s : ℝ => fderiv ℝ ComplexMatrix2.matExp (s • P) Q * W)
      (((1 / 2 : ℂ) • (P * Q + Q * P)) * W) 0 := by
  have hray := (matExp_fderiv_ray_hasDerivAt P Q).mul_const W
  rwa [matExp_secondDeriv_zero] at hray
theorem gaugeTwist_hasDerivAt_inner :
    HasDerivAt (fun t : ℝ => ComplexMatrix2.matExp (t • R) * M * ComplexMatrix2.matExp (t • S))
      (R * M + M * S) 0 := by
  have hprod := ((matExp_smul_hasDerivAt R 0).mul_const M).fun_mul (matExp_smul_hasDerivAt S 0)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one] at hprod
  exact hprod
theorem gaugeTwist_hasDerivAt_outer :
    HasDerivAt (fun s : ℝ => ComplexMatrix2.matExp ((0 : ℝ) • R) *
      (ComplexMatrix2.matExp (s • P) * W) * ComplexMatrix2.matExp ((0 : ℝ) • S)) (P * W) 0 := by
  simpa using (matExp_smul_hasDerivAt P 0).mul_const W
theorem gaugeTwist_hasDerivAt_mixed :
    HasDerivAt (fun s : ℝ => R * (ComplexMatrix2.matExp (s • P) * W) +
      (ComplexMatrix2.matExp (s • P) * W) * S)
      (R * (P * W) + (P * W) * S) 0 := by
  have hcurve : HasDerivAt (fun s : ℝ => ComplexMatrix2.matExp (s • P) * W) (P * W) 0 := by
    simpa using (matExp_smul_hasDerivAt P 0).mul_const W
  exact (hcurve.const_mul R).add (hcurve.mul_const S)
theorem mixed_terms_add (X Y Z Z' : ComplexMatrix2) (hWZ : W * Z = Z' * W) :
    ((1 / 2 : ℂ) • ((Complex.I • X) * (Complex.I • (Z' - Y)) +
        (Complex.I • (Z' - Y)) * (Complex.I • X))) * W +
      ((Complex.I • Y) * ((Complex.I • X) * W) + ((Complex.I • X) * W) * (-(Complex.I • Z))) =
    (Complex.I • ((Complex.I / 2) • ⁅Y + Z', X⁆)) * W := by
  have hlast : ((Complex.I • X) * W) * (-(Complex.I • Z)) = X * Z' * W := by
    have hmove : X * W * Z = X * Z' * W := by rw [mul_assoc, hWZ, mul_assoc]
    simp only [smul_mul_assoc, mul_smul_comm, mul_neg, smul_smul, Complex.I_mul_I, hmove,
      neg_smul, one_smul, neg_neg]
  rw [hlast, Ring.lie_def]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, Complex.I_mul_I, add_mul, mul_add, sub_mul,
    mul_sub]
  have hI : Complex.I * (Complex.I / 2) = -(1 / 2) := by
    rw [mul_div_assoc', Complex.I_mul_I]
    ring
  simp only [hI, mul_assoc]
  match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring
end Families
section Group
theorem compact_inv_mul {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    g⁻¹ * g = 1 := by apply _root_.YangMills.SharedProofs.p14555 <;> assumption
theorem compact_inv_inv {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    g⁻¹⁻¹ = g := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_inv_of_mem_compactGaugeGroup <;> assumption
theorem compact_inv_mem {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    g⁻¹ ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
theorem conjugateBy_mem {g x : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup)
    (hx : x ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.conjugateBy g x ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.SharedProofs.p2904 <;> assumption
theorem halfI_lie_mem {Y X : ComplexMatrix2} (hY : Y ∈ ComplexMatrix2.hermitianTraceless)
    (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    (Complex.I / 2) • ⁅Y, X⁆ ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.Construction.Tower.RealQuadraticTransposes.halfI_smul_bracket_mem <;> assumption
end Group
section Representation
theorem pauliFamily_mem (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.SharedProofs.p1437 <;> assumption
theorem halfTrace_pauli_sum_mul (x y : Fin 3 → ℝ) :
    ComplexMatrix2.halfTrace ((∑ a, x a • ComplexMatrix2.pauliFamily a) *
      ∑ a, y a • ComplexMatrix2.pauliFamily a) = ((∑ a, x a * y a : ℝ) : ℂ) := by
  obtain ⟨h0, h1, h2⟩ := ComplexMatrix2.pauliFamily_apply
  simp only [Fin.sum_univ_three, h0, h1, h2, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace,
    Matrix.trace_fin_two]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring_nf
  simp only [Complex.I_sq]
  ring
theorem exists_pauli_expansion {Z : ComplexMatrix2} (hZ : Z ∈ ComplexMatrix2.hermitianTraceless) :
    ∃ y : Fin 3 → ℝ, Z = ∑ a, y a • ComplexMatrix2.pauliFamily a := by
  obtain ⟨h0, h1, h2⟩ := ComplexMatrix2.pauliFamily_apply
  have hherm : ∀ i j, Z i j = star (Z j i) := fun i j => congrFun (congrFun hZ.1 i) j
  have htr : Z 0 0 + Z 1 1 = 0 := by
    have htr0 := hZ.2
    simpa [ComplexMatrix2.fullTrace, Matrix.trace_fin_two] using htr0
  have him : (Z 0 0).im = 0 := by
    have him0 := congrArg Complex.im (hherm 0 0)
    simp at him0
    linarith
  have hdiag : Z 1 1 = -Z 0 0 := by
    linear_combination htr
  have hoff : Z 1 0 = star (Z 0 1) := hherm 1 0
  refine ⟨![(Z 0 1).re, -(Z 0 1).im, (Z 0 0).re], ?_⟩
  simp only [Fin.sum_univ_three, h0, h1, h2]
  ext i j
  fin_cases i <;> fin_cases j
  · apply Complex.ext <;> simp [him]
  · apply Complex.ext <;> simp
  · apply Complex.ext <;> simp [hoff]
  · apply Complex.ext <;> simp [hdiag, him]
theorem exists_traceFinsumPairing_repr {ι : Type} [Fintype ι] {f : (ι → ComplexMatrix2) → ℝ}
    (hf : IsLinearMap ℝ f) :
    ∃ X : ι → ComplexMatrix2, (∀ i, X i ∈ ComplexMatrix2.hermitianTraceless) ∧
      ∀ c : ι → ComplexMatrix2, (∀ i, c i ∈ ComplexMatrix2.hermitianTraceless) →
        traceFinsumPairing X c = ((f c : ℝ) : ℂ) := by
  classical
  let g := hf.mk' f
  let x : ι → Fin 3 → ℝ := fun i a => g (Pi.single i (ComplexMatrix2.pauliFamily a))
  refine ⟨fun i => ∑ a, x i a • ComplexMatrix2.pauliFamily a, fun i => ?_, fun c hc => ?_⟩
  · exact Submodule.sum_mem _ fun a _ =>
      ComplexMatrix2.hermitianTraceless.smul_mem _ (pauliFamily_mem a)
  · choose y hy using fun i => exists_pauli_expansion (hc i)
    have hsum : c = ∑ i, ∑ a, y i a •
        (Pi.single i (ComplexMatrix2.pauliFamily a) : ι → ComplexMatrix2) := by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply]
      rw [Finset.sum_eq_single j]
      · simpa using hy j
      · intro i _ hij
        simp [Pi.single_eq_of_ne hij.symm]
      · simp
    have hfc : f c = ∑ i, ∑ a, x i a * y i a := by
      have hgc : f c = g c := rfl
      rw [hgc]
      conv_lhs => rw [hsum]
      simp only [map_sum, map_smul, smul_eq_mul, x]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => mul_comm _ _
    rw [traceFinsumPairing, finsum_eq_sum_of_fintype, hfc, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hy i]
    exact halfTrace_pauli_sum_mul _ _
end Representation
section Lattice
variable {L n k : ℕ}
abbrev UniqueOrientation (L n k : ℕ) : Prop :=
  ∀ e : Edge L n k 0, Xor e.IsPositivelyOriented e.opposite.IsPositivelyOriented
theorem uniqueOrientation_of_admissible (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) : UniqueOrientation L n k := fun e =>
  PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite (by have := hL.2; omega)
    (by show -(n : ℤ) < (k : ℤ) - ((0 : ℕ) : ℤ); omega) e
theorem extendOddly_of_pos (f : Edge L n k 0 → ComplexMatrix2) {e : Edge L n k 0}
    (he : e.IsPositivelyOriented) : extendOddly f e = f e := if_pos he
theorem extendOddly_of_not_pos (f : Edge L n k 0 → ComplexMatrix2) {e : Edge L n k 0}
    (he : ¬e.IsPositivelyOriented) : extendOddly f e = -f e.opposite := if_neg he
theorem extendOddly_mem (ho : UniqueOrientation L n k) {f : Edge L n k 0 → ComplexMatrix2}
    (hf : ∀ e : Edge L n k 0, e.IsPositivelyOriented → f e ∈ ComplexMatrix2.hermitianTraceless) :
    extendOddly f ∈ edgeFormSpace L n k 0 := by
  refine ⟨fun e he => ?_, fun e => ?_⟩
  · rw [extendOddly_of_pos f he]
    exact hf e he
  · rcases ho e with ⟨he, hr⟩ | ⟨hr, he⟩
    · rw [extendOddly_of_not_pos f hr, extendOddly_of_pos f he]
      rfl
    · rw [extendOddly_of_pos f hr, extendOddly_of_not_pos f he, neg_neg]
theorem expTwist_of_pos (A U : Edge L n k 0 → ComplexMatrix2) {e : Edge L n k 0}
    (he : e.IsPositivelyOriented) :
    PeriodicLattice.expTwist A U e = ComplexMatrix2.matExp (Complex.I • A e) * U e := if_pos he
theorem expTwist_of_not_pos (A U : Edge L n k 0 → ComplexMatrix2) {e : Edge L n k 0}
    (he : ¬e.IsPositivelyOriented) :
    PeriodicLattice.expTwist A U e =
      (ComplexMatrix2.matExp (Complex.I • A e.opposite) * U e.opposite)⁻¹ := if_neg he
theorem expTwist_mem (ho : UniqueOrientation L n k)
    (hexp : ∀ X ∈ ComplexMatrix2.hermitianTraceless,
      ComplexMatrix2.matExp (Complex.I • X) ∈ PeriodicLattice.compactGaugeGroup)
    {B U : Edge L n k 0 → ComplexMatrix2} (hB : B ∈ edgeFormSpace L n k 0)
    (hU : U ∈ fieldSpace L n k 0) :
    PeriodicLattice.expTwist B U ∈ fieldSpace L n k 0 := by
  have hpos : ∀ e : Edge L n k 0, e.IsPositivelyOriented →
      ComplexMatrix2.matExp (Complex.I • B e) * U e ∈ PeriodicLattice.compactGaugeGroup :=
    fun e he => (ComplexMatrix2.specialUnitary).mul_mem (hexp _ (hB.1 e he)) (hU.1 e (mem_univ e))
  refine ⟨fun e _ => ?_, fun e _ => ?_⟩
  · rcases ho e with ⟨he, -⟩ | ⟨hr, he⟩
    · rw [expTwist_of_pos _ _ he]
      exact hpos e he
    · rw [expTwist_of_not_pos _ _ he]
      exact compact_inv_mem (hpos _ hr)
  · rcases ho e with ⟨he, hr⟩ | ⟨hr, he⟩
    · rw [expTwist_of_not_pos _ _ hr, expTwist_of_pos _ _ he]
      rfl
    · rw [expTwist_of_pos _ _ hr, expTwist_of_not_pos _ _ he, compact_inv_inv (hpos _ hr)]
theorem gaugeTransform_mem {u : Vertex L n k 0 → ComplexMatrix2}
    {V : Edge L n k 0 → ComplexMatrix2}
    (hu : ∀ x, u x ∈ PeriodicLattice.compactGaugeGroup) (hV : V ∈ fieldSpace L n k 0) :
    PeriodicLattice.gaugeTransform u V ∈ fieldSpace L n k 0 := by
  refine ⟨fun e _ => ?_, fun e _ => ?_⟩
  · exact (ComplexMatrix2.specialUnitary).mul_mem
      ((ComplexMatrix2.specialUnitary).mul_mem (hu _) (hV.1 e (mem_univ e)))
      (compact_inv_mem (hu _))
  · have hr : V e.opposite = (V e)⁻¹ := hV.2 e (mem_univ e)
    show u e.opposite.source * V e.opposite * (u e.opposite.target)⁻¹ =
      (u e.source * V e * (u e.target)⁻¹)⁻¹
    rw [hr, Matrix.mul_inv_rev, Matrix.mul_inv_rev, compact_inv_inv (hu _), mul_assoc]
    rfl
theorem covDiff_mem (ho : UniqueOrientation L n k) {U : Edge L n k 0 → ComplexMatrix2}
    (hU : U ∈ fieldSpace L n k 0) {l : Vertex L n k 0 → ComplexMatrix2}
    (hl : l ∈ vertexFunctionSpace L n k 0) :
    covDiff U l ∈ edgeFormSpace L n k 0 :=
  extendOddly_mem ho fun e _ =>
    ComplexMatrix2.hermitianTraceless.sub_mem
      (conjugateBy_mem (hU.1 e (mem_univ e)) (hl _ (mem_univ _))) (hl _ (mem_univ _))
theorem bracketTerm_mem (ho : UniqueOrientation L n k) {U : Edge L n k 0 → ComplexMatrix2}
    (hU : U ∈ fieldSpace L n k 0) {l : Vertex L n k 0 → ComplexMatrix2}
    (hl : l ∈ vertexFunctionSpace L n k 0)
    {B : Edge L n k 0 → ComplexMatrix2} (hB : B ∈ edgeFormSpace L n k 0) :
    bracketTerm U l B ∈ edgeFormSpace L n k 0 :=
  extendOddly_mem ho fun e he => halfI_lie_mem
    (ComplexMatrix2.hermitianTraceless.add_mem (hl _ (mem_univ _))
      (conjugateBy_mem (hU.1 e (mem_univ e)) (hl _ (mem_univ _))))
    (hB.1 e he)
theorem edgeFormSpace_ofReal_smul {B : Edge L n k 0 → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L n k 0) (t : ℝ) :
    (t : ℂ) • B ∈ edgeFormSpace L n k 0 := by apply _root_.YangMills.Construction.Tower.ActionFacts.ofReal_smul_mem_edgeFormSpace <;> assumption
def entryCoordinates (Y : PositiveEdge L n k 0 → ComplexMatrix2) :
    PositiveEdge L n k 0 × Fin 2 × Fin 2 × Bool → ℝ
  | (e, r, c, false) => (Y e r c).re
  | (e, r, c, true) => (Y e r c).im
theorem edgeEntryCoordinates_eq (U : Edge L n k 0 → ComplexMatrix2) :
    ActionFacts.edgeEntryCoordinates U = entryCoordinates (restrictToPositiveEdges U) := by
  funext ⟨e, r, c, f⟩
  cases f <;> rfl
variable [Fintype (PositiveEdge L n k 0)]
theorem entryCoordinates_contDiff (p : PositiveEdge L n k 0 × Fin 2 × Fin 2 × Bool) :
    ContDiff ℝ 2 fun Y : PositiveEdge L n k 0 → ComplexMatrix2 => entryCoordinates Y p := by
  obtain ⟨e, r, c, f⟩ := p
  cases f
  · let T : (PositiveEdge L n k 0 → ComplexMatrix2) →ₗ[ℝ] ℝ :=
      { toFun := fun Y => (Y e r c).re
        map_add' := fun Y Y' => by simp
        map_smul' := fun a Y => by simp }
    exact T.toContinuousLinearMap.contDiff
  · let T : (PositiveEdge L n k 0 → ComplexMatrix2) →ₗ[ℝ] ℝ :=
      { toFun := fun Y => (Y e r c).im
        map_add' := fun Y Y' => by simp
        map_smul' := fun a Y => by simp }
    exact T.toContinuousLinearMap.contDiff
theorem real_smul_I_smul (t : ℝ) (A : ComplexMatrix2) :
    t • (Complex.I • A) = Complex.I • ((t : ℂ) • A) := by
  ext i j
  simp
  ring
variable {F : (PositiveEdge L n k 0 → ComplexMatrix2) → ℝ}
theorem plaquetteAction_twist_hasDerivAt (hF : ContDiff ℝ 2 F)
    (hFA : ∀ V ∈ fieldSpace L n k 0, plaquetteAction L n k V = F (restrictToPositiveEdges V))
    (ho : UniqueOrientation L n k)
    (hexp : ∀ X ∈ ComplexMatrix2.hermitianTraceless,
      ComplexMatrix2.matExp (Complex.I • X) ∈ PeriodicLattice.compactGaugeGroup)
    {U C : Edge L n k 0 → ComplexMatrix2} (hU : U ∈ fieldSpace L n k 0)
    (hC : C ∈ edgeFormSpace L n k 0) :
    HasDerivAt (fun t : ℝ => plaquetteAction L n k (PeriodicLattice.expTwist ((t : ℂ) • C) U))
      (fderiv ℝ F (restrictToPositiveEdges U) fun e => (Complex.I • C e) * U e) 0 := by
  have hfun : (fun t : ℝ => plaquetteAction L n k (PeriodicLattice.expTwist ((t : ℂ) • C) U)) =
      fun t : ℝ => F fun e => ComplexMatrix2.matExp (t • (Complex.I • C e)) * U e := by
    funext t
    rw [hFA _ (expTwist_mem ho hexp (edgeFormSpace_ofReal_smul hC t) hU)]
    congr 1
    funext e
    show PeriodicLattice.expTwist ((t : ℂ) • C) U e = _
    rw [expTwist_of_pos _ _ e.2, real_smul_I_smul]
    rfl
  rw [hfun]
  have hcurve : HasDerivAt (fun (t : ℝ) (e : PositiveEdge L n k 0) =>
      ComplexMatrix2.matExp (t • (Complex.I • C e)) * U e) (fun e => (Complex.I • C e) * U e) 0 :=
    hasDerivAt_pi.2 fun e => by
      simpa using (matExp_smul_hasDerivAt (Complex.I • C e) 0).mul_const (U e)
  have hstart : (fun e : PositiveEdge L n k 0 =>
      ComplexMatrix2.matExp ((0 : ℝ) • (Complex.I • C e)) * U e) = restrictToPositiveEdges U := by
    funext e
    simp [restrictToPositiveEdges]
  have hFd : HasFDerivAt F (fderiv ℝ F (restrictToPositiveEdges U))
      (fun e : PositiveEdge L n k 0 =>
        ComplexMatrix2.matExp ((0 : ℝ) • (Complex.I • C e)) * U e) := by
    rw [hstart]
    exact (hF.differentiable (by norm_num) _).hasFDerivAt
  exact hFd.comp_hasDerivAt (0 : ℝ) hcurve
theorem edgeFormPairing_leftGradient (hF : ContDiff ℝ 2 F)
    (hFA : ∀ V ∈ fieldSpace L n k 0, plaquetteAction L n k V = F (restrictToPositiveEdges V))
    (ho : UniqueOrientation L n k)
    (hexp : ∀ X ∈ ComplexMatrix2.hermitianTraceless,
      ComplexMatrix2.matExp (Complex.I • X) ∈ PeriodicLattice.compactGaugeGroup)
    {U C : Edge L n k 0 → ComplexMatrix2} (hU : U ∈ fieldSpace L n k 0)
    (hC : C ∈ edgeFormSpace L n k 0) :
    edgeFormPairing (leftGradient (fieldSpace L n k 0)
      (fun V => (plaquetteAction L n k V : ℂ)) U) C =
      ((fderiv ℝ F (restrictToPositiveEdges U) fun e => (Complex.I • C e) * U e : ℝ) : ℂ) := by
  classical
  have hlin : IsLinearMap ℝ fun Y : PositiveEdge L n k 0 → ComplexMatrix2 =>
      fderiv ℝ F (restrictToPositiveEdges U) fun e => (Complex.I • Y e) * U e := by
    refine ⟨fun Y Y' => ?_, fun c Y => ?_⟩
    · rw [← map_add]
      congr 1
      funext e
      simp [smul_add, add_mul]
    · rw [← map_smul]
      congr 1
      funext e
      simp [smul_comm c]
  obtain ⟨X₀, hX₀, hpair⟩ := exists_traceFinsumPairing_repr hlin
  let X : Edge L n k 0 → ComplexMatrix2 :=
    extendOddly fun e => if h : e.IsPositivelyOriented then X₀ ⟨e, h⟩ else 0
  have hX : X ∈ edgeFormSpace L n k 0 := extendOddly_mem ho fun e he => by
    simpa [he] using hX₀ ⟨e, he⟩
  have hval : restrictToPositiveEdges X = X₀ := by
    funext e
    have hr : restrictToPositiveEdges X e = X e.1 := rfl
    rw [hr]
    simp only [X]
    rw [extendOddly_of_pos _ e.2, dif_pos e.2]
  have hderiv : ∀ B ∈ edgeFormSpace L n k 0,
      leftDeriv (fun V => (plaquetteAction L n k V : ℂ)) U B =
        ((fderiv ℝ F (restrictToPositiveEdges U) fun e => (Complex.I • B e) * U e : ℝ) : ℂ) := by
    intro B hB
    exact (plaquetteAction_twist_hasDerivAt hF hFA ho hexp hU hB).ofReal_comp.deriv
  have hgrad : IsLeftGradient (fieldSpace L n k 0) (fun V => (plaquetteAction L n k V : ℂ)) U X := by
    refine ⟨⟨fun e he => (hX.1 e he).2, hX.2⟩, fun _ => hX, fun B hB _ => ?_⟩
    rw [hderiv B hB]
    show traceFinsumPairing (restrictToPositiveEdges X) (restrictToPositiveEdges B) = _
    rw [hval]
    exact hpair _ fun e => hB.1 e.1 e.2
  have hspec : IsLeftGradient (fieldSpace L n k 0) (fun V => (plaquetteAction L n k V : ℂ)) U
      (leftGradient (fieldSpace L n k 0) (fun V => (plaquetteAction L n k V : ℂ)) U) :=
    Classical.epsilon_spec ⟨X, hgrad⟩
  rw [hspec.2.2 C hC (Set.toFinite _), hderiv C hC]
theorem leftSecondDeriv_covDiff (hF : ContDiff ℝ 2 F)
    (hFA : ∀ V ∈ fieldSpace L n k 0, plaquetteAction L n k V = F (restrictToPositiveEdges V))
    (ho : UniqueOrientation L n k)
    (hexp : ∀ X ∈ ComplexMatrix2.hermitianTraceless,
      ComplexMatrix2.matExp (Complex.I • X) ∈ PeriodicLattice.compactGaugeGroup)
    (hinv : ∀ Z : ComplexMatrix2, (ComplexMatrix2.matExp Z)⁻¹ = ComplexMatrix2.matExp (-Z))
    (hg : ∀ V ∈ fieldSpace L n k 0, ∀ u ∈ gaugeGroupAt L n k 0,
      plaquetteAction L n k (PeriodicLattice.gaugeTransform u V) = plaquetteAction L n k V)
    {U B : Edge L n k 0 → ComplexMatrix2} (hU : U ∈ fieldSpace L n k 0)
    (hB : B ∈ edgeFormSpace L n k 0)
    {l : Vertex L n k 0 → ComplexMatrix2} (hl : l ∈ vertexFunctionSpace L n k 0) :
    leftSecondDeriv (plaquetteAction L n k) U B (covDiff U l) =
      fderiv ℝ F (restrictToPositiveEdges U) fun e =>
        (Complex.I • bracketTerm U l B e) * U e := by
  have hD := covDiff_mem ho hU hl
  let P : PositiveEdge L n k 0 → ComplexMatrix2 := fun e => Complex.I • B e
  let Q : PositiveEdge L n k 0 → ComplexMatrix2 := fun e => Complex.I • covDiff U l e
  let R : PositiveEdge L n k 0 → ComplexMatrix2 := fun e => Complex.I • l e.1.source
  let S : PositiveEdge L n k 0 → ComplexMatrix2 := fun e => -(Complex.I • l e.1.target)
  let W : PositiveEdge L n k 0 → ComplexMatrix2 := restrictToPositiveEdges U
  let γ₁ : ℝ → ℝ → PositiveEdge L n k 0 → ComplexMatrix2 :=
    fun s t e => ComplexMatrix2.matExp (s • P e + t • Q e) * W e
  let τ₁ : ℝ → PositiveEdge L n k 0 → ComplexMatrix2 :=
    fun s e => fderiv ℝ ComplexMatrix2.matExp (s • P e) (Q e) * W e
  let γ₂ : ℝ → ℝ → PositiveEdge L n k 0 → ComplexMatrix2 :=
    fun s t e => ComplexMatrix2.matExp (t • R e) * (ComplexMatrix2.matExp (s • P e) * W e) *
      ComplexMatrix2.matExp (t • S e)
  let τ₂ : ℝ → PositiveEdge L n k 0 → ComplexMatrix2 :=
    fun s e => R e * (ComplexMatrix2.matExp (s • P e) * W e) +
      (ComplexMatrix2.matExp (s • P e) * W e) * S e
  let v : PositiveEdge L n k 0 → ComplexMatrix2 := fun e => P e * W e
  let w₁ : PositiveEdge L n k 0 → ComplexMatrix2 :=
    fun e => ((1 / 2 : ℂ) • (P e * Q e + Q e * P e)) * W e
  let w₂ : PositiveEdge L n k 0 → ComplexMatrix2 := fun e => R e * (P e * W e) + (P e * W e) * S e
  have hγ₁ : γ₁ 0 0 = W := by
    funext e
    simp [γ₁]
  have hγ₂ : γ₂ 0 0 = W := by
    funext e
    simp [γ₂]
  have hm₁ := hasDerivAt_deriv_comp_two_param hF (γ := γ₁) (τ := τ₁) (v := v) (w := w₁)
    (fun s => hasDerivAt_pi.2 fun e => linkTwist_hasDerivAt_inner (P e) (Q e) (W e) s)
    (hasDerivAt_pi.2 fun e => linkTwist_hasDerivAt_outer (P e) (Q e) (W e))
    (hasDerivAt_pi.2 fun e => linkTwist_hasDerivAt_mixed (P e) (Q e) (W e))
  have hm₂ := hasDerivAt_deriv_comp_two_param hF (γ := γ₂) (τ := τ₂) (v := v) (w := w₂)
    (fun s => hasDerivAt_pi.2 fun e =>
      gaugeTwist_hasDerivAt_inner (R e) (S e) (ComplexMatrix2.matExp (s • P e) * W e))
    (hasDerivAt_pi.2 fun e => gaugeTwist_hasDerivAt_outer (P e) (R e) (S e) (W e))
    (hasDerivAt_pi.2 fun e => gaugeTwist_hasDerivAt_mixed (P e) (R e) (S e) (W e))
  rw [hγ₁] at hm₁
  rw [hγ₂] at hm₂
  have hread₁ : ∀ s t : ℝ, plaquetteAction L n k (PeriodicLattice.expTwist
      (algebraMap ℝ ℂ s • B + algebraMap ℝ ℂ t • covDiff U l) U) = F (γ₁ s t) := by
    intro s t
    have hmem : algebraMap ℝ ℂ s • B + algebraMap ℝ ℂ t • covDiff U l ∈
        edgeFormSpace L n k 0 :=
      (edgeFormSpace L n k 0).add_mem (edgeFormSpace_ofReal_smul hB s)
        (edgeFormSpace_ofReal_smul hD t)
    rw [hFA _ (expTwist_mem ho hexp hmem hU)]
    congr 1
    funext e
    show PeriodicLattice.expTwist _ U e = _
    rw [expTwist_of_pos _ _ e.2]
    simp only [γ₁, P, Q, W, real_smul_I_smul, ← smul_add]
    rfl
  have hread₂ : ∀ s t : ℝ, F (γ₂ s t) =
      plaquetteAction L n k (PeriodicLattice.expTwist ((s : ℂ) • B) U) := by
    intro s t
    have hV := expTwist_mem ho hexp (edgeFormSpace_ofReal_smul hB s) hU
    let u : Vertex L n k 0 → ComplexMatrix2 :=
      fun x => ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • l x))
    have hu : ∀ x, u x ∈ PeriodicLattice.compactGaugeGroup := fun x => by
      refine hexp _ ?_
      have hsm := ComplexMatrix2.hermitianTraceless.smul_mem t (hl x (mem_univ x))
      have hcast : (t : ℂ) • l x = t • l x := by
        ext i j
        simp
      rw [hcast]
      exact hsm
    have hγ : γ₂ s t = restrictToPositiveEdges (PeriodicLattice.gaugeTransform u
        (PeriodicLattice.expTwist ((s : ℂ) • B) U)) := by
      funext e
      show _ = u e.1.source * PeriodicLattice.expTwist ((s : ℂ) • B) U e.1 * (u e.1.target)⁻¹
      rw [expTwist_of_pos _ _ e.2, hinv]
      simp only [γ₂, P, R, S, W, u, real_smul_I_smul, smul_neg]
      rfl
    rw [hγ, ← hFA _ (gaugeTransform_mem hu hV), hg _ hV u hu]
  have hzero : HasDerivAt (fun s => deriv (fun t => F (γ₂ s t)) 0) 0 0 := by
    have hconst : (fun s => deriv (fun t => F (γ₂ s t)) 0) = fun _ => (0 : ℝ) := by
      funext s
      simp only [hread₂, deriv_const]
    rw [hconst]
    exact hasDerivAt_const _ _
  have h₂ := hm₂.unique hzero
  have h₁ : leftSecondDeriv (plaquetteAction L n k) U B (covDiff U l) =
      fderiv ℝ (fderiv ℝ F) W v (τ₁ 0) + fderiv ℝ F W w₁ := by
    have hcong : (fun s : ℝ => deriv (fun t : ℝ => plaquetteAction L n k
        (PeriodicLattice.expTwist
          (algebraMap ℝ ℂ s • B + algebraMap ℝ ℂ t • covDiff U l) U)) 0) =
        fun s => deriv (fun t => F (γ₁ s t)) 0 := by
      funext s
      simp only [hread₁]
    have hd := hm₁.deriv
    rw [← hcong] at hd
    exact hd
  have hτ : τ₂ 0 = -τ₁ 0 := by
    funext e
    have hWi : (W e)⁻¹ * W e = 1 := compact_inv_mul (hU.1 e.1 (mem_univ _))
    have hDe : covDiff U l e.1 = ComplexMatrix2.conjugateBy (W e) (l e.1.target) - l e.1.source :=
      extendOddly_of_pos _ e.2
    simp only [τ₁, τ₂, zero_smul, NormedSpace.exp_zero, one_mul, Pi.neg_apply, matExp_fderiv_zero,
      Q, R, S, hDe, ComplexMatrix2.conjugateBy]
    simp only [smul_mul_assoc, mul_smul_comm, sub_mul, mul_neg, mul_assoc, hWi, mul_one,
      smul_sub, neg_sub]
    abel
  have hw : w₁ + w₂ = fun e : PositiveEdge L n k 0 =>
      (Complex.I • bracketTerm U l B e) * U e := by
    funext e
    have hWi : (W e)⁻¹ * W e = 1 := compact_inv_mul (hU.1 e.1 (mem_univ _))
    have hDe : covDiff U l e.1 = ComplexMatrix2.conjugateBy (W e) (l e.1.target) - l e.1.source :=
      extendOddly_of_pos _ e.2
    have hBe : bracketTerm U l B e.1 = (Complex.I / 2) •
        ⁅l e.1.source + ComplexMatrix2.conjugateBy (W e) (l e.1.target), B e.1⁆ :=
      extendOddly_of_pos _ e.2
    have hcomm : W e * l e.1.target = ComplexMatrix2.conjugateBy (W e) (l e.1.target) * W e := by
      simp only [ComplexMatrix2.conjugateBy, mul_assoc, hWi, mul_one]
    show (w₁ + w₂) e = (Complex.I • bracketTerm U l B e.1) * W e
    simpa only [w₁, w₂, P, Q, R, S, hDe, hBe, Pi.add_apply] using
      mixed_terms_add (W e) (B e.1) (l e.1.source) (l e.1.target)
        (ComplexMatrix2.conjugateBy (W e) (l e.1.target)) hcomm
  rw [hτ, map_neg] at h₂
  rw [h₁, ← hw, map_add]
  show fderiv ℝ (fderiv ℝ F) W v (τ₁ 0) + fderiv ℝ F W w₁ = fderiv ℝ F W w₁ + fderiv ℝ F W w₂
  linear_combination -h₂
end Lattice
theorem hessianAlongGaugeDirection_holds (hA : ActionFacts.Statement) (hC : LeftChartFields.Claim)
    (hI : ComplexMatrix2.UnitaryLogarithmProperties) (hE : ComplexMatrix2.NormExpLogBasics) :
    HessianAlongGaugeDirection := by
  intro L n k hL hn _
  have hfin : Finite (PositiveEdge L n k 0) := ((hC.2.2 L k 0 hL (Nat.zero_le k)).1 n hn).2.1.1
  let _ : Fintype (PositiveEdge L n k 0) := Fintype.ofFinite _
  obtain ⟨⟨⟨p, hp⟩, -, -⟩, hg, -⟩ := hA L k n hL hn
  have ho : UniqueOrientation L n k := uniqueOrientation_of_admissible hL hn
  have hexp : ∀ X ∈ ComplexMatrix2.hermitianTraceless,
      ComplexMatrix2.matExp (Complex.I • X) ∈ PeriodicLattice.compactGaugeGroup :=
    fun X hX => (hI.1 X hX).2.2.2
  have hinv : ∀ Z : ComplexMatrix2, (ComplexMatrix2.matExp Z)⁻¹ = ComplexMatrix2.matExp (-Z) :=
    fun Z => (hE.2.1 Z).2.2.2.2.1
  let F : (PositiveEdge L n k 0 → ComplexMatrix2) → ℝ :=
    fun Y => MvPolynomial.eval (entryCoordinates Y) p
  have hF : ContDiff ℝ 2 F := contDiff_mvPolynomial_eval p entryCoordinates_contDiff
  have hFA : ∀ V ∈ fieldSpace L n k 0, plaquetteAction L n k V = F (restrictToPositiveEdges V) :=
    fun V hV => by
      rw [hp V hV, edgeEntryCoordinates_eq]
  refine eventually_nhdsWithin_of_forall fun U hU B hB l hl => ?_
  rw [leftSecondDeriv_covDiff hF hFA ho hexp hinv hg hU hB hl,
    edgeFormPairing_leftGradient hF hFA ho hexp hU (bracketTerm_mem ho hU hl hB)]
end Tower.GaugeHessian
end YangMills.Construction
end
