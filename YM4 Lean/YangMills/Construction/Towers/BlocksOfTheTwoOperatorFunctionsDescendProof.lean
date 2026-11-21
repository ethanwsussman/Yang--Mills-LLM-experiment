import YangMills.Construction.Towers.TheTorusMatricesOfTheMassiveOperatorFunctionsProof
import YangMills.Construction.Towers.BackgroundOperatorFromAMatrixOfItsFormProof
import YangMills.Construction.Towers.BlocksOfTheTwoOperatorFunctionsDescend
import YangMills.Construction.Towers.BracketOfTheFactorsDescends
import YangMills.Construction.Towers.FactorsOfTheBackgroundKernelDescend
import YangMills.Construction.Towers.TheBackgroundKernelAndTheCovariantLaplacianAreFormed
import YangMills.Construction.Towers.TheBackgroundKernelIsTheBracketOfItsFactors
import YangMills.Construction.Towers.TheBilinearFormOnASideGivesTheQuadraticForm
import YangMills.Construction.Towers.TheBracketOfTheMatricesOfTheBackgroundKernel
import YangMills.Construction.Towers.TheThreeKernelsOfATowerDescend
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.OperatorBlocksDescend
open YangMills.Construction.Matrices
open YangMills.Construction.LocalKernels YangMills.Construction.LocalKernels.Periodisation
open YangMills.Construction.PeriodicOperators (KernelMatrix applyKernel compKernel swapKernel saddleMatrix)
section Entries
variable {N N' N'' : Type}
theorem applyKernel_eq_sum [Fintype N] (K : KernelMatrix N N') (f : N → ℂ) (i : N') :
    applyKernel K f i = ∑ j, K i j * f j := tsum_fintype _
theorem applyKernel_indicator [DecidableEq N] (K : KernelMatrix N N') (ι : N) (ι' : N') :
    applyKernel K (fun κ => if κ = ι then 1 else 0) ι' = K ι' ι := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.PeriodicMatrices.applyKernel_indicator <;> assumption
theorem applyKernel_compKernel [Finite N] [Finite N'] (S : N'' → N' → ℂ) (T : N' → N → ℂ)
    (f : N → ℂ) :
    applyKernel (compKernel S T) f = applyKernel S (applyKernel T f) := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.PeriodicMatrices.applyKernel_compKernel <;> assumption
theorem tsum_eq_add_of_equiv_sum {X Y Z : Type} (e : Z ≃ X ⊕ Y) (f : Z → ℂ)
    (hf : (Function.support f).Finite) :
    ∑' z, f z = ∑' x, f (e.symm (.inl x)) + ∑' y, f (e.symm (.inr y)) := by
  have hg : (Function.support (f ∘ e.symm)).Finite := by
    have : Function.support (f ∘ e.symm) = e '' Function.support f := by
      ext s
      simp [Function.mem_support, Equiv.image_eq_preimage_symm]
    rw [this]
    exact hf.image _
  have hs : Summable (f ∘ e.symm) := summable_of_hasFiniteSupport hg
  rw [← Equiv.tsum_eq e.symm f]
  exact Summable.tsum_sum (hs.comp_injective Sum.inl_injective) (hs.comp_injective Sum.inr_injective)
end Entries
section BlockEvaluations
open PairedFunctionSpace
structure CoeffExtraction (S : PairedFunctionSpace) (P : Type) [Fintype P]
    (read : (S.index → ComplexMatrix2) → P → ℂ) where
  linearEquiv : S.complexSubmodule ≃ₗ[ℂ] (P → ℂ)
  linearEquiv_apply : ∀ f : S.complexSubmodule, linearEquiv f = read f
  real_mem_complex : ∀ f : S.realSubmodule, (f : S.index → ComplexMatrix2) ∈ S.complexSubmodule
  im_read : ∀ (f : S.realSubmodule) (p : P), (read f p).im = 0
  mem_real_of_im : ∀ f : S.complexSubmodule, (∀ p, (read f p).im = 0) →
    (f : S.index → ComplexMatrix2) ∈ S.realSubmodule
  pair_eq_sum : ∀ f g : S.complexSubmodule, S.pair f g = ∑ p, read f p * read g p
  finitelySupported : ∀ f, S.IsFinitelySupported f
variable {S S' : PairedFunctionSpace} {P P' : Type} [Fintype P] [Fintype P']
  {rd : (S.index → ComplexMatrix2) → P → ℂ} {rd' : (S'.index → ComplexMatrix2) → P' → ℂ}
namespace CoeffExtraction
variable (r : CoeffExtraction S P rd)
include r
def toComplex (f : S.realSubmodule) : S.complexSubmodule := ⟨f, r.real_mem_complex f⟩
theorem linearEquiv_toComplex (f : S.realSubmodule) : r.linearEquiv (r.toComplex f) = rd f :=
  r.linearEquiv_apply _
theorem map_read_add (f g : S.realSubmodule) :
    rd ((f + g : S.realSubmodule) : S.index → ComplexMatrix2) = rd f + rd g := by
  rw [← r.linearEquiv_toComplex, ← r.linearEquiv_toComplex, ← r.linearEquiv_toComplex, ← map_add]
  rfl
theorem map_read_smul (c : ℝ) (f : S.realSubmodule) :
    rd ((c • f : S.realSubmodule) : S.index → ComplexMatrix2) = (c : ℂ) • rd f := by
  rw [← r.linearEquiv_toComplex, ← r.linearEquiv_toComplex, ← map_smul]
  congr 1
def ofRealValues (c : P → ℝ) : S.realSubmodule :=
  ⟨r.linearEquiv.symm fun p => (c p : ℂ), r.mem_real_of_im _ fun p => by
    rw [← r.linearEquiv_apply, LinearEquiv.apply_symm_apply]
    exact Complex.ofReal_im _⟩
theorem read_ofRealValues (c : P → ℝ) : rd (r.ofRealValues c) = fun p => (c p : ℂ) := by
  rw [← r.linearEquiv_toComplex]
  show r.linearEquiv (r.linearEquiv.symm _) = _
  rw [LinearEquiv.apply_symm_apply]
theorem ofReal_re_read (f : S.realSubmodule) (p : P) : (((rd f p).re : ℝ) : ℂ) = rd f p :=
  Complex.ext (Complex.ofReal_re _) (by rw [Complex.ofReal_im]; exact (r.im_read f p).symm)
theorem toComplex_injective : Function.Injective r.toComplex := fun f g h =>
  Subtype.ext (congrArg (fun x : S.complexSubmodule => (x : S.index → ComplexMatrix2)) h)
def realCoords : S.realSubmodule ≃ₗ[ℝ] (P → ℝ) where
  toFun f p := (rd f p).re
  map_add' f g := by
    funext p
    rw [r.map_read_add]
    rfl
  map_smul' c f := by
    funext p
    rw [r.map_read_smul]
    simp
  invFun := r.ofRealValues
  left_inv f := by
    apply r.toComplex_injective
    apply r.linearEquiv.injective
    rw [r.linearEquiv_toComplex, r.linearEquiv_toComplex, r.read_ofRealValues]
    funext p
    exact r.ofReal_re_read f p
  right_inv c := by
    funext p
    show (rd (r.ofRealValues c) p).re = c p
    rw [r.read_ofRealValues]
    exact Complex.ofReal_re _
theorem ofReal_realCoords (f : S.realSubmodule) (p : P) :
    ((r.realCoords f p : ℝ) : ℂ) = rd f p := r.ofReal_re_read f p
theorem pair_eq_realCoords (f g : S.realSubmodule) :
    S.pair f g = ((∑ p, r.realCoords f p * r.realCoords g p : ℝ) : ℂ) := by
  have := r.pair_eq_sum (r.toComplex f) (r.toComplex g)
  push_cast
  simp only [r.ofReal_realCoords]
  exact this
theorem exists_innerCore :
    FiniteDimensional ℝ S.realSubmodule ∧ ∃ c : InnerProductSpace.Core ℝ S.realSubmodule,
      ∀ f g : S.realSubmodule, c.inner f g = (S.pair f g).re := by
  refine ⟨LinearEquiv.finiteDimensional r.realCoords.symm, ?_⟩
  refine ⟨{
    inner := fun f g => ∑ p, r.realCoords f p * r.realCoords g p
    conj_inner_symm := fun f g => by
      simp only [conj_trivial]
      exact Finset.sum_congr rfl fun p _ => mul_comm _ _
    re_inner_nonneg := fun f => by
      simp only [RCLike.re_to_real]
      exact Finset.sum_nonneg fun p _ => mul_self_nonneg _
    add_left := fun f f' g => by
      simp only [map_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    smul_left := fun f g c => by
      simp only [map_smul, Pi.smul_apply, smul_eq_mul, conj_trivial, Finset.mul_sum, mul_assoc]
    definite := fun f h => by
      have h₀ := (Finset.sum_eq_zero_iff_of_nonneg fun p _ => mul_self_nonneg _).1 h
      apply r.realCoords.injective
      funext p
      simpa using h₀ p (Finset.mem_univ p) }, fun f g => ?_⟩
  rw [r.pair_eq_realCoords, Complex.ofReal_re]
  rfl
end CoeffExtraction
variable (r : CoeffExtraction S P rd) (r' : CoeffExtraction S' P' rd')
include r r'
theorem exists_transpose_of_matrix (m : S.realSubmodule →ₗ[ℝ] S'.realSubmodule) (M : KernelMatrix P P')
    (hM : ∀ f : S.realSubmodule, rd' (m f) = applyKernel M (rd f)) :
    ∃ m' : S'.realSubmodule →ₗ[ℝ] S.realSubmodule,
      (∀ g : S'.realSubmodule, rd (m' g) = applyKernel (swapKernel M) (rd' g)) ∧
      (∀ (g : S'.realSubmodule) (f : S.realSubmodule), S.pair (m' g) f = S'.pair g (m f)) ∧
      realTransposeMap m = m' := by
  classical
  have hMsum : ∀ (c : P → ℂ) (q : P'), applyKernel M c q = ∑ p, M q p * c p :=
    fun c q => applyKernel_eq_sum M c q
  have hMtsum : ∀ (c : P' → ℂ) (p : P),
      applyKernel (swapKernel M) c p = ∑ q, M q p * c q :=
    fun c p => applyKernel_eq_sum _ c p
  have hre : ∀ q p, (((M q p).re : ℝ) : ℂ) = M q p := by
    intro q p
    have h₁ := congrFun (hM (r.ofRealValues fun i => if i = p then 1 else 0)) q
    rw [r.read_ofRealValues] at h₁
    have h₂ : (fun i => (((if i = p then 1 else 0 : ℝ)) : ℂ)) = fun i => if i = p then 1 else 0 := by
      funext i
      split_ifs <;> simp
    rw [h₂, applyKernel_indicator] at h₁
    rw [← h₁]
    exact r'.ofReal_re_read _ q
  let R := r.realCoords
  let R' := r'.realCoords
  let m' : S'.realSubmodule →ₗ[ℝ] S.realSubmodule := R.symm.toLinearMap ∘ₗ
    (Matrix.of fun p q => (M q p).re).mulVecLin ∘ₗ R'.toLinearMap
  have hm' : ∀ g : S'.realSubmodule, rd (m' g) = applyKernel (swapKernel M) (rd' g) := by
    intro g
    funext p
    rw [← r.ofReal_realCoords, hMtsum]
    have : R (m' g) p = ∑ q, (M q p).re * R' g q := by
      simp [m', Matrix.mulVec, dotProduct]
    show ((R (m' g) p : ℝ) : ℂ) = _
    rw [this]
    push_cast
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hre, r'.ofReal_realCoords]
  have hsum : ∀ (c : P → ℂ) (d : P' → ℂ),
      ∑ p, applyKernel (swapKernel M) d p * c p = ∑ q, d q * applyKernel M c q := by
    intro c d
    simp only [hMsum, hMtsum, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => by ring
  have hp : ∀ (g : S'.realSubmodule) (f : S.realSubmodule), S.pair (m' g) f = S'.pair g (m f) := by
    intro g f
    have h₁ := r.pair_eq_sum (r.toComplex (m' g)) (r.toComplex f)
    have h₂ := r'.pair_eq_sum (r'.toComplex g) (r'.toComplex (m f))
    refine h₁.trans (Eq.trans ?_ h₂.symm)
    show ∑ p, rd (m' g) p * rd f p = ∑ q, rd' g q * rd' (m f) q
    rw [hm', hM]
    exact hsum _ _
  refine ⟨m', hm', hp, ?_⟩
  let e := r.linearEquiv
  let e' := r'.linearEquiv
  let Tc : S.complexSubmodule →ₗ[ℂ] S'.complexSubmodule := e'.symm.toLinearMap ∘ₗ
    (Matrix.of M).mulVecLin ∘ₗ e.toLinearMap
  let Tt : S'.complexSubmodule →ₗ[ℂ] S.complexSubmodule := e.symm.toLinearMap ∘ₗ
    (Matrix.of fun p q => M q p).mulVecLin ∘ₗ e'.toLinearMap
  have hTc : ∀ h, e' (Tc h) = applyKernel M (e h) := by
    intro h
    funext q
    rw [hMsum]
    simp [Tc, Matrix.mulVec, dotProduct]
  have hTt : ∀ h, e (Tt h) = applyKernel (swapKernel M) (e' h) := by
    intro h
    funext p
    rw [hMtsum]
    simp [Tt, Matrix.mulVec, dotProduct]
  have hTcadd : ∀ (c d : P → ℂ) (z : ℂ),
      applyKernel M (c + z • d) = applyKernel M c + z • applyKernel M d := by
    intro c d z
    funext q
    simp only [hMsum, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
      Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun p _ => by ring
  have hdecomp : ∀ h : S.complexSubmodule, ∃ f f' : S.realSubmodule,
      (h : S.index → ComplexMatrix2) = f + Complex.I • (f' : S.index → ComplexMatrix2) := by
    intro h
    refine ⟨r.ofRealValues fun p => (e h p).re, r.ofRealValues fun p => (e h p).im, ?_⟩
    have : h = r.toComplex (r.ofRealValues fun p => (e h p).re) +
        Complex.I • r.toComplex (r.ofRealValues fun p => (e h p).im) := by
      apply e.injective
      rw [map_add, map_smul]
      show e h = r.linearEquiv (r.toComplex _) + Complex.I • r.linearEquiv (r.toComplex _)
      rw [r.linearEquiv_toComplex, r.linearEquiv_toComplex, r.read_ofRealValues, r.read_ofRealValues]
      funext p
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [mul_comm]
      exact (Complex.re_add_im _).symm
    exact congrArg Subtype.val this
  have hcont : IsComplexification m Tc := by
    intro f f' h hh
    have hh' : h = r.toComplex f + Complex.I • r.toComplex f' := Subtype.ext hh
    have : Tc h = r'.toComplex (m f) + Complex.I • r'.toComplex (m f') := by
      apply e'.injective
      rw [hTc, map_add, map_smul, hh', map_add, map_smul]
      show applyKernel M (r.linearEquiv (r.toComplex f) + Complex.I • r.linearEquiv (r.toComplex f')) =
        r'.linearEquiv (r'.toComplex (m f)) + Complex.I • r'.linearEquiv (r'.toComplex (m f'))
      rw [r.linearEquiv_toComplex, r.linearEquiv_toComplex, r'.linearEquiv_toComplex,
        r'.linearEquiv_toComplex, hM, hM, hTcadd]
    exact congrArg Subtype.val this
  have hcu : complexification m = Tc := by
    have hs : IsComplexification m (complexification m) :=
      Classical.epsilon_spec (p := IsComplexification m) ⟨Tc, hcont⟩
    ext1 h
    apply Subtype.ext
    obtain ⟨f, f', hf⟩ := hdecomp h
    rw [hs f f' h hf, hcont f f' h hf]
  have htr : IsTransposeMap Tc Tt := by
    intro g f _
    rw [r.pair_eq_sum, r'.pair_eq_sum]
    simp only [← r.linearEquiv_apply, ← r'.linearEquiv_apply]
    show ∑ p, e (Tt g) p * e f p = ∑ q, e' g q * e' (Tc f) q
    rw [hTt, hTc]
    exact hsum _ _
  have htu : transposeMap Tc = Tt := by
    have hs : IsTransposeMap Tc (transposeMap Tc) :=
      Classical.epsilon_spec (p := IsTransposeMap Tc) ⟨Tt, htr⟩
    ext1 g
    apply e.injective
    funext p
    have h₁ := hs g (e.symm fun i => if i = p then 1 else 0) (r.finitelySupported _)
    have h₂ := htr g (e.symm fun i => if i = p then 1 else 0) (r.finitelySupported _)
    rw [← h₂, r.pair_eq_sum, r.pair_eq_sum] at h₁
    simp only [← r.linearEquiv_apply] at h₁
    have h₃ : r.linearEquiv (e.symm fun i => if i = p then 1 else 0) =
        fun i => if i = p then 1 else 0 :=
      LinearEquiv.apply_symm_apply e _
    rw [h₃] at h₁
    simpa using h₁
  have hrt : IsRealTransposeMap m m' := by
    intro g h hh
    rw [hcu, htu]
    have hh' : h = r'.toComplex g := Subtype.ext hh
    have : r.toComplex (m' g) = Tt h := by
      apply e.injective
      rw [hTt, hh']
      show r.linearEquiv (r.toComplex _) = applyKernel _ (r'.linearEquiv (r'.toComplex g))
      rw [r.linearEquiv_toComplex, r'.linearEquiv_toComplex, hm']
    exact congrArg Subtype.val this
  have hs : IsRealTransposeMap m (realTransposeMap m) :=
    Classical.epsilon_spec (p := IsRealTransposeMap m) ⟨m', hrt⟩
  ext1 g
  apply Subtype.ext
  rw [hs g (r'.toComplex g) rfl, hrt g (r'.toComplex g) rfl]
end BlockEvaluations
theorem saddlePointOperatorOfInnerCores_apply {V V' : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] [AddCommGroup V'] [Module ℝ V'] [FiniteDimensional ℝ V']
    (c : InnerProductSpace.Core ℝ V) (c' : InnerProductSpace.Core ℝ V') (X : V →ₗ[ℝ] V)
    (M : V →ₗ[ℝ] V') (m' : V' →ₗ[ℝ] V) (h : ∀ y x, c.inner (m' y) x = c'.inner y (M x))
    (x : V × V') :
    GaussianConstraint.saddlePointOperatorOfInnerCores c c' X M x = (X x.1 + m' x.2, M x.1) := by
  letI := c.toNormedAddCommGroup
  letI := InnerProductSpace.ofCore c.toCore
  letI := c'.toNormedAddCommGroup
  letI := InnerProductSpace.ofCore c'.toCore
  have ha : LinearMap.adjoint M x.2 = m' x.2 := by
    refine ext_inner_right ℝ fun v => ?_
    rw [LinearMap.adjoint_inner_left]
    exact (h x.2 v).symm
  show GaussianConstraint.saddlePointOperator X M x = _
  simp [GaussianConstraint.saddlePointOperator, ha]
section Coefficients
open YangMills.Construction.OneLoop (pauliCoordinateEquiv)
theorem pauliCoeff_eq_coordinate {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.traceless) (a : Fin 3) :
    pauliCoeff a X = pauliCoordinateEquiv ⟨X, h⟩ a := dif_pos h
theorem pauli_combination_mem_traceless (x : Fin 3 → ℂ) :
    ∑ a, x a • ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_smul_pauli_mem <;> assumption
theorem pauliCoeff_combination (x : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ b, x b • ComplexMatrix2.pauliFamily b) = x a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
theorem combination_pauliCoeff {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
theorem pauliCoeff_add {X Y : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (hY : Y ∈ ComplexMatrix2.traceless) (a : Fin 3) :
    pauliCoeff a (X + Y) = pauliCoeff a X + pauliCoeff a Y := by apply _root_.YangMills.Construction.Tower.ComplexFieldRescaledRelations.pauliCoeff_add <;> assumption
theorem pauliCoeff_smul (c : ℂ) {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) (a : Fin 3) :
    pauliCoeff a (c • X) = c * pauliCoeff a X := by
  rw [pauliCoeff_eq_coordinate hX, pauliCoeff_eq_coordinate (ComplexMatrix2.traceless.smul_mem c hX)]
  exact congrFun (map_smul pauliCoordinateEquiv c ⟨X, hX⟩) a
theorem pauliCoeff_im_eq_zero {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.hermitianTraceless)
    (a : Fin 3) : (pauliCoeff a X).im = 0 := by apply _root_.YangMills.SharedProofs.p23717 <;> assumption
theorem halfTrace_mul_eq_sum {X Y : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (hY : Y ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.halfTrace (X * Y) = ∑ a, pauliCoeff a X * pauliCoeff a Y := by apply _root_.YangMills.Construction.Tower.HessianOfFormMatrix.halfTrace_mul_eq_sum <;> assumption
theorem real_combination_mem_hermitianTraceless (c : Fin 3 → ℝ) :
    ∑ a, (c a : ℂ) • ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.PeriodicMatrices.real_pauli_sum_mem_hermitianTraceless <;> assumption
theorem mem_hermitianTraceless_of_im {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.traceless)
    (him : ∀ a, (pauliCoeff a X).im = 0) : X ∈ ComplexMatrix2.hermitianTraceless := by
  have e : ∑ a, (((pauliCoeff a X).re : ℝ) : ℂ) • ComplexMatrix2.pauliFamily a = X := by
    conv_rhs => rw [← combination_pauliCoeff h]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    exact Complex.ext (Complex.ofReal_re _) (by rw [Complex.ofReal_im]; exact (him a).symm)
  rw [← e]
  exact real_combination_mem_hermitianTraceless _
theorem tracelessFunctions_apply_mem {σ : Type} (f : Matrices.GroupLieProduct.tracelessFunctions σ)
    (x : σ) : (f : σ → ComplexMatrix2) x ∈ ComplexMatrix2.traceless :=
  Submodule.mem_pi.1 f.2 x (mem_univ x)
def pauliCoeffEquiv (σ : Type) :
    Matrices.GroupLieProduct.tracelessFunctions σ ≃ₗ[ℂ] (Fin 3 × σ → ℂ) where
  toFun f := toPauliCoeffs (f : σ → ComplexMatrix2)
  map_add' f g := funext fun t =>
    pauliCoeff_add (tracelessFunctions_apply_mem f t.2) (tracelessFunctions_apply_mem g t.2) t.1
  map_smul' c f := funext fun t => pauliCoeff_smul c (tracelessFunctions_apply_mem f t.2) t.1
  invFun c := ⟨ofPauliCoeffs c, Submodule.mem_pi.2 fun x _ =>
    pauli_combination_mem_traceless fun a => c (a, x)⟩
  left_inv f := Subtype.ext (funext fun x => combination_pauliCoeff (tracelessFunctions_apply_mem f x))
  right_inv c := funext fun t => pauliCoeff_combination (fun a => c (a, t.2)) t.1
theorem traceFinsumPairing_eq_sum {σ P : Type} [Fintype P] (ψ : P ≃ Fin 3 × σ)
    (f g : σ → ComplexMatrix2) (hf : ∀ x, f x ∈ ComplexMatrix2.traceless)
    (hg : ∀ x, g x ∈ ComplexMatrix2.traceless) :
    traceFinsumPairing f g = ∑ p, toPauliCoeffs f (ψ p) * toPauliCoeffs g (ψ p) := by
  have hfin : Finite σ :=
    Finite.of_surjective (fun p : P => (ψ p).2) fun x => ⟨ψ.symm (0, x), by simp⟩
  have := Fintype.ofFinite σ
  rw [Equiv.sum_comp ψ (fun t => toPauliCoeffs f t * toPauliCoeffs g t),
    Fintype.sum_prod_type_right]
  unfold traceFinsumPairing
  rw [finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl fun b _ => halfTrace_mul_eq_sum (hf b) (hg b)
end Coefficients
section Torus
variable {L n k j : ℕ}
def extendFromPositive (g : PositiveEdge L n k j → ComplexMatrix2) : Edge L n k j → ComplexMatrix2 :=
  open Classical in extendOddly fun b => if h : b.IsPositivelyOriented then g ⟨b, h⟩ else 0
theorem extendFromPositive_of_pos (g : PositiveEdge L n k j → ComplexMatrix2) {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) : extendFromPositive g b = g ⟨b, hb⟩ := by
  unfold extendFromPositive
  rw [extendOddly, if_pos hb]
  exact dif_pos hb
theorem extendFromPositive_of_neg (g : PositiveEdge L n k j → ComplexMatrix2) {b : Edge L n k j}
    (hb : ¬b.IsPositivelyOriented) (hb' : b.opposite.IsPositivelyOriented) :
    extendFromPositive g b = -g ⟨b.opposite, hb'⟩ := by
  unfold extendFromPositive
  rw [extendOddly, if_neg hb]
  exact congrArg Neg.neg (dif_pos hb')
def positiveEdgeEquiv
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented) :
    complexEdgeForms L n k j ≃ₗ[ℂ]
      Matrices.GroupLieProduct.tracelessFunctions (PositiveEdge L n k j) where
  toFun B := ⟨restrictToPositiveEdges (B : Edge L n k j → ComplexMatrix2),
    Submodule.mem_pi.2 fun b _ => B.2.1 b.1 b.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun g := ⟨extendFromPositive (g : PositiveEdge L n k j → ComplexMatrix2), by
    refine ⟨fun b hb => ?_, fun b => ?_⟩
    · rw [extendFromPositive_of_pos _ hb]
      exact tracelessFunctions_apply_mem g _
    · rcases hx b with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · rw [extendFromPositive_of_neg _ h₂ h₁, extendFromPositive_of_pos _ h₁]
        rfl
      · rw [extendFromPositive_of_pos _ h₁, extendFromPositive_of_neg _ h₂ h₁, neg_neg]⟩
  left_inv B := by
    apply Subtype.ext
    funext b
    show extendFromPositive (restrictToPositiveEdges (B : Edge L n k j → ComplexMatrix2)) b = _
    rcases hx b with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [extendFromPositive_of_pos _ h₁]
      rfl
    · rw [extendFromPositive_of_neg _ h₂ h₁]
      show -(B : Edge L n k j → ComplexMatrix2) b.opposite = _
      rw [B.2.2 b, neg_neg]
  right_inv g := by
    apply Subtype.ext
    funext b
    exact extendFromPositive_of_pos _ b.2
def imageCarrierEquiv (A : CellClass k)
    (hs : Function.Surjective
      (Cell.proj n : Cell L k A.level A.cellType → QuotientCell L n k A.level A.cellType)) :
    A.colourPairs.ImageCarrier L n ≃ Fin 3 × QuotientCell L n k A.level A.cellType :=
  Equiv.ofBijective (fun κ => κ.2.1) (by
    constructor
    · rintro ⟨⟨⟩, t, ht⟩ ⟨⟨⟩, t', ht'⟩ h
      have h' : t = t' := h
      subst h'
      rfl
    · rintro ⟨a, b⟩
      obtain ⟨x, hx⟩ := hs b
      exact ⟨⟨(), ⟨(a, b), ⟨(a, x), congrArg (Prod.mk a) hx⟩⟩⟩, rfl⟩)
def vertexCoordinate (j : ℕ) (h : j ≤ k)
    (hs : Function.Surjective (Cell.proj n : Cell L k j .vertex → QuotientCell L n k j .vertex))
    [Fintype ((CellClass.vertexClass k j h).colourPairs.ImageCarrier L n)] :
    CoeffExtraction (CellClass.quotSpace L n (CellClass.vertexClass k j h))
      ((CellClass.vertexClass k j h).colourPairs.ImageCarrier L n)
      (CellClass.quotCoeffsOn L n (CellClass.vertexClass k j h)) :=
  let ψ := imageCarrierEquiv (L := L) (n := n) (CellClass.vertexClass k j h) hs
  { linearEquiv := (pauliCoeffEquiv (Vertex L n k j)).trans (LinearEquiv.funCongrLeft ℂ ℂ ψ)
    linearEquiv_apply := fun _ => rfl
    real_mem_complex := fun f =>
      Submodule.mem_pi.2 fun x _ => (Submodule.mem_pi.1 f.2 x (mem_univ x)).2
    im_read := fun f p => pauliCoeff_im_eq_zero (Submodule.mem_pi.1 f.2 _ (mem_univ _)) _
    mem_real_of_im := fun f h' => Submodule.mem_pi.2 fun x _ =>
      mem_hermitianTraceless_of_im (tracelessFunctions_apply_mem f x) fun a => by
        have e : (ψ (ψ.symm (a, x))) = (a, x) := ψ.apply_symm_apply _
        have e' := congrArg (fun t : Fin 3 × Vertex L n k j =>
          (toPauliCoeffs (show Vertex L n k j → ComplexMatrix2 from f.1) t).im) e
        exact e'.symm.trans (h' (ψ.symm (a, x)))
    pair_eq_sum := fun f g => traceFinsumPairing_eq_sum ψ _ _
      (tracelessFunctions_apply_mem f) (tracelessFunctions_apply_mem g)
    finitelySupported := fun f => by
      have : Finite (Vertex L n k j) := Finite.of_surjective
        (fun p : (CellClass.vertexClass k j h).colourPairs.ImageCarrier L n => (ψ p).2)
        fun x => ⟨ψ.symm (0, x), by simp⟩
      exact Set.toFinite _ }
def edgePauliCoordinates (j : ℕ) (h : j ≤ k)
    (hs : Function.Surjective (Cell.proj n : Cell L k j .edge → QuotientCell L n k j .edge))
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    [Fintype ((CellClass.edgeClass k j h).colourPairs.ImageCarrier L n)] :
    CoeffExtraction (CellClass.quotSpace L n (CellClass.edgeClass k j h))
      ((CellClass.edgeClass k j h).colourPairs.ImageCarrier L n)
      (CellClass.quotCoeffsOn L n (CellClass.edgeClass k j h)) :=
  let ψ := imageCarrierEquiv (L := L) (n := n) (CellClass.edgeClass k j h) hs
  { linearEquiv := ((positiveEdgeEquiv hx).trans (pauliCoeffEquiv (PositiveEdge L n k j))).trans
      (LinearEquiv.funCongrLeft ℂ ℂ ψ)
    linearEquiv_apply := fun _ => rfl
    real_mem_complex := fun f => ⟨fun b hb => (f.2.1 b hb).2, f.2.2⟩
    im_read := fun f p => pauliCoeff_im_eq_zero (f.2.1 _ (ψ p).2.2) _
    mem_real_of_im := fun f h' => ⟨fun b hb =>
      mem_hermitianTraceless_of_im (f.2.1 b hb) fun a => by
        have e : (ψ (ψ.symm (a, ⟨b, hb⟩))) = (a, ⟨b, hb⟩) := ψ.apply_symm_apply _
        have e' := congrArg (fun t : Fin 3 × PositiveEdge L n k j =>
          (toPauliCoeffs
            (restrictToPositiveEdges (show Edge L n k j → ComplexMatrix2 from f.1)) t).im) e
        exact e'.symm.trans (h' (ψ.symm (a, ⟨b, hb⟩))), f.2.2⟩
    pair_eq_sum := fun f g => traceFinsumPairing_eq_sum ψ _ _
      (fun b => f.2.1 b.1 b.2) (fun b => g.2.1 b.1 b.2)
    finitelySupported := fun f => by
      have : Finite (PositiveEdge L n k j) := Finite.of_surjective
        (fun p : (CellClass.edgeClass k j h).colourPairs.ImageCarrier L n => (ψ p).2)
        fun x => ⟨ψ.symm (0, x), by simp⟩
      exact Set.toFinite _ }
end Torus
section Kernels
variable (L n : ℕ) {k : ℕ}
theorem applyKernel_smul {N N' : Type} (z : ℂ) (T : KernelMatrix N N') (f : N → ℂ) :
    applyKernel (z • T) f = z • applyKernel T f := by
  funext i
  simp only [applyKernel, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact tsum_mul_left
theorem kernelDescends_smul {I I' : WeightedIndexSet k} {T : KernelMatrix (Idx L I) (Idx L I')}
    {M : KernelMatrix (I.ImageCarrier L n) (I'.ImageCarrier L n)} (z : ℂ)
    (h : KernelDescends L n I I' T M) : KernelDescends L n I I' (z • T) (z • M) := by
  obtain ⟨⟨R, hR, hl⟩, hd⟩ := h
  refine ⟨⟨R, hR, fun ι' ι hι => ?_⟩, fun f => ?_⟩
  · show z * T ι' ι = 0
    rw [hl ι' ι hι, mul_zero]
  · rw [applyKernel_smul, hd, applyKernel_smul]
    rfl
theorem isRLocal_mono {I I' : WeightedIndexSet k} {T : KernelMatrix (Idx L I) (Idx L I')}
    {R R' : ℝ} (h : IsRLocal L I I' R T) (hR : R ≤ R') : IsRLocal L I I' R' T :=
  fun ι' ι hι => h ι' ι fun h' => hι (h'.trans hR)
def idxEquivColourCell (A : CellClass k) : Idx L A.colourPairs ≃ ColourCell L A where
  toFun ι := ι.2
  invFun c := ⟨(), c⟩
  left_inv := fun ⟨⟨⟩, _⟩ => rfl
  right_inv _ := rfl
theorem kernelOnIdx_compKernel (A A' A'' : CellClass k)
    (T : KernelMatrix (ColourCell L A) (ColourCell L A'))
    (S : KernelMatrix (ColourCell L A'') (ColourCell L A)) :
    kernelOnIdx L A'' A' (compKernel T S) =
      compKernel (kernelOnIdx L A A' T) (kernelOnIdx L A'' A S) := by
  funext ι' ι
  exact (Equiv.tsum_eq (idxEquivColourCell L A) fun c => T ι'.2 c * S c ι.2).symm
def pairedSumIdxEquiv (A A' : CellClass k) :
    Idx L (pairedSum A A') ≃ Idx L A.colourPairs ⊕ Idx L A'.colourPairs where
  toFun
    | ⟨.inl p, ι⟩ => .inl ⟨p, ι⟩
    | ⟨.inr p, ι⟩ => .inr ⟨p, ι⟩
  invFun
    | .inl ι => ⟨.inl ι.1, ι.2⟩
    | .inr ι => ⟨.inr ι.1, ι.2⟩
  left_inv := by rintro ⟨_ | _, _⟩ <;> rfl
  right_inv := by rintro (_ | _) <;> rfl
def pairedSumImageEquiv (A A' : CellClass k) :
    (pairedSum A A').ImageCarrier L n ≃
      A.colourPairs.ImageCarrier L n ⊕ A'.colourPairs.ImageCarrier L n where
  toFun
    | ⟨.inl p, ι⟩ => .inl ⟨p, ι⟩
    | ⟨.inr p, ι⟩ => .inr ⟨p, ι⟩
  invFun
    | .inl ι => ⟨.inl ι.1, ι.2⟩
    | .inr ι => ⟨.inr ι.1, ι.2⟩
  left_inv := by rintro ⟨_ | _, _⟩ <;> rfl
  right_inv := by rintro (_ | _) <;> rfl
def saddleBlockMatrix (A A' : CellClass k)
    (X : KernelMatrix (A.colourPairs.ImageCarrier L n) (A.colourPairs.ImageCarrier L n))
    (Mt : KernelMatrix (A'.colourPairs.ImageCarrier L n) (A.colourPairs.ImageCarrier L n))
    (M : KernelMatrix (A.colourPairs.ImageCarrier L n) (A'.colourPairs.ImageCarrier L n)) :
    KernelMatrix ((pairedSum A A').ImageCarrier L n) ((pairedSum A A').ImageCarrier L n)
  | ⟨.inl p', c'⟩, ⟨.inl p, c⟩ => X ⟨p', c'⟩ ⟨p, c⟩
  | ⟨.inl p', c'⟩, ⟨.inr p, c⟩ => Mt ⟨p', c'⟩ ⟨p, c⟩
  | ⟨.inr p', c'⟩, ⟨.inl p, c⟩ => M ⟨p', c'⟩ ⟨p, c⟩
  | ⟨.inr _, _⟩, ⟨.inr _, _⟩ => 0
variable {L n}
theorem saddleBlock_descends (hE : LocalKernelFacts (k := k) L) (A A' : CellClass k)
    [Finite (A.colourPairs.ImageCarrier L n)] [Finite (A'.colourPairs.ImageCarrier L n)]
    {T : KernelMatrix (ColourCell L A) (ColourCell L A)}
    {Tt : KernelMatrix (ColourCell L A') (ColourCell L A)}
    {Q : KernelMatrix (ColourCell L A) (ColourCell L A')}
    {X : KernelMatrix (A.colourPairs.ImageCarrier L n) (A.colourPairs.ImageCarrier L n)}
    {Mt : KernelMatrix (A'.colourPairs.ImageCarrier L n) (A.colourPairs.ImageCarrier L n)}
    {M : KernelMatrix (A.colourPairs.ImageCarrier L n) (A'.colourPairs.ImageCarrier L n)}
    (hX : KernelDescends L n A.colourPairs A.colourPairs (kernelOnIdx L A A T) X)
    (hT : KernelDescends L n A'.colourPairs A.colourPairs (kernelOnIdx L A' A Tt) Mt)
    (hQ : KernelDescends L n A.colourPairs A'.colourPairs (kernelOnIdx L A A' Q) M) :
    KernelDescends L n (pairedSum A A') (pairedSum A A')
      (kernelOnPairedSum L A A' (saddleMatrix T Tt Q)) (saddleBlockMatrix L n A A' X Mt M) := by
  obtain ⟨⟨R₁, h₁, l₁⟩, d₁⟩ := hX
  obtain ⟨⟨R₂, h₂, l₂⟩, d₂⟩ := hT
  obtain ⟨⟨R₃, h₃, l₃⟩, d₃⟩ := hQ
  have hR : 0 ≤ max R₁ (max R₂ R₃) := le_max_of_le_left h₁
  have hloc : IsRLocal L (pairedSum A A') (pairedSum A A') (max R₁ (max R₂ R₃))
      (kernelOnPairedSum L A A' (saddleMatrix T Tt Q)) := by
    rintro ⟨_ | _, i'⟩ ⟨_ | _, i⟩ hd
    · exact l₁ ⟨(), i'⟩ ⟨(), i⟩ fun h => hd (h.trans (le_max_left _ _))
    · exact l₂ ⟨(), i'⟩ ⟨(), i⟩ fun h => hd (h.trans
        ((le_max_left _ _).trans (le_max_right _ _)))
    · exact l₃ ⟨(), i'⟩ ⟨(), i⟩ fun h => hd (h.trans
        ((le_max_right _ _).trans (le_max_right _ _)))
    · rfl
  refine ⟨⟨_, hR, hloc⟩, fun f => ?_⟩
  let g₁ : A.colourPairs.ImageCarrier L n → ℂ := fun c => f ⟨.inl c.1, c.2⟩
  let g₂ : A'.colourPairs.ImageCarrier L n → ℂ := fun c => f ⟨.inr c.1, c.2⟩
  funext ι'
  have hfin := ((hE _ _ _ hR _ hloc).1 ((pairedSum A A').lift L n f) ι')
  have hfinite : Finite ((pairedSum A A').ImageCarrier L n) :=
    Finite.of_equiv _ (pairedSumImageEquiv L n A A').symm
  show ∑' ι, _ = ∑' κ, _
  rw [tsum_eq_add_of_equiv_sum (pairedSumIdxEquiv L A A') _ hfin,
    tsum_eq_add_of_equiv_sum (pairedSumImageEquiv L n A A') _ (Set.toFinite _)]
  rcases ι' with ⟨_ | _, i'⟩
  · exact congrArg₂ (· + ·) (congrFun (d₁ g₁) ⟨(), i'⟩) (congrFun (d₂ g₂) ⟨(), i'⟩)
  · have a₃ := congrFun (d₃ g₁) ⟨(), i'⟩
    show (∑' x, kernelOnIdx L A A' Q ⟨(), i'⟩ x * _) + (∑' y, 0 * _) =
      (∑' c, M ⟨(), _⟩ c * _) + (∑' c, 0 * _)
    simp only [zero_mul, tsum_zero, add_zero]
    exact a₃
theorem saddleBlock_isPauliMatrix (A A' : CellClass k)
    [Finite (A.colourPairs.ImageCarrier L n)] [Finite (A'.colourPairs.ImageCarrier L n)]
    {p : Submodule ℝ ((CellClass.quotSpace L n A).index → ComplexMatrix2)}
    {p' : Submodule ℝ ((CellClass.quotSpace L n A').index → ComplexMatrix2)}
    (m : (p × p') →ₗ[ℝ] p × p')
    {X : KernelMatrix (A.colourPairs.ImageCarrier L n) (A.colourPairs.ImageCarrier L n)}
    {Mt : KernelMatrix (A'.colourPairs.ImageCarrier L n) (A.colourPairs.ImageCarrier L n)}
    {M : KernelMatrix (A.colourPairs.ImageCarrier L n) (A'.colourPairs.ImageCarrier L n)}
    (h₁ : ∀ x : p × p', CellClass.quotCoeffsOn L n A ((m x).1 : _ → ComplexMatrix2) =
      applyKernel X (CellClass.quotCoeffsOn L n A (x.1 : _ → ComplexMatrix2)) +
        applyKernel Mt (CellClass.quotCoeffsOn L n A' (x.2 : _ → ComplexMatrix2)))
    (h₂ : ∀ x : p × p', CellClass.quotCoeffsOn L n A' ((m x).2 : _ → ComplexMatrix2) =
      applyKernel M (CellClass.quotCoeffsOn L n A (x.1 : _ → ComplexMatrix2))) :
    IsPauliMatrixOfPair L n A A' m (saddleBlockMatrix L n A A' X Mt M) := by
  intro x
  funext κ'
  have hfinite : Finite ((pairedSum A A').ImageCarrier L n) :=
    Finite.of_equiv _ (pairedSumImageEquiv L n A A').symm
  show _ = ∑' κ, _
  rw [tsum_eq_add_of_equiv_sum (pairedSumImageEquiv L n A A') _ (Set.toFinite _)]
  rcases κ' with ⟨p | p, c'⟩
  · exact congrFun (h₁ x) ⟨p, c'⟩
  · have a := congrFun (h₂ x) ⟨p, c'⟩
    show _ = (∑' c, M ⟨p, c'⟩ c * _) + (∑' c, 0 * _)
    simp only [zero_mul, tsum_zero, add_zero]
    exact a
end Kernels
section Maps
variable {L n k : ℕ}
theorem linearMapWithValues_apply {α β : Type*} {p : Submodule ℝ (α → ComplexMatrix2)}
    {p' : Submodule ℝ (β → ComplexMatrix2)} {f : (α → ComplexMatrix2) → β → ComplexMatrix2}
    (h : ∃ T : p →ₗ[ℝ] p', ∀ x : p, (T x : β → ComplexMatrix2) = f x) (x : p) :
    (linearMapWithValues p p' f x : β → ComplexMatrix2) = f x := by apply _root_.YangMills.Construction.Tower.RescaledBackgroundFormFiniteSide.linearMapWithValues_apply <;> assumption
theorem saddleOnEdgeForms_apply (h : EdgeFormsEuclidean L n k 0 ∧ EdgeFormsEuclidean L n k k)
    (X : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k 0)
    (M : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k k)
    (m' : edgeFormSpace L n k k →ₗ[ℝ] edgeFormSpace L n k 0)
    (hp : ∀ (y : edgeFormSpace L n k k) (x : edgeFormSpace L n k 0),
      edgeFormPairing (m' y : Edge L n k 0 → ComplexMatrix2) (x : Edge L n k 0 → ComplexMatrix2) =
        edgeFormPairing (y : Edge L n k k → ComplexMatrix2) (M x : Edge L n k k → ComplexMatrix2))
    (x : edgeFormSpace L n k 0 × edgeFormSpace L n k k) :
    saddleOnEdgeForms X M x = (X x.1 + m' x.2, M x.1) := by
  haveI := h.1.1
  haveI := h.2.1
  unfold saddleOnEdgeForms
  rw [dif_pos h]
  refine saddlePointOperatorOfInnerCores_apply _ _ X M m' (fun y x' => ?_) x
  rw [h.1.2.choose_spec, h.2.2.choose_spec, hp]
theorem saddleOnVertexFunctions_apply
    (h : VertexFunctionsEuclidean L n k 0 ∧ VertexFunctionsEuclidean L n k k)
    (X : vertexFunctionSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k 0)
    (M : vertexFunctionSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k k)
    (m' : vertexFunctionSpace L n k k →ₗ[ℝ] vertexFunctionSpace L n k 0)
    (hp : ∀ (y : vertexFunctionSpace L n k k) (x : vertexFunctionSpace L n k 0),
      traceFinsumPairing (m' y : Vertex L n k 0 → ComplexMatrix2)
          (x : Vertex L n k 0 → ComplexMatrix2) =
        traceFinsumPairing (y : Vertex L n k k → ComplexMatrix2)
          (M x : Vertex L n k k → ComplexMatrix2))
    (x : vertexFunctionSpace L n k 0 × vertexFunctionSpace L n k k) :
    saddleOnVertexFunctions X M x = (X x.1 + m' x.2, M x.1) := by
  haveI := h.1.1
  haveI := h.2.1
  unfold saddleOnVertexFunctions
  rw [dif_pos h]
  refine saddlePointOperatorOfInnerCores_apply _ _ X M m' (fun y x' => ?_) x
  rw [h.1.2.choose_spec, h.2.2.choose_spec, hp]
theorem liftGaugeField_mem_complexEdgeForms {j : ℕ}
    (hq : ∀ b : FullSpace.Edge L k j,
      (b.IsPositivelyOriented → (FullSpace.projEdge L n k j b).IsPositivelyOriented) ∧
      (FullSpace.projEdge L n k j b).opposite = FullSpace.projEdge L n k j b.opposite)
    {B : Edge L n k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n k j) :
    liftGaugeField L n k j B ∈ FullSpace.complexEdgeForms (meshAt L k j) := by
  refine ⟨fun b hb => hB.1 _ ((hq b).1 hb), fun b => ?_⟩
  show B (FullSpace.projEdge L n k j b.opposite) = -B (FullSpace.projEdge L n k j b)
  rw [← (hq b).2]
  exact hB.2 _
theorem eventuallyNearIdentity_and {ι : Type*} {D : Set (ι → ComplexMatrix2)}
    {P Q : (ι → ComplexMatrix2) → Prop}
    (hP : EventuallyNearIdentity D P) (hQ : EventuallyNearIdentity D Q) :
    EventuallyNearIdentity D fun V => P V ∧ Q V :=
  Filter.Eventually.and hP hQ
theorem eventuallyNearIdentity_mono {ι : Type*} {D : Set (ι → ComplexMatrix2)}
    {P Q : (ι → ComplexMatrix2) → Prop}
    (hP : EventuallyNearIdentity D P) (h : ∀ V ∈ D, P V → Q V) : EventuallyNearIdentity D Q :=
  (Filter.Eventually.and hP eventually_mem_nhdsWithin).mono fun V hV => h V hV.2 hV.1
theorem hessian_matrix_descends (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    (hn : 0 < n)
    (hF : BackgroundFactorsDescendClaim)
    (hB : LocalKernels.BracketDescent.AssembledFactorsDescend)
    (hS : SixMatrixBracket.BracketIsBackgroundBilinear)
    (hW : HessianKernelIsAssembledFactors)
    (hO : BackgroundHessianFromFormMatrix)
    (hK : FullSpace.HessianLaplacian.HessianKernelAndLaplacianExist)
    (hSP : DescendsAlgebra (k := k) L n)
    (U : Edge L n k 0 → ComplexMatrix2) (hU : U ∈ smallIterateFields L n k)
    (hUw : liftAtBase U ∈ FullSpace.smallIterateFields L k)
    (J : edgeFormSpace L n k 0) (μ : edgeFormSpace L n k k)
    (hJ : (J : Edge L n k 0 → ComplexMatrix2) ∈ complexEdgeForms L n k 0)
    (hμ : (μ : Edge L n k k → ComplexMatrix2) ∈ complexEdgeForms L n k k)
    (hJw : liftAtBase (J : Edge L n k 0 → ComplexMatrix2) ∈
      FullSpace.complexEdgeForms (meshAt L k 0))
    (hμw : liftAtTop (μ : Edge L n k k → ComplexMatrix2) ∈
      FullSpace.complexEdgeForms (meshAt L k k))
    (hBc : ∀ B : edgeFormSpace L n k 0, (B : Edge L n k 0 → ComplexMatrix2) ∈ complexEdgeForms L n k 0)
    (hq : ∀ B : edgeFormSpace L n k 0,
      backgroundBilinear U (J : Edge L n k 0 → ComplexMatrix2) (μ : Edge L n k k → ComplexMatrix2)
          (B : Edge L n k 0 → ComplexMatrix2) (B : Edge L n k 0 → ComplexMatrix2) =
        (backgroundHessianForm U J μ B : ℂ)) :
    ∃ M, IsPauliMatrixOf L n (edgesAtZero k) (edgesAtZero k) (backgroundHessian U J μ) M ∧
      KernelDescends L n (edgesAtZero k).colourPairs (edgesAtZero k).colourPairs
        (kernelOnIdx L (edgesAtZero k) (edgesAtZero k)
          (FullSpace.hessianKernel (liftAtBase U) (liftAtBase (J : Edge L n k 0 → ComplexMatrix2))
            (liftAtTop (μ : Edge L n k k → ComplexMatrix2)))) M := by
  set Mb := (quotFactors L n k U J μ).assembled with hMb
  have hFd := hF L hL k hk n hn U hU J hJ μ hμ
  obtain ⟨d₁, d₂⟩ := hB L hL k n hn _ _ _ _ _ hFd
  have hY := hW L hL k hk n hn U hU J hJ μ hμ
  have hOp := hO L hL k hk n hn U J μ Mb fun B =>
    (hS L hL k hk n hn U hU J hJ μ hμ B (hBc B) B (hBc B)).trans (hq B)
  refine ⟨(1 / 2 : ℂ) • (Mb + swapKernel Mb), hOp, ?_⟩
  have hX := ((hK L hL k hk _ hUw).1 _ hJw _ hμw).2.2.2.2
  rw [hX]
  set Y := (fullFactors L n k U J μ).assembled
  have he : kernelOnIdx L (edgesAtZero k) (edgesAtZero k)
      (FullSpace.HessianLaplacian.symmHessianKernel
        (liftAtBase U) (liftAtBase (J : Edge L n k 0 → ComplexMatrix2))
        (liftAtTop (μ : Edge L n k k → ComplexMatrix2))) = (1 / 2 : ℂ) • (Y + swapKernel Y) := by
    rw [← hY]
    rfl
  rw [he]
  apply kernelDescends_smul
  obtain ⟨⟨R₁, h₁, l₁⟩, -⟩ := id d₁
  obtain ⟨⟨R₂, h₂, l₂⟩, -⟩ := id d₂
  have hR : 0 ≤ max R₁ R₂ := le_max_of_le_left h₁
  have a₁ := isRLocal_mono L l₁ (le_max_left R₁ R₂)
  have a₂ := isRLocal_mono L l₂ (le_max_right R₁ R₂)
  exact (hSP _ _ _ _ hR _ _ _ _ _ _ a₁ a₂ a₁ d₁ d₂ d₁).2.2.1
theorem descendsAt_of (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (hn : 0 < n)
    [Fintype ((edgesAtZero k).colourPairs.ImageCarrier L n)]
    [Fintype ((edgesAtTop k).colourPairs.ImageCarrier L n)]
    [Fintype ((verticesAtZero k).colourPairs.ImageCarrier L n)]
    [Fintype ((verticesAtTop k).colourPairs.ImageCarrier L n)]
    (rb : CoeffExtraction (CellClass.quotSpace L n (edgesAtZero k)) _
      (CellClass.quotCoeffsOn L n (edgesAtZero k)))
    (rc : CoeffExtraction (CellClass.quotSpace L n (edgesAtTop k)) _
      (CellClass.quotCoeffsOn L n (edgesAtTop k)))
    (rs : CoeffExtraction (CellClass.quotSpace L n (verticesAtZero k)) _
      (CellClass.quotCoeffsOn L n (verticesAtZero k)))
    (rt : CoeffExtraction (CellClass.quotSpace L n (verticesAtTop k)) _
      (CellClass.quotCoeffsOn L n (verticesAtTop k)))
    (hE : LocalKernelFacts (k := k) L) (hSP : DescendsAlgebra (k := k) L n)
    (hT : ThreeKernelsDescend.DescentStatement)
    (U : Edge L n k 0 → ComplexMatrix2) (hU : U ∈ smallIterateFields L n k)
    (hQ : ∃ T : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k k, ∀ B : edgeFormSpace L n k 0,
      (T B : Edge L n k k → ComplexMatrix2) = iterCovariantDeriv L n k U k B)
    (hA : ∃ T : vertexFunctionSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k k,
      ∀ l : vertexFunctionSpace L n k 0,
        (T l : Vertex L n k k → ComplexMatrix2) = iterAdjointCubeAverage L n k U k l)
    (hD : ∃ T : vertexFunctionSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k 0,
      ∀ l : vertexFunctionSpace L n k 0, (T l : Edge L n k 0 → ComplexMatrix2) = covDiff U l)
    (J : edgeFormSpace L n k 0) (μ : edgeFormSpace L n k k)
    (hX : ∃ M, IsPauliMatrixOf L n (edgesAtZero k) (edgesAtZero k) (backgroundHessian U J μ) M ∧
      KernelDescends L n (edgesAtZero k).colourPairs (edgesAtZero k).colourPairs
        (kernelOnIdx L (edgesAtZero k) (edgesAtZero k)
          (FullSpace.hessianKernel (liftAtBase U) (liftAtBase (J : Edge L n k 0 → ComplexMatrix2))
            (liftAtTop (μ : Edge L n k k → ComplexMatrix2)))) M) :
    DescendsAt L n k U J μ := by
  obtain ⟨⟨Mq, aq, dq, dqt⟩, ⟨Ma, aa, da, dat⟩, ⟨Md, ad, dd, ddt⟩⟩ := hT L hL k hk n hn U hU
  have mq : IsPauliMatrixOf L n (edgesAtZero k) (edgesAtTop k)
      (iterCovariantDerivLinear L n k U) Mq := fun f =>
    (congrArg (CellClass.quotCoeffsOn L n (edgesAtTop k)) (linearMapWithValues_apply hQ f)).trans
      (aq ⟨f.1, rb.real_mem_complex f⟩)
  have ma : IsPauliMatrixOf L n (verticesAtZero k) (verticesAtTop k)
      (iterAverageLinear L n k U) Ma := fun f =>
    (congrArg (CellClass.quotCoeffsOn L n (verticesAtTop k)) (linearMapWithValues_apply hA f)).trans
      (aa ⟨f.1, rs.real_mem_complex f⟩)
  have md : IsPauliMatrixOf L n (verticesAtZero k) (edgesAtZero k)
      (covDiffLinear L n k U) Md := fun f =>
    (congrArg (CellClass.quotCoeffsOn L n (edgesAtZero k)) (linearMapWithValues_apply hD f)).trans
      (ad ⟨f.1, rs.real_mem_complex f⟩)
  obtain ⟨Qt, qa, qp, qr⟩ := exists_transpose_of_matrix rb rc (iterCovariantDerivLinear L n k U)
    Mq mq
  obtain ⟨At, ta, tp, tr⟩ := exists_transpose_of_matrix rs rt (iterAverageLinear L n k U) Ma ma
  obtain ⟨Dt, ea, -, dr⟩ := exists_transpose_of_matrix rs rb (covDiffLinear L n k U) Md md
  have qe : iterCovariantDerivTranspose L n k U = Qt := qr
  have te : iterAverageRealTranspose L n k U = At := tr
  have de : covDiffRealTranspose L n k U = Dt := dr
  have ml : IsPauliMatrixOf L n (verticesAtZero k) (verticesAtZero k)
      (covLaplacianLinear L n k U) (compKernel (swapKernel Md) Md) := fun f => by
    have e : ((covLaplacianLinear L n k U f : vertexFunctionSpace L n k 0) :
        Vertex L n k 0 → ComplexMatrix2) = (Dt (covDiffLinear L n k U f)).1 := by
      unfold covLaplacianLinear
      rw [de]
      rfl
    refine (congrArg (CellClass.quotCoeffsOn L n (verticesAtZero k)) e).trans ?_
    rw [applyKernel_compKernel]
    exact (ea _).trans (congrArg _ (md f))
  have ddt' : KernelDescends L n (edgesAtZero k).colourPairs (verticesAtZero k).colourPairs
      (kernelOnIdx L (edgesAtZero k) (verticesAtZero k)
        (swapKernel (FullSpace.covDiffKernel L k 0 (liftAtBase U))))
      (swapKernel Md) := ddt
  have dd' : KernelDescends L n (verticesAtZero k).colourPairs (edgesAtZero k).colourPairs
      (kernelOnIdx L (verticesAtZero k) (edgesAtZero k)
        (FullSpace.covDiffKernel L k 0 (liftAtBase U))) Md := dd
  have dl : KernelDescends L n (verticesAtZero k).colourPairs (verticesAtZero k).colourPairs
      (kernelOnIdx L (verticesAtZero k) (verticesAtZero k)
        (compKernel (swapKernel (FullSpace.covDiffKernel L k 0 (liftAtBase U)))
          (FullSpace.covDiffKernel L k 0 (liftAtBase U))))
      (compKernel (swapKernel Md) Md) := by
    have e := kernelOnIdx_compKernel L (edgesAtZero k) (verticesAtZero k) (verticesAtZero k)
      (swapKernel (FullSpace.covDiffKernel L k 0 (liftAtBase U)))
      (FullSpace.covDiffKernel L k 0 (liftAtBase U))
    obtain ⟨⟨R₁, h₁, l₁⟩, -⟩ := id ddt'
    obtain ⟨⟨R₂, h₂, l₂⟩, -⟩ := id dd'
    have hR : 0 ≤ max R₁ R₂ := le_max_of_le_left h₁
    have a₁ := isRLocal_mono L l₁ (le_max_left R₁ R₂)
    have a₂ := isRLocal_mono L l₂ (le_max_right R₁ R₂)
    exact (congrArg (fun T => KernelDescends L n (verticesAtZero k).colourPairs
      (verticesAtZero k).colourPairs T (compKernel (swapKernel Md) Md)) e).mpr
        (hSP _ _ _ _ hR _ _ _ _ _ _ a₁ a₁ a₂ ddt' ddt' dd').2.2.2.2.1
  have hEb : EdgeFormsEuclidean L n k 0 ∧ EdgeFormsEuclidean L n k k := by
    obtain ⟨f₁, c₁, h₁⟩ := rb.exists_innerCore
    obtain ⟨f₂, c₂, h₂⟩ := rc.exists_innerCore
    exact ⟨⟨f₁, c₁, h₁⟩, ⟨f₂, c₂, h₂⟩⟩
  have hEs : VertexFunctionsEuclidean L n k 0 ∧ VertexFunctionsEuclidean L n k k := by
    obtain ⟨f₁, c₁, h₁⟩ := rs.exists_innerCore
    obtain ⟨f₂, c₂, h₂⟩ := rt.exists_innerCore
    exact ⟨⟨f₁, c₁, h₁⟩, ⟨f₂, c₂, h₂⟩⟩
  obtain ⟨Mx, mx, dx⟩ := hX
  refine ⟨⟨Mx, mx, dx⟩, ⟨Mq, mq, dq⟩, ⟨swapKernel Mq, ?_, dqt⟩,
    ⟨_, ml, dl⟩, ⟨Ma, ma, da⟩, ⟨swapKernel Ma, ?_, dat⟩,
    ⟨saddleBlockMatrix L n (edgesAtZero k) (edgesAtTop k) Mx (swapKernel Mq) Mq,
      saddleBlock_isPauliMatrix _ _ _ ?_ ?_, saddleBlock_descends hE _ _ dx dqt dq⟩,
    ⟨saddleBlockMatrix L n (verticesAtZero k) (verticesAtTop k) _ (swapKernel Ma) Ma,
      saddleBlock_isPauliMatrix _ _ _ ?_ ?_, saddleBlock_descends hE _ _ dl dat da⟩⟩
  · intro g
    rw [qe]
    exact qa g
  · intro g
    rw [te]
    exact ta g
  · intro x
    have e := saddleOnEdgeForms_apply hEb (backgroundHessian U J μ)
      (iterCovariantDerivLinear L n k U) Qt qp x
    exact (congrArg (fun y : edgeFormSpace L n k 0 × edgeFormSpace L n k k =>
      CellClass.quotCoeffsOn L n (edgesAtZero k) y.1.1) e).trans
        ((rb.map_read_add _ _).trans (congrArg₂ (· + ·) (mx x.1) (qa x.2)))
  · intro x
    have e := saddleOnEdgeForms_apply hEb (backgroundHessian U J μ)
      (iterCovariantDerivLinear L n k U) Qt qp x
    exact (congrArg (fun y : edgeFormSpace L n k 0 × edgeFormSpace L n k k =>
      CellClass.quotCoeffsOn L n (edgesAtTop k) y.2.1) e).trans (mq x.1)
  · intro x
    have e := saddleOnVertexFunctions_apply hEs (covLaplacianLinear L n k U)
      (iterAverageLinear L n k U) At tp x
    exact (congrArg (fun y : vertexFunctionSpace L n k 0 × vertexFunctionSpace L n k k =>
      CellClass.quotCoeffsOn L n (verticesAtZero k) y.1.1) e).trans
        ((rs.map_read_add _ _).trans (congrArg₂ (· + ·) (ml x.1) (ta x.2)))
  · intro x
    have e := saddleOnVertexFunctions_apply hEs (covLaplacianLinear L n k U)
      (iterAverageLinear L n k U) At tp x
    exact (congrArg (fun y : vertexFunctionSpace L n k 0 × vertexFunctionSpace L n k k =>
      CellClass.quotCoeffsOn L n (verticesAtTop k) y.2.1) e).trans (ma x.1)
end Maps
theorem blocksDescend_holds
    (hT : ThreeKernelsDescend.DescentStatement)
    (hF : BackgroundFactorsDescendClaim)
    (hB : LocalKernels.BracketDescent.AssembledFactorsDescend)
    (hS : SixMatrixBracket.BracketIsBackgroundBilinear)
    (hW : HessianKernelIsAssembledFactors)
    (hQ : BilinearOnDiagonal.DiagonalIsHessianForm)
    (hO : BackgroundHessianFromFormMatrix)
    (hY : LocalKernels.Periodisation.PeriodisationHolds)
    (hC : AsDifferentials.CovariantMeansAreDerivatives)
    (hR : RealLinearMaps.RealLinearMapsStatement)
    (hK : FullSpace.HessianLaplacian.HessianKernelAndLaplacianExist)
    (hM : EdgeProjectionProperties)
    (hP : PeriodicLattice.LevelBondOrientationDichotomy) : BlocksDescend := by
  intro L hL k hk n hn
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
  obtain ⟨hcells, hclasses, hSP, hE, -, -, -, -, hAv⟩ := hY L hL (i + 1) n hn
  have hAv := hAv hk
  have := (hclasses (edgesAtZero (i + 1)).colourPairs).1
  have := (hclasses (edgesAtTop (i + 1)).colourPairs).1
  have := (hclasses (verticesAtZero (i + 1)).colourPairs).1
  have := (hclasses (verticesAtTop (i + 1)).colourPairs).1
  let _ := Fintype.ofFinite ((edgesAtZero (i + 1)).colourPairs.ImageCarrier L n)
  let _ := Fintype.ofFinite ((edgesAtTop (i + 1)).colourPairs.ImageCarrier L n)
  let _ := Fintype.ofFinite ((verticesAtZero (i + 1)).colourPairs.ImageCarrier L n)
  let _ := Fintype.ofFinite ((verticesAtTop (i + 1)).colourPairs.ImageCarrier L n)
  let rb : CoeffExtraction (CellClass.quotSpace L n (edgesAtZero (i + 1))) _
      (CellClass.quotCoeffsOn L n (edgesAtZero (i + 1))) :=
    edgePauliCoordinates 0 (Nat.zero_le _) ((hcells 0 (Nat.zero_le _)).1 .edge).1
      (hP L n (i + 1) hL hn hk 0 (Nat.zero_le _))
  let rc : CoeffExtraction (CellClass.quotSpace L n (edgesAtTop (i + 1))) _
      (CellClass.quotCoeffsOn L n (edgesAtTop (i + 1))) :=
    edgePauliCoordinates (i + 1) le_rfl ((hcells (i + 1) le_rfl).1 .edge).1
      (hP L n (i + 1) hL hn hk (i + 1) le_rfl)
  let rs : CoeffExtraction (CellClass.quotSpace L n (verticesAtZero (i + 1))) _
      (CellClass.quotCoeffsOn L n (verticesAtZero (i + 1))) :=
    vertexCoordinate 0 (Nat.zero_le _) ((hcells 0 (Nat.zero_le _)).1 .vertex).1
  let rt : CoeffExtraction (CellClass.quotSpace L n (verticesAtTop (i + 1))) _
      (CellClass.quotCoeffsOn L n (verticesAtTop (i + 1))) :=
    vertexCoordinate (i + 1) le_rfl ((hcells (i + 1) le_rfl).1 .vertex).1
  have hq₀ : ∀ b : FullSpace.Edge L (i + 1) 0,
      (b.IsPositivelyOriented → (FullSpace.projEdge L n (i + 1) 0 b).IsPositivelyOriented) ∧
      (FullSpace.projEdge L n (i + 1) 0 b).opposite = FullSpace.projEdge L n (i + 1) 0 b.opposite :=
    fun b => ⟨((hM L n (i + 1) 0 hL hn (Nat.zero_le _)).1 b).2.2.1,
      ((hM L n (i + 1) 0 hL hn (Nat.zero_le _)).1 b).2.2.2⟩
  have hq₁ : ∀ b : FullSpace.Edge L (i + 1) (i + 1),
      (b.IsPositivelyOriented →
        (FullSpace.projEdge L n (i + 1) (i + 1) b).IsPositivelyOriented) ∧
      (FullSpace.projEdge L n (i + 1) (i + 1) b).opposite =
        FullSpace.projEdge L n (i + 1) (i + 1) b.opposite :=
    fun b => ⟨((hM L n (i + 1) (i + 1) hL hn le_rfl).1 b).2.2.1,
      ((hM L n (i + 1) (i + 1) hL hn le_rfl).1 b).2.2.2⟩
  have n₁ := ((hC L hL (i + 1) hk).1 n hn).2.2
  have n₂ := hQ L hL (i + 1) hk n hn
  have hst := (hR L n (i + 1) hL hn hk).1 i (Nat.lt_succ_self i)
  have n₃ := hst.iterCovariantDeriv_isLinear
  have n₄ := hst.iterAdjointCubeAverage_isLinear
  have hDl := (hR L n (i + 1) hL hn hk).2.covDiff_isLinear 0 (Nat.zero_le _)
  refine eventuallyNearIdentity_mono
    (eventuallyNearIdentity_and (eventuallyNearIdentity_and n₁ n₂)
      (eventuallyNearIdentity_and n₃ n₄)) ?_
  rintro U hUc ⟨⟨⟨hU, -⟩, hqf⟩, hQl, hAl⟩
  refine ⟨hU, fun J μ => descendsAt_of hL hk hn rb rc rs rt hE hSP hT U hU hQl hAl (hDl U hUc) J μ ?_⟩
  have hJ := rb.real_mem_complex J
  have hμ := rc.real_mem_complex μ
  exact hessian_matrix_descends hL hk hn hF hB hS hW hO hK hSP U hU ((hAv U hU.1).1.1 hU) J μ hJ hμ
    (liftGaugeField_mem_complexEdgeForms hq₀ hJ) (liftGaugeField_mem_complexEdgeForms hq₁ hμ)
    rb.real_mem_complex (hqf J μ)
end YangMills.Construction.Tower.OperatorBlocksDescend
end
