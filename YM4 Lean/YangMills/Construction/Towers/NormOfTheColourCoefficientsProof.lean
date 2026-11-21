import YangMills.Construction.PeriodicOperators.IndexSetsOfATower
import YangMills.Construction.PeriodicOperators.QuotientsTransposesAndNorm
import YangMills.Construction.Towers.BracketsAndTransposesOnThePairsProof
import YangMills.Construction.Towers.NormOfTheColourCoefficients
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.PauliCoefficientNorm
open Matrices
open Matrices.GroupLieProduct (tracelessFunctions)
open OneLoop (pauliCoordinateEquiv)
open PeriodicOperators (PeriodicData IsPeriodic IsQuotInvariant descendFn descendFn_mkQuot)
theorem pauliCoeff_coe (X : ComplexMatrix2.traceless) (a : Fin 3) :
    pauliCoeff a (X : ComplexMatrix2) = pauliCoordinateEquiv X a := by apply _root_.YangMills.Construction.LocalKernels.PairBrackets.pauliCoeff_coe <;> assumption
theorem coe_eq_sum_pauliCoordinateEquiv (X : ComplexMatrix2.traceless) :
    (X : ComplexMatrix2) = ∑ a, pauliCoordinateEquiv X a • ComplexMatrix2.pauliFamily a := by apply _root_.YangMills.SharedProofs.p15988 <;> assumption
theorem halfTrace_conjTranspose_sum_mul_sum (x x' : Fin 3 → ℂ) :
    ComplexMatrix2.halfTrace (Matrix.conjTranspose (∑ a, x a • ComplexMatrix2.pauliFamily a) *
      (∑ a, x' a • ComplexMatrix2.pauliFamily a)) = ∑ a, conj (x a) * x' a := by
  obtain ⟨h0, h1, h2⟩ := ComplexMatrix2.pauliFamily_apply
  simp only [Fin.sum_univ_three, h0, h1, h2, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace]
  simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  ring_nf
  simp only [Complex.I_sq]
  ring
theorem halfTraceInner_eq_sum (X X' : ComplexMatrix2.traceless) :
    halfTraceInner X X' = ∑ a, conj (pauliCoordinateEquiv X a) * pauliCoordinateEquiv X' a := by
  unfold halfTraceInner
  conv_lhs => rw [coe_eq_sum_pauliCoordinateEquiv X, coe_eq_sum_pauliCoordinateEquiv X']
  exact halfTrace_conjTranspose_sum_mul_sum (pauliCoordinateEquiv X) (pauliCoordinateEquiv X')
theorem halfTraceInner_self (X : ComplexMatrix2.traceless) :
    halfTraceInner X X = ((∑ a, ‖pauliCoordinateEquiv X a‖ ^ 2 : ℝ) : ℂ) := by
  rw [halfTraceInner_eq_sum]
  push_cast
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [RCLike.conj_mul]
  simp
theorem pauliNorm_coe (X : ComplexMatrix2.traceless) :
    pauliNorm (X : ComplexMatrix2) = Real.sqrt (∑ a, ‖pauliCoordinateEquiv X a‖ ^ 2) := by
  unfold pauliNorm
  simp only [pauliCoeff_coe]
theorem pauliNorm_sq (X : ComplexMatrix2) : pauliNorm X ^ 2 = ∑ a, ‖pauliCoeff a X‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)
theorem pauliNorm_nonneg (X : ComplexMatrix2) : 0 ≤ pauliNorm X := Real.sqrt_nonneg _
theorem two_mul_pauliNorm_sq (X : ComplexMatrix2.traceless) :
    2 * pauliNorm (X : ComplexMatrix2) ^ 2 = ∑ i, ∑ j, ‖(X : ComplexMatrix2) i j‖ ^ 2 := by
  have h : ((pauliNorm (X : ComplexMatrix2) ^ 2 : ℝ) : ℂ) = halfTraceInner X X := by
    rw [halfTraceInner_self, pauliNorm_sq]
    simp only [pauliCoeff_coe]
  have h' : halfTraceInner X X =
      ((((1 / 2 : ℝ) * ∑ i, ∑ j, ‖(X : ComplexMatrix2) i j‖ ^ 2 : ℝ)) : ℂ) := by
    unfold halfTraceInner
    simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, RCLike.star_def,
      RCLike.conj_mul]
    push_cast
    simp only [Complex.coe_algebraMap]
    ring
  have h'' := Complex.ofReal_injective (h.trans h')
  linarith
theorem halfTraceInnerIsCoordInner_holds (hP : OneLoop.PauliMatrixRelations) :
    HalfTraceInnerIsCoordInner := by
  obtain ⟨-, -, -, -, hpair, -⟩ := hP
  have hbasis : ∀ a, pauliCoordinateEquiv (OneLoop.pauliBasis a) = Pi.single a 1 := by
    intro a
    simp [OneLoop.pauliBasis]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro X X' x x' hX hX'
    unfold halfTraceInner
    rw [hX, hX']
    exact halfTrace_conjTranspose_sum_mul_sum x x'
  · intro X
    rw [pauliNorm_coe, halfTraceInner_self, Complex.ofReal_re]
  · refine ⟨{ inner := halfTraceInner
              conj_inner_symm := ?_
              re_inner_nonneg := ?_
              add_left := ?_
              smul_left := ?_
              definite := ?_ }, fun _ _ => rfl⟩
    · intro X Y
      simp only [halfTraceInner_eq_sum, map_sum, map_mul, Complex.conj_conj]
      exact Finset.sum_congr rfl fun a _ => mul_comm _ _
    · intro X
      rw [halfTraceInner_self]
      simp only [RCLike.re_to_complex, Complex.ofReal_re]
      exact Finset.sum_nonneg fun _ _ => by positivity
    · intro X Y Z
      simp only [halfTraceInner_eq_sum, map_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    · intro X Y r
      simp only [halfTraceInner_eq_sum, map_smul, Pi.smul_apply, smul_eq_mul, map_mul,
        Finset.mul_sum, mul_assoc]
    · intro X hX
      rw [halfTraceInner_self] at hX
      have h0 : ∑ a, ‖pauliCoordinateEquiv X a‖ ^ 2 = 0 := by exact_mod_cast hX
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun a _ => by positivity).1 h0
      have h2 : pauliCoordinateEquiv X = 0 := by
        funext a
        simpa using h1 a (Finset.mem_univ a)
      exact pauliCoordinateEquiv.map_eq_zero_iff.1 h2
  · intro a b
    rw [halfTraceInner_eq_sum]
    simp only [hbasis]
    fin_cases a <;> fin_cases b <;> simp [Fin.sum_univ_three]
  · intro X X'
    rw [hpair X X' _ _ (coe_eq_sum_pauliCoordinateEquiv X) (coe_eq_sum_pauliCoordinateEquiv X'),
      pauliNorm_coe, pauliNorm_coe]
    calc ‖∑ a, pauliCoordinateEquiv X a * pauliCoordinateEquiv X' a‖
        ≤ ∑ a, ‖pauliCoordinateEquiv X a‖ * ‖pauliCoordinateEquiv X' a‖ := by
          refine (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun a _ => norm_mul _ _)
      _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
theorem sum_sq_column_le_opNorm_sq (X : ComplexMatrix2) (j : Fin 2) :
    ∑ i, ‖X i j‖ ^ 2 ≤ ‖X‖ ^ 2 := by
  have h := Matrix.l2_opNorm_mulVec X (EuclideanSpace.single j (1 : ℂ))
  have h1 : ‖(EuclideanSpace.single j (1 : ℂ) : EuclideanSpace ℂ (Fin 2))‖ = 1 := by simp
  rw [h1, mul_one] at h
  have h2 : ‖(EuclideanSpace.equiv (Fin 2) ℂ).symm
      (X.mulVec (EuclideanSpace.single j (1 : ℂ)))‖ ^ 2 = ∑ i, ‖X i j‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  rw [← h2]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2
theorem opNorm_sq_le_sum_sq_entries (X : ComplexMatrix2) : ‖X‖ ^ 2 ≤ ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
  have hS : 0 ≤ ∑ i, ∑ j, ‖X i j‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  have hb : ‖X‖ ≤ Real.sqrt (∑ i, ∑ j, ‖X i j‖ ^ 2) := by
    rw [Matrix.l2_opNorm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
    change ‖(EuclideanSpace.equiv (Fin 2) ℂ).symm (X.mulVec x)‖ ≤ _
    have hrow : ∀ i, ‖X.mulVec x i‖ ^ 2 ≤ (∑ j, ‖X i j‖ ^ 2) * ‖x‖ ^ 2 := by
      intro i
      have h1 : ‖X.mulVec x i‖ ≤ ∑ j, ‖X i j‖ * ‖x j‖ := by
        simp only [Matrix.mulVec, dotProduct]
        refine (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun j _ => norm_mul _ _)
      calc ‖X.mulVec x i‖ ^ 2 ≤ (∑ j, ‖X i j‖ * ‖x j‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ ≤ (∑ j, ‖X i j‖ ^ 2) * ∑ j, ‖x j‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
        _ = _ := by rw [EuclideanSpace.norm_sq_eq]
    have hsq : ‖(EuclideanSpace.equiv (Fin 2) ℂ).symm (X.mulVec x)‖ ^ 2 ≤
        (∑ i, ∑ j, ‖X i j‖ ^ 2) * ‖x‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Finset.sum_mul]
      exact Finset.sum_le_sum fun i _ => hrow i
    calc ‖(EuclideanSpace.equiv (Fin 2) ℂ).symm (X.mulVec x)‖
        = Real.sqrt (‖(EuclideanSpace.equiv (Fin 2) ℂ).symm (X.mulVec x)‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt ((∑ i, ∑ j, ‖X i j‖ ^ 2) * ‖x‖ ^ 2) := Real.sqrt_le_sqrt hsq
      _ = _ := by rw [Real.sqrt_mul hS, Real.sqrt_sq (norm_nonneg _)]
  calc ‖X‖ ^ 2 ≤ Real.sqrt (∑ i, ∑ j, ‖X i j‖ ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    _ = _ := Real.sq_sqrt hS
theorem pauliNorm_smul (z : ℂ) (X : ComplexMatrix2.traceless) :
    pauliNorm (z • (X : ComplexMatrix2)) = ‖z‖ * pauliNorm (X : ComplexMatrix2) := by
  have h : z • (X : ComplexMatrix2) = ((z • X : ComplexMatrix2.traceless) : ComplexMatrix2) := rfl
  rw [h, pauliNorm_coe, pauliNorm_coe]
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
theorem operatorNormComparison_holds (hP : OneLoop.PauliMatrixRelations) :
    OperatorNormComparison := by
  obtain ⟨-, -, -, -, -, -, -, hnorm, -⟩ := hP
  refine ⟨fun X => ⟨?_, ?_⟩, fun z X hX => ?_⟩
  · have h := two_mul_pauliNorm_sq X
    have h0 := sum_sq_column_le_opNorm_sq (X : ComplexMatrix2) 0
    have h1 := sum_sq_column_le_opNorm_sq (X : ComplexMatrix2) 1
    rw [Finset.sum_comm, Fin.sum_univ_two] at h
    refine (pow_le_pow_iff_left₀ (pauliNorm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
    linarith
  · have h := two_mul_pauliNorm_sq X
    have h0 := opNorm_sq_le_sum_sq_entries (X : ComplexMatrix2)
    have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    refine (pow_le_pow_iff_left₀ (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (pauliNorm_nonneg _)) two_ne_zero).1 ?_
    rw [mul_pow, hs]
    exact h0.trans h.ge
  · have hX' : X = X.conjTranspose ∧ ComplexMatrix2.fullTrace X = 0 := hX
    have hsl : X ∈ ComplexMatrix2.traceless := hX'.2
    have hc : pauliNorm X = ComplexMatrix2.operatorNorm X := by
      have h1 := hnorm ⟨X, hsl⟩ hX
      have h2 : ((pauliNorm X ^ 2 : ℝ) : ℂ) = halfTraceInner ⟨X, hsl⟩ ⟨X, hsl⟩ := by
        rw [halfTraceInner_self, pauliNorm_sq]
        simp only [← pauliCoeff_coe]
      have h3 : halfTraceInner ⟨X, hsl⟩ ⟨X, hsl⟩ = OneLoop.traceForm ⟨X, hsl⟩ ⟨X, hsl⟩ := by
        unfold halfTraceInner OneLoop.traceForm
        simp only
        rw [← hX'.1]
      have h4 : pauliNorm X ^ 2 = ComplexMatrix2.operatorNorm X ^ 2 :=
        Complex.ofReal_injective (h2.trans (h3.trans h1.symm))
      exact (pow_left_inj₀ (pauliNorm_nonneg _) (norm_nonneg _) two_ne_zero).1 h4
    have hs := pauliNorm_smul z ⟨X, hsl⟩
    simp only at hs
    refine ⟨?_, by rw [hs, hc]⟩
    rw [hs, hc]
    exact norm_smul z X
section Places
variable {σ : Type}
theorem pauliNorm_sq_apply (f : σ → ComplexMatrix2) (x : σ) :
    pauliNorm (f x) ^ 2 = ∑ a, ‖toPauliCoeffs f (a, x)‖ ^ 2 :=
  pauliNorm_sq (f x)
theorem pointwisePairing_eq_sum (hP : OneLoop.PauliMatrixRelations) {f f' : σ → ComplexMatrix2}
    (hf : f ∈ tracelessFunctions σ) (hf' : f' ∈ tracelessFunctions σ) (x : σ) :
    pointwisePairing hf hf' x = ∑ a, toPauliCoeffs f (a, x) * toPauliCoeffs f' (a, x) := by
  obtain ⟨-, -, -, -, hpair, -⟩ := hP
  unfold pointwisePairing
  rw [hpair _ _ _ _ (coe_eq_sum_pauliCoordinateEquiv _) (coe_eq_sum_pauliCoordinateEquiv _)]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [toPauliCoeffs]
  rw [← pauliCoeff_coe, ← pauliCoeff_coe]
theorem meshNorm_sq (a : ℝ) (f : σ → ComplexMatrix2) :
    meshNorm a f ^ 2 = ∑' ι, a ^ 4 * ‖toPauliCoeffs f ι‖ ^ 2 := by
  unfold meshNorm PeriodicOperators.wNorm
  exact Real.sq_sqrt (tsum_nonneg fun ι => mul_nonneg (by simp only [meshWeight]; positivity)
    (by positivity))
theorem meshPairing_eq_tsum (a : ℝ) (f f' : σ → ComplexMatrix2) :
    meshPairing a f f' =
      ∑' ι, ((a ^ 4 : ℝ) : ℂ) * (toPauliCoeffs f ι * toPauliCoeffs f' ι) :=
  rfl
theorem finiteLatticeFormulas_holds (hP : OneLoop.PauliMatrixRelations) (a : ℝ) [Finite σ] :
    FiniteLatticeFormulas a σ := by
  intro f f' hf hf'
  have := Fintype.ofFinite σ
  constructor
  · rw [meshNorm_sq, tsum_fintype, Fintype.sum_prod_type_right, finsum_eq_sum_of_fintype,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [pauliNorm_sq_apply, Finset.mul_sum]
  · rw [meshPairing_eq_tsum, tsum_fintype, Fintype.sum_prod_type_right, finsum_eq_sum_of_fintype,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [pointwisePairing_eq_sum hP, Finset.mul_sum]
theorem summable_fin_three_prod_iff {g : Fin 3 × σ → ℝ} (hg : ∀ ι, 0 ≤ g ι) :
    Summable g ↔ Summable fun x => ∑ a, g (a, x) := by
  rw [← (Equiv.prodComm σ (Fin 3)).summable_iff,
    summable_prod_of_nonneg (f := g ∘ Equiv.prodComm σ (Fin 3)) (fun ι => hg _)]
  simp only [Function.comp_apply, Equiv.prodComm_apply, Prod.swap_prod_mk, tsum_fintype]
  exact ⟨fun h => h.2, fun h => ⟨fun _ => Summable.of_finite, h⟩⟩
theorem tsum_fin_three_prod {E : Type} [NormedAddCommGroup E] [CompleteSpace E]
    {g : Fin 3 × σ → E} (hg : Summable g) : ∑' ι, g ι = ∑' x, ∑ a, g (a, x) := by
  have h := (Equiv.prodComm σ (Fin 3)).summable_iff.2 hg
  calc ∑' ι, g ι = ∑' c, (g ∘ Equiv.prodComm σ (Fin 3)) c :=
        ((Equiv.prodComm σ (Fin 3)).tsum_eq g).symm
    _ = ∑' x, ∑' b, (g ∘ Equiv.prodComm σ (Fin 3)) (x, b) := h.tsum_prod
    _ = _ := by
      simp only [Function.comp_apply, Equiv.prodComm_apply, Prod.swap_prod_mk, tsum_fintype]
theorem infiniteLatticeFormulas_holds (hP : OneLoop.PauliMatrixRelations) (a : ℝ) :
    InfiniteLatticeFormulas a σ := by
  intro f f' hf hf'
  have hiff : (Summable fun ι : Fin 3 × σ => ‖toPauliCoeffs f ι‖ ^ 2) ↔
      Summable fun x => pauliNorm (f x) ^ 2 := by
    rw [summable_fin_three_prod_iff fun ι => by positivity]
    simp only [pauliNorm_sq_apply]
  refine ⟨hiff, fun hs => ?_, fun hs => ?_⟩
  · rw [meshNorm_sq, tsum_mul_left, tsum_fin_three_prod hs]
    simp only [pauliNorm_sq_apply]
  · have hgroups : Summable fun x => ∑ a, ‖toPauliCoeffs f (a, x) * toPauliCoeffs f' (a, x)‖ :=
      (summable_fin_three_prod_iff (g := fun ι => ‖toPauliCoeffs f ι * toPauliCoeffs f' ι‖)
        fun ι => norm_nonneg _).1 hs
    have hnorm : Summable fun x => ‖pointwisePairing hf hf' x‖ := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => ?_) hgroups
      rw [pointwisePairing_eq_sum hP]
      exact norm_sum_le _ _
    refine ⟨hnorm, ?_⟩
    have hsum : Summable fun ι : Fin 3 × σ => toPauliCoeffs f ι * toPauliCoeffs f' ι :=
      Summable.of_norm hs
    rw [meshPairing_eq_tsum, tsum_mul_left, tsum_fin_three_prod (E := ℂ) hsum]
    simp only [pointwisePairing_eq_sum hP]
end Places
section Periodic
variable {σ : Type}
abbrev colourOrbitData (a : ℝ) (act : (Fin 4 → ℤ) → σ → σ)
    (position : Fin 3 × σ → InfiniteLattice.AmbientSpace) : PeriodicData :=
  PeriodicData.ofSingle (Fin 3 × σ) (fun m ι => (ι.1, act m ι.2)) position (a ^ 4)
def unitQuotEquiv (a : ℝ) (act : (Fin 4 → ℤ) → σ → σ)
    (position : Fin 3 × σ → InfiniteLattice.AmbientSpace) :
    (colourOrbitData a act position).UnitQuot ≃ Fin 3 × OrbitSpace act where
  toFun := Quot.lift (fun ι => (ι.1, Quot.mk _ ι.2)) (by
    rintro ι _ ⟨m, rfl⟩
    exact Prod.ext rfl (Quot.sound ⟨1 • m, rfl⟩))
  invFun p := Quot.lift (fun x => (colourOrbitData a act position).mkQuot 1 (p.1, x)) (by
    rintro x _ ⟨m, rfl⟩
    refine Quot.sound ⟨m, ?_⟩
    rw [one_smul]
    rfl) p.2
  left_inv c := by
    induction c using Quot.ind
    rfl
  right_inv p := by
    obtain ⟨a, c⟩ := p
    induction c using Quot.ind
    rfl
variable {a : ℝ} {act : (Fin 4 → ℤ) → σ → σ}
  {position : Fin 3 × σ → InfiniteLattice.AmbientSpace}
theorem unitQuotEquiv_symm_apply (b : Fin 3) (c : OrbitSpace act) :
    (unitQuotEquiv a act position).symm (b, c) =
      (colourOrbitData a act position).mkQuot 1 (b, Quot.out c) := by
  conv_lhs => rw [← Quot.out_eq c]
  rfl
theorem isQuotInvariant_toPauliCoeffs {f : σ → ComplexMatrix2} (hf : IsTranslationPeriodic act f) :
    IsQuotInvariant (colourOrbitData a act position) (toPauliCoeffs f) := by
  intro ι ι' h
  have key : ∀ u v : Fin 3 × σ,
      (∃ m : Fin 4 → ℤ, v = (colourOrbitData a act position).translate (1 • m) u) →
        toPauliCoeffs f u = toPauliCoeffs f v := by
    rintro u _ ⟨m, rfl⟩
    simp only [toPauliCoeffs]
    change pauliCoeff u.1 (f u.2) = pauliCoeff u.1 (f (act (1 • m) u.2))
    rw [hf]
  exact congrArg (Quot.lift (toPauliCoeffs f) key) h
theorem descendFn_unitQuotEquiv_symm {f : σ → ComplexMatrix2} (hf : IsTranslationPeriodic act f)
    (b : Fin 3) (c : OrbitSpace act) :
    descendFn (colourOrbitData a act position) (toPauliCoeffs f)
        ((unitQuotEquiv a act position).symm (b, c)) = toPauliCoeffs f (b, Quot.out c) := by
  rw [unitQuotEquiv_symm_apply]
  exact descendFn_mkQuot (isQuotInvariant_toPauliCoeffs hf) _
theorem finsum_unitQuot [Finite (colourOrbitData a act position).UnitQuot]
    [Finite (OrbitSpace act)] {M : Type} [AddCommMonoid M]
    (F : (colourOrbitData a act position).UnitQuot → M) :
    ∑ᶠ c, F c = ∑ᶠ p : OrbitSpace act, ∑ b, F ((unitQuotEquiv a act position).symm (b, p)) := by
  have := Fintype.ofFinite (colourOrbitData a act position).UnitQuot
  have := Fintype.ofFinite (OrbitSpace act)
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
    ← Equiv.sum_comp (unitQuotEquiv a act position).symm F, Fintype.sum_prod_type_right]
theorem periodicFormulas_holds (hP : OneLoop.PauliMatrixRelations)
    (hJ : PeriodicOperators.Quotients.QuotientTransposeNorm)
    (hI : IsPeriodic (colourOrbitData a act position)) :
    PeriodicFormulas a act (colourOrbitData a act position) toPauliCoeffs := by
  intro f f' hf hf' pf pf'
  obtain ⟨hfin, hcl, -⟩ := hJ _ _ hI hI 1 one_pos
  obtain ⟨hw, hs⟩ := hcl 1 (Or.inl rfl)
  have hweight : ∀ c, (colourOrbitData a act position).quotWeight 1 c = a ^ 4 :=
    Quot.ind fun ι => hw.2 ι
  have : Finite (colourOrbitData a act position).UnitQuot := hfin.1
  have : Finite (Fin 3 × OrbitSpace act) := Finite.of_equiv _ (unitQuotEquiv a act position)
  have : Finite (OrbitSpace act) :=
    Finite.of_surjective (Prod.snd : Fin 3 × OrbitSpace act → _) fun p => ⟨(0, p), rfl⟩
  have := Fintype.ofFinite (OrbitSpace act)
  obtain ⟨-, -, hpair, hnorm⟩ := hs
    (descendFn (colourOrbitData a act position) (toPauliCoeffs f))
    (descendFn (colourOrbitData a act position) (toPauliCoeffs f'))
  constructor
  · rw [hnorm, Real.sq_sqrt (finsum_nonneg fun c => mul_nonneg (by rw [hweight]; positivity)
      (by positivity)), finsum_unitQuot, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [pauliNorm_sq_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hweight, descendFn_unitQuotEquiv_symm pf]
  · rw [hpair, finsum_unitQuot, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [pointwisePairing_eq_sum hP, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hweight, descendFn_unitQuotEquiv_symm pf, descendFn_unitQuotEquiv_symm pf']
end Periodic
theorem finite_vertex {L : ℕ} (hL : 0 < L) (n k j : ℕ) : Finite (Vertex L n k j) :=
  SeparatedSequences.BaseParameters.site_finite hL _ _
theorem finite_positiveEdge {L : ℕ} (hL : 0 < L) (n k j : ℕ) :
    Finite (PositiveEdge L n k j) := by
  have := finite_vertex hL n k j
  exact Finite.of_injective (fun b : PositiveEdge L n k j => (b.1.source, b.1.target))
    fun b b' h =>
      Subtype.ext (PeriodicLattice.Bond.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
theorem finite_face {L : ℕ} (hL : 0 < L) (n k j : ℕ) : Finite (Face L n k j) := by
  have := finite_vertex hL n k j
  exact Finite.of_injective (fun p : Face L n k j => (p.origin, p.firstAxis, p.secondAxis))
    fun p q h => by
      simp only [Prod.mk.injEq] at h
      exact PeriodicLattice.Plaquette.ext h.1 h.2.1 h.2.2
theorem claim_holds (hT : PeriodicOperators.TowerIndexSets.Claim)
    (hJ : PeriodicOperators.Quotients.QuotientTransposeNorm)
    (hP : OneLoop.PauliMatrixRelations) : Claim := by
  refine ⟨halfTraceInnerIsCoordInner_holds hP, operatorNormComparison_holds hP, ?_⟩
  intro L hL k _ j hj
  have hpos : 0 < L := by
    have := hL.2
    omega
  obtain ⟨hs, hb, hp⟩ := hT L hL k j hj
  refine ⟨fun n _ => ?_, infiniteLatticeFormulas_holds hP _, infiniteLatticeFormulas_holds hP _,
    infiniteLatticeFormulas_holds hP _, ?_, ?_, ?_⟩
  · have := finite_vertex hpos n k j
    have := finite_positiveEdge hpos n k j
    have := finite_face hpos n k j
    exact ⟨finiteLatticeFormulas_holds hP _, finiteLatticeFormulas_holds hP _,
      finiteLatticeFormulas_holds hP _⟩
  · exact periodicFormulas_holds (a := meshAt L k j)
      (act := fun m x => FullSpace.vertexImage (PeriodicOperators.intShift m) x)
      (position := fun ι => ι.2) hP hJ hs
  · exact periodicFormulas_holds (a := meshAt L k j)
      (act := PeriodicOperators.shiftEdge) (position := fun ι => ι.2.1.initial) hP hJ hb
  · exact periodicFormulas_holds (a := meshAt L k j)
      (act := PeriodicOperators.shiftFace) (position := fun ι => ι.2.corner) hP hJ hp
end YangMills.Construction.Tower.PauliCoefficientNorm
end
