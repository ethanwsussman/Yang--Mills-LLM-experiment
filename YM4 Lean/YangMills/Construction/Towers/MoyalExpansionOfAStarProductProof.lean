import YangMills.Construction.FormsOnATorus.ColumnOfTheLimitFormProof
import YangMills.Construction.Towers.BracketsOfTwoSymbolsAsSeries
import YangMills.Construction.Towers.HolomorphicSymbolsAndTheCalculusAtFluxZeroProof
import YangMills.Construction.Towers.MoyalExpansionOfAStarProduct
import YangMills.Construction.Towers.StarProductOfTwoSymbols
import Mathlib
set_option autoImplicit false
open YangMills.Construction.Matrices.RectangularMatrix (opNormValue)
open YangMills.Construction.TorusMetric (euclidNormVec)
open YangMills.Construction.PeriodicOperators (castVec)
noncomputable section
namespace YangMills.Construction.Tower.MoyalRemainderProof
open YangMills.Construction.Tower.MagneticWeyl
def expCubicRemainder (x : ℝ) : ℂ :=
  Complex.exp (Complex.I * (x : ℂ)) - 1 - Complex.I * (x : ℂ) + (x : ℂ) ^ 2 / 2
theorem hasDerivAt_I_mul_ofReal (x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.I * (y : ℂ)) Complex.I x := by
  simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul Complex.I
theorem hasDerivAt_exp_I_mul_ofReal (x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (Complex.I * (y : ℂ)))
      (Complex.I * Complex.exp (Complex.I * (x : ℂ))) x := by
  convert (hasDerivAt_I_mul_ofReal x).cexp using 1
  ring
theorem hasDerivAt_expQuadraticRemainder (x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (Complex.I * (y : ℂ)) - 1 - Complex.I * (y : ℂ))
      (Complex.I * (Complex.exp (Complex.I * (x : ℂ)) - 1)) x := by
  exact (((hasDerivAt_exp_I_mul_ofReal x).sub_const 1).sub (hasDerivAt_I_mul_ofReal x)).congr_deriv
    (by ring)
theorem hasDerivAt_expCubicRemainder (x : ℝ) :
    HasDerivAt expCubicRemainder
      (Complex.I * (Complex.exp (Complex.I * (x : ℂ)) - 1 - Complex.I * (x : ℂ))) x := by
  have hid : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x :=
    (Complex.ofRealCLM.hasDerivAt (x := x)).congr_deriv (by simp)
  have hsq : HasDerivAt (fun y : ℝ => (y : ℂ) ^ 2 / 2) (x : ℂ) x :=
    ((hid.fun_pow 2).div_const 2).congr_deriv (by norm_num)
  have hII : Complex.I * Complex.I = -1 := Complex.I_mul_I
  exact ((hasDerivAt_expQuadraticRemainder x).add hsq).congr_deriv
    (by linear_combination (x : ℂ) * hII)
theorem hasDerivAt_sq_div_two (x : ℝ) : HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
  exact (((hasDerivAt_id' x).fun_pow 2).div_const 2).congr_deriv (by norm_num)
theorem hasDerivAt_cube_div_six (x : ℝ) : HasDerivAt (fun y : ℝ => y ^ 3 / 6) (x ^ 2 / 2) x := by
  exact (((hasDerivAt_id' x).fun_pow 3).div_const 6).congr_deriv (by norm_num; ring)
theorem norm_expQuadraticRemainder_le_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    ‖Complex.exp (Complex.I * (x : ℂ)) - 1 - Complex.I * (x : ℂ)‖ ≤ x ^ 2 / 2 := by
  refine image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := x)
    (f := fun y : ℝ => Complex.exp (Complex.I * (y : ℂ)) - 1 - Complex.I * (y : ℂ))
    (f' := fun y => Complex.I * (Complex.exp (Complex.I * (y : ℂ)) - 1))
    (B := fun y => y ^ 2 / 2) (B' := fun y => y)
    (fun y _ => (hasDerivAt_expQuadraticRemainder y).continuousAt.continuousWithinAt)
    (fun y _ => (hasDerivAt_expQuadraticRemainder y).hasDerivWithinAt) (by simp)
    hasDerivAt_sq_div_two (fun y hy => ?_) ⟨hx, le_rfl⟩
  rw [norm_mul, Complex.norm_I, one_mul]
  calc _ ≤ ‖y‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = y := Real.norm_of_nonneg hy.1
theorem norm_expCubicRemainder_le_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    ‖expCubicRemainder x‖ ≤ x ^ 3 / 6 := by
  refine image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := x)
    (f := expCubicRemainder)
    (f' := fun y => Complex.I * (Complex.exp (Complex.I * (y : ℂ)) - 1 - Complex.I * (y : ℂ)))
    (B := fun y => y ^ 3 / 6) (B' := fun y => y ^ 2 / 2)
    (fun y _ => (hasDerivAt_expCubicRemainder y).continuousAt.continuousWithinAt)
    (fun y _ => (hasDerivAt_expCubicRemainder y).hasDerivWithinAt) (by simp [expCubicRemainder])
    hasDerivAt_cube_div_six (fun y hy => ?_) ⟨hx, le_rfl⟩
  rw [norm_mul, Complex.norm_I, one_mul]
  exact norm_expQuadraticRemainder_le_of_nonneg hy.1
theorem expCubicRemainder_neg (x : ℝ) :
    expCubicRemainder (-x) = (starRingEnd ℂ) (expCubicRemainder x) := by
  have hconj : (starRingEnd ℂ) (Complex.exp (Complex.I * (x : ℂ))) =
      Complex.exp (Complex.I * ((-x : ℝ) : ℂ)) := by
    rw [← Complex.exp_conj]
    simp
  simp only [expCubicRemainder, map_add, map_sub, map_mul, map_one, map_div₀, map_pow, hconj,
    Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg, map_ofNat]
  ring
theorem norm_expCubicRemainder_le (x : ℝ) : ‖expCubicRemainder x‖ ≤ |x| ^ 3 / 6 := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    exact norm_expCubicRemainder_le_of_nonneg hx
  · have h := norm_expCubicRemainder_le_of_nonneg (neg_nonneg.mpr hx)
    rw [expCubicRemainder_neg, RCLike.norm_conj] at h
    rwa [abs_of_nonpos hx]
section OperatorNorm
variable {M K L : ℕ} [NeZero M] [NeZero K] [NeZero L]
theorem opNormValue_nonneg (X : Matrix (Fin M) (Fin K) ℂ) : 0 ≤ opNormValue X := by apply _root_.YangMills.Construction.Tower.MagneticWeyl.FluxZeroCalculus.opNormValue_nonneg <;> assumption
theorem opNormValue_mul_le (X : Matrix (Fin M) (Fin K) ℂ) (Y : Matrix (Fin K) (Fin L) ℂ) :
    opNormValue (X * Y) ≤ opNormValue X * opNormValue Y := by
  open scoped Matrix.Norms.L2Operator in
  exact Matrix.l2_opNorm_mul X Y
theorem opNormValue_smul (c : ℂ) (X : Matrix (Fin M) (Fin K) ℂ) :
    opNormValue (c • X) = ‖c‖ * opNormValue X := by apply _root_.YangMills.Construction.Tower.MagneticWeyl.FluxZeroCalculus.opNormValue_smul <;> assumption
theorem summable_of_opNormValue_le {ι : Type*} {f : ι → Matrix (Fin M) (Fin K) ℂ} {g : ι → ℝ}
    (hg : Summable g) (h : ∀ i, opNormValue (f i) ≤ g i) : Summable f := by
  open scoped Matrix.Norms.L2Operator in
  (have : CompleteSpace (Matrix (Fin M) (Fin K) ℂ) := FiniteDimensional.complete ℂ _
   exact Summable.of_norm_bounded hg h)
theorem opNormValue_tsum_le {ι : Type*} {f : ι → Matrix (Fin M) (Fin K) ℂ}
    (h : Summable fun i => opNormValue (f i)) :
    opNormValue (∑' i, f i) ≤ ∑' i, opNormValue (f i) := by
  open scoped Matrix.Norms.L2Operator in
  (have hs : Summable fun i => ‖f i‖ := h
   have hle := norm_tsum_le_tsum_norm hs
   exact hle)
end OperatorNorm
abbrev Lattice4 := Fin 4 → ℤ
abbrev SumFiber (n : Lattice4) := {p : Lattice4 × Lattice4 // p.1 + p.2 = n}
abbrev latticeWeight (n : Lattice4) : ℝ := 1 + euclidNormVec (castVec n)
theorem euclidNormVec_castVec_nonneg (n : Lattice4) : 0 ≤ euclidNormVec (castVec n) :=
  Real.sqrt_nonneg _
theorem one_le_latticeWeight (n : Lattice4) : 1 ≤ latticeWeight n := by apply _root_.YangMills.DeltaSharedProofs.p500919 <;> assumption
theorem abs_symplecticForm_le (n n' : Lattice4) :
    |(symplecticForm n n' : ℝ)| ≤ euclidNormVec (castVec n) * euclidNormVec (castVec n') := by
  have hsum : ∀ m : Lattice4, ∑ μ, castVec m μ ^ 2 =
      (m 0 : ℝ) ^ 2 + (m 1 : ℝ) ^ 2 + (m 2 : ℝ) ^ 2 + (m 3 : ℝ) ^ 2 := fun m => by
    simp [castVec, Fin.sum_univ_four]
  have hnn : ∀ m : Lattice4, 0 ≤ ∑ μ, castVec m μ ^ 2 := fun m =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  unfold euclidNormVec
  rw [← Real.sqrt_mul (hnn n)]
  apply Real.abs_le_sqrt
  rw [hsum, hsum]
  have hform : (symplecticForm n n' : ℝ) = (n 0 : ℝ) * (n' 1 : ℝ) - (n 1 : ℝ) * (n' 0 : ℝ) := by
    simp [symplecticForm]
  rw [hform]
  have h1 : 0 ≤ ((n 0 : ℝ) ^ 2 + (n 1 : ℝ) ^ 2) * ((n' 2 : ℝ) ^ 2 + (n' 3 : ℝ) ^ 2) := by positivity
  have h2 : 0 ≤ ((n 2 : ℝ) ^ 2 + (n 3 : ℝ) ^ 2) *
      ((n' 0 : ℝ) ^ 2 + (n' 1 : ℝ) ^ 2 + (n' 2 : ℝ) ^ 2 + (n' 3 : ℝ) ^ 2) := by positivity
  nlinarith [sq_nonneg ((n 0 : ℝ) * (n' 0 : ℝ) + (n 1 : ℝ) * (n' 1 : ℝ))]
theorem abs_symplecticForm_le_latticeWeight (p : Lattice4 × Lattice4) :
    |(symplecticForm p.1 p.2 : ℝ)| ≤ latticeWeight p.1 * latticeWeight p.2 := by
  refine (abs_symplecticForm_le p.1 p.2).trans ?_
  have h1 := euclidNormVec_castVec_nonneg p.1
  have h2 := euclidNormVec_castVec_nonneg p.2
  exact mul_le_mul (by simp) (by simp) h2 (by linarith)
theorem one_le_latticeWeight_mul (p : Lattice4 × Lattice4) :
    1 ≤ latticeWeight p.1 * latticeWeight p.2 :=
  one_le_mul_of_one_le_of_one_le (one_le_latticeWeight _) (one_le_latticeWeight _)
theorem hasSum_of_pointwise_eq {ι α : Type*} [AddCommMonoid α] [TopologicalSpace α]
    {f g : ι → α} {s : α} (h : HasSum g s) (e : ∀ i, f i = g i) : HasSum f s := by
  rwa [funext e]
theorem summable_tsum_sumFiber {W : Lattice4 × Lattice4 → ℝ} (hW : Summable W) :
    Summable (fun n => ∑' p : SumFiber n, W p.1) ∧
      ∑' n, ∑' p : SumFiber n, W p.1 = ∑' p, W p := by
  let e := Equiv.sigmaFiberEquiv (fun p : Lattice4 × Lattice4 => p.1 + p.2)
  have hs : Summable (fun x : Σ n, SumFiber n => W x.2.1) := e.summable_iff.mpr hW
  refine ⟨hs.sigma, ?_⟩
  rw [← hs.tsum_sigma]
  exact e.tsum_eq W
section Pairs
variable {M K L : ℕ} [NeZero M] [NeZero K] [NeZero L]
  (A : Lattice4 → Matrix (Fin M) (Fin K) ℂ) (B : Lattice4 → Matrix (Fin K) (Fin L) ℂ)
def weightedNormProduct (p : Lattice4 × Lattice4) : ℝ :=
  (opNormValue (A p.1) * latticeWeight p.1 ^ 3) * (opNormValue (B p.2) * latticeWeight p.2 ^ 3)
variable {A B}
theorem summable_weightedNormProduct
    (hA : Summable fun n => opNormValue (A n) * latticeWeight n ^ 3)
    (hB : Summable fun n => opNormValue (B n) * latticeWeight n ^ 3) :
    Summable (weightedNormProduct A B) :=
  hA.mul_of_nonneg hB
    (fun n => mul_nonneg (opNormValue_nonneg _)
      (pow_nonneg (by linarith [one_le_latticeWeight n]) _))
    (fun n => mul_nonneg (opNormValue_nonneg _)
      (pow_nonneg (by linarith [one_le_latticeWeight n]) _))
theorem opNormValue_term_le {g : Lattice4 × Lattice4 → ℂ} {C : ℝ} {p : Lattice4 × Lattice4}
    (hg : ‖g p‖ ≤ C * (latticeWeight p.1 ^ 3 * latticeWeight p.2 ^ 3)) :
    opNormValue (g p • (A p.1 * B p.2)) ≤ C * weightedNormProduct A B p := by
  rw [opNormValue_smul]
  calc ‖g p‖ * opNormValue (A p.1 * B p.2)
      ≤ (C * (latticeWeight p.1 ^ 3 * latticeWeight p.2 ^ 3)) *
          (opNormValue (A p.1) * opNormValue (B p.2)) :=
        mul_le_mul hg (opNormValue_mul_le _ _) (opNormValue_nonneg _) ((norm_nonneg _).trans hg)
    _ = C * weightedNormProduct A B p := by unfold weightedNormProduct; ring
theorem summable_sumFiber (hF : Summable (weightedNormProduct A B)) {g : Lattice4 × Lattice4 → ℂ}
    {C : ℝ} (hg : ∀ p, ‖g p‖ ≤ C * (latticeWeight p.1 ^ 3 * latticeWeight p.2 ^ 3))
    (n : Lattice4) :
    Summable fun p : SumFiber n => g p.1 • (A p.1.1 * B p.1.2) :=
  summable_of_opNormValue_le
    ((hF.mul_left C).comp_injective Subtype.val_injective) fun p => opNormValue_term_le (hg p.1)
end Pairs
def moyalRemainderFactor (φ : ℝ) (p : Lattice4 × Lattice4) : ℂ :=
  Complex.exp (Complex.I / 2 * (φ : ℂ) * (symplecticForm p.1 p.2 : ℂ)) - 1 +
    (Complex.I / 2 * (φ : ℂ)) * (-(symplecticForm p.1 p.2 : ℂ)) +
    ((1 / 8 : ℂ) * (φ : ℂ) ^ 2) * (symplecticForm p.1 p.2 : ℂ) ^ 2
theorem moyalRemainderFactor_eq (φ : ℝ) (p : Lattice4 × Lattice4) :
    moyalRemainderFactor φ p = expCubicRemainder (φ * (symplecticForm p.1 p.2 : ℝ) / 2) := by
  have h : Complex.I / 2 * (φ : ℂ) * (symplecticForm p.1 p.2 : ℂ) =
      Complex.I * ((φ * (symplecticForm p.1 p.2 : ℝ) / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  unfold moyalRemainderFactor expCubicRemainder
  rw [h]
  push_cast
  ring
theorem norm_moyalRemainderFactor_le (φ : ℝ) (p : Lattice4 × Lattice4) :
    ‖moyalRemainderFactor φ p‖ ≤
      1 / 48 * |φ| ^ 3 * (latticeWeight p.1 ^ 3 * latticeWeight p.2 ^ 3) := by
  rw [moyalRemainderFactor_eq]
  refine (norm_expCubicRemainder_le _).trans ?_
  have hform : |(symplecticForm p.1 p.2 : ℝ)| ^ 3 ≤ (latticeWeight p.1 * latticeWeight p.2) ^ 3 :=
    pow_le_pow_left₀ (abs_nonneg _) (abs_symplecticForm_le_latticeWeight p) 3
  have hs : |φ * (symplecticForm p.1 p.2 : ℝ) / 2| ^ 3 =
      |φ| ^ 3 * |(symplecticForm p.1 p.2 : ℝ)| ^ 3 / 8 := by
    rw [abs_div, abs_mul, abs_two, div_pow, mul_pow]
    norm_num
  rw [hs, ← mul_pow (latticeWeight p.1) (latticeWeight p.2)]
  have hφ : 0 ≤ |φ| ^ 3 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hform hφ]
theorem norm_moyalPhase_le (φ : ℝ) (p : Lattice4 × Lattice4) :
    ‖Complex.exp (Complex.I / 2 * (φ : ℂ) * (symplecticForm p.1 p.2 : ℂ))‖ ≤
      1 * (latticeWeight p.1 ^ 3 * latticeWeight p.2 ^ 3) := by
  have h : Complex.I / 2 * (φ : ℂ) * (symplecticForm p.1 p.2 : ℂ) =
      Complex.I * ((φ * (symplecticForm p.1 p.2 : ℝ) / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h, Complex.norm_exp_I_mul_ofReal, one_mul, ← mul_pow]
  exact one_le_pow₀ (one_le_latticeWeight_mul p)
theorem norm_one_le_latticeWeight (p : Lattice4 × Lattice4) :
    ‖(1 : ℂ)‖ ≤ 1 * (latticeWeight p.1 ^ 3 * latticeWeight p.2 ^ 3) := by
  rw [norm_one, one_mul, ← mul_pow]
  exact one_le_pow₀ (one_le_latticeWeight_mul p)
theorem norm_neg_symplecticForm_le (p : Lattice4 × Lattice4) :
    ‖-(symplecticForm p.1 p.2 : ℂ)‖ ≤ 1 * (latticeWeight p.1 ^ 3 * latticeWeight p.2 ^ 3) := by
  have h : ‖-(symplecticForm p.1 p.2 : ℂ)‖ = |(symplecticForm p.1 p.2 : ℝ)| := by
    rw [norm_neg, ← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
  rw [h, one_mul, ← mul_pow]
  refine (abs_symplecticForm_le_latticeWeight p).trans ?_
  exact le_self_pow₀ (one_le_latticeWeight_mul p) (by norm_num)
theorem norm_symplecticForm_sq_le (p : Lattice4 × Lattice4) :
    ‖(symplecticForm p.1 p.2 : ℂ) ^ 2‖ ≤ 1 * (latticeWeight p.1 ^ 3 * latticeWeight p.2 ^ 3) := by
  have h : ‖(symplecticForm p.1 p.2 : ℂ) ^ 2‖ = |(symplecticForm p.1 p.2 : ℝ)| ^ 2 := by
    rw [norm_pow, ← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
  rw [h, one_mul, ← mul_pow]
  refine (pow_le_pow_left₀ (abs_nonneg _) (abs_symplecticForm_le_latticeWeight p) 2).trans ?_
  exact pow_le_pow_right₀ (one_le_latticeWeight_mul p) (by norm_num)
theorem moyalRemainderBound_holds (hStar : MoyalProductBounds)
    (hBrackets : SymbolBracketSeries)
    (hCoeffs : FourierCoeffsOfSymbol) : MoyalRemainderBound := by
  intro φ N' N'' N''' _ _ _ a a' ha ha' r hr
  have hA : Summable fun n => opNormValue (fourierCoeff a n) * latticeWeight n ^ 3 :=
    ((hCoeffs N' N'' a).2 ha).2 3 le_rfl
  have hB : Summable fun n => opNormValue (fourierCoeff a' n) * latticeWeight n ^ 3 :=
    ((hCoeffs N'' N''' a').2 ha').2 3 le_rfl
  have hF := summable_weightedNormProduct hA hB
  obtain ⟨-, hStarSum, -, -, -⟩ := hStar φ N' N'' N''' a a' ha ha'
  obtain ⟨h0, h1, h2⟩ := hBrackets N' N'' N''' a a' ha ha'
  let R : (Fin 4 → ℤ) → Matrix (Fin N') (Fin N''') ℂ := fun n =>
    moyalCoeff φ a a' n -
      (∑' p : {p : (Fin 4 → ℤ) × (Fin 4 → ℤ) // p.1 + p.2 = n},
        fourierCoeff a p.1.1 * fourierCoeff a' p.1.2) +
      (Complex.I / 2 * (φ : ℂ)) • (∑' p : {p : (Fin 4 → ℤ) × (Fin 4 → ℤ) // p.1 + p.2 = n},
        (-(symplecticForm p.1.1 p.1.2 : ℂ)) • (fourierCoeff a p.1.1 * fourierCoeff a' p.1.2)) +
      ((1 / 8 : ℂ) * (φ : ℂ) ^ 2) • (∑' p : {p : (Fin 4 → ℤ) × (Fin 4 → ℤ) // p.1 + p.2 = n},
        ((symplecticForm p.1.1 p.1.2 : ℂ) ^ 2) • (fourierCoeff a p.1.1 * fourierCoeff a' p.1.2))
  have hExp : HasFourierExpansion R r := fun q => by
    have h := (((hStarSum q).sub (h0 q)).add ((h1 q).const_smul (Complex.I / 2 * (φ : ℂ)))).add
      ((h2 q).const_smul ((1 / 8 : ℂ) * (φ : ℂ) ^ 2))
    rw [hr q]
    refine hasSum_of_pointwise_eq h fun n => ?_
    simp only [R, smul_add, smul_sub]
    rw [smul_comm _ (Complex.I / 2 * (φ : ℂ)), smul_comm _ ((1 / 8 : ℂ) * (φ : ℂ) ^ 2)]
  have hRsum : ∀ n, HasSum (fun p : SumFiber n =>
      moyalRemainderFactor φ p.1 • (fourierCoeff a p.1.1 * fourierCoeff a' p.1.2)) (R n) :=
    fun n => by
    have se := (summable_sumFiber hF (g := fun p =>
      Complex.exp (Complex.I / 2 * (φ : ℂ) * (symplecticForm p.1 p.2 : ℂ)))
        (norm_moyalPhase_le φ) n).hasSum
    have s0 := (summable_sumFiber hF (g := fun _ => 1) norm_one_le_latticeWeight n).hasSum
    have s1 := (summable_sumFiber hF (g := fun p => -(symplecticForm p.1 p.2 : ℂ))
      norm_neg_symplecticForm_le n).hasSum
    have s2 := (summable_sumFiber hF (g := fun p => (symplecticForm p.1 p.2 : ℂ) ^ 2)
      norm_symplecticForm_sq_le n).hasSum
    simp only [one_smul] at s0
    have h := ((se.sub s0).add (s1.const_smul (Complex.I / 2 * (φ : ℂ)))).add
      (s2.const_smul ((1 / 8 : ℂ) * (φ : ℂ) ^ 2))
    refine hasSum_of_pointwise_eq h fun p => ?_
    simp only [moyalRemainderFactor, add_smul, sub_smul, one_smul, mul_smul]
  have hRnorm : ∀ n, opNormValue (R n) ≤
      1 / 48 * |φ| ^ 3 *
        ∑' p : SumFiber n, weightedNormProduct (fourierCoeff a) (fourierCoeff a') p.1 := by
    intro n
    have hfib : Summable fun p : SumFiber n =>
        weightedNormProduct (fourierCoeff a) (fourierCoeff a') p.1 :=
      hF.comp_injective Subtype.val_injective
    have hle : ∀ p : SumFiber n, opNormValue
        (moyalRemainderFactor φ p.1 • (fourierCoeff a p.1.1 * fourierCoeff a' p.1.2)) ≤
        1 / 48 * |φ| ^ 3 * weightedNormProduct (fourierCoeff a) (fourierCoeff a') p.1 :=
      fun p => opNormValue_term_le (norm_moyalRemainderFactor_le φ p.1)
    have hsn : Summable fun p : SumFiber n => opNormValue
        (moyalRemainderFactor φ p.1 • (fourierCoeff a p.1.1 * fourierCoeff a' p.1.2)) :=
      Summable.of_nonneg_of_le (fun _ => opNormValue_nonneg _) hle (hfib.mul_left _)
    rw [← (hRsum n).tsum_eq, ← tsum_mul_left]
    exact (opNormValue_tsum_le hsn).trans (hsn.tsum_le_tsum hle (hfib.mul_left _))
  obtain ⟨hDsum, hDtot⟩ := summable_tsum_sumFiber hF
  have hRsummable : Summable fun n => opNormValue (R n) :=
    Summable.of_nonneg_of_le (fun _ => opNormValue_nonneg _) hRnorm (hDsum.mul_left _)
  refine ⟨⟨R, hExp, hRsummable⟩, ?_⟩
  have hcoef : R = fourierCoeff r :=
    ((hCoeffs N' N''' r).1 ⟨R, hExp, hRsummable⟩).2.2 R hExp hRsummable
  have hnorm0 : weightedCoeffNorm 0 r = ∑' n, opNormValue (R n) := by
    unfold weightedCoeffNorm
    simp only [pow_zero, mul_one, ← hcoef]
  have hprod : weightedCoeffNorm 3 a * weightedCoeffNorm 3 a' =
      ∑' p, weightedNormProduct (fourierCoeff a) (fourierCoeff a') p :=
    hA.tsum_mul_tsum hB (summable_weightedNormProduct hA hB)
  rw [hnorm0, mul_assoc, hprod, ← hDtot, ← tsum_mul_left]
  exact hRsummable.tsum_le_tsum hRnorm (hDsum.mul_left _)
end YangMills.Construction.Tower.MoyalRemainderProof
end
