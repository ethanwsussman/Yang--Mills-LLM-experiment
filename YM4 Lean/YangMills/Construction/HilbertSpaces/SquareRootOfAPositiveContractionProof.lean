import YangMills.Construction.HilbertSpaces.ElementaryFactsOfComplexHilbertSpaces
import YangMills.Construction.HilbertSpaces.SquareRootOfAPositiveContraction
import YangMills.Construction.SpectralMeasures.IntegralsOfBoundedFunctionsAgainstAProjectionValuedMeasure
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Filter Topology
open scoped ComplexOrder InnerProductSpace
noncomputable section
namespace YangMills.Construction
open OneLoopNotation ComplexHilbert SpectralMeasures LatticeConventions
namespace ContractionUnitary.SqrtContraction
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def sqrtRadial : intervalCircle → ℂ := sqrtFn ∘ projIcc
theorem isBddMeasurable_sqrtRadial : IsBddMeasurable sqrtRadial := by
  obtain ⟨hm, C, hC⟩ := isBddMeasurable_sqrtFn
  exact ⟨hm.comp measurable_projIcc, C, fun x => hC _⟩
theorem sqrtRadial_apply (x : intervalCircle) :
    sqrtRadial x = ((Real.sqrt (x.1.1 : ℝ) : ℝ) : ℂ) := rfl
theorem sqrtRadial_mul_self : sqrtRadial * sqrtRadial = radialCoord := by
  funext x
  have hx : (0 : ℝ) ≤ (x.1.1 : ℝ) := x.2.1.1
  rw [Pi.mul_apply, sqrtRadial_apply, ← Complex.ofReal_mul, Real.mul_self_sqrt hx]
  rfl
def invSqrtTrunc (n : ℕ) : intervalCircle → ℂ := fun x =>
  if 1 / ((n : ℝ) + 1) ≤ (x.1.1 : ℝ) then (((Real.sqrt (x.1.1 : ℝ))⁻¹ : ℝ) : ℂ) else 0
theorem isBddMeasurable_invSqrtTrunc (n : ℕ) : IsBddMeasurable (invSqrtTrunc n) := by
  have hm : Measurable fun x : intervalCircle => (x.1.1 : ℝ) :=
    measurable_fst.comp measurable_subtype_coe
  refine ⟨Measurable.ite (measurableSet_le measurable_const hm)
    (Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp hm).inv)
    measurable_const, (n : ℝ) + 1, fun x => ?_⟩
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  unfold invSqrtTrunc
  split_ifs with h
  · have ht : (x.1.1 : ℝ) ≤ 1 := x.2.1.2
    have hinv : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hpos : (0 : ℝ) < (x.1.1 : ℝ) := lt_of_lt_of_le hinv h
    have hle : (x.1.1 : ℝ) ≤ Real.sqrt (x.1.1 : ℝ) :=
      (Real.le_sqrt' hpos).mpr (by nlinarith)
    have hs : 0 < Real.sqrt (x.1.1 : ℝ) := Real.sqrt_pos.mpr hpos
    have hlow : ((n : ℝ) + 1)⁻¹ ≤ Real.sqrt (x.1.1 : ℝ) := by
      rw [← one_div]
      exact h.trans hle
    have hup : (Real.sqrt (x.1.1 : ℝ))⁻¹ ≤ (n : ℝ) + 1 := (inv_le_comm₀ hs hn).mpr hlow
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)]
    exact hup
  · simpa using hn.le
theorem sqrtRadial_mul_invSqrtTrunc_apply (n : ℕ) (x : intervalCircle) :
    (sqrtRadial * invSqrtTrunc n) x =
      if 1 / ((n : ℝ) + 1) ≤ (x.1.1 : ℝ) then 1 else 0 := by
  simp only [Pi.mul_apply, invSqrtTrunc]
  split_ifs with h
  · have hinv : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hs : Real.sqrt (x.1.1 : ℝ) ≠ 0 :=
      (Real.sqrt_pos.mpr (lt_of_lt_of_le hinv h)).ne'
    rw [sqrtRadial_apply, ← Complex.ofReal_mul, mul_inv_cancel₀ hs, Complex.ofReal_one]
  · rw [mul_zero]
def zeroSlice : MeasSet intervalCircle :=
  tube (⟨{0}, measurableSet_singleton 0⟩ : MeasSet (Set.Icc (0 : ℝ) 1))
theorem mem_zeroSlice_iff (x : intervalCircle) : x ∈ zeroSlice.1 ↔ (x.1.1 : ℝ) = 0 := by
  constructor
  · intro h
    have hx : projIcc x = 0 := h
    exact congrArg Subtype.val hx
  · intro h
    exact show projIcc x = 0 from Subtype.ext h
def posIndicator : intervalCircle → ℂ :=
  (fun _ => 1) + (-1 : ℂ) • (indicatorOne zeroSlice.1 : intervalCircle → ℂ)
theorem posIndicator_apply (x : intervalCircle) :
    posIndicator x = if (x.1.1 : ℝ) = 0 then 0 else 1 := by
  have hx : posIndicator x = 1 + (-1 : ℂ) * (indicatorOne zeroSlice.1 x : ℂ) := rfl
  rw [hx]
  split_ifs with h
  · have hi : (indicatorOne zeroSlice.1 x : ℂ) = 1 :=
      Set.indicator_of_mem ((mem_zeroSlice_iff x).mpr h) _
    rw [hi]
    ring
  · have hi : (indicatorOne zeroSlice.1 x : ℂ) = 0 :=
      Set.indicator_of_notMem (fun h' => h ((mem_zeroSlice_iff x).mp h')) _
    rw [hi]
    ring
theorem isBddMeasurable_indicatorOne (Y : MeasSet intervalCircle) :
    IsBddMeasurable (indicatorOne Y.1 : intervalCircle → ℂ) := by
  refine ⟨(measurable_const : Measurable (constOne : intervalCircle → ℂ)).indicator Y.2, 1,
    fun x => ?_⟩
  by_cases h : x ∈ Y.1
  · have hi : (indicatorOne Y.1 x : ℂ) = 1 := Set.indicator_of_mem h _
    simp [hi]
  · have hi : (indicatorOne Y.1 x : ℂ) = 0 := Set.indicator_of_notMem h _
    simp [hi]
theorem isBddMeasurable_one : IsBddMeasurable (fun _ : intervalCircle => (1 : ℂ)) :=
  ⟨measurable_const, 1, fun _ => by simp⟩
theorem isBddMeasurable_neg_indicatorOne :
    IsBddMeasurable ((-1 : ℂ) • (indicatorOne zeroSlice.1 : intervalCircle → ℂ)) := by
  obtain ⟨hm, C, hC⟩ := isBddMeasurable_indicatorOne zeroSlice
  exact ⟨hm.const_smul _, C, fun x => by simpa using hC x⟩
theorem isBddMeasurable_posIndicator : IsBddMeasurable posIndicator := by
  refine ⟨isBddMeasurable_one.1.add isBddMeasurable_neg_indicatorOne.1, 1, fun x => ?_⟩
  rw [posIndicator_apply]
  split_ifs <;> simp
theorem isBddMeasurable_sqrtRadial_mul_invSqrtTrunc (n : ℕ) :
    IsBddMeasurable (sqrtRadial * invSqrtTrunc n) :=
  ⟨isBddMeasurable_sqrtRadial.1.mul (isBddMeasurable_invSqrtTrunc n).1, 1, fun x => by
    rw [sqrtRadial_mul_invSqrtTrunc_apply]
    split_ifs <;> simp⟩
theorem tendsto_sqrtRadial_mul_invSqrtTrunc (x : intervalCircle) :
    Tendsto (fun n => (sqrtRadial * invSqrtTrunc n) x) atTop (𝓝 (posIndicator x)) := by
  by_cases h : (x.1.1 : ℝ) = 0
  · have hconst : ∀ n : ℕ, (sqrtRadial * invSqrtTrunc n) x = posIndicator x := fun n => by
      have hinv : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      rw [sqrtRadial_mul_invSqrtTrunc_apply, posIndicator_apply, if_pos h, if_neg]
      rw [h]
      exact not_le.mpr hinv
    simp only [hconst]
    exact tendsto_const_nhds
  · have hpos : (0 : ℝ) < (x.1.1 : ℝ) := lt_of_le_of_ne x.2.1.1 (Ne.symm h)
    have hev : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < (x.1.1 : ℝ) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.eventually_lt_const hpos
    refine tendsto_const_nhds.congr' (hev.mono fun n hn => ?_)
    beta_reduce
    rw [sqrtRadial_mul_invSqrtTrunc_apply, posIndicator_apply, if_neg h, if_pos hn.le]
theorem isSymmetricOp_contractionSqrt (hI : BddCalculus.Statement)
    (A : BddOp H) : IsSymmetricOp (contractionSqrt A) :=
  (hI intervalCircle H (jointSpectralMeasure A (idOp H))).isSymmetricOp_bddIntegral sqrtRadial
    isBddMeasurable_sqrtRadial (fun _ => Complex.ofReal_im _)
theorem opGE_contractionSqrt (hI : BddCalculus.Statement)
    (A : BddOp H) : OpGE (contractionSqrt A) 0 :=
  (hI intervalCircle H (jointSpectralMeasure A (idOp H))).bddIntegral_nonneg sqrtRadial
    isBddMeasurable_sqrtRadial
    (fun _ => Complex.zero_le_real.mpr (Real.sqrt_nonneg _))
theorem contractionSqrt_mul_self (hJ : JointSpectral.statement)
    (hI : BddCalculus.Statement) {A : BddOp H}
    (hA : IsSymmetricOp A) (hA₀ : OpGE A 0) (hA₁ : OpLE A (idOp H)) :
    contractionSqrt A * contractionSqrt A = A := by
  have hR := hI intervalCircle H (jointSpectralMeasure A (idOp H))
  have hM := (hJ H A (idOp H) (isCommutingPair_idOp hA hA₀ hA₁)).1.2
  have hprod := hR.bddIntegral_mul _ _ isBddMeasurable_sqrtRadial isBddMeasurable_sqrtRadial
  rw [sqrtRadial_mul_self, hM.1] at hprod
  exact hprod.symm
theorem eq_of_commute_of_mul_self_eq
    (hCS : HilbertFacts.PosOpCauchySchwarz)
    {S B : BddOp H} (hS : IsSymmetricOp S) (hS₀ : OpGE S 0)
    (hB : IsSymmetricOp B) (hB₀ : OpGE B 0) (hcomm : B * S = S * B)
    (hsq : S * S = B * B) : B = S := by
  ext ψ
  obtain ⟨φ, hφ⟩ : ∃ φ : H, φ = S ψ - B ψ := ⟨_, rfl⟩
  have hsum : S φ + B φ = 0 := by
    have hc : B (S ψ) = S (B ψ) := congrArg (fun T : BddOp H => T ψ) hcomm
    have hs : S (S ψ) = B (B ψ) := congrArg (fun T : BddOp H => T ψ) hsq
    rw [hφ, map_sub, map_sub, hc, hs]
    abel
  have hinner : ⟪φ, S φ⟫_ℂ + ⟪φ, B φ⟫_ℂ = 0 := by
    rw [← inner_add_right, hsum, inner_zero_right]
  have hSnn : 0 ≤ ⟪φ, S φ⟫_ℂ := by simpa using hS₀.le φ
  have hBnn : 0 ≤ ⟪φ, B φ⟫_ℂ := by simpa using hB₀.le φ
  have hboth := (add_eq_zero_iff_of_nonneg hSnn hBnn).mp hinner
  have hSφ : S φ = 0 := (hCS H S hS hS₀).2 φ hboth.1
  have hBφ : B φ = 0 := (hCS H B hB hB₀).2 φ hboth.2
  have hself : ⟪φ, φ⟫_ℂ = 0 := by
    calc ⟪φ, φ⟫_ℂ = ⟪S ψ, φ⟫_ℂ - ⟪B ψ, φ⟫_ℂ := by rw [← inner_sub_left, ← hφ]
      _ = ⟪ψ, S φ⟫_ℂ - ⟪ψ, B φ⟫_ℂ := by rw [hS ψ φ, hB ψ φ]
      _ = 0 := by simp [hSφ, hBφ]
  have hzero : φ = 0 := inner_self_eq_zero.mp hself
  rw [hφ] at hzero
  exact (sub_eq_zero.mp hzero).symm
theorem linearKer_eq_of_mul_self_eq {S A : BddOp H} (hsq : S * S = A)
    (hnorm : ∀ ψ : H, ((‖S ψ‖ ^ 2 : ℝ) : ℂ) = ⟪ψ, A ψ⟫_ℂ) :
    linearKer (S : H →ₗ[ℂ] H) = linearKer (A : H →ₗ[ℂ] H) := by
  ext ψ
  constructor
  · intro h
    have hSψ : S ψ = 0 := h
    have hSS : S (S ψ) = A ψ := congrArg (fun T : BddOp H => T ψ) hsq
    change A ψ = 0
    rw [← hSS, hSψ, map_zero]
  · intro h
    have hAψ : A ψ = 0 := h
    change S ψ = 0
    have hn := hnorm ψ
    rw [hAψ, inner_zero_right] at hn
    have hsq0 : ‖S ψ‖ ^ 2 = 0 := by exact_mod_cast hn
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hsq0)
theorem seqClosureOf_linearRange_contractionSqrt (hJ : JointSpectral.statement)
    (hI : BddCalculus.Statement)
    (hO : HilbertFacts.OrthSetClosed)
    {A : BddOp H} (hA : IsSymmetricOp A) (hA₀ : OpGE A 0)
    (hA₁ : OpLE A (idOp H))
    (hK : linearKer (contractionSqrt A : H →ₗ[ℂ] H) = linearKer (A : H →ₗ[ℂ] H)) :
    seqClosureOf (linearRange (contractionSqrt A : H →ₗ[ℂ] H)) =
      orthSet (linearKer (A : H →ₗ[ℂ] H)) := by
  apply Set.Subset.antisymm
  · have hcl : IsClosed (orthSet (linearKer (A : H →ₗ[ℂ] H))) :=
      (isClosedSet_iff _).mp (hO H _).2
    rw [seqClosureOf_eq_closure]
    refine closure_minimal ?_ hcl
    rintro _ ⟨φ, rfl⟩ ψ hψ
    rw [← hK] at hψ
    have hr : contractionSqrt A ψ = 0 := hψ
    change ⟪contractionSqrt A φ, ψ⟫_ℂ = 0
    rw [← isSymmetricOp_contractionSqrt hI A φ ψ, hr, inner_zero_right]
  · intro χ hχ
    have hR := hI intervalCircle H (jointSpectralMeasure A (idOp H))
    obtain ⟨hproj, hfix⟩ :=
      (hJ H A (idOp H) (isCommutingPair_idOp hA hA₀ hA₁)).2.2.2.2
    obtain ⟨P, hP⟩ : ∃ P : BddOp H,
        P = jointSpectralMeasure A (idOp H) zeroSlice := ⟨_, rfl⟩
    have hprojP : IsOrthProj P := hP ▸ hproj
    have hfixP : LinearMap.ker (A : H →ₗ[ℂ] H) = fixedSubspace P := hP ▸ hfix
    have hidem : P (P χ) = P χ := by
      have hsq : (P ^ 2) χ = P χ := by rw [hprojP.idempotent]
      rw [pow_two] at hsq
      exact hsq
    have hmem : P χ ∈ LinearMap.ker (A : H →ₗ[ℂ] H) := by
      rw [hfixP]
      exact hidem
    have horth : ⟪χ, P χ⟫_ℂ = 0 := hχ _ (LinearMap.mem_ker.mp hmem)
    have hPP : ⟪P χ, P χ⟫_ℂ = 0 := by
      rw [← hprojP.selfAdjoint χ (P χ), hidem]
      exact horth
    have hzero : P χ = 0 := inner_self_eq_zero.mp hPP
    have hG : (jointSpectralMeasure A (idOp H)).bddIntegral posIndicator χ = χ := by
      have hsplit : (jointSpectralMeasure A (idOp H)).bddIntegral posIndicator =
          idOp H + (-1 : ℂ) • P := by
        rw [hP, posIndicator, hR.bddIntegral_add _ _ isBddMeasurable_one
          isBddMeasurable_neg_indicatorOne, hR.bddIntegral_one,
          hR.bddIntegral_smul _ _ (isBddMeasurable_indicatorOne zeroSlice),
          hR.bddIntegral_indicator zeroSlice]
      rw [hsplit]
      change χ + (-1 : ℂ) • P χ = χ
      rw [hzero, smul_zero, add_zero]
    have ht := hR.tendsto_bddIntegral (fun n => sqrtRadial * invSqrtTrunc n) posIndicator
      isBddMeasurable_sqrtRadial_mul_invSqrtTrunc isBddMeasurable_posIndicator
      tendsto_sqrtRadial_mul_invSqrtTrunc ⟨1, fun n x => by
        rw [sqrtRadial_mul_invSqrtTrunc_apply]
        split_ifs <;> simp⟩ χ
    rw [hG] at ht
    refine ⟨fun n => (jointSpectralMeasure A (idOp H)).bddIntegral
      (sqrtRadial * invSqrtTrunc n) χ, fun n =>
      ⟨(jointSpectralMeasure A (idOp H)).bddIntegral (invSqrtTrunc n) χ, ?_⟩, ht⟩
    beta_reduce
    rw [hR.bddIntegral_mul _ _ isBddMeasurable_sqrtRadial (isBddMeasurable_invSqrtTrunc n)]
    rfl
theorem sqrtContractionProperties_holds (hJ : JointSpectral.statement)
    (hI : BddCalculus.Statement)
    (hE : HilbertFacts.ElementaryFacts) : SqrtContractionProperties := by
  intro H _ _ _ A hA hA₀ hA₁
  have hS := isSymmetricOp_contractionSqrt hI A
  have hS₀ := opGE_contractionSqrt hI A
  have hsq := contractionSqrt_mul_self hJ hI hA hA₀ hA₁
  have hpair := isCommutingPair_idOp hA hA₀ hA₁
  have hnorm : ∀ ψ : H, ((‖contractionSqrt A ψ‖ ^ 2 : ℝ) : ℂ) = ⟪ψ, A ψ⟫_ℂ := by
    intro ψ
    have hSS : contractionSqrt A (contractionSqrt A ψ) = A ψ :=
      congrArg (fun T : BddOp H => T ψ) hsq
    have hns : ⟪contractionSqrt A ψ, contractionSqrt A ψ⟫_ℂ =
        ((‖contractionSqrt A ψ‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast
    rw [← hns, ← hS ψ, hSS]
  have hcomm : ∀ C : BddOp H, C * A = A * C →
      C * contractionSqrt A = contractionSqrt A * C := fun C hC =>
    (hJ H A (idOp H) hpair).2.2.1.2 C hC (by ext ψ; rfl) sqrtRadial isBddMeasurable_sqrtRadial
  have hK := linearKer_eq_of_mul_self_eq hsq hnorm
  refine ⟨⟨hS, hS₀, by rw [pow_two, hsq], hnorm, fun B hB hB₀ hB₂ => ?_⟩,
    ⟨fun H' _ _ _ A' B hA' hA₀' hA₁' hBA => ?_, hcomm⟩, hK,
    seqClosureOf_linearRange_contractionSqrt hJ hI hE.2.2.2.1.2.1 hA hA₀ hA₁ hK⟩
  · have hBA : B * A = A * B := by
      rw [← hB₂, pow_two, mul_assoc]
    refine eq_of_commute_of_mul_self_eq hE.2.2.1 hS hS₀ hB hB₀ (hcomm B hBA) ?_
    rw [hsq, ← hB₂, pow_two]
  · exact ((hJ H A (idOp H) hpair).2.2.1.1 H' A' (idOp H') B
      (isCommutingPair_idOp hA' hA₀' hA₁') hBA (by ext ψ; rfl)).1 sqrtRadial
      isBddMeasurable_sqrtRadial
end ContractionUnitary.SqrtContraction
end YangMills.Construction
end
