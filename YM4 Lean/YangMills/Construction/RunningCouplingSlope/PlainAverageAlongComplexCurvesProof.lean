import YangMills.Construction.Lattice.BlocksBoxesAndPaths
import YangMills.Construction.Lattice.ContourFamiliesAndCombsInABlock
import YangMills.Construction.Lattice.CrossingsAndBareBlocksInTheToolbox
import YangMills.Construction.Matrices.NormExpLogBasicsProof
import YangMills.Construction.Matrices.PointwiseDerivativeRules
import YangMills.Construction.RunningCouplingSlope.PlainAverageAlongComplexCurves
import YangMills.Construction.Towers.BlocksStraightPathsContoursAndPivotBondsOfATowerProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.ContourMeanDerivative
open Tower
open Matrices
section Curves
variable {ι : Type*} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
def HasDerivAlongCurves (V g : ι → ComplexMatrix2) (f : (ι → ComplexMatrix2) → E) (D : E) : Prop :=
  ∀ γ : ℂ → ι → ComplexMatrix2, γ 0 = V → (∀ b, HasDerivAt (fun t => γ t b) (g b) 0) →
    HasDerivAt (fun t => f (γ t)) D 0
variable {V g : ι → ComplexMatrix2}
theorem hasDerivAlongCurves_apply (b : ι) : HasDerivAlongCurves V g (fun U => U b) (g b) :=
  fun _ _ h => h b
theorem hasDerivAlongCurves_const (x : E) : HasDerivAlongCurves V g (fun _ => x) 0 :=
  fun _ _ _ => hasDerivAt_const _ _
theorem hasDerivAlongCurves_mul {f₁ f₂ : (ι → ComplexMatrix2) → ComplexMatrix2}
    {D₁ D₂ : ComplexMatrix2} (h₁ : HasDerivAlongCurves V g f₁ D₁)
    (h₂ : HasDerivAlongCurves V g f₂ D₂) :
    HasDerivAlongCurves V g (fun U => f₁ U * f₂ U) (D₁ * f₂ V + f₁ V * D₂) := by
  intro γ h0 hγ
  have := (h₁ γ h0 hγ).mul (h₂ γ h0 hγ)
  rw [h0] at this
  exact this
theorem hasDerivAlongCurves_sum {α : Type*} (s : Finset α) {f : α → (ι → ComplexMatrix2) → E}
    {D : α → E} (h : ∀ a ∈ s, HasDerivAlongCurves V g (f a) (D a)) :
    HasDerivAlongCurves V g (fun U => ∑ a ∈ s, f a U) (∑ a ∈ s, D a) :=
  fun γ h0 hγ => HasDerivAt.fun_sum fun a ha => h a ha γ h0 hγ
theorem hasDerivAlongCurves_const_smul {f : (ι → ComplexMatrix2) → ComplexMatrix2}
    {D : ComplexMatrix2} (a : ℂ) (h : HasDerivAlongCurves V g f D) :
    HasDerivAlongCurves V g (fun U => a • f U) (a • D) :=
  fun γ h0 hγ => (h γ h0 hγ).const_smul a
theorem hasDerivAlongCurves_inv (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    {f : (ι → ComplexMatrix2) → ComplexMatrix2} {D : ComplexMatrix2}
    (h : HasDerivAlongCurves V g f D) (hu : IsUnit (Matrix.det (f V))) :
    HasDerivAlongCurves V g (fun U => (f U)⁻¹) (-((f V)⁻¹ * D * (f V)⁻¹)) := by
  intro γ h0 hγ
  have hF := h γ h0 hγ
  set w := (f V)⁻¹ with hw
  have hfw : f V * w = 1 := Matrix.mul_nonsing_inv _ hu
  have hwf : w * f V = 1 := Matrix.nonsing_inv_mul _ hu
  have hdw : IsUnit (Matrix.det w) := by
    have h1 : Matrix.det w * Matrix.det (f V) = 1 := by rw [← Matrix.det_mul, hwf, Matrix.det_one]
    exact IsUnit.of_mul_eq_one _ h1
  have hX : HasDerivAt (fun t => f (γ t) * w) (D * w) 0 := hF.mul_const w
  have hX0 : (fun t => f (γ t) * w) 0 = 1 := by simp only [h0, hfw]
  have hinv := ((hd.2 Set.univ _ _ _ _ _ _ Filter.univ_mem hX hX hX).2.1 hX0).2.1
  have e : (fun t => (f (γ t))⁻¹) = fun t => w * (f (γ t) * w)⁻¹ := by
    funext t
    rw [Matrix.mul_inv_rev, ← mul_assoc, Matrix.mul_nonsing_inv _ hdw, one_mul]
  rw [e]
  have := hinv.const_mul w
  exact HasDerivAt.congr_deriv this (by simp [mul_assoc])
theorem hasDerivAt_matrix_entry {W : ℂ → ComplexMatrix2} {D : ComplexMatrix2}
    (h : HasDerivAt W D 0) (a b : Fin 2) :
    HasDerivAt (fun t => W t a b) (D a b) 0 := by
  let e : ComplexMatrix2 →ₗ[ℂ] ℂ := (Matrix.entryLinearMap ℂ ℂ a b)
  exact (LinearMap.toContinuousLinearMap e).hasFDerivAt.comp_hasDerivAt 0 h
end Curves
section Linear
variable {ι : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
def HasLinearDerivAlongCurves (V : ι → ComplexMatrix2) (f : (ι → ComplexMatrix2) → E)
    (T : (ι → ComplexMatrix2) →ₗ[ℂ] E) : Prop :=
  ∀ g, HasDerivAlongCurves V g f (T g)
variable {V : ι → ComplexMatrix2}
theorem hasLinearDerivAlongCurves_apply (b : ι) :
    HasLinearDerivAlongCurves V (fun U => U b)
      (LinearMap.proj (R := ℂ) (φ := fun _ : ι => ComplexMatrix2) b) :=
  fun _ => hasDerivAlongCurves_apply b
theorem hasLinearDerivAlongCurves_one :
    HasLinearDerivAlongCurves V (fun _ => (1 : ComplexMatrix2)) 0 :=
  fun _ => hasDerivAlongCurves_const _
theorem hasLinearDerivAlongCurves_mul {f₁ f₂ : (ι → ComplexMatrix2) → ComplexMatrix2}
    {T₁ T₂ : (ι → ComplexMatrix2) →ₗ[ℂ] ComplexMatrix2}
    (h₁ : HasLinearDerivAlongCurves V f₁ T₁) (h₂ : HasLinearDerivAlongCurves V f₂ T₂) :
    HasLinearDerivAlongCurves V (fun U => f₁ U * f₂ U)
      ((LinearMap.mulRight ℂ (f₂ V)) ∘ₗ T₁ + (LinearMap.mulLeft ℂ (f₁ V)) ∘ₗ T₂) :=
  fun g => hasDerivAlongCurves_mul (h₁ g) (h₂ g)
theorem hasLinearDerivAlongCurves_sum {α : Type*} (s : Finset α)
    {f : α → (ι → ComplexMatrix2) → E} {T : α → (ι → ComplexMatrix2) →ₗ[ℂ] E}
    (h : ∀ a ∈ s, HasLinearDerivAlongCurves V (f a) (T a)) :
    HasLinearDerivAlongCurves V (fun U => ∑ a ∈ s, f a U) (∑ a ∈ s, T a) := by
  intro g
  have := hasDerivAlongCurves_sum (V := V) (g := g) s (fun a ha => h a ha g)
  simpa [LinearMap.sum_apply] using this
theorem hasLinearDerivAlongCurves_const_smul {f : (ι → ComplexMatrix2) → ComplexMatrix2}
    {T : (ι → ComplexMatrix2) →ₗ[ℂ] ComplexMatrix2} (a : ℂ)
    (h : HasLinearDerivAlongCurves V f T) :
    HasLinearDerivAlongCurves V (fun U => a • f U) (a • T) :=
  fun g => hasDerivAlongCurves_const_smul a (h g)
theorem hasLinearDerivAlongCurves_inv
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    {f : (ι → ComplexMatrix2) → ComplexMatrix2} {T : (ι → ComplexMatrix2) →ₗ[ℂ] ComplexMatrix2}
    (h : HasLinearDerivAlongCurves V f T) (hu : IsUnit (Matrix.det (f V))) :
    HasLinearDerivAlongCurves V (fun U => (f U)⁻¹)
      (-((LinearMap.mulRight ℂ (f V)⁻¹) ∘ₗ (LinearMap.mulLeft ℂ (f V)⁻¹) ∘ₗ T)) := by
  intro g
  have := hasDerivAlongCurves_inv hd (h g) hu
  simpa using this
theorem exists_hasLinearDerivAlongCurves_list_prod (l : List ι) :
    ∃ T, HasLinearDerivAlongCurves V (fun U => (l.map U).prod) T := by
  induction l with
  | nil => exact ⟨0, by simpa using hasLinearDerivAlongCurves_one (V := V)⟩
  | cons b l ih =>
    obtain ⟨T, hT⟩ := ih
    exact ⟨_, by simpa using hasLinearDerivAlongCurves_mul (hasLinearDerivAlongCurves_apply b) hT⟩
theorem exists_hasLinearDerivAlongCurves_det {f : (ι → ComplexMatrix2) → ComplexMatrix2}
    {T : (ι → ComplexMatrix2) →ₗ[ℂ] ComplexMatrix2} (h : HasLinearDerivAlongCurves V f T) :
    ∃ T' : (ι → ComplexMatrix2) →ₗ[ℂ] ℂ,
      HasLinearDerivAlongCurves V (fun U => Matrix.det (f U)) T' := by
  refine ⟨{ toFun := fun g => (T g 0 0 * f V 1 1 + f V 0 0 * T g 1 1) -
              (T g 0 1 * f V 1 0 + f V 0 1 * T g 1 0)
            map_add' := fun x y => by simp only [map_add, Matrix.add_apply]; ring
            map_smul' := fun a x => by
              simp only [map_smul, Matrix.smul_apply, RingHom.id_apply, Complex.real_smul]
              ring }, fun g γ h0 hγ => ?_⟩
  have hF := h g γ h0 hγ
  have e : (fun t => Matrix.det (f (γ t))) =
      fun t => f (γ t) 0 0 * f (γ t) 1 1 - f (γ t) 0 1 * f (γ t) 1 0 := by
    funext t
    exact Matrix.det_fin_two _
  rw [e]
  have := ((hasDerivAt_matrix_entry hF 0 0).mul (hasDerivAt_matrix_entry hF 1 1)).sub
    ((hasDerivAt_matrix_entry hF 0 1).mul (hasDerivAt_matrix_entry hF 1 0))
  simp only [h0] at this
  exact this
theorem exists_hasLinearDerivAlongCurves_sqrt {f : (ι → ComplexMatrix2) → ℂ}
    {T : (ι → ComplexMatrix2) →ₗ[ℂ] ℂ} (h : HasLinearDerivAlongCurves V f T)
    (hs : f V ∈ Complex.slitPlane) :
    ∃ T' : (ι → ComplexMatrix2) →ₗ[ℂ] ℂ,
      HasLinearDerivAlongCurves V (fun U => (f U) ^ (1 / 2 : ℂ)) T' := by
  have hr : HasDerivAt (fun z : ℂ => z ^ (1 / 2 : ℂ))
      ((1 / 2 : ℂ) * (f V) ^ ((1 / 2 : ℂ) - 1) * 1) (f V) :=
    (hasDerivAt_id (f V)).cpow_const (c := (1 / 2 : ℂ)) hs
  refine ⟨T.smulRight ((1 / 2 : ℂ) * (f V) ^ ((1 / 2 : ℂ) - 1) * 1), fun g γ h0 hγ => ?_⟩
  have hF := h g γ h0 hγ
  have := HasDerivAt.scomp (0 : ℂ) (g₁ := fun z : ℂ => z ^ (1 / 2 : ℂ))
    (by rw [h0]; exact hr) hF
  exact this
theorem exists_hasLinearDerivAlongCurves_inv_smul {r : (ι → ComplexMatrix2) → ℂ}
    {f : (ι → ComplexMatrix2) → ComplexMatrix2}
    {R : (ι → ComplexMatrix2) →ₗ[ℂ] ℂ} {T : (ι → ComplexMatrix2) →ₗ[ℂ] ComplexMatrix2}
    (hr : HasLinearDerivAlongCurves V r R) (hf : HasLinearDerivAlongCurves V f T)
    (h0 : r V ≠ 0) :
    ∃ T' : (ι → ComplexMatrix2) →ₗ[ℂ] ComplexMatrix2,
      HasLinearDerivAlongCurves V (fun U => (r U)⁻¹ • f U) T' := by
  refine ⟨(r V)⁻¹ • T + ((-((r V) ^ 2)⁻¹) • R).smulRight (f V), fun g γ hγ0 hγ => ?_⟩
  have h1 := hr g γ hγ0 hγ
  have h2 := hf g γ hγ0 hγ
  have h3 := h1.fun_inv (by rw [hγ0]; exact h0)
  have h4 := h3.fun_smul h2
  simp only [hγ0] at h4
  refine HasDerivAt.congr_deriv h4 ?_
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, smul_eq_mul]
  congr 2
  field_simp
end Linear
section Bounds
variable {ι : Type*}
theorem norm_list_prod_sub_one_le (U : ι → ComplexMatrix2) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (h : ∀ b, ‖U b - 1‖ ≤ ρ) (l : List ι) :
    ‖(l.map U).prod - 1‖ ≤ (1 + ρ) ^ l.length - 1 := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    set A := U b
    set B := (l.map U).prod
    have e : A * B - 1 = (A - 1) * (B - 1) + (A - 1) + (B - 1) := by noncomm_ring
    have h1 := h b
    have h2 : ‖(A - 1) * (B - 1)‖ ≤ ρ * ((1 + ρ) ^ l.length - 1) :=
      (norm_mul_le _ _).trans (mul_le_mul h1 ih (norm_nonneg _) hρ)
    rw [e]
    calc ‖(A - 1) * (B - 1) + (A - 1) + (B - 1)‖
        ≤ ‖(A - 1) * (B - 1)‖ + ‖A - 1‖ + ‖B - 1‖ := norm_add₃_le
      _ ≤ ρ * ((1 + ρ) ^ l.length - 1) + ρ + ((1 + ρ) ^ l.length - 1) := by gcongr
      _ = (1 + ρ) ^ (l.length + 1) - 1 := by ring
theorem norm_entry_le_operatorNorm (A : ComplexMatrix2) (a b : Fin 2) : ‖A a b‖ ≤ ‖A‖ := by apply _root_.YangMills.SharedProofs.p14523 <;> assumption
end Bounds
section Scalars
theorem sqrt_near_one (z : ℂ) (h : ‖z - 1‖ ≤ 1 / 10) :
    z ^ (1 / 2 : ℂ) ≠ 0 ∧ (z ^ (1 / 2 : ℂ)) ^ 2 = z ∧ ‖z ^ (1 / 2 : ℂ) - 1‖ ≤ ‖z - 1‖ ∧
      z ∈ Complex.slitPlane := by
  have hre : 0 < z.re := by
    have h1 : |z.re - 1| ≤ ‖z - 1‖ := by
      have := Complex.abs_re_le_norm (z - 1)
      simpa using this
    have h2 := (abs_le.mp (h1.trans h)).1
    linarith
  have hz : z ≠ 0 := fun h0 => by simp [h0] at hre
  have hsq : (z ^ (1 / 2 : ℂ)) ^ 2 = z := by
    have := Complex.cpow_nat_inv_pow z (n := 2) (by norm_num)
    simpa using this
  set r := z ^ (1 / 2 : ℂ) with hr
  have hr0 : r ≠ 0 := fun h0 => hz (by rw [← hsq, h0]; simp)
  have harg : |Complex.arg z| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  have hrre : 0 < r.re := by
    rw [hr, Complex.cpow_def_of_ne_zero hz, Complex.exp_re]
    have him : (Complex.log z * (1 / 2 : ℂ)).im = Complex.arg z / 2 := by
      simp [Complex.log_im]
      ring
    rw [him]
    refine mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ?_)
    have := abs_lt.mp harg
    constructor <;> linarith [this.1, this.2, Real.pi_pos]
  have hplus : 1 ≤ ‖r + 1‖ := by
    have := Complex.abs_re_le_norm (r + 1)
    simp only [Complex.add_re, Complex.one_re] at this
    have h2 := le_abs_self (r.re + 1)
    linarith
  have hfac : (r - 1) * (r + 1) = z - 1 := by
    have : (r - 1) * (r + 1) = r ^ 2 - 1 := by ring
    rw [this, hsq]
  have hnorm : ‖r - 1‖ * ‖r + 1‖ = ‖z - 1‖ := by rw [← norm_mul, hfac]
  refine ⟨hr0, hsq, ?_, Or.inl hre⟩
  nlinarith [norm_nonneg (r - 1)]
end Scalars
section Main
variable {L n k j : ℕ}
theorem det_list_prod_eq_one (V : Edge L n k j → ComplexMatrix2) (hV : ∀ b, Matrix.det (V b) = 1)
    (l : List (Edge L n k j)) : Matrix.det ((l.map V).prod) = 1 := by
  induction l with
  | nil => simp
  | cons b l ih => simp [Matrix.det_mul, hV, ih]
theorem inv_pathHolonomy_eq (V : Edge L n k j → ComplexMatrix2)
    (hV : ∀ b, V b.opposite = (V b)⁻¹)
    (hd : ∀ b, Matrix.det (V b) = 1) (l : List (Edge L n k j)) :
    (PeriodicLattice.pathHolonomy V l)⁻¹ =
      PeriodicLattice.pathHolonomy V (PeriodicLattice.reversePath l) := by
  induction l with
  | nil =>
    have : (1 : ComplexMatrix2)⁻¹ = 1 := Matrix.inv_eq_right_inv (mul_one 1)
    simpa [PeriodicLattice.pathHolonomy, PeriodicLattice.reversePath] using this
  | cons b l ih =>
    have e : PeriodicLattice.reversePath (b :: l) =
        PeriodicLattice.reversePath l ++ [b.opposite] := by
      simp [PeriodicLattice.reversePath]
    rw [e]
    simp only [PeriodicLattice.pathHolonomy, List.map_cons, List.prod_cons, List.map_append,
      List.prod_append, List.map_nil, List.prod_nil, mul_one, Matrix.mul_inv_rev, hV] at ih ⊢
    rw [ih]
theorem length_stepsThroughAxes {a : ℤ} (d : Fin 4 → ℤ) (x : PeriodicLattice.Site L n a)
    (l : List (Fin 4)) :
    (PeriodicLattice.stepsThroughAxes d x l).length = (l.map fun μ => (d μ).natAbs).sum := by apply _root_.YangMills.Construction.Tower.BlockPathContourPivotProof.Periodic.length_stepsThroughAxes <;> assumption
end Main
theorem contourMean_near_one
    (hcf : PeriodicLattice.BlockContoursAndCombs)
    (hbb : PeriodicLattice.BlocksBoxesPaths.Statement)
    (hb : PeriodicLattice.CrossingsAndBareBlocks.Statement) :
    ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ ρ : ℝ, 0 < ρ ∧
      ∀ n k j : ℕ, 0 < n → j < k →
        ∀ V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
          (∀ b, ComplexMatrix2.operatorNorm (V b - 1) < ρ) →
          ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
            ∃ S : Finset (Vertex L n k j), ∃ w : ℂ,
              (∀ U : Edge L n k j → ComplexMatrix2,
                contourMean U c = w • ∑ x ∈ S, ∑ π : Equiv.Perm (Fin 4), contourHolonomy U c x π) ∧
              meanRadius V c ≠ 0 ∧ ‖meanRadius V c - 1‖ < 1 / 2 ∧
              ComplexMatrix2.operatorNorm (normalizedMean V c - 1) < 1 / 2 ∧
              normalizedMean V c ∈ PeriodicLattice.complexGaugeGroup ∧
              Matrix.det (contourMean V c) ∈ Complex.slitPlane := by
  intro L hL
  have hLpos : 0 < L := by have := hL.2; omega
  set ρ : ℝ := 1 / (1000 * L) with hρdef
  have hρ : 0 < ρ := by positivity
  have hε : (1 + ρ) ^ (5 * L) - 1 ≤ 1 / 100 := by
    have h1 : 1 + ρ ≤ Real.exp ρ := by linarith [Real.add_one_le_exp ρ]
    have h2 : (1 + ρ) ^ (5 * L) ≤ Real.exp ρ ^ (5 * L) := by gcongr
    have h3 : Real.exp ρ ^ (5 * L) = Real.exp (1 / 200) := by
      rw [← Real.exp_nat_mul]
      congr 1
      rw [hρdef]
      push_cast
      field_simp
      norm_num
    have h4 : Real.exp (1 / 200) ≤ 1 + 1 / 100 := by
      have h5 := Real.add_one_le_exp (-(1 / 200 : ℝ))
      have h6 : Real.exp (1 / 200) * Real.exp (-(1 / 200)) = 1 := by
        rw [← Real.exp_add]; simp
      have h7 := Real.exp_pos (1 / 200 : ℝ)
      nlinarith
    linarith
  refine ⟨ρ, hρ, ?_⟩
  intro n k j hn hj V hV hVρ c hc
  have hK : 0 < k := by omega
  have hcard := ((hb L hL n k hn).1 j hj c hc).1
  have hfin : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
      Set (Vertex L n k j)).Finite := by
    have h4 : Nat.card ↥(PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
        Set (Vertex L n k j)) ≠ 0 := by rw [hcard]; positivity
    have := Nat.finite_of_card_ne_zero h4
    exact Set.toFinite _
  have hcross := (hbb L k n ⟨rfl, rfl, rfl, hL.1, hL.2, hK, hn⟩).2.2.2.2.2.2 j hj |>.2.1 c hc
  set S := hfin.toFinset with hSdef
  have hScard : S.card = L ^ 4 := by
    have h1 : S.card = (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
        Set (Vertex L n k j)).ncard := (Set.ncard_eq_toFinset_card _ hfin).symm
    rw [h1, ← Nat.card_coe_set_eq, hcard]
  set w : ℂ := (1 / 24 : ℂ) * PeriodicLattice.inverseFourthPowerWeight L with hw
  have hmean : ∀ U : Edge L n k j → ComplexMatrix2, contourMean U c =
      w • ∑ x ∈ S, ∑ π : Equiv.Perm (Fin 4), contourHolonomy U c x π := by
    intro U
    rw [contourMean, finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hdetV : ∀ b, Matrix.det (V b) = 1 := fun b => hV.1 b (Set.mem_univ b)
  have hrevV : ∀ b, V b.opposite = (V b)⁻¹ := fun b => hV.2 b (Set.mem_univ b)
  have hlegLen : ∀ (y : Vertex L n k (j + 1)) (x : Vertex L n k j),
      (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y →
        ∀ π, (contourLeg y x π).length ≤ 2 * L := by
    intro y x hx π
    obtain ⟨d, hd1, -⟩ := (hcf L n k hL hn j hj y x hx).1
    have hspec : PeriodicLattice.IsBlockOffset y x (PeriodicLattice.blockOffset y x) :=
      Classical.epsilon_spec ⟨d, hd1⟩
    rw [contourLeg, length_stepsThroughAxes]
    have hb1 : ∀ μ, ((PeriodicLattice.blockOffset y x) μ).natAbs ≤ L / 2 := by
      intro μ
      have h3 := hspec.2 μ
      have h4 : (((PeriodicLattice.blockOffset y x) μ).natAbs : ℤ) =
          |(PeriodicLattice.blockOffset y x) μ| := Int.natCast_natAbs _
      omega
    have h2 := List.sum_le_card_nsmul (((List.finRange 4).map π).map fun μ =>
      ((PeriodicLattice.blockOffset y x) μ).natAbs) (L / 2) (by
        intro a ha
        obtain ⟨μ, -, rfl⟩ := List.mem_map.mp ha
        exact hb1 μ)
    simp only [List.length_map, List.length_finRange, smul_eq_mul] at h2
    omega
  have hinvhol : ∀ l : List (Edge L n k j), PeriodicLattice.pathHolonomy V l =
      (l.map V).prod := fun _ => rfl
  have hcv : ∀ x ∈ S, ∀ π, ‖contourHolonomy V c x π - 1‖ ≤ (1 + ρ) ^ (5 * L) - 1 := by
    intro x hx π
    have hx1 : x ∈ (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
        Set (Vertex L n k j)) := by simpa [hSdef] using hx
    have hx2 := hcross.1.mapsTo hx1
    have hlen1 := hlegLen c.source x hx1 π
    have hlen2 := hlegLen c.target (PeriodicLattice.shiftAcross c x) hx2 π
    have hlen3 := (hcross.2 x hx1).2.1
    set Γ := contourLeg c.source x π ++ PeriodicLattice.crossingPath c x ++
      PeriodicLattice.reversePath (contourLeg c.target (PeriodicLattice.shiftAcross c x) π)
      with hΓ
    have e : contourHolonomy V c x π = (Γ.map V).prod := by
      rw [contourHolonomy, inv_pathHolonomy_eq V hrevV hdetV, hΓ]
      simp [PeriodicLattice.pathHolonomy, List.map_append, List.prod_append, mul_assoc]
    have hlen : Γ.length ≤ 5 * L := by
      simp only [hΓ, List.length_append, PeriodicLattice.reversePath, List.length_reverse,
        List.length_map]
      omega
    rw [e]
    refine (norm_list_prod_sub_one_le V ρ hρ.le (fun b => (hVρ b).le) Γ).trans ?_
    have : (1 + ρ) ^ Γ.length ≤ (1 + ρ) ^ (5 * L) :=
      pow_le_pow_right₀ (by linarith) hlen
    linarith
  have hwval : w = (((1 / (24 * (L : ℝ) ^ 4) : ℝ)) : ℂ) := by
    rw [hw, PeriodicLattice.inverseFourthPowerWeight]
    push_cast
    rw [zpow_neg]
    field_simp
  have hwnorm : ‖w‖ = 1 / (24 * (L : ℝ) ^ 4) := by
    rw [hwval, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hcount : ∑ _x ∈ S, ∑ _π : Equiv.Perm (Fin 4), (1 : ComplexMatrix2) =
      (((24 * (L : ℝ) ^ 4 : ℝ)) : ℂ) • (1 : ComplexMatrix2) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, hScard]
    rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    congr 1
    push_cast
    norm_num [Nat.factorial]
    ring
  have hone : w • ∑ _x ∈ S, ∑ _π : Equiv.Perm (Fin 4), (1 : ComplexMatrix2) = 1 := by
    rw [hcount, smul_smul, hwval, ← Complex.ofReal_mul]
    have : 1 / (24 * (L : ℝ) ^ 4) * (24 * (L : ℝ) ^ 4) = 1 := by field_simp
    rw [this]
    simp
  have hW : ‖contourMean V c - 1‖ ≤ 1 / 100 := by
    have e : contourMean V c - 1 =
        w • ∑ x ∈ S, ∑ π : Equiv.Perm (Fin 4), (contourHolonomy V c x π - 1) := by
      have h0 : w • ∑ x ∈ S, ∑ π : Equiv.Perm (Fin 4), (contourHolonomy V c x π - 1) =
          w • (∑ x ∈ S, ∑ π : Equiv.Perm (Fin 4), contourHolonomy V c x π) -
            w • ∑ _x ∈ S, ∑ _π : Equiv.Perm (Fin 4), (1 : ComplexMatrix2) := by
        simp only [Finset.sum_sub_distrib, smul_sub]
      rw [h0, hone, hmean]
    rw [e]
    have h1 : ‖∑ x ∈ S, ∑ π : Equiv.Perm (Fin 4), (contourHolonomy V c x π - 1)‖ ≤
        ∑ _x ∈ S, ∑ _π : Equiv.Perm (Fin 4), ((1 + ρ) ^ (5 * L) - 1) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x hx => ?_)
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun π _ => hcv x hx π)
    have h2 : ∑ _x ∈ S, ∑ _π : Equiv.Perm (Fin 4), ((1 + ρ) ^ (5 * L) - 1) =
        (24 * (L : ℝ) ^ 4) * ((1 + ρ) ^ (5 * L) - 1) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, hScard,
        nsmul_eq_mul]
      push_cast
      norm_num [Nat.factorial]
      ring
    rw [h2] at h1
    calc ‖w • ∑ x ∈ S, ∑ π : Equiv.Perm (Fin 4), (contourHolonomy V c x π - 1)‖
        ≤ ‖w‖ * ‖∑ x ∈ S, ∑ π : Equiv.Perm (Fin 4), (contourHolonomy V c x π - 1)‖ :=
          norm_smul_le _ _
      _ ≤ ‖w‖ * ((24 * (L : ℝ) ^ 4) * ((1 + ρ) ^ (5 * L) - 1)) := by gcongr
      _ = (1 + ρ) ^ (5 * L) - 1 := by
          rw [hwnorm]; field_simp
      _ ≤ 1 / 100 := hε
  set W := contourMean V c with hWdef
  set E := W - 1 with hE
  have hentry : ∀ a b, ‖E a b‖ ≤ 1 / 100 := fun a b => (norm_entry_le_operatorNorm E a b).trans hW
  have hdet : ‖Matrix.det W - 1‖ ≤ 3 / 100 := by
    have e00 : W 0 0 = 1 + E 0 0 := by simp [hE]
    have e11 : W 1 1 = 1 + E 1 1 := by simp [hE]
    have e01 : W 0 1 = E 0 1 := by simp [hE]
    have e10 : W 1 0 = E 1 0 := by simp [hE]
    have e : Matrix.det W - 1 = E 0 0 + E 1 1 + E 0 0 * E 1 1 - E 0 1 * E 1 0 := by
      rw [Matrix.det_fin_two, e00, e11, e01, e10]
      ring
    rw [e]
    have a1 := hentry 0 0
    have a2 := hentry 1 1
    have a3 := hentry 0 1
    have a4 := hentry 1 0
    have m1 : ‖E 0 0 * E 1 1‖ ≤ 1 / 100 * (1 / 100) := by
      rw [norm_mul]; exact mul_le_mul a1 a2 (norm_nonneg _) (by norm_num)
    have m2 : ‖E 0 1 * E 1 0‖ ≤ 1 / 100 * (1 / 100) := by
      rw [norm_mul]; exact mul_le_mul a3 a4 (norm_nonneg _) (by norm_num)
    calc ‖E 0 0 + E 1 1 + E 0 0 * E 1 1 - E 0 1 * E 1 0‖
        ≤ ‖E 0 0 + E 1 1 + E 0 0 * E 1 1‖ + ‖E 0 1 * E 1 0‖ := norm_sub_le _ _
      _ ≤ ‖E 0 0‖ + ‖E 1 1‖ + ‖E 0 0 * E 1 1‖ + ‖E 0 1 * E 1 0‖ := by
          gcongr; exact norm_add₃_le
      _ ≤ 3 / 100 := by linarith
  obtain ⟨hr0, hrsq, hrnear, hslit⟩ := sqrt_near_one (Matrix.det W) (by linarith)
  have hlen : meanRadius V c = (Matrix.det W) ^ (1 / 2 : ℂ) := rfl
  set r := (Matrix.det W) ^ (1 / 2 : ℂ) with hr
  have hav : normalizedMean V c = r⁻¹ • W := by
    rw [normalizedMean, hlen]
  have hrclose : ‖r - 1‖ ≤ 3 / 100 := hrnear.trans hdet
  have hrnorm : 1 / 2 ≤ ‖r‖ := by
    have h1 : ‖(1 : ℂ)‖ ≤ ‖r‖ + ‖r - 1‖ := by
      have := norm_sub_le r (r - 1)
      simpa using this
    simp at h1
    linarith
  have hrinv : ‖r⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    exact inv_le_of_inv_le₀ (by norm_num) (by norm_num; linarith)
  have hu : ComplexMatrix2.operatorNorm (normalizedMean V c - 1) < 1 / 2 := by
    have e : normalizedMean V c - 1 = r⁻¹ • (E + (1 - r) • (1 : ComplexMatrix2)) := by
      rw [hav, smul_add, smul_smul, hE]
      have h1 : r⁻¹ * (1 - r) = r⁻¹ - 1 := by field_simp
      rw [h1, sub_smul, smul_sub, one_smul]
      abel
    rw [ComplexMatrix2.operatorNorm, e]
    have h1 : ‖E + (1 - r) • (1 : ComplexMatrix2)‖ ≤ 1 / 100 + 3 / 100 := by
      refine (norm_add_le _ _).trans (add_le_add hW ?_)
      refine (norm_smul_le _ _).trans ?_
      rw [norm_one, mul_one, norm_sub_rev]
      exact hrclose
    calc ‖r⁻¹ • (E + (1 - r) • (1 : ComplexMatrix2))‖
        ≤ ‖r⁻¹‖ * ‖E + (1 - r) • (1 : ComplexMatrix2)‖ := norm_smul_le _ _
      _ ≤ 2 * (1 / 100 + 3 / 100) := by gcongr
      _ < 1 / 2 := by norm_num
  have hudet : normalizedMean V c ∈ PeriodicLattice.complexGaugeGroup := by
    change Matrix.det (normalizedMean V c) = 1
    rw [hav, Matrix.det_smul, Fintype.card_fin, inv_pow, hrsq, inv_mul_cancel₀]
    intro h0
    exact hr0 (by rw [hr]; rw [h0]; simp)
  refine ⟨S, w, hmean, hlen ▸ hr0, ?_, hu, hudet, hslit⟩
  rw [hlen]
  linarith

theorem contourMeanComplexDerivative_holds
    (hd : ComplexMatrix2.PointwiseDerivativeRules.RealAndComplex)
    (hcf : PeriodicLattice.BlockContoursAndCombs)
    (hbb : PeriodicLattice.BlocksBoxesPaths.Statement)
    (hb : PeriodicLattice.CrossingsAndBareBlocks.Statement) :
    RunningCouplingSlope.ContourMeanComplexDerivative := by
  intro L hL
  obtain ⟨ρ, hρ, hnear⟩ := ContourMeanDerivative.contourMean_near_one hcf hbb hb L hL
  refine ⟨ρ, hρ, ?_⟩
  intro n k j hn hj V hV hVρ c hc
  obtain ⟨S, w, hmean, hr0, hrclose, hu, hudet, hslit⟩ := hnear n k j hn hj V hV hVρ c hc
  have hdetV : ∀ b, Matrix.det (V b) = 1 := fun b => hV.1 b (Set.mem_univ b)
  have hinvhol : ∀ l : List (Edge L n k j), PeriodicLattice.pathHolonomy V l =
      (l.map V).prod := fun _ => rfl
  have hhol : ∀ l : List (Edge L n k j), ∃ T,
      HasLinearDerivAlongCurves V (fun U => PeriodicLattice.pathHolonomy U l) T :=
    fun l => exists_hasLinearDerivAlongCurves_list_prod l
  have hcvd : ∀ x π, ∃ T, HasLinearDerivAlongCurves V (fun U => contourHolonomy U c x π) T := by
    intro x π
    obtain ⟨D₁, h₁⟩ := hhol (contourLeg c.source x π)
    obtain ⟨D₂, h₂⟩ := hhol (PeriodicLattice.crossingPath c x)
    obtain ⟨D₃, h₃⟩ := hhol (contourLeg c.target (PeriodicLattice.shiftAcross c x) π)
    have hu3 : IsUnit (Matrix.det (PeriodicLattice.pathHolonomy V
        (contourLeg c.target (PeriodicLattice.shiftAcross c x) π))) := by
      rw [hinvhol, det_list_prod_eq_one V hdetV]
      exact isUnit_one
    exact ⟨_, hasLinearDerivAlongCurves_mul (hasLinearDerivAlongCurves_mul h₁ h₂)
      (hasLinearDerivAlongCurves_inv hd h₃ hu3)⟩
  choose Dc hDc using hcvd
  have hM : HasLinearDerivAlongCurves V (fun U => contourMean U c)
      (w • ∑ x ∈ S, ∑ π : Equiv.Perm (Fin 4), Dc x π) := by
    have h1 := hasLinearDerivAlongCurves_const_smul w (hasLinearDerivAlongCurves_sum S fun x _ =>
      hasLinearDerivAlongCurves_sum Finset.univ fun π _ => hDc x π)
    intro g γ h0 hγ
    have h2 := h1 g γ h0 hγ
    have e : (fun t => contourMean (γ t) c) = fun t => w • ∑ x ∈ S,
        ∑ π : Equiv.Perm (Fin 4), contourHolonomy (γ t) c x π := by
      funext t
      exact hmean _
    rw [e]
    exact h2
  obtain ⟨Dd, hDd⟩ := exists_hasLinearDerivAlongCurves_det hM
  obtain ⟨Dr, hDr⟩ := exists_hasLinearDerivAlongCurves_sqrt hDd hslit
  obtain ⟨Du, hDu⟩ := exists_hasLinearDerivAlongCurves_inv_smul hDr hM hr0
  refine ⟨Du, fun g γ h0 hγ => ?_⟩
  exact hDu g γ h0 hγ
end YangMills.Construction.RunningCouplingSlope.ContourMeanDerivative
end
