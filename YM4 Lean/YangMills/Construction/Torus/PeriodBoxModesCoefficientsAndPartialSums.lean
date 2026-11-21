import YangMills.Construction.Torus.FunctionsOfSeveralPointsOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
open Set
open scoped ComplexConjugate ContDiff
noncomputable section
namespace YangMills.Construction.Torus.FourierBox
open AmbientPoints Conventions TorusMetric
section Box
variable (s : StandingParameters)
def coord (μ : Fin 4) : Pt s .euclidean → ℝ := fun x : Fin 4 → ℝ => x μ
theorem continuous_coord (μ : Fin 4) : Continuous (coord s μ) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun a b => ?_).continuous
  have hab : dist a b = euclidNormVec (fun ν => coord s ν a - coord s ν b) :=
    rfl
  rw [hab, NNReal.coe_one, one_mul, Real.dist_eq]
  refine Real.abs_le_sqrt ?_
  exact Finset.single_le_sum
    (f := fun ν => (coord s ν a - coord s ν b) ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ μ)
def fundamentalBox (L : ℝ) : Set (Pt s .euclidean) :=
  {x | ∀ μ, coord s μ x ∈ Ioo (-L / 2) (L / 2)}
def fundamentalBoxPow (n : ℕ) (L : ℝ) : Set (Tuple s .euclidean n) :=
  {y | ∀ i, y i ∈ fundamentalBox s L}
theorem isOpen_fundamentalBox (L : ℝ) : IsOpen (fundamentalBox s L) := by
  have h : fundamentalBox s L = ⋂ μ, coord s μ ⁻¹' Ioo (-L / 2) (L / 2) := by
    ext x
    simp [fundamentalBox]
  rw [h]
  exact isOpen_iInter_of_finite fun μ => isOpen_Ioo.preimage (continuous_coord s μ)
theorem isOpen_fundamentalBoxPow (n : ℕ) (L : ℝ) : IsOpen (fundamentalBoxPow s n L) := by
  have h : fundamentalBoxPow s n L = Set.pi univ fun _ => fundamentalBox s L := by
    ext y
    simp [fundamentalBoxPow]
  rw [h]
  exact isOpen_set_pi finite_univ fun _ _ => isOpen_fundamentalBox s L
end Box
def fundamentalCube (N : ℕ) (L : ℝ) : Set (Fin N → ℝ) := {x | ∀ j, x j ∈ Ioo (-L / 2) (L / 2)}
theorem flattenCoords_symm_apply {n : ℕ} (x : Fin (4 * n) → ℝ) (i : Fin n) (μ : Fin 4)
    (h : 4 * (i : ℕ) + μ < 4 * n) : (flattenCoords n).symm x i μ = x ⟨4 * i + μ, h⟩ := by
  have := flattenCoords_apply ((flattenCoords n).symm x) i μ h
  rw [Equiv.apply_symm_apply] at this
  exact this.symm
theorem tupleProj_mem_fundamentalBoxPow_iff (s : StandingParameters) (n : ℕ) (L : ℝ)
    (x : Fin (4 * n) → ℝ) :
    tupleProj s .euclidean n x ∈ fundamentalBoxPow s n L ↔ x ∈ fundamentalCube (4 * n) L := by
  constructor
  · intro h j
    have hj := j.2
    have hi : (j : ℕ) / 4 < n := by omega
    have hμ : (j : ℕ) % 4 < 4 := by omega
    have hh : 4 * (((⟨(j : ℕ) / 4, hi⟩ : Fin n) : ℕ)) + ((⟨(j : ℕ) % 4, hμ⟩ : Fin 4) : ℕ) < 4 * n := by
      simp only
      omega
    have := h ⟨(j : ℕ) / 4, hi⟩ ⟨(j : ℕ) % 4, hμ⟩
    have hc : coord s ⟨(j : ℕ) % 4, hμ⟩
        (tupleProj s .euclidean n x ⟨(j : ℕ) / 4, hi⟩) = x j := by
      refine (flattenCoords_symm_apply x _ _ hh).trans (congrArg x (Fin.ext ?_))
      simp only
      omega
    rwa [hc] at this
  · intro h i μ
    have hh : 4 * (i : ℕ) + μ < 4 * n := by
      have := i.2
      have := μ.2
      omega
    have hc : coord s μ (tupleProj s .euclidean n x i) = x ⟨4 * i + μ, hh⟩ :=
      flattenCoords_symm_apply x i μ hh
    rw [hc]
    exact h _
section Modes
variable {N : ℕ}
def intDot (m : Fin N → ℤ) (x : Fin N → ℝ) : ℝ := ∑ j, (m j : ℝ) * x j
def fourierMode (L : ℝ) (m : Fin N → ℤ) (x : Fin N → ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (intDot m x : ℂ) / (L : ℂ))
def supNormInt (m : Fin N → ℤ) : ℕ := Finset.univ.sup fun j => (m j).natAbs
theorem isGreatest_supNormInt (hN : 1 ≤ N) (m : Fin N → ℤ) :
    IsGreatest (range fun j => (m j).natAbs) (supNormInt m) := by
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup Finset.univ hne fun j => (m j).natAbs
  refine ⟨⟨j, hj.symm⟩, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact Finset.le_sup (f := fun j => (m j).natAbs) (Finset.mem_univ i)
def modesWithin (r : ℕ) : Finset (Fin N → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(r : ℤ)) (r : ℤ)
theorem mem_modesWithin (r : ℕ) (m : Fin N → ℤ) : m ∈ modesWithin r ↔ supNormInt m ≤ r := by
  simp only [modesWithin, supNormInt, Fintype.mem_piFinset, Finset.mem_Icc, Finset.sup_le_iff,
    Finset.mem_univ, true_implies]
  exact forall_congr' fun j => by omega
theorem continuousPartialsUpTo_of_contDiff (n : ℕ) :
    ∀ {g : (Fin N → ℝ) → ℂ}, ContDiff ℝ ∞ g → ContinuousPartialsUpTo univ n g := by
  induction n with
  | zero => exact fun hg => hg.continuous.continuousOn
  | succ n ih =>
    intro g hg
    have hd : Differentiable ℝ g := hg.differentiable (by simp)
    refine ⟨hg.continuous.continuousOn, fun j => ⟨fun x _ => (hd x).lineDifferentiableAt, ih ?_⟩⟩
    have he : partialDeriv j g = fun x => fderiv ℝ g x (Pi.single j 1) :=
      funext fun x => (hd x).lineDeriv_eq_fderiv
    rw [he]
    exact (hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
theorem contDiff_fourierMode (L : ℝ) (m : Fin N → ℤ) : ContDiff ℝ ∞ (fourierMode L m) := by
  have hs : ContDiff ℝ ∞ (intDot m) := by
    unfold intDot
    exact ContDiff.sum fun j _ => contDiff_const.mul (contDiff_apply ℝ ℝ j)
  have hc : ContDiff ℝ ∞ fun x => (intDot m x : ℂ) :=
    Complex.ofRealCLM.contDiff.comp hs
  exact ((contDiff_const.mul hc).div_const _).cexp
end Modes
def blockOf {n : ℕ} (m : Fin (4 * n) → ℤ) (i : Fin n) : Fin 4 → ℤ :=
  fun μ => m ⟨4 * (i : ℕ) + (μ : ℕ), by have := i.2; have := μ.2; omega⟩
def euclidNormInt (κ : Fin 4 → ℤ) : ℝ := euclidNormVec fun μ => (κ μ : ℝ)
theorem intDot_eq_sum_blocks {n : ℕ} (m : Fin (4 * n) → ℤ) (x : Fin (4 * n) → ℝ) :
    intDot m x =
      ∑ i, intDot (blockOf m i) ((flattenCoords n).symm x i) := by
  let e : Fin n × Fin 4 ≃ Fin (4 * n) := finProdFinEquiv.trans (finCongr (Nat.mul_comm n 4))
  have he : ∀ (i : Fin n) (μ : Fin 4), (e (i, μ) : ℕ) = 4 * (i : ℕ) + μ := by
    intro i μ
    simp [e, finProdFinEquiv, Nat.add_comm]
  unfold intDot
  rw [← e.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun μ _ => ?_
  have hh : 4 * (i : ℕ) + μ < 4 * n := he i μ ▸ (e (i, μ)).2
  have hidx : e (i, μ) = ⟨4 * (i : ℕ) + μ, hh⟩ := Fin.ext (he i μ)
  rw [flattenCoords_symm_apply x i μ hh, hidx]
  rfl
theorem fourierMode_eq_tensorProd (s : StandingParameters) {n : ℕ} (L : ℝ) (m : Fin (4 * n) → ℤ)
    (x : Fin (4 * n) → ℝ) :
    fourierMode L m x =
      tensorProd (s := s) (E := .euclidean) (fun i => fourierMode L (blockOf m i))
        (tupleProj s .euclidean n x) := by
  have hterm : ∀ i, fourierMode L (blockOf m i) ((flattenCoords n).symm x i) =
      Complex.exp (2 * Real.pi * Complex.I *
        (intDot (blockOf m i) ((flattenCoords n).symm x i) : ℂ) / (L : ℂ)) :=
    fun _ => rfl
  change fourierMode L m x = ∏ i, fourierMode L (blockOf m i) ((flattenCoords n).symm x i)
  simp only [hterm]
  rw [← Complex.exp_sum, fourierMode, intDot_eq_sum_blocks, Complex.ofReal_sum,
    Finset.mul_sum, Finset.sum_div]
section Coefficients
variable {s : StandingParameters} {n : ℕ}
def fourierCoeff (L : ℝ) (f : Tuple s .euclidean n → ℂ) (m : Fin (4 * n) → ℤ) : ℂ :=
  ((L : ℂ) ^ (4 * n))⁻¹ *
    ∫ x in fundamentalCube (4 * n) L, f (tupleProj s .euclidean n x) * conj (fourierMode L m x)
def fourierPartialSum (L : ℝ) (f : Tuple s .euclidean n → ℂ) (r : ℕ+) : (Fin (4 * n) → ℝ) → ℂ :=
  fun x => ∑ m ∈ modesWithin (r : ℕ), fourierCoeff L f m * fourierMode L m x
theorem isCnOn_fourierPartialSum (L : ℝ) (f : Tuple s .euclidean n → ℂ) (r : ℕ+) :
    IsCnOn univ ⊤ (fourierPartialSum L f r) := by
  have h : ContDiff ℝ ∞ (fourierPartialSum L f r) := by
    unfold fourierPartialSum
    exact ContDiff.sum fun m _ => contDiff_const.mul (contDiff_fourierMode L m)
  exact ⟨isOpen_univ, fun k _ => continuousPartialsUpTo_of_contDiff k h⟩
end Coefficients
end YangMills.Construction.Torus.FourierBox
