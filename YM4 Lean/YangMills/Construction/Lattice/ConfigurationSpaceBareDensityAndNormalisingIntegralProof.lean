import YangMills.Construction.InfiniteLattice.FactsFromTopologyMeasureAndFunctionTheoryProof
import YangMills.Construction.Lattice.CompactGaugeFieldSpaceAndPartitionBounds
import YangMills.Construction.Lattice.LatticesCubesOfAStandardPartitionAndEnlargements
import YangMills.Construction.Lattice.OppositeBondsAndPositiveValues
import YangMills.Construction.Lattice.PlaquetteHolonomyTrace
import YangMills.Construction.Lattice.WilsonActionAsAPlaquetteSumAndSymmetriesOfProductHaarProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexConjugate
open YangMills.Construction.Matrices YangMills.Construction.Coordinates
noncomputable section
namespace YangMills.Construction.PeriodicLattice.GaugeFieldSpace
def suMatrix (a c : ℂ) : ComplexMatrix2 := !![a, -conj c; c, conj a]
theorem suMatrix_zero_zero (a c : ℂ) : suMatrix a c 0 0 = a := by
  simp [suMatrix]
theorem suMatrix_one_zero (a c : ℂ) : suMatrix a c 1 0 = c := by
  simp [suMatrix]
theorem suMatrix_mul (a c a' c' : ℂ) :
    suMatrix a c * suMatrix a' c' =
      suMatrix (a * a' - conj c * c') (c * a' + conj a * c') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
theorem star_suMatrix (a c : ℂ) :
    star (suMatrix a c) = suMatrix (conj a) (-c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suMatrix, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
theorem suMatrix_sub (a c a' c' : ℂ) :
    suMatrix a c - suMatrix a' c' = suMatrix (a - a') (c - c') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [suMatrix] <;> ring
theorem suMatrix_add (a c a' c' : ℂ) :
    suMatrix a c + suMatrix a' c' = suMatrix (a + a') (c + c') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [suMatrix] <;> ring
theorem suMatrix_one : suMatrix 1 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [suMatrix]
theorem suMatrix_smul (r : ℝ) (a c : ℂ) :
    (r : ℂ) • suMatrix a c = suMatrix (r * a) (r * c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [suMatrix]
theorem suMatrix_mem_specialUnitary {a c : ℂ} (h : Complex.normSq a + Complex.normSq c = 1) :
    suMatrix a c ∈ ComplexMatrix2.specialUnitary := by
  have hc : ((Complex.normSq a : ℂ) + (Complex.normSq c : ℂ)) = 1 := by exact_mod_cast h
  refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨Matrix.mem_unitaryGroup_iff.mpr ?_, ?_⟩
  · rw [star_suMatrix, suMatrix_mul, ← suMatrix_one]
    congr 1
    · rw [Complex.mul_conj, mul_neg, sub_neg_eq_add, mul_comm (conj c), Complex.mul_conj, hc]
    · simp [mul_comm]
  · rw [Matrix.det_fin_two]
    simp only [suMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [Complex.mul_conj, ← hc, ← Complex.mul_conj c]
    ring
theorem eq_suMatrix (u : ComplexMatrix2.specialUnitary) :
    u.1 = suMatrix (u.1 0 0) (u.1 1 0) ∧
      Complex.normSq (u.1 0 0) + Complex.normSq (u.1 1 0) = 1 := by
  obtain ⟨hu, hd⟩ := Matrix.mem_specialUnitaryGroup_iff.mp u.2
  have h1 : star u.1 * u.1 = 1 := Matrix.mem_unitaryGroup_iff'.mp hu
  have h2 : u.1 * Matrix.adjugate u.1 = 1 := by rw [Matrix.mul_adjugate, hd, one_smul]
  have h3 : star u.1 = Matrix.adjugate u.1 := left_inv_eq_right_inv h1 h2
  rw [Matrix.adjugate_fin_two] at h3
  have e00 := congrFun (congrFun h3 0) 0
  have e01 := congrFun (congrFun h3 0) 1
  simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply] at e00 e01
  rw [Matrix.det_fin_two] at hd
  have hm : u.1 = suMatrix (u.1 0 0) (u.1 1 0) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [suMatrix, e00, e01]
  refine ⟨hm, ?_⟩
  have : ((Complex.normSq (u.1 0 0) + Complex.normSq (u.1 1 0) : ℝ) : ℂ) = 1 := by
    push_cast
    rw [← Complex.mul_conj, ← Complex.mul_conj, ← hd, e00, e01]
    simp only [star, mul_neg, neg_mul]
    ring
  exact_mod_cast this
def traceHalf (u : ComplexMatrix2.specialUnitary) : ℝ := (u.1 0 0).re
theorem traceHalf_eq_re_trace_div_two (u : ComplexMatrix2.specialUnitary) :
    traceHalf u = (Matrix.trace u.1).re / 2 := by
  have hm := (eq_suMatrix u).1
  have : Matrix.trace u.1 = u.1 0 0 + conj (u.1 0 0) := by
    conv_lhs => rw [hm]
    simp [Matrix.trace, Fin.sum_univ_two, suMatrix]
  rw [this, traceHalf]
  simp
theorem coe_inv_eq_star (u : ComplexMatrix2.specialUnitary) :
    ((u⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) = star u.1 := rfl
theorem traceHalf_conj (y u : ComplexMatrix2.specialUnitary) :
    traceHalf (y * u * y⁻¹) = traceHalf u := by
  rw [traceHalf_eq_re_trace_div_two, traceHalf_eq_re_trace_div_two]
  have : ((y * u * y⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) =
      y.1 * u.1 * ((y⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) := rfl
  rw [this, Matrix.trace_mul_comm, ← mul_assoc]
  have h : ((y⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) * y.1 = 1 := by
    have := congrArg Subtype.val (inv_mul_cancel y)
    exact this
  rw [h, one_mul]
theorem traceHalf_le_one (u : ComplexMatrix2.specialUnitary) : traceHalf u ≤ 1 := by
  have h := (eq_suMatrix u).2
  have h1 : (u.1 0 0).re ^ 2 ≤ Complex.normSq (u.1 0 0) := by
    rw [Complex.normSq_apply]; nlinarith [mul_self_nonneg (u.1 0 0).im]
  have h2 := Complex.normSq_nonneg (u.1 1 0)
  rw [traceHalf]
  nlinarith
theorem neg_one_le_traceHalf (u : ComplexMatrix2.specialUnitary) : -1 ≤ traceHalf u := by
  have h := (eq_suMatrix u).2
  have h1 : (u.1 0 0).re ^ 2 ≤ Complex.normSq (u.1 0 0) := by
    rw [Complex.normSq_apply]; nlinarith [mul_self_nonneg (u.1 0 0).im]
  have h2 := Complex.normSq_nonneg (u.1 1 0)
  rw [traceHalf]
  nlinarith
theorem add_star_eq_suMatrix (u : ComplexMatrix2.specialUnitary) :
    u.1 + star u.1 = suMatrix ((2 * traceHalf u : ℝ)) 0 := by
  have hm := (eq_suMatrix u).1
  conv_lhs => rw [hm, star_suMatrix, suMatrix_add]
  congr 1
  · rw [Complex.add_conj]
    simp [traceHalf]
  · simp
theorem exists_conj_or_eq_inv_of_traceHalf_eq (u u₁ : ComplexMatrix2.specialUnitary)
    (h : traceHalf u = traceHalf u₁) :
    (∃ y : ComplexMatrix2.specialUnitary, u = y * u₁ * y⁻¹) ∨ u = u₁⁻¹ := by
  have hsum : u.1 + star u.1 = u₁.1 + star u₁.1 := by
    rw [add_star_eq_suMatrix, add_star_eq_suMatrix, h]
  set y₀ : ComplexMatrix2 := u.1 - star u₁.1 with hy₀
  have hy₁ : y₀ = u₁.1 - star u.1 := by
    rw [hy₀, sub_eq_sub_iff_add_eq_add]
    exact hsum
  have huu : u.1 * star u.1 = 1 :=
    Matrix.mem_unitaryGroup_iff.mp (Matrix.specialUnitaryGroup_le_unitaryGroup u.2)
  have huu₁ : star u₁.1 * u₁.1 = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (Matrix.specialUnitaryGroup_le_unitaryGroup u₁.2)
  have hcomm : u.1 * y₀ = y₀ * u₁.1 := by
    calc u.1 * y₀ = u.1 * (u₁.1 - star u.1) := by rw [hy₁]
      _ = u.1 * u₁.1 - 1 := by rw [mul_sub, huu]
      _ = (u.1 - star u₁.1) * u₁.1 := by rw [sub_mul, huu₁]
  obtain ⟨α, γ, hαγ⟩ : ∃ α γ : ℂ, y₀ = suMatrix α γ := by
    refine ⟨u.1 0 0 - conj (u₁.1 0 0), u.1 1 0 - -(u₁.1 1 0), ?_⟩
    rw [hy₀, ← suMatrix_sub, ← star_suMatrix, ← (eq_suMatrix u).1,
      ← (eq_suMatrix u₁).1]
  by_cases hs : Complex.normSq α + Complex.normSq γ = 0
  · right
    have hα : α = 0 := by
      have := Complex.normSq_nonneg α
      have := Complex.normSq_nonneg γ
      exact Complex.normSq_eq_zero.mp (by linarith)
    have hγ : γ = 0 := by
      have := Complex.normSq_nonneg α
      have := Complex.normSq_nonneg γ
      exact Complex.normSq_eq_zero.mp (by linarith)
    have h0 : y₀ = 0 := by
      rw [hαγ, hα, hγ]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [suMatrix]
    apply Subtype.ext
    rw [coe_inv_eq_star]
    exact sub_eq_zero.mp (hy₀ ▸ h0)
  · left
    have hpos : 0 < Complex.normSq α + Complex.normSq γ :=
      lt_of_le_of_ne (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)) (Ne.symm hs)
    set r : ℝ := (Real.sqrt (Complex.normSq α + Complex.normSq γ))⁻¹ with hr
    have hr2 : r ^ 2 * (Complex.normSq α + Complex.normSq γ) = 1 := by
      rw [hr, inv_pow, Real.sq_sqrt hpos.le]
      exact inv_mul_cancel₀ hs
    have hmem : suMatrix (r * α) (r * γ) ∈ ComplexMatrix2.specialUnitary := by
      apply suMatrix_mem_specialUnitary
      simp only [Complex.normSq_mul, Complex.normSq_ofReal]
      nlinarith
    have hy : (r : ℂ) • y₀ = suMatrix (r * α) (r * γ) := by
      rw [hαγ, suMatrix_smul]
    refine ⟨⟨_, hmem⟩, ?_⟩
    apply eq_mul_inv_of_mul_eq
    apply Subtype.ext
    show u.1 * suMatrix (r * α) (r * γ) = suMatrix (r * α) (r * γ) * u₁.1
    rw [← hy, Matrix.mul_smul, Matrix.smul_mul, hcomm]
def halfAngleRoot (c : ℝ) : ℂ := ⟨Real.sqrt ((1 + c) / 2), Real.sqrt ((1 - c) / 2)⟩
theorem halfAngleRoot_normSq {c : ℝ} (h₁ : -1 ≤ c) (h₂ : c ≤ 1) :
    Complex.normSq (halfAngleRoot c) = 1 := by
  rw [Complex.normSq_apply]
  simp only [halfAngleRoot]
  rw [Real.mul_self_sqrt (by linarith), Real.mul_self_sqrt (by linarith)]
  ring
theorem halfAngleRoot_sq_re {c : ℝ} (h₁ : -1 ≤ c) (h₂ : c ≤ 1) :
    (halfAngleRoot c ^ 2).re = c := by
  rw [sq, Complex.mul_re]
  simp only [halfAngleRoot]
  rw [Real.mul_self_sqrt (by linarith), Real.mul_self_sqrt (by linarith)]
  ring
def diagRotation (c : ℝ) (h₁ : -1 ≤ c) (h₂ : c ≤ 1) : ComplexMatrix2.specialUnitary :=
  ⟨suMatrix (halfAngleRoot c) 0,
    suMatrix_mem_specialUnitary (by rw [halfAngleRoot_normSq h₁ h₂]; simp)⟩
theorem traceHalf_diagRotation_commutator (c : ℝ) (h₁ : -1 ≤ c) (h₂ : c ≤ 1)
    (v : ComplexMatrix2.specialUnitary) :
    traceHalf (diagRotation c h₁ h₂ * v * (diagRotation c h₁ h₂)⁻¹ * v⁻¹) =
      1 - (1 - c) * Complex.normSq (v.1 1 0) := by
  obtain ⟨hv, hn⟩ := eq_suMatrix v
  set α := v.1 0 0 with hα
  set γ := v.1 1 0 with hγ
  set ζ := halfAngleRoot c with hζ
  have hcoe : ((diagRotation c h₁ h₂ * v * (diagRotation c h₁ h₂)⁻¹ * v⁻¹ :
      ComplexMatrix2.specialUnitary) : ComplexMatrix2) =
      suMatrix ζ 0 * suMatrix α γ * star (suMatrix ζ 0) * star (suMatrix α γ) := by
    rw [← hv]
    rfl
  have hζ1 : ζ * conj ζ = 1 := by
    rw [Complex.mul_conj, hζ, halfAngleRoot_normSq h₁ h₂]; simp
  have hentry : (suMatrix ζ 0 * suMatrix α γ * star (suMatrix ζ 0) *
      star (suMatrix α γ)) 0 0 =
      (Complex.normSq α : ℂ) + ζ ^ 2 * (Complex.normSq γ : ℂ) := by
    simp only [star_suMatrix, suMatrix_mul, suMatrix_zero_zero]
    rw [← Complex.mul_conj α, ← Complex.mul_conj γ]
    simp only [map_zero, map_mul, map_sub, map_add, Complex.conj_conj, zero_mul, mul_zero, sub_zero,
      add_zero, zero_add, map_neg]
    linear_combination (α * conj α) * hζ1
  rw [traceHalf, hcoe, hentry]
  rw [Complex.add_re, Complex.ofReal_re, Complex.re_mul_ofReal, hζ, halfAngleRoot_sq_re h₁ h₂]
  linarith
theorem traceHalf_superlevel_eq_range (c : ℝ) (h₁ : -1 ≤ c) (h₂ : c < 1) :
    ∃ e : ComplexMatrix2.specialUnitary, {u | c ≤ traceHalf u} =
      range fun p : ComplexMatrix2.specialUnitary × ComplexMatrix2.specialUnitary =>
        p.1 * e * p.1⁻¹ * p.2 * e⁻¹ * p.2⁻¹ := by
  refine ⟨diagRotation c h₁ h₂.le, ?_⟩
  set e := diagRotation c h₁ h₂.le with he
  ext u
  constructor
  · intro hu
    have hu' : c ≤ traceHalf u := hu
    have hu1 := traceHalf_le_one u
    set q : ℝ := (1 - traceHalf u) / (1 - c) with hq
    have hc1 : 0 < 1 - c := by linarith
    have hq0 : 0 ≤ q := div_nonneg (by linarith) hc1.le
    have hq1 : q ≤ 1 := (div_le_one hc1).mpr (by linarith)
    have hqc : (1 - c) * q = 1 - traceHalf u := by rw [hq]; field_simp
    have hvm : suMatrix ((Real.sqrt (1 - q) : ℝ)) ((Real.sqrt q : ℝ)) ∈
        ComplexMatrix2.specialUnitary := by
      apply suMatrix_mem_specialUnitary
      rw [Complex.normSq_ofReal, Complex.normSq_ofReal, Real.mul_self_sqrt (by linarith),
        Real.mul_self_sqrt hq0]
      ring
    set v : ComplexMatrix2.specialUnitary := ⟨_, hvm⟩ with hv
    have hγ : Complex.normSq (v.1 1 0) = q := by
      show Complex.normSq (suMatrix _ _ 1 0) = q
      rw [suMatrix_one_zero, Complex.normSq_ofReal, Real.mul_self_sqrt hq0]
    have ht : traceHalf u = traceHalf (e * v * e⁻¹ * v⁻¹) := by
      rw [he, traceHalf_diagRotation_commutator, hγ, hqc]
      ring
    rcases exists_conj_or_eq_inv_of_traceHalf_eq _ _ ht with ⟨y, hy⟩ | hy
    · refine ⟨(y, y * v), ?_⟩
      simp only
      rw [hy]
      group
    · refine ⟨(v, 1), ?_⟩
      simp only
      rw [hy]
      group
  · rintro ⟨⟨y, y₁⟩, rfl⟩
    have hrew : y * e * y⁻¹ * y₁ * e⁻¹ * y₁⁻¹ =
        y * (e * (y⁻¹ * y₁) * e⁻¹ * (y⁻¹ * y₁)⁻¹) * y⁻¹ := by group
    show c ≤ traceHalf (y * e * y⁻¹ * y₁ * e⁻¹ * y₁⁻¹)
    rw [hrew, traceHalf_conj, he, traceHalf_diagRotation_commutator]
    have hn := (eq_suMatrix (y⁻¹ * y₁)).2
    have := Complex.normSq_nonneg (((y⁻¹ * y₁ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) 0 0)
    nlinarith
theorem eq_one_of_one_le_traceHalf (u : ComplexMatrix2.specialUnitary) (h : 1 ≤ traceHalf u) :
    u = 1 := by
  obtain ⟨hm, hn⟩ := eq_suMatrix u
  have h1 := traceHalf_le_one u
  have hre : (u.1 0 0).re = 1 := le_antisymm h1 h
  rw [Complex.normSq_apply, hre] at hn
  have h2 := Complex.normSq_nonneg (u.1 1 0)
  have him : (u.1 0 0).im = 0 := by nlinarith [mul_self_nonneg (u.1 0 0).im]
  have hc : Complex.normSq (u.1 1 0) = 0 := by nlinarith [mul_self_nonneg (u.1 0 0).im]
  have ha : u.1 0 0 = 1 := Complex.ext (by simpa using hre) (by simpa using him)
  apply Subtype.ext
  show u.1 = 1
  rw [hm, ha, Complex.normSq_eq_zero.mp hc, suMatrix_one]
theorem traceHalf_mul_suMatrix (u : ComplexMatrix2.specialUnitary) {a c : ℂ}
    (hm : suMatrix a c ∈ ComplexMatrix2.specialUnitary) :
    traceHalf (u * ⟨_, hm⟩) = (u.1 0 0 * a - conj (u.1 1 0) * c).re := by
  show ((u.1 * suMatrix a c) 0 0).re = _
  conv_lhs => rw [(eq_suMatrix u).1, suMatrix_mul, suMatrix_zero_zero]
theorem isClosed_range_conj_mul_conj {H : Type} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [CompactSpace H] [T2Space H] (e : H) :
    IsClosed (range fun p : H × H => p.1 * e * p.1⁻¹ * p.2 * e⁻¹ * p.2⁻¹) := by
  have hc : Continuous fun p : H × H => p.1 * e * p.1⁻¹ * p.2 * e⁻¹ * p.2⁻¹ := by fun_prop
  exact (isCompact_range hc).isClosed
section Uniqueness
variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [T2Space H] (φ : H ≃* ComplexMatrix2.specialUnitary)
include φ in
theorem isClosed_superlevel_traceHalf (c : ℝ) : IsClosed {h : H | c ≤ traceHalf (φ h)} := by
  rcases lt_or_ge c (-1) with hc | hc
  · have : {h : H | c ≤ traceHalf (φ h)} = univ :=
      eq_univ_of_forall fun h => hc.le.trans (neg_one_le_traceHalf _)
    rw [this]
    exact isClosed_univ
  rcases lt_or_ge c 1 with hc1 | hc1
  · obtain ⟨e, he⟩ := traceHalf_superlevel_eq_range c hc hc1
    have : {h : H | c ≤ traceHalf (φ h)} =
        range fun p : H × H => p.1 * φ.symm e * p.1⁻¹ * p.2 * (φ.symm e)⁻¹ * p.2⁻¹ := by
      ext h
      have h' : (c ≤ traceHalf (φ h)) ↔ φ h ∈ {u | c ≤ traceHalf u} := Iff.rfl
      rw [mem_setOf_eq, h', he]
      constructor
      · rintro ⟨⟨y, y₁⟩, hy⟩
        refine ⟨(φ.symm y, φ.symm y₁), ?_⟩
        apply φ.injective
        simpa using hy
      · rintro ⟨⟨y, y₁⟩, rfl⟩
        exact ⟨(φ y, φ y₁), by simp⟩
    rw [this]
    exact isClosed_range_conj_mul_conj _
  · have hone : ∀ k : H, c ≤ traceHalf (φ k) → φ k = 1 := fun k hk =>
      eq_one_of_one_le_traceHalf _ (hc1.trans hk)
    apply Set.Subsingleton.isClosed
    intro h hh h' hh'
    apply φ.injective
    rw [hone h hh, hone h' hh']
include φ in
theorem isClosed_sublevel_traceHalf (a : ℝ) : IsClosed {h : H | traceHalf (φ h) ≤ a} := by
  have hm : suMatrix (-1) 0 ∈ ComplexMatrix2.specialUnitary := suMatrix_mem_specialUnitary (by simp)
  have : {h : H | traceHalf (φ h) ≤ a} =
      (fun h => h * φ.symm ⟨_, hm⟩) ⁻¹' {h : H | -a ≤ traceHalf (φ h)} := by
    ext h
    simp only [mem_setOf_eq, mem_preimage, map_mul, MulEquiv.apply_symm_apply,
      traceHalf_mul_suMatrix]
    simp only [traceHalf, mul_neg, mul_one, mul_zero, sub_zero, Complex.neg_re]
    constructor <;> intro h' <;> linarith
  rw [this]
  exact (isClosed_superlevel_traceHalf φ (-a)).preimage (continuous_mul_right _)
include φ in
theorem continuous_traceHalf_comp : Continuous fun h : H => traceHalf (φ h) := by
  rw [continuous_iff_continuousAt]
  intro x
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · have : IsOpen {h : H | a < traceHalf (φ h)} := by
      have := (isClosed_sublevel_traceHalf φ a).isOpen_compl
      simpa [compl_setOf] using this
    exact this.mem_nhds ha
  · have : IsOpen {h : H | traceHalf (φ h) < a} := by
      have := (isClosed_superlevel_traceHalf φ a).isOpen_compl
      simpa [compl_setOf] using this
    exact this.mem_nhds ha
include φ in
theorem continuous_mulEquiv_specialUnitary : Continuous φ := by
  have key : ∀ (a c : ℂ), suMatrix a c ∈ ComplexMatrix2.specialUnitary →
      Continuous fun h : H => ((φ h).1 0 0 * a - conj ((φ h).1 1 0) * c).re := by
    intro a c hm
    have : (fun h : H => ((φ h).1 0 0 * a - conj ((φ h).1 1 0) * c).re) =
        (fun k : H => traceHalf (φ k)) ∘ fun h => h * φ.symm ⟨_, hm⟩ := by
      funext h
      simp only [Function.comp, map_mul, MulEquiv.apply_symm_apply, traceHalf_mul_suMatrix]
    rw [this]
    exact (continuous_traceHalf_comp φ).comp (continuous_mul_right _)
  have h₁ := key 1 0 (suMatrix_mem_specialUnitary (by simp))
  have h₂ := key Complex.I 0 (suMatrix_mem_specialUnitary (by simp))
  have h₃ := key 0 1 (suMatrix_mem_specialUnitary (by simp))
  have h₄ := key 0 Complex.I (suMatrix_mem_specialUnitary (by simp))
  simp only [mul_one, mul_zero, sub_zero, zero_sub, Complex.neg_re, Complex.mul_I_re,
    Complex.conj_im, neg_neg, Complex.conj_re] at h₁ h₂ h₃ h₄
  have ha : Continuous fun h : H => (φ h).1 0 0 := by
    have : (fun h : H => (φ h).1 0 0) = fun h =>
        (((φ h).1 0 0).re : ℂ) + ((- - ((φ h).1 0 0).im : ℝ) : ℂ) * Complex.I :=
      funext fun h => by simp
    rw [this]
    exact (Complex.continuous_ofReal.comp h₁).add
      ((Complex.continuous_ofReal.comp h₂.neg).mul continuous_const)
  have hc : Continuous fun h : H => (φ h).1 1 0 := by
    have : (fun h : H => (φ h).1 1 0) = fun h =>
        ((- - ((φ h).1 1 0).re : ℝ) : ℂ) + ((- - ((φ h).1 1 0).im : ℝ) : ℂ) * Complex.I :=
      funext fun h => by simp
    rw [this]
    exact (Complex.continuous_ofReal.comp h₃.neg).add
      ((Complex.continuous_ofReal.comp h₄.neg).mul continuous_const)
  refine continuous_induced_rng.mpr ?_
  have hq : (Subtype.val ∘ fun h : H => φ h) = fun h =>
      suMatrix ((φ h).1 0 0) ((φ h).1 1 0) :=
    funext fun h => (eq_suMatrix (φ h)).1
  show Continuous (Subtype.val ∘ fun h : H => φ h)
  rw [hq]
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j
  · simpa [suMatrix] using ha
  · have hcc : Continuous fun h : H => -conj ((φ h).1 1 0) := (Complex.continuous_conj.comp hc).neg
    simpa [suMatrix] using hcc
  · simpa [suMatrix] using hc
  · have hcc : Continuous fun h : H => conj ((φ h).1 0 0) := Complex.continuous_conj.comp ha
    simpa [suMatrix] using hcc
end Uniqueness
theorem metrizableSpace_specialUnitary :
    TopologicalSpace.MetrizableSpace ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.InfiniteLattice.AmbientFacts.Proofs.metrizableSpace_specialUnitary <;> assumption
theorem eq_induced_of_continuous_bijective {X Y : Type} [tX : TopologicalSpace X]
    [tY : TopologicalSpace Y] [CompactSpace X] [T2Space Y] (f : X → Y) (hf : Continuous f)
    (hb : Function.Bijective f) : tX = TopologicalSpace.induced f tY :=
  (isHomeomorph_iff_continuous_bijective.mpr ⟨hf, hb⟩).isEmbedding.isInducing.eq_induced
theorem topology_eq_subtype_of_compact_metrizable
    (τ : TopologicalSpace ComplexMatrix2.specialUnitary)
    (h₁ : @IsTopologicalGroup ComplexMatrix2.specialUnitary τ _)
    (h₂ : @CompactSpace ComplexMatrix2.specialUnitary τ)
    (h₃ : @TopologicalSpace.MetrizableSpace ComplexMatrix2.specialUnitary τ) :
    τ = (instTopologicalSpaceSubtype : TopologicalSpace ComplexMatrix2.specialUnitary) := by
  have ht : @T2Space ComplexMatrix2.specialUnitary τ := by
    haveI := h₃
    infer_instance
  haveI := metrizableSpace_specialUnitary
  have hc : @Continuous ComplexMatrix2.specialUnitary ComplexMatrix2.specialUnitary τ
      instTopologicalSpaceSubtype id :=
    @continuous_mulEquiv_specialUnitary ComplexMatrix2.specialUnitary _ τ h₁ h₂ ht
      (MulEquiv.refl _)
  have hi := @eq_induced_of_continuous_bijective ComplexMatrix2.specialUnitary
    ComplexMatrix2.specialUnitary τ instTopologicalSpaceSubtype h₂ _ id hc Function.bijective_id
  exact hi.trans (@induced_id _ instTopologicalSpaceSubtype)
theorem entrywiseTopology_eq_instance :
    ComplexMatrix2.entrywiseTopology = (inferInstance : TopologicalSpace ComplexMatrix2) := by
  let e : ComplexMatrix2 ≃ₜ ComplexCoordinates 4 :=
    { toEquiv := ComplexCoordinates.matrixEquiv
      continuous_toFun := continuous_pi fun k => continuous_id.matrix_elem _ _
      continuous_invFun := continuous_matrix fun i j => continuous_apply _ }
  exact e.isInducing.eq_induced.symm
theorem specialUnitaryEntrywiseTopology_eq_instance :
    ComplexMatrix2.specialUnitaryEntrywiseTopology =
      (inferInstance : TopologicalSpace ComplexMatrix2.specialUnitary) := by
  unfold ComplexMatrix2.specialUnitaryEntrywiseTopology
  rw [entrywiseTopology_eq_instance]
  rfl
theorem specialUnitaryTopologyUnique_holds : SpecialUnitaryTopologyUnique := by
  unfold SpecialUnitaryTopologyUnique
  rw [specialUnitaryEntrywiseTopology_eq_instance]
  exact ⟨fun τ h₁ h₂ h₃ => topology_eq_subtype_of_compact_metrizable τ h₁ h₂ h₃, rfl,
    inferInstance, inferInstance, metrizableSpace_specialUnitary⟩
variable {L m : ℕ} {j : ℤ}
theorem matrix_inv_coe (g : ComplexMatrix2.specialUnitary) :
    (g.1)⁻¹ = ((g⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) := by apply _root_.YangMills.Construction.PeriodicLattice.WilsonPlaquetteSum.coe_inv_specialUnitary <;> assumption
theorem matrix_inv_inv_coe (g : ComplexMatrix2.specialUnitary) : ((g.1)⁻¹)⁻¹ = g.1 := by
  rw [matrix_inv_coe, matrix_inv_coe, inv_inv]
def restrictPositive (U : compactGaugeFields L m j) :
    PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary :=
  fun b => ⟨U.1 b.1,
    (show IsGaugeField compactGaugeGroup univ U.1 from U.2).1 b.1 (mem_univ _)⟩
theorem gaugeFieldOfPositive_apply_pos
    (v : PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary)
    (b : Bond L m j) (h : b.IsPositivelyOriented) :
    gaugeFieldOfPositive v b = (v ⟨b, h⟩ : ComplexMatrix2) := by
  rw [gaugeFieldOfPositive, dif_pos h]
theorem gaugeFieldOfPositive_apply_opposite
    (v : PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary)
    (b : Bond L m j) (h : ¬ b.IsPositivelyOriented) (h' : b.opposite.IsPositivelyOriented) :
    gaugeFieldOfPositive v b = ((v ⟨b.opposite, h'⟩ : ComplexMatrix2))⁻¹ := by
  rw [gaugeFieldOfPositive, dif_neg h, dif_pos h']
structure OppositeFacts (L m : ℕ) (j : ℤ) : Prop where
  opposite_opposite : ∀ b : Bond L m j, b.opposite.opposite = b
  xor : ∀ b : Bond L m j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented
theorem gaugeFieldOfPositive_mem_compactGaugeFields (hr : OppositeFacts L m j)
    (v : PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary) :
    gaugeFieldOfPositive v ∈ compactGaugeFields L m j := by
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · rcases hr.xor b with ⟨h, _⟩ | ⟨h', h⟩
    · rw [gaugeFieldOfPositive_apply_pos v b h]
      exact (v ⟨b, h⟩).2
    · rw [gaugeFieldOfPositive_apply_opposite v b h h', matrix_inv_coe]
      exact ((v ⟨b.opposite, h'⟩)⁻¹).2
  · rcases hr.xor b with ⟨h, h'⟩ | ⟨h', h⟩
    · have h'' : b.opposite.opposite.IsPositivelyOriented := by
        rw [hr.opposite_opposite]; exact h
      rw [gaugeFieldOfPositive_apply_pos v b h, gaugeFieldOfPositive_apply_opposite v _ h' h'']
      congr 3
    · rw [gaugeFieldOfPositive_apply_pos v _ h', gaugeFieldOfPositive_apply_opposite v b h h',
        matrix_inv_inv_coe]
theorem gaugeFieldOfPositive_restrictPositive (hr : OppositeFacts L m j)
    (U : compactGaugeFields L m j) : gaugeFieldOfPositive (restrictPositive U) = U.1 := by
  funext b
  rcases hr.xor b with ⟨h, _⟩ | ⟨h', h⟩
  · rw [gaugeFieldOfPositive_apply_pos _ b h]
    rfl
  · rw [gaugeFieldOfPositive_apply_opposite _ b h h']
    have h2 := (show IsGaugeField compactGaugeGroup univ U.1 from U.2).2 b.opposite (mem_univ _)
    rw [hr.opposite_opposite] at h2
    rw [h2]
    rfl
theorem restrictPositive_bijective (hr : OppositeFacts L m j) :
    Function.Bijective (restrictPositive (L := L) (m := m) (j := j)) := by
  constructor
  · intro U U' h
    apply Subtype.ext
    rw [← gaugeFieldOfPositive_restrictPositive hr U, h,
      gaugeFieldOfPositive_restrictPositive hr U']
  · intro v
    refine ⟨⟨_, gaugeFieldOfPositive_mem_compactGaugeFields hr v⟩, ?_⟩
    funext b
    apply Subtype.ext
    exact gaugeFieldOfPositive_apply_pos v b.1 b.2
theorem continuous_gaugeFieldOfPositive_apply (b : Bond L m j) :
    Continuous fun v : PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary =>
      gaugeFieldOfPositive v b := by
  by_cases h : b.IsPositivelyOriented
  · simp only [gaugeFieldOfPositive, dif_pos h]
    exact continuous_subtype_val.comp (continuous_apply _)
  · by_cases h' : b.opposite.IsPositivelyOriented
    · simp only [gaugeFieldOfPositive, dif_neg h, dif_pos h', matrix_inv_coe]
      exact continuous_subtype_val.comp (continuous_inv.comp (continuous_apply _))
    · simp only [gaugeFieldOfPositive, dif_neg h, dif_neg h']
      exact continuous_const
section Continuity
variable {X : Type} [TopologicalSpace X] {W : X → Bond L m j → ComplexMatrix2}
theorem continuous_pathHolonomy (hW : ∀ b, Continuous fun x => W x b) (Γ : List (Bond L m j)) :
    Continuous fun x => pathHolonomy (W x) Γ := by
  induction Γ with
  | nil => simpa [pathHolonomy] using continuous_const
  | cons b Γ ih =>
    simp only [pathHolonomy, List.map_cons, List.prod_cons] at ih ⊢
    exact (hW b).matrix_mul ih
theorem continuous_plaquetteEnergy (hW : ∀ b, Continuous fun x => W x b) (p : Plaquette L m j) :
    Continuous fun x => plaquetteCost (W x) p := by
  have h := continuous_pathHolonomy hW p.boundaryBonds
  have ht : Continuous fun x => (ComplexMatrix2.fullTrace (pathHolonomy (W x) p.boundaryBonds)).re :=
    Complex.continuous_re.comp h.matrix_trace
  simp only [plaquetteCost, plaquetteHolonomy]
  exact continuous_const.sub (continuous_const.mul ht)
theorem continuous_wilsonAction_comp [Finite (Plaquette L m j)]
    (hW : ∀ b, Continuous fun x => W x b) : Continuous fun x => wilsonAction (W x) := by
  cases nonempty_fintype (Plaquette L m j)
  simp only [wilsonAction, finsum_eq_sum_of_fintype]
  exact continuous_finset_sum _ fun p _ => continuous_plaquetteEnergy hW p
theorem continuous_boltzmannWeight [Finite (Plaquette L m j)]
    (hW : ∀ b, Continuous fun x => W x b) (β : ℝ) :
    Continuous fun x => boltzmannWeight β (W x) := by
  simp only [boltzmannWeight]
  exact Real.continuous_exp.comp (continuous_const.mul (continuous_wilsonAction_comp hW))
end Continuity
theorem wilsonAction_mem_bounds [Finite (Plaquette L m j)] (U : Bond L m j → ComplexMatrix2)
    (h : ∀ p : Plaquette L m j, plaquetteCost U p ∈ Icc (0 : ℝ) 2) :
    0 ≤ wilsonAction U ∧ wilsonAction U ≤ 2 * (Nat.card (Plaquette L m j) : ℝ) := by
  cases nonempty_fintype (Plaquette L m j)
  simp only [wilsonAction, finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card]
  refine ⟨Finset.sum_nonneg fun p _ => (h p).1, ?_⟩
  calc ∑ p, plaquetteCost U p ≤ ∑ _p : Plaquette L m j, (2 : ℝ) :=
        Finset.sum_le_sum fun p _ => (h p).2
    _ = 2 * (Fintype.card (Plaquette L m j) : ℝ) := by
        simp [Finset.card_univ, mul_comm]
theorem exp_neg_mul_bounds {A n β : ℝ} (hβ : 0 < β) (h₀ : 0 ≤ A) (h₁ : A ≤ 2 * n) :
    Real.exp (-2 * β * n) ≤ Real.exp (-β * A) ∧ Real.exp (-β * A) ≤ 1 := by
  constructor
  · apply Real.exp_le_exp.mpr
    nlinarith
  · apply Real.exp_le_one_iff.mpr
    nlinarith
theorem induced_compact_metrizable {X Y : Type} [tY : TopologicalSpace Y] [CompactSpace Y]
    [TopologicalSpace.MetrizableSpace Y] (f : X → Y) (hf : Function.Bijective f) :
    @CompactSpace X (TopologicalSpace.induced f tY) ∧
      @TopologicalSpace.MetrizableSpace X (TopologicalSpace.induced f tY) := by
  letI : TopologicalSpace X := TopologicalSpace.induced f tY
  have hi : Topology.IsInducing f := ⟨rfl⟩
  have he : Topology.IsEmbedding f := ⟨hi, hf.1⟩
  refine ⟨⟨?_⟩, he.metrizableSpace⟩
  rw [hi.isCompact_iff, image_univ, hf.2.range_eq]
  exact isCompact_univ
theorem continuous_comp_of_induced {X Y Z : Type} [tY : TopologicalSpace Y] [TopologicalSpace Z]
    (f : X → Y) {g : Y → Z} (hg : Continuous g) :
    @Continuous X Z (TopologicalSpace.induced f tY) _ (g ∘ f) := by
  letI : TopologicalSpace X := TopologicalSpace.induced f tY
  exact hg.comp continuous_induced_dom
theorem productTopology_eq_induced (L m K : ℕ) :
    productTopology L m K =
      TopologicalSpace.induced (restrictPositive (L := L) (m := m) (j := (K : ℤ)))
        inferInstance := by
  unfold productTopology
  rw [specialUnitaryEntrywiseTopology_eq_instance]
  rfl
theorem continuous_eval_bond {K : ℕ} (hr : OppositeFacts L m (K : ℤ)) (b : Bond L m (K : ℤ)) :
    @Continuous (compactGaugeFields L m (K : ℤ)) ComplexMatrix2 (productTopology L m K) _
      fun U => U.1 b := by
  rw [productTopology_eq_induced]
  have h : (fun U : compactGaugeFields L m (K : ℤ) => U.1 b) =
      (fun v => gaugeFieldOfPositive v b) ∘ restrictPositive :=
    funext fun U => (congrFun (gaugeFieldOfPositive_restrictPositive hr U) b).symm
  rw [h]
  exact continuous_comp_of_induced _ (continuous_gaugeFieldOfPositive_apply b)
theorem compactMetrizableFieldSpace_holds {K : ℕ} (hr : OppositeFacts L m (K : ℤ))
    (hB : Finite (Bond L m (K : ℤ))) (hP : Finite (Plaquette L m (K : ℤ))) :
    CompactMetrizableFieldSpace L m K := by
  have hb := restrictPositive_bijective hr
  haveI := metrizableSpace_specialUnitary
  have hcm := induced_compact_metrizable _ hb
  refine ⟨hB, hP, hb, ?_, ?_, ?_, ?_⟩
  · rw [productTopology_eq_induced]
    rfl
  · rw [productTopology_eq_induced]
    exact hcm.1
  · rw [productTopology_eq_induced]
    exact hcm.2
  · intro b
    rw [entrywiseTopology_eq_instance]
    exact continuous_eval_bond hr b
theorem boltzmannWeightBounds_holds {K : ℕ} (hr : OppositeFacts L m (K : ℤ))
    [Finite (Plaquette L m (K : ℤ))]
    (hact : ∀ p : Plaquette L m (K : ℤ), ∀ U ∈ compactGaugeFields L m (K : ℤ),
      plaquetteCost U p ∈ Icc (0 : ℝ) 2) {β : ℝ} (hβ : 0 < β) :
    BoltzmannWeightBounds L m K β := by
  refine ⟨fun p => @continuous_plaquetteEnergy L m _ _ (productTopology L m K) _
      (continuous_eval_bond hr) p,
    @continuous_wilsonAction_comp L m _ _ (productTopology L m K) _ _ (continuous_eval_bond hr),
    @continuous_boltzmannWeight L m _ _ (productTopology L m K) _ _ (continuous_eval_bond hr) β,
    fun U hU => ?_⟩
  obtain ⟨h₀, h₁⟩ := wilsonAction_mem_bounds U fun p => hact p U hU
  exact ⟨h₀, h₁, exp_neg_mul_bounds hβ h₀ h₁⟩
theorem partitionFunctionBounds_holds {K : ℕ} (hr : OppositeFacts L m (K : ℤ))
    [Finite (Plaquette L m (K : ℤ))]
    (hact : ∀ p : Plaquette L m (K : ℤ), ∀ U ∈ compactGaugeFields L m (K : ℤ),
      plaquetteCost U p ∈ Icc (0 : ℝ) 2) {β : ℝ} (hβ : 0 < β) :
    PartitionFunctionBounds L m K β := by
  haveI : IsProbabilityMeasure (gaugeFieldHaar L m (K : ℤ)) := by
    unfold gaugeFieldHaar ComplexMatrix2.haarPi
    infer_instance
  haveI : SecondCountableTopology ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  haveI : SecondCountableTopology ComplexMatrix2.specialUnitary :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  have hcm : Measurable (gaugeFieldOfPositive (L := L) (m := m) (j := (K : ℤ))) :=
    measurable_pi_iff.mpr fun b => (continuous_gaugeFieldOfPositive_apply b).measurable
  have hfm : Measurable (boltzmannWeight β : (Bond L m (K : ℤ) → ComplexMatrix2) → ℝ) :=
    (continuous_boltzmannWeight (W := fun U : Bond L m (K : ℤ) → ComplexMatrix2 => U)
      (fun b => continuous_apply b) β).measurable
  have hbound : ∀ v : PositivelyOrientedBond L m (K : ℤ) → ComplexMatrix2.specialUnitary,
      Real.exp (-2 * β * (plaquetteCount L m K : ℝ)) ≤ boltzmannWeight β (gaugeFieldOfPositive v) ∧
        boltzmannWeight β (gaugeFieldOfPositive v) ≤ 1 := fun v => by
    obtain ⟨h₀, h₁⟩ := wilsonAction_mem_bounds (gaugeFieldOfPositive v)
      fun p => hact p _ (gaugeFieldOfPositive_mem_compactGaugeFields hr v)
    exact exp_neg_mul_bounds hβ h₀ h₁
  have hint : Integrable (fun v => boltzmannWeight β (gaugeFieldOfPositive v))
      (gaugeFieldHaar L m (K : ℤ)) :=
    Integrable.of_bound (hfm.comp hcm).aestronglyMeasurable 1 (ae_of_all _ fun v => by
      rw [Real.norm_eq_abs, abs_of_nonneg ((Real.exp_pos _).le.trans (hbound v).1)]
      exact (hbound v).2)
  have hZ : partitionFunction L m K β =
      ∫ v, boltzmannWeight β (gaugeFieldOfPositive v) ∂gaugeFieldHaar L m (K : ℤ) := by
    unfold partitionFunction productHaarMeasure
    exact integral_map hcm.aemeasurable hfm.aestronglyMeasurable
  refine ⟨?_, ?_, ?_⟩
  · unfold productHaarMeasure
    exact (integrable_map_measure hfm.aestronglyMeasurable hcm.aemeasurable).mpr hint
  · rw [hZ]
    calc Real.exp (-2 * β * (plaquetteCount L m K : ℝ))
        = ∫ _v, Real.exp (-2 * β * (plaquetteCount L m K : ℝ))
            ∂gaugeFieldHaar L m (K : ℤ) := by simp
      _ ≤ _ := integral_mono (integrable_const _) hint fun v => (hbound v).1
  · rw [hZ]
    calc ∫ v, boltzmannWeight β (gaugeFieldOfPositive v) ∂gaugeFieldHaar L m (K : ℤ)
        ≤ ∫ _v, (1 : ℝ) ∂gaugeFieldHaar L m (K : ℤ) :=
          integral_mono hint (integrable_const _) fun v => (hbound v).2
      _ = 1 := by simp
theorem fieldSpaceAndPartitionBounds_holds
    (h₁ : OppositeBonds.OppositeAndPositiveRestriction)
    (h₂ : PlaquetteHolonomyTraceBounds)
    (h₃ : CubePartitions.CubePartitionFacts) : FieldSpaceAndPartitionBounds := by
  intro s
  have hj : -((s.m : ℕ) : ℤ) < ((s.K : ℕ) : ℤ) := by
    have := s.K.pos
    have := s.m.pos
    omega
  have hr : OppositeFacts s.L s.m ((s.K : ℕ) : ℤ) :=
    ⟨fun b => ((h₁ s _ hj).1 b).2.2.1, fun b => ((h₁ s _ hj).1 b).2.2.2.2.2⟩
  have hc := (h₃ s _ hj.le 1 (Or.inl rfl)).1
  have hB : Finite (Bond s.L s.m ((s.K : ℕ) : ℤ)) := hc.2.2.1
  have hP : Finite (Plaquette s.L s.m ((s.K : ℕ) : ℤ)) := hc.2.2.2.1
  have hact := (h₂ s).2
  exact ⟨compactMetrizableFieldSpace_holds hr hB hP,
    fun β hβ => ⟨boltzmannWeightBounds_holds hr hact hβ, partitionFunctionBounds_holds hr hact hβ⟩,
    specialUnitaryTopologyUnique_holds⟩
end YangMills.Construction.PeriodicLattice.GaugeFieldSpace
