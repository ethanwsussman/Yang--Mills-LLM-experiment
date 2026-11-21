import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.ResponseInTheExpansion.CalculusOfTheParts
import YangMills.Construction.RunningCouplingSlope.MomentOfAnExpansionProof
import YangMills.Construction.RunningCouplingSlope.MomentOfTheExpansionAtTheLeastField
import YangMills.Construction.RunningCouplingSlope.TangentsOfTheLeastField
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
open TorusFields TorusLumps TorusBalls CongruentBoxes BlockAverages SlopeCoefficient Filter
namespace RunningCouplingSlope
namespace MinimizerMoment
section Sums
variable {m : ℕ} [NeZero m]
private def siteSum (κ : ℝ) : ℝ := (2 / (1 - Real.exp (-κ / 4))) ^ 4
private theorem siteSum_nonneg {κ : ℝ} (hκ : 0 < κ) : 0 ≤ siteSum κ := by
  unfold siteSum
  have h : Real.exp (-κ / 4) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have : 0 < 1 - Real.exp (-κ / 4) := by linarith
  positivity
private theorem sum_sites {κ : ℝ} (hκ : 0 < κ) (o : TorusSite m) :
    ∑ y : TorusSite m, Real.exp (-κ * _root_.YangMills.Construction.TorusFields.supDist y o) ≤ siteSum κ := sum_exp_neg_mul_supDist_le hκ o
private theorem sum_bonds {κ : ℝ} (hκ : 0 < κ) (o : TorusSite m) :
    ∑ b : TorusBond m, Real.exp (-κ * _root_.YangMills.Construction.TorusFields.supDist b.1 o) ≤ 4 * siteSum κ := by
  rw [Fintype.sum_prod_type]
  have h := sum_sites (m := m) hκ o
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  push_cast
  linarith
private def gw (κ : ℝ) (o o' y : TorusSite m) (b b' : TorusBond m) : ℝ :=
  Real.exp (-κ * _root_.YangMills.Construction.TorusFields.supDist b.1 o) * Real.exp (-κ * _root_.YangMills.Construction.TorusFields.supDist b'.1 o') * Real.exp (-κ * _root_.YangMills.Construction.TorusFields.supDist y b.1)
private theorem gw_nonneg (κ : ℝ) (o o' y : TorusSite m) (b b' : TorusBond m) : 0 ≤ gw κ o o' y b b' := by
  unfold gw
  positivity
private def gwSum (κ : ℝ) : ℝ := (4 * siteSum κ) * (4 * siteSum κ) * siteSum κ
private theorem gwSum_nonneg {κ : ℝ} (hκ : 0 < κ) : 0 ≤ gwSum κ := by
  have := siteSum_nonneg hκ
  unfold gwSum
  positivity
private theorem sum_gw {κ : ℝ} (hκ : 0 < κ) (o o' : TorusSite m) :
    ∑ b : TorusBond m, ∑ b' : TorusBond m, ∑ y : TorusSite m, gw κ o o' y b b' ≤ gwSum κ := by
  have hS := siteSum_nonneg hκ
  have h1 : ∀ b b' : TorusBond m, ∑ y : TorusSite m, gw κ o o' y b b' ≤
      Real.exp (-κ * _root_.YangMills.Construction.TorusFields.supDist b.1 o) * Real.exp (-κ * _root_.YangMills.Construction.TorusFields.supDist b'.1 o') * siteSum κ := by
    intro b b'
    unfold gw
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_sites hκ b.1) (by positivity)
  have h2 : ∀ b : TorusBond m, ∑ b' : TorusBond m, ∑ y : TorusSite m, gw κ o o' y b b' ≤
      Real.exp (-κ * _root_.YangMills.Construction.TorusFields.supDist b.1 o) * (4 * siteSum κ) * siteSum κ := by
    intro b
    calc ∑ b' : TorusBond m, ∑ y : TorusSite m, gw κ o o' y b b'
        ≤ ∑ b' : TorusBond m, Real.exp (-κ * _root_.YangMills.Construction.TorusFields.supDist b.1 o) * Real.exp (-κ * _root_.YangMills.Construction.TorusFields.supDist b'.1 o') * siteSum κ :=
          Finset.sum_le_sum fun b' _ => h1 b b'
      _ = Real.exp (-κ * _root_.YangMills.Construction.TorusFields.supDist b.1 o) * (∑ b' : TorusBond m, Real.exp (-κ * _root_.YangMills.Construction.TorusFields.supDist b'.1 o')) * siteSum κ := by
          rw [Finset.mul_sum, Finset.sum_mul]
      _ ≤ _ := by
          have := sum_bonds (m := m) hκ o'
          gcongr
  calc ∑ b : TorusBond m, ∑ b' : TorusBond m, ∑ y : TorusSite m, gw κ o o' y b b'
      ≤ ∑ b : TorusBond m, Real.exp (-κ * _root_.YangMills.Construction.TorusFields.supDist b.1 o) * (4 * siteSum κ) * siteSum κ :=
        Finset.sum_le_sum fun b _ => h2 b
    _ = (∑ b : TorusBond m, Real.exp (-κ * _root_.YangMills.Construction.TorusFields.supDist b.1 o)) * (4 * siteSum κ) * siteSum κ := by
        rw [Finset.sum_mul, Finset.sum_mul]
    _ ≤ _ := by
        have := sum_bonds (m := m) hκ o
        unfold gwSum
        gcongr
private theorem sum_le_of_term {κ A : ℝ} (hκ : 0 < κ) (hA : 0 ≤ A) (o o' : TorusSite m)
    (t : TorusSite m → TorusBond m → TorusBond m → ℝ) (h : ∀ y b b', |t y b b'| ≤ A * gw κ o o' y b b') :
    |∑ b : TorusBond m, ∑ b' : TorusBond m, ∑ y : TorusSite m, t y b b'| ≤ A * gwSum κ := by
  calc |∑ b : TorusBond m, ∑ b' : TorusBond m, ∑ y : TorusSite m, t y b b'|
      ≤ ∑ b : TorusBond m, ∑ b' : TorusBond m, ∑ y : TorusSite m, |t y b b'| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ =>
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b' _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ b : TorusBond m, ∑ b' : TorusBond m, ∑ y : TorusSite m, A * gw κ o o' y b b' :=
        Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun b' _ => Finset.sum_le_sum fun y _ => h y b b'
    _ = A * ∑ b : TorusBond m, ∑ b' : TorusBond m, ∑ y : TorusSite m, gw κ o o' y b b' := by
        simp only [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_gw hκ o o') hA
private theorem term_le {θ r κ d1 d2 d3 s' s : ℝ} (hκ : 0 < κ) (h1 : 3 * κ ≤ θ) (h2 : 6 * κ ≤ r) (n1 : 0 ≤ d1)
    (n2 : 0 ≤ d2) (n3 : 0 ≤ d3) (n4 : 0 ≤ s') (hs3 : d3 ≤ s) (hs4 : s' ≤ s) :
    Real.exp (-(θ * d1)) * Real.exp (-(θ * d2)) * Real.exp (-(r * s)) ≤
      Real.exp (-(2 * κ * (d1 + d2 + d3 + s'))) *
        (Real.exp (-κ * d1) * Real.exp (-κ * d2) * Real.exp (-κ * d3)) := by
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have a1 := mul_le_mul_of_nonneg_right h1 n1
  have a2 := mul_le_mul_of_nonneg_right h1 n2
  have a3 := mul_le_mul_of_nonneg_left hs3 hκ.le
  have a4 := mul_le_mul_of_nonneg_left hs4 hκ.le
  have a5 := mul_le_mul_of_nonneg_right h2 (n3.trans hs3)
  have a6 := mul_nonneg hκ.le n4
  nlinarith
private theorem le_span_left (y : TorusSite m) (c c' : TorusBond m) : _root_.YangMills.Construction.TorusFields.supDist y c.1 ≤ supportDiam y ![c, c'] := by
  unfold supportDiam
  exact le_max_of_le_left (Finset.le_sup (f := fun l : Fin 2 => _root_.YangMills.Construction.TorusFields.supDist y ((![c, c'] : Fin 2 → TorusBond m) l).1) (Finset.mem_univ 0))
private theorem le_span_mid (y : TorusSite m) (c c' : TorusBond m) : _root_.YangMills.Construction.TorusFields.supDist c.1 c'.1 ≤ supportDiam y ![c, c'] := by
  unfold supportDiam
  refine le_max_of_le_right (le_trans ?_ (Finset.le_sup
    (f := fun l : Fin 2 => Finset.univ.sup fun l' : Fin 2 =>
      _root_.YangMills.Construction.TorusFields.supDist ((![c, c'] : Fin 2 → TorusBond m) l).1 ((![c, c'] : Fin 2 → TorusBond m) l').1) (Finset.mem_univ 0)))
  exact Finset.le_sup (f := fun l' : Fin 2 => _root_.YangMills.Construction.TorusFields.supDist ((![c, c'] : Fin 2 → TorusBond m) 0).1 ((![c, c'] : Fin 2 → TorusBond m) l').1)
    (Finset.mem_univ 1)
private def IsTermBound (Q θ r : ℝ) (o o' : TorusSite m) (τ : TorusSite m → TorusBond m → TorusBond m → ℝ) : Prop :=
  ∀ y b b', |τ y b b'| ≤ Q * (Real.exp (-(θ * _root_.YangMills.Construction.TorusFields.supDist b.1 o)) * Real.exp (-(θ * _root_.YangMills.Construction.TorusFields.supDist b'.1 o')) *
    Real.exp (-(r * supportDiam y ![b, b'])))
private theorem term_bound {Q θ r κ : ℝ} (hQ : 0 ≤ Q) (hκ : 0 < κ) (h1 : 3 * κ ≤ θ) (h2 : 6 * κ ≤ r) {o o' : TorusSite m}
    {τ : TorusSite m → TorusBond m → TorusBond m → ℝ} (h : IsTermBound Q θ r o o' τ) (y : TorusSite m) (b b' : TorusBond m) :
    |τ y b b'| ≤ Q * Real.exp (-(2 * κ * ((_root_.YangMills.Construction.TorusFields.supDist b.1 o : ℝ) + _root_.YangMills.Construction.TorusFields.supDist b'.1 o' + _root_.YangMills.Construction.TorusFields.supDist y b.1 + _root_.YangMills.Construction.TorusFields.supDist b.1 b'.1))) *
      gw κ o o' y b b' := by
  have e := term_le (θ := θ) (r := r) (κ := κ) (d1 := _root_.YangMills.Construction.TorusFields.supDist b.1 o) (d2 := _root_.YangMills.Construction.TorusFields.supDist b'.1 o') (d3 := _root_.YangMills.Construction.TorusFields.supDist y b.1)
    (s' := _root_.YangMills.Construction.TorusFields.supDist b.1 b'.1) (s := supportDiam y ![b, b']) hκ h1 h2 (by positivity) (by positivity) (by positivity)
    (by positivity) (by exact_mod_cast le_span_left y b b') (by exact_mod_cast le_span_mid y b b')
  refine (h y b b').trans ((mul_le_mul_of_nonneg_left e hQ).trans (le_of_eq ?_))
  unfold gw
  ring
private theorem kernel_decay {Q θ r κ : ℝ} (hQ : 0 ≤ Q) (hκ : 0 < κ) (h1 : 3 * κ ≤ θ) (h2 : 6 * κ ≤ r) {o o' : TorusSite m}
    {τ : TorusSite m → TorusBond m → TorusBond m → ℝ} (h : IsTermBound Q θ r o o' τ) :
    |∑ b : TorusBond m, ∑ b' : TorusBond m, ∑ y : TorusSite m, τ y b b'| ≤
      Q * Real.exp (-(2 * κ * _root_.YangMills.Construction.TorusFields.supDist o o')) * gwSum κ := by
  refine sum_le_of_term hκ (by positivity) o o' τ fun y b b' => (term_bound hQ hκ h1 h2 h y b b').trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (gw_nonneg _ _ _ _ _ _)
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hQ
  have t1 : _root_.YangMills.Construction.TorusFields.supDist o o' ≤ _root_.YangMills.Construction.TorusFields.supDist b.1 o + _root_.YangMills.Construction.TorusFields.supDist b.1 b'.1 + _root_.YangMills.Construction.TorusFields.supDist b'.1 o' := by
    have a := _root_.YangMills.Construction.TorusFields.supDist_triangle o b.1 o'
    have b2 := _root_.YangMills.Construction.TorusFields.supDist_triangle b.1 b'.1 o'
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm o b.1] at a
    omega
  have t2 : (_root_.YangMills.Construction.TorusFields.supDist o o' : ℝ) ≤ (_root_.YangMills.Construction.TorusFields.supDist b.1 o : ℝ) + _root_.YangMills.Construction.TorusFields.supDist b.1 b'.1 + _root_.YangMills.Construction.TorusFields.supDist b'.1 o' := by exact_mod_cast t1
  nlinarith
open Classical in
private theorem kernel_tail {Q θ r κ : ℝ} (hQ : 0 ≤ Q) (hκ : 0 < κ) (h1 : 3 * κ ≤ θ) (h2 : 6 * κ ≤ r) {o o' : TorusSite m}
    {τ : TorusSite m → TorusBond m → TorusBond m → ℝ} (h : IsTermBound Q θ r o o' τ) (ρ : ℕ) :
    |(∑ b : TorusBond m, ∑ b' : TorusBond m, ∑ y : TorusSite m, τ y b b') -
      ∑ b : TorusBond m, ∑ b' : TorusBond m, ∑ y : TorusSite m,
        if _root_.YangMills.Construction.TorusFields.supDist b.1 o < ρ ∧ _root_.YangMills.Construction.TorusFields.supDist b'.1 o' < ρ ∧ _root_.YangMills.Construction.TorusFields.supDist y b.1 < ρ then τ y b b' else 0| ≤
      Q * Real.exp (-(2 * κ * ρ)) * gwSum κ := by
  have e : (∑ b : TorusBond m, ∑ b' : TorusBond m, ∑ y : TorusSite m, τ y b b') -
      ∑ b : TorusBond m, ∑ b' : TorusBond m, ∑ y : TorusSite m,
        (if _root_.YangMills.Construction.TorusFields.supDist b.1 o < ρ ∧ _root_.YangMills.Construction.TorusFields.supDist b'.1 o' < ρ ∧ _root_.YangMills.Construction.TorusFields.supDist y b.1 < ρ then τ y b b' else 0) =
      ∑ b : TorusBond m, ∑ b' : TorusBond m, ∑ y : TorusSite m,
        (τ y b b' - if _root_.YangMills.Construction.TorusFields.supDist b.1 o < ρ ∧ _root_.YangMills.Construction.TorusFields.supDist b'.1 o' < ρ ∧ _root_.YangMills.Construction.TorusFields.supDist y b.1 < ρ then τ y b b' else 0) := by
    simp only [Finset.sum_sub_distrib]
  rw [e]
  refine sum_le_of_term hκ (by positivity) o o' _ fun y b b' => ?_
  by_cases hc : _root_.YangMills.Construction.TorusFields.supDist b.1 o < ρ ∧ _root_.YangMills.Construction.TorusFields.supDist b'.1 o' < ρ ∧ _root_.YangMills.Construction.TorusFields.supDist y b.1 < ρ
  · rw [if_pos hc, sub_self, abs_zero]
    have := gw_nonneg κ o o' y b b'
    positivity
  · rw [if_neg hc, sub_zero]
    refine (term_bound hQ hκ h1 h2 h y b b').trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (gw_nonneg _ _ _ _ _ _)
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hQ
    have t : (ρ : ℝ) ≤ (_root_.YangMills.Construction.TorusFields.supDist b.1 o : ℝ) + _root_.YangMills.Construction.TorusFields.supDist b'.1 o' + _root_.YangMills.Construction.TorusFields.supDist y b.1 + _root_.YangMills.Construction.TorusFields.supDist b.1 b'.1 := by
      have t1 : ρ ≤ _root_.YangMills.Construction.TorusFields.supDist b.1 o + _root_.YangMills.Construction.TorusFields.supDist b'.1 o' + _root_.YangMills.Construction.TorusFields.supDist y b.1 + _root_.YangMills.Construction.TorusFields.supDist b.1 b'.1 := by
        by_contra hlt
        exact hc ⟨by omega, by omega, by omega⟩
      exact_mod_cast t1
    nlinarith
private def latBox (ρ : ℕ) : Finset (Fin 4 → ℤ) := Fintype.piFinset fun _ => Finset.Icc (1 - (ρ : ℤ)) ((ρ : ℤ) - 1)
private theorem mem_latBox {ρ : ℕ} {z : Fin 4 → ℤ} : z ∈ latBox ρ ↔ ∀ i, 1 - (ρ : ℤ) ≤ z i ∧ z i ≤ (ρ : ℤ) - 1 := by
  simp [latBox, Fintype.mem_piFinset]
private theorem card_latBox (ρ : ℕ) : ((latBox ρ).card : ℝ) ≤ (2 * (ρ : ℝ)) ^ 4 := by
  unfold latBox
  rw [Fintype.card_piFinset]
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  push_cast
  have h : (((((ρ : ℤ) - 1 + 1 - (1 - (ρ : ℤ))).toNat : ℕ)) : ℝ) ≤ 2 * (ρ : ℝ) := by
    have h2 : (((ρ : ℤ) - 1 + 1 - (1 - (ρ : ℤ))).toNat : ℤ) ≤ 2 * (ρ : ℤ) := by omega
    exact_mod_cast h2
  gcongr
open Classical in
private theorem sum_ball (o : TorusSite m) {ρ : ℕ} (hρ : 2 * ρ ≤ m) (g : TorusSite m → ℝ) :
    ∑ w : TorusSite m, (if _root_.YangMills.Construction.TorusFields.supDist w o < ρ then g w else 0) = ∑ z ∈ latBox ρ, g (o + siteOfInt z) := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_nbij (fun z => o + siteOfInt z) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro z hz
    have hb := mem_latBox.mp hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have h0 : 1 ≤ ρ := by
      have := hb 0
      omega
    have := _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le o z (ρ - 1) fun i => by
      have := hb i
      omega
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
    omega
  · intro z hz z' hz' h
    have hb := mem_latBox.mp hz
    have hb' := mem_latBox.mp hz'
    refine eq_of_siteOfInt_eq (n := m) (add_left_cancel h) fun i => ?_
    have := hb i
    have := hb' i
    rw [abs_lt]
    omega
  · intro w hw
    have hw' : _root_.YangMills.Construction.TorusFields.supDist w o < ρ := by
      simpa using hw
    obtain ⟨e, he, hb⟩ := exists_offset_of_supDist o w
    refine ⟨e, ?_, he.symm⟩
    refine mem_latBox.mpr fun i => ?_
    have := hb i
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm] at this
    omega
open Classical in
private theorem sum_ball_bonds (o : TorusSite m) {ρ : ℕ} (hρ : 2 * ρ ≤ m) (g : TorusBond m → ℝ) :
    ∑ b : TorusBond m, (if _root_.YangMills.Construction.TorusFields.supDist b.1 o < ρ then g b else 0) = ∑ z ∈ latBox ρ, ∑ i : Fin 4, g (o + siteOfInt z, i) := by
  rw [Fintype.sum_prod_type, ← sum_ball o hρ (fun w => ∑ i : Fin 4, g (w, i))]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases h : _root_.YangMills.Construction.TorusFields.supDist w o < ρ
  · simp [h]
  · simp [h]
open Classical in
private theorem trunc_eq (o o' : TorusSite m) {ρ : ℕ} (hρ : 2 * ρ ≤ m) (τ : TorusSite m → TorusBond m → TorusBond m → ℝ) :
    (∑ b : TorusBond m, ∑ b' : TorusBond m, ∑ y : TorusSite m,
      if supDist b.1 o < ρ ∧ supDist b'.1 o' < ρ ∧ supDist y b.1 < ρ then τ y b b' else 0) =
    ∑ z ∈ latBox ρ, ∑ i : Fin 4, ∑ z' ∈ latBox ρ, ∑ i' : Fin 4, ∑ ζ ∈ latBox ρ,
      τ (o + siteOfInt z + siteOfInt ζ) (o + siteOfInt z, i) (o' + siteOfInt z', i') := by
  have e : ∀ b : TorusBond m, (∑ b' : TorusBond m, ∑ y : TorusSite m,
      if supDist b.1 o < ρ ∧ supDist b'.1 o' < ρ ∧ supDist y b.1 < ρ then τ y b b' else 0) =
      if _root_.YangMills.Construction.TorusFields.supDist b.1 o < ρ then ∑ z' ∈ latBox ρ, ∑ i' : Fin 4, ∑ ζ ∈ latBox ρ,
        τ (b.1 + siteOfInt ζ) b (o' + siteOfInt z', i') else 0 := by
    intro b
    by_cases h : _root_.YangMills.Construction.TorusFields.supDist b.1 o < ρ
    · rw [if_pos h, ← sum_ball_bonds o' hρ (fun b' => ∑ ζ ∈ latBox ρ, τ (b.1 + siteOfInt ζ) b b')]
      refine Finset.sum_congr rfl fun b' _ => ?_
      by_cases h' : _root_.YangMills.Construction.TorusFields.supDist b'.1 o' < ρ
      · rw [if_pos h', ← sum_ball b.1 hρ (fun y => τ y b b')]
        refine Finset.sum_congr rfl fun y _ => ?_
        by_cases h'' : _root_.YangMills.Construction.TorusFields.supDist y b.1 < ρ
        · rw [if_pos ⟨h, h', h''⟩, if_pos h'']
        · rw [if_neg (fun q => h'' q.2.2), if_neg h'']
      · rw [if_neg h']
        exact Finset.sum_eq_zero fun y _ => if_neg fun q => h' q.2.1
    · rw [if_neg h]
      exact Finset.sum_eq_zero fun b' _ => Finset.sum_eq_zero fun y _ => if_neg fun q => h q.1
  simp only [e]
  rw [sum_ball_bonds o hρ (fun b => ∑ z' ∈ latBox ρ, ∑ i' : Fin 4, ∑ ζ ∈ latBox ρ,
    τ (b.1 + siteOfInt ζ) b (o' + siteOfInt z', i'))]
end Sums
section Fine
variable {n L : ℕ} [NeZero n] [NeZero L]
private theorem anchor_of (w : Fin 4 → ℤ) :
    blockCentre L (siteOfInt w : TorusSite n) = siteOfInt (fun i => (L : ℤ) * w i) := by
  funext j
  simp only [blockCentre, siteOfInt]
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  have hc : (((w j : ZMod n)).cast : ℤ) = w j % (n : ℤ) := ZMod.coe_intCast _
  rw [hc, Int.emod_def]
  refine ⟨w j / (n : ℤ), ?_⟩
  push_cast
  ring
private theorem exists_siteOfInt (Y : TorusSite n) : ∃ w : Fin 4 → ℤ, Y = siteOfInt w :=
  ⟨fun i => ((Y i).cast : ℤ), by
    funext i
    simp [siteOfInt]⟩
private theorem anchor_dist (Y c : TorusSite n) :
    _root_.YangMills.Construction.TorusFields.supDist (blockCentre L Y) (blockCentre L c) ≤ L * _root_.YangMills.Construction.TorusFields.supDist Y c := by
  obtain ⟨w, rfl⟩ := exists_siteOfInt Y
  obtain ⟨e, he, hb⟩ := exists_offset_of_supDist (siteOfInt w : TorusSite n) c
  rw [he, ← siteOfInt_add, anchor_of, anchor_of]
  have h1 : (siteOfInt (fun i => (L : ℤ) * (w + e) i) : TorusSite (n * L)) =
      siteOfInt (fun i => (L : ℤ) * w i) + siteOfInt (fun i => (L : ℤ) * e i) := by
    rw [← siteOfInt_add]
    congr 1
    funext i
    simp only [Pi.add_apply]
    ring
  rw [h1]
  refine _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le _ _ _ fun i => ?_
  rw [Int.natAbs_mul, Int.natAbs_natCast]
  have := hb i
  rw [show (siteOfInt (w + e) : TorusSite n) = c by rw [siteOfInt_add, ← he]]
  exact Nat.mul_le_mul_left _ this
private theorem coarseOffset_zero (hL : 0 < L) : coarseOffset L 0 = 0 := by
  funext i
  simp only [coarseOffset, Pi.zero_apply, zero_add]
  have : (0 : ℤ) < L := by exact_mod_cast hL
  exact Int.ediv_eq_zero_of_lt (by omega) (by omega)
private theorem block_of_anchor (hL : 0 < L) (Y : TorusSite n) : parentBlock L (blockCentre L Y) = Y := by
  have h := parentBlock_blockCentre_add (L := L) Y 0
  rw [coarseOffset_zero hL] at h
  have e : (siteOfInt (0 : Fin 4 → ℤ) : TorusSite (n * L)) = 0 := siteOfInt_zero_offset
  have e' : (siteOfInt (0 : Fin 4 → ℤ) : TorusSite n) = 0 := siteOfInt_zero_offset
  rw [e, e', add_zero, add_zero] at h
  exact h
private theorem fine_le (hL : 0 < L) (b : TorusSite (n * L)) (c : TorusSite n) :
    (_root_.YangMills.Construction.TorusFields.supDist b (blockCentre L c) : ℝ) ≤ (L : ℝ) * ((_root_.YangMills.Construction.TorusFields.supDist (parentBlock L b) c : ℝ) + 1) := by
  have a1 : _root_.YangMills.Construction.TorusFields.supDist b (blockCentre L (parentBlock L b)) ≤ L :=
    ClusterExpansionOfAStep.supDist_le_of_parentBlock_eq (block_of_anchor hL _).symm
  have a2 := anchor_dist (L := L) (parentBlock L b) c
  have a3 := _root_.YangMills.Construction.TorusFields.supDist_triangle b (blockCentre L (parentBlock L b)) (blockCentre L c)
  have a4 : _root_.YangMills.Construction.TorusFields.supDist b (blockCentre L c) ≤ L * (_root_.YangMills.Construction.TorusFields.supDist (parentBlock L b) c + 1) := by
    rw [mul_add, mul_one]
    omega
  exact_mod_cast a4
private theorem coarse_le (hL : 0 < L) (c c' : TorusSite n) :
    _root_.YangMills.Construction.TorusFields.supDist c c' ≤ _root_.YangMills.Construction.TorusFields.supDist (blockCentre L c) (blockCentre L c') + 1 := by
  have h := _root_.YangMills.Construction.TorusBalls.supDist_parentBlock_le_div_add_one L (blockCentre L c) (blockCentre L c')
  rw [block_of_anchor hL, block_of_anchor hL] at h
  exact h.trans (Nat.add_le_add_right (Nat.div_le_self _ _) 1)
end Fine
section Data
private structure IsData (L n₀ : ℕ) (E r M θ : ℝ)
    (d : (m : ℕ) → TorusSite m → TorusBond m → TorusBond m → imaginaryQuaternions → imaginaryQuaternions → ℝ)
    (Z : (n : ℕ) → TorusBond n → imaginaryQuaternions → TorusBond (n * L) → imaginaryQuaternions)
    (X : imaginaryQuaternions) : Prop where
  sub_left : ∀ (m : ℕ) [NeZero m], n₀ ≤ m → ∀ (y : TorusSite m) (b b' : TorusBond m) (Y₁ Y₂ Y' : imaginaryQuaternions),
    d m y b b' (Y₁ - Y₂) Y' = d m y b b' Y₁ Y' - d m y b b' Y₂ Y'
  sub_right : ∀ (m : ℕ) [NeZero m], n₀ ≤ m → ∀ (y : TorusSite m) (b b' : TorusBond m) (Y Y₁ Y₂ : imaginaryQuaternions),
    d m y b b' Y (Y₁ - Y₂) = d m y b b' Y Y₁ - d m y b b' Y Y₂
  bound : ∀ (m : ℕ) [NeZero m], n₀ ≤ m → ∀ (y : TorusSite m) (b b' : TorusBond m) (Y Y' : imaginaryQuaternions),
    |d m y b b' Y Y'| ≤ ‖Y‖ * ‖Y'‖ * (E * Real.exp (-(r * supportDiam y ![b, b'])))
  compare : ∀ (m m' : ℕ) [NeZero m] [NeZero m'], n₀ ≤ m → n₀ ≤ m' → ∀ (y : TorusSite m) (y' : TorusSite m') (q : ℕ),
    2 * q + 2 < m → 2 * q + 2 < m' → ∀ h₀ h₁ : LatticeBond, BondOffsetInBox q h₀ → BondOffsetInBox q h₁ →
    ∀ Y Y' : imaginaryQuaternions, |d m y (bondFrom y h₀) (bondFrom y h₁) Y Y' - d m' y' (bondFrom y' h₀) (bondFrom y' h₁) Y Y'| ≤
      ‖Y‖ * ‖Y'‖ * (E * Real.exp (-(r * q)))
  tan_bound : ∀ (n : ℕ) [NeZero n], n₀ ≤ n → ∀ (c : TorusBond n) (b : TorusBond (n * L)),
    ‖Z n c X b‖ ≤ M * Real.exp (-(θ * (_root_.YangMills.Construction.TorusFields.supDist (parentBlock L b.1) c.1 : ℝ)))
  tan_compare : ∀ (n n' : ℕ) [NeZero n] [NeZero n'] (ρ : ℕ) (u e : Fin 4 → ℤ) (i k : Fin 4), n₀ ≤ n → n₀ ≤ n' →
    16 ≤ ρ → 2 * ρ + 2 < n → 2 * ρ + 2 < n' → (∀ j, |e j - coarseOffset L u j| + 1 ≤ (ρ : ℤ)) →
    ‖Z n (siteOfInt e, k) X (siteOfInt u, i) - Z n' (siteOfInt e, k) X (siteOfInt u, i)‖ ≤ M * Real.exp (-(θ * (ρ : ℝ)))
private def kern (L : ℕ) (d : (m : ℕ) → TorusSite m → TorusBond m → TorusBond m → imaginaryQuaternions → imaginaryQuaternions → ℝ)
    (Z : (n : ℕ) → TorusBond n → imaginaryQuaternions → TorusBond (n * L) → imaginaryQuaternions) (X : imaginaryQuaternions)
    (n : ℕ) [NeZero (n * L)] (c c' : TorusBond n) : ℝ :=
  ∑ b : TorusBond (n * L), ∑ b' : TorusBond (n * L), ∑ y : TorusSite (n * L), d (n * L) y b b' (Z n c X b) (Z n c' X b')
private def qc (E M θ : ℝ) : ℝ := (M * Real.exp θ) * (M * Real.exp θ) * E
private def κc (L : ℕ) (r θ : ℝ) : ℝ := min (θ / L) r / 6
variable {L n₀ : ℕ} [NeZero L] {E r M θ : ℝ}
  {d : (m : ℕ) → TorusSite m → TorusBond m → TorusBond m → imaginaryQuaternions → imaginaryQuaternions → ℝ}
  {Z : (n : ℕ) → TorusBond n → imaginaryQuaternions → TorusBond (n * L) → imaginaryQuaternions} {X : imaginaryQuaternions}
private theorem κc_pos (hL : 0 < L) (hr : 0 < r) (hθ : 0 < θ) : 0 < κc L r θ := by
  unfold κc
  have : (0 : ℝ) < L := by exact_mod_cast hL
  have : 0 < θ / L := by positivity
  have : 0 < min (θ / L) r := lt_min this hr
  positivity
private theorem κc_le (hL : 0 < L) (hr : 0 < r) (hθ : 0 < θ) : 3 * κc L r θ ≤ θ / L ∧ 6 * κc L r θ ≤ r := by
  have h1 : min (θ / L) r ≤ θ / L := min_le_left _ _
  have h2 : min (θ / L) r ≤ r := min_le_right _ _
  have hp : 0 < κc L r θ := κc_pos hL hr hθ
  unfold κc at hp ⊢
  constructor <;> linarith
private theorem tangent_fine (hD : IsData L n₀ E r M θ d Z X) (hL : 0 < L) (hM : 0 ≤ M) (hθ : 0 < θ) {n : ℕ} [NeZero n]
    (hn : n₀ ≤ n) (c : TorusBond n) (b : TorusBond (n * L)) :
    ‖Z n c X b‖ ≤ (M * Real.exp θ) * Real.exp (-(θ / L * (_root_.YangMills.Construction.TorusFields.supDist b.1 (blockCentre L c.1) : ℝ))) := by
  refine (hD.tan_bound n hn c b).trans ?_
  rw [mul_assoc, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hM
  have hf := fine_le hL b.1 c.1
  have h2 : θ / L * (_root_.YangMills.Construction.TorusFields.supDist b.1 (blockCentre L c.1) : ℝ) ≤ θ / L * ((L : ℝ) * ((_root_.YangMills.Construction.TorusFields.supDist (parentBlock L b.1) c.1 : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_left hf (by positivity)
  have h3 : θ / L * ((L : ℝ) * ((_root_.YangMills.Construction.TorusFields.supDist (parentBlock L b.1) c.1 : ℝ) + 1)) = θ * ((_root_.YangMills.Construction.TorusFields.supDist (parentBlock L b.1) c.1 : ℝ) + 1) := by
    field_simp
  rw [h3] at h2
  nlinarith
private theorem term_of_data (hD : IsData L n₀ E r M θ d Z X) (hL : 0 < L) (hE : 0 ≤ E) (hM : 0 ≤ M) (hθ : 0 < θ)
    {n : ℕ} [NeZero n] [NeZero (n * L)] (hn : n₀ ≤ n) (hnL : n₀ ≤ n * L) (c c' : TorusBond n) :
    IsTermBound (qc E M θ) (θ / L) r (blockCentre L c.1) (blockCentre L c'.1)
      (fun y b b' => d (n * L) y b b' (Z n c X b) (Z n c' X b')) := by
  intro y b b'
  have h1 := tangent_fine hD hL hM hθ hn c b
  have h2 := tangent_fine hD hL hM hθ hn c' b'
  refine (hD.bound (n * L) hnL y b b' _ _).trans ?_
  calc ‖Z n c X b‖ * ‖Z n c' X b'‖ * (E * Real.exp (-(r * (supportDiam y ![b, b'] : ℝ))))
      ≤ ((M * Real.exp θ) * Real.exp (-(θ / L * (_root_.YangMills.Construction.TorusFields.supDist b.1 (blockCentre L c.1) : ℝ)))) *
        ((M * Real.exp θ) * Real.exp (-(θ / L * (_root_.YangMills.Construction.TorusFields.supDist b'.1 (blockCentre L c'.1) : ℝ)))) *
          (E * Real.exp (-(r * (supportDiam y ![b, b'] : ℝ)))) := by
        gcongr
    _ = _ := by
        unfold qc
        ring
private theorem kern_decay (hD : IsData L n₀ E r M θ d Z X) (hL : 0 < L) (hE : 0 ≤ E) (hM : 0 ≤ M) (hr : 0 < r)
    (hθ : 0 < θ) {n : ℕ} [NeZero n] [NeZero (n * L)] (hn : n₀ ≤ n) (hnL : n₀ ≤ n * L) (c c' : TorusBond n) :
    |kern L d Z X n c c'| ≤ (qc E M θ * Real.exp (2 * κc L r θ) * gwSum (κc L r θ)) *
      Real.exp (-(2 * κc L r θ * (_root_.YangMills.Construction.TorusFields.supDist c.1 c'.1 : ℝ))) := by
  have hκ := κc_pos hL hr hθ
  obtain ⟨h1, h2⟩ := κc_le (L := L) hL hr hθ
  have hq : 0 ≤ qc E M θ := by
    unfold qc
    positivity
  have hG := gwSum_nonneg hκ
  have h := kernel_decay hq hκ h1 h2 (term_of_data hD hL hE hM hθ hn hnL c c')
  refine h.trans ?_
  have e : Real.exp (-(2 * κc L r θ * (_root_.YangMills.Construction.TorusFields.supDist (blockCentre L c.1) (blockCentre L c'.1) : ℝ))) ≤
      Real.exp (2 * κc L r θ) * Real.exp (-(2 * κc L r θ * (_root_.YangMills.Construction.TorusFields.supDist c.1 c'.1 : ℝ))) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have t : (_root_.YangMills.Construction.TorusFields.supDist c.1 c'.1 : ℝ) ≤ (_root_.YangMills.Construction.TorusFields.supDist (blockCentre L c.1) (blockCentre L c'.1) : ℝ) + 1 := by
      exact_mod_cast coarse_le hL c.1 c'.1
    nlinarith
  calc qc E M θ * Real.exp (-(2 * κc L r θ * (_root_.YangMills.Construction.TorusFields.supDist (blockCentre L c.1) (blockCentre L c'.1) : ℝ))) * gwSum (κc L r θ)
      ≤ qc E M θ * (Real.exp (2 * κc L r θ) * Real.exp (-(2 * κc L r θ * (_root_.YangMills.Construction.TorusFields.supDist c.1 c'.1 : ℝ)))) * gwSum (κc L r θ) := by
        gcongr
    _ = _ := by ring
private def trunc (L : ℕ) (d : (m : ℕ) → TorusSite m → TorusBond m → TorusBond m → imaginaryQuaternions → imaginaryQuaternions → ℝ)
    (Z : (n : ℕ) → TorusBond n → imaginaryQuaternions → TorusBond (n * L) → imaginaryQuaternions) (X : imaginaryQuaternions)
    (w : ℕ) [NeZero (w * L)] (R : ℕ) (e₀ e₁ : Fin 4 → ℤ) (k₀ k₁ : Fin 4) : ℝ :=
  ∑ z ∈ latBox R, ∑ i : Fin 4, ∑ z' ∈ latBox R, ∑ i' : Fin 4, ∑ ζ ∈ latBox R,
    d (w * L) (siteOfInt ((fun j => (L : ℤ) * e₀ j) + z + ζ)) (siteOfInt ((fun j => (L : ℤ) * e₀ j) + z), i)
      (siteOfInt ((fun j => (L : ℤ) * e₁ j) + z'), i')
      (Z w (siteOfInt e₀, k₀) X (siteOfInt ((fun j => (L : ℤ) * e₀ j) + z), i))
      (Z w (siteOfInt e₁, k₁) X (siteOfInt ((fun j => (L : ℤ) * e₁ j) + z'), i'))
private theorem tail_side (hD : IsData L n₀ E r M θ d Z X) (hL : 0 < L) (hE : 0 ≤ E) (hM : 0 ≤ M) (hr : 0 < r)
    (hθ : 0 < θ) {w : ℕ} [NeZero w] [NeZero (w * L)] (hn : n₀ ≤ w) (hnL : n₀ ≤ w * L) {R : ℕ} (hR : 2 * R ≤ w * L)
    (e₀ e₁ : Fin 4 → ℤ) (k₀ k₁ : Fin 4) :
    |kern L d Z X w (siteOfInt e₀, k₀) (siteOfInt e₁, k₁) - trunc L d Z X w R e₀ e₁ k₀ k₁| ≤
      qc E M θ * Real.exp (-(2 * κc L r θ * R)) * gwSum (κc L r θ) := by
  classical
  have hκ := κc_pos hL hr hθ
  obtain ⟨h1, h2⟩ := κc_le (L := L) hL hr hθ
  have hq : 0 ≤ qc E M θ := by
    unfold qc
    positivity
  have ht := kernel_tail hq hκ h1 h2 (term_of_data hD hL hE hM hθ hn hnL (siteOfInt e₀, k₀) (siteOfInt e₁, k₁)) R
  rw [trunc_eq _ _ hR] at ht
  have ea : blockCentre L (siteOfInt e₀ : TorusSite w) = siteOfInt (fun j => (L : ℤ) * e₀ j) := anchor_of e₀
  have eb : blockCentre L (siteOfInt e₁ : TorusSite w) = siteOfInt (fun j => (L : ℤ) * e₁ j) := anchor_of e₁
  simp only [ea, eb, ← siteOfInt_add] at ht
  unfold kern trunc
  exact ht
end Data
section Compare
variable {L n₀ : ℕ} [NeZero L] {E r M θ : ℝ}
  {d : (m : ℕ) → TorusSite m → TorusBond m → TorusBond m → imaginaryQuaternions → imaginaryQuaternions → ℝ}
  {Z : (n : ℕ) → TorusBond n → imaginaryQuaternions → TorusBond (n * L) → imaginaryQuaternions} {X : imaginaryQuaternions}
private theorem coarseOffset_abs {L : ℕ} (hL : Odd L) {c : ℤ} (hc : 0 ≤ c) {p : Fin 4 → ℤ} {i : Fin 4}
    (hp : |p i| ≤ c * L) : |coarseOffset L p i| ≤ c := by
  obtain ⟨k, hk⟩ := hL
  have hLp : (0 : ℤ) < L := by omega
  have hh2 : ((L : ℤ) - 1) / 2 = k := by omega
  simp only [coarseOffset]
  rw [hh2]
  obtain ⟨h1, h2⟩ := abs_le.mp hp
  rw [abs_le]
  constructor
  · apply Int.le_ediv_of_mul_le hLp
    nlinarith
  · have : (p i + (k : ℤ)) / (L : ℤ) < c + 1 := by
      apply Int.ediv_lt_of_lt_mul hLp
      nlinarith
    omega
abbrev _root_.YangMills.SharedProofs.p21677 := @coarseOffset_abs
private theorem coarseOffset_shift (hL : 0 < L) (e z : Fin 4 → ℤ) (j : Fin 4) :
    coarseOffset L ((fun j => (L : ℤ) * e j) + z) j = e j + coarseOffset L z j := by
  have hL' : (0 : ℤ) < L := by exact_mod_cast hL
  simp only [coarseOffset, Pi.add_apply]
  have : (L : ℤ) * e j + z j + ((L : ℤ) - 1) / 2 = (z j + ((L : ℤ) - 1) / 2) + (L : ℤ) * e j := by ring
  rw [this, Int.add_mul_ediv_left _ _ hL'.ne']
  ring
private theorem box_of {q : ℕ} {v : Fin 4 → ℤ} (hv : ∀ j, |v j| + 1 ≤ (q : ℤ)) (i : Fin 4) :
    BondOffsetInBox q (v, i) := by
  constructor
  · intro j
    have := hv j
    show |v j| ≤ (q : ℤ)
    omega
  · intro j
    have h3 := hv j
    have h4 : |(Pi.single i 1 : Fin 4 → ℤ) j| ≤ 1 := by
      by_cases h : j = i
      · subst h
        simp
      · simp [h]
    show |(v + (Pi.single i 1 : Fin 4 → ℤ)) j| ≤ (q : ℤ)
    simp only [Pi.add_apply]
    exact (abs_add_le _ _).trans (by omega)
private theorem bond_a {m : ℕ} [NeZero m] (u ζ : Fin 4 → ℤ) (i : Fin 4) :
    bondFrom (siteOfInt (u + ζ) : TorusSite m) (-ζ, i) = (siteOfInt u, i) := by
  show ((siteOfInt (u + ζ) + siteOfInt (-ζ) : TorusSite m), i) = _
  rw [← siteOfInt_add]
  simp
private theorem bond_b {m : ℕ} [NeZero m] (u v : Fin 4 → ℤ) (i : Fin 4) :
    bondFrom (siteOfInt v : TorusSite m) (u - v, i) = (siteOfInt u, i) := by
  show ((siteOfInt v + siteOfInt (u - v) : TorusSite m), i) = _
  rw [← siteOfInt_add]
  simp
private theorem three_terms (hD : IsData L n₀ E r M θ d Z X) {m m' : ℕ} [NeZero m] [NeZero m'] (hm' : n₀ ≤ m')
    (hE : 0 ≤ E) (hr : 0 < r) (hM : 0 ≤ M) {y : TorusSite m} {y' : TorusSite m'} {b b' : TorusBond m} {c c' : TorusBond m'}
    {A A' A₂ A₂' : imaginaryQuaternions} {ε δ : ℝ} (a1 : ‖A‖ ≤ M) (a2 : ‖A'‖ ≤ M) (a3 : ‖A₂‖ ≤ M) (a4 : ‖A - A₂‖ ≤ ε)
    (a5 : ‖A' - A₂'‖ ≤ ε) (hδ : 0 ≤ δ) (a6 : |d m y b b' A A' - d m' y' c c' A A'| ≤ ‖A‖ * ‖A'‖ * δ) :
    |d m y b b' A A' - d m' y' c c' A₂ A₂'| ≤ M * M * δ + 2 * (M * ε * E) := by
  have e : d m y b b' A A' - d m' y' c c' A₂ A₂' = (d m y b b' A A' - d m' y' c c' A A') +
      d m' y' c c' (A - A₂) A' + d m' y' c c' A₂ (A' - A₂') := by
    rw [hD.sub_left m' hm', hD.sub_right m' hm']
    ring
  rw [e]
  have hε : 0 ≤ ε := (norm_nonneg _).trans a4
  have x1 : Real.exp (-(r * (supportDiam y' ![c, c'] : ℝ))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : (0 : ℝ) ≤ (supportDiam y' ![c, c'] : ℝ) := by positivity
    nlinarith
  have x2 : E * Real.exp (-(r * (supportDiam y' ![c, c'] : ℝ))) ≤ E := by nlinarith
  have c1 : |d m' y' c c' (A - A₂) A'| ≤ M * ε * E := by
    refine (hD.bound m' hm' y' c c' _ _).trans ?_
    calc ‖A - A₂‖ * ‖A'‖ * (E * Real.exp (-(r * (supportDiam y' ![c, c'] : ℝ)))) ≤ ε * M * E := by gcongr
      _ = _ := by ring
  have c2 : |d m' y' c c' A₂ (A' - A₂')| ≤ M * ε * E := by
    refine (hD.bound m' hm' y' c c' _ _).trans ?_
    gcongr
  have c0 : |d m y b b' A A' - d m' y' c c' A A'| ≤ M * M * δ := by
    refine a6.trans ?_
    gcongr
  calc _ ≤ |d m y b b' A A' - d m' y' c c' A A'| + |d m' y' c c' (A - A₂) A'| + |d m' y' c c' A₂ (A' - A₂')| :=
        (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
    _ ≤ _ := by linarith
private theorem term_close (hD : IsData L n₀ E r M θ d Z X) (hodd : Odd L) (hE : 0 ≤ E) (hM : 0 ≤ M) (hr : 0 < r)
    (hθ : 0 < θ) {n n' : ℕ} [NeZero n] [NeZero n'] [NeZero (n * L)] [NeZero (n' * L)] (hn : n₀ ≤ n) (hnn : n ≤ n')
    (hnL : n₀ ≤ n * L) (hnL' : n₀ ≤ n' * L) (h4 : 4096 ≤ n) {e₀ e₁ : Fin 4 → ℤ} (k₀ k₁ : Fin 4)
    (he₀ : ∀ j, |e₀ j| ≤ 2 * ((n / 16 : ℕ) : ℤ)) (he₁ : ∀ j, |e₁ j| ≤ 2 * ((n / 16 : ℕ) : ℤ)) {z z' ζ : Fin 4 → ℤ}
    (hz : z ∈ latBox (L * (n / 16))) (hz' : z' ∈ latBox (L * (n / 16))) (hζ : ζ ∈ latBox (L * (n / 16))) (i i' : Fin 4) :
    |d (n * L) (siteOfInt ((fun j => (L : ℤ) * e₀ j) + z + ζ)) (siteOfInt ((fun j => (L : ℤ) * e₀ j) + z), i)
        (siteOfInt ((fun j => (L : ℤ) * e₁ j) + z'), i')
        (Z n (siteOfInt e₀, k₀) X (siteOfInt ((fun j => (L : ℤ) * e₀ j) + z), i))
        (Z n (siteOfInt e₁, k₁) X (siteOfInt ((fun j => (L : ℤ) * e₁ j) + z'), i')) -
      d (n' * L) (siteOfInt ((fun j => (L : ℤ) * e₀ j) + z + ζ)) (siteOfInt ((fun j => (L : ℤ) * e₀ j) + z), i)
        (siteOfInt ((fun j => (L : ℤ) * e₁ j) + z'), i')
        (Z n' (siteOfInt e₀, k₀) X (siteOfInt ((fun j => (L : ℤ) * e₀ j) + z), i))
        (Z n' (siteOfInt e₁, k₁) X (siteOfInt ((fun j => (L : ℤ) * e₁ j) + z'), i'))| ≤
      3 * (M * M * E) * Real.exp (-(min r (2 * θ) * ((n / 16 : ℕ) : ℝ))) := by
  obtain ⟨h, hh⟩ : ∃ h, h = n / 16 := ⟨_, rfl⟩
  rw [← hh] at hz hz' hζ he₀ he₁ ⊢
  have hL : 0 < L := hodd.pos
  have hh2 : 256 ≤ h := by omega
  have hh3 : 16 * h ≤ n := by omega
  obtain ⟨R, hR⟩ : ∃ R, R = L * h := ⟨_, rfl⟩
  rw [← hR] at hz hz' hζ
  have hRh : h ≤ R := by
    rw [hR]
    exact Nat.le_mul_of_pos_left _ hL
  have hRn : 16 * R ≤ n * L := by
    rw [hR]
    calc 16 * (L * h) = (16 * h) * L := by ring
      _ ≤ n * L := Nat.mul_le_mul_right _ hh3
  have hRn' : 16 * R ≤ n' * L := hRn.trans (Nat.mul_le_mul_right _ hnn)
  obtain ⟨u₀, hu₀⟩ : ∃ u₀, u₀ = (fun j => (L : ℤ) * e₀ j) + z := ⟨_, rfl⟩
  obtain ⟨u₁, hu₁⟩ : ∃ u₁, u₁ = (fun j => (L : ℤ) * e₁ j) + z' := ⟨_, rfl⟩
  rw [← hu₀, ← hu₁]
  have hκ₂ : min r (2 * θ) ≤ r := min_le_left _ _
  have hκ₂' : min r (2 * θ) ≤ 2 * θ := min_le_right _ _
  obtain ⟨ex, hex⟩ : ∃ ex, ex = Real.exp (-(min r (2 * θ) * (h : ℝ))) := ⟨_, rfl⟩
  have hex0 : 0 ≤ ex := by
    rw [hex]
    positivity
  have tb : ∀ (w : ℕ) [NeZero w], n₀ ≤ w → ∀ (c : TorusBond w) (b : TorusBond (w * L)), ‖Z w c X b‖ ≤ M := by
    intro w _ hw c b
    refine (hD.tan_bound w hw c b).trans ?_
    have : Real.exp (-(θ * (_root_.YangMills.Construction.TorusFields.supDist (parentBlock L b.1) c.1 : ℝ))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : (0 : ℝ) ≤ (_root_.YangMills.Construction.TorusFields.supDist (parentBlock L b.1) c.1 : ℝ) := by positivity
      nlinarith
    nlinarith
  have hn' : n₀ ≤ n' := hn.trans hnn
  have tcomp : ∀ (e z₀ : Fin 4 → ℤ) (k l : Fin 4), (∀ j, (1 - (R : ℤ)) ≤ z₀ j ∧ z₀ j ≤ (R : ℤ) - 1) →
      ‖Z n (siteOfInt e, k) X (siteOfInt ((fun j => (L : ℤ) * e j) + z₀), l) -
        Z n' (siteOfInt e, k) X (siteOfInt ((fun j => (L : ℤ) * e j) + z₀), l)‖ ≤ M * ex := by
    intro e z₀ k l hb
    have hc : ∀ j, |e j - coarseOffset L ((fun j => (L : ℤ) * e j) + z₀) j| + 1 ≤ ((2 * h : ℕ) : ℤ) := by
      intro j
      rw [coarseOffset_shift hL]
      have h1 : |z₀ j| ≤ (h : ℤ) * L := by
        have e1 : (R : ℤ) = (h : ℤ) * L := by
          rw [hR]
          push_cast
          ring
        have := hb j
        rw [abs_le]
        constructor <;> omega
      have h2 := coarseOffset_abs hodd (c := (h : ℤ)) (by positivity) h1
      have e2 : e j - (e j + coarseOffset L z₀ j) = -coarseOffset L z₀ j := by ring
      rw [e2, abs_neg]
      push_cast
      omega
    refine (hD.tan_compare n n' (2 * h) _ e l k hn hn' (by omega) (by omega) (by omega) hc).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hM
    rw [hex]
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith
  have hzb := mem_latBox.mp hz
  have hzb' := mem_latBox.mp hz'
  have hζb := mem_latBox.mp hζ
  obtain ⟨q, hq⟩ : ∃ q, q = 7 * R + 1 := ⟨_, rfl⟩
  have hb₀ : BondOffsetInBox q (-ζ, i) := box_of (fun j => by
    have := hζb j
    show |(-ζ) j| + 1 ≤ (q : ℤ)
    simp only [Pi.neg_apply, abs_neg]
    have e1 : |ζ j| ≤ (R : ℤ) := abs_le.mpr ⟨by omega, by omega⟩
    omega) i
  have hLe : ∀ (e : Fin 4 → ℤ), (∀ j, |e j| ≤ 2 * (h : ℤ)) → ∀ j, |(L : ℤ) * e j| ≤ 2 * (R : ℤ) := by
    intro e he j
    rw [abs_mul, abs_of_pos (by exact_mod_cast hL : (0 : ℤ) < L), hR]
    push_cast
    have := he j
    nlinarith
  have hb₁ : BondOffsetInBox q (u₁ - (u₀ + ζ), i') := box_of (fun j => by
    have a1 := abs_le.mp (hLe e₀ he₀ j)
    have a2 := abs_le.mp (hLe e₁ he₁ j)
    have a3 := hζb j
    have a4 := hzb j
    have a5 := hzb' j
    show |(u₁ - (u₀ + ζ)) j| + 1 ≤ (q : ℤ)
    rw [hu₀, hu₁]
    simp only [Pi.sub_apply, Pi.add_apply]
    have : |(L : ℤ) * e₁ j + z' j - ((L : ℤ) * e₀ j + z j + ζ j)| ≤ 7 * (R : ℤ) := by
      rw [abs_le]
      constructor <;> omega
    rw [hq]
    push_cast
    omega) i'
  have hq2 : 2 * q + 2 < n * L := by omega
  have hq2' : 2 * q + 2 < n' * L := by omega
  have hc := hD.compare (n * L) (n' * L) hnL hnL' (siteOfInt (u₀ + ζ)) (siteOfInt (u₀ + ζ)) q hq2 hq2' _ _ hb₀ hb₁
    (Z n (siteOfInt e₀, k₀) X (siteOfInt u₀, i)) (Z n (siteOfInt e₁, k₁) X (siteOfInt u₁, i'))
  rw [bond_a, bond_a, bond_b, bond_b] at hc
  have hqh : (h : ℝ) ≤ (q : ℝ) := by
    have : h ≤ q := by omega
    exact_mod_cast this
  have a6 : E * Real.exp (-(r * (q : ℝ))) ≤ E * ex := by
    refine mul_le_mul_of_nonneg_left ?_ hE
    rw [hex]
    apply Real.exp_le_exp.mpr
    nlinarith
  have h3 := three_terms hD (m := n * L) (m' := n' * L) hnL' hE hr hM (y := siteOfInt (u₀ + ζ)) (y' := siteOfInt (u₀ + ζ))
    (b := (siteOfInt u₀, i)) (b' := (siteOfInt u₁, i')) (c := (siteOfInt u₀, i)) (c' := (siteOfInt u₁, i'))
    (A := Z n (siteOfInt e₀, k₀) X (siteOfInt u₀, i)) (A' := Z n (siteOfInt e₁, k₁) X (siteOfInt u₁, i'))
    (A₂ := Z n' (siteOfInt e₀, k₀) X (siteOfInt u₀, i)) (A₂' := Z n' (siteOfInt e₁, k₁) X (siteOfInt u₁, i'))
    (ε := M * ex) (δ := E * ex) (tb n hn _ _) (tb n hn _ _) (tb n' hn' _ _)
    (by rw [hu₀]; exact tcomp e₀ z k₀ i hzb) (by rw [hu₁]; exact tcomp e₁ z' k₁ i' hzb') (by positivity)
    (hc.trans (by gcongr))
  refine h3.trans (le_of_eq ?_)
  rw [← hex]
  ring
private theorem abs_sum_sub_le {ι : Type*} (s : Finset ι) (f g : ι → ℝ) {B : ℝ} (h : ∀ i ∈ s, |f i - g i| ≤ B) :
    |∑ i ∈ s, f i - ∑ i ∈ s, g i| ≤ s.card * B := by
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ _i ∈ s, B := Finset.sum_le_sum h
    _ = _ := by simp
private theorem kern_compare (hD : IsData L n₀ E r M θ d Z X) (hodd : Odd L) (hE : 0 ≤ E) (hM : 0 ≤ M) (hr : 0 < r)
    (hθ : 0 < θ) {n n' : ℕ} [NeZero n] [NeZero n'] [NeZero (n * L)] [NeZero (n' * L)] (hn : n₀ ≤ n) (hnn : n ≤ n')
    (hnL : n₀ ≤ n * L) (hnL' : n₀ ≤ n' * L) (h4 : 4096 ≤ n) {e₀ e₁ : Fin 4 → ℤ} (k₀ k₁ : Fin 4)
    (he₀ : ∀ j, |e₀ j| ≤ 2 * ((n / 16 : ℕ) : ℤ)) (he₁ : ∀ j, |e₁ j| ≤ 2 * ((n / 16 : ℕ) : ℤ)) :
    |kern L d Z X n (siteOfInt e₀, k₀) (siteOfInt e₁, k₁) - kern L d Z X n' (siteOfInt e₀, k₀) (siteOfInt e₁, k₁)| ≤
      2 * (qc E M θ * Real.exp (-(2 * κc L r θ * ((L * (n / 16) : ℕ) : ℝ))) * gwSum (κc L r θ)) +
        ((2 * ((L * (n / 16) : ℕ) : ℝ)) ^ 4) ^ 3 * 16 *
          (3 * (M * M * E) * Real.exp (-(min r (2 * θ) * ((n / 16 : ℕ) : ℝ)))) := by
  have hL : 0 < L := hodd.pos
  obtain ⟨R, hR⟩ : ∃ R, R = L * (n / 16) := ⟨_, rfl⟩
  have h16 : 16 * (n / 16) ≤ n := by omega
  have hRn : 2 * R ≤ n * L := by
    rw [hR]
    calc 2 * (L * (n / 16)) ≤ 16 * (n / 16) * L := by nlinarith
      _ ≤ n * L := Nat.mul_le_mul_right _ h16
  have hRn' : 2 * R ≤ n' * L := hRn.trans (Nat.mul_le_mul_right _ hnn)
  rw [← hR]
  have t1 := tail_side (R := R) hD hL hE hM hr (by exact hθ) hn hnL hRn e₀ e₁ k₀ k₁
  have t2 := tail_side (R := R) hD hL hE hM hr (by exact hθ) (hn.trans hnn) hnL' hRn' e₀ e₁ k₀ k₁
  obtain ⟨B, hB⟩ : ∃ B, B = 3 * (M * M * E) * Real.exp (-(min r (2 * θ) * ((n / 16 : ℕ) : ℝ))) := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by
    rw [hB]
    positivity
  rw [← hB]
  have t3 : |trunc L d Z X n R e₀ e₁ k₀ k₁ - trunc L d Z X n' R e₀ e₁ k₀ k₁| ≤
      ((2 * (R : ℝ)) ^ 4) ^ 3 * 16 * B := by
    have hc := card_latBox R
    have hc0 : (0 : ℝ) ≤ ((latBox R).card : ℝ) := by positivity
    have main : |trunc L d Z X n R e₀ e₁ k₀ k₁ - trunc L d Z X n' R e₀ e₁ k₀ k₁| ≤
        ((latBox R).card : ℝ) * (4 * (((latBox R).card : ℝ) * (4 * (((latBox R).card : ℝ) * B)))) := by
      unfold trunc
      refine abs_sum_sub_le _ _ _ fun z hz => ?_
      have e4 : ((Finset.univ : Finset (Fin 4)).card : ℝ) = 4 := by simp
      rw [← e4]
      refine abs_sum_sub_le _ _ _ fun i _ => ?_
      refine abs_sum_sub_le _ _ _ fun z' hz' => ?_
      refine abs_sum_sub_le _ _ _ fun i' _ => ?_
      refine abs_sum_sub_le _ _ _ fun ζ hζ => ?_
      rw [hB]
      have := term_close hD hodd hE hM hr hθ hn hnn hnL hnL' h4 k₀ k₁ he₀ he₁ (hR ▸ hz) (hR ▸ hz') (hR ▸ hζ) i i'
      exact this
    refine main.trans ?_
    have hp : (0 : ℝ) ≤ (2 * (R : ℝ)) ^ 4 := by positivity
    calc ((latBox R).card : ℝ) * (4 * (((latBox R).card : ℝ) * (4 * (((latBox R).card : ℝ) * B))))
        ≤ (2 * (R : ℝ)) ^ 4 * (4 * ((2 * (R : ℝ)) ^ 4 * (4 * ((2 * (R : ℝ)) ^ 4 * B)))) := by gcongr
      _ = _ := by ring
  have e : kern L d Z X n (siteOfInt e₀, k₀) (siteOfInt e₁, k₁) - kern L d Z X n' (siteOfInt e₀, k₀) (siteOfInt e₁, k₁) =
      (kern L d Z X n (siteOfInt e₀, k₀) (siteOfInt e₁, k₁) - trunc L d Z X n R e₀ e₁ k₀ k₁) +
        (trunc L d Z X n R e₀ e₁ k₀ k₁ - trunc L d Z X n' R e₀ e₁ k₀ k₁) -
        (kern L d Z X n' (siteOfInt e₀, k₀) (siteOfInt e₁, k₁) - trunc L d Z X n' R e₀ e₁ k₀ k₁) := by ring
  rw [e]
  refine (abs_sub _ _).trans ?_
  refine (add_le_add (abs_add_le _ _) le_rfl).trans ?_
  linarith
end Compare
section Moment
private theorem valMinAbs_of {n : ℕ} [NeZero n] {z : ℤ} (h : 2 * z.natAbs + 1 < n) :
    ((z : ZMod n)).valMinAbs = z := by
  refine (ZMod.valMinAbs_spec _ _).mpr ⟨rfl, ?_, ?_⟩ <;> omega
private theorem pow_mul_exp_le {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) (k : ℕ) :
    x ^ k * Real.exp (-(a * x)) ≤ k.factorial / a ^ k := by
  have h := Real.pow_div_factorial_le_exp (a * x) (by positivity) k
  have hf : (0 : ℝ) < k.factorial := by positivity
  rw [div_le_iff₀ hf] at h
  rw [le_div_iff₀ (by positivity), Real.exp_neg]
  have e : x ^ k * (Real.exp (a * x))⁻¹ * a ^ k = (a * x) ^ k / Real.exp (a * x) := by
    rw [mul_pow, div_eq_mul_inv]
    ring
  rw [e, div_le_iff₀ (Real.exp_pos _)]
  linarith [mul_comm (Real.exp (a * x)) (k.factorial : ℝ)]
private theorem le_size (z : Fin 4 → ℤ) (i : Fin 4) : (z i).natAbs ≤ offsetNorm z := by apply _root_.YangMills.Construction.LatticePaths.natAbs_le_supNorm <;> assumption
private theorem sum_lattice_le {a : ℝ} (ha : 0 < a) (u : Finset (Fin 4 → ℤ)) :
    ∑ z ∈ u, Real.exp (-(a * (offsetNorm z : ℝ))) ≤ siteSum a := by
  classical
  obtain ⟨B, hB⟩ : ∃ B : ℕ, ∀ z ∈ u, offsetNorm z ≤ B := ⟨u.sup offsetNorm, fun z hz => Finset.le_sup hz⟩
  haveI : NeZero (2 * B + 3) := ⟨by omega⟩
  have hinj : Set.InjOn (fun z => (siteOfInt z : TorusSite (2 * B + 3))) (u : Set (Fin 4 → ℤ)) := by
    intro z hz z' hz' h
    refine eq_of_siteOfInt_eq h fun i => ?_
    have h1 := le_size z i
    have h2 := le_size z' i
    have h3 := hB z hz
    have h4 := hB z' hz'
    rw [abs_lt]
    push_cast
    omega
  calc ∑ z ∈ u, Real.exp (-(a * (offsetNorm z : ℝ)))
      ≤ ∑ z ∈ u, Real.exp (-a * (_root_.YangMills.Construction.TorusFields.supDist (siteOfInt z : TorusSite (2 * B + 3)) 0 : ℝ)) := by
        refine Finset.sum_le_sum fun z _ => Real.exp_le_exp.mpr ?_
        have h1 := _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le (0 : TorusSite (2 * B + 3)) z (offsetNorm z) (le_size z)
        rw [zero_add, _root_.YangMills.Construction.TorusFields.supDist_comm] at h1
        have h2 : (_root_.YangMills.Construction.TorusFields.supDist (siteOfInt z : TorusSite (2 * B + 3)) 0 : ℝ) ≤ (offsetNorm z : ℝ) := by exact_mod_cast h1
        nlinarith
    _ = ∑ w ∈ u.image (fun z => (siteOfInt z : TorusSite (2 * B + 3))), Real.exp (-a * (_root_.YangMills.Construction.TorusFields.supDist w 0 : ℝ)) :=
        (Finset.sum_image (f := fun w : TorusSite (2 * B + 3) => Real.exp (-a * (_root_.YangMills.Construction.TorusFields.supDist w 0 : ℝ))) hinj).symm
    _ ≤ ∑ w : TorusSite (2 * B + 3), Real.exp (-a * (_root_.YangMills.Construction.TorusFields.supDist w 0 : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => (Real.exp_pos _).le
    _ ≤ siteSum a := sum_sites ha 0
private theorem tail_of_sum {f : (Fin 4 → ℤ) → ℝ} (hf : HasSum f 0) (s : Finset (Fin 4 → ℤ)) {B : ℝ}
    (hB : ∀ u : Finset (Fin 4 → ℤ), Disjoint u s → ∑ z ∈ u, |f z| ≤ B) : |∑ z ∈ s, f z| ≤ B := by
  classical
  have ht : Tendsto (fun t : Finset (Fin 4 → ℤ) => |∑ z ∈ t, f z - ∑ z ∈ s, f z|) atTop (𝓝 |0 - ∑ z ∈ s, f z|) :=
    (hf.sub_const _).abs
  have h0 : |0 - ∑ z ∈ s, f z| = |∑ z ∈ s, f z| := by
    rw [zero_sub, abs_neg]
  rw [← h0]
  refine le_of_tendsto ht ?_
  filter_upwards [eventually_ge_atTop s] with t ht'
  rw [← Finset.sum_sdiff ht', add_sub_cancel_right]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (hB _ Finset.sdiff_disjoint)
set_option maxHeartbeats 1600000 in
private theorem moment_small {C₁ κ₁ C₂ κ₂ : ℝ} (hC₁ : 0 ≤ C₁) (hκ₁ : 0 < κ₁) (hC₂ : 0 ≤ C₂) (hκ₂ : 0 < κ₂) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (n₀ : ℕ) (kn : (n : ℕ) → TorusBond n → TorusBond n → ℝ) (Kl : LatticeBond → LatticeBond → ℝ),
      4096 ≤ n₀ →
      (∀ (n : ℕ) [NeZero n], n₀ ≤ n → ∀ c c' : TorusBond n, |kn n c c'| ≤ C₁ * Real.exp (-(κ₁ * (_root_.YangMills.Construction.TorusFields.supDist c.1 c'.1 : ℝ)))) →
      (∀ (n n' : ℕ) [NeZero n] [NeZero n'], n₀ ≤ n → n ≤ n' → ∀ (e₀ e₁ : Fin 4 → ℤ) (k₀ k₁ : Fin 4),
        (∀ j, |e₀ j| ≤ 2 * ((n / 16 : ℕ) : ℤ)) → (∀ j, |e₁ j| ≤ 2 * ((n / 16 : ℕ) : ℤ)) →
        |kn n (siteOfInt e₀, k₀) (siteOfInt e₁, k₁) - kn n' (siteOfInt e₀, k₀) (siteOfInt e₁, k₁)| ≤
          C₂ * Real.exp (-(κ₂ * ((n / 16 : ℕ) : ℝ)))) →
      (∀ c c' : LatticeBond, Tendsto (fun n => kn n (bondFrom 0 c) (bondFrom 0 c')) atTop (𝓝 (Kl c c'))) →
      HasSum (secondMomentTerm Kl) 0 →
      ∀ (n : ℕ) [NeZero n], n₀ ≤ n → |kernelSecondMoment (kn n)| ≤ C * Real.exp (-(c * (n : ℝ))) := by
  obtain ⟨a, ha⟩ : ∃ a, a = κ₁ / 3 := ⟨_, rfl⟩
  have ha0 : 0 < a := by
    rw [ha]
    positivity
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = (Nat.factorial 6 : ℝ) / (κ₂ / 2) ^ 6 := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by
    rw [hP]
    positivity
  obtain ⟨Cf, hCf⟩ : ∃ Cf : ℝ, Cf = C₁ / a ^ 2 := ⟨_, rfl⟩
  have hCf0 : 0 ≤ Cf := by
    rw [hCf]
    positivity
  have hS := siteSum_nonneg ha0
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, c₀ = min (κ₂ / 2) a := ⟨_, rfl⟩
  have hc₀p : 0 < c₀ := by
    rw [hc₀]
    exact lt_min (by positivity) ha0
  refine ⟨2592 * P * C₂ + Cf * siteSum a + 1, c₀ / 32, by positivity, by positivity, ?_⟩
  intro n₀ kn Kl h4 hU hT hlim hsum n _ hn
  obtain ⟨h, hh⟩ : ∃ h, h = n / 16 := ⟨_, rfl⟩
  have hh2 : 256 ≤ h := by omega
  have hhr : (256 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh2
  have hKl : ∀ z : Fin 4 → ℤ, |Kl (0, secondAxis) (z, secondAxis)| ≤
      C₁ * Real.exp (-(κ₁ * (offsetNorm z : ℝ))) := by
    intro z
    refine le_of_tendsto (hlim (0, secondAxis) (z, secondAxis)).abs ?_
    filter_upwards [eventually_ge_atTop (max n₀ (2 * offsetNorm z + 2))] with w hw
    have h1 : n₀ ≤ w := (le_max_left _ _).trans hw
    have h2 : 2 * offsetNorm z + 2 ≤ w := (le_max_right _ _).trans hw
    haveI : NeZero w := ⟨by omega⟩
    refine (hU w h1 _ _).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC₁
    have hs : offsetNorm z ≤ _root_.YangMills.Construction.TorusFields.supDist (bondFrom (0 : TorusSite w) (0, secondAxis)).1 (bondFrom (0 : TorusSite w) (z, secondAxis)).1 := by
      rw [supDist_comm]
      refine Finset.sup_le fun i _ => ?_
      have h3 := (_root_.YangMills.Construction.TorusFields.supDist_le_iff (bondFrom (0 : TorusSite w) (z, secondAxis)).1 (bondFrom (0 : TorusSite w) (0, secondAxis)).1 _).mp le_rfl i
      have e : (bondFrom (0 : TorusSite w) (z, secondAxis)).1 i - (bondFrom (0 : TorusSite w) (0, secondAxis)).1 i =
          ((z i : ℤ) : ZMod w) := by
        simp [bondFrom, siteOfInt]
      rw [e, valMinAbs_of (by have := le_size z i; omega)] at h3
      exact h3
    have hs' : (offsetNorm z : ℝ) ≤ (_root_.YangMills.Construction.TorusFields.supDist (bondFrom (0 : TorusSite w) (0, secondAxis)).1 (bondFrom (0 : TorusSite w) (z, secondAxis)).1 : ℝ) := by
      exact_mod_cast hs
    nlinarith
  have hclose : ∀ z : Fin 4 → ℤ, (∀ j, |z j| ≤ 2 * (h : ℤ)) →
      |kn n (siteOfInt 0, secondAxis) (siteOfInt z, secondAxis) - Kl (0, secondAxis) (z, secondAxis)| ≤
        C₂ * Real.exp (-(κ₂ * (h : ℝ))) := by
    intro z hz
    refine le_of_tendsto (((hlim (0, secondAxis) (z, secondAxis)).const_sub _).abs) ?_
    filter_upwards [eventually_ge_atTop n] with w hw
    haveI : NeZero w := ⟨by omega⟩
    have e0 : ∀ e : LatticeBond, bondFrom (0 : TorusSite w) e = (siteOfInt e.1, e.2) := fun e => by
      simp [bondFrom]
    rw [e0, e0]
    have := hT n w hn hw 0 z secondAxis secondAxis (fun j => by simp only [Pi.zero_apply, abs_zero]; positivity) (by rw [← hh]; exact hz)
    rw [← hh] at this
    exact this
  have hρ : 2 * (2 * h + 1) ≤ n := by omega
  have hmom : kernelSecondMoment (kn n) = ∑ z ∈ latBox (2 * h + 1),
      (-(1 / 2) * kn n (siteOfInt 0, secondAxis) (siteOfInt z, secondAxis) * ((z 0 : ℤ) : ℝ) ^ 2) := by
    classical
    unfold kernelSecondMoment momentCutoff
    rw [← hh]
    have e1 : (∑ y : TorusSite n, if _root_.YangMills.Construction.TorusFields.supDist 0 y ≤ 2 * h then
        ((firstCoordDiff 0 y : ℤ) : ℝ) ^ 2 * kn n (0, secondAxis) (y, secondAxis) else 0) =
        ∑ y : TorusSite n, if _root_.YangMills.Construction.TorusFields.supDist y 0 < 2 * h + 1 then
        ((firstCoordDiff 0 y : ℤ) : ℝ) ^ 2 * kn n (0, secondAxis) (y, secondAxis) else 0 := by
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [supDist_comm]
      by_cases hy : _root_.YangMills.Construction.TorusFields.supDist y 0 ≤ 2 * h
      · rw [if_pos hy, if_pos (by omega)]
      · rw [if_neg hy, if_neg (by omega)]
    rw [e1, sum_ball 0 hρ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z hz => ?_
    have hzb := mem_latBox.mp hz
    have e2 : firstCoordDiff 0 (0 + siteOfInt z : TorusSite n) = z 0 := by
      unfold firstCoordDiff
      have e3 : ((0 + siteOfInt z : TorusSite n) 0 - (0 : TorusSite n) 0) = ((z 0 : ℤ) : ZMod n) := by
        simp [siteOfInt]
      rw [e3]
      refine valMinAbs_of ?_
      have := hzb 0
      omega
    have e4 : (siteOfInt 0 : TorusSite n) = 0 := siteOfInt_zero_offset
    rw [e2, zero_add, e4]
    ring
  have hcard : ((latBox (2 * h + 1)).card : ℝ) ≤ (6 * (h : ℝ)) ^ 4 := by
    refine (card_latBox _).trans ?_
    push_cast
    exact pow_le_pow_left₀ (by positivity) (by nlinarith) 4
  have hfirst : |kernelSecondMoment (kn n) - ∑ z ∈ latBox (2 * h + 1), secondMomentTerm Kl z| ≤
      ((latBox (2 * h + 1)).card : ℝ) * (2 * (h : ℝ) ^ 2 * (C₂ * Real.exp (-(κ₂ * (h : ℝ))))) := by
    rw [hmom]
    refine abs_sum_sub_le _ _ _ fun z hz => ?_
    have hzb := mem_latBox.mp hz
    have hz2 : ∀ j, |z j| ≤ 2 * (h : ℤ) := fun j => by
      have := hzb j
      push_cast at this
      exact abs_le.mpr ⟨by omega, by omega⟩
    have hc := hclose z hz2
    unfold secondMomentTerm
    have e : -(1 / 2) * kn n (siteOfInt 0, secondAxis) (siteOfInt z, secondAxis) * ((z 0 : ℤ) : ℝ) ^ 2 -
        -(1 / 2) * Kl (0, secondAxis) (z, secondAxis) * ((z 0 : ℤ) : ℝ) ^ 2 =
        -(1 / 2) * ((z 0 : ℤ) : ℝ) ^ 2 * (kn n (siteOfInt 0, secondAxis) (siteOfInt z, secondAxis) -
          Kl (0, secondAxis) (z, secondAxis)) := by ring
    rw [e, abs_mul, abs_mul]
    have hz0 : |((z 0 : ℤ) : ℝ)| ≤ 2 * (h : ℝ) := by
      have := hz2 0
      have h5 : ((|z 0| : ℤ) : ℝ) ≤ ((2 * (h : ℤ) : ℤ) : ℝ) := by exact_mod_cast this
      simpa using h5
    have hsq : |((z 0 : ℤ) : ℝ) ^ 2| ≤ (2 * (h : ℝ)) ^ 2 := by
      rw [abs_pow]
      gcongr
    have h1 : |(-(1 / 2) : ℝ)| = 1 / 2 := by
      rw [abs_neg, abs_of_pos (by norm_num)]
    rw [h1]
    calc 1 / 2 * |((z 0 : ℤ) : ℝ) ^ 2| * |kn n (siteOfInt 0, secondAxis) (siteOfInt z, secondAxis) -
          Kl (0, secondAxis) (z, secondAxis)|
        ≤ 1 / 2 * (2 * (h : ℝ)) ^ 2 * (C₂ * Real.exp (-(κ₂ * (h : ℝ)))) := by gcongr
      _ = _ := by ring
  have hsecond : |∑ z ∈ latBox (2 * h + 1), secondMomentTerm Kl z| ≤ Cf * Real.exp (-(a * (h : ℝ))) * siteSum a := by
    refine tail_of_sum hsum _ fun u hu => ?_
    have hterm : ∀ z ∈ u, |secondMomentTerm Kl z| ≤ Cf * Real.exp (-(a * (h : ℝ))) * Real.exp (-(a * (offsetNorm z : ℝ))) := by
      intro z hz
      have hnot : z ∉ latBox (2 * h + 1) := Finset.disjoint_left.mp hu hz
      have hbig : (h : ℝ) ≤ (offsetNorm z : ℝ) := by
        have : h ≤ offsetNorm z := by
          by_contra hlt
          refine hnot (mem_latBox.mpr fun i => ?_)
          have := le_size z i
          push_cast
          omega
        exact_mod_cast this
      obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (offsetNorm z : ℝ) := ⟨_, rfl⟩
      rw [← hs] at hbig ⊢
      have hs0 : 0 ≤ s := by
        rw [hs]
        positivity
      have hz0 : |((z 0 : ℤ) : ℝ)| ≤ s := by
        rw [hs]
        have := le_size z 0
        have h5 : ((z 0).natAbs : ℝ) ≤ (offsetNorm z : ℝ) := by exact_mod_cast this
        rwa [Nat.cast_natAbs, Int.cast_abs] at h5
      have hp := pow_mul_exp_le ha0 hs0 2
      have h2 : (Nat.factorial 2 : ℝ) = 2 := by norm_num
      rw [h2] at hp
      unfold secondMomentTerm
      rw [abs_mul, abs_mul, abs_pow]
      have h1 : |(-(1 / 2) : ℝ)| = 1 / 2 := by
        rw [abs_neg, abs_of_pos (by norm_num)]
      rw [h1]
      have hk := hKl z
      rw [← hs] at hk
      have e3 : Real.exp (-(κ₁ * s)) = Real.exp (-(a * s)) * Real.exp (-(a * s)) * Real.exp (-(a * s)) := by
        rw [← Real.exp_add, ← Real.exp_add, ha]
        congr 1
        ring
      have hq : Real.exp (-(a * s)) ≤ Real.exp (-(a * (h : ℝ))) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      have hsq : |((z 0 : ℤ) : ℝ)| ^ 2 ≤ s ^ 2 := by gcongr
      obtain ⟨E₁, hE₁⟩ : ∃ E₁, E₁ = Real.exp (-(a * s)) := ⟨_, rfl⟩
      have hE₁0 : 0 ≤ E₁ := by
        rw [hE₁]
        positivity
      rw [← hE₁] at e3 hq hp ⊢
      rw [e3] at hk
      calc 1 / 2 * |Kl (0, secondAxis) (z, secondAxis)| * |((z 0 : ℤ) : ℝ)| ^ 2
          ≤ 1 / 2 * (C₁ * (E₁ * E₁ * E₁)) * s ^ 2 := by gcongr
        _ = 1 / 2 * C₁ * (s ^ 2 * E₁) * E₁ * E₁ := by ring
        _ ≤ 1 / 2 * C₁ * (2 / a ^ 2) * Real.exp (-(a * (h : ℝ))) * E₁ := by gcongr
        _ = _ := by
            rw [hCf]
            ring
    calc ∑ z ∈ u, |secondMomentTerm Kl z|
        ≤ ∑ z ∈ u, Cf * Real.exp (-(a * (h : ℝ))) * Real.exp (-(a * (offsetNorm z : ℝ))) :=
          Finset.sum_le_sum hterm
      _ = Cf * Real.exp (-(a * (h : ℝ))) * ∑ z ∈ u, Real.exp (-(a * (offsetNorm z : ℝ))) := by
          rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_lattice_le ha0 u) (by positivity)
  have hpow := pow_mul_exp_le (a := κ₂ / 2) (x := (h : ℝ)) (by positivity) (by positivity) 6
  rw [← hP] at hpow
  have hexp : Real.exp (-(κ₂ * (h : ℝ))) = Real.exp (-(κ₂ / 2 * (h : ℝ))) * Real.exp (-(κ₂ / 2 * (h : ℝ))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hfin : Real.exp (-(c₀ * (h : ℝ))) ≤ Real.exp (-(c₀ / 32 * (n : ℝ))) := by
    apply Real.exp_le_exp.mpr
    have : (n : ℝ) ≤ 32 * (h : ℝ) := by
      have h6 : n ≤ 32 * h := by omega
      exact_mod_cast h6
    nlinarith
  have hA : Real.exp (-(κ₂ / 2 * (h : ℝ))) ≤ Real.exp (-(c₀ * (h : ℝ))) := by
    apply Real.exp_le_exp.mpr
    have : c₀ ≤ κ₂ / 2 := by
      rw [hc₀]
      exact min_le_left _ _
    nlinarith
  have hB : Real.exp (-(a * (h : ℝ))) ≤ Real.exp (-(c₀ * (h : ℝ))) := by
    apply Real.exp_le_exp.mpr
    have : c₀ ≤ a := by
      rw [hc₀]
      exact min_le_right _ _
    nlinarith
  obtain ⟨F, hF⟩ : ∃ F, F = Real.exp (-(κ₂ / 2 * (h : ℝ))) := ⟨_, rfl⟩
  have hF0 : 0 ≤ F := by
    rw [hF]
    positivity
  rw [← hF] at hexp hpow hA
  have t1 : ((latBox (2 * h + 1)).card : ℝ) * (2 * (h : ℝ) ^ 2 * (C₂ * Real.exp (-(κ₂ * (h : ℝ))))) ≤
      2592 * P * C₂ * Real.exp (-(c₀ * (h : ℝ))) := by
    rw [hexp]
    calc ((latBox (2 * h + 1)).card : ℝ) * (2 * (h : ℝ) ^ 2 * (C₂ * (F * F)))
        ≤ (6 * (h : ℝ)) ^ 4 * (2 * (h : ℝ) ^ 2 * (C₂ * (F * F))) := by gcongr
      _ = 2592 * C₂ * ((h : ℝ) ^ 6 * F) * F := by ring
      _ ≤ 2592 * C₂ * P * Real.exp (-(c₀ * (h : ℝ))) := by gcongr
      _ = _ := by ring
  have t2 : Cf * Real.exp (-(a * (h : ℝ))) * siteSum a ≤ Cf * siteSum a * Real.exp (-(c₀ * (h : ℝ))) := by
    calc Cf * Real.exp (-(a * (h : ℝ))) * siteSum a ≤ Cf * Real.exp (-(c₀ * (h : ℝ))) * siteSum a := by gcongr
      _ = _ := by ring
  have hE : 0 < Real.exp (-(c₀ / 32 * (n : ℝ))) := Real.exp_pos _
  have tri : |kernelSecondMoment (kn n)| ≤ |kernelSecondMoment (kn n) - ∑ z ∈ latBox (2 * h + 1), secondMomentTerm Kl z| +
      |∑ z ∈ latBox (2 * h + 1), secondMomentTerm Kl z| := by
    have := abs_add_le (kernelSecondMoment (kn n) - ∑ z ∈ latBox (2 * h + 1), secondMomentTerm Kl z)
      (∑ z ∈ latBox (2 * h + 1), secondMomentTerm Kl z)
    simpa using this
  calc |kernelSecondMoment (kn n)|
      ≤ (2592 * P * C₂ + Cf * siteSum a) * Real.exp (-(c₀ * (h : ℝ))) := by nlinarith
    _ ≤ (2592 * P * C₂ + Cf * siteSum a) * Real.exp (-(c₀ / 32 * (n : ℝ))) := by gcongr
    _ ≤ _ := by nlinarith
end Moment
section WilsonWeightSeriesExpansion
variable {m : ℕ}
private theorem trivial_cold {s : ℝ} (hs : 0 < s) : IsCold s (trivialField m) := by apply _root_.YangMills.Construction.AbelianSecondOrder.isCold_trivialField <;> assumption
private theorem cold_near [NeZero m] {s : ℝ} (hs : 0 < s) : ∀ᶠ V in 𝓝 (trivialField m), IsCold s V := by apply _root_.YangMills.SharedProofs.p23383 <;> assumption
private theorem scale_bound (Φ : imaginaryQuaternions → imaginaryQuaternions → ℝ)
    (h1 : ∀ (a : ℝ) (Y Y' : imaginaryQuaternions), Φ (a • Y) Y' = a * Φ Y Y')
    (h2 : ∀ (a : ℝ) (Y Y' : imaginaryQuaternions), Φ Y (a • Y') = a * Φ Y Y') {A : ℝ}
    (hu : ∀ Y Y' : imaginaryQuaternions, ‖Y‖ = 1 → ‖Y'‖ = 1 → |Φ Y Y'| ≤ A) (Y Y' : imaginaryQuaternions) :
    |Φ Y Y'| ≤ ‖Y‖ * ‖Y'‖ * A := by
  by_cases h0 : Y = 0
  · subst h0
    have e : Φ 0 Y' = 0 := by
      have := h1 0 0 Y'
      simpa using this
    simp [e]
  by_cases h3 : Y' = 0
  · subst h3
    have e : Φ Y 0 = 0 := by
      have := h2 0 Y 0
      simpa using this
    simp [e]
  have n0 : ‖Y‖ ≠ 0 := norm_ne_zero_iff.mpr h0
  have n1 : ‖Y'‖ ≠ 0 := norm_ne_zero_iff.mpr h3
  have e0 : Y = ‖Y‖ • (‖Y‖⁻¹ • Y) := by
    rw [smul_smul, mul_inv_cancel₀ n0, one_smul]
  have e1 : Y' = ‖Y'‖ • (‖Y'‖⁻¹ • Y') := by
    rw [smul_smul, mul_inv_cancel₀ n1, one_smul]
  have u0 : ‖‖Y‖⁻¹ • Y‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ n0]
  have u1 : ‖‖Y'‖⁻¹ • Y'‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ n1]
  have h := hu _ _ u0 u1
  conv_lhs => rw [e0, e1]
  rw [h1, h2, abs_mul, abs_mul, abs_of_nonneg (norm_nonneg Y), abs_of_nonneg (norm_nonneg Y'), ← mul_assoc]
  exact mul_le_mul_of_nonneg_left h (mul_nonneg (norm_nonneg _) (norm_nonneg _))
private def dForm (f : LocalDensity) :
    (m : ℕ) → TorusSite m → TorusBond m → TorusBond m → imaginaryQuaternions → imaginaryQuaternions → ℝ :=
  fun m y b b' Y Y' => mixedDeriv (centered f m y) (trivialField m) ![b, b'] ![Y, Y']
variable {ℓ : TorusLumps.StepParameters} {t : ℕ} {x : ℝ} {D : TorusFunctional} {f : LocalDensity}
private theorem centered_c3 (hrow : ColdExpansion ℓ t x D f) (hσ : 0 < ℓ.threshold) [NeZero m] (hm : ℓ.n₀ ≤ m)
    (y : TorusSite m) : ContDiffThreeAt (centered f m y) (trivialField m) := fun k c X =>
  (hrow.smooth m hm y _ (trivial_cold hσ) k c X).sub contDiffAt_const
private theorem weight_le (hE : 0 ≤ ℓ.E) (q : ℕ) : ℓ.E / ℓ.weight q ≤ ℓ.E * Real.exp (-(ℓ.weightRate * q)) := by apply _root_.YangMills.Construction.RunningCouplingSlope.CenteredDensityMoment.E_div_weight_le <;> assumption
private theorem units_two {Y Y' : imaginaryQuaternions} (hY : ‖Y‖ = 1) (hY' : ‖Y'‖ = 1) : AreUnitVectors ![Y, Y'] := by apply _root_.YangMills.SharedProofs.p1051 <;> assumption
private theorem is_data (hSec : SecondDerivativePullback) (hrow : ColdExpansion ℓ t x D f)
    (hσ : 0 < ℓ.threshold) (hE : 0 ≤ ℓ.E) {L : ℕ} {M θ : ℝ}
    {Z : (n : ℕ) → TorusBond n → imaginaryQuaternions → TorusBond (n * L) → imaginaryQuaternions} {X : imaginaryQuaternions}
    (hb : ∀ (n : ℕ) [NeZero n], ℓ.n₀ ≤ n → ∀ (c : TorusBond n) (b : TorusBond (n * L)),
      ‖Z n c X b‖ ≤ M * Real.exp (-(θ * (_root_.YangMills.Construction.TorusFields.supDist (parentBlock L b.1) c.1 : ℝ))))
    (hc : ∀ (n n' : ℕ) [NeZero n] [NeZero n'] (ρ : ℕ) (u e : Fin 4 → ℤ) (i k : Fin 4), ℓ.n₀ ≤ n → ℓ.n₀ ≤ n' →
      16 ≤ ρ → 2 * ρ + 2 < n → 2 * ρ + 2 < n' → (∀ j, |e j - coarseOffset L u j| + 1 ≤ (ρ : ℤ)) →
      ‖Z n (siteOfInt e, k) X (siteOfInt u, i) - Z n' (siteOfInt e, k) X (siteOfInt u, i)‖ ≤ M * Real.exp (-(θ * (ρ : ℝ)))) :
    IsData L ℓ.n₀ ℓ.E ℓ.weightRate M θ (dForm f) Z X := by
  have hs : ∀ (m : ℕ) [NeZero m], ℓ.n₀ ≤ m → ∀ (y : TorusSite m) (k : ℕ) (c : Fin k → TorusBond m) (X : Fin k → imaginaryQuaternions),
      ContDiffAt ℝ 2 (fun σ : Fin k → ℝ => centered f m y (perturb c X σ (trivialField m))) 0 := fun m _ hm y k c X =>
    (centered_c3 hrow hσ hm y k c X).of_le (by norm_num)
  refine ⟨?_, ?_, ?_, ?_, hb, hc⟩
  · intro m _ hm y b b' Y₁ Y₂ Y'
    obtain ⟨B, hB, -⟩ := hSec m (centered f m y) (hs m hm y)
    simp only [dForm]
    rw [hB, hB, hB, Pi.single_sub, map_sub, ContinuousLinearMap.sub_apply]
  · intro m _ hm y b b' Y Y₁ Y₂
    obtain ⟨B, hB, -⟩ := hSec m (centered f m y) (hs m hm y)
    simp only [dForm]
    rw [hB, hB, hB, Pi.single_sub, map_sub]
  · intro m _ hm y b b' Y Y'
    obtain ⟨B, hB, -⟩ := hSec m (centered f m y) (hs m hm y)
    refine scale_bound (fun Y Y' => mixedDeriv (centered f m y) (trivialField m) ![b, b'] ![Y, Y']) ?_ ?_ ?_ Y Y'
    · intro a Y Y'
      simp only [hB]
      rw [Pi.single_smul, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    · intro a Y Y'
      simp only [hB]
      rw [Pi.single_smul, map_smul, smul_eq_mul]
    · intro Y Y' hY hY'
      have h1 := hrow.decay m hm y (trivialField m) (trivial_cold hσ) 2 ![b, b'] ![Y, Y'] (by norm_num) (by norm_num)
        (units_two hY hY')
      simp only [show ¬ (2 = 3) by norm_num, if_false] at h1
      have e : mixedDeriv (centered f m y) (trivialField m) ![b, b'] ![Y, Y'] =
          mixedDeriv (f m y) (trivialField m) ![b, b'] ![Y, Y'] :=
        ResponseInTheExpansion.TermCalculus.mixedDeriv_sub_const (f m y) (f m y (trivialField m)) (trivialField m) _ _
          (by norm_num) (by norm_num) (hrow.smooth m hm y _ (trivial_cold hσ) 2 _ _)
      show |mixedDeriv (centered f m y) (trivialField m) ![b, b'] ![Y, Y']| ≤ _
      rw [e]
      exact h1.trans (weight_le hE _)
  · intro m m' _ _ hm hm' y y' q hq hq' h₀ h₁ hb₀ hb₁ Y Y'
    obtain ⟨B, hB, -⟩ := hSec m (centered f m y) (hs m hm y)
    obtain ⟨B', hB', -⟩ := hSec m' (centered f m' y') (hs m' hm' y')
    refine scale_bound (fun Y Y' => mixedDeriv (centered f m y) (trivialField m) ![bondFrom y h₀, bondFrom y h₁] ![Y, Y'] -
      mixedDeriv (centered f m' y') (trivialField m') ![bondFrom y' h₀, bondFrom y' h₁] ![Y, Y']) ?_ ?_ ?_ Y Y'
    · intro a Y Y'
      simp only [hB, hB']
      rw [Pi.single_smul, Pi.single_smul, map_smul, map_smul, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
      ring
    · intro a Y Y'
      simp only [hB, hB']
      rw [Pi.single_smul, Pi.single_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      ring
    · intro Y Y' hY hY'
      have h1 := hrow.local_density m m' hm hm' y y' (trivialField m) (trivialField m') q hq hq' (trivial_cold hσ)
        (trivial_cold hσ) (fun _ _ => rfl) 2 ![h₀, h₁] ![Y, Y'] (by norm_num) (fun l => by
          fin_cases l
          · exact hb₀
          · exact hb₁) (units_two hY hY')
      have e1 : (fun l => bondFrom y ((![h₀, h₁] : Fin 2 → LatticeBond) l)) = ![bondFrom y h₀, bondFrom y h₁] := by
        funext l
        fin_cases l <;> rfl
      have e2 : (fun l => bondFrom y' ((![h₀, h₁] : Fin 2 → LatticeBond) l)) = ![bondFrom y' h₀, bondFrom y' h₁] := by
        funext l
        fin_cases l <;> rfl
      rw [e1, e2] at h1
      exact h1.trans (weight_le hE _)
private theorem density_is_sum [NeZero m] (V : TorusField m) : centeredDensityTotal f m V = ∑ y, centered f m y V := by
  simp [centeredDensityTotal, NeZero.ne m]
private theorem second_is_kern (hSec : SecondDerivativePullback) (hrow : ColdExpansion ℓ t x D f)
    (hσ : 0 < ℓ.threshold) {L : ℕ} {a ρ : ℝ} {t' n : ℕ} [NeZero n] [NeZero (n * L)] (hnL : ℓ.n₀ ≤ n * L)
    {Z : (n : ℕ) → TorusBond n → imaginaryQuaternions → TorusBond (n * L) → imaginaryQuaternions}
    (hZ : HasFlatTangents (minimizerOnFinerTorus a ρ L t' n) (Z n))
    (c c' : TorusBond n) (X : imaginaryQuaternions) :
    hessianAtTrivial (atMinimizer a ρ L t' (centeredDensityTotal f)) n c c' X X = kern L (dForm f) Z X n c c' := by
  have hg : centeredDensityTotal f (n * L) = fun V => ∑ y, centered f (n * L) y V := funext density_is_sum
  have hc3 := fun y => centered_c3 hrow hσ hnL y
  have hs : ∀ (k : ℕ) (c : Fin k → TorusBond (n * L)) (X : Fin k → imaginaryQuaternions),
      ContDiffAt ℝ 2 (fun σ : Fin k → ℝ => centeredDensityTotal f (n * L) (perturb c X σ (trivialField (n * L)))) 0 := by
    intro k c X
    rw [hg]
    exact ContDiffAt.sum fun y _ => (hc3 y k c X).of_le (by norm_num)
  obtain ⟨B, hB, hth⟩ := hSec (n * L) (centeredDensityTotal f (n * L)) hs
  have hinv : ∀ u : UnitQuaternion, ∀ᶠ V in 𝓝 (trivialField (n * L)),
      centeredDensityTotal f (n * L) (_root_.YangMills.Construction.TorusFields.gaugeTransform (fun _ => u) V) = centeredDensityTotal f (n * L) V := by
    intro u
    filter_upwards [cold_near (m := n * L) hσ] with V hV
    rw [density_is_sum, density_is_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    unfold centered
    rw [hrow.gauge (n * L) hnL y _ V hV]
  have h := hth hinv n _ (Z n) hZ c c' X X
  show mixedDeriv (fun V => centeredDensityTotal f (n * L) (minimizerOnFinerTorus a ρ L t' n V)) (trivialField n)
    ![c, c'] ![X, X] = _
  rw [h]
  unfold kern
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  rw [← hB, hg]
  unfold mixedDeriv
  have hc : ∀ y ∈ (Finset.univ : Finset (TorusSite (n * L))),
      ContDiffAt ℝ 2 (fun σ : Fin 2 → ℝ =>
        centered f (n * L) y (perturb ![b, b'] ![Z n c X b, Z n c' X b'] σ (trivialField (n * L)))) 0 :=
    fun y _ => (hc3 y 2 _ _).of_le (by norm_num)
  rw [iteratedFDeriv_fun_sum_apply hc, ContinuousMultilinearMap.sum_apply]
  rfl
private theorem simple_bound {Q G B₂ κ κ₂ : ℝ} {L : ℕ} (hL : 0 < L) (hQ : 0 ≤ Q) (hG : 0 ≤ G) (hB : 0 ≤ B₂)
    (hκ : 0 < κ) (hκ₂ : 0 < κ₂) (h : ℕ) :
    2 * (Q * Real.exp (-(2 * κ * ((L * h : ℕ) : ℝ))) * G) + ((2 * ((L * h : ℕ) : ℝ)) ^ 4) ^ 3 * 16 *
        (3 * B₂ * Real.exp (-(κ₂ * (h : ℝ)))) ≤
      (2 * (Q * G) + 48 * B₂ * (2 * (L : ℝ)) ^ 12 * ((Nat.factorial 12 : ℝ) / (κ₂ / 2) ^ 12)) *
        Real.exp (-(min (2 * κ) (κ₂ / 2) * (h : ℝ))) := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hh0 : (0 : ℝ) ≤ (h : ℝ) := by positivity
  obtain ⟨κ₃, hκ₃⟩ : ∃ κ₃, κ₃ = min (2 * κ) (κ₂ / 2) := ⟨_, rfl⟩
  rw [← hκ₃]
  have k1 : κ₃ ≤ 2 * κ := by
    rw [hκ₃]
    exact min_le_left _ _
  have k2 : κ₃ ≤ κ₂ / 2 := by
    rw [hκ₃]
    exact min_le_right _ _
  have e1 : Real.exp (-(2 * κ * ((L * h : ℕ) : ℝ))) ≤ Real.exp (-(κ₃ * (h : ℝ))) := by
    apply Real.exp_le_exp.mpr
    push_cast
    have : (h : ℝ) ≤ (L : ℝ) * h := by nlinarith
    nlinarith
  have hpow := pow_mul_exp_le (a := κ₂ / 2) (x := (h : ℝ)) (by positivity) hh0 12
  have hexp : Real.exp (-(κ₂ * (h : ℝ))) = Real.exp (-(κ₂ / 2 * (h : ℝ))) * Real.exp (-(κ₂ / 2 * (h : ℝ))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have e2 : Real.exp (-(κ₂ / 2 * (h : ℝ))) ≤ Real.exp (-(κ₃ * (h : ℝ))) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  obtain ⟨F, hF⟩ : ∃ F, F = Real.exp (-(κ₂ / 2 * (h : ℝ))) := ⟨_, rfl⟩
  have hF0 : 0 ≤ F := by
    rw [hF]
    positivity
  rw [← hF] at hexp hpow e2
  rw [hexp]
  push_cast
  have t1 : 2 * (Q * Real.exp (-(2 * κ * ((L : ℝ) * (h : ℝ)))) * G) ≤ 2 * (Q * G) * Real.exp (-(κ₃ * (h : ℝ))) := by
    have : Real.exp (-(2 * κ * ((L : ℝ) * (h : ℝ)))) ≤ Real.exp (-(κ₃ * (h : ℝ))) := by
      simpa using e1
    calc 2 * (Q * Real.exp (-(2 * κ * ((L : ℝ) * (h : ℝ)))) * G) ≤ 2 * (Q * Real.exp (-(κ₃ * (h : ℝ))) * G) := by gcongr
      _ = _ := by ring
  have t2 : ((2 * ((L : ℝ) * (h : ℝ))) ^ 4) ^ 3 * 16 * (3 * B₂ * (F * F)) ≤
      48 * B₂ * (2 * (L : ℝ)) ^ 12 * ((Nat.factorial 12 : ℝ) / (κ₂ / 2) ^ 12) * Real.exp (-(κ₃ * (h : ℝ))) := by
    calc ((2 * ((L : ℝ) * (h : ℝ))) ^ 4) ^ 3 * 16 * (3 * B₂ * (F * F))
        = 48 * B₂ * (2 * (L : ℝ)) ^ 12 * ((h : ℝ) ^ 12 * F) * F := by ring
      _ ≤ _ := by gcongr
  linarith
end WilsonWeightSeriesExpansion
end MinimizerMoment
open MinimizerMoment in
theorem minimizerDensityMomentDecay_holds (hTan : MinimizerDerivativeDecay)
    (hSec : SecondDerivativePullback) (hCoef : ColdDensitiesHaveZeroCoefficient) :
    MinimizerDensityMomentDecay := by
  refine ⟨fun _ => 1, fun _ => one_pos, fun T hD _ => ?_⟩
  obtain ⟨M, θ, hM, hθ, Z₀, hZ⟩ := hTan T hD
  have hodd := hD.L_odd
  have hL : 0 < T.side := hodd.pos
  obtain ⟨r, hr⟩ : ∃ r, r = T.rt / 2 ^ 10 := ⟨_, rfl⟩
  have hr0 : 0 < r := by
    rw [hr]
    have := hD.rt_pos
    positivity
  have hE : 0 ≤ T.E := by
    have h1 := hD.B_ge
    unfold RenormalizationStepParameters.ParameterAssignment.E
    linarith
  have hκ : 0 < κc T.side r θ := κc_pos hL hr0 hθ
  have hq : 0 ≤ qc T.E M θ := by
    unfold qc
    positivity
  have hGw := gwSum_nonneg hκ
  have hκ₂ : 0 < min r (2 * θ) := lt_min hr0 (by positivity)
  have hB₂ : 0 ≤ M * M * T.E := by positivity
  have hC₁ : 0 ≤ qc T.E M θ * Real.exp (2 * κc T.side r θ) * gwSum (κc T.side r θ) := by positivity
  have hC₂ : 0 ≤ 2 * (qc T.E M θ * gwSum (κc T.side r θ)) + 48 * (M * M * T.E) * (2 * (T.side : ℝ)) ^ 12 *
      ((Nat.factorial 12 : ℝ) / (min r (2 * θ) / 2) ^ 12) := by positivity
  have hκ₃ : 0 < min (2 * κc T.side r θ) (min r (2 * θ) / 2) := lt_min (by positivity) (by positivity)
  obtain ⟨C, c, hC, hc, hmom⟩ := moment_small hC₁ (show 0 < 2 * κc T.side r θ by positivity) hC₂ hκ₃
  refine ⟨C, c, hC, hc, fun y R hy hT hA n _ X hn hX => ?_⟩
  have hl := hT.params_eq
  have hrow : ColdExpansion (T.stepParameters y) R.depth R.coupling R.functional R.density := by
    have := hT.isStep.1.1
    rwa [hl] at this
  have hfit := hD.fits y hy
  have harr : IsInvariantFunctionalAbove (T.stepParameters y) R.functional := by
    have := hA
    unfold StepSettings.StepSetup.IsSymmetricWeight at this
    rwa [hl] at this
  have hG : densityAtMinimizer R = atMinimizer T.coupling T.ρA T.side R.depth (centeredDensityTotal R.density) := by
    unfold densityAtMinimizer
    rw [hl, hT.anchorRadius_eq]
    rfl
  rw [hG]
  obtain ⟨-, -, -, hρ0, hρ1, -⟩ := hD.chain
  obtain ⟨K, hK, hsum⟩ := (hCoef T y R.depth R.coupling T.ρA R.functional R.density hD hfit hρ0 hρ1 harr hrow).2
  have hσ : 0 < (T.stepParameters y).threshold := hfit.σ_pos
  have h64 : ∀ w : ℕ, T.n₀ ≤ w → 64 ≤ w := fun w hw => le_trans (by have := hD.n₀_ge; omega) hw
  have hData : IsData T.side T.n₀ T.E r M θ (dForm R.density) (Z₀ R.depth) X := by
    rw [hr]
    refine is_data (ℓ := T.stepParameters y) hSec hrow hσ hE ?_ ?_
    · intro w _ hw c b
      exact ((hZ R.depth).1 w (h64 w hw)).2 c X b hX
    · intro w w' _ _ ρ u e i k hw hw' h16 h2 h2' he
      have := (hZ R.depth).2 w w' ρ u e i k X (h64 w hw) (h64 w' hw') h16 h2 h2' hX he
      rw [← Submodule.coe_sub] at this
      exact this
  have hin : inner ℝ (X : ℍ[ℝ]) (X : ℍ[ℝ]) = 1 := by
    rw [real_inner_self_eq_norm_sq]
    show ‖X‖ ^ 2 = 1
    rw [hX]
    norm_num
  have hnz : ∀ (w : ℕ) [NeZero w], NeZero (w * T.side) := fun w _ => ⟨Nat.mul_ne_zero (NeZero.ne w) hL.ne'⟩
  have hwL : ∀ w, T.n₀ ≤ w → T.n₀ ≤ w * T.side := fun w hw => hw.trans (Nat.le_mul_of_pos_right _ hL)
  refine hmom T.n₀ (fun w c c' => hessianAtTrivial (atMinimizer T.coupling T.ρA T.side R.depth
    (centeredDensityTotal R.density)) w c c' X X) K hD.n₀_ge ?_ ?_ ?_ hsum n hn
  · intro w _ hw c c'
    haveI := hnz w
    show |hessianAtTrivial (atMinimizer T.coupling T.ρA T.side R.depth (centeredDensityTotal R.density)) w c c' X X| ≤ _
    rw [second_is_kern (Z := Z₀ R.depth) hSec hrow hσ (hwL w hw) ((hZ R.depth).1 w (h64 w hw)).1 c c' X]
    exact kern_decay hData hL hE hM.le hr0 hθ hw (hwL w hw) c c'
  · intro w w' _ _ hw hww e₀ e₁ k₀ k₁ he₀ he₁
    haveI := hnz w
    haveI := hnz w'
    have hw' : T.n₀ ≤ w' := hw.trans hww
    show |hessianAtTrivial (atMinimizer T.coupling T.ρA T.side R.depth (centeredDensityTotal R.density)) w _ _ X X -
      hessianAtTrivial (atMinimizer T.coupling T.ρA T.side R.depth (centeredDensityTotal R.density)) w' _ _ X X| ≤ _
    rw [second_is_kern (Z := Z₀ R.depth) hSec hrow hσ (hwL w hw) ((hZ R.depth).1 w (h64 w hw)).1 _ _ X,
      second_is_kern (Z := Z₀ R.depth) hSec hrow hσ (hwL w' hw') ((hZ R.depth).1 w' (h64 w' hw')).1 _ _ X]
    refine (kern_compare hData hodd hE hM.le hr0 hθ hw hww (hwL w hw) (hwL w' hw') (hD.n₀_ge.trans hw) k₀ k₁ he₀ he₁).trans ?_
    exact simple_bound hL hq hGw hB₂ hκ hκ₂ _
  · intro c c'
    have := hK.tendsto_kernel c c' X X
    rw [hin, one_mul] at this
    exact this
end RunningCouplingSlope
end YangMills.Construction
end
