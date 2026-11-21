import YangMills.Construction.QuaternionicWilsonModel.WhatTheTopGivesAtEveryCouplingProof
import YangMills.Construction.FourPointCondition.RiemannSumOfTheBareTracesProof
import YangMills.Construction.ResponseInTheExpansion.CurvatureKernelVariesSlowly
import YangMills.Construction.ResponseInTheExpansion.DisplacementsNearSites
import YangMills.Construction.ResponseInTheExpansion.SitesAroundASite
import YangMills.Construction.ResponseInTheExpansion.SitesOfATuple
import YangMills.Construction.ResponseInTheExpansion.SumsOverCellsAreIntegrals
import YangMills.Construction.ResponseInTheExpansion.TraceOfAProductMovesLittle
import YangMills.Construction.ResponseInTheExpansion.TracesOfChainsOfLocalKernels
import YangMills.Construction.ResponseInTheExpansion.TracesOfTheKernelsAreTheLaw
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion.ResponseKernelTraces
open YangMills.Construction.LinearResponse YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.WeightedResponses YangMills.Construction.MatrixTraces YangMills.Construction.LatticeCells YangMills.Construction.PeriodicLattice YangMills.Construction.TorusMetric YangMills.Construction.ResponseInTheExpansion MeasureTheory
private theorem pow_le_one_add_cube (a : ℝ) (ha : 0 ≤ a) (q : ℕ) (hq : q ≤ 3) : a ^ q ≤ (1 + a) ^ 3 := by
  calc a ^ q ≤ (1 + a) ^ q := pow_le_pow_left₀ ha (by linarith) q
    _ ≤ (1 + a) ^ 3 := pow_le_pow_right₀ (by linarith) hq
private theorem abs_prod_sub_prod_le {ι : Type} (s : Finset ι) (a h : ι → ℝ) (ha : ∀ i, |a i| ≤ 1) (hh : ∀ i, |h i| ≤ 1) :
    |∏ i ∈ s, a i - ∏ i ∈ s, h i| ≤ ∑ i ∈ s, |a i - h i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
    have h1 : a i * ∏ j ∈ s, a j - h i * ∏ j ∈ s, h j =
        (a i - h i) * ∏ j ∈ s, a j + h i * (∏ j ∈ s, a j - ∏ j ∈ s, h j) := by ring
    have h2 : |∏ j ∈ s, a j| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one (fun _ _ => abs_nonneg _) fun j _ => ha j
    rw [h1]
    calc _ ≤ |(a i - h i) * ∏ j ∈ s, a j| + |h i * (∏ j ∈ s, a j - ∏ j ∈ s, h j)| := abs_add_le _ _
      _ ≤ |a i - h i| * 1 + 1 * ∑ j ∈ s, |a j - h j| := by
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
          (mul_le_mul (hh i) ih (abs_nonneg _) zero_le_one)
      _ = _ := by ring
private theorem continuumCurvatureKernel_neg (z : Fin 4 → ℝ) (μ ν ρ τ : Fin 4) :
    continuumCurvatureKernel (-z) μ ν ρ τ = continuumCurvatureKernel z μ ν ρ τ := by apply _root_.YangMills.SharedProofs.p14816 <;> assumption
private theorem measurable_round_real : Measurable (round : ℝ → ℤ) := by
  have : (round : ℝ → ℤ) = fun x => ⌊x + 1 / 2⌋ := by
    funext x
    exact round_eq x
  rw [this]
  exact (measurable_id.add_const _).floor
private theorem continuumCurvatureKernel_measurable (μ ν ρ τ : Fin 4) :
    Measurable fun z : Fin 4 → ℝ => continuumCurvatureKernel z μ ν ρ τ := by apply _root_.YangMills.SharedProofs.p18031 <;> assumption
private theorem circleSub_measurable {U : Type} [MeasurableSpace U] (S : ℝ) (a b : U → ℝ) (ha : Measurable a)
    (hb : Measurable b) : Measurable fun u => circleSub S (a u) (b u) := by
  unfold circleSub
  have h1 : Measurable fun u => a u - b u := ha.sub hb
  have h2 : Measurable fun u => ((round ((a u - b u) / S) : ℤ) : ℝ) :=
    (measurable_from_top (f := fun t : ℤ => (t : ℝ))).comp (measurable_round_real.comp (h1.div_const S))
  exact h1.sub (measurable_const.mul h2)
private theorem list_prod_apply_measurable {U Q : Type} [MeasurableSpace U] [Fintype Q] [DecidableEq Q]
    (l : List (U → Matrix Q Q ℝ)) (h : ∀ M ∈ l, ∀ x y, Measurable fun u => M u x y) (x y : Q) :
    Measurable fun u => (l.map fun M => M u).prod x y := by
  induction l generalizing x y with
  | nil =>
    simp only [List.map_nil, List.prod_nil]
    exact measurable_const
  | cons M t ih =>
    simp only [List.map_cons, List.prod_cons, Matrix.mul_apply]
    refine Finset.measurable_sum _ fun w _ => ?_
    exact (h M (by simp) x w).mul (ih (fun M' hM' => h M' (by simp [hM'])) w y)
private theorem sum_oriented_le (N : ℕ) [NeZero N] (φ : TorusSite N → ℝ) (hφ : ∀ z, 0 ≤ φ z) :
    ∑ a : OrientedPlaquette N, φ a.1.1 ≤ 16 * ∑ z, φ z := by
  classical
  have h1 : ∑ a : OrientedPlaquette N, φ a.1.1 ≤ ∑ p : TorusPlaquette N, φ p.1 := by
    rw [← Finset.sum_subtype (Finset.univ.filter fun p : TorusPlaquette N => p.2.1 < p.2.2) (by simp) (fun p => φ p.1)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun p _ _ => hφ _
  refine h1.trans (le_of_eq ?_)
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.mul_sum]
  norm_num
private theorem weighted_mass_le (N : ℕ) [NeZero N] (del size M₀ : ℝ) (hdel : 0 < del) (hsize : 0 ≤ size)
    (z : TorusSite N)
    (hM : ∑ a : TorusSite N, Real.exp (-(del / 2 * (_root_.YangMills.Construction.TorusFields.supDist a z : ℝ))) * (1 + (_root_.YangMills.Construction.TorusFields.supDist a z : ℝ)) ≤ M₀)
    (κ : TorusPlaquette N → TorusPlaquette N → ℝ)
    (hκ : ∀ p p', |κ p p'| ≤ size * Real.exp (-(del * max (_root_.YangMills.Construction.TorusFields.supDist p.1 z : ℝ) (_root_.YangMills.Construction.TorusFields.supDist p'.1 z : ℝ)))) :
    ∑ a : OrientedPlaquette N, ∑ b : OrientedPlaquette N,
      |κ a.1 b.1| * (1 + (_root_.YangMills.Construction.TorusFields.supDist a.1.1 z : ℝ)) * (1 + (_root_.YangMills.Construction.TorusFields.supDist b.1.1 z : ℝ)) ≤ size * (16 * M₀) ^ 2 := by
  let φ : TorusSite N → ℝ := fun y => Real.exp (-(del / 2 * (_root_.YangMills.Construction.TorusFields.supDist y z : ℝ))) * (1 + (_root_.YangMills.Construction.TorusFields.supDist y z : ℝ))
  have hφ : ∀ y, 0 ≤ φ y := fun y => by
    simp only [φ]
    positivity
  have hterm : ∀ a b : OrientedPlaquette N, |κ a.1 b.1| * (1 + (_root_.YangMills.Construction.TorusFields.supDist a.1.1 z : ℝ)) * (1 + (_root_.YangMills.Construction.TorusFields.supDist b.1.1 z : ℝ)) ≤
      size * (φ a.1.1 * φ b.1.1) := by
    intro a b
    have h1 := hκ a.1 b.1
    set s := (_root_.YangMills.Construction.TorusFields.supDist a.1.1 z : ℝ) with hs
    set t := (_root_.YangMills.Construction.TorusFields.supDist b.1.1 z : ℝ) with ht
    have hs0 : 0 ≤ s := Nat.cast_nonneg _
    have ht0 : 0 ≤ t := Nat.cast_nonneg _
    have hexp : Real.exp (-(del * max s t)) ≤ Real.exp (-(del / 2 * s)) * Real.exp (-(del / 2 * t)) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have h2 : s ≤ max s t := le_max_left _ _
      have h3 : t ≤ max s t := le_max_right _ _
      nlinarith
    have h4 : |κ a.1 b.1| ≤ size * (Real.exp (-(del / 2 * s)) * Real.exp (-(del / 2 * t))) :=
      h1.trans (mul_le_mul_of_nonneg_left hexp hsize)
    calc _ ≤ size * (Real.exp (-(del / 2 * s)) * Real.exp (-(del / 2 * t))) * (1 + s) * (1 + t) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h4 (by positivity)) (by positivity)
      _ = _ := by
        simp only [φ]
        rw [← hs, ← ht]
        ring
  have hsum : ∑ a : OrientedPlaquette N, φ a.1.1 ≤ 16 * M₀ := (sum_oriented_le N φ hφ).trans (by linarith)
  have hsum0 : 0 ≤ ∑ a : OrientedPlaquette N, φ a.1.1 := Finset.sum_nonneg fun a _ => hφ _
  calc _ ≤ ∑ a : OrientedPlaquette N, ∑ b : OrientedPlaquette N, size * (φ a.1.1 * φ b.1.1) :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hterm a b
    _ = size * ((∑ a : OrientedPlaquette N, φ a.1.1) * ∑ b : OrientedPlaquette N, φ b.1.1) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
    _ ≤ size * ((16 * M₀) * (16 * M₀)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul hsum hsum hsum0 (hsum0.trans hsum)) hsize
    _ = _ := by ring
private def planeOfOriented {N : ℕ} (a : OrientedPlaquette N) : OrderedPlane := ⟨(a.1.2.1, a.1.2.2), a.2⟩
private theorem sum_over_plane (N : ℕ) [NeZero N] (Q : OrderedPlane) (φ : TorusPlaquette N → ℝ) :
    ∑ a : OrientedPlaquette N, (if planeOfOriented a = Q then φ a.1 else 0) =
      ∑ p ∈ (plaquettesIn Finset.univ).filter (fun p : TorusPlaquette N => p.2 = (Q.1.1, Q.1.2)), φ p := by
  classical
  rw [← Finset.sum_filter]
  have hQ : ∀ a : OrientedPlaquette N, planeOfOriented a = Q ↔ a.1.2 = (Q.1.1, Q.1.2) := fun a => by
    rw [Subtype.ext_iff]
    rfl
  refine Finset.sum_nbij (fun a => a.1) ?_ ?_ ?_ ?_
  · intro a ha
    have h1 := (hQ a).1 (Finset.mem_filter.mp ha).2
    refine Finset.mem_filter.mpr ⟨?_, h1⟩
    simp [plaquettesIn, a.2]
  · intro a _ b _ h
    exact Subtype.ext h
  · intro p hp
    have hp' := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
    have hlt : p.2.1 < p.2.2 := (Finset.mem_filter.mp hp'.1).2.1
    exact ⟨⟨p, hlt⟩, Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hQ _).2 hp'.2⟩), rfl⟩
  · intro a _
    rfl
private theorem sum_over_two_planes (N : ℕ) [NeZero N] (Q₁ Q₂ : OrderedPlane) (κ : TorusPlaquette N → TorusPlaquette N → ℝ) :
    (∑ a : OrientedPlaquette N, ∑ b : OrientedPlaquette N,
        if planeOfOriented a = Q₁ ∧ planeOfOriented b = Q₂ then κ a.1 b.1 else 0) =
      ∑ p ∈ (plaquettesIn Finset.univ).filter (fun p : TorusPlaquette N => p.2 = (Q₁.1.1, Q₁.1.2)),
        ∑ p' ∈ (plaquettesIn Finset.univ).filter (fun p' : TorusPlaquette N => p'.2 = (Q₂.1.1, Q₂.1.2)), κ p p' := by
  classical
  rw [← sum_over_plane N Q₁ fun p =>
    ∑ p' ∈ (plaquettesIn Finset.univ).filter (fun p' : TorusPlaquette N => p'.2 = (Q₂.1.1, Q₂.1.2)), κ p p']
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : planeOfOriented a = Q₁
  · simp only [h, true_and, if_true]
    exact sum_over_plane N Q₂ (κ a.1)
  · simp [h]
private theorem isLocalKernel_mono {n : ℕ} [NeZero n] {ρ₀ del s s' : ℝ}
    {κ : TorusSite n → TorusPlaquette n → TorusPlaquette n → ℝ}
    (h : IsLocalKernel ρ₀ del s κ) (hs : s ≤ s') : IsLocalKernel ρ₀ del s' κ :=
  ⟨h.support, fun y p p' => (h.decay y p p').trans (mul_le_mul_of_nonneg_right hs (Real.exp_pos _).le)⟩
private def orientedLocalKernel {N : ℕ} (h al : ℝ) (ka kr : TorusPlaquette N → TorusPlaquette N → ℝ) :
    Matrix (OrientedPlaquette N) (OrientedPlaquette N) ℝ :=
  fun a b => h * al * ka a.1 b.1 + kr a.1 b.1
private def sitePlaneKernel {N : ℕ} (z z' : TorusSite N) : Matrix OrderedPlane OrderedPlane ℝ :=
  planeKernelMatrix (torusDisplacement z z')
private theorem sq_le_sqNorm (v : Fin 4 → ℝ) (μ : Fin 4) (b : ℝ) (hb : 0 ≤ b) (h : b ≤ |v μ|) : b ^ 2 ≤ sqNorm v := by
  calc b ^ 2 ≤ |v μ| ^ 2 := pow_le_pow_left₀ hb h 2
    _ = v μ ^ 2 := sq_abs _
    _ ≤ _ := Finset.single_le_sum (f := fun i => v i ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ μ)
private theorem sqNorm_le_of_abs_le (v : Fin 4 → ℝ) (b : ℝ) (h : ∀ μ, |v μ| ≤ b) : sqNorm v ≤ 4 * b ^ 2 := by apply _root_.YangMills.Construction.NonGaussianLimits.sum_sq_le_four_mul_sq <;> assumption
private theorem kernel_near_sites (hB : ContinuumCurvatureKernelBoundAndLipschitz) (hH : TorusDisplacementNearSites)
    {N : ℕ} [NeZero N] (Tc : Matrix (OrientedPlaquette N) (OrientedPlaquette N) ℝ) (n ρ₀ c₆ : ℝ)
    (hn : 4096 ≤ n) (hρ0 : 0 ≤ ρ₀) (hρ : ρ₀ ≤ n / 4096) (hN : n ^ 2 ≤ N) (hc₆ : 0 ≤ c₆)
    (hT : ∀ p p' : OrientedPlaquette N, (n / 8) ^ 2 ≤ sqNorm (plaquetteCentreDisplacement p.1 p'.1) →
      sqNorm (plaquetteCentreDisplacement p.1 p'.1) ≤ ((N : ℝ) / 8) ^ 2 →
      |Tc p p' - continuumCurvatureKernel (plaquetteCentreDisplacement p.1 p'.1) p.1.2.1 p.1.2.2 p'.1.2.1 p'.1.2.2|
        ≤ c₆ / n ^ 5)
    (z z' : TorusSite N) (μ₀ : Fin 4) (hμ₀ : n / 3 - 2 ≤ |torusDisplacement z z' μ₀|)
    (hup : ∀ μ, |torusDisplacement z z' μ| ≤ 10 * n + 2) (a b : OrientedPlaquette N)
    (ha : (_root_.YangMills.Construction.TorusFields.supDist a.1.1 z : ℝ) ≤ ρ₀) (hb : (_root_.YangMills.Construction.TorusFields.supDist b.1.1 z' : ℝ) ≤ ρ₀) :
    |Tc a b - sitePlaneKernel z z' (planeOfOriented a) (planeOfOriented b)| ≤
      (c₆ / n ^ 5 + 400 / (n / 8) ^ 5) * (1 + (_root_.YangMills.Construction.TorusFields.supDist a.1.1 z : ℝ)) * (1 + (_root_.YangMills.Construction.TorusFields.supDist b.1.1 z' : ℝ)) := by
  set sd := torusDisplacement z z' with hsd
  set dA := (_root_.YangMills.Construction.TorusFields.supDist a.1.1 z : ℝ) with hdA
  set dB := (_root_.YangMills.Construction.TorusFields.supDist b.1.1 z' : ℝ) with hdB
  have hNn : 4096 * n ≤ N := by nlinarith
  have hsmall : ∀ μ, |sd μ| + dA + dB < (N : ℝ) / 2 := fun μ => by
    have := hup μ
    linarith
  have hd := (hH N z z').1 a.1.1 b.1.1 hsmall
  have hh : ∀ μ, |plaquetteCentreDisplacement a.1 b.1 μ - torusDisplacement a.1.1 b.1.1 μ| ≤ 1 := by
    intro μ
    simp only [plaquetteCentreDisplacement, add_sub_cancel_left]
    split_ifs <;> norm_num
  set cd := plaquetteCentreDisplacement a.1 b.1 with hcddef
  have hcd : ∀ μ, |cd μ - sd μ| ≤ 1 + dA + dB := by
    intro μ
    have e1 := hh μ
    have e2 := hd μ
    have hs : cd μ - sd μ =
        (cd μ - torusDisplacement a.1.1 b.1.1 μ) + (torusDisplacement a.1.1 b.1.1 μ - sd μ) := by ring
    rw [hs]
    refine (abs_add_le _ _).trans ?_
    linarith
  set E := 1 + dA + dB with hE
  have hr : 0 < n / 8 := by positivity
  have hsd_lo : (n / 8) ^ 2 ≤ sqNorm sd := sq_le_sqNorm sd μ₀ _ hr.le (by linarith)
  have hcd_lo : (n / 8) ^ 2 ≤ sqNorm cd := by
    refine sq_le_sqNorm cd μ₀ _ hr.le ?_
    have e1 := hcd μ₀
    have e2 : |sd μ₀| ≤ |cd μ₀| + |cd μ₀ - sd μ₀| := by
      have := abs_sub_abs_le_abs_sub (sd μ₀) (cd μ₀)
      rw [abs_sub_comm (sd μ₀)] at this
      linarith
    linarith
  have hcd_hi : sqNorm cd ≤ ((N : ℝ) / 8) ^ 2 := by
    have h1 : ∀ μ, |cd μ| ≤ 11 * n := fun μ => by
      have e1 := hcd μ
      have e2 := hup μ
      have e3 : |cd μ| ≤ |sd μ| + |cd μ - sd μ| := by
        have := abs_sub_abs_le_abs_sub (cd μ) (sd μ)
        linarith
      linarith
    have h2 := sqNorm_le_of_abs_le cd _ h1
    have h3 : (22 * n) ^ 2 ≤ ((N : ℝ) / 8) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
    nlinarith
  have h1 := hT a b hcd_lo hcd_hi
  have h2 := (hB (n / 8) cd sd a.1.2.1 a.1.2.2 b.1.2.1 b.1.2.2 hr hcd_lo hsd_lo).2
  have h3 : Real.sqrt (sqNorm (cd - sd)) ≤ 2 * E := by
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    have := sqNorm_le_of_abs_le (cd - sd) E fun μ => hcd μ
    nlinarith
  have hgoal : sitePlaneKernel z z' (planeOfOriented a) (planeOfOriented b) =
      continuumCurvatureKernel sd a.1.2.1 a.1.2.2 b.1.2.1 b.1.2.2 := rfl
  rw [hgoal]
  set W := (1 + dA) * (1 + dB) with hW
  have hW1 : 1 ≤ W := by nlinarith
  have hEW : E ≤ W := by
    simp only [hE, hW]
    nlinarith
  have hr5 : 0 < (n / 8) ^ 5 := by positivity
  have hc0 : 0 ≤ c₆ / n ^ 5 := by positivity
  calc _ ≤ |Tc a b - continuumCurvatureKernel cd a.1.2.1 a.1.2.2 b.1.2.1 b.1.2.2| +
        |continuumCurvatureKernel cd a.1.2.1 a.1.2.2 b.1.2.1 b.1.2.2 -
          continuumCurvatureKernel sd a.1.2.1 a.1.2.2 b.1.2.1 b.1.2.2| :=
        abs_sub_le _ _ _
    _ ≤ c₆ / n ^ 5 + 200 * (2 * E) / (n / 8) ^ 5 := by
        refine add_le_add h1 (h2.trans ?_)
        exact div_le_div_of_nonneg_right (by linarith) hr5.le
    _ ≤ c₆ / n ^ 5 * W + 400 / (n / 8) ^ 5 * W := by
        have e1 : c₆ / n ^ 5 ≤ c₆ / n ^ 5 * W := by nlinarith
        have e2 : 200 * (2 * E) / (n / 8) ^ 5 = 400 / (n / 8) ^ 5 * E := by ring
        have e3 : 400 / (n / 8) ^ 5 * E ≤ 400 / (n / 8) ^ 5 * W :=
          mul_le_mul_of_nonneg_left hEW (by positivity)
        linarith
    _ = _ := by
        simp only [hW]
        ring
private theorem plane_block_sum_le {N : ℕ} [NeZero N] (ka kr : TorusPlaquette N → TorusPlaquette N → ℝ)
    (h al e₀ P : ℝ) (Q₁ Q₂ : OrderedPlane) (hh : |h| ≤ 1) (hal : |al| ≤ 2)
    (hf : |(∑ p ∈ (plaquettesIn Finset.univ).filter (fun p : TorusPlaquette N => p.2 = (Q₁.1.1, Q₁.1.2)),
        ∑ p' ∈ (plaquettesIn Finset.univ).filter (fun p' : TorusPlaquette N => p'.2 = (Q₂.1.1, Q₂.1.2)), ka p p') -
      (if (Q₁.1.1, Q₁.1.2) = (Q₂.1.1, Q₂.1.2) then 1 else 0)| ≤ e₀)
    (hP : ∑ a : OrientedPlaquette N, ∑ b : OrientedPlaquette N, |kr a.1 b.1| ≤ P) :
    |(∑ a : OrientedPlaquette N, ∑ b : OrientedPlaquette N,
        if planeOfOriented a = Q₁ ∧ planeOfOriented b = Q₂ then orientedLocalKernel h al ka kr a b else 0) -
      (if Q₁ = Q₂ then al * h else 0)| ≤ 2 * e₀ + P := by
  classical
  have hsplit : (∑ a : OrientedPlaquette N, ∑ b : OrientedPlaquette N,
      if planeOfOriented a = Q₁ ∧ planeOfOriented b = Q₂ then orientedLocalKernel h al ka kr a b else 0) =
      h * al * (∑ a : OrientedPlaquette N, ∑ b : OrientedPlaquette N,
        if planeOfOriented a = Q₁ ∧ planeOfOriented b = Q₂ then ka a.1 b.1 else 0) +
      ∑ a : OrientedPlaquette N, ∑ b : OrientedPlaquette N,
        if planeOfOriented a = Q₁ ∧ planeOfOriented b = Q₂ then kr a.1 b.1 else 0 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hc : planeOfOriented a = Q₁ ∧ planeOfOriented b = Q₂
    · simp only [if_pos hc, orientedLocalKernel]
    · simp only [if_neg hc, mul_zero, add_zero]
  rw [hsplit, sum_over_two_planes]
  set P₁ := ∑ p ∈ (plaquettesIn Finset.univ).filter (fun p : TorusPlaquette N => p.2 = (Q₁.1.1, Q₁.1.2)),
        ∑ p' ∈ (plaquettesIn Finset.univ).filter (fun p' : TorusPlaquette N => p'.2 = (Q₂.1.1, Q₂.1.2)), ka p p'
  set P₂ := ∑ a : OrientedPlaquette N, ∑ b : OrientedPlaquette N,
    if planeOfOriented a = Q₁ ∧ planeOfOriented b = Q₂ then kr a.1 b.1 else 0
  have hP₂ : |P₂| ≤ P := by
    refine le_trans ?_ hP
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    by_cases hc : planeOfOriented a = Q₁ ∧ planeOfOriented b = Q₂
    · simp only [if_pos hc, le_refl]
    · simp only [if_neg hc, abs_zero]
      exact abs_nonneg _
  set I : ℝ := if (Q₁.1.1, Q₁.1.2) = (Q₂.1.1, Q₂.1.2) then 1 else 0 with hI
  have hg : (if Q₁ = Q₂ then al * h else 0) = h * al * I := by
    by_cases hq : Q₁ = Q₂
    · simp [hI, hq, mul_comm]
    · have : ¬ (Q₁.1.1, Q₁.1.2) = (Q₂.1.1, Q₂.1.2) := fun h' => hq (Subtype.ext (by simpa using h'))
      simp [hI, hq, this]
  rw [hg]
  have hs : h * al * P₁ + P₂ - h * al * I = h * al * (P₁ - I) + P₂ := by ring
  rw [hs]
  have hha : |h * al| ≤ 2 := by
    rw [abs_mul]
    nlinarith [abs_nonneg h, abs_nonneg al]
  calc _ ≤ |h * al * (P₁ - I)| + |P₂| := abs_add_le _ _
    _ ≤ 2 * e₀ + P := by
      refine add_le_add ?_ hP₂
      rw [abs_mul]
      exact mul_le_mul hha hf (abs_nonneg _) (by norm_num)
private theorem lattice_chain_trace_bound (hA : TraceOfLocalKernelCycle) (hB : ContinuumCurvatureKernelBoundAndLipschitz)
    (hH : TorusDisplacementNearSites) {N : ℕ} [NeZero N] (q : ℕ)
    (A : Fin (q + 1) → Finset (TorusSite N)) (hat : Fin (q + 1) → TorusSite N → ℝ)
    (ka : TorusSite N → TorusPlaquette N → TorusPlaquette N → ℝ)
    (kr : Fin (q + 1) → TorusSite N → TorusPlaquette N → TorusPlaquette N → ℝ)
    (Tc : Matrix (OrientedPlaquette N) (OrientedPlaquette N) ℝ) (s : Equiv.Perm (Fin (q + 1)))
    (al n ρ₀ del Ms C₁ ε e₀ c₆ : ℝ)
    (hq : 1 ≤ q) (hn : 4096 ≤ n) (hρ0 : 0 ≤ ρ₀) (hρ : ρ₀ ≤ n / 4096) (hN : n ^ 2 ≤ N) (hC₁ : 0 ≤ C₁)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (he₀ : 0 ≤ e₀) (hc₆ : 0 ≤ c₆) (hMs : 0 ≤ Ms) (hal : |al| ≤ 2)
    (hMass : ∀ (κ : TorusPlaquette N → TorusPlaquette N → ℝ) (size : ℝ) (z : TorusSite N), 0 ≤ size →
      (∀ p p', |κ p p'| ≤ size * Real.exp (-(del * max (supDist p.1 z : ℝ) (supDist p'.1 z : ℝ)))) →
      ∑ a : OrientedPlaquette N, ∑ b : OrientedPlaquette N,
        |κ a.1 b.1| * (1 + (_root_.YangMills.Construction.TorusFields.supDist a.1.1 z : ℝ)) * (1 + (_root_.YangMills.Construction.TorusFields.supDist b.1.1 z : ℝ)) ≤ size * Ms)
    (hka : IsLocalKernel ρ₀ del C₁ ka) (hkr : ∀ i, IsLocalKernel ρ₀ del (C₁ * ε) (kr i))
    (hform : IsNormalizedShareForm e₀ ka)
    (hcard : ∀ i, ((A i).card : ℝ) ≤ (64 * n) ^ 4)
    (hhat : ∀ i z, |hat i z| ≤ 1)
    (hlow : ∀ i j, i ≠ j → ∀ z ∈ A i, ∀ z' ∈ A j, ∃ μ, n / 3 - 2 ≤ |torusDisplacement z z' μ|)
    (hup : ∀ i j, ∀ z ∈ A i, ∀ z' ∈ A j, ∀ μ, |torusDisplacement z z' μ| ≤ 10 * n + 2)
    (hT : ∀ p p' : OrientedPlaquette N, (n / 8) ^ 2 ≤ sqNorm (plaquetteCentreDisplacement p.1 p'.1) →
      sqNorm (plaquetteCentreDisplacement p.1 p'.1) ≤ ((N : ℝ) / 8) ^ 2 →
      |Tc p p' - continuumCurvatureKernel (plaquetteCentreDisplacement p.1 p'.1) p.1.2.1 p.1.2.2 p'.1.2.1 p'.1.2.2|
        ≤ c₆ / n ^ 5) :
    |Matrix.trace (List.ofFn fun j : Fin (q + 1) =>
        (∑ z ∈ A (s j), orientedLocalKernel (hat (s j) z) al (ka z) (kr (s j) z)) * Tc).prod -
      ∑ z ∈ Fintype.piFinset A, (∏ i, al * hat i (z i)) *
        Matrix.trace (List.ofFn fun j : Fin (q + 1) =>
          sitePlaneKernel (z (s j)) (z (s (finRotate (q + 1) j)))).prod| ≤
      ((q : ℝ) + 1) * ((c₆ / n ^ 5 + 400 / (n / 8) ^ 5) * (18 / (n / 8) ^ 4 + (c₆ / n ^ 5 + 400 / (n / 8) ^ 5)) ^ q *
          ((64 * n) ^ 4 * (3 * C₁ * Ms)) ^ (q + 1)) +
        ((q : ℝ) + 1) * ((18 / (n / 8) ^ 4) ^ (q + 1) *
            ((64 * n) ^ 4 * (Fintype.card OrderedPlane : ℝ) ^ 2 * (2 * e₀ + C₁ * ε * Ms)) *
          ((64 * n) ^ 4 * (3 * C₁ * Ms + (Fintype.card OrderedPlane : ℝ) * 2)) ^ q) := by
  have hr : 0 < n / 8 := by positivity
  have hCε : C₁ * ε ≤ C₁ := by nlinarith
  refine hA (TorusSite N) (OrientedPlaquette N) OrderedPlane q A
    (fun i z => orientedLocalKernel (hat i z) al (ka z) (kr i z)) Tc planeOfOriented
    sitePlaneKernel (fun z a => 1 + (_root_.YangMills.Construction.TorusFields.supDist a.1.1 z : ℝ)) (fun z a => (_root_.YangMills.Construction.TorusFields.supDist a.1.1 z : ℝ) ≤ ρ₀)
    (fun i z => al * hat i z)
    (3 * C₁ * Ms) (c₆ / n ^ 5 + 400 / (n / 8) ^ 5) (18 / (n / 8) ^ 4) (2 * e₀ + C₁ * ε * Ms) 2 ((64 * n) ^ 4) s hq
    (by positivity) (by positivity) (by positivity) (by positivity) (by norm_num) (by positivity)
    (fun z a => by
      have : (0 : ℝ) ≤ (_root_.YangMills.Construction.TorusFields.supDist a.1.1 z : ℝ) := Nat.cast_nonneg _
      linarith)
    hcard ?_ ?_ ?_ ?_ ?_ ?_
  · intro i z _ a b hk
    by_contra hno
    apply hk
    have hout : ρ₀ < (_root_.YangMills.Construction.TorusFields.supDist a.1.1 z : ℝ) ∨ ρ₀ < (_root_.YangMills.Construction.TorusFields.supDist b.1.1 z : ℝ) := by
      by_contra h
      push Not at h
      exact hno ⟨h.1, h.2⟩
    simp only [orientedLocalKernel, hka.support z a.1 b.1 hout, (hkr i).support z a.1 b.1 hout, mul_zero, add_zero]
  · intro i z _
    refine hMass (fun p p' => hat i z * al * ka z p p' + kr i z p p') (3 * C₁) z (by positivity) fun p p' => ?_
    have h1 := hka.decay z p p'
    have h2 := (hkr i).decay z p p'
    set e := Real.exp (-(del * max (_root_.YangMills.Construction.TorusFields.supDist p.1 z : ℝ) (_root_.YangMills.Construction.TorusFields.supDist p'.1 z : ℝ))) with he
    have he0 : 0 ≤ e := (Real.exp_pos _).le
    have hha : |hat i z * al| ≤ 2 := by
      rw [abs_mul]
      nlinarith [abs_nonneg (hat i z), abs_nonneg al, hhat i z]
    calc _ ≤ |hat i z * al * ka z p p'| + |kr i z p p'| := abs_add_le _ _
      _ ≤ 2 * (C₁ * e) + C₁ * e := by
        refine add_le_add ?_ (h2.trans (mul_le_mul_of_nonneg_right hCε he0))
        rw [abs_mul]
        exact mul_le_mul hha h1 (abs_nonneg _) (by norm_num)
      _ = _ := by ring
  · intro i j hij z hz z' hz' a b ha hb
    obtain ⟨μ₀, hμ₀⟩ := hlow i j hij z hz z' hz'
    exact kernel_near_sites hB hH Tc n ρ₀ c₆ hn hρ0 hρ hN hc₆ hT z z' μ₀ hμ₀ (hup i j z hz z' hz') a b ha hb
  · intro i j hij z hz z' hz' Q₁ Q₂
    obtain ⟨μ₀, hμ₀⟩ := hlow i j hij z hz z' hz'
    have hlo : (n / 8) ^ 2 ≤ sqNorm (torusDisplacement z z') :=
      sq_le_sqNorm _ μ₀ _ hr.le (by linarith)
    exact (hB (n / 8) _ _ Q₁.1.1 Q₁.1.2 Q₂.1.1 Q₂.1.2 hr hlo hlo).1
  · intro i z _ Q₁ Q₂
    have hf := hform z Q₁.1.1 Q₁.1.2 Q₂.1.1 Q₂.1.2 Q₁.2 Q₂.2
    refine plane_block_sum_le (ka z) (kr i z) (hat i z) al e₀ (C₁ * ε * Ms) Q₁ Q₂ (hhat i z) hal hf ?_
    have hm := hMass (kr i z) (C₁ * ε) z (by positivity) fun p p' => (hkr i).decay z p p'
    refine le_trans (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_) hm
    have h1 : (0 : ℝ) ≤ (_root_.YangMills.Construction.TorusFields.supDist a.1.1 z : ℝ) := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ (_root_.YangMills.Construction.TorusFields.supDist b.1.1 z : ℝ) := Nat.cast_nonneg _
    have h3 := abs_nonneg (kr i z a.1 b.1)
    have h4 : 1 ≤ (1 + (_root_.YangMills.Construction.TorusFields.supDist a.1.1 z : ℝ)) * (1 + (_root_.YangMills.Construction.TorusFields.supDist b.1.1 z : ℝ)) := by nlinarith
    nlinarith
  · intro i z _
    rw [abs_mul]
    nlinarith [abs_nonneg (hat i z), abs_nonneg al, hhat i z]
private theorem finRotate_ne_self (q : ℕ) (hq : 1 ≤ q) (j : Fin (q + 1)) : finRotate (q + 1) j ≠ j := by apply _root_.YangMills.SharedProofs.p60146 <;> assumption
private theorem cell_sum_near_integral (hB : ContinuumCurvatureKernelBoundAndLipschitz) (hD : IntegralNearCellSum)
    (hF : TraceProdLipschitz) (hH : TorusDisplacementNearSites) (ℓ : StepParameters) (k m q : ℕ)
    (n vt : ℝ) (f : Fin (q + 1) → FourTorus ℓ.side m → ℝ) (D : Fin (q + 1) → Finset (TorusSite (2 * ℓ.side ^ m)))
    (s : Equiv.Perm (Fin (q + 1))) (hq : 1 ≤ q) (hn : 4096 ≤ n) (hvt : 0 < vt)
    (hN : n ^ 2 ≤ ((2 * ℓ.side ^ m : ℕ) : ℝ))
    (hcard : ∀ i, ((D i).card : ℝ) ≤ (64 * n) ^ 4)
    (hlow : ∀ i j, i ≠ j → ∀ z ∈ D i, ∀ z' ∈ D j, ∃ μ, n / 3 - 2 ≤ |torusDisplacement z z' μ|)
    (hup : ∀ i j, ∀ z ∈ D i, ∀ z' ∈ D j, ∀ μ, |torusDisplacement z z' μ| ≤ 10 * n + 2)
    (hnear : ∀ i, ∀ z ∈ D i, ∀ u, InUnitCell z u →
      |blockMeanOfFunction ℓ k m (f i) z - f i (torusProj (torusSide ℓ.side m) u)| ≤ 4 / (vt * n))
    (hzero : ∀ i z, z ∉ D i → ∀ u, InUnitCell z u → f i (torusProj (torusSide ℓ.side m) u) = 0)
    (hhat : ∀ i z, |blockMeanOfFunction ℓ k m (f i) z| ≤ 1) (hf1 : ∀ i x, |f i x| ≤ 1)
    (hcont : ∀ i, Continuous fun v : Fin 4 → ℝ => f i (torusProj (torusSide ℓ.side m) v)) :
    |(∫ u in Set.pi Set.univ (fun _ : Fin (q + 1) =>
          Set.pi Set.univ fun _ : Fin 4 => Set.Ico (0 : ℝ) (torusSide ℓ.side m)),
        (∏ i, f i (torusProj (torusSide ℓ.side m) (u i))) * traceAlongCycle (torusSide ℓ.side m) u s) -
      ∑ z ∈ Fintype.piFinset D, (∏ i, blockMeanOfFunction ℓ k m (f i) (z i)) *
        Matrix.trace (List.ofFn fun j : Fin (q + 1) =>
          sitePlaneKernel (z (s j)) (z (s (finRotate (q + 1) j)))).prod| ≤
      (((q : ℝ) + 1) * (Fintype.card OrderedPlane : ℝ) ^ (q + 2) * (18 / (n / 8) ^ 4) ^ q * (400 / (n / 8) ^ 5) +
        ((q : ℝ) + 1) * (4 / (vt * n)) *
          (((q : ℝ) + 1) * (Fintype.card OrderedPlane : ℝ) ^ (q + 2) * (18 / (n / 8) ^ 4) ^ q * (18 / (n / 8) ^ 4))) *
        ((64 * n) ^ 4) ^ (q + 1) := by
  have hSN : torusSide ℓ.side m = ((2 * ℓ.side ^ m : ℕ) : ℝ) := by
    simp only [torusSide]
    push_cast
    ring
  set S := torusSide ℓ.side m with hS
  have hr : 0 < n / 8 := by positivity
  have hNn : 4096 * n ≤ ((2 * ℓ.side ^ m : ℕ) : ℝ) := by nlinarith
  set c := 18 / (n / 8) ^ 4 with hc
  set b := 400 / (n / 8) ^ 5 with hb
  have hc0 : 0 ≤ c := by positivity
  have hb0 : 0 ≤ b := by positivity
  set cQ := (Fintype.card OrderedPlane : ℝ) with hcQ
  set Xb := ((q : ℝ) + 1) * cQ ^ (q + 2) * c ^ q * b with hXb
  set Yb := ((q : ℝ) + 1) * cQ ^ (q + 2) * c ^ q * c with hYb
  set F : (Fin (q + 1) → Fin 4 → ℝ) → ℝ := fun u =>
    (∏ i, f i (torusProj S (u i))) * traceAlongCycle S u s with hFdef
  set Gz : (Fin (q + 1) → TorusSite (2 * ℓ.side ^ m)) → ℝ := fun z =>
    (∏ i, blockMeanOfFunction ℓ k m (f i) (z i)) *
      Matrix.trace (List.ofFn fun j : Fin (q + 1) =>
        sitePlaneKernel (z (s j)) (z (s (finRotate (q + 1) j)))).prod with hGz
  have hFm : Measurable F := by
    refine (Finset.measurable_prod _ fun i _ => (hcont i).measurable.comp (measurable_pi_apply i)).mul ?_
    have hentry : ∀ (j : Fin (q + 1)) (x y : OrderedPlane), Measurable fun u : Fin (q + 1) → Fin 4 → ℝ =>
        planeKernelMatrix (periodicDisplacement S (u (s (finRotate (q + 1) j))) (u (s j))) x y := by
      intro j x y
      refine (continuumCurvatureKernel_measurable x.1.1 x.1.2 y.1.1 y.1.2).comp (measurable_pi_iff.mpr fun μ => ?_)
      exact circleSub_measurable S _ _ ((measurable_pi_apply μ).comp (measurable_pi_apply _))
        ((measurable_pi_apply μ).comp (measurable_pi_apply _))
    have hl := fun x y => list_prod_apply_measurable
      (List.ofFn fun j : Fin (q + 1) => fun u : Fin (q + 1) → Fin 4 → ℝ =>
        planeKernelMatrix (periodicDisplacement S (u (s (finRotate (q + 1) j))) (u (s j))))
      (fun M hM x y => by
        obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).mp hM
        exact hentry j x y) x y
    have heq : (fun u : Fin (q + 1) → Fin 4 → ℝ => traceAlongCycle S u s) = fun u =>
        ∑ x, ((List.ofFn fun j : Fin (q + 1) =>
          fun u : Fin (q + 1) → Fin 4 → ℝ =>
            planeKernelMatrix (periodicDisplacement S (u (s (finRotate (q + 1) j))) (u (s j)))).map
          fun M => M u).prod x x := by
      funext u
      simp only [traceAlongCycle, Matrix.trace, Matrix.diag, List.map_ofFn, Function.comp_def]
    rw [heq]
    exact Finset.measurable_sum _ fun x _ => hl x x
  have hcell : ∀ z ∈ Fintype.piFinset D, ∀ u ∈ unitCell z, |F u - Gz z| ≤
      Xb + ((q : ℝ) + 1) * (4 / (vt * n)) * Yb := by
    intro z hz u hu
    have hzm := Fintype.mem_piFinset.mp hz
    have huc : ∀ i, InUnitCell (z i) (u i) := fun i μ => by
      have := (hu i (Set.mem_univ _)) μ (Set.mem_univ _)
      exact ⟨this.1, this.2⟩
    set Pa := ∏ i, f i (torusProj S (u i)) with hPa
    set Ph := ∏ i, blockMeanOfFunction ℓ k m (f i) (z i) with hPh
    have hPa1 : |Pa| ≤ 1 := by
      rw [hPa, Finset.abs_prod]
      exact Finset.prod_le_one (fun _ _ => abs_nonneg _) fun i _ => hf1 i _
    have hPd : |Pa - Ph| ≤ ((q : ℝ) + 1) * (4 / (vt * n)) := by
      refine (abs_prod_sub_prod_le Finset.univ _ _ (fun i => hf1 i _) (fun i => hhat i (z i))).trans ?_
      calc _ ≤ ∑ _i : Fin (q + 1), 4 / (vt * n) := Finset.sum_le_sum fun i _ => by
            rw [abs_sub_comm]
            exact hnear i (z i) (hzm i) (u i) (huc i)
        _ = _ := by simp
    have hpair : ∀ j : Fin (q + 1), ∀ x y : OrderedPlane,
        |planeKernelMatrix (periodicDisplacement S (u (s (finRotate (q + 1) j))) (u (s j))) x y| ≤ c ∧
        |sitePlaneKernel (z (s j)) (z (s (finRotate (q + 1) j))) x y| ≤ c ∧
        |planeKernelMatrix (periodicDisplacement S (u (s (finRotate (q + 1) j))) (u (s j))) x y -
          sitePlaneKernel (z (s j)) (z (s (finRotate (q + 1) j))) x y| ≤ b := by
      intro j x y
      set zA := z (s (finRotate (q + 1) j)) with hzA
      set zB := z (s j) with hzB
      have hne : s (finRotate (q + 1) j) ≠ s j := fun h => finRotate_ne_self q hq j (s.injective h)
      obtain ⟨μ₀, hμ₀⟩ := hlow _ _ hne zA (hzm _) zB (hzm _)
      have hupAB := hup _ _ zA (hzm _) zB (hzm _)
      set w := torusDisplacement zA zB with hw
      have hsm : ∀ μ, |w μ| + 1 < ((2 * ℓ.side ^ m : ℕ) : ℝ) / 2 := fun μ => by
        have := hupAB μ
        linarith
      obtain ⟨-, hanti, hcellH⟩ := hH (2 * ℓ.side ^ m) zA zB
      have hv := hcellH (u (s (finRotate (q + 1) j))) (u (s j)) (huc _) (huc _) hsm
      set v : Fin 4 → ℝ := periodicDisplacement S (u (s (finRotate (q + 1) j))) (u (s j)) with hvdef
      have hvw : ∀ μ, |v μ - w μ| ≤ 1 := fun μ => by
        have : v μ = circleSub ((2 * ℓ.side ^ m : ℕ) : ℝ) (u (s j) μ) (u (s (finRotate (q + 1) j)) μ) := by
          simp only [hvdef, periodicDisplacement, hSN]
        rw [this]
        exact hv μ
      have hwlo : (n / 8) ^ 2 ≤ sqNorm w := sq_le_sqNorm _ μ₀ _ hr.le (by linarith)
      have hvlo : (n / 8) ^ 2 ≤ sqNorm v := by
        refine sq_le_sqNorm _ μ₀ _ hr.le ?_
        have e1 := hvw μ₀
        have e2 : |w μ₀| ≤ |v μ₀| + |v μ₀ - w μ₀| := by
          have := abs_sub_abs_le_abs_sub (w μ₀) (v μ₀)
          rw [abs_sub_comm (w μ₀)] at this
          linarith
        linarith
      have hplane : sitePlaneKernel zB zA x y = planeKernelMatrix w x y := by
        have h1 : torusDisplacement zB zA = -w := by
          funext μ
          have := hanti μ (by have := hsm μ; linarith)
          simpa using this
        show continuumCurvatureKernel (torusDisplacement zB zA) _ _ _ _ = continuumCurvatureKernel w _ _ _ _
        rw [h1, continuumCurvatureKernel_neg]
      rw [hplane]
      have hv1 := hB (n / 8) v w x.1.1 x.1.2 y.1.1 y.1.2 hr hvlo hwlo
      have hw1 := hB (n / 8) w w x.1.1 x.1.2 y.1.1 y.1.2 hr hwlo hwlo
      refine ⟨hv1.1, hw1.1, hv1.2.trans ?_⟩
      have hsq : Real.sqrt (sqNorm (v - w)) ≤ 2 := by
        refine Real.sqrt_le_iff.mpr ⟨by norm_num, ?_⟩
        have := sqNorm_le_of_abs_le (v - w) 1 fun μ => hvw μ
        linarith
      calc _ ≤ 200 * 2 / (n / 8) ^ 5 := div_le_div_of_nonneg_right (by linarith) (by positivity)
        _ = b := by
          rw [hb]
          norm_num
    have hdiff := hF OrderedPlane q
      (fun j => planeKernelMatrix (periodicDisplacement S (u (s (finRotate (q + 1) j))) (u (s j))))
      (fun j => sitePlaneKernel (z (s j)) (z (s (finRotate (q + 1) j)))) c b hc0 hb0
      (fun j x y => (hpair j x y).1) (fun j x y => (hpair j x y).2.1) (fun j x y => (hpair j x y).2.2)
    have hsize := hF OrderedPlane q (fun j => sitePlaneKernel (z (s j)) (z (s (finRotate (q + 1) j))))
      (fun _ => 0) c c hc0 hc0
      (fun j x y => (hpair j x y).2.1) (fun j x y => by simpa using hc0)
      (fun j x y => by simpa using (hpair j x y).2.1)
    have hzero_tr : Matrix.trace (List.ofFn fun _ : Fin (q + 1) => (0 : Matrix OrderedPlane OrderedPlane ℝ)).prod = 0 := by
      simp [List.ofFn_succ]
    rw [hzero_tr, sub_zero] at hsize
    set tM := Matrix.trace (List.ofFn fun j : Fin (q + 1) =>
      planeKernelMatrix (periodicDisplacement S (u (s (finRotate (q + 1) j))) (u (s j)))).prod with htM
    set tM' := Matrix.trace (List.ofFn fun j : Fin (q + 1) =>
      sitePlaneKernel (z (s j)) (z (s (finRotate (q + 1) j)))).prod with htM'
    have hFu : F u = Pa * tM := rfl
    have hGu : Gz z = Ph * tM' := rfl
    rw [hFu, hGu]
    have hs : Pa * tM - Ph * tM' = Pa * (tM - tM') + (Pa - Ph) * tM' := by ring
    rw [hs]
    calc _ ≤ |Pa * (tM - tM')| + |(Pa - Ph) * tM'| := abs_add_le _ _
      _ ≤ 1 * Xb + ((q : ℝ) + 1) * (4 / (vt * n)) * Yb := by
        rw [abs_mul, abs_mul]
        refine add_le_add (mul_le_mul hPa1 hdiff (abs_nonneg _) zero_le_one)
          (mul_le_mul hPd hsize (abs_nonneg _) (by positivity))
      _ = _ := by ring
  have hoff : ∀ z, z ∉ Fintype.piFinset D → ∀ u ∈ unitCell z, F u = 0 := by
    intro z hz u hu
    have hz' : ∃ i, z i ∉ D i := by
      by_contra hno
      push Not at hno
      exact hz (Fintype.mem_piFinset.mpr hno)
    obtain ⟨i, hi⟩ := hz'
    have h0 := hzero i (z i) hi (u i) fun μ => by
      have := (hu i (Set.mem_univ _)) μ (Set.mem_univ _)
      exact ⟨this.1, this.2⟩
    simp only [hFdef]
    rw [Finset.prod_eq_zero (Finset.mem_univ i) h0, zero_mul]
  have hres := hD (2 * ℓ.side ^ m) (q + 1) F Gz (Fintype.piFinset D) (Xb + ((q : ℝ) + 1) * (4 / (vt * n)) * Yb) hFm
    (by positivity) hcell hoff
  rw [← hSN] at hres
  refine hres.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  rw [Fintype.card_piFinset]
  push_cast
  calc _ ≤ ∏ _i : Fin (q + 1), (64 * n) ^ 4 :=
        Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) fun i _ => hcard i
    _ = _ := by simp
private theorem eventually_large_scale (vt c₀ : ℝ) (hvt : 0 < vt) (hc₀ : 0 < c₀) :
    ∃ x₀ : ℝ, ∀ x, x₀ ≤ x → 1 ≤ x ∧ Real.log x ^ 3 ≤ x ^ ((1 : ℝ) / 100) ∧
      Real.exp (-(c₀ * logCubeScale x)) ≤ x ^ (-(1 / 2 : ℝ)) ∧
      (x ^ ((1 : ℝ) / 90)) ^ 2 ≤ Real.exp (Real.log x ^ 3) ∧ 2 / vt ≤ x ^ ((1 : ℝ) / 100) ∧
      x ^ (-(1 / 2 : ℝ)) ≤ 1 / 2 := by
  have e1 : ∀ᶠ x : ℝ in Filter.atTop, (1 : ℝ) ≤ x := Filter.eventually_ge_atTop 1
  have e2 : ∀ᶠ x : ℝ in Filter.atTop, Real.log x ^ 3 ≤ x ^ ((1 : ℝ) / 100) := by
    have h := (isLittleO_log_rpow_rpow_atTop 3 (show (0 : ℝ) < 1 / 100 by norm_num)).bound
      (show (0 : ℝ) < 1 by norm_num)
    filter_upwards [h, Filter.eventually_ge_atTop 1] with x hx hx1
    have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
    have h3 : Real.log x ^ (3 : ℝ) = Real.log x ^ 3 := by
      rw [← Real.rpow_natCast]
      norm_num
    rw [h3, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), one_mul] at hx
    exact hx
  have e3 : ∀ᶠ x : ℝ in Filter.atTop, max 2 (1 / c₀ + 1) ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually_ge_atTop _
  have e4 : ∀ᶠ x : ℝ in Filter.atTop, 2 / vt ≤ x ^ ((1 : ℝ) / 100) :=
    (tendsto_rpow_atTop (by norm_num)).eventually_ge_atTop _
  have e5 : ∀ᶠ x : ℝ in Filter.atTop, x ^ (-(1 / 2 : ℝ)) ≤ 1 / 2 :=
    (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).eventually_le_const (by norm_num)
  obtain ⟨x₀, h⟩ := Filter.eventually_atTop.mp (e1.and (e2.and (e3.and (e4.and e5))))
  refine ⟨x₀, fun x hx => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := h x hx
  have hx0 : 0 < x := by linarith
  set y := Real.log x with hy
  have hy2 : 2 ≤ y := le_trans (le_max_left _ _) h3
  have hyc : 1 / c₀ + 1 ≤ y := le_trans (le_max_right _ _) h3
  have hcy : 1 ≤ c₀ * y := by
    have : c₀ * (1 / c₀ + 1) ≤ c₀ * y := mul_le_mul_of_nonneg_left hyc hc₀.le
    have h6 : c₀ * (1 / c₀ + 1) = 1 + c₀ := by
      field_simp
    linarith
  refine ⟨h1, h2, ?_, ?_, h4, h5⟩
  · rw [Real.rpow_def_of_pos hx0]
    refine Real.exp_le_exp.mpr ?_
    have hfl : y ^ 3 - 1 ≤ logCubeScale x := by
      have := Nat.lt_floor_add_one (y ^ 3)
      simp only [logCubeScale]
      linarith
    have hy4 : 4 ≤ y ^ 2 := by nlinarith
    have hy3 : 4 * y ≤ y ^ 3 := by
      have : y ^ 3 = y * y ^ 2 := by ring
      rw [this]
      nlinarith
    have hc1 : c₀ * (y ^ 3 - 1) ≤ c₀ * logCubeScale x := mul_le_mul_of_nonneg_left hfl hc₀.le
    have h7 : y ^ 3 - 1 ≥ y ^ 3 / 2 := by nlinarith
    have h8 : c₀ * (y ^ 3 / 2) ≤ c₀ * (y ^ 3 - 1) := mul_le_mul_of_nonneg_left h7 hc₀.le
    have h9 : y ^ 3 = y * y ^ 2 := by ring
    have h10 : y ^ 2 / 2 ≤ c₀ * (y ^ 3 / 2) := by
      have : c₀ * (y ^ 3 / 2) = (c₀ * y) * (y ^ 2 / 2) := by
        rw [h9]
        ring
      rw [this]
      nlinarith [sq_nonneg y]
    nlinarith
  · rw [Real.rpow_def_of_pos hx0, ← Real.exp_nat_mul]
    refine Real.exp_le_exp.mpr ?_
    push_cast
    nlinarith [sq_nonneg y]
set_option maxHeartbeats 1600000 in
private theorem error_terms_le (C₁ Ms c₆ cQ vt : ℝ) (hC₁ : 0 ≤ C₁) (hMs : 0 ≤ Ms) (hc₆ : 0 ≤ c₆) (hcQ : 0 ≤ cQ)
    (hvt : 0 < vt) : ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ (q : ℕ) (n e₀ ε X : ℝ), q ≤ 3 → 4096 ≤ n → 0 ≤ X → 0 ≤ e₀ → e₀ ≤ X →
      0 ≤ ε → ε ≤ (X + 1 / n) / vt →
      ((q : ℝ) + 1) * ((c₆ / n ^ 5 + 400 / (n / 8) ^ 5) * (18 / (n / 8) ^ 4 + (c₆ / n ^ 5 + 400 / (n / 8) ^ 5)) ^ q *
          ((64 * n) ^ 4 * (3 * C₁ * Ms)) ^ (q + 1)) +
        ((q : ℝ) + 1) * ((18 / (n / 8) ^ 4) ^ (q + 1) * ((64 * n) ^ 4 * cQ ^ 2 * (2 * e₀ + C₁ * ε * Ms)) *
          ((64 * n) ^ 4 * (3 * C₁ * Ms + cQ * 2)) ^ q) +
        16 * ((((q : ℝ) + 1) * cQ ^ (q + 2) * (18 / (n / 8) ^ 4) ^ q * (400 / (n / 8) ^ 5) +
          ((q : ℝ) + 1) * (4 / (vt * n)) *
            (((q : ℝ) + 1) * cQ ^ (q + 2) * (18 / (n / 8) ^ 4) ^ q * (18 / (n / 8) ^ 4))) *
          ((64 * n) ^ 4) ^ (q + 1)) ≤ Cb * (X + 1 / n) := by
  set a : ℝ := 64 ^ 4 with ha
  set c₅ : ℝ := 400 * 8 ^ 5 with hc₅
  set K₁ : ℝ := 18 * 8 ^ 4 * a with hK₁
  set B : ℝ := 3 * C₁ * Ms with hB
  set K₂ : ℝ := K₁ + (c₆ + c₅) * a with hK₂
  have hK₁0 : 0 ≤ K₁ := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hK₂0 : 0 ≤ K₂ := by positivity
  set Yb : ℝ := (1 + cQ) ^ 5 with hYb
  have hYb0 : 0 ≤ Yb := by positivity
  clear_value Yb
  set T₁ : ℝ := 4 * ((c₆ + c₅) * a * B * (1 + K₂ * B) ^ 3) with hT₁
  set T₂ : ℝ := 4 * (K₁ * cQ ^ 2 * (2 + C₁ * Ms / vt) * (1 + K₁ * (B + cQ * 2)) ^ 3) with hT₂
  set T₃ : ℝ := 16 * (4 * (Yb * (1 + K₁) ^ 3 * (c₅ * a)) + 16 * (4 / vt) * (Yb * (1 + K₁) ^ 4)) with hT₃
  have hT₁0 : 0 ≤ T₁ := by positivity
  have hT₂0 : 0 ≤ T₂ := by positivity
  have hT₃0 : 0 ≤ T₃ := by positivity
  clear_value T₁ T₂ T₃ K₂ K₁ B
  refine ⟨T₁ + T₂ + T₃, by positivity, fun q n e₀ ε X hq hn hX he₀ he₀X hε hεX => ?_⟩
  have hnpos : 0 < n := by linarith
  set t : ℝ := 1 / n with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := by
    rw [ht, div_le_one hnpos]
    linarith
  have hq4 : (q : ℝ) + 1 ≤ 4 := by
    have : (q : ℝ) ≤ 3 := by exact_mod_cast hq
    linarith
  have h4vt : 4 / (vt * n) = 4 / vt * t := by
    rw [ht]
    field_simp
  rw [h4vt]
  set c := 18 / (n / 8) ^ 4 with hc
  set b := 400 / (n / 8) ^ 5 with hb
  set δ := c₆ / n ^ 5 + b with hδ
  set Am := (64 * n) ^ 4 with hAm
  have hcA : c * Am = K₁ := by
    rw [hc, hAm, hK₁, ha]
    field_simp
  have hbA : b * Am = c₅ * a * t := by
    rw [hb, hAm, hc₅, ha, ht]
    field_simp
  have hδA : δ * Am = (c₆ + c₅) * a * t := by
    have : c₆ / n ^ 5 * Am = c₆ * a * t := by
      rw [hAm, ha, ht]
      field_simp
    rw [hδ, add_mul, this, hbA]
    ring
  have hcδA : (c + δ) * Am ≤ K₂ := by
    rw [add_mul, hcA, hδA, hK₂]
    have : (c₆ + c₅) * a * t ≤ (c₆ + c₅) * a := by
      nlinarith
    linarith
  have hcδA0 : 0 ≤ (c + δ) * Am := by positivity
  clear_value c b δ Am t
  obtain ⟨u, hu⟩ : ∃ u, u = c + δ := ⟨_, rfl⟩
  rw [← hu] at hcδA hcδA0 ⊢
  have hE1 : ((q : ℝ) + 1) * (δ * u ^ q * (Am * B) ^ (q + 1)) ≤ T₁ * t := by
    have h1 : δ * u ^ q * (Am * B) ^ (q + 1) = (δ * Am * B) * (u * Am * B) ^ q := by ring
    have h2 : (u * Am * B) ^ q ≤ (1 + K₂ * B) ^ 3 := by
      refine le_trans (pow_le_pow_left₀ (by positivity) ?_ q) (pow_le_one_add_cube _ (by positivity) q hq)
      exact mul_le_mul_of_nonneg_right hcδA hB0
    rw [h1, hδA]
    calc _ ≤ 4 * ((c₆ + c₅) * a * t * B * (1 + K₂ * B) ^ 3) := by
          refine mul_le_mul hq4 ?_ (by positivity) (by norm_num)
          exact mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by
          rw [hT₁]
          ring
  have hη : 2 * e₀ + C₁ * ε * Ms ≤ (2 + C₁ * Ms / vt) * (X + t) := by
    have h1 : C₁ * ε * Ms ≤ C₁ * Ms * ((X + t) / vt) := by
      have : C₁ * ε * Ms = C₁ * Ms * ε := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hεX (by positivity)
    have h2 : C₁ * Ms * ((X + t) / vt) = C₁ * Ms / vt * (X + t) := by ring
    have h3 : (2 + C₁ * Ms / vt) * (X + t) = 2 * (X + t) + C₁ * Ms / vt * (X + t) := by ring
    rw [h3]
    linarith
  have hE2 : ((q : ℝ) + 1) * (c ^ (q + 1) * (Am * cQ ^ 2 * (2 * e₀ + C₁ * ε * Ms)) * (Am * (B + cQ * 2)) ^ q) ≤
      T₂ * (X + t) := by
    have h1 : ∀ W E : ℝ, c ^ (q + 1) * (Am * cQ ^ 2 * E) * (Am * W) ^ q =
        (c * Am * cQ ^ 2 * E) * (c * Am * W) ^ q := by
      intro W E
      ring
    rw [h1, hcA]
    have h2 : (K₁ * (B + cQ * 2)) ^ q ≤ (1 + K₁ * (B + cQ * 2)) ^ 3 := pow_le_one_add_cube _ (by positivity) q hq
    calc _ ≤ 4 * (K₁ * cQ ^ 2 * ((2 + C₁ * Ms / vt) * (X + t)) * (1 + K₁ * (B + cQ * 2)) ^ 3) := by
          refine mul_le_mul hq4 ?_ (by positivity) (by norm_num)
          refine mul_le_mul ?_ h2 (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left hη (by positivity)
      _ = _ := by
          rw [hT₂]
          ring
  have hY : cQ ^ (q + 2) ≤ Yb := by
    rw [hYb]
    calc _ ≤ (1 + cQ) ^ (q + 2) := pow_le_pow_left₀ hcQ (by linarith) _
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega)
  have hcube : K₁ ^ q ≤ (1 + K₁) ^ 3 := pow_le_one_add_cube _ hK₁0 q hq
  have hfour : K₁ ^ (q + 1) ≤ (1 + K₁) ^ 4 := by
    calc _ ≤ (1 + K₁) ^ (q + 1) := pow_le_pow_left₀ hK₁0 (by linarith) _
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega)
  have hE3 : 16 * ((((q : ℝ) + 1) * cQ ^ (q + 2) * c ^ q * b +
      ((q : ℝ) + 1) * (4 / vt * t) * (((q : ℝ) + 1) * cQ ^ (q + 2) * c ^ q * c)) * Am ^ (q + 1)) ≤ T₃ * t := by
    have h1 : (((q : ℝ) + 1) * cQ ^ (q + 2) * c ^ q * b +
        ((q : ℝ) + 1) * (4 / vt * t) * (((q : ℝ) + 1) * cQ ^ (q + 2) * c ^ q * c)) * Am ^ (q + 1) =
        ((q : ℝ) + 1) * (cQ ^ (q + 2) * (c * Am) ^ q * (b * Am)) +
        (((q : ℝ) + 1) * ((q : ℝ) + 1)) * (4 / vt * t) * (cQ ^ (q + 2) * (c * Am) ^ (q + 1)) := by
      ring
    rw [h1, hcA, hbA]
    have h2 : ((q : ℝ) + 1) * (cQ ^ (q + 2) * K₁ ^ q * (c₅ * a * t)) ≤ 4 * (Yb * (1 + K₁) ^ 3 * (c₅ * a * t)) := by
      refine mul_le_mul hq4 ?_ (by positivity) (by norm_num)
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact mul_le_mul hY hcube (by positivity) hYb0
    have h3 : (((q : ℝ) + 1) * ((q : ℝ) + 1)) * (4 / vt * t) * (cQ ^ (q + 2) * K₁ ^ (q + 1)) ≤
        16 * (4 / vt * t) * (Yb * (1 + K₁) ^ 4) := by
      have hqq : ((q : ℝ) + 1) * ((q : ℝ) + 1) ≤ 16 := by nlinarith
      refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
      · exact mul_le_mul_of_nonneg_right hqq (by positivity)
      · exact mul_le_mul hY hfour (by positivity) hYb0
    calc _ ≤ 16 * (4 * (Yb * (1 + K₁) ^ 3 * (c₅ * a * t)) + 16 * (4 / vt * t) * (Yb * (1 + K₁) ^ 4)) := by
          have := add_le_add h2 h3
          linarith
      _ = _ := by
          rw [hT₃]
          ring
  have hfin : T₁ * t + T₂ * (X + t) + T₃ * t ≤ (T₁ + T₂ + T₃) * (X + t) := by nlinarith
  calc _ ≤ T₁ * t + T₂ * (X + t) + T₃ * t := add_le_add (add_le_add hE1 hE2) hE3
    _ ≤ _ := hfin
private theorem kernelCycleTrace_eq_trace {I : Type} [Fintype I] [DecidableEq I] {q : ℕ}
    (κ : Fin (q + 1) → Matrix I I ℝ) (Tc : Matrix I I ℝ) (s : Equiv.Perm (Fin (q + 1))) :
    kernelCycleTrace κ Tc s = Matrix.trace (List.ofFn fun i : Fin (q + 1) => κ (s i) * Tc).prod := by
  unfold kernelCycleTrace
  congr!
private theorem responseKernel_eq_sum {N : ℕ} [NeZero N] (A : Finset (TorusSite N)) (hat : TorusSite N → ℝ) (al : ℝ)
    (ka kr : TorusSite N → TorusPlaquette N → TorusPlaquette N → ℝ) :
    responseKernel A hat al ka kr = ∑ z ∈ A, orientedLocalKernel (hat z) al (ka z) (kr z) := by
  refine Matrix.ext fun a b => ?_
  rw [Matrix.sum_apply]
  rfl
private theorem rpow_neg_five_halves_le (t s : ℝ) (ht : 0 < t) (h : t ^ 2 ≤ s) : s ^ (-(5 / 2 : ℝ)) ≤ 1 / t ^ 5 := by
  have h1 : s ^ (-(5 / 2 : ℝ)) ≤ (t ^ 2) ^ (-(5 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) h (by norm_num)
  have h2 : (t ^ 2) ^ (-(5 / 2 : ℝ)) = 1 / t ^ 5 := by
    rw [← Real.rpow_natCast t 2, ← Real.rpow_mul ht.le]
    have : (((2 : ℕ) : ℝ) * -(5 / 2 : ℝ)) = -((5 : ℕ) : ℝ) := by norm_num
    rw [this, Real.rpow_neg ht.le, Real.rpow_natCast, one_div]
  rw [← h2]
  exact h1
private theorem scaled_sum_sub_le {ι : Type} (t : Finset ι) (a b : ι → ℝ) (c Bd : ℝ) (h : ∀ s, |a s - c * b s| ≤ Bd)
    (ht : (t.card : ℝ) ≤ 24) (hBd : 0 ≤ Bd) :
    |(3 / 2) * ∑ s ∈ t, a s - c * ((3 / 2) * ∑ s ∈ t, b s)| ≤ 36 * Bd := by
  have hs : (3 / 2) * ∑ s ∈ t, a s - c * ((3 / 2) * ∑ s ∈ t, b s) = (3 / 2) * ∑ s ∈ t, (a s - c * b s) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  rw [hs, abs_mul]
  have h1 : |∑ s ∈ t, (a s - c * b s)| ≤ (t.card : ℝ) * Bd := by
    calc _ ≤ ∑ s ∈ t, |a s - c * b s| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _s ∈ t, Bd := Finset.sum_le_sum fun s _ => h s
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have h2 : (t.card : ℝ) * Bd ≤ 24 * Bd := mul_le_mul_of_nonneg_right ht hBd
  have h3 : |(3 / 2 : ℝ)| = 3 / 2 := by norm_num
  rw [h3]
  linarith
set_option maxHeartbeats 1600000 in
theorem of_stepParameters (hA : TraceOfLocalKernelCycle) (hB : ContinuumCurvatureKernelBoundAndLipschitz)
    (hD : IntegralNearCellSum) (hE : ExpDecaySumAndBallCard)
    (hF : TraceProdLipschitz) (hG : tupleSupportSitesStatement)
    (hH : TorusDisplacementNearSites) (ℓ : StepParameters) (hodd : Odd ℓ.side) : responseKernelTracesAt ℓ := by
  intro vt del c₀ C₀ hvt hvt1 hdel hc₀
  obtain ⟨M₀, hM₀⟩ := hE.1 (del / 2) (by positivity)
  obtain ⟨x₀, hx₀⟩ := eventually_large_scale vt c₀ hvt hc₀
  obtain ⟨C₁, hC₁def⟩ : ∃ C₁ : ℝ, C₁ = |C₀| + 1 := ⟨_, rfl⟩
  have hC₁ : 0 ≤ C₁ := by
    rw [hC₁def]
    positivity
  have hC₀₁ : C₀ ≤ C₁ := by
    rw [hC₁def]
    linarith [le_abs_self C₀]
  obtain ⟨c₆, hc₆def⟩ : ∃ c₆ : ℝ, c₆ = C₁ * (8 ^ 5 + 1) + 1 := ⟨_, rfl⟩
  have hc₆ : 0 ≤ c₆ := by
    rw [hc₆def]
    positivity
  obtain ⟨Ms, hMsdef⟩ : ∃ Ms : ℝ, Ms = (16 * |M₀|) ^ 2 := ⟨_, rfl⟩
  have hMs : 0 ≤ Ms := by
    rw [hMsdef]
    positivity
  obtain ⟨Cb, hCb0, hCb⟩ :=
    error_terms_le C₁ Ms c₆ (Fintype.card OrderedPlane : ℝ) vt hC₁ hMs hc₆ (Nat.cast_nonneg _) hvt
  refine ⟨36 * Cb, x₀, ?_⟩
  intro q k m x nn al f ka kr Tc hq1 hq3 hx hwin1 hwin2 hside hal hf hka hform hkr hT
  obtain ⟨hx1, hlog, hexp, hsq, hvtx, hhalf⟩ := hx₀ x hx
  have hL1 : (1 : ℝ) ≤ (ℓ.side : ℝ) := by
    have : 1 ≤ ℓ.side := Nat.pos_of_ne_zero (NeZero.ne ℓ.side)
    exact_mod_cast this
  have hSN : 2 * (ℓ.side : ℝ) ^ m = ((2 * ℓ.side ^ m : ℕ) : ℝ) := by
    push_cast
    ring
  have hxr1 : 1 ≤ x ^ ((1 : ℝ) / 100) := Real.one_le_rpow hx1 (by norm_num)
  have hrange : x ^ ((1 : ℝ) / 100) ≤ (clusterRange x : ℝ) := Nat.le_ceil _
  have hn1 : 4096 * x ^ ((1 : ℝ) / 100) ≤ nn := by
    have h1 : 4096 * x ^ ((1 : ℝ) / 100) ≤ 2 ^ 12 * (ℓ.side : ℝ) * (clusterRange x : ℝ) := by
      have : (2 : ℝ) ^ 12 = 4096 := by norm_num
      rw [this]
      have h2 : (1 : ℝ) * x ^ ((1 : ℝ) / 100) ≤ (ℓ.side : ℝ) * (clusterRange x : ℝ) :=
        mul_le_mul hL1 hrange (by positivity) (by linarith)
      have h3 : 4096 * (ℓ.side : ℝ) * (clusterRange x : ℝ) = 4096 * ((ℓ.side : ℝ) * (clusterRange x : ℝ)) := by ring
      rw [h3]
      linarith
    linarith
  have hn : 4096 ≤ nn := by linarith
  have hnpos : 0 < nn := by linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hρ0 : 0 ≤ logCubeScale x := by
    simp only [logCubeScale]
    positivity
  have hρ : logCubeScale x ≤ nn / 4096 := by
    have h1 : logCubeScale x ≤ Real.log x ^ 3 := by
      simp only [logCubeScale]
      exact Nat.floor_le (by positivity)
    linarith
  have hN : nn ^ 2 ≤ ((2 * ℓ.side ^ m : ℕ) : ℝ) := by
    rw [← hSN]
    calc nn ^ 2 ≤ (x ^ ((1 : ℝ) / 90)) ^ 2 := pow_le_pow_left₀ hnpos.le hwin2 2
      _ ≤ _ := hsq.trans hside
  have hNn : 4096 * nn ≤ ((2 * ℓ.side ^ m : ℕ) : ℝ) := by
    have h1 : 4096 * nn ≤ nn * nn := mul_le_mul_of_nonneg_right hn hnpos.le
    have h2 : nn * nn = nn ^ 2 := by ring
    linarith
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = x ^ (-(1 / 2 : ℝ)) := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by
    rw [hXdef]
    positivity
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = X + 1 / (vt * nn) := ⟨_, rfl⟩
  have hε0 : 0 ≤ ε := by
    rw [hεdef]
    positivity
  have hvn : 2 ≤ vt * nn := by
    have h1 : 2 / vt ≤ nn := by linarith
    rw [div_le_iff₀ hvt] at h1
    linarith
  have hε1 : ε ≤ 1 := by
    have h2 : 1 / (vt * nn) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hvn
    rw [hεdef, hXdef]
    linarith
  have hεX : ε ≤ (X + 1 / nn) / vt := by
    rw [hεdef, le_div_iff₀ hvt]
    have h1 : 1 / (vt * nn) * vt = 1 / nn := by
      field_simp
    have h2 : X * vt ≤ X := mul_le_of_le_one_right hX0 hvt1
    rw [add_mul, h1]
    linarith
  obtain ⟨e₀, he₀def⟩ : ∃ e₀ : ℝ, e₀ = Real.exp (-(c₀ * logCubeScale x)) := ⟨_, rfl⟩
  have he₀ : 0 ≤ e₀ := by
    rw [he₀def]
    positivity
  have he₀X : e₀ ≤ X := by
    rw [he₀def, hXdef]
    exact hexp
  have hka' : IsLocalKernel (logCubeScale x) del C₁ ka := isLocalKernel_mono hka hC₀₁
  have hkr' : ∀ i, IsLocalKernel (logCubeScale x) del (C₁ * ε) (kr i) := fun i => by
    refine isLocalKernel_mono (hkr i) ?_
    rw [hεdef, hXdef]
    exact mul_le_mul_of_nonneg_right hC₀₁ (by positivity)
  have hform' : IsNormalizedShareForm e₀ ka := by
    rw [he₀def]
    exact hform
  have hMass : ∀ (κ : TorusPlaquette (2 * ℓ.side ^ m) → TorusPlaquette (2 * ℓ.side ^ m) → ℝ) (size : ℝ)
      (z : TorusSite (2 * ℓ.side ^ m)), 0 ≤ size →
      (∀ p p', |κ p p'| ≤ size * Real.exp (-(del * max (supDist p.1 z : ℝ) (supDist p'.1 z : ℝ)))) →
      ∑ a : OrientedPlaquette (2 * ℓ.side ^ m), ∑ b : OrientedPlaquette (2 * ℓ.side ^ m),
        |κ a.1 b.1| * (1 + (_root_.YangMills.Construction.TorusFields.supDist a.1.1 z : ℝ)) * (1 + (_root_.YangMills.Construction.TorusFields.supDist b.1.1 z : ℝ)) ≤ size * Ms := by
    intro κ size z hs hκ
    rw [hMsdef]
    exact weighted_mass_le (2 * ℓ.side ^ m) del size |M₀| hdel hs z
      ((hM₀ (2 * ℓ.side ^ m) z).trans (le_abs_self _)) κ hκ
  have hTn : ∀ p p' : OrientedPlaquette (2 * ℓ.side ^ m),
      (nn / 8) ^ 2 ≤ sqNorm (plaquetteCentreDisplacement p.1 p'.1) →
      sqNorm (plaquetteCentreDisplacement p.1 p'.1) ≤ (((2 * ℓ.side ^ m : ℕ) : ℝ) / 8) ^ 2 →
      |Tc p p' - continuumCurvatureKernel (plaquetteCentreDisplacement p.1 p'.1) p.1.2.1 p.1.2.2 p'.1.2.1 p'.1.2.2|
        ≤ c₆ / nn ^ 5 := by
    intro p p' h1 h2
    have hone : (1 : ℝ) ≤ (nn / 8) ^ 2 := one_le_pow₀ (by linarith)
    have h3 := hT p p' (hone.trans h1) (by rw [hSN]; exact h2)
    have hr : 0 < nn / 8 := by positivity
    have h4 := rpow_neg_five_halves_le (nn / 8) _ hr h1
    have hn5 : 0 < nn ^ 5 := by positivity
    have h5 : 1 / (nn / 8) ^ 5 = 8 ^ 5 / nn ^ 5 := by
      field_simp
    have h6 : (2 * (ℓ.side : ℝ) ^ m) ^ (-(4 : ℤ)) ≤ 1 / nn ^ 5 := by
      rw [hSN, zpow_neg]
      have h7 : (((2 * ℓ.side ^ m : ℕ) : ℝ)) ^ (4 : ℤ) = ((2 * ℓ.side ^ m : ℕ) : ℝ) ^ 4 := by norm_cast
      rw [h7, ← one_div]
      refine one_div_le_one_div_of_le hn5 ?_
      calc nn ^ 5 ≤ nn ^ 8 := pow_le_pow_right₀ (by linarith) (by norm_num)
        _ = (nn ^ 2) ^ 4 := by ring
        _ ≤ _ := pow_le_pow_left₀ (by positivity) hN 4
    have h8 : x ^ (-(50 : ℝ)) ≤ 1 / nn ^ 5 := by
      rw [Real.rpow_neg (by linarith), ← one_div]
      refine one_div_le_one_div_of_le hn5 ?_
      calc nn ^ 5 ≤ (x ^ ((1 : ℝ) / 90)) ^ 5 := pow_le_pow_left₀ hnpos.le hwin2 5
        _ = x ^ ((1 : ℝ) / 90 * 5) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
          norm_num
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    have hpos : 0 ≤ sqNorm (plaquetteCentreDisplacement p.1 p'.1) ^ (-(5 / 2 : ℝ)) +
        (2 * (ℓ.side : ℝ) ^ m) ^ (-(4 : ℤ)) := by
      have hs0 : 0 ≤ sqNorm (plaquetteCentreDisplacement p.1 p'.1) := Finset.sum_nonneg fun _ _ => sq_nonneg _
      positivity
    have h9 : C₀ * (sqNorm (plaquetteCentreDisplacement p.1 p'.1) ^ (-(5 / 2 : ℝ)) +
        (2 * (ℓ.side : ℝ) ^ m) ^ (-(4 : ℤ))) ≤ C₁ * (8 ^ 5 / nn ^ 5 + 1 / nn ^ 5) := by
      calc _ ≤ C₁ * (sqNorm (plaquetteCentreDisplacement p.1 p'.1) ^ (-(5 / 2 : ℝ)) +
              (2 * (ℓ.side : ℝ) ^ m) ^ (-(4 : ℤ))) :=
            mul_le_mul_of_nonneg_right hC₀₁ hpos
        _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add (h5 ▸ h4) h6) hC₁
    calc _ ≤ C₁ * (8 ^ 5 / nn ^ 5 + 1 / nn ^ 5) + 1 / nn ^ 5 := by linarith
      _ = c₆ / nn ^ 5 := by
        rw [hc₆def]
        ring
  obtain ⟨D, hsub, hcardD, hlowD, hupD, hnearD, hzeroD, hhatD, hhat0, hf1, hcont⟩ :=
    hG ℓ hodd k m (q + 1) nn vt f hvt (by linarith) (by rw [hSN]; linarith) hf
  let A : Fin (q + 1) → Finset (TorusSite (2 * ℓ.side ^ m)) := fun i =>
    weightSupportSites ℓ.side k (2 * ℓ.side ^ m) (testWeight ℓ.side k m (f i))
  have hcardA : ∀ i, ((A i).card : ℝ) ≤ (64 * nn) ^ 4 := fun i => by
    refine le_trans ?_ (hcardD i)
    exact_mod_cast Finset.card_le_card (hsub i)
  have hmain : ∀ s : Equiv.Perm (Fin (q + 1)),
      |kernelCycleTrace (fun i => responseKernel (A i)
          (fun z => blockMean ℓ.side k (2 * ℓ.side ^ m) z (testWeight ℓ.side k m (f i))) al ka (kr i)) Tc s -
        al ^ (q + 1) * ∫ u in Set.pi Set.univ (fun _ : Fin (q + 1) =>
            Set.pi Set.univ fun _ : Fin 4 => Set.Ico (0 : ℝ) (torusSide ℓ.side m)),
          (∏ i, f i (torusProj (torusSide ℓ.side m) (u i))) * traceAlongCycle (torusSide ℓ.side m) u s| ≤
        Cb * (X + 1 / nn) := by
    intro s
    have hc := lattice_chain_trace_bound hA hB hH q A (fun i z => blockMeanOfFunction ℓ k m (f i) z) ka kr Tc s al nn
      (logCubeScale x) del Ms C₁ ε e₀ c₆
      hq1 hn hρ0 hρ hN hC₁ hε0 hε1 he₀ hc₆ hMs hal hMass hka' hkr' hform' hcardA hhatD
      (fun i j hij z hz z' hz' => hlowD i j hij z (hsub i hz) z' (hsub j hz'))
      (fun i j z hz z' hz' => hupD i j z (hsub i hz) z' (hsub j hz')) hTn
    have hr := cell_sum_near_integral hB hD hF hH ℓ k m q nn vt f D s hq1 hn hvt hN hcardD hlowD hupD hnearD hzeroD
      hhatD hf1 hcont
    set I := ∫ u in Set.pi Set.univ (fun _ : Fin (q + 1) =>
            Set.pi Set.univ fun _ : Fin 4 => Set.Ico (0 : ℝ) (torusSide ℓ.side m)),
          (∏ i, f i (torusProj (torusSide ℓ.side m) (u i))) * traceAlongCycle (torusSide ℓ.side m) u s with hI
    set Tz : (Fin (q + 1) → TorusSite (2 * ℓ.side ^ m)) → ℝ := fun z =>
      Matrix.trace (List.ofFn fun j : Fin (q + 1) =>
        sitePlaneKernel (z (s j)) (z (s (finRotate (q + 1) j)))).prod with hTz
    have hsumD : ∑ z ∈ Fintype.piFinset D, (∏ i, blockMeanOfFunction ℓ k m (f i) (z i)) * Tz z =
        ∑ z ∈ Fintype.piFinset A, (∏ i, blockMeanOfFunction ℓ k m (f i) (z i)) * Tz z := by
      refine (Finset.sum_subset (Fintype.piFinset_subset _ _ hsub) ?_).symm
      intro z _ hz
      have hz' : ∃ i, z i ∉ A i := by
        by_contra hno
        push Not at hno
        exact hz (Fintype.mem_piFinset.mpr hno)
      obtain ⟨i, hi⟩ := hz'
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (hhat0 i (z i) hi), zero_mul]
    have hsumA : ∑ z ∈ Fintype.piFinset A, (∏ i, al * blockMeanOfFunction ℓ k m (f i) (z i)) * Tz z =
        al ^ (q + 1) * ∑ z ∈ Fintype.piFinset A, (∏ i, blockMeanOfFunction ℓ k m (f i) (z i)) * Tz z := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      ring
    rw [hsumD] at hr
    rw [hsumA] at hc
    have hcyc : kernelCycleTrace (fun i => responseKernel (A i)
        (fun z => blockMean ℓ.side k (2 * ℓ.side ^ m) z (testWeight ℓ.side k m (f i))) al ka (kr i)) Tc s =
        Matrix.trace (List.ofFn fun j : Fin (q + 1) =>
          (∑ z ∈ A (s j), orientedLocalKernel (blockMeanOfFunction ℓ k m (f (s j)) z) al (ka z) (kr (s j) z)) * Tc).prod := by
      rw [kernelCycleTrace_eq_trace]
      simp only [responseKernel_eq_sum]
    rw [hcyc]
    set Cy := Matrix.trace (List.ofFn fun j : Fin (q + 1) =>
          (∑ z ∈ A (s j), orientedLocalKernel (blockMeanOfFunction ℓ k m (f (s j)) z) al (ka z) (kr (s j) z)) * Tc).prod
      with hCy
    set Gs := ∑ z ∈ Fintype.piFinset A, (∏ i, blockMeanOfFunction ℓ k m (f i) (z i)) * Tz z with hGs
    have hal16 : |al ^ (q + 1)| ≤ 16 := by
      rw [abs_pow]
      calc |al| ^ (q + 1) ≤ 2 ^ (q + 1) := pow_le_pow_left₀ (abs_nonneg _) hal _
        _ ≤ 2 ^ 4 := pow_le_pow_right₀ (by norm_num) (by omega)
        _ = 16 := by norm_num
    have hbound := hCb q nn e₀ ε X hq3 hn hX0 he₀ he₀X hε0 hεX
    have hsplit : Cy - al ^ (q + 1) * I = (Cy - al ^ (q + 1) * Gs) - al ^ (q + 1) * (I - Gs) := by ring
    rw [hsplit]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul]
    have h16 := mul_le_mul hal16 hr (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 16)
    linarith
  have hperm : ∀ t : Finset (Equiv.Perm (Fin (q + 1))), (t.card : ℝ) ≤ 24 := by
    intro t
    have h1 : t.card ≤ (q + 1).factorial := by
      refine (Finset.card_le_univ t).trans (le_of_eq ?_)
      rw [Fintype.card_perm, Fintype.card_fin]
    have h2 : (q + 1).factorial ≤ 24 := by
      interval_cases q <;> decide
    exact_mod_cast h1.trans h2
  rw [hXdef] at hmain
  have hBd : 0 ≤ Cb * (x ^ (-(1 / 2 : ℝ)) + 1 / nn) := by positivity
  simp only [cyclicTraceSum, gaussianCumulantLimit]
  rw [mul_assoc]
  exact scaled_sum_sub_le _ _ _ _ _ hmain (hperm _) hBd
theorem statement_holds (hA : TraceOfLocalKernelCycle) (hB : ContinuumCurvatureKernelBoundAndLipschitz)
    (hD : IntegralNearCellSum) (hE : ExpDecaySumAndBallCard)
    (hF : TraceProdLipschitz) (hG : tupleSupportSitesStatement)
    (hH : TorusDisplacementNearSites) : responseKernelTracesStatement := by
  intro a _
  refine ⟨1, fun _ => 1, 0, fun _ => one_pos, fun L hL _ T _ hTL _ _ _ _ _ => ⟨0, fun y _ _ _ => ?_⟩⟩
  refine of_stepParameters hA hB hD hE hF hG hH (T.stepParameters y) ?_
  show Odd T.side
  rw [hTL]
  exact hL
end YangMills.Construction.ResponseInTheExpansion.ResponseKernelTraces
end
