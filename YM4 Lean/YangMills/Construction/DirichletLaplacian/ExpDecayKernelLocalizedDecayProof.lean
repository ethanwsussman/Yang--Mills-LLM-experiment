import YangMills.Construction.Lattice.SetsOfSitesInEveryDimension
import YangMills.Construction.Lattice.ExpDecayKernelsUnitMesh
import YangMills.Construction.Lattice.OneScaleOperatorsOnCubesWithArbitraryCentresProof
import Mathlib
set_option autoImplicit false
open Finset
noncomputable section
namespace YangMills.Construction.DirichletLaplacian.ExpDecayKernel
open PeriodicLattice
variable {d N : ℕ}
theorem taxicabDist_comm (u v : Torus d N) : taxicabDist u v = taxicabDist v u := by apply _root_.YangMills.SharedProofs.p1021 <;> assumption
theorem taxicabDist_triangle (u v w : Torus d N) :
    taxicabDist u w ≤ taxicabDist u v + taxicabDist v w := by apply _root_.YangMills.Construction.PeriodicLattice.CenteredCubeDecay.taxicabDist_triangle <;> assumption
theorem taxicabDist_le_of_maxDist_le {u v : Torus d N} (h : maxDist u v ≤ 1) :
    taxicabDist u v ≤ d := by apply _root_.YangMills.Construction.PeriodicLattice.CenteredCubeDecay.taxicabDist_le_of_maxDist_le_one <;> assumption
theorem norm_coe_one_le : ‖((1 : ℝ) : AddCircle (N : ℝ))‖ ≤ 1 := by
  simpa using QuotientAddGroup.norm_mk_le_norm (S := AddSubgroup.zmultiples (N : ℝ)) (m := (1 : ℝ))
theorem taxicabDist_add_axisMultiple_le (y : Torus d N) (μ : Fin d) :
    taxicabDist (y + (axisMultiple μ (1 : ℝ) : Torus d N)) y ≤ 1 := by
  unfold taxicabDist
  have h : ∀ ν, ‖(y + (axisMultiple μ (1 : ℝ) : Torus d N)) ν - y ν‖ =
      if ν = μ then ‖((1 : ℝ) : AddCircle (N : ℝ))‖ else 0 := by
    intro ν
    by_cases hν : ν = μ
    · subst hν
      simp [axisMultiple]
    · simp [axisMultiple, hν, Pi.single_eq_of_ne hν]
  simp only [h]
  simpa using norm_coe_one_le (N := N)
theorem exists_int_eq_of_mem_zmultiples {w : AddCircle (N : ℝ)}
    (hw : w ∈ AddSubgroup.zmultiples (((1 : ℝ)) : AddCircle (N : ℝ))) :
    ∃ k : ℤ, w = ((k : ℝ) : AddCircle (N : ℝ)) := by
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hw
  refine ⟨k, ?_⟩
  rw [← AddCircle.coe_zsmul]
  simp
theorem site_mem_zmultiples {s : Mesh N} (hs : s.h = 1) (z : GridPoint d s) (μ : Fin d) :
    (z : Torus d N) μ ∈ AddSubgroup.zmultiples (((1 : ℝ)) : AddCircle (N : ℝ)) := by
  have := z.2 μ (Set.mem_univ μ)
  rwa [hs] at this
theorem exists_fin_three_lift (r : ℝ) {w : AddCircle (N : ℝ)}
    (hw : w ∈ AddSubgroup.zmultiples (((1 : ℝ)) : AddCircle (N : ℝ)))
    (h : ‖w - (r : AddCircle (N : ℝ))‖ ≤ 1) :
    ∃ t : Fin 3, w = (((⌈r - 1⌉ + ((t : ℕ) : ℤ) : ℤ) : ℝ) : AddCircle (N : ℝ)) := by
  obtain ⟨k, rfl⟩ := exists_int_eq_of_mem_zmultiples hw
  rw [← AddCircle.coe_sub, AddCircle.norm_eq] at h
  set n := round ((N : ℝ)⁻¹ * ((k : ℝ) - r)) with hn
  have hab := abs_le.mp h
  set k' : ℤ := k - n * (N : ℤ) with hk'
  have hk'r : (k' : ℝ) = (k : ℝ) - (n : ℝ) * (N : ℝ) := by rw [hk']; push_cast; ring
  have hlo : r - 1 ≤ (k' : ℝ) := by rw [hk'r]; linarith [hab.1]
  have hhi : (k' : ℝ) ≤ r + 1 := by rw [hk'r]; linarith [hab.2]
  have h1 : ⌈r - 1⌉ ≤ k' := Int.ceil_le.mpr hlo
  have h2 : k' ≤ ⌈r - 1⌉ + 2 := by
    have : (k' : ℝ) ≤ ((⌈r - 1⌉ + 2 : ℤ) : ℝ) := by
      push_cast
      linarith [Int.le_ceil (r - 1)]
    exact_mod_cast this
  refine ⟨⟨(k' - ⌈r - 1⌉).toNat, by omega⟩, ?_⟩
  have h3 : ⌈r - 1⌉ + (((k' - ⌈r - 1⌉).toNat : ℕ) : ℤ) = k' := by omega
  simp only [h3]
  have hz : (((n : ℝ) * (N : ℝ) : ℝ) : AddCircle (N : ℝ)) = 0 :=
    (AddCircle.coe_eq_zero_iff (N : ℝ)).2 ⟨n, by simp⟩
  rw [hk'r, AddCircle.coe_sub, hz, sub_zero]
open Classical in
def ballSites (s : Mesh N) (u : Torus d N) : Finset (GridPoint d s) :=
  univ.filter fun x => x ∈ closedMaxBall s u
theorem card_ballSites_le {s : Mesh N} (hs : s.h = 1) (u : Torus d N) :
    (ballSites s u).card ≤ 3 ^ d := by
  classical
  choose r hr using fun μ => QuotientAddGroup.mk_surjective (u μ)
  let Φ : (Fin d → Fin 3) → Torus d N := fun t μ =>
    (((⌈r μ - 1⌉ + ((t μ : ℕ) : ℤ) : ℤ) : ℝ) : AddCircle (N : ℝ))
  have hsub : (ballSites (d := d) s u).image Subtype.val ⊆ univ.image Φ := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
    have hx' : maxDist (x : Torus d N) u ≤ 1 := (mem_filter.mp hx).2
    have hμ : ∀ μ, ∃ t : Fin 3, (x : Torus d N) μ =
        (((⌈r μ - 1⌉ + ((t : ℕ) : ℤ) : ℤ) : ℝ) : AddCircle (N : ℝ)) := fun μ =>
      exists_fin_three_lift (r μ) (site_mem_zmultiples hs x μ) (by
        have h1 := (norm_le_pi_norm ((x : Torus d N) - u) μ).trans hx'
        have h2 : ((r μ : ℝ) : AddCircle (N : ℝ)) = u μ := hr μ
        rw [h2]
        exact h1)
    choose t ht using hμ
    exact mem_image.mpr ⟨t, mem_univ _, funext fun μ => (ht μ).symm⟩
  have h1 := card_le_card hsub
  rw [card_image_of_injective _ Subtype.val_injective] at h1
  calc (ballSites s u).card ≤ (univ.image Φ).card := h1
    _ ≤ (univ : Finset (Fin d → Fin 3)).card := card_image_le
    _ = 3 ^ d := by simp
section Fields
variable {s : Mesh N} {ι κ : Type}
theorem abs_sub_le_abs_add_abs (a b : ℝ) : |a - b| ≤ |a| + |b| :=
  abs_le.mpr ⟨by linarith [neg_abs_le a, le_abs_self b], by linarith [le_abs_self a, neg_abs_le b]⟩
theorem scaledFun_sum_apply {α X : Type} (t : Finset α) (F : α → ScaledFun d s X) (x : X) :
    (∑ a ∈ t, F a) x = ∑ a ∈ t, F a x := by apply _root_.YangMills.Construction.PeriodicLattice.CenteredDecay.finsetSum_apply <;> assumption
def expWeightedSum [Fintype ι] (θ : ℝ) (u' : Torus d N) (f : MultiField d s ι) : ℝ :=
  ∑ q : ι × GridPoint d s, |f q| * Real.exp (θ * taxicabDist (q.2 : Torus d N) u')
def ExpDominated (θ : ℝ) (u' : Torus d N) (f : MultiField d s ι) (A : ℝ) : Prop :=
  ∀ q : ι × GridPoint d s, |f q| ≤ A * Real.exp (-θ * taxicabDist (q.2 : Torus d N) u')
theorem expWeightedSum_nonneg [Fintype ι] (θ : ℝ) (u' : Torus d N) (f : MultiField d s ι) :
    0 ≤ expWeightedSum θ u' f :=
  sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
theorem ExpDominated.mono {θ : ℝ} {u' : Torus d N} {f : MultiField d s ι} {A B : ℝ}
    (h : ExpDominated θ u' f A) (hAB : A ≤ B) : ExpDominated θ u' f B := fun q =>
  (h q).trans (mul_le_mul_of_nonneg_right hAB (Real.exp_pos _).le)
theorem exp_neg_mul_taxicab_le {θ : ℝ} (hθ : 0 ≤ θ) {y y' u' : Torus d N}
    (h : taxicabDist y y' ≤ 1) :
    Real.exp (-θ * taxicabDist y' u') ≤ Real.exp θ * Real.exp (-θ * taxicabDist y u') := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have h1 := taxicabDist_triangle y y' u'
  nlinarith [mul_le_mul_of_nonneg_left (h1.trans (add_le_add_left h _)) hθ]
theorem taxicabDist_add_basisStep_le (hs : s.h = 1) (y : GridPoint d s) (μ : Fin d) :
    taxicabDist ((y + s.basisStep μ : GridPoint d s) : Torus d N) y ≤ 1 := by
  have h : ((y + s.basisStep μ : GridPoint d s) : Torus d N) =
      (y : Torus d N) + (axisMultiple μ (1 : ℝ) : Torus d N) := by
    show (y : Torus d N) + axisMultiple μ s.h = _
    rw [hs]
  rw [h]
  exact taxicabDist_add_axisMultiple_le _ μ
theorem taxicabDist_sub_basisStep_le (hs : s.h = 1) (y : GridPoint d s) (μ : Fin d) :
    taxicabDist (y : Torus d N) ((y - s.basisStep μ : GridPoint d s) : Torus d N) ≤ 1 := by
  have := taxicabDist_add_basisStep_le hs (y - s.basisStep μ) μ
  rwa [sub_add_cancel] at this
theorem forwardDiff_apply_unit (hs : s.h = 1) (μ : Fin d) (g : SiteFun d s) (x : GridPoint d s) :
    forwardDiff s μ g x = g (x + s.basisStep μ) - g x := by
  show s.h⁻¹ * (g (x + s.basisStep μ) - g x) = _
  rw [hs]
  simp
theorem fieldGrad_apply_unit (hs : s.h = 1) (f : MultiField d s ι) (μ : Fin d) (i : ι)
    (x : GridPoint d s) :
    fieldGrad s ι f ((μ, i), x) = f (i, x + s.basisStep μ) - f (i, x) :=
  forwardDiff_apply_unit hs μ (f.comp i) x
theorem ExpDominated.abs_sub_le {θ θbar A : ℝ} {u' : Torus d N} {f : MultiField d s ι}
    (hf : ExpDominated θ u' f A) (hθ : 0 ≤ θ) (hb : θ ≤ θbar) (hA : 0 ≤ A) (k : ι)
    {y y' : GridPoint d s} (h : taxicabDist (y : Torus d N) y' ≤ 1) :
    |f (k, y') - f (k, y)| ≤
      2 * Real.exp θbar * A * Real.exp (-θ * taxicabDist (y : Torus d N) u') := by
  have h1 := hf (k, y')
  have h2 := hf (k, y)
  have h3 := exp_neg_mul_taxicab_le (u' := u') hθ h
  have h4 : Real.exp θ ≤ Real.exp θbar := Real.exp_le_exp.mpr hb
  have h5 : 1 ≤ Real.exp θbar := Real.one_le_exp (hθ.trans hb)
  simp only at h1 h2
  set w := Real.exp (-θ * taxicabDist (y : Torus d N) u') with hw
  have hw0 : 0 < w := Real.exp_pos _
  have hAw : 0 ≤ A * w := mul_nonneg hA hw0.le
  have h6 : A * Real.exp (-θ * taxicabDist (y' : Torus d N) u') ≤ Real.exp θbar * (A * w) := by
    calc A * Real.exp (-θ * taxicabDist (y' : Torus d N) u') ≤ A * (Real.exp θ * w) :=
          mul_le_mul_of_nonneg_left h3 hA
      _ = Real.exp θ * (A * w) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h4 hAw
  have h7 : A * w ≤ Real.exp θbar * (A * w) := le_mul_of_one_le_left hAw h5
  have h8 := abs_sub_le_abs_add_abs (f (k, y')) (f (k, y))
  nlinarith
theorem ExpDominated.fieldGrad {θ θbar A : ℝ} {u' : Torus d N} {f : MultiField d s ι}
    (hf : ExpDominated θ u' f A) (hs : s.h = 1) (hθ : 0 ≤ θ) (hb : θ ≤ θbar) (hA : 0 ≤ A) :
    ExpDominated θ u' (PeriodicLattice.fieldGrad s ι f) (2 * Real.exp θbar * A) := by
  rintro ⟨⟨μ, i⟩, y⟩
  rw [fieldGrad_apply_unit hs]
  have h1 : taxicabDist (y : Torus d N) ((y + s.basisStep μ : GridPoint d s) : Torus d N) ≤ 1 := by
    rw [taxicabDist_comm]
    exact taxicabDist_add_basisStep_le hs y μ
  exact hf.abs_sub_le hθ hb hA i h1
theorem fieldLaplacian_apply_unit (hs : s.h = 1) (hD : ForwardDiffTranslationLaws d s)
    (f : MultiField d s ι) (i : ι) (y : GridPoint d s) :
    fieldLaplacian s ι f (i, y) =
      ∑ μ, (fieldGrad s ι f ((μ, i), y - s.basisStep μ) - fieldGrad s ι f ((μ, i), y)) := by
  show discreteLaplacian s (f.comp i) y = _
  unfold discreteLaplacian
  rw [LinearMap.sum_apply, scaledFun_sum_apply]
  refine sum_congr rfl fun μ _ => ?_
  rw [LinearMap.comp_apply, hD.adjoint_forwardDiff_apply, forwardDiff_apply_unit hs, sub_add_cancel]
  show _ = forwardDiff s μ (f.comp i) (y - s.basisStep μ) - forwardDiff s μ (f.comp i) y
  ring
theorem ExpDominated.fieldLaplacian {θ θbar A : ℝ} {u' : Torus d N} {f : MultiField d s ι}
    (hf : ExpDominated θ u' f A) (hs : s.h = 1) (hD : ForwardDiffTranslationLaws d s)
    (hθ : 0 ≤ θ) (hb : θ ≤ θbar) (hA : 0 ≤ A) :
    ExpDominated θ u' (PeriodicLattice.fieldLaplacian s ι f)
      (d * (2 * Real.exp θbar) ^ 2 * A) := by
  rintro ⟨i, y⟩
  rw [fieldLaplacian_apply_unit hs hD]
  have ha : 0 ≤ 2 * Real.exp θbar * A := by positivity
  have hg := hf.fieldGrad hs hθ hb hA
  calc |∑ μ, (PeriodicLattice.fieldGrad s ι f ((μ, i), y - s.basisStep μ) -
          PeriodicLattice.fieldGrad s ι f ((μ, i), y))|
      ≤ ∑ μ, |PeriodicLattice.fieldGrad s ι f ((μ, i), y - s.basisStep μ) -
          PeriodicLattice.fieldGrad s ι f ((μ, i), y)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _μ : Fin d, 2 * Real.exp θbar * (2 * Real.exp θbar * A) *
          Real.exp (-θ * taxicabDist (y : Torus d N) u') :=
        sum_le_sum fun μ _ => hg.abs_sub_le hθ hb ha (μ, i) (taxicabDist_sub_basisStep_le hs y μ)
    _ = _ := by simp; ring
theorem norm_sq_eq_sum_sq [Fintype ι] (hs : s.h = 1) (f : MultiField d s ι) :
    ‖f‖ ^ 2 = ∑ q, f q ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ScaledFun.inner_eq, hs]
  exact sum_congr rfl fun q _ => by rw [one_pow]; ring
theorem abs_le_maxNorm [Fintype ι] (J : MultiField d s ι) (q : ι × GridPoint d s) :
    |J q| ≤ MultiField.maxNorm J :=
  calc |J q| ≤ MultiField.normAt J q.2 :=
        le_ciSup (f := fun i => |J (i, q.2)|) (Set.finite_range _).bddAbove q.1
    _ ≤ MultiField.maxNorm J :=
        le_ciSup (f := fun x => MultiField.normAt J x) (Set.finite_range _).bddAbove q.2
theorem abs_le_siteFun_maxNorm (ζ : SiteFun d s) (x : GridPoint d s) :
    |ζ x| ≤ SiteFun.maxNorm ζ :=
  le_ciSup (f := fun x => |ζ x|) (Set.finite_range _).bddAbove x
theorem maxNorm_nonneg [Fintype ι] (J : MultiField d s ι) : 0 ≤ MultiField.maxNorm J :=
  Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => abs_nonneg _
theorem siteFun_maxNorm_nonneg (ζ : SiteFun d s) : 0 ≤ SiteFun.maxNorm ζ :=
  Real.iSup_nonneg fun _ => abs_nonneg _
theorem holderSemi_nonneg [Fintype ι] (α : ℝ) (J : MultiField d s ι) :
    0 ≤ MultiField.holderSemi α J := by apply _root_.YangMills.Construction.CubeCovering.RescaledGreen.multiField_holderSemi_nonneg <;> assumption
theorem siteFun_holderSemi_nonneg (α : ℝ) (ζ : SiteFun d s) :
    0 ≤ SiteFun.holderSemi α ζ := by apply _root_.YangMills.Construction.CubeCovering.RescaledGreen.siteFun_holderSemi_nonneg <;> assumption
def ballPairs (ι : Type) [Fintype ι] (s : Mesh N) (u' : Torus d N) :
    Finset (ι × GridPoint d s) :=
  univ ×ˢ ballSites s u'
theorem card_ballPairs_le [Fintype ι] (hs : s.h = 1) (u' : Torus d N) :
    ((ballPairs ι s u').card : ℝ) ≤ Fintype.card ι * 3 ^ d := by
  rw [ballPairs, card_product, card_univ]
  push_cast
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  exact_mod_cast card_ballSites_le hs u'
theorem mem_ballPairs [Fintype ι] {u' : Torus d N} {q : ι × GridPoint d s} :
    q ∈ ballPairs ι s u' ↔ q.2 ∈ closedMaxBall s u' := by
  classical
  simp [ballPairs, ballSites]
theorem expWeightedSum_le_ball [Fintype ι] {θ : ℝ} (hθ : 0 ≤ θ) {u' : Torus d N}
    {J : MultiField d s ι} (hJ : MultiField.SupportedIn J (closedMaxBall s u')) :
    expWeightedSum θ u' J ≤ Real.exp (θ * d) * ∑ q ∈ ballPairs ι s u', |J q| := by
  unfold expWeightedSum
  rw [mul_sum]
  have e := sum_subset (subset_univ (ballPairs ι s u'))
    (f := fun q => |J q| * Real.exp (θ * taxicabDist (q.2 : Torus d N) u')) (by
      rintro ⟨i, y⟩ _ hq
      have hy : y ∉ closedMaxBall s u' := fun hy => hq (mem_ballPairs.mpr hy)
      simp only
      rw [hJ y hy i]
      simp)
  rw [← e]
  refine sum_le_sum fun q hq => ?_
  rw [mul_comm (Real.exp (θ * (d : ℝ)))]
  have hq' : maxDist (q.2 : Torus d N) u' ≤ 1 := mem_ballPairs.mp hq
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left (taxicabDist_le_of_maxDist_le hq') hθ)) (abs_nonneg _)
theorem expWeightedSum_sq_le [Fintype ι] (hs : s.h = 1) {θ : ℝ} (hθ : 0 ≤ θ)
    {u' : Torus d N} {J : MultiField d s ι} (hJ : MultiField.SupportedIn J (closedMaxBall s u')) :
    expWeightedSum θ u' J ^ 2 ≤
      Real.exp (θ * d) ^ 2 * (Fintype.card ι * 3 ^ d * ‖J‖ ^ 2) := by
  have h1 : (∑ q ∈ ballPairs ι s u', |J q|) ^ 2 ≤ Fintype.card ι * 3 ^ d * ‖J‖ ^ 2 := by
    calc (∑ q ∈ ballPairs ι s u', |J q|) ^ 2
        ≤ ((ballPairs ι s u').card : ℝ) * ∑ q ∈ ballPairs ι s u', |J q| ^ 2 :=
          sq_sum_le_card_mul_sum_sq
      _ ≤ ((ballPairs ι s u').card : ℝ) * ‖J‖ ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          rw [norm_sq_eq_sum_sq hs]
          simp only [sq_abs]
          exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => sq_nonneg _
      _ ≤ _ := mul_le_mul_of_nonneg_right (card_ballPairs_le hs u') (sq_nonneg _)
  calc expWeightedSum θ u' J ^ 2
      ≤ (Real.exp (θ * d) * ∑ q ∈ ballPairs ι s u', |J q|) ^ 2 :=
        pow_le_pow_left₀ (expWeightedSum_nonneg θ u' J) (expWeightedSum_le_ball hθ hJ) 2
    _ = Real.exp (θ * d) ^ 2 * (∑ q ∈ ballPairs ι s u', |J q|) ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
theorem abs_mulLeft_le [Fintype ι] {u : Torus d N} {ζ : SiteFun d s}
    (hζ : SiteFun.SupportedIn ζ (closedMaxBall s u)) {F : MultiField d s ι} {B : ℝ} (hB : 0 ≤ B)
    (hF : ∀ k y, y ∈ closedMaxBall s u → |F (k, y)| ≤ B) (q : ι × GridPoint d s) :
    |MultiField.mulLeft ζ F q| ≤ SiteFun.maxNorm ζ * B := by
  show |ζ q.2 * F q| ≤ _
  by_cases hy : q.2 ∈ closedMaxBall s u
  · rw [abs_mul]
    exact mul_le_mul (abs_le_siteFun_maxNorm ζ q.2) (hF q.1 q.2 hy) (abs_nonneg _)
      (siteFun_maxNorm_nonneg ζ)
  · rw [hζ _ hy, zero_mul, abs_zero]
    exact mul_nonneg (siteFun_maxNorm_nonneg ζ) hB
theorem norm_mulLeft_sq_le [Fintype ι] (hs : s.h = 1) {u : Torus d N} {ζ : SiteFun d s}
    (hζ : SiteFun.SupportedIn ζ (closedMaxBall s u)) {F : MultiField d s ι} {B : ℝ} (hB : 0 ≤ B)
    (hF : ∀ k y, y ∈ closedMaxBall s u → |F (k, y)| ≤ B) :
    ‖MultiField.mulLeft ζ F‖ ^ 2 ≤ Fintype.card ι * 3 ^ d * (SiteFun.maxNorm ζ * B) ^ 2 := by
  rw [norm_sq_eq_sum_sq hs]
  have e := sum_subset (subset_univ (ballPairs ι s u))
    (f := fun q => MultiField.mulLeft ζ F q ^ 2) (by
      rintro ⟨i, y⟩ _ hq
      have hy : y ∉ closedMaxBall s u := fun hy => hq (mem_ballPairs.mpr hy)
      show (ζ y * F (i, y)) ^ 2 = 0
      rw [hζ y hy]
      simp)
  rw [← e]
  calc ∑ q ∈ ballPairs ι s u, MultiField.mulLeft ζ F q ^ 2
      ≤ (ballPairs ι s u).card • (SiteFun.maxNorm ζ * B) ^ 2 :=
        sum_le_card_nsmul _ _ _ fun q _ => by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (abs_mulLeft_le hζ hB hF q) 2
    _ = ((ballPairs ι s u).card : ℝ) * (SiteFun.maxNorm ζ * B) ^ 2 := nsmul_eq_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (card_ballPairs_le hs u) (sq_nonneg _)
theorem exp_neg_mul_ball_le {θ : ℝ} (hθ : 0 ≤ θ) {u u' : Torus d N} {y : GridPoint d s}
    (hy : y ∈ closedMaxBall s u) :
    Real.exp (-θ * taxicabDist (y : Torus d N) u') ≤
      Real.exp (θ * d) * Real.exp (-θ * taxicabDist u u') := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have h1 := taxicabDist_triangle u (y : Torus d N) u'
  have h2 : taxicabDist u (y : Torus d N) ≤ d := by
    rw [taxicabDist_comm]
    exact taxicabDist_le_of_maxDist_le hy
  have h3 : taxicabDist u u' ≤ d + taxicabDist (y : Torus d N) u' := by linarith
  nlinarith [mul_le_mul_of_nonneg_left h3 hθ]
theorem exp_two_mul_add_two_mul (d : ℕ) (θbar : ℝ) :
    Real.exp ((2 * (d : ℝ) + 2) * θbar) =
      Real.exp θbar ^ 2 * Real.exp (θbar * d) ^ 2 := by
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  push_cast
  ring
theorem norm_mulLeft_le [Fintype ι] [Fintype κ] (hs : s.h = 1) (hd : 1 ≤ d) {θ θbar c₀ C : ℝ}
    (hθ : 0 ≤ θ) (hb : θ ≤ θbar) (hc : 0 ≤ c₀) {u u' : Torus d N} {ζ : SiteFun d s}
    {F : MultiField d s κ} {J : MultiField d s ι}
    (hcard : (Fintype.card κ : ℝ) * Fintype.card ι ≤ (d : ℝ) ^ 4) (hC0 : 0 ≤ C)
    (hC : C ≤ (2 * Real.exp θbar) ^ 2)
    (hF : ExpDominated θ u' F (C * (c₀ * expWeightedSum θ u' J)))
    (hζ : SiteFun.SupportedIn ζ (closedMaxBall s u))
    (hJ : MultiField.SupportedIn J (closedMaxBall s u')) :
    ‖MultiField.mulLeft ζ F‖ ≤ c₀ * unitMeshDecayConst d θbar *
      Real.exp (-θ * taxicabDist u u') * SiteFun.maxNorm ζ * ‖J‖ := by
  have hW0 := expWeightedSum_nonneg θ u' J
  have hZ := siteFun_maxNorm_nonneg ζ
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hQ : Real.exp (θ * d) ≤ Real.exp (θbar * d) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg _))
  have hE0 := Real.exp_pos (-θ * taxicabDist u u')
  set E := Real.exp (-θ * taxicabDist u u') with hE
  set P := Real.exp θbar with hP
  set Q := Real.exp (θbar * d) with hQdef
  set W := expWeightedSum θ u' J with hWdef
  set Z := SiteFun.maxNorm ζ with hZdef
  have hB0 : 0 ≤ (2 * P) ^ 2 * (c₀ * W) * (Q * E) := by positivity
  have hFc : ∀ k y, y ∈ closedMaxBall s u → |F (k, y)| ≤ (2 * P) ^ 2 * (c₀ * W) * (Q * E) := by
    intro k y hy
    calc |F (k, y)| ≤ C * (c₀ * W) * Real.exp (-θ * taxicabDist (y : Torus d N) u') := hF (k, y)
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right hC (mul_nonneg hc hW0))
          ((exp_neg_mul_ball_le hθ hy).trans (mul_le_mul_of_nonneg_right hQ hE0.le))
          (Real.exp_pos _).le (by positivity)
  have hW2 : W ^ 2 ≤ Q ^ 2 * (Fintype.card ι * 3 ^ d * ‖J‖ ^ 2) :=
    (expWeightedSum_sq_le hs hθ hJ).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Real.exp_pos _).le hQ 2) (by positivity))
  have hd4 : (d : ℝ) ^ 4 ≤ 4 * (d : ℝ) ^ 8 := by
    have : (d : ℝ) ^ 4 ≤ (d : ℝ) ^ 8 := pow_le_pow_right₀ hd1 (by norm_num)
    nlinarith [pow_pos (lt_of_lt_of_le one_pos hd1) 8]
  set R := (3 ^ d : ℝ) ^ 2 * Z ^ 2 * P ^ 4 * c₀ ^ 2 * Q ^ 4 * E ^ 2 * ‖J‖ ^ 2 with hR
  have hsq : ‖MultiField.mulLeft ζ F‖ ^ 2 ≤
      (c₀ * unitMeshDecayConst d θbar * E * Z * ‖J‖) ^ 2 := by
    calc ‖MultiField.mulLeft ζ F‖ ^ 2
        ≤ Fintype.card κ * 3 ^ d * (Z * ((2 * P) ^ 2 * (c₀ * W) * (Q * E))) ^ 2 :=
          norm_mulLeft_sq_le hs hζ hB0 hFc
      _ = Fintype.card κ * 3 ^ d * (Z * ((2 * P) ^ 2 * c₀ * (Q * E))) ^ 2 * W ^ 2 := by ring
      _ ≤ Fintype.card κ * 3 ^ d * (Z * ((2 * P) ^ 2 * c₀ * (Q * E))) ^ 2 *
            (Q ^ 2 * (Fintype.card ι * 3 ^ d * ‖J‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hW2 (by positivity)
      _ = ((Fintype.card κ : ℝ) * Fintype.card ι) * (16 * R) := by rw [hR]; ring
      _ ≤ (d : ℝ) ^ 4 * (16 * R) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ ≤ (4 * (d : ℝ) ^ 8) * (16 * R) := mul_le_mul_of_nonneg_right hd4 (by positivity)
      _ = _ := by
          unfold unitMeshDecayConst
          rw [exp_two_mul_add_two_mul, hR]
          ring
  have hT0 : 0 ≤ c₀ * unitMeshDecayConst d θbar * E * Z * ‖J‖ := by
    unfold unitMeshDecayConst
    positivity
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hT0 two_ne_zero).mp hsq
end Fields
end YangMills.Construction.DirichletLaplacian.ExpDecayKernel
