import YangMills.Construction.ClusterExpansionOfAStep.DensitiesAgainstAMirror
import YangMills.Construction.ResponseInTheExpansion.MomentsOfAStepOfTheCurvatureProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages hiding unitStep
open LumpContours TorusFields MirrorDensities TorusLumps ExponentialSums TorusMirror TorusFrame
namespace ResponseInTheExpansion
open Classical
namespace MirrorKernels
def lieInner (w w' : imaginaryQuaternions) : ℝ :=
  ∑ e : Fin 3, imaginaryComponent e w * imaginaryComponent e w'
theorem abs_imaginaryComponent_le (e : Fin 3) (w : imaginaryQuaternions) :
    |imaginaryComponent e w| ≤ ‖(w : ℍ[ℝ])‖ := by apply _root_.YangMills.SharedProofs.p13926 <;> assumption
theorem imaginaryComponent_sub (e : Fin 3) (a b : imaginaryQuaternions) :
    imaginaryComponent e (a - b) = imaginaryComponent e a - imaginaryComponent e b := by
  fin_cases e <;> simp [imaginaryComponent]
theorem abs_lieInner_sub_le (a b c d : imaginaryQuaternions) :
    |lieInner a b - lieInner c d| ≤
      3 * (‖((a - c : imaginaryQuaternions) : ℍ[ℝ])‖ * ‖(b : ℍ[ℝ])‖ +
        ‖(c : ℍ[ℝ])‖ * ‖((b - d : imaginaryQuaternions) : ℍ[ℝ])‖) := by
  unfold lieInner
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h : ∀ e ∈ (Finset.univ : Finset (Fin 3)),
      |imaginaryComponent e a * imaginaryComponent e b - imaginaryComponent e c * imaginaryComponent e d| ≤
        ‖((a - c : imaginaryQuaternions) : ℍ[ℝ])‖ * ‖(b : ℍ[ℝ])‖ +
          ‖(c : ℍ[ℝ])‖ * ‖((b - d : imaginaryQuaternions) : ℍ[ℝ])‖ := by
    intro e _
    have e1 : imaginaryComponent e a * imaginaryComponent e b - imaginaryComponent e c * imaginaryComponent e d =
        imaginaryComponent e (a - c) * imaginaryComponent e b +
          imaginaryComponent e c * imaginaryComponent e (b - d) := by
      rw [imaginaryComponent_sub, imaginaryComponent_sub]
      ring
    rw [e1]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    exact add_le_add
      (mul_le_mul (abs_imaginaryComponent_le _ _) (abs_imaginaryComponent_le _ _) (abs_nonneg _) (norm_nonneg _))
      (mul_le_mul (abs_imaginaryComponent_le _ _) (abs_imaginaryComponent_le _ _) (abs_nonneg _) (norm_nonneg _))
  refine (Finset.sum_le_sum h).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num
section Translation
variable {n m : ℕ} [NeZero n] [NeZero (4 * m)]
def translatePlaquette (z : TorusSite n) (a : TorusPlaquette (4 * m)) : TorusPlaquette n :=
  (z + siteOfInt (offset 0 a.1), a.2)
def translatedKernel (S : Finset (TorusPlaquette (4 * m))) (z : TorusSite n)
    (κ : TorusPlaquette (4 * m) → TorusPlaquette (4 * m) → ℝ) (p p' : TorusPlaquette n) : ℝ :=
  ∑ a ∈ S, ∑ b ∈ S, if translatePlaquette z a = p ∧ translatePlaquette z b = p' then κ a b else 0
theorem translatePlaquette_mem_plaquettesIn (z : TorusSite n) {a : TorusPlaquette (4 * m)} (h : a.2.1 < a.2.2) :
    translatePlaquette z a ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)) := by
  simp [plaquettesIn, translatePlaquette, h]
theorem sum_translatedKernel_mul (S : Finset (TorusPlaquette (4 * m))) (z : TorusSite n)
    (κ : TorusPlaquette (4 * m) → TorusPlaquette (4 * m) → ℝ)
    (Φ : TorusPlaquette n → TorusPlaquette n → ℝ) (hS : ∀ a ∈ S, a.2.1 < a.2.2) :
    ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
        translatedKernel S z κ p p' * Φ p p' =
      ∑ a ∈ S, ∑ b ∈ S, κ a b * Φ (translatePlaquette z a) (translatePlaquette z b) := by
  simp only [translatedKernel, Finset.sum_mul]
  have e1 : ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
      ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
      ∑ a ∈ S, ∑ b ∈ S,
        (if translatePlaquette z a = p ∧ translatePlaquette z b = p' then κ a b else 0) * Φ p p' =
      ∑ a ∈ S, ∑ b ∈ S, ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
        ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
        (if translatePlaquette z a = p ∧ translatePlaquette z b = p' then κ a b else 0) * Φ p p' := by
    rw [Finset.sum_congr rfl fun p _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_congr rfl fun p _ => Finset.sum_comm]
    exact Finset.sum_comm
  rw [e1]
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
  rw [Finset.sum_eq_single (translatePlaquette z a), Finset.sum_eq_single (translatePlaquette z b)]
  · simp
  · intro p' _ hne
    simp [Ne.symm hne]
  · intro h
    exact absurd (translatePlaquette_mem_plaquettesIn z (hS b hb)) h
  · intro p _ hne
    refine Finset.sum_eq_zero fun p' _ => ?_
    simp [Ne.symm hne]
  · intro h
    exact absurd (translatePlaquette_mem_plaquettesIn z (hS a ha)) h
theorem supDist_translatePlaquette_le (z : TorusSite n) (a : TorusPlaquette (4 * m)) :
    _root_.YangMills.Construction.TorusFields.supDist (translatePlaquette z a).1 z ≤ _root_.YangMills.Construction.TorusFields.supDist a.1 (0 : TorusSite (4 * m)) := by
  rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
  exact _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le z _ _ fun i => natAbs_offset_le 0 a.1 i
theorem eq_of_add_siteOfInt_offset_eq {R : ℕ} (hn : 2 * R < n) {x y : TorusSite (4 * m)}
    (hx : _root_.YangMills.Construction.TorusFields.supDist x 0 ≤ R) (hy : _root_.YangMills.Construction.TorusFields.supDist y 0 ≤ R)
    (z : TorusSite n) (h : z + siteOfInt (offset 0 x) = z + siteOfInt (offset 0 y)) : x = y := by
  have h1 : (siteOfInt (offset 0 x) : TorusSite n) = siteOfInt (offset 0 y) := add_left_cancel h
  have h2 : offset 0 x = offset 0 y := by
    refine siteOfInt_injective_of_abs_sub_lt (fun i => ?_) h1
    have a1 := abs_offset_le (0 : TorusSite (4 * m)) x i
    have a2 := abs_offset_le (0 : TorusSite (4 * m)) y i
    calc |offset 0 x i - offset 0 y i| ≤ |offset 0 x i| + |offset 0 y i| := abs_sub _ _
      _ < n := by linarith
  have e1 := add_siteOfInt_offset (0 : TorusSite (4 * m)) x
  have e2 := add_siteOfInt_offset (0 : TorusSite (4 * m)) y
  rw [← e1, ← e2, h2]
theorem translatePlaquette_injective {R : ℕ} (hn : 2 * R < n) {a b : TorusPlaquette (4 * m)}
    (ha : _root_.YangMills.Construction.TorusFields.supDist a.1 0 ≤ R) (hb : _root_.YangMills.Construction.TorusFields.supDist b.1 0 ≤ R)
    (z : TorusSite n) (h : translatePlaquette z a = translatePlaquette z b) : a = b := by
  have h1 : z + siteOfInt (offset 0 a.1) = z + siteOfInt (offset 0 b.1) := (Prod.ext_iff.mp h).1
  have h2 : a.2 = b.2 := (Prod.ext_iff.mp h).2
  exact Prod.ext (eq_of_add_siteOfInt_offset_eq hn ha hb z h1) h2
theorem translatedKernel_eq_zero_of_far (S : Finset (TorusPlaquette (4 * m))) (z : TorusSite n)
    (κ : TorusPlaquette (4 * m) → TorusPlaquette (4 * m) → ℝ) {ρ : ℝ}
    (hρ : ∀ a ∈ S, (_root_.YangMills.Construction.TorusFields.supDist a.1 (0 : TorusSite (4 * m)) : ℝ) ≤ ρ) (p p' : TorusPlaquette n)
    (h : ρ < (_root_.YangMills.Construction.TorusFields.supDist p.1 z : ℝ) ∨ ρ < (_root_.YangMills.Construction.TorusFields.supDist p'.1 z : ℝ)) : translatedKernel S z κ p p' = 0 := by
  refine Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb => ?_
  rw [if_neg]
  rintro ⟨e1, e2⟩
  have t1 : (_root_.YangMills.Construction.TorusFields.supDist p.1 z : ℝ) ≤ ρ := by
    rw [← e1]
    exact le_trans (by exact_mod_cast _root_.YangMills.Construction.ResponseInTheExpansion.MirrorKernels.supDist_translatePlaquette_le z a) (hρ a ha)
  have t2 : (_root_.YangMills.Construction.TorusFields.supDist p'.1 z : ℝ) ≤ ρ := by
    rw [← e2]
    exact le_trans (by exact_mod_cast _root_.YangMills.Construction.ResponseInTheExpansion.MirrorKernels.supDist_translatePlaquette_le z b) (hρ b hb)
  rcases h with h | h <;> linarith
theorem abs_translatedKernel_le (S : Finset (TorusPlaquette (4 * m))) (z : TorusSite n)
    (κ : TorusPlaquette (4 * m) → TorusPlaquette (4 * m) → ℝ) {R : ℕ}
    (hn : 2 * R < n) (hR : ∀ a ∈ S, _root_.YangMills.Construction.TorusFields.supDist a.1 (0 : TorusSite (4 * m)) ≤ R) {D d : ℝ} (hd : 0 ≤ d) (hD : 0 ≤ D)
    (hκ : ∀ a ∈ S, ∀ b ∈ S, |κ a b| ≤
      D * Real.exp (-(d * max (_root_.YangMills.Construction.TorusFields.supDist a.1 (0 : TorusSite (4 * m)) : ℝ) (_root_.YangMills.Construction.TorusFields.supDist b.1 (0 : TorusSite (4 * m)) : ℝ))))
    (p p' : TorusPlaquette n) :
    |translatedKernel S z κ p p'| ≤ D * Real.exp (-(d * max (_root_.YangMills.Construction.TorusFields.supDist p.1 z : ℝ) (_root_.YangMills.Construction.TorusFields.supDist p'.1 z : ℝ))) := by
  by_cases h : ∃ a ∈ S, ∃ b ∈ S, translatePlaquette z a = p ∧ translatePlaquette z b = p'
  · obtain ⟨a, ha, b, hb, e1, e2⟩ := h
    have hv : translatedKernel S z κ p p' = κ a b := by
      unfold translatedKernel
      rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
      · rw [if_pos ⟨e1, e2⟩]
      · intro b' hb' hne
        rw [if_neg]
        rintro ⟨_, f⟩
        exact hne (translatePlaquette_injective hn (hR b' hb') (hR b hb) z (f.trans e2.symm))
      · intro h'
        exact absurd hb h'
      · intro a' ha' hne
        refine Finset.sum_eq_zero fun b' _ => ?_
        rw [if_neg]
        rintro ⟨f, _⟩
        exact hne (translatePlaquette_injective hn (hR a' ha') (hR a ha) z (f.trans e1.symm))
      · intro h'
        exact absurd ha h'
    rw [hv]
    refine (hκ a ha b hb).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hD)
    have t1 : (_root_.YangMills.Construction.TorusFields.supDist p.1 z : ℝ) ≤ _root_.YangMills.Construction.TorusFields.supDist a.1 (0 : TorusSite (4 * m)) := by
      rw [← e1]
      exact_mod_cast _root_.YangMills.Construction.ResponseInTheExpansion.MirrorKernels.supDist_translatePlaquette_le z a
    have t2 : (_root_.YangMills.Construction.TorusFields.supDist p'.1 z : ℝ) ≤ _root_.YangMills.Construction.TorusFields.supDist b.1 (0 : TorusSite (4 * m)) := by
      rw [← e2]
      exact_mod_cast _root_.YangMills.Construction.ResponseInTheExpansion.MirrorKernels.supDist_translatePlaquette_le z b
    have := max_le_max t1 t2
    have := mul_le_mul_of_nonneg_left this hd
    linarith
  · have hv : translatedKernel S z κ p p' = 0 := by
      refine Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb => ?_
      rw [if_neg]
      rintro ⟨e1, e2⟩
      exact h ⟨a, ha, b, hb, e1, e2⟩
    rw [hv, abs_zero]
    positivity
theorem sum_translatedKernel_orientation (S : Finset (TorusPlaquette (4 * m))) (z : TorusSite n)
    (κ : TorusPlaquette (4 * m) → TorusPlaquette (4 * m) → ℝ)
    (hS : ∀ a ∈ S, a.2.1 < a.2.2) (P P' : Fin 4 × Fin 4) :
    ∑ p ∈ (plaquettesIn (Finset.univ : Finset (TorusSite n))).filter (fun p : TorusPlaquette n => p.2 = P),
        ∑ p' ∈ (plaquettesIn (Finset.univ : Finset (TorusSite n))).filter (fun p' : TorusPlaquette n => p'.2 = P'),
          translatedKernel S z κ p p' =
      ∑ a ∈ S.filter (fun a : TorusPlaquette (4 * m) => a.2 = P),
        ∑ b ∈ S.filter (fun b : TorusPlaquette (4 * m) => b.2 = P'), κ a b := by
  have h := sum_translatedKernel_mul S z κ (fun p p' => if p.2 = P ∧ p'.2 = P' then 1 else 0) hS
  have e1 : ∑ p ∈ (plaquettesIn (Finset.univ : Finset (TorusSite n))).filter (fun p : TorusPlaquette n => p.2 = P),
        ∑ p' ∈ (plaquettesIn (Finset.univ : Finset (TorusSite n))).filter (fun p' : TorusPlaquette n => p'.2 = P'),
          translatedKernel S z κ p p' =
      ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), ∑ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
        translatedKernel S z κ p p' * (if p.2 = P ∧ p'.2 = P' then 1 else 0) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_filter]
    by_cases hp : p.2 = P
    · simp [hp]
    · simp [hp]
  have e2 : ∑ a ∈ S.filter (fun a : TorusPlaquette (4 * m) => a.2 = P),
        ∑ b ∈ S.filter (fun b : TorusPlaquette (4 * m) => b.2 = P'), κ a b =
      ∑ a ∈ S, ∑ b ∈ S,
        κ a b * (if (translatePlaquette z a).2 = P ∧ (translatePlaquette z b).2 = P' then 1 else 0) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_filter]
    by_cases ha : a.2 = P
    · simp [ha, translatePlaquette]
    · simp [ha, translatePlaquette]
  rw [e1, e2]
  exact h
theorem sum_abs_kernel_le_sq (S : Finset (TorusPlaquette (4 * m)))
    (κ : TorusPlaquette (4 * m) → TorusPlaquette (4 * m) → ℝ) {D d : ℝ} (hd : 0 < d)
    (hD : 0 ≤ D)
    (hκ : ∀ a ∈ S, ∀ b ∈ S, |κ a b| ≤
      D * Real.exp (-(d * max (_root_.YangMills.Construction.TorusFields.supDist a.1 (0 : TorusSite (4 * m)) : ℝ) (_root_.YangMills.Construction.TorusFields.supDist b.1 (0 : TorusSite (4 * m)) : ℝ)))) :
    ∑ a ∈ S, ∑ b ∈ S, |κ a b| ≤ D * (16 * expLatticeSum (d / 2)) ^ 2 := by
  set e : TorusPlaquette (4 * m) → ℝ :=
    fun a => Real.exp (-(d / 2) * (_root_.YangMills.Construction.TorusFields.supDist a.1 (0 : TorusSite (4 * m)) : ℝ)) with he
  have he0 : ∀ a, 0 ≤ e a := fun a => (Real.exp_pos _).le
  have h1 : ∀ a ∈ S, ∀ b ∈ S, |κ a b| ≤ D * (e a * e b) := by
    intro a ha b hb
    refine (hκ a ha b hb).trans (mul_le_mul_of_nonneg_left ?_ hD)
    rw [he]
    simp only
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := le_max_left (_root_.YangMills.Construction.TorusFields.supDist a.1 (0 : TorusSite (4 * m)) : ℝ) (_root_.YangMills.Construction.TorusFields.supDist b.1 (0 : TorusSite (4 * m)) : ℝ)
    have := le_max_right (_root_.YangMills.Construction.TorusFields.supDist a.1 (0 : TorusSite (4 * m)) : ℝ) (_root_.YangMills.Construction.TorusFields.supDist b.1 (0 : TorusSite (4 * m)) : ℝ)
    nlinarith
  have h2 : ∑ a ∈ S, e a ≤ 16 * expLatticeSum (d / 2) := by
    calc ∑ a ∈ S, e a ≤ ∑ a : TorusPlaquette (4 * m), e a :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun a _ _ => he0 a
      _ = ∑ y : TorusSite (4 * m), ∑ _q : Fin 4 × Fin 4,
            Real.exp (-(d / 2) * (_root_.YangMills.Construction.TorusFields.supDist y (0 : TorusSite (4 * m)) : ℝ)) :=
          Fintype.sum_prod_type _
      _ = 16 * ∑ y : TorusSite (4 * m), Real.exp (-(d / 2) * (_root_.YangMills.Construction.TorusFields.supDist y (0 : TorusSite (4 * m)) : ℝ)) := by
          simp [Finset.mul_sum]
      _ ≤ 16 * expLatticeSum (d / 2) := by
          have := sum_torus_exp_le (n := 4 * m) (c := d / 2) (by positivity) 0
          linarith
  have h3 : 0 ≤ ∑ a ∈ S, e a := Finset.sum_nonneg fun a _ => he0 a
  calc ∑ a ∈ S, ∑ b ∈ S, |κ a b| ≤ ∑ a ∈ S, ∑ b ∈ S, D * (e a * e b) :=
        Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => h1 a ha b hb
    _ = D * ((∑ a ∈ S, e a) * ∑ b ∈ S, e b) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by rw [Finset.mul_sum]
    _ ≤ D * (16 * expLatticeSum (d / 2)) ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ hD
        rw [sq]
        exact mul_le_mul h2 h2 h3 (h3.trans h2)
def mirrorGauge (z : TorusSite n) (g : TorusSite n → UnitQuaternion) (x : TorusSite (4 * m)) : UnitQuaternion :=
  g (z + siteOfInt (offset 0 x))
theorem supDist_add_unitStep_le (x : TorusSite (4 * m)) (i : Fin 4) :
    _root_.YangMills.Construction.TorusFields.supDist (x + unitStep (4 * m) i) 0 ≤ _root_.YangMills.Construction.TorusFields.supDist x 0 + 1 := by
  have h1 := _root_.YangMills.Construction.TorusFields.supDist_triangle (x + unitStep (4 * m) i) x 0
  have h2 : _root_.YangMills.Construction.TorusFields.supDist (x + unitStep (4 * m) i) x ≤ 1 := by
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm, unitStep_eq_siteOfInt]
    refine _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le x _ 1 fun j => ?_
    by_cases h : j = i
    · subst h
      simp
    · simp [h]
  omega
theorem offset_add_unitStep {x : TorusSite (4 * m)} (i : Fin 4) (hx : _root_.YangMills.Construction.TorusFields.supDist x 0 + 1 ≤ m) :
    offset 0 (x + unitStep (4 * m) i) = offset 0 x + Pi.single i 1 := by
  have e1 : (siteOfInt (offset 0 (x + unitStep (4 * m) i)) : TorusSite (4 * m)) =
      siteOfInt (offset 0 x + Pi.single i 1) := by
    have a1 := add_siteOfInt_offset (0 : TorusSite (4 * m)) (x + unitStep (4 * m) i)
    have a2 := add_siteOfInt_offset (0 : TorusSite (4 * m)) x
    rw [zero_add] at a1 a2
    rw [a1, siteOfInt_add, a2, ← unitStep_eq_siteOfInt]
  refine siteOfInt_injective_of_abs_sub_lt (fun j => ?_) e1
  have a1 := abs_offset_le (0 : TorusSite (4 * m)) (x + unitStep (4 * m) i) j
  have a2 := abs_offset_le (0 : TorusSite (4 * m)) x j
  have a3 : (_root_.YangMills.Construction.TorusFields.supDist (x + unitStep (4 * m) i) 0 : ℤ) ≤ m := by
    exact_mod_cast (_root_.YangMills.Construction.ResponseInTheExpansion.MirrorKernels.supDist_add_unitStep_le x i).trans hx
  have a5 : |(Pi.single i 1 : Fin 4 → ℤ) j| ≤ 1 := by
    by_cases h : j = i
    · subst h
      simp
    · simp [h]
  have a6 : |offset 0 (x + unitStep (4 * m) i) j - (offset (0 : TorusSite (4 * m)) x + Pi.single i 1 : Fin 4 → ℤ) j| ≤
      |offset 0 (x + unitStep (4 * m) i) j| + (|offset 0 x j| + |(Pi.single i 1 : Fin 4 → ℤ) j|) :=
    (abs_sub _ _).trans (add_le_add le_rfl (abs_add_le _ _))
  push_cast
  linarith
theorem gaugeTransform_mirrorField (z : TorusSite n) (W : TorusField n) (g : TorusSite n → UnitQuaternion)
    (hm : 2 ≤ m) {x : TorusSite (4 * m)} (i : Fin 4) (hx : _root_.YangMills.Construction.TorusFields.supDist x 0 + 1 ≤ m) :
    ResponseInTheExpansion.gaugeTransform (mirrorGauge z g) (mirrorField m z W) (x, i) =
      ResponseInTheExpansion.gaugeTransform g W (z + siteOfInt (offset 0 x), i) := by
  set b := offset 0 x with hb
  have hxb : x = siteOfInt b := by
    have := add_siteOfInt_offset (0 : TorusSite (4 * m)) x
    rwa [zero_add, eq_comm] at this
  have hn := offset_add_unitStep i hx
  have hbox1 : TorusFields.OffsetInBox m b := fun j => by
    have a1 := abs_offset_le (0 : TorusSite (4 * m)) x j
    have a2 : (_root_.YangMills.Construction.TorusFields.supDist x 0 : ℤ) + 1 ≤ m := by exact_mod_cast hx
    rw [hb]
    linarith
  have hbox2 : TorusFields.OffsetInBox m (b + Pi.single i 1) := fun j => by
    rw [← hn]
    have a1 := abs_offset_le (0 : TorusSite (4 * m)) (x + unitStep (4 * m) i) j
    have a2 : (_root_.YangMills.Construction.TorusFields.supDist (x + unitStep (4 * m) i) 0 : ℤ) ≤ m := by
      exact_mod_cast (_root_.YangMills.Construction.ResponseInTheExpansion.MirrorKernels.supDist_add_unitStep_le x i).trans hx
    linarith
  have hW := mirrorField_siteOfInt hm z W (b, i) ⟨hbox1, hbox2⟩
  simp only at hW
  unfold ResponseInTheExpansion.gaugeTransform mirrorGauge
  simp only
  rw [hn, ← hb, ← hxb] at *
  rw [hW, add_siteOfInt_add, ← unitStep_eq_siteOfInt]
theorem supDist_le_of_mem_supBall {x : TorusSite (4 * m)} {ρ : ℝ} (hx : x ∈ supBall (0 : TorusSite (4 * m)) ρ) :
    (_root_.YangMills.Construction.TorusFields.supDist x (0 : TorusSite (4 * m)) : ℝ) ≤ ρ := (Finset.mem_filter.mp hx).2
theorem supDist_add_one_le_of_mem_supBall {x : TorusSite (4 * m)} {ρ : ℝ}
    (hx : x ∈ supBall (0 : TorusSite (4 * m)) ρ) (hρ : ρ + 1 ≤ m) :
    _root_.YangMills.Construction.TorusFields.supDist x 0 + 1 ≤ m := by
  have h := _root_.YangMills.Construction.ResponseInTheExpansion.MirrorKernels.supDist_le_of_mem_supBall hx
  have : ((_root_.YangMills.Construction.TorusFields.supDist x 0 + 1 : ℕ) : ℝ) ≤ m := by
    push_cast
    linarith
  exact_mod_cast this
theorem ballLog_mirrorField (z : TorusSite n) (W : TorusField n) (g : TorusSite n → UnitQuaternion) (o : TorusSite n)
    {r ρ : ℝ} (hm : 2 ≤ m)
    (hρ : ρ + 1 ≤ m) (hb : ∀ y : TorusSite n, (_root_.YangMills.Construction.TorusFields.supDist y z : ℝ) ≤ ρ → y ∈ supBall o r) {x : TorusSite (4 * m)}
    (hx : x ∈ supBall (0 : TorusSite (4 * m)) ρ) (i : Fin 4) :
    ballLog (mirrorGauge z g) (mirrorField m z W) 0 ρ (x, i) = ballLog g W o r (z + siteOfInt (offset 0 x), i) := by
  have h1 : z + siteOfInt (offset 0 x) ∈ supBall o r := by
    apply hb
    have : supDist (z + siteOfInt (offset 0 x)) z ≤ supDist x (0 : TorusSite (4 * m)) :=
      supDist_translatePlaquette_le z (x, 0, 0)
    exact le_trans (by exact_mod_cast this) (supDist_le_of_mem_supBall hx)
  unfold ballLog
  simp only
  rw [if_pos hx, if_pos h1, gaugeTransform_mirrorField z W g hm i (_root_.YangMills.Construction.ResponseInTheExpansion.MirrorKernels.supDist_add_one_le_of_mem_supBall hx hρ)]
theorem lieFormCurl_mirrorField (z : TorusSite n) (W : TorusField n) (g : TorusSite n → UnitQuaternion)
    (o : TorusSite n) {r ρ : ℝ} (hm : 2 ≤ m)
    (hρ : ρ + 1 ≤ m) (hb : ∀ y : TorusSite n, (_root_.YangMills.Construction.TorusFields.supDist y z : ℝ) ≤ ρ → y ∈ supBall o r) {a : TorusPlaquette (4 * m)}
    (ha : a ∈ plaquettesIn (supBall (0 : TorusSite (4 * m)) ρ)) :
    lieFormCurl (ballLog (mirrorGauge z g) (mirrorField m z W) 0 ρ) a =
      lieFormCurl (ballLog g W o r) (translatePlaquette z a) := by
  have hc := (Finset.mem_filter.mp ha).2.2
  have c0 : a.1 ∈ supBall (0 : TorusSite (4 * m)) ρ := hc _ (by simp [plaquetteVertices])
  have c1 : a.1 + unitStep (4 * m) a.2.1 ∈ supBall (0 : TorusSite (4 * m)) ρ := hc _ (by simp [plaquetteVertices])
  have c2 : a.1 + unitStep (4 * m) a.2.2 ∈ supBall (0 : TorusSite (4 * m)) ρ := hc _ (by simp [plaquetteVertices])
  have hn : ∀ i, z + siteOfInt (offset 0 (a.1 + unitStep (4 * m) i)) =
      z + siteOfInt (offset 0 a.1) + unitStep n i := fun i => by
    rw [offset_add_unitStep i (_root_.YangMills.Construction.ResponseInTheExpansion.MirrorKernels.supDist_add_one_le_of_mem_supBall c0 hρ), add_siteOfInt_add, ← unitStep_eq_siteOfInt]
  unfold lieFormCurl translatePlaquette
  simp only
  rw [ballLog_mirrorField z W g o hm hρ hb c0, ballLog_mirrorField z W g o hm hρ hb c1,
    ballLog_mirrorField z W g o hm hρ hb c2, ballLog_mirrorField z W g o hm hρ hb c0, hn, hn]
theorem isNearIdentity_mirrorField (z : TorusSite n) (W : TorusField n) (g : TorusSite n → UnitQuaternion)
    (o : TorusSite n) {r ρ s : ℝ} (hm : 2 ≤ m)
    (hρ : ρ + 1 ≤ m) (hb : ∀ y : TorusSite n, (_root_.YangMills.Construction.TorusFields.supDist y z : ℝ) ≤ ρ → y ∈ supBall o r) (hs0 : 0 ≤ s)
    (hs : ∀ b : TorusBond n, b.1 ∈ supBall o r →
      ‖(minimalLog (ResponseInTheExpansion.gaugeTransform g W b) : ℍ[ℝ])‖ ≤ s) :
    IsNearIdentity (mirrorGauge z g) (mirrorField m z W) 0 ρ (4 * s) := by
  have hlog : ∀ x ∈ supBall (0 : TorusSite (4 * m)) ρ, ∀ i,
      ‖(minimalLog (ResponseInTheExpansion.gaugeTransform (mirrorGauge z g) (mirrorField m z W) (x, i)) : ℍ[ℝ])‖ ≤ s := by
    intro x hx i
    rw [gaugeTransform_mirrorField z W g hm i (_root_.YangMills.Construction.ResponseInTheExpansion.MirrorKernels.supDist_add_one_le_of_mem_supBall hx hρ)]
    refine hs _ (hb _ ?_)
    have : supDist (z + siteOfInt (offset 0 x)) z ≤ supDist x (0 : TorusSite (4 * m)) :=
      supDist_translatePlaquette_le z (x, 0, 0)
    exact le_trans (by exact_mod_cast this) (supDist_le_of_mem_supBall hx)
  have hclose : ∀ x ∈ supBall (0 : TorusSite (4 * m)) ρ, ∀ i,
      ‖((TorusFields.gaugeTransform (mirrorGauge z g) (mirrorField m z W) x i : UnitQuaternion) : ℍ[ℝ]) -
        ((trivialField (4 * m) x i : UnitQuaternion) : ℍ[ℝ])‖ ≤ s := by
    intro x hx i
    have e : TorusFields.gaugeTransform (mirrorGauge z g) (mirrorField m z W) x i =
        expUnit (minimalLog (ResponseInTheExpansion.gaugeTransform (mirrorGauge z g) (mirrorField m z W) (x, i))) := by
      rw [TopLevelSites.expUnit_minimalLog]
      rfl
    rw [e]
    have := norm_expUnit_sub_one_le
      (minimalLog (ResponseInTheExpansion.gaugeTransform (mirrorGauge z g) (mirrorField m z W) (x, i)))
    simp only [trivialField, OneMemClass.coe_one] at *
    exact this.trans (hlog x hx i)
  refine ⟨?_, ?_⟩
  · rintro ⟨x, i⟩ hx
    exact (hlog x hx i).trans (by linarith)
  · intro p hp
    have hc := (Finset.mem_filter.mp hp).2.2
    have c0 : p.1 ∈ supBall (0 : TorusSite (4 * m)) ρ := hc _ (by simp [plaquetteVertices])
    have c1 : p.1 + unitStep (4 * m) p.2.1 ∈ supBall (0 : TorusSite (4 * m)) ρ := hc _ (by simp [plaquetteVertices])
    have c2 : p.1 + unitStep (4 * m) p.2.2 ∈ supBall (0 : TorusSite (4 * m)) ρ := hc _ (by simp [plaquetteVertices])
    have h := TopLevelSites.curvature_le_add (TorusFields.gaugeTransform (mirrorGauge z g) (mirrorField m z W))
      (trivialField (4 * m)) p.1 p.2.1 p.2.2
    rw [_root_.YangMills.Construction.TorusFields.curvature_gaugeTransform] at h
    have h0 : curvature (trivialField (4 * m)) p.1 p.2.1 p.2.2 = 0 := by
      simp [curvature, holonomy, trivialField]
    have a1 := hclose _ c0 p.2.1
    have a2 := hclose _ c1 p.2.2
    have a3 := hclose _ c2 p.2.1
    have a4 := hclose _ c0 p.2.2
    linarith
end Translation
end MirrorKernels
end ResponseInTheExpansion
end YangMills.Construction
end
