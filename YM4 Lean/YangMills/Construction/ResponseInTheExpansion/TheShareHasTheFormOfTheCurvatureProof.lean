import YangMills.Construction.ClusterExpansionOfAStep.AnglesAlongOneDirection
import YangMills.Construction.ClusterExpansionOfAStep.CountsOnATorus
import YangMills.Construction.ClusterExpansionOfAStep.MovesOfAField
import YangMills.Construction.ColdChainAtEveryLevel.SecondOrderOfTheShareAtAFlatTop
import YangMills.Construction.ResponseInTheExpansion.TheCurvatureIsTheDescendedFormProof
import YangMills.Construction.ResponseInTheExpansion.TheShareHasTheFormOfTheCurvature
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages hiding unitStep
open LumpContours
namespace ResponseInTheExpansion
open TorusFields TorusLumps TorusFrame FieldMoves StepCosts ShareFamilies RenormalizationStepParameters TorusCounting BlockTrees
open Classical
private theorem contDiffAt_deriv_of_succ {φ : ℝ → ℝ} {v : ℝ} {k : ℕ}
    (h : ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) φ v) : ContDiffAt ℝ (k : WithTop ℕ∞) (deriv φ) v := by
  have h1 : ContDiffAt ℝ (k : WithTop ℕ∞) (fderiv ℝ φ) v := h.fderiv_right (by norm_cast)
  have h2 : deriv φ = fun x => fderiv ℝ φ x 1 := by
    funext x
    simp
  rw [h2]
  exact h1.clm_apply contDiffAt_const
private theorem abs_le_of_deriv_bound {f f' : ℝ → ℝ} {C a : ℝ} (ha : 0 ≤ a)
    (hf : ∀ t ∈ Set.Icc (-a) a, HasDerivAt f (f' t) t)
    (hb : ∀ t ∈ Set.Icc (-a) a, |f' t| ≤ C) (h0 : f 0 = 0) :
    ∀ t ∈ Set.Icc (-a) a, |f t| ≤ C * a := by
  intro t ht
  have hz : (0 : ℝ) ∈ Set.Icc (-a) a := ⟨by linarith, ha⟩
  have hC : 0 ≤ C := (abs_nonneg _).trans (hb 0 hz)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := f) (f' := f') (C := C)
    (s := Set.Icc (-a) a) (x := 0) (y := t) (fun x hx => (hf x hx).hasDerivWithinAt)
    (fun x hx => by simpa using hb x hx) (convex_Icc _ _) hz ht
  simp only [h0, sub_zero, Real.norm_eq_abs] at h
  exact h.trans (mul_le_mul_of_nonneg_left (abs_le.mpr ⟨ht.1, ht.2⟩) hC)
private theorem second_difference {g : ℝ → ℝ} {τ M : ℝ} (hτ : 0 ≤ τ)
    (hg : ∀ t ∈ Set.Icc (-τ) τ, ContDiffAt ℝ 3 g t)
    (hM : ∀ t ∈ Set.Icc (-τ) τ, |iteratedDeriv 3 g t| ≤ M) :
    |g τ + g (-τ) - 2 * g 0 - τ ^ 2 * iteratedDeriv 2 g 0| ≤ 2 * (M * τ * τ * τ) := by
  have e2 : iteratedDeriv 2 g = deriv (deriv g) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have e3 : iteratedDeriv 3 g = deriv (deriv (deriv g)) := by
    rw [iteratedDeriv_succ, e2]
  have c1 : ∀ t ∈ Set.Icc (-τ) τ, ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (deriv g) t := fun t ht =>
    contDiffAt_deriv_of_succ (k := 2) (by exact_mod_cast hg t ht)
  have c2 : ∀ t ∈ Set.Icc (-τ) τ, ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) (deriv (deriv g)) t := fun t ht =>
    contDiffAt_deriv_of_succ (k := 1) (by exact_mod_cast c1 t ht)
  have d3 : ∀ t ∈ Set.Icc (-τ) τ, HasDerivAt (deriv (deriv g)) (deriv (deriv (deriv g)) t) t := fun t ht =>
    ((c2 t ht).differentiableAt (by norm_num)).hasDerivAt
  have d2 : ∀ t ∈ Set.Icc (-τ) τ, HasDerivAt (deriv g) (deriv (deriv g) t) t := fun t ht =>
    ((c1 t ht).differentiableAt (by norm_num)).hasDerivAt
  have d1 : ∀ t ∈ Set.Icc (-τ) τ, HasDerivAt g (deriv g t) t := fun t ht =>
    ((hg t ht).differentiableAt (by norm_num)).hasDerivAt
  have v2 := abs_le_of_deriv_bound (f := fun t => deriv (deriv g) t - deriv (deriv g) 0)
    (f' := deriv (deriv (deriv g))) (C := M) hτ (fun t ht => (d3 t ht).sub_const _)
    (fun t ht => by rw [← e3]; exact hM t ht) (by simp)
  have v1 := abs_le_of_deriv_bound (f := fun t => deriv g t - deriv g 0 - deriv (deriv g) 0 * t)
    (f' := fun t => deriv (deriv g) t - deriv (deriv g) 0) (C := M * τ) hτ
    (fun t ht => by
      have h := ((d2 t ht).sub_const (deriv g 0)).sub ((hasDerivAt_id t).const_mul (deriv (deriv g) 0))
      exact h.congr_deriv (by simp)) v2 (by simp)
  have v0 := abs_le_of_deriv_bound (f := fun t => g t - g 0 - deriv g 0 * t - deriv (deriv g) 0 * (t ^ 2 / 2))
    (f' := fun t => deriv g t - deriv g 0 - deriv (deriv g) 0 * t) (C := M * τ * τ) hτ
    (fun t ht => by
      have h2 : HasDerivAt (fun t : ℝ => t ^ 2 / 2) t t := by
        have := ((hasDerivAt_id t).pow 2).div_const 2
        simpa using this
      have h := (((d1 t ht).sub_const (g 0)).sub ((hasDerivAt_id t).const_mul (deriv g 0))).sub
        (h2.const_mul (deriv (deriv g) 0))
      exact h.congr_deriv (by simp)) v1 (by simp)
  have a := v0 τ ⟨by linarith, le_rfl⟩
  have b := v0 (-τ) ⟨le_rfl, by linarith⟩
  have e : g τ + g (-τ) - 2 * g 0 - τ ^ 2 * iteratedDeriv 2 g 0 =
      (g τ - g 0 - deriv g 0 * τ - deriv (deriv g) 0 * (τ ^ 2 / 2)) +
        (g (-τ) - g 0 - deriv g 0 * (-τ) - deriv (deriv g) 0 * ((-τ) ^ 2 / 2)) := by
    rw [e2]
    ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  linarith
section Field
variable {n : ℕ}
private def quatI : ℍ[ℝ] := ⟨0, 1, 0, 0⟩
private theorem quatI_re : quatI.re = 0 := rfl
private theorem quatI_imI : quatI.imI = 1 := rfl
private theorem quatI_imJ : quatI.imJ = 0 := rfl
private theorem quatI_imK : quatI.imK = 0 := rfl
private def unitI : imaginaryQuaternions := ⟨quatI, rfl⟩
private theorem norm_unitI : ‖unitI‖ = 1 := by
  show ‖quatI‖ = 1
  have h : ‖quatI‖ * ‖quatI‖ = 1 := by
    rw [← Quaternion.normSq_eq_norm_mul_self]
    rw [Quaternion.normSq_def', quatI_re, quatI_imI, quatI_imJ, quatI_imK]
    norm_num
  have h0 := norm_nonneg quatI
  rcases mul_self_eq_one_iff.mp h with h1 | h1
  · exact h1
  · linarith
private theorem norm_smul_unitI (c : ℝ) : ‖(((c • unitI : imaginaryQuaternions)) : ℍ[ℝ])‖ = |c| := by
  have h : ‖c • unitI‖ = |c| := by rw [norm_smul, norm_unitI, mul_one, Real.norm_eq_abs]
  simpa using h
private theorem sum_imaginaryComponent_smul_unitI (a b : ℝ) :
    ∑ e : Fin 3, imaginaryComponent e (a • unitI) * imaginaryComponent e (b • unitI) = a * b := by
  have hc : ∀ c : ℝ, (((c • unitI : imaginaryQuaternions)) : ℍ[ℝ]) = c • quatI := fun c => rfl
  simp [Fin.sum_univ_three, imaginaryComponent, hc, quatI_imI, quatI_imJ, quatI_imK]
private def centredCoords (x : TorusSite n) : Fin 4 → ℤ := fun i => (x i).valMinAbs
private def InRadius (r : ℕ) (x : TorusSite n) : Prop := OffsetInBox r (centredCoords x)
private theorem centredCoords_add_unitStep [NeZero n] {r : ℕ} (hn : 2 * r + 2 < n) {x : TorusSite n}
    (hx : InRadius r x) (μ : Fin 4) :
    centredCoords (x + unitStep n μ) = centredCoords x + Pi.single μ 1 := by
  funext i
  by_cases h : i = μ
  · subst h
    have hb := abs_le.mp (hx i)
    have h1 : (x i + 1).valMinAbs = (x i).valMinAbs + 1 := by
      rw [ZMod.valMinAbs_spec]
      constructor
      · simp
      · have h2 : centredCoords x i = (x i).valMinAbs := rfl
        rw [h2] at hb
        constructor <;> omega
    simpa [centredCoords, unitStep] using h1
  · simp [centredCoords, unitStep, Pi.single_eq_of_ne h]
private def linearAngle (r : ℕ) (f : Fin 4 → Fin 4 → ℝ) (x : TorusSite n) (μ : Fin 4) : ℝ :=
  if BondOffsetInBox r (centredCoords x, μ) then (1 / 2) * ∑ ν, ((centredCoords x ν : ℤ) : ℝ) * f ν μ else 0
private theorem abs_linearAngle_le {r : ℕ} {f : Fin 4 → Fin 4 → ℝ} (hf : ∀ μ ν, |f μ ν| ≤ 2)
    (x : TorusSite n) (μ : Fin 4) :
    |linearAngle r f x μ| ≤ 4 * r := by
  unfold linearAngle
  split_ifs with h
  · have hc : ∀ ν, |((centredCoords x ν : ℤ) : ℝ)| ≤ r := fun ν => by
      have h1 : |centredCoords x ν| ≤ (r : ℤ) := h.1 ν
      exact_mod_cast h1
    calc |(1 / 2) * ∑ ν, ((centredCoords x ν : ℤ) : ℝ) * f ν μ|
        = (1 / 2) * |∑ ν, ((centredCoords x ν : ℤ) : ℝ) * f ν μ| := by rw [abs_mul]; norm_num
      _ ≤ (1 / 2) * ∑ ν : Fin 4, (r : ℝ) * 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ν _ => ?_)
        rw [abs_mul]
        exact mul_le_mul (hc ν) (hf ν μ) (abs_nonneg _) (Nat.cast_nonneg r)
      _ = 4 * r := by simp; ring
  · simp
private theorem angleCurl_linearAngle [NeZero n] {r : ℕ} {f : Fin 4 → Fin 4 → ℝ} (hn : 2 * r + 2 < n)
    (hanti : ∀ μ ν, f μ ν = - f ν μ) {x : TorusSite n} {μ ν : Fin 4}
    (h0 : InRadius r x) (h1 : InRadius r (x + unitStep n μ)) (h2 : InRadius r (x + unitStep n ν))
    (h3 : InRadius r (x + unitStep n μ + unitStep n ν)) :
    linearAngle r f x μ + linearAngle r f (x + unitStep n μ) ν - linearAngle r f (x + unitStep n ν) μ -
      linearAngle r f x ν = f μ ν := by
  have c1 := centredCoords_add_unitStep hn h0 μ
  have c2 := centredCoords_add_unitStep hn h0 ν
  have c4 := centredCoords_add_unitStep hn h2 μ
  have h3' : InRadius r (x + unitStep n ν + unitStep n μ) := by
    rw [add_right_comm]
    exact h3
  have b1 : BondOffsetInBox r (centredCoords x, μ) := ⟨h0, by
    have := h1
    unfold InRadius at this
    rw [c1] at this
    exact this⟩
  have b2 : BondOffsetInBox r (centredCoords (x + unitStep n μ), ν) := ⟨h1, by
    have := h3
    unfold InRadius at this
    rw [centredCoords_add_unitStep hn h1 ν] at this
    exact this⟩
  have b3 : BondOffsetInBox r (centredCoords (x + unitStep n ν), μ) := ⟨h2, by
    have := h3'
    unfold InRadius at this
    rw [c4] at this
    exact this⟩
  have b4 : BondOffsetInBox r (centredCoords x, ν) := ⟨h0, by
    have := h2
    unfold InRadius at this
    rw [c2] at this
    exact this⟩
  have shift : ∀ α β : Fin 4, ∑ a, ((((centredCoords x + Pi.single α 1 : Fin 4 → ℤ) a : ℤ)) : ℝ) * f a β =
      ∑ a, ((centredCoords x a : ℤ) : ℝ) * f a β + f α β := by
    intro α β
    have e : ∀ a, ((((centredCoords x + Pi.single α 1 : Fin 4 → ℤ) a : ℤ)) : ℝ) * f a β =
        ((centredCoords x a : ℤ) : ℝ) * f a β + (if a = α then f a β else 0) := by
      intro a
      by_cases h : a = α
      · subst h
        simp [add_mul]
      · simp [h]
    simp only [e, Finset.sum_add_distrib]
    simp
  unfold linearAngle
  rw [if_pos b1, if_pos b2, if_pos b3, if_pos b4, c1, c2, shift, shift]
  rw [hanti ν μ]
  ring
private def constantCurvatureField (r : ℕ) (f : Fin 4 → Fin 4 → ℝ) (z : TorusSite n) (τ : ℝ) : TorusField n :=
  fun x μ => expUnit ((τ * linearAngle r f (x - z) μ) • unitI)
private theorem translate_constantCurvatureField (r : ℕ) (f : Fin 4 → Fin 4 → ℝ) (z : TorusSite n) (τ : ℝ) :
    TorusFields.translate z (constantCurvatureField r f z τ) = constantCurvatureField r f 0 τ := by
  funext x μ
  simp [TorusFields.translate, constantCurvatureField]
private theorem holonomy_constantCurvatureField (r : ℕ) (f : Fin 4 → Fin 4 → ℝ) (z : TorusSite n) (τ : ℝ)
    (x : TorusSite n) (μ ν : Fin 4) :
    holonomy (constantCurvatureField r f z τ) x μ ν =
      expUnit (angleCurl (fun x μ => τ * linearAngle r f (x - z) μ) x μ ν • unitI) :=
  holonomy_eq_expUnit_angleCurl unitI _ _ (fun _ _ => rfl) x μ ν
private theorem abs_angleCurl_le {r : ℕ} {f : Fin 4 → Fin 4 → ℝ} (hf : ∀ μ ν, |f μ ν| ≤ 2) (z : TorusSite n)
    (τ : ℝ) (x : TorusSite n) (μ ν : Fin 4) :
    |angleCurl (fun x μ => τ * linearAngle r f (x - z) μ) x μ ν| ≤ 16 * r * |τ| := by
  have hb : ∀ (y : TorusSite n) (i : Fin 4), |τ * linearAngle r f (y - z) i| ≤ 4 * r * |τ| := fun y i => by
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (abs_linearAngle_le hf _ _) (abs_nonneg _)
  have h1 := hb x μ
  have h2 := hb (x + unitStep n μ) ν
  have h3 := hb (x + unitStep n ν) μ
  have h4 := hb x ν
  unfold angleCurl
  rw [abs_le] at *
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]
private theorem curvature_constantCurvatureField_le {r : ℕ} {f : Fin 4 → Fin 4 → ℝ} (hf : ∀ μ ν, |f μ ν| ≤ 2)
    (z : TorusSite n) (τ : ℝ) (x : TorusSite n) (μ ν : Fin 4) :
    curvature (constantCurvatureField r f z τ) x μ ν ≤ 16 * r * |τ| := by
  unfold curvature
  rw [holonomy_constantCurvatureField]
  refine (norm_expUnit_sub_one_le _).trans ?_
  rw [norm_smul_unitI]
  exact abs_angleCurl_le hf z τ x μ ν
private theorem minimalLog_constantCurvatureField {r : ℕ} {f : Fin 4 → Fin 4 → ℝ} (hf : ∀ μ ν, |f μ ν| ≤ 2)
    (z : TorusSite n) {τ : ℝ} (hπ : 4 * r * |τ| < Real.pi) (x : TorusSite n) (μ : Fin 4) :
    minimalLog (constantCurvatureField r f z τ x μ) = (τ * linearAngle r f (x - z) μ) • unitI := by
  apply minimalLog_expUnit
  rw [norm_smul_unitI, abs_mul, mul_comm]
  exact (mul_le_mul_of_nonneg_right (abs_linearAngle_le hf _ _) (abs_nonneg _)).trans_lt hπ
private theorem gaugeTransform_one (V : TorusField n) (b : TorusBond n) :
    gaugeTransform (fun _ => 1) V b = V b.1 b.2 := by
  simp [gaugeTransform]
private theorem inRadius_of_mem [NeZero n] {z c : TorusSite n} {ρ₀ : ℝ} (hc : c ∈ supBall z ρ₀) :
    InRadius ⌊ρ₀⌋₊ (c - z) := by
  have h : (_root_.YangMills.Construction.TorusFields.supDist c z : ℝ) ≤ ρ₀ := (Finset.mem_filter.mp hc).2
  have h2 : _root_.YangMills.Construction.TorusFields.supDist c z ≤ ⌊ρ₀⌋₊ := Nat.le_floor h
  intro i
  have h3 := (_root_.YangMills.Construction.TorusFields.supDist_le_iff c z _).mp h2 i
  show |((c - z) i).valMinAbs| ≤ ((⌊ρ₀⌋₊ : ℕ) : ℤ)
  rw [Pi.sub_apply, Int.abs_eq_natAbs]
  exact_mod_cast h3
private theorem lieFormCurl_constantCurvatureField [NeZero n] {f : Fin 4 → Fin 4 → ℝ} {ρ₀ : ℝ}
    {z : TorusSite n} {τ : ℝ}
    (hf : ∀ μ ν, |f μ ν| ≤ 2) (hanti : ∀ μ ν, f μ ν = - f ν μ) (hn : 2 * ⌊ρ₀⌋₊ + 2 < n)
    (hπ : 4 * (⌊ρ₀⌋₊ : ℝ) * |τ| < Real.pi) {p : TorusPlaquette n} (hp : p ∈ plaquettesIn (supBall z ρ₀)) :
    lieFormCurl (ballLog (fun _ => 1) (constantCurvatureField ⌊ρ₀⌋₊ f z τ) z ρ₀) p =
      (τ * f p.2.1 p.2.2) • unitI := by
  obtain ⟨x, μ, ν⟩ := p
  have hc := (Finset.mem_filter.mp hp).2.2
  have m0 : x ∈ supBall z ρ₀ := hc x (by simp [plaquetteVertices])
  have m1 : x + unitStep n μ ∈ supBall z ρ₀ := hc _ (by simp [plaquetteVertices])
  have m2 : x + unitStep n ν ∈ supBall z ρ₀ := hc _ (by simp [plaquetteVertices])
  have m3 : x + unitStep n μ + unitStep n ν ∈ supBall z ρ₀ := hc _ (by simp [plaquetteVertices])
  have e1 : x + unitStep n μ - z = x - z + unitStep n μ := by abel
  have e2 : x + unitStep n ν - z = x - z + unitStep n ν := by abel
  have e3 : x + unitStep n μ + unitStep n ν - z = x - z + unitStep n μ + unitStep n ν := by abel
  have i0 := inRadius_of_mem m0
  have i1 := inRadius_of_mem m1
  have i2 := inRadius_of_mem m2
  have i3 := inRadius_of_mem m3
  rw [e1] at i1
  rw [e2] at i2
  rw [e3] at i3
  have hk := angleCurl_linearAngle hn hanti i0 i1 i2 i3
  have hb : ∀ b : TorusBond n, b.1 ∈ supBall z ρ₀ →
      ballLog (fun _ => 1) (constantCurvatureField ⌊ρ₀⌋₊ f z τ) z ρ₀ b =
        (τ * linearAngle ⌊ρ₀⌋₊ f (b.1 - z) b.2) • unitI := by
    intro b hb
    unfold ballLog
    rw [if_pos hb, gaugeTransform_one, minimalLog_constantCurvatureField hf z hπ]
  unfold lieFormCurl
  simp only
  rw [hb (x, μ) m0, hb (x + unitStep n μ, ν) m1, hb (x + unitStep n ν, μ) m2, hb (x, ν) m0]
  simp only [e1, e2]
  rw [← add_smul, ← sub_smul, ← sub_smul, ← hk]
  congr 1
  ring
private def boxForm (κ : TorusPlaquette n → TorusPlaquette n → ℝ) [NeZero n] (z : TorusSite n) (ρ₀ : ℝ)
    (u v : TorusPlaquette n → ℝ) : ℝ :=
  ∑ p ∈ plaquettesIn (supBall z ρ₀), ∑ p' ∈ plaquettesIn (supBall z ρ₀), κ p p' * (u p * v p')
private def planeValue (f : Fin 4 → Fin 4 → ℝ) (p : TorusPlaquette n) : ℝ := f p.2.1 p.2.2
private theorem kernelQuadraticForm_constantCurvatureField [NeZero n] {f : Fin 4 → Fin 4 → ℝ} {ρ₀ : ℝ}
    {z : TorusSite n} {τ : ℝ}
    (κ : TorusPlaquette n → TorusPlaquette n → ℝ) (hf : ∀ μ ν, |f μ ν| ≤ 2) (hanti : ∀ μ ν, f μ ν = - f ν μ)
    (hn : 2 * ⌊ρ₀⌋₊ + 2 < n) (hπ : 4 * (⌊ρ₀⌋₊ : ℝ) * |τ| < Real.pi) :
    kernelQuadraticForm κ z ρ₀ (lieFormCurl (ballLog (fun _ => 1) (constantCurvatureField ⌊ρ₀⌋₊ f z τ) z ρ₀)) =
      τ ^ 2 / 2 * boxForm κ z ρ₀ (planeValue f) (planeValue f) := by
  unfold kernelQuadraticForm boxForm
  have e : ∀ p ∈ plaquettesIn (supBall z ρ₀), ∀ p' ∈ plaquettesIn (supBall z ρ₀),
      κ p p' * ∑ e : Fin 3,
        imaginaryComponent e (lieFormCurl (ballLog (fun _ => 1) (constantCurvatureField ⌊ρ₀⌋₊ f z τ) z ρ₀) p) *
        imaginaryComponent e (lieFormCurl (ballLog (fun _ => 1) (constantCurvatureField ⌊ρ₀⌋₊ f z τ) z ρ₀) p') =
      τ ^ 2 * (κ p p' * (planeValue f p * planeValue f p')) := by
    intro p hp p' hp'
    rw [lieFormCurl_constantCurvatureField hf hanti hn hπ hp, lieFormCurl_constantCurvatureField hf hanti hn hπ hp',
      sum_imaginaryComponent_smul_unitI]
    simp only [planeValue]
    ring
  rw [Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun p' hp' => e p hp p' hp']
  simp only [← Finset.mul_sum]
  ring
private theorem isNearIdentity_constantCurvatureField [NeZero n] {f : Fin 4 → Fin 4 → ℝ} {ρ₀ : ℝ}
    {z : TorusSite n} {τ : ℝ}
    (hf : ∀ μ ν, |f μ ν| ≤ 2) (hπ : 4 * (⌊ρ₀⌋₊ : ℝ) * |τ| < Real.pi) :
    IsNearIdentity (fun _ => 1) (constantCurvatureField ⌊ρ₀⌋₊ f z τ) z ρ₀ (16 * (⌊ρ₀⌋₊ : ℝ) * |τ|) where
  log_le := by
    intro b _
    rw [gaugeTransform_one, minimalLog_constantCurvatureField hf z hπ, norm_smul_unitI, abs_mul, mul_comm]
    have h := mul_le_mul_of_nonneg_right (abs_linearAngle_le (r := ⌊ρ₀⌋₊) hf (b.1 - z) b.2) (abs_nonneg τ)
    have h2 : 0 ≤ (⌊ρ₀⌋₊ : ℝ) * |τ| := by positivity
    linarith
  curvature_le := fun p _ => curvature_constantCurvatureField_le hf z τ _ _ _
private theorem expansion_at_constantCurvatureField [NeZero n] {σ C c ρ₀ : ℝ} {G : TorusField n → ℝ}
    {z : TorusSite n} {κ : TorusPlaquette n → TorusPlaquette n → ℝ}
    {f : Fin 4 → Fin 4 → ℝ} {τ : ℝ} (hE : IsQuadraticInCurvature σ C c 1 ρ₀ G z κ)
    (hf : ∀ μ ν, |f μ ν| ≤ 2) (hanti : ∀ μ ν, f μ ν = - f ν μ) (hn : 2 * ⌊ρ₀⌋₊ + 2 < n) (hσ : 0 < σ)
    (hs : 5 * (16 * (⌊ρ₀⌋₊ : ℝ) * |τ|) ≤ σ) (hπ : 4 * (⌊ρ₀⌋₊ : ℝ) * |τ| < Real.pi) :
    |G (constantCurvatureField ⌊ρ₀⌋₊ f z τ) - τ ^ 2 / 2 * boxForm κ z ρ₀ (planeValue f) (planeValue f)| ≤
      |C| * ((16 * (⌊ρ₀⌋₊ : ℝ) * |τ|) ^ 3 + Real.exp (-(c * ρ₀))) := by
  have hs0 : 0 ≤ 16 * (⌊ρ₀⌋₊ : ℝ) * |τ| := by positivity
  have hcold : IsCold σ (constantCurvatureField ⌊ρ₀⌋₊ f z τ) := fun x μ ν _ => by
    have := curvature_constantCurvatureField_le (r := ⌊ρ₀⌋₊) hf z τ x μ ν
    linarith
  have h := hE (fun _ => 1) _ _ hs0 hs hcold (isNearIdentity_constantCurvatureField hf hπ)
  rw [kernelQuadraticForm_constantCurvatureField κ hf hanti hn hπ] at h
  refine h.trans ?_
  have hp : 0 ≤ (16 * (⌊ρ₀⌋₊ : ℝ) * |τ|) ^ 3 + Real.exp (-(c * ρ₀)) := by positivity
  rw [mul_one]
  exact mul_le_mul_of_nonneg_right (le_abs_self C) hp
private theorem boxForm_near_of_second_difference [NeZero n] {σ C c ρ₀ : ℝ} {G : TorusField n → ℝ}
    {z : TorusSite n} {κ : TorusPlaquette n → TorusPlaquette n → ℝ}
    {f : Fin 4 → Fin 4 → ℝ} {τ q E : ℝ} (hE : IsQuadraticInCurvature σ C c 1 ρ₀ G z κ)
    (hf : ∀ μ ν, |f μ ν| ≤ 2) (hanti : ∀ μ ν, f μ ν = - f ν μ) (hn : 2 * ⌊ρ₀⌋₊ + 2 < n) (hσ : 0 < σ)
    (hτ : 0 < τ) (hs : 5 * (16 * (⌊ρ₀⌋₊ : ℝ) * τ) ≤ σ) (hπ : 4 * (⌊ρ₀⌋₊ : ℝ) * τ < Real.pi)
    (hsec : |G (constantCurvatureField ⌊ρ₀⌋₊ f z τ) + G (constantCurvatureField ⌊ρ₀⌋₊ f z (-τ)) -
      2 * G (constantCurvatureField ⌊ρ₀⌋₊ f z 0) - τ ^ 2 * q| ≤ τ ^ 2 * E) :
    |boxForm κ z ρ₀ (planeValue f) (planeValue f) - q| ≤
      E + |C| * (2 * (16 * (⌊ρ₀⌋₊ : ℝ) * τ) ^ 3 + 4 * Real.exp (-(c * ρ₀))) / τ ^ 2 := by
  have ha : |τ| = τ := abs_of_pos hτ
  have ha' : |-τ| = τ := by rw [abs_neg, ha]
  have h1 := expansion_at_constantCurvatureField (τ := τ) hE hf hanti hn hσ (by rwa [ha]) (by rwa [ha])
  have h2 := expansion_at_constantCurvatureField (τ := -τ) hE hf hanti hn hσ (by rwa [ha']) (by rwa [ha'])
  have h3 := expansion_at_constantCurvatureField (τ := 0) hE hf hanti hn hσ (by simpa using hσ.le)
    (by simpa using Real.pi_pos)
  rw [ha] at h1
  rw [ha'] at h2
  simp only [abs_zero, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, zero_mul,
    sub_zero, zero_add] at h3
  set Q := boxForm κ z ρ₀ (planeValue f) (planeValue f)
  set s3 := (16 * (⌊ρ₀⌋₊ : ℝ) * τ) ^ 3
  set ee := Real.exp (-(c * ρ₀))
  have hτ2 : 0 < τ ^ 2 := by positivity
  rw [neg_sq] at h2
  have key : τ ^ 2 * |Q - q| ≤ τ ^ 2 * E + |C| * (2 * s3 + 4 * ee) := by
    rw [← abs_of_pos hτ2, ← abs_mul, abs_of_pos hτ2]
    rw [abs_le] at *
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, hsec.1, hsec.2]
  rw [← sub_le_iff_le_add', le_div_iff₀ hτ2]
  nlinarith
end Field
section Planes
variable {n : ℕ} [NeZero n]
private def squareSum (f : Fin 4 → Fin 4 → ℝ) : ℝ := ∑ a, ∑ b ∈ Finset.univ.filter (a < ·), f a b ^ 2
private def unitPlaneCurvature (P : Fin 4 × Fin 4) : Fin 4 → Fin 4 → ℝ :=
  fun a b => (if (a, b) = P then 1 else 0) - (if (b, a) = P then 1 else 0)
private theorem unitPlaneCurvature_anti (P : Fin 4 × Fin 4) (a b : Fin 4) :
    unitPlaneCurvature P a b = - unitPlaneCurvature P b a := by
  unfold unitPlaneCurvature
  ring
private theorem abs_unitPlaneCurvature_le (P : Fin 4 × Fin 4) (a b : Fin 4) : |unitPlaneCurvature P a b| ≤ 1 := by
  unfold unitPlaneCurvature
  split_ifs <;> norm_num
private theorem unitPlaneCurvature_of_lt {P : Fin 4 × Fin 4} (hP : P.1 < P.2) {a b : Fin 4} (hab : a < b) :
    unitPlaneCurvature P a b = if (a, b) = P then 1 else 0 := by
  unfold unitPlaneCurvature
  have : ¬ (b, a) = P := by
    rintro rfl
    exact absurd hab (not_lt.mpr hP.le)
  simp [this]
private def planeIndicator (P : Fin 4 × Fin 4) (p : TorusPlaquette n) : ℝ := if p.2 = P then 1 else 0
private theorem sum_ordered_pairs_eq_one {P : Fin 4 × Fin 4} (hP : P.1 < P.2) :
    ∑ a, ∑ b ∈ Finset.univ.filter (a < ·), (if (a, b) = P then (1 : ℝ) else 0) = 1 := by
  rw [Finset.sum_eq_single P.1, Finset.sum_eq_single P.2]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (congrArg Prod.snd h)
  · intro h
    exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP⟩) h
  · intro a _ ha
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [if_neg]
    intro h
    exact ha (congrArg Prod.fst h)
  · simp
private theorem squareSum_unitPlaneCurvature {P : Fin 4 × Fin 4} (hP : P.1 < P.2) :
    squareSum (unitPlaneCurvature P) = 1 := by
  unfold squareSum
  rw [← sum_ordered_pairs_eq_one hP]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => ?_
  rw [unitPlaneCurvature_of_lt hP (Finset.mem_filter.mp hb).2]
  split_ifs <;> norm_num
private theorem squareSum_two_planes {P Q : Fin 4 × Fin 4} (hP : P.1 < P.2) (hQ : Q.1 < Q.2) (hPQ : P ≠ Q) :
    squareSum (fun a b => unitPlaneCurvature P a b + unitPlaneCurvature Q a b) = 2 := by
  unfold squareSum
  have h : (2 : ℝ) = (∑ a, ∑ b ∈ Finset.univ.filter (a < ·), (if (a, b) = P then (1 : ℝ) else 0)) +
      ∑ a, ∑ b ∈ Finset.univ.filter (a < ·), (if (a, b) = Q then (1 : ℝ) else 0) := by
    rw [sum_ordered_pairs_eq_one hP, sum_ordered_pairs_eq_one hQ]
    norm_num
  rw [h, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b hb => ?_
  have hab := (Finset.mem_filter.mp hb).2
  show (unitPlaneCurvature P a b + unitPlaneCurvature Q a b) ^ 2 = _
  rw [unitPlaneCurvature_of_lt hP hab, unitPlaneCurvature_of_lt hQ hab]
  by_cases h1 : (a, b) = P
  · have h2 : ¬ (a, b) = Q := fun h2 => hPQ (h1.symm.trans h2)
    rw [if_pos h1, if_neg h2]
    norm_num
  · by_cases h2 : (a, b) = Q
    · rw [if_neg h1, if_pos h2]
      norm_num
    · rw [if_neg h1, if_neg h2]
      norm_num
private theorem boxForm_congr (κ : TorusPlaquette n → TorusPlaquette n → ℝ) (z : TorusSite n) (ρ₀ : ℝ)
    {u u' v v' : TorusPlaquette n → ℝ}
    (hu : ∀ p ∈ plaquettesIn (supBall z ρ₀), u p = u' p) (hv : ∀ p ∈ plaquettesIn (supBall z ρ₀), v p = v' p) :
    boxForm κ z ρ₀ u v = boxForm κ z ρ₀ u' v' := by
  unfold boxForm
  refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun p' hp' => ?_
  rw [hu p hp, hv p' hp']
private theorem boxForm_add_left (κ : TorusPlaquette n → TorusPlaquette n → ℝ) (z : TorusSite n) (ρ₀ : ℝ)
    (u u' v : TorusPlaquette n → ℝ) :
    boxForm κ z ρ₀ (fun p => u p + u' p) v = boxForm κ z ρ₀ u v + boxForm κ z ρ₀ u' v := by
  simp only [boxForm, add_mul, mul_add, Finset.sum_add_distrib]
private theorem boxForm_add_right (κ : TorusPlaquette n → TorusPlaquette n → ℝ) (z : TorusSite n) (ρ₀ : ℝ)
    (u v v' : TorusPlaquette n → ℝ) :
    boxForm κ z ρ₀ u (fun p => v p + v' p) = boxForm κ z ρ₀ u v + boxForm κ z ρ₀ u v' := by
  simp only [boxForm, mul_add, Finset.sum_add_distrib]
private theorem boxForm_comm {κ : TorusPlaquette n → TorusPlaquette n → ℝ} (hs : ∀ p p', κ p p' = κ p' p)
    (z : TorusSite n) (ρ₀ : ℝ) (u v : TorusPlaquette n → ℝ) : boxForm κ z ρ₀ u v = boxForm κ z ρ₀ v u := by
  unfold boxForm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun p' _ => ?_
  rw [hs, mul_comm (u p')]
private theorem planeValue_unitPlaneCurvature {P : Fin 4 × Fin 4} (hP : P.1 < P.2) {z : TorusSite n} {ρ₀ : ℝ} :
    ∀ p ∈ plaquettesIn (supBall z ρ₀), planeValue (unitPlaneCurvature P) p = planeIndicator P p := by
  intro p hp
  have h := (Finset.mem_filter.mp hp).2.1
  simp only [planeValue, planeIndicator]
  rw [unitPlaneCurvature_of_lt hP h]
private theorem plane_sums_of_form {κ : TorusPlaquette n → TorusPlaquette n → ℝ} (hs : ∀ p p', κ p p' = κ p' p)
    {z : TorusSite n} {ρ₀ U : ℝ}
    (hU : ∀ f : Fin 4 → Fin 4 → ℝ, (∀ μ ν, |f μ ν| ≤ 2) → (∀ μ ν, f μ ν = - f ν μ) →
      |boxForm κ z ρ₀ (planeValue f) (planeValue f) - squareSum f| ≤ U)
    {P Q : Fin 4 × Fin 4} (hP : P.1 < P.2) (hQ : Q.1 < Q.2) :
    |boxForm κ z ρ₀ (planeIndicator P) (planeIndicator Q) - (if P = Q then 1 else 0)| ≤ 2 * U := by
  have one : ∀ {R : Fin 4 × Fin 4}, R.1 < R.2 →
      |boxForm κ z ρ₀ (planeIndicator R) (planeIndicator R) - 1| ≤ U := by
    intro R hR
    have h := hU (unitPlaneCurvature R) (fun μ ν => (abs_unitPlaneCurvature_le R μ ν).trans (by norm_num))
      (unitPlaneCurvature_anti R)
    rw [squareSum_unitPlaneCurvature hR,
      boxForm_congr κ z ρ₀ (planeValue_unitPlaneCurvature hR) (planeValue_unitPlaneCurvature hR)] at h
    exact h
  have hU0 : 0 ≤ U := (abs_nonneg _).trans (one hP)
  by_cases hPQ : P = Q
  · subst hPQ
    rw [if_pos rfl]
    have := one hP
    linarith
  · rw [if_neg hPQ, sub_zero]
    have h := hU (fun a b => unitPlaneCurvature P a b + unitPlaneCurvature Q a b)
      (fun μ ν => (abs_add_le _ _).trans (by
        linarith [abs_unitPlaneCurvature_le P μ ν, abs_unitPlaneCurvature_le Q μ ν]))
      (fun μ ν => by rw [unitPlaneCurvature_anti P μ ν, unitPlaneCurvature_anti Q μ ν]; ring)
    have e : ∀ p ∈ plaquettesIn (supBall z ρ₀),
        planeValue (fun a b => unitPlaneCurvature P a b + unitPlaneCurvature Q a b) p =
          planeIndicator P p + planeIndicator Q p := fun p hp => by
      have h1 := planeValue_unitPlaneCurvature hP p hp
      have h2 := planeValue_unitPlaneCurvature hQ p hp
      simp only [planeValue] at h1 h2 ⊢
      rw [h1, h2]
    rw [squareSum_two_planes hP hQ hPQ, boxForm_congr κ z ρ₀ e e, boxForm_add_left, boxForm_add_right,
      boxForm_add_right, boxForm_comm hs z ρ₀ (planeIndicator Q) (planeIndicator P)] at h
    have h1 := abs_le.mp (one hP)
    have h2 := abs_le.mp (one hQ)
    have h3 := abs_le.mp h
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
private theorem supDist_vertex_le {x c : TorusSite n} {μ ν : Fin 4} (hc : c ∈ plaquetteVertices x μ ν) :
    _root_.YangMills.Construction.TorusFields.supDist c x ≤ 2 := by apply _root_.YangMills.SharedProofs.p38261 <;> assumption
private theorem mem_plaquettesIn_supBall_of_near {p : TorusPlaquette n} {z : TorusSite n} {ρ₀ : ℝ}
    (hp : p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)))
    (h : (_root_.YangMills.Construction.TorusFields.supDist p.1 z : ℝ) ≤ ρ₀ - 2) : p ∈ plaquettesIn (supBall z ρ₀) := by
  obtain ⟨hu, hlt, _⟩ := Finset.mem_filter.mp hp
  refine Finset.mem_filter.mpr ⟨hu, hlt, fun c hc => Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  have h1 := supDist_vertex_le hc
  have h2 := _root_.YangMills.Construction.TorusFields.supDist_triangle c p.1 z
  have h3 : (_root_.YangMills.Construction.TorusFields.supDist c z : ℝ) ≤ (_root_.YangMills.Construction.TorusFields.supDist c p.1 : ℝ) + _root_.YangMills.Construction.TorusFields.supDist p.1 z := by exact_mod_cast h2
  have h4 : (_root_.YangMills.Construction.TorusFields.supDist c p.1 : ℝ) ≤ 2 := by exact_mod_cast h1
  linarith
private theorem card_plane_plaquettes_near_le (P : Fin 4 × Fin 4) (z : TorusSite n) (ρ₀ : ℝ) :
    (((plaquettesIn (Finset.univ : Finset (TorusSite n))).filter fun p : TorusPlaquette n => p.2 = P).filter
      fun p => (_root_.YangMills.Construction.TorusFields.supDist p.1 z : ℝ) ≤ ρ₀).card ≤ (2 * ⌊ρ₀⌋₊ + 1) ^ 4 := by
  refine le_trans ?_ (card_thickening_singleton_le ⌊ρ₀⌋₊ z)
  refine Finset.card_le_card_of_injOn (fun p => p.1) ?_ ?_
  · intro p hp
    have h := (Finset.mem_filter.mp hp).2
    exact (mem_thickening _ _ _).2 ⟨z, by simp, Nat.le_floor h⟩
  · intro p hp p' hp' e
    have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
    have h2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hp').1).2
    exact Prod.ext e (h1.trans h2.symm)
private theorem plane_sums_off_box {κ : TorusPlaquette n → TorusPlaquette n → ℝ} {z : TorusSite n} {ρ₀ D d : ℝ}
    (hd : 0 < d)
    (hsupp : ∀ p p', ρ₀ < (_root_.YangMills.Construction.TorusFields.supDist p.1 z : ℝ) ∨ ρ₀ < (_root_.YangMills.Construction.TorusFields.supDist p'.1 z : ℝ) → κ p p' = 0)
    (hdec : ∀ p p', |κ p p'| ≤ D * Real.exp (-(d * max (_root_.YangMills.Construction.TorusFields.supDist p.1 z : ℝ) (_root_.YangMills.Construction.TorusFields.supDist p'.1 z : ℝ))))
    (P Q : Fin 4 × Fin 4) :
    |(∑ p ∈ (plaquettesIn Finset.univ).filter (fun p : TorusPlaquette n => p.2 = P),
        ∑ p' ∈ (plaquettesIn Finset.univ).filter (fun p' : TorusPlaquette n => p'.2 = Q), κ p p') -
      boxForm κ z ρ₀ (planeIndicator P) (planeIndicator Q)| ≤
      ((2 * ⌊ρ₀⌋₊ + 1 : ℕ) : ℝ) ^ 8 * (|D| * Real.exp (-(d * (ρ₀ - 2)))) := by
  set A := (plaquettesIn (Finset.univ : Finset (TorusSite n))).filter (fun p : TorusPlaquette n => p.2 = P) with hA
  set B := (plaquettesIn (Finset.univ : Finset (TorusSite n))).filter (fun p : TorusPlaquette n => p.2 = Q) with hB
  set A' := (plaquettesIn (supBall z ρ₀)).filter (fun p : TorusPlaquette n => p.2 = P) with hA'
  set B' := (plaquettesIn (supBall z ρ₀)).filter (fun p : TorusPlaquette n => p.2 = Q) with hB'
  have sub : ∀ (R : Fin 4 × Fin 4),
      (plaquettesIn (supBall z ρ₀)).filter (fun p : TorusPlaquette n => p.2 = R) ⊆
        (plaquettesIn (Finset.univ : Finset (TorusSite n))).filter (fun p : TorusPlaquette n => p.2 = R) := by
    intro R p hp
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hp
    obtain ⟨_, h3, _⟩ := Finset.mem_filter.mp h1
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h3, fun _ _ => Finset.mem_univ _⟩, h2⟩
  have hsub : A' ×ˢ B' ⊆ A ×ˢ B := Finset.product_subset_product (sub P) (sub Q)
  have e1 : (∑ p ∈ A, ∑ p' ∈ B, κ p p') = ∑ x ∈ A ×ˢ B, κ x.1 x.2 := (Finset.sum_product' _ _ _).symm
  have e2 : boxForm κ z ρ₀ (planeIndicator P) (planeIndicator Q) = ∑ x ∈ A' ×ˢ B', κ x.1 x.2 := by
    rw [Finset.sum_product', hA', hB', Finset.sum_filter]
    unfold boxForm
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h : p.2 = P
    · rw [if_pos h, Finset.sum_filter]
      refine Finset.sum_congr rfl fun p' _ => ?_
      by_cases h' : p'.2 = Q <;> simp [planeIndicator, h, h']
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun p' _ => ?_
      simp [planeIndicator, h]
  rw [e1, e2, ← Finset.sum_sdiff hsub, add_sub_cancel_right]
  set A₀ := A.filter fun p => (_root_.YangMills.Construction.TorusFields.supDist p.1 z : ℝ) ≤ ρ₀ with hA₀
  set B₀ := B.filter fun p => (_root_.YangMills.Construction.TorusFields.supDist p.1 z : ℝ) ≤ ρ₀ with hB₀
  set b := |D| * Real.exp (-(d * (ρ₀ - 2))) with hb
  have hb0 : 0 ≤ b := by positivity
  have hz : ∀ x ∈ (A ×ˢ B) \ (A' ×ˢ B'), κ x.1 x.2 ≠ 0 → x ∈ A₀ ×ˢ B₀ ∧ |κ x.1 x.2| ≤ b := by
    rintro ⟨p, p'⟩ hx hne
    obtain ⟨hab, hnot⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨hpA, hpB⟩ := Finset.mem_product.mp hab
    simp only at hpA hpB hne
    have h1 : (_root_.YangMills.Construction.TorusFields.supDist p.1 z : ℝ) ≤ ρ₀ := not_lt.mp fun h => hne (hsupp _ _ (Or.inl h))
    have h2 : (_root_.YangMills.Construction.TorusFields.supDist p'.1 z : ℝ) ≤ ρ₀ := not_lt.mp fun h => hne (hsupp _ _ (Or.inr h))
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hpA, h1⟩, Finset.mem_filter.mpr ⟨hpB, h2⟩⟩, ?_⟩
    have hfar : ρ₀ - 2 ≤ max (_root_.YangMills.Construction.TorusFields.supDist p.1 z : ℝ) (_root_.YangMills.Construction.TorusFields.supDist p'.1 z : ℝ) := by
      by_contra hc
      rw [not_le] at hc
      have c1 := (max_lt_iff.mp hc).1
      have c2 := (max_lt_iff.mp hc).2
      apply hnot
      refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨?_, (Finset.mem_filter.mp hpA).2⟩,
        Finset.mem_filter.mpr ⟨?_, (Finset.mem_filter.mp hpB).2⟩⟩
      · exact mem_plaquettesIn_supBall_of_near (Finset.mem_filter.mp hpA).1 c1.le
      · exact mem_plaquettesIn_supBall_of_near (Finset.mem_filter.mp hpB).1 c2.le
    refine (hdec p p').trans ?_
    have h3 : Real.exp (-(d * max (_root_.YangMills.Construction.TorusFields.supDist p.1 z : ℝ) (_root_.YangMills.Construction.TorusFields.supDist p'.1 z : ℝ))) ≤ Real.exp (-(d * (ρ₀ - 2))) := by
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left hfar hd.le
      linarith
    calc D * Real.exp (-(d * max (_root_.YangMills.Construction.TorusFields.supDist p.1 z : ℝ) (_root_.YangMills.Construction.TorusFields.supDist p'.1 z : ℝ)))
        ≤ |D| * Real.exp (-(d * max (_root_.YangMills.Construction.TorusFields.supDist p.1 z : ℝ) (_root_.YangMills.Construction.TorusFields.supDist p'.1 z : ℝ))) :=
          mul_le_mul_of_nonneg_right (le_abs_self D) (Real.exp_nonneg _)
      _ ≤ b := mul_le_mul_of_nonneg_left h3 (abs_nonneg D)
  have hsum : |∑ x ∈ (A ×ˢ B) \ (A' ×ˢ B'), κ x.1 x.2| ≤ ((A₀ ×ˢ B₀).card : ℝ) * b := by
    rw [← Finset.sum_filter_of_ne (s := (A ×ˢ B) \ (A' ×ˢ B')) (f := fun x => κ x.1 x.2)
      (p := fun x => x ∈ A₀ ×ˢ B₀) (fun x hx hne => (hz x hx hne).1)]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hle : ∀ x ∈ ((A ×ˢ B) \ (A' ×ˢ B')).filter (fun x => x ∈ A₀ ×ˢ B₀), |κ x.1 x.2| ≤ b := by
      intro x hx
      obtain ⟨h1, _⟩ := Finset.mem_filter.mp hx
      by_cases h0 : κ x.1 x.2 = 0
      · rw [h0, abs_zero]
        exact hb0
      · exact (hz x h1 h0).2
    refine (Finset.sum_le_card_nsmul _ _ _ hle).trans ?_
    rw [nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ hb0
    exact_mod_cast Finset.card_le_card fun x hx => (Finset.mem_filter.mp hx).2
  refine hsum.trans (mul_le_mul_of_nonneg_right ?_ hb0)
  have c1 : A₀.card ≤ (2 * ⌊ρ₀⌋₊ + 1) ^ 4 := card_plane_plaquettes_near_le P z ρ₀
  have c2 : B₀.card ≤ (2 * ⌊ρ₀⌋₊ + 1) ^ 4 := card_plane_plaquettes_near_le Q z ρ₀
  rw [Finset.card_product]
  have c3 : A₀.card * B₀.card ≤ (2 * ⌊ρ₀⌋₊ + 1) ^ 8 := by
    calc A₀.card * B₀.card ≤ (2 * ⌊ρ₀⌋₊ + 1) ^ 4 * (2 * ⌊ρ₀⌋₊ + 1) ^ 4 := Nat.mul_le_mul c1 c2
      _ = (2 * ⌊ρ₀⌋₊ + 1) ^ 8 := by ring
  exact_mod_cast c3
end Planes
section Family
variable {n : ℕ} [NeZero n]
private def bondEnum : Fin (Fintype.card (TorusBond n)) → TorusBond n := (Fintype.equivFin (TorusBond n)).symm
private theorem bondShift_bondEnum (σ : Fin (Fintype.card (TorusBond n)) → ℝ) (β : TorusBond n) :
    bondShift (bondEnum (n := n)) (fun _ => unitI) σ β = σ (Fintype.equivFin (TorusBond n) β) • unitI := by
  unfold bondShift
  rw [Finset.sum_eq_single (Fintype.equivFin (TorusBond n) β)]
  · simp [bondEnum]
  · intro l _ hl
    rw [if_neg]
    intro h
    apply hl
    rw [← h]
    simp [bondEnum]
  · simp
private def bondAngles (r : ℕ) (f : Fin 4 → Fin 4 → ℝ) : Fin (Fintype.card (TorusBond n)) → ℝ :=
  fun l => linearAngle r f (bondEnum l).1 (bondEnum l).2
private theorem perturb_constantCurvatureField (r : ℕ) (f : Fin 4 → Fin 4 → ℝ) (t h : ℝ) :
    perturb (bondEnum (n := n)) (fun _ => unitI) (h • bondAngles r f) (constantCurvatureField r f 0 t) =
      constantCurvatureField r f 0 (t + h) := by
  funext x μ
  rw [perturb_apply, bondShift_bondEnum]
  have e : (h • bondAngles (n := n) r f) (Fintype.equivFin (TorusBond n) (x, μ)) = h * linearAngle r f x μ := by
    simp [bondAngles, bondEnum]
  rw [e]
  simp only [constantCurvatureField, sub_zero]
  rw [← TorusFields.expUnit_add_smul]
  congr 2
  ring
private theorem mixedDeriv_bondEnum {G : TorusField n → ℝ} {W : TorusField n}
    (hC : ContDiffAt ℝ 3 (fun s => G (perturb (bondEnum (n := n)) (fun _ => unitI) s W)) 0)
    (ι : Fin 3 → Fin (Fintype.card (TorusBond n))) :
    mixedDeriv G W (bondEnum ∘ ι) ((fun _ => unitI) ∘ ι) =
      iteratedFDeriv ℝ 3 (fun s => G (perturb (bondEnum (n := n)) (fun _ => unitI) s W)) 0
        (fun l => Pi.single (ι l) 1) := by
  unfold mixedDeriv
  have e : (fun σ : Fin 3 → ℝ => G (perturb (bondEnum ∘ ι) ((fun _ => unitI) ∘ ι) σ W)) =
      fun σ => (fun s => G (perturb (bondEnum (n := n)) (fun _ => unitI) s W)) (0 + pullParamsCLM ι σ) := by
    funext σ
    rw [perturb_comp, zero_add, pullParamsCLM_apply]
  rw [e, iteratedFDeriv_comp_affine_zero (pullParamsCLM ι) hC]
  simp only [pullParamsCLM_single]
private theorem third_derivative_along_field {G : TorusField n → ℝ} {σ A : ℝ} {r : ℕ} {f : Fin 4 → Fin 4 → ℝ}
    (hs : ∀ W, IsCold σ W → ContDiffThreeAt G W)
    (hd : ∀ W, IsCold σ W → ∀ (c : Fin 3 → TorusBond n) (X : Fin 3 → imaginaryQuaternions), AreUnitVectors X →
      |mixedDeriv G W c X| ≤ A)
    {t : ℝ} (ht : IsCold σ (constantCurvatureField (n := n) r f 0 t)) :
    ContDiffAt ℝ 3 (fun u => G (constantCurvatureField r f 0 u)) t ∧
      |iteratedDeriv 3 (fun u => G (constantCurvatureField r f 0 u)) t| ≤
        A * (∑ l, |bondAngles (n := n) r f l|) ^ 3 := by
  set Φ : (Fin (Fintype.card (TorusBond n)) → ℝ) → ℝ :=
    fun s => G (perturb (bondEnum (n := n)) (fun _ => unitI) s (constantCurvatureField r f 0 t)) with hΦ
  have hC : ContDiffAt ℝ 3 Φ 0 := hs _ ht _ _ _
  let Lθ : ℝ →L[ℝ] (Fin (Fintype.card (TorusBond n)) → ℝ) :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight (bondAngles r f)
  have hL : ∀ u, Lθ u = u • bondAngles r f := fun u => rfl
  have line : (fun u => G (constantCurvatureField r f 0 (t + u))) = fun u => Φ (0 + Lθ u) := by
    funext u
    simp only [zero_add, hΦ, hL, perturb_constantCurvatureField]
  constructor
  · have hm : ContDiffAt ℝ 3 (fun u : ℝ => 0 + Lθ (u - t)) t :=
      contDiffAt_const.add (Lθ.contDiff.contDiffAt.comp t (contDiffAt_id.sub contDiffAt_const))
    have hC' : ContDiffAt ℝ 3 Φ (0 + Lθ (t - t)) := by simpa using hC
    have h1 : ContDiffAt ℝ 3 (fun u => Φ (0 + Lθ (u - t))) t := ContDiffAt.comp (g := Φ) t hC' hm
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
    have h2 := congrFun line (u - t)
    show G (constantCurvatureField r f 0 u) = Φ (0 + Lθ (u - t))
    rw [← h2]
    simp
  · have hsh := congrFun (iteratedFDeriv_comp_const_add (fun u => G (constantCurvatureField r f 0 u)) t 3) 0
    simp only [add_zero] at hsh
    rw [iteratedDeriv_eq_iteratedFDeriv, ← hsh, line, iteratedFDeriv_comp_affine_zero Lθ hC]
    set D := iteratedFDeriv ℝ 3 Φ 0 with hD
    have hθ : Lθ 1 = ∑ l, bondAngles (n := n) r f l •
        (Pi.single l 1 : Fin (Fintype.card (TorusBond n)) → ℝ) := by
      rw [hL, one_smul]
      funext m
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hθ, D.map_sum (fun _ l => bondAngles (n := n) r f l •
      (Pi.single l 1 : Fin (Fintype.card (TorusBond n)) → ℝ))]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Fintype.sum_pow, Finset.mul_sum]
    refine Finset.sum_le_sum fun ι _ => ?_
    rw [D.map_smul_univ (fun i => bondAngles (n := n) r f (ι i)) (fun i => Pi.single (ι i) 1)]
    rw [smul_eq_mul, abs_mul, Finset.abs_prod, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun _ _ => abs_nonneg _)
    rw [hD, ← mixedDeriv_bondEnum hC ι]
    exact hd _ ht _ _ fun _ => norm_unitI
private theorem mem_thickening_of_linearAngle_ne_zero {r : ℕ} {f : Fin 4 → Fin 4 → ℝ} {x : TorusSite n}
    {μ : Fin 4} (h : linearAngle r f x μ ≠ 0) :
    x ∈ thickening r ({0} : Finset (TorusSite n)) := by
  unfold linearAngle at h
  have hb : BondOffsetInBox r (centredCoords x, μ) := by
    by_contra hc
    exact h (if_neg hc)
  refine (mem_thickening _ _ _).2 ⟨0, by simp, (_root_.YangMills.Construction.TorusFields.supDist_le_iff _ _ _).2 fun i => ?_⟩
  have h1 : |centredCoords x i| ≤ (r : ℤ) := hb.1 i
  rw [Int.abs_eq_natAbs] at h1
  have h2 : (x i - (0 : TorusSite n) i) = x i := by simp
  rw [h2]
  exact_mod_cast h1
private theorem sum_abs_bondAngles_le {r : ℕ} {f : Fin 4 → Fin 4 → ℝ} (hf : ∀ μ ν, |f μ ν| ≤ 2) :
    ∑ l, |bondAngles (n := n) r f l| ≤ (((2 * r + 1) ^ 4 : ℕ) : ℝ) * (16 * r) := by
  have e : ∑ l, |bondAngles (n := n) r f l| = ∑ b : TorusBond n, |linearAngle r f b.1 b.2| :=
    Equiv.sum_comp (Fintype.equivFin (TorusBond n)).symm (fun b : TorusBond n => |linearAngle r f b.1 b.2|)
  rw [e, Fintype.sum_prod_type]
  have h1 : ∀ x : TorusSite n, ∑ μ, |linearAngle r f x μ| ≤
      if x ∈ thickening r ({0} : Finset (TorusSite n)) then 16 * (r : ℝ) else 0 := by
    intro x
    split_ifs with hx
    · calc ∑ μ, |linearAngle r f x μ| ≤ ∑ _μ : Fin 4, 4 * (r : ℝ) :=
            Finset.sum_le_sum fun μ _ => abs_linearAngle_le hf x μ
        _ = 16 * r := by simp; ring
    · refine le_of_eq (Finset.sum_eq_zero fun μ _ => ?_)
      by_contra hc
      exact hx (mem_thickening_of_linearAngle_ne_zero fun h0 => hc (by rw [h0, abs_zero]))
  refine (Finset.sum_le_sum fun x _ => h1 x).trans ?_
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  exact_mod_cast card_thickening_singleton_le r (0 : TorusSite n)
end Family
section Link
variable {n : ℕ} [NeZero n]
private theorem centredCoords_siteOfCell {L t : ℕ} (y : (torusFrame L t n).Cell) :
    centredCoords (siteOfCell y) = BlockAverages.minimalCoords y := by
  funext k
  have h := valMinAbs_sub_castInt (period_torusFrame (L := L) (t := t) (m := n) k) (y k) 0
  simpa [centredCoords, siteOfCell, siteCoords, BlockAverages.minimalCoords] using h.symm
private theorem readAtLevel_constantCurvatureField {L t r : ℕ} (f : Fin 4 → Fin 4 → ℝ) (u : ℝ) :
    readAtLevel (torusFrame L t n) (torusFrame L t n).top (constantCurvatureField r f (0 : TorusSite n) u) =
      rotatedField (fun y μ => (u * (if BondWithinRadius r (BlockAverages.minimalCoords y, μ) then (1 : ℝ) else 0)) •
        constantCurvaturePotential (F := torusFrame L t n) (fun μ ν => f μ ν • unitI) y μ) flatTopField := by
  funext y μ
  rw [readAtLevel_torusFrame]
  simp only [constantCurvatureField, rotatedField, flatTopField, mul_one, sub_zero]
  congr 1
  unfold linearAngle constantCurvaturePotential
  rw [centredCoords_siteOfCell]
  by_cases hB : BondWithinRadius r (BlockAverages.minimalCoords y, μ)
  · have hB' : BondOffsetInBox r (BlockAverages.minimalCoords y, μ) := hB
    rw [if_pos hB, if_pos hB']
    have e : ∑ ν, ((BlockAverages.minimalCoords y ν : ℤ) : ℝ) • (f ν μ • unitI) =
        (∑ ν, ((BlockAverages.minimalCoords y ν : ℤ) : ℝ) * f ν μ) • unitI := by
      simp only [smul_smul, Finset.sum_smul]
    rw [e, smul_smul, smul_smul]
    congr 1
    ring
  · have hB' : ¬ BondOffsetInBox r (BlockAverages.minimalCoords y, μ) := hB
    rw [if_neg hB, if_neg hB']
    simp
private theorem curvatureNormSq_smul_unitI (f : Fin 4 → Fin 4 → ℝ) :
    curvatureNormSq (fun μ ν => f μ ν • unitI) = squareSum f := by
  unfold curvatureNormSq squareSum
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [norm_smul, norm_unitI, mul_one, Real.norm_eq_abs, sq_abs]
private theorem second_derivative_at_flat {a δ N0 : ℝ} {L t r : ℕ} {f : Fin 4 → Fin 4 → ℝ}
    (hh : HasFlatSecondVariation a δ N0 (cellsOfSites (torusFrame L t n) (Finset.univ : Finset (TorusSite n))))
    (hr : 1 ≤ r) (hn : 2 * r + 2 < n) (hanti : ∀ μ ν, f μ ν = - f ν μ) :
    |iteratedDeriv 2 (fun u => levelShare a L (t + 1) Finset.univ (0 : TorusSite n)
        (constantCurvatureField r f 0 u)) 0 - squareSum f| ≤
      N0 * squareSum f * (r : ℝ) ^ 4 * Real.exp (-δ * r) := by
  have key := hh r (fun μ ν => f μ ν • unitI)
    (fun y μ => if BondWithinRadius r (BlockAverages.minimalCoords y, μ) then (1 : ℝ) else 0) hr
    (fun _ _ => mem_cellsOfSites_torusFrame.mpr (Finset.mem_univ _)) (fun _ => Or.inr hn)
    (fun μ ν => by
      have h := neg_smul (f ν μ) unitI
      rw [hanti μ ν]
      exact h)
    (fun y i => by split_ifs <;> norm_num)
    (fun y μ h => if_pos ⟨fun i => (h.1 i).trans (by exact_mod_cast Nat.div_le_self r 2),
      fun i => (h.2 i).trans (by exact_mod_cast Nat.div_le_self r 2)⟩)
    (fun y μ h => if_neg h)
  rw [curvatureNormSq_smul_unitI] at key
  have hz : torusSiteInFrame (torusFrame L t n) (t + 1) (0 : TorusSite n) = 0 := by
    funext i
    simp [torusSiteInFrame, siteOfCoords]
  have e : (fun u => levelShare a L (t + 1) Finset.univ (0 : TorusSite n) (constantCurvatureField r f 0 u)) =
      fun u => minimalCellShare a (cellsOfSites (torusFrame L t n) (Finset.univ : Finset (TorusSite n))) 0
        (rotatedField (fun y μ =>
          (u * (if BondWithinRadius r (BlockAverages.minimalCoords y, μ) then (1 : ℝ) else 0)) •
          constantCurvaturePotential (F := torusFrame L t n) (fun μ ν => f μ ν • unitI) y μ) flatTopField) := by
    funext u
    rw [← readAtLevel_constantCurvatureField]
    show minimalCellShare a _ (torusSiteInFrame (torusFrame L t n) (t + 1) (0 : TorusSite n)) _ = _
    rw [hz]
    rfl
  rw [e]
  exact key
end Link
section Steps
variable {n : ℕ} [NeZero n]
private theorem levelShareFamily_eq (a : ℝ) (L t : ℕ) (y : TorusSite n) (V : TorusField n) :
    levelShareFamily a L t n y V = levelShare a L t Finset.univ y V := by
  simp [levelShareFamily, NeZero.ne n]
private theorem one_le_weight {ℓ : TorusLumps.StepParameters} (hr : 0 ≤ ℓ.weightRate) (m : ℕ) : 1 ≤ ℓ.weight m := by
  unfold TorusLumps.StepParameters.weight
  have h1 : (1 : ℝ) ≤ max 1 (((m : ℝ) / ℓ.n₁) ^ 16000) := le_max_left _ _
  have h2 : (1 : ℝ) ≤ Real.exp (ℓ.weightRate * m) := Real.one_le_exp (by positivity)
  nlinarith
private theorem second_difference_above {ℓ : TorusLumps.StepParameters} {a δ N0 C : ℝ} {L t r : ℕ}
    {f : Fin 4 → Fin 4 → ℝ} {z : TorusSite n}
    {τ : ℝ} (fam : IsCurvatureFamily ℓ C (levelShareFamily a L (t + 1))) (hrate : 0 ≤ ℓ.weightRate)
    (hn₀ : ℓ.n₀ ≤ n)
    (hh : HasFlatSecondVariation a δ N0 (cellsOfSites (torusFrame L t n) (Finset.univ : Finset (TorusSite n))))
    (hr : 1 ≤ r) (hn : 2 * r + 2 < n) (hf : ∀ μ ν, |f μ ν| ≤ 2) (hanti : ∀ μ ν, f μ ν = - f ν μ)
    (hτ : 0 ≤ τ) (hcold : 16 * (r : ℝ) * τ < ℓ.threshold) :
    |levelShare a L (t + 1) Finset.univ z (constantCurvatureField r f z τ) +
        levelShare a L (t + 1) Finset.univ z (constantCurvatureField r f z (-τ)) -
        2 * levelShare a L (t + 1) Finset.univ z (constantCurvatureField r f z 0) - τ ^ 2 * squareSum f| ≤
      τ ^ 2 * (2 * (|C| * (∑ l, |bondAngles (n := n) r f l|) ^ 3 * τ) +
        N0 * squareSum f * (r : ℝ) ^ 4 * Real.exp (-δ * r)) := by
  set G₀ : TorusField n → ℝ := levelShareFamily a L (t + 1) n 0 with hG₀
  have cold : ∀ (w : TorusSite n) (u : ℝ), |u| ≤ τ → IsCold ℓ.threshold (constantCurvatureField r f w u) := by
    intro w u hu x μ ν _
    refine (curvature_constantCurvatureField_le hf w u x μ ν).trans_lt (lt_of_le_of_lt ?_ hcold)
    exact mul_le_mul_of_nonneg_left hu (by positivity)
  have move : ∀ u : ℝ, |u| ≤ τ →
      levelShare a L (t + 1) Finset.univ z (constantCurvatureField r f z u) = G₀ (constantCurvatureField r f 0 u) := by
    intro u hu
    have h := fam.translation n hn₀ 0 z (constantCurvatureField r f z u) (cold z u hu)
    rw [translate_constantCurvatureField, zero_add, levelShareFamily_eq (y := z)] at h
    exact h.symm
  have hs : ∀ W, IsCold ℓ.threshold W → ContDiffThreeAt G₀ W := fun W hW => fam.smooth n hn₀ 0 W hW
  have hd : ∀ W, IsCold ℓ.threshold W → ∀ (c : Fin 3 → TorusBond n) (X : Fin 3 → imaginaryQuaternions),
      AreUnitVectors X → |mixedDeriv G₀ W c X| ≤ |C| := by
    intro W hW c X hX
    refine (fam.decay n hn₀ 0 W hW 3 c X (by norm_num) le_rfl hX).trans ?_
    have hw := one_le_weight hrate (supportDiam (0 : TorusSite n) c)
    calc C / ℓ.weight (supportDiam (0 : TorusSite n) c) ≤ |C| / ℓ.weight (supportDiam (0 : TorusSite n) c) :=
          div_le_div_of_nonneg_right (le_abs_self C) (by linarith)
      _ ≤ |C| := div_le_self (abs_nonneg C) hw
  have hsec := second_difference (g := fun u => G₀ (constantCurvatureField r f 0 u)) (τ := τ)
    (M := |C| * (∑ l, |bondAngles (n := n) r f l|) ^ 3) hτ
    (fun u hu => (third_derivative_along_field hs hd (cold 0 u (abs_le.mpr hu))).1)
    (fun u hu => (third_derivative_along_field hs hd (cold 0 u (abs_le.mpr hu))).2)
  have hlink := second_derivative_at_flat (r := r) (f := f) hh hr hn hanti
  have e2 : iteratedDeriv 2 (fun u => G₀ (constantCurvatureField r f 0 u)) 0 =
      iteratedDeriv 2 (fun u => levelShare a L (t + 1) Finset.univ (0 : TorusSite n)
        (constantCurvatureField r f 0 u)) 0 := by
    congr 1
    funext u
    exact levelShareFamily_eq a L (t + 1) 0 _
  rw [← e2] at hlink
  rw [move τ (by rw [abs_of_nonneg hτ]), move (-τ) (by rw [abs_neg, abs_of_nonneg hτ]),
    move 0 (by simpa using hτ)]
  set d2 := iteratedDeriv 2 (fun u => G₀ (constantCurvatureField r f 0 u)) 0
  set S := |C| * (∑ l, |bondAngles (n := n) r f l|) ^ 3
  set E := N0 * squareSum f * (r : ℝ) ^ 4 * Real.exp (-δ * r)
  have hτ2 : 0 ≤ τ ^ 2 := by positivity
  have h3 : τ ^ 2 * |d2 - squareSum f| ≤ τ ^ 2 * E := mul_le_mul_of_nonneg_left hlink hτ2
  rw [← abs_of_nonneg hτ2, ← abs_mul, abs_of_nonneg hτ2] at h3
  have h4 := abs_le.mp hsec
  have h5 := abs_le.mp h3
  rw [abs_le]
  constructor <;> nlinarith [h4.1, h4.2, h5.1, h5.2]
end Steps
section Bare
variable {n : ℕ} [NeZero n]
private theorem count_plaquetteVertices (x z : TorusSite n) (μ ν : Fin 4) :
    (((plaquetteVertices x μ ν).count z : ℕ) : ℝ) = (if x = z then 1 else 0) +
      (if x + unitStep n μ = z then 1 else 0) + (if x + unitStep n ν = z then 1 else 0) +
      (if x + unitStep n μ + unitStep n ν = z then 1 else 0) := by
  simp only [plaquetteVertices, List.count_cons, List.count_nil, beq_iff_eq]
  split_ifs <;> norm_num
private theorem sum_translate_indicator (c z : TorusSite n) :
    ∑ x : TorusSite n, (if x + c = z then (1 : ℝ) else 0) = 1 := by
  rw [Finset.sum_eq_single (z - c)]
  · simp
  · intro x _ hx
    rw [if_neg]
    intro h
    exact hx (eq_sub_of_add_eq h)
  · simp
private theorem sum_vertex_weights (z : TorusSite n) (μ ν : Fin 4) :
    ∑ x : TorusSite n, (((plaquetteVertices x μ ν).count z : ℕ) : ℝ) / 4 = 1 := by
  have h0 : ∑ x : TorusSite n, (if x = z then (1 : ℝ) else 0) = 1 := by
    simpa using sum_translate_indicator 0 z
  have h3 : ∑ x : TorusSite n, (if x + unitStep n μ + unitStep n ν = z then (1 : ℝ) else 0) = 1 := by
    simpa only [add_assoc] using sum_translate_indicator (unitStep n μ + unitStep n ν) z
  simp only [count_plaquetteVertices, ← Finset.sum_div, Finset.sum_add_distrib]
  rw [h0, h3, sum_translate_indicator, sum_translate_indicator]
  norm_num
private theorem sum_plaquettes_vertex_weight (z : TorusSite n) (H : Fin 4 → Fin 4 → ℝ) :
    ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
        (((plaquetteVertices p.1 p.2.1 p.2.2).count z : ℕ) : ℝ) / 4 * H p.2.1 p.2.2 =
      ∑ a, ∑ b ∈ Finset.univ.filter (a < ·), H a b := by
  unfold plaquettesIn
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, Finset.mem_univ, implies_true, and_true]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h : a < b
  · simp only [if_pos h]
    rw [← Finset.sum_mul, sum_vertex_weights, one_mul]
  · simp [h]
private theorem inRadius_of_supDist_le {c z : TorusSite n} {r : ℕ} (h : _root_.YangMills.Construction.TorusFields.supDist c z ≤ r) : InRadius r (c - z) := by
  have h1 := inRadius_of_mem (z := z) (c := c) (ρ₀ := (r : ℝ))
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by exact_mod_cast h⟩)
  rwa [Nat.floor_natCast] at h1
private theorem plaquetteEnergy_constantCurvatureField {r : ℕ} {f : Fin 4 → Fin 4 → ℝ} (hr : 4 ≤ r)
    (hn : 2 * r + 2 < n) (hanti : ∀ μ ν, f μ ν = - f ν μ) {z x : TorusSite n} {μ ν : Fin 4} (u : ℝ)
    (hz : z ∈ plaquetteVertices x μ ν) :
    plaquetteEnergy (constantCurvatureField r f z u) x μ ν = 1 - Real.cos (u * f μ ν) := by
  have near : ∀ c ∈ plaquetteVertices x μ ν, InRadius r (c - z) := by
    intro c hc
    apply inRadius_of_supDist_le
    have h1 := supDist_vertex_le hc
    have h2 := supDist_vertex_le hz
    have h3 := _root_.YangMills.Construction.TorusFields.supDist_triangle c x z
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm x z] at h3
    omega
  have e1 : x + unitStep n μ - z = x - z + unitStep n μ := by abel
  have e2 : x + unitStep n ν - z = x - z + unitStep n ν := by abel
  have e3 : x + unitStep n μ + unitStep n ν - z = x - z + unitStep n μ + unitStep n ν := by abel
  have i0 := near x (by simp [plaquetteVertices])
  have i1 := near (x + unitStep n μ) (by simp [plaquetteVertices])
  have i2 := near (x + unitStep n ν) (by simp [plaquetteVertices])
  have i3 := near (x + unitStep n μ + unitStep n ν) (by simp [plaquetteVertices])
  rw [e1] at i1
  rw [e2] at i2
  rw [e3] at i3
  have hk := angleCurl_linearAngle hn hanti i0 i1 i2 i3
  have hc : angleCurl (fun x μ => u * linearAngle r f (x - z) μ) x μ ν = u * f μ ν := by
    unfold angleCurl
    simp only [e1, e2]
    rw [← hk]
    ring
  unfold TorusFields.plaquetteEnergy
  rw [holonomy_constantCurvatureField, hc, coe_expUnit_smul unitI norm_unitI]
  have hu : ((unitI : imaginaryQuaternions) : ℍ[ℝ]) = quatI := rfl
  rw [hu]
  simp [quatI_re]
private theorem levelShare_zero_constantCurvatureField {r : ℕ} {f : Fin 4 → Fin 4 → ℝ} (hr : 4 ≤ r)
    (hn : 2 * r + 2 < n) (hanti : ∀ μ ν, f μ ν = - f ν μ) (a : ℝ) (L : ℕ) (z : TorusSite n) (u : ℝ) :
    levelShare a L 0 Finset.univ z (constantCurvatureField r f z u) =
      ∑ a, ∑ b ∈ Finset.univ.filter (a < ·), (1 - Real.cos (u * f a b)) := by
  rw [← sum_plaquettes_vertex_weight z fun a b => 1 - Real.cos (u * f a b)]
  show ∑ p ∈ plaquettesIn Finset.univ, (((plaquetteVertices p.1 p.2.1 p.2.2).count z : ℕ) : ℝ) / 4 *
    plaquetteEnergy (constantCurvatureField r f z u) p.1 p.2.1 p.2.2 = _
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hz : z ∈ plaquetteVertices p.1 p.2.1 p.2.2
  · rw [plaquetteEnergy_constantCurvatureField hr hn hanti u hz]
  · rw [List.count_eq_zero_of_not_mem hz]
    simp
private theorem second_difference_bare {r : ℕ} {f : Fin 4 → Fin 4 → ℝ} {a : ℝ} {L : ℕ} {z : TorusSite n}
    {τ : ℝ} (hr : 4 ≤ r) (hn : 2 * r + 2 < n) (hf : ∀ μ ν, |f μ ν| ≤ 2) (hanti : ∀ μ ν, f μ ν = - f ν μ)
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1 / 2) :
    |levelShare a L 0 Finset.univ z (constantCurvatureField r f z τ) +
        levelShare a L 0 Finset.univ z (constantCurvatureField r f z (-τ)) -
        2 * levelShare a L 0 Finset.univ z (constantCurvatureField r f z 0) - τ ^ 2 * squareSum f| ≤
      τ ^ 2 * (256 * τ ^ 2) := by
  rw [levelShare_zero_constantCurvatureField hr hn hanti, levelShare_zero_constantCurvatureField hr hn hanti,
    levelShare_zero_constantCurvatureField hr hn hanti]
  have e : (∑ a, ∑ b ∈ Finset.univ.filter (a < ·), (1 - Real.cos (τ * f a b))) +
      (∑ a, ∑ b ∈ Finset.univ.filter (a < ·), (1 - Real.cos (-τ * f a b))) -
      2 * (∑ a, ∑ b ∈ Finset.univ.filter (a < ·), (1 - Real.cos (0 * f a b))) - τ ^ 2 * squareSum f =
      ∑ a, ∑ b ∈ Finset.univ.filter (a < ·), (2 * (1 - Real.cos (τ * f a b)) - (τ * f a b) ^ 2) := by
    unfold squareSum
    simp only [neg_mul, Real.cos_neg, zero_mul, Real.cos_zero, sub_self, Finset.sum_const_zero, mul_zero,
      sub_zero, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [e]
  have hterm : ∀ a b, |2 * (1 - Real.cos (τ * f a b)) - (τ * f a b) ^ 2| ≤ 16 * τ ^ 4 := by
    intro a b
    have hx : |τ * f a b| ≤ 2 * τ := by
      rw [abs_mul, abs_of_nonneg hτ]
      nlinarith [hf a b]
    have hx1 : |τ * f a b| ≤ 1 := by linarith
    have hb := Real.cos_bound hx1
    have e2 : 2 * (1 - Real.cos (τ * f a b)) - (τ * f a b) ^ 2 =
        -(2 * (Real.cos (τ * f a b) - (1 - (τ * f a b) ^ 2 / 2))) := by ring
    rw [e2, abs_neg, abs_mul]
    have h4 : |τ * f a b| ^ 4 ≤ (2 * τ) ^ 4 := pow_le_pow_left₀ (abs_nonneg _) hx 4
    have h5 : (0 : ℝ) ≤ τ ^ 4 := by positivity
    norm_num
    nlinarith
  calc |∑ a, ∑ b ∈ Finset.univ.filter (a < ·), (2 * (1 - Real.cos (τ * f a b)) - (τ * f a b) ^ 2)|
      ≤ ∑ a : Fin 4, ∑ b ∈ Finset.univ.filter (a < ·), 16 * τ ^ 4 := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => hterm a b)
    _ ≤ ∑ _a : Fin 4, 4 * (16 * τ ^ 4) := by
        refine Finset.sum_le_sum fun a _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have : (Finset.univ.filter (a < ·)).card ≤ 4 := (Finset.card_filter_le _ _).trans (by simp)
        exact_mod_cast this
    _ = τ ^ 2 * (256 * τ ^ 2) := by
        simp
        ring
end Bare
section Numbers
private theorem pow_mul_exp_neg_le {b ρ : ℝ} (hb : 0 < b) (hρ : 0 ≤ ρ) :
    ρ ^ 15 * Real.exp (-(b * ρ)) ≤ ((Nat.factorial 15 : ℝ) * (2 / b) ^ 15) * Real.exp (-(b / 2 * ρ)) := by
  have h := Real.pow_div_factorial_le_exp (b / 2 * ρ) (by positivity) 15
  have hf : (0 : ℝ) < (Nat.factorial 15 : ℝ) := by exact_mod_cast Nat.factorial_pos 15
  have h1 : (b / 2 * ρ) ^ 15 ≤ Real.exp (b / 2 * ρ) * (Nat.factorial 15 : ℝ) := by
    rwa [div_le_iff₀ hf] at h
  have h2 : ρ ^ 15 = (2 / b) ^ 15 * (b / 2 * ρ) ^ 15 := by
    rw [← mul_pow]
    congr 1
    field_simp
  have h3 : Real.exp (-(b * ρ)) = Real.exp (-(b / 2 * ρ)) * Real.exp (-(b / 2 * ρ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h4 : Real.exp (b / 2 * ρ) * Real.exp (-(b / 2 * ρ)) = 1 := by
    rw [← Real.exp_add]
    simp
  calc ρ ^ 15 * Real.exp (-(b * ρ))
      = (2 / b) ^ 15 * ((b / 2 * ρ) ^ 15 * Real.exp (-(b / 2 * ρ))) * Real.exp (-(b / 2 * ρ)) := by
        rw [h2, h3]
        ring
    _ ≤ (2 / b) ^ 15 * ((Real.exp (b / 2 * ρ) * (Nat.factorial 15 : ℝ)) * Real.exp (-(b / 2 * ρ))) *
          Real.exp (-(b / 2 * ρ)) := by
        gcongr
    _ = _ := by
        have h5 : (Real.exp (b / 2 * ρ) * (Nat.factorial 15 : ℝ)) * Real.exp (-(b / 2 * ρ)) =
            (Nat.factorial 15 : ℝ) := by
          rw [mul_right_comm, h4, one_mul]
        rw [h5]
        ring
private theorem amplitude_small {a₀ σ ρ : ℝ} (ha : 0 < a₀) (hσ : 0 < σ)
    (hρ : (2 / a₀) * Real.log (160 / (a₀ * σ)) ≤ ρ) :
    80 * ρ * Real.exp (-(a₀ * ρ)) ≤ σ := by
  set x := a₀ * ρ / 2 with hx
  have h1 : ρ ≤ (2 / a₀) * Real.exp x := by
    have h := Real.add_one_le_exp x
    have e : ρ = (2 / a₀) * x := by
      rw [hx]
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hy : 0 < 160 / (a₀ * σ) := by positivity
  have h2 : Real.log (160 / (a₀ * σ)) ≤ x := by
    have h := mul_le_mul_of_nonneg_left hρ (by positivity : 0 ≤ a₀ / 2)
    have e : a₀ / 2 * (2 / a₀ * Real.log (160 / (a₀ * σ))) = Real.log (160 / (a₀ * σ)) := by
      field_simp
    rw [e] at h
    rw [hx]
    linarith
  have h3 : 160 / (a₀ * σ) ≤ Real.exp x := by
    have := Real.exp_le_exp.mpr h2
    rwa [Real.exp_log hy] at this
  have h4 : Real.exp (-x) ≤ a₀ * σ / 160 := by
    rw [Real.exp_neg]
    have h5 := inv_anti₀ hy h3
    have e : (160 / (a₀ * σ))⁻¹ = a₀ * σ / 160 := by
      field_simp
    rwa [e] at h5
  have e2 : Real.exp (-(a₀ * ρ)) = Real.exp (-x) * Real.exp (-x) := by
    rw [← Real.exp_add, hx]
    congr 1
    ring
  have e3 : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    simp
  calc 80 * ρ * Real.exp (-(a₀ * ρ)) ≤ 80 * ((2 / a₀) * Real.exp x) * (Real.exp (-x) * Real.exp (-x)) := by
        rw [e2]
        gcongr
    _ = (160 / a₀) * (Real.exp x * Real.exp (-x)) * Real.exp (-x) := by ring
    _ = (160 / a₀) * Real.exp (-x) := by rw [e3, mul_one]
    _ ≤ (160 / a₀) * (a₀ * σ / 160) := mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = σ := by field_simp
private theorem squareSum_bounds {f : Fin 4 → Fin 4 → ℝ} (hf : ∀ μ ν, |f μ ν| ≤ 2) :
    0 ≤ squareSum f ∧ squareSum f ≤ 64 := by
  constructor
  · exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _
  · calc squareSum f ≤ ∑ a : Fin 4, ∑ b ∈ Finset.univ.filter (a < ·), (4 : ℝ) := by
          refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
          rw [← sq_abs]
          have := hf a b
          have h0 := abs_nonneg (f a b)
          nlinarith
      _ ≤ ∑ _a : Fin 4, 4 * (4 : ℝ) := by
          refine Finset.sum_le_sum fun a _ => ?_
          rw [Finset.sum_const, nsmul_eq_mul]
          refine mul_le_mul_of_nonneg_right ?_ (by norm_num)
          have : (Finset.univ.filter (a < ·)).card ≤ 4 := (Finset.card_filter_le _ _).trans (by simp)
          exact_mod_cast this
      _ = 64 := by
          simp
          norm_num
end Numbers
set_option maxHeartbeats 1000000 in
private theorem shareCurvatureFormAt_of_admissible {T : ParameterAssignment} {y δ N0 : ℝ} (hD : T.Admissible)
    (hy : T.floorMin ≤ y)
    (h₁ : LevelSharesFormCurvatureFamily) (hδ : 0 < δ) (hN0 : 0 < N0)
    (hh : ∀ (t n : ℕ) [NeZero n], 64 ≤ n →
      HasFlatSecondVariation T.coupling δ N0
        (cellsOfSites (torusFrame T.side t n) (Finset.univ : Finset (TorusSite n)))) :
    shareCurvatureFormAt T y := by
  intro C₂ c₂ D₂ d₂ hc₂ hd₂
  have hσ : 0 < T.threshold := hD.σ_pos
  have hσ1 : T.threshold ≤ 1 := hD.σ_one
  set Cw := weightGrowthSup T.rt T.n₁ * maxOfFirstFour T.N with hCw
  have fam : ∀ t : ℕ, IsCurvatureFamily (T.stepParameters y) Cw (levelShareFamily T.coupling T.side (t + 1)) :=
    fun t => (h₁ T hD y hy t).1
  have hrate : 0 ≤ (T.stepParameters y).weightRate := by
    show 0 ≤ T.rt / 2 ^ 10
    have := hD.rt_pos
    positivity
  set a₀ := c₂ / 3 with ha₀d
  have ha₀ : 0 < a₀ := by positivity
  set b := min δ (min a₀ d₂) with hbd
  have hb : 0 < b := lt_min hδ (lt_min ha₀ hd₂)
  have hbδ : b ≤ δ := min_le_left _ _
  have hba : b ≤ a₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hbd₂ : b ≤ d₂ := (min_le_right _ _).trans (min_le_right _ _)
  set K₀ := 2 * |Cw| * 1296 ^ 3 + 64 * N0 * Real.exp δ + 256 + 8196 * |C₂| with hK₀
  set K := 2 * K₀ + 6561 * |D₂| * Real.exp (2 * d₂) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨K * ((Nat.factorial 15 : ℝ) * (2 / b) ^ 15), b / 2,
    max 5 ((2 / a₀) * Real.log (160 / (a₀ * T.threshold))), by positivity, ?_⟩
  intro k n _ ρ₀ z κ hρ₁ hn₀ hn hsym hsupp hdec hE μ ν ρ' τ' hμν hρτ
  have hρ5 : 5 ≤ ρ₀ := (le_max_left _ _).trans hρ₁
  have hρL : (2 / a₀) * Real.log (160 / (a₀ * T.threshold)) ≤ ρ₀ := (le_max_right _ _).trans hρ₁
  have hρ0 : 0 ≤ ρ₀ := by linarith
  have hn64 : 64 ≤ n := by
    have := hD.n₀_ge
    omega
  set r := ⌊ρ₀⌋₊ with hr
  have hr4 : 4 ≤ r := Nat.le_floor (by norm_num; linarith)
  have hr4' : (4 : ℝ) ≤ r := by exact_mod_cast hr4
  have hrρ : (r : ℝ) ≤ ρ₀ := Nat.floor_le hρ0
  have hρr : ρ₀ < r + 1 := Nat.lt_floor_add_one ρ₀
  have hnr : 2 * r + 2 < n := by
    have h : ((2 * r + 2 : ℕ) : ℝ) < n := by
      push_cast
      linarith
    exact_mod_cast h
  set τ := Real.exp (-(a₀ * ρ₀)) with hτd
  have hτ0 : 0 < τ := Real.exp_pos _
  have hsmall : 80 * ρ₀ * τ ≤ T.threshold := amplitude_small ha₀ hσ hρL
  have hrτ : 80 * (r : ℝ) * τ ≤ T.threshold := by
    refine le_trans ?_ hsmall
    gcongr
  have hs : 5 * (16 * (r : ℝ) * τ) ≤ (T.stepParameters y).threshold := by
    show 5 * (16 * (r : ℝ) * τ) ≤ T.threshold
    linarith
  have hπ : 4 * (r : ℝ) * τ < Real.pi := by
    have := Real.pi_gt_three
    linarith
  have hcold : 16 * (r : ℝ) * τ < (T.stepParameters y).threshold := by
    show 16 * (r : ℝ) * τ < T.threshold
    linarith
  have hτ1 : τ ≤ 1 / 2 := by
    have : 80 * (4 : ℝ) * τ ≤ 80 * (r : ℝ) * τ := by gcongr
    linarith
  set Pe := Real.exp (-(b * ρ₀)) with hPe
  have hPe0 : 0 < Pe := Real.exp_pos _
  set R15 := ρ₀ ^ 15 with hR15
  have hρ1 : 1 ≤ ρ₀ := by linarith
  have hR1 : 1 ≤ R15 := one_le_pow₀ hρ1
  have hτPe : τ ≤ Pe := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right hba hρ0
    linarith
  have hpow : ∀ j : ℕ, j ≤ 15 → (r : ℝ) ^ j ≤ R15 := fun j hj =>
    (pow_le_pow_left₀ (Nat.cast_nonneg r) hrρ j).trans (pow_le_pow_right₀ hρ1 hj)
  have hRP : 0 ≤ R15 * Pe := by positivity
  have t4 : |C₂| * (2 * (16 * (r : ℝ) * τ) ^ 3 + 4 * Real.exp (-(c₂ * ρ₀))) / τ ^ 2 ≤
      8196 * |C₂| * (R15 * Pe) := by
    have hexp : Real.exp (-(c₂ * ρ₀)) = τ ^ 3 := by
      rw [hτd, ← Real.exp_nat_mul]
      congr 1
      rw [ha₀d]
      push_cast
      ring
    have e : |C₂| * (2 * (16 * (r : ℝ) * τ) ^ 3 + 4 * Real.exp (-(c₂ * ρ₀))) / τ ^ 2 =
        |C₂| * (8192 * (r : ℝ) ^ 3 + 4) * τ := by
      rw [hexp]
      field_simp
      ring
    rw [e]
    have h3 := hpow 3 (by norm_num)
    have h4 : 8192 * (r : ℝ) ^ 3 + 4 ≤ 8196 * R15 := by linarith
    calc |C₂| * (8192 * (r : ℝ) ^ 3 + 4) * τ ≤ |C₂| * (8196 * R15) * Pe := by gcongr
      _ = _ := by ring
  have hKs : K₀ * (R15 * Pe) = 2 * |Cw| * 1296 ^ 3 * (R15 * Pe) + 64 * N0 * Real.exp δ * (R15 * Pe) +
      256 * (R15 * Pe) + 8196 * |C₂| * (R15 * Pe) := by
    rw [hK₀]
    ring
  have hU : ∀ f : Fin 4 → Fin 4 → ℝ, (∀ μ ν, |f μ ν| ≤ 2) → (∀ μ ν, f μ ν = - f ν μ) →
      |boxForm κ z ρ₀ (planeValue f) (planeValue f) - squareSum f| ≤ K₀ * (R15 * Pe) := by
    intro f hf hanti
    cases k with
    | zero =>
      have hsec := second_difference_bare (a := T.coupling) (L := T.side) (z := z) hr4 hnr hf hanti hτ0.le hτ1
      have h := boxForm_near_of_second_difference hE hf hanti hnr hσ hτ0 hs hπ hsec
      refine h.trans ?_
      have t3 : 256 * τ ^ 2 ≤ 256 * (R15 * Pe) := by
        have h1 : τ ^ 2 ≤ τ := by
          rw [sq]
          exact mul_le_of_le_one_right hτ0.le (by linarith)
        have h2 : Pe ≤ R15 * Pe := le_mul_of_one_le_left hPe0.le hR1
        linarith
      have p1 : 0 ≤ 2 * |Cw| * 1296 ^ 3 * (R15 * Pe) := by positivity
      have p2 : 0 ≤ 64 * N0 * Real.exp δ * (R15 * Pe) := by positivity
      rw [hKs]
      linarith
    | succ t =>
      have hsec := second_difference_above (z := z) (fam t) hrate hn₀ (hh t n hn64) (by omega) hnr hf hanti
        hτ0.le hcold
      have h := boxForm_near_of_second_difference hE hf hanti hnr hσ hτ0 hs hπ hsec
      refine h.trans ?_
      have hS := sum_abs_bondAngles_le (n := n) (r := r) hf
      set S := ∑ l, |bondAngles (n := n) r f l| with hSd
      have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
      have hS1 : S ≤ 1296 * ρ₀ ^ 5 := by
        refine hS.trans ?_
        have h2r : (2 * (r : ℝ) + 1) ≤ 3 * ρ₀ := by linarith
        have h3 : (((2 * r + 1) ^ 4 : ℕ) : ℝ) ≤ (3 * ρ₀) ^ 4 := by
          push_cast
          exact pow_le_pow_left₀ (by positivity) h2r 4
        calc (((2 * r + 1) ^ 4 : ℕ) : ℝ) * (16 * (r : ℝ)) ≤ (3 * ρ₀) ^ 4 * (16 * ρ₀) := by gcongr
          _ = 1296 * ρ₀ ^ 5 := by ring
      have hS3 : S ^ 3 ≤ 1296 ^ 3 * R15 := by
        calc S ^ 3 ≤ (1296 * ρ₀ ^ 5) ^ 3 := pow_le_pow_left₀ hS0 hS1 3
          _ = 1296 ^ 3 * R15 := by rw [hR15]; ring
      have t1 : 2 * (|Cw| * S ^ 3 * τ) ≤ 2 * |Cw| * 1296 ^ 3 * (R15 * Pe) := by
        calc 2 * (|Cw| * S ^ 3 * τ) ≤ 2 * (|Cw| * (1296 ^ 3 * R15) * Pe) := by gcongr
          _ = _ := by ring
      have hsq := squareSum_bounds hf
      have hexpδ : Real.exp (-δ * r) ≤ Real.exp δ * Pe := by
        rw [hPe, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have h1 : b * ρ₀ ≤ δ * ρ₀ := mul_le_mul_of_nonneg_right hbδ hρ0
        have h2 : δ * ρ₀ ≤ δ * ((r : ℝ) + 1) := mul_le_mul_of_nonneg_left hρr.le hδ.le
        linarith
      have t2 : N0 * squareSum f * (r : ℝ) ^ 4 * Real.exp (-δ * r) ≤ 64 * N0 * Real.exp δ * (R15 * Pe) := by
        have h4 := hpow 4 (by norm_num)
        calc N0 * squareSum f * (r : ℝ) ^ 4 * Real.exp (-δ * r) ≤ N0 * 64 * R15 * (Real.exp δ * Pe) := by
              have := hsq.1
              have := hsq.2
              gcongr
          _ = _ := by ring
      rw [hKs]
      linarith
  have hP := plane_sums_of_form hsym hU (P := (μ, ν)) (Q := (ρ', τ')) hμν hρτ
  have hO := plane_sums_off_box (ρ₀ := ρ₀) hd₂ hsupp hdec (μ, ν) (ρ', τ')
  have t5 : ((2 * r + 1 : ℕ) : ℝ) ^ 8 * (|D₂| * Real.exp (-(d₂ * (ρ₀ - 2)))) ≤
      6561 * |D₂| * Real.exp (2 * d₂) * (R15 * Pe) := by
    have h1 : ((2 * r + 1 : ℕ) : ℝ) ^ 8 ≤ 6561 * R15 := by
      have h2r : ((2 * r + 1 : ℕ) : ℝ) ≤ 3 * ρ₀ := by
        push_cast
        linarith
      calc ((2 * r + 1 : ℕ) : ℝ) ^ 8 ≤ (3 * ρ₀) ^ 8 := pow_le_pow_left₀ (by positivity) h2r 8
        _ = 6561 * ρ₀ ^ 8 := by ring
        _ ≤ 6561 * R15 := by
          have := pow_le_pow_right₀ hρ1 (show 8 ≤ 15 by norm_num)
          linarith
    have h2 : Real.exp (-(d₂ * (ρ₀ - 2))) ≤ Real.exp (2 * d₂) * Pe := by
      rw [hPe, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_right hbd₂ hρ0
      linarith
    calc ((2 * r + 1 : ℕ) : ℝ) ^ 8 * (|D₂| * Real.exp (-(d₂ * (ρ₀ - 2))))
        ≤ (6561 * R15) * (|D₂| * (Real.exp (2 * d₂) * Pe)) := by gcongr
      _ = _ := by ring
  have hfin := pow_mul_exp_neg_le hb hρ0
  have htri := abs_sub_le (∑ p ∈ (plaquettesIn Finset.univ).filter (fun p : TorusPlaquette n => p.2 = (μ, ν)),
      ∑ p' ∈ (plaquettesIn Finset.univ).filter (fun p' : TorusPlaquette n => p'.2 = (ρ', τ')), κ p p')
    (boxForm κ z ρ₀ (planeIndicator (μ, ν)) (planeIndicator (ρ', τ')))
    (if ((μ, ν) : Fin 4 × Fin 4) = (ρ', τ') then (1 : ℝ) else 0)
  refine htri.trans ?_
  calc _ ≤ 6561 * |D₂| * Real.exp (2 * d₂) * (R15 * Pe) + 2 * (K₀ * (R15 * Pe)) :=
        add_le_add (hO.trans t5) hP
    _ = K * (R15 * Pe) := by rw [hK]; ring
    _ ≤ K * (((Nat.factorial 15 : ℝ) * (2 / b) ^ 15) * Real.exp (-(b / 2 * ρ₀))) :=
        mul_le_mul_of_nonneg_left hfin hK0
    _ = _ := by ring
theorem shareCurvatureFormStatement_of_curvatureFamily_of_quadraticResponse
    (h₁ : LevelSharesFormCurvatureFamily)
    (h₂ : quadraticResponseAtFlatStatement) : shareCurvatureFormStatement := by
  intro a ha
  obtain ⟨δ₀, hδ₀, h₃⟩ := h₂ a (by linarith)
  obtain ⟨L₀, h₄⟩ := h₃ δ₀ hδ₀ le_rfl
  refine ⟨L₀, fun _ => 1, 0, fun _ => one_pos, ?_⟩
  intro L hL hLL T hTa hTL hD _ _ _ _
  obtain ⟨N0, hN0, h₅⟩ := h₄ L hL hLL
  refine ⟨T.floorMin, fun y hy _ _ => ?_⟩
  subst hTa hTL
  refine shareCurvatureFormAt_of_admissible hD hy h₁ hδ₀ hN0 fun t n _ hn => ?_
  exact h₅ (torusFrame T.side t n) 1024 _ rfl (isAdmissibleAmbient_torusFrame hn) le_rfl
    (isOrthantRegular_torusFrame fun _ => ⟨fun _ => 1, fun _ => Or.inl rfl, fun _ _ _ _ _ _ => Finset.mem_univ _⟩)
end ResponseInTheExpansion
end YangMills.Construction
end
