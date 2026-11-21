import YangMills.Construction.LawInAState.SecondOrderOfAFunctionOfTheFieldProof
import YangMills.Construction.LawInAState.TheMarkOfAFunctionOfTheField
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open Filter
namespace YangMills.Construction.CurvatureKernel
open TorusFields TorusLumps StateLaw LatticeSums BoxForm AxialLogarithm AxialForms ResponseInTheExpansion BlockAverages
  LumpContours ExponentialSums
namespace ExpansionProof
variable {n : ℕ}
private theorem abs_flatHessian_le [NeZero n] {σ E E₃ r : ℝ} {w : ℕ → ℝ} {z : TorusSite n} {u : TorusField n → ℝ} (hσ : 0 < σ)
    (hE : 0 ≤ E) (hE₃ : 0 ≤ E₃) (hw : ∀ m : ℕ, Real.exp (r * m) ≤ w m) (hu : IsRegularObservable σ E E₃ w z u)
    (hT : secondOrderExpansionStatement) {c c' : LatticeBond} (hc : 2 * offsetSupNorm c.1 < n)
    (hc' : 2 * offsetSupNorm c'.1 < n) (hr : 0 < r) :
    |flatHessian u (bondFrom z c) (bondFrom z c')| ≤
      E * Real.exp (-(r * max (offsetSupNorm c.1 : ℝ) (offsetSupNorm c'.1 : ℝ))) := by
  have hwp : ∀ m, 0 < w m := fun m => (Real.exp_pos _).trans_le (hw m)
  obtain ⟨-, hb, -, -⟩ := hT n σ E E₃ w z u hσ hwp hE₃ hu
  refine (hb _ _).trans ?_
  set d := supportDiam z ![bondFrom z c, bondFrom z c'] with hd
  have t1 : offsetSupNorm c.1 ≤ d := by
    have h1 : _root_.YangMills.Construction.TorusFields.supDist z (bondFrom z c).1 ≤ d := le_max_of_le_left
      (Finset.le_sup (f := fun l : Fin 2 => supDist z ((![bondFrom z c, bondFrom z c'] : Fin 2 → TorusBond n) l).1)
        (Finset.mem_univ 0))
    have h2 : _root_.YangMills.Construction.TorusFields.supDist (z + siteOfInt c.1) z = offsetSupNorm c.1 := _root_.YangMills.Construction.LatticeSums.supDist_add_siteOfInt z hc
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm] at h1
    change _root_.YangMills.Construction.TorusFields.supDist (z + siteOfInt c.1) z ≤ d at h1
    omega
  have t2 : offsetSupNorm c'.1 ≤ d := by
    have h1 : _root_.YangMills.Construction.TorusFields.supDist z (bondFrom z c').1 ≤ d := le_max_of_le_left
      (Finset.le_sup (f := fun l : Fin 2 => supDist z ((![bondFrom z c, bondFrom z c'] : Fin 2 → TorusBond n) l).1)
        (Finset.mem_univ 1))
    have h2 : _root_.YangMills.Construction.TorusFields.supDist (z + siteOfInt c'.1) z = offsetSupNorm c'.1 := _root_.YangMills.Construction.LatticeSums.supDist_add_siteOfInt z hc'
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm] at h1
    change _root_.YangMills.Construction.TorusFields.supDist (z + siteOfInt c'.1) z ≤ d at h1
    omega
  have hm : max (offsetSupNorm c.1 : ℝ) (offsetSupNorm c'.1 : ℝ) ≤ d :=
    max_le (by exact_mod_cast t1) (by exact_mod_cast t2)
  rw [div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_left ?_ hE
  rw [Real.exp_neg]
  refine inv_anti₀ (Real.exp_pos _) ((Real.exp_le_exp.mpr ?_).trans (hw d))
  exact mul_le_mul_of_nonneg_left hm hr.le
private theorem two_mul_offsetSupNorm_lt {m : ℕ} (hn : 16 ≤ n) (hm : m ≤ n / 4) {c : LatticeBond} (hc : c ∈ bondsWithin m) :
    2 * offsetSupNorm c.1 < n := by
  have := mem_bondsWithin_iff.1 hc
  omega
private theorem curvatureKernel_symm [NeZero n] {σ E E₃ : ℝ} {w : ℕ → ℝ} {z : TorusSite n} {u : TorusField n → ℝ}
    (hσ : 0 < σ) (hE₃ : 0 ≤ E₃) (hwp : ∀ m, 0 < w m) (hu : IsRegularObservable σ E E₃ w z u)
    (hT : secondOrderExpansionStatement) (m : ℕ) (p p' : TorusPlaquette n) :
    curvatureKernel u z m p p' = curvatureKernel u z m p' p := by
  obtain ⟨hs, -, -, -⟩ := hT n σ E E₃ w z u hσ hwp hE₃ hu
  unfold curvatureKernel
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
  rw [hs]
  ring
private theorem abs_curvatureKernel_le [NeZero n] {σ E E₃ r : ℝ} {w : ℕ → ℝ} {z : TorusSite n} {u : TorusField n → ℝ}
    (hσ : 0 < σ) (hE : 0 ≤ E) (hE₃ : 0 ≤ E₃) (hr : 0 < r) (hn : 16 ≤ n) (hw : ∀ m : ℕ, Real.exp (r * m) ≤ w m)
    (hu : IsRegularObservable σ E E₃ w z u) (hT : secondOrderExpansionStatement) (p p' : TorusPlaquette n) :
    |curvatureKernel u z (n / 4) p p'| ≤
      16 * E * bondWeightSum (r / 4) 3 ^ 2 * Real.exp (-(r / 2 * max (_root_.YangMills.Construction.TorusFields.supDist p.1 z : ℝ) (_root_.YangMills.Construction.TorusFields.supDist p'.1 z : ℝ))) := by
  set P := max (_root_.YangMills.Construction.TorusFields.supDist p.1 z : ℝ) (_root_.YangMills.Construction.TorusFields.supDist p'.1 z : ℝ) with hP
  have hP0 : 0 ≤ P := le_max_of_le_left (Nat.cast_nonneg _)
  unfold curvatureKernel
  rw [← Finset.sum_product' (bondsWithin (n / 4)) (bondsWithin (n / 4))
    (fun c c' => flatHessian u (bondFrom z c) (bondFrom z c') * (axialFormCoeff z c p * axialFormCoeff z c' p'))]
  set s := (bondsWithin (n / 4) ×ˢ bondsWithin (n / 4)).filter
    (fun cc : LatticeBond × LatticeBond => _root_.YangMills.Construction.TorusFields.supDist p.1 z ≤ offsetSupNorm cc.1.1 ∧ _root_.YangMills.Construction.TorusFields.supDist p'.1 z ≤ offsetSupNorm cc.2.1)
    with hs
  have hzero : ∑ cc ∈ bondsWithin (n / 4) ×ˢ bondsWithin (n / 4), flatHessian u (bondFrom z cc.1) (bondFrom z cc.2) *
      (axialFormCoeff z cc.1 p * axialFormCoeff z cc.2 p') =
      ∑ cc ∈ s, flatHessian u (bondFrom z cc.1) (bondFrom z cc.2) *
        (axialFormCoeff z cc.1 p * axialFormCoeff z cc.2 p') := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) fun cc h1 h2 => ?_
    have h3 : ¬ (_root_.YangMills.Construction.TorusFields.supDist p.1 z ≤ offsetSupNorm cc.1.1 ∧ _root_.YangMills.Construction.TorusFields.supDist p'.1 z ≤ offsetSupNorm cc.2.1) := fun h =>
      h2 (Finset.mem_filter.2 ⟨h1, h⟩)
    by_cases h4 : _root_.YangMills.Construction.TorusFields.supDist p.1 z ≤ offsetSupNorm cc.1.1
    · have h5 : offsetSupNorm cc.2.1 < _root_.YangMills.Construction.TorusFields.supDist p'.1 z := by
        by_contra h6
        exact h3 ⟨h4, not_lt.1 h6⟩
      rw [axialFormCoeff_eq_zero_of_lt z cc.2 p' h5]
      simp
    · rw [axialFormCoeff_eq_zero_of_lt z cc.1 p (not_le.1 h4)]
      simp
  rw [hzero]
  have hb : ∀ cc ∈ s, |flatHessian u (bondFrom z cc.1) (bondFrom z cc.2) *
      (axialFormCoeff z cc.1 p * axialFormCoeff z cc.2 p')| ≤ 16 * E * bondPairWeight r cc := by
    intro cc hcc
    obtain ⟨h1, -⟩ := Finset.mem_filter.1 hcc
    obtain ⟨c1, c2⟩ := Finset.mem_product.1 h1
    have q1 := abs_flatHessian_le hσ hE hE₃ hw hu hT (two_mul_offsetSupNorm_lt hn le_rfl c1)
      (two_mul_offsetSupNorm_lt hn le_rfl c2) hr
    have a1 := abs_axialFormCoeff_le z cc.1 p
    have a2 := abs_axialFormCoeff_le z cc.2 p'
    have b1 : (offsetSupNorm cc.1.1 : ℝ) ≤ (1 + (offsetSupNorm cc.1.1 : ℝ)) ^ 3 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) (offsetSupNorm cc.1.1), sq_nonneg (offsetSupNorm cc.1.1 : ℝ),
        pow_nonneg (Nat.cast_nonneg (α := ℝ) (offsetSupNorm cc.1.1)) 3]
    have b2 : (offsetSupNorm cc.2.1 : ℝ) ≤ (1 + (offsetSupNorm cc.2.1 : ℝ)) ^ 3 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) (offsetSupNorm cc.2.1), sq_nonneg (offsetSupNorm cc.2.1 : ℝ),
        pow_nonneg (Nat.cast_nonneg (α := ℝ) (offsetSupNorm cc.2.1)) 3]
    rw [abs_mul, abs_mul]
    calc _ ≤ E * Real.exp (-(r * max (offsetSupNorm cc.1.1 : ℝ) (offsetSupNorm cc.2.1 : ℝ))) *
          ((4 * (1 + (offsetSupNorm cc.1.1 : ℝ)) ^ 3) * (4 * (1 + (offsetSupNorm cc.2.1 : ℝ)) ^ 3)) := by
          gcongr
          · exact a1.trans (by linarith)
          · exact a2.trans (by linarith)
      _ = _ := by
          unfold bondPairWeight
          ring
  have hsum := sum_bondPairWeight_le hr s P hP0 (fun cc hcc => by
    obtain ⟨-, h1, h2⟩ := Finset.mem_filter.1 hcc
    have h1' : (_root_.YangMills.Construction.TorusFields.supDist p.1 z : ℝ) ≤ offsetSupNorm cc.1.1 := by exact_mod_cast h1
    have h2' : (_root_.YangMills.Construction.TorusFields.supDist p'.1 z : ℝ) ≤ offsetSupNorm cc.2.1 := by exact_mod_cast h2
    exact max_le_max h1' h2')
  calc _ ≤ ∑ cc ∈ s, |flatHessian u (bondFrom z cc.1) (bondFrom z cc.2) *
        (axialFormCoeff z cc.1 p * axialFormCoeff z cc.2 p')| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ cc ∈ s, 16 * E * bondPairWeight r cc := Finset.sum_le_sum hb
    _ = 16 * E * ∑ cc ∈ s, bondPairWeight r cc := by rw [Finset.mul_sum]
    _ ≤ 16 * E * (bondWeightSum (r / 4) 3 ^ 2 * Real.exp (-(r / 2 * P))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring
private def curlCoeff [NeZero n] (z : TorusSite n) (ρ : ℝ) (v : TorusBond n → imaginaryQuaternions) (e : Fin 3)
    (c : LatticeBond) : ℝ :=
  ∑ p ∈ plaquettesIn (supBall z ρ), axialFormCoeff z c p * imaginaryComponent e (lieFormCurl v p)
private theorem kernel_sum_eq_coeff_sum [NeZero n] (u : TorusField n → ℝ) (z : TorusSite n) (m : ℕ) (ρ : ℝ)
    (v : TorusBond n → imaginaryQuaternions) :
    ∑ p ∈ plaquettesIn (supBall z ρ), ∑ p' ∈ plaquettesIn (supBall z ρ), curvatureKernel u z m p p' *
        ∑ e : Fin 3, imaginaryComponent e (lieFormCurl v p) * imaginaryComponent e (lieFormCurl v p') =
      ∑ e : Fin 3, ∑ c ∈ bondsWithin m, ∑ c' ∈ bondsWithin m, flatHessian u (bondFrom z c) (bondFrom z c') *
        (curlCoeff z ρ v e c * curlCoeff z ρ v e c') := by
  have h : ∀ e : Fin 3, ∑ c ∈ bondsWithin m, ∑ c' ∈ bondsWithin m, flatHessian u (bondFrom z c) (bondFrom z c') *
      (curlCoeff z ρ v e c * curlCoeff z ρ v e c') =
      ∑ p ∈ plaquettesIn (supBall z ρ), ∑ p' ∈ plaquettesIn (supBall z ρ), curvatureKernel u z m p p' *
        (imaginaryComponent e (lieFormCurl v p) * imaginaryComponent e (lieFormCurl v p')) := fun e =>
    (sum_kernel_form_eq (plaquettesIn (supBall z ρ)) (bondsWithin m)
      (fun c c' => flatHessian u (bondFrom z c) (bondFrom z c'))
      (fun c p => axialFormCoeff z c p) (fun p => imaginaryComponent e (lieFormCurl v p))).symm
  simp only [h, Finset.mul_sum]
  calc _ = ∑ p ∈ plaquettesIn (supBall z ρ), ∑ e : Fin 3, ∑ p' ∈ plaquettesIn (supBall z ρ),
        curvatureKernel u z m p p' *
        (imaginaryComponent e (lieFormCurl v p) * imaginaryComponent e (lieFormCurl v p')) :=
        Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = _ := Finset.sum_comm
private theorem mem_plaquettesIn_univ [NeZero n] {x : TorusSite n} {μ ν : Fin 4} (h : μ < ν) :
    ((x, μ, ν) : TorusPlaquette n) ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)) := by
  simp [plaquettesIn, h]
private theorem plaquettesIn_subset_univ [NeZero n] (S : Finset (TorusSite n)) :
    plaquettesIn S ⊆ plaquettesIn Finset.univ := by
  intro p hp
  simp only [plaquettesIn, Finset.mem_filter, Finset.mem_univ, true_and, implies_true, and_true] at hp ⊢
  exact hp.1
private theorem abs_imaginaryComponent_le (e : Fin 3) (w : imaginaryQuaternions) :
    |imaginaryComponent e w| ≤ ‖(w : ℍ[ℝ])‖ := by apply _root_.YangMills.SharedProofs.p13926 <;> assumption
private theorem abs_curlCoeff_le [NeZero n] {z : TorusSite n} {ρ s t : ℝ} {W : TorusField n}
    {g : TorusSite n → UnitQuaternion} {v : TorusBond n → imaginaryQuaternions}
    (hbox : IsSmallOnBall W g v z ρ s t) (ht : 0 ≤ t) (e : Fin 3) (c : LatticeBond) :
    |curlCoeff z ρ v e c| ≤ 4 * offsetSupNorm c.1 * t := by
  have h1 := axialForm_eq_sum_coeff z c (plaquettesIn Finset.univ)
    (fun p => if p ∈ plaquettesIn (supBall z ρ) then imaginaryComponent e (lieFormCurl v p) else 0)
    (fun ν hν j _ => mem_plaquettesIn_univ hν)
  have h2 : ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), axialFormCoeff z c p *
      (if p ∈ plaquettesIn (supBall z ρ) then imaginaryComponent e (lieFormCurl v p) else 0) =
      curlCoeff z ρ v e c := by
    simp only [mul_ite, mul_zero]
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 (plaquettesIn_subset_univ _)]
    rfl
  rw [← h2, ← h1]
  refine abs_axialForm_le (fun ν _ j _ => ?_) ht
  split_ifs with hp
  · exact (abs_imaginaryComponent_le e _).trans (hbox.curl_le _ hp)
  · simpa using ht
private theorem curlCoeff_eq_circulation [NeZero n] {z : TorusSite n} {ρ : ℝ} {v : TorusBond n → imaginaryQuaternions}
    (e : Fin 3) {c : LatticeBond} (h : (offsetSupNorm c.1 : ℝ) + 2 ≤ ρ) :
    curlCoeff z ρ v e c = circulation z v e c := by
  unfold curlCoeff circulation
  rw [← axialForm_eq_sum_coeff z c (plaquettesIn (supBall z ρ)) (fun p => imaginaryComponent e (lieFormCurl v p))]
  intro ν hν j hj
  have hs := offsetSupNorm_truncate_le c.1 ν hj
  simp only [plaquettesIn, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨hν, fun y hy => ?_⟩
  set x : TorusSite n := z + siteOfInt (truncate c.1 ν j) with hx
  have hd : _root_.YangMills.Construction.TorusFields.supDist x z ≤ offsetSupNorm c.1 := (LatticeSums.supDist_add_siteOfInt_le z _).trans hs
  have step : ∀ (a : TorusSite n) (i : Fin 4), _root_.YangMills.Construction.TorusFields.supDist (a + TorusFields.unitStep n i) z ≤ _root_.YangMills.Construction.TorusFields.supDist a z + 1 := fun a i =>
    (_root_.YangMills.Construction.TorusFields.supDist_triangle _ a _).trans (by rw [_root_.YangMills.Construction.TorusFields.supDist_comm]; have := _root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le a i; omega)
  have hy2 : _root_.YangMills.Construction.TorusFields.supDist y z ≤ offsetSupNorm c.1 + 2 := by
    simp only [plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · omega
    · have := step x c.2
      omega
    · have := step x ν
      omega
    · have h1 := step x c.2
      have h2 := step (x + TorusFields.unitStep n c.2) ν
      omega
  simp only [supBall, Finset.mem_filter, Finset.mem_univ, true_and]
  have : (_root_.YangMills.Construction.TorusFields.supDist y z : ℝ) ≤ (offsetSupNorm c.1 : ℝ) + 2 := by exact_mod_cast hy2
  linarith
private def latticeForm (ζ : LatticeBond → imaginaryQuaternions) (z : TorusSite n) (m : ℕ) (b : TorusBond n) :
    imaginaryQuaternions :=
  ∑ c ∈ bondsWithin m, if bondFrom z c = b then ζ c else 0
private def componentHom (e : Fin 3) : imaginaryQuaternions →+ ℝ :=
  AddMonoidHom.mk' (imaginaryComponent e) (fun a b => by fin_cases e <;> simp [imaginaryComponent])
private theorem imaginaryComponent_latticeForm (ζ : LatticeBond → imaginaryQuaternions) (z : TorusSite n) (m : ℕ)
    (b : TorusBond n) (e : Fin 3) :
    imaginaryComponent e (latticeForm ζ z m b) =
      ∑ c ∈ bondsWithin m, if bondFrom z c = b then imaginaryComponent e (ζ c) else 0 := by
  have h := map_sum (componentHom e) (fun c => if bondFrom z c = b then ζ c else 0) (bondsWithin m)
  simp only [apply_ite (componentHom e), map_zero] at h
  exact h
private theorem latticeForm_bondFrom [NeZero n] (ζ : LatticeBond → imaginaryQuaternions) (z : TorusSite n) {m : ℕ}
    (hm : 2 * m < n) {c : LatticeBond} (hc : c ∈ bondsWithin m) : latticeForm ζ z m (bondFrom z c) = ζ c := by
  unfold latticeForm
  have hs := mem_bondsWithin_iff.1 hc
  rw [Finset.sum_eq_single c]
  · simp
  · intro c' h1 h2
    have hs' := mem_bondsWithin_iff.1 h1
    rw [if_neg fun e => h2 (bondFrom_inj_of_small z (by omega) (by omega) e)]
  · exact fun h => absurd hc h
private theorem latticeForm_eq_zero (ζ : LatticeBond → imaginaryQuaternions) (z : TorusSite n) {m : ℕ} {b : TorusBond n}
    (h : ∀ c ∈ bondsWithin m, bondFrom z c ≠ b) : latticeForm ζ z m b = 0 :=
  Finset.sum_eq_zero fun c hc => if_neg (h c hc)
private theorem sum_pair_eq_sum_bondFrom [NeZero n] (f : TorusBond n → TorusBond n → ℝ) (s : Finset LatticeBond)
    (z : TorusSite n) (x : LatticeBond → ℝ) :
    ∑ b, ∑ b', f b b' * ((∑ c ∈ s, if bondFrom z c = b then x c else 0) *
        ∑ c' ∈ s, if bondFrom z c' = b' then x c' else 0) =
      ∑ c ∈ s, ∑ c' ∈ s, f (bondFrom z c) (bondFrom z c') * (x c * x c') := by
  have h1 : ∀ g : TorusBond n → ℝ, ∑ b, g b * (∑ c ∈ s, if bondFrom z c = b then x c else 0) =
      ∑ c ∈ s, g (bondFrom z c) * x c := by
    intro g
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp
  have h2 : ∀ b, ∑ b', f b b' * ((∑ c ∈ s, if bondFrom z c = b then x c else 0) *
      ∑ c' ∈ s, if bondFrom z c' = b' then x c' else 0) =
      (∑ c' ∈ s, f b (bondFrom z c') * x c') * ∑ c ∈ s, if bondFrom z c = b then x c else 0 := by
    intro b
    rw [← h1 (f b), Finset.sum_mul]
    refine Finset.sum_congr rfl fun b' _ => ?_
    ring
  simp only [h2]
  rw [h1 fun b => ∑ c' ∈ s, f b (bondFrom z c') * x c']
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun c' _ => ?_
  ring
private theorem isCold_expField {σ ε : ℝ} (ξ : TorusBond n → imaginaryQuaternions) (hξ : ∀ b, ‖(ξ b : ℍ[ℝ])‖ ≤ ε)
    (h : 4 * ε < σ) : IsCold σ (expField ξ) := by apply _root_.YangMills.SharedProofs.p24113 <;> assumption
private def torusTripleBound (r : ℝ) : ℝ :=
  (2 * ((1 : ℕ) + 1) / (r / 3) + 1) ^ 1 * (4 * expLatticeSum (r / 3 / 2))
private theorem torusTripleBound_nonneg {r : ℝ} (hr : 0 < r) : 0 ≤ torusTripleBound r := by
  unfold torusTripleBound
  have := expLatticeSum_pos (show 0 < r / 3 / 2 by positivity)
  positivity
private theorem sum_triple_le [NeZero n] {r A : ℝ} {w : ℕ → ℝ} {z : TorusSite n} (ξ : TorusBond n → imaginaryQuaternions)
    (hr : 0 < r) (hA : 0 ≤ A) (hw : ∀ m : ℕ, Real.exp (r * m) ≤ w m)
    (hξ : ∀ b : TorusBond n, ‖(ξ b : ℍ[ℝ])‖ ≤ A * (1 + (_root_.YangMills.Construction.TorusFields.supDist b.1 z : ℝ))) :
    ∑ f : Fin 3 → TorusBond n, (∏ i, ‖(ξ (f i) : ℍ[ℝ])‖) / w (supportDiam z f) ≤ A ^ 3 * torusTripleBound r ^ 3 := by
  set θ := r / 3 with hθ
  have hθ0 : 0 < θ := by positivity
  set h : TorusBond n → ℝ := fun b => A * ((1 + (_root_.YangMills.Construction.TorusFields.supDist b.1 z : ℝ)) ^ 1 * Real.exp (-θ * _root_.YangMills.Construction.TorusFields.supDist b.1 z)) with hh
  have hh0 : ∀ b, 0 ≤ h b := fun b => by positivity
  have term : ∀ f : Fin 3 → TorusBond n, (∏ i, ‖(ξ (f i) : ℍ[ℝ])‖) / w (supportDiam z f) ≤ ∏ i, h (f i) := by
    intro f
    have hd : ∀ i, _root_.YangMills.Construction.TorusFields.supDist (f i).1 z ≤ supportDiam z f := fun i => by
      rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
      exact le_max_of_le_left (Finset.le_sup (f := fun l : Fin 3 => _root_.YangMills.Construction.TorusFields.supDist z (f l).1) (Finset.mem_univ i))
    have he : Real.exp (-(r * supportDiam z f)) ≤ ∏ i, Real.exp (-θ * _root_.YangMills.Construction.TorusFields.supDist (f i).1 z) := by
      rw [← Real.exp_sum]
      apply Real.exp_le_exp.mpr
      have h1 : ∑ i : Fin 3, (_root_.YangMills.Construction.TorusFields.supDist (f i).1 z : ℝ) ≤ 3 * supportDiam z f := by
        calc _ ≤ ∑ _i : Fin 3, (supportDiam z f : ℝ) := Finset.sum_le_sum fun i _ => by exact_mod_cast hd i
          _ = _ := by simp
      rw [← Finset.mul_sum]
      simp only [hθ]
      nlinarith
    have hinv : (w (supportDiam z f))⁻¹ ≤ Real.exp (-(r * supportDiam z f)) := by
      rw [Real.exp_neg]
      exact inv_anti₀ (Real.exp_pos _) (hw _)
    have hp : ∏ i, ‖(ξ (f i) : ℍ[ℝ])‖ ≤ ∏ i, A * (1 + (_root_.YangMills.Construction.TorusFields.supDist (f i).1 z : ℝ)) :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hξ (f i))
    have hnn : 0 ≤ ∏ i, A * (1 + (_root_.YangMills.Construction.TorusFields.supDist (f i).1 z : ℝ)) := Finset.prod_nonneg fun i _ => by positivity
    rw [div_eq_mul_inv]
    calc _ ≤ (∏ i, A * (1 + (_root_.YangMills.Construction.TorusFields.supDist (f i).1 z : ℝ))) * ∏ i, Real.exp (-θ * _root_.YangMills.Construction.TorusFields.supDist (f i).1 z) :=
          mul_le_mul hp (hinv.trans he) (inv_nonneg.2 ((Real.exp_pos _).le.trans (hw _))) hnn
      _ = _ := by
          rw [← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun i _ => ?_
          simp only [hh, pow_one]
          ring
  have hsum : ∑ f : Fin 3 → TorusBond n, ∏ i, h (f i) = (∑ b, h b) ^ 3 := by
    have := Finset.prod_univ_sum (fun _ : Fin 3 => (Finset.univ : Finset (TorusBond n))) (fun _ b => h b)
    simp only [Fintype.piFinset_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
    exact this.symm
  have hb : ∑ b, h b ≤ A * torusTripleBound r := by
    simp only [hh]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_torusBonds_pow_mul_exp_le hθ0 1 z) hA
  calc _ ≤ ∑ f : Fin 3 → TorusBond n, ∏ i, h (f i) := Finset.sum_le_sum fun f _ => term f
    _ = (∑ b, h b) ^ 3 := hsum
    _ ≤ (A * torusTripleBound r) ^ 3 := pow_le_pow_left₀ (Finset.sum_nonneg fun b _ => hh0 b) hb 3
    _ = _ := by ring
private theorem abs_mul_sub_mul_le {al al' y y' A A' K t s i i' j : ℝ} (hA : 1 ≤ A) (hA' : 1 ≤ A') (hK : 1 ≤ K)
    (ht : 0 ≤ t) (hs : 0 ≤ s) (hi : 0 ≤ i) (hi' : 0 ≤ i') (hij : i ≤ j) (hij' : i' ≤ j) (hy : |y| ≤ K * A * t)
    (ha' : |al'| ≤ 4 * A' * t) (hd : |al - y| ≤ K * A ^ 2 * s ^ 2 + i * (4 * A * t))
    (hd' : |al' - y'| ≤ K * A' ^ 2 * s ^ 2 + i' * (4 * A' * t)) :
    |al * al' - y * y'| ≤ A ^ 3 * A' ^ 3 * ((4 * K + K ^ 2) * (t * s ^ 2) + (32 + 8 * K) * (t ^ 2 * j)) := by
  have hj : 0 ≤ j := hi.trans hij
  have e : al * al' - y * y' = (al - y) * al' + y * (al' - y') := by ring
  rw [e]
  have h1 : |(al - y) * al'| ≤ (K * A ^ 2 * s ^ 2 + i * (4 * A * t)) * (4 * A' * t) := by
    rw [abs_mul]
    exact mul_le_mul hd ha' (abs_nonneg _) (by positivity)
  have h2 : |y * (al' - y')| ≤ (K * A * t) * (K * A' ^ 2 * s ^ 2 + i' * (4 * A' * t)) := by
    rw [abs_mul]
    exact mul_le_mul hy hd' (abs_nonneg _) (by positivity)
  have hP1 : A ^ 2 * A' ≤ A ^ 3 * A' ^ 3 := by
    have a1 : A ^ 2 ≤ A ^ 3 := pow_le_pow_right₀ hA (by norm_num)
    have a2 : A' ≤ A' ^ 3 := le_self_pow₀ hA' (by norm_num)
    exact mul_le_mul a1 a2 (by positivity) (by positivity)
  have hP2 : A * A' ^ 2 ≤ A ^ 3 * A' ^ 3 := by
    have a1 : A ≤ A ^ 3 := le_self_pow₀ hA (by norm_num)
    have a2 : A' ^ 2 ≤ A' ^ 3 := pow_le_pow_right₀ hA' (by norm_num)
    exact mul_le_mul a1 a2 (by positivity) (by positivity)
  have hP3 : A * A' ≤ A ^ 3 * A' ^ 3 := by
    have a1 : A ≤ A ^ 3 := le_self_pow₀ hA (by norm_num)
    have a2 : A' ≤ A' ^ 3 := le_self_pow₀ hA' (by norm_num)
    exact mul_le_mul a1 a2 (by positivity) (by positivity)
  set P := A ^ 3 * A' ^ 3 with hP
  have t1 : (K * A ^ 2 * s ^ 2) * (4 * A' * t) ≤ 4 * K * (t * s ^ 2) * P := by
    calc _ = 4 * K * (t * s ^ 2) * (A ^ 2 * A') := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hP1 (by positivity)
  have t2 : (i * (4 * A * t)) * (4 * A' * t) ≤ 16 * (t ^ 2 * j) * P := by
    calc _ = 16 * (t ^ 2 * i) * (A * A') := by ring
      _ ≤ 16 * (t ^ 2 * j) * (A * A') := by gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_left hP3 (by positivity)
  have t3 : (K * A * t) * (K * A' ^ 2 * s ^ 2) ≤ K ^ 2 * (t * s ^ 2) * P := by
    calc _ = K ^ 2 * (t * s ^ 2) * (A * A' ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hP2 (by positivity)
  have t4 : (K * A * t) * (i' * (4 * A' * t)) ≤ 4 * K * (t ^ 2 * j) * P := by
    calc _ = 4 * K * (t ^ 2 * i') * (A * A') := by ring
      _ ≤ 4 * K * (t ^ 2 * j) * (A * A') := by gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_left hP3 (by positivity)
  have hx : 0 ≤ (t ^ 2 * j) * P := by positivity
  have hk : 0 ≤ K * ((t ^ 2 * j) * P) := by positivity
  refine (abs_add_le _ _).trans ((add_le_add h1 h2).trans ?_)
  nlinarith
private theorem abs_quadratic_sub_le {Qf : LatticeBond → LatticeBond → ℝ} {al y : LatticeBond → ℝ} {E r K t s : ℝ}
    {M m : ℕ} (hE : 0 ≤ E) (hr : 0 < r) (hK : 1 ≤ K) (ht0 : 0 ≤ t) (hs0 : 0 ≤ s)
    (hq : ∀ c ∈ bondsWithin M, ∀ c' ∈ bondsWithin M, |Qf c c'| ≤
      E * Real.exp (-(r * max (offsetSupNorm c.1 : ℝ) (offsetSupNorm c'.1 : ℝ))))
    (hyb : ∀ c : LatticeBond, |y c| ≤ K * (1 + offsetSupNorm c.1) * t)
    (hab : ∀ c : LatticeBond, |al c| ≤ 4 * (1 + (offsetSupNorm c.1 : ℝ)) * t)
    (hdb : ∀ c : LatticeBond, |al c - y c| ≤
      K * (1 + (offsetSupNorm c.1 : ℝ)) ^ 2 * s ^ 2 +
        (if c ∈ bondsWithin m then 0 else 1) * (4 * (1 + (offsetSupNorm c.1 : ℝ)) * t)) :
    |(∑ c ∈ bondsWithin M, ∑ c' ∈ bondsWithin M, Qf c c' * (al c * al c')) -
      ∑ c ∈ bondsWithin M, ∑ c' ∈ bondsWithin M, Qf c c' * (y c * y c')| ≤
      E * bondWeightSum (r / 4) 3 ^ 2 *
        ((4 * K + K ^ 2) * (t * s ^ 2) + (32 + 8 * K) * t ^ 2 * Real.exp (-(r / 2 * m))) := by
  rw [← Finset.sum_product' (bondsWithin M) (bondsWithin M) (fun c c' => Qf c c' * (al c * al c')),
    ← Finset.sum_product' (bondsWithin M) (bondsWithin M) (fun c c' => Qf c c' * (y c * y c')),
    ← Finset.sum_sub_distrib]
  set s₀ := bondsWithin M ×ˢ bondsWithin M with hs₀
  let pr : LatticeBond × LatticeBond → Prop := fun cc => ¬ (cc.1 ∈ bondsWithin m ∧ cc.2 ∈ bondsWithin m)
  set c₁ := (4 * K + K ^ 2) * (t * s ^ 2) with hc₁
  set c₂ := (32 + 8 * K) * t ^ 2 with hc₂
  have hterm : ∀ cc ∈ s₀, |Qf cc.1 cc.2 * (al cc.1 * al cc.2) - Qf cc.1 cc.2 * (y cc.1 * y cc.2)| ≤
      E * (c₁ * bondPairWeight r cc + c₂ * (if pr cc then bondPairWeight r cc else 0)) := by
    intro cc hcc
    obtain ⟨i1, i2⟩ := Finset.mem_product.1 hcc
    have q1 := hq _ i1 _ i2
    set j : ℝ := if pr cc then 1 else 0 with hj
    have hj0 : 0 ≤ j := by
      simp only [hj]
      split_ifs <;> norm_num
    have hb := abs_mul_sub_mul_le (al := al cc.1) (al' := al cc.2) (y := y cc.1) (y' := y cc.2)
      (A := 1 + (offsetSupNorm cc.1.1 : ℝ)) (A' := 1 + (offsetSupNorm cc.2.1 : ℝ)) (K := K) (t := t) (s := s)
      (i := if cc.1 ∈ bondsWithin m then 0 else 1) (i' := if cc.2 ∈ bondsWithin m then 0 else 1) (j := j)
      (by have := Nat.cast_nonneg (α := ℝ) (offsetSupNorm cc.1.1); linarith)
      (by have := Nat.cast_nonneg (α := ℝ) (offsetSupNorm cc.2.1); linarith) hK ht0 hs0
      (by split_ifs <;> norm_num) (by split_ifs <;> norm_num)
      (by
        by_cases h1 : cc.1 ∈ bondsWithin m
        · simpa only [h1, if_true] using hj0
        · have : pr cc := fun h => h1 h.1
          simp [h1, hj, this])
      (by
        by_cases h1 : cc.2 ∈ bondsWithin m
        · simpa only [h1, if_true] using hj0
        · have : pr cc := fun h => h1 h.2
          simp [h1, hj, this])
      (hyb _) (hab _) (hdb _) (hdb _)
    have hsplit : Qf cc.1 cc.2 * (al cc.1 * al cc.2) - Qf cc.1 cc.2 * (y cc.1 * y cc.2) =
        Qf cc.1 cc.2 * (al cc.1 * al cc.2 - y cc.1 * y cc.2) := by ring
    rw [hsplit, abs_mul]
    calc _ ≤ (E * Real.exp (-(r * max (offsetSupNorm cc.1.1 : ℝ) (offsetSupNorm cc.2.1 : ℝ)))) *
          ((1 + (offsetSupNorm cc.1.1 : ℝ)) ^ 3 * (1 + (offsetSupNorm cc.2.1 : ℝ)) ^ 3 *
            ((4 * K + K ^ 2) * (t * s ^ 2) + (32 + 8 * K) * (t ^ 2 * j))) :=
          mul_le_mul q1 hb (abs_nonneg _) (by positivity)
      _ = E * (c₁ * bondPairWeight r cc + c₂ * (j * bondPairWeight r cc)) := by
          simp only [hc₁, hc₂, bondPairWeight]
          ring
      _ = _ := by
          simp only [hj]
          split_ifs <;> simp
  have hsum0 := sum_bondPairWeight_le hr s₀ 0 le_rfl (fun cc _ => le_max_of_le_left (Nat.cast_nonneg _))
  have hsumI := sum_bondPairWeight_le hr (s₀.filter pr) m (Nat.cast_nonneg _) (fun cc hcc => by
    obtain ⟨-, hp⟩ := Finset.mem_filter.1 hcc
    by_cases h1 : cc.1 ∈ bondsWithin m
    · have h2 : cc.2 ∉ bondsWithin m := fun h => hp ⟨h1, h⟩
      have h3 : m < offsetSupNorm cc.2.1 := by
        by_contra h
        exact h2 (mem_bondsWithin_iff.2 (not_lt.1 h))
      have : (m : ℝ) ≤ offsetSupNorm cc.2.1 := by exact_mod_cast h3.le
      exact le_max_of_le_right this
    · have h3 : m < offsetSupNorm cc.1.1 := by
        by_contra h
        exact h1 (mem_bondsWithin_iff.2 (not_lt.1 h))
      have : (m : ℝ) ≤ offsetSupNorm cc.1.1 := by exact_mod_cast h3.le
      exact le_max_of_le_left this)
  simp only [mul_zero, neg_zero, Real.exp_zero, mul_one] at hsum0
  calc _ ≤ ∑ cc ∈ s₀, |Qf cc.1 cc.2 * (al cc.1 * al cc.2) - Qf cc.1 cc.2 * (y cc.1 * y cc.2)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ cc ∈ s₀, E * (c₁ * bondPairWeight r cc + c₂ * (if pr cc then bondPairWeight r cc else 0)) :=
        Finset.sum_le_sum hterm
    _ = E * (c₁ * ∑ cc ∈ s₀, bondPairWeight r cc + c₂ * ∑ cc ∈ s₀.filter pr, bondPairWeight r cc) := by
        rw [Finset.sum_filter, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ E * (c₁ * bondWeightSum (r / 4) 3 ^ 2 + c₂ * (bondWeightSum (r / 4) 3 ^ 2 * Real.exp (-(r / 2 * m)))) := by
        gcongr
    _ = _ := by ring
private theorem expansion_near [NeZero n] {σ E E₃ r K : ℝ} {w : ℕ → ℝ} {z : TorusSite n} {u : TorusField n → ℝ}
    {W : TorusField n} {G g : TorusSite n → UnitQuaternion} {v : TorusBond n → imaginaryQuaternions} {ρ s t : ℝ}
    (hσ : 0 < σ) (hE : 0 ≤ E) (hE₃ : 0 ≤ E₃) (hr : 0 < r) (hK : 1 ≤ K) (hn : 16 ≤ n)
    (hw : ∀ m : ℕ, Real.exp (r * m) ≤ w m) (hu : IsRegularObservable σ E E₃ w z u)
    (hcomp : ∀ (W W' : TorusField n) (m : ℕ), IsCold σ W → IsCold σ W' → 2 * m + 2 < n → FieldsAgreeNear W W' z z m →
      |u W - u W'| ≤ E / w m)
    (hT : secondOrderExpansionStatement) (hW : IsCold σ W) (hs0 : 0 ≤ s) (ht0 : 0 ≤ t)
    (hbox : IsSmallOnBall W g v z ρ s t) (m : ℕ) (hm : (m : ℝ) + 2 ≤ ρ) (hρ : 4 * ρ + 4 ≤ n)
    (hKt : K * (1 + m) * t ≤ 1) (hKσ : K * (1 + m) * t ≤ σ / 16)
    (hG : ∀ c : LatticeBond, (offsetSupNorm c.1 : ℝ) + 2 ≤ ρ → K * (1 + offsetSupNorm c.1) * t ≤ 1 →
      ‖(minimalLog (ResponseInTheExpansion.gaugeTransform G W (bondFrom z c)) : ℍ[ℝ])‖ ≤ K * (1 + offsetSupNorm c.1) * t ∧
      ∀ e : Fin 3, |imaginaryComponent e (minimalLog (ResponseInTheExpansion.gaugeTransform G W (bondFrom z c))) -
        circulation z v e c| ≤ K * (1 + offsetSupNorm c.1) ^ 2 * s ^ 2) :
    |u W - u (trivialField n) - (1 / 2) * ∑ p ∈ plaquettesIn (supBall z ρ), ∑ p' ∈ plaquettesIn (supBall z ρ),
        curvatureKernel u z (n / 4) p p' *
          ∑ e : Fin 3, imaginaryComponent e (lieFormCurl v p) * imaginaryComponent e (lieFormCurl v p')| ≤
      E * Real.exp (-(r * m)) + 27 * E₃ * ((K * t) ^ 3 * torusTripleBound r ^ 3) +
        (3 / 2) * (E * bondWeightSum (r / 4) 3 ^ 2 * ((4 * K + K ^ 2) * (t * s ^ 2) +
          (32 + 8 * K) * (t ^ 2 * Real.exp (-(r / 2 * m))))) := by
  have hwp : ∀ m, 0 < w m := fun m => (Real.exp_pos _).trans_le (hw m)
  set M := n / 4 with hM
  have hmn : 4 * m + 12 ≤ n := by
    have : 4 * (m : ℝ) + 12 ≤ n := by linarith
    exact_mod_cast this
  have hmM : m ≤ M := by omega
  have hMn : 2 * M < n := by omega
  set ζ : LatticeBond → imaginaryQuaternions := fun c =>
    minimalLog (ResponseInTheExpansion.gaugeTransform G W (bondFrom z c)) with hζd
  set ζ' : LatticeBond → imaginaryQuaternions := fun c => if c ∈ bondsWithin m then ζ c else 0 with hζ'd
  set ξ : TorusBond n → imaginaryQuaternions := latticeForm ζ' z M with hξd
  have hζ : ∀ c ∈ bondsWithin m, ‖(ζ c : ℍ[ℝ])‖ ≤ K * (1 + offsetSupNorm c.1) * t ∧
      ∀ e : Fin 3, |imaginaryComponent e (ζ c) - circulation z v e c| ≤ K * (1 + offsetSupNorm c.1) ^ 2 * s ^ 2 := by
    intro c hc
    have hs : (offsetSupNorm c.1 : ℝ) ≤ m := by exact_mod_cast mem_bondsWithin_iff.1 hc
    refine hG c (by linarith) (le_trans ?_ hKt)
    gcongr
  have hζσ : ∀ c ∈ bondsWithin m, ‖(ζ c : ℍ[ℝ])‖ ≤ σ / 16 := by
    intro c hc
    have hs : (offsetSupNorm c.1 : ℝ) ≤ m := by exact_mod_cast mem_bondsWithin_iff.1 hc
    refine (hζ c hc).1.trans (le_trans ?_ hKσ)
    gcongr
  have hsub : ∀ {c : LatticeBond}, c ∈ bondsWithin m → c ∈ bondsWithin M := fun hc =>
    mem_bondsWithin_iff.2 ((mem_bondsWithin_iff.1 hc).trans hmM)
  have hxi : ∀ b, ‖(ξ b : ℍ[ℝ])‖ ≤ K * t * (1 + (_root_.YangMills.Construction.TorusFields.supDist b.1 z : ℝ)) ∧ ‖(ξ b : ℍ[ℝ])‖ ≤ σ / 16 := by
    intro b
    have nn : 0 ≤ K * t * (1 + (_root_.YangMills.Construction.TorusFields.supDist b.1 z : ℝ)) := by positivity
    by_cases hb : ∃ c ∈ bondsWithin M, bondFrom z c = b
    · obtain ⟨c, hc, rfl⟩ := hb
      have hcs := mem_bondsWithin_iff.1 hc
      have hv : ξ (bondFrom z c) = ζ' c := latticeForm_bondFrom ζ' z hMn hc
      rw [hv]
      by_cases hcm : c ∈ bondsWithin m
      · simp only [hζ'd, hcm, if_true]
        refine ⟨(hζ c hcm).1.trans (le_of_eq ?_), hζσ c hcm⟩
        have : _root_.YangMills.Construction.TorusFields.supDist (bondFrom z c).1 z = offsetSupNorm c.1 := _root_.YangMills.Construction.LatticeSums.supDist_add_siteOfInt z (by omega)
        rw [this]
        ring
      · simp only [hζ'd, hcm, if_false, ZeroMemClass.coe_zero, norm_zero]
        exact ⟨nn, by positivity⟩
    · have hb' : ∀ c ∈ bondsWithin M, bondFrom z c ≠ b := fun c hc e => hb ⟨c, hc, e⟩
      have hv : ξ b = 0 := latticeForm_eq_zero ζ' z hb'
      rw [hv]
      simp only [ZeroMemClass.coe_zero, norm_zero]
      exact ⟨nn, by positivity⟩
  have hcoldW : IsCold σ (expField ξ) := isCold_expField (ε := σ / 16) ξ (fun b => (hxi b).2) (by linarith)
  have hcoldG : IsCold σ (TorusFields.gaugeTransform G W) := fun x μ ν h => by
    rw [_root_.YangMills.Construction.TorusFields.curvature_gaugeTransform]
    exact hW x μ ν h
  have hagree : FieldsAgreeNear (TorusFields.gaugeTransform G W) (expField ξ) z z m := by
    intro b hb
    have hc : b ∈ bondsWithin m := by
      refine mem_bondsWithin_iff.2 (Finset.sup_le fun i _ => ?_)
      have := hb.1 i
      rw [Int.abs_eq_natAbs] at this
      exact_mod_cast this
    have hv : ξ (bondFrom z b) = ζ b := by
      rw [hξd, latticeForm_bondFrom ζ' z hMn (hsub hc)]
      simp [hζ'd, hc]
    change ResponseInTheExpansion.gaugeTransform G W (bondFrom z b) = expUnit (ξ (bondFrom z b))
    rw [hv]
    exact (GaugeFixing.expUnit_minimalLog _).symm
  have h1 : |u W - u (expField ξ)| ≤ E * Real.exp (-(r * m)) := by
    have := hcomp _ _ m hcoldG hcoldW (by omega) hagree
    rw [hu.gauge_invariant G W hW] at this
    refine this.trans ?_
    rw [div_eq_mul_inv, Real.exp_neg]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ (Real.exp_pos _) (hw m)) hE
  obtain ⟨-, -, -, htay⟩ := hT n σ E E₃ w z u hσ hwp hE₃ hu
  have h2 := htay ξ fun b => (hxi b).2
  have h3 : ∑ f : Fin 3 → TorusBond n, (∏ i, ‖(ξ (f i) : ℍ[ℝ])‖) / w (supportDiam z f) ≤
      (K * t) ^ 3 * torusTripleBound r ^ 3 :=
    sum_triple_le ξ hr (by positivity) hw fun b => (hxi b).1
  set y : Fin 3 → LatticeBond → ℝ := fun e c => imaginaryComponent e (ζ' c) with hy
  set Q : LatticeBond → LatticeBond → ℝ := fun c c' => flatHessian u (bondFrom z c) (bondFrom z c') with hQ
  have h4 : ∑ b, ∑ b', flatHessian u b b' * colorPairing ξ ξ b b' =
      ∑ e : Fin 3, ∑ c ∈ bondsWithin M, ∑ c' ∈ bondsWithin M, Q c c' * (y e c * y e c') := by
    have he : ∀ e : Fin 3, ∑ b, ∑ b', flatHessian u b b' * (imaginaryComponent e (ξ b) * imaginaryComponent e (ξ b')) =
        ∑ c ∈ bondsWithin M, ∑ c' ∈ bondsWithin M, Q c c' * (y e c * y e c') := by
      intro e
      simp only [hξd, imaginaryComponent_latticeForm]
      exact sum_pair_eq_sum_bondFrom (flatHessian u) (bondsWithin M) z (y e)
    simp only [← he, colorPairing, Finset.mul_sum]
    calc _ = ∑ b, ∑ e : Fin 3, ∑ b', flatHessian u b b' *
          (imaginaryComponent e (ξ b) * imaginaryComponent e (ξ b')) :=
          Finset.sum_congr rfl fun b _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  have h5 := kernel_sum_eq_coeff_sum u z M ρ v
  set S2 := bondWeightSum (r / 4) 3 ^ 2 with hS2
  set c₁ := (4 * K + K ^ 2) * (t * s ^ 2) with hc₁
  set c₂ := (32 + 8 * K) * t ^ 2 with hc₂
  have h6 : ∀ e : Fin 3,
      |(∑ c ∈ bondsWithin M, ∑ c' ∈ bondsWithin M, Q c c' * (curlCoeff z ρ v e c * curlCoeff z ρ v e c')) -
      ∑ c ∈ bondsWithin M, ∑ c' ∈ bondsWithin M, Q c c' * (y e c * y e c')| ≤
      E * S2 * (c₁ + c₂ * Real.exp (-(r / 2 * m))) := by
    intro e
    have hyb : ∀ c : LatticeBond, |y e c| ≤ K * (1 + offsetSupNorm c.1) * t := by
      intro c
      by_cases hc : c ∈ bondsWithin m
      · simp only [hy, hζ'd, hc, if_true]
        exact (abs_imaginaryComponent_le e _).trans (hζ c hc).1
      · simp only [hy, hζ'd, hc, if_false]
        have : imaginaryComponent e (0 : imaginaryQuaternions) = 0 := by
          fin_cases e <;> simp [imaginaryComponent]
        rw [this, abs_zero]
        positivity
    have hab : ∀ c : LatticeBond, |curlCoeff z ρ v e c| ≤ 4 * (1 + (offsetSupNorm c.1 : ℝ)) * t := by
      intro c
      refine (abs_curlCoeff_le hbox ht0 e c).trans ?_
      gcongr
      linarith
    have hdb : ∀ c : LatticeBond, |curlCoeff z ρ v e c - y e c| ≤
        K * (1 + (offsetSupNorm c.1 : ℝ)) ^ 2 * s ^ 2 +
          (if c ∈ bondsWithin m then 0 else 1) * (4 * (1 + (offsetSupNorm c.1 : ℝ)) * t) := by
      intro c
      by_cases hc : c ∈ bondsWithin m
      · have hs : (offsetSupNorm c.1 : ℝ) ≤ m := by exact_mod_cast mem_bondsWithin_iff.1 hc
        simp only [hc, if_true, zero_mul, add_zero]
        rw [curlCoeff_eq_circulation e (by linarith), abs_sub_comm]
        simp only [hy, hζ'd, hc, if_true]
        exact (hζ c hc).2 e
      · simp only [hc, if_false, one_mul]
        have hy0 : y e c = 0 := by
          simp only [hy, hζ'd, hc, if_false]
          fin_cases e <;> simp [imaginaryComponent]
        rw [hy0, sub_zero]
        refine (hab c).trans ?_
        have : 0 ≤ K * (1 + (offsetSupNorm c.1 : ℝ)) ^ 2 * s ^ 2 := by positivity
        linarith
    exact abs_quadratic_sub_le hE hr hK ht0 hs0 (fun c hc c' hc' =>
      abs_flatHessian_le hσ hE hE₃ hw hu hT (two_mul_offsetSupNorm_lt hn le_rfl hc)
        (two_mul_offsetSupNorm_lt hn le_rfl hc') hr) hyb hab hdb
  have h7 : |(∑ b, ∑ b', flatHessian u b b' * colorPairing ξ ξ b b') -
      ∑ p ∈ plaquettesIn (supBall z ρ), ∑ p' ∈ plaquettesIn (supBall z ρ), curvatureKernel u z M p p' *
        ∑ e : Fin 3, imaginaryComponent e (lieFormCurl v p) * imaginaryComponent e (lieFormCurl v p')| ≤
      3 * (E * S2 * (c₁ + c₂ * Real.exp (-(r / 2 * m)))) := by
    rw [h4, h5, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ _e : Fin 3, E * S2 * (c₁ + c₂ * Real.exp (-(r / 2 * m))) := Finset.sum_le_sum fun e _ => by
          rw [abs_sub_comm]
          exact h6 e
      _ = _ := by simp
  set X := ∑ b, ∑ b', flatHessian u b b' * colorPairing ξ ξ b b' with hX
  set Z := ∑ p ∈ plaquettesIn (supBall z ρ), ∑ p' ∈ plaquettesIn (supBall z ρ), curvatureKernel u z M p p' *
        ∑ e : Fin 3, imaginaryComponent e (lieFormCurl v p) * imaginaryComponent e (lieFormCurl v p') with hZ
  have e3 : u W - u (trivialField n) - (1 / 2) * Z = (u W - u (expField ξ)) +
      (u (expField ξ) - u (trivialField n) - (1 / 2) * X) + (1 / 2) * (X - Z) := by ring
  rw [e3]
  have h8 : 27 * E₃ * ∑ f : Fin 3 → TorusBond n, (∏ i, ‖(ξ (f i) : ℍ[ℝ])‖) / w (supportDiam z f) ≤
      27 * E₃ * ((K * t) ^ 3 * torusTripleBound r ^ 3) := mul_le_mul_of_nonneg_left h3 (by positivity)
  have h9 : |(1 / 2 : ℝ) * (X - Z)| ≤ (3 / 2) * (E * S2 * (c₁ + c₂ * Real.exp (-(r / 2 * m)))) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith
  have h10 := abs_add_three (u W - u (expField ξ)) (u (expField ξ) - u (trivialField n) - (1 / 2) * X)
    ((1 / 2) * (X - Z))
  linarith [h2.trans h8]
private theorem exists_good_radius {ρ t K₁ r : ℝ} (hρ : 2 ≤ ρ) (ht : 0 ≤ t) (hK₁ : 0 < K₁) (hKt : K₁ * t ≤ 1 / 4)
    (hr : 0 < r) :
    ∃ m : ℕ, (m : ℝ) + 2 ≤ ρ ∧ K₁ * (1 + m) * t ≤ 1 ∧
      Real.exp (-(r / 2 * m)) ≤ Real.exp (3 * r / 2) * (Real.exp (-(r / 2 * ρ)) + 27 * (2 * K₁ / r) ^ 3 * t ^ 3) := by
  by_cases h : K₁ * t * ρ ≤ 1
  · refine ⟨⌊ρ - 2⌋₊, ?_, ?_, ?_⟩
    · have := Nat.floor_le (show 0 ≤ ρ - 2 by linarith)
      linarith
    · have h1 := Nat.floor_le (show 0 ≤ ρ - 2 by linarith)
      have h2 : 1 + (⌊ρ - 2⌋₊ : ℝ) ≤ ρ := by linarith
      calc _ = K₁ * t * (1 + (⌊ρ - 2⌋₊ : ℝ)) := by ring
        _ ≤ K₁ * t * ρ := by gcongr
        _ ≤ 1 := h
    · have h1 := Nat.lt_floor_add_one (ρ - 2)
      have e1 : Real.exp (-(r / 2 * (⌊ρ - 2⌋₊ : ℝ))) ≤ Real.exp (3 * r / 2) * Real.exp (-(r / 2 * ρ)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith
      refine e1.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
      have : 0 ≤ 27 * (2 * K₁ / r) ^ 3 * t ^ 3 := by positivity
      linarith
  · have hKtρ : 1 < K₁ * t * ρ := not_le.1 h
    have htpos : 0 < t := by
      rcases ht.lt_or_eq with h0 | h0
      · exact h0
      · rw [← h0] at hKtρ
        simp at hKtρ
        linarith
    have hq : 0 < K₁ * t := by positivity
    set x := 1 / (K₁ * t) with hx
    have hxK : x * (K₁ * t) = 1 := by
      rw [hx]
      field_simp
    have hx4 : 4 ≤ x := by
      rw [hx, le_div_iff₀ hq]
      linarith
    have hxρ : x < ρ := by
      rw [hx, div_lt_iff₀ hq]
      nlinarith
    refine ⟨⌊x - 2⌋₊, ?_, ?_, ?_⟩
    · have := Nat.floor_le (show 0 ≤ x - 2 by linarith)
      linarith
    · have h1 := Nat.floor_le (show 0 ≤ x - 2 by linarith)
      have h2 : 1 + (⌊x - 2⌋₊ : ℝ) ≤ x := by linarith
      calc _ = K₁ * t * (1 + (⌊x - 2⌋₊ : ℝ)) := by ring
        _ ≤ K₁ * t * x := by gcongr
        _ = 1 := by rw [mul_comm]; exact hxK
    · have h1 := Nat.lt_floor_add_one (x - 2)
      set yy := r / 2 * x with hy
      have hyp : 0 < yy := by positivity
      have e1 : Real.exp (-(r / 2 * (⌊x - 2⌋₊ : ℝ))) ≤ Real.exp (3 * r / 2) * Real.exp (-yy) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        simp only [hy]
        nlinarith
      have e2 : Real.exp (-yy) ≤ 27 * (2 * K₁ / r) ^ 3 * t ^ 3 := by
        have h3 : yy / 3 ≤ Real.exp (yy / 3) := by
          have := Real.add_one_le_exp (yy / 3)
          linarith
        have h4 : (yy / 3) ^ 3 ≤ Real.exp yy := by
          calc (yy / 3) ^ 3 ≤ Real.exp (yy / 3) ^ 3 := pow_le_pow_left₀ (by positivity) h3 3
            _ = Real.exp yy := by
              rw [← Real.exp_nat_mul]
              congr 1
              push_cast
              ring
        have h5 : 0 < (yy / 3) ^ 3 := by positivity
        have h6 : Real.exp (-yy) ≤ ((yy / 3) ^ 3)⁻¹ := by
          rw [Real.exp_neg]
          exact inv_anti₀ h5 h4
        refine h6.trans (le_of_eq ?_)
        have hyy : yy = r / (2 * (K₁ * t)) := by
          simp only [hy, hx]
          field_simp
        rw [hyy]
        field_simp
        norm_num
      refine e1.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
      have := Real.exp_pos (-(r / 2 * ρ))
      linarith
private theorem abs_kernel_sum_le [NeZero n] {σ E E₃ r : ℝ} {w : ℕ → ℝ} {z : TorusSite n} {u : TorusField n → ℝ}
    {W : TorusField n} {g : TorusSite n → UnitQuaternion} {v : TorusBond n → imaginaryQuaternions} {ρ s t : ℝ}
    (hσ : 0 < σ) (hE : 0 ≤ E) (hE₃ : 0 ≤ E₃) (hr : 0 < r) (hn : 16 ≤ n)
    (hw : ∀ m : ℕ, Real.exp (r * m) ≤ w m) (hu : IsRegularObservable σ E E₃ w z u)
    (hT : secondOrderExpansionStatement) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hbox : IsSmallOnBall W g v z ρ s t) :
    |∑ p ∈ plaquettesIn (supBall z ρ), ∑ p' ∈ plaquettesIn (supBall z ρ), curvatureKernel u z (n / 4) p p' *
        ∑ e : Fin 3, imaginaryComponent e (lieFormCurl v p) * imaginaryComponent e (lieFormCurl v p')| ≤
      48 * E * bondWeightSum (r / 4) 3 ^ 2 := by
  rw [kernel_sum_eq_coeff_sum]
  have he : ∀ e : Fin 3, |∑ c ∈ bondsWithin (n / 4), ∑ c' ∈ bondsWithin (n / 4),
      flatHessian u (bondFrom z c) (bondFrom z c') * (curlCoeff z ρ v e c * curlCoeff z ρ v e c')| ≤
      16 * E * bondWeightSum (r / 4) 3 ^ 2 := by
    intro e
    rw [← Finset.sum_product' (bondsWithin (n / 4)) (bondsWithin (n / 4))
      (fun c c' => flatHessian u (bondFrom z c) (bondFrom z c') * (curlCoeff z ρ v e c * curlCoeff z ρ v e c'))]
    have hb : ∀ cc ∈ bondsWithin (n / 4) ×ˢ bondsWithin (n / 4), |flatHessian u (bondFrom z cc.1) (bondFrom z cc.2) *
        (curlCoeff z ρ v e cc.1 * curlCoeff z ρ v e cc.2)| ≤ 16 * E * bondPairWeight r cc := by
      intro cc hcc
      obtain ⟨i1, i2⟩ := Finset.mem_product.1 hcc
      have q1 := abs_flatHessian_le hσ hE hE₃ hw hu hT (two_mul_offsetSupNorm_lt hn le_rfl i1)
        (two_mul_offsetSupNorm_lt hn le_rfl i2) hr
      have a1 := abs_curlCoeff_le hbox ht0 e cc.1
      have a2 := abs_curlCoeff_le hbox ht0 e cc.2
      have b1 : 4 * (offsetSupNorm cc.1.1 : ℝ) * t ≤ 4 * (1 + (offsetSupNorm cc.1.1 : ℝ)) ^ 3 := by
        have : (offsetSupNorm cc.1.1 : ℝ) ≤ (1 + (offsetSupNorm cc.1.1 : ℝ)) ^ 3 := by
          nlinarith [Nat.cast_nonneg (α := ℝ) (offsetSupNorm cc.1.1), sq_nonneg (offsetSupNorm cc.1.1 : ℝ),
            pow_nonneg (Nat.cast_nonneg (α := ℝ) (offsetSupNorm cc.1.1)) 3]
        nlinarith [Nat.cast_nonneg (α := ℝ) (offsetSupNorm cc.1.1)]
      have b2 : 4 * (offsetSupNorm cc.2.1 : ℝ) * t ≤ 4 * (1 + (offsetSupNorm cc.2.1 : ℝ)) ^ 3 := by
        have : (offsetSupNorm cc.2.1 : ℝ) ≤ (1 + (offsetSupNorm cc.2.1 : ℝ)) ^ 3 := by
          nlinarith [Nat.cast_nonneg (α := ℝ) (offsetSupNorm cc.2.1), sq_nonneg (offsetSupNorm cc.2.1 : ℝ),
            pow_nonneg (Nat.cast_nonneg (α := ℝ) (offsetSupNorm cc.2.1)) 3]
        nlinarith [Nat.cast_nonneg (α := ℝ) (offsetSupNorm cc.2.1)]
      rw [abs_mul, abs_mul]
      calc _ ≤ E * Real.exp (-(r * max (offsetSupNorm cc.1.1 : ℝ) (offsetSupNorm cc.2.1 : ℝ))) *
            ((4 * (1 + (offsetSupNorm cc.1.1 : ℝ)) ^ 3) * (4 * (1 + (offsetSupNorm cc.2.1 : ℝ)) ^ 3)) := by
            gcongr
            · exact a1.trans b1
            · exact a2.trans b2
        _ = _ := by
            unfold bondPairWeight
            ring
    have hsum := sum_bondPairWeight_le hr (bondsWithin (n / 4) ×ˢ bondsWithin (n / 4)) 0 le_rfl
      (fun cc _ => le_max_of_le_left (Nat.cast_nonneg _))
    simp only [mul_zero, neg_zero, Real.exp_zero, mul_one] at hsum
    calc _ ≤ ∑ cc ∈ bondsWithin (n / 4) ×ˢ bondsWithin (n / 4), |flatHessian u (bondFrom z cc.1) (bondFrom z cc.2) *
          (curlCoeff z ρ v e cc.1 * curlCoeff z ρ v e cc.2)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ cc ∈ bondsWithin (n / 4) ×ˢ bondsWithin (n / 4), 16 * E * bondPairWeight r cc := Finset.sum_le_sum hb
      _ = 16 * E * ∑ cc ∈ bondsWithin (n / 4) ×ˢ bondsWithin (n / 4), bondPairWeight r cc := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ _e : Fin 3, 16 * E * bondWeightSum (r / 4) 3 ^ 2 := Finset.sum_le_sum fun e _ => he e
    _ = _ := by
      simp
      ring
private theorem abs_sub_trivialField_le [NeZero n] {σ E E₃ r : ℝ} {w : ℕ → ℝ} {z : TorusSite n} {u : TorusField n → ℝ}
    {W : TorusField n} (hσ : 0 < σ) (hE : 0 ≤ E) (hn : 16 ≤ n) (hw : ∀ m : ℕ, Real.exp (r * m) ≤ w m)
    (hcomp : ∀ (W W' : TorusField n) (m : ℕ), IsCold σ W → IsCold σ W' → 2 * m + 2 < n → FieldsAgreeNear W W' z z m →
      |u W - u W'| ≤ E / w m) (hW : IsCold σ W) : |u W - u (trivialField n)| ≤ E := by
  have hflat : IsCold σ (trivialField n) := fun x μ ν _ => by simpa [curvature, holonomy, trivialField] using hσ
  have hag : FieldsAgreeNear W (trivialField n) z z 0 := by
    intro b hb
    exfalso
    have h1 := hb.1 b.2
    have h2 := hb.2 b.2
    simp only [Pi.add_apply, Pi.single_eq_same] at h2
    simp only [Nat.cast_zero, abs_nonpos_iff] at h1 h2
    omega
  have h := hcomp W (trivialField n) 0 hW hflat (by omega) hag
  refine h.trans ?_
  have h0 := hw 0
  simp only [Nat.cast_zero, mul_zero, Real.exp_zero] at h0
  exact div_le_self hE h0
private theorem near_bound_le {E E₃ S2 Tb K t s2 e ex ee D Eb C A₃ A₁ A₂ B₂ : ℝ} (hE : 0 ≤ E) (hS : 0 ≤ S2)
    (hK : 0 ≤ K) (ht : 0 ≤ t) (ht1 : t ≤ 1) (hs2 : 0 ≤ s2) (he : 0 ≤ e) (hee : 0 ≤ ee) (hex : ex ≤ e)
    (hA₃ : A₃ = 27 * E₃ * (K ^ 3 * Tb ^ 3)) (hA₁ : A₁ = (3 / 2) * (E * S2 * (4 * K + K ^ 2)))
    (hA₂ : A₂ = E + (3 / 2) * (E * S2 * (32 + 8 * K))) (hB₂ : B₂ = A₂ * Eb) (hA₂0 : 0 ≤ A₂)
    (hm : e ≤ Eb * (ee + D * t ^ 3))
    (hC1 : A₃ + B₂ * D ≤ C) (hC2 : A₁ ≤ C) (hC3 : B₂ ≤ C) :
    E * ex + 27 * E₃ * ((K * t) ^ 3 * Tb ^ 3) +
        (3 / 2) * (E * S2 * ((4 * K + K ^ 2) * (t * s2) + (32 + 8 * K) * (t ^ 2 * e))) ≤
      C * (t ^ 3 + t * s2 + ee) := by
  have b1 : E * ex ≤ E * e := mul_le_mul_of_nonneg_left hex hE
  have b2 : 27 * E₃ * ((K * t) ^ 3 * Tb ^ 3) = A₃ * t ^ 3 := by
    rw [hA₃]
    ring
  have ht2 : t ^ 2 ≤ 1 := by nlinarith
  have h8 : 0 ≤ 32 + 8 * K := by positivity
  have hES : 0 ≤ E * S2 := by positivity
  have b3 : (32 + 8 * K) * (t ^ 2 * e) ≤ (32 + 8 * K) * e := by
    refine mul_le_mul_of_nonneg_left ?_ h8
    calc t ^ 2 * e ≤ 1 * e := mul_le_mul_of_nonneg_right ht2 he
      _ = e := one_mul e
  have b4 : (3 / 2) * (E * S2 * ((4 * K + K ^ 2) * (t * s2) + (32 + 8 * K) * (t ^ 2 * e))) ≤
      A₁ * (t * s2) + (3 / 2) * (E * S2 * (32 + 8 * K)) * e := by
    have := mul_le_mul_of_nonneg_left b3 hES
    rw [hA₁]
    linarith
  have b5 : A₂ * e ≤ B₂ * (ee + D * t ^ 3) := by
    rw [hB₂, mul_assoc]
    exact mul_le_mul_of_nonneg_left hm hA₂0
  have hsum : E * e + (3 / 2) * (E * S2 * (32 + 8 * K)) * e = A₂ * e := by
    rw [hA₂]
    ring
  have ht3 : 0 ≤ t ^ 3 := by positivity
  have hts : 0 ≤ t * s2 := by positivity
  have g1 : (A₃ + B₂ * D) * t ^ 3 ≤ C * t ^ 3 := mul_le_mul_of_nonneg_right hC1 ht3
  have g2 : A₁ * (t * s2) ≤ C * (t * s2) := mul_le_mul_of_nonneg_right hC2 hts
  have g3 : B₂ * ee ≤ C * ee := mul_le_mul_of_nonneg_right hC3 hee
  have e7 : C * (t ^ 3 + t * s2 + ee) = C * t ^ 3 + C * (t * s2) + C * ee := by ring
  rw [e7, b2]
  linarith
private theorem far_bound_le {T₁ K₁ r t ρ s2 C ee : ℝ} (hT₁ : 0 ≤ T₁) (hK₁ : 0 < K₁) (ht : 0 ≤ t) (hs2 : 0 ≤ s2)
    (hr : 0 < r) (hee : ee = Real.exp (-(r / 2 * ρ))) (hmain : ¬ (2 ≤ ρ ∧ K₁ * t ≤ 1 / 4))
    (hC0 : 0 ≤ C) (hC1 : 64 * K₁ ^ 3 * T₁ ≤ C) (hC2 : T₁ * Real.exp r ≤ C) : T₁ ≤ C * (t ^ 3 + t * s2 + ee) := by
  have hee0 : 0 < ee := by
    rw [hee]
    exact Real.exp_pos _
  have ht3 : 0 ≤ t ^ 3 := by positivity
  have e7 : C * (t ^ 3 + t * s2 + ee) = C * t ^ 3 + C * (t * s2) + C * ee := by ring
  have p1 : 0 ≤ C * t ^ 3 := by positivity
  have p2 : 0 ≤ C * (t * s2) := by positivity
  have p3 : 0 ≤ C * ee := by positivity
  rw [e7]
  by_cases h2 : 2 ≤ ρ
  · have hKt : 1 / 4 < K₁ * t := by
      by_contra h
      exact hmain ⟨h2, not_lt.1 h⟩
    have h64 : 1 ≤ 64 * (K₁ * t) ^ 3 := by
      have : (1 / 4 : ℝ) ^ 3 ≤ (K₁ * t) ^ 3 := pow_le_pow_left₀ (by norm_num) hKt.le 3
      linarith
    have e1 : T₁ ≤ 64 * K₁ ^ 3 * T₁ * t ^ 3 := by
      calc T₁ = T₁ * 1 := by ring
        _ ≤ T₁ * (64 * (K₁ * t) ^ 3) := mul_le_mul_of_nonneg_left h64 hT₁
        _ = _ := by ring
    have e2 : 64 * K₁ ^ 3 * T₁ * t ^ 3 ≤ C * t ^ 3 := mul_le_mul_of_nonneg_right hC1 ht3
    linarith
  · have hρ2 : ρ < 2 := not_le.1 h2
    have e1 : Real.exp (-r) ≤ ee := by
      rw [hee]
      apply Real.exp_le_exp.mpr
      nlinarith
    have e2 : T₁ ≤ T₁ * Real.exp r * ee := by
      have h3 : T₁ * Real.exp r * Real.exp (-r) = T₁ := by
        rw [mul_assoc, ← Real.exp_add]
        simp
      calc T₁ = T₁ * Real.exp r * Real.exp (-r) := h3.symm
        _ ≤ _ := mul_le_mul_of_nonneg_left e1 (by positivity)
    have e3 : T₁ * Real.exp r * ee ≤ C * ee := mul_le_mul_of_nonneg_right hC2 hee0.le
    linarith
end ExpansionProof
theorem curvatureKernelExpansion_of_secondOrder (hT : secondOrderExpansionStatement)
    (hA : axialLogEqCirculationStatement) : curvatureKernelExpansionStatement := by
  intro σ E E₃ r hσ hE hE₃ hr
  obtain ⟨K, hK, hAx⟩ := hA
  have hK0 : 0 < K := by linarith
  obtain ⟨K₁, hK₁⟩ : ∃ K₁, K₁ = K + 16 * K / σ := ⟨_, rfl⟩
  have hK₁0 : 0 < K₁ := by
    rw [hK₁]
    positivity
  have hKK₁ : K ≤ K₁ := by
    have : 0 ≤ 16 * K / σ := by positivity
    linarith
  have hKσ₁ : 16 * K / σ ≤ K₁ := by linarith
  obtain ⟨S2, hS2⟩ : ∃ S2, S2 = bondWeightSum (r / 4) 3 ^ 2 := ⟨_, rfl⟩
  have hS20 : 0 ≤ S2 := by
    rw [hS2]
    positivity
  obtain ⟨Tb, hTb⟩ : ∃ Tb, Tb = ExpansionProof.torusTripleBound r := ⟨_, rfl⟩
  have hTb0 : 0 ≤ Tb := by
    rw [hTb]
    exact ExpansionProof.torusTripleBound_nonneg hr
  obtain ⟨T₁, hT₁⟩ : ∃ T₁, T₁ = E + 24 * E * S2 := ⟨_, rfl⟩
  have hT₁0 : 0 ≤ T₁ := by
    rw [hT₁]
    positivity
  obtain ⟨A₃, hA₃⟩ : ∃ A₃, A₃ = 27 * E₃ * (K ^ 3 * Tb ^ 3) := ⟨_, rfl⟩
  obtain ⟨A₁, hA₁⟩ : ∃ A₁, A₁ = (3 / 2) * (E * S2 * (4 * K + K ^ 2)) := ⟨_, rfl⟩
  obtain ⟨A₂, hA₂⟩ : ∃ A₂, A₂ = E + (3 / 2) * (E * S2 * (32 + 8 * K)) := ⟨_, rfl⟩
  have hA₃0 : 0 ≤ A₃ := by
    rw [hA₃]
    positivity
  have hA₁0 : 0 ≤ A₁ := by
    rw [hA₁]
    positivity
  have hA₂0 : 0 ≤ A₂ := by
    rw [hA₂]
    positivity
  obtain ⟨B₂, hB₂⟩ : ∃ B₂, B₂ = A₂ * Real.exp (3 * r / 2) := ⟨_, rfl⟩
  have hB₂0 : 0 ≤ B₂ := by
    rw [hB₂]
    positivity
  obtain ⟨D, hD⟩ : ∃ D, D = 27 * (2 * K₁ / r) ^ 3 := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by
    rw [hD]
    positivity
  obtain ⟨C₁, hC₁⟩ : ∃ C₁, C₁ = 64 * K₁ ^ 3 * T₁ := ⟨_, rfl⟩
  have hC₁0 : 0 ≤ C₁ := by
    rw [hC₁]
    positivity
  obtain ⟨C₂, hC₂⟩ : ∃ C₂, C₂ = T₁ * Real.exp r := ⟨_, rfl⟩
  have hC₂0 : 0 ≤ C₂ := by
    rw [hC₂]
    positivity
  obtain ⟨C₃, hC₃⟩ : ∃ C₃, C₃ = 16 * E * S2 := ⟨_, rfl⟩
  have hC₃0 : 0 ≤ C₃ := by
    rw [hC₃]
    positivity
  have hBD : 0 ≤ B₂ * D := mul_nonneg hB₂0 hD0
  obtain ⟨C, hC⟩ : ∃ C, C = A₃ + A₁ + (B₂ + B₂ * D) + C₁ + C₂ + C₃ := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by
    rw [hC]
    linarith
  refine ⟨C, r / 2, by positivity, ?_⟩
  intro n _ z w u hn hw hu hcomp
  have hwp : ∀ m, 0 < w m := fun m => (Real.exp_pos _).trans_le (hw m)
  refine ⟨ExpansionProof.curvatureKernel_symm hσ hE₃ hwp hu hT _, ?_, ?_⟩
  · intro p p'
    refine (ExpansionProof.abs_curvatureKernel_le hσ hE hE₃ hr hn hw hu hT p p').trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    rw [← hS2, show 16 * E * S2 = C₃ from hC₃.symm, hC]
    linarith
  · intro W g v ρ s t hW hρ1 hρn hs0 hs1 ht0 ht1 hbox
    by_cases hmain : 2 ≤ ρ ∧ K₁ * t ≤ 1 / 4
    · obtain ⟨h2, hKt⟩ := hmain
      obtain ⟨m, hm1, hm2, hm3⟩ := ExpansionProof.exists_good_radius h2 ht0 hK₁0 hKt hr
      obtain ⟨G, hG⟩ := hAx n z W g v ρ s t hρ1 hρn hs0 hs1 ht0 ht1 hbox
      have hKle : K * (1 + m) * t ≤ K₁ * (1 + m) * t := by gcongr
      have hKσ : K * (1 + m) * t ≤ σ / 16 := by
        have h2' : (16 * K / σ) * ((1 + m) * t) ≤ 1 := by
          calc _ ≤ K₁ * ((1 + m) * t) := by gcongr
            _ ≤ 1 := by rw [← mul_assoc]; exact hm2
        have h3 : (σ / 16) * ((16 * K / σ) * ((1 + m) * t)) = K * (1 + m) * t := by
          field_simp
        rw [← h3]
        have hs16 : 0 < σ / 16 := by positivity
        calc _ ≤ (σ / 16) * 1 := mul_le_mul_of_nonneg_left h2' hs16.le
          _ = _ := by ring
      have hnear := ExpansionProof.expansion_near hσ hE hE₃ hr hK hn hw hu hcomp hT hW hs0 ht0 hbox m hm1 hρn
        (hKle.trans hm2) hKσ hG
      refine hnear.trans ?_
      rw [← hS2, ← hTb, ← hD] at *
      refine ExpansionProof.near_bound_le (S2 := S2) (Tb := Tb) (D := D) (Eb := Real.exp (3 * r / 2))
        (A₃ := A₃) (A₁ := A₁) (A₂ := A₂) (B₂ := B₂) hE hS20 hK0.le ht0 ht1 (by positivity) (Real.exp_pos _).le
        (Real.exp_pos _).le ?_ hA₃ hA₁ hA₂ hB₂ hA₂0 hm3 ?_ ?_ ?_
      · apply Real.exp_le_exp.mpr
        have : 0 ≤ r * (m : ℝ) := by positivity
        linarith
      · rw [hC]
        linarith
      · rw [hC]
        linarith
      · rw [hC]
        linarith
    · have htriv : |u W - u (trivialField n) - (1 / 2) * ∑ p ∈ plaquettesIn (supBall z ρ),
          ∑ p' ∈ plaquettesIn (supBall z ρ), curvatureKernel u z (n / 4) p p' *
            ∑ e : Fin 3, imaginaryComponent e (lieFormCurl v p) * imaginaryComponent e (lieFormCurl v p')| ≤ T₁ := by
        have h1 := ExpansionProof.abs_sub_trivialField_le (E₃ := E₃) hσ hE hn hw hcomp hW
        have h2 := ExpansionProof.abs_kernel_sum_le hσ hE hE₃ hr hn hw hu hT ht0 ht1 hbox
        rw [← hS2] at h2
        refine (abs_sub _ _).trans ?_
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), hT₁]
        linarith
      refine htriv.trans ?_
      refine ExpansionProof.far_bound_le hT₁0 hK₁0 ht0 (by positivity) hr ?_ hmain hC0 ?_ ?_
      · congr 2
      · rw [← hC₁, hC]
        linarith
      · rw [← hC₂, hC]
        linarith
end YangMills.Construction.CurvatureKernel
end
