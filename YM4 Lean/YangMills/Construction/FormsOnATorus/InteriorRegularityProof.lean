import YangMills.Construction.FormsOnATorus.KernelOfTheCurlOnABoxProof
import YangMills.Construction.FormsOnATorus.CurlStepsOnALatticeBox
import YangMills.Construction.FormsOnATorus.FarEntriesOfACube
import YangMills.Construction.LawInAState.HatsSumToTheFreeKernelProof
import YangMills.Construction.LawOnABoxOfTheFlow.FormOfACube
import YangMills.Construction.LawOnABoxOfTheFlow.InteriorRegularity
import YangMills.Construction.LawOnABoxOfTheFlow.LimitFormOfTheCube
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.BoxGaussian
open TorusFields TorusLumps LimitForms ResponseInTheExpansion
open BlockAverages hiding unitStep
private def basisImag (e : Fin 3) : imaginaryQuaternions :=
  ⟨⟨0, if e = 0 then 1 else 0, if e = 1 then 1 else 0, if e = 2 then 1 else 0⟩, rfl⟩
private theorem component_basisImag (e e' : Fin 3) :
    imaginaryComponent e' (basisImag e) = if e' = e then 1 else 0 := by
  fin_cases e <;> fin_cases e' <;> simp [imaginaryComponent, basisImag]
private theorem component_zero (e : Fin 3) : imaginaryComponent e (0 : imaginaryQuaternions) = 0 := by
  fin_cases e <;> simp [imaginaryComponent]
private theorem component_add (e : Fin 3) (a b : imaginaryQuaternions) :
    imaginaryComponent e (a + b) = imaginaryComponent e a + imaginaryComponent e b := by
  fin_cases e <;> simp [imaginaryComponent]
private theorem component_sub (e : Fin 3) (a b : imaginaryQuaternions) :
    imaginaryComponent e (a - b) = imaginaryComponent e a - imaginaryComponent e b := by
  fin_cases e <;> simp [imaginaryComponent]
private theorem norm_sq_eq_sum_components (w : imaginaryQuaternions) :
    ‖w‖ ^ 2 = ∑ e : Fin 3, imaginaryComponent e w ^ 2 := by
  have h0 : (w : ℍ[ℝ]).re = 0 := w.2
  have h1 : ‖w‖ ^ 2 = Quaternion.normSq (w : ℍ[ℝ]) := by
    rw [Quaternion.normSq_eq_norm_mul_self, Submodule.coe_norm, sq]
  rw [h1, Quaternion.normSq_def', h0, Fin.sum_univ_three]
  simp [imaginaryComponent]
abbrev _root_.YangMills.SharedProofs.p8485 := @norm_sq_eq_sum_components
private theorem component_sq_le_norm_sq (e : Fin 3) (w : imaginaryQuaternions) :
    imaginaryComponent e w ^ 2 ≤ ‖w‖ ^ 2 := by
  rw [norm_sq_eq_sum_components]
  exact Finset.single_le_sum (f := fun e => imaginaryComponent e w ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ e)
private theorem abs_component_le_norm (e : Fin 3) (w : imaginaryQuaternions) :
    |imaginaryComponent e w| ≤ ‖w‖ :=
  abs_le_of_sq_le_sq (component_sq_le_norm_sq e w) (norm_nonneg _)
abbrev _root_.YangMills.SharedProofs.p84614 := @abs_component_le_norm
private theorem norm_le_sum_abs_components (w : imaginaryQuaternions) :
    ‖w‖ ≤ ∑ e : Fin 3, |imaginaryComponent e w| := by
  have h0 : 0 ≤ ∑ e : Fin 3, |imaginaryComponent e w| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine abs_le_of_sq_le_sq' ?_ h0 |>.2
  rw [norm_sq_eq_sum_components, Fin.sum_univ_three, Fin.sum_univ_three]
  have a0 := abs_nonneg (imaginaryComponent 0 w)
  have a1 := abs_nonneg (imaginaryComponent 1 w)
  have a2 := abs_nonneg (imaginaryComponent 2 w)
  have b0 := sq_abs (imaginaryComponent 0 w)
  have b1 := sq_abs (imaginaryComponent 1 w)
  have b2 := sq_abs (imaginaryComponent 2 w)
  nlinarith [mul_nonneg a0 a1, mul_nonneg a0 a2, mul_nonneg a1 a2]
private theorem norm_basisImag (e : Fin 3) : ‖basisImag e‖ = 1 := by
  have h := norm_sq_eq_sum_components (basisImag e)
  simp only [component_basisImag] at h
  have h2 : ‖basisImag e‖ ^ 2 = 1 := by
    rw [h]
    simp
  nlinarith [norm_nonneg (basisImag e), sq_nonneg (‖basisImag e‖ - 1), sq_nonneg (‖basisImag e‖ + 1)]
section QuadraticForms
variable {n : ℕ}
private theorem form_apply_single
    (Φ : (TorusBond n → imaginaryQuaternions) → (TorusBond n → imaginaryQuaternions) → ℝ)
    [Fintype (TorusBond n)] [DecidableEq (TorusBond n)]
    (E : TorusBond n → TorusBond n → ℝ)
    (hcol : ∀ u v, Φ u v = ∑ e : Fin 3, ∑ b : TorusBond n, ∑ b' : TorusBond n,
      E b b' * imaginaryComponent e (u b) * imaginaryComponent e (v b'))
    (A : TorusBond n → imaginaryQuaternions) (b₁ : TorusBond n) (e : Fin 3) :
    Φ A (Pi.single b₁ (basisImag e)) = ∑ b : TorusBond n, E b b₁ * imaginaryComponent e (A b) := by
  rw [hcol]
  have inner : ∀ (e' : Fin 3) (b : TorusBond n),
      ∑ b' : TorusBond n, E b b' * imaginaryComponent e' (A b) *
          imaginaryComponent e' ((Pi.single b₁ (basisImag e) : TorusBond n → imaginaryQuaternions) b') =
        E b b₁ * imaginaryComponent e' (A b) * (if e' = e then 1 else 0) := by
    intro e' b
    rw [Finset.sum_eq_single b₁]
    · simp [component_basisImag]
    · intro b' _ hb'
      simp [Pi.single_eq_of_ne hb', component_zero]
    · simp
  simp only [inner]
  rw [Finset.sum_eq_single e]
  · simp
  · intro e' _ he'
    simp [he']
  · simp
private theorem eq_zero_of_quadratic_nonneg {a b : ℝ} (ha : 0 ≤ a)
    (h : ∀ s : ℝ, 0 ≤ 2 * s * b + s ^ 2 * a) : b = 0 := by
  have h1 := h (-(b / (a + 1)))
  have e : 2 * (-(b / (a + 1))) * b + (-(b / (a + 1))) ^ 2 * a = -(b ^ 2 * (a + 2)) / (a + 1) ^ 2 := by
    field_simp
    ring
  rw [e, le_div_iff₀ (by positivity), zero_mul] at h1
  have h3 : b ^ 2 ≤ 0 := by
    by_contra hn
    push Not at hn
    have := mul_pos hn (by linarith : 0 < a + 2)
    linarith
  exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm h3 (sq_nonneg b))
private theorem form_null_vector
    (Φ : (TorusBond n → imaginaryQuaternions) → (TorusBond n → imaginaryQuaternions) → ℝ)
    (hsym : ∀ u v, Φ u v = Φ v u)
    (hlin : ∀ (c : ℝ) (u u' v : TorusBond n → imaginaryQuaternions), Φ (c • u + u') v = c * Φ u v + Φ u' v)
    (hpos : ∀ v, 0 ≤ Φ v v) (N : TorusBond n → imaginaryQuaternions) (hN : Φ N N ≤ 0)
    (η : TorusBond n → imaginaryQuaternions) : Φ N η = 0 := by
  refine eq_zero_of_quadratic_nonneg (hpos η) fun s => ?_
  have h := hpos (s • η + N)
  have a2 : Φ η (s • η + N) = s * Φ η η + Φ N η := by rw [hsym, hlin]
  have a3 : Φ N (s • η + N) = s * Φ η N + Φ N N := by rw [hsym, hlin]
  have e1 : Φ (s • η + N) (s • η + N) = s ^ 2 * Φ η η + 2 * s * Φ N η + Φ N N := by
    rw [hlin, a2, a3, hsym η N]
    ring
  rw [e1] at h
  linarith
private theorem entries_symm_of_form
    (Φ : (TorusBond n → imaginaryQuaternions) → (TorusBond n → imaginaryQuaternions) → ℝ)
    [Fintype (TorusBond n)] [DecidableEq (TorusBond n)]
    (E : TorusBond n → TorusBond n → ℝ) (hsym : ∀ u v, Φ u v = Φ v u)
    (hcol : ∀ u v, Φ u v = ∑ e : Fin 3, ∑ b : TorusBond n, ∑ b' : TorusBond n,
      E b b' * imaginaryComponent e (u b) * imaginaryComponent e (v b'))
    (b₀ b₁ : TorusBond n) : E b₀ b₁ = E b₁ b₀ := by
  have key : ∀ b b', Φ (Pi.single b (basisImag 0)) (Pi.single b' (basisImag 0)) = E b b' := by
    intro b b'
    rw [form_apply_single Φ E hcol, Finset.sum_eq_single b]
    · simp [component_basisImag]
    · intro b'' _ h
      simp [Pi.single_eq_of_ne h, component_zero]
    · simp
  rw [← key, ← key, hsym]
end QuadraticForms
section Torus
variable {n : ℕ} [NeZero n]
private theorem valMinAbs_intCast_of_small {z : ℤ} (hz : 2 * |z| < n) : ((z : ZMod n)).valMinAbs = z := by apply _root_.YangMills.SharedProofs.p9640 <;> assumption
private theorem siteOfInt_add_single (z : Fin 4 → ℤ) (i : Fin 4) :
    (siteOfInt (z + Pi.single i 1) : TorusSite n) = siteOfInt z + unitStep n i := by
  funext k
  simp only [siteOfInt, unitStep, Pi.add_apply, Pi.single_apply]
  split_ifs <;> simp
abbrev _root_.YangMills.DeltaSharedProofs.p500445 := @siteOfInt_add_single
abbrev _root_.YangMills.SharedProofs.p5434 := @siteOfInt_add_single
private def offsetFrom (o x : TorusSite n) : Fin 4 → ℤ := fun i => (x i - o i).valMinAbs
private theorem add_siteOfInt_offsetFrom (o x : TorusSite n) : o + siteOfInt (offsetFrom o x) = x := by apply _root_.YangMills.DeltaSharedProofs.p500399 <;> assumption
private theorem offsetFrom_add_siteOfInt {z : Fin 4 → ℤ} (hz : ∀ i, 2 * |z i| < n) (o : TorusSite n) :
    offsetFrom o (o + siteOfInt z) = z := by
  funext i
  simp [offsetFrom, siteOfInt, valMinAbs_intCast_of_small (hz i)]
private theorem supDist_le_iff_offsetInBox (o x : TorusSite n) (r : ℕ) :
    supDist x o ≤ r ↔ OffsetInBox r (offsetFrom o x) := by
  simp only [supDist, Finset.sup_le_iff, Finset.mem_univ, true_implies, OffsetInBox, offsetFrom]
  refine forall_congr' fun i => ?_
  rw [Int.abs_eq_natAbs]
  omega
private theorem mem_supBall_natCast_iff (o x : TorusSite n) (r : ℕ) :
    x ∈ supBall o (r : ℝ) ↔ OffsetInBox r (offsetFrom o x) := by
  rw [← supDist_le_iff_offsetInBox]
  simp [supBall]
abbrev _root_.YangMills.DeltaSharedProofs.p501389 := @mem_supBall_natCast_iff
private theorem mem_supBall_two_mul_iff (o x : TorusSite n) (R : ℕ) :
    x ∈ supBall o (2 * (R : ℝ)) ↔ OffsetInBox (2 * R) (offsetFrom o x) := by
  rw [← mem_supBall_natCast_iff]
  push_cast
  rfl
private theorem offsetInBox_add_single {r : ℕ} {z : Fin 4 → ℤ} (h : OffsetInBox r z) (i : Fin 4) :
    OffsetInBox (r + 1) (z + Pi.single i 1) := by
  intro k
  have := h k
  simp only [Pi.add_apply, Pi.single_apply]
  rw [abs_le] at this ⊢
  push_cast
  split_ifs <;> omega
private theorem offsetInBox_mono {r s : ℕ} {z : Fin 4 → ℤ} (h : OffsetInBox r z) (hrs : r ≤ s) :
    OffsetInBox s z := fun k =>
  (h k).trans (by exact_mod_cast hrs)
private theorem offsetInBox_small {r : ℕ} {z : Fin 4 → ℤ} (h : OffsetInBox r z) (hr : 2 * r < n) :
    ∀ i, 2 * |z i| < n := by
  intro i
  have := h i
  omega
private theorem bondOffsetInBox_of_offsetInBox {r : ℕ} {b : IntBond} (h : OffsetInBox r b.1) :
    BondOffsetInBox (r + 1) b :=
  ⟨offsetInBox_mono h (by omega), offsetInBox_add_single h b.2⟩
open Classical in
private def doubleCubeBonds (R : ℕ) : Finset IntBond :=
  (bondCube (2 * R)).filter fun b => BondOffsetInBox (2 * R) b
private theorem mem_siteCube_iff {r : ℕ} {x : Fin 4 → ℤ} : x ∈ siteCube r ↔ OffsetInBox r x := by
  simp [siteCube, Fintype.mem_piFinset, abs_le, OffsetInBox]
open Classical in
private theorem mem_doubleCubeBonds {R : ℕ} {b : IntBond} :
    b ∈ doubleCubeBonds R ↔ BondOffsetInBox (2 * R) b := by
  simp only [doubleCubeBonds, Finset.mem_filter, and_iff_right_iff_imp]
  intro h
  exact Finset.mem_product.2 ⟨mem_siteCube_iff.2 h.1, Finset.mem_univ _⟩
open Classical in
private theorem card_doubleCubeBonds_le (R : ℕ) : ((doubleCubeBonds R).card : ℝ) ≤ bondCubeCard (2 * R) := by
  have h : (Finset.Icc (-((2 * R : ℕ) : ℤ)) ((2 * R : ℕ) : ℤ)).card = 2 * (2 * R) + 1 := by
    rw [Int.card_Icc]; omega
  have h1 : ((bondCube (2 * R)).card : ℝ) = bondCubeCard (2 * R) := by
    simp only [bondCube, siteCube, Finset.card_product, Fintype.card_piFinset, h, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, bondCubeCard]
    push_cast
    ring
  rw [← h1]
  have h2 : (doubleCubeBonds R).card ≤ (bondCube (2 * R)).card :=
    Finset.card_le_card fun b hb => by
      unfold doubleCubeBonds at hb
      exact (Finset.mem_filter.1 hb).1
  exact_mod_cast h2
private theorem mem_bondsWithin_iff {S : Finset (TorusSite n)} {b : TorusBond n} :
    b ∈ bondsWithin S ↔ b.1 ∈ S ∧ b.1 + unitStep n b.2 ∈ S := by
  simp [bondsWithin]
private theorem bondFrom_mem_bondsWithin (o : TorusSite n) {R : ℕ} (hR : 1 ≤ R) (hn : 16 * R < n) {b : IntBond}
    (hb : b ∈ doubleCubeBonds R) : bondFrom o b ∈ bondsWithin (supBall o (2 * (R : ℝ))) := by
  obtain ⟨h1, h2⟩ := mem_doubleCubeBonds.1 hb
  refine mem_bondsWithin_iff.2 ⟨?_, ?_⟩
  · rw [mem_supBall_two_mul_iff]
    simp only [bondFrom]
    rw [offsetFrom_add_siteOfInt (offsetInBox_small h1 (by omega))]
    exact h1
  · rw [mem_supBall_two_mul_iff]
    simp only [bondFrom]
    rw [add_assoc, ← siteOfInt_add_single, offsetFrom_add_siteOfInt (offsetInBox_small h2 (by omega))]
    exact h2
private theorem sum_bondsWithin_eq_sum_doubleCube (o : TorusSite n) {R : ℕ} (hR : 1 ≤ R) (hn : 16 * R < n)
    (f : TorusBond n → ℝ) :
    ∑ b ∈ bondsWithin (supBall o (2 * (R : ℝ))), f b = ∑ b ∈ doubleCubeBonds R, f (bondFrom o b) := by
  have hsmall : 2 * (2 * R + 1) < n := by omega
  refine Finset.sum_nbij' (fun b => (offsetFrom o b.1, b.2)) (bondFrom o) ?_ ?_ ?_ ?_ ?_
  · intro b hb
    obtain ⟨h1, h2⟩ := mem_bondsWithin_iff.1 hb
    rw [mem_supBall_two_mul_iff] at h1 h2
    refine mem_doubleCubeBonds.2 ⟨h1, ?_⟩
    have e : offsetFrom o (b.1 + unitStep n b.2) = offsetFrom o b.1 + Pi.single b.2 1 := by
      have h3 := add_siteOfInt_offsetFrom o b.1
      have : b.1 + unitStep n b.2 = o + siteOfInt (offsetFrom o b.1 + Pi.single b.2 1) := by
        rw [siteOfInt_add_single, ← add_assoc, h3]
      rw [this, offsetFrom_add_siteOfInt (offsetInBox_small (offsetInBox_add_single h1 b.2) hsmall)]
    rw [e] at h2
    exact h2
  · exact fun b hb => bondFrom_mem_bondsWithin o hR hn hb
  · intro b _
    exact Prod.ext (add_siteOfInt_offsetFrom o b.1) rfl
  · intro b hb
    obtain ⟨h1, _⟩ := mem_doubleCubeBonds.1 hb
    exact Prod.ext (offsetFrom_add_siteOfInt (offsetInBox_small h1 (by omega)) o) rfl
  · intro b _
    have : bondFrom o (offsetFrom o b.1, b.2) = b := Prod.ext (add_siteOfInt_offsetFrom o b.1) rfl
    rw [this]
private theorem plaquette_bonds_mem {S : Finset (TorusSite n)} {p : TorusPlaquette n} (hp : p ∈ plaquettesIn S) :
    (p.1, p.2.1) ∈ bondsWithin S ∧ (p.1 + unitStep n p.2.1, p.2.2) ∈ bondsWithin S ∧
      (p.1 + unitStep n p.2.2, p.2.1) ∈ bondsWithin S ∧ (p.1, p.2.2) ∈ bondsWithin S := by
  have h := (Finset.mem_filter.1 hp).2.2
  simp only [plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  have h3' : p.1 + unitStep n p.2.2 + unitStep n p.2.1 ∈ S := by rwa [add_right_comm]
  exact ⟨mem_bondsWithin_iff.2 ⟨h0, h1⟩, mem_bondsWithin_iff.2 ⟨h1, h3⟩, mem_bondsWithin_iff.2 ⟨h2, h3'⟩,
    mem_bondsWithin_iff.2 ⟨h0, h2⟩⟩
abbrev _root_.YangMills.SharedProofs.p50589 := @plaquette_bonds_mem
end Torus
private theorem poly_mul_exp_le_exp_half (A μ : ℝ) (hμ : 0 < μ) (p : ℕ) : ∃ R₁ : ℕ, ∀ R : ℕ, R₁ ≤ R →
    A * (R : ℝ) ^ p * Real.exp (-(μ * R)) ≤ Real.exp (-(μ / 2 * R)) := by
  have hb : 0 < μ / 2 := by positivity
  have h1 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero p
  have h2 : Filter.Tendsto (fun R : ℕ => μ / 2 * (R : ℝ)) Filter.atTop Filter.atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hb
  have h3 := h1.comp h2
  have hpos : 0 < (μ / 2) ^ p / (|A| + 1) := by positivity
  have h4 := (h3.eventually (gt_mem_nhds hpos))
  obtain ⟨R₁, hR₁⟩ := Filter.eventually_atTop.1 h4
  refine ⟨R₁, fun R hR => ?_⟩
  have h5 := hR₁ R hR
  simp only [Function.comp] at h5
  rw [mul_pow] at h5
  have hE : Real.exp (-(μ * R)) = Real.exp (-(μ / 2 * R)) * Real.exp (-(μ / 2 * R)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hp : 0 < (μ / 2) ^ p := by positivity
  have hA1 : 0 < |A| + 1 := by positivity
  have h6 : (R : ℝ) ^ p * Real.exp (-(μ / 2 * R)) < 1 / (|A| + 1) := by
    have e : (μ / 2) ^ p * (R : ℝ) ^ p * Real.exp (-(μ / 2 * R)) =
        (μ / 2) ^ p * ((R : ℝ) ^ p * Real.exp (-(μ / 2 * R))) := by ring
    have e2 : (μ / 2) ^ p / (|A| + 1) = (μ / 2) ^ p * (1 / (|A| + 1)) := by ring
    rw [e, e2] at h5
    exact lt_of_mul_lt_mul_left h5 hp.le
  have h7 : A * ((R : ℝ) ^ p * Real.exp (-(μ / 2 * R))) ≤ 1 := by
    have h8 : 0 ≤ (R : ℝ) ^ p * Real.exp (-(μ / 2 * R)) := by positivity
    calc A * ((R : ℝ) ^ p * Real.exp (-(μ / 2 * R))) ≤ |A| * ((R : ℝ) ^ p * Real.exp (-(μ / 2 * R))) :=
          mul_le_mul_of_nonneg_right (le_abs_self A) h8
      _ ≤ (|A| + 1) * (1 / (|A| + 1)) := by
          refine mul_le_mul (by linarith) h6.le h8 hA1.le
      _ = 1 := by field_simp
  have hEp := Real.exp_pos (-(μ / 2 * R))
  calc A * (R : ℝ) ^ p * Real.exp (-(μ * R))
      = (A * ((R : ℝ) ^ p * Real.exp (-(μ / 2 * R)))) * Real.exp (-(μ / 2 * R)) := by rw [hE]; ring
    _ ≤ 1 * Real.exp (-(μ / 2 * R)) := mul_le_mul_of_nonneg_right h7 hEp.le
    _ = _ := one_mul _
private theorem bondCubeCard_le {r : ℕ} {x : ℝ} (hx : 2 * (r : ℝ) + 1 ≤ 5 * x) :
    bondCubeCard r ≤ 2500 * x ^ 4 := by
  unfold bondCubeCard
  calc 4 * (2 * (r : ℝ) + 1) ^ 4 ≤ 4 * (5 * x) ^ 4 := by gcongr
    _ = 2500 * x ^ 4 := by ring
private theorem energyStepError_small (c c₁ c₂ C₁ cK κ Cp : ℝ) (hc : 0 < c) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hC₁ : 0 ≤ C₁) (hcK : 0 < cK) (hκ : 0 < κ) (j : ℕ) : ∃ (μ : ℝ) (R₁ : ℕ), 0 < μ ∧ ∀ (R t : ℕ), R₁ ≤ R → t ≤ R →
      (R : ℝ) ≤ 16 * (j + 5) * t →
      3 * κ * ((t : ℝ) ^ 2 * Real.sqrt (energyStepError c₁ C₁ (2 * R) (R - 2) (j + 4) t ((R : ℝ) ^ Cp)
        (Real.exp (-(c * R)) + bondCubeCard (2 * R) * ((R : ℝ) ^ Cp *
          (Real.exp (-(c₁ * R)) + C₁ * Real.exp (-(c₁ * ((R : ℝ) / 4))) + Real.exp (-(c₂ * R))))) / (2 * cK))) ≤
        Real.exp (-(μ * R)) := by
  set u : ℝ := 16 * ((j : ℝ) + 5) with hu
  have hu0 : 0 < u := by positivity
  set μ : ℝ := min (min c (c₁ / 4)) (min c₂ (c₁ / u)) with hμ
  have hμ0 : 0 < μ := lt_min (lt_min hc (by positivity)) (lt_min hc₂ (by positivity))
  have hμc : μ ≤ c := (min_le_left _ _).trans (min_le_left _ _)
  have hμ1 : μ ≤ c₁ / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hμ2 : μ ≤ c₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hμ3 : μ ≤ c₁ / u := (min_le_right _ _).trans (min_le_right _ _)
  set a : ℕ := ⌈|Cp|⌉₊ with ha
  set M : ℕ := j + 4 with hM
  set A₁ : ℝ := 1 + 2500 * (2 + C₁) with hA₁
  set A₂ : ℝ := 2500 * 8 ^ M * A₁ + 2500 ^ 2 * 16 ^ M * C₁ with hA₂
  set A₃ : ℝ := 9 * κ ^ 2 * A₂ / (2 * cK) with hA₃
  obtain ⟨R₂, hR₂⟩ := poly_mul_exp_le_exp_half A₃ μ hμ0 (2 * a + 12)
  refine ⟨μ / 4, max (max R₂ 1) (2 * j + 9), by positivity, fun R t hR htR hRt => ?_⟩
  have hRR₂ : R₂ ≤ R := (le_max_left _ _).trans ((le_max_left _ _).trans hR)
  have hR1 : 1 ≤ R := (le_max_right _ _).trans ((le_max_left _ _).trans hR)
  have hRj : 2 * j + 9 ≤ R := (le_max_right _ _).trans hR
  set x : ℝ := (R : ℝ) with hx
  have hx1 : 1 ≤ x := by rw [hx]; exact_mod_cast hR1
  have hx0 : 0 < x := by linarith
  have hxj : 2 * (j : ℝ) + 9 ≤ x := by rw [hx]; exact_mod_cast hRj
  have ht0 : (0 : ℝ) ≤ t := by positivity
  have htx : (t : ℝ) ≤ x := by rw [hx]; exact_mod_cast htR
  set e : ℝ := Real.exp (-(μ * x)) with he
  have he0 : 0 < e := Real.exp_pos _
  have expc : ∀ s : ℝ, μ * x ≤ s → Real.exp (-s) ≤ e := fun s hs => Real.exp_le_exp.2 (by linarith)
  set W : ℝ := x ^ Cp with hW
  have hWa : W ≤ x ^ a := by
    have : Cp ≤ (a : ℝ) := (le_abs_self Cp).trans (Nat.le_ceil _)
    calc W ≤ x ^ (a : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 this
      _ = x ^ a := Real.rpow_natCast _ _
  have hc1 : bondCubeCard (2 * R) ≤ 2500 * x ^ 4 := bondCubeCard_le (by push_cast; linarith)
  have hc2 : bondCubeCard (R - 2) ≤ 2500 * x ^ 4 := bondCubeCard_le (by
    have : ((R - 2 : ℕ) : ℝ) ≤ x := by rw [hx]; exact_mod_cast Nat.sub_le _ _
    linarith)
  have hc3 : bondCubeCard (2 * R + M) ≤ 2500 * x ^ 4 := bondCubeCard_le (by
    simp only [hM]; push_cast; linarith)
  have hc10 : 0 ≤ bondCubeCard (2 * R) := by unfold bondCubeCard; positivity
  have hc20 : 0 ≤ bondCubeCard (R - 2) := by unfold bondCubeCard; positivity
  have hc30 : 0 ≤ bondCubeCard (2 * R + M) := by unfold bondCubeCard; positivity
  have hd : Real.exp (-(c₁ * x)) + C₁ * Real.exp (-(c₁ * (x / 4))) + Real.exp (-(c₂ * x)) ≤ (2 + C₁) * e := by
    have e1 := expc (c₁ * x) (by
      have : μ ≤ c₁ := hμ1.trans (by linarith)
      exact mul_le_mul_of_nonneg_right this hx0.le)
    have e2 := expc (c₁ * (x / 4)) (by
      have := mul_le_mul_of_nonneg_right hμ1 hx0.le
      linarith)
    have e3 := expc (c₂ * x) (mul_le_mul_of_nonneg_right hμ2 hx0.le)
    have := mul_le_mul_of_nonneg_left e2 hC₁
    linarith
  set ε : ℝ := Real.exp (-(c * x)) + bondCubeCard (2 * R) * (W *
      (Real.exp (-(c₁ * x)) + C₁ * Real.exp (-(c₁ * (x / 4))) + Real.exp (-(c₂ * x)))) with hε
  have hεb : ε ≤ A₁ * x ^ (a + 4) * e := by
    have e1 := expc (c * x) (mul_le_mul_of_nonneg_right hμc hx0.le)
    have e2 : bondCubeCard (2 * R) * (W * (Real.exp (-(c₁ * x)) + C₁ * Real.exp (-(c₁ * (x / 4))) +
        Real.exp (-(c₂ * x)))) ≤ (2500 * x ^ 4) * (x ^ a * ((2 + C₁) * e)) := by gcongr
    have e3 : e ≤ x ^ (a + 4) * e := le_mul_of_one_le_left he0.le (one_le_pow₀ hx1)
    have e4 : (2500 * x ^ 4) * (x ^ a * ((2 + C₁) * e)) = 2500 * (2 + C₁) * (x ^ (a + 4) * e) := by
      rw [pow_add]; ring
    simp only [hε, hA₁]
    nlinarith
  have hct : Real.exp (-(c₁ * t)) ≤ e := expc _ (by
    have h1 : μ * u ≤ c₁ := by
      have := mul_le_mul_of_nonneg_right hμ3 hu0.le
      rwa [div_mul_cancel₀ _ hu0.ne'] at this
    have h2 : x ≤ u * t := by simpa [hu] using hRt
    calc μ * x ≤ μ * (u * t) := mul_le_mul_of_nonneg_left h2 hμ0.le
      _ = (μ * u) * t := by ring
      _ ≤ c₁ * t := mul_le_mul_of_nonneg_right h1 ht0)
  have herr : energyStepError c₁ C₁ (2 * R) (R - 2) M t W ε ≤ A₂ * x ^ (2 * a + 8) * e := by
    unfold energyStepError
    have e1 : bondCubeCard (R - 2) * ((4 ^ M * W) * (2 ^ M * ε)) ≤
        (2500 * x ^ 4) * ((4 ^ M * x ^ a) * (2 ^ M * (A₁ * x ^ (a + 4) * e))) := by
      have : 0 ≤ A₁ := by positivity
      gcongr
    have e2 : bondCubeCard (R - 2) * (bondCubeCard (2 * R + M) *
        ((4 ^ M * W) ^ 2 * (C₁ * Real.exp (-(c₁ * t))))) ≤
        (2500 * x ^ 4) * ((2500 * x ^ 4) * ((4 ^ M * x ^ a) ^ 2 * (C₁ * e))) := by gcongr
    have e3 : (2500 * x ^ 4) * ((4 ^ M * x ^ a) * (2 ^ M * (A₁ * x ^ (a + 4) * e))) =
        2500 * 8 ^ M * A₁ * x ^ (2 * a + 8) * e := by
      have : (8 : ℝ) ^ M = 4 ^ M * 2 ^ M := by rw [← mul_pow]; norm_num
      rw [this, pow_add, show 2 * a + 8 = a + a + 4 + 4 by ring, pow_add, pow_add, pow_add]
      ring
    have e4 : (2500 * x ^ 4) * ((2500 * x ^ 4) * ((4 ^ M * x ^ a) ^ 2 * (C₁ * e))) ≤
        2500 ^ 2 * 16 ^ M * C₁ * x ^ (2 * a + 8) * e := by
      have : (16 : ℝ) ^ M = (4 ^ M) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [this, show 2 * a + 8 = a + a + 4 + 4 by ring, pow_add, pow_add, pow_add]
      apply le_of_eq
      ring
    have e5 : A₂ * x ^ (2 * a + 8) * e = 2500 * 8 ^ M * A₁ * x ^ (2 * a + 8) * e +
        2500 ^ 2 * 16 ^ M * C₁ * x ^ (2 * a + 8) * e := by
      simp only [hA₂]; ring
    linarith
  have herr0 : 0 ≤ energyStepError c₁ C₁ (2 * R) (R - 2) M t W ε := by
    unfold energyStepError
    positivity
  set Er : ℝ := energyStepError c₁ C₁ (2 * R) (R - 2) M t W ε / (2 * cK) with hEr
  have hfin := hR₂ R hRR₂
  have hY : (3 * κ * (t : ℝ) ^ 2) ^ 2 * Er ≤ Real.exp (-(μ / 2 * x)) := by
    refine le_trans ?_ hfin
    have h1 : (3 * κ * (t : ℝ) ^ 2) ^ 2 ≤ 9 * κ ^ 2 * x ^ 4 := by
      have : (t : ℝ) ^ 2 ≤ x ^ 2 := by gcongr
      calc (3 * κ * (t : ℝ) ^ 2) ^ 2 ≤ (3 * κ * x ^ 2) ^ 2 := by gcongr
        _ = 9 * κ ^ 2 * x ^ 4 := by ring
    have h2 : Er ≤ A₂ * x ^ (2 * a + 8) * e / (2 * cK) := by
      simp only [hEr]
      gcongr
    calc (3 * κ * (t : ℝ) ^ 2) ^ 2 * Er ≤ (9 * κ ^ 2 * x ^ 4) * (A₂ * x ^ (2 * a + 8) * e / (2 * cK)) := by
          have : 0 ≤ A₂ := by positivity
          gcongr
      _ = A₃ * x ^ (2 * a + 12) * e := by
          simp only [hA₃]
          rw [show 2 * a + 12 = 2 * a + 8 + 4 by ring, pow_add]
          ring
  have hroot : 3 * κ * ((t : ℝ) ^ 2 * Real.sqrt Er) = Real.sqrt ((3 * κ * (t : ℝ) ^ 2) ^ 2 * Er) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    ring
  rw [hroot]
  have hE2 : Real.exp (-(μ / 4 * x)) ^ 2 = Real.exp (-(μ / 2 * x)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  refine Real.sqrt_le_iff.2 ⟨(Real.exp_pos _).le, ?_⟩
  rw [hE2]
  exact hY
section LatticeForm
variable {n : ℕ} [NeZero n]
open Classical in
private def componentField (A : TorusBond n → imaginaryQuaternions) (o : TorusSite n) (R : ℕ) (e : Fin 3) :
    IntBond → ℝ :=
  fun b => if BondOffsetInBox (2 * R) b then imaginaryComponent e (A (bondFrom o b)) else 0
open Classical in
private theorem hessianForm_single_eq_sum {a : ℝ} {L k : ℕ} {S : Finset (TorusSite n)} {cK CQ : ℝ} (hcK : 0 < cK)
    (hsym : ∀ u v, hessianForm a L k S u v = hessianForm a L k S v u)
    (hlin : ∀ (c : ℝ) (u u' v : TorusBond n → imaginaryQuaternions),
      hessianForm a L k S (c • u + u') v = c * hessianForm a L k S u v + hessianForm a L k S u' v)
    (hbd : ∀ v, 2 * cK * curlNormSq S v ≤ hessianForm a L k S v v ∧ hessianForm a L k S v v ≤ CQ * curlNormSq S v)
    (hcol : ∀ u v : TorusBond n → imaginaryQuaternions, hessianForm a L k S u v =
      ∑ e : Fin 3, ∑ b : TorusBond n, ∑ b' : TorusBond n,
        mixedDeriv (actionAtLevel a L k S) (trivialField n) ![b, b'] ![imaginaryUnitI, imaginaryUnitI] *
          imaginaryComponent e (u b) * imaginaryComponent e (v b'))
    (A : TorusBond n → imaginaryQuaternions) (e : Fin 3) (b₁ : TorusBond n) :
    hessianForm a L k S A (Pi.single b₁ (basisImag e)) = ∑ b ∈ bondsWithin S,
      mixedDeriv (actionAtLevel a L k S) (trivialField n) ![b, b₁] ![imaginaryUnitI, imaginaryUnitI] *
        imaginaryComponent e (A b) := by
  have hA' : ∃ A' : TorusBond n → imaginaryQuaternions, (∀ b ∈ bondsWithin S, A' b = A b) ∧
      ∀ b, b ∉ bondsWithin S → A' b = 0 :=
    ⟨fun b => if b ∈ bondsWithin S then A b else 0, fun b hb => by simp [hb], fun b hb => by simp [hb]⟩
  obtain ⟨A', h1, h2⟩ := hA'
  have hNb : ∀ b ∈ bondsWithin S, (A - A') b = 0 := fun b hb => by simp [h1 b hb]
  have hcurl : curlNormSq S (A - A') = 0 := by
    refine Finset.sum_eq_zero fun p hp => ?_
    obtain ⟨g1, g2, g3, g4⟩ := plaquette_bonds_mem hp
    simp [lieFormCurl, hNb _ g1, hNb _ g2, hNb _ g3, hNb _ g4]
  have hN : hessianForm a L k S (A - A') (A - A') ≤ 0 := by
    have := (hbd (A - A')).2
    rwa [hcurl, mul_zero] at this
  have hpos : ∀ v, 0 ≤ hessianForm a L k S v v := fun v =>
    le_trans (mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)) (hbd v).1
  have hnull := form_null_vector (hessianForm a L k S) hsym hlin hpos (A - A') hN (Pi.single b₁ (basisImag e))
  have hA : A = (1 : ℝ) • (A - A') + A' := by
    funext b
    simp
  have e1 : hessianForm a L k S A (Pi.single b₁ (basisImag e)) =
      hessianForm a L k S A' (Pi.single b₁ (basisImag e)) := by
    have := hlin 1 (A - A') A' (Pi.single b₁ (basisImag e))
    rw [← hA, hnull, mul_zero, zero_add] at this
    exact this
  rw [e1, form_apply_single (hessianForm a L k S)
    (fun b b' => mixedDeriv (actionAtLevel a L k S) (trivialField n) ![b, b'] ![imaginaryUnitI, imaginaryUnitI])
    hcol A' b₁ e]
  symm
  have e2 : ∑ b ∈ bondsWithin S, mixedDeriv (actionAtLevel a L k S) (trivialField n) ![b, b₁]
        ![imaginaryUnitI, imaginaryUnitI] * imaginaryComponent e (A b) =
      ∑ b ∈ bondsWithin S, mixedDeriv (actionAtLevel a L k S) (trivialField n) ![b, b₁]
        ![imaginaryUnitI, imaginaryUnitI] * imaginaryComponent e (A' b) :=
    Finset.sum_congr rfl fun b hb => by rw [h1 b hb]
  rw [e2]
  refine Finset.sum_subset (Finset.subset_univ _) fun b _ hb => ?_
  rw [h2 b hb, component_zero, mul_zero]
private theorem le_four_mul_bondSupDist {R : ℕ} (hR : 4 ≤ R) {b b' : IntBond} (hb' : b' ∈ bondCube (R - 2))
    (hn : ¬ BondOffsetInBox (3 * R / 2) b) : R ≤ 4 * bondSupDist b b' := by
  by_contra h
  push Not at h
  apply hn
  have hd : ∀ i, (b.1 i - b'.1 i).natAbs ≤ bondSupDist b b' := fun i =>
    Finset.le_sup (f := fun i => (b.1 i - b'.1 i).natAbs) (Finset.mem_univ i)
  have hb1 : OffsetInBox (R - 2) b'.1 := mem_siteCube_iff.1 (Finset.mem_product.1 hb').1
  have key : ∀ i, |b.1 i| + 1 ≤ ((3 * R / 2 : ℕ) : ℤ) := by
    intro i
    have h1 := hd i
    have h2 := hb1 i
    rw [Int.abs_eq_natAbs] at h2 ⊢
    omega
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have := key i
    omega
  · have := key i
    simp only [Pi.add_apply, Pi.single_apply]
    rw [abs_le]
    have h3 := abs_le.1 (le_refl |b.1 i|)
    split_ifs <;> omega
private theorem kernelResidual_bound {Q : IntBond → IntBond → ℝ} {E : TorusBond n → TorusBond n → ℝ}
    {o : TorusSite n} {R : ℕ} {c c₁ c₂ C₁ W : ℝ} (hR : 4 ≤ R) (hn : 16 * R < n) (hc₁ : 0 < c₁)
    (hdecay : ∀ b b', |Q b b'| ≤ C₁ * Real.exp (-(c₁ * bondSupDist b b')))
    (hnear : ∀ b b' : IntBond, BondOffsetInBox (3 * R / 2) b → BondOffsetInBox (3 * R / 2) b' →
      |E (bondFrom o b) (bondFrom o b') - Q b b'| ≤ Real.exp (-(c₁ * R)))
    (hfar : ∀ b b' : IntBond, BondOffsetInBox (2 * R) b → BondOffsetInBox (2 * R) b' →
      R ≤ 4 * bondSupDist b b' → |E (bondFrom o b) (bondFrom o b')| ≤ Real.exp (-(c₂ * R)))
    (A : TorusBond n → imaginaryQuaternions) (hA : ∀ b ∈ bondsWithin (supBall o (2 * (R : ℝ))), ‖A b‖ ≤ W)
    (hW0 : 0 ≤ W) (hC₁ : 0 ≤ C₁)
    (e : Fin 3) (b' : IntBond) (hb' : b' ∈ bondCube (R - 2))
    (hin : |∑ b ∈ bondsWithin (supBall o (2 * (R : ℝ))), E b (bondFrom o b') * imaginaryComponent e (A b)| ≤
      Real.exp (-(c * R))) :
    |kernelResidual Q (componentField A o R e) b'| ≤ Real.exp (-(c * R)) + bondCubeCard (2 * R) * (W *
      (Real.exp (-(c₁ * R)) + C₁ * Real.exp (-(c₁ * ((R : ℝ) / 4))) + Real.exp (-(c₂ * R)))) := by
  have hR1 : 1 ≤ R := by omega
  have hsum := sum_bondsWithin_eq_sum_doubleCube o hR1 hn
    (fun b => E b (bondFrom o b') * imaginaryComponent e (A b))
  rw [hsum] at hin
  set δ : ℝ := Real.exp (-(c₁ * R)) + C₁ * Real.exp (-(c₁ * ((R : ℝ) / 4))) + Real.exp (-(c₂ * R)) with hδ
  have hres : kernelResidual Q (componentField A o R e) b' =
      ∑ b ∈ doubleCubeBonds R, componentField A o R e b * Q b b' := by
    refine finsum_eq_sum_of_support_subset _ ?_
    intro b hb
    by_contra hnot
    have : ¬ BondOffsetInBox (2 * R) b := fun h => hnot (by simpa using mem_doubleCubeBonds.2 h)
    exact hb (by simp [componentField, this])
  have hb'3 : BondOffsetInBox (3 * R / 2) b' := by
    have h0 : OffsetInBox (R - 2) b'.1 := mem_siteCube_iff.1 (Finset.mem_product.1 hb').1
    obtain ⟨g1, g2⟩ := bondOffsetInBox_of_offsetInBox h0
    exact ⟨offsetInBox_mono g1 (by omega), offsetInBox_mono g2 (by omega)⟩
  have hb'2 : BondOffsetInBox (2 * R) b' :=
    ⟨offsetInBox_mono hb'3.1 (by omega), offsetInBox_mono hb'3.2 (by omega)⟩
  have hdiff : ∀ b ∈ doubleCubeBonds R, |Q b b' - E (bondFrom o b) (bondFrom o b')| ≤ δ := by
    intro b hb
    have hbc := mem_doubleCubeBonds.1 hb
    have p1 := Real.exp_pos (-(c₁ * (R : ℝ)))
    have p3 := Real.exp_pos (-(c₂ * (R : ℝ)))
    have p4 : 0 ≤ C₁ * Real.exp (-(c₁ * ((R : ℝ) / 4))) := by positivity
    by_cases hnr : BondOffsetInBox (3 * R / 2) b
    · have := hnear b b' hnr hb'3
      rw [abs_sub_comm]
      simp only [hδ]
      linarith
    · have hfr := le_four_mul_bondSupDist hR hb' hnr
      have h1 := hfar b b' hbc hb'2 hfr
      have h2 := hdecay b b'
      have h3 : Real.exp (-(c₁ * bondSupDist b b')) ≤ Real.exp (-(c₁ * ((R : ℝ) / 4))) := by
        refine Real.exp_le_exp.2 ?_
        have : (R : ℝ) ≤ 4 * bondSupDist b b' := by exact_mod_cast hfr
        nlinarith
      have h4 := mul_le_mul_of_nonneg_left h3 hC₁
      have h5 := abs_sub (Q b b') (E (bondFrom o b) (bondFrom o b'))
      simp only [hδ]
      linarith
  have hT : ∑ b ∈ doubleCubeBonds R, componentField A o R e b * Q b b' =
      ∑ b ∈ doubleCubeBonds R, E (bondFrom o b) (bondFrom o b') * imaginaryComponent e (A (bondFrom o b)) +
      ∑ b ∈ doubleCubeBonds R, imaginaryComponent e (A (bondFrom o b)) *
        (Q b b' - E (bondFrom o b) (bondFrom o b')) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b hb => ?_
    have : componentField A o R e b = imaginaryComponent e (A (bondFrom o b)) := by
      simp [componentField, mem_doubleCubeBonds.1 hb]
    rw [this]
    ring
  have hsmall : |∑ b ∈ doubleCubeBonds R, imaginaryComponent e (A (bondFrom o b)) *
      (Q b b' - E (bondFrom o b) (bondFrom o b'))| ≤ bondCubeCard (2 * R) * (W * δ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have h1 : ∀ b ∈ doubleCubeBonds R, |imaginaryComponent e (A (bondFrom o b)) *
        (Q b b' - E (bondFrom o b) (bondFrom o b'))| ≤ W * δ := by
      intro b hb
      rw [abs_mul]
      have g1 := (abs_component_le_norm e (A (bondFrom o b))).trans
        (hA _ (bondFrom_mem_bondsWithin o hR1 hn hb))
      exact mul_le_mul g1 (hdiff b hb) (abs_nonneg _) hW0
    refine (Finset.sum_le_sum h1).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (card_doubleCubeBonds_le R) (by positivity)
  rw [hres, hT]
  refine (abs_add_le _ _).trans ?_
  linarith
private theorem component_iteratedDiff_eq (A : TorusBond n → imaginaryQuaternions) (o : TorusSite n) (R : ℕ)
    (e : Fin 3) (i k : Fin 4) (l : List (Fin 4)) :
    ∀ (m : ℕ) (y : Fin 4 → ℤ), OffsetInBox m y → m + l.length + 2 ≤ 2 * R →
      imaginaryComponent e (iteratedDiff l (lieFormCurl A) (o + siteOfInt y, i, k)) =
        plaquetteForwardDiffs l (intCurl (componentField A o R e)) (y, i, k) := by
  induction l with
  | nil =>
    intro m y hy hm
    simp only [List.length_nil, add_zero] at hm
    have hv : ∀ (z : Fin 4 → ℤ) (j : Fin 4), OffsetInBox (m + 1) z →
        componentField A o R e (z, j) = imaginaryComponent e (A (o + siteOfInt z, j)) := by
      intro z j hz
      have h2 := bondOffsetInBox_of_offsetInBox (b := (z, j)) hz
      have h3 : BondOffsetInBox (2 * R) (z, j) :=
        ⟨offsetInBox_mono h2.1 (by omega), offsetInBox_mono h2.2 (by omega)⟩
      simp [componentField, h3, bondFrom]
    show imaginaryComponent e (lieFormCurl A (o + siteOfInt y, i, k)) =
      intCurl (componentField A o R e) (y, i, k)
    simp only [lieFormCurl, intCurl]
    rw [hv _ _ (offsetInBox_mono hy (by omega)), hv _ _ (offsetInBox_add_single hy i),
      hv _ _ (offsetInBox_add_single hy k), hv _ _ (offsetInBox_mono hy (by omega)),
      siteOfInt_add_single, siteOfInt_add_single, ← add_assoc, ← add_assoc,
      component_sub, component_sub, component_add]
  | cons d l ih =>
    intro m y hy hm
    simp only [List.length_cons] at hm
    have h1 := ih m y hy (by omega)
    have h2 := ih (m + 1) (y + Pi.single d 1) (offsetInBox_add_single hy d) (by omega)
    rw [siteOfInt_add_single, ← add_assoc] at h2
    show imaginaryComponent e (iteratedDiff l (lieFormCurl A) (o + siteOfInt y + unitStep n d, i, k) -
        iteratedDiff l (lieFormCurl A) (o + siteOfInt y, i, k)) =
      plaquetteForwardDiffs l (intCurl (componentField A o R e)) (y + Pi.single d 1, i, k) -
        plaquetteForwardDiffs l (intCurl (componentField A o R e)) (y, i, k)
    rw [component_sub, h1, h2]
private theorem sum_intCurl_sq_le_curlNormSq (A : TorusBond n → imaginaryQuaternions) (o : TorusSite n) {R : ℕ}
    (hR : 2 ≤ R) (hn : 16 * R < n) (e : Fin 3) :
    ∑ p ∈ plaquetteCube (R - 2), intCurl (componentField A o R e) p ^ 2 ≤ curlNormSq (supBall o R) A := by
  set φ : (Fin 4 → ℤ) × Fin 4 × Fin 4 → TorusPlaquette n := fun p => (o + siteOfInt p.1, p.2) with hφ
  have hinj : Set.InjOn φ (plaquetteCube (R - 2)) := by
    intro p hp p' hp' h
    have h1 : OffsetInBox (R - 2) p.1 := mem_siteCube_iff.1 (Finset.mem_product.1 hp).1
    have h2 : OffsetInBox (R - 2) p'.1 := mem_siteCube_iff.1 (Finset.mem_product.1 hp').1
    have e1 : (φ p).1 = (φ p').1 := congrArg Prod.fst h
    have e2 : (φ p).2 = (φ p').2 := congrArg Prod.snd h
    simp only [hφ] at e1 e2
    have e3 : p.1 = p'.1 := by
      rw [← offsetFrom_add_siteOfInt (offsetInBox_small h1 (by omega)) o, e1,
        offsetFrom_add_siteOfInt (offsetInBox_small h2 (by omega))]
    exact Prod.ext e3 e2
  have hmem : ∀ p ∈ plaquetteCube (R - 2), φ p ∈ plaquettesIn (supBall o R) := by
    intro p hp
    have h1 : OffsetInBox (R - 2) p.1 := mem_siteCube_iff.1 (Finset.mem_product.1 hp).1
    have h2 : p.2.1 < p.2.2 := by simpa using (Finset.mem_product.1 hp).2
    have hcorner : ∀ z : Fin 4 → ℤ, OffsetInBox R z → o + siteOfInt z ∈ supBall o (R : ℝ) := by
      intro z hz
      rw [mem_supBall_natCast_iff, offsetFrom_add_siteOfInt (offsetInBox_small hz (by omega))]
      exact hz
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, h2, ?_⟩
    have g0 : OffsetInBox R p.1 := offsetInBox_mono h1 (by omega)
    have g1 := offsetInBox_add_single h1 p.2.1
    have g2 := offsetInBox_add_single h1 p.2.2
    have g3 := offsetInBox_add_single g1 p.2.2
    have hR' : R - 2 + 1 + 1 = R := by omega
    rw [hR'] at g3
    have g1' := offsetInBox_mono g1 (by omega : R - 2 + 1 ≤ R)
    have g2' := offsetInBox_mono g2 (by omega : R - 2 + 1 ≤ R)
    have e1 : (siteOfInt (p.1 + Pi.single p.2.1 1) : TorusSite n) = siteOfInt p.1 + unitStep n p.2.1 :=
      siteOfInt_add_single _ _
    have e2 : (siteOfInt (p.1 + Pi.single p.2.2 1) : TorusSite n) = siteOfInt p.1 + unitStep n p.2.2 :=
      siteOfInt_add_single _ _
    have e3 : (siteOfInt (p.1 + Pi.single p.2.1 1 + Pi.single p.2.2 1) : TorusSite n) =
        siteOfInt p.1 + unitStep n p.2.1 + unitStep n p.2.2 := by rw [siteOfInt_add_single, e1]
    simp only [plaquetteVertices, hφ, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    refine ⟨hcorner _ g0, ?_, ?_, ?_⟩
    · have := hcorner _ g1'
      rwa [e1, ← add_assoc] at this
    · have := hcorner _ g2'
      rwa [e2, ← add_assoc] at this
    · have := hcorner _ g3
      rwa [e3, ← add_assoc, ← add_assoc] at this
  calc ∑ p ∈ plaquetteCube (R - 2), intCurl (componentField A o R e) p ^ 2
      ≤ ∑ p ∈ plaquetteCube (R - 2), ‖lieFormCurl A (φ p)‖ ^ 2 := by
        refine Finset.sum_le_sum fun p hp => ?_
        have h1 : OffsetInBox (R - 2) p.1 := mem_siteCube_iff.1 (Finset.mem_product.1 hp).1
        have := component_iteratedDiff_eq A o R e p.2.1 p.2.2 [] (R - 2) p.1 h1
          (by simp only [List.length_nil]; omega)
        have e1 : intCurl (componentField A o R e) p = imaginaryComponent e (lieFormCurl A (φ p)) := this.symm
        rw [e1]
        exact component_sq_le_norm_sq _ _
    _ = ∑ P ∈ (plaquetteCube (R - 2)).image φ, ‖lieFormCurl A P‖ ^ 2 :=
        (Finset.sum_image (f := fun P => ‖lieFormCurl A P‖ ^ 2) hinj).symm
    _ ≤ curlNormSq (supBall o R) A := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => sq_nonneg _
        intro P hP
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hP
        exact hmem p hp
end LatticeForm
private theorem gradientBlind_of_limitForm {a cK c C : ℝ} {L k : ℕ} {Q : IntBond → IntBond → ℝ}
    (hQ : IsLimitForm a cK c C L k Q) (hsym : ∀ b b', Q b b' = Q b' b) : IsGradientBlindKernel cK c C Q := by
  refine ⟨hsym, fun d b b' => ?_, hQ.decay, hQ.kills_gradients, hQ.coercive⟩
  have e : ∀ b : IntBond, bondImage ⟨1, fun _ => 1, Pi.single d 1, fun _ => Or.inl rfl⟩ b =
      ((b.1 + Pi.single d 1, b.2), 1) := by
    intro b
    simp only [bondImage, Equiv.Perm.coe_one, id_eq, Equiv.Perm.one_symm, if_true]
    refine Prod.ext (Prod.ext ?_ rfl) rfl
    funext i
    simp
  have := hQ.invariant ⟨1, fun _ => 1, Pi.single d 1, fun _ => Or.inl rfl⟩ b b'
  rw [e, e] at this
  simpa using this
private theorem main_term_bound {t R u Y : ℝ} (j : ℕ) (ht : 0 < t) (hR : 0 < R) (hu : 0 < u) (hRt : R ≤ u * t)
    (hY : 0 ≤ Y) :
    (t ^ (j + 2))⁻¹ * Real.sqrt Y ≤ u ^ (j + 2) * (R ^ j)⁻¹ * Real.sqrt ((R ^ 4)⁻¹ * Y) := by
  have hs : Real.sqrt Y = R ^ 2 * Real.sqrt ((R ^ 4)⁻¹ * Y) := by
    have h4 : (R ^ 4)⁻¹ = ((R ^ 2)⁻¹) ^ 2 := by
      rw [inv_pow, ← pow_mul]
    rw [h4, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    field_simp
  have hinv : (t ^ (j + 2))⁻¹ ≤ (u / R) ^ (j + 2) := by
    have h1 : R / u ≤ t := by
      rw [div_le_iff₀ hu]
      linarith
    have h2 : (R / u) ^ (j + 2) ≤ t ^ (j + 2) := by gcongr
    have h3 : (u / R) ^ (j + 2) = ((R / u) ^ (j + 2))⁻¹ := by
      rw [← inv_pow, inv_div]
    rw [h3]
    exact inv_anti₀ (by positivity) h2
  have hs0 := Real.sqrt_nonneg Y
  calc (t ^ (j + 2))⁻¹ * Real.sqrt Y ≤ (u / R) ^ (j + 2) * Real.sqrt Y :=
        mul_le_mul_of_nonneg_right hinv hs0
    _ = u ^ (j + 2) * (R ^ j)⁻¹ * Real.sqrt ((R ^ 4)⁻¹ * Y) := by
        rw [hs, div_pow, pow_add R j 2]
        field_simp
private theorem interior_bound_at_parameters (Tb : RenormalizationStepParameters.ParameterAssignment) (hD : Tb.Admissible)
    (h₁ : cubeLimitFormStatement) (h₂ : cubeHessianStatement) (h₃ : offDiagonalDecayStatement)
    (h₄ : curlDiffBoundStatement)
    (Cp c : ℝ) (hc : 0 < c) (j : ℕ) : ∃ (C c' : ℝ) (R₀ : ℕ), 0 < c' ∧
    ∀ (k n : ℕ) [NeZero n] (o : TorusSite n) (R : ℕ) (A : TorusBond n → imaginaryQuaternions), R₀ ≤ R → 16 * R < n →
      (∀ b ∈ bondsWithin (supBall o (2 * R)), ‖A b‖ ≤ (R : ℝ) ^ Cp) →
      (∀ η : TorusBond n → imaginaryQuaternions, (∀ b, b ∉ bondsTouching o R → η b = 0) →
        |hessianForm Tb.coupling Tb.side k (supBall o (2 * R)) A η| ≤ Real.exp (-(c * R)) * ∑ b : TorusBond n, ‖η b‖) →
      ∀ (l : List (Fin 4)), l.length = j → ∀ p ∈ plaquettesIn (supBall o ((R : ℝ) / 4)),
        ‖iteratedDiff l (lieFormCurl A) p‖ ≤
          C * ((R : ℝ) ^ j)⁻¹ *
              Real.sqrt (((R : ℝ) ^ 4)⁻¹ * curlNormSq (supBall o R) A) + Real.exp (-(c' * R)) := by
  obtain ⟨c₁, C₁, R₁, hc₁, hlim⟩ := h₁ Tb hD
  obtain ⟨CQ, R₂, -, hform⟩ := h₂ Tb hD
  obtain ⟨c₂, R₃, hc₂, hfar⟩ := h₃ Tb hD
  have hcK : 0 < Tb.coercivity := hD.cK_pos
  have hC₁ : 0 ≤ C₁ := by
    obtain ⟨Q, hQ, -⟩ := hlim 0
    have h := hQ.decay ((0 : Fin 4 → ℤ), (0 : Fin 4)) ((0 : Fin 4 → ℤ), (0 : Fin 4))
    by_contra hn
    push Not at hn
    have := mul_neg_of_neg_of_pos hn
      (Real.exp_pos (-(c₁ * bondSupDist ((0 : Fin 4 → ℤ), (0 : Fin 4)) ((0 : Fin 4 → ℤ), (0 : Fin 4)))))
    linarith [abs_nonneg (Q ((0 : Fin 4 → ℤ), (0 : Fin 4)) ((0 : Fin 4 → ℤ), (0 : Fin 4)))]
  obtain ⟨κ, hκ, hst⟩ := h₄ Tb.coercivity c₁ C₁ hcK hc₁ hC₁ j
  obtain ⟨μ, R₄, hμ, herr⟩ := energyStepError_small c c₁ c₂ C₁ Tb.coercivity κ Cp hc hc₁ hc₂ hC₁ hcK hκ j
  set u : ℝ := 16 * ((j : ℝ) + 5) with hu
  have hu0 : 0 < u := by positivity
  refine ⟨3 * κ * u ^ (j + 2), μ, max (max (max R₁ R₂) (max R₃ R₄)) (8 * (j + 5)), hμ, ?_⟩
  intro k n _ o R A hR hn hAb hcrit l hl p hp
  have hRR₁ : R₁ ≤ R :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_trans (le_max_left _ _) hR)
  have hRR₂ : R₂ ≤ R :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_trans (le_max_left _ _) hR)
  have hRR₃ : R₃ ≤ R :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_trans (le_max_left _ _) hR)
  have hRR₄ : R₄ ≤ R :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_trans (le_max_left _ _) hR)
  have hRj : 8 * (j + 5) ≤ R := le_trans (le_max_right _ _) hR
  have hR4 : 4 ≤ R := by omega
  have hR0 : (0 : ℝ) < R := by exact_mod_cast (by omega : 0 < R)
  obtain ⟨Q, hQl, hnear⟩ := hlim k
  have hsymQ : ∀ b b', Q b b' = Q b' b := by
    intro b b'
    have hdouble : Filter.Tendsto (fun R : ℕ => 2 * R) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_mono (fun R => by simp only [id]; omega) Filter.tendsto_id
    refine tendsto_nhds_unique_of_eventuallyEq ((hQl.tendsto b b').comp hdouble)
      ((hQl.tendsto b' b).comp hdouble) ?_
    filter_upwards [Filter.eventually_ge_atTop R₂] with R' hR'
    haveI : NeZero (16 * (2 * R' + 1)) := ⟨by omega⟩
    obtain ⟨-, -, hs, -, -, -, hcl⟩ := hform k (16 * (2 * R' + 1)) 0 R' hR' (by omega)
    have := entries_symm_of_form (hessianForm Tb.coupling Tb.side k (supBall (0 : TorusSite (16 * (2 * R' + 1))) (2 * R')))
      (fun b b' => mixedDeriv (actionAtLevel Tb.coupling Tb.side k (supBall (0 : TorusSite (16 * (2 * R' + 1))) (2 * R')))
        (trivialField (16 * (2 * R' + 1))) ![b, b'] ![imaginaryUnitI, imaginaryUnitI]) hs hcl
      (bondFrom 0 b) (bondFrom 0 b')
    have e : (((2 * R' : ℕ)) : ℝ) = 2 * (R' : ℝ) := by push_cast; ring
    simp only [Function.comp, cubeEntry]
    rw [e]
    exact this
  have hQ : IsGradientBlindKernel Tb.coercivity c₁ C₁ Q := gradientBlind_of_limitForm hQl hsymQ
  obtain ⟨-, -, hs, hlin, hbd, -, hcl⟩ := hform k n o R hRR₂ hn
  set W : ℝ := (R : ℝ) ^ Cp with hW
  have hW0 : 0 ≤ W := Real.rpow_nonneg hR0.le _
  set ε : ℝ := Real.exp (-(c * R)) + bondCubeCard (2 * R) * (W *
      (Real.exp (-(c₁ * R)) + C₁ * Real.exp (-(c₁ * ((R : ℝ) / 4))) + Real.exp (-(c₂ * R)))) with hε
  have hε0 : 0 ≤ ε := by
    have : 0 ≤ bondCubeCard (2 * R) := by unfold bondCubeCard; positivity
    positivity
  set t : ℕ := R / (8 * (j + 5)) with ht
  have hdiv : 0 < 8 * (j + 5) := by omega
  have htm : t * (8 * (j + 5)) ≤ R := Nat.div_mul_le_self _ _
  have htl : R < (t + 1) * (8 * (j + 5)) := by
    have := Nat.lt_mul_div_succ R hdiv
    rw [mul_comm] at this
    exact this
  have ht1 : 1 ≤ t := Nat.div_pos hRj hdiv
  have htR : t ≤ R := Nat.div_le_self _ _
  have hq : R / 4 + t + (j + 4) * (2 * t + 2) ≤ R - 2 := by
    have e1 : (j + 4) * (2 * t + 2) + 2 * t = 2 * (t * (j + 5)) + 2 * j + 8 := by ring
    have e2 : t * (8 * (j + 5)) = 8 * (t * (j + 5)) := by ring
    have e3 : t ≤ t * (j + 5) := Nat.le_mul_of_pos_right _ (by omega)
    rw [e2] at htm
    generalize t * (j + 5) = P at *
    generalize (j + 4) * (2 * t + 2) = P' at *
    omega
  have hRt : (R : ℝ) ≤ 16 * ((j : ℝ) + 5) * t := by
    have h1 : R ≤ 16 * (j + 5) * t := by
      have : (t + 1) * (8 * (j + 5)) ≤ (2 * t) * (8 * (j + 5)) := Nat.mul_le_mul_right _ (by omega)
      have e : (2 * t) * (8 * (j + 5)) = 16 * (j + 5) * t := by ring
      omega
    exact_mod_cast h1
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht1
  have hsupp : ∀ e : Fin 3, ∀ b, b ∉ bondCube (2 * R) → componentField A o R e b = 0 := by
    intro e b hb
    have : ¬ BondOffsetInBox (2 * R) b := fun h =>
      hb (Finset.mem_product.2 ⟨mem_siteCube_iff.2 h.1, Finset.mem_univ _⟩)
    simp [componentField, this]
  have hsize : ∀ e : Fin 3, ∀ b, |componentField A o R e b| ≤ W := by
    intro e b
    by_cases h : BondOffsetInBox (2 * R) b
    · have h1 : componentField A o R e b = imaginaryComponent e (A (bondFrom o b)) := by
        simp [componentField, h]
      rw [h1]
      exact (abs_component_le_norm e _).trans
        (hAb _ (bondFrom_mem_bondsWithin o (by omega) hn (mem_doubleCubeBonds.2 h)))
    · simpa [componentField, h] using hW0
  have hres : ∀ e : Fin 3, ∀ b' ∈ bondCube (R - 2), |kernelResidual Q (componentField A o R e) b'| ≤ ε := by
    intro e b' hb'
    have h0 : OffsetInBox (R - 2) b'.1 := mem_siteCube_iff.1 (Finset.mem_product.1 hb').1
    have hinner : bondFrom o b' ∈ bondsTouching o R := by
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, Or.inl ?_⟩
      simp only [bondFrom]
      rw [mem_supBall_natCast_iff, offsetFrom_add_siteOfInt (offsetInBox_small h0 (by omega))]
      exact offsetInBox_mono h0 (by omega)
    have hcut := hcrit (Pi.single (bondFrom o b') (basisImag e)) (fun b hb =>
      Pi.single_eq_of_ne (fun h => hb (by rw [h]; exact hinner)) _)
    have hnorm : ∑ b : TorusBond n,
        ‖(Pi.single (bondFrom o b') (basisImag e) : TorusBond n → imaginaryQuaternions) b‖ = 1 := by
      rw [Finset.sum_eq_single (bondFrom o b')]
      · rw [Pi.single_eq_same]
        exact norm_basisImag e
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb]
      · simp
    rw [hnorm, mul_one, hessianForm_single_eq_sum hcK hs hlin hbd hcl A e _] at hcut
    exact kernelResidual_bound (E := fun b b' => mixedDeriv (actionAtLevel Tb.coupling Tb.side k (supBall o (2 * R)))
      (trivialField n) ![b, b'] ![imaginaryUnitI, imaginaryUnitI]) hR4 hn hc₁ hQ.decay (hnear n o R hRR₁ hn)
      (hfar k n o R hRR₃ hn) A hAb hW0 hC₁ e b' hb' hcut
  obtain ⟨x, i, k'⟩ := p
  have hp' := (Finset.mem_filter.1 hp).2
  have hik : i < k' := hp'.1
  have hx : x ∈ supBall o ((R : ℝ) / 4) := hp'.2 x (by simp [plaquetteVertices])
  have hxd : supDist x o ≤ R / 4 := by
    have h1 : (supDist x o : ℝ) ≤ (R : ℝ) / 4 := (Finset.mem_filter.1 hx).2
    have h2 : 4 * supDist x o ≤ R := by
      have : (4 : ℝ) * supDist x o ≤ R := by linarith
      exact_mod_cast this
    omega
  have hy : OffsetInBox (R / 4) (offsetFrom o x) := (supDist_le_iff_offsetInBox o x _).1 hxd
  set Y := curlNormSq (supBall o R) A with hY
  have hY0 : 0 ≤ Y := Finset.sum_nonneg fun _ _ => sq_nonneg _
  set Er := energyStepError c₁ C₁ (2 * R) (R - 2) (j + 4) t W ε / (2 * Tb.coercivity) with hEr
  have hcolour : ∀ e : Fin 3, |imaginaryComponent e (iteratedDiff l (lieFormCurl A) (x, i, k'))| ≤
      κ * (((t : ℝ) ^ (j + 2))⁻¹ * Real.sqrt Y + (t : ℝ) ^ 2 * Real.sqrt Er) := by
    intro e
    have h1 := hst Q hQ (componentField A o R e) (2 * R) (R - 2) t (R / 4) W ε ht1 hq hW0 hε0 (hsupp e)
      (hsize e) (hres e) l hl _ (mem_siteCube_iff.2 hy) i k' hik
    have h2 := component_iteratedDiff_eq A o R e i k' l (R / 4) _ hy (by rw [hl]; omega)
    rw [add_siteOfInt_offsetFrom] at h2
    rw [h2]
    refine h1.trans ?_
    have h3 := sum_intCurl_sq_le_curlNormSq A o (by omega : 2 ≤ R) hn e
    have h4 := Real.sqrt_le_sqrt h3
    gcongr
  have hnorm := norm_le_sum_abs_components (iteratedDiff l (lieFormCurl A) (x, i, k'))
  rw [Fin.sum_univ_three] at hnorm
  have hsum : ‖iteratedDiff l (lieFormCurl A) (x, i, k')‖ ≤
      3 * κ * (((t : ℝ) ^ (j + 2))⁻¹ * Real.sqrt Y) + 3 * κ * ((t : ℝ) ^ 2 * Real.sqrt Er) := by
    have := hcolour 0
    have := hcolour 1
    have := hcolour 2
    nlinarith
  have hmain := main_term_bound j ht0 hR0 hu0 hRt hY0
  have hE := herr R t hRR₄ htR hRt
  have hm2 : 3 * κ * (((t : ℝ) ^ (j + 2))⁻¹ * Real.sqrt Y) ≤
      3 * κ * u ^ (j + 2) * ((R : ℝ) ^ j)⁻¹ * Real.sqrt (((R : ℝ) ^ 4)⁻¹ * Y) := by
    have := mul_le_mul_of_nonneg_left hmain (by positivity : 0 ≤ 3 * κ)
    calc _ ≤ _ := this
      _ = _ := by ring
  linarith
theorem interiorRegularity (h₁ : cubeLimitFormStatement) (h₂ : cubeHessianStatement)
    (h₃ : offDiagonalDecayStatement) (h₄ : curlDiffBoundStatement) : interiorRegularityStatement := by
  intro a _
  refine ⟨0, fun _ => 1, fun _ => one_pos, fun L _ _ T _ _ hD _ => ⟨0, fun y _ _ _ => ?_⟩⟩
  exact fun Cp c hc j => interior_bound_at_parameters T hD h₁ h₂ h₃ h₄ Cp c hc j
end YangMills.Construction.BoxGaussian
end
