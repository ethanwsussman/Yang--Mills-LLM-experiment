import YangMills.Construction.ColdStepAtMirrorFrames.FreezingOfTheMeansProof
import YangMills.Construction.ColdStepAtMirrorFrames.BoxesOfTwoToriMatchProof
import YangMills.Construction.ColdStepAtMirrorFrames.CommonBondsOfTwoTori
import YangMills.Construction.ColdStepAtMirrorFrames.EntryBoundOfASymmetricSystem
import YangMills.Construction.ColdStepAtMirrorFrames.FramesAtTheFlatTop
import YangMills.Construction.ColdStepAtMirrorFrames.SumOfADecayOnATorus
import YangMills.Construction.ResponseInTheExpansion.EntriesOfTheHessianOfTheMirror
import YangMills.Construction.ResponseInTheExpansion.HessianAtTheFramesIsCoerciveAndLocal
import YangMills.Construction.ResponseInTheExpansion.HessiansOfTheMirrorAndOfTheFlatTorus
import YangMills.Construction.ResponseInTheExpansion.MirrorOfAColdBoxIsCold
import YangMills.Construction.SummableBoundsOfTheFlow.MeanAlongATiltProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames
namespace ResponseInTheExpansion
open TorusFields TorusLumps StepCosts RenormalizationStepParameters WeightedResponses
namespace ReflectedHessianComparison
section Inverse
variable {ι : Type} [Fintype ι] [DecidableEq ι]
private theorem isUnit_det_of_coercive (M : Matrix ι ι ℝ) {lam : ℝ} (hl : 0 < lam)
    (hc : ∀ x : ι → ℝ, lam * ∑ i, x i ^ 2 ≤ ∑ i, x i * M.mulVec x i) : IsUnit M.det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have h1 := hc v
  simp only [hMv, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h1
  have hs : ∑ i, v i ^ 2 ≤ 0 := by
    by_contra hcon
    have : 0 < lam * ∑ i, v i ^ 2 := mul_pos hl (not_le.mp hcon)
    linarith
  apply hv
  funext i
  have h2 : v i ^ 2 ≤ ∑ j, v j ^ 2 :=
    Finset.single_le_sum (f := fun j => v j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have h3 : v i ^ 2 = 0 := le_antisymm (h2.trans hs) (sq_nonneg _)
  simpa using h3
private theorem mulVec_inv_mulVec (M : Matrix ι ι ℝ) (hM : IsUnit M.det) (v : ι → ℝ) :
    M.mulVec (M⁻¹.mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hM, Matrix.one_mulVec]
private theorem inv_mulVec_mulVec (M : Matrix ι ι ℝ) (hM : IsUnit M.det) (v : ι → ℝ) :
    M⁻¹.mulVec (M.mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hM, Matrix.one_mulVec]
private theorem mulVec_single_one_apply (M : Matrix ι ι ℝ) (j i : ι) :
    M.mulVec (Pi.single j 1) i = M i j := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]
private theorem abs_inv_apply_le (hEB : SymmetricSystemGreenDecay) (d : ι → ι → ℝ) (M : Matrix ι ι ℝ) (lam κ : ℝ)
    (hl : 0 < lam) (hκ : 0 ≤ κ) (h0 : ∀ i, d i i = 0) (hs : ∀ i j, d i j = d j i)
    (ht : ∀ i j k, d i k ≤ d i j + d j k) (hsym : M.IsSymm)
    (hc : ∀ x : ι → ℝ, lam * ∑ i, x i ^ 2 ≤ ∑ i, x i * M.mulVec x i)
    (hr : ∀ i, ∑ j, |M i j| * (Real.exp (2 * κ * d i j) - 1) ≤ lam / 2) (i j : ι) :
    |M⁻¹ i j| ≤ 2 / lam * Real.exp (-(2 * κ * d i j)) := by
  have hu := isUnit_det_of_coercive M hl hc
  have h := hEB ι d M lam κ hl hκ h0 hs ht hsym hc hr (M⁻¹.mulVec (Pi.single j 1)) j
    (mulVec_inv_mulVec M hu _) i
  rwa [mulVec_single_one_apply] at h
private theorem exp_mul_exp_sub_one_le {δ κ t : ℝ} (hδ : 0 < δ) (hκ : 0 ≤ κ) (hκδ : κ ≤ δ / 8) (ht : 0 ≤ t) :
    Real.exp (-(δ * t)) * (Real.exp (2 * κ * t) - 1) ≤ 8 * κ / δ * Real.exp (-(δ / 2 * t)) := by
  have h1 : Real.exp (2 * κ * t) - 1 ≤ 2 * κ * t * Real.exp (2 * κ * t) := by
    have h := Real.add_one_le_exp (-(2 * κ * t))
    have hp := Real.exp_pos (2 * κ * t)
    have e : Real.exp (-(2 * κ * t)) * Real.exp (2 * κ * t) = 1 := by
      rw [← Real.exp_add]
      simp
    nlinarith
  have h2 : t ≤ 4 / δ * Real.exp (δ / 4 * t) := by
    have h := Real.add_one_le_exp (δ / 4 * t)
    have e : 4 / δ * (δ / 4 * t + 1) = t + 4 / δ := by
      field_simp
    have h3 : 4 / δ * (δ / 4 * t + 1) ≤ 4 / δ * Real.exp (δ / 4 * t) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    have h4 : 0 < 4 / δ := by positivity
    linarith
  have hE : 0 ≤ Real.exp (2 * κ * t) := (Real.exp_pos _).le
  have h3 : Real.exp (2 * κ * t) - 1 ≤ 8 * κ / δ * Real.exp (δ / 4 * t) * Real.exp (2 * κ * t) := by
    refine h1.trans ?_
    have : 2 * κ * t ≤ 2 * κ * (4 / δ * Real.exp (δ / 4 * t)) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have e : 2 * κ * (4 / δ * Real.exp (δ / 4 * t)) = 8 * κ / δ * Real.exp (δ / 4 * t) := by ring
    rw [e] at this
    exact mul_le_mul_of_nonneg_right this hE
  have hexp : Real.exp (-(δ * t)) * (Real.exp (δ / 4 * t) * Real.exp (2 * κ * t)) ≤ Real.exp (-(δ / 2 * t)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  calc Real.exp (-(δ * t)) * (Real.exp (2 * κ * t) - 1)
      ≤ Real.exp (-(δ * t)) * (8 * κ / δ * Real.exp (δ / 4 * t) * Real.exp (2 * κ * t)) :=
        mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
    _ = 8 * κ / δ * (Real.exp (-(δ * t)) * (Real.exp (δ / 4 * t) * Real.exp (2 * κ * t))) := by ring
    _ ≤ 8 * κ / δ * Real.exp (-(δ / 2 * t)) := mul_le_mul_of_nonneg_left hexp (by positivity)
omit [DecidableEq ι] in
private theorem weighted_row_sum_le (d : ι → ι → ℝ) (M : Matrix ι ι ℝ) {lam K δ κ S : ℝ} (hK : 0 ≤ K)
    (hδ : 0 < δ) (hκ : 0 ≤ κ) (hκδ : κ ≤ δ / 8) (hd : ∀ i j, 0 ≤ d i j)
    (hM : ∀ i j, |M i j| ≤ K * Real.exp (-(δ * d i j)))
    (hS : ∀ i, ∑ j, Real.exp (-(δ / 2 * d i j)) ≤ S) (hsmall : K * (8 * κ / δ) * S ≤ lam / 2) (i : ι) :
    ∑ j, |M i j| * (Real.exp (2 * κ * d i j) - 1) ≤ lam / 2 := by
  have h1 : ∀ j, |M i j| * (Real.exp (2 * κ * d i j) - 1) ≤
      K * (8 * κ / δ) * Real.exp (-(δ / 2 * d i j)) := by
    intro j
    have hw : 0 ≤ Real.exp (2 * κ * d i j) - 1 := by
      have : 1 ≤ Real.exp (2 * κ * d i j) := Real.one_le_exp (by have := hd i j; positivity)
      linarith
    calc |M i j| * (Real.exp (2 * κ * d i j) - 1)
        ≤ K * Real.exp (-(δ * d i j)) * (Real.exp (2 * κ * d i j) - 1) :=
          mul_le_mul_of_nonneg_right (hM i j) hw
      _ = K * (Real.exp (-(δ * d i j)) * (Real.exp (2 * κ * d i j) - 1)) := by ring
      _ ≤ K * (8 * κ / δ * Real.exp (-(δ / 2 * d i j))) :=
          mul_le_mul_of_nonneg_left (exp_mul_exp_sub_one_le hδ hκ hκδ (hd i j)) hK
      _ = K * (8 * κ / δ) * Real.exp (-(δ / 2 * d i j)) := by ring
  calc ∑ j, |M i j| * (Real.exp (2 * κ * d i j) - 1)
      ≤ ∑ j, K * (8 * κ / δ) * Real.exp (-(δ / 2 * d i j)) := Finset.sum_le_sum fun j _ => h1 j
    _ = K * (8 * κ / δ) * ∑ j, Real.exp (-(δ / 2 * d i j)) := by rw [Finset.mul_sum]
    _ ≤ K * (8 * κ / δ) * S := mul_le_mul_of_nonneg_left (hS i) (by positivity)
    _ ≤ lam / 2 := hsmall
private theorem abs_inv_mulVec_sub_le (A : Matrix ι ι ℝ) (hA : IsUnit A.det) {R T : ℝ} (hR : ∀ p, ∑ q, |A⁻¹ p q| ≤ R) (hT : 0 ≤ T)
    (f v : ι → ℝ) (hres : ∀ p, |A.mulVec f p - v p| ≤ T) (p : ι) : |A⁻¹.mulVec v p - f p| ≤ R * T := by
  have e : A⁻¹.mulVec v = f - A⁻¹.mulVec (A.mulVec f - v) := by
    rw [Matrix.mulVec_sub, inv_mulVec_mulVec A hA]
    abel
  rw [e]
  have h1 : (f - A⁻¹.mulVec (A.mulVec f - v)) p - f p = -(A⁻¹.mulVec (A.mulVec f - v) p) := by
    simp
  rw [h1, abs_neg]
  calc |A⁻¹.mulVec (A.mulVec f - v) p| = |∑ q, A⁻¹ p q * (A.mulVec f - v) q| := rfl
    _ ≤ ∑ q, |A⁻¹ p q * (A.mulVec f - v) q| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q, |A⁻¹ p q| * T := by
        refine Finset.sum_le_sum fun q _ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hres q) (abs_nonneg _)
    _ = (∑ q, |A⁻¹ p q|) * T := by rw [Finset.sum_mul]
    _ ≤ R * T := mul_le_mul_of_nonneg_right (hR p) hT
end Inverse
section Compare
variable {J P Q : Type} [Fintype J] [DecidableEq J] [Fintype P] [Fintype Q] [DecidableEq (P × Fin 3)]
private structure InverseComparison (A : Matrix (P × Fin 3) (P × Fin 3) ℝ) (B : Matrix J J ℝ) (h : Q → J) (t : Q → P)
    (dJ : J → J → ℝ) (dP : P → P → ℝ) (rJ : J → ℝ) (rP : P → ℝ) (a ρ ε R K K' S κ δ γ : ℝ) : Prop where
  hA : IsUnit A.det
  hB : IsUnit B.det
  h_inj : Function.Injective h
  t_inj : Function.Injective t
  standingConstraints : ∀ p, ∑ q, |A⁻¹ p q| ≤ R
  R_nonneg : 0 ≤ R
  K_nonneg : 0 ≤ K
  K'_nonneg : 0 ≤ K'
  S_nonneg : 0 ≤ S
  ε_nonneg : 0 ≤ ε
  κ_nonneg : 0 ≤ κ
  ρ_nonneg : 0 ≤ ρ
  γ_nonneg : 0 ≤ γ
  γ_δ : 2 * γ ≤ δ
  γ_κ : 2 * γ ≤ κ
  invB : ∀ c c', |B⁻¹ c c'| ≤ K * Real.exp (-(κ * dJ c c'))
  sumJ : ∀ c', ∑ c, Real.exp (-(κ * dJ c c')) ≤ S
  rowB : ∀ c, ∑ c', |B c c'| ≤ K'
  decA : ∀ (p q : P) (e e' : Fin 3), |A (p, e) (q, e')| ≤ K * Real.exp (-(δ * dP p q))
  sumP : ∀ p, ∑ q, Real.exp (-(γ * dP p q)) ≤ S
  dP_nonneg : ∀ p q, 0 ≤ dP p q
  dP_tri : ∀ p q r, dP p r ≤ dP p q + dP q r
  d_same : ∀ q q', dJ (h q) (h q') = dP (t q) (t q')
  r_same : ∀ q, rJ (h q) = rP (t q)
  covJ : ∀ c, rJ c ≤ a + ρ → ∃ q, h q = c
  covP : ∀ p, rP p ≤ a + ρ / 2 → ∃ q, t q = p
  lipJ : ∀ c c', rJ c ≤ rJ c' + dJ c c'
  lipP : ∀ p p', rP p ≤ rP p' + dP p p'
  entries : ∀ (q₁ q₂ : Q) (e e' : Fin 3), rJ (h q₁) ≤ a + ρ / 2 → rJ (h q₂) ≤ a + ρ →
    |A (t q₁, e) (t q₂, e') - (if e = e' then B (h q₁) (h q₂) else 0)| ≤ ε
variable {A : Matrix (P × Fin 3) (P × Fin 3) ℝ} {B : Matrix J J ℝ} {h : Q → J} {t : Q → P}
  {dJ : J → J → ℝ} {dP : P → P → ℝ} {rJ : J → ℝ} {rP : P → ℝ} {a ρ ε R K K' S κ δ γ : ℝ}
private theorem InverseComparison.abs_inv_sub_le (C : InverseComparison A B h t dJ dP rJ rP a ρ ε R K K' S κ δ γ) (q₁ q₂ : Q) (e e' : Fin 3)
    (h₁ : rJ (h q₁) ≤ a) (h₂ : rJ (h q₂) ≤ a) :
    |A⁻¹ (t q₁, e) (t q₂, e') - (if e = e' then B⁻¹ (h q₁) (h q₂) else 0)| ≤
      R * (ε * (K * S) + K' * (K * Real.exp (-(κ * ρ))) + K * K * S * Real.exp (-(γ * (ρ / 2)))) := by
  classical
  have hρ := C.ρ_nonneg
  have hK := C.K_nonneg
  have hS := C.S_nonneg
  have hK' := C.K'_nonneg
  have hε := C.ε_nonneg
  set f' : J → ℝ := B⁻¹.mulVec (Pi.single (h q₂) 1) with hf'
  have hf'e : ∀ c, f' c = B⁻¹ c (h q₂) := fun c => mulVec_single_one_apply _ _ _
  have hBf : ∀ c, B.mulVec f' c = if c = h q₂ then 1 else 0 := by
    intro c
    rw [hf', mulVec_inv_mulVec B C.hB, Pi.single_apply]
  have habs : ∀ c, |f' c| ≤ K * Real.exp (-(κ * dJ c (h q₂))) := fun c => by
    rw [hf'e]
    exact C.invB _ _
  let Qs : Finset Q := Finset.univ.filter fun q => rJ (h q) ≤ a + ρ
  have hmem : ∀ q, q ∈ Qs ↔ rJ (h q) ≤ a + ρ := fun q => by simp [Qs]
  let f : P × Fin 3 → ℝ := fun p => ∑ q ∈ Qs, if p = (t q, e') then f' (h q) else 0
  let v : P × Fin 3 → ℝ := Pi.single (t q₂, e') 1
  have hAf : ∀ p, A.mulVec f p = ∑ q ∈ Qs, A p (t q, e') * f' (h q) := by
    intro p
    show ∑ r, A p r * f r = _
    simp only [f, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp [mul_ite]
  have hsumf : ∑ q ∈ Qs, |f' (h q)| ≤ K * S := by
    calc ∑ q ∈ Qs, |f' (h q)| = ∑ c ∈ Qs.image h, |f' c| := by
          rw [Finset.sum_image fun x _ y _ hxy => C.h_inj hxy]
      _ ≤ ∑ c, |f' c| := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => abs_nonneg _
      _ ≤ ∑ c, K * Real.exp (-(κ * dJ c (h q₂))) := Finset.sum_le_sum fun c _ => habs c
      _ = K * ∑ c, Real.exp (-(κ * dJ c (h q₂))) := by rw [Finset.mul_sum]
      _ ≤ K * S := mul_le_mul_of_nonneg_left (C.sumJ _) hK
  set T : ℝ := ε * (K * S) + K' * (K * Real.exp (-(κ * ρ))) + K * K * S * Real.exp (-(γ * (ρ / 2))) with hT
  have hE1 : 0 ≤ K' * (K * Real.exp (-(κ * ρ))) := by positivity
  have hE2 : 0 ≤ K * K * S * Real.exp (-(γ * (ρ / 2))) := by positivity
  have hE0 : 0 ≤ ε * (K * S) := by positivity
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  have hfirst : ∀ (q : Q) (e₀ : Fin 3), rJ (h q) ≤ a + ρ / 2 →
      |∑ r ∈ Qs, (A (t q, e₀) (t r, e') - (if e₀ = e' then B (h q) (h r) else 0)) * f' (h r)| ≤ ε * (K * S) := by
    intro q e₀ hq
    calc |∑ r ∈ Qs, (A (t q, e₀) (t r, e') - (if e₀ = e' then B (h q) (h r) else 0)) * f' (h r)|
        ≤ ∑ r ∈ Qs, |(A (t q, e₀) (t r, e') - (if e₀ = e' then B (h q) (h r) else 0)) * f' (h r)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ r ∈ Qs, ε * |f' (h r)| := by
          refine Finset.sum_le_sum fun r hr => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (C.entries q r e₀ e' hq ((hmem r).mp hr)) (abs_nonneg _)
      _ = ε * ∑ r ∈ Qs, |f' (h r)| := by rw [Finset.mul_sum]
      _ ≤ ε * (K * S) := mul_le_mul_of_nonneg_left hsumf hε
  have hoff : ∀ q : Q, |∑ c ∈ Finset.univ \ Qs.image h, B (h q) c * f' c| ≤ K' * (K * Real.exp (-(κ * ρ))) := by
    intro q
    have hc : ∀ c ∈ Finset.univ \ Qs.image h, |f' c| ≤ K * Real.exp (-(κ * ρ)) := by
      intro c hc
      have hc' : ¬ rJ c ≤ a + ρ := by
        intro hle
        obtain ⟨q', rfl⟩ := C.covJ c hle
        exact (Finset.mem_sdiff.mp hc).2 (Finset.mem_image_of_mem _ ((hmem q').mpr hle))
      have hd : ρ ≤ dJ c (h q₂) := by
        have := C.lipJ c (h q₂)
        linarith [not_le.mp hc']
      refine (habs c).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hK)
      exact neg_le_neg (mul_le_mul_of_nonneg_left hd C.κ_nonneg)
    calc |∑ c ∈ Finset.univ \ Qs.image h, B (h q) c * f' c|
        ≤ ∑ c ∈ Finset.univ \ Qs.image h, |B (h q) c * f' c| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ c ∈ Finset.univ \ Qs.image h, |B (h q) c| * (K * Real.exp (-(κ * ρ))) := by
          refine Finset.sum_le_sum fun c hcm => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hc c hcm) (abs_nonneg _)
      _ = (∑ c ∈ Finset.univ \ Qs.image h, |B (h q) c|) * (K * Real.exp (-(κ * ρ))) := by rw [Finset.sum_mul]
      _ ≤ (∑ c, |B (h q) c|) * (K * Real.exp (-(κ * ρ))) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => abs_nonneg _
      _ ≤ K' * (K * Real.exp (-(κ * ρ))) := mul_le_mul_of_nonneg_right (C.rowB _) (by positivity)
  have hsplit : ∀ q : Q, B.mulVec f' (h q) =
      ∑ r ∈ Qs, B (h q) (h r) * f' (h r) + ∑ c ∈ Finset.univ \ Qs.image h, B (h q) c * f' c := by
    intro q
    have e1 : ∑ r ∈ Qs, B (h q) (h r) * f' (h r) = ∑ c ∈ Qs.image h, B (h q) c * f' c := by
      rw [Finset.sum_image fun x _ y _ hxy => C.h_inj hxy]
    rw [e1, add_comm, Finset.sum_sdiff (Finset.subset_univ _)]
    rfl
  have hres : ∀ p, |A.mulVec f p - v p| ≤ T := by
    rintro ⟨p, e₀⟩
    by_cases hp : rP p ≤ a + ρ / 2
    · obtain ⟨q, rfl⟩ := C.covP p hp
      have hq : rJ (h q) ≤ a + ρ / 2 := by rw [C.r_same]; exact hp
      rw [hAf]
      by_cases he : e₀ = e'
      · subst he
        have hv : v (t q, e₀) = B.mulVec f' (h q) := by
          rw [hBf]
          simp [v, Pi.single_apply, C.t_inj.eq_iff, C.h_inj.eq_iff]
        rw [hv, hsplit]
        have h1 := hfirst q e₀ hq
        have h2 := hoff q
        simp only [if_true] at h1
        have e2 : ∑ r ∈ Qs, A (t q, e₀) (t r, e₀) * f' (h r) -
            (∑ r ∈ Qs, B (h q) (h r) * f' (h r) + ∑ c ∈ Finset.univ \ Qs.image h, B (h q) c * f' c) =
            ∑ r ∈ Qs, (A (t q, e₀) (t r, e₀) - B (h q) (h r)) * f' (h r) -
              ∑ c ∈ Finset.univ \ Qs.image h, B (h q) c * f' c := by
          simp only [sub_mul, Finset.sum_sub_distrib]
          ring
        rw [e2]
        calc _ ≤ |∑ r ∈ Qs, (A (t q, e₀) (t r, e₀) - B (h q) (h r)) * f' (h r)| +
              |∑ c ∈ Finset.univ \ Qs.image h, B (h q) c * f' c| := abs_sub _ _
          _ ≤ T := by rw [hT]; linarith
      · have hv : v (t q, e₀) = 0 := by
          simp [v, he]
        rw [hv, sub_zero]
        have h1 := hfirst q e₀ hq
        simp only [if_neg he, sub_zero] at h1
        rw [hT]
        linarith
    · have hp' : a + ρ / 2 < rP p := not_le.mp hp
      have hv : v (p, e₀) = 0 := by
        have hne : (p, e₀) ≠ (t q₂, e') := by
          intro heq
          have : p = t q₂ := congrArg Prod.fst heq
          rw [this, ← C.r_same] at hp'
          linarith
        simp [v, hne]
      rw [hAf, hv, sub_zero]
      have hterm : ∀ q ∈ Qs, |A (p, e₀) (t q, e') * f' (h q)| ≤
          K * K * Real.exp (-(γ * (ρ / 2))) * Real.exp (-(γ * dP p (t q))) := by
        intro q _
        rw [abs_mul]
        have hb1 := C.decA p (t q) e₀ e'
        have hb2 := habs (h q)
        rw [C.d_same] at hb2
        have hd1 := C.dP_nonneg p (t q)
        have hd2 := C.dP_nonneg (t q) (t q₂)
        have hρd : ρ / 2 ≤ dP p (t q) + dP (t q) (t q₂) := by
          have l1 := C.lipP p (t q₂)
          have l2 := C.dP_tri p (t q) (t q₂)
          have l3 := C.r_same q₂
          linarith
        calc |A (p, e₀) (t q, e')| * |f' (h q)|
            ≤ (K * Real.exp (-(δ * dP p (t q)))) * (K * Real.exp (-(κ * dP (t q) (t q₂)))) :=
              mul_le_mul hb1 hb2 (abs_nonneg _) (by positivity)
          _ = K * K * Real.exp (-(δ * dP p (t q)) + -(κ * dP (t q) (t q₂))) := by
              rw [Real.exp_add]; ring
          _ ≤ K * K * Real.exp (-(γ * (ρ / 2)) + -(γ * dP p (t q))) := by
              refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
              have g0 := C.γ_nonneg
              have a1 : 2 * γ * dP p (t q) ≤ δ * dP p (t q) := mul_le_mul_of_nonneg_right C.γ_δ hd1
              have a2 : 2 * γ * dP (t q) (t q₂) ≤ κ * dP (t q) (t q₂) := mul_le_mul_of_nonneg_right C.γ_κ hd2
              have a3 : γ * (ρ / 2) ≤ γ * (dP p (t q) + dP (t q) (t q₂)) := mul_le_mul_of_nonneg_left hρd g0
              have a4 : 0 ≤ γ * dP (t q) (t q₂) := mul_nonneg g0 hd2
              nlinarith
          _ = K * K * Real.exp (-(γ * (ρ / 2))) * Real.exp (-(γ * dP p (t q))) := by
              rw [Real.exp_add]; ring
      have hsumP : ∑ q ∈ Qs, Real.exp (-(γ * dP p (t q))) ≤ S := by
        calc ∑ q ∈ Qs, Real.exp (-(γ * dP p (t q))) = ∑ r ∈ Qs.image t, Real.exp (-(γ * dP p r)) := by
              rw [Finset.sum_image fun x _ y _ hxy => C.t_inj hxy]
          _ ≤ ∑ r, Real.exp (-(γ * dP p r)) :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => (Real.exp_pos _).le
          _ ≤ S := C.sumP p
      calc |∑ q ∈ Qs, A (p, e₀) (t q, e') * f' (h q)|
          ≤ ∑ q ∈ Qs, |A (p, e₀) (t q, e') * f' (h q)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ q ∈ Qs, K * K * Real.exp (-(γ * (ρ / 2))) * Real.exp (-(γ * dP p (t q))) :=
            Finset.sum_le_sum hterm
        _ = K * K * Real.exp (-(γ * (ρ / 2))) * ∑ q ∈ Qs, Real.exp (-(γ * dP p (t q))) := by
            rw [Finset.mul_sum]
        _ ≤ K * K * Real.exp (-(γ * (ρ / 2))) * S :=
            mul_le_mul_of_nonneg_left hsumP (by positivity)
        _ ≤ T := by rw [hT]; nlinarith
  have hfin := abs_inv_mulVec_sub_le A C.hA C.standingConstraints hT0 f v hres (t q₁, e)
  have e1 : A⁻¹.mulVec v (t q₁, e) = A⁻¹ (t q₁, e) (t q₂, e') := mulVec_single_one_apply _ _ _
  have hq₁ : q₁ ∈ Qs := (hmem q₁).mpr (by linarith)
  have e2 : f (t q₁, e) = if e = e' then B⁻¹ (h q₁) (h q₂) else 0 := by
    show (∑ q ∈ Qs, if (t q₁, e) = (t q, e') then f' (h q) else 0) = _
    by_cases he : e = e'
    · subst he
      rw [if_pos rfl, Finset.sum_eq_single q₁]
      · simp [hf'e]
      · intro r _ hr
        have : ¬ (t q₁, e) = (t r, e) := by
          intro heq
          exact hr (C.t_inj (congrArg Prod.fst heq)).symm
        simp [this]
      · intro hnot
        exact absurd hq₁ hnot
    · rw [if_neg he]
      refine Finset.sum_eq_zero fun r _ => ?_
      have : ¬ (t q₁, e) = (t r, e') := fun heq => he (congrArg Prod.snd heq)
      simp [this]
  rwa [e1, e2] at hfin
end Compare
section Geometry
open TopLevelSites
variable {F : BlockFrame}
private theorem cellSupDist_comm (y z : F.Cell) : cellSupDist y z = cellSupDist z y := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_comm <;> assumption
private theorem cellSupDist_triangle (y w z : F.Cell) : cellSupDist y z ≤ cellSupDist y w + cellSupDist w z := by apply _root_.YangMills.Construction.BlockAverages.PatchLocality.cellSupDist_triangle <;> assumption
private theorem cellSupDist_self (y : F.Cell) : cellSupDist y y = 0 := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_self <;> assumption
private theorem siteOfCoords_eq_iff {j : ℕ} {a b : Fin 4 → ℤ} :
    (siteOfCoords j a : F.Site j) = siteOfCoords j b ↔ ∀ i, (F.period j i : ℤ) ∣ b i - a i := by apply _root_.YangMills.Construction.BlockSites.siteOfCoords_eq_iff <;> assumption
private theorem siteCoords_siteOfCoords {j : ℕ} (a : Fin 4 → ℤ) (i : Fin 4) :
    siteCoords (siteOfCoords j a : F.Site j) i = a i % (F.period j i : ℤ) := by apply _root_.YangMills.Construction.BlockLines.siteCoords_siteOfCoords <;> assumption
variable {n : ℕ} [NeZero n]
private theorem cellSupDist_torusSiteInFrame (hn : ∀ i, F.extent i = n) (x y : TorusSite n) :
    cellSupDist (torusSiteInFrame F F.top x) (torusSiteInFrame F F.top y) = _root_.YangMills.Construction.TorusFields.supDist x y := by
  have e : torusSiteInFrame F F.top x - torusSiteInFrame F F.top y = torusSiteInFrame F F.top (x - y) := by
    have h := torusSiteInFrame_add (F := F) (j := F.top) (period_top_of_extent hn) (x - y) y
    rw [sub_add_cancel] at h
    rw [h]
    abel
  unfold cellSupDist TorusFields.supDist
  congr 1
  funext i
  have e' : torusSiteInFrame F F.top x i - torusSiteInFrame F F.top y i = torusSiteInFrame F F.top (x - y) i := congrFun e i
  rw [e']
  exact congrArg Int.natAbs (valMinAbs_intCast_cast (period_top_of_extent hn i).symm ((x - y) i))
private theorem mem_chordBonds_finiteCells_iff (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (b : F.Site F.depth × Fin 4) :
    b ∈ chordBonds (finiteCells F) ↔ ¬ IsAxialTreeBond b := by apply _root_.YangMills.SharedProofs.p118456 <;> assumption
variable {L : ℕ} [NeZero L]
private theorem isAxialTreeBond_reflectedBondPosition_iff (hL : Odd L) {t m : ℕ} (hm : 0 < m) (h2 : 2 ≤ n) (o : TorusSite n)
    (b : TorusBond (n * L)) :
    IsAxialTreeBond (F := reflectedTorusFrame L t m n) (reflectedBondPosition L t m o b) ↔
      IsAxialTreeBond (F := stepBlockFrame L n) (torusSiteInFrame (stepBlockFrame L n) 0 b.1, b.2) := by
  classical
  have hLp : 0 < L := hL.pos
  have h2' : 2 ≤ 4 * m := by omega
  have : NeZero (4 * m) := ⟨by omega⟩
  have : NeZero (4 * m * (reflectedTorusFrame L t m n).blockSide) := ⟨Nat.mul_ne_zero (by omega) (NeZero.ne L)⟩
  have : NeZero (n * (stepBlockFrame L n).blockSide) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
  set Xf : Fin 4 → ℤ := fun i => (b.1 i - (siteOfInt (n := n * L) fun l => (L : ℤ) * ((o l).cast : ℤ)) i).valMinAbs with hXf
  have hp : reflectedBondPosition L t m o b = (torusSiteInFrame (reflectedTorusFrame L t m n) (reflectedTorusFrame L t m n).depth
      (siteOfInt Xf : TorusSite (4 * m * (reflectedTorusFrame L t m n).blockSide)), b.2) := by
    rw [torusSiteInFrame_siteOfInt (period_depth_of_extent fun _ => rfl)]
    rfl
  rw [hp]
  refine Iff.trans (isAxialTreeBond_torusSiteInFrame_iff (F := reflectedTorusFrame L t m n) (n := 4 * m) (fun _ => rfl) hL h2' _ _)
    (Iff.trans ?_ (isAxialTreeBond_torusSiteInFrame_iff (F := stepBlockFrame L n) (n := n) (fun _ => rfl) hL h2 b.1 b.2).symm)
  have key : (fun l => offsetFromCentre L ((((siteOfInt Xf : TorusSite (4 * m * L)) l).cast : ℤ))) =
      fun l => offsetFromCentre L (((b.1 l).cast : ℤ)) := by
    funext l
    have h1 : (L : ℤ) ∣ ((((siteOfInt Xf : TorusSite (4 * m * L)) l).cast : ℤ)) - Xf l := by
      have : ((((siteOfInt Xf : TorusSite (4 * m * L)) l).cast : ℤ)) = Xf l % ((4 * m * L : ℕ) : ℤ) := ZMod.coe_intCast (Xf l)
      rw [this]
      have e := Int.emod_add_mul_ediv (Xf l) ((4 * m * L : ℕ) : ℤ)
      refine ⟨-(4 * m * (Xf l / ((4 * m * L : ℕ) : ℤ))), ?_⟩
      push_cast at e ⊢
      linarith
    have h2 : (L : ℤ) ∣ Xf l - ((b.1 l).cast : ℤ) := by
      have e1 : ((Xf l : ℤ) : ZMod (n * L)) = b.1 l - ((((L : ℤ) * ((o l).cast : ℤ) : ℤ)) : ZMod (n * L)) := by
        simp only [hXf]
        rw [ZMod.coe_valMinAbs]
        rfl
      have e2 : ((((b.1 l).cast : ℤ) - (L : ℤ) * ((o l).cast : ℤ) : ℤ) : ZMod (n * L)) = ((Xf l : ℤ) : ZMod (n * L)) := by
        rw [e1]
        push_cast
        simp
      have h3 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp e2
      obtain ⟨w, hw⟩ := h3
      refine ⟨(n : ℤ) * w + -((o l).cast : ℤ), ?_⟩
      push_cast at hw
      linarith
    have h3 : (L : ℤ) ∣ ((((siteOfInt Xf : TorusSite (4 * m * L)) l).cast : ℤ)) - ((b.1 l).cast : ℤ) := by
      have := dvd_add h1 h2
      simpa using this
    have e := offsetFromCentre_add_dvd hLp hL (((b.1 l).cast : ℤ)) _ h3
    rw [add_sub_cancel] at e
    exact e
  change IsTreeOffset L ((fun l => offsetFromCentre L ((((siteOfInt Xf : TorusSite (4 * m * L)) l).cast : ℤ))), b.2) ↔
    IsTreeOffset L ((fun l => offsetFromCentre L (((b.1 l).cast : ℤ))), b.2)
  rw [key]
private theorem reflectedBondPosition_fineBondAt (hL : Odd L) {t u m : ℕ} (hm : 0 < m) (o : TorusSite n) (g v : Fin 4 → ℤ)
    (k : Fin 4) (hv : v ∈ centredCube L) (hg : ∀ i, 2 * |g i| + 1 < (n : ℤ)) :
    reflectedBondPosition L t m o
        (toTorusSite (n * L) (fineBondAt (F := torusFrame L u n) (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).top o) g v k).1, k) =
      fineBondAt (F := reflectedTorusFrame L t m n) 0 g v k := by
  classical
  have hLp : 0 < L := hL.pos
  have hLz : (0 : ℤ) < L := by exact_mod_cast hLp
  have : NeZero (4 * m) := ⟨by omega⟩
  have hN : NeZero (n * L) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
  set F := torusFrame L u n with hF
  have hpb : ∀ i, F.period F.depth i = n * L := period_depth_of_extent (F := F) (n := n) fun _ => rfl
  have hpt : ∀ i, F.period F.top i = n := period_top_of_extent (F := F) (n := n) fun _ => rfl
  have hvb := (_root_.YangMills.Construction.TopLevelSites.mem_centredCube_iff v).mp hv
  let X : Fin 4 → ℤ := fun i => (L : ℤ) * g i + v i
  have hval : ∀ i, ((toTorusSite (n * L) (fineBondAt (F := F) (torusSiteInFrame F F.top o) g v k).1) i -
      (siteOfInt (n := n * L) fun l => (L : ℤ) * ((o l).cast : ℤ)) i).valMinAbs = X i := by
    intro i
    rw [ZMod.valMinAbs_spec]
    constructor
    · have e0 : (fineBondAt (F := F) (torusSiteInFrame F F.top o) g v k).1 =
          siteOfCoords F.depth (fun l => (F.blockSide : ℤ) ^ (F.top - F.depth) *
            siteCoords (torusSiteInFrame F F.top o + siteOfCoords F.top g : F.Cell) l) +
            siteOfCoords F.depth v := rfl
      rw [e0, toTorusSite_add hpb, toTorusSite_siteOfCoords hpb, toTorusSite_siteOfCoords hpb]
      have e1 : (torusSiteInFrame F F.top o + siteOfCoords F.top g : F.Cell) =
          siteOfCoords F.top (fun l => ((o l).cast : ℤ) + g l) := by
        have := _root_.YangMills.Construction.BlockAverages.siteOfCoords_add (F := F) F.top (fun l => ((o l).cast : ℤ)) g
        exact this.symm
      rw [e1]
      have ec : siteCoords (siteOfCoords F.top (fun l => ((o l).cast : ℤ) + g l) : F.Cell) i =
          (((o i).cast : ℤ) + g i) % (n : ℤ) := by
        rw [siteCoords_siteOfCoords, hpt]
      have hs1 : F.top - F.depth = 1 := _root_.YangMills.Construction.TopLevelSites.top_sub_depth
      have hFL : (F.blockSide : ℤ) = (L : ℤ) := rfl
      simp only [siteOfInt, Pi.add_apply]
      rw [ec, hs1, hFL, pow_one]
      have hd : (((L : ℤ) * ((((o i).cast : ℤ) + g i) % (n : ℤ)) + v i - (L : ℤ) * ((o i).cast : ℤ) : ℤ) : ZMod (n * L)) =
          ((X i : ℤ) : ZMod (n * L)) := by
        refine (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr ⟨(((o i).cast : ℤ) + g i) / (n : ℤ), ?_⟩
        have e := Int.emod_add_mul_ediv (((o i).cast : ℤ) + g i) (n : ℤ)
        have e' : (L : ℤ) * ((((o i).cast : ℤ) + g i) % (n : ℤ)) + (L : ℤ) * ((n : ℤ) * ((((o i).cast : ℤ) + g i) / (n : ℤ))) =
            (L : ℤ) * (((o i).cast : ℤ) + g i) := by
          rw [← mul_add, e]
        simp only [X]
        push_cast
        linarith
      rw [← hd]
      push_cast
      ring
    · have hgi := hg i
      have h1 := neg_abs_le (g i)
      have h2 := le_abs_self (g i)
      obtain ⟨h3, h4⟩ := hvb i
      have hh : 2 * halfWidth L ≤ (L : ℤ) - 1 := by
        unfold halfWidth
        omega
      have h5 : (2 * |g i| + 2) * (L : ℤ) ≤ (n : ℤ) * L := mul_le_mul_of_nonneg_right (by omega) hLz.le
      have h6 : (L : ℤ) * g i ≤ (L : ℤ) * |g i| := mul_le_mul_of_nonneg_left h2 hLz.le
      have h7 : (L : ℤ) * (-|g i|) ≤ (L : ℤ) * g i := mul_le_mul_of_nonneg_left h1 hLz.le
      simp only [X, Set.mem_Ioc]
      push_cast
      constructor <;> nlinarith
  have e2 : (fun i => ((toTorusSite (n * L) (fineBondAt (F := F) (torusSiteInFrame F F.top o) g v k).1) i -
      (siteOfInt (n := n * L) fun l => (L : ℤ) * ((o l).cast : ℤ)) i).valMinAbs) = X := funext hval
  unfold reflectedBondPosition
  simp only
  rw [e2]
  set Mf := reflectedTorusFrame L t m n with hMf
  have hpb' : ∀ i, Mf.period Mf.depth i = 4 * m * L := period_depth_of_extent (F := Mf) (n := 4 * m) fun _ => rfl
  have hpt' : ∀ i, Mf.period Mf.top i = 4 * m := period_top_of_extent (F := Mf) (n := 4 * m) fun _ => rfl
  unfold fineBondAt
  refine Prod.ext ?_ rfl
  simp only
  have e3 : (cellCentre Mf.depth ((0 : Mf.Cell) + siteOfCoords Mf.top g) : Mf.Site Mf.depth) =
      siteOfCoords Mf.depth (fun l => (Mf.blockSide : ℤ) ^ (Mf.top - Mf.depth) *
        siteCoords ((0 : Mf.Cell) + siteOfCoords Mf.top g) l) := rfl
  rw [e3, ← _root_.YangMills.Construction.BlockAverages.siteOfCoords_add, siteOfCoords_eq_iff]
  intro i
  rw [hpb']
  have hs1 : Mf.top - Mf.depth = 1 := _root_.YangMills.Construction.TopLevelSites.top_sub_depth
  have hFL : (Mf.blockSide : ℤ) = (L : ℤ) := rfl
  simp only [Pi.add_apply]
  rw [hs1, hFL, pow_one, zero_add, siteCoords_siteOfCoords, hpt']
  have e := Int.emod_add_mul_ediv (g i) ((4 * m : ℕ) : ℤ)
  refine ⟨-(g i / ((4 * m : ℕ) : ℤ)), ?_⟩
  have e' : (L : ℤ) * (g i % ((4 * m : ℕ) : ℤ)) + (L : ℤ) * (((4 * m : ℕ) : ℤ) * (g i / ((4 * m : ℕ) : ℤ))) = (L : ℤ) * g i := by
    rw [← mul_add, e]
  simp only [X]
  push_cast at e' ⊢
  linarith
end Geometry
section Pairings
variable {I X : Type} [Fintype I] [Fintype X]
private theorem dotProduct_mulVec_sum_smul (M : Matrix I I ℝ) (u u' : X → I → ℝ) (l l' : X → ℝ) :
    (∑ b, l b • u b) ⬝ᵥ M.mulVec (∑ b', l' b' • u' b') =
      ∑ b, ∑ b', l b * l' b' * (u b ⬝ᵥ M.mulVec (u' b')) := by
  have h1 : M.mulVec (∑ b', l' b' • u' b') = ∑ b', l' b' • M.mulVec (u' b') := by
    calc M.mulVec (∑ b', l' b' • u' b') = Matrix.mulVecLin M (∑ b', l' b' • u' b') := rfl
      _ = ∑ b', Matrix.mulVecLin M (l' b' • u' b') := map_sum _ _ _
      _ = ∑ b', l' b' • Matrix.mulVecLin M (u' b') := by simp only [map_smul]
      _ = ∑ b', l' b' • M.mulVec (u' b') := rfl
  rw [h1, sum_dotProduct]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [dotProduct_sum]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring
variable [DecidableEq I]
private theorem single_dotProduct_mulVec_single (M : Matrix I I ℝ) (i j : I) :
    (Pi.single i 1 : I → ℝ) ⬝ᵥ M.mulVec (Pi.single j 1) = M i j := by
  rw [single_one_dotProduct, mulVec_single_one_apply]
end Pairings
section Functionals
variable {L : ℕ} [NeZero L] {n : ℕ} [NeZero n]
open Classical in
private theorem reflectedFunctional_bondIndicator (t m : ℕ) (o : TorusSite n) (b : TorusBond (n * L)) (e : Fin 3)
    (p : ChartCoordinate (reflectedTorusFrame L t m n)) :
    reflectedFunctional L t m o (bondIndicator b) e p =
      if p.2 = e ∧ reflectedBondPosition L t m o b = p.1.1 then 1 else 0 := by
  unfold reflectedFunctional bondIndicator
  by_cases h : p.2 = e
  · simp only [h, if_true, true_and]
    rw [Finset.sum_eq_single b]
    · simp
    · intro c _ hc
      simp [hc]
    · intro hb
      exact absurd (Finset.mem_univ b) hb
  · simp [h]
open Classical in
private theorem chartRestriction_bondIndicator (u : ℕ) (b : TorusBond (n * L))
    (p : ↥(chordBonds (finiteCells (torusFrame L u n)))) :
    chartRestriction L u n (bondIndicator b) p =
      if (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth b.1, b.2) = p.1 then 1 else 0 := by
  unfold chartRestriction bondIndicator
  rw [Finset.sum_eq_single b]
  · simp
  · intro c _ hc
    simp [hc]
  · intro hb
    exact absurd (Finset.mem_univ b) hb
open Classical in
private theorem reflectedFunctional_eq_sum (t m : ℕ) (o : TorusSite n) (l : TorusBond (n * L) → ℝ) (e : Fin 3) :
    reflectedFunctional L t m o l e = ∑ b, l b • reflectedFunctional L t m o (bondIndicator b) e := by
  funext p
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, reflectedFunctional_bondIndicator]
  unfold reflectedFunctional
  by_cases h : p.2 = e
  · simp only [h, if_true, true_and, mul_ite, mul_one, mul_zero]
  · simp [h]
open Classical in
private theorem chartRestriction_eq_sum (u : ℕ) (l : TorusBond (n * L) → ℝ) :
    chartRestriction L u n l = ∑ b, l b • chartRestriction L u n (bondIndicator b) := by
  funext p
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, chartRestriction_bondIndicator]
  unfold chartRestriction
  simp only [mul_ite, mul_one, mul_zero]
end Functionals
section Rates
private structure DecayRates (L : ℕ) (lam K δ κ Sh S : ℝ) : Prop where
  lam_pos : 0 < lam
  K_pos : 0 < K
  δ_pos : 0 < δ
  κ_pos : 0 < κ
  κ_le : κ ≤ δ / 8
  Sh_nonneg : 0 ≤ Sh
  S_nonneg : 0 ≤ S
  sum_half : ∀ (F : BlockFrame) (n : ℕ), F.blockSide = L → 2 ≤ n → (∀ i, F.extent i = n) → ∀ z : F.Cell,
    ∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(δ / 2 * (cellSupDist (enclosingCell b.1.1) z : ℝ))) ≤ Sh
  sum_two : ∀ (F : BlockFrame) (n : ℕ), F.blockSide = L → 2 ≤ n → (∀ i, F.extent i = n) → ∀ z : F.Cell,
    ∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(2 * κ * (cellSupDist (enclosingCell b.1.1) z : ℝ))) ≤ S
  sum_one : ∀ (F : BlockFrame) (n : ℕ), F.blockSide = L → 2 ≤ n → (∀ i, F.extent i = n) → ∀ z : F.Cell,
    ∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(κ * (cellSupDist (enclosingCell b.1.1) z : ℝ))) ≤ S
  small : K * (8 * κ / δ) * (3 * Sh) ≤ lam / 2
private theorem exists_decayRates (hS : decaySumOnTorusStatement) {L : ℕ} (hL : Odd L) {lam K δ : ℝ}
    (hl : 0 < lam) (hK : 0 < K) (hδ : 0 < δ) : ∃ κ Sh S : ℝ, DecayRates L lam K δ κ Sh S := by
  obtain ⟨S₁, h₁⟩ := hS L (δ / 2) hL (by positivity)
  set Sh : ℝ := max S₁ 0 with hSh
  have hSh0 : 0 ≤ Sh := le_max_right _ _
  set w : ℝ := lam * δ / (48 * K * (Sh + 1)) with hw
  have hw0 : 0 < w := by positivity
  set κ : ℝ := min (δ / 8) w with hκ
  have hκ0 : 0 < κ := lt_min (by positivity) hw0
  obtain ⟨S₂, h₂⟩ := hS L (2 * κ) hL (by positivity)
  obtain ⟨S₃, h₃⟩ := hS L κ hL hκ0
  refine ⟨κ, Sh, max (max S₂ S₃) 0, hl, hK, hδ, hκ0, min_le_left _ _, hSh0, le_max_right _ _, ?_, ?_, ?_, ?_⟩
  · intro F n hF h2 hn z
    exact ((h₁ F n hF h2 hn z).1).trans (le_max_left _ _)
  · intro F n hF h2 hn z
    exact ((h₂ F n hF h2 hn z).1).trans ((le_max_left _ _).trans (le_max_left _ _))
  · intro F n hF h2 hn z
    exact ((h₃ F n hF h2 hn z).1).trans ((le_max_right _ _).trans (le_max_left _ _))
  · have h1 : K * (8 * κ / δ) * (3 * Sh) ≤ K * (8 * w / δ) * (3 * Sh) := by
      have : κ ≤ w := min_le_right _ _
      have h8 : 8 * κ / δ ≤ 8 * w / δ := by gcongr
      gcongr
    have h2 : K * (8 * w / δ) * (3 * Sh) = lam / 2 * (Sh / (Sh + 1)) := by
      rw [hw]
      field_simp
      ring
    have h3 : Sh / (Sh + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    calc K * (8 * κ / δ) * (3 * Sh) ≤ lam / 2 * (Sh / (Sh + 1)) := h2 ▸ h1
      _ ≤ lam / 2 * 1 := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = lam / 2 := mul_one _
variable {L : ℕ} {lam K δ κ Sh S : ℝ}
private theorem chordBondDist_nonneg (F : BlockFrame) (b b' : ↥(chordBonds (finiteCells F))) : 0 ≤ chordBondDist F b b' := by
  unfold chordBondDist
  positivity
private theorem chordBondDist_comm (F : BlockFrame) (b b' : ↥(chordBonds (finiteCells F))) :
    chordBondDist F b b' = chordBondDist F b' b := by
  unfold chordBondDist
  rw [cellSupDist_comm]
private theorem chordBondDist_triangle (F : BlockFrame) (b c d : ↥(chordBonds (finiteCells F))) :
    chordBondDist F b d ≤ chordBondDist F b c + chordBondDist F c d := by
  unfold chordBondDist
  exact_mod_cast cellSupDist_triangle _ _ _
private theorem chordBondDist_self (F : BlockFrame) (b : ↥(chordBonds (finiteCells F))) : chordBondDist F b b = 0 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.LocalTerms.placementDist_self <;> assumption
private theorem isUnit_and_inv_decay {ι : Type} [Fintype ι] [DecidableEq ι] (hEB : SymmetricSystemGreenDecay)
    (d : ι → ι → ℝ) (M : Matrix ι ι ℝ) {S' : ℝ} (hl : 0 < lam) (hK : 0 < K) (hδ : 0 < δ) (hκ : 0 < κ) (hκδ : κ ≤ δ / 8)
    (h0 : ∀ i, d i i = 0) (hs : ∀ i j, d i j = d j i) (ht : ∀ i j k, d i k ≤ d i j + d j k) (hd : ∀ i j, 0 ≤ d i j)
    (hsym : M.IsSymm) (hc : ∀ x : ι → ℝ, lam * ∑ i, x i ^ 2 ≤ ∑ i, x i * M.mulVec x i)
    (hM : ∀ i j, |M i j| ≤ K * Real.exp (-(δ * d i j)))
    (hS : ∀ i, ∑ j, Real.exp (-(δ / 2 * d i j)) ≤ S') (hsmall : K * (8 * κ / δ) * S' ≤ lam / 2) :
    IsUnit M.det ∧ ∀ i j, |M⁻¹ i j| ≤ 2 / lam * Real.exp (-(2 * κ * d i j)) :=
  ⟨isUnit_det_of_coercive M hl hc, abs_inv_apply_le hEB d M lam κ hl hκ.le h0 hs ht hsym hc
    (weighted_row_sum_le d M hK.le hδ hκ.le hκδ hd hM hS hsmall)⟩
private theorem sum_chartCoordinate {F : BlockFrame} (g : ↥(chordBonds (finiteCells F)) → ℝ) :
    ∑ q : ChartCoordinate F, g q.1 = 3 * ∑ b, g b := by
  rw [Fintype.sum_prod_type]
  simp [Finset.mul_sum]
private theorem inverse_row_bound (R : DecayRates L lam K δ κ Sh S) (hEB : SymmetricSystemGreenDecay) {F : BlockFrame} {n : ℕ}
    (hFL : F.blockSide = L) (h2 : 2 ≤ n) (hn : ∀ i, F.extent i = n) [DecidableEq (ChartCoordinate F)]
    (M : Matrix (ChartCoordinate F) (ChartCoordinate F) ℝ) (hsym : M.IsSymm)
    (hc : ∀ x : ChartCoordinate F → ℝ, lam * ∑ p, x p ^ 2 ≤ ∑ p, x p * M.mulVec x p)
    (hM : ∀ p q : ChartCoordinate F, |M p q| ≤ K * Real.exp (-(δ * chordBondDist F p.1 q.1))) :
    IsUnit M.det ∧ ∀ p, ∑ q, |M⁻¹ p q| ≤ 2 / lam * (3 * S) := by
  have hl := R.lam_pos
  have hsum : ∀ p : ChartCoordinate F, ∑ q : ChartCoordinate F, Real.exp (-(δ / 2 * chordBondDist F p.1 q.1)) ≤ 3 * Sh := by
    intro p
    rw [sum_chartCoordinate fun b => Real.exp (-(δ / 2 * chordBondDist F p.1 b))]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine le_trans (le_of_eq ?_) (R.sum_half F n hFL h2 hn (enclosingCell p.1.1.1))
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [chordBondDist_comm]
    rfl
  obtain ⟨hu, hi⟩ := isUnit_and_inv_decay (κ := κ) hEB (fun p q : ChartCoordinate F => chordBondDist F p.1 q.1) M hl R.K_pos
    R.δ_pos R.κ_pos R.κ_le
    (fun _ => chordBondDist_self F _) (fun _ _ => chordBondDist_comm F _ _) (fun _ _ _ => chordBondDist_triangle F _ _ _)
    (fun _ _ => chordBondDist_nonneg F _ _) hsym hc hM hsum R.small
  refine ⟨hu, fun p => ?_⟩
  calc ∑ q, |M⁻¹ p q| ≤ ∑ q : ChartCoordinate F, 2 / lam * Real.exp (-(2 * κ * chordBondDist F p.1 q.1)) :=
        Finset.sum_le_sum fun q _ => hi p q
    _ = 2 / lam * ∑ q : ChartCoordinate F, Real.exp (-(2 * κ * chordBondDist F p.1 q.1)) := by rw [Finset.mul_sum]
    _ ≤ 2 / lam * (3 * S) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [sum_chartCoordinate fun b => Real.exp (-(2 * κ * chordBondDist F p.1 b))]
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        refine le_trans (le_of_eq ?_) (R.sum_two F n hFL h2 hn (enclosingCell p.1.1.1))
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [chordBondDist_comm]
        rfl
private theorem inverse_single_colour_bounds (R : DecayRates L lam K δ κ Sh S) (hEB : SymmetricSystemGreenDecay)
    {F : BlockFrame} {n : ℕ}
    (hFL : F.blockSide = L) (h2 : 2 ≤ n) (hn : ∀ i, F.extent i = n) [DecidableEq ↥(chordBonds (finiteCells F))]
    (M : Matrix ↥(chordBonds (finiteCells F)) ↥(chordBonds (finiteCells F)) ℝ) (hsym : M.IsSymm)
    (hc : ∀ x : ↥(chordBonds (finiteCells F)) → ℝ, lam * ∑ p, x p ^ 2 ≤ ∑ p, x p * M.mulVec x p)
    (hM : ∀ p q, |M p q| ≤ K * Real.exp (-(δ * chordBondDist F p q))) :
    IsUnit M.det ∧ (∀ p q, |M⁻¹ p q| ≤ 2 / lam * Real.exp (-(2 * κ * chordBondDist F p q))) ∧
      ∀ p, ∑ q, |M p q| ≤ K * Sh := by
  have hl := R.lam_pos
  have hK := R.K_pos
  have hδ := R.δ_pos
  have hsum : ∀ p : ↥(chordBonds (finiteCells F)), ∑ q, Real.exp (-(δ / 2 * chordBondDist F p q)) ≤ Sh := by
    intro p
    refine le_trans (le_of_eq ?_) (R.sum_half F n hFL h2 hn (enclosingCell p.1.1))
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [chordBondDist_comm]
    rfl
  have hsmall : K * (8 * κ / δ) * Sh ≤ lam / 2 := by
    have h0 : 0 ≤ K * (8 * κ / δ) := by
      have := R.κ_pos
      positivity
    have := R.small
    have hS0 := R.Sh_nonneg
    nlinarith
  obtain ⟨hu, hi⟩ := isUnit_and_inv_decay (κ := κ) hEB (fun p q => chordBondDist F p q) M hl hK hδ R.κ_pos R.κ_le
    (chordBondDist_self F) (chordBondDist_comm F) (chordBondDist_triangle F) (chordBondDist_nonneg F) hsym hc hM hsum hsmall
  refine ⟨hu, hi, fun p => ?_⟩
  calc ∑ q, |M p q| ≤ ∑ q, K * Real.exp (-(δ / 2 * chordBondDist F p q)) := by
        refine Finset.sum_le_sum fun q _ => (hM p q).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hK.le)
        have := chordBondDist_nonneg F p q
        nlinarith
    _ = K * ∑ q, Real.exp (-(δ / 2 * chordBondDist F p q)) := by rw [Finset.mul_sum]
    _ ≤ K * Sh := mul_le_mul_of_nonneg_left (hsum p) hK.le
end Rates
section Flat
open scoped Quaternion
variable {L u n : ℕ}
open Classical in
private theorem stepCoordinates_twoCoordinateVariation (b b' : ↥(chordBonds (finiteCells (torusFrame L u n)))) (s s' : ℝ) :
    stepCoordinates (twoCoordinateVariation (F := torusFrame L u n) (b, 0) (b', 0) s s') = pairCoordinates L u n b b' s s' := by
  funext x i
  unfold stepCoordinates pairCoordinates
  by_cases h : (x, i) ∈ chordBonds (finiteCells (torusFrame L u n))
  · rw [dif_pos h]
    apply Subtype.ext
    have e1 : ((⟨(x, i), h⟩ : ↥(chordBonds (finiteCells (torusFrame L u n)))) = b) ↔ (x, i) = b.1 := Subtype.ext_iff
    have e2 : ((⟨(x, i), h⟩ : ↥(chordBonds (finiteCells (torusFrame L u n)))) = b') ↔ (x, i) = b'.1 := Subtype.ext_iff
    have hc : ∀ c : ℝ, (c • unitGenerator : imaginaryQuaternions) = ⟨(⟨0, c, 0, 0⟩ : ℍ[ℝ]), rfl⟩ := by
      intro c
      apply Subtype.ext
      show c • (⟨0, 1, 0, 0⟩ : ℍ[ℝ]) = ⟨0, c, 0, 0⟩
      refine Quaternion.ext (R := ℝ) _ _ ?_ ?_ ?_ ?_ <;> simp
    rw [hc, hc]
    unfold toImaginary twoCoordinateVariation
    refine Quaternion.ext (R := ℝ) _ _ ?_ ?_ ?_ ?_ <;> simp [Prod.ext_iff, e1, e2]
    all_goals first | rfl | (show (0 : ℝ) = 0 + 0; simp)
  · rw [dif_neg h]
    have h1 : (x, i) ≠ b.1 := fun e => h (e ▸ b.2)
    have h2 : (x, i) ≠ b'.1 := fun e => h (e ▸ b'.2)
    simp [h1, h2]
open Classical in
private theorem trivialHessian_eq_submatrix {a ρA : ℝ} {m : ℕ}
    (hz : ∀ b, stepFrame false a ρA m b (uniformField (torusFrame L u n) (torusFrame L u n).top) = 0) :
    trivialHessian a L u n = (frameHessian a ρA m (uniformField (torusFrame L u n) (torusFrame L u n).top)).submatrix
      (fun b => (b, (0 : Fin 3))) (fun b => (b, (0 : Fin 3))) := by
  ext b b'
  simp only [Matrix.submatrix_apply, trivialHessian, frameHessian]
  have e : ∀ s s' : ℝ, coordsAboveFrame false a ρA m (uniformField (torusFrame L u n) (torusFrame L u n).top)
      (twoCoordinateVariation (F := torusFrame L u n) (b, 0) (b', 0) s s') = pairCoordinates L u n b b' s s' := by
    intro s s'
    funext x i
    unfold coordsAboveFrame
    rw [hz, zero_add, stepCoordinates_twoCoordinateVariation]
  simp only [e]
private theorem coercive_submatrix {ι κ' : Type} [Fintype ι] [Fintype κ'] [DecidableEq ι] [DecidableEq κ'] {lam : ℝ}
    (M : Matrix ι ι ℝ) (f : κ' → ι)
    (hf : Function.Injective f) (hc : ∀ x : ι → ℝ, lam * ∑ i, x i ^ 2 ≤ ∑ i, x i * M.mulVec x i) (x : κ' → ℝ) :
    lam * ∑ i, x i ^ 2 ≤ ∑ i, x i * (M.submatrix f f).mulVec x i := by
  let y : ι → ℝ := fun i => ∑ k, if f k = i then x k else 0
  have hy : ∀ k, y (f k) = x k := by
    intro k
    simp only [y, hf.eq_iff]
    simp
  have hoff : ∀ i, i ∉ Finset.univ.image f → y i = 0 := by
    intro i hi
    refine Finset.sum_eq_zero fun k _ => ?_
    have : f k ≠ i := fun e => hi (e ▸ Finset.mem_image_of_mem f (Finset.mem_univ k))
    simp [this]
  have hsum : ∀ g : ι → ℝ, (∀ i, i ∉ Finset.univ.image f → g i = 0) → ∑ i, g i = ∑ k, g (f k) := by
    intro g hg
    rw [← Finset.sum_image (s := Finset.univ) (g := f) (f := g) fun a _ b _ hab => hf hab]
    exact (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => hg i hi).symm
  have h1 := hc y
  have e1 : ∑ i, y i ^ 2 = ∑ k, x k ^ 2 := by
    rw [hsum (fun i => y i ^ 2) fun i hi => by simp [hoff i hi]]
    simp only [hy]
  have e2 : ∑ i, y i * M.mulVec y i = ∑ k, x k * (M.submatrix f f).mulVec x k := by
    rw [hsum (fun i => y i * M.mulVec y i) fun i hi => by simp [hoff i hi]]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hy]
    congr 1
    show ∑ i, M (f k) i * y i = ∑ k', M (f k) (f k') * x k'
    rw [hsum (fun i => M (f k) i * y i) fun i hi => by simp [hoff i hi]]
    simp only [hy]
  rwa [e1, e2] at h1
end Flat
section Torus
open TopLevelSites
variable {L : ℕ} [NeZero L] {n : ℕ} [NeZero n] {lam K δ κ Sh S : ℝ}
private theorem mem_chartBonds_iff (b : TorusBond (n * L)) :
    b ∈ chartBonds L n ↔ ¬ IsAxialTreeBond (F := stepBlockFrame L n) (torusSiteInFrame (stepBlockFrame L n) 0 b.1, b.2) := by
  unfold chartBonds
  simp
private theorem isAxialTreeBond_torusFrame_iff (hL : Odd L) (h2 : 2 ≤ n) (u : ℕ) (x : TorusSite (n * L)) (k : Fin 4) :
    IsAxialTreeBond (F := torusFrame L u n) (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth x, k) ↔
      IsAxialTreeBond (F := stepBlockFrame L n) (torusSiteInFrame (stepBlockFrame L n) 0 x, k) := by
  have : NeZero (n * (torusFrame L u n).blockSide) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
  have : NeZero (n * (stepBlockFrame L n).blockSide) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
  exact (isAxialTreeBond_torusSiteInFrame_iff (F := torusFrame L u n) (n := n) (fun _ => rfl) hL h2 x k).trans
    (isAxialTreeBond_torusSiteInFrame_iff (F := stepBlockFrame L n) (n := n) (fun _ => rfl) hL h2 x k).symm
open Classical in
private theorem reflectedFunctional_bondIndicator_cases (hL : Odd L) {t m : ℕ} (hm : 0 < m) (h2 : 2 ≤ n) (o : TorusSite n)
    (b : TorusBond (n * L)) (e : Fin 3) :
    (b ∈ chartBonds L n ∧ ∃ p : ↥(chordBonds (finiteCells (reflectedTorusFrame L t m n))),
        p.1 = reflectedBondPosition L t m o b ∧
        reflectedFunctional L t m o (bondIndicator b) e = Pi.single (p, e) 1) ∨
      (b ∉ chartBonds L n ∧ reflectedFunctional L t m o (bondIndicator b) e = 0) := by
  have hs : ∀ i, 2 ≤ (reflectedTorusFrame L t m n).extent i := fun _ => by
    show 2 ≤ 4 * m
    omega
  by_cases hb : b ∈ chartBonds L n
  · left
    have hmem : reflectedBondPosition L t m o b ∈ chordBonds (finiteCells (reflectedTorusFrame L t m n)) := by
      rw [mem_chordBonds_finiteCells_iff hL hs, isAxialTreeBond_reflectedBondPosition_iff hL hm h2]
      exact (mem_chartBonds_iff b).mp hb
    refine ⟨hb, ⟨_, hmem⟩, rfl, ?_⟩
    funext p
    rw [reflectedFunctional_bondIndicator, Pi.single_apply]
    congr 1
    refine propext ⟨fun h => ?_, fun h => ?_⟩
    · exact Prod.ext (Subtype.ext h.2.symm) h.1
    · subst h
      exact ⟨rfl, rfl⟩
  · right
    refine ⟨hb, ?_⟩
    funext p
    rw [reflectedFunctional_bondIndicator, if_neg]
    · rfl
    · rintro ⟨_, h⟩
      have h1 : reflectedBondPosition L t m o b ∈ chordBonds (finiteCells (reflectedTorusFrame L t m n)) := h ▸ p.1.2
      rw [mem_chordBonds_finiteCells_iff hL hs, isAxialTreeBond_reflectedBondPosition_iff hL hm h2] at h1
      exact hb ((mem_chartBonds_iff b).mpr h1)
open Classical in
private theorem chartRestriction_bondIndicator_cases (hL : Odd L) (h2 : 2 ≤ n) (u : ℕ) (b : TorusBond (n * L)) :
    (b ∈ chartBonds L n ∧ ∃ p : ↥(chordBonds (finiteCells (torusFrame L u n))),
        p.1 = (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth b.1, b.2) ∧
        chartRestriction L u n (bondIndicator b) = Pi.single p 1) ∨
      (b ∉ chartBonds L n ∧ chartRestriction L u n (bondIndicator b) = 0) := by
  have hs : ∀ i, 2 ≤ (torusFrame L u n).extent i := fun _ => h2
  by_cases hb : b ∈ chartBonds L n
  · left
    have hmem : (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth b.1, b.2) ∈
        chordBonds (finiteCells (torusFrame L u n)) := by
      rw [mem_chordBonds_finiteCells_iff hL hs, isAxialTreeBond_torusFrame_iff hL h2]
      exact (mem_chartBonds_iff b).mp hb
    refine ⟨hb, ⟨_, hmem⟩, rfl, ?_⟩
    funext p
    rw [chartRestriction_bondIndicator, Pi.single_apply]
    congr 1
    refine propext ⟨fun h => Subtype.ext h.symm, fun h => ?_⟩
    subst h
    rfl
  · right
    refine ⟨hb, ?_⟩
    funext p
    rw [chartRestriction_bondIndicator, if_neg]
    · rfl
    · intro h
      have h1 : (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth b.1, b.2) ∈
          chordBonds (finiteCells (torusFrame L u n)) := h ▸ p.2
      rw [mem_chordBonds_finiteCells_iff hL hs, isAxialTreeBond_torusFrame_iff hL h2] at h1
      exact hb ((mem_chartBonds_iff b).mpr h1)
private theorem abs_double_sum_le {X : Type} [Fintype X] (l l' : X → ℝ) (Φ : X → X → ℝ) {E : ℝ}
    (h : ∀ b b', l b ≠ 0 → l' b' ≠ 0 → |Φ b b'| ≤ E) :
    |∑ b, ∑ b', l b * l' b' * Φ b b'| ≤ E * (∑ b, |l b|) * (∑ b, |l' b|) := by
  have h1 : ∀ b b', |l b * l' b' * Φ b b'| ≤ E * (|l b| * |l' b'|) := by
    intro b b'
    by_cases h0 : l b = 0
    · simp [h0]
    by_cases h0' : l' b' = 0
    · simp [h0']
    rw [abs_mul, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (h b b' h0 h0') (by positivity)
  calc |∑ b, ∑ b', l b * l' b' * Φ b b'| ≤ ∑ b, |∑ b', l b * l' b' * Φ b b'| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b, ∑ b', |l b * l' b' * Φ b b'| := Finset.sum_le_sum fun b _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b, ∑ b', E * (|l b| * |l' b'|) := Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun b' _ => h1 b b'
    _ = E * (∑ b, |l b|) * (∑ b, |l' b|) := by
        simp only [← Finset.mul_sum, Finset.sum_mul, mul_assoc]
end Torus
section Bound
open TopLevelSites
variable {L : ℕ} [NeZero L] {n : ℕ} [NeZero n] {lam K δ κ Sh S : ℝ}
open Classical in
private theorem torus_inverse_bounds (hCB : commonBondsOfTwoTori) (hEB : SymmetricSystemGreenDecay) (hL : Odd L)
    (R : DecayRates L lam K δ κ Sh S) {a₀ : ℝ} {u tt m : ℕ} (o : TorusSite n) (hm : 16 ≤ m) (hn : 2 * m + 2 < n)
    (H : Matrix (ChartCoordinate (reflectedTorusFrame L tt m n)) (ChartCoordinate (reflectedTorusFrame L tt m n)) ℝ)
    (hHs : H.IsSymm)
    (hHc : ∀ x : ChartCoordinate (reflectedTorusFrame L tt m n) → ℝ, lam * ∑ p, x p ^ 2 ≤ ∑ p, x p * H.mulVec x p)
    (hHd : ∀ p q : ChartCoordinate (reflectedTorusFrame L tt m n),
      |H p q| ≤ K * Real.exp (-(δ * chordBondDist (reflectedTorusFrame L tt m n) p.1 q.1)))
    (hBs : (trivialHessian a₀ L u n).IsSymm)
    (hBc : ∀ x : ↥(chordBonds (finiteCells (torusFrame L u n))) → ℝ,
      lam * ∑ p, x p ^ 2 ≤ ∑ p, x p * (trivialHessian a₀ L u n).mulVec x p)
    (hBd : ∀ p q, |trivialHessian a₀ L u n p q| ≤ K * Real.exp (-(δ * chordBondDist (torusFrame L u n) p q)))
    {a ρ ε : ℝ} (hρ : 0 ≤ ρ) (hε : 0 ≤ ε) (har : a + ρ < (m : ℝ) / 2)
    (hent : ∀ b b' : TorusBond (n * L), b ∈ chartBonds L n → b' ∈ chartBonds L n →
      (_root_.YangMills.Construction.TorusFields.supDist (parentBlock L b.1) o : ℝ) ≤ a + ρ / 2 → (_root_.YangMills.Construction.TorusFields.supDist (parentBlock L b'.1) o : ℝ) ≤ a + ρ → ∀ e e' : Fin 3,
      |reflectedFunctional L tt m o (bondIndicator b) e ⬝ᵥ
          Matrix.mulVec H (reflectedFunctional L tt m o (bondIndicator b') e') -
        (if e = e' then trivialHessianPairing a₀ L u n (bondIndicator b) (bondIndicator b') else 0)| ≤ ε)
    (l l' : TorusBond (n * L) → ℝ) (e e' : Fin 3)
    (hl : ∀ b, l b ≠ 0 → (_root_.YangMills.Construction.TorusFields.supDist (parentBlock L b.1) o : ℝ) ≤ a)
    (hl' : ∀ b, l' b ≠ 0 → (_root_.YangMills.Construction.TorusFields.supDist (parentBlock L b.1) o : ℝ) ≤ a) :
    |reflectedFunctional L tt m o l e ⬝ᵥ Matrix.mulVec H⁻¹ (reflectedFunctional L tt m o l' e') -
        (if e = e' then stepCovariance a₀ L u n l l' else 0)| ≤
      (2 / lam * (3 * S)) * (ε * (max K (2 / lam) * S) + K * Sh * (max K (2 / lam) * Real.exp (-(2 * κ * ρ))) +
        max K (2 / lam) * max K (2 / lam) * S * Real.exp (-(κ * (ρ / 2)))) * (∑ b, |l b|) * (∑ b, |l' b|) ∧
    |stepCovariance a₀ L u n l l'| ≤ 2 / lam * (∑ b, |l b|) * (∑ b, |l' b|) ∧
    |reflectedFunctional L tt m o l e ⬝ᵥ Matrix.mulVec H⁻¹ (reflectedFunctional L tt m o l' e')| ≤
      (2 / lam * (3 * S)) * (∑ b, |l b|) * (∑ b, |l' b|) := by
  have hm0 : 0 < m := by omega
  have h2 : 2 ≤ n := by omega
  have hlam := R.lam_pos
  have hK0 := R.K_pos
  have hκ0 := R.κ_pos
  have hS0 := R.S_nonneg
  have hSh0 := R.Sh_nonneg
  have hm4 : 2 ≤ 4 * m := by omega
  obtain ⟨hAu, hArow⟩ := inverse_row_bound (n := 4 * m) R hEB (F := reflectedTorusFrame L tt m n) rfl hm4 (fun _ => rfl)
    H hHs hHc hHd
  obtain ⟨hBu, hBi, hBrow⟩ := inverse_single_colour_bounds R hEB (F := torusFrame L u n) (n := n) rfl h2 (fun _ => rfl)
    (trivialHessian a₀ L u n) hBs hBc hBd
  have hnF : ∀ i, (torusFrame L u n).extent i = n := fun _ => rfl
  have hnM : ∀ i, (reflectedTorusFrame L tt m n).extent i = 4 * m := fun _ => rfl
  let Y : (torusFrame L u n).Cell := torusSiteInFrame (torusFrame L u n) (torusFrame L u n).top o
  let Y' : (reflectedTorusFrame L tt m n).Cell := 0
  have hCom := (hCB L hL).2 (torusFrame L u n) (reflectedTorusFrame L tt m n) Y Y' m n (4 * m) rfl rfl hnF hnM hn (by omega)
  let hh := commonBondLeft Y Y' (m / 2)
  let tq := commonBondRight Y Y' (m / 2)
  let back : ↥(commonBondOffsets Y Y' (m / 2)) → TorusBond (n * L) :=
    fun q => (toTorusSite (n * L) (hh q).1.1, (hh q).1.2)
  have hpb : ∀ i, (torusFrame L u n).period (torusFrame L u n).depth i = n * L :=
    period_depth_of_extent (F := torusFrame L u n) (n := n) hnF
  have hτ : ∀ q, (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth (back q).1, (back q).2) = (hh q).1 :=
    fun q => Prod.ext (torusSiteInFrame_toTorusSite hpb _) rfl
  have hoff : ∀ q : ↥(commonBondOffsets Y Y' (m / 2)), q.1.1 ∈ centredCube (2 * (m / 2) + 1) ∧ q.1.2.1 ∈ centredCube L := by
    intro q
    have h1 := (Finset.mem_filter.mp q.2).1
    have h2' := Finset.mem_product.mp h1
    exact ⟨h2'.1, (Finset.mem_product.mp h2'.2).1⟩
  have hplace : ∀ q, reflectedBondPosition L tt m o (back q) = (tq q).1 := by
    intro q
    obtain ⟨hg, hv⟩ := hoff q
    refine reflectedBondPosition_fineBondAt hL hm0 o q.1.1 q.1.2.1 q.1.2.2 hv fun i => ?_
    have hb := (_root_.YangMills.Construction.TopLevelSites.mem_centredCube_iff _).mp hg i
    rw [halfWidth_two_mul_add_one] at hb
    have : |q.1.1 i| ≤ ((m / 2 : ℕ) : ℤ) := abs_le.mpr hb
    have h3 : (((m / 2 : ℕ) : ℤ)) * 2 ≤ m := by
      have := Nat.div_mul_le_self m 2
      exact_mod_cast this
    omega
  have hs2 : ∀ i, 2 ≤ (torusFrame L u n).extent i := fun _ => h2
  have hchart : ∀ q, back q ∈ chartBonds L n := by
    intro q
    rw [mem_chartBonds_iff, ← isAxialTreeBond_torusFrame_iff hL h2 u, hτ q]
    exact (mem_chordBonds_finiteCells_iff hL hs2 _).mp (hh q).2
  have hNZ : NeZero (n * (torusFrame L u n).blockSide) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
  have hblock : ∀ (p : ↥(chordBonds (finiteCells (torusFrame L u n)))) (b : TorusBond (n * L)),
      p.1 = (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth b.1, b.2) →
      (_root_.YangMills.Construction.TorusFields.supDist (parentBlock L b.1) o : ℝ) = cellDistReal (torusFrame L u n) Y (chordBondCell (torusFrame L u n) p) := by
    intro p b hp
    have e1 : enclosingCell p.1.1 = torusSiteInFrame (torusFrame L u n) (torusFrame L u n).top (parentBlock L b.1) := by
      rw [hp]
      exact enclosingCell_torusSiteInFrame (F := torusFrame L u n) (n := n) hnF b.1
    unfold cellDistReal chordBondCell
    rw [e1, cellSupDist_comm, cellSupDist_torusSiteInFrame hnF]
  have hmu : ∀ (q : ↥(commonBondOffsets Y Y' (m / 2))) (e₀ : Fin 3),
      reflectedFunctional L tt m o (bondIndicator (back q)) e₀ = Pi.single (tq q, e₀) 1 := by
    intro q e₀
    rcases reflectedFunctional_bondIndicator_cases (t := tt) hL hm0 h2 o (back q) e₀ with ⟨_, p, hp, hf⟩ | ⟨hb, _⟩
    · have : p = tq q := Subtype.ext (hp.trans (hplace q))
      rw [hf, this]
    · exact absurd (hchart q) hb
  have hfu : ∀ q : ↥(commonBondOffsets Y Y' (m / 2)),
      chartRestriction L u n (bondIndicator (back q)) = Pi.single (hh q) 1 := by
    intro q
    rcases chartRestriction_bondIndicator_cases hL h2 u (back q) with ⟨_, p, hp, hf⟩ | ⟨hb, _⟩
    · have : p = hh q := Subtype.ext (hp.trans (hτ q))
      rw [hf, this]
    · exact absurd (hchart q) hb
  have hzm : ∀ (b : TorusBond (n * L)) (e₀ : Fin 3), b ∉ chartBonds L n →
      reflectedFunctional L tt m o (bondIndicator b) e₀ = 0 := by
    intro b e₀ hb
    rcases reflectedFunctional_bondIndicator_cases (t := tt) hL hm0 h2 o b e₀ with ⟨h, _⟩ | ⟨_, h⟩
    · exact absurd h hb
    · exact h
  have hzf : ∀ b : TorusBond (n * L), b ∉ chartBonds L n → chartRestriction L u n (bondIndicator b) = 0 := by
    intro b hb
    rcases chartRestriction_bondIndicator_cases hL h2 u b with ⟨h, _⟩ | ⟨_, h⟩
    · exact absurd h hb
    · exact h
  have hKc : 0 ≤ max K (2 / lam) := le_trans hK0.le (le_max_left _ _)
  have C : InverseComparison H (trivialHessian a₀ L u n) hh tq (chordBondDist (torusFrame L u n))
      (chordBondDist (reflectedTorusFrame L tt m n))
      (fun c => cellDistReal (torusFrame L u n) Y (chordBondCell (torusFrame L u n) c))
      (fun p => cellDistReal (reflectedTorusFrame L tt m n) Y' (chordBondCell (reflectedTorusFrame L tt m n) p))
      a ρ ε (2 / lam * (3 * S)) (max K (2 / lam)) (K * Sh) S (2 * κ) δ κ :=
    { hA := hAu
      hB := hBu
      h_inj := hCom.injective_left
      t_inj := hCom.injective_right
      standingConstraints := hArow
      R_nonneg := by positivity
      K_nonneg := hKc
      K'_nonneg := by positivity
      S_nonneg := hS0
      ε_nonneg := hε
      κ_nonneg := by positivity
      ρ_nonneg := hρ
      γ_nonneg := hκ0.le
      γ_δ := by linarith [R.κ_le]
      γ_κ := le_refl _
      invB := fun c c' => (hBi c c').trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)
      sumJ := fun c' => R.sum_two _ n rfl h2 hnF (enclosingCell c'.1.1)
      rowB := hBrow
      decA := fun p q e₀ e₁ =>
        (hHd (p, e₀) (q, e₁)).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
      sumP := fun p => by
        refine le_trans (le_of_eq ?_) (R.sum_one _ (4 * m) rfl hm4 hnM (enclosingCell p.1.1))
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [chordBondDist_comm]
        rfl
      dP_nonneg := chordBondDist_nonneg _
      dP_tri := chordBondDist_triangle _
      d_same := hCom.dist_eq
      r_same := hCom.dist_centre_eq
      covJ := fun c hc => by
        by_contra hno
        have h := hCom.far_of_not_common c fun hr => hno hr
        linarith
      covP := fun p hp => by
        by_contra hno
        have h := hCom.far_of_not_common' p fun hr => hno hr
        linarith
      lipJ := fun c c' => by
        have h1 := cellSupDist_triangle Y (enclosingCell c'.1.1) (enclosingCell c.1.1)
        have h3 := cellSupDist_comm (enclosingCell c'.1.1) (enclosingCell c.1.1)
        simp only [cellDistReal, chordBondCell, chordBondDist]
        rw [h3] at h1
        exact_mod_cast h1
      lipP := fun p p' => by
        have h1 := cellSupDist_triangle Y' (enclosingCell p'.1.1) (enclosingCell p.1.1)
        have h3 := cellSupDist_comm (enclosingCell p'.1.1) (enclosingCell p.1.1)
        simp only [cellDistReal, chordBondCell, chordBondDist]
        rw [h3] at h1
        exact_mod_cast h1
      entries := fun q₁ q₂ e₀ e₁ h₁ h₂ => by
        have h := hent (back q₁) (back q₂) (hchart q₁) (hchart q₂)
          (by rw [hblock (hh q₁) (back q₁) (hτ q₁).symm]; exact h₁)
          (by rw [hblock (hh q₂) (back q₂) (hτ q₂).symm]; exact h₂) e₀ e₁
        unfold trivialHessianPairing at h
        rw [hmu, hmu, hfu, hfu, single_dotProduct_mulVec_single, single_dotProduct_mulVec_single] at h
        exact h }
  have hcls : ∀ b : TorusBond (n * L), (_root_.YangMills.Construction.TorusFields.supDist (parentBlock L b.1) o : ℝ) ≤ a →
      (∃ q, back q = b ∧ cellDistReal (torusFrame L u n) Y (chordBondCell (torusFrame L u n) (hh q)) ≤ a) ∨
        b ∉ chartBonds L n := by
    intro b hb
    by_cases hbc : b ∈ chartBonds L n
    · left
      rcases chartRestriction_bondIndicator_cases hL h2 u b with ⟨_, p, hp, _⟩ | ⟨hno, _⟩
      · have hr := hblock p b hp
        have hle : cellDistReal (torusFrame L u n) Y (chordBondCell (torusFrame L u n) p) ≤ a + ρ := by
          rw [← hr]
          linarith
        obtain ⟨q, hq⟩ := C.covJ p hle
        refine ⟨q, ?_, by rw [hq, ← hr]; exact hb⟩
        have e1 : (hh q).1 = (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth b.1, b.2) := by rw [hq, hp]
        show (toTorusSite (n * L) (hh q).1.1, (hh q).1.2) = b
        rw [e1]
        exact Prod.ext (toTorusSite_torusSiteInFrame hpb b.1) rfl
      · exact absurd hbc hno
    · right
      exact hbc
  have eM : reflectedFunctional L tt m o l e ⬝ᵥ Matrix.mulVec H⁻¹ (reflectedFunctional L tt m o l' e') =
      ∑ b, ∑ b', l b * l' b' * (reflectedFunctional L tt m o (bondIndicator b) e ⬝ᵥ
        Matrix.mulVec H⁻¹ (reflectedFunctional L tt m o (bondIndicator b') e')) := by
    rw [reflectedFunctional_eq_sum tt m o l e, reflectedFunctional_eq_sum tt m o l' e', dotProduct_mulVec_sum_smul]
  have eS : stepCovariance a₀ L u n l l' = ∑ b, ∑ b', l b * l' b' * (chartRestriction L u n (bondIndicator b) ⬝ᵥ
      Matrix.mulVec (trivialHessian a₀ L u n)⁻¹ (chartRestriction L u n (bondIndicator b'))) := by
    have e0 : stepCovariance a₀ L u n l l' =
        chartRestriction L u n l ⬝ᵥ Matrix.mulVec (trivialHessian a₀ L u n)⁻¹ (chartRestriction L u n l') := rfl
    rw [e0, chartRestriction_eq_sum u l, chartRestriction_eq_sum u l', dotProduct_mulVec_sum_smul]
  refine ⟨?_, ?_, ?_⟩
  · rw [eM, eS]
    have ed : (∑ b, ∑ b', l b * l' b' * (reflectedFunctional L tt m o (bondIndicator b) e ⬝ᵥ
          Matrix.mulVec H⁻¹ (reflectedFunctional L tt m o (bondIndicator b') e'))) -
        (if e = e' then ∑ b, ∑ b', l b * l' b' * (chartRestriction L u n (bondIndicator b) ⬝ᵥ
          Matrix.mulVec (trivialHessian a₀ L u n)⁻¹ (chartRestriction L u n (bondIndicator b'))) else 0) =
        ∑ b, ∑ b', l b * l' b' * ((reflectedFunctional L tt m o (bondIndicator b) e ⬝ᵥ
          Matrix.mulVec H⁻¹ (reflectedFunctional L tt m o (bondIndicator b') e')) -
          (if e = e' then chartRestriction L u n (bondIndicator b) ⬝ᵥ
            Matrix.mulVec (trivialHessian a₀ L u n)⁻¹ (chartRestriction L u n (bondIndicator b')) else 0)) := by
      by_cases he : e = e'
      · simp only [he, if_true, mul_sub, Finset.sum_sub_distrib]
      · simp only [he, if_false, sub_zero]
    rw [ed]
    have hE0 : 0 ≤ (2 / lam * (3 * S)) * (ε * (max K (2 / lam) * S) +
        K * Sh * (max K (2 / lam) * Real.exp (-(2 * κ * ρ))) +
        max K (2 / lam) * max K (2 / lam) * S * Real.exp (-(κ * (ρ / 2)))) := by positivity
    refine abs_double_sum_le l l' _ fun b b' hb hb' => ?_
    rcases hcls b (hl b hb) with ⟨q₁, rfl, h₁⟩ | hn₁
    · rcases hcls b' (hl' b' hb') with ⟨q₂, rfl, h₂⟩ | hn₂
      · rw [hmu, hmu, hfu, hfu, single_dotProduct_mulVec_single, single_dotProduct_mulVec_single]
        exact C.abs_inv_sub_le q₁ q₂ e e' h₁ h₂
      · rw [hzm b' e' hn₂, hzf b' hn₂]
        simpa using hE0
    · rw [hzm b e hn₁, hzf b hn₁]
      simpa using hE0
  · rw [eS]
    have hcl : 0 ≤ 2 / lam := by positivity
    refine abs_double_sum_le l l' _ fun b b' _ _ => ?_
    rcases chartRestriction_bondIndicator_cases hL h2 u b with ⟨_, p, _, hp⟩ | ⟨_, hp⟩
    · rcases chartRestriction_bondIndicator_cases hL h2 u b' with ⟨_, p', _, hp'⟩ | ⟨_, hp'⟩
      · rw [hp, hp', single_dotProduct_mulVec_single]
        refine (hBi p p').trans ?_
        have h1 : Real.exp (-(2 * κ * chordBondDist (torusFrame L u n) p p')) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          have := chordBondDist_nonneg _ p p'
          have h3 : 0 ≤ 2 * κ * chordBondDist (torusFrame L u n) p p' := by positivity
          linarith
        nlinarith
      · rw [hp']
        simpa using hcl
    · rw [hp]
      simpa using hcl
  · rw [eM]
    have hcl : 0 ≤ 2 / lam * (3 * S) := by positivity
    refine abs_double_sum_le l l' _ fun b b' _ _ => ?_
    rcases reflectedFunctional_bondIndicator_cases (t := tt) hL hm0 h2 o b e with ⟨_, p, _, hp⟩ | ⟨_, hp⟩
    · rcases reflectedFunctional_bondIndicator_cases (t := tt) hL hm0 h2 o b' e' with ⟨_, p', _, hp'⟩ | ⟨_, hp'⟩
      · rw [hp, hp', single_dotProduct_mulVec_single]
        exact (Finset.single_le_sum (f := fun q => |H⁻¹ (p, e) q|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ (p', e'))).trans (hArow (p, e))
      · rw [hp']
        simpa using hcl
    · rw [hp]
      simpa using hcl
end Bound
section Numbers
private theorem eventually_side_large : ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
    16 ≤ ⌊x ^ ((1 : ℝ) / 20)⌋₊ ∧
      20 * x ^ ((1 : ℝ) / 90) + 2 * (⌊Real.log x ^ 3⌋₊ : ℝ) < (⌊x ^ ((1 : ℝ) / 20)⌋₊ : ℝ) / 2 := by
  have h1 : ∀ᶠ x : ℝ in Filter.atTop, Real.log x ≤ x ^ ((1 : ℝ) / 720) := by
    have h := isLittleO_log_rpow_atTop (r := (1 : ℝ) / 720) (by norm_num)
    have h2 := h.bound (c := 1) (by norm_num)
    filter_upwards [h2, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have e1 : 0 ≤ Real.log x := Real.log_nonneg hx1
    have e2 : 0 ≤ x ^ ((1 : ℝ) / 720) := Real.rpow_nonneg (by linarith) _
    rw [Real.norm_of_nonneg e1, Real.norm_of_nonneg e2, one_mul] at hx
    exact hx
  have h2 : ∀ᶠ x : ℝ in Filter.atTop, (2 : ℝ) ≤ x ^ ((1 : ℝ) / 720) :=
    (tendsto_rpow_atTop (by norm_num)).eventually_ge_atTop 2
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.mp (h1.and h2)
  refine ⟨max x₁ 1, le_max_right _ _, fun x hx => ?_⟩
  obtain ⟨hl, hw⟩ := hx₁ x ((le_max_left _ _).trans hx)
  have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 ≤ x := by linarith
  set w : ℝ := x ^ ((1 : ℝ) / 720) with hwd
  have e20 : x ^ ((1 : ℝ) / 20) = w ^ 36 := by
    rw [hwd, ← Real.rpow_natCast, ← Real.rpow_mul hx0]
    norm_num
  have e90 : x ^ ((1 : ℝ) / 90) = w ^ 8 := by
    rw [hwd, ← Real.rpow_natCast, ← Real.rpow_mul hx0]
    norm_num
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hfl : ((⌊Real.log x ^ 3⌋₊ : ℕ) : ℝ) ≤ w ^ 3 :=
    (Nat.floor_le (by positivity)).trans (pow_le_pow_left₀ hlog0 hl 3)
  have hw3 : w ^ 3 ≤ w ^ 8 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hw28 : (2 : ℝ) ^ 28 ≤ w ^ 28 := pow_le_pow_left₀ (by norm_num) hw 28
  have hw8 : (2 : ℝ) ^ 8 ≤ w ^ 8 := pow_le_pow_left₀ (by norm_num) hw 8
  have hsplit : w ^ 36 = w ^ 28 * w ^ 8 := by ring
  have hbig : (2 : ℝ) ^ 28 * w ^ 8 ≤ w ^ 36 := by
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right hw28 (by positivity)
  have hfloor : w ^ 36 - 1 < (⌊w ^ 36⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one (w ^ 36)
    linarith
  rw [e20, e90]
  constructor
  · have : (16 : ℝ) ≤ (⌊w ^ 36⌋₊ : ℝ) := by nlinarith
    exact_mod_cast this
  · nlinarith
private theorem clusterRange_large {x : ℝ} (hx : (2 : ℝ) ^ 1600 ≤ x) : 2 ^ 15 ≤ clusterRange x := by
  have h1 : ((2 : ℝ) ^ 1600) ^ ((1 : ℝ) / 100) ≤ x ^ ((1 : ℝ) / 100) :=
    Real.rpow_le_rpow (by positivity) hx (by norm_num)
  have h2 : ((2 : ℝ) ^ 1600) ^ ((1 : ℝ) / 100) = 2 ^ 16 := by
    rw [← Real.rpow_natCast 2 1600, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast 2 16]
    norm_num
  have h3 : x ^ ((1 : ℝ) / 100) ≤ (clusterRange x : ℝ) := Nat.le_ceil _
  have h4 : ((2 ^ 15 : ℕ) : ℝ) ≤ (clusterRange x : ℝ) := by
    push_cast
    rw [h2] at h1
    nlinarith
  exact_mod_cast h4
end Numbers
section Assembly
private theorem bracket_bound {Rr c1 P Q Q' s E E₁ E₂ E₃ : ℝ} (hR : 0 ≤ Rr) (hc : 0 ≤ c1) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hQ' : 0 ≤ Q') (hs : 0 ≤ s) (hE : 0 ≤ E) (h₁ : E₁ ≤ E) (h₂ : E₂ ≤ E) (h₃ : E₃ ≤ E) :
    Rr * ((c1 * s + E₁) * P + Q * E₂ + Q' * E₃) ≤ Rr * (c1 * P + P + Q + Q') * (s + E) := by
  have h0 : (c1 * s + E₁) * P + Q * E₂ + Q' * E₃ ≤ (c1 * P + P + Q + Q') * (s + E) := by
    have a1 : E₁ * P ≤ E * P := mul_le_mul_of_nonneg_right h₁ hP
    have a2 : Q * E₂ ≤ Q * E := mul_le_mul_of_nonneg_left h₂ hQ
    have a3 : Q' * E₃ ≤ Q' * E := mul_le_mul_of_nonneg_left h₃ hQ'
    have a4 : 0 ≤ c1 * P * E := by positivity
    have a5 : 0 ≤ P * s := by positivity
    have a6 : 0 ≤ Q * s := by positivity
    have a7 : 0 ≤ Q' * s := by positivity
    nlinarith
  calc Rr * ((c1 * s + E₁) * P + Q * E₂ + Q' * E₃) ≤ Rr * ((c1 * P + P + Q + Q') * (s + E)) :=
        mul_le_mul_of_nonneg_left h0 hR
    _ = Rr * (c1 * P + P + Q + Q') * (s + E) := by ring
private theorem uniformField_isSmallCurvature {F : BlockFrame} {σ : ℝ} (hσ : 0 < σ) :
    IsSmallCurvature σ (uniformField F F.top) := by apply _root_.YangMills.Construction.BlockMeans.SegmentMean.isSmallCurvature_uniformField <;> assumption
open Classical in
private theorem comparison_at (hK : frameHessianCoerciveLocalStatement) (hMc : mirrorOfColdBallSmallCurvatureStatement)
    (hFl : stepFramesAtUniformTop) (hEB : SymmetricSystemGreenDecay) (hS : decaySumOnTorusStatement)
    (hCB : commonBondsOfTwoTori) (Tb : ParameterAssignment) (y : ℝ) (hD : Tb.Admissible) (hCS : Tb.ColdStepHolds)
    (hy : (2 : ℝ) ^ 1600 ≤ y) (hEn : reflectedHessianEntriesAt Tb y) :
    reflectedHessianComparisonAt Tb y := by
  obtain ⟨c, nss, hTies, -⟩ := hCS
  obtain ⟨C₀, hC₀, hK1⟩ := hK Tb c hD hTies
  obtain ⟨C₁, c₁, x₁, hc₁, hEnt⟩ := hEn
  have hLo := hD.L_odd
  obtain ⟨hδ, -, hl, -⟩ := hD.chain
  obtain ⟨κ, Sh, S, R⟩ := exists_decayRates hS hLo hl hC₀ hδ
  obtain ⟨xN, -, hxN⟩ := eventually_side_large
  have hκ0 := R.κ_pos
  have hS0 := R.S_nonneg
  have hSh0 := R.Sh_nonneg
  have hσ := hD.σ_pos
  set Kc : ℝ := max C₀ (2 / Tb.lam) with hKc
  have hKc0 : 0 ≤ Kc := le_trans hC₀.le (le_max_left _ _)
  set Rr : ℝ := 2 / Tb.lam * (3 * S) with hRr
  have hRr0 : 0 ≤ Rr := by positivity
  set Cm : ℝ := Rr * (|C₁| * (Kc * S) + Kc * S + C₀ * Sh * Kc + Kc * Kc * S) with hCm
  refine ⟨max Cm (max (2 / Tb.lam) Rr), min c₁ (κ / 2), max x₁ xN, lt_min hc₁ (by positivity), ?_⟩
  intro T β k n _ nn j o V g s l l' e e' hOn hj hs hCold hNear hsup
  have hOn' : IsLocalChainAbove Tb y T β k n nn x₁ :=
    { hOn with floor_le := (le_max_left _ _).trans hOn.floor_le }
  obtain ⟨hm16, hnum⟩ := hxN _ ((le_max_right _ _).trans hOn.floor_le)
  have hm : 16 ≤ localBlockSide (Tb.stepParameters y) β k := hm16
  have hρ0 : 0 ≤ localLogScale (Tb.stepParameters y) β k := Nat.cast_nonneg _
  have hside : 2 ^ 10 * (localBlockSide (Tb.stepParameters y) β k : ℝ) ≤ (n : ℝ) := hOn.side_ge
  have hside' : 2 ^ 10 * localBlockSide (Tb.stepParameters y) β k ≤ n := by exact_mod_cast hside
  have hn : 2 * localBlockSide (Tb.stepParameters y) β k + 2 < n := by omega
  have hnn0 : (0 : ℝ) ≤ nn := by linarith [hOn.one_le]
  have hLpos : (1 : ℝ) ≤ (Tb.stepParameters y).side := by exact_mod_cast hLo.pos
  have hpow : (1 : ℝ) ≤ ((Tb.stepParameters y).side : ℝ) ^ (j + 1) := one_le_pow₀ hLpos
  have hfrac : 20 * nn / ((Tb.stepParameters y).side : ℝ) ^ (j + 1) ≤ 20 * nn := div_le_self (by positivity) hpow
  have hbelow : 20 * nn ≤ 20 * (couplingFlow (Tb.stepParameters y) β k).1 ^ ((1 : ℝ) / 90) := by
    have := hOn.le_rpow
    linarith
  have har : ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) (j + 1) -
      3 * localLogScale (Tb.stepParameters y) β k + localLogScale (Tb.stepParameters y) β k <
      (localBlockSide (Tb.stepParameters y) β k : ℝ) / 2 := by
    have h1 : ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) (j + 1) =
        20 * nn / ((Tb.stepParameters y).side : ℝ) ^ (j + 1) + 4 * localLogScale (Tb.stepParameters y) β k := rfl
    have h2 : 20 * (couplingFlow (Tb.stepParameters y) β k).1 ^ ((1 : ℝ) / 90) +
        2 * localLogScale (Tb.stepParameters y) β k < (localBlockSide (Tb.stepParameters y) β k : ℝ) / 2 := hnum
    rw [h1]
    linarith
  have hjle : k + j ≤ k + 2 * chainDepth (couplingFlow (Tb.stepParameters y) β k).1 := by
    have : j < chainDepth (couplingFlow (Tb.stepParameters y) β k).1 := hj
    omega
  have hTab := hOn.onFamily.onFamily (k + j) hjle
  have eρ : (T.stage (k + j)).anchorRadius = Tb.ρA := hTab.anchorRadius_eq
  have hm₀ : 16 ≤ (T.stage (k + j)).toStepSetup.frameReach := by
    have h1 : 2 ^ 15 ≤ clusterRange (T.stage (k + j)).coupling := clusterRange_large (hy.trans hTab.le_coupling)
    show 16 ≤ clusterRange (T.stage (k + j)).coupling / 2 ^ 11
    omega
  have hm0 : 0 < localBlockSide (Tb.stepParameters y) β k := by omega
  have hcoldM := hMc (Tb.stepParameters y).side (T.stage (k + j)).depth (localBlockSide (Tb.stepParameters y) β k) n o V
    (restrictGauge g (supBall o (ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) (j + 1))))
    Tb.threshold hσ hm0 hn hLo hCold
  have hMt : IsBlockTorus Tb.side
      (reflectedTorusFrame (Tb.stepParameters y).side (T.stage (k + j)).depth (localBlockSide (Tb.stepParameters y) β k) n) :=
    ⟨rfl, 4 * localBlockSide (Tb.stepParameters y) β k, by omega, fun _ => rfl⟩
  have hKM := hK1 _ (T.stage (k + j)).toStepSetup.frameReach _ hMt hm₀ hcoldM
  rw [← eρ] at hKM
  obtain ⟨hHs, hHc, hHd⟩ := hKM
  have hn64 : 64 ≤ n := by omega
  have hFt : IsBlockTorus Tb.side (torusFrame (Tb.stepParameters y).side (k + j) n) := ⟨rfl, n, hn64, fun _ => rfl⟩
  obtain ⟨h₀s, h₀c, h₀d⟩ := hK1 _ 16 _ hFt le_rfl (uniformField_isSmallCurvature hσ)
  have hz : ∀ b, stepFrame false Tb.coupling Tb.ρA 16 b
      (uniformField (torusFrame (Tb.stepParameters y).side (k + j) n)
        (torusFrame (Tb.stepParameters y).side (k + j) n).top) = 0 := by
    have h := (hFl Tb.coupling Tb.side c 16 hD.a_ge hLo hTies.2.2.2.2.2.2.2 le_rfl _ false hFt).1
    rw [hTies.2.2.1] at h
    exact h
  have hB := trivialHessian_eq_submatrix (L := (Tb.stepParameters y).side) (u := k + j) (n := n) hz
  have hBs : (trivialHessian (Tb.stepParameters y).coupling (Tb.stepParameters y).side (k + j) n).IsSymm := by
    show (trivialHessian Tb.coupling (Tb.stepParameters y).side (k + j) n).IsSymm
    rw [hB]
    exact h₀s.submatrix _
  have hBc : ∀ x : ↥(chordBonds (finiteCells (torusFrame (Tb.stepParameters y).side (k + j) n))) → ℝ,
      Tb.lam * ∑ p, x p ^ 2 ≤
        ∑ p, x p * (trivialHessian (Tb.stepParameters y).coupling (Tb.stepParameters y).side (k + j) n).mulVec x p := by
    intro x
    show _ ≤ ∑ p, x p * (trivialHessian Tb.coupling (Tb.stepParameters y).side (k + j) n).mulVec x p
    rw [hB]
    exact coercive_submatrix _ _ (fun b b' h => (Prod.ext_iff.mp h).1) h₀c x
  have hBd : ∀ p q, |trivialHessian (Tb.stepParameters y).coupling (Tb.stepParameters y).side (k + j) n p q| ≤
      C₀ * Real.exp (-(Tb.δ₁ * chordBondDist (torusFrame (Tb.stepParameters y).side (k + j) n) p q)) := by
    intro p q
    show |trivialHessian Tb.coupling (Tb.stepParameters y).side (k + j) n p q| ≤ _
    rw [hB]
    exact h₀d (p, 0) (q, 0)
  have hε : 0 ≤ |C₁| * s + Real.exp (-(c₁ * localLogScale (Tb.stepParameters y) β k)) := by positivity
  have hent : ∀ b b' : TorusBond (n * (Tb.stepParameters y).side), b ∈ chartBonds (Tb.stepParameters y).side n →
      b' ∈ chartBonds (Tb.stepParameters y).side n →
      (supDist (parentBlock (Tb.stepParameters y).side b.1) o : ℝ) ≤
        ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) (j + 1) -
        3 * localLogScale (Tb.stepParameters y) β k + localLogScale (Tb.stepParameters y) β k / 2 →
      (_root_.YangMills.Construction.TorusFields.supDist (parentBlock (Tb.stepParameters y).side b'.1) o : ℝ) ≤
        ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) (j + 1) -
        3 * localLogScale (Tb.stepParameters y) β k + localLogScale (Tb.stepParameters y) β k → ∀ e₀ e₁ : Fin 3,
      |reflectedFunctional (Tb.stepParameters y).side (T.stage (k + j)).depth (localBlockSide (Tb.stepParameters y) β k) o
          (bondIndicator b) e₀ ⬝ᵥ
        Matrix.mulVec (frameHessian (Tb.stepParameters y).coupling (T.stage (k + j)).anchorRadius
          (T.stage (k + j)).toStepSetup.frameReach
          (reflectedTopField (Tb.stepParameters y).side (T.stage (k + j)).depth (localBlockSide (Tb.stepParameters y) β k) o
            (TorusFields.gaugeTransform (restrictGauge g (supBall o (ballRadius (Tb.stepParameters y).side nn
              (localLogScale (Tb.stepParameters y) β k) (j + 1)))) V)))
          (reflectedFunctional (Tb.stepParameters y).side (T.stage (k + j)).depth (localBlockSide (Tb.stepParameters y) β k) o
            (bondIndicator b') e₁) -
        (if e₀ = e₁ then trivialHessianPairing (Tb.stepParameters y).coupling (Tb.stepParameters y).side (k + j) n
          (bondIndicator b) (bondIndicator b') else 0)| ≤
      |C₁| * s + Real.exp (-(c₁ * localLogScale (Tb.stepParameters y) β k)) := by
    intro b b' hb hb' h₁ h₂ e₀ e₁
    have m₁ : parentBlock (Tb.stepParameters y).side b.1 ∈ supBall o (ballRadius (Tb.stepParameters y).side nn
        (localLogScale (Tb.stepParameters y) β k) (j + 1) - 5 / 2 * localLogScale (Tb.stepParameters y) β k) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      linarith
    have m₂ : parentBlock (Tb.stepParameters y).side b'.1 ∈ supBall o (ballRadius (Tb.stepParameters y).side nn
        (localLogScale (Tb.stepParameters y) β k) (j + 1) - 2 * localLogScale (Tb.stepParameters y) β k) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      linarith
    refine (hEnt T β k n nn j o V g s b b' e₀ e₁ hOn' hj hs hCold hNear hb hb' m₁ m₂).trans ?_
    have h1 : Real.exp (-(c₁ * (_root_.YangMills.Construction.TorusFields.supDist b.1 b'.1 : ℝ))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ c₁ * (_root_.YangMills.Construction.TorusFields.supDist b.1 b'.1 : ℝ) := by positivity
      linarith
    have h2 : C₁ * s * Real.exp (-(c₁ * (_root_.YangMills.Construction.TorusFields.supDist b.1 b'.1 : ℝ))) ≤ |C₁| * s := by
      have h3 : C₁ * s ≤ |C₁| * s := mul_le_mul_of_nonneg_right (le_abs_self _) hs
      have h4 : 0 ≤ |C₁| * s := by positivity
      calc C₁ * s * Real.exp (-(c₁ * (_root_.YangMills.Construction.TorusFields.supDist b.1 b'.1 : ℝ))) ≤ |C₁| * s * Real.exp (-(c₁ * (_root_.YangMills.Construction.TorusFields.supDist b.1 b'.1 : ℝ))) :=
            mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
        _ ≤ |C₁| * s * 1 := mul_le_mul_of_nonneg_left h1 h4
        _ = |C₁| * s := mul_one _
    linarith
  have hsupp : ∀ (f : TorusBond (n * (Tb.stepParameters y).side) → ℝ),
      (∀ b, parentBlock (Tb.stepParameters y).side b.1 ∉ supBall o (ballRadius (Tb.stepParameters y).side nn
        (localLogScale (Tb.stepParameters y) β k) (j + 1) - 3 * localLogScale (Tb.stepParameters y) β k) → f b = 0) →
      ∀ b, f b ≠ 0 →
      (supDist (parentBlock (Tb.stepParameters y).side b.1) o : ℝ) ≤
        ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) (j + 1) -
        3 * localLogScale (Tb.stepParameters y) β k := by
    intro f hf b hb
    by_contra hcon
    apply hb
    refine hf b fun hmem => hcon ?_
    exact (Finset.mem_filter.mp hmem).2
  obtain ⟨b1, b2, b3⟩ := torus_inverse_bounds hCB hEB hLo R (a₀ := (Tb.stepParameters y).coupling) (u := k + j)
    (tt := (T.stage (k + j)).depth) o hm hn _ hHs hHc hHd hBs hBc hBd
    (a := ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) (j + 1) -
      3 * localLogScale (Tb.stepParameters y) β k)
    hρ0 hε har hent l l' e e' (hsupp l fun b h => (hsup b h).1) (hsupp l' fun b h => (hsup b h).2)
  have hA₁ : 0 ≤ ∑ b, |l b| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hA₂ : 0 ≤ ∑ b, |l' b| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hCm' : Cm ≤ max Cm (max (2 / Tb.lam) Rr) := le_max_left _ _
  have hC2 : 2 / Tb.lam ≤ max Cm (max (2 / Tb.lam) Rr) := (le_max_left _ _).trans (le_max_right _ _)
  have hC3 : Rr ≤ max Cm (max (2 / Tb.lam) Rr) := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨?_, ?_, ?_⟩
  · refine b1.trans ?_
    set ρ := localLogScale (Tb.stepParameters y) β k with hρdef
    set E := Real.exp (-(min c₁ (κ / 2) * ρ)) with hEdef
    have hmin1 : min c₁ (κ / 2) ≤ c₁ := min_le_left _ _
    have hmin2 : min c₁ (κ / 2) ≤ κ / 2 := min_le_right _ _
    have hE1 : Real.exp (-(c₁ * ρ)) ≤ E := Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right hmin1 hρ0))
    have hE2 : Real.exp (-(2 * κ * ρ)) ≤ E :=
      Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right (by linarith) hρ0))
    have hE3 : Real.exp (-(κ * (ρ / 2))) ≤ E := by
      refine Real.exp_le_exp.mpr ?_
      have : min c₁ (κ / 2) * ρ ≤ κ / 2 * ρ := mul_le_mul_of_nonneg_right hmin2 hρ0
      nlinarith
    have hE0 : 0 ≤ E := (Real.exp_pos _).le
    have hbr := bracket_bound (Rr := Rr) (c1 := |C₁|) (P := Kc * S) (Q := C₀ * Sh * Kc) (Q' := Kc * Kc * S) (s := s) (E := E)
      (E₁ := Real.exp (-(c₁ * ρ))) (E₂ := Real.exp (-(2 * κ * ρ))) (E₃ := Real.exp (-(κ * (ρ / 2)))) hRr0 (abs_nonneg _)
      (by positivity) (by positivity) (by positivity) hs hE0 hE1 hE2 hE3
    have hfin : Rr * ((|C₁| * s + Real.exp (-(c₁ * ρ))) * (Kc * S) + C₀ * Sh * (Kc * Real.exp (-(2 * κ * ρ))) +
        Kc * Kc * S * Real.exp (-(κ * (ρ / 2)))) ≤ max Cm (max (2 / Tb.lam) Rr) * (s + E) := by
      have e1 : Rr * ((|C₁| * s + Real.exp (-(c₁ * ρ))) * (Kc * S) + C₀ * Sh * (Kc * Real.exp (-(2 * κ * ρ))) +
          Kc * Kc * S * Real.exp (-(κ * (ρ / 2)))) =
          Rr * ((|C₁| * s + Real.exp (-(c₁ * ρ))) * (Kc * S) + C₀ * Sh * Kc * Real.exp (-(2 * κ * ρ)) +
          Kc * Kc * S * Real.exp (-(κ * (ρ / 2)))) := by ring
      rw [e1]
      refine hbr.trans ?_
      exact mul_le_mul_of_nonneg_right hCm' (by positivity)
    calc Rr * ((|C₁| * s + Real.exp (-(c₁ * ρ))) * (Kc * S) + C₀ * Sh * (Kc * Real.exp (-(2 * κ * ρ))) +
          Kc * Kc * S * Real.exp (-(κ * (ρ / 2)))) * (∑ b, |l b|) * (∑ b, |l' b|)
        ≤ max Cm (max (2 / Tb.lam) Rr) * (s + E) * (∑ b, |l b|) * (∑ b, |l' b|) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfin hA₁) hA₂
      _ = max Cm (max (2 / Tb.lam) Rr) * (∑ b, |l b|) * (∑ b, |l' b|) * (s + E) := by ring
  · refine b2.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC2 hA₁) hA₂
  · refine b3.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC3 hA₁) hA₂
end Assembly
end ReflectedHessianComparison
open ReflectedHessianComparison in
theorem reflectedHessianComparison_holds (hE : reflectedHessianEntriesStatement)
    (hK : frameHessianCoerciveLocalStatement) (hMc : mirrorOfColdBallSmallCurvatureStatement)
    (hFl : stepFramesAtUniformTop) (hEB : SymmetricSystemGreenDecay) (hS : decaySumOnTorusStatement)
    (hCB : commonBondsOfTwoTori) : reflectedHessianComparisonStatement := by
  intro a ha
  obtain ⟨L₀, rt₀, C₀, hrt, hall⟩ := hE a ha
  refine ⟨L₀, rt₀, C₀, hrt, fun L hLodd hLL T hTa hTL hD hCS hCH hrt' hCd => ?_⟩
  obtain ⟨y₀, hy₀⟩ := hall L hLodd hLL T hTa hTL hD hCS hCH hrt' hCd
  refine ⟨max y₀ (2 ^ 1600), fun y hy hRow hW => ?_⟩
  exact comparison_at hK hMc hFl hEB hS hCB T y hD hCS ((le_max_right _ _).trans hy)
    (hy₀ y ((le_max_left _ _).trans hy) hRow hW)
end ResponseInTheExpansion
end YangMills.Construction
end
