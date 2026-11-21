import YangMills.Construction.FormsOnATorus.KernelOfTheCurlOnABoxProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.BoxGaussian
open TorusFields TorusLumps RenormalizationStepParameters StepSettings ResponseInTheExpansion WeightedResponses BlockAverages
  LatticeFractionalIntegration ColdStepAtMirrorFrames
section Algebra
open Matrix
variable {ι π σ : Type} [Fintype ι] [DecidableEq ι]
omit [Fintype ι] [DecidableEq ι] in
private theorem sum_comm_three (P Q : Finset π) (B : Finset ι) (F : π → π → ι → ℝ) :
    ∑ p ∈ P, ∑ p' ∈ Q, ∑ b ∈ B, F p p' b = ∑ b ∈ B, ∑ p ∈ P, ∑ p' ∈ Q, F p p' b :=
  (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm
omit [DecidableEq ι] in
private theorem kernelQuad_eq_dotProduct (Mi : Matrix ι ι ℝ) (P : Finset π) (c : π → ι → ℝ) (u : π → ℝ) :
    ∑ p ∈ P, ∑ p' ∈ P, u p * (∑ b, ∑ b', c p b * Mi b b' * c p' b') * u p' =
      (fun b => ∑ p ∈ P, u p * c p b) ⬝ᵥ (Mi *ᵥ fun b => ∑ p ∈ P, u p * c p b) := by
  have h1 : ∑ p ∈ P, ∑ p' ∈ P, u p * (∑ b, ∑ b', c p b * Mi b b' * c p' b') * u p' =
      ∑ p ∈ P, ∑ p' ∈ P, ∑ b, ∑ b', (u p * c p b) * Mi b b' * (u p' * c p' b') := by
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun p' _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b' _ => ?_
    ring
  rw [h1, sum_comm_three]
  simp only [dotProduct, Matrix.mulVec]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [sum_comm_three, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p' _ => ?_
  ring
private theorem kernelQuad_bounds (M : Matrix ι ι ℝ) (hdet : M.det ≠ 0) (P : Finset π) (c : π → ι → ℝ) (u : π → ℝ)
    (κ : ℝ) (hκ : 0 < κ)
    (hlow : ∀ f : ι → ℝ, κ * ∑ p ∈ P, (∑ b, c p b * f b) ^ 2 ≤ f ⬝ᵥ (M *ᵥ f)) :
    0 ≤ ∑ p ∈ P, ∑ p' ∈ P, u p * (∑ b, ∑ b', c p b * M⁻¹ b b' * c p' b') * u p' ∧
      ∑ p ∈ P, ∑ p' ∈ P, u p * (∑ b, ∑ b', c p b * M⁻¹ b b' * c p' b') * u p' ≤ κ⁻¹ * ∑ p ∈ P, u p ^ 2 := by
  rw [kernelQuad_eq_dotProduct]
  set w : ι → ℝ := fun b => ∑ p ∈ P, u p * c p b with hw
  set y : ι → ℝ := M⁻¹ *ᵥ w with hy
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  have hMy : M *ᵥ y = w := by
    rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
  have hs : w ⬝ᵥ y = y ⬝ᵥ (M *ᵥ y) := by rw [hMy, dotProduct_comm]
  set V : ℝ := ∑ p ∈ P, (∑ b, c p b * y b) ^ 2 with hVdef
  set U : ℝ := ∑ p ∈ P, u p ^ 2 with hUdef
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hU0 : 0 ≤ U := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hV : κ * V ≤ w ⬝ᵥ y := by rw [hs]; exact hlow y
  have hs0 : 0 ≤ w ⬝ᵥ y := le_trans (mul_nonneg hκ.le hV0) hV
  have hpair : w ⬝ᵥ y = ∑ p ∈ P, u p * ∑ b, c p b * y b := by
    simp only [dotProduct, hw, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hcs : (w ⬝ᵥ y) ^ 2 ≤ U * V := by
    rw [hpair]
    exact Finset.sum_mul_sq_le_sq_mul_sq P u fun p => ∑ b, c p b * y b
  refine ⟨hs0, ?_⟩
  rw [le_inv_mul_iff₀ hκ]
  rcases hs0.eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]; exact hU0
  · have h2 : κ * (w ⬝ᵥ y) ^ 2 ≤ U * (w ⬝ᵥ y) := by
      calc κ * (w ⬝ᵥ y) ^ 2 ≤ κ * (U * V) := by gcongr
        _ = U * (κ * V) := by ring
        _ ≤ U * (w ⬝ᵥ y) := by gcongr
    have h3 : (κ * (w ⬝ᵥ y)) * (w ⬝ᵥ y) ≤ U * (w ⬝ᵥ y) := by nlinarith
    exact le_of_mul_le_mul_right h3 hpos
omit [DecidableEq ι] in
private theorem dotProduct_mulVec_add_gram (M : Matrix ι ι ℝ) (Dm : ι → ι → ℝ) (Z : Finset σ) (g : σ → ι → ℝ)
    (hM : ∀ b b', M b b' = Dm b b' + ∑ z ∈ Z, g z b * g z b') (f : ι → ℝ) :
    f ⬝ᵥ (M *ᵥ f) = ∑ b, ∑ b', f b * Dm b b' * f b' + ∑ z ∈ Z, (∑ b, g z b * f b) ^ 2 := by
  have hsq : ∀ z, (∑ b, g z b * f b) ^ 2 = ∑ b, ∑ b', f b * (g z b * g z b') * f b' := by
    intro z
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
    ring
  have hswap : ∑ z ∈ Z, (∑ b, g z b * f b) ^ 2 = ∑ b, ∑ b', ∑ z ∈ Z, f b * (g z b * g z b') * f b' := by
    simp only [hsq]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_comm
  rw [hswap, ← Finset.sum_add_distrib]
  simp only [dotProduct, Matrix.mulVec]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b' _ => ?_
  have hz : ∑ z ∈ Z, f b * (g z b * g z b') * f b' = f b * ((∑ z ∈ Z, g z b * g z b') * f b') := by
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => by ring
  rw [hz, hM]
  ring
end Algebra
variable {n : ℕ} [NeZero n]
private def alongI (s : TorusBond n → ℝ) : TorusBond n → imaginaryQuaternions := fun b => s b • imaginaryUnitI
open Classical in
private def extendByZero {o : TorusSite n} {R : ℕ} (f : TouchingBond o R → ℝ) (b : TorusBond n) : ℝ :=
  if h : b ∈ bondsTouching o R then f ⟨b, h⟩ else 0
private theorem extendByZero_coe {o : TorusSite n} {R : ℕ} (f : TouchingBond o R → ℝ) (b : TouchingBond o R) :
    extendByZero f b.1 = f b := by
  simp [extendByZero, b.2]
private theorem extendByZero_of_not_mem {o : TorusSite n} {R : ℕ} (f : TouchingBond o R → ℝ) {b : TorusBond n}
    (hb : b ∉ bondsTouching o R) : extendByZero f b = 0 := by
  simp [extendByZero, hb]
private theorem sum_extendByZero_mul {o : TorusSite n} {R : ℕ} (f : TouchingBond o R → ℝ) (h : TorusBond n → ℝ) :
    ∑ b : TorusBond n, extendByZero f b * h b = ∑ b : TouchingBond o R, f b * h b.1 := by
  have h1 : ∑ b : TouchingBond o R, f b * h b.1 = ∑ b ∈ bondsTouching o R, extendByZero f b * h b := by
    rw [Finset.sum_subtype (bondsTouching o R) (fun _ => Iff.rfl) (fun b => extendByZero f b * h b)]
    exact Finset.sum_congr rfl fun b _ => by rw [extendByZero_coe]
  rw [h1]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun b _ hb => ?_
  rw [extendByZero_of_not_mem f hb, zero_mul]
private theorem imaginaryUnitI_re : (imaginaryUnitI : ℍ[ℝ]).re = 0 := rfl
private theorem imaginaryUnitI_imI : (imaginaryUnitI : ℍ[ℝ]).imI = 1 := rfl
private theorem imaginaryUnitI_imJ : (imaginaryUnitI : ℍ[ℝ]).imJ = 0 := rfl
private theorem imaginaryUnitI_imK : (imaginaryUnitI : ℍ[ℝ]).imK = 0 := rfl
private theorem add_smul_imaginaryUnitI (a b : ℝ) :
    (a + b) • imaginaryUnitI = a • imaginaryUnitI + b • imaginaryUnitI :=
  add_smul a b imaginaryUnitI
private theorem sub_smul_imaginaryUnitI (a b : ℝ) :
    (a - b) • imaginaryUnitI = a • imaginaryUnitI - b • imaginaryUnitI :=
  sub_smul a b imaginaryUnitI
private theorem imaginaryComponent_smul_imaginaryUnitI (e : Fin 3) (c : ℝ) :
    imaginaryComponent e (c • imaginaryUnitI) = if e = 0 then c else 0 := by
  fin_cases e <;> simp [imaginaryComponent, imaginaryUnitI_imI, imaginaryUnitI_imJ, imaginaryUnitI_imK]
private theorem norm_imaginaryUnitI : ‖imaginaryUnitI‖ = 1 := by apply _root_.YangMills.SharedProofs.p16675 <;> assumption
private theorem inner_smul_imaginaryUnitI (c : ℝ) (w : imaginaryQuaternions) :
    inner ℝ (c • imaginaryUnitI) w = c * imaginaryComponent 0 w := by
  show (((c • imaginaryUnitI : imaginaryQuaternions) : ℍ[ℝ]) * star (w : ℍ[ℝ])).re = _
  simp [imaginaryComponent, Quaternion.re_mul, imaginaryUnitI_re, imaginaryUnitI_imI, imaginaryUnitI_imJ,
    imaginaryUnitI_imK]
private theorem form_alongI {Q : (TorusBond n → imaginaryQuaternions) → (TorusBond n → imaginaryQuaternions) → ℝ}
    {D : TorusBond n → TorusBond n → ℝ}
    (h : ∀ u v, Q u v = ∑ e : Fin 3, ∑ b : TorusBond n, ∑ b' : TorusBond n,
      D b b' * imaginaryComponent e (u b) * imaginaryComponent e (v b')) (s t : TorusBond n → ℝ) :
    Q (alongI s) (alongI t) = ∑ b : TorusBond n, ∑ b' : TorusBond n, D b b' * s b * t b' := by
  rw [h]
  simp only [alongI, imaginaryComponent_smul_imaginaryUnitI, Fin.sum_univ_three]
  simp
private theorem form_extendByZero {o : TorusSite n} {R : ℕ} (D : TorusBond n → TorusBond n → ℝ)
    (f : TouchingBond o R → ℝ) :
    ∑ b : TorusBond n, ∑ b' : TorusBond n, D b b' * extendByZero f b * extendByZero f b' =
      ∑ b : TouchingBond o R, ∑ b' : TouchingBond o R, f b * D b.1 b'.1 * f b' := by
  have h1 : ∀ b : TorusBond n, ∑ b' : TorusBond n, D b b' * extendByZero f b * extendByZero f b' =
      extendByZero f b * ∑ b' : TouchingBond o R, f b' * D b b'.1 := by
    intro b
    rw [← sum_extendByZero_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b' _ => by ring
  simp only [h1]
  rw [sum_extendByZero_mul f fun b => ∑ b' : TouchingBond o R, f b' * D b b'.1]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b' _ => by ring
private theorem lieFormCurl_alongI (s : TorusBond n → ℝ) (p : TorusPlaquette n) :
    lieFormCurl (alongI s) p = (∑ b : TorusBond n, curlCoeff p b * s b) • imaginaryUnitI := by
  have h : ∑ b : TorusBond n, curlCoeff p b * s b =
      s (p.1, p.2.1) + s (p.1 + TorusFields.unitStep n p.2.1, p.2.2) -
        s (p.1 + TorusFields.unitStep n p.2.2, p.2.1) - s (p.1, p.2.2) := by
    classical
    simp only [curlCoeff, add_mul, sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [h, sub_smul_imaginaryUnitI, sub_smul_imaginaryUnitI, add_smul_imaginaryUnitI]
  rfl
private theorem sum_gradCoeff_mul (t : TorusSite n → ℝ) (b : TorusBond n) :
    ∑ z : TorusSite n, gradCoeff z b * t z = t b.1 - t (b.1 + TorusFields.unitStep n b.2) := by apply _root_.YangMills.SharedProofs.p55520 <;> assumption
private theorem curlNormSq_alongI_extendByZero (S : Finset (TorusSite n)) {o : TorusSite n} {R : ℕ}
    (f : TouchingBond o R → ℝ) :
    curlNormSq S (alongI (extendByZero f)) =
      ∑ p ∈ plaquettesIn S, (∑ b : TouchingBond o R, curlCoeff p b.1 * f b) ^ 2 := by
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [lieFormCurl_alongI, norm_smul, norm_imaginaryUnitI, mul_one, Real.norm_eq_abs, sq_abs]
  congr 1
  have := sum_extendByZero_mul f (curlCoeff p)
  simp only [mul_comm (curlCoeff p _)]
  exact this
private theorem isAxialSmall_zero (o : TorusSite n) (R : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    IsAxialSmall o R δ (0 : TorusBond n → imaginaryQuaternions) := by apply _root_.YangMills.SharedProofs.p91808 <;> assumption
private theorem alongI_mem_gaugeSlice {o : TorusSite n} {R : ℕ} (f : TouchingBond o R → ℝ)
    (hf : ∀ z ∈ supBall o R, ∑ b : TouchingBond o R, gradCoeff z b.1 * f b = 0) :
    alongI (extendByZero f) ∈ gaugeSlice o R (0 : TorusBond n → imaginaryQuaternions) := by
  have hexp : expUnit (0 : imaginaryQuaternions) = 1 := by
    apply Subtype.ext
    simp [expUnit]
  refine ⟨fun b hb => by simp [alongI, extendByZero_of_not_mem f hb], fun χ hχ => ?_⟩
  set t : TorusSite n → ℝ := fun z => imaginaryComponent 0 (χ z) with ht
  have hcomp : ∀ b : TorusBond n, imaginaryComponent 0 (covariantGrad (0 : TorusBond n → imaginaryQuaternions) χ b) =
      ∑ z : TorusSite n, gradCoeff z b * t z := by
    intro b
    rw [sum_gradCoeff_mul]
    have : ColdStepAtMirrorFrames.adjointAction (expUnit (0 : imaginaryQuaternions))
        (χ (b.1 + TorusFields.unitStep n b.2)) = χ (b.1 + TorusFields.unitStep n b.2) := by
      apply Subtype.ext
      simp [ColdStepAtMirrorFrames.adjointAction, hexp]
    simp [covariantGrad, this, ht, imaginaryComponent]
  have h1 : ∑ b : TorusBond n,
      inner ℝ (alongI (extendByZero f) b) (covariantGrad (0 : TorusBond n → imaginaryQuaternions) χ b) =
      ∑ b : TouchingBond o R, f b * ∑ z : TorusSite n, gradCoeff z b.1 * t z := by
    rw [← sum_extendByZero_mul f fun b => ∑ z : TorusSite n, gradCoeff z b * t z]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [alongI, inner_smul_imaginaryUnitI, hcomp]
  rw [h1]
  have h2 : ∑ b : TouchingBond o R, f b * ∑ z : TorusSite n, gradCoeff z b.1 * t z =
      ∑ z : TorusSite n, t z * ∑ b : TouchingBond o R, gradCoeff z b.1 * f b := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun b _ => by ring
  rw [h2]
  refine Finset.sum_eq_zero fun z _ => ?_
  by_cases hz : z ∈ supBall o R
  · rw [hf z hz, mul_zero]
  · have : t z = 0 := by simp [ht, hχ z hz, imaginaryComponent]
    rw [this, zero_mul]
private theorem natAbs_valMinAbs_unitStep_le (h : 2 < n) (j : Fin 4) (i : Fin 4) :
    (TorusFields.unitStep n i j).valMinAbs.natAbs ≤ 1 ∧
      (-(TorusFields.unitStep n i j)).valMinAbs.natAbs ≤ 1 := by
  have : Fact (1 < n) := ⟨by omega⟩
  have h1 : (1 : ZMod n).valMinAbs = 1 := by
    rw [ZMod.valMinAbs_spec]
    refine ⟨by simp, ?_⟩
    constructor <;> push_cast <;> omega
  have h2 : (-1 : ZMod n).valMinAbs = -1 := by
    rw [ZMod.valMinAbs_spec]
    refine ⟨by simp, ?_⟩
    constructor <;> push_cast <;> omega
  by_cases hij : j = i
  · subst hij
    simp [TorusFields.unitStep, h1, h2]
  · simp [TorusFields.unitStep, hij]
private theorem supDist_add_unitStep (h : 2 < n) (x o : TorusSite n) (i : Fin 4) :
    _root_.YangMills.Construction.TorusFields.supDist (x + TorusFields.unitStep n i) o ≤ _root_.YangMills.Construction.TorusFields.supDist x o + 1 ∧
      _root_.YangMills.Construction.TorusFields.supDist x o ≤ _root_.YangMills.Construction.TorusFields.supDist (x + TorusFields.unitStep n i) o + 1 := by
  have hle : ∀ (a : TorusSite n) (j : Fin 4), ((a j - o j).valMinAbs).natAbs ≤ _root_.YangMills.Construction.TorusFields.supDist a o := by
    intro a j
    exact Finset.le_sup (f := fun i => ((a i - o i).valMinAbs).natAbs) (Finset.mem_univ j)
  constructor
  · refine Finset.sup_le fun j _ => ?_
    have e : (x + TorusFields.unitStep n i) j - o j = (x j - o j) + TorusFields.unitStep n i j := by
      simp; ring
    rw [e]
    have h1 := ZMod.natAbs_valMinAbs_add_le (x j - o j) (TorusFields.unitStep n i j)
    have h2 := (natAbs_valMinAbs_unitStep_le h j i).1
    have h3 := hle x j
    omega
  · refine Finset.sup_le fun j _ => ?_
    have e : x j - o j = ((x + TorusFields.unitStep n i) j - o j) + -(TorusFields.unitStep n i j) := by
      simp; ring
    rw [e]
    have h1 := ZMod.natAbs_valMinAbs_add_le ((x + TorusFields.unitStep n i) j - o j)
      (-(TorusFields.unitStep n i j))
    have h2 := (natAbs_valMinAbs_unitStep_le h j i).2
    have h3 := hle (x + TorusFields.unitStep n i) j
    omega
private theorem mem_bondsWithin_of_mem_bondsTouching {o : TorusSite n} {R : ℕ} (hR : 1 ≤ R) (h : 2 < n)
    {b : TorusBond n} (hb : b ∈ bondsTouching o R) : b ∈ bondsWithin (supBall o (2 * R)) := by
  have hs := supDist_add_unitStep h b.1 o b.2
  have hb' : (_root_.YangMills.Construction.TorusFields.supDist b.1 o : ℝ) ≤ R ∨ (_root_.YangMills.Construction.TorusFields.supDist (b.1 + TorusFields.unitStep n b.2) o : ℝ) ≤ R := by
    simpa [bondsTouching, supBall] using hb
  have hn : _root_.YangMills.Construction.TorusFields.supDist b.1 o ≤ R ∨ _root_.YangMills.Construction.TorusFields.supDist (b.1 + TorusFields.unitStep n b.2) o ≤ R := by
    exact_mod_cast hb'
  have h1 : _root_.YangMills.Construction.TorusFields.supDist b.1 o ≤ 2 * R ∧ _root_.YangMills.Construction.TorusFields.supDist (b.1 + TorusFields.unitStep n b.2) o ≤ 2 * R := by omega
  have h2 : (_root_.YangMills.Construction.TorusFields.supDist b.1 o : ℝ) ≤ 2 * R ∧
      (_root_.YangMills.Construction.TorusFields.supDist (b.1 + TorusFields.unitStep n b.2) o : ℝ) ≤ 2 * R := by
    exact_mod_cast h1
  simpa [bondsWithin, supBall] using h2
private theorem boxRadius_pow (R : ℕ) : boxRadius (1 / 27) ((R : ℝ) ^ 27) = R := by
  have h : (((R : ℝ) ^ 27) ^ (1 / 27 : ℝ)) = R := by
    have := Real.pow_rpow_inv_natCast (Nat.cast_nonneg R : (0 : ℝ) ≤ R) (n := 27) (by norm_num)
    simpa using this
  unfold boxRadius
  rw [h]
  exact Nat.ceil_natCast R
private theorem boxScale_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ boxScale x := by apply _root_.YangMills.SharedProofs.p57587 <;> assumption
theorem curlCovarianceBounds (hForm : cubeHessianStatement) (hEll : ellipsoidBoundsStatement) :
    curlCovarianceBoundsStatement := by
  intro Tb hTb
  obtain ⟨CQ, R₁, -, hform⟩ := hForm Tb hTb
  obtain ⟨K, xs, -, hell⟩ := hEll Tb hTb (1 / 27) le_rfl (by norm_num) 1 one_pos
  have hcK : 0 < Tb.coercivity := hTb.cK_pos
  refine ⟨max (max R₁ 1) ⌈xs⌉₊, fun k n _ o R hR hn => ?_⟩
  have hR₁ : R₁ ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hR
  have hR1 : 1 ≤ R := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hR
  have hRx : ⌈xs⌉₊ ≤ R := le_trans (le_max_right _ _) hR
  have hn2 : 2 < n := by omega
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR1
  have hR1r : (1 : ℝ) ≤ R := by exact_mod_cast hR1
  have hx1 : (1 : ℝ) ≤ (R : ℝ) ^ 27 := one_le_pow₀ hR1r
  have hxs : xs ≤ (R : ℝ) ^ 27 := by
    have h1 : xs ≤ R := le_trans (Nat.le_ceil xs) (by exact_mod_cast hRx)
    have h2 : (R : ℝ) ≤ (R : ℝ) ^ 27 := by
      calc (R : ℝ) = (R : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (R : ℝ) ^ 27 := pow_le_pow_right₀ hR1r (by norm_num)
    linarith
  obtain ⟨-, -, hsym, -, hbd, -, hcol⟩ := hform k n o R hR₁ hn
  have hcoer := (hell ((R : ℝ) ^ 27) R k n o 0 hxs (boxRadius_pow R).symm hn
    (isAxialSmall_zero o R (boxScale_nonneg hx1))).1
  set S := supBall o (2 * R) with hS
  set Q := hessianForm Tb.coupling Tb.side k S with hQ
  set D : TorusBond n → TorusBond n → ℝ := fun b b' =>
    mixedDeriv (actionAtLevel Tb.coupling Tb.side k S) (trivialField n) ![b, b'] ![imaginaryUnitI, imaginaryUnitI]
    with hD
  set M := regularizedHessian Tb.coupling Tb.side k o R with hMdef
  have hMe : ∀ b b' : TouchingBond o R, M b b' = D b.1 b'.1 +
      ∑ z ∈ supBall o R, gradCoeff z b.1 * gradCoeff z b'.1 := fun _ _ => rfl
  have hQu : ∀ f : TouchingBond o R → ℝ, Q (alongI (extendByZero f)) (alongI (extendByZero f)) =
      ∑ b : TouchingBond o R, ∑ b' : TouchingBond o R, f b * D b.1 b'.1 * f b' := by
    intro f
    rw [form_alongI (D := D) hcol, form_extendByZero]
  have hquad : ∀ f : TouchingBond o R → ℝ, f ⬝ᵥ (M.mulVec f) =
      Q (alongI (extendByZero f)) (alongI (extendByZero f)) +
        ∑ z ∈ supBall o R, (∑ b : TouchingBond o R, gradCoeff z b.1 * f b) ^ 2 := by
    intro f
    rw [hQu, dotProduct_mulVec_add_gram M (fun b b' => D b.1 b'.1) (supBall o R) (fun z b => gradCoeff z b.1) hMe]
  have hlow : ∀ f : TouchingBond o R → ℝ,
      (2 * Tb.coercivity) * ∑ p ∈ plaquettesIn S, (∑ b : TouchingBond o R, curlCoeff p b.1 * f b) ^ 2 ≤
        f ⬝ᵥ (M.mulVec f) := by
    intro f
    rw [hquad, ← curlNormSq_alongI_extendByZero]
    have h1 := (hbd (alongI (extendByZero f))).1
    have h2 : 0 ≤ ∑ z ∈ supBall o R, (∑ b : TouchingBond o R, gradCoeff z b.1 * f b) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  have hdet : M.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    apply hv
    have hq := hquad v
    rw [hMv, dotProduct_zero] at hq
    have hQ0 : 0 ≤ Q (alongI (extendByZero v)) (alongI (extendByZero v)) :=
      le_trans (mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)) (hbd _).1
    have hG0 : 0 ≤ ∑ z ∈ supBall o R, (∑ b : TouchingBond o R, gradCoeff z b.1 * v b) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hQz : Q (alongI (extendByZero v)) (alongI (extendByZero v)) = 0 := by linarith
    have hGz : ∑ z ∈ supBall o R, (∑ b : TouchingBond o R, gradCoeff z b.1 * v b) ^ 2 = 0 := by linarith
    have hg : ∀ z ∈ supBall o R, ∑ b : TouchingBond o R, gradCoeff z b.1 * v b = 0 := by
      intro z hz
      have := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).mp hGz z hz
      exact pow_eq_zero_iff (by norm_num) |>.mp this
    have hc := hcoer _ (alongI_mem_gaugeSlice v hg)
    rw [hQz] at hc
    have hcoef : 0 < 2 * Tb.coercivity * ((R : ℝ) ^ 2)⁻¹ := by positivity
    have hB0 : bondNormSq S (alongI (extendByZero v)) ≤ 0 := by
      by_contra hpos
      exact absurd hc (not_le.mpr (mul_pos hcoef (not_le.mp hpos)))
    have hBz : bondNormSq S (alongI (extendByZero v)) = 0 :=
      le_antisymm hB0 (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    funext b
    have hb := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).mp hBz b.1
      (mem_bondsWithin_of_mem_bondsTouching hR1 hn2 b.2)
    have hb' : ‖alongI (extendByZero v) b.1‖ = 0 := pow_eq_zero_iff (by norm_num) |>.mp hb
    rw [alongI, norm_smul, norm_imaginaryUnitI, mul_one, extendByZero_coe, Real.norm_eq_abs, abs_eq_zero] at hb'
    exact hb'
  have hDsym : ∀ b b' : TorusBond n, D b b' = D b' b := by
    classical
    have hone : ∀ b b' : TorusBond n, Q (alongI (Pi.single b 1)) (alongI (Pi.single b' 1)) = D b b' := by
      intro b b'
      rw [form_alongI (D := D) hcol]
      simp [Pi.single_apply]
    intro b b'
    rw [← hone, ← hone, hsym]
  have hMt : M.transpose = M := by
    ext b b'
    rw [Matrix.transpose_apply, hMe, hMe, hDsym]
    congr 1
    exact Finset.sum_congr rfl fun z _ => mul_comm _ _
  have hMi : ∀ b b' : TouchingBond o R, M⁻¹ b b' = M⁻¹ b' b := by
    intro b b'
    have := Matrix.transpose_nonsing_inv M
    rw [hMt] at this
    exact congrFun (congrFun this.symm b) b' |>.trans rfl
  refine ⟨isUnit_iff_ne_zero.mpr hdet, fun p p' => ?_, fun u => ?_⟩
  · show ∑ b : TouchingBond o R, ∑ b' : TouchingBond o R, curlCoeff p b.1 * M⁻¹ b b' * curlCoeff p' b'.1 =
      ∑ b : TouchingBond o R, ∑ b' : TouchingBond o R, curlCoeff p' b.1 * M⁻¹ b b' * curlCoeff p b'.1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
    rw [hMi]
    ring
  · have key := fun e : Fin 3 => kernelQuad_bounds M hdet (plaquettesIn S)
      (fun p (b : TouchingBond o R) => curlCoeff p b.1) (fun p => u p e) (2 * Tb.coercivity) (by positivity) hlow
    constructor
    · exact Finset.sum_nonneg fun e _ => (key e).1
    · rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun e _ => (key e).2
end YangMills.Construction.BoxGaussian
end
