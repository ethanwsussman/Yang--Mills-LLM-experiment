import YangMills.Construction.ClusterExpansionOfAStep.DistancesAndClasses
import YangMills.Construction.SummableBoundsOfTheFlow.InverseOfAMixture
import YangMills.Construction.SummableBoundsOfTheFlow.MixtureDerivativeInCoordinatesForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames TorusFields TorusLumps StepCosts WeightedResponses TwoLevelMixtures MixtureJets
namespace CriticalGerms
private theorem abs_one_sub_exp_le_exp_sub_one (x y : ℝ) (h : |x| ≤ y) : |1 - Real.exp x| ≤ Real.exp y - 1 := by
  rcases le_total 0 x with hx | hx
  · have h1 : 1 ≤ Real.exp x := Real.one_le_exp hx
    rw [abs_of_nonpos (by linarith)]
    have h2 : Real.exp x ≤ Real.exp y := Real.exp_le_exp.mpr ((le_abs_self x).trans h)
    linarith
  · have h1 : Real.exp x ≤ 1 := Real.exp_le_one_iff.mpr hx
    rw [abs_of_nonneg (by linarith)]
    have h2 : Real.exp (-x) ≤ Real.exp y := Real.exp_le_exp.mpr ((neg_le_abs x).trans h)
    have h3 : 2 ≤ Real.exp x + Real.exp (-x) := by
      have h4 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
      nlinarith [sq_nonneg (Real.exp x - Real.exp (-x)), Real.exp_pos x, Real.exp_pos (-x)]
    linarith
private theorem weighted_decay_of_coercive_rows {ι : Type} [Fintype ι] (S : Finset ι) (m : ι → ι → ℝ) (dist₀ : ι → ℝ)
    (dist : ι → ι → ℝ)
    (lam r : ℝ) (hlam : 0 < lam) (hr : 0 ≤ r) (hdist₀ : ∀ b b', |dist₀ b - dist₀ b'| ≤ dist b b')
    (hdist_symm : ∀ b b', dist b b' = dist b' b)
    (hrow : ∀ b ∈ S, ∑ b' ∈ S, |m b b'| * (Real.exp (2 * r * dist b b') - 1) ≤ lam / 2)
    (hcol : ∀ b ∈ S, ∑ b' ∈ S, |m b' b| * (Real.exp (2 * r * dist b b') - 1) ≤ lam / 2)
    (hcoercive : ∀ u : ι → ℝ, (∀ b, b ∉ S → u b = 0) →
      lam * ∑ b, u b ^ 2 ≤ ∑ b ∈ S, ∑ b' ∈ S, u b * m b b' * u b')
    (g : ι → ℝ) (hg : ∀ b, b ∉ S → g b = 0) (b₀ : ι) (hb₀ : dist₀ b₀ = 0)
    (hsolve : ∀ φ : ι → ℝ, (∀ b, b ∉ S → φ b = 0) → ∑ b ∈ S, ∑ b' ∈ S, g b * m b b' * φ b' = φ b₀)
    (b : ι) : |g b| ≤ 2 / lam * Real.exp (-(2 * r * dist₀ b)) := by
  classical
  set ρ : ι → ℝ := fun b => Real.exp (2 * r * dist₀ b) with hρ
  have hρ0 : ∀ b, 0 < ρ b := fun b => Real.exp_pos _
  set u : ι → ℝ := fun b => ρ b * g b with hu
  set φ : ι → ℝ := fun b => ρ b ^ 2 * g b with hφ
  set U : ℝ := ∑ b, u b ^ 2 with hU
  have huS : ∀ b, b ∉ S → u b = 0 := fun b hb => by simp [hu, hg b hb]
  have hφS : ∀ b, b ∉ S → φ b = 0 := fun b hb => by simp [hφ, hg b hb]
  have hρb₀ : ρ b₀ = 1 := by simp [hρ, hb₀]
  have h1 := hcoercive u huS
  have h2 := hsolve φ hφS
  have hφb₀ : φ b₀ = u b₀ := by simp [hφ, hu, hρb₀]
  have hterm : ∀ b b', u b * m b b' * u b' - g b * m b b' * φ b' ≤
      (u b ^ 2 + u b' ^ 2) / 2 * (|m b b'| * (Real.exp (2 * r * dist b b') - 1)) := by
    intro b b'
    have e1 : u b * m b b' * u b' - g b * m b b' * φ b' =
        u b * u b' * m b b' * (1 - Real.exp (2 * r * (dist₀ b' - dist₀ b))) := by
      have e2 : Real.exp (2 * r * (dist₀ b' - dist₀ b)) * ρ b = ρ b' := by
        simp only [hρ]
        rw [← Real.exp_add]
        congr 1
        ring
      simp only [hu, hφ]
      rw [← e2]
      ring
    rw [e1]
    have e3 : |1 - Real.exp (2 * r * (dist₀ b' - dist₀ b))| ≤ Real.exp (2 * r * dist b b') - 1 := by
      apply abs_one_sub_exp_le_exp_sub_one
      rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * r)]
      have := hdist₀ b' b
      rw [hdist_symm b b']
      exact mul_le_mul_of_nonneg_left this (by linarith)
    have e4 : |u b * u b'| ≤ (u b ^ 2 + u b' ^ 2) / 2 := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (u b - u b'), sq_nonneg (u b + u b')]
    calc u b * u b' * m b b' * (1 - Real.exp (2 * r * (dist₀ b' - dist₀ b)))
        ≤ |u b * u b' * m b b' * (1 - Real.exp (2 * r * (dist₀ b' - dist₀ b)))| := le_abs_self _
      _ = |u b * u b'| * (|m b b'| * |1 - Real.exp (2 * r * (dist₀ b' - dist₀ b))|) := by
          rw [abs_mul, abs_mul]; ring
      _ ≤ (u b ^ 2 + u b' ^ 2) / 2 * (|m b b'| * (Real.exp (2 * r * dist b b') - 1)) := by
          apply mul_le_mul e4 (mul_le_mul_of_nonneg_left e3 (abs_nonneg _))
            (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by positivity)
  set w : ι → ι → ℝ := fun b b' => |m b b'| * (Real.exp (2 * r * dist b b') - 1) with hw
  have hsumS : ∑ b ∈ S, u b ^ 2 ≤ U :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _
  have h3 : ∑ b ∈ S, ∑ b' ∈ S, u b * m b b' * u b' - ∑ b ∈ S, ∑ b' ∈ S, g b * m b b' * φ b' ≤ lam / 2 * U := by
    rw [← Finset.sum_sub_distrib]
    have e5 : ∀ b ∈ S, ∑ b' ∈ S, u b * m b b' * u b' - ∑ b' ∈ S, g b * m b b' * φ b' ≤
        ∑ b' ∈ S, (u b ^ 2 / 2 * w b b' + u b' ^ 2 / 2 * w b b') := by
      intro b _
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_le_sum fun b' _ => ?_
      have := hterm b b'
      simp only [hw]
      linarith
    refine (Finset.sum_le_sum e5).trans ?_
    simp only [Finset.sum_add_distrib]
    have e6 : ∑ b ∈ S, ∑ b' ∈ S, u b ^ 2 / 2 * w b b' ≤ ∑ b ∈ S, u b ^ 2 / 2 * (lam / 2) := by
      refine Finset.sum_le_sum fun b hb => ?_
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hrow b hb) (by positivity)
    have e7 : ∑ b ∈ S, ∑ b' ∈ S, u b' ^ 2 / 2 * w b b' ≤ ∑ b ∈ S, u b ^ 2 / 2 * (lam / 2) := by
      rw [Finset.sum_comm]
      refine Finset.sum_le_sum fun b hb => ?_
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have := hcol b hb
      simp only [hw]
      refine le_trans (le_of_eq ?_) this
      refine Finset.sum_congr rfl fun b' _ => ?_
      rw [hdist_symm b' b]
    have e8 : ∑ b ∈ S, u b ^ 2 / 2 * (lam / 2) = lam / 4 * ∑ b ∈ S, u b ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    nlinarith
  have h4 : lam / 2 * U ≤ u b₀ := by
    rw [h2, hφb₀] at h3
    linarith
  have hsq : ∀ b, u b ^ 2 ≤ U := fun b =>
    Finset.single_le_sum (f := fun b => u b ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ b)
  have hxle : u b₀ ≤ 2 / lam := by
    by_contra hc
    have hc := not_le.mp hc
    have hpos : 0 < u b₀ := lt_trans (by positivity) hc
    have h5 : lam / 2 * u b₀ ^ 2 ≤ u b₀ := le_trans (mul_le_mul_of_nonneg_left (hsq b₀) (by positivity)) h4
    have h6 : lam / 2 * u b₀ ≤ 1 := by
      by_contra h7
      have h7 := not_le.mp h7
      nlinarith
    have h9 : 2 < u b₀ * lam := by
      rwa [div_lt_iff₀ hlam] at hc
    linarith
  have hUle : U ≤ (2 / lam) ^ 2 := by
    have h5 : lam / 2 * U ≤ 2 / lam := h4.trans hxle
    have h6 : (2 / lam) ^ 2 = 2 / lam / (lam / 2) := by
      field_simp
    rw [h6, le_div_iff₀ (by positivity)]
    linarith
  have hub : |u b| ≤ 2 / lam := by
    have h5 : u b ^ 2 ≤ (2 / lam) ^ 2 := (hsq b).trans hUle
    have h6 := sq_le_sq.mp h5
    rwa [abs_of_pos (by positivity : 0 < 2 / lam)] at h6
  have e9 : g b = Real.exp (-(2 * r * dist₀ b)) * u b := by
    simp only [hu, hρ]
    rw [← mul_assoc, ← Real.exp_add]
    simp
  rw [e9, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
  exact mul_le_mul_of_nonneg_right hub (Real.exp_pos _).le
variable {n : ℕ}
private theorem contourMean_add (L : ℕ) (W W' : TorusBond (n * L) → ℝ) (c : TorusBond n) :
    contourMean L (W + W') c = contourMean L W c + contourMean L W' c := by apply _root_.YangMills.Construction.MixtureDerivatives.contourMean_add <;> assumption
private theorem contourMean_smul (L : ℕ) (s : ℝ) (W : TorusBond (n * L) → ℝ) (c : TorusBond n) :
    contourMean L (s • W) c = s * contourMean L W c := by apply _root_.YangMills.Construction.MixtureDerivatives.contourMean_smul <;> assumption
section Forms
set_option linter.unusedSectionVars false
variable [NeZero n] (a : ℝ) (L t : ℕ) (θ : ℝ) [NeZero L]
private theorem maxwellForm_add_left (u : ℕ) (A B C : TorusBond (n * L) → ℝ) :
    maxwellForm a L u (A + B) C = maxwellForm a L u A C + maxwellForm a L u B C := by
  simp only [maxwellForm, Pi.add_apply, add_mul, Finset.sum_add_distrib]
private theorem maxwellForm_add_right (u : ℕ) (A B C : TorusBond (n * L) → ℝ) :
    maxwellForm a L u A (B + C) = maxwellForm a L u A B + maxwellForm a L u A C := by
  simp only [maxwellForm, Pi.add_apply, mul_add, Finset.sum_add_distrib]
private theorem maxwellForm_smul_left (u : ℕ) (s : ℝ) (A C : TorusBond (n * L) → ℝ) :
    maxwellForm a L u (s • A) C = s * maxwellForm a L u A C := by
  simp only [maxwellForm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
private theorem maxwellForm_smul_right (u : ℕ) (s : ℝ) (A C : TorusBond (n * L) → ℝ) :
    maxwellForm a L u A (s • C) = s * maxwellForm a L u A C := by
  simp only [maxwellForm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
private theorem contourPairing_add_left (A B C : TorusBond (n * L) → ℝ) :
    contourPairing L (A + B) C = contourPairing L A C + contourPairing L B C := by
  simp only [contourPairing, contourMean_add, add_mul, Finset.sum_add_distrib]
private theorem contourPairing_add_right (A B C : TorusBond (n * L) → ℝ) :
    contourPairing L A (B + C) = contourPairing L A B + contourPairing L A C := by
  simp only [contourPairing, contourMean_add, mul_add, Finset.sum_add_distrib]
private theorem contourPairing_smul_left (s : ℝ) (A C : TorusBond (n * L) → ℝ) :
    contourPairing L (s • A) C = s * contourPairing L A C := by
  simp only [contourPairing, contourMean_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring
private theorem contourPairing_smul_right (s : ℝ) (A C : TorusBond (n * L) → ℝ) :
    contourPairing L A (s • C) = s * contourPairing L A C := by
  simp only [contourPairing, contourMean_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring
private def interpBilin : (TorusBond (n * L) → ℝ) →ₗ[ℝ] (TorusBond (n * L) → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (interpForm a L t θ)
    (fun A B C => by
      simp only [interpForm, interpKinetic, maxwellForm_add_left, contourPairing_add_left]; ring)
    (fun s A C => by
      simp only [interpForm, interpKinetic, maxwellForm_smul_left, contourPairing_smul_left, smul_eq_mul]; ring)
    (fun A B C => by
      simp only [interpForm, interpKinetic, maxwellForm_add_right, contourPairing_add_right]; ring)
    (fun s A C => by
      simp only [interpForm, interpKinetic, maxwellForm_smul_right, contourPairing_smul_right, smul_eq_mul]; ring)
private theorem linearMap_eq_sum_single {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → ℝ) →ₗ[ℝ] ℝ) (x : ι → ℝ) :
    f x = ∑ i, x i * f (Pi.single i 1) := by
  rw [LinearMap.pi_apply_eq_sum_univ f x]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul]
  congr 2
  funext j
  simp [Pi.single_apply, eq_comm]
open Classical in
private theorem interpForm_eq_sum_entries (A A' : TorusBond (n * L) → ℝ) :
    interpForm a L t θ A A' =
      ∑ b, ∑ b', A b * interpForm a L t θ (Pi.single b 1) (Pi.single b' 1) * A' b' := by
  have h1 : interpForm a L t θ A A' = interpBilin a L t θ A A' := rfl
  have h3 := linearMap_eq_sum_single ((interpBilin a L t θ).flip A') A
  simp only [LinearMap.flip_apply] at h3
  rw [h1, h3]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [linearMap_eq_sum_single (interpBilin a L t θ (Pi.single b 1)) A', Finset.mul_sum]
  refine Finset.sum_congr rfl fun b' _ => ?_
  have h2 : interpBilin a L t θ (Pi.single b 1) (Pi.single b' 1) =
      interpForm a L t θ (Pi.single b 1) (Pi.single b' 1) := rfl
  rw [h2]
  ring
open Classical in
private theorem interpForm_eq_sum_chartBonds (A A' : TorusBond (n * L) → ℝ) (hA : VanishesOnTrees L A)
    (hA' : VanishesOnTrees L A') :
    interpForm a L t θ A A' = ∑ b ∈ chartBonds L n, ∑ b' ∈ chartBonds L n,
      A b * interpForm a L t θ (Pi.single b 1) (Pi.single b' 1) * A' b' := by
  rw [interpForm_eq_sum_entries, ← Finset.sum_subset (Finset.subset_univ (chartBonds L n))]
  · refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_subset (Finset.subset_univ (chartBonds L n))]
    intro b' _ hb'
    rw [hA' b' hb', mul_zero]
  · intro b _ hb
    rw [hA b hb]
    simp
private theorem interpForm_eq_convex_comb (A A' : TorusBond (n * L) → ℝ) :
    interpForm a L t θ A A' = (1 - θ) * interpForm a L t 0 A A' + θ * interpForm a L (t + 1) 0 A A' := by
  simp only [interpForm, interpKinetic]
  ring
end Forms
private theorem decayWeightExcess_nonneg (L : ℕ) (r : ℝ) (hr : 0 ≤ r) (b b' : TorusBond (n * L)) :
    0 ≤ decayWeightExcess L r b b' := by
  have : 1 ≤ Real.exp (2 * r * supDist (parentBlock L b.1) (parentBlock L b'.1)) := Real.one_le_exp (by positivity)
  simp only [decayWeightExcess]
  linarith
open Classical in
theorem interpInverseDecay_of_flatFieldJetBounds (h : flatFieldJetBoundsStatement) : interpInverseDecayStatement := by
  unfold flatFieldJetBoundsStatement EventuallyOrdered at h
  unfold interpInverseDecayStatement EventuallyOrdered
  refine EventuallyInParameters.mono h fun T hT hd h1 => ?_
  intro _ r hr hrows t n _ θ b₀ g hn h0 h1' hb₀ hg b
  obtain ⟨Cm, hCm⟩ := hT hd h1
  have hM := hCm t n θ hn h0 h1'
  have hlam : 0 < T.lam := hd.chain_admissible.positivity.2.2.1
  set S := chartBonds T.L n with hS
  set m : TorusBond (n * T.L) → TorusBond (n * T.L) → ℝ :=
    fun b b' => interpForm T.a T.L t θ (Pi.single b 1) (Pi.single b' 1) with hm
  have hmean : ∀ b b', |m b b'| ≤
      (1 - θ) * |levelHessianEntry T.a T.L t b b'| + θ * |levelHessianEntry T.a T.L (t + 1) b b'| := by
    intro b b'
    simp only [hm, levelHessianEntry]
    rw [interpForm_eq_convex_comb]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - θ), abs_of_nonneg h0]
  have hcost : ∀ b b' : TorusBond (n * T.L),
      Real.exp (2 * r * (supDist (parentBlock T.L b.1) (parentBlock T.L b'.1) : ℝ)) - 1 = decayWeightExcess T.L r b b' :=
    fun _ _ => rfl
  refine weighted_decay_of_coercive_rows S m (fun b => (supDist (parentBlock T.L b.1) (parentBlock T.L b₀.1) : ℝ))
    (fun b b' => (supDist (parentBlock T.L b.1) (parentBlock T.L b'.1) : ℝ)) T.lam r hlam hr ?_ ?_ ?_ ?_ ?_ g
    hg.vanishes b₀ ?_ ?_ b
  · intro b b'
    rw [abs_le]
    have e1 := supDist_triangle (parentBlock T.L b.1) (parentBlock T.L b'.1) (parentBlock T.L b₀.1)
    have e2 := supDist_triangle (parentBlock T.L b'.1) (parentBlock T.L b.1) (parentBlock T.L b₀.1)
    rw [supDist_comm (parentBlock T.L b'.1) (parentBlock T.L b.1)] at e2
    have e1' : (supDist (parentBlock T.L b.1) (parentBlock T.L b₀.1) : ℝ) ≤
        supDist (parentBlock T.L b.1) (parentBlock T.L b'.1) +
        supDist (parentBlock T.L b'.1) (parentBlock T.L b₀.1) := by exact_mod_cast e1
    have e2' : (supDist (parentBlock T.L b'.1) (parentBlock T.L b₀.1) : ℝ) ≤
        supDist (parentBlock T.L b.1) (parentBlock T.L b'.1) +
        supDist (parentBlock T.L b.1) (parentBlock T.L b₀.1) := by exact_mod_cast e2
    constructor <;> linarith
  · intro b b'
    exact_mod_cast supDist_comm _ _
  · intro b hb
    simp only [hcost]
    calc ∑ b' ∈ S, |m b b'| * decayWeightExcess T.L r b b'
        ≤ ∑ b' ∈ S, ((1 - θ) * (|levelHessianEntry T.a T.L t b b'| * decayWeightExcess T.L r b b') +
            θ * (|levelHessianEntry T.a T.L (t + 1) b b'| * decayWeightExcess T.L r b b')) := by
          refine Finset.sum_le_sum fun b' _ => ?_
          have := mul_le_mul_of_nonneg_right (hmean b b') (decayWeightExcess_nonneg T.L r hr b b')
          linarith
      _ ≤ T.lam / 2 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          have e1 := (hrows t n hn b hb).1
          have e2 := (hrows (t + 1) n hn b hb).1
          nlinarith
  · intro b hb
    simp only [hcost]
    calc ∑ b' ∈ S, |m b' b| * decayWeightExcess T.L r b b'
        ≤ ∑ b' ∈ S, ((1 - θ) * (|levelHessianEntry T.a T.L t b' b| * decayWeightExcess T.L r b b') +
            θ * (|levelHessianEntry T.a T.L (t + 1) b' b| * decayWeightExcess T.L r b b')) := by
          refine Finset.sum_le_sum fun b' _ => ?_
          have := mul_le_mul_of_nonneg_right (hmean b' b) (decayWeightExcess_nonneg T.L r hr b b')
          linarith
      _ ≤ T.lam / 2 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          have e1 := (hrows t n hn b hb).2
          have e2 := (hrows (t + 1) n hn b hb).2
          nlinarith
  · intro u hu
    have := hM.coercive u hu
    rwa [interpForm_eq_sum_chartBonds T.a T.L t θ u u hu hu] at this
  · simp [supDist_self]
  · intro φ hφ
    have e1 := hg.eq φ hφ
    have e2 : shiftedInterpForm T.a T.L t θ 1 T.lam g φ = interpForm T.a T.L t θ g φ := by
      simp [shiftedInterpForm]
    rw [e2, interpForm_eq_sum_chartBonds T.a T.L t θ g φ hg.vanishes hφ] at e1
    rw [e1]
    simp [bondIndicator]
end CriticalGerms
end YangMills.Construction
end
