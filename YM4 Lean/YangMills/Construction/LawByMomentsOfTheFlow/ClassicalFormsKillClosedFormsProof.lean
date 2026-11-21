import YangMills.Construction.ClusterExpansionOfAStep.ContoursFromBases
import YangMills.Construction.LawByMomentsOfTheFlow.ClassicalFormsKillClosedForms
import YangMills.Construction.LawByMomentsOfTheFlow.ResponseOnClosedForms
import YangMills.Construction.ResponseInTheExpansion.GradientsUnderTheMaxwellFormProof
import YangMills.Construction.ResponseInTheExpansion.SharesAtEveryLevel
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.deprecated false
noncomputable section
open scoped Quaternion Topology
open Filter
namespace YangMills.Construction
open TorusFields WeightedResponses
namespace MomentLaw
namespace ClosedFormAnnihilation
section Calculus
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
private theorem iteratedFDeriv_two_comp_clm {Φ : E → ℝ} (hΦ : ContDiffAt ℝ 2 Φ 0) (ι : G →L[ℝ] E) (m : Fin 2 → G) :
    iteratedFDeriv ℝ 2 (fun s => Φ (ι s)) 0 m = fderiv ℝ (fderiv ℝ Φ) 0 (ι (m 0)) (ι (m 1)) := by apply _root_.YangMills.SharedProofs.p5330 <;> assumption
private theorem secondDeriv_eq_zero_of_critical_line {Φ : E → ℝ} (hΦ : ContDiffAt ℝ 2 Φ 0) (g : E)
    (hz : ∀ τ : ℝ, fderiv ℝ Φ (τ • g) = 0) (A : E) :
    fderiv ℝ (fderiv ℝ Φ) 0 g A = 0 ∧ fderiv ℝ (fderiv ℝ Φ) 0 A g = 0 := by
  have hsym : IsSymmSndFDerivAt ℝ Φ 0 := hΦ.isSymmSndFDerivAt (by simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ Φ) 0 :=
    (hΦ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hline : HasDerivAt (fun τ : ℝ => τ • g) g 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const g
  have hf : HasFDerivAt (fderiv ℝ Φ) (fderiv ℝ (fderiv ℝ Φ) 0) ((fun τ : ℝ => τ • g) 0) := by
    simpa using hd.hasFDerivAt
  have h1 := hf.comp_hasDerivAt (0 : ℝ) hline
  have h2 : (fderiv ℝ Φ ∘ fun τ : ℝ => τ • g) = fun _ => 0 := funext hz
  rw [h2] at h1
  have h3 : fderiv ℝ (fderiv ℝ Φ) 0 g = 0 := h1.unique (hasDerivAt_const _ _)
  have h4 : fderiv ℝ (fderiv ℝ Φ) 0 g A = 0 := by rw [h3]; rfl
  exact ⟨h4, by rw [← hsym.eq g A]; exact h4⟩
private theorem sum_basis_bilinear {B : Type*} [Fintype B] [DecidableEq B]
    (D : (B → ℝ) →L[ℝ] (B → ℝ) →L[ℝ] ℝ) (A A' : B → ℝ) :
    ∑ b, ∑ b', A b * D (Pi.single b 1) (Pi.single b' 1) * A' b' = D A A' := by apply _root_.YangMills.SharedProofs.p21054 <;> assumption
end Calculus
section Abelian
private theorem expUnit_zero : BlockAverages.expUnit (0 : BlockAverages.imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
private theorem expUnit_zero_smul : BlockAverages.expUnit ((0 : ℝ) • unitGenerator) = 1 :=
  Subtype.ext (by simp [BlockAverages.expUnit])
private theorem expUnit_smul_mul (s t : ℝ) :
    BlockAverages.expUnit (s • unitGenerator) * BlockAverages.expUnit (t • unitGenerator) =
      BlockAverages.expUnit ((s + t) • unitGenerator) := by
  let +nondep : NormedAlgebra ℚ ℍ[ℝ] := .restrictScalars ℚ ℝ _
  apply Subtype.ext
  have hc : Commute (((s • unitGenerator : BlockAverages.imaginaryQuaternions)) : ℍ[ℝ])
      (((t • unitGenerator : BlockAverages.imaginaryQuaternions)) : ℍ[ℝ]) := by
    simp only [Submodule.coe_smul]
    exact ((Commute.refl _).smul_left s).smul_right t
  have e : (((s + t) • unitGenerator : BlockAverages.imaginaryQuaternions) : ℍ[ℝ]) =
      ((s • unitGenerator : BlockAverages.imaginaryQuaternions) : ℍ[ℝ]) +
        ((t • unitGenerator : BlockAverages.imaginaryQuaternions) : ℍ[ℝ]) := by
    simp [add_smul]
  simp only [BlockAverages.expUnit, Submonoid.coe_mul]
  rw [e, NormedSpace.exp_add_of_commute hc]
private theorem expUnit_smul_inv (s : ℝ) :
    (BlockAverages.expUnit (s • unitGenerator))⁻¹ = BlockAverages.expUnit ((-s) • unitGenerator) := by apply _root_.YangMills.SharedProofs.p1618 <;> assumption
private theorem re_expUnit_smul (s : ℝ) :
    ((BlockAverages.expUnit (s • unitGenerator) : BlockAverages.UnitQuaternion) : ℍ[ℝ]).re = Real.cos s := by apply _root_.YangMills.SharedProofs.p36152 <;> assumption
variable {n : ℕ}
private def abelianField (σ : TorusBond n → ℝ) : TorusField n :=
  fun x i => BlockAverages.expUnit (σ (x, i) • unitGenerator)
private theorem holonomy_abelianField (σ : TorusBond n → ℝ) (x : TorusSite n) (μ ν : Fin 4) :
    holonomy (abelianField σ) x μ ν = BlockAverages.expUnit (curl σ (x, μ, ν) • unitGenerator) := by
  simp only [holonomy, abelianField, curl]
  rw [expUnit_smul_inv, expUnit_smul_inv, expUnit_smul_mul, expUnit_smul_mul, expUnit_smul_mul]
  congr 2
private theorem plaquetteEnergy_abelianField (σ : TorusBond n → ℝ) (x : TorusSite n) (μ ν : Fin 4) :
    plaquetteEnergy (abelianField σ) x μ ν = 1 - Real.cos (curl σ (x, μ, ν)) := by
  rw [plaquetteEnergy, holonomy_abelianField, re_expUnit_smul]
private theorem curl_smul_left (τ : ℝ) (A : TorusBond n → ℝ) (p : TorusPlaquette n) :
    curl (τ • A) p = τ * curl A p := by apply _root_.YangMills.SharedProofs.p39240 <;> assumption
variable [NeZero n]
private theorem hessianAtIdentity_eq_abelian (G : TorusField n → ℝ)
    (hC : ContDiffAt ℝ 2 (fun σ : TorusBond n → ℝ => G (abelianField σ)) 0) (b b' : TorusBond n) :
    hessianAtIdentity G b b' = fderiv ℝ (fderiv ℝ fun σ : TorusBond n → ℝ => G (abelianField σ)) 0
      (Pi.single b 1) (Pi.single b' 1) := by
  let ι : (Fin 2 → ℝ) →L[ℝ] (TorusBond n → ℝ) :=
    (ContinuousLinearMap.proj 0).smulRight (Pi.single b 1) +
      (ContinuousLinearMap.proj 1).smulRight (Pi.single b' 1)
  have e1 : ∀ (d : TorusBond n) (x : TorusSite n) (i : Fin 4) (s : ℝ),
      (if d = (x, i) then s • unitGenerator else (0 : BlockAverages.imaginaryQuaternions)) =
      (s * (Pi.single d (1 : ℝ) : TorusBond n → ℝ) (x, i)) • unitGenerator := by
    intro d x i s
    by_cases h : d = (x, i)
    · rw [if_pos h, h]
      simp
    · rw [if_neg h, Pi.single_eq_of_ne (Ne.symm h)]
      simp
  have hfun : (fun σ : Fin 2 → ℝ => G (perturb ![b, b'] ![unitGenerator, unitGenerator] σ (trivialField n))) =
      fun σ => (fun σ : TorusBond n → ℝ => G (abelianField σ)) (ι σ) := by
    funext σ
    show G _ = G _
    congr 1
    funext x i
    have hs : (∑ l : Fin 2, if (![b, b'] : Fin 2 → TorusBond n) l = (x, i) then
        σ l • (![unitGenerator, unitGenerator] : Fin 2 → BlockAverages.imaginaryQuaternions) l
        else 0) = (ι σ (x, i)) • unitGenerator := by
      rw [Fin.sum_univ_two]
      show (if b = (x, i) then σ 0 • unitGenerator else (0 : BlockAverages.imaginaryQuaternions)) +
        (if b' = (x, i) then σ 1 • unitGenerator else (0 : BlockAverages.imaginaryQuaternions)) = _
      rw [e1, e1, ← add_smul]
      simp [ι]
    show BlockAverages.expUnit _ * 1 = BlockAverages.expUnit _
    rw [mul_one, hs]
  unfold hessianAtIdentity mixedDeriv
  rw [hfun, iteratedFDeriv_two_comp_clm hC ι]
  simp [ι]
private theorem bilinearEval_hessian_abelian (G : TorusField n → ℝ)
    (hC : ContDiffAt ℝ 2 (fun σ : TorusBond n → ℝ => G (abelianField σ)) 0) (A A' : TorusBond n → ℝ) :
    bilinearEval (hessianAtIdentity G) A A' =
      fderiv ℝ (fderiv ℝ fun σ : TorusBond n → ℝ => G (abelianField σ)) 0 A A' := by
  classical
  rw [← sum_basis_bilinear]
  unfold bilinearEval
  simp only [hessianAtIdentity_eq_abelian G hC]
private theorem contDiffAt_abelian (G : TorusField n → ℝ) (h : ContDiffThreeAt G (trivialField n)) :
    ContDiffAt ℝ 2 (fun σ : TorusBond n → ℝ => G (abelianField σ)) 0 := by
  classical
  let e : Fin (Fintype.card (TorusBond n)) ≃ TorusBond n := (Fintype.equivFin (TorusBond n)).symm
  have hA := h _ (fun l => e l) (fun _ => unitGenerator)
  let P : (TorusBond n → ℝ) →L[ℝ] (Fin (Fintype.card (TorusBond n)) → ℝ) :=
    ContinuousLinearMap.pi fun l => ContinuousLinearMap.proj (e l)
  have hA' : ContDiffAt ℝ 2
      (fun σ' => G (perturb (fun l => e l) (fun _ => unitGenerator) σ' (trivialField n))) (P 0) := by
    rw [map_zero]
    exact hA.of_le (by norm_num)
  have hc := hA'.comp (0 : TorusBond n → ℝ) P.contDiff.contDiffAt
  refine hc.congr_of_eventuallyEq (Eventually.of_forall fun σ => ?_)
  show G (abelianField σ) = G (perturb (fun l => e l) (fun _ => unitGenerator) (P σ) (trivialField n))
  congr 1
  funext x i
  show BlockAverages.expUnit _ = BlockAverages.expUnit _ * 1
  rw [mul_one]
  congr 1
  rw [Finset.sum_eq_single (e.symm (x, i))]
  · rw [if_pos (by simp)]
    show _ = σ (e (e.symm (x, i))) • unitGenerator
    rw [Equiv.apply_symm_apply]
  · intro l _ hl
    rw [if_neg]
    intro hc'
    exact hl (by rw [← hc', Equiv.symm_apply_apply])
  · intro hn
    exact absurd (Finset.mem_univ _) hn
private def AnnihilatesCurlFree (q : BondBilinear n) : Prop :=
  ∀ A : TorusBond n → ℝ, (∀ p, curl A p = 0) → ∀ A' : TorusBond n → ℝ,
    bilinearEval q A A' = 0 ∧ bilinearEval q A' A = 0
private theorem annihilates_of_critical (G : TorusField n → ℝ)
    (hC : ContDiffAt ℝ 2 (fun σ : TorusBond n → ℝ => G (abelianField σ)) 0)
    (hz : ∀ A : TorusBond n → ℝ, (∀ p, curl A p = 0) → ∀ τ : ℝ,
      fderiv ℝ (fun σ : TorusBond n → ℝ => G (abelianField σ)) (τ • A) = 0) :
    AnnihilatesCurlFree (hessianAtIdentity G) := by
  intro A hA A'
  rw [bilinearEval_hessian_abelian G hC, bilinearEval_hessian_abelian G hC]
  exact secondDeriv_eq_zero_of_critical_line hC A (hz A hA) A'
private theorem annihilates_of_minimum (G : TorusField n → ℝ)
    (hC : ContDiffAt ℝ 2 (fun σ : TorusBond n → ℝ => G (abelianField σ)) 0)
    (hnn : ∀ σ : TorusBond n → ℝ, 0 ≤ G (abelianField σ))
    (h0 : ∀ A : TorusBond n → ℝ, (∀ p, curl A p = 0) → G (abelianField A) = 0) :
    AnnihilatesCurlFree (hessianAtIdentity G) := by
  refine annihilates_of_critical G hC fun A hA τ => ?_
  have hmin : IsLocalMin (fun σ : TorusBond n → ℝ => G (abelianField σ)) (τ • A) := by
    refine Eventually.of_forall fun σ => ?_
    show G (abelianField (τ • A)) ≤ G (abelianField σ)
    rw [h0 (τ • A) fun p => by rw [curl_smul_left, hA p, mul_zero]]
    exact hnn σ
  exact hmin.fderiv_eq_zero
end Abelian
section ClosedForms
variable {n : ℕ} [NeZero n]
private theorem nsmul_unitStep (i : Fin 4) : n • unitStep n i = 0 := by
  funext k
  by_cases h : k = i
  · subst h
    simp [unitStep]
  · simp [unitStep, Pi.single_eq_of_ne h]
private def fwdDiff (i : Fin 4) (f : TorusSite n → ℝ) : TorusSite n → ℝ := fun x => f (x + unitStep n i) - f x
private def circleMean (i : Fin 4) (f : TorusSite n → ℝ) : TorusSite n → ℝ :=
  fun x => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, f (x + k • unitStep n i)
private def weightedCircleMean (i : Fin 4) (f : TorusSite n → ℝ) : TorusSite n → ℝ :=
  fun x => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (k : ℝ) * f (x + k • unitStep n i)
private theorem sum_range_shift (i : Fin 4) (f : TorusSite n → ℝ) (x : TorusSite n) :
    ∑ k ∈ Finset.range n, f (x + (k + 1) • unitStep n i) = ∑ k ∈ Finset.range n, f (x + k • unitStep n i) := by
  have h1 := Finset.sum_range_succ (fun k => f (x + k • unitStep n i)) n
  have h2 := Finset.sum_range_succ' (fun k => f (x + k • unitStep n i)) n
  rw [h1] at h2
  simp only [nsmul_unitStep, add_zero, zero_smul] at h2
  linarith
private theorem circleMean_fwdDiff (i : Fin 4) (f : TorusSite n → ℝ) : circleMean i (fwdDiff i f) = 0 := by
  funext x
  have h := sum_range_shift i f x
  have e : ∀ k : ℕ, x + k • unitStep n i + unitStep n i = x + (k + 1) • unitStep n i := fun k => by
    rw [succ_nsmul, add_assoc]
  simp only [circleMean, fwdDiff, Finset.sum_sub_distrib, e, h, sub_self, mul_zero, Pi.zero_apply]
private theorem fwdDiff_weightedCircleMean_self (i : Fin 4) (f : TorusSite n → ℝ) (x : TorusSite n) :
    fwdDiff i (weightedCircleMean i f) x = f x - circleMean i f x := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  have h := sum_range_shift i f x
  have e : ∀ k : ℕ, x + unitStep n i + k • unitStep n i = x + (k + 1) • unitStep n i := fun k => by
    rw [succ_nsmul, add_assoc, add_comm (unitStep n i)]
  have tel := Finset.sum_range_sub (fun k : ℕ => (k : ℝ) * f (x + k • unitStep n i)) n
  simp only [nsmul_unitStep, add_zero, Nat.cast_zero, zero_mul, sub_zero] at tel
  have hs : ∀ k : ℕ, ((k + 1 : ℕ) : ℝ) * f (x + (k + 1) • unitStep n i) - (k : ℝ) * f (x + k • unitStep n i) =
      ((k : ℝ) * f (x + (k + 1) • unitStep n i) - (k : ℝ) * f (x + k • unitStep n i)) +
        f (x + (k + 1) • unitStep n i) := fun k => by
    push_cast
    ring
  simp only [hs, Finset.sum_add_distrib, Finset.sum_sub_distrib, h] at tel
  simp only [fwdDiff, weightedCircleMean, circleMean, e]
  generalize (∑ k ∈ Finset.range n, (k : ℝ) * f (x + (k + 1) • unitStep n i)) = S₁ at tel ⊢
  generalize (∑ k ∈ Finset.range n, (k : ℝ) * f (x + k • unitStep n i)) = S₀ at tel ⊢
  generalize (∑ k ∈ Finset.range n, f (x + k • unitStep n i)) = T at tel ⊢
  have h3 : S₁ - S₀ = n * f x - T := by linarith
  rw [← mul_sub, h3, mul_sub, inv_mul_cancel_left₀ hn]
private theorem fwdDiff_comm (i j : Fin 4) (f : TorusSite n → ℝ) :
    fwdDiff i (fwdDiff j f) = fwdDiff j (fwdDiff i f) := by
  funext x
  simp only [fwdDiff]
  rw [add_right_comm x (unitStep n i) (unitStep n j)]
  ring
private theorem fwdDiff_circleMean (j i : Fin 4) (f : TorusSite n → ℝ) :
    fwdDiff j (circleMean i f) = circleMean i (fwdDiff j f) := by
  funext x
  simp only [fwdDiff, circleMean, ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [add_right_comm x (unitStep n j)]
private theorem fwdDiff_weightedCircleMean (j i : Fin 4) (f : TorusSite n → ℝ) :
    fwdDiff j (weightedCircleMean i f) = weightedCircleMean i (fwdDiff j f) := by
  funext x
  simp only [fwdDiff, weightedCircleMean, ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [add_right_comm x (unitStep n j)]
private theorem fwdDiff_sub (i : Fin 4) (f g : TorusSite n → ℝ) :
    fwdDiff i (f - g) = fwdDiff i f - fwdDiff i g := by
  funext x
  simp only [fwdDiff, Pi.sub_apply]
  ring
private theorem fwdDiff_add (i : Fin 4) (f g : TorusSite n → ℝ) :
    fwdDiff i (f + g) = fwdDiff i f + fwdDiff i g := by
  funext x
  simp only [fwdDiff, Pi.add_apply]
  ring
private theorem fwdDiff_zero (i : Fin 4) : fwdDiff i (0 : TorusSite n → ℝ) = 0 := by
  funext x
  simp [fwdDiff]
private theorem weightedCircleMean_zero (i : Fin 4) : weightedCircleMean i (0 : TorusSite n → ℝ) = 0 := by
  funext x
  simp [weightedCircleMean]
private theorem exists_partial_potential (A : Fin 4 → TorusSite n → ℝ)
    (hA : ∀ i j, fwdDiff i (A j) = fwdDiff j (A i)) :
    ∀ m : ℕ, m ≤ 4 → ∃ φ : TorusSite n → ℝ, ∀ j k : Fin 4, k.1 < m → fwdDiff k (A j - fwdDiff j φ) = 0 := by
  intro m
  induction m with
  | zero => exact fun _ => ⟨0, fun _ k hk => absurd hk (Nat.not_lt_zero _)⟩
  | succ m ih =>
    intro hm
    obtain ⟨φ, hφ⟩ := ih (by omega)
    obtain ⟨e, he⟩ : ∃ e : Fin 4, e.1 = m := ⟨⟨m, by omega⟩, rfl⟩
    obtain ⟨A', hA'⟩ : ∃ A' : Fin 4 → TorusSite n → ℝ, ∀ j, A' j = A j - fwdDiff j φ := ⟨_, fun _ => rfl⟩
    have hcl : ∀ i j, fwdDiff i (A' j) = fwdDiff j (A' i) := by
      intro i j
      rw [hA', hA', fwdDiff_sub, fwdDiff_sub, hA i j, fwdDiff_comm i j]
    have hφ' : ∀ j k : Fin 4, k.1 < m → fwdDiff k (A' j) = 0 := fun j k hk => by rw [hA']; exact hφ j k hk
    refine ⟨φ + weightedCircleMean e (A' e), fun j k hk => ?_⟩
    have e1 : A j - fwdDiff j (φ + weightedCircleMean e (A' e)) = A' j - fwdDiff j (weightedCircleMean e (A' e)) := by
      rw [fwdDiff_add, hA' j, sub_sub]
    rw [e1, fwdDiff_sub, fwdDiff_comm k j]
    by_cases hkm : k.1 < m
    · rw [hφ' j k hkm, fwdDiff_weightedCircleMean, hφ' e k hkm, weightedCircleMean_zero, fwdDiff_zero, sub_zero]
    · have hk' : k = e := Fin.ext (by omega)
      subst hk'
      have h2 : fwdDiff k (weightedCircleMean k (A' k)) = A' k - circleMean k (A' k) :=
        funext fun x => fwdDiff_weightedCircleMean_self k _ x
      rw [h2, fwdDiff_sub, fwdDiff_circleMean, hcl j k, circleMean_fwdDiff]
      simp
private theorem eq_at_zero_of_fwdDiff_eq_zero (f : TorusSite n → ℝ) (h : ∀ k, fwdDiff k f = 0) (x : TorusSite n) :
    f x = f 0 := by
  have hstep : ∀ (k : Fin 4) (x : TorusSite n), f (x + unitStep n k) = f x := fun k x => by
    have := congrFun (h k) x
    simpa [fwdDiff, sub_eq_zero] using this
  have hmul : ∀ (k : Fin 4) (m : ℕ) (x : TorusSite n), f (x + m • unitStep n k) = f x := by
    intro k m
    induction m with
    | zero => simp
    | succ m ih => intro x; rw [succ_nsmul, ← add_assoc, hstep, ih]
  have e : x = 0 + (x 0).val • unitStep n 0 + (x 1).val • unitStep n 1 + (x 2).val • unitStep n 2 +
      (x 3).val • unitStep n 3 := by
    have hc : ∀ k i : Fin 4, ((x k).val • unitStep n k) i = if i = k then x k else 0 := by
      intro k i
      by_cases hik : i = k
      · subst hik
        simp only [Pi.smul_apply, unitStep, Pi.single_eq_same, nsmul_eq_mul, mul_one, if_true,
          ZMod.natCast_zmod_val]
      · simp only [Pi.smul_apply, unitStep, Pi.single_eq_of_ne hik, smul_zero, if_neg hik]
    funext i
    simp only [Pi.add_apply, Pi.zero_apply, hc]
    fin_cases i <;> simp
  rw [e, hmul, hmul, hmul, hmul]
private theorem curlFree_eq_gradient_add_const (A : TorusBond n → ℝ) (hA : ∀ p, curl A p = 0) :
    ∃ (φ : TorusSite n → ℝ) (v : Fin 4 → ℝ), ∀ b, A b = latticeGradient φ b + constantOneForm v b := by
  let A₁ : Fin 4 → TorusSite n → ℝ := fun i x => A (x, i)
  have hcl : ∀ i j, fwdDiff i (A₁ j) = fwdDiff j (A₁ i) := by
    intro i j
    funext x
    have h := hA (x, i, j)
    simp only [curl] at h
    simp only [fwdDiff, A₁]
    linarith
  obtain ⟨φ, hφ⟩ := exists_partial_potential A₁ hcl 4 le_rfl
  refine ⟨φ, fun j => (A₁ j - fwdDiff j φ) 0, fun b => ?_⟩
  have h3 : A b - (φ (b.1 + unitStep n b.2) - φ b.1) = (A₁ b.2 - fwdDiff b.2 φ) 0 :=
    eq_at_zero_of_fwdDiff_eq_zero (A₁ b.2 - fwdDiff b.2 φ) (fun k => hφ b.2 k k.2) b.1
  show A b = (φ (b.1 + unitStep n b.2) - φ b.1) + (A₁ b.2 - fwdDiff b.2 φ) 0
  linarith
abbrev _root_.YangMills.SharedProofs.p19533 := @curlFree_eq_gradient_add_const
private theorem curl_latticeGradient (φ : TorusSite n → ℝ) (p : TorusPlaquette n) :
    curl (latticeGradient φ) p = 0 := by
  have e : p.1 + unitStep n p.2.1 + unitStep n p.2.2 = p.1 + unitStep n p.2.2 + unitStep n p.2.1 := by abel
  simp only [curl, latticeGradient]
  rw [e]
  ring
private theorem curl_constantOneForm (v : Fin 4 → ℝ) (p : TorusPlaquette n) : curl (constantOneForm v) p = 0 := by
  simp only [curl, constantOneForm]
  ring
end ClosedForms
section Chains
open BlockAverages (expUnit UnitQuaternion PathStep stepDisplacement pathHolonomy linkValue reversePath bondContour
  blockFit contourAverage centredCube norm_coe_unitQuaternion quaternion_re_le_norm cellShare minimalCellShare
  chainAction wilsonAction innerPlaquettes innerBonds plaquetteHolonomy baseSite refineSite siteOfCoords siteCoords
  refineSite_add unitStep_eq baseSite_refineSite period_zero_eq siteOfCoords_siteCoords BlockFrame)
variable {F : BlockFrame}
private def gradientField {j : ℕ} (f : F.Site j → ℝ) (w : Fin 4 → ℝ) : F.GaugeField j :=
  fun x i => expUnit ((f (x + BlockAverages.unitStep j i) - f x + w i) • unitGenerator)
private def pathDisplacement (j : ℕ) : List PathStep → F.Site j
  | [] => 0
  | st :: r => stepDisplacement j st + pathDisplacement j r
private def pathConstSum (w : Fin 4 → ℝ) : List PathStep → ℝ
  | [] => 0
  | st :: r => (if st.2 then w st.1 else - w st.1) + pathConstSum w r
private theorem pathHolonomy_gradientField {j : ℕ} (f : F.Site j → ℝ) (w : Fin 4 → ℝ) (l : List PathStep)
    (x : F.Site j) :
    pathHolonomy (gradientField f w) x l =
      expUnit ((f (x + pathDisplacement j l) - f x + pathConstSum w l) • unitGenerator) := by
  induction l generalizing x with
  | nil => simp [pathHolonomy, pathDisplacement, pathConstSum, expUnit_zero]
  | cons st r ih =>
    obtain ⟨d, b⟩ := st
    cases b with
    | true =>
      have hs : linkValue (gradientField f w) x (d, true) =
          expUnit ((f (x + BlockAverages.unitStep j d) - f x + w d) • unitGenerator) := by
        simp [linkValue, gradientField]
      have hv : stepDisplacement j (d, true) = BlockAverages.unitStep (F := F) j d := by simp [stepDisplacement]
      rw [pathHolonomy, ih, hs, hv, expUnit_smul_mul]
      simp only [pathDisplacement, pathConstSum, hv, if_true]
      rw [add_assoc x]
      congr 2
      ring
    | false =>
      have hs : linkValue (gradientField f w) x (d, false) =
          expUnit ((f (x - BlockAverages.unitStep j d) - f x - w d) • unitGenerator) := by
        simp only [linkValue, gradientField, Bool.false_eq_true, if_false]
        rw [expUnit_smul_inv, sub_add_cancel]
        congr 2
        ring
      have hv : stepDisplacement j (d, false) = - BlockAverages.unitStep (F := F) j d := by simp [stepDisplacement]
      rw [pathHolonomy, ih, hs, hv, expUnit_smul_mul]
      simp only [pathDisplacement, pathConstSum, hv, Bool.false_eq_true, if_false]
      rw [← add_assoc x, ← sub_eq_add_neg x]
      congr 2
      ring
private theorem pathDisplacement_append (j : ℕ) (l l' : List PathStep) :
    pathDisplacement (F := F) j (l ++ l') = pathDisplacement j l + pathDisplacement j l' := by
  induction l with
  | nil => simp [pathDisplacement]
  | cons st r ih => simp only [List.cons_append, pathDisplacement, ih, add_assoc]
private theorem pathConstSum_append (w : Fin 4 → ℝ) (l l' : List PathStep) :
    pathConstSum w (l ++ l') = pathConstSum w l + pathConstSum w l' := by
  induction l with
  | nil => simp [pathConstSum]
  | cons st r ih => simp only [List.cons_append, pathConstSum, ih, add_assoc]
private theorem pathDisplacement_replicate (j : ℕ) (m : ℕ) (i : Fin 4) :
    pathDisplacement (F := F) j (List.replicate m (i, true)) = m • BlockAverages.unitStep j i := by
  induction m with
  | zero => simp [pathDisplacement]
  | succ m ih => simp only [List.replicate_succ, pathDisplacement, ih, stepDisplacement, if_true, succ_nsmul, add_comm]
private theorem pathConstSum_replicate (w : Fin 4 → ℝ) (m : ℕ) (i : Fin 4) :
    pathConstSum w (List.replicate m (i, true)) = m * w i := by
  induction m with
  | zero => simp [pathConstSum]
  | succ m ih =>
    simp only [List.replicate_succ, pathConstSum, ih, if_true]
    push_cast
    ring
private theorem pathDisplacement_reversePath (j : ℕ) (l : List PathStep) :
    pathDisplacement (F := F) j (reversePath l) = - pathDisplacement j l := by
  induction l with
  | nil => simp [pathDisplacement, reversePath]
  | cons st r ih =>
    have e : reversePath (st :: r) = reversePath r ++ [(st.1, !st.2)] := by simp [reversePath]
    rw [e, pathDisplacement_append, ih]
    obtain ⟨d, b⟩ := st
    cases b <;> simp [pathDisplacement, stepDisplacement, add_comm]
private theorem pathConstSum_reversePath (w : Fin 4 → ℝ) (l : List PathStep) :
    pathConstSum w (reversePath l) = - pathConstSum w l := by
  induction l with
  | nil => simp [pathConstSum, reversePath]
  | cons st r ih =>
    have e : reversePath (st :: r) = reversePath r ++ [(st.1, !st.2)] := by simp [reversePath]
    rw [e, pathConstSum_append, ih]
    obtain ⟨d, b⟩ := st
    cases b <;> simp [pathConstSum]
private theorem pathDisplacement_bondContour (j L : ℕ) (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) (i : Fin 4) :
    pathDisplacement (F := F) j (bondContour L h π i) = L • BlockAverages.unitStep j i := by
  rw [bondContour, pathDisplacement_append, pathDisplacement_append, pathDisplacement_reversePath,
    pathDisplacement_replicate]
  abel
private theorem pathConstSum_bondContour (w : Fin 4 → ℝ) (L : ℕ) (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4))
    (i : Fin 4) : pathConstSum w (bondContour L h π i) = L * w i := by
  rw [bondContour, pathConstSum_append, pathConstSum_append, pathConstSum_reversePath, pathConstSum_replicate]
  ring
private theorem blockFit_eq_zero_of_const {j : ℕ} (X : F.GaugeField j) (X' : F.GaugeField (j + 1))
    (c : F.Site (j + 1) × Fin 4) (g : UnitQuaternion)
    (hh : ∀ h π, pathHolonomy X (refineSite c.1) (bondContour F.blockSide h π c.2) = g) (hX : X' c.1 c.2 = g) :
    blockFit X X' c = 0 := by
  obtain ⟨r, hr, hm⟩ : ∃ r : ℝ, 0 ≤ r ∧ BlockAverages.contourAverage X c = r • (g : ℍ[ℝ]) := by
    refine ⟨(1 / (24 * (F.blockSide : ℝ) ^ 4)) *
      (((centredCube F.blockSide).card * Fintype.card (Equiv.Perm (Fin 4)) : ℕ) : ℝ), by positivity, ?_⟩
    simp only [BlockAverages.contourAverage, hh, Finset.sum_const, Finset.card_univ]
    rw [mul_smul, ← mul_nsmul', Nat.cast_smul_eq_nsmul, mul_comm]
  have hone : (g : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := by
    rw [← Submonoid.coe_mul, mul_inv_cancel]
    rfl
  rw [blockFit, hm, hX, smul_mul_assoc, hone, norm_smul, norm_coe_unitQuaternion, Real.norm_of_nonneg hr]
  simp
private theorem one_sub_re_nonneg (g : UnitQuaternion) : 0 ≤ 1 - (g : ℍ[ℝ]).re := by apply _root_.YangMills.Construction.BlockAverages.MinimalChain.one_sub_re_nonneg <;> assumption
private theorem blockFit_nonneg' {j : ℕ} (X : F.GaugeField j) (X' : F.GaugeField (j + 1))
    (c : F.Site (j + 1) × Fin 4) : 0 ≤ blockFit X X' c := by apply _root_.YangMills.Construction.BlockAverages.MinimalChain.blockFit_nonneg <;> assumption
private theorem cellShare_nonneg' {a : ℝ} (ha : 0 ≤ a) (S : Finset F.Cell) (Y : F.Cell) (X : F.FieldChain) :
    0 ≤ cellShare a S Y X := by
  unfold cellShare
  refine add_nonneg (Finset.sum_nonneg fun p _ => mul_nonneg ?_ (one_sub_re_nonneg _))
    (mul_nonneg ha (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun c _ => mul_nonneg ?_ (blockFit_nonneg' _ _ _)))
  · exact Finset.sum_nonneg fun x _ => by split_ifs <;> norm_num
  · split_ifs <;> norm_num
private theorem minimalCellShare_nonneg' {a : ℝ} (ha : 0 ≤ a) (S : Finset F.Cell) (Y : F.Cell)
    (V : F.GaugeField F.top) : 0 ≤ minimalCellShare a S Y V := by
  unfold minimalCellShare
  split_ifs with h
  · exact cellShare_nonneg' ha S Y _
  · exact le_rfl
private theorem minimalCellShare_eq_zero_of_null {a : ℝ} (ha : 0 < a) (S : Finset F.Cell) (Y : F.Cell)
    (V : F.GaugeField F.top) (X₀ : F.FieldChain) (htop : X₀ F.top = V)
    (hp : ∀ p, 1 - ((plaquetteHolonomy (X₀ 0) p : UnitQuaternion) : ℍ[ℝ]).re = 0)
    (hf : ∀ j, j + 1 ≤ F.top → ∀ c, blockFit (X₀ j) (X₀ (j + 1)) c = 0) : minimalCellShare a S Y V = 0 := by
  unfold minimalCellShare
  split_ifs with h
  · obtain ⟨_, hmin⟩ := h.choose_spec
    have htot : chainAction a S h.choose ≤ 0 := by
      have h0 : chainAction a S X₀ = 0 := by
        unfold chainAction BlockAverages.wilsonAction
        rw [Finset.sum_eq_zero fun p _ => hp p, zero_add, Finset.sum_eq_zero, mul_zero]
        intro j hj
        exact Finset.sum_eq_zero fun c _ => hf j (Finset.mem_range.1 hj) c
      rw [← h0]
      exact hmin X₀ htop
    unfold chainAction BlockAverages.wilsonAction at htot
    have hA : 0 ≤ ∑ p ∈ innerPlaquettes S 0,
        (1 - ((plaquetteHolonomy (h.choose 0) p : UnitQuaternion) : ℍ[ℝ]).re) :=
      Finset.sum_nonneg fun p _ => one_sub_re_nonneg _
    have hB : 0 ≤ ∑ j ∈ Finset.range F.top, ∑ c ∈ innerBonds S (j + 1), blockFit (h.choose j) (h.choose (j + 1)) c :=
      Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun c _ => blockFit_nonneg' _ _ _
    have hA0 : ∑ p ∈ innerPlaquettes S 0,
        (1 - ((plaquetteHolonomy (h.choose 0) p : UnitQuaternion) : ℍ[ℝ]).re) = 0 := by
      nlinarith [mul_nonneg ha.le hB]
    have hB0 : ∑ j ∈ Finset.range F.top, ∑ c ∈ innerBonds S (j + 1),
        blockFit (h.choose j) (h.choose (j + 1)) c = 0 := by
      have : a * ∑ j ∈ Finset.range F.top, ∑ c ∈ innerBonds S (j + 1),
          blockFit (h.choose j) (h.choose (j + 1)) c = 0 := by
        nlinarith [mul_nonneg ha.le hB]
      exact (mul_eq_zero.1 this).resolve_left ha.ne'
    have hA1 := (Finset.sum_eq_zero_iff_of_nonneg fun p _ => one_sub_re_nonneg _).1 hA0
    have hB1 := (Finset.sum_eq_zero_iff_of_nonneg
      fun j _ => Finset.sum_nonneg fun c _ => blockFit_nonneg' _ _ _).1 hB0
    unfold cellShare
    rw [Finset.sum_eq_zero fun p hp' => by rw [hA1 p hp', mul_zero], zero_add, Finset.sum_eq_zero, mul_zero]
    intro j hj
    have hB2 := (Finset.sum_eq_zero_iff_of_nonneg fun c _ => blockFit_nonneg' _ _ _).1 (hB1 j hj)
    exact Finset.sum_eq_zero fun c hc => by rw [hB2 c hc, mul_zero]
  · rfl
private def gradientChain (Ψ : F.Site 0 → ℝ) (v : Fin 4 → ℝ) : F.FieldChain :=
  fun j => gradientField (fun x : F.Site j => Ψ (baseSite x)) fun i => v i / (F.blockSide : ℝ) ^ (F.top - j)
private theorem nsmul_siteOfCoords' (j m : ℕ) (a : LatticeFractionalIntegration.Lattice4) :
    m • siteOfCoords (F := F) j a = siteOfCoords j fun i => (m : ℤ) * a i := by apply _root_.YangMills.Construction.TorusContours.nsmul_siteOfCoords <;> assumption
private theorem blockFit_gradientChain (hL : F.blockSide ≠ 0) (Ψ : F.Site 0 → ℝ) (v : Fin 4 → ℝ) (j : ℕ)
    (hj : j + 1 ≤ F.top) (c : F.Site (j + 1) × Fin 4) :
    blockFit (gradientChain Ψ v j) (gradientChain Ψ v (j + 1)) c = 0 := by
  have hL' : (F.blockSide : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hL
  refine blockFit_eq_zero_of_const _ _ c _ (fun h π => ?_) rfl
  show pathHolonomy (gradientField _ _) _ _ = _
  rw [pathHolonomy_gradientField, pathDisplacement_bondContour, pathConstSum_bondContour]
  have e1 : refineSite c.1 + F.blockSide • BlockAverages.unitStep j c.2 =
      refineSite (c.1 + BlockAverages.unitStep (j + 1) c.2) := by
    rw [unitStep_eq, unitStep_eq, refineSite_add j hj, nsmul_siteOfCoords']
  have e2 : (F.blockSide : ℝ) * (v c.2 / (F.blockSide : ℝ) ^ (F.top - j)) =
      v c.2 / (F.blockSide : ℝ) ^ (F.top - (j + 1)) := by
    have : F.top - j = (F.top - (j + 1)) + 1 := by omega
    rw [this, pow_succ]
    field_simp
  rw [e1, e2, baseSite_refineSite j hj, baseSite_refineSite j hj]
  rfl
private theorem plaquette_gradientChain (Ψ : F.Site 0 → ℝ) (v : Fin 4 → ℝ) (p : F.Site 0 × Fin 4 × Fin 4) :
    1 - ((plaquetteHolonomy (gradientChain Ψ v 0) p : UnitQuaternion) : ℍ[ℝ]).re = 0 := by
  have h : plaquetteHolonomy (gradientChain Ψ v 0) p = 1 := by
    show pathHolonomy (gradientField _ _) _ _ = _
    rw [pathHolonomy_gradientField]
    have e1 : pathDisplacement (F := F) 0 [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] = 0 := by
      simp only [pathDisplacement, stepDisplacement, if_true, Bool.false_eq_true, if_false]
      abel
    rw [e1, add_zero]
    simp only [pathConstSum, if_true, Bool.false_eq_true, if_false]
    rw [← expUnit_zero_smul]
    congr 2
    ring
  rw [h]
  simp
private theorem baseSite_injective (hL : F.blockSide ≠ 0) : Function.Injective (baseSite : F.Cell → F.Site 0) := by
  intro y y' h
  funext i
  have h1 := congrFun h i
  simp only [baseSite, siteOfCoords] at h1
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub, period_zero_eq F.top le_rfl i] at h1
  have hp : ((F.blockSide : ℤ) ^ F.top) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hL)
  have h2 : ((F.period F.top i : ℕ) : ℤ) ∣ siteCoords y' i - siteCoords y i := by
    have e : (F.blockSide : ℤ) ^ F.top * siteCoords y' i - (F.blockSide : ℤ) ^ F.top * siteCoords y i =
        (F.blockSide : ℤ) ^ F.top * (siteCoords y' i - siteCoords y i) := by
      ring
    rw [e, mul_comm ((F.period F.top i : ℕ) : ℤ)] at h1
    exact (mul_dvd_mul_iff_left hp).1 h1
  have h3 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2 h2
  have ey := congrFun (siteOfCoords_siteCoords y) i
  have ey' := congrFun (siteOfCoords_siteCoords y') i
  simp only [siteOfCoords] at ey ey'
  rw [← ey, ← ey', h3]
end Chains
section Shares
variable {n : ℕ} [NeZero n]
private theorem exists_gradientChain_readAtLevel {F : BlockAverages.BlockFrame} (hL : F.blockSide ≠ 0)
    (hm : ∀ k, F.period F.top k = n) (A : TorusBond n → ℝ) (φ : TorusSite n → ℝ) (v : Fin 4 → ℝ)
    (hA : ∀ b, A b = latticeGradient φ b + constantOneForm v b) :
    ∃ Ψ : F.Site 0 → ℝ, gradientChain Ψ v F.top = readAtLevel F F.top (abelianField A) := by
  refine ⟨Function.extend (BlockAverages.baseSite : F.Cell → F.Site 0)
    (fun x => φ (FrameTransfer.frameToTorus n x)) 0, ?_⟩
  have hinj := baseSite_injective (F := F) hL
  funext x i
  have e0 : ∀ y : F.Cell, Function.extend (BlockAverages.baseSite : F.Cell → F.Site 0)
      (fun x => φ (FrameTransfer.frameToTorus n x)) 0 (BlockAverages.baseSite y) =
      φ (FrameTransfer.frameToTorus n y) := fun y => hinj.extend_apply _ _ y
  have e1 : FrameTransfer.frameToTorus n (x + BlockAverages.unitStep F.top i) =
      FrameTransfer.frameToTorus n x + unitStep n i := by
    have e : x + BlockAverages.unitStep F.top i =
        FrameTransfer.torusToFrame F F.top (FrameTransfer.frameToTorus n x + unitStep n i) := by
      rw [FrameTransfer.torusToFrame_add hm, FrameTransfer.torusToFrame_unitStep hm,
        FrameTransfer.torusToFrame_frameToTorus hm]
    rw [e, FrameTransfer.frameToTorus_torusToFrame hm]
  show BlockAverages.expUnit ((_ - _ + v i / (F.blockSide : ℝ) ^ (F.top - F.top)) • unitGenerator) =
    BlockAverages.expUnit (A (FrameTransfer.frameToTorus n x, i) • unitGenerator)
  beta_reduce
  rw [e0, e0, e1, hA]
  simp [latticeGradient, constantOneForm]
private theorem levelShare_abelian_eq_zero {a : ℝ} (ha : 0 < a) (L : ℕ) [NeZero L] (u : ℕ) (y : TorusSite n)
    (A : TorusBond n → ℝ) (hA : ∀ p, curl A p = 0) :
    StepCosts.levelShare a L u Finset.univ y (abelianField A) = 0 := by
  cases u with
  | zero =>
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [plaquetteEnergy_abelianField]
    have := hA (p.1, p.2.1, p.2.2)
    rw [this]
    simp
  | succ t =>
    obtain ⟨φ, v, hs⟩ := curlFree_eq_gradient_add_const A hA
    have hm : ∀ k, (torusFrame L t n).period (torusFrame L t n).top k = n := fun k => by
      simp [BlockAverages.BlockFrame.period, torusFrame, BlockAverages.BlockFrame.top]
    obtain ⟨Ψ, hΨ⟩ := exists_gradientChain_readAtLevel (F := torusFrame L t n) (NeZero.ne L) hm A φ v hs
    exact minimalCellShare_eq_zero_of_null ha _ _ _ (gradientChain Ψ v) hΨ (plaquette_gradientChain Ψ v)
      fun j hj c => blockFit_gradientChain (NeZero.ne L) Ψ v j hj c
private theorem plaquetteEnergy_nonneg' (W : TorusField n) (x : TorusSite n) (μ ν : Fin 4) :
    0 ≤ plaquetteEnergy W x μ ν :=
  one_sub_re_nonneg _
private theorem levelShare_nonneg' {a : ℝ} (ha : 0 ≤ a) (L : ℕ) [NeZero L] (u : ℕ) (y : TorusSite n)
    (W : TorusField n) : 0 ≤ StepCosts.levelShare a L u Finset.univ y W := by
  cases u with
  | zero => exact Finset.sum_nonneg fun p _ => mul_nonneg (by positivity) (plaquetteEnergy_nonneg' _ _ _ _)
  | succ t => exact minimalCellShare_nonneg' ha _ _ _
private theorem shareHessian_annihilates {a : ℝ} (ha : 0 < a) (L : ℕ) [NeZero L] (u : ℕ) (y : TorusSite n)
    (hs : ContDiffThreeAt (StepCosts.levelShare a L u Finset.univ y) (trivialField n)) :
    AnnihilatesCurlFree (shareHessian a L u y) :=
  annihilates_of_minimum _ (contDiffAt_abelian _ hs) (fun _ => levelShare_nonneg' ha.le L u y _)
    fun A hA => levelShare_abelian_eq_zero ha L u y A hA
end Shares
section Forms
variable {n : ℕ} [NeZero n]
private theorem sum_sum_sum_comm {α β γ : Type*} (s : Finset α) (t : Finset β) (u : Finset γ)
    (f : α → β → γ → ℝ) :
    ∑ x ∈ s, ∑ y ∈ t, ∑ z ∈ u, f x y z = ∑ z ∈ u, ∑ x ∈ s, ∑ y ∈ t, f x y z := by
  have h : ∑ x ∈ s, ∑ y ∈ t, ∑ z ∈ u, f x y z = ∑ x ∈ s, ∑ z ∈ u, ∑ y ∈ t, f x y z :=
    Finset.sum_congr rfl fun x _ => Finset.sum_comm
  rw [h, Finset.sum_comm]
private theorem bilinearEval_pullback (a ρA : ℝ) (L u : ℕ) [NeZero L] (q : BondBilinear (n * L))
    (A A' : TorusBond n → ℝ) :
    bilinearEval (pullbackForm a ρA L u q) A A' =
      bilinearEval q (responseMap a ρA L u A) (responseMap a ρA L u A') := by
  unfold bilinearEval pullbackForm responseMap
  have key : ∀ b b' : TorusBond (n * L), (∑ c, responseKernel a ρA L u b c * A c) * q b b' *
      (∑ c', responseKernel a ρA L u b' c' * A' c') =
      ∑ c, ∑ c', A c * (responseKernel a ρA L u b c * q b b' * responseKernel a ρA L u b' c') * A' c' := by
    intro b b'
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c' _ => ?_
    ring
  simp only [key]
  have left : ∀ c c' : TorusBond n,
      A c * (∑ b, ∑ b', responseKernel a ρA L u b c * q b b' * responseKernel a ρA L u b' c') * A' c' =
      ∑ b, ∑ b', A c * (responseKernel a ρA L u b c * q b b' * responseKernel a ρA L u b' c') * A' c' := by
    intro c c'
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
  simp only [left]
  rw [sum_sum_sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [sum_sum_sum_comm]
private theorem bilinearEval_finset_sum {ι : Type*} (s : Finset ι) (Q : ι → BondBilinear n)
    (A A' : TorusBond n → ℝ) :
    bilinearEval (fun c c' => ∑ y ∈ s, Q y c c') A A' = ∑ y ∈ s, bilinearEval (Q y) A A' := by
  unfold bilinearEval
  simp only [Finset.mul_sum, Finset.sum_mul]
  exact sum_sum_sum_comm _ _ _ _
private theorem bilinearEval_smul_add (r : ℝ) (q q' : BondBilinear n) (A A' : TorusBond n → ℝ) :
    bilinearEval (fun b b' => r * q b b' + q' b b') A A' = r * bilinearEval q A A' + bilinearEval q' A A' := by
  unfold bilinearEval
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  ring
end Forms
section Weights
private theorem isPlaquetteAt_of_mem_block (L : ℕ) [NeZero L] (t n : ℕ) [NeZero n] (Y : TorusSite n)
    (y : TorusSite (n * L)) (hy : y ∈ TorusLumps.sitesInBlocks L {Y}) (p : TorusPlaquette (fineSide L t (n * L)))
    (h : IsPlaquetteAt L t y p) : IsPlaquetteAt L (t + 1) Y p := by
  obtain ⟨h1, c, hc, hb⟩ := h
  refine ⟨h1, c, hc, ?_⟩
  show c ∈ (TorusLumps.sitesInBlocks L {Y}).biUnion fun y => fineBlock L t (n * L) y
  exact Finset.mem_biUnion.2 ⟨y, hy, hb⟩
private theorem isPlaquetteAt_of_vertex {L : ℕ} [NeZero L] {n : ℕ} [NeZero n] (y : TorusSite n)
    (p : TorusPlaquette n) (hp : p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)))
    (hc : vertexMultiplicity y p ≠ 0) : IsPlaquetteAt L 0 y p := by
  have h0 : 0 < (plaquetteVertices p.1 p.2.1 p.2.2).count y :=
    Nat.pos_of_ne_zero fun h => hc (by simp [vertexMultiplicity, h])
  have hm : y ∈ plaquetteVertices p.1 p.2.1 p.2.2 := List.count_pos_iff.1 h0
  refine ⟨(Finset.mem_filter.1 hp).2.1, y, hm, ?_⟩
  show y ∈ ({y} : Finset (TorusSite n))
  exact Finset.mem_singleton_self y
private theorem blockMean_congr' (L : ℕ) [NeZero L] :
    ∀ (t n : ℕ) [NeZero n] (y : TorusSite n) (h h' : PlaquetteWeight (fineSide L t n)),
      (∀ p, IsPlaquetteAt L t y p → h p = h' p) → blockMean L t n y h = blockMean L t n y h'
  | 0, n, _, y, h, h', hh => by
    show (1 / 24) * ∑ p ∈ plaquettesIn Finset.univ, vertexMultiplicity y p * h p =
      (1 / 24) * ∑ p ∈ plaquettesIn Finset.univ, vertexMultiplicity y p * h' p
    congr 1
    refine Finset.sum_congr rfl fun p hp => ?_
    by_cases hc : vertexMultiplicity y p = 0
    · rw [hc, zero_mul, zero_mul]
    · rw [hh p (isPlaquetteAt_of_vertex y p hp hc)]
  | t + 1, n, _, Y, h, h', hh => by
    show ((L : ℝ) ^ 4)⁻¹ * ∑ y ∈ TorusLumps.sitesInBlocks L {Y}, blockMean L t (n * L) y h =
      ((L : ℝ) ^ 4)⁻¹ * ∑ y ∈ TorusLumps.sitesInBlocks L {Y}, blockMean L t (n * L) y h'
    congr 1
    refine Finset.sum_congr rfl fun y hy => ?_
    exact blockMean_congr' L t (n * L) y h h' fun p hp => hh p (isPlaquetteAt_of_mem_block L t n Y y hy p hp)
private theorem blockMean_eq_zero' (L : ℕ) [NeZero L] :
    ∀ (t n : ℕ) [NeZero n] (y : TorusSite n) (h : PlaquetteWeight (fineSide L t n)),
      (∀ p, h p = 0) → blockMean L t n y h = 0
  | 0, n, _, y, h, hh => by
    show (1 / 24) * ∑ p ∈ plaquettesIn Finset.univ, vertexMultiplicity y p * h p = 0
    rw [Finset.sum_eq_zero fun p _ => by rw [hh p, mul_zero], mul_zero]
  | t + 1, n, _, Y, h, hh => by
    show ((L : ℝ) ^ 4)⁻¹ * ∑ y ∈ TorusLumps.sitesInBlocks L {Y}, blockMean L t (n * L) y h = 0
    rw [Finset.sum_eq_zero fun y _ => blockMean_eq_zero' L t (n * L) y h hh, mul_zero]
end Weights
section LevelZero
variable {L : ℕ} [NeZero L]
private def IsWilsonResponse {u₀ : ℕ} (P : ColdResponse L u₀) : Prop :=
  ∀ (n : ℕ) [NeZero n] (y : TorusSite n) (W : TorusField n) (h : PlaquetteWeight n)
    (h' : PlaquetteWeight (fineSide L u₀ n)), HEq h h' → P n y W h' = siteResponse y W h
private theorem responseRemainder_eq (P : ColdResponse L 0) (hz : IsWilsonResponse P) (n : ℕ) [NeZero n]
    (y : TorusSite n) (h : PlaquetteWeight n) (W : TorusField n) :
    responseRemainder P n y h W = ∑ p ∈ plaquettesIn Finset.univ,
      (vertexMultiplicity y p / 4 * (h p - blockMean L 0 n y h)) * plaquetteEnergyOf W p := by
  unfold responseRemainder
  rw [hz n y W h h HEq.rfl, hz n y W (constOneWeight n) (constOneWeight _) HEq.rfl]
  simp only [siteResponse, constOneWeight, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring
private theorem plaquetteSum_annihilates {n : ℕ} [NeZero n] (c : TorusPlaquette n → ℝ) :
    AnnihilatesCurlFree (hessianAtIdentity fun W => ∑ p ∈ plaquettesIn Finset.univ, c p * plaquetteEnergyOf W p) := by
  let pr : TorusBond n → ((TorusBond n → ℝ) →L[ℝ] ℝ) := fun b => ContinuousLinearMap.proj b
  let κ : TorusPlaquette n → ((TorusBond n → ℝ) →L[ℝ] ℝ) := fun p =>
    pr (p.1, p.2.1) + pr (p.1 + unitStep n p.2.1, p.2.2) - pr (p.1 + unitStep n p.2.2, p.2.1) - pr (p.1, p.2.2)
  have hκ : ∀ (p : TorusPlaquette n) (σ : TorusBond n → ℝ), curl σ p = κ p σ := fun _ _ => rfl
  let g : TorusPlaquette n → (TorusBond n → ℝ) → ℝ := fun p σ => 1 - Real.cos (κ p σ)
  have hg : ∀ p, ContDiff ℝ 2 (g p) := fun p =>
    contDiff_const.sub (Real.contDiff_cos.comp (κ p).contDiff)
  have hform : (fun σ : TorusBond n → ℝ => ∑ p ∈ plaquettesIn Finset.univ, c p * plaquetteEnergyOf (abelianField σ) p) =
      fun σ => ∑ p ∈ plaquettesIn Finset.univ, c p * g p σ := by
    funext σ
    refine Finset.sum_congr rfl fun p _ => ?_
    show c p * plaquetteEnergy (abelianField σ) p.1 p.2.1 p.2.2 = _
    rw [plaquetteEnergy_abelianField]
    rfl
  have hC : ContDiff ℝ 2 fun σ : TorusBond n → ℝ => ∑ p ∈ plaquettesIn Finset.univ, c p * g p σ :=
    ContDiff.sum fun p _ => contDiff_const.mul (hg p)
  refine annihilates_of_critical _ (by rw [hform]; exact hC.contDiffAt) fun A hA τ => ?_
  rw [hform]
  have hloc : ∀ p, HasFDerivAt (g p) (0 : (TorusBond n → ℝ) →L[ℝ] ℝ) (τ • A) := by
    intro p
    have hmin : IsLocalMin (g p) (τ • A) := by
      refine Eventually.of_forall fun σ => ?_
      have h0 : κ p (τ • A) = 0 := by rw [← hκ, curl_smul_left, hA p, mul_zero]
      show 1 - Real.cos (κ p (τ • A)) ≤ 1 - Real.cos (κ p σ)
      rw [h0, Real.cos_zero]
      linarith [Real.cos_le_one (κ p σ)]
    have hd := ((hg p).differentiable (by norm_num)) (τ • A)
    have := hd.hasFDerivAt
    rwa [hmin.fderiv_eq_zero] at this
  have hs : ∀ s : Finset (TorusPlaquette n), HasFDerivAt (fun σ : TorusBond n → ℝ => ∑ p ∈ s, c p * g p σ)
      (0 : (TorusBond n → ℝ) →L[ℝ] ℝ) (τ • A) := by
    classical
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hasFDerivAt_const (0 : ℝ) (τ • A)
    | insert p s hp ih =>
      have h2 := ((hloc p).const_mul (c p)).add ih
      refine (h2.congr_fderiv (by simp)).congr_of_eventuallyEq (Eventually.of_forall fun σ => ?_)
      show ∑ q ∈ insert p s, c q * g q σ = c p * g p σ + ∑ q ∈ s, c q * g q σ
      rw [Finset.sum_insert hp]
  exact (hs _).fderiv
private theorem remainder_annihilates {u₀ : ℕ} (hu : u₀ = 0) (P : ColdResponse L u₀) (hz : IsWilsonResponse P)
    (n : ℕ) [NeZero n] (y : TorusSite n) (h : PlaquetteWeight (fineSide L u₀ n)) :
    AnnihilatesCurlFree (hessianAtIdentity (responseRemainder P n y h)) := by
  subst hu
  have e : responseRemainder P n y h = fun W => ∑ p ∈ plaquettesIn Finset.univ,
      (vertexMultiplicity y p / 4 * (h p - blockMean L 0 n y h)) * plaquetteEnergyOf W p :=
    funext (responseRemainder_eq P hz n y h)
  rw [e]
  exact plaquetteSum_annihilates _
private theorem remainder_congr {u₀ : ℕ} (hu : u₀ = 0) (P : ColdResponse L u₀) (hz : IsWilsonResponse P)
    (n : ℕ) [NeZero n] (y : TorusSite n) (h h' : PlaquetteWeight (fineSide L u₀ n))
    (hh : ∀ p, IsPlaquetteAt L u₀ y p → h p = h' p) :
    responseRemainder P n y h = responseRemainder P n y h' := by
  subst hu
  funext W
  rw [responseRemainder_eq P hz n y h W, responseRemainder_eq P hz n y h' W, blockMean_congr' L 0 n y h h' hh]
  refine Finset.sum_congr rfl fun p hp => ?_
  by_cases hc : vertexMultiplicity y p = 0
  · simp [hc]
  · rw [hh p (isPlaquetteAt_of_vertex y p hp hc)]
private theorem remainder_eq_zero {u₀ : ℕ} (hu : u₀ = 0) (P : ColdResponse L u₀) (hz : IsWilsonResponse P)
    (n : ℕ) [NeZero n] (y : TorusSite n) (h : PlaquetteWeight (fineSide L u₀ n)) (hh : ∀ p, h p = 0) :
    responseRemainder P n y h = fun _ => 0 := by
  subst hu
  funext W
  rw [responseRemainder_eq P hz n y h W, blockMean_eq_zero' L 0 n y h hh]
  exact Finset.sum_eq_zero fun p _ => by rw [hh p]; simp
end LevelZero
section Tower
variable {ℓ : TorusLumps.StepParameters} (T : StageTower ℓ) (A : ∀ t, ResponseSetup (T.stage t).toStepSetup)
private theorem classicalRemainder_succ (t n : ℕ) [NeZero n]
    (h : PlaquetteWeight (fineSide ℓ.side (T.stage (t + 1)).depth n)) (Y : TorusSite n) :
    classicalRemainder T A (t + 1) n h Y = fun c c' => ∑ y ∈ TorusLumps.sitesInBlocks ℓ.side {Y},
      pullbackForm ℓ.coupling (T.stage t).anchorRadius ℓ.side (T.stage t).depth (n := n) (fun b b' =>
        (blockMean ℓ.side (T.stage t).depth (n * ℓ.side) y h - blockMean ℓ.side ((T.stage t).depth + 1) n Y h) *
            shareHessian ℓ.coupling ℓ.side (T.stage t).depth y b b' +
          classicalRemainder T A t (n * ℓ.side) h y b b') c c' := rfl
private theorem classicalRemainder_annihilates
    (hL : ∀ n : ℕ, ℓ.n₀ ≤ n → ℓ.n₀ ≤ n * ℓ.side)
    (hM : ∀ (t n : ℕ) [NeZero n], ℓ.n₀ ≤ n → ∀ B : TorusBond n → ℝ, (∀ p, curl B p = 0) →
      ∀ p, curl (responseMap ℓ.coupling (T.stage t).anchorRadius ℓ.side (T.stage t).depth B) p = 0)
    (hS : ∀ (u n : ℕ) [NeZero n], ℓ.n₀ ≤ n → ∀ y : TorusSite n,
      AnnihilatesCurlFree (shareHessian ℓ.coupling ℓ.side u y))
    (h0 : ∀ (n : ℕ) [NeZero n] (y : TorusSite n) (h : PlaquetteWeight (fineSide ℓ.side (T.stage 0).depth n)),
      AnnihilatesCurlFree (remainderHessian (A 0) n y h)) :
    ∀ (t n : ℕ) [NeZero n], ℓ.n₀ ≤ n → ∀ (h : PlaquetteWeight (fineSide ℓ.side (T.stage t).depth n))
      (y : TorusSite n), AnnihilatesCurlFree (classicalRemainder T A t n h y)
  | 0, n, _, _, h, y => h0 n y h
  | t + 1, n, _, hn, h, Y => by
    intro B hB B'
    have hMB := hM t n hn B hB
    have hn' := hL n hn
    rw [classicalRemainder_succ]
    constructor
    · rw [bilinearEval_finset_sum]
      refine Finset.sum_eq_zero fun y _ => ?_
      rw [bilinearEval_pullback, bilinearEval_smul_add, (hS _ _ hn' y _ hMB _).1,
        (classicalRemainder_annihilates hL hM hS h0 t (n * ℓ.side) hn' h y _ hMB _).1, mul_zero, add_zero]
    · rw [bilinearEval_finset_sum]
      refine Finset.sum_eq_zero fun y _ => ?_
      rw [bilinearEval_pullback, bilinearEval_smul_add, (hS _ _ hn' y _ hMB _).2,
        (classicalRemainder_annihilates hL hM hS h0 t (n * ℓ.side) hn' h y _ hMB _).2, mul_zero, add_zero]
private theorem classicalRemainder_congr
    (h0 : ∀ (n : ℕ) [NeZero n] (y : TorusSite n) (h h' : PlaquetteWeight (fineSide ℓ.side (T.stage 0).depth n)),
      (∀ p, IsPlaquetteAt ℓ.side (T.stage 0).depth y p → h p = h' p) →
        remainderHessian (A 0) n y h = remainderHessian (A 0) n y h') :
    ∀ (t n : ℕ) [NeZero n] (y : TorusSite n) (h h' : PlaquetteWeight (fineSide ℓ.side (T.stage t).depth n)),
      (∀ p, IsPlaquetteAt ℓ.side (T.stage t).depth y p → h p = h' p) →
        classicalRemainder T A t n h y = classicalRemainder T A t n h' y
  | 0, n, _, y, h, h', hh => h0 n y h h' hh
  | t + 1, n, _, Y, h, h', hh => by
    rw [classicalRemainder_succ, classicalRemainder_succ]
    funext c c'
    refine Finset.sum_congr rfl fun y hy => ?_
    have hy' : ∀ p, IsPlaquetteAt ℓ.side (T.stage t).depth y p → h p = h' p :=
      fun p hp => hh p (isPlaquetteAt_of_mem_block ℓ.side _ n Y y hy p hp)
    rw [blockMean_congr' ℓ.side (T.stage t).depth (n * ℓ.side) y h h' hy',
      blockMean_congr' ℓ.side ((T.stage t).depth + 1) n Y h h' hh,
      classicalRemainder_congr h0 t (n * ℓ.side) y h h' hy']
private theorem classicalRemainder_eq_zero
    (h0 : ∀ (n : ℕ) [NeZero n] (y : TorusSite n) (h : PlaquetteWeight (fineSide ℓ.side (T.stage 0).depth n)),
      (∀ p, h p = 0) → remainderHessian (A 0) n y h = 0) :
    ∀ (t n : ℕ) [NeZero n] (y : TorusSite n) (h : PlaquetteWeight (fineSide ℓ.side (T.stage t).depth n)),
      (∀ p, h p = 0) → classicalRemainder T A t n h y = 0
  | 0, n, _, y, h, hh => h0 n y h hh
  | t + 1, n, _, Y, h, hh => by
    rw [classicalRemainder_succ]
    funext c c'
    refine Finset.sum_eq_zero fun y _ => ?_
    have e : (fun b b' => (blockMean ℓ.side (T.stage t).depth (n * ℓ.side) y h -
        blockMean ℓ.side ((T.stage t).depth + 1) n Y h) * shareHessian ℓ.coupling ℓ.side (T.stage t).depth y b b' +
        classicalRemainder T A t (n * ℓ.side) h y b b') = fun _ _ => (0 : ℝ) := by
      funext b b'
      rw [blockMean_eq_zero' ℓ.side (T.stage t).depth (n * ℓ.side) y h hh,
        blockMean_eq_zero' ℓ.side ((T.stage t).depth + 1) n Y h hh,
        classicalRemainder_eq_zero h0 t (n * ℓ.side) y h hh]
      simp
    rw [e]
    simp [pullbackForm]
end Tower
section Point
private theorem hessianAtIdentity_zero {n : ℕ} [NeZero n] :
    hessianAtIdentity (fun _ : TorusField n => (0 : ℝ)) = 0 := by
  funext b b'
  simp [hessianAtIdentity, mixedDeriv]
private theorem momentPoint_annihilates {Λ : MomentParameters} (S : MomentPoint Λ) (ha : 0 < Λ.stepParams.coupling)
    (hM : ∀ (u n : ℕ) [NeZero n], Λ.stepParams.n₀ ≤ n → ∀ B : TorusBond n → ℝ, (∀ p, curl B p = 0) →
      ∀ p, curl (responseMap Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side u B) p = 0)
    (hS : ∀ (u n : ℕ) [NeZero n], Λ.stepParams.n₀ ≤ n → ∀ y : TorusSite n,
      ContDiffThreeAt (StepCosts.levelShare Λ.stepParams.coupling Λ.stepParams.side u Finset.univ y) (trivialField n))
    (t n : ℕ) [NeZero n] (hn : Λ.stepParams.n₀ ≤ n) (y : TorusSite n)
    (h : PlaquetteWeight (fineSide Λ.stepParams.side (S.tower.stage t).depth n)) :
    AnnihilatesClosedForms (classicalRemainder S.tower S.resp t n h y) ∧
    AnnihilatesClosedForms (classicalQuadratic S.tower S.resp t n h y) ∧
    (∀ h' : PlaquetteWeight (fineSide Λ.stepParams.side (S.tower.stage t).depth n),
      (∀ p, IsPlaquetteAt Λ.stepParams.side (S.tower.stage t).depth y p → h p = h' p) →
      classicalRemainder S.tower S.resp t n h y = classicalRemainder S.tower S.resp t n h' y ∧
        classicalQuadratic S.tower S.resp t n h y = classicalQuadratic S.tower S.resp t n h' y) ∧
    ((∀ p, IsPlaquetteAt Λ.stepParams.side (S.tower.stage t).depth y p → h p = 0) →
      classicalRemainder S.tower S.resp t n h y = 0 ∧ classicalQuadratic S.tower S.resp t n h y = 0) := by
  have hρ : ∀ t, (S.tower.stage t).anchorRadius = Λ.table.ρA := by
    intro t
    induction t with
    | zero =>
      have e := congrArg (fun z : ResponseInTheExpansion.StageWithResponse Λ.stepParams => z.1.anchorRadius)
        (S.stage_eq 0 (Nat.zero_le _))
      exact e.trans S.isInitial.anchorRadius_eq
    | succ t ih => exact ih
  have hu : (S.tower.stage 0).depth = 0 := by
    have e := congrArg (fun z : ResponseInTheExpansion.StageWithResponse Λ.stepParams => z.1.depth)
      (S.stage_eq 0 (Nat.zero_le _))
    exact e.trans S.isInitial.depth_eq
  have hz : IsWilsonResponse (S.resp 0).cold := S.cold_zero
  have hKS : ∀ (u n : ℕ) [NeZero n], Λ.stepParams.n₀ ≤ n → ∀ y : TorusSite n,
      AnnihilatesCurlFree (shareHessian Λ.stepParams.coupling Λ.stepParams.side u y) :=
    fun u n _ hn y => shareHessian_annihilates ha _ u y (hS u n hn y)
  have hKR : ∀ (t n : ℕ) [NeZero n], Λ.stepParams.n₀ ≤ n →
      ∀ (h : PlaquetteWeight (fineSide Λ.stepParams.side (S.tower.stage t).depth n)) (y : TorusSite n),
      AnnihilatesCurlFree (classicalRemainder S.tower S.resp t n h y) :=
    classicalRemainder_annihilates S.tower S.resp
      (fun n hn => hn.trans (Nat.le_mul_of_pos_right n (Nat.pos_of_ne_zero (NeZero.ne _))))
      (fun t n _ hn B hB p => by rw [hρ t]; exact hM _ n hn B hB p) hKS
      fun n _ y h => remainder_annihilates hu (S.resp 0).cold hz n y h
  have hread := classicalRemainder_congr S.tower S.resp
    fun n _ y h h' hh => congrArg hessianAtIdentity (remainder_congr hu (S.resp 0).cold hz n y h h' hh)
  have hzero := classicalRemainder_eq_zero S.tower S.resp fun n _ y h hh => by
    show hessianAtIdentity (responseRemainder (S.resp 0).cold n y h) = 0
    rw [remainder_eq_zero hu (S.resp 0).cold hz n y h hh, hessianAtIdentity_zero]
  have closed : ∀ q : BondBilinear n, AnnihilatesCurlFree q → AnnihilatesClosedForms q := fun q hq =>
    ⟨fun φ A => hq _ (curl_latticeGradient φ) A, fun v A => hq _ (curl_constantOneForm v) A⟩
  have hform : AnnihilatesCurlFree (classicalQuadratic S.tower S.resp t n h y) := by
    intro B hB B'
    unfold classicalQuadratic
    rw [bilinearEval_smul_add, bilinearEval_smul_add, (hKS _ n hn y B hB B').1, (hKS _ n hn y B hB B').2,
      (hKR t n hn h y B hB B').1, (hKR t n hn h y B hB B').2]
    simp
  have hreads : ∀ h' : PlaquetteWeight (fineSide Λ.stepParams.side (S.tower.stage t).depth n),
      (∀ p, IsPlaquetteAt Λ.stepParams.side (S.tower.stage t).depth y p → h p = h' p) →
      classicalRemainder S.tower S.resp t n h y = classicalRemainder S.tower S.resp t n h' y ∧
        classicalQuadratic S.tower S.resp t n h y = classicalQuadratic S.tower S.resp t n h' y := by
    intro h' hh
    have e := hread t n y h h' hh
    refine ⟨e, ?_⟩
    unfold classicalQuadratic
    rw [e, blockMean_congr' Λ.stepParams.side _ n y h h' hh]
  refine ⟨closed _ (hKR t n hn h y), closed _ hform, hreads, fun h0 => ?_⟩
  obtain ⟨e1, e2⟩ := hreads 0 h0
  have e3 := hzero t n y 0 fun _ => rfl
  refine ⟨e1.trans e3, e2.trans ?_⟩
  unfold classicalQuadratic
  rw [e3, blockMean_eq_zero' Λ.stepParams.side _ n y 0 fun _ => rfl]
  funext b b'
  simp
end Point
end ClosedFormAnnihilation
theorem classicalFormsAnnihilateClosed (h₁ : responseMapClosedFormsStatement)
    (h₂ : ResponseInTheExpansion.levelSharesUniformStatement) : classicalFormsAnnihilateClosedStatement := by
  intro a ha
  obtain ⟨L₁, rt₁, C₁, hr₁, H₁⟩ := h₁ a ha
  obtain ⟨L₂, rt₂, C₂, hr₂, H₂⟩ := h₂ a ha
  refine ⟨max L₁ L₂, fun c => min (rt₁ c) (rt₂ c), max C₁ C₂, fun c => lt_min (hr₁ c) (hr₂ c), ?_⟩
  intro L hLo hL Tb hTa hTL hD hCS hCH hrt hC Kr _
  obtain ⟨y₁, Y₁⟩ := H₁ L hLo ((le_max_left _ _).trans hL) Tb hTa hTL hD hCS hCH (hrt.trans (min_le_left _ _))
    ((le_max_left _ _).trans hC)
  obtain ⟨y₂, Y₂⟩ := H₂ L hLo ((le_max_right _ _).trans hL) Tb hTa hTL hD hCS hCH (hrt.trans (min_le_right _ _))
    ((le_max_right _ _).trans hC)
  refine ⟨max y₁ y₂, fun y hy hR hW g _ _ k _ _ _ R d _ => ?_⟩
  have P₁ := Y₁ y ((le_max_left _ _).trans hy) hR hW
  obtain ⟨Cs, _, P₂⟩ := Y₂ y ((le_max_right _ _).trans hy) hR hW
  refine ⟨fun _ => 0, 1, y, one_pos, le_rfl, fun S t _ n _ hn yy h => ?_⟩
  have h64 : ∀ m : ℕ, Tb.n₀ ≤ m → 64 ≤ m := fun m hm => le_trans (by have := hD.n₀_ge; omega) hm
  have hflat : ∀ (m : ℕ), IsCold Tb.threshold (trivialField m) := fun m x μ ν _ => by
    simpa [curvature, holonomy, trivialField] using hD.σ_pos
  refine ClosedFormAnnihilation.momentPoint_annihilates S (lt_of_lt_of_le one_pos hD.a_ge) ?_ ?_ t n hn yy h
  · intro u m _ hm B hB p
    have e := (P₁ u m (h64 m hm)).2.2 B 0 (fun q => by rw [hB q]; simp [curl]) p
    exact e.trans (by simp [curl, responseMap])
  · intro u m _ hm z
    have e : ShareFamilies.levelShareFamily (Tb.stepParameters y).coupling (Tb.stepParameters y).side u m z =
        StepCosts.levelShare (Tb.stepParameters y).coupling (Tb.stepParameters y).side u Finset.univ z := by
      funext V
      simp [ShareFamilies.levelShareFamily, NeZero.ne m]
    have := (P₂ u).1.smooth m hm z (trivialField m) (hflat m)
    rw [show ShareFamilies.levelShareFamily (Tb.stepParameters y).coupling (Tb.stepParameters y).side u m z = _
      from e] at this
    exact this
end MomentLaw
end YangMills.Construction
end
