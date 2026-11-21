import YangMills.Construction.HilbertSpace.SemidefiniteFormCompletion
import Mathlib
set_option autoImplicit false
open Filter Topology
open scoped ComplexConjugate InnerProductSpace
noncomputable section
namespace YangMills.Construction
namespace FormCompletion
variable {𝒜 : Type*}
def IsDualCauchy (q : 𝒜 → 𝒜 → ℂ) (u : ℕ → 𝒜 → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ l ≥ n₀, dualNorm q (u n - u l) < ε
def IsDualComplete (q : 𝒜 → 𝒜 → ℂ) (S : Set (𝒜 → ℂ)) : Prop :=
  ∀ u : ℕ → 𝒜 → ℂ, (∀ n, u n ∈ S) → IsDualCauchy q u →
    ∃ φ ∈ S, Tendsto (fun n => dualNorm q (u n - φ)) atTop (𝓝 0)
structure IsDualNormOn (q : 𝒜 → 𝒜 → ℂ) (S : Set (𝒜 → ℂ)) : Prop where
  nonneg : ∀ φ ∈ S, 0 ≤ dualNorm q φ
  eq_zero : ∀ φ ∈ S, dualNorm q φ = 0 → φ = 0
  add_le : ∀ φ ∈ S, ∀ φ' ∈ S, dualNorm q (φ + φ') ≤ dualNorm q φ + dualNorm q φ'
  smul : ∀ (z : ℂ), ∀ φ ∈ S, dualNorm q (z • φ) = ‖z‖ * dualNorm q φ
variable [AddCommGroup 𝒜] [Module ℂ 𝒜]
structure IsCompletionInner (q : 𝒜 → 𝒜 → ℂ) (s : (𝒜 → ℂ) → (𝒜 → ℂ) → ℂ) : Prop where
  add_left : ∀ φ ∈ formCompletion q, ∀ φ' ∈ formCompletion q, ∀ ψ ∈ formCompletion q,
    s (φ + φ') ψ = s φ ψ + s φ' ψ
  smul_left : ∀ (z : ℂ), ∀ φ ∈ formCompletion q, ∀ ψ ∈ formCompletion q,
    s (z • φ) ψ = conj z * s φ ψ
  add_right : ∀ φ ∈ formCompletion q, ∀ ψ ∈ formCompletion q, ∀ ψ' ∈ formCompletion q,
    s φ (ψ + ψ') = s φ ψ + s φ ψ'
  smul_right : ∀ (z : ℂ), ∀ φ ∈ formCompletion q, ∀ ψ ∈ formCompletion q,
    s φ (z • ψ) = z * s φ ψ
  diagonal : ∀ φ ∈ formCompletion q, s φ φ = (dualNorm q φ : ℂ) ^ 2
def completionInner (q : 𝒜 → 𝒜 → ℂ) : (𝒜 → ℂ) → (𝒜 → ℂ) → ℂ :=
  Classical.epsilon (IsCompletionInner q)
structure HasHilbertStructure (q : 𝒜 → 𝒜 → ℂ) : Prop where
  linear : (Submodule.span ℂ (formCompletion q) : Set (𝒜 → ℂ)) = formCompletion q
  form : IsCompletionInner q (completionInner q)
  hermitian : ∀ φ ∈ formCompletion q, ∀ ψ ∈ formCompletion q,
    completionInner q ψ φ = conj (completionInner q φ ψ)
  norm : IsDualNormOn q (formCompletion q)
  complete : IsDualComplete q (formCompletion q)
open Classical in
def hilbertSubmodule (q : 𝒜 → 𝒜 → ℂ) : Submodule ℂ (𝒜 → ℂ) :=
  if HasHilbertStructure q then Submodule.span ℂ (formCompletion q) else ⊥
def FormHilbertSpace (q : 𝒜 → 𝒜 → ℂ) : Type _ := hilbertSubmodule q
variable {q : 𝒜 → 𝒜 → ℂ}
instance : AddCommGroup (FormHilbertSpace q) := inferInstanceAs (AddCommGroup (hilbertSubmodule q))
instance : Module ℂ (FormHilbertSpace q) := inferInstanceAs (Module ℂ (hilbertSubmodule q))
def asMap (φ : FormHilbertSpace q) : 𝒜 → ℂ := Subtype.val (p := (· ∈ hilbertSubmodule q)) φ
theorem asMap_injective : Function.Injective (asMap (q := q)) :=
  Subtype.val_injective
theorem asMap_add (φ ψ : FormHilbertSpace q) : asMap (φ + ψ) = asMap φ + asMap ψ := rfl
theorem asMap_sub (φ ψ : FormHilbertSpace q) : asMap (φ - ψ) = asMap φ - asMap ψ := rfl
theorem asMap_smul (z : ℂ) (φ : FormHilbertSpace q) : asMap (z • φ) = z • asMap φ := rfl
theorem mem_hilbertSubmodule (hq : HasHilbertStructure q) {φ : 𝒜 → ℂ} :
    φ ∈ hilbertSubmodule q ↔ φ ∈ formCompletion q := by
  rw [hilbertSubmodule, if_pos hq, ← SetLike.mem_coe, hq.linear]
theorem asMap_mem (hq : HasHilbertStructure q) (φ : FormHilbertSpace q) :
    asMap φ ∈ formCompletion q :=
  (mem_hilbertSubmodule hq).1 φ.2
@[instance_reducible] def innerCoreOfStructure (hq : HasHilbertStructure q) :
    InnerProductSpace.Core ℂ (FormHilbertSpace q) where
  inner φ ψ := completionInner q (asMap φ) (asMap ψ)
  conj_inner_symm φ ψ := (hq.hermitian _ (asMap_mem hq ψ) _ (asMap_mem hq φ)).symm
  re_inner_nonneg φ := by
    have hd := hq.form.diagonal _ (asMap_mem hq φ)
    simp only [hd, ← Complex.ofReal_pow, RCLike.re_to_complex, Complex.ofReal_re]
    positivity
  add_left φ φ' ψ := hq.form.add_left _ (asMap_mem hq φ) _ (asMap_mem hq φ') _ (asMap_mem hq ψ)
  smul_left φ ψ z := hq.form.smul_left z _ (asMap_mem hq φ) _ (asMap_mem hq ψ)
  definite φ h0 := by
    have hd := hq.form.diagonal _ (asMap_mem hq φ)
    have hz : dualNorm q (asMap φ) = 0 := by
      have h1 : (dualNorm q (asMap φ) : ℂ) ^ 2 = 0 := hd.symm.trans h0
      exact_mod_cast pow_eq_zero_iff (two_ne_zero) |>.1 h1
    exact asMap_injective (hq.norm.eq_zero _ (asMap_mem hq φ) hz)
theorem subsingleton_of_not_hasHilbertStructure (hq : ¬ HasHilbertStructure q) :
    Subsingleton (FormHilbertSpace q) := by
  have hb : hilbertSubmodule q = ⊥ := if_neg hq
  refine ⟨fun φ ψ => asMap_injective ?_⟩
  have h1 : asMap φ ∈ hilbertSubmodule q := φ.2
  have h2 : asMap ψ ∈ hilbertSubmodule q := ψ.2
  rw [hb, Submodule.mem_bot] at h1 h2
  rw [h1, h2]
@[instance_reducible] def innerCoreTrivial (hq : ¬ HasHilbertStructure q) :
    InnerProductSpace.Core ℂ (FormHilbertSpace q) where
  inner _ _ := 0
  conj_inner_symm _ _ := by simp
  re_inner_nonneg _ := by simp
  add_left _ _ _ := by simp
  smul_left _ _ _ := by simp
  definite φ _ := by
    have := subsingleton_of_not_hasHilbertStructure hq
    exact Subsingleton.elim _ _
open Classical in
@[instance_reducible] def innerCore (q : 𝒜 → 𝒜 → ℂ) :
    InnerProductSpace.Core ℂ (FormHilbertSpace q) :=
  if hq : HasHilbertStructure q then innerCoreOfStructure hq else innerCoreTrivial hq
instance : NormedAddCommGroup (FormHilbertSpace q) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (innerCore q)
instance : InnerProductSpace ℂ (FormHilbertSpace q) :=
  InnerProductSpace.ofCore (innerCore q).toCore
theorem inner_eq_completionInner (hq : HasHilbertStructure q) (φ ψ : FormHilbertSpace q) :
    inner ℂ φ ψ = completionInner q (asMap φ) (asMap ψ) := by
  change (innerCore q).inner φ ψ = _
  rw [innerCore, dif_pos hq]
  rfl
theorem norm_eq_dualNorm (hq : HasHilbertStructure q) (φ : FormHilbertSpace q) :
    ‖φ‖ = dualNorm q (asMap φ) := by
  have hn := hq.norm.nonneg _ (asMap_mem hq φ)
  rw [@norm_eq_sqrt_re_inner ℂ, inner_eq_completionInner hq, hq.form.diagonal _ (asMap_mem hq φ),
    ← Complex.ofReal_pow, RCLike.re_to_complex, Complex.ofReal_re, Real.sqrt_sq hn]
instance : CompleteSpace (FormHilbertSpace q) := by
  by_cases hq : HasHilbertStructure q
  · refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
    have hc : IsDualCauchy q (fun n => asMap (u n)) := fun ε hε => by
      obtain ⟨n₀, hn₀⟩ := Metric.cauchySeq_iff.1 hu ε hε
      refine ⟨n₀, fun n hn l hl => ?_⟩
      have := hn₀ n hn l hl
      rwa [dist_eq_norm, norm_eq_dualNorm hq, asMap_sub] at this
    obtain ⟨φ, hφ, hlim⟩ := hq.complete _ (fun n => asMap_mem hq (u n)) hc
    let a : FormHilbertSpace q := ⟨φ, (mem_hilbertSubmodule hq).2 hφ⟩
    refine ⟨a, tendsto_iff_norm_sub_tendsto_zero.2 ?_⟩
    have he : ∀ n, ‖u n - a‖ = dualNorm q (asMap (u n) - φ) := fun n => by
      rw [norm_eq_dualNorm hq, asMap_sub]
      rfl
    simpa only [he] using hlim
  · have := subsingleton_of_not_hasHilbertStructure hq
    infer_instance
open Classical in
def classVec (q : 𝒜 → 𝒜 → ℂ) (F : 𝒜) : FormHilbertSpace q :=
  if hF : formClass q F ∈ hilbertSubmodule q then ⟨formClass q F, hF⟩ else 0
def DualSpaceComplete (q : 𝒜 → 𝒜 → ℂ) : Prop :=
  (∃ S : Submodule ℂ (𝒜 → ℂ), (S : Set (𝒜 → ℂ)) = boundedConjLinearMaps q) ∧
  IsDualNormOn q (boundedConjLinearMaps q) ∧
  IsDualComplete q (boundedConjLinearMaps q) ∧
  (∀ F', formClass q F' ∈ boundedConjLinearMaps q) ∧
  (∀ F F', formClass q (F + F') = formClass q F + formClass q F') ∧
  (∀ (z : ℂ) F', formClass q (z • F') = z • formClass q F') ∧
  (∀ F', dualNorm q (formClass q F') = seminormOfForm q F') ∧
  ∀ F F', formClass q F = formClass q F' ↔ q (F - F') (F - F') = 0
def FormCompletionHilbert (q : 𝒜 → 𝒜 → ℂ) : Prop :=
  HasHilbertStructure q ∧
  (∀ s, IsCompletionInner q s → ∀ φ ∈ formCompletion q, ∀ ψ ∈ formCompletion q,
    s φ ψ = completionInner q φ ψ) ∧
  (hilbertSubmodule q : Set (𝒜 → ℂ)) = formCompletion q ∧
  (∀ φ ψ : FormHilbertSpace q, inner ℂ φ ψ = completionInner q (asMap φ) (asMap ψ)) ∧
  (∀ φ : FormHilbertSpace q, ‖φ‖ = dualNorm q (asMap φ)) ∧
  (∀ F, asMap (classVec q F) = formClass q F) ∧
  (∀ F F', inner ℂ (classVec q F) (classVec q F') = q F F') ∧
  (∃ S : Submodule ℂ (FormHilbertSpace q),
    (S : Set (FormHilbertSpace q)) = Set.range (classVec q)) ∧
  Dense (Set.range (classVec q))
def InducedOperators (q : 𝒜 → 𝒜 → ℂ) : Prop :=
  ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    (C : ℝ) (R : 𝒜 →ₗ[ℂ] H'), 0 ≤ C → (∀ F, ‖R F‖ ≤ C * seminormOfForm q F) →
    (∃! B : FormHilbertSpace q →L[ℂ] H', ∀ F, B (classVec q F) = R F) ∧
    ∀ B : FormHilbertSpace q →L[ℂ] H', (∀ F, B (classVec q F) = R F) →
      ‖B‖ ≤ C ∧
      ((∀ F, ‖R F‖ = seminormOfForm q F) →
        (∀ φ, ‖B φ‖ = ‖φ‖) ∧ Set.range B = closure (Set.range R))
def FormCompletionIsHilbertSpace : Prop :=
  ∀ (𝒜 : Type) [AddCommGroup 𝒜] [Module ℂ 𝒜] (q : 𝒜 → 𝒜 → ℂ),
    IsPosSemidefHermitianForm q →
      DualSpaceComplete q ∧ FormCompletionHilbert q ∧ InducedOperators q
end FormCompletion
end YangMills.Construction
end
