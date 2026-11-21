import YangMills.Construction.HilbertSpace.SpectralMeasuresSelfAdjoint
import YangMills.Construction.SpectralMeasures.EuclideanComplexMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ComplexConjugate ComplexOrder InnerProductSpace
noncomputable section
namespace YangMills.Construction.FormsOperators
open YangMills.Construction.EuclideanBorel (Space BorelSubset)
open YangMills.Construction.SpectralTheory (UnboundedOp)
section Sesquilinear
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
structure IsSesquilinear (q : V → V → ℂ) : Prop where
  add_left : ∀ x₁ x₂ y, q (x₁ + x₂) y = q x₁ y + q x₂ y
  smul_left : ∀ (c : ℂ) x y, q (c • x) y = conj c * q x y
  add_right : ∀ x y₁ y₂, q x (y₁ + y₂) = q x y₁ + q x y₂
  smul_right : ∀ (c : ℂ) x y, q x (c • y) = c * q x y
structure IsHermitianForm (q : V → V → ℂ) : Prop extends IsSesquilinear q where
  conj_symm : ∀ x y, q y x = conj (q x y)
structure IsPosSemidefForm (q : V → V → ℂ) : Prop extends IsSesquilinear q where
  nonneg : ∀ x, 0 ≤ q x x
structure IsInnerProductForm (q : V → V → ℂ) : Prop where
  hermitian : IsHermitianForm q
  positive : IsPosSemidefForm q
  definite : ∀ x, q x x = 0 → x = 0
end Sesquilinear
section Subsets
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
omit [CompleteSpace H] in
theorem norm_eq_sqrt_re_inner_self (ψ : H) : ‖ψ‖ = Real.sqrt (⟪ψ, ψ⟫_ℂ).re :=
  norm_eq_sqrt_re_inner (𝕜 := ℂ) ψ
def IsDenseWithin (S D : Set H) : Prop :=
  S ⊆ D ∧ ∀ ψ ∈ D, ∀ ε : ℝ, 0 < ε → ({φ | ‖φ - ψ‖ < ε} ∩ S).Nonempty
def IsDenseSet (S : Set H) : Prop := IsDenseWithin S univ
omit [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem isDenseSet_iff_dense (S : Set H) : IsDenseSet S ↔ Dense S := by
  constructor
  · intro h ψ
    refine Metric.mem_closure_iff.mpr fun ε hε => ?_
    obtain ⟨φ, hφ, hS⟩ := h.2 ψ (mem_univ ψ) ε hε
    exact ⟨φ, hS, by rwa [dist_comm, dist_eq_norm]⟩
  · intro h
    refine ⟨subset_univ S, fun ψ _ ε hε => ?_⟩
    obtain ⟨φ, hS, hφ⟩ := Metric.mem_closure_iff.mp (h ψ) ε hε
    exact ⟨φ, by rwa [dist_comm, dist_eq_norm] at hφ, hS⟩
variable (H) in
def HasCountableDenseSet : Prop := ∃ S : Set H, S.Countable ∧ IsDenseSet S
def IsSeqClosedSubmodule (M : Submodule ℂ H) : Prop :=
  ∀ (u : ℕ → H) (ψ : H), (∀ k, u k ∈ M) → Tendsto u atTop (𝓝 ψ) → ψ ∈ M
omit [CompleteSpace H] in
theorem isSeqClosedSubmodule_iff (M : Submodule ℂ H) :
    IsSeqClosedSubmodule M ↔ IsClosed (M : Set H) := by
  constructor
  · intro h
    refine isClosed_of_closure_subset fun ψ hψ => ?_
    obtain ⟨u, hu, hl⟩ := mem_closure_iff_seq_limit.mp hψ
    exact h u ψ hu hl
  · intro h u ψ hu hl
    exact h.mem_of_tendsto hl (Eventually.of_forall hu)
def complexLine (ψ : H) : Set H := {φ | ∃ c : ℂ, φ = c • ψ}
structure IsHilbertCompletion {V₁ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [CompleteSpace H]
    (q : V₁ → V₁ → ℂ) (j : V₁ →ₗ[ℂ] H) : Prop where
  isInnerProduct : IsInnerProductForm q
  inner_map : ∀ u v, ⟪j u, j v⟫_ℂ = q u v
  dense_range : IsDenseSet (range j)
end Subsets
section Bounded
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def Commutes (B B' : H →L[ℂ] H) : Prop := B * B' = B' * B
def IsContractive (B : H →L[ℂ] H) : Prop := ∀ ψ, ‖B ψ‖ ≤ ‖ψ‖
def IsPositiveBounded (B : H →L[ℂ] H) : Prop := ∀ ψ, 0 ≤ ⟪ψ, B ψ⟫_ℂ
abbrev UnitaryMap (H H' : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] : Type _ := H ≃ₗᵢ[ℂ] H'
def IsOrthProjOnto (P : H →L[ℂ] H) (M : Set H) : Prop :=
  YangMills.Construction.EuclideanBorel.IsOrthoProjection P ∧ range P = M
end Bounded
section Unbounded
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem unboundedOp_eq_iff (A A' : UnboundedOp H) :
    A = A' ↔ ∃ h : A.domain = A'.domain, ∀ χ : A.domain, A' ⟨χ, h ▸ χ.2⟩ = A χ := by
  constructor
  · rintro rfl
    exact ⟨rfl, fun _ => rfl⟩
  · rintro ⟨h, hv⟩
    exact LinearPMap.ext h fun x hx _ => (hv ⟨x, hx⟩).symm
def IsExtendedBy (A A' : UnboundedOp H) : Prop :=
  ∃ h : A.domain ≤ A'.domain, ∀ χ : A.domain, A' ⟨χ, h χ.2⟩ = A χ
def ker (A : UnboundedOp H) : Set H := {χ | ∃ h : χ ∈ A.domain, A ⟨χ, h⟩ = 0}
def addConst (A : UnboundedOp H) (c : ℂ) : UnboundedOp H :=
  ⟨A.domain, A.toFun + c • A.domain.subtype⟩
def IsDenselyDefined (A : UnboundedOp H) : Prop := IsDenseSet (A.domain : Set H)
def adjDomain (A : UnboundedOp H) : Submodule ℂ H where
  carrier := {φ | ∃ φ' : H, ∀ χ : A.domain, ⟪φ, A χ⟫_ℂ = ⟪φ', (χ : H)⟫_ℂ}
  add_mem' := by
    rintro φ₁ φ₂ ⟨φ₁', h₁⟩ ⟨φ₂', h₂⟩
    exact ⟨φ₁' + φ₂', fun χ => by rw [inner_add_left, inner_add_left, h₁, h₂]⟩
  zero_mem' := ⟨0, fun χ => by simp⟩
  smul_mem' := by
    rintro c φ ⟨φ', h⟩
    exact ⟨c • φ', fun χ => by rw [inner_smul_left, inner_smul_left, h]⟩
theorem adjValue_unique {A : UnboundedOp H} (hA : IsDenselyDefined A) {φ φ₁ φ₂ : H}
    (h₁ : ∀ χ : A.domain, ⟪φ, A χ⟫_ℂ = ⟪φ₁, (χ : H)⟫_ℂ)
    (h₂ : ∀ χ : A.domain, ⟪φ, A χ⟫_ℂ = ⟪φ₂, (χ : H)⟫_ℂ) : φ₁ = φ₂ := by
  have hd : Dense (A.domain : Set H) := (isDenseSet_iff_dense _).mp hA
  have he : (fun x : H => ⟪φ₁ - φ₂, x⟫_ℂ) = fun _ => 0 := by
    refine Continuous.ext_on hd (by fun_prop) continuous_const fun x hx => ?_
    have := (h₁ ⟨x, hx⟩).symm.trans (h₂ ⟨x, hx⟩)
    simp only [inner_sub_left, this, sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp (congrFun he (φ₁ - φ₂)))
def adjValue (A : UnboundedOp H) (φ : adjDomain A) : H :=
  Classical.choose
    (show ∃ φ' : H, ∀ χ : A.domain, ⟪(φ : H), A χ⟫_ℂ = ⟪φ', (χ : H)⟫_ℂ from φ.2)
theorem adjValue_spec (A : UnboundedOp H) (φ : adjDomain A) (χ : A.domain) :
    ⟪(φ : H), A χ⟫_ℂ = ⟪adjValue A φ, (χ : H)⟫_ℂ :=
  Classical.choose_spec
    (show ∃ φ' : H, ∀ χ : A.domain, ⟪(φ : H), A χ⟫_ℂ = ⟪φ', (χ : H)⟫_ℂ from φ.2) χ
def adj (A : UnboundedOp H) (hA : IsDenselyDefined A) : UnboundedOp H where
  domain := adjDomain A
  toFun :=
    { toFun := adjValue A
      map_add' := fun φ₁ φ₂ => by
        refine adjValue_unique hA (adjValue_spec A (φ₁ + φ₂)) fun χ => ?_
        rw [Submodule.coe_add, inner_add_left, inner_add_left, adjValue_spec A φ₁ χ,
          adjValue_spec A φ₂ χ]
      map_smul' := fun c φ => by
        refine adjValue_unique hA (adjValue_spec A (c • φ)) fun χ => ?_
        rw [Submodule.coe_smul, RingHom.id_apply, inner_smul_left, inner_smul_left,
          adjValue_spec A φ χ] }
theorem adj_spec (A : UnboundedOp H) (hA : IsDenselyDefined A) (φ : (adj A hA).domain)
    (χ : A.domain) : ⟪(φ : H), A χ⟫_ℂ = ⟪adj A hA φ, (χ : H)⟫_ℂ :=
  adjValue_spec A φ χ
def IsSelfAdj (A : UnboundedOp H) : Prop :=
  ∃ hA : IsDenselyDefined A, adj A hA = A
def IsNonneg (A : UnboundedOp H) : Prop := ∀ χ : A.domain, 0 ≤ ⟪(χ : H), A χ⟫_ℂ
def ofCLM (B : H →L[ℂ] H) : UnboundedOp H := (B : H →ₗ[ℂ] H).toPMap ⊤
def IsLoewnerGE (B B' : H →L[ℂ] H) : Prop := ∀ ψ, ⟪ψ, B' ψ⟫_ℂ ≤ ⟪ψ, B ψ⟫_ℂ
def unitaryConjugate (U : UnitaryMap H H) (A : UnboundedOp H) : UnboundedOp H :=
  ⟨A.domain.map U.toLinearEquiv.toLinearMap,
    U.toLinearEquiv.toLinearMap ∘ₗ A.toFun ∘ₗ
      (U.toLinearEquiv.submoduleMap A.domain).symm.toLinearMap⟩
theorem unitaryConjugate_apply (U : UnitaryMap H H) (A : UnboundedOp H) (χ : A.domain) :
    unitaryConjugate U A ⟨U χ, Submodule.mem_map_of_mem χ.2⟩ = U (A χ) := by
  have h : (U.toLinearEquiv.submoduleMap A.domain).symm ⟨U χ, Submodule.mem_map_of_mem χ.2⟩ = χ :=
    (LinearEquiv.symm_apply_eq _).2 rfl
  exact congrArg (fun p : A.domain => U (A.toFun p)) h
end Unbounded
section Families
variable {H H' : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
def TendstoStrongly {ι : Type*} (l : Filter ι) (B : ι → H →L[ℂ] H') (B₀ : H →L[ℂ] H') : Prop :=
  ∀ ψ, Tendsto (fun t => ‖B t ψ - B₀ ψ‖) l (𝓝 0)
structure IsC0Semigroup (B : ℝ≥0 → H →L[ℂ] H) : Prop where
  map_zero : B 0 = 1
  map_add : ∀ t t', B t * B t' = B (t + t')
  continuous_apply : ∀ ψ, Continuous fun t => B t ψ
structure IsStronglyContUnitaryRep {n : ℕ}
    (V : Space n → UnitaryMap H H) : Prop where
  map_zero : V 0 = 1
  map_add : ∀ v v', V v * V v' = V (v + v')
  continuous_apply : ∀ ψ, Continuous fun v => V v ψ
structure IsUnitaryRep {W : Type*} [Group W] (U : W → UnitaryMap H H) : Prop where
  map_one : U 1 = 1
  map_mul : ∀ w w', U (w * w') = U w * U w'
end Families
end YangMills.Construction.FormsOperators
