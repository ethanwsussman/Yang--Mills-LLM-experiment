import YangMills.Construction.TorusOrFourSpace.DistanceOpenSetsDerivativesAndTensorsOfSeveralPoints
import YangMills.Construction.TorusOrFourSpace.GluingOfDistributions
import YangMills.Construction.TorusOrFourSpace.PartitionsOfUnityOnCompactSubsetsOfPowers
import YangMills.Construction.TorusOrFourSpace.SmallFactsOnLiftsProductsAndDistributions
import Mathlib
set_option autoImplicit false
open scoped ENNReal NNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind.Tuple.DistribGluing
open PeriodicSpace.TupleFacts
variable {D : Params} {E : Kind} {p : ℕ+}
open Classical in
def extendByZero {A : Set (E.Tuple D p)} (T : testFns D E A → ℂ)
    (G : E.Tuple D p → ℂ) : ℂ :=
  if h : G ∈ testFns D E A then T ⟨G, h⟩ else 0
theorem extendByZero_of_mem {A : Set (E.Tuple D p)} (T : testFns D E A → ℂ)
    {G : E.Tuple D p → ℂ} (h : G ∈ testFns D E A) : _root_.YangMills.Construction.PeriodicSpace.Kind.Tuple.DistribGluing.extendByZero T G = T ⟨G, h⟩ :=
  dif_pos h
section Stable
variable (hstab : TestFnsSubmodule D E p)
  {A : Set (E.Tuple D p)} (hA : IsOpenT D E A)
include hstab hA
theorem add_mem_testFns {F G : E.Tuple D p → ℂ} (hF : F ∈ testFns D E A)
    (hG : G ∈ testFns D E A) : F + G ∈ testFns D E A := by
  obtain ⟨S, hS⟩ := (hstab A hA).1
  rw [← hS] at hF hG ⊢
  exact S.add_mem hF hG
theorem smul_mem_testFns (c : ℂ) {F : E.Tuple D p → ℂ}
    (hF : F ∈ testFns D E A) : c • F ∈ testFns D E A := by
  obtain ⟨S, hS⟩ := (hstab A hA).1
  rw [← hS] at hF ⊢
  exact S.smul_mem c hF
theorem zero_mem_testFns : (0 : E.Tuple D p → ℂ) ∈ testFns D E A := by
  obtain ⟨S, hS⟩ := (hstab A hA).1
  rw [← hS]
  exact S.zero_mem
theorem sum_mem_testFns {ι : Type*} (s : Finset ι) (f : ι → E.Tuple D p → ℂ)
    (hf : ∀ a ∈ s, f a ∈ testFns D E A) : ∑ a ∈ s, f a ∈ testFns D E A := by
  obtain ⟨S, hS⟩ := (hstab A hA).1
  have hf' : ∀ a ∈ s, f a ∈ S := fun a ha => by
    have := hf a ha
    rw [← hS] at this
    exact this
  have := S.sum_mem hf'
  rw [← hS]
  exact this
theorem mul_mem_testFns {θ F : E.Tuple D p → ℂ} (hθ : θ ∈ testFns D E A)
    (hF : IsSmoothT D E F) : θ * F ∈ testFns D E A := by
  rw [mul_comm]
  exact ((hstab A hA).2 θ hθ).2.2.2.1 F hF
theorem smooth_mul_mem_testFns {θ F : E.Tuple D p → ℂ} (hθ : IsSmoothT D E θ)
    (hF : F ∈ testFns D E A) : θ * F ∈ testFns D E A :=
  ((hstab A hA).2 F hF).2.2.2.1 θ hθ
variable {T : testFns D E A → ℂ} (hT : IsComplexLinearForm T)
include hT
theorem extendByZero_add {F G : E.Tuple D p → ℂ} (hF : F ∈ testFns D E A)
    (hG : G ∈ testFns D E A) : _root_.YangMills.Construction.PeriodicSpace.Kind.Tuple.DistribGluing.extendByZero T (F + G) = _root_.YangMills.Construction.PeriodicSpace.Kind.Tuple.DistribGluing.extendByZero T F + _root_.YangMills.Construction.PeriodicSpace.Kind.Tuple.DistribGluing.extendByZero T G := by
  have hFG := add_mem_testFns hstab hA hF hG
  rw [extendByZero_of_mem T hFG, extendByZero_of_mem T hF, extendByZero_of_mem T hG]
  exact hT.1 ⟨F, hF⟩ ⟨G, hG⟩ ⟨F + G, hFG⟩ rfl
theorem extendByZero_smul (c : ℂ) {F : E.Tuple D p → ℂ} (hF : F ∈ testFns D E A) :
    _root_.YangMills.Construction.PeriodicSpace.Kind.Tuple.DistribGluing.extendByZero T (c • F) = c * _root_.YangMills.Construction.PeriodicSpace.Kind.Tuple.DistribGluing.extendByZero T F := by
  have hcF := smul_mem_testFns hstab hA c hF
  rw [extendByZero_of_mem T hcF, extendByZero_of_mem T hF]
  exact hT.2 c ⟨F, hF⟩ ⟨c • F, hcF⟩ rfl
theorem extendByZero_zero : _root_.YangMills.Construction.PeriodicSpace.Kind.Tuple.DistribGluing.extendByZero T 0 = 0 := by
  have h0 := zero_mem_testFns hstab hA
  have := extendByZero_smul hstab hA hT 0 h0
  simpa using this
theorem extendByZero_sum {ι : Type*} (s : Finset ι) (f : ι → E.Tuple D p → ℂ)
    (hf : ∀ a ∈ s, f a ∈ testFns D E A) :
    _root_.YangMills.Construction.PeriodicSpace.Kind.Tuple.DistribGluing.extendByZero T (∑ a ∈ s, f a) = ∑ a ∈ s, _root_.YangMills.Construction.PeriodicSpace.Kind.Tuple.DistribGluing.extendByZero T (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using extendByZero_zero hstab hA hT
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      extendByZero_add hstab hA hT (hf a (Finset.mem_insert_self a s))
        (sum_mem_testFns hstab hA s f fun b hb => hf b (Finset.mem_insert_of_mem hb)),
      ih fun b hb => hf b (Finset.mem_insert_of_mem hb)]
end Stable
theorem mem_supportT_of_ne_zero (hd : ∀ y : E.Tuple D p, tupleDist D E y y = 0)
    {F : E.Tuple D p → ℂ} {y : E.Tuple D p} (h : F y ≠ 0) :
    y ∈ supportT D E F :=
  fun r hr => ⟨y, h, by rw [hd]; exact hr⟩
theorem isCompactT_union {K L : Set (E.Tuple D p)} (hK : IsCompactT D E K)
    (hL : IsCompactT D E L) : IsCompactT D E (K ∪ L) := by
  intro U hU hc
  obtain ⟨U₁, h₁, f₁, c₁⟩ := hK U hU (Set.subset_union_left.trans hc)
  obtain ⟨U₂, h₂, f₂, c₂⟩ := hL U hU (Set.subset_union_right.trans hc)
  refine ⟨U₁ ∪ U₂, Set.union_subset h₁ h₂, f₁.union f₂, Set.union_subset ?_ ?_⟩
  · exact c₁.trans (Set.sUnion_mono Set.subset_union_left)
  · exact c₂.trans (Set.sUnion_mono Set.subset_union_right)
theorem cNorm_mono {ν ν' : ℕ} (h : ν ≤ ν') (F : E.Tuple D p → ℂ) :
    cNorm D E ν F ≤ cNorm D E ν' F := by
  unfold cNorm
  refine iSup_mono fun α => ?_
  exact iSup_le fun hα => le_iSup_of_le (hα.trans h) le_rfl
theorem hasOrderBoundOn_mono {A K : Set (E.Tuple D p)} {T : testFns D E A → ℂ}
    {ν ν' : ℕ} (hs : HasOrderBoundOn T K ν) (h : ν ≤ ν') : HasOrderBoundOn T K ν' := by
  obtain ⟨C, hC⟩ := hs
  exact ⟨C, fun F hF => (hC F hF).trans (mul_le_mul_right (cNorm_mono h F.1) _)⟩
section Gluing
variable {Γ : Type} {O : Γ → Set (E.Tuple D p)}
variable (O) in
structure LocalDecomp (K : Set (E.Tuple D p)) where
  size : ℕ
  index : Fin size → Γ
  θ : Fin size → E.Tuple D p → ℂ
  mem : ∀ a, θ a ∈ testFns D E (O (index a))
  sum_eq_one : ∀ y ∈ K, ∑ a, θ a y = 1
theorem LocalDecomp.eq_sum_mul {K : Set (E.Tuple D p)} (d : LocalDecomp O K)
    {G : E.Tuple D p → ℂ} (hG : ∀ y, G y ≠ 0 → y ∈ K) : G = ∑ a, d.θ a * G := by
  funext y
  rw [Finset.sum_apply]
  simp only [Pi.mul_apply]
  by_cases h : G y = 0
  · simp [h]
  · rw [← Finset.sum_mul, d.sum_eq_one y (hG y h), one_mul]
theorem exists_localDecomp (hpart : PartitionOfUnityExists D E p)
    (hO : ∀ γ, IsOpenT D E (O γ)) {K : Set (E.Tuple D p)} (hK : IsCompactT D E K)
    (hKO : K ⊆ ⋃ γ, O γ) : Nonempty (LocalDecomp O K) := by
  classical
  by_cases hne : K = ∅
  · subst hne
    exact ⟨⟨0, Fin.elim0, Fin.elim0, fun a => a.elim0, fun y hy => hy.elim⟩⟩
  obtain ⟨y₀, hy₀⟩ := Set.nonempty_iff_ne_empty.mpr hne
  obtain ⟨U, hsub, hfin, hcov⟩ := hK (Set.range O) (by rintro _ ⟨γ, rfl⟩; exact hO γ)
    (by rwa [Set.sUnion_range])
  have hpick : ∀ V : U, ∃ γ, O γ = V := fun V => hsub V.2
  choose f hf using hpick
  have := hfin.fintype
  obtain ⟨V₀, hV₀, -⟩ := hcov hy₀
  have hpos : 0 < Fintype.card U := Fintype.card_pos_iff.mpr ⟨⟨V₀, hV₀⟩⟩
  let e : U ≃ Fin (Fintype.card U) := Fintype.equivFin U
  let r : ℕ+ := ⟨Fintype.card U, hpos⟩
  obtain ⟨φ, hφ, -, N, -, hKN, hsum⟩ := hpart r K (fun a => O (f (e.symm a))) hK
    (fun a => hO _) (by
      intro y hy
      obtain ⟨V, hV, hyV⟩ := hcov hy
      refine Set.mem_iUnion.mpr ⟨e ⟨V, hV⟩, ?_⟩
      show y ∈ O (f (e.symm (e ⟨V, hV⟩)))
      rw [e.symm_apply_apply, hf]
      exact hyV)
  exact ⟨⟨r, fun a => f (e.symm a), φ, hφ, fun y hy => hsum y (hKN hy)⟩⟩
def gluedValue (T : ∀ γ, testFns D E (O γ) → ℂ) {K : Set (E.Tuple D p)}
    (d : LocalDecomp O K) (F : E.Tuple D p → ℂ) : ℂ :=
  ∑ a, _root_.YangMills.Construction.PeriodicSpace.Kind.Tuple.DistribGluing.extendByZero (T (d.index a)) (d.θ a * F)
variable {T : ∀ γ, testFns D E (O γ) → ℂ}
theorem gluedValue_indep (hstab : TestFnsSubmodule D E p)
    (hO : ∀ γ, IsOpenT D E (O γ)) (hlin : ∀ γ, IsComplexLinearForm (T γ))
    (hag : ∀ (γ γ' : Γ) (G : E.Tuple D p → ℂ), G ∈ testFns D E (O γ) →
      G ∈ testFns D E (O γ') → _root_.YangMills.Construction.PeriodicSpace.Kind.Tuple.DistribGluing.extendByZero (T γ) G = _root_.YangMills.Construction.PeriodicSpace.Kind.Tuple.DistribGluing.extendByZero (T γ') G)
    {K K' : Set (E.Tuple D p)} (d : LocalDecomp O K) (d' : LocalDecomp O K')
    {F : E.Tuple D p → ℂ} (hF : IsSmoothT D E F) (hK : ∀ y, F y ≠ 0 → y ∈ K)
    (hK' : ∀ y, F y ≠ 0 → y ∈ K') : gluedValue T d F = gluedValue T d' F := by
  have hmem' : ∀ a b, d.θ a * (d'.θ b * F) ∈ testFns D E (O (d'.index b)) := fun a b =>
    smooth_mul_mem_testFns hstab (hO _) (d.mem a).1
      (mul_mem_testFns hstab (hO _) (d'.mem b) hF)
  have hmem : ∀ a b, d.θ a * (d'.θ b * F) ∈ testFns D E (O (d.index a)) := fun a b =>
    mul_mem_testFns hstab (hO _) (d.mem a)
      (mul_mem_testFns hstab (hO _) (d'.mem b) hF).1
  have h1 : ∀ a, _root_.YangMills.Construction.PeriodicSpace.Kind.Tuple.DistribGluing.extendByZero (T (d.index a)) (d.θ a * F) =
      ∑ b, _root_.YangMills.Construction.PeriodicSpace.Kind.Tuple.DistribGluing.extendByZero (T (d.index a)) (d.θ a * (d'.θ b * F)) := by
    intro a
    have e : d.θ a * F = ∑ b, d.θ a * (d'.θ b * F) := by
      rw [← Finset.mul_sum, ← d'.eq_sum_mul hK']
    rw [← extendByZero_sum hstab (hO _) (hlin _) _ _ fun b _ => hmem a b, ← e]
  have h2 : ∀ b, _root_.YangMills.Construction.PeriodicSpace.Kind.Tuple.DistribGluing.extendByZero (T (d'.index b)) (d'.θ b * F) =
      ∑ a, _root_.YangMills.Construction.PeriodicSpace.Kind.Tuple.DistribGluing.extendByZero (T (d'.index b)) (d.θ a * (d'.θ b * F)) := by
    intro b
    have e : d'.θ b * F = ∑ a, d.θ a * (d'.θ b * F) :=
      d.eq_sum_mul fun y hy => hK y (right_ne_zero_of_mul hy)
    rw [← extendByZero_sum hstab (hO _) (hlin _) _ _ fun a _ => hmem' a b, ← e]
  calc gluedValue T d F = ∑ a, ∑ b, _root_.YangMills.Construction.PeriodicSpace.Kind.Tuple.DistribGluing.extendByZero (T (d.index a)) (d.θ a * (d'.θ b * F)) :=
        Finset.sum_congr rfl fun a _ => h1 a
    _ = ∑ a, ∑ b, _root_.YangMills.Construction.PeriodicSpace.Kind.Tuple.DistribGluing.extendByZero (T (d'.index b)) (d.θ a * (d'.θ b * F)) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
          hag _ _ _ (hmem a b) (hmem' a b)
    _ = ∑ b, ∑ a, _root_.YangMills.Construction.PeriodicSpace.Kind.Tuple.DistribGluing.extendByZero (T (d'.index b)) (d.θ a * (d'.θ b * F)) := Finset.sum_comm
    _ = gluedValue T d' F := Finset.sum_congr rfl fun b _ => (h2 b).symm
variable {Ω : Set (E.Tuple D p)}
def IsGluedForm (T : ∀ γ, testFns D E (O γ) → ℂ) (S : testFns D E Ω → ℂ) : Prop :=
  ∀ (K : Set (E.Tuple D p)) (d : LocalDecomp O K) (F : testFns D E Ω),
    (∀ y, F.1 y ≠ 0 → y ∈ K) → S F = gluedValue T d F.1
theorem isComplexLinearForm_of_isGluedForm (hstab : TestFnsSubmodule D E p)
    (hd : ∀ y : E.Tuple D p, tupleDist D E y y = 0)
    (hO : ∀ γ, IsOpenT D E (O γ)) (hlin : ∀ γ, IsComplexLinearForm (T γ))
    (hdec : ∀ K, IsCompactT D E K → K ⊆ Ω → Nonempty (LocalDecomp O K))
    {S : testFns D E Ω → ℂ} (hrep : IsGluedForm T S) : IsComplexLinearForm S := by
  constructor
  · intro F G H hH
    obtain ⟨d⟩ := hdec _ (isCompactT_union F.2.2.1 G.2.2.1)
      (Set.union_subset F.2.2.2 G.2.2.2)
    have hFm : ∀ y, F.1 y ≠ 0 → y ∈ supportT D E F.1 ∪ supportT D E G.1 :=
      fun y hy => Or.inl (mem_supportT_of_ne_zero hd hy)
    have hGm : ∀ y, G.1 y ≠ 0 → y ∈ supportT D E F.1 ∪ supportT D E G.1 :=
      fun y hy => Or.inr (mem_supportT_of_ne_zero hd hy)
    have hHm : ∀ y, H.1 y ≠ 0 → y ∈ supportT D E F.1 ∪ supportT D E G.1 := by
      intro y hy
      by_cases hF0 : F.1 y = 0
      · refine hGm y fun hG0 => hy ?_
        rw [hH, Pi.add_apply, hF0, hG0, add_zero]
      · exact hFm y hF0
    rw [hrep _ d H hHm, hrep _ d F hFm, hrep _ d G hGm, hH]
    unfold gluedValue
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_add]
    exact extendByZero_add hstab (hO _) (hlin _)
      (mul_mem_testFns hstab (hO _) (d.mem a) F.2.1)
      (mul_mem_testFns hstab (hO _) (d.mem a) G.2.1)
  · intro c F H hH
    obtain ⟨d⟩ := hdec _ F.2.2.1 F.2.2.2
    have hFm : ∀ y, F.1 y ≠ 0 → y ∈ supportT D E F.1 :=
      fun y hy => mem_supportT_of_ne_zero hd hy
    have hHm : ∀ y, H.1 y ≠ 0 → y ∈ supportT D E F.1 := by
      intro y hy
      refine hFm y fun hF0 => hy ?_
      rw [hH, Pi.smul_apply, hF0, smul_zero]
    rw [hrep _ d H hHm, hrep _ d F hFm, hH]
    unfold gluedValue
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_smul_comm]
    exact extendByZero_smul hstab (hO _) (hlin _) c
      (mul_mem_testFns hstab (hO _) (d.mem a) F.2.1)
theorem hasOrderBoundOn_of_isGluedForm (hstab : TestFnsSubmodule D E p)
    (hd : ∀ y : E.Tuple D p, tupleDist D E y y = 0)
    (hsupp : SupportAddMul D E p) (hO : ∀ γ, IsOpenT D E (O γ))
    (hΩ : IsOpenT D E Ω) {ν : ℕ} (hleib : LiftsProductsDistributions.LeibnizBound D E p ν)
    {S : testFns D E Ω → ℂ} (hrep : IsGluedForm T S)
    {K : Set (E.Tuple D p)} (d : LocalDecomp O K)
    (hs : ∀ a, HasOrderBoundOn (T (d.index a)) (supportT D E (d.θ a)) ν) :
    HasOrderBoundOn S K ν := by
  choose C hC using hs
  refine ⟨∑ a, C a * 2 ^ ν * (cNorm D E ν (d.θ a)).toNNReal, fun F hFK => ?_⟩
  rw [hrep K d F fun y hy => hFK (mem_supportT_of_ne_zero hd hy)]
  have hfin : ∀ a, cNorm D E ν (d.θ a) < ⊤ := fun a =>
    ((hstab _ (hO _)).2 _ (d.mem a)).2.2.2.2 ν
  have hFfin : cNorm D E ν F.1 < ⊤ := ((hstab _ hΩ).2 _ F.2).2.2.2.2 ν
  have hterm : ∀ a, ENNReal.ofReal ‖_root_.YangMills.Construction.PeriodicSpace.Kind.Tuple.DistribGluing.extendByZero (T (d.index a)) (d.θ a * F.1)‖ ≤
      (C a : ℝ≥0∞) * (2 ^ ν * cNorm D E ν (d.θ a) * cNorm D E ν F.1) := by
    intro a
    have hm := mul_mem_testFns hstab (hO _) (d.mem a) F.2.1
    rw [extendByZero_of_mem _ hm]
    refine (hC a ⟨_, hm⟩ ?_).trans ?_
    · have := (hsupp (d.θ a) F.1 1 1).2
      exact this.trans Set.inter_subset_left
    · gcongr
      exact hleib _ _ ((d.mem a).1 ν) (F.2.1 ν) (hfin a) hFfin
  calc ENNReal.ofReal ‖gluedValue T d F.1‖
      ≤ ∑ a, ENNReal.ofReal ‖_root_.YangMills.Construction.PeriodicSpace.Kind.Tuple.DistribGluing.extendByZero (T (d.index a)) (d.θ a * F.1)‖ :=
        (ENNReal.ofReal_le_ofReal (norm_sum_le _ _)).trans
          (ENNReal.ofReal_sum_of_nonneg fun _ _ => norm_nonneg _).le
    _ ≤ ∑ a, (C a : ℝ≥0∞) * (2 ^ ν * cNorm D E ν (d.θ a) * cNorm D E ν F.1) :=
        Finset.sum_le_sum fun a _ => hterm a
    _ = ((∑ a, C a * 2 ^ ν * (cNorm D E ν (d.θ a)).toNNReal : ℝ≥0) : ℝ≥0∞) *
          cNorm D E ν F.1 := by
        push_cast
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [ENNReal.coe_toNNReal (hfin a).ne]
        ring
theorem isGluedForm_of_restrictions (hstab : TestFnsSubmodule D E p)
    (hO : ∀ γ, IsOpenT D E (O γ)) (hΩ : IsOpenT D E Ω) (hsub : ∀ γ, O γ ⊆ Ω)
    {S : testFns D E Ω → ℂ} (hS : IsComplexLinearForm S)
    (hres : ∀ γ, restrictDistrib (hsub γ) S = T γ) : IsGluedForm T S := by
  intro K d F hK
  have hm : ∀ a, d.θ a * F.1 ∈ testFns D E (O (d.index a)) := fun a =>
    mul_mem_testFns hstab (hO _) (d.mem a) F.2.1
  have hmΩ : ∀ a, d.θ a * F.1 ∈ testFns D E Ω := fun a =>
    ⟨(hm a).1, (hm a).2.1, (hm a).2.2.trans (hsub _)⟩
  have key : ∀ a, _root_.YangMills.Construction.PeriodicSpace.Kind.Tuple.DistribGluing.extendByZero (T (d.index a)) (d.θ a * F.1) = _root_.YangMills.Construction.PeriodicSpace.Kind.Tuple.DistribGluing.extendByZero S (d.θ a * F.1) := by
    intro a
    rw [extendByZero_of_mem _ (hm a), extendByZero_of_mem _ (hmΩ a), ← hres (d.index a)]
    rfl
  have hsum : _root_.YangMills.Construction.PeriodicSpace.Kind.Tuple.DistribGluing.extendByZero S F.1 = ∑ a, _root_.YangMills.Construction.PeriodicSpace.Kind.Tuple.DistribGluing.extendByZero S (d.θ a * F.1) := by
    rw [← extendByZero_sum hstab hΩ hS _ _ fun a _ => hmΩ a, ← d.eq_sum_mul hK]
  unfold gluedValue
  rw [Finset.sum_congr rfl fun a _ => key a, ← hsum, extendByZero_of_mem _ F.2]
theorem eq_of_isGluedForm (hdec : ∀ K, IsCompactT D E K → K ⊆ Ω → Nonempty (LocalDecomp O K))
    (hd : ∀ y : E.Tuple D p, tupleDist D E y y = 0)
    {S S' : testFns D E Ω → ℂ} (hS : IsGluedForm T S) (hS' : IsGluedForm T S') : S = S' := by
  funext F
  obtain ⟨d⟩ := hdec _ F.2.2.1 F.2.2.2
  have hFm : ∀ y, F.1 y ≠ 0 → y ∈ supportT D E F.1 :=
    fun y hy => mem_supportT_of_ne_zero hd hy
  rw [hS _ d F hFm, hS' _ d F hFm]
end Gluing
theorem statement_holds (hpartitions : PartitionsOfUnity.Statement)
    (hfacts : LiftsProductsDistributions.Statement)
    (hpoints : TupleFacts.AllFacts) :
    Statement := by
  intro D E p ν₀ Γ Ω O hΩ hΩo hO T hT hag
  obtain ⟨_, _, hmet, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsupp, _, hstab, _⟩ :=
    hpoints D E p
  obtain ⟨_, _, hleib, _, _, _, _⟩ := hfacts D E
  have hd : ∀ y : E.Tuple D p, tupleDist D E y y = 0 := fun y => (hmet.2.1 y y).mpr rfl
  have hsub : ∀ γ, O γ ⊆ Ω := fun γ => (Set.subset_iUnion O γ).trans hΩ.subset
  have hlin : ∀ γ, IsComplexLinearForm (T γ) := fun γ => (hT γ).1
  have hdec : ∀ K, IsCompactT D E K → K ⊆ Ω → Nonempty (LocalDecomp O K) := fun K hK hKΩ =>
    exists_localDecomp (hpartitions D E p).1 hO hK (hKΩ.trans hΩ.superset)
  have hag' : ∀ (γ γ' : Γ) (G : E.Tuple D p → ℂ), G ∈ testFns D E (O γ) →
      G ∈ testFns D E (O γ') → _root_.YangMills.Construction.PeriodicSpace.Kind.Tuple.DistribGluing.extendByZero (T γ) G = _root_.YangMills.Construction.PeriodicSpace.Kind.Tuple.DistribGluing.extendByZero (T γ') G := by
    intro γ γ' G h h'
    have h'' : G ∈ testFns D E (O γ ∩ O γ') := ⟨h.1, h.2.1, Set.subset_inter h.2.2 h'.2.2⟩
    rw [extendByZero_of_mem _ h, extendByZero_of_mem _ h']
    exact hag γ γ' ⟨G, h''⟩
  have hdecF : ∀ F : testFns D E Ω, Nonempty (LocalDecomp O (supportT D E F.1)) :=
    fun F => hdec _ F.2.2.1 F.2.2.2
  let S : testFns D E Ω → ℂ := fun F => gluedValue T (Classical.choice (hdecF F)) F.1
  have hrep : IsGluedForm T S := fun K d F hK =>
    gluedValue_indep hstab hO hlin hag' _ d F.2.1 (fun y hy => mem_supportT_of_ne_zero hd hy) hK
  have hSlin : IsComplexLinearForm S :=
    isComplexLinearForm_of_isGluedForm hstab hd hO hlin hdec hrep
  have hSdist : IsDistrib S := by
    refine ⟨hSlin, fun K hK hKΩ => ?_⟩
    obtain ⟨d⟩ := hdec K hK hKΩ
    have hex : ∀ a, ∃ ν, HasOrderBoundOn (T (d.index a)) (supportT D E (d.θ a)) ν :=
      fun a => (hT _).2 _ (d.mem a).2.1 (d.mem a).2.2
    choose νf hν using hex
    exact ⟨Finset.univ.sup νf, hasOrderBoundOn_of_isGluedForm hstab hd hsupp hO hΩo (hleib p _) hrep d
      fun a => hasOrderBoundOn_mono (hν a) (Finset.le_sup (Finset.mem_univ a))⟩
  have hSres : ∀ γ, restrictDistrib (hsub γ) S = T γ := by
    intro γ
    funext F
    obtain ⟨d⟩ := hdec _ F.2.2.1 (F.2.2.2.trans (hsub γ))
    have hFm : ∀ y, F.1 y ≠ 0 → y ∈ supportT D E F.1 :=
      fun y hy => mem_supportT_of_ne_zero hd hy
    have hm : ∀ a, d.θ a * F.1 ∈ testFns D E (O γ) := fun a =>
      smooth_mul_mem_testFns hstab (hO _) (d.mem a).1 F.2
    have key : ∀ a, _root_.YangMills.Construction.PeriodicSpace.Kind.Tuple.DistribGluing.extendByZero (T (d.index a)) (d.θ a * F.1) = _root_.YangMills.Construction.PeriodicSpace.Kind.Tuple.DistribGluing.extendByZero (T γ) (d.θ a * F.1) :=
      fun a => hag' _ _ _ (mul_mem_testFns hstab (hO _) (d.mem a) F.2.1) (hm a)
    have hsum : _root_.YangMills.Construction.PeriodicSpace.Kind.Tuple.DistribGluing.extendByZero (T γ) F.1 = ∑ a, _root_.YangMills.Construction.PeriodicSpace.Kind.Tuple.DistribGluing.extendByZero (T γ) (d.θ a * F.1) := by
      rw [← extendByZero_sum hstab (hO γ) (hlin γ) _ _ fun a _ => hm a, ← d.eq_sum_mul hFm]
    show S ⟨F.1, F.2.1, F.2.2.1, F.2.2.2.trans (hsub γ)⟩ = T γ F
    rw [hrep _ d _ hFm]
    unfold gluedValue
    rw [Finset.sum_congr rfl fun a _ => key a, ← hsum, extendByZero_of_mem _ F.2]
  refine ⟨⟨S, ⟨hSdist, hSres⟩, fun S' hS' => ?_⟩, fun hord S' hS' hres' => ?_⟩
  · exact eq_of_isGluedForm hdec hd
      (isGluedForm_of_restrictions hstab hO hΩo hsub hS'.1.1 hS'.2) hrep
  · have hrep' := isGluedForm_of_restrictions hstab hO hΩo hsub hS'.1 hres'
    refine ⟨hS', fun K hK hKΩ => ?_⟩
    obtain ⟨d⟩ := hdec K hK hKΩ
    exact hasOrderBoundOn_of_isGluedForm hstab hd hsupp hO hΩo (hleib p ν₀) hrep' d
      fun a => (hord _).2 _ (d.mem a).2.1 (d.mem a).2.2
end YangMills.Construction.PeriodicSpace.Kind.Tuple.DistribGluing
