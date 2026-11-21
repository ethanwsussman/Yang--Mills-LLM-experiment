import YangMills.Construction.RunningCouplingSlope.NormsOfThePlainProductsProof
import YangMills.Construction.Towers.TransposesBetweenFormsOfTheWholeLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.EdgeFormTransposesProof
open YangMills.Construction.Tower.LeftChartFields YangMills.Construction.Tower.PairedFunctionSpace
open YangMills.Construction.Matrices
structure PairedTransport (S A : PairedFunctionSpace) where
  equiv : S.complexSubmodule ≃ₗ[ℂ] A.complexSubmodule
  realSubmodule_le : ∀ f : S.index → ComplexMatrix2, f ∈ S.realSubmodule → f ∈ S.complexSubmodule
  realSubmodule_le' : ∀ f : A.index → ComplexMatrix2, f ∈ A.realSubmodule → f ∈ A.complexSubmodule
  mem_real_iff : ∀ f : S.complexSubmodule,
    (f : S.index → ComplexMatrix2) ∈ S.realSubmodule ↔
      (equiv f : A.index → ComplexMatrix2) ∈ A.realSubmodule
  pair_equiv : ∀ f g : S.complexSubmodule, A.pair (equiv f) (equiv g) = S.pair f g
  finite_equiv : ∀ f : S.complexSubmodule,
    A.IsFinitelySupported (equiv f) ↔ S.IsFinitelySupported f
namespace PairedTransport
variable {S S' A A' : PairedFunctionSpace}
def symm (e : PairedTransport S A) : PairedTransport A S where
  equiv := e.equiv.symm
  realSubmodule_le := e.realSubmodule_le'
  realSubmodule_le' := e.realSubmodule_le
  mem_real_iff f := by simpa using (e.mem_real_iff (e.equiv.symm f)).symm
  pair_equiv f g := by simpa using (e.pair_equiv (e.equiv.symm f) (e.equiv.symm g)).symm
  finite_equiv f := by simpa using (e.finite_equiv (e.equiv.symm f)).symm
def conjugate (e : PairedTransport S A) (e' : PairedTransport S' A')
    (T : S.complexSubmodule →ₗ[ℂ] S'.complexSubmodule) :
    A.complexSubmodule →ₗ[ℂ] A'.complexSubmodule :=
  e'.equiv.toLinearMap ∘ₗ T ∘ₗ e.equiv.symm.toLinearMap
theorem conjugate_apply (e : PairedTransport S A) (e' : PairedTransport S' A')
    (T : S.complexSubmodule →ₗ[ℂ] S'.complexSubmodule) (f : A.complexSubmodule) :
    conjugate e e' T f = e'.equiv (T (e.equiv.symm f)) := rfl
theorem symm_equiv_apply (e : PairedTransport S A) (f : A.complexSubmodule) :
    e.symm.equiv f = e.equiv.symm f := rfl
theorem symm_equiv_symm_apply (e : PairedTransport S A) (f : S.complexSubmodule) :
    e.symm.equiv.symm f = e.equiv f := rfl
theorem conjugate_preserves (e : PairedTransport S A) (e' : PairedTransport S' A')
    {T : S.complexSubmodule →ₗ[ℂ] S'.complexSubmodule} (h : PreservesFiniteSupport T) :
    PreservesFiniteSupport (conjugate e e' T) := fun f hf =>
  (e'.finite_equiv _).2 (h _ ((e.finite_equiv (e.equiv.symm f)).1 (by simpa using hf)))
theorem conjugate_isTransposeMap (e : PairedTransport S A) (e' : PairedTransport S' A')
    {T : S.complexSubmodule →ₗ[ℂ] S'.complexSubmodule}
    {T' : S'.complexSubmodule →ₗ[ℂ] S.complexSubmodule} (h : IsTransposeMap T T') :
    IsTransposeMap (conjugate e e' T) (conjugate e' e T') := by
  intro g f hf
  have hf' : S.IsFinitelySupported (e.equiv.symm f) := (e.finite_equiv _).1 (by simpa using hf)
  have h₀ := h (e'.equiv.symm g) (e.equiv.symm f) hf'
  have h₁ := e.pair_equiv (T' (e'.equiv.symm g)) (e.equiv.symm f)
  have h₂ := e'.pair_equiv (e'.equiv.symm g) (T (e.equiv.symm f))
  rw [LinearEquiv.apply_symm_apply] at h₁ h₂
  rw [conjugate_apply, conjugate_apply, h₁, h₀, ← h₂]
theorem conjugate_conjugate (e : PairedTransport S A) (e' : PairedTransport S' A')
    (T : S.complexSubmodule →ₗ[ℂ] S'.complexSubmodule) :
    conjugate e.symm e'.symm (conjugate e e' T) = T := by
  refine LinearMap.ext fun f => ?_
  rw [conjugate_apply, conjugate_apply, symm_equiv_apply, symm_equiv_symm_apply]
  simp
theorem hasUniqueTranspose (e : PairedTransport S A) (e' : PairedTransport S' A')
    (h : HasUniqueTranspose A A') : HasUniqueTranspose S S' := by
  intro T hT
  obtain ⟨T', hT', hu⟩ := h (conjugate e e' T) (conjugate_preserves e e' hT)
  refine ⟨conjugate e'.symm e.symm T', ?_, ?_⟩
  · have h₁ := conjugate_isTransposeMap e.symm e'.symm hT'
    rwa [conjugate_conjugate] at h₁
  · intro R hR
    have h₁ : (fun x => e.equiv (R (e'.equiv.symm x))) = T' := by
      refine hu _ fun x f hf => ?_
      have hf' : S.IsFinitelySupported (e.equiv.symm f) := (e.finite_equiv _).1 (by simpa using hf)
      have h₀ := hR (e'.equiv.symm x) (e.equiv.symm f) hf'
      have h₂ := e.pair_equiv (R (e'.equiv.symm x)) (e.equiv.symm f)
      have h₃ := e'.pair_equiv (e'.equiv.symm x) (T (e.equiv.symm f))
      rw [LinearEquiv.apply_symm_apply] at h₂ h₃
      rw [h₂, h₀, ← h₃, conjugate_apply]
    funext g
    have h₂ := congrFun h₁ (e'.equiv g)
    simp only [LinearEquiv.symm_apply_apply] at h₂
    rw [conjugate_apply, symm_equiv_apply, symm_equiv_symm_apply, ← h₂]
    simp
def ofReal (e : PairedTransport S A) (f : S.realSubmodule) : S.complexSubmodule :=
  ⟨f, e.realSubmodule_le _ f.2⟩
theorem mem_traceless_of_mem_hermitianTraceless {X : ComplexMatrix2}
    (h : X ∈ ComplexMatrix2.hermitianTraceless) : X ∈ ComplexMatrix2.traceless := h.2
theorem real_smul_eq_complex_smul {ι : Type} (c : ℝ) (x : ι → ComplexMatrix2) :
    c • x = (c : ℂ) • x := by apply _root_.YangMills.SharedProofs.p7664 <;> assumption
def realMap (e : PairedTransport S A) : S.realSubmodule →ₗ[ℝ] A.realSubmodule where
  toFun f := ⟨e.equiv (e.ofReal f), (e.mem_real_iff _).1 f.2⟩
  map_add' f g := by
    have h : e.ofReal (f + g) = e.ofReal f + e.ofReal g := rfl
    apply Subtype.ext
    change ((e.equiv (e.ofReal (f + g)) : A.complexSubmodule) : A.index → ComplexMatrix2) = _
    rw [h, map_add]
    rfl
  map_smul' c f := by
    have h : e.ofReal (c • f) = (c : ℂ) • e.ofReal f :=
      Subtype.ext (real_smul_eq_complex_smul c (f : S.index → ComplexMatrix2))
    apply Subtype.ext
    change ((e.equiv (e.ofReal (c • f)) : A.complexSubmodule) : A.index → ComplexMatrix2) = _
    rw [h, map_smul]
    exact (real_smul_eq_complex_smul c _).symm
theorem ofReal_realMap (e : PairedTransport S A) (f : S.realSubmodule) :
    e.symm.ofReal (e.realMap f) = e.equiv (e.ofReal f) := rfl
theorem ofReal_symm_realMap (e : PairedTransport S A) (f : A.realSubmodule) :
    e.ofReal (e.symm.realMap f) = e.equiv.symm (e.symm.ofReal f) := rfl
theorem symm_realMap_realMap (e : PairedTransport S A) (f : S.realSubmodule) :
    e.symm.realMap (e.realMap f) = f := by
  apply Subtype.ext
  change ((e.equiv.symm (e.symm.ofReal (e.realMap f)) : S.complexSubmodule) :
    S.index → ComplexMatrix2) = f
  rw [ofReal_realMap, LinearEquiv.symm_apply_apply]
  rfl
theorem realMap_symm_realMap (e : PairedTransport S A) (f : A.realSubmodule) :
    e.realMap (e.symm.realMap f) = f := by
  apply Subtype.ext
  change ((e.equiv (e.ofReal (e.symm.realMap f)) : A.complexSubmodule) :
    A.index → ComplexMatrix2) = f
  rw [ofReal_symm_realMap, LinearEquiv.apply_symm_apply]
  rfl
theorem pair_realMap (e : PairedTransport S A) (f g : S.realSubmodule) :
    A.pair (e.realMap f) (e.realMap g) = S.pair f g := e.pair_equiv (e.ofReal f) (e.ofReal g)
theorem isFinitelySupported_realMap (e : PairedTransport S A) (f : S.realSubmodule) :
    A.IsFinitelySupported (e.realMap f) ↔ S.IsFinitelySupported f := e.finite_equiv (e.ofReal f)
theorem eq_ofReal_add_I_smul (e : PairedTransport S A) {f f' : S.realSubmodule}
    {h : S.complexSubmodule}
    (hh : (h : S.index → ComplexMatrix2) = f + Complex.I • (f' : S.index → ComplexMatrix2)) :
    h = e.ofReal f + Complex.I • e.ofReal f' := Subtype.ext hh
theorem hasRealDecomposition (e : PairedTransport S A) (h : A.HasRealDecomposition) :
    S.HasRealDecomposition := by
  intro f
  obtain ⟨⟨q₁, q₂⟩, hq, hu⟩ := h (e.equiv f)
  have hf : e.equiv f = e.symm.ofReal q₁ + Complex.I • e.symm.ofReal q₂ :=
    e.symm.eq_ofReal_add_I_smul hq
  refine ⟨(e.symm.realMap q₁, e.symm.realMap q₂), ?_, ?_⟩
  · have h₁ : f = e.ofReal (e.symm.realMap q₁) + Complex.I • e.ofReal (e.symm.realMap q₂) := by
      apply e.equiv.injective
      rw [hf, map_add, map_smul, ofReal_symm_realMap, ofReal_symm_realMap]
      simp
    exact congrArg Subtype.val h₁
  · rintro ⟨p₁, p₂⟩ hp
    have hp' : f = e.ofReal p₁ + Complex.I • e.ofReal p₂ := e.eq_ofReal_add_I_smul hp
    have h₁ := hu (e.realMap p₁, e.realMap p₂) (by
      have h₂ : e.equiv f =
          e.symm.ofReal (e.realMap p₁) + Complex.I • e.symm.ofReal (e.realMap p₂) := by
        rw [ofReal_realMap, ofReal_realMap, hp', map_add, map_smul]
      exact congrArg Subtype.val h₂)
    have h₂ : e.realMap p₁ = q₁ := congrArg Prod.fst h₁
    have h₃ : e.realMap p₂ = q₂ := congrArg Prod.snd h₁
    rw [← h₂, ← h₃, symm_realMap_realMap, symm_realMap_realMap]
theorem isComplexification_conjugate (e : PairedTransport S A) (e' : PairedTransport S' A')
    {T₀ : S.realSubmodule →ₗ[ℝ] S'.realSubmodule} {A₀ : A.realSubmodule →ₗ[ℝ] A'.realSubmodule}
    (ha : ∀ x, A₀ (e.realMap x) = e'.realMap (T₀ x))
    {TA : A.complexSubmodule →ₗ[ℂ] A'.complexSubmodule}
    (hc : IsComplexification A₀ TA) : IsComplexification T₀ (conjugate e.symm e'.symm TA) := by
  intro f f' h hh
  have hh' := e.eq_ofReal_add_I_smul hh
  have he : e.equiv h = e.symm.ofReal (e.realMap f) + Complex.I • e.symm.ofReal (e.realMap f') := by
    rw [ofReal_realMap, ofReal_realMap, hh', map_add, map_smul]
  have h₁ := hc (e.realMap f) (e.realMap f') (e.equiv h) (congrArg Subtype.val he)
  rw [ha, ha] at h₁
  have h₂ : TA (e.equiv h) = e'.equiv (e'.ofReal (T₀ f) + Complex.I • e'.ofReal (T₀ f')) := by
    rw [map_add, map_smul, ← ofReal_realMap, ← ofReal_realMap]
    exact e'.symm.eq_ofReal_add_I_smul h₁
  have h₃ : conjugate e.symm e'.symm TA h = e'.ofReal (T₀ f) + Complex.I • e'.ofReal (T₀ f') := by
    rw [conjugate_apply, symm_equiv_apply, symm_equiv_symm_apply, h₂]
    simp
  exact congrArg Subtype.val h₃
theorem admitsRealTransposes (e : PairedTransport S A) (e' : PairedTransport S' A')
    (h₀ : HasUniqueTranspose A A') (h : AdmitsRealTransposes A A') :
    AdmitsRealTransposes S S' := by
  have hsplit := e.hasRealDecomposition h.1
  refine ⟨hsplit, fun T₀ hT₀ => ?_⟩
  have ha : ∀ x, (e'.realMap ∘ₗ T₀ ∘ₗ e.symm.realMap) (e.realMap x) = e'.realMap (T₀ x) :=
    fun x => by
      simp only [LinearMap.comp_apply, symm_realMap_realMap]
  obtain ⟨c₁, c₂, c₃, c₄, c₅, c₆⟩ := h.2 (e'.realMap ∘ₗ T₀ ∘ₗ e.symm.realMap) (fun f hf =>
    (e'.isFinitelySupported_realMap _).2 (hT₀ _ ((e.symm.isFinitelySupported_realMap f).2 hf)))
  generalize hA₀ : e'.realMap ∘ₗ T₀ ∘ₗ e.symm.realMap = A₀ at ha c₁ c₂ c₃ c₄ c₅ c₆
  have hAr : ∀ x, A₀ x = e'.realMap (T₀ (e.symm.realMap x)) := fun x => by
    rw [← hA₀]
    rfl
  have hC := isComplexification_conjugate e e' ha c₁
  have hcont : complexification T₀ = conjugate e.symm e'.symm (complexification A₀) := by
    have hs : IsComplexification T₀ (complexification T₀) := Classical.epsilon_spec ⟨_, hC⟩
    refine LinearMap.ext fun f => ?_
    obtain ⟨⟨p₁, p₂⟩, hp, -⟩ := hsplit f
    exact Subtype.ext ((hs p₁ p₂ f hp).trans (hC p₁ p₂ f hp).symm)
  have hCc : PreservesFiniteSupport (conjugate e.symm e'.symm (complexification A₀)) :=
    conjugate_preserves e.symm e'.symm c₂
  have hT : IsTransposeMap (complexification A₀) (transposeMap (complexification A₀)) := by
    obtain ⟨T', hT', -⟩ := h₀ _ c₂
    exact Classical.epsilon_spec ⟨T', hT'⟩
  have hD := conjugate_isTransposeMap e.symm e'.symm hT
  have htr : transposeMap (conjugate e.symm e'.symm (complexification A₀)) =
      conjugate e'.symm e.symm (transposeMap (complexification A₀)) := by
    obtain ⟨T', hT', hu⟩ := hasUniqueTranspose e e' h₀ _ hCc
    have hs : IsTransposeMap (conjugate e.symm e'.symm (complexification A₀))
        (transposeMap (conjugate e.symm e'.symm (complexification A₀))) :=
      Classical.epsilon_spec ⟨T', hT'⟩
    exact DFunLike.coe_injective ((hu _ hs).trans (hu _ hD).symm)
  have hval : ∀ g : S'.realSubmodule,
      conjugate e'.symm e.symm (transposeMap (complexification A₀)) (e'.ofReal g) =
        e.ofReal (e.symm.realMap (realTransposeMap A₀ (e'.realMap g))) := by
    intro g
    have h₁ := c₄ (e'.realMap g) (e'.equiv (e'.ofReal g)) rfl
    have h₂ : transposeMap (complexification A₀) (e'.equiv (e'.ofReal g)) =
        e.symm.ofReal (realTransposeMap A₀ (e'.realMap g)) := Subtype.ext h₁.symm
    rw [conjugate_apply, symm_equiv_apply, symm_equiv_symm_apply, h₂, ofReal_symm_realMap]
  have hQ : IsRealTransposeMap T₀ (e.symm.realMap ∘ₗ realTransposeMap A₀ ∘ₗ e'.realMap) := by
    intro g k hk
    have hk' : k = e'.ofReal g := Subtype.ext hk
    rw [hcont, htr, hk', hval]
    rfl
  have hrt : realTransposeMap T₀ = e.symm.realMap ∘ₗ realTransposeMap A₀ ∘ₗ e'.realMap := by
    have hs : IsRealTransposeMap T₀ (realTransposeMap T₀) := Classical.epsilon_spec ⟨_, hQ⟩
    exact LinearMap.ext fun g =>
      Subtype.ext ((hs g (e'.ofReal g) rfl).trans (hQ g (e'.ofReal g) rfl).symm)
  have hpair : ∀ (g : S'.realSubmodule) (f : S.realSubmodule), S.IsFinitelySupported f →
      S.pair (e.symm.realMap (realTransposeMap A₀ (e'.realMap g))) f = S'.pair g (T₀ f) := by
    intro g f hf
    have h₁ := c₅ (e'.realMap g) (e.realMap f) ((e.isFinitelySupported_realMap f).2 hf)
    rw [ha, e'.pair_realMap] at h₁
    rw [← h₁, ← e.pair_realMap, realMap_symm_realMap]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcont]
    exact hC
  · rw [hcont]
    exact hCc
  · intro g
    refine ⟨e'.ofReal g, rfl, ?_⟩
    rw [hcont, htr, hval]
    exact (e.symm.realMap _).2
  · exact Classical.epsilon_spec ⟨_, hQ⟩
  · intro g f hf
    rw [hrt]
    exact hpair g f hf
  · intro R hR
    have h₁ : (fun x => e.realMap (R (e'.symm.realMap x))) = realTransposeMap A₀ := by
      refine c₆ _ fun x f hf => ?_
      have h₂ := hR (e'.symm.realMap x) (e.symm.realMap f)
        ((e.symm.isFinitelySupported_realMap f).2 hf)
      have h₃ := e.pair_realMap (R (e'.symm.realMap x)) (e.symm.realMap f)
      have h₄ := e'.pair_realMap (e'.symm.realMap x) (T₀ (e.symm.realMap f))
      rw [realMap_symm_realMap] at h₃ h₄
      rw [hAr, h₃, h₂, ← h₄]
    rw [hrt]
    funext g
    have h₂ := congrFun h₁ (e'.realMap g)
    simp only [symm_realMap_realMap] at h₂
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← h₂, symm_realMap_realMap]
end PairedTransport
section Forms
variable {a : ℝ}
theorem opposite_isPositivelyOriented_of_not {b : InfiniteLattice.Link a}
    (h : ¬b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodSublattice.isPositivelyOriented_opposite_of_not <;> assumption
theorem not_isPositivelyOriented_opposite (ha : 0 < a) {b : InfiniteLattice.Link a}
    (h : b.IsPositivelyOriented) : ¬b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.Link.opposite_not_isPositivelyOriented <;> assumption
abbrev PositiveEdgeSet (a : ℝ) : Type := (Set.univ : Set (FullSpace.PositiveEdge a))
def extendByZero (f : PositiveEdgeSet a → ComplexMatrix2) :
    InfiniteLattice.Link a → ComplexMatrix2 :=
  open Classical in fun b => if h : b.IsPositivelyOriented then f ⟨⟨b, h⟩, trivial⟩ else 0
def restrictToPositive (a : ℝ) :
    (FullSpace.edgePairedSpace a).complexSubmodule →ₗ[ℂ]
      (pairedFunctions (PositiveEdgeSet a)).complexSubmodule where
  toFun B := ⟨fun b => B.1 b.1.1,
    fun b _ => B.2.1 b.1.1 b.1.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem restrictToPositive_bijective (ha : 0 < a) : Function.Bijective (restrictToPositive a) := by
  constructor
  · intro B B' h
    have hp : ∀ b : InfiniteLattice.Link a, b.IsPositivelyOriented →
        B.1 b = B'.1 b :=
      fun b hb => congrFun (congrArg Subtype.val h) ⟨⟨b, hb⟩, trivial⟩
    refine Subtype.ext (funext fun b => ?_)
    by_cases hb : b.IsPositivelyOriented
    · exact hp b hb
    · have h₁ := hp _ (opposite_isPositivelyOriented_of_not hb)
      have r : B.1 b.opposite = -B.1 b := B.2.2 b
      have r' : B'.1 b.opposite = -B'.1 b := B'.2.2 b
      rw [r, r'] at h₁
      exact neg_injective h₁
  · intro f
    have hpos : ∀ b : InfiniteLattice.Link a, ∀ hb : b.IsPositivelyOriented,
        FullSpace.extendOddly (extendByZero f.1) b = f.1 ⟨⟨b, hb⟩, trivial⟩ := by
      intro b hb
      simp [FullSpace.extendOddly, extendByZero, hb]
    have hneg : ∀ b : InfiniteLattice.Link a, ¬b.IsPositivelyOriented →
        FullSpace.extendOddly (extendByZero f.1) b = -extendByZero f.1 b.opposite := by
      intro b hb
      simp [FullSpace.extendOddly, hb]
    have hext : ∀ b : InfiniteLattice.Link a, ∀ hb : b.IsPositivelyOriented,
        extendByZero f.1 b = f.1 ⟨⟨b, hb⟩, trivial⟩ := by
      intro b hb
      simp [extendByZero, hb]
    have hmem : FullSpace.extendOddly (extendByZero f.1) ∈ FullSpace.complexEdgeForms a := by
      refine ⟨fun b hb => ?_, fun b => ?_⟩
      · rw [hpos b hb]
        exact f.2 _ trivial
      · by_cases hb : b.IsPositivelyOriented
        · rw [hneg _ (not_isPositivelyOriented_opposite ha hb),
            InfiniteLattice.Link.opposite_opposite, hpos b hb, hext b hb]
        · have hr := opposite_isPositivelyOriented_of_not hb
          rw [hneg b hb, hpos _ hr, hext _ hr, neg_neg]
    refine ⟨⟨_, hmem⟩, Subtype.ext (funext fun b => ?_)⟩
    exact hpos b.1.1 b.1.2
theorem hasFiniteSupp_comp_equiv {α β : Type} (e : α ≃ β) (h : β → ComplexMatrix2) :
    HasFiniteSupp (h ∘ e) ↔ HasFiniteSupp h := by
  unfold HasFiniteSupp
  rw [Function.support_comp_eq_preimage]
  constructor
  · intro hs
    refine (hs.image e).subset fun x hx => ⟨e.symm x, ?_, by simp⟩
    simpa using hx
  · intro hs
    exact hs.preimage e.injective.injOn
def positiveTransport (ha : 0 < a) :
    PairedTransport (FullSpace.edgePairedSpace a) (pairedFunctions (PositiveEdgeSet a)) where
  equiv := LinearEquiv.ofBijective (restrictToPositive a) (restrictToPositive_bijective ha)
  realSubmodule_le B h :=
    ⟨fun b hb => PairedTransport.mem_traceless_of_mem_hermitianTraceless (h.1 b hb), h.2⟩
  realSubmodule_le' f h := fun b _ =>
    PairedTransport.mem_traceless_of_mem_hermitianTraceless (h b trivial)
  mem_real_iff B := by
    constructor
    · intro h b _
      exact h.1 b.1.1 b.1.2
    · intro h
      exact ⟨fun b hb => h ⟨⟨b, hb⟩, trivial⟩ trivial, B.2.2⟩
  pair_equiv f g :=
    finsum_comp_equiv (Equiv.Set.univ (FullSpace.PositiveEdge a))
      (f := fun b => ComplexMatrix2.halfTrace (f.1 b.1 * g.1 b.1))
  finite_equiv f :=
    hasFiniteSupp_comp_equiv (Equiv.Set.univ (FullSpace.PositiveEdge a)) (fun b => f.1 b.1)
end Forms
theorem meshAt_pos {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ) :
    0 < meshAt L k j := by apply _root_.YangMills.Construction.Tower.BlockPathContourPivotProof.Periodic.meshAt_pos <;> assumption
theorem edgeFormTransposes_holds (h₁ : LeftChartFields.Claim) (h₂ : RealTransposesExist) :
    FullSpace.EdgeFormTransposes := by
  intro L k i j hL hi hj
  have hT : HasUniqueTranspose (pairedFunctions (PositiveEdgeSet (meshAt L k i)))
      (pairedFunctions (PositiveEdgeSet (meshAt L k j))) :=
    (h₁.2.2 L k i hL hi).2.2 (.edges i hi Set.univ) (.edges j hj Set.univ)
  have hR : AdmitsRealTransposes (pairedFunctions (PositiveEdgeSet (meshAt L k i)))
      (pairedFunctions (PositiveEdgeSet (meshAt L k j))) :=
    (h₂ L k hL).2 (.edges i hi Set.univ) (.edges j hj Set.univ)
  exact ⟨(positiveTransport (meshAt_pos hL k i)).hasUniqueTranspose
      (positiveTransport (meshAt_pos hL k j)) hT,
    (positiveTransport (meshAt_pos hL k i)).admitsRealTransposes
      (positiveTransport (meshAt_pos hL k j)) hT hR⟩
end YangMills.Construction.Tower.FullSpace.EdgeFormTransposesProof
end
