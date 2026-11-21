import YangMills.Construction.Torus.CoveringMapOpenAndCompactSetsAndDerivativesOfTuples
import YangMills.Construction.Torus.GradientNormLipschitzConstantAndSharpNorm
import YangMills.Construction.Torus.SeparatedTuplesFormsAndDistinctPointsOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false

section
open Set Filter Function
noncomputable section
namespace YangMills.Construction.AmbientPoints
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
variable {s : Conventions.StandingParameters} {E : Ambient} {n : ℕ}
def lipschitzCompactSupportIn (A : Set (Pt s E)) : Set (Pt s E → ℝ) :=
  {f | TestFunctions.IsLipschitzFor (pointDist s E) f ∧ IsCompact (tsupport f) ∧ tsupport f ⊆ A}
def IsLinearSpaceWithUnionSupport (V : Set (Pt s E → ℝ)) : Prop :=
  0 ∈ V ∧ ∀ f ∈ V, ∀ g ∈ V, ∀ a b : ℝ,
    a • f + b • g ∈ V ∧ tsupport (a • f + b • g) ⊆ tsupport f ∪ tsupport g
def IsClosedUnderComponentCombination (S : Set (Fin n → Pt s E → ℝ)) : Prop :=
  ∀ (k : Fin n) (f g : Fin n → Pt s E → ℝ), f ∈ S → g ∈ S → (∀ i, i ≠ k → f i = g i) →
    ∀ a b : ℝ, update f k (a • f k + b • g k) ∈ S
def c1ProductOver (A : Fin n → Set (Pt s E)) : Set (Fin n → Pt s E → ℝ) :=
  pi univ fun i => c1CompactSupportIn (A i)
def PairwiseDisjointFamily (A : Fin n → Set (Pt s E)) : Prop :=
  ∀ i j, i ≠ j → Disjoint (A i) (A j)
def PairwisePositiveGap (A : Fin n → Set (Pt s E)) : Prop :=
  ∀ i j, i ≠ j → 0 < setDist s E (A i) (A j)
def restrictForm {S P : Set (Fin n → Pt s E → ℝ)} (h : P ⊆ S) (Φ : TupleForm S) : TupleForm P :=
  fun f => Φ ⟨f, h f.2⟩
def IsEntrywiseLinear {P : Set (Fin n → Pt s E → ℝ)} (Ψ : TupleForm P) : Prop :=
  (∀ (k : Fin n) (g : Fin n → Pt s E → ℝ) (u v : Pt s E → ℝ)
      (hu : update g k u ∈ P) (hv : update g k v ∈ P) (huv : update g k (u + v) ∈ P),
      Ψ ⟨_, huv⟩ = Ψ ⟨_, hu⟩ + Ψ ⟨_, hv⟩) ∧
    ∀ (k : Fin n) (g : Fin n → Pt s E → ℝ) (u : Pt s E → ℝ) (c : ℝ)
      (hu : update g k u ∈ P) (hc : update g k (c • u) ∈ P),
      Ψ ⟨_, hc⟩ = (c : ℂ) * Ψ ⟨_, hu⟩
variable (s E n) in
structure SeparationAndProductFacts : Prop where
  gap_pos : 2 ≤ n → ∀ f : Fin n → Pt s E → ℝ,
    f ∈ sepTuples s E n ∨ f ∈ sepLipTuples s E n → 0 < supportGap f
  c1_isSpace : ∀ A : Set (Pt s E),
    IsLinearSpaceWithUnionSupport (c1CompactSupportIn A)
  lip_isSpace : ∀ A : Set (Pt s E),
    IsLinearSpaceWithUnionSupport (lipschitzCompactSupportIn A)
  sepTuplesIn_closed : ∀ O : Set (Pt s E), IsOpen O →
    IsClosedUnderComponentCombination (sepTuplesIn n O)
  sepLipTuplesIn_closed : ∀ O : Set (Pt s E), IsOpen O →
    IsClosedUnderComponentCombination (sepLipTuplesIn n O)
  c1ProductOver_subset : ∀ A : Fin n → Set (Pt s E), PairwiseDisjointFamily A →
    c1ProductOver A ⊆ sepTuples s E n
  restrict_isEntrywiseLinear : ∀ (A : Fin n → Set (Pt s E)) (hA : PairwiseDisjointFamily A)
    (Φ : TupleForm (sepTuples s E n)), TupleForm.IsMultilinear Φ →
    IsEntrywiseLinear (restrictForm (c1ProductOver_subset A hA) Φ)
  restrict_isReal : ∀ (A : Fin n → Set (Pt s E)) (hA : PairwiseDisjointFamily A)
    (Φ : TupleForm (sepTuples s E n)), TupleForm.IsMultilinear Φ → TupleForm.IsReal Φ →
    TupleForm.IsReal (restrictForm (c1ProductOver_subset A hA) Φ)
  isMultilinear_of_restrict : ∀ Φ : TupleForm (sepTuples s E n),
    (∀ (A : Fin n → Set (Pt s E)) (hA : PairwiseDisjointFamily A), (∀ i, IsCompact (A i)) →
      IsEntrywiseLinear (restrictForm (c1ProductOver_subset A hA) Φ)) →
    TupleForm.IsMultilinear Φ
  disjoint_iff_gap_pos : ∀ A : Fin n → Set (Pt s E), (∀ i, IsCompact (A i)) →
    (PairwiseDisjointFamily A ↔ PairwisePositiveGap A)
  eq_zero_of_entry_eq_zero : ∀ Φ : TupleForm (sepTuples s E n), TupleForm.IsMultilinear Φ →
    ∀ (f : sepTuples s E n) (k : Fin n), (∀ y, f.1 k y = 0) → Φ f = 0
  sepTuplesIn_subset_sepLipTuplesIn : ∀ O : Set (Pt s E), IsOpen O →
    sepTuplesIn n O ⊆ sepLipTuplesIn n O
def SeparationAndProductFacts.statement : Prop :=
  ∀ (s : Conventions.StandingParameters) (n : ℕ), 1 ≤ n →
    (∀ E : Ambient, SeparationAndProductFacts s E n) ∧
      ∀ r : ℕ → ℝ, (∀ j, 0 < r j) → Tendsto r atTop atTop →
        ∀ f ∈ sepTuples s .euclidean n, ∃ j₀ : ℕ, ∀ j, j₀ ≤ j →
          f ∈ sepTuplesIn n (openBall s .euclidean (0 : Fin 4 → ℝ) (r j))
end YangMills.Construction.AmbientPoints
end
end

open Set Filter YangMills.Construction.TestFunctions
open Function (update update_self update_of_ne update_eq_self)
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
noncomputable section
namespace YangMills.Construction.AmbientPoints.SeparationAndProductFacts
variable {s : Conventions.StandingParameters} {E : Ambient} {n : ℕ}
theorem contPartials_const_zero {D : ℕ} (ν : ℕ) :
    ContinuousPartialsUpTo (univ : Set (Fin D → ℝ)) ν (fun _ => (0 : ℂ)) := by
  induction ν with
  | zero => exact continuousOn_const
  | succ ν ih =>
    refine ⟨continuousOn_const, fun j => ?_⟩
    have hd : ∀ x : Fin D → ℝ,
        HasLineDerivAt ℝ (fun _ : Fin D → ℝ => (0 : ℂ)) 0 x (Pi.single j 1) :=
      fun x => hasDerivAt_const _ _
    have he : partialDeriv j (fun _ : Fin D → ℝ => (0 : ℂ)) = fun _ => 0 :=
      funext fun x => (hd x).lineDeriv
    refine ⟨fun x _ => (hd x).lineDifferentiableAt, ?_⟩
    rw [he]
    exact ih
theorem contPartials_linComb {D : ℕ} (c c' : ℂ) {ν : ℕ} {G G' : (Fin D → ℝ) → ℂ}
    (h : ContinuousPartialsUpTo univ ν G) (h' : ContinuousPartialsUpTo univ ν G') :
    ContinuousPartialsUpTo univ ν (fun x => c * G x + c' * G' x) := by
  induction ν generalizing G G' with
  | zero => exact (continuousOn_const.mul h).add (continuousOn_const.mul h')
  | succ ν ih =>
    refine ⟨(continuousOn_const.mul h.1).add (continuousOn_const.mul h'.1), fun j => ?_⟩
    have hd : ∀ x : Fin D → ℝ, HasLineDerivAt ℝ (fun y => c * G y + c' * G' y)
        (c * partialDeriv j G x + c' * partialDeriv j G' x) x (Pi.single j 1) := by
      intro x
      have h₁ : HasDerivAt (fun t : ℝ => G (x + t • Pi.single j 1)) (partialDeriv j G x) 0 :=
        ((h.2 j).1 x (mem_univ x)).hasLineDerivAt
      have h₂ : HasDerivAt (fun t : ℝ => G' (x + t • Pi.single j 1))
          (partialDeriv j G' x) 0 := ((h'.2 j).1 x (mem_univ x)).hasLineDerivAt
      exact (h₁.const_mul c).add (h₂.const_mul c')
    have he : partialDeriv j (fun y => c * G y + c' * G' y) =
        fun x => c * partialDeriv j G x + c' * partialDeriv j G' x :=
      funext fun x => (hd x).lineDeriv
    refine ⟨fun x _ => (hd x).lineDifferentiableAt, ?_⟩
    rw [he]
    exact ih (h.2 j).2 (h'.2 j).2
theorem isC1_zero : IsC1 (0 : Pt s E → ℝ) := by
  refine ⟨isOpen_univ, fun m _ => ?_⟩
  have he : asFunctionOnOnePoint (0 : Pt s E → ℝ) ∘ tupleProj s E 1 = fun _ => (0 : ℂ) := by
    funext x
    simp [asFunctionOnOnePoint]
  rw [he]
  exact contPartials_const_zero m
theorem isC1_linComb {f f' : Pt s E → ℝ} (b b' : ℝ) (h : IsC1 f)
    (h' : IsC1 f') : IsC1 (b • f + b' • f') := by
  refine ⟨isOpen_univ, fun m hm => ?_⟩
  have he : asFunctionOnOnePoint (b • f + b' • f') ∘ tupleProj s E 1 =
      fun x => (b : ℂ) * (asFunctionOnOnePoint f ∘ tupleProj s E 1) x +
        (b' : ℂ) * (asFunctionOnOnePoint f' ∘ tupleProj s E 1) x := by
    funext x
    simp [asFunctionOnOnePoint]
  rw [he]
  exact contPartials_linComb _ _ (h.2 m hm) (h'.2 m hm)
theorem isLipschitzFor_zero : IsLipschitzFor (pointDist s E) (0 : Pt s E → ℝ) :=
  ⟨0, le_rfl, fun x y => by simp⟩
theorem isLipschitzFor_linComb {f f' : Pt s E → ℝ} (b b' : ℝ)
    (h : IsLipschitzFor (pointDist s E) f) (h' : IsLipschitzFor (pointDist s E) f') :
    IsLipschitzFor (pointDist s E) (b • f + b' • f') := by
  obtain ⟨C, hC, hf⟩ := h
  obtain ⟨C', hC', hf'⟩ := h'
  refine ⟨|b| * C + |b'| * C', by positivity, fun x y => ?_⟩
  have he : (b • f + b' • f') x - (b • f + b' • f') y =
      b * (f x - f y) + b' * (f' x - f' y) := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [he]
  calc ‖b * (f x - f y) + b' * (f' x - f' y)‖
      ≤ ‖b * (f x - f y)‖ + ‖b' * (f' x - f' y)‖ := norm_add_le _ _
    _ = |b| * ‖f x - f y‖ + |b'| * ‖f' x - f' y‖ := by
        simp only [norm_mul, Real.norm_eq_abs]
    _ ≤ |b| * (C * pointDist s E x y) + |b'| * (C' * pointDist s E x y) :=
        add_le_add (mul_le_mul_of_nonneg_left (hf x y) (abs_nonneg b))
          (mul_le_mul_of_nonneg_left (hf' x y) (abs_nonneg b'))
    _ = (|b| * C + |b'| * C') * pointDist s E x y := by ring
theorem tsupport_linComb_subset (f f' : Pt s E → ℝ) (b b' : ℝ) :
    tsupport (b • f + b' • f') ⊆ tsupport f ∪ tsupport f' := by
  refine closure_minimal ?_ ((isClosed_tsupport f).union (isClosed_tsupport f'))
  intro x hx
  by_contra hn
  simp only [mem_union, not_or] at hn
  have h₁ : f x = 0 := image_eq_zero_of_notMem_tsupport hn.1
  have h₂ : f' x = 0 := image_eq_zero_of_notMem_tsupport hn.2
  exact (Function.mem_support.mp hx) (by simp [h₁, h₂])
theorem isCompact_tsupport_linComb {f f' : Pt s E → ℝ} (b b' : ℝ)
    (h : IsCompact (tsupport f)) (h' : IsCompact (tsupport f')) :
    IsCompact (tsupport (b • f + b' • f')) :=
  (h.union h').of_isClosed_subset (isClosed_tsupport _) (tsupport_linComb_subset f f' b b')
theorem isLinearSpace_of_closed (P : (Pt s E → ℝ) → Prop) (h0 : P 0)
    (hc : ∀ (f f' : Pt s E → ℝ) (b b' : ℝ), P f → P f' → P (b • f + b' • f'))
    (A : Set (Pt s E)) :
    IsLinearSpaceWithUnionSupport {f | P f ∧ IsCompact (tsupport f) ∧ tsupport f ⊆ A} := by
  have hz : tsupport (0 : Pt s E → ℝ) = ∅ := by simp [tsupport]
  refine ⟨⟨h0, by rw [hz]; exact isCompact_empty, by rw [hz]; exact empty_subset _⟩, ?_⟩
  intro f hf f' hf' b b'
  have hs := tsupport_linComb_subset f f' b b'
  exact ⟨⟨hc f f' b b' hf.1 hf'.1, isCompact_tsupport_linComb b b' hf.2.1 hf'.2.1,
    hs.trans (union_subset hf.2.2 hf'.2.2)⟩, hs⟩
theorem c1CompactSupportIn_isSpace (A : Set (Pt s E)) :
    IsLinearSpaceWithUnionSupport (c1CompactSupportIn A) :=
  isLinearSpace_of_closed IsC1 isC1_zero
    (fun _ _ b b' h h' => isC1_linComb b b' h h') A
theorem lipschitzCompactSupportIn_isSpace (A : Set (Pt s E)) :
    IsLinearSpaceWithUnionSupport (lipschitzCompactSupportIn A) :=
  isLinearSpace_of_closed (IsLipschitzFor (pointDist s E)) isLipschitzFor_zero
    (fun _ _ b b' h h' => isLipschitzFor_linComb b b' h h') A
theorem update_mem_of_forall {P : (Pt s E → ℝ) → Prop} {f : Fin n → Pt s E → ℝ}
    (hf : ∀ i, P (f i)) (l : Fin n) {u : Pt s E → ℝ} (hu : P u) (i : Fin n) :
    P (update f l u i) := by
  by_cases hi : i = l
  · subst hi
    rw [update_self]
    exact hu
  · rw [update_of_ne hi]
    exact hf i
theorem compactDisjointSupports_update {f f' : Fin n → Pt s E → ℝ}
    (hf : CompactDisjointSupports f) (hf' : CompactDisjointSupports f') (l : Fin n)
    (hag : ∀ i, i ≠ l → f i = f' i) (b b' : ℝ) :
    CompactDisjointSupports (update f l (b • f l + b' • f' l)) := by
  have hs : ∀ i, i ≠ l → update f l (b • f l + b' • f' l) i = f i :=
    fun i hi => update_of_ne hi _ _
  have hl : update f l (b • f l + b' • f' l) l = b • f l + b' • f' l := update_self _ _ _
  have hd : ∀ i, i ≠ l → Disjoint (tsupport (b • f l + b' • f' l)) (tsupport (f i)) := by
    intro i hi
    refine Disjoint.mono_left (tsupport_linComb_subset _ _ b b') ?_
    refine disjoint_union_left.2 ⟨hf.2 l i (Ne.symm hi), ?_⟩
    rw [hag i hi]
    exact hf'.2 l i (Ne.symm hi)
  refine ⟨fun i => ?_, fun i i' hii' => ?_⟩
  · by_cases hi : i = l
    · subst hi
      rw [hl]
      exact isCompact_tsupport_linComb b b' (hf.1 i) (hf'.1 i)
    · rw [hs i hi]
      exact hf.1 i
  · by_cases hi : i = l
    · subst hi
      rw [hl, hs i' (Ne.symm hii')]
      exact hd i' (Ne.symm hii')
    · by_cases hi' : i' = l
      · subst hi'
        rw [hl, hs i hi]
        exact (hd i hi).symm
      · rw [hs i hi, hs i' hi']
        exact hf.2 i i' hii'
theorem supportsWithin_update {f f' : Fin n → Pt s E → ℝ} {O : Set (Pt s E)}
    (hf : SupportsWithin f O) (hf' : SupportsWithin f' O) (l : Fin n) (b b' : ℝ) :
    SupportsWithin (update f l (b • f l + b' • f' l)) O :=
  update_mem_of_forall (P := fun u => tsupport u ⊆ O) hf l
    ((tsupport_linComb_subset _ _ b b').trans (union_subset (hf l) (hf' l)))
theorem sepTuplesIn_componentClosed (O : Set (Pt s E)) :
    IsClosedUnderComponentCombination (sepTuplesIn n O) := by
  intro l f f' hf hf' hag b b'
  exact ⟨⟨update_mem_of_forall hf.1.1 l (isC1_linComb b b' (hf.1.1 l) (hf'.1.1 l)),
    compactDisjointSupports_update hf.1.2 hf'.1.2 l hag b b'⟩,
    supportsWithin_update hf.2 hf'.2 l b b'⟩
theorem sepLipTuplesIn_componentClosed (O : Set (Pt s E)) :
    IsClosedUnderComponentCombination (sepLipTuplesIn n O) := by
  intro l f f' hf hf' hag b b'
  exact ⟨⟨update_mem_of_forall hf.1.1 l (isLipschitzFor_linComb b b' (hf.1.1 l) (hf'.1.1 l)),
    compactDisjointSupports_update hf.1.2 hf'.1.2 l hag b b'⟩,
    supportsWithin_update hf.2 hf'.2 l b b'⟩
theorem c1ProductOver_subset_sepTuples (A : Fin n → Set (Pt s E))
    (hA : PairwiseDisjointFamily A) : c1ProductOver A ⊆ sepTuples s E n := by
  intro f hf
  have hf' : ∀ i, f i ∈ c1CompactSupportIn (A i) := fun i => hf i (mem_univ i)
  exact ⟨fun i => (hf' i).1, fun i => (hf' i).2.1, fun i i' hii' =>
    (hA i i' hii').mono (hf' i).2.2 (hf' i').2.2⟩
theorem tupleForm_congr {𝔖 : Set (Fin n → Pt s E → ℝ)} (Φ : TupleForm 𝔖)
    {x y : Fin n → Pt s E → ℝ} (hx : x ∈ 𝔖) (hy : y ∈ 𝔖) (h : x = y) :
    Φ ⟨x, hx⟩ = Φ ⟨y, hy⟩ := by
  subst h
  rfl
theorem restrictForm_entrywiseLinear {A : Fin n → Set (Pt s E)}
    (hA : PairwiseDisjointFamily A) (Φ : TupleForm (sepTuples s E n))
    (hΦ : TupleForm.IsMultilinear Φ) :
    IsEntrywiseLinear (restrictForm (c1ProductOver_subset_sepTuples A hA) Φ) := by
  have hsub := c1ProductOver_subset_sepTuples A hA
  refine ⟨fun l g u v hu hv huv => ?_, fun l g u b hu hb => ?_⟩
  · have e : update (update g l u) l ((1 : ℝ) • update g l u l + (1 : ℝ) • update g l v l) =
        update g l (u + v) := by
      simp
    have hm : update (update g l u) l ((1 : ℝ) • update g l u l + (1 : ℝ) • update g l v l) ∈
        sepTuples s E n := by
      rw [e]
      exact hsub huv
    have key := hΦ l 1 1 ⟨_, hsub hu⟩ ⟨_, hsub hv⟩
      (fun i hi => by simp [update_of_ne hi]) hm
    simp only [Complex.ofReal_one, one_mul] at key
    exact (tupleForm_congr Φ (hsub huv) hm e.symm).trans key
  · have e : update (update g l u) l (b • update g l u l + (0 : ℝ) • update g l u l) =
        update g l (b • u) := by
      simp
    have hm : update (update g l u) l (b • update g l u l + (0 : ℝ) • update g l u l) ∈
        sepTuples s E n := by
      rw [e]
      exact hsub hb
    have key := hΦ l b 0 ⟨_, hsub hu⟩ ⟨_, hsub hu⟩ (fun _ _ => rfl) hm
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at key
    exact (tupleForm_congr Φ (hsub hb) hm e.symm).trans key
theorem isMultilinear_of_restrictForm (Φ : TupleForm (sepTuples s E n))
    (hΦ : ∀ (A : Fin n → Set (Pt s E)) (hA : PairwiseDisjointFamily A), (∀ i, IsCompact (A i)) →
      IsEntrywiseLinear (restrictForm (c1ProductOver_subset_sepTuples A hA) Φ)) :
    TupleForm.IsMultilinear Φ := by
  intro l b b' f f' hag h
  obtain ⟨f, hf⟩ := f
  obtain ⟨f', hf'⟩ := f'
  simp only at hag h ⊢
  let A : Fin n → Set (Pt s E) :=
    update (fun i => tsupport (f i)) l (tsupport (f l) ∪ tsupport (f' l))
  have hAl : A l = tsupport (f l) ∪ tsupport (f' l) := update_self _ _ _
  have hAi : ∀ i, i ≠ l → A i = tsupport (f i) := fun i hi => update_of_ne hi _ _
  have hcomp : ∀ i, IsCompact (A i) := by
    intro i
    by_cases hi : i = l
    · subst hi
      rw [hAl]
      exact (hf.2.1 i).union (hf'.2.1 i)
    · rw [hAi i hi]
      exact hf.2.1 i
  have hdl : ∀ i, i ≠ l → Disjoint (A l) (A i) := by
    intro i hi
    rw [hAl, hAi i hi]
    refine disjoint_union_left.2 ⟨hf.2.2 l i (Ne.symm hi), ?_⟩
    rw [hag i hi]
    exact hf'.2.2 l i (Ne.symm hi)
  have hdisj : PairwiseDisjointFamily A := by
    intro i i' hii'
    by_cases hi : i = l
    · subst hi
      exact hdl i' (Ne.symm hii')
    · by_cases hi' : i' = l
      · subst hi'
        exact (hdl i hi).symm
      · rw [hAi i hi, hAi i' hi']
        exact hf.2.2 i i' hii'
  have hfl : f l ∈ c1CompactSupportIn (A l) :=
    ⟨hf.1 l, hf.2.1 l, by rw [hAl]; exact subset_union_left⟩
  have hf'l : f' l ∈ c1CompactSupportIn (A l) :=
    ⟨hf'.1 l, hf'.2.1 l, by rw [hAl]; exact subset_union_right⟩
  have hprod : ∀ u ∈ c1CompactSupportIn (A l), update f l u ∈ c1ProductOver A := by
    intro u hu i _
    by_cases hi : i = l
    · subst hi
      rw [update_self]
      exact hu
    · rw [update_of_ne hi]
      exact ⟨hf.1 i, hf.2.1 i, by rw [hAi i hi]⟩
  have hsub := c1ProductOver_subset_sepTuples A hdisj
  obtain ⟨hadd, hhom⟩ := hΦ A hdisj hcomp
  have hS := (c1CompactSupportIn_isSpace (A l)).2
  have hu : b • f l ∈ c1CompactSupportIn (A l) := by
    simpa using (hS _ hfl _ hfl b 0).1
  have hv : b' • f' l ∈ c1CompactSupportIn (A l) := by
    simpa using (hS _ hf'l _ hf'l 0 b').1
  have huv := (hS _ hfl _ hf'l b b').1
  have e₁ : Φ ⟨_, hsub (hprod _ huv)⟩ =
      Φ ⟨_, hsub (hprod _ hu)⟩ + Φ ⟨_, hsub (hprod _ hv)⟩ :=
    hadd l f _ _ (hprod _ hu) (hprod _ hv) (hprod _ huv)
  have e₂ : Φ ⟨_, hsub (hprod _ hu)⟩ = (b : ℂ) * Φ ⟨_, hsub (hprod _ hfl)⟩ :=
    hhom l f _ b (hprod _ hfl) (hprod _ hu)
  have e₃ : Φ ⟨_, hsub (hprod _ hv)⟩ = (b' : ℂ) * Φ ⟨_, hsub (hprod _ hf'l)⟩ :=
    hhom l f _ b' (hprod _ hf'l) (hprod _ hv)
  have e₄ : Φ ⟨_, hsub (hprod _ hfl)⟩ = Φ ⟨f, hf⟩ :=
    tupleForm_congr Φ _ _ (update_eq_self l f)
  have e₅ : Φ ⟨_, hsub (hprod _ hf'l)⟩ = Φ ⟨f', hf'⟩ := by
    refine tupleForm_congr Φ _ _ ?_
    funext i
    by_cases hi : i = l
    · subst hi
      rw [update_self]
    · rw [update_of_ne hi, hag i hi]
  rw [e₄] at e₂
  rw [e₅] at e₃
  rw [e₂, e₃] at e₁
  exact e₁
theorem tupleForm_eq_zero_of_component (Φ : TupleForm (sepTuples s E n))
    (hΦ : TupleForm.IsMultilinear Φ)
    (f : sepTuples s E n) (l : Fin n) (h0 : ∀ y, f.1 l y = 0) : Φ f = 0 := by
  have hz : f.1 l = 0 := funext h0
  have e : update f.1 l ((0 : ℝ) • f.1 l + (0 : ℝ) • f.1 l) = f.1 := by
    rw [zero_smul, add_zero, ← hz, update_eq_self]
  have hm : update f.1 l ((0 : ℝ) • f.1 l + (0 : ℝ) • f.1 l) ∈ sepTuples s E n := by
    rw [e]
    exact f.2
  have key := hΦ l 0 0 f f (fun _ _ => rfl) hm
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at key
  exact (tupleForm_congr Φ f.2 hm e.symm).trans key
theorem disjoint_iff_setDist_pos (h₁ : TupleTopology.Holds) (A : Fin n → Set (Pt s E))
    (hA : ∀ i, IsCompact (A i)) : PairwiseDisjointFamily A ↔ PairwisePositiveGap A := by
  refine ⟨fun h i i' hii' => (h₁ s E).2.2 _ _ (hA i) (hA i') (h i i' hii'),
    fun h i i' hii' => ?_⟩
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  have hle : setDist s E (A i) (A i') ≤ ENNReal.ofReal (pointDist s E x x) :=
    iInf₂_le_of_le x hx (iInf₂_le_of_le x hx' le_rfl)
  rw [pointDist_self, ENNReal.ofReal_zero] at hle
  exact absurd (lt_of_lt_of_le (h i i' hii') hle) (lt_irrefl _)
theorem supportGap_pos_of_compact (h₁ : TupleTopology.Holds) (hn : 2 ≤ n)
    (f : Fin n → Pt s E → ℝ) (hc : CompactDisjointSupports f) : 0 < supportGap f := by
  obtain ⟨⟨p, hp, hpe⟩, -⟩ := isLeast_supportGap hn f
  rw [← hpe]
  exact (h₁ s E).2.2 _ _ (hc.1 _) (hc.1 _) (hc.2 _ _ hp)
theorem isLipschitzFor_of_isC1 (h₂ : GradientC1Bounds.Statement)
    {u : Pt s E → ℝ} (hu : IsC1 u) (hc : IsCompact (tsupport u)) :
    IsLipschitzFor (pointDist s E) u := by
  have hs : IsCompact (closedSupport (ofSinglePoint fun x : Pt s E => (u x : ℂ))) := by
    change IsCompact (closedSupport (asFunctionOnOnePoint u))
    rw [closedSupport_asFunctionOnOnePoint]
    exact (Homeomorph.funUnique (Fin 1) (Pt s E)).isCompact_preimage.mpr hc
  exact ((h₂ s E).2 ⟨1, mem_Ici.2 le_rfl⟩ u hu hs).2.1
theorem sepTuplesIn_subset_lip (h₂ : GradientC1Bounds.Statement)
    (O : Set (Pt s E)) : sepTuplesIn n O ⊆ sepLipTuplesIn n O :=
  fun _ hf => ⟨⟨fun i => isLipschitzFor_of_isC1 h₂ (hf.1.1 i) (hf.1.2.1 i), hf.1.2⟩, hf.2⟩
theorem eventually_mem_sepTuplesIn_ball (r : ℕ → ℝ) (hr : Tendsto r atTop atTop)
    (f : Fin n → Pt s .euclidean → ℝ) (hf : f ∈ sepTuples s .euclidean n) :
    ∃ j₀ : ℕ, ∀ j, j₀ ≤ j →
      f ∈ sepTuplesIn n (openBall s .euclidean (0 : Fin 4 → ℝ) (r j)) := by
  have hb : Bornology.IsBounded (⋃ i, tsupport (f i)) := (isCompact_iUnion hf.2.1).isBounded
  obtain ⟨R, hR⟩ := hb.subset_ball (show Pt s .euclidean from (0 : Fin 4 → ℝ))
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.1 (tendsto_atTop.1 hr R)
  refine ⟨j₀, fun j hj => ⟨hf, fun i x hx => ?_⟩⟩
  exact Metric.ball_subset_ball (hj₀ j hj) (hR (mem_iUnion.2 ⟨i, hx⟩))
theorem statement_holds (h₁ : TupleTopology.Holds)
    (h₂ : GradientC1Bounds.Statement) :
    SeparationAndProductFacts.statement := by
  intro s n _
  refine ⟨fun E => ?_, fun r _ hr f hf => eventually_mem_sepTuplesIn_ball r hr f hf⟩
  exact
    { gap_pos := fun hn f hf => supportGap_pos_of_compact h₁ hn f (hf.elim (·.2) (·.2))
      c1_isSpace := c1CompactSupportIn_isSpace
      lip_isSpace := lipschitzCompactSupportIn_isSpace
      sepTuplesIn_closed := fun O _ => sepTuplesIn_componentClosed O
      sepLipTuplesIn_closed := fun O _ => sepLipTuplesIn_componentClosed O
      c1ProductOver_subset := c1ProductOver_subset_sepTuples
      restrict_isEntrywiseLinear := fun _ hA Φ hΦ => restrictForm_entrywiseLinear hA Φ hΦ
      restrict_isReal := fun _ _ Φ _ hr f => hr _
      isMultilinear_of_restrict := isMultilinear_of_restrictForm
      disjoint_iff_gap_pos := disjoint_iff_setDist_pos h₁
      eq_zero_of_entry_eq_zero := tupleForm_eq_zero_of_component
      sepTuplesIn_subset_sepLipTuplesIn := fun O _ => sepTuplesIn_subset_lip h₂ O }
end YangMills.Construction.AmbientPoints.SeparationAndProductFacts
