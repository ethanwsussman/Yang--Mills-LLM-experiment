import YangMills.Construction.Towers.CovariantAveragesAtTheTrivialConfigurationProof
import YangMills.Construction.Towers.PairingOfTheRealTransposeOnForms
import YangMills.Construction.Towers.TransposesOfRealLinearMaps
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.EdgeFormTranspose
open YangMills.Construction.Matrices
open LeftChartFields PairedFunctionSpace
structure TransportedPairing (S F : PairedFunctionSpace) where
  push : (S.index → ComplexMatrix2) →ₗ[ℂ] (F.index → ComplexMatrix2)
  pull : (F.index → ComplexMatrix2) →ₗ[ℂ] (S.index → ComplexMatrix2)
  push_pull : ∀ f, push (pull f) = f
  pull_push : ∀ h ∈ S.complexSubmodule, pull (push h) = h
  push_real : ∀ x ∈ S.realSubmodule, push x ∈ F.realSubmodule
  pull_real : ∀ y ∈ F.realSubmodule, pull y ∈ S.realSubmodule
  push_complex : ∀ x ∈ S.complexSubmodule, push x ∈ F.complexSubmodule
  pull_complex : ∀ y ∈ F.complexSubmodule, pull y ∈ S.complexSubmodule
  real_subset : ∀ x ∈ S.realSubmodule, x ∈ S.complexSubmodule
  pair_eq : ∀ x y, S.pair x y = F.pair (push x) (push y)
  finite_src : ∀ x, S.IsFinitelySupported x
  finite_tgt : ∀ y, F.IsFinitelySupported y
variable {S F S' F' : PairedFunctionSpace}
def liftReal (e : TransportedPairing S F) (e' : TransportedPairing S' F')
    (T₀ : S.realSubmodule →ₗ[ℝ] S'.realSubmodule) :
    F.realSubmodule →ₗ[ℝ] F'.realSubmodule where
  toFun f := ⟨e'.push (T₀ ⟨e.pull f, e.pull_real _ f.2⟩), e'.push_real _ (T₀ _).2⟩
  map_add' f g := by
    have h : (⟨e.pull (f + g : F.realSubmodule), e.pull_real _ (f + g).2⟩ : S.realSubmodule) =
        ⟨e.pull f, e.pull_real _ f.2⟩ + ⟨e.pull g, e.pull_real _ g.2⟩ :=
      Subtype.ext (by simp)
    apply Subtype.ext
    simp only [h, map_add]
    simp
  map_smul' c f := by
    have h : (⟨e.pull (c • f : F.realSubmodule), e.pull_real _ (c • f).2⟩ : S.realSubmodule) =
        c • ⟨e.pull f, e.pull_real _ f.2⟩ :=
      Subtype.ext (by simp)
    apply Subtype.ext
    simp only [h, map_smul, RingHom.id_apply]
    simp
def pullComplex (e : TransportedPairing S F) (e' : TransportedPairing S' F')
    (T : F.complexSubmodule →ₗ[ℂ] F'.complexSubmodule) :
    S.complexSubmodule →ₗ[ℂ] S'.complexSubmodule where
  toFun h := ⟨e'.pull (T ⟨e.push h, e.push_complex _ h.2⟩), e'.pull_complex _ (T _).2⟩
  map_add' f g := by
    have h : (⟨e.push (f + g : S.complexSubmodule), e.push_complex _ (f + g).2⟩ :
        F.complexSubmodule) =
        ⟨e.push f, e.push_complex _ f.2⟩ + ⟨e.push g, e.push_complex _ g.2⟩ :=
      Subtype.ext (by simp)
    apply Subtype.ext
    simp only [h, map_add]
    simp
  map_smul' c f := by
    have h : (⟨e.push (c • f : S.complexSubmodule), e.push_complex _ (c • f).2⟩ :
        F.complexSubmodule) =
        c • ⟨e.push f, e.push_complex _ f.2⟩ :=
      Subtype.ext (by simp)
    apply Subtype.ext
    simp only [h, map_smul, RingHom.id_apply]
    simp
def pullReal (e : TransportedPairing S F) (e' : TransportedPairing S' F')
    (T : F.realSubmodule →ₗ[ℝ] F'.realSubmodule) :
    S.realSubmodule →ₗ[ℝ] S'.realSubmodule where
  toFun h := ⟨e'.pull (T ⟨e.push h, e.push_real _ h.2⟩), e'.pull_real _ (T _).2⟩
  map_add' f g := by
    have h : (⟨e.push (f + g : S.realSubmodule), e.push_real _ (f + g).2⟩ : F.realSubmodule) =
        ⟨e.push f, e.push_real _ f.2⟩ + ⟨e.push g, e.push_real _ g.2⟩ :=
      Subtype.ext (by simp)
    apply Subtype.ext
    simp only [h, map_add]
    simp
  map_smul' c f := by
    have h : (⟨e.push (c • f : S.realSubmodule), e.push_real _ (c • f).2⟩ : F.realSubmodule) =
        c • ⟨e.push f, e.push_real _ f.2⟩ :=
      Subtype.ext (by simp)
    apply Subtype.ext
    simp only [h, map_smul, RingHom.id_apply]
    simp
theorem liftReal_push (e : TransportedPairing S F) (e' : TransportedPairing S' F')
    (T₀ : S.realSubmodule →ₗ[ℝ] S'.realSubmodule) (f : S.realSubmodule) :
    (liftReal e e' T₀ ⟨e.push f, e.push_real _ f.2⟩ : F'.index → ComplexMatrix2) =
      e'.push (T₀ f) := by
  have h : (⟨e.pull (e.push f), e.pull_real _ (e.push_real _ f.2)⟩ : S.realSubmodule) = f :=
    Subtype.ext (e.pull_push _ (e.real_subset _ f.2))
  change e'.push (T₀ ⟨e.pull (e.push f), _⟩ : S'.index → ComplexMatrix2) = _
  rw [h]
theorem pair_realTransposeMap_eq (e : TransportedPairing S F) (e' : TransportedPairing S' F')
    (hR : AdmitsRealTransposes F F') (hT : HasUniqueTranspose F F')
    (T₀ : S.realSubmodule →ₗ[ℝ] S'.realSubmodule)
    (g : S'.realSubmodule) (f : S.realSubmodule) :
    S.pair (realTransposeMap T₀ g) f = S'.pair g (T₀ f) := by
  obtain ⟨hF, hR'⟩ := hR
  obtain ⟨h1, h2, -, h4, -, -⟩ := hR' (liftReal e e' T₀) fun _ _ => e'.finite_tgt _
  have hC₁ : IsComplexification T₀ (pullComplex e e' (complexification (liftReal e e' T₀))) := by
    intro a b h hh
    have hρ := h1 ⟨e.push a, e.push_real _ a.2⟩ ⟨e.push b, e.push_real _ b.2⟩
      ⟨e.push h, e.push_complex _ h.2⟩ (by simp [hh])
    change e'.pull _ = _
    rw [hρ, map_add, map_smul, liftReal_push, liftReal_push,
      e'.pull_push _ (e'.real_subset _ (T₀ a).2), e'.pull_push _ (e'.real_subset _ (T₀ b).2)]
  have hC : IsComplexification T₀ (complexification T₀) := Classical.epsilon_spec ⟨_, hC₁⟩
  have hA : ∀ y : F.complexSubmodule,
      e'.push (complexification T₀ ⟨e.pull y, e.pull_complex _ y.2⟩ :
          S'.index → ComplexMatrix2) =
        (complexification (liftReal e e' T₀) y : F'.index → ComplexMatrix2) := by
    intro y
    obtain ⟨⟨p, q⟩, hp, -⟩ := hF y
    have hs := hC ⟨e.pull p, e.pull_real _ p.2⟩ ⟨e.pull q, e.pull_real _ q.2⟩
      ⟨e.pull y, e.pull_complex _ y.2⟩ (by simp [hp])
    rw [hs, map_add, map_smul, h1 p q y hp]
    rfl
  obtain ⟨T', hT', uniq⟩ := hT _ h2
  have hĈ : IsTransposeMap (complexification (liftReal e e' T₀))
      (transposeMap (complexification (liftReal e e' T₀))) := Classical.epsilon_spec ⟨T', hT'⟩
  have hD₁ : IsTransposeMap (complexification T₀)
      (pullComplex e' e (transposeMap (complexification (liftReal e e' T₀)))) := by
    intro a b _
    change S.pair (e.pull _) _ = _
    rw [e.pair_eq, e.push_pull, hĈ _ ⟨e.push b, e.push_complex _ b.2⟩ (e.finite_tgt _),
      e'.pair_eq, ← hA]
    have h : (⟨e.pull (e.push b), e.pull_complex _ (e.push_complex _ b.2)⟩ :
        S.complexSubmodule) = b :=
      Subtype.ext (e.pull_push _ b.2)
    simp only [h]
  have hD : IsTransposeMap (complexification T₀) (transposeMap (complexification T₀)) :=
    Classical.epsilon_spec ⟨_, hD₁⟩
  have hQ : ∀ y : F'.complexSubmodule,
      e.push (transposeMap (complexification T₀) ⟨e'.pull y, e'.pull_complex _ y.2⟩ :
          S.index → ComplexMatrix2) =
        (transposeMap (complexification (liftReal e e' T₀)) y : F.index → ComplexMatrix2) := by
    intro y
    have hq := uniq (fun y => ⟨e.push (transposeMap (complexification T₀)
      ⟨e'.pull y, e'.pull_complex _ y.2⟩ : S.index → ComplexMatrix2),
        e.push_complex _ (Subtype.property _)⟩) (by
        intro a b _
        have h := hD ⟨e'.pull a, e'.pull_complex _ a.2⟩ ⟨e.pull b, e.pull_complex _ b.2⟩
          (e.finite_src _)
        rw [e.pair_eq, e'.pair_eq] at h
        simp only [e.push_pull, e'.push_pull, hA] at h
        exact h)
    have hq' := uniq _ hĈ
    exact congrArg Subtype.val ((congrFun hq y).trans (congrFun hq' y).symm)
  have hR₁ : IsRealTransposeMap T₀ (pullReal e' e (realTransposeMap (liftReal e e' T₀))) := by
    intro a h hh
    have h5 := h4 ⟨e'.push a, e'.push_real _ a.2⟩
      ⟨e'.push a, e'.push_complex _ (e'.real_subset _ a.2)⟩ rfl
    change e.pull _ = _
    rw [h5, ← hQ, e.pull_push _ (Subtype.property _)]
    have h6 : (⟨e'.pull (e'.push a), e'.pull_complex _ (e'.push_complex _
        (e'.real_subset _ a.2))⟩ : S'.complexSubmodule) = h :=
      Subtype.ext (by rw [hh]; exact e'.pull_push _ (e'.real_subset _ a.2))
    simp only [h6]
  have hRR : IsRealTransposeMap T₀ (realTransposeMap T₀) := Classical.epsilon_spec ⟨_, hR₁⟩
  have e1 := hRR g ⟨g, e'.real_subset _ g.2⟩ rfl
  have e2 := hD ⟨g, e'.real_subset _ g.2⟩ ⟨f, e.real_subset _ f.2⟩ (e.finite_src _)
  have e3 := hC f 0 ⟨f, e.real_subset _ f.2⟩ (by simp)
  simp only [map_zero, ZeroMemClass.coe_zero, smul_zero, add_zero] at e3
  rw [e1]
  rw [e3] at e2
  exact e2
section OnTheTower
variable {L n k j : ℕ}
abbrev PositiveEdgeIndex (L n k j : ℕ) : Type := ↥(univ : Set (PositiveEdge L n k j))
theorem isPositivelyOriented_or_opposite (b : Edge L n k j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
theorem not_isPositivelyOriented_opposite
    (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) (b : Edge L n k j)
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_not_both_positive <;> assumption
theorem opposite_opposite (b : Edge L n k j) : b.opposite.opposite = b := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_opposite_opposite <;> assumption
def restrictPositive :
    (Edge L n k j → ComplexMatrix2) →ₗ[ℂ] (PositiveEdgeIndex L n k j → ComplexMatrix2) where
  toFun B b := B b.1.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
open Classical in
def oddExtension :
    (PositiveEdgeIndex L n k j → ComplexMatrix2) →ₗ[ℂ] (Edge L n k j → ComplexMatrix2) where
  toFun f b := if h : b.IsPositivelyOriented then f ⟨⟨b, h⟩, trivial⟩
    else if h' : b.opposite.IsPositivelyOriented then -f ⟨⟨b.opposite, h'⟩, trivial⟩ else 0
  map_add' f g := by
    funext b
    by_cases h : b.IsPositivelyOriented
    · simp [h]
    · by_cases h' : b.opposite.IsPositivelyOriented
      · simp [h, h']
        abel
      · simp [h, h']
  map_smul' c f := by
    funext b
    by_cases h : b.IsPositivelyOriented
    · simp [h]
    · by_cases h' : b.opposite.IsPositivelyOriented <;> simp [h, h']
theorem oddExtension_of_pos (f : PositiveEdgeIndex L n k j → ComplexMatrix2) (b : Edge L n k j)
    (h : b.IsPositivelyOriented) : oddExtension f b = f ⟨⟨b, h⟩, trivial⟩ := by
  simp [oddExtension, h]
theorem oddExtension_of_neg (f : PositiveEdgeIndex L n k j → ComplexMatrix2) (b : Edge L n k j)
    (h : ¬ b.IsPositivelyOriented) (h' : b.opposite.IsPositivelyOriented) :
    oddExtension f b = -f ⟨⟨b.opposite, h'⟩, trivial⟩ := by
  simp [oddExtension, h, h']
theorem isBondForm_oddExtension (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k)
    {𝔥 : Set ComplexMatrix2}
    {f : PositiveEdgeIndex L n k j → ComplexMatrix2} (h : ∀ b, f b ∈ 𝔥) :
    PeriodicLattice.IsBondForm 𝔥 (oddExtension f) := by
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · rw [oddExtension_of_pos f b hb]
    exact h _
  · by_cases hb : b.IsPositivelyOriented
    · have h' := not_isPositivelyOriented_opposite hA hL hn hj b hb
      have h'' : b.opposite.opposite.IsPositivelyOriented := by rwa [opposite_opposite]
      rw [oddExtension_of_neg f _ h' h'', oddExtension_of_pos f b hb]
      simp only [opposite_opposite]
    · have h' := (isPositivelyOriented_or_opposite b).resolve_left hb
      rw [oddExtension_of_neg f b hb h', oddExtension_of_pos f _ h', neg_neg]
def edgeFormTransport (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k)
    (hfin : Finite (PositiveEdge L n k j)) :
    TransportedPairing (edgePairedSpace L n k j) (pairedFunctions (PositiveEdgeIndex L n k j)) where
  push := restrictPositive
  pull := oddExtension
  push_pull f := by
    funext b
    exact oddExtension_of_pos f b.1.1 b.1.2
  pull_push h hh := by
    funext b
    by_cases hb : b.IsPositivelyOriented
    · exact oddExtension_of_pos _ b hb
    · have h' := (isPositivelyOriented_or_opposite b).resolve_left hb
      refine (oddExtension_of_neg _ b hb h').trans ?_
      change -h b.opposite = h b
      rw [hh.2 b, neg_neg]
  push_real x hx := fun b _ => hx.1 b.1.1 b.1.2
  pull_real y hy := isBondForm_oddExtension hA hL hn hj fun b => hy b trivial
  push_complex x hx := fun b _ => hx.1 b.1.1 b.1.2
  pull_complex y hy := isBondForm_oddExtension hA hL hn hj fun b => hy b trivial
  real_subset x hx := ⟨fun b hb => (hx.1 b hb).2, hx.2⟩
  pair_eq x y := by
    change traceFinsumPairing _ _ = traceFinsumPairing _ _
    unfold YangMills.Construction.Tower.traceFinsumPairing
    exact (finsum_comp_equiv (Equiv.Set.univ (PositiveEdge L n k j))
      (f := fun b => ComplexMatrix2.halfTrace
        (restrictToPositiveEdges x b * restrictToPositiveEdges y b))).symm
  finite_src x := Set.toFinite _
  finite_tgt y := Set.toFinite _
end OnTheTower
theorem realTransposeEdgeFormPairing_holds (hChart : LeftChartFields.Claim)
    (hReal : RealTransposesExist)
    (hLat : QuotientLattices.TorusAndSpaceLatticeProperties) :
    RealTransposeEdgeFormPairing := by
  intro L n k a b hL hn ha hb T₀ g f
  have hAa := (hChart.2.2 L k a hL ha).1 n hn
  have hAb := (hChart.2.2 L k b hL hb).1 n hn
  have ea := edgeFormTransport hLat hL hn ha hAa.2.1.1
  have eb := edgeFormTransport hLat hL hn hb hAb.2.1.1
  have hR : PairedFunctionSpace.AdmitsRealTransposes (pairedFunctions (PositiveEdgeIndex L n k a))
      (pairedFunctions (PositiveEdgeIndex L n k b)) :=
    (hReal L k hL).1 n hn (.edges a ha univ) (.edges b hb univ)
  have hT : LeftChartFields.HasUniqueTranspose (pairedFunctions (PositiveEdgeIndex L n k a))
      (pairedFunctions (PositiveEdgeIndex L n k b)) :=
    (hAa.2.2 (.edges a ha univ) (.edges b hb univ)).1
  exact pair_realTransposeMap_eq ea eb hR hT T₀ g f
end YangMills.Construction.Tower.EdgeFormTranspose
end
