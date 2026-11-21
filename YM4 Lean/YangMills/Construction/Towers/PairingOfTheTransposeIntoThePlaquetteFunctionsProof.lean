import YangMills.Construction.Towers.CovariantAveragesAtTheTrivialConfigurationProof
import YangMills.Construction.Towers.PairingOfTheTransposeIntoThePlaquetteFunctions
import YangMills.Construction.Towers.PlaquettesAndSumsOfATower
import YangMills.Construction.Towers.TransposesOfRealLinearMaps
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.TransposeIntoFaces
open YangMills.Construction.Matrices
open YangMills.Construction.Tower.LeftChartFields
open YangMills.Construction.Tower.PairedFunctionSpace
structure Transport (S F : PairedFunctionSpace) where
  ρ : (S.index → ComplexMatrix2) →ₗ[ℂ] (F.index → ComplexMatrix2)
  σ : (F.index → ComplexMatrix2) →ₗ[ℂ] (S.index → ComplexMatrix2)
  ρ_σ : ∀ f, ρ (σ f) = f
  σ_ρ : ∀ h ∈ S.complexSubmodule, σ (ρ h) = h
  ρ_real : ∀ x ∈ S.realSubmodule, ρ x ∈ F.realSubmodule
  σ_real : ∀ y ∈ F.realSubmodule, σ y ∈ S.realSubmodule
  ρ_complex : ∀ x ∈ S.complexSubmodule, ρ x ∈ F.complexSubmodule
  σ_complex : ∀ y ∈ F.complexSubmodule, σ y ∈ S.complexSubmodule
  real_mem_complex : ∀ x ∈ S.realSubmodule, x ∈ S.complexSubmodule
  pair_eq : ∀ x y, S.pair x y = F.pair (ρ x) (ρ y)
  finiteSource : ∀ x, S.IsFinitelySupported x
  finiteTarget : ∀ y, F.IsFinitelySupported y
variable {S F S' F' : PairedFunctionSpace}
def liftLinear (e : Transport S F) (e' : Transport S' F')
    (T₀ : S.realSubmodule →ₗ[ℝ] S'.realSubmodule) :
    F.realSubmodule →ₗ[ℝ] F'.realSubmodule where
  toFun f := ⟨e'.ρ (T₀ ⟨e.σ f, e.σ_real _ f.2⟩), e'.ρ_real _ (T₀ _).2⟩
  map_add' f g := by
    have h : (⟨e.σ (f + g : F.realSubmodule), e.σ_real _ (f + g).2⟩ : S.realSubmodule) =
        ⟨e.σ f, e.σ_real _ f.2⟩ + ⟨e.σ g, e.σ_real _ g.2⟩ :=
      Subtype.ext (by simp)
    apply Subtype.ext
    simp only [h, map_add]
    simp
  map_smul' c f := by
    have h : (⟨e.σ (c • f : F.realSubmodule), e.σ_real _ (c • f).2⟩ : S.realSubmodule) =
        c • ⟨e.σ f, e.σ_real _ f.2⟩ :=
      Subtype.ext (by simp)
    apply Subtype.ext
    simp only [h, map_smul, RingHom.id_apply]
    simp
def pullLinear (e : Transport S F) (e' : Transport S' F')
    (T : F.complexSubmodule →ₗ[ℂ] F'.complexSubmodule) :
    S.complexSubmodule →ₗ[ℂ] S'.complexSubmodule where
  toFun h := ⟨e'.σ (T ⟨e.ρ h, e.ρ_complex _ h.2⟩), e'.σ_complex _ (T _).2⟩
  map_add' f g := by
    have h : (⟨e.ρ (f + g : S.complexSubmodule), e.ρ_complex _ (f + g).2⟩ :
        F.complexSubmodule) = ⟨e.ρ f, e.ρ_complex _ f.2⟩ + ⟨e.ρ g, e.ρ_complex _ g.2⟩ :=
      Subtype.ext (by simp)
    apply Subtype.ext
    simp only [h, map_add]
    simp
  map_smul' c f := by
    have h : (⟨e.ρ (c • f : S.complexSubmodule), e.ρ_complex _ (c • f).2⟩ :
        F.complexSubmodule) = c • ⟨e.ρ f, e.ρ_complex _ f.2⟩ :=
      Subtype.ext (by simp)
    apply Subtype.ext
    simp only [h, map_smul, RingHom.id_apply]
    simp
def pullRealLinear (e : Transport S F) (e' : Transport S' F')
    (T : F.realSubmodule →ₗ[ℝ] F'.realSubmodule) :
    S.realSubmodule →ₗ[ℝ] S'.realSubmodule where
  toFun h := ⟨e'.σ (T ⟨e.ρ h, e.ρ_real _ h.2⟩), e'.σ_real _ (T _).2⟩
  map_add' f g := by
    have h : (⟨e.ρ (f + g : S.realSubmodule), e.ρ_real _ (f + g).2⟩ : F.realSubmodule) =
        ⟨e.ρ f, e.ρ_real _ f.2⟩ + ⟨e.ρ g, e.ρ_real _ g.2⟩ :=
      Subtype.ext (by simp)
    apply Subtype.ext
    simp only [h, map_add]
    simp
  map_smul' c f := by
    have h : (⟨e.ρ (c • f : S.realSubmodule), e.ρ_real _ (c • f).2⟩ : F.realSubmodule) =
        c • ⟨e.ρ f, e.ρ_real _ f.2⟩ :=
      Subtype.ext (by simp)
    apply Subtype.ext
    simp only [h, map_smul, RingHom.id_apply]
    simp
theorem liftLinear_apply_ρ (e : Transport S F) (e' : Transport S' F')
    (T₀ : S.realSubmodule →ₗ[ℝ] S'.realSubmodule) (f : S.realSubmodule) :
    (liftLinear e e' T₀ ⟨e.ρ f, e.ρ_real _ f.2⟩ : F'.index → ComplexMatrix2) = e'.ρ (T₀ f) := by
  have h : (⟨e.σ (e.ρ f), e.σ_real _ (e.ρ_real _ f.2)⟩ : S.realSubmodule) = f :=
    Subtype.ext (e.σ_ρ _ (e.real_mem_complex _ f.2))
  change e'.ρ (T₀ ⟨e.σ (e.ρ f), _⟩ : S'.index → ComplexMatrix2) = _
  rw [h]
theorem pair_realTransposeMap_of_transport (e : Transport S F) (e' : Transport S' F')
    (hR : AdmitsRealTransposes F F') (hT : HasUniqueTranspose F F')
    (T₀ : S.realSubmodule →ₗ[ℝ] S'.realSubmodule) (g : S'.realSubmodule) (f : S.realSubmodule) :
    S.pair (realTransposeMap T₀ g) f = S'.pair g (T₀ f) := by
  obtain ⟨hF, hR'⟩ := hR
  obtain ⟨h1, h2, -, h4, -, -⟩ := hR' (liftLinear e e' T₀) fun _ _ => e'.finiteTarget _
  have hC₁ : IsComplexification T₀ (pullLinear e e' (complexification (liftLinear e e' T₀))) := by
    intro a b h hh
    have hρ := h1 ⟨e.ρ a, e.ρ_real _ a.2⟩ ⟨e.ρ b, e.ρ_real _ b.2⟩ ⟨e.ρ h, e.ρ_complex _ h.2⟩
      (by simp [hh])
    change e'.σ _ = _
    rw [hρ, map_add, map_smul, liftLinear_apply_ρ, liftLinear_apply_ρ,
      e'.σ_ρ _ (e'.real_mem_complex _ (T₀ a).2), e'.σ_ρ _ (e'.real_mem_complex _ (T₀ b).2)]
  have hC : IsComplexification T₀ (complexification T₀) := Classical.epsilon_spec ⟨_, hC₁⟩
  have hA : ∀ y : F.complexSubmodule,
      e'.ρ (complexification T₀ ⟨e.σ y, e.σ_complex _ y.2⟩ : S'.index → ComplexMatrix2) =
        (complexification (liftLinear e e' T₀) y : F'.index → ComplexMatrix2) := by
    intro y
    obtain ⟨⟨p, q⟩, hp, -⟩ := hF y
    have hs := hC ⟨e.σ p, e.σ_real _ p.2⟩ ⟨e.σ q, e.σ_real _ q.2⟩ ⟨e.σ y, e.σ_complex _ y.2⟩
      (by simp [hp])
    rw [hs, map_add, map_smul, h1 p q y hp]
    rfl
  obtain ⟨T', hT', uniq⟩ := hT _ h2
  have hĈ : IsTransposeMap (complexification (liftLinear e e' T₀))
      (transposeMap (complexification (liftLinear e e' T₀))) := Classical.epsilon_spec ⟨T', hT'⟩
  have hD₁ : IsTransposeMap (complexification T₀)
      (pullLinear e' e (transposeMap (complexification (liftLinear e e' T₀)))) := by
    intro a b _
    change S.pair (e.σ _) _ = _
    rw [e.pair_eq, e.ρ_σ, hĈ _ ⟨e.ρ b, e.ρ_complex _ b.2⟩ (e.finiteTarget _), e'.pair_eq, ← hA]
    have h : (⟨e.σ (e.ρ b), e.σ_complex _ (e.ρ_complex _ b.2)⟩ : S.complexSubmodule) = b :=
      Subtype.ext (e.σ_ρ _ b.2)
    simp only [h]
  have hD : IsTransposeMap (complexification T₀) (transposeMap (complexification T₀)) :=
    Classical.epsilon_spec ⟨_, hD₁⟩
  have hQ : ∀ y : F'.complexSubmodule,
      e.ρ (transposeMap (complexification T₀) ⟨e'.σ y, e'.σ_complex _ y.2⟩ :
        S.index → ComplexMatrix2) =
        (transposeMap (complexification (liftLinear e e' T₀)) y : F.index → ComplexMatrix2) := by
    intro y
    have hq := uniq (fun y => ⟨e.ρ (transposeMap (complexification T₀)
      ⟨e'.σ y, e'.σ_complex _ y.2⟩ : S.index → ComplexMatrix2),
        e.ρ_complex _ (Subtype.property _)⟩) (by
        intro a b _
        have h := hD ⟨e'.σ a, e'.σ_complex _ a.2⟩ ⟨e.σ b, e.σ_complex _ b.2⟩ (e.finiteSource _)
        rw [e.pair_eq, e'.pair_eq] at h
        simp only [e.ρ_σ, e'.ρ_σ, hA] at h
        exact h)
    have hq' := uniq _ hĈ
    exact congrArg Subtype.val ((congrFun hq y).trans (congrFun hq' y).symm)
  have hR₁ : IsRealTransposeMap T₀
      (pullRealLinear e' e (realTransposeMap (liftLinear e e' T₀))) := by
    intro a h hh
    have h5 := h4 ⟨e'.ρ a, e'.ρ_real _ a.2⟩
      ⟨e'.ρ a, e'.ρ_complex _ (e'.real_mem_complex _ a.2)⟩ rfl
    change e.σ _ = _
    rw [h5, ← hQ, e.σ_ρ _ (Subtype.property _)]
    have h6 : (⟨e'.σ (e'.ρ a), e'.σ_complex _ (e'.ρ_complex _ (e'.real_mem_complex _ a.2))⟩ :
        S'.complexSubmodule) = h :=
      Subtype.ext (by rw [hh]; exact e'.σ_ρ _ (e'.real_mem_complex _ a.2))
    simp only [h6]
  have hRR : IsRealTransposeMap T₀ (realTransposeMap T₀) := Classical.epsilon_spec ⟨_, hR₁⟩
  have e1 := hRR g ⟨g, e'.real_mem_complex _ g.2⟩ rfl
  have e2 := hD ⟨g, e'.real_mem_complex _ g.2⟩ ⟨f, e.real_mem_complex _ f.2⟩ (e.finiteSource _)
  have e3 := hC f 0 ⟨f, e.real_mem_complex _ f.2⟩ (by simp)
  simp only [map_zero, ZeroMemClass.coe_zero, smul_zero, add_zero] at e3
  rw [e1]
  rw [e3] at e2
  exact e2
section Levels
variable {L n k j : ℕ}
abbrev PositiveEdgeIndex (L n k j : ℕ) : Type := ↥(univ : Set (PositiveEdge L n k j))
theorem isPositive_or_opposite (b : Edge L n k j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
theorem not_isPositive_opposite (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) (b : Edge L n k j)
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_not_both_positive <;> assumption
theorem opposite_opposite (b : Edge L n k j) : b.opposite.opposite = b := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_opposite_opposite <;> assumption
def restrictPositive :
    (Edge L n k j → ComplexMatrix2) →ₗ[ℂ] (PositiveEdgeIndex L n k j → ComplexMatrix2) where
  toFun B b := B b.1.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
open Classical in
def extendOdd :
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
theorem extendOdd_of_positive (f : PositiveEdgeIndex L n k j → ComplexMatrix2) (b : Edge L n k j)
    (h : b.IsPositivelyOriented) : extendOdd f b = f ⟨⟨b, h⟩, trivial⟩ := by
  simp [extendOdd, h]
theorem extendOdd_of_negative (f : PositiveEdgeIndex L n k j → ComplexMatrix2) (b : Edge L n k j)
    (h : ¬ b.IsPositivelyOriented) (h' : b.opposite.IsPositivelyOriented) :
    extendOdd f b = -f ⟨⟨b.opposite, h'⟩, trivial⟩ := by
  simp [extendOdd, h, h']
theorem isBondForm_extendOdd (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k)
    {𝔥 : Set ComplexMatrix2} {f : PositiveEdgeIndex L n k j → ComplexMatrix2}
    (h : ∀ b, f b ∈ 𝔥) : PeriodicLattice.IsBondForm 𝔥 (extendOdd f) := by
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · rw [extendOdd_of_positive f b hb]
    exact h _
  · by_cases hb : b.IsPositivelyOriented
    · have h' := not_isPositive_opposite hA hL hn hj b hb
      have h'' : b.opposite.opposite.IsPositivelyOriented := by rwa [opposite_opposite]
      rw [extendOdd_of_negative f _ h' h'', extendOdd_of_positive f b hb]
      simp only [opposite_opposite]
    · have h' := (isPositive_or_opposite b).resolve_left hb
      rw [extendOdd_of_negative f b hb h', extendOdd_of_positive f _ h', neg_neg]
def transportForms (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k)
    (hfin : Finite (PositiveEdge L n k j)) :
    Transport (edgePairedSpace L n k j) (pairedFunctions (PositiveEdgeIndex L n k j)) where
  ρ := restrictPositive
  σ := extendOdd
  ρ_σ f := by
    funext b
    exact extendOdd_of_positive f b.1.1 b.1.2
  σ_ρ h hh := by
    funext b
    by_cases hb : b.IsPositivelyOriented
    · exact extendOdd_of_positive _ b hb
    · have h' := (isPositive_or_opposite b).resolve_left hb
      refine (extendOdd_of_negative _ b hb h').trans ?_
      change -h b.opposite = h b
      rw [hh.2 b, neg_neg]
  ρ_real x hx := fun b _ => hx.1 b.1.1 b.1.2
  σ_real y hy := isBondForm_extendOdd hA hL hn hj fun b => hy b trivial
  ρ_complex x hx := fun b _ => hx.1 b.1.1 b.1.2
  σ_complex y hy := isBondForm_extendOdd hA hL hn hj fun b => hy b trivial
  real_mem_complex x hx := ⟨fun b hb => (hx.1 b hb).2, hx.2⟩
  pair_eq x y := by
    change traceFinsumPairing _ _ = traceFinsumPairing _ _
    unfold YangMills.Construction.Tower.traceFinsumPairing
    exact (finsum_comp_equiv (Equiv.Set.univ (PositiveEdge L n k j))
      (f := fun b => ComplexMatrix2.halfTrace
        (restrictToPositiveEdges x b * restrictToPositiveEdges y b))).symm
  finiteSource x := Set.toFinite _
  finiteTarget y := Set.toFinite _
end Levels
def transportFunctions (ι : Type) [Finite ι] :
    Transport (pairedFunctions ι) (pairedFunctions ↥(univ : Set ι)) where
  ρ := { toFun := fun f b => f b.1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  σ := { toFun := fun f x => f ⟨x, trivial⟩, map_add' := fun _ _ => rfl,
         map_smul' := fun _ _ => rfl }
  ρ_σ _ := rfl
  σ_ρ _ _ := rfl
  ρ_real _ hx := fun b _ => hx b.1 trivial
  σ_real _ hy := fun x _ => hy ⟨x, trivial⟩ trivial
  ρ_complex _ hx := fun b _ => hx b.1 trivial
  σ_complex _ hy := fun x _ => hy ⟨x, trivial⟩ trivial
  real_mem_complex _ hx := fun b _ => (hx b trivial).2
  pair_eq x y := by
    change traceFinsumPairing _ _ = traceFinsumPairing _ _
    unfold YangMills.Construction.Tower.traceFinsumPairing
    exact (finsum_comp_equiv (Equiv.Set.univ ι)
      (f := fun b => ComplexMatrix2.halfTrace (x b * y b))).symm
  finiteSource _ := Set.toFinite _
  finiteTarget _ := Set.toFinite _
theorem realTransposeFaceFunctionPairing_holds (hChart : LeftChartFields.Claim)
    (hReal : RealTransposesExist)
    (hLat : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hSums : FaceSums.FacesAndPairings) : RealTransposeFaceFunctionPairing := by
  intro L n k a b hL hn ha hb T₀ g f
  have hAa := (hChart.2.2 L k a hL ha).1 n hn
  have hplaq := ((hSums L hL k b hb).1 n hn).2.2.2 univ
  have hfinP : Finite (Face L n k b) := Set.finite_univ_iff.mp hplaq.2.1
  have ea := transportForms hLat hL hn ha hAa.2.1.1
  have eb := transportFunctions (Face L n k b)
  have hR : PairedFunctionSpace.AdmitsRealTransposes (pairedFunctions (PositiveEdgeIndex L n k a))
      (pairedFunctions ↥(univ : Set (Face L n k b))) :=
    (hReal L k hL).1 n hn (.edges a ha univ) (.faces b hb univ)
  have hT : LeftChartFields.HasUniqueTranspose (pairedFunctions (PositiveEdgeIndex L n k a))
      (pairedFunctions ↥(univ : Set (Face L n k b))) :=
    (hAa.2.2 (.edges a ha univ) (.faces b hb univ)).1
  exact pair_realTransposeMap_of_transport ea eb hR hT T₀ g f
end YangMills.Construction.Tower.TransposeIntoFaces
end
