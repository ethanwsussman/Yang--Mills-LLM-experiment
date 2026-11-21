import YangMills.Construction.Towers.CovariantAveragesAtTheTrivialConfigurationProof
import YangMills.Construction.Towers.MultiplierPairingOfTheChain
import YangMills.Construction.Towers.TheCriticalBranch
import YangMills.Construction.Towers.TransposesOfRealLinearMaps
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.ChainMultiplierPairingProof
open LeftChartFields PairedFunctionSpace
structure Transport (S F : PairedFunctionSpace) where
  fwd : (S.index → Matrices.ComplexMatrix2) →ₗ[ℂ] (F.index → Matrices.ComplexMatrix2)
  bwd : (F.index → Matrices.ComplexMatrix2) →ₗ[ℂ] (S.index → Matrices.ComplexMatrix2)
  fwd_bwd : ∀ f, fwd (bwd f) = f
  bwd_fwd : ∀ h ∈ S.complexSubmodule, bwd (fwd h) = h
  fwd_real : ∀ x ∈ S.realSubmodule, fwd x ∈ F.realSubmodule
  bwd_real : ∀ y ∈ F.realSubmodule, bwd y ∈ S.realSubmodule
  fwd_complex : ∀ x ∈ S.complexSubmodule, fwd x ∈ F.complexSubmodule
  bwd_complex : ∀ y ∈ F.complexSubmodule, bwd y ∈ S.complexSubmodule
  real_sub : ∀ x ∈ S.realSubmodule, x ∈ S.complexSubmodule
  pair_eq : ∀ x y, S.pair x y = F.pair (fwd x) (fwd y)
  finSupp : ∀ x, S.IsFinitelySupported x
  finSupp' : ∀ y, F.IsFinitelySupported y
variable {S F S' F' : PairedFunctionSpace}
def transportLinear (e : Transport S F) (e' : Transport S' F')
    (T₀ : S.realSubmodule →ₗ[ℝ] S'.realSubmodule) :
    F.realSubmodule →ₗ[ℝ] F'.realSubmodule where
  toFun f := ⟨e'.fwd (T₀ ⟨e.bwd f, e.bwd_real _ f.2⟩), e'.fwd_real _ (T₀ _).2⟩
  map_add' f g := by
    have h : (⟨e.bwd (f + g : F.realSubmodule), e.bwd_real _ (f + g).2⟩ : S.realSubmodule) =
        ⟨e.bwd f, e.bwd_real _ f.2⟩ + ⟨e.bwd g, e.bwd_real _ g.2⟩ :=
      Subtype.ext (by simp)
    apply Subtype.ext
    simp only [h, map_add]
    simp
  map_smul' c f := by
    have h : (⟨e.bwd (c • f : F.realSubmodule), e.bwd_real _ (c • f).2⟩ : S.realSubmodule) =
        c • ⟨e.bwd f, e.bwd_real _ f.2⟩ :=
      Subtype.ext (by simp)
    apply Subtype.ext
    simp only [h, map_smul, RingHom.id_apply]
    simp
def pullbackLinear (e : Transport S F) (e' : Transport S' F')
    (T : F.complexSubmodule →ₗ[ℂ] F'.complexSubmodule) :
    S.complexSubmodule →ₗ[ℂ] S'.complexSubmodule where
  toFun h := ⟨e'.bwd (T ⟨e.fwd h, e.fwd_complex _ h.2⟩), e'.bwd_complex _ (T _).2⟩
  map_add' f g := by
    have h : (⟨e.fwd (f + g : S.complexSubmodule), e.fwd_complex _ (f + g).2⟩ :
        F.complexSubmodule) =
        ⟨e.fwd f, e.fwd_complex _ f.2⟩ + ⟨e.fwd g, e.fwd_complex _ g.2⟩ :=
      Subtype.ext (by simp)
    apply Subtype.ext
    simp only [h, map_add]
    simp
  map_smul' c f := by
    have h : (⟨e.fwd (c • f : S.complexSubmodule), e.fwd_complex _ (c • f).2⟩ :
        F.complexSubmodule) =
        c • ⟨e.fwd f, e.fwd_complex _ f.2⟩ :=
      Subtype.ext (by simp)
    apply Subtype.ext
    simp only [h, map_smul, RingHom.id_apply]
    simp
def pullbackRealLinear (e : Transport S F) (e' : Transport S' F')
    (T : F.realSubmodule →ₗ[ℝ] F'.realSubmodule) :
    S.realSubmodule →ₗ[ℝ] S'.realSubmodule where
  toFun h := ⟨e'.bwd (T ⟨e.fwd h, e.fwd_real _ h.2⟩), e'.bwd_real _ (T _).2⟩
  map_add' f g := by
    have h : (⟨e.fwd (f + g : S.realSubmodule), e.fwd_real _ (f + g).2⟩ : F.realSubmodule) =
        ⟨e.fwd f, e.fwd_real _ f.2⟩ + ⟨e.fwd g, e.fwd_real _ g.2⟩ :=
      Subtype.ext (by simp)
    apply Subtype.ext
    simp only [h, map_add]
    simp
  map_smul' c f := by
    have h : (⟨e.fwd (c • f : S.realSubmodule), e.fwd_real _ (c • f).2⟩ : F.realSubmodule) =
        c • ⟨e.fwd f, e.fwd_real _ f.2⟩ :=
      Subtype.ext (by simp)
    apply Subtype.ext
    simp only [h, map_smul, RingHom.id_apply]
    simp
theorem transportLinear_fwd (e : Transport S F) (e' : Transport S' F')
    (T₀ : S.realSubmodule →ₗ[ℝ] S'.realSubmodule) (f : S.realSubmodule) :
    (transportLinear e e' T₀ ⟨e.fwd f, e.fwd_real _ f.2⟩ : F'.index → Matrices.ComplexMatrix2) =
      e'.fwd (T₀ f) := by
  have h : (⟨e.bwd (e.fwd f), e.bwd_real _ (e.fwd_real _ f.2)⟩ : S.realSubmodule) = f :=
    Subtype.ext (e.bwd_fwd _ (e.real_sub _ f.2))
  change e'.fwd (T₀ ⟨e.bwd (e.fwd f), _⟩ : S'.index → Matrices.ComplexMatrix2) = _
  rw [h]
theorem pair_realTransposeMap (e : Transport S F) (e' : Transport S' F')
    (hR : AdmitsRealTransposes F F') (hT : HasUniqueTranspose F F')
    (T₀ : S.realSubmodule →ₗ[ℝ] S'.realSubmodule) (g : S'.realSubmodule) (f : S.realSubmodule) :
    S.pair (realTransposeMap T₀ g) f = S'.pair g (T₀ f) := by
  obtain ⟨hF, hR'⟩ := hR
  obtain ⟨h1, h2, -, h4, -, -⟩ := hR' (transportLinear e e' T₀) fun _ _ => e'.finSupp' _
  have hC₁ : IsComplexification T₀
      (pullbackLinear e e' (complexification (transportLinear e e' T₀))) := by
    intro a b h hh
    have hρ := h1 ⟨e.fwd a, e.fwd_real _ a.2⟩ ⟨e.fwd b, e.fwd_real _ b.2⟩
      ⟨e.fwd h, e.fwd_complex _ h.2⟩ (by simp [hh])
    change e'.bwd _ = _
    rw [hρ, map_add, map_smul, transportLinear_fwd, transportLinear_fwd,
      e'.bwd_fwd _ (e'.real_sub _ (T₀ a).2), e'.bwd_fwd _ (e'.real_sub _ (T₀ b).2)]
  have hC : IsComplexification T₀ (complexification T₀) := Classical.epsilon_spec ⟨_, hC₁⟩
  have hA : ∀ y : F.complexSubmodule,
      e'.fwd (complexification T₀ ⟨e.bwd y, e.bwd_complex _ y.2⟩ :
        S'.index → Matrices.ComplexMatrix2) =
        (complexification (transportLinear e e' T₀) y : F'.index → Matrices.ComplexMatrix2) := by
    intro y
    obtain ⟨⟨p, q⟩, hp, -⟩ := hF y
    have hs := hC ⟨e.bwd p, e.bwd_real _ p.2⟩ ⟨e.bwd q, e.bwd_real _ q.2⟩
      ⟨e.bwd y, e.bwd_complex _ y.2⟩ (by simp [hp])
    rw [hs, map_add, map_smul, h1 p q y hp]
    rfl
  obtain ⟨T', hT', uniq⟩ := hT _ h2
  have hĈ : IsTransposeMap (complexification (transportLinear e e' T₀))
      (transposeMap (complexification (transportLinear e e' T₀))) :=
    Classical.epsilon_spec ⟨T', hT'⟩
  have hD₁ : IsTransposeMap (complexification T₀)
      (pullbackLinear e' e (transposeMap (complexification (transportLinear e e' T₀)))) := by
    intro a b _
    change S.pair (e.bwd _) _ = _
    rw [e.pair_eq, e.fwd_bwd, hĈ _ ⟨e.fwd b, e.fwd_complex _ b.2⟩ (e.finSupp' _), e'.pair_eq,
      ← hA]
    have h : (⟨e.bwd (e.fwd b), e.bwd_complex _ (e.fwd_complex _ b.2)⟩ : S.complexSubmodule) =
        b := Subtype.ext (e.bwd_fwd _ b.2)
    simp only [h]
  have hD : IsTransposeMap (complexification T₀) (transposeMap (complexification T₀)) :=
    Classical.epsilon_spec ⟨_, hD₁⟩
  have hQ : ∀ y : F'.complexSubmodule,
      e.fwd (transposeMap (complexification T₀) ⟨e'.bwd y, e'.bwd_complex _ y.2⟩ :
        S.index → Matrices.ComplexMatrix2) =
        (transposeMap (complexification (transportLinear e e' T₀)) y :
          F.index → Matrices.ComplexMatrix2) := by
    intro y
    have hq := uniq (fun y => ⟨e.fwd (transposeMap (complexification T₀)
      ⟨e'.bwd y, e'.bwd_complex _ y.2⟩ : S.index → Matrices.ComplexMatrix2),
        e.fwd_complex _ (Subtype.property _)⟩) (by
        intro a b _
        have h := hD ⟨e'.bwd a, e'.bwd_complex _ a.2⟩ ⟨e.bwd b, e.bwd_complex _ b.2⟩
          (e.finSupp _)
        rw [e.pair_eq, e'.pair_eq] at h
        simp only [e.fwd_bwd, e'.fwd_bwd, hA] at h
        exact h)
    have hq' := uniq _ hĈ
    exact congrArg Subtype.val ((congrFun hq y).trans (congrFun hq' y).symm)
  have hR₁ : IsRealTransposeMap T₀
      (pullbackRealLinear e' e (realTransposeMap (transportLinear e e' T₀))) := by
    intro a h hh
    have h5 := h4 ⟨e'.fwd a, e'.fwd_real _ a.2⟩ ⟨e'.fwd a, e'.fwd_complex _ (e'.real_sub _ a.2)⟩
      rfl
    change e.bwd _ = _
    rw [h5, ← hQ, e.bwd_fwd _ (Subtype.property _)]
    have h6 : (⟨e'.bwd (e'.fwd a), e'.bwd_complex _ (e'.fwd_complex _ (e'.real_sub _ a.2))⟩ :
        S'.complexSubmodule) = h :=
      Subtype.ext (by rw [hh]; exact e'.bwd_fwd _ (e'.real_sub _ a.2))
    simp only [h6]
  have hRR : IsRealTransposeMap T₀ (realTransposeMap T₀) := Classical.epsilon_spec ⟨_, hR₁⟩
  have e1 := hRR g ⟨g, e'.real_sub _ g.2⟩ rfl
  have e2 := hD ⟨g, e'.real_sub _ g.2⟩ ⟨f, e.real_sub _ f.2⟩ (e.finSupp _)
  have e3 := hC f 0 ⟨f, e.real_sub _ f.2⟩ (by simp)
  simp only [map_zero, ZeroMemClass.coe_zero, smul_zero, add_zero] at e3
  rw [e1]
  rw [e3] at e2
  exact e2
section Edges
variable {L n k j : ℕ}
abbrev PositiveEdgeIndex (L n k j : ℕ) : Type := ↥(univ : Set (PositiveEdge L n k j))
theorem isPositivelyOriented_or_opposite (b : Edge L n k j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
theorem not_isPositivelyOriented_opposite (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) (b : Edge L n k j)
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_not_both_positive <;> assumption
theorem opposite_opposite (b : Edge L n k j) : b.opposite.opposite = b := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_opposite_opposite <;> assumption
def restrictPositive :
    (Edge L n k j → Matrices.ComplexMatrix2) →ₗ[ℂ]
      (PositiveEdgeIndex L n k j → Matrices.ComplexMatrix2) where
  toFun B b := B b.1.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
open Classical in
def oddExtension :
    (PositiveEdgeIndex L n k j → Matrices.ComplexMatrix2) →ₗ[ℂ]
      (Edge L n k j → Matrices.ComplexMatrix2) where
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
theorem oddExtension_of_pos (f : PositiveEdgeIndex L n k j → Matrices.ComplexMatrix2)
    (b : Edge L n k j) (h : b.IsPositivelyOriented) :
    oddExtension f b = f ⟨⟨b, h⟩, trivial⟩ := by
  simp [oddExtension, h]
theorem oddExtension_of_neg (f : PositiveEdgeIndex L n k j → Matrices.ComplexMatrix2)
    (b : Edge L n k j) (h : ¬ b.IsPositivelyOriented) (h' : b.opposite.IsPositivelyOriented) :
    oddExtension f b = -f ⟨⟨b.opposite, h'⟩, trivial⟩ := by
  simp [oddExtension, h, h']
theorem isBondForm_oddExtension (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k)
    {𝔥 : Set Matrices.ComplexMatrix2}
    {f : PositiveEdgeIndex L n k j → Matrices.ComplexMatrix2} (h : ∀ b, f b ∈ 𝔥) :
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
def edgeFormsTransport (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k)
    (hfin : Finite (PositiveEdge L n k j)) :
    Transport (edgePairedSpace L n k j) (pairedFunctions (PositiveEdgeIndex L n k j)) where
  fwd := restrictPositive
  bwd := oddExtension
  fwd_bwd f := by
    funext b
    exact oddExtension_of_pos f b.1.1 b.1.2
  bwd_fwd h hh := by
    funext b
    by_cases hb : b.IsPositivelyOriented
    · exact oddExtension_of_pos _ b hb
    · have h' := (isPositivelyOriented_or_opposite b).resolve_left hb
      refine (oddExtension_of_neg _ b hb h').trans ?_
      change -h b.opposite = h b
      rw [hh.2 b, neg_neg]
  fwd_real x hx := fun b _ => hx.1 b.1.1 b.1.2
  bwd_real y hy := isBondForm_oddExtension hA hL hn hj fun b => hy b trivial
  fwd_complex x hx := fun b _ => hx.1 b.1.1 b.1.2
  bwd_complex y hy := isBondForm_oddExtension hA hL hn hj fun b => hy b trivial
  real_sub x hx := ⟨fun b hb => (hx.1 b hb).2, hx.2⟩
  pair_eq x y := by
    change traceFinsumPairing _ _ = traceFinsumPairing _ _
    unfold YangMills.Construction.Tower.traceFinsumPairing
    exact (finsum_comp_equiv (Equiv.Set.univ (PositiveEdge L n k j))
      (f := fun b => Matrices.ComplexMatrix2.halfTrace
        (restrictToPositiveEdges x b * restrictToPositiveEdges y b))).symm
  finSupp x := Set.toFinite _
  finSupp' y := Set.toFinite _
end Edges
end YangMills.Construction.Tower.ChainMultiplierPairingProof
namespace YangMills.Construction
open Tower Tower.ChainMultiplierPairingProof in
theorem Tower.ChainMultiplierPairing.statement_holds (hBranch : Tower.CriticalBranchExists)
    (hChart : Tower.LeftChartFields.Claim)
    (hReal : Tower.RealTransposesExist)
    (hLat : QuotientLattices.TorusAndSpaceLatticeProperties) :
    Tower.ChainMultiplierPairing.Statement := by
  intro L n k hL hn _
  have hb : (chosenCriticalBranch L n k).IsCritical :=
    Classical.epsilon_spec (hBranch L n k hL hn)
  refine Filter.Eventually.mono (hb.prolongComp_section k le_rfl) ?_
  rintro W ⟨-, -, g, hg, hrel⟩ ξ
  have hU : chainBottom W = (chosenCriticalBranch L n k).prolongComp k W := chainBottom_eq W
  have hA₀ := (hChart.2.2 L k 0 hL (Nat.zero_le k)).1 n hn
  have hAk := (hChart.2.2 L k k hL le_rfl).1 n hn
  have e₀ := edgeFormsTransport hLat hL hn (Nat.zero_le k) hA₀.2.1.1
  have eₖ := edgeFormsTransport hLat hL hn (le_refl k) hAk.2.1.1
  have hR : PairedFunctionSpace.AdmitsRealTransposes (pairedFunctions (PositiveEdgeIndex L n k 0))
      (pairedFunctions (PositiveEdgeIndex L n k k)) :=
    (hReal L k hL).1 n hn (.edges 0 (Nat.zero_le k) univ) (.edges k le_rfl univ)
  have hT : LeftChartFields.HasUniqueTranspose (pairedFunctions (PositiveEdgeIndex L n k 0))
      (pairedFunctions (PositiveEdgeIndex L n k k)) :=
    (hA₀.2.2 (.edges 0 (Nat.zero_le k) univ) (.edges k le_rfl univ)).1
  have key := pair_realTransposeMap e₀ eₖ hR hT
    (leftDifferentialLinear (smoothingIter L n k k)
      ((chosenCriticalBranch L n k).prolongComp k W)) g ξ
  rw [← hg]
  unfold topConstraintMap smoothingIterDifferential
  rw [hU, ← hrel]
  exact key
end YangMills.Construction
end
