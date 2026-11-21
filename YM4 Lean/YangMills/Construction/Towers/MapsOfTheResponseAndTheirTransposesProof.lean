import YangMills.Construction.RunningCouplingSlope.NormsOfThePlainProductsProof
import YangMills.Construction.Towers.BackgroundFormOfTheFunctionalOnASideProof
import YangMills.Construction.Towers.LinearMapsAreOnto
import YangMills.Construction.Towers.MapsOfTheResponseAndTheirTransposes
import YangMills.Construction.Towers.PairingOfTheRealTransposeOnForms
import YangMills.Construction.Towers.QuadraticFormOfAStepOfTheBranchProof
import YangMills.Construction.Towers.TransposesOfRealLinearMaps
import YangMills.Construction.Towers.ValuesOfTheLinearMapsAtTheTrivialConfiguration
import Mathlib
set_option autoImplicit false
open Set
namespace YangMills.Construction.Tower.ResponseMaps
noncomputable section
open LeftChartFields PairedFunctionSpace
structure PairedEquiv (S F : PairedFunctionSpace) where
  fwd : (S.index → Matrices.ComplexMatrix2) →ₗ[ℂ] (F.index → Matrices.ComplexMatrix2)
  bwd : (F.index → Matrices.ComplexMatrix2) →ₗ[ℂ] (S.index → Matrices.ComplexMatrix2)
  fwd_bwd : ∀ f, fwd (bwd f) = f
  bwd_fwd : ∀ h ∈ S.complexSubmodule, bwd (fwd h) = h
  fwd_real : ∀ x ∈ S.realSubmodule, fwd x ∈ F.realSubmodule
  bwd_real : ∀ y ∈ F.realSubmodule, bwd y ∈ S.realSubmodule
  fwd_complex : ∀ x ∈ S.complexSubmodule, fwd x ∈ F.complexSubmodule
  bwd_complex : ∀ y ∈ F.complexSubmodule, bwd y ∈ S.complexSubmodule
  real_le : ∀ x ∈ S.realSubmodule, x ∈ S.complexSubmodule
  pair_eq : ∀ x y, S.pair x y = F.pair (fwd x) (fwd y)
  finite_src : ∀ x, S.IsFinitelySupported x
  finite_tgt : ∀ y, F.IsFinitelySupported y
variable {S F S' F' : PairedFunctionSpace}
def liftReal (e : PairedEquiv S F) (e' : PairedEquiv S' F')
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
def pullComplex (e : PairedEquiv S F) (e' : PairedEquiv S' F')
    (T : F.complexSubmodule →ₗ[ℂ] F'.complexSubmodule) :
    S.complexSubmodule →ₗ[ℂ] S'.complexSubmodule where
  toFun h := ⟨e'.bwd (T ⟨e.fwd h, e.fwd_complex _ h.2⟩), e'.bwd_complex _ (T _).2⟩
  map_add' f g := by
    have h : (⟨e.fwd (f + g : S.complexSubmodule), e.fwd_complex _ (f + g).2⟩ :
        F.complexSubmodule) = ⟨e.fwd f, e.fwd_complex _ f.2⟩ + ⟨e.fwd g, e.fwd_complex _ g.2⟩ :=
      Subtype.ext (by simp)
    apply Subtype.ext
    simp only [h, map_add]
    simp
  map_smul' c f := by
    have h : (⟨e.fwd (c • f : S.complexSubmodule), e.fwd_complex _ (c • f).2⟩ :
        F.complexSubmodule) = c • ⟨e.fwd f, e.fwd_complex _ f.2⟩ :=
      Subtype.ext (by simp)
    apply Subtype.ext
    simp only [h, map_smul, RingHom.id_apply]
    simp
def pullReal (e : PairedEquiv S F) (e' : PairedEquiv S' F')
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
theorem liftReal_fwd (e : PairedEquiv S F) (e' : PairedEquiv S' F')
    (T₀ : S.realSubmodule →ₗ[ℝ] S'.realSubmodule) (f : S.realSubmodule) :
    (liftReal e e' T₀ ⟨e.fwd f, e.fwd_real _ f.2⟩ : F'.index → Matrices.ComplexMatrix2) =
      e'.fwd (T₀ f) := by
  have h : (⟨e.bwd (e.fwd f), e.bwd_real _ (e.fwd_real _ f.2)⟩ : S.realSubmodule) = f :=
    Subtype.ext (e.bwd_fwd _ (e.real_le _ f.2))
  change e'.fwd (T₀ ⟨e.bwd (e.fwd f), _⟩ : S'.index → Matrices.ComplexMatrix2) = _
  rw [h]
theorem pair_realTransposeMap (e : PairedEquiv S F) (e' : PairedEquiv S' F')
    (hR : AdmitsRealTransposes F F') (hT : HasUniqueTranspose F F')
    (T₀ : S.realSubmodule →ₗ[ℝ] S'.realSubmodule) (g : S'.realSubmodule) (f : S.realSubmodule) :
    S.pair (realTransposeMap T₀ g) f = S'.pair g (T₀ f) := by
  obtain ⟨hF, hR'⟩ := hR
  obtain ⟨h1, h2, -, h4, -, -⟩ := hR' (liftReal e e' T₀) fun _ _ => e'.finite_tgt _
  have hC₁ : IsComplexification T₀ (pullComplex e e' (complexification (liftReal e e' T₀))) := by
    intro a b h hh
    have hρ := h1 ⟨e.fwd a, e.fwd_real _ a.2⟩ ⟨e.fwd b, e.fwd_real _ b.2⟩
      ⟨e.fwd h, e.fwd_complex _ h.2⟩ (by simp [hh])
    change e'.bwd _ = _
    rw [hρ, map_add, map_smul, liftReal_fwd, liftReal_fwd,
      e'.bwd_fwd _ (e'.real_le _ (T₀ a).2), e'.bwd_fwd _ (e'.real_le _ (T₀ b).2)]
  have hC : IsComplexification T₀ (complexification T₀) := Classical.epsilon_spec ⟨_, hC₁⟩
  have hA : ∀ y : F.complexSubmodule,
      e'.fwd (complexification T₀ ⟨e.bwd y, e.bwd_complex _ y.2⟩ :
        S'.index → Matrices.ComplexMatrix2) =
        (complexification (liftReal e e' T₀) y : F'.index → Matrices.ComplexMatrix2) := by
    intro y
    obtain ⟨⟨p, q⟩, hp, -⟩ := hF y
    have hs := hC ⟨e.bwd p, e.bwd_real _ p.2⟩ ⟨e.bwd q, e.bwd_real _ q.2⟩
      ⟨e.bwd y, e.bwd_complex _ y.2⟩ (by simp [hp])
    rw [hs, map_add, map_smul, h1 p q y hp]
    rfl
  obtain ⟨T', hT', uniq⟩ := hT _ h2
  have hĈ : IsTransposeMap (complexification (liftReal e e' T₀))
      (transposeMap (complexification (liftReal e e' T₀))) := Classical.epsilon_spec ⟨T', hT'⟩
  have hD₁ : IsTransposeMap (complexification T₀)
      (pullComplex e' e (transposeMap (complexification (liftReal e e' T₀)))) := by
    intro a b _
    change S.pair (e.bwd _) _ = _
    rw [e.pair_eq, e.fwd_bwd, hĈ _ ⟨e.fwd b, e.fwd_complex _ b.2⟩ (e.finite_tgt _), e'.pair_eq,
      ← hA]
    have h : (⟨e.bwd (e.fwd b), e.bwd_complex _ (e.fwd_complex _ b.2)⟩ : S.complexSubmodule) =
        b := Subtype.ext (e.bwd_fwd _ b.2)
    simp only [h]
  have hD : IsTransposeMap (complexification T₀) (transposeMap (complexification T₀)) :=
    Classical.epsilon_spec ⟨_, hD₁⟩
  have hQ : ∀ y : F'.complexSubmodule,
      e.fwd (transposeMap (complexification T₀) ⟨e'.bwd y, e'.bwd_complex _ y.2⟩ :
        S.index → Matrices.ComplexMatrix2) =
        (transposeMap (complexification (liftReal e e' T₀)) y :
          F.index → Matrices.ComplexMatrix2) := by
    intro y
    have hq := uniq (fun y => ⟨e.fwd (transposeMap (complexification T₀)
      ⟨e'.bwd y, e'.bwd_complex _ y.2⟩ : S.index → Matrices.ComplexMatrix2),
      e.fwd_complex _ (Subtype.property _)⟩) (by
        intro a b _
        have h := hD ⟨e'.bwd a, e'.bwd_complex _ a.2⟩ ⟨e.bwd b, e.bwd_complex _ b.2⟩
          (e.finite_src _)
        rw [e.pair_eq, e'.pair_eq] at h
        simp only [e.fwd_bwd, e'.fwd_bwd, hA] at h
        exact h)
    have hq' := uniq _ hĈ
    exact congrArg Subtype.val ((congrFun hq y).trans (congrFun hq' y).symm)
  have hR₁ : IsRealTransposeMap T₀ (pullReal e' e (realTransposeMap (liftReal e e' T₀))) := by
    intro a h hh
    have h5 := h4 ⟨e'.fwd a, e'.fwd_real _ a.2⟩
      ⟨e'.fwd a, e'.fwd_complex _ (e'.real_le _ a.2)⟩ rfl
    change e.bwd _ = _
    rw [h5, ← hQ, e.bwd_fwd _ (Subtype.property _)]
    have h6 : (⟨e'.bwd (e'.fwd a), e'.bwd_complex _ (e'.fwd_complex _ (e'.real_le _ a.2))⟩ :
        S'.complexSubmodule) = h :=
      Subtype.ext (by rw [hh]; exact e'.bwd_fwd _ (e'.real_le _ a.2))
    simp only [h6]
  have hRR : IsRealTransposeMap T₀ (realTransposeMap T₀) := Classical.epsilon_spec ⟨_, hR₁⟩
  have e1 := hRR g ⟨g, e'.real_le _ g.2⟩ rfl
  have e2 := hD ⟨g, e'.real_le _ g.2⟩ ⟨f, e.real_le _ f.2⟩ (e.finite_src _)
  have e3 := hC f 0 ⟨f, e.real_le _ f.2⟩ (by simp)
  simp only [map_zero, ZeroMemClass.coe_zero, smul_zero, add_zero] at e3
  rw [e1]
  rw [e3] at e2
  exact e2
section Tower
variable {L n k j : ℕ}
abbrev PosEdgeIndex (L n k j : ℕ) : Type := ↥(univ : Set (PositiveEdge L n k j))
theorem isPositivelyOriented_or_opposite (b : Edge L n k j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
theorem not_opposite_of_positive (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) (b : Edge L n k j)
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_not_both_positive <;> assumption
theorem opposite_opposite (b : Edge L n k j) : b.opposite.opposite = b := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_opposite_opposite <;> assumption
def toPositive :
    (Edge L n k j → Matrices.ComplexMatrix2) →ₗ[ℂ] (PosEdgeIndex L n k j → Matrices.ComplexMatrix2) where
  toFun B b := B b.1.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
open Classical in
def oddExtension :
    (PosEdgeIndex L n k j → Matrices.ComplexMatrix2) →ₗ[ℂ] (Edge L n k j → Matrices.ComplexMatrix2) where
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
theorem oddExtension_pos (f : PosEdgeIndex L n k j → Matrices.ComplexMatrix2) (b : Edge L n k j)
    (h : b.IsPositivelyOriented) : oddExtension f b = f ⟨⟨b, h⟩, trivial⟩ := by
  simp [oddExtension, h]
theorem oddExtension_neg (f : PosEdgeIndex L n k j → Matrices.ComplexMatrix2) (b : Edge L n k j)
    (h : ¬ b.IsPositivelyOriented) (h' : b.opposite.IsPositivelyOriented) :
    oddExtension f b = -f ⟨⟨b.opposite, h'⟩, trivial⟩ := by
  simp [oddExtension, h, h']
theorem isBondForm_oddExtension (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k)
    {𝔥 : Set Matrices.ComplexMatrix2} {f : PosEdgeIndex L n k j → Matrices.ComplexMatrix2}
    (h : ∀ b, f b ∈ 𝔥) : PeriodicLattice.IsBondForm 𝔥 (oddExtension f) := by
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · rw [oddExtension_pos f b hb]
    exact h _
  · by_cases hb : b.IsPositivelyOriented
    · have h' := not_opposite_of_positive hA hL hn hj b hb
      have h'' : b.opposite.opposite.IsPositivelyOriented := by rwa [opposite_opposite]
      rw [oddExtension_neg f _ h' h'', oddExtension_pos f b hb]
      simp only [opposite_opposite]
    · have h' := (isPositivelyOriented_or_opposite b).resolve_left hb
      rw [oddExtension_neg f b hb h', oddExtension_pos f _ h', neg_neg]
def edgeFormsEquiv (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k)
    (hfin : Finite (PositiveEdge L n k j)) :
    PairedEquiv (edgePairedSpace L n k j) (pairedFunctions (PosEdgeIndex L n k j)) where
  fwd := toPositive
  bwd := oddExtension
  fwd_bwd f := by
    funext b
    exact oddExtension_pos f b.1.1 b.1.2
  bwd_fwd h hh := by
    funext b
    by_cases hb : b.IsPositivelyOriented
    · exact oddExtension_pos _ b hb
    · have h' := (isPositivelyOriented_or_opposite b).resolve_left hb
      refine (oddExtension_neg _ b hb h').trans ?_
      change -h b.opposite = h b
      rw [hh.2 b, neg_neg]
  fwd_real x hx := fun b _ => hx.1 b.1.1 b.1.2
  bwd_real y hy := isBondForm_oddExtension hA hL hn hj fun b => hy b trivial
  fwd_complex x hx := fun b _ => hx.1 b.1.1 b.1.2
  bwd_complex y hy := isBondForm_oddExtension hA hL hn hj fun b => hy b trivial
  real_le x hx := ⟨fun b hb => (hx.1 b hb).2, hx.2⟩
  pair_eq x y := by
    change traceFinsumPairing _ _ = traceFinsumPairing _ _
    unfold traceFinsumPairing
    exact (finsum_comp_equiv (Equiv.Set.univ (PositiveEdge L n k j))
      (f := fun b => Matrices.ComplexMatrix2.halfTrace
        (restrictToPositiveEdges x b * restrictToPositiveEdges y b))).symm
  finite_src x := Set.toFinite _
  finite_tgt y := Set.toFinite _
end Tower
def univFunctionsEquiv (ι : Type) [Finite ι] :
    PairedEquiv (pairedFunctions ι) (pairedFunctions ↥(univ : Set ι)) where
  fwd := { toFun := fun f b => f b.1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  bwd := { toFun := fun f x => f ⟨x, trivial⟩, map_add' := fun _ _ => rfl,
           map_smul' := fun _ _ => rfl }
  fwd_bwd _ := rfl
  bwd_fwd _ _ := rfl
  fwd_real _ hx := fun b _ => hx b.1 trivial
  bwd_real _ hy := fun x _ => hy ⟨x, trivial⟩ trivial
  fwd_complex _ hx := fun b _ => hx b.1 trivial
  bwd_complex _ hy := fun x _ => hy ⟨x, trivial⟩ trivial
  real_le _ hx := fun b _ => (hx b trivial).2
  pair_eq x y := by
    change traceFinsumPairing _ _ = traceFinsumPairing _ _
    unfold traceFinsumPairing
    exact (finsum_comp_equiv (Equiv.Set.univ ι)
      (f := fun b => Matrices.ComplexMatrix2.halfTrace (x b * y b))).symm
  finite_src _ := Set.toFinite _
  finite_tgt _ := Set.toFinite _
section Step
variable {L n k j : ℕ}
theorem sumAlong_smul {m : ℕ} {i : ℤ} (r : ℝ)
    (A : PeriodicLattice.Bond L m i → Matrices.ComplexMatrix2)
    (Γ : List (PeriodicLattice.Bond L m i)) :
    PeriodicLattice.bondFormSumAlong (r • A) Γ = r • PeriodicLattice.bondFormSumAlong A Γ := by
  induction Γ with
  | nil => simp [PeriodicLattice.bondFormSumAlong]
  | cons b Γ ih =>
    simp only [PeriodicLattice.bondFormSumAlong, List.map_cons, List.sum_cons,
      Pi.smul_apply] at ih ⊢
    rw [ih, smul_add]
theorem contourFormAverage_smul {m : ℕ} {i i' : ℤ} (r : ℝ)
    (A : PeriodicLattice.Bond L m i' → Matrices.ComplexMatrix2)
    (y : PeriodicLattice.Site L m i) (x : PeriodicLattice.Site L m i') :
    PeriodicLattice.contourFormAverage (r • A) y x =
      r • PeriodicLattice.contourFormAverage A y x := by
  simp only [PeriodicLattice.contourFormAverage, sumAlong_smul, ← Finset.smul_sum]
  rw [smul_comm]
theorem finsum_mem_smul_real {α : Type*} (r : ℝ) (f : α → Matrices.ComplexMatrix2) {s : Set α}
    (hs : s.Finite) : ∑ᶠ x ∈ s, r • f x = r • ∑ᶠ x ∈ s, f x :=
  ((smulAddHom ℝ Matrices.ComplexMatrix2 r).map_finsum_mem f hs).symm
theorem linearSmoothing_add (hfin : Finite (Vertex L n k j))
    (A A' : Edge L n k j → Matrices.ComplexMatrix2) :
    linearSmoothing L n k j (A + A') = linearSmoothing L n k j A + linearSmoothing L n k j A' := by apply _root_.YangMills.Construction.Tower.StepQuadraticFormProof.linearSmoothing_add <;> assumption
theorem linearSmoothing_smul (hfin : Finite (Vertex L n k j)) (r : ℝ)
    (A : Edge L n k j → Matrices.ComplexMatrix2) :
    linearSmoothing L n k j (r • A) = r • linearSmoothing L n k j A := by
  funext c
  simp only [linearSmoothing, PeriodicLattice.scaledLinearBlockStep,
    PeriodicLattice.scaledLinearBlockAverage, PeriodicLattice.linearBlockSum, Pi.smul_apply]
  rw [smul_comm r, ← finsum_mem_smul_real _ _ (Set.toFinite _)]
  congr 1
  refine finsum_mem_congr rfl fun x _ => ?_
  rw [contourFormAverage_smul, sumAlong_smul, contourFormAverage_smul, smul_sub, smul_add]
theorem crossingSmoothing_add (hfin : Finite (Vertex L n k j))
    (A A' : Edge L n k j → Matrices.ComplexMatrix2) :
    crossingSmoothing L n k j (A + A') =
      crossingSmoothing L n k j A + crossingSmoothing L n k j A' := by apply _root_.YangMills.SharedProofs.p41844 <;> assumption
theorem crossingSmoothing_smul (hfin : Finite (Vertex L n k j)) (r : ℝ)
    (A : Edge L n k j → Matrices.ComplexMatrix2) :
    crossingSmoothing L n k j (r • A) = r • crossingSmoothing L n k j A := by
  funext c
  simp only [crossingSmoothing, edgeFormPathSum, Pi.smul_apply]
  rw [smul_comm r, ← finsum_mem_smul_real _ _ (Set.toFinite _)]
  congr 1
  exact finsum_mem_congr rfl fun x _ => sumAlong_smul _ _ _
theorem edgeForm_apply_mem {B : Edge L n k j → Matrices.ComplexMatrix2}
    (h : B ∈ edgeFormSpace L n k j) (b : Edge L n k j) :
    B b ∈ Matrices.ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.Construction.Tower.SmoothingIterProof.edgeForm_apply_mem <;> assumption
theorem edgeCoboundary_mem {B : Edge L n k j → Matrices.ComplexMatrix2}
    (h : B ∈ edgeFormSpace L n k j) : edgeCoboundary B ∈ faceFunctionSpace L n k j := fun _ _ =>
  Matrices.ComplexMatrix2.hermitianTraceless.sub_mem
    (Matrices.ComplexMatrix2.hermitianTraceless.sub_mem
      (Matrices.ComplexMatrix2.hermitianTraceless.add_mem (edgeForm_apply_mem h _)
        (edgeForm_apply_mem h _))
      (edgeForm_apply_mem h _)) (edgeForm_apply_mem h _)
end Step
section Iterates
variable {L n k : ℕ}
structure StepLinear
    (step : ∀ j, (Edge L n k j → Matrices.ComplexMatrix2) → Edge L n k (j + 1) →
      Matrices.ComplexMatrix2) : Prop where
  map_add : ∀ j, j + 1 ≤ k → ∀ A A', step j (A + A') = step j A + step j A'
  map_smul : ∀ j, j + 1 ≤ k → ∀ (r : ℝ) A, step j (r • A) = r • step j A
  maps_to : ∀ j, j + 1 ≤ k → ∀ B ∈ edgeFormSpace L n k j, step j B ∈ edgeFormSpace L n k (j + 1)
theorem StepLinear.iter
    {step : ∀ j, (Edge L n k j → Matrices.ComplexMatrix2) → Edge L n k (j + 1) →
      Matrices.ComplexMatrix2}
    (h : StepLinear step) (m : ℕ) (hm : m ≤ k) :
    (∀ B ∈ edgeFormSpace L n k 0,
      PeriodicLattice.iterateFromBare step m B ∈ edgeFormSpace L n k m) ∧
    (∀ A A', PeriodicLattice.iterateFromBare step m (A + A') =
      PeriodicLattice.iterateFromBare step m A + PeriodicLattice.iterateFromBare step m A') ∧
    ∀ (r : ℝ) A, PeriodicLattice.iterateFromBare step m (r • A) =
      r • PeriodicLattice.iterateFromBare step m A := by
  induction m with
  | zero => exact ⟨fun B hB => hB, fun _ _ => rfl, fun _ _ => rfl⟩
  | succ m ih =>
    obtain ⟨i₁, i₂, i₃⟩ := ih (by omega)
    refine ⟨fun B hB => h.maps_to m hm _ (i₁ B hB), fun A A' => ?_, fun r A => ?_⟩
    · change step m _ = step m _ + step m _
      rw [i₂, h.map_add m hm]
    · change step m _ = r • step m _
      rw [i₃, h.map_smul m hm]
theorem StepLinear.exists_linearMap
    {step : ∀ j, (Edge L n k j → Matrices.ComplexMatrix2) → Edge L n k (j + 1) →
      Matrices.ComplexMatrix2}
    (h : StepLinear step) :
    ∃ T : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k k, ∀ x : edgeFormSpace L n k 0,
      (T x : Edge L n k k → Matrices.ComplexMatrix2) = PeriodicLattice.iterateFromBare step k x := by
  obtain ⟨i₁, i₂, i₃⟩ := h.iter k le_rfl
  exact ⟨{ toFun := fun x => ⟨_, i₁ x x.2⟩
           map_add' := fun x y => Subtype.ext (i₂ x y)
           map_smul' := fun r x => Subtype.ext (i₃ r x) }, fun _ => rfl⟩
theorem linearMapWithValues_apply {α β : Type*} {p : Submodule ℝ (α → Matrices.ComplexMatrix2)}
    {p' : Submodule ℝ (β → Matrices.ComplexMatrix2)}
    {f : (α → Matrices.ComplexMatrix2) → β → Matrices.ComplexMatrix2}
    (h : ∃ T : p →ₗ[ℝ] p', ∀ x : p, (T x : β → Matrices.ComplexMatrix2) = f x) (x : p) :
    (linearMapWithValues p p' f x : β → Matrices.ComplexMatrix2) = f x := by apply _root_.YangMills.Construction.Tower.RescaledBackgroundFormFiniteSide.linearMapWithValues_apply <;> assumption
theorem exists_coboundary_linearMap :
    ∃ T : edgeFormSpace L n k 0 →ₗ[ℝ] faceFunctionSpace L n k 0, ∀ x : edgeFormSpace L n k 0,
      (T x : Face L n k 0 → Matrices.ComplexMatrix2) =
        edgeCoboundary (x : Edge L n k 0 → Matrices.ComplexMatrix2) :=
  ⟨{ toFun := fun x => ⟨_, edgeCoboundary_mem x.2⟩
     map_add' := fun x y => Subtype.ext (by
       funext p
       simp only [edgeCoboundary, Submodule.coe_add, Pi.add_apply]
       abel)
     map_smul' := fun r x => Subtype.ext (by
       funext p
       simp only [edgeCoboundary, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply,
         smul_sub, smul_add]) }, fun _ => rfl⟩
end Iterates
theorem face_pair_self_eq_zero {L n k : ℕ}
    (hI : FaceSums.PairingIsInner ↥(univ : Set (Face L n k 0)))
    (g : faceFunctionSpace L n k 0)
    (hfin : Finite (Face L n k 0))
    (h : traceFinsumPairing (g : Face L n k 0 → Matrices.ComplexMatrix2)
      (g : Face L n k 0 → Matrices.ComplexMatrix2) = 0) : g = 0 := by
  obtain ⟨c, hc⟩ := hI.2
  let f : FaceSums.finSuppLieFields ↥(univ : Set (Face L n k 0)) :=
    ⟨fun p => (g : Face L n k 0 → Matrices.ComplexMatrix2) p.1, fun p => g.2 p.1 trivial,
      Set.toFinite _⟩
  have e := hc f f
  have e' : traceFinsumPairing (f : ↥(univ : Set (Face L n k 0)) → Matrices.ComplexMatrix2)
      (f : ↥(univ : Set (Face L n k 0)) → Matrices.ComplexMatrix2) =
      traceFinsumPairing (g : Face L n k 0 → Matrices.ComplexMatrix2)
        (g : Face L n k 0 → Matrices.ComplexMatrix2) := by
    unfold traceFinsumPairing
    exact finsum_comp_equiv (Equiv.Set.univ (Face L n k 0))
      (f := fun b => Matrices.ComplexMatrix2.halfTrace
        ((g : Face L n k 0 → Matrices.ComplexMatrix2) b *
          (g : Face L n k 0 → Matrices.ComplexMatrix2) b))
  rw [e', h] at e
  have z : c.inner f f = 0 := by exact_mod_cast e
  have f0 : f = 0 := c.definite f z
  apply Subtype.ext
  funext p
  exact congrFun (congrArg Subtype.val f0) ⟨p, trivial⟩
theorem responseMapsHold_of (hV : LinearMapValues.Statement)
    (hO : LinearizationFacts.surjectivityStatement)
    (hP : RealTransposeEdgeFormPairing)
    (hR : RealTransposesExist)
    (hC : LeftChartFields.Claim)
    (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hS : FaceSums.FacesAndPairings) : ResponseMapsHold := by
  intro L hL k n hk hn
  have hsite : ∀ j, j ≤ k → Finite (Vertex L n k j) := fun j hj =>
    Set.finite_univ_iff.mp (((hS L hL k j hj).1 n hn).2.1 univ).2.1
  have hvals := (hV L hL k).1 n hn
  have hQ : StepLinear (L := L) (n := n) (k := k) (linearSmoothing L n k) :=
    ⟨fun j hj => linearSmoothing_add (hsite j (by omega)),
     fun j hj => linearSmoothing_smul (hsite j (by omega)),
     fun j hj B hB => (((hvals.1 j hj).1 B hB).2.2).1⟩
  have hQ' : StepLinear (L := L) (n := n) (k := k) (crossingSmoothing L n k) :=
    ⟨fun j hj => crossingSmoothing_add (hsite j (by omega)),
     fun j hj => crossingSmoothing_smul (hsite j (by omega)),
     fun j hj B hB => (((hvals.1 j hj).1 B hB).2).1⟩
  have vD : ∀ B : edgeFormSpace L n k 0,
      (CriticalBranchResponse.formCoboundary L n k B : Face L n k 0 → Matrices.ComplexMatrix2) =
        edgeCoboundary (B : Edge L n k 0 → Matrices.ComplexMatrix2) :=
    fun B => linearMapWithValues_apply exists_coboundary_linearMap B
  have vC : ∀ B : edgeFormSpace L n k 0,
      (CriticalBranchResponse.crossingSmoothingToTop L n k B :
        Edge L n k k → Matrices.ComplexMatrix2) = crossingSmoothingIter L n k k B :=
    fun B => linearMapWithValues_apply hQ'.exists_linearMap B
  have vL : ∀ B : edgeFormSpace L n k 0,
      (CriticalBranchResponse.linearSmoothingToTop L n k B :
        Edge L n k k → Matrices.ComplexMatrix2) = linearSmoothingIter L n k k B :=
    fun B => linearMapWithValues_apply hQ.exists_linearMap B
  have hplaq := ((hS L hL k 0 (Nat.zero_le _)).1 n hn).2.2.2 univ
  have hfinP : Finite (Face L n k 0) := Set.finite_univ_iff.mp hplaq.2.1
  have hC0 := (hC.2.2 L k 0 hL (Nat.zero_le _)).1 n hn
  refine
    { coboundary_eq := vD
      crossing_eq := vC
      linear_eq := vL
      coboundary_transpose := fun g f => ?_
      crossing_transpose := fun g f => hP L n k 0 k hL hn (Nat.zero_le _) le_rfl _ g f
      linear_transpose := fun g f => hP L n k 0 k hL hn (Nat.zero_le _) le_rfl _ g f
      linear_surjective := fun C => ?_
      face_pairing_definite := fun g h => face_pair_self_eq_zero hplaq.1 g hfinP h }
  · have e := edgeFormsEquiv hA hL hn (Nat.zero_le k) hC0.2.1.1
    have e' := univFunctionsEquiv (Face L n k 0)
    have hR' : PairedFunctionSpace.AdmitsRealTransposes (pairedFunctions (PosEdgeIndex L n k 0))
        (pairedFunctions ↥(univ : Set (Face L n k 0))) :=
      (hR L k hL).1 n hn (.edges 0 (Nat.zero_le _) univ) (.faces 0 (Nat.zero_le _) univ)
    have hT : LeftChartFields.HasUniqueTranspose (pairedFunctions (PosEdgeIndex L n k 0))
        (pairedFunctions ↥(univ : Set (Face L n k 0))) :=
      (hC0.2.2 (.edges 0 (Nat.zero_le _) univ) (.faces 0 (Nat.zero_le _) univ)).1
    exact pair_realTransposeMap e e' hR' hT _ g f
  · obtain ⟨B, hB, hBC⟩ := ((hO L hL n k 0 k hn (by omega) le_rfl).2.2).1 C C.2
    exact ⟨⟨B, hB⟩, Subtype.ext ((vL ⟨B, hB⟩).trans hBC)⟩
end
end YangMills.Construction.Tower.ResponseMaps
