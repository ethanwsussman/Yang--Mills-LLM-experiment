import YangMills.Construction.Continuum.ConnectedFunctionsOfARealFunctionByRecursion
import YangMills.Construction.Continuum.SeparatedTuplesOfFourSpace
import YangMills.Construction.Continuum.SubTuplesIsometriesAndTheConjugateOnFourSpace
import YangMills.Construction.EuclideanFunctionals.TuplesIsometriesFreeSpaceAndMirrorOfFourSpace
import YangMills.Construction.Torus.MultilinearFunctionalsOnSeparatedTuplesOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
noncomputable section
namespace YangMills.Construction.TestSpaces
open YangMills.Construction.SetPartition
variable {n : ℕ}
theorem ofFn_mem_ambientSeparatedN (D : ReflectionPositivity.AxisMirror.MirrorData)
    (X : SepTupleOfCard n) :
    (List.ofFn X.1 : Ambient.FnList D .euclidean) ∈ Ambient.separatedN D .euclidean n := by
  have hT : DisjointTuples.IsDisjointTuple (List.ofFn X.1) := by
    refine ⟨fun f hf => ?_, List.pairwise_ofFn.2 fun i j hij => X.2.2 hij.ne⟩
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hf
    obtain ⟨h₁, h₂, -⟩ := X.2.1 i
    exact ⟨h₁, h₂⟩
  obtain ⟨m, hm⟩ := Set.mem_iUnion.1
    ((SeparatedTuplesR4.isDisjointTuple_iff_mem_separatedAll D _).1 hT)
  exact ⟨List.length_ofFn, hm.2⟩
theorem get_mem_disjointSupportTuples (D : ReflectionPositivity.AxisMirror.MirrorData)
    (Y : Ambient.separatedN D .euclidean n) :
    (fun i : Fin n => (Y.1.get (Fin.cast Y.2.1.symm i) : (Fin 4 → ℝ) → ℝ)) ∈
      disjointSupportTuples (Set.univ : Set (Fin 4 → ℝ)) n := by
  have hT : DisjointTuples.IsDisjointTuple Y.1 :=
    (SeparatedTuplesR4.isDisjointTuple_iff_mem_separatedAll D _).2
      (Ambient.separatedN_subset_separatedAll D _ n Y.2)
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · obtain ⟨h₁, h₂⟩ := hT.1 _ (List.get_mem Y.1 (Fin.cast Y.2.1.symm i))
    exact ⟨h₁, h₂, Set.subset_univ _⟩
  · have hp := List.pairwise_iff_get.1 hT.2
    rcases lt_or_gt_of_ne hij with h' | h'
    · exact hp (Fin.cast Y.2.1.symm i) (Fin.cast Y.2.1.symm j) (show (i : ℕ) < j from h')
    · exact (hp (Fin.cast Y.2.1.symm j) (Fin.cast Y.2.1.symm i) (show (j : ℕ) < i from h')).symm
def sepTupleListEquiv (D : ReflectionPositivity.AxisMirror.MirrorData) (n : ℕ) :
    SepTupleOfCard n ≃ Ambient.separatedN D .euclidean n where
  toFun X := ⟨List.ofFn X.1, ofFn_mem_ambientSeparatedN D X⟩
  invFun Y := ⟨_, get_mem_disjointSupportTuples D Y⟩
  left_inv X := Subtype.ext (funext fun i =>
    (List.get_ofFn X.1 _).trans (congrArg X.1 (Fin.ext rfl)))
  right_inv Y := Subtype.ext (List.ext_get (by simpa using Y.2.1.symm) fun i h₁ h₂ => by simp)
def onAmbientLists (D : ReflectionPositivity.AxisMirror.MirrorData) (Φ : SepTupleOfCard n → ℝ) :
    Ambient.separatedN D .euclidean n → ℝ :=
  fun Y => Φ ((sepTupleListEquiv D n).symm Y)
def onPointTuples (p : Conventions.StandingParameters) (Φ : SepTupleOfCard n → ℝ) :
    AmbientPoints.separatedTuples p .euclidean n → ℝ :=
  fun f => Φ (Continuum.SeparatedFourTuples.sepLenEquiv p n f)
def onAllPointTuples (p : Conventions.StandingParameters) (σ : SepTuple → ℝ) :
    AmbientPoints.allSeparatedTuples p .euclidean → ℝ :=
  fun X => σ (Continuum.SeparatedFourTuples.sepTupleEquiv p X)
def connFamilyOnTuples (S : EuclideanFunctionals.ConnFamily) :
    (m : ℕ) → 2 ≤ m → SepTupleOfCard m → ℝ :=
  fun m hm X => S.fn m hm (sepTupleListEquiv _ m X)
def centredOfConnFamily (S : EuclideanFunctionals.ConnFamily) (X : SepTuple) : ℝ :=
  EuclideanFunctionals.centeredFn S
    ⟨(sepTupleListEquiv _ X.1 X.2).1,
      Ambient.separatedN_subset_separatedAll _ _ X.1 (sepTupleListEquiv _ X.1 X.2).2⟩
def CumulantRecursionUniqueAt (σ : SepTuple → ℝ) {k : ℕ} (X : SepTupleOfCard k) : Prop :=
  SatisfiesCumulantRecursionAt σ X ∧
    ∀ c : Finset (Fin k) → ℝ,
      (∀ I : Finset (Fin k), I.Nonempty → σ ⟨I.card, sepRestrict X I⟩ =
        ∑ P : Partitions I, ∏ B ∈ P.parts, c B) →
      ∀ I : Finset (Fin k), I.Nonempty →
        c I = cumulantRec σ I.card (sepRestrict X I)
def HasLowOrderValues (σ : SepTuple → ℝ) (S₂ : SepTupleOfCard 2 → ℝ) : Prop :=
  σ sepTupleNil = 1 ∧ (∀ X : SepTupleOfCard 1, σ ⟨1, X⟩ = 0) ∧
    ∀ X : SepTupleOfCard 2, σ ⟨2, X⟩ = S₂ X
def CentredLowOrderFormulas : Prop :=
  (∀ S : EuclideanFunctionals.ConnFamily,
    (∀ (k : ℕ) (X : SepTupleOfCard k), centredOfConnFamily S ⟨k, X⟩ =
      centredOfCumulants (connFamilyOnTuples S) ⟨k, X⟩) ∧
    HasLowOrderValues (centredOfConnFamily S) (connFamilyOnTuples S 2 le_rfl)) ∧
  ∀ S : (m : ℕ) → 2 ≤ m → SepTupleOfCard m → ℝ,
    HasLowOrderValues (centredOfCumulants S) (S 2 le_rfl)
def MultilinearFormsAgree : Prop :=
  (∀ (n : ℕ), 1 ≤ n → ∀ (D : ReflectionPositivity.AxisMirror.MirrorData)
      (p : Conventions.StandingParameters) (Φ : SepTupleOfCard n → ℝ),
    (IsMultilinearOnSep Φ ↔ Ambient.IsSeparatedMultilinear D .euclidean (onAmbientLists D Φ)) ∧
    (Ambient.IsSeparatedMultilinear D .euclidean (onAmbientLists D Φ) ↔
      AmbientPoints.IsTupleMultilinear (onPointTuples p Φ))) ∧
  ∀ (p : Conventions.StandingParameters) (σ : SepTuple → ℝ),
    IsSepFunctional σ ↔
      AmbientPoints.IsTupleFunctional (onAllPointTuples p σ)
def CumulantExplicitFormula (σ : SepTuple → ℝ) (n : ℕ) : Prop :=
  (∀ X : SepTupleOfCard n, cumulantRec σ n X =
    ∑ P : Partitions (Finset.univ : Finset (Fin n)),
      (-1 : ℝ) ^ (blockCount P - 1) * ((blockCount P - 1).factorial : ℝ) *
        ∏ B ∈ P.parts, σ ⟨B.card, sepRestrict X B⟩) ∧
  (∀ X : SepTupleOfCard n, cumulantRec σ n X = cumulant σ X) ∧
  (∀ (p : Conventions.StandingParameters) (X : SepTupleOfCard n), cumulantRec σ n X =
    AmbientPoints.connectedOf (onAllPointTuples p σ) n
      ((Continuum.SeparatedFourTuples.sepLenEquiv p n).symm X)) ∧
  IsMultilinearOnSep (cumulantRec σ n)
def CumulantRecursionTriangular : Prop :=
  (∀ (σ : SepTuple → ℝ) (k : ℕ), 1 ≤ k → ∀ X : SepTupleOfCard k,
    CumulantRecursionUniqueAt σ X) ∧
  CentredLowOrderFormulas ∧
  MultilinearFormsAgree ∧
  ∀ σ : SepTuple → ℝ, IsSepFunctional σ →
    (∀ n, 1 ≤ n → CumulantExplicitFormula σ n) ∧ centredOfRec σ = centredPart σ
end YangMills.Construction.TestSpaces
