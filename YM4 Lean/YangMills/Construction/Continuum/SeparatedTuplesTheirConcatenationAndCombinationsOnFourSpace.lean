import YangMills.Construction.Torus.SeparatedTuplesAndIsometriesOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
open YangMills.Construction.AmbientPoints
noncomputable section
namespace YangMills.Construction.Continuum.SeparatedFourTuples
variable (s : YangMills.Construction.Conventions.StandingParameters)
abbrev EuclideanFour : Type := Pt s .euclidean
abbrev SepTupleLen (k : ℕ) : Type := separatedTuples s .euclidean k
abbrev SepTuple : Type := allSeparatedTuples s .euclidean
variable {s}
def tupleLength (X : SepTuple s) : ℕ := X.1.1
def tupleComponents (X : SepTuple s) : Fin (tupleLength X) → EuclideanFour s → ℝ := X.1.2
theorem tupleComponents_mem (X : SepTuple s) :
    tupleComponents X ∈ separatedTuples s .euclidean (tupleLength X) := X.2
def ofFixedLength {k : ℕ} (X : SepTupleLen s k) : SepTuple s := ⟨⟨k, X.1⟩, X.2⟩
theorem sepTuple_ext {X Y : SepTuple s} (hlen : tupleLength X = tupleLength Y)
    (hent : ∀ i, tupleComponents X i = tupleComponents Y (Fin.cast hlen i)) : X = Y := by
  obtain ⟨⟨k, f⟩, hf⟩ := X
  obtain ⟨⟨k', g⟩, hg⟩ := Y
  change k = k' at hlen
  subst hlen
  have : f = g := funext hent
  subst this
  rfl
variable (s) in
def nilSepTuple : SepTuple s := ⟨nilTuple s .euclidean, nilTuple_mem_allSeparatedTuples⟩
abbrev c1SupportedIn (A : Set (EuclideanFour s)) : Set (EuclideanFour s → ℝ) :=
  c1CompactlySupportedIn A
def fixedLengthTuplesIn (O : Set (EuclideanFour s)) (k : ℕ) : Set (SepTupleLen s k) :=
  {X | ∀ i, X.1 i ∈ c1SupportedIn O}
def sepTuplesIn (O : Set (EuclideanFour s)) : Set (SepTuple s) :=
  ⋃ k, ofFixedLength '' fixedLengthTuplesIn O k
theorem mem_sepTuplesIn {O : Set (EuclideanFour s)} {X : SepTuple s} :
    X ∈ sepTuplesIn O ↔ ∀ i, tupleComponents X i ∈ c1SupportedIn O := by
  constructor
  · intro hX
    obtain ⟨k, Y, hY, rfl⟩ := Set.mem_iUnion.1 hX
    exact hY
  · intro hX
    exact Set.mem_iUnion.2 ⟨tupleLength X, ⟨tupleComponents X, tupleComponents_mem X⟩, hX, rfl⟩
def CanConcat (X Y : SepTuple s) : Prop :=
  ∀ i j, Disjoint (tsupport (tupleComponents X i)) (tsupport (tupleComponents Y j))
def appendTuple (X Y : SepTuple s) :
    Fin (tupleLength X + tupleLength Y) → EuclideanFour s → ℝ :=
  Fin.append (tupleComponents X) (tupleComponents Y)
theorem appendTuple_mem {X Y : SepTuple s} (hXY : CanConcat X Y) :
    appendTuple X Y ∈ separatedTuples s .euclidean (tupleLength X + tupleLength Y) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · simpa [appendTuple] using (tupleComponents_mem X).1 a
    · simpa [appendTuple] using (tupleComponents_mem Y).1 b
  · induction i using Fin.addCases with
    | left a =>
      induction j using Fin.addCases with
      | left b =>
        simpa [appendTuple] using
          (tupleComponents_mem X).2 (fun e => hij (by rw [e]) : a ≠ b)
      | right b => simpa [appendTuple] using hXY a b
    | right a =>
      induction j using Fin.addCases with
      | left b => simpa [appendTuple] using (hXY b a).symm
      | right b =>
        simpa [appendTuple] using
          (tupleComponents_mem Y).2 (fun e => hij (by rw [e]) : a ≠ b)
def concat (X Y : SepTuple s) (hXY : CanConcat X Y) : SepTuple s :=
  ⟨⟨_, appendTuple X Y⟩, appendTuple_mem hXY⟩
end YangMills.Construction.Continuum.SeparatedFourTuples
