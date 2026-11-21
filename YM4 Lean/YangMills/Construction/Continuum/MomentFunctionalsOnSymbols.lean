import YangMills.Construction.QuaternionicWilsonModel.TheDefaultCasesAreUnusedProof
import YangMills.Construction.HilbertSpaces.ReconstructionFromAPositiveFormDefs
import Mathlib
set_option autoImplicit false
open Filter Topology
open scoped NNReal ENNReal ComplexOrder ComplexConjugate
noncomputable section
namespace YangMills.Construction.TimeAxisSymbols
open TorusTransport TorusTransport.TupleVectors TorusTransport.TestFunctionOrders
open PositiveFormReconstruction (PreHilbertData)
open TorusLifts (signedCoordinateEquiv)
variable {D : TransportData}
def ofSepTuple {k : ℕ+} (f : Domain.euclidean.FnFamily D k ℝ) (hf : f ∈ symbolsOfCard D k) :
    SpaceTimeSymbol D :=
  ⟨⟨k, f⟩, (mem_spaceTimeSymbols_iff D _).mpr (Or.inr ⟨k, f, hf, rfl⟩)⟩
def restrictCard (m : SpaceTimeSymbol D → ℝ) (k : ℕ+) : symbolsOfCard D k → ℝ :=
  fun f => m (ofSepTuple f.1 f.2)
def posToSymbol (X : PosSymbol D) : SpaceTimeSymbol D :=
  inclusionMap D (Set.subset_univ _) X
def posUnitSymbol : PosSymbol D := ⟨nilTuple _, nilTuple_mem_sepTuples D _⟩
theorem timeAxisStabilizer_apply_last (w : timeAxisStabilizer) (x : Fin 4 → ℝ) :
    w.1.1 x 3 = x 3 := by apply _root_.YangMills.Construction.ConditionDefaults.stabilizer_preserves_time <;> assumption
theorem actAny_mem_posSymbols {s : (Fin 4 → ℝ) → Fin 4 → ℝ}
    (hs : IsEuclideanMotion s) (hmaps : Set.MapsTo s posTimeHalf posTimeHalf) {t : FnTuple}
    (ht : t ∈ posSymbols D) : actAny hs t ∈ posSymbols D := by
  obtain ⟨hsym, hpos⟩ := (mem_posSymbols_iff D t).mp ht
  refine (mem_posSymbols_iff D _).mpr ⟨actAny_mem_spaceTimeSymbols hs hsym, fun i => ?_⟩
  have hsupp : entrySupp D ((actAny hs t).2 i) =
      hs.toPerm.symm ⁻¹' entrySupp D (t.2 i) :=
    tsupport_comp_eq_preimage (t.2 i) (motionHomeomorph hs).symm
  rw [hsupp]
  intro x hx
  have hmem := hmaps (hpos i hx)
  have hback : s (hs.toPerm.symm x) = x := hs.toPerm.apply_symm_apply x
  rwa [hback] at hmem
def posMotion {s : (Fin 4 → ℝ) → Fin 4 → ℝ} (hs : IsEuclideanMotion s)
    (hmaps : Set.MapsTo s posTimeHalf posTimeHalf) (X : PosSymbol D) : PosSymbol D :=
  ⟨actAny hs X.1, actAny_mem_posSymbols hs hmaps X.2⟩
theorem mapsTo_posTimeHalf_timeShift (t : ℝ≥0) :
    Set.MapsTo (translationEquiv ((t : ℝ) • timeAxisVec)) posTimeHalf posTimeHalf := by
  intro x hx
  have hx3 : 0 < x 3 := hx
  show 0 < (x + (t : ℝ) • timeAxisVec) 3
  have hlast : timeAxisVec 3 = 1 := by simp [PeriodicLattice.coordVec]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hlast, mul_one]
  have := t.2
  linarith
theorem mapsTo_posTimeHalf_spaceShift (a : Fin 3 → ℝ) :
    Set.MapsTo (translationEquiv (spaceTimePoint a 0)) posTimeHalf posTimeHalf := by
  intro x hx
  have hx3 : 0 < x 3 := hx
  show 0 < (x + spaceTimePoint a 0) 3
  rw [Pi.add_apply, spaceTimePoint_last, add_zero]
  exact hx3
theorem mapsTo_posTimeHalf_stabilizer (w : timeAxisStabilizer) :
    Set.MapsTo w.1.1 posTimeHalf posTimeHalf := by
  intro x hx
  show 0 < w.1.1 x 3
  rw [timeAxisStabilizer_apply_last]
  exact hx
def posTimeShift (t : ℝ≥0) (X : PosSymbol D) : PosSymbol D :=
  posMotion (isEuclideanMotion_translationEquiv _) (mapsTo_posTimeHalf_timeShift t) X
def posSpaceShift (a : Fin 3 → ℝ) (X : PosSymbol D) : PosSymbol D :=
  posMotion (isEuclideanMotion_translationEquiv _) (mapsTo_posTimeHalf_spaceShift a) X
def posRotate (w : timeAxisStabilizer) (X : PosSymbol D) : PosSymbol D :=
  posMotion (isEuclideanMotion_hyperoctahedral w.1) (mapsTo_posTimeHalf_stabilizer w) X
theorem posToSymbol_posTimeShift (t : ℝ≥0) (X : PosSymbol D) :
    posToSymbol (posTimeShift t X) =
      translateSymbol ((t : ℝ) • timeAxisVec) (posToSymbol X) :=
  rfl
theorem posToSymbol_posSpaceShift (a : Fin 3 → ℝ) (X : PosSymbol D) :
    posToSymbol (posSpaceShift a X) =
      translateSymbol (spaceTimePoint a 0) (posToSymbol X) :=
  rfl
theorem appendDefined_reflect (X Y : PosSymbol D) :
    AppendDefined D (reflectSymbol (posToSymbol X)).1 (posToSymbol Y).1 := by
  refine (appendDefined_iff (reflectSymbol (posToSymbol X)).2
    (posToSymbol Y).2).mpr fun i j => Set.disjoint_left.mpr fun x hx hy => ?_
  have hinv : isEuclideanMotion_timeReflect.toPerm.symm x = timeReflect x :=
    (Equiv.symm_apply_eq _).mpr (timeReflect_timeReflect x).symm
  have hsupp : entrySupp D ((reflectSymbol (posToSymbol X)).1.2 i) =
      isEuclideanMotion_timeReflect.toPerm.symm ⁻¹' entrySupp D (X.1.2 i) :=
    tsupport_comp_eq_preimage (X.1.2 i) (motionHomeomorph isEuclideanMotion_timeReflect).symm
  rw [hsupp] at hx
  have hX : 0 < isEuclideanMotion_timeReflect.toPerm.symm x 3 :=
    ((mem_posSymbols_iff D X.1).mp X.2).2 i hx
  have hY : 0 < x 3 := ((mem_posSymbols_iff D Y.1).mp Y.2).2 j hy
  rw [hinv, timeReflect_apply] at hX
  have hneg : (![x 0, x 1, x 2, -x 3] : Fin 4 → ℝ) 3 = -x 3 := rfl
  rw [hneg] at hX
  linarith
def reflectAppend (X Y : PosSymbol D) : SpaceTimeSymbol D :=
  sepAppend (reflectSymbol (posToSymbol X)) (posToSymbol Y)
    (appendDefined_reflect X Y)
structure IsNormedSymmMultilinear (m : SpaceTimeSymbol D → ℝ) : Prop where
  unit_eq_one : m (unitSymbol D) = 1
  multilinear : ∀ k : ℕ+, IsMultilinearOnSymbolsOfCard D (restrictCard m k)
  symmetric : ∀ k : ℕ+, IsPermSymmetric (restrictCard m k)
def IsScaleBounded (m : SpaceTimeSymbol D → ℝ) (b : ℕ+ → ℝ → ℝ → ℝ≥0) : Prop :=
  ∀ (k : ℕ+) (d R : ℝ) (hd : 0 < d) (hR : 0 < R) (f : Domain.euclidean.FnFamily D k ℝ)
    (hf : (⟨k, f⟩ : FnTuple) ∈ scaledSymbols D d R hd hR),
    ENNReal.ofReal |m ⟨_, admissibleSepTuples_subset D hd hR hf⟩| ≤
      (b k d R : ℝ≥0∞) * ∏ i, Domain.euclidean.ennSharpNorm D (f i)
def IsMotionInvariant (m : SpaceTimeSymbol D → ℝ) : Prop :=
  ∀ (s : (Fin 4 → ℝ) → Fin 4 → ℝ) (hs : IsEuclideanMotion s), s ∈ affineHyperoctahedral →
    ∀ X : SpaceTimeSymbol D, m (motionSymbol hs X) = m X
def IsReflPositive (m : SpaceTimeSymbol D → ℝ) : Prop :=
  ∀ (N : ℕ), 1 ≤ N → ∀ (X : Fin N → PosSymbol D) (c : Fin N → ℂ),
    0 ≤ ∑ p, ∑ q, conj (c p) * c q * ((m (reflectAppend (X p) (X q)) : ℝ) : ℂ)
def momentLinExtend (m : SpaceTimeSymbol D → ℝ) : SymbolSpan D →ₗ[ℂ] ℂ :=
  linExtend fun X => ((m X : ℝ) : ℂ)
def osForm (m : SpaceTimeSymbol D → ℝ) (F G : PosSymbolSpan D) : ℂ :=
  momentLinExtend m
    (appendBilin
      (linExtendSymbolMap reflectSymbol (posSymbolSpanInclusion D (conjCoeffs F)))
      (posSymbolSpanInclusion D G))
theorem osForm_basisVec (m : SpaceTimeSymbol D → ℝ) (X Y : PosSymbol D) :
    osForm m (basisVec X) (basisVec Y) = ((m (reflectAppend X Y) : ℝ) : ℂ) := by
  have hconj : conjCoeffs (basisVec X) = basisVec X := by
    simp [conjCoeffs, TupleVectors.basisVec]
  have hincl : ∀ Z : PosSymbol D,
      posSymbolSpanInclusion D (basisVec Z) = basisVec (posToSymbol Z) := fun Z =>
    linExtend_basisVec _ Z
  rw [osForm, hconj, hincl, hincl, linExtendSymbolMap_basisVec, appendBilin_basisVec,
    appendOnBasis, dif_pos (appendDefined_reflect X Y)]
  exact linExtend_basisVec _ _
def osPreHilbertData (m : SpaceTimeSymbol D → ℝ) : PreHilbertData (PosSymbolSpan D) where
  form := osForm m
  unitVec := basisVec posUnitSymbol
  semigroupMap t := linExtend fun X => basisVec (posTimeShift t X)
  translationMap a := linExtend fun X => basisVec (posSpaceShift a.ofLp X)
  rotationMap w := linExtend fun X => basisVec (posRotate w X)
def cardBound (b : ℕ+ → ℝ → ℝ → ℝ≥0) : ℕ → ℝ → ℝ → ℝ≥0
  | 0, _, _ => 1
  | k + 1, d, R => b k.succPNat d R
def sharpNormProd (X : PosSymbol D) : ℝ≥0∞ :=
  ∏ i, Domain.euclidean.ennSharpNorm D (X.1.2 i)
def gaussianRationals : Set ℂ := {z | ∃ p q : ℚ, z = (p : ℂ) + (q : ℂ) * Complex.I}
def IsUnitOrDense (C : DenseChoice D) (X : PosSymbol D) : Prop :=
  X.1 = nilTuple _ ∨ X.1 ∈ C.family
def rationalSpan (C : DenseChoice D) : Set (PosSymbolSpan D) :=
  {F | ∃ (N : ℕ) (c : Fin N → ℂ) (X : Fin N → PosSymbol D),
    (∀ p, c p ∈ gaussianRationals) ∧ (∀ p, IsUnitOrDense C (X p)) ∧ F = linComb c X}
namespace MomentFunctionals
def LipschitzOnProducts (m : SpaceTimeSymbol D → ℝ) (b : ℕ+ → ℝ → ℝ → ℝ≥0) : Prop :=
  ∀ (k : ℕ+) (d R : ℝ) (hd : 0 < d) (hR : 0 < R) (A : Fin k → Set (Fin 4 → ℝ)),
    IsAdmissibleSets D d R hd hR A →
    ∀ f g : Domain.euclidean.FnFamily D k ℝ,
      (∀ i, f i ∈ c1SupportedIn (A i)) →
      (∀ i, g i ∈ c1SupportedIn (A i)) →
      ∃ (hf : (⟨k, f⟩ : FnTuple) ∈ spaceTimeSymbols D) (hg : (⟨k, g⟩ : FnTuple) ∈ spaceTimeSymbols D),
        ENNReal.ofReal |m ⟨_, hf⟩ - m ⟨_, hg⟩| ≤
          (b k d R : ℝ≥0∞) * ∑ i, Domain.euclidean.ennSharpNorm D (f i - g i) *
            ∏ l ∈ Finset.univ.erase i,
              max (Domain.euclidean.ennSharpNorm D (f l))
                (Domain.euclidean.ennSharpNorm D (g l))
def ContinuousInShift (m : SpaceTimeSymbol D → ℝ) : Prop :=
  ∀ (X Y : SpaceTimeSymbol D) (v : Fin 4 → ℝ) (h : AppendDefined D X.1 (translateSymbol v Y).1),
    (∀ᶠ w in 𝓝 v, AppendDefined D X.1 (translateSymbol w Y).1) ∧
    ∀ ε : ℝ, 0 < ε → ∀ᶠ w in 𝓝 v,
      ∃ h' : AppendDefined D X.1 (translateSymbol w Y).1,
        |m (sepAppend X (translateSymbol w Y) h') -
          m (sepAppend X (translateSymbol v Y) h)| < ε
def SupBound (m : SpaceTimeSymbol D → ℝ) (b : ℕ+ → ℝ → ℝ → ℝ≥0) : Prop :=
  ∀ (N : ℕ) (c : Fin N → ℂ) (X : Fin N → PosSymbol D) (δ d₀ R₀ : ℝ) (_hδ : 0 < δ)
    (hd₀ : 0 < d₀) (_hd₀δ : d₀ ≤ 2 * δ) (hR₀ : 0 < R₀),
    (∀ p i, entrySupp D ((X p).1.2 i) ⊆ {x | δ ≤ x 3}) →
    (∀ p, (X p).1 ∈ scaledSymbols D d₀ R₀ hd₀ hR₀) →
    ⨆ t : ℝ≥0, ENNReal.ofReal
        ‖osForm m (linComb c X) ((osPreHilbertData m).semigroupMap t (linComb c X))‖ ≤
      ∑ p, ∑ q, ENNReal.ofReal ‖c p‖ * ENNReal.ofReal ‖c q‖ *
        (cardBound b ((X p).1.1 + (X q).1.1) d₀ R₀ : ℝ≥0∞) *
        sharpNormProd (X p) * sharpNormProd (X q)
def RationalSpanDense (m : SpaceTimeSymbol D → ℝ) (C : DenseChoice D) : Prop :=
  (rationalSpan C).Countable ∧
    ∀ (F : PosSymbolSpan D) (ε : ℝ), 0 < ε →
      ∃ F₀ ∈ rationalSpan C, osForm m (F - F₀) (F - F₀) < (ε : ℂ)
def Statement : Prop :=
  ∀ (D : TransportData) (m : SpaceTimeSymbol D → ℝ) (b : ℕ+ → ℝ → ℝ → ℝ≥0),
    IsNormedSymmMultilinear m → IsScaleBounded m b →
    LipschitzOnProducts m b ∧ ContinuousInShift m ∧
      (IsMotionInvariant m → IsReflPositive m →
        (osPreHilbertData m).IsAdmissible ∧ SupBound m b ∧
          ∀ C : DenseChoice D, RationalSpanDense m C)
end MomentFunctionals
end YangMills.Construction.TimeAxisSymbols
end
