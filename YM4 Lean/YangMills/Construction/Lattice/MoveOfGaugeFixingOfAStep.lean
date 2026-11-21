import YangMills.Construction.Lattice.BlockLawOfTheAxialFactor
import YangMills.Construction.Lattice.SettingOfTheMovesOfGaugeFixing
import YangMills.Construction.Lattice.SmallFieldDomainOfAStep
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.PeriodicLattice
namespace ConfigSpaces
open BorelKernels FaddeevPopov TermEvaluation Matrices
variable {L m K k : ℕ}
theorem finite_bondAtLevel_of_finite_siteAtLevel [Finite (SiteAtLevel L m K k)] :
    Finite (BondAtLevel L m K k) :=
  Finite.of_injective (fun e : BondAtLevel L m K k => (e.source, e.target)) fun _ _ h =>
    Bond.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
def gradedBondsOf [Finite (SiteAtLevel L m K k)] (B : Set (BondAtLevel L m K k)) :
    Finset (GradedBond L m K) :=
  haveI := finite_bondAtLevel_of_finite_siteAtLevel (L := L) (m := m) (K := K) (k := k)
  (Set.toFinite ((fun e => (⟨k, e⟩ : GradedBond L m K)) '' B)).toFinset
theorem mem_gradedBondsOf [Finite (SiteAtLevel L m K k)] {B : Set (BondAtLevel L m K k)}
    {e : BondAtLevel L m K k} : (⟨k, e⟩ : GradedBond L m K) ∈ gradedBondsOf B ↔ e ∈ B := by
  simp [gradedBondsOf]
theorem exists_of_mem_gradedBondsOf [Finite (SiteAtLevel L m K k)] {B : Set (BondAtLevel L m K k)}
    {c : GradedBond L m K} (h : c ∈ gradedBondsOf B) :
    ∃ e ∈ B, (⟨k, e⟩ : GradedBond L m K) = c := by
  simpa [gradedBondsOf] using h
def TouchesSites (S : Finset (FourTorus L m)) (e : BondAtLevel L m K k) : Prop :=
  (e.source : FourTorus L m) ∈ S ∨ (e.target : FourTorus L m) ∈ S
theorem touchesSites_opposite {S : Finset (FourTorus L m)} {e : BondAtLevel L m K k} :
    TouchesSites S e.opposite ↔ TouchesSites S e :=
  or_comm
structure BondOrientation (L m K k : ℕ) where
  chosen : Set (BondAtLevel L m K k)
  mem_chosen_iff : ∀ e, e ∈ chosen ↔ e.opposite ∉ chosen
namespace BondOrientation
variable [Finite (SiteAtLevel L m K k)] (O : BondOrientation L m K k) (S : Finset (FourTorus L m))
def incidentBonds : Finset (GradedBond L m K) :=
  gradedBondsOf {e | e ∈ O.chosen ∧ TouchesSites S e}
def nonIncidentBonds : Finset (GradedBond L m K) :=
  gradedBondsOf {e | e ∈ O.chosen ∧ ¬TouchesSites S e}
abbrev ExteriorField : Type := O.nonIncidentBonds S → ComplexMatrix2.specialUnitary
variable {O S}
omit [Finite (SiteAtLevel L m K k)] in
theorem not_mem_and_flip_mem {𝔅 : Finset (GradedBond L m K)}
    (h𝔅 : ∀ e : BondAtLevel L m K k, (⟨k, e⟩ : GradedBond L m K) ∈ 𝔅 → e ∈ O.chosen)
    (e : BondAtLevel L m K k) :
    ¬((⟨k, e⟩ : GradedBond L m K) ∈ 𝔅 ∧
      OrientedEdgeEnds.flip (⟨k, e⟩ : GradedBond L m K) ∈ 𝔅) := fun h =>
  (O.mem_chosen_iff e).1 (h𝔅 e h.1) (h𝔅 e.opposite h.2)
end BondOrientation
theorem linkValue_flip_of_not_both {𝔅 : Finset (GradedBond L m K)}
    (v : 𝔅 → ComplexMatrix2.specialUnitary)
    (e : GradedBond L m K) (h : ¬(e ∈ 𝔅 ∧ OrientedEdgeEnds.flip e ∈ 𝔅)) :
    linkValue v (OrientedEdgeEnds.flip e) = (linkValue v e)⁻¹ := by
  by_cases he : e ∈ 𝔅
  · have hf : OrientedEdgeEnds.flip e ∉ 𝔅 := fun hf => h ⟨he, hf⟩
    simp [linkValue, he, hf, OrientedEdgeEnds.flip_flip]
  · by_cases hf : OrientedEdgeEnds.flip e ∈ 𝔅
    · simp [linkValue, he, hf]
    · simp [linkValue, he, hf, OrientedEdgeEnds.flip_flip]
namespace BondOrientation
variable [Finite (SiteAtLevel L m K k)] (O : BondOrientation L m K k) (S : Finset (FourTorus L m))
def linkOfPair (v : O.incidentBonds S → ComplexMatrix2.specialUnitary) (v' : O.ExteriorField S)
    (e : BondAtLevel L m K k) : ComplexMatrix2.specialUnitary :=
  open Classical in
  if TouchesSites S e then linkValue v ⟨k, e⟩ else linkValue v' ⟨k, e⟩
variable {O S}
theorem linkOfPair_opposite (v : O.incidentBonds S → ComplexMatrix2.specialUnitary)
    (v' : O.ExteriorField S) (e : BondAtLevel L m K k) :
    O.linkOfPair S v v' e.opposite = (O.linkOfPair S v v' e)⁻¹ := by
  by_cases hS : TouchesSites S e
  · have hS' : TouchesSites S e.opposite := touchesSites_opposite.2 hS
    simp only [linkOfPair, hS, hS', if_true]
    exact linkValue_flip_of_not_both v _ (not_mem_and_flip_mem
      (fun c hc => (mem_gradedBondsOf.1 hc).1) e)
  · have hS' : ¬TouchesSites S e.opposite := fun h => hS (touchesSites_opposite.1 h)
    simp only [linkOfPair, hS, hS', if_false]
    exact linkValue_flip_of_not_both v' _ (not_mem_and_flip_mem
      (fun c hc => (mem_gradedBondsOf.1 hc).1) e)
variable (O S)
def assembledField
    (w : (O.incidentBonds S → ComplexMatrix2.specialUnitary) × O.ExteriorField S) :
    BlockFields L m K k :=
  ⟨fun e => (O.linkOfPair S w.1 w.2 e : ComplexMatrix2), fun e _ => (O.linkOfPair S w.1 w.2 e).2,
    fun e _ => by
    have inv_coe : ∀ g : ComplexMatrix2.specialUnitary,
        ((g⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) = (g : ComplexMatrix2)⁻¹ :=
      fun g => by
        symm
        apply Matrix.inv_eq_right_inv
        exact congrArg Subtype.val (mul_inv_cancel g)
    beta_reduce
    rw [linkOfPair_opposite, inv_coe]⟩
end BondOrientation
def orientedBondsAtLevel (L m K k : ℕ) [Finite (SiteAtLevel L m K k)] :
    Finset (GradedBond L m K) :=
  gradedBondsOf {e : BondAtLevel L m K k | e.IsPositivelyOriented ∧ ¬e.opposite.IsPositivelyOriented}
theorem exists_orientedBond_eq [Finite (SiteAtLevel L m K k)]
    (c : orientedBondsAtLevel L m K k) :
    ∃ e : PositivelyOrientedBond L m (levelDepth K k), (⟨k, e.1⟩ : GradedBond L m K) = c.1 := by
  obtain ⟨e, he, h⟩ := exists_of_mem_gradedBondsOf c.2
  exact ⟨⟨e, he.1⟩, h⟩
def orientedBondOf [Finite (SiteAtLevel L m K k)] (c : orientedBondsAtLevel L m K k) :
    PositivelyOrientedBond L m (levelDepth K k) :=
  Classical.choose (exists_orientedBond_eq c)
theorem orientedBondOf_spec [Finite (SiteAtLevel L m K k)] (c : orientedBondsAtLevel L m K k) :
    (⟨k, (orientedBondOf c).1⟩ : GradedBond L m K) = c.1 :=
  Classical.choose_spec (exists_orientedBond_eq c)
def linkVariable (L m K k : ℕ) (Stored : Type) [Finite (SiteAtLevel L m K k)] :
    BondField L m K k Stored where
  support := orientedBondsAtLevel L m K k
  support_one_orientation := fun c hc hr => by
    obtain ⟨e, he, rfl⟩ := exists_of_mem_gradedBondsOf hc
    exact he.2 (mem_gradedBondsOf.1 hr).1
  coord := fun c => Sum.inl (orientedBondOf c)
  coord_injective := fun c c' h => by
    apply Subtype.ext
    rw [← orientedBondOf_spec c, ← orientedBondOf_spec c', Sum.inl_injective h]
def gaugeMoveOnSet (Stored : Type) [Finite (SiteAtLevel L m K k)] (O : BondOrientation L m K k)
    (S : Finset (FourTorus L m))
    (kern : ∀ (𝒴' : Type) [MeasurableSpace 𝒴'],
      ConfigSpace (O.incidentBonds S) (O.ExteriorField S × 𝒴') →
        Measure (SiteGaugeGroup S)) :
    GaugeMoveData.{0} L m K k Stored where
  siteSet := S
  moved := linkVariable L m K k Stored
  bondSet := O.incidentBonds S
  fixedSpace := O.ExteriorField S
  blockMap := O.assembledField S
  kernel := kern
end ConfigSpaces
namespace CubesOfStep
open ParameterChoice ConfigSpaces Matrices
variable (c : ChoiceUpToDegreeConstants) {m : ℕ} (K : ℕ) (x : ℕ → ℝ)
def laterGaugeSites (k : ℕ) (P Y : Set (FourTorus c.L m)) : Set (SiteAtLevel c.L m K (k + 1)) :=
  gaugeFixedSites c K k (stepGaugeFixedRegion c K x k P Y)
def initialOuterRegion (P₀ : Set (FourTorus c.L m)) : Set (FourTorus c.L m) :=
  complementRegion (coarsePartitionIndex c K x 0)
    (coarseCollar c K x 0 (coarseCubeHull c K x 0 P₀) 1)
def initialGaugeRegion (P₀ P₁ : Set (FourTorus c.L m)) : Set (FourTorus c.L m) :=
  gaugeFixedRegion c K x 0 P₁ (coarseCollar c K x 0 (coarseCubeHull c K x 0 P₀) 2)
def initialGaugeSites (P₀ P₁ : Set (FourTorus c.L m)) : Set (SiteAtLevel c.L m K 1) :=
  gaugeFixedSites c K 0 (initialGaugeRegion c K x P₀ P₁)
structure IsLaterStep (k : ℕ) (P Y : Set (FourTorus c.L m)) : Prop where
  one_le : 1 ≤ k
  lt : k < K
  inRange : IsAxialLawRange c.A₀ c.𝔭₀ x k
  isUnion : P ∈ unionsOfTestCubes c K x k (plaquetteTestRegion c K x k Y)
structure IsInitialStep (P₀ P₁ : Set (FourTorus c.L m)) : Prop where
  pos : 0 < K
  inRange : IsAxialLawRange c.A₀ c.𝔭₀ x 0
  densityUnion : ∃ C ⊆ densityPartition c K x 0, P₀ = ⋃₀ C
  isUnion : P₁ ∈ unionsOfTestCubes c K x 0 (initialOuterRegion c K x P₀)
def gaugeMoveAt (Stored : Type) (k : ℕ) [Finite (SiteAtLevel c.L m K k)]
    (O : BondOrientation c.L m K k) (P'' : Set (SiteAtLevel c.L m K (k + 1))) :
    GaugeMoveData.{0} c.L m K k Stored :=
  gaugeMoveOnSet Stored O (shellPoints K k P'') fun _ _ =>
    axialLaw K k P'' (x k) (Thresholds.epsThreshold c.A₀ c.𝔭₀ x k)
def laterStepMove (Stored : Type) (k : ℕ) [Finite (SiteAtLevel c.L m K k)]
    (O : BondOrientation c.L m K k) (P Y : Set (FourTorus c.L m)) :
    GaugeMoveData.{0} c.L m K k Stored :=
  gaugeMoveAt c K x Stored k O (laterGaugeSites c K x k P Y)
def initialStepMove (Stored : Type) [Finite (SiteAtLevel c.L m K 0)]
    (O : BondOrientation c.L m K 0) (P₀ P₁ : Set (FourTorus c.L m)) :
    GaugeMoveData.{0} c.L m K 0 Stored :=
  gaugeMoveAt c K x Stored 0 O (initialGaugeSites c K x P₀ P₁)
end CubesOfStep
end YangMills.Construction.PeriodicLattice
