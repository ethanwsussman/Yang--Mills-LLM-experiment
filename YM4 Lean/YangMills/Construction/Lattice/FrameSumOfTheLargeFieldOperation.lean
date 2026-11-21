import YangMills.Construction.ClusterExpansion.PolymerPartitionAndClusterSeries
import YangMills.Construction.Lattice.FormsOfCombsTreesGaugesAndProjectionsInAFrame
import YangMills.Construction.Lattice.ListOfTheOperationsOfALevel
import YangMills.Construction.Lattice.PolymerExpansionAndOutputOfTheOperation
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction
open ParameterChoice
namespace PeriodicLattice.FrameAveraging
open CentralBlock LargeFieldCompletion OperationList LargeFieldCourse LargeFieldExpansion
  ComponentReferenceLaw CubesOfStep ClassOperations TermForms
section Course
variable {L m K k : ℕ} {B : Type}
def HasFrameSum (slots : List Slot) (s : OperationState L m K k B)
    (X : Set (FourTorus L m)) : Prop :=
  ∃ i, slots[i]? = some .frameSum ∧ i < (s.performedAt X).length
def frameSumRegions (slots : List Slot) (s : OperationState L m K k B) :
    Set (Set (FourTorus L m)) :=
  {X | (X ∈ s.remaining ∨ X ∈ s.droppedRegions) ∧ HasFrameSum slots s X}
variable {Y : Type}
def statesWithFrames (C : Set (Set (FourTorus L m))) (r : ↥C → SignedFrame) :
    Set (StoredState L m K k Y) :=
  {p | ∀ X : ↥C, p.2.1.2.frame X.1 = r X}
def frameSummand [MeasurableSpace Y] (C : Set (Set (FourTorus L m))) (r : ↥C → SignedFrame)
    (μ : StoredTerm L m K k Y) : StoredTerm L m K k Y :=
  μ.restrict (statesWithFrames C r)
def resultTerm {σ : StateTerm L m K k} {X : Set (FourTorus L m)} (side : Bool) :
    TermOperation σ X → StateTerm L m K k
  | .partition d => if side then d.termχ else d.termCompl
  | .identity i => i.result
  | .equivalence e => e.result
end Course
section LandauInAFrame
variable {L m : ℕ}
def activeRepresentativeInFrame (ε : ℝ) (r : SignedFrame) (K k : ℕ)
    (Ω : ℕ → Set (FourTorus L m)) (V : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2) :
    BondAtLevel L m K 0 → Matrices.ComplexMatrix2 :=
  framedAxialRepresentativeAtOne ε r K k Ω (activeBondSet K k Ω) V
def activeLandauPotentialInFrame (r : SignedFrame) (ξ α ε : ℝ) (K k : ℕ)
    (Ω : ℕ → Set (FourTorus L m)) (V₀ : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2)
    (B : ActiveFamily L m K k Ω) : BondAtLevel L m K 0 → Matrices.ComplexMatrix2 :=
  FrameForms.landauGaugeFormRot r (Averaging.smoothingRadius L) ξ α k Ω
    (activeRepresentativeInFrame ε r K k Ω V₀)
    (activeRepresentativeInFrame ε r K k Ω (expTwistedDatum B V₀))
def activeLandauLinearizationInFrame (r : SignedFrame) (ε ξ α : ℝ) (K k : ℕ)
    (Ω : ℕ → Set (FourTorus L m)) (V₀ : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2)
    (B : ActiveFamily L m K k Ω) : BondAtLevel L m K 0 → Matrices.ComplexMatrix2 :=
  fun b => deriv (fun t : ℝ =>
    activeLandauPotentialInFrame r ξ α ε K k Ω V₀ (((t : ℝ) : ℂ) • B) b) 0
end LandauInAFrame
section Operator
variable (c : ChoiceUpToRadii) {m K : ℕ} {x : ℕ → ℝ} {k : ℕ}
  (S : LabelAtLevel c.toChoiceUpToDegreeConstants m K x k) (Q : Set (Set (FourTorus c.L m)))
  (X : Set (FourTorus c.L m))
def gluedLinearizationInFrame (α : ℝ) (f : SignedFrame) (D₀ B : AllLevelFields c.L m K) :
    BondAtLevel c.L m K 0 → Matrices.ComplexMatrix2 :=
  activeLandauLinearizationInFrame f c.εv (finestMeshInLevelUnits c.L k) α K k
    (gluedTrimmedChain c S Q X) D₀ (familyOnGluedSet c S Q X B)
def componentQuadFormInFrame (α : ℝ) (f : SignedFrame) (D₀ B : AllLevelFields c.L m K) : ℝ :=
  ∑ᶠ p ∈ (plaquettesInside (gluedTrimmedChain c S Q X 0) : Set (PlaquetteAtLevel c.L m K 0)),
    finestMeshInLevelUnits c.L k ^ 4 * combinedCutoff c S Q p.barycenter *
      Matrices.ComplexMatrix2.operatorNorm (covExteriorDeriv (finestMeshInLevelUnits c.L k)
        (activeRepresentativeInFrame c.εv f K k (gluedTrimmedChain c S Q X) D₀)
        (gluedLinearizationInFrame c S Q X α f D₀ B) p.firstAxis p.secondAxis p.origin) ^ 2
variable {N : AnalyticityConstants} (T : StepCompletionData N c m K x k)
def componentExponentInFrame (α : ℝ) (f : SignedFrame) (D₀ V : AllLevelFields c.L m K)
    (Vb VΛ : BondAtLevel c.L m K k → Matrices.ComplexMatrix2) (V' : AllLevelFields c.L m K) : ℂ :=
  -(1 / 2) * (componentQuadFormInFrame c S Q X α f D₀
      (LargeFieldCompletion.fluctuationVariables c S Q V') : ℂ) -
    componentInnerWilson c S Q X V' V +
    resummedPieceAt (stepConstants N c.toChoiceUpToDegreeConstants) T
      (addCubeLayer (coarseCubeIndex K (Nat.log c.L c.M) k) X)
      (completedBackgroundField c S Q V Vb VΛ)
      (LargeFieldCompletion.fluctuationVariables c S Q V')
      (V (outerShellLevel c.toChoiceUpToDegreeConstants x k))
end Operator
section Term
variable {N : AnalyticityConstants} {a : FullChoice} {m K : ℕ} {x : ℕ → ℝ} {E : ℕ → Type}
  {k : ℕ} (t : ClassedTerm N a m K x E k)
def ruleSummand (form : DisplayForm) (α : ℝ)
    (P : (BondAtLevel a.L m K k → Matrices.ComplexMatrix2) ×
      (BondAtLevel a.L m K 0 → Matrices.ComplexMatrix2)) (f : SignedFrame)
    (X : Set (FourTorus a.L m)) : PairOperation a.L m K :=
  fun H R =>
    gaugeFixedIntegral (c := degreeChoice a)
      (t.stepLabel.nestFixedBonds a.r x t.remainingComponents X)
      (nestTreeInFrame (degreeChoice a) t.stepLabel t.remainingComponents X f) fun V₁ =>
        let V' := patchVariables (t.stepLabel.nestFixedBonds a.r x t.remainingComponents X) V₁ R.1
        (fluctuationSmallnessIndicator (degreeChoice a) t.stepLabel t.remainingComponents X V' : ℂ) *
          haarIntegralOn
            (lowerBondsOffDomain (degreeChoice a) x t.stepLabel t.remainingComponents X) R.2
            fun W₁ =>
              (t.componentLowerOp X).integral W₁ fun y =>
                let V := (t.componentLowerOp X).down y ((t.componentLowerOp X).up y W₁)
                (outerShellIndicator (degreeChoice a) t.stepLabel t.remainingComponents
                    (V (outerShellLevel (degreeChoice a) x k))
                    (outerShell (degreeChoice a) t.stepLabel t.remainingComponents X) : ℂ) *
                  (t.componentLowerOp X).factor y V *
                  Complex.exp (componentExponentInFrame (radiiChoice a) t.stepLabel
                      t.remainingComponents X t.completionData α f
                      (displayDatum (radiiChoice a) t.stepLabel t.remainingComponents X form P.2 V)
                      V (relativeVariable t.innerBoxBondSet (V k) P.1) P.1 V' +
                    componentConstants (radiiChoice a) t.stepLabel t.remainingComponents X f
                      t.completionData form) *
                  H (V', V)
def ruleProduct (form : DisplayForm) (α : ℝ)
    (P : (BondAtLevel a.L m K k → Matrices.ComplexMatrix2) ×
      (BondAtLevel a.L m K 0 → Matrices.ComplexMatrix2))
    (ρ : ↥t.remainingComponents → SignedFrame) (C : Set (Set (FourTorus a.L m))) :
    PairOperation a.L m K :=
  composeOperations {Y : ↥t.remainingComponents | Y.1 ∈ C}
    (fun Y => ruleSummand t form α P (ρ Y) Y.1)
end Term
section Output
variable {N : AnalyticityConstants} {a : FullChoice} {m K : ℕ} {x : ℕ → ℝ} {E : ℕ → Type}
  {k : ℕ} (𝒯 : Set (ClassedTerm N a m K x E k)) (t₀ : ClassedTerm N a m K x E k)
  (form : DisplayForm) (α : ℝ) (r : Set (FourTorus a.L m) → SignedFrame)
  (evalOnSigma : ConnectionType)
def domainFirstClass (t : ClassedTerm N a m K x E k) : Set (Set (FourTorus a.L m)) :=
  match evalOnSigma with
  | .literal => t.firstClass
  | .viaCubes => addCubeLayer (termCubeIndex t) '' t.firstClass
def framedTermDecomposition (t : ClassedTerm N a m K x E k)
    (D : Finset (Set (FourTorus a.L m))) : Set (Set (FourTorus a.L m)) :=
  polymerDecomposition K (termCubeIndex t) evalOnSigma t.secondClass (domainFirstClass evalOnSigma t) ↑D
def framedFamiliesWithRegion (t : ClassedTerm N a m K x E k) (X' : Set (FourTorus a.L m)) :
    Set (Finset (Set (FourTorus a.L m))) :=
  {D | ↑D ⊆ expDomains t ∧ framedTermDecomposition evalOnSigma t D = {X'}}
def framedComponentFamilies : Set (Set (Set (FourTorus a.L m))) :=
  {𝒜 | 𝒜.Nonempty ∧ ∃ t ∈ bracketTerms 𝒯 t₀, ∃ D : Finset (Set (FourTorus a.L m)),
    ↑D ⊆ expDomains t ∧ framedTermDecomposition evalOnSigma t D = 𝒜}
def framedPolymerSet : Set (Set (FourTorus a.L m)) :=
  {X' | ({X'} : Set (Set (FourTorus a.L m))) ∈ framedComponentFamilies 𝒯 t₀ evalOnSigma}
def framedPolymerRelation [Fintype ↥(framedPolymerSet 𝒯 t₀ evalOnSigma)] :
    ClusterExpansion.PolymerRelation ↥(framedPolymerSet 𝒯 t₀ evalOnSigma) where
  Related Z Z' := Z = Z' ∨
    ({Z.1, Z'.1} : Set (Set (FourTorus a.L m))) ∉ framedComponentFamilies 𝒯 t₀ evalOnSigma
  refl _ := Or.inl rfl
  symm Z Z' := by rw [eq_comm, Set.pair_comm]
def framedActivity (X' : Set (FourTorus a.L m)) (R : FluctuationFieldPair a.L m K) : ℂ :=
  ∑ᶠ C ∈ ClassedTerm.firstClass '' bracketTerms 𝒯 t₀,
    ∑ᶠ t ∈ {t | t ∈ bracketTerms 𝒯 t₀ ∧ t.firstClass = C},
      frameAverage t.firstClass fun ρ =>
        ∑ᶠ D ∈ framedFamiliesWithRegion evalOnSigma t X',
          ∫ τ in Icc (0 : ↥D → ℝ) 1,
            ruleProduct t form α (termPair t α r ρ R) (termFrames t r ρ) t.firstClass
              (mayerIntegrand t (termPair t α r ρ R).1 D τ) R
def framedClusterSum (X : Set (FourTorus a.L m)) (R : FluctuationFieldPair a.L m K) : ℂ :=
  open Classical in
  if h : (framedPolymerSet 𝒯 t₀ evalOnSigma).Finite then
    letI := h.fintype
    (framedPolymerRelation 𝒯 t₀ evalOnSigma).fiberSum
      (ClusterExpansion.PolymerRelation.supportUnion
        (Function.Embedding.subtype (· ∈ framedPolymerSet 𝒯 t₀ evalOnSigma))) X
      fun Z => framedActivity 𝒯 t₀ form α r evalOnSigma Z.1 R
  else 0
end Output
end PeriodicLattice.FrameAveraging
end YangMills.Construction
