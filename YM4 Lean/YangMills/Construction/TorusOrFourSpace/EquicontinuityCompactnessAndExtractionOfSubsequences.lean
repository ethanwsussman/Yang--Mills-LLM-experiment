import YangMills.Construction.Sequences.DiagonalSubsequence
import YangMills.Construction.TorusOrFourSpace.ApproximationByMembersOfTheFamily
import YangMills.Construction.TorusOrFourSpace.FactsOnTheRadiusThetaAndUnitFamilies
import YangMills.Construction.TorusOrFourSpace.SignsWrittenOutAgainAndClusterPoints
import YangMills.Construction.TorusOrFourSpace.TheTwoKindsOfSequencesOfC1Forms
import Mathlib
set_option autoImplicit false
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction.PeriodicSpace.EquicontinuityCompactness
section Definitions
variable (D : Params) (E : Kind)
def lipschitzTuplesSupportedIn {n : ℕ} (A : Fin n → Set (E.Pt D)) : Set (Kind.FnTuple D E n) :=
  Kind.productSet D E fun l => {h | Kind.IsLipschitzQ D E h ∧ Kind.supportQ D E h ⊆ A l}
variable {D E}
def tupleBoundsNN {θ : RadiusRatio} (P : Kind.TorusPartitionChoice D θ)
    (F : Kind.DenseChoiceFamily D E) (C : BoundFamily) : F.tuples → NNReal :=
  fun φ => Real.toNNReal (Kind.tupleBound E P C φ.1.2)
def evalMap (F : Kind.DenseChoiceFamily D E) (C : BoundFamily) :
    Kind.boundedHierarchies D E C → F.tuples → ℝ :=
  fun Φ φ => Φ.1.evalSigma φ.1
def LimitsAlong {J₀ : Sequences.PNatIndexSet} {ρ : J₀.carrier → ℝ≥0∞}
    (Φ : Kind.PartialHierarchySeq D E J₀ ρ) {I : Type} (s : I → ℤ)
    (v : ∀ ι : I, {j : ℤ // s ι ≤ j} → ℂ) (J : Sequences.PNatIndexSet)
    (hJ : J.carrier ⊆ J₀.carrier) (w : I → ℂ) (Ξ : Kind.Hierarchy D E) : Prop :=
  (∀ ι, DiagonalLimits.TendsToAlong J (s ι) (DiagonalSubsequence.restrictAlong (v ι) J) (w ι)) ∧
    Φ.TendsToOnSepAlong J hJ Ξ
def IsLimitExtraction {J₀ : Sequences.PNatIndexSet} {ρ : J₀.carrier → ℝ≥0∞}
    (Φ : Kind.PartialHierarchySeq D E J₀ ρ) (C : BoundFamily) {I : Type} (s : I → ℤ)
    (v : ∀ ι : I, {j : ℤ // s ι ≤ j} → ℂ) (J : Sequences.PNatIndexSet)
    (hJ : J.carrier ⊆ J₀.carrier) (Ξ : Kind.Hierarchy D E) : Prop :=
  ∃ w : I → ℂ, LimitsAlong Φ s v J hJ w Ξ ∧
    Ξ ∈ Kind.boundedHierarchies D E C ∧ Ξ.SatisfiesSepEstimate C ∧
    ∀ (J' : Sequences.PNatIndexSet) (hJ' : J'.carrier ⊆ J.carrier),
      LimitsAlong Φ s v J' (hJ'.trans hJ) w Ξ
variable (E)
def extractionDefect {θ : RadiusRatio} (P : Kind.TorusPartitionChoice D θ) (C : BoundFamily)
    {n : ℕ} (f : Kind.FnTuple D E n) (d R' ε : ℝ) : ℝ :=
  Kind.effConstAt P E C n (d / 3) R' * DiagonalLimits.approxDefect D E f ε
variable {E}
def ApproxEstimate {J₀ : Sequences.PNatIndexSet} {ρ : J₀.carrier → ℝ≥0∞}
    (Φ : Kind.PartialHierarchySeq D E J₀ ρ) {θ : RadiusRatio} (P : Kind.TorusPartitionChoice D θ)
    (F : Kind.DenseChoiceFamily D E) (C : BoundFamily) {n : ℕ} (hn : 2 ≤ n) (f : Kind.FnTuple D E n)
    (r d : ℝ) (hd : 0 < d) (ε : ℝ) : Prop :=
  ∃ φ : Kind.FnTuple D E n, (⟨n, φ⟩ : Σ n : ℕ, Fin n → E.Pt D → ℝ) ∈ F.tuples ∧
    (∀ i, Kind.sharpNormQ D E (f i - φ i) ≤ ENNReal.ofReal (40 * D.M * ε) ∧
      Kind.WithinDist D E (Kind.supportQ D E (φ i)) (Kind.supportQ D E (f i)) (d / 3)
        (div_pos hd three_pos)) ∧
    ∃ j₁ : ℤ, ∀ j : J₀.carrier, j₁ ≤ (((j.1 : ℕ+) : ℕ) : ℤ) →
      Φ.IsDefinedAt j f ∧ Φ.IsDefinedAt j φ ∧
        |Φ.evalAt j n hn f - Φ.evalAt j n hn φ| ≤ extractionDefect E P C f d (r + d / 3) ε
end Definitions
section Claims
variable (D : Params) (E : Kind)
def HeadClaims (θ : RadiusRatio) (P : Kind.TorusPartitionChoice D θ) (C : BoundFamily) : Prop :=
  Kind.allowedRadii D Kind.euclidean = Set.Ioi 0 ∧
    Kind.allowedRadii D Kind.torus = Set.Ioo 0 ((D.L : ℝ) ^ (D.m : ℕ) / 2) ∧
    Kind.ballRadius D θ E ∈ Kind.allowedRadii D E ∧
    Kind.thetaNumber P E ∈ Set.Ici (1 : ℝ) ∧
    RadiusThetaDependence ∧
    ∀ (n : ℕ), 2 ≤ n → ∀ d R : ℝ, 0 < d → 0 < R →
      (R ∈ Kind.allowedRadii D E → Kind.effConstAt P E C n d R = C.val n d R) ∧
      (R ∉ Kind.allowedRadii D E → Kind.effConstAt P E C n d R =
        Kind.thetaNumber P E ^ n * C.val n d (Kind.ballRadius D θ E)) ∧
      (E = Kind.euclidean → Kind.effConstAt P E C n d R = C.val n d R)
def EquicontinuityPart (C : BoundFamily) : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (d R : ℝ), 0 < d → ∀ A : Fin n → Set (E.Pt D),
    (∀ l, ∃ S, Kind.IsClosedBallWithRadius D E S R ∧ A l ⊆ S) →
    DiagonalLimits.PairwiseSetDistGe D E A d →
    ∀ Ψ : lipschitzTuplesSupportedIn D E A → ℝ,
      Kind.IsMultilinearOnProduct D E (lipschitzTuplesSupportedIn D E A)
        (fun l => {h | Kind.IsLipschitzQ D E h ∧ Kind.supportQ D E h ⊆ A l}) Ψ →
      (∀ h, ENNReal.ofReal |Ψ h| ≤ ENNReal.ofReal (C.val n d R) * ∏ l, Kind.sharpNormQ D E (h.1 l)) →
      ∀ f g : lipschitzTuplesSupportedIn D E A,
        Kind.EquicontinuityBounds D E (C.val n d R) (Ψ f) (Ψ g) f.1 g.1
def EvalClosedEmbedding {θ : RadiusRatio}
    (P : Kind.TorusPartitionChoice D θ) (F : Kind.DenseChoiceFamily D E) (C : BoundFamily) : Prop :=
  ∃ hMaps : ∀ Φ, evalMap F C Φ ∈ FamilyTopology.intervalBox (tupleBoundsNN P F C),
    FamilyTopology.IsCompactViaCovers
        (FamilyTopology.boxTopology (tupleBoundsNN P F C)) ∧
      FamilyTopology.IsMetrizableVia
        (FamilyTopology.boxTopology (tupleBoundsNN P F C)) ∧
      @Topology.IsClosedEmbedding _ _
        (Kind.sepConvTopology (Kind.boundedHierarchies D E C))
        (FamilyTopology.boxTopology (tupleBoundsNN P F C))
        (fun Φ => ⟨evalMap F C Φ, hMaps Φ⟩)
def CompactnessPart {θ : RadiusRatio} (P : Kind.TorusPartitionChoice D θ)
    (F : Kind.DenseChoiceFamily D E) (C : BoundFamily) : Prop :=
  FamilyTopology.IsCompactViaCovers
      (Kind.sepConvTopology (Kind.boundedHierarchies D E C)) ∧
    FamilyTopology.IsMetrizableVia
      (Kind.sepConvTopology (Kind.boundedHierarchies D E C)) ∧
    Kind.IsSeqClosedHierarchies (Kind.boundedHierarchies D E C) ∧
    (∀ φ ∈ F.tuples, ∀ i, ∃ S, Kind.IsClosedBallWithRadius D E S (Kind.tupleRadius D E φ.2) ∧
      Kind.supportQ D E (φ.2 i) ⊆ S) ∧
    (∀ φ ∈ F.tuples, 0 ≤ Kind.tupleBound E P C φ.2) ∧
    (∀ φ ∈ F.tuples, 2 ≤ φ.1 → Kind.supportGap D E φ.2 < ∞ →
      Kind.tupleBound E P C φ.2 =
        Kind.effConstAt P E C φ.1 (Kind.supportGap D E φ.2).toReal
            (Kind.tupleRadius D E φ.2) *
          ∏ i, Kind.sharpNormReal D E (φ.2 i)) ∧
    EvalClosedEmbedding D E P F C ∧
    Kind.BoundedDeterminedOn F C ∧
    ∀ Φ : ℕ+ → Kind.Hierarchy D E, (∀ j, Φ j ∈ Kind.boundedHierarchies D E C) →
      (Kind.ConvergesOnSep (J := C1FormSeqKinds.allPNat)
          (fun j => Φ j.1) ↔
        ∀ φ ∈ F.tuples, Kind.ConvergesAtSigma Φ φ)
def ExtractionPart {θ : RadiusRatio} (P : Kind.TorusPartitionChoice D θ)
    (F : Kind.DenseChoiceFamily D E) (C : BoundFamily) : Prop :=
  ∀ (J₀ : Sequences.PNatIndexSet) (ρ : J₀.carrier → ℝ≥0∞)
    (Φ : Kind.BoundedPartialHierarchySeq D E J₀ ρ C) (I : Type) [Countable I] (s : I → ℤ)
    (v : ∀ ι : I, {j : ℤ // s ι ≤ j} → ℂ),
    (∀ ι : I, ∃ B : ℝ, ∀ j : {j : ℤ // s ι ≤ j}, ‖v ι j‖ ≤ B) →
    (∃ (J : Sequences.PNatIndexSet) (hJ : J.carrier ⊆ J₀.carrier) (Ξ : Kind.Hierarchy D E),
      IsLimitExtraction Φ.toPartialHierarchySeq C s v J hJ Ξ) ∧
    ∀ (n : ℕ) (hn : 2 ≤ n) (f : Kind.FnTuple D E n), f ∈ Kind.sepC1Tuples D E n →
      ∀ r : ℝ≥0∞, Kind.SupportsInBall D E f r →
      ∀ (d : ℝ) (hd : 0 < d), Kind.IsGapValue D E f d →
        (∀ ε : ℝ, 0 < ε →
          ApproxEstimate Φ.toPartialHierarchySeq P F C hn f r.toReal d hd ε) ∧
        Filter.Tendsto (extractionDefect E P C f d (r.toReal + d / 3)) (𝓝[>] 0) (𝓝 0)
def ClusterPointPart (C : BoundFamily) : Prop :=
  ∀ (J₀ : Sequences.PNatIndexSet) (ρ : J₀.carrier → ℝ≥0∞)
    (Φ : Kind.BoundedPartialHierarchySeq D E J₀ ρ C) (Ξ : Kind.Hierarchy D E),
    Φ.toPartialHierarchySeq.IsClusterHierarchy Ξ →
      (∃ (J : Sequences.PNatIndexSet) (hJ : J.carrier ⊆ J₀.carrier),
        Φ.toPartialHierarchySeq.TendsToOnSepAlong J hJ Ξ) ∧
      Ξ ∈ Kind.boundedHierarchies D E C
end Claims
def Statement : Prop :=
  ∀ (D : Params) (E : Kind) (θ : RadiusRatio) (P : Kind.TorusPartitionChoice D θ)
    (F : Kind.DenseChoiceFamily D E) (C : BoundFamily),
    HeadClaims D E θ P C ∧ EquicontinuityPart D E C ∧ CompactnessPart D E P F C ∧
      ExtractionPart D E P F C ∧ ClusterPointPart D E C
end YangMills.Construction.PeriodicSpace.EquicontinuityCompactness
