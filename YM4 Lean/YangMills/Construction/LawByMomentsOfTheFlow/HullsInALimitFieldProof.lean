import YangMills.Construction.HullsInEveryVolume.LocalHullLiesInTheHull
import YangMills.Construction.HullsInEveryVolume.MeansOfTheLaw
import YangMills.Construction.HullsInEveryVolume.MeansOfTheLocalHull
import YangMills.Construction.HullsInEveryVolume.MomentOfTheLocalHull
import YangMills.Construction.HullsInEveryVolume.NoisesCarryTheChain
import YangMills.Construction.HullsInEveryVolume.RatesOfTheMoments
import YangMills.Construction.HullsInEveryVolume.ReachOfTheLocalHull
import YangMills.Construction.HullsInEveryVolume.SitesBelowACellProof
import YangMills.Construction.HullsInEveryVolume.TheChainOfTheNoisesIsBorel
import YangMills.Construction.LawByMomentsOfTheFlow.BandsBoundAStarMean
import YangMills.Construction.LawByMomentsOfTheFlow.EveryMthCopyBoundsALimitField
import YangMills.Construction.LawByMomentsOfTheFlow.HullsClearOfThePointInALimitFieldProof
import YangMills.Construction.LawByMomentsOfTheFlow.MeanOverSeparateCells
import YangMills.Construction.LawByMomentsOfTheFlow.MomentsAlongTheTelescopeProof
import YangMills.Construction.LawByMomentsOfTheFlow.SeveralLongClassesOnATorus
import YangMills.Construction.LawByMomentsOfTheFlow.TranslationsMoveTheHull
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace YangMills.Construction.MomentLaw
open YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.RenormalizationStepParameters YangMills.Construction.StepSettings YangMills.Construction.StepReturn YangMills.Construction.WeightedResponses YangMills.Construction.ResponseInTheExpansion YangMills.Construction.HullTrees YangMills.Construction.ChainNoise YangMills.Construction.ChessboardGrids YangMills.Construction.TorusLimits YangMills.Construction.MomentMethod YangMills.Construction.LevelTestFunctions
open YangMills.Construction.HullsInEveryVolume renaming holderExponentAtBand → holderBandExponent,
  dyadicDiameterFloor → dyadicBandFloor
section Pairs
variable {ℓ : StepParameters}
private def restrictPair (ℓ : StepParameters) (u : ℕ) : (d n : ℕ) →
    TorusField (fineSide ℓ.side (u + d) n) × ChainNoise.ChainNoise ℓ (u + d) n →
    TorusField (fineSide ℓ.side u (fineSide ℓ.side d n)) × ChainNoise.ChainNoise ℓ u (fineSide ℓ.side d n)
  | 0, _, p => p
  | d + 1, n, p => restrictPair ℓ u d (n * ℓ.side) (p.1, p.2.1)
private theorem chain_restrictPair (rule : NoiseRule ℓ) (T : StageTower ℓ) (u : ℕ) :
    ∀ (d n : ℕ) [NeZero n] (p : TorusField (fineSide ℓ.side (u + d) n) × ChainNoise.ChainNoise ℓ (u + d) n),
      sampleBelow ℓ u d n (rule.chain T (u + d) n p.1 p.2) =
        rule.chain T u (fineSide ℓ.side d n) (restrictPair ℓ u d n p).1 (restrictPair ℓ u d n p).2
  | 0, _, _, _ => rfl
  | d + 1, n, _, p => chain_restrictPair rule T u d (n * ℓ.side) (p.1, p.2.1)
private theorem restrictPair_translate (u : ℕ) : ∀ (d n : ℕ) [NeZero n] (h : Fin 4 → ℤ)
    (p : TorusField (fineSide ℓ.side (u + d) n) × ChainNoise.ChainNoise ℓ (u + d) n),
    restrictPair ℓ u d n (pairTranslate ℓ (u + d) n h p) =
      pairTranslate ℓ u (fineSide ℓ.side d n) (fun i => (ℓ.side : ℤ) ^ d * h i) (restrictPair ℓ u d n p)
  | 0, n, _, h, p => by
    simp only [pow_zero, one_mul]
    rfl
  | d + 1, n, _, h, p => by
    have hpair : ((pairTranslate ℓ (u + (d + 1)) n h p).1, (pairTranslate ℓ (u + (d + 1)) n h p).2.1) =
        pairTranslate ℓ (u + d) (n * ℓ.side) (fun i => (ℓ.side : ℤ) * h i) (p.1, p.2.1) := by
      refine Prod.ext ?_ rfl
      have hvec : (fun i => (ℓ.side : ℤ) ^ (u + (d + 1)) * h i) =
          fun i => (ℓ.side : ℤ) ^ (u + d) * ((ℓ.side : ℤ) * h i) := by
        funext i
        rw [← add_assoc, pow_succ]
        ring
      show TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) ^ (u + (d + 1)) * h i) p.1 =
        TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) ^ (u + d) * ((ℓ.side : ℤ) * h i)) p.1
      rw [hvec]
    have hpow : (fun i => (ℓ.side : ℤ) ^ d * ((ℓ.side : ℤ) * h i)) = fun i => (ℓ.side : ℤ) ^ (d + 1) * h i := by
      funext i
      rw [pow_succ]
      ring
    have hrec := restrictPair_translate u d (n * ℓ.side) (fun i => (ℓ.side : ℤ) * h i) (p.1, p.2.1)
    rw [hpow] at hrec
    exact (congrArg (restrictPair ℓ u d (n * ℓ.side)) hpair).trans hrec
private def pairAtStage (ℓ : StepParameters) {K u d : ℕ} (hd : u + d = K) (n : ℕ)
    (p : TorusField (fineSide ℓ.side K n) × ChainNoise.ChainNoise ℓ K n) :
    TorusField (fineSide ℓ.side u (fineSide ℓ.side d n)) × ChainNoise.ChainNoise ℓ u (fineSide ℓ.side d n) :=
  restrictPair ℓ u d n (hd.symm ▸ p)
private theorem sampleBelow_pairAtStage (rule : NoiseRule ℓ) (T : StageTower ℓ) {K u d : ℕ} (hd : u + d = K) (n : ℕ)
    [NeZero n] (p : TorusField (fineSide ℓ.side K n) × ChainNoise.ChainNoise ℓ K n) :
    sampleBelow ℓ u d n (hd.symm ▸ rule.chain T K n p.1 p.2) =
      rule.chain T u (fineSide ℓ.side d n) (pairAtStage ℓ hd n p).1 (pairAtStage ℓ hd n p).2 := by
  subst hd
  exact chain_restrictPair rule T u d n p
private theorem pairAtStage_translate {K u d : ℕ} (hd : u + d = K) (n : ℕ) [NeZero n] (h : Fin 4 → ℤ)
    (p : TorusField (fineSide ℓ.side K n) × ChainNoise.ChainNoise ℓ K n) :
    pairAtStage ℓ hd n (pairTranslate ℓ K n h p) =
      pairTranslate ℓ u (fineSide ℓ.side d n) (fun i => (ℓ.side : ℤ) ^ d * h i) (pairAtStage ℓ hd n p) := by
  subst hd
  exact restrictPair_translate u d n h p
private theorem sampleBelow_law (hfit : ℓ.Admissible) (hgt : 11 * 2 ^ 12 * ℓ.baseDepth < ℓ.side)
    (hLaw : sampleBelowLawStatement) (T : StageTower ℓ)
    (hcut : ColdStepAtMirrorFrames.IsCutoff (ℓ.threshold / 64) T.base.barrierFn) (hco : T.MarksMeasurable) (β : ℝ)
    {K u d : ℕ} (hd : u + d = K) (n : ℕ) [NeZero n] :
    Measurable (fun w : MarkedSample ℓ K n => sampleBelow ℓ u d n (hd.symm ▸ w)) ∧
      (markedSampleLaw T β K n).map (fun w : MarkedSample ℓ K n => sampleBelow ℓ u d n (hd.symm ▸ w)) =
        markedSampleLaw T β u (fineSide ℓ.side d n) := by apply _root_.YangMills.SharedProofs.p37385 <;> assumption
end Pairs
section Classes
variable {n : ℕ} [NeZero n]
private theorem supDist_add_right (a x y : TorusSite n) :
    TorusFields.supDist (x + a) (y + a) = TorusFields.supDist x y := by
  simp [TorusFields.supDist]
private theorem chainConnected_add {r : ℕ} {Y Y' : Finset (TorusSite n)} {a : TorusSite n}
    (h : ∀ x, x ∈ Y' ↔ x + a ∈ Y) {z w : TorusSite n}
    (hj : ChainConnected r Y' z w) : ChainConnected r Y (z + a) (w + a) := by
  unfold ChainConnected at hj ⊢
  induction hj with
  | refl => exact .refl
  | tail _ hs ih =>
    obtain ⟨hu, hv, huv⟩ := hs
    exact ih.tail ⟨(h _).1 hu, (h _).1 hv, by rwa [supDist_add_right]⟩
private theorem chainConnected_sub {r : ℕ} {Y Y' : Finset (TorusSite n)} {a : TorusSite n}
    (h : ∀ x, x ∈ Y' ↔ x + a ∈ Y) {z w : TorusSite n}
    (hj : ChainConnected r Y (z + a) w) : ChainConnected r Y' z (w - a) := by
  have h' : ∀ x, x ∈ Y ↔ x + (-a) ∈ Y' := fun x => by
    rw [h]
    simp
  have hneg := chainConnected_add h' hj
  simpa [sub_eq_add_neg] using hneg
private theorem supDiam_hullClass_add (r : ℕ) {Y Y' : Finset (TorusSite n)} {a : TorusSite n}
    (h : ∀ x, x ∈ Y' ↔ x + a ∈ Y) (z : TorusSite n) :
    supDiam (hullClass r Y' z) = supDiam (hullClass r Y (z + a)) := by
  classical
  have himg : hullClass r Y (z + a) = (hullClass r Y' z).image fun x => x + a := by
    ext w
    simp only [hullClass, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨w - a, ⟨(h _).2 (by simpa using h1), chainConnected_sub h h2⟩, by simp⟩
    · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
      exact ⟨(h _).1 h1, chainConnected_add h h2⟩
  rw [himg]
  simp only [supDiam, Finset.sup_image, Function.comp_def, supDist_add_right]
private theorem le_supDist_axis (x : TorusSite n) (t : ℕ) (ht : t ≤ n / 2) :
    t ≤ TorusFields.supDist (x + (siteOfInt (Pi.single 0 (t : ℤ)) : TorusSite n)) x := by
  obtain ⟨y, hy⟩ : ∃ y : TorusSite n, y = x + siteOfInt (Pi.single 0 (t : ℤ)) := ⟨_, rfl⟩
  rw [← hy]
  have h1 : ((y 0 - x 0).valMinAbs).natAbs ≤ TorusFields.supDist y x :=
    Finset.le_sup (f := fun i => ((y i - x i).valMinAbs).natAbs) (Finset.mem_univ 0)
  have h2 : y 0 - x 0 = ((t : ℕ) : ZMod n) := by
    rw [hy]
    simp [siteOfInt]
  rw [h2, ZMod.valMinAbs_natCast_of_le_half ht] at h1
  simpa using h1
private theorem nsmul_siteOfInt (k : ℕ) (v : Fin 4 → ℤ) :
    k • (siteOfInt v : TorusSite n) = siteOfInt (fun i => (k : ℤ) * v i) := by
  funext i
  simp [siteOfInt]
end Classes
section Point
variable {Λ : MomentParameters} (S : MomentPoint Λ)
private theorem stage_coupling_eq {j : ℕ} (hj : j ≤ S.data.windowLevel + 1) :
    (S.tower.stage j).coupling = (couplingFlow (Λ.table.stepParameters Λ.floor) S.β j).1 := by apply _root_.YangMills.SharedProofs.p30777 <;> assumption
private theorem hullChain_of_point (hg : 0 < Λ.g) (hy : Λ.floor ≤ (Λ.g ^ 2)⁻¹) :
    HullChain Λ.table Λ.floor Λ.g S.β S.data.windowLevel S.data.sideExponent S.tower := by apply _root_.YangMills.SharedProofs.p4319 <;> assumption
private theorem hullChainAtLevel_of_point (hg : 0 < Λ.g) (hy : Λ.floor ≤ (Λ.g ^ 2)⁻¹) {u : ℕ}
    (hu : u ≤ S.data.windowLevel) :
    HullChainAtLevel Λ.table Λ.floor Λ.g S.β S.data.windowLevel S.data.sideExponent S.tower u (S.sideAtLevel u) :=
  ⟨hullChain_of_point S hg hy, hu, rfl⟩
private abbrev stagePair (u : ℕ) (hu : u ≤ S.data.windowLevel) (ω : S.SampleSpace) :
    TorusField (fineSide Λ.stepParams.side u (S.sideAtLevel u)) × ChainNoise.ChainNoise Λ.stepParams u (S.sideAtLevel u) :=
  pairAtStage Λ.stepParams (Nat.add_sub_of_le hu) (S.data.period Λ.stepParams.side) ω
private theorem sampleAtLevel_eq (rule : NoiseRule Λ.stepParams) {u : ℕ} (hu : u ≤ S.data.windowLevel)
    (ω : S.SampleSpace) :
    S.sampleAtLevel u hu (S.sampleOf rule ω) =
      rule.chain S.tower u (S.sideAtLevel u) (stagePair S u hu ω).1 (stagePair S u hu ω).2 :=
  sampleBelow_pairAtStage rule S.tower (Nat.add_sub_of_le hu) _ ω
private def translationStep (L p d : ℕ) : ℕ := L * (L ^ d * p)
private def axisDisplacement (L p d : ℕ) : Fin 4 → ℤ := Pi.single 0 ((L : ℤ) ^ d * (p : ℤ))
private theorem scaled_translationVector (L p d : ℕ) :
    (fun i => (L : ℤ) ^ d * translationVector L p i) = fun i => (L : ℤ) * axisDisplacement L p d i := by
  funext i
  by_cases h : i = 0
  · subst h
    simp [translationVector, axisDisplacement]
    ring
  · simp [translationVector, axisDisplacement, h]
private theorem siteOfInt_axisDisplacement (L p d : ℕ) (n : ℕ) :
    (siteOfInt (fun i => (L : ℤ) * axisDisplacement L p d i) : TorusSite n) =
      siteOfInt (Pi.single 0 ((translationStep L p d : ℕ) : ℤ)) := by
  congr 1
  funext i
  by_cases h : i = 0
  · subst h
    simp [axisDisplacement, translationStep]
  · simp [axisDisplacement, h]
private abbrev stageTranslation (u p : ℕ) : TorusSite (S.sideAtLevel u) :=
  siteOfInt (fun i => (Λ.stepParams.side : ℤ) * axisDisplacement Λ.stepParams.side p (S.data.windowLevel - u) i)
private abbrev sampleTranslate (p : ℕ) : S.SampleSpace → S.SampleSpace :=
  pairTranslate Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)
    (translationVector Λ.stepParams.side p)
private theorem stagePair_translate {u : ℕ} (hu : u ≤ S.data.windowLevel) (p : ℕ) (ω : S.SampleSpace) :
    stagePair S u hu (sampleTranslate S p ω) =
      pairTranslate Λ.stepParams u (S.sideAtLevel u)
        (fun i => (Λ.stepParams.side : ℤ) * axisDisplacement Λ.stepParams.side p (S.data.windowLevel - u) i)
        (stagePair S u hu ω) := by
  show pairAtStage Λ.stepParams _ _ (pairTranslate Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)
    (translationVector Λ.stepParams.side p) ω) = _
  rw [pairAtStage_translate, scaled_translationVector]
private theorem iterate_translate {α : Type} {u : ℕ} (hu : u ≤ S.data.windowLevel) (p : ℕ)
    (Ψ : TorusSite (S.sideAtLevel u) →
      (TorusField (fineSide Λ.stepParams.side u (S.sideAtLevel u)) ×
        ChainNoise.ChainNoise Λ.stepParams u (S.sideAtLevel u)) → α)
    (h : ∀ y q, Ψ y (pairTranslate Λ.stepParams u (S.sideAtLevel u)
      (fun i => (Λ.stepParams.side : ℤ) * axisDisplacement Λ.stepParams.side p (S.data.windowLevel - u) i) q) =
        Ψ (y + stageTranslation S u p) q) :
    ∀ (k : ℕ) (y : TorusSite (S.sideAtLevel u)) (ω : S.SampleSpace),
      Ψ y (stagePair S u hu ((sampleTranslate S p)^[k] ω)) = Ψ (y + k • stageTranslation S u p) (stagePair S u hu ω) := by
  intro k
  induction k with
  | zero =>
    intro y ω
    simp
  | succ k ih =>
    intro y ω
    rw [Function.iterate_succ_apply, ih, stagePair_translate, h, succ_nsmul, add_assoc]
end Point
section Facts
private def BandRateBound (Λ : MomentParameters) (CE : ParameterAssignment → ℝ) (C : ℝ) : Prop :=
  ∀ (β : ℝ) (K m : ℕ) (T : StageTower Λ.stepParams) (u n : ℕ) [NeZero n],
    HullChainAtLevel Λ.table Λ.floor Λ.g β K m T u n →
    (∀ i, 2 ≤ holderBandExponent Λ.table.side (stageRange T u) i) ∧ ∀ (k I : ℕ) (q : ℕ → ℝ), 1 ≤ k →
      (∀ i, q i ≤ ((Λ.table.side : ℝ) * (16 * (2 ^ i * (stageRange T u : ℝ)) + 40 * (stageRange T u : ℝ))) ^ 4) →
      ∑ i ∈ Finset.range I,
          (16 ^ (k * holderBandExponent Λ.table.side (stageRange T u) i) *
            ((k * holderBandExponent Λ.table.side (stageRange T u) i).factorial : ℝ) *
            Real.exp (|CE Λ.table| * Real.log (stageCoupling T u) * q i)) ^
              (1 / (holderBandExponent Λ.table.side (stageRange T u) i : ℝ)) *
          (Real.exp (-(hullDecayRate Λ.table * stageCoupling T u *
            (1 + dyadicBandFloor (stageRange T u) i / (stageRange T u : ℝ))))) ^
            (1 - 1 / (holderBandExponent Λ.table.side (stageRange T u) i : ℝ)) ≤
        C ^ k * (k.factorial : ℝ) ^ 6 * Real.exp (-(hullDecayRate Λ.table * stageCoupling T u / 4))
private structure LimitHullInputs (Λ : MomentParameters) (CE : ParameterAssignment → ℝ) : Prop where
  drawn : Λ.table.Admissible
  fit : Λ.stepParams.Admissible
  g_pos : 0 < Λ.g
  floor : Λ.floor ≤ (Λ.g ^ 2)⁻¹
  one_le : 1 ≤ Λ.floor
  s_nonneg : 0 ≤ Λ.response.s₁
  coupling_ge : ∀ (g β : ℝ) (K m : ℕ) (T : StageTower Λ.stepParams) (u n : ℕ) [NeZero n],
    HullChainAtLevel Λ.table Λ.floor g β K m T u n → Λ.floor ≤ stageCoupling T u
  classes : ∀ (g β : ℝ) (K m : ℕ) (T : StageTower Λ.stepParams) (u n : ℕ) [NeZero n],
    HullChainAtLevel Λ.table Λ.floor g β K m T u n →
    ∀ (q : ℕ) (zs : Fin q → TorusSite n) (D : ℝ), 1 ≤ q → 0 ≤ D →
      (∀ c e, c ≠ e → 83 * stageRange T u * keptSitesAlong D (stageRange T u) ≤
        TorusFields.supDist (zs c) (zs e)) →
      (markedSampleLaw T β u n).real {w | ∀ e, zs e ∈ hullSet T u n w ∧
          D ≤ (supDiam (hullClass (stageRange T u) (hullSet T u n w) (zs e)) : ℝ)} ≤
        Real.exp (-(hullDecayRate Λ.table * stageCoupling T u * (1 + D / (stageRange T u : ℝ)))) ^ q
  moves : ∀ (g β : ℝ) (K m : ℕ) (T : StageTower Λ.stepParams) (u n : ℕ) [NeZero n],
    HullChainAtLevel Λ.table Λ.floor g β K m T u n →
    ∀ rule : NoiseRule Λ.stepParams, rule.IsAdmissible T → ∀ (z : TorusSite n) (w : Fin 4 → ℤ)
      (p : TorusField (fineSide Λ.stepParams.side u n) × ChainNoise.ChainNoise Λ.stepParams u n),
      z ∈ hullSet T u n (rule.chain T u n (pairTranslate Λ.stepParams u n (fun i => (Λ.stepParams.side : ℤ) * w i) p).1
          (pairTranslate Λ.stepParams u n (fun i => (Λ.stepParams.side : ℤ) * w i) p).2) ↔
        z + siteOfInt (fun i => (Λ.stepParams.side : ℤ) * w i) ∈ hullSet T u n (rule.chain T u n p.1 p.2)
  reach : ∀ (g β : ℝ) (K m : ℕ) (T : StageTower Λ.stepParams) (u n : ℕ) [NeZero n],
    HullChainAtLevel Λ.table Λ.floor g β K m T u n →
    ∀ rule : NoiseRule Λ.stepParams, rule.IsAdmissible T → ∀ (z : TorusSite n) (D : ℝ) (k : ℕ), 0 < D → 1 ≤ k →
      DependsAbove Λ.stepParams u n (box z (⌊2 * D⌋₊ + 6 * stageRange T u))
        (localScore rule T Λ.response.s₁ u n z D k) ∧
      ∀ (h : Fin 4 → ℤ) (p : TorusField (fineSide Λ.stepParams.side u n) × ChainNoise.ChainNoise Λ.stepParams u n),
        localScore rule T Λ.response.s₁ u n z D k
            (pairTranslate Λ.stepParams u n (fun i => (Λ.stepParams.side : ℤ) * h i) p) =
          localScore rule T Λ.response.s₁ u n (z + siteOfInt fun i => (Λ.stepParams.side : ℤ) * h i) D k p
  carries : ∀ (g β : ℝ) (K m : ℕ) (T : StageTower Λ.stepParams), HullChain Λ.table Λ.floor g β K m T →
    (∃ rule : NoiseRule Λ.stepParams, rule.IsAdmissible T) ∧
    ∀ rule : NoiseRule Λ.stepParams, rule.IsAdmissible T → ∀ (u n : ℕ) [NeZero n],
      HullChainAtLevel Λ.table Λ.floor g β K m T u n →
      ((wilsonLaw β (fineSide Λ.stepParams.side u n)).prod (chainNoiseLaw Λ.stepParams u n)).map
          (fun p => rule.chain T u n p.1 p.2) = markedSampleLaw T β u n
  lies : ∀ (g β : ℝ) (K m : ℕ) (T : StageTower Λ.stepParams),
    (∀ (u n : ℕ) [NeZero n], HullChainAtLevel Λ.table Λ.floor g β K m T u n → ∀ w : MarkedSample Λ.stepParams u n,
      (∀ Q : Finset (TorusSite n), (localHullData T Λ.response.s₁ u n w Q).1 ⊆ hullSet T u n w ∧
        ∀ z ∈ (localHullData T Λ.response.s₁ u n w Q).1,
          (localHullData T Λ.response.s₁ u n w Q).2 z ≤ siteSize T Λ.response.s₁ u n w z) ∧
      ∀ (z : TorusSite n) (D : ℝ), 0 < D → z ∈ hullSet T u n w →
        ((supDiam (hullClass (stageRange T u) (hullSet T u n w) z) : ℕ) : ℝ) < D →
        z ∈ (localHullData T Λ.response.s₁ u n w (localHullBox T u z D)).1 ∧
          (localHullData T Λ.response.s₁ u n w (localHullBox T u z D)).2 z = siteSize T Λ.response.s₁ u n w z) ∧
    ∀ (j n : ℕ) [NeZero n], HullChainAtLevel Λ.table Λ.floor g β K m T (j + 1) n →
      ∀ (w : MarkedSample Λ.stepParams (j + 1) n) (Q : Finset (TorusSite n)),
        localCoreZone T Λ.response.s₁ j n w Q ⊆ coreZone T j n w
  rates : ∃ C : ℝ, 1 ≤ C ∧ BandRateBound Λ CE C
  moment : ∀ (g β : ℝ) (K m : ℕ) (T : StageTower Λ.stepParams) (u n : ℕ) [NeZero n],
    HullChainAtLevel Λ.table Λ.floor g β K m T u n →
    ∀ rule : NoiseRule Λ.stepParams, rule.IsAdmissible T → ∀ (z : TorusSite n) (D : ℝ) (k : ℕ), 0 < D → 1 ≤ k →
      (∀ g : MirrorGrid, g.side = leastPowerAbove Λ.stepParams.side ⌈16 * D + 40 * (stageRange T u : ℝ)⌉₊ →
        2 * g.side ≤ n →
        ∀ c : Fin 4 → ℕ, c ∈ g.cellIndices n → box z (⌊2 * D⌋₊ + 6 * stageRange T u) ⊆ g.cellSites n c →
          ∀ M₀ : ℝ, 0 < M₀ →
          (g.atDepth Λ.stepParams.side u).chessboardNormAt β (fineSide Λ.stepParams.side u n) c
              (noiseExpectation Λ.stepParams u n fun p => min (localScore rule T Λ.response.s₁ u n z D k p) M₀) ≤
            16 ^ k * (k.factorial : ℝ) * Real.exp (CE Λ.table * Real.log (stageCoupling T u) * (g.side : ℝ) ^ 4)) ∧
      ∫ w, localScoreMoment T Λ.response.s₁ u n z D k w ∂(markedSampleLaw T β u n) ≤
        16 ^ k * (k.factorial : ℝ) * Real.exp (CE Λ.table * Real.log (stageCoupling T u) *
          ((Λ.stepParams.side : ℝ) * (16 * D + 40 * (stageRange T u : ℝ))) ^ 4)
variable {Λ : MomentParameters} {CE : ParameterAssignment → ℝ}
private theorem sampleAtLevel_law (hF : LimitHullInputs Λ CE) (hLaw : sampleBelowLawStatement)
    (hDraw : forgetLastStepStatement) (S : MomentPoint Λ) {rule : NoiseRule Λ.stepParams}
    (hrule : rule.IsAdmissible S.tower) {u : ℕ} (hu : u ≤ S.data.windowLevel) :
    AEMeasurable (fun ω => S.sampleAtLevel u hu (S.sampleOf rule ω)) S.sampleLaw ∧
      S.sampleLaw.map (fun ω => S.sampleAtLevel u hu (S.sampleOf rule ω)) =
        markedSampleLaw S.tower S.β u (S.sideAtLevel u) := by
  have hgt : 11 * 2 ^ 12 * Λ.stepParams.baseDepth < Λ.stepParams.side := hF.drawn.L_gt
  have hrun := hullChain_of_point S hF.g_pos hF.floor
  have hAtK : HullChainAtLevel Λ.table Λ.floor Λ.g S.β S.data.windowLevel S.data.sideExponent S.tower
      S.data.windowLevel (S.data.period Λ.stepParams.side) := ⟨hrun, le_rfl, by
    show S.data.period Λ.stepParams.side =
      fineSide Λ.table.side (S.data.windowLevel - S.data.windowLevel) (2 * Λ.table.side ^ S.data.sideExponent)
    rw [Nat.sub_self]
    rfl⟩
  have hprob : IsProbabilityMeasure (markedSampleLaw S.tower S.β S.data.windowLevel (S.data.period Λ.stepParams.side)) :=
    (hDraw _ hF.fit hgt S.tower S.isCutoff S.marksMeasurable S.β _ _).1
  have hc : S.sampleLaw.map (S.sampleOf rule) =
      markedSampleLaw S.tower S.β S.data.windowLevel (S.data.period Λ.stepParams.side) :=
    (hF.carries Λ.g S.β S.data.windowLevel S.data.sideExponent S.tower hrun).2 rule hrule _ _ hAtK
  have hm : AEMeasurable (S.sampleOf rule) S.sampleLaw :=
    AEMeasurable.of_map_ne_zero (by rw [hc]; exact IsProbabilityMeasure.ne_zero _)
  obtain ⟨h1, h2⟩ := sampleBelow_law hF.fit hgt hLaw S.tower S.isCutoff S.marksMeasurable S.β
    (Nat.add_sub_of_le hu) (S.data.period Λ.stepParams.side)
  refine ⟨h1.comp_aemeasurable hm, ?_⟩
  have h3 := AEMeasurable.map_map_of_aemeasurable (μ := S.sampleLaw) (f := S.sampleOf rule)
    (by rw [hc]; exact h1.aemeasurable) hm
  rw [hc, h2] at h3
  exact h3.symm
private def IsLongAt {ℓ : StepParameters} (T : StageTower ℓ) (u n : ℕ) [NeZero n] (D : ℝ) (y : TorusSite n)
    (w : MarkedSample ℓ u n) : Prop :=
  y ∈ hullSet T u n w ∧ D ≤ (supDiam (hullClass (stageRange T u) (hullSet T u n w) y) : ℝ)
private theorem measurableSet_hullSet_pred {ℓ : StepParameters} (hfit : ℓ.Admissible)
    (hSt : StageStatesMeasurableStatement) (T : StageTower ℓ) (t n : ℕ) [NeZero n]
    (Q : Finset (TorusSite n) → Prop) :
    MeasurableSet {w : MarkedSample ℓ t n | Q (hullSet T t n w)} := by
  have hB := hSt ℓ hfit T t n
  have hE0 : MeasurableSet {z : Σ Y : Finset (TorusSite n), (Y → (T.stage t).labels.Ω) | Q z.1} :=
    measurableSet_setOfPred.2 (TiltedSquares.measurable_sigma_of_fibres
      (f := fun z : Σ Y : Finset (TorusSite n), (Y → (T.stage t).labels.Ω) => Q z.1) fun a => by
        show Measurable fun _ => Q a
        exact measurable_const)
  have hEm : MeasurableSet {q : StageState T t n | Q q.2.1} := measurable_snd hE0
  exact hB hEm
private theorem largeHullIndicator_eq_pair (S : MomentPoint Λ) (rule : NoiseRule Λ.stepParams) {u : ℕ}
    (hu : u ≤ S.data.windowLevel) (z : Fin 4 → ℤ) (D : ℝ) (ω : S.SampleSpace) : open Classical in
    largeHullIndicator u z D S (S.sampleOf rule ω) =
      if IsLongAt S.tower u (S.sideAtLevel u) D (S.siteAt u z)
        (rule.chain S.tower u (S.sideAtLevel u) (stagePair S u hu ω).1 (stagePair S u hu ω).2) then 1 else 0 := by
  classical
  have e := sampleAtLevel_eq S rule hu ω
  unfold largeHullIndicator
  rw [dif_pos hu]
  split_ifs with h1 h2 h2
  · rfl
  · have h3 : IsLongAt S.tower u (S.sideAtLevel u) D (S.siteAt u z) (S.sampleAtLevel u hu (S.sampleOf rule ω)) := h1
    rw [e] at h3
    exact absurd h3 h2
  · rw [← e] at h2
    exact absurd h2 h1
  · rfl
private theorem isLongAt_translate (hF : LimitHullInputs Λ CE) (S : MomentPoint Λ) {rule : NoiseRule Λ.stepParams}
    (hrule : rule.IsAdmissible S.tower) {u : ℕ} (hu : u ≤ S.data.windowLevel) (p : ℕ) (D : ℝ)
    (y : TorusSite (S.sideAtLevel u))
    (q : TorusField (fineSide Λ.stepParams.side u (S.sideAtLevel u)) ×
      ChainNoise.ChainNoise Λ.stepParams u (S.sideAtLevel u)) :
    IsLongAt S.tower u (S.sideAtLevel u) D y (rule.chain S.tower u (S.sideAtLevel u)
        (pairTranslate Λ.stepParams u (S.sideAtLevel u)
          (fun i => (Λ.stepParams.side : ℤ) * axisDisplacement Λ.stepParams.side p (S.data.windowLevel - u) i) q).1
        (pairTranslate Λ.stepParams u (S.sideAtLevel u)
          (fun i => (Λ.stepParams.side : ℤ) * axisDisplacement Λ.stepParams.side p (S.data.windowLevel - u) i) q).2) =
      IsLongAt S.tower u (S.sideAtLevel u) D (y + stageTranslation S u p) (rule.chain S.tower u (S.sideAtLevel u) q.1 q.2) := by
  have hm := fun x => hF.moves Λ.g S.β S.data.windowLevel S.data.sideExponent S.tower u (S.sideAtLevel u)
    (hullChainAtLevel_of_point S hF.g_pos hF.floor hu) rule hrule x
    (axisDisplacement Λ.stepParams.side p (S.data.windowLevel - u)) q
  apply propext
  unfold IsLongAt
  rw [supDiam_hullClass_add _ hm y]
  exact and_congr_left' (hm y)
private theorem longClasses_integral_le (hF : LimitHullInputs Λ CE) (hLaw : sampleBelowLawStatement)
    (hDraw : forgetLastStepStatement) (hSt : StageStatesMeasurableStatement) (S : MomentPoint Λ)
    {rule : NoiseRule Λ.stepParams} (hrule : rule.IsAdmissible S.tower) {u : ℕ}
    (hu : u ≤ S.data.windowLevel) (z : Fin 4 → ℤ) (D : ℝ) (hD : 0 ≤ D) (p q : ℕ) (hq : 1 ≤ q) (k : Fin q → ℕ)
    (hfar : ∀ c e, c ≠ e → 83 * stageRange S.tower u * keptSitesAlong D (stageRange S.tower u) ≤
      TorusFields.supDist (S.siteAt u z + k c • stageTranslation S u p) (S.siteAt u z + k e • stageTranslation S u p)) :
    ∫ ω, ∏ c, largeHullIndicator u z D S (S.sampleOf rule ((sampleTranslate S p)^[k c] ω)) ∂S.sampleLaw ≤
      Real.exp (-(hullDecayRate Λ.table * stageCoupling S.tower u * (1 + D / (stageRange S.tower u : ℝ)))) ^ q := by
  classical
  obtain ⟨hm, hmap⟩ := sampleAtLevel_law hF hLaw hDraw S hrule hu
  set E : Set (MarkedSample Λ.stepParams u (S.sideAtLevel u)) :=
    {w | ∀ e, IsLongAt S.tower u (S.sideAtLevel u) D (S.siteAt u z + k e • stageTranslation S u p) w} with hE
  have hEm : MeasurableSet E := by
    have e : E = ⋂ e, {w | IsLongAt S.tower u (S.sideAtLevel u) D (S.siteAt u z + k e • stageTranslation S u p) w} := by
      ext w
      simp [hE]
    rw [e]
    exact MeasurableSet.iInter fun e => measurableSet_hullSet_pred hF.fit hSt S.tower u (S.sideAtLevel u) fun Y =>
      S.siteAt u z + k e • stageTranslation S u p ∈ Y ∧
        D ≤ (supDiam (hullClass (stageRange S.tower u) Y (S.siteAt u z + k e • stageTranslation S u p)) : ℝ)
  have hval : ∀ ω, ∏ c, largeHullIndicator u z D S (S.sampleOf rule ((sampleTranslate S p)^[k c] ω)) =
      E.indicator (1 : MarkedSample Λ.stepParams u (S.sideAtLevel u) → ℝ) (S.sampleAtLevel u hu (S.sampleOf rule ω)) := by
    intro ω
    have h1 : ∀ c, largeHullIndicator u z D S (S.sampleOf rule ((sampleTranslate S p)^[k c] ω)) =
        if IsLongAt S.tower u (S.sideAtLevel u) D (S.siteAt u z + k c • stageTranslation S u p)
          (S.sampleAtLevel u hu (S.sampleOf rule ω)) then 1 else 0 := by
      intro c
      rw [largeHullIndicator_eq_pair S rule hu, sampleAtLevel_eq]
      have hit := iterate_translate S hu p
        (fun y q => IsLongAt S.tower u (S.sideAtLevel u) D y (rule.chain S.tower u (S.sideAtLevel u) q.1 q.2))
        (fun y q => isLongAt_translate hF S hrule hu p D y q) (k c) (S.siteAt u z) ω
      simp only [hit]
    by_cases hall : ∀ c, IsLongAt S.tower u (S.sideAtLevel u) D (S.siteAt u z + k c • stageTranslation S u p)
        (S.sampleAtLevel u hu (S.sampleOf rule ω))
    · rw [Set.indicator_of_mem (show S.sampleAtLevel u hu (S.sampleOf rule ω) ∈ E from hall)]
      exact Finset.prod_eq_one fun c _ => by rw [h1 c, if_pos (hall c)]
    · rw [Set.indicator_of_notMem (show S.sampleAtLevel u hu (S.sampleOf rule ω) ∉ E from hall)]
      obtain ⟨c, hc⟩ := not_forall.1 hall
      exact Finset.prod_eq_zero (Finset.mem_univ c) (by rw [h1 c, if_neg hc])
  have hint : ∫ ω, ∏ c, largeHullIndicator u z D S (S.sampleOf rule ((sampleTranslate S p)^[k c] ω)) ∂S.sampleLaw =
      (markedSampleLaw S.tower S.β u (S.sideAtLevel u)).real E := by
    rw [integral_congr_ae (Eventually.of_forall hval), ← integral_indicator_one hEm, ← hmap]
    exact (integral_map hm (by
      rw [hmap]
      exact (measurable_const.indicator hEm).aestronglyMeasurable)).symm
  rw [hint]
  exact hF.classes Λ.g S.β S.data.windowLevel S.data.sideExponent S.tower u (S.sideAtLevel u)
    (hullChainAtLevel_of_point S hF.g_pos hF.floor hu) q
    (fun c => S.siteAt u z + k c • stageTranslation S u p) D hq hD hfar
end Facts
section Star
variable {Λ : MomentParameters} {CE : ParameterAssignment → ℝ}
private theorem points_data {S : MomentPoint Λ} (F : LimitLawAtPoint S) (i : ℕ) :
    (F.points i).data.windowLevel = S.data.windowLevel ∧ (F.points i).β = S.β ∧ (F.points i).tower = S.tower ∧
      (F.points i).data.sideExponent = F.exponents i := by
  obtain ⟨hp, hs, e⟩ := F.points_eq i
  rw [e]
  exact ⟨rfl, rfl, rfl, rfl⟩
private theorem stageCoupling_points {S : MomentPoint Λ} (F : LimitLawAtPoint S) (i : ℕ) {u : ℕ}
    (hu : u ≤ S.data.windowLevel) : stageCoupling (F.points i).tower u = S.coupling u := by
  obtain ⟨hK, hβ, -, -⟩ := points_data F i
  have h := stage_coupling_eq (F.points i) (j := u) (by omega)
  show ((F.points i).tower.stage u).coupling = (couplingFlow Λ.stepParams S.β u).1
  rw [h, hβ]
private theorem stageRange_points {S : MomentPoint Λ} (F : LimitLawAtPoint S) (i : ℕ) {u : ℕ}
    (hu : u ≤ S.data.windowLevel) : stageRange (F.points i).tower u = clusterRange (S.coupling u) := by
  show clusterRange (stageCoupling (F.points i).tower u) = _
  rw [stageCoupling_points F i hu]
private theorem eventually_le_half_side (hF : LimitHullInputs Λ CE) {S : MomentPoint Λ} (F : LimitLawAtPoint S)
    (u B : ℕ) : ∀ᶠ i in atTop, B ≤ (F.points i).sideAtLevel u / 2 := by
  filter_upwards [eventually_ge_atTop B] with i hi
  obtain ⟨-, -, -, hm⟩ := points_data F i
  have hL : 1 < Λ.stepParams.side := by
    have := hF.fit.L_ge
    omega
  have h1 : (F.points i).sideAtLevel u =
      2 * (Λ.stepParams.side ^ (F.points i).data.sideExponent *
        Λ.stepParams.side ^ ((F.points i).data.windowLevel - u)) := by
    show fineSide Λ.stepParams.side ((F.points i).data.windowLevel - u)
      (2 * Λ.stepParams.side ^ (F.points i).data.sideExponent) = _
    rw [fineSide_eq]
    ring
  have h2 : i ≤ F.exponents i := F.strictMono_exponents.le_apply
  have h3 : (F.points i).data.sideExponent < Λ.stepParams.side ^ (F.points i).data.sideExponent := Nat.lt_pow_self hL
  have h4 : 1 ≤ Λ.stepParams.side ^ ((F.points i).data.windowLevel - u) := Nat.one_le_pow _ _ (by omega)
  rw [h1, Nat.mul_div_cancel_left _ (by norm_num)]
  have h5 : Λ.stepParams.side ^ (F.points i).data.sideExponent ≤
      Λ.stepParams.side ^ (F.points i).data.sideExponent * Λ.stepParams.side ^ ((F.points i).data.windowLevel - u) :=
    Nat.le_mul_of_pos_right _ h4
  omega
private theorem copies_supDist_ge {n : ℕ} [NeZero n] (x : TorusSite n) (A k₁ k₂ : ℕ) (h12 : k₂ ≤ k₁)
    (hbig : k₁ * A ≤ n / 2) :
    (k₁ - k₂) * A ≤ TorusFields.supDist (x + k₁ • (siteOfInt (Pi.single 0 (A : ℤ)) : TorusSite n))
      (x + k₂ • (siteOfInt (Pi.single 0 (A : ℤ)) : TorusSite n)) := by
  obtain ⟨t, rfl⟩ : ∃ t, k₁ = k₂ + t := ⟨k₁ - k₂, by omega⟩
  have e : x + (k₂ + t) • (siteOfInt (Pi.single 0 (A : ℤ)) : TorusSite n) =
      (x + k₂ • (siteOfInt (Pi.single 0 (A : ℤ)) : TorusSite n)) + siteOfInt (Pi.single 0 (((t * A : ℕ)) : ℤ)) := by
    rw [add_nsmul, add_assoc, nsmul_siteOfInt t]
    congr 3
    funext i
    by_cases h : i = 0
    · subst h
      simp
    · simp [h]
  rw [e, Nat.add_sub_cancel_left]
  refine le_supDist_axis _ _ ?_
  have : t * A ≤ (k₂ + t) * A := Nat.mul_le_mul_right _ (by omega)
  omega
private theorem condMean_largeHull_le (hF : LimitHullInputs Λ CE) (hLaw : sampleBelowLawStatement)
    (hDraw : forgetLastStepStatement) (hSt : StageStatesMeasurableStatement) (hMe : jointLimitPropertiesStatement)
    {S : MomentPoint Λ} (F : LimitLawAtPoint S) (hKeep : (translatedTori F.points F.period).IsPreserving) (j : F.Index)
    {u : ℕ} (hu : u ≤ S.data.windowLevel) (z : Fin 4 → ℤ) (D : ℝ) (hD : 0 ≤ D)
    (hg : F.observables j = largeHullIndicator u z D) :
    ∀ᵐ v ∂F.law, F.condMeanAt j v ≤
      Real.exp (-(hullDecayRate Λ.table * S.coupling u * (1 + D / (clusterRange (S.coupling u) : ℝ)))) := by
  haveI := F.countable_index
  obtain ⟨-, h2, h3, -, -, h6⟩ := hMe (translatedTori F.points F.period) F.Index
    (fun j => sampleFamily F.rule F.points F.period (F.observables j)) F.law hKeep F.hasBoundedMoments F.isJointLimitLaw
  have hval : ∀ i ω, sampleFamily F.rule F.points F.period (F.observables j) i ω = 0 ∨
      sampleFamily F.rule F.points F.period (F.observables j) i ω = 1 := by
    intro i ω
    show F.observables j (F.points i) _ = 0 ∨ F.observables j (F.points i) _ = 1
    rw [hg]
    unfold largeHullIndicator
    split_ifs <;> simp
  have hbd : ∀ᵐ v ∂F.law, 0 ≤ v (j, 0) ∧ v (j, 0) ≤ 1 := by
    have h := h3 1 (fun _ => (j, 0)) (fun x => x 0 * (1 - x 0)) (by fun_prop) (Eventually.of_forall fun i ω => by
      rcases hval i ω with e | e
      · show sampleFamily F.rule F.points F.period (F.observables j) i ω *
          (1 - sampleFamily F.rule F.points F.period (F.observables j) i ω) = 0
        rw [e]
        ring
      · show sampleFamily F.rule F.points F.period (F.observables j) i ω *
          (1 - sampleFamily F.rule F.points F.period (F.observables j) i ω) = 0
        rw [e]
        ring)
    filter_upwards [h] with v hv
    rcases mul_eq_zero.1 hv with e | e
    · rw [show v (j, 0) = 0 from e]
      norm_num
    · have e' : v (j, 0) = 1 := by linarith
      rw [e']
      norm_num
  refine h6 j _ 1 1 (Real.exp_pos _).le hbd fun q hq => ?_
  obtain ⟨Rb, hRb⟩ : ∃ Rb, Rb = 83 * clusterRange (S.coupling u) * keptSitesAlong D (clusterRange (S.coupling u)) :=
    ⟨_, rfl⟩
  refine ⟨Rb + 1, fun k hk => ?_⟩
  obtain ⟨-, hlim⟩ := h2 q (fun c => (j, k c))
  refine le_of_tendsto hlim ?_
  filter_upwards [eventually_le_half_side hF F u ((∑ c, k c) * translationStep Λ.stepParams.side F.period
    (S.data.windowLevel - u))] with i hi
  obtain ⟨hK, hβ, hT, -⟩ := points_data F i
  have hu' : u ≤ (F.points i).data.windowLevel := by rw [hK]; exact hu
  have hrule' : F.rule.IsAdmissible (F.points i).tower := by rw [hT]; exact F.rule_admissible
  have hL0 : 0 < Λ.stepParams.side := hF.fit.L_odd.pos
  have hA1 : 1 ≤ translationStep Λ.stepParams.side F.period ((F.points i).data.windowLevel - u) := by
    unfold translationStep
    exact Nat.mul_pos hL0 (Nat.mul_pos (pow_pos hL0 _) F.one_le_period)
  have hsum : ∀ c, k c * translationStep Λ.stepParams.side F.period ((F.points i).data.windowLevel - u) ≤
      (F.points i).sideAtLevel u / 2 := by
    intro c
    rw [hK]
    refine le_trans (Nat.mul_le_mul_right _ ?_) hi
    exact Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
  have ham : stageTranslation (F.points i) u F.period =
      siteOfInt (Pi.single 0 ((translationStep Λ.stepParams.side F.period ((F.points i).data.windowLevel - u) : ℕ) : ℤ)) :=
    siteOfInt_axisDisplacement _ _ _ _
  have hres := longClasses_integral_le hF hLaw hDraw hSt (F.points i) hrule' hu' z D hD F.period q hq k (by
    intro c e hce
    rw [stageRange_points F i hu, ← hRb, ham]
    rcases hk c e hce with h | h
    · have h1 := copies_supDist_ge ((F.points i).siteAt u z) _ (k c) (k e) (by omega) (hsum c)
      refine le_trans ?_ h1
      calc Rb ≤ (k c - k e) * 1 := by omega
        _ ≤ _ := Nat.mul_le_mul_left _ hA1
    · have h1 := copies_supDist_ge ((F.points i).siteAt u z) _ (k e) (k c) (by omega) (hsum e)
      rw [supDist_comm]
      refine le_trans ?_ h1
      calc Rb ≤ (k e - k c) * 1 := by omega
        _ ≤ _ := Nat.mul_le_mul_left _ hA1)
  rw [stageCoupling_points F i hu, stageRange_points F i hu] at hres
  rw [one_mul]
  show ∫ ω, ∏ c, F.observables j (F.points i) ((F.points i).sampleOf F.rule
    ((sampleTranslate (F.points i) F.period)^[k c] ω)) ∂(F.points i).sampleLaw ≤ _
  rw [hg]
  exact hres
end Star
section Moments
variable {Λ : MomentParameters} {CE : ParameterAssignment → ℝ}
private def truncatedScoreMoment (u : ℕ) (z : Fin 4 → ℤ) (D : ℝ) (k : ℕ) (M : ℝ) : SampleObservable Λ := fun S w =>
  if h : u ≤ S.data.windowLevel then
    min (localScoreMoment S.tower Λ.response.s₁ u (S.sideAtLevel u) (S.siteAt u z) D k (S.sampleAtLevel u h w)) M
  else 0
private theorem truncatedScoreMoment_eq_pair (S : MomentPoint Λ) (rule : NoiseRule Λ.stepParams) {u : ℕ}
    (hu : u ≤ S.data.windowLevel) (z : Fin 4 → ℤ) (D : ℝ) (k : ℕ) (M : ℝ) (ω : S.SampleSpace) :
    truncatedScoreMoment u z D k M S (S.sampleOf rule ω) =
      min (localScore rule S.tower Λ.response.s₁ u (S.sideAtLevel u) (S.siteAt u z) D k (stagePair S u hu ω)) M := by
  unfold truncatedScoreMoment
  rw [dif_pos hu, sampleAtLevel_eq]
  rfl
private theorem sitesInBlocks_mono {L n : ℕ} [NeZero L] [NeZero n] {Q Q' : Finset (TorusSite n)} (h : Q ⊆ Q') :
    sitesInBlocks L Q ⊆ sitesInBlocks L Q' := by
  intro x hx
  simp only [sitesInBlocks, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact h hx
private theorem sitesUnder_mono {L : ℕ} [NeZero L] (u : ℕ) :
    ∀ (n : ℕ) [NeZero n] {Q Q' : Finset (TorusSite n)}, Q ⊆ Q' → sitesUnder L u n Q ⊆ sitesUnder L u n Q' := by apply _root_.YangMills.SharedProofs.p53753 <;> assumption
private theorem noiseAgreeAbove_mono (ℓ : StepParameters) (u : ℕ) :
    ∀ (n : ℕ) [NeZero n] {Q Q' : Finset (TorusSite n)} {U U' : ChainNoise.ChainNoise ℓ u n}, Q ⊆ Q' →
      NoiseAgreeAbove ℓ u n Q' U U' → NoiseAgreeAbove ℓ u n Q U U' := by
  induction u with
  | zero => exact fun _ _ _ _ _ _ _ h => h
  | succ u ih =>
    intro n _ Q Q' U U' h hU
    obtain ⟨h1, h2, h3, h4⟩ := hU
    refine ⟨ih (n * ℓ.side) (sitesInBlocks_mono h) h1, fun y hy => h2 y (h hy), fun c hc => h3 c (h hc), ?_⟩
    exact fun b hb => h4 b (h hb)
abbrev _root_.YangMills.SharedProofs.p6852 := @noiseAgreeAbove_mono
private theorem chainNoiseLaw_isProbability (ℓ : StepParameters) (s : ℕ) :
    ∀ (n : ℕ) [NeZero n], IsProbabilityMeasure (chainNoiseLaw ℓ s n) := by
  induction s with
  | zero =>
    intro n _
    show IsProbabilityMeasure (Measure.dirac ())
    infer_instance
  | succ s ih =>
    intro n _
    letI := instMeasurableSpaceChainNoise ℓ s (n * ℓ.side)
    haveI := ih (n * ℓ.side)
    haveI : IsProbabilityMeasure (stepNoiseLaw ℓ n) := by
      unfold stepNoiseLaw
      infer_instance
    show IsProbabilityMeasure ((chainNoiseLaw ℓ s (n * ℓ.side)).prod (stepNoiseLaw ℓ n))
    infer_instance
abbrev _root_.YangMills.SharedProofs.p2413 := @chainNoiseLaw_isProbability
private theorem localSizes_nonneg {ℓ : StepParameters} (T : StageTower ℓ) {s₁ : ℝ} (hs : 0 ≤ s₁) (j : ℕ) :
    ∀ (n : ℕ) [NeZero n] (w : MarkedSample ℓ j n) (Q : Finset (TorusSite n)) (y : TorusSite n),
      0 ≤ (localHullData T s₁ j n w Q).2 y := by
  induction j with
  | zero =>
    intro n _ w Q y
    exact le_rfl
  | succ j ih =>
    intro n _ w Q y
    simp only [localHullData]
    split_ifs
    · exact add_nonneg hs (Finset.sum_nonneg fun z _ => ih _ _ _ _)
    · exact hs
    · exact le_rfl
private theorem localMoment_nonneg {ℓ : StepParameters} (T : StageTower ℓ) {s₁ : ℝ} (hs : 0 ≤ s₁) (u n : ℕ) [NeZero n]
    (y : TorusSite n) (D : ℝ) (k : ℕ) (w : MarkedSample ℓ u n) : 0 ≤ localScoreMoment T s₁ u n y D k w := by
  unfold localScoreMoment
  split_ifs
  · exact pow_nonneg (localSizes_nonneg T hs u n w _ y) k
  · exact le_rfl
private theorem measurable_localMoment {ℓ : StepParameters} (hfit : ℓ.Admissible)
    (hSt : StageStatesMeasurableStatement) (hWh : chainMeasurabilityStatement) (T : StageTower ℓ) (s₁ : ℝ)
    (u n : ℕ) [NeZero n] (y : TorusSite n) (D : ℝ) (k : ℕ) :
    Measurable (localScoreMoment T s₁ u n y D k) := by
  classical
  have hq : ∀ (n : ℕ) [NeZero n], Measurable (stageState T 0 n) := fun n _ => hSt ℓ hfit T 0 n
  have h1 := HullMeans.measurableSet_localHullData_fst_eq T s₁ hWh.1 hq u n (localHullBox T u y D)
  have h2 := HullMeans.measurable_localHullData_snd T s₁ hWh.1 hq u n (localHullBox T u y D) y
  have h3 : MeasurableSet {w : MarkedSample ℓ u n | y ∈ (localHullData T s₁ u n w (localHullBox T u y D)).1} := by
    have e : {w : MarkedSample ℓ u n | y ∈ (localHullData T s₁ u n w (localHullBox T u y D)).1} =
        ⋃ A ∈ {A : Finset (TorusSite n) | y ∈ A}, {w | (localHullData T s₁ u n w (localHullBox T u y D)).1 = A} := by
      ext w
      simp
    rw [e]
    exact MeasurableSet.biUnion (Set.to_countable _) fun A _ => h1 A
  show Measurable fun w => localScoreMoment T s₁ u n y D k w
  simp only [localScoreMoment]
  exact Measurable.ite h3 (h2.pow_const k) measurable_const
private theorem box_subset_translated_cell {n : ℕ} [NeZero n] (y : TorusSite n) (R l t : ℕ) (hR : 2 * R < l)
    (ht : (t + 1) * l ≤ n) :
    box (y + (siteOfInt (Pi.single 0 ((l * t : ℕ) : ℤ)) : TorusSite n)) R ⊆
      (⟨l, fun i => ((y i).val : ℤ) - (R : ℤ) - 1⟩ : MirrorGrid).cellSites n (Pi.single 0 t) := by
  classical
  intro x hx
  obtain ⟨v, hv⟩ : ∃ v : TorusSite n, v = siteOfInt (Pi.single 0 ((l * t : ℕ) : ℤ)) := ⟨_, rfl⟩
  rw [← hv] at hx
  have hx' : TorusFields.supDist x (y + v) ≤ R := by
    simp only [box, thickening, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      exists_eq_left] at hx
    exact hx
  simp only [MirrorGrid.cellSites, Finset.mem_filter, Finset.mem_univ, true_and]
  funext i
  simp only [MirrorGrid.cellIndex]
  have hd : ((x i - (y + v) i).valMinAbs).natAbs ≤ R :=
    (Finset.le_sup (f := fun i => ((x i - (y + v) i).valMinAbs).natAbs) (Finset.mem_univ i)).trans hx'
  obtain ⟨d, hdd⟩ : ∃ d : ℤ, d = (x i - (y + v) i).valMinAbs := ⟨_, rfl⟩
  rw [← hdd] at hd
  obtain ⟨e, he⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ d + R by omega)
  have hel : e < l := by omega
  obtain ⟨s, hs⟩ : ∃ s : ℕ, s = (Pi.single (0 : Fin 4) t : Fin 4 → ℕ) i := ⟨_, rfl⟩
  have hst : s ≤ t := by
    rw [hs]
    by_cases h : i = 0
    · subst h
      simp
    · simp [h]
  have hvi : v i = ((l * s : ℕ) : ZMod n) := by
    rw [hv, hs]
    by_cases h : i = 0
    · subst h
      simp [siteOfInt]
    · simp [siteOfInt, h]
  have h1 : ((d : ℤ) : ZMod n) = x i - (y i + v i) := by
    rw [hdd, ZMod.coe_valMinAbs]
    rfl
  have h2 : ((e : ℕ) : ZMod n) = (d : ZMod n) + (R : ZMod n) := by
    have hcast := congrArg (Int.cast : ℤ → ZMod n) he
    push_cast at hcast
    exact hcast.symm
  have key : x i - (((((y i).val : ℤ) - (R : ℤ) - 1 + 1 : ℤ)) : ZMod n) = ((e + l * s : ℕ) : ZMod n) := by
    have h3 : (((y i).val : ZMod n)) = y i := ZMod.natCast_zmod_val _
    push_cast at hvi ⊢
    rw [h3, h2, h1, hvi]
    ring
  have hlt : e + l * s < n := by
    have h4 : l * s ≤ l * t := Nat.mul_le_mul_left _ hst
    have h5 : (t + 1) * l = l * t + l := by ring
    omega
  show (x i - ((((y i).val : ℤ) - (R : ℤ) - 1 + 1 : ℤ) : ZMod n)).val / l = _
  rw [key, ZMod.val_natCast_of_lt hlt, hs.symm]
  have hl : 0 < l := by omega
  rw [Nat.add_mul_div_left _ _ hl, Nat.div_eq_of_lt hel, zero_add]
end Moments
section MomentsOnATorus
variable {Λ : MomentParameters} {CE : ParameterAssignment → ℝ}
private theorem truncatedMoments_integral_le (hF : LimitHullInputs Λ CE) (hLaw : sampleBelowLawStatement)
    (hDraw : forgetLastStepStatement) (hSt : StageStatesMeasurableStatement) (hWh : chainMeasurabilityStatement)
    (hBo : HullsInEveryVolume.noiseChainMeasurableStatement) (hMC : separateCellsExpectationStatement)
    (S : MomentPoint Λ) {rule : NoiseRule Λ.stepParams} (hrule : rule.IsAdmissible S.tower) {u : ℕ}
    (hu : u ≤ S.data.windowLevel) (z : Fin 4 → ℤ) (D : ℝ) (hD : 0 < D) (k : ℕ) (hk : 1 ≤ k) (M₀ : ℝ) (hM₀ : 0 < M₀)
    (p : ℕ) (hp : 1 ≤ p) (q : ℕ) (ks : Fin q → ℕ) (hks : Function.Injective ks) (l : ℕ)
    (hl : l = leastPowerAbove Λ.stepParams.side ⌈16 * D + 40 * (stageRange S.tower u : ℝ)⌉₊)
    (hbig : 2 * l ≤ S.sideAtLevel u)
    (ht : ∀ c, (ks c * translationStep Λ.stepParams.side p (S.data.windowLevel - u) + 1) * l ≤ S.sideAtLevel u) :
    ∫ ω, ∏ c, truncatedScoreMoment u z D k M₀ S (S.sampleOf rule ((sampleTranslate S p)^[l * ks c] ω)) ∂S.sampleLaw ≤
      (16 ^ k * (k.factorial : ℝ) *
        Real.exp (CE Λ.table * Real.log (stageCoupling S.tower u) * (l : ℝ) ^ 4)) ^ q := by
  classical
  have hfit := hF.fit
  have hAt := hullChainAtLevel_of_point S hF.g_pos hF.floor hu
  have hrun := hAt.chain
  have hgt : 11 * 2 ^ 12 * Λ.stepParams.baseDepth < Λ.stepParams.side := hF.drawn.L_gt
  have hLg : 2 ^ 16 ≤ Λ.stepParams.side := hfit.L_ge
  have hL1 : 1 < Λ.stepParams.side := by omega
  have hL0 : 0 < Λ.stepParams.side := by omega
  have hβ : 0 < S.β := by
    have h1 : (1 : ℝ) ≤ Λ.floor := hF.one_le
    have h2 := hF.floor
    have h3 : windowUpper Λ.stepParams Λ.g ≤ S.β := S.window_le
    have h4 : windowUpper Λ.stepParams Λ.g = (Λ.g ^ 2)⁻¹ + 2 * Λ.stepParams.B := rfl
    have h5 := hfit.B_pos
    linarith
  have hm : 2 ≤ S.data.sideExponent := by
    by_contra hlt
    have hvol : Λ.table.side * Λ.table.n₀ ≤ 2 * Λ.table.side ^ S.data.sideExponent := hrun.volume_le
    have hn0 : 4096 ≤ Λ.table.n₀ := hF.drawn.n₀_ge
    have hLg' : 2 ^ 16 ≤ Λ.table.side := hLg
    have hm' : S.data.sideExponent = 0 ∨ S.data.sideExponent = 1 := by omega
    rcases hm' with h | h
    · rw [h] at hvol
      simp only [pow_zero, mul_one] at hvol
      nlinarith
    · rw [h] at hvol
      simp only [pow_one] at hvol
      nlinarith
  have hnM : S.sideAtLevel u = 2 * Λ.stepParams.side ^ (S.data.sideExponent + (S.data.windowLevel - u)) := by
    show fineSide Λ.stepParams.side (S.data.windowLevel - u) (2 * Λ.stepParams.side ^ S.data.sideExponent) = _
    rw [fineSide_eq, pow_add]
    ring
  have hdvd : Λ.stepParams.side ∣ S.sideAtLevel u := by
    rw [hnM]
    exact Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) 2
  have h64 : 64 ≤ S.sideAtLevel u := by
    have h1 : Λ.stepParams.side ≤ Λ.stepParams.side ^ (S.data.sideExponent + (S.data.windowLevel - u)) :=
      Nat.le_self_pow (by omega) _
    omega
  have hx : 1 ≤ stageCoupling S.tower u :=
    hF.one_le.trans (hF.coupling_ge Λ.g S.β S.data.windowLevel S.data.sideExponent S.tower u _ hAt)
  have hx0 : 0 < (S.tower.stage u).coupling := lt_of_lt_of_le one_pos hx
  have hr : 1 ≤ stageRange S.tower u := Nat.ceil_pos.2 (Real.rpow_pos_of_pos hx0 _)
  have hrR : (1 : ℝ) ≤ (stageRange S.tower u : ℝ) := by exact_mod_cast hr
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 16 * D + 40 * (stageRange S.tower u : ℝ) := ⟨_, rfl⟩
  rw [← ha] at hl
  have hc2 : 1 < ⌈a⌉₊ := Nat.lt_ceil.2 (by rw [ha]; norm_num; linarith)
  obtain ⟨pp, hppd⟩ : ∃ pp, pp = Nat.clog Λ.stepParams.side ⌈a⌉₊ := ⟨_, rfl⟩
  have hpp1 : 1 ≤ pp := by
    rw [hppd]
    exact Nat.clog_pos hL1 hc2
  have hside : l = Λ.stepParams.side ^ pp := by
    rw [hl, hppd]
    rfl
  have hlow : a ≤ (l : ℝ) := (Nat.le_ceil a).trans (by
    rw [hside, hppd]
    exact_mod_cast Nat.le_pow_clog hL1 _)
  obtain ⟨R, hRd⟩ : ∃ R, R = ⌊2 * D⌋₊ + 6 * stageRange S.tower u := ⟨_, rfl⟩
  have hR : 2 * R < l := by
    have h1 : ((⌊2 * D⌋₊ : ℕ) : ℝ) ≤ 2 * D := Nat.floor_le (by linarith)
    have h2' : ((2 * R : ℕ) : ℝ) < (l : ℝ) := by
      refine lt_of_lt_of_le ?_ hlow
      rw [hRd, ha]
      push_cast
      linarith
    exact_mod_cast h2'
  have hl0 : 0 < l := by omega
  have hpM : pp ≤ S.data.sideExponent + (S.data.windowLevel - u) := by
    have h1 : 2 * Λ.stepParams.side ^ pp ≤ 2 * Λ.stepParams.side ^ (S.data.sideExponent + (S.data.windowLevel - u)) := by
      rw [← hside, ← hnM]
      exact hbig
    exact (Nat.pow_le_pow_iff_right hL1).1 (by omega)
  obtain ⟨g, hg⟩ : ∃ g : MirrorGrid, g = ⟨l, fun i => ((S.siteAt u z i).val : ℤ) - (R : ℤ) - 1⟩ := ⟨_, rfl⟩
  have hgs : g.side = l := by rw [hg]
  have hgrid : IsGridOfTorus g Λ.stepParams.side (S.data.sideExponent + (S.data.windowLevel - u)) :=
    ⟨pp, hpp1, hpM, hgs.trans hside⟩
  obtain ⟨A, hAd⟩ : ∃ A, A = translationStep Λ.stepParams.side p (S.data.windowLevel - u) := ⟨_, rfl⟩
  rw [← hAd] at ht
  have hA1 : 1 ≤ A := by
    rw [hAd]
    unfold translationStep
    exact Nat.mul_pos hL0 (Nat.mul_pos (pow_pos hL0 _) hp)
  have ham : stageTranslation S u p = siteOfInt (Pi.single 0 (A : ℤ)) := by
    rw [hAd]
    exact siteOfInt_axisDisplacement _ _ _ _
  obtain ⟨y, hyd⟩ : ∃ y : Fin q → TorusSite (S.sideAtLevel u),
      y = fun c => S.siteAt u z + (l * ks c) • stageTranslation S u p := ⟨_, rfl⟩
  have hy : ∀ c, y c = S.siteAt u z + siteOfInt (Pi.single 0 ((l * (ks c * A) : ℕ) : ℤ)) := by
    intro c
    rw [hyd]
    show S.siteAt u z + (l * ks c) • stageTranslation S u p = _
    rw [ham, nsmul_siteOfInt]
    congr 2
    funext i
    by_cases h : i = 0
    · subst h
      simp
      ring
    · simp [h]
  obtain ⟨cell, hcelld⟩ : ∃ cell : Fin q → Fin 4 → ℕ, cell = fun c => Pi.single 0 (ks c * A) := ⟨_, rfl⟩
  have hbox : ∀ c, box (y c) R ⊆ g.cellSites (S.sideAtLevel u) (cell c) := by
    intro c
    rw [hy c, hg, hcelld]
    exact box_subset_translated_cell _ R l _ hR (ht c)
  have hind : ∀ c, cell c ∈ g.cellIndices (S.sideAtLevel u) := by
    intro c
    have h1 : ks c * A + 1 ≤ S.sideAtLevel u / l := (Nat.le_div_iff_mul_le hl0).2 (ht c)
    refine Fintype.mem_piFinset.2 fun i => Finset.mem_range.2 ?_
    rw [hgs, hcelld]
    by_cases h : i = 0
    · subst h
      simpa using h1
    · simp only [Pi.single_eq_of_ne h]
      omega
  have hinj : Function.Injective cell := by
    intro c e hce
    have h1 : ks c * A = ks e * A := by
      have hc0 := congrFun hce 0
      rw [hcelld] at hc0
      simpa using hc0
    exact hks (Nat.eq_of_mul_eq_mul_right hA1 h1)
  have hchain : Measurable fun p : TorusField (fineSide Λ.stepParams.side u (S.sideAtLevel u)) ×
      ChainNoise.ChainNoise Λ.stepParams u (S.sideAtLevel u) => rule.chain S.tower u (S.sideAtLevel u) p.1 p.2 :=
    hBo Λ.stepParams hfit S.tower rule S.marksMeasurable hrule u _ hdvd h64
  have hlm : ∀ x, Measurable (localScoreMoment S.tower Λ.response.s₁ u (S.sideAtLevel u) x D k) := fun x =>
    measurable_localMoment hfit hSt hWh S.tower _ u _ x D k
  have hnn : ∀ x w, 0 ≤ localScoreMoment S.tower Λ.response.s₁ u (S.sideAtLevel u) x D k w := fun x w =>
    localMoment_nonneg S.tower hF.s_nonneg u _ x D k w
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Fin q → TorusField (fineSide Λ.stepParams.side u (S.sideAtLevel u)) ×
      ChainNoise.ChainNoise Λ.stepParams u (S.sideAtLevel u) → ℝ,
      Φ = fun c r => min (localScore rule S.tower Λ.response.s₁ u (S.sideAtLevel u) (y c) D k r) M₀ := ⟨_, rfl⟩
  have hΦm : ∀ c, Measurable (Φ c) := fun c => by
    rw [hΦ]
    exact ((hlm (y c)).comp hchain).min measurable_const
  have hΦ0 : ∀ c r, 0 ≤ Φ c r := fun c r => by
    rw [hΦ]
    exact le_min (hnn _ _) hM₀.le
  have hΦ1 : ∀ c r, Φ c r ≤ M₀ := fun c r => by
    rw [hΦ]
    exact min_le_right _ _
  have hin : ∀ c, IsCellObservable Λ.stepParams g u (S.sideAtLevel u) (cell c) (Φ c) := fun c =>
    { measurable := hΦm c
      bounded := ⟨M₀, fun r => by
        rw [abs_of_nonneg (hΦ0 c r)]
        exact hΦ1 c r⟩
      nonneg := hΦ0 c
      depends := fun W W' U U' hW hU => by
        have hre := (hF.reach Λ.g S.β S.data.windowLevel S.data.sideExponent S.tower u _ hAt rule hrule (y c) D k hD hk).1
        have h1 := hre W W' U U'
          (fun b h1 h2 => hW b (sitesUnder_mono u _ (hRd ▸ hbox c) h1) (sitesUnder_mono u _ (hRd ▸ hbox c) h2))
          (noiseAgreeAbove_mono Λ.stepParams u _ (hRd ▸ hbox c) hU)
        rw [hΦ]
        show min _ _ = min _ _
        rw [h1] }
  have hdeep : 2 ≤ S.data.sideExponent + (S.data.windowLevel - u) + u := by omega
  have hmean := hMC Λ.stepParams S.β u (S.sideAtLevel u) (S.data.sideExponent + (S.data.windowLevel - u)) g
    hfit.L_odd hLg hβ hnM hdeep hgrid Finset.univ cell Φ (fun c _ => hind c) hinj.injOn (fun c _ => hin c)
  obtain ⟨Gv, hGvd⟩ : ∃ Gv : ℝ, Gv = 16 ^ k * (k.factorial : ℝ) *
      Real.exp (CE Λ.table * Real.log (stageCoupling S.tower u) * (l : ℝ) ^ 4) := ⟨_, rfl⟩
  have hGv : ∀ c, (g.atDepth Λ.stepParams.side u).chessboardNormAt S.β (fineSide Λ.stepParams.side u (S.sideAtLevel u))
      (cell c) (noiseExpectation Λ.stepParams u (S.sideAtLevel u) (Φ c)) ≤ Gv := by
    intro c
    have h1 := (hF.moment Λ.g S.β S.data.windowLevel S.data.sideExponent S.tower u _ hAt rule hrule (y c) D k hD hk).1 g
      (by rw [hgs, hl, ha]) (by rw [hgs]; exact hbig) (cell c) (hind c) (hRd ▸ hbox c) M₀ hM₀
    rw [hgs] at h1
    rw [hGvd, hΦ]
    exact h1
  have hnorm0 : ∀ c, 0 ≤ (g.atDepth Λ.stepParams.side u).chessboardNormAt S.β
      (fineSide Λ.stepParams.side u (S.sideAtLevel u)) (cell c)
      (noiseExpectation Λ.stepParams u (S.sideAtLevel u) (Φ c)) := by
    intro c
    have hF0 : ∀ W, 0 ≤ noiseExpectation Λ.stepParams u (S.sideAtLevel u) (Φ c) W := fun W =>
      integral_nonneg fun U => hΦ0 c _
    exact Real.rpow_nonneg (integral_nonneg fun W => Finset.prod_nonneg fun c' _ => hF0 _) _
  have hprod : ∏ c, (g.atDepth Λ.stepParams.side u).chessboardNormAt S.β
      (fineSide Λ.stepParams.side u (S.sideAtLevel u)) (cell c)
      (noiseExpectation Λ.stepParams u (S.sideAtLevel u) (Φ c)) ≤ Gv ^ q := by
    calc _ ≤ ∏ _c : Fin q, Gv := Finset.prod_le_prod (fun c _ => hnorm0 c) (fun c _ => hGv c)
      _ = Gv ^ q := by simp
  obtain ⟨hm', hmap⟩ := sampleAtLevel_law hF hLaw hDraw S hrule hu
  have hcar := (hF.carries Λ.g S.β S.data.windowLevel S.data.sideExponent S.tower hrun).2 rule hrule u _ hAt
  haveI : IsProbabilityMeasure (wilsonLaw S.β (fineSide Λ.stepParams.side u (S.sideAtLevel u))) :=
    (hDraw _ hfit hgt S.tower S.isCutoff S.marksMeasurable S.β 0 _).1
  haveI := chainNoiseLaw_isProbability Λ.stepParams u (S.sideAtLevel u)
  obtain ⟨H, hHd⟩ : ∃ H : MarkedSample Λ.stepParams u (S.sideAtLevel u) → ℝ,
      H = fun w => ∏ c, min (localScoreMoment S.tower Λ.response.s₁ u (S.sideAtLevel u) (y c) D k w) M₀ := ⟨_, rfl⟩
  have hH : Measurable H := by
    rw [hHd]
    exact Finset.measurable_prod _ fun c _ => (hlm (y c)).min measurable_const
  have hshift : ∀ (x : TorusSite (S.sideAtLevel u))
      (r : TorusField (fineSide Λ.stepParams.side u (S.sideAtLevel u)) ×
        ChainNoise.ChainNoise Λ.stepParams u (S.sideAtLevel u)),
      localScore rule S.tower Λ.response.s₁ u (S.sideAtLevel u) x D k
        (pairTranslate Λ.stepParams u (S.sideAtLevel u)
          (fun i => (Λ.stepParams.side : ℤ) * axisDisplacement Λ.stepParams.side p (S.data.windowLevel - u) i) r) =
      localScore rule S.tower Λ.response.s₁ u (S.sideAtLevel u) (x + stageTranslation S u p) D k r := fun x r =>
    (hF.reach Λ.g S.β S.data.windowLevel S.data.sideExponent S.tower u _ hAt rule hrule x D k hD hk).2 _ r
  have e1 : ∫ ω, ∏ c, truncatedScoreMoment u z D k M₀ S (S.sampleOf rule ((sampleTranslate S p)^[l * ks c] ω))
        ∂S.sampleLaw =
      ∫ ω, H (S.sampleAtLevel u hu (S.sampleOf rule ω)) ∂S.sampleLaw := by
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    rw [hHd]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [truncatedScoreMoment_eq_pair S rule hu,
      iterate_translate S hu p (fun x r => localScore rule S.tower Λ.response.s₁ u (S.sideAtLevel u) x D k r) hshift
        (l * ks c) _ ω,
      sampleAtLevel_eq, hyd]
    rfl
  have e2 : ∫ ω, H (S.sampleAtLevel u hu (S.sampleOf rule ω)) ∂S.sampleLaw =
      ∫ w, H w ∂(markedSampleLaw S.tower S.β u (S.sideAtLevel u)) := by
    rw [← hmap]
    exact (integral_map hm' hH.aestronglyMeasurable).symm
  have e3 : ∫ w, H w ∂(markedSampleLaw S.tower S.β u (S.sideAtLevel u)) =
      ∫ r, H (rule.chain S.tower u (S.sideAtLevel u) r.1 r.2)
        ∂((wilsonLaw S.β (fineSide Λ.stepParams.side u (S.sideAtLevel u))).prod
          (chainNoiseLaw Λ.stepParams u (S.sideAtLevel u))) := by
    rw [← hcar]
    exact integral_map hchain.aemeasurable hH.aestronglyMeasurable
  have hHΦ : ∀ r, H (rule.chain S.tower u (S.sideAtLevel u) r.1 r.2) = ∏ c, Φ c r := by
    intro r
    rw [hHd, hΦ]
    rfl
  have hint : Integrable (fun r => ∏ c, Φ c r)
      ((wilsonLaw S.β (fineSide Λ.stepParams.side u (S.sideAtLevel u))).prod
        (chainNoiseLaw Λ.stepParams u (S.sideAtLevel u))) := by
    refine Integrable.of_bound (Finset.measurable_prod _ fun c _ => hΦm c).aestronglyMeasurable (M₀ ^ q)
      (Eventually.of_forall fun r => ?_)
    rw [Real.norm_of_nonneg (Finset.prod_nonneg fun c _ => hΦ0 c r)]
    calc ∏ c, Φ c r ≤ ∏ _c : Fin q, M₀ := Finset.prod_le_prod (fun c _ => hΦ0 c r) (fun c _ => hΦ1 c r)
      _ = M₀ ^ q := by simp
  have e4 : ∫ r, H (rule.chain S.tower u (S.sideAtLevel u) r.1 r.2)
        ∂((wilsonLaw S.β (fineSide Λ.stepParams.side u (S.sideAtLevel u))).prod
          (chainNoiseLaw Λ.stepParams u (S.sideAtLevel u))) =
      pairExpectation Λ.stepParams S.β u (S.sideAtLevel u) (fun r => ∏ c, Φ c r) := by
    simp only [hHΦ]
    exact integral_prod _ hint
  rw [e1, e2, e3, e4, ← hGvd]
  exact hmean.trans hprod
end MomentsOnATorus
section Bands
variable {Λ : MomentParameters} {CE : ParameterAssignment → ℝ}
private theorem largeHullIndicator_eq (S : MomentPoint Λ) {u : ℕ} (hu : u ≤ S.data.windowLevel) (z : Fin 4 → ℤ)
    (D : ℝ) (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) : open Classical in
    largeHullIndicator u z D S w =
      if IsLongAt S.tower u (S.sideAtLevel u) D (S.siteAt u z) (S.sampleAtLevel u hu w) then 1 else 0 := by
  classical
  unfold largeHullIndicator
  rw [dif_pos hu]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd h1 h2
  · exact absurd h2 h1
  · rfl
private theorem truncatedScoreMoment_eq (S : MomentPoint Λ) {u : ℕ} (hu : u ≤ S.data.windowLevel) (z : Fin 4 → ℤ)
    (D : ℝ) (k : ℕ) (M : ℝ) (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) :
    truncatedScoreMoment u z D k M S w =
      min (localScoreMoment S.tower Λ.response.s₁ u (S.sideAtLevel u) (S.siteAt u z) D k (S.sampleAtLevel u hu w)) M := by
  unfold truncatedScoreMoment
  rw [dif_pos hu]
private theorem hullSizePower_eq (S : MomentPoint Λ) {u : ℕ} (hu : u ≤ S.data.windowLevel) (z : Fin 4 → ℤ) (k : ℕ)
    (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) :
    hullSizePower u z k S w =
      siteSize S.tower Λ.response.s₁ u (S.sideAtLevel u) (S.sampleAtLevel u hu w) (S.siteAt u z) ^ k := by
  unfold hullSizePower
  rw [dif_pos hu]
private theorem hasBoundedMoments_of_bound {Sq : ℕ → MomentPoint Λ} {p : ℕ} {rule : NoiseRule Λ.stepParams}
    (hK : (translatedTori Sq p).IsPreserving) (g : SampleObservable Λ) (B : ℝ)
    (hB : ∀ i ω, |g (Sq i) ((Sq i).sampleOf rule ω)| ≤ B)
    (hm : ∀ i, AEMeasurable (fun ω => g (Sq i) ((Sq i).sampleOf rule ω)) (Sq i).sampleLaw) :
    TranslatedLaws.HasBoundedMoments (sampleFamily rule Sq p g) := by
  refine ⟨hm, fun q => ⟨B ^ q, fun i => ?_⟩⟩
  haveI : IsProbabilityMeasure (Sq i).sampleLaw := hK.isProbability i
  calc ∫⁻ ω, ENNReal.ofReal (|sampleFamily rule Sq p g i ω| ^ q) ∂((translatedTori Sq p).μ i)
      ≤ ∫⁻ _ω, ENNReal.ofReal (B ^ q) ∂(Sq i).sampleLaw :=
        lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (abs_nonneg _) (hB i ω) q)
    _ = ENNReal.ofReal (B ^ q) := by simp
private theorem aemeasurable_largeHullIndicator (hF : LimitHullInputs Λ CE) (hLaw : sampleBelowLawStatement)
    (hDraw : forgetLastStepStatement) (hSt : StageStatesMeasurableStatement) (S : MomentPoint Λ)
    {rule : NoiseRule Λ.stepParams} (hrule : rule.IsAdmissible S.tower) {u : ℕ} (hu : u ≤ S.data.windowLevel)
    (z : Fin 4 → ℤ) (D : ℝ) :
    AEMeasurable (fun ω => largeHullIndicator u z D S (S.sampleOf rule ω)) S.sampleLaw := by
  classical
  obtain ⟨hm, -⟩ := sampleAtLevel_law hF hLaw hDraw S hrule hu
  have hE : MeasurableSet {w | IsLongAt S.tower u (S.sideAtLevel u) D (S.siteAt u z) w} :=
    measurableSet_hullSet_pred hF.fit hSt S.tower u (S.sideAtLevel u) fun Y =>
      S.siteAt u z ∈ Y ∧ D ≤ (supDiam (hullClass (stageRange S.tower u) Y (S.siteAt u z)) : ℝ)
  have h1 : Measurable fun w : MarkedSample Λ.stepParams u (S.sideAtLevel u) =>
      if IsLongAt S.tower u (S.sideAtLevel u) D (S.siteAt u z) w then (1 : ℝ) else 0 :=
    Measurable.ite hE measurable_const measurable_const
  refine (h1.comp_aemeasurable hm).congr (Eventually.of_forall fun ω => ?_)
  exact (largeHullIndicator_eq S hu z D _).symm
private theorem aemeasurable_truncatedScoreMoment (hF : LimitHullInputs Λ CE) (hLaw : sampleBelowLawStatement)
    (hDraw : forgetLastStepStatement) (hSt : StageStatesMeasurableStatement) (hWh : chainMeasurabilityStatement)
    (S : MomentPoint Λ) {rule : NoiseRule Λ.stepParams} (hrule : rule.IsAdmissible S.tower) {u : ℕ}
    (hu : u ≤ S.data.windowLevel) (z : Fin 4 → ℤ) (D : ℝ) (k : ℕ) (M : ℝ) :
    AEMeasurable (fun ω => truncatedScoreMoment u z D k M S (S.sampleOf rule ω)) S.sampleLaw := by
  obtain ⟨hm, -⟩ := sampleAtLevel_law hF hLaw hDraw S hrule hu
  have h1 : Measurable fun w : MarkedSample Λ.stepParams u (S.sideAtLevel u) =>
      min (localScoreMoment S.tower Λ.response.s₁ u (S.sideAtLevel u) (S.siteAt u z) D k w) M :=
    (measurable_localMoment hF.fit hSt hWh S.tower _ u _ _ D k).min measurable_const
  refine (h1.comp_aemeasurable hm).congr (Eventually.of_forall fun ω => ?_)
  exact (truncatedScoreMoment_eq S hu z D k M _).symm
private theorem exists_band_of_lt {r : ℕ} (hr : 1 ≤ r) (d I : ℕ) (hd : (d : ℝ) < dyadicBandFloor r I) :
    ∃ i < I, dyadicBandFloor r i ≤ d ∧ (d : ℝ) < 2 ^ i * (r : ℝ) := by
  classical
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hex : ∃ i : ℕ, (d : ℝ) < 2 ^ i * (r : ℝ) := by
    refine ⟨d, ?_⟩
    have h1 : (d : ℝ) < 2 ^ d := by exact_mod_cast Nat.lt_two_pow_self
    nlinarith
  refine ⟨Nat.find hex, ?_, ?_, Nat.find_spec hex⟩
  · cases I with
    | zero =>
      have h0 : dyadicBandFloor r 0 = 0 := by simp [dyadicBandFloor]
      rw [h0] at hd
      linarith
    | succ j =>
      have e : dyadicBandFloor r (j + 1) = 2 ^ j * (r : ℝ) := by simp [dyadicBandFloor]
      rw [e] at hd
      exact Nat.lt_succ_of_le (Nat.find_min' hex hd)
  · have key : ∀ i : ℕ, (∀ j < i, ¬ (d : ℝ) < 2 ^ j * (r : ℝ)) → dyadicBandFloor r i ≤ d := by
      intro i h
      cases i with
      | zero =>
        have h0 : dyadicBandFloor r 0 = 0 := by simp [dyadicBandFloor]
        rw [h0]
        exact Nat.cast_nonneg d
      | succ j =>
        have e : dyadicBandFloor r (j + 1) = 2 ^ j * (r : ℝ) := by simp [dyadicBandFloor]
        rw [e]
        exact not_lt.mp (h j (Nat.lt_succ_self j))
    exact key _ fun j hj => Nat.find_min hex hj
private theorem truncatedSize_le_bandSum {ℓ : StepParameters} (T : StageTower ℓ) {s₁ : ℝ} (hs : 0 ≤ s₁) {u n : ℕ}
    [NeZero n] (hr : 1 ≤ stageRange T u) (y : TorusSite n) (w : MarkedSample ℓ u n) (k : ℕ) (hk : 1 ≤ k)
    (pw : ℕ → ℕ) (hpw : ∀ i, 2 ≤ pw i)
    (hsize : 0 ≤ siteSize T s₁ u n w y) (hoff : y ∉ hullSet T u n w → siteSize T s₁ u n w y = 0)
    (hloc : ∀ D : ℝ, 0 < D → y ∈ hullSet T u n w →
      ((supDiam (hullClass (stageRange T u) (hullSet T u n w) y) : ℕ) : ℝ) < D →
      y ∈ (localHullData T s₁ u n w (localHullBox T u y D)).1 ∧
        (localHullData T s₁ u n w (localHullBox T u y D)).2 y = siteSize T s₁ u n w y)
    (I M : ℕ) (E : ℕ → ℝ) (hE : ∀ i, (IsLongAt T u n (dyadicBandFloor (stageRange T u) i) y w → E i = 1) ∧
      (¬ IsLongAt T u n (dyadicBandFloor (stageRange T u) i) y w → E i = 0)) :
    min (siteSize T s₁ u n w y ^ k) (M : ℝ) * (1 - E I) ≤
      ∑ i ∈ Finset.range I, (min (localScoreMoment T s₁ u n y (2 ^ i * (stageRange T u : ℝ)) (k * pw i) w)
        (((M ^ pw i : ℕ) : ℝ) + 1)) ^ (1 / (pw i : ℝ)) * E i := by
  classical
  have hE01 : ∀ i, 0 ≤ E i := fun i => by
    by_cases h : IsLongAt T u n (dyadicBandFloor (stageRange T u) i) y w
    · rw [(hE i).1 h]
      norm_num
    · rw [(hE i).2 h]
  have hterm : ∀ i ∈ Finset.range I,
      0 ≤ (min (localScoreMoment T s₁ u n y (2 ^ i * (stageRange T u : ℝ)) (k * pw i) w)
        (((M ^ pw i : ℕ) : ℝ) + 1)) ^ (1 / (pw i : ℝ)) * E i := fun i _ =>
    mul_nonneg (Real.rpow_nonneg (le_min (localMoment_nonneg T hs u n y _ _ w) (by positivity)) _) (hE01 i)
  have hsum0 := Finset.sum_nonneg hterm
  by_cases hy : y ∈ hullSet T u n w
  · by_cases hI : IsLongAt T u n (dyadicBandFloor (stageRange T u) I) y w
    · rw [(hE I).1 hI]
      simpa using hsum0
    · rw [(hE I).2 hI, sub_zero, mul_one]
      have hdI : ((supDiam (hullClass (stageRange T u) (hullSet T u n w) y) : ℕ) : ℝ) <
          dyadicBandFloor (stageRange T u) I := not_le.1 fun h => hI ⟨hy, h⟩
      obtain ⟨i, hiI, hfl, hlt⟩ := exists_band_of_lt hr _ I hdI
      have hDpos : (0 : ℝ) < 2 ^ i * (stageRange T u : ℝ) := by positivity
      obtain ⟨hl1, hl2⟩ := hloc _ hDpos hy hlt
      have hEi : E i = 1 := (hE i).1 ⟨hy, hfl⟩
      have hmom : localScoreMoment T s₁ u n y (2 ^ i * (stageRange T u : ℝ)) (k * pw i) w =
          siteSize T s₁ u n w y ^ (k * pw i) := by
        unfold localScoreMoment
        rw [if_pos hl1, hl2]
      have hp2 := hpw i
      obtain ⟨a, ha⟩ : ∃ a : ℝ, a = min (siteSize T s₁ u n w y ^ k) (M : ℝ) := ⟨_, rfl⟩
      have ha0 : 0 ≤ a := by
        rw [ha]
        exact le_min (pow_nonneg hsize k) (Nat.cast_nonneg M)
      have h1 : a ^ pw i ≤ min (siteSize T s₁ u n w y ^ (k * pw i)) (((M ^ pw i : ℕ) : ℝ) + 1) := by
        refine le_min ?_ ?_
        · rw [pow_mul]
          exact pow_le_pow_left₀ ha0 (ha ▸ min_le_left _ _) _
        · have h2 : a ^ pw i ≤ (M : ℝ) ^ pw i := pow_le_pow_left₀ ha0 (ha ▸ min_le_right _ _) _
          push_cast
          linarith
      have h3 : a ≤ (min (siteSize T s₁ u n w y ^ (k * pw i)) (((M ^ pw i : ℕ) : ℝ) + 1)) ^ (1 / (pw i : ℝ)) := by
        calc a = (a ^ pw i) ^ (1 / (pw i : ℝ)) := by
              rw [one_div]
              exact (Real.pow_rpow_inv_natCast ha0 (by omega)).symm
          _ ≤ _ := Real.rpow_le_rpow (pow_nonneg ha0 _) h1 (by positivity)
      have hsingle := Finset.single_le_sum hterm (Finset.mem_range.2 hiI)
      rw [hEi, mul_one, hmom] at hsingle
      rw [← ha]
      exact h3.trans hsingle
  · have hz : siteSize T s₁ u n w y = 0 := hoff hy
    rw [hz, zero_pow (by omega), min_eq_left (Nat.cast_nonneg M), zero_mul]
    exact hsum0
end Bands
section Final
variable {Λ : MomentParameters} {CE : ParameterAssignment → ℝ}
private theorem condMean_truncated_le (hF : LimitHullInputs Λ CE) (hLaw : sampleBelowLawStatement)
    (hDraw : forgetLastStepStatement) (hSt : StageStatesMeasurableStatement) (hWh : chainMeasurabilityStatement)
    (hBo : HullsInEveryVolume.noiseChainMeasurableStatement) (hMC : separateCellsExpectationStatement)
    (hMe : jointLimitPropertiesStatement) (hEv : multipleTranslatesBoundStatement) {S : MomentPoint Λ}
    (F : LimitLawAtPoint S) (hKeep : (translatedTori F.points F.period).IsPreserving) (j : F.Index) {u : ℕ}
    (hu : u ≤ S.data.windowLevel) (z : Fin 4 → ℤ) (D : ℝ) (hD : 0 < D) (k : ℕ) (hk : 1 ≤ k) (M₀ : ℝ) (hM₀ : 0 < M₀)
    (hg : F.observables j = truncatedScoreMoment u z D k M₀) :
    ∀ᵐ v ∂F.law, F.condMeanAt j v ≤ 16 ^ k * (k.factorial : ℝ) * Real.exp (CE Λ.table * Real.log (S.coupling u) *
      ((leastPowerAbove Λ.stepParams.side ⌈16 * D + 40 * (clusterRange (S.coupling u) : ℝ)⌉₊ : ℕ) : ℝ) ^ 4) := by
  haveI := F.countable_index
  obtain ⟨-, h2, h3, -, -, -⟩ := hMe (translatedTori F.points F.period) F.Index
    (fun j => sampleFamily F.rule F.points F.period (F.observables j)) F.law hKeep F.hasBoundedMoments F.isJointLimitLaw
  obtain ⟨l, hl⟩ : ∃ l, l = leastPowerAbove Λ.stepParams.side ⌈16 * D + 40 * (clusterRange (S.coupling u) : ℝ)⌉₊ :=
    ⟨_, rfl⟩
  rw [← hl]
  have hL1 : 1 < Λ.stepParams.side := by
    have := hF.fit.L_ge
    omega
  have hl1 : 1 ≤ l := by
    rw [hl]
    exact Nat.pos_of_ne_zero (pow_ne_zero _ (by omega))
  have hval : ∀ i ω, 0 ≤ sampleFamily F.rule F.points F.period (F.observables j) i ω ∧
      sampleFamily F.rule F.points F.period (F.observables j) i ω ≤ M₀ := by
    intro i ω
    show 0 ≤ F.observables j (F.points i) _ ∧ F.observables j (F.points i) _ ≤ M₀
    rw [hg]
    unfold truncatedScoreMoment
    split_ifs
    · exact ⟨le_min (localMoment_nonneg _ hF.s_nonneg _ _ _ _ _ _) hM₀.le, min_le_right _ _⟩
    · exact ⟨le_rfl, hM₀.le⟩
  have hbd : ∀ᵐ v ∂F.law, 0 ≤ v (j, 0) ∧ v (j, 0) ≤ M₀ := by
    have h := h3 1 (fun _ => (j, 0)) (fun x => max 0 (-x 0) + max 0 (x 0 - M₀))
      ((continuous_const.max (continuous_apply 0).neg).add
        (continuous_const.max ((continuous_apply 0).sub continuous_const)))
      (Eventually.of_forall fun i ω => by
        have h1 := hval i ω
        show max 0 (-sampleFamily F.rule F.points F.period (F.observables j) i ω) +
          max 0 (sampleFamily F.rule F.points F.period (F.observables j) i ω - M₀) = 0
        rw [max_eq_left (by linarith [h1.1]), max_eq_left (by linarith [h1.2])]
        simp)
    filter_upwards [h] with v hv
    have h1 : 0 ≤ max 0 (-v (j, 0)) := le_max_left _ _
    have h2' : 0 ≤ max 0 (v (j, 0) - M₀) := le_max_left _ _
    have h3' : -v (j, 0) ≤ max 0 (-v (j, 0)) := le_max_right _ _
    have h4 : v (j, 0) - M₀ ≤ max 0 (v (j, 0) - M₀) := le_max_right _ _
    have hv' : max 0 (-v (j, 0)) + max 0 (v (j, 0) - M₀) = 0 := hv
    constructor <;> linarith
  have hGv0 : 0 ≤ 16 ^ k * (k.factorial : ℝ) * Real.exp (CE Λ.table * Real.log (S.coupling u) * (l : ℝ) ^ 4) := by
    positivity
  refine hEv (translatedTori F.points F.period) F.Index (fun j => sampleFamily F.rule F.points F.period (F.observables j))
    F.law hKeep F.hasBoundedMoments F.isJointLimitLaw j _ 1 M₀ l hl1 hGv0 hbd fun q hq => ⟨1, fun ks hks => ?_⟩
  obtain ⟨-, hlim⟩ := h2 q (fun c => (j, l * ks c))
  refine le_of_tendsto hlim ?_
  filter_upwards [eventually_le_half_side hF F u
    (((∑ c, ks c) * translationStep Λ.stepParams.side F.period (S.data.windowLevel - u) + 2) * l)] with i hi
  obtain ⟨hK, hβ, hT, -⟩ := points_data F i
  have hu' : u ≤ (F.points i).data.windowLevel := by rw [hK]; exact hu
  have hrule' : F.rule.IsAdmissible (F.points i).tower := by rw [hT]; exact F.rule_admissible
  have hinj : Function.Injective ks := by
    intro c e hce
    by_contra hne
    rcases hks c e hne with h | h <;> omega
  have h2B := Nat.div_mul_le_self ((F.points i).sideAtLevel u) 2
  have hres := truncatedMoments_integral_le (CE := CE) hF hLaw hDraw hSt hWh hBo hMC (F.points i) hrule' hu' z D hD k
    hk M₀ hM₀ F.period F.one_le_period q ks hinj l
    (by rw [stageRange_points F i hu, hl]) (by
      have h3' : 2 * l ≤ ((∑ c, ks c) * translationStep Λ.stepParams.side F.period (S.data.windowLevel - u) + 2) * l :=
        Nat.mul_le_mul_right _ (by omega)
      omega) (fun c => by
      rw [hK]
      have h3' : (ks c * translationStep Λ.stepParams.side F.period (S.data.windowLevel - u) + 1) * l ≤
          ((∑ c, ks c) * translationStep Λ.stepParams.side F.period (S.data.windowLevel - u) + 2) * l := by
        refine Nat.mul_le_mul_right _ ?_
        have h4 : ks c ≤ ∑ c, ks c := Finset.single_le_sum (f := ks) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
        have h5 := Nat.mul_le_mul_right (translationStep Λ.stepParams.side F.period (S.data.windowLevel - u)) h4
        omega
      omega)
  rw [stageCoupling_points F i hu] at hres
  rw [one_mul]
  show ∫ ω, ∏ c, F.observables j (F.points i) ((F.points i).sampleOf F.rule
    ((sampleTranslate (F.points i) F.period)^[l * ks c] ω)) ∂(F.points i).sampleLaw ≤ _
  rw [hg]
  exact hres
private theorem ae_eq_zero_of_closed {T : TranslatedLaws} {J : Type} {X : J → T.Family}
    {P : Measure (TranslateValues J)}
    (h3 : ∀ (l : ℕ) (a : Fin l → J × ℕ) (G : (Fin l → ℝ) → ℝ), Continuous G →
      (∀ᶠ i in atTop, ∀ ω, G (fun c => TranslatedLaws.translate (X (a c).1) (a c).2 i ω) = 0) →
      ∀ᵐ v ∂P, G (fun c => v (a c)) = 0)
    {ι : Type} [Fintype ι] (a : ι → J × ℕ) (G : (ι → ℝ) → ℝ) (hG : Continuous G)
    (h : ∀ i ω, G (fun c => TranslatedLaws.translate (X (a c).1) (a c).2 i ω) = 0) :
    ∀ᵐ v ∂P, G (fun c => v (a c)) = 0 := by
  obtain ⟨e⟩ : Nonempty (ι ≃ Fin (Fintype.card ι)) := ⟨Fintype.equivFin ι⟩
  have h1 := h3 _ (fun c => a (e.symm c)) (fun x => G fun c => x (e c))
    (hG.comp (continuous_pi fun c => continuous_apply _))
    (Eventually.of_forall fun i ω => by simpa using h i ω)
  filter_upwards [h1] with v hv
  simpa using hv
private theorem leastPowerAbove_le {L : ℕ} (hL1 : 1 < L) {a : ℝ} (ha : 2 ≤ a) :
    ((leastPowerAbove L ⌈a⌉₊ : ℕ) : ℝ) ≤ (L : ℝ) * a := by
  have hc2 : 1 < ⌈a⌉₊ := Nat.lt_ceil.2 (by norm_num; linarith)
  obtain ⟨p, hp⟩ : ∃ p, p = Nat.clog L ⌈a⌉₊ := ⟨_, rfl⟩
  have hp1 : 1 ≤ p := by
    rw [hp]
    exact Nat.clog_pos hL1 hc2
  have h1 : L ^ (p - 1) < ⌈a⌉₊ := by
    rw [hp]
    exact Nat.pow_pred_clog_lt_self hL1 hc2
  have h2 : ((L ^ (p - 1) : ℕ) : ℝ) ≤ a := by
    have h3 : L ^ (p - 1) + 1 ≤ ⌈a⌉₊ := h1
    have h4 : ((L ^ (p - 1) + 1 : ℕ) : ℝ) ≤ (⌈a⌉₊ : ℝ) := by exact_mod_cast h3
    have h5 : (⌈a⌉₊ : ℝ) < a + 1 := Nat.ceil_lt_add_one (by linarith)
    push_cast at h4 ⊢
    linarith
  have h6 : leastPowerAbove L ⌈a⌉₊ = L * L ^ (p - 1) := by
    show L ^ Nat.clog L ⌈a⌉₊ = _
    rw [← hp, ← pow_succ', Nat.sub_add_cancel hp1]
  rw [h6]
  push_cast at h2 ⊢
  exact mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg L)
private def extendLaw {S : MomentPoint Λ} (F : LimitLawAtPoint S) (J' : Type) [Countable J']
    (g' : J' → SampleObservable Λ) (sub : ℕ → ℕ) (hsub : StrictMono sub) (P' : Measure (TranslateValues (F.Index ⊕ J')))
    (hm : ∀ j, TranslatedLaws.HasBoundedMoments
      (sampleFamily F.rule (fun i => F.points (sub i)) F.period (Sum.elim F.observables g' j)))
    (hl : IsJointLimitLaw (translatedTori (fun i => F.points (sub i)) F.period)
      (fun j => sampleFamily F.rule (fun i => F.points (sub i)) F.period (Sum.elim F.observables g' j)) P') :
    LimitLawAtPoint S where
  rule := F.rule
  rule_admissible := F.rule_admissible
  period := F.period
  one_le_period := F.one_le_period
  exponents := fun i => F.exponents (sub i)
  strictMono_exponents := fun _ _ h => F.strictMono_exponents (hsub h)
  points := fun i => F.points (sub i)
  points_eq := fun i => F.points_eq (sub i)
  Index := F.Index ⊕ J'
  countable_index := by
    haveI := F.countable_index
    infer_instance
  observables := Sum.elim F.observables g'
  hasBoundedMoments := hm
  law := P'
  isJointLimitLaw := hl
end Final
section Sizes
variable {Λ : MomentParameters} {CE : ParameterAssignment → ℝ}
private theorem hullDecayRate_pos (Tb : ParameterAssignment) (hD : Tb.Admissible) : 0 < hullDecayRate Tb := by apply _root_.YangMills.SharedProofs.p22298 <;> assumption
private theorem siteSize_facts (hF : LimitHullInputs Λ CE) (S : MomentPoint Λ) {u : ℕ} (hu : u ≤ S.data.windowLevel)
    (y : TorusSite (S.sideAtLevel u)) (w : MarkedSample Λ.stepParams u (S.sideAtLevel u)) :
    0 ≤ siteSize S.tower Λ.response.s₁ u (S.sideAtLevel u) w y ∧
      (y ∉ hullSet S.tower u (S.sideAtLevel u) w → siteSize S.tower Λ.response.s₁ u (S.sideAtLevel u) w y = 0) := by
  classical
  have hoff : y ∉ hullSet S.tower u (S.sideAtLevel u) w → siteSize S.tower Λ.response.s₁ u (S.sideAtLevel u) w y = 0 :=
    fun h => dif_neg h
  refine ⟨?_, hoff⟩
  by_cases hy : y ∈ hullSet S.tower u (S.sideAtLevel u) w
  · have hAt := hullChainAtLevel_of_point S hF.g_pos hF.floor hu
    have hl := ((hF.lies Λ.g S.β S.data.windowLevel S.data.sideExponent S.tower).1 u _ hAt w).2 y
      ((supDiam (hullClass (stageRange S.tower u) (hullSet S.tower u (S.sideAtLevel u) w) y) : ℕ) + 1)
      (by positivity) hy (by linarith)
    rw [← hl.2]
    exact localSizes_nonneg S.tower hF.s_nonneg u _ w _ y
  · rw [hoff hy]
end Sizes
section Sizes2
variable {Λ : MomentParameters} {CE : ParameterAssignment → ℝ}
private theorem condMean_hullSizePower_le (hF : LimitHullInputs Λ CE) (hLaw : sampleBelowLawStatement)
    (hDraw : forgetLastStepStatement) (hSt : StageStatesMeasurableStatement) (hWh : chainMeasurabilityStatement)
    (hBo : HullsInEveryVolume.noiseChainMeasurableStatement) (hMC : separateCellsExpectationStatement)
    (hMe : jointLimitPropertiesStatement) (hEv : multipleTranslatesBoundStatement)
    (hExt : jointLimitExtendStatement) (hBB : invariantCondExpBandBoundStatement) {C : ℝ}
    (hCr : BandRateBound Λ CE C) {S : MomentPoint Λ}
    (F : LimitLawAtPoint S) (hKeep : (translatedTori F.points F.period).IsPreserving) (j : F.Index) {u : ℕ}
    (hu : u ≤ S.data.windowLevel) (z : Fin 4 → ℤ)
    (k : ℕ) (hk : 1 ≤ k) (hg : F.observables j = hullSizePower u z k) :
    ∀ᵐ v ∂F.law, F.condMeanAt j v ≤ C ^ k * (k.factorial : ℝ) ^ 6 *
      Real.exp (-(hullDecayRate Λ.table * S.coupling u / 4)) := by
  classical
  haveI := F.countable_index
  have hAt := hullChainAtLevel_of_point S hF.g_pos hF.floor hu
  have hcx : stageCoupling S.tower u = S.coupling u := stage_coupling_eq S (j := u) (by omega)
  have hx1 : 1 ≤ S.coupling u := by
    rw [← hcx]
    exact hF.one_le.trans (hF.coupling_ge _ _ _ _ _ _ _ hAt)
  obtain ⟨r, hrd⟩ : ∃ r, r = clusterRange (S.coupling u) := ⟨_, rfl⟩
  have hrT : stageRange S.tower u = r := by
    rw [hrd]
    show clusterRange (stageCoupling S.tower u) = _
    rw [hcx]
  have hr1 : 1 ≤ r := by
    rw [hrd]
    exact Nat.ceil_pos.2 (Real.rpow_pos_of_pos (by linarith) _)
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  obtain ⟨hpw, hsum⟩ := hCr S.β S.data.windowLevel S.data.sideExponent S.tower u _ hAt
  rw [hrT] at hpw
  simp only [hrT, hcx] at hsum
  have hL1 : 1 < Λ.stepParams.side := by
    have := hF.fit.L_ge
    omega
  have hc5 : 0 < hullDecayRate Λ.table := hullDecayRate_pos _ hF.drawn
  have hside : ∀ i, (F.points i).data.windowLevel = S.data.windowLevel ∧ (F.points i).tower = S.tower := fun i =>
    ⟨(points_data F i).1, (points_data F i).2.2.1⟩
  have hui : ∀ i, u ≤ (F.points i).data.windowLevel := fun i => by
    rw [(hside i).1]
    exact hu
  have hrulei : ∀ i, F.rule.IsAdmissible (F.points i).tower := fun i => by
    rw [(hside i).2]
    exact F.rule_admissible
  let g' : (ℕ ⊕ (ℕ × ℕ)) → SampleObservable Λ := Sum.elim (fun i => largeHullIndicator u z (dyadicBandFloor r i))
    (fun a => truncatedScoreMoment u z (2 ^ a.1 * (r : ℝ)) (k * holderBandExponent Λ.table.side r a.1) ((a.2 : ℝ) + 1))
  have hevb : ∀ (D : ℝ) (S' : MomentPoint Λ)
      (w : MarkedSample Λ.stepParams S'.data.windowLevel (S'.data.period Λ.stepParams.side)),
      largeHullIndicator u z D S' w = 0 ∨ largeHullIndicator u z D S' w = 1 := by
    intro D S' w
    unfold largeHullIndicator
    split_ifs <;> simp
  have hcutb : ∀ (D : ℝ) (k' : ℕ) (M : ℝ) (S' : MomentPoint Λ)
      (w : MarkedSample Λ.stepParams S'.data.windowLevel (S'.data.period Λ.stepParams.side)), 0 ≤ M →
      0 ≤ truncatedScoreMoment u z D k' M S' w ∧ truncatedScoreMoment u z D k' M S' w ≤ M := by
    intro D k' M S' w hM
    unfold truncatedScoreMoment
    split_ifs
    · exact ⟨le_min (localMoment_nonneg _ hF.s_nonneg _ _ _ _ _ _) hM, min_le_right _ _⟩
    · exact ⟨le_rfl, hM⟩
  have hX' : ∀ j', TranslatedLaws.HasBoundedMoments (sampleFamily F.rule F.points F.period (g' j')) := by
    rintro (i | ⟨i, M⟩)
    · refine hasBoundedMoments_of_bound hKeep _ 1 (fun i' ω => ?_)
        (fun i' => aemeasurable_largeHullIndicator hF hLaw hDraw hSt (F.points i') (hrulei i') (hui i') z _)
      rcases hevb (dyadicBandFloor r i) (F.points i') ((F.points i').sampleOf F.rule ω) with e | e
      · show |largeHullIndicator u z (dyadicBandFloor r i) (F.points i') _| ≤ 1
        rw [e]
        norm_num
      · show |largeHullIndicator u z (dyadicBandFloor r i) (F.points i') _| ≤ 1
        rw [e]
        norm_num
    · refine hasBoundedMoments_of_bound hKeep _ ((M : ℝ) + 1) (fun i' ω => ?_)
        (fun i' => aemeasurable_truncatedScoreMoment hF hLaw hDraw hSt hWh (F.points i') (hrulei i') (hui i') z _ _ _)
      have h1 := hcutb (2 ^ i * (r : ℝ)) (k * holderBandExponent Λ.table.side r i) ((M : ℝ) + 1) (F.points i')
        ((F.points i').sampleOf F.rule ω) (by positivity)
      show |truncatedScoreMoment u z (2 ^ i * (r : ℝ)) (k * holderBandExponent Λ.table.side r i) ((M : ℝ) + 1)
        (F.points i') _| ≤ _
      rw [abs_of_nonneg h1.1]
      exact h1.2
  obtain ⟨sub, P', hsub, hlim', hmap, hback⟩ := hExt (translatedTori F.points F.period) F.Index (ℕ ⊕ (ℕ × ℕ))
    (fun j => sampleFamily F.rule F.points F.period (F.observables j))
    (fun j' => sampleFamily F.rule F.points F.period (g' j')) F.law hKeep F.hasBoundedMoments hX' F.isJointLimitLaw
  have : IsProbabilityMeasure P' := hlim'.isProbability
  have hKeep' : (translatedTori (fun i => F.points (sub i)) F.period).IsPreserving :=
    ⟨fun i => hKeep.isProbability (sub i), fun i => hKeep.measurePreserving (sub i)⟩
  have hm' : ∀ j'', TranslatedLaws.HasBoundedMoments
      (sampleFamily F.rule (fun i => F.points (sub i)) F.period (Sum.elim F.observables g' j'')) := by
    rintro (j₁ | j₂)
    · exact ⟨fun i => (F.hasBoundedMoments j₁).aemeasurable (sub i), fun q =>
        let ⟨C', hC'⟩ := (F.hasBoundedMoments j₁).moment_bound q
        ⟨C', fun i => hC' (sub i)⟩⟩
    · exact ⟨fun i => (hX' j₂).aemeasurable (sub i), fun q =>
        let ⟨C', hC'⟩ := (hX' j₂).moment_bound q
        ⟨C', fun i => hC' (sub i)⟩⟩
  have hl' : IsJointLimitLaw (translatedTori (fun i => F.points (sub i)) F.period)
      (fun j => sampleFamily F.rule (fun i => F.points (sub i)) F.period (Sum.elim F.observables g' j)) P' := by
    refine ⟨hlim'.isProbability, fun l a G hG hb => ?_⟩
    refine (hlim'.tendsto l a G hG hb).congr fun i => integral_congr_ae (Eventually.of_forall fun ω => ?_)
    show G _ = G _
    congr 1
    funext c
    obtain ⟨(j₁ | j₂), t⟩ := a c <;> rfl
  let F' : LimitLawAtPoint S := extendLaw F (ℕ ⊕ (ℕ × ℕ)) g' sub hsub P' hm' hl'
  obtain ⟨-, h2, h3, -, -, -⟩ := hMe (translatedTori (fun i => F.points (sub i)) F.period) (F.Index ⊕ (ℕ ⊕ (ℕ × ℕ)))
    (fun j => sampleFamily F.rule (fun i => F.points (sub i)) F.period (Sum.elim F.observables g' j)) P' hKeep' hm' hl'
  obtain ⟨-, h2F, -, -, -, -⟩ := hMe (translatedTori F.points F.period) F.Index
    (fun j => sampleFamily F.rule F.points F.period (F.observables j)) F.law hKeep F.hasBoundedMoments F.isJointLimitLaw
  have hcoord : ∀ a, Integrable (evalAtZero a) P' := fun a => by
    have hone := (h2 1 (fun _ => (a, 0))).1
    exact show Integrable (fun v : TranslateValues (F.Index ⊕ (ℕ ⊕ (ℕ × ℕ))) => v (a, 0)) P' from by simpa using hone
  have hcoordF : Integrable (evalAtZero j) F.law := by
    have hone := (h2F 1 (fun _ => (j, 0))).1
    exact show Integrable (fun v : TranslateValues F.Index => v (j, 0)) F.law from by simpa using hone
  have hnonneg : ∀ a, (∀ i ω, 0 ≤ sampleFamily F.rule (fun i => F.points (sub i)) F.period
      (Sum.elim F.observables g' a) i ω) → ∀ᵐ v ∂P', 0 ≤ evalAtZero a v := by
    intro a h
    have h1 := h3 1 (fun _ => (a, 0)) (fun x => max 0 (-x 0)) (continuous_const.max (continuous_apply 0).neg)
      (Eventually.of_forall fun i ω => by
        show max 0 (-sampleFamily F.rule (fun i => F.points (sub i)) F.period (Sum.elim F.observables g' a) i ω) = 0
        exact max_eq_left (by linarith [h i ω]))
    filter_upwards [h1] with v hv
    have h4 : -v (a, 0) ≤ max 0 (-v (a, 0)) := le_max_right _ _
    have hv' : max 0 (-v (a, 0)) = 0 := hv
    show 0 ≤ v (a, 0)
    linarith
  obtain ⟨Bd, hBd⟩ : ∃ Bd, Bd = C ^ k * (k.factorial : ℝ) ^ 6 *
      Real.exp (-(hullDecayRate Λ.table * S.coupling u / 4)) := ⟨_, rfl⟩
  have hsumk := fun (I : ℕ) (q : ℕ → ℝ)
      (hq : ∀ i, q i ≤ ((Λ.table.side : ℝ) * (16 * (2 ^ i * (r : ℝ)) + 40 * (r : ℝ))) ^ 4) => hsum k I q hk hq
  rw [← hBd]
  simp only [← hBd] at hsumk
  obtain ⟨lc, hlc⟩ : ∃ lc : ℕ → ℕ,
      lc = fun i => leastPowerAbove Λ.stepParams.side ⌈16 * (2 ^ i * (r : ℝ)) + 40 * (r : ℝ)⌉₊ := ⟨_, rfl⟩
  have hlq : ∀ i, ((lc i : ℕ) : ℝ) ^ 4 ≤ ((Λ.table.side : ℝ) * (16 * (2 ^ i * (r : ℝ)) + 40 * (r : ℝ))) ^ 4 := by
    intro i
    rw [hlc]
    refine pow_le_pow_left₀ (Nat.cast_nonneg _) (leastPowerAbove_le hL1 ?_) 4
    have : (0 : ℝ) ≤ 2 ^ i * (r : ℝ) := by positivity
    linarith
  obtain ⟨Gv, hGvd⟩ : ∃ Gv : ℕ → ℝ, Gv = fun i => 16 ^ (k * holderBandExponent Λ.table.side r i) *
      ((k * holderBandExponent Λ.table.side r i).factorial : ℝ) *
      Real.exp (|CE Λ.table| * Real.log (S.coupling u) * ((lc i : ℕ) : ℝ) ^ 4) := ⟨_, rfl⟩
  obtain ⟨bb, hbb⟩ : ∃ bb : ℕ → ℝ,
      bb = fun i => Real.exp (-(hullDecayRate Λ.table * S.coupling u * (1 + dyadicBandFloor r i / (r : ℝ)))) :=
    ⟨_, rfl⟩
  have hsumB : ∀ I, ∑ i ∈ Finset.range I, Gv i ^ (1 / (holderBandExponent Λ.table.side r i : ℝ)) *
      bb i ^ (1 - 1 / (holderBandExponent Λ.table.side r i : ℝ)) ≤ Bd := by
    intro I
    rw [hGvd, hbb]
    exact hsumk I (fun i => ((lc i : ℕ) : ℝ) ^ 4) hlq
  have hfloor0 : ∀ i, 0 ≤ dyadicBandFloor r i := by
    intro i
    unfold dyadicBandFloor
    split_ifs
    · exact le_rfl
    · positivity
  have hes : ∀ i, ∀ᵐ v ∂P', invariantCondExp P' (evalAtZero (Sum.inr (Sum.inl i) : F.Index ⊕ (ℕ ⊕ (ℕ × ℕ)))) v ≤
      bb i := by
    intro i
    have h := condMean_largeHull_le hF hLaw hDraw hSt hMe F' hKeep' (Sum.inr (Sum.inl i) : F.Index ⊕ (ℕ ⊕ (ℕ × ℕ)))
      hu z (dyadicBandFloor r i) (hfloor0 i) rfl
    rw [← hrd] at h
    rw [hbb]
    exact h
  have hlog : 0 ≤ Real.log (S.coupling u) := Real.log_nonneg hx1
  have hfs : ∀ i M : ℕ, ∀ᵐ v ∂P',
      invariantCondExp P' (evalAtZero (Sum.inr (Sum.inr (i, M)) : F.Index ⊕ (ℕ ⊕ (ℕ × ℕ)))) v ≤ Gv i := by
    intro i M
    have hp2 := hpw i
    have hpos : (0 : ℝ) < 2 ^ i * (r : ℝ) := by positivity
    have h := condMean_truncated_le hF hLaw hDraw hSt hWh hBo hMC hMe hEv F' hKeep'
      (Sum.inr (Sum.inr (i, M)) : F.Index ⊕ (ℕ ⊕ (ℕ × ℕ))) hu z
      (2 ^ i * (r : ℝ)) hpos (k * holderBandExponent Λ.table.side r i) (Nat.mul_pos hk (by omega)) ((M : ℝ) + 1)
      (by positivity) rfl
    rw [← hrd] at h
    have hle : 16 ^ (k * holderBandExponent Λ.table.side r i) *
        ((k * holderBandExponent Λ.table.side r i).factorial : ℝ) * Real.exp (CE Λ.table * Real.log (S.coupling u) *
        ((leastPowerAbove Λ.stepParams.side ⌈16 * (2 ^ i * (r : ℝ)) + 40 * (r : ℝ)⌉₊ : ℕ) : ℝ) ^ 4) ≤ Gv i := by
      rw [hGvd, hlc]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
      have h1 := le_abs_self (CE Λ.table)
      gcongr
    filter_upwards [h] with v hv
    exact le_trans hv hle
  have he : ∀ i, Integrable (evalAtZero (Sum.inr (Sum.inl i) : F.Index ⊕ (ℕ ⊕ (ℕ × ℕ)))) P' ∧
      ∀ᵐ v ∂P', evalAtZero (Sum.inr (Sum.inl i) : F.Index ⊕ (ℕ ⊕ (ℕ × ℕ))) v = 0 ∨
        evalAtZero (Sum.inr (Sum.inl i) : F.Index ⊕ (ℕ ⊕ (ℕ × ℕ))) v = 1 := by
    intro i
    refine ⟨hcoord _, ?_⟩
    have h1 := h3 1 (fun _ => ((Sum.inr (Sum.inl i) : F.Index ⊕ (ℕ ⊕ (ℕ × ℕ))), 0)) (fun x => x 0 * (1 - x 0))
      (by fun_prop)
      (Eventually.of_forall fun i' ω => by
        show largeHullIndicator u z (dyadicBandFloor r i) (F.points (sub i')) ((F.points (sub i')).sampleOf F.rule ω) *
          (1 - largeHullIndicator u z (dyadicBandFloor r i) (F.points (sub i'))
            ((F.points (sub i')).sampleOf F.rule ω)) = 0
        rcases hevb (dyadicBandFloor r i) (F.points (sub i')) ((F.points (sub i')).sampleOf F.rule ω) with e | e
        · rw [e]
          ring
        · rw [e]
          ring)
    filter_upwards [h1] with v hv
    rcases mul_eq_zero.1 hv with e | e
    · exact Or.inl e
    · exact Or.inr (by
        show v _ = 1
        have e' : (1 : ℝ) - v ((Sum.inr (Sum.inl i) : F.Index ⊕ (ℕ ⊕ (ℕ × ℕ))), 0) = 0 := e
        linarith)
  have hf : ∀ i M : ℕ, Integrable (evalAtZero (Sum.inr (Sum.inr (i, M)) : F.Index ⊕ (ℕ ⊕ (ℕ × ℕ)))) P' ∧
      ∀ᵐ v ∂P', 0 ≤ evalAtZero (Sum.inr (Sum.inr (i, M)) : F.Index ⊕ (ℕ ⊕ (ℕ × ℕ))) v := by
    intro i M
    refine ⟨hcoord _, hnonneg _ fun i' ω => ?_⟩
    exact (hcutb _ _ _ (F.points (sub i')) ((F.points (sub i')).sampleOf F.rule ω) (by positivity)).1
  have hY0 : ∀ᵐ v ∂P', 0 ≤ evalAtZero (Sum.inl j : F.Index ⊕ (ℕ ⊕ (ℕ × ℕ))) v := by
    refine hnonneg _ fun i' ω => ?_
    show 0 ≤ F.observables j (F.points (sub i')) _
    rw [hg, hullSizePower_eq _ (hui _)]
    exact pow_nonneg (siteSize_facts hF _ (hui _) _ _).1 _
  have hb0 : ∀ i, 0 ≤ bb i := fun i => by
    rw [hbb]
    exact (Real.exp_pos _).le
  have hG0 : ∀ i, 0 ≤ Gv i := fun i => by
    rw [hGvd]
    positivity
  have hlimb : Tendsto bb atTop (𝓝 0) := by
    have hxpos : 0 < hullDecayRate Λ.table * S.coupling u := mul_pos hc5 (by linarith)
    have h1 : Tendsto (fun i : ℕ => hullDecayRate Λ.table * S.coupling u * (1 + dyadicBandFloor r i / (r : ℝ)))
        atTop atTop := by
      refine Tendsto.const_mul_atTop hxpos ?_
      refine tendsto_atTop_mono (f := fun i : ℕ => (i : ℝ)) (fun i => ?_) tendsto_natCast_atTop_atTop
      cases i with
      | zero => simp [dyadicBandFloor]
      | succ t =>
        have e : dyadicBandFloor r (t + 1) / (r : ℝ) = 2 ^ t := by
          simp only [dyadicBandFloor, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, Nat.add_sub_cancel]
          field_simp
        rw [e]
        have h2 : (t : ℝ) < 2 ^ t := by exact_mod_cast Nat.lt_two_pow_self
        push_cast
        linarith
    rw [hbb]
    exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)
  have hrel : ∀ I M : ℕ, ∀ᵐ v ∂P', min (evalAtZero (Sum.inl j : F.Index ⊕ (ℕ ⊕ (ℕ × ℕ))) v) (M : ℝ) *
      (1 - evalAtZero (Sum.inr (Sum.inl I) : F.Index ⊕ (ℕ ⊕ (ℕ × ℕ))) v) ≤
      ∑ i ∈ Finset.range I, evalAtZero (Sum.inr (Sum.inr (i, M ^ holderBandExponent Λ.table.side r i)) :
          F.Index ⊕ (ℕ ⊕ (ℕ × ℕ))) v ^
        (1 / (holderBandExponent Λ.table.side r i : ℝ)) *
          evalAtZero (Sum.inr (Sum.inl i) : F.Index ⊕ (ℕ ⊕ (ℕ × ℕ))) v := by
    intro I M
    let a : (Unit ⊕ (Unit ⊕ (Fin I ⊕ Fin I))) → (F.Index ⊕ (ℕ ⊕ (ℕ × ℕ))) × ℕ :=
      Sum.elim (fun _ => (Sum.inl j, 0)) (Sum.elim (fun _ => (Sum.inr (Sum.inl I), 0))
        (Sum.elim (fun i => (Sum.inr (Sum.inl (i : ℕ)), 0))
          (fun i => (Sum.inr (Sum.inr ((i : ℕ), M ^ holderBandExponent Λ.table.side r i)), 0))))
    let G : ((Unit ⊕ (Unit ⊕ (Fin I ⊕ Fin I))) → ℝ) → ℝ := fun x =>
      max 0 (min (x (Sum.inl ())) (M : ℝ) * (1 - x (Sum.inr (Sum.inl ()))) -
        ∑ i : Fin I, x (Sum.inr (Sum.inr (Sum.inr i))) ^ (1 / (holderBandExponent Λ.table.side r i : ℝ)) *
          x (Sum.inr (Sum.inr (Sum.inl i))))
    have hGc : Continuous G := by
      have c0 : ∀ c, Continuous fun x : (Unit ⊕ (Unit ⊕ (Fin I ⊕ Fin I))) → ℝ => x c := fun c => continuous_apply c
      have c1 : Continuous fun x : (Unit ⊕ (Unit ⊕ (Fin I ⊕ Fin I))) → ℝ =>
          min (x (Sum.inl ())) (M : ℝ) * (1 - x (Sum.inr (Sum.inl ()))) :=
        ((c0 _).min continuous_const).mul (continuous_const.sub (c0 _))
      have c2 : Continuous fun x : (Unit ⊕ (Unit ⊕ (Fin I ⊕ Fin I))) → ℝ =>
          ∑ i : Fin I, x (Sum.inr (Sum.inr (Sum.inr i))) ^ (1 / (holderBandExponent Λ.table.side r i : ℝ)) *
            x (Sum.inr (Sum.inr (Sum.inl i))) := by
        refine continuous_finsetSum _ fun i _ => ?_
        exact ((c0 _).rpow_const fun _ => Or.inr (by positivity)).mul (c0 _)
      exact continuous_const.max (c1.sub c2)
    have h1 := ae_eq_zero_of_closed (T := translatedTori (fun i => F.points (sub i)) F.period)
      (X := fun j => sampleFamily F.rule (fun i => F.points (sub i)) F.period (Sum.elim F.observables g' j)) (P := P')
      h3 a G hGc (fun i' ω => by
      have hu' := hui (sub i')
      have hr' : stageRange (F.points (sub i')).tower u = r := (stageRange_points F (sub i') hu).trans hrd.symm
      have hAt' := hullChainAtLevel_of_point (F.points (sub i')) hF.g_pos hF.floor hu'
      have hl := (hF.lies Λ.g (F.points (sub i')).β (F.points (sub i')).data.windowLevel
        (F.points (sub i')).data.sideExponent (F.points (sub i')).tower).1 u _ hAt'
        ((F.points (sub i')).sampleAtLevel u hu' ((F.points (sub i')).sampleOf F.rule ω))
      have hsz := siteSize_facts hF (F.points (sub i')) hu' ((F.points (sub i')).siteAt u z)
        ((F.points (sub i')).sampleAtLevel u hu' ((F.points (sub i')).sampleOf F.rule ω))
      have key := truncatedSize_le_bandSum (F.points (sub i')).tower hF.s_nonneg (by rw [hr']; exact hr1)
        ((F.points (sub i')).siteAt u z)
        ((F.points (sub i')).sampleAtLevel u hu' ((F.points (sub i')).sampleOf F.rule ω)) k hk
        (fun i => holderBandExponent Λ.table.side r i) hpw hsz.1 hsz.2
        (hl.2 _) I M
        (fun i => largeHullIndicator u z (dyadicBandFloor r i) (F.points (sub i')) ((F.points (sub i')).sampleOf F.rule ω))
        (fun i => by
          rw [hr']
          refine ⟨fun h => ?_, fun h => ?_⟩
          · show largeHullIndicator u z (dyadicBandFloor r i) (F.points (sub i')) _ = 1
            rw [largeHullIndicator_eq _ hu' z]
            exact if_pos h
          · show largeHullIndicator u z (dyadicBandFloor r i) (F.points (sub i')) _ = 0
            rw [largeHullIndicator_eq _ hu' z]
            exact if_neg h)
      rw [hr'] at key
      have hmain : min (F.observables j (F.points (sub i')) ((F.points (sub i')).sampleOf F.rule ω)) (M : ℝ) *
          (1 - largeHullIndicator u z (dyadicBandFloor r I) (F.points (sub i')) ((F.points (sub i')).sampleOf F.rule ω)) ≤
          ∑ c : Fin I, truncatedScoreMoment u z (2 ^ (c : ℕ) * (r : ℝ)) (k * holderBandExponent Λ.table.side r c)
              (((M ^ holderBandExponent Λ.table.side r c : ℕ) : ℝ) + 1)
              (F.points (sub i')) ((F.points (sub i')).sampleOf F.rule ω) ^
                (1 / (holderBandExponent Λ.table.side r c : ℝ)) *
            largeHullIndicator u z (dyadicBandFloor r c) (F.points (sub i')) ((F.points (sub i')).sampleOf F.rule ω) := by
        rw [hg, hullSizePower_eq _ hu' z k,
          ← Finset.sum_range (fun c => truncatedScoreMoment u z (2 ^ c * (r : ℝ)) (k * holderBandExponent Λ.table.side r c)
              (((M ^ holderBandExponent Λ.table.side r c : ℕ) : ℝ) + 1)
              (F.points (sub i')) ((F.points (sub i')).sampleOf F.rule ω) ^
                (1 / (holderBandExponent Λ.table.side r c : ℝ)) *
            largeHullIndicator u z (dyadicBandFloor r c) (F.points (sub i')) ((F.points (sub i')).sampleOf F.rule ω))]
        simp only [truncatedScoreMoment_eq _ hu' z]
        exact key
      exact max_eq_left (sub_nonpos.2 hmain))
    filter_upwards [h1] with v hv
    have h5 : min (v (Sum.inl j, 0)) (M : ℝ) * (1 - v (Sum.inr (Sum.inl I), 0)) -
        ∑ i : Fin I, v (Sum.inr (Sum.inr ((i : ℕ), M ^ holderBandExponent Λ.table.side r i)), 0) ^
            (1 / (holderBandExponent Λ.table.side r i : ℝ)) *
          v (Sum.inr (Sum.inl (i : ℕ)), 0) ≤ 0 := (le_max_right 0 _).trans (le_of_eq hv)
    rw [Finset.sum_range]
    exact sub_nonpos.1 h5
  have hres := hBB (F.Index ⊕ (ℕ ⊕ (ℕ × ℕ))) P' (evalAtZero (Sum.inl j)) (fun i => evalAtZero (Sum.inr (Sum.inl i)))
    (fun i M => evalAtZero (Sum.inr (Sum.inr (i, M)))) (fun i => holderBandExponent Λ.table.side r i) bb Gv Bd
    (hcoord _) hY0 he hf hpw hb0 hG0 hes hfs hlimb hsumB hrel
  have h0 : ∀ᵐ v ∂P', 0 ≤ invariantCondExp P' (evalAtZero (Sum.inl j : F.Index ⊕ (ℕ ⊕ (ℕ × ℕ)))) v :=
    condExp_nonneg hY0
  have hfin := hback (evalAtZero j) 0 Bd hcoordF (by
    filter_upwards [h0, hres] with v h1 h2
    exact ⟨h1, h2⟩)
  filter_upwards [hfin] with v hv
  exact hv.2
end Sizes2
section ModelParameters
private theorem eventually_and {P Q : ParameterAssignment → ResponseParameters → ℝ → Prop} (hP : EventuallyInParameters P)
    (hQ : EventuallyInParameters Q) : EventuallyInParameters fun Tb Kr y => P Tb Kr y ∧ Q Tb Kr y := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, hr₁, H₁⟩ := hP a ha
  obtain ⟨L₂, r₂, C₂, hr₂, H₂⟩ := hQ a ha
  refine ⟨max L₁ L₂, fun c => min (r₁ c) (r₂ c), max C₁ C₂, fun c => lt_min (hr₁ c) (hr₂ c),
    fun L hL hLL Tb hTa hTL hD hC hO hrt hCd => ?_⟩
  obtain ⟨M₁, G₁⟩ := H₁ L hL (le_of_max_le_left hLL) Tb hTa hTL hD hC hO (hrt.trans (min_le_left _ _))
    (le_of_max_le_left hCd)
  obtain ⟨M₂, G₂⟩ := H₂ L hL (le_of_max_le_right hLL) Tb hTa hTL hD hC hO (hrt.trans (min_le_right _ _))
    (le_of_max_le_right hCd)
  refine ⟨max M₁ M₂, fun Kr hM hη hN hF hRs => ?_⟩
  obtain ⟨y₁, F₁⟩ := G₁ Kr (le_of_max_le_left hM) hη hN hF hRs
  obtain ⟨y₂, F₂⟩ := G₂ Kr (le_of_max_le_right hM) hη hN hF hRs
  exact ⟨max y₁ y₂, fun y hy hR hW =>
    ⟨F₁ y (le_of_max_le_left hy) hR hW, F₂ y (le_of_max_le_right hy) hR hW⟩⟩
private theorem eventually_mono {P Q : ParameterAssignment → ResponseParameters → ℝ → Prop} (hP : EventuallyInParameters P)
    (h : ∀ Tb Kr y, P Tb Kr y → Q Tb Kr y) : EventuallyInParameters Q := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, h₁, hP⟩ := hP a ha
  refine ⟨L₁, r₁, C₁, h₁, fun L hL hLge Tb e1 e2 hD hC hO hr hCd => ?_⟩
  obtain ⟨M₁, hP⟩ := hP L hL hLge Tb e1 e2 hD hC hO hr hCd
  refine ⟨M₁, fun Kr h1 h2 h3 h4 h5 => ?_⟩
  obtain ⟨y₁, hP⟩ := hP Kr h1 h2 h3 h4 h5
  exact ⟨y₁, fun y hy hR hH => h _ _ _ (hP y hy hR hH)⟩
abbrev _root_.YangMills.SharedProofs.p60552 := @eventually_mono
private theorem floor_le_couplingFlow {ℓ : StepParameters} (hR : ExpansionReturnsAt ℓ)
    (hW : ∀ β : ℝ, ℓ.y₁ ≤ β → HasExpansion ℓ 0 β (wilsonWeight β)) (hB : 0 ≤ ℓ.B) {g β : ℝ} {K : ℕ}
    (hy : ℓ.y₁ ≤ (g ^ 2)⁻¹) (hβ : windowUpper ℓ g ≤ β)
    (hK : IsFirstCrossing ℓ (windowUpper ℓ g) β K) :
    ∀ j ≤ K, ℓ.y₁ ≤ (couplingFlow ℓ β j).1 := by apply _root_.YangMills.Construction.HullMeans.y₁_le_couplingFlow_of_le_crossing <;> assumption
private theorem eventually_base : EventuallyInParameters fun Tb Kr y => Tb.Admissible ∧
    (Tb.stepParameters y).Admissible ∧ 1 ≤ y ∧ 0 ≤ Kr.s₁ ∧
    ∀ (g β : ℝ) (K m : ℕ) (T : StageTower (Tb.stepParameters y)) (u n : ℕ) [NeZero n],
      HullChainAtLevel Tb y g β K m T u n → y ≤ stageCoupling T u := by
  intro a _
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, fun L _ _ Tb _ _ hD _ _ _ _ =>
    ⟨0, fun Kr _ _ _ hF _ => ⟨Tb.floorMin, fun y hyT hR hW => ?_⟩⟩⟩
  have hfit : (Tb.stepParameters y).Admissible := hD.fits y hyT
  have hy1 : 1 ≤ y := by
    have h1 : Tb.yC ≤ Tb.floorMin := le_max_left _ _
    linarith [hD.yC_ge]
  have hs : 0 ≤ Kr.s₁ := by
    have f := hF y
    have ha1 : (1 : ℝ) ≤ (Tb.stepParameters y).coupling := hD.a_ge
    have hC0 : 0 ≤ Kr.C₀ := by
      rw [f.C₀_eq]
      linarith [f.N₀_nonneg, f.Kc_ge]
    rw [f.s₁_eq]
    have : 0 ≤ 2 * ((Tb.stepParameters y).side : ℝ) ^ 4 * (Kr.C₀ + 2) := by positivity
    linarith
  refine ⟨hD, hfit, hy1, hs, fun g β K m T u n _ hlev => ?_⟩
  have hrun := hlev.chain
  have e : stageCoupling T u = (couplingFlow (Tb.stepParameters y) β u).1 :=
    hrun.follows u (by have := hlev.le; omega)
  rw [e]
  exact floor_le_couplingFlow hR hW (by have := hD.B_ge; show 0 ≤ Tb.B; linarith) hrun.le_inv_sq hrun.upper_le
    hrun.isFirst u hlev.le
end ModelParameters
theorem limitHullBounds (h₁ : severalLongHullClassesStatement) (h₂ : hullTranslationStatement)
    (h₃ : HullsInEveryVolume.localHullLocalityStatement) (h₄ : noiseRepresentationStatement)
    (h₅ : localHullSubsetStatement) (h₆ : localHullMomentBound) (h₇ : bandMomentSumStatement)
    (h₈ : largerToriStatement) (hMe : jointLimitPropertiesStatement) (hExt : jointLimitExtendStatement)
    (hEv : multipleTranslatesBoundStatement) (hBB : invariantCondExpBandBoundStatement)
    (hMC : separateCellsExpectationStatement) (hLaw : sampleBelowLawStatement) (hDraw : forgetLastStepStatement)
    (hSt : StageStatesMeasurableStatement) (hWh : chainMeasurabilityStatement)
    (hBo : HullsInEveryVolume.noiseChainMeasurableStatement) : limitHullBoundsStatement := by
  obtain ⟨CE, h₆⟩ := h₆
  have H := eventually_and h₁ (eventually_and h₂ (eventually_and h₃ (eventually_and h₄ (eventually_and h₅
    (eventually_and h₆ (eventually_and (h₇ (fun Tb => |CE Tb|) (fun _ => abs_nonneg _))
      (eventually_and h₈ eventually_base)))))))
  refine eventually_mono H ?_
  rintro Tb Kr y ⟨p₁, p₂, p₃, p₄, p₅, p₆, p₇, p₈, hDr, hfit, hy1, hs, hcg⟩ g hg hgy k _ h2 h8 R d hd
  have hF : LimitHullInputs ⟨Tb, Kr, y, g, k, R, d⟩ CE :=
    { drawn := hDr
      fit := hfit
      g_pos := hg
      floor := hgy
      one_le := hy1
      s_nonneg := hs
      coupling_ge := hcg
      classes := p₁
      moves := p₂
      reach := p₃
      carries := p₄
      lies := p₅
      moment := p₆
      rates := p₇ g }
  obtain ⟨C, hC1, hCr⟩ := hF.rates
  have hKp := p₈ g hg hgy k h2 h8 R d hd
  refine ⟨C, hC1, fun S F u z hu => ?_⟩
  have hKeep : (translatedTori F.points F.period).IsPreserving :=
    ((hKp S).2.2.2 F.rule F.exponents F.points F.period F.rule_admissible F.one_le_period F.strictMono_exponents
      F.points_eq).1
  refine ⟨fun D j hD hgj => condMean_largeHull_le hF hLaw hDraw hSt hMe F hKeep j hu z D hD hgj, fun k' j hk hgj => ?_⟩
  exact condMean_hullSizePower_le hF hLaw hDraw hSt hWh hBo hMC hMe hEv hExt hBB hCr F hKeep j hu z k' hk hgj
end YangMills.Construction.MomentLaw
end
