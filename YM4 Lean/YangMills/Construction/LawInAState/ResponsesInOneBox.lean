import YangMills.Construction.LawInAState.DataOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.BoxResponses
open StateLaws
def periodizeUnitTorus (f : InfiniteLattice.AmbientSpace → ℝ) (x : InfiniteLattice.AmbientSpace) : ℝ :=
  ∑ᶠ z : Fin 4 → ℤ, f (fun i => x i + 2 * (z i : ℝ))
def boxSide (L K k : ℕ) : ℕ := 2 * L ^ (K - k)
instance boxSide_neZero (L K k : ℕ) [NeZero L] : NeZero (boxSide L K k) :=
  ⟨mul_ne_zero two_ne_zero (pow_ne_zero _ (NeZero.ne L))⟩
def unitTorusWeight (L K k : ℕ) (f : InfiniteLattice.AmbientSpace → ℝ) :
    WeightedResponses.PlaquetteWeight (WeightedResponses.fineSide L k (boxSide L K k)) := fun p =>
  periodizeUnitTorus f fun i => ((WeightedResponses.doubledBarycentre p i).val : ℝ) / (2 * (L : ℝ) ^ K)
variable {ℓ : TorusLumps.StepParameters}
def stageLaw (T : WeightedResponses.StageTower ℓ) (β : ℝ) (K k : ℕ) :
    Measure (WeightedResponses.MarkedSample ℓ k (boxSide ℓ.side K k)) :=
  WeightedResponses.markedSampleLaw T β k (boxSide ℓ.side K k)
def boxResponse (T : WeightedResponses.StageTower ℓ) (β : ℝ) (al : ℕ → ℝ) (K k : ℕ)
    (f : InfiniteLattice.AmbientSpace → ℝ)
    (u : WeightedResponses.MarkedSample ℓ k (boxSide ℓ.side K k)) : ℝ :=
  WeightedResponses.response T β al k (boxSide ℓ.side K k) (unitTorusWeight ℓ.side K k f) u
def centeredBoxResponse (T : WeightedResponses.StageTower ℓ) (β : ℝ) (al : ℕ → ℝ) (K k : ℕ)
    (f : InfiniteLattice.AmbientSpace → ℝ)
    (u : WeightedResponses.MarkedSample ℓ k (boxSide ℓ.side K k)) : ℝ :=
  boxResponse T β al K k f u - ∫ u', boxResponse T β al K k f u' ∂stageLaw T β K k
def shiftAveragedProduct (T : WeightedResponses.StageTower ℓ) (β : ℝ) (al : ℕ → ℝ) (K k m : ℕ)
    (f h : (Fin 4 → ℤ) → InfiniteLattice.AmbientSpace → ℝ)
    (u : WeightedResponses.MarkedSample ℓ k (boxSide ℓ.side K k)) : ℝ :=
  ((shiftSet m).card : ℝ)⁻¹ *
    ∑ v ∈ shiftSet m, centeredBoxResponse T β al K k (f v) u * centeredBoxResponse T β al K k (h v) u
def shiftAveragedResponse (T : WeightedResponses.StageTower ℓ) (β : ℝ) (al : ℕ → ℝ) (K k m : ℕ)
    (f : (Fin 4 → ℤ) → InfiniteLattice.AmbientSpace → ℝ)
    (u : WeightedResponses.MarkedSample ℓ k (boxSide ℓ.side K k)) : ℝ :=
  ((shiftSet m).card : ℝ)⁻¹ * ∑ v ∈ shiftSet m, centeredBoxResponse T β al K k (f v) u
structure IsStateChain (Tb : RenormalizationStepParameters.ParameterAssignment) (y : ℝ) (Kr : WeightedResponses.ResponseParameters)
    (Xi d : ℝ) (K : ℕ) (β : ℝ) (al : ℕ → ℝ) (T : WeightedResponses.StageTower (Tb.stepParameters y)) : Prop where
  isFlowDatum : IsFlowDatum (Tb.stepParameters y) Xi K β
  minimalCutoff_le : minimalCutoff (Tb.stepParameters y) Xi d ≤ K
  isCoeff : ResponseInTheExpansion.IsChainResponseCoeff (Tb.stepParameters y) Kr β
    (separationLevel (Tb.stepParameters y) β K d) al
  onFamily : ResponseInTheExpansion.IsTowerAtParameters Tb y T β (K - 1)
  isCutoff_bottom : ColdStepAtMirrorFrames.IsCutoff ((Tb.stepParameters y).threshold / 64) T.base.barrierFn
  marksMeasurable : T.MarksMeasurable
  scored : ∃ S : FreeEnergies.ScoredStageTower T, S.params = Kr ∧ S.FollowsFlow β (K - 1) ∧ S.coeffs = al
def markError (ℓ : TorusLumps.StepParameters) (C x : ℝ) : ℝ :=
  x ^ C * Real.exp (-(4 * ℓ.rt * (TorusLumps.clusterRange x : ℝ)))
end YangMills.Construction.BoxResponses
end
