import YangMills.Construction.Towers.PlaneWaveCoefficientsOnTheBondsProof
import YangMills.Construction.Towers.TheBackgroundFieldAsASumOfWaves
import YangMills.Construction.Towers.TheBackgroundNumbersOnTheRealPolydisc
import YangMills.Construction.Towers.TheFreePropagatorsAndTheirRootsProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.MassiveOpFunctions.WaveExpansion
open PeriodicOperators
open Scaling
open FullSpace.BackgroundJets
open PlaneWaves (edgeAt)
open PlaneWaveCalculus (expWave)
theorem pauliCoords_unique {c d : Fin 3 → ℂ}
    (h : ∑ a, c a • Matrices.ComplexMatrix2.pauliFamily a =
      ∑ a, d a • Matrices.ComplexMatrix2.pauliFamily a) : c = d := by apply _root_.YangMills.Construction.Tower.PeriodicMultiplierMatrices.pauliFamily_sum_injective <;> assumption
variable {L k : ℕ}
theorem exists_eq_edgeAt (e : PeriodicOperators.PosEdge L k 0) :
    ∃ (x : FullSpace.Vertex L k 0) (ρ : Fin 4), e = edgeAt L k x ρ := by apply _root_.YangMills.Construction.Tower.FreeResolvents.edgeCover <;> assumption
theorem axisStep_injective (hL : Conventions.IsAdmissibleBlockingFactor L) {μ ν : Fin 4}
    (h : InfiniteLattice.axisStep (meshAt L k 0) μ = InfiniteLattice.axisStep (meshAt L k 0) ν) :
    μ = ν := by apply _root_.YangMills.Construction.Tower.EdgeWaves.axisStep_injective <;> assumption
theorem thirdColourWave_apply (hL : Conventions.IsAdmissibleBlockingFactor L)
    (q : InfiniteLattice.AmbientSpace) (ρ σ : Fin 4) (a : Fin 3) (x : FullSpace.Vertex L k 0) :
    thirdColourWave L k q ρ (a, edgeAt L k x σ) =
      if a = 2 ∧ ρ = σ then expWave (toComplexVec q) x else 0 := by
  have hstep : (edgeAt L k x σ).1.terminal - (edgeAt L k x σ).1.initial =
      InfiniteLattice.axisStep (meshAt L k 0) ρ ↔ ρ = σ := by
    have e : (edgeAt L k x σ).1.terminal - (edgeAt L k x σ).1.initial =
        InfiniteLattice.axisStep (meshAt L k 0) σ := by
      show x + _ - x = _
      abel
    rw [e]
    exact ⟨fun h => (axisStep_injective (k := k) hL h).symm, fun h => by rw [h]⟩
  unfold thirdColourWave
  by_cases h : a = 2 ∧ ρ = σ
  · rw [if_pos ⟨h.1, hstep.2 h.2⟩, if_pos h]
    rfl
  · rw [if_neg (fun h' => h ⟨h'.1, hstep.1 h'.2⟩), if_neg h]
theorem toComplexVec_shiftedMomentum (p : InfiniteLattice.AmbientSpace) (m : Fin 4 → ℤ) :
    toComplexVec (shiftedMomentum p m) = PlaneWaves.shiftedFreq (toComplexVec p) m := by
  funext μ
  simp [toComplexVec, shiftedMomentum, PlaneWaves.shiftedFreq]
theorem backgroundFieldWaveSum_holds (hCalc : PlaneWaveCalculus.PlaneWaveCalculusHolds)
    (hPoly : BackgroundCoeffsOnRealPolydisc.Claim) : BackgroundFieldWaveSum := by
  intro L hL k hk p hp μ ι
  obtain ⟨a, e⟩ := ι
  obtain ⟨x, σ, rfl⟩ := exists_eq_edgeAt e
  have hC : PlaneWaveCalculus.EdgeCoeffFacts L k := (hCalc L hL k hk).2.2.1
  have hw := hC.exp_expansion (toComplexVec p) (responseAmplitude L k (toComplexVec p) μ) σ x
  have hnum := (hPoly L hL k hk).1 p hp μ σ
  set S : ℂ := ∑ m ∈ PlaneWaves.freqBox L k,
    expWave (PlaneWaves.shiftedFreq (toComplexVec p) m) x *
      backgroundCoeff L k (toComplexVec p) μ σ m with hS
  have hsum : ∑ m ∈ PlaneWaves.freqBox L k,
      expWave (PlaneWaves.shiftedFreq (toComplexVec p) m) x •
        PlaneWaves.edgeFourierCoeff L k (responseAmplitude L k (toComplexVec p) μ) σ m =
      S • Matrices.ComplexMatrix2.pauliFamily 2 := by
    rw [hS, Finset.sum_smul]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [hnum m hm, smul_smul]
  have hcoord : (fun a' : Fin 3 => expWave (toComplexVec p) x *
        responseAmplitude L k (toComplexVec p) μ
          ((colourEdges L k 0).mkQuot 1 (a', edgeAt L k x σ))) =
      fun a' => if a' = 2 then S else 0 := by
    apply pauliCoords_unique
    have hl : expWave (toComplexVec p) x • PlaneWaves.edgeFieldOfClasses L k
          (responseAmplitude L k (toComplexVec p) μ) (edgeAt L k x σ) =
        ∑ a' : Fin 3, (expWave (toComplexVec p) x *
          responseAmplitude L k (toComplexVec p) μ
            ((colourEdges L k 0).mkQuot 1 (a', edgeAt L k x σ))) •
            Matrices.ComplexMatrix2.pauliFamily a' := by
      show expWave (toComplexVec p) x • ∑ a' : Fin 3, responseAmplitude L k (toComplexVec p) μ
        ((colourEdges L k 0).mkQuot 1 (a', edgeAt L k x σ)) •
          Matrices.ComplexMatrix2.pauliFamily a' = _
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun a' _ => smul_smul _ _ _
    rw [← hl, hw, hsum]
    simp [ite_smul]
  have ha : expWave (toComplexVec p) x * responseAmplitude L k (toComplexVec p) μ
      ((colourEdges L k 0).mkQuot 1 (a, edgeAt L k x σ)) = if a = 2 then S else 0 :=
    congrFun hcoord a
  have hleft : blochWave (colourEdges L k 0) (toComplexVec p)
        (scaledResponseField L k (toComplexVec p) μ) (a, edgeAt L k x σ) =
      ((finestMesh L k : ℝ) : ℂ) * (expWave (toComplexVec p) x *
        responseAmplitude L k (toComplexVec p) μ
          ((colourEdges L k 0).mkQuot 1 (a, edgeAt L k x σ))) := by
    show expWave (toComplexVec p) x * (((finestMesh L k : ℝ) : ℂ) *
        responseAmplitude L k (toComplexVec p) μ
          ((colourEdges L k 0).mkQuot 1 (a, edgeAt L k x σ))) = _
    ring
  rw [hleft, ha]
  congr 1
  simp only [thirdColourWave_apply hL]
  by_cases h2 : a = 2
  · rw [if_pos h2, hS]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_eq_single σ]
    · rw [if_pos ⟨h2, rfl⟩, toComplexVec_shiftedMomentum, mul_comm]
    · intro ρ _ hρ
      rw [if_neg fun h => hρ h.2, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ σ) h
  · rw [if_neg h2]
    symm
    refine Finset.sum_eq_zero fun m _ => Finset.sum_eq_zero fun ρ _ => ?_
    rw [if_neg fun h => h2 h.1, mul_zero]
end YangMills.Construction.Tower.MassiveOpFunctions.WaveExpansion
end
