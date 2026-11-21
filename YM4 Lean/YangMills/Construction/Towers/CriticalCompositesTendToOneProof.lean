import YangMills.Construction.Towers.CompositesOfTheLiftsAndLayersOfSitesProof
import YangMills.Construction.Towers.CriticalCompositesTendToOne
import YangMills.Construction.Towers.RealAnalyticMapsAlongPaths
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology
open YangMills.Construction.Matrices (ComplexMatrix2)
noncomputable section
namespace YangMills.Construction.Tower
namespace ProlongCompTendsto
variable {L n k i : ℕ}
theorem eventually_mem_of_isOpenNhdOfOne {𝒰 : Set (Edge L n k i → ComplexMatrix2)}
    (h : IsOpenNhdOfOne 𝒰) :
    ∀ᶠ V in 𝓝[fieldSpace L n k i] trivialField L n k i, V ∈ 𝒰 := by apply _root_.YangMills.Construction.Tower.ProlongCompositesProof.eventually_mem_of_isOpenNhdOfOne <;> assumption
theorem tendsto_prolong (hR : AnalyticMapsAlongCurves)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {b : CriticalBranchData L n k}
    (hb : b.IsCritical) (hi : i < k) :
    Tendsto (b.prolong i) (𝓝[fieldSpace L n k (i + 1)] trivialField L n k (i + 1))
      (𝓝[fieldSpace L n k i] trivialField L n k i) := by
  obtain ⟨𝒰, hU, hA⟩ := hb.analytic_prolong i hi
  have hnear := eventually_mem_of_isOpenNhdOfOne hU
  have hc := (hR L n k (i + 1) i hL hn hi hi.le).1 𝒰 _ hA |>.1 _ hU.2
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, hnear.mono fun W hW => hA.2.1 hW⟩
  have h := hc.tendsto.mono_left (nhdsWithin_le_of_mem (Filter.mem_of_superset hnear fun _ h => h))
  rwa [hb.prolong_trivial i hi] at h
end ProlongCompTendsto
open ProlongCompTendsto in
theorem chosenProlongCompTendsto_holds (hB : CriticalBranchExists)
    (hR : AnalyticMapsAlongCurves) : ChosenProlongCompTendsto := by
  intro L n k j hL hn hj
  have hb : (chosenCriticalBranch L n k).IsCritical := Classical.epsilon_spec (hB L n k hL hn)
  induction j with
  | zero => exact tendsto_id
  | succ i ih =>
    exact (ih (by omega)).comp (tendsto_prolong hR hL hn hb (by omega))
end YangMills.Construction.Tower
end
