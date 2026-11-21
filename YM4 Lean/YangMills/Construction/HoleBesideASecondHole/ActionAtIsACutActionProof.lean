import YangMills.Construction.ClusterExpansionOfAStep.ChainOnATorus
import YangMills.Construction.HoleBesideASecondHole.ActionAtIsACutAction
import YangMills.Construction.HoleBesideASecondHole.CarriedSitesAndPaths
import YangMills.Construction.HoleBesideASecondHole.CellsPutBackProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages TorusFields LumpContours FrameTransfer
namespace LumpContours
namespace CutActionLevels
variable {F F' : BlockFrame}
theorem centredCube_one : centredCube 1 = {0} := by apply _root_.YangMills.Construction.TorusChain.centredCube_one <;> assumption
theorem sitesOfCells_top (S : Finset F.Cell) : sitesOfCells S F.top = S := by apply _root_.YangMills.Construction.Reinsertion.sitesOfCells_top <;> assumption
theorem sitesBelow_self {j : ℕ} (x : F.Site j) : sitesBelow j x = {x} := by
  simp only [sitesBelow, Nat.sub_self, pow_zero, centredCube_one, Finset.image_singleton, Finset.singleton_inj]
  funext k
  simp [siteOfCoords, siteCoords]
theorem cutBelow_self {j : ℕ} (X : Finset (F.Site j)) : cutBelow j X = X := by
  ext x
  simp [cutBelow, sitesBelow_self]
theorem plaquetteEnergy_transfer (h : ∀ i, F.period 0 i = F'.period 0 i) (U : F.GaugeField 0)
    (p : F.Site 0 × Fin 4 × Fin 4) :
    LumpContours.plaquetteEnergy (transferField F' 0 U) (transferSite F' 0 p.1, p.2) =
      LumpContours.plaquetteEnergy U p := by
  unfold LumpContours.plaquetteEnergy
  rw [plaquetteHolonomy_transfer h]
theorem cutChainEnergy_transfer {j : ℕ} (hL : F.blockSide = F'.blockSide)
    (hp : ∀ i, i ≤ j → ∀ k, F.period i k = F'.period i k) (a : ℝ)
    (X : Finset (F.Site j)) (U : F.FieldChain) :
    cutChainEnergy a j (transferSet F' j X) (fun i => transferField F' i (U i)) = cutChainEnergy a j X U := by
  have h0 := hp 0 (Nat.zero_le j)
  have hj := hp j le_rfl
  unfold cutChainEnergy
  rw [cutBelow_transferSet hL h0 hj rfl, cutPlaquettes_transferSet h0, Finset.sum_image]
  · congr 1
    · exact Finset.sum_congr rfl fun p _ => plaquetteEnergy_transfer h0 (U 0) p
    · congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      have hij : i + 1 ≤ j := Finset.mem_range.1 hi
      have h1 := hp (i + 1) hij
      have h2 := hp i (by omega)
      rw [cutBelow_transferSet hL h1 hj rfl, cutBonds_transferSet h1,
        Finset.sum_image (transferBond_injective h1).injOn]
      exact Finset.sum_congr rfl fun c _ => blockFit_transfer hL h2 h1 (U i) (U (i + 1)) c
  · intro p _ q _ e
    have e1 := transferSite_injective h0 (Prod.ext_iff.1 e).1
    exact Prod.ext e1 (Prod.ext_iff.1 e).2
theorem cutEffectiveAction_transfer {j : ℕ} (hL : F.blockSide = F'.blockSide)
    (hp : ∀ i, i ≤ j → ∀ k, F.period i k = F'.period i k) (a : ℝ)
    (X : Finset (F.Site j)) (V : F.GaugeField j) :
    cutEffectiveAction a j (transferSet F' j X) (transferField F' j V) = cutEffectiveAction a j X V := by
  have hj := hp j le_rfl
  have hp' : ∀ i, i ≤ j → ∀ k, F'.period i k = F.period i k := fun i hi k => (hp i hi k).symm
  unfold cutEffectiveAction
  apply congrArg sInf
  ext r
  simp only [Set.mem_range, Subtype.exists]
  constructor
  · rintro ⟨U', hU', rfl⟩
    refine ⟨fun i => transferField F i (U' i), ?_, ?_⟩
    · simp only [hU']
      exact transferField_transferField hj V
    · have := cutChainEnergy_transfer hL.symm hp' a (transferSet F' j X) U'
      rwa [transferSet_transferSet hj] at this
  · rintro ⟨U, hU, rfl⟩
    exact ⟨fun i => transferField F' i (U i), by simp only [hU], cutChainEnergy_transfer hL hp a X U⟩
theorem cutEffectiveAction_zero (a : ℝ) (X : Finset (F.Site 0)) (V : F.GaugeField 0) :
    cutEffectiveAction a 0 X V = ∑ p ∈ cutPlaquettes X, LumpContours.plaquetteEnergy V p := by
  have hne : Nonempty {U : F.FieldChain // U 0 = V} :=
    ⟨⟨Function.update (fun _ _ _ => 1) 0 V, by simp⟩⟩
  have hc : ∀ U : {U : F.FieldChain // U 0 = V},
      cutChainEnergy a 0 X U.1 = ∑ p ∈ cutPlaquettes X, LumpContours.plaquetteEnergy V p := by
    rintro ⟨U, rfl⟩
    simp [cutChainEnergy, cutBelow_self]
  unfold cutEffectiveAction
  simp only [hc]
  exact ciInf_const
theorem sum_cutPlaquettes_eq_wilsonAction {m : ℕ} [NeZero m] (hm : ∀ k, F.period 0 k = m)
    (X : Finset (TorusSite m)) (W : TorusField m) :
    ∑ p ∈ cutPlaquettes (sitesOfTorus F 0 X), LumpContours.plaquetteEnergy (readAtLevel F 0 W) p =
      TorusFields.wilsonAction X W := by
  unfold YangMills.Construction.TorusFields.wilsonAction
  symm
  refine Finset.sum_nbij' (fun p => (torusToFrame F 0 p.1, p.2)) (fun q => (frameToTorus m q.1, q.2))
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨x, μ, ν⟩ hp
    exact (torusToFrame_mem_cutPlaquettes hm X x μ ν).2 hp
  · rintro ⟨y, μ, ν⟩ hq
    apply (torusToFrame_mem_cutPlaquettes hm X _ μ ν).1
    simpa only [torusToFrame_frameToTorus hm] using hq
  · rintro ⟨x, μ, ν⟩ _
    simp only [frameToTorus_torusToFrame hm]
  · rintro ⟨y, μ, ν⟩ _
    simp only [torusToFrame_frameToTorus hm]
  · rintro ⟨x, μ, ν⟩ _
    simp only [LumpContours.plaquetteEnergy, YangMills.Construction.TorusFields.plaquetteEnergy]
    rw [plaquetteHolonomy_readAtLevel hm]
end CutActionLevels
open CutActionLevels in
theorem actionAtLevelIsCutAction (h : CutActionEqualsMinimalAction) : ActionAtLevelIsCutAction := by
  intro a ha L _ hodd n _ F hFL hside
  obtain ⟨L', t, side⟩ := F
  obtain rfl : L' = L := hFL
  obtain rfl : side = fun _ => n := funext hside
  have hT : (⟨L', t, fun _ => n⟩ : BlockFrame) = torusFrame L' t n := rfl
  rw [hT]
  constructor
  · intro S V
    have := (h (torusFrame L' t n) a ha).2 hodd (cellsOfSites (torusFrame L' t n) S) (torusFrame L' t n).top
      le_rfl (readAtLevel (torusFrame L' t n) (torusFrame L' t n).top V)
    rw [sitesOfCells_top] at this
    exact this
  · intro X W
    cases t with
    | zero =>
      have hm : ∀ k, (torusFrame L' 0 n).period 0 k = n * L' := by
        intro k
        simp [BlockFrame.period, torusFrame, BlockFrame.top]
      exact (cutEffectiveAction_zero (F := torusFrame L' 0 n) a (sitesOfTorus (torusFrame L' 0 n) 0 X)
        (readAtLevel (torusFrame L' 0 n) 0 W)).trans (sum_cutPlaquettes_eq_wilsonAction hm X W)
    | succ t =>
      have hp : ∀ i, i ≤ t + 1 → ∀ k,
          (torusFrame L' t (n * L')).period i k = (torusFrame L' (t + 1) n).period i k := by
        intro i hi k
        simp only [BlockFrame.period, torusFrame, BlockFrame.top]
        have : t + 1 + 1 - i = (t + 1 - i) + 1 := by omega
        rw [this, pow_succ]
        ring
      have hsite : sitesOfTorus (torusFrame L' (t + 1) n) (t + 1) X =
          transferSet (torusFrame L' (t + 1) n) (t + 1) (cellsOfSites (torusFrame L' t (n * L')) X) := by
        unfold transferSet cellsOfSites sitesOfTorus
        rw [Finset.image_image]
        refine Finset.image_congr fun x _ => ?_
        exact (transferSite_siteOfCoords (hp (t + 1) le_rfl) _).symm
      have hfield : readAtLevel (torusFrame L' (t + 1) n) (t + 1) W =
          transferField (torusFrame L' (t + 1) n) (t + 1) (readAtLevel (torusFrame L' t (n * L')) (t + 1) W) :=
        (transferField_readAtLevel (hp (t + 1) le_rfl) W).symm
      have htop := (h (torusFrame L' t (n * L')) a ha).2 hodd (cellsOfSites (torusFrame L' t (n * L')) X)
        (torusFrame L' t (n * L')).top le_rfl
        (readAtLevel (torusFrame L' t (n * L')) (torusFrame L' t (n * L')).top W)
      rw [sitesOfCells_top] at htop
      show cutEffectiveAction a (t + 1) (sitesOfTorus (torusFrame L' (t + 1) n) (t + 1) X)
        (readAtLevel (torusFrame L' (t + 1) n) (t + 1) W) = _
      rw [hsite, hfield]
      exact (cutEffectiveAction_transfer (F := torusFrame L' t (n * L')) (F' := torusFrame L' (t + 1) n)
        (j := t + 1) rfl hp a (cellsOfSites (torusFrame L' t (n * L')) X)
        (readAtLevel (torusFrame L' t (n * L')) (t + 1) W)).trans htop
end LumpContours
end YangMills.Construction
end
