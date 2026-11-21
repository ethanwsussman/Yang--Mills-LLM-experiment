import YangMills.Construction.ClusterExpansionOfAStep.SharesAddToTheAction
import YangMills.Construction.ClusterExpansionOfAStep.TopFieldOffTheHull
import YangMills.Construction.ClusterExpansionOfAStep.TopFrameOfATorus
import YangMills.Construction.FreeEnergiesOfTheFlow.ActionOfAColdField
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdFieldAction
open TorusFields StepCosts BlockAverages TopLevelSites TorusFrame RenormalizationStepParameters
theorem coldActionBound_of_sharesSumToAction (hShares : SharesSumToAction) : ColdActionBound := by
  intro T hT
  obtain ⟨-, -, -, -, -, -, -, hN, hchain⟩ := hT.chain
  have hN0 := hN 0
  refine ⟨T.N 0 + 8, by positivity, ?_⟩
  intro t n _ hn s U hs hsσ hcold
  have hn4 : 4096 ≤ n := hT.n₀_ge.trans hn
  have hcard : (Fintype.card (TorusSite n) : ℝ) = (n : ℝ) ^ 4 := by
    simp [TorusSite, ZMod.card]
  have hs2 : 0 ≤ s ^ 2 := by positivity
  cases t with
  | zero =>
    show wilsonAction Finset.univ U ≤ _
    have hplaq : ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
        plaquetteEnergy U p.1 p.2.1 p.2.2 ≤ s ^ 2 / 2 := by
      intro p hp
      have hlt : p.2.1 < p.2.2 := (Finset.mem_filter.mp hp).2.1
      have hc := hcold p.1 p.2.1 p.2.2 hlt
      rw [plaquetteEnergy_eq_curvature_sq]
      have h0 : 0 ≤ curvature U p.1 p.2.1 p.2.2 := norm_nonneg _
      nlinarith
    have hcount : ((plaquettesIn (Finset.univ : Finset (TorusSite n))).card : ℝ) ≤ 16 * (n : ℝ) ^ 4 := by
      have h1 : (plaquettesIn (Finset.univ : Finset (TorusSite n))).card ≤ Fintype.card (TorusPlaquette n) :=
        Finset.card_le_univ _
      have h2 : Fintype.card (TorusPlaquette n) = Fintype.card (TorusSite n) * 16 := by
        simp [TorusPlaquette]
      have h3 : ((plaquettesIn (Finset.univ : Finset (TorusSite n))).card : ℝ) ≤
          (Fintype.card (TorusPlaquette n) : ℝ) := by
        exact_mod_cast h1
      rw [h2] at h3
      push_cast at h3
      rw [hcard] at h3
      linarith
    calc wilsonAction Finset.univ U ≤ ∑ _p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)), s ^ 2 / 2 :=
          Finset.sum_le_sum hplaq
      _ = ((plaquettesIn (Finset.univ : Finset (TorusSite n))).card : ℝ) * (s ^ 2 / 2) := by simp
      _ ≤ 16 * (n : ℝ) ^ 4 * (s ^ 2 / 2) := by gcongr
      _ = 8 * s ^ 2 * (n : ℝ) ^ 4 := by ring
      _ ≤ (T.N 0 + 8) * s ^ 2 * (n : ℝ) ^ 4 := by
        have : 0 ≤ T.N 0 * s ^ 2 * (n : ℝ) ^ 4 := by positivity
        nlinarith
  | succ t =>
    have hext : ∀ i, (torusFrame T.side t n).extent i = n := fun _ => rfl
    have hamb : IsAdmissibleAmbient (torusFrame T.side t n) := isAdmissibleAmbient_torusFrame (by omega)
    have hreg : IsOrthantRegular (cellsOfSites (torusFrame T.side t n) (Finset.univ : Finset (TorusSite n))) 2047 := by
      rw [cellsOfSites_univ hext]
      exact isOrthantRegular_finiteCells (fun i => by
        show 0 < n
        omega) _
    have hcoldFrame : IsCold (cellsOfSites (torusFrame T.side t n) (Finset.univ : Finset (TorusSite n)))
        (torusFrame T.side t n).top s
        (readAtLevel (torusFrame T.side t n) (torusFrame T.side t n).top U) := by
      rw [cellsOfSites_univ hext]
      exact isCold_readAtLevel hext hcold
    have hle : s ≤ T.σA := by
      have := hT.σ_le
      have := hT.σ_pos
      linarith
    have hall := hchain (torusFrame T.side t n) 2047 _ rfl hamb (by norm_num) hreg s _ hs hle hcoldFrame
    have hbound := hall.2.2.1.2.2.2.2.2.2.2.1
    have hsum := hShares T.coupling T.side t n Finset.univ U (by linarith [hT.a_ge])
      (Nat.pos_of_ne_zero (NeZero.ne _)) (by omega)
    rw [← hsum]
    have hsite : ∀ y ∈ (Finset.univ : Finset (TorusSite n)),
        levelShare T.coupling T.side (t + 1) Finset.univ y U ≤ T.N 0 * s ^ 2 := fun y _ =>
      (hbound (torusSiteInFrame (torusFrame T.side t n) (torusFrame T.side t n).top y)).2
    calc ∑ y : TorusSite n, levelShare T.coupling T.side (t + 1) Finset.univ y U ≤
          ∑ _y : TorusSite n, T.N 0 * s ^ 2 :=
          Finset.sum_le_sum hsite
      _ = (Fintype.card (TorusSite n) : ℝ) * (T.N 0 * s ^ 2) := by simp
      _ = T.N 0 * s ^ 2 * (n : ℝ) ^ 4 := by rw [hcard]; ring
      _ ≤ (T.N 0 + 8) * s ^ 2 * (n : ℝ) ^ 4 := by
        have : 0 ≤ s ^ 2 * (n : ℝ) ^ 4 := by positivity
        nlinarith
end YangMills.Construction.ColdFieldAction
end
