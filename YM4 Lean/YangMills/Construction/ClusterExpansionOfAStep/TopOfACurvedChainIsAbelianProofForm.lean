import YangMills.Construction.ClusterExpansionOfAStep.SitesOfTheTopOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.TopOfACurvedChainIsAbelian
import YangMills.Construction.ColdStepAtMirrorFrames.BareActionIsCriticalAtAnAbelianFieldProof
import YangMills.Construction.ColdStepAtMirrorFrames.CurvedChainIsAbelian
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep.ConstantCurvatureTop
open BlockAverages ColdStepAtMirrorFrames TorusFields
theorem expUnit_add_smul (X : imaginaryQuaternions) (s t : ℝ) :
    expUnit ((s + t) • X) = expUnit (s • X) * expUnit (t • X) := by apply _root_.YangMills.SharedProofs.p2328 <;> assumption
theorem inv_expUnit_smul (X : imaginaryQuaternions) (s : ℝ) : (expUnit (s • X))⁻¹ = expUnit ((-s) • X) := by apply _root_.YangMills.SharedProofs.p4359 <;> assumption
theorem expUnit_plaquette_smul (X : imaginaryQuaternions) (p q r s : ℝ) :
    expUnit (p • X) * expUnit (q • X) * (expUnit (r • X))⁻¹ * (expUnit (s • X))⁻¹ =
      expUnit ((p + q - r - s) • X) := by
  rw [inv_expUnit_smul, inv_expUnit_smul, ← expUnit_add_smul, ← expUnit_add_smul, ← expUnit_add_smul]
  congr 2
theorem linearFluxAngle_circulation (g : ℝ) (μ ν : Fin 4) (hμν : μ < ν) (φ : (Fin 4 → ℤ) → ℝ)
    (z : Fin 4 → ℤ) (i j : Fin 4) (hij : i < j) :
    linearFluxAngle g μ ν φ z i + linearFluxAngle g μ ν φ (z + Pi.single i 1) j -
        linearFluxAngle g μ ν φ (z + Pi.single j 1) i - linearFluxAngle g μ ν φ z j =
      g * PlaneFields.planeForm μ ν i j := by
  have hcomm : z + Pi.single j 1 + Pi.single i 1 = z + Pi.single i 1 + Pi.single j 1 := by abel
  simp only [linearFluxAngle, hcomm]
  have hne : i ≠ j := hij.ne
  by_cases hj : j = ν
  · subst hj
    have hi' : i ≠ j := hne
    by_cases hi : i = μ
    · subst hi
      simp [hi', PlaneFields.planeForm]
      try ring
    · have h1 : μ ≠ i := fun h => hi h.symm
      have h2 : ¬ (i = j ∧ j = μ) := fun h => hne h.1
      simp [hi', PlaneFields.planeForm, hi, h1]
      try ring
  · by_cases hi : i = ν
    · subst hi
      have h3 : μ ≠ j := by
        intro h
        subst h
        exact absurd (hμν.trans hij) (lt_irrefl _)
      have h4 : ¬ (j = μ) := fun h => h3 h.symm
      simp [hj, PlaneFields.planeForm, h3, h4]
      try ring
    · simp [hj, hi, PlaneFields.planeForm]
      try ring
theorem intCast_zmodCast_of_eq {m n : ℕ} [NeZero n] (h : m = n) (z : ℤ) :
    (((((z : ZMod n)).cast : ℤ)) : ZMod m) = (z : ZMod m) := by
  subst h
  simp
theorem topOfConstantCurvatureChainIsAbelian_holds (h : ConstantCurvatureChainAbelian) :
    TorusLumps.TopOfConstantCurvatureChainIsAbelian := by
  intro L hL
  refine ⟨1, one_pos, fun F X μ ν n l hFL hs hn hX hμν hγ => ?_⟩
  have : NeZero n := ⟨by omega⟩
  have hodd : Odd F.blockSide := hFL ▸ hL
  obtain ⟨⟨φ, hφ⟩, -⟩ := h F X μ ν n l hodd hs (by omega) hX hμν hγ F.top le_rfl
  have hper : ∀ i, F.period F.top i = n := fun i => (TopLevelSites.period_top i).trans (hs i)
  have hg : levelFlux F μ l F.top = 2 * Real.pi * l / (n : ℝ) ^ 2 := by
    simp [levelFlux, hper]
  rw [hg] at hφ
  set g : ℝ := 2 * Real.pi * l / (n : ℝ) ^ 2 with hgdef
  have key : ∀ (z : Fin 4 → ℤ) (i : Fin 4),
      restrictToTorus n (constantCurvatureChain F X μ ν l F.top) (siteOfInt z) i =
        expUnit (linearFluxAngle g μ ν φ z i • X) := by
    intro z i
    have e : (siteOfCoords F.top fun k => (((siteOfInt z : TorusSite n) k).cast : ℤ) : F.Cell) =
        siteOfCoords F.top z := by
      funext k
      exact intCast_zmodCast_of_eq (hper k) (z k)
    show constantCurvatureChain F X μ ν l F.top
      (siteOfCoords F.top fun k => (((siteOfInt z : TorusSite n) k).cast : ℤ)) i = _
    rw [e]
    exact hφ z i
  have hlift : ∀ x : TorusSite n, ∃ z : Fin 4 → ℤ, x = siteOfInt z := by
    intro x
    refine ⟨fun k => ((x k).cast : ℤ), ?_⟩
    funext k
    simp [siteOfInt]
  have hstep : ∀ (z : Fin 4 → ℤ) (i : Fin 4),
      (siteOfInt z : TorusSite n) + TorusFields.unitStep n i = siteOfInt (z + Pi.single i 1) := by
    intro z i
    funext k
    by_cases hk : k = i
    · subst hk
      simp [siteOfInt, TorusFields.unitStep]
    · simp [siteOfInt, TorusFields.unitStep, hk]
  refine ⟨⟨fun x i => linearFluxAngle g μ ν φ (fun k => ((x k).cast : ℤ)) i, fun x i => ?_⟩,
    fun x i j hij => ?_⟩
  · obtain ⟨z, rfl⟩ := hlift x
    have e : (siteOfInt z : TorusSite n) = siteOfInt fun k => (((siteOfInt z : TorusSite n) k).cast : ℤ) := by
      funext k
      simp [siteOfInt]
    conv_lhs => rw [e]
    exact key _ i
  · obtain ⟨z, rfl⟩ := hlift x
    unfold holonomy
    rw [hstep, hstep, key, key, key, key, expUnit_plaquette_smul,
      linearFluxAngle_circulation g μ ν hμν φ z i j hij]
end YangMills.Construction.ClusterExpansionOfAStep.ConstantCurvatureTop
end
