import YangMills.Construction.ColdStepAtMirrorFrames.BareActionIsCriticalAtAnAbelianFieldProof
import YangMills.Construction.ColdStepAtMirrorFrames.CurvedChainIsAbelian
import YangMills.Construction.ColdStepAtMirrorFrames.LevelOfTheCurvedChainOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields
namespace YangMills.Construction.ColdStepAtMirrorFrames
private abbrev IntLattice : Type := Fin 4 → ℤ
private theorem expUnit_add_smul (A : imaginaryQuaternions) (s t : ℝ) :
    expUnit ((s + t) • A) = expUnit (s • A) * expUnit (t • A) := by apply _root_.YangMills.SharedProofs.p2328 <;> assumption
private theorem expUnit_smul_inv (A : imaginaryQuaternions) (s : ℝ) :
    (expUnit (s • A))⁻¹ = expUnit ((-s) • A) := by apply _root_.YangMills.SharedProofs.p4359 <;> assumption
theorem constantCurvatureLevelOnTorus_holds (habelian : ConstantCurvatureChainAbelian) :
    ConstantCurvatureLevelOnTorus := by
  intro F A μ ν n l j M hodd hn h0 hA hμν hl hj hM hM0
  obtain ⟨φ, hφ⟩ := (habelian F A μ ν n l hodd hn h0 hA hμν hl j hj).1
  have hflux : levelFlux F μ l j = 2 * Real.pi * l / (M : ℝ) ^ 2 := by
    unfold levelFlux
    rw [hM]
  rw [hflux] at hφ
  set g : ℝ := 2 * Real.pi * l / (M : ℝ) ^ 2 with hg
  have hper : ∀ i, F.period j i = M := hM
  have hsite : ∀ (x : TorusSite M) (w : IntLattice),
      (siteOfCoords j (fun k => ((x k).cast : ℤ) + w k) : F.Site j) =
      siteOfCoords j (fun k => (((x + (fun k => ((w k : ℤ) : ZMod M))) k).cast : ℤ)) := by
    intro x w
    funext k
    unfold siteOfCoords
    apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2
    rw [hper k]
    have h1 : ((((x k + (w k : ZMod M)).cast : ℤ) : ZMod M)) = (((x k).cast + w k : ℤ) : ZMod M) := by
      have : NeZero M := ⟨hM0.ne'⟩
      push_cast
      simp
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h1.symm
    exact this
  have hV : ∀ (x : TorusSite M) (w : IntLattice) (i : Fin 4),
      restrictToTorus M (constantCurvatureChain F A μ ν l j) (x + (fun k => ((w k : ℤ) : ZMod M))) i =
        expUnit (linearFluxAngle g μ ν φ (fun k => ((x k).cast : ℤ) + w k) i • A) := by
    intro x w i
    unfold restrictToTorus
    rw [← hsite, hφ]
  have hV0 : ∀ (x : TorusSite M) (i : Fin 4), restrictToTorus M (constantCurvatureChain F A μ ν l j) x i =
      expUnit (linearFluxAngle g μ ν φ (fun k => ((x k).cast : ℤ)) i • A) := by
    intro x i
    have h00 : x + (fun k => (((0 : IntLattice) k : ℤ) : ZMod M)) = x := by
      funext k
      simp
    have := hV x 0 i
    rw [h00] at this
    simpa using this
  refine ⟨⟨fun x i => linearFluxAngle g μ ν φ (fun k => ((x k).cast : ℤ)) i, hV0⟩, ?_⟩
  intro x i j hij
  have hstep : ∀ i : Fin 4, TorusFields.unitStep M i = (fun k => (((Pi.single i 1 : IntLattice) k : ℤ) : ZMod M)) := by
    intro i
    funext k
    unfold TorusFields.unitStep
    by_cases hk : k = i
    · subst hk; simp
    · simp [hk]
  unfold holonomy
  rw [hstep i, hstep j, hV x (Pi.single i 1) j, hV x (Pi.single j 1) i, hV0 x i, hV0 x j,
    expUnit_smul_inv, expUnit_smul_inv, ← expUnit_add_smul, ← expUnit_add_smul, ← expUnit_add_smul]
  congr 2
  set z : IntLattice := fun k => ((x k).cast : ℤ) with hz
  have hcomm : z + Pi.single i 1 + Pi.single j 1 = z + Pi.single j 1 + Pi.single i 1 := by abel
  have hz1 : (fun k => ((x k).cast : ℤ) + (Pi.single i 1 : IntLattice) k) = z + Pi.single i 1 := rfl
  have hz2 : (fun k => ((x k).cast : ℤ) + (Pi.single j 1 : IntLattice) k) = z + Pi.single j 1 := rfl
  rw [hz1, hz2]
  unfold linearFluxAngle
  rw [hcomm]
  unfold planeUnitForm
  have hne : i ≠ j := hij.ne
  have e1 : (((z + Pi.single i 1 : IntLattice) μ : ℤ) : ℝ) = (z μ : ℝ) + if i = μ then 1 else 0 := by
    by_cases h : i = μ
    · subst h; simp
    · simp [h, Ne.symm h]
  have e2 : (((z + Pi.single j 1 : IntLattice) μ : ℤ) : ℝ) = (z μ : ℝ) + if j = μ then 1 else 0 := by
    by_cases h : j = μ
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [e1, e2]
  by_cases hiν : i = ν
  · have hjν : j ≠ ν := by rw [← hiν]; exact Ne.symm hne
    have hiμ : i ≠ μ := by rw [hiν]; exact hμν.ne'
    have hjμ : j ≠ μ := by
      intro h
      rw [hiν, h] at hij
      exact absurd hij (not_lt.mpr hμν.le)
    have hp : (if i = μ ∧ j = ν then (1 : ℝ) else if i = ν ∧ j = μ then (-1 : ℝ) else 0) = 0 := by
      rw [if_neg (fun h => hiμ h.1), if_neg (fun h => hjμ h.2)]
    rw [hp]
    simp only [if_pos hiν, if_neg hjν, if_neg hiμ, if_neg hjμ]
    ring
  · by_cases hjν : j = ν
    · by_cases hiμ : i = μ
      · have hjμ : j ≠ μ := by rw [hiμ] at hne; exact Ne.symm hne
        have hp : (if i = μ ∧ j = ν then (1 : ℝ) else if i = ν ∧ j = μ then (-1 : ℝ) else 0) = 1 := by
          rw [if_pos ⟨hiμ, hjν⟩]
        rw [hp]
        simp only [if_neg hiν, if_pos hjν, if_pos hiμ, if_neg hjμ]
        ring
      · have hp : (if i = μ ∧ j = ν then (1 : ℝ) else if i = ν ∧ j = μ then (-1 : ℝ) else 0) = 0 := by
          rw [if_neg (fun h => hiμ h.1), if_neg (fun h => hiν h.1)]
        rw [hp]
        simp only [if_neg hiν, if_pos hjν, if_neg hiμ]
        ring
    · have hp : (if i = μ ∧ j = ν then (1 : ℝ) else if i = ν ∧ j = μ then (-1 : ℝ) else 0) = 0 := by
        rw [if_neg (fun h => hjν h.2), if_neg (fun h => hiν h.1)]
      rw [hp]
      simp only [if_neg hiν, if_neg hjν]
      ring
end YangMills.Construction.ColdStepAtMirrorFrames
end
