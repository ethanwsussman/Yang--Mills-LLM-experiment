import YangMills.Construction.ColdStepAtMirrorFrames.BareActionIsCriticalAtAnAbelianFieldProof
import YangMills.Construction.ColdStepAtMirrorFrames.CurvedChainIsAbelian
import YangMills.Construction.ColdStepAtMirrorFrames.TopOfTheCurvedChainOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
private abbrev Lattice4 : Type := Fin 4 → ℤ
private theorem expUnit_add_smul (X : imaginaryQuaternions) (s t : ℝ) :
    expUnit ((s + t) • X) = expUnit (s • X) * expUnit (t • X) := by apply _root_.YangMills.SharedProofs.p2328 <;> assumption
private theorem expUnit_smul_inv (X : imaginaryQuaternions) (s : ℝ) :
    (expUnit (s • X))⁻¹ = expUnit ((-s) • X) := by apply _root_.YangMills.SharedProofs.p4359 <;> assumption
theorem constantCurvatureTopOnTorus_of_abelian (habelian : ConstantCurvatureChainAbelian) :
    ConstantCurvatureTopOnTorus := by
  intro F X μ ν n l hodd hn h0 hX hμν hl
  obtain ⟨φ, hφ⟩ := (habelian F X μ ν n l hodd hn h0 hX hμν hl F.top le_rfl).1
  have hflux : levelFlux F μ l F.top = 2 * Real.pi * l / (n : ℝ) ^ 2 := by
    unfold levelFlux BlockFrame.period
    simp [hn]
  rw [hflux] at hφ
  set g : ℝ := 2 * Real.pi * l / (n : ℝ) ^ 2 with hg
  have hper : ∀ i, F.period F.top i = n := by
    intro i
    unfold BlockFrame.period
    simp [hn]
  have hsite : ∀ (x : TorusFields.TorusSite n) (w : Lattice4),
      (siteOfCoords F.top (fun k => ((x k).cast : ℤ) + w k) : F.Site F.top) =
      siteOfCoords F.top (fun k => (((x + (fun k => ((w k : ℤ) : ZMod n))) k).cast : ℤ)) := by
    intro x w
    funext k
    unfold siteOfCoords
    apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2
    rw [hper k]
    have h1 : ((((x k + (w k : ZMod n)).cast : ℤ) : ZMod n)) = (((x k).cast + w k : ℤ) : ZMod n) := by
      have : NeZero n := ⟨h0.ne'⟩
      push_cast
      simp
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h1.symm
    exact this
  have hV : ∀ (x : TorusFields.TorusSite n) (w : Lattice4) (i : Fin 4),
      restrictToTorus n (constantCurvatureChain F X μ ν l F.top) (x + (fun k => ((w k : ℤ) : ZMod n))) i =
        expUnit (linearFluxAngle g μ ν φ (fun k => ((x k).cast : ℤ) + w k) i • X) := by
    intro x w i
    unfold restrictToTorus
    rw [← hsite, hφ]
  have hV0 : ∀ (x : TorusFields.TorusSite n) (i : Fin 4),
      restrictToTorus n (constantCurvatureChain F X μ ν l F.top) x i =
      expUnit (linearFluxAngle g μ ν φ (fun k => ((x k).cast : ℤ)) i • X) := by
    intro x i
    have h00 : x + (fun k => (((0 : Lattice4) k : ℤ) : ZMod n)) = x := by
      funext k
      simp
    have := hV x 0 i
    rw [h00] at this
    simpa using this
  refine ⟨⟨fun x i => linearFluxAngle g μ ν φ (fun k => ((x k).cast : ℤ)) i, hV0⟩, ?_⟩
  intro x i j hij
  have hev : ∀ i : Fin 4, TorusFields.unitStep n i = (fun k => (((Pi.single i 1 : Lattice4) k : ℤ) : ZMod n)) := by
    intro i
    funext k
    unfold TorusFields.unitStep
    by_cases hk : k = i
    · subst hk; simp
    · simp [hk]
  unfold TorusFields.holonomy
  rw [hev i, hev j, hV x (Pi.single i 1) j, hV x (Pi.single j 1) i, hV0 x i, hV0 x j,
    expUnit_smul_inv, expUnit_smul_inv, ← expUnit_add_smul, ← expUnit_add_smul, ← expUnit_add_smul]
  congr 2
  set z : Lattice4 := fun k => ((x k).cast : ℤ) with hz
  have hcomm : z + Pi.single i 1 + Pi.single j 1 = z + Pi.single j 1 + Pi.single i 1 := by abel
  have hz1 : (fun k => ((x k).cast : ℤ) + (Pi.single i 1 : Lattice4) k) = z + Pi.single i 1 := rfl
  have hz2 : (fun k => ((x k).cast : ℤ) + (Pi.single j 1 : Lattice4) k) = z + Pi.single j 1 := rfl
  rw [hz1, hz2]
  unfold linearFluxAngle
  rw [hcomm]
  unfold planeUnitForm
  have hne : i ≠ j := hij.ne
  have e1 : (((z + Pi.single i 1 : Lattice4) μ : ℤ) : ℝ) = (z μ : ℝ) + if i = μ then 1 else 0 := by
    by_cases h : i = μ
    · subst h; simp
    · simp [h, Ne.symm h]
  have e2 : (((z + Pi.single j 1 : Lattice4) μ : ℤ) : ℝ) = (z μ : ℝ) + if j = μ then 1 else 0 := by
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
end ColdStepAtMirrorFrames
end YangMills.Construction
end
