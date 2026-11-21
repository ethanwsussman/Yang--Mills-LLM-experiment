import YangMills.Construction.SourcesAndGluing.LinksUnderLatticeSimilaritiesOfToriForm
import YangMills.Construction.SourcesAndGluing.PlaquettesUnderLatticeSimilaritiesOfToriForm
import YangMills.Construction.SourcesAndGluing.ScalingOfLatticeSimilaritiesOfTori
import YangMills.Construction.SourcesAndGluing.SimilarityCarriesTheTorusLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusLifts
namespace SourcesAndGluing
open InfiniteLattice (AmbientSpace)
namespace PeriodicLatticeRescaling
theorem eq_one_of_isSignedPermOn_one {σ : Equiv.Perm (Fin 4)} {ε : Fin 4 → ℤˣ}
    (h : IsSignedPermOn (⇑(1 : Equiv.Perm AmbientSpace)) σ ε) : σ = 1 ∧ ε = 1 := by
  have hfix : ∀ i, σ i = i ∧ ε i = 1 := fun i => by
    have h1 := congrFun (h i) i
    by_cases hs : σ i = i
    · refine ⟨hs, ?_⟩
      rw [hs] at h1
      have h2 : (((ε i : ℤˣ) : ℤ) : ℝ) = 1 := by simpa using h1.symm
      have h3 : ((ε i : ℤˣ) : ℤ) = 1 := by exact_mod_cast h2
      exact Units.ext h3
    · simp [Pi.single_eq_of_ne (Ne.symm hs)] at h1
  exact ⟨Equiv.ext fun i => (hfix i).1, funext fun i => (hfix i).2⟩
theorem isSignedPermOn_one :
    IsSignedPermOn (⇑(1 : Equiv.Perm AmbientSpace)) 1 (1 : Fin 4 → ℤˣ) := fun i => by
  simp
theorem axisPerm_one : axisPerm (⇑(1 : Equiv.Perm AmbientSpace)) = 1 := by
  have h : ∃ σ, ∃ ε, IsSignedPermOn (⇑(1 : Equiv.Perm AmbientSpace)) σ ε :=
    ⟨1, 1, isSignedPermOn_one⟩
  obtain ⟨ε, hε⟩ := Classical.epsilon_spec h
  exact (eq_one_of_isSignedPermOn_one hε).1
theorem axisSigns_one : axisSigns (⇑(1 : Equiv.Perm AmbientSpace)) = 1 := by
  have h : ∃ ε, IsSignedPermOn (⇑(1 : Equiv.Perm AmbientSpace))
      (axisPerm (⇑(1 : Equiv.Perm AmbientSpace))) ε :=
    ⟨1, by rw [axisPerm_one]; exact isSignedPermOn_one⟩
  exact (eq_one_of_isSignedPermOn_one (Classical.epsilon_spec h)).2
theorem translateBy_mesh_smul_stdBasis (D : GluingSetup) (u : D.Torus) (i : Fin 4) :
    D.translateBy u (D.mesh • stdBasis i) =
      u + (PeriodicLattice.unitStep D.L (D.m : ℕ) ((D.K : ℕ) : ℤ) i : D.Torus) := by
  have h : D.mesh • (stdBasis i : Fin 4 → ℝ) = Pi.single i D.mesh := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp [stdBasis]
    · simp [stdBasis, Pi.single_eq_of_ne hj]
  rw [GluingSetup.translateBy, h]
  congr 1
  exact torusProj_single D.L (D.m : ℕ) i D.mesh
variable {D : GluingSetup} (Ψ : LatticeRescaling D)
theorem perm_eq_one : Ψ.toMotion.perm = 1 := axisPerm_one
theorem signs_eq_one (i : Fin 4) : Ψ.toMotion.signs i = 1 := congrFun axisSigns_one i
theorem onTorusSite_add_unitStep (hΦ : Ψ.toMotion.IsDilatingBijectionOfTori) (i : Fin 4)
    (x : PeriodicLattice.Site D.L (D.m : ℕ) ((D.K : ℕ) : ℤ)) :
    Ψ.toMotion.onTorusSite (x + PeriodicLattice.unitStep D.L (D.m : ℕ) ((D.K : ℕ) : ℤ) i) =
      Ψ.toMotion.onTorusSite x +
        PeriodicLattice.unitStep Ψ.scaleExponent.target.L (Ψ.scaleExponent.target.m : ℕ)
          ((Ψ.scaleExponent.target.K : ℕ) : ℤ) i := by
  obtain ⟨-, -, -, hstep, -⟩ := hΦ
  refine Subtype.ext ?_
  have h := hstep (x : D.Torus) i
  rw [translateBy_mesh_smul_stdBasis, signs_eq_one, perm_eq_one] at h
  have h' : ((((1 : ℤˣ) : ℤ) : ℝ) * Ψ.scaleExponent.target.mesh) = Ψ.scaleExponent.target.mesh := by
    simp
  rw [h', translateBy_mesh_smul_stdBasis] at h
  exact h
theorem projectPoint_signDefect (i j : Fin 4) :
    InfiniteLattice.projectPoint Ψ.scaleExponent.target.L (Ψ.scaleExponent.target.m : ℕ)
        ((Ψ.scaleExponent.target.K : ℕ) : ℤ)
        ⟨_, signDefect_smul_axisStep_mem (Ψ.toMotion.signs i) Ψ.scaleExponent.target.mesh j⟩ = 0 := by
  have h : (⟨_, signDefect_smul_axisStep_mem (Ψ.toMotion.signs i) Ψ.scaleExponent.target.mesh j⟩ :
      InfiniteLattice.LatticePoint Ψ.scaleExponent.target.mesh) = 0 := by
    refine Subtype.ext ?_
    simp [signs_eq_one, signDefect]
  have h0 := InfiniteLattice.projectPoint_sub Ψ.scaleExponent.target.L (Ψ.scaleExponent.target.m : ℕ)
    ((Ψ.scaleExponent.target.K : ℕ) : ℤ) 0 0
  simp only [sub_self] at h0
  exact (congrArg (InfiniteLattice.projectPoint Ψ.scaleExponent.target.L
    (Ψ.scaleExponent.target.m : ℕ) ((Ψ.scaleExponent.target.K : ℕ) : ℤ)) h).trans h0
theorem onTorusPlaquette_eq (p : PeriodicLattice.Plaquette D.L (D.m : ℕ) ((D.K : ℕ) : ℤ)) :
    Ψ.toMotion.onTorusPlaquette p =
      ⟨Ψ.toMotion.onTorusSite p.origin, p.firstAxis, p.secondAxis, p.firstAxis_lt_secondAxis⟩ := by
  have hσ := perm_eq_one Ψ
  refine PeriodicLattice.Plaquette.ext ?_ ?_ ?_
  · change Ψ.toMotion.torusPlaquetteOrigin p.origin p.firstAxis p.secondAxis = _
    rw [ScaledLatticeMotion.torusPlaquetteOrigin, projectPoint_signDefect, projectPoint_signDefect,
      sub_zero, sub_zero]
  · change min (Ψ.toMotion.perm p.firstAxis) (Ψ.toMotion.perm p.secondAxis) = p.firstAxis
    rw [hσ]
    exact min_eq_left p.firstAxis_lt_secondAxis.le
  · change max (Ψ.toMotion.perm p.firstAxis) (Ψ.toMotion.perm p.secondAxis) = p.secondAxis
    rw [hσ]
    exact max_eq_right p.firstAxis_lt_secondAxis.le
end PeriodicLatticeRescaling
open PeriodicLatticeRescaling in
theorem rescalingMapsPeriodicLatticeClaim_holds
    (hLinks : ScaledMotionLinksOfToriClaim)
    (hPlaquettes : ScaledMotionPlaquettesOfToriClaim)
    (hScaling : TorusDilationOfScaledMotions.Statement) :
    RescalingMapsPeriodicLatticeClaim := by
  intro D Ψ
  have hΦ := hScaling D Ψ.scaleExponent Ψ.toMotion
  obtain ⟨hlink, -, hpos⟩ := hLinks D Ψ.scaleExponent Ψ.toMotion
  obtain ⟨-, hplaq, -, hbar⟩ := hPlaquettes D Ψ.scaleExponent Ψ.toMotion
  refine ⟨?_, hΦ.1, hΦ.2.2.2.2, hlink.2, ?_, onTorusPlaquette_eq Ψ, fun p => (hbar p).symm, ?_⟩
  · rw [← Ψ.target_side_eq]
    exact D.side_withCutoffAndSide_mem_sideSet Ψ.scaleExponent.targetCutoff
      Ψ.scaleExponent.targetSideExponent
  · ext c'
    constructor
    · rintro ⟨c, ⟨i, hi⟩, rfl⟩
      have hc : c = PeriodicLattice.Bond.forwardFrom c.source i :=
        PeriodicLattice.Bond.ext rfl (by
          change c.target = c.source + _
          rw [← hi]
          abel)
      rw [hc]
      exact (hpos c.source i).1 (signs_eq_one Ψ i)
    · rintro ⟨j, hj⟩
      obtain ⟨c, rfl⟩ := hlink.2 c'
      refine ⟨PeriodicLattice.Bond.forwardFrom c.source j,
        ⟨j, by simp [PeriodicLattice.Bond.forwardFrom]⟩, ?_⟩
      refine PeriodicLattice.Bond.ext rfl ?_
      change Ψ.toMotion.onTorusSite
        (c.source + PeriodicLattice.unitStep D.L (D.m : ℕ) ((D.K : ℕ) : ℤ) j) = _
      rw [onTorusSite_add_unitStep Ψ hΦ, ← hj]
      change Ψ.toMotion.onTorusSite c.source + (_ - Ψ.toMotion.onTorusSite c.source) = _
      abel
  · ext y
    constructor
    · rintro ⟨_, ⟨p, rfl⟩, rfl⟩
      exact ⟨Ψ.toMotion.onTorusPlaquette p, hbar p⟩
    · rintro ⟨p', rfl⟩
      obtain ⟨p, rfl⟩ := hplaq.2 p'
      exact ⟨_, ⟨p, rfl⟩, (hbar p).symm⟩
end SourcesAndGluing
end YangMills.Construction
end
