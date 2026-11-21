import YangMills.Construction.SourcesAndGluing.SimilarityCarriesTheTorusLatticeProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SourcesAndGluing
namespace ScaledMotionLinks
theorem translateBy_mesh_smul_stdBasis (D : GluingSetup) (u : D.Torus) (μ : Fin 4) :
    D.translateBy u (D.mesh • stdBasis μ) =
      u + (PeriodicLattice.unitStep D.L (D.m : ℕ) ((D.K : ℕ) : ℤ) μ : D.Torus) := by apply _root_.YangMills.Construction.SourcesAndGluing.PeriodicLatticeRescaling.translateBy_mesh_smul_stdBasis <;> assumption
theorem translateBy_neg_mesh_smul_stdBasis (D : GluingSetup) (u : D.Torus) (μ : Fin 4) :
    D.translateBy u ((-1 * D.mesh) • stdBasis μ) =
      u - (PeriodicLattice.unitStep D.L (D.m : ℕ) ((D.K : ℕ) : ℤ) μ : D.Torus) := by
  have hzero := translateBy_mesh_smul_stdBasis D 0 μ
  simp only [GluingSetup.translateBy, zero_add] at hzero
  have hneg : (-1 * D.mesh) • (stdBasis μ : Fin 4 → ℝ) = -(D.mesh • stdBasis μ) := by
    rw [neg_one_mul, neg_smul]
  rw [GluingSetup.translateBy, hneg, sub_eq_add_neg, ← hzero]
  congr 1
variable {D : GluingSetup} {e : ScaleExponent D} (Φ : ScaledLatticeMotion e)
theorem onTorusSite_bijective (hΦ : Φ.IsDilatingBijectionOfTori) :
    Function.Bijective Φ.onTorusSite := by
  obtain ⟨hbij, -, -, -, himg⟩ := hΦ
  refine ⟨fun x y hxy => Subtype.ext (hbij.1 (congrArg Subtype.val hxy)), fun y => ?_⟩
  have hy : (y : e.target.Torus) ∈ Φ.onTorus '' (D.periodicLattice : Set D.Torus) := by
    rw [himg]
    exact y.2
  obtain ⟨x, hx, hxy⟩ := hy
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
theorem onTorusSite_add_unitStep_of_eq_one (hΦ : Φ.IsDilatingBijectionOfTori) {μ : Fin 4}
    (hμ : Φ.signs μ = 1) (x : PeriodicLattice.Site D.L (D.m : ℕ) ((D.K : ℕ) : ℤ)) :
    Φ.onTorusSite (x + PeriodicLattice.unitStep D.L (D.m : ℕ) ((D.K : ℕ) : ℤ) μ) =
      Φ.onTorusSite x +
        PeriodicLattice.unitStep e.target.L (e.target.m : ℕ) ((e.target.K : ℕ) : ℤ) (Φ.perm μ) := by
  obtain ⟨-, -, -, hstep, -⟩ := hΦ
  refine Subtype.ext ?_
  have hx := hstep (x : D.Torus) μ
  rw [translateBy_mesh_smul_stdBasis, hμ] at hx
  have hcoef : ((((1 : ℤˣ) : ℤ) : ℝ) * e.target.mesh) = e.target.mesh := by simp
  rw [hcoef, translateBy_mesh_smul_stdBasis] at hx
  exact hx
theorem onTorusSite_add_unitStep_of_eq_neg_one (hΦ : Φ.IsDilatingBijectionOfTori) {μ : Fin 4}
    (hμ : Φ.signs μ = -1) (x : PeriodicLattice.Site D.L (D.m : ℕ) ((D.K : ℕ) : ℤ)) :
    Φ.onTorusSite (x + PeriodicLattice.unitStep D.L (D.m : ℕ) ((D.K : ℕ) : ℤ) μ) =
      Φ.onTorusSite x -
        PeriodicLattice.unitStep e.target.L (e.target.m : ℕ) ((e.target.K : ℕ) : ℤ) (Φ.perm μ) := by
  obtain ⟨-, -, -, hstep, -⟩ := hΦ
  refine Subtype.ext ?_
  have hx := hstep (x : D.Torus) μ
  rw [translateBy_mesh_smul_stdBasis, hμ] at hx
  have hcoef : (((((-1 : ℤˣ)) : ℤ) : ℝ) * e.target.mesh) = -1 * e.target.mesh := by simp
  rw [hcoef, translateBy_neg_mesh_smul_stdBasis] at hx
  exact hx
theorem onTorusLink_surjective (hΦ : Φ.IsDilatingBijectionOfTori) :
    Function.Surjective Φ.onTorusLink := by
  intro b'
  obtain ⟨t, ht⟩ := (onTorusSite_bijective Φ hΦ).2 b'.source
  obtain ⟨ν, hν⟩ := b'.isNeighbour
  obtain ⟨μ, rfl⟩ := Φ.perm.surjective ν
  have hlift : ∀ s : PeriodicLattice.Site D.L (D.m : ℕ) ((D.K : ℕ) : ℤ),
      Φ.onTorusSite s = b'.target →
      (s - t = PeriodicLattice.unitStep D.L (D.m : ℕ) ((D.K : ℕ) : ℤ) μ ∨
        s - t = -PeriodicLattice.unitStep D.L (D.m : ℕ) ((D.K : ℕ) : ℤ) μ) →
      ∃ b, Φ.onTorusLink b = b' := fun s hs hst =>
    ⟨⟨t, s, μ, hst⟩, PeriodicLattice.Bond.ext ht hs⟩
  have htarget : b'.target = b'.source + (b'.target - b'.source) := by abel
  rcases Int.units_eq_one_or (Φ.signs μ) with hsign | hsign
  · have hmove := onTorusSite_add_unitStep_of_eq_one Φ hΦ hsign
    rcases hν with hν | hν
    · refine hlift (t + PeriodicLattice.unitStep D.L (D.m : ℕ) ((D.K : ℕ) : ℤ) μ) ?_
        (Or.inl (by abel))
      rw [hmove, ht, ← hν]
      abel
    · refine hlift (t - PeriodicLattice.unitStep D.L (D.m : ℕ) ((D.K : ℕ) : ℤ) μ) ?_
        (Or.inr (by abel))
      have hback := hmove (t - PeriodicLattice.unitStep D.L (D.m : ℕ) ((D.K : ℕ) : ℤ) μ)
      rw [sub_add_cancel, ht] at hback
      rw [htarget, hν, hback]
      abel
  · have hmove := onTorusSite_add_unitStep_of_eq_neg_one Φ hΦ hsign
    rcases hν with hν | hν
    · refine hlift (t - PeriodicLattice.unitStep D.L (D.m : ℕ) ((D.K : ℕ) : ℤ) μ) ?_
        (Or.inr (by abel))
      have hback := hmove (t - PeriodicLattice.unitStep D.L (D.m : ℕ) ((D.K : ℕ) : ℤ) μ)
      rw [sub_add_cancel, ht] at hback
      rw [htarget, hν, hback]
      abel
    · refine hlift (t + PeriodicLattice.unitStep D.L (D.m : ℕ) ((D.K : ℕ) : ℤ) μ) ?_
        (Or.inl (by abel))
      rw [hmove, ht, htarget, hν]
      abel
theorem onTorusLink_injective (hΦ : Φ.IsDilatingBijectionOfTori) :
    Function.Injective Φ.onTorusLink := fun _ _ hb =>
  PeriodicLattice.Bond.ext
    ((onTorusSite_bijective Φ hΦ).1 (congrArg PeriodicLattice.Bond.source hb))
    ((onTorusSite_bijective Φ hΦ).1 (congrArg PeriodicLattice.Bond.target hb))
end ScaledMotionLinks
theorem scaledMotionLinksOfToriClaim_of_dilation
    (hDil : TorusDilationOfScaledMotions.Statement) :
    ScaledMotionLinksOfToriClaim := by
  intro D e Φ
  have hΦ := hDil D e Φ
  refine ⟨⟨ScaledMotionLinks.onTorusLink_injective Φ hΦ,
      ScaledMotionLinks.onTorusLink_surjective Φ hΦ⟩, fun b => rfl,
    fun x μ => ⟨fun hsign => ⟨Φ.perm μ, ?_⟩, fun hsign => ⟨Φ.perm μ, ?_⟩⟩⟩
  · change Φ.onTorusSite (x + PeriodicLattice.unitStep D.L (D.m : ℕ) ((D.K : ℕ) : ℤ) μ) -
      Φ.onTorusSite x = _
    rw [ScaledMotionLinks.onTorusSite_add_unitStep_of_eq_one Φ hΦ hsign]
    abel
  · change Φ.onTorusSite x -
      Φ.onTorusSite (x + PeriodicLattice.unitStep D.L (D.m : ℕ) ((D.K : ℕ) : ℤ) μ) = _
    rw [ScaledMotionLinks.onTorusSite_add_unitStep_of_eq_neg_one Φ hΦ hsign]
    abel
end YangMills.Construction.SourcesAndGluing
end
