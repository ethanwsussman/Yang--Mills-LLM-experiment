import YangMills.Construction.SourcesAndGluing.CompositeOfLatticeSimilaritiesProof
import YangMills.Construction.SourcesAndGluing.InverseOfALatticeSimilarityForm
import YangMills.Construction.SourcesAndGluing.LatticeSimilarityDeterminesItsLinearPartForm
import YangMills.Construction.SourcesAndGluing.PlaquettesUnderLatticeSimilaritiesOfFourSpaceForm
import YangMills.Construction.SourcesAndGluing.PlaquettesUnderLatticeSimilaritiesOfToriForm
import YangMills.Construction.SourcesAndGluing.ScalingOfLatticeSimilaritiesOfFourSpaceForm
import YangMills.Construction.SourcesAndGluing.ScalingOfLatticeSimilaritiesOfTori
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SourcesAndGluing
namespace PlaquettesOnTori
open InfiniteLattice (AmbientSpace)
open TorusLifts
abbrev plaquetteProj (D : GluingSetup) (q : InfiniteLattice.ElementaryPlaquette D.mesh) :
    D.PeriodicPlaquette :=
  projectPlaquette D.L (D.m : ℕ) ((D.K : ℕ) : ℤ) q
abbrev pointProj (D : GluingSetup) (x : InfiniteLattice.LatticePoint D.mesh) :
    PeriodicLattice.Site D.L (D.m : ℕ) ((D.K : ℕ) : ℤ) :=
  InfiniteLattice.projectPoint D.L (D.m : ℕ) ((D.K : ℕ) : ℤ) x
theorem pointProj_add (D : GluingSetup) (x y : InfiniteLattice.LatticePoint D.mesh) :
    pointProj D (x + y) = pointProj D x + pointProj D y :=
  Subtype.ext (torusProj_add _ _ _)
theorem pointProj_sub (D : GluingSetup) (x y : InfiniteLattice.LatticePoint D.mesh) :
    pointProj D (x - y) = pointProj D x - pointProj D y :=
  InfiniteLattice.projectPoint_sub D.L (D.m : ℕ) ((D.K : ℕ) : ℤ) x y
theorem pointProj_axisStep (D : GluingSetup) (μ : Fin 4) :
    pointProj D (InfiniteLattice.axisStep D.mesh μ) =
      PeriodicLattice.unitStep D.L (D.m : ℕ) ((D.K : ℕ) : ℤ) μ :=
  InfiniteLattice.projectPoint_axisStep D.L (D.m : ℕ) ((D.K : ℕ) : ℤ) μ
theorem pointProj_surjective (D : GluingSetup) : Function.Surjective (pointProj D) := by
  rintro ⟨u, n, hn⟩
  exact ⟨⟨fun μ => (n μ : ℝ) * D.mesh, n, fun _ => rfl⟩, Subtype.ext (funext hn).symm⟩
theorem plaquetteProj_surjective (D : GluingSetup) : Function.Surjective (plaquetteProj D) := by
  rintro ⟨u, μ, ν, h⟩
  obtain ⟨x, rfl⟩ := pointProj_surjective D u
  exact ⟨⟨x, μ, ν, h⟩, rfl⟩
theorem vertices_plaquetteProj (D : GluingSetup) (q : InfiniteLattice.ElementaryPlaquette D.mesh) :
    (plaquetteProj D q).vertices = pointProj D '' plaquetteVertexSet q := by
  simp only [plaquetteVertexSet, Set.image_insert_eq, Set.image_singleton, pointProj_add,
    pointProj_axisStep]
  rfl
theorem barycenter_plaquetteProj (D : GluingSetup) (q : InfiniteLattice.ElementaryPlaquette D.mesh) :
    (plaquetteProj D q).barycenter =
      TorusMetric.torusProj (PeriodicLattice.torusSide D.L (D.m : ℕ)) q.center := by
  simp only [InfiniteLattice.ElementaryPlaquette.center, torusProj_add]
  rw [torusProj_single, torusProj_single]
  rfl
theorem transport_plaquetteProj {X Y : GluingSetup} (h : X = Y)
    (q : InfiniteLattice.ElementaryPlaquette X.mesh) :
    transport (F := fun Z : GluingSetup => Z.PeriodicPlaquette) h (plaquetteProj X q) =
      plaquetteProj Y
        (transport (F := fun Z : GluingSetup => InfiniteLattice.ElementaryPlaquette Z.mesh) h q) := by
  subst h
  rfl
theorem transport_torusProj {X Y : GluingSetup} (h : X = Y) (x : AmbientSpace) :
    transport (F := fun Z : GluingSetup => Z.Torus) h
        (TorusMetric.torusProj (PeriodicLattice.torusSide X.L (X.m : ℕ)) x) =
      TorusMetric.torusProj (PeriodicLattice.torusSide Y.L (Y.m : ℕ)) x := by apply _root_.YangMills.Construction.SourcesAndGluing.CompositionOfScaledMotions.transport_torusProj <;> assumption
section Maps
variable {D : GluingSetup} {e : ScaleExponent D} (Φ : ScaledLatticeMotion e)
theorem onTorusSite_pointProj (x : InfiniteLattice.LatticePoint D.mesh) :
    Φ.onTorusSite (pointProj D x) = pointProj e.target (Φ.onPoint x) :=
  Subtype.ext (Φ.onTorus_torusProj x)
theorem onTorusPlaquette_plaquetteProj (q : InfiniteLattice.ElementaryPlaquette D.mesh) :
    Φ.onTorusPlaquette (plaquetteProj D q) = plaquetteProj e.target (Φ.onPlaquette q) := by
  refine PeriodicLattice.Plaquette.ext ?_ rfl rfl
  have hA : ∀ x A B : InfiniteLattice.LatticePoint e.target.mesh, pointProj e.target (x - A - B) =
      pointProj e.target x - pointProj e.target A - pointProj e.target B := fun x A B => by
    rw [pointProj_sub, pointProj_sub]
  change Φ.onTorusSite (pointProj D q.corner) -
      pointProj e.target
        ⟨_, signDefect_smul_axisStep_mem (Φ.signs q.lowAxis) e.target.mesh (Φ.perm q.lowAxis)⟩ -
      pointProj e.target
        ⟨_, signDefect_smul_axisStep_mem (Φ.signs q.highAxis) e.target.mesh (Φ.perm q.highAxis)⟩ =
    pointProj e.target (Φ.onPoint q.corner -
      ⟨_, signDefect_smul_axisStep_mem (Φ.signs q.lowAxis) e.target.mesh (Φ.perm q.lowAxis)⟩ -
      ⟨_, signDefect_smul_axisStep_mem (Φ.signs q.highAxis) e.target.mesh (Φ.perm q.highAxis)⟩)
  rw [onTorusSite_pointProj, hA]
theorem onTorusPlaquette_congr {Φ' : ScaledLatticeMotion e} (hS : Φ.rotation = Φ'.rotation)
    (hT : Φ.onTorus = Φ'.onTorus) : Φ.onTorusPlaquette = Φ'.onTorusPlaquette := by
  have hσ : Φ.perm = Φ'.perm := congrArg (fun S : Equiv.Perm AmbientSpace => axisPerm S) hS
  have hε : Φ.signs = Φ'.signs := congrArg (fun S : Equiv.Perm AmbientSpace => axisSigns S) hS
  have hs : Φ.onTorusSite = Φ'.onTorusSite :=
    funext fun u => Subtype.ext (congrFun hT (u : D.Torus))
  funext p
  simp only [ScaledLatticeMotion.onTorusPlaquette, ScaledLatticeMotion.torusPlaquetteOrigin, hσ, hε,
    hs]
end Maps
theorem onTorus_eq_torusInv {D : GluingSetup} {e : ScaleExponent D} (Φ : ScaledLatticeMotion e)
    (Ψ : ScaledLatticeMotion e.neg) (hspace : Function.Injective Φ.onSpace)
    (htorus : Function.Bijective Φ.onTorus) (hΨ : Ψ.onSpace = Function.invFun Φ.onSpace) :
    Ψ.onTorus = Φ.torusInv := by
  funext v
  obtain ⟨u, rfl⟩ := htorus.2 v
  obtain ⟨x, rfl⟩ := TestFunctions.torusProj_surjective _ u
  have hl : Ψ.onSpace (Φ.onSpace x) = x := by
    rw [hΨ]
    exact Function.leftInverse_invFun hspace x
  have hi : Function.invFun Φ.onTorus (Φ.onTorus (TorusMetric.torusProj _ x)) =
      TorusMetric.torusProj _ x :=
    Function.leftInverse_invFun htorus.1 _
  rw [ScaledLatticeMotion.torusInv, hi, transport_torusProj, Φ.onTorus_torusProj]
  refine (Ψ.onTorus_torusProj (Φ.onSpace x)).trans ?_
  rw [hl]
  rfl
end PlaquettesOnTori
open PlaquettesOnTori in
theorem scaledMotionPlaquettesOfTori
    (hSpace : ScaledMotionDilationOfSpaceClaim)
    (hTori : TorusDilationOfScaledMotions.Statement)
    (hDet : ScaledMotionRotationClaim)
    (hInv : ScaledMotionInverseClaim)
    (hPlaq : ScaledMotionPlaquettesOfSpaceClaim) :
    ScaledMotionPlaquettesOfToriClaim := by
  intro D e Φ
  obtain ⟨hc, -, hinv, hb⟩ := hPlaq D e Φ
  obtain ⟨⟨Ψ₁, hS₁, hΨ₁⟩, ⟨Ψ₂, hS₂, hΨ₂⟩⟩ := hInv D e Φ
  have hT₁ : Ψ₁.onTorus = Φ.torusInv :=
    onTorus_eq_torusInv Φ Ψ₁ (hSpace D e Φ).1.injective (hTori D e Φ).1 hΨ₁
  obtain ⟨hl, hr⟩ := hinv Ψ₁ hΨ₁
  have back : ∀ Ψ : ScaledLatticeMotion e.neg, Ψ.onTorus = Φ.torusInv →
      (∀ p, transport (F := fun X : GluingSetup => X.PeriodicPlaquette) e.target_neg
          (Ψ.onTorusPlaquette (Φ.onTorusPlaquette p)) = p) ∧
        ∀ p', Φ.onTorusPlaquette (transport (F := fun X : GluingSetup => X.PeriodicPlaquette)
          e.target_neg (Ψ.onTorusPlaquette p')) = p' := by
    intro Ψ hΨ
    have hS : Ψ.rotation = Ψ₁.rotation :=
      ((hDet _ _ Ψ₂).2 Ψ (hΨ.trans hΨ₂.symm)).trans (hS₂.trans hS₁.symm)
    rw [onTorusPlaquette_congr Ψ hS (hΨ.trans hT₁.symm)]
    refine ⟨fun p => ?_, fun p' => ?_⟩
    · obtain ⟨q, rfl⟩ := plaquetteProj_surjective D p
      rw [onTorusPlaquette_plaquetteProj Φ, onTorusPlaquette_plaquetteProj Ψ₁,
        transport_plaquetteProj, hl q]
    · obtain ⟨q', rfl⟩ := plaquetteProj_surjective e.target p'
      rw [onTorusPlaquette_plaquetteProj Ψ₁, transport_plaquetteProj,
        onTorusPlaquette_plaquetteProj Φ, hr q']
  obtain ⟨bl, br⟩ := back Ψ₂ hΨ₂
  refine ⟨fun p => ?_, ⟨fun p q hpq => ?_, fun p' => ⟨_, br p'⟩⟩, back, fun p => ?_⟩
  · obtain ⟨q, rfl⟩ := plaquetteProj_surjective D p
    rw [onTorusPlaquette_plaquetteProj, vertices_plaquetteProj, hc q, vertices_plaquetteProj,
      Set.image_image, Set.image_image]
    exact Set.image_congr fun x _ => (onTorusSite_pointProj Φ x).symm
  · rw [← bl p, ← bl q, hpq]
  · obtain ⟨q, rfl⟩ := plaquetteProj_surjective D p
    rw [onTorusPlaquette_plaquetteProj, barycenter_plaquetteProj, hb q, barycenter_plaquetteProj]
    exact (Φ.onTorus_torusProj _).symm
end YangMills.Construction.SourcesAndGluing
end
