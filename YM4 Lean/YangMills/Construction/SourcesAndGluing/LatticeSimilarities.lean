import YangMills.Construction.TwoPoints.SignsOfTheContinuumFunctions
import YangMills.Construction.InfiniteLattice.CoveringOfTheTorusLatticeAtOneSpacingProof
import YangMills.Construction.Lattice.LatticeIsometriesAsMapsOfPairsProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusLifts TorusMetric
open InfiniteLattice (AmbientSpace)
namespace SourcesAndGluing
section Closure
variable {L : ℕ} {b j j' : ℤ} {S : Equiv.Perm AmbientSpace}
theorem meshSize_shift_eq_zpow_mul (hL : 0 < L) (h : j' = j - b) :
    PeriodicLattice.meshSize L j' = (L : ℝ) ^ b * PeriodicLattice.meshSize L j := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  subst h
  simp only [PeriodicLattice.meshSize]
  rw [← zpow_add₀ hL']
  congr 1
  ring
theorem map_add_of_mem_hyperoctahedral (hS : S ∈ hyperoctahedralGroupEuclidean)
    (x y : AmbientSpace) : S (x + y) = S x + S y := by apply _root_.YangMills.Construction.TwoPoints.hyperoctahedral_map_add <;> assumption
theorem exists_map_single_of_mem_hyperoctahedral (hS : S ∈ hyperoctahedralGroupEuclidean)
    (μ : Fin 4) :
    ∃ (ν : Fin 4) (ε : ℤˣ), ∀ t : ℝ,
      S (Pi.single μ t) = (((ε : ℤ) : ℝ) * t) • (Pi.single ν 1 : AmbientSpace) := by
  obtain ⟨π, s, rfl⟩ := hS
  refine ⟨π.symm μ, s (π.symm μ), fun t => funext fun κ => ?_⟩
  by_cases h : κ = π.symm μ
  · subst h
    simp [signedCoordinateEquiv, PeriodicLattice.CutoffTorus.signedPermEuclidean]
  · have h' : π κ ≠ μ := fun e => h (by rw [← e]; simp)
    simp [signedCoordinateEquiv, PeriodicLattice.CutoffTorus.signedPermEuclidean,
      Pi.single_eq_of_ne h, Pi.single_eq_of_ne h']
theorem exists_scaledMotion_add_single (hL : 0 < L) (h : j' = j - b)
    (hS : S ∈ hyperoctahedralGroupEuclidean) (w : AmbientSpace) (μ : Fin 4) :
    ∃ ν : Fin 4,
      (∀ x, scaledMotion L b S w (x + Pi.single μ (PeriodicLattice.meshSize L j)) =
        scaledMotion L b S w x + Pi.single ν (PeriodicLattice.meshSize L j')) ∨
      (∀ x, scaledMotion L b S w (x + Pi.single μ (PeriodicLattice.meshSize L j)) =
        scaledMotion L b S w x - Pi.single ν (PeriodicLattice.meshSize L j')) := by
  obtain ⟨ν, ε, hε⟩ := exists_map_single_of_mem_hyperoctahedral hS μ
  refine ⟨ν, ?_⟩
  have hsingle : ∀ c : ℝ, (L : ℝ) ^ b • (c • (Pi.single ν 1 : AmbientSpace)) =
      (c * (L : ℝ) ^ b) • (Pi.single ν 1 : AmbientSpace) := fun c => by
    rw [smul_smul, mul_comm]
  have hstep : (Pi.single ν (PeriodicLattice.meshSize L j') : AmbientSpace) =
      ((L : ℝ) ^ b * PeriodicLattice.meshSize L j) • (Pi.single ν 1 : AmbientSpace) := by
    rw [meshSize_shift_eq_zpow_mul hL h]
    funext κ
    by_cases hκ : κ = ν
    · subst hκ
      simp
    · simp [Pi.single_eq_of_ne hκ]
  rcases Int.units_eq_one_or ε with rfl | rfl
  · refine Or.inl fun x => ?_
    simp only [scaledMotion, map_add_of_mem_hyperoctahedral hS, hε, smul_add, hsingle, hstep]
    simp only [Units.val_one, Int.cast_one, one_mul]
    rw [mul_comm (PeriodicLattice.meshSize L j)]
    abel
  · refine Or.inr fun x => ?_
    simp only [scaledMotion, map_add_of_mem_hyperoctahedral hS, hε, smul_add, hsingle, hstep]
    simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_mul, one_mul,
      neg_smul]
    rw [mul_comm (PeriodicLattice.meshSize L j)]
    abel
theorem scaledMotion_mem_latticeSubgroup (hL : 0 < L) (h : j' = j - b)
    (hS : S ∈ hyperoctahedralGroupEuclidean) {w x : AmbientSpace}
    (hw : w ∈ InfiniteLattice.latticeSubgroup (PeriodicLattice.meshSize L j'))
    (hx : x ∈ InfiniteLattice.latticeSubgroup (PeriodicLattice.meshSize L j)) :
    scaledMotion L b S w x ∈ InfiniteLattice.latticeSubgroup (PeriodicLattice.meshSize L j') := by
  obtain ⟨π, s, rfl⟩ := hS
  obtain ⟨n, hn⟩ := hx
  obtain ⟨n', hn'⟩ := hw
  refine ⟨fun μ => (s μ : ℤ) * n (π μ) + n' μ, fun μ => ?_⟩
  have hμ : (signedCoordinateEquiv π s) x μ = ((s μ : ℤ) : ℝ) * x (π μ) := rfl
  simp only [scaledMotion, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hμ, hn, hn', Int.cast_add,
    Int.cast_mul, meshSize_shift_eq_zpow_mul hL h]
  ring
theorem descendedMap_torusProj {ℓ ℓ' : ℝ} (hℓ : ℓ' = (L : ℝ) ^ b * ℓ)
    (hS : S ∈ hyperoctahedralGroupEuclidean) (w x : AmbientSpace) :
    descendedMap ℓ ℓ' (scaledMotion L b S w) (torusProj ℓ x) =
      torusProj ℓ' (scaledMotion L b S w x) := by
  obtain ⟨k, hk⟩ := TestFunctions.exists_latticeTranslate_of_torusProj_eq
    (TestFunctions.torusProj_liftPoint (torusProj ℓ x))
  rw [descendedMap, hk]
  obtain ⟨π, s, rfl⟩ := hS
  have hper : scaledMotion L b (signedCoordinateEquiv π s) w
      (x + TestFunctions.latticeTranslate ℓ k) =
      scaledMotion L b (signedCoordinateEquiv π s) w x +
        TestFunctions.latticeTranslate ℓ' fun μ => (s μ : ℤ) * k (π μ) := by
    funext μ
    have hμ : ∀ y : AmbientSpace,
        (signedCoordinateEquiv π s) y μ = ((s μ : ℤ) : ℝ) * y (π μ) :=
      fun _ => rfl
    simp only [scaledMotion, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hμ,
      TestFunctions.latticeTranslate, hℓ, Int.cast_mul]
    ring
  rw [hper, TestFunctions.torusProj_add_latticeTranslate]
theorem torusProj_add (ℓ : ℝ) (x y : AmbientSpace) :
    torusProj ℓ (x + y) = torusProj ℓ x + torusProj ℓ y := by apply _root_.YangMills.Construction.AffineTorusIsometries.torusProj_add' <;> assumption
theorem torusProj_single (L m : ℕ) (μ : Fin 4) (t : ℝ) :
    torusProj (PeriodicLattice.torusSide L m) (Pi.single μ t) =
      PeriodicLattice.pointOnAxis L m μ t := by apply _root_.YangMills.Construction.InfiniteLattice.TorusCovering.torusProj_single <;> assumption
theorem torusProj_mem_sublattice (L m : ℕ) {j : ℤ} {x : AmbientSpace}
    (hx : x ∈ InfiniteLattice.latticeSubgroup (PeriodicLattice.meshSize L j)) :
    torusProj (PeriodicLattice.torusSide L m) x ∈ PeriodicLattice.sublattice L m j :=
  (InfiniteLattice.projectPoint L m j ⟨x, hx⟩).2
theorem descendedMap_mem_sublattice {m m' : ℕ} (hL : 0 < L) (h : j' = j - b)
    (hm : PeriodicLattice.torusSide L m' = (L : ℝ) ^ b * PeriodicLattice.torusSide L m)
    (hS : S ∈ hyperoctahedralGroupEuclidean) {w : AmbientSpace}
    (hw : w ∈ InfiniteLattice.latticeSubgroup (PeriodicLattice.meshSize L j'))
    {u : PeriodicLattice.FourTorus L m} (hu : u ∈ PeriodicLattice.sublattice L m j) :
    descendedMap (PeriodicLattice.torusSide L m) (PeriodicLattice.torusSide L m')
        (scaledMotion L b S w) u ∈
      PeriodicLattice.sublattice L m' j' := by
  obtain ⟨n, hn⟩ := hu
  have hx : (fun μ => (n μ : ℝ) * PeriodicLattice.meshSize L j) ∈
      InfiniteLattice.latticeSubgroup (PeriodicLattice.meshSize L j) := ⟨n, fun _ => rfl⟩
  have hu' : u = torusProj (PeriodicLattice.torusSide L m)
      fun μ => (n μ : ℝ) * PeriodicLattice.meshSize L j :=
    funext hn
  rw [hu', descendedMap_torusProj hm hS]
  exact torusProj_mem_sublattice L m' (scaledMotion_mem_latticeSubgroup hL h hS hw hx)
theorem exists_descendedMap_add_pointOnAxis {m m' : ℕ} (hL : 0 < L) (h : j' = j - b)
    (hm : PeriodicLattice.torusSide L m' = (L : ℝ) ^ b * PeriodicLattice.torusSide L m)
    (hS : S ∈ hyperoctahedralGroupEuclidean) (w : AmbientSpace) (μ : Fin 4) :
    ∃ ν : Fin 4,
      (∀ u : PeriodicLattice.FourTorus L m,
        descendedMap (PeriodicLattice.torusSide L m) (PeriodicLattice.torusSide L m')
            (scaledMotion L b S w)
            (u + PeriodicLattice.pointOnAxis L m μ (PeriodicLattice.meshSize L j)) =
          descendedMap (PeriodicLattice.torusSide L m) (PeriodicLattice.torusSide L m')
              (scaledMotion L b S w) u +
            PeriodicLattice.pointOnAxis L m' ν (PeriodicLattice.meshSize L j')) ∨
      (∀ u : PeriodicLattice.FourTorus L m,
        descendedMap (PeriodicLattice.torusSide L m) (PeriodicLattice.torusSide L m')
            (scaledMotion L b S w)
            (u + PeriodicLattice.pointOnAxis L m μ (PeriodicLattice.meshSize L j)) =
          descendedMap (PeriodicLattice.torusSide L m) (PeriodicLattice.torusSide L m')
              (scaledMotion L b S w) u -
            PeriodicLattice.pointOnAxis L m' ν (PeriodicLattice.meshSize L j')) := by
  obtain ⟨ν, hν⟩ := exists_scaledMotion_add_single hL h hS w μ
  refine ⟨ν, hν.imp (fun hp u => ?_) (fun hp u => ?_)⟩
  · obtain ⟨x, rfl⟩ := TestFunctions.torusProj_surjective _ u
    rw [← torusProj_single, ← torusProj_add, descendedMap_torusProj hm hS,
      descendedMap_torusProj hm hS, hp, torusProj_add, torusProj_single]
  · obtain ⟨x, rfl⟩ := TestFunctions.torusProj_surjective _ u
    rw [← torusProj_single, ← torusProj_add, descendedMap_torusProj hm hS,
      descendedMap_torusProj hm hS, hp, sub_eq_add_neg, torusProj_add, sub_eq_add_neg,
      ← torusProj_single]
    congr 1
theorem sub_eq_or_of_translate_step {G G' : Type*} [AddCommGroup G] [AddCommGroup G']
    {f : G → G'} {A : G} {A' : G'}
    (hf : (∀ x, f (x + A) = f x + A') ∨ (∀ x, f (x + A) = f x - A')) {x y : G}
    (hxy : y - x = A ∨ y - x = -A) : f y - f x = A' ∨ f y - f x = -A' := by
  rcases hxy with hxy | hxy
  · obtain rfl : y = x + A := by rw [← hxy]; abel
    rcases hf with hf | hf
    · exact Or.inl (by rw [hf]; abel)
    · exact Or.inr (by rw [hf]; abel)
  · obtain rfl : x = y + A := by rw [← neg_eq_iff_eq_neg.mpr hxy]; abel
    rcases hf with hf | hf
    · exact Or.inr (by rw [hf]; abel)
    · exact Or.inl (by rw [hf]; abel)
end Closure
structure ScaleExponent (D : GluingSetup) where
  shift : ℤ
  one_le_cutoff_sub : 1 ≤ ((D.K : ℕ) : ℤ) - shift
  one_le_side_add : 1 ≤ ((D.m : ℕ) : ℤ) + shift
namespace ScaleExponent
variable {D : GluingSetup} (e : ScaleExponent D)
def targetCutoff : ℕ+ :=
  ⟨(((D.K : ℕ) : ℤ) - e.shift).toNat, by have := e.one_le_cutoff_sub; omega⟩
def targetSideExponent : ℕ+ :=
  ⟨(((D.m : ℕ) : ℤ) + e.shift).toNat, by have := e.one_le_side_add; omega⟩
def target : GluingSetup := D.withCutoffAndSide e.targetCutoff e.targetSideExponent
theorem target_K : ((e.target.K : ℕ) : ℤ) = ((D.K : ℕ) : ℤ) - e.shift := by
  have h := e.one_le_cutoff_sub
  change (((((D.K : ℕ) : ℤ) - e.shift).toNat : ℕ) : ℤ) = _
  omega
theorem target_m : ((e.target.m : ℕ) : ℤ) = ((D.m : ℕ) : ℤ) + e.shift := by
  have h := e.one_le_side_add
  change (((((D.m : ℕ) : ℤ) + e.shift).toNat : ℕ) : ℤ) = _
  omega
theorem L_pos : 0 < D.L := by
  have h := D.isAdmissible.2
  omega
theorem torusSide_target :
    PeriodicLattice.torusSide D.L (e.target.m : ℕ) =
      (D.L : ℝ) ^ e.shift * PeriodicLattice.torusSide D.L (D.m : ℕ) := by
  have hL : (D.L : ℝ) ≠ 0 := by exact_mod_cast (L_pos (D := D)).ne'
  simp only [PeriodicLattice.torusSide]
  rw [← zpow_natCast, ← zpow_natCast, e.target_m, zpow_add₀ hL]
  ring
end ScaleExponent
structure ScaledLatticeMotion {D : GluingSetup} (e : ScaleExponent D) where
  rotation : Equiv.Perm AmbientSpace
  rotation_mem : rotation ∈ hyperoctahedralGroupEuclidean
  offset : AmbientSpace
  offset_mem : offset ∈ e.target.gridPoints
def signDefect (ε : ℤˣ) : ℝ := (1 - ((ε : ℤ) : ℝ)) / 2
theorem signDefect_smul_axisStep_mem (ε : ℤˣ) (a : ℝ) (ν : Fin 4) :
    signDefect ε • ((InfiniteLattice.axisStep a ν : InfiniteLattice.LatticePoint a) :
      AmbientSpace) ∈ InfiniteLattice.latticeSubgroup a := by
  rcases Int.units_eq_one_or ε with rfl | rfl
  · simp [signDefect]
  · have h : signDefect (-1) = 1 := by norm_num [signDefect]
    rw [h, one_smul]
    exact (InfiniteLattice.axisStep a ν).2
namespace ScaledLatticeMotion
variable {D : GluingSetup} {e : ScaleExponent D} (Φ : ScaledLatticeMotion e)
def onSpace : AmbientSpace → AmbientSpace := scaledMotion D.L e.shift Φ.rotation Φ.offset
def onTorus : D.Torus → e.target.Torus :=
  descendedMap (PeriodicLattice.torusSide D.L (D.m : ℕ))
    (PeriodicLattice.torusSide D.L (e.target.m : ℕ)) Φ.onSpace
theorem onTorus_torusProj (x : AmbientSpace) :
    Φ.onTorus (torusProj (PeriodicLattice.torusSide D.L (D.m : ℕ)) x) =
      torusProj (PeriodicLattice.torusSide D.L (e.target.m : ℕ)) (Φ.onSpace x) :=
  descendedMap_torusProj e.torusSide_target Φ.rotation_mem Φ.offset x
def perm : Equiv.Perm (Fin 4) := axisPerm Φ.rotation
def signs : Fin 4 → ℤˣ := axisSigns Φ.rotation
theorem target_mesh :
    e.target.mesh = PeriodicLattice.meshSize D.L (((D.K : ℕ) : ℤ) - e.shift) :=
  congrArg (PeriodicLattice.meshSize D.L) e.target_K
def onPoint (x : InfiniteLattice.LatticePoint D.mesh) :
    InfiniteLattice.LatticePoint e.target.mesh :=
  ⟨Φ.onSpace x, scaledMotion_mem_latticeSubgroup ScaleExponent.L_pos e.target_K
    Φ.rotation_mem Φ.offset_mem x.2⟩
def onTorusSite (u : PeriodicLattice.Site D.L (D.m : ℕ) ((D.K : ℕ) : ℤ)) :
    PeriodicLattice.Site e.target.L (e.target.m : ℕ) ((e.target.K : ℕ) : ℤ) :=
  ⟨Φ.onTorus u, descendedMap_mem_sublattice ScaleExponent.L_pos e.target_K
    e.torusSide_target Φ.rotation_mem Φ.offset_mem u.2⟩
def onLink (c : InfiniteLattice.Link D.mesh) : InfiniteLattice.Link e.target.mesh where
  initial := Φ.onPoint c.initial
  terminal := Φ.onPoint c.terminal
  isAdjacent := by
    obtain ⟨μ, hμ⟩ := c.isAdjacent
    obtain ⟨ν, hν⟩ := exists_scaledMotion_add_single ScaleExponent.L_pos
      e.target_K Φ.rotation_mem Φ.offset μ
    exact ⟨ν, (sub_eq_or_of_translate_step hν
      (hμ.imp (congrArg Subtype.val) (congrArg Subtype.val))).imp Subtype.ext Subtype.ext⟩
def onTorusLink (c : D.PeriodicLink) : e.target.PeriodicLink where
  source := Φ.onTorusSite c.source
  target := Φ.onTorusSite c.target
  isNeighbour := by
    obtain ⟨μ, hμ⟩ := c.isNeighbour
    obtain ⟨ν, hν⟩ := exists_descendedMap_add_pointOnAxis ScaleExponent.L_pos
      e.target_K e.torusSide_target Φ.rotation_mem Φ.offset μ
    exact ⟨ν, (sub_eq_or_of_translate_step hν
      (hμ.imp (congrArg Subtype.val) (congrArg Subtype.val))).imp Subtype.ext Subtype.ext⟩
def plaquetteCorner (x : InfiniteLattice.LatticePoint D.mesh) (μ ν : Fin 4) :
    InfiniteLattice.LatticePoint e.target.mesh :=
  Φ.onPoint x -
    ⟨_, signDefect_smul_axisStep_mem (Φ.signs μ) e.target.mesh (Φ.perm μ)⟩ -
    ⟨_, signDefect_smul_axisStep_mem (Φ.signs ν) e.target.mesh (Φ.perm ν)⟩
def torusPlaquetteOrigin (u : PeriodicLattice.Site D.L (D.m : ℕ) ((D.K : ℕ) : ℤ))
    (μ ν : Fin 4) :
    PeriodicLattice.Site e.target.L (e.target.m : ℕ) ((e.target.K : ℕ) : ℤ) :=
  Φ.onTorusSite u -
    InfiniteLattice.projectPoint e.target.L (e.target.m : ℕ) ((e.target.K : ℕ) : ℤ)
      ⟨_, signDefect_smul_axisStep_mem (Φ.signs μ) e.target.mesh (Φ.perm μ)⟩ -
    InfiniteLattice.projectPoint e.target.L (e.target.m : ℕ) ((e.target.K : ℕ) : ℤ)
      ⟨_, signDefect_smul_axisStep_mem (Φ.signs ν) e.target.mesh (Φ.perm ν)⟩
def onPlaquette (p : InfiniteLattice.ElementaryPlaquette D.mesh) :
    InfiniteLattice.ElementaryPlaquette e.target.mesh where
  corner := Φ.plaquetteCorner p.corner p.lowAxis p.highAxis
  lowAxis := min (Φ.perm p.lowAxis) (Φ.perm p.highAxis)
  highAxis := max (Φ.perm p.lowAxis) (Φ.perm p.highAxis)
  lowAxis_lt_highAxis := min_lt_max.2 (Φ.perm.injective.ne p.lowAxis_lt_highAxis.ne)
def onTorusPlaquette (p : PeriodicLattice.Plaquette D.L (D.m : ℕ) ((D.K : ℕ) : ℤ)) :
    PeriodicLattice.Plaquette e.target.L (e.target.m : ℕ) ((e.target.K : ℕ) : ℤ) where
  origin := Φ.torusPlaquetteOrigin p.origin p.firstAxis p.secondAxis
  firstAxis := min (Φ.perm p.firstAxis) (Φ.perm p.secondAxis)
  secondAxis := max (Φ.perm p.firstAxis) (Φ.perm p.secondAxis)
  firstAxis_lt_secondAxis := min_lt_max.2 (Φ.perm.injective.ne p.firstAxis_lt_secondAxis.ne)
def pullField (U' : e.target.GridField) : D.GridField :=
  ⟨fun c => U' (Φ.onLink c), fun c => U'.2 (Φ.onLink c)⟩
def pullTorusField (U' : e.target.PeriodicLink → Matrices.ComplexMatrix2) :
    D.PeriodicLink → Matrices.ComplexMatrix2 :=
  fun c => U' (Φ.onTorusLink c)
end ScaledLatticeMotion
def IsScaledMotionOfSpace {D : GluingSetup} (e : ScaleExponent D)
    (S : Equiv.Perm AmbientSpace) (f : AmbientSpace → AmbientSpace) : Prop :=
  ∃ Φ : ScaledLatticeMotion e, Φ.rotation = S ∧ Φ.onSpace = f
def IsScaledMotionOfTori {D : GluingSetup} (e : ScaleExponent D)
    (S : Equiv.Perm AmbientSpace) (f : D.Torus → e.target.Torus) : Prop :=
  ∃ Φ : ScaledLatticeMotion e, Φ.rotation = S ∧ Φ.onTorus = f
end SourcesAndGluing
end YangMills.Construction
end
