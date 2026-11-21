import YangMills.Construction.InfiniteLattice.BondsPlaquettesCircuitsAndConfigurationsOfTheLatticeOfACutoffProof
import YangMills.Construction.SourcesAndGluing.CompositeOfLatticeSimilaritiesProof
import YangMills.Construction.SourcesAndGluing.CumulantsOfBoundedVariablesProof
import YangMills.Construction.SourcesAndGluing.InverseOfALatticeSimilarityForm
import YangMills.Construction.SourcesAndGluing.PlaquettesUnderLatticeSimilaritiesOfFourSpaceForm
import YangMills.Construction.SourcesAndGluing.ScalingOfLatticeSimilaritiesOfFourSpaceForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SourcesAndGluing.PlaquetteImages
open InfiniteLattice (AmbientSpace)
open TorusLifts
theorem hyperoctahedral_map_smul {S : Equiv.Perm AmbientSpace} (hS : S ∈ hyperoctahedralGroupEuclidean)
    (t : ℝ) (x : AmbientSpace) : S (t • x) = t • S x := by apply _root_.YangMills.Construction.SourcesAndGluing.CompositionOfScaledMotions.map_smul_of_mem_hyperoctahedral <;> assumption
theorem single_eq_smul_stdBasis (i : Fin 4) (t : ℝ) :
    (Pi.single i t : AmbientSpace) = t • stdBasis i := by apply _root_.YangMills.Construction.RefinedLatticeSymmetries.single_eq_smul_basisVector <;> assumption
theorem mesh_pos (G : GluingSetup) : 0 < G.mesh := by apply _root_.YangMills.Construction.SourcesAndGluing.BoundedCumulants.mesh_pos <;> assumption
theorem signDefect_mul_add_self (u : ℤˣ) : signDefect u * ((u : ℤ) : ℝ) + signDefect u = 0 := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> norm_num [signDefect]
section Step
variable {G : GluingSetup} {k : ScaleExponent G} (Φ : ScaledLatticeMotion k)
theorem onSpace_add_smul (hΦ : Φ.IsDilatingBijectionOfSpace) (x : AmbientSpace) (r : ℝ)
    (i : Fin 4) :
    Φ.onSpace (x + r • (G.mesh • stdBasis i)) =
      Φ.onSpace x + (r * (((Φ.signs i : ℤˣ) : ℤ) : ℝ) * k.target.mesh) • stdBasis (Φ.perm i) := by
  obtain ⟨-, -, h₃, h₄, -⟩ := hΦ
  have hv : (G.L : ℝ) ^ k.shift • Φ.rotation (G.mesh • stdBasis i) =
      ((((Φ.signs i : ℤˣ) : ℤ) : ℝ) * k.target.mesh) • stdBasis (Φ.perm i) :=
    add_left_cancel ((h₃ x (G.mesh • stdBasis i)).symm.trans (h₄ x i))
  rw [h₃, hyperoctahedral_map_smul Φ.rotation_mem, smul_comm, hv, smul_smul, mul_assoc]
theorem onSpace_add_smul_add_smul (hΦ : Φ.IsDilatingBijectionOfSpace) (x : AmbientSpace)
    (r r' : ℝ) (i j : Fin 4) :
    Φ.onSpace (x + r • (G.mesh • stdBasis i) + r' • (G.mesh • stdBasis j)) =
      Φ.onSpace x + (r * (((Φ.signs i : ℤˣ) : ℤ) : ℝ) * k.target.mesh) • stdBasis (Φ.perm i) +
        (r' * (((Φ.signs j : ℤˣ) : ℤ) : ℝ) * k.target.mesh) • stdBasis (Φ.perm j) := by
  rw [onSpace_add_smul Φ hΦ, onSpace_add_smul Φ hΦ]
theorem coe_plaquetteCorner (x : InfiniteLattice.LatticePoint G.mesh) (i j : Fin 4) :
    ((Φ.plaquetteCorner x i j : InfiniteLattice.LatticePoint k.target.mesh) : AmbientSpace) =
      Φ.onSpace x - signDefect (Φ.signs i) • (k.target.mesh • stdBasis (Φ.perm i)) -
        signDefect (Φ.signs j) • (k.target.mesh • stdBasis (Φ.perm j)) := by
  rw [← single_eq_smul_stdBasis, ← single_eq_smul_stdBasis]
  rfl
theorem onPoint_add_axisStep (hΦ : Φ.IsDilatingBijectionOfSpace)
    (x : InfiniteLattice.LatticePoint G.mesh) (i : Fin 4) :
    Φ.onPoint (x + InfiniteLattice.axisStep G.mesh i) =
      Φ.onPoint x + ((Φ.signs i : ℤˣ) : ℤ) • InfiniteLattice.axisStep k.target.mesh (Φ.perm i) := by
  apply Subtype.ext
  have h := onSpace_add_smul Φ hΦ x 1 i
  rw [one_smul, one_mul, ← single_eq_smul_stdBasis] at h
  change Φ.onSpace ((x : AmbientSpace) + Pi.single i G.mesh) =
    Φ.onSpace x + ((Φ.signs i : ℤˣ) : ℤ) • (Pi.single (Φ.perm i) k.target.mesh : AmbientSpace)
  rw [h, single_eq_smul_stdBasis (Φ.perm i), ← Int.cast_smul_eq_zsmul ℝ, smul_smul]
end Step
theorem vertexSet_eq_of_signs {A : Type*} [AddCommGroup A] (z u v d d' : A) (s t : ℤˣ)
    (h : (s = 1 ∧ d = 0) ∨ (s = -1 ∧ d = u)) (h' : (t = 1 ∧ d' = 0) ∨ (t = -1 ∧ d' = v)) :
    ({z - d - d', z - d - d' + u, z - d - d' + u + v, z - d - d' + v} : Set A) =
      {z, z + (s : ℤ) • u, z + (s : ℤ) • u + (t : ℤ) • v, z + (t : ℤ) • v} := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [Units.val_neg, Units.val_one, neg_smul, one_smul] <;>
    (ext w
     simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
     constructor <;>
     rintro (rfl | rfl | rfl | rfl) <;>
     first
     | (left; abel1)
     | (right; left; abel1)
     | (right; right; left; abel1)
     | (right; right; right; abel1))
theorem vertexSet_comm {A : Type*} [AddCommGroup A] (y u v : A) :
    ({y, y + u, y + u + v, y + v} : Set A) = {y, y + v, y + v + u, y + u} := by
  ext w
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor <;>
  rintro (rfl | rfl | rfl | rfl) <;>
  first
  | (left; abel1)
  | (right; left; abel1)
  | (right; right; left; abel1)
  | (right; right; right; abel1)
theorem signDefect_point_cases (u : ℤˣ) (a : ℝ) (j : Fin 4) :
    (u = 1 ∧ (⟨_, signDefect_smul_axisStep_mem u a j⟩ : InfiniteLattice.LatticePoint a) = 0) ∨
      (u = -1 ∧ (⟨_, signDefect_smul_axisStep_mem u a j⟩ : InfiniteLattice.LatticePoint a) =
        InfiniteLattice.axisStep a j) := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact Or.inl ⟨rfl, Subtype.ext (by simp [signDefect])⟩
  · refine Or.inr ⟨rfl, Subtype.ext ?_⟩
    have h : signDefect (-1) = 1 := by norm_num [signDefect]
    simp only [h, one_smul]
section Plaquettes
variable {G : GluingSetup} {k : ScaleExponent G} (Φ : ScaledLatticeMotion k)
theorem vertexSet_onPlaquette (hΦ : Φ.IsDilatingBijectionOfSpace)
    (p : InfiniteLattice.ElementaryPlaquette G.mesh) :
    plaquetteVertexSet (Φ.onPlaquette p) = Φ.onPoint '' plaquetteVertexSet p := by
  obtain ⟨x, i, j, hij⟩ := p
  simp only [plaquetteVertexSet, Set.image_insert_eq, Set.image_singleton,
    onPoint_add_axisStep Φ hΦ]
  rw [← vertexSet_eq_of_signs (Φ.onPoint x) (InfiniteLattice.axisStep k.target.mesh (Φ.perm i))
    (InfiniteLattice.axisStep k.target.mesh (Φ.perm j)) _ _ (Φ.signs i) (Φ.signs j)
    (signDefect_point_cases (Φ.signs i) k.target.mesh (Φ.perm i))
    (signDefect_point_cases (Φ.signs j) k.target.mesh (Φ.perm j))]
  rcases le_total (Φ.perm i) (Φ.perm j) with h | h
  · simp only [ScaledLatticeMotion.onPlaquette, min_eq_left h, max_eq_right h]
    rfl
  · simp only [ScaledLatticeMotion.onPlaquette, min_eq_right h, max_eq_left h]
    exact vertexSet_comm _ _ _
theorem center_onPlaquette (hΦ : Φ.IsDilatingBijectionOfSpace)
    (p : InfiniteLattice.ElementaryPlaquette G.mesh) :
    (Φ.onPlaquette p).center = Φ.onSpace p.center := by
  obtain ⟨x, i, j, hij⟩ := p
  have hsrc : (InfiniteLattice.ElementaryPlaquette.mk x i j hij).center =
      (x : AmbientSpace) + (1 / 2 : ℝ) • (G.mesh • stdBasis i) +
        (1 / 2 : ℝ) • (G.mesh • stdBasis j) := by
    simp only [InfiniteLattice.ElementaryPlaquette.center, single_eq_smul_stdBasis]
    module
  rw [hsrc, onSpace_add_smul_add_smul Φ hΦ]
  rcases le_total (Φ.perm i) (Φ.perm j) with h | h
  · simp only [InfiniteLattice.ElementaryPlaquette.center, ScaledLatticeMotion.onPlaquette,
      min_eq_left h, max_eq_right h, coe_plaquetteCorner, single_eq_smul_stdBasis, signDefect]
    module
  · simp only [InfiniteLattice.ElementaryPlaquette.center, ScaledLatticeMotion.onPlaquette,
      min_eq_right h, max_eq_left h, coe_plaquetteCorner, single_eq_smul_stdBasis, signDefect]
    module
end Plaquettes
theorem transport_plaquette_eq {X Y : GluingSetup} (h : X = Y)
    (q : InfiniteLattice.ElementaryPlaquette X.mesh) (p : InfiniteLattice.ElementaryPlaquette Y.mesh)
    (hb : (q.corner : AmbientSpace) = p.corner) (hf : q.lowAxis = p.lowAxis)
    (hs : q.highAxis = p.highAxis) :
    transport (F := fun Z : GluingSetup => InfiniteLattice.ElementaryPlaquette Z.mesh) h q = p := by
  subst h
  exact InfiniteLattice.ElementaryPlaquette.ext (Subtype.ext hb) hf hs
theorem perm_signs_of_leftInverse {G : GluingSetup} {k : ScaleExponent G}
    {k' : ScaleExponent k.target} (Φ : ScaledLatticeMotion k) (Ψ : ScaledLatticeMotion k')
    (hΦ : Φ.IsDilatingBijectionOfSpace) (hΨ : Ψ.IsDilatingBijectionOfSpace)
    (ha : k'.target.mesh = G.mesh) (hinv : ∀ x, Ψ.onSpace (Φ.onSpace x) = x) (i : Fin 4) :
    Ψ.perm (Φ.perm i) = i ∧ Ψ.signs (Φ.perm i) = Φ.signs i := by
  have k₁ := onSpace_add_smul Φ hΦ 0 1 i
  have k₂ := onSpace_add_smul Ψ hΨ (Φ.onSpace 0) (((Φ.signs i : ℤˣ) : ℤ) : ℝ) (Φ.perm i)
  have harg : Φ.onSpace 0 + (((Φ.signs i : ℤˣ) : ℤ) : ℝ) • (k.target.mesh • stdBasis (Φ.perm i)) =
      Φ.onSpace 0 + (1 * (((Φ.signs i : ℤˣ) : ℤ) : ℝ) * k.target.mesh) • stdBasis (Φ.perm i) := by
    module
  rw [harg, ← k₁, hinv, hinv, ha] at k₂
  have hval := congrFun k₂ i
  have hapos := mesh_pos G
  by_cases hp : Ψ.perm (Φ.perm i) = i
  · refine ⟨hp, ?_⟩
    rw [hp] at hval
    simp only [stdBasis, Pi.add_apply, Pi.zero_apply, Pi.smul_apply, Pi.single_eq_same,
      smul_eq_mul, zero_add, one_mul, mul_one] at hval
    rcases Int.units_eq_one_or (Φ.signs i) with h₁ | h₁ <;>
      rcases Int.units_eq_one_or (Ψ.signs (Φ.perm i)) with h₂ | h₂ <;>
      rw [h₁, h₂] at hval ⊢ <;>
      (exfalso; norm_num at hval; linarith)
  · exfalso
    have hne : i ≠ Ψ.perm (Φ.perm i) := fun h => hp h.symm
    simp only [stdBasis, Pi.add_apply, Pi.zero_apply, Pi.smul_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne hne, smul_eq_mul, zero_add, one_mul, mul_one, mul_zero] at hval
    linarith
theorem onPlaquette_leftInverse
    (hS : ScaledMotionDilationOfSpaceClaim) {G G' : GluingSetup}
    {k : ScaleExponent G} {k' : ScaleExponent G'}
    (Φ : ScaledLatticeMotion k) (Ψ : ScaledLatticeMotion k') (h : k.target = G') (h' : k'.target = G)
    (hinv : ∀ x, Ψ.onSpace (Φ.onSpace x) = x) (p : InfiniteLattice.ElementaryPlaquette G.mesh) :
    transport (F := fun X : GluingSetup => InfiniteLattice.ElementaryPlaquette X.mesh) h'
      (Ψ.onPlaquette (transport (F := fun X : GluingSetup => InfiniteLattice.ElementaryPlaquette X.mesh) h
        (Φ.onPlaquette p))) = p := by
  subst h
  change transport (F := fun X : GluingSetup => InfiniteLattice.ElementaryPlaquette X.mesh) h'
    (Ψ.onPlaquette (Φ.onPlaquette p)) = p
  have ha : k'.target.mesh = G.mesh := congrArg GluingSetup.mesh h'
  have hΦ := hS _ _ Φ
  have hΨ := hS _ _ Ψ
  have hsg := perm_signs_of_leftInverse Φ Ψ hΦ hΨ ha hinv
  obtain ⟨x, i, j, hij⟩ := p
  obtain ⟨hpi, hsi⟩ := hsg i
  obtain ⟨hpj, hsj⟩ := hsg j
  have key := onSpace_add_smul_add_smul Ψ hΨ (Φ.onSpace x) (-signDefect (Φ.signs i))
    (-signDefect (Φ.signs j)) (Φ.perm i) (Φ.perm j)
  rw [hinv, hpi, hpj, hsi, hsj, ha] at key
  have harg : Φ.onSpace x - signDefect (Φ.signs i) • (k.target.mesh • stdBasis (Φ.perm i)) -
        signDefect (Φ.signs j) • (k.target.mesh • stdBasis (Φ.perm j)) =
      Φ.onSpace x + (-signDefect (Φ.signs i)) • (k.target.mesh • stdBasis (Φ.perm i)) +
        (-signDefect (Φ.signs j)) • (k.target.mesh • stdBasis (Φ.perm j)) := by
    module
  have hi := signDefect_mul_add_self (Φ.signs i)
  have hj := signDefect_mul_add_self (Φ.signs j)
  have hfin : ((x : AmbientSpace) +
        (-signDefect (Φ.signs i) * (((Φ.signs i : ℤˣ) : ℤ) : ℝ) * G.mesh) • stdBasis i +
        (-signDefect (Φ.signs j) * (((Φ.signs j : ℤˣ) : ℤ) : ℝ) * G.mesh) • stdBasis j -
        signDefect (Φ.signs i) • (G.mesh • stdBasis i) -
        signDefect (Φ.signs j) • (G.mesh • stdBasis j)) = (x : AmbientSpace) := by
    have : ((x : AmbientSpace) +
        (-signDefect (Φ.signs i) * (((Φ.signs i : ℤˣ) : ℤ) : ℝ) * G.mesh) • stdBasis i +
        (-signDefect (Φ.signs j) * (((Φ.signs j : ℤˣ) : ℤ) : ℝ) * G.mesh) • stdBasis j -
        signDefect (Φ.signs i) • (G.mesh • stdBasis i) -
        signDefect (Φ.signs j) • (G.mesh • stdBasis j)) =
      (x : AmbientSpace) +
          (-(signDefect (Φ.signs i) * (((Φ.signs i : ℤˣ) : ℤ) : ℝ) + signDefect (Φ.signs i)) *
            G.mesh) • stdBasis i +
        (-(signDefect (Φ.signs j) * (((Φ.signs j : ℤˣ) : ℤ) : ℝ) + signDefect (Φ.signs j)) *
            G.mesh) • stdBasis j := by
      module
    rw [this, hi, hj]
    simp
  have hlt := hij
  rcases le_total (Φ.perm i) (Φ.perm j) with hle | hle
  · refine transport_plaquette_eq h' _ _ ?_ ?_ ?_
    · simp only [ScaledLatticeMotion.onPlaquette, min_eq_left hle, max_eq_right hle,
        coe_plaquetteCorner, harg, key, hpi, hpj, hsi, hsj, ha]
      exact hfin
    · simp only [ScaledLatticeMotion.onPlaquette, min_eq_left hle, max_eq_right hle, hpi, hpj]
      exact min_eq_left hlt.le
    · simp only [ScaledLatticeMotion.onPlaquette, min_eq_left hle, max_eq_right hle, hpi, hpj]
      exact max_eq_right hlt.le
  · refine transport_plaquette_eq h' _ _ ?_ ?_ ?_
    · simp only [ScaledLatticeMotion.onPlaquette, min_eq_right hle, max_eq_left hle,
        coe_plaquetteCorner, harg, key, hpi, hpj, hsi, hsj, ha]
      refine Eq.trans ?_ hfin
      module
    · simp only [ScaledLatticeMotion.onPlaquette, min_eq_right hle, max_eq_left hle, hpi, hpj]
      exact min_eq_right hlt.le
    · simp only [ScaledLatticeMotion.onPlaquette, min_eq_right hle, max_eq_left hle, hpi, hpj]
      exact max_eq_left hlt.le
theorem scaledMotionPlaquettesOfSpace (hS : ScaledMotionDilationOfSpaceClaim)
    (hI : ScaledMotionInverseClaim) :
    ScaledMotionPlaquettesOfSpaceClaim := by
  intro G k Φ
  have hΦ := hS G k Φ
  have back : ∀ Ψ : ScaledLatticeMotion k.neg, Ψ.onSpace = Function.invFun Φ.onSpace →
      (∀ p, transport (F := fun X : GluingSetup => InfiniteLattice.ElementaryPlaquette X.mesh)
          k.target_neg (Ψ.onPlaquette (Φ.onPlaquette p)) = p) ∧
        ∀ p', Φ.onPlaquette (transport
          (F := fun X : GluingSetup => InfiniteLattice.ElementaryPlaquette X.mesh)
          k.target_neg (Ψ.onPlaquette p')) = p' := by
    intro Ψ hΨ
    have hl : ∀ x, Ψ.onSpace (Φ.onSpace x) = x := fun x => by
      rw [hΨ]
      exact Function.leftInverse_invFun hΦ.1.injective x
    have hr : ∀ y, Φ.onSpace (Ψ.onSpace y) = y := fun y => by
      rw [hΨ]
      exact Function.rightInverse_invFun hΦ.1.surjective y
    exact ⟨fun p => onPlaquette_leftInverse hS Φ Ψ rfl k.target_neg hl p,
      fun p' => onPlaquette_leftInverse hS Ψ Φ k.target_neg rfl hr p'⟩
  obtain ⟨Ψ, -, hΨ⟩ := (hI G k Φ).1
  obtain ⟨hl, hr⟩ := back Ψ hΨ
  refine ⟨vertexSet_onPlaquette Φ hΦ, ⟨?_, ?_⟩, back, center_onPlaquette Φ hΦ⟩
  · intro p q hpq
    rw [← hl p, ← hl q, hpq]
  · intro p'
    exact ⟨_, hr p'⟩
end YangMills.Construction.SourcesAndGluing.PlaquetteImages
end
