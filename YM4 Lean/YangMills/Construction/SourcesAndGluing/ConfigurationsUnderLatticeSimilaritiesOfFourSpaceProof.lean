import YangMills.Construction.InfiniteLattice.BondsPlaquettesCircuitsAndConfigurationsOfTheLatticeOfACutoffProof
import YangMills.Construction.InfiniteLattice.EightLoopsRoundAPlaquetteProof
import YangMills.Construction.SourcesAndGluing.ConfigurationsUnderLatticeSimilaritiesOfFourSpace
import YangMills.Construction.SourcesAndGluing.ConfigurationsUnderLatticeSimilaritiesOfToriProof
import YangMills.Construction.SourcesAndGluing.InverseOfALatticeSimilarityForm
import YangMills.Construction.SourcesAndGluing.ScalingOfLatticeSimilaritiesOfFourSpaceForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SourcesAndGluing
open Matrices
open InfiniteLattice (AmbientSpace Link LatticePoint GaugeField axisStep faceHolonomy faceEnergy
  ElementaryPlaquette)
namespace FieldsUnderScaledMotionsOfSpace
section Loops
variable {a : ℝ}
open Classical in
def edgeValue (U : Link a → ComplexMatrix2.specialUnitary) (c c' : LatticePoint a) :
    ComplexMatrix2.specialUnitary :=
  if h : ∃ μ : Fin 4, c' - c = axisStep a μ ∨ c' - c = -axisStep a μ then U ⟨c, c', h⟩ else 1
theorem edgeValue_link (U : Link a → ComplexMatrix2.specialUnitary) (b : Link a) :
    edgeValue U b.initial b.terminal = U b := by
  rw [edgeValue, dif_pos b.isAdjacent]
theorem edgeValue_symm (U : GaugeField a) (c c' : LatticePoint a) :
    edgeValue U.1 c' c = (edgeValue U.1 c c')⁻¹ := by
  by_cases h : ∃ μ : Fin 4, c' - c = axisStep a μ ∨ c' - c = -axisStep a μ
  · have hb := U.2 (⟨c, c', h⟩ : Link a)
    exact (edgeValue_link U.1 (Link.opposite ⟨c, c', h⟩)).trans
      (hb.trans (congrArg _ (edgeValue_link U.1 ⟨c, c', h⟩).symm))
  · have h' : ¬∃ μ : Fin 4, c - c' = axisStep a μ ∨ c - c' = -axisStep a μ := by
      intro hc
      exact h (Link.opposite ⟨c', c, hc⟩).isAdjacent
    simp [edgeValue, h, h']
def loopProduct (V : LatticePoint a → LatticePoint a → ComplexMatrix2.specialUnitary)
    (c₀ c₁ c₂ c₃ : LatticePoint a) : ComplexMatrix2.specialUnitary :=
  V c₀ c₁ * V c₁ c₂ * V c₂ c₃ * V c₃ c₀
def realTrace (g : ComplexMatrix2.specialUnitary) : ℝ :=
  (ComplexMatrix2.fullTrace (g : ComplexMatrix2)).re
theorem realTrace_mul_comm (g h : ComplexMatrix2.specialUnitary) :
    realTrace (g * h) = realTrace (h * g) := by apply _root_.YangMills.Construction.InfiniteLattice.PlaquetteLoops.re_fullTrace_mul_comm <;> assumption
theorem realTrace_inv (g : ComplexMatrix2.specialUnitary) : realTrace g⁻¹ = realTrace g := by apply _root_.YangMills.Construction.RefinedLatticeSymmetries.re_fullTrace_inv <;> assumption
theorem realTrace_loopProduct_rotate
    (V : LatticePoint a → LatticePoint a → ComplexMatrix2.specialUnitary)
    (c₀ c₁ c₂ c₃ : LatticePoint a) :
    realTrace (loopProduct V c₁ c₂ c₃ c₀) = realTrace (loopProduct V c₀ c₁ c₂ c₃) := by
  simp only [loopProduct]
  rw [realTrace_mul_comm]
  simp only [mul_assoc]
theorem realTrace_loopProduct_reverse (U : GaugeField a) (c₀ c₁ c₂ c₃ : LatticePoint a) :
    realTrace (loopProduct (edgeValue U.1) c₀ c₃ c₂ c₁) =
      realTrace (loopProduct (edgeValue U.1) c₀ c₁ c₂ c₃) := by
  have h : loopProduct (edgeValue U.1) c₀ c₃ c₂ c₁ =
      (loopProduct (edgeValue U.1) c₀ c₁ c₂ c₃)⁻¹ := by
    simp only [loopProduct, mul_inv_rev, mul_assoc]
    rw [edgeValue_symm U c₃ c₀, edgeValue_symm U c₂ c₃, edgeValue_symm U c₁ c₂,
      edgeValue_symm U c₀ c₁]
  rw [h, realTrace_inv]
theorem faceHolonomy_eq_loopProduct (U : GaugeField a) (p : ElementaryPlaquette a) :
    faceHolonomy U.1 p = loopProduct (edgeValue U.1) p.corner (p.corner + axisStep a p.lowAxis)
      (p.corner + axisStep a p.lowAxis + axisStep a p.highAxis)
      (p.corner + axisStep a p.highAxis) := by
  have h₀ := edgeValue_link U.1 (Link.forwardFrom p.corner p.lowAxis)
  have h₁ := edgeValue_link U.1 (Link.forwardFrom (p.corner + axisStep a p.lowAxis) p.highAxis)
  have h₂ := edgeValue_link U.1 (Link.forwardFrom (p.corner + axisStep a p.highAxis) p.lowAxis)
  have h₃ := edgeValue_link U.1 (Link.forwardFrom p.corner p.highAxis)
  simp only [Link.forwardFrom] at h₀ h₁ h₂ h₃
  simp only [faceHolonomy, loopProduct, Link.forwardFrom]
  rw [← h₀, ← h₁, ← h₂, ← h₃, ← edgeValue_symm, ← edgeValue_symm, add_right_comm]
theorem realTrace_loopProduct_from_adjacent (U : GaugeField a) (y A B : LatticePoint a) :
    realTrace (loopProduct (edgeValue U.1) (y + A) y (y + B) (y + A + B)) =
      realTrace (loopProduct (edgeValue U.1) y (y + A) (y + A + B) (y + B)) :=
  (realTrace_loopProduct_rotate _ (y + A) y (y + B) (y + A + B)).symm.trans
    (realTrace_loopProduct_reverse U y (y + A) (y + A + B) (y + B))
theorem realTrace_loopProduct_from_last (U : GaugeField a) (y A B : LatticePoint a) :
    realTrace (loopProduct (edgeValue U.1) (y + B) (y + A + B) (y + A) y) =
      realTrace (loopProduct (edgeValue U.1) y (y + A) (y + A + B) (y + B)) :=
  (realTrace_loopProduct_rotate _ y (y + B) (y + A + B) (y + A)).trans
    (realTrace_loopProduct_reverse U y (y + A) (y + A + B) (y + B))
theorem realTrace_loopProduct_from_opposite (U : GaugeField a) (y A B : LatticePoint a) :
    realTrace (loopProduct (edgeValue U.1) (y + A + B) (y + B) y (y + A)) =
      realTrace (loopProduct (edgeValue U.1) y (y + A) (y + A + B) (y + B)) :=
  (realTrace_loopProduct_rotate _ (y + A + B) (y + B) y (y + A)).symm.trans
    (realTrace_loopProduct_rotate _ (y + B) y (y + A) (y + A + B)).symm
theorem realTrace_loopProduct_of_signs (U : GaugeField a) {P c₁ c₂ c₃ y A B : LatticePoint a}
    (h : (c₁ = P + A ∧ c₂ = P + A + B ∧ c₃ = P + B ∧ y = P) ∨
      (c₁ = P - A ∧ c₂ = P - A + B ∧ c₃ = P + B ∧ y = P - A) ∨
      (c₁ = P + A ∧ c₂ = P + A - B ∧ c₃ = P - B ∧ y = P - B) ∨
      (c₁ = P - A ∧ c₂ = P - A - B ∧ c₃ = P - B ∧ y = P - A - B)) :
    realTrace (loopProduct (edgeValue U.1) P c₁ c₂ c₃) =
      realTrace (loopProduct (edgeValue U.1) y (y + A) (y + A + B) (y + B)) := by
  rcases h with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩
  · rfl
  · have h := realTrace_loopProduct_from_adjacent U (P - A) A B
    have e₁ : P - A + A = P := by abel
    simp only [e₁] at h ⊢
    exact h
  · have h := realTrace_loopProduct_from_last U (P - B) A B
    have e₁ : P - B + A + B = P + A := by abel
    have e₂ : P - B + B = P := by abel
    have e₃ : P - B + A = P + A - B := by abel
    rw [e₁, e₂, e₃] at h
    rw [e₁, e₂, e₃]
    exact h
  · have h := realTrace_loopProduct_from_opposite U (P - A - B) A B
    have e₁ : P - A - B + A + B = P := by abel
    have e₂ : P - A - B + B = P - A := by abel
    have e₃ : P - A - B + A = P - B := by abel
    rw [e₁, e₂, e₃] at h
    rw [e₁, e₂, e₃]
    exact h
end Loops
theorem transport_gridField_apply {X X' : GluingSetup} (h : X = X') (U : X.GridField)
    (c : Link X'.mesh) :
    (transport (F := fun Y : GluingSetup => Y.GridField) h U).1 c =
      U.1 (transport (F := fun Y : GluingSetup => Link Y.mesh) h.symm c) := by
  subst h
  rfl
theorem transport_initial {X X' : GluingSetup} (h : X = X') (c : Link X.mesh) :
    ((transport (F := fun Y : GluingSetup => Link Y.mesh) h c).initial : AmbientSpace) =
      c.initial := by
  subst h
  rfl
theorem transport_terminal {X X' : GluingSetup} (h : X = X') (c : Link X.mesh) :
    ((transport (F := fun Y : GluingSetup => Link Y.mesh) h c).terminal : AmbientSpace) =
      c.terminal := by
  subst h
  rfl
theorem link_eq_of_endpoints {a : ℝ} {c c' : Link a}
    (ht : (c.initial : AmbientSpace) = c'.initial)
    (hh : (c.terminal : AmbientSpace) = c'.terminal) : c = c' :=
  Link.ext (Subtype.ext ht) (Subtype.ext hh)
theorem smul_stdBasis (c : ℝ) (μ : Fin 4) : c • stdBasis μ = (Pi.single μ c : AmbientSpace) := by apply _root_.YangMills.Construction.SourcesAndGluing.FieldsUnderScaledMotionsOfTori.smul_stdBasis <;> assumption
theorem signDefect_point_of_one {ε : ℤˣ} (h : ε = 1) (a : ℝ) (ν : Fin 4) :
    (⟨_, signDefect_smul_axisStep_mem ε a ν⟩ : LatticePoint a) = 0 := by
  subst h
  exact Subtype.ext (by simp [signDefect])
theorem signDefect_point_of_neg_one {ε : ℤˣ} (h : ε = -1) (a : ℝ) (ν : Fin 4) :
    (⟨_, signDefect_smul_axisStep_mem ε a ν⟩ : LatticePoint a) = axisStep a ν := by
  subst h
  have h' : signDefect (-1) = 1 := by norm_num [signDefect]
  exact Subtype.ext (by simp only [h', one_smul])
variable {D : GluingSetup} {e : ScaleExponent D} (Φ : ScaledLatticeMotion e)
theorem onPoint_add_axisStep_of_one (hΦ : Φ.IsDilatingBijectionOfSpace) (x : LatticePoint D.mesh)
    {μ : Fin 4} (h : Φ.signs μ = 1) :
    Φ.onPoint (x + axisStep D.mesh μ) = Φ.onPoint x + axisStep e.target.mesh (Φ.perm μ) := by
  have hs := hΦ.2.2.2.1 (x : AmbientSpace) μ
  rw [smul_stdBasis, smul_stdBasis, h] at hs
  refine Subtype.ext ?_
  change Φ.onSpace ((x : AmbientSpace) + Pi.single μ D.mesh) =
    Φ.onSpace x + Pi.single (Φ.perm μ) e.target.mesh
  rw [hs]
  simp
theorem onPoint_add_axisStep_of_neg_one (hΦ : Φ.IsDilatingBijectionOfSpace)
    (x : LatticePoint D.mesh) {μ : Fin 4} (h : Φ.signs μ = -1) :
    Φ.onPoint (x + axisStep D.mesh μ) = Φ.onPoint x - axisStep e.target.mesh (Φ.perm μ) := by
  have hs := hΦ.2.2.2.1 (x : AmbientSpace) μ
  rw [smul_stdBasis, smul_stdBasis, h] at hs
  refine Subtype.ext ?_
  change Φ.onSpace ((x : AmbientSpace) + Pi.single μ D.mesh) =
    Φ.onSpace x - Pi.single (Φ.perm μ) e.target.mesh
  rw [hs, sub_eq_add_neg, ← Pi.single_neg]
  simp
theorem realTrace_loopProduct_images (hΦ : Φ.IsDilatingBijectionOfSpace)
    (U' : e.target.GridField) (x : LatticePoint D.mesh) (μ ν : Fin 4) :
    realTrace (loopProduct (edgeValue U'.1) (Φ.onPoint x) (Φ.onPoint (x + axisStep D.mesh μ))
        (Φ.onPoint (x + axisStep D.mesh μ + axisStep D.mesh ν))
        (Φ.onPoint (x + axisStep D.mesh ν))) =
      realTrace (loopProduct (edgeValue U'.1) (Φ.plaquetteCorner x μ ν)
        (Φ.plaquetteCorner x μ ν + axisStep e.target.mesh (Φ.perm μ))
        (Φ.plaquetteCorner x μ ν + axisStep e.target.mesh (Φ.perm μ) +
          axisStep e.target.mesh (Φ.perm ν))
        (Φ.plaquetteCorner x μ ν + axisStep e.target.mesh (Φ.perm ν))) := by
  apply realTrace_loopProduct_of_signs
  rcases Int.units_eq_one_or (Φ.signs μ) with hμ | hμ <;>
    rcases Int.units_eq_one_or (Φ.signs ν) with hν | hν
  · refine Or.inl ⟨onPoint_add_axisStep_of_one Φ hΦ x hμ, ?_,
      onPoint_add_axisStep_of_one Φ hΦ x hν, ?_⟩
    · rw [onPoint_add_axisStep_of_one Φ hΦ _ hν, onPoint_add_axisStep_of_one Φ hΦ x hμ]
    · simp only [ScaledLatticeMotion.plaquetteCorner, signDefect_point_of_one hμ,
        signDefect_point_of_one hν, sub_zero]
  · refine Or.inr (Or.inr (Or.inl ⟨onPoint_add_axisStep_of_one Φ hΦ x hμ, ?_,
      onPoint_add_axisStep_of_neg_one Φ hΦ x hν, ?_⟩))
    · rw [onPoint_add_axisStep_of_neg_one Φ hΦ _ hν, onPoint_add_axisStep_of_one Φ hΦ x hμ]
    · simp only [ScaledLatticeMotion.plaquetteCorner, signDefect_point_of_one hμ,
        signDefect_point_of_neg_one hν, sub_zero]
  · refine Or.inr (Or.inl ⟨onPoint_add_axisStep_of_neg_one Φ hΦ x hμ, ?_,
      onPoint_add_axisStep_of_one Φ hΦ x hν, ?_⟩)
    · rw [onPoint_add_axisStep_of_one Φ hΦ _ hν, onPoint_add_axisStep_of_neg_one Φ hΦ x hμ]
    · simp only [ScaledLatticeMotion.plaquetteCorner, signDefect_point_of_neg_one hμ,
        signDefect_point_of_one hν, sub_zero]
  · refine Or.inr (Or.inr (Or.inr ⟨onPoint_add_axisStep_of_neg_one Φ hΦ x hμ, ?_,
      onPoint_add_axisStep_of_neg_one Φ hΦ x hν, ?_⟩))
    · rw [onPoint_add_axisStep_of_neg_one Φ hΦ _ hν, onPoint_add_axisStep_of_neg_one Φ hΦ x hμ]
    · simp only [ScaledLatticeMotion.plaquetteCorner, signDefect_point_of_neg_one hμ,
        signDefect_point_of_neg_one hν]
theorem faceHolonomy_pullField (U' : e.target.GridField) (p : ElementaryPlaquette D.mesh) :
    faceHolonomy (Φ.pullField U').1 p = loopProduct (edgeValue U'.1) (Φ.onPoint p.corner)
      (Φ.onPoint (p.corner + axisStep D.mesh p.lowAxis))
      (Φ.onPoint (p.corner + axisStep D.mesh p.lowAxis + axisStep D.mesh p.highAxis))
      (Φ.onPoint (p.corner + axisStep D.mesh p.highAxis)) := by
  have h₀ := edgeValue_link U'.1 (Φ.onLink (Link.forwardFrom p.corner p.lowAxis))
  have h₁ := edgeValue_link U'.1
    (Φ.onLink (Link.forwardFrom (p.corner + axisStep D.mesh p.lowAxis) p.highAxis))
  have h₂ := edgeValue_link U'.1
    (Φ.onLink (Link.forwardFrom (p.corner + axisStep D.mesh p.highAxis) p.lowAxis))
  have h₃ := edgeValue_link U'.1 (Φ.onLink (Link.forwardFrom p.corner p.highAxis))
  change U'.1 (Φ.onLink (Link.forwardFrom p.corner p.lowAxis)) *
      U'.1 (Φ.onLink (Link.forwardFrom (p.corner + axisStep D.mesh p.lowAxis) p.highAxis)) *
      (U'.1 (Φ.onLink (Link.forwardFrom (p.corner + axisStep D.mesh p.highAxis) p.lowAxis)))⁻¹ *
      (U'.1 (Φ.onLink (Link.forwardFrom p.corner p.highAxis)))⁻¹ = _
  rw [← h₀, ← h₁, ← h₂, ← h₃]
  change edgeValue U'.1 (Φ.onPoint p.corner) (Φ.onPoint (p.corner + axisStep D.mesh p.lowAxis)) *
      edgeValue U'.1 (Φ.onPoint (p.corner + axisStep D.mesh p.lowAxis))
        (Φ.onPoint (p.corner + axisStep D.mesh p.lowAxis + axisStep D.mesh p.highAxis)) *
      (edgeValue U'.1 (Φ.onPoint (p.corner + axisStep D.mesh p.highAxis))
        (Φ.onPoint (p.corner + axisStep D.mesh p.highAxis + axisStep D.mesh p.lowAxis)))⁻¹ *
      (edgeValue U'.1 (Φ.onPoint p.corner)
        (Φ.onPoint (p.corner + axisStep D.mesh p.highAxis)))⁻¹ = _
  rw [← edgeValue_symm, ← edgeValue_symm, add_right_comm]
  rfl
theorem faceEnergy_pullField (hΦ : Φ.IsDilatingBijectionOfSpace)
    (U' : e.target.GridField) (p : ElementaryPlaquette D.mesh) :
    faceEnergy (Φ.pullField U').1 p = faceEnergy U'.1 (Φ.onPlaquette p) := by
  have key : realTrace (faceHolonomy (Φ.pullField U').1 p) =
      realTrace (faceHolonomy U'.1 (Φ.onPlaquette p)) := by
    rw [faceHolonomy_pullField, faceHolonomy_eq_loopProduct, realTrace_loopProduct_images Φ hΦ]
    have hcorner : (Φ.onPlaquette p).corner = Φ.plaquetteCorner p.corner p.lowAxis p.highAxis :=
      rfl
    rw [hcorner]
    rcases lt_or_gt_of_ne (Φ.perm.injective.ne p.lowAxis_lt_highAxis.ne) with h | h
    · have h₁ : (Φ.onPlaquette p).lowAxis = Φ.perm p.lowAxis := min_eq_left h.le
      have h₂ : (Φ.onPlaquette p).highAxis = Φ.perm p.highAxis := max_eq_right h.le
      rw [h₁, h₂]
    · have h₁ : (Φ.onPlaquette p).lowAxis = Φ.perm p.highAxis := min_eq_right h.le
      have h₂ : (Φ.onPlaquette p).highAxis = Φ.perm p.lowAxis := max_eq_left h.le
      rw [h₁, h₂]
      have hr := realTrace_loopProduct_reverse U'
        (Φ.plaquetteCorner p.corner p.lowAxis p.highAxis)
        (Φ.plaquetteCorner p.corner p.lowAxis p.highAxis +
          axisStep e.target.mesh (Φ.perm p.lowAxis))
        (Φ.plaquetteCorner p.corner p.lowAxis p.highAxis +
          axisStep e.target.mesh (Φ.perm p.lowAxis) + axisStep e.target.mesh (Φ.perm p.highAxis))
        (Φ.plaquetteCorner p.corner p.lowAxis p.highAxis +
          axisStep e.target.mesh (Φ.perm p.highAxis))
      rw [add_right_comm (Φ.plaquetteCorner p.corner p.lowAxis p.highAxis)
        (axisStep e.target.mesh (Φ.perm p.highAxis)) (axisStep e.target.mesh (Φ.perm p.lowAxis))]
      exact hr.symm
  have h : ∀ (a : ℝ) (U : Link a → ComplexMatrix2.specialUnitary) (q : ElementaryPlaquette a),
      faceEnergy U q = 1 - (1 / 2) * realTrace (faceHolonomy U q) := fun _ _ _ => rfl
  rw [h, h, key]
theorem continuous_pullField : Continuous Φ.pullField := by
  have h : Continuous fun U' : e.target.GridField =>
      (fun c => U'.1 (Φ.onLink c) : Link D.mesh → ComplexMatrix2.specialUnitary) :=
    continuous_pi fun c => (continuous_apply _).comp continuous_subtype_val
  exact h.subtype_mk _
theorem pullField_pullField (Ψ : ScaledLatticeMotion e.neg)
    (h : ∀ x, Ψ.onSpace (Φ.onSpace x) = x) (U : D.GridField) :
    Φ.pullField (Ψ.pullField
      (transport (F := fun X : GluingSetup => X.GridField) e.target_neg.symm U)) = U := by
  refine Subtype.ext (funext fun c => ?_)
  change (transport (F := fun X : GluingSetup => X.GridField) e.target_neg.symm U).1
    (Ψ.onLink (Φ.onLink c)) = U.1 c
  rw [transport_gridField_apply]
  refine congrArg U.1 (link_eq_of_endpoints ?_ ?_)
  · rw [transport_initial]
    exact h _
  · rw [transport_terminal]
    exact h _
theorem pullField_transport_pullField (Ψ : ScaledLatticeMotion e.neg)
    (h : ∀ y, Φ.onSpace (Ψ.onSpace y) = y) (U' : e.target.GridField) :
    Ψ.pullField (transport (F := fun X : GluingSetup => X.GridField) e.target_neg.symm
      (Φ.pullField U')) = U' := by
  refine Subtype.ext (funext fun c => ?_)
  change (transport (F := fun X : GluingSetup => X.GridField) e.target_neg.symm
    (Φ.pullField U')).1 (Ψ.onLink c) = U'.1 c
  rw [transport_gridField_apply]
  change U'.1 (Φ.onLink _) = U'.1 c
  refine congrArg U'.1 (link_eq_of_endpoints ?_ ?_)
  · change Φ.onSpace _ = _
    rw [transport_initial]
    exact h _
  · change Φ.onSpace _ = _
    rw [transport_terminal]
    exact h _
theorem pullField_comp {e₂ : ScaleExponent e.target} (Φ₂ : ScaledLatticeMotion e₂)
    (Φ₃ : ScaledLatticeMotion (e.add e₂)) (h : Φ₃.onSpace = Φ₂.onSpace ∘ Φ.onSpace)
    (U'' : e₂.target.GridField) :
    Φ₃.pullField (transport (F := fun X : GluingSetup => X.GridField) (e.target_add e₂) U'') =
      Φ.pullField (Φ₂.pullField U'') := by
  refine Subtype.ext (funext fun c => ?_)
  change (transport (F := fun X : GluingSetup => X.GridField) (e.target_add e₂) U'').1
    (Φ₃.onLink c) = U''.1 (Φ₂.onLink (Φ.onLink c))
  rw [transport_gridField_apply]
  refine congrArg U''.1 (link_eq_of_endpoints ?_ ?_)
  · rw [transport_initial]
    exact congrFun h _
  · rw [transport_terminal]
    exact congrFun h _
theorem holds (hs : ScaledMotionDilationOfSpaceClaim) (hi : ScaledMotionInverseClaim) :
    FieldsUnderScaledMotionsOfSpace.Statement := by
  intro D e Φ
  have hΦ := hs D e Φ
  have hb : Function.Bijective Φ.onSpace := hΦ.1
  have hleft : ∀ Ψ : ScaledLatticeMotion e.neg, Ψ.onSpace = Function.invFun Φ.onSpace →
      ∀ x, Ψ.onSpace (Φ.onSpace x) = x := fun Ψ hΨ x => by
    rw [hΨ]
    exact Function.leftInverse_invFun hb.1 x
  have hright : ∀ Ψ : ScaledLatticeMotion e.neg, Ψ.onSpace = Function.invFun Φ.onSpace →
      ∀ y, Φ.onSpace (Ψ.onSpace y) = y := fun Ψ hΨ y => by
    rw [hΨ]
    exact Function.rightInverse_invFun hb.2 y
  obtain ⟨Ψ₀, -, hΨ₀⟩ := (hi D e Φ).1
  refine ⟨⟨?_, ?_⟩, continuous_pullField Φ, fun Ψ hΨ => ⟨pullField_pullField Φ Ψ (hleft Ψ hΨ),
    pullField_transport_pullField Φ Ψ (hright Ψ hΨ)⟩, fun e₂ Φ₂ Φ₃ h U'' =>
    pullField_comp Φ Φ₂ Φ₃ h U'', fun p U' => faceEnergy_pullField Φ hΦ U' p⟩
  · intro U₁ U₂ h
    have hp := pullField_transport_pullField Φ Ψ₀ (hright Ψ₀ hΨ₀)
    rw [← hp U₁, ← hp U₂, h]
  · exact fun U => ⟨_, pullField_pullField Φ Ψ₀ (hleft Ψ₀ hΨ₀) U⟩
end FieldsUnderScaledMotionsOfSpace
end YangMills.Construction.SourcesAndGluing
end
