import YangMills.Construction.Lattice.HolonomyUnderReordering
import YangMills.Construction.PeriodicLattice.PathRearrangementProof
import Mathlib
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice.HolonomyUnderReordering
variable {L m : ℕ} {j : ℤ}
theorem mul_inv_cancel_of_mem {A : Matrices.ComplexMatrix2} (hA : A ∈ compactGaugeGroup) :
    A * A⁻¹ = 1 := by apply _root_.YangMills.SharedProofs.p16098 <;> assumption
theorem inv_mul_cancel_of_mem {A : Matrices.ComplexMatrix2} (hA : A ∈ compactGaugeGroup) :
    A⁻¹ * A = 1 := by apply _root_.YangMills.SharedProofs.p14555 <;> assumption
theorem inv_inv_of_mem {A : Matrices.ComplexMatrix2} (hA : A ∈ compactGaugeGroup) :
    (A⁻¹)⁻¹ = A := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_inv_of_mem_compactGaugeGroup <;> assumption
theorem mul_mem_of_mem {A B : Matrices.ComplexMatrix2} (hA : A ∈ compactGaugeGroup)
    (hB : B ∈ compactGaugeGroup) : A * B ∈ compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.mul_mem_of_mem <;> assumption
theorem inv_mem_of_mem {A : Matrices.ComplexMatrix2} (hA : A ∈ compactGaugeGroup) :
    A⁻¹ ∈ compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
theorem mem_unitary_of_mem {A : Matrices.ComplexMatrix2} (hA : A ∈ compactGaugeGroup) :
    A ∈ unitary Matrices.ComplexMatrix2 :=
  (Matrix.mem_specialUnitaryGroup_iff.1 hA).1
theorem norm_inv_sub_one_of_mem {W : Matrices.ComplexMatrix2} (hW : W ∈ compactGaugeGroup) :
    ‖W⁻¹ - 1‖ = ‖W - 1‖ := by
  have e : W⁻¹ - 1 = W⁻¹ * (1 - W) := by rw [mul_sub, mul_one, inv_mul_cancel_of_mem hW]
  rw [e, CStarRing.norm_mem_unitary_mul _ (mem_unitary_of_mem (inv_mem_of_mem hW)), norm_sub_rev]
theorem norm_conj_sub_one_of_mem {T W : Matrices.ComplexMatrix2} (hT : T ∈ compactGaugeGroup) :
    ‖T * W * T⁻¹ - 1‖ = ‖W - 1‖ := by
  have e : T * W * T⁻¹ - 1 = T * ((W - 1) * T⁻¹) := by
    rw [sub_mul, one_mul, mul_sub, mul_inv_cancel_of_mem hT, mul_assoc]
  rw [e, CStarRing.norm_mem_unitary_mul _ (mem_unitary_of_mem hT),
    CStarRing.norm_mul_mem_unitary _ (mem_unitary_of_mem (inv_mem_of_mem hT))]
theorem norm_mul_inv_sub_one_le {A B C : Matrices.ComplexMatrix2} (hA : A ∈ compactGaugeGroup)
    {x y : ℝ} (hx : ‖A * B⁻¹ - 1‖ ≤ x) (hy : ‖C * A⁻¹ - 1‖ ≤ y) :
    ‖C * B⁻¹ - 1‖ ≤ (1 + x) * (1 + y) - 1 := by
  set X := A * B⁻¹ - 1 with hX
  set Y := C * A⁻¹ - 1 with hY
  have e : C * B⁻¹ - 1 = Y + X + Y * X := by
    have : C * B⁻¹ = (C * A⁻¹) * (A * B⁻¹) := by
      rw [mul_assoc, ← mul_assoc A⁻¹, inv_mul_cancel_of_mem hA, one_mul]
    rw [this, hX, hY]
    noncomm_ring
  have h1 : ‖Y * X‖ ≤ ‖Y‖ * ‖X‖ := norm_mul_le _ _
  have h2 : ‖Y‖ * ‖X‖ ≤ y * x :=
    mul_le_mul hy hx (norm_nonneg _) ((norm_nonneg _).trans hy)
  have h3 : ‖Y + X + Y * X‖ ≤ ‖Y‖ + ‖X‖ + ‖Y * X‖ :=
    (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
  rw [e]
  nlinarith
def axisUnitStep (L m : ℕ) (j : ℤ) (μ : Fin 4) : UnitStepVec L m j :=
  ⟨unitStep L m j μ, μ, Or.inl rfl⟩
def negUnitStep (a : UnitStepVec L m j) : UnitStepVec L m j :=
  ⟨-(a : Site L m j), by
    obtain ⟨μ, h | h⟩ := a.2
    · exact ⟨μ, Or.inr (by rw [h])⟩
    · exact ⟨μ, Or.inl (by rw [h, neg_neg])⟩⟩
@[simp] theorem coe_negUnitStep (a : UnitStepVec L m j) :
    ((negUnitStep a : UnitStepVec L m j) : Site L m j) = -(a : Site L m j) := rfl
def IsAlongAxis (a : UnitStepVec L m j) (μ : Fin 4) : Prop :=
  (a : Site L m j) = unitStep L m j μ ∨ (a : Site L m j) = -unitStep L m j μ
theorem IsAlongAxis.neg {a : UnitStepVec L m j} {μ : Fin 4} (h : IsAlongAxis a μ) :
    IsAlongAxis (negUnitStep a) μ := by
  rcases h with h | h
  · exact Or.inr (by rw [coe_negUnitStep, h])
  · exact Or.inl (by rw [coe_negUnitStep, h, neg_neg])
theorem unitStep_coord_self_ne_zero (hL : 1 ≤ L) (hj : -(m : ℤ) ≤ j) (μ : Fin 4) :
    ((unitStep L m j μ : Site L m j) : FourTorus L m) μ ≠ 0 := by apply _root_.YangMills.Construction.PeriodicLattice.PathRearrangementProof.unitStep_apply_self_ne_zero <;> assumption
theorem unitStep_coord_of_ne (μ ν : Fin 4) (h : ν ≠ μ) :
    ((unitStep L m j μ : Site L m j) : FourTorus L m) ν = 0 := by
  simp [unitStep, pointOnAxis, Pi.single_eq_of_ne h]
theorem IsAlongAxis.coord_ne_zero {a : UnitStepVec L m j} {μ : Fin 4} (h : IsAlongAxis a μ)
    (hL : 1 ≤ L) (hj : -(m : ℤ) ≤ j) : (((a : Site L m j) : FourTorus L m)) μ ≠ 0 := by
  rcases h with h | h
  · rw [h]; exact unitStep_coord_self_ne_zero hL hj μ
  · rw [h]
    simpa using unitStep_coord_self_ne_zero (j := j) hL hj μ
theorem IsAlongAxis.coord_eq_zero {a : UnitStepVec L m j} {μ ν : Fin 4} (h : IsAlongAxis a μ)
    (hν : ν ≠ μ) : (((a : Site L m j) : FourTorus L m)) ν = 0 := by
  rcases h with h | h
  · rw [h]; exact unitStep_coord_of_ne μ ν hν
  · rw [h]
    simpa using unitStep_coord_of_ne (L := L) (m := m) (j := j) μ ν hν
theorem unitStep_eq_of_mem_square {y : Site L m j} {a b : UnitStepVec L m j} {μ ν κ : Fin 4}
    (ha : IsAlongAxis a μ) (hb : IsAlongAxis b ν) (hμν : μ ≠ ν) (hL : 1 ≤ L)
    (hj : -(m : ℤ) ≤ j)
    (h : y + unitStep L m j κ ∈
      ({y, y + a, y + b, y + a + b} : Set (Site L m j))) :
    unitStep L m j κ = a ∨ unitStep L m j κ = b := by
  simp only [mem_insert_iff, mem_singleton_iff] at h
  rcases h with h | h | h | h
  · exfalso
    have h0 : unitStep L m j κ = 0 := by simpa using h
    exact unitStep_coord_self_ne_zero hL hj κ (by rw [h0]; rfl)
  · exact Or.inl (add_left_cancel h)
  · exact Or.inr (add_left_cancel h)
  · exfalso
    have h1 : unitStep L m j κ = (a : Site L m j) + b := by
      rw [add_assoc] at h; exact add_left_cancel h
    have hc : ∀ ρ, ((unitStep L m j κ : Site L m j) : FourTorus L m) ρ =
        (((a : Site L m j) : FourTorus L m)) ρ + (((b : Site L m j) : FourTorus L m)) ρ := by
      intro ρ; rw [h1]; rfl
    by_cases hκ : κ = μ
    · have := hc ν
      rw [unitStep_coord_of_ne κ ν (by rw [hκ]; exact hμν.symm), ha.coord_eq_zero hμν.symm,
        zero_add] at this
      exact hb.coord_ne_zero hL hj this.symm
    · have := hc μ
      rw [unitStep_coord_of_ne κ μ (Ne.symm hκ), hb.coord_eq_zero hμν, add_zero] at this
      exact ha.coord_ne_zero hL hj this.symm
section Square
variable {U : Bond L m j → Matrices.ComplexMatrix2}
theorem value_mem (hc : U ∈ compactGaugeFields L m j) (b : Bond L m j) :
    U b ∈ compactGaugeGroup :=
  (show IsGaugeField compactGaugeGroup univ U from hc).1 b (mem_univ b)
theorem value_opposite (hc : U ∈ compactGaugeFields L m j) (b : Bond L m j) :
    U b.opposite = (U b)⁻¹ :=
  (show IsGaugeField compactGaugeGroup univ U from hc).2 b (mem_univ b)
abbrev bondValue (U : Bond L m j → Matrices.ComplexMatrix2) (y : Site L m j)
    (a : UnitStepVec L m j) : Matrices.ComplexMatrix2 :=
  U (bondOfStep y a)
def squareHolonomy (U : Bond L m j → Matrices.ComplexMatrix2) (y : Site L m j)
    (a b : UnitStepVec L m j) : Matrices.ComplexMatrix2 :=
  bondValue U y a * bondValue U (y + (a : Site L m j)) b *
    (bondValue U (y + (b : Site L m j)) a)⁻¹ * (bondValue U y b)⁻¹
theorem bondOfStep_negUnitStep (y : Site L m j) (a : UnitStepVec L m j) :
    bondOfStep (y + (a : Site L m j)) (negUnitStep a) = (bondOfStep y a).opposite :=
  Bond.ext rfl (by simp [bondOfStep, Bond.opposite])
theorem add_add_negUnitStep (y : Site L m j) (a : UnitStepVec L m j) :
    y + (a : Site L m j) + ((negUnitStep a : UnitStepVec L m j) : Site L m j) = y := by
  simp
theorem squareHolonomy_comm (hc : U ∈ compactGaugeFields L m j) (y : Site L m j)
    (a b : UnitStepVec L m j) : squareHolonomy U y a b = (squareHolonomy U y b a)⁻¹ := by
  simp only [squareHolonomy, Matrix.mul_inv_rev, inv_inv_of_mem (value_mem hc _), mul_assoc]
theorem squareHolonomy_mem (hc : U ∈ compactGaugeFields L m j) (y : Site L m j)
    (a b : UnitStepVec L m j) : squareHolonomy U y a b ∈ compactGaugeGroup :=
  mul_mem_of_mem (mul_mem_of_mem (mul_mem_of_mem (value_mem hc _) (value_mem hc _))
    (inv_mem_of_mem (value_mem hc _))) (inv_mem_of_mem (value_mem hc _))
theorem squareHolonomy_eq_conj (hc : U ∈ compactGaugeFields L m j) (y : Site L m j)
    (a b : UnitStepVec L m j) :
    squareHolonomy U y a b =
      bondValue U y a * squareHolonomy U (y + (a : Site L m j)) b (negUnitStep a) *
        (bondValue U y a)⁻¹ := by
  have e1 : bondValue U (y + (a : Site L m j) + (b : Site L m j)) (negUnitStep a) =
      (bondValue U (y + (b : Site L m j)) a)⁻¹ := by
    rw [bondValue, add_right_comm y (a : Site L m j) (b : Site L m j), bondOfStep_negUnitStep]
    exact value_opposite hc _
  have e2 : bondValue U (y + (a : Site L m j)) (negUnitStep a) = (bondValue U y a)⁻¹ := by
    rw [bondValue, bondOfStep_negUnitStep]
    exact value_opposite hc _
  have e3 : bondValue U (y + (a : Site L m j) + ((negUnitStep a : UnitStepVec L m j) : Site L m j)) b =
      bondValue U y b := by
    rw [add_add_negUnitStep]
  have hA := mul_inv_cancel_of_mem (value_mem hc (bondOfStep y a))
  simp only [squareHolonomy, e1, e2, e3, inv_inv_of_mem (value_mem hc (bondOfStep y a)), mul_assoc]
  rw [hA, mul_one]
def SquareDistance (U : Bond L m j → Matrices.ComplexMatrix2) (w : ℝ) (y : Site L m j)
    (a b : UnitStepVec L m j) : Prop :=
  ‖squareHolonomy U y a b - 1‖ = w
theorem SquareDistance.swap (hc : U ∈ compactGaugeFields L m j) {w : ℝ} {y : Site L m j}
    {a b : UnitStepVec L m j} (h : SquareDistance U w y a b) : SquareDistance U w y b a := by
  rw [SquareDistance, squareHolonomy_comm hc y b a, norm_inv_sub_one_of_mem (squareHolonomy_mem hc _ _ _)]
  exact h
theorem SquareDistance.rotate (hc : U ∈ compactGaugeFields L m j) {w : ℝ} {y : Site L m j}
    {a b : UnitStepVec L m j} (h : SquareDistance U w y a b) :
    SquareDistance U w (y + (a : Site L m j)) b (negUnitStep a) := by
  have e := norm_conj_sub_one_of_mem (W := squareHolonomy U (y + (a : Site L m j)) b (negUnitStep a))
    (value_mem hc (bondOfStep y a))
  rw [← squareHolonomy_eq_conj hc] at e
  rw [SquareDistance, ← e]
  exact h
theorem plaquetteHolonomy_eq_squareHolonomy (hc : U ∈ compactGaugeFields L m j)
    (p : Plaquette L m j) :
    plaquetteHolonomy U p =
      squareHolonomy U p.origin (axisUnitStep L m j p.firstAxis) (axisUnitStep L m j p.secondAxis) := by
  have e1 : U (Bond.forwardFrom (p.origin + unitStep L m j p.secondAxis) p.firstAxis).opposite =
      (U (Bond.forwardFrom (p.origin + unitStep L m j p.secondAxis) p.firstAxis))⁻¹ :=
    value_opposite hc _
  have e2 : U (Bond.forwardFrom p.origin p.secondAxis).opposite =
      (U (Bond.forwardFrom p.origin p.secondAxis))⁻¹ :=
    value_opposite hc _
  simp only [plaquetteHolonomy, pathHolonomy, Plaquette.boundaryBonds, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, e1, e2]
  simp only [squareHolonomy, mul_assoc]
  rfl
theorem SquareDistance.plaquette_norm (hc : U ∈ compactGaugeFields L m j) (hL : 1 ≤ L)
    (hj : -(m : ℤ) ≤ j) {w : ℝ} {a b : UnitStepVec L m j} {μ ν : Fin 4} {p : Plaquette L m j}
    (h : SquareDistance U w p.origin a b) (ha : IsAlongAxis a μ) (hb : IsAlongAxis b ν)
    (hμν : μ ≠ ν)
    (hcorners : p.vertices ⊆
      ({p.origin, p.origin + a, p.origin + b, p.origin + a + b} : Set (Site L m j))) :
    ‖plaquetteHolonomy U p - 1‖ = w := by
  have hne : unitStep L m j p.firstAxis ≠ unitStep L m j p.secondAxis := by
    intro he
    have h1 := unitStep_coord_self_ne_zero (j := j) hL hj p.firstAxis
    rw [he, unitStep_coord_of_ne p.secondAxis p.firstAxis p.4.ne] at h1
    exact h1 rfl
  have hf := unitStep_eq_of_mem_square (κ := p.firstAxis) ha hb hμν hL hj
    (hcorners (by simp [Plaquette.vertices]))
  have hg := unitStep_eq_of_mem_square (κ := p.secondAxis) ha hb hμν hL hj
    (hcorners (by simp [Plaquette.vertices]))
  have hfg : SquareDistance U w p.origin (axisUnitStep L m j p.firstAxis)
      (axisUnitStep L m j p.secondAxis) := by
    rcases hf with hf | hf <;> rcases hg with hg | hg
    · exact absurd (hf.trans hg.symm) hne
    · have e1 : axisUnitStep L m j p.firstAxis = a := Subtype.ext hf
      have e2 : axisUnitStep L m j p.secondAxis = b := Subtype.ext hg
      rw [e1, e2]; exact h
    · have e1 : axisUnitStep L m j p.firstAxis = b := Subtype.ext hf
      have e2 : axisUnitStep L m j p.secondAxis = a := Subtype.ext hg
      rw [e1, e2]; exact h.swap hc
    · exact absurd (hf.trans hg.symm) hne
  rw [plaquetteHolonomy_eq_squareHolonomy hc p]
  exact hfg
theorem norm_plaquetteHolonomy_sub_one_eq (hc : U ∈ compactGaugeFields L m j)
    (hL : 1 ≤ L) (hj : -(m : ℤ) ≤ j) {c : Site L m j} {s s' : UnitStepVec L m j} {μ ν : Fin 4}
    (hs : IsAlongAxis s μ) (hs' : IsAlongAxis s' ν) (hμν : μ ≠ ν)
    {p : Plaquette L m j}
    (hp : p.vertices = ({c, c + s, c + s', c + s + s'} : Set (Site L m j))) :
    ‖plaquetteHolonomy U p - 1‖ = ‖squareHolonomy U c s s' - 1‖ := by
  have R0 : SquareDistance U ‖squareHolonomy U c s s' - 1‖ c s s' := rfl
  have R1 := R0.rotate hc
  have R2 := R1.rotate hc
  have R3 := R2.rotate hc
  have e3 : c + (s : Site L m j) + s' + ((negUnitStep s : UnitStepVec L m j) : Site L m j) =
      c + s' := by
    rw [coe_negUnitStep]; abel
  rw [e3] at R3
  have hbase : p.origin ∈ p.vertices := by simp [Plaquette.vertices]
  rw [hp] at hbase
  simp only [mem_insert_iff, mem_singleton_iff] at hbase
  rcases hbase with hb | hb | hb | hb
  · have R0' : SquareDistance U ‖squareHolonomy U c s s' - 1‖ p.origin s s' := by rw [hb]; exact R0
    refine R0'.plaquette_norm hc hL hj hs hs' hμν ?_
    intro y hy
    rw [hp] at hy
    rw [hb]
    exact hy
  · rw [← hb] at R1
    refine R1.plaquette_norm hc hL hj hs' hs.neg hμν.symm ?_
    rw [hp, hb]
    intro y hy
    simp only [mem_insert_iff, mem_singleton_iff, coe_negUnitStep] at hy ⊢
    have e1 : c + (s : Site L m j) + -(s : Site L m j) = c := by abel
    have e2 : c + (s : Site L m j) + s' + -(s : Site L m j) = c + s' := by abel
    rw [e1, e2]
    tauto
  · rw [← hb] at R3
    refine R3.plaquette_norm hc hL hj hs'.neg hs.neg.neg hμν.symm ?_
    rw [hp, hb]
    intro y hy
    simp only [mem_insert_iff, mem_singleton_iff, coe_negUnitStep, neg_neg] at hy ⊢
    have e1 : c + (s' : Site L m j) + -(s' : Site L m j) = c := by abel
    have e2 : c + (s' : Site L m j) + -(s' : Site L m j) + s = c + s := by abel
    have e3 : c + (s' : Site L m j) + s = c + s + s' := by abel
    rw [e2, e1, e3]
    tauto
  · rw [← hb] at R2
    refine R2.plaquette_norm hc hL hj hs.neg hs'.neg hμν ?_
    rw [hp, hb]
    intro y hy
    simp only [mem_insert_iff, mem_singleton_iff, coe_negUnitStep] at hy ⊢
    have e1 : c + (s : Site L m j) + s' + -(s : Site L m j) = c + s' := by abel
    have e2 : c + (s : Site L m j) + s' + -(s' : Site L m j) = c + s := by abel
    have e3 : c + (s : Site L m j) + s' + -(s : Site L m j) + -(s' : Site L m j) = c := by abel
    rw [e3, e1, e2]
    tauto
end Square
theorem exists_plaquette_vertices_of_lt {κ κ' : Fin 4} (hκ : κ < κ') (c : Site L m j)
    {a b : UnitStepVec L m j} (ha : IsAlongAxis a κ) (hb : IsAlongAxis b κ') :
    ∃ p : Plaquette L m j, p.vertices = ({c, c + a, c + b, c + a + b} : Set (Site L m j)) := by
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · refine ⟨⟨c, κ, κ', hκ⟩, ?_⟩
    ext y
    simp only [Plaquette.vertices, mem_insert_iff, mem_singleton_iff, ha, hb]
    tauto
  · refine ⟨⟨c + -unitStep L m j κ', κ, κ', hκ⟩, ?_⟩
    ext y
    have e2 : c + unitStep L m j κ + -unitStep L m j κ' + unitStep L m j κ' =
        c + unitStep L m j κ := by abel
    have e1 : c + -unitStep L m j κ' + unitStep L m j κ =
        c + unitStep L m j κ + -unitStep L m j κ' := by abel
    have e3 : c + -unitStep L m j κ' + unitStep L m j κ' = c := by abel
    simp only [Plaquette.vertices, mem_insert_iff, mem_singleton_iff, ha, hb, e2, e1, e3]
    tauto
  · refine ⟨⟨c + -unitStep L m j κ, κ, κ', hκ⟩, ?_⟩
    ext y
    have e1 : c + -unitStep L m j κ + unitStep L m j κ = c := by abel
    simp only [Plaquette.vertices, mem_insert_iff, mem_singleton_iff, ha, hb, e1]
    tauto
  · refine ⟨⟨c + -unitStep L m j κ + -unitStep L m j κ', κ, κ', hκ⟩, ?_⟩
    ext y
    have e2 : c + -unitStep L m j κ' + unitStep L m j κ' = c := by abel
    have e1 : c + -unitStep L m j κ + -unitStep L m j κ' + unitStep L m j κ =
        c + -unitStep L m j κ' := by abel
    have e3 : c + -unitStep L m j κ + -unitStep L m j κ' + unitStep L m j κ' =
        c + -unitStep L m j κ := by abel
    simp only [Plaquette.vertices, mem_insert_iff, mem_singleton_iff, ha, hb, e2, e1, e3]
    tauto
theorem exists_plaquette_vertices {μ ν : Fin 4} (hμν : μ ≠ ν) (c : Site L m j)
    {a b : UnitStepVec L m j} (ha : IsAlongAxis a μ) (hb : IsAlongAxis b ν) :
    ∃ p : Plaquette L m j, p.vertices = ({c, c + a, c + b, c + a + b} : Set (Site L m j)) := by
  rcases lt_or_gt_of_ne hμν with h | h
  · exact exists_plaquette_vertices_of_lt h c ha hb
  · obtain ⟨p, hp⟩ := exists_plaquette_vertices_of_lt h c hb ha
    refine ⟨p, ?_⟩
    rw [hp, add_right_comm c (b : Site L m j) (a : Site L m j)]
    ext y
    simp only [mem_insert_iff, mem_singleton_iff]
    tauto
theorem exists_axes_of_not_parallel {a b : UnitStepVec L m j}
    (hn : ¬ ((b : Site L m j) = a ∨ (b : Site L m j) = -(a : Site L m j))) :
    ∃ μ ν : Fin 4, IsAlongAxis a μ ∧ IsAlongAxis b ν ∧ μ ≠ ν := by
  obtain ⟨μ, h1⟩ := a.2
  obtain ⟨ν, h2⟩ := b.2
  refine ⟨μ, ν, h1, h2, ?_⟩
  rintro rfl
  apply hn
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact Or.inl (h2.trans h1.symm)
  · exact Or.inr (by rw [h1, h2])
  · exact Or.inr (by rw [h1, h2, neg_neg])
  · exact Or.inl (h2.trans h1.symm)
def wordSum (𝔲 : StepWord L m j) : Site L m j :=
  (𝔲.map fun s : UnitStepVec L m j => (s : Site L m j)).sum
theorem wordSum_nil : wordSum ([] : StepWord L m j) = 0 := by
  simp [wordSum]
theorem wordSum_append (𝔲 𝔳 : StepWord L m j) :
    wordSum (𝔲 ++ 𝔳) = wordSum 𝔲 + wordSum 𝔳 := by
  simp [wordSum]
theorem wordSum_cons (s : UnitStepVec L m j) (𝔲 : StepWord L m j) :
    wordSum (s :: 𝔲) = (s : Site L m j) + wordSum 𝔲 := by
  simp [wordSum]
theorem pathOfWord_append (z : Site L m j) (u v : StepWord L m j) :
    pathOfWord z (u ++ v) = pathOfWord z u ++ pathOfWord (z + wordSum u) v := by
  induction u generalizing z with
  | nil => simp [pathOfWord, wordSum]
  | cons s u ih => simp [pathOfWord, ih, wordSum_cons, add_assoc]
theorem pathHolonomy_append (U : Bond L m j → Matrices.ComplexMatrix2) (Γ Γ' : List (Bond L m j)) :
    pathHolonomy U (Γ ++ Γ') = pathHolonomy U Γ * pathHolonomy U Γ' := by
  simp [pathHolonomy]
theorem pathHolonomy_cons (U : Bond L m j → Matrices.ComplexMatrix2) (b : Bond L m j)
    (Γ : List (Bond L m j)) : pathHolonomy U (b :: Γ) = U b * pathHolonomy U Γ := by
  simp [pathHolonomy]
section Swap
variable {U : Bond L m j → Matrices.ComplexMatrix2}
theorem pathHolonomy_mem (hc : U ∈ compactGaugeFields L m j) (Γ : List (Bond L m j)) :
    pathHolonomy U Γ ∈ compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.pathHolonomy_mem_compactGaugeGroup <;> assumption
theorem wordHolonomy_split (U : Bond L m j → Matrices.ComplexMatrix2) (z : Site L m j)
    (𝔲 𝔳 : StepWord L m j) (a b : UnitStepVec L m j) :
    wordHolonomy U z (𝔲 ++ a :: b :: 𝔳) = pathHolonomy U (pathOfWord z 𝔲) *
      (bondValue U (z + wordSum 𝔲) a * (bondValue U (z + wordSum 𝔲 + (a : Site L m j)) b *
        pathHolonomy U (pathOfWord (z + wordSum 𝔲 + (a : Site L m j) + (b : Site L m j)) 𝔳))) := by
  rw [wordHolonomy, pathOfWord_append, pathHolonomy_append]
  simp only [pathOfWord, pathHolonomy_cons]
theorem wordHolonomy_swap_ratio (hc : U ∈ compactGaugeFields L m j) (z : Site L m j)
    (𝔲 𝔳 : StepWord L m j) (a b : UnitStepVec L m j) :
    wordHolonomy U z (𝔲 ++ a :: b :: 𝔳) * (wordHolonomy U z (𝔲 ++ b :: a :: 𝔳))⁻¹ =
      pathHolonomy U (pathOfWord z 𝔲) * squareHolonomy U (z + wordSum 𝔲) a b *
        (pathHolonomy U (pathOfWord z 𝔲))⁻¹ := by
  have hV := mul_inv_cancel_of_mem (pathHolonomy_mem hc
    (pathOfWord (z + wordSum 𝔲 + (a : Site L m j) + (b : Site L m j)) 𝔳))
  rw [wordHolonomy_split, wordHolonomy_split,
    add_right_comm (z + wordSum 𝔲) (b : Site L m j) (a : Site L m j)]
  simp only [squareHolonomy, Matrix.mul_inv_rev, mul_assoc]
  rw [← mul_assoc (pathHolonomy U (pathOfWord (z + wordSum 𝔲 + (a : Site L m j) + (b : Site L m j)) 𝔳)),
    hV, one_mul]
theorem wordHolonomy_swap_of_parallel (hc : U ∈ compactGaugeFields L m j) (z : Site L m j)
    (𝔲 𝔳 : StepWord L m j) {a b : UnitStepVec L m j}
    (hp : (b : Site L m j) = a ∨ (b : Site L m j) = -(a : Site L m j)) :
    wordHolonomy U z (𝔲 ++ a :: b :: 𝔳) = wordHolonomy U z (𝔲 ++ b :: a :: 𝔳) := by
  rcases hp with hp | hp
  · have he : b = a := Subtype.ext hp
    rw [he]
  · have h1 : bondValue U (z + wordSum 𝔲 + (a : Site L m j)) b =
        (bondValue U (z + wordSum 𝔲) a)⁻¹ := by
      have hb : bondOfStep (z + wordSum 𝔲 + (a : Site L m j)) b =
          (bondOfStep (z + wordSum 𝔲) a).opposite :=
        Bond.ext rfl (by simp [bondOfStep, Bond.opposite, hp])
      rw [bondValue, hb]
      exact value_opposite hc _
    have h2 : bondValue U (z + wordSum 𝔲 + (b : Site L m j)) a =
        (bondValue U (z + wordSum 𝔲) b)⁻¹ := by
      have hb : bondOfStep (z + wordSum 𝔲 + (b : Site L m j)) a =
          (bondOfStep (z + wordSum 𝔲) b).opposite :=
        Bond.ext rfl (by simp [bondOfStep, Bond.opposite, hp])
      rw [bondValue, hb]
      exact value_opposite hc _
    rw [wordHolonomy_split, wordHolonomy_split, h1, h2,
      add_right_comm (z + wordSum 𝔲) (b : Site L m j) (a : Site L m j),
      ← mul_assoc (bondValue U _ a), ← mul_assoc (bondValue U _ b),
      mul_inv_cancel_of_mem (value_mem hc _), mul_inv_cancel_of_mem (value_mem hc _)]
theorem norm_wordHolonomy_swap_le (hc : U ∈ compactGaugeFields L m j) (hL : 1 ≤ L)
    (hj : -(m : ℤ) ≤ j) {S : Set (Site L m j)} {ω : ℝ} (hω : 0 ≤ ω)
    (hpl : ∀ p : Plaquette L m j, p.vertices ⊆ S → ‖plaquetteHolonomy U p - 1‖ ≤ ω)
    (z : Site L m j) (𝔲 𝔳 : StepWord L m j) (a b : UnitStepVec L m j)
    (hS : ({z + wordSum 𝔲, z + wordSum 𝔲 + a, z + wordSum 𝔲 + b,
      z + wordSum 𝔲 + a + b} : Set (Site L m j)) ⊆ S) :
    ‖wordHolonomy U z (𝔲 ++ a :: b :: 𝔳) * (wordHolonomy U z (𝔲 ++ b :: a :: 𝔳))⁻¹ - 1‖ ≤ ω := by
  by_cases hp : (b : Site L m j) = a ∨ (b : Site L m j) = -(a : Site L m j)
  · rw [wordHolonomy_swap_of_parallel hc z 𝔲 𝔳 hp, mul_inv_cancel_of_mem (pathHolonomy_mem hc _),
      sub_self, norm_zero]
    exact hω
  · obtain ⟨μ, ν, h1, h2, hμν⟩ := exists_axes_of_not_parallel hp
    obtain ⟨p, hcorners⟩ := exists_plaquette_vertices hμν (z + wordSum 𝔲) h1 h2
    rw [wordHolonomy_swap_ratio hc, norm_conj_sub_one_of_mem (pathHolonomy_mem hc _),
      ← norm_plaquetteHolonomy_sub_one_eq hc hL hj h1 h2 hμν hcorners]
    exact hpl p (hcorners ▸ hS)
end Swap
theorem exists_finset_of_sublist {𝔱 𝔰 : StepWord L m j} (h : 𝔱.Sublist 𝔰) :
    ∃ I : Finset (Fin 𝔰.length), wordSum 𝔱 = ∑ i ∈ I, (𝔰.get i : Site L m j) := by
  induction h with
  | slnil => exact ⟨∅, by simp [wordSum]⟩
  | @cons 𝔱 𝔰 a _ ih =>
    obtain ⟨I, hI⟩ := ih
    refine ⟨I.map (Fin.succEmb 𝔰.length), ?_⟩
    rw [Finset.sum_map, hI]
    rfl
  | @cons_cons 𝔱 𝔰 a _ ih =>
    obtain ⟨I, hI⟩ := ih
    refine ⟨insert (0 : Fin (𝔰.length + 1)) (I.map (Fin.succEmb 𝔰.length)), ?_⟩
    rw [Finset.sum_insert (by simp), Finset.sum_map, wordSum_cons, hI]
    rfl
theorem add_wordSum_mem_partialSumSites {σ 𝔱 𝔰 : StepWord L m j} (hσ : σ.Perm 𝔰)
    (h : 𝔱.Sublist σ) (z : Site L m j) : z + wordSum 𝔱 ∈ partialSumSites z 𝔰 := by
  obtain ⟨𝔱', hp, hs⟩ := h.subperm.trans hσ.subperm
  obtain ⟨I, hI⟩ := exists_finset_of_sublist hs
  refine ⟨I, ?_⟩
  rw [← hI]
  have : wordSum 𝔱' = wordSum 𝔱 :=
    (hp.map fun s : UnitStepVec L m j => (s : Site L m j)).sum_eq
  rw [this]
inductive AdjacentSwaps {α : Type*} (s : List α) : ℕ → List α → Prop
  | refl : AdjacentSwaps s 0 s
  | swap {T : ℕ} (u : List α) (a b : α) (v : List α) :
      AdjacentSwaps s T (u ++ a :: b :: v) → AdjacentSwaps s (T + 1) (u ++ b :: a :: v)
namespace AdjacentSwaps
variable {α : Type*}
theorem perm {T : ℕ} {s t : List α} (h : AdjacentSwaps s T t) : s.Perm t := by
  induction h with
  | refl => exact List.Perm.refl s
  | swap u a b v _ ih => exact ih.trans ((List.Perm.swap b a v).append_left u)
theorem trans {T T' : ℕ} {s t r : List α} (h : AdjacentSwaps s T t) (h' : AdjacentSwaps t T' r) :
    AdjacentSwaps s (T + T') r := by
  induction h' with
  | refl => exact h
  | swap u a b v _ ih => exact AdjacentSwaps.swap u a b v ih
theorem cons (x : α) {T : ℕ} {s t : List α} (h : AdjacentSwaps s T t) :
    AdjacentSwaps (x :: s) T (x :: t) := by
  induction h with
  | refl => exact AdjacentSwaps.refl
  | swap u a b v _ ih => exact AdjacentSwaps.swap (x :: u) a b v ih
theorem moveRight (a : α) (u v : List α) :
    AdjacentSwaps (a :: (u ++ v)) u.length (u ++ a :: v) := by
  induction u with
  | nil => exact AdjacentSwaps.refl
  | cons x u ih =>
    have h1 : AdjacentSwaps (a :: x :: (u ++ v)) 1 (x :: a :: (u ++ v)) :=
      AdjacentSwaps.swap [] a x (u ++ v) AdjacentSwaps.refl
    have h2 := h1.trans (ih.cons x)
    rw [add_comm] at h2
    exact h2
end AdjacentSwaps
theorem exists_adjacentSwaps_of_perm {α : Type*} {s t : List α} (h : s.Perm t) :
    ∃ T, T ≤ s.length * (s.length - 1) / 2 ∧ AdjacentSwaps s T t := by
  induction s generalizing t with
  | nil =>
    obtain rfl := h.nil_eq.symm
    exact ⟨0, Nat.zero_le _, AdjacentSwaps.refl⟩
  | cons a l ih =>
    obtain ⟨u, v, rfl⟩ := List.append_of_mem (h.mem_iff.1 List.mem_cons_self)
    have hp : l.Perm (u ++ v) := (h.trans List.perm_middle).cons_inv
    obtain ⟨T, hT, hch⟩ := ih hp
    refine ⟨T + u.length, ?_, (hch.cons a).trans (AdjacentSwaps.moveRight a u v)⟩
    have hu : u.length ≤ l.length := by
      have := hp.length_eq
      simp only [List.length_append] at this
      omega
    have h2 : T * 2 ≤ l.length * (l.length - 1) :=
      (Nat.le_div_iff_mul_le (by norm_num)).1 hT
    simp only [List.length_cons, Nat.add_sub_cancel]
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    rcases hl : l.length with _ | n
    · rw [hl] at hu h2
      simp only [Nat.zero_mul, Nat.le_zero] at h2
      omega
    · rw [hl] at hu h2
      simp only [Nat.add_sub_cancel] at h2
      nlinarith
theorem norm_wordHolonomy_ratio_le_of_adjacentSwaps {U : Bond L m j → Matrices.ComplexMatrix2}
    (hc : U ∈ compactGaugeFields L m j) (hL : 1 ≤ L) (hj : -(m : ℤ) ≤ j) {z : Site L m j}
    {𝔰 : StepWord L m j} {ω : ℝ} (hω : 0 ≤ ω)
    (hpl : ∀ p : Plaquette L m j, p.vertices ⊆ partialSumSites z 𝔰 →
      ‖plaquetteHolonomy U p - 1‖ ≤ ω)
    {T : ℕ} {𝔱 : StepWord L m j} (h : AdjacentSwaps 𝔰 T 𝔱) :
    ‖wordHolonomy U z 𝔱 * (wordHolonomy U z 𝔰)⁻¹ - 1‖ ≤ (1 + ω) ^ T - 1 := by
  induction h with
  | refl =>
    rw [mul_inv_cancel_of_mem (pathHolonomy_mem hc _), sub_self, norm_zero]
    simp
  | @swap T u a b v hch ih =>
    have hσ : (u ++ a :: b :: v).Perm 𝔰 := hch.perm.symm
    have hS : ({z + wordSum u, z + wordSum u + b, z + wordSum u + a,
        z + wordSum u + b + a} : Set (Site L m j)) ⊆ partialSumSites z 𝔰 := by
      have s0 : u.Sublist (u ++ a :: b :: v) := List.sublist_append_left _ _
      have s1 : (u ++ [a]).Sublist (u ++ a :: b :: v) :=
        List.Sublist.append_left (by simp) u
      have s2 : (u ++ [b]).Sublist (u ++ a :: b :: v) :=
        List.Sublist.append_left (by simp) u
      have s3 : (u ++ [a, b]).Sublist (u ++ a :: b :: v) :=
        List.Sublist.append_left (by simp) u
      have m0 := add_wordSum_mem_partialSumSites hσ s0 z
      have m1 := add_wordSum_mem_partialSumSites hσ s1 z
      have m2 := add_wordSum_mem_partialSumSites hσ s2 z
      have m3 := add_wordSum_mem_partialSumSites hσ s3 z
      simp only [wordSum_append, wordSum_cons, wordSum_nil, add_zero,
        ← add_assoc] at m1 m2 m3
      intro x hx
      simp only [mem_insert_iff, mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact m0
      · exact m2
      · exact m1
      · rw [add_right_comm]
        exact m3
    have h1 := norm_wordHolonomy_swap_le hc hL hj hω hpl z u v b a hS
    have h2 := norm_mul_inv_sub_one_le (pathHolonomy_mem hc (pathOfWord z (u ++ a :: b :: v))) ih h1
    have e : (1 + ((1 + ω) ^ T - 1)) * (1 + ω) - 1 = (1 + ω) ^ (T + 1) - 1 := by ring
    rw [e] at h2
    exact h2
theorem holonomyReorderingBound_holds : HolonomyReorderingBound := by
  intro L m _ hL13 _ j hj U hc z 𝔰 𝔰' ω hre hω hpl
  have hL : 1 ≤ L := by omega
  have hperm : 𝔰.Perm 𝔰' := by
    obtain ⟨π, rfl⟩ := hre
    have h := π.ofFn_comp_perm 𝔰.get
    rw [List.ofFn_get] at h
    exact h.symm
  obtain ⟨T, hT, hch⟩ := exists_adjacentSwaps_of_perm hperm
  refine (norm_wordHolonomy_ratio_le_of_adjacentSwaps hc hL hj hω hpl hch).trans ?_
  have h1 : (1 : ℝ) ≤ 1 + ω := by linarith
  exact sub_le_sub_right (pow_le_pow_right₀ h1 hT) 1
end YangMills.Construction.PeriodicLattice.HolonomyUnderReordering
