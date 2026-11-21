import YangMills.Construction.Lattice.ElementaryBoundsOfOneStepProof
import Mathlib
open Set
open scoped Matrix.Norms.L2Operator
open YangMills.Construction.Matrices
noncomputable section
namespace YangMills.Construction.PeriodicLattice.PathRearrangementProof
variable {L m : ℕ} {j : ℤ}
theorem isUnit_det_of_mem {A : ComplexMatrix2} (hA : A ∈ compactGaugeGroup) : IsUnit A.det := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.det_isUnit_of_mem <;> assumption
theorem gauge_mul_inv {A : ComplexMatrix2} (hA : A ∈ compactGaugeGroup) : A * A⁻¹ = 1 := by apply _root_.YangMills.SharedProofs.p16098 <;> assumption
theorem gauge_inv_inv {A : ComplexMatrix2} (hA : A ∈ compactGaugeGroup) : (A⁻¹)⁻¹ = A := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_inv_of_mem_compactGaugeGroup <;> assumption
theorem gauge_one_mem : (1 : ComplexMatrix2) ∈ compactGaugeGroup :=
  (Matrix.specialUnitaryGroup (Fin 2) ℂ).one_mem
theorem gauge_mul_mem {A B : ComplexMatrix2} (hA : A ∈ compactGaugeGroup)
    (hB : B ∈ compactGaugeGroup) : A * B ∈ compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.mul_mem_of_mem <;> assumption
theorem gauge_inv_mem {A : ComplexMatrix2} (hA : A ∈ compactGaugeGroup) :
    A⁻¹ ∈ compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
def IsConjOrInvConj (A B : ComplexMatrix2) : Prop :=
  ∃ T ∈ compactGaugeGroup, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ A = T * B ^ ε * T⁻¹
theorem IsConjOrInvConj.refl (A : ComplexMatrix2) : IsConjOrInvConj A A :=
  ⟨1, gauge_one_mem, 1, Or.inl rfl, by simp⟩
theorem IsConjOrInvConj.trans_conj {A B C V : ComplexMatrix2} (h : IsConjOrInvConj A B)
    (hV : V ∈ compactGaugeGroup) (hB : B = V * C * V⁻¹) : IsConjOrInvConj A C := by
  obtain ⟨T, hT, ε, hε | hε, rfl⟩ := h
  · subst hε
    refine ⟨T * V, gauge_mul_mem hT hV, 1, Or.inl rfl, ?_⟩
    simp only [hB, zpow_one, Matrix.mul_inv_rev, mul_assoc]
  · subst hε
    refine ⟨T * V, gauge_mul_mem hT hV, -1, Or.inr rfl, ?_⟩
    simp only [hB, zpow_neg_one, Matrix.mul_inv_rev, gauge_inv_inv hV, mul_assoc]
theorem IsConjOrInvConj.trans_inv {A B C : ComplexMatrix2} (h : IsConjOrInvConj A B)
    (hC : C ∈ compactGaugeGroup) (hB : B = C⁻¹) : IsConjOrInvConj A C := by
  obtain ⟨T, hT, ε, hε | hε, rfl⟩ := h
  · subst hε
    exact ⟨T, hT, -1, Or.inr rfl, by simp only [hB, zpow_one, zpow_neg_one]⟩
  · subst hε
    exact ⟨T, hT, 1, Or.inl rfl, by simp only [hB, zpow_one, zpow_neg_one, gauge_inv_inv hC]⟩
def basisStep (L m : ℕ) (j : ℤ) (μ : Fin 4) : UnitStepVec L m j :=
  ⟨unitStep L m j μ, μ, Or.inl rfl⟩
def flipStep (a : UnitStepVec L m j) : UnitStepVec L m j :=
  ⟨-(a : Site L m j), by
    obtain ⟨μ, h | h⟩ := a.2
    · exact ⟨μ, Or.inr (by rw [h])⟩
    · exact ⟨μ, Or.inl (by rw [h, neg_neg])⟩⟩
@[simp] theorem coe_flipStep (a : UnitStepVec L m j) :
    ((flipStep a : UnitStepVec L m j) : Site L m j) = -(a : Site L m j) := rfl
def IsAlongAxis (a : UnitStepVec L m j) (μ : Fin 4) : Prop :=
  (a : Site L m j) = unitStep L m j μ ∨ (a : Site L m j) = -unitStep L m j μ
theorem IsAlongAxis.flip {a : UnitStepVec L m j} {μ : Fin 4} (h : IsAlongAxis a μ) :
    IsAlongAxis (flipStep a) μ := by
  rcases h with h | h
  · exact Or.inr (by rw [coe_flipStep, h])
  · exact Or.inl (by rw [coe_flipStep, h, neg_neg])
theorem unitStep_apply_self_ne_zero (hL : 1 ≤ L) (hj : -(m : ℤ) ≤ j) (μ : Fin 4) :
    ((unitStep L m j μ : Site L m j) : FourTorus L m) μ ≠ 0 := by
  have hcoe : ((unitStep L m j μ : Site L m j) : FourTorus L m) μ =
      ((meshSize L j : ℝ) : AddCircle (torusSide L m)) := by
    simp [unitStep, pointOnAxis]
  rw [hcoe]
  intro h0
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).1 h0
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hLm : (0 : ℝ) < (L : ℝ) ^ m := by positivity
  have hsp : 0 < meshSize L j := zpow_pos (by linarith) _
  have hle : meshSize L j ≤ (L : ℝ) ^ m := by
    have := zpow_le_zpow_right₀ hL1 (show -j ≤ (m : ℤ) by omega)
    simpa [meshSize] using this
  have hside : torusSide L m = 2 * (L : ℝ) ^ m := rfl
  rw [zsmul_eq_mul, hside] at hn
  rcases le_or_gt n 0 with h | h
  · have : (n : ℝ) ≤ 0 := by exact_mod_cast h
    nlinarith
  · have : (1 : ℝ) ≤ n := by exact_mod_cast h
    nlinarith
theorem unitStep_apply_of_ne (μ ν : Fin 4) (h : ν ≠ μ) :
    ((unitStep L m j μ : Site L m j) : FourTorus L m) ν = 0 := by
  simp [unitStep, pointOnAxis, Pi.single_eq_of_ne h]
theorem IsAlongAxis.apply_self_ne_zero {a : UnitStepVec L m j} {μ : Fin 4} (h : IsAlongAxis a μ)
    (hL : 1 ≤ L) (hj : -(m : ℤ) ≤ j) : (((a : Site L m j) : FourTorus L m)) μ ≠ 0 := by
  rcases h with h | h
  · rw [h]; exact unitStep_apply_self_ne_zero hL hj μ
  · rw [h]
    simpa using unitStep_apply_self_ne_zero (j := j) hL hj μ
theorem IsAlongAxis.apply_of_ne {a : UnitStepVec L m j} {μ ν : Fin 4} (h : IsAlongAxis a μ)
    (hν : ν ≠ μ) : (((a : Site L m j) : FourTorus L m)) ν = 0 := by
  rcases h with h | h
  · rw [h]; exact unitStep_apply_of_ne μ ν hν
  · rw [h]
    simpa using unitStep_apply_of_ne (L := L) (m := m) (j := j) μ ν hν
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
    exact unitStep_apply_self_ne_zero hL hj κ (by rw [h0]; rfl)
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
      rw [unitStep_apply_of_ne κ ν (by rw [hκ]; exact hμν.symm), ha.apply_of_ne hμν.symm,
        zero_add] at this
      exact hb.apply_self_ne_zero hL hj this.symm
    · have := hc μ
      rw [unitStep_apply_of_ne κ μ (Ne.symm hκ), hb.apply_of_ne hμν, add_zero] at this
      exact ha.apply_self_ne_zero hL hj this.symm
section Square
variable {ℬ : Set (Bond L m j)} {U : Bond L m j → ComplexMatrix2}
abbrev linkVar (U : Bond L m j → ComplexMatrix2) (y : Site L m j) (a : UnitStepVec L m j) :
    ComplexMatrix2 :=
  U (bondOfStep y a)
def squareHolonomy (U : Bond L m j → ComplexMatrix2) (y : Site L m j) (a b : UnitStepVec L m j) :
    ComplexMatrix2 :=
  linkVar U y a * linkVar U (y + (a : Site L m j)) b * (linkVar U (y + (b : Site L m j)) a)⁻¹ *
    (linkVar U y b)⁻¹
def SquareInside (ℬ : Set (Bond L m j)) (y : Site L m j) (a b : UnitStepVec L m j) : Prop :=
  bondOfStep y a ∈ ℬ ∧ bondOfStep (y + (a : Site L m j)) b ∈ ℬ ∧ bondOfStep y b ∈ ℬ ∧
    bondOfStep (y + (b : Site L m j)) a ∈ ℬ
theorem bondOfStep_flip (y : Site L m j) (a : UnitStepVec L m j) :
    bondOfStep (y + (a : Site L m j)) (flipStep a) = (bondOfStep y a).opposite :=
  Bond.ext rfl (by simp [bondOfStep, Bond.opposite])
theorem add_add_flip (y : Site L m j) (a : UnitStepVec L m j) :
    y + (a : Site L m j) + ((flipStep a : UnitStepVec L m j) : Site L m j) = y := by
  simp
theorem SquareInside.symm {y : Site L m j} {a b : UnitStepVec L m j} (h : SquareInside ℬ y a b) :
    SquareInside ℬ y b a :=
  ⟨h.2.2.1, h.2.2.2, h.1, h.2.1⟩
theorem SquareInside.rearrangedPathCorner (hr : IsReversalClosed ℬ) {y : Site L m j} {a b : UnitStepVec L m j}
    (h : SquareInside ℬ y a b) : SquareInside ℬ (y + (a : Site L m j)) b (flipStep a) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h2, ?_, ?_, ?_⟩
  · rw [add_right_comm y (a : Site L m j) (b : Site L m j), bondOfStep_flip]
    exact hr _ h4
  · rw [bondOfStep_flip]
    exact hr _ h1
  · rw [add_add_flip]
    exact h3
theorem SquareInside.holonomy_mem (hc : IsGaugeField compactGaugeGroup ℬ U) {y : Site L m j}
    {a b : UnitStepVec L m j} (h : SquareInside ℬ y a b) :
    squareHolonomy U y a b ∈ compactGaugeGroup :=
  gauge_mul_mem (gauge_mul_mem (gauge_mul_mem (hc.1 _ h.1) (hc.1 _ h.2.1))
    (gauge_inv_mem (hc.1 _ h.2.2.2))) (gauge_inv_mem (hc.1 _ h.2.2.1))
theorem squareHolonomy_symm (hc : IsGaugeField compactGaugeGroup ℬ U) {y : Site L m j}
    {a b : UnitStepVec L m j} (h : SquareInside ℬ y a b) :
    squareHolonomy U y a b = (squareHolonomy U y b a)⁻¹ := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [squareHolonomy, Matrix.mul_inv_rev, gauge_inv_inv (hc.1 _ h1),
    gauge_inv_inv (hc.1 _ h2), mul_assoc]
theorem squareHolonomy_rotate (hc : IsGaugeField compactGaugeGroup ℬ U) {y : Site L m j}
    {a b : UnitStepVec L m j} (h : SquareInside ℬ y a b) :
    squareHolonomy U y a b =
      linkVar U y a * squareHolonomy U (y + (a : Site L m j)) b (flipStep a) *
        (linkVar U y a)⁻¹ := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have e1 : linkVar U (y + (a : Site L m j) + (b : Site L m j)) (flipStep a) =
      (linkVar U (y + (b : Site L m j)) a)⁻¹ := by
    rw [linkVar, add_right_comm y (a : Site L m j) (b : Site L m j), bondOfStep_flip]
    exact hc.2 _ h4
  have e2 : linkVar U (y + (a : Site L m j)) (flipStep a) = (linkVar U y a)⁻¹ := by
    rw [linkVar, bondOfStep_flip]
    exact hc.2 _ h1
  have e3 : linkVar U (y + (a : Site L m j) + ((flipStep a : UnitStepVec L m j) : Site L m j)) b =
      linkVar U y b := by
    rw [add_add_flip]
  have hA := gauge_mul_inv (hc.1 _ h1)
  simp only [squareHolonomy, e1, e2, e3, gauge_inv_inv (hc.1 _ h1), mul_assoc]
  rw [hA, mul_one]
def IsReachedFrom (ℬ : Set (Bond L m j)) (U : Bond L m j → ComplexMatrix2) (W : ComplexMatrix2)
    (y : Site L m j) (a b : UnitStepVec L m j) : Prop :=
  SquareInside ℬ y a b ∧ IsConjOrInvConj W (squareHolonomy U y a b)
theorem IsReachedFrom.symm (hc : IsGaugeField compactGaugeGroup ℬ U) {W : ComplexMatrix2}
    {y : Site L m j} {a b : UnitStepVec L m j} (h : IsReachedFrom ℬ U W y a b) :
    IsReachedFrom ℬ U W y b a :=
  ⟨h.1.symm, h.2.trans_inv (h.1.symm.holonomy_mem hc) (squareHolonomy_symm hc h.1)⟩
theorem IsReachedFrom.rearrangedPathCorner (hr : IsReversalClosed ℬ) (hc : IsGaugeField compactGaugeGroup ℬ U)
    {W : ComplexMatrix2} {y : Site L m j} {a b : UnitStepVec L m j}
    (h : IsReachedFrom ℬ U W y a b) :
    IsReachedFrom ℬ U W (y + (a : Site L m j)) b (flipStep a) :=
  ⟨h.1.rearrangedPathCorner hr, h.2.trans_conj (hc.1 _ h.1.1) (squareHolonomy_rotate hc h.1)⟩
theorem plaquetteHolonomy_eq_squareHolonomy (hc : IsGaugeField compactGaugeGroup ℬ U)
    (p : Plaquette L m j)
    (h : SquareInside ℬ p.origin (basisStep L m j p.firstAxis) (basisStep L m j p.secondAxis)) :
    plaquetteHolonomy U p =
      squareHolonomy U p.origin (basisStep L m j p.firstAxis) (basisStep L m j p.secondAxis) := by
  have e1 : U (Bond.forwardFrom (p.origin + unitStep L m j p.secondAxis) p.firstAxis).opposite =
      (U (Bond.forwardFrom (p.origin + unitStep L m j p.secondAxis) p.firstAxis))⁻¹ :=
    hc.2 _ h.2.2.2
  have e2 : U (Bond.forwardFrom p.origin p.secondAxis).opposite =
      (U (Bond.forwardFrom p.origin p.secondAxis))⁻¹ :=
    hc.2 _ h.2.2.1
  simp only [plaquetteHolonomy, pathHolonomy, Plaquette.boundaryBonds, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one, e1, e2]
  simp only [squareHolonomy, mul_assoc]
  rfl
theorem IsReachedFrom.toPlaquette (hc : IsGaugeField compactGaugeGroup ℬ U) (hL : 1 ≤ L)
    (hj : -(m : ℤ) ≤ j) {W : ComplexMatrix2} {a b : UnitStepVec L m j} {μ ν : Fin 4}
    {p : Plaquette L m j} (h : IsReachedFrom ℬ U W p.origin a b) (ha : IsAlongAxis a μ)
    (hb : IsAlongAxis b ν) (hμν : μ ≠ ν)
    (hcorners : p.vertices ⊆
      ({p.origin, p.origin + a, p.origin + b, p.origin + a + b} : Set (Site L m j))) :
    IsConjOrInvConj W (plaquetteHolonomy U p) := by
  have hne : unitStep L m j p.firstAxis ≠ unitStep L m j p.secondAxis := by
    intro he
    have h1 := unitStep_apply_self_ne_zero (j := j) hL hj p.firstAxis
    rw [he, unitStep_apply_of_ne p.secondAxis p.firstAxis p.firstAxis_lt_secondAxis.ne] at h1
    exact h1 rfl
  have hf := unitStep_eq_of_mem_square (κ := p.firstAxis) ha hb hμν hL hj
    (hcorners (by simp [Plaquette.vertices]))
  have hg := unitStep_eq_of_mem_square (κ := p.secondAxis) ha hb hμν hL hj
    (hcorners (by simp [Plaquette.vertices]))
  have hfg : IsReachedFrom ℬ U W p.origin (basisStep L m j p.firstAxis)
      (basisStep L m j p.secondAxis) := by
    rcases hf with hf | hf <;> rcases hg with hg | hg
    · exact absurd (hf.trans hg.symm) hne
    · have e1 : basisStep L m j p.firstAxis = a := Subtype.ext hf
      have e2 : basisStep L m j p.secondAxis = b := Subtype.ext hg
      rw [e1, e2]; exact h
    · have e1 : basisStep L m j p.firstAxis = b := Subtype.ext hf
      have e2 : basisStep L m j p.secondAxis = a := Subtype.ext hg
      rw [e1, e2]; exact h.symm hc
    · exact absurd (hf.trans hg.symm) hne
  rw [plaquetteHolonomy_eq_squareHolonomy hc p hfg.1]
  exact hfg.2
theorem conj_plaquette_of_vertices (hr : IsReversalClosed ℬ)
    (hc : IsGaugeField compactGaugeGroup ℬ U) (hL : 1 ≤ L) (hj : -(m : ℤ) ≤ j) {c : Site L m j}
    {s s' : UnitStepVec L m j} {μ ν : Fin 4} (hcar : SquareInside ℬ c s s')
    (hs : IsAlongAxis s μ) (hs' : IsAlongAxis s' ν) (hμν : μ ≠ ν) {p : Plaquette L m j}
    (hp : p.vertices = ({c, c + s, c + s', c + s + s'} : Set (Site L m j))) :
    IsConjOrInvConj (squareHolonomy U c s s') (plaquetteHolonomy U p) := by
  have R0 : IsReachedFrom ℬ U (squareHolonomy U c s s') c s s' :=
    ⟨hcar, IsConjOrInvConj.refl _⟩
  have R1 := R0.rearrangedPathCorner hr hc
  have R2 := R1.rearrangedPathCorner hr hc
  have R3 := R2.rearrangedPathCorner hr hc
  have e3 : c + (s : Site L m j) + s' + ((flipStep s : UnitStepVec L m j) : Site L m j) =
      c + s' := by
    rw [coe_flipStep]; abel
  rw [e3] at R3
  have hbase : p.origin ∈ p.vertices := by simp [Plaquette.vertices]
  rw [hp] at hbase
  simp only [mem_insert_iff, mem_singleton_iff] at hbase
  rcases hbase with hb | hb | hb | hb
  · have R0' : IsReachedFrom ℬ U (squareHolonomy U c s s') p.origin s s' := by rw [hb]; exact R0
    refine R0'.toPlaquette hc hL hj hs hs' hμν ?_
    intro y hy
    rw [hp] at hy
    rw [hb]
    exact hy
  · rw [← hb] at R1
    refine R1.toPlaquette hc hL hj hs' hs.flip hμν.symm ?_
    rw [hp, hb]
    intro y hy
    simp only [mem_insert_iff, mem_singleton_iff, coe_flipStep] at hy ⊢
    have e1 : c + (s : Site L m j) + -(s : Site L m j) = c := by abel
    have e2 : c + (s : Site L m j) + s' + -(s : Site L m j) = c + s' := by abel
    rw [e1, e2]
    tauto
  · rw [← hb] at R3
    refine R3.toPlaquette hc hL hj hs'.flip hs.flip.flip hμν.symm ?_
    rw [hp, hb]
    intro y hy
    simp only [mem_insert_iff, mem_singleton_iff, coe_flipStep, neg_neg] at hy ⊢
    have e1 : c + (s' : Site L m j) + -(s' : Site L m j) = c := by abel
    have e2 : c + (s' : Site L m j) + -(s' : Site L m j) + s = c + s := by abel
    have e3 : c + (s' : Site L m j) + s = c + s + s' := by abel
    rw [e2, e1, e3]
    tauto
  · rw [← hb] at R2
    refine R2.toPlaquette hc hL hj hs.flip hs'.flip hμν ?_
    rw [hp, hb]
    intro y hy
    simp only [mem_insert_iff, mem_singleton_iff, coe_flipStep] at hy ⊢
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
theorem exists_axes_of_not_collinear {e : AdjacentSwap L m j} (hn : ¬ e.IsCollinear) :
    ∃ μ ν : Fin 4, IsAlongAxis e.fst μ ∧ IsAlongAxis e.snd ν ∧ μ ≠ ν := by
  obtain ⟨μ, h1⟩ := e.fst.2
  obtain ⟨ν, h2⟩ := e.snd.2
  refine ⟨μ, ν, h1, h2, ?_⟩
  rintro rfl
  apply hn
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact Or.inl (h2.trans h1.symm)
  · exact Or.inr (by rw [h1, h2])
  · exact Or.inr (by rw [h1, h2, neg_neg])
  · exact Or.inl (h2.trans h1.symm)
theorem pathOfWord_append (z : Site L m j) (u v : StepWord L m j) :
    pathOfWord z (u ++ v) =
      pathOfWord z u ++ pathOfWord (z + (u.map fun s => (s : Site L m j)).sum) v := by
  induction u generalizing z with
  | nil => simp [pathOfWord]
  | cons s u ih => simp [pathOfWord, ih, add_assoc]
theorem pathHolonomy_append (U : Bond L m j → ComplexMatrix2) (Γ Γ' : List (Bond L m j)) :
    pathHolonomy U (Γ ++ Γ') = pathHolonomy U Γ * pathHolonomy U Γ' := by
  simp [pathHolonomy]
theorem pathHolonomy_cons (U : Bond L m j → ComplexMatrix2) (b : Bond L m j)
    (Γ : List (Bond L m j)) : pathHolonomy U (b :: Γ) = U b * pathHolonomy U Γ := by
  simp [pathHolonomy]
theorem pathOfWord_original (e : AdjacentSwap L m j) (z : Site L m j) :
    pathOfWord z e.original = pathOfWord z e.pre ++
      bondOfStep (e.cornerSite z) e.fst :: bondOfStep (e.cornerSite z + (e.fst : Site L m j)) e.snd ::
        pathOfWord (e.cornerSite z + (e.fst : Site L m j) + (e.snd : Site L m j)) e.post := by
  rw [AdjacentSwap.original, pathOfWord_append]
  rfl
theorem pathOfWord_swapped (e : AdjacentSwap L m j) (z : Site L m j) :
    pathOfWord z e.swapped = pathOfWord z e.pre ++
      bondOfStep (e.cornerSite z) e.snd :: bondOfStep (e.cornerSite z + (e.snd : Site L m j)) e.fst ::
        pathOfWord (e.cornerSite z + (e.fst : Site L m j) + (e.snd : Site L m j)) e.post := by
  rw [AdjacentSwap.swapped, pathOfWord_append,
    add_right_comm (e.cornerSite z) (e.fst : Site L m j) (e.snd : Site L m j)]
  rfl
section Swap
variable {ℬ : Set (Bond L m j)} {U : Bond L m j → ComplexMatrix2}
theorem pathHolonomy_mem (hc : IsGaugeField compactGaugeGroup ℬ U) {Γ : List (Bond L m j)}
    (h : ∀ b ∈ Γ, b ∈ ℬ) : pathHolonomy U Γ ∈ compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.pathHolonomy_mem <;> assumption
theorem wordHolonomy_original (U : Bond L m j → ComplexMatrix2) (e : AdjacentSwap L m j)
    (z : Site L m j) :
    wordHolonomy U z e.original = pathHolonomy U (pathOfWord z e.pre) *
      (linkVar U (e.cornerSite z) e.fst * (linkVar U (e.cornerSite z + (e.fst : Site L m j)) e.snd *
        pathHolonomy U (pathOfWord (e.cornerSite z + (e.fst : Site L m j) + (e.snd : Site L m j))
          e.post))) := by
  rw [wordHolonomy, pathOfWord_original, pathHolonomy_append, pathHolonomy_cons,
    pathHolonomy_cons]
theorem wordHolonomy_swapped (U : Bond L m j → ComplexMatrix2) (e : AdjacentSwap L m j)
    (z : Site L m j) :
    wordHolonomy U z e.swapped = pathHolonomy U (pathOfWord z e.pre) *
      (linkVar U (e.cornerSite z) e.snd * (linkVar U (e.cornerSite z + (e.snd : Site L m j)) e.fst *
        pathHolonomy U (pathOfWord (e.cornerSite z + (e.fst : Site L m j) + (e.snd : Site L m j))
          e.post))) := by
  rw [wordHolonomy, pathOfWord_swapped, pathHolonomy_append, pathHolonomy_cons,
    pathHolonomy_cons]
theorem squareInside_of_paths {e : AdjacentSwap L m j} {z : Site L m j}
    (hs : ∀ b ∈ pathOfWord z e.original, b ∈ ℬ) (ht : ∀ b ∈ pathOfWord z e.swapped, b ∈ ℬ) :
    SquareInside ℬ (e.cornerSite z) e.fst e.snd :=
  ⟨hs _ (by rw [pathOfWord_original]; simp), hs _ (by rw [pathOfWord_original]; simp),
    ht _ (by rw [pathOfWord_swapped]; simp), ht _ (by rw [pathOfWord_swapped]; simp)⟩
theorem wordHolonomy_eq_of_collinear (hc : IsGaugeField compactGaugeGroup ℬ U)
    {e : AdjacentSwap L m j} {z : Site L m j} (hs : ∀ b ∈ pathOfWord z e.original, b ∈ ℬ)
    (ht : ∀ b ∈ pathOfWord z e.swapped, b ∈ ℬ) (hp : e.IsCollinear) :
    wordHolonomy U z e.original = wordHolonomy U z e.swapped := by
  rcases hp with hp | hp
  · have he : e.snd = e.fst := Subtype.ext hp
    simp only [AdjacentSwap.original, AdjacentSwap.swapped, he]
  · have hcar := squareInside_of_paths hs ht
    have h1 : linkVar U (e.cornerSite z + (e.fst : Site L m j)) e.snd =
        (linkVar U (e.cornerSite z) e.fst)⁻¹ := by
      have hb : bondOfStep (e.cornerSite z + (e.fst : Site L m j)) e.snd =
          (bondOfStep (e.cornerSite z) e.fst).opposite :=
        Bond.ext rfl (by simp [bondOfStep, Bond.opposite, hp])
      rw [linkVar, hb]
      exact hc.2 _ hcar.1
    have h2 : linkVar U (e.cornerSite z + (e.snd : Site L m j)) e.fst =
        (linkVar U (e.cornerSite z) e.snd)⁻¹ := by
      have hb : bondOfStep (e.cornerSite z + (e.snd : Site L m j)) e.fst =
          (bondOfStep (e.cornerSite z) e.snd).opposite :=
        Bond.ext rfl (by simp [bondOfStep, Bond.opposite, hp])
      rw [linkVar, hb]
      exact hc.2 _ hcar.2.2.1
    rw [wordHolonomy_original, wordHolonomy_swapped, h1, h2, ← mul_assoc (linkVar U _ e.fst),
      ← mul_assoc (linkVar U _ e.snd), gauge_mul_inv (hc.1 _ hcar.1),
      gauge_mul_inv (hc.1 _ hcar.2.2.1)]
theorem wordHolonomy_quotient (hc : IsGaugeField compactGaugeGroup ℬ U) {e : AdjacentSwap L m j}
    {z : Site L m j} (hs : ∀ b ∈ pathOfWord z e.original, b ∈ ℬ) :
    wordHolonomy U z e.original * (wordHolonomy U z e.swapped)⁻¹ =
      pathHolonomy U (pathOfWord z e.pre) * squareHolonomy U (e.cornerSite z) e.fst e.snd *
        (pathHolonomy U (pathOfWord z e.pre))⁻¹ := by
  have hV : pathHolonomy U (pathOfWord (e.cornerSite z + (e.fst : Site L m j) +
      (e.snd : Site L m j)) e.post) ∈ compactGaugeGroup :=
    pathHolonomy_mem hc fun b hb => hs b (by rw [pathOfWord_original]; simp [hb])
  have hV' := gauge_mul_inv hV
  rw [wordHolonomy_original, wordHolonomy_swapped]
  simp only [squareHolonomy, Matrix.mul_inv_rev, mul_assoc]
  rw [← mul_assoc (pathHolonomy U (pathOfWord (e.cornerSite z + (e.fst : Site L m j) +
    (e.snd : Site L m j)) e.post)), hV', one_mul]
theorem quotient_conj_plaquette (hr : IsReversalClosed ℬ)
    (hc : IsGaugeField compactGaugeGroup ℬ U) (hL : 1 ≤ L) (hj : -(m : ℤ) ≤ j)
    {e : AdjacentSwap L m j} {z : Site L m j} (hs : ∀ b ∈ pathOfWord z e.original, b ∈ ℬ)
    (ht : ∀ b ∈ pathOfWord z e.swapped, b ∈ ℬ) (hn : ¬ e.IsCollinear) {p : Plaquette L m j}
    (hp : e.SpansPlaquette z p) :
    ∃ T ∈ compactGaugeGroup, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      wordHolonomy U z e.original * (wordHolonomy U z e.swapped)⁻¹ =
        T * plaquetteHolonomy U p ^ ε * T⁻¹ := by
  obtain ⟨μ, ν, h1, h2, hμν⟩ := exists_axes_of_not_collinear hn
  have hcorners : p.vertices = ({e.cornerSite z, e.cornerSite z + e.fst, e.cornerSite z + e.snd,
      e.cornerSite z + e.fst + e.snd} : Set (Site L m j)) := hp
  have hconj := conj_plaquette_of_vertices hr hc hL hj (squareInside_of_paths hs ht) h1 h2 hμν
    hcorners
  have hH : pathHolonomy U (pathOfWord z e.pre) ∈ compactGaugeGroup :=
    pathHolonomy_mem hc fun b hb => hs b (by rw [pathOfWord_original]; simp [hb])
  obtain ⟨T, hT, ε, hε, hE⟩ := hconj
  refine ⟨pathHolonomy U (pathOfWord z e.pre) * T, gauge_mul_mem hH hT, ε, hε, ?_⟩
  rw [wordHolonomy_quotient hc hs, hE]
  simp only [Matrix.mul_inv_rev, mul_assoc]
end Swap
section Telescope
theorem rotationAngle_one_nonpos (hA : ComplexMatrix2.SpecialUnitaryAngleBounds) :
    ComplexMatrix2.rotationAngle 1 ≤ 0 := by
  have h := (hA.2.1 1 gauge_one_mem).2.2.2.2.1
  have h0 : ComplexMatrix2.operatorNorm (0 : ComplexMatrix2) = 0 := norm_zero
  rw [sub_self, h0] at h
  have hp : 0 < 2 / Real.pi := by positivity
  by_contra hc
  exact absurd h (not_le.2 (mul_pos hp (not_le.1 hc)))
theorem rotationAngle_telescope (hA : ComplexMatrix2.SpecialUnitaryAngleBounds) :
    ∀ (N : ℕ) (h : Fin (N + 1) → ComplexMatrix2) (a : Fin N → ℝ),
      (∀ i, h i ∈ compactGaugeGroup) →
      (∀ l : Fin N, ComplexMatrix2.rotationAngle (h l.castSucc * (h l.succ)⁻¹) ≤ a l) →
      ComplexMatrix2.rotationAngle (h 0 * (h (Fin.last N))⁻¹) ≤ ∑ l, a l := by
  intro N
  induction N with
  | zero =>
    intro h a hh _
    simp only [Fin.last_zero, Finset.univ_eq_empty, Finset.sum_empty]
    rw [gauge_mul_inv (hh 0)]
    exact rotationAngle_one_nonpos hA
  | succ N ih =>
    intro h a hh ha
    have h1 := ih (fun i => h i.castSucc) (fun l => a l.castSucc) (fun i => hh _)
      (fun l => ha l.castSucc)
    have h2 := ha (Fin.last N)
    have e : h 0 * (h (Fin.last (N + 1)))⁻¹ =
        h 0 * (h (Fin.last N).castSucc)⁻¹ *
          (h (Fin.last N).castSucc * (h (Fin.last (N + 1)))⁻¹) := by
      rw [mul_assoc, ← mul_assoc _ (h (Fin.last N).castSucc),
        Matrix.nonsing_inv_mul _ (isUnit_det_of_mem (hh _)), one_mul]
    rw [Fin.sum_univ_castSucc, e]
    have h3 := hA.2.2.2.2.1 _ (gauge_mul_mem (hh 0) (gauge_inv_mem (hh (Fin.last N).castSucc))) _
      (gauge_mul_mem (hh (Fin.last N).castSucc) (gauge_inv_mem (hh (Fin.last (N + 1)))))
    rw [Fin.succ_last] at h2
    have h1' : ComplexMatrix2.rotationAngle (h 0 * (h (Fin.last N).castSucc)⁻¹) ≤
        ∑ l : Fin N, a l.castSucc := h1
    linarith
theorem operatorNorm_telescope : ∀ (N : ℕ) (h : Fin (N + 1) → ComplexMatrix2) (a : Fin N → ℝ),
    (∀ l : Fin N, ComplexMatrix2.operatorNorm (h l.castSucc - h l.succ) ≤ a l) →
    (∀ l, 0 ≤ a l) → ComplexMatrix2.operatorNorm (h 0 - h (Fin.last N)) ≤ ∑ l, a l := by
  intro N
  induction N with
  | zero =>
    intro h a _ _
    simp
  | succ N ih =>
    intro h a ha hpos
    have h1 := ih (fun i => h i.castSucc) (fun l => a l.castSucc) (fun l => ha l.castSucc)
      (fun l => hpos _)
    have h1' : ComplexMatrix2.operatorNorm (h 0 - h (Fin.last N).castSucc) ≤
        ∑ l : Fin N, a l.castSucc := h1
    have h2 := ha (Fin.last N)
    rw [Fin.succ_last] at h2
    rw [Fin.sum_univ_castSucc]
    have h3 := norm_sub_le_norm_sub_add_norm_sub (h 0) (h (Fin.last N).castSucc)
      (h (Fin.last (N + 1)))
    simp only [ComplexMatrix2.operatorNorm] at *
    linarith
theorem rotationAngle_operatorNorm_of_conj (hA : ComplexMatrix2.SpecialUnitaryAngleBounds)
    {W P : ComplexMatrix2} (hW : W ∈ compactGaugeGroup) (hP : P ∈ compactGaugeGroup)
    (h : ∃ T ∈ compactGaugeGroup, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ W = T * P ^ ε * T⁻¹) :
    ComplexMatrix2.rotationAngle W = ComplexMatrix2.rotationAngle P ∧
      ComplexMatrix2.operatorNorm (W - 1) = ComplexMatrix2.operatorNorm (P - 1) := by
  obtain ⟨T, hT, ε, hε, rfl⟩ := h
  have ha : ComplexMatrix2.rotationAngle (T * P ^ ε * T⁻¹) = ComplexMatrix2.rotationAngle P := by
    rcases hε with rfl | rfl
    · rw [zpow_one]
      exact ((hA.2.1 P hP).2.2.2.1 T hT).symm
    · rw [zpow_neg_one]
      rw [← (hA.2.1 _ (gauge_inv_mem hP)).2.2.2.1 T hT]
      exact (hA.2.1 P hP).2.2.1
  refine ⟨ha, ?_⟩
  rw [(hA.2.1 _ hW).1, (hA.2.1 _ hP).1, ha]
theorem operatorNorm_sub_le_of_mem (hA : ComplexMatrix2.SpecialUnitaryAngleBounds)
    {a b : ComplexMatrix2} (ha : a ∈ compactGaugeGroup) (hb : b ∈ compactGaugeGroup) :
    ComplexMatrix2.operatorNorm (a - b) ≤ ComplexMatrix2.operatorNorm (a * b⁻¹ - 1) := by
  have h := (hA.2.2.2.2.2.1 1 (fun _ => a) (fun _ => b) (fun _ => ha) (fun _ => hb)).2
  simpa using h
end Telescope
theorem pathRearrangementBound_holds (hA : ComplexMatrix2.SpecialUnitaryAngleBounds) :
    PathRearrangementBound := by
  intro L m _ hL13 _ j hj ℬ U hr hc z
  have hL : 1 ≤ L := by omega
  refine ⟨fun e hs ht => ⟨fun hp => wordHolonomy_eq_of_collinear hc hs ht hp,
    fun hn => ⟨?_, ?_⟩⟩, ?_⟩
  · obtain ⟨μ, ν, h1, h2, hμν⟩ := exists_axes_of_not_collinear hn
    exact exists_plaquette_vertices hμν (e.cornerSite z) h1 h2
  · intro p hp _
    exact quotient_conj_plaquette hr hc hL hj hs ht hn hp
  · intro N σ e p hσ hpath hplaq
    have hs : ∀ l : Fin N, ∀ b ∈ pathOfWord z (e l).original, b ∈ ℬ := fun l b hb =>
      hpath l.castSucc b (by rwa [← (hσ l).1])
    have ht : ∀ l : Fin N, ∀ b ∈ pathOfWord z (e l).swapped, b ∈ ℬ := fun l b hb =>
      hpath l.succ b (by rwa [← (hσ l).2])
    have hmem : ∀ l, wordHolonomy U z (σ l) ∈ compactGaugeGroup := fun l =>
      pathHolonomy_mem hc (hpath l)
    have hsrc : ∀ l : Fin N, wordHolonomy U z (e l).original = wordHolonomy U z (σ l.castSucc) :=
      fun l => by rw [(hσ l).1]
    have htgt : ∀ l : Fin N, wordHolonomy U z (e l).swapped = wordHolonomy U z (σ l.succ) :=
      fun l => by rw [(hσ l).2]
    have hP : ∀ l : Fin N, ¬ (e l).IsCollinear → plaquetteHolonomy U (p l) ∈ compactGaugeGroup :=
      fun l hl => pathHolonomy_mem hc (hplaq l hl).2
    rw [Finset.sum_filter, Finset.sum_filter]
    refine ⟨rotationAngle_telescope hA N (fun i => wordHolonomy U z (σ i)) _ hmem fun l => ?_,
      operatorNorm_telescope N (fun i => wordHolonomy U z (σ i)) _ (fun l => ?_) fun l => ?_⟩
    · by_cases hl : (e l).IsCollinear
      · have he := wordHolonomy_eq_of_collinear hc (hs l) (ht l) hl
        rw [hsrc, htgt] at he
        rw [he, gauge_mul_inv (hmem _), if_neg (not_not.2 hl)]
        exact rotationAngle_one_nonpos hA
      · have hconj := quotient_conj_plaquette hr hc hL hj (hs l) (ht l) hl (hplaq l hl).1
        rw [hsrc, htgt] at hconj
        rw [if_pos hl]
        exact (rotationAngle_operatorNorm_of_conj hA
          (gauge_mul_mem (hmem _) (gauge_inv_mem (hmem _))) (hP l hl) hconj).1.le
    · by_cases hl : (e l).IsCollinear
      · have he := wordHolonomy_eq_of_collinear hc (hs l) (ht l) hl
        rw [hsrc, htgt] at he
        rw [he, sub_self, if_neg (not_not.2 hl)]
        exact (norm_zero (E := ComplexMatrix2)).le
      · have hconj := quotient_conj_plaquette hr hc hL hj (hs l) (ht l) hl (hplaq l hl).1
        rw [hsrc, htgt] at hconj
        rw [if_pos hl, ← (rotationAngle_operatorNorm_of_conj hA
          (gauge_mul_mem (hmem _) (gauge_inv_mem (hmem _))) (hP l hl) hconj).2]
        exact operatorNorm_sub_le_of_mem hA (hmem _) (hmem _)
    · split_ifs
      · exact le_rfl
      · exact norm_nonneg _
end YangMills.Construction.PeriodicLattice.PathRearrangementProof
