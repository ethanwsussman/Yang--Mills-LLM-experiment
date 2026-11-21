import YangMills.Construction.InfiniteLattice.BondsPlaquettesCircuitsAndConfigurationsOfTheLatticeOfACutoffProof
import YangMills.Construction.InfiniteLattice.FactsOfTheBondsConfigurationsAndMotionsAtOneSpacing
import YangMills.Construction.InfiniteLattice.PlaquetteFunctionAndActionOfTheIsometries
import YangMills.Construction.Matrices.UnitaryLogarithmClosedForm
import YangMills.Construction.ReflectionPositivity.CovarianceAlgebraAndLocalisationOfTheRepresentativesProof
import Mathlib
set_option autoImplicit false
open Set
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction
open Matrices
namespace InfiniteLattice.FaceEnergyAndMotions
def reTraceLoop (g₁ g₂ g₃ g₄ : ComplexMatrix2.specialUnitary) : ℝ :=
  (ComplexMatrix2.fullTrace ((g₁ * g₂ * g₃ * g₄ : ComplexMatrix2.specialUnitary) : ComplexMatrix2)).re
theorem re_fullTrace_inv (g : ComplexMatrix2.specialUnitary) :
    (ComplexMatrix2.fullTrace ((g⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2)).re =
      (ComplexMatrix2.fullTrace (g : ComplexMatrix2)).re := by apply _root_.YangMills.Construction.RefinedLatticeSymmetries.re_fullTrace_inv <;> assumption
theorem reTraceLoop_rotate (g₁ g₂ g₃ g₄ : ComplexMatrix2.specialUnitary) :
    reTraceLoop g₂ g₃ g₄ g₁ = reTraceLoop g₁ g₂ g₃ g₄ := by
  have h : ((g₂ * g₃ * g₄ * g₁ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) =
      ((g₂ * g₃ * g₄ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) * (g₁ : ComplexMatrix2) := rfl
  have h' : ((g₁ * g₂ * g₃ * g₄ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) =
      (g₁ : ComplexMatrix2) * ((g₂ * g₃ * g₄ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) := by
    rw [show g₁ * g₂ * g₃ * g₄ = g₁ * (g₂ * g₃ * g₄) by simp only [mul_assoc]]
    rfl
  rw [reTraceLoop, reTraceLoop, h, h', ComplexMatrix2.fullTrace, ComplexMatrix2.fullTrace,
    Matrix.trace_mul_comm]
theorem reTraceLoop_reverse (g₁ g₂ g₃ g₄ : ComplexMatrix2.specialUnitary) :
    reTraceLoop g₄⁻¹ g₃⁻¹ g₂⁻¹ g₁⁻¹ = reTraceLoop g₁ g₂ g₃ g₄ := by
  have h : g₄⁻¹ * g₃⁻¹ * g₂⁻¹ * g₁⁻¹ = (g₁ * g₂ * g₃ * g₄)⁻¹ := by
    simp only [mul_inv_rev, mul_assoc]
  rw [reTraceLoop, h, re_fullTrace_inv, reTraceLoop]
set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem fin_four_cyclic_or_reversed : ∀ i₁ i₂ i₃ i₄ : Fin 4,
    (∀ k, k = i₁ ∨ k = i₂ ∨ k = i₃ ∨ k = i₄) →
    i₂ ≠ i₁ + 2 → i₃ ≠ i₂ + 2 → i₄ ≠ i₃ + 2 → i₁ ≠ i₄ + 2 →
    (i₁ = 0 ∧ i₂ = 1 ∧ i₃ = 2 ∧ i₄ = 3) ∨ (i₁ = 1 ∧ i₂ = 2 ∧ i₃ = 3 ∧ i₄ = 0) ∨
    (i₁ = 2 ∧ i₂ = 3 ∧ i₃ = 0 ∧ i₄ = 1) ∨ (i₁ = 3 ∧ i₂ = 0 ∧ i₃ = 1 ∧ i₄ = 2) ∨
    (i₁ = 0 ∧ i₂ = 3 ∧ i₃ = 2 ∧ i₄ = 1) ∨ (i₁ = 1 ∧ i₂ = 0 ∧ i₃ = 3 ∧ i₄ = 2) ∨
    (i₁ = 2 ∧ i₂ = 1 ∧ i₃ = 0 ∧ i₄ = 3) ∨ (i₁ = 3 ∧ i₂ = 2 ∧ i₃ = 1 ∧ i₄ = 0) := by
  decide +kernel
theorem reTraceLoop_of_four_corners {S : Type*} (c : Fin 4 → S) (hc : Function.Injective c)
    (w : S → S → ComplexMatrix2.specialUnitary) (hw : ∀ i, w (c (i + 1)) (c i) = (w (c i) (c (i + 1)))⁻¹)
    (A : S → S → Prop) (hA : ∀ i, ¬ A (c i) (c (i + 2))) {y₁ y₂ y₃ y₄ : S}
    (hy : ({y₁, y₂, y₃, y₄} : Set S) = range c)
    (h₁₂ : A y₁ y₂) (h₂₃ : A y₂ y₃) (h₃₄ : A y₃ y₄) (h₄₁ : A y₄ y₁) :
    reTraceLoop (w y₁ y₂) (w y₂ y₃) (w y₃ y₄) (w y₄ y₁) =
      reTraceLoop (w (c 0) (c 1)) (w (c 1) (c 2)) (w (c 2) (c 3)) (w (c 3) (c 0)) := by
  obtain ⟨i₁, rfl⟩ : y₁ ∈ range c := hy ▸ (by simp)
  obtain ⟨i₂, rfl⟩ : y₂ ∈ range c := hy ▸ (by simp)
  obtain ⟨i₃, rfl⟩ : y₃ ∈ range c := hy ▸ (by simp)
  obtain ⟨i₄, rfl⟩ : y₄ ∈ range c := hy ▸ (by simp)
  have hs : ∀ k, k = i₁ ∨ k = i₂ ∨ k = i₃ ∨ k = i₄ := fun k => by
    have h : c k ∈ ({c i₁, c i₂, c i₃, c i₄} : Set S) := hy ▸ mem_range_self k
    simpa [hc.eq_iff] using h
  have n₁ : i₂ ≠ i₁ + 2 := fun h => hA i₁ (h ▸ h₁₂)
  have n₂ : i₃ ≠ i₂ + 2 := fun h => hA i₂ (h ▸ h₂₃)
  have n₃ : i₄ ≠ i₃ + 2 := fun h => hA i₃ (h ▸ h₃₄)
  have n₄ : i₁ ≠ i₄ + 2 := fun h => hA i₄ (h ▸ h₄₁)
  have e₀ : w (c 1) (c 0) = (w (c 0) (c 1))⁻¹ := hw 0
  have e₁ : w (c 2) (c 1) = (w (c 1) (c 2))⁻¹ := hw 1
  have e₂ : w (c 3) (c 2) = (w (c 2) (c 3))⁻¹ := hw 2
  have e₃ : w (c 0) (c 3) = (w (c 3) (c 0))⁻¹ := hw 3
  have r₁ := reTraceLoop_rotate (w (c 0) (c 1)) (w (c 1) (c 2)) (w (c 2) (c 3)) (w (c 3) (c 0))
  have r₂ :=
    (reTraceLoop_rotate (w (c 1) (c 2)) (w (c 2) (c 3)) (w (c 3) (c 0)) (w (c 0) (c 1))).trans r₁
  have r₃ :=
    (reTraceLoop_rotate (w (c 2) (c 3)) (w (c 3) (c 0)) (w (c 0) (c 1)) (w (c 1) (c 2))).trans r₂
  rcases fin_four_cyclic_or_reversed i₁ i₂ i₃ i₄ hs n₁ n₂ n₃ n₄ with
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · rfl
  · exact r₁
  · exact r₂
  · exact r₃
  · rw [e₃, e₂, e₁, e₀]
    exact reTraceLoop_reverse _ _ _ _
  · rw [e₀, e₃, e₂, e₁]
    exact (reTraceLoop_reverse _ _ _ _).trans r₁
  · rw [e₁, e₀, e₃, e₂]
    exact (reTraceLoop_reverse _ _ _ _).trans r₂
  · rw [e₂, e₁, e₀, e₃]
    exact (reTraceLoop_reverse _ _ _ _).trans r₃
def squareCorners {G : Type*} [Add G] (x u v : G) : Fin 4 → G := ![x, x + u, x + u + v, x + v]
theorem range_squareCorners {G : Type*} [Add G] (x u v : G) :
    range (squareCorners x u v) = {x, x + u, x + u + v, x + v} := by
  ext y
  simp [squareCorners, eq_comm]
  tauto
theorem squareCorners_injective_and_diagonals {G A : Type*} [AddCommGroup G] [AddCommGroup A]
    (st : Fin 4 → G) (co : Fin 4 → G →+ A) {d : A} (hd : d ≠ 0)
    (hco : ∀ ν μ, co ν (st μ) = if ν = μ then d else 0) {κ l : Fin 4} (hκl : κ ≠ l) (x : G) :
    Function.Injective (squareCorners x (st κ) (st l)) ∧
      ∀ i : Fin 4, ¬ ∃ μ, squareCorners x (st κ) (st l) (i + 2) - squareCorners x (st κ) (st l) i = st μ ∨
        squareCorners x (st κ) (st l) (i + 2) - squareCorners x (st κ) (st l) i = -st μ := by
  have c₁ : co κ (st κ) = d := by simp [hco]
  have c₂ : co l (st l) = d := by simp [hco]
  have c₃ : co κ (st l) = 0 := by simp [hco, hκl]
  have c₄ : co l (st κ) = 0 := by simp [hco, hκl.symm]
  have hκ0 : st κ ≠ 0 := fun h => hd (by rw [← c₁, h, map_zero])
  have hl0 : st l ≠ 0 := fun h => hd (by rw [← c₂, h, map_zero])
  have hsum : st κ + st l ≠ 0 := fun h => hd (by
    have := congrArg (co κ) h
    simpa [c₁, c₃] using this)
  have hne : st κ ≠ st l := fun h => hd (by
    have := congrArg (co κ) h
    simpa [c₁, c₃] using this)
  have key : ∀ (u : G) (μ ν : Fin 4), ν ≠ μ → (co ν u = d ∨ co ν u = -d) →
      u ≠ st μ ∧ u ≠ -st μ := by
    intro u μ ν hν h
    have z : co ν (st μ) = 0 := by simp [hco, hν]
    have bad : ¬ (co ν u = 0) := fun h₀ => by
      rcases h with h | h
      · exact hd (h.symm.trans h₀)
      · exact hd (neg_eq_zero.mp (h.symm.trans h₀))
    constructor
    · rintro rfl
      exact bad z
    · rintro rfl
      exact bad (by rw [map_neg, z, neg_zero])
  have diag : ∀ u : G, (co κ u = d ∨ co κ u = -d) → (co l u = d ∨ co l u = -d) →
      ∀ μ, u ≠ st μ ∧ u ≠ -st μ := by
    intro u h₁ h₂ μ
    by_cases hμ : κ = μ
    · exact key u μ l (fun h => hκl (hμ.trans h.symm)) h₂
    · exact key u μ κ hμ h₁
  refine ⟨?_, fun i => ?_⟩
  · intro i j h
    fin_cases i <;> fin_cases j <;>
      first
      | rfl
      | (exfalso
         simp [squareCorners, add_assoc, hκ0, hl0, hsum, hne, hne.symm] at h)
  · rintro ⟨μ, h⟩
    have D : ∃ u, squareCorners x (st κ) (st l) (i + 2) - squareCorners x (st κ) (st l) i = u ∧
        (co κ u = d ∨ co κ u = -d) ∧ (co l u = d ∨ co l u = -d) := by
      fin_cases i
      · refine ⟨st κ + st l, ?_, Or.inl (by simp [c₁, c₃]), Or.inl (by simp [c₂, c₄])⟩
        change x + st κ + st l - x = _
        abel
      · refine ⟨st l - st κ, ?_, Or.inr (by simp [c₁, c₃]), Or.inl (by simp [c₂, c₄])⟩
        change x + st l - (x + st κ) = _
        abel
      · refine ⟨-(st κ + st l), ?_, Or.inr (by simp [c₁, c₃]), Or.inr (by simp [c₂, c₄])⟩
        change x - (x + st κ + st l) = _
        abel
      · refine ⟨st κ - st l, ?_, Or.inl (by simp [c₁, c₃]), Or.inr (by simp [c₂, c₄])⟩
        change x + st κ - (x + st l) = _
        abel
    obtain ⟨u, hu, h₁, h₂⟩ := D
    rw [hu] at h
    rcases h with h | h
    · exact (diag u h₁ h₂ μ).1 h
    · exact (diag u h₁ h₂ μ).2 h
theorem energy_bounds (hlog : ComplexMatrix2.UnitaryLogarithmProperties) (g : ComplexMatrix2.specialUnitary) :
    0 ≤ 1 - (1 / 2) * (ComplexMatrix2.fullTrace (g : ComplexMatrix2)).re ∧
      1 - (1 / 2) * (ComplexMatrix2.fullTrace (g : ComplexMatrix2)).re ≤ 2 := by
  obtain ⟨t, ⟨h₁, h₂⟩, ht⟩ := (hlog.2.1 g g.2).1
  have hre : ((1 / 2 : ℂ) * ComplexMatrix2.fullTrace (g : ComplexMatrix2)).re = (t : ℂ).re :=
    congrArg Complex.re ht
  have e : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  rw [e, Complex.re_ofReal_mul, Complex.ofReal_re] at hre
  constructor <;> linarith
theorem continuous_energy {X : Type*} [TopologicalSpace X] {g : X → ComplexMatrix2.specialUnitary}
    (hg : Continuous g) :
    Continuous fun x => 1 - (1 / 2) * (ComplexMatrix2.fullTrace (g x : ComplexMatrix2)).re := by
  have h₁ : Continuous fun x => (g x : ComplexMatrix2) := continuous_subtype_val.comp hg
  have h₂ : Continuous fun x => ComplexMatrix2.fullTrace (g x : ComplexMatrix2) := h₁.matrix_trace
  exact continuous_const.sub (continuous_const.mul (Complex.continuous_re.comp h₂))
section Infinite
variable {a : ℝ}
def coordAddHom (a : ℝ) (ν : Fin 4) : LatticePoint a →+ ℝ where
  toFun x := (x : AmbientSpace) ν
  map_zero' := rfl
  map_add' _ _ := rfl
theorem coordAddHom_axisStep (ν μ : Fin 4) :
    coordAddHom a ν (axisStep a μ) = if ν = μ then a else 0 := by
  simp [coordAddHom, axisStep, Pi.single_apply]
def Neighbours (x y : LatticePoint a) : Prop :=
  ∃ μ : Fin 4, y - x = axisStep a μ ∨ y - x = -axisStep a μ
theorem Neighbours.symm {x y : LatticePoint a} (h : Neighbours x y) : Neighbours y x := by
  obtain ⟨μ, h | h⟩ := h
  · exact ⟨μ, Or.inr (by rw [← h]; abel)⟩
  · exact ⟨μ, Or.inl (by rw [← neg_eq_iff_eq_neg.mpr h]; abel)⟩
open Classical in
def linkVal (U : GaugeField a) (x y : LatticePoint a) : ComplexMatrix2.specialUnitary :=
  if h : Neighbours x y then U ⟨x, y, h⟩ else 1
theorem linkVal_of_neighbours (U : GaugeField a) {x y : LatticePoint a} (h : Neighbours x y) :
    linkVal U x y = U ⟨x, y, h⟩ :=
  dif_pos h
theorem linkVal_swap (U : GaugeField a) (x y : LatticePoint a) : linkVal U y x = (linkVal U x y)⁻¹ := by
  by_cases h : Neighbours x y
  · rw [linkVal_of_neighbours U h.symm, linkVal_of_neighbours U h]
    exact U.2 ⟨x, y, h⟩
  · have h' : ¬ Neighbours y x := fun k => h k.symm
    simp [linkVal, h, h']
theorem re_trace_boundaryCycle (ha : a ≠ 0) (p : ElementaryPlaquette a) (U : GaugeField a)
    (c : GibbsAtFixedSpacing.BoundaryCycle p) :
    (ComplexMatrix2.fullTrace (c.holonomy U : ComplexMatrix2)).re =
      reTraceLoop (linkVal U (squareCorners p.corner (axisStep a p.lowAxis) (axisStep a p.highAxis) 0)
          (squareCorners p.corner (axisStep a p.lowAxis) (axisStep a p.highAxis) 1))
        (linkVal U (squareCorners p.corner (axisStep a p.lowAxis) (axisStep a p.highAxis) 1)
          (squareCorners p.corner (axisStep a p.lowAxis) (axisStep a p.highAxis) 2))
        (linkVal U (squareCorners p.corner (axisStep a p.lowAxis) (axisStep a p.highAxis) 2)
          (squareCorners p.corner (axisStep a p.lowAxis) (axisStep a p.highAxis) 3))
        (linkVal U (squareCorners p.corner (axisStep a p.lowAxis) (axisStep a p.highAxis) 3)
          (squareCorners p.corner (axisStep a p.lowAxis) (axisStep a p.highAxis) 0)) := by
  have hcs := squareCorners_injective_and_diagonals (axisStep a) (coordAddHom a) ha coordAddHom_axisStep
    (ne_of_lt p.lowAxis_lt_highAxis) p.corner
  have key := reTraceLoop_of_four_corners _ hcs.1 (linkVal U) (fun i => linkVal_swap U _ _) Neighbours hcs.2
    (y₁ := c.v₁) (y₂ := c.v₂) (y₃ := c.v₃) (y₄ := c.v₄)
    (c.corners_eq.trans (range_squareCorners _ _ _).symm)
    c.adj₁₂ c.adj₂₃ c.adj₃₄ c.adj₄₁
  rw [← key, linkVal_of_neighbours U c.adj₁₂, linkVal_of_neighbours U c.adj₂₃,
    linkVal_of_neighbours U c.adj₃₄, linkVal_of_neighbours U c.adj₄₁]
  rfl
theorem continuous_eval_link (b : Link a) : Continuous fun U : GaugeField a => U b := by apply _root_.YangMills.Construction.ReflectionPositivity.RepresentativeCovariance.continuous_eval_link <;> assumption
theorem faceEnergyProperties_of (hlog : ComplexMatrix2.UnitaryLogarithmProperties) (ha : a ≠ 0) :
    FaceEnergyProperties a := by
  intro p
  refine ⟨fun U c c' => ?_, fun U => energy_bounds hlog _, ?_, ?_⟩
  · rw [re_trace_boundaryCycle ha p U c, re_trace_boundaryCycle ha p U c']
  · refine continuous_energy (g := fun U : GaugeField a => faceHolonomy U p) ?_
    exact (((continuous_eval_link _).mul (continuous_eval_link _)).mul (continuous_eval_link _).inv).mul
      (continuous_eval_link _).inv
  · intro U U' h
    have e : ∀ b ∈ p.sideLinks, U b = U' b := fun b hb => congrFun h ⟨b, hb⟩
    simp only [faceEnergy, faceHolonomy]
    rw [e (Link.forwardFrom p.corner p.lowAxis) (by simp [ElementaryPlaquette.sideLinks]),
      e (Link.forwardFrom (p.corner + axisStep a p.lowAxis) p.highAxis)
        (by simp [ElementaryPlaquette.sideLinks]),
      e (Link.forwardFrom (p.corner + axisStep a p.highAxis) p.lowAxis)
        (by simp [ElementaryPlaquette.sideLinks]),
      e (Link.forwardFrom p.corner p.highAxis) (by simp [ElementaryPlaquette.sideLinks])]
end Infinite
section Torus
open PeriodicLattice (CompactGaugeField)
variable {L m : ℕ} {j : ℤ}
def torusCoordAddHom (L m : ℕ) (j : ℤ) (ν : Fin 4) :
    PeriodicLattice.Site L m j →+ AddCircle (PeriodicLattice.torusSide L m) where
  toFun x := (x : PeriodicLattice.FourTorus L m) ν
  map_zero' := rfl
  map_add' _ _ := rfl
theorem torusCoordAddHom_unitStep (ν μ : Fin 4) :
    torusCoordAddHom L m j ν (PeriodicLattice.unitStep L m j μ) =
      if ν = μ then ((PeriodicLattice.meshSize L j : ℝ) : AddCircle (PeriodicLattice.torusSide L m))
      else 0 := by
  simp [torusCoordAddHom, PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, Pi.single_apply]
theorem addCircle_coe_ne_zero {ℓ t : ℝ} (h₀ : 0 < t) (h₁ : t < ℓ / 2) :
    ((t : ℝ) : AddCircle ℓ) ≠ 0 := by
  intro h
  rw [AddCircle.coe_eq_zero_iff] at h
  obtain ⟨n, hn⟩ := h
  rw [zsmul_eq_mul] at hn
  rcases lt_trichotomy n 0 with h | h | h
  · have h' : (n : ℝ) ≤ -1 := by exact_mod_cast (by omega : n ≤ -1)
    nlinarith
  · subst h
    simp at hn
    linarith
  · have h' : (1 : ℝ) ≤ n := by exact_mod_cast h
    nlinarith
def TorusNeighbours (x y : PeriodicLattice.Site L m j) : Prop :=
  ∃ μ : Fin 4, y - x = PeriodicLattice.unitStep L m j μ ∨ y - x = -PeriodicLattice.unitStep L m j μ
theorem TorusNeighbours.symm {x y : PeriodicLattice.Site L m j} (h : TorusNeighbours x y) :
    TorusNeighbours y x := by
  obtain ⟨μ, h | h⟩ := h
  · exact ⟨μ, Or.inr (by rw [← h]; abel)⟩
  · exact ⟨μ, Or.inl (by rw [← neg_eq_iff_eq_neg.mpr h]; abel)⟩
open Classical in
def torusLinkVal (U : CompactGaugeField L m j) (x y : PeriodicLattice.Site L m j) :
    ComplexMatrix2.specialUnitary :=
  if h : TorusNeighbours x y then U.linkValue ⟨x, y, h⟩ else 1
theorem torusLinkVal_of_neighbours (U : CompactGaugeField L m j) {x y : PeriodicLattice.Site L m j}
    (h : TorusNeighbours x y) : torusLinkVal U x y = U.linkValue ⟨x, y, h⟩ :=
  dif_pos h
theorem torusLinkVal_swap (U : CompactGaugeField L m j) (x y : PeriodicLattice.Site L m j) :
    torusLinkVal U y x = (torusLinkVal U x y)⁻¹ := by
  by_cases h : TorusNeighbours x y
  · rw [torusLinkVal_of_neighbours U h.symm, torusLinkVal_of_neighbours U h]
    exact U.linkValue_opposite ⟨x, y, h⟩
  · have h' : ¬ TorusNeighbours y x := fun k => h k.symm
    simp [torusLinkVal, h, h']
theorem torusNeighbours_of_bond (b : PeriodicLattice.Bond L m j) {y : PeriodicLattice.Site L m j}
    (h : b.target = y) : TorusNeighbours b.source y :=
  h ▸ b.isNeighbour
theorem torusLinkVal_of_bond (U : CompactGaugeField L m j) (b : PeriodicLattice.Bond L m j)
    {y : PeriodicLattice.Site L m j} (h : b.target = y) : torusLinkVal U b.source y = U.linkValue b := by
  subst h
  exact torusLinkVal_of_neighbours U b.isNeighbour
theorem re_trace_loopAroundPlaquette
    (hd : ((PeriodicLattice.meshSize L j : ℝ) : AddCircle (PeriodicLattice.torusSide L m)) ≠ 0)
    (p : PeriodicLattice.Plaquette L m j) (U : CompactGaugeField L m j)
    {Γ : List (PeriodicLattice.Bond L m j)} (hΓ : PeriodicLattice.IsLoopAroundPlaquette p Γ) :
    (ComplexMatrix2.fullTrace (PeriodicLattice.pathHolonomy U.1 Γ)).re =
      reTraceLoop
        (torusLinkVal U (squareCorners p.origin (PeriodicLattice.unitStep L m j p.firstAxis)
            (PeriodicLattice.unitStep L m j p.secondAxis) 0)
          (squareCorners p.origin (PeriodicLattice.unitStep L m j p.firstAxis)
            (PeriodicLattice.unitStep L m j p.secondAxis) 1))
        (torusLinkVal U (squareCorners p.origin (PeriodicLattice.unitStep L m j p.firstAxis)
            (PeriodicLattice.unitStep L m j p.secondAxis) 1)
          (squareCorners p.origin (PeriodicLattice.unitStep L m j p.firstAxis)
            (PeriodicLattice.unitStep L m j p.secondAxis) 2))
        (torusLinkVal U (squareCorners p.origin (PeriodicLattice.unitStep L m j p.firstAxis)
            (PeriodicLattice.unitStep L m j p.secondAxis) 2)
          (squareCorners p.origin (PeriodicLattice.unitStep L m j p.firstAxis)
            (PeriodicLattice.unitStep L m j p.secondAxis) 3))
        (torusLinkVal U (squareCorners p.origin (PeriodicLattice.unitStep L m j p.firstAxis)
            (PeriodicLattice.unitStep L m j p.secondAxis) 3)
          (squareCorners p.origin (PeriodicLattice.unitStep L m j p.firstAxis)
            (PeriodicLattice.unitStep L m j p.secondAxis) 0)) := by
  obtain ⟨hl, ⟨x, hpath, -, hhead, hlast⟩, hset⟩ := hΓ
  rcases Γ with _ | ⟨b₁, _ | ⟨b₂, _ | ⟨b₃, _ | ⟨b₄, _ | ⟨b₅, Γ⟩⟩⟩⟩⟩
  · simp at hl
  · simp at hl
  · simp at hl
  · simp at hl
  swap
  · simp only [List.length_cons] at hl
    omega
  have h₁₂ : b₁.target = b₂.source := by
    simp [PeriodicLattice.IsBondPath] at hpath
    exact hpath.1
  have h₂₃ : b₂.target = b₃.source := by
    simp [PeriodicLattice.IsBondPath] at hpath
    exact hpath.2.1
  have h₃₄ : b₃.target = b₄.source := by
    simp [PeriodicLattice.IsBondPath] at hpath
    exact hpath.2.2
  have h₄₁ : b₄.target = b₁.source := by
    have e₁ : b₁.source = x := hhead b₁ (by simp)
    have e₂ : b₄.target = x := hlast b₄ (by simp)
    rw [e₁, e₂]
  have hcs := squareCorners_injective_and_diagonals (PeriodicLattice.unitStep L m j)
    (torusCoordAddHom L m j) hd torusCoordAddHom_unitStep (ne_of_lt p.firstAxis_lt_secondAxis) p.origin
  have hy : ({b₁.source, b₂.source, b₃.source, b₄.source} : Set (PeriodicLattice.Site L m j)) =
      range (squareCorners p.origin (PeriodicLattice.unitStep L m j p.firstAxis)
        (PeriodicLattice.unitStep L m j p.secondAxis)) := by
    rw [range_squareCorners]
    refine Eq.trans ?_ hset
    ext y
    simp [eq_comm]
  have key := reTraceLoop_of_four_corners _ hcs.1 (torusLinkVal U) (fun i => torusLinkVal_swap U _ _)
    TorusNeighbours hcs.2 hy (torusNeighbours_of_bond b₁ h₁₂) (torusNeighbours_of_bond b₂ h₂₃)
    (torusNeighbours_of_bond b₃ h₃₄) (torusNeighbours_of_bond b₄ h₄₁)
  rw [torusLinkVal_of_bond U b₁ h₁₂, torusLinkVal_of_bond U b₂ h₂₃, torusLinkVal_of_bond U b₃ h₃₄,
    torusLinkVal_of_bond U b₄ h₄₁] at key
  rw [← key]
  have hol : PeriodicLattice.pathHolonomy U.1 [b₁, b₂, b₃, b₄] =
      ((U.linkValue b₁ * U.linkValue b₂ * U.linkValue b₃ * U.linkValue b₄ :
        ComplexMatrix2.specialUnitary) : ComplexMatrix2) := by
    simp only [Submonoid.coe_mul, PeriodicLattice.pathHolonomy, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, mul_assoc]
    rfl
  rw [hol]
  rfl
def torusFaceHolonomy (U : CompactGaugeField L m j) (p : PeriodicLattice.Plaquette L m j) :
    ComplexMatrix2.specialUnitary :=
  U.linkValue (PeriodicLattice.Bond.forwardFrom p.origin p.firstAxis) *
    U.linkValue (PeriodicLattice.Bond.forwardFrom (p.origin + PeriodicLattice.unitStep L m j p.firstAxis)
      p.secondAxis) *
    (U.linkValue (PeriodicLattice.Bond.forwardFrom (p.origin + PeriodicLattice.unitStep L m j p.secondAxis)
      p.firstAxis))⁻¹ *
    (U.linkValue (PeriodicLattice.Bond.forwardFrom p.origin p.secondAxis))⁻¹
theorem plaquetteHolonomy_eq (U : CompactGaugeField L m j) (p : PeriodicLattice.Plaquette L m j) :
    PeriodicLattice.plaquetteHolonomy U.1 p = (torusFaceHolonomy U p : ComplexMatrix2) := by
  have r : ∀ b : PeriodicLattice.Bond L m j,
      U.1 b.opposite = (((U.linkValue b)⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) :=
    fun b => congrArg Subtype.val (U.linkValue_opposite b)
  simp only [PeriodicLattice.plaquetteHolonomy, PeriodicLattice.pathHolonomy,
    PeriodicLattice.Plaquette.boundaryBonds, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, r, torusFaceHolonomy, Submonoid.coe_mul, mul_assoc]
  rfl
theorem plaquetteEnergy_eq (U : CompactGaugeField L m j) (p : PeriodicLattice.Plaquette L m j) :
    PeriodicLattice.plaquetteCost U.1 p =
      1 - (1 / 2) * (ComplexMatrix2.fullTrace (torusFaceHolonomy U p : ComplexMatrix2)).re := by
  rw [PeriodicLattice.plaquetteCost, plaquetteHolonomy_eq]
theorem continuous_linkValue (b : PeriodicLattice.Bond L m j) :
    Continuous fun U : CompactGaugeField L m j => U.linkValue b :=
  continuous_iInf_dom continuous_induced_dom
theorem periodicFaceEnergyProperties_of (hlog : ComplexMatrix2.UnitaryLogarithmProperties)
    (hd : ((PeriodicLattice.meshSize L j : ℝ) : AddCircle (PeriodicLattice.torusSide L m)) ≠ 0) :
    PeriodicFaceEnergyProperties L m j := by
  intro p
  refine ⟨fun U Γ Γ' h h' => ?_, fun U => ?_, ?_, ?_⟩
  · rw [re_trace_loopAroundPlaquette hd p U h, re_trace_loopAroundPlaquette hd p U h']
  · rw [plaquetteEnergy_eq]
    exact energy_bounds hlog _
  · simp only [plaquetteEnergy_eq]
    refine continuous_energy (g := fun U : CompactGaugeField L m j => torusFaceHolonomy U p) ?_
    exact (((continuous_linkValue _).mul (continuous_linkValue _)).mul
      (continuous_linkValue _).inv).mul (continuous_linkValue _).inv
  · intro U U' h
    have e : ∀ b ∈ p.edges, U.linkValue b = U'.linkValue b := fun b hb => congrFun h ⟨b, hb⟩
    simp only [plaquetteEnergy_eq, torusFaceHolonomy]
    rw [e (PeriodicLattice.Bond.forwardFrom p.origin p.firstAxis)
        (by simp [PeriodicLattice.Plaquette.edges]),
      e (PeriodicLattice.Bond.forwardFrom (p.origin + PeriodicLattice.unitStep L m j p.firstAxis)
        p.secondAxis) (by simp [PeriodicLattice.Plaquette.edges]),
      e (PeriodicLattice.Bond.forwardFrom (p.origin + PeriodicLattice.unitStep L m j p.secondAxis)
        p.firstAxis) (by simp [PeriodicLattice.Plaquette.edges]),
      e (PeriodicLattice.Bond.forwardFrom p.origin p.secondAxis)
        (by simp [PeriodicLattice.Plaquette.edges])]
end Torus
section Motions
open OneSpacing (MotionsClosed)
variable {a : ℝ}
theorem latticeMotionField_comp (r t : latticeMotions a)
    (h : latticeMotionMul r.1 t.1 ∈ latticeMotions a) :
    latticeMotionField t ∘ latticeMotionField r = latticeMotionField ⟨_, h⟩ :=
  funext fun U => Subtype.ext (funext fun _ => congrArg U.1 (Link.ext rfl rfl))
theorem latticeMotionField_cancel (r t : latticeMotions a)
    (h : latticeMotionMul r.1 t.1 = id) (U : GaugeField a) :
    latticeMotionField t (latticeMotionField r U) = U :=
  Subtype.ext (funext fun _ => congrArg U.1
    (Link.ext (Subtype.ext (congrFun h _)) (Subtype.ext (congrFun h _))))
theorem eq_of_eq_on_positiveLinks {U U' : GaugeField a} {T : Set (Link a)}
    (hT : ∀ b ∈ T, b.opposite ∈ T)
    (h : ∀ b ∈ T, b ∈ positiveLinkSet a → U b = U' b) {b : Link a} (hb : b ∈ T) :
    U b = U' b := by
  rcases mem_positiveLinks_or_opposite_mem b with hp | hp
  · exact h b hb hp
  · have e := h b.opposite (hT b hb) hp
    have hU : U b = (U b.opposite)⁻¹ := U.2 b.opposite
    have hU' : U' b = (U' b.opposite)⁻¹ := U'.2 b.opposite
    rw [hU, hU', e]
theorem latticeMotionAct_mem_localized (r : latticeMotions a) {S : Set AmbientSpace}
    {F : GaugeField a → ℂ} (hF : F ∈ localizedBoundedObservables a S) :
    latticeMotionAct r F ∈ localizedBoundedObservables a (r.1 '' S) := by
  refine ⟨hF.1.latticeMotionAct r, fun U U' h => hF.2 _ _ (funext fun b => ?_)⟩
  have hb : (b : Link a) ∈ linksWithin S := b.2.2
  refine eq_of_eq_on_positiveLinks (T := linksWithin (r.1 '' S)) (fun c hc => ⟨hc.2, hc.1⟩)
    (fun c hc hp => congrFun h ⟨c, hp, hc⟩) (b := (latticeMotionSymmetry r).linkMap b) ?_
  exact ⟨⟨_, hb.1, rfl⟩, ⟨_, hb.2, rfl⟩⟩
theorem latticeMotionAct_mem_cylinder (r : latticeMotions a) {F : GaugeField a → ℂ}
    (hF : F ∈ continuousCylinderFunctions a) :
    latticeMotionAct r F ∈ continuousCylinderFunctions a := by
  obtain ⟨hc, W, hWf, -, hW⟩ := hF
  refine ⟨hc.comp (continuous_latticeMotionField r), ?_⟩
  let T : Set (Link a) := (latticeMotionSymmetry r).linkMap '' W ∪
    (fun b => ((latticeMotionSymmetry r).linkMap b).opposite) '' W
  refine ⟨positiveLinkSet a ∩ T, ((hWf.image _).union (hWf.image _)).inter_of_right _,
    inter_subset_left, fun U U' h => hW _ _ (funext fun b => ?_)⟩
  refine eq_of_eq_on_positiveLinks (T := T) ?_ (fun c hc hp => congrFun h ⟨c, hp, hc⟩)
    (b := (latticeMotionSymmetry r).linkMap b) (Or.inl ⟨b, b.2, rfl⟩)
  rintro c (⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩)
  · exact Or.inr ⟨d, hd, rfl⟩
  · exact Or.inl ⟨d, hd, rfl⟩
theorem composesOnTheRight_of (hg : MotionsClosed a) (r t : latticeMotions a) :
    ComposesOnTheRight r t := by
  have h := hg.2.1 r.1 r.2 t.1 t.2
  exact ⟨h, latticeMotionField_comp r t h, fun F => funext fun U =>
    congrArg F (congrFun (latticeMotionField_comp r t h) U)⟩
theorem actsByHomeomorph_of (hg : MotionsClosed a) (r : latticeMotions a) :
    ActsByHomeomorph r := by
  obtain ⟨r', hr', h₁, h₂⟩ := hg.2.2 r.1 r.2
  refine ⟨⟨r', hr'⟩, h₁, h₂,
    { toFun := latticeMotionField r
      invFun := latticeMotionField ⟨r', hr'⟩
      left_inv := latticeMotionField_cancel r ⟨r', hr'⟩ h₁
      right_inv := latticeMotionField_cancel ⟨r', hr'⟩ r h₂
      continuous_toFun := continuous_latticeMotionField r
      continuous_invFun := continuous_latticeMotionField ⟨r', hr'⟩ }, rfl, rfl⟩
theorem actsOnObservables_of (hg : MotionsClosed a) (r : latticeMotions a) :
    ActsOnObservables r := by
  obtain ⟨r', hr', h₁, h₂⟩ := hg.2.2 r.1 r.2
  have back : ∀ H : GaugeField a → ℂ,
      latticeMotionAct r (latticeMotionAct ⟨r', hr'⟩ H) = H := fun H =>
    funext fun U => congrArg H (latticeMotionField_cancel r ⟨r', hr'⟩ h₁ U)
  refine ⟨fun _ _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun S => ?_, ?_⟩
  · refine Subset.antisymm ?_ fun H hH => ⟨latticeMotionAct ⟨r', hr'⟩ H, ?_, back H⟩
    · rintro _ ⟨F, hF, rfl⟩
      exact latticeMotionAct_mem_localized r hF
    · have h := latticeMotionAct_mem_localized ⟨r', hr'⟩ hH
      have hS : r' '' (r.1 '' S) = S := by
        rw [image_image]
        exact (image_congr fun x _ => congrFun h₂ x).trans (image_id S)
      rwa [hS] at h
  · refine Subset.antisymm ?_ fun H hH => ⟨latticeMotionAct ⟨r', hr'⟩ H, ?_, back H⟩
    · rintro _ ⟨F, hF, rfl⟩
      exact latticeMotionAct_mem_cylinder r hF
    · exact latticeMotionAct_mem_cylinder ⟨r', hr'⟩ hH
end Motions
theorem faceEnergyAndMotionStatement_holds (hlog : ComplexMatrix2.UnitaryLogarithmProperties)
    (hset : OneSpacing.AllFacts) : FaceEnergyAndMotionStatement := by
  intro D
  have hs := hset D.toStandingParameters
  have hpos : 0 < D.mesh := OneSpacing.meshSize_pos D.toStandingParameters
  have hg : OneSpacing.MotionsClosed D.mesh := hs.2.2.2.1.1
  obtain ⟨-, -, -, -, -, hlt, -⟩ := hs.2.2.2.2.2.1
  exact ⟨faceEnergyProperties_of hlog hpos.ne',
    periodicFaceEnergyProperties_of hlog (addCircle_coe_ne_zero hpos hlt), fun r =>
      ⟨fun U b => (latticeMotionField r U).2 b, fun t => composesOnTheRight_of hg r t,
        actsByHomeomorph_of hg r, actsOnObservables_of hg r⟩⟩
end InfiniteLattice.FaceEnergyAndMotions
end YangMills.Construction
