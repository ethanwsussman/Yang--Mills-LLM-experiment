import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.InfiniteLattice.PositiveLinksAndCylinderFunctions
import Mathlib
set_option autoImplicit false
open MeasureTheory Set YangMills.Construction.InfiniteLattice
noncomputable section
namespace YangMills.Construction.CutoffLinks
structure CutoffData extends Conventions.StandingParameters where
  coupling : ℝ
  coupling_pos : 0 < coupling
namespace CutoffData
variable (d : CutoffData)
abbrev spacing : ℝ := PeriodicLattice.meshSize d.L ((d.K : ℕ) : ℤ)
theorem spacing_pos : 0 < d.spacing := by
  have hAdm := d.isAdmissible.2
  have hL : (0 : ℝ) < d.L := by exact_mod_cast (by omega : 0 < d.L)
  exact zpow_pos hL _
abbrev links : Set (Link d.spacing) := positiveLinkSet d.spacing
abbrev sideSet : Set ℝ := PeriodicLattice.torusSides d.L
theorem side_mem_sideSet : d.side ∈ d.sideSet := ⟨d.m, d.m.pos, rfl⟩
theorem existsUnique_sideExponent {s : ℝ} (hs : s ∈ d.sideSet) :
    ∃! q : ℕ+, PeriodicLattice.torusSide d.L q = s := by
  obtain ⟨q, hq, rfl⟩ := hs
  refine ⟨⟨q, hq⟩, rfl, fun q' hq' => ?_⟩
  have hL : (1 : ℝ) < d.L := by
    have hAdm := d.isAdmissible.2
    exact_mod_cast (by omega : 1 < d.L)
  have hpow : (d.L : ℝ) ^ (q' : ℕ) = (d.L : ℝ) ^ q := by
    simpa [PeriodicLattice.torusSide] using hq'
  exact PNat.eq (pow_right_injective₀ (by linarith) hL.ne' hpow)
def sideExponent (s : d.sideSet) : ℕ+ := (d.existsUnique_sideExponent s.2).exists.choose
theorem torusSide_sideExponent (s : d.sideSet) :
    PeriodicLattice.torusSide d.L (d.sideExponent s) = s :=
  (d.existsUnique_sideExponent s.2).exists.choose_spec
def withSide (s : d.sideSet) : CutoffData := { d with m := d.sideExponent s }
theorem side_withSide (s : d.sideSet) : (d.withSide s).side = s := d.torusSide_sideExponent s
end CutoffData
variable {a : ℝ}
def linkEndpoints (b : Link a) : Set (LatticePoint a) := {b.initial, b.terminal}
def restrictVariables {S S' : Set (Link a)} (h : S' ⊆ S) (Y : LinkVariables S) : LinkVariables S' :=
  fun b => Y (Set.inclusion h b)
def variablesUnionHomeomorph {S S' : Set (Link a)} (h : Disjoint S S') :
    LinkVariables ↥(S ∪ S') ≃ₜ LinkVariables S × LinkVariables S' where
  toFun Y := (restrictVariables subset_union_left Y, restrictVariables subset_union_right Y)
  invFun p := open Classical in fun b =>
    if hb : (b : Link a) ∈ S then p.1 ⟨b, hb⟩ else p.2 ⟨b, b.2.resolve_left hb⟩
  left_inv Y := by
    funext b
    by_cases hb : (b : Link a) ∈ S <;> simp [hb, restrictVariables, Set.inclusion]
  right_inv p := by
    refine Prod.ext (funext fun b => ?_) (funext fun b => ?_)
    · simp [restrictVariables, b.2]
    · have hb : (b : Link a) ∉ S := fun hb => Set.disjoint_left.mp h hb b.2
      simp [restrictVariables, hb]
  continuous_toFun := by
    refine Continuous.prodMk (continuous_pi fun b => continuous_apply _)
      (continuous_pi fun b => continuous_apply _)
  continuous_invFun := by
    refine continuous_pi fun b => ?_
    by_cases hb : (b : Link a) ∈ S
    · simp only [hb, dite_true]
      exact (continuous_apply _).comp continuous_fst
    · simp only [hb, dite_false]
      exact (continuous_apply _).comp continuous_snd
def CutoffData.extendByOne (d : CutoffData) {S : Set (Link d.spacing)} (hS : S ⊆ d.links)
    (V : LinkVariables S) : GaugeField d.spacing :=
  gluedField d.spacing_pos hS V (trivialField d.spacing)
theorem CutoffData.extendByOne_of_mem (d : CutoffData) {S : Set (Link d.spacing)}
    (hS : S ⊆ d.links) (V : LinkVariables S) (b : S) : d.extendByOne hS V b = V b :=
  gluedField_apply_of_mem d.spacing_pos hS V _ b
def CutoffData.replaceOn (d : CutoffData) {W : Set (Link d.spacing)} (hW : W ⊆ d.links)
    (V : LinkVariables W) (U : GaugeField d.spacing) : GaugeField d.spacing :=
  gluedField d.spacing_pos hW V U
theorem CutoffData.replaceOn_of_mem (d : CutoffData) {W : Set (Link d.spacing)}
    (hW : W ⊆ d.links) (V : LinkVariables W) (U : GaugeField d.spacing) (b : W) :
    d.replaceOn hW V U b = V b :=
  gluedField_apply_of_mem d.spacing_pos hW V U b
theorem CutoffData.replaceOn_of_notMem (d : CutoffData) {W : Set (Link d.spacing)}
    (hW : W ⊆ d.links) (V : LinkVariables W) (U : GaugeField d.spacing)
    {b : Link d.spacing} (hb : b ∈ d.links \ W) :
    d.replaceOn hW V U b = U b :=
  gluedField_apply_of_notMem d.spacing_pos hW V U hb
section EvaluationMaps
variable {E : Type*}
def ReadsLinks (S : Set (Link a)) (F : GaugeField a → E) : Prop :=
  ∃ f : LinkVariables S → E, ∀ U, F U = f (restrictField U S)
def liftToFields {S : Set (Link a)} (f : LinkVariables S → E) : GaugeField a → E :=
  fun U => f (restrictField U S)
end EvaluationMaps
def IsContinuousLocal (F : GaugeField a → ℂ) : Prop :=
  Continuous F ∧ ∃ S : Set (Link a), S.Finite ∧ S ⊆ positiveLinkSet a ∧ ReadsLinks S F
def continuousVariableFunctions (S : Set (Link a)) : Set (LinkVariables S → ℂ) :=
  {f | Continuous f}
def marginalOn (S : Set (Link a)) (ν : Measure (GaugeField a)) : Measure (LinkVariables S) :=
  ν.map fun U => restrictField U S
def variablesDist {S : Set (Link a)} (V V' : LinkVariables S) : ℝ :=
  ⨆ b : S, Matrices.ComplexMatrix2.operatorNorm
    ((V b : Matrices.ComplexMatrix2) - (V' b : Matrices.ComplexMatrix2))
end YangMills.Construction.CutoffLinks
