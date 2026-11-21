import YangMills.Construction.HilbertSpace.FormsAndOperators
import YangMills.Construction.SpectralTheory.FunctionalCalculus
import Mathlib
set_option autoImplicit false
open Filter Topology
open scoped NNReal InnerProductSpace ComplexOrder
noncomputable section
namespace YangMills.Construction
namespace SpectralTheory
open HilbertSpaceBasics (ofBounded)
def zeroPoint : BorelSets 1 :=
  ⟨{0}, measurableSet_singleton 0⟩
def coordProj {n : ℕ} (r : Fin n) (x : Fin n → ℝ) : Fin 1 → ℝ :=
  fun _ => x r
theorem measurable_coordProj {n : ℕ} (r : Fin n) :
    Measurable (coordProj r) :=
  measurable_pi_iff.mpr fun _ => measurable_pi_apply r
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def toBounded (T : UnboundedOperator H) : H →L[ℂ] H :=
  Classical.epsilon fun B => T = ofBounded B
namespace ProjectionMeasure
def unitaryFlow (P : ProjectionMeasure 1 H) (s : ℝ) : H →L[ℂ] H :=
  toBounded (P.expIMulOp s)
def contractionFlow (P : ProjectionMeasure 1 H) (t : ℝ≥0) : H →L[ℂ] H :=
  toBounded (P.expNegMulOp t)
structure UnitaryFlowFacts (P : ProjectionMeasure 1 H) : Prop where
  expIMulOp_eq : ∀ s, P.expIMulOp s = ofBounded (P.unitaryFlow s)
  flow_zero : P.unitaryFlow 0 = 1
  flow_add : ∀ s s', P.unitaryFlow s * P.unitaryFlow s' = P.unitaryFlow (s + s')
  star_flow : ∀ s, star (P.unitaryFlow s) = P.unitaryFlow (-s)
  flow_isometry : ∀ s, ∃ V : H ≃ₗᵢ[ℂ] H, ∀ v, P.unitaryFlow s v = V v
  flow_continuous : StronglyContinuous P.unitaryFlow
  mem_domain_iff_bdd : ∀ v : H, v ∈ (P.coordinateOp 0).domain ↔
    BddAbove ((fun s : ℝ => |s|⁻¹ * ‖P.unitaryFlow s v - v‖) '' {s | 0 < |s| ∧ |s| ≤ 1})
  tendsto_derivQuot : ∀ v : (P.coordinateOp 0).domain,
    Tendsto (fun s : ℝ => (Complex.I * (s : ℂ))⁻¹ • (P.unitaryFlow s v - v)) (𝓝[≠] 0)
      (𝓝 (P.coordinateOp 0 v))
  flow_preserves_domain : ∀ (s : ℝ) (v : (P.coordinateOp 0).domain),
    ∃ h : P.unitaryFlow s v ∈ (P.coordinateOp 0).domain,
      P.coordinateOp 0 ⟨P.unitaryFlow s v, h⟩ =
        P.unitaryFlow s (P.coordinateOp 0 v)
  concentrated_nonneg_iff : P.IsConcentratedOn nonnegReals ↔
    ∀ v : (P.coordinateOp 0).domain, 0 ≤ ⟪(v : H), P.coordinateOp 0 v⟫_ℂ
structure ContractionFlowFacts (P : ProjectionMeasure 1 H) : Prop where
  expNegMulOp_eq : ∀ t, P.expNegMulOp t = ofBounded (P.contractionFlow t)
  flow_selfAdjoint : ∀ t, IsSelfAdjoint (P.contractionFlow t)
  flow_nonneg : ∀ t, LoewnerGe (P.contractionFlow t) 0
  flow_le_one : ∀ t, LoewnerGe 1 (P.contractionFlow t)
  flow_zero : P.contractionFlow 0 = 1
  flow_add : ∀ t t', P.contractionFlow t * P.contractionFlow t' = P.contractionFlow (t + t')
  mem_domain_iff_bdd : ∀ v : H, v ∈ (P.coordinateOp 0).domain ↔
    BddAbove ((fun t : ℝ≥0 => (t : ℝ)⁻¹ * ‖v - P.contractionFlow t v‖) '' {t | 0 < t ∧ t ≤ 1})
  tendsto_derivQuot : ∀ v : (P.coordinateOp 0).domain,
    Tendsto (fun t : ℝ≥0 => ((t : ℝ) : ℂ)⁻¹ • ((v : H) - P.contractionFlow t v)) (𝓝[>] 0)
      (𝓝 (P.coordinateOp 0 v))
  inner_generator_nonneg : ∀ v : (P.coordinateOp 0).domain,
    0 ≤ ⟪(v : H), P.coordinateOp 0 v⟫_ℂ
  kernel_eq_range_atom : opKernel (P.coordinateOp 0) = Set.range (P zeroPoint)
  kernel_eq_fixedPoints : opKernel (P.coordinateOp 0) = {v | ∀ t, P.contractionFlow t v = v}
  tendsto_atom : TendstoStrongly atTop P.contractionFlow (P zeroPoint)
structure DeterminedBy (P : ProjectionMeasure 1 H) : Prop where
  eq_of_expIMulOp : ∀ Q : ProjectionMeasure 1 H, (∀ s, Q.expIMulOp s = P.expIMulOp s) → Q = P
  eq_of_generator : ∀ Q : ProjectionMeasure 1 H,
    Q.coordinateOp 0 = P.coordinateOp 0 → Q = P
  eq_of_expNegMulOp : ∀ Q : ProjectionMeasure 1 H, P.IsConcentratedOn nonnegReals →
    Q.IsConcentratedOn nonnegReals →
      (∀ t : ℝ≥0, 0 < t → t ≤ 1 → Q.expNegMulOp t = P.expNegMulOp t) → Q = P
def CommutesWithFlows (P : ProjectionMeasure 1 H) (B : H →L[ℂ] H) : Prop :=
  (∀ s, Commute B (P.unitaryFlow s)) ∨
    (P.IsConcentratedOn nonnegReals ∧
      ∀ t : ℝ≥0, 0 < t → t ≤ 1 → Commute B (P.contractionFlow t))
def GeneratorCommutant (P : ProjectionMeasure 1 H) : Prop :=
  ∀ B : H →L[ℂ] H, P.CommutesWithFlows B →
    (∀ v : (P.coordinateOp 0).domain,
      ∃ h : B v ∈ (P.coordinateOp 0).domain,
        P.coordinateOp 0 ⟨B v, h⟩ = B (P.coordinateOp 0 v)) ∧
    ∀ V : H ≃ₗᵢ[ℂ] H, (∀ v, B v = V v) → unitaryConj V (P.coordinateOp 0) = P.coordinateOp 0
structure MarginalFacts {n : ℕ} [NeZero n] (E : ProjectionMeasure n H) : Prop where
  coordinateOp_eq_marginal : ∀ r : Fin n, ∃ G : ProjectionMeasure 1 H,
    (∀ A, G A = E.pushforward (coordProj r) (measurable_coordProj r) A) ∧
      E.coordinateOp r = G.coordinateOp 0
  marginals_commute : ∀ (r s : Fin n) (A A' : BorelSets 1),
    Commute (E.pushforward (coordProj r) (measurable_coordProj r) A)
      (E.pushforward (coordProj s) (measurable_coordProj s) A')
  eq_of_coordinateOps : ∀ E' : ProjectionMeasure n H,
    (∀ r, E'.coordinateOp r = E.coordinateOp r) → E' = E
end ProjectionMeasure
end SpectralTheory
namespace GeneratorsAndFlows
open SpectralTheory
def GeneratorFlowTheorem : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    (∀ P : ProjectionMeasure 1 H,
      P.UnitaryFlowFacts ∧ (P.IsConcentratedOn nonnegReals → P.ContractionFlowFacts) ∧
        P.DeterminedBy ∧ P.GeneratorCommutant) ∧
      ∀ (n : ℕ) [NeZero n] (E : ProjectionMeasure n H), E.MarginalFacts
end GeneratorsAndFlows
end YangMills.Construction
