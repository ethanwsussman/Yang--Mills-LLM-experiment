import Mathlib

/-!
# The four-dimensional Wilson continuum limit

The reference observable uses one smooth bump and its translate three units away.
Its least positive bare coupling is used both on growing observation tori and in
the infinite-volume limit. The continuum Schwinger distributions satisfy the
Euclidean conditions below on tests flat at collisions. Their components satisfy
the full Osterwalder–Schrader axioms, including spatial clustering.
-/

noncomputable section
open MeasureTheory Set

namespace YangMills.Wilson

abbrev Point := Fin 4 → ℝ

/-- Compact gauge group, normalized real character of the chosen representation,
real Lie algebra dimension, and adjoint Casimir in normalized-trace units. -/
structure GaugeModel where
  Carrier : Type
  [group : Group Carrier]
  [topology : TopologicalSpace Carrier]
  [topologicalGroup : IsTopologicalGroup Carrier]
  [compact : CompactSpace Carrier]
  [t2 : T2Space Carrier]
  normalizedRealTrace : Carrier → ℝ
  lieDim : ℕ
  adjointCasimir : ℝ

attribute [instance] GaugeModel.group GaugeModel.topology GaugeModel.topologicalGroup
  GaugeModel.compact GaugeModel.t2

instance (G : GaugeModel) : MeasurableSpace G.Carrier := borel G.Carrier
instance (G : GaugeModel) : BorelSpace G.Carrier := ⟨rfl⟩

abbrev Site (N : ℕ) := Fin 4 → ZMod N
abbrev Field (G : GaugeModel) (N : ℕ) := Site N → Fin 4 → G.Carrier
abbrev Face (N : ℕ) := {p : Site N × Fin 4 × Fin 4 // p.2.1 < p.2.2}

theorem compact_unitaries (N : ℕ) :
    IsCompact (Matrix.unitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ)) := by
  have box : IsCompact (Set.univ.pi fun _ : Fin N => Set.univ.pi fun _ : Fin N =>
      Metric.closedBall (0 : ℂ) 1 : Set (Matrix (Fin N) (Fin N) ℂ)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine box.of_isClosed_subset (isClosed_unitary (R := Matrix (Fin N) (Fin N) ℂ)) ?_
  intro U hU
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
  exact fun i j => entry_norm_bound_of_unitary hU i j

/-- A closed subgroup of U(N), in its given matrix representation. The Lie dimension
and adjoint Casimir use the inner product −Re tr(XY)/N. -/
def ofMatrixSubgroup {N : ℕ} [NeZero N]
    (H : ClosedSubgroup (Matrix.unitaryGroup (Fin N) ℂ))
    (lieDim : ℕ) (adjointCasimir : ℝ) : GaugeModel := by
  letI : CompactSpace (Matrix.unitaryGroup (Fin N) ℂ) := isCompact_iff_compactSpace.mp (compact_unitaries N)
  exact { Carrier := H.toSubgroup, compact := isCompact_iff_compactSpace.mp H.isClosed'.isCompact
          normalizedRealTrace := fun U => ((U.val : Matrix (Fin N) (Fin N) ℂ).trace).re / N
          lieDim := lieDim, adjointCasimir := adjointCasimir }

/-- Mathlib's SU(N) in its defining representation, with the normalized trace. -/
def specialUnitary (N : ℕ) (_hN : 2 ≤ N := by decide) : GaugeModel := by
  let G := Matrix.specialUnitaryGroup (Fin N) ℂ
  have hclosed : IsClosed {U : Matrix (Fin N) (Fin N) ℂ | U.det = 1} :=
    isClosed_eq (Continuous.matrix_det continuous_id) continuous_const
  haveI : CompactSpace G := isCompact_iff_compactSpace.mp ((compact_unitaries N).inter_right hclosed)
  haveI : IsTopologicalGroup G :=
    { continuous_mul := continuous_mul
      continuous_inv := (Continuous.matrix_conjTranspose (continuous_subtype_val (p := (· ∈ G)))).subtype_mk fun U => (U⁻¹).2 }
  exact { Carrier := G
          normalizedRealTrace := fun U => ((U : Matrix (Fin N) (Fin N) ℂ).trace).re / N
          lieDim := N^2 - 1, adjointCasimir := 2 * (N : ℝ)^2 }

/-- Change the rank here to state the challenge for another SU(N). -/
abbrev selectedGauge := specialUnitary 2

def haar (G : GaugeModel) : Measure G.Carrier := Measure.haarMeasure ⊤

def physicalSide (L m : ℕ) : ℝ := 2 * (L:ℝ)^m
def siteCount (L m K : ℕ) : ℕ := 2 * L^(m+K)
instance (L m K : ℕ) [NeZero L] : NeZero (siteCount L m K) :=
  ⟨mul_ne_zero (by decide) (pow_ne_zero _ (NeZero.ne L))⟩

/-- One minus the normalized real trace of the positively oriented plaquette holonomy. -/
def energy (G : GaugeModel) {N : ℕ} (U : Field G N) (p : Face N) : ℝ :=
  let (x,μ,ν) := p.1
  1 - G.normalizedRealTrace (U x μ * U (x + Pi.single μ 1) ν * (U (x + Pi.single ν 1) μ)⁻¹ * (U x ν)⁻¹)

def action (G : GaugeModel) {N : ℕ} [NeZero N] (U : Field G N) : ℝ := ∑ p : Face N, energy G U p

def law (G : GaugeModel) (N : ℕ) [NeZero N] (β : ℝ) : Measure (Field G N) :=
  let μ := Measure.pi fun _ : Site N => Measure.pi fun _ : Fin 4 => haar G
  let w := fun U : Field G N => Real.exp (-β * action G U)
  μ.withDensity (fun U => ENNReal.ofReal (w U / ∫ V, w V ∂μ))

/-- The finite torus sees the periodic sum of the test at the plaquette barycenter. -/
def smear (G : GaugeModel) (L m K : ℕ) [NeZero L] (f : Point → ℝ) (U : Field G (siteCount L m K)) : ℝ :=
  ∑ p : Face (siteCount L m K), energy G U p *
    ∑' z : Fin 4 → ℤ, f (fun i =>
      (((p.1.1 i).val : ℝ) + (if i = p.1.2.1 then 1/2 else 0) +
        (if i = p.1.2.2 then 1/2 else 0)) * (L:ℝ)^(-(K:ℤ)) + physicalSide L m * (z i:ℝ))

def centeredMoment (G : GaugeModel) (L m K : ℕ) [NeZero L] (β : ℝ) {n : ℕ} (f : Fin n → Point → ℝ) : ℝ :=
  let μ := law G (siteCount L m K) β
  ∫ U, ∏ i, (smear G L m K (f i) U - ∫ V, smear G L m K (f i) V ∂μ) ∂μ

def bump (x : Point) : ℝ := Real.smoothTransition (2 - ∑ i, ((32 / (6/5 : ℝ)) * x i)^2)
def translatedBump (x : Point) : ℝ := bump (x - Pi.single 0 3)

def referenceResponse (G : GaugeModel) (L M K : ℕ) [NeZero L] (β : ℝ) : ℝ :=
  centeredMoment G L M K β ![bump, translatedBump]

def fixedPhysicalLevel (G : GaugeModel) (g₀ : ℝ) : ℝ :=
  (3 * (G.lieDim : ℝ) * g₀^4 / Real.pi^4) * ∫ x : Point, ∫ y : Point,
    bump x * translatedBump y / (Real.sqrt (∑ i, (x i-y i)^2))^8

def couplingsAt (G : GaugeModel) (L M K : ℕ) [NeZero L] (g₀ : ℝ) : Set ℝ :=
  {g | 0 < g ∧ referenceResponse G L M K (g^2)⁻¹ = fixedPhysicalLevel G g₀}

def bareCoupling (G : GaugeModel) (L M K : ℕ) [NeZero L] (g₀ : ℝ) : ℝ :=
  sInf (couplingsAt G L M K g₀)

end YangMills.Wilson
end

noncomputable section
open scoped ContDiff ENNReal ComplexConjugate
namespace YangMills.WilsonOS

abbrev Point := Fin 4 → ℝ
abbrev Config (n : ℕ) := Fin n → Point
abbrev Test (n : ℕ) := Config n → ℂ
abbrev Family := (n : ℕ) → Test n → ℂ
abbrev Index (n : ℕ) := Fin n → Fin 4 → ℕ

/-- The coordinate partial derivative with multi-index α. -/
def partialDeriv {n : ℕ} (α : Index n) (f : Test n) : Test n :=
  (List.finRange n).foldr (fun i h => (List.finRange 4).foldr
    (fun μ g => (fun (u : Test n) x => lineDeriv ℝ u x (Pi.single i (Pi.single μ 1)))^[α i μ] g) h) f

/-- The Schwartz seminorm of order k, with the Euclidean norm on configuration space. -/
def seminorm {n : ℕ} (k : ℕ) (f : Test n) : ℝ≥0∞ :=
  ⨆ (x : Config n) (α : Index n) (_ : (∑ i, ∑ μ, α i μ) ≤ k),
    ENNReal.ofReal ((1 + ∑ i, ∑ μ, x i μ ^ 2) ^ ((k : ℝ) / 2) * ‖partialDeriv α f x‖)

/-- A Schwartz test whose derivatives of all orders vanish outside U. -/
def FlatOutside {n : ℕ} (U : Set (Config n)) (f : Test n) : Prop :=
  ContDiff ℝ ∞ f ∧ (∀ k : ℕ, 1 ≤ k → seminorm k f < ⊤) ∧
    ∀ x ∉ U, ∀ α : Index n, partialDeriv α f x = 0

def Flat {n : ℕ} (f : Test n) := FlatOutside {x | Function.Injective x} f
def PositiveTime {n : ℕ} (f : Test n) :=
  FlatOutside {x | Function.Injective x ∧ ∀ i, 0 < x i 3} f
def reflect (x : Point) : Point := ![x 0, x 1, x 2, -x 3]
def reflectConj {n : ℕ} (f : Test n) : Test n := fun x => conj (f fun i => reflect (x i))
def tensor {n : ℕ} (f : Fin n → Point → ℝ) : Test n := fun x => ∏ i, (f i (x i) : ℂ)
def reflectedProduct {p q : ℕ} (f : Test p) (g : Test q) : Test (p + q) :=
  fun z => reflectConj f (fun i => z (Fin.castAdd q i)) * g (fun j => z (Fin.natAdd p j))

abbrev Sequence := (n : ℕ) → Test n
def Admissible (Φ : Sequence) : Prop :=
  (∀ n, PositiveTime (Φ (n+1))) ∧ {n | Φ n ≠ 0}.Finite
def pairing (S : Family) (Φ Ψ : Sequence) : ℂ :=
  ∑ᶠ p : ℕ × ℕ, S (p.1+p.2) (reflectedProduct (Φ p.1) (Ψ p.2))
def translate {n : ℕ} (w : Point) (f : Test n) : Test n := fun x => f fun i => x i - w

/-- Euclidean distribution axioms inherited by a mixture of phases. -/
structure EuclideanAxioms (S : Family) : Prop where
  normalized : ∀ f : Test 0, S 0 f = f Fin.elim0
  linear : ∀ (n : ℕ) (f g : Test (n+1)) (a b : ℂ), Flat f → Flat g →
    S (n+1) (a • f + b • g) = a * S (n+1) f + b * S (n+1) g
  growth : ∃ (k : ℕ) (c C s : ℝ), 0 < k ∧ 0 < c ∧ 0 < C ∧ 0 < s ∧
    ∀ (n : ℕ) (f : Test (n+1)), Flat f → ‖S (n+1) f‖ ≤
      c * C ^ (n+1) * ((n+1).factorial : ℝ)^s * (seminorm (k*(n+1)) f).toReal
  euclidean : ∀ (n : ℕ) (f : Test (n+1)), Flat f →
    ∀ R ∈ Matrix.orthogonalGroup (Fin 4) ℝ, ∀ v : Point,
    S (n+1) (fun x => f fun i => R⁻¹.mulVec (x i - v)) = S (n+1) f
  permutation : ∀ (n : ℕ) (f : Test (n+1)), Flat f → ∀ π : Equiv.Perm (Fin (n+1)),
    S (n+1) (fun x => f fun i => x (π i)) = S (n+1) f
  reflectionReal : ∀ (n : ℕ) (f : Test (n+1)), Flat f → S (n+1) (reflectConj f) = conj (S (n+1) f)
  reflectionPositive : ∀ Φ, Admissible Φ → (pairing S Φ Φ).im = 0 ∧ 0 ≤ (pairing S Φ Φ).re

open Filter Topology in
/-- The full Osterwalder–Schrader axioms, including clustering along spatial rays. -/
structure Axioms (S : Family) : Prop extends EuclideanAxioms S where
  cluster : ∀ Φ Ψ, Admissible Φ → Admissible Ψ → ∀ v : Point, v 3 = 0 → v ≠ 0 →
    Tendsto (fun t : ℝ => pairing S Φ (fun n => translate (t • v) (Ψ n))) atTop
      (𝓝 ((∑ᶠ n, S n (reflectConj (Φ n))) * ∑ᶠ n, S n (Ψ n)))

end YangMills.WilsonOS
end

noncomputable section
open Filter Set
open scoped Topology ContDiff

namespace YangMills.Wilson

/-- Smooth real tests with compact, pairwise disjoint supports in four-space. -/
def Separated {n : ℕ} (f : Fin n → Point → ℝ) : Prop :=
  (∀ i, ContDiff ℝ ∞ (f i) ∧ HasCompactSupport (f i)) ∧
    Pairwise fun i j => Disjoint (tsupport (f i)) (tsupport (f j))

open Classical in
/-- Connected correlations from the moments by the moment–cumulant formula. -/
def connected (S : WilsonOS.Family) {n : ℕ} (f : Fin n → Point → ℝ) : ℝ :=
  ∑ P ∈ Finset.univ.filter (fun P : Finset (Finset (Fin n)) =>
      (∀ B ∈ P, B.Nonempty) ∧ (P : Set (Finset (Fin n))).PairwiseDisjoint id ∧ P.biUnion id = Finset.univ),
    (-1 : ℝ)^(P.card-1) * ((P.card-1).factorial : ℝ) *
      ∏ B ∈ P, (S B.card (WilsonOS.tensor fun i => f (B.orderEmbOfFin rfl i))).re

open MeasureTheory in
/-- The continuum moments are the barycenter of components satisfying all OS axioms. -/
def HasOSDecomposition (S : WilsonOS.Family) : Prop :=
  ∃ (Ξ : Type) (_ : MeasurableSpace Ξ) (μ : Measure Ξ) (T : Ξ → WilsonOS.Family),
    IsProbabilityMeasure μ ∧ (∀ ξ, WilsonOS.Axioms (T ξ)) ∧
    (∀ n (f : Fin n → Point → ℝ), Separated f →
      Integrable (fun ξ => T ξ n (WilsonOS.tensor f)) μ ∧
      S n (WilsonOS.tensor f) = ∫ ξ, T ξ n (WilsonOS.tensor f) ∂μ) ∧
    ∀ᵐ ξ ∂μ, ∃ f : Fin 4 → Point → ℝ, Separated f ∧ connected (T ξ) f ≠ 0

end YangMills.Wilson
end

noncomputable section
open Filter Set
open scoped Topology ContDiff

namespace YangMills.Wilson

/-- The continuum limit on four-space, with the bare coupling selected by
the smallest positive solution of the fixed two-point reference equation. -/
def ContinuumLimitFor (G : GaugeModel) : Prop :=
    ∃ L₀ : ℕ, ∀ L : ℕ+, Odd (L:ℕ) → L₀ ≤ (L:ℕ) →
      ∃ (M : ℕ+) (δ : ℝ), 8 ≤ physicalSide L M ∧ 0 < δ ∧
        (∀ᶠ k : ℕ in atTop, ∀ g₀ ∈ Ioo (0:ℝ) δ,
          IsLeast (couplingsAt G L M k g₀) (bareCoupling G L M k g₀)) ∧
        ∀ g₀ ∈ Ioo (0:ℝ) δ, let g := fun k : ℕ => bareCoupling G L M k g₀
          ∃ (K m : ℕ → ℕ+) (v : ℕ → ℕ → ℕ+) (S : WilsonOS.Family), StrictMono K ∧
            Tendsto (fun j => physicalSide L (m j)) atTop atTop ∧
            (∀ j, Tendsto (fun t => physicalSide L (v j t)) atTop atTop) ∧
            (∀ j, IsLeast (couplingsAt G L M (K j) g₀) (g (K j))) ∧
            Tendsto (fun j => g (K j)^2 * (K j:ℝ) * Real.log (L:ℝ)) atTop (𝓝 (24 * Real.pi^2 / (11 * G.adjointCasimir))) ∧
            (∀ n (f : Fin n → Point → ℝ), Separated f → ∃ z : ℕ → ℂ,
              (∀ j, Tendsto (fun t => (centeredMoment G L (v j t) (K j) ((g (K j))^2)⁻¹ f : ℂ))
                atTop (𝓝 (z j))) ∧ Tendsto z atTop (𝓝 (S n (WilsonOS.tensor f))) ∧
              Tendsto (fun j => (centeredMoment G L (m j) (K j) ((g (K j))^2)⁻¹ f : ℂ))
                atTop (𝓝 (S n (WilsonOS.tensor f)))) ∧
            WilsonOS.EuclideanAxioms S ∧ HasOSDecomposition S ∧
            (∃ f : Fin 2 → Point → ℝ, Separated f ∧ 0 < (S 2 (WilsonOS.tensor f)).re) ∧
            ∃ f : Fin 4 → Point → ℝ, Separated f ∧ 0 < connected S f

end YangMills.Wilson
end

namespace YangMills

/-- The Wilson continuum limit for the gauge group chosen above. -/
theorem wilson_subsequence : Wilson.ContinuumLimitFor Wilson.selectedGauge := by
  sorry

end YangMills
