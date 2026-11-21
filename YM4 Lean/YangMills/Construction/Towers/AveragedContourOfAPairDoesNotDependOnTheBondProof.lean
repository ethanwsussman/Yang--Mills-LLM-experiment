import YangMills.Construction.Towers.AveragedContourOfAPairDoesNotDependOnTheBond
import YangMills.Construction.Towers.BlocksStraightPathsContoursAndPivotBondsOfATower
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.PairContourIndependence
section FiniteSide
variable {L n k j : ℕ}
theorem pathHolonomy_congr {U U' : Edge L n k j → Matrices.ComplexMatrix2} {γ : List (Edge L n k j)}
    (h : ∀ e ∈ γ, U e = U' e) : PeriodicLattice.pathHolonomy U γ = PeriodicLattice.pathHolonomy U' γ := by
  simp only [PeriodicLattice.pathHolonomy, List.map_congr_left h]
theorem edge_ends_mem_unitBlock (hS : BlockPathContourPivotStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j < k) {y : Vertex L n k (j + 1)}
    {x : Vertex L n k j} (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y)
    {γ : List (Edge L n k j)} (hγ : γ ∈ PeriodicLattice.contourSet y x) {e : Edge L n k j}
    (he : e ∈ γ) :
    (e.source : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y ∧
      (e.target : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y := by
  obtain ⟨hpart, -, -, -, -, hc⟩ := (hS L hL k 1 (j + 1) (by omega) (by omega) (by omega)).1 n hn
  have hmem : (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.refinedBlock 1 y := hx
  rw [hpart.eq_image y] at hmem
  obtain ⟨ν, hν, hxν⟩ := hmem
  obtain ⟨-, -, -, -, hs⟩ := ((hc (by omega)).1.contours y ν hν x hxν.symm).2 γ hγ
  exact ⟨hs e.source (Or.inr (Or.inr ⟨e, he, Or.inl rfl⟩)),
    hs e.target (Or.inr (Or.inr ⟨e, he, Or.inr rfl⟩))⟩
theorem complexMeanContourHolonomy_congr (hS : BlockPathContourPivotStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j < k) {ρ : ℝ}
    {c : Edge L n k (j + 1)} (hp : DoubleBlockPolydisc.PolydiscPropertiesAt ρ c)
    {y : Vertex L n k (j + 1)} (hy : y ∈ ({c.source, c.target} : Set (Vertex L n k (j + 1))))
    {x : Vertex L n k j} (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y)
    {V U : Edge L n k j → Matrices.ComplexMatrix2}
    (hU : AgreesOn (DoubleBlockPolydisc.doubleBlockBonds c) V U) :
    PeriodicLattice.complexMeanContourHolonomy U y x =
      PeriodicLattice.complexMeanContourHolonomy V y x := by
  have hsub : PeriodicLattice.unitBlock y ⊆
      PeriodicLattice.unitBlock c.source ∪ PeriodicLattice.unitBlock c.target := by
    rcases hy with rfl | rfl
    · exact subset_union_left
    · exact subset_union_right
  have hval : PeriodicLattice.contourHolonomies U y x = PeriodicLattice.contourHolonomies V y x := by
    funext σ
    refine pathHolonomy_congr fun e he => hU e ?_
    obtain ⟨h₁, h₂⟩ := edge_ends_mem_unitBlock hS hL hn hj hx ⟨σ, rfl⟩ he
    rw [hp.doubleBlockBonds_eq]
    exact ⟨hsub h₁, hsub h₂⟩
  unfold PeriodicLattice.complexMeanContourHolonomy
  rw [hval]
theorem agreesOn_mem_nearIdentityPolydisc {ρ : ℝ} {c : Edge L n k (j + 1)}
    (hp : DoubleBlockPolydisc.PolydiscPropertiesAt ρ c) {V U : Edge L n k j → Matrices.ComplexMatrix2}
    (hV : PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup univ V)
    (hρ : ∀ e ∈ DoubleBlockPolydisc.doubleBlockBonds c,
      Matrices.ComplexMatrix2.operatorNorm (V e - 1) < ρ)
    (hU : AgreesOn (DoubleBlockPolydisc.doubleBlockBonds c) V U) :
    U ∈ nearIdentityPolydisc ρ c := by
  refine ⟨⟨fun e he => ?_, fun e he => ?_⟩, fun e he => ?_⟩
  · rw [hU e he]
    exact hV.1 e (mem_univ _)
  · rw [hU e he, hU _ (hp.finite_open.opposite_mem e he)]
    exact hV.2 e (mem_univ _)
  · rw [hU e he]
    exact hρ e he
end FiniteSide
namespace Infinite
open YangMills.Construction.Tower.FullSpace
variable {L k j : ℕ}
theorem linkHolonomy_congr {a : ℝ} {U U' : InfiniteLattice.Link a → Matrices.ComplexMatrix2}
    {γ : List (InfiniteLattice.Link a)} (h : ∀ e ∈ γ, U e = U' e) :
    linkHolonomy U γ = linkHolonomy U' γ := by
  simp only [linkHolonomy, List.map_congr_left h]
theorem edge_ends_mem_cube (hS : BlockPathContourPivotStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) {y : FullSpace.Vertex L k (j + 1)}
    {x : FullSpace.Vertex L k j} (hx : x ∈ cubeVertices L (meshAt L k j) y)
    {γ : List (FullSpace.Edge L k j)} (hγ : γ ∈ contourSet L y x) {e : FullSpace.Edge L k j}
    (he : e ∈ γ) :
    (e.initial : InfiniteLattice.AmbientSpace) ∈ cube L (meshAt L k j) y ∧
      (e.terminal : InfiniteLattice.AmbientSpace) ∈ cube L (meshAt L k j) y := by
  obtain ⟨hpart, -, -, -, -, hc⟩ := (hS L hL k 1 (j + 1) (by omega) (by omega) (by omega)).2
  have hmem : (x : InfiniteLattice.AmbientSpace) ∈ cubeOfOrder L (meshAt L k (j + 1 - 1)) 1 y := hx
  rw [hpart.eq_image y] at hmem
  obtain ⟨ν, hν, hxν⟩ := hmem
  obtain ⟨-, -, -, -, hs⟩ := ((hc (by omega)).1.contours y ν hν x hxν.symm).2 γ hγ
  exact ⟨hs e.initial (Or.inr (Or.inr ⟨e, he, Or.inl rfl⟩)),
    hs e.terminal (Or.inr (Or.inr ⟨e, he, Or.inr rfl⟩))⟩
theorem complexContourMean_congr (hS : BlockPathContourPivotStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) {ρ : ℝ}
    {c : FullSpace.Edge L k (j + 1)} (hp : DoubleBlockPolydisc.Infinite.PolydiscPropertiesAt L k j ρ c)
    {y : FullSpace.Vertex L k (j + 1)}
    (hy : y ∈ ({c.initial, c.terminal} : Set (FullSpace.Vertex L k (j + 1))))
    {x : FullSpace.Vertex L k j} (hx : x ∈ cubeVertices L (meshAt L k j) y)
    {V U : FullSpace.Edge L k j → Matrices.ComplexMatrix2}
    (hU : AgreesOn (DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c) V U) :
    complexContourMean L U y x = complexContourMean L V y x := by
  have hsub : cube L (meshAt L k j) y ⊆
      cube L (meshAt L k j) c.initial ∪ cube L (meshAt L k j) c.terminal := by
    rcases hy with rfl | rfl
    · exact subset_union_left
    · exact subset_union_right
  have hval : contourHolonomies L U y x = contourHolonomies L V y x := by
    funext σ
    refine linkHolonomy_congr fun e he => hU e ?_
    obtain ⟨h₁, h₂⟩ := edge_ends_mem_cube hS hL hj hx ⟨σ, rfl⟩ he
    rw [hp.doubleBlockBonds_eq]
    exact ⟨hsub h₁, hsub h₂⟩
  unfold complexContourMean
  rw [hval]
theorem agreesOn_mem_nearIdentityPolydisc {ρ : ℝ} {c : FullSpace.Edge L k (j + 1)}
    (hp : DoubleBlockPolydisc.Infinite.PolydiscPropertiesAt L k j ρ c)
    {V U : FullSpace.Edge L k j → Matrices.ComplexMatrix2}
    (hV : IsFieldIn PeriodicLattice.complexGaugeGroup V)
    (hρ : ∀ e ∈ DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c,
      Matrices.ComplexMatrix2.operatorNorm (V e - 1) < ρ)
    (hU : AgreesOn (DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c) V U) :
    U ∈ FullSpace.nearIdentityPolydisc L k j ρ c := by
  refine ⟨⟨fun e he => ?_, fun e he => ?_⟩, fun e he => ?_⟩
  · rw [hU e he]
    exact hV.1 e
  · rw [hU e he, hU _ (hp.finite_open.opposite_mem e he)]
    exact hV.2 e
  · rw [hU e he]
    exact hρ e he
end Infinite
theorem statement_holds (hP : DoubleBlockPolydisc.PolydiscsHold)
    (hS : BlockPathContourPivotStatement) : Statement := by
  intro L hL k j hj
  refine ⟨fun n hn y x hx c c' hc hc' hy hy' V' hV hρ hρ' U U' hU hU' => ?_,
    fun y x hx c c' hc hc' hy hy' V' hV hρ hρ' U U' hU hU' => ?_⟩
  · have hp := (hP L hL k j hj).1 n hn c hc
    have hp' := (hP L hL k j hj).1 n hn c' hc'
    exact ⟨agreesOn_mem_nearIdentityPolydisc hp hV hρ hU,
      agreesOn_mem_nearIdentityPolydisc hp' hV hρ' hU',
      (complexMeanContourHolonomy_congr hS hL hn hj hp hy hx hU).trans
        (complexMeanContourHolonomy_congr hS hL hn hj hp' hy' hx hU').symm⟩
  · have hp := (hP L hL k j hj).2 c hc
    have hp' := (hP L hL k j hj).2 c' hc'
    exact ⟨Infinite.agreesOn_mem_nearIdentityPolydisc hp hV hρ hU,
      Infinite.agreesOn_mem_nearIdentityPolydisc hp' hV hρ' hU',
      (Infinite.complexContourMean_congr hS hL hj hp hy hx hU).trans
        (Infinite.complexContourMean_congr hS hL hj hp' hy' hx hU').symm⟩
end YangMills.Construction.Tower.PairContourIndependence
end
