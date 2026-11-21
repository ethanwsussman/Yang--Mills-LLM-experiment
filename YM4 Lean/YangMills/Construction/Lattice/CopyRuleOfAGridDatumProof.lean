import YangMills.Construction.Lattice.CopyRuleOfAGridDatum
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.GridCopyRule
variable {L : ℕ} {κ : ℤ}
def conjIf {X : Type} (ε : ℝ) (G : X → ℂ) : X → ℂ :=
  open Classical in
  if ε = 1 then G else fun U => starRingEnd ℂ (G U)
theorem conjIf_one {X : Type} (G : X → ℂ) : conjIf 1 G = G := if_pos rfl
theorem conjIf_neg_one {X : Type} (G : X → ℂ) :
    conjIf (-1) G = fun U => starRingEnd ℂ (G U) :=
  if_neg (by norm_num)
theorem conjIf_conjIf {X : Type} {ε ε' : ℝ} (hε : ε = 1 ∨ ε = -1) (hε' : ε' = 1 ∨ ε' = -1)
    (G : X → ℂ) : conjIf ε (conjIf ε' G) = conjIf (ε * ε') G := by
  rcases hε with rfl | rfl <;> rcases hε' with rfl | rfl <;>
    simp only [mul_one, conjIf_one, conjIf_neg_one, mul_neg, neg_neg]
  simp
theorem checkerboardCopy_eq_conjIf (d : CellGrid L κ) (c c' : d.spaceCells)
    (F : d.cellObservables c) :
    d.checkerboardCopy c c' F = conjIf (d.inducedSign (d.cellTransporter c.1 c'.1))
      ((d.symmetryOfMap (d.cellTransporter c.1 c'.1)).actOnObservables F.1) :=
  rfl
theorem gridSymmetry_ext {d : CellGrid L κ} {g h : d.GridSymmetry}
    (e : g.toFun = h.toFun) : g = h := by
  cases g
  cases h
  cases e
  rfl
theorem actOnObservables_conjIf {d : CellGrid L κ}
    (hA : GroupAndCells.ObservableAction d) (g : d.GridSymmetry)
    {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (G : d.GaugeConfig → ℂ) :
    g.actOnObservables (conjIf ε G) = conjIf ε (g.actOnObservables G) := by
  rcases hε with rfl | rfl
  · simp only [conjIf_one]
  · simp only [conjIf_neg_one]
    exact (hA.2.1 g).2.2 G
theorem edgeImage_of_toFun_eq_id {d : CellGrid L κ} (g : d.GridSymmetry)
    (e : g.toFun = fun x => x) (b : d.DirectedEdge) : g.edgeImage b = b := by
  have hx : ∀ x : d.GridPoint, g.pointImage x = x := fun x => Subtype.ext (congrFun e x.1)
  unfold CellGrid.GridSymmetry.edgeImage
  split_ifs with hb
  · cases b
    simp only [hx]
  · rfl
theorem actOnObservables_of_toFun_eq_id {d : CellGrid L κ} (g : d.GridSymmetry)
    (e : g.toFun = fun x => x) {X : Type} (F : d.GaugeConfig → X) :
    g.actOnObservables F = F := by
  funext U
  show F (g.pullback U) = F U
  congr 1
  funext b
  show BoxTorus.edgeVariable U (g.edgeImage b.1) = U b
  rw [edgeImage_of_toFun_eq_id g e, BoxTorus.edgeVariable, dif_pos b.2]
theorem checkerboardCopy_of_mapsCellTo (d : CellGrid L κ) (hG : GroupAndCells.AllHold)
    (c c' c'' : d.spaceCells) (F : d.cellObservables c) {h : d.Space → d.Space}
    (hh : h ∈ d.inducedGroupMaps) (hc : c''.1 = h '' c'.1) :
    d.checkerboardCopy c c'' F =
      conjIf (d.inducedSign h)
        ((d.symmetryOfMap h).actOnObservables (d.checkerboardCopy c c' F)) := by
  obtain ⟨-, hInd, -, hCells, hSgn, -, hAct⟩ := hG L κ d
  have hgc := (hCells.2 c.1 c.2 c'.1 c'.2).2
  set g := d.cellTransporter c.1 c'.1 with hg
  have hhg : h ∘ g ∈ d.inducedGroupMaps := hInd.2.2.2.1 h hh g hgc.1
  have hmaps : d.MapsCellTo (h ∘ g) c.1 c''.1 :=
    ⟨hhg, by rw [Set.image_comp, hgc.2, hc]⟩
  have huniq := (hCells.2 c.1 c.2 c''.1 c''.2)
  have e : d.cellTransporter c.1 c''.1 = h ∘ g := huniq.1.unique huniq.2 hmaps
  have hsg := hSgn.2.2.1 g hgc.1
  have hsh := hSgn.2.2.1 h hh
  have hsym : d.symmetryOfMap (h ∘ g) =
      (d.symmetryOfMap h).compose (d.symmetryOfMap g) := by
    apply gridSymmetry_ext
    show (d.symmetryOfMap (h ∘ g)).toFun =
      (d.symmetryOfMap h).toFun ∘ (d.symmetryOfMap g).toFun
    rw [hInd.2.1 _ hhg, hInd.2.1 _ hh, hInd.2.1 _ hgc.1]
  rw [checkerboardCopy_eq_conjIf d c c'', checkerboardCopy_eq_conjIf d c c', ← hg, e,
    hSgn.2.2.2 h hh g hgc.1, hsym,
    actOnObservables_conjIf hAct _ hsg, conjIf_conjIf hsh hsg,
    ((hAct.1 (d.symmetryOfMap h) (d.symmetryOfMap g)).2 ℂ F.1)]
theorem checkerboardCopy_mem (d : CellGrid L κ) (hG : GroupAndCells.AllHold)
    (c c' : d.spaceCells) (F : d.cellObservables c) :
    d.checkerboardCopy c c' F ∈ d.cellObservables c' := by
  obtain ⟨-, hInd, -, hCells, hSgn, -, hAct⟩ := hG L κ d
  have hgc := (hCells.2 c.1 c.2 c'.1 c'.2).2
  have hto := hInd.2.1 _ hgc.1
  have hT : (d.symmetryOfMap (d.cellTransporter c.1 c'.1)).actOnObservables F.1 ∈
      d.cellObservables c' := by
    rw [← hAct.2.2 (d.symmetryOfMap (d.cellTransporter c.1 c'.1)) (by rw [hto]; exact hgc.1) c c'
      (by rw [hto]; exact hgc.2.symm)]
    exact ⟨F.1, F.2, rfl⟩
  rcases hSgn.2.2.1 _ hgc.1 with hs | hs
  · rw [d.checkerboardCopy_of_inducedSign_eq_one F hs]
    exact hT
  · rw [d.checkerboardCopy_of_inducedSign_eq_neg_one F hs]
    exact d.conj_mem_cellObservables c' hT
theorem linearSign_faceReflectEquiv (d : CellGrid L κ) (μ : Fin 4) (a : ℤ)
    (hg : d.faceReflectEquiv μ a ∈ d.reflectionGroup) :
    d.linearSign ⟨d.faceReflectEquiv μ a, hg⟩ = -1 := by
  have hl : ((d.faceReflectEquiv μ a).linear :
      InfiniteLattice.AmbientSpace →ₗ[ℝ] InfiniteLattice.AmbientSpace) =
      Matrix.toLin' (Matrix.diagonal (CellGrid.flipDiag μ)) := rfl
  show LinearMap.det ((d.faceReflectEquiv μ a).linear :
    InfiniteLattice.AmbientSpace →ₗ[ℝ] InfiniteLattice.AmbientSpace) = -1
  rw [hl, LinearMap.det_toLin', Matrix.det_diagonal]
  fin_cases μ <;> simp [CellGrid.flipDiag, Function.update]
theorem copyRuleHolds (hG : GroupAndCells.AllHold) : CopyRuleHolds := by
  intro L κ d c c' F
  refine ⟨checkerboardCopy_mem d hG c c' F, ?_, ?_, ?_, ?_⟩
  · intro h hh c'' hc
    have key := checkerboardCopy_of_mapsCellTo d hG c c' c'' F hh hc
    refine ⟨fun hs => ?_, fun hs => ?_⟩
    · rw [key, hs, conjIf_one]
    · rw [key, hs, conjIf_neg_one]
  · obtain ⟨-, hInd, -, hCells, hSgn, -, -⟩ := hG L κ d
    have hid := hInd.2.2.1
    have huniq := hCells.2 c.1 c.2 c.1 c.2
    have e : d.cellTransporter c.1 c.1 = fun x => x :=
      huniq.1.unique huniq.2 ⟨hid, Set.image_id _⟩
    have hs : d.inducedSign (fun x : d.Space => x) = 1 := by
      have hm := hSgn.2.2.2 _ hid _ hid
      have hcomp : ((fun x : d.Space => x) ∘ fun x : d.Space => x) = fun x => x := rfl
      rw [hcomp] at hm
      rcases hSgn.2.2.1 _ hid with h | h
      · exact h
      · rw [h] at hm
        norm_num at hm
    rw [checkerboardCopy_eq_conjIf, e, hs, conjIf_one]
    exact actOnObservables_of_toFun_eq_id _ (hInd.2.1 _ hid) F.1
  · intro c''
    obtain ⟨-, -, -, hCells, -, -, -⟩ := hG L κ d
    have hgc := (hCells.2 c'.1 c'.2 c''.1 c''.2).2
    rw [checkerboardCopy_eq_conjIf d c' c'']
    exact (checkerboardCopy_of_mapsCellTo d hG c c' c'' F hgc.1 hgc.2.symm).symm
  · rintro θ ⟨μ, a, hθ⟩ c'' hc
    obtain ⟨-, -, -, -, hSgn, -, -⟩ := hG L κ d
    have hmem : d.faceReflectEquiv μ a ∈ d.reflectionGroup :=
      Subgroup.subset_closure ⟨(μ, a), rfl⟩
    have hind : d.IsInducedMap θ ((⟨d.faceReflectEquiv μ a, hmem⟩ : d.reflectionGroup) :
        InfiniteLattice.AmbientSpace ≃ᵃ[ℝ] InfiniteLattice.AmbientSpace) := hθ
    have hθG : θ ∈ d.inducedGroupMaps := ⟨_, hmem, hind⟩
    have hs : d.inducedSign θ = -1 := by
      rw [hSgn.2.1 ⟨d.faceReflectEquiv μ a, hmem⟩ θ hind]
      exact linearSign_faceReflectEquiv d μ a hmem
    rw [checkerboardCopy_of_mapsCellTo d hG c c' c'' F hθG hc, hs, conjIf_neg_one]
end YangMills.Construction.GridCopyRule
end
