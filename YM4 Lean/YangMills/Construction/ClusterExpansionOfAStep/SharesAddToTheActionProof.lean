import YangMills.Construction.ClusterExpansionOfAStep.PotentialOfASettingProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.StepCosts
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields
namespace ShareSum
variable {F : BlockFrame}
theorem card_plaquetteCorners (hL : 0 < F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) {j : ℕ} (x : F.Site j)
    {μ ν : Fin 4} (h : μ ≠ ν) : (plaquetteCorners (x, μ, ν)).card = 4 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CellShares.card_plaquetteCorners <;> assumption
theorem sum_ite_at_point {β : Type} [Fintype β] (y : β) (c : ℝ) [∀ Y, Decidable (y = Y)] :
    ∑ Y : β, (if y = Y then c else 0) = c := by apply _root_.YangMills.Construction.StepSettings.PotentialFactorization.sum_ite_eq_const <;> assumption
theorem sum_corner_quarters (hL : 0 < F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) {β : Type} [Fintype β]
    (g : F.Site 0 → β) (p : F.Site 0 × Fin 4 × Fin 4) (hp : p.2.1 ≠ p.2.2)
    [∀ x Y, Decidable (g x = Y)] :
    ∑ Y : β, ∑ x ∈ plaquetteCorners p, (if g x = Y then (1 / 4 : ℝ) else 0) = 1 := by
  rw [Finset.sum_comm]
  simp only [sum_ite_at_point, Finset.sum_const, nsmul_eq_mul]
  obtain ⟨x, μ, ν⟩ := p
  rw [card_plaquetteCorners hL hs x hp]
  norm_num
theorem sum_endpoint_halves {β γ : Type} [Fintype β] (g : γ → β) (c c' : γ) [∀ x Y, Decidable (g x = Y)] :
    ∑ Y : β, ((if g c = Y then (1 / 2 : ℝ) else 0) + (if g c' = Y then (1 / 2 : ℝ) else 0)) = 1 := by
  rw [Finset.sum_add_distrib, sum_ite_at_point, sum_ite_at_point]
  norm_num
theorem ne_of_mem_innerPlaquettes {S : Finset F.Cell} {p : F.Site 0 × Fin 4 × Fin 4}
    (hp : p ∈ innerPlaquettes S 0) : p.2.1 ≠ p.2.2 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CellShares.ne_of_mem_innerPlaquettes <;> assumption
theorem zmod_cast_cast_of_eq {N M : ℕ} (h : N = M) (y : ZMod M) :
    (ZMod.cast (((ZMod.cast y : ℤ) : ZMod N)) : ZMod M) = y := by
  subst h
  simp
theorem zmod_cast_cast_of_eq' {N M : ℕ} (h : N = M) (c : ZMod N) :
    (((ZMod.cast (ZMod.cast c : ZMod M) : ℤ)) : ZMod N) = c := by
  subst h
  simp
end ShareSum
open ShareSum in
theorem sharesSumToAction (hLV : minimalChainExistenceStatement) : SharesSumToAction := by
  classical
  intro a L t n _ S V ha hL hn
  let F : BlockFrame := torusFrame L t n
  have hFL : 0 < F.blockSide := hL
  have hFs : ∀ i, 2 ≤ F.extent i := fun _ => hn
  have hper : ∀ i, F.period F.top i = n := by
    intro i
    simp [F, torusFrame, BlockFrame.period]
  let e : TorusSite n → F.Cell := fun y => torusSiteInFrame F (t + 1) y
  let back : F.Cell → TorusSite n := fun c i => (ZMod.cast (c i) : ZMod n)
  have hbe : ∀ y, back (e y) = y := by
    intro y
    funext i
    exact zmod_cast_cast_of_eq (hper i) (y i)
  have heb : ∀ c, e (back c) = c := by
    intro c
    funext i
    exact zmod_cast_cast_of_eq' (hper i) (c i)
  have hiff : ∀ (c : F.Cell) (Y : TorusSite n), c = e Y ↔ back c = Y := by
    intro c Y
    constructor
    · intro h
      rw [h, hbe]
    · intro h
      rw [← h, heb]
  set S' : Finset F.Cell := cellsOfSites F S with hS'
  set V' : F.GaugeField F.top := readAtLevel F (t + 1) V with hV'
  obtain ⟨X₀, hX₀, htot⟩ := (hLV F a S' ha).2.2.2 V'
  have hex : ∃ X, IsMinimalChain a S' V' X := ⟨X₀, hX₀⟩
  have hsum : ∀ X : F.FieldChain, ∑ y : TorusSite n, cellShare a S' (e y) X = chainAction a S' X := by
    intro X
    unfold cellShare chainAction
    rw [Finset.sum_add_distrib, Finset.sum_comm, ← Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro p hp
      rw [← Finset.sum_mul]
      simp only [hiff]
      rw [sum_corner_quarters hFL hFs (fun x => back (enclosingCell x)) p (ne_of_mem_innerPlaquettes hp), one_mul]
    · congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      rw [← Finset.sum_mul]
      simp only [hiff]
      rw [sum_endpoint_halves (fun x : F.Site (j + 1) => back (enclosingCell x)), one_mul]
  have hshare : ∀ y : TorusSite n, levelShare a L (t + 1) S y V = cellShare a S' (e y) hex.choose := by
    intro y
    change minimalCellShare a S' (e y) V' = _
    unfold minimalCellShare
    rw [dif_pos hex]
  have hact : actionAtLevel a L (t + 1) S V = minimalAction a S' F.top V' := rfl
  simp only [hshare]
  rw [hsum, hact, ← htot]
  exact le_antisymm (hex.choose_spec.2 X₀ hX₀.1) (hX₀.2 _ hex.choose_spec.1)
end YangMills.Construction.StepCosts
end
