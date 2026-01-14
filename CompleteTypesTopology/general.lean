import Mathlib.Topology.Basic
import Mathlib.Topology.Bases
import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Types
import Mathlib.Data.Fin.Basic
import Mathlib.Topology.Separation.Regular

namespace CompleteTypesTopology
open FirstOrder

lemma neq_element {L : Language} (T : L.Theory) {α : Type*} {p q : T.CompleteType α} (h : ¬p=q) :
  ∃ φ ∈ p, φ ∉ q := by
  rw [SetLike.ext_iff] at h
  push_neg at h
  obtain ⟨a, ha⟩ := h
  cases ha with
  | inl ha => use a
  | inr ha =>
    by_contra h1
    push_neg at h1
    obtain ⟨ha1, ha2⟩ := ha
    rcases FirstOrder.Language.Theory.CompleteType.mem_or_not_mem p a with m1 | m2
    · contradiction
    · specialize h1 a.not m2
      rw [FirstOrder.Language.Theory.CompleteType.not_mem_iff] at h1
      contradiction

lemma extend_partial_type {L : Language} (T : L.Theory) {α : Type*}
                          (T' : (L.withConstants α).Theory) (h1 : T'.IsSatisfiable)
                          (h2 : (L.lhomWithConstants α).onTheory T ⊆ T') :
  ∃ (p : T.CompleteType α), T' ⊆ p.toTheory := by
  let m := (Classical.choice h1)
  let p : T.CompleteType α := ⟨(L.withConstants α).completeTheory m,
                          by exact HasSubset.Subset.trans h2 Language.Theory.completeTheory.subset,
                          by exact Language.completeTheory.isMaximal (L[[α]]) ↑m⟩
  use p
  exact Language.Theory.completeTheory.subset

lemma formulas_countable {α : Type*} {L : Language} (h1 : Countable α) (h2 : Countable L.Symbols) :
  Countable (L.Formula α) := by
  have h3 : Cardinal.mk (L.Formula α) ≤ Cardinal.mk ((m : ℕ) × L.BoundedFormula α m) := by
    rw [Cardinal.mk_sigma]
    exact Cardinal.le_sum (fun i ↦ Cardinal.mk (L.BoundedFormula α i)) 0
  suffices Cardinal.mk (L.Formula α) ≤ Cardinal.aleph0 by exact Cardinal.mk_le_aleph0_iff.mp this
  suffices Cardinal.mk ((m : ℕ) × L.BoundedFormula α m) ≤ Cardinal.aleph0 by
    exact le_trans h3 this
  have h5 : Cardinal.aleph0 =
    max Cardinal.aleph0 (Cardinal.lift.{max u_2 u_3, u_1} (Cardinal.mk α) +
                          Cardinal.lift.{u_1, max u_2 u_3} L.card) := by
    simp only [left_eq_sup, Cardinal.add_le_aleph0, Cardinal.lift_le_aleph0, Cardinal.mk_le_aleph0]
    suffices Cardinal.mk L.Symbols ≤ Cardinal.aleph0 by trivial
    exact Cardinal.mk_le_aleph0_iff.mpr h2
  rw [h5]
  exact FirstOrder.Language.BoundedFormula.card_le (L := L) (α := α)

end CompleteTypesTopology
