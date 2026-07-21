/-
A finite countermodel for possible and uncertain coreference.

Every exact normalization is an ordinary partition.  Nevertheless, the union
of the coreference relations across feasible worlds need not be transitive:
one world may merge `a` with `b`, while another merges `b` with `c`, without
any world merging `a` with `c`.  Thus neither `MaySame` nor the `Uncertain`
overlay can be used as the quotient relation.
-/
import Ste.DynamicFrame.Laws

namespace STE.DynamicFrame.Counterexample

inductive Mention where
  | a
  | b
  | c
  deriving DecidableEq, Repr

inductive World where
  | left
  | right
  deriving DecidableEq, Repr

/-- In the left world `{a,b}` is a block; in the right world `{b,c}` is a
block. -/
def label : World → Mention → Bool
  | .left, .a => false
  | .left, .b => false
  | .left, .c => true
  | .right, .a => false
  | .right, .b => true
  | .right, .c => true

/-- A constraint-free normalization model containing exactly the two worlds
above. -/
def model : Model Unit Mention Unit World (Fin 0) where
  claimDocument := fun _ => ()
  candidateFrames := fun _ => Set.univ
  candidateFrames_nonempty := fun _ => ⟨(), Set.mem_univ ()⟩
  interpretation := fun _ _ => ()
  interpretation_mem := fun _ _ => Set.mem_univ ()
  sameFrame := fun h c d => label h c = label h d
  sameFrame_equivalence := fun _ =>
    ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩
  support := fun k => Fin.elim0 k
  satisfies := fun _ k => Fin.elim0 k

def allDocuments : Set Unit := Set.univ

theorem all_feasible (h : World) : h ∈ model.feasible allDocuments := by
  apply model.mem_feasible.mpr
  intro k
  exact Fin.elim0 k

theorem consistent : model.Consistent allDocuments :=
  ⟨.left, all_feasible .left⟩

theorem maySame_ab : model.MaySame allDocuments .a .b :=
  ⟨.left, all_feasible .left, rfl⟩

theorem maySame_bc : model.MaySame allDocuments .b .c :=
  ⟨.right, all_feasible .right, rfl⟩

theorem cannotSame_ac : model.CannotSame allDocuments .a .c := by
  intro h _
  cases h <;> simp [model, label]

theorem not_maySame_ac : ¬model.MaySame allDocuments .a .c :=
  model.cannot_iff_not_may.mp cannotSame_ac

theorem uncertain_ab : model.Uncertain allDocuments .a .b := by
  refine ⟨maySame_ab, ?_⟩
  refine ⟨.right, all_feasible .right, ?_⟩
  simp [model, label]

theorem uncertain_bc : model.Uncertain allDocuments .b .c := by
  refine ⟨maySame_bc, ?_⟩
  refine ⟨.left, all_feasible .left, ?_⟩
  simp [model, label]

/-- Possible coreference is not transitive, even though coreference in each
exact world is an equivalence relation. -/
theorem maySame_not_transitive :
    ¬Transitive (model.MaySame allDocuments) := by
  intro ht
  exact not_maySame_ac (ht maySame_ab maySame_bc)

/-- The uncertainty overlay is also not transitive and therefore cannot define
the normalized partition. -/
theorem uncertain_not_transitive :
    ¬Transitive (model.Uncertain allDocuments) := by
  intro ht
  exact model.cannot_not_uncertain cannotSame_ac
    (ht uncertain_ab uncertain_bc)

end STE.DynamicFrame.Counterexample
