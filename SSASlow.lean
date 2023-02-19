inductive Kind where
| k_a : Kind

@[reducible]
def Kind.eval: Kind -> Type
| .k_a => Int

structure Val where
  kind: Kind
  val: Int

inductive Op where
| op (name : String) (argval : List Val)

def sem: (o: Op) → Val
| .op "a" [⟨.k_a, _⟩] => ⟨.k_a, 0⟩
| .op "b" [⟨.k_a, _⟩] => ⟨.k_a, 0⟩
| .op "c" [⟨.k_a, _⟩] => ⟨.k_a, 0⟩
| .op "d" [⟨.k_a, _⟩] => ⟨.k_a, 0⟩
| .op "e" [⟨.k_a, _⟩] => ⟨.k_a, 0⟩
| .op "f" [⟨.k_a, _⟩] => ⟨.k_a, 0⟩
| .op "g" [⟨.k_a, _⟩] => ⟨.k_a, 0⟩
| .op "h" [⟨.k_a, _⟩] => ⟨.k_a, 0⟩
| .op "i" [⟨.k_a, _⟩] => ⟨.k_a, 0⟩
| _ => ⟨.k_a, 0⟩

theorem Fail: sem (.op "x" [⟨.k_a, 0⟩]) = output  := by {
  -- tactic 'simp' failed, nested error:
  -- (deterministic) timeout at 'whnf', maximum number of heartbeats (200000) has been reached (use 'set_option maxHeartbeats <num>' to set the limit)
  simp only[sem];
}

-- The timeout disappears with the following changes
-- x Change 'Int' to 'Unit'
-- x Remove List
-- x Hardcode 'val : Int'
-- x Remove 'k_f' case
-- x remove '.op "h"' case
-- x remove name from Op
-- x remove 'reducible'