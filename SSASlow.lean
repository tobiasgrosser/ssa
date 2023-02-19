inductive Kind where
| k_a : Kind

inductive Op where
| op (name : String) (argval : Int)

def sem: (o: Op) → Unit
| .op "a" _ => ()
| .op "b" _ => ()
| .op "c" _ => ()
| .op "d" _ => ()
| .op "e" _ => ()
| .op "f" _ => ()
| .op "g" _ => ()
| .op "h" _ => ()
| .op "i" _ => ()
| _ => ()

theorem Fail: sem (.op "x" 0) = output  := by {
  -- tactic 'simp' failed, nested error:
  -- (deterministic) timeout at 'whnf', maximum number of heartbeats (200000) has been reached (use 'set_option maxHeartbeats <num>' to set the limit)
  simp only[sem];
}

-- The timeout disappears with the following changes
-- x Change 'Int' to 'Unit'
-- x remove '.op "i"' case
-- x remove name from Op
-- x remove 'reducible'