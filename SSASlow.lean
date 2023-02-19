inductive Op where
| op (name : String)

def sem: (o: Op) → Unit
| .op "a" => ()
| .op "b" => ()
| .op "c" => ()
| .op "d" => ()
| .op "e" => ()
| .op "f" => ()
| .op "g" => ()
| .op "h" => ()
| .op "i" => ()
| _ => ()

theorem Fail: sem (.op "x") = output  := by {
  -- tactic 'simp' failed, nested error:
  -- (deterministic) timeout at 'whnf', maximum number of heartbeats (200000) has been reached (use 'set_option maxHeartbeats <num>' to set the limit)
  simp only[sem];
}

-- The timeout disappears with the following changes
-- x Change 'Int' to 'Unit'
-- x remove '.op "i"' case
-- x remove name from Op
-- x remove 'reducible'