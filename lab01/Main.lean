import Lab01

def main : IO Unit := askAndAdd

-- this works btw
-- def main : IO Unit := do
--   let stdin ← .getStdin
--   .println "select size of range: "
--   let num_str ← stdin.getLine
--   match num_str.trimAscii.toNat? with
--   | none => .println "not a number"
--   | some n => do
--     let vec := Vector.range n
--     .println vec.toArray
