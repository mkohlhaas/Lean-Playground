def main : IO Unit := do
  let stdin  ← IO.getStdin
  let stdout ← IO.getStdout

  stdout.putStrLn "How would you like to be addressed?" -- NOTE: accessor notation
  let input ← stdin.getLine                             -- NOTE: ←  (IO action)
  let name := input.trimAscii                           -- NOTE: := (expression)
  stdout.putStrLn s!"Hello, {name}!"                    -- NOTE: accessor notation
