def main : IO Unit := do
  let englishGreeting := IO.println "Hello!" -- expression
  IO.println "Bonjour!"                      -- action
  englishGreeting                            -- action

-- output:
-- Bonjour!
-- Hello!
