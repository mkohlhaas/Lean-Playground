-- from previous chapters

structure LetterCounts where
  vowels     : Nat
  consonants : Nat
deriving Repr

inductive Err where
  | notALetter : Char → Err
deriving Repr

def vowels :=
  let lowerVowels := "aeiuoy"
  lowerVowels ++ lowerVowels.map (·.toUpper)

def consonants :=
  let lowerConsonants := "bcdfghjklmnpqrstvwxz"
  lowerConsonants ++ lowerConsonants.map (·.toUpper )

-- ---------------- --
-- More do Features --
-- ---------------- --

-- https://lean-lang.org/functional_programming_in_lean/Monad-Transformers/More-do-Features/#more-do-features

-- ------------------ --
-- Single-Branched if --
-- ------------------ --

-- https://lean-lang.org/functional_programming_in_lean/Monad-Transformers/More-do-Features/#single-branched-if

def countLetters (str : String) : StateT LetterCounts (Except Err) Unit :=
  let rec loop (chars : List Char) := do
    match chars with
    | []      => pure ()
    | c :: cs => if c.isAlpha then                                              
                   if vowels.contains c then                                    
                     modify fun st => {st with vowels := st.vowels + 1}         
                   else if consonants.contains c then                           
                     modify fun st => {st with consonants := st.consonants + 1} 
                   else
                     pure () -- NOTE: superfluous! Lean inserts it automatically!
                 else throw $ .notALetter c                                     
                 loop cs
  loop str.toList

-- count the entries in a list that satisfy some monadic check
def count [Monad m] [MonadState Nat m] (p : α → m Bool) : List α → m Unit
  | []      => pure ()
  | x :: xs => do
               if ← p x
                 then modify (· + 1)
                 -- NOTE: missing else branch is replaced `pure ()`
               count p xs
 
def countNot [Monad m] [MonadState Nat m] (p : α → m Bool) : List α → m Unit
 | []      => pure ()
 | x :: xs => do
              unless ← p x do
                modify (· + 1)
              -- NOTE: missing else branch is replaced `pure ()`
              countNot p xs              

-- ------------ --
-- Early Return --
-- ------------ --

-- https://lean-lang.org/functional_programming_in_lean/Monad-Transformers/More-do-Features/#early-return

def List.find'? (p : α → Bool) : List α → Option α
  | []      => none
  | x :: xs => if p x
                 then some x     
                 else find'? p xs 

def List.find''? (p : α → Bool) : List α → Option α
  | []      => failure
  | x :: xs => do
               if p x then return x
               find''? p xs

-- strip outer monad; exception type and return type are the same
def runCatch [Monad m] (action : ExceptT α m α) : m α := do
  match ← action with
  | Except.ok    x => pure x
  | Except.error x => pure x

#print ExceptT

def List.find'''? (p : α → Bool) : List α → Option α
  | []      => failure
  | x :: xs => runCatch do -- in `ExceptT α Option α` monad
                 if p x
                   then throw x
                   else pure () 
                 monadLift $ find'''? p xs        

-- typical main program; checking inputs
-- without early return; nested if's
def main' (argv : List String) : IO UInt32 := do
  let stdin  ← IO.getStdin
  let stdout ← IO.getStdout
  let stderr ← IO.getStderr

  if argv != [] then
    stderr.putStrLn s!"Expected no arguments, but got {argv.length}"
    pure 1
  else
    stdout.putStrLn "How would you like to be addressed?"
    stdout.flush

    let name := (← stdin.getLine).trimAscii
    if name == "" then
      stderr.putStrLn s!"No name provided"
      pure 1
    else
      stdout.putStrLn s!"Hello, {name}!"
      pure 0

-- with early return
def main (argv : List String) : IO UInt32 := do
  let stdin  ← IO.getStdin
  let stdout ← IO.getStdout
  let stderr ← IO.getStderr

  unless argv == [] do
    stderr.putStrLn s!"Expected no arguments, but got {argv.length}"
    return 1

  stdout.putStrLn "How would you like to be addressed?"
  stdout.flush

  let name := (← stdin.getLine).trimAscii
  if name == "" then
    stderr.putStrLn s!"No name provided"
    return 1

  stdout.putStrLn s!"Hello, {name}!"

  return 0

-- $ lean --run moreDoFeatures.lean
-- $ lean --run moreDoFeatures.lean Hans

-- NOTE: early return applies only to the current do-block
def greet (name : String) : String :=
  "Hello, " ++ Id.run do return name

-- "Hello, Hans", not just "Hans"
#eval greet "Hans"

-- ----- --
-- Loops --
-- ----- --

-- https://lean-lang.org/functional_programming_in_lean/Monad-Transformers/More-do-Features/#loops


