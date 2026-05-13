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

-- --------------------------- --
-- Ordering Monad Transformers --
-- --------------------------- --

-- https://lean-lang.org/functional_programming_in_lean/Monad-Transformers/Ordering-Monad-Transformers/#monad-transformer-order

-- When composing a monad from a stack of monad transformers, it's important to
-- be aware that the order in which the monad transformers are layered matters.
-- Different orderings of the same set of transformers result in different
-- monads.

-- just like the previous version, except it uses type classes to describe the
-- set of available effects instead of providing a concrete monad
def countLetters [Monad m] [MonadState LetterCounts m] [MonadExcept Err m] (str : String) : m Unit :=
  let rec loop (chars : List Char) := do
    match chars with
    | []      => pure ()
    | c :: cs => if c.isAlpha then                                              
                   if vowels.contains c then                                    
                     modify fun st => {st with vowels := st.vowels + 1}         
                   else if consonants.contains c then                           
                     modify fun st => {st with consonants := st.consonants + 1} 
                   else -- modified or non-English letter                       
                     pure ()                                                    
                 else throw $ .notALetter c                                     
                 loop cs                                                        
  loop str.toList

abbrev M1 := StateT LetterCounts (ExceptT Err Id)
abbrev M2 := ExceptT Err (StateT LetterCounts Id)

-- similar results when no error
#eval countLetters (m := M1) "hello" ⟨0, 0⟩
#eval countLetters (m := M2) "hello" ⟨0, 0⟩

-- different results when error
#eval countLetters (m := M1) "hello!" ⟨0, 0⟩
#eval countLetters (m := M2) "hello!" ⟨0, 0⟩

-- It might be tempting to think that M2 is superior to M1 because it provides
-- more information that might be useful when debugging. The same program might
-- compute different answers in M1 than it does in M2, and there's no
-- principled reason to say that one of these answers is necessarily better
-- than the other. 

def countWithFallback [Monad m] [MonadState LetterCounts m] [MonadExcept Err m] (str : String) : m Unit :=
  try
    countLetters str
  catch _ =>
    countLetters "Fallback"

#eval countWithFallback (m := M1) "hello" ⟨0, 0⟩ 
#eval countWithFallback (m := M2) "hello" ⟨0, 0⟩ 

#eval countWithFallback (m := M1) "hello!" ⟨0, 0⟩
#eval countWithFallback (m := M2) "hello!" ⟨0, 0⟩

-- ---------------- --
-- Commuting Monads --
-- ---------------- --

-- https://lean-lang.org/functional_programming_in_lean/Monad-Transformers/Ordering-Monad-Transformers/#commuting-monads
