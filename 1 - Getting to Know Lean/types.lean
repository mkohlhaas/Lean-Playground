/- ----- -/
/- Types -/
/- ----- -/

-- https://lean-lang.org/functional_programming_in_lean/find/?domain=Verso.Genre.Manual.section&name=getting-to-know-types

-- Lean's type system is unusually expressive.
-- Types can encode strong specifications like “this sorting function returns a permutation of its input” and flexible specifications like “this function has different return types, depending on the value of its argument”.
-- The type system can even be used as a full-blown logic for proving mathematical theorems. 

#eval (1 + 2 : Nat )                       
#eval  1 - 2                               
#eval (1 - 2 : Nat )                       
#eval (1 - 2 : Int )                       

#eval  1/0                                 
#check 1/0                                 

#check  1 - 2                              
#check (1 - 2 : Int)                       

#check String.append ["hello", " "] "world"
